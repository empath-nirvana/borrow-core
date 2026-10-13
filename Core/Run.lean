import Core.Steps
import Support.Dynamics.Interpreter

/-!
# Core — a run of the machine, computed  `[spec §3, §19]`

`look e` finds the evaluation position of `e` and says what is there: `e` is a value, a head step
that keeps every memory and allocates nothing (`red K a a'`: `e = K[a]`, `a ↦ a'`), an operation
that no frame of its context catches (`op r K p n`: `e = K[op p]`, the context free of the name
`n`), or something it does not decide (`stuck`).  It covers the steps a run through handlers,
finalisers and cancels takes (`beta`, `seq`, `letpair`, `case`, `hret`, `hop`, `hunwind`,
`uthen`, `ufin`, `ufinC`, `cfret`, `cferr`, `cfcancel`, `cancel`, `creraise`) and no step that
reads or changes the memory.  `look_sound` states what each answer means in Core's terms (`Head`,
`opE`, `OpFree`).  The steps `look` finds in a row are a computation (`lookRun`), and each is a
head step at a context that keeps every memory (`HeadChain`, `lookRun_sound`).

`runM` adds the four memory steps (`alloc`, `free`, `load`, `store`) at a finite memory kept as a
list of cells (`LMem`); an allocation takes one past the largest location in use.  `memAt` finds
a memory redex at an evaluation position of the term, with its context, and `memOp` steps it on
the list.  `runM_sound`: every run `runM` computes is a run of Core's machine (`Steps`), from the
memory the list denotes (`LMem.heap`) to the memory the final list denotes.  The kernel evaluates
`runM`, so a closed program's run to a value is proved by `rfl` and read as a run of the machine
(`runM_val`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE ccatchE cfinE
  hndVal cancelVal kappa clauseAt errVal errNext kappaAt capTag)

/-! ### Deciding values and payloads -/

theorem isValB_of_isVal : ∀ {e : Expr}, IsVal e → isValB e = true
  | _, .unit => rfl
  | _, .pair h₁ h₂ => by simp [isValB, isValB_of_isVal h₁, isValB_of_isVal h₂]
  | _, .inj₁ h => by simp [isValB, isValB_of_isVal h]
  | _, .inj₂ h => by simp [isValB, isValB_of_isVal h]
  | _, .lam => rfl
  | _, .loc => rfl
  | _, .prim => rfl
  | _, .storeV h => by simp [isValB, isValB_of_isVal h]

theorem valOf?_some {e : Expr} {v : Val} (h : valOf? e = some v) : e = v.1 := by
  unfold valOf? at h
  split at h
  · cases h; rfl
  · cases h

theorem valOf?_none {e : Expr} (h : valOf? e = none) : ¬ IsVal e := by
  intro hv
  unfold valOf? at h
  rw [dif_pos (isValB_of_isVal hv)] at h
  cases h

theorem valOf?_val (v : Val) : valOf? v.1 = some v := by
  unfold valOf?
  rw [dif_pos (isValB_of_isVal v.2)]

theorem clauseOf_some : ∀ (hs : Expr) (i : ℕ) (c : Val), clauseOf hs i = some c →
    clauseAt hs i = some c
  | .pair c' _, 0, c, h => by
      simp only [clauseOf] at h
      have := valOf?_some h
      subst this
      simp [clauseAt, c.2]
  | .pair _ r, i + 1, c, h => by
      simp only [clauseOf] at h
      simp only [clauseAt]
      exact clauseOf_some r i c h
  | .var _, _, _, h | .unit, _, _, h | .inj₁ _, _, _, h | .inj₂ _, _, _, h | .lam _, _, _, h
  | .loc _, _, _, h | .prim _, _, _, h | .seq _ _, _, _, h | .letpair _ _, _, _, h
  | .case _ _ _, _, _, h | .app _ _, _, _, h => by simp [clauseOf] at h

theorem errOf_some (y : Expr) (err : Option Val) (h : BoCa.errOf y = some err) :
    y = (errVal err).1 := by
  unfold BoCa.errOf at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; rfl
  · rename_i e
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨E, hE, rfl⟩ := h
    rw [valOf?_some hE]; rfl
  · cases h

/-- The name of an operation's payload. -/
def nameOf? : Expr → Option UInt32
  | .pair (.prim (.lit (.i32 n))) _ => some n
  | _ => none

theorem nameOf?_val (p : Val) : nameOf? p.1 = payloadName p := by
  obtain ⟨p, hp⟩ := p
  cases p with
  | pair a b =>
      cases a with
      | prim q =>
          cases q with
          | lit c => cases c <;> rfl
          | _ => rfl
      | _ => rfl
  | _ => rfl

/-- The name, operation and argument of a payload `(n, (i, v))`. -/
def payOf? : Expr → Option (UInt32 × UInt32 × Val)
  | .pair (.prim (.lit (.i32 n))) (.pair (.prim (.lit (.i32 i))) v) =>
      (valOf? v).map fun w => (n, i, w)
  | _ => none

theorem payOf?_some {e : Expr} {n i : UInt32} {w : Val} (h : payOf? e = some (n, i, w)) :
    e = (opPayload n i w).1 := by
  unfold payOf? at h
  split at h
  · simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
    obtain ⟨w', hw', rfl, rfl, rfl⟩ := h
    rw [valOf?_some hw']; rfl
  · cases h

/-- The state `err` of a cancel payload. -/
def cancelOf? (e : Expr) : Option (Option Val) :=
  match payOf? e with
  | some (0, 0, w) => BoCa.errOf w.1
  | _ => none

theorem cancelOf?_some {e : Expr} {err : Option Val} (h : cancelOf? e = some err) :
    e = (cancelVal err).1 := by
  unfold cancelOf? at h
  split at h
  · rename_i w hw
    rw [payOf?_some hw]
    have hw' : w = errVal err := Subtype.ext (errOf_some w.1 err h)
    rw [hw']; rfl
  · cases h

/-! ### Where evaluation stands -/

/-- What `look` finds at a term's evaluation position. -/
inductive Look
  | val
  | red (K : Kont) (a a' : Expr)
  | op (r : Bool) (K : Kont) (p : Val) (n : UInt32)
  | stuck

/-- The finding under one more frame. -/
def Look.under (F : Kont → Kont) : Look → Look
  | .red K a a' => .red (F K) a a'
  | .op r K p n => .op r (F K) p n
  | _ => .stuck

/-- What the frame `f □` makes of the stopped operation `K[op r p]` of the name `n` in its hole:
it passes it on when it does not catch it, and steps when it does. -/
def lookCatch (f arg : Expr) (r : Bool) (K : Kont) (p : Val) (n : UInt32) : Look :=
  if cond r ((Kont.appR f .hole).Catches n) ((Kont.appR f .hole).HasHnd n) = false then
    .op r (.appR f K) p n
  else
    match f, r with
    | .app (.prim .hnd) (.pair (.prim (.lit (.i32 _))) (.pair qs (.pair hr hs))), r =>
        match valOf? qs, valOf? hr, valOf? hs, payOf? p.1 with
        | some qsv, some hrv, some hsv, some (_, i, w) =>
            match clauseOf hs i.toNat with
            | some c =>
                if r then .red .hole (.app f arg) (.app c.1 w.1)
                else .red .hole (.app f arg) (.app c.1 (.pair w.1
                  (kappaAt (capTag qs i.toNat) (hndVal n qsv hrv hsv) K)))
            | none => .stuck
        | _, _, _, _ => .stuck
    | .app (.prim .ubind) (.pair N D), true =>
        match valOf? N, valOf? D with
        | some _, some _ =>
            if n = 0 then
              match cancelOf? p.1 with
              | some _ => .red .hole (.app f arg) (cfinE p (.app D (.val .unit)))
              | none => .stuck
            else
              match payOf? p.1 with
              | some _ => .red .hole (.app f arg) (.seq (.app D (.val .unit)) (raiseE (.val p)))
              | none => .stuck
        | _, _ => .stuck
    | .prim .ccatch, true =>
        match cancelOf? p.1 with
        | some none => .red .hole (.app f arg) (.val .unit)
        | some (some E) => .red .hole (.app f arg) (raiseE (.val E))
        | none => .stuck
    | .app (.prim .cfin) s, true =>
        match cancelOf? s with
        | some err =>
            if n = 0 then
              match cancelOf? p.1 with
              | some err' => .red .hole (.app f arg) (raiseE (.val (cancelVal (err.or err'))))
              | none => .stuck
            else
              match payOf? p.1 with
              | some (m, j, w) =>
                  .red .hole (.app f arg) (raiseE (.val (cancelVal (errNext err m j w))))
              | none => .stuck
        | none => .stuck
    | _, _ => .stuck

/-- **Where the evaluation of a term stands.** -/
def look : Expr → Look
  | .var _ => .stuck
  | .unit => .val
  | .lam _ => .val
  | .loc _ => .val
  | .prim _ => .val
  | .pair a b =>
      match valOf? a with
      | some va =>
          match look b with
          | .val => .val
          | l => l.under (.pairR va)
      | none => (look a).under (.pairL · b)
  | .inj₁ a =>
      match look a with
      | .val => .val
      | l => l.under .inj₁
  | .inj₂ a =>
      match look a with
      | .val => .val
      | l => l.under .inj₂
  | .seq a b =>
      match a with
      | .unit => .red .hole (.seq .unit b) b
      | _ => (look a).under (.seq · b)
  | .letpair a b =>
      match valOf? a with
      | some _ =>
          match a with
          | .pair x y =>
              match valOf? x, valOf? y with
              | some vx, some vy =>
                  .red .hole (.letpair a b) ((b.subst 0 (vy.shift 1 0)).subst 0 vx)
              | _, _ => .stuck
          | _ => .stuck
      | none => (look a).under (.letpair · b)
  | .case a b₁ b₂ =>
      match valOf? a with
      | some _ =>
          match a with
          | .inj₁ x =>
              match valOf? x with
              | some vx => .red .hole (.case a b₁ b₂) (b₁.subst 0 vx)
              | none => .stuck
          | .inj₂ x =>
              match valOf? x with
              | some vx => .red .hole (.case a b₁ b₂) (b₂.subst 0 vx)
              | none => .stuck
          | _ => .stuck
      | none => (look a).under (.case · b₁ b₂)
  | .app f a =>
      match valOf? a with
      | none =>
          match look a with
          | .red K x x' => .red (.appR f K) x x'
          | .op r K p n => lookCatch f a r K p n
          | _ => .stuck
      | some va =>
          match f with
          | .lam b => .red .hole (.app (.lam b) a) (b.subst 0 va)
          | .prim .store => .val
          | .prim .perform =>
              match nameOf? a with
              | some n => .op false .hole va n
              | none => .stuck
          | .prim .raise =>
              match nameOf? a with
              | some n => .op true .hole va n
              | none => .stuck
          | .app (.prim .hnd) (.pair (.prim (.lit (.i32 _))) (.pair qs (.pair hr hs))) =>
              match valOf? qs, valOf? hr, valOf? hs with
              | some _, some _, some _ => .red .hole (.app f a) (.app hr a)
              | _, _, _ => .stuck
          | .app (.prim .ubind) (.pair N D) =>
              match valOf? N, valOf? D with
              | some _, some _ => .red .hole (.app f a) (.app N a)
              | _, _ => .stuck
          | .app (.prim .cfin) s =>
              match cancelOf? s with
              | some _ => .red .hole (.app f a) (raiseE s)
              | none => .stuck
          | _ =>
              match valOf? f with
              | some _ => .stuck
              | none => (look f).under (fun K => .appL K va)

/-! ### What `look` finds, in Core's terms -/

/-- What a finding means: a value; a head step at a context that keeps every memory and allocates
nothing; an operation its context does not catch; or nothing claimed. -/
def LookOK (e : Expr) : Look → Prop
  | .val => IsVal e
  | .red K a a' => e = K.plug a ∧ (∀ μ, Head (ℍ := ℍ) μ a μ a') ∧ a.allocs = false
  | .op r K p n => e = K.plug (opE r p) ∧ payloadName p = some n ∧ OpFree r n K
  | .stuck => True

theorem lookOK_under (F : Kont → Kont) (G : Expr → Expr)
    (hplug : ∀ K x, (F K).plug x = G (K.plug x))
    (hfree : ∀ r n K, OpFree r n K → OpFree r n (F K)) {e : Expr} {l : Look}
    (h : LookOK (ℍ := ℍ) e l) : LookOK (ℍ := ℍ) (G e) (l.under F) := by
  cases l with
  | val => trivial
  | red K a a' =>
      obtain ⟨rfl, hh, hn⟩ := h
      exact ⟨(hplug K a).symm, hh, hn⟩
  | op r K p n =>
      obtain ⟨rfl, hp, hK⟩ := h
      exact ⟨(hplug K _).symm, hp, hfree r n K hK⟩
  | stuck => trivial

/-- A frame that is neither a handler, a finaliser, a `ccatch` nor a `cfin` passes what its hole
holds. -/
theorem opFree_frame {r : Bool} {n : UInt32} {K : Kont} (F : Kont → Kont)
    (hH : ∀ K, (F K).HasHnd n = K.HasHnd n) (hC : ∀ K, (F K).Catches n = K.Catches n)
    (h : OpFree r n K) : OpFree r n (F K) := by
  cases r <;> simp_all [OpFree]

theorem lookCatch_sound {f a : Expr} {r : Bool} {K : Kont} {p : Val} {n : UInt32}
    (ha : a = K.plug (opE r p)) (hn : payloadName p = some n) (hK : OpFree r n K) :
    LookOK (ℍ := ℍ) (.app f a) (lookCatch f a r K p n) := by
  subst ha
  unfold lookCatch
  split
  · rename_i hpass
    refine ⟨rfl, hn, ?_⟩
    cases r <;> simp only [OpFree, cond_false, cond_true] at hK hpass ⊢
    · have : (Kont.appR f K) = (Kont.appR f .hole).comp K := rfl
      rw [this, hasHnd_comp, hpass, hK]; rfl
    · have : (Kont.appR f K) = (Kont.appR f .hole).comp K := rfl
      rw [this, catches_comp, hpass, hK]; rfl
  · rename_i hcatch
    split
    · -- a handler frame of the name
      rename_i rr m qs hr hs
      split
      · rename_i qsv hrv hsv n' i w hqs hhr hhs hpay
        have hm : m = n := by
          cases r <;> simp [Kont.Catches, Kont.HasHnd] at hcatch <;> exact hcatch
        subst hm
        obtain rfl := valOf?_some hqs
        obtain rfl := valOf?_some hhr
        obtain rfl := valOf?_some hhs
        have hp := payOf?_some hpay
        have hp' : p = opPayload n' i w := Subtype.ext hp
        subst hp'
        simp only [payloadName_opPayload, Option.some.injEq] at hn
        subst hn
        split
        · rename_i c hc
          have hc' := clauseOf_some _ _ _ hc
          split
          · rename_i hr'
            subst hr'
            refine ⟨rfl, fun μ => ?_, rfl⟩
            exact Head.hunwind μ _ i qsv hrv hsv c w K hc' (by simpa [OpFree] using hK)
          · rename_i hr'
            simp only [Bool.not_eq_true] at hr'
            subst hr'
            refine ⟨rfl, fun μ => ?_, rfl⟩
            exact Head.hop μ _ i qsv hrv hsv c w K hc' (by simpa [OpFree] using hK)
        · trivial
      · trivial
    · -- a finaliser frame, at a raise
      rename_i N D
      split
      · rename_i Nv Dv hN hD
        obtain rfl := valOf?_some hN
        obtain rfl := valOf?_some hD
        split
        · rename_i hn0
          subst hn0
          split
          · rename_i err hst
            have hp' : p = cancelVal err := Subtype.ext (cancelOf?_some hst)
            subst hp'
            refine ⟨rfl, fun μ => ?_, rfl⟩
            exact Head.ufinC μ Nv Dv err K (by simpa [OpFree] using hK)
          · trivial
        · rename_i hn0
          split
          · rename_i pl hpl
            obtain ⟨n', i, v⟩ := pl
            have hp' : p = opPayload n' i v := Subtype.ext (payOf?_some hpl)
            subst hp'
            simp only [payloadName_opPayload, Option.some.injEq] at hn
            subst hn
            refine ⟨rfl, fun μ => ?_, rfl⟩
            exact Head.ufin μ Nv Dv n' i v K hn0 (by simpa [OpFree] using hK)
          · trivial
      · trivial
    · -- `ccatch`, at a raise of the reserved name
      have hn0 : n = 0 := by simpa [Kont.Catches] using hcatch
      subst hn0
      split
      · rename_i hst
        have hp' : p = cancelVal none := Subtype.ext (cancelOf?_some hst)
        subst hp'
        refine ⟨rfl, fun μ => ?_, rfl⟩
        exact Head.cancel μ K (by simpa [OpFree] using hK)
      · rename_i E hst
        have hp' : p = cancelVal (some E) := Subtype.ext (cancelOf?_some hst)
        subst hp'
        refine ⟨rfl, fun μ => ?_, rfl⟩
        exact Head.creraise μ E K (by simpa [OpFree] using hK)
      · trivial
    · -- a cancel-mode finaliser frame, at a raise
      rename_i s
      split
      · rename_i err hst
        have hs := cancelOf?_some hst
        subst hs
        split
        · -- a cancel reaches it
          rename_i hn0
          subst hn0
          split
          · rename_i err' hst'
            have hp' : p = cancelVal err' := Subtype.ext (cancelOf?_some hst')
            subst hp'
            refine ⟨rfl, fun μ => ?_, rfl⟩
            exact Head.cfcancel μ err err' K (by simpa [OpFree] using hK)
          · trivial
        · -- the finaliser raised
          rename_i hn0
          split
          · rename_i m j w hpay
            have hp' : p = opPayload m j w := Subtype.ext (payOf?_some hpay)
            subst hp'
            simp only [payloadName_opPayload, Option.some.injEq] at hn
            subst hn
            refine ⟨rfl, fun μ => ?_, rfl⟩
            exact Head.cferr μ err m j w K hn0 (by simpa [OpFree] using hK)
          · trivial
      · trivial
    · trivial

theorem opFree_pairL {r : Bool} {n : UInt32} {K : Kont} (b : Expr) (h : OpFree r n K) :
    OpFree r n (.pairL K b) := opFree_frame (fun K => .pairL K b) (fun _ => rfl) (fun _ => rfl) h

theorem opFree_pairR {r : Bool} {n : UInt32} {K : Kont} (v : Val) (h : OpFree r n K) :
    OpFree r n (.pairR v K) := opFree_frame (fun K => .pairR v K) (fun _ => rfl) (fun _ => rfl) h

theorem opFree_inj₁ {r : Bool} {n : UInt32} {K : Kont} (h : OpFree r n K) :
    OpFree r n (.inj₁ K) := opFree_frame Kont.inj₁ (fun _ => rfl) (fun _ => rfl) h

theorem opFree_inj₂ {r : Bool} {n : UInt32} {K : Kont} (h : OpFree r n K) :
    OpFree r n (.inj₂ K) := opFree_frame Kont.inj₂ (fun _ => rfl) (fun _ => rfl) h

theorem opFree_seq {r : Bool} {n : UInt32} {K : Kont} (b : Expr) (h : OpFree r n K) :
    OpFree r n (.seq K b) := opFree_frame (fun K => .seq K b) (fun _ => rfl) (fun _ => rfl) h

theorem opFree_letpair {r : Bool} {n : UInt32} {K : Kont} (b : Expr) (h : OpFree r n K) :
    OpFree r n (.letpair K b) :=
  opFree_frame (fun K => .letpair K b) (fun _ => rfl) (fun _ => rfl) h

theorem opFree_case {r : Bool} {n : UInt32} {K : Kont} (b₁ b₂ : Expr) (h : OpFree r n K) :
    OpFree r n (.case K b₁ b₂) :=
  opFree_frame (fun K => .case K b₁ b₂) (fun _ => rfl) (fun _ => rfl) h

theorem opFree_appL {r : Bool} {n : UInt32} {K : Kont} (v : Val) (h : OpFree r n K) :
    OpFree r n (.appL K v) := opFree_frame (fun K => .appL K v) (fun _ => rfl) (fun _ => rfl) h

/-- **What `look` finds is what Core's machine has there.** -/
theorem look_sound : ∀ e : Expr, LookOK (ℍ := ℍ) e (look e)
  | .var _ => trivial
  | .unit => IsVal.unit
  | .lam _ => IsVal.lam
  | .loc _ => IsVal.loc
  | .prim _ => IsVal.prim
  | .pair a b => by
      have iha := look_sound a
      have ihb := look_sound b
      unfold look
      rcases hva : valOf? a with _ | va
      · exact lookOK_under (.pairL · b) (fun x => .pair x b) (fun _ _ => rfl)
          (fun _ _ _ h => opFree_pairL b h) iha
      · obtain rfl := valOf?_some hva
        rcases hb : look b with _ | ⟨K, x, x'⟩ | ⟨r, K, p, n⟩ | _
        · rw [hb] at ihb; exact IsVal.pair va.2 ihb
        all_goals rw [hb] at ihb
        · exact lookOK_under (.pairR va) (fun x => .pair va.1 x) (fun _ _ => rfl)
            (fun _ _ _ h => opFree_pairR va h) (l := .red K x x') ihb
        · exact lookOK_under (.pairR va) (fun x => .pair va.1 x) (fun _ _ => rfl)
            (fun _ _ _ h => opFree_pairR va h) (l := .op r K p n) ihb
        · trivial
  | .inj₁ a => by
      have iha := look_sound a
      unfold look
      rcases ha : look a with _ | ⟨K, x, x'⟩ | ⟨r, K, p, n⟩ | _
      · rw [ha] at iha; exact IsVal.inj₁ iha
      all_goals rw [ha] at iha
      · exact lookOK_under Kont.inj₁ Expr.inj₁ (fun _ _ => rfl) (fun _ _ _ h => opFree_inj₁ h)
          (l := .red K x x') iha
      · exact lookOK_under Kont.inj₁ Expr.inj₁ (fun _ _ => rfl) (fun _ _ _ h => opFree_inj₁ h)
          (l := .op r K p n) iha
      · trivial
  | .inj₂ a => by
      have iha := look_sound a
      unfold look
      rcases ha : look a with _ | ⟨K, x, x'⟩ | ⟨r, K, p, n⟩ | _
      · rw [ha] at iha; exact IsVal.inj₂ iha
      all_goals rw [ha] at iha
      · exact lookOK_under Kont.inj₂ Expr.inj₂ (fun _ _ => rfl) (fun _ _ _ h => opFree_inj₂ h)
          (l := .red K x x') iha
      · exact lookOK_under Kont.inj₂ Expr.inj₂ (fun _ _ => rfl) (fun _ _ _ h => opFree_inj₂ h)
          (l := .op r K p n) iha
      · trivial
  | .seq a b => by
      have iha := look_sound a
      unfold look
      split
      · exact ⟨rfl, fun μ => Head.seq μ b, rfl⟩
      · exact lookOK_under (.seq · b) (fun x => .seq x b) (fun _ _ => rfl)
          (fun _ _ _ h => opFree_seq b h) iha
  | .letpair a b => by
      have iha := look_sound a
      unfold look
      rcases hva : valOf? a with _ | va
      · exact lookOK_under (.letpair · b) (fun x => .letpair x b) (fun _ _ => rfl)
          (fun _ _ _ h => opFree_letpair b h) iha
      · simp only
        split
        · rename_i x y
          rcases hx : valOf? x with _ | vx
          · trivial
          rcases hy : valOf? y with _ | vy
          · trivial
          obtain rfl := valOf?_some hx
          obtain rfl := valOf?_some hy
          exact ⟨rfl, fun μ => Head.letpair μ vx vy b, rfl⟩
        · trivial
  | .case a b₁ b₂ => by
      have iha := look_sound a
      unfold look
      rcases hva : valOf? a with _ | va
      · exact lookOK_under (.case · b₁ b₂) (fun x => .case x b₁ b₂) (fun _ _ => rfl)
          (fun _ _ _ h => opFree_case b₁ b₂ h) iha
      · simp only
        split
        · rename_i x
          rcases hx : valOf? x with _ | vx
          · trivial
          obtain rfl := valOf?_some hx
          exact ⟨rfl, fun μ => Head.case₁ μ vx b₁ b₂, rfl⟩
        · rename_i x
          rcases hx : valOf? x with _ | vx
          · trivial
          obtain rfl := valOf?_some hx
          exact ⟨rfl, fun μ => Head.case₂ μ vx b₁ b₂, rfl⟩
        · trivial
  | .app f a => by
      have iha := look_sound a
      have ihf := look_sound f
      unfold look
      rcases hva : valOf? a with _ | va
      · simp only
        rcases ha : look a with _ | ⟨K, x, x'⟩ | ⟨r, K, p, n⟩ | _
        · trivial
        · rw [ha] at iha
          obtain ⟨rfl, hh, hn⟩ := iha
          exact ⟨rfl, hh, hn⟩
        · rw [ha] at iha
          obtain ⟨rfl, hp, hK⟩ := iha
          exact lookCatch_sound rfl hp hK
        · trivial
      · obtain rfl := valOf?_some hva
        simp only
        split
        · rename_i b
          exact ⟨rfl, fun μ => Head.beta μ b va, rfl⟩
        · exact IsVal.storeV va.2
        · split
          · rename_i n hn
            refine ⟨rfl, ?_, rfl⟩
            rw [← nameOf?_val]; exact hn
          · trivial
        · split
          · rename_i n hn
            refine ⟨rfl, ?_, rfl⟩
            rw [← nameOf?_val]; exact hn
          · trivial
        · rename_i m qs hr hs
          split
          · rename_i qsv hrv hsv hqs hhr hhs
            obtain rfl := valOf?_some hqs
            obtain rfl := valOf?_some hhr
            obtain rfl := valOf?_some hhs
            exact ⟨rfl, fun μ => Head.hret μ m qsv hrv hsv va, rfl⟩
          · trivial
        · rename_i N D
          split
          · rename_i Nv Dv hN hD
            obtain rfl := valOf?_some hN
            obtain rfl := valOf?_some hD
            exact ⟨rfl, fun μ => Head.uthen μ Nv Dv va, rfl⟩
          · trivial
        · rename_i st
          split
          · rename_i err hc
            have hs := cancelOf?_some hc
            subst hs
            exact ⟨rfl, fun μ => Head.cfret μ err va, rfl⟩
          · trivial
        · split
          · trivial
          · exact lookOK_under (fun K => .appL K va) (fun x => .app x va.1) (fun _ _ => rfl)
              (fun _ _ _ h => opFree_appL va h) ihf

/-! ### Runs `look` computes -/

/-- The steps `look` finds from `e`, at most `k` of them: each a context, a redex and its
reduct. -/
def lookRun : ℕ → Expr → List (Kont × Expr × Expr)
  | 0, _ => []
  | k + 1, e =>
      match look e with
      | .red K a a' => (K, a, a') :: lookRun k (K.plug a')
      | _ => []

/-- Where those steps end. -/
def lookEnd : ℕ → Expr → Expr
  | 0, e => e
  | k + 1, e =>
      match look e with
      | .red K _ a' => lookEnd k (K.plug a')
      | _ => e

/-- A chain of head steps that keep every memory and allocate nothing, from `e` to `e'`. -/
inductive HeadChain : Expr → List (Kont × Expr × Expr) → Expr → Prop
  | nil {e : Expr} : HeadChain e [] e
  | cons {K : Kont} {a a' e' : Expr} {q : List (Kont × Expr × Expr)} :
      (∀ μ, Head (ℍ := ℍ) μ a μ a') → a.allocs = false → HeadChain (K.plug a') q e' →
      HeadChain (K.plug a) ((K, a, a') :: q) e'

/-- Two chains, the second from the first's end, make a chain. -/
theorem HeadChain.append {e e₁ e₂ : Expr} :
    ∀ {q₁ q₂ : List (Kont × Expr × Expr)}, HeadChain (ℍ := ℍ) e q₁ e₁ →
      HeadChain (ℍ := ℍ) e₁ q₂ e₂ → HeadChain (ℍ := ℍ) e (q₁ ++ q₂) e₂
  | _, _, .nil, h₂ => h₂
  | _, _, .cons hh hn h₁, h₂ => .cons hh hn (HeadChain.append h₁ h₂)

/-- **The run `look` computes is a chain of Core's head steps.** -/
theorem lookRun_sound : ∀ (k : ℕ) (e : Expr), HeadChain (ℍ := ℍ) e (lookRun k e) (lookEnd k e)
  | 0, _ => .nil
  | k + 1, e => by
      have h := look_sound (ℍ := ℍ) e
      unfold lookRun lookEnd
      split
      · rename_i K a a' hl
        rw [hl] at h
        obtain ⟨rfl, hh, hn⟩ := h
        exact .cons hh hn (lookRun_sound k _)
      · exact .nil

/-! ### A finite memory -/

/-- A finite memory, as its cells; the first cell at a location is its content. -/
abbrev LMem := List (Loc × Val)

/-- The memory a list of cells denotes. -/
def LMem.heap (m : LMem) : Heap := fun ℓ => List.lookup ℓ m

/-- One past the largest location in use. -/
def LMem.fresh (m : LMem) : Loc := (m.map Prod.fst).foldr max 0 + 1

theorem LMem.lookup_gt : ∀ (m : LMem) (ℓ : Loc), (m.map Prod.fst).foldr max 0 < ℓ →
    List.lookup ℓ m = none
  | [], _, _ => rfl
  | (k, v) :: m, ℓ, h => by
      simp only [List.map_cons, List.foldr_cons] at h
      have hk : k < ℓ := lt_of_le_of_lt (le_max_left _ _) h
      have hm : (m.map Prod.fst).foldr max 0 < ℓ := lt_of_le_of_lt (le_max_right _ _) h
      have hne : (ℓ == k) = false := by
        rw [beq_eq_false_iff_ne]; exact fun he => absurd hk (by rw [he]; exact lt_irrefl k)
      simp only [List.lookup, hne]
      exact LMem.lookup_gt m ℓ hm

/-- The fresh location is free. -/
theorem LMem.heap_fresh (m : LMem) : m.heap m.fresh = none :=
  LMem.lookup_gt m _ (Nat.lt_succ_self _)

/-- A cell in front updates the memory. -/
theorem LMem.heap_cons (m : LMem) (ℓ : Loc) (v : Val) :
    LMem.heap ((ℓ, v) :: m) = (LMem.heap m).upd ℓ v := by
  funext k
  simp only [LMem.heap, List.lookup, Heap.upd]
  by_cases h : k = ℓ
  · subst h; simp
  · have : (k == ℓ) = false := by simp [h]
    simp [this, h]

/-- Dropping every cell at a location removes it from the memory. -/
theorem LMem.heap_filter (m : LMem) (ℓ : Loc) :
    LMem.heap (m.filter fun c => c.1 != ℓ) = (LMem.heap m).del ℓ := by
  funext k
  simp only [LMem.heap, Heap.del]
  induction m with
  | nil => simp
  | cons c m ih =>
      obtain ⟨k', v⟩ := c
      by_cases hk' : k' = ℓ
      · subst hk'
        have hf : (k' != k') = false := by simp
        simp only [List.filter_cons, hf, Bool.false_eq_true, if_false]
        rw [ih]
        by_cases hk : k = k'
        · simp [hk]
        · have : (k == k') = false := by simp [hk]
          simp [List.lookup, this, hk]
      · have hf : (k' != ℓ) = true := by simp [hk']
        simp only [List.filter_cons, hf, if_true, List.lookup]
        by_cases hk : k = k'
        · subst hk; simp [hk']
        · have : (k == k') = false := by simp [hk]
          simp only [this]
          exact ih

/-- The empty list denotes the empty memory. -/
theorem LMem.heap_nil : LMem.heap [] = Adequacy.emptyMem := rfl

/-! ### The memory redex at an evaluation position -/

/-- A memory redex at an evaluation position of the term, and its context: the redex is `alloc v`,
`free ℓ`, `load ℓ` or `store ℓ v`, the argument a value. -/
def memAt : Expr → Option (Kont × Expr)
  | .pair a b =>
      match valOf? a with
      | some va => (memAt b).map fun p => (.pairR va p.1, p.2)
      | none => (memAt a).map fun p => (.pairL p.1 b, p.2)
  | .inj₁ a => (memAt a).map fun p => (.inj₁ p.1, p.2)
  | .inj₂ a => (memAt a).map fun p => (.inj₂ p.1, p.2)
  | .seq a b => (memAt a).map fun p => (.seq p.1 b, p.2)
  | .letpair a b => (memAt a).map fun p => (.letpair p.1 b, p.2)
  | .case a b₁ b₂ => (memAt a).map fun p => (.case p.1 b₁ b₂, p.2)
  | .app f a =>
      match valOf? a with
      | none => (memAt a).map fun p => (.appR f p.1, p.2)
      | some va =>
          match f with
          | .prim .alloc => some (.hole, .app f a)
          | .prim .free => some (.hole, .app f a)
          | .prim .load => some (.hole, .app f a)
          | .app (.prim .store) (.loc ℓ) => some (.hole, .app (.app (.prim .store) (.loc ℓ)) a)
          | _ =>
              match valOf? f with
              | some _ => none
              | none => (memAt f).map fun p => (.appL p.1 va, p.2)
  | _ => none

theorem memAt_sound : ∀ (e : Expr) (K : Kont) (x : Expr), memAt e = some (K, x) → e = K.plug x
  | .pair a b, K, x, h => by
      unfold memAt at h
      rcases hva : valOf? a with _ | va <;> rw [hva] at h <;> simp only at h
      · obtain ⟨⟨K', x'⟩, h', hK⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at hK; obtain ⟨rfl, rfl⟩ := hK
        rw [memAt_sound a K' x' h']; rfl
      · obtain ⟨⟨K', x'⟩, h', hK⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at hK; obtain ⟨rfl, rfl⟩ := hK
        rw [valOf?_some hva, memAt_sound b K' x' h']; rfl
  | .inj₁ a, K, x, h => by
      unfold memAt at h
      obtain ⟨⟨K', x'⟩, h', hK⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at hK; obtain ⟨rfl, rfl⟩ := hK
      rw [memAt_sound a K' x' h']; rfl
  | .inj₂ a, K, x, h => by
      unfold memAt at h
      obtain ⟨⟨K', x'⟩, h', hK⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at hK; obtain ⟨rfl, rfl⟩ := hK
      rw [memAt_sound a K' x' h']; rfl
  | .seq a b, K, x, h => by
      unfold memAt at h
      obtain ⟨⟨K', x'⟩, h', hK⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at hK; obtain ⟨rfl, rfl⟩ := hK
      rw [memAt_sound a K' x' h']; rfl
  | .letpair a b, K, x, h => by
      unfold memAt at h
      obtain ⟨⟨K', x'⟩, h', hK⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at hK; obtain ⟨rfl, rfl⟩ := hK
      rw [memAt_sound a K' x' h']; rfl
  | .case a b₁ b₂, K, x, h => by
      unfold memAt at h
      obtain ⟨⟨K', x'⟩, h', hK⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at hK; obtain ⟨rfl, rfl⟩ := hK
      rw [memAt_sound a K' x' h']; rfl
  | .app f a, K, x, h => by
      unfold memAt at h
      rcases hva : valOf? a with _ | va <;> rw [hva] at h <;> simp only at h
      · obtain ⟨⟨K', x'⟩, h', hK⟩ := Option.map_eq_some_iff.mp h
        simp only [Prod.mk.injEq] at hK; obtain ⟨rfl, rfl⟩ := hK
        rw [memAt_sound a K' x' h']; rfl
      · split at h
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
        · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; rfl
        · rcases hvf : valOf? f with _ | vf <;> rw [hvf] at h <;> simp only at h
          · obtain ⟨⟨K', x'⟩, h', hK⟩ := Option.map_eq_some_iff.mp h
            simp only [Prod.mk.injEq] at hK; obtain ⟨rfl, rfl⟩ := hK
            rw [memAt_sound f K' x' h', valOf?_some hva]; rfl
          · cases h
  | .var _, _, _, h | .unit, _, _, h | .lam _, _, _, h | .loc _, _, _, h | .prim _, _, _, h => by
      simp [memAt] at h

/-! ### The memory steps -/

/-- The memory step at a redex `memAt` finds. -/
def memOp (m : LMem) : Expr → Option (LMem × Expr)
  | .app (.prim .alloc) a => (valOf? a).map fun v => ((m.fresh, v) :: m, .loc m.fresh)
  | .app (.prim .free) (.loc ℓ) =>
      (List.lookup ℓ m).map fun v => (m.filter fun c => c.1 != ℓ, v.1)
  | .app (.prim .load) (.loc ℓ) => (List.lookup ℓ m).map fun v => (m, v.1)
  | .app (.app (.prim .store) (.loc ℓ)) a =>
      match valOf? a, List.lookup ℓ m with
      | some v, some _ => some ((ℓ, v) :: m, .unit)
      | _, _ => none
  | _ => none

theorem memOp_sound {m m' : LMem} {a a' : Expr} (h : memOp m a = some (m', a')) :
    Head (ℍ := ℍ) m.heap a m'.heap a' := by
  unfold memOp at h
  split at h
  · rename_i x
    obtain ⟨v, hv, hm⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl⟩ := hm
    rw [valOf?_some hv, LMem.heap_cons]
    exact Head.alloc m.heap v m.fresh (LMem.heap_fresh m)
  · rename_i ℓ
    obtain ⟨v, hv, hm⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl⟩ := hm
    rw [LMem.heap_filter]
    exact Head.free m.heap ℓ v hv
  · rename_i ℓ
    obtain ⟨v, hv, hm⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl⟩ := hm
    exact Head.load m.heap ℓ v hv
  · rename_i ℓ x
    split at h
    · rename_i v w hv hw
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      rw [valOf?_some hv, LMem.heap_cons]
      exact Head.store m.heap ℓ v w hw
    · cases h
  · cases h

/-! ### Runs -/

/-- One step: `look`'s memory-free step, or a memory step at a redex `memAt` finds. -/
def stepM (m : LMem) (e : Expr) : Option (LMem × Expr) :=
  match look e with
  | .red K _ a' => some (m, K.plug a')
  | _ =>
      match memAt e with
      | some (K, x) => (memOp m x).map fun p => (p.1, K.plug p.2)
      | none => none

theorem stepM_sound {m m' : LMem} {e e' : Expr} (h : stepM m e = some (m', e')) :
    Step1 (ℍ := ℍ) m.heap e m'.heap e' := by
  unfold stepM at h
  split at h
  · rename_i K a a' hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have hok := look_sound (ℍ := ℍ) e
    rw [hl] at hok
    obtain ⟨he, hh, -⟩ := hok
    exact ⟨K, a, a', he, rfl, hh m.heap⟩
  · split at h
    · rename_i K x hK
      obtain ⟨⟨m₁, x'⟩, hx, hm⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at hm; obtain ⟨rfl, rfl⟩ := hm
      exact ⟨K, x, x', memAt_sound e K x hK, rfl, memOp_sound hx⟩
    · cases h

/-- At most `k` steps from `(m, e)`, ending where no step is found. -/
def runM : ℕ → LMem → Expr → LMem × Expr
  | 0, m, e => (m, e)
  | k + 1, m, e =>
      match stepM m e with
      | some (m', e') => runM k m' e'
      | none => (m, e)

/-- **The run `runM` computes is a run of Core's machine.** -/
theorem runM_sound : ∀ (k : ℕ) (m : LMem) (e : Expr),
    Steps (ℍ := ℍ) m.heap e (runM k m e).1.heap (runM k m e).2
  | 0, m, e => .refl _ _
  | k + 1, m, e => by
      unfold runM
      split
      · rename_i m' e' hs
        exact .more (stepM_sound hs) (runM_sound k m' e')
      · exact .refl _ _

/-- **A computed run to a value is a run of Core's machine to that value.** -/
theorem runM_val {k : ℕ} {m m' : LMem} {e : Expr} {v : Val} (h : runM k m e = (m', v.1)) :
    Steps (ℍ := ℍ) m.heap e m'.heap (.val v) := by
  have hs := runM_sound (ℍ := ℍ) k m e
  rw [h] at hs
  exact hs

end BoCa.Fig16.LogRel.Core

end
