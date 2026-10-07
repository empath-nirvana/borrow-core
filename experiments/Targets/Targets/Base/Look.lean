import Support.Dynamics.Interpreter
import Targets.Base.Runs

/-!
# Base — where a term's evaluation stands, decided

`look e` finds the evaluation position of `e` and says what is there: `e` is a value, a head step
that keeps every memory and allocates nothing (`red K a a'`: `e = K[a]`, `a ↦ a'`), an operation
that no frame of its context catches (`op r K p n`: `e = K[op p]`, the context free of the name
`n`), or something it does not decide (`stuck`).  It covers the steps a run through handlers,
finalisers and cancels takes (`beta`, `seq`, `letpair`, `case`, `hret`, `hop`, `hunwind`, `uthen`,
`ufin`, `ufinC`, `cfret`, `cferr`, `cancel`, `creraise`) and no step that reads or changes the
memory.  `look_sound` states what each answer means in Core's terms (`Head`, `opE`, `OpFree`).

`look` is computed by the kernel, so the run of a closed program through these steps is a
computation (`lookRun`), and each of its steps is a `Head` step at a context (`lookRun_sound`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE ccatchE cfinE
  hndVal cancelVal kappa clauseAt namesVal errVal errNext)

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

theorem namesOf_some : ∀ (x : Expr) (N : List UInt32), namesOf x = some N → x = (namesVal N).1
  | .inj₁ .unit, N, h => by
      simp only [namesOf, Option.some.injEq] at h
      subst h; rfl
  | .inj₂ (.pair (.prim (.lit (.i32 m))) r), N, h => by
      simp only [namesOf, Option.map_eq_some_iff] at h
      obtain ⟨N', hN', rfl⟩ := h
      rw [namesOf_some r N' hN']
      rfl
  | .var _, _, h | .unit, _, h | .pair _ _, _, h | .lam _, _, h | .loc _, _, h | .prim _, _, h
  | .seq _ _, _, h | .letpair _ _, _, h | .case _ _ _, _, h | .app _ _, _, h => by
      simp [namesOf] at h
  | .inj₁ (.var _), _, h | .inj₁ (.pair _ _), _, h | .inj₁ (.inj₁ _), _, h
  | .inj₁ (.inj₂ _), _, h | .inj₁ (.lam _), _, h | .inj₁ (.loc _), _, h | .inj₁ (.prim _), _, h
  | .inj₁ (.seq _ _), _, h | .inj₁ (.letpair _ _), _, h | .inj₁ (.case _ _ _), _, h
  | .inj₁ (.app _ _), _, h => by simp [namesOf] at h
  | .inj₂ (.var _), _, h | .inj₂ .unit, _, h | .inj₂ (.inj₁ _), _, h | .inj₂ (.inj₂ _), _, h
  | .inj₂ (.lam _), _, h | .inj₂ (.loc _), _, h | .inj₂ (.prim _), _, h | .inj₂ (.seq _ _), _, h
  | .inj₂ (.letpair _ _), _, h | .inj₂ (.case _ _ _), _, h | .inj₂ (.app _ _), _, h => by
      simp [namesOf] at h
  | .inj₂ (.pair (.var _) _), _, h | .inj₂ (.pair .unit _), _, h
  | .inj₂ (.pair (.pair _ _) _), _, h | .inj₂ (.pair (.inj₁ _) _), _, h
  | .inj₂ (.pair (.inj₂ _) _), _, h | .inj₂ (.pair (.lam _) _), _, h
  | .inj₂ (.pair (.loc _) _), _, h | .inj₂ (.pair (.seq _ _) _), _, h
  | .inj₂ (.pair (.letpair _ _) _), _, h | .inj₂ (.pair (.case _ _ _) _), _, h
  | .inj₂ (.pair (.app _ _) _), _, h => by simp [namesOf] at h
  | .inj₂ (.pair (.prim (.lit (.i64 _))) _), _, h | .inj₂ (.pair (.prim (.lit (.u8 _))) _), _, h
  | .inj₂ (.pair (.prim .alloc) _), _, h | .inj₂ (.pair (.prim .free) _), _, h
  | .inj₂ (.pair (.prim .load) _), _, h | .inj₂ (.pair (.prim .store) _), _, h
  | .inj₂ (.pair (.prim (.host _)) _), _, h | .inj₂ (.pair (.prim .tab) _), _, h
  | .inj₂ (.pair (.prim .idx) _), _, h | .inj₂ (.pair (.prim .drop) _), _, h
  | .inj₂ (.pair (.prim .split) _), _, h | .inj₂ (.pair (.prim .count) _), _, h
  | .inj₂ (.pair (.prim .countTry) _), _, h | .inj₂ (.pair (.prim .boundedFix) _), _, h
  | .inj₂ (.pair (.prim .perform) _), _, h | .inj₂ (.pair (.prim .raise) _), _, h
  | .inj₂ (.pair (.prim .hnd) _), _, h | .inj₂ (.pair (.prim .ubind) _), _, h
  | .inj₂ (.pair (.prim .ccatch) _), _, h | .inj₂ (.pair (.prim .cfin) _), _, h => by
      simp [namesOf] at h

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

/-- The state `(N, err)` of a cancel payload. -/
def cancelOf? (e : Expr) : Option (List UInt32 × Option Val) :=
  match payOf? e with
  | some (0, 0, w) =>
      match w.1 with
      | .pair x y =>
          match namesOf x, BoCa.errOf y with
          | some N, some err => some (N, err)
          | _, _ => none
      | _ => none
  | _ => none

theorem cancelOf?_some {e : Expr} {N : List UInt32} {err : Option Val}
    (h : cancelOf? e = some (N, err)) : e = (cancelVal N err).1 := by
  unfold cancelOf? at h
  split at h
  · rename_i w hw
    rw [payOf?_some hw]
    split at h
    · rename_i x y hxy
      split at h
      · rename_i N' err' hN herr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hw' : w = Val.pair (namesVal N') (errVal err') :=
          Subtype.ext (by rw [hxy, namesOf_some x N' hN, errOf_some y err' herr]; rfl)
        rw [hw']; rfl
      · cases h
    · cases h
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
def catchOp (f arg : Expr) (r : Bool) (K : Kont) (p : Val) (n : UInt32) : Look :=
  if cond r ((Kont.appR f .hole).Catches n) ((Kont.appR f .hole).HasHnd n) = false then
    .op r (.appR f K) p n
  else
    match f, r with
    | .app (.prim .hnd) (.pair (.prim (.lit (.i32 _))) (.pair hr hs)), r =>
        match valOf? hr, valOf? hs, payOf? p.1 with
        | some hrv, some hsv, some (_, i, w) =>
            match clauseOf hs i.toNat with
            | some c =>
                if r then .red .hole (.app f arg) (.app c.1 w.1)
                else .red .hole (.app f arg) (.app c.1 (.pair w.1 (kappa n (hndVal n hrv hsv) K)))
            | none => .stuck
        | _, _, _ => .stuck
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
        | some (_, none) => .red .hole (.app f arg) (.val .unit)
        | some (_, some E) => .red .hole (.app f arg) (raiseE (.val E))
        | none => .stuck
    | .app (.prim .cfin) s, true =>
        match cancelOf? s, payOf? p.1 with
        | some (N, err), some (m, j, w) =>
            .red .hole (.app f arg) (raiseE (.val (cancelVal N (errNext N err m j w))))
        | _, _ => .stuck
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
          | .op r K p n => catchOp f a r K p n
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
          | .app (.prim .hnd) (.pair (.prim (.lit (.i32 _))) (.pair hr hs)) =>
              match valOf? hr, valOf? hs with
              | some _, some _ => .red .hole (.app f a) (.app hr a)
              | _, _ => .stuck
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

theorem catchOp_sound {f a : Expr} {r : Bool} {K : Kont} {p : Val} {n : UInt32}
    (ha : a = K.plug (opE r p)) (hn : payloadName p = some n) (hK : OpFree r n K) :
    LookOK (ℍ := ℍ) (.app f a) (catchOp f a r K p n) := by
  subst ha
  unfold catchOp
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
      rename_i rr m hr hs
      split
      · rename_i hrv hsv n' i w hhr hhs hpay
        have hm : m = n := by
          cases r <;> simp [Kont.Catches, Kont.HasHnd] at hcatch <;> exact hcatch
        subst hm
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
            exact Head.hunwind μ _ i hrv hsv c w K hc' (by simpa [OpFree] using hK)
          · rename_i hr'
            simp only [Bool.not_eq_true] at hr'
            subst hr'
            refine ⟨rfl, fun μ => ?_, rfl⟩
            exact Head.hop μ _ i hrv hsv c w K hc' (by simpa [OpFree] using hK)
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
          · rename_i st hst
            obtain ⟨Ns, err⟩ := st
            have hp' : p = cancelVal Ns err := Subtype.ext (cancelOf?_some hst)
            subst hp'
            refine ⟨rfl, fun μ => ?_, rfl⟩
            exact Head.ufinC μ Nv Dv Ns err K (by simpa [OpFree] using hK)
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
      · rename_i Ns hst
        have hp' : p = cancelVal Ns none := Subtype.ext (cancelOf?_some hst)
        subst hp'
        refine ⟨rfl, fun μ => ?_, rfl⟩
        exact Head.cancel μ Ns K (by simpa [OpFree] using hK)
      · rename_i Ns E hst
        have hp' : p = cancelVal Ns (some E) := Subtype.ext (cancelOf?_some hst)
        subst hp'
        refine ⟨rfl, fun μ => ?_, rfl⟩
        exact Head.creraise μ Ns E K (by simpa [OpFree] using hK)
      · trivial
    · -- a cancel-mode finaliser frame, at a raise
      rename_i s
      split
      · rename_i N err m j w hst hpay
        have hs := cancelOf?_some hst
        subst hs
        have hp' : p = opPayload m j w := Subtype.ext (payOf?_some hpay)
        subst hp'
        simp only [payloadName_opPayload, Option.some.injEq] at hn
        subst hn
        refine ⟨rfl, fun μ => ?_, rfl⟩
        exact Head.cferr μ N err m j w K (by simpa [OpFree] using hK)
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
          exact catchOp_sound rfl hp hK
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
        · rename_i m hr hs
          split
          · rename_i hrv hsv hhr hhs
            obtain rfl := valOf?_some hhr
            obtain rfl := valOf?_some hhs
            exact ⟨rfl, fun μ => Head.hret μ m hrv hsv va, rfl⟩
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
          · rename_i c hc
            obtain ⟨Ns, err⟩ := c
            have hs := cancelOf?_some hc
            subst hs
            exact ⟨rfl, fun μ => Head.cfret μ Ns err va, rfl⟩
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

end Targets

end
