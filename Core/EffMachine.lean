import Core.EffCancel

/-!
# Core — the handler laws as machine lemmas  `[spec §19, §25]`

The deep handler laws at the capture cell, and an abort's absorption of the frames it passes, as
facts of Core's machine (`Head`, `Step1`, `Steps`), in every evaluation context.  A law is a step
that is its configuration's only step (`Step1Only`: unique decomposition and determinism,
`step1Only_plug`), or a run of such steps; where the machine allocates, at every free location.

* **H-ret** (`catch_ret`): `hnd (n, H) v` steps to `h_ret v`.
* **H-op** (`catch_step`): the catch of `perform (n, (i, v))` hands the clause `c` the argument and
  `κ`, keeping the store.  At an unrestricted operation `κ` is `kappa H K` (`catch_unr`).  At a
  must-resume or cancellable one the next two steps allocate `κ`'s cell at a location `ℓ` the memory
  does not hold, any such, and make `κ` `kappaC` at `ℓ`, cancellable exactly at a cancellable
  operation (`catch_cell`); every run from the catch is a prefix of those three steps or goes on
  from them (`catchEv_cell`).
* **Deep resume and cancel at the cell.**  Resuming `kappaC` at `ℓ` releases `ℓ` and runs
  `hnd (n, H) K[w]` (`kappaC_resume`): three steps reach the release, and after it `κ` resumes as
  `kappa` does (`kappaC_resume_parts`, `kappa_resume_kResume`).  Cancelling a cancellable `κ`
  releases `ℓ` and runs `κ`'s cancel run (`kappaC_cancel`, `kappaC_cancel_parts`); a must-resume
  `κ`'s cancel branch has no step (`kappaC_cancel_lin`).  On a run to a value, a use of `κ` at its
  cell releases the cell three steps later (`use_frees_cell`).
* **H-fwd** (`catch_fwd`): an operation passes a handler of another name, which takes no step on
  it; the nearest handler of its name catches it, and `κ` holds the passed handler, so resuming
  `κ` reinstalls both (`fwd_resume`).  An abortive operation steps as if the passed handler were
  not there (`fwd_abort`).
* **`[unwind]`, `[then]`, `[finalise]`** (`catch_abort`, `then_ret`, `then_fin`).
* **A2** (`abort_absorbs`): `raise p` under frames that catch nothing of its name steps, in every
  context, exactly as `raise p` steps there, the frame that catches it dropping them:
  `raise e to x. N = raise e` (`abort_to`) and `(raise e) w = raise e` (`abort_app`).

The facts they read: a stuck redex takes no step (`StuckAt`, `stuck_no_step`); the steps of an
allocation and of a release (`step1_alloc_iff`, `step1_free_iff`); an operation whose context
catches nothing of it takes no step (`opPlug_no_step`); and a redex that holds a raise is a frame
that catches it, its step the same around every context that catches nothing of its name
(`head_raise_ctx`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.BoLo (Heap Steps Step1 Head Kont hndE hndVal performE raiseE ubindE ccatchE cfinE
  opPayload clauseAt capTag cancelVal kappa kappaAt kappaC kappaCBody kappaCell freeE stuckE)

/-! ### A configuration's only step -/

/-- `(μ, e)` steps to `(μ', e')`, and that is its only step. -/
def Step1Only (μ : Heap) (e : Expr) (μ' : Heap) (e' : Expr) : Prop :=
  Step1 (ℍ := ℍ) μ e μ' e' ∧ ∀ μ₂ e₂, Step1 (ℍ := ℍ) μ e μ₂ e₂ → μ₂ = μ' ∧ e₂ = e'

/-- **A head step that allocates nothing is its configuration's only step**, in every
context. -/
theorem step1Only_plug {μ μ' : Heap} {a a' : Expr} (hh : Head (ℍ := ℍ) μ a μ' a')
    (hn : a.allocs = false) (K : Kont) : Step1Only (ℍ := ℍ) μ (K.plug a) μ' (K.plug a') := by
  refine ⟨⟨K, a, a', rfl, rfl, hh⟩, fun μ₂ e₂ h => ?_⟩
  obtain ⟨K', b, b', he, rfl, hb⟩ := h
  obtain ⟨rfl, rfl⟩ := plug_decomp hb K K' hh he
  obtain ⟨h₁, h₂⟩ := head_det hh hn hb rfl
  exact ⟨h₁.symm, by rw [h₂]⟩

/-- A run from a configuration with one step is empty, or goes on from that step. -/
theorem Step1Only.steps {μ μ₁ μ' : Heap} {e e₁ E : Expr} (h : Step1Only (ℍ := ℍ) μ e μ₁ e₁)
    (hs : Steps (ℍ := ℍ) μ e μ' E) : (μ' = μ ∧ E = e) ∨ Steps (ℍ := ℍ) μ₁ e₁ μ' E := by
  cases hs with
  | refl => exact .inl ⟨rfl, rfl⟩
  | more h' t =>
      obtain ⟨rfl, rfl⟩ := h.2 _ _ h'
      exact .inr t

/-- A run to a value from a configuration with one step goes on from that step. -/
theorem Step1Only.steps_val {μ μ₁ μ' : Heap} {e e₁ : Expr} {v : Val}
    (h : Step1Only (ℍ := ℍ) μ e μ₁ e₁) (hnv : ¬ IsVal e) (hs : Steps (ℍ := ℍ) μ e μ' (.val v)) :
    Steps (ℍ := ℍ) μ₁ e₁ μ' (.val v) := by
  rcases h.steps hs with ⟨-, he⟩ | h'
  · exact absurd (he ▸ v.2) hnv
  · exact h'

/-! ### Stuck redexes -/

/-- `s` is a stuck redex: not a value, reduced by no head rule, every proper evaluation subterm of
it a value, and neither an operation nor an inert primitive applied to a value. -/
structure StuckAt (s : Expr) : Prop where
  not_val : ¬ IsVal s
  no_head : ∀ μ μ' a', ¬ Head (ℍ := ℍ) μ s μ' a'
  subs : ∀ (K : Kont) (a : Expr), s = K.plug a → K ≠ .hole → IsVal a
  not_op : ∀ (r : Bool) (p : Val), s ≠ opE r p
  not_inert : ∀ (p : Prim) (H : Val), p.Inert → s ≠ .app (.val (.prim p)) (.val H)

/-- A proper evaluation subterm of an operation is a value. -/
theorem isVal_of_plug_opE {K : Kont} {s : Expr} {r : Bool} {p : Val}
    (h : K.plug s = opE r p) (hK : K ≠ .hole) : IsVal s := by
  rw [opE_eq_app] at h
  cases K with
  | hole => exact absurd rfl hK
  | appR f K =>
      simp only [Kont.plug, Expr.app.injEq] at h
      exact K.isVal_of_plug (by rw [h.2]; exact p.2)
  | appL K v =>
      simp only [Kont.plug, Expr.app.injEq] at h
      have h1 := h.1
      cases K <;> simp [Kont.plug] at h1
      rw [h1]; exact .prim
  | _ => simp [Kont.plug] at h

/-- A stuck redex and an operation are never both at evaluation positions of one term. -/
theorem stuck_ne_op {s : Expr} (hs : StuckAt (ℍ := ℍ) s) (K K' : Kont) (r : Bool) (p : Val) :
    K.plug s ≠ K'.plug (opE r p) := by
  intro h
  rcases plug_cmp K K' hs.not_val (opE_not_isVal r p) h with ⟨K'', h₁, -⟩ | ⟨K'', h₁, -⟩
  · by_cases h0 : K'' = .hole
    · subst h0; exact hs.not_op r p h₁
    · exact opE_not_isVal r p (hs.subs K'' _ h₁ h0)
  · by_cases h0 : K'' = .hole
    · subst h0; exact hs.not_op r p h₁.symm
    · exact hs.not_val (isVal_of_plug_opE h₁.symm h0)

/-- **A term holding a stuck redex at an evaluation position takes no step.** -/
theorem stuck_no_step {s : Expr} (hs : StuckAt (ℍ := ℍ) s) (K : Kont) {μ μ' : Heap} {t : Expr} :
    ¬ Step1 (ℍ := ℍ) μ (K.plug s) μ' t := by
  rintro ⟨K', a, a', hE, -, hh⟩
  rcases plug_cmp K K' hs.not_val hh.not_isVal hE with ⟨K'', h₁, -⟩ | ⟨K'', h₁, -⟩
  · by_cases h0 : K'' = .hole
    · subst h0; simp only [Kont.plug] at h₁; subst h₁; exact hs.no_head _ _ _ hh
    · exact hh.not_isVal (hs.subs K'' a h₁ h0)
  · by_cases h0 : K'' = .hole
    · subst h0; simp only [Kont.plug] at h₁; subst h₁; exact hs.no_head _ _ _ hh
    have hbody : ∀ (K₃ : Kont) (w : Val), K₃.plug s ≠ w.1 := fun K₃ w h =>
      hs.not_val (K₃.isVal_of_plug (by rw [h]; exact w.2))
    rcases head_plug hh K'' hs.not_val h₁ h0 with
      ⟨n, qs, hr, hs', K₃, rfl⟩ | ⟨N, D, K₃, rfl⟩ | ⟨K₃, rfl⟩ | ⟨w, H, q, hq, rfl, he⟩ |
        ⟨err, K₃, rfl⟩
    · generalize hX :
        (Kont.appR (.app (.val (.prim .hnd)) (.val (hndVal n qs hr hs'))) K₃).plug s = X at h₁
      subst h₁
      cases hh with
      | hret _ _ _ _ w =>
          simp only [hndE, Kont.plug, Expr.app.injEq] at hX; exact hbody K₃ w hX.2
      | hop n' i _ _ _ _ v K₀ =>
          simp only [hndE, Kont.plug, Expr.app.injEq] at hX
          exact stuck_ne_op hs K₃ K₀ false (opPayload n' i v) hX.2
      | hunwind n' i _ _ _ _ v K₀ =>
          simp only [hndE, Kont.plug, Expr.app.injEq] at hX
          exact stuck_ne_op hs K₃ K₀ true (opPayload n' i v) hX.2
      | _ => simp_all [Kont.plug, ubindE, ccatchE, cfinE]
    · generalize hX : (Kont.appR (.app (.val (.prim .ubind)) (.val (Val.pair N D))) K₃).plug s = X
        at h₁
      subst h₁
      cases hh with
      | uthen _ _ w =>
          simp only [ubindE, Kont.plug, Expr.app.injEq] at hX; exact hbody K₃ w hX.2
      | ufin _ _ n i v K₀ =>
          simp only [ubindE, Kont.plug, Expr.app.injEq] at hX
          exact stuck_ne_op hs K₃ K₀ true (opPayload n i v) hX.2
      | ufinC _ _ err K₀ =>
          simp only [ubindE, Kont.plug, Expr.app.injEq] at hX
          exact stuck_ne_op hs K₃ K₀ true (cancelVal err) hX.2
      | _ => simp_all [Kont.plug, hndE, ccatchE, cfinE]
    · generalize hX : (Kont.appR (.val (.prim .ccatch)) K₃).plug s = X at h₁
      subst h₁
      cases hh with
      | cancel K₀ =>
          simp only [ccatchE, Kont.plug, Expr.app.injEq] at hX
          exact stuck_ne_op hs K₃ K₀ true (cancelVal none) hX.2
      | creraise E K₀ =>
          simp only [ccatchE, Kont.plug, Expr.app.injEq] at hX
          exact stuck_ne_op hs K₃ K₀ true (cancelVal (some E)) hX.2
      | _ => simp_all [Kont.plug, hndE, ubindE, cfinE]
    · exact hs.not_inert q H hq he
    · generalize hX : (Kont.appR (.app (.val (.prim .cfin)) (.val (cancelVal err))) K₃).plug s = X
        at h₁
      subst h₁
      cases hh with
      | cferr _ m j w K₀ =>
          simp only [cfinE, Kont.plug, Expr.app.injEq] at hX
          exact stuck_ne_op hs K₃ K₀ true (opPayload m j w) hX.2
      | cfcancel _ err' K₀ =>
          simp only [cfinE, Kont.plug, Expr.app.injEq] at hX
          exact stuck_ne_op hs K₃ K₀ true (cancelVal err') hX.2
      | cfret _ w =>
          simp only [cfinE, Kont.plug, Expr.app.injEq] at hX; exact hbody K₃ w hX.2
      | _ => simp_all [Kont.plug, hndE, ubindE, ccatchE]

/-- `()` applied to a value is a stuck redex: `stuckE` among them. -/
theorem stuckAt_unit_app (x : Val) : StuckAt (ℍ := ℍ) (.app .unit x.1) where
  not_val := by simp
  no_head := by
    intro μ μ' a' h
    generalize hE : Expr.app .unit x.1 = E at h
    cases h <;> simp_all [hndE, ubindE, ccatchE, cfinE]
  subs := by
    intro K a h hK
    cases K with
    | hole => exact absurd rfl hK
    | appR f K =>
        simp only [Kont.plug, Expr.app.injEq] at h
        exact K.isVal_of_plug (by rw [← h.2]; exact x.2)
    | appL K v =>
        simp only [Kont.plug, Expr.app.injEq] at h
        have h1 := h.1
        cases K <;> simp [Kont.plug] at h1
        rw [← h1]; exact .unit
    | _ => simp [Kont.plug] at h
  not_op := by intro r p h; cases r <;> simp [opE, raiseE, performE] at h
  not_inert := by intro p H _ h; simp at h

/-- `case` at a value that is no injection is a stuck redex. -/
theorem stuckAt_case {v : Val} (hv : ∀ a, v.1 ≠ .inj₁ a ∧ v.1 ≠ .inj₂ a) (e₁ e₂ : Expr) :
    StuckAt (ℍ := ℍ) (.case v.1 e₁ e₂) where
  not_val := by simp
  no_head := by
    intro μ μ' a' h
    generalize hE : Expr.case v.1 e₁ e₂ = E at h
    cases h with
    | case₁ w _ _ =>
        simp only [Expr.case.injEq] at hE
        exact (hv _).1 hE.1
    | case₂ w _ _ =>
        simp only [Expr.case.injEq] at hE
        exact (hv _).2 hE.1
    | _ => simp_all [hndE, ubindE, ccatchE, cfinE]
  subs := by
    intro K a h hK
    cases K with
    | hole => exact absurd rfl hK
    | case K _ _ =>
        simp only [Kont.plug, Expr.case.injEq] at h
        exact K.isVal_of_plug (by rw [← h.1]; exact v.2)
    | _ => simp [Kont.plug] at h
  not_op := by intro r p h; cases r <;> simp [opE, raiseE, performE] at h
  not_inert := by intro p H _ h; simp at h

/-- `v; e` at a value other than `()` is a stuck redex. -/
theorem stuckAt_seq {w : Val} (hw : w.1 ≠ .unit) (e : Expr) : StuckAt (ℍ := ℍ) (.seq w.1 e) where
  not_val := by simp
  no_head := by
    intro μ μ' a' h
    generalize hE : Expr.seq w.1 e = E at h
    cases h with
    | seq _ =>
        simp only [Expr.seq.injEq] at hE
        exact hw hE.1
    | _ => simp_all [hndE, ubindE, ccatchE, cfinE]
  subs := by
    intro K a h hK
    cases K with
    | hole => exact absurd rfl hK
    | seq K _ =>
        simp only [Kont.plug, Expr.seq.injEq] at h
        exact K.isVal_of_plug (by rw [← h.1]; exact w.2)
    | _ => simp [Kont.plug] at h
  not_op := by intro r p h; cases r <;> simp [opE, raiseE, performE] at h
  not_inert := by intro p H _ h; simp at h

/-- No run to a value passes a configuration holding a stuck redex. -/
theorem stuck_not_steps_val {s : Expr} (hs : StuckAt (ℍ := ℍ) s) (K : Kont) {μ μ' : Heap}
    {v : Val} : ¬ Steps (ℍ := ℍ) μ (K.plug s) μ' (.val v) := by
  intro h
  generalize hE : Expr.val v = E at h
  cases h with
  | refl => exact hs.not_val (K.isVal_of_plug (hE ▸ v.2))
  | more h _ => exact stuck_no_step hs K h

/-! ### Allocation and release -/

/-- An allocation's head steps: `v` at a location the memory does not hold. -/
theorem head_alloc_inv {μ μ' : Heap} {v : Val} {a' : Expr}
    (h : Head (ℍ := ℍ) μ (.app (.val (.prim .alloc)) (.val v)) μ' a') :
    ∃ ℓ, μ ℓ = none ∧ μ' = μ.upd ℓ v ∧ a' = .val (.loc ℓ) := by
  generalize hb : Expr.app (.val (.prim .alloc)) (.val v) = b at h
  cases h with
  | alloc w ℓ hℓ =>
      simp only [Expr.val, Val.prim, Expr.app.injEq, true_and] at hb
      obtain rfl : v = w := Subtype.ext hb
      exact ⟨ℓ, hℓ, rfl, rfl⟩
  | _ => simp_all [hndE, ubindE, ccatchE, cfinE, Expr.val, Val.prim]

/-- **The steps of an allocation**, in every context: each allocates `v` at a location the memory
does not hold. -/
theorem step1_alloc_iff {μ μ₁ : Heap} {e₁ : Expr} (K : Kont) (v : Val) :
    Step1 (ℍ := ℍ) μ (K.plug (.app (.val (.prim .alloc)) (.val v))) μ₁ e₁ ↔
      ∃ ℓ, μ ℓ = none ∧ μ₁ = μ.upd ℓ v ∧ e₁ = K.plug (.val (.loc ℓ)) := by
  constructor
  · rintro ⟨K', b, b', he, rfl, hb⟩
    obtain ⟨rfl, rfl⟩ := plug_decomp hb K K'
      (Head.alloc (ℍ := ℍ) (fun _ => none) v 0 rfl) he
    obtain ⟨ℓ, hℓ, rfl, rfl⟩ := head_alloc_inv hb
    exact ⟨ℓ, hℓ, rfl, rfl⟩
  · rintro ⟨ℓ, hℓ, rfl, rfl⟩
    exact ⟨K, _, _, rfl, rfl, Head.alloc μ v ℓ hℓ⟩

/-- A release's head steps: a location the memory holds, answering its contents. -/
theorem head_free_inv {μ μ' : Heap} {ℓ : Loc} {a' : Expr}
    (h : Head (ℍ := ℍ) μ (freeE (.val (Val.loc ℓ))) μ' a') :
    ∃ u, μ ℓ = some u ∧ μ' = μ.del ℓ ∧ a' = .val u := by
  generalize hb : freeE (.val (Val.loc ℓ)) = b at h
  cases h with
  | free k u hk =>
      simp only [freeE, Expr.val, Val.prim, Val.loc, Expr.app.injEq, Expr.loc.injEq,
        true_and] at hb
      subst hb
      exact ⟨u, hk, rfl, rfl⟩
  | _ => simp_all [freeE, hndE, ubindE, ccatchE, cfinE, Expr.val, Val.prim]

/-- **The steps of a release**, in every context: it releases a location the memory holds, and
answers its contents; at a location the memory does not hold there is none. -/
theorem step1_free_iff {μ μ₁ : Heap} {e₁ : Expr} (K : Kont) (ℓ : Loc) :
    Step1 (ℍ := ℍ) μ (K.plug (freeE (.val (Val.loc ℓ)))) μ₁ e₁ ↔
      ∃ u, μ ℓ = some u ∧ μ₁ = μ.del ℓ ∧ e₁ = K.plug (.val u) := by
  constructor
  · rintro ⟨K', b, b', he, rfl, hb⟩
    obtain ⟨rfl, rfl⟩ := plug_decomp hb K K'
      (Head.free (ℍ := ℍ) (fun _ => some Val.unit) ℓ Val.unit rfl) he
    obtain ⟨u, hu, rfl, rfl⟩ := head_free_inv hb
    exact ⟨u, hu, rfl, rfl⟩
  · rintro ⟨u, hu, rfl, rfl⟩
    exact ⟨K, _, _, rfl, rfl, Head.free μ ℓ u hu⟩

/-- A release of a location the memory holds is its configuration's only step. -/
theorem free_step1Only {μ : Heap} {ℓ : Loc} {u : Val} (hℓ : μ ℓ = some u) (K : Kont) :
    Step1Only (ℍ := ℍ) μ (K.plug (freeE (.val (Val.loc ℓ)))) (μ.del ℓ) (K.plug (.val u)) := by
  refine ⟨(step1_free_iff K ℓ).2 ⟨u, hℓ, rfl, rfl⟩, fun μ₂ e₂ h => ?_⟩
  obtain ⟨u', hu', rfl, rfl⟩ := (step1_free_iff K ℓ).1 h
  rw [hℓ] at hu'
  cases hu'
  exact ⟨rfl, rfl⟩

/-! ### `[ret]` and `[op]`: the handler laws H-ret and H-op -/

/-- **H-ret**: `hnd (n, (qs, (h_ret, hs))) w` steps only to `h_ret w`, keeping the store.
`[spec §19]` -/
theorem catch_ret (μ : Heap) (n : UInt32) (qs hr hs w : Val) (K₀ : Kont) :
    Step1Only (ℍ := ℍ) μ (K₀.plug (hndE (hndVal n qs hr hs) (.val w))) μ
      (K₀.plug (.app (.val hr) (.val w))) :=
  step1Only_plug (Head.hret μ n qs hr hs w) rfl K₀

/-- **The catch**: `hnd (n, (qs, H)) K[perform (n, (i, v))]`, `K` free of `n` and `c` the clause
at `i`, steps only to `c (v, κ)`, `κ` by the operation's tag, keeping the store.
`[spec §19, §25]` -/
theorem catch_step (μ : Heap) {n i : UInt32} {qs hr hs c : Val} (v : Val) {K : Kont}
    (hc : clauseAt hs.1 i.toNat = some c) (hK : K.HasHnd n = false) (K₀ : Kont) :
    Step1Only (ℍ := ℍ) μ
      (K₀.plug (hndE (hndVal n qs hr hs) (K.plug (performE (.val (opPayload n i v)))))) μ
      (K₀.plug (.app (.val c) (.pair (.val v)
        (kappaAt (capTag qs.1 i.toNat) (hndVal n qs hr hs) K)))) :=
  step1Only_plug (Head.hop μ n i qs hr hs c v K hc hK) rfl K₀

/-- A continuation at a must-resume or cancellable operation owns a cell; it is cancellable exactly
at a cancellable operation.  `[spec §25]` -/
def cellCancel (q : Qual) : Bool := q == .cancel

/-- The tag of a must-resume or cancellable operation makes `[op]`'s `κ` a cell's.  `[spec §25]` -/
theorem kappaAt_cell {q : Qual} (hq : q ≠ .unr) (H : Val) (K : Kont) :
    kappaAt q.tag H K = kappaCell (cellCancel q) H K := by
  cases q
  · rfl
  · rfl
  · exact absurd rfl hq

/-- **H-op at an unrestricted operation**: the catch hands the clause the argument and
`kappa H K`, and keeps the store; it is the configuration's only step.  `[spec §19, §25]` -/
theorem catch_unr (μ : Heap) {n i : UInt32} {qs hr hs c : Val} (v : Val) {K : Kont}
    (hc : clauseAt hs.1 i.toNat = some c) (hK : K.HasHnd n = false)
    (htag : capTag qs.1 i.toNat = Qual.unr.tag) (K₀ : Kont) :
    Step1Only (ℍ := ℍ) μ
      (K₀.plug (hndE (hndVal n qs hr hs) (K.plug (performE (.val (opPayload n i v)))))) μ
      (K₀.plug (.app (.val c) (.pair (.val v) (kappa (hndVal n qs hr hs) K)))) := by
  have h := catch_step (qs := qs) (hr := hr) μ v hc hK K₀
  rwa [htag, kappaAt_tag] at h

/-- The clause applied to the argument and `κ` before its cell allocates the cell, the only step
of its configuration; this is that configuration, as an allocation in its context. -/
theorem plug_kappaCell (K₀ : Kont) (c v : Val) (hasCancel : Bool) (H : Val) (K : Kont) :
    K₀.plug (.app (.val c) (.pair (.val v) (kappaCell hasCancel H K))) =
      (K₀.comp (.appR (.val c)
          (.pairR v (.appR (.val (Val.lam (kappaCBody hasCancel H K))) .hole)))).plug
        (.app (.val (.prim .alloc)) (.val Val.unit)) := by
  rw [Kont.plug_comp]; rfl

/-- The allocation's answer `ℓ`, back in its configuration: `κ` before its β-step. -/
theorem plug_kappaCellLoc (K₀ : Kont) (c v : Val) (hasCancel : Bool) (H : Val) (K : Kont)
    (ℓ : Loc) :
    (K₀.comp (.appR (.val c)
        (.pairR v (.appR (.val (Val.lam (kappaCBody hasCancel H K))) .hole)))).plug
        (.val (Val.loc ℓ)) =
      K₀.plug (.app (.val c) (.pair (.val v)
        (.app (.val (Val.lam (kappaCBody hasCancel H K))) (.val (Val.loc ℓ))))) := by
  rw [Kont.plug_comp]; rfl

/-- `κ`'s β-step at its cell `ℓ`: the only step of its configuration, to `kappaC` at `ℓ`. -/
theorem kappaCell_beta (μ : Heap) (K₀ : Kont) (c v : Val) (hasCancel : Bool) (ℓ : Loc) (H : Val)
    (K : Kont) :
    Step1Only (ℍ := ℍ) μ
      (K₀.plug (.app (.val c) (.pair (.val v)
        (.app (.val (Val.lam (kappaCBody hasCancel H K))) (.val (Val.loc ℓ)))))) μ
      (K₀.plug (.app (.val c) (.pair (.val v) (kappaC hasCancel ℓ H K)))) := by
  have h := step1Only_plug (Head.beta (ℍ := ℍ) μ (kappaCBody hasCancel H K) (Val.loc ℓ)) rfl
    (K₀.comp (.appR (.val c) (.pairR v .hole)))
  rw [kappaCBody_subst, Kont.plug_comp, Kont.plug_comp] at h
  exact h

/-- **H-op at a must-resume or cancellable operation** (`catch_cell`): the catch hands the clause
the argument and `κ` before its cell, keeping the store; the cell is allocated at a location the
memory does not hold, any such; and `κ`'s β-step makes it `kappaC` there, cancellable exactly at a
cancellable operation.  `[spec §19, §25]` -/
theorem catch_cell {μ : Heap} {ℓ : Loc} (hℓ : μ ℓ = none) {n i : UInt32} {qs hr hs c : Val}
    (v : Val) {K : Kont} {q : Qual} (hq : q ≠ .unr) (hc : clauseAt hs.1 i.toNat = some c)
    (hK : K.HasHnd n = false) (htag : capTag qs.1 i.toNat = q.tag) (K₀ : Kont) :
    Steps (ℍ := ℍ) μ
      (K₀.plug (hndE (hndVal n qs hr hs) (K.plug (performE (.val (opPayload n i v))))))
      (μ.upd ℓ Val.unit)
      (K₀.plug (.app (.val c)
        (.pair (.val v) (kappaC (cellCancel q) ℓ (hndVal n qs hr hs) K)))) := by
  have h₁ := (catch_step (qs := qs) (hr := hr) μ v hc hK K₀).1
  rw [htag, kappaAt_cell hq, plug_kappaCell] at h₁
  have h₂ := (step1_alloc_iff (ℍ := ℍ) (μ := μ)
    (K₀.comp (.appR (.val c) (.pairR v (.appR (.val (Val.lam (kappaCBody (cellCancel q)
      (hndVal n qs hr hs) K))) .hole)))) Val.unit).2 ⟨ℓ, hℓ, rfl, rfl⟩
  rw [plug_kappaCellLoc] at h₂
  exact .more h₁ (.more h₂ (.more (kappaCell_beta _ K₀ c v _ ℓ _ K).1 (.refl _ _)))

/-- **A capture event allocates `κ`'s cell** (`catchEv_cell`).  Every run from a catch of a
must-resume or cancellable operation is a prefix of, or goes on from: the `[op]` step, keeping the
store, to the clause applied to the argument and `κ` before its cell; the allocation of the cell at
a location `ℓ` the memory does not hold; and `κ`'s β-step, which hands the clause `kappaC` at `ℓ`,
cancellable exactly at a cancellable operation.  `[spec §19, §25]` -/
theorem catchEv_cell {μ μ' : Heap} {E : Expr} {n i : UInt32} {qs hr hs c : Val} {v : Val}
    {K : Kont} {q : Qual} (hq : q ≠ .unr) (hc : clauseAt hs.1 i.toNat = some c)
    (hK : K.HasHnd n = false) (htag : capTag qs.1 i.toNat = q.tag) {K₀ : Kont}
    (hrun : Steps (ℍ := ℍ) μ
      (K₀.plug (hndE (hndVal n qs hr hs) (K.plug (performE (.val (opPayload n i v)))))) μ' E) :
    (μ' = μ ∧
      E = K₀.plug (hndE (hndVal n qs hr hs) (K.plug (performE (.val (opPayload n i v)))))) ∨
    (μ' = μ ∧ E = K₀.plug (.app (.val c) (.pair (.val v)
      (kappaCell (cellCancel q) (hndVal n qs hr hs) K)))) ∨
    (∃ ℓ, μ ℓ = none ∧ μ' = μ.upd ℓ Val.unit ∧ E = K₀.plug (.app (.val c) (.pair (.val v)
      (.app (.val (Val.lam (kappaCBody (cellCancel q) (hndVal n qs hr hs) K)))
        (.val (Val.loc ℓ)))))) ∨
    ∃ ℓ, μ ℓ = none ∧ Steps (ℍ := ℍ) (μ.upd ℓ Val.unit)
      (K₀.plug (.app (.val c) (.pair (.val v) (kappaC (cellCancel q) ℓ (hndVal n qs hr hs) K))))
      μ' E := by
  have h₁ := catch_step (ℍ := ℍ) (qs := qs) (hr := hr) μ v hc hK K₀
  rw [htag, kappaAt_cell hq] at h₁
  rcases h₁.steps hrun with ⟨rfl, rfl⟩ | h
  · exact .inl ⟨rfl, rfl⟩
  cases h with
  | refl => exact .inr (.inl ⟨rfl, rfl⟩)
  | more hst t =>
      rw [plug_kappaCell] at hst
      obtain ⟨ℓ, hℓ, rfl, rfl⟩ := (step1_alloc_iff _ _).1 hst
      rw [plug_kappaCellLoc] at t
      rcases (kappaCell_beta (ℍ := ℍ) _ K₀ c v _ ℓ _ K).steps t with ⟨rfl, h₃⟩ | h₃
      · exact .inr (.inr (.inl ⟨ℓ, hℓ, rfl, h₃⟩))
      · exact .inr (.inr (.inr ⟨ℓ, hℓ, h₃⟩))

/-! ### Resuming and cancelling `κ` -/

/-- `κ`'s resume branch once chosen: `λy. hnd H K[y]`, the handler reinstalled around the
captured context.  `[spec §19]` -/
def kResume (H : Val) (K : Kont) : Val :=
  Val.lam (hndE (H.shift 1 0) ((K.shift 1 0).plug (.var 0)))

/-- `κ`'s resume branch, its binders `s` and `u` substituted, is `kResume`. -/
theorem subst_kResume (H : Val) (K : Kont) (s u : Val) :
    Expr.subst 0 u (Expr.subst 1 s
      (.val (.lam (hndE (H.shift 3 0) ((K.shift 3 0).plug (.var 0)))))) = (kResume H K).1 := by
  simp only [kResume, hndE, Expr.subst, Expr.val, Val.val_lam, Val.val_shift]
  rw [Expr.subst_shift 2 0 2 _ H.1 (by omega) (by omega),
    Expr.subst_shift 1 0 1 _ H.1 (by omega) (by omega),
    plug_shift_subst 2 K 0 2 _ _ (by omega) (by omega),
    plug_shift_subst 1 K 0 1 _ _ (by omega) (by omega)]
  simp [Expr.subst]

/-- **Deep resume**: `kResume H K` applied to `w` is `hnd H K[w]`, by its β-step.  `[spec §19]` -/
theorem kResume_beta (μ : Heap) (H : Val) (K : Kont) (w : Val) :
    Head (ℍ := ℍ) μ (.app (.val (kResume H K)) (.val w)) μ (hndE H (K.plug (.val w))) := by
  have h := Head.beta (ℍ := ℍ) μ (hndE (H.shift 1 0) ((K.shift 1 0).plug (.var 0))) w
  have e : Expr.subst 0 w (hndE (H.shift 1 0) ((K.shift 1 0).plug (.var 0))) =
      hndE H (K.plug (.val w)) := by
    simp only [hndE, Expr.subst, Expr.val, Val.val_shift]
    rw [Expr.subst_shift 0 0 0 w H.1 (by omega) (by omega), Expr.shift_zero,
      plug_shift_subst 0 K 0 0 w _ (by omega) (by omega), Kont.shift_zero]
    simp [Expr.subst]
  rw [e] at h
  exact h

/-- **Resuming `κ` with no cell** chooses its resume branch in three steps that keep every store,
reaching `kResume H K` applied to `w`; its β-step is `kappa_resume_steps`'s last.  `[spec §19]` -/
theorem kappa_resume_kResume (μ : Heap) (H : Val) (K : Kont) (w : Val) :
    Steps (ℍ := ℍ) μ (.app (.app (kappa H K) (.val (Val.inj₁ .unit))) (.val w)) μ
      (.app (.val (kResume H K)) (.val w)) := by
  refine .more ((Step1.head (Head.beta μ _ _)).plug (.appL .hole w)) ?_
  refine .more ((Step1.head (Head.case₁ μ Val.unit _ _)).plug (.appL .hole w)) ?_
  refine .more ((Step1.head (Head.seq μ _)).plug (.appL .hole w)) ?_
  simp only [Kont.plug]
  rw [subst_kResume]
  exact .refl _ _

/-- `κ`'s resume branch at its cell `ℓ`, under its binders `s` and `u`:
`u; free ℓ; λy. hnd H K[y]`.  `[spec §25]` -/
def kResBr (ℓ : Loc) (H : Val) (K : Kont) : Expr :=
  .seq (.var 0) (.seq (freeE (.val (.loc ℓ)))
    (.val (.lam (hndE (H.shift 3 0) ((K.shift 3 0).plug (.var 0))))))

/-- `κ`'s cancel branch at its cell `ℓ`, under its binders `s` and `u`: at a cancellable operation
`u; free ℓ; ccatch (K†[raise (0, (0, none))])`, at a must-resume one `() ()`.  `[spec §25]` -/
def kCanBr (hasCancel : Bool) (ℓ : Loc) (K : Kont) : Expr :=
  if hasCancel then
    .seq (.var 0) (.seq (freeE (.val (.loc ℓ)))
      (ccatchE ((K.dead.shift 2 0).plug (raiseE (.val (cancelVal none))))))
  else stuckE

/-- `κ` at its cell is `λs. case s {inj₁ u. resume branch | inj₂ u. cancel branch}`. -/
theorem kappaC_eq (hasCancel : Bool) (ℓ : Loc) (H : Val) (K : Kont) :
    kappaC hasCancel ℓ H K = .lam (.case (.var 0) (kResBr ℓ H K) (kCanBr hasCancel ℓ K)) := rfl

/-- The resume branch at `inj₁ a`: `a; free ℓ; kResume H K`. -/
theorem subst_kResBr (ℓ : Loc) (H : Val) (K : Kont) (s a : Val) :
    Expr.subst 0 a (Expr.subst 1 s (kResBr ℓ H K)) =
      .seq (.val a) (.seq (freeE (.val (Val.loc ℓ))) (kResume H K).1) := by
  have e := subst_kResume H K s a
  simp only [kResBr, Expr.subst] at e ⊢
  rw [e]
  rfl

/-- The cancel branch of a cancellable `κ` at `inj₂ a`:
`a; free ℓ; ccatch (K†[raise (0, (0, none))])`. -/
theorem subst_kCanBr_cancel (ℓ : Loc) (K : Kont) (s a : Val) :
    Expr.subst 0 a (Expr.subst 1 s (kCanBr true ℓ K)) =
      .seq (.val a) (.seq (freeE (.val (Val.loc ℓ)))
        (ccatchE (K.dead.plug (raiseE (.val (cancelVal none)))))) := by
  have e := kappa_cancel_subst K s a
  simp only [kCanBr, if_true, Expr.subst] at e ⊢
  rw [e]
  rfl

/-- The cancel branch of a must-resume `κ`: `() ()`. -/
theorem subst_kCanBr_lin (ℓ : Loc) (K : Kont) (s a : Val) :
    Expr.subst 0 a (Expr.subst 1 s (kCanBr false ℓ K)) = stuckE := rfl

/-- `κ` at its cell applied to `w` takes its β-step, its configuration's only step, to the
`case` on `w`. -/
theorem kappaC_beta (μ : Heap) (hasCancel : Bool) (ℓ : Loc) (H : Val) (K : Kont) (w : Val)
    (K₀ : Kont) :
    Step1Only (ℍ := ℍ) μ (K₀.plug (.app (kappaC hasCancel ℓ H K) (.val w))) μ
      (K₀.plug (.case (.val w) (Expr.subst 1 (w.shift 1 0) (kResBr ℓ H K))
        (Expr.subst 1 (w.shift 1 0) (kCanBr hasCancel ℓ K)))) :=
  step1Only_plug (Head.beta μ (.case (.var 0) (kResBr ℓ H K) (kCanBr hasCancel ℓ K)) w) rfl K₀

/-- At `inj₁ a`, the `case` chooses the resume branch: `a; free ℓ; kResume H K`. -/
theorem kappaC_case₁ (μ : Heap) (hasCancel : Bool) (ℓ : Loc) (H : Val) (K : Kont) (s a : Val)
    (K₀ : Kont) :
    Step1Only (ℍ := ℍ) μ (K₀.plug (.case (.val (Val.inj₁ a)) (Expr.subst 1 s (kResBr ℓ H K))
        (Expr.subst 1 s (kCanBr hasCancel ℓ K)))) μ
      (K₀.plug (.seq (.val a) (.seq (freeE (.val (Val.loc ℓ))) (kResume H K).1))) := by
  have h := step1Only_plug (ℍ := ℍ)
    (Head.case₁ μ a (Expr.subst 1 s (kResBr ℓ H K)) (Expr.subst 1 s (kCanBr hasCancel ℓ K))) rfl K₀
  rwa [subst_kResBr] at h

/-- At `inj₂ a`, the `case` chooses the cancel branch. -/
theorem kappaC_case₂ (μ : Heap) (hasCancel : Bool) (ℓ : Loc) (H : Val) (K : Kont) (s a : Val)
    (K₀ : Kont) :
    Step1Only (ℍ := ℍ) μ (K₀.plug (.case (.val (Val.inj₂ a)) (Expr.subst 1 s (kResBr ℓ H K))
        (Expr.subst 1 s (kCanBr hasCancel ℓ K)))) μ
      (K₀.plug (Expr.subst 0 a (Expr.subst 1 s (kCanBr hasCancel ℓ K)))) :=
  step1Only_plug (Head.case₂ μ a _ _) rfl K₀

/-- **Resuming `κ` at its cell `ℓ`** (`kappaC_resume_parts`): three steps that keep every store
choose the resume branch and reach the release of `ℓ`; from the release's answer `()` one step
that keeps every store reaches `kResume H K` applied to `w`, where resuming `kappa H K` stands
after its three steps (`kappa_resume_kResume`).  `[spec §25]` -/
theorem kappaC_resume_parts (hasCancel : Bool) (ℓ : Loc) (H : Val) (K : Kont) (w : Val) :
    (∀ μ, Steps (ℍ := ℍ) μ (.app (.app (kappaC hasCancel ℓ H K) (.val (Val.inj₁ .unit))) (.val w)) μ
      ((Kont.appL (Kont.seq .hole (kResume H K).1) w).plug (freeE (.val (Val.loc ℓ))))) ∧
    (∀ μ, Steps (ℍ := ℍ) μ ((Kont.appL (Kont.seq .hole (kResume H K).1) w).plug (.val Val.unit)) μ
      (.app (.val (kResume H K)) (.val w))) := by
  refine ⟨fun μ => ?_, fun μ => .one ((Step1.head (Head.seq μ _)).plug (.appL .hole w))⟩
  refine .more (kappaC_beta μ hasCancel ℓ H K (Val.inj₁ Val.unit) (.appL .hole w)).1 ?_
  refine .more (kappaC_case₁ μ hasCancel ℓ H K _ Val.unit (.appL .hole w)).1 ?_
  exact .one ((Step1.head (Head.seq μ _)).plug (.appL .hole w))

/-- **H-op's deep resume at a cell** (`kappaC_resume`): at a store holding `ℓ` with `()`, resuming
`kappaC` at `ℓ` releases `ℓ` and runs `hnd H K[w]`, in every context.  `[spec §19, §25]` -/
theorem kappaC_resume {μ : Heap} {ℓ : Loc} (hℓ : μ ℓ = some Val.unit) (hasCancel : Bool) (H : Val)
    (K : Kont) (w : Val) (K₀ : Kont) :
    Steps (ℍ := ℍ) μ
      (K₀.plug (.app (.app (kappaC hasCancel ℓ H K) (.val (Val.inj₁ .unit))) (.val w)))
      (μ.del ℓ) (K₀.plug (hndE H (K.plug (.val w)))) := by
  obtain ⟨h₁, h₂⟩ := kappaC_resume_parts (ℍ := ℍ) hasCancel ℓ H K w
  have hfree := (step1_free_iff (ℍ := ℍ) (μ := μ)
    (K₀.comp (Kont.appL (Kont.seq .hole (kResume H K).1) w)) ℓ).2 ⟨Val.unit, hℓ, rfl, rfl⟩
  rw [Kont.plug_comp, Kont.plug_comp] at hfree
  exact ((h₁ μ).plug K₀).trans (.more hfree (((h₂ _).plug K₀).trans
    (.one ((Step1.head (kResume_beta _ H K w)).plug K₀))))

/-- **Cancelling a cancellable `κ` at its cell `ℓ`** (`kappaC_cancel_parts`): three steps that keep
every store choose the cancel branch and reach the release of `ℓ`; from the release's answer
`()` one step reaches `ccatch (K†[raise (0, (0, none))])`, where cancelling `kappa H K` stands
after its three steps (`kappa_cancel_steps`).  `[spec §25]` -/
theorem kappaC_cancel_parts (ℓ : Loc) (H : Val) (K : Kont) :
    (∀ μ, Steps (ℍ := ℍ) μ (.app (kappaC true ℓ H K) (.val (Val.inj₂ .unit))) μ
      ((Kont.seq .hole (ccatchE (K.dead.plug (raiseE (.val (cancelVal none)))))).plug
        (freeE (.val (Val.loc ℓ))))) ∧
    (∀ μ, Steps (ℍ := ℍ) μ
      ((Kont.seq .hole (ccatchE (K.dead.plug (raiseE (.val (cancelVal none)))))).plug
        (.val Val.unit)) μ (ccatchE (K.dead.plug (raiseE (.val (cancelVal none)))))) := by
  refine ⟨fun μ => ?_, fun μ => .one (Step1.head (Head.seq μ _))⟩
  refine .more (kappaC_beta μ true ℓ H K (Val.inj₂ Val.unit) .hole).1 ?_
  have h := (kappaC_case₂ (ℍ := ℍ) μ true ℓ H K ((Val.inj₂ Val.unit).shift 1 0) Val.unit .hole).1
  rw [subst_kCanBr_cancel] at h
  exact .more h (.one (Step1.head (Head.seq μ _)))

/-- **Cancelling a cancellable `κ` at its cell** (`kappaC_cancel`): at a store holding `ℓ` with
`()`, it releases `ℓ` and runs `κ`'s cancel run `ccatch (K†[raise (0, (0, none))])`, in every
context. `[spec §19, §25]` -/
theorem kappaC_cancel {μ : Heap} {ℓ : Loc} (hℓ : μ ℓ = some Val.unit) (H : Val) (K : Kont)
    (K₀ : Kont) :
    Steps (ℍ := ℍ) μ (K₀.plug (.app (kappaC true ℓ H K) (.val (Val.inj₂ .unit)))) (μ.del ℓ)
      (K₀.plug (ccatchE (K.dead.plug (raiseE (.val (cancelVal none)))))) := by
  obtain ⟨h₁, h₂⟩ := kappaC_cancel_parts (ℍ := ℍ) ℓ H K
  have hfree := (step1_free_iff (ℍ := ℍ) (μ := μ)
    (K₀.comp (Kont.seq .hole (ccatchE (K.dead.plug (raiseE (.val (cancelVal none))))))) ℓ).2
      ⟨Val.unit, hℓ, rfl, rfl⟩
  rw [Kont.plug_comp, Kont.plug_comp] at hfree
  exact ((h₁ μ).plug K₀).trans (.more hfree ((h₂ _).plug K₀))

/-- **A must-resume `κ`'s cancel branch has no step** (`kappaC_cancel_lin`): cancelling `κ` at a
must-resume operation reaches `() ()`, which takes no step in any context.  `[spec §25]` -/
theorem kappaC_cancel_lin (μ : Heap) (ℓ : Loc) (H : Val) (K : Kont) (K₀ : Kont) :
    Steps (ℍ := ℍ) μ (K₀.plug (.app (kappaC false ℓ H K) (.val (Val.inj₂ .unit)))) μ
      (K₀.plug stuckE) ∧ ∀ μ' E, ¬ Step1 (ℍ := ℍ) μ (K₀.plug stuckE) μ' E := by
  refine ⟨.more (kappaC_beta μ false ℓ H K (Val.inj₂ Val.unit) K₀).1
    (.one (kappaC_case₂ μ false ℓ H K _ Val.unit K₀).1), fun μ' E => ?_⟩
  exact stuck_no_step (stuckAt_unit_app Val.unit) K₀

/-- A complete run from `a; free ℓ; R`: `a` is `()` and `ℓ` holds `()`; the run takes the `;`,
keeping the store, then releases `ℓ`, each its configuration's only step, and goes on from
`(); R`. -/
theorem steps_seq_free {μ μ' : Heap} {K₀ : Kont} {a : Val} {ℓ : Loc} {R : Expr} {v : Val}
    (hs : Steps (ℍ := ℍ) μ (K₀.plug (.seq (.val a) (.seq (freeE (.val (Val.loc ℓ))) R))) μ'
      (.val v)) :
    a = Val.unit ∧ μ ℓ = some Val.unit ∧
      Step1Only (ℍ := ℍ) μ (K₀.plug (.seq (.val a) (.seq (freeE (.val (Val.loc ℓ))) R))) μ
        (K₀.plug (.seq (freeE (.val (Val.loc ℓ))) R)) ∧
      Step1Only (ℍ := ℍ) μ (K₀.plug (.seq (freeE (.val (Val.loc ℓ))) R)) (μ.del ℓ)
        (K₀.plug (.seq (.val Val.unit) R)) ∧
      Steps (ℍ := ℍ) (μ.del ℓ) (K₀.plug (.seq (.val Val.unit) R)) μ' (.val v) := by
  have hnv : ∀ (x y : Expr), ¬ IsVal (K₀.plug (.seq x y)) := fun x y h =>
    not_isVal_seq (K₀.isVal_of_plug h)
  by_cases ha : a = Val.unit
  swap
  · exact absurd hs (stuck_not_steps_val (stuckAt_seq (w := a)
      (fun h => ha (Subtype.ext h)) _) K₀)
  subst ha
  have hseq := step1Only_plug (ℍ := ℍ) (Head.seq μ (.seq (freeE (.val (Val.loc ℓ))) R)) rfl K₀
  have hs₁ := hseq.steps_val (hnv _ _) hs
  have hplug : ∀ x, K₀.plug (.seq x R) = (K₀.comp (.seq .hole R)).plug x := fun x => by
    rw [Kont.plug_comp]; rfl
  cases hℓ : μ ℓ with
  | none =>
      exfalso
      rw [hplug] at hs₁
      generalize hE : Expr.val v = E at hs₁
      cases hs₁ with
      | refl => exact hnv _ _ (by rw [hplug, ← hE]; exact v.2)
      | more h _ =>
          obtain ⟨u, hu, -, -⟩ := (step1_free_iff _ ℓ).1 h
          rw [hℓ] at hu
          cases hu
  | some u =>
      have hfr := free_step1Only (ℍ := ℍ) hℓ (K₀.comp (.seq .hole R))
      rw [← hplug, ← hplug] at hfr
      have hs₂ := hfr.steps_val (hnv _ _) hs₁
      by_cases hu : u = Val.unit
      swap
      · exact absurd hs₂ (stuck_not_steps_val (stuckAt_seq (w := u)
          (fun h => hu (Subtype.ext h)) _) K₀)
      subst hu
      exact ⟨rfl, rfl, hseq, hfr, hs₂⟩

/-- **A use of `κ` releases its cell three steps later** (`use_frees_cell`).  On a run to a value
from `κ` at its cell `ℓ` applied to a value `w`, in any context: `w` is `inj₁ ()`, or `inj₂ ()` at
a cancellable `κ` (a must-resume `κ`'s cancel branch has no step); the memory holds `ℓ` with `()`;
and the run takes `κ`'s β-step, its `case` and its `;`, each keeping the store and its
configuration's only step, then releases `ℓ`, and goes on.  `[spec §25]` -/
theorem use_frees_cell {μ μ' : Heap} {K₀ : Kont} {hasCancel : Bool} {ℓ : Loc} {H : Val} {K : Kont}
    {w v : Val}
    (hs : Steps (ℍ := ℍ) μ (K₀.plug (.app (kappaC hasCancel ℓ H K) (.val w))) μ' (.val v)) :
    (w = Val.inj₁ Val.unit ∨ (hasCancel = true ∧ w = Val.inj₂ Val.unit)) ∧ μ ℓ = some Val.unit ∧
    ∃ e₁ e₂ e₃ e₄, Step1Only (ℍ := ℍ) μ (K₀.plug (.app (kappaC hasCancel ℓ H K) (.val w))) μ e₁ ∧
      Step1Only (ℍ := ℍ) μ e₁ μ e₂ ∧ Step1Only (ℍ := ℍ) μ e₂ μ e₃ ∧
      Step1Only (ℍ := ℍ) μ e₃ (μ.del ℓ) e₄ ∧ Steps (ℍ := ℍ) (μ.del ℓ) e₄ μ' (.val v) := by
  have hb := kappaC_beta (ℍ := ℍ) μ hasCancel ℓ H K w K₀
  have hs₁ := hb.steps_val (fun h => by
    have := K₀.isVal_of_plug h
    simp [kappaC] at this) hs
  have hnc : ∀ (x y z : Expr), ¬ IsVal (K₀.plug (.case x y z)) := fun x y z h =>
    not_isVal_case (K₀.isVal_of_plug h)
  by_cases h₁ : ∃ a, w = Val.inj₁ a
  · obtain ⟨a, rfl⟩ := h₁
    have hc := kappaC_case₁ (ℍ := ℍ) μ hasCancel ℓ H K ((Val.inj₁ a).shift 1 0) a K₀
    obtain ⟨rfl, hℓ, h₃, h₄, h₅⟩ := steps_seq_free (hc.steps_val (hnc _ _ _) hs₁)
    exact ⟨.inl rfl, hℓ, _, _, _, _, hb, hc, h₃, h₄, h₅⟩
  by_cases h₂ : ∃ a, w = Val.inj₂ a
  · obtain ⟨a, rfl⟩ := h₂
    have hc := kappaC_case₂ (ℍ := ℍ) μ hasCancel ℓ H K ((Val.inj₂ a).shift 1 0) a K₀
    have hs₂ := hc.steps_val (hnc _ _ _) hs₁
    cases hasCancel with
    | false => exact absurd hs₂ (stuck_not_steps_val (stuckAt_unit_app Val.unit) K₀)
    | true =>
        rw [subst_kCanBr_cancel] at hc hs₂
        obtain ⟨rfl, hℓ, h₃, h₄, h₅⟩ := steps_seq_free hs₂
        exact ⟨.inr ⟨rfl, rfl⟩, hℓ, _, _, _, _, hb, hc, h₃, h₄, h₅⟩
  exfalso
  refine stuck_not_steps_val (stuckAt_case (v := w) (fun a => ⟨fun h => ?_, fun h => ?_⟩) _ _)
    K₀ hs₁
  · exact h₁ ⟨⟨a, (h ▸ w.2).inj₁_inv⟩, Subtype.ext h⟩
  · exact h₂ ⟨⟨a, (h ▸ w.2).inj₂_inv⟩, Subtype.ext h⟩

/-! ### `[unwind]`, `[then]`, `[finalise]` -/

/-- **An abortive operation caught** (`[unwind]`): `hnd (n, (qs, H)) K[raise (n, (i, v))]`, `K`
catching nothing of `n` and `c` the clause at `i`, steps only to `c v`, keeping the store; its
continuation is never reified.  `[spec §19]` -/
theorem catch_abort (μ : Heap) {n i : UInt32} {qs hr hs c : Val} (v : Val) {K : Kont}
    (hc : clauseAt hs.1 i.toNat = some c) (hK : K.Catches n = false) (K₀ : Kont) :
    Step1Only (ℍ := ℍ) μ
      (K₀.plug (hndE (hndVal n qs hr hs) (K.plug (raiseE (.val (opPayload n i v)))))) μ
      (K₀.plug (.app (.val c) (.val v))) :=
  step1Only_plug (Head.hunwind μ n i qs hr hs c v K hc hK) rfl K₀

/-- **A finaliser frame whose body returned** (`[then]`): `ubind (N, D) w` steps only to `N w`,
keeping the store.  `[spec §19]` -/
theorem then_ret (μ : Heap) (N D w : Val) (K₀ : Kont) :
    Step1Only (ℍ := ℍ) μ (K₀.plug (ubindE (.pair N D) (.val w))) μ
      (K₀.plug (.app (.val N) (.val w))) :=
  step1Only_plug (Head.uthen μ N D w) rfl K₀

/-- **An unwind that reaches a finaliser frame** (`[finalise]`): `ubind (N, D) K[raise p]`, `p` of a
name `n ≠ 0` that `K` does not catch, steps only to `D (); raise p`, keeping the store.  The
finaliser runs where the frame was, under `[·]; raise p`, which catches nothing; once it answers
`()`, the raise goes on.  `[spec §19]` -/
theorem then_fin (μ : Heap) (N D : Val) {n i : UInt32} (v : Val) {K : Kont} (hn : n ≠ 0)
    (hK : K.Catches n = false) (K₀ : Kont) :
    Step1Only (ℍ := ℍ) μ (K₀.plug (ubindE (.pair N D) (K.plug (raiseE (.val (opPayload n i v)))))) μ
      (K₀.plug ((Kont.seq .hole (raiseE (.val (opPayload n i v)))).plug
        (.app (.val D) (.val Val.unit)))) ∧
    (∀ m, (Kont.seq .hole (raiseE (.val (opPayload n i v)))).Catches m = false) ∧
    Step1Only (ℍ := ℍ) μ (K₀.plug ((Kont.seq .hole (raiseE (.val (opPayload n i v)))).plug
        (.val Val.unit))) μ (K₀.plug (raiseE (.val (opPayload n i v)))) :=
  ⟨step1Only_plug (Head.ufin μ N D n i v K hn hK) rfl K₀, fun _ => rfl,
    step1Only_plug (Head.seq μ _) rfl K₀⟩

/-! ### Forwarding -/

/-- **An operation whose context catches nothing of it takes no step**: `K[perform (n, …)]` with `K`
free of `n`, and `K[raise (n, …)]` with `K` catching nothing of `n`, are final.  `[spec §19]` -/
theorem opPlug_no_step {μ μ' : Heap} {K : Kont} {r : Bool} {p : Val} {n : UInt32} {t' : Expr}
    (hn : payloadName p = some n) (hK : OpFree r n K) :
    ¬ Step1 (ℍ := ℍ) μ (K.plug (opE r p)) μ' t' := by
  rintro ⟨K', a, a', he, -, hh⟩
  rcases plug_cmp K K' (opE_not_isVal r p) hh.not_isVal he with ⟨K'', h₁, h₂⟩ | ⟨K'', h₁, h₂⟩
  · have hK'' := plug_primApp (h₁.symm.trans (opE_eq_app r p)) hh.not_isVal
    subst hK''
    have h₀ : OpFree r n Kont.hole := by cases r <;> simp [OpFree, Kont.HasHnd, Kont.Catches]
    have ha : a = opE r p := by simpa [Kont.plug] using h₁.symm
    subst ha
    exact head_not_opPlug hn h₀ hh
  · subst h₂
    exact head_not_opPlug hn (opFree_right hK) (h₁ ▸ hh)

/-- The context a handler `hnd (n, H)` forms with the contexts around and inside it. -/
theorem plug_hndK (K₁ : Kont) (H : Val) (K : Kont) (e : Expr) :
    (K₁.comp ((hndK H).comp K)).plug e = K₁.plug (hndE H (K.plug e)) := by
  rw [Kont.plug_comp, Kont.plug_comp]; rfl

/-- **H-fwd: an operation passes a handler of another name** (`catch_fwd`).  `hnd (n, H) K[perform
(m, (i, v))]`, `n ≠ m`, takes no step in any context free of `m`: the handler of `n` does not
handle it.  Under `hnd (m, (qs', H')) K₁[·]`, `K₁` free of `m`, the handler of `m` catches it, and
the continuation it hands the clause holds `hnd (n, H)` inside: resuming it runs
`hnd (m, H') K₁[hnd (n, H) K[w]]` (`kappa_resume_steps`, `kappaC_resume`, at `plug_hndK`), so the
handler of `n` stays installed around `K`.  `[spec §19]` -/
theorem catch_fwd (μ : Heap) {m n i : UInt32} {qs hr hs qs' hr' hs' c : Val} (v : Val)
    {K₁ K : Kont} (hnm : n ≠ m) (hK₁ : K₁.HasHnd m = false) (hK : K.HasHnd m = false) :
    (∀ μ' E, ¬ Step1 (ℍ := ℍ) μ
      (K₁.plug (hndE (hndVal n qs hr hs) (K.plug (performE (.val (opPayload m i v)))))) μ' E) ∧
    (clauseAt hs'.1 i.toNat = some c → ∀ K₀ : Kont,
      Step1Only (ℍ := ℍ) μ (K₀.plug (hndE (hndVal m qs' hr' hs')
        (K₁.plug (hndE (hndVal n qs hr hs) (K.plug (performE (.val (opPayload m i v)))))))) μ
        (K₀.plug (.app (.val c) (.pair (.val v) (kappaAt (capTag qs'.1 i.toNat)
          (hndVal m qs' hr' hs') (K₁.comp ((hndK (hndVal n qs hr hs)).comp K))))))) := by
  have hfree : (K₁.comp ((hndK (hndVal n qs hr hs)).comp K)).HasHnd m = false := by
    rw [hasHnd_comp, hasHnd_comp, hndK_hasHnd, hK₁, hK]
    simpa using hnm
  refine ⟨fun μ' E h => ?_, fun hc K₀ => ?_⟩
  · rw [← plug_hndK] at h
    exact opPlug_no_step (r := false) (payloadName_opPayload m i v) hfree h
  · have h := catch_step (ℍ := ℍ) (qs := qs') (hr := hr') μ v hc hfree K₀
    rwa [plug_hndK] at h

/-- **Deep forwarding** (`fwd_resume`): resuming the continuation the catch of a forwarded
operation hands its clause runs `hnd (m, H') K₁[hnd (n, H) K[w]]`, the handler of `m` and the
passed handler of `n` both reinstalled; at a cell, across its release.  `[spec §19]` -/
theorem fwd_resume {μ : Heap} (H' H : Val) (K₁ K : Kont) (w : Val) (K₀ : Kont) :
    Steps (ℍ := ℍ) μ (K₀.plug (.app (.app (kappa H' (K₁.comp ((hndK H).comp K)))
        (.val (Val.inj₁ .unit))) (.val w))) μ
      (K₀.plug (hndE H' (K₁.plug (hndE H (K.plug (.val w)))))) ∧
    ∀ {ℓ : Loc}, μ ℓ = some Val.unit → ∀ hasCancel : Bool,
      Steps (ℍ := ℍ) μ (K₀.plug (.app (.app (kappaC hasCancel ℓ H' (K₁.comp ((hndK H).comp K)))
          (.val (Val.inj₁ .unit))) (.val w))) (μ.del ℓ)
        (K₀.plug (hndE H' (K₁.plug (hndE H (K.plug (.val w)))))) := by
  refine ⟨?_, fun hℓ hasCancel => ?_⟩
  · have h := (CancelIntercept.kappa_resume_steps (ℍ := ℍ) μ H' (K₁.comp ((hndK H).comp K))
      w).plug K₀
    rwa [plug_hndK] at h
  · have h := kappaC_resume (ℍ := ℍ) hℓ hasCancel H' (K₁.comp ((hndK H).comp K)) w K₀
    rwa [plug_hndK] at h

/-! ### A2: an abort absorbs the frames it passes -/

/-- **The redex of a raise**: a head step at `K'[raise p]` is a frame `f [·]` that catches `p`'s
name `n`, around a context catching nothing of `n`; and `f`, around any context that catches
nothing of `n`, takes the same step. -/
theorem head_raise_ctx {μ μ' : Heap} {K' : Kont} {p : Val} {n : UInt32} {a' : Expr}
    (hn : payloadName p = some n) (h : Head (ℍ := ℍ) μ (K'.plug (raiseE (.val p))) μ' a') :
    ∃ f K₁, K' = .appR f K₁ ∧ (Kont.appR f .hole).Catches n = true ∧ K₁.Catches n = false ∧
      ∀ K₂ : Kont, K₂.Catches n = false →
        Head (ℍ := ℍ) μ ((Kont.appR f K₂).plug (raiseE (.val p))) μ' a' := by
  by_cases h0 : K' = .hole
  · subst h0
    exact (head_not_inertApp (p := .raise) trivial (by simpa [raiseE] using h)).elim
  rcases head_plug h K' (opE_not_isVal true p) rfl h0 with
    ⟨m, qs, hr, hs, K₁, rfl⟩ | ⟨N, D, K₁, rfl⟩ | ⟨K₁, rfl⟩ | ⟨w, H, q, hq, rfl, he⟩ |
      ⟨err, K₁, rfl⟩
  · generalize hX : (Kont.appR (.app (.val (.prim .hnd)) (.val (hndVal m qs hr hs))) K₁).plug
      (raiseE (.val p)) = X at h
    cases h with
    | hunwind m' i qs' hr' hs' c v K₄ hc hK₄ =>
        simp only [hndE, Kont.plug, Expr.app.injEq, true_and] at hX
        obtain ⟨hH, hX⟩ := hX
        obtain ⟨rfl, rfl⟩ := plug_raise_inj hX
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hndVal_inj hH
        simp only [payloadName_opPayload, Option.some.injEq] at hn
        subst hn
        refine ⟨_, K₁, rfl, by simp [Kont.Catches, hndVal, Val.pair, Val.i32, Expr.val], hK₄,
          fun K₂ hK₂ => ?_⟩
        exact Head.hunwind μ _ i _ _ _ c v K₂ hc hK₂
    | hop m' i _ _ _ _ v K₄ =>
        simp only [hndE, Kont.plug, Expr.app.injEq] at hX
        exact (plug_perform_ne_raise _ _ _ _ hX.2.symm).elim
    | hret _ _ _ _ w =>
        simp only [hndE, Kont.plug, Expr.app.injEq] at hX
        exact (plug_raise_ne_val _ _ _ hX.2).elim
    | _ => simp_all [Kont.plug, ubindE, ccatchE, cfinE]
  · generalize hX : (Kont.appR (.app (.val (.prim .ubind)) (.val (Val.pair N D))) K₁).plug
      (raiseE (.val p)) = X at h
    cases h with
    | ufin N' D' m i v K₄ hm hK₄ =>
        simp only [ubindE, Kont.plug, Expr.app.injEq, true_and] at hX
        obtain ⟨hND, hX⟩ := hX
        obtain ⟨rfl, rfl⟩ := plug_raise_inj hX
        obtain ⟨rfl, rfl⟩ := valPair_inj hND
        simp only [payloadName_opPayload, Option.some.injEq] at hn
        subst hn
        exact ⟨_, K₁, rfl, by simp [Kont.Catches, Val.pair, Expr.val], hK₄,
          fun K₂ hK₂ => Head.ufin μ _ _ m i v K₂ hm hK₂⟩
    | ufinC N' D' err K₄ hK₄ =>
        simp only [ubindE, Kont.plug, Expr.app.injEq, true_and] at hX
        obtain ⟨hND, hX⟩ := hX
        obtain ⟨rfl, rfl⟩ := plug_raise_inj hX
        obtain ⟨rfl, rfl⟩ := valPair_inj hND
        simp only [payloadName_cancelVal, Option.some.injEq] at hn
        subst hn
        exact ⟨_, K₁, rfl, by simp [Kont.Catches, Val.pair, Expr.val], hK₄,
          fun K₂ hK₂ => Head.ufinC μ _ _ err K₂ hK₂⟩
    | uthen _ _ w =>
        simp only [ubindE, Kont.plug, Expr.app.injEq] at hX
        exact (plug_raise_ne_val _ _ _ hX.2).elim
    | _ => simp_all [Kont.plug, hndE, ccatchE, cfinE]
  · generalize hX : (Kont.appR (.val (.prim .ccatch)) K₁).plug (raiseE (.val p)) = X at h
    cases h with
    | cancel K₄ hK₄ =>
        simp only [ccatchE, Kont.plug, Expr.app.injEq, true_and] at hX
        obtain ⟨rfl, rfl⟩ := plug_raise_inj hX
        simp only [payloadName_cancelVal, Option.some.injEq] at hn
        subst hn
        exact ⟨_, K₁, rfl, by simp [Kont.Catches, Expr.val], hK₄,
          fun K₂ hK₂ => Head.cancel μ K₂ hK₂⟩
    | creraise E K₄ hK₄ =>
        simp only [ccatchE, Kont.plug, Expr.app.injEq, true_and] at hX
        obtain ⟨rfl, rfl⟩ := plug_raise_inj hX
        simp only [payloadName_cancelVal, Option.some.injEq] at hn
        subst hn
        exact ⟨_, K₁, rfl, by simp [Kont.Catches, Expr.val], hK₄,
          fun K₂ hK₂ => Head.creraise μ E K₂ hK₂⟩
    | _ => simp_all [Kont.plug, hndE, ubindE, cfinE]
  · generalize hX : (Kont.appL .hole w).plug (raiseE (.val p)) = X at h
    cases h <;> simp_all [Kont.plug, raiseE, hndE, ubindE, ccatchE, cfinE]
  · generalize hX : (Kont.appR (.app (.val (.prim .cfin)) (.val (cancelVal err))) K₁).plug
      (raiseE (.val p)) = X at h
    cases h with
    | cferr err' m j w K₄ hm hK₄ =>
        simp only [cfinE, Kont.plug, Expr.app.injEq, true_and] at hX
        obtain ⟨hst, hX⟩ := hX
        obtain ⟨rfl, rfl⟩ := plug_raise_inj hX
        obtain rfl := cancelVal_inj (Subtype.ext hst)
        simp only [payloadName_opPayload, Option.some.injEq] at hn
        subst hn
        exact ⟨_, K₁, rfl, by simp [Kont.Catches, Expr.val], hK₄,
          fun K₂ hK₂ => Head.cferr μ err m j w K₂ hm hK₂⟩
    | cfcancel err' err'' K₄ hK₄ =>
        simp only [cfinE, Kont.plug, Expr.app.injEq, true_and] at hX
        obtain ⟨hst, hX⟩ := hX
        obtain ⟨rfl, rfl⟩ := plug_raise_inj hX
        obtain rfl := cancelVal_inj (Subtype.ext hst)
        simp only [payloadName_cancelVal, Option.some.injEq] at hn
        subst hn
        exact ⟨_, K₁, rfl, by simp [Kont.Catches, Expr.val], hK₄,
          fun K₂ hK₂ => Head.cfcancel μ err err'' K₂ hK₂⟩
    | cfret _ w =>
        simp only [cfinE, Kont.plug, Expr.app.injEq] at hX
        exact (plug_raise_ne_val _ _ _ hX.2).elim
    | _ => simp_all [Kont.plug, hndE, ubindE, ccatchE]

/-- **A2: an abort absorbs the frames it passes** (`abort_absorbs`).  `raise p` under frames that
catch nothing of `p`'s name steps, in every context, exactly as `raise p` steps there: the frame
that catches it drops them, by `[unwind]`, `[finalise]`, `[finalise-cancel]`, `[cfin-raise]`,
`[cfin-cancel]`, `[cancel]` or `[cancel-raise]`.  `[spec §19]` -/
theorem abort_absorbs {p : Val} {n : UInt32} (hn : payloadName p = some n) {K : Kont}
    (hK : K.Catches n = false) (K₁ : Kont) {μ μ' : Heap} {E : Expr} :
    Step1 (ℍ := ℍ) μ (K₁.plug (K.plug (raiseE (.val p)))) μ' E ↔
      Step1 (ℍ := ℍ) μ (K₁.plug (raiseE (.val p))) μ' E := by
  have hr : ¬ IsVal (raiseE (.val p)) := opE_not_isVal true p
  -- a redex holding the raise holds it at a catcher frame
  have inner : ∀ {K' K'' : Kont} {a a' : Expr} {μ₁ : Heap}, Head (ℍ := ℍ) μ a μ₁ a' →
      ∀ (X : Expr), K'.plug a = X → X = K''.plug (raiseE (.val p)) →
        ∃ K₃, a = K₃.plug (raiseE (.val p)) ∧ K'' = K'.comp K₃ := by
    intro K' K'' a a' μ₁ hh X hX hX'
    subst hX
    rcases plug_cmp K' K'' hh.not_isVal hr hX' with ⟨K₃, h₁, h₂⟩ | ⟨K₃, h₁, -⟩
    · exact ⟨K₃, h₁, h₂⟩
    · have h0 := plug_primApp (h₁.symm.trans (opE_eq_app true p)) hh.not_isVal
      subst h0
      simp only [Kont.plug] at h₁
      subst h₁
      exact (head_not_inertApp (p := .raise) trivial (by simpa [raiseE] using hh)).elim
  constructor
  · rintro ⟨K', a, a', he, rfl, hh⟩
    obtain ⟨K₃, rfl, hK'⟩ := inner hh _ he.symm (Kont.plug_comp K₁ K _).symm
    obtain ⟨f, K₇, rfl, hf, hK₇, hall⟩ := head_raise_ctx hn hh
    -- the catching frame is outside `K`
    have he' : K₁.plug (K.plug (raiseE (.val p))) =
        K'.plug ((Kont.appR f K₇).plug (raiseE (.val p))) := by
      rw [← Kont.plug_comp, hK', Kont.plug_comp]
    rcases plug_cmp K₁ K' (fun h => hr (K.isVal_of_plug h))
        (fun h => hr ((Kont.appR f K₇).isVal_of_plug h)) he' with ⟨K₆, h₁, h₂⟩ | ⟨K₆, h₁, h₂⟩
    · rw [← Kont.plug_comp] at h₁
      have hKe := plug_inj_ctx hr h₁
      rw [hKe, catches_comp] at hK
      have : (Kont.appR f K₇).Catches n = true := by
        simp only [Kont.Catches] at hf ⊢
        simp only [Bool.or_false] at hf
        rw [hf]; rfl
      rw [this, Bool.or_true] at hK
      cases hK
    · rw [← Kont.plug_comp] at h₁
      have hKe := plug_inj_ctx hr h₁
      cases K₆ with
      | hole =>
          simp only [Kont.comp] at hKe
          subst hKe
          simp only [Kont.Catches] at hf hK
          simp only [Bool.or_false] at hf
          rw [hf] at hK
          cases hK
      | appR f' K₆' =>
          simp only [Kont.comp, Kont.appR.injEq] at hKe
          obtain ⟨rfl, rfl⟩ := hKe
          rw [catches_comp, Bool.or_eq_false_iff] at hK₇
          refine ⟨K', (Kont.appR f K₆').plug (raiseE (.val p)), a', ?_, rfl, hall K₆' hK₇.1⟩
          rw [h₂, Kont.plug_comp]
      | _ => simp [Kont.comp] at hKe
  · rintro ⟨K', a, a', he, rfl, hh⟩
    obtain ⟨K₃, rfl, rfl⟩ := inner hh _ he.symm rfl
    obtain ⟨f, K₇, rfl, -, hK₇, hall⟩ := head_raise_ctx hn hh
    have h := hall (K₇.comp K) (by rw [catches_comp, hK₇, hK]; rfl)
    refine ⟨K', _, a', ?_, rfl, h⟩
    simp only [Kont.plug_comp, Kont.plug]

/-- **A2 at `to`**: `raise p to x. N` steps, in every context, as `raise p` does:
`raise e to x. N = raise e`.  `[spec §19]` -/
theorem abort_to {p : Val} {n : UInt32} (hn : payloadName p = some n) (N : Expr) (K₁ : Kont)
    {μ μ' : Heap} {E : Expr} :
    Step1 (ℍ := ℍ) μ (K₁.plug (bindE (raiseE (.val p)) N)) μ' E ↔
      Step1 (ℍ := ℍ) μ (K₁.plug (raiseE (.val p))) μ' E :=
  abort_absorbs hn (K := .appR (.val (Val.lam N)) .hole) rfl K₁

/-- **A2 at application**: `(raise p) w` steps, in every context, as `raise p` does: `(raise e) w
= raise e`, the projections of `&` (`w = inj₁ ()`, `inj₂ ()`) among them.  `[spec §19]` -/
theorem abort_app {p : Val} {n : UInt32} (hn : payloadName p = some n) (w : Val) (K₁ : Kont)
    {μ μ' : Heap} {E : Expr} :
    Step1 (ℍ := ℍ) μ (K₁.plug (.app (raiseE (.val p)) (.val w))) μ' E ↔
      Step1 (ℍ := ℍ) μ (K₁.plug (raiseE (.val p))) μ' E :=
  abort_absorbs hn (K := .appL .hole w) rfl K₁

/-- **H-fwd at an abortive operation** (`fwd_abort`): `hnd (m, H) K[raise p]`, `m` not `p`'s name
and `K` catching nothing of it, steps, in every context, as `raise p` does: `handle_m (raise_n v)
= raise_n v`.  `[spec §19]` -/
theorem fwd_abort {p : Val} {n m : UInt32} (hn : payloadName p = some n) (hmn : m ≠ n)
    (qs hr hs : Val) {K : Kont} (hK : K.Catches n = false) (K₁ : Kont) {μ μ' : Heap} {E : Expr} :
    Step1 (ℍ := ℍ) μ (K₁.plug (hndE (hndVal m qs hr hs) (K.plug (raiseE (.val p))))) μ' E ↔
      Step1 (ℍ := ℍ) μ (K₁.plug (raiseE (.val p))) μ' E := by
  have h := abort_absorbs (ℍ := ℍ) hn (K := (hndK (hndVal m qs hr hs)).comp K)
    (by rw [catches_comp, hndK_catches, hK]; simpa using hmn) K₁ (μ := μ) (μ' := μ') (E := E)
  rwa [Kont.plug_comp] at h

end BoCa.Fig16.LogRel.Core

end
