import Core.Chain.SI.Capture
import Core.Chain.SI.HandleN
import Core.Chain.SI.BindN

/-!
# The effectful relation over `crwpG`: `cerwp`

`erwp` (`SI/ErwpN.lean`) is `rwpG` at "a value in `Q`, or a stop the table allows, owing its
continuation at every lower index". `cerwp` is the same over `crwpG`, with two changes the owned
records and the qualified frames force at a stop:

* the continuation's share owns the records the run owns at the stop, and is resumed owning
  them (`contShareC`'s `O`): a record left open at a stop is held by the stopped branch;
* the continuation is owed at the frame condition the run had, strengthened by the entry's
  `fd` at the payload: what the resumer guarantees of the rest of the world when it resumes. An
  entry lifted from `erwp` asks nothing (`liftEnt`); the join of a lend scope asks that no other
  computation hold a cell at the location it names (`SI/CaptureScope.lean`).

`cerwp_of_erwp`: every `erwp` derivation at a table with no unrestricted and no abortive entry is a
`cerwp` derivation at the lifted table, at every frame condition and every owned list, the garbage
kept in the resource (in the postcondition at a return, in the continuation's share at a stop).
So every frame rule across stops proved at `erwp` holds at `cerwp`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload)

/-! ### Tables -/

/-- `OpEntN` with a frame condition the resumer meets and an answer predicate, both read at the
payload: a join names the location whose borrows it waits for, and gets back the borrows of
that location the joined tasks held. -/
structure OpEntC extends OpEntN where
  fd : Val → WRes → Prop
  PBv : Val → Nat → List SRec → Val → WProp
  /-- What the stopped branch may own at the stop: the resumer reads it to keep the records of
  the branches it holds apart. -/
  oc : List FrameRec → Prop

abbrev OpTabC := UInt32 → UInt32 → Option OpEntC

/-- What a stop owes: a continuation at a frame condition, owning records, at an index and a
list. -/
abbrev ContC := (WRes → Prop) → List FrameRec → Nat → List SRec → Expr → WProp

/-- A table: the stop at `t`, under the frame condition `F`, at the index `k`, the list and the
records owned, owing `Ψ`. -/
abbrev TableC := (WRes → Prop) → Nat → List SRec → List FrameRec → Expr → ContC → WProp

/-- A postcondition over values. -/
abbrev PostCV : Type := Nat → List SRec → List FrameRec → Val → WProp

/-- The continuation's share: resumed at every answer in `PBv` at the payload, at every `k′ < k`,
at every list `wc` allows, owning `O`, under a frame meeting `F` and the entry's `fd` at the
payload. -/
def contShareC (en : OpEntC) (F : WRes → Prop) (k : Nat) (ls : List SRec) (O : List FrameRec)
    (K : Kont) (v : Val) (Ψ : ContC) : WProp := fun ρ =>
  (en.q = .unr → ρ = PMap.empty) ∧
  ∀ ls', en.wc ls ls' ρ →
    (∀ k', k' < k → ∀ w : Val, (en.PBv v k' ls' w ─⋆
      Ψ (fun ρf => F ρf ∧ en.fd v ρf) O k' ls' (K.plug (.val w))) ρ) ∧
    (en.q ≠ .lin → cancelOKN en.toOpEntN k ls' K ρ)

/-- A stop at a non-abortive operation the table allows. -/
def opTableC (T : OpTabC) : TableC := fun F k ls O t Ψ =>
  ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
    ex fun (en : OpEntC) =>
      ⌜t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧
        T n i = some en ∧ en.abort = false ∧ en.oc O⌝ ⋆
        (en.PA k ls v ⋆ contShareC en F k ls O K v Ψ)

/-- A table reads what is owed only below the index it stops at. -/
def TableC.Local (Tb : TableC) : Prop :=
  ∀ F k ls O t (Ψ Ψ' : ContC) ρ,
    (∀ F' O' k', k' < k → ∀ ls e ρ, Ψ F' O' k' ls e ρ → Ψ' F' O' k' ls e ρ) →
    Tb F k ls O t Ψ ρ → Tb F k ls O t Ψ' ρ

/-- A table is downward closed in its index. -/
def TableC.Down (Tb : TableC) : Prop :=
  ∀ F k ls O t Ψ ρ, Tb F (k + 1) ls O t Ψ ρ → Tb F k ls O t Ψ ρ

theorem opTableC_local (T : OpTabC) : (opTableC T).Local := by
  intro F k ls O t Ψ Ψ' ρ hΨ h
  obtain ⟨K, n, i, v, en, h⟩ := h
  obtain ⟨hp, ρa, ρk, hc, hA, hu, hcont⟩ := pure_sep_iff.mp h
  exact ⟨K, n, i, v, en, pure_sep_mk hp ⟨ρa, ρk, hc, hA, hu, fun ls' he =>
    ⟨fun k' hk w σ₁ σ₂ hB hcσ => hΨ _ _ k' hk _ _ _ ((hcont ls' he).1 k' hk w σ₁ σ₂ hB hcσ),
      (hcont ls' he).2⟩⟩⟩

/-- The entries of a table, their payload predicates and cancel obligations downward closed. -/
structure OpTabC.Down (T : OpTabC) : Prop where
  pa : ∀ n i en, T n i = some en → ∀ k ls v ρ, en.PA (k + 1) ls v ρ → en.PA k ls v ρ
  fin : ∀ n i en P, T n i = some en → en.fin = some P → ∀ k ls e ρ, P (k + 1) ls e ρ → P k ls e ρ

theorem opTableC_down {T : OpTabC} (hT : T.Down) : (opTableC T).Down := by
  intro F k ls O t Ψ ρ h
  obtain ⟨K, n, i, v, en, h⟩ := h
  obtain ⟨⟨h₁, h₂, h₃, h₄, h₅⟩, ρa, ρk, hc, hA, hu, hcont⟩ := pure_sep_iff.mp h
  exact ⟨K, n, i, v, en, pure_sep_mk ⟨h₁, h₂, h₃, h₄, h₅⟩ ⟨ρa, ρk, hc,
    hT.pa _ _ _ h₃ _ _ _ _ hA, hu, fun ls' he =>
    ⟨fun k' hk => (hcont ls' he).1 k' (by omega), fun hq P hP =>
      hT.fin _ _ _ _ h₃ hP _ _ _ _ ((hcont ls' he).2 hq P hP)⟩⟩⟩

/-! ### The relation -/

/-- A value in `Q`, or a stop the table allows. -/
def cerwpPost (Tb : TableC) (Q : PostCV) (Ψ : ContC) (F : WRes → Prop) : PostC :=
  fun k ls O t => BoLo.or (fun ρ => ∃ v : Val, t = v.1 ∧ Q k ls O v ρ) (Tb F k ls O t Ψ)

/-- **The effectful relation over `crwpG`.** -/
def cerwp (Tb : TableC) (Q : PostCV) :
    (WRes → Prop) → Nat → List SRec → List FrameRec → Expr → WProp
  | F, n, ls, O, e => crwpG (ℍ := ℍ) F (cerwpPost Tb Q (fun F' O' k' ls' e' =>
      if _h : k' < n then cerwp Tb Q F' k' ls' O' e' else fun _ => False) F) n ls O e
termination_by _ n => n

/-- What `cerwp` at `N` owes below it. -/
def cerwpC (Tb : TableC) (Q : PostCV) (N : Nat) : ContC := fun F' O' k' ls' e' =>
  if k' < N then cerwp (ℍ := ℍ) Tb Q F' k' ls' O' e' else fun _ => False

theorem cerwp_eq (Tb : TableC) (Q : PostCV) (F : WRes → Prop) (n : Nat) (ls : List SRec)
    (O : List FrameRec) (e : Expr) :
    cerwp (ℍ := ℍ) Tb Q F n ls O e =
      crwpG (ℍ := ℍ) F (cerwpPost Tb Q (cerwpC (ℍ := ℍ) Tb Q n) F) n ls O e := by
  rw [cerwp]
  congr 1

theorem cerwp_unfold_at {Tb : TableC} (hTb : Tb.Local) {Q : PostCV} {F : WRes → Prop}
    {n N : Nat} (hnN : n ≤ N) {ls : List SRec} {O : List FrameRec} {e : Expr} {ρ : WRes}
    (h : cerwp (ℍ := ℍ) Tb Q F n ls O e ρ) :
    crwpG (ℍ := ℍ) F (cerwpPost Tb Q (cerwpC (ℍ := ℍ) Tb Q N) F) n ls O e ρ := by
  rw [cerwp_eq] at h
  refine crwpG_mono_le (fun k hk ls' O' t ρ' ht => ?_) h
  rcases ht with ht | ht
  · exact Or.inl ht
  · refine Or.inr (hTb F k ls' O' t _ _ ρ' (fun F' O'' k' hk' ls'' e'' ρ'' hΨ => ?_) ht)
    simp only [cerwpC, show k' < n by omega, show k' < N by omega, if_true] at hΨ ⊢
    exact hΨ

theorem cerwp_fold_at {Tb : TableC} (hTb : Tb.Local) {Q : PostCV} {F : WRes → Prop}
    {n N : Nat} (hnN : n ≤ N) {ls : List SRec} {O : List FrameRec} {e : Expr} {ρ : WRes}
    (h : crwpG (ℍ := ℍ) F (cerwpPost Tb Q (cerwpC (ℍ := ℍ) Tb Q N) F) n ls O e ρ) :
    cerwp (ℍ := ℍ) Tb Q F n ls O e ρ := by
  rw [cerwp_eq]
  refine crwpG_mono_le (fun k hk ls' O' t ρ' ht => ?_) h
  rcases ht with ht | ht
  · exact Or.inl ht
  · refine Or.inr (hTb F k ls' O' t _ _ ρ' (fun F' O'' k' hk' ls'' e'' ρ'' hΨ => ?_) ht)
    simp only [cerwpC, show k' < n by omega, show k' < N by omega, if_true] at hΨ ⊢
    exact hΨ

theorem cerwp_zero {Tb : TableC} {Q : PostCV} {F : WRes → Prop} {ls : List SRec}
    {O : List FrameRec} {e : Expr} {ρ : WRes} : cerwp (ℍ := ℍ) Tb Q F 0 ls O e ρ := by
  rw [cerwp_eq]; exact crwpG_zero

/-- A postcondition over values is downward closed. -/
def PostCV.Down (Q : PostCV) : Prop := ∀ n ls O v ρ, Q (n + 1) ls O v ρ → Q n ls O v ρ

theorem cerwpPost_down {Tb : TableC} (hTb : Tb.Down) {Q : PostCV} (hQ : Q.Down) (Ψ : ContC)
    (F : WRes → Prop) : (cerwpPost Tb Q Ψ F).Down := by
  intro k ls O t ρ h
  rcases h with ⟨v, hv, hq⟩ | h
  · exact Or.inl ⟨v, hv, hQ _ _ _ _ _ hq⟩
  · exact Or.inr (hTb _ _ _ _ _ _ _ h)

/-- **`cerwp` is downward closed.** -/
theorem cerwp_le {Tb : TableC} (hTb : Tb.Local) (hTd : Tb.Down) {Q : PostCV} (hQ : Q.Down)
    {F : WRes → Prop} {m n : Nat} (hmn : m ≤ n) {ls : List SRec} {O : List FrameRec} {e : Expr}
    {ρ : WRes} (h : cerwp (ℍ := ℍ) Tb Q F n ls O e ρ) : cerwp (ℍ := ℍ) Tb Q F m ls O e ρ :=
  cerwp_fold_at hTb hmn (crwpG_le (cerwpPost_down hTd hQ _ F) hmn (cerwp_unfold_at hTb le_rfl h))

/-- A stronger frame condition. -/
theorem cerwp_frameCond {Tb : TableC} {Q : PostCV} {F F' : WRes → Prop}
    (hTF : ∀ k ls O t Ψ ρ, Tb F k ls O t Ψ ρ → Tb F' k ls O t Ψ ρ) (hF : ∀ ρf, F' ρf → F ρf)
    {n : Nat} {ls : List SRec} {O : List FrameRec} {e : Expr} {ρ : WRes}
    (h : cerwp (ℍ := ℍ) Tb Q F n ls O e ρ) : cerwp (ℍ := ℍ) Tb Q F' n ls O e ρ := by
  rw [cerwp_eq] at h ⊢
  refine crwpG_frameCond hF (crwpG_mono (fun k ls' O' t ρ' ht => ?_) h)
  rcases ht with ht | ht
  · exact Or.inl ht
  · exact Or.inr (hTF _ _ _ _ _ _ ht)

/-- A deterministic step in front of a `cerwp`, for free. -/
theorem cerwp_det {Tb : TableC} (hTd : Tb.Down) {Q : PostCV} (hQ : Q.Down) {F : WRes → Prop}
    {n : Nat} {ls : List SRec} {O : List FrameRec} {e e' : Expr} {ρ : WRes}
    (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e') (h : cerwp (ℍ := ℍ) Tb Q F n ls O e' ρ) :
    cerwp (ℍ := ℍ) Tb Q F n ls O e ρ := by
  rw [cerwp_eq] at h ⊢
  exact crwpG_det (cerwpPost_down hTd hQ _ F) hdet h

/-- A deterministic step in front of a `cerwp`, paid. -/
theorem cerwp_step {Tb : TableC} (hL : Tb.Local) {Q : PostCV} {F : WRes → Prop} {n : Nat}
    {ls : List SRec} {O : List FrameRec} {e e' : Expr} {ρ : WRes}
    (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e') (h : cerwp (ℍ := ℍ) Tb Q F n ls O e' ρ) :
    cerwp (ℍ := ℍ) Tb Q F (n + 1) ls O e ρ :=
  cerwp_fold_at hL le_rfl (crwpG_step hdet (cerwp_unfold_at hL (Nat.le_succ n) h))

/-- A value in the postcondition. -/
theorem cerwp_val {Tb : TableC} {Q : PostCV} {F : WRes → Prop} {n : Nat} {ls : List SRec}
    {O : List FrameRec} {v : Val} {ρ : WRes} (h : Q n ls O v ρ) :
    cerwp (ℍ := ℍ) Tb Q F n ls O v.1 ρ := by
  rw [cerwp_eq]
  exact crwpG_here (fun μ => final_val μ v) (Or.inl ⟨v, rfl, h⟩)

/-- **A stop at a non-abortive operation the table allows.** -/
theorem cerwp_perform {T : OpTabC} {Q : PostCV} {F : WRes → Prop} (K : Kont) {m i : UInt32}
    {v : Val} {en : OpEntC} (hK : K.HasHnd m = false) (hT : T m i = some en)
    (ha : en.abort = false) {n : Nat} {ls : List SRec} {O : List FrameRec} {ρa ρk ρ : WRes}
    (hoc : en.oc O) (hc : ResU.CompS ρa ρk ρ) (hA : en.PA n ls v ρa)
    (hu : en.q = .unr → ρk = PMap.empty)
    (hk : ∀ ls', en.wc ls ls' ρk → ∀ k', k' < n → ∀ w : Val,
      (en.PBv v k' ls' w ─⋆ cerwp (ℍ := ℍ) (opTableC T) Q (fun ρf => F ρf ∧ en.fd v ρf) k' ls' O
        (K.plug (.val w))) ρk)
    (hcan : ∀ ls', en.wc ls ls' ρk → en.q ≠ .lin → cancelOKN en.toOpEntN n ls' K ρk) :
    cerwp (ℍ := ℍ) (opTableC T) Q F n ls O (K.plug (performE (.val (opPayload m i v)))) ρ := by
  rw [cerwp_eq]
  refine crwpG_here (final_opPlug (r := false) (payloadName_opPayload m i v) hK) (Or.inr
    ⟨K, m, i, v, en, pure_sep_mk ⟨rfl, hK, hT, ha, hoc⟩ ⟨ρa, ρk, hc, hA, hu,
      fun ls' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_, hcan ls' he⟩⟩⟩)
  simp only [cerwpC, hk', if_true]
  exact hk ls' he k' hk' w τ₁ τ₂ hB hcτ

/-! ### Bind with a computation that does not stop -/

/-- **`rwp` in front of a `cerwp`**: a run of `e` to a value at `rwp`, the garbage kept, then the
continuation. -/
theorem cerwp_bindRwp {Φ : LocFam} {Tb : TableC} (hL : Tb.Local) {Q : PostCV}
    {F : WRes → Prop} (K : Kont) {Q' : PostN} {n : Nat} {ls : List SRec} {O : List FrameRec}
    {e : Expr} {ρ : WRes} (h : rwp (ℍ := ℍ) Φ Q' n ls e ρ)
    (hK : ∀ k ls' (v : Val) ρ₁ ρ₂ ρ', k ≤ n → Q' k ls' v ρ₁ → NoOwn ρ₂ → ResU.CompS ρ₁ ρ₂ ρ' →
      cerwp (ℍ := ℍ) Tb Q F k ls' O (K.plug v.1) ρ') :
    cerwp (ℍ := ℍ) Tb Q F n ls O (K.plug e) ρ := by
  rw [cerwp_eq]
  refine crwpG_bind K (crwpG_mono_le (fun k hk ls' O' t ρ' ht => ?_)
    (crwpG_of_rwpG (O := O) (F := F) (rwp_iff_rwpG.mp h)))
  obtain ⟨rfl, ρ₁, ρ₂, hc, hno, v, rfl, hq⟩ := ht
  exact cerwp_unfold_at hL hk (hK k ls' v ρ₁ ρ₂ ρ' hk hq hno hc)

/-- An allocation at an evaluation position. -/
theorem cerwp_alloc {Φ : LocFam} {Tb : TableC} (hL : Tb.Local) {Q : PostCV}
    {F : WRes → Prop} (K : Kont) (v : Val) {n : Nat} {ls : List SRec} {O : List FrameRec}
    {ρ : WRes}
    (h : ∀ (ℓ : Loc) (σ₁ σ₂ g σ₃ : WRes), ptoOwn ℓ v σ₁ →
      ResU.CompS ρ σ₁ σ₂ → NoOwn g → ResU.CompS σ₂ g σ₃ →
      cerwp (ℍ := ℍ) Tb Q F (n - 1) ls O (K.plug (.val (Val.loc ℓ))) σ₃) :
    cerwp (ℍ := ℍ) Tb Q F n ls O (K.plug (.app (.val (.prim .alloc)) (.val v))) ρ := by
  refine cerwp_bindRwp (Φ := Φ) hL K (Q' := fun k ls' w σ => k = n - 1 ∧ ls' = ls ∧ ∃ ℓ σ₁,
      w = Val.loc ℓ ∧ ptoOwn ℓ v σ₁ ∧ ResU.CompS ρ σ₁ σ)
    (rwp_alloc (Φ := Φ) ls v _ (fun ℓ σ₁ σ₂ hp hc => ⟨rfl, rfl, ℓ, σ₁, rfl, hp, hc⟩))
    (fun k ls' w ρ₁ ρ₂ ρ' _ hq hno hc => ?_)
  obtain ⟨rfl, rfl, ℓ, σ₁, rfl, hp, hc₁⟩ := hq
  exact h ℓ σ₁ ρ₁ ρ₂ ρ' hp hc₁ hno hc

/-- A release of an owned cell at an evaluation position. -/
theorem cerwp_free {Φ : LocFam} {Tb : TableC} (hL : Tb.Local) {Q : PostCV}
    {F : WRes → Prop} (K : Kont) (ℓ : Loc) (v : Val) {n : Nat} {ls : List SRec}
    {O : List FrameRec} {ρ ρ₁ ρ₂ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) (hp : ptoOwn ℓ v ρ₁)
    (h : ∀ (g σ : WRes), NoOwn g → ResU.CompS ρ₂ g σ →
      cerwp (ℍ := ℍ) Tb Q F (n - 1) ls O (K.plug (.val v)) σ) :
    cerwp (ℍ := ℍ) Tb Q F n ls O (K.plug (BoLo.freeE (.val (Val.loc ℓ)))) ρ := by
  refine cerwp_bindRwp (Φ := Φ) hL K
    (Q' := fun k ls' w σ => k = n - 1 ∧ ls' = ls ∧ w = v ∧ σ = ρ₂)
    (rwp_free (Φ := Φ) ls ℓ v _ ⟨ρ₁, ρ₂, hc, hp, rfl, rfl, rfl, rfl⟩)
    (fun k ls' w σ₁ g σ _ hq hno hcg => ?_)
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hq
  exact h g σ hno hcg

/-! ### `erwp` lifts -/

/-- An `erwp` entry asks nothing of the resumer's frame, and its answer does not read the
payload. -/
def liftEnt (en : OpEntN) : OpEntC :=
  { en with fd := fun _ _ => True, PBv := fun _ => en.PB, oc := fun _ => True }

def liftTab (T : OpTabN) : OpTabC := fun m i => (T m i).map liftEnt

theorem liftTab_some {T : OpTabN} {m i : UInt32} {en : OpEntC} (h : liftTab T m i = some en) :
    ∃ en₀, T m i = some en₀ ∧ en = liftEnt en₀ := by
  unfold liftTab at h
  cases e : T m i with
  | none => rw [e] at h; cases h
  | some en₀ => rw [e] at h; exact ⟨en₀, rfl, (Option.some.inj h).symm⟩

/-- The postcondition an `erwp` postcondition lifts to: the garbage kept, the records
unchanged. -/
def liftQ (Q : PostN) (O : List FrameRec) : PostCV := fun k ls O' v ρ =>
  O' = O ∧ ∃ ρ₁ ρ₂, ResU.CompS ρ₁ ρ₂ ρ ∧ NoOwn ρ₂ ∧ Q k ls v ρ₁

/-- A cancel obligation keeps its garbage. -/
def FinGarbage (T : OpTabN) : Prop :=
  ∀ m i en P, T m i = some en → en.fin = some P →
    ∀ k ls e (ρ g ρg : WRes), ResU.CompS ρ g ρg → NoOwn g → P k ls e ρ → P k ls e ρg

/-- **`erwp` is `cerwp`** at the lifted table, at every frame condition and every owned list.
The garbage of a stop goes into the continuation's share, which is why unrestricted entries
(whose share is empty) are excluded. -/
theorem cerwp_of_erwp {Φ : LocFam} {T : OpTabN} (hTD : T.Down)
    (hab : ∀ m i en, T m i = some en → en.abort = false)
    (hunr : ∀ m i en, T m i = some en → en.q ≠ .unr) (hfin : FinGarbage T) {Q : PostN} :
    ∀ n (F : WRes → Prop) ls (O : List FrameRec) e ρ, erwp (ℍ := ℍ) Φ (opTableN T) Q n ls e ρ →
      cerwp (ℍ := ℍ) (opTableC (liftTab T)) (liftQ Q O) F n ls O e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro F ls O e ρ h
  rw [erwp_eq] at h
  rw [cerwp_eq]
  refine crwpG_mono_le (fun k hk ls' O' t ρ' ht => ?_) (crwpG_of_rwpG (O := O) (F := F) h)
  obtain ⟨rfl, ρ₁, ρ₂, hc, hno, ht⟩ := ht
  rcases ht with ⟨v, rfl, hv⟩ | ⟨K, m, i, v, en, hp⟩ | ⟨K, m, i, v, en, hp⟩
  · exact Or.inl ⟨v, rfl, rfl, ρ₁, ρ₂, hc, hno, hv⟩
  · obtain ⟨⟨rfl, hK, hT, ha⟩, ρa, ρk, hcak, hA, -, hcont⟩ := pure_sep_iff.mp hp
    obtain ⟨y, hy, hay⟩ := compS_reassoc hcak hc
    refine Or.inr ⟨K, m, i, v, liftEnt en, pure_sep_mk ⟨rfl, hK, by simp [liftTab, hT], ha, trivial⟩
      ⟨ρa, y, hay, hA, fun hu => absurd hu (hunr m i en hT), fun ls'' he => ⟨?_, ?_⟩⟩⟩
    · have he' : en.wc ls' ls'' ρk := hTD.wcl _ _ _ hT _ _ _ _ _ hy he
      intro k' hk' w τ₁ τ₂ hB hcτ
      obtain ⟨z, hz, hzτ⟩ := compS_exch hy hcτ
      have h₁ := (hcont ls'' he').1 k' hk' w τ₁ z hB hz
      simp only [erwpC, show k' < n by omega, if_true] at h₁
      simp only [cerwpC, show k' < n by omega, if_true]
      exact ih k' (by omega) _ ls'' _ _ τ₂ (erwp_garbage hzτ hno h₁)
    · intro hq P hP
      have he' : en.wc ls' ls'' ρk := hTD.wcl _ _ _ hT _ _ _ _ _ hy he
      exact hfin m i en P hT hP _ _ _ _ _ _ hy hno ((hcont ls'' he').2 hq P hP)
  · obtain ⟨⟨-, -, hT, ha⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd (hab m i en hT) (by rw [ha]; simp)

end BoCa.Fig16.LogRel.Core.Chain.SI

end
