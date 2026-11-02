import DtorUnwind.TreeWp.Rel
import DtorUnwind.SI.CaptureE

/-!
# `cerwp` over the tree world: `cerwpT`

`SI/CaptureE.lean`'s `cerwp`, over `twp`. A stop leaves a continuation share `ρ_k` and owes the
continuation below the index. What changes:

* **The resume world is any extension of the stop's world**, with the share re-read there
  (`contShareT`): the continuation is a Kripke wand. A table entry's `wc` (the lists the
  continuation may be resumed at, `extF` for an operation performed under a live lend) becomes
  `TWd.Ext` along `RR`: what `extF` kept (the records named by frozen locations) has no list to
  live in; the cells at frozen locations are kept by the re-reading, which changes no tag, value
  or witness domain. At `RR.refl` the resume is at the stop's own world.
* **No owned records** (`oc`, `O`): see `TreeWp/Rel.lean`.
* The resumer's guarantee `fd` and the payload-dependent answer `PBv` are `OpEntC`'s, read at the
  resume world.

Resuming a stored continuation inside a lend opened after the stop (round 7's graft) is a resume
at the grafted world: `contShareT_resume` is that step, by the definition of the share.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.DtorUnwind.SI
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload)

/-! ### Tables -/

/-- A world-indexed predicate over values at a step index. -/
abbrev TVProp : Type := Nat → (w : TWd) → Val → TRes w.K → Prop

/-- An operation's entry over the tree world. -/
structure OpEntT where
  q : Qual
  abort : Bool
  PA : TVProp
  /-- The answer, read at the payload. -/
  PBv : Val → TVProp
  /-- The cancel obligation, at a world. -/
  fin : Option (Nat → (w : TWd) → Expr → TRes w.K → Prop)
  /-- What the resumer guarantees of the frame at the resume, read at the payload. -/
  fd : Val → TFrame

abbrev OpTabT := UInt32 → UInt32 → Option OpEntT

/-- What a stop owes: a continuation at a frame condition, an index, a world. -/
abbrev ContT : Type := TFrame → Nat → (w : TWd) → Expr → TRes w.K → Prop

/-- A table: the stop at `t` at the world `w`, under `F`, at `k`, owing `Ψ`. -/
abbrev TableT : Type := TFrame → Nat → (w : TWd) → Expr → ContT → TRes w.K → Prop

/-- A postcondition over values. -/
abbrev TPostV : Type := Nat → (w : TWd) → Val → TRes w.K → Prop

/-- **The continuation's share at the tree world**: at every extension of the stop's world, on
the share's re-reading there, resumed at every answer at every `k′ < k` under a frame meeting
`F` and the entry's `fd`; cancellable when the entry is. -/
def contShareT (en : OpEntT) (F : TFrame) (k : Nat) (w : TWd) (K : Kont) (v : Val) (Ψ : ContT) :
    TRes w.K → Prop := fun ρ =>
  (en.q = .unr → ρ = PMap.empty) ∧
  ∀ (w' : TWd) (ρ' : TRes w'.K), w.Ext w' ρ → RRw (w := w) (w' := w') ρ ρ' →
    (∀ k', k' < k → ∀ (a : Val) (σ σ' : TRes w'.K), en.PBv v k' w' a σ →
      ResUT.CompS ρ' σ σ' → Ψ (fun w'' ρf => F w'' ρf ∧ en.fd v w'' ρf) k' w'
        (K.plug (.val a)) σ') ∧
    (en.q ≠ .lin → ∀ P, en.fin = some P → P k w' (K.dead.plug (raiseE (.val (cancelVal none)))) ρ')

/-- A stop at a non-abortive operation the table allows. -/
def opTableT (T : OpTabT) : TableT := fun F k w t Ψ ρ =>
  ∃ (K : Kont) (n i : UInt32) (v : Val) (en : OpEntT),
    t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧ T n i = some en ∧
    en.abort = false ∧ ∃ ρa ρk : TRes w.K, ResUT.CompS ρa ρk ρ ∧ en.PA k w v ρa ∧
      contShareT en F k w K v Ψ ρk

/-- A table reads what is owed only below the index it stops at. -/
def TableT.Local (Tb : TableT) : Prop :=
  ∀ F k w t (Ψ Ψ' : ContT) ρ,
    (∀ F' k', k' < k → ∀ w' e ρ', Ψ F' k' w' e ρ' → Ψ' F' k' w' e ρ') →
    Tb F k w t Ψ ρ → Tb F k w t Ψ' ρ

theorem opTableT_local (T : OpTabT) : (opTableT T).Local := by
  intro F k w t Ψ Ψ' ρ hΨ h
  obtain ⟨K, n, i, v, en, h₁, h₂, h₃, h₄, ρa, ρk, hc, hA, hu, hcont⟩ := h
  exact ⟨K, n, i, v, en, h₁, h₂, h₃, h₄, ρa, ρk, hc, hA, hu, fun w' ρ' hE hr =>
    ⟨fun k' hk a σ σ' hB hcσ => hΨ _ k' hk _ _ _ ((hcont w' ρ' hE hr).1 k' hk a σ σ' hB hcσ),
      (hcont w' ρ' hE hr).2⟩⟩

/-! ### The relation -/

/-- A value in `Q`, or a stop the table allows. -/
def cerwpPostT (Tb : TableT) (Q : TPostV) (Ψ : ContT) (F : TFrame) : TPost :=
  fun k w t ρ => (∃ v : Val, t = v.1 ∧ Q k w v ρ) ∨ Tb F k w t Ψ ρ

/-- **`cerwp` over the tree world.** -/
def cerwpT (Tb : TableT) (Q : TPostV) : TFrame → Nat → (w : TWd) → Expr → TRes w.K → Prop
  | F, n, w, e => twp (ℍ := ℍ) F (cerwpPostT Tb Q (fun F' k' w' e' =>
      if _h : k' < n then cerwpT Tb Q F' k' w' e' else fun _ => False) F) n w e
termination_by _ n => n

/-- What `cerwpT` at `N` owes below it. -/
def cerwpTC (Tb : TableT) (Q : TPostV) (N : Nat) : ContT := fun F' k' w' e' =>
  if k' < N then cerwpT (ℍ := ℍ) Tb Q F' k' w' e' else fun _ => False

theorem cerwpT_eq (Tb : TableT) (Q : TPostV) (F : TFrame) (n : Nat) (w : TWd) (e : Expr) :
    cerwpT (ℍ := ℍ) Tb Q F n w e =
      twp (ℍ := ℍ) F (cerwpPostT Tb Q (cerwpTC (ℍ := ℍ) Tb Q n) F) n w e := by
  rw [cerwpT]
  congr 1

theorem cerwpT_unfold_at {Tb : TableT} (hTb : Tb.Local) {Q : TPostV} {F : TFrame}
    {n N : Nat} (hnN : n ≤ N) {w : TWd} {e : Expr} {ρ : TRes w.K}
    (h : cerwpT (ℍ := ℍ) Tb Q F n w e ρ) :
    twp (ℍ := ℍ) F (cerwpPostT Tb Q (cerwpTC (ℍ := ℍ) Tb Q N) F) n w e ρ := by
  rw [cerwpT_eq] at h
  refine twp_mono_le (fun k hk w' t ρ' ht => ?_) h
  rcases ht with ht | ht
  · exact Or.inl ht
  · refine Or.inr (hTb F k w' t _ _ ρ' (fun F' k' hk' w'' e'' ρ'' hΨ => ?_) ht)
    simp only [cerwpTC, show k' < n by omega, show k' < N by omega, if_true] at hΨ ⊢
    exact hΨ

theorem cerwpT_fold_at {Tb : TableT} (hTb : Tb.Local) {Q : TPostV} {F : TFrame}
    {n N : Nat} (hnN : n ≤ N) {w : TWd} {e : Expr} {ρ : TRes w.K}
    (h : twp (ℍ := ℍ) F (cerwpPostT Tb Q (cerwpTC (ℍ := ℍ) Tb Q N) F) n w e ρ) :
    cerwpT (ℍ := ℍ) Tb Q F n w e ρ := by
  rw [cerwpT_eq]
  refine twp_mono_le (fun k hk w' t ρ' ht => ?_) h
  rcases ht with ht | ht
  · exact Or.inl ht
  · refine Or.inr (hTb F k w' t _ _ ρ' (fun F' k' hk' w'' e'' ρ'' hΨ => ?_) ht)
    simp only [cerwpTC, show k' < n by omega, show k' < N by omega, if_true] at hΨ ⊢
    exact hΨ

theorem cerwpT_zero {Tb : TableT} {Q : TPostV} {F : TFrame} {w : TWd} {e : Expr}
    {ρ : TRes w.K} : cerwpT (ℍ := ℍ) Tb Q F 0 w e ρ := by
  rw [cerwpT_eq]; exact twp_zero

/-- **`cerwpT` is monotone along world extension.** -/
theorem cerwpT_kripke {Tb : TableT} {Q : TPostV} {F : TFrame} {n : Nat} {w w₁ : TWd}
    {e : Expr} {ρ : TRes w.K} {ρ₁ : TRes w₁.K} (hE : w.Ext w₁ ρ)
    (hr : RRw (w := w) (w' := w₁) ρ ρ₁) (h : cerwpT (ℍ := ℍ) Tb Q F n w e ρ) :
    cerwpT (ℍ := ℍ) Tb Q F n w₁ e ρ₁ := by
  rw [cerwpT_eq] at h ⊢
  exact twp_kripke hE hr h

/-- A deterministic step in front of a `cerwpT`, paid. -/
theorem cerwpT_step {Tb : TableT} (hL : Tb.Local) {Q : TPostV} {F : TFrame} {n : Nat}
    {w : TWd} {e e' : Expr} {ρ : TRes w.K} (hdet : ∀ μ, Step1Only (ℍ := ℍ) μ e μ e')
    (h : cerwpT (ℍ := ℍ) Tb Q F n w e' ρ) : cerwpT (ℍ := ℍ) Tb Q F (n + 1) w e ρ :=
  cerwpT_fold_at hL le_rfl (twp_step hdet (cerwpT_unfold_at hL (Nat.le_succ n) h))

/-- A value in the postcondition, at every extension. -/
theorem cerwpT_val {Tb : TableT} {Q : TPostV} {F : TFrame} {n : Nat} {w : TWd} {v : Val}
    {ρ : TRes w.K}
    (h : ∀ (w₀ : TWd) (ρ₀ : TRes w₀.K), w.Ext w₀ ρ → RRw (w := w) (w' := w₀) ρ ρ₀ → Q n w₀ v ρ₀) :
    cerwpT (ℍ := ℍ) Tb Q F n w v.1 ρ := by
  rw [cerwpT_eq]
  exact twp_here (fun μ => final_val μ v) fun w₀ ρ₀ hE hr => Or.inl ⟨v, rfl, h w₀ ρ₀ hE hr⟩

/-- A table carried along re-reading. -/
def TableT.Mono (Tb : TableT) : Prop :=
  ∀ F k (w w' : TWd) t Ψ (ρ : TRes w.K) (ρ' : TRes w'.K), w.Ext w' ρ →
    RRw (w := w) (w' := w') ρ ρ' → Tb F k w t Ψ ρ → Tb F k w' t Ψ ρ'

/-- **A stop at a non-abortive operation the table allows**, at every extension of the world. -/
theorem cerwpT_perform {T : OpTabT} {Q : TPostV} {F : TFrame} (K : Kont) {m i : UInt32}
    {v : Val} {en : OpEntT} (hK : K.HasHnd m = false) (hT : T m i = some en)
    (ha : en.abort = false) {n : Nat} {w : TWd} {ρ : TRes w.K}
    (h : ∀ (w₀ : TWd) (ρ₀ : TRes w₀.K), w.Ext w₀ ρ → RRw (w := w) (w' := w₀) ρ ρ₀ →
      ∃ ρa ρk : TRes w₀.K, ResUT.CompS ρa ρk ρ₀ ∧ en.PA n w₀ v ρa ∧
        contShareT en F n w₀ K v (cerwpTC (ℍ := ℍ) (opTableT T) Q n) ρk) :
    cerwpT (ℍ := ℍ) (opTableT T) Q F n w (K.plug (performE (.val (opPayload m i v)))) ρ := by
  rw [cerwpT_eq]
  refine twp_here (final_opPlug (r := false) (payloadName_opPayload m i v) hK)
    fun w₀ ρ₀ hE hr => Or.inr ?_
  obtain ⟨ρa, ρk, hc, hA, hs⟩ := h w₀ ρ₀ hE hr
  exact ⟨K, m, i, v, en, rfl, hK, hT, ha, ρa, ρk, hc, hA, hs⟩

/-! ### The resume -/

/-- **Resuming a stored continuation at a grown world.** A share captured at the stop's world
`w`, re-read at any extension `w′` (a graft of the stored task under a lend opened since, a fresh
child, a grown store typing), resumed with an answer in `PBv` beside it, is the continuation at
`w′` under the frame condition extended by the entry's `fd`. -/
theorem contShareT_resume {en : OpEntT} {F : TFrame} {k : Nat} {w w' : TWd} {K : Kont}
    {v : Val} {Ψ : ContT} {ρ : TRes w.K} {ρ' : TRes w'.K} (h : contShareT en F k w K v Ψ ρ)
    (hE : w.Ext w' ρ) (hr : RRw (w := w) (w' := w') ρ ρ') {k' : Nat} (hk : k' < k) {a : Val}
    {σ σ' : TRes w'.K} (hB : en.PBv v k' w' a σ) (hc : ResUT.CompS ρ' σ σ') :
    Ψ (fun w'' ρf => F w'' ρf ∧ en.fd v w'' ρf) k' w' (K.plug (.val a)) σ' :=
  (h.2 w' ρ' hE hr).1 k' hk a σ σ' hB hc

/-- **The share is carried along re-reading**: a stored share is a resource in the scheduler's
frame, re-read whenever the world grows. -/
theorem contShareT_mono {en : OpEntT} {F : TFrame} {k : Nat} {K : Kont} {v : Val} {Ψ : ContT} :
    TRProp.Mono (fun w ρ => ∃ w₀ : TWd, ∃ ρ₀ : TRes w₀.K, w₀.Ext w ρ₀ ∧
      RRw (w := w₀) (w' := w) ρ₀ ρ ∧ contShareT en F k w₀ K v Ψ ρ₀) := by
  intro w w' ρ ρ' hE hr ⟨w₀, ρ₀, hE₀, hr₀, hs⟩
  exact ⟨w₀, ρ₀, hE₀.trans hr₀ hE, RRw.trans hE.1 hr₀ hr, hs⟩

/-- A share captured at `w` is a share at every extension of `w` on its re-reading. -/
theorem contShareT_kripke {en : OpEntT} {F : TFrame} {k : Nat} {w w₁ : TWd} {K : Kont}
    {v : Val} {Ψ : ContT} {ρ : TRes w.K} {ρ₁ : TRes w₁.K} (h : contShareT en F k w K v Ψ ρ)
    (hE : w.Ext w₁ ρ) (hr : RRw (w := w) (w' := w₁) ρ ρ₁) (hu : en.q = .unr → ρ₁ = PMap.empty) :
    contShareT en F k w₁ K v Ψ ρ₁ :=
  ⟨hu, fun w' ρ' hE' hr' => h.2 w' ρ' (hE.trans hr hE') (RRw.trans hE'.1 hr hr')⟩

end BoCa.Fig16.Tree.Wp

end
