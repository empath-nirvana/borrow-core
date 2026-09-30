import Core.Steps

/-!
# Core — a cancel whose unwind is intercepted inside `κ`  `[spec §19]`

§19 types `κ`'s cancel branch at `F_Σ 1`, and its term is `ccatch (hnd (n, H) K[raise (⊥, ())])`.
§19's K3 paragraph lets a finaliser's raise supersede a pending unwind. When the finaliser's
raise is caught by a handler *inside* `K`, the computation continues normally, `hnd (n, H)`
returns through `h_ret`, and `ccatch` receives a value. `ccatch` has no step at a value.

The run below builds that configuration: a handler of name `1` whose clause cancels its `κ`,
where `K = hnd (2, H₂) (ubind (N, D) [·])` and the finaliser `D` raises name `2`, which `H₂`
answers with `()`. It reaches `ccatch ()` and stops there, at a term that is not a value.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.CancelIntercept
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont hndE hndVal raiseE performE ccatchE opPayload clauseAt kappa cancelPayload)

/-- The identity. -/
def idV : Val := Val.lam (.var 0)

/-- Handler `1`'s clause: `λp. let (x, k) = p; k (inj₂ ())`, the cancel entry of `κ`. -/
def c₁ : Val := Val.lam (.letpair (.var 0) (.app (.var 0) (.val (Val.inj₂ Val.unit))))

def H₁ : Val := hndVal 1 idV (Val.pair c₁ Val.unit)

/-- Handler `2`'s clause answers `()`. -/
def c₂ : Val := Val.lam (.val Val.unit)

def H₂ : Val := hndVal 2 idV (Val.pair c₂ Val.unit)

/-- The finaliser raises name `2`. -/
def D : Val := Val.lam (raiseE (.val (opPayload 2 0 Val.unit)))

/-- `K = hnd (2, H₂) (ubind (id, D) [·])`. -/
def K : Kont :=
  .appR (.app (.val (.prim .hnd)) (.val H₂)) (.appR (.app (.val (.prim .ubind)) (.val (Val.pair idV D))) .hole)

/-- The program: `hnd (1, H₁) K[perform (1, (0, ()))]`. -/
def prog : Expr := hndE H₁ (K.plug (performE (.val (opPayload 1 0 Val.unit))))

theorem st (K' : Kont) {μ : Heap} {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ a') :
    Step1 (ℍ := ℍ) μ (K'.plug a) μ (K'.plug a') :=
  ⟨K', a, a', rfl, rfl, h⟩

/-- **The run.** `prog` reaches `ccatch ()`. -/
theorem prog_run (μ : Heap) : Steps (ℍ := ℍ) μ prog μ (ccatchE (.val Val.unit)) := by
  have hc₁ : clauseAt (Val.pair c₁ Val.unit).1 (0 : UInt32).toNat = some c₁ := by
    simp [clauseAt, Val.pair, c₁, Val.lam, IsVal.lam]
  have hc₂ : clauseAt (Val.pair c₂ Val.unit).1 (0 : UInt32).toNat = some c₂ := by
    simp [clauseAt, Val.pair, c₂, Val.lam, IsVal.lam]
  let κv : Val := ⟨kappa H₁ K, by unfold kappa; exact .lam⟩
  refine .more (st .hole (Head.hop μ 1 0 idV (Val.pair c₁ Val.unit) c₁ Val.unit K hc₁ rfl)) ?_
  refine .more (st .hole (Head.beta μ _ (Val.pair Val.unit κv))) ?_
  refine .more (st .hole (Head.letpair μ Val.unit κv _)) ?_
  refine .more (st .hole (Head.beta μ _ (Val.inj₂ Val.unit))) ?_
  refine .more (st .hole (Head.case₂ μ Val.unit _ _)) ?_
  refine .more (st .hole (Head.seq μ _)) ?_
  show Steps μ (ccatchE (hndE H₁ (K.plug (raiseE (.val cancelPayload))))) μ _
  refine .more (st (.appR (.val (.prim .ccatch)) (.appR (.app (.val (.prim .hnd)) (.val H₁))
    (.appR (.app (.val (.prim .hnd)) (.val H₂)) .hole)))
    (Head.ufin μ idV D 0 0 Val.unit .hole rfl)) ?_
  refine .more (st (.appR (.val (.prim .ccatch)) (.appR (.app (.val (.prim .hnd)) (.val H₁))
    (.appR (.app (.val (.prim .hnd)) (.val H₂)) (.seq .hole (raiseE (.val cancelPayload))))))
    (Head.beta μ _ Val.unit)) ?_
  show Steps μ ((Kont.appR (.val (.prim .ccatch)) (.appR (.app (.val (.prim .hnd)) (.val H₁))
    .hole)).plug (hndE H₂ ((Kont.seq .hole (raiseE (.val cancelPayload))).plug
      (raiseE (.val (opPayload 2 0 Val.unit)))))) μ _
  refine .more (st _ (Head.hunwind μ 2 0 idV (Val.pair c₂ Val.unit) c₂ Val.unit _ hc₂ rfl)) ?_
  refine .more (st (.appR (.val (.prim .ccatch)) (.appR (.app (.val (.prim .hnd)) (.val H₁))
    .hole)) (Head.beta μ _ Val.unit)) ?_
  show Steps μ ((Kont.appR (.val (.prim .ccatch)) .hole).plug (hndE H₁ (.val Val.unit))) μ _
  refine .more (st _ (Head.hret μ 1 idV (Val.pair c₁ Val.unit) Val.unit)) ?_
  refine .more (st (.appR (.val (.prim .ccatch)) .hole) (Head.beta μ _ Val.unit)) ?_
  exact .refl _ _

/-- `ccatch ()` is not a value and takes no step. -/
theorem ccatch_unit_stuck (μ μ' : Heap) (e' : Expr) :
    ¬ IsVal (ccatchE (.val Val.unit)) ∧ ¬ Step1 (ℍ := ℍ) μ (ccatchE (.val Val.unit)) μ' e' := by
  refine ⟨fun h => (by cases h), fun ⟨K', a, a', hE, _, hh⟩ => ?_⟩
  obtain rfl := plug_primApp hE.symm hh.not_isVal
  simp only [Kont.plug] at hE
  subst hE
  exact head_not_inertApp (p := .ccatch) (v := Val.unit) trivial hh

/-- `prog` runs to a term that is not a value and takes no step. -/
theorem prog_stuck (μ : Heap) : ∃ t, Steps (ℍ := ℍ) μ prog μ t ∧ ¬ IsVal t ∧
    ∀ μ' e', ¬ Step1 (ℍ := ℍ) μ t μ' e' :=
  ⟨_, prog_run μ, (ccatch_unit_stuck μ μ .unit).1, fun μ' e' => (ccatch_unit_stuck μ μ' e').2⟩

end BoCa.Fig16.LogRel.Core.CancelIntercept
