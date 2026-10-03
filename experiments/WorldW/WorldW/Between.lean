import WorldW.Wp

/-!
# WorldW — a handler between two lenders (DESIGN §3.4, stage D)

**World: the W-draft, with `σ` unordered** (DESIGN §1.4). Every result here is at an unordered
`σ`, read only through the 6.64 selection.

The configuration: `L₁` (a 6.64 frame `e₁` at `α₁`), inside it a handler `H` of `n`, inside it
`L₂` (a 6.64 frame `e₂` at `α₂`) with an abstract borrower `b₂`; a stop of `n` inside `L₂` hands
`[e₂]` to `H`, whose clause lends a fresh `ℓ₃` mutably (`L₃`) and resumes, cancels or drops `κ`
inside that lend.

What is stated here, verbatim from the design:
* the pieces the probes read (`C3Sem`, `FinW`, `InnerBorrower`, …, `BetweenPremises`);
* the probes of OQ-3 (b): `HandlerBetweenLendersB`, `…Cancel`, `…Drop`;
* the handler lemmas and the clause step, as named propositions (`EwpHandleW`, `EwpHandleWExt`,
  `ClauseBetweenStmt`, …);
* the OQ-3 (a) arm: `ExtentOK`, `ReentryInheritA`, `ReentryFreshA`, `ResumeOutOfOrder`,
  `extentObligation_bypassed`;
* the argument variant: `ArgBelowExtent`, `ArgAboveExtent`.

What is proved here: the OQ-3 (a) arm (`reentryInheritA`, `reentryFreshA`, `resumeOutOfOrder`,
`extentObligation_bypassed`) and the argument variant (`argBelowExtent`, `argAboveExtent`). Each
is a lifetime or resource argument whose premises are the configuration's own: `α₃ ⊏ α₂` from
6.65's H11 at `L₃`'s entry (`κ`'s share, holding `e₂`'s view at `α₂`, is inside `L₃`'s callback,
which lies in `Res_{α₃}`), `α₂ ⊏ h` from `extTabW h`, and `h ⊏ α₃` from the re-entry's nesting.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace WorldW
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Kont hndE hndVal clauseAt)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The clauses -/

/-- `λp. let (_, κ) = p in let r = alloc (inj₁ ()) in
      let q = withborU d₃ r (λ_. λm. let a = κ (inj₁ ()) () in c₃ m ; a) in
      let (r′, a) = q in d₃ r′ ; a`
(`let x = e₁ in e₂` is `(λx. e₂) e₁`; `let (x, y) = e₁ in e₂` is `letpair`, `y` the index 0.) -/
def betweenClause (d₃ : Expr) (c₃ : Val) : Val :=
  Val.lam (.letpair (.var 0)
    (.app (.val (Val.lam
      (.app (.val (Val.lam (.letpair (.var 0) (.seq (.app d₃ (.var 1)) (.var 0)))))
        (.app (.app (.val (withborUV d₃)) (.var 0))
          (.val (Val.lam (.val (Val.lam
            (.app (.val (Val.lam (.seq (.app (.val c₃) (.var 1)) (.var 0))))
              (.app (.app (.var 3) (.val (Val.inj₁ Val.unit))) (.val Val.unit)))))))))))
      (.app (.val (Val.prim .alloc)) (.val (Val.inj₁ Val.unit)))))

/-- The same, cancelling `κ` inside `L₃` and answering by `k₀ ()`:
`… (λ_. λm. κ (inj₂ ()) ; let a = k₀ () in c₃ m ; a) …`. -/
def betweenClauseCancel (d₃ : Expr) (c₃ k₀ : Val) : Val :=
  Val.lam (.letpair (.var 0)
    (.app (.val (Val.lam
      (.app (.val (Val.lam (.letpair (.var 0) (.seq (.app d₃ (.var 1)) (.var 0)))))
        (.app (.app (.val (withborUV d₃)) (.var 0))
          (.val (Val.lam (.val (Val.lam
            (.seq (.app (.var 3) (.val (Val.inj₂ Val.unit)))
              (.app (.val (Val.lam (.seq (.app (.val c₃) (.var 1)) (.var 0))))
                (.app (.val k₀) (.val Val.unit))))))))))))
      (.app (.val (Val.prim .alloc)) (.val (Val.inj₁ Val.unit)))))

/-- The clause tuple with `betweenClause d₃ c₃` at index 0. -/
def betweenClauses (d₃ : Expr) (c₃ : Val) : Val := Val.pair (betweenClause d₃ c₃) Val.unit

/-- The clause tuple with `betweenClauseCancel d₃ c₃ k₀` at index 0. -/
def betweenClausesCancel (d₃ : Expr) (c₃ k₀ : Val) : Val :=
  Val.pair (betweenClauseCancel d₃ c₃ k₀) Val.unit

/-! ### The pieces the probes read -/

/-- `c₃`, run on a `Mut` view of a place, as Core's relation reads the view at the list it runs
at. For a typed `c₃`, `fundamentalC` and `ewpTS_ewpW` give it. -/
def C3Sem (c₃ : Val) (S : VTy) (δ : LSub) (T : OpTab) : Prop :=
  ∀ (ℓ₃ : BoCa.Loc) (α : Life) (σ : List OEnt) (ls : List SRec) (ρ : WRes),
    ptoMutS ℓ₃ α ls (fun ls₀ => vC true S ls₀ δ) ρ →
    ewpW [] σ ls (.app (.val c₃) (.val (.loc ℓ₃))) (opTableW T)
      (fun _ v ρ' => v = Val.unit ∧ ρ'.InStratum α) ρ

/-- `d : Ref S ⊸ 1` frees the source (`fin_run`'s premise). -/
def FinW (d : Expr) (S : VTy) (δ : LSub) : Prop :=
  closedAt 0 d = true ∧
    ∀ ls, wpTS ls d (fun ls'' => vP (.lolli (.ref S) .unit) ls'' δ) PMap.empty

/-- The inner borrower, abstract: 6.64's entry premise at `ℓ₂ : Ref 1`, for every fresh `α₂`
(`wpG_I_frameX`'s premise at `W`). -/
def InnerBorrower (Tin : OpTab) (ℓ₂ : BoCa.Loc) (v₂ b₂ : Val) (δ : LSub) (σ : List OEnt)
    (Qb : List SRec → Val → WProp) (ls : List SRec) : WProp :=
  fresh fun α₂ ρ => ∀ ls', AddAt ls ls' α₂ →
    (∃ r ∈ rsOf ls', r.le = ℓ₂ ∧ r.T = .unit ∧ r.δ = δ) →
    (ptoImmS ℓ₂ α₂ ls' (fun ls₀ => vC true .unit ls₀ δ) ─⋆
      ewpW [] (.imm (⟨ℓ₂, v₂, PMap.empty, .unit, δ⟩, α₂) :: σ) ls'
        (.app (.app (.val b₂) (.val .unit)) (.val (.loc ℓ₂))) (opTableW Tin)
        (exitI ⟨ℓ₂, v₂, PMap.empty, .unit, δ⟩ α₂ Qb)) ρ

/-- The same under OQ-3 (a): the body runs under the marker `hnd n (some h)`, its stops are read
at `extTabW h`, and the entry takes `α₂` below `h`. -/
def InnerBorrowerExt (h : Life) (Tin : OpTab) (n : UInt32) (ℓ₂ : BoCa.Loc) (v₂ b₂ : Val)
    (δ : LSub) (σ : List OEnt) (Qb : List SRec → Val → WProp) (ls : List SRec) : WProp :=
  fresh fun α₂ ρ => α₂ ⊏ h → ∀ ls', AddAt ls ls' α₂ →
    (∃ r ∈ rsOf ls', r.le = ℓ₂ ∧ r.T = .unit ∧ r.δ = δ) →
    (ptoImmS ℓ₂ α₂ ls' (fun ls₀ => vC true .unit ls₀ δ) ─⋆
      ewpW [] (.imm (⟨ℓ₂, v₂, PMap.empty, .unit, δ⟩, α₂) :: .hnd n (some h) :: σ) ls'
        (.app (.app (.val b₂) (.val .unit)) (.val (.loc ℓ₂))) (extTabW h (opTableW Tin))
        (exitI ⟨ℓ₂, v₂, PMap.empty, .unit, δ⟩ α₂ Qb)) ρ

/-- The body's answer: the pair `withborUE d₂` returns, the place `ℓ₂` owned beside the inner
borrower's answer in `Qb` (GhostEnd's `finPost` with the answer read through `Qb`). -/
def finPostW (ℓ₂ : BoCa.Loc) (δ : LSub) (Qb : List SRec → Val → WProp) :
    List SRec → Val → WProp :=
  fun ls v => ex fun u => ⌜v = Val.pair (.loc ℓ₂) u⌝ ⋆ (GhostEnd.owner ℓ₂ .unit δ ls ⋆ Qb ls u)

/-- The return clause: from the body's answer, `hr` answers in `L₁`'s borrower postcondition. -/
def HretW (hr : Val) (ℓ₂ : BoCa.Loc) (δ : LSub) (Qb : List SRec → Val → WProp) (Tout : OpTab)
    (σ : List OEnt) (Qout : List SRec → Val → WProp) : Prop :=
  ∀ ls v ρ, finPostW ℓ₂ δ Qb ls v ρ →
    ewpW [] σ ls (.app (.val hr) (.val v)) (opTableW Tout) Qout ρ

/-- `n : 1 ↠ 1`: its argument and answer hold nothing. -/
def UnitOp (T : OpTab) (n : UInt32) : Prop :=
  ∀ i en ls w ρ', T n i = some en →
    (en.PA ls w ρ' → ρ' = PMap.empty) ∧ (en.PB ls w ρ' → ρ' = PMap.empty)

/-- The cancelling clause's own answer: `k₀ ()`, from nothing, in the handler's outer
postcondition. -/
def FallbackW (k₀ : Val) (Tout : OpTab) (σ : List OEnt) (Qout : List SRec → Val → WProp) :
    Prop :=
  ∀ ls, ewpW [] σ ls (.app (.val k₀) (.val .unit)) (opTableW Tout) Qout PMap.empty

/-- The premises every between-lenders statement shares. -/
def BetweenPremises (Tin Tout : OpTab) (n : UInt32) (T₃ : LifeVar → VTy) (p₁ : FrameRec)
    (α₁ : Life) (x₁ : LifeVar) (δ : LSub) (Q Qb : List SRec → Val → WProp) (ℓ₂ : BoCa.Loc)
    (v₂ b₂ c₃ hr : Val) (d₂ d₃ : Expr) (σ : List OEnt) (ls : List SRec) (ρ : WRes) : Prop :=
  n ≠ 0 ∧ (∀ m i, m ≠ n → Tin m i = Tout m i) ∧
  ClosedOps Tin ∧ Tin.Local ∧ NoUnr Tin ∧ UnitOp Tin n ∧ QExt Q ∧
  δ.find? x₁ = some α₁ ∧ FinW d₂ .unit δ ∧ FinW d₃ (T₃ x₁) δ ∧ C3Sem c₃ (T₃ x₁) δ Tout ∧
  HretW hr ℓ₂ δ Qb Tout (.imm (p₁, α₁) :: σ) (exitI p₁ α₁ Q) ∧
  OpenInv [] ls (.imm (p₁, α₁)) ρ ∧
  (ptoImmS p₁.le α₁ ls (fun ls₀ => vC true p₁.T ls₀ p₁.δ) ⋆
    GhostEnd.ownerI ℓ₂ v₂ .unit δ ls ⋆
    InnerBorrower Tin ℓ₂ v₂ b₂ δ (.hnd n none :: .imm (p₁, α₁) :: σ) Qb ls) ρ

/-! ### The probes, OQ-3 (b): no extent -/

/-- The resume path. -/
def HandlerBetweenLendersB (T₃ : LifeVar → VTy) : Prop :=
  ∀ (Tin : OpTab) (n : UInt32) (p₁ : FrameRec) (α₁ : Life) (x₁ : LifeVar) (δ : LSub)
    (Q Qb : List SRec → Val → WProp) (ℓ₂ : BoCa.Loc) (v₂ b₂ c₃ hr : Val) (d₂ d₃ : Expr)
    (σ : List OEnt) (ls : List SRec) (ρ : WRes),
    OpAt Tin n .lin →
    BetweenPremises Tin OpTab.empty n T₃ p₁ α₁ x₁ δ Q Qb ℓ₂ v₂ b₂ c₃ hr d₂ d₃ σ ls ρ →
    ewpW [.imm (p₁, α₁)] σ ls
      (hndE (hndVal n hr (betweenClauses d₃ c₃))
        (.app (.app (.val (withborUV d₂)) (.val (.loc ℓ₂))) (.val b₂)))
      (opTabW OpTab.empty (GhostEnd.ownerI p₁.le p₁.v p₁.T p₁.δ)) Q ρ

/-- The cancel path: `n` affine, and the clause cancels `κ` inside `L₃`, then answers by `k₀`. -/
def HandlerBetweenLendersBCancel (T₃ : LifeVar → VTy) : Prop :=
  ∀ (Tin : OpTab) (n : UInt32) (p₁ : FrameRec) (α₁ : Life) (x₁ : LifeVar) (δ : LSub)
    (Q Qb : List SRec → Val → WProp) (ℓ₂ : BoCa.Loc) (v₂ b₂ c₃ hr k₀ : Val) (d₂ d₃ : Expr)
    (σ : List OEnt) (ls : List SRec) (ρ : WRes),
    OpAt Tin n .aff → FallbackW k₀ OpTab.empty (.imm (p₁, α₁) :: σ) (exitI p₁ α₁ Q) →
    BetweenPremises Tin OpTab.empty n T₃ p₁ α₁ x₁ δ Q Qb ℓ₂ v₂ b₂ c₃ hr d₂ d₃ σ ls ρ →
    ewpW [.imm (p₁, α₁)] σ ls
      (hndE (hndVal n hr (betweenClausesCancel d₃ c₃ k₀))
        (.app (.app (.val (withborUV d₂)) (.val (.loc ℓ₂))) (.val b₂)))
      (opTabW OpTab.empty (GhostEnd.ownerI p₁.le p₁.v p₁.T p₁.δ)) Q ρ

/-- The drop path: an abortive `f` that `H` forwards. Raised from `b₂`'s continuation after the
resume inside `L₃`, it unwinds `e₂`, then `e₃`, then `e₁`. -/
def HandlerBetweenLendersBDrop (T₃ : LifeVar → VTy) : Prop :=
  ∀ (Tin : OpTab) (n f : UInt32) (enf : OpEnt) (p₁ : FrameRec) (α₁ : Life) (x₁ : LifeVar)
    (δ : LSub) (Q Qb : List SRec → Val → WProp) (ℓ₂ : BoCa.Loc) (v₂ b₂ c₃ hr : Val)
    (d₂ d₃ : Expr) (σ : List OEnt) (ls : List SRec) (ρ : WRes),
    f ≠ n → f ≠ 0 → enf.abort = true → OpAt Tin n .lin →
    BetweenPremises Tin (OpTab.ext f 0 enf OpTab.empty) n T₃ p₁ α₁ x₁ δ Q Qb ℓ₂ v₂ b₂ c₃ hr
      d₂ d₃ σ ls ρ →
    ewpW [.imm (p₁, α₁)] σ ls
      (hndE (hndVal n hr (betweenClauses d₃ c₃))
        (.app (.app (.val (withborUV d₂)) (.val (.loc ℓ₂))) (.val b₂)))
      (opTabW (OpTab.ext f 0 enf OpTab.empty) (GhostEnd.ownerI p₁.le p₁.v p₁.T p₁.δ)) Q ρ

/-- The two payload types the probes are instantiated at: list-stable, and list-reading. -/
def T3Stable : LifeVar → VTy := fun _ => .sum .unit .unit
def T3Reads : LifeVar → VTy := fun x₁ => .sum .unit (.imm (.var x₁) .unit)

/-! ### The handler lemmas and the clause step, as named propositions -/

/-- `ewp_handle` (`Core/EffRules.lean:615`) at `W`, the body at `hnd n none :: σ`, at every
obligation `τb`. -/
def EwpHandleW : Prop :=
  ∀ (Tin Tout : OpTab) (n : UInt32), n ≠ 0 → (∀ m i, m ≠ n → Tin m i = Tout m i) →
  ∀ (hr hs : Val) (Qin Qout : List SRec → Val → WProp),
    (∀ σ ls v ρ, Qin ls v ρ → ewpW [] σ ls (.app (.val hr) (.val v)) (opTableW Tout) Qout ρ) →
    (∀ i en, Tin n i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ τ' σ ls v (κ : Val) ρ,
        (en.PA ls v ⋆ KapRelWB Tout Qout en σ ls τ' κ) ρ →
        ewpW τ' σ ls (.app (.val c) (.pair (.val v) κ.1)) (opTableW Tout) Qout ρ) ∧
      (en.abort = true → ∀ σ ls v ρ, en.PA ls v ρ →
        ewpW [] σ ls (.app (.val c) (.val v)) (opTableW Tout) Qout ρ)) →
    ∀ {τb σ : List OEnt} {ls : List SRec} {e : Expr} {ρ : WRes},
      ewpW τb (.hnd n none :: σ) ls e (opTableW Tin) Qin ρ →
      ewpW τb σ ls (hndE (hndVal n hr hs) e) (opTableW Tout) Qout ρ

/-- 6.112 at a handler entry, read relative to the entries the entered expression holds: the
closed resource is in `Res_h`, and every tag of the list outside those entries' lineages is above
`h`. -/
def ExtentRes (h : Life) (τ : List OEnt) (ls : List SRec) (ρ : WRes) : Prop :=
  (∀ ρc, Close τ ρ ρc → ρc.InStratum h) ∧ (∀ x ∈ ls, (∀ e ∈ τ, ¬ LinOf e x) → h ⊏ x.2)

/-- The site is nested inside every lend and handler extent around it, as a borrow's lifetime is
(D-ORD (3), read at the handler). -/
def ExtentNest (h : Life) (σ : List OEnt) : Prop :=
  ∀ e ∈ σ, ∀ β, e.ordLife? = some β → h ⊏ β

def ExtentOK (h : Life) (τ σ : List OEnt) (ls : List SRec) (ρ : WRes) : Prop :=
  ExtentRes h τ ls ρ ∧ ExtentNest h σ

/-- OQ-3 (a)'s `[handle]`: the site opens `h`, chosen at the entry (`ExtentOK`), and the body's
stops are read at `extTabW h`. The reinstalled handler in `κ` re-enters at `h`. -/
def EwpHandleWExt : Prop :=
  ∀ (h : Life) (Tin Tout : OpTab) (n : UInt32), n ≠ 0 → (∀ m i, m ≠ n → Tin m i = Tout m i) →
  ∀ (hr hs : Val) (Qin Qout : List SRec → Val → WProp),
    (∀ σ ls v ρ, Qin ls v ρ → ewpW [] σ ls (.app (.val hr) (.val v)) (opTableW Tout) Qout ρ) →
    (∀ i en, Tin n i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
      (en.abort = false → ∀ τ' σ ls v (κ : Val) ρ,
        (en.PA ls v ⋆ KapRelW Tout Qout en (fun σ' ls' ρ' => ExtentOK h τ' σ' ls' ρ') σ ls τ' κ)
          ρ →
        ewpW τ' σ ls (.app (.val c) (.pair (.val v) κ.1)) (opTableW Tout) Qout ρ) ∧
      (en.abort = true → ∀ σ ls v ρ, en.PA ls v ρ →
        ewpW [] σ ls (.app (.val c) (.val v)) (opTableW Tout) Qout ρ)) →
    ∀ {τb σ : List OEnt} {ls : List SRec} {e : Expr} {ρ : WRes}, ExtentOK h τb σ ls ρ →
      ewpW τb (.hnd n (some h) :: σ) ls e (extTabW h (opTableW Tin)) Qin ρ →
      ewpW τb σ ls (hndE (hndVal n hr hs) e) (opTableW Tout) Qout ρ

/-- The clause, resumed path: given `κ` holding `[e₂]` at the handler's outer stack `e₁ :: σ`. -/
def ClauseBetweenStmt (T₃ : LifeVar → VTy) : Prop :=
  ∀ {Tout : OpTab} {en : OpEnt} {p₁ p₂ : FrameRec} {α₁ α₂ : Life} {x₁ : LifeVar} {δ : LSub}
    {Q : List SRec → Val → WProp} {c₃ : Val} {d₃ : Expr} {σ : List OEnt} {ls : List SRec}
    {v κ : Val} {ρ : WRes},
    en.abort = false ∧ en.q = .lin →
    (∀ ls w ρ', en.PA ls w ρ' → ρ' = PMap.empty) → (∀ ls w ρ', en.PB ls w ρ' → ρ' = PMap.empty) →
    FinW d₃ (T₃ x₁) δ → C3Sem c₃ (T₃ x₁) δ Tout → δ.find? x₁ = some α₁ →
    (en.PA ls v ⋆ KapRelWB Tout (exitI p₁ α₁ Q) en (.imm (p₁, α₁) :: σ) ls [.imm (p₂, α₂)] κ)
      ρ →
    ewpW [.imm (p₂, α₂)] (.imm (p₁, α₁) :: σ) ls
      (.app (.val (betweenClause d₃ c₃)) (.pair (.val v) κ.1)) (opTableW Tout) (exitI p₁ α₁ Q) ρ

/-- The clause, cancel path. -/
def ClauseBetweenCancelStmt (T₃ : LifeVar → VTy) : Prop :=
  ∀ {Tout : OpTab} {en : OpEnt} {p₁ p₂ : FrameRec} {α₁ α₂ : Life} {x₁ : LifeVar} {δ : LSub}
    {Q : List SRec → Val → WProp} {c₃ k₀ : Val} {d₃ : Expr} {σ : List OEnt} {ls : List SRec}
    {v κ : Val} {ρ : WRes},
    en.abort = false ∧ en.q = .aff →
    (∀ ls w ρ', en.PA ls w ρ' → ρ' = PMap.empty) → (∀ ls w ρ', en.PB ls w ρ' → ρ' = PMap.empty) →
    FinW d₃ (T₃ x₁) δ → C3Sem c₃ (T₃ x₁) δ Tout → δ.find? x₁ = some α₁ →
    FallbackW k₀ Tout (.imm (p₁, α₁) :: σ) (exitI p₁ α₁ Q) →
    (en.PA ls v ⋆ KapRelWB Tout (exitI p₁ α₁ Q) en (.imm (p₁, α₁) :: σ) ls [.imm (p₂, α₂)] κ)
      ρ →
    ewpW [.imm (p₂, α₂)] (.imm (p₁, α₁) :: σ) ls
      (.app (.val (betweenClauseCancel d₃ c₃ k₀)) (.pair (.val v) κ.1)) (opTableW Tout)
      (exitI p₁ α₁ Q) ρ

/-- The clause under OQ-3 (a)'s rule: `κ` carries the re-entry obligation `ExtentOK h [e₂]`. -/
def ClauseBetweenAStmt (T₃ : LifeVar → VTy) (h : Life) : Prop :=
  ∀ {Tout : OpTab} {en : OpEnt} {p₁ p₂ : FrameRec} {α₁ α₂ : Life} {x₁ : LifeVar} {δ : LSub}
    {Q : List SRec → Val → WProp} {c₃ : Val} {d₃ : Expr} {σ : List OEnt} {ls : List SRec}
    {v κ : Val} {ρ : WRes},
    en.abort = false ∧ en.q = .lin →
    (∀ ls w ρ', en.PA ls w ρ' → ρ' = PMap.empty) → (∀ ls w ρ', en.PB ls w ρ' → ρ' = PMap.empty) →
    FinW d₃ (T₃ x₁) δ → C3Sem c₃ (T₃ x₁) δ Tout → δ.find? x₁ = some α₁ →
    (en.PA ls v ⋆ KapRelW Tout (exitI p₁ α₁ Q) en
        (fun σ' ls' ρ' => ExtentOK h [.imm (p₂, α₂)] σ' ls' ρ') (.imm (p₁, α₁) :: σ) ls
        [.imm (p₂, α₂)] κ) ρ →
    ewpW [.imm (p₂, α₂)] (.imm (p₁, α₁) :: σ) ls
      (.app (.val (betweenClause d₃ c₃)) (.pair (.val v) κ.1)) (opTableW Tout) (exitI p₁ α₁ Q) ρ

/-! ### The OQ-3 (a) arm -/

/-- OQ-3 (a), the reinstalled handler re-entering at the extent `h` its first entry chose. At the
call of `κ` inside `L₃`: `κ`'s share holds `e₂` (`Holds`) inside `L₃`'s callback, which is in
`Res_{α₃}` (6.65's H11); the first stop handed `e₂` under `extTabW h`, which puts `α₂` below `h`.
The re-entry's nesting conjunct then fails. -/
def ReentryInheritA : Prop :=
  ∀ (h α₂ α₃ : Life) (p₂ : FrameRec) (ℓ₃ : BoCa.Loc) (S₃ : VTy) (δ : LSub) (σ : List OEnt)
    (ls : List SRec) (ρk ρb ρκ : WRes),
    Holds [.imm (p₂, α₂)] ρk → ResU.Le ρk ρb → ρb.InStratum α₃ →           -- L₃'s H11
    α₂ ⊏ h →                                                                -- extTabW h, first stop
    ¬ ExtentOK h [.imm (p₂, α₂)] (.mut ℓ₃ α₃ S₃ δ :: σ) ls ρκ

/-- OQ-3 (a), the reinstalled handler opening a fresh extent `h′` at each call, as a new site does.
At the call inside `L₃`, any `h′` meeting the re-entry obligation is below `α₃`, hence below
`α₂`. -/
def ReentryFreshA : Prop :=
  ∀ (h' α₂ α₃ : Life) (p₂ : FrameRec) (ℓ₃ : BoCa.Loc) (S₃ : VTy) (δ : LSub) (σ : List OEnt)
    (ls : List SRec) (ρk ρb ρκ : WRes),
    Holds [.imm (p₂, α₂)] ρk → ResU.Le ρk ρb → ρb.InStratum α₃ →
    ExtentOK h' [.imm (p₂, α₂)] (.mut ℓ₃ α₃ S₃ δ :: σ) ls ρκ →
    ¬ (α₂ ⊏ h')

/-- Under D-ORD (OQ-8), read on the stack the resumed term sits under. Inside `L₃`, `κ`'s run
holds `e₂` above `e₃`, out of nesting order, under OQ-3 (b) (`mk = none`) and under (a). -/
def ResumeOutOfOrder : Prop :=
  ∀ (n : UInt32) (mk : Option Life) (α₂ α₃ : Life) (p₂ : FrameRec) (ℓ₃ : BoCa.Loc) (S₃ : VTy)
    (δ : LSub) (σ : List OEnt) (ρk ρb : WRes),
    Holds [.imm (p₂, α₂)] ρk → ResU.Le ρk ρb → ρb.InStratum α₃ →
    ¬ List.IsChain (· < ·)
        (((([.imm (p₂, α₂), .hnd n mk, .mut ℓ₃ α₃ S₃ δ] : List OEnt) ++ σ)).filterMap OEnt.ordLife?)

/-- Where the extent acts at a stop, past `ClosedOps`. An argument holding a copy of `κ`'s entry's
view, below `h`, is rejected by the table's `CompatW`; `extTabW h` admits it. -/
def ArgBelowExtent : Prop :=
  ∀ (h α₂ : Life) (p₂ : FrameRec) (hR : p₂.R.InStratum (LSet.singleton α₂).join)
    (ρk ρ : WRes),
    α₂ ⊏ h → Holds [.imm (p₂, α₂)] ρk → (∀ ρc, Close [.imm (p₂, α₂)] ρk ρc → ρc.InStratum h) →
    ResU.CompS (ResU.single p₂.le (CellU.immOf (LSet.singleton α₂) p₂.v p₂.R hR)) ρk ρ →
    ¬ CompatW [.imm (p₂, α₂)]
        (ResU.single p₂.le (CellU.immOf (LSet.singleton α₂) p₂.v p₂.R hR)) ρk ∧
      (∀ ρc, Close [.imm (p₂, α₂)] ρ ρc → ρc.InStratum h)

/-- An argument holding a copy of `L₁`'s view, above `h`, at a place `e₂`'s exit does not touch,
is admitted by both. -/
def ArgAboveExtent : Prop :=
  ∀ (h α₁ α₂ : Life) (p₁ p₂ : FrameRec) (hR : p₁.R.InStratum (LSet.singleton α₁).join)
    (ρk ρ : WRes),
    h ⊏ α₁ → p₁.le ≠ p₂.le → Holds [.imm (p₂, α₂)] ρk →
    (∀ ρc, Close [.imm (p₂, α₂)] ρk ρc → ρc.InStratum h ∧
      ResU.Hash (ResU.single p₁.le (CellU.immOf (LSet.singleton α₁) p₁.v p₁.R hR)) ρc) →
    ResU.CompS (ResU.single p₁.le (CellU.immOf (LSet.singleton α₁) p₁.v p₁.R hR)) ρk ρ →
    CompatW [.imm (p₂, α₂)]
        (ResU.single p₁.le (CellU.immOf (LSet.singleton α₁) p₁.v p₁.R hR)) ρk ∧
      (∀ ρc, Close [.imm (p₂, α₂)] ρ ρc → ρc.InStratum h)

/-! ### Proofs: the OQ-3 (a) arm -/

/-- A 6.64 entry that can close holds its view `imm({α}, v, R)` at the top level. -/
theorem holds_imm_get {p : FrameRec} {α : Life} {ρ : WRes} (h : Holds [.imm (p, α)] ρ) :
    ∃ hR, ρ.get p.le = some (CellU.immOf (LSet.singleton α) p.v p.R hR) := by
  obtain ⟨ρc, hc⟩ := h
  obtain ⟨π₁, hstep, -⟩ := closePre_cons_inv hc
  obtain ⟨hR, X, hg, -⟩ := hstep
  exact ⟨hR, hg⟩

/-- An `imm` cell of a part is under the whole's cell at its place. -/
theorem le_get_imm {ρ σ : WRes} (hle : ResU.Le ρ σ) {m : BoCa.Loc} {s : LSet} {v : Val}
    {w : WRes} {h : w.InStratum s.join} (hm : ρ.get m = some (CellU.immOf s v w h)) :
    ∃ (s' : LSet) (h' : w.InStratum s'.join), σ.get m = some (CellU.immOf s' v w h') ∧
      ∀ x, s.mem x → s'.mem x := by
  obtain ⟨T, hT⟩ := hle
  rcases ResU.Comp.get hT m with ⟨e₁, -, -⟩ | ⟨ψ, e₁, -, e⟩ | ⟨ψ, e₁, -, -⟩ |
      ⟨ψ₁, ψ₂, ψ, e₁, e₂, e, hc⟩
  · rw [hm] at e₁; exact absurd e₁ (by simp)
  · rw [hm] at e₁; cases Option.some.inj e₁; exact ⟨s, h, e, fun x hx => hx⟩
  · rw [hm] at e₁; exact absurd e₁ (by simp)
  · rw [hm] at e₁; cases Option.some.inj e₁
    obtain ⟨t, ht, ht', rfl, rfl⟩ := cellCompS_imm_right (CellU.CompS.comm hc)
    exact ⟨t ∪ s, ht', e, fun x hx => Or.inr hx⟩

/-- **6.65's H11 at `L₃`'s entry puts `α₃` below `α₂`.** `κ`'s share holds `e₂`'s view at `α₂`,
and it lies inside a resource in `Res_{α₃}`. -/
theorem below_of_holds {p₂ : FrameRec} {α₂ α₃ : Life} {ρk ρb : WRes}
    (hH : Holds [.imm (p₂, α₂)] ρk) (hle : ResU.Le ρk ρb) (hs : ρb.InStratum α₃) : α₃ ⊏ α₂ := by
  obtain ⟨hR, hg⟩ := holds_imm_get hH
  obtain ⟨s', h', hg', hsub⟩ := le_get_imm hle hg
  have hin := (CellU.inStratum_immOf α₃ s' p₂.v p₂.R h').mp (hs p₂.le _ hg')
  exact lt_of_lt_of_le hin (s'.meet_least α₂ (hsub α₂ rfl))

theorem extentNest_head {h α₃ : Life} {ℓ₃ : BoCa.Loc} {S₃ : VTy} {δ : LSub} {σ : List OEnt}
    (hn : ExtentNest h (.mut ℓ₃ α₃ S₃ δ :: σ)) : h ⊏ α₃ :=
  hn _ List.mem_cons_self α₃ rfl

/-- **`ReentryInheritA`.** With an inherited extent, the re-entry's nesting fails at the call of
`κ` inside `L₃`: `h ⊏ α₃ ⊏ α₂ ⊏ h`. -/
theorem reentryInheritA : ReentryInheritA := by
  intro h α₂ α₃ p₂ ℓ₃ S₃ δ σ ls ρk ρb ρκ hH hle hs hα hok
  exact lt_irrefl _
    (lt_trans (lt_trans (extentNest_head hok.2) (below_of_holds hH hle hs)) hα)

/-- **`ReentryFreshA`.** With a fresh extent per call, any `h′` meeting the re-entry obligation
inside `L₃` is below `α₂`. -/
theorem reentryFreshA : ReentryFreshA := by
  intro h' α₂ α₃ p₂ ℓ₃ S₃ δ σ ls ρk ρb ρκ hH hle hs hok hα
  exact lt_irrefl _
    (lt_trans (lt_trans (extentNest_head hok.2) (below_of_holds hH hle hs)) hα)

/-- **`ResumeOutOfOrder`.** Read on the stack the resumed term sits under, `e₂` is above `e₃`,
out of nesting order, with or without a marker's extent between them. -/
theorem resumeOutOfOrder : ResumeOutOfOrder := by
  intro n mk α₂ α₃ p₂ ℓ₃ S₃ δ σ ρk ρb hH hle hs hch
  have hlt := below_of_holds hH hle hs
  rw [List.isChain_iff_pairwise] at hch
  have hmem : α₃ ∈ (((([.imm (p₂, α₂), .hnd n mk, .mut ℓ₃ α₃ S₃ δ] : List OEnt) ++ σ)).filterMap
      OEnt.ordLife?).tail := by
    cases mk <;> simp [OEnt.ordLife?, OEnt.life?]
  have hhead : (((([.imm (p₂, α₂), .hnd n mk, .mut ℓ₃ α₃ S₃ δ] : List OEnt) ++ σ)).filterMap
      OEnt.ordLife?) = α₂ :: (((([.imm (p₂, α₂), .hnd n mk, .mut ℓ₃ α₃ S₃ δ] : List OEnt) ++
        σ)).filterMap OEnt.ordLife?).tail := by
    simp [OEnt.ordLife?, OEnt.life?]
  rw [hhead] at hch
  exact lt_irrefl _ (lt_trans (List.rel_of_pairwise_cons hch hmem) hlt)

/-- **The relation does not enforce (a)'s nesting** (`ewpW_σmono` at `extra = []`): a `κ` re-entered
under the full obligation at the handler's own stack is `κ` under the resource-and-list part
alone at every extension. -/
theorem extentObligation_bypassed {h : Life} {Tout : OpTab} {Qout : List SRec → Val → WProp}
    {en : OpEnt} {σ : List OEnt} {ls : List SRec} {τ : List OEnt} {κ : Val} {ρ : WRes}
    (hn : ExtentNest h σ) :
    KapRelW Tout Qout en (fun σ' ls' ρ' => ExtentOK h τ σ' ls' ρ') σ ls τ κ ρ →
    KapRelW Tout Qout en (fun _ ls' ρ' => ExtentRes h τ ls' ρ') σ ls τ κ ρ := by
  rintro ⟨hu, hk⟩
  refine ⟨hu, fun extra ls' he => ?_⟩
  obtain ⟨h₁, h₂⟩ := hk [] ls' he
  refine ⟨fun w ρ₁ ρ₂ hB hc hre => ?_, fun hq hre => ?_⟩
  · exact ewpW_σmono_opTabW (h₁ w ρ₁ ρ₂ hB hc ⟨hre, hn⟩) (extra ++ σ) (sigmaLe_append extra σ)
  · exact ewpW_σmono_opTabW (h₂ hq ⟨hre, hn⟩) (extra ++ σ) (sigmaLe_append extra σ)

/-! ### Proofs: the argument variant -/

/-- A singleton beside `ρk` changes nothing away from its place. -/
theorem del_compS_single_eq {m : BoCa.Loc} {c : CellU BoCa.Loc Val} {ρk ρ : WRes}
    (hc : ResU.CompS (ResU.single m c) ρk ρ) : ρ.del m = ρk.del m := by
  classical
  refine PMap.ext fun k => ?_
  by_cases hk : k = m
  · subst hk; rw [ResU.del_get_self, ResU.del_get_self]
  · rw [ResU.del_get_ne _ hk, ResU.del_get_ne _ hk, compS_get_right hc (single_get_none _ hk)]

/-- The only closure of `ρ` by one 6.64 entry. -/
theorem close_imm_iff {p : FrameRec} {α : Life} {ρ ρc : WRes} :
    Close [.imm (p, α)] ρ ρc ↔ CloseE [] (.imm (p, α)) ρ ρc := by
  constructor
  · intro h
    obtain ⟨π₁, hstep, hrest⟩ := closePre_cons_inv h
    rw [closePre_nil_inv hrest]; exact hstep
  · intro h; exact .cons h (.nil _ _)

/-- **`ArgBelowExtent`.** A copy of `κ`'s entry's view in the argument fails the table's `CompatW`
(after the exit the place is `own`, the copy `imm`), while `extTabW h` admits the whole: closing
the composite closes the copy with the view. -/
theorem argBelowExtent : ArgBelowExtent := by
  intro h α₂ p₂ hR ρk ρ _ hH hstr hc
  obtain ⟨hR', hg⟩ := holds_imm_get hH
  refine ⟨fun hcw => ?_, fun ρc hρc => ?_⟩
  · obtain ⟨ρc, hρc⟩ := hH
    obtain ⟨hash, -⟩ := hcw ρc hρc
    obtain ⟨-, X, -, hX, hcX, -⟩ := close_imm_iff.mp hρc
    have hown : ρc.get p₂.le = some (CellU.ownOf p₂.v) := by
      rw [compS_get_right hcX (ResU.del_get_self _ _)]
      exact compS_single_nonimm_get hX (kind_ownOf_ne p₂.v)
    exact kind_ownOf_ne p₂.v
      (hash.1 p₂.le _ _ (ResU.single_get_self _ _) hown).kinds.2
  · obtain ⟨-, X, -, hX, hcX, hv⟩ := close_imm_iff.mp hρc
    refine hstr ρc (close_imm_iff.mpr ⟨hR', X, hg, hX, ?_, hv⟩)
    rwa [del_compS_single_eq hc] at hcX

/-- **`ArgAboveExtent`.** A copy of `L₁`'s view above `h`, at a place `e₂`'s exit does not touch,
is compatible with the closure and inert under it, and the composite closes into `Res_h`. -/
theorem argAboveExtent : ArgAboveExtent := by
  intro h α₁ α₂ p₁ p₂ hR ρk ρ hh hne hH hcl hc
  obtain ⟨hR', hg⟩ := holds_imm_get hH
  have hcp₂ : (ResU.single p₁.le (CellU.immOf (LSet.singleton α₁) p₁.v p₁.R hR)).get p₂.le =
      none := single_get_none _ (Ne.symm hne)
  -- closing a composite with the copy is closing `ρk`, the copy beside
  have hcomp : ∀ X ρc, ResU.CompS
      (ResU.single p₁.le (CellU.immOf (LSet.singleton α₁) p₁.v p₁.R hR)) ρk X →
      Close [.imm (p₂, α₂)] ρk ρc →
      ∃ Xc, Close [.imm (p₂, α₂)] X Xc ∧
        ResU.CompS (ResU.single p₁.le (CellU.immOf (LSet.singleton α₁) p₁.v p₁.R hR)) ρc Xc := by
    intro X ρc hX hρc
    obtain ⟨-, Xe, -, hXe, hcXe, -⟩ := close_imm_iff.mp hρc
    obtain ⟨-, Xc, hXc, hvXc⟩ := (hcl ρc hρc).2
    refine ⟨Xc, close_imm_iff.mpr ⟨hR', Xe, ?_, hXe, ?_, hvXc⟩, hXc⟩
    · rw [compS_get_right hX hcp₂]; exact hg
    · have hXd := compS_del_right hX hcp₂
      obtain ⟨ab, hab, habc⟩ := compS_reassoc' hcXe hXc
      rw [ResU.CompS.functional hab hXd] at habc
      exact habc
  refine ⟨fun ρc hρc => ⟨(hcl ρc hρc).2, fun X hX => hcomp X ρc hX hρc⟩, fun ρc' hρc' => ?_⟩
  obtain ⟨ρc, hρc⟩ := hH
  obtain ⟨Xc, hXc, hcXc⟩ := hcomp ρ ρc hc hρc
  -- the closure of `ρ` is unique: the 6.64 step is a function
  obtain ⟨-, Xe₁, -, hXe₁, hc₁, -⟩ := close_imm_iff.mp hρc'
  obtain ⟨-, Xe₂, -, hXe₂, hc₂, -⟩ := close_imm_iff.mp hXc
  cases ResU.CompS.functional hXe₂ hXe₁
  cases ResU.CompS.functional hc₂ hc₁
  have hcopy : (ResU.single p₁.le
      (CellU.immOf (LSet.singleton α₁) p₁.v p₁.R hR)).InStratum h := by
    intro k ψ e
    by_cases hk : k = p₁.le
    · subst hk; rw [ResU.single_get_self] at e; cases Option.some.inj e; exact hh
    · rw [single_get_none _ hk] at e; exact absurd e (by simp)
  exact (outlives_comp hcXc h).mpr ⟨hcopy, (hcl ρc hρc).1⟩

end WorldW

end
