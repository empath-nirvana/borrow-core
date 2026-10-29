import SuspSpike.Lend

/-!
# SuspSpike — class 1 at nesting depth three, every hypothesis discharged

The class hypothesis is satisfiable, and its theorems compose at depth three without a case of
their own:

* `callRow_tabOf`, `argIn_tabOf`: a row of call-like operations, one per name, taking and
  answering `()`; any finite set of names (here `{1, 2, 3}`, `{2, 3}`, `{3}`, `{2}` and `∅`);
* `prog3_lends`: three nested lends of three owned cells, `ℓ₁ ⊃ ℓ₂ ⊃ ℓ₃`, the innermost callback
  performing the operation of name `1` with all three lends open, in the graded relation;
* `prog3`: that computation under three nested tail handlers: the handler of `1` answers by
  performing `2`, the handler of `2` by performing `3`, the handler of `3` by `()`. The whole is
  in `wpTS`: a pure computation of `Ref 1 ⊗ (Ref 1 ⊗ (Ref 1 ⊗ 1))` from the three owners.

Each step is `withborC`, `ewp_handleC` and `tail_hop`, applied once per level.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace SuspSpike
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N Head performE opPayload hndE hndVal clauseAt capTag)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### A class-1 row -/

/-- A linear operation taking and answering `()`, at the empty resource. -/
def unitEnt : OpEnt :=
  ⟨.lin, false, fun _ v ρ => v = Val.unit ∧ ρ = PMap.empty,
    fun _ v ρ => v = Val.unit ∧ ρ = PMap.empty, none, false⟩

/-- The row of the names `ns`, one operation each (index `0`). -/
def tabOf (ns : List UInt32) : OpTab := fun n i => if n ∈ ns ∧ i = 0 then some unitEnt else none

/-- Every operation call-like. -/
def Grade.all : Grade := fun _ _ => true

theorem tabOf_some {ns : List UInt32} {n i : UInt32} {en : OpEnt} (h : tabOf ns n i = some en) :
    n ∈ ns ∧ i = 0 ∧ en = unitEnt := by
  unfold tabOf at h
  split at h
  · rename_i hc; exact ⟨hc.1, hc.2, (Option.some.inj h).symm⟩
  · cases h

theorem callRow_tabOf (ns : List UInt32) : CallRow (tabOf ns) Grade.all := by
  refine ⟨fun n i en h => ?_, fun α n i en h _ ls w τ hB => ?_⟩
  · obtain ⟨-, -, rfl⟩ := tabOf_some h; exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨-, -, rfl⟩ := tabOf_some h
    rw [hB.2]; exact ResU.inStratum_empty α

theorem argIn_tabOf (ns : List UInt32) : ∀ α, ArgIn α (tabOf ns) := by
  intro α n i en h _ ls w τ hA
  obtain ⟨-, -, rfl⟩ := tabOf_some h
  rw [hA.2]; exact ResU.inStratum_empty α

theorem tabOf_le {ns ms : List UInt32} (h : ∀ n ∈ ns, n ∈ ms) : (tabOf ns).Le (tabOf ms) := by
  intro n i en hT
  obtain ⟨hn, rfl, rfl⟩ := tabOf_some hT
  exact ⟨unitEnt, by simp [tabOf, h n hn], OpEnt.Le.refl _⟩

/-! ### Steps -/

/-- A `perform` at a graded table stops at once, its argument at the empty resource and the rest
in the continuation's share. -/
theorem ewp_performC_here {T : OpTab} {C : Grade} {n i : UInt32} {en : OpEnt}
    (hT : T n i = some en) (ha : en.abort = false) (hg : C n i = true) {ls : List SRec}
    {v : Val} {Q : List SRec → Val → WProp} {ρ : WRes} (hA : en.PA ls v PMap.empty)
    (hk : ∀ ls' w τ σ, SameMem ls ls' → en.PB ls' w τ → ResU.CompS ρ τ σ →
      ewpTS ls' (.val w) (opTableC T C) Q σ) :
    ewpTS ls (performE (.val (opPayload n i v))) (opTableC T C) Q ρ :=
  ewp_fold (opTableC_mono T C) (wpG_here _ _ _ ρ (Or.inr
    (stopC_mk' (K := .hole) hg rfl hT ha (compS_empty_left ρ) hA
      fun ls' hs w τ σ hB hc => hk ls' w τ σ hs hB hc)))

/-- A value, with a part holding nothing owned left behind. -/
theorem ewp_val_garbage {Tb : Table} (hTb : Tb.Mono) {ls : List SRec} {v : Val}
    {Q : List SRec → Val → WProp} {ρ ρ₁ ρ₂ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ) (hn : NoOwn ρ₂)
    (h : Q ls v ρ₁) : ewpTS ls (.val v) Tb Q ρ :=
  ewp_fold hTb (wpG_garbage (wpG_mono (fun ls' t σ h' => by
      obtain ⟨w, rfl, ρa, ρb, hc', hn', hq⟩ := h'
      exact ⟨ρa, ρb, hc', hn', Or.inl ⟨w, rfl, hq⟩⟩)
    ((wpTS_iff_wpG ls _ _ ρ).mp (wpTS_val ls v (fun ls' w σ => ∃ ρa ρb : WRes,
      ResU.CompS ρa ρb σ ∧ NoOwn ρb ∧ Q ls' w ρa) ρ ⟨ρ₁, ρ₂, hc, hn, h⟩))))

/-! ### Three nested lends -/

/-- `Λ. λm. M`. -/
def lam2V (M : Expr) : Val := ⟨.lam (.lam M), .lam⟩

/-- The innermost borrower's body: `perform (1, (0, ()))`. -/
def body3 : Expr := performE (.val (opPayload 1 0 Val.unit))

/-- `withbor ℓ f`. -/
def wb (l : BoCa.Loc) (f : Val) : Expr := .app (.app withbor (.val (.loc l))) (.val f)

def f3 : Val := lam2V body3
def f2 (l3 : BoCa.Loc) : Val := lam2V (wb l3 f3)
def f1 (l2 l3 : BoCa.Loc) : Val := lam2V (wb l2 (f2 l3))

/-- `withbor ℓ₁ (Λ. λm₁. withbor ℓ₂ (Λ. λm₂. withbor ℓ₃ (Λ. λm₃. perform (1, (0, ())))))`. -/
def prog3L (l1 l2 l3 : BoCa.Loc) : Expr := wb l1 (f1 l2 l3)

/-- The rows: the body's `{1, 2, 3}`. -/
abbrev T123 : OpTab := tabOf [1, 2, 3]
abbrev Tb123 : Table := opTableC T123 Grade.all

/-- `Ref 1 ⊗ B`. -/
abbrev rT (B : VTy) : VTy := .tensor (.ref .unit) B
abbrev R1 : VTy := rT .unit
abbrev R2 : VTy := rT R1
abbrev R3 : VTy := rT R2

theorem closedAt_wb (l : BoCa.Loc) (f : Val) (hf : closedAt 0 f.1 = true) :
    closedAt 0 (wb l f) = true := by
  have hw : closedAt 0 withbor = true := rfl
  have hl : closedAt 0 (Expr.val (Val.loc l)) = true := rfl
  simp only [wb, closedAt, Bool.and_eq_true]
  exact ⟨⟨hw, hl⟩, hf⟩

theorem closedAt_lam2V (M : Expr) (h : closedAt 0 M = true) : closedAt 0 (lam2V M).1 = true := by
  have h2 : closedAt 2 M = true := closedAt_mono M h (by omega)
  simpa [lam2V, closedAt] using h2

theorem closedAt_body3 : closedAt 0 body3 = true := rfl

theorem closedAt_f3 : closedAt 0 f3.1 = true := closedAt_lam2V _ closedAt_body3
theorem closedAt_f2 (l3 : BoCa.Loc) : closedAt 0 (f2 l3).1 = true :=
  closedAt_lam2V _ (closedAt_wb _ _ closedAt_f3)

/-- The borrower applied: two β-steps to its closed body. -/
theorem ewp_cbApp {Tb : Table} (hTb : Tb.Mono) {M : Expr} (hM : closedAt 0 M = true)
    (l : BoCa.Loc) {ls : List SRec} {Q : List SRec → Val → WProp} {ρ : WRes}
    (h : ewpTS ls M Tb Q ρ) : ewpTS ls (cbApp (lam2V M) l) Tb Q ρ := by
  refine ewp_step hTb (fun μ => (Step1N.head (Head.beta μ (.lam M) Val.unit)
    rfl).plug (Kont.appL .hole (Val.loc l))) ls Q ρ ?_
  refine ewp_step hTb (fun μ => Step1N.head (Head.beta μ _ (Val.loc l)) rfl) ls Q ρ ?_
  have h1 : closedAt 1 M = true := closedAt_mono M hM (by omega)
  rw [subst_closedAt M _ h1 le_rfl, subst_closedAt M _ hM le_rfl]
  exact h

/-- A borrower `Λ. λm. M`, `M` closed, is in the relation at every lend below the stratum of
the resource it captures. -/
theorem fresh_of {l : BoCa.Loc} {T : VTy} {δ : LSub} {ls : List SRec} {M : Expr}
    (hM : closedAt 0 M = true) {Q' : Life → List SRec → Val → WProp} {ρ : WRes}
    (h : ∀ α ρm σ, ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ) ρm → ResU.CompS ρ ρm σ →
      ewpTS ls M Tb123 (Q' α) σ) :
    fresh (fun α => ptoMutS l α ls (fun ls₀ => vC true T ls₀ δ) ─⋆
      ewpTS ls (cbApp (lam2V M) l) Tb123 (Q' α)) ρ := by
  obtain ⟨a, ha⟩ := ρ.exists_atLife
  exact ⟨a, fun α hα => ⟨fun ρm σ hm hc =>
    ewp_cbApp (opTableC_mono _ _) hM l (h α ρm σ hm hc), outlives_of_atLife ha hα⟩⟩

theorem noOwn_ptoMutS {l : BoCa.Loc} {α : Life} {ls : List SRec}
    {P : List SRec → Val → WProp} {ρ : WRes} (h : ptoMutS l α ls P ρ) : NoOwn ρ := by
  obtain ⟨b, u, σ, hσ, Q, hw, ls₀, -, rfl, -⟩ := h
  exact noOwn_single_mut _ _ (by rw [CellU.kind_mutOf]; exact fun c => Kind.noConfusion c)

/-- The borrower's post from a result whose resource lies in `Res_α`. -/
theorem postA_of {l : BoCa.Loc} {δ : LSub} {α : Life} {B : VTy} {ls : List SRec} {r : Val}
    {τ : WRes} (hB : vC true B ls δ r τ) (hτ : τ.InStratum α) :
    postA l .unit δ α (finPost l .unit B δ) ls r τ := by
  refine ⟨fun w ρo σo ho hco ρP σP hP hcP => ?_, hτ⟩
  obtain ⟨y, hy₁, hy₂⟩ := compS_reassoc hco hcP
  exact ⟨y, τ, ResU.CompS.comm hy₂, ⟨w, ρo, ρP, hy₁, ho, hP⟩, hB⟩

/-- A result `(ℓ, b)` of `Ref 1 ⊗ B` lies in every stratum when `b`'s does. -/
theorem rT_inStratum {B : VTy} {ls : List SRec} {δ : LSub} {r : Val} {τ : WRes} {α : Life}
    (hB : ∀ v σ, vC true B ls δ v σ → σ.InStratum α) (h : vC true (rT B) ls δ r τ) :
    τ.InStratum α := by
  obtain ⟨a, b, h⟩ := h
  obtain ⟨-, τ₁, τ₂, hc, ⟨ℓ, w, ha⟩, hb⟩ := pure_sep_iff.mp h
  obtain ⟨-, ρo, ρu, hco, ho, hu⟩ := pure_sep_iff.mp ha
  subst ho
  have hu' := (vC_unit_iff.mp hu).2
  subst hu'
  exact inStratum_compS hc (inStratum_compS hco (ResU.inStratum_single_own α ℓ w)
    (ResU.inStratum_empty α)) (hB b τ₂ hb)

theorem unit_inStratum {ls : List SRec} {δ : LSub} {α : Life} :
    ∀ v σ, vC true .unit ls δ v σ → σ.InStratum α := fun _ _ h => by
  rw [(vC_unit_iff.mp h).2]; exact ResU.inStratum_empty α

theorem hP_unit {δ : LSub} : ∀ ls w σ, vC true .unit ls δ w σ → σ.InStratum (0 : Life) :=
  fun _ _ _ h => unit_inStratum _ _ h

theorem T123_1 : T123 1 0 = some unitEnt := by simp [tabOf]

/-- The innermost borrower, at any captured resource holding nothing owned. -/
theorem cb3 (l3 : BoCa.Loc) {δ : LSub} {ls : List SRec} {ρ : WRes} (hn : NoOwn ρ) :
    fresh (fun α => ptoMutS l3 α ls (fun ls₀ => vC true .unit ls₀ δ) ─⋆
      ewpTS ls (cbApp f3 l3) Tb123 (postA l3 .unit δ α (finPost l3 .unit .unit δ))) ρ := by
  refine fresh_of closedAt_body3 fun α ρm σ hm hc => ?_
  refine ewp_performC_here T123_1 rfl rfl ⟨rfl, rfl⟩ fun ls' w τ σ' hs hB hc' => ?_
  obtain ⟨rfl, rfl⟩ := hB
  have e : σ' = σ := ResU.CompS.functional hc' (ResU.comp_empty_right σ)
  rw [e]
  exact ewp_val_garbage (opTableC_mono _ _) (compS_empty_left σ)
    (noOwn_compS hc hn (noOwn_ptoMutS hm))
    (postA_of (B := .unit) (vC_unit_iff.mpr ⟨rfl, rfl⟩) (ResU.inStratum_empty α))

/-- A middle borrower: it lends the next cell, whose owner it captures beside the rest `ρ_r`; the
next borrower is in the relation at the rest and the view it was lent. -/
theorem cbMid {l l' : BoCa.Loc} {f : Val} (hf : closedAt 0 f.1 = true) {B : VTy}
    (hBs : ∀ ls δ α v σ, vC true B ls δ v σ → σ.InStratum α)
    {δ : LSub} {ls : List SRec} {ρo ρr ρ : WRes}
    (ho : ptoOwn l' Val.unit ρo) (hc : ResU.CompS ρo ρr ρ)
    (hinner : ∀ α ρm y, ptoMutS l α ls (fun ls₀ => vC true .unit ls₀ δ) ρm →
      ResU.CompS ρr ρm y →
      fresh (fun α => ptoMutS l' α ls (fun ls₀ => vC true .unit ls₀ δ) ─⋆
        ewpTS ls (cbApp f l') Tb123 (postA l' .unit δ α (finPost l' .unit B δ))) y) :
    fresh (fun α => ptoMutS l α ls (fun ls₀ => vC true .unit ls₀ δ) ─⋆
      ewpTS ls (cbApp (lam2V (wb l' f)) l) Tb123
        (postA l .unit δ α (finPost l .unit (rT B) δ))) ρ := by
  refine fresh_of (closedAt_wb _ _ hf) fun α ρm σ hm hcm => ?_
  obtain ⟨y, hy, hσ⟩ := compS_reassoc hc hcm
  have hw := withborC (callRow_tabOf [1, 2, 3]) (argIn_tabOf [1, 2, 3]) (T₂ := B) hP_unit f ls
    Val.unit σ ⟨ρo, y, hσ, ho, PMap.empty, y, compS_empty_left y, vC_unit_iff.mpr ⟨rfl, rfl⟩,
      hinner α ρm y hm hy⟩
  exact ewp_mono (opTableC_mono _ _) (fun _ _ _ _ h => h)
    (fun ls' r τ h => postA_of h (rT_inStratum (fun v σ h => hBs ls' δ α v σ h) h)) hw

theorem R1_inStratum : ∀ ls δ α v σ, vC true R1 ls δ v σ → σ.InStratum α :=
  fun _ _ _ _ _ h => rT_inStratum (fun _ _ h => unit_inStratum _ _ h) h

theorem R2_inStratum : ∀ ls δ α v σ, vC true R2 ls δ v σ → σ.InStratum α :=
  fun ls δ α _ _ h => rT_inStratum (fun v σ h => R1_inStratum ls δ α v σ h) h

/-- The middle borrower, capturing the innermost cell's owner beside a part holding nothing
owned. -/
theorem cb2 (l2 l3 : BoCa.Loc) {δ : LSub} {ls : List SRec} {ρo ρj ρ : WRes}
    (ho : ptoOwn l3 Val.unit ρo) (hj : NoOwn ρj) (hc : ResU.CompS ρo ρj ρ) :
    fresh (fun α => ptoMutS l2 α ls (fun ls₀ => vC true .unit ls₀ δ) ─⋆
      ewpTS ls (cbApp (f2 l3) l2) Tb123 (postA l2 .unit δ α (finPost l2 .unit R1 δ))) ρ :=
  cbMid closedAt_f3 (fun _ _ α v σ h => unit_inStratum (α := α) v σ h) ho hc
    (fun _ _ _ hm hy => cb3 l3 (noOwn_compS hy hj (noOwn_ptoMutS hm)))

/-- **Three nested lends spanning a call-like stop.** From the three owners, the program is in
the graded relation at `{1, 2, 3}`, answering `Ref 1 ⊗ (Ref 1 ⊗ (Ref 1 ⊗ 1))`. -/
theorem prog3_lends (l1 l2 l3 : BoCa.Loc) {δ : LSub} {ls : List SRec} :
    Entails (ptoOwn l1 Val.unit ⋆ ptoOwn l2 Val.unit ⋆ ptoOwn l3 Val.unit)
      (ewpTS ls (prog3L l1 l2 l3) Tb123 (fun ls r => vC true R3 ls δ r)) := by
  rintro ρ ⟨ρ1, ρ23, hc, h1, ρ2, ρ3, hc23, h2, h3⟩
  have hin := cbMid (l := l1) (l' := l2) (f := f2 l3) (B := R1) (δ := δ) (ls := ls)
    (closedAt_f2 l3) R1_inStratum h2 hc23
    (fun _ _ _ hm hy => cb2 l2 l3 h3 (noOwn_ptoMutS hm) hy)
  exact withborC (callRow_tabOf [1, 2, 3]) (argIn_tabOf [1, 2, 3]) (T₂ := R2) hP_unit _ ls
    Val.unit ρ ⟨ρ1, ρ23, hc, h1, PMap.empty, ρ23, compS_empty_left ρ23,
      vC_unit_iff.mpr ⟨rfl, rfl⟩, hin⟩

/-! ### Three nested tail handlers -/

/-- `λx. x`. -/
def idV : Val := ⟨.lam (.var 0), .lam⟩

/-- `λx. perform (m, (0, x))`: the answering function of a clause that answers by performing the
operation of the name `m`. -/
def gpV (m : UInt32) : Val := ⟨.lam (performE (opArgE m 0 (.var 0))), .lam⟩

/-- The tail clause `λ(x, κ). (λw. κ.1 w) (g x)`. -/
def clV (g : Val) : Val :=
  ⟨tailClause 0 false (.val (Val.pair g Val.unit)), isVal_tailClause _ _ _⟩

/-- The handler of the name `n`, with one linear operation, answering by `g`. -/
def hH (n : UInt32) (g : Val) : Val := hndVal n (qualsVal [.lin]) idV (Val.pair (clV g) Val.unit)

/-- **The program.** The three nested lends, under the handlers of `1` (answering by performing
`2`), `2` (answering by performing `3`) and `3` (answering `()`). -/
def prog3 (l1 l2 l3 : BoCa.Loc) : Expr :=
  hndE (hH 3 idV) (hndE (hH 2 (gpV 3)) (hndE (hH 1 (gpV 2)) (prog3L l1 l2 l3)))

theorem ewp_id {Tb : Table} (hTb : Tb.Mono) {ls : List SRec} {v : Val}
    {Q : List SRec → Val → WProp} {ρ : WRes} (h : Q ls v ρ) :
    ewpTS ls (.app (.val idV) (.val v)) Tb Q ρ :=
  ewp_step hTb (fun μ => Step1N.head (Head.beta μ (.var 0) v) rfl) ls Q ρ
    (by simp only [Expr.subst]; exact ewp_val hTb h)

theorem clauseAt_hH (g : Val) : clauseAt (Val.pair (clV g) Val.unit).1 0 = some (clV g) := by
  simp [clauseAt, Val.pair, clV, isVal_tailClause]

theorem clV_steps (g v κ : Val) :
    PureSteps (.app (.val (clV g)) (.pair (.val v) κ.1)) ((resK κ).plug (.app (.val g) (.val v))) :=
  tailClause_steps 0 (Val.pair g Val.unit) g v κ
    (pickE_steps 0 g Val.unit _ rfl g (fun _ => rfl) (fun j' h => absurd h (by omega)))

/-- `λx. perform (m, (0, x))` answers in the graded relation at `{m}`. -/
theorem gp_spec (m : UInt32) {ls : List SRec} {v : Val} {ρ : WRes} (h : unitEnt.PA ls v ρ) :
    ewpTS ls (.app (.val (gpV m)) (.val v)) (opTableC (tabOf [m]) Grade.all) unitEnt.PB ρ := by
  obtain ⟨rfl, rfl⟩ := h
  refine ewp_step (opTableC_mono _ _) (fun μ => Step1N.head (Head.beta μ _ Val.unit) rfl) ls _ _ ?_
  have e : Expr.subst 0 Val.unit (performE (opArgE m 0 (.var 0))) =
      performE (.val (opPayload m 0 Val.unit)) := by
    simp [performE, opArgE, opPayload, Expr.subst, Val.pair, Val.i32]
  rw [e]
  refine ewp_performC_here (en := unitEnt) (by simp [tabOf]) rfl rfl ⟨rfl, rfl⟩
    fun ls' w τ σ _ hB hc => ?_
  have hσ : σ = τ := eq_of_compS_empty_left hc
  rw [hσ]
  exact ewp_val (opTableC_mono _ _) hB

/-- `λx. x` answers at once. -/
theorem id_spec {ls : List SRec} {v : Val} {ρ : WRes} (h : unitEnt.PA ls v ρ) :
    ewpTS ls (.app (.val idV) (.val v)) (opTableC (tabOf []) Grade.all) unitEnt.PB ρ :=
  ewp_id (opTableC_mono _ _) h

/-- **One tail handler**, at any level: the name `n` call-like in `Tin`, the outer rows `Tout`,
the answering function `g` at a class-1 row `TN` below `Tout`. -/
theorem handle_level {Tin Tout TN : OpTab} (n : UInt32) (hn0 : n ≠ 0)
    (hTin : ∀ m i, m ≠ n → Tin m i = Tout m i)
    (hn : ∀ i en, Tin n i = some en → i = 0 ∧ en = unitEnt)
    (hN : CallRow TN Grade.all) (hle : TN.Le Tout) (g : Val)
    (hg : ∀ ls v ρ, unitEnt.PA ls v ρ → ewpTS ls (.app (.val g) (.val v)) (opTableC TN Grade.all)
      unitEnt.PB ρ)
    {Q : List SRec → Val → WProp} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : ewpTS ls e (opTableC Tin Grade.all) Q ρ) :
    ewpTS ls (hndE (hH n g) e) (opTableC Tout Grade.all) Q ρ := by
  refine ewp_handleC Tin Tout Grade.all Grade.all n hn0 hTin (fun _ _ _ => rfl)
    (fun i en hT => by obtain ⟨rfl, rfl⟩ := hn i en hT; exact ⟨rfl, rfl, rfl⟩)
    (qualsVal [.lin]) idV _ Q Q (fun i en hT => ?_)
    (fun ls v ρ hv => ewp_id (opTableC_mono _ _) hv) (fun i en hT => ?_) h
  · obtain ⟨rfl, rfl⟩ := hn i en hT
    exact capTag_qualsVal [.lin] 0 (by simp)
  · obtain ⟨rfl, rfl⟩ := hn i en hT
    refine ⟨clV g, clauseAt_hH g, fun ls v κ ρ hκ => ?_⟩
    exact tail_hop hN hle (fun n i en _ => rfl) (fun v κ => clV_steps g v κ)
      (fun ls v ρ h => hg ls v ρ h) hκ

theorem tabOf_eq_off {ns ms : List UInt32} {n : UInt32} (h : ∀ m, m ≠ n → (m ∈ ns ↔ m ∈ ms)) :
    ∀ m i, m ≠ n → tabOf ns m i = tabOf ms m i := by
  intro m i hm
  simp only [tabOf, h m hm]

theorem tabOf_n {ns : List UInt32} {n : UInt32} :
    ∀ i en, tabOf ns n i = some en → i = 0 ∧ en = unitEnt :=
  fun _ _ h => let ⟨_, h₁, h₂⟩ := tabOf_some h; ⟨h₁, h₂⟩

/-- A table with no operation stops nowhere: `ewpTS` there is `wpTS`. -/
theorem ewp_empty_wp {C : Grade} {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp}
    {ρ : WRes} (h : ewpTS ls e (opTableC (tabOf []) C) Q ρ) : wpTS ls e Q ρ := by
  refine ewp_bot.mp (ewp_mono (fun _ _ _ _ _ _ h => h) (fun ls t Φ ρ h => ?_) (fun _ _ _ h => h) h)
  rcases h with ⟨K, n, i, v, en, hp⟩ | ⟨K, n, i, v, en, hp⟩
  · obtain ⟨⟨-, -, hT, -⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd (tabOf_some hT).1 (by simp)
  · obtain ⟨⟨-, -, hT, -⟩, -⟩ := pure_sep_iff.mp hp
    exact absurd (tabOf_some hT).1 (by simp)

/-- **Class 1 at depth three, every hypothesis discharged.** Three nested lends of three owned
cells, open across a call-like operation, under three nested tail handlers whose clauses perform
the next name's operation. From the three owners the whole is a pure computation of
`Ref 1 ⊗ (Ref 1 ⊗ (Ref 1 ⊗ 1))`, each cell handed back. -/
theorem prog3_sem (l1 l2 l3 : BoCa.Loc) {δ : LSub} {ls : List SRec} :
    Entails (ptoOwn l1 Val.unit ⋆ ptoOwn l2 Val.unit ⋆ ptoOwn l3 Val.unit)
      (wpTS ls (prog3 l1 l2 l3) (fun ls r => vC true R3 ls δ r)) := by
  intro ρ hρ
  have h1 := prog3_lends l1 l2 l3 (δ := δ) (ls := ls) ρ hρ
  have h2 := handle_level (Tin := tabOf [1, 2, 3]) (Tout := tabOf [2, 3]) (TN := tabOf [2]) 1
    (by decide) (tabOf_eq_off (by intro m hm; simp [hm])) tabOf_n (callRow_tabOf [2])
    (tabOf_le (by simp)) (gpV 2) (fun _ _ _ h => gp_spec 2 h) h1
  have h3 := handle_level (Tin := tabOf [2, 3]) (Tout := tabOf [3]) (TN := tabOf [3]) 2
    (by decide) (tabOf_eq_off (by intro m hm; simp [hm])) tabOf_n (callRow_tabOf [3])
    (tabOf_le (by simp)) (gpV 3) (fun _ _ _ h => gp_spec 3 h) h2
  have h4 := handle_level (Tin := tabOf [3]) (Tout := tabOf []) (TN := tabOf []) 3
    (by decide) (tabOf_eq_off (by intro m hm; simp [hm])) tabOf_n (callRow_tabOf [])
    (tabOf_le (by simp)) idV (fun _ _ _ h => id_spec h) h3
  exact ewp_empty_wp h4

end SuspSpike

end
