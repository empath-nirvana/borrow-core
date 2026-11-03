import PoolSpike.Seg

/-!
# Pool spike: preservation through the invariant's operations, and adequacy

The invariant over a configuration (`Inv`): at a boundary (no branch active) the pool's branches
meet `CInv`, `PoolEsc` and their certificates (`EntOK`); with a branch active, they did at the
segment's start, and the active branch has run some steps since.

* A **ready** branch is a closed program verified at every world and list, owning nothing.
* A **parked** branch's certificate is the share its stop left (`contShareP`) at the stop's world
  and list, with the branch's present resource and records its re-readings, and the records of
  the stop's list it is relevant to present in the present list (`KeepRel`). Nothing about the
  stop list is taken from outside: the stop sets it (`park_inv`), every segment of another branch
  keeps it (`entOK_seg`, from `seg`).
* The **active** branch is verified at its index (`ActOK`).

Each operation keeps it: a segment (`after_seg`), park (`park_inv`), finishing (`done_inv`),
resume (`resume_inv`), start (`start_inv`). Adequacy (`poolAdequacy`) reads it at every
configuration a run reaches.

The table's entries (`TabOK`) answer `()` at the empty resource, take an empty payload resource,
and guarantee nothing of the frame (`fd` trivial); `Q` ends at the empty resource owning no
record (`QOK`). These are scope restrictions on the theorem, not facts about runs.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.Pool
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Kont performE freeE opPayload)

/-- **The scope of the table**: one operation `(m₀, i₀)`, an empty payload resource, the answer
`()` at the empty resource, and no guarantee asked of the frame. -/
def TabOK (T : OpTabT) (m₀ i₀ : UInt32) : Prop :=
  ∀ m i en, T m i = some en → m = m₀ ∧ i = i₀ ∧
    (∀ k w ls v ρ, en.PA k w ls v ρ → ρ = PMap.empty) ∧
    (∀ v k w ls, en.PBv v k w ls Val.unit PMap.empty) ∧ (∀ v w O ρf, en.fd v w O ρf)

/-- A finished branch holds nothing and owns no record. -/
def QOK (Q : TPostV) : Prop := ∀ k w ls O v ρ, Q k w ls O v ρ → ρ = PMap.empty ∧ O = []

/-- A frame condition every frame meets. -/
def AllF (F : TFrame) : Prop := ∀ w ρ, F w ρ

section
variable (T : OpTabT) (Q : TPostV) (m₀ i₀ : UInt32)

/-- The active branch, verified at its index. -/
def ActOK (N t : Nat) (w : TWd) (ls : List (SRecT w.K)) (e : Expr) (b : TBranch w.K) : Prop :=
  ∃ F k, AllF F ∧ N < k + t ∧ cerwpT (ℍ := ℍ) (opTableP T) Q F k w ls b.2 e b.1

/-- **A branch of the pool and its certificate.** -/
def EntOK (N t : Nat) (w : TWd) (ls : List (SRecT w.K)) : PEnt → TBranch w.K → Prop
  | .ready e, b => b = (PMap.empty, []) ∧
      ∀ (w' : TWd) (ls' : List (SRecT w'.K)) n,
        cerwpT (ℍ := ℍ) (opTableP T) Q (fun _ _ => True) n w' ls' [] e PMap.empty
  | .parked K v, b => ∃ (wp : TWd) (lsp : List (SRecT wp.K)) (Op : List (FrameRecT wp.K))
      (ρp : TRes wp.K) (en : OpEntT) (F : TFrame) (k kΨ : Nat),
      T m₀ i₀ = some en ∧ AllF F ∧ N < k + t ∧ k ≤ kΨ ∧
      contShareP en F k wp lsp Op K v (cerwpTC (ℍ := ℍ) (opTableP T) Q kΨ) ρp ∧
      wp.Ext w ρp ∧ RRw (w := wp) (w' := w) ρp b.1 ∧ RecsRR w.Θ Op b.2 ∧
      KeepRel w.Θ lsp ls ρp

/-- The pool, no branch active. -/
def BIdle (N t : Nat) (μ : Heap) (pool : List PEnt) : Prop :=
  ∃ (w : TWd) (bs : List (TBranch w.K)) (W : TRes w.K) (ps : List (FrameRecT w.K))
    (ls : List (SRecT w.K)), CInv w bs W ps ls μ ∧ FinDom μ ∧ PoolEsc bs ∧
    List.Forall₂ (EntOK (ℍ := ℍ) T Q m₀ i₀ N t w ls) pool bs

/-- The pool, the branch `e` active at the start of its segment. -/
def BAct (N t : Nat) (μ : Heap) (e : Expr) (pool : List PEnt) : Prop :=
  ∃ (w : TWd) (b : TBranch w.K) (rest : List (TBranch w.K)) (W : TRes w.K)
    (ps : List (FrameRecT w.K)) (ls : List (SRecT w.K)), CInv w (b :: rest) W ps ls μ ∧
    FinDom μ ∧ PoolEsc (b :: rest) ∧ ActOK (ℍ := ℍ) T Q N t w ls e b ∧
    List.Forall₂ (EntOK (ℍ := ℍ) T Q m₀ i₀ N t w ls) pool rest

/-- **The invariant over a configuration**, for runs of at most `N` steps, after `t`. -/
def Inv (N t : Nat) (c : PCfg) : Prop :=
  match c.act with
  | none => BIdle (ℍ := ℍ) T Q m₀ i₀ N t c.μ c.pool
  | some e => ∃ (μ₀ : Heap) (e₀ : Expr) (j : Nat), j ≤ t ∧ StepsN (ℍ := ℍ) j μ₀ e₀ c.μ e ∧
      BAct (ℍ := ℍ) T Q m₀ i₀ N (t - j) μ₀ e₀ c.pool

end

variable {T : OpTabT} {Q : TPostV} {m₀ i₀ : UInt32}

/-! ### Certificates along time and along a segment -/

theorem entOK_mono {N t t' : Nat} (htt : t ≤ t') {w : TWd} {ls : List (SRecT w.K)} :
    ∀ {x : PEnt} {b : TBranch w.K}, EntOK (ℍ := ℍ) T Q m₀ i₀ N t w ls x b →
      EntOK (ℍ := ℍ) T Q m₀ i₀ N t' w ls x b
  | .ready _, _, h => h
  | .parked _ _, _, ⟨wp, lsp, Op, ρp, en, F, k, kΨ, h₀, h₁, h₂, h₃⟩ =>
      ⟨wp, lsp, Op, ρp, en, F, k, kΨ, h₀, h₁, by omega, h₃⟩

/-- **A parked branch's certificate is carried by another branch's segment.** -/
theorem entOK_seg {N t : Nat} {w w' : TWd} (hK : w.K.Ext w'.K) {ls : List (SRecT w.K)}
    {ls' : List (SRecT w'.K)} :
    ∀ {x : PEnt} {a : TBranch w.K} {b : TBranch w'.K}, EntOK (ℍ := ℍ) T Q m₀ i₀ N t w ls x a →
      SegRel ls ls' a b → EntOK (ℍ := ℍ) T Q m₀ i₀ N t w' ls' x b
  | .ready _, _, b, ⟨rfl, hc⟩, ⟨_, hr, hO, _⟩ => by
      refine ⟨?_, hc⟩
      obtain ⟨b₁, b₂⟩ := b
      cases hO
      obtain rfl : b₁ = PMap.empty := RR.of_empty hr
      rfl
  | .parked _ _, a, b, ⟨wp, lsp, Op, ρp, en, F, k, kΨ, h₀, h₁, h₂, h₃, h₄, hE, hr, hO, hk⟩,
      ⟨hE', hr', hO', hk'⟩ => by
      refine ⟨wp, lsp, Op, ρp, en, F, k, kΨ, h₀, h₁, h₂, h₃, h₄, hE.trans hr hE',
        RRw.trans hK hr hr', RecsRR.trans hK hO hO', fun r hr₀ hrel => ?_⟩
      obtain ⟨r₁, hr₁, hrr₁⟩ := hk r hr₀ hrel
      obtain ⟨r₂, hr₂, hrr₂⟩ := hk' r₁ hr₁ ((RelFT.rr_iff hrr₁ hr).mp hrel)
      exact ⟨r₂, hr₂, RecRR.trans hK hrr₁ hrr₂⟩

/-- **The end of a segment**: the invariant at the end world, the active branch at its
postcondition, the pool's certificates carried. -/
theorem after_seg {N t : Nat} {μ₀ μ : Heap} {e₀ e : Expr} {pool : List PEnt} {j : Nat}
    (hB : BAct (ℍ := ℍ) T Q m₀ i₀ N t μ₀ e₀ pool) (hjN : t + j ≤ N)
    (hrun : StepsN (ℍ := ℍ) j μ₀ e₀ μ e) (hfin : Final (ℍ := ℍ) μ e) :
    ∃ (w' : TWd) (ρ' W' : TRes w'.K) (O' ps' : List (FrameRecT w'.K))
      (ls' : List (SRecT w'.K)) (rest' : List (TBranch w'.K)) (F : TFrame) (k kΨ : Nat),
      CInv w' ((ρ', O') :: rest') W' ps' ls' μ ∧ FinDom μ ∧ PoolEsc ((ρ', O') :: rest') ∧
      List.Forall₂ (EntOK (ℍ := ℍ) T Q m₀ i₀ N (t + j) w' ls') pool rest' ∧ AllF F ∧
      N < k + (t + j) ∧ k ≤ kΨ ∧
      cerwpPostT (opTableP T) Q (cerwpTC (ℍ := ℍ) (opTableP T) Q kΨ) F k w' ls' O' e ρ' := by
  obtain ⟨w, ⟨ρ, O⟩, rest, W, ps, ls, hI, hfd, hP, ⟨F, k, hF, hk, h⟩, hpool⟩ := hB
  rw [cerwpT_eq] at h
  have hjk : j < k := by omega
  obtain ⟨w', ρ', W', O', ps', ls', rest', hK, hrel, hI', hP', hQ'⟩ :=
    seg h hI hP (fun ρf => hF w ρf) hfd hjk hrun hfin
  refine ⟨w', ρ', W', O', ps', ls', rest', F, k - j, k, hI', fd_stepsN hrun hfd, hP',
    forall₂_trans (R := EntOK (ℍ := ℍ) T Q m₀ i₀ N t w ls) (S := SegRel ls ls')
      (T := EntOK (ℍ := ℍ) T Q m₀ i₀ N (t + j) w' ls')
      (fun x a b hx hab => entOK_mono (t := t) (by omega) (entOK_seg hK hx hab)) hpool hrel,
    hF, by omega, by omega, hQ'⟩

/-! ### Park, finish, resume, start -/

theorem opPayload_inj {n i n' i' : UInt32} {v v' : Val}
    (h : opPayload n i v = opPayload n' i' v') : v = v' := by
  have := congrArg Subtype.val h
  simp only [opPayload, Val.pair, Expr.pair.injEq] at this
  exact Subtype.ext this.2.2

theorem perform_eq (p : Val) : performE (.val p) = .app (.prim .perform) p.1 := rfl

theorem stop_shape (hTab : TabOK T m₀ i₀) {F : TFrame} {k : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {Ψ : ContT} {ρ : TRes w.K} {e : Expr}
    (h : opTableP T F k w ls O e Ψ ρ) :
    ∃ (K : Kont) (v : Val), e = K.plug (performE (.val (opPayload m₀ i₀ v))) ∧
      K.HasHnd m₀ = false := by
  obtain ⟨K, n, i, v, en, rfl, hK, hTn, -⟩ := h
  obtain ⟨rfl, rfl, -⟩ := hTab n i en hTn
  exact ⟨K, v, rfl, hK⟩

/-- **Park**: the stopped branch is the share its stop left, at the stop's own world, list and
records. -/
theorem park_inv (hTab : TabOK T m₀ i₀) {N t : Nat} {μ : Heap} {e : Expr} {pool : List PEnt}
    {w' : TWd} {ρ' W' : TRes w'.K} {O' ps' : List (FrameRecT w'.K)}
    {ls' : List (SRecT w'.K)} {rest' : List (TBranch w'.K)} {F : TFrame} {k kΨ : Nat}
    (hI : CInv w' ((ρ', O') :: rest') W' ps' ls' μ) (hfd : FinDom μ)
    (hP : PoolEsc ((ρ', O') :: rest'))
    (hpool : List.Forall₂ (EntOK (ℍ := ℍ) T Q m₀ i₀ N t w' ls') pool rest') (hF : AllF F)
    (hk : N < k + t) (hkΨ : k ≤ kΨ)
    (hst : opTableP T F k w' ls' O' e (cerwpTC (ℍ := ℍ) (opTableP T) Q kΨ) ρ')
    {K₁ : Kont} {v₁ : Val} (he : e = K₁.plug (performE (.val (opPayload m₀ i₀ v₁)))) :
    BIdle (ℍ := ℍ) T Q m₀ i₀ N (t + 1) μ (.parked K₁ v₁ :: pool) := by
  obtain ⟨K, n, i, v, en, rfl, -, hTn, -, -, ρa, ρk, hc, hA, hsh⟩ := hst
  have he' : K.plug (.app (.prim .perform) (opPayload n i v).1) =
      K₁.plug (.app (.prim .perform) (opPayload m₀ i₀ v₁).1) := he
  obtain ⟨rfl, -, hv⟩ := plug_prim_inj (a := .perform) (b := .perform) (by decide) (by decide) he'
  obtain rfl := opPayload_inj hv
  obtain ⟨rfl, rfl, hPA, -⟩ := hTab n i en hTn
  obtain rfl := hPA _ _ _ _ _ hA
  obtain rfl : ρk = ρ' := ResUT.CompS.functional (ResUT.compS_empty_right ρk) (ResUT.CompS.comm hc)
  obtain ⟨hC, hps, hA, hR, hW⟩ := hI
  have hcov : CovR (sem w'.Θ) w'.K ρk := by
    simp only [List.map_cons] at hC
    cases hC with
    | cons _ hc' => exact cov_of_comp (ResUT.CompS.comm hc') hW
  refine ⟨w', (ρk, O') :: rest', W', ps', ls', ⟨hC, hps, hA, hR, hW⟩, hfd, hP,
    .cons ⟨w', ls', O', ρk, en, F, k, kΨ, hTn, hF, by omega, hkΨ, hsh, TWd.Ext.refl _ _,
      RR.refl hcov, RecsRR.refl fun r hr => hR.cov_ps r ((hps r).mpr (by simp [hr])),
      fun r hr _ => ⟨r, hr, RecRR.refl (by
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
        exact hR.cov_ls x hx)⟩⟩
      (hpool.imp fun _ _ h => entOK_mono (by omega) h)⟩

/-- **Finish**: a branch at a value holds nothing, owns nothing, and leaves the pool. -/
theorem done_inv (hQ : QOK Q) {N t : Nat} {μ : Heap} {e : Expr} {pool : List PEnt}
    {w' : TWd} {ρ' W' : TRes w'.K} {O' ps' : List (FrameRecT w'.K)}
    {ls' : List (SRecT w'.K)} {rest' : List (TBranch w'.K)}
    (hI : CInv w' ((ρ', O') :: rest') W' ps' ls' μ) (hfd : FinDom μ)
    (hP : PoolEsc ((ρ', O') :: rest'))
    (hpool : List.Forall₂ (EntOK (ℍ := ℍ) T Q m₀ i₀ N t w' ls') pool rest') {k : Nat}
    (hv : ∃ v : Val, e = v.1 ∧ Q k w' ls' O' v ρ') :
    BIdle (ℍ := ℍ) T Q m₀ i₀ N (t + 1) μ pool := by
  obtain ⟨v, -, hq⟩ := hv
  obtain ⟨rfl, rfl⟩ := hQ _ _ _ _ _ _ hq
  exact ⟨w', rest', W', ps', ls', hI.drop, hfd, (List.pairwise_cons.mp hP).2,
    hpool.imp fun _ _ h => entOK_mono (by omega) h⟩

theorem poolEsc_perm {K : WCactus} {bs bs' : List (TBranch K)} (hp : bs.Perm bs')
    (h : PoolEsc bs) : PoolEsc bs' :=
  (hp.pairwise_iff fun {_ _} h => escApart_symm h).mp h

/-- **Resume**: a parked branch, after any number of other branches' segments since its park,
is resumed at `()` from its certificate alone. -/
theorem resume_inv (hTab : TabOK T m₀ i₀) {N t : Nat} (htN : t < N) {μ : Heap} {K : Kont}
    {v : Val} {p₁ p₂ : List PEnt}
    (hB : BIdle (ℍ := ℍ) T Q m₀ i₀ N t μ (p₁ ++ .parked K v :: p₂)) :
    BAct (ℍ := ℍ) T Q m₀ i₀ N (t + 1) μ (K.plug (.val .unit)) (p₁ ++ p₂) := by
  obtain ⟨w, bs, W, ps, ls, hI, hfd, hP, hpool⟩ := hB
  obtain ⟨bs₁, b, bs₂, rfl, h₁, ⟨wp, lsp, Op, ρp, en, F, k, kΨ, hTn, hF, hk, hkΨ, hsh, hE, hr,
    hO, hkeep⟩, h₂⟩ := forall₂_split_right hpool
  have hperm : (bs₁ ++ b :: bs₂).Perm (b :: (bs₁ ++ bs₂)) := List.perm_middle
  obtain ⟨-, -, -, hPB, hfdB⟩ := hTab m₀ i₀ en hTn
  have hk1 : k - 1 < k := by omega
  have hres := (hsh.2 w b.1 ls b.2 hE hr hkeep hO).1 (k - 1) hk1 Val.unit PMap.empty b.1
    (hPB v (k - 1) w ls) (ResUT.compS_empty_right _)
  simp only [cerwpTC, show k - 1 < kΨ by omega, if_true] at hres
  refine ⟨w, b, bs₁ ++ bs₂, W, ps, ls, hI.perm hperm, hfd, poolEsc_perm hperm hP,
    ⟨fdAt en v F b.2, k - 1, fun w' ρf => ⟨hF w' ρf, fun O'' _ => hfdB v w' O'' ρf⟩, by omega,
      hres⟩, (forall₂_append h₁ h₂).imp fun _ _ h => entOK_mono (by omega) h⟩

/-- **Start**: a ready branch becomes active. -/
theorem start_inv {N t : Nat} {μ : Heap} {e : Expr} {p₁ p₂ : List PEnt}
    (hB : BIdle (ℍ := ℍ) T Q m₀ i₀ N t μ (p₁ ++ .ready e :: p₂)) :
    BAct (ℍ := ℍ) T Q m₀ i₀ N (t + 1) μ e (p₁ ++ p₂) := by
  obtain ⟨w, bs, W, ps, ls, hI, hfd, hP, hpool⟩ := hB
  obtain ⟨bs₁, b, bs₂, rfl, h₁, ⟨rfl, hc⟩, h₂⟩ := forall₂_split_right hpool
  have hperm : (bs₁ ++ (PMap.empty, []) :: bs₂).Perm ((PMap.empty, []) :: (bs₁ ++ bs₂)) :=
    List.perm_middle
  exact ⟨w, (PMap.empty, []), bs₁ ++ bs₂, W, ps, ls, hI.perm hperm, hfd, poolEsc_perm hperm hP,
    ⟨fun _ _ => True, N + 1, fun _ _ => trivial, by omega, hc w ls (N + 1)⟩,
    (forall₂_append h₁ h₂).imp fun _ _ h => entOK_mono (by omega) h⟩

/-! ### Every step keeps the invariant -/

theorem stepsN_snoc {j : Nat} {μ₀ μ μ' : Heap} {e₀ e e' : Expr}
    (h : StepsN (ℍ := ℍ) j μ₀ e₀ μ e) (hs : Step1 (ℍ := ℍ) μ e μ' e') :
    StepsN (ℍ := ℍ) (j + 1) μ₀ e₀ μ' e' := by
  induction h with
  | refl => exact .more hs (.refl _ _)
  | more h₁ _ ih => exact .more h₁ (ih hs)

theorem final_of_park {μ : Heap} {K : Kont} {v : Val} (hK : K.HasHnd m₀ = false) :
    Final (ℍ := ℍ) μ (K.plug (performE (.val (opPayload m₀ i₀ v)))) :=
  final_opPlug (r := false) (payloadName_opPayload m₀ i₀ v) hK μ

/-- **Every step of the machine keeps the invariant.** -/
theorem inv_step (hTab : TabOK T m₀ i₀) (hQ : QOK Q) {N t : Nat} (htN : t < N) {c c' : PCfg}
    (hI : Inv (ℍ := ℍ) T Q m₀ i₀ N t c) (hs : PStep (ℍ := ℍ) m₀ i₀ c c') :
    Inv (ℍ := ℍ) T Q m₀ i₀ N (t + 1) c' := by
  cases hs with
  | run h =>
      obtain ⟨μ₀, e₀, j, hj, hrun, hB⟩ := hI
      exact ⟨μ₀, e₀, j + 1, by omega, stepsN_snoc hrun h, by rwa [show t + 1 - (j + 1) = t - j by omega]⟩
  | @park μ K v pool hK =>
      obtain ⟨μ₀, e₀, j, hj, hrun, hB⟩ := hI
      obtain ⟨w', ρ', W', O', ps', ls', rest', F, k, kΨ, hI', hfd, hP, hpool, hF, hk, hkΨ, hq⟩ :=
        after_seg hB (by omega) hrun (final_of_park hK)
      rw [show t - j + j = t by omega] at hpool hk
      rcases hq with ⟨v', hv', -⟩ | hst
      · exact absurd (hv' ▸ v'.2) (by rw [perform_eq]; exact plug_prim_not_val (by decide) K)
      · exact park_inv hTab hI' hfd hP hpool hF hk hkΨ hst rfl
  | @done μ v pool =>
      obtain ⟨μ₀, e₀, j, hj, hrun, hB⟩ := hI
      obtain ⟨w', ρ', W', O', ps', ls', rest', F, k, kΨ, hI', hfd, hP, hpool, hF, hk, hkΨ, hq⟩ :=
        after_seg hB (by omega) hrun (final_val μ v)
      rw [show t - j + j = t by omega] at hpool
      rcases hq with hv | hst
      · exact done_inv hQ hI' hfd hP hpool hv
      · obtain ⟨K, v', he, -⟩ := stop_shape hTab hst
        exact absurd (he ▸ v.2) (by rw [perform_eq]; exact plug_prim_not_val (by decide) K)
  | resume => exact ⟨_, _, 0, by omega, .refl _ _, resume_inv hTab htN hI⟩
  | start => exact ⟨_, _, 0, by omega, .refl _ _, start_inv hI⟩

/-! ### Adequacy -/

/-- The initial pool: closed programs, each verified at every world and list, owning nothing. -/
def initCfg (progs : List Expr) : PCfg := ⟨Adequacy.emptyMem, none, progs.map .ready⟩

theorem compAllT_empties {K : WCactus} :
    ∀ (n : Nat), CompAllT (List.replicate n (PMap.empty : TRes K)) PMap.empty
  | 0 => .nil
  | n + 1 => .cons (compAllT_empties n) (ResUT.compS_empty_right _)

theorem inv_init (P : ParentFn) {progs : List Expr}
    (hall : ∀ e ∈ progs, ∀ (w : TWd) (ls : List (SRecT w.K)) n,
      cerwpT (ℍ := ℍ) (opTableP T) Q (fun _ _ => True) n w ls [] e PMap.empty) (N : Nat) :
    Inv (ℍ := ℍ) T Q m₀ i₀ N 0 (initCfg progs) := by
  let w : TWd := ⟨P, fun _ => none, tmplT _ (fun _ => none)⟩
  let bs : List (TBranch w.K) := progs.map fun _ => (PMap.empty, [])
  refine ⟨w, bs, PMap.empty, [], [], ⟨?_, fun p => ?_, ?_, recInv_empty P, winv_empty P⟩,
    finDom_empty, ?_, ?_⟩
  · have : bs.map Prod.fst = List.replicate progs.length PMap.empty := by
      simp [bs, List.map_const']
    rw [this]; exact compAllT_empties _
  · simp [bs]
  · simp only [bs, List.map_map]
    exact List.pairwise_map.mpr (List.Pairwise.imp (R := fun _ _ => True)
      (fun _ p hp => by simp at hp) (List.pairwise_of_forall fun _ _ => trivial))
  · simp only [bs]
    exact List.pairwise_map.mpr (List.Pairwise.imp (R := fun _ _ => True)
      (fun _ => ⟨fun p hp => by simp at hp, fun p hp => by simp at hp⟩)
      (List.pairwise_of_forall fun _ _ => trivial))
  · simp only [initCfg, bs]
    induction progs with
    | nil => exact .nil
    | cons e progs ih =>
        exact .cons ⟨rfl, hall e List.mem_cons_self⟩
          (ih fun e' he' => hall e' (List.mem_cons_of_mem _ he'))

theorem inv_run (hTab : TabOK T m₀ i₀) (hQ : QOK Q) (P : ParentFn) {progs : List Expr}
    (hall : ∀ e ∈ progs, ∀ (w : TWd) (ls : List (SRecT w.K)) n,
      cerwpT (ℍ := ℍ) (opTableP T) Q (fun _ _ => True) n w ls [] e PMap.empty)
    {t : Nat} {c : PCfg} (h : PRun (ℍ := ℍ) m₀ i₀ t (initCfg progs) c) :
    ∀ N, t ≤ N → Inv (ℍ := ℍ) T Q m₀ i₀ N t c := by
  generalize hc₀ : initCfg progs = c₀ at h
  induction h with
  | refl => subst hc₀; exact fun N _ => inv_init P hall N
  | step _ hs ih => exact fun N hN => inv_step hTab hQ (by omega) (ih hc₀ N (by omega)) hs

/-- **Adequacy of the pool machine.** Closed programs verified at `cerwpT (opTableP T)` at every
world and list, run together under any schedule: every configuration a run reaches steps, or is
final (no branch active, none in the pool) at the empty memory; and every `free` the active
branch reaches finds its cell. -/
def PoolAdequacy (T : OpTabT) (Q : TPostV) (m₀ i₀ : UInt32) : Prop :=
  ∀ (progs : List Expr),
    (∀ e ∈ progs, ∀ (w : TWd) (ls : List (SRecT w.K)) n,
      cerwpT (ℍ := ℍ) (opTableP T) Q (fun _ _ => True) n w ls [] e PMap.empty) →
    ∀ {t : Nat} {c : PCfg}, PRun (ℍ := ℍ) m₀ i₀ t (initCfg progs) c →
      ((∃ c', PStep (ℍ := ℍ) m₀ i₀ c c') ∨
        (c.act = none ∧ c.pool = [] ∧ c.μ = Adequacy.emptyMem)) ∧
      ∀ (K : Kont) (ℓ : Loc), c.act = some (K.plug (freeE (.val (Val.loc ℓ)))) →
        ∃ u, c.μ ℓ = some u

theorem free_eq (ℓ : Loc) : freeE (.val (Val.loc ℓ)) = .app (.prim .free) (Val.loc ℓ).1 := rfl

theorem poolAdequacy (hTab : TabOK T m₀ i₀) (hQ : QOK Q) :
    PoolAdequacy (ℍ := ℍ) T Q m₀ i₀ := by
  intro progs hall t c hrun
  have hI := inv_run hTab hQ beforeP hall hrun t le_rfl
  obtain ⟨μ, act, pool⟩ := c
  cases act with
  | none =>
      refine ⟨?_, fun K ℓ h => by cases h⟩
      cases pool with
      | nil =>
          refine .inr ⟨rfl, rfl, ?_⟩
          obtain ⟨w, bs, W, ps, ls, ⟨hC, -, -, -, hW⟩, -, -, hpool⟩ := hI
          cases hpool
          cases hC
          exact ResUT.Lower.functional hW.2 lower_emptyT
      | cons x pool =>
          cases x with
          | ready e => exact .inl ⟨_, PStep.start (p₁ := [])⟩
          | parked K v => exact .inl ⟨_, PStep.resume (p₁ := [])⟩
  | some e =>
      obtain ⟨μ₀, e₀, j, hj, hrun', hB⟩ := hI
      -- a final active branch is a value or a stop at the pool's operation
      have hend : Final (ℍ := ℍ) μ e → (∃ v : Val, e = v.1) ∨
          ∃ (K : Kont) (v : Val), e = K.plug (performE (.val (opPayload m₀ i₀ v))) ∧
            K.HasHnd m₀ = false := by
        intro hfin
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hq⟩ :=
          after_seg hB (by omega) hrun' hfin
        rcases hq with ⟨v, hv, -⟩ | hst
        · exact .inl ⟨v, hv⟩
        · exact .inr (stop_shape hTab hst)
      by_cases hst : ∃ μ' e', Step1 (ℍ := ℍ) μ e μ' e'
      · obtain ⟨μ', e', h⟩ := hst
        refine ⟨.inl ⟨_, PStep.run h⟩, fun K ℓ he => ?_⟩
        cases he
        obtain ⟨u, hu, -, -⟩ := (step1_free_iff K ℓ).1 h
        exact ⟨u, hu⟩
      · have hfin : Final (ℍ := ℍ) μ e := fun μ' e' h => hst ⟨μ', e', h⟩
        refine ⟨?_, fun K ℓ he => ?_⟩
        · rcases hend hfin with ⟨v, rfl⟩ | ⟨K, v, rfl, hK⟩
          · exact .inl ⟨_, PStep.done⟩
          · exact .inl ⟨_, PStep.park hK⟩
        · cases he
          exfalso
          rcases hend hfin with ⟨v, hv⟩ | ⟨K', v, hv, -⟩
          · exact plug_prim_not_val (a := .free) (by decide) K (by rw [← free_eq, hv]; exact v.2)
          · rw [free_eq, perform_eq] at hv
            exact absurd (plug_prim_inj (by decide) (by decide) hv).2.1 (by decide)

end BoCa.Fig16.Tree.Wp.Pool

end
