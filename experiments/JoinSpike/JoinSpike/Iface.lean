import JoinSpike.Compat
import Core.TreePoolSched

/-!
# Join spike: a scheduler interface whose invariant covers the running task and the pool

`PoolAns` (`Core/TreePoolSched.lean`) asks every two tasks to hold nothing at each other's record
masks, and says nothing about where the running task's borrowed cells sit. Here:

* **The pool is a stack** (`PoolTJ`). Every entry is held apart from the entries *below* it at
  their masks, except at the lent locations the nearest joiner below shares (`shTop`): a task
  above a joiner may hold views of what the joiner shares. Entries below hold nothing at the masks
  of entries above. Each entry's share holds its `imm` cells at its own masks or at what is shared
  with it (`HoldsIn`).
* **The running task** is above the whole pool and meets the same conditions (`PoolAnsJAt`'s
  premises): it holds nothing at the masks of unshared pool records, its `imm` cells are at its own
  masks or shared locations, and the pool holds nothing at its masks.
* **A joiner** (`join = true`) shares `sh`: lent locations of its own or already shared with it.
  It is resumed with an answer `σ` that holds what is shared with it (its children's views), the
  stack above it being empty.

Every condition is per record and is kept by a run (`twp_keepsPoolJ`, from `twp_frame_keep_sh`
and `twp_holdsIn`). The moves are park (`poolAnsJ_park`), resume (`poolAnsJ_resume`), run
(`poolAnsJ_run_le`), and the headline (`poolSchedAdequacyJ`) has `PoolSchedAdequacyT`'s statement
with `PoolAnsJ` for `PoolAns`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.Join
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont hndE hndVal)

/-- **A pool entry**: a stored task, whether it waits for the tasks above it (`join`), the lent
locations it shares with them (`sh`), and the tag the scheduler's code stores beside it. -/
structure StoredJ where
  t : StoredT
  join : Bool
  sh : BoCa.Loc → Prop
  tag : Val

/-- What the nearest joiner shares. -/
def shTop : List StoredJ → BoCa.Loc → Prop
  | [] => fun _ => False
  | s :: ss => fun x => (s.join = true ∧ s.sh x) ∨ (s.join = false ∧ shTop ss x)

/-- **Nothing at the masks of the records not lent at `A`.** -/
def AvoidUnsh {K : WCactus} (A : BoCa.Loc → Prop) (Os : List (FrameRecT K)) (ρ : TRes K) : Prop :=
  ∀ q ∈ Os, ¬ A q.le → NoneAt (recMask [q]) ρ

def poolValJ : List StoredJ → Val
  | [] => Val.inj₂ Val.unit
  | s :: ss => Val.inj₁ (Val.pair (Val.pair s.tag s.t.κ) (poolValJ ss))

def stateValJ (H : Val) (ss : List StoredJ) : Val := Val.pair H (poolValJ ss)

/-- Records apart by location, and each list's lent locations outside the other's masks. -/
def RecsApart {K : WCactus} (O₁ O₂ : List (FrameRecT K)) : Prop :=
  (∀ p ∈ O₁, ∀ q ∈ O₂, p.le ≠ q.le) ∧ (∀ q ∈ O₂, ¬ recMask O₁ q.le) ∧ ∀ p ∈ O₁, ¬ recMask O₂ p.le

/-- **The pool as a stack.** -/
def PoolTJ : List StoredJ → (w : TWd) → List (SRecT w.K) → List (FrameRecT w.K) → TRes w.K → Prop
  | [], _, _, O, ρ => O = [] ∧ ρ = PMap.empty
  | s :: ss, w, ls, O, ρ => ∃ (Ot Os : List (FrameRecT w.K)) (a b : TRes w.K),
      O = Ot ++ Os ∧ ResUT.CompS a b ρ ∧
      KapAtT (ℍ := ℍ) s.t.Q s.t.M s.t.en s.t.H s.t.k s.t.v s.t.κ w ls Ot a ∧
      (∀ x, s.t.M x ↔ recMask Ot x) ∧ PoolTJ ss w ls Os b ∧ NoneAt (recMask Ot) b ∧
      AvoidUnsh (shTop ss) Os a ∧ HoldsIn (shTop ss) Ot a ∧
      (∀ x, s.sh x → recMask Ot x ∨ shTop ss x) ∧ RecsApart Ot Os

theorem poolTJ_nil {w : TWd} {ls : List (SRecT w.K)} :
    PoolTJ (ℍ := ℍ) [] w ls [] (PMap.empty : TRes w.K) := ⟨rfl, rfl⟩

/-! ### `AvoidUnsh` -/

section Avoid
variable {K K' : WCactus}

theorem AvoidUnsh.of_noneAt {A : BoCa.Loc → Prop} {Os : List (FrameRecT K)} {ρ : TRes K}
    (h : NoneAt (recMask Os) ρ) : AvoidUnsh A Os ρ :=
  fun q hq _ => h.mono fun x ⟨p, hp, hx⟩ => ⟨p, by simp at hp; exact hp ▸ hq, hx⟩

theorem AvoidUnsh.mono {A A' : BoCa.Loc → Prop} {Os : List (FrameRecT K)} {ρ : TRes K}
    (h : AvoidUnsh A Os ρ) (hA : ∀ x, A x → A' x) : AvoidUnsh A' Os ρ :=
  fun q hq hn => h q hq fun h' => hn (hA _ h')

theorem AvoidUnsh.of_append_right {A : BoCa.Loc → Prop} {O₁ O₂ : List (FrameRecT K)}
    {ρ : TRes K} (h : AvoidUnsh A (O₁ ++ O₂) ρ) : AvoidUnsh A O₂ ρ :=
  fun q hq => h q (List.mem_append_right _ hq)

theorem AvoidUnsh.of_append_left {A : BoCa.Loc → Prop} {O₁ O₂ : List (FrameRecT K)}
    {ρ : TRes K} (h : AvoidUnsh A (O₁ ++ O₂) ρ) : AvoidUnsh A O₁ ρ :=
  fun q hq => h q (List.mem_append_left _ hq)

theorem AvoidUnsh.append {A : BoCa.Loc → Prop} {O₁ O₂ : List (FrameRecT K)} {ρ : TRes K}
    (h₁ : AvoidUnsh A O₁ ρ) (h₂ : AvoidUnsh A O₂ ρ) : AvoidUnsh A (O₁ ++ O₂) ρ := by
  intro q hq
  rcases List.mem_append.mp hq with h | h
  · exact h₁ q h
  · exact h₂ q h

theorem AvoidUnsh.compS {A : BoCa.Loc → Prop} {Os : List (FrameRecT K)} {a b c : TRes K}
    (hc : ResUT.CompS a b c) (hva : ResUT.Valid a) (hvb : ResUT.Valid b) (ha : AvoidUnsh A Os a)
    (hb : AvoidUnsh A Os b) : AvoidUnsh A Os c :=
  fun q hq hn => NoneAt.compS hc hva hvb (ha q hq hn) (hb q hq hn)

theorem AvoidUnsh.of_compS_left {A : BoCa.Loc → Prop} {Os : List (FrameRecT K)} {a b c : TRes K}
    (hc : ResUT.CompS a b c) (hv : ResUT.Valid c) (h : AvoidUnsh A Os c) : AvoidUnsh A Os a :=
  fun q hq hn => (h q hq hn).of_compS_left hc hv

theorem AvoidUnsh.rr {Θ : CodeTy} (hE : K.Ext K') {A : BoCa.Loc → Prop} {Os : List (FrameRecT K)}
    {Os' : List (FrameRecT K')} (hO : RecsRR Θ Os Os') {ρ : TRes K} {ρ' : TRes K'}
    (hv : ResUT.Valid ρ) (hr : RR (sem Θ) ρ ρ') (h : AvoidUnsh A Os ρ) : AvoidUnsh A Os' ρ' := by
  intro q' hq' hn
  obtain ⟨q, hq, hqq⟩ := forall₂_mem_right hO hq'
  exact ((h q hq (by rw [← hqq.1]; exact hn)).rr hE hv hr).mono fun x hx =>
    (recMask_rr (List.Forall₂.cons hqq .nil) x).mpr hx

theorem RecsApart.rr {Θ : CodeTy} {O₁ O₂ : List (FrameRecT K)} {O₁' O₂' : List (FrameRecT K')}
    (h₁ : RecsRR Θ O₁ O₁') (h₂ : RecsRR Θ O₂ O₂') (h : RecsApart O₁ O₂) : RecsApart O₁' O₂' := by
  refine ⟨apart_rr h₁ h₂ h.1, fun q' hq' hm => ?_, fun p' hp' hm => ?_⟩
  · obtain ⟨q, hq, hqq⟩ := forall₂_mem_right h₂ hq'
    exact h.2.1 q hq ((recMask_rr h₁ _).mpr (hqq.1 ▸ hm))
  · obtain ⟨p, hp, hpp⟩ := forall₂_mem_right h₁ hp'
    exact h.2.2 p hp ((recMask_rr h₂ _).mpr (hpp.1 ▸ hm))

end Avoid

/-- **What the nearest joiner shares is lent in the pool.** -/
theorem shTop_sub : ∀ {ss : List StoredJ} {w : TWd} {ls : List (SRecT w.K)}
    {Os : List (FrameRecT w.K)} {b : TRes w.K}, PoolTJ (ℍ := ℍ) ss w ls Os b →
    ∀ x, shTop ss x → recMask Os x
  | [], _, _, _, _, _, _, hx => hx.elim
  | s :: ss, _, _, _, _, ⟨Ot, Os, a, b, hO, _, _, _, hP, _, _, _, hsh, _⟩, x, hx => by
      subst hO
      rcases hx with ⟨-, hx⟩ | ⟨-, hx⟩
      · rcases hsh x hx with h | h
        · exact (recMask_append x).mpr (Or.inl h)
        · exact (recMask_append x).mpr (Or.inr (shTop_sub hP x h))
      · exact (recMask_append x).mpr (Or.inr (shTop_sub hP x hx))

/-! ### The pool across re-reading -/

theorem PoolTJ.kripke : ∀ {ts : List StoredJ} {w w' : TWd} {ls : List (SRecT w.K)}
    {ls' : List (SRecT w'.K)} {O : List (FrameRecT w.K)} {O' : List (FrameRecT w'.K)}
    {ρ : TRes w.K} {ρ' : TRes w'.K}, PoolTJ (ℍ := ℍ) ts w ls O ρ → w.Ext w' ρ →
    RRw (w := w) (w' := w') ρ ρ' → RecsRR w'.Θ O O' → KeepRel w'.Θ ls ls' ρ →
    CovR (sem w.Θ) w.K ρ → ResUT.Valid ρ → PoolTJ (ℍ := ℍ) ts w' ls' O' ρ'
  | [], _, _, _, _, _, _, _, _, ⟨hO, hρ⟩, _, hr, hOr, _, _, _ => by
      subst hO; subst hρ; cases hOr; exact ⟨rfl, RR.of_empty hr⟩
  | t :: ts, w, w', ls, ls', O, O', ρ, ρ',
      ⟨Ot, Os, a, b, hO, hc, hκ, hM, hP, hb, ha, hH, hsh, hap⟩, hE, hr, hOr, hl, hcov, hv => by
      subst hO
      obtain ⟨Ot', Os', rfl, hOt, hOs⟩ := forall₂_append_left hOr
      obtain ⟨a', b', hra, hrb, hc'⟩ := RR.split_retype hE.1 hc hcov hE.2 hr
      have hva := (ResUT.Valid.split hc hv).1
      have hvb := (ResUT.Valid.split hc hv).2
      refine ⟨Ot', Os', a', b', rfl, hc',
        hκ.kripke (hE.of_compS_left hc) hra hOt (hl.of_compS_left hc),
        fun x => (hM x).trans (recMask_rr hOt x),
        PoolTJ.kripke hP (hE.of_compS_right hc) hrb hOs
          (hl.of_compS_left (ResUT.CompS.comm hc)) (hcov.of_compS_right hc) hvb,
        (NoneAt.rr hE.1 hvb hrb hb).mono fun x hx => (recMask_rr hOt x).mpr hx,
        ha.rr hE.1 hOs hva hra, hH.rr hE.1 (recMask_rr hOt) hva hra,
        fun x hx => (hsh x hx).imp (recMask_rr hOt x).mp id, hap.rr hOt hOs⟩

theorem PoolTJ.cov_recs : ∀ {ts : List StoredJ} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {ρ : TRes w.K}, PoolTJ (ℍ := ℍ) ts w ls O ρ →
    ∀ r ∈ O, CovR (sem w.Θ) w.K r.R
  | [], _, _, _, _, ⟨hO, _⟩ => by subst hO; intro r hr; cases hr
  | _ :: _, _, _, _, _, ⟨Ot, Os, a, b, hO, _, hκ, _, hP, _⟩ => by
      subst hO
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨w₁, ls₁, O₁, ρ₁', hK, hE₁, hr₁, hO₁, -⟩ := hκ
        obtain ⟨r₁, -, hrr⟩ := forall₂_mem_right hO₁ hr
        exact hrr.2.2.2.cov
      · exact PoolTJ.cov_recs hP r hr

/-! ### A run beside the pool -/

/-- **What a run beside the pool ends with.** -/
def PoolPostJ (P : TPost) (ts : List StoredJ) : TPost := fun k₁ w' ls' O' t ρ' =>
  ∃ (Oa Ob : List (FrameRecT w'.K)) (a b : TRes w'.K), O' = Oa ++ Ob ∧ ResUT.CompS a b ρ' ∧
    P k₁ w' ls' Oa t a ∧ PoolTJ (ℍ := ℍ) ts w' ls' Ob b ∧ NoneAt (recMask Oa) b ∧
    AvoidUnsh (shTop ts) Ob a ∧ HoldsIn (shTop ts) Oa a ∧ RecsApart Oa Ob

/-- **A run keeps the pool**: the pool holds nothing at the run's masks; the run holds nothing at
the masks of the pool's unshared records, and its `imm` cells at its own masks or shared
locations. All of it holds again at every end. -/
theorem twp_keepsPoolJ {ts : List StoredJ} {F F₁ : TFrame} {P : TPost} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {Or Op : List (FrameRecT w.K)} {e : Expr} {ρ₁ ρp ρ : TRes w.K}
    (hcρ : ResUT.CompS ρ₁ ρp ρ) (hcov : CovR (sem w.Θ) w.K ρ) (hv : ResUT.Valid ρ)
    (hap : ∀ p ∈ Or, ∀ q ∈ Op, p.le ≠ q.le)
    (hesc₁ : NoneAt (recMask Or) ρp) (hesc₂ : AvoidUnsh (shTop ts) Op ρ₁)
    (hA : HoldsIn (shTop ts) Or ρ₁)
    (hF : ∀ (w₀ : TWd) (ρf ρ₁₀ ρ₂₀ y fρ : TRes w₀.K) (O₁₀ O₂₀ ps psF : List (FrameRecT w₀.K))
      (ls₀ : List (SRecT w₀.K)) (μ : Heap), w.Ext w₀ ρp → RRw (w := w) (w' := w₀) ρp ρ₂₀ →
      RecsRR w₀.Θ Or O₁₀ → RecsRR w₀.Θ Op O₂₀ → F w₀ ρf → ResUT.CompS ρf ρ₂₀ y →
      ResUT.CompS y ρ₁₀ fρ → SplitT ps (O₁₀ ++ O₂₀) psF →
      (∀ p ∈ O₁₀, ∀ q ∈ O₂₀, p.le ≠ q.le) → RecInv w₀ fρ ps ls₀ → WInv w₀ fρ μ → F₁ w₀ y)
    (hwp : twp (ℍ := ℍ) F₁ P n w ls Or e ρ₁) (hP : PoolTJ (ℍ := ℍ) ts w ls Op ρp) :
    twp (ℍ := ℍ) F (PoolPostJ (ℍ := ℍ) P ts) n w ls (Or ++ Op) e ρ := by
  let R : TRProp := fun w' O ρ' => w.Ext w' ρp ∧ RRw (w := w) (w' := w') ρp ρ' ∧ RecsRR w'.Θ Op O
  have hRm : R.Mono := fun _ _ _ _ _ _ hE hr hO ⟨a, b, c⟩ =>
    ⟨a.trans b hE, RRw.trans hE.1 b hr, c.trans hE.1 hO⟩
  have hcovp : CovR (sem w.Θ) w.K ρp := CovR.of_compS_right hcρ hcov
  have hvp : ResUT.Valid ρp := (ResUT.Valid.split hcρ hv).2
  have hv₁ : ResUT.Valid ρ₁ := (ResUT.Valid.split hcρ hv).1
  have hOpc : ∀ r ∈ Op, CovR (sem w.Θ) w.K r.R := PoolTJ.cov_recs hP
  have h := twp_frame_keep_sh (S := shTop ts) (R := R) hRm hap hcρ hcov hv hesc₁ hesc₂ hF
    (twp_holdsIn hv₁ hA hwp) ⟨TWd.Ext.refl _ _, RR.refl hcovp, RecsRR.refl hOpc⟩
  refine twp_mono (fun k₁ w' ls' O' t ρ' hp => ?_) h
  obtain ⟨Oa, Ob, a, b, hO', hc, ⟨hPa, hHa⟩, ⟨hEb, hrb, hOb⟩, hkeep, hb, ha, hap', ho₁, ho₂⟩ := hp
  exact ⟨Oa, Ob, a, b, hO', hc, hPa, hP.kripke hEb hrb hOb hkeep hcovp hvp, hb, ha, hHa,
    hap', ho₁, ho₂⟩

/-! ### The interface -/

/-- **A scheduler answer at index `k`**: applied to any pool meeting `Inv` whose tasks are good
at `k`, with the running task's conditions against it, it answers `Q`. -/
def PoolAnsJAt (Q : TPostV) (H : Val) (Inv : List StoredJ → Prop) : (k : Nat) → (w : TWd) →
    List (SRecT w.K) → List (FrameRecT w.K) → Val → TRes w.K → Prop
  | k, w, ls, O, f, ρ =>
    ∀ (ts : List StoredJ) (Os : List (FrameRecT w.K)) (σ ρ' : TRes w.K),
      Inv ts → (∀ t ∈ ts, t.t.H = H ∧ k ≤ t.t.k ∧
        ∀ (j : Nat) (_hj : j < k) (w' : TWd) (ls' : List (SRecT w'.K))
          (O' : List (FrameRecT w'.K)) (v : Val) (ρ'' : TRes w'.K), t.t.Q j w' ls' O' v ρ'' →
          ∀ (j' : Nat) (_hj' : j' ≤ j), PoolAnsJAt Q H Inv j' w' ls' O' v ρ'') →
      PoolTJ (ℍ := ℍ) ts w ls Os σ → ResUT.CompS ρ σ ρ' → NoneAt (recMask O) σ →
      AvoidUnsh (shTop ts) Os ρ → HoldsIn (shTop ts) O ρ → RecsApart O Os →
      CovR (sem w.Θ) w.K ρ' → ResUT.Valid ρ' → (∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R) →
      (∀ r ∈ O, CovR (sem w.Θ) w.K r.R) →
      ∀ F : TFrame, F.Mono → (∀ w' ρf, F w' ρf → fdMask (recMask (O ++ Os)) w' ρf) →
      twp (ℍ := ℍ) F (valPost Q) k w ls (O ++ Os) (.app f.1 (stateValJ H ts).1) ρ'
termination_by k => k

def PoolAnsJ (Q : TPostV) (H : Val) (Inv : List StoredJ → Prop) : TPostV :=
  fun k w ls O f ρ => ∀ j ≤ k, PoolAnsJAt (ℍ := ℍ) Q H Inv j w ls O f ρ

theorem poolAnsJ_down (Q : TPostV) (H : Val) (Inv : List StoredJ → Prop) :
    (PoolAnsJ (ℍ := ℍ) Q H Inv).Down :=
  fun _ _ _ _ _ _ h j hj => h j (by omega)

def GoodJ (Q : TPostV) (H : Val) (Inv : List StoredJ → Prop) (k : Nat) (t : StoredJ) : Prop :=
  t.t.H = H ∧ k ≤ t.t.k ∧
    ∀ (j : Nat), j < k → ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (O' : List (FrameRecT w'.K))
      (v : Val) (ρ'' : TRes w'.K), t.t.Q j w' ls' O' v ρ'' → PoolAnsJ (ℍ := ℍ) Q H Inv j w' ls' O' v ρ''

theorem GoodJ.le {Q : TPostV} {H : Val} {Inv : List StoredJ → Prop} {k k' : Nat} {t : StoredJ}
    (h : GoodJ (ℍ := ℍ) Q H Inv k t) (hk : k' ≤ k) : GoodJ (ℍ := ℍ) Q H Inv k' t :=
  ⟨h.1, by have := h.2.1; omega, fun j hj => h.2.2 j (by omega)⟩

theorem poolAnsJAt_iff {Q : TPostV} {H : Val} {Inv : List StoredJ → Prop} {k : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {f : Val} {ρ : TRes w.K} :
    PoolAnsJAt (ℍ := ℍ) Q H Inv k w ls O f ρ ↔
      ∀ (ts : List StoredJ) (Os : List (FrameRecT w.K)) (σ ρ' : TRes w.K),
        Inv ts → (∀ t ∈ ts, GoodJ (ℍ := ℍ) Q H Inv k t) →
        PoolTJ (ℍ := ℍ) ts w ls Os σ → ResUT.CompS ρ σ ρ' → NoneAt (recMask O) σ →
        AvoidUnsh (shTop ts) Os ρ → HoldsIn (shTop ts) O ρ → RecsApart O Os →
        CovR (sem w.Θ) w.K ρ' → ResUT.Valid ρ' → (∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R) →
        (∀ r ∈ O, CovR (sem w.Θ) w.K r.R) →
        ∀ F : TFrame, F.Mono → (∀ w' ρf, F w' ρf → fdMask (recMask (O ++ Os)) w' ρf) →
        twp (ℍ := ℍ) F (valPost Q) k w ls (O ++ Os) (.app f.1 (stateValJ H ts).1) ρ' := by
  rw [PoolAnsJAt]
  constructor
  · intro h ts Os σ ρ' hi hg
    exact h ts Os σ ρ' hi fun t ht => ⟨(hg t ht).1, (hg t ht).2.1,
      fun j hj w' ls' O' v ρ'' hq => (hg t ht).2.2 j hj w' ls' O' v ρ'' hq⟩
  · intro h ts Os σ ρ' hi hg
    exact h ts Os σ ρ' hi fun t ht => ⟨(hg t ht).1, (hg t ht).2.1,
      fun j hj w' ls' O' v ρ'' hq => (hg t ht).2.2 j hj w' ls' O' v ρ'' hq⟩

/-! ### The moves -/

/-- **Park**: the stopped task joins the pool at its top, as a ready task or a joiner sharing
`sh` (lent locations of its own or shared with it). -/
theorem poolAnsJ_park {Q : TPostV} {H : Val} {Inv : List StoredJ → Prop} {en : OpEntT} {k : Nat}
    {v κ : Val} (jn : Bool) (sh : BoCa.Loc → Prop) (tag : Val) {ts : List StoredJ} {w : TWd}
    {ls : List (SRecT w.K)} {Ot Os : List (FrameRecT w.K)} {a b ρ : TRes w.K}
    (hκ : KapSchedT (ℍ := ℍ) (PoolAnsJ (ℍ := ℍ) Q H Inv) (recMask Ot) en H k w ls Ot v κ a)
    {j : Nat} (hj : j ≤ k) (hg : ∀ t ∈ ts, GoodJ (ℍ := ℍ) Q H Inv j t)
    (hP : PoolTJ (ℍ := ℍ) ts w ls Os b) (hc : ResUT.CompS a b ρ)
    (hb : NoneAt (recMask Ot) b) (ha : AvoidUnsh (shTop ts) Os a) (hH : HoldsIn (shTop ts) Ot a)
    (hsh : ∀ x, sh x → recMask Ot x ∨ shTop ts x) (hap : RecsApart Ot Os)
    (hcov : CovR (sem w.Θ) w.K a)
    (hls : ∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R) (hO : ∀ r ∈ Ot, CovR (sem w.Θ) w.K r.R) :
    PoolTJ (ℍ := ℍ) (⟨⟨PoolAnsJ (ℍ := ℍ) Q H Inv, recMask Ot, en, H, k, v, κ⟩, jn, sh, tag⟩ :: ts)
      w ls (Ot ++ Os) ρ ∧
    ∀ t ∈ (⟨⟨PoolAnsJ (ℍ := ℍ) Q H Inv, recMask Ot, en, H, k, v, κ⟩, jn, sh, tag⟩ :: ts :
      List StoredJ), GoodJ (ℍ := ℍ) Q H Inv j t := by
  refine ⟨⟨Ot, Os, a, b, rfl, hc, KapAtT.of_stop hκ hcov hls hO, fun _ => Iff.rfl, hP, hb, ha, hH,
    hsh, hap⟩, ?_⟩
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact ⟨rfl, hj, fun _ _ _ _ _ _ _ h => h⟩
  · exact hg t ht

/-- What a stored task answers when resumed, handed the rest of the pool. -/
theorem poolAnsJ_handRest {Q : TPostV} {H : Val} {Inv : List StoredJ → Prop} {t : StoredJ}
    {ts : List StoredJ} {k' : Nat} (hg : ∀ u ∈ t :: ts, GoodJ (ℍ := ℍ) Q H Inv (k' + 1) u)
    (hi : Inv ts) {F : TFrame} (hFm : F.Mono) :
    ∀ k₁, k₁ ≤ k' → ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (O' : List (FrameRecT w'.K)) t₁
      (ρ' : TRes w'.K), CovR (sem w'.Θ) w'.K ρ' → ResUT.Valid ρ' →
      (∀ x ∈ ls', CovR (sem w'.Θ) w'.K x.1.R) → (∀ r ∈ O', CovR (sem w'.Θ) w'.K r.R) →
      PoolPostJ (ℍ := ℍ) (valPost t.t.Q) ts k₁ w' ls' O' t₁ ρ' →
      twp (ℍ := ℍ) (F.and (fdMask (recMask O'))) (valPost Q) k₁ w' ls' O'
        ((Kont.appL .hole (stateValJ H ts)).plug t₁) ρ' := by
  intro k₁ hk₁ w' ls' O' t₁ ρ' hcov hv hls hO hpost
  obtain ⟨Oa, Ob, a, b, rfl, hc, ⟨f, rfl, hf⟩, hP, hb, ha, hH, hap⟩ := hpost
  have hfa := (hg t List.mem_cons_self).2.2 k₁ (by omega) w' ls' Oa f a hf
  exact poolAnsJAt_iff.mp (hfa k₁ le_rfl) ts Ob b ρ' hi
    (fun u hu => (hg u (List.mem_cons_of_mem _ hu)).le (by omega)) hP hc hb ha hH hap hcov hv hls
    (fun x hx => hO x (List.mem_append_left _ hx)) _ (TFrame.and_mono hFm (fdMask_mono _))
    (fun _ _ h => h.2)

/-- **Resume**: the pool's top task resumed at an answer `a` its entry accepts, the rest handed to
what it answers. The answer `σ` holds nothing at the pool's records the top's nearest joiner does
not share, and its `imm` cells only where the top's nearest joiner shares: a joiner resumed with
its children's views, say. -/
theorem poolAnsJ_resume {Q : TPostV} {H : Val} {Inv : List StoredJ → Prop} {t : StoredJ}
    {ts : List StoredJ} {k' : Nat} (hg : ∀ u ∈ t :: ts, GoodJ (ℍ := ℍ) Q H Inv (k' + 1) u)
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ρp σ ρ : TRes w.K}
    (hP : PoolTJ (ℍ := ℍ) (t :: ts) w ls O ρp) {a : Val} (hB : t.t.en.PBv t.t.v k' w ls a σ)
    (hc : ResUT.CompS ρp σ ρ) (hσ : AvoidUnsh (shTop (t :: ts)) O σ)
    (hσH : HoldsIn (shTop (t :: ts)) [] σ) (hcov : CovR (sem w.Θ) w.K ρ)
    (hv : ResUT.Valid ρ) {F : TFrame} (hFm : F.Mono)
    (hFM : ∀ w' ρf, F w' ρf → fdMask (recMask O) w' ρf) (hi : Inv ts) :
    twp (ℍ := ℍ) F (valPost Q) k' w ls O
      (.app (.app (.app t.t.κ.1 (.val (Val.inj₁ .unit))) (.val a)) (stateValJ H ts).1) ρ := by
  obtain ⟨Ot, Os, ρt, ρs, rfl, hcp, hκ, hM, hPs, hb, ha, hH, hsh, hap⟩ := id hP
  have hk : k' < t.t.k := by have := (hg t List.mem_cons_self).2.1; omega
  obtain ⟨σ', hσ₁, hσ₂⟩ := (ResUT.CompS.assoc ρs ρt σ ρ).mpr ⟨ρp, ResUT.CompS.comm hcp, hc⟩
  have hσ₂' := ResUT.CompS.comm hσ₂
  have hvσ' := (ResUT.Valid.split hσ₂' hv).1
  have hvs := (ResUT.Valid.split hσ₂' hv).2
  have hvt := ResUT.Valid.split hσ₁ hvσ'
  -- the answer avoids the rest's unshared records: what the top shares is its own or shared below
  have hσs : AvoidUnsh (shTop ts) Os σ := fun q hq hn => hσ q (List.mem_append_right _ hq) fun h => by
    rcases h with ⟨-, h⟩ | ⟨-, h⟩
    · rcases hsh _ h with h | h
      · exact hap.2.1 q hq h
      · exact hn h
    · exact hn h
  have hσH' : HoldsIn (shTop ts) Ot σ := by
    intro τ hτ x ψ e k
    rcases (hσH τ hτ x ψ e k).resolve_left (by simp [recMask]) with ⟨-, h⟩ | ⟨-, h⟩
    · rcases hsh x h with h | h
      · exact Or.inl ((hM x).mp ((hM x).mpr h))
      · exact Or.inr h
    · exact Or.inr h
  have hres := cerwpTE_iff.mp (hκ.resume hk hB hσ₁ (fdMask_mono t.t.M) (fun _ _ h => h))
  have h := twp_keepsPoolJ (ts := ts) hσ₂' hcov hv hap.1 hb
    (AvoidUnsh.compS hσ₁ hvt.1 hvt.2 ha hσs) ((hH.compS hσ₁ hσH'))
    (pool_frame (F := F) (M := t.t.M)
      (fun w' ρf hf => fdMask_le (fun x hx => (recMask_append x).mpr (Or.inl ((hM x).mp hx)))
        (hFM w' ρf hf)) hM hvs hb) hres hPs
  have hM' : ∀ w' ρf, F w' ρf → fdMask (fun x => recMask Ot x ∨ recMask Os x) w' ρf :=
    fun w' ρf hf => fdMask_le (fun x hx => (recMask_append x).mpr hx) (hFM w' ρf hf)
  exact twp_bind_fd hFm (fun _ _ h => h) (Kont.appL .hole (stateValJ H ts))
    (fun w₀ ρf hf => (hFM w₀ ρf hf).2) h (poolAnsJ_handRest hg hi hFm)

/-- **Join**: a task that has finished owning no record, its resource `ρ`, the pool's top a joiner
`t`: `t` is resumed with `ρ` as its answer's resource. The finished task's own conditions against
the pool (`PoolAnsJAt`'s premises at `O = []`) are what the resume asks of `σ`: the views it hands
back are where `t` shares, and it holds nothing of the pool's unshared records. -/
theorem poolAnsJ_join {Q : TPostV} {H : Val} {Inv : List StoredJ → Prop} {t : StoredJ}
    {ts : List StoredJ} {k' : Nat} (hg : ∀ u ∈ t :: ts, GoodJ (ℍ := ℍ) Q H Inv (k' + 1) u)
    {w : TWd} {ls : List (SRecT w.K)} {Os : List (FrameRecT w.K)} {ρ σp ρ' : TRes w.K}
    (hP : PoolTJ (ℍ := ℍ) (t :: ts) w ls Os σp) (hc : ResUT.CompS ρ σp ρ')
    (hA : AvoidUnsh (shTop (t :: ts)) Os ρ) (hH : HoldsIn (shTop (t :: ts)) [] ρ) {a : Val}
    (hB : t.t.en.PBv t.t.v k' w ls a ρ) (hcov : CovR (sem w.Θ) w.K ρ') (hv : ResUT.Valid ρ')
    {F : TFrame} (hFm : F.Mono) (hFM : ∀ w' ρf, F w' ρf → fdMask (recMask Os) w' ρf)
    (hi : Inv ts) :
    twp (ℍ := ℍ) F (valPost Q) k' w ls Os
      (.app (.app (.app t.t.κ.1 (.val (Val.inj₁ .unit))) (.val a)) (stateValJ H ts).1) ρ' :=
  poolAnsJ_resume hg hP hB (ResUT.CompS.comm hc) hA hH hcov hv hFm hFM hi

/-- **Run, at a scheduler meeting its clauses up to `N`**: a task run under the scheduler beside
the pool, the state handed to what it answers. -/
theorem poolAnsJ_run_le {N : Nat} {T : OpTabT} {n₀ : UInt32} {qs hr hs : Val} {Qin Q : TPostV}
    {Inv : List StoredJ → Prop}
    (hS : SchedOKTLe (ℍ := ℍ) N T n₀ qs hr hs Qin (PoolAnsJ (ℍ := ℍ) Q (hndVal n₀ qs hr hs) Inv))
    {ts : List StoredJ} {k : Nat} (hkN : k ≤ N)
    (hg : ∀ u ∈ ts, GoodJ (ℍ := ℍ) Q (hndVal n₀ qs hr hs) Inv k u) (hi : Inv ts)
    {w : TWd} {ls : List (SRecT w.K)} {Or Op : List (FrameRecT w.K)} {e : Expr}
    {ρ₁ ρp ρ : TRes w.K} (hP : PoolTJ (ℍ := ℍ) ts w ls Op ρp) (hcρ : ResUT.CompS ρ₁ ρp ρ)
    (hcov : CovR (sem w.Θ) w.K ρ) (hv : ResUT.Valid ρ) (hap : ∀ p ∈ Or, ∀ q ∈ Op, p.le ≠ q.le)
    (hesc₁ : NoneAt (recMask Or) ρp) (hesc₂ : AvoidUnsh (shTop ts) Op ρ₁)
    (hA : HoldsIn (shTop ts) Or ρ₁) {Fb Fe : TFrame}
    (hFb : ∀ w ρf, ResUT.Valid ρf → Fb w ρf) (hFe : ∀ w ρf, fdMask (recMask Or) w ρf → Fe w ρf)
    (he : cerwpT (ℍ := ℍ) (opTableT T) Qin Fb Fe k w ls Or e ρ₁) {F : TFrame} (hFm : F.Mono)
    (hFM : ∀ w' ρf, F w' ρf → fdMask (recMask (Or ++ Op)) w' ρf) :
    twp (ℍ := ℍ) F (valPost Q) k w ls (Or ++ Op)
      (.app (hndE (hndVal n₀ qs hr hs) e) (stateValJ (hndVal n₀ qs hr hs) ts).1) ρ := by
  have hvp := (ResUT.Valid.split hcρ hv).2
  have h₁ := cerwpT_schedHandle_le hS k hkN (recMask Or) (fdMask (recMask Or)) Fb Fe w ls Or e ρ₁
    (fdMask_mono _) (fun _ _ h => h) (fun _ h => h) hFb hFe he
  have h₂ := twp_keepsPoolJ hcρ hcov hv hap hesc₁ hesc₂ hA
    (pool_frame (M := recMask Or) (F := F)
      (fun w ρf hf => fdMask_le (fun x hx => (recMask_append x).mpr (_root_.Or.inl hx)) (hFM w ρf hf))
      (fun _ => Iff.rfl) hvp hesc₁) h₁ hP
  refine twp_bind_fd hFm (fun _ _ h => h) (Kont.appL .hole (stateValJ (hndVal n₀ qs hr hs) ts))
    (fun w₀ ρf hf => (hFM w₀ ρf hf).2) h₂ ?_
  intro k₁ hk₁ w' ls' O' t₁ ρ' hcov' hv' hls' hO' hpost
  obtain ⟨Oa, Ob, a, b, rfl, hc, ⟨f, rfl, hf⟩, hP', hb, ha, hH, hap'⟩ := hpost
  exact poolAnsJAt_iff.mp (hf k₁ le_rfl) ts Ob b ρ' hi (fun u hu => (hg u hu).le hk₁) hP' hc hb ha
    hH hap' hcov' hv' hls' (fun x hx => hO' x (List.mem_append_left _ hx)) _
    (TFrame.and_mono hFm (fdMask_mono _)) (fun _ _ h => h.2)

/-! ### The headline -/

/-- **Pool-scheduler adequacy, at the stack interface**: `PoolSchedAdequacyT`'s statement with
`PoolAnsJ` for `PoolAns`. -/
def PoolSchedAdequacyJ : Prop :=
  ∀ (P : ParentFn) (T : OpTabT) (n₀ : UInt32) (qs hr hs : Val) (Qin Q : TPostV)
    (Inv : List StoredJ → Prop) (Fb Fe : TFrame) (e₀ : Expr),
    (∀ k w ls O v ρ, Q k w ls O v ρ → ρ = PMap.empty) → Inv [] →
    SchedOKT (ℍ := ℍ) T n₀ qs hr hs Qin (PoolAnsJ (ℍ := ℍ) Q (hndVal n₀ qs hr hs) Inv) →
    (∀ w ρf, ResUT.Valid ρf → Fb w ρf) → (∀ w ρf, fdMask (fun _ => False) w ρf → Fe w ρf) →
    (∀ n, cerwpT (ℍ := ℍ) (opTableT T) Qin Fb Fe n (w₀ P) [] [] e₀
      (PMap.empty : TRes (WCactus.ofParent P))) →
    OrDiverges (ℍ := ℍ) (.app (hndE (hndVal n₀ qs hr hs) e₀) (stateValJ (hndVal n₀ qs hr hs) []).1)

theorem poolSchedJ_twp {T : OpTabT} {n₀ : UInt32} {qs hr hs : Val} {Qin Q : TPostV}
    {Inv : List StoredJ → Prop} {Fb Fe : TFrame} {e₀ : Expr} (hInv : Inv [])
    (hS : SchedOKT (ℍ := ℍ) T n₀ qs hr hs Qin (PoolAnsJ (ℍ := ℍ) Q (hndVal n₀ qs hr hs) Inv))
    (hFb : ∀ w ρf, ResUT.Valid ρf → Fb w ρf) (hFe : ∀ w ρf, fdMask (fun _ => False) w ρf → Fe w ρf)
    {F : TFrame} (hFm : F.Mono) (hF0 : ∀ w ρf, F w ρf → ρf = PMap.empty) {n : Nat} {w : TWd}
    {ρ : TRes w.K} (hv : ResUT.Valid ρ) (hH : HoldsIn (fun _ => False) [] ρ)
    (he : cerwpT (ℍ := ℍ) (opTableT T) Qin Fb Fe n w [] [] e₀ ρ) :
    twp (ℍ := ℍ) F (valPost Q) n w [] []
      (.app (hndE (hndVal n₀ qs hr hs) e₀) (stateValJ (hndVal n₀ qs hr hs) []).1) ρ := by
  have hFv : ∀ w ρf, F w ρf → fdMask (fun _ => False) w ρf :=
    fun w ρf h => by rw [hF0 w ρf h]; exact fdMask_empty _ w
  have h := twp_holdsIn hv hH (schedProgram_twp hS hFb hFe hFm hFv he)
  refine twp_bind_fd hFm (fun _ _ h => h) (Kont.appL .hole (stateValJ (hndVal n₀ qs hr hs) []))
    (fun w₀ ρf hf => by rw [hF0 _ _ hf]; exact noneAt_empty _) h ?_
  rintro k _ w' ls' O' t ρ' hcov hv' hls hO ⟨⟨f, rfl, hf⟩, hH'⟩
  have h₁ := poolAnsJAt_iff.mp (hf k le_rfl) [] [] PMap.empty ρ' hInv (fun _ h => by cases h)
    poolTJ_nil (ResUT.compS_empty_right ρ') (noneAt_empty _) (fun _ h => by cases h) hH'
    ⟨fun _ _ _ h => (by cases h), fun _ h => (by cases h), fun _ _ h => (by simp [recMask] at h)⟩
    hcov hv' hls hO _ (TFrame.and_mono hFm (fdMask_mono _)) (fun _ _ h => by simpa using h.2)
  rw [List.append_nil] at h₁; exact h₁

theorem poolSchedAdequacyJ : PoolSchedAdequacyJ (ℍ := ℍ) :=
  fun P _ _ _ _ _ _ _ _ _ _ _ hQ hInv hS hFb hFe he => topAdequacyT P _ _ hQ fun n =>
    cerwpTE_iff.mpr (poolSchedJ_twp hInv hS hFb hFe emptyFrame_mono (fun _ _ h => h)
      ⟨_, flat_empty⟩ (HoldsIn.empty _ _) (he n))

end BoCa.Fig16.Tree.Wp.Join

end
