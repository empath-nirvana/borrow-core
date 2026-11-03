import Core.TreePool

/-!
# The scheduler's pool: stored tasks and their separation, kept by every operation  `[spec §62]`

**The guarantee.** A scheduler that holds its stored tasks as a pool (`PoolT`: each a continuation
held at the present world, `KapAtT`, and every two apart at the masks of each other's records) keeps
the pool through each of its operations:

* **a segment** (`twp_keepsPool`): any run beside the pool, the run's records apart from the pool's,
  ends with the pool held at the end world and list, still apart from the run. The run may open
  lends, end lends of its own (those open when a stored task stopped included), allocate and free;
* **a park** (`poolT_park`): a continuation the stepper hands back (`KapSchedT` at its stop) joins
  the pool, apart from it by what the segment that stopped returned;
* **a resume** (`poolT_resume`): the pool's first task resumed at an answer its entry accepts, the
  rest beside it; at every end of the resumed run the rest is a pool at the end world;
* **a cancel** (`poolT_cancel`): the same, its cancel branch run under its scheduler again
  (`KapSchedT`'s third clause), at a cancellable entry. An unwinding that stops at an operation
  comes back as the scheduler's answer like a resume's, and is parked again.

Each stored task's premises are its own stop's (`KapSchedT`); nothing in a resume reads another
task's history. The pool's separation is the join condition in location form, both ways.

**Scope.** A stored task's mask `M` is the masks of the records it holds (`t.M x ↔ recMask O x`),
not a history: a run beside the pool keeps apart from the pool's present records (R1), not from
locations a stored task held at an earlier stop and has since ended. `KapSchedT`'s `M` holds that
history (`cerwpT_schedHandle` accumulates it through `fdAt` at the frame condition the task resumes
at); resuming at the task's base frame condition removes it. Until then a pool admits a task whose
history is its present records, which is every task that owns no record across an earlier stop.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont hndE)

/-- **A stored task**: what its continuation `κ` answers (`Q`), its mask, its entry, the scheduler
it runs under (`H`), its index and payload. -/
structure StoredT where
  Q : TPostV
  M : BoCa.Loc → Prop
  en : OpEntT
  H : Val
  k : Nat
  v : Val
  κ : Val

/-- **The pool**: the tasks' shares and records, each task held at `w` with the list `ls`, its
mask its records' masks, and each apart from the tasks after it, both ways. -/
def PoolT : List StoredT → (w : TWd) → List (SRecT w.K) → List (FrameRecT w.K) → TRes w.K → Prop
  | [], _, _, O, ρ => O = [] ∧ ρ = PMap.empty
  | t :: ts, w, ls, O, ρ => ∃ (Ot Os : List (FrameRecT w.K)) (a b : TRes w.K),
      O = Ot ++ Os ∧ ResUT.CompS a b ρ ∧
      KapAtT (ℍ := ℍ) t.Q t.M t.en t.H t.k t.v t.κ w ls Ot a ∧ (∀ x, t.M x ↔ recMask Ot x) ∧
      PoolT ts w ls Os b ∧ NoneAt (recMask Ot) b ∧ NoneAt (recMask Os) a ∧
      (∀ p ∈ Ot, ∀ q ∈ Os, p.le ≠ q.le)

theorem poolT_nil {w : TWd} {ls : List (SRecT w.K)} :
    PoolT (ℍ := ℍ) [] w ls [] (PMap.empty : TRes w.K) := ⟨rfl, rfl⟩

/-- Apartness of two record lists, carried along their re-readings. -/
theorem apart_rr {K K' : WCactus} {Θ' : CodeTy} {O₁ O₂ : List (FrameRecT K)}
    {O₁' O₂' : List (FrameRecT K')} (h₁ : RecsRR Θ' O₁ O₁') (h₂ : RecsRR Θ' O₂ O₂')
    (h : ∀ p ∈ O₁, ∀ q ∈ O₂, p.le ≠ q.le) : ∀ p ∈ O₁', ∀ q ∈ O₂', p.le ≠ q.le := by
  intro p hp q hq
  obtain ⟨p₁, hp₁, r₁⟩ := forall₂_mem_right h₁ hp
  obtain ⟨q₂, hq₂, r₂⟩ := forall₂_mem_right h₂ hq
  rw [r₁.1, r₂.1]
  exact h p₁ hp₁ q₂ hq₂

/-- **The pool is held at every extension of the world**, on its re-reading, at every list keeping
the records of `ls` its shares read. -/
theorem PoolT.kripke : ∀ {ts : List StoredT} {w w' : TWd} {ls : List (SRecT w.K)}
    {ls' : List (SRecT w'.K)} {O : List (FrameRecT w.K)} {O' : List (FrameRecT w'.K)}
    {ρ : TRes w.K} {ρ' : TRes w'.K}, PoolT (ℍ := ℍ) ts w ls O ρ → w.Ext w' ρ →
    RRw (w := w) (w' := w') ρ ρ' → RecsRR w'.Θ O O' → KeepRel w'.Θ ls ls' ρ →
    CovR (sem w.Θ) w.K ρ → ResUT.Valid ρ → PoolT (ℍ := ℍ) ts w' ls' O' ρ'
  | [], _, _, _, _, _, _, _, _, ⟨hO, hρ⟩, _, hr, hOr, _, _, _ => by
      subst hO; subst hρ; cases hOr; exact ⟨rfl, RR.of_empty hr⟩
  | t :: ts, w, w', ls, ls', O, O', ρ, ρ',
      ⟨Ot, Os, a, b, hO, hc, hκ, hM, hP, hb, ha, hap⟩, hE, hr, hOr, hl, hcov, hv => by
      subst hO
      obtain ⟨Ot', Os', rfl, hOt, hOs⟩ := forall₂_append_left hOr
      obtain ⟨a', b', hra, hrb, hc'⟩ := RR.split_retype hE.1 hc hcov hE.2 hr
      have hva := (ResUT.Valid.split hc hv).1
      have hvb := (ResUT.Valid.split hc hv).2
      refine ⟨Ot', Os', a', b', rfl, hc',
        hκ.kripke (hE.of_compS_left hc) hra hOt (hl.of_compS_left hc),
        fun x => (hM x).trans (recMask_rr hOt x),
        PoolT.kripke hP (hE.of_compS_right hc) hrb hOs
          (hl.of_compS_left (ResUT.CompS.comm hc)) (hcov.of_compS_right hc) hvb,
        (NoneAt.rr hE.1 hvb hrb hb).mono fun x hx => (recMask_rr hOt x).mpr hx,
        (NoneAt.rr hE.1 hva hra ha).mono fun x hx => (recMask_rr hOs x).mpr hx,
        apart_rr hOt hOs hap⟩

/-- The pool's records are covered at its world (each a re-reading, `KapAtT`). -/
theorem PoolT.cov_recs : ∀ {ts : List StoredT} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {ρ : TRes w.K}, PoolT (ℍ := ℍ) ts w ls O ρ →
    ∀ r ∈ O, CovR (sem w.Θ) w.K r.R
  | [], _, _, _, _, ⟨hO, _⟩ => by subst hO; intro r hr; cases hr
  | _ :: _, _, _, _, _, ⟨Ot, Os, a, b, hO, _, hκ, _, hP, _⟩ => by
      subst hO
      intro r hr
      rcases List.mem_append.mp hr with hr | hr
      · obtain ⟨w₁, ls₁, O₁, ρ₁', hK, hE₁, hr₁, hO₁, -⟩ := hκ
        obtain ⟨r₁, -, hrr⟩ := forall₂_mem_right hO₁ hr
        exact hrr.2.2.2.cov
      · exact PoolT.cov_recs hP r hr

/-! ### A segment beside the pool -/

/-- **A segment keeps the pool.** A run of `e` from `ρ₁` owning `Or`, beside the pool (`ρp`
owning `Op`), the two holding nothing at each other's record masks: at every end of the run, at the
world `w′` and list `ls′` it ends in, the pool is held there, and the run's end and the pool are
still apart. `hF` is `twp_frame_keep`'s frame obligation. -/
theorem twp_keepsPool {ts : List StoredT} {F F₁ : TFrame} {P : TPost} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {Or Op : List (FrameRecT w.K)} {e : Expr} {ρ₁ ρp ρ : TRes w.K}
    (hcρ : ResUT.CompS ρ₁ ρp ρ) (hcov : CovR (sem w.Θ) w.K ρ) (hv : ResUT.Valid ρ)
    (hap : ∀ p ∈ Or, ∀ q ∈ Op, p.le ≠ q.le)
    (hesc₁ : NoneAt (recMask Or) ρp) (hesc₂ : NoneAt (recMask Op) ρ₁)
    (hF : ∀ (w₀ : TWd) (ρf ρ₁₀ ρ₂₀ y fρ : TRes w₀.K) (O₁₀ O₂₀ ps psF : List (FrameRecT w₀.K))
      (ls₀ : List (SRecT w₀.K)) (μ : Heap), w.Ext w₀ ρp → RRw (w := w) (w' := w₀) ρp ρ₂₀ →
      RecsRR w₀.Θ Or O₁₀ → RecsRR w₀.Θ Op O₂₀ → F w₀ ρf → ResUT.CompS ρf ρ₂₀ y →
      ResUT.CompS y ρ₁₀ fρ → SplitT ps (O₁₀ ++ O₂₀) psF →
      (∀ p ∈ O₁₀, ∀ q ∈ O₂₀, p.le ≠ q.le) → RecInv w₀ fρ ps ls₀ → WInv w₀ fρ μ → F₁ w₀ y)
    (hwp : twp (ℍ := ℍ) F₁ P n w ls Or e ρ₁) (hP : PoolT (ℍ := ℍ) ts w ls Op ρp) :
    twp (ℍ := ℍ) F (fun k₁ w' ls' O' t ρ' => ∃ (Oa Ob : List (FrameRecT w'.K)) (a b : TRes w'.K),
      O' = Oa ++ Ob ∧ ResUT.CompS a b ρ' ∧ P k₁ w' ls' Oa t a ∧
        PoolT (ℍ := ℍ) ts w' ls' Ob b ∧ NoneAt (recMask Oa) b ∧ NoneAt (recMask Ob) a)
      n w ls (Or ++ Op) e ρ := by
  let R : TRProp := fun w' O ρ' => w.Ext w' ρp ∧ RRw (w := w) (w' := w') ρp ρ' ∧ RecsRR w'.Θ Op O
  have hRm : R.Mono := fun _ _ _ _ _ _ hE hr hO ⟨a, b, c⟩ =>
    ⟨a.trans b hE, RRw.trans hE.1 b hr, c.trans hE.1 hO⟩
  have hcovp : CovR (sem w.Θ) w.K ρp := CovR.of_compS_right hcρ hcov
  have hvp : ResUT.Valid ρp := (ResUT.Valid.split hcρ hv).2
  have hOpc : ∀ r ∈ Op, CovR (sem w.Θ) w.K r.R := PoolT.cov_recs hP
  have h := twp_frame_keep (R := R) hRm hap hcρ hcov hv hesc₁ hesc₂ hF hwp
    ⟨TWd.Ext.refl _ _, RR.refl hcovp, RecsRR.refl hOpc⟩
  refine twp_mono (fun k₁ w' ls' O' t ρ' hp => ?_) h
  obtain ⟨Oa, Ob, a, b, hO', hc, hPa, ⟨hEb, hrb, hOb⟩, hkeep, hb, ha⟩ := hp
  exact ⟨Oa, Ob, a, b, hO', hc, hPa, hP.kripke hEb hrb hOb hkeep hcovp hvp, hb, ha⟩

/-! ### Park, resume, cancel -/

/-- **A park**: a continuation at its stop (`KapSchedT`), its mask its records' masks, joins the
pool beside it, the two apart both ways. -/
theorem poolT_park {t : StoredT} {ts : List StoredT} {w : TWd} {ls : List (SRecT w.K)}
    {Ot Os : List (FrameRecT w.K)} {a b ρ : TRes w.K}
    (hκ : KapSchedT (ℍ := ℍ) t.Q t.M t.en t.H t.k w ls Ot t.v t.κ a)
    (hM : ∀ x, t.M x ↔ recMask Ot x) (hP : PoolT (ℍ := ℍ) ts w ls Os b) (hc : ResUT.CompS a b ρ)
    (hb : NoneAt (recMask Ot) b) (ha : NoneAt (recMask Os) a) (hap : ∀ p ∈ Ot, ∀ q ∈ Os, p.le ≠ q.le)
    (hcov : CovR (sem w.Θ) w.K a) (hls : ∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R)
    (hO : ∀ r ∈ Ot, CovR (sem w.Θ) w.K r.R) : PoolT (ℍ := ℍ) (t :: ts) w ls (Ot ++ Os) ρ :=
  ⟨Ot, Os, a, b, rfl, hc, KapAtT.of_stop hκ hcov hls hO, hM, hP, hb, ha, hap⟩

/-- `κ` held at `w`, at a cancellable entry: its cancel branch under its scheduler, at `w`. -/
theorem KapAtT.cancel {Qout : TPostV} {M : BoCa.Loc → Prop} {en : OpEntT} {H : Val} {k : Nat}
    {v κ : Val} {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ρ : TRes w.K}
    (h : KapAtT (ℍ := ℍ) Qout M en H k v κ w ls O ρ) (hq : en.q ≠ .lin) (hf : en.fin = true)
    {k' : Nat} (hk : k' < k) {F' : TFrame} (hF'm : F'.Mono)
    (hF'M : ∀ w'' ρf, F' w'' ρf → fdMask M w'' ρf) :
    cerwpT (ℍ := ℍ) (opTableT OpTabT.empty) Qout F' k' w ls O
      (hndE H (.app κ.1 (.val (Val.inj₂ .unit)))) ρ := by
  obtain ⟨w₁, ls₁, O₁, ρ₁, hK, hE, hr, hO, hl⟩ := h
  exact hK.2.2 w ρ ls O hE hr hl hO hq hf k' hk F' hF'm hF'M

theorem recMask_append_right {K : WCactus} {O₁ O₂ : List (FrameRecT K)} {x : BoCa.Loc}
    (h : recMask O₂ x) : recMask (O₁ ++ O₂) x := by
  obtain ⟨q, hq, hx⟩ := h
  exact ⟨q, List.mem_append_right _ hq, hx⟩

/-- The frame obligation of a stored task's run beside the rest of the pool: a frame avoiding the
task's mask, beside the rest re-read, which holds nothing at the task's records. -/
theorem pool_frame {M : BoCa.Loc → Prop} {F : TFrame} (hFM : ∀ w' ρf, F w' ρf → fdMask M w' ρf)
    {w : TWd} {Ot : List (FrameRecT w.K)} {ρs : TRes w.K} (hM : ∀ x, M x ↔ recMask Ot x)
    (hvs : ResUT.Valid ρs) (hb : NoneAt (recMask Ot) ρs) {Or Op : List (FrameRecT w.K)} :
    ∀ (w₀ : TWd) (ρf ρ₁₀ ρ₂₀ y fρ : TRes w₀.K) (O₁₀ O₂₀ ps psF : List (FrameRecT w₀.K))
      (ls₀ : List (SRecT w₀.K)) (μ : Heap), w.Ext w₀ ρs → RRw (w := w) (w' := w₀) ρs ρ₂₀ →
      RecsRR w₀.Θ Or O₁₀ → RecsRR w₀.Θ Op O₂₀ → F w₀ ρf → ResUT.CompS ρf ρ₂₀ y →
      ResUT.CompS y ρ₁₀ fρ → SplitT ps (O₁₀ ++ O₂₀) psF →
      (∀ p ∈ O₁₀, ∀ q ∈ O₂₀, p.le ≠ q.le) → RecInv w₀ fρ ps ls₀ → WInv w₀ fρ μ → fdMask M w₀ y := by
  intro w₀ ρf ρ₁₀ ρ₂₀ y fρ O₁₀ O₂₀ ps psF ls₀ μ hE h₂₀ _ _ hFρ hy hyf _ _ _ hI
  have hvy : ResUT.Valid y := (ResUT.Valid.split hyf hI.valid).1
  have hvf := ResUT.Valid.split hy hvy
  exact ⟨hvy, NoneAt.compS hy hvf.1 hvf.2 (hFM w₀ ρf hFρ).2
    ((NoneAt.rr hE.1 hvs h₂₀ hb).mono fun x hx => (hM x).mp hx)⟩

/-- **A resume keeps the pool.** The pool's first task resumed at an answer `a` its entry accepts
(the answer's resource `σ` holding nothing of the pool's lends), under frames avoiding its mask,
the rest of the pool beside it: at every end of the run, the rest is a pool at the end world and
list, apart from the run's end. -/
theorem poolT_resume {t : StoredT} {ts : List StoredT} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {ρp σ ρ : TRes w.K} (hP : PoolT (ℍ := ℍ) (t :: ts) w ls O ρp)
    {k' : Nat} (hk : k' < t.k) {a : Val} (hB : t.en.PBv t.v k' w ls a σ)
    (hc : ResUT.CompS ρp σ ρ) (hσ : NoneAt (recMask O) σ) (hcov : CovR (sem w.Θ) w.K ρ)
    (hv : ResUT.Valid ρ) {F : TFrame} (hFM : ∀ w' ρf, F w' ρf → fdMask t.M w' ρf) :
    twp (ℍ := ℍ) F (fun k₁ w' ls' O' e ρ' => ∃ (Oa Ob : List (FrameRecT w'.K)) (a b : TRes w'.K),
      O' = Oa ++ Ob ∧ ResUT.CompS a b ρ' ∧ valPost t.Q k₁ w' ls' Oa e a ∧
        PoolT (ℍ := ℍ) ts w' ls' Ob b ∧ NoneAt (recMask Oa) b ∧ NoneAt (recMask Ob) a)
      k' w ls O (.app (.app t.κ.1 (.val (Val.inj₁ .unit))) (.val a)) ρ := by
  obtain ⟨Ot, Os, ρt, ρs, rfl, hcp, hκ, hM, hPs, hb, ha, hap⟩ := hP
  obtain ⟨σ', hσ₁, hσ₂⟩ := (ResUT.CompS.assoc ρs ρt σ ρ).mpr ⟨ρp, ResUT.CompS.comm hcp, hc⟩
  have hσ₂' := ResUT.CompS.comm hσ₂
  have hvσ' := (ResUT.Valid.split hσ₂' hv).1
  have hvs := (ResUT.Valid.split hσ₂' hv).2
  have hvt := ResUT.Valid.split hσ₁ hvσ'
  have h := cerwpTE_iff.mp (hκ.resume hk hB hσ₁ (fdMask_mono t.M) (fun _ _ h => h))
  exact twp_keepsPool hσ₂' hcov hv hap hb
    (NoneAt.compS hσ₁ hvt.1 hvt.2 ha (hσ.mono fun x hx => recMask_append_right hx))
    (pool_frame hFM hM hvs hb) h hPs

/-- **A cancel keeps the pool.** The pool's first task, at a cancellable entry, its cancel branch
run under its scheduler (`hnd H (κ (inj₂ ()))`), under frames avoiding its mask, the rest of the
pool beside it: at every end of the run (the unwinding finished, or stopped at an operation of the
scheduler's and handed back), the rest is a pool at the end world and list, apart from the run's
end. -/
theorem poolT_cancel {t : StoredT} {ts : List StoredT} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {ρ : TRes w.K} (hP : PoolT (ℍ := ℍ) (t :: ts) w ls O ρ)
    (hq : t.en.q ≠ .lin) (hf : t.en.fin = true) {k' : Nat} (hk : k' < t.k)
    (hcov : CovR (sem w.Θ) w.K ρ) (hv : ResUT.Valid ρ) {F : TFrame}
    (hFM : ∀ w' ρf, F w' ρf → fdMask t.M w' ρf) :
    twp (ℍ := ℍ) F (fun k₁ w' ls' O' e ρ' => ∃ (Oa Ob : List (FrameRecT w'.K)) (a b : TRes w'.K),
      O' = Oa ++ Ob ∧ ResUT.CompS a b ρ' ∧ valPost t.Q k₁ w' ls' Oa e a ∧
        PoolT (ℍ := ℍ) ts w' ls' Ob b ∧ NoneAt (recMask Oa) b ∧ NoneAt (recMask Ob) a)
      k' w ls O (hndE t.H (.app t.κ.1 (.val (Val.inj₂ .unit)))) ρ := by
  obtain ⟨Ot, Os, ρt, ρs, rfl, hcp, hκ, hM, hPs, hb, ha, hap⟩ := hP
  have hvs := (ResUT.Valid.split hcp hv).2
  have h := cerwpTE_iff.mp (hκ.cancel hq hf hk (fdMask_mono t.M) (fun _ _ h => h))
  exact twp_keepsPool hcp hcov hv hap hb ha (pool_frame hFM hM hvs hb) h hPs

end BoCa.Fig16.Tree.Wp

end
