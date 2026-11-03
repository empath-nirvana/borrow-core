import Core.TreeSchedPool
import Core.TreeHeadlines

/-!
# Pool-scheduler adequacy: a scheduler handler that keeps its stored tasks as a pool  `[spec §62]`

**The guarantee** (`PoolSchedAdequacyT`, `poolSchedAdequacyT`). A closed program `(hnd H e₀) s₀`,
`H = hndVal n₀ qs hr hs` a scheduler meeting `SchedOKT` whose answers are functions of its
state (`PoolAns`), `s₀` the empty pool and `e₀` a task verified at `cerwpT` at the scheduler's
table at frame conditions every valid frame meets, is safe or diverges: every configuration it
reaches steps or is a value, a value is reached only at the empty memory, and every `free` finds
its cell.

**The scheduler's state is a pool.** The state is a list value of stored continuations
(`poolVal`); its resource is a pool (`PoolT`): each task held at the present world, each apart from
the others at the masks of their records. A scheduler answer `f` (a clause's or the return
clause's) is in `PoolAns Q H Inv` when, applied to any pool of any length whose tasks run under `H`,
answer in `PoolAns` again (`GoodT`), and that meets the scheduler's own invariant `Inv`, beside
`f`'s own resource and apart from it, it answers the program's `Q` under every frame condition whose
frames avoid all their records. The state value is the scheduler's handler with the pool
(`stateVal`), so a clause can run a task under its own handler (a new task, or a stored task's
cancel branch) without naming itself. Nothing fixes which task the scheduler runs next, whether it
resumes or cancels it, how many it holds, or what lends they hold; `Inv` is the scheduler's own
condition on its pool (for instance, which entries its tasks stopped at, or their order).

**What the scheduler must satisfy** is `SchedOKT` at `Qout = PoolAns Q H Inv`: the return clause
and each operation's clause answer such a function. A clause proves it by the pool's moves, each a
preservation lemma: run a task under the scheduler beside the pool (`poolAns_run`, from
`twp_keepsPool`), park the stopped task (`poolAns_park`, from `poolT_park`), resume a stored task
and hand the rest of the pool to what it answers (`poolAns_resume`, from `poolT_resume` and
`twp_keepsPool`), or cancel one the same way (`poolAns_cancel`, from `poolT_cancel`). A task
resumed or cancelled runs at its base frame condition and its resumer's guarantee at that resume
(`cerwpT`'s base frame condition), so it may open and end lends of its own, those open when it
parked included.

**How it is proved.** `[handle]` for the scheduler (`cerwpT_schedHandle`, by induction on the index)
gives the handled task's answer in `PoolAns`; applying it to the empty pool (`poolT_nil`, `Inv []`) answers
`Q`; `topAdequacyT` closes the program.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont hndE hndVal)

/-- **The scheduler's state**: the stored tasks' continuations as a list value,
`inj₁ (κ, rest)` or `inj₂ ()`. -/
def poolVal : List StoredT → Val
  | [] => Val.inj₂ Val.unit
  | t :: ts => Val.inj₁ (Val.pair t.κ (poolVal ts))

/-- **The scheduler's state**: its own handler value, so a clause can run a task under it (a new
task, or a stored task's cancel branch) without naming itself, and its pool. -/
def stateVal (H : Val) (ts : List StoredT) : Val := Val.pair H (poolVal ts)

/-- **A scheduler answer at index `k`** (`PoolAns` closes it downward): `f` applied to any pool
meeting `Inv` whose tasks are good at `k` (run under `H`, held at index at least `k`, and answer
in `PoolAns` below `k`), beside `f`'s resource and apart from it, answers `Q` under every frame
condition whose frames avoid all their records. -/
def PoolAnsAt (Q : TPostV) (H : Val) (Inv : List StoredT → Prop) : (k : Nat) → (w : TWd) →
    List (SRecT w.K) → List (FrameRecT w.K) → Val → TRes w.K → Prop
  | k, w, ls, O, f, ρ =>
    ∀ (ts : List StoredT) (Os : List (FrameRecT w.K)) (σ ρ' : TRes w.K),
      Inv ts → (∀ t ∈ ts, t.H = H ∧ k ≤ t.k ∧
        ∀ (j : Nat) (_hj : j < k) (w' : TWd) (ls' : List (SRecT w'.K))
          (O' : List (FrameRecT w'.K)) (v : Val) (ρ'' : TRes w'.K), t.Q j w' ls' O' v ρ'' →
          ∀ (j' : Nat) (_hj' : j' ≤ j), PoolAnsAt Q H Inv j' w' ls' O' v ρ'') →
      PoolT (ℍ := ℍ) ts w ls Os σ → ResUT.CompS ρ σ ρ' → NoneAt (recMask O) σ →
      NoneAt (recMask Os) ρ → (∀ p ∈ O, ∀ q ∈ Os, p.le ≠ q.le) →
      CovR (sem w.Θ) w.K ρ' → ResUT.Valid ρ' → (∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R) →
      (∀ r ∈ O, CovR (sem w.Θ) w.K r.R) →
      ∀ F : TFrame, F.Mono → (∀ w' ρf, F w' ρf → fdMask (recMask (O ++ Os)) w' ρf) →
      twp (ℍ := ℍ) F (valPost Q) k w ls (O ++ Os) (.app f.1 (stateVal H ts).1) ρ'
termination_by k => k

/-- **A scheduler answer**: `PoolAnsAt` at every index up to `k`. -/
def PoolAns (Q : TPostV) (H : Val) (Inv : List StoredT → Prop) : TPostV :=
  fun k w ls O f ρ => ∀ j ≤ k, PoolAnsAt (ℍ := ℍ) Q H Inv j w ls O f ρ

theorem poolAns_down (Q : TPostV) (H : Val) (Inv : List StoredT → Prop) :
    (PoolAns (ℍ := ℍ) Q H Inv).Down :=
  fun _ _ _ _ _ _ h j hj => h j (by omega)

/-- **A stored task good at `k`**: run under `H`, held at index at least `k`, and answering a
scheduler answer at every index below `k`. -/
def GoodT (Q : TPostV) (H : Val) (Inv : List StoredT → Prop) (k : Nat) (t : StoredT) : Prop :=
  t.H = H ∧ k ≤ t.k ∧
    ∀ (j : Nat), j < k → ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (O' : List (FrameRecT w'.K))
      (v : Val) (ρ'' : TRes w'.K), t.Q j w' ls' O' v ρ'' → PoolAns (ℍ := ℍ) Q H Inv j w' ls' O' v ρ''

theorem GoodT.le {Q : TPostV} {H : Val} {Inv : List StoredT → Prop} {k k' : Nat} {t : StoredT}
    (h : GoodT (ℍ := ℍ) Q H Inv k t) (hk : k' ≤ k) : GoodT (ℍ := ℍ) Q H Inv k' t :=
  ⟨h.1, by have := h.2.1; omega, fun j hj => h.2.2 j (by omega)⟩

theorem poolAnsAt_iff {Q : TPostV} {H : Val} {Inv : List StoredT → Prop} {k : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {f : Val} {ρ : TRes w.K} :
    PoolAnsAt (ℍ := ℍ) Q H Inv k w ls O f ρ ↔
      ∀ (ts : List StoredT) (Os : List (FrameRecT w.K)) (σ ρ' : TRes w.K),
        Inv ts → (∀ t ∈ ts, GoodT (ℍ := ℍ) Q H Inv k t) →
        PoolT (ℍ := ℍ) ts w ls Os σ → ResUT.CompS ρ σ ρ' → NoneAt (recMask O) σ →
        NoneAt (recMask Os) ρ → (∀ p ∈ O, ∀ q ∈ Os, p.le ≠ q.le) →
        CovR (sem w.Θ) w.K ρ' → ResUT.Valid ρ' → (∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R) →
        (∀ r ∈ O, CovR (sem w.Θ) w.K r.R) →
        ∀ F : TFrame, F.Mono → (∀ w' ρf, F w' ρf → fdMask (recMask (O ++ Os)) w' ρf) →
        twp (ℍ := ℍ) F (valPost Q) k w ls (O ++ Os) (.app f.1 (stateVal H ts).1) ρ' := by
  rw [PoolAnsAt]
  constructor
  · intro h ts Os σ ρ' hi hg
    exact h ts Os σ ρ' hi fun t ht => ⟨(hg t ht).1, (hg t ht).2.1,
      fun j hj w' ls' O' v ρ'' hq => (hg t ht).2.2 j hj w' ls' O' v ρ'' hq⟩
  · intro h ts Os σ ρ' hi hg
    exact h ts Os σ ρ' hi fun t ht => ⟨(hg t ht).1, (hg t ht).2.1,
      fun j hj w' ls' O' v ρ'' hq => (hg t ht).2.2 j hj w' ls' O' v ρ'' hq⟩

/-! ### The pool's moves -/

/-- **Park**: the stopped task (`KapSchedT` at the masks of its records, answering a scheduler
answer) joins the pool, good at every index `j` up to its stop's. -/
theorem poolAns_park {Q : TPostV} {H : Val} {Inv : List StoredT → Prop} {en : OpEntT} {k : Nat}
    {v κ : Val} {ts : List StoredT} {w : TWd} {ls : List (SRecT w.K)}
    {Ot Os : List (FrameRecT w.K)} {a b ρ : TRes w.K}
    (hκ : KapSchedT (ℍ := ℍ) (PoolAns (ℍ := ℍ) Q H Inv) (recMask Ot) en H k w ls Ot v κ a)
    {j : Nat} (hj : j ≤ k) (hg : ∀ t ∈ ts, GoodT (ℍ := ℍ) Q H Inv j t)
    (hP : PoolT (ℍ := ℍ) ts w ls Os b) (hc : ResUT.CompS a b ρ)
    (hb : NoneAt (recMask Ot) b) (ha : NoneAt (recMask Os) a)
    (hap : ∀ p ∈ Ot, ∀ q ∈ Os, p.le ≠ q.le) (hcov : CovR (sem w.Θ) w.K a)
    (hls : ∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R) (hO : ∀ r ∈ Ot, CovR (sem w.Θ) w.K r.R) :
    PoolT (ℍ := ℍ) (⟨PoolAns (ℍ := ℍ) Q H Inv, recMask Ot, en, H, k, v, κ⟩ :: ts) w ls
      (Ot ++ Os) ρ ∧
    ∀ t ∈ (⟨PoolAns (ℍ := ℍ) Q H Inv, recMask Ot, en, H, k, v, κ⟩ :: ts : List StoredT),
      GoodT (ℍ := ℍ) Q H Inv j t := by
  refine ⟨poolT_park (t := ⟨_, _, en, H, k, v, κ⟩) hκ (fun _ => Iff.rfl) hP hc hb ha hap hcov
    hls hO, ?_⟩
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact ⟨rfl, hj, fun _ _ _ _ _ _ _ h => h⟩
  · exact hg t ht

/-! ### Reordering the pool -/

/-- A pointwise relation carried along a permutation of its left list. -/
theorem forall₂_perm {α β : Type _} {R : α → β → Prop} {l u : List α} {v : List β}
    (hp : l.Perm u) (h : List.Forall₂ R u v) : ∃ v', List.Forall₂ R l v' ∧ v'.Perm v := by
  induction hp generalizing v with
  | nil => cases h; exact ⟨[], .nil, .nil⟩
  | cons x _ ih =>
      cases h with
      | cons hx t => obtain ⟨v', h', hp'⟩ := ih t; exact ⟨_, .cons hx h', hp'.cons _⟩
  | swap x y l =>
      cases h with
      | cons hx t => cases t with
        | cons hy t' => exact ⟨_, .cons hy (.cons hx t'), .swap _ _ _⟩
  | trans _ _ ih₁ ih₂ =>
      obtain ⟨v₁, h₁, p₁⟩ := ih₂ h
      obtain ⟨v₂, h₂, p₂⟩ := ih₁ h₁
      exact ⟨v₂, h₂, p₂.trans p₁⟩

/-- A record list's masks do not depend on its order. -/
theorem recMask_perm {K : WCactus} {O O' : List (FrameRecT K)} (h : O.Perm O') :
    recMask O = recMask O' :=
  funext fun _ => propext ⟨fun ⟨p, hp, hx⟩ => ⟨p, h.mem_iff.mp hp, hx⟩,
    fun ⟨p, hp, hx⟩ => ⟨p, h.mem_iff.mpr hp, hx⟩⟩

/-- **`twp` does not depend on the order of the records the run owns**: it reads them through
their re-readings (pointwise, carried along the permutation), `SplitT` and their masks (both by
membership). -/
theorem twp_perm {F : TFrame} {P : TPost} {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O O' : List (FrameRecT w.K)} (hp : O.Perm O') {e : Expr} {ρ : TRes w.K}
    (h : twp (ℍ := ℍ) F P n w ls O e ρ) : twp (ℍ := ℍ) F P n w ls O' e ρ := by
  intro w₀ ρ₀ ρf fρ ls₀ O₀' ps psF μ hE hr hl hO' hF hh hc hS hR hI hfd j μ' e' hj hrun hfin
  obtain ⟨O₀, hO, hp₀⟩ := forall₂_perm hp hO'
  have hS' : SplitT ps O₀ psF :=
    ⟨fun q => by rw [hS.1 q, hp₀.mem_iff], fun q hq r hr => hS.2 q (hp₀.mem_iff.mp hq) r hr⟩
  have := h w₀ ρ₀ ρf fρ ls₀ O₀ ps psF μ hE hr hl hO hF hh hc hS' hR hI hfd j μ' e' hj hrun hfin
  unfold EndT at this ⊢
  rwa [recMask_perm hp₀] at this

/-- **The pool's first two tasks exchanged**: the same resource, the records permuted. -/
theorem poolT_swap {a b : StoredT} {ts : List StoredT} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {ρ : TRes w.K} (hP : PoolT (ℍ := ℍ) (a :: b :: ts) w ls O ρ)
    (hv : ResUT.Valid ρ) : ∃ O' : List (FrameRecT w.K), O'.Perm O ∧
      PoolT (ℍ := ℍ) (b :: a :: ts) w ls O' ρ := by
  obtain ⟨Oa, Os₁, ra, rs₁, rfl, hc₁, hκa, hMa, hP₁, hb₁, ha₁, hap₁⟩ := hP
  obtain ⟨Ob, Os, rb, rs, rfl, hc₂, hκb, hMb, hPs, hb₂, ha₂, hap₂⟩ := hP₁
  obtain ⟨x, hx₁, hx₂⟩ := (ResUT.CompS.assoc ra rb rs ρ).mp ⟨_, hc₂, hc₁⟩
  obtain ⟨y, hy₁, hy₂⟩ := (ResUT.CompS.assoc rb ra rs ρ).mpr ⟨x, ResUT.CompS.comm hx₁, hx₂⟩
  have hvs₁ := (ResUT.Valid.split hc₁ hv).2
  have hvy := (ResUT.Valid.split hy₂ hv).2
  have hvar := ResUT.Valid.split hy₁ hvy
  refine ⟨Ob ++ (Oa ++ Os), ?_, Ob, Oa ++ Os, rb, y, rfl, hy₂, hκb, hMb,
    ⟨Oa, Os, ra, rs, rfl, hy₁, hκa, hMa, hPs, hb₁.of_compS_right hc₂ hvs₁,
      ha₁.mono fun x hx => (recMask_append x).mpr (Or.inr hx),
      fun p hp q hq => hap₁ p hp q (List.mem_append_right _ hq)⟩,
    NoneAt.compS hy₁ hvar.1 hvar.2 (ha₁.mono fun x hx => (recMask_append x).mpr (Or.inl hx)) hb₂,
    (NoneAt.or (hb₁.of_compS_left hc₂ hvs₁) ha₂).mono fun x hx => (recMask_append x).mp hx,
    fun p hp q hq => ?_⟩
  · rw [← List.append_assoc, ← List.append_assoc]
    exact List.perm_append_comm.append_right _
  · rcases List.mem_append.mp hq with hq | hq
    · exact (hap₁ q hq p (List.mem_append_left _ hp)).symm
    · exact hap₂ p hp q hq

/-- What a stored task answers when resumed or cancelled, handed the rest of the pool: the
continuation from `PoolPost` at a good task, under frames avoiding everything's records. -/
theorem poolAns_handRest {Q : TPostV} {H : Val} {Inv : List StoredT → Prop} {t : StoredT}
    {ts : List StoredT} {k' : Nat} (hg : ∀ u ∈ t :: ts, GoodT (ℍ := ℍ) Q H Inv (k' + 1) u)
    (hi : Inv ts) {F : TFrame} (hFm : F.Mono) :
    ∀ k₁, k₁ ≤ k' → ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (O' : List (FrameRecT w'.K)) t₁
      (ρ' : TRes w'.K), CovR (sem w'.Θ) w'.K ρ' → ResUT.Valid ρ' →
      (∀ x ∈ ls', CovR (sem w'.Θ) w'.K x.1.R) → (∀ r ∈ O', CovR (sem w'.Θ) w'.K r.R) →
      PoolPost (ℍ := ℍ) (valPost t.Q) ts k₁ w' ls' O' t₁ ρ' →
      twp (ℍ := ℍ) (F.and (fdMask (recMask O'))) (valPost Q) k₁ w' ls' O'
        ((Kont.appL .hole (stateVal H ts)).plug t₁) ρ' := by
  intro k₁ hk₁ w' ls' O' t₁ ρ' hcov hv hls hO hpost
  obtain ⟨Oa, Ob, a, b, rfl, hc, ⟨f, rfl, hf⟩, hP, hb, ha, hap⟩ := hpost
  have hfa := (hg t List.mem_cons_self).2.2 k₁ (by omega) w' ls' Oa f a hf
  exact poolAnsAt_iff.mp (hfa k₁ le_rfl) ts Ob b ρ' hi
    (fun u hu => (hg u (List.mem_cons_of_mem _ hu)).le (by omega)) hP hc hb ha hap hcov hv hls
    (fun x hx => hO x (List.mem_append_left _ hx)) _ (TFrame.and_mono hFm (fdMask_mono _))
    (fun _ _ h => h.2)

/-- **Resume**: the pool's first task resumed at an answer `a` its entry accepts (`σ` holding
nothing of the pool's lends), the rest of the pool (meeting `Inv`) handed to what it answers. -/
theorem poolAns_resume {Q : TPostV} {H : Val} {Inv : List StoredT → Prop} {t : StoredT}
    {ts : List StoredT} {k' : Nat} (hg : ∀ u ∈ t :: ts, GoodT (ℍ := ℍ) Q H Inv (k' + 1) u)
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ρp σ ρ : TRes w.K}
    (hP : PoolT (ℍ := ℍ) (t :: ts) w ls O ρp) {a : Val} (hB : t.en.PBv t.v k' w ls a σ)
    (hc : ResUT.CompS ρp σ ρ) (hσ : NoneAt (recMask O) σ) (hcov : CovR (sem w.Θ) w.K ρ)
    (hv : ResUT.Valid ρ) {F : TFrame} (hFm : F.Mono)
    (hFM : ∀ w' ρf, F w' ρf → fdMask (recMask O) w' ρf) (hi : Inv ts) :
    twp (ℍ := ℍ) F (valPost Q) k' w ls O
      (.app (.app (.app t.κ.1 (.val (Val.inj₁ .unit))) (.val a)) (stateVal H ts).1) ρ := by
  obtain ⟨Ot, Os, ρt, ρs, rfl, -, -, hM, -⟩ := id hP
  have hk : k' < t.k := by have := (hg t List.mem_cons_self).2.1; omega
  have h := poolT_resume hP hk hB hc hσ hcov hv (F := F)
    (fun w' ρf hf => fdMask_le (fun x hx => (recMask_append x).mpr (Or.inl ((hM x).mp hx)))
      (hFM w' ρf hf))
  exact twp_bind_fd hFm (fun _ _ h => h) (Kont.appL .hole (stateVal H ts))
    (fun w₀ ρf hf => (hFM w₀ ρf hf).2) h (poolAns_handRest hg hi hFm)

/-- **Resume the second**: the pool's second task resumed at an answer `a` its entry accepts, the
first kept at the head of the rest (`poolT_swap`, `twp_perm`). A park that resumes another task
and keeps the parked one in its place is this move after `poolAns_park`. -/
theorem poolAns_resumeSnd {Q : TPostV} {H : Val} {Inv : List StoredT → Prop} {t u : StoredT}
    {ts : List StoredT} {k' : Nat} (hg : ∀ x ∈ t :: u :: ts, GoodT (ℍ := ℍ) Q H Inv (k' + 1) x)
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ρp σ ρ : TRes w.K}
    (hP : PoolT (ℍ := ℍ) (t :: u :: ts) w ls O ρp) (hvp : ResUT.Valid ρp) {a : Val}
    (hB : u.en.PBv u.v k' w ls a σ) (hc : ResUT.CompS ρp σ ρ) (hσ : NoneAt (recMask O) σ)
    (hcov : CovR (sem w.Θ) w.K ρ) (hv : ResUT.Valid ρ) {F : TFrame} (hFm : F.Mono)
    (hFM : ∀ w' ρf, F w' ρf → fdMask (recMask O) w' ρf) (hi : Inv (t :: ts)) :
    twp (ℍ := ℍ) F (valPost Q) k' w ls O
      (.app (.app (.app u.κ.1 (.val (Val.inj₁ .unit))) (.val a)) (stateVal H (t :: ts)).1) ρ := by
  obtain ⟨O', hp, hP'⟩ := poolT_swap hP hvp
  have hM := recMask_perm hp
  refine twp_perm hp (poolAns_resume (fun x hx => hg x ((List.Perm.swap t u ts).mem_iff.mp hx))
    hP' hB hc (by rw [hM]; exact hσ) hcov hv hFm (by rw [hM]; exact hFM) hi)

/-- **Cancel**: the pool's first task, at a cancellable entry, its cancel branch run under its
scheduler, the rest of the pool handed to what it answers (the unwinding finished, or stopped at
an operation of the scheduler's and parked again by its clause). -/
theorem poolAns_cancel {Q : TPostV} {H : Val} {Inv : List StoredT → Prop} {t : StoredT}
    {ts : List StoredT} {k' : Nat} (hg : ∀ u ∈ t :: ts, GoodT (ℍ := ℍ) Q H Inv (k' + 1) u)
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ρ : TRes w.K}
    (hP : PoolT (ℍ := ℍ) (t :: ts) w ls O ρ) (hq : t.en.q ≠ .lin) (hfin : t.en.fin = true)
    (hcov : CovR (sem w.Θ) w.K ρ) (hv : ResUT.Valid ρ) {F : TFrame} (hFm : F.Mono)
    (hFM : ∀ w' ρf, F w' ρf → fdMask (recMask O) w' ρf) (hi : Inv ts) :
    twp (ℍ := ℍ) F (valPost Q) k' w ls O
      (.app (hndE t.H (.app t.κ.1 (.val (Val.inj₂ .unit)))) (stateVal H ts).1) ρ := by
  obtain ⟨Ot, Os, ρt, ρs, rfl, -, -, hM, -⟩ := id hP
  have hk : k' < t.k := by have := (hg t List.mem_cons_self).2.1; omega
  have h := poolT_cancel hP hq hfin hk hcov hv (F := F)
    (fun w' ρf hf => fdMask_le (fun x hx => (recMask_append x).mpr (Or.inl ((hM x).mp hx)))
      (hFM w' ρf hf))
  exact twp_bind_fd hFm (fun _ _ h => h) (Kont.appL .hole (stateVal H ts))
    (fun w₀ ρf hf => (hFM w₀ ρf hf).2) h (poolAns_handRest hg hi hFm)

/-- **Cancel the second**: the pool's second task, at a cancellable entry, its cancel branch run
under its scheduler, the first kept at the head of the rest (`poolT_swap`, `twp_perm`). A clause
that parks the task it stopped and cancels another is this move after `poolAns_park`. -/
theorem poolAns_cancelSnd {Q : TPostV} {H : Val} {Inv : List StoredT → Prop} {t u : StoredT}
    {ts : List StoredT} {k' : Nat} (hg : ∀ x ∈ t :: u :: ts, GoodT (ℍ := ℍ) Q H Inv (k' + 1) x)
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ρ : TRes w.K}
    (hP : PoolT (ℍ := ℍ) (t :: u :: ts) w ls O ρ) (hq : u.en.q ≠ .lin) (hfin : u.en.fin = true)
    (hcov : CovR (sem w.Θ) w.K ρ) (hv : ResUT.Valid ρ) {F : TFrame} (hFm : F.Mono)
    (hFM : ∀ w' ρf, F w' ρf → fdMask (recMask O) w' ρf) (hi : Inv (t :: ts)) :
    twp (ℍ := ℍ) F (valPost Q) k' w ls O
      (.app (hndE u.H (.app u.κ.1 (.val (Val.inj₂ .unit)))) (stateVal H (t :: ts)).1) ρ := by
  obtain ⟨O', hp, hP'⟩ := poolT_swap hP hv
  have hM := recMask_perm hp
  exact twp_perm hp (poolAns_cancel (fun x hx => hg x ((List.Perm.swap t u ts).mem_iff.mp hx))
    hP' hq hfin hcov hv hFm (by rw [hM]; exact hFM) hi)

/-- **Run, at a scheduler meeting its clauses up to `N`**: a task `e` (at `cerwpT` at the scheduler's table, owning `Or`, at a base frame
condition every valid frame meets and a present one met by every frame avoiding its records) run
under the scheduler beside the pool, the state handed to what it answers. The pool is kept across
the run (`twp_keepsPool`): the task may open lends, end lends of its own, allocate and free. A
spawn clause at a stop `k` runs its child at an index below `k`, from `SchedOKTLe` below `k`. -/
theorem poolAns_run_le {N : Nat} {T : OpTabT} {n₀ : UInt32} {qs hr hs : Val} {Qin Q : TPostV}
    {Inv : List StoredT → Prop}
    (hS : SchedOKTLe (ℍ := ℍ) N T n₀ qs hr hs Qin (PoolAns (ℍ := ℍ) Q (hndVal n₀ qs hr hs) Inv))
    {ts : List StoredT} {k : Nat} (hkN : k ≤ N)
    (hg : ∀ u ∈ ts, GoodT (ℍ := ℍ) Q (hndVal n₀ qs hr hs) Inv k u) (hi : Inv ts)
    {w : TWd} {ls : List (SRecT w.K)} {Or Op : List (FrameRecT w.K)} {e : Expr}
    {ρ₁ ρp ρ : TRes w.K} (hP : PoolT (ℍ := ℍ) ts w ls Op ρp) (hcρ : ResUT.CompS ρ₁ ρp ρ)
    (hcov : CovR (sem w.Θ) w.K ρ) (hv : ResUT.Valid ρ) (hap : ∀ p ∈ Or, ∀ q ∈ Op, p.le ≠ q.le)
    (hesc₁ : NoneAt (recMask Or) ρp) (hesc₂ : NoneAt (recMask Op) ρ₁) {Fb Fe : TFrame}
    (hFb : ∀ w ρf, ResUT.Valid ρf → Fb w ρf) (hFe : ∀ w ρf, fdMask (recMask Or) w ρf → Fe w ρf)
    (he : cerwpT (ℍ := ℍ) (opTableT T) Qin Fb Fe k w ls Or e ρ₁) {F : TFrame} (hFm : F.Mono)
    (hFM : ∀ w' ρf, F w' ρf → fdMask (recMask (Or ++ Op)) w' ρf) :
    twp (ℍ := ℍ) F (valPost Q) k w ls (Or ++ Op)
      (.app (hndE (hndVal n₀ qs hr hs) e) (stateVal (hndVal n₀ qs hr hs) ts).1) ρ := by
  have hvp := (ResUT.Valid.split hcρ hv).2
  have h₁ := cerwpT_schedHandle_le hS k hkN (recMask Or) (fdMask (recMask Or)) Fb Fe w ls Or e ρ₁
    (fdMask_mono _) (fun _ _ h => h) (fun _ h => h) hFb hFe he
  have h₂ := twp_keepsPool hcρ hcov hv hap hesc₁ hesc₂
    (pool_frame (M := recMask Or) (F := F)
      (fun w ρf hf => fdMask_le (fun x hx => (recMask_append x).mpr (_root_.Or.inl hx)) (hFM w ρf hf))
      (fun _ => Iff.rfl) hvp hesc₁) h₁ hP
  refine twp_bind_fd hFm (fun _ _ h => h) (Kont.appL .hole (stateVal (hndVal n₀ qs hr hs) ts))
    (fun w₀ ρf hf => (hFM w₀ ρf hf).2) h₂ ?_
  intro k₁ hk₁ w' ls' O' t₁ ρ' hcov' hv' hls' hO' hpost
  obtain ⟨Oa, Ob, a, b, rfl, hc, ⟨f, rfl, hf⟩, hP', hb, ha, hap'⟩ := hpost
  exact poolAnsAt_iff.mp (hf k₁ le_rfl) ts Ob b ρ' hi (fun u hu => (hg u hu).le hk₁) hP' hc hb ha
    hap' hcov' hv' hls' (fun x hx => hO' x (List.mem_append_left _ hx)) _
    (TFrame.and_mono hFm (fdMask_mono _)) (fun _ _ h => h.2)

/-- **Run**: a task `e` (at `cerwpT` at the scheduler's table, owning `Or`, at a base frame
condition every valid frame meets and a present one met by every frame avoiding its records) run
under the scheduler beside the pool, the state handed to what it answers. The pool is kept across
the run (`twp_keepsPool`): the task may open lends, end lends of its own, allocate and free. -/
theorem poolAns_run {T : OpTabT} {n₀ : UInt32} {qs hr hs : Val} {Qin Q : TPostV}
    {Inv : List StoredT → Prop}
    (hS : SchedOKT (ℍ := ℍ) T n₀ qs hr hs Qin (PoolAns (ℍ := ℍ) Q (hndVal n₀ qs hr hs) Inv))
    {ts : List StoredT} {k : Nat}
    (hg : ∀ u ∈ ts, GoodT (ℍ := ℍ) Q (hndVal n₀ qs hr hs) Inv k u) (hi : Inv ts)
    {w : TWd} {ls : List (SRecT w.K)} {Or Op : List (FrameRecT w.K)} {e : Expr}
    {ρ₁ ρp ρ : TRes w.K} (hP : PoolT (ℍ := ℍ) ts w ls Op ρp) (hcρ : ResUT.CompS ρ₁ ρp ρ)
    (hcov : CovR (sem w.Θ) w.K ρ) (hv : ResUT.Valid ρ) (hap : ∀ p ∈ Or, ∀ q ∈ Op, p.le ≠ q.le)
    (hesc₁ : NoneAt (recMask Or) ρp) (hesc₂ : NoneAt (recMask Op) ρ₁) {Fb Fe : TFrame}
    (hFb : ∀ w ρf, ResUT.Valid ρf → Fb w ρf) (hFe : ∀ w ρf, fdMask (recMask Or) w ρf → Fe w ρf)
    (he : cerwpT (ℍ := ℍ) (opTableT T) Qin Fb Fe k w ls Or e ρ₁) {F : TFrame} (hFm : F.Mono)
    (hFM : ∀ w' ρf, F w' ρf → fdMask (recMask (Or ++ Op)) w' ρf) :
    twp (ℍ := ℍ) F (valPost Q) k w ls (Or ++ Op)
      (.app (hndE (hndVal n₀ qs hr hs) e) (stateVal (hndVal n₀ qs hr hs) ts).1) ρ :=
  poolAns_run_le (hS.le k) le_rfl hg hi hP hcρ hcov hv hap hesc₁ hesc₂ hFb hFe he hFm hFM

/-! ### The headline -/

/-- **Pool-scheduler adequacy.** A closed program `(hnd H e₀) s₀`, `s₀` the empty pool: the task
`e₀` at `cerwpT` at the scheduler's table `T`, from the empty world at any tree, at a base frame
condition `Fb` and a present one `Fe` every valid frame meets; the scheduler
`H = hndVal n₀ qs hr hs` meeting `SchedOKT` with its answers functions of its state
(`PoolAns Q H Inv`, for any invariant `Inv` of its pool the empty pool meets); the program's
answers holding nothing. -/
def PoolSchedAdequacyT : Prop :=
  ∀ (P : ParentFn) (T : OpTabT) (n₀ : UInt32) (qs hr hs : Val) (Qin Q : TPostV)
    (Inv : List StoredT → Prop) (Fb Fe : TFrame) (e₀ : Expr),
    (∀ k w ls O v ρ, Q k w ls O v ρ → ρ = PMap.empty) → Inv [] →
    SchedOKT (ℍ := ℍ) T n₀ qs hr hs Qin (PoolAns (ℍ := ℍ) Q (hndVal n₀ qs hr hs) Inv) →
    (∀ w ρf, ResUT.Valid ρf → Fb w ρf) → (∀ w ρf, fdMask (fun _ => False) w ρf → Fe w ρf) →
    (∀ n, cerwpT (ℍ := ℍ) (opTableT T) Qin Fb Fe n (w₀ P) [] [] e₀
      (PMap.empty : TRes (WCactus.ofParent P))) →
    OrDiverges (ℍ := ℍ) (.app (hndE (hndVal n₀ qs hr hs) e₀) (stateVal (hndVal n₀ qs hr hs) []).1)

/-- **The scheduled program applied to the empty pool at `twp`**, under frames that are empty. -/
theorem poolSched_twp {T : OpTabT} {n₀ : UInt32} {qs hr hs : Val} {Qin Q : TPostV}
    {Inv : List StoredT → Prop} {Fb Fe : TFrame} {e₀ : Expr}
    (hInv : Inv []) (hS : SchedOKT (ℍ := ℍ) T n₀ qs hr hs Qin (PoolAns (ℍ := ℍ) Q (hndVal n₀ qs hr hs) Inv))
    (hFb : ∀ w ρf, ResUT.Valid ρf → Fb w ρf) (hFe : ∀ w ρf, fdMask (fun _ => False) w ρf → Fe w ρf)
    {F : TFrame} (hFm : F.Mono) (hF0 : ∀ w ρf, F w ρf → ρf = PMap.empty) {n : Nat} {w : TWd}
    {ρ : TRes w.K} (he : cerwpT (ℍ := ℍ) (opTableT T) Qin Fb Fe n w [] [] e₀ ρ) :
    twp (ℍ := ℍ) F (valPost Q) n w [] []
      (.app (hndE (hndVal n₀ qs hr hs) e₀) (stateVal (hndVal n₀ qs hr hs) []).1) ρ := by
  have hFv : ∀ w ρf, F w ρf → fdMask (fun _ => False) w ρf :=
    fun w ρf h => by rw [hF0 w ρf h]; exact fdMask_empty _ w
  have h := schedProgram_twp hS hFb hFe hFm hFv he
  refine twp_bind_fd hFm (fun _ _ h => h) (Kont.appL .hole (stateVal (hndVal n₀ qs hr hs) []))
    (fun w₀ ρf hf => by rw [hF0 _ _ hf]; exact noneAt_empty _) h ?_
  rintro k _ w' ls' O' t ρ' hcov hv hls hO ⟨f, rfl, hf⟩
  have h₁ := poolAnsAt_iff.mp (hf k le_rfl) [] [] PMap.empty ρ' hInv (fun _ h => by cases h)
    poolT_nil (ResUT.compS_empty_right ρ') (noneAt_empty _)
    (NoneAt.of_false (fun x hx => by simp [recMask] at hx) _) (fun _ _ _ h => by cases h) hcov hv
    hls hO _ (TFrame.and_mono hFm (fdMask_mono _)) (fun _ _ h => by simpa using h.2)
  rw [List.append_nil] at h₁; exact h₁

theorem poolSchedAdequacyT : PoolSchedAdequacyT (ℍ := ℍ) :=
  fun P _ _ _ _ _ _ _ _ _ _ _ hQ hInv hS hFb hFe he => topAdequacyT P _ _ hQ fun n =>
    cerwpTE_iff.mpr (poolSched_twp hInv hS hFb hFe emptyFrame_mono (fun _ _ h => h) (he n))

end BoCa.Fig16.Tree.Wp

end
