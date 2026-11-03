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
clause's) is in `PoolAns Q H Ok` when, applied to any pool of any length whose tasks run under `H`,
meet `Ok` and answer in `PoolAns` again (`GoodT`), beside `f`'s own resource and apart from it, it
answers the program's `Q` under every frame condition whose frames avoid all their records. Nothing
fixes which task the scheduler runs next, whether it resumes or cancels it, how many it holds, or
what lends they hold; `Ok` is the scheduler's own condition on the tasks it stores (for instance,
which entries they stopped at).

**What the scheduler must satisfy** is `SchedOKT` at `Qout = PoolAns Q H Ok`: the return clause
and each operation's clause answer such a function. A clause proves it by the pool's moves, each a
preservation lemma: park the stopped task (`poolAns_park`, from `poolT_park`), resume a stored task
and hand the rest of the pool to what it answers (`poolAns_resume`, from `poolT_resume` and
`twp_keepsPool`), or cancel one the same way (`poolAns_cancel`, from `poolT_cancel`). A task
resumed or cancelled runs at its base frame condition and its resumer's guarantee at that resume
(`cerwpT`'s base frame condition), so it may open and end lends of its own, those open when it
parked included.

**How it is proved.** `[handle]` for the scheduler (`cerwpT_schedHandle`, by induction on the index)
gives the handled task's answer in `PoolAns`; applying it to the empty pool (`poolT_nil`) answers
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

/-- **A scheduler answer at index `k`** (`PoolAns` closes it downward): `f` applied to any pool
whose tasks are good at `k` (run under `H`, meet `Ok`, held at index at least `k`, and answer in
`PoolAns` below `k`), beside `f`'s resource and apart from it, answers `Q` under every frame
condition whose frames avoid all their records. -/
def PoolAnsAt (Q : TPostV) (H : Val) (Ok : StoredT → Prop) : (k : Nat) → (w : TWd) →
    List (SRecT w.K) → List (FrameRecT w.K) → Val → TRes w.K → Prop
  | k, w, ls, O, f, ρ =>
    ∀ (ts : List StoredT) (Os : List (FrameRecT w.K)) (σ ρ' : TRes w.K),
      (∀ t ∈ ts, Ok t ∧ t.H = H ∧ k ≤ t.k ∧
        ∀ (j : Nat) (_hj : j < k) (w' : TWd) (ls' : List (SRecT w'.K))
          (O' : List (FrameRecT w'.K)) (v : Val) (ρ'' : TRes w'.K), t.Q j w' ls' O' v ρ'' →
          ∀ (j' : Nat) (_hj' : j' ≤ j), PoolAnsAt Q H Ok j' w' ls' O' v ρ'') →
      PoolT (ℍ := ℍ) ts w ls Os σ → ResUT.CompS ρ σ ρ' → NoneAt (recMask O) σ →
      NoneAt (recMask Os) ρ → (∀ p ∈ O, ∀ q ∈ Os, p.le ≠ q.le) →
      CovR (sem w.Θ) w.K ρ' → ResUT.Valid ρ' → (∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R) →
      (∀ r ∈ O, CovR (sem w.Θ) w.K r.R) →
      ∀ F : TFrame, F.Mono → (∀ w' ρf, F w' ρf → fdMask (recMask (O ++ Os)) w' ρf) →
      twp (ℍ := ℍ) F (valPost Q) k w ls (O ++ Os) (.app f.1 (poolVal ts).1) ρ'
termination_by k => k

/-- **A scheduler answer**: `PoolAnsAt` at every index up to `k`. -/
def PoolAns (Q : TPostV) (H : Val) (Ok : StoredT → Prop) : TPostV :=
  fun k w ls O f ρ => ∀ j ≤ k, PoolAnsAt (ℍ := ℍ) Q H Ok j w ls O f ρ

theorem poolAns_down (Q : TPostV) (H : Val) (Ok : StoredT → Prop) :
    (PoolAns (ℍ := ℍ) Q H Ok).Down :=
  fun _ _ _ _ _ _ h j hj => h j (by omega)

/-- **A stored task good at `k`**: run under `H`, meeting `Ok`, held at index at least `k`, and
answering a scheduler answer at every index below `k`. -/
def GoodT (Q : TPostV) (H : Val) (Ok : StoredT → Prop) (k : Nat) (t : StoredT) : Prop :=
  Ok t ∧ t.H = H ∧ k ≤ t.k ∧
    ∀ (j : Nat), j < k → ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (O' : List (FrameRecT w'.K))
      (v : Val) (ρ'' : TRes w'.K), t.Q j w' ls' O' v ρ'' → PoolAns (ℍ := ℍ) Q H Ok j w' ls' O' v ρ''

theorem GoodT.le {Q : TPostV} {H : Val} {Ok : StoredT → Prop} {k k' : Nat} {t : StoredT}
    (h : GoodT (ℍ := ℍ) Q H Ok k t) (hk : k' ≤ k) : GoodT (ℍ := ℍ) Q H Ok k' t :=
  ⟨h.1, h.2.1, by have := h.2.2.1; omega, fun j hj => h.2.2.2 j (by omega)⟩

theorem poolAnsAt_iff {Q : TPostV} {H : Val} {Ok : StoredT → Prop} {k : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {f : Val} {ρ : TRes w.K} :
    PoolAnsAt (ℍ := ℍ) Q H Ok k w ls O f ρ ↔
      ∀ (ts : List StoredT) (Os : List (FrameRecT w.K)) (σ ρ' : TRes w.K),
        (∀ t ∈ ts, GoodT (ℍ := ℍ) Q H Ok k t) →
        PoolT (ℍ := ℍ) ts w ls Os σ → ResUT.CompS ρ σ ρ' → NoneAt (recMask O) σ →
        NoneAt (recMask Os) ρ → (∀ p ∈ O, ∀ q ∈ Os, p.le ≠ q.le) →
        CovR (sem w.Θ) w.K ρ' → ResUT.Valid ρ' → (∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R) →
        (∀ r ∈ O, CovR (sem w.Θ) w.K r.R) →
        ∀ F : TFrame, F.Mono → (∀ w' ρf, F w' ρf → fdMask (recMask (O ++ Os)) w' ρf) →
        twp (ℍ := ℍ) F (valPost Q) k w ls (O ++ Os) (.app f.1 (poolVal ts).1) ρ' := by
  rw [PoolAnsAt]
  constructor
  · intro h ts Os σ ρ' hg
    exact h ts Os σ ρ' fun t ht => ⟨(hg t ht).1, (hg t ht).2.1, (hg t ht).2.2.1,
      fun j hj w' ls' O' v ρ'' hq => (hg t ht).2.2.2 j hj w' ls' O' v ρ'' hq⟩
  · intro h ts Os σ ρ' hg
    exact h ts Os σ ρ' fun t ht => ⟨(hg t ht).1, (hg t ht).2.1, (hg t ht).2.2.1,
      fun j hj w' ls' O' v ρ'' hq => (hg t ht).2.2.2 j hj w' ls' O' v ρ'' hq⟩

/-! ### The pool's moves -/

/-- **Park**: the stopped task (`KapSchedT` at the masks of its records, answering a scheduler
answer) joins the pool, good at its stop's index when the scheduler's `Ok` admits it. -/
theorem poolAns_park {Q : TPostV} {H : Val} {Ok : StoredT → Prop} {en : OpEntT} {k : Nat}
    {v κ : Val} {ts : List StoredT} {w : TWd} {ls : List (SRecT w.K)}
    {Ot Os : List (FrameRecT w.K)} {a b ρ : TRes w.K}
    (hκ : KapSchedT (ℍ := ℍ) (PoolAns (ℍ := ℍ) Q H Ok) (recMask Ot) en H k w ls Ot v κ a)
    (hok : Ok ⟨PoolAns (ℍ := ℍ) Q H Ok, recMask Ot, en, H, k, v, κ⟩)
    (hg : ∀ t ∈ ts, GoodT (ℍ := ℍ) Q H Ok k t)
    (hP : PoolT (ℍ := ℍ) ts w ls Os b) (hc : ResUT.CompS a b ρ)
    (hb : NoneAt (recMask Ot) b) (ha : NoneAt (recMask Os) a)
    (hap : ∀ p ∈ Ot, ∀ q ∈ Os, p.le ≠ q.le) (hcov : CovR (sem w.Θ) w.K a)
    (hls : ∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R) (hO : ∀ r ∈ Ot, CovR (sem w.Θ) w.K r.R) :
    PoolT (ℍ := ℍ) (⟨PoolAns (ℍ := ℍ) Q H Ok, recMask Ot, en, H, k, v, κ⟩ :: ts) w ls
      (Ot ++ Os) ρ ∧
    ∀ t ∈ (⟨PoolAns (ℍ := ℍ) Q H Ok, recMask Ot, en, H, k, v, κ⟩ :: ts : List StoredT),
      GoodT (ℍ := ℍ) Q H Ok k t := by
  refine ⟨poolT_park (t := ⟨_, _, en, H, k, v, κ⟩) hκ (fun _ => Iff.rfl) hP hc hb ha hap hcov
    hls hO, ?_⟩
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact ⟨hok, rfl, le_refl _, fun _ _ _ _ _ _ _ h => h⟩
  · exact hg t ht

/-- What a stored task answers when resumed or cancelled, handed the rest of the pool: the
continuation from `PoolPost` at a good task, under frames avoiding everything's records. -/
theorem poolAns_handRest {Q : TPostV} {H : Val} {Ok : StoredT → Prop} {t : StoredT}
    {ts : List StoredT} {k' : Nat} (hg : ∀ u ∈ t :: ts, GoodT (ℍ := ℍ) Q H Ok (k' + 1) u)
    {F : TFrame} (hFm : F.Mono) :
    ∀ k₁, k₁ ≤ k' → ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (O' : List (FrameRecT w'.K)) t₁
      (ρ' : TRes w'.K), CovR (sem w'.Θ) w'.K ρ' → ResUT.Valid ρ' →
      (∀ x ∈ ls', CovR (sem w'.Θ) w'.K x.1.R) → (∀ r ∈ O', CovR (sem w'.Θ) w'.K r.R) →
      PoolPost (ℍ := ℍ) (valPost t.Q) ts k₁ w' ls' O' t₁ ρ' →
      twp (ℍ := ℍ) (F.and (fdMask (recMask O'))) (valPost Q) k₁ w' ls' O'
        ((Kont.appL .hole (poolVal ts)).plug t₁) ρ' := by
  intro k₁ hk₁ w' ls' O' t₁ ρ' hcov hv hls hO hpost
  obtain ⟨Oa, Ob, a, b, rfl, hc, ⟨f, rfl, hf⟩, hP, hb, ha, hap⟩ := hpost
  have hfa := (hg t List.mem_cons_self).2.2.2 k₁ (by omega) w' ls' Oa f a hf
  exact poolAnsAt_iff.mp (hfa k₁ le_rfl) ts Ob b ρ'
    (fun u hu => (hg u (List.mem_cons_of_mem _ hu)).le (by omega)) hP hc hb ha hap hcov hv hls
    (fun x hx => hO x (List.mem_append_left _ hx)) _ (TFrame.and_mono hFm (fdMask_mono _))
    (fun _ _ h => h.2)

/-- **Resume**: the pool's first task resumed at an answer `a` its entry accepts (`σ` holding
nothing of the pool's lends), the rest of the pool handed to what it answers. -/
theorem poolAns_resume {Q : TPostV} {H : Val} {Ok : StoredT → Prop} {t : StoredT}
    {ts : List StoredT} {k' : Nat} (hg : ∀ u ∈ t :: ts, GoodT (ℍ := ℍ) Q H Ok (k' + 1) u)
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ρp σ ρ : TRes w.K}
    (hP : PoolT (ℍ := ℍ) (t :: ts) w ls O ρp) {a : Val} (hB : t.en.PBv t.v k' w ls a σ)
    (hc : ResUT.CompS ρp σ ρ) (hσ : NoneAt (recMask O) σ) (hcov : CovR (sem w.Θ) w.K ρ)
    (hv : ResUT.Valid ρ) {F : TFrame} (hFm : F.Mono)
    (hFM : ∀ w' ρf, F w' ρf → fdMask (recMask O) w' ρf) :
    twp (ℍ := ℍ) F (valPost Q) k' w ls O
      (.app (.app (.app t.κ.1 (.val (Val.inj₁ .unit))) (.val a)) (poolVal ts).1) ρ := by
  obtain ⟨Ot, Os, ρt, ρs, rfl, -, -, hM, -⟩ := id hP
  have hk : k' < t.k := by have := (hg t List.mem_cons_self).2.2.1; omega
  have h := poolT_resume hP hk hB hc hσ hcov hv (F := F)
    (fun w' ρf hf => fdMask_le (fun x hx => (recMask_append x).mpr (Or.inl ((hM x).mp hx)))
      (hFM w' ρf hf))
  exact twp_bind_fd hFm (fun _ _ h => h) (Kont.appL .hole (poolVal ts))
    (fun w₀ ρf hf => (hFM w₀ ρf hf).2) h (poolAns_handRest hg hFm)

/-- **Cancel**: the pool's first task, at a cancellable entry, its cancel branch run under its
scheduler, the rest of the pool handed to what it answers (the unwinding finished, or stopped at
an operation of the scheduler's and parked again by its clause). -/
theorem poolAns_cancel {Q : TPostV} {H : Val} {Ok : StoredT → Prop} {t : StoredT}
    {ts : List StoredT} {k' : Nat} (hg : ∀ u ∈ t :: ts, GoodT (ℍ := ℍ) Q H Ok (k' + 1) u)
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ρ : TRes w.K}
    (hP : PoolT (ℍ := ℍ) (t :: ts) w ls O ρ) (hq : t.en.q ≠ .lin) (hfin : t.en.fin = true)
    (hcov : CovR (sem w.Θ) w.K ρ) (hv : ResUT.Valid ρ) {F : TFrame} (hFm : F.Mono)
    (hFM : ∀ w' ρf, F w' ρf → fdMask (recMask O) w' ρf) :
    twp (ℍ := ℍ) F (valPost Q) k' w ls O
      (.app (hndE t.H (.app t.κ.1 (.val (Val.inj₂ .unit)))) (poolVal ts).1) ρ := by
  obtain ⟨Ot, Os, ρt, ρs, rfl, -, -, hM, -⟩ := id hP
  have hk : k' < t.k := by have := (hg t List.mem_cons_self).2.2.1; omega
  have h := poolT_cancel hP hq hfin hk hcov hv (F := F)
    (fun w' ρf hf => fdMask_le (fun x hx => (recMask_append x).mpr (Or.inl ((hM x).mp hx)))
      (hFM w' ρf hf))
  exact twp_bind_fd hFm (fun _ _ h => h) (Kont.appL .hole (poolVal ts))
    (fun w₀ ρf hf => (hFM w₀ ρf hf).2) h (poolAns_handRest hg hFm)

/-! ### The headline -/

/-- **Pool-scheduler adequacy.** A closed program `(hnd H e₀) s₀`, `s₀` the empty pool: the task
`e₀` at `cerwpT` at the scheduler's table `T`, from the empty world at any tree, at a base frame
condition `Fb` and a present one `Fe` every valid frame meets; the scheduler
`H = hndVal n₀ qs hr hs` meeting `SchedOKT` with its answers functions of its pool
(`PoolAns Q H Ok`, for any condition `Ok` on the tasks it stores); the program's answers holding
nothing. -/
def PoolSchedAdequacyT : Prop :=
  ∀ (P : ParentFn) (T : OpTabT) (n₀ : UInt32) (qs hr hs : Val) (Qin Q : TPostV)
    (Ok : StoredT → Prop) (Fb Fe : TFrame) (e₀ : Expr),
    (∀ k w ls O v ρ, Q k w ls O v ρ → ρ = PMap.empty) →
    SchedOKT (ℍ := ℍ) T n₀ qs hr hs Qin (PoolAns (ℍ := ℍ) Q (hndVal n₀ qs hr hs) Ok) →
    (∀ w ρf, ResUT.Valid ρf → Fb w ρf) → (∀ w ρf, fdMask (fun _ => False) w ρf → Fe w ρf) →
    (∀ n, cerwpT (ℍ := ℍ) (opTableT T) Qin Fb Fe n (w₀ P) [] [] e₀
      (PMap.empty : TRes (WCactus.ofParent P))) →
    OrDiverges (ℍ := ℍ) (.app (hndE (hndVal n₀ qs hr hs) e₀) (poolVal []).1)

/-- **The scheduled program applied to the empty pool at `twp`**, under frames that are empty. -/
theorem poolSched_twp {T : OpTabT} {n₀ : UInt32} {qs hr hs : Val} {Qin Q : TPostV}
    {Ok : StoredT → Prop} {Fb Fe : TFrame} {e₀ : Expr}
    (hS : SchedOKT (ℍ := ℍ) T n₀ qs hr hs Qin (PoolAns (ℍ := ℍ) Q (hndVal n₀ qs hr hs) Ok))
    (hFb : ∀ w ρf, ResUT.Valid ρf → Fb w ρf) (hFe : ∀ w ρf, fdMask (fun _ => False) w ρf → Fe w ρf)
    {F : TFrame} (hFm : F.Mono) (hF0 : ∀ w ρf, F w ρf → ρf = PMap.empty) {n : Nat} {w : TWd}
    {ρ : TRes w.K} (he : cerwpT (ℍ := ℍ) (opTableT T) Qin Fb Fe n w [] [] e₀ ρ) :
    twp (ℍ := ℍ) F (valPost Q) n w [] []
      (.app (hndE (hndVal n₀ qs hr hs) e₀) (poolVal []).1) ρ := by
  have hFv : ∀ w ρf, F w ρf → fdMask (fun _ => False) w ρf :=
    fun w ρf h => by rw [hF0 w ρf h]; exact fdMask_empty _ w
  have h := schedProgram_twp hS hFb hFe hFm hFv he
  refine twp_bind_fd hFm (fun _ _ h => h) (Kont.appL .hole (poolVal []))
    (fun w₀ ρf hf => by rw [hF0 _ _ hf]; exact noneAt_empty _) h ?_
  rintro k _ w' ls' O' t ρ' hcov hv hls hO ⟨f, rfl, hf⟩
  have h₁ := poolAnsAt_iff.mp (hf k le_rfl) [] [] PMap.empty ρ' (fun _ h => by cases h)
    poolT_nil (ResUT.compS_empty_right ρ') (noneAt_empty _)
    (NoneAt.of_false (fun x hx => by simp [recMask] at hx) _) (fun _ _ _ h => by cases h) hcov hv
    hls hO _ (TFrame.and_mono hFm (fdMask_mono _)) (fun _ _ h => by simpa using h.2)
  rw [List.append_nil] at h₁; exact h₁

theorem poolSchedAdequacyT : PoolSchedAdequacyT (ℍ := ℍ) :=
  fun P _ _ _ _ _ _ _ _ _ _ _ hQ hS hFb hFe he => topAdequacyT P _ _ hQ fun n =>
    cerwpTE_iff.mpr (poolSched_twp hS hFb hFe emptyFrame_mono (fun _ _ h => h) (he n))

end BoCa.Fig16.Tree.Wp

end
