import Core.TreePoolShare
import Core.TreeHeadlines
import Core.TreeSchedProgs

/-!
# Pool-scheduler adequacy: a scheduler handler whose invariant covers the running task and its pool  `[spec §62]`

**The guarantee** (`PoolSchedAdequacyT`, `poolSchedAdequacyT`). A closed program `(hnd H e₀) s₀`,
`H = hndVal n₀ qs hr hs` a scheduler meeting `SchedOKT` whose answers are functions of its
state (`PoolAns`), `s₀` the empty pool and `e₀` a task verified at `cerwpT` at the scheduler's
table at frame conditions every valid frame meets, is safe or diverges: every configuration it
reaches steps or is a value, a value is reached only at the empty memory, and every `free` finds
its cell.

**The scheduler's state is a stack of tasks.** The state is a list value of stored entries, each
the scheduler's tag beside a continuation (`poolVal`); its resource is a stack (`PoolTJ`,
`Core/TreePoolShare.lean`). A task above a **joiner** may hold views of what the joiner shares, and
hands them back to it when it ends (`PoolTJ.deposit`); the joiner is resumed with what it has
collected. A scheduler answer `f` (a clause's or the return clause's) is in `PoolAns Q H Inv` when,
applied to any stack of any length whose tasks run under `H`, answer in `PoolAns` again (`GoodT`),
and that meets the scheduler's own invariant `Inv`, it answers the program's `Q` under every frame
condition whose frames avoid all their records, **given the running task's conditions against the
stack**: the stack holds nothing at `f`'s masks; `f`'s resource holds nothing at the masks of the
stack's records not lent at what the nearest joiner shares, and its `imm` cells only at its own
masks or there. The state value is the scheduler's handler with the stack (`stateVal`), so a
clause can run a task under its own handler (a new task, or a stored task's cancel branch)
without naming itself. Nothing fixes which task the scheduler runs next, how many tasks or
joiners it holds, how deep they nest, or what lends they hold; `Inv` is the scheduler's own
condition on its stack (for instance, which entries its tags mark as joiners).

**What the scheduler must satisfy** is `SchedOKT` at `Qout = PoolAns Q H Inv`: the return clause
and each operation's clause answer such a function. A clause proves it by the stack's moves, each a
preservation lemma: run a task under the scheduler beside the stack (`poolAns_run`, from
`twp_keepsPoolJ`), park the stopped task as a ready task or a joiner (`poolAns_park`), resume the
top with what it has collected and hand the rest to what it answers (`poolAns_resume`), resume the
second with the first in its place (`poolAns_resumeSnd`), cancel the top or the second
(`poolAns_cancel`, `poolAns_cancelSnd`), or hand a finished task's copies to the nearest joiner and
resume the top (`poolAns_depositResume`).

**How it is proved.** `[handle]` for the scheduler (`cerwpT_schedHandle`, by induction on the
index) gives the handled task's answer in `PoolAns`, and every run keeps where its `imm` cells sit
(`twp_holdsIn`); applying it to the empty stack (`poolTJ_nil`, `Inv []`) answers `Q`;
`topAdequacyT` closes the program.
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

/-- **The scheduler's state**: the stored entries, each its tag beside its continuation, as a list
value, `inj₁ ((tag, κ), rest)` or `inj₂ ()`. -/
def poolVal : List StoredJ → Val
  | [] => Val.inj₂ Val.unit
  | s :: ss => Val.inj₁ (Val.pair (Val.pair s.tag s.t.κ) (poolVal ss))

/-- **The scheduler's state**: its own handler value, so a clause can run a task under it (a new
task, or a stored task's cancel branch) without naming itself, and its stack. -/
def stateVal (H : Val) (ss : List StoredJ) : Val := Val.pair H (poolVal ss)

/-- **A scheduler answer at index `k`** (`PoolAns` closes it downward): `f` applied to any stack
meeting `Inv` whose tasks are good at `k` (run under `H`, held at index at least `k`, and answer
in `PoolAns` below `k`), with `f`'s resource meeting the running task's conditions against it,
answers `Q` under every frame condition whose frames avoid all their records. -/
def PoolAnsAt (Q : TPostV) (H : Val) (Inv : List StoredJ → Prop) : (k : Nat) → (w : TWd) →
    List (SRecT w.K) → List (FrameRecT w.K) → Val → TRes w.K → Prop
  | k, w, ls, O, f, ρ =>
    ∀ (ts : List StoredJ) (Os : List (FrameRecT w.K)) (σ ρ' : TRes w.K),
      Inv ts → (∀ t ∈ ts, t.t.H = H ∧ k ≤ t.t.k ∧
        ∀ (j : Nat) (_hj : j < k) (w' : TWd) (ls' : List (SRecT w'.K))
          (O' : List (FrameRecT w'.K)) (v : Val) (ρ'' : TRes w'.K), t.t.Q j w' ls' O' v ρ'' →
          ∀ (j' : Nat) (_hj' : j' ≤ j), PoolAnsAt Q H Inv j' w' ls' O' v ρ'') →
      PoolTJ (ℍ := ℍ) ts w ls Os σ → ResUT.CompS ρ σ ρ' → NoneAt (recMask O) σ →
      AvoidUnsh (shTop ts) Os ρ → HoldsIn (shTop ts) O ρ → RecsApart O Os →
      CovR (sem w.Θ) w.K ρ' → ResUT.Valid ρ' → (∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R) →
      (∀ r ∈ O, CovR (sem w.Θ) w.K r.R) →
      ∀ F : TFrame, F.Mono → (∀ w' ρf, F w' ρf → fdMask (recMask (O ++ Os)) w' ρf) →
      twp (ℍ := ℍ) F (valPost Q) k w ls (O ++ Os) (.app f.1 (stateVal H ts).1) ρ'
termination_by k => k

/-- **A scheduler answer**: `PoolAnsAt` at every index up to `k`. -/
def PoolAns (Q : TPostV) (H : Val) (Inv : List StoredJ → Prop) : TPostV :=
  fun k w ls O f ρ => ∀ j ≤ k, PoolAnsAt (ℍ := ℍ) Q H Inv j w ls O f ρ

theorem poolAns_down (Q : TPostV) (H : Val) (Inv : List StoredJ → Prop) :
    (PoolAns (ℍ := ℍ) Q H Inv).Down :=
  fun _ _ _ _ _ _ h j hj => h j (by omega)

/-- **A stored task good at `k`**: run under `H`, held at index at least `k`, and answering a
scheduler answer at every index below `k`. -/
def GoodT (Q : TPostV) (H : Val) (Inv : List StoredJ → Prop) (k : Nat) (t : StoredJ) : Prop :=
  t.t.H = H ∧ k ≤ t.t.k ∧
    ∀ (j : Nat), j < k → ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (O' : List (FrameRecT w'.K))
      (v : Val) (ρ'' : TRes w'.K), t.t.Q j w' ls' O' v ρ'' →
        PoolAns (ℍ := ℍ) Q H Inv j w' ls' O' v ρ''

theorem GoodT.le {Q : TPostV} {H : Val} {Inv : List StoredJ → Prop} {k k' : Nat} {t : StoredJ}
    (h : GoodT (ℍ := ℍ) Q H Inv k t) (hk : k' ≤ k) : GoodT (ℍ := ℍ) Q H Inv k' t :=
  ⟨h.1, by have := h.2.1; omega, fun j hj => h.2.2 j (by omega)⟩

theorem poolAnsAt_iff {Q : TPostV} {H : Val} {Inv : List StoredJ → Prop} {k : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {f : Val} {ρ : TRes w.K} :
    PoolAnsAt (ℍ := ℍ) Q H Inv k w ls O f ρ ↔
      ∀ (ts : List StoredJ) (Os : List (FrameRecT w.K)) (σ ρ' : TRes w.K),
        Inv ts → (∀ t ∈ ts, GoodT (ℍ := ℍ) Q H Inv k t) →
        PoolTJ (ℍ := ℍ) ts w ls Os σ → ResUT.CompS ρ σ ρ' → NoneAt (recMask O) σ →
        AvoidUnsh (shTop ts) Os ρ → HoldsIn (shTop ts) O ρ → RecsApart O Os →
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

/-! ### The stack's moves -/

/-- **Park**: the stopped task (`KapSchedT` at the masks of its records, answering a scheduler
answer) joins the stack at its top, as a ready task (`jn = false`) or a joiner sharing `sh`
(lent locations of its own or shared with it), good at every index `j` up to its stop's. -/
theorem poolAns_park {Q : TPostV} {H : Val} {Inv : List StoredJ → Prop} {en : OpEntT} {k : Nat}
    {v κ : Val} (jn : Bool) (sh : BoCa.Loc → Prop) (tag : Val) {ts : List StoredJ} {w : TWd}
    {ls : List (SRecT w.K)} {Ot Os : List (FrameRecT w.K)} {a b ρ : TRes w.K}
    (hκ : KapSchedT (ℍ := ℍ) (PoolAns (ℍ := ℍ) Q H Inv) (recMask Ot) en H k w ls Ot v κ a)
    {j : Nat} (hj : j ≤ k) (hg : ∀ t ∈ ts, GoodT (ℍ := ℍ) Q H Inv j t)
    (hP : PoolTJ (ℍ := ℍ) ts w ls Os b) (hc : ResUT.CompS a b ρ)
    (hb : NoneAt (recMask Ot) b) (ha : AvoidUnsh (shTop ts) Os a) (hH : HoldsIn (shTop ts) Ot a)
    (hsh : ∀ x, sh x → recMask Ot x ∨ shTop ts x) (hap : RecsApart Ot Os)
    (hcov : CovR (sem w.Θ) w.K a)
    (hls : ∀ x ∈ ls, CovR (sem w.Θ) w.K x.1.R) (hO : ∀ r ∈ Ot, CovR (sem w.Θ) w.K r.R) :
    PoolTJ (ℍ := ℍ) (⟨⟨PoolAns (ℍ := ℍ) Q H Inv, recMask Ot, en, H, k, v, κ⟩, jn, sh, tag⟩ :: ts)
      w ls (Ot ++ Os) ρ ∧
    ∀ t ∈ (⟨⟨PoolAns (ℍ := ℍ) Q H Inv, recMask Ot, en, H, k, v, κ⟩, jn, sh, tag⟩ :: ts :
      List StoredJ), GoodT (ℍ := ℍ) Q H Inv j t := by
  refine ⟨⟨Ot, Os, a, PMap.empty, a, b, rfl, ResUT.compS_empty_right a, hc,
    KapAtT.of_stop hκ hcov hls hO, fun _ => rfl, ViewsT.empty, fun _ => Iff.rfl, hP, hb, ha, hH,
    hsh, hap⟩, ?_⟩
  intro t ht
  rcases List.mem_cons.mp ht with rfl | ht
  · exact ⟨rfl, hj, fun _ _ _ _ _ _ _ h => h⟩
  · exact hg t ht

/-- What a stored task answers when resumed or cancelled, handed the rest of the stack: the
continuation from `PoolPostJ` at a good task, under frames avoiding everything's records. -/
theorem poolAns_handRest {Q : TPostV} {H : Val} {Inv : List StoredJ → Prop} {t : StoredJ}
    {ts : List StoredJ} {k' : Nat} (hg : ∀ u ∈ t :: ts, GoodT (ℍ := ℍ) Q H Inv (k' + 1) u)
    (hi : Inv ts) {F : TFrame} (hFm : F.Mono) :
    ∀ k₁, k₁ ≤ k' → ∀ (w' : TWd) (ls' : List (SRecT w'.K)) (O' : List (FrameRecT w'.K)) t₁
      (ρ' : TRes w'.K), CovR (sem w'.Θ) w'.K ρ' → ResUT.Valid ρ' →
      (∀ x ∈ ls', CovR (sem w'.Θ) w'.K x.1.R) → (∀ r ∈ O', CovR (sem w'.Θ) w'.K r.R) →
      PoolPostJ (ℍ := ℍ) (valPost t.t.Q) ts k₁ w' ls' O' t₁ ρ' →
      twp (ℍ := ℍ) (F.and (fdMask (recMask O'))) (valPost Q) k₁ w' ls' O'
        ((Kont.appL .hole (stateVal H ts)).plug t₁) ρ' := by
  intro k₁ hk₁ w' ls' O' t₁ ρ' hcov hv hls hO hpost
  obtain ⟨Oa, Ob, a, b, rfl, hc, ⟨f, rfl, hf⟩, hP, hb, ha, hH, hap⟩ := hpost
  have hfa := (hg t List.mem_cons_self).2.2 k₁ (by omega) w' ls' Oa f a hf
  exact poolAnsAt_iff.mp (hfa k₁ le_rfl) ts Ob b ρ' hi
    (fun u hu => (hg u (List.mem_cons_of_mem _ hu)).le (by omega)) hP hc hb ha hH hap hcov hv hls
    (fun x hx => hO x (List.mem_append_left _ hx)) _ (TFrame.and_mono hFm (fdMask_mono _))
    (fun _ _ h => h.2)

/-- **Resume the top**: the stack's top task resumed at an answer `a` its entry accepts, with what
it has collected beside the answer's resource `σ`, the rest of the stack (meeting `Inv`) handed to
what it answers. `σ` holds nothing at the masks of the stack's records not lent at what the top's
nearest joiner shares, and its `imm` cells only there. -/
theorem poolAns_resume {Q : TPostV} {H : Val} {Inv : List StoredJ → Prop} {t : StoredJ}
    {ts : List StoredJ} {k' : Nat} (hg : ∀ u ∈ t :: ts, GoodT (ℍ := ℍ) Q H Inv (k' + 1) u)
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ρp σ ρ : TRes w.K}
    (hP : PoolTJ (ℍ := ℍ) (t :: ts) w ls O ρp) {a : Val}
    (hB : ∀ c σ' : TRes w.K, ViewsT c → (t.join = false → c = PMap.empty) → ResUT.CompS c σ σ' →
      t.t.en.PBv t.t.v k' w ls a σ')
    (hc : ResUT.CompS ρp σ ρ) (hσ : AvoidUnsh (shTop (t :: ts)) O σ)
    (hσH : HoldsIn (shTop (t :: ts)) [] σ) (hcov : CovR (sem w.Θ) w.K ρ)
    (hv : ResUT.Valid ρ) {F : TFrame} (hFm : F.Mono)
    (hFM : ∀ w' ρf, F w' ρf → fdMask (recMask O) w' ρf) (hi : Inv ts) :
    twp (ℍ := ℍ) F (valPost Q) k' w ls O
      (.app (.app (.app t.t.κ.1 (.val (Val.inj₁ .unit))) (.val a)) (stateVal H ts).1) ρ := by
  obtain ⟨Ot, Os, -, -, -, -, rfl, -, -, -, -, -, hM, -⟩ := id hP
  have hk : k' < t.t.k := by have := (hg t List.mem_cons_self).2.1; omega
  have h := poolTJ_resume hP hk hB hc hσ hσH hcov hv (F := F)
    (fun w' ρf hf => fdMask_le (fun x hx => (recMask_append x).mpr (Or.inl ((hM x).mp hx)))
      (hFM w' ρf hf))
  exact twp_bind_fd hFm (fun _ _ h => h) (Kont.appL .hole (stateVal H ts))
    (fun w₀ ρf hf => (hFM w₀ ρf hf).2) h (poolAns_handRest hg hi hFm)

/-- **Cancel the top**: the stack's top task, not a joiner, at a cancellable entry, its cancel
branch run under its scheduler, the rest of the stack handed to what it answers (the unwinding
finished, or stopped at an operation of the scheduler's and parked again by its clause). -/
theorem poolAns_cancel {Q : TPostV} {H : Val} {Inv : List StoredJ → Prop} {t : StoredJ}
    {ts : List StoredJ} {k' : Nat} (hg : ∀ u ∈ t :: ts, GoodT (ℍ := ℍ) Q H Inv (k' + 1) u)
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ρ : TRes w.K}
    (hP : PoolTJ (ℍ := ℍ) (t :: ts) w ls O ρ) (hjn : t.join = false) (hq : t.t.en.q ≠ .lin)
    (hfin : t.t.en.fin = true) (hcov : CovR (sem w.Θ) w.K ρ) (hv : ResUT.Valid ρ) {F : TFrame}
    (hFm : F.Mono) (hFM : ∀ w' ρf, F w' ρf → fdMask (recMask O) w' ρf) (hi : Inv ts) :
    twp (ℍ := ℍ) F (valPost Q) k' w ls O
      (.app (hndE t.t.H (.app t.t.κ.1 (.val (Val.inj₂ .unit)))) (stateVal H ts).1) ρ := by
  obtain ⟨Ot, Os, -, -, -, -, rfl, -, -, -, -, -, hM, -⟩ := id hP
  have hk : k' < t.t.k := by have := (hg t List.mem_cons_self).2.1; omega
  have h := poolTJ_cancel hP hjn hq hfin hk hcov hv (F := F)
    (fun w' ρf hf => fdMask_le (fun x hx => (recMask_append x).mpr (Or.inl ((hM x).mp hx)))
      (hFM w' ρf hf))
  exact twp_bind_fd hFm (fun _ _ h => h) (Kont.appL .hole (stateVal H ts))
    (fun w₀ ρf hf => (hFM w₀ ρf hf).2) h (poolAns_handRest hg hi hFm)

/-! ### Reordering the stack -/

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

/-- **Resume the second**: the stack's second task, not a joiner, resumed at an answer `a` its
entry accepts, the first (not a joiner) kept at the top of the rest (`PoolTJ.swap`, `twp_perm`).
A park that resumes another task and keeps the parked one in its place is this move after
`poolAns_park`. -/
theorem poolAns_resumeSnd {Q : TPostV} {H : Val} {Inv : List StoredJ → Prop} {t u : StoredJ}
    {ts : List StoredJ} {k' : Nat} (hg : ∀ x ∈ t :: u :: ts, GoodT (ℍ := ℍ) Q H Inv (k' + 1) x)
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ρp σ ρ : TRes w.K}
    (hP : PoolTJ (ℍ := ℍ) (t :: u :: ts) w ls O ρp) (htj : t.join = false) (huj : u.join = false)
    (hvp : ResUT.Valid ρp) {a : Val} (hB : u.t.en.PBv u.t.v k' w ls a σ)
    (hc : ResUT.CompS ρp σ ρ) (hσ : AvoidUnsh (shTop ts) O σ) (hσH : HoldsIn (shTop ts) [] σ)
    (hcov : CovR (sem w.Θ) w.K ρ) (hv : ResUT.Valid ρ) {F : TFrame} (hFm : F.Mono)
    (hFM : ∀ w' ρf, F w' ρf → fdMask (recMask O) w' ρf) (hi : Inv (t :: ts)) :
    twp (ℍ := ℍ) F (valPost Q) k' w ls O
      (.app (.app (.app u.t.κ.1 (.val (Val.inj₁ .unit))) (.val a)) (stateVal H (t :: ts)).1) ρ := by
  obtain ⟨O', hp, hP'⟩ := PoolTJ.swap hP htj huj hvp
  have hM := recMask_perm hp
  have hsh : ∀ x, shTop (u :: t :: ts) x ↔ shTop ts x := fun x =>
    (shTop_ready huj x).trans (shTop_ready htj x)
  refine twp_perm hp (poolAns_resume (fun x hx => hg x ((List.Perm.swap t u ts).mem_iff.mp hx))
    hP' (fun c σ' _ hcj hcσ => ?_) hc
    ((hσ.sub fun q hq => hp.mem_iff.mp hq).mono fun x hx => (hsh x).mpr hx)
    (hσH.mono fun x hx => (hsh x).mpr hx) hcov hv hFm (by rw [hM]; exact hFM) hi)
  obtain rfl := hcj huj
  rw [SchedProgs.compS_empty_left_eq hcσ]
  exact hB

/-- **Cancel the second**: the stack's second task, not a joiner, at a cancellable entry, its
cancel branch run under its scheduler, the first (not a joiner) kept at the top of the rest
(`PoolTJ.swap`, `twp_perm`). A clause that parks the task it stopped and cancels another is this
move after `poolAns_park`. -/
theorem poolAns_cancelSnd {Q : TPostV} {H : Val} {Inv : List StoredJ → Prop} {t u : StoredJ}
    {ts : List StoredJ} {k' : Nat} (hg : ∀ x ∈ t :: u :: ts, GoodT (ℍ := ℍ) Q H Inv (k' + 1) x)
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ρ : TRes w.K}
    (hP : PoolTJ (ℍ := ℍ) (t :: u :: ts) w ls O ρ) (htj : t.join = false) (huj : u.join = false)
    (hq : u.t.en.q ≠ .lin) (hfin : u.t.en.fin = true) (hcov : CovR (sem w.Θ) w.K ρ)
    (hv : ResUT.Valid ρ) {F : TFrame} (hFm : F.Mono)
    (hFM : ∀ w' ρf, F w' ρf → fdMask (recMask O) w' ρf) (hi : Inv (t :: ts)) :
    twp (ℍ := ℍ) F (valPost Q) k' w ls O
      (.app (hndE u.t.H (.app u.t.κ.1 (.val (Val.inj₂ .unit)))) (stateVal H (t :: ts)).1) ρ := by
  obtain ⟨O', hp, hP'⟩ := PoolTJ.swap hP htj huj hv
  have hM := recMask_perm hp
  exact twp_perm hp (poolAns_cancel (fun x hx => hg x ((List.Perm.swap t u ts).mem_iff.mp hx))
    hP' huj hq hfin hcov hv hFm (by rw [hM]; exact hFM) hi)

/-- **A finished task's copies to the nearest joiner, then resume the top**: the copies `L` the
finished task holds (where the nearest joiner shares, nothing at the stack's other records) join
the nearest joiner's collection (`PoolTJ.deposit`), and the stack's top is resumed at an answer
`a` its entry accepts with what it has collected. When the top is the joiner this is the join: it
is resumed with every copy handed back to it. -/
theorem poolAns_depositResume {Q : TPostV} {H : Val} {Inv : List StoredJ → Prop} {t : StoredJ}
    {ts : List StoredJ} {k' : Nat} (hg : ∀ u ∈ t :: ts, GoodT (ℍ := ℍ) Q H Inv (k' + 1) u)
    {w : TWd} {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {ρp L ρ : TRes w.K}
    (hP : PoolTJ (ℍ := ℍ) (t :: ts) w ls O ρp) (hc : ResUT.CompS ρp L ρ) (hVL : ViewsT L)
    (hHL : HoldsIn (shTop (t :: ts)) [] L) (hAL : AvoidUnsh (shTop (t :: ts)) O L) {a : Val}
    (hB : ∀ c : TRes w.K, ViewsT c → (t.join = false → c = PMap.empty) →
      t.t.en.PBv t.t.v k' w ls a c)
    (hcov : CovR (sem w.Θ) w.K ρ) (hv : ResUT.Valid ρ) {F : TFrame} (hFm : F.Mono)
    (hFM : ∀ w' ρf, F w' ρf → fdMask (recMask O) w' ρf) (hi : Inv ts) :
    twp (ℍ := ℍ) F (valPost Q) k' w ls O
      (.app (.app (.app t.t.κ.1 (.val (Val.inj₁ .unit))) (.val a)) (stateVal H ts).1) ρ := by
  have hP' := PoolTJ.deposit hP hc hv hVL hHL hAL
  refine poolAns_resume hg hP' (fun c σ' hV hj hcσ => ?_) (ResUT.compS_empty_right ρ)
    (AvoidUnsh.empty _ _) (HoldsIn.empty _ _) hcov hv hFm hFM hi
  rw [SchedProgs.compS_empty_right_eq hcσ]
  exact hB c hV hj

/-- **Run, at a scheduler meeting its clauses up to `N`**: a task `e` (at `cerwpT` at the
scheduler's table, owning `Or`, at a base frame condition every valid frame meets and a present
one met by every frame avoiding its records) run under the scheduler beside the stack, with the
running task's conditions against it, the state handed to what it answers. The stack is kept
across the run (`twp_keepsPoolJ`): the task may open lends, end lends of its own, allocate and
free, and hold views of what the nearest joiner shares. A clause at a stop `k` runs a new task
below `k`, from `SchedOKTLe` below `k`. -/
theorem poolAns_run_le {N : Nat} {T : OpTabT} {n₀ : UInt32} {qs hr hs : Val} {Qin Q : TPostV}
    {Inv : List StoredJ → Prop}
    (hS : SchedOKTLe (ℍ := ℍ) N T n₀ qs hr hs Qin (PoolAns (ℍ := ℍ) Q (hndVal n₀ qs hr hs) Inv))
    {ts : List StoredJ} {k : Nat} (hkN : k ≤ N)
    (hg : ∀ u ∈ ts, GoodT (ℍ := ℍ) Q (hndVal n₀ qs hr hs) Inv k u) (hi : Inv ts)
    {w : TWd} {ls : List (SRecT w.K)} {Or Op : List (FrameRecT w.K)} {e : Expr}
    {ρ₁ ρp ρ : TRes w.K} (hP : PoolTJ (ℍ := ℍ) ts w ls Op ρp) (hcρ : ResUT.CompS ρ₁ ρp ρ)
    (hcov : CovR (sem w.Θ) w.K ρ) (hv : ResUT.Valid ρ) (hap : RecsApart Or Op)
    (hesc₁ : NoneAt (recMask Or) ρp) (hesc₂ : AvoidUnsh (shTop ts) Op ρ₁)
    (hA : HoldsIn (shTop ts) Or ρ₁) {Fb Fe : TFrame}
    (hFb : ∀ w ρf, ResUT.Valid ρf → Fb w ρf) (hFe : ∀ w ρf, fdMask (recMask Or) w ρf → Fe w ρf)
    (he : cerwpT (ℍ := ℍ) (opTableT T) Qin Fb Fe k w ls Or e ρ₁) {F : TFrame} (hFm : F.Mono)
    (hFM : ∀ w' ρf, F w' ρf → fdMask (recMask (Or ++ Op)) w' ρf) :
    twp (ℍ := ℍ) F (valPost Q) k w ls (Or ++ Op)
      (.app (hndE (hndVal n₀ qs hr hs) e) (stateVal (hndVal n₀ qs hr hs) ts).1) ρ := by
  have hvp := (ResUT.Valid.split hcρ hv).2
  have h₁ := cerwpT_schedHandle_le hS k hkN (recMask Or) (fdMask (recMask Or)) Fb Fe w ls Or e ρ₁
    (fdMask_mono _) (fun _ _ h => h) (fun _ h => h) hFb hFe he
  have h₂ := twp_keepsPoolJ hcρ hcov hv hap.1 hesc₁ hesc₂ hA
    (pool_frame (M := recMask Or) (F := F)
      (fun w ρf hf => fdMask_le (fun x hx => (recMask_append x).mpr (_root_.Or.inl hx)) (hFM w ρf hf))
      (fun _ => Iff.rfl) hvp hesc₁) h₁ hP
  refine twp_bind_fd hFm (fun _ _ h => h) (Kont.appL .hole (stateVal (hndVal n₀ qs hr hs) ts))
    (fun w₀ ρf hf => (hFM w₀ ρf hf).2) h₂ ?_
  intro k₁ hk₁ w' ls' O' t₁ ρ' hcov' hv' hls' hO' hpost
  obtain ⟨Oa, Ob, a, b, rfl, hc, ⟨f, rfl, hf⟩, hP', hb, ha, hH, hap'⟩ := hpost
  exact poolAnsAt_iff.mp (hf k₁ le_rfl) ts Ob b ρ' hi (fun u hu => (hg u hu).le hk₁) hP' hc hb ha
    hH hap' hcov' hv' hls' (fun x hx => hO' x (List.mem_append_left _ hx)) _
    (TFrame.and_mono hFm (fdMask_mono _)) (fun _ _ h => h.2)

/-- **Run**: `poolAns_run_le` at a scheduler meeting `SchedOKT`. -/
theorem poolAns_run {T : OpTabT} {n₀ : UInt32} {qs hr hs : Val} {Qin Q : TPostV}
    {Inv : List StoredJ → Prop}
    (hS : SchedOKT (ℍ := ℍ) T n₀ qs hr hs Qin (PoolAns (ℍ := ℍ) Q (hndVal n₀ qs hr hs) Inv))
    {ts : List StoredJ} {k : Nat}
    (hg : ∀ u ∈ ts, GoodT (ℍ := ℍ) Q (hndVal n₀ qs hr hs) Inv k u) (hi : Inv ts)
    {w : TWd} {ls : List (SRecT w.K)} {Or Op : List (FrameRecT w.K)} {e : Expr}
    {ρ₁ ρp ρ : TRes w.K} (hP : PoolTJ (ℍ := ℍ) ts w ls Op ρp) (hcρ : ResUT.CompS ρ₁ ρp ρ)
    (hcov : CovR (sem w.Θ) w.K ρ) (hv : ResUT.Valid ρ) (hap : RecsApart Or Op)
    (hesc₁ : NoneAt (recMask Or) ρp) (hesc₂ : AvoidUnsh (shTop ts) Op ρ₁)
    (hA : HoldsIn (shTop ts) Or ρ₁) {Fb Fe : TFrame}
    (hFb : ∀ w ρf, ResUT.Valid ρf → Fb w ρf) (hFe : ∀ w ρf, fdMask (recMask Or) w ρf → Fe w ρf)
    (he : cerwpT (ℍ := ℍ) (opTableT T) Qin Fb Fe k w ls Or e ρ₁) {F : TFrame} (hFm : F.Mono)
    (hFM : ∀ w' ρf, F w' ρf → fdMask (recMask (Or ++ Op)) w' ρf) :
    twp (ℍ := ℍ) F (valPost Q) k w ls (Or ++ Op)
      (.app (hndE (hndVal n₀ qs hr hs) e) (stateVal (hndVal n₀ qs hr hs) ts).1) ρ :=
  poolAns_run_le (hS.le k) le_rfl hg hi hP hcρ hcov hv hap hesc₁ hesc₂ hA hFb hFe he hFm hFM

/-! ### The headline -/

/-- **Pool-scheduler adequacy.** A closed program `(hnd H e₀) s₀`, `s₀` the empty stack: the task
`e₀` at `cerwpT` at the scheduler's table `T`, from the empty world at any tree, at a base frame
condition `Fb` and a present one `Fe` every valid frame meets; the scheduler
`H = hndVal n₀ qs hr hs` meeting `SchedOKT` with its answers functions of its state
(`PoolAns Q H Inv`, for any invariant `Inv` of its stack the empty stack meets); the program's
answers holding nothing. -/
def PoolSchedAdequacyT : Prop :=
  ∀ (P : ParentFn) (T : OpTabT) (n₀ : UInt32) (qs hr hs : Val) (Qin Q : TPostV)
    (Inv : List StoredJ → Prop) (Fb Fe : TFrame) (e₀ : Expr),
    (∀ k w ls O v ρ, Q k w ls O v ρ → ρ = PMap.empty) → Inv [] →
    SchedOKT (ℍ := ℍ) T n₀ qs hr hs Qin (PoolAns (ℍ := ℍ) Q (hndVal n₀ qs hr hs) Inv) →
    (∀ w ρf, ResUT.Valid ρf → Fb w ρf) → (∀ w ρf, fdMask (fun _ => False) w ρf → Fe w ρf) →
    (∀ n, cerwpT (ℍ := ℍ) (opTableT T) Qin Fb Fe n (w₀ P) [] [] e₀
      (PMap.empty : TRes (WCactus.ofParent P))) →
    OrDiverges (ℍ := ℍ) (.app (hndE (hndVal n₀ qs hr hs) e₀) (stateVal (hndVal n₀ qs hr hs) []).1)

/-- **The scheduled program applied to the empty stack at `twp`**, under frames that are empty,
from a resource whose `imm` cells sit nowhere. -/
theorem poolSched_twp {T : OpTabT} {n₀ : UInt32} {qs hr hs : Val} {Qin Q : TPostV}
    {Inv : List StoredJ → Prop} {Fb Fe : TFrame} {e₀ : Expr} (hInv : Inv [])
    (hS : SchedOKT (ℍ := ℍ) T n₀ qs hr hs Qin (PoolAns (ℍ := ℍ) Q (hndVal n₀ qs hr hs) Inv))
    (hFb : ∀ w ρf, ResUT.Valid ρf → Fb w ρf) (hFe : ∀ w ρf, fdMask (fun _ => False) w ρf → Fe w ρf)
    {F : TFrame} (hFm : F.Mono) (hF0 : ∀ w ρf, F w ρf → ρf = PMap.empty) {n : Nat} {w : TWd}
    {ρ : TRes w.K} (hv : ResUT.Valid ρ) (hH : HoldsIn (fun _ => False) [] ρ)
    (he : cerwpT (ℍ := ℍ) (opTableT T) Qin Fb Fe n w [] [] e₀ ρ) :
    twp (ℍ := ℍ) F (valPost Q) n w [] []
      (.app (hndE (hndVal n₀ qs hr hs) e₀) (stateVal (hndVal n₀ qs hr hs) []).1) ρ := by
  have hFv : ∀ w ρf, F w ρf → fdMask (fun _ => False) w ρf :=
    fun w ρf h => by rw [hF0 w ρf h]; exact fdMask_empty _ w
  have h := twp_holdsIn hv hH (schedProgram_twp hS hFb hFe hFm hFv he)
  refine twp_bind_fd hFm (fun _ _ h => h) (Kont.appL .hole (stateVal (hndVal n₀ qs hr hs) []))
    (fun w₀ ρf hf => by rw [hF0 _ _ hf]; exact noneAt_empty _) h ?_
  rintro k _ w' ls' O' t ρ' hcov hv' hls hO ⟨⟨f, rfl, hf⟩, hH'⟩
  have h₁ := poolAnsAt_iff.mp (hf k le_rfl) [] [] PMap.empty ρ' hInv (fun _ h => by cases h)
    poolTJ_nil (ResUT.compS_empty_right ρ') (noneAt_empty _) (fun _ h => by cases h) hH'
    (RecsApart.nil_right _) hcov hv' hls hO _ (TFrame.and_mono hFm (fdMask_mono _))
    (fun _ _ h => by simpa using h.2)
  rw [List.append_nil] at h₁; exact h₁

theorem poolSchedAdequacyT : PoolSchedAdequacyT (ℍ := ℍ) :=
  fun P _ _ _ _ _ _ _ _ _ _ _ hQ hInv hS hFb hFe he => topAdequacyT P _ _ hQ fun n =>
    cerwpTE_iff.mpr (poolSched_twp hInv hS hFb hFe emptyFrame_mono (fun _ _ h => h)
      ⟨_, flat_empty⟩ (HoldsIn.empty _ _) (he n))

end BoCa.Fig16.Tree.Wp

end
