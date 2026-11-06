import Core.Chain.SI.HandleN
import Core.Chain.SI.BindN
import Core.Chain.SI.AntiStopN
import Core.Chain.SI.LoopN

/-!
# Pool-scheduler adequacy over the chain relation  `[spec §62]`

**The guarantee** (`PoolSchedAdequacyN`, `poolSchedAdequacyN`). A closed program `(hnd H e₀) s₀`,
`H = hndVal n₀ qs hr hs` a scheduler meeting `SchedOKN` whose answers are functions of its state
(`PoolAnsN`), `s₀` the empty pool and `e₀` a task at `erwp` at the scheduler's table, is safe or
diverges: every configuration it reaches steps or is a value, a value is reached only at the empty
memory, and every `free` finds its cell.

**The scheduler's state is a list of stored tasks.** The state value is the scheduler's own
handler beside the list (`stateValN`), so a clause can run a task under its handler (a new task,
or a stored task's cancel branch) without naming itself; each stored entry is its tag beside its
continuation (`poolValN`). The pool's resource is the separating conjunction of the entries'
shares (`PoolN`): each a continuation as `erwp_handle` hands it to a clause (`KapRelN`, at the
empty table, answering `t.Q`), at the stop's list, with the entry's world condition holding at
every list with the members of the current one. A run never changes the members of its list
(`EndOKG`), so every list the scheduler's clauses see has the members of the root's.

**A scheduler answer** `f` (a clause's or the return clause's) is in `PoolAnsN Q H Inv` when,
applied to any pool meeting the scheduler's invariant `Inv` whose entries answer in `PoolAnsN`
again below the index they are held at (`GoodN`), beside the pool's resource, it answers the
program's `Q` at the empty table. Nothing fixes how many tasks the scheduler holds, in what order,
or which of them it resumes or cancels; `Inv` is the scheduler's own condition on its list.

**What the scheduler must satisfy** is `SchedOKN` at `Qout = PoolAnsN Q H Inv`: the premises of
`erwp_handle_le` at the empty outer table, each clause getting the stopped task's continuation as
`KapRelN`, its cancel run at the scheduler's own table. A clause proves its case by the pool's
moves: run a task under the scheduler beside the pool (`poolAnsN_run_le`), park the stopped task
(`poolAnsN_park`), resume the top task (`poolAnsN_resume`), cancel it (`poolAnsN_cancel`), or
reorder the entries (`PoolN.perm`, `PoolN.swap`), so any stored task can be brought to the top;
`poolAnsN_resumeSnd` and `poolAnsN_cancelSnd` are the moves at the second entry.

**How it is proved.** `[handle]` for the scheduler (`erwp_handle_le`) gives the handled task's
answer in `PoolAnsN`; the pool is framed beside the handled run (`erwpE_frame`, the outer table
empty, so the run never stops); applying the answer to the state closes the run; applying it to
the empty pool answers `Q`, and `erwp_adequacy` closes the program.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont hndE hndVal clauseAt capTag)

/-! ### The empty outer table -/

/-- The empty table is downward closed. -/
theorem OpTabN.empty_down : OpTabN.empty.Down where
  pa := fun _ _ _ h => by simp [OpTabN.empty] at h
  fin := fun _ _ _ _ h => by simp [OpTabN.empty] at h
  wcl := fun _ _ _ h => by simp [OpTabN.empty] at h

/-- At the empty table a run never stops: what it ends with is a value in its postcondition. -/
theorem erwpPostE_val {Q : PostN} {Ψ : ContN} {k : Nat} {ls : List SRec} {t : Expr} {ρ : WRes}
    (h : erwpPost (opTableN OpTabN.empty) Q Ψ k ls t ρ) : valPostN Q k ls t ρ := by
  rcases h with h | ⟨_, _, _, _, _, h'⟩ | ⟨_, _, _, _, _, h'⟩
  · exact h
  · exact absurd (pure_sep_iff.mp h').1.2.2.1 (by simp [OpTabN.empty])
  · exact absurd (pure_sep_iff.mp h').1.2.2.1 (by simp [OpTabN.empty])

/-- **The frame at the empty table**: a resource beside a run that never stops, read at every
list with the members of the run's, is held beside its end. -/
theorem erwpE_frame {Φ : LocFam} {P : PostN} (R : List SRec → WProp)
    (hR : ∀ ls ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ ρ, R ls ρ → R ls' ρ) {n : Nat}
    {ls : List SRec} {e : Expr} {ρ₁ ρ₂ ρ : WRes} (hc : ResU.CompS ρ₁ ρ₂ ρ)
    (h : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) P n ls e ρ₁) (hR₂ : R ls ρ₂) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) (fun k ls' v => P k ls' v ⋆ R ls') n ls e ρ := by
  rw [erwp_eq] at h ⊢
  have h₁ := rwpG_frame R hR hc (rwpG_mono (fun _ _ _ _ h => erwpPostE_val h) h) hR₂
  refine rwpG_mono (fun k ls' t σ hs => ?_) h₁
  obtain ⟨σ₁, σ₂, hcσ, ⟨v, rfl, hp⟩, hr⟩ := hs
  exact Or.inl ⟨v, rfl, σ₁, σ₂, hcσ, hp, hr⟩

/-- A run at `n` ends at indices up to `n`. -/
theorem erwpE_post_le {Φ : LocFam} {Q : PostN} {n : Nat} {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls e ρ) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) (fun k ls' v ρ' => k ≤ n ∧ Q k ls' v ρ') n ls e ρ :=
  erwp_mono_le n (fun _ hk _ _ _ h => ⟨hk, h⟩)
    (fun k _ ls t Ψ Ψ' ρ hΨ h => opTableN_local _ k ls t Ψ Ψ' ρ hΨ h) n le_rfl ls e ρ h

/-! ### The pool -/

/-- **A stored task**: what its continuation answers when resumed (`Q`), its entry, the table
its cancel run is at, the index and list of its stop, its continuation, and the tag the
scheduler's code stores beside it. -/
structure StoredN where
  Q : PostN
  en : OpEntN
  Tc : Option OpTabN
  k : Nat
  ls : List SRec
  κ : Val
  tag : Val

/-- **The scheduler's stored tasks** as a list value, `inj₁ ((tag, κ), rest)` or `inj₂ ()`. -/
def poolValN : List StoredN → Val
  | [] => Val.inj₂ Val.unit
  | s :: ss => Val.inj₁ (Val.pair (Val.pair s.tag s.κ) (poolValN ss))

/-- **The scheduler's state**: its own handler value beside its stored tasks. -/
def stateValN (H : Val) (ss : List StoredN) : Val := Val.pair H (poolValN ss)

/-- **A stored task's share**, at the current list `ls`: its continuation as a clause receives
it (`KapRelN`, at the empty outer table), and the entry's world condition from the stop's list to
every list with the members of `ls`. -/
def EntryN (Φ : LocFam) (t : StoredN) (ls : List SRec) : WProp := fun ρ =>
  KapRelN (ℍ := ℍ) Φ (opTableN OpTabN.empty) t.Q t.en t.Tc t.k t.ls t.κ ρ ∧
    ∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → t.en.wc t.ls ls' ρ

/-- **The pool**: the separating conjunction of the stored tasks' shares. -/
def PoolN (Φ : LocFam) : List StoredN → List SRec → WProp
  | [], _ => fun ρ => ρ = PMap.empty
  | t :: ts, ls => EntryN (ℍ := ℍ) Φ t ls ⋆ PoolN Φ ts ls

theorem poolN_nil {Φ : LocFam} {ls : List SRec} : PoolN (ℍ := ℍ) Φ [] ls PMap.empty := rfl

/-- The pool reads its list only through the list's members. -/
theorem PoolN.mem {Φ : LocFam} : ∀ {ts : List StoredN} {ls ls' : List SRec},
    (∀ x, x ∈ ls' ↔ x ∈ ls) → ∀ {ρ : WRes}, PoolN (ℍ := ℍ) Φ ts ls ρ → PoolN (ℍ := ℍ) Φ ts ls' ρ
  | [], _, _, _, _, h => h
  | _ :: _, _, _, hm, _, ⟨a, b, hc, ⟨hκ, hw⟩, hb⟩ =>
      ⟨a, b, hc, ⟨hκ, fun l₂ h₂ => hw l₂ fun x => (h₂ x).trans (hm x)⟩, PoolN.mem hm hb⟩

/-- **Exchange the two top entries**: the same resource. -/
theorem PoolN.swap {Φ : LocFam} {t u : StoredN} {ts : List StoredN} {ls : List SRec}
    {ρ : WRes} (h : PoolN (ℍ := ℍ) Φ (t :: u :: ts) ls ρ) :
    PoolN (ℍ := ℍ) Φ (u :: t :: ts) ls ρ := by
  obtain ⟨a, bc, hc, ha, b, c, hbc, hb, hcp⟩ := h
  obtain ⟨ac, hac, hx⟩ := compS_lcomm hbc hc
  exact ⟨b, ac, hx, hb, a, c, hac, ha, hcp⟩

/-- The pool's resource does not depend on the order of its entries. -/
theorem PoolN.perm {Φ : LocFam} {ls : List SRec} {ts ts' : List StoredN} (hp : ts.Perm ts') :
    ∀ {ρ : WRes}, PoolN (ℍ := ℍ) Φ ts ls ρ → PoolN (ℍ := ℍ) Φ ts' ls ρ := by
  induction hp with
  | nil => exact fun h => h
  | cons t _ ih => exact fun ⟨a, b, hc, ha, hb⟩ => ⟨a, b, hc, ha, ih hb⟩
  | swap t u _ => exact fun h => PoolN.swap h
  | trans _ _ ih₁ ih₂ => exact fun h => ih₂ (ih₁ h)

/-! ### Scheduler answers -/

/-- **A scheduler answer at index `k`** (`PoolAnsN` closes it downward): `f` applied to any pool
meeting `Inv` whose entries are held at index at least `k` and answer in `PoolAnsN` below `k`,
beside the pool's resource, answers `Q` at the empty table. -/
def PoolAnsAtN (Φ : LocFam) (Q : PostN) (H : Val) (Inv : List StoredN → Prop) :
    (k : Nat) → List SRec → Val → WRes → Prop
  | k, ls, f, ρ =>
    ∀ (ts : List StoredN) (σ ρ' : WRes), Inv ts →
      (∀ t ∈ ts, k ≤ t.k ∧ ∀ (j : Nat) (_hj : j < k) (ls' : List SRec) (v : Val) (ρ'' : WRes),
        t.Q j ls' v ρ'' → ∀ (j' : Nat) (_hj' : j' ≤ j), PoolAnsAtN Φ Q H Inv j' ls' v ρ'') →
      PoolN (ℍ := ℍ) Φ ts ls σ → ResU.CompS ρ σ ρ' →
      erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q k ls (.app f.1 (stateValN H ts).1) ρ'
termination_by k => k

/-- **A scheduler answer**: `PoolAnsAtN` at every index up to `k`. -/
def PoolAnsN (Φ : LocFam) (Q : PostN) (H : Val) (Inv : List StoredN → Prop) : PostN :=
  fun k ls f ρ => ∀ j ≤ k, PoolAnsAtN (ℍ := ℍ) Φ Q H Inv j ls f ρ

theorem poolAnsN_down (Φ : LocFam) (Q : PostN) (H : Val) (Inv : List StoredN → Prop) :
    (PoolAnsN (ℍ := ℍ) Φ Q H Inv).Down :=
  fun _ _ _ _ h j hj => h j (by omega)

/-- **A stored task good at `k`**: held at index at least `k`, and answering a scheduler answer
at every index below `k`. -/
def GoodN (Φ : LocFam) (Q : PostN) (H : Val) (Inv : List StoredN → Prop) (k : Nat)
    (t : StoredN) : Prop :=
  k ≤ t.k ∧ ∀ j, j < k → ∀ (ls' : List SRec) (v : Val) (ρ'' : WRes), t.Q j ls' v ρ'' →
    PoolAnsN (ℍ := ℍ) Φ Q H Inv j ls' v ρ''

theorem GoodN.le {Φ : LocFam} {Q : PostN} {H : Val} {Inv : List StoredN → Prop} {k k' : Nat}
    {t : StoredN} (h : GoodN (ℍ := ℍ) Φ Q H Inv k t) (hk : k' ≤ k) :
    GoodN (ℍ := ℍ) Φ Q H Inv k' t :=
  ⟨by have := h.1; omega, fun j hj => h.2 j (by omega)⟩

theorem poolAnsAtN_iff {Φ : LocFam} {Q : PostN} {H : Val} {Inv : List StoredN → Prop} {k : Nat}
    {ls : List SRec} {f : Val} {ρ : WRes} :
    PoolAnsAtN (ℍ := ℍ) Φ Q H Inv k ls f ρ ↔
      ∀ (ts : List StoredN) (σ ρ' : WRes), Inv ts → (∀ t ∈ ts, GoodN (ℍ := ℍ) Φ Q H Inv k t) →
        PoolN (ℍ := ℍ) Φ ts ls σ → ResU.CompS ρ σ ρ' →
        erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q k ls (.app f.1 (stateValN H ts).1) ρ' := by
  rw [PoolAnsAtN]
  constructor
  · intro h ts σ ρ' hi hg
    exact h ts σ ρ' hi fun t ht => ⟨(hg t ht).1, fun j hj ls' v ρ'' hq => (hg t ht).2 j hj ls' v ρ'' hq⟩
  · intro h ts σ ρ' hi hg
    exact h ts σ ρ' hi fun t ht => ⟨(hg t ht).1, fun j hj ls' v ρ'' hq => (hg t ht).2 j hj ls' v ρ'' hq⟩

/-! ### What the scheduler must satisfy -/

/-- **A top-level scheduler `hnd (n₀, (qs, (h_ret, hs)))` meeting its clauses at the stops up to
`N`**, for tasks at the table `T` answering `Qin`, the program answering `Qout`: the premises of
`erwp_handle_le` at the empty outer table, each stopped task's cancel run at `T` itself.

* `T` is downward closed and every operation of `T` is the scheduler's (`n₀`);
* each non-abortive operation's continuation tag (`qs`) is its entry's qualifier;
* a cancellable entry's cancel obligation is a cancel run at a table inside `T`;
* an entry's world condition holds between lists with the same members;
* `Qout` is downward closed;
* the return clause, and every operation's clause, at the empty table. -/
structure SchedOKNLe (Φ : LocFam) (N : Nat) (T : OpTabN) (n₀ : UInt32) (qs hr hs : Val)
    (Qin Qout : PostN) : Prop where
  down : T.Down
  names : ∀ m i, m ≠ n₀ → T m i = none
  tags : ∀ i en, T n₀ i = some en → en.abort = false → capTag qs.1 i.toNat = en.q.tag
  fin : ∀ i en, T n₀ i = some en → en.abort = false → en.q ≠ .lin →
    ∃ T₁, en.fin = some (cancelOblN (ℍ := ℍ) Φ T₁) ∧ T₁.Sub T
  wc : ∀ i en, T n₀ i = some en → ∀ (ls ls' : List SRec) (ρ : WRes),
    (∀ x, x ∈ ls' ↔ x ∈ ls) → en.wc ls ls' ρ
  qdown : Qout.Down
  ret : ∀ k, k ≤ N → ∀ ls v ρ, Qin k ls v ρ →
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Qout k ls (.app (.val hr) (.val v)) ρ
  op : ∀ i en, T n₀ i = some en → ∃ c, clauseAt hs.1 i.toNat = some c ∧
    (en.abort = false → ∀ k, k ≤ N → ∀ ls v (κ : Val) ρ,
      (en.PA k ls v ⋆ KapRelN (ℍ := ℍ) Φ (opTableN OpTabN.empty) Qout en (some T) k ls κ) ρ →
      erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Qout k ls (.app (.val c) (.pair (.val v) κ.1)) ρ) ∧
    (en.abort = true → ∀ k, k ≤ N → ∀ ls v ρ, en.PA k ls v ρ →
      erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Qout k ls (.app (.val c) (.val v)) ρ)

/-- **A scheduler meeting its clauses at every stop index.** A clause that runs a task under its
own scheduler (a spawn) proves its case at `N` from `SchedOKNLe` below `N`, so this is proved by
strong induction on `N`. -/
def SchedOKN (Φ : LocFam) (T : OpTabN) (n₀ : UInt32) (qs hr hs : Val) (Qin Qout : PostN) : Prop :=
  ∀ N, SchedOKNLe (ℍ := ℍ) Φ N T n₀ qs hr hs Qin Qout

/-- **`[handle]` for the scheduler**, at every index up to `N`. -/
theorem erwp_schedHandle_le {Φ : LocFam} (hΦ : Φ.Down) {N : Nat} {T : OpTabN} {n₀ : UInt32}
    {qs hr hs : Val} {Qin Qout : PostN} (hS : SchedOKNLe (ℍ := ℍ) Φ N T n₀ qs hr hs Qin Qout) :
    ∀ n, n ≤ N → ∀ ls e ρ, erwp (ℍ := ℍ) Φ (opTableN T) Qin n ls e ρ →
      erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Qout n ls (hndE (hndVal n₀ qs hr hs) e) ρ :=
  erwp_handle_le hΦ N T OpTabN.empty hS.down OpTabN.empty_down n₀ hS.names qs hr hs Qin Qout
    hS.qdown hS.tags (fun _ => some T)
    (fun i en hT ha hq Tk hTk => by
      cases hTk
      obtain ⟨T₁, hf, hs⟩ := hS.fin i en hT ha hq
      exact ⟨T₁, hf, hs, hS.down⟩)
    hS.ret hS.op

/-! ### The pool's moves -/

/-- The context that applies a scheduler answer to the state. -/
theorem stateK_hnd (s : Val) : ∀ m, (Kont.appL .hole s).HasHnd m = false := fun _ => rfl
theorem stateK_catch (s : Val) : ∀ m, (Kont.appL .hole s).Catches m = false := fun _ => rfl
theorem stateK_closed (s : Val) : OpTabN.empty.CtxClosed (Kont.appL .hole s) :=
  fun _ _ _ _ h => by simp [OpTabN.empty] at h

/-- **A run beside the pool, its value applied to the state**: the pool framed beside the run
(`erwpE_frame`), the run's end at an index up to its own, beside the pool at the end list. -/
theorem erwpE_runPool {Φ : LocFam} (hΦ : Φ.Down) {Q P : PostN} {ts : List StoredN} (s : Val)
    {n : Nat} {ls : List SRec} {e : Expr} {ρ₁ ρp ρ : WRes}
    (h : erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) P n ls e ρ₁) (hP : PoolN (ℍ := ℍ) Φ ts ls ρp)
    (hc : ResU.CompS ρ₁ ρp ρ)
    (hcont : ∀ k, k ≤ n → ∀ ls' (v : Val) (ρa ρb ρ' : WRes), P k ls' v ρa →
      PoolN (ℍ := ℍ) Φ ts ls' ρb → ResU.CompS ρa ρb ρ' →
      erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q k ls' (.app v.1 s.1) ρ') :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q n ls (.app e s.1) ρ := by
  have h₁ := erwpE_frame (PoolN (ℍ := ℍ) Φ ts) (fun _ _ hm _ h => PoolN.mem hm h) hc
    (erwpE_post_le h) hP
  exact erwp_bind hΦ (Kont.appL .hole s) (stateK_hnd s) (stateK_catch s) (stateK_closed s)
    (fun k ls' v ρ' ⟨ρa, ρb, hcab, ⟨hk, hp⟩, hb⟩ => hcont k hk ls' v ρa ρb ρ' hp hb hcab)
    n ls e ρ h₁

/-- **Run**: a task `e` at the scheduler's table, at an index up to `N`, run under the scheduler
beside the pool, the state applied to what it answers. -/
theorem poolAnsN_run_le {Φ : LocFam} (hΦ : Φ.Down) {N : Nat} {T : OpTabN} {n₀ : UInt32}
    {qs hr hs : Val} {Qin Q : PostN} {Inv : List StoredN → Prop}
    (hS : SchedOKNLe (ℍ := ℍ) Φ N T n₀ qs hr hs Qin
      (PoolAnsN (ℍ := ℍ) Φ Q (hndVal n₀ qs hr hs) Inv))
    {ts : List StoredN} {k : Nat} (hkN : k ≤ N)
    (hg : ∀ u ∈ ts, GoodN (ℍ := ℍ) Φ Q (hndVal n₀ qs hr hs) Inv k u) (hi : Inv ts)
    {ls : List SRec} {e : Expr} {ρ₁ ρp ρ : WRes} (hP : PoolN (ℍ := ℍ) Φ ts ls ρp)
    (hc : ResU.CompS ρ₁ ρp ρ) (he : erwp (ℍ := ℍ) Φ (opTableN T) Qin k ls e ρ₁) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q k ls
      (.app (hndE (hndVal n₀ qs hr hs) e) (stateValN (hndVal n₀ qs hr hs) ts).1) ρ := by
  refine erwpE_runPool hΦ _ (erwp_schedHandle_le hΦ hS k hkN ls e ρ₁ he) hP hc ?_
  intro k₁ hk₁ ls' v ρa ρb ρ' hf hb hcab
  exact poolAnsAtN_iff.mp (hf k₁ le_rfl) ts ρb ρ' hi (fun u hu => (hg u hu).le hk₁) hb hcab

/-- **Park**: the stopped task's continuation, as its clause receives it, joins the pool at its
top, good at every index up to its stop's. -/
theorem poolAnsN_park {Φ : LocFam} {Q : PostN} {H : Val} {Inv : List StoredN → Prop}
    {en : OpEntN} {Tc : Option OpTabN} {k : Nat} {ls : List SRec} {κ : Val} (tag : Val)
    {ρk σ ρ : WRes}
    (hκ : KapRelN (ℍ := ℍ) Φ (opTableN OpTabN.empty) (PoolAnsN (ℍ := ℍ) Φ Q H Inv) en Tc k ls κ ρk)
    (hwc : ∀ ls', (∀ x, x ∈ ls' ↔ x ∈ ls) → en.wc ls ls' ρk)
    {j : Nat} (hj : j ≤ k) {ts : List StoredN} (hg : ∀ t ∈ ts, GoodN (ℍ := ℍ) Φ Q H Inv j t)
    (hP : PoolN (ℍ := ℍ) Φ ts ls σ) (hc : ResU.CompS ρk σ ρ) :
    PoolN (ℍ := ℍ) Φ (⟨PoolAnsN (ℍ := ℍ) Φ Q H Inv, en, Tc, k, ls, κ, tag⟩ :: ts) ls ρ ∧
    ∀ t ∈ (⟨PoolAnsN (ℍ := ℍ) Φ Q H Inv, en, Tc, k, ls, κ, tag⟩ :: ts : List StoredN),
      GoodN (ℍ := ℍ) Φ Q H Inv j t := by
  refine ⟨⟨ρk, σ, hc, ⟨hκ, hwc⟩, hP⟩, fun t ht => ?_⟩
  rcases List.mem_cons.mp ht with rfl | ht
  · exact ⟨hj, fun _ _ _ _ _ h => h⟩
  · exact hg t ht

/-- **Resume the top**: the pool's top task resumed at an answer `a` its entry accepts, with the
answer's resource `σ` beside the pool, the rest of the pool (meeting `Inv`) handed to what it
answers. -/
theorem poolAnsN_resume {Φ : LocFam} (hΦ : Φ.Down) {Q : PostN} {H : Val}
    {Inv : List StoredN → Prop} {t : StoredN} {ts : List StoredN} {k' : Nat}
    (hg : ∀ u ∈ t :: ts, GoodN (ℍ := ℍ) Φ Q H Inv (k' + 1) u) {ls : List SRec}
    {ρp σ ρ : WRes} (hP : PoolN (ℍ := ℍ) Φ (t :: ts) ls ρp) {a : Val}
    (hB : t.en.PB k' ls a σ) (hc : ResU.CompS ρp σ ρ) (hi : Inv ts) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q k' ls
      (.app (.app (.app t.κ.1 (.val (Val.inj₁ .unit))) (.val a)) (stateValN H ts).1) ρ := by
  obtain ⟨ρt, ρs, hcp, ⟨hκ, hwc⟩, hPs⟩ := hP
  have hk : k' < t.k := by have := (hg t List.mem_cons_self).1; omega
  obtain ⟨x, hx, hxρ⟩ := compS_exch hcp hc
  have hres := (hκ.2 ls (hwc ls fun _ => Iff.rfl) k' hk).1 a σ x hB hx
  refine erwpE_runPool hΦ _ hres hPs hxρ ?_
  intro k₁ hk₁ ls' v ρa ρb ρ' hq hb hcab
  have hfa := (hg t List.mem_cons_self).2 k₁ (by omega) ls' v ρa hq
  exact poolAnsAtN_iff.mp (hfa k₁ le_rfl) ts ρb ρ' hi
    (fun u hu => (hg u (List.mem_cons_of_mem _ hu)).le (by omega)) hb hcab

/-- **Cancel the top**: the pool's top task, at a cancellable entry whose cancel run is at the
scheduler's table, its cancel branch run under the scheduler beside the rest of the pool. -/
theorem poolAnsN_cancel {Φ : LocFam} (hΦ : Φ.Down) {N : Nat} {T : OpTabN} {n₀ : UInt32}
    {qs hr hs : Val} {Qin Q : PostN} {Inv : List StoredN → Prop}
    (hS : SchedOKNLe (ℍ := ℍ) Φ N T n₀ qs hr hs Qin
      (PoolAnsN (ℍ := ℍ) Φ Q (hndVal n₀ qs hr hs) Inv))
    (hQin : ∀ k ls v ρ, unitPost k ls v ρ → Qin k ls v ρ)
    {t : StoredN} {ts : List StoredN} {k' : Nat} (hkN : k' ≤ N)
    (hg : ∀ u ∈ t :: ts, GoodN (ℍ := ℍ) Φ Q (hndVal n₀ qs hr hs) Inv (k' + 1) u)
    {ls : List SRec} {ρ : WRes} (hP : PoolN (ℍ := ℍ) Φ (t :: ts) ls ρ) (hq : t.en.q ≠ .lin)
    (hTc : t.Tc = some T) (hi : Inv ts) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q k' ls
      (.app (hndE (hndVal n₀ qs hr hs) (.app t.κ.1 (.val (Val.inj₂ .unit))))
        (stateValN (hndVal n₀ qs hr hs) ts).1) ρ := by
  obtain ⟨ρt, ρs, hcp, ⟨hκ, hwc⟩, hPs⟩ := hP
  have hk : k' < t.k := by have := (hg t List.mem_cons_self).1; omega
  have hcan := (hκ.2 ls (hwc ls fun _ => Iff.rfl) k' hk).2 hq T hTc
  have he := erwp_mono (Tb := opTableN T) (fun k ls v ρ h => hQin k ls v ρ h)
    (opTableN_local T) k' ls _ ρt hcan
  exact poolAnsN_run_le hΦ hS hkN (fun u hu => (hg u (List.mem_cons_of_mem _ hu)).le (by omega))
    hi hPs hcp he

/-- **Resume the second**: the pool's second task resumed, the first kept at the top of the rest
(`PoolN.swap`). A park that resumes another task and keeps the parked one in its place is this
move after `poolAnsN_park`. -/
theorem poolAnsN_resumeSnd {Φ : LocFam} (hΦ : Φ.Down) {Q : PostN} {H : Val}
    {Inv : List StoredN → Prop} {t u : StoredN} {ts : List StoredN} {k' : Nat}
    (hg : ∀ x ∈ t :: u :: ts, GoodN (ℍ := ℍ) Φ Q H Inv (k' + 1) x) {ls : List SRec}
    {ρp σ ρ : WRes} (hP : PoolN (ℍ := ℍ) Φ (t :: u :: ts) ls ρp) {a : Val}
    (hB : u.en.PB k' ls a σ) (hc : ResU.CompS ρp σ ρ) (hi : Inv (t :: ts)) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q k' ls
      (.app (.app (.app u.κ.1 (.val (Val.inj₁ .unit))) (.val a)) (stateValN H (t :: ts)).1) ρ :=
  poolAnsN_resume hΦ (fun x hx => hg x ((List.Perm.swap t u ts).mem_iff.mp hx)) hP.swap hB hc hi

/-- **Cancel the second**: the pool's second task cancelled, the first kept at the top of the
rest (`PoolN.swap`). A clause that parks the task it stopped and cancels another is this move
after `poolAnsN_park`. -/
theorem poolAnsN_cancelSnd {Φ : LocFam} (hΦ : Φ.Down) {N : Nat} {T : OpTabN} {n₀ : UInt32}
    {qs hr hs : Val} {Qin Q : PostN} {Inv : List StoredN → Prop}
    (hS : SchedOKNLe (ℍ := ℍ) Φ N T n₀ qs hr hs Qin
      (PoolAnsN (ℍ := ℍ) Φ Q (hndVal n₀ qs hr hs) Inv))
    (hQin : ∀ k ls v ρ, unitPost k ls v ρ → Qin k ls v ρ)
    {t u : StoredN} {ts : List StoredN} {k' : Nat} (hkN : k' ≤ N)
    (hg : ∀ x ∈ t :: u :: ts, GoodN (ℍ := ℍ) Φ Q (hndVal n₀ qs hr hs) Inv (k' + 1) x)
    {ls : List SRec} {ρ : WRes} (hP : PoolN (ℍ := ℍ) Φ (t :: u :: ts) ls ρ) (hq : u.en.q ≠ .lin)
    (hTc : u.Tc = some T) (hi : Inv (t :: ts)) :
    erwp (ℍ := ℍ) Φ (opTableN OpTabN.empty) Q k' ls
      (.app (hndE (hndVal n₀ qs hr hs) (.app u.κ.1 (.val (Val.inj₂ .unit))))
        (stateValN (hndVal n₀ qs hr hs) (t :: ts)).1) ρ :=
  poolAnsN_cancel hΦ hS hQin hkN (fun x hx => hg x ((List.Perm.swap t u ts).mem_iff.mp hx))
    hP.swap hq hTc hi

/-! ### The headline -/

/-- **Pool-scheduler adequacy over the chain relation.** A closed program `(hnd H e₀) s₀`, `s₀`
the empty pool: the task `e₀` at `erwp` at the scheduler's table `T`, from the empty list and
resource, at every index; the scheduler `H = hndVal n₀ qs hr hs` meeting `SchedOKN` with its
answers functions of its state (`PoolAnsN Q H Inv`, for any invariant `Inv` of its list the empty
list meets), at any downward-closed location family holding no `imm` record (the program starts
at the empty list, so the entry tie asks that); the program's answers holding nothing. -/
def PoolSchedAdequacyN : Prop :=
  ∀ (Φ : LocFam) (T : OpTabN) (n₀ : UInt32) (qs hr hs : Val) (Qin Q : PostN)
    (Inv : List StoredN → Prop) (e₀ : Expr), Φ.Down → Φ.imm = [] →
    (∀ k ls v ρ, Q k ls v ρ → ρ = PMap.empty) → Inv [] →
    SchedOKN (ℍ := ℍ) Φ T n₀ qs hr hs Qin (PoolAnsN (ℍ := ℍ) Φ Q (hndVal n₀ qs hr hs) Inv) →
    (∀ n, erwp (ℍ := ℍ) Φ (opTableN T) Qin n [] e₀ (PMap.empty : WRes)) →
    OrDiverges (ℍ := ℍ) (.app (hndE (hndVal n₀ qs hr hs) e₀) (stateValN (hndVal n₀ qs hr hs) []).1)

theorem poolSchedAdequacyN : PoolSchedAdequacyN (ℍ := ℍ) :=
  fun _ _ _ _ _ _ _ _ _ _ hΦ hΦI hQ hInv hS he => erwp_adequacy hQ (fun n =>
    poolAnsN_run_le hΦ (hS n) le_rfl (fun _ h => by cases h) hInv poolN_nil
      (ResU.comp_empty_right _) (he n)) (ImmTieL.of_nil hΦI [])

end BoCa.Fig16.LogRel.Core.Chain.SI

end
