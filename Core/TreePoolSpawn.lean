import Core.TreePoolSchedProgs

/-!
# An interleaving scheduler with park, spawn, cancel and join, through `PoolSchedAdequacyT`  `[spec §62]`

The scheduler `HS` keeps its stopped tasks in a stack (`PoolAns`) and has four operations under
the name `nP`:

* `park ()` (`enPark`, index 0): the stopped task is parked; if the stack's top is a ready task it
  is resumed and the stopped task stays beneath it (`poolAns_park`, then `poolAns_resumeSnd`);
  otherwise (the stack empty, or its top a joiner) the stopped task is resumed;
* `spawn th` (index 1): the spawner is parked as a ready task and the child `th ()`, holding
  nothing, is run under the scheduler beside the stack (`poolAns_park`, then `poolAns_run_le`);
* `cancel ()` (`enPark`, index 2): the stopped task is parked; if the top is a ready task it is
  cancelled, its cancel branch run under the scheduler (`poolAns_park`, then
  `poolAns_cancelSnd`); otherwise the stopped task is resumed;
* `par (th₁, th₂)` (index 3): the payload's resource is the two children's (`parPA`); the parent
  is parked as a **joiner** sharing every lent location it owns or is shared with it, the second
  child is stored unstarted above it (`κU`, a continuation the clause builds: resumed it runs
  `th₂ ()` under the scheduler, cancelled it hands its resource back), and the first child is run
  (`poolAns_park` twice, then `poolAns_run_le`). The parent is resumed when every task above it
  has ended, with the copies they handed back (`enParP`'s answer, `ViewsT`).

A task's end hands its copies to the nearest joiner and resumes the stack's top (`stackRet`,
`poolAns_depositResume`). The clauses are proved for every stack of any length (`hs_schedOK`), by
strong induction on the stop index (`SchedOKTLe`): the spawn and par clauses run their children
below their own index, at the scheduler's clauses there.

**Children at any depth.** A child's thunk is verified at a table that itself has `spawn` and
`par`: the tables are indexed (`tabAt k`), the entries of `tabAt k` reading the children of a stop
at `j < k` at `tabAt j`. Every `tabAt k` agrees with the scheduler's table `TJ` at the stops up to
`k` (`tabAt_inclLe`), so a child verified at `tabAt j` at index `j` is verified at `TJ`
(`cerwpT_tabAt`).

**Why a continuation the clause builds, not a new operation.** A second, unstarted child must be
stored like any other task, as a continuation the scheduler resumes or cancels. The clause builds
one from the thunk and its own handler (`κU`) and proves it is a stored task (`kapSchedT_κU`), with
the operations already in the kernel; a `fork` operation would add a primitive to the kernel for
the same entry.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.SchedProgs.Spawn
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.Tree.Wp.SchedProgs.Park
open BoCa.Fig16.Tree.Wp.SchedProgs.Stack
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont performE opPayload hndE hndVal capTag clauseAt ccatchE raiseE
  cancelVal)

/-! ### Copies of lends: their flattening -/

section ViewsFlat
variable {K : WCactus}

theorem ag_viewS {S : TSet} {m : BoCa.Loc} {a : TRes K} (h : AgWT (viewResS S m) a) :
    a = viewResS S m := by
  obtain ⟨e, a', p, he, ha', hp, hc⟩ := AgWT.single_imm_inv (χ := PMap.empty) h
  obtain rfl : e = PMap.empty :=
    ExRT.functional he (ExWT.empty_of_all_imm (fun _ _ e => by simp at e))
  obtain rfl : a' = PMap.empty := AgWT.functional ha' BoCa.Fig16.Tree.agW_empty
  obtain rfl : PMap.empty = p := ResUT.eq_of_comp_empty_right hp
  exact (ResUT.eq_of_comp_empty_right hc).symm

/-- **The aliasable walk of copies sits where they sit**, by induction on a list covering their
locations. -/
theorem ViewsT.ag_none : ∀ (L : List BoCa.Loc) {Z a : TRes K},
    (∀ x, Z.get x ≠ none → x ∈ L) → ViewsT Z → AgWT Z a → ∀ l, Z.get l = none → a.get l = none
  | [], Z, a, hL, _, ha, l, _ => by
      have hZ : Z = PMap.empty := PMap.ext fun x => by
        by_contra h
        exact absurd (hL x (by simpa using h)) (by simp)
      subst hZ
      obtain rfl := AgWT.functional ha BoCa.Fig16.Tree.agW_empty
      simp
  | x :: L, Z, a, hL, hV, ha, l, hl => by
      classical
      cases ex : Z.get x with
      | none =>
          refine ViewsT.ag_none L (fun y hy => ?_) hV ha l hl
          rcases List.mem_cons.mp (hL y hy) with rfl | h
          · exact absurd ex hy
          · exact h
      | some ψ =>
          obtain ⟨S, rfl⟩ := hV x _ ex
          have hc : ResUT.CompS (Z.del x) (viewResS S x) Z := ResUT.del_compS ex
          obtain ⟨σ₁, σ₂, h₁, h₂, h₁₂⟩ := (AgWT.split hc).mp ha
          obtain rfl := ag_viewS h₂
          have hlx : l ≠ x := fun e => by rw [e, ex] at hl; cases hl
          have hσ₁ : σ₁.get l = none := by
            refine ViewsT.ag_none L (fun y hy => ?_) (hV.del x) h₁ l
              (by rw [ResUT.del_get_ne _ hlx]; exact hl)
            by_cases hyx : y = x
            · subst hyx; simp at hy
            · rw [ResUT.del_get_ne _ hyx] at hy
              rcases List.mem_cons.mp (hL y hy) with h | h
              · exact absurd h hyx
              · exact h
          rcases ResUT.Comp.get h₁₂ l with ⟨-, -, f⟩ | ⟨χ, f₁, -, -⟩ | ⟨χ, -, f₂, -⟩ |
              ⟨χ₁, χ₂, χ, f₁, -, -, -⟩
          · exact f
          · rw [hσ₁] at f₁; cases f₁
          · rw [viewResS, ResUT.single_get_ne _ hlx] at f₂; cases f₂
          · rw [hσ₁] at f₁; cases f₁

/-- **Copies hold nothing in their flattening where they hold no cell.** -/
theorem ViewsT.noneAt {Z : TRes K} (hV : ViewsT Z) {l : BoCa.Loc} (hl : Z.get l = none) :
    NoneAt (· = l) Z := by
  intro τ hτ x hx
  subst hx
  obtain ⟨e, a, he, ha, hc⟩ := hτ
  obtain rfl : e = PMap.empty := ExST.functional he (exST_all_imm fun _ _ e => hV.kind e)
  obtain rfl := ResUT.CompS.functional hc (ResUT.comp_empty_left a)
  obtain ⟨L, hL⟩ := Z.finite
  exact ViewsT.ag_none L (fun y hy => hL y hy) hV ha x hl

end ViewsFlat

/-! ### The tables, indexed -/

/-- `spawn`'s entry, at a payload condition `P`. -/
def enSpawnP (P : TVProp) : OpEntT where
  q := .cancel
  abort := false
  PA := P
  PBv := fun _ _ _ _ a σ => a = Val.unit ∧ σ = PMap.empty
  fin := true
  fd := fdJoinT
  oc := fun _ _ => True

/-- `par`'s entry, at a payload condition `P`: the parent is resumed with copies of lends. -/
def enParP (P : TVProp) : OpEntT where
  q := .lin
  abort := false
  PA := P
  PBv := fun _ _ _ _ a σ => a = Val.unit ∧ ViewsT σ
  fin := false
  fd := fdJoinT
  oc := fun _ _ => True

/-- **A child, run as a new task from `ρ`**: at every index `j` below `k`, at every extension of
the stop's world on `ρ`'s re-reading, at every list, at every base frame condition every valid frame
meets and present one every frame meets, `th ()` is verified at the table `T j`. -/
def ChildOK (T : Nat → OpTabT) (k : Nat) (w : TWd) (th : Val) (ρ : TRes w.K) : Prop :=
  ∀ j, j < k → ∀ (w' : TWd) (ρ' : TRes w'.K) (ls' : List (SRecT w'.K)), w.Ext w' ρ →
    RRw (w := w) (w' := w') ρ ρ' → ∀ (Fb Fe : TFrame), (∀ w ρf, ResUT.Valid ρf → Fb w ρf) →
    (∀ w ρf, fdMask (fun _ => False) w ρf → Fe w ρf) →
    cerwpT (ℍ := ℍ) (opTableT (T j)) QV Fb Fe j w' ls' [] (.app th.1 (.val Val.unit)) ρ'

/-- `spawn`'s payload: a child holding nothing. -/
def spawnPA (T : Nat → OpTabT) : TVProp := fun k w _ v ρ =>
  ρ = PMap.empty ∧ ChildOK (ℍ := ℍ) T k w v ρ

/-- `par`'s payload: two children, the resource split between them, each holding copies of
lends. -/
def parPA (T : Nat → OpTabT) : TVProp := fun k w _ v ρ =>
  ∃ (th₁ th₂ : Val) (ρ₁ ρ₂ : TRes w.K), v = Val.pair th₁ th₂ ∧ ResUT.CompS ρ₁ ρ₂ ρ ∧
    ViewsT ρ₁ ∧ ViewsT ρ₂ ∧ ChildOK (ℍ := ℍ) T k w th₁ ρ₁ ∧ ChildOK (ℍ := ℍ) T k w th₂ ρ₂

/-- The table, its children's tables given. -/
def tabOf (T : Nat → OpTabT) : OpTabT := fun m i =>
  if m = nP then
    (if i = 0 then some enPark else if i = 1 then some (enSpawnP (spawnPA (ℍ := ℍ) T))
      else if i = 2 then some enPark else if i = 3 then some (enParP (parPA (ℍ := ℍ) T))
      else none)
  else none

/-- **The table at index `k`**: its children's tables are those below `k`. -/
def tabAt : Nat → OpTabT
  | k => tabOf (ℍ := ℍ) fun j => if _h : j < k then tabAt j else OpTabT.empty
termination_by k => k

/-- **The scheduler's table**: its children's tables are the indexed ones. -/
def TJ : OpTabT := tabOf (ℍ := ℍ) (tabAt (ℍ := ℍ))

theorem tabAt_eq (k : Nat) :
    tabAt (ℍ := ℍ) k = tabOf (ℍ := ℍ) fun j => if j < k then tabAt (ℍ := ℍ) j else OpTabT.empty := by
  rw [tabAt]; rfl

theorem tabOf_some {T : Nat → OpTabT} {m i : UInt32} {en : OpEntT}
    (h : tabOf (ℍ := ℍ) T m i = some en) :
    m = nP ∧ ((i = 0 ∧ en = enPark) ∨ (i = 1 ∧ en = enSpawnP (spawnPA (ℍ := ℍ) T)) ∨
      (i = 2 ∧ en = enPark) ∨ (i = 3 ∧ en = enParP (parPA (ℍ := ℍ) T))) := by
  unfold tabOf at h
  split at h
  · rename_i hm
    refine ⟨hm, ?_⟩
    split at h
    · cases h; exact Or.inl ⟨by assumption, rfl⟩
    split at h
    · cases h; exact Or.inr (Or.inl ⟨by assumption, rfl⟩)
    split at h
    · cases h; exact Or.inr (Or.inr (Or.inl ⟨by assumption, rfl⟩))
    split at h
    · cases h; exact Or.inr (Or.inr (Or.inr ⟨by assumption, rfl⟩))
    · cases h
  · cases h

theorem tabOf_park (T : Nat → OpTabT) : tabOf (ℍ := ℍ) T nP 0 = some enPark := by simp [tabOf]
theorem tabOf_spawn (T : Nat → OpTabT) :
    tabOf (ℍ := ℍ) T nP 1 = some (enSpawnP (spawnPA (ℍ := ℍ) T)) := by simp [tabOf]
theorem tabOf_cancel (T : Nat → OpTabT) : tabOf (ℍ := ℍ) T nP 2 = some enPark := by simp [tabOf]
theorem tabOf_par (T : Nat → OpTabT) :
    tabOf (ℍ := ℍ) T nP 3 = some (enParP (parPA (ℍ := ℍ) T)) := by simp [tabOf]

theorem ChildOK.down {T : Nat → OpTabT} {k : Nat} {w : TWd} {th : Val} {ρ : TRes w.K}
    (h : ChildOK (ℍ := ℍ) T (k + 1) w th ρ) : ChildOK (ℍ := ℍ) T k w th ρ :=
  fun j hj => h j (by omega)

theorem tabOf_down (T : Nat → OpTabT) : ∀ m i en, tabOf (ℍ := ℍ) T m i = some en →
    ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ → en.PA k w ls v ρ := by
  intro m i en h k w ls v ρ hA
  obtain ⟨-, ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩⟩ := tabOf_some h
  · exact hA
  · exact ⟨hA.1, hA.2.down⟩
  · exact hA
  · obtain ⟨th₁, th₂, ρ₁, ρ₂, h₁, h₂, h₃, h₄, h₅, h₆⟩ := hA
    exact ⟨th₁, th₂, ρ₁, ρ₂, h₁, h₂, h₃, h₄, h₅.down, h₆.down⟩

/-! ### A table agreeing with another at the stops up to an index -/

/-- **A table includes another at the stops up to `N`.** -/
def InclLe (N : Nat) (Tb₁ Tb₂ : TableT) : Prop :=
  ∀ F k w ls O t (Ψ Ψ' : ContT) ρ, k ≤ N →
    (∀ F' w' O' k', k' < k → ∀ ls' e ρ', Ψ F' w' O' k' ls' e ρ' → Ψ' F' w' O' k' ls' e ρ') →
    Tb₁ F k w ls O t Ψ ρ → Tb₂ F k w ls O t Ψ' ρ

/-- **A run verified at a table at an index up to `N` is verified at a table including it at the
stops up to `N`**, by strong induction on the index: every stop of the run is at an index up to
its own. -/
theorem cerwpT_table_mono_le {Tb₁ Tb₂ : TableT} {N : Nat} (hI : InclLe N Tb₁ Tb₂) {Q : TPostV}
    {Fb : TFrame} : ∀ (n : Nat), n ≤ N → ∀ (F : TFrame) (w : TWd) (ls : List (SRecT w.K))
      (O : List (FrameRecT w.K)) (e : Expr) (ρ : TRes w.K),
      cerwpT (ℍ := ℍ) Tb₁ Q Fb F n w ls O e ρ → cerwpT (ℍ := ℍ) Tb₂ Q Fb F n w ls O e ρ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN F w ls O e ρ h
  rw [cerwpT_eq] at h ⊢
  refine twp_mono_le (fun k hk w' ls' O' t ρ' ht => ?_) h
  rcases ht with ht | ht
  · exact Or.inl ht
  · refine Or.inr (hI Fb k w' ls' O' t _ _ ρ' (by omega)
      (fun F' w'' O'' k' hk' ls'' e'' ρ'' hΨ => ?_) ht)
    simp only [cerwpTC, show k' < n by omega, if_true] at hΨ ⊢
    exact ih k' (by omega) (by omega) F' w'' ls'' O'' e'' ρ'' hΨ

/-- `tabAt k`'s children's tables are the indexed ones below `k`. -/
theorem childOK_trunc {k k' : Nat} (hk : k' ≤ k) {w : TWd} {th : Val} {ρ : TRes w.K}
    (h : ChildOK (ℍ := ℍ) (fun j => if j < k then tabAt (ℍ := ℍ) j else OpTabT.empty) k' w th ρ) :
    ChildOK (ℍ := ℍ) (tabAt (ℍ := ℍ)) k' w th ρ := by
  intro j hj w' ρ' ls' hE hr Fb Fe hFb hFe
  have := h j hj w' ρ' ls' hE hr Fb Fe hFb hFe
  simp only [show j < k by omega, if_true] at this
  exact this

/-- **`tabAt k` is included in `TJ` at the stops up to `k`**: the entries are the same but for
the payload conditions, and those agree up to `k`. -/
theorem tabAt_inclLe (k : Nat) : InclLe k (opTableT (tabAt (ℍ := ℍ) k)) (opTableT (TJ (ℍ := ℍ))) := by
  intro F k' w ls O t Ψ Ψ' ρ hk hΨ ht
  obtain ⟨K, n, i, v, en, h₁, h₂, h₃, h₄, h₅, ρa, ρk, hc, hA, hcont⟩ := ht
  rw [tabAt_eq] at h₃
  refine opTableT_local _ F k' w ls O t Ψ Ψ' ρ hΨ ?_
  obtain ⟨rfl, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := tabOf_some h₃
  · exact ⟨K, nP, 0, v, enPark, h₁, h₂, tabOf_park _, h₄, h₅, ρa, ρk, hc, hA, hcont⟩
  · exact ⟨K, nP, 1, v, enSpawnP (spawnPA (ℍ := ℍ) (tabAt (ℍ := ℍ))), h₁, h₂, tabOf_spawn _, h₄, h₅,
      ρa, ρk, hc, ⟨hA.1, childOK_trunc hk hA.2⟩, hcont⟩
  · exact ⟨K, nP, 2, v, enPark, h₁, h₂, tabOf_cancel _, h₄, h₅, ρa, ρk, hc, hA, hcont⟩
  · obtain ⟨th₁, th₂, ρ₁, ρ₂, e₁, e₂, e₃, e₄, e₅, e₆⟩ := hA
    exact ⟨K, nP, 3, v, enParP (parPA (ℍ := ℍ) (tabAt (ℍ := ℍ))), h₁, h₂, tabOf_par _, h₄, h₅, ρa,
      ρk, hc, ⟨th₁, th₂, ρ₁, ρ₂, e₁, e₂, e₃, e₄, childOK_trunc hk e₅, childOK_trunc hk e₆⟩, hcont⟩

/-- **A child verified at `tabAt j` at index `j` is verified at `TJ`.** -/
theorem cerwpT_tabAt {Q : TPostV} {Fb F : TFrame} {j : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {e : Expr} {ρ : TRes w.K}
    (h : cerwpT (ℍ := ℍ) (opTableT (tabAt (ℍ := ℍ) j)) Q Fb F j w ls O e ρ) :
    cerwpT (ℍ := ℍ) (opTableT (TJ (ℍ := ℍ))) Q Fb F j w ls O e ρ :=
  cerwpT_table_mono_le (tabAt_inclLe j) j le_rfl F w ls O e ρ h

/-! ### The clauses -/

/-- The common prefix `λ(v, κ). λs. let (h, p) = s in b`. -/
def clauseOf (b : Expr) : Val := Val.lam (.letpair (.var 0) (.lam (.letpair (.var 0) b)))

/-- The stopped task as a ready entry, under `h, p, s, κ, v` and `n` more binders. -/
def readyE (n : Nat) : Expr := .pair (.inj₁ .unit) (.var (3 + n))

/-- `park`'s body: the top ready, `κ' (inj₁ ()) () (h, inj₁ ((inj₁ (), κ), p′))`; the top a
joiner or the stack empty, `κ (inj₁ ()) () (h, p)`. -/
def parkB : Expr :=
  .case (.var 0)
    (.letpair (.var 0) (.letpair (.var 1) (.case (.var 1)
      (.app (.app (.app (.var 1) (.inj₁ .unit)) .unit)
        (.pair (.var 7) (.inj₁ (.pair (readyE 6) (.var 3)))))
      (.app (.app (.app (.var 9) (.inj₁ .unit)) .unit) (.pair (.var 7) (.var 6))))))
    (.app (.app (.app (.var 4) (.inj₁ .unit)) .unit) (.pair (.var 2) (.var 1)))

/-- `cancel`'s body: the top ready, `(hnd h (κ' (inj₂ ()))) (h, inj₁ ((inj₁ (), κ), p′))`;
otherwise `κ (inj₁ ()) () (h, p)`. -/
def cancelB : Expr :=
  .case (.var 0)
    (.letpair (.var 0) (.letpair (.var 1) (.case (.var 1)
      (.app (.app (.app (.prim .hnd) (.var 7)) (.app (.var 1) (.inj₂ .unit)))
        (.pair (.var 7) (.inj₁ (.pair (readyE 6) (.var 3)))))
      (.app (.app (.app (.var 9) (.inj₁ .unit)) .unit) (.pair (.var 7) (.var 6))))))
    (.app (.app (.app (.var 4) (.inj₁ .unit)) .unit) (.pair (.var 2) (.var 1)))

/-- `spawn`'s body: `(hnd h (th ())) (h, inj₁ ((inj₁ (), κ), p))`. -/
def spawnB : Expr :=
  .app (.app (.app (.prim .hnd) (.var 1)) (.app (.var 4) .unit))
    (.pair (.var 1) (.inj₁ (.pair (readyE 0) (.var 0))))

/-- The unstarted second child, under `th₂, th₁, p, h`: `λx. case x {inj₁ _. λ_. hnd h (th₂ ())
| inj₂ _. ()}`. -/
def kUB : Expr :=
  .lam (.case (.var 0) (.lam (.app (.app (.prim .hnd) (.var 6)) (.app (.var 3) .unit))) .unit)

/-- `par`'s body: `let (th₁, th₂) = v in (hnd h (th₁ ())) (h, inj₁ ((inj₁ (), κU), inj₁ ((inj₂ (),
κ), p)))`. -/
def parB : Expr :=
  .letpair (.var 4) (.app (.app (.app (.prim .hnd) (.var 3)) (.app (.var 1) .unit))
    (.pair (.var 3) (.inj₁ (.pair (.pair (.inj₁ .unit) kUB)
      (.inj₁ (.pair (.pair (.inj₂ .unit) (.var 5)) (.var 2)))))))

def parkCl : Val := clauseOf parkB
def spawnCl : Val := clauseOf spawnB
def cancelCl : Val := clauseOf cancelB
def parCl : Val := clauseOf parB

def qsS : Val :=
  Val.pair (Val.i32 1) (Val.pair (Val.i32 1) (Val.pair (Val.i32 1) (Val.pair (Val.i32 0) Val.unit)))
def hsS : Val := Val.pair parkCl (Val.pair spawnCl (Val.pair cancelCl (Val.pair parCl Val.unit)))
def HS : Val := hndVal nP qsS stackRet hsS

/-- **The unstarted child** `κU H th`: resumed, `th ()` under `H`; cancelled, `()`. -/
def κU (H th : Val) : Val :=
  Val.lam (.case (.var 0) (.lam (.app (.app (.prim .hnd) (H.shift 3 0).1)
    (.app (th.shift 3 0).1 .unit))) .unit)

/-- The unstarted child's entry: resumed at `()` holding nothing, cancellable. -/
def enU : OpEntT where
  q := .cancel
  abort := false
  PA := fun _ _ _ _ _ => True
  PBv := fun _ _ _ _ a σ => a = Val.unit ∧ σ = PMap.empty
  fin := true
  fd := fdJoinT
  oc := fun _ _ => True

/-- **The stack invariant**: every entry may be resumed by the return clause; a ready entry is
tagged `inj₁ ()` and cancellable, a joiner tagged `inj₂ ()`. -/
def InvS (ts : List StoredJ) : Prop :=
  ∀ t ∈ ts, RetOK t ∧
    ((t.tag = Val.inj₁ Val.unit ∧ t.join = false ∧ t.t.en.q = .cancel ∧ t.t.en.fin = true) ∨
      (t.tag = Val.inj₂ Val.unit ∧ t.join = true))

theorem invS_cons {t : StoredJ} {ts : List StoredJ} (h : InvS (t :: ts)) :
    (RetOK t ∧ ((t.tag = Val.inj₁ Val.unit ∧ t.join = false ∧ t.t.en.q = .cancel ∧
      t.t.en.fin = true) ∨ (t.tag = Val.inj₂ Val.unit ∧ t.join = true))) ∧ InvS ts :=
  ⟨h t List.mem_cons_self, fun u hu => h u (List.mem_cons_of_mem _ hu)⟩

abbrev PA_S : TPostV := PoolAns (ℍ := ℍ) QS HS InvS

set_option linter.unusedSimpArgs false

/-- A substitution below a shift by more than its index undoes one step of the shift. -/
theorem subst_shift0 (d j : Nat) (s : Val) (e : Expr) (h : j ≤ d) :
    Expr.subst j s (Expr.shift (d + 1) 0 e) = Expr.shift d 0 e :=
  Expr.subst_shift d 0 j s e (Nat.zero_le _) (by omega)

/-- Substitution into a clause body after a step. -/
syntax "ssimp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
macro_rules
  | `(tactic| ssimp) => `(tactic| simp [Kont.plug, Expr.subst, Expr.shift_shift,
      BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.subst_shift0, Expr.shift_zero, clauseOf, readyE, parkB,
      cancelB, spawnB, parB, kUB, stateVal, poolVal])
  | `(tactic| ssimp [$ls,*]) => `(tactic| simp [Kont.plug, Expr.subst, Expr.shift_shift,
      BoCa.Fig16.Tree.Wp.SchedProgs.Spawn.subst_shift0, Expr.shift_zero, clauseOf, readyE, parkB,
      cancelB, spawnB, parB, kUB, stateVal, poolVal, $ls,*])

/-- The stopped task, parked as a ready entry. -/
def readyJ (k : Nat) {w : TWd} (O : List (FrameRecT w.K)) (en : OpEntT) (v κ : Val) : StoredJ :=
  ⟨⟨PA_S (ℍ := ℍ), recMask O, en, HS, k, v, κ⟩, false, fun _ => False, Val.inj₁ Val.unit⟩

theorem invS_ready {k : Nat} {w : TWd} {O : List (FrameRecT w.K)} {en : OpEntT} {v κ : Val}
    {ts : List StoredJ} (hq : en.q = .cancel) (hf : en.fin = true)
    (hB : ∀ k w ls, en.PBv v k w ls Val.unit PMap.empty) (hi : InvS ts) :
    InvS (readyJ (ℍ := ℍ) k O en v κ :: ts) := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ⟨fun k w ls c _ hj => by rw [hj rfl]; exact hB k w ls, Or.inl ⟨rfl, rfl, hq, hf⟩⟩
  · exact hi x hx

/-- **`park`'s clause**: the stopped task parked; the top ready, it is resumed and the stopped
task kept beneath it (`poolAns_resumeSnd`); otherwise the stopped task resumed
(`poolAns_resume`). -/
theorem parkCl_ok (N : Nat) :
    SchedClauseTLe (ℍ := ℍ) N HS (PA_S (ℍ := ℍ)) enPark parkCl := by
  rintro F k w ls O v κ ρ _ _ _ _ _ _ _ ⟨ρa, ρk, hc, ⟨rfl, rfl⟩, hκ⟩
  obtain rfl := compS_empty_left_eq hc
  rw [cerwpTE_iff]
  have hD := valPost_down (poolAns_down (ℍ := ℍ) QS HS InvS)
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ _ (Val.pair Val.unit κ)) rfl .hole) ?_
  refine twp_det hD (fun μ => step1Only_plug (Head.letpair μ Val.unit κ _) rfl .hole) ?_
  simp only [Kont.plug]
  refine twp_here (fun μ => final_val μ ⟨_, .lam⟩) fun w₀ ρ₀ ls₀ O₀ hE hr hl hO => ?_
  refine ⟨⟨_, .lam⟩, rfl, fun j hj => poolAnsAt_iff.mpr ?_⟩
  intro ts Os σ ρ' hi hg hP hc' hσ hρ hH hap hcov hv hls hO' F' hF'm hF'M
  have hκ' := KapSchedT.mask_mono (fun x hx => (recMask_rr hO x).mp hx)
    (KapSchedT.kripke hκ hE hr (KeepRel.of_srecsRR hl _) hO)
  obtain ⟨hP', hg'⟩ := poolAns_park (Inv := InvS) false (fun _ => False) (Val.inj₁ Val.unit) hκ' hj
    hg hP hc' hσ hρ hH (fun _ h => h.elim) hap (CovR.of_compS_left hc' hcov) hls hO'
  have hQD := valPost_down QB_down
  cases j with
  | zero => exact twp_zero
  | succ j₀ =>
  refine twp_step (fun μ => step1Only_plug (Head.beta μ _ (stateVal HS ts)) rfl .hole) ?_
  ssimp
  refine twp_det hQD (fun μ => step1Only_plug (Head.letpair μ HS (poolVal ts) _) rfl .hole) ?_
  ssimp
  have hBP : ∀ c σ' : TRes w₀.K, ViewsT c → (false = false → c = PMap.empty) →
      ResUT.CompS c PMap.empty σ' → enPark.PBv Val.unit j₀ w₀ ls₀ Val.unit σ' := by
    intro c σ' _ hj hcσ
    obtain rfl := hj rfl
    exact ⟨rfl, compS_empty_left_eq hcσ⟩
  cases ts with
  | nil =>
    refine twp_det hQD (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl .hole) ?_
    ssimp
    exact poolAns_resume hg' hP' hBP (ResUT.compS_empty_right ρ') (AvoidUnsh.empty _ _)
      (HoldsIn.empty _ _) hcov hv hF'm hF'M hi
  | cons u ts =>
    obtain ⟨⟨hret, hk⟩, hi'⟩ := invS_cons hi
    obtain ⟨ut, uj, ush, utag⟩ := u
    refine twp_det hQD (fun μ => step1Only_plug
      (Head.case₁ μ (Val.pair (Val.pair utag ut.κ) (poolVal ts)) _ _) rfl .hole) ?_
    ssimp
    refine twp_det hQD (fun μ => step1Only_plug
      (Head.letpair μ (Val.pair utag ut.κ) (poolVal ts) _) rfl .hole) ?_
    ssimp
    refine twp_det hQD (fun μ => step1Only_plug (Head.letpair μ utag ut.κ _) rfl .hole) ?_
    ssimp
    rcases hk with ⟨htag, hju, hq, hf⟩ | ⟨htag, hju⟩
    · simp only at htag hju hq hf
      subst htag; subst hju
      refine twp_det hQD (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl .hole) ?_
      ssimp
      exact poolAns_resumeSnd hg' hP' rfl rfl hv (hret _ _ _ _ ViewsT.empty fun _ => rfl)
        (ResUT.compS_empty_right ρ') (AvoidUnsh.empty _ _) (HoldsIn.empty _ _) hcov hv hF'm hF'M
        (invS_ready (k := k) rfl rfl (fun _ _ _ => ⟨rfl, rfl⟩) hi')
    · simp only at htag hju
      subst htag; subst hju
      refine twp_det hQD (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl .hole) ?_
      ssimp
      exact poolAns_resume hg' hP' hBP (ResUT.compS_empty_right ρ') (AvoidUnsh.empty _ _)
        (HoldsIn.empty _ _) hcov hv hF'm hF'M hi

/-- **`cancel`'s clause**: the stopped task parked; the top ready, it is cancelled, its cancel
branch run under the scheduler, the stopped task kept beneath it (`poolAns_cancelSnd`);
otherwise the stopped task resumed (`poolAns_resume`). -/
theorem cancelCl_ok (N : Nat) :
    SchedClauseTLe (ℍ := ℍ) N HS (PA_S (ℍ := ℍ)) enPark cancelCl := by
  rintro F k w ls O v κ ρ _ _ _ _ _ _ _ ⟨ρa, ρk, hc, ⟨rfl, rfl⟩, hκ⟩
  obtain rfl := compS_empty_left_eq hc
  rw [cerwpTE_iff]
  have hD := valPost_down (poolAns_down (ℍ := ℍ) QS HS InvS)
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ _ (Val.pair Val.unit κ)) rfl .hole) ?_
  refine twp_det hD (fun μ => step1Only_plug (Head.letpair μ Val.unit κ _) rfl .hole) ?_
  simp only [Kont.plug]
  refine twp_here (fun μ => final_val μ ⟨_, .lam⟩) fun w₀ ρ₀ ls₀ O₀ hE hr hl hO => ?_
  refine ⟨⟨_, .lam⟩, rfl, fun j hj => poolAnsAt_iff.mpr ?_⟩
  intro ts Os σ ρ' hi hg hP hc' hσ hρ hH hap hcov hv hls hO' F' hF'm hF'M
  have hκ' := KapSchedT.mask_mono (fun x hx => (recMask_rr hO x).mp hx)
    (KapSchedT.kripke hκ hE hr (KeepRel.of_srecsRR hl _) hO)
  obtain ⟨hP', hg'⟩ := poolAns_park (Inv := InvS) false (fun _ => False) (Val.inj₁ Val.unit) hκ' hj
    hg hP hc' hσ hρ hH (fun _ h => h.elim) hap (CovR.of_compS_left hc' hcov) hls hO'
  have hQD := valPost_down QB_down
  cases j with
  | zero => exact twp_zero
  | succ j₀ =>
  refine twp_step (fun μ => step1Only_plug (Head.beta μ _ (stateVal HS ts)) rfl .hole) ?_
  ssimp
  refine twp_det hQD (fun μ => step1Only_plug (Head.letpair μ HS (poolVal ts) _) rfl .hole) ?_
  ssimp
  have hBP : ∀ c σ' : TRes w₀.K, ViewsT c → (false = false → c = PMap.empty) →
      ResUT.CompS c PMap.empty σ' → enPark.PBv Val.unit j₀ w₀ ls₀ Val.unit σ' := by
    intro c σ' _ hj hcσ
    obtain rfl := hj rfl
    exact ⟨rfl, compS_empty_left_eq hcσ⟩
  cases ts with
  | nil =>
    refine twp_det hQD (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl .hole) ?_
    ssimp
    exact poolAns_resume hg' hP' hBP (ResUT.compS_empty_right ρ') (AvoidUnsh.empty _ _)
      (HoldsIn.empty _ _) hcov hv hF'm hF'M hi
  | cons u ts =>
    obtain ⟨⟨hret, hk⟩, hi'⟩ := invS_cons hi
    obtain ⟨ut, uj, ush, utag⟩ := u
    refine twp_det hQD (fun μ => step1Only_plug
      (Head.case₁ μ (Val.pair (Val.pair utag ut.κ) (poolVal ts)) _ _) rfl .hole) ?_
    ssimp
    refine twp_det hQD (fun μ => step1Only_plug
      (Head.letpair μ (Val.pair utag ut.κ) (poolVal ts) _) rfl .hole) ?_
    ssimp
    refine twp_det hQD (fun μ => step1Only_plug (Head.letpair μ utag ut.κ _) rfl .hole) ?_
    ssimp
    rcases hk with ⟨htag, hju, hq, hf⟩ | ⟨htag, hju⟩
    · simp only at htag hju hq hf
      subst htag; subst hju
      refine twp_det hQD (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl .hole) ?_
      ssimp
      have hH' : ut.H = HS := (hg' _ (List.mem_cons_of_mem _ List.mem_cons_self)).1
      have h := poolAns_cancelSnd hg' hP' rfl rfl (by rw [hq]; decide) hf hcov hv hF'm hF'M
        (invS_ready (k := k) rfl rfl (fun _ _ _ => ⟨rfl, rfl⟩) hi')
      rw [hH'] at h
      exact h
    · simp only at htag hju
      subst htag; subst hju
      refine twp_det hQD (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl .hole) ?_
      ssimp
      exact poolAns_resume hg' hP' hBP (ResUT.compS_empty_right ρ') (AvoidUnsh.empty _ _)
        (HoldsIn.empty _ _) hcov hv hF'm hF'M hi

theorem recsApart_nil_left {K : WCactus} (O : List (FrameRecT K)) : RecsApart ([] : List (FrameRecT K)) O :=
  ⟨fun _ h => (by cases h), fun _ _ h => (by simp [recMask] at h), fun _ h => (by cases h)⟩

/-- **`spawn`'s clause at stops up to `N`**, from the scheduler's clauses below `N`: the spawner
parked as a ready task (`poolAns_park`), the child run under the scheduler beside the stack at an
index below the stop's (`poolAns_run_le`), lifted from its indexed table (`cerwpT_tabAt`). -/
theorem spawnCl_ok (N : Nat)
    (ih : ∀ N', N' < N → SchedOKTLe (ℍ := ℍ) N' (TJ (ℍ := ℍ)) nP qsS stackRet hsS QV (PA_S (ℍ := ℍ))) :
    SchedClauseTLe (ℍ := ℍ) N HS (PA_S (ℍ := ℍ)) (enSpawnP (spawnPA (ℍ := ℍ) (tabAt (ℍ := ℍ))))
      spawnCl := by
  rintro F k w ls O v κ ρ hkN _ _ _ _ _ _ ⟨ρa, ρk, hc, ⟨rfl, hth⟩, hκ⟩
  obtain rfl := compS_empty_left_eq hc
  rw [cerwpTE_iff]
  have hD := valPost_down (poolAns_down (ℍ := ℍ) QS HS InvS)
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ _ (Val.pair v κ)) rfl .hole) ?_
  refine twp_det hD (fun μ => step1Only_plug (Head.letpair μ v κ _) rfl .hole) ?_
  simp only [Kont.plug]
  refine twp_here (fun μ => final_val μ ⟨_, .lam⟩) fun w₀ ρ₀ ls₀ O₀ hE hr hl hO => ?_
  refine ⟨⟨_, .lam⟩, rfl, fun j hj => poolAnsAt_iff.mpr ?_⟩
  intro ts Os σ ρ' hi hg hP hc' hσ hρ hH hap hcov hv hls hO' F' hF'm hF'M
  have hκ' := KapSchedT.mask_mono (fun x hx => (recMask_rr hO x).mp hx)
    (KapSchedT.kripke hκ hE hr (KeepRel.of_srecsRR hl _) hO)
  obtain ⟨hP', hg'⟩ := poolAns_park (Inv := InvS) false (fun _ => False) (Val.inj₁ Val.unit) hκ' hj
    hg hP hc' hσ hρ hH (fun _ h => h.elim) hap (CovR.of_compS_left hc' hcov) hls hO'
  have hQD := valPost_down QB_down
  cases j with
  | zero => exact twp_zero
  | succ j₀ =>
  refine twp_step (fun μ => step1Only_plug (Head.beta μ _ (stateVal HS ts)) rfl .hole) ?_
  ssimp
  refine twp_det hQD (fun μ => step1Only_plug (Head.letpair μ HS (poolVal ts) _) rfl .hole) ?_
  ssimp
  have hE₀ : w.Ext w₀ (PMap.empty : TRes w.K) :=
    TWd.Ext.of_compS_left (ResUT.CompS.comm (ResUT.compS_empty_right _)) hE
  have he := cerwpT_tabAt (hth j₀ (by omega) w₀ PMap.empty ls₀ hE₀ RR.empty
    (fun w ρf => ResUT.Valid ρf) (fdMask (recMask ([] : List (FrameRecT w₀.K))))
    (fun _ _ h => h) (fun _ _ h => fdMask_le (fun x hx => by simp [recMask] at hx) h))
  have h := poolAns_run_le (ih j₀ (by omega)) le_rfl (fun u hu => (hg' u hu).le (by omega))
    (invS_ready (k := k) rfl rfl (fun _ _ _ => ⟨rfl, rfl⟩) hi)
    hP' (ResUT.CompS.comm (ResUT.compS_empty_right ρ')) hcov hv (recsApart_nil_left _)
    (NoneAt.of_false (fun x hx => by simp [recMask] at hx) _) (AvoidUnsh.empty _ _)
    (HoldsIn.empty _ _) (fun _ _ h => h) (fun _ _ h => h) he hF'm (by simpa using hF'M)
  simp only [List.nil_append] at h
  exact h


theorem ChildOK.kripke {T : Nat → OpTabT} {k : Nat} {w w₀ : TWd} {th : Val} {ρ : TRes w.K}
    {ρ₀ : TRes w₀.K} (h : ChildOK (ℍ := ℍ) T k w th ρ) (hE : w.Ext w₀ ρ)
    (hr : RRw (w := w) (w' := w₀) ρ ρ₀) : ChildOK (ℍ := ℍ) T k w₀ th ρ₀ :=
  fun j hj w' ρ' ls' hE' hr' => h j hj w' ρ' ls' (hE.trans hr hE') (RRw.trans hE'.1 hr hr')

theorem ChildOK.le {T : Nat → OpTabT} {k k' : Nat} (hk : k' ≤ k) {w : TWd} {th : Val}
    {ρ : TRes w.K} (h : ChildOK (ℍ := ℍ) T k w th ρ) : ChildOK (ℍ := ℍ) T k' w th ρ :=
  fun j hj => h j (by omega)

theorem TJ_down : ∀ m i en, TJ (ℍ := ℍ) m i = some en →
    ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ → en.PA k w ls v ρ := tabOf_down _

/-- **The unstarted child is a stored task**: `κU H th` at `enU`, holding the child's copies `ρ`,
owning no record. Resumed at `()` it runs `th ()` under the scheduler (`cerwpT_schedHandle_le`,
from the scheduler's clauses below its index); cancelled, it answers `()` holding `ρ`, which the
return clause hands to the nearest joiner. -/
theorem kapSchedT_κU {N : Nat}
    (ih : ∀ N', N' < N → SchedOKTLe (ℍ := ℍ) N' (TJ (ℍ := ℍ)) nP qsS stackRet hsS QV (PA_S (ℍ := ℍ)))
    {kU : Nat} (hkU : kU ≤ N) {w : TWd} {ls : List (SRecT w.K)} {th : Val} {ρ : TRes w.K}
    (hth : ChildOK (ℍ := ℍ) (tabAt (ℍ := ℍ)) kU w th ρ) (hV : ViewsT ρ) :
    KapSchedT (ℍ := ℍ) (PA_S (ℍ := ℍ)) (recMask ([] : List (FrameRecT w.K))) enU HS kU w ls []
      Val.unit (κU HS th) ρ := by
  have hQD := valPost_down (poolAns_down (ℍ := ℍ) QS HS InvS)
  refine ⟨fun h => (by cases h), ?_, ?_⟩
  · intro w' ρ' ls' O' hE hr _ hO k' hk' a σ σ' hB hcσ F' hF'm hF'M
    cases hO
    obtain ⟨rfl, rfl⟩ := hB
    obtain rfl : ρ' = σ' := (compS_empty_right_eq hcσ).symm
    rw [cerwpTE_iff]
    refine twp_det hQD (fun μ => step1Only_plug (Head.beta μ _ (Val.inj₁ Val.unit)) rfl
      (.appL .hole Val.unit)) ?_
    ssimp [κU]
    refine twp_det hQD (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl
      (.appL .hole Val.unit)) ?_
    ssimp
    refine twp_det hQD (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
    ssimp
    have he := cerwpT_tabAt (hth k' hk' w' ρ' ls' hE hr (fun w ρf => ResUT.Valid ρf)
      (fdMask (recMask ([] : List (FrameRecT w'.K)))) (fun _ _ h => h)
      (fun _ _ h => fdMask_le (fun x hx => by simp [recMask] at hx) h))
    exact cerwpT_schedHandle_le (ih k' (by omega)) k' le_rfl (recMask ([] : List (FrameRecT w'.K)))
      F' _ _ w' ls' [] _ ρ' hF'm (fun w'' ρf hf => fdMask_le (fun x hx => by simp [recMask] at hx) (hF'M w'' ρf hf))
      (fun _ h => h) (fun _ _ h => h) (fun _ _ h => h) he
  · intro w' ρ' ls' O' hE hr _ hO _ _ k' hk' F' hF'm hF'M
    cases hO
    rw [cerwpTE_iff]
    have hV' : ViewsT ρ' := hV.rr hr
    have he : cerwpT (ℍ := ℍ) (opTableT (TJ (ℍ := ℍ))) QV (fun w ρf => ResUT.Valid ρf)
        (fdMask (recMask ([] : List (FrameRecT w'.K)))) k' w' ls' []
        (.app (κU HS th).1 (.val (Val.inj₂ Val.unit))) ρ' := by
      have hPD := cerwpPostT_down (Ψ := cerwpTC (ℍ := ℍ) (opTableT (TJ (ℍ := ℍ))) QV
        (fun w ρf => ResUT.Valid ρf) k') (F := fun w ρf => ResUT.Valid ρf) QV_down
        TJ_down
      refine cerwpT_det hPD (fun μ => step1Only_plug (Head.beta μ _ (Val.inj₂ Val.unit)) rfl
        .hole) ?_
      ssimp [κU]
      refine cerwpT_det hPD (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl .hole) ?_
      ssimp
      exact cerwpT_val (v := Val.unit) fun w₀ ρ₀ _ O₀ _ hr₀ _ hO₀ => by
        cases hO₀; exact ⟨rfl, rfl, hV'.rr hr₀⟩
    exact cerwpT_schedHandle_le (ih k' (by omega)) k' le_rfl (recMask ([] : List (FrameRecT w'.K)))
      F' _ _ w' ls' [] _ ρ' hF'm (fun w'' ρf hf => fdMask_le (fun x hx => by simp [recMask] at hx) (hF'M w'' ρf hf))
      (fun _ h => h) (fun _ _ h => h) (fun _ _ h => h) he


/-- **`par`'s clause at stops up to `N`**, from the scheduler's clauses below `N`: the parent
parked as a joiner sharing what it owns or is shared with it (`poolAns_park`), the second child
stored unstarted above it (`kapSchedT_κU`, `poolAns_park`), the first child run under the
scheduler beside the stack (`poolAns_run_le`). Each child's copies sit where the parent shares:
the parent's own `imm` cells sit at its masks or where its nearest joiner shares (the running
task's condition), and it shares exactly those. -/
theorem parCl_ok (N : Nat)
    (ih : ∀ N', N' < N → SchedOKTLe (ℍ := ℍ) N' (TJ (ℍ := ℍ)) nP qsS stackRet hsS QV (PA_S (ℍ := ℍ))) :
    SchedClauseTLe (ℍ := ℍ) N HS (PA_S (ℍ := ℍ)) (enParP (parPA (ℍ := ℍ) (tabAt (ℍ := ℍ))))
      parCl := by
  rintro F k w ls O v κ ρ hkN _ _ _ hcovρ _ _ ⟨ρa, ρk, hc, ⟨th₁, th₂, ρ₁, ρ₂, rfl, h12, hV₁, hV₂,
    hth₁, hth₂⟩, hκ⟩
  rw [cerwpTE_iff]
  have hD := valPost_down (poolAns_down (ℍ := ℍ) QS HS InvS)
  refine twp_det hD (fun μ => step1Only_plug (Head.beta μ _ (Val.pair (Val.pair th₁ th₂) κ)) rfl
    .hole) ?_
  refine twp_det hD (fun μ => step1Only_plug (Head.letpair μ (Val.pair th₁ th₂) κ _) rfl .hole) ?_
  simp only [Kont.plug]
  refine twp_here (fun μ => final_val μ ⟨_, .lam⟩) fun w₀ ρ₀ ls₀ O₀ hE hr hl hO => ?_
  -- the stop's resource re-read: the children's copies and the parent's share
  obtain ⟨ρa₀, ρk₀, hra, hrk, hc₀⟩ := RR.split_retype hE.1 hc hcovρ hE.2 hr
  have hEa := hE.of_compS_left hc
  obtain ⟨ρ₁₀, ρ₂₀, hr₁, hr₂, h12₀⟩ :=
    RR.split_retype hEa.1 h12 (hcovρ.of_compS_left hc) hEa.2 hra
  have hκ' := KapSchedT.mask_mono (fun x hx => (recMask_rr hO x).mp hx)
    (KapSchedT.kripke hκ (hE.of_compS_right hc) hrk (KeepRel.of_srecsRR hl _) hO)
  have hth₁' := hth₁.kripke (hEa.of_compS_left h12) hr₁
  have hth₂' := hth₂.kripke (hEa.of_compS_right h12) hr₂
  refine ⟨⟨_, .lam⟩, rfl, fun j hj => poolAnsAt_iff.mpr ?_⟩
  intro ts Os σ ρ' hi hg hP hc' hσ hρ hH hap hcov hv hls hO' F' hF'm hF'M
  have hv₀ := (ResUT.Valid.split hc' hv).1
  have hva₀ := (ResUT.Valid.split hc₀ hv₀).1
  -- `ρ′ = ρ₁ ● (ρ₂ ● (ρk ● σ))`
  obtain ⟨y, hy₁, hy₂⟩ := (ResUT.CompS.assoc ρa₀ ρk₀ σ ρ').mpr ⟨ρ₀, hc₀, hc'⟩
  obtain ⟨z, hz₁, hz₂⟩ := (ResUT.CompS.assoc ρ₁₀ ρ₂₀ y ρ').mpr ⟨ρa₀, h12₀, hy₂⟩
  let shJ : BoCa.Loc → Prop := fun x => recMask O₀ x ∨ shTop ts x
  -- the parent parked as a joiner sharing `shJ`
  obtain ⟨hPJ, hgJ⟩ := poolAns_park (Inv := InvS) true shJ (Val.inj₂ Val.unit) hκ' hj hg hP hy₁ hσ
    (hρ.of_compS_right hc₀ hv₀) (hH.of_compS_right hc₀ hv₀) (fun _ h => h) hap
    (CovR.of_compS_right hc₀ (CovR.of_compS_left hc' hcov)) hls hO'
  have hshJ : ∀ x, shTop (⟨⟨PA_S (ℍ := ℍ), recMask O₀, enParP (parPA (ℍ := ℍ) (tabAt (ℍ := ℍ))), HS,
      k, Val.pair th₁ th₂, κ⟩, true, shJ, Val.inj₂ Val.unit⟩ :: ts) x ↔ shJ x :=
    shTop_joiner rfl
  -- a child's copies against the stack above the joiner
  have hAv : ∀ {ρc : TRes w₀.K}, (∃ o, ResUT.CompS ρc o ρ₀) →
      AvoidUnsh shJ (O₀ ++ Os) ρc ∧ HoldsIn shJ [] ρc := by
    rintro ρc ⟨o, ho⟩
    refine ⟨fun q hq hn => ?_, fun τ hτ x ψ e k => ?_⟩
    · rcases List.mem_append.mp hq with hq | hq
      · exact (hn (Or.inl ⟨q, hq, Or.inl rfl⟩)).elim
      · exact (hρ.of_compS_left ho hv₀) q hq fun h => hn (Or.inr h)
    · exact Or.inr ((hH.of_compS_left ho hv₀) τ hτ x ψ e k)
  obtain ⟨o₁, ho₁⟩ : ∃ o, ResUT.CompS ρ₁₀ o ρ₀ := by
    obtain ⟨x, hx₁, hx₂⟩ := (ResUT.CompS.assoc ρ₁₀ ρ₂₀ ρk₀ ρ₀).mpr ⟨ρa₀, h12₀, hc₀⟩
    exact ⟨x, hx₂⟩
  obtain ⟨o₂, ho₂⟩ : ∃ o, ResUT.CompS ρ₂₀ o ρ₀ := by
    obtain ⟨x, hx₁, hx₂⟩ := (ResUT.CompS.assoc ρ₂₀ ρ₁₀ ρk₀ ρ₀).mpr
      ⟨ρa₀, ResUT.CompS.comm h12₀, hc₀⟩
    exact ⟨x, hx₂⟩
  have hvz := (ResUT.Valid.split hz₂ hv).2
  have hvy := (ResUT.Valid.split hz₁ hvz).2
  have hcovz := CovR.of_compS_right hz₂ hcov
  -- the second child stored unstarted above the joiner
  have hκU := kapSchedT_κU (ls := ls₀) ih (kU := j) (by omega) (hth₂'.le hj) (hV₂.rr hr₂)
  obtain ⟨hPU, hgU⟩ := poolAns_park (Inv := InvS) false (fun _ => False) (Val.inj₁ Val.unit) hκU
    le_rfl hgJ hPJ hz₁ (NoneAt.of_false (fun x hx => by simp [recMask] at hx) _)
    (((hAv ⟨o₂, ho₂⟩).1).mono fun x hx => (hshJ x).mpr hx)
    (((hAv ⟨o₂, ho₂⟩).2).mono fun x hx => (hshJ x).mpr hx) (fun _ h => h.elim)
    (recsApart_nil_left _) (CovR.of_compS_left hz₁ hcovz) hls (fun _ h => by cases h)
  have hQD := valPost_down QB_down
  cases j with
  | zero => exact twp_zero
  | succ j₀ =>
  refine twp_step (fun μ => step1Only_plug (Head.beta μ _ (stateVal HS ts)) rfl .hole) ?_
  ssimp
  refine twp_det hQD (fun μ => step1Only_plug (Head.letpair μ HS (poolVal ts) _) rfl .hole) ?_
  ssimp
  refine twp_det hQD (fun μ => step1Only_plug (Head.letpair μ th₁ th₂ _) rfl .hole) ?_
  ssimp
  have hEc : w₀.Ext w₀ ρ₁₀ := TWd.Ext.refl _ _
  have he := cerwpT_tabAt (hth₁' j₀ (by omega) w₀ ρ₁₀ ls₀ (TWd.Ext.refl _ _)
    (RR.refl (CovR.of_compS_left hz₂ hcov)) (fun w ρf => ResUT.Valid ρf)
    (fdMask (recMask ([] : List (FrameRecT w₀.K)))) (fun _ _ h => h)
    (fun _ _ h => fdMask_le (fun x hx => by simp [recMask] at hx) h))
  have hiU : InvS (⟨⟨PA_S (ℍ := ℍ), recMask ([] : List (FrameRecT w₀.K)), enU, HS, j₀ + 1, Val.unit,
      κU HS th₂⟩, false, fun _ => False, Val.inj₁ Val.unit⟩ ::
      ⟨⟨PA_S (ℍ := ℍ), recMask O₀, enParP (parPA (ℍ := ℍ) (tabAt (ℍ := ℍ))), HS, k,
        Val.pair th₁ th₂, κ⟩, true, shJ, Val.inj₂ Val.unit⟩ :: ts) := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨fun k w ls c _ hj => by rw [hj rfl]; exact ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨fun k w ls c hc _ => ⟨rfl, hc⟩, Or.inr ⟨rfl, rfl⟩⟩
    · exact hi x hx
  have hshU : ∀ x, shTop (⟨⟨PA_S (ℍ := ℍ), recMask ([] : List (FrameRecT w₀.K)), enU, HS, j₀ + 1,
      Val.unit, κU HS th₂⟩, false, fun _ => False, Val.inj₁ Val.unit⟩ ::
      ⟨⟨PA_S (ℍ := ℍ), recMask O₀, enParP (parPA (ℍ := ℍ) (tabAt (ℍ := ℍ))), HS, k,
        Val.pair th₁ th₂, κ⟩, true, shJ, Val.inj₂ Val.unit⟩ :: ts) x ↔ shJ x :=
    fun x => (shTop_ready rfl x).trans (hshJ x)
  have h := poolAns_run_le (ih j₀ (by omega)) le_rfl (fun u hu => (hgU u hu).le (by omega)) hiU
    hPU hz₂ hcov hv (recsApart_nil_left _)
    (NoneAt.of_false (fun x hx => by simp [recMask] at hx) _)
    (((hAv ⟨o₁, ho₁⟩).1).mono fun x hx => (hshU x).mpr hx)
    (((hAv ⟨o₁, ho₁⟩).2).mono fun x hx => (hshU x).mpr hx)
    (fun _ _ h => h) (fun _ _ h => h) he hF'm (by simpa using hF'M)
  simp only [List.nil_append] at h
  exact h


/-- **The scheduler meets its clauses at stops up to every `N`**, by strong induction on `N`. -/
theorem hs_schedOKLe : ∀ N, SchedOKTLe (ℍ := ℍ) N (TJ (ℍ := ℍ)) nP qsS stackRet hsS QV
    (PA_S (ℍ := ℍ)) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  refine ⟨fun m i hm => by simp [TJ, tabOf, hm], fun i en h _ => ?_, fun i en h v w O ρf hj => ?_,
    poolAns_down _ _ _, fun F k w ls O v ρ _ =>
      stackRet_okAt (fun t ts hi => ⟨(invS_cons hi).1.1, (invS_cons hi).2⟩) F k w ls O v ρ,
    fun i en h => ?_⟩
  · obtain ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := tabOf_some h <;> rfl
  · obtain ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := tabOf_some h <;> exact hj
  · obtain ⟨-, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := tabOf_some h
    · exact ⟨parkCl, by simp [clauseAt, hsS, Val.pair, parkCl, clauseOf, Val.lam, IsVal.lam],
        parkCl_ok N⟩
    · exact ⟨spawnCl, by simp [clauseAt, hsS, Val.pair, spawnCl, clauseOf, Val.lam, IsVal.lam],
        spawnCl_ok N ih⟩
    · exact ⟨cancelCl, by simp [clauseAt, hsS, Val.pair, cancelCl, clauseOf, Val.lam, IsVal.lam],
        cancelCl_ok N⟩
    · exact ⟨parCl, by simp [clauseAt, hsS, Val.pair, parCl, clauseOf, Val.lam, IsVal.lam],
        parCl_ok N ih⟩

/-- **The scheduler meets `SchedOKT`** with its answers functions of its stack, for every stack. -/
theorem hs_schedOK : SchedOKT (ℍ := ℍ) (TJ (ℍ := ℍ)) nP qsS stackRet hsS QV (PA_S (ℍ := ℍ)) :=
  schedOKT_of_le hs_schedOKLe

end BoCa.Fig16.Tree.Wp.SchedProgs.Spawn

end
