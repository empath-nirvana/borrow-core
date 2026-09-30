import Core.Steps
import Core.CommonList

/-!
# Core — every run  `[spec §13]`

`wpTS` asks for a run under every allocator (`Core/Alloc.lean`).  That covers every run of the
machine:

* **Determinism.**  A step under an allocator is determined by the configuration and the
  allocation count (`AStep1.deterministic`): the machine decomposes a term uniquely (`plug_decomp`), every
  head step but `alloc` and `tab` is a function of the memory and the redex (the host is a
  function), and those two take the allocator's location.
* **Replay.**  Every run is a run under the allocator that replays its choices
  (`Alloc.replay`, `steps_replay`).
* **Prefix.**  A run under an allocator is a prefix of every run under it that reaches a value
  (`ARun.rest`).

So the run `wpTS` gives under the replaying allocator continues the given run
(`wpTS_demonic`): **every** run of a term `wpTS` holds of continues to a value run whose
end lands in the postcondition.  That is `wpTSD`, the demonic `wp`: no run is stuck, and every
run that reaches a value lands in the postcondition.  It is partial correctness plus safety, so
it admits divergence; every term the relation holds of also terminates under every allocator.

`fundamentalD` is the Fundamental Property at `wpTSD`, and `adequacyD` its closed instance: every
run of a closed `F 1` program from empty memory continues to `()` at empty memory.
`mapProgC_every_run` is the instance at a program whose `withswap` callback frees the payload the
lent cell still names and allocates: under an allocator that reuses the freed location, the cell
names the new node until `withswap` overwrites it, and the run is still safe and leak-free.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc AHead AStep1 ARun Step1N)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Determinism -/

/-- A head step that allocates nothing is a function of the memory and the redex. -/
theorem head_det {μ μ₁ μ₂ : Heap} {a a₁ a₂ : Expr} (h₁ : Head μ a μ₁ a₁)
    (hn : a.allocs = false) : ∀ {x : Expr}, Head μ x μ₂ a₂ → a = x → μ₁ = μ₂ ∧ a₁ = a₂ := by
  intro x h₂ hx
  by_cases hE : EffRedex a
  · exact head_det_eff h₁ hE h₂ hx
  cases h₁ <;> (try (exfalso; apply hE; first
    | exact .inl ⟨_, _, rfl⟩ | exact .inr (.inl ⟨_, _, rfl⟩) | exact .inr (.inr (.inl ⟨_, rfl⟩))
    | exact .inr (.inr (.inr ⟨_, _, rfl⟩)))) <;>
    cases h₂ <;> simp [Expr.allocs] at hn hx ⊢
  all_goals (try simp only [Expr.val, ← Subtype.ext_iff] at hx)
  all_goals (try simp only [Expr.val, ← Subtype.ext_iff])
  all_goals (try obtain ⟨hx₁, hx₂⟩ := hx)
  all_goals (try subst_vars)
  all_goals first
    | rfl
    | (obtain ⟨rfl, rfl⟩ := hx₁; rfl)
    | (obtain ⟨rfl, rfl⟩ := hx₂; rfl)
    | (obtain ⟨rfl, rfl⟩ := Val.arr_inj hx₁
       have hi := congrArg Subtype.val hx₂
       simp only [Val.i32, Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq] at hi
       subst hi
       try rfl)
    | (obtain ⟨hn, hi, rfl⟩ := hx₂
       have hn' := congrArg Subtype.val hn
       have hi' := congrArg Subtype.val hi
       simp only [Val.i32, Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq] at hn' hi'
       subst hn' hi'
       rfl)
    | simp_all

theorem _root_.BoCa.BoLo.AHead.det_aux {A : Alloc} {k k₁ k₂ : Nat} {μ μ₁ μ₂ : Heap} {a a₁ a₂ x : Expr}
    (h₁ : AHead (ℍ := ℍ) A k μ a k₁ μ₁ a₁) (h₂ : AHead (ℍ := ℍ) A k μ x k₂ μ₂ a₂) (hx : a = x) :
    k₁ = k₂ ∧ μ₁ = μ₂ ∧ a₁ = a₂ := by
  cases h₁ with
  | det h hn =>
      cases h₂ with
      | det h' _ => exact ⟨rfl, head_det h hn h' hx⟩
      | alloc v _ => subst hx; simp [Expr.allocs] at hn
      | tab c f _ => subst hx; simp [Expr.allocs] at hn
  | alloc v h =>
      cases h₂ with
      | det h' hn => subst hx; simp [Expr.allocs] at hn
      | alloc v' _ =>
          simp only [Expr.val, Expr.app.injEq, true_and] at hx
          obtain rfl : v = v' := Subtype.ext hx
          exact ⟨rfl, rfl, rfl⟩
      | tab c f _ => simp [Expr.val, Val.prim] at hx
  | tab c f h =>
      cases h₂ with
      | det h' hn => subst hx; simp [Expr.allocs] at hn
      | alloc v' _ => simp [Expr.val, Val.prim] at hx
      | tab c' f' _ =>
          simp only [Expr.val, Expr.app.injEq, true_and, Val.pair, Expr.pair.injEq] at hx
          obtain ⟨hc, hf⟩ := hx
          obtain rfl : f = f' := Subtype.ext hf
          simp only [Val.i32, Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq] at hc
          subst hc
          exact ⟨rfl, rfl, rfl⟩

/-- A head step under an allocator is a function of the count, the memory and the redex. -/
theorem _root_.BoCa.BoLo.AHead.deterministic {A : Alloc} {k k₁ k₂ : Nat} {μ μ₁ μ₂ : Heap} {a a₁ a₂ : Expr}
    (h₁ : AHead (ℍ := ℍ) A k μ a k₁ μ₁ a₁) (h₂ : AHead (ℍ := ℍ) A k μ a k₂ μ₂ a₂) :
    k₁ = k₂ ∧ μ₁ = μ₂ ∧ a₁ = a₂ :=
  AHead.det_aux h₁ h₂ rfl

/-- A step under an allocator is a function of the count, the memory and the term. -/
theorem _root_.BoCa.BoLo.AStep1.deterministic {A : Alloc} {k k₁ k₂ : Nat} {μ μ₁ μ₂ : Heap} {e e₁ e₂ : Expr}
    (h₁ : AStep1 (ℍ := ℍ) A k μ e k₁ μ₁ e₁) (h₂ : AStep1 (ℍ := ℍ) A k μ e k₂ μ₂ e₂) :
    k₁ = k₂ ∧ μ₁ = μ₂ ∧ e₁ = e₂ := by
  obtain ⟨K₁, a₁, a₁', rfl, rfl, hh₁⟩ := h₁
  obtain ⟨K₂, a₂, a₂', he, rfl, hh₂⟩ := h₂
  obtain ⟨rfl, rfl⟩ := plug_decomp hh₂.toHead K₁ K₂ hh₁.toHead he
  obtain ⟨rfl, rfl, rfl⟩ := AHead.deterministic hh₁ hh₂
  exact ⟨rfl, rfl, rfl⟩

theorem _root_.BoCa.BoLo.AStep1.not_val {A : Alloc} {k k' : Nat} {μ μ' : Heap} {w : Val} {e' : Expr}
    (h : AStep1 (ℍ := ℍ) A k μ (.val w) k' μ' e') : False :=
  BoCa.BoLo.no_step_val h.toStep1

/-- **Prefix.**  A run under an allocator is continued, under it, by every run under it that
reaches a value. -/
theorem _root_.BoCa.BoLo.ARun.rest {A : Alloc} {i j j₁ : Nat} {μ μ' μ₁ : Heap} {e e₁ : Expr} {v : Val}
    (h' : ARun (ℍ := ℍ) A i μ e j₁ μ₁ e₁) :
    ARun (ℍ := ℍ) A i μ e j μ' (.val v) → ARun (ℍ := ℍ) A j₁ μ₁ e₁ j μ' (.val v) := by
  induction h' with
  | refl => exact id
  | more s' _ ih =>
      intro h
      cases h with
      | refl => exact (AStep1.not_val s').elim
      | more s t =>
          obtain ⟨rfl, rfl, rfl⟩ := AStep1.deterministic s s'
          exact ih t

/-! ### Replay -/

/-- `A` answers the `j`-th of the choices `cs` from count `i`, wherever that choice is free. -/
def Agree (A : Alloc) (i : Nat) (cs : List Loc) : Prop :=
  ∀ j, j < cs.length → ∀ (μ : Heap) (n : Nat), (∀ m, m < n → μ (cs.getD j 0 + m) = none) →
    A.pick (i + j) μ n = cs.getD j 0

theorem Agree.tail {A : Alloc} {i : Nat} {ℓ : Loc} {cs : List Loc} (h : Agree A i (ℓ :: cs)) :
    Agree A (i + 1) cs := by
  intro j hj μ n hfree
  have := h (j + 1) (by simp; omega) μ n (by simpa using hfree)
  rw [show i + 1 + j = i + (j + 1) by omega, this]
  simp

theorem Agree.head {A : Alloc} {i : Nat} {ℓ : Loc} {cs : List Loc} (h : Agree A i (ℓ :: cs))
    {μ : Heap} {n : Nat} (hfree : ∀ m, m < n → μ (ℓ + m) = none) : A.pick i μ n = ℓ := by
  simpa using h 0 (by simp) μ n (by simpa using hfree)

/-- **Every run is an allocator run**: of every allocator that answers its choices. -/
theorem steps_replay {μ μ' : Heap} {e e' : Expr} (hs : Steps μ e μ' e') :
    ∃ cs : List Loc, ∀ (A : Alloc) (i : Nat), Agree A i cs →
      ARun (ℍ := ℍ) A i μ e (i + cs.length) μ' e' := by
  induction hs with
  | refl μ e => exact ⟨[], fun A i _ => .refl _ _ _⟩
  | @more μ μ₁ μ' e e₁ e' h _ ih =>
      obtain ⟨cs, hcs⟩ := ih
      obtain ⟨K, a, a', rfl, rfl, hh⟩ := h
      cases hal : a.allocs with
      | false =>
          exact ⟨cs, fun A i hA => .more ⟨K, a, a', rfl, rfl, .det hh hal⟩ (hcs A i hA)⟩
      | true =>
          cases hh with
          | alloc v ℓ hl =>
              refine ⟨ℓ :: cs, fun A i hA => ?_⟩
              have hp : A.pick i μ 1 = ℓ := hA.head (fun m hm => by
                rw [show m = 0 by omega, Nat.add_zero]; exact hl)
              have hstep : AStep1 (ℍ := ℍ) A i μ (K.plug (.app (.val (.prim .alloc)) (.val v)))
                  (i + 1) (μ.upd ℓ v) (K.plug (.val (.loc ℓ))) := by
                have := AHead.alloc (ℍ := ℍ) (A := A) i μ v (by rw [hp]; exact hl)
                rw [hp] at this
                exact ⟨K, _, _, rfl, rfl, this⟩
              have := ARun.more hstep (hcs A (i + 1) hA.tail)
              rwa [show i + 1 + cs.length = i + (ℓ :: cs).length by simp; omega] at this
          | tab c f ℓ hl =>
              refine ⟨ℓ :: cs, fun A i hA => ?_⟩
              have hp : A.pick i μ (arrLen c).toNat = ℓ := hA.head hl
              have hstep : AStep1 (ℍ := ℍ) A i μ
                  (K.plug (.app (.val (.prim .tab)) (.val (.pair (.i32 c) f)))) (i + 1)
                  (μ.fill ℓ (arrLen c).toNat .unit)
                  (K.plug (tabFill f ℓ (arrLen c) 0 (arrLen c).toNat)) := by
                have := AHead.tab (ℍ := ℍ) (A := A) i μ c f (by rw [hp]; exact hl)
                rw [hp] at this
                exact ⟨K, _, _, rfl, rfl, this⟩
              have := ARun.more hstep (hcs A (i + 1) hA.tail)
              rwa [show i + 1 + cs.length = i + (ℓ :: cs).length by simp; omega] at this
          | _ => simp [Expr.allocs, BoLo.hndE, BoLo.ubindE, BoLo.ccatchE, BoLo.cfinE] at hal

open Classical in
/-- The allocator that answers the choices `cs` in order, wherever they are free, and the
least free block otherwise.  `[spec §13]` -/
def Alloc.replay (cs : List Loc) : Alloc where
  pick k μ n := if k < cs.length ∧ ∀ m, m < n → μ (cs.getD k 0 + m) = none then cs.getD k 0
    else Alloc.leastFree.pick k μ n
  fresh k μ n hfin i hi := by
    split
    · next h => exact h.2 i hi
    · exact Alloc.leastFree.fresh k μ n hfin i hi

theorem Alloc.replay_agree (cs : List Loc) : Agree (Alloc.replay cs) 0 cs := by
  intro j hj μ n hfree
  simp only [Alloc.replay, Nat.zero_add]
  rw [if_pos ⟨hj, hfree⟩]

/-! ### The demonic `wp` -/

/-- **The demonic `wp`**: from every configuration `wpTS` quantifies over, every run of `e`
continues to a value run whose end is a post-configuration of `wpTS`'s shape at which `Q` holds.
`[spec §13]` -/
def wpTSD (ls : List SRec) (e : Expr) (Q : List SRec → Val → WProp) : WProp := fun ρ =>
  ∀ (ρf fρ : WRes) (ps : List FrameRec), ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ →
    TW fρ ps (rsOf ls) → Tagged fρ ps ls → ∀ (μ : Heap), ResU.Lower fρ μ →
    ∀ (μ₁ : Heap) (e₁ : Expr), Steps μ e μ₁ e₁ →
    ∃ (ρ' ρp fρ' fρ'p π : WRes) (v : Val) (μ' : Heap) (ps' : List FrameRec)
      (ls' : List SRec),
      ResU.Hash ρ' ρf ∧
      ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧
      ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧
      Steps μ₁ e₁ μ' (.val v) ∧
      ResU.CompS ρ' ρp π ∧ ResU.UpdV ρ π ∧
      NoOwn ρp ∧
      TW fρ'p ps' (rsOf ls') ∧ Tagged fρ'p ps' ls' ∧
      (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls) ∧ Q ls' v ρ'

/-- **`wpTS` is demonic**: the run under the allocator that replays a given run continues it.
`[spec §13]` -/
theorem wpTS_demonic {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp} :
    Entails (wpTS ls e Q) (wpTSD ls e Q) := by
  intro ρ hw ρf fρ ps hf hc hT htg μ hμ μ₁ e₁ hs
  obtain ⟨cs, hcs⟩ := steps_replay hs
  have hrun := hcs (Alloc.replay cs) 0 (Alloc.replay_agree cs)
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ₀, μ', ps', ls', h₁, h₂, h₃, h₅, h₆, h₇, ⟨j, h₈⟩, h₉, hA, hB,
    hT', htg', hps, hls, hC⟩ := hw ρf fρ ps hf hc hT htg (Alloc.replay cs) 0
  obtain rfl := ResU.Lower.functional h₅ hμ
  exact ⟨ρ', ρp, fρ', fρ'p, π, v, μ', ps', ls', h₁, h₂, h₃, h₆, h₇, (hrun.rest h₈).toSteps, h₉,
    hA, hB, hT', htg', hps, hls, hC⟩

/-- **No stuck state**: under `wpTSD`, every run ends at a value or can step. -/
theorem wpTSD_safe {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp} {ρ ρf fρ : WRes}
    {ps : List FrameRec} (hw : wpTSD ls e Q ρ) (hf : ResU.Hash ρf ρ) (hc : ResU.CompS ρf ρ fρ)
    (hT : TW fρ ps (rsOf ls)) (htg : Tagged fρ ps ls) {μ μ₁ : Heap} (hμ : ResU.Lower fρ μ)
    {e₁ : Expr} (hs : Steps μ e μ₁ e₁) :
    IsVal e₁ ∨ ∃ μ₂ e₂, Step1 μ₁ e₁ μ₂ e₂ := by
  obtain ⟨_, _, _, _, _, v, _, _, _, -, -, -, -, -, h, -⟩ := hw ρf fρ ps hf hc hT htg μ hμ μ₁ e₁ hs
  cases h with
  | refl => exact .inl v.2
  | more h _ => exact .inr ⟨_, _, h⟩

/-- **Every value run lands in the postcondition**: under `wpTSD`, a run that reaches a value
reaches a post-configuration at which `Q` holds, lowered to the run's final memory. -/
theorem wpTSD_val {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp} {ρ ρf fρ : WRes}
    {ps : List FrameRec} (hw : wpTSD ls e Q ρ) (hf : ResU.Hash ρf ρ) (hc : ResU.CompS ρf ρ fρ)
    (hT : TW fρ ps (rsOf ls)) (htg : Tagged fρ ps ls) {μ μ₁ : Heap} (hμ : ResU.Lower fρ μ)
    {w : Val} (hs : Steps μ e μ₁ (.val w)) :
    ∃ (ρ' ρp fρ' fρ'p π : WRes) (ps' : List FrameRec) (ls' : List SRec),
      ResU.Hash ρ' ρf ∧ ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧
      ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ₁ ∧
      ResU.CompS ρ' ρp π ∧ ResU.UpdV ρ π ∧ NoOwn ρp ∧
      TW fρ'p ps' (rsOf ls') ∧ Tagged fρ'p ps' ls' ∧
      (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls) ∧ Q ls' w ρ' := by
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ', ps', ls', h₁, h₂, h₃, h₆, h₇, h₈, h₉, hA, hB, hT', htg',
    hps, hls, hC⟩ := hw ρf fρ ps hf hc hT htg μ hμ μ₁ _ hs
  obtain ⟨rfl, hv⟩ := steps_from_val h₈
  subst hv
  exact ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', h₁, h₂, h₃, h₆, h₇, h₉, hA, hB, hT', htg', hps, hls, hC⟩

/-! ### The Fundamental Property and adequacy at `wpTSD` -/

/-- **Fundamental Property at the demonic `wp`**: a computation of `F A` satisfies `wpTSD` at
`𝒱⟦A⟧` from every closing substitution.  `[spec §13]` -/
theorem fundamentalD {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {A : VTy}
    (h : CDerives Δ Γ e (.comp (.ret A))) {δ : LSub} {γ : List Val} {ls : List SRec} {ρ : WRes}
    (hδ : Δ.Models δ) (hg : gDenC ls δ Γ γ ρ) :
    wpTSD ls (substAll γ e) (fun ls'' => vC true A ls'' δ) ρ :=
  wpTS_demonic ρ (fundamentalC h δ γ ls ρ hδ hg)

/-- `[CONF]` Theorem 3.2 at the demonic `wp`: every run from the empty memory continues to a
value satisfying `P` at the empty memory.  `[spec §13]` -/
theorem theorem32D (e : Expr) (P : Val → Prop)
    (hwp : wpTS [] e (fun _ v => Fig16.BoLo.pure (P v)) (PMap.empty : WRes))
    {μ₁ : Heap} {e₁ : Expr} (hs : Steps Adequacy.emptyMem e μ₁ e₁) :
    ∃ v : Val, Steps μ₁ e₁ Adequacy.emptyMem (.val v) ∧ P v := by
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ', -, -, h1, h2, h3, h6, h7, h8, h9, h10, h11, -, -, -, -,
    h12⟩ :=
    wpTS_demonic _ hwp PMap.empty PMap.empty [] Fig16.LogRel.hash_empty
      (ResU.comp_empty_right _) TW.empty htg _ Fig16.BoLo.lower_empty μ₁ e₁ hs
  obtain ⟨hρ'e, hPv⟩ := h12
  subst hρ'e
  obtain rfl : (PMap.empty : WRes) = fρ' := ResU.eq_of_comp_empty_left h2
  obtain rfl : ρp = fρ'p := ResU.eq_of_comp_empty_left h6
  obtain rfl : ρp = π := ResU.eq_of_comp_empty_left h9
  obtain rfl : ρp = PMap.empty := reclaim ρp h10 h11
  obtain rfl : μ' = (fun _ => none) := ResU.Lower.functional h7 Fig16.BoLo.lower_empty
  exact ⟨v, h8, hPv⟩

/-- **Adequacy at the demonic `wp`**: every run of a closed computation of type `F 1` from the
empty memory continues to `()` at the empty memory.  `[spec §13]` -/
theorem adequacyD {e : Expr} (h : CDerives LifeCtx.empty [] e (.comp (.ret .unit)))
    {μ₁ : Heap} {e₁ : Expr} (hs : Steps Adequacy.emptyMem e μ₁ e₁) :
    Steps μ₁ e₁ Adequacy.emptyMem (.val .unit) := by
  have hwp := fundamentalC h LSub.empty [] [] PMap.empty Adequacy.models_empty (gDenC_nil _ _)
  have hwp' : wpTS [] e (fun _ v => Fig16.BoLo.pure (v = Val.unit)) (PMap.empty : WRes) := by
    have he : substAll [] e = e := Adequacy.psub_nil 0 e
    rw [he] at hwp
    exact hwp
  obtain ⟨v, hsteps, rfl⟩ := theorem32D e (· = Val.unit) hwp' hs
  exact hsteps

/-- **No stuck state**: no run of a closed `F 1` program from the empty memory is stuck.
`[spec §13]` -/
theorem adequacyD_safe {e : Expr} (h : CDerives LifeCtx.empty [] e (.comp (.ret .unit)))
    {μ₁ : Heap} {e₁ : Expr} (hs : Steps Adequacy.emptyMem e μ₁ e₁) :
    IsVal e₁ ∨ ∃ μ₂ e₂, Step1 μ₁ e₁ μ₂ e₂ := by
  cases adequacyD h hs with
  | refl => exact .inl Val.unit.2
  | more h _ => exact .inr ⟨_, _, h⟩

/-- **Every value run is correct**: a run of a closed `F 1` program from the empty memory that
reaches a value reaches `()` at the empty memory.  `[spec §13]` -/
theorem adequacyD_val {e : Expr} (h : CDerives LifeCtx.empty [] e (.comp (.ret .unit)))
    {μ₁ : Heap} {w : Val} (hs : Steps Adequacy.emptyMem e μ₁ (.val w)) :
    w = Val.unit ∧ μ₁ = Adequacy.emptyMem := by
  obtain ⟨h₁, h₂⟩ := steps_from_val (adequacyD h hs)
  exact ⟨h₂.symm, h₁.symm⟩

/-! ### The `withswap` window -/

/-- **The `withswap` window, under every allocator.**  `mapProgC` borrows a cell holding a list
mutably and runs `withswap` with a callback that frees every node and allocates a fresh one
(`mapIncCE`, a `foldOwn`).  While the callback runs, the lent cell still names the old head
node; an allocator that reuses freed locations may give that location to a new node.  Every
run, under every allocator, continues to a pure list at the empty memory.  `[spec §13]` -/
theorem mapProgC_every_run {μ₁ : Heap} {e₁ : Expr} (hs : Steps Adequacy.emptyMem mapProgC μ₁ e₁) :
    ∃ v, PureOut v ∧ Steps μ₁ e₁ Adequacy.emptyMem (.val v) := by
  have hwp : wpTS [] mapProgC (fun _ v => Fig16.BoLo.pure (PureOut v)) (PMap.empty : WRes) := by
    refine wpTS_mono (fun ls v ρ hv => ?_) PMap.empty (wp_of_derives mapProgC_derives)
    have e := vC_pureL_empty (sizeOf v.1 + 1) (Nat.lt_succ_self _) hv
    subst e
    exact ⟨rfl, true, ls, LSub.empty, hv⟩
  obtain ⟨v, hsteps, hv⟩ := theorem32D mapProgC PureOut hwp hs
  exact ⟨v, hv, hsteps⟩

end BoCa.Fig16.LogRel.Core

end
