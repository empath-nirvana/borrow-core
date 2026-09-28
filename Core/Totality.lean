import Core.Demonic

/-!
# Core — totality  `[spec §14]`

A closed computation of `F A` terminates on every run.  The Fundamental Property gives `wpTS`,
whose run is taken under every allocator, so:

* **Every allocator** (`total_every_alloc`): under every allocator, from every allocation count,
  the run from the empty memory reaches a value.
* **Bounded** (`total_run_prefix`): every run under an allocator is a prefix of that value run
  (`ARun.rest`).
* **Every run** (`total_every_run`): every run of the machine continues to a value, because it is
  a run under the allocator that replays its choices (`steps_replay`).
* **No infinite run** (`total_no_infinite_run`): an infinite run of the machine is an infinite
  run under one allocator, the one that answers each allocation count with the location the run
  chose at the step of that count (`Alloc.ofRun`).  Under an allocator the machine is
  deterministic (`AStep1.deterministic`), so that run would pass through the value run of
  `total_every_alloc`, and a value takes no step.

A computation of `U (Loop A B)`, which may diverge, is observed through `F`: `driveE n` makes it
a closed `F (A ⊕ B)` program for every `n` (SPEC §7), and these theorems apply to that program.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc AHead AStep1 ARun Step1N)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Every allocator -/

/-- **Totality under every allocator.**  A closed computation of `F A`, run from the empty memory
under any allocator from any allocation count, reaches a value.  `[spec §14]` -/
theorem total_every_alloc {e : Expr} {A : VTy} (h : CDerives LifeCtx.empty [] e (.comp (.ret A)))
    (Al : Alloc) (k : Nat) :
    ∃ (k' : Nat) (μ' : Heap) (v : Val), ARun (ℍ := ℍ) Al k Adequacy.emptyMem e k' μ' (.val v) := by
  have hwp := fundamentalC (ℍ := ℍ) h LSub.empty [] [] PMap.empty Adequacy.models_empty
    (gDenC_nil _ _)
  have he : substAll [] e = e := Adequacy.psub_nil 0 e
  rw [he] at hwp
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  obtain ⟨-, -, -, -, -, v, μ, μ', -, -, -, -, -, h4, -, -, ⟨k', hrun⟩, -⟩ :=
    hwp PMap.empty PMap.empty [] Fig16.LogRel.hash_empty (ResU.comp_empty_right _) TW.empty htg
      Al k
  obtain rfl : μ = (fun _ => none) := ResU.Lower.functional h4 Fig16.BoLo.lower_empty
  exact ⟨k', μ', v, hrun⟩

/-- **Every run under an allocator is bounded**: it is a prefix of the value run, which it
continues to.  `[spec §14]` -/
theorem total_run_prefix {e : Expr} {A : VTy} (h : CDerives LifeCtx.empty [] e (.comp (.ret A)))
    (Al : Alloc) {k j : Nat} {μ₁ : Heap} {e₁ : Expr}
    (hr : ARun (ℍ := ℍ) Al k Adequacy.emptyMem e j μ₁ e₁) :
    ∃ (k' : Nat) (μ' : Heap) (v : Val), ARun (ℍ := ℍ) Al j μ₁ e₁ k' μ' (.val v) := by
  obtain ⟨k', μ', v, hv⟩ := total_every_alloc (ℍ := ℍ) h Al k
  exact ⟨k', μ', v, hr.rest hv⟩

/-- **Every run continues to a value.**  `[spec §14]` -/
theorem total_every_run {e : Expr} {A : VTy} (h : CDerives LifeCtx.empty [] e (.comp (.ret A)))
    {μ₁ : Heap} {e₁ : Expr} (hs : Steps (ℍ := ℍ) Adequacy.emptyMem e μ₁ e₁) :
    ∃ (μ' : Heap) (v : Val), Steps (ℍ := ℍ) μ₁ e₁ μ' (.val v) := by
  obtain ⟨cs, hcs⟩ := steps_replay hs
  obtain ⟨_, μ', v, hv⟩ := total_run_prefix h (Alloc.replay cs) (hcs _ 0 (Alloc.replay_agree cs))
  exact ⟨μ', v, hv.toSteps⟩

/-! ### No infinite run -/

/-- No infinite run under an allocator passes through a configuration with a value run. -/
theorem ARun.no_infinite {Al : Alloc} {k k' : Nat} {μ μ' : Heap} {e : Expr} {v : Val}
    (hr : ARun (ℍ := ℍ) Al k μ e k' μ' (.val v)) :
    ∀ g : ℕ → Nat × Heap × Expr, g 0 = (k, μ, e) →
      (∀ n, AStep1 (ℍ := ℍ) Al (g n).1 (g n).2.1 (g n).2.2 (g (n + 1)).1 (g (n + 1)).2.1
        (g (n + 1)).2.2) → False := by
  generalize hx : Expr.val v = x at hr
  induction hr with
  | refl =>
      intro g h0 hg
      have := hg 0
      rw [h0, ← hx] at this
      exact AStep1.not_val this
  | more s _ ih =>
      intro g h0 hg
      have h1 := hg 0
      rw [h0] at h1
      obtain ⟨hk, hμ, he⟩ := AStep1.deterministic s h1
      exact ih hx (fun n => g (n + 1))
        (by simp only [hk, hμ, he]) (fun n => hg (n + 1))

/-- The head step `a ↦ a'` from `μ` to `μ'` allocates a block of `n` cells at `ℓ`. -/
def AllocAt (μ : Heap) (a : Expr) (μ' : Heap) (a' : Expr) (ℓ : Loc) (n : Nat) : Prop :=
  (∃ v, a = .app (.val (.prim .alloc)) (.val v) ∧ n = 1 ∧ μ ℓ = none ∧ μ' = μ.upd ℓ v ∧
    a' = .val (.loc ℓ)) ∨
  (∃ (c : UInt32) (f : Val), a = .app (.val (.prim .tab)) (.val (.pair (.i32 c) f)) ∧
    n = (arrLen c).toNat ∧ (∀ i, i < n → μ (ℓ + i) = none) ∧
    μ' = μ.fill ℓ (arrLen c).toNat .unit ∧ a' = tabFill f ℓ (arrLen c) 0 (arrLen c).toNat)

theorem Head.allocAt {μ μ' : Heap} {a a' : Expr} (hh : Head (ℍ := ℍ) μ a μ' a')
    (hal : a.allocs = true) : ∃ ℓ n, AllocAt μ a μ' a' ℓ n := by
  cases hh with
  | alloc v ℓ hl =>
      exact ⟨ℓ, 1, .inl ⟨v, rfl, rfl, hl, rfl, rfl⟩⟩
  | tab c f ℓ hl =>
      exact ⟨ℓ, _, .inr ⟨c, f, rfl, rfl, hl, rfl, rfl⟩⟩
  | _ => simp [Expr.allocs] at hal

/-- An infinite run of the machine. -/
def InfRun (f : ℕ → Heap × Expr) : Prop :=
  ∀ n, Step1 (ℍ := ℍ) (f n).1 (f n).2 (f (n + 1)).1 (f (n + 1)).2

/-- The number of `i < n` at which `g i` holds. -/
def countTrue (g : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | n + 1 => countTrue g n + if g n then 1 else 0

section OfRun
variable {f : ℕ → Heap × Expr} (hf : InfRun (ℍ := ℍ) f)

open Classical

/-- The decomposition of step `n` the construction uses. -/
def InfRun.wit (n : ℕ) : Kont × Expr × Expr := by
  have := hf n
  exact ⟨Classical.choose this, Classical.choose (Classical.choose_spec this),
    Classical.choose (Classical.choose_spec (Classical.choose_spec this))⟩

theorem InfRun.wit_spec (n : ℕ) :
    (f n).2 = (hf.wit n).1.plug (hf.wit n).2.1 ∧ (f (n + 1)).2 = (hf.wit n).1.plug (hf.wit n).2.2 ∧
      Head (ℍ := ℍ) (f n).1 (hf.wit n).2.1 (f (n + 1)).1 (hf.wit n).2.2 :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hf n)))

/-- Step `n` allocates. -/
def InfRun.alc (n : ℕ) : Bool := (hf.wit n).2.1.allocs

/-- The allocation count before step `n`. -/
def InfRun.cnt (n : ℕ) : ℕ := countTrue hf.alc n

/-- The location step `n` allocates at, when it allocates. -/
def InfRun.loc (n : ℕ) : Loc :=
  if h : ∃ ℓ m, AllocAt (f n).1 (hf.wit n).2.1 (f (n + 1)).1 (hf.wit n).2.2 ℓ m then
    Classical.choose h else 0

theorem InfRun.cnt_mono {m n : ℕ} (h : m ≤ n) : hf.cnt m ≤ hf.cnt n := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (by simp [InfRun.cnt, countTrue])

theorem InfRun.cnt_inj {m n : ℕ} (hm : hf.alc m = true) (hn : hf.alc n = true)
    (h : hf.cnt m = hf.cnt n) : m = n := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h1 : hf.cnt (m + 1) ≤ hf.cnt n := hf.cnt_mono hlt
    have h2 : hf.cnt (m + 1) = hf.cnt m + 1 := by simp [InfRun.cnt, countTrue, hm]
    omega
  · have h1 : hf.cnt (n + 1) ≤ hf.cnt m := hf.cnt_mono hlt
    have h2 : hf.cnt (n + 1) = hf.cnt n + 1 := by simp [InfRun.cnt, countTrue, hn]
    omega

/-- The allocator of an infinite run: at count `k`, the location the run chose at its allocating
step of that count, when that block is free; the least free block otherwise.  `[spec §14]` -/
def Alloc.ofRun : Alloc where
  pick k μ m :=
    if h : ∃ n, hf.cnt n = k ∧ hf.alc n = true then
      if ∀ i, i < m → μ (hf.loc (Nat.find h) + i) = none then hf.loc (Nat.find h)
      else Alloc.leastFree.pick k μ m
    else Alloc.leastFree.pick k μ m
  fresh k μ m hfin i hi := by
    split
    · split
      · next h' => exact h' i hi
      · exact Alloc.leastFree.fresh k μ m hfin i hi
    · exact Alloc.leastFree.fresh k μ m hfin i hi

theorem Alloc.ofRun_pick {n : ℕ} (hn : hf.alc n = true) {μ : Heap} {m : Nat}
    (hfree : ∀ i, i < m → μ (hf.loc n + i) = none) :
    (Alloc.ofRun hf).pick (hf.cnt n) μ m = hf.loc n := by
  have h : ∃ n', hf.cnt n' = hf.cnt n ∧ hf.alc n' = true := ⟨n, rfl, hn⟩
  have hfind : Nat.find h = n := by
    have hs := Nat.find_spec h
    exact hf.cnt_inj hs.2 hn hs.1
  simp only [Alloc.ofRun, dif_pos h, hfind, if_pos hfree]

/-- Every step of an infinite run is a step under `Alloc.ofRun`. -/
theorem InfRun.astep (n : ℕ) :
    AStep1 (ℍ := ℍ) (Alloc.ofRun hf) (hf.cnt n) (f n).1 (f n).2 (hf.cnt (n + 1)) (f (n + 1)).1
      (f (n + 1)).2 := by
  obtain ⟨h1, h2, hh⟩ := hf.wit_spec n
  refine ⟨(hf.wit n).1, (hf.wit n).2.1, (hf.wit n).2.2, h1, h2, ?_⟩
  cases hal : hf.alc n with
  | false =>
      have hc : hf.cnt (n + 1) = hf.cnt n := by simp [InfRun.cnt, countTrue, hal]
      rw [hc]
      exact AHead.det hh hal
  | true =>
      have hc : hf.cnt (n + 1) = hf.cnt n + 1 := by simp [InfRun.cnt, countTrue, hal]
      rw [hc]
      have hex := Head.allocAt hh hal
      have hloc : hf.loc n = Classical.choose hex := by simp only [InfRun.loc, dif_pos hex]
      obtain ⟨m, hm⟩ := Classical.choose_spec hex
      rw [← hloc] at hm
      rcases hm with ⟨v, ha, rfl, hl, hμ, ha'⟩ | ⟨c, g, ha, rfl, hl, hμ, ha'⟩
      · have hp : (Alloc.ofRun hf).pick (hf.cnt n) (f n).1 1 = hf.loc n :=
          Alloc.ofRun_pick hf hal (fun i hi => by rw [show i = 0 by omega, Nat.add_zero]; exact hl)
        rw [ha, hμ, ha']
        have := AHead.alloc (ℍ := ℍ) (A := Alloc.ofRun hf) (hf.cnt n) (f n).1 v (by rw [hp]; exact hl)
        rw [hp] at this
        exact this
      · have hp : (Alloc.ofRun hf).pick (hf.cnt n) (f n).1 (arrLen c).toNat = hf.loc n :=
          Alloc.ofRun_pick hf hal hl
        rw [ha, hμ, ha']
        have := AHead.tab (ℍ := ℍ) (A := Alloc.ofRun hf) (hf.cnt n) (f n).1 c g (by rw [hp]; exact hl)
        rw [hp] at this
        exact this

end OfRun

/-- **No infinite run.**  A closed computation of `F A` has no infinite run from the empty
memory: every run of it terminates.  `[spec §14]` -/
theorem total_no_infinite_run {e : Expr} {A : VTy}
    (h : CDerives LifeCtx.empty [] e (.comp (.ret A))) :
    ¬ ∃ f : ℕ → Heap × Expr, f 0 = (Adequacy.emptyMem, e) ∧
      ∀ n, Step1 (ℍ := ℍ) (f n).1 (f n).2 (f (n + 1)).1 (f (n + 1)).2 := by
  rintro ⟨f, h0, hf⟩
  obtain ⟨_, _, _, hv⟩ := total_every_alloc (ℍ := ℍ) h (Alloc.ofRun (ℍ := ℍ) hf) 0
  refine ARun.no_infinite hv (fun n => ((InfRun.cnt hf n), (f n).1, (f n).2)) ?_ ?_
  · simp [InfRun.cnt, countTrue, h0]
  · intro n
    exact InfRun.astep hf n

end BoCa.Fig16.LogRel.Core
