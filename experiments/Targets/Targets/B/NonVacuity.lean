import Targets.B.BoLo

/-!
# System B — B5 is not a tautology (RESTRUCTURE §6.2 item 3; finding #2)

`ReleasedOnceAll` held at every typing system (`releasedOnceAll`): it assumed its conclusion.  B5,
`ReleasedOnceReuse`, does not: `staleFree := x ← alloc (); free x; y ← alloc (); free x`.  Under an
allocator that gives `y` the location `x` had, its run ends at `()` with the memory empty: a
complete run.  B5 asks that run to be the image, step for step, of a complete **bump** run.  No such
bump run exists: the bump run's second allocation may not reuse the location its term still names
(`free x`), so it gives `y` another one, and its last step, `free x` at the location already freed,
has no step.  So a typing system that types `staleFree` fails B5 (`not_releasedOnceReuse_staleFree`).

That is all it shows: such a typing system already fails B3, whose bump run is stuck at the second
`free x`; given the step-for-step simulation (`BumpSim`), B5 follows from B3 and B4 (RESTRUCTURE
§2.4).  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.B
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont hndE ubindE ccatchE cfinE)
open BoCa.Programs (alloc' free')
open BoCa.Lifetime (LSub LifeCtx)

/-! ### Inversion of the steps `staleFree` takes -/

/-- `alloc v` steps only to a fresh location holding `v`. -/
theorem step1_alloc_inv {μ μ₁ : Heap} {e₁ : Expr} {v : Val}
    (h : Step1 (ℍ := ℍ) μ (.app alloc' v.1) μ₁ e₁) :
    ∃ ℓ, μ ℓ = none ∧ μ₁ = μ.upd ℓ v ∧ e₁ = (Val.loc ℓ).1 := by
  have hh := step1_top h fun K c hE hK => by
    cases K with
    | hole => exact absurd rfl hK
    | appR f K =>
        simp only [Kont.plug, Expr.app.injEq] at hE
        exact K.isVal_of_plug (hE.2 ▸ v.2)
    | appL K u =>
        simp only [Kont.plug, Expr.app.injEq] at hE
        exact K.isVal_of_plug (hE.1 ▸ IsVal.prim)
    | _ => simp [Kont.plug] at hE
  generalize hE : Expr.app alloc' v.1 = E at hh
  cases hh with
  | alloc v' ℓ hℓ =>
      simp only [alloc', Expr.app.injEq, Expr.val] at hE
      have : v = v' := Subtype.ext hE.2
      subst this
      exact ⟨ℓ, hℓ, rfl, rfl⟩
  | _ => simp_all [alloc', hndE, ubindE, ccatchE, cfinE, Expr.val, Val.prim, Val.lam]

/-- `free ℓ` steps only where `ℓ` holds a value, to that value, releasing `ℓ`. -/
theorem step1_free_inv {μ μ₁ : Heap} {e₁ : Expr} {ℓ : Loc}
    (h : Step1 (ℍ := ℍ) μ (.app free' (Val.loc ℓ).1) μ₁ e₁) :
    ∃ w : Val, μ ℓ = some w ∧ μ₁ = μ.del ℓ ∧ e₁ = w.1 := by
  have hh := step1_top h fun K c hE hK => by
    cases K with
    | hole => exact absurd rfl hK
    | appR f K =>
        simp only [Kont.plug, Expr.app.injEq] at hE
        exact K.isVal_of_plug (hE.2 ▸ IsVal.loc)
    | appL K u =>
        simp only [Kont.plug, Expr.app.injEq] at hE
        exact K.isVal_of_plug (hE.1 ▸ IsVal.prim)
    | _ => simp [Kont.plug] at hE
  generalize hE : Expr.app free' (Val.loc ℓ).1 = E at hh
  cases hh with
  | free ℓ' w hw =>
      simp only [free', Expr.app.injEq, Expr.val, Val.loc, Expr.loc.injEq] at hE
      obtain ⟨-, rfl⟩ := hE
      exact ⟨w, hw, rfl, rfl⟩
  | _ => simp_all [free', hndE, ubindE, ccatchE, cfinE, Expr.val, Val.prim, Val.lam, Val.loc]

/-- `(); e` steps only to `e`. -/
theorem step1_seqUnit_inv {μ μ₁ : Heap} {e e₁ : Expr}
    (h : Step1 (ℍ := ℍ) μ (.seq Val.unit.1 e) μ₁ e₁) : μ₁ = μ ∧ e₁ = e := by
  have hh := step1_top h fun K c hE hK => by
    cases K with
    | hole => exact absurd rfl hK
    | seq K u =>
        simp only [Kont.plug, Expr.seq.injEq] at hE
        exact K.isVal_of_plug (hE.1 ▸ IsVal.unit)
    | _ => simp [Kont.plug] at hE
  generalize hE : Expr.seq Val.unit.1 e = E at hh
  cases hh with
  | seq e' =>
      simp only [Expr.seq.injEq] at hE
      obtain ⟨-, rfl⟩ := hE
      exact ⟨rfl, rfl⟩
  | _ => simp_all [hndE, ubindE, ccatchE, cfinE]

/-! ### The program and its reusing run -/

/-- The rest after the first allocation, `x` at `0`: `free x; y ← alloc (); free x`. -/
def staleRest : Expr := .seq (.app free' (.var 0)) (bindE (.app alloc' unit') (.app free' (.var 1)))

/-- **`staleFree`**: `x ← alloc (); free x; y ← alloc (); free x`. -/
def staleFree : Expr := bindE (.app alloc' unit') staleRest

/-- `free ℓ`. -/
def freeAt (ℓ : Loc) : Expr := .app free' (Val.loc ℓ).1

/-- What is left after the first release: `y ← alloc (); free ℓ`. -/
def staleTail (ℓ : Loc) : Expr := bindE (.app alloc' unit') (freeAt ℓ)

theorem staleRest_subst (ℓ : Loc) :
    staleRest.subst 0 (Val.loc ℓ) = .seq (freeAt ℓ) (staleTail ℓ) := rfl

theorem freeAt_subst (ℓ ℓ' : Loc) : (freeAt ℓ).subst 0 (Val.loc ℓ') = freeAt ℓ := rfl

theorem bindK_plain (N : Expr) : (Kont.appR (Expr.lam N) .hole).Plain = true := rfl

theorem seqK_plain (N : Expr) : (Kont.seq .hole N).Plain = true := rfl

theorem not_isVal_app {f a : Expr} (hf : ∀ b, f ≠ .prim .store ∨ ¬ IsVal b) : ¬ IsVal (.app f a) := by
  intro h
  cases h with
  | storeV hv => exact ((hf a).elim (fun h => h rfl) fun h => h hv)

/-- The empty memory, an allocation and its release give the empty memory. -/
theorem upd_del_empty (ℓ : Loc) (v : Val) :
    (Adequacy.emptyMem.upd ℓ v).del ℓ = Adequacy.emptyMem := by
  funext k
  by_cases hk : k = ℓ
  · subst hk; simp only [BoCa.BoLo.Heap.del_same]; rfl
  · simp only [BoCa.BoLo.Heap.del_other hk, BoCa.BoLo.Heap.upd_other hk]

/-- One machine step under the empty platform. -/
theorem pstep_mach {μ μ' : Heap} {e e' : Expr} (K : Kont) {a a' : Expr} (he : e = K.plug a)
    (he' : e' = K.plug a') (hh : Head (ℍ := ℍ) μ a μ' a') :
    PStep (ℍ := ℍ) Platform.none (⟨μ, e, ()⟩ : Conf Platform.none) ⟨μ', e', ()⟩ :=
  .mach ⟨K, a, a', he, he', hh⟩

/-- **The reusing run** of `staleFree`: both allocations at the location `0`. -/
def staleRun : List (Conf Platform.none) :=
  [⟨Adequacy.emptyMem.upd 0 Val.unit, .app (.lam staleRest) (Val.loc 0).1, ()⟩,
   ⟨Adequacy.emptyMem.upd 0 Val.unit, .seq (freeAt 0) (staleTail 0), ()⟩,
   ⟨Adequacy.emptyMem, .seq Val.unit.1 (staleTail 0), ()⟩,
   ⟨Adequacy.emptyMem, staleTail 0, ()⟩,
   ⟨Adequacy.emptyMem.upd 0 Val.unit, .app (.lam (freeAt 0)) (Val.loc 0).1, ()⟩,
   ⟨Adequacy.emptyMem.upd 0 Val.unit, freeAt 0, ()⟩,
   ⟨Adequacy.emptyMem, Val.unit.1, ()⟩]

theorem staleRun_prun :
    PRun (ℍ := ℍ) Platform.none (init Platform.none staleFree :: staleRun) := by
  have h0 : Adequacy.emptyMem (0 : Loc) = none := rfl
  refine .cons (pstep_mach (Kont.appR (.lam staleRest) .hole) rfl rfl
    (Head.alloc _ Val.unit 0 h0)) ?_
  refine .cons (pstep_mach .hole rfl (staleRest_subst 0).symm (Head.beta _ staleRest (Val.loc 0))) ?_
  have hs3 := pstep_mach (ℍ := ℍ) (μ := Adequacy.emptyMem.upd 0 Val.unit)
    (e := Expr.seq (freeAt 0) (staleTail 0)) (e' := Expr.seq Val.unit.1 (staleTail 0))
    (Kont.seq .hole (staleTail 0)) rfl rfl
    (Head.free (Adequacy.emptyMem.upd 0 Val.unit) 0 Val.unit (BoCa.BoLo.Heap.upd_same _ _ _))
  rw [upd_del_empty] at hs3
  refine .cons hs3 ?_
  refine .cons (pstep_mach .hole rfl rfl (Head.seq _ (staleTail 0))) ?_
  refine .cons (pstep_mach (Kont.appR (.lam (freeAt 0)) .hole) rfl rfl
    (Head.alloc _ Val.unit 0 h0)) ?_
  refine .cons (pstep_mach .hole rfl (freeAt_subst 0 0).symm (Head.beta _ (freeAt 0) (Val.loc 0))) ?_
  refine .cons ?_ (.one _)
  have := pstep_mach (ℍ := ℍ) (μ := Adequacy.emptyMem.upd 0 Val.unit) (e := freeAt 0)
    (e' := Val.unit.1) .hole rfl rfl
    (Head.free (Adequacy.emptyMem.upd 0 Val.unit) 0 Val.unit (BoCa.BoLo.Heap.upd_same _ _ _))
  rwa [upd_del_empty] at this

theorem staleRun_final :
    ∀ c, (init Platform.none staleFree :: staleRun).getLast? = some c → Final Platform.none .unit c := by
  intro c hc
  simp [staleRun, init] at hc
  subst hc
  exact ⟨Val.unit, rfl, .unit, rfl⟩

/-! ### No complete bump run -/

theorem platformNone_respects' : Platform.none.Respects where
  uniq := by simp [Platform.none, Row.Uniq]
  nz := by simp [Platform.none, Row.NZ]
  lin := by simp [Platform.none]
  data := by simp [Platform.none]
  total := by simp [Platform.none]
  typed := by simp [Platform.none]

/-- **B5 is not a tautology**: a typing system that types `staleFree` fails it, at every world. -/
theorem not_releasedOnceReuse_staleFree (J : TypingJ) (M : BWorld)
    (h : J.closed staleFree (.ret .unit)) : ¬ ReleasedOnceReuse (ℍ := ℍ) J M := by
  intro hR
  have hD : DivFree ([] : Row) .unit := .unit 0
  have hle : RowLe ([] : Row) Platform.none.ops := fun _ _ _ h => by simp [Row.find] at h
  have h₀ := hR Platform.none platformNone_respects' [] [] [] .unit staleFree hD hle h
    (contractsW_nil M)
  rw [show substAll [] staleFree = staleFree from Adequacy.psub_nil 0 staleFree] at h₀
  obtain ⟨cs', g, hlen, hrun, hbump, -, -, -⟩ := h₀ staleRun staleRun_prun staleRun_final
  match cs', hlen with
  | [d₁, d₂, d₃, d₄, d₅, d₆, d₇], _ =>
  obtain ⟨μ₁, e₁, s₁⟩ := d₁
  obtain ⟨μ₂, e₂, s₂⟩ := d₂
  obtain ⟨μ₃, e₃, s₃⟩ := d₃
  obtain ⟨μ₄, e₄, s₄⟩ := d₄
  obtain ⟨μ₅, e₅, s₅⟩ := d₅
  obtain ⟨μ₆, e₆, s₆⟩ := d₆
  obtain ⟨μ₇, e₇, s₇⟩ := d₇
  cases hrun with
  | cons h₁ hrun => cases hrun with
  | cons h₂ hrun => cases hrun with
  | cons h₃ hrun => cases hrun with
  | cons h₄ hrun => cases hrun with
  | cons h₅ hrun => cases hrun with
  | cons h₆ hrun => cases hrun with
  | cons h₇ _ =>
  -- step 1: the first allocation, at some `ℓ₀`
  have s₁' := pstep_none h₁
  obtain ⟨e₁', rfl, s₁'⟩ := step1_plug_inv (Kont.appR (.lam staleRest) .hole) (bindK_plain _)
    (not_isVal_app fun _ => Or.inl (by simp [alloc'])) s₁'
  obtain ⟨ℓ₀, -, rfl, rfl⟩ := step1_alloc_inv (v := Val.unit) s₁'
  -- step 2: β
  obtain ⟨rfl, rfl⟩ := step1_beta_inv (v := Val.loc ℓ₀) (pstep_none h₂)
  rw [staleRest_subst] at h₃
  -- step 3: the first release
  obtain ⟨e₃', rfl, s₃'⟩ := step1_plug_inv (Kont.seq .hole (staleTail ℓ₀)) (seqK_plain _)
    (not_isVal_app fun _ => Or.inl (by simp [free'])) (pstep_none h₃)
  obtain ⟨w, hw, rfl, rfl⟩ := step1_free_inv s₃'
  simp only [BoCa.BoLo.Heap.upd_same, Option.some.injEq] at hw
  subst hw
  -- step 4: `(); …`
  obtain ⟨rfl, rfl⟩ := step1_seqUnit_inv (pstep_none h₄)
  -- step 5: the second allocation, at some `ℓ₁`
  obtain ⟨e₅', rfl, s₅'⟩ := step1_plug_inv (Kont.appR (.lam (freeAt ℓ₀)) .hole) (bindK_plain _)
    (not_isVal_app fun _ => Or.inl (by simp [alloc'])) (pstep_none h₅)
  obtain ⟨ℓ₁, hfree, rfl, rfl⟩ := step1_alloc_inv (v := Val.unit) s₅'
  -- the bump run does not reuse a location its term names
  have hne : ℓ₁ ≠ ℓ₀ := by
    rintro rfl
    refine hbump 4 ℓ₁ ⟨_, _, rfl, rfl, hfree, by simp⟩ 4 _ le_rfl rfl (Or.inr (Or.inl ?_))
    simp [staleTail, freeAt, bindE, Expr.MentionsLoc]
  -- step 6: β
  obtain ⟨rfl, rfl⟩ := step1_beta_inv (v := Val.loc ℓ₁) (pstep_none h₆)
  rw [freeAt_subst] at h₇
  -- step 7: the second release, at the freed `ℓ₀`: no step
  obtain ⟨w', hw', -, -⟩ := step1_free_inv (pstep_none h₇)
  simp [BoCa.BoLo.Heap.upd_other (Ne.symm hne)] at hw'

end Targets.B

end
