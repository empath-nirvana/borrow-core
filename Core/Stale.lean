import Core.Demonic

/-!
# Core — a stale read, under every allocator  `[spec §13]`

    staleL = let x = alloc () in free x;
             let y = alloc (inj₁ ()) in (λ_. ()) (load x); case (free y) {_ ⇒ () | _ ⇒ ()}

`staleL` reads `x` after freeing it.  The run that gives `y` the location `x` had reads
`inj₁ ()` there and gives the memory back, so `staleL` is in `wpTSAngelic` from every
configuration (`staleL_angelic`).  Under the allocator `Alloc.atCount`, which allocates at the
allocation count whenever that location is free, `y` goes elsewhere and `load x` is stuck, so
`staleL` is in `wpTS` at no postcondition from the empty world (`staleL_not_every_alloc`).  The
two differ exactly in the quantifier over allocators.

The closure `λ_. staleL` is therefore outside the value relation at `!U(1 ⊸ F 1)`
(`staleClosure_not_vC`), the type at which a borrowed `!` closure is called (`Imm̲ (!A) = !A`).
The `Imm` clause reads its payload at the observable view, which reads `!A` at the program's
view, so a cell holding it is not an `Imm` borrow of that type either
(`staleClosure_not_immPayload`).  (#41.)
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc AHead AStep1 ARun Step1N)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The term -/

/-- `alloc e`. -/
def stAlloc (e : Expr) : Expr := .app (.val (.prim .alloc)) e
/-- `free e`. -/
def stFree (e : Expr) : Expr := .app (.val (.prim .free)) e
/-- `load e`. -/
def stLoad (e : Expr) : Expr := .app (.val (.prim .load)) e

/-- `(λ_. ()) (load x); case (free y) {_ ⇒ () | _ ⇒ ()}`, with `y` at index 0. -/
def staleTail (x : Expr) : Expr :=
  .seq (.app (.val (.lam unit')) (stLoad x)) (.case (stFree (.var 0)) unit' unit')

/-- `let y = alloc (inj₁ ()) in staleTail x`. -/
def staleInner (x : Expr) : Expr := elet (stAlloc (.val (.inj₁ .unit))) (staleTail x)

/-- `free x; staleInner x`, with `x` at index 0. -/
def staleBody : Expr := .seq (stFree (.var 0)) (staleInner (.var 1))

/-- `let x = alloc () in free x; let y = alloc (inj₁ ()) in …; load x; free y`.  `[spec §13]` -/
def staleL : Expr := elet (stAlloc unit') staleBody

/-- `λ_. staleL`.  `[spec §13]` -/
def staleClosure : Val := Val.lam staleL

/-- The closure type a borrowed `!` closure is called at: `!U(1 ⊸ F 1)`. -/
def staleTy : VTy := .bang (.thunk (.arr .unit (.ret .unit)))

theorem staleBody_subst (l : Loc) :
    staleBody.subst 0 (Val.loc l) = .seq (stFree (.val (.loc l))) (staleInner (.val (.loc l))) := by
  simp [staleBody, staleInner, staleTail, elet, stAlloc, stFree, stLoad, unit', Expr.subst,
    Expr.shift, Val.shift, Expr.val, Val.lam, Val.unit, Val.prim, Val.inj₁, Val.loc]

theorem staleTail_subst (l l' : Loc) :
    (staleTail (.val (.loc l))).subst 0 (Val.loc l') =
      .seq (.app (.val (.lam unit')) (stLoad (.val (.loc l))))
        (.case (stFree (.val (.loc l'))) unit' unit') := by
  simp [staleTail, stFree, stLoad, unit', Expr.subst, Expr.val, Val.lam, Val.unit, Val.prim,
    Val.loc]

theorem staleL_subst (j : Nat) (v : Val) : staleL.subst j v = staleL := by
  simp [staleL, staleBody, staleInner, staleTail, elet, stAlloc, stFree, stLoad, unit',
    Expr.subst, Expr.val, Val.lam, Val.unit, Val.prim, Val.inj₁]

theorem upd_del_of_none {μ : Heap} {l : Loc} {v : Val} (hl : μ l = none) :
    (μ.upd l v).del l = μ := by
  funext x
  by_cases e : x = l
  · subst e; rw [BoCa.BoLo.Heap.del_same, hl]
  · rw [BoCa.BoLo.Heap.del_other e, BoCa.BoLo.Heap.upd_other e]

/-! ### Some run: `y` at `x`'s location -/

/-- The run that allocates `x` and `y` at the same free location `l`, and gives the memory
back. -/
theorem staleL_runs {μ : Heap} {l : Loc} (hl : μ l = none) :
    Steps μ staleL μ (.val .unit) := by
  refine .more (μ₁ := μ.upd l .unit) (e₁ := .app (.val (.lam staleBody)) (.val (.loc l)))
    ⟨.appR (.val (.lam staleBody)) .hole, _, _, rfl, rfl, Head.alloc μ .unit l hl⟩ ?_
  refine .more (μ₁ := μ.upd l .unit) (e₁ := staleBody.subst 0 (Val.loc l))
    (Step1.head (Head.beta _ staleBody (Val.loc l))) ?_
  rw [staleBody_subst]
  refine .more (μ₁ := μ) (e₁ := .seq (.val .unit) (staleInner (.val (.loc l))))
    ⟨.seq .hole (staleInner (.val (.loc l))), _, _, rfl, rfl, by
      have := Head.free (μ.upd l Val.unit) l Val.unit (BoCa.BoLo.Heap.upd_same _ _ _)
      rwa [upd_del_of_none hl] at this⟩ ?_
  refine .more (μ₁ := μ) (e₁ := staleInner (.val (.loc l))) (Step1.head (Head.seq _ _)) ?_
  refine .more (μ₁ := μ.upd l (.inj₁ .unit))
    (e₁ := .app (.val (.lam (staleTail (.val (.loc l))))) (.val (.loc l)))
    ⟨.appR (.val (.lam (staleTail (.val (.loc l))))) .hole, _, _, rfl, rfl,
      Head.alloc μ (.inj₁ .unit) l hl⟩ ?_
  refine .more (μ₁ := μ.upd l (.inj₁ .unit))
    (e₁ := (staleTail (.val (.loc l))).subst 0 (Val.loc l))
    (Step1.head (Head.beta _ _ (Val.loc l))) ?_
  rw [staleTail_subst]
  refine .more (μ₁ := μ.upd l (.inj₁ .unit))
    (e₁ := .seq (.app (.val (.lam unit')) (.val (.inj₁ .unit)))
      (.case (stFree (.val (.loc l))) unit' unit'))
    ⟨.seq (.appR (.val (.lam unit')) .hole) (.case (stFree (.val (.loc l))) unit' unit'), _, _,
      rfl, rfl, Head.load _ l (.inj₁ .unit) (BoCa.BoLo.Heap.upd_same _ _ _)⟩ ?_
  refine .more (μ₁ := μ.upd l (.inj₁ .unit))
    (e₁ := .seq unit' (.case (stFree (.val (.loc l))) unit' unit'))
    ⟨.seq .hole (.case (stFree (.val (.loc l))) unit' unit'), _, _, rfl, rfl,
      Head.beta _ unit' (.inj₁ .unit)⟩ ?_
  refine .more (μ₁ := μ.upd l (.inj₁ .unit)) (e₁ := .case (stFree (.val (.loc l))) unit' unit')
    (Step1.head (Head.seq _ _)) ?_
  refine .more (μ₁ := μ) (e₁ := .case (.val (.inj₁ .unit)) unit' unit')
    ⟨.case .hole unit' unit', _, _, rfl, rfl, by
      have := Head.free (μ.upd l (Val.inj₁ Val.unit)) l (Val.inj₁ Val.unit)
        (BoCa.BoLo.Heap.upd_same _ _ _)
      rwa [upd_del_of_none hl] at this⟩ ?_
  exact .one (Step1.head (Head.case₁ μ Val.unit unit' unit'))

/-- A run that gives the memory back puts `wpTSAngelic` at the empty resource. -/
theorem wpTSAngelic_restore {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp} {v : Val}
    (hrun : ∀ μ : Heap, FinDom μ → Steps μ e μ (.val v)) (hQ : Q ls v PMap.empty) :
    wpTSAngelic ls e Q PMap.empty := by
  intro ρf fρ ps hf hc hT htg
  obtain ⟨μ, hμ⟩ := lower_of_hash hf hc
  exact ⟨PMap.empty, PMap.empty, fρ, fρ, PMap.empty, v, μ, μ, ps, ls, ResU.hash_symm hf, hc,
    ResU.hash_symm (ResU.hash_empty_right (hash_valid_comp hf hc)), hμ,
    ResU.comp_empty_right fρ, hμ, hrun μ (lower_finDom hμ), ResU.comp_empty_right _,
    (ResU.updV_self_iff _).mpr (hash_valid hf).2, noOwn_empty, hT, htg,
    fun _ => Iff.rfl, fun _ => Iff.rfl, hQ⟩

/-- **`staleL` is in `wpTSAngelic`** at `𝒱⟦1⟧`, from every configuration completing `∅`.
`[spec §13]` -/
theorem staleL_angelic (ls : List SRec) (δ : LSub) :
    wpTSAngelic ls staleL (fun ls'' => vC true .unit ls'' δ) PMap.empty :=
  wpTSAngelic_restore (v := .unit) (fun μ hfin => by
    obtain ⟨l, hl⟩ := BoCa.BoLo.finDom_block hfin
    exact staleL_runs (l := l) (by simpa using hl 0)) ⟨rfl, rfl⟩

/-- **The call `(λ_. staleL) ()` is in `wpTSAngelic`** at `𝒱⟦1⟧`.  `[spec §13]` -/
theorem staleCall_angelic (ls : List SRec) (δ : LSub) :
    wpTSAngelic ls (.app (.val staleClosure) (.val .unit)) (fun ls'' => vC true .unit ls'' δ)
      PMap.empty :=
  wpTSAngelic_restore (v := .unit) (fun μ hfin => by
    obtain ⟨l, hl⟩ := BoCa.BoLo.finDom_block hfin
    refine .more (Step1.head (Head.beta μ staleL Val.unit)) ?_
    rw [staleL_subst]
    exact staleL_runs (l := l) (by simpa using hl 0)) ⟨rfl, rfl⟩

/-! ### Every allocator: an allocator that does not reuse `x`'s location -/

open Classical in
/-- The allocator that allocates at the allocation count `k` when the block from `k` is free,
and at the least free block otherwise.  `[spec §13]` -/
def Alloc.atCount : Alloc where
  pick k μ n := if ∀ i, i < n → μ (k + i) = none then k else Alloc.leastFree.pick k μ n
  fresh k μ n hfin i hi := by
    split
    · next h => exact h i hi
    · exact Alloc.leastFree.fresh k μ n hfin i hi

theorem Alloc.atCount_pick {k : Nat} {μ : Heap} {n : Nat} (h : ∀ i, i < n → μ (k + i) = none) :
    Alloc.atCount.pick k μ n = k := by
  simp only [Alloc.atCount]
  rw [if_pos h]

/-- The empty memory. -/
abbrev μ₀ : Heap := fun _ => none

/-- The term `staleL` is stuck at, under `Alloc.atCount` from the empty memory: `load x` with
`x = 0` freed and `y = 1`. -/
def staleStuck : Expr :=
  .seq (.app (.val (.lam unit')) (stLoad (.val (.loc 0))))
    (.case (stFree (.val (.loc 1))) unit' unit')

/-- Under `Alloc.atCount`, `x` is `0`, freed, and `y` is `1`. -/
theorem staleL_atCount :
    ARun (ℍ := ℍ) Alloc.atCount 0 μ₀ staleL 2 (μ₀.upd 1 (.inj₁ .unit)) staleStuck := by
  have hp₀ : Alloc.atCount.pick 0 μ₀ 1 = 0 := Alloc.atCount_pick (fun _ _ => rfl)
  have hp₁ : Alloc.atCount.pick 1 μ₀ 1 = 1 := Alloc.atCount_pick (fun _ _ => rfl)
  have ha₀ := AHead.alloc (ℍ := ℍ) (A := Alloc.atCount) 0 μ₀ Val.unit (by rw [hp₀])
  rw [hp₀] at ha₀
  have ha₁ := AHead.alloc (ℍ := ℍ) (A := Alloc.atCount) 1 μ₀ (Val.inj₁ Val.unit) (by rw [hp₁])
  rw [hp₁] at ha₁
  refine .more (k₁ := 1) (μ₁ := μ₀.upd 0 .unit)
    (e₁ := .app (.val (.lam staleBody)) (.val (.loc 0)))
    ⟨.appR (.val (.lam staleBody)) .hole, _, _, rfl, rfl, ha₀⟩ ?_
  refine ARun.cons (μ₁ := μ₀.upd 0 .unit) (e₁ := staleBody.subst 0 (Val.loc 0))
    (Step1N.head (Head.beta _ staleBody (Val.loc 0)) rfl) ?_
  rw [staleBody_subst]
  refine ARun.cons (μ₁ := μ₀) (e₁ := .seq (.val .unit) (staleInner (.val (.loc 0))))
    ⟨.seq .hole (staleInner (.val (.loc 0))), _, _, rfl, rfl, by
      have := Head.free (μ₀.upd 0 Val.unit) 0 Val.unit (BoCa.BoLo.Heap.upd_same _ _ _)
      rwa [upd_del_of_none rfl] at this, rfl⟩ ?_
  refine ARun.cons (μ₁ := μ₀) (e₁ := staleInner (.val (.loc 0)))
    (Step1N.head (Head.seq _ _) rfl) ?_
  refine .more (k₁ := 2) (μ₁ := μ₀.upd 1 (.inj₁ .unit))
    (e₁ := .app (.val (.lam (staleTail (.val (.loc 0))))) (.val (.loc 1)))
    ⟨.appR (.val (.lam (staleTail (.val (.loc 0))))) .hole, _, _, rfl, rfl, ha₁⟩ ?_
  refine ARun.cons (μ₁ := μ₀.upd 1 (.inj₁ .unit))
    (e₁ := (staleTail (.val (.loc 0))).subst 0 (Val.loc 1))
    (Step1N.head (Head.beta _ _ (Val.loc 1)) rfl) ?_
  rw [staleTail_subst]
  exact .refl _ _ _

/-- `staleStuck` takes no step at a memory without `0`. -/
theorem staleStuck_no_step {A : Alloc} {k k' : Nat} {μ μ' : Heap} {e' : Expr} (h0 : μ 0 = none)
    (h : AStep1 (ℍ := ℍ) A k μ staleStuck k' μ' e') : False := by
  have h₀ : Head (ℍ := ℍ) (BoCa.BoLo.Heap.upd μ₀ 0 Val.unit) (stLoad (.val (.loc 0)))
      (BoCa.BoLo.Heap.upd μ₀ 0 Val.unit) (.val Val.unit) :=
    Head.load _ 0 .unit (BoCa.BoLo.Heap.upd_same _ _ _)
  obtain ⟨K', a, a', hE, -, hh⟩ := h
  have hE' : (Kont.seq (.appR (.val (.lam unit')) .hole)
      (.case (stFree (.val (.loc 1))) unit' unit')).plug (stLoad (.val (.loc 0))) = K'.plug a :=
    hE
  obtain ⟨K'', hb, -⟩ := plug_decomp hh.toHead _ K' h₀.not_isVal hE'
  obtain rfl : K'' = .hole := head_plug h₀ K'' hh.toHead.not_isVal hb
  simp only [BoCa.BoLo.Kont.plug] at hb
  have hh' := hh.toHead
  generalize hx : a = x at hh'
  cases hh' <;> simp [stLoad, Expr.val, Val.prim, Val.loc, ← hb] at hx
  case load ℓ v hv =>
    subst hx
    rw [h0] at hv
    cases hv

/-- `staleStuck` does not run to a value at a memory without `0`. -/
theorem staleStuck_no_run {A : Alloc} {k j : Nat} {μ μ' : Heap} {v : Val} (h0 : μ 0 = none)
    (h : ARun (ℍ := ℍ) A k μ staleStuck j μ' (.val v)) : False := by
  generalize hE : staleStuck = E at h
  cases h with
  | refl =>
      have : IsVal staleStuck := hE ▸ v.2
      cases this
  | more s _ =>
      subst hE
      exact staleStuck_no_step h0 s

/-- **`staleL` is in `wpTS` at no postcondition from the empty world**: under
`Alloc.atCount` its only run is stuck at `load x`.  `[spec §13]` -/
theorem staleL_not_every_alloc (Q : List SRec → Val → WProp) :
    ¬ wpTS [] staleL Q PMap.empty := by
  intro hw
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  obtain ⟨_, _, _, _, _, v, μ, μ', _, _, -, -, -, hμ, -, -, ⟨j, hrun⟩, -⟩ :=
    hw PMap.empty PMap.empty [] Fig16.LogRel.hash_empty (ResU.comp_empty_right _) TW.empty htg
      Alloc.atCount 0
  obtain rfl : μ = μ₀ := ResU.Lower.functional hμ Fig16.BoLo.lower_empty
  exact staleStuck_no_run (by simp) (staleL_atCount.rest hrun)

/-- The call `(λ_. staleL) ()` is in `wpTS` at no postcondition from the empty world. -/
theorem staleCall_not_every_alloc (Q : List SRec → Val → WProp) :
    ¬ wpTS [] (.app (.val staleClosure) (.val .unit)) Q PMap.empty := by
  intro hw
  have htg : Tagged (PMap.empty : WRes) [] [] := fun x hx => absurd hx (by simp)
  obtain ⟨_, _, _, _, _, v, μ, μ', _, _, -, -, -, hμ, -, -, ⟨j, hrun⟩, -⟩ :=
    hw PMap.empty PMap.empty [] Fig16.LogRel.hash_empty (ResU.comp_empty_right _) TW.empty htg
      Alloc.atCount 0
  obtain rfl : μ = μ₀ := ResU.Lower.functional hμ Fig16.BoLo.lower_empty
  have hpre : ARun (ℍ := ℍ) Alloc.atCount 0 μ₀ (.app (.val staleClosure) (.val .unit)) 2
      (μ₀.upd 1 (.inj₁ .unit)) staleStuck := by
    refine ARun.cons (Step1N.head (Head.beta μ₀ staleL Val.unit) rfl) ?_
    rw [staleL_subst]
    exact staleL_atCount
  exact staleStuck_no_run (by simp) (hpre.rest hrun)

/-- **`λ_. staleL` is outside the value relation at `!U(1 ⊸ F 1)`**, at the empty list.
`[spec §13]` -/
theorem staleClosure_not_vC (δ : LSub) (ρ : WRes) : ¬ vC true staleTy [] δ staleClosure ρ := by
  rintro ⟨rfl, hv⟩
  have hc := hv [] (Ext.refl _ _) Val.unit PMap.empty PMap.empty ⟨rfl, rfl⟩
    (ResU.comp_empty_right _)
  exact staleCall_not_every_alloc _ hc

/-- **The `Imm` clause's payload excludes it too**: an `Imm` borrow reads its payload at the
observable view, which reads `!A` at the program's view, so no `imm` cell holding `λ_. staleL`
is an `Imm` borrow of `!U(1 ⊸ F 1)` at the empty list.  `[spec §13]` -/
theorem staleClosure_not_immPayload (δ : LSub) {ℓ : Loc} {α : Life} {s : LSet} {σ : WRes}
    {hs : σ.InStratum s.join} :
    ¬ ptoImmS ℓ α [] (fun ls₀ => vC false staleTy ls₀ δ)
      (ResU.single ℓ (CellU.immOf s staleClosure σ hs)) := by
  rintro ⟨s', u, σ', hs', ls₀, he, hP, -, hls₀⟩
  have e := congrArg (fun ρ : WRes => ρ.get ℓ) he
  simp only [ResU.single_get_self] at e
  obtain ⟨-, hu, -⟩ := CellU.immOf_inj (Option.some.inj e)
  subst hu
  have hnil : ls₀ = [] := List.eq_nil_iff_forall_not_mem.mpr fun x hx => by
    simpa using (hls₀ x).mp hx
  subst hnil
  exact staleClosure_not_vC δ σ' hP

end BoCa.Fig16.LogRel.Core

end
