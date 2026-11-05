import Core.Chain.PoolJoinC
import Core.Chain.SI.CrossProg
import Core.TreePoolSpawnProgs

/-!
# A lend left open while its borrow is held in the outer pool, ended after a join, through `poolSchedAdequacyC`  `[spec §62]`

Closed programs run under the scheduler `HJ` (`Core/Chain/PoolJoinC.lean`), each safe and leak-free
through the general headline `poolSchedAdequacyC`, every premise discharged.

**Case 1, `imm`** (`rootI false`, `rootI true`):

    let c = alloc () in
      (spawn (λ_. parkC (); !c); !c; parkL (); ()); join c;   -- the lend of `c` open
      free c

The root lends `c` `imm` (`cerwp_scope`, `[TR]` 6.64 across stops) around its body and the join.
The body spawns the child into the scheduler's pool with a copy of the borrow (6.116) and keeps
the other. Under `HJ` the child runs first; its `parkC` resumes the root and keeps the child, holding
its copy, beneath it; the root reads `!c` while the child is parked; then the root `parkL`s to the
scheduler with the lend open, which resumes the child: it reads `!c` and ends, handing its copy to
the scheduler's bag. The root is resumed, its body returns, and `join c` finds the pool empty: the
scheduler hands it the bag's copies of `c`, the lend ends, and `c` is freed.

The cancelled variant (`rootI true`) has `cancel ()` for `parkL ()`: the child, the pool's top,
cancellable and parked holding its copy, is cancelled; its cancel run ends holding the copy, which
joins the bag; then the root is resumed, joins and frees `c` as before.

The root's lend is open across every stop of its body (`spawn`, `parkL`/`cancel`) and across the
join: the lend's record and the borrow are in the root's stored continuation while the child runs,
and the lend ends in the segment the join resumes (`joinFd`: the scheduler's bag holds nothing at
`c` once its copies are handed back).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Cross821C
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.PoolJoin
open BoCa.Fig16.LogRel.Core.Chain.SI.CrossProg (Q₀ Qsc Qsc_down Φe δ₀)
open BoCa.Fig16.Tree.Wp.SchedProgs.Park (nP)
open BoCa.Fig16.Tree.Wp.SchedProgs.SpawnProgs (parkE cancelE spawnE)
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal ccatchE)

set_option linter.unusedSimpArgs false

/-! ### A load at `erwp0` -/

/-- **`!ℓ` through an `imm` cell at `erwp0`**: the load's only step, for free. -/
theorem erwp0_loadI {Φ : LocFam} (hΦ : Φ.Down) {Tb : TableN} (hTd : Tb.Down) {Q : PostN}
    (hQ : Q.Down) (K : Kont) (l : Loc) {s : LSet} {u : Val} {χ : WRes} {h : χ.InStratum s.join}
    {n : Nat} {ls : List SRec} {ρ ρR : WRes}
    (hc : ResU.CompS (ResU.single l (CellU.immOf s u χ h)) ρR ρ)
    (hk : erwp0 (ℍ := ℍ) Φ Tb Q n ls (K.plug (.val u)) ρ) :
    erwp0 (ℍ := ℍ) Φ Tb Q n ls (K.plug (.app (.val (.prim .load)) (.val (Val.loc l)))) ρ := by
  rw [erwp0_eq] at hk ⊢
  have hPD := erwpPost_down hTd hQ (erwp0C (ℍ := ℍ) Φ Tb Q n)
  intro ρf fρ ps μ hf hcf hT htg hl hfd j μ' E hj hrun hfin
  obtain ⟨χ₁, hχ, heχ⟩ := compS_get_erase hc (ResU.single_get_self l _)
  obtain ⟨χ', hχ', heχ'⟩ := compS_get_erase (ResU.CompS.comm hcf) hχ
  have hlv : μ l = some u := by
    rw [lower_get hl hχ', heχ', heχ]
    rfl
  have hdet := step1Only_plug (ℍ := ℍ) (Head.load μ l u hlv) rfl K
  cases hrun with
  | refl => exact absurd hdet.1 (hfin _ _)
  | @more j' _ _ _ _ _ _ hs t =>
      obtain ⟨rfl, rfl⟩ := hdet.2 _ _ hs
      exact (hk ρf fρ ps _ hf hcf hT htg hl hfd j' μ' E (by omega) t hfin).mono hΦ (by omega)
        (fun _ _ x => hPD.le (by omega) _ _ _ x)

/-! ### The programs -/

/-- `parkL ()`. -/
def parkLE : Expr := performE (.val (opPayload nP 4 Val.unit))

/-- `!ℓ`. -/
def ldL (l : Loc) : Expr := .app (.val (.prim .load)) (.val (Val.loc l))

/-- **The `imm` child**: `λ_. parkC (); !ℓ`. -/
def childI (l : Loc) : Val := Val.lam (.seq parkE (ldL l))

/-- The root's body after the spawn's `!ℓ`: `parkL ()`, or `cancel ()` for the cancelled
variant. -/
def tailI (b : Bool) : Expr := if b then cancelE else parkLE

/-- **The root's body**, the lend open: `spawn (λ_. parkC (); !ℓ); !ℓ; tail; ()`. -/
def bodyI (b : Bool) (l : Loc) : Expr :=
  .seq (spawnE (childI l)) (.seq (ldL l) (.seq (tailI b) (.val Val.unit)))

/-- **The root at `ℓ`**: the body and `join ℓ`, then `free ℓ`. -/
def rootIB (b : Bool) (l : Loc) : Expr :=
  .seq ((seqK nP 3 l).plug (bodyI b l)) (freeE (.val (Val.loc l)))

/-- The root, the cell a variable. -/
def rootIT (b : Bool) : Expr :=
  .seq (.seq (.seq (performE (.pair (.val (Val.i32 nP)) (.pair (.val (Val.i32 1))
      (.lam (.seq parkE (.app (.val (.prim .load)) (.var 1)))))))
      (.seq (.app (.val (.prim .load)) (.var 0)) (.seq (tailI b) (.val Val.unit))))
    (performE (.pair (.val (Val.i32 nP)) (.pair (.val (Val.i32 3)) (.var 0)))))
    (freeE (.var 0))

/-- **The program's root**: `let c = alloc () in …`. -/
def rootI (b : Bool) : Expr := .app (.val (Val.lam (rootIT b))) (.app (.val (.prim .alloc)) (.val .unit))

theorem rootIT_subst (b : Bool) (l : Loc) : Expr.subst 0 (Val.loc l) (rootIT b) = rootIB b l := by
  cases b <;>
  simp [rootIT, rootIB, bodyI, tailI, childI, ldL, seqK, joinE, parkE, cancelE, parkLE, spawnE,
    Expr.subst, Kont.plug, performE, opPayload, Val.pair, Val.i32, Val.unit, Val.loc, Val.lam,
    Val.shift, Expr.shift, Expr.val, Val.prim, freeE]

/-! ### The child -/

/-- **The `imm` child**, at any table of the scheduler's shape: from its copy, `parkC` holding
it, then the read, then its end holding the copy; cancelled, its cancel run ends holding the copy. -/
theorem childI_ok {PS : Nat → List SRec → Val → WProp}
    (hPS : ∀ k ls v ρ, PS (k + 1) ls v ρ → PS k ls v ρ) (l : Loc) (A : Life) (F : WRes → Prop)
    (n : Nat) (ls : List SRec) :
    cerwp (ℍ := ℍ) (opTableC (tabOfC (ℍ := ℍ) PS)) QinJ F n ls []
      (.app (.val (childI l)) (.val Val.unit)) (viewA l Val.unit A) := by
  have hL := opTableC_local (tabOfC (ℍ := ℍ) PS)
  have hD := opTableC_down (tabOfC_down (ℍ := ℍ) hPS)
  refine cerwp_det hD QinJ_down (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit (.seq parkE (ldL l))) =
      (Kont.seq .hole (ldL l)).plug (performE (.val (opPayload nP 0 Val.unit))) := by
    simp [Expr.subst, Kont.plug, parkE, ldL, performE, opPayload, Val.pair, Val.i32, Val.unit,
      Val.loc, Expr.val, Val.prim]
  rw [e]
  refine cerwp_perform (T := tabOfC (ℍ := ℍ) PS) (en := enParkC (ℍ := ℍ))
    (Kont.seq .hole (ldL l)) (by simp [Kont.HasHnd]) (by simp [tabOfC]) rfl rfl
    (compS_empty_left _) ⟨rfl, rfl⟩ (fun hq => by simp [enParkC] at hq)
    (fun ls' _ k' hk' w σ₁ σ₂ hB hc => ?_) (fun ls' _ _ P hP => ?_)
  · obtain ⟨rfl, rfl⟩ := hB
    obtain rfl := ResU.CompS.functional hc (ResU.comp_empty_right _)
    refine cerwp_det hD QinJ_down (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    exact cerwp_loadI hL .hole l (ResU.comp_empty_right _)
      (cerwp_val ⟨rfl, ViewsC.single _ _ _ _⟩)
  · cases hP
    intro F'
    show cerwp (ℍ := ℍ) _ _ _ _ _ _ (ccatchE ((Kont.seq .hole (ldL l)).dead.plug
      (raiseE (.val (cancelVal none))))) _
    refine cerwp_det (opTableC_down opTabC_emptyC_down) QinJ_down
      (fun μ => step1Only_plug (Head.cancel μ (Kont.seq .hole (ldL l)).dead
        (by simp [Kont.dead, Kont.Catches])) rfl .hole) ?_
    exact cerwp_val ⟨rfl, ViewsC.single _ _ _ _⟩

/-! ### The root's body, the lend open -/

/-- The spawn payload of the scheduler's table. -/
abbrev PSJ : Nat → List SRec → Val → WProp := spawnPAC (ℍ := ℍ) (tabAtC (ℍ := ℍ))

theorem tabInN_down {PS : Nat → List SRec → Val → WProp}
    (hPS : ∀ k ls v ρ, PS (k + 1) ls v ρ → PS k ls v ρ) : (tabInN PS).Down where
  pa := fun _ _ en h k ls v ρ hA => by
    simp only [tabInN] at h
    split_ifs at h <;> cases h <;> first | exact hA | exact hPS _ _ _ _ hA
  fin := fun _ _ en P h hP => by
    simp only [tabInN] at h
    split_ifs at h <;> cases h <;> cases hP
  wcl := fun _ _ en h _ _ _ _ _ _ _ => by
    simp only [tabInN] at h
    split_ifs at h <;> cases h <;> trivial

/-- **The root's body**: `spawn` hands one copy of the borrow to the child and keeps the other
(6.116); `!ℓ` through the kept copy, the child parked; `parkL ()` or `cancel ()`; `()` holding the
copy. -/
theorem bodyI_ok (b : Bool) (l : Loc) (A : Life) (n : Nat) (ls : List SRec) :
    erwp0 (ℍ := ℍ) Φe (opTableN (tabInN (PSJ (ℍ := ℍ)))) (Q₀ l A) n ls (bodyI b l)
      (viewA l Val.unit A) := by
  have hTD := opTableN_down (tabInN_down (spawnPAC_down (ℍ := ℍ) (tabAtC (ℍ := ℍ))))
  have hΦ : Φe.Down := fun _ _ _ h => by cases h
  have hQ : (Q₀ l A).Down := fun _ _ _ _ h => h
  show erwp0 (ℍ := ℍ) _ _ _ _ _ ((Kont.seq .hole (.seq (ldL l) (.seq (tailI b) (.val Val.unit)))).plug
    (performE (.val (opPayload nP 1 (childI l))))) _
  refine erwp0_perform (T := tabInN (PSJ (ℍ := ℍ))) (en := enLinN (PSJ (ℍ := ℍ))) _
    (by simp [Kont.HasHnd]) (by simp [tabInN]) rfl rfl
    (compS_imm_dup l _ Val.unit PMap.empty (inStratumE A))
    (fun j _ ls' => by rw [tabAtC_eq]; exact childI_ok (spawnPAC_down _) l A _ j ls')
    (fun ls' _ k' _ w σ₁ σ₂ hB hc => ?_)
  obtain ⟨rfl, rfl⟩ := hB
  obtain rfl := ResU.CompS.functional hc (ResU.comp_empty_right _)
  refine erwp0_det hΦ hTD hQ (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  refine erwp0_loadI hΦ hTD hQ (Kont.seq .hole (.seq (tailI b) (.val Val.unit))) l
    (ResU.comp_empty_right _) ?_
  refine erwp0_det hΦ hTD hQ (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
  have htail : ∀ i : UInt32, tabInN (PSJ (ℍ := ℍ)) nP i = some (enLinN unitPJ) →
      erwp0 (ℍ := ℍ) Φe (opTableN (tabInN (PSJ (ℍ := ℍ)))) (Q₀ l A) k' ls'
        (.seq (performE (.val (opPayload nP i Val.unit))) (.val Val.unit)) (viewA l Val.unit A) :=
    fun i hi => by
      show erwp0 (ℍ := ℍ) _ _ _ _ _ ((Kont.seq .hole (.val Val.unit)).plug _) _
      refine erwp0_perform (en := enLinN unitPJ) _ (by simp [Kont.HasHnd]) hi rfl rfl
        (compS_empty_left _) ⟨rfl, rfl⟩ (fun ls'' _ k'' _ w σ₁ σ₂ hB hc => ?_)
      obtain ⟨rfl, rfl⟩ := hB
      obtain rfl := ResU.CompS.functional hc (ResU.comp_empty_right _)
      refine erwp0_det hΦ hTD hQ (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
      exact erwp0_val ⟨rfl, .inl rfl⟩
  cases b
  · exact htail 4 (by simp [tabInN])
  · exact htail 2 (by simp [tabInN])

/-! ### The root -/

/-- **The root**: the lend scope (`cerwp_scope`) around the body and the join, at the scheduler's
must-resume part, then `free ℓ`; lifted to the scheduler's table. -/
theorem rootI_ok (b : Bool) (n : Nat) :
    cerwp (ℍ := ℍ) (opTableC (TJC (ℍ := ℍ))) QinJ (fun _ => True) n [] [] (rootI b)
      (PMap.empty : WRes) := by
  have hLJ := opTableC_local (TJC (ℍ := ℍ))
  refine cerwp_allocX hLJ (.appR (.val (Val.lam (rootIT b))) .hole) Val.unit (fun l ρ' hc => ?_)
  obtain rfl := eq_of_compS_empty_left hc
  refine cerwp_det (opTableC_down TJC_down) QinJ_down
    (fun μ => step1Only_plug (Head.beta μ (rootIT b) (Val.loc l)) rfl .hole) ?_
  simp only [Kont.plug]
  rw [rootIT_subst]
  refine cerwp_tab_sub (tabLinC_sub (ℍ := ℍ) (PSJ (ℍ := ℍ))) ?_
  have hLL := opTableC_local (tabLinC (PSJ (ℍ := ℍ)))
  have hDL := tabLinC_down (spawnPAC_down (ℍ := ℍ) (tabAtC (ℍ := ℍ)))
  show cerwp (ℍ := ℍ) _ _ _ _ _ _ ((Kont.seq .hole (freeE (.val (Val.loc l)))).plug
    ((seqK nP 3 l).plug (bodyI b l))) _
  refine cerwp_bindK (Q' := Qsc l) (Kont.seq .hole (freeE (.val (Val.loc l)))) (fun _ => rfl)
    (fun _ _ _ h => tabLinC_lin h) (fun F k ls O v ρ hq => ?_) _ _ _ _ _ _ ?_
  · obtain ⟨rfl, rfl, hO⟩ := hq
    obtain rfl : O = [] := List.eq_nil_iff_forall_not_mem.mpr hO
    refine cerwp_det (opTableC_down hDL) QinJ_down
      (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    exact cerwp_freeX hLL .hole l Val.unit (ResU.comp_empty_right _) (cerwp_val ⟨rfl, .empty⟩)
  · -- the lend scope, `[TR]` 6.64 across stops
    have hshape : vShape .unk δ₀ Val.unit (PMap.empty : WRes) := ⟨rfl, trivial⟩
    have hadm : AdmWf .unk δ₀ := fun _ h => h.elim
    obtain ⟨ds, hds⟩ := lineage_list (r := recP l Val.unit .unk δ₀) hshape hadm
      (ExW.empty_of_all_imm (fun _ _ h => by simp [recP, PMap.empty_get] at h))
    refine cerwp_scope (Φ := Φe) (Q₀ := Q₀ l 0) l Val.unit .unk δ₀ hadm hshape 0 nP 3 hDL
      (scopeTabs _) (Qsc_down l) (fun _ _ _ _ h => h.1) [] ?_ _ _ [] (bodyI b l) PMap.empty _
      (inStratumE 0) (ResU.comp_empty_right _) (ResU.valid_single_own l _) ds hds
      (fun BI hBI => ?_)
    · intro k k₀ ls₀ ls' O' w₀ π ρout _ hq hO' hc
      have hnil : ∀ q, q ∉ O' := fun q hq => by
        obtain ⟨h₁, h₂⟩ := (hO' q).mp hq
        rcases List.mem_cons.mp h₁ with h | h
        · exact h₂ h
        · simp at h
      obtain ⟨-, hπ | hπ⟩ := hq
      · subst hπ
        rw [viewA_del] at hc
        obtain rfl := eq_of_compS_empty_left hc
        exact ⟨rfl, rfl, hnil⟩
      · subst hπ
        have : ResU.del (PMap.empty : WRes) l = PMap.empty := by
          refine PMap.ext fun m => ?_
          by_cases hm : m = l
          · subst hm; rw [ResU.del_get_self]; rfl
          · rw [ResU.del_get_ne _ hm]
        rw [this] at hc
        obtain rfl := eq_of_compS_empty_left hc
        exact ⟨rfl, rfl, hnil⟩
    · obtain rfl := eq_of_compS_empty_left hBI
      exact bodyI_ok b l 0 _ _

/-! ### The headlines -/

/-- **Case 1, the child resumed**: `(hnd HJ (rootI false)) (HJ, [])` is safe and leak-free or
diverges. The root lends `c` `imm` and spawns `λ_. parkC (); !c` into the scheduler's pool with a
copy of the borrow; it reads `!c` while the child is parked holding its copy, then `parkL`s to the
scheduler with the lend open; the child is resumed, reads `!c` and ends; the root is resumed, and
`join c` hands it the child's copy back; the lend ends and `c` is freed. Through
`poolSchedAdequacyC` (`progOfC_orDiverges`). -/
theorem crossImmJ : OrDiverges (ℍ := ℍ) (.app (hndE HJ (rootI false)) (stateValC HJ []).1) :=
  progOfC_orDiverges (rootI_ok false)

/-- **Case 1, the child cancelled**: as `crossImmJ`, the root `cancel`ling the child, the pool's
top, parked holding its copy; the child's cancel run hands the copy to the scheduler, and the
root's `join c` gets it back. -/
theorem crossImmJC : OrDiverges (ℍ := ℍ) (.app (hndE HJ (rootI true)) (stateValC HJ []).1) :=
  progOfC_orDiverges (rootI_ok true)

end BoCa.Fig16.LogRel.Core.Chain.SI.Cross821C

end
