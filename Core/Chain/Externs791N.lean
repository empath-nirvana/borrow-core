import Core.Chain.Adequacy791N
import Core.Stdio
import Core.Closed

/-!
# The standard externs at the typed world  `[spec §72]`

The models of `Core/Stdio.lean` meet the chain's extern contract `ExternN`, and the chain's
end-to-end theorems for I/O programs, read from `goal791N`.

* **Representation.** The relation `vN` at an opaque host type is the relation at its
  representation: `vN_bytesRep` (`Input`), `vN_argsRep` (`Args`), `vN_outRep` (`Output`),
  `vN_clockRep` (`Clock`), each an equation of predicates at every lifetime substitution, Core's
  `vC_*Rep` form. The relation at an extern's type depends on its payload type only through
  `vN` at it (`cN_*C_congr`), so it is the same at the representation and at the opaque type.
* **The models meet `ExternN`.** `meets_of_derivesN`: a closed value with a derivation at a
  computation type other than `F` meets `ExternN` at `!U` of that type, by `fundamentalN_all`
  from `HandlerLawN`. The 15 `*_meetsN` read each model's derivation `d_*` there and move it to
  the opaque type; `stdModel_meetsN` lists them; `externsMeetN_of_model` gives `ExternsMeetN`
  for externs each given its model.
* **End to end.** `externs_every_runN`, `io_every_runN`: `run_io : Bytes ⊸ F R`, `R`
  persistent, at a context of externs meeting `ExternN`: the run of `run_io[γ] inp` is safe,
  ends at the empty memory, or diverges. The input is one more extern slot at the end of the
  context, a closed value of `Bytes` (`externN_bytes`), and the program is `run_io` applied to
  that slot, so the theorem is `goal791N` at no constants. `externs_loop_every_runN`,
  `io_loop_every_runN`: the same for `run_io : Bytes ⊸ F (U (Loop R R'))` driven `n` times.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel (LtLife substAll)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Fig16.Tree.Wp.Goal791 (Const791 ctx791 vals791)

/-! ### The opaque types read as their representations -/

/-- The relation at `Bytes` holds exactly at a byte list, with no resource.  `[spec §72]` -/
theorem vN_bytes_iff {δ : LSub} {Θ : LocTy} {n : Nat} {v : Val} {ρ : WRes} :
    vN (ℍ := ℍ) bytesTy δ Θ n v ρ ↔ ρ = PMap.empty ∧ BytesV v := by
  constructor
  · intro h
    refine vBN_mu_ind (η := none) (A := bytesBody) (δ := δ)
      (fun _ _ _ v ρ => ρ = PMap.empty ∧ BytesV v) ?_ true Θ n v ρ h
    rintro b Θ' k w r - - hb
    cases b
    · rcases hb with ⟨w₁, rfl, rfl, rfl⟩ |
        ⟨w₂, rfl, w₁, w₃, r₁, r₂, rfl, hc, ⟨⟨m, rfl⟩, rfl⟩, -, rfl, hB⟩
      · exact ⟨rfl, .nil⟩
      · exact ⟨eq_empty_of_compS_empty hc, .cons m hB⟩
    · rcases hb with ⟨w₁, rfl, rfl, rfl⟩ |
        ⟨w₂, rfl, w₁, w₃, r₁, r₂, rfl, hc, ⟨⟨m, rfl⟩, rfl⟩, -, rfl, hB⟩
      · exact ⟨rfl, .nil⟩
      · exact ⟨eq_empty_of_compS_empty hc, .cons m hB⟩
  · rintro ⟨rfl, hB⟩
    induction hB with
    | nil =>
        refine vN_roll bytesBody_noMut bytesTy_closed ?_
        show vN (ℍ := ℍ) (.sum .unit (.tensor (.int .w8) bytesTy)) δ Θ n _ _
        exact Or.inl ⟨_, rfl, rfl, rfl⟩
    | cons m _ ih =>
        refine vN_roll bytesBody_noMut bytesTy_closed ?_
        show vN (ℍ := ℍ) (.sum .unit (.tensor (.int .w8) bytesTy)) δ Θ n _ _
        exact Or.inr ⟨_, rfl, _, _, PMap.empty, PMap.empty, rfl, ResU.comp_empty_right _,
          ⟨⟨m, rfl⟩, rfl⟩, ih⟩

/-- **`Input` is `Bytes` with the rules taken away**, at the typed world.  `[spec §72]` -/
theorem vN_bytesRep (δ : LSub) : vN (ℍ := ℍ) bytesTy δ = vN (ℍ := ℍ) (.opq .input) δ := by
  funext Θ n v ρ
  exact propext (vN_bytes_iff.trans ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩)

/-- **`Args` is `Bytes` with the rules taken away**, as `Input` is.  `[spec §72]` -/
theorem vN_argsRep (δ : LSub) : vN (ℍ := ℍ) bytesTy δ = vN (ℍ := ℍ) (.opq .args) δ := by
  funext Θ n v ρ
  exact propext (vN_bytes_iff.trans ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩)

/-- **`Output` is `I32 ⊗ Bytes` with the rules taken away.**  `[spec §72]` -/
theorem vN_outRep (δ : LSub) : vN (ℍ := ℍ) outRep δ = vN (ℍ := ℍ) (.opq .output) δ := by
  funext Θ n v ρ
  apply propext
  constructor
  · rintro ⟨v₁, v₂, ρ₁, ρ₂, rfl, hc, ⟨⟨m, rfl⟩, rfl⟩, h₂⟩
    obtain ⟨rfl, hB⟩ := vN_bytes_iff.mp h₂
    exact ⟨eq_empty_of_compS_empty hc, m, v₂, rfl, hB⟩
  · rintro ⟨rfl, m, bs, rfl, hB⟩
    exact ⟨_, _, PMap.empty, PMap.empty, rfl, ResU.comp_empty_right _, ⟨⟨m, rfl⟩, rfl⟩,
      vN_bytes_iff.mpr ⟨rfl, hB⟩⟩

/-- **`Clock` is `I64` with the rules taken away.**  `[spec §72]` -/
theorem vN_clockRep (δ : LSub) : vN (ℍ := ℍ) .i64 δ = vN (ℍ := ℍ) (.opq .clock) δ := by
  funext Θ n v ρ
  exact propext ⟨fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩, fun ⟨h₁, h₂⟩ => ⟨h₂, h₁⟩⟩

/-! ### The extern types depend on the payload only through `vN` at it -/

theorem cN_readByteC_congr {I₁ I₂ : VTy} (h : vNE (ℍ := ℍ) none I₁ = vNE (ℍ := ℍ) none I₂) :
    cN (ℍ := ℍ) (readByteC I₁) = cN (ℍ := ℍ) (readByteC I₂) := by
  funext δ Θ c n ls e ρ
  simp only [readByteC, cN, vNE, forceE]
  rw [h]

theorem cN_writeByteC_congr {O₁ O₂ : VTy} (h : vNE (ℍ := ℍ) none O₁ = vNE (ℍ := ℍ) none O₂) :
    cN (ℍ := ℍ) (writeByteC O₁) = cN (ℍ := ℍ) (writeByteC O₂) := by
  funext δ Θ c n ls e ρ
  simp only [writeByteC, cN, vNE, forceE]
  rw [h]

theorem cN_mkInputC_congr {I₁ I₂ : VTy} (h : vNE (ℍ := ℍ) none I₁ = vNE (ℍ := ℍ) none I₂) :
    cN (ℍ := ℍ) (mkInputC I₁) = cN (ℍ := ℍ) (mkInputC I₂) := by
  funext δ Θ c n ls e ρ
  simp only [mkInputC, cN, vNE]
  rw [h]

theorem cN_mkOutputC_congr {O₁ O₂ : VTy} (h : vNE (ℍ := ℍ) none O₁ = vNE (ℍ := ℍ) none O₂) :
    cN (ℍ := ℍ) (mkOutputC O₁) = cN (ℍ := ℍ) (mkOutputC O₂) := by
  funext δ Θ c n ls e ρ
  simp only [mkOutputC, cN, vNE]
  rw [h]

theorem cN_takeInputC_congr {I₁ I₂ : VTy} (h : vNE (ℍ := ℍ) none I₁ = vNE (ℍ := ℍ) none I₂) :
    cN (ℍ := ℍ) (takeInputC I₁) = cN (ℍ := ℍ) (takeInputC I₂) := by
  funext δ Θ c n ls e ρ
  simp only [takeInputC, cN, vNE]
  rw [h]

theorem cN_takeOutputC_congr {O₁ O₂ : VTy} (h : vNE (ℍ := ℍ) none O₁ = vNE (ℍ := ℍ) none O₂) :
    cN (ℍ := ℍ) (takeOutputC O₁) = cN (ℍ := ℍ) (takeOutputC O₂) := by
  funext δ Θ c n ls e ρ
  simp only [takeOutputC, cN, vNE]
  rw [h]

theorem cN_writeAllC_congr {O₁ O₂ : VTy} (h : vNE (ℍ := ℍ) none O₁ = vNE (ℍ := ℍ) none O₂) :
    cN (ℍ := ℍ) (writeAllC O₁) = cN (ℍ := ℍ) (writeAllC O₂) := by
  funext δ Θ c n ls e ρ
  simp only [writeAllC, cN, vNE, forceE]
  rw [h]

theorem cN_readIntoC_congr {I₁ I₂ : VTy} (h : vNE (ℍ := ℍ) none I₁ = vNE (ℍ := ℍ) none I₂) :
    cN (ℍ := ℍ) (readIntoC I₁) = cN (ℍ := ℍ) (readIntoC I₂) := by
  funext δ Θ c n ls e ρ
  simp only [readIntoC, cN, vNE, forceE]
  rw [h]

theorem cN_clockNowC_congr {C₁ C₂ : VTy} (h : vNE (ℍ := ℍ) none C₁ = vNE (ℍ := ℍ) none C₂) :
    cN (ℍ := ℍ) (clockNowC C₁) = cN (ℍ := ℍ) (clockNowC C₂) := by
  funext δ Θ c n ls e ρ
  simp only [clockNowC, cN, vNE, forceE]
  rw [h]

theorem cN_clockSleepC_congr {C₁ C₂ : VTy} (h : vNE (ℍ := ℍ) none C₁ = vNE (ℍ := ℍ) none C₂) :
    cN (ℍ := ℍ) (clockSleepC C₁) = cN (ℍ := ℍ) (clockSleepC C₂) := by
  funext δ Θ c n ls e ρ
  simp only [clockSleepC, cN, vNE, forceE]
  rw [h]

theorem cN_mkClockC_congr {C₁ C₂ : VTy} (h : vNE (ℍ := ℍ) none C₁ = vNE (ℍ := ℍ) none C₂) :
    cN (ℍ := ℍ) (mkClockC C₁) = cN (ℍ := ℍ) (mkClockC C₂) := by
  funext δ Θ c n ls e ρ
  simp only [mkClockC, cN, vNE]
  rw [h]

theorem cN_takeClockC_congr {C₁ C₂ : VTy} (h : vNE (ℍ := ℍ) none C₁ = vNE (ℍ := ℍ) none C₂) :
    cN (ℍ := ℍ) (takeClockC C₁) = cN (ℍ := ℍ) (takeClockC C₂) := by
  funext δ Θ c n ls e ρ
  simp only [takeClockC, cN, vNE]
  rw [h]

/-- The relation at `!U C` depends on `C` only through `cN C`. -/
theorem vN_externTy_congrN {C₁ C₂ : CTy} (h₁ : C₁.isRet = false) (h₂ : C₂.isRet = false)
    (h : cN (ℍ := ℍ) C₁ = cN (ℍ := ℍ) C₂) :
    vN (ℍ := ℍ) (externTy C₁) = vN (ℍ := ℍ) (externTy C₂) := by
  funext δ Θ n v ρ
  simp only [vNE, forceE_of_not_ret h₁, forceE_of_not_ret h₂]
  rw [h]

/-! ### The models meet the contract -/

/-- **A closed value typed at a computation type other than `F` meets `ExternN` at `!U` of
it**: the fundamental property at the empty context, from `HandlerLawN`.  `[spec §72]` -/
theorem meets_of_derivesN (hL : HandlerLawN (ℍ := ℍ)) {v : Val} {C : CTy} (hC : C.isRet = false)
    (h : CDerives LifeCtx.empty [] (.val v) (.comp C)) : ExternN (ℍ := ℍ) (externTy C) v := by
  refine ⟨closedAt_of_derives h, rfl, fun δ Θ n _ => ⟨rfl, fun Θ' _ hΘ' c hc ls => ?_⟩⟩
  have hs := fundamentalN_all (handlerLawN_iff.mp hL) h δ [] Θ' c n ls PMap.empty
    (models_empty_any δ) hΘ' hc trivial rfl
  rw [show substAll [] (Expr.val v) = Expr.val v from Adequacy.psub_nil 0 _] at hs
  rw [forceE_of_not_ret hC]
  exact hs

/-- A model typed at the representation meets `ExternN` at the opaque type, when the two extern
types are related alike.  `[spec §72]` -/
theorem externN_of_rep (hL : HandlerLawN (ℍ := ℍ)) {v : Val} {C₁ C₂ : CTy}
    (h₁ : C₁.isRet = false) (h₂ : C₂.isRet = false) (hc : cN (ℍ := ℍ) C₁ = cN (ℍ := ℍ) C₂)
    (hd : CDerives LifeCtx.empty [] (.val v) (.comp C₁)) : ExternN (ℍ := ℍ) (externTy C₂) v := by
  obtain ⟨hcl, -, hv⟩ := meets_of_derivesN hL h₁ hd
  refine ⟨hcl, rfl, fun δ Θ n hΘ => ?_⟩
  rw [← vN_externTy_congrN h₁ h₂ hc]
  exact hv δ Θ n hΘ

/-- **The model of `read_byte` meets `ExternN`.**  `[spec §72]` -/
theorem readByte_meetsN (hL : HandlerLawN (ℍ := ℍ)) :
    ExternN (ℍ := ℍ) (externTy (readByteC (.opq .input))) readByteV :=
  externN_of_rep hL rfl rfl (cN_readByteC_congr (funext vN_bytesRep)) d_readByte

/-- **The model of `write_byte` meets `ExternN`.**  `[spec §72]` -/
theorem writeByte_meetsN (hL : HandlerLawN (ℍ := ℍ)) :
    ExternN (ℍ := ℍ) (externTy (writeByteC (.opq .output))) writeByteV :=
  externN_of_rep hL rfl rfl (cN_writeByteC_congr (funext vN_outRep)) d_writeByte

/-- **The model of `mk_input` meets `ExternN`.**  `[spec §72]` -/
theorem mkInput_meetsN (hL : HandlerLawN (ℍ := ℍ)) :
    ExternN (ℍ := ℍ) (externTy (mkInputC (.opq .input))) mkInputV :=
  externN_of_rep hL rfl rfl (cN_mkInputC_congr (funext vN_bytesRep)) d_mkInput

/-- **The model of `mk_output` meets `ExternN`.**  `[spec §72]` -/
theorem mkOutput_meetsN (hL : HandlerLawN (ℍ := ℍ)) :
    ExternN (ℍ := ℍ) (externTy (mkOutputC (.opq .output))) mkOutputV :=
  externN_of_rep hL rfl rfl (cN_mkOutputC_congr (funext vN_outRep)) d_mkOutput

/-- **The model of `take_input` meets `ExternN`.**  `[spec §72]` -/
theorem takeInput_meetsN (hL : HandlerLawN (ℍ := ℍ)) :
    ExternN (ℍ := ℍ) (externTy (takeInputC (.opq .input))) takeCapV :=
  externN_of_rep hL rfl rfl (cN_takeInputC_congr (funext vN_bytesRep)) d_takeInput

/-- **The model of `take_output` meets `ExternN`.**  `[spec §72]` -/
theorem takeOutput_meetsN (hL : HandlerLawN (ℍ := ℍ)) :
    ExternN (ℍ := ℍ) (externTy (takeOutputC (.opq .output))) takeCapV :=
  externN_of_rep hL rfl rfl (cN_takeOutputC_congr (funext vN_outRep)) d_takeOutput

/-- **The model of `write_all` meets `ExternN`.**  `[spec §72]` -/
theorem writeAll_meetsN (hL : HandlerLawN (ℍ := ℍ)) :
    ExternN (ℍ := ℍ) (externTy (writeAllC (.opq .output))) writeAllV :=
  externN_of_rep hL rfl rfl (cN_writeAllC_congr (funext vN_outRep)) d_writeAll

/-- **The model of `read_into` meets `ExternN`.**  `[spec §72]` -/
theorem readInto_meetsN (hL : HandlerLawN (ℍ := ℍ)) :
    ExternN (ℍ := ℍ) (externTy (readIntoC (.opq .input))) readIntoV :=
  externN_of_rep hL rfl rfl (cN_readIntoC_congr (funext vN_bytesRep)) d_readInto

/-- **The model of `clock_now` meets `ExternN`.**  `[spec §72]` -/
theorem clockNow_meetsN (hL : HandlerLawN (ℍ := ℍ)) :
    ExternN (ℍ := ℍ) (externTy (clockNowC (.opq .clock))) clockNowV :=
  externN_of_rep hL rfl rfl (cN_clockNowC_congr (funext vN_clockRep)) d_clockNow

/-- **The model of `clock_sleep` meets `ExternN`.**  `[spec §72]` -/
theorem clockSleep_meetsN (hL : HandlerLawN (ℍ := ℍ)) :
    ExternN (ℍ := ℍ) (externTy (clockSleepC (.opq .clock))) clockSleepV :=
  externN_of_rep hL rfl rfl (cN_clockSleepC_congr (funext vN_clockRep)) d_clockSleep

/-- **The model of `mk_clock` meets `ExternN`.**  `[spec §72]` -/
theorem mkClock_meetsN (hL : HandlerLawN (ℍ := ℍ)) :
    ExternN (ℍ := ℍ) (externTy (mkClockC (.opq .clock))) mkClockV :=
  externN_of_rep hL rfl rfl (cN_mkClockC_congr (funext vN_clockRep)) d_mkClock

/-- **The model of `take_clock` meets `ExternN`.**  `[spec §72]` -/
theorem takeClock_meetsN (hL : HandlerLawN (ℍ := ℍ)) :
    ExternN (ℍ := ℍ) (externTy (takeClockC (.opq .clock))) takeCapV :=
  externN_of_rep hL rfl rfl (cN_takeClockC_congr (funext vN_clockRep)) d_takeClock

/-- **The model of `read_arg` meets `ExternN`**: `read_byte`'s, at `Args`.  `[spec §72]` -/
theorem readArg_meetsN (hL : HandlerLawN (ℍ := ℍ)) :
    ExternN (ℍ := ℍ) (externTy (readByteC (.opq .args))) readByteV :=
  externN_of_rep hL rfl rfl (cN_readByteC_congr (funext vN_argsRep)) d_readByte

/-- **The model of `mk_args` meets `ExternN`**: `mk_input`'s, at `Args`.  `[spec §72]` -/
theorem mkArgs_meetsN (hL : HandlerLawN (ℍ := ℍ)) :
    ExternN (ℍ := ℍ) (externTy (mkInputC (.opq .args))) mkInputV :=
  externN_of_rep hL rfl rfl (cN_mkInputC_congr (funext vN_argsRep)) d_mkInput

/-- **The model of `take_args` meets `ExternN`**: `take_input`'s, at `Args`.  `[spec §72]` -/
theorem takeArgs_meetsN (hL : HandlerLawN (ℍ := ℍ)) :
    ExternN (ℍ := ℍ) (externTy (takeInputC (.opq .args))) takeCapV :=
  externN_of_rep hL rfl rfl (cN_takeInputC_congr (funext vN_argsRep)) d_takeInput

/-- **Every standard model meets `ExternN`**, from `HandlerLawN`.  `[spec §72]` -/
theorem stdModel_meetsN (hL : HandlerLawN (ℍ := ℍ)) :
    ∀ p ∈ stdModel, ExternN (ℍ := ℍ) p.1 p.2 := by
  intro p hp
  simp only [stdModel, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · exact readByte_meetsN hL
  · exact writeByte_meetsN hL
  · exact mkInput_meetsN hL
  · exact mkOutput_meetsN hL
  · exact takeInput_meetsN hL
  · exact takeOutput_meetsN hL
  · exact writeAll_meetsN hL
  · exact readInto_meetsN hL
  · exact clockNow_meetsN hL
  · exact clockSleep_meetsN hL
  · exact mkClock_meetsN hL
  · exact takeClock_meetsN hL
  · exact readArg_meetsN hL
  · exact mkArgs_meetsN hL
  · exact takeArgs_meetsN hL

/-- **Externs each given its model meet their contracts.**  `[spec §72]` -/
theorem externsMeetN_of_model (hL : HandlerLawN (ℍ := ℍ)) : ∀ {Γ : Ctx VTy} {γ : List Val},
    List.Forall₂ (fun s v => s.live = true ∧ (s.ty, v) ∈ stdModel) Γ γ →
      ExternsMeetN (ℍ := ℍ) Γ γ
  | [], [], .nil => .nil
  | ⟨_, l⟩ :: _, _ :: _, .cons ⟨hl, hm⟩ h => by
      simp only at hl; subst hl
      exact .cons (stdModel_meetsN hL _ hm) (externsMeetN_of_model hL h)

/-! ### The input as one more extern -/

/-- A byte list is closed. -/
theorem closedAt_of_bytesV {v : Val} (h : BytesV v) : closedAt 0 v.1 = true := by
  induction h with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- **A byte list meets `ExternN` at `Bytes`**: it is closed, `Bytes` is persistent, and it is a
value of `Bytes` with no resource.  `[spec §72]` -/
theorem externN_bytes {v : Val} (h : BytesV v) : ExternN (ℍ := ℍ) bytesTy v :=
  ⟨closedAt_of_bytesV h, rfl, fun _ _ _ _ => vN_bytes_iff.mpr ⟨rfl, h⟩⟩

theorem length_of_meetsN {Γ : Ctx VTy} {γ : List Val} (h : ExternsMeetN (ℍ := ℍ) Γ γ) :
    γ.length = Γ.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- One more extern at the end of the context. -/
theorem meetsN_snoc {T : VTy} {v : Val} (hv : ExternN (ℍ := ℍ) T v) :
    ∀ {Γ : Ctx VTy} {γ : List Val}, ExternsMeetN (ℍ := ℍ) Γ γ →
      ExternsMeetN (ℍ := ℍ) (Γ ++ [⟨T, true⟩]) (γ ++ [v])
  | _, _, .nil => .cons hv .nil
  | _, _, .cons hw h => .cons hw (meetsN_snoc hv h)

/-- The last slot to the right, every other slot as before. -/
theorem splitP_snoc_right {T : VTy} : ∀ {Γ Γ₁ Γ₂ : Ctx VTy}, Ctx.SplitP Γ Γ₁ Γ₂ →
    Ctx.SplitP (Γ ++ [⟨T, true⟩]) (Γ₁ ++ [⟨T, false⟩]) (Γ₂ ++ [⟨T, true⟩])
  | _, _, _, .nil => .right .nil
  | _, _, _, .left h => .left (splitP_snoc_right h)
  | _, _, _, .right h => .right (splitP_snoc_right h)
  | _, _, _, .dead h => .dead (splitP_snoc_right h)
  | _, _, _, .dup hT h => .dup hT (splitP_snoc_right h)

/-- The last slot alone, after a consumed context. -/
theorem soloP_kill_snoc (T : VTy) : ∀ Γ : Ctx VTy, Ctx.SoloP (kill Γ ++ [⟨T, true⟩]) Γ.length T
  | [] => .here .nil
  | _ :: Γ => .there (soloP_kill_snoc T Γ)

/-- **`run_io` applied to the input slot** is typed at `F R`, in the context with the input as
its last slot. -/
theorem d_runInput {Γ : Ctx VTy} {e : Expr} {R : VTy}
    (h : CDerives LifeCtx.empty Γ e (.comp (.arr bytesTy (.ret R)))) :
    CDerives LifeCtx.empty (Γ ++ [⟨bytesTy, true⟩]) (.app e (.var Γ.length)) (.comp (.ret R)) :=
  .app (splitP_snoc_right (splitP_left_all Γ)) (CDerives.append_dead (.cons .nil) h)
    (soloP_kill_snoc bytesTy Γ)

/-- A closing substitution with more values than a term's free variables reads only the first. -/
theorem psub_append_of_closedAt : ∀ (e : Expr) {j k : Nat} (γ γ' : List Val),
    closedAt j e = true → j ≤ k + γ.length → Expr.psub k (γ ++ γ') e = Expr.psub k γ e
  | .var i, _, k, γ, γ', h, hj => by
      simp only [closedAt, decide_eq_true_eq] at h
      simp only [Expr.psub]
      split
      · rfl
      · rw [List.getElem?_append_left (by omega), List.getElem?_eq_getElem (by omega)]
  | .unit, _, _, _, _, _, _ => rfl
  | .pair e₁ e₂, _, _, γ, γ', h, hj => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.psub, psub_append_of_closedAt e₁ γ γ' h.1 hj,
        psub_append_of_closedAt e₂ γ γ' h.2 hj]
  | .inj₁ e, _, _, γ, γ', h, hj => by
      simp only [Expr.psub, psub_append_of_closedAt e γ γ' h hj]
  | .inj₂ e, _, _, γ, γ', h, hj => by
      simp only [Expr.psub, psub_append_of_closedAt e γ γ' h hj]
  | .lam b, j, k, γ, γ', h, hj => by
      simp only [Expr.psub, psub_append_of_closedAt b (j := j + 1) (k := k + 1) γ γ' h (by omega)]
  | .loc _, _, _, _, _, _, _ => rfl
  | .prim _, _, _, _, _, _, _ => rfl
  | .seq e₁ e₂, _, _, γ, γ', h, hj => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.psub, psub_append_of_closedAt e₁ γ γ' h.1 hj,
        psub_append_of_closedAt e₂ γ γ' h.2 hj]
  | .letpair e₁ e₂, j, k, γ, γ', h, hj => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.psub, psub_append_of_closedAt e₁ γ γ' h.1 hj,
        psub_append_of_closedAt e₂ (j := j + 2) (k := k + 2) γ γ' h.2 (by omega)]
  | .case e e₁ e₂, j, k, γ, γ', h, hj => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.psub, psub_append_of_closedAt e γ γ' h.1.1 hj,
        psub_append_of_closedAt e₁ (j := j + 1) (k := k + 1) γ γ' h.1.2 (by omega),
        psub_append_of_closedAt e₂ (j := j + 1) (k := k + 1) γ γ' h.2 (by omega)]
  | .app f a, _, _, γ, γ', h, hj => by
      simp only [closedAt, Bool.and_eq_true] at h
      simp only [Expr.psub, psub_append_of_closedAt f γ γ' h.1 hj,
        psub_append_of_closedAt a γ γ' h.2 hj]

/-- `run_io` applied to the input slot, closed by the externs and the input, is `run_io[γ] inp`. -/
theorem substAll_runInput {Γ : Ctx VTy} {e : Expr} {j : Jdg} (h : CDerives LifeCtx.empty Γ e j)
    {γ : List Val} (hl : γ.length = Γ.length) (inp : Val) :
    substAll (γ ++ [inp]) (.app e (.var Γ.length)) = .app (substAll γ e) (.val inp) := by
  show Expr.app (Expr.psub 0 (γ ++ [inp]) e) (Expr.psub 0 (γ ++ [inp]) (.var Γ.length)) = _
  rw [psub_append_of_closedAt e γ [inp] (closedAt_of_derives h) (by omega)]
  congr 1
  simp [Expr.psub, ← hl, Val.shift_zero]

/-! ### End to end -/

/-- **End to end, at every implementation of the externs meeting `ExternN`.** `run_io : Bytes ⊸
F R` is checked at a context of externs, `R` is persistent, and `γ` meets `ExternN` slot by slot.
Then for every input byte list, the run of `run_io[γ] inp` from the empty memory is safe, ends at
the empty memory, or diverges. The statement is `goal791N` at no constants: the input is one more
extern slot at the end of the context (`Γ ++ [⟨bytesTy, true⟩]`, `γ ++ [inp]`, meeting `ExternN`
by `externN_bytes`), and the program is `run_io` applied to that slot (`.app e (.var Γ.length)`,
typed by `d_runInput`), since `CDerives`'s application takes a variable; closed by `γ ++ [inp]`
it is `run_io[γ] inp` (`substAll_runInput`).  `[spec §72]` -/
theorem externs_every_runN (hL : HandlerLawN (ℍ := ℍ)) {Γ : Ctx VTy} {e : Expr} {R : VTy}
    (h : CDerives LifeCtx.empty Γ e (.comp (.arr bytesTy (.ret R)))) (hR : R.Persistent)
    {γ : List Val} (hγ : ExternsMeetN (ℍ := ℍ) Γ γ) {inp : Val} (hin : BytesV inp) :
    OrDiverges (ℍ := ℍ) (.app (substAll γ e) (.val inp)) := by
  have hg : OrDiverges (ℍ := ℍ) (substAll (γ ++ [inp]) (.app e (.var Γ.length))) :=
    goal791N hL [] (Γ ++ [⟨bytesTy, true⟩]) (γ ++ [inp]) (.app e (.var Γ.length)) R
      (fun _ h => nomatch h) (meetsN_snoc (externN_bytes hin) hγ) (d_runInput h) hR
  rwa [substAll_runInput h (length_of_meetsN hγ) inp] at hg

/-- **End to end, the model.** `bcc interp`'s run: `run_io` with every extern given its model is
safe, ends at the empty memory, or diverges, from `HandlerLawN`.  `[spec §72]` -/
theorem io_every_runN (hL : HandlerLawN (ℍ := ℍ)) {Γ : Ctx VTy} {e : Expr} {R : VTy}
    (h : CDerives LifeCtx.empty Γ e (.comp (.arr bytesTy (.ret R)))) (hR : R.Persistent)
    {γ : List Val} (hγ : List.Forall₂ (fun s v => s.live = true ∧ (s.ty, v) ∈ stdModel) Γ γ)
    {inp : Val} (hin : BytesV inp) :
    OrDiverges (ℍ := ℍ) (.app (substAll γ e) (.val inp)) :=
  externs_every_runN hL h hR (externsMeetN_of_model hL hγ) hin

/-- **End to end for a program that runs until its input ends, at every implementation of the
externs meeting `ExternN`.** `run_io : Bytes ⊸ F (U (Loop R R'))`, both residuals persistent. For
every input and every `n`, `run_io[γ] inp` observed at most `n` times is safe, ends at the empty
memory, or diverges: `goal791N` at no constants, at the driven program.  `[spec §72]` -/
theorem externs_loop_every_runN (hL : HandlerLawN (ℍ := ℍ)) {Γ : Ctx VTy} {N : Expr}
    {R R' : VTy}
    (h : CDerives LifeCtx.empty Γ (.val (.lam N)) (.comp (.arr bytesTy (.ret (.thunk (.loop R R'))))))
    (hR : R.Persistent) (hR' : R'.Persistent) {γ : List Val} (hγ : ExternsMeetN (ℍ := ℍ) Γ γ)
    (bs : List UInt8) (n : ℕ) : OrDiverges (ℍ := ℍ) (substAll γ (ioLoopE N bs n)) := by
  have hS : (VTy.sum R R').Persistent := by
    simp only [VTy.Persistent, VTy.persistent, Bool.and_eq_true]; exact ⟨hR, hR'⟩
  have hg : OrDiverges (ℍ := ℍ) (substAll (vals791 [] ++ γ) (ioLoopE N bs n)) :=
    goal791N hL [] Γ γ (ioLoopE N bs n) (.sum R R') (fun _ h => nomatch h) hγ (d_ioLoop h bs n) hS
  intro μ e hs
  exact hg hs

/-- **End to end for a program that runs until its input ends, at the model.**  `[spec §72]` -/
theorem io_loop_every_runN (hL : HandlerLawN (ℍ := ℍ)) {Γ : Ctx VTy} {N : Expr} {R R' : VTy}
    (h : CDerives LifeCtx.empty Γ (.val (.lam N)) (.comp (.arr bytesTy (.ret (.thunk (.loop R R'))))))
    (hR : R.Persistent) (hR' : R'.Persistent) {γ : List Val}
    (hγ : List.Forall₂ (fun s v => s.live = true ∧ (s.ty, v) ∈ stdModel) Γ γ)
    (bs : List UInt8) (n : ℕ) : OrDiverges (ℍ := ℍ) (substAll γ (ioLoopE N bs n)) :=
  externs_loop_every_runN hL h hR hR' (externsMeetN_of_model hL hγ) bs n

end BoCa.Fig16.LogRel.Core.Chain.SI.Goal791N

end
