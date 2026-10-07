import Core.EffPrograms
import Targets.I.Pins
import Targets.I.Restricted.Answering
import Targets.Base.Support
import Targets.Base.Data

/-!
# The interaction — witnesses for the pins and the device (RESTRUCTURE §4.5)

The platforms respect their protocol
(`platformNone_respects`, `platformPing_respects`); the rows a lend may span are inhabited
(`rowSpan_failSig`, `rowSpan_fooSig`, `rowSpan_suspSig`); the resuming tables are inhabited
(`resuming_fooSig`, `resuming_suspSig`); `I4a`'s hypotheses are met (`i4a_witness`,
`d_ansRun_witness`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.EffPrograms
open BoCa.Lifetime (LifeCtx LifeVar)

/-- `ping : 1 ↠^lin 1`, the operation `0` of the name `9`. -/
def pingSig : OpSig := ⟨9, 0, .lin, .unit, .unit⟩

/-- A platform with one operation, answering `()` and keeping its state. -/
def Platform.ping : Platform :=
  ⟨[pingSig], Unit, (), fun s n i _ => if n = 9 ∧ i = 0 then some (Val.unit, s) else Option.none⟩

theorem platformPing_respects : Platform.ping.Respects where
  uniq := List.pairwise_singleton _ _
  nz := by simp [Platform.ping, Row.NZ, pingSig]
  lin := by
    intro o h
    simp only [Platform.ping, List.mem_singleton] at h
    subst h; exact ⟨rfl, rfl⟩
  data := by
    intro o h
    simp only [Platform.ping, List.mem_singleton] at h
    subst h; exact ⟨.unit 0, .unit 0⟩
  total := by
    intro s o v h _
    simp only [Platform.ping, List.mem_singleton] at h
    subst h; exact ⟨Val.unit, s, by simp [Platform.ping, pingSig]⟩
  typed := by
    intro s s' o v w h _ hco
    simp only [Platform.ping, List.mem_singleton] at h
    subst h
    simp [Platform.ping, pingSig] at hco
    obtain ⟨rfl, -⟩ := hco
    exact .unit

theorem rowSpan_failSig (Δ : LifeCtx) (x : LifeVar) :
    RowSpan admClosedOp Δ x [failSig] ∧ RowClass.abortive.Admits [failSig] := by
  refine ⟨fun o ho => ?_, fun o ho => ?_⟩ <;> simp only [List.mem_singleton] at ho <;> subst ho
  · exact ⟨by decide, Or.inl rfl, by simp [failSig, VFree], by simp [failSig, VFree],
      fun _ _ => .unit, fun _ _ => .zero⟩
  · rfl

theorem rowSpan_fooSig (Δ : LifeCtx) (x : LifeVar) :
    RowSpan admClosedOp Δ x [fooSig] ∧ RowClass.resumeOnce.Admits [fooSig] := by
  refine ⟨fun o ho => ?_, fun o ho => ?_⟩ <;> simp only [List.mem_singleton] at ho <;> subst ho
  · exact ⟨by decide, Or.inr (by decide), by simp [fooSig, VFree], by simp [fooSig, VFree],
      fun _ _ => .unit, fun _ _ => .unit⟩
  · exact Or.inr rfl

theorem rowSpan_suspSig (Δ : LifeCtx) (x : LifeVar) :
    RowSpan admClosedOp Δ x [suspSig] ∧ RowClass.any.Admits [suspSig] := by
  refine ⟨fun o ho => ?_, ?_⟩
  · simp only [List.mem_singleton] at ho; subst ho
    exact ⟨by decide, Or.inr (by decide), by simp [suspSig, VFree], by simp [suspSig, VFree],
      fun _ _ => .unit, fun _ _ => .unit⟩
  · intro n i o h
    simp only [Row.find, List.find?_cons, List.find?_nil] at h
    split at h
    · cases h; right; decide
    · cases h

theorem resuming_fooSig (M : SemWorld) (δ : BoCa.Lifetime.LSub) :
    OpTabI.Resuming .resumeOnce (rowTabW M [fooSig] δ) := by
  intro n j en h
  simp only [rowTabW, Row.find, List.find?_cons, List.find?_nil] at h
  split at h
  · cases h; exact ⟨rfl, by simp [entW, fooSig], by decide, fun _ => rfl⟩
  · cases h

theorem resuming_suspSig (M : SemWorld) (δ : BoCa.Lifetime.LSub) :
    OpTabI.Resuming .any (rowTabW M [suspSig] δ) := by
  intro n j en h
  simp only [rowTabW, Row.find, List.find?_cons, List.find?_nil] at h
  split at h
  · cases h; exact ⟨rfl, by simp [entW, suspSig], by decide, fun h => by cases h⟩
  · cases h

/-- The answering implementation of a state `Flag` with no operation. -/
def flagImpl : AnsImpl := ⟨Flag, [], []⟩

/-- The body: forget the borrow, answer `()` at `['x]`. -/
def forgetBody : Expr := .seq (.app forget (.var 0)) (.val .unit)

theorem d_forgetBody :
    CDerives (LifeCtx.empty.extend 0 LifeCtx.empty.meetOfDom) [⟨.mut (.var 0) Flag, true⟩]
      forgetBody (.comp (CTy.effOf [failSig] (.box (.var 0) .unit))) := by
  refine .unitE (.left .nil) (.lolliE (.left .nil) (.var (.here .nil)) (.forgetMut (.cons .nil)))
    (.effSub (S := []) (fun _ _ _ h => by simp [Row.find] at h)
      (.ret (.boxI (.unitI (.cons .nil)) ⟨LifeCtx.defines_of_wf rfl, ?_⟩)))
  intro s hs hl
  simp only [List.mem_singleton] at hs; subst hs; cases hl

/-- **Every hypothesis of `I4a tier1 admClosedOp .abortive` is met** at the abortive row
`[failSig]`. -/
theorem i4a_witness :
    ImplTyped tier1 flagImpl ∧ Ctx.DeadP ([] : Ctx VTy) ∧ LifeCtx.empty.find? 0 = Option.none ∧
    (∀ y u, LifeCtx.empty.find? y = some u → u.mentions 0 = false) ∧
    (∀ s ∈ ([] : Ctx VTy), s.live = true → ¬ VFree 0 s.ty) ∧ ¬ VFree 0 flagImpl.S ∧
    ¬ VFree 0 (.unit : VTy) ∧
    (∃ b, LifeCtx.empty.Defines b ∧ tier1.out.le LifeCtx.empty b flagImpl.S) ∧
    RowSpan admClosedOp LifeCtx.empty 0 [failSig] ∧ RowClass.abortive.Admits [failSig] ∧
    closedAt 0 dFlag = true ∧
    tier1.at LifeCtx.empty [] (.inj₁ (.val .unit)) (.val flagImpl.S) ∧
    tier1.at LifeCtx.empty [] dFlag (.val (.lolli (.ref flagImpl.S) .unit)) ∧
    tier1.at (LifeCtx.empty.extend 0 LifeCtx.empty.meetOfDom) [⟨.mut (.var 0) flagImpl.S, true⟩]
      forgetBody (.comp (CTy.effOf [failSig] (.box (.var 0) .unit))) := by
  have hΔ : ∀ y u, LifeCtx.empty.find? y = some u → u.mentions 0 = false := by
    intro y u h
    simp [LifeCtx.find?, LifeCtx.empty, Lifetime.assocFind] at h
  have hΓ : ∀ s ∈ ([] : Ctx VTy), s.live = true → ¬ VFree 0 s.ty := fun _ hs => nomatch hs
  have hS : ¬ VFree 0 flagImpl.S := by simp [flagImpl, VFree]
  have hB : ¬ VFree 0 (.unit : VTy) := by simp [VFree]
  have hside : ∃ b, LifeCtx.empty.Defines b ∧ tier1.out.le LifeCtx.empty b flagImpl.S :=
    ⟨.top, LifeCtx.defines_of_wf rfl, (outlives_of_dataB rfl).toLe⟩
  have hs₀ : tier1.at LifeCtx.empty [] (.inj₁ (.val .unit)) (.val flagImpl.S) :=
    fun _ _ => .sumI₁ (.unitI .nil)
  have hd : tier1.at LifeCtx.empty [] dFlag (.val (.lolli (.ref flagImpl.S) .unit)) :=
    fun _ _ => dtor_wf (.ref (.sum .unit .unit)) .nil
  exact ⟨.nil, .nil, rfl, hΔ, hΓ, hS, hB, hside, (rowSpan_failSig _ _).1, (rowSpan_failSig LifeCtx.empty 0).2,
    dFlag_closed, hs₀, hd, fun _ _ => d_forgetBody⟩

/-- The borrow form it types: `with h(inj₁ ()) { forget m; () }` at `F_{[failSig]}(Flag ⊗ 1)`. -/
theorem d_ansRun_witness :
    tier1.at LifeCtx.empty [] (ansRun dFlag (.inj₁ (.val .unit)) forgetBody)
      (.comp (CTy.effOf [failSig] (.tensor Flag .unit))) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄⟩ := i4a_witness
  exact i4a_tier1 flagImpl LifeCtx.empty [] 0 [failSig] dFlag (.inj₁ (.val .unit)) forgetBody .unit
    h₁ h₂ h₃ h₄ h₅ h₆ h₇ h₈ h₉ h₁₀ h₁₁ h₁₂ h₁₃ h₁₄

end Targets

end
