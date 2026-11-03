import HandleSpike.Handle
import HandleSpike.Counter

/-!
# Spike (#792): a handler stack, by induction on the stack

`cerwpT_handleStack`: a computation at `cerwpT` at a table `T`, under a stack of handlers each
meeting `HandleOKT` between the table below it and its own outer table, is `cerwpT` at the top
table. One induction on the stack, each step `cerwpT_handle`; nothing per level.

Instances at depth 1 and 3 (`depth1`, `depth3`): handlers of names 7, 8, 9 that forward a
must-resume operation `nB` (no cancel branch) and return their argument.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.HandleSpike
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.Tree.Wp.SchedProgs (cerwpPostT_down compS_empty_left_eq cerwpT_det)
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload hndE hndVal capTag
  clauseAt ccatchE)

/-- A handler in a stack, with the table, answer and base frame condition it runs at. -/
structure HFrame where
  n₀ : UInt32
  qs : Val
  hr : Val
  hs : Val
  To : OpTabT
  Qout : TPostV
  Fbo : TFrame

/-- The stack meets `HandleOKT` at every level, from `T`, `Q` at the bottom. -/
def StackOK : OpTabT → TPostV → List HFrame → Prop
  | _, _, [] => True
  | T, Q, h :: hs => HandleOKT (ℍ := ℍ) T h.To h.n₀ h.qs h.hr h.hs Q h.Qout h.Fbo ∧ h.Fbo.Mono ∧
      (∀ w ρf, ResUT.Valid ρf → h.Fbo w ρf) ∧ StackOK h.To h.Qout hs

def topT : OpTabT → List HFrame → OpTabT
  | T, [] => T
  | _, h :: hs => topT h.To hs

def topQ : TPostV → List HFrame → TPostV
  | Q, [] => Q
  | _, h :: hs => topQ h.Qout hs

def topFb : TFrame → List HFrame → TFrame
  | Fb, [] => Fb
  | _, h :: hs => topFb h.Fbo hs

/-- The stack around `e`, innermost first. -/
def wrap : List HFrame → Expr → Expr
  | [], e => e
  | h :: hs, e => wrap hs (hndE (hndVal h.n₀ h.qs h.hr h.hs) e)

/-- **`[handle]` for a handler stack**, by induction on the stack. -/
theorem cerwpT_handleStack : ∀ (Hs : List HFrame) (T : OpTabT) (Q : TPostV) (Fb : TFrame),
    StackOK (ℍ := ℍ) T Q Hs → (∀ w ρf, ResUT.Valid ρf → Fb w ρf) →
    ∀ (n : Nat) (M : BoCa.Loc → Prop) (w : TWd) (ls : List (SRecT w.K))
      (O : List (FrameRecT w.K)) (e : Expr) (ρ : TRes w.K), (∀ x, recMask O x → M x) →
      cerwpT (ℍ := ℍ) (opTableT T) Q Fb (fdMask M) n w ls O e ρ →
      cerwpT (ℍ := ℍ) (opTableT (topT T Hs)) (topQ Q Hs) (topFb Fb Hs) (fdMask M) n w ls O
        (wrap Hs e) ρ
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, h => h
  | hd :: Hs, T, Q, Fb, ⟨hOK, hFm, hFv, hrest⟩, hFb, n, M, w, ls, O, e, ρ, hOM, h =>
      cerwpT_handleStack Hs hd.To hd.Qout hd.Fbo hrest hFv n M w ls O _ ρ hOM
        (cerwpT_handle hOK hFm n M (fdMask M) Fb (fdMask M) w ls O e ρ (fdMask_mono M)
          (fun _ _ h => h) hOM hFb (fun _ _ h => h) h)

/-! ### Instances at depth 1 and 3 -/

namespace Inst
open BoCa.Fig16.Tree.Wp.HandleSpike.Counter (nB T_some)

/-- The forwarded operation: must-resume, so no cancel branch. -/
def enL : OpEntT where
  q := .lin
  abort := false
  PA := fun _ _ _ v ρ => v = Val.unit ∧ ρ = PMap.empty
  PBv := fun _ _ _ _ a σ => a = Val.unit ∧ σ = PMap.empty
  fin := false
  fd := fdJoinT
  oc := fun _ O => O = []

def TL : OpTabT := fun m i => if m = nB ∧ i = 0 then some enL else none

theorem TL_some {m i : UInt32} {en : OpEntT} (h : TL m i = some en) :
    m = nB ∧ i = 0 ∧ en = enL := by
  unfold TL at h
  split at h
  · rename_i hm; cases h; exact ⟨hm.1, hm.2, rfl⟩
  · cases h

def QU : TPostV := fun _ _ _ O r ρ => r = Val.unit ∧ O = [] ∧ ρ = PMap.empty

theorem QU_down : QU.Down := fun _ _ _ _ _ _ h => h

theorem TL_PA_down : ∀ m i en, TL m i = some en → ∀ k w ls v ρ, en.PA (k + 1) w ls v ρ →
    en.PA k w ls v ρ := fun _ _ en h _ _ _ _ _ hA => by obtain ⟨-, -, rfl⟩ := TL_some h; exact hA

/-- `λx. x`. -/
def idV : Val := Val.lam (.var 0)

/-- A handler of name `nm`, forwarding `nB`, returning its argument. -/
def hF (nm : UInt32) : HFrame :=
  ⟨nm, Val.pair Val.unit Val.unit, idV, Val.pair Val.unit Val.unit, TL, QU,
    fun _ ρf => ResUT.Valid ρf⟩

theorem idRet_ok : RetT (ℍ := ℍ) TL QU QU (fun _ ρf => ResUT.Valid ρf) idV := by
  intro F k w ls O v ρ _ _ _ _ _ ⟨hv, hO, hρ⟩
  subst hv; subst hO; subst hρ
  refine cerwpT_det (cerwpPostT_down QU_down TL_PA_down)
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  exact cerwpT_val (v := Val.unit) fun w₀ ρ₀ _ O₀ _ hr _ hO => by
    cases hO; exact ⟨rfl, rfl, RR.of_empty hr⟩

theorem hF_ok (nm : UInt32) (hnm : nm ≠ nB) :
    HandleOKT (ℍ := ℍ) TL TL nm (hF nm).qs (hF nm).hr (hF nm).hs QU QU
      (fun _ ρf => ResUT.Valid ρf) := by
  refine ⟨fun m i en _ h => ⟨h, ?_⟩, fun i en h => ?_, fun m i en h v w O ρf => ?_, QU_down,
    TL_PA_down, idRet_ok, fun i en h => ?_⟩
  · obtain ⟨-, -, rfl⟩ := TL_some h; exact Or.inl rfl
  · obtain ⟨h, -⟩ := TL_some h; exact absurd h hnm
  · obtain ⟨-, -, rfl⟩ := TL_some h; exact Iff.rfl
  · obtain ⟨h, -⟩ := TL_some h; exact absurd h hnm

theorem valid_mono : TFrame.Mono (fun _ ρf => ResUT.Valid ρf) :=
  fun _ _ _ _ _ hr hv => WitRel.ResUT.Valid.sim (W := rrRel _ _ _) hv hr.rsim

def eL : Expr := performE (.val (opPayload nB 0 Val.unit))

/-- The bottom computation: performs `nB` and answers `()`. -/
theorem eL_ok (n : Nat) (Fb F : TFrame) (w : TWd) (ls : List (SRecT w.K)) :
    cerwpT (ℍ := ℍ) (opTableT TL) QU Fb F n w ls [] eL PMap.empty := by
  show cerwpT (ℍ := ℍ) (opTableT TL) QU Fb F n w ls [] (Kont.hole.plug eL) PMap.empty
  refine cerwpT_perform .hole rfl (show TL nB 0 = some enL by simp [TL]) rfl ?_
  intro w₀ ρ₀ ls₀ O₀ _ hr _ hO
  cases hO
  obtain rfl := RR.of_empty hr
  refine ⟨rfl, PMap.empty, PMap.empty, ResUT.compS_empty_right _, ⟨rfl, rfl⟩, ?_⟩
  unfold contShareT
  refine ⟨fun h => absurd h (by simp [enL]), ?_⟩
  intro w' ρ' ls' O' _ hr' _ hO'
  refine ⟨fun k' hk' a σ σ' hB hcσ => ?_, fun hq _ _ _ => absurd rfl hq⟩
  obtain ⟨rfl, rfl⟩ := hB
  obtain rfl := RR.of_empty hr'
  obtain rfl := compS_empty_left_eq hcσ
  cases hO'
  simp only [cerwpTC, hk', if_true]
  exact cerwpT_val (v := Val.unit) fun w₀ ρ₀ _ O₀ _ hr _ hO => by
    cases hO; exact ⟨rfl, rfl, RR.of_empty hr⟩

theorem stack_ok : ∀ (ns : List UInt32), (∀ nm ∈ ns, nm ≠ nB) →
    StackOK (ℍ := ℍ) TL QU (ns.map hF)
  | [], _ => trivial
  | nm :: ns, h => ⟨hF_ok nm (h nm (by simp)), valid_mono, fun _ _ hv => hv,
      stack_ok ns fun x hx => h x (by simp [hx])⟩

theorem top_eq : ∀ (ns : List UInt32), topT TL (ns.map hF) = TL ∧ topQ QU (ns.map hF) = QU
  | [] => ⟨rfl, rfl⟩
  | _ :: ns => top_eq ns

/-- **Depth 1.** -/
theorem depth1 (n : Nat) (w : TWd) (ls : List (SRecT w.K)) :
    cerwpT (ℍ := ℍ) (opTableT TL) QU (topFb (fun _ ρf => ResUT.Valid ρf) ([7].map hF))
      (fdMask fun _ => False) n w ls [] (wrap ([7].map hF) eL) PMap.empty :=
  cerwpT_handleStack _ TL QU _ (stack_ok [7] (by intro x hx; simp only [List.mem_singleton] at hx; subst hx; decide)) (fun _ _ hv => hv) n _ w ls [] eL
    PMap.empty (fun x hx => by simp [recMask] at hx) (eL_ok n _ _ w ls)

/-- **Depth 3**: `hnd₉ (hnd₈ (hnd₇ (perform nB)))`. -/
theorem depth3 (n : Nat) (w : TWd) (ls : List (SRecT w.K)) :
    cerwpT (ℍ := ℍ) (opTableT TL) QU (topFb (fun _ ρf => ResUT.Valid ρf) ([7, 8, 9].map hF))
      (fdMask fun _ => False) n w ls [] (wrap ([7, 8, 9].map hF) eL) PMap.empty :=
  cerwpT_handleStack _ TL QU _ (stack_ok [7, 8, 9] (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> decide)) (fun _ _ hv => hv) n _ w ls []
    eL PMap.empty (fun x hx => by simp [recMask] at hx) (eL_ok n _ _ w ls)

end Inst

end BoCa.Fig16.Tree.Wp.HandleSpike

end
