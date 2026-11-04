import HandleSpike.Param
import HandleSpike.Counter
import HandleSpike.Stack

/-!
# Spike (#792): programs at the canceller-parametric share

* `param_counter`: `Counter.lean`'s program, `hnd H (perform (nB, 0, ()))` with `nB` cancellable and
  forwarded, at every index.
* `cerwpP_handleStack`: a handler stack, one induction on the stack, each step `cerwpP_handle`;
  `depth1`, `depth3`: handlers 7, 8, 9 forwarding the cancellable `nB`.
* `cancel_as_resume`: a scheduler `HC` whose clause cancels the stored task under itself,
  `hnd h (κ (inj₂ ()))`; the task's finaliser parks again at `HC`'s operation, comes back to `HC`'s
  clause as an ordinary stored continuation, is cancelled again, and the program answers `()`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.HandleSpike.Param
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.Tree.Wp.HandleSpike
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.Tree.Wp.SchedProgs (compS_empty_left_eq)
open BoCa.BoLo (Heap Step1 Head Kont performE raiseE cancelVal opPayload hndE hndVal capTag
  clauseAt ccatchE)

theorem PADown.empty : PADown OpTabP.empty := fun _ _ _ h => by simp [OpTabP.empty] at h

/-- A forwarded stop's cancel needs nothing of its canceller here: `ccatch (raise cancel)`. -/
theorem cerwpP_cancelHole {T' : OpTabP} (hT' : PADown T') {Fb F : TFrame} {n : Nat} {w : TWd}
    {ls : List (SRecT w.K)} :
    cerwpP (ℍ := ℍ) T' Qunit Fb F n w ls [] (cancelE .hole) PMap.empty :=
  cerwpP_det Qunit_down hT' (fun μ => step1Only_plug (Head.cancel μ .hole rfl) rfl .hole)
    cerwpP_unit

/-! ### The counterexample's program -/

namespace PCounter
open BoCa.Fig16.Tree.Wp.HandleSpike.Counter (nB nH enF retOne qsH hsH H e Qout Qout_down)
open BoCa.Fig16.Tree.Wp.HandleSpike.Inst (valid_mono)

/-- `enF`, its finaliser performing nothing. -/
def enFP : OpEntP := ⟨enF, fun _ _ => False⟩

def TP : OpTabP := fun m i => if m = nB ∧ i = 0 then some enFP else none

theorem TP_some {m i : UInt32} {en : OpEntP} (h : TP m i = some en) :
    m = nB ∧ i = 0 ∧ en = enFP := by
  unfold TP at h
  split at h
  · rename_i hm; cases h; exact ⟨hm.1, hm.2, rfl⟩
  · cases h

theorem TP_PA : PADown TP := fun _ _ _ h _ _ _ _ _ hA => by
  obtain ⟨-, -, rfl⟩ := TP_some h; exact hA

/-- `perform (nB, 0, ())` at `TP`, answering `()`, at every index, base and frame condition. -/
theorem perform_ok (n : Nat) (Fb F : TFrame) (w : TWd) (ls : List (SRecT w.K)) :
    cerwpP (ℍ := ℍ) TP Qunit Fb F n w ls [] e PMap.empty := by
  show cerwpP (ℍ := ℍ) TP Qunit Fb F n w ls [] (Kont.hole.plug e) PMap.empty
  refine cerwpP_perform .hole rfl (show TP nB 0 = some enFP by simp [TP]) rfl ?_
  intro w₀ ρ₀ ls₀ O₀ _ hr _ hO
  cases hO
  obtain rfl := RR.of_empty hr
  refine ⟨rfl, PMap.empty, PMap.empty, ResUT.compS_empty_right _, ⟨rfl, rfl⟩,
    fun h => absurd h (by simp [enFP, enF]), ?_⟩
  intro w' ρ' ls' O' _ hr' _ hO'
  obtain rfl := RR.of_empty hr'
  cases hO'
  refine ⟨fun k' hk' a σ σ' hB hcσ => ?_, fun _ _ k' hk' T' Fb' hT' _ => ?_⟩
  · obtain ⟨rfl, rfl⟩ := hB
    obtain rfl := compS_empty_left_eq hcσ
    simp only [cerwpPC, hk', if_true]
    exact cerwpP_unit
  · simp only [cerwpPK, hk', if_true]
    exact cerwpP_cancelHole hT'.2

theorem retOne_ok (Fbo : TFrame) : RetP (ℍ := ℍ) TP Qunit Qout Fbo retOne := by
  intro F k w ls O v ρ _ _ _ _ _ ⟨_, hO, hρ⟩
  subst hO; subst hρ
  refine cerwpP_det Qout_down TP_PA (fun μ => step1Only_plug (Head.beta μ _ v) rfl .hole) ?_
  exact cerwpP_val (v := Val.i32 1) fun w₀ ρ₀ _ O₀ _ hr _ hO => by
    cases hO; exact ⟨rfl, rfl, RR.of_empty hr⟩

theorem handler_okP (Fbo : TFrame) :
    HandleOKP (ℍ := ℍ) TP TP nH qsH retOne hsH Qunit Qout Fbo := by
  refine ⟨fun m i en _ h => ⟨h, fun _ _ _ _ h' => h'⟩, fun i en h => ?_,
    fun m i en h v w O ρf => ?_, Qout_down, TP_PA, TP_PA, retOne_ok Fbo, retOne_ok Fbo, fun i en h => ?_⟩
  · obtain ⟨h, -⟩ := TP_some h; cases h
  · obtain ⟨-, -, rfl⟩ := TP_some h; exact Iff.rfl
  · obtain ⟨h, -⟩ := TP_some h; cases h

/-- **`forward_cancel_fails`'s program passes at the parametric share**, at every index. -/
theorem param_counter (n : Nat) (w : TWd) (ls : List (SRecT w.K)) :
    cerwpP (ℍ := ℍ) TP Qout (fun _ ρf => ResUT.Valid ρf) (fdMask fun _ => False) n w ls []
      (hndE H e) PMap.empty :=
  cerwpP_handle (handler_okP _) valid_mono n Qunit (retOne_ok _) _ (fdMask fun _ => False)
    (fun _ ρf => ResUT.Valid ρf) (fdMask fun _ => False) w ls [] e PMap.empty (fdMask_mono _)
    (fun _ _ h => h) (fun x hx => by simp [recMask] at hx) (fun _ _ hv => hv) (fun _ _ h => h)
    (perform_ok n _ _ w ls)

end PCounter

/-! ### Handler stacks -/

structure HFrameP where
  n₀ : UInt32
  qs : Val
  hr : Val
  hs : Val
  To : OpTabP
  Qout : TPostV
  Fbo : TFrame

def StackOKP : OpTabP → TPostV → List HFrameP → Prop
  | _, _, [] => True
  | T, Q, h :: hs => HandleOKP (ℍ := ℍ) T h.To h.n₀ h.qs h.hr h.hs Q h.Qout h.Fbo ∧ h.Fbo.Mono ∧
      (∀ w ρf, ResUT.Valid ρf → h.Fbo w ρf) ∧ StackOKP h.To h.Qout hs

def topTP : OpTabP → List HFrameP → OpTabP
  | T, [] => T
  | _, h :: hs => topTP h.To hs

def topQP : TPostV → List HFrameP → TPostV
  | Q, [] => Q
  | _, h :: hs => topQP h.Qout hs

def topFbP : TFrame → List HFrameP → TFrame
  | Fb, [] => Fb
  | _, h :: hs => topFbP h.Fbo hs

def wrapP : List HFrameP → Expr → Expr
  | [], e => e
  | h :: hs, e => wrapP hs (hndE (hndVal h.n₀ h.qs h.hr h.hs) e)

/-- **`[handle]` for a handler stack at the parametric share**, by induction on the stack. -/
theorem cerwpP_handleStack : ∀ (Hs : List HFrameP) (T : OpTabP) (Q : TPostV) (Fb : TFrame),
    StackOKP (ℍ := ℍ) T Q Hs → (∀ w ρf, ResUT.Valid ρf → Fb w ρf) →
    ∀ (n : Nat) (M : BoCa.Loc → Prop) (w : TWd) (ls : List (SRecT w.K))
      (O : List (FrameRecT w.K)) (e : Expr) (ρ : TRes w.K), (∀ x, recMask O x → M x) →
      cerwpP (ℍ := ℍ) T Q Fb (fdMask M) n w ls O e ρ →
      cerwpP (ℍ := ℍ) (topTP T Hs) (topQP Q Hs) (topFbP Fb Hs) (fdMask M) n w ls O
        (wrapP Hs e) ρ
  | [], _, _, _, _, _, _, _, _, _, _, _, _, _, h => h
  | hd :: Hs, _, Q, Fb, ⟨hOK, hFm, hFv, hrest⟩, hFb, n, M, w, ls, O, e, ρ, hOM, h =>
      cerwpP_handleStack Hs hd.To hd.Qout hd.Fbo hrest hFv n M w ls O _ ρ hOM
        (cerwpP_handle hOK hFm n Q hOK.2.2.2.2.2.2.1 M (fdMask M) Fb (fdMask M) w ls O e ρ
          (fdMask_mono M) (fun _ _ h => h) hOM hFb (fun _ _ h => h) h)

namespace PInst
open BoCa.Fig16.Tree.Wp.HandleSpike.Counter (nB e)
open BoCa.Fig16.Tree.Wp.HandleSpike.Inst (valid_mono)
open PCounter (TP TP_some TP_PA perform_ok)

/-- A handler of name `nm`, forwarding the cancellable `nB`, returning its argument. -/
def hF (nm : UInt32) : HFrameP :=
  ⟨nm, Val.pair Val.unit Val.unit, Inst.idV, Val.pair Val.unit Val.unit, TP, Qunit,
    fun _ ρf => ResUT.Valid ρf⟩

theorem idRet_ok : RetP (ℍ := ℍ) TP Qunit Qunit (fun _ ρf => ResUT.Valid ρf) Inst.idV := by
  intro F k w ls O v ρ _ _ _ _ _ ⟨hv, hO, hρ⟩
  subst hv; subst hO; subst hρ
  exact cerwpP_det Qunit_down TP_PA (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole)
    cerwpP_unit

theorem hF_ok (nm : UInt32) (hnm : nm ≠ nB) :
    HandleOKP (ℍ := ℍ) TP TP nm (hF nm).qs (hF nm).hr (hF nm).hs Qunit Qunit
      (fun _ ρf => ResUT.Valid ρf) := by
  refine ⟨fun m i en _ h => ⟨h, fun _ _ _ _ h' => h'⟩, fun i en h => ?_,
    fun m i en h v w O ρf => ?_, Qunit_down, TP_PA, TP_PA, idRet_ok, idRet_ok, fun i en h => ?_⟩
  · obtain ⟨h, -⟩ := TP_some h; exact absurd h hnm
  · obtain ⟨-, -, rfl⟩ := TP_some h; exact Iff.rfl
  · obtain ⟨h, -⟩ := TP_some h; exact absurd h hnm

theorem stack_ok : ∀ (ns : List UInt32), (∀ nm ∈ ns, nm ≠ nB) →
    StackOKP (ℍ := ℍ) TP Qunit (ns.map hF)
  | [], _ => trivial
  | nm :: ns, h => ⟨hF_ok nm (h nm (by simp)), valid_mono, fun _ _ hv => hv,
      stack_ok ns fun x hx => h x (by simp [hx])⟩

/-- **Depth 1**, the cancellable `nB` forwarded. -/
theorem depth1 (n : Nat) (w : TWd) (ls : List (SRecT w.K)) :
    cerwpP (ℍ := ℍ) TP Qunit (topFbP (fun _ ρf => ResUT.Valid ρf) ([7].map hF))
      (fdMask fun _ => False) n w ls [] (wrapP ([7].map hF) e) PMap.empty :=
  cerwpP_handleStack _ TP Qunit _ (stack_ok [7] (by
    intro x hx; simp only [List.mem_singleton] at hx; subst hx; decide)) (fun _ _ hv => hv) n _
    w ls [] e PMap.empty (fun x hx => by simp [recMask] at hx) (perform_ok n _ _ w ls)

/-- **Depth 3**: `hnd₉ (hnd₈ (hnd₇ (perform nB)))`, the cancellable `nB` forwarded three times. -/
theorem depth3 (n : Nat) (w : TWd) (ls : List (SRecT w.K)) :
    cerwpP (ℍ := ℍ) TP Qunit (topFbP (fun _ ρf => ResUT.Valid ρf) ([7, 8, 9].map hF))
      (fdMask fun _ => False) n w ls [] (wrapP ([7, 8, 9].map hF) e) PMap.empty :=
  cerwpP_handleStack _ TP Qunit _ (stack_ok [7, 8, 9] (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> decide)) (fun _ _ hv => hv) n _ w ls []
    e PMap.empty (fun x hx => by simp [recMask] at hx) (perform_ok n _ _ w ls)

end PInst

end BoCa.Fig16.Tree.Wp.HandleSpike.Param

end
