import PoolSpike.Adequacy

/-!
# Pool spike: the theorem's premises at a concrete pool, and `contShareP` against `contShareT`

* **A pool of two branches** (`nonvac`): `progA = (perform (m₀, (i₀, ())); ())` and `progB = ()`,
  verified at `cerwpT (opTableP awT)` at every world and list; the table and the postcondition
  meet `TabOK`/`QOK`. A run of the machine starts `progA`, parks it, runs `progB` to its end while
  `progA` is parked, resumes `progA` and runs it to the empty final configuration. Neither
  branch holds a lend: no program rule at `twp` opens or ends one, so a parked branch holding a
  view cannot be verified here without first building those rules.
* **`contShareP` is the stronger promise** (`contShareP_contShareT`): every share `contShareP`
  gives is a share `contShareT` gives. So every stop `opTableP` admits, `opTableT` admits.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.Pool
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Head Kont performE opPayload)

/-- **`contShareP` is the stronger promise.** -/
theorem contShareP_contShareT {en : OpEntT} {F : TFrame} {k : Nat} {w : TWd}
    {ls : List (SRecT w.K)} {O : List (FrameRecT w.K)} {K : Kont} {v : Val} {Ψ : ContT}
    {ρ : TRes w.K} (h : contShareP en F k w ls O K v Ψ ρ) : contShareT en F k w ls O K v Ψ ρ :=
  ⟨h.1, fun w' ρ' lsR ls' O' hE hr hl hx hO => h.2 w' ρ' ls' O' hE hr (keepRel_of_extFT hl hr hx) hO⟩

/-- **With `contShareT`, `extFT` follows from the pool's certificate**: given a re-reading `lsR`
of the stop list at the resume world, `KeepRel` gives `extFT lsR ls ρ'`. What the certificate does
not give is `lsR` itself: `EndT` re-reads the frame's records proper and nothing of the records
of the branch that ran, which that branch may end. -/
theorem extFT_of_keepRel {K K' : WCactus} {Θ' : CodeTy} {lsp : List (SRecT K)}
    {lsR ls : List (SRecT K')} {ρp : TRes K} {ρ : TRes K'} (hl : SRecsRR Θ' lsp lsR)
    (hr : RR (sem Θ') ρp ρ) (hk : KeepRel Θ' lsp ls ρp) : extFT lsR ls ρ := by
  intro r' hr' hrel
  obtain ⟨r, hr₀, hrr⟩ := hl.mem_back hr'
  obtain ⟨r'', hr'', hrr'⟩ := hk r hr₀ ((RelFT.rr_iff hrr hr).mpr hrel)
  rw [RecRR.func hrr hrr']
  exact hr''

/-- **The resume at Core's share, from the pool's certificate and a re-reading of the stop list.**
A share `contShareT` left at a stop, carried to the present world with `KeepRel`, is resumed at the
present list once a re-reading `lsR` of the stop list exists there (`hl`). `hl` is the premise the
pool does not discharge. -/
theorem resume_core {en : OpEntT} {F : TFrame} {k : Nat} {wp w : TWd}
    {lsp : List (SRecT wp.K)} {Op : List (FrameRecT wp.K)} {K : Kont} {v : Val} {Ψ : ContT}
    {ρp : TRes wp.K} {ρ : TRes w.K} {O : List (FrameRecT w.K)} {ls lsR : List (SRecT w.K)}
    (hsh : contShareT en F k wp lsp Op K v Ψ ρp) (hE : wp.Ext w ρp)
    (hr : RRw (w := wp) (w' := w) ρp ρ) (hO : RecsRR w.Θ Op O) (hk : KeepRel w.Θ lsp ls ρp)
    (hl : SRecsRR w.Θ lsp lsR) {k' : Nat} (hk' : k' < k) {a : Val} {σ σ' : TRes w.K}
    (hB : en.PBv v k' w ls a σ) (hc : ResUT.CompS ρ σ σ') :
    Ψ (fdAt en v F O) w O k' ls (K.plug (.val a)) σ' :=
  contShareT_resume hsh hE hr hl (extFT_of_keepRel hl hr hk) hO hk' hB hc

/-- The pool's operation. -/
def awN : UInt32 := 7
def awI : UInt32 := 0

/-- Its entry: strictly linear, an empty payload, the answer `()` at the empty resource. -/
def awEn : OpEntT where
  q := .lin
  abort := false
  PA := fun _ _ _ _ ρ => ρ = PMap.empty
  PBv := fun _ _ _ _ a σ => a = Val.unit ∧ σ = PMap.empty
  fin := none
  fd := fun _ _ _ _ => True
  oc := fun _ _ => True

def awT : OpTabT := fun m i => if m = awN ∧ i = awI then some awEn else none

theorem awT_ok : TabOK awT awN awI := by
  intro m i en h
  unfold awT at h
  split_ifs at h with hm
  obtain ⟨rfl, rfl⟩ := hm
  cases h
  exact ⟨rfl, rfl, fun _ _ _ _ _ h => h, fun _ _ _ _ => ⟨rfl, rfl⟩, fun _ _ _ _ => trivial⟩

/-- Ends hold nothing and own nothing. -/
def emQ : TPostV := fun _ _ _ O _ ρ => ρ = PMap.empty ∧ O = []

theorem emQ_ok : QOK emQ := fun _ _ _ _ _ _ h => h

def awK : Kont := .seq .hole .unit
def progA : Expr := awK.plug (performE (.val (opPayload awN awI Val.unit)))
def progB : Expr := Val.unit.1

theorem cerwp_unit {F : TFrame} {n : Nat} {w : TWd} {ls : List (SRecT w.K)} :
    cerwpT (ℍ := ℍ) (opTableP awT) emQ F n w ls [] Val.unit.1 PMap.empty :=
  cerwpT_val fun _ _ _ _ _ hr _ hO => by cases hO; exact ⟨RR.of_empty hr, rfl⟩

theorem cerwp_after {F : TFrame} {n : Nat} {w : TWd} {ls : List (SRecT w.K)} :
    cerwpT (ℍ := ℍ) (opTableP awT) emQ F n w ls [] (awK.plug (.val Val.unit)) PMap.empty := by
  cases n with
  | zero => exact cerwpT_zero
  | succ n =>
      exact cerwpT_step (opTableP_local _)
        (fun μ => step1Only_plug (Head.seq (ℍ := ℍ) μ Val.unit.1) (by simp [Expr.allocs])
          .hole) cerwp_unit

theorem cerwp_progA {F : TFrame} {n : Nat} {w : TWd} {ls : List (SRecT w.K)} :
    cerwpT (ℍ := ℍ) (opTableP awT) emQ F n w ls [] progA PMap.empty := by
  refine cerwpP_perform (en := awEn) awK rfl (by simp [awT]) rfl fun w₀ ρ₀ ls₀ O₀ _ hr _ hO => ?_
  obtain rfl := RR.of_empty hr
  cases hO
  refine ⟨trivial, PMap.empty, PMap.empty, ResUT.compS_empty_right _, rfl,
    fun _ => rfl, fun w' ρ' ls' O' _ hr' _ hO' => ⟨fun k' hk a σ σ' hB hc => ?_,
      fun h => absurd rfl h⟩⟩
  obtain rfl := RR.of_empty hr'
  cases hO'
  obtain ⟨rfl, rfl⟩ := hB
  obtain rfl : σ' = PMap.empty :=
    ResUT.CompS.functional hc (ResUT.compS_empty_right _)
  simp only [cerwpTC, hk, if_true]
  exact cerwp_after

theorem progs_ok : ∀ e ∈ [progA, progB], ∀ (w : TWd) (ls : List (SRecT w.K)) n,
    cerwpT (ℍ := ℍ) (opTableP awT) emQ (fun _ _ => True) n w ls [] e PMap.empty := by
  intro e he w ls n
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl
  · exact cerwp_progA
  · exact cerwp_unit

/-- **A concrete pool through the theorem.** The premises of `poolAdequacy` hold of
`[progA, progB]`; a run parks `progA`, runs `progB` to its end while `progA` is parked, resumes
`progA`, and ends at the empty final configuration. -/
theorem nonvac :
    PoolAdequacy (ℍ := ℍ) awT emQ awN awI ∧
    PRun (ℍ := ℍ) awN awI 5 (initCfg [progA, progB])
      ⟨Adequacy.emptyMem, some (awK.plug (.val Val.unit)), []⟩ ∧
    PRun (ℍ := ℍ) awN awI 7 (initCfg [progA, progB]) ⟨Adequacy.emptyMem, none, []⟩ := by
  have r₅ : PRun (ℍ := ℍ) awN awI 5 (initCfg [progA, progB])
      ⟨Adequacy.emptyMem, some (awK.plug (.val Val.unit)), []⟩ :=
    .step (.step (.step (.step (.step (.refl _)
      (PStep.start (p₁ := []) (p₂ := [.ready progB])))
      (PStep.park (K := awK) (v := Val.unit) rfl))
      (PStep.start (p₁ := [.parked awK Val.unit]) (p₂ := [])))
      (PStep.done (v := Val.unit)))
      (PStep.resume (p₁ := []) (p₂ := []))
  refine ⟨poolAdequacy awT_ok emQ_ok, r₅, .step (.step r₅ (PStep.run ?_)) (PStep.done (v := Val.unit))⟩
  exact (step1Only_plug (Head.seq (ℍ := ℍ) _ Val.unit.1) (by simp [Expr.allocs]) .hole).1

end BoCa.Fig16.Tree.Wp.Pool

end
