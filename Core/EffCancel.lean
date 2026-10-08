import Core.Steps

/-!
# Core — cancels: finaliser errors under a cancel  `[spec §19]`

Two regressions for §19's cancel.  Each is a closed program whose handler `1` cancels its `κ`,
with `K = hnd (2, H₂) (ubind (id, D) [·])` inside the cancelled region, so `H₂` is dying.

* `prog`: the finaliser raises name `2`.  No handler outside the region handles `2`, so the error
  is suppressed; `H₂` does not catch it, and the cancel answers `()` (`prog_run`).
* `prog₃`: the finaliser raises name `3`, which `H₃` handles outside the region.  The error is
  kept, re-raised at the canceller, and `H₃` catches it (`prog₃_run`).

The handlers' operations are unrestricted (`qualsVal [.unr]`), so `κ` owns no cell (§25) and the
runs allocate nothing.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.CancelIntercept
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont hndE hndVal raiseE performE ccatchE cfinE opPayload
  clauseAt kappa cancelVal errNext)

/-- The identity. -/
def idV : Val := Val.lam (.var 0)

/-- Handler `1`'s clause: `λp. let (x, k) = p; k (inj₂ ())`, the cancel entry of `κ`. -/
def c₁ : Val := Val.lam (.letpair (.var 0) (.app (.var 0) (.val (Val.inj₂ Val.unit))))

def H₁ : Val := hndVal 1 (qualsVal [.unr]) idV (Val.pair c₁ Val.unit)

/-- Handler `2`'s clause answers `()`. -/
def c₂ : Val := Val.lam (.val Val.unit)

def H₂ : Val := hndVal 2 (qualsVal [.unr]) idV (Val.pair c₂ Val.unit)

/-- Handler `3`'s clause answers `inj₂ ()`. -/
def c₃ : Val := Val.lam (.val (Val.inj₂ Val.unit))

def H₃ : Val := hndVal 3 (qualsVal [.unr]) idV (Val.pair c₃ Val.unit)

/-- A finaliser that raises name `m`. -/
def D (m : UInt32) : Val := Val.lam (raiseE (.val (opPayload m 0 Val.unit)))

/-- `K = hnd (2, H₂) (ubind (id, D m) [·])`. -/
def K (m : UInt32) : Kont :=
  .appR (.app (.val (.prim .hnd)) (.val H₂))
    (.appR (.app (.val (.prim .ubind)) (.val (Val.pair idV (D m)))) .hole)

/-- `hnd (1, H₁) K[perform (1, (0, ()))]`. -/
def body (m : UInt32) : Expr := hndE H₁ ((K m).plug (performE (.val (opPayload 1 0 Val.unit))))

/-- The finaliser raises `2`, a name handled only inside the region. -/
def prog : Expr := body 2

/-- The finaliser raises `3`, a name handled outside the region by `H₃`. -/
def prog₃ : Expr := hndE H₃ (body 3)

theorem st (K' : Kont) {μ : Heap} {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ a') :
    Step1 (ℍ := ℍ) μ (K'.plug a) μ (K'.plug a') :=
  ⟨K', a, a', rfl, rfl, h⟩

theorem hc₁ : clauseAt (Val.pair c₁ Val.unit).1 (0 : UInt32).toNat = some c₁ := by
  simp [clauseAt, Val.pair, c₁, Val.lam, IsVal.lam]

theorem hc₂ : clauseAt (Val.pair c₂ Val.unit).1 (0 : UInt32).toNat = some c₂ := by
  simp [clauseAt, Val.pair, c₂, Val.lam, IsVal.lam]

theorem hc₃ : clauseAt (Val.pair c₃ Val.unit).1 (0 : UInt32).toNat = some c₃ := by
  simp [clauseAt, Val.pair, c₃, Val.lam, IsVal.lam]

/-- The cancel: `body m ⟶* ccatch (…)[raise s]` with `s` the cancel state after the finaliser. -/
theorem body_run (m : UInt32) (μ : Heap) :
    Steps (ℍ := ℍ) μ (body m) μ
      (ccatchE ((Kont.appR (.app (.val (.prim .hnd)) (.val H₁))
        (.appR (.app (.val (.prim .hnd)) (.val H₂)) .hole)).plug
          (raiseE (.val (cancelVal [1, 2] (errNext [1, 2] none m 0 Val.unit)))))) := by
  let κv : Val := ⟨kappa 1 H₁ (K m), by unfold kappa; exact .lam⟩
  refine .more (st .hole (Head.hop μ 1 0 (qualsVal [.unr]) idV (Val.pair c₁ Val.unit) c₁ Val.unit (K m) hc₁ rfl)) ?_
  refine .more (st .hole (Head.beta μ _ (Val.pair Val.unit κv))) ?_
  refine .more (st .hole (Head.letpair μ Val.unit κv _)) ?_
  refine .more (st .hole (Head.beta μ _ (Val.inj₂ Val.unit))) ?_
  refine .more (st .hole (Head.case₂ μ Val.unit _ _)) ?_
  refine .more (st .hole (Head.seq μ _)) ?_
  show Steps μ (ccatchE (hndE H₁ ((K m).plug (raiseE (.val (cancelVal [1, 2] none)))))) μ _
  refine .more (st ((.appR (.val (.prim .ccatch)) (.appR (.app (.val (.prim .hnd)) (.val H₁))
    (.appR (.app (.val (.prim .hnd)) (.val H₂)) .hole))))
    (Head.ufinC μ idV (D m) [1, 2] none .hole rfl)) ?_
  refine .more (st ((.appR (.val (.prim .ccatch)) (.appR (.app (.val (.prim .hnd)) (.val H₁))
    (.appR (.app (.val (.prim .hnd)) (.val H₂))
      (.appR (.app (.val (.prim .cfin)) (.val (cancelVal [1, 2] none))) .hole)))))
    (Head.beta μ _ Val.unit)) ?_
  show Steps μ ((Kont.appR (.val (.prim .ccatch)) (.appR (.app (.val (.prim .hnd)) (.val H₁))
    (.appR (.app (.val (.prim .hnd)) (.val H₂)) .hole))).plug
      (cfinE (cancelVal [1, 2] none) (Kont.hole.plug (raiseE (.val (opPayload m 0 Val.unit)))))) μ _
  refine .more (st _ (Head.cferr μ [1, 2] none m 0 Val.unit .hole rfl)) ?_
  exact .refl _ _

/-- **`prog`**: the error of name `2` is suppressed; `H₂` does not catch it, and the cancel
answers `()`. -/
theorem prog_run (μ : Heap) : Steps (ℍ := ℍ) μ prog μ (.val Val.unit) := by
  have h := body_run (ℍ := ℍ) 2 μ
  have hn : errNext [1, 2] none 2 0 Val.unit = none := by simp [errNext]
  rw [hn] at h
  refine BoCa.BoLo.Steps.trans h ?_
  refine .more (st .hole (Head.cancel μ [1, 2] _ rfl)) ?_
  exact .refl _ _

/-- **`prog₃`**: the error of name `3` is kept, re-raised at the canceller, and caught by `H₃`,
outside the region. -/
theorem prog₃_run (μ : Heap) : Steps (ℍ := ℍ) μ prog₃ μ (.val (Val.inj₂ Val.unit)) := by
  have h := BoCa.BoLo.Steps.plug (.appR (.app (.val (.prim .hnd)) (.val H₃)) .hole)
    (body_run (ℍ := ℍ) 3 μ)
  have hn : errNext [1, 2] none 3 0 Val.unit = some (opPayload 3 0 Val.unit) := by
    simp [errNext]
  rw [hn] at h
  refine BoCa.BoLo.Steps.trans h ?_
  refine .more (st (.appR (.app (.val (.prim .hnd)) (.val H₃)) .hole)
    (Head.creraise μ [1, 2] (opPayload 3 0 Val.unit) _ rfl)) ?_
  show Steps μ (hndE H₃ (Kont.hole.plug (raiseE (.val (opPayload 3 0 Val.unit))))) μ _
  refine .more (st .hole (Head.hunwind μ 3 0 (qualsVal [.unr]) idV (Val.pair c₃ Val.unit) c₃ Val.unit .hole hc₃ rfl)) ?_
  refine .more (st .hole (Head.beta μ _ Val.unit)) ?_
  exact .refl _ _

end BoCa.Fig16.LogRel.Core.CancelIntercept
