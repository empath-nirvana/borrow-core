import Optics.Laws

/-!
# Optics — a program through a composite lens  (stage 1)

    let (c, u) = (withbor ∘ lift fst) (alloc (alloc (inj₁ ()), alloc (inj₁ ()))) (Λ. λm.
                   let (m′, u) = withswap m setG; u; forget m′; ());
    u; let (a, b) = free c; drop (free a); drop (free b)

The composite lens borrows the cell `c : Ref (Ref B ⊗ Ref B)` at `'x₁` (`idLens`), and through
that `Mut 'x₁ (Ref B ⊗ Ref B)` lends the first leaf at `'y ⊏ 'x₁` (`fstLens` lifted by
`withswap`), keeping the second leaf as the residual.  The callback writes `inj₂ ()` into the
first leaf.  The typing is `Optic.comp`'s, with no derivation written for the program's
borrowing; `adequacyC` runs it to `()` with no cell left, and the interpreter shows the first
leaf changed and the second not.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Optics
open BoCa
open BoCa.Fig16
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.BoLo (Heap Steps Kont)
open BoCa.Programs (app2 alloc' free' unitNoLeak)

/-- `Ref B ⊗ Ref B`, `B = 1 ⊕ 1`. -/
abbrev PB : VTy := refs2 BB BB

theorem PB_plain : plainV PB = true := rfl

/-- The composite: `Ref (Ref B ⊗ Ref B) → Mut 'y B`, the first leaf. -/
def cellFst : Lens (fun _ => .ref PB) (fun c => .mut c BB) :=
  Optic.comp (idLens PB PB_plain) (fstLens BB BB rfl).lift
    (mut_focusFree rfl) (mut_focusInst rfl) (fun _ => True) id rfl (fun _ h _ => h)

/-- `Λ. λm. let (m′, u) = withswap m setG; u; forget m′; ()`. -/
def setBorrower : Expr :=
  .val (.lam (.val (.lam (.letpair (app2 withswap (.var 0) setG)
    (.seq (.var 0) (.seq (.app forget (.var 1)) unit'))))))

theorem d_setBorrower :
    CDerives LifeCtx.empty [] setBorrower (.val (cbTy (fun c => .mut c BB) 0 LifeCtx.empty.meetOfDom .unit)) :=
  callbackW ok_empty rfl .nil <|
    letW (A := .mut (.var 0) BB) (B := .unit)
      (appW (d_setG (by cdead)) (appW (.var (by csolo)) (.withswap (by cdead)))) <|
    seqW (.var (by csolo)) <|
    seqW (appW (.var (by csolo)) (.forgetMut (by cdead)))
      (.boxI (.unitI (by cdead)) ⟨Lifetime.LifeCtx.defines_of_wf rfl, dead_noLive (by cdead)⟩)

def mkPB : Expr := .pair (.app alloc' (.inj₁ unit')) (.app alloc' (.inj₁ unit'))

/-- The composite's term, `withbor ∘ lift fst`. -/
def cellFstV : Val := compV withborV (liftV fstV)

theorem cellFst_run : (cellFst (ℍ := ℍ)).run = cellFstV := rfl

def fieldProg : Expr :=
  .letpair (app2 (.val cellFstV) (.app alloc' mkPB) setBorrower)
    (.seq (.var 0) (.letpair (.app free' (.var 1))
      (.seq (dropB (.app free' (.var 1))) (dropB (.app free' (.var 0))))))

/-- The same run, returning both leaves' contents. -/
def fieldObs : Expr :=
  .letpair (app2 (.val cellFstV) (.app alloc' mkPB) setBorrower)
    (.seq (.var 0) (.letpair (.app free' (.var 1))
      (.pair (.app free' (.var 1)) (.app free' (.var 0)))))

theorem cellFst_adm : cellFst.Adm LifeCtx.empty .top 0 :=
  ⟨1, 2, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- The typing, read off `cellFst.wf` at any host (the derivation does not depend on it). -/
theorem d_fieldProg (ℍ : BoCa.Host) [BoCa.HostIs ℍ] :
    CDerives LifeCtx.empty [] fieldProg (.val .unit) := by
  refine letW (A := .ref PB) (B := .unit)
    (appW d_setBorrower
      (appW (appW (pairW (appW (.sumI₁ (.unitI (by cdead))) (.alloc (by cdead)))
          (appW (.sumI₁ (.unitI (by cdead))) (.alloc (by cdead))))
          (.alloc (by cdead)))
        (cellFst_run (ℍ := ℍ) ▸ cellFst.wf (T := .unit) cellFst_adm rfl (by cdead)))) ?_
  refine seqW (.var (by csolo)) ?_
  refine letW (A := .ref BB) (B := .ref BB) (appW (.var (by csolo)) (.free (by cdead))) ?_
  exact seqW (d_dropB (appW (.var (by csolo)) (.free (by cdead))) (by cdead))
    (d_dropB (appW (.var (by csolo)) (.free (by cdead))) (by cdead))

theorem fieldProg_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem fieldProg Adequacy.emptyMem (.val .unit) :=
  adequacyC (.ret (d_fieldProg ℍ))

theorem fieldProg_eval : unitNoLeak (eval fieldProg) = true := by decide

/-- The first leaf holds `inj₂ ()`, the second still `inj₁ ()`. -/
theorem fieldObs_eval :
    (match eval fieldObs with
      | .value ⟨.pair (.inj₂ .unit) (.inj₁ .unit), _⟩ false => true
      | _ => false) = true := by decide

end BoCa.Fig16.LogRel.Core.Optics

end
