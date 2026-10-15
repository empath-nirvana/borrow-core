import Frontend.Check.Tied

/-!
# Frontend — Check — rules

One builder per `CDerives` constructor (and, in `Frontend/Check/Consts.lean`, per derived
rule). A builder takes the checked premises (`Res`: an erasure with its family of
derivations, `Frontend/Check/Fam.lean`) and the decided side conditions, and returns the
conclusion's `Res`: the erased term of the conclusion together with its derivations, each
built by applying the constructor, tied (decision R, `Frontend/Check/Tied.lean`): a derivation
is `CDerivesAt Ξ` at every effect context `Ξ` at which the rows it reads at `[perform]`, `[raise]`
and `[handle]` are, and those rows are the `Res`'s `sigs`. Nothing else produces a `Res`, so every
derivation the checker returns is a tied derivation, and so a `CDerives` derivation
(`CDerivesAt.toCDerives`), by construction.
-/

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check
open BoCa.Fig16.LogRel.Core (Jdg withPair withCtx absurdE forceE Persistent CtxOutlives HasDtor
  dropE dtorE)

abbrev CExpr := BoCa.Expr

/-- A checked term: its erasure `e`, the rows `sigs` its derivations read at `[perform]`,
`[raise]` and `[handle]`, and a tied derivation `TiedDer sigs Δ (mkCtx T L) e j` at every
admissible liveness `L` of the slots `T`. -/
structure Res (Δ : LifeCtx) (T : List CVTy) (j : Jdg) where
  e : CExpr
  sigs : CRow
  F : Fam T (fun L => TiedDer sigs Δ (mkCtx T L) e j)

section
variable {Δ : LifeCtx} {T : List CVTy}

/-! ### Leaves -/

def rVar (i : Nat) (A : CVTy) (h : T[i]? = some A) : Res Δ T (.val A) :=
  ⟨.var i, [], (Fam.var T i A h).map fun _ hs => .var hs⟩

def rUnit : Res Δ T (.val .unit) :=
  ⟨Expr.val BoCa.Val.unit, [], (Fam.dead T).map fun _ h => .unitI h⟩

def rTop : Res Δ T (.comp .top) :=
  ⟨Expr.val BoCa.Val.unit, [], (Fam.top T).map fun _ _ => .topI⟩

def rForce (i : Nat) (C : CCTy) (h : T[i]? = some (.thunk C)) : Res Δ T (.comp C) :=
  ⟨forceE C (.var i), [], (Fam.var T i _ h).map fun _ hs => .force hs⟩

/-! ### Structural value rules -/

def rPair {A B : CVTy} (r₁ : Res Δ T (.val A)) (r₂ : Res Δ T (.val B))
    (h : overlapOK T r₁.F.u r₂.F.u = true) : Res Δ T (.val (.tensor A B)) :=
  ⟨.pair r₁.e r₂.e, r₁.sigs ∪ r₂.sigs,
    (r₁.F.split r₂.F h).map fun _ ⟨_, _, hs, h₁, h₂⟩ => .tensorI hs h₁ h₂⟩

def rInl {A : CVTy} (B : CVTy) (r : Res Δ T (.val A)) : Res Δ T (.val (.sum A B)) :=
  ⟨.inj₁ r.e, r.sigs, r.F.map fun _ h => .sumI₁ h⟩

def rInr (A : CVTy) {B : CVTy} (r : Res Δ T (.val B)) : Res Δ T (.val (.sum A B)) :=
  ⟨.inj₂ r.e, r.sigs, r.F.map fun _ h => .sumI₂ h⟩

/-- `thunk M`: the body under one dead slot. -/
def rThunkF {A : CVTy} (r : Res Δ (.unit :: T) (.comp (.ret A))) :
    Option (Res Δ T (.val (.thunk (.ret A)))) := do
  let F ← r.F.popDead
  pure ⟨Expr.val (BoCa.Val.lam r.e), r.sigs, F.map fun _ h => .thunkF h⟩

/-- `thunkv N`: `N` erases to a λ. -/
def rThunkV {C : CCTy} (hC : C.isRet = false) (r : Res Δ T (.comp C)) :
    Option (Res Δ T (.val (.thunk C))) :=
  match r with
  | ⟨.lam b, s, F⟩ => some ⟨.lam b, s, F.map fun _ h => .thunkV (N := b) hC h⟩
  | _ => none

/-- The first used slot failing `p`. -/
def firstBad (p : CVTy → Bool) : List CVTy → List Bool → Option Nat
  | A :: T, a :: as => if a && !p A then some 0 else (firstBad p T as).map (· + 1)
  | _, _ => none

theorem persistent_of {L : List Bool} (h : ∀ s ∈ mkCtx T L, s.live = true → isBangB s.ty = true) :
    Persistent (mkCtx T L) := fun s hs hl => isBangB_sound (h s hs hl)

/-- `!thunk M`: every live slot of the context is at a `!` type. -/
def rBangThunkF {A : CVTy} (r : Res Δ (.unit :: T) (.comp (.ret A))) :
    Except (Option Nat) (Res Δ T (.val (.bang (.thunk (.ret A))))) := do
  let some F := r.F.popDead | throw none
  if hs : usedSat isBangB T F.u = true then
    pure ⟨Expr.val (BoCa.Val.lam r.e), r.sigs, (F.restrict isBangB hs).map fun _ ⟨h, hp⟩ =>
      .bangThunkF (persistent_of hp) h⟩
  else throw (firstBad isBangB T F.u)

/-- `!thunkv N`. -/
def rBangThunkV {C : CCTy} (hC : C.isRet = false) (r : Res Δ T (.comp C)) :
    Except (Option Nat) (Res Δ T (.val (.bang (.thunk C)))) :=
  match r with
  | ⟨.lam b, s, F⟩ =>
      if hs : usedSat isBangB T F.u = true then
        pure ⟨.lam b, s, (F.restrict isBangB hs).map fun _ ⟨h, hp⟩ =>
          .bangThunkV (N := b) (persistent_of hp) hC h⟩
      else throw (firstBad isBangB T F.u)
  | _ => throw none

def rBangE {A : CVTy} (r : Res Δ T (.val (.bang A))) : Res Δ T (.val A) :=
  ⟨r.e, r.sigs, r.F.map fun _ h => .bangE h⟩

/-- `boxed[@a] V`: `@a` defined and every live slot outlives it. -/
def rBoxI {A : CVTy} (a : CLife) (hwf : a.wf Δ = true) (r : Res Δ T (.val A))
    (hs : usedSat (outlivesB Δ a) T r.F.u = true) : Res Δ T (.val (.box a A)) :=
  ⟨r.e, r.sigs, (r.F.restrict (outlivesB Δ a) hs).map fun _ ⟨h, ho⟩ =>
    .boxI h ⟨defines_of_wf hwf, fun s hsm hl => outlivesB_sound Δ a s.ty (ho s hsm hl)⟩⟩

def rBoxE {a : CLife} {A : CVTy} (r : Res Δ T (.val (.box a A))) : Res Δ T (.val A) :=
  ⟨r.e, r.sigs, r.F.map fun _ h => .boxE h⟩

def rImmSub {b : CLife} {A : CVTy} (a : CLife) (hle : leB Δ a b = true)
    (r : Res Δ T (.val (.imm b A))) : Res Δ T (.val (.imm a A)) :=
  ⟨r.e, r.sigs, r.F.map fun _ h => .immSub h (leB_sound hle)⟩

def rMutSub {b : CLife} {A : CVTy} (a : CLife) (hle : leB Δ a b = true)
    (r : Res Δ T (.val (.mut b A))) : Res Δ T (.val (.mut a A)) :=
  ⟨r.e, r.sigs, r.F.map fun _ h => .mutSub h (leB_sound hle)⟩

def rRoll {A : CVTy} (hA : VTy.noMutB 0 A = true) (hc : VTy.clB 0 (.mu A) = true)
    (r : Res Δ T (.val (BoCa.Fig16.LogRel.Core.VTy.inst (.mu A) A))) : Res Δ T (.val (.mu A)) :=
  ⟨r.e, r.sigs, r.F.map fun _ h => .roll (VTy.noMutB_sound 0 A hA) (VTy.clB_sound 0 _ hc) h⟩

def rUnroll {A : CVTy} (r : Res Δ T (.val (.mu A))) :
    Res Δ T (.val (BoCa.Fig16.LogRel.Core.VTy.inst (.mu A) A)) :=
  ⟨r.e, r.sigs, r.F.map fun _ h => .unroll h⟩

def rOfRet {A : CVTy} (r : Res Δ T (.comp (.ret A))) : Res Δ T (.val A) :=
  ⟨r.e, r.sigs, r.F.map fun _ h => .ofRet h⟩

/-- `V W`: the argument on the left of the split, as `lolliE` has it. -/
def rLolliE {A B : CVTy} (rf : Res Δ T (.val (.lolli A B))) (ra : Res Δ T (.val A))
    (h : overlapOK T ra.F.u rf.F.u = true) : Res Δ T (.val B) :=
  ⟨.app rf.e ra.e, ra.sigs ∪ rf.sigs,
    (ra.F.split rf.F h).map fun _ ⟨_, _, hs, ha, hf⟩ => .lolliE hs ha hf⟩

def rAllEV {x : LifeVar} {b : CLife} {A : CVTy} (a : CLife) (hlt : ltB Δ a b = true)
    (r : Res Δ T (.val (.all x b A))) : Res Δ T (.val (A.instLife x a)) :=
  ⟨.app r.e (Expr.val BoCa.Val.unit), r.sigs, r.F.map fun _ h => .allEV h (ltB_sound hlt)⟩

/-! ### Computation rules -/

def rRet {A : CVTy} (r : Res Δ T (.val A)) : Res Δ T (.comp (.ret A)) :=
  ⟨r.e, r.sigs, r.F.map fun _ h => .ret h⟩

/-- `x <- M; N`: `N`'s binder closed live, then split. -/
def rBind {A : CVTy} {C : CCTy} {sN : CRow} (rM : Res Δ T (.comp (.ret A)))
    (FN : Fam T (fun L => TiedDer sN Δ (mkCtx (A :: T) (true :: L)) eN (.comp C)))
    (h : overlapOK T rM.F.u FN.u = true) : Res Δ T (.comp C) :=
  ⟨.app (Expr.val (BoCa.Val.lam eN)) rM.e, rM.sigs ∪ sN,
    (rM.F.split FN h).map fun _ ⟨_, _, hs, h₁, h₂⟩ => .bind hs h₁ h₂⟩

def rLam {A : CVTy} {C : CCTy} {sM : CRow}
    (FM : Fam T (fun L => TiedDer sM Δ (mkCtx (A :: T) (true :: L)) eM (.comp C))) :
    Res Δ T (.comp (.arr A C)) :=
  ⟨Expr.val (BoCa.Val.lam eM), sM, FM.map fun _ h => .lam h⟩

/-- `[λ-dead]`: `λx. M : 1 ⊸ F_Σ B`, the binder's slot closed dead: `M` does not use it.
`[spec §26]` -/
def rLamDead {S : CRow} {B : CVTy} {sM : CRow}
    (FM : Fam T (fun L => TiedDer sM Δ (mkCtx (.unit :: T) (false :: L)) eM (.comp (effOf S B)))) :
    Res Δ T (.comp (.arr .unit (effOf S B))) :=
  ⟨Expr.val (BoCa.Val.lam eM), sM, FM.map fun _ h => .lamDead h⟩

def rApp {A : CVTy} {C : CCTy} (rM : Res Δ T (.comp (.arr A C))) (i : Nat)
    (hi : T[i]? = some A) (h : overlapOK T rM.F.u (oneL T i) = true) : Res Δ T (.comp C) :=
  ⟨.app rM.e (.var i), rM.sigs, (rM.F.split (Fam.var T i A hi) h).map fun _ ⟨_, _, hs, h₁, h₂⟩ =>
    .app hs h₁ h₂⟩

/-- The two dead slots of `⟨M, N⟩`'s components (`withCtx`). -/
abbrev withT (T : List CVTy) : List CVTy := .unit :: .sum .unit .unit :: T

def popWith {j : Jdg} {e : CExpr} {s : CRow}
    (F : Fam (withT T) (fun L => TiedDer s Δ (mkCtx (withT T) L) e j)) :
    Option (Fam T (fun L => TiedDer s Δ (withCtx (mkCtx T L)) e j)) := do
  let F₁ ← F.popDead
  F₁.popDead

def rWith {C D : CCTy} {s₁ s₂ : CRow} (e₁ e₂ : CExpr)
    (F : Fam T (fun L => TiedDer s₁ Δ (withCtx (mkCtx T L)) e₁ (.comp C) ∧
      TiedDer s₂ Δ (withCtx (mkCtx T L)) e₂ (.comp D))) : Res Δ T (.comp (.amp C D)) :=
  ⟨withPair e₁ e₂, s₁ ∪ s₂, F.map fun _ ⟨h₁, h₂⟩ => .withI h₁ h₂⟩

def rProj₁ {C D : CCTy} (r : Res Δ T (.comp (.amp C D))) : Res Δ T (.comp C) :=
  ⟨.app r.e (Expr.val (BoCa.Val.inj₁ BoCa.Val.unit)), r.sigs, r.F.map fun _ h => .proj₁ h⟩

def rProj₂ {C D : CCTy} (r : Res Δ T (.comp (.amp C D))) : Res Δ T (.comp D) :=
  ⟨.app r.e (Expr.val (BoCa.Val.inj₂ BoCa.Val.unit)), r.sigs, r.F.map fun _ h => .proj₂ h⟩

def rUnitE {C : CCTy} (rV : Res Δ T (.val .unit)) (rM : Res Δ T (.comp C))
    (h : overlapOK T rV.F.u rM.F.u = true) : Res Δ T (.comp C) :=
  ⟨.seq rV.e rM.e, rV.sigs ∪ rM.sigs,
    (rV.F.split rM.F h).map fun _ ⟨_, _, hs, h₁, h₂⟩ => .unitE hs h₁ h₂⟩

def rTensorE {A B : CVTy} {C : CCTy} {sM : CRow} (rV : Res Δ T (.val (.tensor A B)))
    (FM : Fam T (fun L => TiedDer sM Δ (mkCtx (B :: A :: T) (true :: true :: L)) eM (.comp C)))
    (h : overlapOK T rV.F.u FM.u = true) : Res Δ T (.comp C) :=
  ⟨.letpair rV.e eM, rV.sigs ∪ sM,
    (rV.F.split FM h).map fun _ ⟨_, _, hs, h₁, h₂⟩ => .tensorE hs h₁ h₂⟩

def rSumE {A B : CVTy} {C : CCTy} {s₁ s₂ : CRow} (rV : Res Δ T (.val (.sum A B)))
    (F : Fam T (fun L => TiedDer s₁ Δ (mkCtx (A :: T) (true :: L)) e₁ (.comp C) ∧
      TiedDer s₂ Δ (mkCtx (B :: T) (true :: L)) e₂ (.comp C)))
    (h : overlapOK T rV.F.u F.u = true) : Res Δ T (.comp C) :=
  ⟨.case rV.e e₁ e₂, rV.sigs ∪ (s₁ ∪ s₂),
    (rV.F.split F h).map fun _ ⟨_, _, hs, h₁, h₂, h₃⟩ => .sumE hs h₁ h₂ h₃⟩

/-- `dtorE A xᵢ; M`: the destructor of slot `i` before `M`, which does not use it (SPEC §12).
`TiedDer.drop`, as `drop_derives`: `unitE` over `lolliE` of the variable and `dtor_wf`. -/
def rDrop {C : CCTy} (i : Nat) (A : CVTy) (hi : T[i]? = some A) (hA : HasDtor A)
    (hE : (dtorE A).effFree = true) (r : Res Δ T (.comp C))
    (h : overlapOK T (oneL T i) r.F.u = true) : Res Δ T (.comp C) :=
  ⟨dropE A i r.e, r.sigs, ((Fam.var T i A hi).split r.F h).map fun _ ⟨_, _, hs, hx, hM⟩ =>
    .drop hs hx hA hE hM⟩

/-- `absurd V`: the rest of the context is absorbed. -/
def rZeroE (C : CCTy) (rV : Res Δ T (.val .zero)) (h : overlapOK T rV.F.u (Fam.top T).u = true) :
    Res Δ T (.comp C) :=
  ⟨absurdE rV.e, rV.sigs, (rV.F.split (Fam.top T) h).map fun _ ⟨_, _, hs, h₁, _⟩ => .zeroE hs h₁⟩

/-- `Fun 'x < @b. M`: the body at `Δ, 'x ⊏ @b` under one dead slot, no live slot mentioning
`'x`. -/
def rAllI {x : LifeVar} {b : CLife} {C : CCTy} {sM : CRow} (hbx : b.mentions x = false)
    (hΔx : boundsAvoidB Δ x = true)
    (F : Fam T (fun L => TiedDer sM (Δ.extend x b) (mkCtx (.unit :: T) (false :: L)) eM (.comp C)))
    (hs : usedSat (fun A => !vfreeB x A) T F.u = true) : Res Δ T (.comp (.all x b C)) :=
  ⟨Expr.val (BoCa.Val.lam eM), sM, (F.restrict _ hs).map fun _ ⟨h, hx⟩ =>
    .allI hbx (boundsAvoidB_sound hΔx)
      (fun s hsm hl => not_vfree_of_vfreeB (by simpa using hx s hsm hl)) h⟩

def rAllE {x : LifeVar} {b : CLife} {C : CCTy} (a : CLife) (hlt : ltB Δ a b = true)
    (r : Res Δ T (.comp (.all x b C))) : Res Δ T (.comp (C.instLife x a)) :=
  ⟨.app r.e (Expr.val BoCa.Val.unit), r.sigs, r.F.map fun _ h => .allE h (ltB_sound hlt)⟩

/-- `nu_in M`: `M` at the unrolling of a positive `νX. C`. -/
def rNuIn {C : CCTy} (hC : C.NuOk) (r : Res Δ T (.comp C.unroll)) : Res Δ T (.comp (.nu C)) :=
  ⟨r.e, r.sigs, r.F.map fun _ h => .nuIn hC h⟩

/-- `nu_out M`. -/
def rNuOut {C : CCTy} (hC : C.NuOk) (r : Res Δ T (.comp (.nu C))) : Res Δ T (.comp C.unroll) :=
  ⟨r.e, r.sigs, r.F.map fun _ h => .nuOut hC h⟩

/-! ### Effects  `[spec §19]` -/

/-- `[sub]`: `F_Σ A ≤ F_Σ′ A` at `Σ ⊆ Σ′`. -/
def rEffSub {S S' : CRow} {A : CVTy} (hle : rowLeB S S' = true) (r : Res Δ T (.comp (effOf S A))) :
    Res Δ T (.comp (effOf S' A)) :=
  ⟨r.e, r.sigs, r.F.map fun _ h => .effSub (rowLeB_sound hle) h⟩

/-- `[perform]`: a non-abortive operation of the row, at its argument; it reads the row. -/
def rPerform {S : CRow} {o : COpSig} (hf : BoCa.Fig16.LogRel.Core.Row.find S o.n o.i = some o)
    (hna : o.abort = false) (r : Res Δ T (.val o.A)) : Res Δ T (.comp (effOf S o.B)) :=
  ⟨BoCa.BoLo.performE (BoCa.Fig16.LogRel.Core.opArgE o.n o.i r.e), S ∪ r.sigs,
    r.F.map fun _ h => .effPerform hf hna h⟩

/-- The abortive rule (SPEC §19): an abortive operation of the row, at any answer `B`; its argument
drops. It reads the row. -/
def rRaise {S : CRow} {o : COpSig} (B : CVTy)
    (hf : BoCa.Fig16.LogRel.Core.Row.find S o.n o.i = some o) (ha : o.abort = true)
    (hd : dropB o.A = true) (r : Res Δ T (.val o.A)) : Res Δ T (.comp (effOf S B)) :=
  ⟨BoCa.BoLo.raiseE (BoCa.Fig16.LogRel.Core.opArgE o.n o.i r.e), S ∪ r.sigs,
    r.F.map fun _ h => .effRaise hf ha (dropB_sound _ hd) h⟩

/-- `[let]`: `M to x. N` at a row, `N`'s context dropping at a row with weakening and persistent
at an unrestricted row. -/
def rEffLet {S : CRow} {A B : CVTy} {sN : CRow} (rM : Res Δ T (.comp (effOf S A)))
    (FN : Fam T (fun L => TiedDer sN Δ (mkCtx (A :: T) (true :: L)) eN (.comp (effOf S B)) ∧
      (S.Weak → (mkCtx T L).Drops) ∧ (S.Unr → Persistent (mkCtx T L))))
    (h : overlapOK T rM.F.u FN.u = true) : Res Δ T (.comp (effOf S B)) :=
  ⟨.app (Expr.val (BoCa.Val.lam eN)) rM.e, rM.sigs ∪ sN, (rM.F.split FN h).map
    fun _ ⟨_, _, hs, h₁, h₂, hW, hU⟩ => .effLet hs hW hU h₁ h₂⟩

/-- `[then]`: `M then x. N unwind D`, `N` and the finaliser `D` at one context. -/
def rEffThen {S : CRow} {A B : CVTy} {sN sD : CRow} (hNZ : S.NZ) (hUq : S.Uniq)
    (rM : Res Δ T (.comp (effOf S A)))
    (F : Fam T (fun L => (TiedDer sN Δ (mkCtx (A :: T) (true :: L)) eN (.comp (effOf S B)) ∧
      TiedDer sD Δ (mkCtx (.unit :: T) (false :: L)) eD
        (.comp (effOf [] .unit))) ∧
      (S.UnrD → Persistent (mkCtx T L))))
    (h : overlapOK T rM.F.u F.u = true) : Res Δ T (.comp (effOf S B)) :=
  ⟨BoCa.Fig16.LogRel.Core.thenE eN eD rM.e, rM.sigs ∪ (sN ∪ sD), (rM.F.split F h).map
    fun _ ⟨_, _, hs, h₁, ⟨hN, hD⟩, hU⟩ => .effThenA hs hNZ hUq hU h₁ hN hD⟩

/-- `[handle]`: `handle_n e with (h_ret, hs)`, the answer clause and the clauses the slots `ir`
and `ic`. It reads the handled row. -/
def rEffHandle {S : CRow} {E : List (CQual × CVTy × CVTy)} {n : UInt32} {A R : CVTy}
    (ir ic : Nat) (hir : T[ir]? = some (BoCa.Fig16.LogRel.Core.retTy S A R))
    (hic : T[ic]? = some (BoCa.Fig16.LogRel.Core.clausesTy S R E)) (hn0 : n ≠ 0)
    (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (rM : Res Δ T (.comp (effOf (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) A)))
    (h₁ : overlapOK T (oneL T ir) (oneL T ic) = true)
    (h₂ : overlapOK T (orL (oneL T ir) (oneL T ic)) rM.F.u = true) : Res Δ T (.comp (effOf S R)) :=
  ⟨BoCa.Fig16.LogRel.Core.hndTerm n (E.map Prod.fst) ir ic rM.e,
    (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) ∪ rM.sigs,
    (((Fam.var T ir _ hir).split (Fam.var T ic _ hic) h₁).split rM.F h₂).map
      fun _ ⟨_, _, hs, ⟨_, _, hs₁, hr, hc⟩, he⟩ => .effHandle hs hs₁ hr hc hn0 hnS hlen he⟩

/-- BOXED-κ: `handle_n e with (h_ret, hs)`, the clauses at `clausesTyB S R d E`, each capturing
clause's `κ` boxed at `@d`; `@d` defined, every live slot `e` uses outliving it, and every
non-abortive answer type of the handled row outliving it. It reads the handled row.
`[spec §28]` -/
def rEffHandleB {S : CRow} {E : List (CQual × CVTy × CVTy)} {n : UInt32} {A R : CVTy} {d : CLife}
    (ir ic : Nat) (hir : T[ir]? = some (BoCa.Fig16.LogRel.Core.retTy S A R))
    (hic : T[ic]? = some (BoCa.Fig16.LogRel.Core.clausesTyB S R d E)) (hn0 : n ≠ 0)
    (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32) (hwf : d.wf Δ = true)
    (hSd : ansOutlivesB Δ d (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) = true)
    (rM : Res Δ T (.comp (effOf (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) A)))
    (hso : usedSat (outlivesB Δ d) T rM.F.u = true)
    (h₁ : overlapOK T (oneL T ir) (oneL T ic) = true)
    (h₂ : overlapOK T (orL (oneL T ir) (oneL T ic)) rM.F.u = true) : Res Δ T (.comp (effOf S R)) :=
  ⟨BoCa.Fig16.LogRel.Core.hndTerm n (E.map Prod.fst) ir ic rM.e,
    (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) ∪ rM.sigs,
    (((Fam.var T ir _ hir).split (Fam.var T ic _ hic) h₁).split (rM.F.restrict (outlivesB Δ d) hso)
      h₂).map fun _ ⟨_, _, hs, ⟨_, _, hs₁, hr, hc⟩, he, ho⟩ =>
        .effHandleB hs hs₁ hr hc hn0 hnS hlen he
          ⟨defines_of_wf hwf, fun s hsm hl => outlivesB_sound Δ d s.ty (ho s hsm hl)⟩
          (ansOutlivesB_sound hSd)⟩

end

end Frontend.Check
