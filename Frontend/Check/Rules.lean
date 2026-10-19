import Frontend.Check.TTied

/-!
# Frontend — Check — rules

One builder per `CDerives` constructor (and, in `Frontend/Check/Consts.lean`, per derived
rule). A builder takes the checked premises (`Res`: a typed term with its family of
derivations, `Frontend/Check/Fam.lean`), the decided side conditions and the source the node is
checked from (`TInfo`), and returns the conclusion's `Res`: the conclusion's node of the typed
term (`Frontend/Check/TExpr.lean`), its children the premises' terms, together with its
derivations, each built by applying the typed rule, tied (decision R, `Frontend/Check/TTied.lean`):
a derivation is `TDerivesAt Ξ` at every effect context `Ξ` at which the rows it reads at
`[perform]`, `[raise]` and `[handle]` are, and those rows are the `Res`'s `sigs`. Nothing else
produces a `Res`, so every derivation the checker returns is a tied derivation of its typed term,
and so a `CDerives` derivation of the term's erasure (`TDerivesAt.erase`,
`CDerivesAt.toCDerives`), by construction.
-/

namespace Frontend.Check
open BoCa BoCa.Lifetime
open BoCa.Fig16.LogRel.Core.Check
open BoCa.Fig16.LogRel.Core (Jdg withPair withCtx absurdE forceE Persistent CtxOutlives HasDtor
  dropE dtorE)

abbrev CExpr := BoCa.Expr

/-- A checked term: its typed term `t`, the rows `sigs` its derivations read at `[perform]`,
`[raise]` and `[handle]`, the relaxed rules `pins` they use (SPEC §29), and a derivation
`TTied pins sigs Δ (mkCtx T L) t j` at every admissible liveness `L` of the slots `T`. -/
structure Res (Δ : LifeCtx) (T : List CVTy) (j : Jdg) where
  t : TExpr
  sigs : CRow
  pins : Pins
  F : Fam T (fun L => TTied pins sigs Δ (mkCtx T L) t j)

/-- The checked term's erasure: the term its derivations type. -/
def Res.e {Δ : LifeCtx} {T : List CVTy} {j : Jdg} (r : Res Δ T j) : CExpr := r.t.erase

/-- A node's source: its span. -/
abbrev at_ (sp : Span) : TInfo := { sp }

section
variable {Δ : LifeCtx} {T : List CVTy} (i : TInfo)

/-! ### Leaves -/

def rVar (k : Nat) (A : CVTy) (h : T[k]? = some A) : Res Δ T (.val A) :=
  ⟨.var i (.val A) k A, [], [], (Fam.var T k A h).map fun _ hs => TTied.var i hs⟩

def rUnit : Res Δ T (.val .unit) :=
  ⟨.unitI i (.val .unit), [], [], (Fam.dead T).map fun _ h => TTied.unitI i h⟩

def rTop : Res Δ T (.comp .top) :=
  ⟨.topI i (.comp .top), [], [], (Fam.top T).map fun _ _ => TTied.topI i⟩

def rForce (k : Nat) (C : CCTy) (h : T[k]? = some (.thunk C)) : Res Δ T (.comp C) :=
  ⟨.force i (.comp C) k C, [], [], (Fam.var T k _ h).map fun _ hs => TTied.force i hs⟩

/-! ### A `def` at its use  `[spec §10]`

A `def`'s body is checked once per key at a context `Tc` of persistent externs, and placed at a use
whose context `T` is `Tc` under `m` more slots (`T.drop m = Tc`): the use's slots before `Tc` are
unused by the body, and each may be given to it, live, where the body's absorption holds of its
type (`TTied.weaken`). -/

theorem btw_append : ∀ {u₁ w₁ u₂ w₂ L : List Bool}, u₁.length = w₁.length →
    Btw (u₁ ++ u₂) (w₁ ++ w₂) L → ∃ L₁ L₂, L = L₁ ++ L₂ ∧ L₁.length = u₁.length ∧ Btw u₁ w₁ L₁ ∧
      Btw u₂ w₂ L₂
  | [], [], _, _, L, _, h => ⟨[], L, rfl, rfl, .nil, h⟩
  | _ :: _, _ :: _, _, _, _ :: _, hl, .cons h₁ h₂ h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      obtain ⟨L₁, L₂, rfl, hl₁, b₁, b₂⟩ := btw_append hl h
      exact ⟨_ :: L₁, L₂, rfl, by simp [hl₁], .cons h₁ h₂ b₁, b₂⟩
  | [], _ :: _, _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, _, hl, _ => by simp at hl

theorem mkCtx_append : ∀ {T₁ : List CVTy} {L₁ : List Bool} (T₂ : List CVTy) (L₂ : List Bool),
    L₁.length = T₁.length → mkCtx (T₁ ++ T₂) (L₁ ++ L₂) = mkCtx T₁ L₁ ++ mkCtx T₂ L₂
  | [], [], _, _, _ => rfl
  | _ :: T₁, _ :: L₁, T₂, L₂, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.cons_append, mkCtx, mkCtx_append T₂ L₂ h]
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h

theorem mkCtx_length : ∀ {T : List CVTy} {L : List Bool}, L.length = T.length →
    (mkCtx T L).length = T.length
  | [], [], _ => rfl
  | _ :: T, _ :: L, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp [mkCtx, mkCtx_length h]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem liveP_of_btw (p : CVTy → Bool) : ∀ {T : List CVTy} {L : List Bool},
    Btw (noneL T) (T.map p) L → LiveP p (mkCtx T L)
  | [], [], _ => fun _ hs => by simp [mkCtx] at hs
  | A :: T, l :: L, .cons _ h₂ h => by
      intro s hs hl
      simp only [mkCtx, List.mem_cons] at hs
      rcases hs with rfl | hs
      · rcases h₂ hl with h | h
        · simp at h
        · simpa using h
      · exact liveP_of_btw p h s hs hl

/-- **A `def`'s body at its use**: the body `r`, checked at `Tc`, at the use's context `T`, its
`m` slots before `Tc` unused and absorbed where the body's absorption `f` holds. -/
def rUse (name : String) (decl : Nat) (targs : List CVTy) {Tc : List CVTy} {A : CVTy}
    (m : Nat) (hT : T.drop m = Tc) (r : Res Δ Tc (.val A)) (f : AbsF)
    (hf : r.t.absF Δ = some f) : Res Δ T (.val A) :=
  have hT' : T = T.take m ++ Tc := by rw [← hT, List.take_append_drop]
  have hl : (noneL (T.take m)).length = ((T.take m).map f.eval).length := by
    simp [noneL]
  hT' ▸ ⟨.use i (.val A) name decl targs (some f) (r.t.shift (T.take m).length 0), r.sigs, r.pins,
    ⟨noneL (T.take m) ++ r.F.u, (T.take m).map f.eval ++ r.F.w,
      by simp [noneL, r.F.hu], by simp [r.F.hw],
      fun L hb => by
        obtain ⟨L₁, L₂, rfl, hl₁, b₁, b₂⟩ := btw_append hl hb
        rw [noneL_length] at hl₁
        have hw := TTied.weaken (Γa := []) (Γp := mkCtx (T.take m) L₁) (r.F.d L₂ b₂) hf
          (liveP_of_btw f.eval b₁)
        rw [mkCtx_length hl₁] at hw
        rw [mkCtx_append Tc L₂ hl₁]
        have hu := TTied.use (i := i) name decl targs hw
        rwa [TExpr.absF_shift, hf] at hu⟩⟩

/-- A `def`'s body checked at the use's own context, under its `use` node. -/
def rUseAt (name : String) (decl : Nat) (targs : List CVTy) {A : CVTy} (r : Res Δ T (.val A)) :
    Res Δ T (.val A) :=
  ⟨.use i (.val A) name decl targs (r.t.absF Δ) r.t, r.sigs, r.pins,
    r.F.map fun _ h => TTied.use i name decl targs h⟩

/-! ### Marked schemes  `[spec §3]` -/

/-- A string literal's table, the bytes `bs`: the derived node over its checked term `r`, when
`r`'s erasure is `litFnE bs`. -/
def rLitFn {j : Jdg} (bs : List Nat) (r : Res Δ T j) : Option (Res Δ T j) :=
  if hb : r.t.erase = litFnE bs then
    if hcl : BoCa.Fig16.LogRel.Core.closedAt 0 (litFnE bs) = true then
      some ⟨.litFn i j bs r.t, r.sigs, r.pins, r.F.map fun _ h => TTied.litFn i hb hcl h⟩
    else none
  else none

/-! ### Structural value rules -/

def rPair {A B : CVTy} (r₁ : Res Δ T (.val A)) (r₂ : Res Δ T (.val B))
    (h : overlapOK T r₁.F.u r₂.F.u = true) : Res Δ T (.val (.tensor A B)) :=
  ⟨.tensorI i (.val (.tensor A B)) A B r₁.F.u r₁.t r₂.t, r₁.sigs ∪ r₂.sigs, r₁.pins ++ r₂.pins,
    (r₁.F.split r₂.F h).map fun _ ⟨_, _, hs, h₁, h₂⟩ => TTied.tensorI i r₁.F.u hs h₁ h₂⟩

def rInl {A : CVTy} (B : CVTy) (r : Res Δ T (.val A)) : Res Δ T (.val (.sum A B)) :=
  ⟨.sumI₁ i (.val (.sum A B)) A B r.t, r.sigs, r.pins, r.F.map fun _ h => TTied.sumI₁ i h⟩

def rInr (A : CVTy) {B : CVTy} (r : Res Δ T (.val B)) : Res Δ T (.val (.sum A B)) :=
  ⟨.sumI₂ i (.val (.sum A B)) A B r.t, r.sigs, r.pins, r.F.map fun _ h => TTied.sumI₂ i h⟩

/-- `thunk M`: the body under one dead slot. -/
def rThunkF {A : CVTy} (r : Res Δ (.unit :: T) (.comp (.ret A))) :
    Option (Res Δ T (.val (.thunk (.ret A)))) := do
  let F ← r.F.popDead
  pure ⟨.thunkF i (.val (.thunk (.ret A))) A r.t, r.sigs, r.pins, F.map fun _ h => TTied.thunkF i h⟩

/-- `thunkv N`: `N` erases to a λ. -/
def rThunkV {C : CCTy} (hC : C.isRet = false) (r : Res Δ T (.comp C)) :
    Option (Res Δ T (.val (.thunk C))) :=
  if hl : r.t.isLam = true then
    some ⟨.thunkV i (.val (.thunk C)) C r.t, r.sigs, r.pins, r.F.map fun _ h =>
      have ⟨_, q⟩ := TExpr.isLam_sound _ hl
      TTied.thunkV i hC h q⟩
  else none

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
    pure ⟨.bangThunkF i (.val (.bang (.thunk (.ret A)))) A r.t, r.sigs, r.pins,
      (F.restrict isBangB hs).map fun _ ⟨h, hp⟩ => TTied.bangThunkF i (persistent_of hp) h⟩
  else throw (firstBad isBangB T F.u)

/-- `!thunkv N`. -/
def rBangThunkV {C : CCTy} (hC : C.isRet = false) (r : Res Δ T (.comp C)) :
    Except (Option Nat) (Res Δ T (.val (.bang (.thunk C)))) :=
  if hl : r.t.isLam = true then
    if hs : usedSat isBangB T r.F.u = true then
      pure ⟨.bangThunkV i (.val (.bang (.thunk C))) C r.t, r.sigs, r.pins,
        (r.F.restrict isBangB hs).map fun _ ⟨h, hp⟩ =>
          have ⟨_, q⟩ := TExpr.isLam_sound _ hl
          TTied.bangThunkV i (persistent_of hp) hC h q⟩
    else throw (firstBad isBangB T r.F.u)
  else throw none

def rBangE {A : CVTy} (r : Res Δ T (.val (.bang A))) : Res Δ T (.val A) :=
  ⟨.bangE i (.val A) A r.t, r.sigs, r.pins, r.F.map fun _ h => TTied.bangE i h⟩

/-- `boxed[@a] V`: `@a` defined and every live slot outlives it. -/
def rBoxI {A : CVTy} (a : CLife) (hwf : a.wf Δ = true) (r : Res Δ T (.val A))
    (hs : usedSat (outlivesB Δ a) T r.F.u = true) : Res Δ T (.val (.box a A)) :=
  ⟨.boxI i (.val (.box a A)) a A r.t, r.sigs, r.pins,
    (r.F.restrict (outlivesB Δ a) hs).map fun _ ⟨h, ho⟩ =>
      TTied.boxI i h ⟨defines_of_wf hwf, fun s hsm hl => outlivesB_sound Δ a s.ty (ho s hsm hl)⟩⟩

def rBoxE {a : CLife} {A : CVTy} (r : Res Δ T (.val (.box a A))) : Res Δ T (.val A) :=
  ⟨.boxE i (.val A) a A r.t, r.sigs, r.pins, r.F.map fun _ h => TTied.boxE i h⟩

def rImmSub {b : CLife} {A : CVTy} (a : CLife) (hle : leB Δ a b = true)
    (r : Res Δ T (.val (.imm b A))) : Res Δ T (.val (.imm a A)) :=
  ⟨.immSub i (.val (.imm a A)) a b A r.t, r.sigs, r.pins,
    r.F.map fun _ h => TTied.immSub i h (leB_sound hle)⟩

def rMutSub {b : CLife} {A : CVTy} (a : CLife) (hle : leB Δ a b = true)
    (r : Res Δ T (.val (.mut b A))) : Res Δ T (.val (.mut a A)) :=
  ⟨.mutSub i (.val (.mut a A)) a b A r.t, r.sigs, r.pins,
    r.F.map fun _ h => TTied.mutSub i h (leB_sound hle)⟩

def rRoll {A : CVTy} (hA : VTy.noMutB 0 A = true) (hc : VTy.clB 0 (.mu A) = true)
    (r : Res Δ T (.val (BoCa.Fig16.LogRel.Core.VTy.inst (.mu A) A))) : Res Δ T (.val (.mu A)) :=
  ⟨.roll i (.val (.mu A)) A r.t, r.sigs, r.pins, r.F.map fun _ h =>
    TTied.roll i (VTy.noMutB_sound 0 A hA) (VTy.clB_sound 0 _ hc) h⟩

def rUnroll {A : CVTy} (r : Res Δ T (.val (.mu A))) :
    Res Δ T (.val (BoCa.Fig16.LogRel.Core.VTy.inst (.mu A) A)) :=
  ⟨.unroll i (.val (BoCa.Fig16.LogRel.Core.VTy.inst (.mu A) A)) A r.t, r.sigs, r.pins,
    r.F.map fun _ h => TTied.unroll i h⟩

def rOfRet {A : CVTy} (r : Res Δ T (.comp (.ret A))) : Res Δ T (.val A) :=
  ⟨.ofRet i (.val A) A r.t, r.sigs, r.pins, r.F.map fun _ h => TTied.ofRet i h⟩

/-- `V W`: the argument on the left of the split, as `lolliE` has it. -/
def rLolliE {A B : CVTy} (rf : Res Δ T (.val (.lolli A B))) (ra : Res Δ T (.val A))
    (h : overlapOK T ra.F.u rf.F.u = true) : Res Δ T (.val B) :=
  ⟨.lolliE i (.val B) A B ra.F.u ra.t rf.t, ra.sigs ∪ rf.sigs, ra.pins ++ rf.pins,
    (ra.F.split rf.F h).map fun _ ⟨_, _, hs, ha, hf⟩ => TTied.lolliE i ra.F.u hs ha hf⟩

def rAllEV {x : LifeVar} {b : CLife} {A : CVTy} (a : CLife) (hlt : ltB Δ a b = true)
    (r : Res Δ T (.val (.all x b A))) : Res Δ T (.val (A.instLife x a)) :=
  ⟨.allEV i (.val (A.instLife x a)) x b a A r.t, r.sigs, r.pins,
    r.F.map fun _ h => TTied.allEV i h (ltB_sound hlt)⟩

/-! ### Computation rules -/

def rRet {A : CVTy} (r : Res Δ T (.val A)) : Res Δ T (.comp (.ret A)) :=
  ⟨.ret i (.comp (.ret A)) A r.t, r.sigs, r.pins, r.F.map fun _ h => TTied.ret i h⟩

/-- `x <- M; N`: `N`'s binder closed live, then split. -/
def rBind {A : CVTy} {C : CCTy} {tN : TExpr} {sN : CRow} {pN : Pins}
    (rM : Res Δ T (.comp (.ret A)))
    (FN : Fam T (fun L => TTied pN sN Δ (mkCtx (A :: T) (true :: L)) tN (.comp C)))
    (h : overlapOK T rM.F.u FN.u = true) : Res Δ T (.comp C) :=
  ⟨.bind i (.comp C) A C rM.F.u rM.t tN, rM.sigs ∪ sN, rM.pins ++ pN,
    (rM.F.split FN h).map fun _ ⟨_, _, hs, h₁, h₂⟩ => TTied.bind i rM.F.u hs h₁ h₂⟩

def rLam {A : CVTy} {C : CCTy} {tM : TExpr} {sM : CRow} {pM : Pins}
    (FM : Fam T (fun L => TTied pM sM Δ (mkCtx (A :: T) (true :: L)) tM (.comp C))) :
    Res Δ T (.comp (.arr A C)) :=
  ⟨.lam i (.comp (.arr A C)) A C tM, sM, pM, FM.map fun _ h => TTied.lam i h⟩

/-- `[λ-dead]`: `λx. M : 1 ⊸ F_Σ B`, the binder's slot closed dead: `M` does not use it.
`[spec §26]` -/
def rLamDead {S : CRow} {B : CVTy} {tM : TExpr} {sM : CRow} {pM : Pins}
    (FM : Fam T (fun L => TTied pM sM Δ (mkCtx (.unit :: T) (false :: L)) tM (.comp (effOf S B)))) :
    Res Δ T (.comp (.arr .unit (effOf S B))) :=
  ⟨.lamDead i (.comp (.arr .unit (effOf S B))) S B tM, sM, pM, FM.map fun _ h => TTied.lamDead i h⟩

/-- `M x`: the node's name is the argument's. -/
def rApp {A : CVTy} {C : CCTy} (rM : Res Δ T (.comp (.arr A C))) (k : Nat)
    (hk : T[k]? = some A) (h : overlapOK T rM.F.u (oneL T k) = true) : Res Δ T (.comp C) :=
  ⟨.app i (.comp C) k A C rM.F.u rM.t, rM.sigs, rM.pins,
    (rM.F.split (Fam.var T k A hk) h).map fun _ ⟨_, _, hs, h₁, h₂⟩ => TTied.app i rM.F.u hs h₁ h₂⟩

/-- The two dead slots of `⟨M, N⟩`'s components (`withCtx`). -/
abbrev withT (T : List CVTy) : List CVTy := .unit :: .sum .unit .unit :: T

def popWith {j : Jdg} {t : TExpr} {s : CRow} {p : Pins}
    (F : Fam (withT T) (fun L => TTied p s Δ (mkCtx (withT T) L) t j)) :
    Option (Fam T (fun L => TTied p s Δ (withCtx (mkCtx T L)) t j)) := do
  let F₁ ← F.popDead
  F₁.popDead

def rWith {C D : CCTy} {s₁ s₂ : CRow} {p₁ p₂ : Pins} (t₁ t₂ : TExpr)
    (F : Fam T (fun L => TTied p₁ s₁ Δ (withCtx (mkCtx T L)) t₁ (.comp C) ∧
      TTied p₂ s₂ Δ (withCtx (mkCtx T L)) t₂ (.comp D))) : Res Δ T (.comp (.amp C D)) :=
  ⟨.withI i (.comp (.amp C D)) C D t₁ t₂, s₁ ∪ s₂, p₁ ++ p₂,
    F.map fun _ ⟨h₁, h₂⟩ => TTied.withI i h₁ h₂⟩

def rProj₁ {C D : CCTy} (r : Res Δ T (.comp (.amp C D))) : Res Δ T (.comp C) :=
  ⟨.proj₁ i (.comp C) C D r.t, r.sigs, r.pins, r.F.map fun _ h => TTied.proj₁ i h⟩

def rProj₂ {C D : CCTy} (r : Res Δ T (.comp (.amp C D))) : Res Δ T (.comp D) :=
  ⟨.proj₂ i (.comp D) C D r.t, r.sigs, r.pins, r.F.map fun _ h => TTied.proj₂ i h⟩

def rUnitE {C : CCTy} (rV : Res Δ T (.val .unit)) (rM : Res Δ T (.comp C))
    (h : overlapOK T rV.F.u rM.F.u = true) : Res Δ T (.comp C) :=
  ⟨.unitE i (.comp C) C rV.F.u rV.t rM.t, rV.sigs ∪ rM.sigs, rV.pins ++ rM.pins,
    (rV.F.split rM.F h).map fun _ ⟨_, _, hs, h₁, h₂⟩ => TTied.unitE i rV.F.u hs h₁ h₂⟩

def rTensorE {A B : CVTy} {C : CCTy} {tM : TExpr} {sM : CRow} {pM : Pins}
    (rV : Res Δ T (.val (.tensor A B)))
    (FM : Fam T (fun L => TTied pM sM Δ (mkCtx (B :: A :: T) (true :: true :: L)) tM (.comp C)))
    (h : overlapOK T rV.F.u FM.u = true) : Res Δ T (.comp C) :=
  ⟨.tensorE i (.comp C) A B C rV.F.u rV.t tM, rV.sigs ∪ sM, rV.pins ++ pM,
    (rV.F.split FM h).map fun _ ⟨_, _, hs, h₁, h₂⟩ => TTied.tensorE i rV.F.u hs h₁ h₂⟩

def rSumE {A B : CVTy} {C : CCTy} {t₁ t₂ : TExpr} {s₁ s₂ : CRow} {p₁ p₂ : Pins}
    (rV : Res Δ T (.val (.sum A B)))
    (F : Fam T (fun L => TTied p₁ s₁ Δ (mkCtx (A :: T) (true :: L)) t₁ (.comp C) ∧
      TTied p₂ s₂ Δ (mkCtx (B :: T) (true :: L)) t₂ (.comp C)))
    (h : overlapOK T rV.F.u F.u = true) : Res Δ T (.comp C) :=
  ⟨.sumE i (.comp C) A B C rV.F.u rV.t t₁ t₂, rV.sigs ∪ (s₁ ∪ s₂), rV.pins ++ (p₁ ++ p₂),
    (rV.F.split F h).map fun _ ⟨_, _, hs, h₁, h₂, h₃⟩ => TTied.sumE i rV.F.u hs h₁ h₂ h₃⟩

/-- `dtorE A xᵢ; M`: the destructor of slot `k` before `M`, which does not use it (SPEC §12).
`TTied.drop`, as `drop_derives`: `unitE` over `lolliE` of the variable and the destructor. The
variable's node has the source `ix`. -/
def rDrop (ix : TInfo) {C : CCTy} (k : Nat) (A : CVTy) (hk : T[k]? = some A) (hA : HasDtor A)
    (hc : BoCa.Fig16.LogRel.Core.closedAt 0 (dtorE A) = true) (hE : (dtorE A).effFree = true)
    (r : Res Δ T (.comp C))
    (h : overlapOK T (oneL T k) r.F.u = true) : Res Δ T (.comp C) :=
  ⟨.unitE i (.comp C) C (oneL T k)
      (.lolliE ix (.val .unit) A .unit (oneL T k) (.var ix (.val A) k A)
        (.dtor ix (.val (.lolli A .unit)) A)) r.t,
    r.sigs, r.pins, ((Fam.var T k A hk).split r.F h).map fun _ ⟨_, _, hs, hx, hM⟩ =>
      TTied.drop i ix (oneL T k) hs hx hA hc hE hM⟩

/-- `absurd V`: the rest of the context is absorbed. -/
def rZeroE (C : CCTy) (rV : Res Δ T (.val .zero)) (h : overlapOK T rV.F.u (Fam.top T).u = true) :
    Res Δ T (.comp C) :=
  ⟨.zeroE i (.comp C) C rV.F.u rV.t, rV.sigs, rV.pins,
    (rV.F.split (Fam.top T) h).map fun _ ⟨_, _, hs, h₁, _⟩ => TTied.zeroE i rV.F.u hs h₁⟩

/-- `Fun 'x < @b. M`: the body at `Δ, 'x ⊏ @b` under one dead slot, no live slot mentioning
`'x`. -/
def rAllI {x : LifeVar} {b : CLife} {C : CCTy} {tM : TExpr} {sM : CRow} {pM : Pins}
    (hbx : b.mentions x = false) (hΔx : boundsAvoidB Δ x = true)
    (F : Fam T (fun L => TTied pM sM (Δ.extend x b) (mkCtx (.unit :: T) (false :: L)) tM (.comp C)))
    (hs : usedSat (fun A => !vfreeB x A) T F.u = true) : Res Δ T (.comp (.all x b C)) :=
  ⟨.allI i (.comp (.all x b C)) x b .unit C tM, sM, pM, (F.restrict _ hs).map fun _ ⟨h, hx⟩ =>
    TTied.allI i hbx (boundsAvoidB_sound hΔx)
      (fun s hsm hl => not_vfree_of_vfreeB (by simpa using hx s hsm hl)) h⟩

def rAllE {x : LifeVar} {b : CLife} {C : CCTy} (a : CLife) (hlt : ltB Δ a b = true)
    (r : Res Δ T (.comp (.all x b C))) : Res Δ T (.comp (C.instLife x a)) :=
  ⟨.allE i (.comp (C.instLife x a)) x b a C r.t, r.sigs, r.pins,
    r.F.map fun _ h => TTied.allE i h (ltB_sound hlt)⟩

/-- `nu_in M`: `M` at the unrolling of a positive `νX. C`. -/
def rNuIn {C : CCTy} (hC : C.NuOk) (r : Res Δ T (.comp C.unroll)) : Res Δ T (.comp (.nu C)) :=
  ⟨.nuIn i (.comp (.nu C)) C r.t, r.sigs, r.pins, r.F.map fun _ h => TTied.nuIn i hC h⟩

/-- `nu_out M`. -/
def rNuOut {C : CCTy} (hC : C.NuOk) (r : Res Δ T (.comp (.nu C))) : Res Δ T (.comp C.unroll) :=
  ⟨.nuOut i (.comp C.unroll) C r.t, r.sigs, r.pins, r.F.map fun _ h => TTied.nuOut i hC h⟩

/-! ### Effects  `[spec §19]` -/

/-- `[sub]`: `F_Σ A ≤ F_Σ′ A` at `Σ ⊆ Σ′`. -/
def rEffSub {S S' : CRow} {A : CVTy} (hle : rowLeB S S' = true) (r : Res Δ T (.comp (effOf S A))) :
    Res Δ T (.comp (effOf S' A)) :=
  ⟨.effSub i (.comp (effOf S' A)) S S' A r.t, r.sigs, r.pins,
    r.F.map fun _ h => TTied.effSub i (rowLeB_sound hle) h⟩

/-- `[perform]`: a non-abortive operation of the row, at its argument; it reads the row. -/
def rPerform {S : CRow} {o : COpSig} (hf : BoCa.Fig16.LogRel.Core.Row.find S o.n o.i = some o)
    (hna : o.abort = false) (r : Res Δ T (.val o.A)) : Res Δ T (.comp (effOf S o.B)) :=
  ⟨.effPerform i (.comp (effOf S o.B)) S o r.t, S ∪ r.sigs, r.pins,
    r.F.map fun _ h => TTied.effPerform i hf hna h⟩

/-- The abortive rule (SPEC §19): an abortive operation of the row, at any answer `B`; its argument
drops. It reads the row. -/
def rRaise {S : CRow} {o : COpSig} (B : CVTy)
    (hf : BoCa.Fig16.LogRel.Core.Row.find S o.n o.i = some o) (ha : o.abort = true)
    (hd : dropB o.A = true) (r : Res Δ T (.val o.A)) : Res Δ T (.comp (effOf S B)) :=
  ⟨.effRaise i (.comp (effOf S B)) S o B r.t, S ∪ r.sigs, r.pins,
    r.F.map fun _ h => TTied.effRaise i hf ha (dropB_sound _ hd) h⟩

/-- `[let]`: `M to x. N` at a row, `N`'s context dropping at a row with weakening and persistent
at an unrestricted row. -/
def rEffLet {S : CRow} {A B : CVTy} {tN : TExpr} {sN : CRow} {pN : Pins}
    (rM : Res Δ T (.comp (effOf S A)))
    (FN : Fam T (fun L => TTied pN sN Δ (mkCtx (A :: T) (true :: L)) tN (.comp (effOf S B)) ∧
      (S.Weak → (mkCtx T L).Drops) ∧ (S.Unr → Persistent (mkCtx T L))))
    (h : overlapOK T rM.F.u FN.u = true) : Res Δ T (.comp (effOf S B)) :=
  ⟨.effLet i (.comp (effOf S B)) A B S rM.F.u rM.t tN, rM.sigs ∪ sN, rM.pins ++ pN, (rM.F.split FN h).map
    fun _ ⟨_, _, hs, h₁, h₂, hW, hU⟩ => TTied.effLet i rM.F.u hs hW hU h₁ h₂⟩

/-- `[then]`: `M then x. N unwind D`, `N` and the finaliser `D` at one context. -/
def rEffThen {S : CRow} {A B : CVTy} {tN tD : TExpr} {sN sD : CRow} {pN pD : Pins} (hNZ : S.NZ)
    (hUq : S.Uniq) (rM : Res Δ T (.comp (effOf S A)))
    (F : Fam T (fun L => (TTied pN sN Δ (mkCtx (A :: T) (true :: L)) tN (.comp (effOf S B)) ∧
      TTied pD sD Δ (mkCtx (.unit :: T) (false :: L)) tD
        (.comp (effOf [] .unit))) ∧
      (S.UnrD → Persistent (mkCtx T L))))
    (h : overlapOK T rM.F.u F.u = true) : Res Δ T (.comp (effOf S B)) :=
  ⟨.effThen i (.comp (effOf S B)) A B S S [] rM.F.u rM.t tN tD, rM.sigs ∪ (sN ∪ sD),
    rM.pins ++ (pN ++ pD), (rM.F.split F h).map
    fun _ ⟨_, _, hs, h₁, ⟨hN, hD⟩, hU⟩ => TTied.effThenA i rM.F.u hs hNZ hUq hU h₁ hN hD⟩

/-- `[handle]`: `handle_n e with (h_ret, hs)`, the answer clause and the clauses the slots `kr`
and `kc`, the variables' nodes with the sources `ir` and `ic`. It reads the handled row. -/
def rEffHandle (ir ic : TInfo) {S : CRow} {E : List (CQual × CVTy × CVTy)} {n : UInt32}
    {A R : CVTy} (kr kc : Nat) (ks : List BoCa.Fig16.LogRel.Core.ClauseKinds.HKind)
    (site : Option HSite) (hkr : T[kr]? = some (BoCa.Fig16.LogRel.Core.retTy S A R))
    (hkc : T[kc]? = some (BoCa.Fig16.LogRel.Core.clausesTy S R E)) (hn0 : n ≠ 0)
    (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : BoCa.Fig16.LogRel.Core.Row.divB (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) = false)
    (rM : Res Δ T (.comp (effOf (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) A)))
    (h₁ : overlapOK T (oneL T kr) (oneL T kc) = true)
    (h₂ : overlapOK T (orL (oneL T kr) (oneL T kc)) rM.F.u = true) : Res Δ T (.comp (effOf S R)) :=
  ⟨.effHandleV i (.comp (effOf S R)) S E BoCa.Fig16.LogRel.Core.finsNil n A R
      (orL (oneL T kr) (oneL T kc)) ks site
      (TTied.hndPair ir ic (BoCa.Fig16.LogRel.Core.retTy S A R)
        (BoCa.Fig16.LogRel.Core.clausesTy S R E) kr kc (oneL T kr)) rM.t,
    (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) ∪ rM.sigs, rM.pins,
    (((Fam.var T kr _ hkr).split (Fam.var T kc _ hkc) h₁).split rM.F h₂).map
      fun _ ⟨_, _, hs, ⟨_, _, hs₁, hr, hc⟩, he⟩ => TTied.effHandle i ir ic _ _ ks site hs hs₁ hr hc hn0 hnS hlen hdv he⟩

/-- BOXED-κ: `handle_n e with (h_ret, hs)`, the clauses at `clausesTyB S R d E`, each capturing
clause's `κ` boxed at `@d`; `@d` defined, every live slot `e` uses outliving it, and every
non-abortive answer type of the handled row outliving it. It reads the handled row.
`[spec §28]` -/
def rEffHandleB (ir ic : TInfo) {S : CRow} {E : List (CQual × CVTy × CVTy)} {n : UInt32}
    {A R : CVTy} {d : CLife} (kr kc : Nat) (ks : List BoCa.Fig16.LogRel.Core.ClauseKinds.HKind)
    (site : Option HSite)
    (hkr : T[kr]? = some (BoCa.Fig16.LogRel.Core.retTy S A R))
    (hkc : T[kc]? = some (BoCa.Fig16.LogRel.Core.clausesTyB S R d E)) (hn0 : n ≠ 0)
    (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : BoCa.Fig16.LogRel.Core.Row.divB (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) = false)
    (hwf : d.wf Δ = true)
    (hSd : ansOutlivesB Δ d (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) = true)
    (rM : Res Δ T (.comp (effOf (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) A)))
    (hso : usedSat (outlivesB Δ d) T rM.F.u = true)
    (h₁ : overlapOK T (oneL T kr) (oneL T kc) = true)
    (h₂ : overlapOK T (orL (oneL T kr) (oneL T kc)) rM.F.u = true) : Res Δ T (.comp (effOf S R)) :=
  ⟨.effHandleVB i (.comp (effOf S R)) S E BoCa.Fig16.LogRel.Core.finsNil n A R d
      (orL (oneL T kr) (oneL T kc)) ks site
      (TTied.hndPair ir ic (BoCa.Fig16.LogRel.Core.retTy S A R)
        (BoCa.Fig16.LogRel.Core.clausesTyB S R d E) kr kc (oneL T kr)) rM.t,
    (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) ∪ rM.sigs, rM.pins,
    (((Fam.var T kr _ hkr).split (Fam.var T kc _ hkc) h₁).split (rM.F.restrict (outlivesB Δ d) hso)
      h₂).map fun _ ⟨_, _, hs, ⟨_, _, hs₁, hr, hc⟩, he, ho⟩ =>
        TTied.effHandleB i ir ic _ _ ks site hs hs₁ hr hc hn0 hnS hlen hdv he
          ⟨defines_of_wf hwf, fun s hsm hl => outlivesB_sound Δ d s.ty (ho s hsm hl)⟩
          (ansOutlivesB_sound hSd)⟩

end

end Frontend.Check
