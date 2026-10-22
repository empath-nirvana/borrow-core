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

/-- A binding's source: its span and the names it binds. -/
abbrev atB (sp : Span) (bs : List String) : TInfo := { sp, binders := bs }

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

/-- The walk reads (`TExpr.walkGet`) of a walk's typed term, outside the walks inside it (to a
depth bound). -/
def walkGets : Nat → TExpr → Nat
  | 0, _ => 0
  | f + 1, t => match t with
    | .walkGet .. => 1
    | .walk .. => 0
    | t => (t.children.map fun (_, c) => walkGets f c).foldl (· + ·) 0

/-- A marked scheme's derived node over its checked term `r`, when `r`'s erasure is the scheme's
(`divLitB`, `walkB`, `selfCallB`, `lendCellB`): `none` otherwise. -/
def rMarked {j : Jdg} (k : Frontend.SchemeMark) (r : Res Δ T j) : Option (Res Δ T j) :=
  match k with
  | .litFn bs => rLitFn i bs r
  | .divLit op c =>
    if hb : divLitB op c r.t.erase = true then
      if hs : safeDivB op c = true then
        some ⟨.divLit i j op c r.t, r.sigs, r.pins, r.F.map fun _ h => TTied.divLit i hb hs h⟩
      else none
    else none
  | .walk m =>
    if hb : walkB r.t.erase = true then
      let read := walkReadB m r.t.erase && walkGets 4096 r.t == 1
      some ⟨.walk i j m read r.t, r.sigs, r.pins, r.F.map fun _ h => TTied.walk i m read hb (fun h => (Bool.and_eq_true _ _ ▸ h).1) h⟩
    else none
  | .walkGet m =>
    if hb : walkGetB m r.t.erase = true then
      some ⟨.walkGet i j m r.t, r.sigs, r.pins, r.F.map fun _ h => TTied.walkGet i m hb h⟩
    else none
  | .selfCall k n =>
    if hb : selfCallB r.t.erase = true then
      some ⟨.selfCall i j k n r.t, r.sigs, r.pins, r.F.map fun _ h => TTied.selfCall i k n hb h⟩
    else none
  | .lendCell m =>
    if hb : lendCellB r.t.erase = true then
      some ⟨.lendCell i j m r.t, r.sigs, r.pins, r.F.map fun _ h => TTied.lendCell i m hb h⟩
    else none

/-! ### Structural value rules -/

def rPair {A B : CVTy} (r₁ : Res Δ T (.val A)) (r₂ : Res Δ T (.val B))
    (h : overlapOK T r₁.F.u r₂.F.u = true) : Res Δ T (.val (.tensor A B)) :=
  ⟨.tensorI i (.val (.tensor A B)) A B (Masks.of r₁.F.u r₂.F.u) r₁.t r₂.t, r₁.sigs ∪ r₂.sigs,
    r₁.pins ++ r₂.pins,
    (r₁.F.split r₂.F h).map fun _ ⟨_, _, hs, hm, h₁, h₂⟩ => TTied.tensorI i _ hs hm.rel_of h₁ h₂⟩

def rInl {A : CVTy} (B : CVTy) (r : Res Δ T (.val A)) : Res Δ T (.val (.sum A B)) :=
  ⟨.sumI₁ i (.val (.sum A B)) A B r.t, r.sigs, r.pins, r.F.map fun _ h => TTied.sumI₁ i h⟩

def rInr (A : CVTy) {B : CVTy} (r : Res Δ T (.val B)) : Res Δ T (.val (.sum A B)) :=
  ⟨.sumI₂ i (.val (.sum A B)) A B r.t, r.sigs, r.pins, r.F.map fun _ h => TTied.sumI₂ i h⟩

/-- `thunk M`: the body under one dead slot. -/
def rThunkF {A : CVTy} (r : Res Δ (.unit :: T) (.comp (.ret A))) :
    Option (Res Δ T (.val (.thunk (.ret A)))) := do
  let F ← r.F.popDead
  pure ⟨.thunkF i (.val (.thunk (.ret A))) A r.t, r.sigs, r.pins, F.map fun _ h => TTied.thunkF i h⟩

/-- The variables of the η-thunk of codata (`nuEtaE`), when the term is one. -/
def nuEtaOf? : Expr → Option (Nat × Option Nat)
  | .lam (.case (.var 0) (.seq (.var 0) (.app (.app (.var f) (.var s)) _)) _) =>
    if 2 ≤ f && 2 ≤ s then some (f - 2, some (s - 2)) else none
  | .lam (.case (.var 0) (.seq (.var 0) (.app (.lam (.app (.app (.var 0) (.var s)) _)) (.var f))) _) =>
    if 2 ≤ f && 3 ≤ s then some (f - 2, some (s - 3)) else none
  | .lam (.case (.var 0) (.seq (.var 0) (.app (.lam (.app (.var 0) _)) (.var f))) _) =>
    if 2 ≤ f then some (f - 2, none) else none
  | .lam (.case (.var 0) (.seq (.var 0) (.app (.var f) _)) _) =>
    if 2 ≤ f then some (f - 2, none) else none
  | _ => none

/-- The η-thunk of codata as its derived node (SPEC §45), when the thunk's erasure is the scheme. -/
def rNuEta {C : CCTy} (r : Res Δ T (.val (.thunk C))) : Res Δ T (.val (.thunk C)) :=
  if C matches .nu _ then
    match nuEtaOf? r.t.erase with
    | some (f, s) =>
      if hb : nuEtaB f s r.t.erase = true then
        ⟨.nuEta i (.val (.thunk C)) f s r.t, r.sigs, r.pins, r.F.map fun _ h => TTied.nuEta i f s hb h⟩
      else r
    | none => r
  else r

/-- `thunkv N`: `N` erases to a λ; the η-thunk of codata is its derived node (`rNuEta`). -/
def rThunkV {C : CCTy} (hC : C.isRet = false) (r : Res Δ T (.comp C)) :
    Option (Res Δ T (.val (.thunk C))) :=
  if hl : r.t.isLam = true then
    some (rNuEta i ⟨.thunkV i (.val (.thunk C)) C r.t, r.sigs, r.pins, r.F.map fun _ h =>
      have ⟨_, q⟩ := TExpr.isLam_sound _ hl
      TTied.thunkV i hC h q⟩)
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
  ⟨.lolliE i (.val B) A B (Masks.of ra.F.u rf.F.u) ra.t rf.t, ra.sigs ∪ rf.sigs, ra.pins ++ rf.pins,
    (ra.F.split rf.F h).map fun _ ⟨_, _, hs, hm, ha, hf⟩ => TTied.lolliE i _ hs hm.rel_of ha hf⟩

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
  ⟨.bind i (.comp C) A C (Masks.of rM.F.u FN.u) rM.t tN, rM.sigs ∪ sN, rM.pins ++ pN,
    (rM.F.split FN h).map fun _ ⟨_, _, hs, hm, h₁, h₂⟩ => TTied.bind i _ hs hm.rel_of h₁ h₂⟩

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
  ⟨.app i (.comp C) k A C (Masks.of rM.F.u (oneL T k)) rM.t, rM.sigs, rM.pins,
    (rM.F.split (Fam.var T k A hk) h).map fun _ ⟨_, _, hs, hm, h₁, h₂⟩ =>
      TTied.app i _ hs hm.rel_of h₁ h₂⟩

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
  ⟨.unitE i (.comp C) C (Masks.of rV.F.u rM.F.u) rV.t rM.t, rV.sigs ∪ rM.sigs, rV.pins ++ rM.pins,
    (rV.F.split rM.F h).map fun _ ⟨_, _, hs, hm, h₁, h₂⟩ => TTied.unitE i _ hs hm.rel_of h₁ h₂⟩

def rTensorE {A B : CVTy} {C : CCTy} {tM : TExpr} {sM : CRow} {pM : Pins}
    (rV : Res Δ T (.val (.tensor A B)))
    (FM : Fam T (fun L => TTied pM sM Δ (mkCtx (B :: A :: T) (true :: true :: L)) tM (.comp C)))
    (h : overlapOK T rV.F.u FM.u = true) : Res Δ T (.comp C) :=
  ⟨.tensorE i (.comp C) A B C (Masks.of rV.F.u FM.u) rV.t tM, rV.sigs ∪ sM, rV.pins ++ pM,
    (rV.F.split FM h).map fun _ ⟨_, _, hs, hm, h₁, h₂⟩ => TTied.tensorE i _ hs hm.rel_of h₁ h₂⟩

def rSumE {A B : CVTy} {C : CCTy} {t₁ t₂ : TExpr} {s₁ s₂ : CRow} {p₁ p₂ : Pins}
    (rV : Res Δ T (.val (.sum A B)))
    (F : Fam T (fun L => TTied p₁ s₁ Δ (mkCtx (A :: T) (true :: L)) t₁ (.comp C) ∧
      TTied p₂ s₂ Δ (mkCtx (B :: T) (true :: L)) t₂ (.comp C)))
    (h : overlapOK T rV.F.u F.u = true) : Res Δ T (.comp C) :=
  ⟨.sumE i (.comp C) A B C (Masks.of rV.F.u F.u) rV.t t₁ t₂, rV.sigs ∪ (s₁ ∪ s₂), rV.pins ++ (p₁ ++ p₂),
    (rV.F.split F h).map fun _ ⟨_, _, hs, hm, h₁, h₂, h₃⟩ => TTied.sumE i _ hs hm.rel_of h₁ h₂ h₃⟩

/-- `dtorE A xᵢ; M`: the destructor of slot `k` before `M`, which does not use it (SPEC §12).
`TTied.drop`, as `drop_derives`: `unitE` over `lolliE` of the variable and the destructor. The
variable's node has the source `ix`. -/
def rDrop (ix : TInfo) {C : CCTy} (k : Nat) (A : CVTy) (hk : T[k]? = some A) (hA : HasDtor A)
    (hc : BoCa.Fig16.LogRel.Core.closedAt 0 (dtorE A) = true) (hE : (dtorE A).effFree = true)
    (r : Res Δ T (.comp C))
    (h : overlapOK T (oneL T k) r.F.u = true) : Res Δ T (.comp C) :=
  ⟨.unitE i (.comp C) C (Masks.of (oneL T k) r.F.u)
      (.lolliE ix (.val .unit) A .unit (Masks.of (oneL T k) (noUse (oneL T k))) (.var ix (.val A) k A)
        (.dtor ix (.val (.lolli A .unit)) A)) r.t,
    r.sigs, r.pins, ((Fam.var T k A hk).split r.F h).map fun _ ⟨_, _, hs, hm, hx, hM⟩ =>
      TTied.drop i ix (oneL T k) r.F.u hs hm hx hA hc hE hM⟩

/-- `absurd V`: the rest of the context is absorbed. -/
def rZeroE (C : CCTy) (rV : Res Δ T (.val .zero)) (h : overlapOK T rV.F.u (Fam.top T).u = true) :
    Res Δ T (.comp C) :=
  ⟨.zeroE i (.comp C) C (Masks.of rV.F.u (Fam.top T).u) rV.t, rV.sigs, rV.pins,
    (rV.F.split (Fam.top T) h).map fun _ ⟨_, _, hs, hm, h₁, _⟩ => TTied.zeroE i _ hs hm.rel_of h₁⟩

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
  ⟨.effLet i (.comp (effOf S B)) A B S (Masks.of rM.F.u FN.u) rM.t tN, rM.sigs ∪ sN, rM.pins ++ pN,
    (rM.F.split FN h).map fun _ ⟨_, _, hs, hm, h₁, h₂, hW, hU⟩ => TTied.effLet i _ hs hm.rel_of hW hU h₁ h₂⟩

/-- `[then]`: `M then x. N unwind D`, `N` and the finaliser `D` at one context. -/
def rEffThen {S : CRow} {A B : CVTy} {tN tD : TExpr} {sN sD : CRow} {pN pD : Pins} (hNZ : S.NZ)
    (hUq : S.Uniq) (rM : Res Δ T (.comp (effOf S A)))
    (F : Fam T (fun L => (TTied pN sN Δ (mkCtx (A :: T) (true :: L)) tN (.comp (effOf S B)) ∧
      TTied pD sD Δ (mkCtx (.unit :: T) (false :: L)) tD
        (.comp (effOf [] .unit))) ∧
      (S.UnrD → Persistent (mkCtx T L))))
    (h : overlapOK T rM.F.u F.u = true) : Res Δ T (.comp (effOf S B)) :=
  ⟨.effThen i (.comp (effOf S B)) A B S S [] (Masks.of rM.F.u F.u) rM.t tN tD, rM.sigs ∪ (sN ∪ sD),
    rM.pins ++ (pN ++ pD), (rM.F.split F h).map
    fun _ ⟨_, _, hs, hm, h₁, ⟨hN, hD⟩, hU⟩ => TTied.effThenA i _ hs hm.rel_of hNZ hUq hU h₁ hN hD⟩

/-! ### `[handle]`  `[spec §19]` -/

/-- The erasure `e` is a value form whose variables are slots of `u`. -/
def valFormB (u : List Bool) : CExpr → Bool
  | .var k => u[k]? == some true
  | .unit | .lam _ | .loc _ | .prim _ => true
  | .pair a b => valFormB u a && valFormB u b
  | .inj₁ a => valFormB u a
  | .inj₂ a => valFormB u a
  | _ => false

theorem btw_subL : ∀ {u w L : List Bool}, Btw u w L → subL u L = true
  | [], [], [], .nil => rfl
  | _ :: _, _ :: _, _ :: _, .cons h₁ _ h => by
      rename_i a _ _ l _ _
      simp only [BoCa.Fig16.LogRel.Core.Check.subL, Bool.and_eq_true]
      exact ⟨by cases a <;> cases l <;> simp_all, btw_subL h⟩

theorem mkCtx_live_of_subL : ∀ {T : List CVTy} {u L : List Bool} {k : Nat},
    u.length = T.length → L.length = T.length → subL u L = true → u[k]? = some true →
    ∃ s, (mkCtx T L)[k]? = some s ∧ s.live = true
  | A :: T, a :: u, l :: L, 0, _, _, hs, hk => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      simp only [BoCa.Fig16.LogRel.Core.Check.subL, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hs
      exact ⟨⟨A, l⟩, rfl, hs.1⟩
  | A :: T, a :: u, l :: L, k + 1, hu, hL, hs, hk => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hu hL
      simp only [BoCa.Fig16.LogRel.Core.Check.subL, Bool.and_eq_true] at hs
      simpa [mkCtx] using mkCtx_live_of_subL hu hL hs.2 (by simpa using hk)
  | [], [], _, _, _, _, _, hk => by simp at hk
  | [], _ :: _, _, _, hu, _, _, _ => by simp at hu
  | _ :: _, [], _, _, hu, _, _, _ => by simp at hu
  | _ :: _, _ :: _, [], _, _, hL, _, _ => by simp at hL

theorem valFormB_sound {T : List CVTy} {u L : List Bool} (hu : u.length = T.length)
    (hL : L.length = T.length) (hs : subL u L = true) :
    ∀ {e : CExpr}, valFormB u e = true → e.ValFormIn (mkCtx T L)
  | .var k, h => by
      simp only [valFormB, beq_iff_eq] at h
      obtain ⟨_, hk, hl⟩ := mkCtx_live_of_subL hu hL hs h
      exact .var hk hl
  | .unit, _ => .val ⟨_, .unit⟩
  | .lam _, _ => .val ⟨_, .lam⟩
  | .loc _, _ => .val ⟨_, .loc⟩
  | .prim _, _ => .val ⟨_, .prim⟩
  | .pair a b, h => by
      simp only [valFormB, Bool.and_eq_true] at h
      exact .pair (valFormB_sound hu hL hs h.1) (valFormB_sound hu hL hs h.2)
  | .inj₁ a, h => .inj₁ (valFormB_sound hu hL hs (by simpa [valFormB] using h))
  | .inj₂ a, h => .inj₂ (valFormB_sound hu hL hs (by simpa [valFormB] using h))
  | .app _ _, h | .letpair _ _, h | .seq _ _, h | .case _ _ _, h => by simp [valFormB] at h

/-- A context whose live slots are persistent is consumed up to them. -/
theorem deadP_of_live : ∀ {Γ : Ctx CVTy}, (∀ s ∈ Γ, s.live = true → s.ty.persistent = true) →
    BoCa.Fig16.LogRel.Core.Ctx.DeadP Γ
  | [], _ => .nil
  | ⟨_, false⟩ :: _, h => .cons (deadP_of_live fun s hs => h s (List.mem_cons_of_mem _ hs))
  | ⟨_, true⟩ :: _, h =>
      .drop (h _ List.mem_cons_self rfl) (deadP_of_live fun s hs => h s (List.mem_cons_of_mem _ hs))

/-- The family, with each liveness it holds at using the slots `u`. -/
def _root_.BoCa.Fig16.LogRel.Core.Check.Fam.withUse {P : List Bool → Prop} (F : Fam T P) :
    Fam T (fun L => P L ∧ subL F.u L = true ∧ L.length = T.length) :=
  ⟨F.u, F.w, F.hu, F.hw, fun L hb => ⟨F.d L hb, btw_subL hb, hb.length.trans F.hu⟩⟩

/-- **`[handle]`**: `handle_n e with H`, the handler's pair `H` checked (`rH`), its erasure a
value form over the slots it uses (`hv`), each of which is persistent (`hp`). It reads the handled
row. The node records the clause kinds `ks` and the site `site`. -/
def rEffHandle {S : CRow} {E : List (CQual × CVTy × CVTy)} {n : UInt32} {A R Tr Tc : CVTy}
    (ks : List BoCa.Fig16.LogRel.Core.ClauseKinds.HKind) (site : Option HSite)
    (hr : BoCa.Fig16.LogRel.Core.retTy S A R = Tr) (hc : BoCa.Fig16.LogRel.Core.clausesTy S R E = Tc)
    (rH : Res Δ T (.val (.tensor Tr Tc)))
    (hp : usedSat BoCa.Fig16.LogRel.Core.VTy.persistent T rH.F.u = true) (hv : valFormB rH.F.u rH.t.erase = true)
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : BoCa.Fig16.LogRel.Core.Row.divB (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) = false)
    (rM : Res Δ T (.comp (effOf (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) A)))
    (h : overlapOK T rH.F.u rM.F.u = true) : Res Δ T (.comp (effOf S R)) :=
  ⟨.effHandleV i (.comp (effOf S R)) S E BoCa.Fig16.LogRel.Core.finsNil n A R (Masks.of rH.F.u rM.F.u) ks site
      rM.t.erase.hin rH.t rM.t,
    (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) ∪ (rH.sigs ∪ rM.sigs), rH.pins ++ rM.pins,
    ((rH.F.restrict BoCa.Fig16.LogRel.Core.VTy.persistent hp).withUse.split rM.F h).map
      fun _ ⟨_, _, hs, hm, ⟨⟨hH, hl⟩, hsub, hlen'⟩, he⟩ => by
        subst hr hc
        exact TTied.effHandle i _ ks site hs hm.rel_of (deadP_of_live hl)
          (valFormB_sound rH.F.hu hlen' hsub hv) hH hn0 hnS hlen hdv he⟩

/-- BOXED-κ: `[handle]` at the clauses `clausesTyB S R d E`, each capturing clause's `κ` boxed at
`@d`; `@d` defined, every live slot `e` uses outliving it, and every non-abortive answer type of
the handled row outliving it. It reads the handled row.  `[spec §28]` -/
def rEffHandleB {S : CRow} {E : List (CQual × CVTy × CVTy)} {n : UInt32} {A R Tr Tc : CVTy}
    {d : CLife} (ks : List BoCa.Fig16.LogRel.Core.ClauseKinds.HKind) (site : Option HSite)
    (hr : BoCa.Fig16.LogRel.Core.retTy S A R = Tr)
    (hc : BoCa.Fig16.LogRel.Core.clausesTyB S R d E = Tc) (rH : Res Δ T (.val (.tensor Tr Tc)))
    (hp : usedSat BoCa.Fig16.LogRel.Core.VTy.persistent T rH.F.u = true) (hv : valFormB rH.F.u rH.t.erase = true)
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : BoCa.Fig16.LogRel.Core.Row.divB (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) = false)
    (hwf : d.wf Δ = true)
    (hSd : ansOutlivesB Δ d (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) = true)
    (rM : Res Δ T (.comp (effOf (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) A)))
    (hso : usedSat (outlivesB Δ d) T rM.F.u = true)
    (h : overlapOK T rH.F.u rM.F.u = true) : Res Δ T (.comp (effOf S R)) :=
  ⟨.effHandleVB i (.comp (effOf S R)) S E BoCa.Fig16.LogRel.Core.finsNil n A R d (Masks.of rH.F.u rM.F.u) ks site
      rM.t.erase.hin rH.t rM.t,
    (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) ∪ (rH.sigs ∪ rM.sigs), rH.pins ++ rM.pins,
    ((rH.F.restrict BoCa.Fig16.LogRel.Core.VTy.persistent hp).withUse.split (rM.F.restrict (outlivesB Δ d) hso) h).map
      fun _ ⟨_, _, hs, hm, ⟨⟨hH, hl⟩, hsub, hlen'⟩, he, ho⟩ => by
        subst hr hc
        exact TTied.effHandleB i _ ks site hs hm.rel_of (deadP_of_live hl)
          (valFormB_sound rH.F.hu hlen' hsub hv) hH hn0 hnS hlen hdv he
          ⟨defines_of_wf hwf, fun s hsm hl => outlivesB_sound Δ d s.ty (ho s hsm hl)⟩
          (ansOutlivesB_sound hSd)⟩

/-- A value form that is a pair has value forms for its components. -/
theorem valFormIn_pair {Γ : Ctx CVTy} {a b : BoCa.Expr}
    (h : (BoCa.Expr.pair a b).ValFormIn Γ) : a.ValFormIn Γ ∧ b.ValFormIn Γ := by
  generalize he : BoCa.Expr.pair a b = e at h
  cases h with
  | pair ha hb => cases he; exact ⟨ha, hb⟩
  | val v =>
      obtain ⟨e', hv⟩ := v
      change BoCa.Expr.pair a b = e' at he
      subst he
      cases hv with
      | pair h₁ h₂ => exact ⟨.val ⟨a, h₁⟩, .val ⟨b, h₂⟩⟩
  | var => cases he
  | inj₁ => cases he
  | inj₂ => cases he

/-- **`[handle]` at clauses written by the tail-resuming rule** (`handle_tail`, `effHandleT`):
`h_ret` (`rr`) and the answering functions' tuple (`rc`), checked as a pair whose erasure is a
value form over persistent slots; `Σ_N ≤ Σ` of linear operations (`hSN`, `hLin`); `n` not `Div`.
It reads the handled row, which may hold `Div`.  `[spec §14, §54]` -/
def rEffHandleT {S SN : CRow} {E : List (CQual × CVTy × CVTy)} {n : UInt32} {A R : CVTy}
    (site : Option HSite) (rr : Res Δ T (.val (BoCa.Fig16.LogRel.Core.retTy S A R)))
    (rc : Res Δ T (.val (BoCa.Fig16.LogRel.Core.ansesTy S SN R E)))
    (hov : overlapOK T rr.F.u rc.F.u = true)
    (hp : usedSat BoCa.Fig16.LogRel.Core.VTy.persistent T (rPair i rr rc hov).F.u = true)
    (hv : valFormB (rPair i rr rc hov).F.u (rPair i rr rc hov).t.erase = true)
    (hn0 : n ≠ 0) (hnd : n ≠ BoCa.divEff) (hnS : ∀ o ∈ S, o.n ≠ n)
    (hlen : E.length ≤ 2 ^ 32) (hSN : rowLeB SN S = true)
    (hLin : ∀ o ∈ SN, o.q = .lin ∧ o.abort = false)
    (rM : Res Δ T (.comp (effOf (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) A)))
    (h : overlapOK T (rPair i rr rc hov).F.u rM.F.u = true) : Res Δ T (.comp (effOf S R)) :=
  let rH := rPair i rr rc hov
  ⟨.effHandleT i (.comp (effOf S R)) S SN E BoCa.Fig16.LogRel.Core.finsNil n A R
      (Masks.of rH.F.u rM.F.u) site rM.t.erase.hin rH.t rM.t,
    (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) ∪ (rH.sigs ∪ rM.sigs), rH.pins ++ rM.pins,
    ((rH.F.restrict BoCa.Fig16.LogRel.Core.VTy.persistent hp).withUse.split rM.F h).map
      fun _ ⟨_, _, hs, hm, ⟨⟨hH, hl⟩, hsub, hlen'⟩, he⟩ => by
        have hvf := valFormB_sound rH.F.hu hlen' hsub hv
        obtain ⟨hHr, hHc⟩ := valFormIn_pair (a := rr.t.erase) (b := rc.t.erase) hvf
        exact TTied.effHandleT i _ site hs hm.rel_of (deadP_of_live hl) hHr hHc hH rfl
            hn0 hnd hnS hlen (rowLeB_sound hSN) hLin he⟩

/-- **`[handle-last]`** (`handle_last`, `effHandleL`): `h_ret` (`rr`), the works' tuple (`rw`) and
the exits' tuple (`rn`), checked as the pair `(h_ret, (ws, nfs))` whose erasure is a value form
over persistent slots; the operations affine or abortive (`hAff`); `Σ_W ≤ Σ` (`hSW`, which gives
`LastFinOK` at the empty cancel rows, `lastFinOK_of_rowLeB`); `Σ.NZ`; `¬ Σ.UnrD` (`Row.unrDB`); `n`
not `Div`. It reads the handled row, which may hold `Div`.  `[spec §51, §54]` -/
def rEffHandleL {S SW : CRow} {E : List (CQual × CVTy × CVTy)} {Xs : Nat → CVTy} {n : UInt32}
    {A R : CVTy} (site : Option HSite) (rr : Res Δ T (.val (BoCa.Fig16.LogRel.Core.retTy S A R)))
    (rw : Res Δ T (.val (BoCa.Fig16.LogRel.Core.worksTy S SW R Xs E 0)))
    (rn : Res Δ T (.val (BoCa.Fig16.LogRel.Core.exitsTy S R Xs E 0)))
    (hov₁ : overlapOK T rw.F.u rn.F.u = true)
    (hov : overlapOK T rr.F.u (rPair i rw rn hov₁).F.u = true)
    (hp : usedSat BoCa.Fig16.LogRel.Core.VTy.persistent T
      (rPair i rr (rPair i rw rn hov₁) hov).F.u = true)
    (hv : valFormB (rPair i rr (rPair i rw rn hov₁) hov).F.u
      (rPair i rr (rPair i rw rn hov₁) hov).t.erase = true)
    (hn0 : n ≠ 0) (hnd : n ≠ BoCa.divEff) (hnS : ∀ o ∈ S, o.n ≠ n)
    (hlen : E.length ≤ 2 ^ 32) (hNZ : Row.nzB S = true)
    (hAff : ∀ o ∈ E, o.1 = .aff ∨ (o.2.2.isZero && o.1 != .lin) = true)
    (hSW : rowLeB SW S = true) (hSu : Row.unrDB S = false)
    (rM : Res Δ T (.comp (effOf (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) A)))
    (h : overlapOK T (rPair i rr (rPair i rw rn hov₁) hov).F.u rM.F.u = true) :
    Res Δ T (.comp (effOf S R)) :=
  let rH := rPair i rr (rPair i rw rn hov₁) hov
  ⟨.effHandleL i (.comp (effOf S R)) S SW E BoCa.Fig16.LogRel.Core.finsNil Xs n A R
      (Masks.of rH.F.u rM.F.u) site rM.t.erase.hin rH.t rM.t,
    (BoCa.Fig16.LogRel.Core.Row.ofEff n E 0 ++ S) ∪ (rH.sigs ∪ rM.sigs), rH.pins ++ rM.pins,
    ((rH.F.restrict BoCa.Fig16.LogRel.Core.VTy.persistent hp).withUse.split rM.F h).map
      fun _ ⟨_, _, hs, hm, ⟨⟨hH, hl⟩, hsub, hlen'⟩, he⟩ => by
        have hvf := valFormB_sound rH.F.hu hlen' hsub hv
        obtain ⟨hHr, hHwn⟩ := valFormIn_pair (a := rr.t.erase)
          (b := BoCa.Expr.pair rw.t.erase rn.t.erase) hvf
        obtain ⟨hHw, hHn⟩ := valFormIn_pair hHwn
        exact TTied.effHandleL i _ site hs hm.rel_of (deadP_of_live hl) hHr hHw hHn hH rfl
          hn0 hnd hnS hlen (Row.nzB_sound hNZ) hAff (rowLeB_sound hSW)
          (fun hU => absurd (Row.unrDB_iff.mpr hU) (by simp [hSu]))
          (fun _ _ => lastFinOK_of_rowLeB hSW _) he⟩

end

end Frontend.Check
