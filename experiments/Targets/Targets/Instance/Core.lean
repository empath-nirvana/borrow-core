import Targets.Instance.Typing
import Targets.A.Expressiveness
import Targets.Base.Machine

/-!
# The Instance — our calculus as one instance of A (RESTRUCTURE §4.1)

`ourInst RF Ξ J : A.EffectSystem` is Core at the row form `RF`, the effect context `Ξ` (which gives
each name its signature) and the typing system `J`.  Done asks A's properties at every admissible
`Ξ` (`AdmEff`: no resuming `unr` operation, operation types closed in lifetimes, and two names at
each signature the (E) programs use).

| A field | ours |
|---|---|
| `EA`, `sig`, `has` | `RF.alg Ξ`; `Ξ`'s signature of the label's name (`abortive` when `B = 0 ∧ q ≠ lin`, else `linear`/`affine` by `q`); `has ε l i` when the label's operation `i` is in the row's reading at every environment |
| `Ty`, `CTy`, `F`, data | the open types; `F ε A` the returner at the row's reading, `effF` |
| `DivFree` | the type's instances are returners at closed data (decision 35's reading) |
| `Val`, `Term` | expressions in value form, variables included (`OVal`), and expressions |
| formers | Core's: `lam` is `λ`, `force V` is `V` (every A-thunk is a function), `app M V` is `V to x. M x` (Core's `[app]` takes a variable), `bind` is `bindE`, `perform`/`raise` are `performE`/`raiseE` at the payload, at an index below `2³²` (beyond it, the stuck `opJunk`), `handle` is the run-time handler frame, its tags `Ξ`'s qualifiers of the name (`qsOf`), `resume k w` is `w to y. k (inj₁ ()) y`, `cancel k` is `k (inj₂ ())`, `thenT M N D` is `thenE N D↑ M` |
| `unfold A B f g s` | `unfoldV (loopEffBody [] A B)` at the coalgebra `λs. ⟨f s, g s⟩` and the state, stepped to its loop value `etaN` (`unfoldV`'s code is type-directed, so `unfold` carries the answer types); `next` is `nextE`, `close l` is `l (inj₂ ())` |
| `drive M`, `driveF` | the context `drive □`, a frame Core never steps (an applied literal); the driver's steps are `top` steps at the whole term (`RStep.again`, and the return to the main program at `inj₁ a`) |
| `Kont`, `plug`, `kcomp`, frames | Core's `Kont`, `Kont.plug`, `Kont.comp`; `bindF N` is `□ to x. N`, `appF V` is `□ V`, `handleF` the handler frame, `thenF` the `ubind` frame |
| `catches`, `unwindClear`, `fins` | `Kont.HasHnd`; no `ubind` and no `cfin` frame; `Kont.fins`, each read as an A-term |
| `capture`, `cancelOf` | `kappa`, `cancelOf` (base): the continuation of an unrestricted operation; at a linear or affine one the catch hands `kappaC` at a fresh cell (SPEC §25) |
| `Cell`, `captureAt`, `cellFree`, `withCell` | locations; `kappaC` at the location, affine at an affine class (SPEC §25); the memory holds nothing at the location; the memory with `()` at the location |
| `step` | `Step1` under every allocator, labelled `fire D` at `ufin`/`ufinC`, `finEnd` at `cfret`/`cferr`, `tau` otherwise; and the driver's `top` steps |
| `derV`, `der` | `J` at `Ξ` (`derAt`: its inner rows tied to `Ξ`, decision R), at the empty lifetime context and a row context declaring row variables at `any`, every slot live; a computation at a returner whose row is tied to `Ξ` (`OCTy.TiedAt`, decision D1); a driven program is typed at `[]` and a loop sum, its current step's type, the loop's row below the step's and its body positive (decision D2) |

**Builder's encodings** (RESTRUCTURE §Unresolved): A's values include variables and Core's `Val`
does not, so A's `Val` is `OVal`; `drive` is a marked context rather than a phase, so that a
finaliser frame keeps its finaliser exactly (`fins (thenF N D) = [D]`); `unfold` carries its answer
types.  Where an A-former is given a variable where Core needs a value (`appF`, `capture`,
`cancelOf`, `unfold`), it is read as a junk value: no configuration a typed closed program reaches
has one (`Live`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets.Inst
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE cfinE cancelVal
  kappa kappaC)
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open Targets (RVar RowEnv RowCon RowCtx RowForm EffCtx TypingJ OutJ Phase nextE orowRF RowClass
  RowAt rowAt_nil orowAlg ORow)

/-! ### The effect contexts done ranges over -/

/-- No resuming `unr` operation (decision 63): an `unr` operation is abortive. -/
def _root_.Targets.EffCtx.NU (Ξ : EffCtx) : Prop :=
  ∀ n q A B, (q, A, B) ∈ Ξ n → q = .unr → B.isZero = true

/-- Operation types closed in lifetimes (SPEC §19: "operation types are closed in lifetimes"). -/
def _root_.Targets.EffCtx.ClosedLife (Ξ : EffCtx) : Prop :=
  ∀ n q A B, (q, A, B) ∈ Ξ n → ∀ x, ¬ VFree x A ∧ ¬ VFree x B

/-- `bool`, as a Core type. -/
def boolT : VTy := .sum .unit .unit

/-- The signatures the (E) programs use, as Core signatures: `exn : 1 ↠ 0` (affine, so abortive),
`wait : 1 ↠ 1` affine, `yield : bool ↠ 1` affine, `log : bool ↠ 1` linear, `tick : 1 ↠ 1` linear,
`kube : 1 ↠ bool` linear. -/
def eSigs : List (List (Qual × VTy × VTy)) :=
  [[(.aff, .unit, .zero)], [(.aff, .unit, .unit)], [(.aff, boolT, .unit)], [(.lin, boolT, .unit)],
   [(.lin, .unit, .unit)], [(.lin, .unit, boolT)]]

/-- Two names at each signature the (E) programs use, so that each `ForLabels` has its labels. -/
def Rich (Ξ : EffCtx) : Prop :=
  ∀ E ∈ eSigs, ∃ n₁ n₂ : UInt32, n₁ ≠ n₂ ∧ n₁ ≠ 0 ∧ n₂ ≠ 0 ∧ Ξ n₁ = E ∧ Ξ n₂ = E

/-- **The effect contexts done ranges over.** -/
def AdmEff (Ξ : EffCtx) : Prop := Ξ.NU ∧ Ξ.ClosedLife ∧ Rich Ξ

/-- **A row tied to an effect context with no resuming `unr` operation is unr-free** (decision D6):
every operation the row finds is the context's, and the context's `unr` operations are abortive. -/
theorem rowNU_of_rowAt {Ξ : EffCtx} (hΞ : Ξ.NU) {S : Row} (h : RowAt Ξ S) : Row.NU S := by
  intro n i o hf
  obtain ⟨-, -, hget⟩ := h n i o hf
  by_cases hq : o.q = .unr
  · have hB := hΞ n o.q o.A o.B (List.mem_of_getElem? hget) hq
    exact Or.inl (by simp [OpSig.abort, hB, hq])
  · exact Or.inr hq

/-- **A well-formed row at an admissible effect context is unr-free** (decision D6): the
well-formedness of `orowAlg`, `Γ ⊢ ε : Eff`, ties the row's operations to `Ξ`. -/
theorem rowNU_of_wf {Ξ : EffCtx} (hΞ : AdmEff Ξ) {Γ : List RVar} {ε : ORow}
    (h : (orowAlg Ξ).WF Γ ε) : Row.NU ε.ops :=
  rowNU_of_rowAt hΞ.1 h.2

/-! ### Rows tied to the effect context (decision D1) -/

/-- A row environment whose rows are tied to the effect context. -/
def EnvAt (Ξ : EffCtx) (η : RowEnv) : Prop := ∀ ρ, RowAt Ξ (η ρ)

/-- The environment that reads every row variable as the empty row is tied to every context. -/
theorem envAt_nil (Ξ : EffCtx) : EnvAt Ξ (fun _ => []) := fun _ => rowAt_nil Ξ

theorem effOf_inj : ∀ {S S' : Row} {Y Y' : VTy}, CTy.effOf S Y = CTy.effOf S' Y' → S = S' ∧ Y = Y'
  | [], [], _, _, h => by simp only [CTy.effOf, CTy.ret.injEq] at h; exact ⟨rfl, h⟩
  | [], _ :: _, _, _, h => by simp [CTy.effOf] at h
  | _ :: _, [], _, _, h => by simp [CTy.effOf] at h
  | o :: S, o' :: S', _, _, h => by
      simp only [CTy.effOf, CTy.eff.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
      obtain ⟨rfl, rfl⟩ := effOf_inj h7
      cases o; cases o'
      simp_all

/-- **A computation type tied to the effect context** (decision D1): at every row environment tied
to `Ξ`, the type is a returner `F_S A` whose row `S` is tied to `Ξ`, every operation it finds a
label's at the signature `Ξ` declares.  A's computation types are its returners `F ε A`, and a
typed program at our instance is read at one of these. -/
def OCTy.TiedAt (Ξ : EffCtx) (C : OCTy) : Prop :=
  ∀ η, EnvAt Ξ η → ∃ (S : Row) (A : VTy), C.den η = CTy.effOf S A ∧ RowAt Ξ S

/-! ### Values, variables included -/

/-- Expressions in value form, variables included: A's values are open terms. -/
inductive IsOVal : Expr → Prop
  | var (i : ℕ) : IsOVal (.var i)
  | unit : IsOVal .unit
  | pair {a b : Expr} : IsOVal a → IsOVal b → IsOVal (.pair a b)
  | inj₁ {a : Expr} : IsOVal a → IsOVal (.inj₁ a)
  | inj₂ {a : Expr} : IsOVal a → IsOVal (.inj₂ a)
  | lam {b : Expr} : IsOVal (.lam b)
  | loc {ℓ : Loc} : IsOVal (.loc ℓ)
  | prim {p : Prim} : IsOVal (.prim p)
  | storeV {a : Expr} : IsOVal a → IsOVal (.app (.prim .store) a)

/-- A's values at our instance. -/
abbrev OVal := {e : Expr // IsOVal e}

theorem isOVal_of_isVal {e : Expr} (h : IsVal e) : IsOVal e := by
  induction h with
  | unit => exact .unit
  | pair _ _ ih₁ ih₂ => exact .pair ih₁ ih₂
  | inj₁ _ ih => exact .inj₁ ih
  | inj₂ _ ih => exact .inj₂ ih
  | lam => exact .lam
  | loc => exact .loc
  | prim => exact .prim
  | storeV _ ih => exact .storeV ih

/-- A Core value as an A-value. -/
def OVal.ofVal (v : Val) : OVal := ⟨v.1, isOVal_of_isVal v.2⟩

/-! ### The encodings -/

/-- The driver's mark: a literal, which Core never applies. -/
def driveMark : Expr := .prim (.lit (.u8 0))

/-- `drive M`: `M` under the driver's frame. -/
def driveE (M : Expr) : Expr := .app driveMark M

/-- The driver's frame. -/
def driveK : Kont := .appR driveMark .hole

/-- `M V`, A-normal: `V to x. M x`. -/
def appE (M V : Expr) : Expr := .app (.lam (.app (M.shift 1 0) (.var 0))) V

/-- `resume k w`, A-normal: `w to y. k (inj₁ ()) y`. -/
def resumeE (k w : Expr) : Expr := .app (.lam (.app (.app (k.shift 1 0) (.inj₁ .unit)) (.var 0))) w

/-- `cancel k`: `k (inj₂ ())`. -/
def cancelE (k : Expr) : Expr := .app k (.inj₂ .unit)

/-- The term an operation index beyond `UInt32` encodes to: the operation at an open payload,
stuck, and held by no closed configuration.  Reading every index through `UInt32.ofNat` would make
`i` and `i + 2³²` one operation, and a runner that keeps its protocol may answer the second with
anything (`Runner.Respects` constrains only the operations a label has). -/
def opJunk (r : Bool) : Expr := .app (.prim (if r then .raise else .perform)) (.var 0)

/-- A right-nested tuple of clauses. -/
def clausesE : List Expr → Expr
  | [] => .unit
  | c :: cs => .pair c (clausesE cs)

/-- The handler value `(n, (qs, (h_ret, hs)))`, as an expression. -/
def hndValE (n : UInt32) (qs r : Expr) (cs : List Expr) : Expr :=
  .pair (.prim (.lit (.i32 n))) (.pair qs (.pair r (clausesE cs)))

/-- The run-time handler frame `hnd (n, (qs, (h_ret, hs))) □`. -/
def handleK (n : UInt32) (qs r : Expr) (cs : List Expr) : Kont :=
  .appR (.app (.prim .hnd) (hndValE n qs r cs)) .hole

/-- The tags of the name `n`'s operations' qualifiers at `Ξ` (SPEC §25). -/
def qsOf (Ξ : EffCtx) (n : UInt32) : Expr := (qualsVal ((Ξ n).map Prod.fst)).1

/-- The finaliser frame `ubind (λx. N, λ_. D↑) □`. -/
def thenK (N D : Expr) : Kont := .appR (.app (.prim .ubind) (.pair (.lam N) (.lam (D.shift 1 0)))) .hole

/-- The bind frame `□ to x. N`. -/
def bindK (N : Expr) : Kont := .appR (.lam N) .hole

/-- A finaliser `λ_. D` of a `ubind` frame, read as the A-term `D` (its body at `()`). -/
def finE : Expr → Expr
  | .lam b => b.subst 0 Val.unit
  | e => .app e (.val .unit)

/-- `K` has no `ubind` and no `cfin` frame: no frame of it stops a raise of a label, other than a
handler of the label (`ccatch` stops only the reserved name `0`, which no label is). -/
def _root_.BoCa.BoLo.Kont.NoUnwind : Kont → Prop
  | .hole => True
  | .appR f K => (∀ x, f ≠ .app (.prim .ubind) x) ∧ (∀ s, f ≠ .app (.prim .cfin) s) ∧ K.NoUnwind
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .appL K _ | .seq K _ | .inj₁ K
  | .inj₂ K => K.NoUnwind

open Classical in
/-- `□ V`, at a value `V` (at a variable, which no configuration a typed closed program reaches
holds, the hole). -/
def appK (V : Expr) : Kont := if h : IsVal V then .appL .hole ⟨V, h⟩ else .hole

open Classical in
/-- The continuation `κ` a catch of an unrestricted operation hands its clause (`kappa`), at a
handler of values.  At a linear or affine operation the catch hands `kappaC` at a fresh cell
(SPEC §25), which no function of the handler and the context names. -/
def captureE (n : UInt32) (qs r : Expr) (cs : List Expr) (K : Kont) : Expr :=
  if h : IsVal (hndValE n qs r cs) then kappa ⟨_, h⟩ K else .unit

open Classical in
/-- `κ` at its cell `ℓ` (`kappaC`, SPEC §25), at a handler of values: affine when its cancel releases
the cell. -/
def captureAtE (aff : Bool) (ℓ : Loc) (n : UInt32) (qs r : Expr) (cs : List Expr) (K : Kont) :
    Expr :=
  if h : IsVal (hndValE n qs r cs) then kappaC aff ℓ ⟨_, h⟩ K else .unit

open Classical in
/-- The start of `κ`'s cancel run (`cancelOf`), at a handler of values. -/
def cancelOfE (n : UInt32) (qs r : Expr) (cs : List Expr) (K : Kont) : Expr :=
  if IsVal (hndValE n qs r cs) then Targets.cancelOf K else .unit

/-- The coalgebra `λs. ⟨f s, g s⟩` of a loop.  `withPair`'s arms sit under its two binders (the
selector and the branch's unit, Core's `withCtx`), so `s` is `var 2` there and `f`, `g` are shifted
past three binders, as Core's `loopStep` (`Core/DelayPrograms.lean`) writes its arms. -/
def coalgE (f g : Expr) : Expr :=
  .lam (withPair (appE (f.shift 3 0) (.var 2)) (appE (g.shift 3 0) (.var 2)))

open Classical in
/-- The loop value of `unfold A B f g s`: `unfoldV (loopEffBody [] A B)`'s codata at the
coalgebra `λs. ⟨f s, g s⟩` and the state (`etaN`), at values. -/
def unfoldE (A B : VTy) (f g s : Expr) : Expr :=
  if h : IsVal (coalgE f g) ∧ IsVal s then
    (etaN (CTy.loopEffBody [] A B) ⟨coalgE f g, h.1⟩ ⟨s, h.2⟩).1
  else .unit

/-! ### The labelled machine -/

section
variable (RF : RowForm) (Ξ : EffCtx)

open Classical in
/-- The error a `[cfin-raise]` step ends with, at a label of the name. -/
def errOf (m j : UInt32) (w : Val) : Option ((RF.alg Ξ).Lab × ℕ × OVal) :=
  if h : ∃ l, RF.name Ξ l = m then some (Classical.choose h, j.toNat, OVal.ofVal w) else none

open Classical in
/-- The error a cancel keeps, read at the labels: the kept raise's label, operation and argument. -/
def keptErrOf : Option Val → Option ((RF.alg Ξ).Lab × ℕ × OVal)
  | none => none
  | some E => if h : ∃ (m j : UInt32) (w : Val), E = opPayload m j w then
      errOf RF Ξ (Classical.choose h) (Classical.choose (Classical.choose_spec h))
        (Classical.choose (Classical.choose_spec (Classical.choose_spec h)))
    else none

open Classical in
/-- **The label of a head step**: `fire D` at a `ubind` frame stopped by a raise (`[finalise]`,
`[finalise-cancel]`), `finEnd` at a `cfin` frame whose finaliser returned, raised, or was passed by
a nested cancel (`[cfin-ret]`, `[cfin-raise]`, `[cfin-cancel]`: the nested cancel's kept error),
`tau` otherwise. -/
def labelOf (a : Expr) : A.Ev (RF.alg Ξ).Lab OVal Expr :=
  if h : ∃ (N D : Val) (e : Expr), a = ubindE (Val.pair N D) e ∧ ¬ IsVal e then
    .fire (finE (Classical.choose (Classical.choose_spec h)).1)
  else if ∃ (s w : Val), a = cfinE s (.val w) then .finEnd none
  else if h : ∃ (s : Val) (K : Kont) (err : Option Val),
      a = cfinE s (K.plug (raiseE (.val (cancelVal err)))) then
    .finEnd (keptErrOf RF Ξ (Classical.choose (Classical.choose_spec (Classical.choose_spec h))))
  else if h : ∃ (s : Val) (K : Kont) (m j : UInt32) (w : Val),
      a = cfinE s (K.plug (raiseE (.val (opPayload m j w)))) then
    .finEnd (errOf RF Ξ (Classical.choose (Classical.choose_spec (Classical.choose_spec h)))
      (Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec h))))
      (Classical.choose (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
        (Classical.choose_spec h))))))
  else .tau

/-- **Our machine, labelled**: `Step1` under every allocator, labelled by its head step, and the
driver's `top` steps at the whole term. -/
inductive OStep : Heap × Expr → A.Ev (RF.alg Ξ).Lab OVal Expr → Heap × Expr → Prop
  | mach {μ μ' : Heap} {K : Kont} {a a' : Expr} :
      Head (ℍ := ℍ) μ a μ' a' → OStep (μ, K.plug a) (labelOf RF Ξ a) (μ', K.plug a')
  | again {μ : Heap} {l : Val} :
      OStep (μ, driveE (.val (Val.inj₂ l))) .top (μ, driveE (nextE l))
  | fin {μ : Heap} {a : Val} :
      OStep (μ, driveE (.val (Val.inj₁ a))) .top (μ, .val a)

end

/-! ### The instance -/

/-- The class of an operation of signature `(q, A, B)`. -/
def clsOf (q : Qual) (B : VTy) : A.OpClass :=
  if B.isZero && q != .lin then .abortive else if q = .lin then .linear else .affine

/-- The constraint every row variable of an instance's judgement carries. -/
def anyCon : RowCon := ⟨.any, fun _ => True⟩

/-- A computation type whose instances are loop sums `F_S (A ⊕ U(Loop_S₀ A 1))`, the loop's row
`S₀` below the step's row `S` (`[sub]` weakens the step's row, not the loop's), and the loop's body
positive: `νX. C` is well formed at a positive `C` (`CTy.NuOk`, decision D2). -/
def IsLoopSum (C : OCTy) : Prop :=
  ∀ η, ∃ (S S₀ : Row) (A₀ : VTy), RowLe S₀ S ∧ (CTy.loopEffBody S₀ A₀ .unit).NuOk ∧
    C.den η = CTy.effOf S (.sum A₀ (.thunk (CTy.loopEff S₀ A₀ .unit)))

/-- Every slot live. -/
def liveCtx (Γ : List OVTy) : Ctx OVTy := Γ.map fun A => ⟨A, true⟩

/-- **Our calculus as an effect system**, at the row form `RF`, the effect context `Ξ` and the
typing system `J`. -/
def ourInst (RF : RowForm) (Ξ : EffCtx) (J : OurTyping RF) : A.EffectSystem where
  EA := RF.alg Ξ
  Ty := OVTy
  CTy := OCTy
  sig l := (Ξ (RF.name Ξ l)).map fun p => ⟨OVTy.ofV p.2.1, OVTy.ofV p.2.2, clsOf p.1 p.2.2⟩
  has ε l i := i < 2 ^ 32 ∧ ∀ η, Targets.Row.Has (RF.den Ξ ε η) (RF.name Ξ l) (UInt32.ofNat i)
  UnitT := .unit
  ZeroT := .zero
  Tensor := .tensor
  Sum := .sum
  F ε A := .effF (fun η => RF.den Ξ ε (J.env Ξ η)) A
  DivFree C := ∀ η, ∃ (S : Row) (A₀ : VTy), C.den η = CTy.effOf S A₀ ∧ A₀.Data
  Val := OVal
  Term := Expr
  Hnd := OVal × List OVal
  Kont := Kont
  Conf := Heap × Expr
  var i := ⟨.var i, .var i⟩
  unitV := ⟨.unit, .unit⟩
  pair a b := ⟨.pair a.1 b.1, .pair a.2 b.2⟩
  inl a := ⟨.inj₁ a.1, .inj₁ a.2⟩
  inr a := ⟨.inj₂ a.1, .inj₂ a.2⟩
  lam M := ⟨.lam M, .lam⟩
  force V := V.1
  app M V := appE M V.1
  ret V := V.1
  bind M N := bindE M N
  split V M := .letpair V.1 M
  case V M₁ M₂ := .case V.1 M₁ M₂
  perform l i v := if i < 2 ^ 32 then performE (opArgE (RF.name Ξ l) (UInt32.ofNat i) v.1)
    else opJunk false
  raise l i v := if i < 2 ^ 32 then raiseE (opArgE (RF.name Ξ l) (UInt32.ofNat i) v.1)
    else opJunk true
  hnd r cs := (r, cs)
  handle l H M := (handleK (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1 (H.2.map Subtype.val)).plug M
  resume k w := resumeE k.1 w.1
  cancel k := cancelE k.1
  thenT M N D := (thenK N D).plug M
  unfold A B f g s := ⟨unfoldE (A.den fun _ => []) (B.den fun _ => []) f.1 g.1 s.1, by
    unfold unfoldE; split
    · exact isOVal_of_isVal (etaN _ _ _).2
    · exact .unit⟩
  next l := .app l.1 (.inj₁ .unit)
  close l := .app l.1 (.inj₂ .unit)
  drive M := driveE M
  hole := .hole
  kcomp := Kont.comp
  bindF := bindK
  appF V := appK V.1
  handleF l H := handleK (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1 (H.2.map Subtype.val)
  thenF := thenK
  driveF := driveK
  plug := Kont.plug
  catches K l := K.HasHnd (RF.name Ξ l)
  unwindClear K := K.NoUnwind
  fins K := K.fins.map finE
  capture l H K := ⟨captureE (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1 (H.2.map Subtype.val) K, by
    unfold captureE; split
    · unfold kappa; exact .lam
    · exact .unit⟩
  cancelOf l H K := cancelOfE (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l)) H.1.1 (H.2.map Subtype.val) K
  Cell := Loc
  captureAt k l H K ℓ := ⟨captureAtE (decide (k = .affine)) ℓ (RF.name Ξ l) (qsOf Ξ (RF.name Ξ l))
    H.1.1 (H.2.map Subtype.val) K, by
    unfold captureAtE; split
    · unfold kappaC; exact .lam
    · exact .unit⟩
  cellFree c ℓ := c.1 ℓ = none
  withCell c ℓ := (c.1.upd ℓ Val.unit, c.2)
  init e := (Adequacy.emptyMem, e)
  term c := c.2
  setT c t := (c.1, t)
  step := OStep (ℍ := ℍ) RF Ξ
  derV Γ V A := ∃ Θ : RowCtx, (∀ p ∈ Θ, p.2 = anyCon) ∧
    J.derAt Ξ Θ LifeCtx.empty (liveCtx Γ) V.1 (.val A)
  der Γ e C := C.TiedAt Ξ ∧
    ((∃ Θ : RowCtx, (∀ p ∈ Θ, p.2 = anyCon) ∧ J.derAt Ξ Θ LifeCtx.empty (liveCtx Γ) e (.comp C)) ∨
    (Γ = [] ∧ ∃ M, e = driveE M ∧ IsLoopSum C ∧
      ∃ Θ : RowCtx, (∀ p ∈ Θ, p.2 = anyCon) ∧ J.derAt Ξ Θ LifeCtx.empty [] M (.comp C)))

theorem perform_eq {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF} {l : (RF.alg Ξ).Lab} {i : ℕ}
    (v : OVal) (hi : i < 2 ^ 32) :
    (ourInst RF Ξ J).perform l i v = performE (opArgE (RF.name Ξ l) (UInt32.ofNat i) v.1) :=
  if_pos hi

theorem raise_eq {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF} {l : (RF.alg Ξ).Lab} {i : ℕ}
    (v : OVal) (hi : i < 2 ^ 32) :
    (ourInst RF Ξ J).raise l i v = raiseE (opArgE (RF.name Ξ l) (UInt32.ofNat i) v.1) :=
  if_pos hi

theorem perform_junk {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF} {l : (RF.alg Ξ).Lab} {i : ℕ}
    (v : OVal) (hi : ¬ i < 2 ^ 32) : (ourInst RF Ξ J).perform l i v = opJunk false :=
  if_neg hi

theorem raise_junk {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF} {l : (RF.alg Ξ).Lab} {i : ℕ}
    (v : OVal) (hi : ¬ i < 2 ^ 32) : (ourInst RF Ξ J).raise l i v = opJunk true :=
  if_neg hi

/-- The pure row's returner is tied to every effect context, at every typing system. -/
theorem tiedAt_unit {Ξ : EffCtx} (J : OurTyping orowRF) (A : OVTy) :
    ((ourInst orowRF Ξ J).F (orowAlg Ξ).unit A).TiedAt Ξ :=
  fun η _ => ⟨[] ++ [], A.den η, rfl, rowAt_nil Ξ⟩

/-- A data value of A's at our instance is a Core value. -/
theorem isVal_of_dataVal {RF : RowForm} {Ξ : EffCtx} {J : OurTyping RF} :
    ∀ {T : OVTy} {w : OVal}, (ourInst RF Ξ J).DataVal T w → IsVal w.1
  | _, _, .unit => .unit
  | _, _, .pair ha hb => .pair (isVal_of_dataVal ha) (isVal_of_dataVal hb)
  | _, _, .inl ha => .inj₁ (isVal_of_dataVal ha)
  | _, _, .inr hb => .inj₂ (isVal_of_dataVal hb)

end Targets.Inst

end
