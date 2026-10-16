import Core.Demonic
import Core.IntPrograms
import Core.DelayPrograms
import Core.Weaken

/-!
# Core — standard I/O  `[spec §11]`

The capabilities `stdin : Ref Input`, `stdout`, `stderr : Ref Output` and their operations are
externs: hypotheses of the end-to-end theorem, not rules.  This file gives their model and
proves that it meets their contracts.

* **Representation.** `Bytes = μX. 1 ⊕ (U8 ⊗ X)`.  The relation at `Bytes` is the model of
  `Input` (`vC_bytes`), and at `I32 ⊗ Bytes` the model of `Output` (`vC_outRep`): an opaque type
  is its representation with the rules taken away.
* **The model** is ordinary core terms at the representation: `read_byte` is `withswap` popping
  the head of the list, `write_byte` is `withswap` consing onto it, and the harness `mk_input`,
  `mk_output`, `take_input`, `take_output` is `alloc` and `free`.  Each is a `CDerives`
  derivation at the representation (`d_readByte`, …), so the Fundamental Property puts it in the
  relation there, and the relation at the extern's type is the same (`cC_readByteC`, …):
  `readByte_meets`, `writeByte_meets`, `mkInput_meets`, `mkOutput_meets`, `takeInput_meets`,
  `takeOutput_meets`.
* **Bulk transfer.** `write_all` and `read_into` move a byte view in one call; their models are
  counted loops of the byte operations' (`writeAll_meets`, `readInto_meets`).
* **End to end** (`externs_every_run`, `io_every_run`): a checked `run_io : Bytes ⊸ F R`, `R`
  persistent, at a context of externs met at `∅`, runs from the empty memory under every
  allocator; every run continues to a value at the empty memory.
* **No capability, no effect** (`wpTSD_frame_own`): a cell owned by the frame holds its value
  at the end of every value run.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### The representation -/

/-- `1 ⊕ (U8 ⊗ X)`. -/
def bytesBody : VTy := .sum .unit (.tensor (.int .w8) (.tvar 0))

/-- `Bytes = μX. 1 ⊕ (U8 ⊗ X)`: a byte list.  `[spec §11]` -/
def bytesTy : VTy := .mu bytesBody

/-- `I32 ⊗ Bytes`: an output stream's descriptor and the bytes written to it, the
representation of `Output`.  `[spec §11]` -/
def outRep : VTy := .tensor .i32 bytesTy

theorem bytesBody_noMut : bytesBody.NoMut 0 := ⟨trivial, trivial, trivial⟩

theorem bytesTy_closed : bytesTy.Cl 0 := ⟨trivial, trivial, Nat.zero_lt_one⟩

theorem bytes_unroll : VTy.inst bytesTy bytesBody = .sum .unit (.tensor (.int .w8) bytesTy) := rfl

/-- The relation at `Bytes` holds exactly at a byte list, at `∅`. -/
theorem vC_bytes_iff {b : Bool} {ls : List SRec} {δ : LSub} {v : Val} {ρ : WRes} :
    vC b bytesTy ls δ v ρ ↔ ρ = PMap.empty ∧ BytesV v := by
  constructor
  · intro h
    refine vC_mu_ind (A := bytesBody) (δ := δ) (fun _ _ v ρ => ρ = PMap.empty ∧ BytesV v) ?_
      b ls v ρ h
    rintro b ls v ρ - - (⟨v₁, hs⟩ | ⟨v₂, hs⟩)
    · obtain ⟨rfl, hρ, rfl⟩ := pure_sep_iff.mp hs
      exact ⟨hρ, .nil⟩
    · obtain ⟨rfl, hG⟩ := pure_sep_iff.mp hs
      obtain ⟨w₁, w₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ⟨hρ₁, n, rfl⟩, ⟨-, hρ₂, hB⟩⟩ := hG
      subst hρ₁; subst hρ₂
      rw [eq_empty_of_compS_empty hc'] at hc
      obtain ⟨rfl, rfl⟩ := hp
      exact ⟨eq_empty_of_compS_empty hc, .cons n hB⟩
  · rintro ⟨rfl, hB⟩
    induction hB with
    | nil =>
        refine vC_roll (A := bytesBody) bytesBody_noMut bytesTy_closed ?_
        show vC b (.sum .unit (.tensor (.int .w8) bytesTy)) ls δ _ _
        exact Or.inl ⟨.unit, pure_sep_iff.mpr ⟨rfl, rfl, rfl⟩⟩
    | cons n _ ih =>
        refine vC_roll (A := bytesBody) bytesBody_noMut bytesTy_closed ?_
        show vC b (.sum .unit (.tensor (.int .w8) bytesTy)) ls δ _ _
        refine Or.inr ⟨_, pure_sep_iff.mpr ⟨rfl, ?_⟩⟩
        exact ⟨_, _, PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, rfl⟩,
          PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, n, rfl⟩, ih⟩

/-- **`Input` is `Bytes` with the rules taken away**: the relation at `Bytes` is `Input`'s
model.  `[spec §11]` -/
theorem vC_bytes (b : Bool) (ls : List SRec) (δ : LSub) :
    vC b bytesTy ls δ = vC b (.opq .input) ls δ := by
  funext v ρ
  exact propext (vC_bytes_iff.trans ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩)

/-- **`Args` is `Bytes` with the rules taken away**, as `Input` is.  `[spec §34]` -/
theorem vC_argsRep (b : Bool) (ls : List SRec) (δ : LSub) :
    vC b bytesTy ls δ = vC b (.opq .args) ls δ := by
  funext v ρ
  exact propext (vC_bytes_iff.trans ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩)

/-- **`Output` is `I32 ⊗ Bytes` with the rules taken away.**  `[spec §11]` -/
theorem vC_outRep (b : Bool) (ls : List SRec) (δ : LSub) :
    vC b outRep ls δ = vC b (.opq .output) ls δ := by
  funext v ρ
  apply propext
  constructor
  · rintro ⟨w₁, w₂, ρ₀, ρ₃, hc, hp, ρ₁, ρ₂, hc', ⟨hρ₁, n, rfl⟩, h₂⟩
    obtain ⟨hρ₂, hB⟩ := vC_bytes_iff.mp h₂
    subst hρ₁; subst hρ₂
    rw [eq_empty_of_compS_empty hc'] at hc
    obtain ⟨rfl, rfl⟩ := hp
    exact ⟨eq_empty_of_compS_empty hc, n, w₂, rfl, hB⟩
  · rintro ⟨rfl, n, bs, rfl, hB⟩
    exact ⟨_, _, PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, rfl⟩,
      PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, n, rfl⟩,
      vC_bytes_iff.mpr ⟨rfl, hB⟩⟩

/-! ### The operations' types

Each extern's type is `!U C`, with `C` a function of the payload: the opaque type in the
extern, its representation in the model. -/

/-- `read_byte`: `∀'a ⊏ ⊤. F (Mut 'a I ⇒ Mut 'a I ⊗ (U8 ⊕ 1))`.  `[spec §11]` -/
def readByteC (I : VTy) : CTy :=
  .all 0 .top (.ret (.lolli (.mut (.var 0) I) (.tensor (.mut (.var 0) I) (.sum (.int .w8) .unit))))

/-- `write_byte`: `∀'a ⊏ ⊤. F (Mut 'a O ⊗ U8 ⇒ Mut 'a O)`.  `[spec §11]` -/
def writeByteC (O : VTy) : CTy :=
  .all 0 .top (.ret (.lolli (.tensor (.mut (.var 0) O) (.int .w8)) (.mut (.var 0) O)))

/-- `mk_input`: `Bytes ⊸ F (Ref I)`.  `[spec §11]` -/
def mkInputC (I : VTy) : CTy := .arr bytesTy (.ret (.ref I))

/-- `mk_output`: `I32 ⊸ F (Ref O)`.  `[spec §11]` -/
def mkOutputC (O : VTy) : CTy := .arr .i32 (.ret (.ref O))

/-- `take_input`: `Ref I ⊸ F Bytes`.  `[spec §11]` -/
def takeInputC (I : VTy) : CTy := .arr (.ref I) (.ret bytesTy)

/-- `take_output`: `Ref O ⊸ F (I32 ⊗ Bytes)`.  `[spec §11]` -/
def takeOutputC (O : VTy) : CTy := .arr (.ref O) (.ret outRep)

/-- An extern's type: `!U C`. -/
abbrev externTy (C : CTy) : VTy := .bang (.thunk C)

/-! ### The model -/

/-- `read_byte`'s callback: `λs. case s {inj₁ u. (inj₁ u, inj₂ ()) | inj₂ p. let (b, r) = p in
(r, inj₁ b)}`: the rest of the list and the head, or the empty list and end of input. -/
def rbCallback : Expr :=
  .val (.lam (.case (.var 0) (.pair (.inj₁ (.var 0)) (.inj₂ (.val .unit)))
    (.letpair (.var 0) (.pair (.var 0) (.inj₁ (.var 1))))))

/-- The model of `read_byte`: `Λ. λm. withswap m rbCallback`.  `[spec §11]` -/
def readByteV : Val := .lam (.val (.lam (.app (.app withswap (.var 0)) rbCallback)))

/-- `write_byte`'s callback at the byte `b` (index `1`): `λo. let (fd, bs) = o in
((fd, inj₂ (b, bs)), ())`. -/
def wbCallback : Expr :=
  .val (.lam (.letpair (.var 0)
    (.pair (.pair (.var 1) (.inj₂ (.pair (.var 3) (.var 0)))) (.val .unit))))

/-- The model of `write_byte`: `Λ. λp. let (m, b) = p in let (m', u) = withswap m wbCallback in
u; m'`.  `[spec §11]` -/
def writeByteV : Val :=
  .lam (.val (.lam (.letpair (.var 0)
    (.letpair (.app (.app withswap (.var 1)) wbCallback) (.seq (.var 0) (.var 1))))))

/-- The model of `mk_input`: `λbs. alloc bs`.  `[spec §11]` -/
def mkInputV : Val := .lam (.app (.val (.prim .alloc)) (.var 0))

/-- The model of `mk_output`: `λfd. alloc (fd, nil)`.  `[spec §11]` -/
def mkOutputV : Val := .lam (.app (.val (.prim .alloc)) (.pair (.var 0) (.inj₁ (.val .unit))))

/-- The model of `take_input` and `take_output`: `λc. free c`.  `[spec §11]` -/
def takeCapV : Val := .lam (.app (.val (.prim .free)) (.var 0))

/-! ### The model is typed at the representation -/

theorem d_readByte : CDerives LifeCtx.empty [] (.val readByteV) (.comp (readByteC bytesTy)) := by
  refine .allI (S := .unit) rfl (fun _ _ hy => LifeCtx.Ok.bound_mentions_false ok_empty rfl hy)
    (fun _ h => by cases h) (.ret (.lamV ?_))
  refine appP (A := .lolli bytesTy (.tensor bytesTy (.sum (.int .w8) .unit))) ?_ ?_
  · refine .lamV (caseP (A := .unit) (B := .tensor (.int .w8) bytesTy)
      (.unroll (A := bytesBody) (.var (by csoloP))) ?_ ?_)
    · exact pairP (.roll bytesBody_noMut bytesTy_closed (.sumI₁ (.var (by csoloP))))
        (.sumI₂ (.unitI (by cdeadP)))
    · exact letP (A := .int .w8) (B := bytesTy) (.var (by csoloP))
        (pairP (.var (by csoloP)) (.sumI₁ (.var (by csoloP))))
  · exact appP (A := .mut (.var 0) bytesTy) (.var (by csoloP)) (.withswap (by cdeadP))

theorem d_writeByte :
    CDerives LifeCtx.empty [] (.val writeByteV) (.comp (writeByteC outRep)) := by
  refine .allI (S := .unit) rfl (fun _ _ hy => LifeCtx.Ok.bound_mentions_false ok_empty rfl hy)
    (fun _ h => by cases h) (.ret (.lamV ?_))
  refine letP (A := .mut (.var 0) outRep) (B := .int .w8) (.var (by csoloP)) ?_
  refine letP (A := .mut (.var 0) outRep) (B := .unit) ?_
    (.seqV (partP_split (.var 0) 0 _) (.var (by csoloP)) (.var (by csoloP)))
  refine appP (A := .lolli outRep (.tensor outRep .unit)) ?_ ?_
  · exact .lamV (letP (A := .i32) (B := bytesTy) (.var (by csoloP))
      (pairP (pairP (.var (by csoloP)) (.roll bytesBody_noMut bytesTy_closed
        (.sumI₂ (pairP (.var (by csoloP)) (.var (by csoloP))))))
        (.unitI (by cdeadP))))
  · exact appP (A := .mut (.var 0) outRep) (.var (by csoloP)) (.withswap (by cdeadP))

theorem d_mkInput : CDerives LifeCtx.empty [] (.val mkInputV) (.comp (mkInputC bytesTy)) :=
  .lam (.ret (appP (.var (by csoloP)) (.alloc (by cdeadP))))

theorem d_mkOutput : CDerives LifeCtx.empty [] (.val mkOutputV) (.comp (mkOutputC outRep)) :=
  .lam (.ret (appP (pairP (.var (by csoloP))
    (.roll bytesBody_noMut bytesTy_closed (.sumI₁ (.unitI (by cdeadP))))) (.alloc (by cdeadP))))

theorem d_takeInput : CDerives LifeCtx.empty [] (.val takeCapV) (.comp (takeInputC bytesTy)) :=
  .lam (.ret (appP (.var (by csoloP)) (.free (by cdeadP))))

theorem d_takeOutput : CDerives LifeCtx.empty [] (.val takeCapV) (.comp (takeOutputC outRep)) :=
  .lam (.ret (appP (.var (by csoloP)) (.free (by cdeadP))))

/-! ### The model meets the contracts -/

/-- A closed `λ` typed at a computation type other than `F` is in the relation at `!U C`, at
`∅`: the Fundamental Property at the empty context. -/
theorem meets_of_derives {N : Expr} {C : CTy} (hC : C.isRet = false)
    (h : CDerives LifeCtx.empty [] (.val (.lam N)) (.comp C)) (ls : List SRec) (δ : LSub) :
    vC true (externTy C) ls δ (Val.lam N) PMap.empty := by
  refine ⟨rfl, fun ls' _ => ?_⟩
  have hs := fundamentalC h δ [] ls' PMap.empty (models_empty_any δ) (gDenC_nil _ _)
  rw [show substAll [] (Expr.val (Val.lam N)) = Expr.val (Val.lam N) from
    Adequacy.psub_nil 0 _] at hs
  rw [forceE_of_not_ret hC]
  exact hs

/-- The relation at `!U C` depends on `C` only through `cC C`. -/
theorem vC_externTy_congr {C₁ C₂ : CTy} (h₁ : C₁.isRet = false) (h₂ : C₂.isRet = false)
    (h : cC C₁ = cC C₂) : vC true (externTy C₁) = vC true (externTy C₂) := by
  funext ls δ v ρ
  simp only [vCE, forceE_of_not_ret h₁, forceE_of_not_ret h₂, h]

theorem cC_readByteC : cC (readByteC bytesTy) = cC (readByteC (.opq .input)) := by
  funext ls δ e ρ
  simp only [readByteC, cC, vCE, forceE, vC_bytes]

theorem cC_writeByteC : cC (writeByteC outRep) = cC (writeByteC (.opq .output)) := by
  funext ls δ e ρ
  simp only [writeByteC, cC, vCE, forceE, vC_outRep]

theorem cC_mkInputC : cC (mkInputC bytesTy) = cC (mkInputC (.opq .input)) := by
  funext ls δ e ρ
  simp only [mkInputC, cC, vCE, vC_bytes]

theorem cC_mkOutputC : cC (mkOutputC outRep) = cC (mkOutputC (.opq .output)) := by
  funext ls δ e ρ
  simp only [mkOutputC, cC, vCE, vC_outRep]

theorem cC_takeInputC : cC (takeInputC bytesTy) = cC (takeInputC (.opq .input)) := by
  funext ls δ e ρ
  simp only [takeInputC, cC, vCE, vC_bytes]

theorem cC_takeOutputC : cC (takeOutputC outRep) = cC (takeOutputC (.opq .output)) := by
  funext ls δ e ρ
  simp only [takeOutputC, cC, vCE, vC_outRep]

/-- **The model of `read_byte` meets its contract.**  `[spec §11]` -/
theorem readByte_meets (ls : List SRec) (δ : LSub) :
    vC true (externTy (readByteC (.opq .input))) ls δ readByteV PMap.empty := by
  rw [← vC_externTy_congr rfl rfl cC_readByteC]
  exact meets_of_derives rfl d_readByte ls δ

/-- **The model of `write_byte` meets its contract.**  `[spec §11]` -/
theorem writeByte_meets (ls : List SRec) (δ : LSub) :
    vC true (externTy (writeByteC (.opq .output))) ls δ writeByteV PMap.empty := by
  rw [← vC_externTy_congr rfl rfl cC_writeByteC]
  exact meets_of_derives rfl d_writeByte ls δ

/-- **The model of `mk_input` meets its contract.**  `[spec §11]` -/
theorem mkInput_meets (ls : List SRec) (δ : LSub) :
    vC true (externTy (mkInputC (.opq .input))) ls δ mkInputV PMap.empty := by
  rw [← vC_externTy_congr rfl rfl cC_mkInputC]
  exact meets_of_derives rfl d_mkInput ls δ

/-- **The model of `mk_output` meets its contract.**  `[spec §11]` -/
theorem mkOutput_meets (ls : List SRec) (δ : LSub) :
    vC true (externTy (mkOutputC (.opq .output))) ls δ mkOutputV PMap.empty := by
  rw [← vC_externTy_congr rfl rfl cC_mkOutputC]
  exact meets_of_derives rfl d_mkOutput ls δ

/-- **The model of `take_input` meets its contract.**  `[spec §11]` -/
theorem takeInput_meets (ls : List SRec) (δ : LSub) :
    vC true (externTy (takeInputC (.opq .input))) ls δ takeCapV PMap.empty := by
  rw [← vC_externTy_congr rfl rfl cC_takeInputC]
  exact meets_of_derives rfl d_takeInput ls δ

/-- **The model of `take_output` meets its contract.**  `[spec §11]` -/
theorem takeOutput_meets (ls : List SRec) (δ : LSub) :
    vC true (externTy (takeOutputC (.opq .output))) ls δ takeCapV PMap.empty := by
  rw [← vC_externTy_congr rfl rfl cC_takeOutputC]
  exact meets_of_derives rfl d_takeOutput ls δ

/-- Every slot to the left. -/
theorem splitP_left_all : ∀ Γ : Ctx VTy, Ctx.SplitP Γ Γ (kill Γ)
  | [] => .nil
  | ⟨_, true⟩ :: Γ => .left (splitP_left_all Γ)
  | ⟨_, false⟩ :: Γ => .dead (splitP_left_all Γ)

/-- Every slot to the right. -/
theorem splitP_right_all : ∀ Γ : Ctx VTy, Ctx.SplitP Γ (kill Γ) Γ
  | [] => .nil
  | ⟨_, true⟩ :: Γ => .right (splitP_right_all Γ)
  | ⟨_, false⟩ :: Γ => .dead (splitP_right_all Γ)

/-! ### Bulk transfer: `write_all` and `read_into`  `[spec §11]`

`write_all` writes every byte of an `imm` view to an output; `read_into` fills a `mut` view from
an input and answers the number of bytes read, which is less than the view's length only when the
input ended. Each model is a counted loop (`count_fold`, §16) of the byte operations' models, so
its contract is again the Fundamental Property at its type (`writeAll_meets`, `readInto_meets`).
The host implementation is one `fd_write` of the view, and `fd_read`s into it until it is full or
the input ends: one system call per view instead of one per byte. -/

/-- A byte. -/
abbrev u8T : VTy := .int .w8

/-- `write_all`: `∀'a ⊏ ⊤. F (∀'b ⊏ ⊤. Mut 'a O ⊗ [Imm 'b U8] ⇒ Mut 'a O)`.  `[spec §11]` -/
def writeAllC (O : VTy) : CTy :=
  .all 0 .top (.ret (.all 1 .top
    (.lolli (.tensor (.mut (.var 0) O) (.arrayImm (.var 1) u8T)) (.mut (.var 0) O))))

/-- `read_into`: `∀'a ⊏ ⊤. F (∀'b ⊏ ⊤. Mut 'a I ⊗ [Mut 'b U8] ⇒ Mut 'a I ⊗ ([Mut 'b U8] ⊗ I32))`.
`[spec §11]` -/
def readIntoC (I : VTy) : CTy :=
  .all 0 .top (.ret (.all 1 .top
    (.lolli (.tensor (.mut (.var 0) I) (.sliceMut (.var 1) u8T))
      (.tensor (.mut (.var 0) I) (.tensor (.sliceMut (.var 1) u8T) .i32)))))

/-- `write_byte`'s function under its `Λ`. -/
def wbFnV : Val :=
  .lam (.letpair (.var 0)
    (.letpair (.app (.app withswap (.var 1)) wbCallback) (.seq (.var 0) (.var 1))))

theorem writeByteV_eq : writeByteV = .lam (.val wbFnV) := rfl

/-- `read_byte`'s function under its `Λ`. -/
def rbFnV : Val := .lam (.app (.app withswap (.var 0)) rbCallback)

theorem readByteV_eq : readByteV = .lam (.val rbFnV) := rfl

theorem partP_deadP (e : Expr) : ∀ {i : Nat} {Γ : Ctx VTy}, Ctx.DeadP Γ →
    Ctx.DeadP (partP e i Γ).1 ∧ Ctx.DeadP (partP e i Γ).2
  | _, _, .nil => ⟨.nil, .nil⟩
  | i, _, .cons h => by
      simp only [partP, Bool.false_eq_true, if_false]
      exact ⟨.cons (partP_deadP e (i := i + 1) h).1, .cons (partP_deadP e (i := i + 1) h).2⟩
  | i, _, .drop hT h => by
      have hp : _ = true := hT
      simp only [partP, if_true, hp]
      exact ⟨.drop hT (partP_deadP e (i := i + 1) h).1, .drop hT (partP_deadP e (i := i + 1) h).2⟩

theorem part_deadP (e : Expr) : ∀ {i : Nat} {Γ : Ctx VTy}, Ctx.DeadP Γ →
    Ctx.DeadP (part e i Γ).1 ∧ Ctx.DeadP (part e i Γ).2
  | _, _, .nil => ⟨.nil, .nil⟩
  | i, _, .cons h => by
      simp only [part, Bool.false_eq_true, if_false]
      exact ⟨.cons (part_deadP e (i := i + 1) h).1, .cons (part_deadP e (i := i + 1) h).2⟩
  | i, _, .drop hT h => by
      simp only [part, if_true]
      split
      · exact ⟨.drop hT (part_deadP e (i := i + 1) h).1, .cons (part_deadP e (i := i + 1) h).2⟩
      · exact ⟨.cons (part_deadP e (i := i + 1) h).1, .drop hT (part_deadP e (i := i + 1) h).2⟩

/-- `Γ` consumed, up to live persistent slots, with `DeadP` hypotheses in scope. -/
syntax "cdeadQ" : tactic
macro_rules
  | `(tactic| cdeadQ) => `(tactic| first | assumption | exact Ctx.DeadP.nil | exact Ctx.Dead.toP (by assumption) | (refine Ctx.DeadP.cons ?_; cdeadQ) | (refine Ctx.DeadP.drop (by decide) ?_; cdeadQ) | exact (partP_deadP _ (by cdeadQ)).1 | exact (partP_deadP _ (by cdeadQ)).2 | exact (part_deadP _ (by cdeadQ)).1 | exact (part_deadP _ (by cdeadQ)).2)

/-- `Γ = x : A`, up to live persistent slots elsewhere, with `DeadP` hypotheses in scope. -/
syntax "csoloQ" : tactic
macro_rules
  | `(tactic| csoloQ) => `(tactic| first | (refine Ctx.SoloP.here ?_; cdeadQ) | (refine Ctx.SoloP.there ?_; csoloQ) | (refine Ctx.SoloP.skip (by decide) ?_; csoloQ))

theorem d_wbFn {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (hΓ : Ctx.DeadP Γ) :
    CDerives Δ Γ (.val wbFnV) (.val (.lolli (.tensor (.mut a outRep) u8T) (.mut a outRep))) := by
  refine .lamV ?_
  refine letP (A := .mut a outRep) (B := u8T) (.var (by csoloQ)) ?_
  refine letP (A := .mut a outRep) (B := .unit) ?_
    (.seqV (partP_split (.var 0) 0 _) (.var (by csoloQ)) (.var (by csoloQ)))
  refine appP (A := .lolli outRep (.tensor outRep .unit)) ?_ ?_
  · exact .lamV (letP (A := .i32) (B := bytesTy) (.var (by csoloQ))
      (pairP (pairP (.var (by csoloQ)) (.roll bytesBody_noMut bytesTy_closed
        (.sumI₂ (pairP (.var (by csoloQ)) (.var (by csoloQ))))))
        (.unitI (by cdeadQ))))
  · exact appP (A := .mut a outRep) (.var (by csoloQ)) (.withswap (by cdeadQ))

theorem d_rbFn {Δ : LifeCtx} {Γ : Ctx VTy} (a : Lifetime.Life) (hΓ : Ctx.DeadP Γ) :
    CDerives Δ Γ (.val rbFnV)
      (.val (.lolli (.mut a bytesTy) (.tensor (.mut a bytesTy) (.sum u8T .unit)))) := by
  refine .lamV ?_
  refine appP (A := .lolli bytesTy (.tensor bytesTy (.sum u8T .unit))) ?_ ?_
  · refine .lamV (caseP (A := .unit) (B := .tensor u8T bytesTy)
      (.unroll (A := bytesBody) (.var (by csoloQ))) ?_ ?_)
    · exact pairP (.roll bytesBody_noMut bytesTy_closed (.sumI₁ (.var (by csoloQ))))
        (.sumI₂ (.unitI (by cdeadQ)))
    · exact letP (A := u8T) (B := bytesTy) (.var (by csoloQ))
        (pairP (.var (by csoloQ)) (.sumI₁ (.var (by csoloQ))))
  · exact appP (A := .mut a bytesTy) (.var (by csoloQ)) (.withswap (by cdeadQ))


/-- A closed term receives no live slot. -/
theorem part_dead_closed {e : Expr} (he : ∀ j, occ j e = false) :
    ∀ {i : Nat} {Γ : Ctx VTy}, Ctx.Dead (part e i Γ).1
  | _, [] => .nil
  | i, ⟨T, true⟩ :: Γ => by
      simp only [part, he, if_true, Bool.false_eq_true, if_false]
      exact .cons (part_dead_closed he)
  | i, ⟨T, false⟩ :: Γ => by
      simp only [part, Bool.false_eq_true, if_false]
      exact .cons (part_dead_closed he)

theorem occ_readCb (j : Nat) : occ j (lam2 (.var 0)) = false := by
  simp [lam2, occ]

/-- `(Λ. Λ. …)`'s lifetime context: `'a ⊏ ⊤`, `'b ⊏ ⊤`. -/
abbrev Δwa : LifeCtx := (LifeCtx.empty.extend 0 .top).extend 1 .top

theorem Δwa₁_ok : (LifeCtx.empty.extend 0 .top).Ok := ok_empty.extend rfl rfl

theorem Δwa_ok : Δwa.Ok := Δwa₁_ok.extend rfl rfl

/-- `write_all`'s loop state: the output borrow and the view. -/
abbrev waS : VTy := .tensor (.mut (.var 0) outRep) (.arrayImm (.var 1) u8T)

/-- One step of `write_all` at index `i`: the byte at `i`, if there is one, to the output.
`λq. let (i, s) = q in let (m, v) = s in let (v, w) = copy v in
case idx (w, i) {inj₁ g. (write_byte (m, *g), v) | inj₂ _. (m, v)}`. -/
def waStepB : Expr :=
  .letpair (.var 0)
    (.letpair (.var 0)
      (.letpair (.app (.val copyV) (.var 0))
        (.case (.app (.val (.prim .idx)) (.pair (.var 0) (.var 5)))
          (.pair (.app (.val wbFnV) (.pair (.var 4) (readI (.var 0)))) (.var 2))
          (.pair (.var 4) (.var 2)))))

def waStepV : Val := .lam waStepB

theorem d_waStep :
    CDerives Δwa [] (.val waStepV) (.val (.bang (.lolli (.tensor .i32 waS) waS))) := by
  refine .bangThunkV (fun s hs => by cases hs) rfl (.lam (.ret ?_))
  refine letP (A := .i32) (B := waS) (.var (by csoloQ)) ?_
  refine letP (A := .mut (.var 0) outRep) (B := .arrayImm (.var 1) u8T) (.var (by csoloQ)) ?_
  refine letP (A := .arrayImm (.var 1) u8T) (B := .arrayImm (.var 1) u8T)
    (appP (.var (by csoloQ)) (.bangE (.arrCopy (.var 1) u8T (by cdeadQ)))) ?_
  refine caseP (A := .imm (.var 1) u8T) (B := .unit)
    (appP (pairP (.var (by csoloQ)) (.var (by csoloQ))) (.bangE (.arrGet (.var 1) u8T (by cdeadQ))))
    ?_ ?_
  · refine pairP (appP (pairP (.var (by csoloQ)) ?_) (d_wbFn (.var 0) (by cdeadQ)))
      (.var (by csoloQ))
    exact appW
      (callbackW Δwa_ok (x := 2) rfl (by cdead)
        (.boxI (.var (by csoloP))
          (CtxOutlives.solo (LifeCtx.defines_of_wf (wf_var_self _ _ _)) (outlives_of_dataB rfl)
            (by cdead))))
      (appW (.var (by csoloQ))
        (.withload (a := .var 1) (A := u8T) (B := u8T) 2 (by cdeadQ) rfl (by simp [VFree])
          (by simp [VFree])))
  · exact pairP (.var (by csoloQ)) (.var (by csoloQ))

theorem d_waStepΓ {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δwa Γ (.val waStepV) (.val (.bang (.lolli (.tensor .i32 waS) waS))) := by
  simpa using d_waStep.append_dead hΓ

/-- The model of `write_all`: `Λ. Λ. λp. let (m, v) = p in let (v, w) = copy v in
count_fold (step, (len w, (0, (m, v)))) to (m, v). forget v; m`.  `[spec §11]` -/
def writeAllB : Expr :=
  .letpair (.var 0)
    (.letpair (.app (.val copyV) (.var 0))
      (bindE (.app (.val arrLenV) (.var 0))
        (.letpair (.app (.val (.prim .count))
            (.pair (.val waStepV) (.pair (.var 0) (.pair (i32E 0) (.pair (.var 4) (.var 2))))))
          (.seq (.app (.val forgetV) (.var 0)) (.var 1)))))

def writeAllV : Val := .lam (.val (.lam (.val (.lam writeAllB))))

theorem d_writeAll :
    CDerives LifeCtx.empty [] (.val writeAllV) (.comp (writeAllC outRep)) := by
  refine .allI (S := .unit) rfl (fun _ _ hy => LifeCtx.Ok.bound_mentions_false ok_empty rfl hy)
    (fun _ h => by cases h) (.ret (.thunkV rfl ?_))
  refine .allI (S := .unit) rfl (fun _ _ hy => LifeCtx.Ok.bound_mentions_false Δwa₁_ok rfl hy)
    (fun s hs hl => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs; cases hl)
    (.ret (.lamV ?_))
  refine letP (A := .mut (.var 0) outRep) (B := .arrayImm (.var 1) u8T) (.var (by csoloQ)) ?_
  refine letP (A := .arrayImm (.var 1) u8T) (B := .arrayImm (.var 1) u8T)
    (appP (.var (by csoloQ)) (.bangE (.arrCopy (.var 1) u8T (by cdeadQ)))) ?_
  refine bindP (A := .i32) (appP (.var (by csoloQ)) (.bangE (.arrLen (.var 1) u8T (by cdeadQ)))) ?_
  refine letP (A := .mut (.var 0) outRep) (B := .arrayImm (.var 1) u8T) ?_ ?_
  · refine appP (A := .tensor (.bang (.lolli (.tensor .i32 waS) waS)) (.tensor .i32 (.tensor .i32 waS)))
      ?_ (.bangE (.countFold waS (by cdeadQ)))
    refine .tensorI (splitP_right_all _) (d_waStepΓ (kill_dead _)) ?_
    exact pairP (.var (by csoloQ)) (pairP (d_i32 0 (by cdeadQ))
      (pairP (.var (by csoloQ)) (.var (by csoloQ))))
  · exact .seqV (partP_split (.app (.val forgetV) (.var 0)) 0 _)
      (appP (.var (by csoloQ)) (.bangE (.arrForget (.var 1) u8T (by cdeadQ)))) (.var (by csoloQ))


/-- `read_into`'s loop state: the input borrow, the view, and the bytes read. -/
abbrev riS : VTy := .tensor (.mut (.var 0) bytesTy) (.tensor (.sliceMut (.var 1) u8T) .i32)

/-- One step of `read_into` at index `i`, with `k` bytes read so far. While every step has read a
byte (`k = i`), the next byte goes to slot `i`; after the end of the input nothing is read.
`λq. let (i, s) = q in let (m, r) = s in let (v, k) = r in
case eq (k, i) {inj₁ _. (m, (v, k)) | inj₂ _. let (m, o) = read_byte m in
  case o {inj₁ b. let (v, _) = replace (v, (i, b)) in (m, (v, k + 1)) | inj₂ _. (m, (v, k))}}`. -/
def riStepB : Expr :=
  .letpair (.var 0)
    (.letpair (.var 0)
      (.letpair (.var 0)
        (.case (hop (.rel .w32 .eq) (.pair (.var 0) (.var 5)))
          (.pair (.var 4) (.pair (.var 2) (.var 1)))
          (.letpair (.app (.val rbFnV) (.var 4))
            (.case (.var 0)
              (.letpair (.app (.val replaceV) (.pair (.var 5) (.pair (.var 9) (.var 0))))
                (.pair (.var 4) (.pair (.var 1) (hop (.bin .w32 .add) (.pair (.var 6) (i32E 1))))))
              (.pair (.var 2) (.pair (.var 5) (.var 4))))))))

def riStepV : Val := .lam riStepB

theorem d_riStep :
    CDerives Δwa [] (.val riStepV) (.val (.bang (.lolli (.tensor .i32 riS) riS))) := by
  refine .bangThunkV (fun s hs => by cases hs) rfl (.lam (.ret ?_))
  refine letP (A := .i32) (B := riS) (.var (by csoloQ)) ?_
  refine letP (A := .mut (.var 0) bytesTy) (B := .tensor (.sliceMut (.var 1) u8T) .i32)
    (.var (by csoloQ)) ?_
  refine letP (A := .sliceMut (.var 1) u8T) (B := .i32) (.var (by csoloQ)) ?_
  refine caseP (A := .unit) (B := .unit)
    (d_hop (.rel .w32 .eq) (pairP (.var (by csoloQ)) (.var (by csoloQ))) (by cdeadQ)) ?_ ?_
  · exact pairP (.var (by csoloQ)) (pairP (.var (by csoloQ)) (.var (by csoloQ)))
  · refine letP (A := .mut (.var 0) bytesTy) (B := .sum u8T .unit)
      (appP (.var (by csoloQ)) (d_rbFn (.var 0) (by cdeadQ))) ?_
    refine caseP (A := u8T) (B := .unit) (.var (by csoloQ)) ?_ ?_
    · refine letP (A := .sliceMut (.var 1) u8T) (B := .sum u8T u8T)
        (appP (pairP (.var (by csoloQ)) (pairP (.var (by csoloQ)) (.var (by csoloQ))))
          (.bangE (.sliceReplaceM (.var 1) u8T (by cdeadQ)))) ?_
      exact pairP (.var (by csoloQ)) (pairP (.var (by csoloQ))
        (d_hop (.bin .w32 .add) (pairP (.var (by csoloQ)) (d_i32 1 (by cdeadQ))) (by cdeadQ)))
    · exact pairP (.var (by csoloQ)) (pairP (.var (by csoloQ)) (.var (by csoloQ)))

theorem d_riStepΓ {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives Δwa Γ (.val riStepV) (.val (.bang (.lolli (.tensor .i32 riS) riS))) := by
  simpa using d_riStep.append_dead hΓ

/-- The model of `read_into`: `Λ. Λ. λp. let (m, v) = p in let (v, n) = len v in
count_fold (step, (n, (0, (m, (v, 0)))))`.  `[spec §11]` -/
def readIntoB : Expr :=
  .letpair (.var 0)
    (.letpair (.app (.val sizeV) (.var 0))
      (.app (.val (.prim .count))
        (.pair (.val riStepV)
          (.pair (.var 0) (.pair (i32E 0) (.pair (.var 3) (.pair (.var 1) (i32E 0))))))))

def readIntoV : Val := .lam (.val (.lam (.val (.lam readIntoB))))

theorem d_readInto :
    CDerives LifeCtx.empty [] (.val readIntoV) (.comp (readIntoC bytesTy)) := by
  refine .allI (S := .unit) rfl (fun _ _ hy => LifeCtx.Ok.bound_mentions_false ok_empty rfl hy)
    (fun _ h => by cases h) (.ret (.thunkV rfl ?_))
  refine .allI (S := .unit) rfl (fun _ _ hy => LifeCtx.Ok.bound_mentions_false Δwa₁_ok rfl hy)
    (fun s hs hl => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hs; subst hs; cases hl)
    (.ret (.lamV ?_))
  refine letP (A := .mut (.var 0) bytesTy) (B := .sliceMut (.var 1) u8T) (.var (by csoloQ)) ?_
  refine letP (A := .sliceMut (.var 1) u8T) (B := .i32)
    (appP (.var (by csoloQ)) (.bangE (.sliceLenM (.var 1) u8T (by cdeadQ)))) ?_
  refine appP (A := .tensor (.bang (.lolli (.tensor .i32 riS) riS)) (.tensor .i32 (.tensor .i32 riS)))
    ?_ (.bangE (.countFold riS (by cdeadQ)))
  refine .tensorI (splitP_right_all _) (d_riStepΓ (kill_dead _)) ?_
  exact pairP (.var (by csoloQ)) (pairP (d_i32 0 (by cdeadQ))
    (pairP (.var (by csoloQ)) (pairP (.var (by csoloQ)) (d_i32 0 (by cdeadQ)))))

theorem cC_writeAllC : cC (writeAllC outRep) = cC (writeAllC (.opq .output)) := by
  funext ls δ e ρ
  simp only [writeAllC, cC, vCE, forceE, vC_outRep]

theorem cC_readIntoC : cC (readIntoC bytesTy) = cC (readIntoC (.opq .input)) := by
  funext ls δ e ρ
  simp only [readIntoC, cC, vCE, forceE, vC_bytes]

/-- **The model of `write_all` meets its contract.**  `[spec §11]` -/
theorem writeAll_meets (ls : List SRec) (δ : LSub) :
    vC true (externTy (writeAllC (.opq .output))) ls δ writeAllV PMap.empty := by
  rw [← vC_externTy_congr rfl rfl cC_writeAllC]
  exact meets_of_derives rfl d_writeAll ls δ

/-- **The model of `read_into` meets its contract.**  `[spec §11]` -/
theorem readInto_meets (ls : List SRec) (δ : LSub) :
    vC true (externTy (readIntoC (.opq .input))) ls δ readIntoV PMap.empty := by
  rw [← vC_externTy_congr rfl rfl cC_readIntoC]
  exact meets_of_derives rfl d_readInto ls δ

/-! ### The clock  `[spec §34]`

A clock is a cell whose content is a time in nanoseconds: its representation is `I64`, and the
relation there is `Clock`'s model (`vC_clockRep`). `clock_now` answers the time and keeps it;
`clock_sleep` adds `max(ns, 0)` to it, saturating at `2^63 − 1`; the harness `mk_clock` makes a
clock at time `0` and `take_clock` frees it. Each model is a `CDerives` derivation at the
representation, so it meets its contract by the Fundamental Property, as the streams' do. -/

/-- **`Clock` is `I64` with the rules taken away.**  `[spec §34]` -/
theorem vC_clockRep (b : Bool) (ls : List SRec) (δ : LSub) :
    vC b .i64 ls δ = vC b (.opq .clock) ls δ := by
  funext v ρ
  rfl

/-- `clock_now`: `∀'a ⊏ ⊤. F (Mut 'a C ⇒ Mut 'a C ⊗ I64)`.  `[spec §34]` -/
def clockNowC (C : VTy) : CTy :=
  .all 0 .top (.ret (.lolli (.mut (.var 0) C) (.tensor (.mut (.var 0) C) .i64)))

/-- `clock_sleep`: `∀'a ⊏ ⊤. F (Mut 'a C ⊗ I64 ⇒ Mut 'a C)`.  `[spec §34]` -/
def clockSleepC (C : VTy) : CTy :=
  .all 0 .top (.ret (.lolli (.tensor (.mut (.var 0) C) .i64) (.mut (.var 0) C)))

/-- `mk_clock`: `1 ⊸ F (Ref C)`.  `[spec §34]` -/
def mkClockC (C : VTy) : CTy := .arr .unit (.ret (.ref C))

/-- `take_clock`: `Ref C ⊸ F I64`.  `[spec §34]` -/
def takeClockC (C : VTy) : CTy := .arr (.ref C) (.ret .i64)

/-- `clock_now`'s callback: `λt. (t, t)`. -/
def cnCallback : Expr := .val (.lam (.pair (.var 0) (.var 0)))

/-- The model of `clock_now`: `Λ. λm. withswap m cnCallback`.  `[spec §34]` -/
def clockNowV : Val := .lam (.val (.lam (.app (.app withswap (.var 0)) cnCallback)))

/-- A 64-bit literal. -/
def i64E (n : UInt64) : Expr := .val (Val.i64 n)

/-- The time after a sleep, under `λt` with the duration `ns` at index `1`: `t` when `ns ≤ 0`,
else `t + ns`, or `2^63 − 1` when the sum overflows. -/
def sleptT : Expr :=
  .case (hop (.rel .w64 .gt_s) (.pair (.var 1) (i64E 0)))
    (.var 1)
    (.case (hop (.rel .w64 .lt_s) (.pair (hop (.bin .w64 .add) (.pair (.var 1) (.var 2))) (.var 1)))
      (hop (.bin .w64 .add) (.pair (.var 2) (.var 3)))
      (i64E 0x7fffffffffffffff))

/-- `clock_sleep`'s callback at the duration (index `0`): `λt. (sleptT, ())`. -/
def csCallback : Expr := .val (.lam (.pair sleptT (.val .unit)))

/-- The model of `clock_sleep`: `Λ. λp. let (m, ns) = p in let (m', u) = withswap m csCallback in
u; m'`.  `[spec §34]` -/
def clockSleepV : Val :=
  .lam (.val (.lam (.letpair (.var 0)
    (.letpair (.app (.app withswap (.var 1)) csCallback) (.seq (.var 0) (.var 1))))))

/-- The model of `mk_clock`: `λu. alloc i64[0]`.  `[spec §34]` -/
def mkClockV : Val := .lam (.app (.val (.prim .alloc)) (i64E 0))

theorem d_clockNow : CDerives LifeCtx.empty [] (.val clockNowV) (.comp (clockNowC .i64)) := by
  refine .allI (S := .unit) rfl (fun _ _ hy => LifeCtx.Ok.bound_mentions_false ok_empty rfl hy)
    (fun _ h => by cases h) (.ret (.lamV ?_))
  refine appP (A := .lolli .i64 (.tensor .i64 .i64)) ?_ ?_
  · exact .lamV (pairP (.var (by csoloP)) (.var (by csoloP)))
  · exact appP (A := .mut (.var 0) .i64) (.var (by csoloP)) (.withswap (by cdeadP))

theorem d_clockSleep :
    CDerives LifeCtx.empty [] (.val clockSleepV) (.comp (clockSleepC .i64)) := by
  refine .allI (S := .unit) rfl (fun _ _ hy => LifeCtx.Ok.bound_mentions_false ok_empty rfl hy)
    (fun _ h => by cases h) (.ret (.lamV ?_))
  refine letP (A := .mut (.var 0) .i64) (B := .i64) (.var (by csoloP)) ?_
  refine letP (A := .mut (.var 0) .i64) (B := .unit) ?_
    (.seqV (partP_split (.var 0) 0 _) (.var (by csoloP)) (.var (by csoloP)))
  refine appP (A := .lolli .i64 (.tensor .i64 .unit)) ?_ ?_
  · refine .lamV (pairP ?_ (.unitI (by cdeadP)))
    refine caseP (A := .unit) (B := .unit)
      (d_hop (.rel .w64 .gt_s) (pairP (.var (by csoloP)) (.lit (.i64 0) (by cdeadP))) (by cdeadP))
      (.var (by csoloP)) ?_
    refine caseP (A := .unit) (B := .unit)
      (d_hop (.rel .w64 .lt_s) (pairP (d_hop (.bin .w64 .add)
        (pairP (.var (by csoloP)) (.var (by csoloP))) (by cdeadP)) (.var (by csoloP))) (by cdeadP))
      ?_ (.lit (.i64 0x7fffffffffffffff) (by cdeadP))
    exact d_hop (.bin .w64 .add) (pairP (.var (by csoloP)) (.var (by csoloP))) (by cdeadP)
  · exact appP (A := .mut (.var 0) .i64) (.var (by csoloP)) (.withswap (by cdeadP))

theorem d_mkClock : CDerives LifeCtx.empty [] (.val mkClockV) (.comp (mkClockC .i64)) :=
  .lam (.ret (appP (.lit (.i64 0) (by cdeadP)) (.alloc (by cdeadP))))

theorem d_takeClock : CDerives LifeCtx.empty [] (.val takeCapV) (.comp (takeClockC .i64)) :=
  .lam (.ret (appP (.var (by csoloP)) (.free (by cdeadP))))

theorem cC_clockNowC : cC (clockNowC .i64) = cC (clockNowC (.opq .clock)) := by
  funext ls δ e ρ
  simp only [clockNowC, cC, vCE, forceE, Opaque.Holds, Val.IsInt]

theorem cC_clockSleepC : cC (clockSleepC .i64) = cC (clockSleepC (.opq .clock)) := by
  funext ls δ e ρ
  simp only [clockSleepC, cC, vCE, forceE, Opaque.Holds, Val.IsInt]

theorem cC_mkClockC : cC (mkClockC .i64) = cC (mkClockC (.opq .clock)) := by
  funext ls δ e ρ
  simp only [mkClockC, cC, vCE, Opaque.Holds, Val.IsInt]

theorem cC_takeClockC : cC (takeClockC .i64) = cC (takeClockC (.opq .clock)) := by
  funext ls δ e ρ
  simp only [takeClockC, cC, vCE, Opaque.Holds, Val.IsInt]

/-- **The model of `clock_now` meets its contract.**  `[spec §34]` -/
theorem clockNow_meets (ls : List SRec) (δ : LSub) :
    vC true (externTy (clockNowC (.opq .clock))) ls δ clockNowV PMap.empty := by
  rw [← vC_externTy_congr rfl rfl cC_clockNowC]
  exact meets_of_derives rfl d_clockNow ls δ

/-- **The model of `clock_sleep` meets its contract.**  `[spec §34]` -/
theorem clockSleep_meets (ls : List SRec) (δ : LSub) :
    vC true (externTy (clockSleepC (.opq .clock))) ls δ clockSleepV PMap.empty := by
  rw [← vC_externTy_congr rfl rfl cC_clockSleepC]
  exact meets_of_derives rfl d_clockSleep ls δ

/-- **The model of `mk_clock` meets its contract.**  `[spec §34]` -/
theorem mkClock_meets (ls : List SRec) (δ : LSub) :
    vC true (externTy (mkClockC (.opq .clock))) ls δ mkClockV PMap.empty := by
  rw [← vC_externTy_congr rfl rfl cC_mkClockC]
  exact meets_of_derives rfl d_mkClock ls δ

/-- **The model of `take_clock` meets its contract.**  `[spec §34]` -/
theorem takeClock_meets (ls : List SRec) (δ : LSub) :
    vC true (externTy (takeClockC (.opq .clock))) ls δ takeCapV PMap.empty := by
  rw [← vC_externTy_congr rfl rfl cC_takeClockC]
  exact meets_of_derives rfl d_takeClock ls δ

/-! ### The arguments  `[spec §34]`

The arguments' cell holds the arguments not yet read, a byte list, as an input's does: `read_arg`
is `read_byte`'s model at `Args`, and the harness `mk_args`, `take_args` is `mk_input`'s and
`take_input`'s. -/

theorem cC_readArgC : cC (readByteC bytesTy) = cC (readByteC (.opq .args)) := by
  funext ls δ e ρ
  simp only [readByteC, cC, vCE, forceE, vC_argsRep]

theorem cC_mkArgsC : cC (mkInputC bytesTy) = cC (mkInputC (.opq .args)) := by
  funext ls δ e ρ
  simp only [mkInputC, cC, vCE, vC_argsRep]

theorem cC_takeArgsC : cC (takeInputC bytesTy) = cC (takeInputC (.opq .args)) := by
  funext ls δ e ρ
  simp only [takeInputC, cC, vCE, vC_argsRep]

/-- **The model of `read_arg` meets its contract.**  `[spec §34]` -/
theorem readArg_meets (ls : List SRec) (δ : LSub) :
    vC true (externTy (readByteC (.opq .args))) ls δ readByteV PMap.empty := by
  rw [← vC_externTy_congr rfl rfl cC_readArgC]
  exact meets_of_derives rfl d_readByte ls δ

/-- **The model of `mk_args` meets its contract.**  `[spec §34]` -/
theorem mkArgs_meets (ls : List SRec) (δ : LSub) :
    vC true (externTy (mkInputC (.opq .args))) ls δ mkInputV PMap.empty := by
  rw [← vC_externTy_congr rfl rfl cC_mkArgsC]
  exact meets_of_derives rfl d_mkInput ls δ

/-- **The model of `take_args` meets its contract.**  `[spec §34]` -/
theorem takeArgs_meets (ls : List SRec) (δ : LSub) :
    vC true (externTy (takeInputC (.opq .args))) ls δ takeCapV PMap.empty := by
  rw [← vC_externTy_congr rfl rfl cC_takeArgsC]
  exact meets_of_derives rfl d_takeInput ls δ

/-! ### End to end -/

/-- **The contracts, as a named hypothesis.**  Each slot of `Γ` is live, at a persistent type,
and the value of `γ` at its index implements it at `∅`, at every record list and lifetime
substitution.  `[spec §11]` -/
inductive ExternsMeet : Ctx VTy → List Val → Prop
  | nil : ExternsMeet [] []
  | cons {T : VTy} {Γ : Ctx VTy} {v : Val} {γ : List Val} (hT : T.Persistent)
      (hv : ∀ ls δ, vC true T ls δ v PMap.empty) (h : ExternsMeet Γ γ) :
      ExternsMeet (⟨T, true⟩ :: Γ) (v :: γ)

/-- Externs that meet their contracts at `∅` satisfy the context relation at `∅`. -/
theorem gDenC_of_meets {Γ : Ctx VTy} {γ : List Val} (h : ExternsMeet Γ γ) (ls : List SRec)
    (δ : LSub) : gDenC ls δ Γ γ PMap.empty := by
  refine ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, ?_⟩, ?_⟩
  · clear ls δ
    induction h with
    | nil => trivial
    | cons _ _ _ ih => exact ih
  · induction h with
    | nil => exact ⟨rfl, trivial⟩
    | cons _ hv _ ih =>
        show (vC true _ ls δ _ ⋆ gSepC ls δ _ _) PMap.empty
        exact ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, hv ls δ, ih⟩

/-- **End to end, at every implementation of the externs.**  `run_io : Bytes ⊸ F R` is checked
at a context of externs, `R` is persistent, and `γ` implements every extern at `∅` (the named
hypothesis `ExternsMeet`).  Then for every input byte list, every run of `run_io[γ] inp` from the
empty memory, under every allocator, can be continued to a value of `R` at the empty memory.
`adequacyD`'s form, by `theorem32D`.  `[spec §11, §13]` -/
theorem externs_every_run {Γ : Ctx VTy} {e : Expr} {R : VTy}
    (h : CDerives LifeCtx.empty Γ e (.comp (.arr bytesTy (.ret R)))) (hR : R.Persistent)
    {γ : List Val} (hγ : ExternsMeet Γ γ) {inp : Val} (hin : BytesV inp)
    {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps Adequacy.emptyMem (.app (substAll γ e) (.val inp)) μ₁ e₁) :
    ∃ v : Val, Steps μ₁ e₁ Adequacy.emptyMem (.val v) ∧
      ∃ ls δ, vC true R ls δ v PMap.empty := by
  have hsem := fundamentalC h LSub.empty γ [] PMap.empty Adequacy.models_empty
    (gDenC_of_meets hγ [] LSub.empty)
  have hwp := hsem inp PMap.empty PMap.empty (vC_bytes_iff.mpr ⟨rfl, hin⟩)
    (ResU.comp_empty_right _)
  have hwp' : wpTS [] (.app (substAll γ e) (.val inp))
      (fun _ v => Fig16.BoLo.pure (∃ ls δ, vC true R ls δ v PMap.empty)) PMap.empty := by
    refine wpTS_mono (fun ls v ρ hv => ?_) PMap.empty hwp
    obtain rfl := vP_empty_of_persistent hR hv
    exact ⟨rfl, ls, LSub.empty, hv⟩
  exact theorem32D _ _ hwp' hs

/-- **No run is stuck**: under the hypotheses of `externs_every_run`, every run of
`run_io[γ] inp` from the empty memory ends at a value or can step.  `[spec §11, §13]` -/
theorem externs_safe {Γ : Ctx VTy} {e : Expr} {R : VTy}
    (h : CDerives LifeCtx.empty Γ e (.comp (.arr bytesTy (.ret R)))) (hR : R.Persistent)
    {γ : List Val} (hγ : ExternsMeet Γ γ) {inp : Val} (hin : BytesV inp)
    {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps Adequacy.emptyMem (.app (substAll γ e) (.val inp)) μ₁ e₁) :
    IsVal e₁ ∨ ∃ μ₂ e₂, Step1 μ₁ e₁ μ₂ e₂ := by
  obtain ⟨v, hv, -⟩ := externs_every_run h hR hγ hin hs
  cases hv with
  | refl => exact .inl v.2
  | more h _ => exact .inr ⟨_, _, h⟩

/-! ### The model instance -/

/-- The standard externs' types and their models.  `[spec §11]` -/
def stdModel : List (VTy × Val) :=
  [(externTy (readByteC (.opq .input)), readByteV),
   (externTy (writeByteC (.opq .output)), writeByteV),
   (externTy (mkInputC (.opq .input)), mkInputV),
   (externTy (mkOutputC (.opq .output)), mkOutputV),
   (externTy (takeInputC (.opq .input)), takeCapV),
   (externTy (takeOutputC (.opq .output)), takeCapV),
   (externTy (writeAllC (.opq .output)), writeAllV),
   (externTy (readIntoC (.opq .input)), readIntoV),
   (externTy (clockNowC (.opq .clock)), clockNowV),
   (externTy (clockSleepC (.opq .clock)), clockSleepV),
   (externTy (mkClockC (.opq .clock)), mkClockV),
   (externTy (takeClockC (.opq .clock)), takeCapV),
   (externTy (readByteC (.opq .args)), readByteV),
   (externTy (mkInputC (.opq .args)), mkInputV),
   (externTy (takeInputC (.opq .args)), takeCapV)]

theorem stdModel_meets : ∀ p ∈ stdModel, ∀ ls δ, vC true p.1 ls δ p.2 PMap.empty := by
  intro p hp ls δ
  simp only [stdModel, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  · exact readByte_meets ls δ
  · exact writeByte_meets ls δ
  · exact mkInput_meets ls δ
  · exact mkOutput_meets ls δ
  · exact takeInput_meets ls δ
  · exact takeOutput_meets ls δ
  · exact writeAll_meets ls δ
  · exact readInto_meets ls δ
  · exact clockNow_meets ls δ
  · exact clockSleep_meets ls δ
  · exact mkClock_meets ls δ
  · exact takeClock_meets ls δ
  · exact readArg_meets ls δ
  · exact mkArgs_meets ls δ
  · exact takeArgs_meets ls δ

/-- Externs each given its model, by type. -/
theorem externsMeet_of_model : ∀ {Γ : Ctx VTy} {γ : List Val},
    List.Forall₂ (fun s v => s.live = true ∧ (s.ty, v) ∈ stdModel) Γ γ → ExternsMeet Γ γ
  | [], [], .nil => .nil
  | ⟨T, l⟩ :: _, v :: _, .cons ⟨hl, hm⟩ h => by
      simp only at hl; subst hl
      have hT : T.Persistent := by
        simp only [stdModel, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
          ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ |
          ⟨rfl, -⟩ <;> rfl
      exact .cons hT (stdModel_meets _ hm) (externsMeet_of_model h)

/-- **End to end, the model.**  `bcc interp`'s run: `run_io` with every extern given its model.
Every run from the empty memory, under every allocator, continues to a value of `R` at the empty
memory.  `[spec §11, §13]` -/
theorem io_every_run {Γ : Ctx VTy} {e : Expr} {R : VTy}
    (h : CDerives LifeCtx.empty Γ e (.comp (.arr bytesTy (.ret R)))) (hR : R.Persistent)
    {γ : List Val} (hγ : List.Forall₂ (fun s v => s.live = true ∧ (s.ty, v) ∈ stdModel) Γ γ)
    {inp : Val} (hin : BytesV inp) {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps Adequacy.emptyMem (.app (substAll γ e) (.val inp)) μ₁ e₁) :
    ∃ v : Val, Steps μ₁ e₁ Adequacy.emptyMem (.val v) ∧
      ∃ ls δ, vC true R ls δ v PMap.empty :=
  externs_every_run h hR (externsMeet_of_model hγ) hin hs

/-! ### Every run of `main`, and no capability, no effect -/

/-- **Every run of `main`**: at any extern context, from every configuration whose resource
satisfies the contracts, no run of `main` is stuck.  `fundamentalD` at `main`.  `[spec §11]` -/
theorem externs_main_safe {Γ : Ctx VTy} {e : Expr} {A : VTy}
    (h : CDerives LifeCtx.empty Γ e (.comp (.ret A))) {δ : LSub} {γ : List Val}
    {ls : List SRec} {ρ ρf fρ : WRes} {ps : List FrameRec} (hg : gDenC ls δ Γ γ ρ)
    (hf : ResU.Hash ρf ρ) (hc : ResU.CompS ρf ρ fρ) (hT : TW fρ ps (rsOf ls))
    (htg : Tagged fρ ps ls) {μ μ₁ : Heap} (hμ : ResU.Lower fρ μ) {e₁ : Expr}
    (hs : Steps μ (substAll γ e) μ₁ e₁) : IsVal e₁ ∨ ∃ μ₂ e₂, Step1 μ₁ e₁ μ₂ e₂ :=
  wpTSD_safe (fundamentalD h (models_empty_any δ) hg) hf hc hT htg hμ hs

/-- **No capability, no effect.**  A cell owned by the frame of a computation holds the same
value at the end of every value run of it, under every allocator.  A computation's resource is
what its context and captures hold, so a function given neither a capability's cell nor a
borrow of it leaves the cell's content as it was: given no `stdout`, it writes nothing to
standard output.  `[spec §11]` -/
theorem wpTSD_frame_own {ls : List SRec} {e : Expr} {Q : List SRec → Val → WProp}
    {ρ ρf fρ : WRes} {ps : List FrameRec} (hw : wpTSD ls e Q ρ) (hf : ResU.Hash ρf ρ)
    (hc : ResU.CompS ρf ρ fρ) (hT : TW fρ ps (rsOf ls)) (htg : Tagged fρ ps ls)
    {μ μ₁ : Heap} (hμ : ResU.Lower fρ μ) {w : Val} (hs : Steps μ e μ₁ (.val w))
    {l : Loc} {v : Val} (hl : ρf.get l = some (CellU.ownOf v)) : μ₁ l = some v := by
  obtain ⟨ρ', ρp, fρ', fρ'p, π, ps', ls', -, h₂, -, h₄, h₅, -⟩ :=
    wpTSD_val hw hf hc hT htg hμ hs
  obtain ⟨ψ, hψ, -, -, he⟩ := Typed.compS_get_left' h₂ hl
  obtain ⟨ψ', hψ', -, -, he'⟩ := Typed.compS_get_left' h₄ hψ
  rw [lower_get h₅ hψ', he', he, CellU.erase_ownOf]

/-! ### Programs that run until their input ends  `[spec §11]` -/

/-- A byte list as a value of `Bytes`. -/
def bytesVal : List UInt8 → Val
  | [] => .inj₁ .unit
  | b :: bs => .inj₂ (.pair (.u8 b) (bytesVal bs))

theorem bytesVal_bytes : ∀ bs, BytesV (bytesVal bs)
  | [] => .nil
  | b :: bs => .cons b (bytesVal_bytes bs)

theorem d_bytesVal {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    ∀ bs, CDerives Δ Γ (.val (bytesVal bs)) (.val bytesTy)
  | [] => .roll bytesBody_noMut bytesTy_closed (.sumI₁ (.unitI hΓ.toP))
  | b :: bs => .roll bytesBody_noMut bytesTy_closed
      (.sumI₂ (.tensorI (deadSplit hΓ) (.lit (.u8 b) hΓ.toP) (d_bytesVal hΓ bs)))

/-- `run_io inp`, driven: `run_io` applied to the input, then observed at most `n` times and
closed if it has not finished (`driveE`, SPEC §7). -/
def ioLoopE (N : Expr) (bs : List UInt8) (n : ℕ) : Expr :=
  bindE (.app (.val (.lam N)) (.val (bytesVal bs))) (driveE n)

/-- **The driven program is an ordinary program**: at the externs' context, for every input and
every `n`. -/
theorem d_ioLoop {Γ : Ctx VTy} {N : Expr} {R R' : VTy}
    (h : CDerives LifeCtx.empty Γ (.val (.lam N)) (.comp (.arr bytesTy (.ret (.thunk (.loop R R'))))))
    (bs : List UInt8) (n : ℕ) :
    CDerives LifeCtx.empty Γ (ioLoopE N bs n) (.comp (.ret (.sum R R'))) :=
  .bind (splitP_left_all Γ)
    (.ret (.lolliE (splitP_right_all Γ) (d_bytesVal (kill_dead Γ) bs) (.thunkV rfl h)))
    (d_driveL R R' n (kill_dead Γ))

/-- **End to end for a program that runs until its input ends, at every implementation of the
externs.**  `run_io : Bytes ⊸ F (U (Loop R R'))`, both residuals persistent, `γ` meeting the
contracts at `∅`. For every input and every `n`, every run of `run_io[γ] inp` observed at most
`n` times, from the empty memory and under every allocator, continues to a value at the empty
memory: `inl` of the finished result, or `inr` of the closed residual.  `[spec §11, §13]` -/
theorem externs_loop_every_run {Γ : Ctx VTy} {N : Expr} {R R' : VTy}
    (h : CDerives LifeCtx.empty Γ (.val (.lam N)) (.comp (.arr bytesTy (.ret (.thunk (.loop R R'))))))
    (hR : R.Persistent) (hR' : R'.Persistent) {γ : List Val} (hγ : ExternsMeet Γ γ)
    (bs : List UInt8) (n : ℕ) {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps Adequacy.emptyMem (substAll γ (ioLoopE N bs n)) μ₁ e₁) :
    ∃ v : Val, Steps μ₁ e₁ Adequacy.emptyMem (.val v) ∧
      ∃ ls δ, vC true (.sum R R') ls δ v PMap.empty := by
  have hwp := fundamentalC (d_ioLoop h bs n) LSub.empty γ [] PMap.empty Adequacy.models_empty
    (gDenC_of_meets hγ [] LSub.empty)
  have hS : (VTy.sum R R').Persistent := by
    simp only [VTy.Persistent, VTy.persistent, Bool.and_eq_true]; exact ⟨hR, hR'⟩
  have hwp' : wpTS [] (substAll γ (ioLoopE N bs n))
      (fun _ v => Fig16.BoLo.pure (∃ ls δ, vC true (.sum R R') ls δ v PMap.empty)) PMap.empty := by
    refine wpTS_mono (fun ls v ρ hv => ?_) PMap.empty hwp
    obtain rfl := vP_empty_of_persistent hS hv
    exact ⟨rfl, ls, LSub.empty, hv⟩
  exact theorem32D _ _ hwp' hs

/-- **End to end for a program that runs until its input ends, at the model.**
`[spec §11, §13]` -/
theorem io_loop_every_run {Γ : Ctx VTy} {N : Expr} {R R' : VTy}
    (h : CDerives LifeCtx.empty Γ (.val (.lam N)) (.comp (.arr bytesTy (.ret (.thunk (.loop R R'))))))
    (hR : R.Persistent) (hR' : R'.Persistent) {γ : List Val}
    (hγ : List.Forall₂ (fun s v => s.live = true ∧ (s.ty, v) ∈ stdModel) Γ γ)
    (bs : List UInt8) (n : ℕ) {μ₁ : Heap} {e₁ : Expr}
    (hs : Steps Adequacy.emptyMem (substAll γ (ioLoopE N bs n)) μ₁ e₁) :
    ∃ v : Val, Steps μ₁ e₁ Adequacy.emptyMem (.val v) ∧
      ∃ ls δ, vC true (.sum R R') ls δ v PMap.empty :=
  externs_loop_every_run h hR hR' (externsMeet_of_model hγ) bs n hs

end BoCa.Fig16.LogRel.Core

end
