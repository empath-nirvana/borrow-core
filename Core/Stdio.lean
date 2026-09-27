import Core.Demonic
import Core.IntPrograms

/-!
# Core — standard I/O  `[spec §11]`

The capabilities `stdin : Ref Input`, `stdout`, `stderr : Ref Output` and their operations are
externs: hypotheses of the end-to-end theorem, not rules.  This file gives their model and
proves that it meets their contracts.

* **Representation.** `Bytes = μX. 1 ⊕ (I32 ⊗ X)`.  The relation at `Bytes` is the model of
  `Input` (`vC_bytes`), and at `I32 ⊗ Bytes` the model of `Output` (`vC_outRep`): an opaque type
  is its representation with the rules taken away.
* **The model** is ordinary core terms at the representation: `read_byte` is `withswap` popping
  the head of the list, `write_byte` is `withswap` consing onto it, and the harness `mk_input`,
  `mk_output`, `take_input`, `take_output` is `alloc` and `free`.  Each is a `CDerives`
  derivation at the representation (`d_readByte`, …), so the Fundamental Property puts it in the
  relation there, and the relation at the extern's type is the same (`cC_readByteC`, …):
  `readByte_meets`, `writeByte_meets`, `mkInput_meets`, `mkOutput_meets`, `takeInput_meets`,
  `takeOutput_meets`.
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

/-- `1 ⊕ (I32 ⊗ X)`. -/
def bytesBody : VTy := .sum .unit (.tensor .i32 (.tvar 0))

/-- `Bytes = μX. 1 ⊕ (I32 ⊗ X)`: a byte list.  `[spec §11]` -/
def bytesTy : VTy := .mu bytesBody

/-- `I32 ⊗ Bytes`: an output stream's descriptor and the bytes written to it, the
representation of `Output`.  `[spec §11]` -/
def outRep : VTy := .tensor .i32 bytesTy

theorem bytesBody_noMut : bytesBody.NoMut 0 := ⟨trivial, trivial, trivial⟩

theorem bytesTy_closed : bytesTy.Cl 0 := ⟨trivial, trivial, Nat.zero_lt_one⟩

theorem bytes_unroll : VTy.inst bytesTy bytesBody = .sum .unit (.tensor .i32 bytesTy) := rfl

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
        show vC b (.sum .unit (.tensor .i32 bytesTy)) ls δ _ _
        exact Or.inl ⟨.unit, pure_sep_iff.mpr ⟨rfl, rfl, rfl⟩⟩
    | cons n _ ih =>
        refine vC_roll (A := bytesBody) bytesBody_noMut bytesTy_closed ?_
        show vC b (.sum .unit (.tensor .i32 bytesTy)) ls δ _ _
        refine Or.inr ⟨_, pure_sep_iff.mpr ⟨rfl, ?_⟩⟩
        exact ⟨_, _, PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, rfl⟩,
          PMap.empty, PMap.empty, ResU.comp_empty_right _, ⟨rfl, n, rfl⟩, ih⟩

/-- **`Input` is `Bytes` with the rules taken away**: the relation at `Bytes` is `Input`'s
model.  `[spec §11]` -/
theorem vC_bytes (b : Bool) (ls : List SRec) (δ : LSub) :
    vC b bytesTy ls δ = vC b (.opq .input) ls δ := by
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

/-- `read_byte`: `∀'a ⊏ ⊤. F (Mut 'a I ⇒ Mut 'a I ⊗ (I32 ⊕ 1))`.  `[spec §11]` -/
def readByteC (I : VTy) : CTy :=
  .all 0 .top (.ret (.lolli (.mut (.var 0) I) (.tensor (.mut (.var 0) I) (.sum .i32 .unit))))

/-- `write_byte`: `∀'a ⊏ ⊤. F (Mut 'a O ⊗ I32 ⇒ Mut 'a O)`.  `[spec §11]` -/
def writeByteC (O : VTy) : CTy :=
  .all 0 .top (.ret (.lolli (.tensor (.mut (.var 0) O) .i32) (.mut (.var 0) O)))

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
  refine appP (A := .lolli bytesTy (.tensor bytesTy (.sum .i32 .unit))) ?_ ?_
  · refine .lamV (caseP (A := .unit) (B := .tensor .i32 bytesTy)
      (.unroll (A := bytesBody) (.var (by csoloP))) ?_ ?_)
    · exact pairP (.roll bytesBody_noMut bytesTy_closed (.sumI₁ (.var (by csoloP))))
        (.sumI₂ (.unitI (by cdeadP)))
    · exact letP (A := .i32) (B := bytesTy) (.var (by csoloP))
        (pairP (.var (by csoloP)) (.sumI₁ (.var (by csoloP))))
  · exact appP (A := .mut (.var 0) bytesTy) (.var (by csoloP)) (.withswap (by cdeadP))

theorem d_writeByte :
    CDerives LifeCtx.empty [] (.val writeByteV) (.comp (writeByteC outRep)) := by
  refine .allI (S := .unit) rfl (fun _ _ hy => LifeCtx.Ok.bound_mentions_false ok_empty rfl hy)
    (fun _ h => by cases h) (.ret (.lamV ?_))
  refine letP (A := .mut (.var 0) outRep) (B := .i32) (.var (by csoloP)) ?_
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
   (externTy (takeOutputC (.opq .output)), takeCapV)]

theorem stdModel_meets : ∀ p ∈ stdModel, ∀ ls δ, vC true p.1 ls δ p.2 PMap.empty := by
  intro p hp ls δ
  simp only [stdModel, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact readByte_meets ls δ
  · exact writeByte_meets ls δ
  · exact mkInput_meets ls δ
  · exact mkOutput_meets ls δ
  · exact takeInput_meets ls δ
  · exact takeOutput_meets ls δ

/-- Externs each given its model, by type. -/
theorem externsMeet_of_model : ∀ {Γ : Ctx VTy} {γ : List Val},
    List.Forall₂ (fun s v => s.live = true ∧ (s.ty, v) ∈ stdModel) Γ γ → ExternsMeet Γ γ
  | [], [], .nil => .nil
  | ⟨T, l⟩ :: _, v :: _, .cons ⟨hl, hm⟩ h => by
      simp only at hl; subst hl
      have hT : T.Persistent := by
        simp only [stdModel, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hm
        rcases hm with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
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

end BoCa.Fig16.LogRel.Core

end
