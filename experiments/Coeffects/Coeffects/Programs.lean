import Coeffects.Judgment

/-!
# Coeffects — a helper that needs `stdout`

The surface program (a sketch, not parsed):

    fn greet() needs stdout = { put(72); put(105) }       -- "Hi"
    main(inp) = { let c = mk_output(1);
                  let (c, _) = provide c { greet(); greet() };
                  take_output(c) }

`greet` never names the capability: `put` needs `Mut Output`, `greet` sequences two of them,
and `main` sequences two `greet`s.  Each sequencing is the reborrow contraction (`seqD`), and
`provide` is `withbor` form 2 on the capability's cell.

* `d_putD`: `put b` at the demand type, through the `write_byte` extern of SPEC §11.
* `k_greet`, `k_greet2`: the `KDem` derivations.
* `d_main`: `main : Bytes ⊸ F (I32 ⊗ Bytes)` at the context of the three externs, a `CDerives`
  derivation.
* `main_every_run`: `io_every_run` at it, unchanged: with each extern given its model, every run
  from the empty memory, under every allocator, continues to a value at the empty memory.
* `main_eval`: the interpreter runs it and the output stream holds `i H i H` (most recent
  first): "HiHi".
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Coeffects
open BoCa
open BoCa.Fig16
open BoCa.Lifetime (LSub LifeCtx LifeVar LSubst)
open BoCa.Programs (app2 entailsLt_top)
open Optics

/-- `Output`, the payload of the `stdout` capability's cell. -/
abbrev OutT : VTy := .opq .output

abbrev wbT : VTy := externTy (writeByteC OutT)
abbrev mkT : VTy := externTy (mkOutputC OutT)
abbrev tkT : VTy := externTy (takeOutputC OutT)

/-- The externs: `write_byte` (index 0), `mk_output` (1), `take_output` (2). -/
abbrev Γx : Ctx VTy := [⟨wbT, true⟩, ⟨mkT, true⟩, ⟨tkT, true⟩]

/-- The context of the demanding computations: the capability's cell `c` (lent, so dead here),
the input, and the externs. -/
abbrev Γg : Ctx VTy := ⟨.ref OutT, false⟩ :: ⟨bytesTy, true⟩ :: Γx

/-- `put b`, needing `Mut Output`: `Λ. λm. forget (write_byte () (m, b)); ()`, with
`write_byte` at index `k` outside the two binders. -/
def putD (k : Nat) (b : UInt32) : Expr :=
  .val (.lam (.val (.lam (.seq (.app forget (app2 (.var (k + 2)) unit' (.pair (.var 0) (i32E b))))
    unit'))))

theorem bytes_persistent : bytesTy.Persistent := by decide

theorem d_putD (b : UInt32) :
    CDerives LifeCtx.empty Γg (putD 2 b) (.val (demTy OutT 0 LifeCtx.empty.meetOfDom .unit)) := by
  refine .thunkV rfl (.allI (S := .unit) (by decide)
    (fun _ _ hy => LifeCtx.Ok.bound_mentions_false ok_empty rfl hy) ?_ (.ret (.lamV ?_)))
  · intro s hs hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl <;>
      simp_all [VFree, CFree, bytesTy, bytesBody, writeByteC, mkOutputC, takeOutputC, outRep,
        Lifetime.Life.mentions]
  refine .seqV (splitP_left_all _) ?_ (.boxI (.unitI (kill_dead _).toP)
    ⟨Lifetime.LifeCtx.defines_of_wf (wf_var_self _ _ _),
      fun s hs hl => (dead_noLive (kill_dead _) (P := fun _ => False) s hs hl).elim⟩)
  refine appP (A := .mut (.var 0) OutT) ?_ (.forgetMut (by cdeadP))
  refine appP (A := .tensor (.mut (.var 0) OutT) .i32) (pairP (.var (by csoloP)) (d_i32 _ (by cdeadP))) ?_
  rw [show VTy.lolli (.tensor (.mut (.var 0) OutT) .i32) (.mut (.var 0) OutT) =
      VTy.instLife 0 (.var 0) (.lolli (.tensor (.mut (.var 0) OutT) .i32) (.mut (.var 0) OutT)) by
    simp [VTy.instLife, VTy.applyLSub, CTy.applyLSub, Lifetime.Life.applySub, Lifetime.assocFind]]
  exact .allEV (b := .top) (.bangE (.var (by csoloP)))
    (entailsLt_top (u := LifeCtx.empty.meetOfDom) (by simp [Lifetime.LifeCtx.find?_extend]))

theorem ext_persistent : ∀ s ∈ Γx, s.ty.Persistent := by decide

/-- Every live slot of `Γg` goes to both sides. -/
theorem splitΓg : Ctx.SplitP Γg Γg Γg :=
  .dead (.dup bytes_persistent (.dup rfl (.dup rfl (.dup rfl .nil))))

/-- `greet = put 'H'; put 'i'`. -/
def greetE : Expr := app2 seqD (putD 2 72) (putD 2 105)

/-- `greet(); greet()`. -/
def greet2E : Expr := app2 seqD greetE greetE

abbrev greetT : VTy := .tensor .unit .unit
abbrev greet2T : VTy := .tensor greetT greetT

theorem k_greet : KDem OutT 0 LifeCtx.empty Γg greetE greetT :=
  .seq splitΓg (.need rfl (d_putD 72)) (.need rfl (d_putD 105))

theorem k_greet2 : KDem OutT 0 LifeCtx.empty Γg greet2E greet2T :=
  .seq splitΓg k_greet k_greet

/-- `main`'s body at `inp :: Γx`: `let c = mk_output 1; let (c, r) = withbor c greet2;
take_output c`. -/
def mainBody : Expr :=
  elet (.app (.var 2) (i32E 1))
    (.letpair (app2 withbor (.var 0) greet2E) (.app (.var 6) (.var 1)))

def mainE : Expr := .val (.lam mainBody)

theorem d_mainBody :
    CDerives LifeCtx.empty (⟨bytesTy, true⟩ :: Γx) mainBody (.val outRep) := by
  refine .eletV (.dup bytes_persistent (.dup rfl (.dup rfl (.dup rfl .nil))))
    (appP (d_i32 1 (by cdeadP)) (.bangE (.var (by csoloP)))) ?_
  refine .letpairV (A := .ref OutT) (B := greet2T)
    (.left (.dup bytes_persistent (.dup rfl (.dup rfl (.dup rfl .nil))))) ?_ ?_
  · exact provide_wf (y := 1) ok_empty rfl rfl (by decide) (Payload.opq _)
      (.right (.dup bytes_persistent (.dup rfl (.dup rfl (.dup rfl .nil)))))
      (.var (by csoloP)) k_greet2
  · exact appP (A := .ref OutT) (.var (by csoloP)) (.bangE (.var (by csoloP)))

/-- **`main : Bytes ⊸ F (I32 ⊗ Bytes)`** at the externs' context: an ordinary `CDerives`
derivation. -/
theorem d_main :
    CDerives LifeCtx.empty Γx mainE (.comp (.arr bytesTy (.ret outRep))) :=
  .lam (.ret d_mainBody)

/-- The externs' models, in `Γx`'s order. -/
def γx : List Val := [writeByteV, mkOutputV, takeCapV]

theorem γx_models :
    List.Forall₂ (fun s v => s.live = true ∧ (s.ty, v) ∈ stdModel) Γx γx := by
  refine .cons ⟨rfl, ?_⟩ (.cons ⟨rfl, ?_⟩ (.cons ⟨rfl, ?_⟩ .nil)) <;> simp [stdModel]

/-- **Every run is safe and leak-free**, by `io_every_run` unchanged: with each extern given its
model, every run of `main inp` from the empty memory, under every allocator, continues to a
value of `I32 ⊗ Bytes` at the empty memory. -/
theorem main_every_run {ℍ : BoCa.Host} [BoCa.HostIs ℍ] {inp : Val} (hin : BytesV inp)
    {μ₁ : BoLo.Heap} {e₁ : Expr}
    (hs : BoLo.Steps (ℍ := ℍ) Adequacy.emptyMem (.app (substAll γx mainE) (.val inp)) μ₁ e₁) :
    ∃ v : Val, BoLo.Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v) ∧
      ∃ ls δ, vC true outRep ls δ v PMap.empty :=
  io_every_run d_main (by decide) γx_models hin hs

/-- The bytes of a byte-list value. -/
def bytesOf : Expr → Option (List UInt32)
  | .inj₁ .unit => some []
  | .inj₂ (.pair (.prim (.lit (.i32 n))) r) => (bytesOf r).map (n :: ·)
  | _ => none

/-- `main` on the empty input, with each extern given its model. -/
def mainRun : Expr := .app (substAll γx mainE) (.val (bytesVal []))

/-- **The run.**  The interpreter runs `mainRun` to `(1, [i, H, i, H])` (most recent first:
"HiHi" on file descriptor 1) with no cell left. -/
theorem main_eval :
    (match eval mainRun with
      | .value ⟨.pair (.prim (.lit (.i32 1))) bs, _⟩ false => bytesOf bs == some [105, 72, 105, 72]
      | _ => false) = true := by decide

end BoCa.Fig16.LogRel.Core.Coeffects

end
