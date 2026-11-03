import Core.LetDtorSafety

/-!
# Core — `[let]` and `[let-dtor]`  `[spec §62]`

`[let-dtor]` is meant to generalise `[let]`. What is proved, and what keeps `[let]` a rule of its
own:

**The runs agree.** At destructors that are all `none`, `drop_ctx` is `return ()`
(`dropCtxE_none`), and on every exit `letDE (none…) N M` runs as `M to x. N` does, up to
administrative steps:
- return: one step (`[then]`) reaches `M to x. N` itself at `M = return w`, for any destructors
  (`letDE_return_eq_let`);
- raise: three steps reach `K[raise p]` (`letDE_none_raise`), and `M to x. N` is already
  `K[F[raise p]]` with `F` catching nothing of `p`'s name (`let_raise_shape`): the same raise,
  from under the same `K`;
- cancel: three steps reach `K[raise c]` (`letDE_none_cancel`), likewise.

**The rules.** `[let]` at a cancelling row asks `Γ₂` own-free (`hW`); an own-free type has a
destructor at every row once each host type it holds has a declared one (`DropOk.ofOwnFree`): its
derived drop, or `⊗`/`⊕` of them. So `[let]`'s premises, with `[then]`'s row conditions, give
`[let-dtor]` at the same `M` and `N` (`effLet_as_effLetD`), its term `letDT` in place of
`M to x. N`. `[let]` is not the instance of `[let-dtor]` at all-`none` destructors, for three
reasons, each checked:
1. At a row that does not cancel, `[let]` has no `hW` and admits any `Γ₂`, a live `U(F 1)`
   included; `[let-dtor]` types `drop_ctx` even where no exit runs it, and `U(F 1)` has no
   destructor (`not_dropOk_thunkRet`).
2. `[let-dtor]` is `[then]`, and carries `[then]`'s conditions on the row: `Σ.NZ`, `Σ.Uniq`,
   `hfin`, and `Γ₂` banged at `Σ.UnrD` (not only `Σ.Unr`). `[let]`'s term has no frame and
   needs none of them.
3. The terms differ (`thenE` against the application `(λx. N) M`); the runs agree only up to the
   administrative steps above, which `CDerives` does not identify.
A form with both as instances would take the finaliser's premise at `Γ₂` only where `Σ` cancels,
and `[then]`'s row conditions only where there is a frame: a change to `then_compatC`, not made
here.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.BoLo (Heap Steps Step1 Head Kont raiseE opPayload cancelVal cfinE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- With no destructor to run, `drop_ctx` is `return ()`. -/
theorem dropCtxE_none : ∀ (k j : Nat), dropCtxE (List.replicate k none) j = .val .unit
  | 0, _ => rfl
  | k + 1, j => dropCtxE_none k (j + 1)

/-- **The return exit is `[let]`'s**: at `M = return w`, `[let-dtor]`'s term steps (`[then]`) to
`M to x. N`, for any destructors.  `[spec §62]` -/
theorem letDE_return_eq_let (μ : Heap) (ds : List (Option Expr)) (N : Expr) (w : Val) (K : Kont) :
    Step1 (ℍ := ℍ) μ (K.plug (letDE ds N (.val w))) μ (K.plug (.app (.val (.lam N)) (.val w))) :=
  ⟨K, _, _, rfl, rfl, Head.uthen μ (.lam N) (.lam (dropCtxE ds 1)) w⟩

/-- **The raise exit at no destructors**: three administrative steps to the same raise under the
same context `K`.  `[spec §62]` -/
theorem letDE_none_raise (μ : Heap) (k : Nat) (N : Expr) {n i : UInt32} {v : Val} (K K' : Kont)
    (hn : n ≠ 0) (hK : K'.Catches n = false) :
    Steps (ℍ := ℍ) μ (K.plug (letDE (List.replicate k none) N (K'.plug (raiseE (.val (opPayload n i v))))))
      μ (K.plug (raiseE (.val (opPayload n i v)))) := by
  refine .more (letDE_finalise μ _ N n i v K K' hn hK) ?_
  rw [dropCtxE_none]
  refine .more ⟨K.comp (.seq .hole (raiseE (.val (opPayload n i v)))), _, _, ?_, ?_,
    Head.beta μ (.val .unit) .unit⟩ (.one ⟨K, _, _, rfl, rfl, Head.seq μ _⟩)
  · simp [Kont.plug_comp, Kont.plug]
  · simp [Kont.plug_comp, Kont.plug, Expr.subst]

/-- **`[let]`'s term at a raise**: the raise under `K`, the binding frame and `K'`, which catch
nothing of its name.  `[spec §62]` -/
theorem let_raise_shape (N : Expr) (K K' : Kont) (r : Expr) {n : UInt32}
    (hK : K'.Catches n = false) :
    K.plug (.app (.val (.lam N)) (K'.plug r)) = (K.comp (.appR (.val (.lam N)) K')).plug r ∧
      Kont.Catches n (.appR (.val (.lam N)) K') = false := by
  refine ⟨by simp [Kont.plug_comp, Kont.plug], ?_⟩
  simp [Kont.Catches, hK]

/-- **The cancel exit at no destructors**: three administrative steps to the same cancel under
the same context `K`.  `[spec §62]` -/
theorem letDE_none_cancel (μ : Heap) (k : Nat) (N : Expr) {err : Option Val} (K K' : Kont)
    (hK : K'.Catches 0 = false) :
    Steps (ℍ := ℍ) μ (K.plug (letDE (List.replicate k none) N (K'.plug (raiseE (.val (cancelVal err))))))
      μ (K.plug (raiseE (.val (cancelVal err)))) := by
  refine .more (letDE_finaliseCancel μ _ N err K K' hK) ?_
  rw [dropCtxE_none]
  refine .more ⟨K.comp (.appR (.app (.val (.prim .cfin)) (.val (cancelVal err))) .hole), _, _, ?_,
    ?_, Head.beta μ (.val .unit) .unit⟩ (.one ⟨K, _, _, rfl, rfl, Head.cfret μ err .unit⟩)
  · simp [Kont.plug_comp, Kont.plug, cfinE]
  · simp [Kont.plug_comp, Kont.plug, cfinE, Expr.subst]

/-! ### The rules -/

/-- **An own-free type has a destructor**, at every row, once each host type in it has a declared
one: its derived drop, or `⊗`/`⊕` of them.  `[spec §62]` -/
theorem DropOk.ofOwnFree {Δ : LifeCtx} {SD : Row} {decl : Opaque → Option Expr}
    (hhost : ∀ k, k.Host → DropOk Δ SD decl (.opq k)) :
    ∀ {T : VTy}, T.OwnFree → DropOk Δ SD decl T
  | _, .unit => .derived rfl .unit
  | _, .zero => .derived rfl .zero
  | _, .int _ => .derived rfl .int
  | _, .unk => .derived rfl .unk
  | _, .opq k hk => hhost k hk
  | _, .bang _ => .derived rfl .bang
  | _, .imm _ _ => .derived rfl .imm
  | _, .mut _ _ => .derived rfl .mut
  | _, .tensor ha hb => .tensor (DropOk.ofOwnFree hhost ha) (DropOk.ofOwnFree hhost hb)
  | _, .sum ha hb => .sum (DropOk.ofOwnFree hhost ha) (DropOk.ofOwnFree hhost hb)

/-- **`[let]`'s premises give `[let-dtor]`**: at a cancelling row, `[let]`'s `hW` makes `Γ₂`
own-free, so each of its live slots has a destructor (`DropOk.ofOwnFree`); with `[then]`'s
conditions on the row, `[let-dtor]` types the same `M` and `N`.  `[spec §62]` -/
theorem effLet_as_effLetD {Δ : LifeCtx} {Γ Γ₁ Γ₂ : Ctx VTy} {M N : Expr} {A B : VTy}
    {S : Row} {decl : Opaque → Option Expr}
    (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hW : S.Cancels → Γ₂.OwnFree) (hc : S.Cancels)
    (hhost : ∀ k, k.Host → DropOk Δ [] decl (.opq k))
    (hNZ : S.NZ) (hUq : S.Uniq) (hU : S.UnrD → Ctx.Banged Γ₂)
    (hfin : ∀ n i o o', Row.find S n i = some o → Row.find S n i = some o' →
      o.finRead = true → ThenLe o.fin [] o'.fin)
    (hM : CDerives Δ Γ₁ M (.comp (CTy.effOf S A)))
    (hN : CDerives Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B))) :
    CDerives Δ Γ (letDT decl Γ₂ N M) (.comp (CTy.effOf S B)) :=
  CDerives.effLetD (SD := []) hs hNZ hUq hU (RowLe.refl S) (RowLe.nil S)
    (fun ⟨_, h, _⟩ => by cases h) rfl hfin
    (fun s hs hl => .inr (DropOk.ofOwnFree hhost (hW hc s hs hl))) hM hN

/-- **`U(F 1)` has no destructor**: a thunk of a computation that is not `C & D` is disposed of
only by running it. `[let]` at a row that does not cancel holds such a slot; `[let-dtor]` does
not.  `[spec §12, §62]` -/
theorem not_dropOk_thunkRet {Δ : LifeCtx} {SD : Row} {decl : Opaque → Option Expr} :
    ¬ DropOk Δ SD decl (.thunk (.ret .unit)) := by
  intro h
  cases h with
  | derived _ hT => cases hT

end BoCa.Fig16.LogRel.Core

end
