import Core.Inversions
import Core.EffPrograms

/-!
# Core — programs no derivation types  `[spec §19]`

Four programs that `CDerives` types at no context and no judgement, each refused by inversion
(`Core/Inversions.lean`).  Three are handlers whose clause tuple `(cl, ())` is `[handle]`'s, so the
clause is at its clause type (`handleWith_clause`, `clause_lin`), and its `κ` at a linear operation
is at `kTy`, a thunk of an `&`.

* **AT13** (`not_der_at13`): a clause that forgets `κ`.  `forget`'s axioms take `!`, `Imm`, `Mut`,
  `Unk` and `ArrayImm`, and as a λ it drops its argument only at a persistent type
  (`not_forget_kappa`).
* **AT06** (`not_der_at06`): a clause that releases a cell the handled body also releases.  The
  clause is at a `!` type, so typed over a persistent context, and the cell's slot is at a view of a
  `Ref`.
* **AT08** (`not_der_at08`): a continuation read twice out of a cell.  `alloc` stores a view of
  `κ`'s type, and `swap` is typed at its axiom alone (`der_swap`), so the first `swap` reads that
  view out as `k₁`; the second `swap` and `k₁`'s resume use `k₁` on the two sides of a split, so its
  slot is persistent, and a view of a thunk is not.  The same clause with the copy used once is
  typed (`d_at08Once`) and every run of it ends at `()` with the memory empty (`at08Once_runs`):
  moving `κ` through a cell is allowed, and using it twice is not.  `at08Once` is the kernel program
  `at08-once`.
* **AT05** (`not_der_at05`): an answering handler whose body uses its capability twice.  The
  callback reaches `withborU dFlag`'s second argument.  Typed as a λ, `withborU dFlag` uses its
  first argument on both sides of its `then`, so that argument is persistent, while the cell is a
  `Ref`; typed by an unwinding constant, the callback is at `∀'x ⊏ @b. L ⊸ F_Σ(['x] B)` with `L` a
  borrow, and `λm. (m, m)` uses `m` twice.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Rejections
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Inversions
open BoCa.Lifetime (LifeCtx)
open BoCa.Programs (alloc' free')
open BoCa.BoLo (performE)
open BoCa.Fig16.LogRel.Core.EffPrograms (dFlag d_hrS)

/-! ### The handlers -/

/-- `Foo : 1 ↠^lin 1`, the operation `0` of the name `5`. -/
def fooSig : OpSig := ⟨5, 0, .lin, .unit, .unit, .ret .unit⟩

/-- `foo ()`. -/
def fooE : Expr := performE (opArgE 5 0 (.val .unit))

/-- `handle_n e` with the identity answer clause and the one clause `cl`, its operation's
qualifier `q`: `hs ← (cl, ()); hr ← λx. x; hnd (n, ([q], (hr, hs))) e`. -/
def handleWith (n : UInt32) (q : Qual) (cl : Expr) (e : Expr) : Expr :=
  bindE (.pair cl (.val .unit)) (bindE (.val (.lam (.var 0))) (hndTerm n [q] 0 1 e))

/-- A term is no λ-constant, by unfolding, the handlers' terms included. -/
macro "not_constH" : tactic => `(tactic| ((try simp only [handleWith, fooE, dropB]) <;> not_const))

/-- A term is no `⟨M, N⟩`, by unfolding, the handlers' terms included. -/
macro "not_withPairH" : tactic => `(tactic| (intro M₁ M₂ h; simp [withPair, Expr.val, Val.lam,
    bindE, hndTerm, hndExpr, Val.unit, Val.prim, Val.i32, Val.inj₁, Val.inj₂, Val.pair, fooE, dropB,
    BoCa.BoLo.performE, opArgE, handleWith, free', alloc'] at h))

/-! ### A continuation is not forgotten -/

/-- A type whose head is a thunk of an `&`: what `κ` is at `lin` and `aff`. -/
theorem kview {C₁ C₂ : CTy} {A : VTy} (h : VView (.thunk (.amp C₁ C₂)) A) :
    A.persistent = false ∧ Hnf A (.thunk (.amp C₁ C₂)) := by
  have hh := h.hnf_of (hnf_self (fun _ _ h => by cases h) (fun _ h => by cases h))
    (fun _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => by cases h)
  exact ⟨by rw [hh.persistent]; rfl, hh⟩

/-- A type with a thunk head is none of `forget`'s arguments, and no `1`. -/
theorem kview_not {C : CTy} {A : VTy} (h : Hnf A (.thunk C)) :
    (∀ X, A ≠ .bang X) ∧ (∀ a X, A ≠ .imm a X) ∧ (∀ a X, A ≠ .mut a X) ∧ A ≠ .unk ∧
      (∀ L, A ≠ .fam L) ∧ A ≠ .unit := by
  refine ⟨fun X hA => ?_, fun a X hA => ?_, fun a X hA => ?_, fun hA => ?_, fun L hA => ?_,
    fun hA => ?_⟩ <;> subst hA <;>
    have := h.eq_self (fun _ _ h => by cases h) (fun _ h => by cases h) <;> cases this

/-- **`forget κ` has no derivation at `1`** when `κ`'s slot is a thunk of an `&` (`kTy` at `lin` and
`aff`): `forget`'s axioms take `!`, `Imm`, `Mut`, `Unk` and `ArrayImm`, and as a λ it drops its
argument only at a persistent type. -/
theorem not_forget_kappa {Δ : LifeCtx} {Γ : Ctx VTy} {C₁ C₂ : CTy}
    (h : CDerives Δ Γ (.app forget (.var 0)) (.val .unit))
    (hΓ : ∀ T, Γ[0]? = some ⟨T, true⟩ → T = .thunk (.amp C₁ C₂)) : False := by
  obtain ⟨j₀, hb, hr⟩ := der_app h _ _ rfl
  rcases hb with ⟨Γ₁, Γ₂, A, B, hs, hY, hf, rfl⟩ | ⟨Γ₁, Γ₂, i, A, C, hi, hs, hf, hx, rfl⟩ |
    ⟨N, Γ₁, Γ₂, A, S, C, hN, hs, hY, hU, rfl⟩ | ⟨N, b, C, -, hb, -⟩ |
    ⟨-, -, -, -, hu, -⟩ | ⟨-, -, -, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨hu, -⟩ | hX
  · -- `⊸E`: `forget` at `A ⊸ B`, `κ` at `A`
    obtain ⟨T, hT, hcT⟩ := der_var hY 0 rfl
    obtain rfl := hΓ T (splitP_le_left hs _ _ hT)
    obtain ⟨hAp, hAh⟩ := kview hcT.val
    obtain ⟨hb, hi, hm, hu, hfam, hun⟩ := kview_not hAh
    rcases der_lam hf .unit rfl with ⟨A', D, hM, hcl⟩ | ⟨S, B', hM, hcl⟩ |
      ⟨x, b, Δ', S, C, hM, hcl⟩ | ⟨A', hM, hcl⟩ | ⟨M₁, M₂, hwp⟩ | hx
    · have := hcl.val_thunk
      simp only [CTy.arr.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      rcases der_unit hM rfl with ⟨hd, -⟩ | hr'
      · have := deadP_slot hd (k := 0) rfl
        simp [VTy.Persistent, hAp] at this
      · have := hr'.rigid rigid_top; cases this
    · have := hcl.val_thunk
      simp only [CTy.arr.injEq] at this
      exact hun this.1.symm
    · have := hcl.val_thunk; cases this
    · rcases hcl with hcl | ⟨-, hcl⟩
      · have := vview_thunk hcl; cases this
      · have := vview_bang_thunk hcl; cases this
    · simp [withPair, Expr.val, Val.lam] at hwp
    · rcases hx with ⟨-, T₀, hT₀, hc₀⟩ | ⟨d, he, -⟩ | ⟨ho, -⟩
      · rcases hT₀ with ⟨X, rfl, hX⟩ | ⟨a, A', rfl⟩
        · have := vview_thunk hc₀
          simp only [CTy.arr.injEq] at this
          obtain ⟨rfl, -⟩ := this
          rcases hX with ⟨X', rfl⟩ | ⟨a, X', rfl⟩ | ⟨a, X', rfl⟩ | rfl
          · exact hb X' rfl
          · exact hi a X' rfl
          · exact hm a X' rfl
          · exact hu rfl
        · have := vview_bang_thunk hc₀
          simp only [CTy.arr.injEq] at this
          exact hfam _ this.1.symm
      · simp [withborUE, Expr.val, Val.lam] at he
      · simp only [OtherLam, copy, swap, withbor, withload, withswap, sizeV, replaceV, arrLenV,
          swapV,
          foldImmV, foldOwnV, foldReuseV, unfoldV, Expr.val, Val.lam, lam2, elet, unit', v0, v1, v2,
          v3, Expr.lam.injEq, reduceCtorEq, exists_false, or_self] at ho
  · -- `[app]`: `forget` at `κ ⊸ C`, typed at `κ`'s slot
    cases hi
    obtain rfl := hΓ A (splitP_le_right hs _ _ (soloP_le hx))
    obtain ⟨S', Y', rfl⟩ := hr.comp_val
    rcases der_lam hf .unit rfl with ⟨A', D, hM, hcl⟩ | ⟨S, B', hM, hcl⟩ |
      ⟨x, b, Δ', S, C, hM, hcl⟩ | ⟨A', hM, hcl⟩ | ⟨M₁, M₂, hwp⟩ | hx'
    · have := hcl.comp_rigid (rigid_arr _ _)
      simp only [CTy.arr.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      rcases der_unit hM rfl with ⟨hd, -⟩ | hr'
      · have := deadP_slot hd (k := 0) rfl
        simp [VTy.Persistent, VTy.persistent] at this
      · have := (hr'.rigid rigid_top)
        simp only [Jdg.comp.injEq] at this
        exact effOf_ne_top _ _ this
    · have := hcl.comp_rigid (rigid_arr _ _)
      simp only [CTy.arr.injEq] at this
      cases this.1
    · have := hcl.comp_rigid (rigid_arr _ _); cases this
    · rcases hcl with hcl | ⟨-, hcl⟩
      · obtain ⟨S, Y, he, -⟩ := hcl; exact effOf_ne_arr _ _ _ _ he.symm
      · obtain ⟨S, Y, he, -⟩ := hcl; exact effOf_ne_arr _ _ _ _ he.symm
    · simp [withPair, Expr.val, Val.lam] at hwp
    · have := hx'.not_comp; simp [CTy.isRet] at this
  · -- `[let]`: `κ` at a row over `A`, `()` under `A`
    simp only [forget, Expr.val, Val.lam, unit', Val.unit, Expr.lam.injEq] at hN
    subst hN
    obtain ⟨S', Y', rfl⟩ := hr.comp_val
    obtain ⟨T, hT, hcT⟩ := der_var hY 0 rfl
    obtain rfl := hΓ T (splitP_le_left hs _ _ hT)
    rcases der_unit hU rfl with ⟨hd, -⟩ | hr'
    · have hAp := deadP_slot hd (k := 0) rfl
      rcases hcT with ⟨S'', Y, he, hv⟩ | ⟨C', hC', -, hr''⟩
      · obtain ⟨-, rfl⟩ := effOf_inj he
        have := (kview hv).1
        simp [VTy.Persistent, this] at hAp
      · cases hC'
        obtain ⟨D', he, hD'⟩ := hr''.ampNu (.inl ⟨_, _, rfl⟩)
        simp only [Jdg.comp.injEq] at he
        rcases hD' with ⟨_, _, h'⟩ | ⟨_, h'⟩
        · exact effOf_ne_amp _ _ _ _ (he.trans h')
        · exact effOf_ne_nu _ _ _ (he.trans h')
    · have := hr'.rigid rigid_top
      simp only [Jdg.comp.injEq] at this
      exact effOf_ne_top _ _ this
  · cases hb
  · cases hu
  · cases hu
  · cases hu
  · cases hu
  · cases hu
  · rcases hX with hX | hX | ⟨Z, hX⟩ | ⟨Z, hX⟩ <;> simp [forget, Expr.val, Val.lam] at hX

/-! ### The handler of the clause tuple `(cl, ())` -/

/-- **The clause tuple's type**: in `handleWith n q cl M` typed at any judgement, the tuple
`(cl, ())` is read at a row over a type viewing to `clausesTy S R E`, whose tags are `[q]`. -/
theorem handleWith_clause {Δ : LifeCtx} {Γ : Ctx VTy} {n : UInt32} {q : Qual} {cl M : Expr}
    {j : Jdg} (h : CDerives Δ Γ (handleWith n q cl M) j)
    (hcl' : ∀ b, Expr.pair cl .unit ≠ .lam b)
    (hNc : NotConst (.lam (bindE (.val (.lam (.var 0))) (hndTerm n [q] 0 1 M))))
    (hHc : NotConst (.lam (hndTerm n [q] 0 1 M)))
    (hM : ((M.subst 0 (Val.lam (.var 0))).shift 1 0) = M) :
    ∃ Γ₁ S₁ T₁ S R E fs, CtxLe Γ₁ Γ ∧ CDerives Δ Γ₁ (.pair cl .unit) (.comp (CTy.effOf S₁ T₁)) ∧
      VView T₁ (clausesTy S R E fs) ∧ E.map Prod.fst = [q] := by
  obtain ⟨Γ₁, Γ', T₁, b, S₁, j₁, hle₁, -, hP, hN₁⟩ := der_bind (M := .pair cl .unit) h
    (fun i h => by cases h) (fun b h => hcl' b h) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h) (by not_withPairH) hNc
  have hH : ∃ Γ₄ j₄ X, (∀ T, Γ₄[1]? = some ⟨T, true⟩ → T = T₁) ∧
      CDerives Δ Γ₄ (hndExpr n [q] (.pair X (.var 1)) M) j₄ := by
    rcases der_bindLam (N := hndTerm n [q] 0 1 M) (b := .var 0) hN₁ (by not_withPairH) hHc with
      ⟨_, Γ'', T₀, b₀, _, j'', _, hle'', _, hH5⟩ | ⟨j'', hH5⟩
    · refine ⟨_, _, .var 0, fun T hT => ?_, hH5⟩
      have := hle'' 0 T (by simpa using hT)
      simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq] at this
      exact this.1.symm
    · refine ⟨⟨.unit, false⟩ :: ⟨T₁, b⟩ :: Γ', j'', .lam (.var 0), fun T hT => ?_, ?_⟩
      · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          Slot.mk.injEq] at hT
        exact hT.1.symm
      · have he : ((hndTerm n [q] 0 1 M).subst 0 (Val.lam (.var 0))).shift 1 0 =
            hndExpr n [q] (.pair (.lam (.var 0)) (.var 1)) M := by
          simp only [hndTerm, hndExpr, Expr.subst, Expr.shift, hM]
          simp [qualsVal, Val.pair, Val.i32, Val.unit, Val.prim, Val.lam, Expr.subst, Expr.shift]
        rw [he] at hH5
        exact hH5
  obtain ⟨Γ₄, j₄, X, hslot, hH5⟩ := hH
  obtain ⟨T, S, R, E, fs, hT, hv, hE⟩ := hnd_clauses hH5
  obtain rfl := hslot T hT
  exact ⟨Γ₁, S₁, T, S, R, E, fs, hle₁, hP, hv, hE⟩

/-- The clause tuple's clause is read at the clause type of its handler's one operation: at a linear
operation, `!U(A ⊗ kTy ⊸ F_Σ R)`. -/
theorem clause_lin {Δ : LifeCtx} {Γ : Ctx VTy} {cl : Expr} {S₁ : Row} {T₁ : VTy} {S : Row}
    {R : VTy} {E : List (Qual × VTy × VTy)} {fs : Nat → CTy}
    (hP : CDerives Δ Γ (.pair cl .unit) (.comp (CTy.effOf S₁ T₁)))
    (hv : VView T₁ (clausesTy S R E fs)) (hE : E.map Prod.fst = [.lin]) :
    ∃ Γ' A₀ B₀, CtxLe Γ' Γ ∧ CDerives Δ Γ' cl
      (.val (.bang (.thunk (.arr (.tensor A₀ (.thunk (.amp (.arr B₀ (CTy.effOf S R)) .top)))
        (CTy.effOf S R))))) := by
  obtain ⟨⟨q, A₀, B₀⟩, rfl⟩ : ∃ e, E = [e] := by
    cases E with
    | nil => simp at hE
    | cons e E' =>
        cases E' with
        | nil => exact ⟨e, rfl⟩
        | cons => simp at hE
  simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hE
  subst hE
  obtain ⟨Γ', A, B, hle, hcl, hv'⟩ := pair_row hP (fun c h => by cases h)
  obtain ⟨rfl, -⟩ := vview_tensor (hv'.trans hv)
  have hty : clauseTy S R (.lin, A₀, B₀) (fs 0) =
      .bang (.thunk (.arr (.tensor A₀ (.thunk (.amp (.arr B₀ (CTy.effOf S R)) .top)))
        (CTy.effOf S R))) := by
    simp [clauseTy, kTy]
  rw [hty] at hcl
  exact ⟨Γ', A₀, B₀, hle, hcl⟩

/-! ### AT13: `forget κ` -/

/-- AT13's clause: `λ(a, κ). forget κ; ()`. -/
abbrev at13Cl : Expr := .lam (.letpair (.var 0) (.seq (.app forget (.var 0)) unit'))

/-- **AT13**: `forget κ`.  A linear or affine continuation has no weakening, and the `forget`
constants are at `Imm`, `Mut`, `!` and `Unk`; discarding `κ` is an explicit cancel. -/
def at13 : Expr := handleWith 5 .lin at13Cl fooE

/-- **AT13 has no derivation**: the clause's `κ` is at `kTy` at `lin` (the clause tuple is
`[handle]`'s), and `forget κ` has no derivation there (`not_forget_kappa`). -/
theorem not_der_at13 {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg} : ¬ CDerives Δ Γ at13 j := by
  intro h
  obtain ⟨Γ₁, S₁, T₁, S, R, E, fs, -, hP, hv, hE⟩ := handleWith_clause (cl := at13Cl) h
    (fun b h => by cases h) (by not_constH) (by not_constH) rfl
  obtain ⟨Γ_cl, A₀, B₀, -, hCL⟩ := clause_lin hP hv hE
  obtain ⟨-, hB⟩ := lam_bang hCL (fun h => by cases h) (by not_withPairH) (by not_constH)
  obtain ⟨Γ₆₁, Γ₆₂, A₆, B₆, C₆, hs₆, hV₆, hM₆, -⟩ := der_letpair hB _ _ rfl
  obtain ⟨T₆, hT₆, hc₆⟩ := der_var hV₆ 0 rfl
  have hT := splitP_le_left hs₆ 0 T₆ hT₆
  simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq, and_true] at hT
  subst hT
  obtain ⟨-, rfl⟩ := vview_tensor hc₆.val
  obtain ⟨Γ₇₁, Γ₇₂, C₇, hs₇, hF, -, -⟩ := der_seq hM₆ _ _ rfl
  refine not_forget_kappa (C₁ := .arr B₀ (CTy.effOf S R)) (C₂ := .top) hF (fun T hT => ?_)
  have := splitP_le_left hs₇ 0 T hT
  simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq, and_true] at this
  exact this.symm

/-! ### AT06: a clause captures the linear cell -/

/-- `alloc (inj₁ ())`, read at a row, is at a view of a `Ref`. -/
theorem alloc_row {Δ : LifeCtx} {Γ : Ctx VTy} {S : Row} {T : VTy}
    (h : CDerives Δ Γ (.app alloc' (.inj₁ unit')) (.comp (CTy.effOf S T))) :
    ∃ A, VView (.ref A) T := by
  obtain ⟨j₀, hb, hr⟩ := der_app h _ _ rfl
  rcases hb with ⟨Γ₁, Γ₂, A, B, hs, hY, hf, rfl⟩ | ⟨-, -, i, -, -, hi, -⟩ |
    ⟨N, -, -, -, -, -, hN, -⟩ | ⟨N, b, C, hN, -⟩ |
    ⟨-, -, -, -, hu, -⟩ | ⟨-, -, -, -, hu, -⟩ | ⟨C, D, -, hX, rfl⟩ | ⟨-, -, hu, -⟩ | ⟨hu, -⟩ | hX
  · obtain ⟨A₀, hc⟩ := der_prim_alloc hf rfl
    have := vview_thunk hc
    simp only [CTy.arr.injEq, CTy.ret.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    obtain ⟨S', Y, he, hY'⟩ := (ValCls.refl (.ref A₀)).reach hr
    obtain ⟨-, rfl⟩ := effOf_inj he
    exact ⟨A₀, hY'⟩
  · cases hi
  · cases hN
  · cases hN
  · cases hu
  · cases hu
  · obtain ⟨A₀, S', Y, he, -⟩ := der_prim_alloc hX rfl
    exact (effOf_ne_amp _ _ _ _ he.symm).elim
  · cases hu
  · cases hu
  · rcases hX with hX | hX | ⟨Z, hX⟩ | ⟨Z, hX⟩ <;> cases hX

/-- A view of a `Ref` is no `!`. -/
theorem vview_ref_bang {A X : VTy} (h : VView (.ref A) (.bang X)) : False := by
  have := (h.hnf_of (hnf_self (fun _ _ h => by cases h) (fun _ h => by cases h))
    (fun _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => by cases h)).eq_self
    (fun _ _ h => by cases h) (fun _ h => by cases h)
  cases this

/-- AT06's clause: `λ(a, κ). drop (free c); κ.resume ()`, `c` the cell bound outside. -/
abbrev at06Cl : Expr :=
  .lam (.letpair (.var 0) (.seq (dropB (.app free' (.var 3)))
    (.app (.app (.var 0) (.val (.inj₁ .unit))) (.val .unit))))

/-- AT06's handled body: `foo (); drop (free c)`. -/
abbrev at06Body : Expr := bindE fooE (dropB (.app free' (.var 3)))

/-- **AT06**: a clause that writes a place the suspended body uses.  The clause captures the cell
`c`, which the body also releases; clauses are `!U`, so they capture only persistent values, and `c`
is linear. -/
def at06 : Expr := bindE (.app alloc' (.inj₁ unit')) (handleWith 5 .lin at06Cl at06Body)

/-- **AT06 has no derivation**: the clause is in `[handle]`'s clause tuple, so at a `!` type, typed
over a persistent context; it uses the cell `c`, whose slot is a view of a `Ref`. -/
theorem not_der_at06 {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg} : ¬ CDerives Δ Γ at06 j := by
  intro h
  obtain ⟨Γ₁, Γ', T_c, b_c, S, j', -, -, hA, hN⟩ := der_bind (M := .app alloc' (.inj₁ unit')) h
    (fun i h => by cases h) (fun b h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h) (by not_withPairH) (by not_constH)
  obtain ⟨A₀, hvc⟩ := alloc_row hA
  obtain ⟨Γ_p, S₁, T₁, S', R, E, fs, hle_p, hP, hv, hE⟩ :=
    handleWith_clause (cl := at06Cl) (M := at06Body) hN (fun b h => by cases h) (by not_constH)
      (by not_constH) rfl
  obtain ⟨Γ_cl, A₁, B₁, hle_cl, hCL⟩ := clause_lin hP hv hE
  obtain ⟨hp, hB⟩ := lam_bang hCL (fun h => by cases h) (by not_withPairH) (by not_constH)
  obtain ⟨T, hT⟩ := fv_live hB 1 (by simp [Expr.HasVar, dropB, free', Expr.val, Val.prim, Val.inj₁,
    Val.unit])
  have hT' : Γ_cl[0]? = some ⟨T, true⟩ := by simpa using hT
  obtain ⟨X, rfl⟩ := persistent_slot hp hT'
  have := hle_p 0 _ (hle_cl 0 _ hT')
  simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq] at this
  obtain ⟨rfl, -⟩ := this
  exact vview_ref_bang hvc

/-! ### AT08: a continuation read twice out of a cell -/

/-- A view of a `Ref` that is a `Ref` has its content. -/
theorem vview_ref {A A' : VTy} (h : VView (.ref A) (.ref A')) : A = A' := by
  have := h.eq_of_heads (fun _ _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
    (fun _ _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => by cases h)
    (fun _ h => by cases h)
  cases this; rfl

/-- **`alloc x`, `x` a variable, read at a row**: `x` is read at `A`, and the row's type is a view
of `Ref A`. -/
theorem alloc_var_row {Δ : LifeCtx} {Γ : Ctx VTy} {i : Nat} {S : Row} {T : VTy}
    (h : CDerives Δ Γ (.app alloc' (.var i)) (.comp (CTy.effOf S T))) :
    ∃ Γ₁ A, CtxLe Γ₁ Γ ∧ CDerives Δ Γ₁ (.var i) (.val A) ∧ VView (.ref A) T := by
  obtain ⟨j₀, hb, hr⟩ := der_app h _ _ rfl
  rcases hb with ⟨Γ₁, Γ₂, A, B, hs, hY, hf, rfl⟩ | ⟨Γ₁, Γ₂, i', A, C, hi, hs, hf, hx, rfl⟩ |
    ⟨N, -, -, -, -, -, hN, -⟩ | ⟨N, b, C, hN, -⟩ |
    ⟨-, -, -, -, hu, -⟩ | ⟨-, -, -, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨hu, -⟩ | hX
  · obtain ⟨A₀, hc⟩ := der_prim_alloc hf rfl
    have := vview_thunk hc
    simp only [CTy.arr.injEq, CTy.ret.injEq] at this
    obtain ⟨rfl, rfl⟩ := this
    obtain ⟨S', Y, he, hY'⟩ := (ValCls.refl (.ref A₀)).reach hr
    obtain ⟨-, rfl⟩ := effOf_inj he
    exact ⟨Γ₁, A₀, splitP_le_left hs, hY, hY'⟩
  · obtain ⟨A₀, hc⟩ := der_prim_alloc hf rfl
    have := hc.comp_isRet
    simp [CTy.isRet] at this
  · cases hN
  · cases hN
  · cases hu
  · cases hu
  · cases hu
  · cases hu
  · cases hu
  · rcases hX with hX | hX | ⟨Z, hX⟩ | ⟨Z, hX⟩ <;> cases hX

/-- AT08's clause. -/
abbrev at08Cl : Expr :=
  .lam (.letpair (.var 0)
    (bindE (.app alloc' (.var 0))
      (.letpair (.app (.app swap (.var 0)) unit')
        (.letpair (.app (.app swap (.var 1)) (.var 0))
          (bindE (.app free' (.var 1))
            (bindE (.app (.app (.var 3) (.val (.inj₁ .unit))) (.var 1))
              (.seq (.var 0) (.app (.app (.var 1) (.val (.inj₁ .unit))) (.var 8)))))))))

/-- **AT08**: a continuation in a shared cell, read twice.  The clause stores `κ` in a cell, reads
it out with `swap` (leaving `()`), puts the copy `k₁` back with a second `swap`, reads it out again
with `free` as `k₂`, and resumes both, `k₁` at the cell's old `()` and `k₂` at the operation's
argument:

    op (a, κ) ⇒ c ← alloc κ; (c, k₁) ← swap c (); (c, u) ← swap c k₁; k₂ ← free c;
                r ← resume k₁ u; r; resume k₂ a

The two `swap`s are a `load` of the cell. -/
def at08 : Expr := handleWith 5 .lin at08Cl fooE

/-- **AT08 has no derivation**: the clause's `κ` is at `kTy` at `lin`, a thunk of an `&` (the
clause tuple is `[handle]`'s).  `alloc` stores a view of it; `swap` is typed at its axiom alone, so
the first `swap` reads that view out as `k₁`.  The second `swap` uses `k₁` and so does `k₁`'s
resume, on the two sides of a split: `k₁`'s slot is persistent, and a view of a thunk is not. -/
theorem not_der_at08 {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg} : ¬ CDerives Δ Γ at08 j := by
  intro h
  obtain ⟨Γ₁, S₁, T₁, S, R, E, fs, -, hP, hv, hE⟩ := handleWith_clause (cl := at08Cl) h
    (fun b h => by cases h) (by not_constH) (by not_constH) rfl
  obtain ⟨Γ_cl, A₀, B₀, -, hCL⟩ := clause_lin hP hv hE
  obtain ⟨-, hB⟩ := lam_bang hCL (fun h => by cases h) (by not_withPairH) (by not_constH)
  -- `(a, κ)`: `κ`'s slot is at `kTy` at `lin`
  obtain ⟨Γ₆₁, Γ₆₂, A₆, B₆, C₆, hs₆, hV₆, hM₆, -⟩ := der_letpair hB _ _ rfl
  obtain ⟨T₆, hT₆, hc₆⟩ := der_var hV₆ 0 rfl
  have hT := splitP_le_left hs₆ 0 T₆ hT₆
  simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq, and_true] at hT
  subst hT
  obtain ⟨-, rfl⟩ := vview_tensor hc₆.val
  -- `c ← alloc κ`: the cell holds a view `Aκ` of `κ`'s type, which is not persistent
  obtain ⟨Γ₇, Γ₇', T₇, b₇, S₇, j₇, hle₇, -, hA₇, hN₇⟩ := der_bind hM₆ (fun i h => by cases h)
    (fun b h => by cases h) (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (by not_withPairH) (by not_constH)
  obtain ⟨Γκ, Aκ, hleκ, hκ, hcell⟩ := alloc_var_row hA₇
  obtain ⟨Tκ, hTκ, hcκ⟩ := der_var hκ 0 rfl
  have hTκ' := hle₇ 0 Tκ (hleκ 0 Tκ hTκ)
  simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq, and_true] at hTκ'
  subst hTκ'
  obtain ⟨hAκ, -⟩ := kview hcκ.val
  -- `(c₁, k₁) ← swap c ()`: `k₁` is at the cell's content type
  obtain ⟨Γ₈₁, Γ₈₂, A₈, B₈, C₈, hs₈, hV₈, hM₈, -⟩ := der_letpair hN₇ _ _ rfl
  obtain ⟨Γc, Ac, Bc, hlec, hc, hcl⟩ := der_swap_app hV₈ (fun h => by cases h) (fun h => by cases h)
  obtain ⟨rfl, rfl⟩ := vview_tensor hcl
  obtain ⟨Tc, hTc, hcc⟩ := der_var hc 0 rfl
  have hTc' := splitP_le_left hs₈ 0 Tc (hlec 0 Tc hTc)
  simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq] at hTc'
  obtain ⟨rfl, -⟩ := hTc'
  obtain rfl := vview_ref (hcell.trans hcc.val)
  -- `(c₂, u) ← swap c₁ k₁`: `k₁` is used here and by its resume
  obtain ⟨Γ₉₁, Γ₉₂, A₉, B₉, C₉, hs₉, hV₉, hM₉, -⟩ := der_letpair hM₈ _ _ rfl
  obtain ⟨T₁, hT₁⟩ := fv_live hV₉ 0 (by simp [Expr.HasVar])
  obtain ⟨T₂, hT₂⟩ := fv_live hM₉ 2 (by simp [Expr.HasVar, bindE, Expr.val, Val.lam, Val.inj₁,
    Val.unit])
  have hp := splitP_both hs₉ hT₁ (slot_succ₂ hT₂)
  have hT₁' := splitP_le_left hs₉ 0 T₁ hT₁
  simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq, and_true] at hT₁'
  subst hT₁'
  simp [VTy.Persistent, hAκ] at hp

/-- AT08's clause with the copy used once. -/
abbrev at08OnceCl : Expr :=
  .lam (.letpair (.var 0)
    (bindE (.app alloc' (.var 0))
      (.letpair (.app (.app swap (.var 0)) unit')
        (.letpair (.app (.app swap (.var 1)) (.var 0))
          (bindE (.app free' (.var 1))
            (.seq (.var 1) (.app (.app (.var 0) (.val (.inj₁ .unit))) (.var 7))))))))

/-- **AT08 with the copy used once**: the same reads and writes of the cell at `κ`'s type, `k₁` put
back into the cell and only `k₂` resumed, `u` consumed by `;`:

    op (a, κ) ⇒ c ← alloc κ; (c, k₁) ← swap c (); (c, u) ← swap c k₁; k₂ ← free c; u; resume k₂ a

The kernel program `at08-once`. -/
def at08Once : Expr := handleWith 5 .lin at08OnceCl fooE

/-- The clause of `at08Once` at its clause type: `alloc`, `swap` and `free` at `κ`'s type, `k₂`
resumed once. -/
theorem d_at08OnceCl {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty Γ at08OnceCl (.val (clauseTy [] .unit (.lin, .unit, .unit))) := by
  refine .bangThunkV (persistent_dead hΓ) rfl (.lam ?_)
  refine .tensorE (.left (deadSplit hΓ)) (.var (.here hΓ.toP)) ?_
  refine .bind (A := .ref (kTy [] .unit .lin .unit)) (.left (.right (.dead (deadSplit hΓ))))
    (.ret (appW (.var (by csolo)) (.alloc (by cdead)))) ?_
  refine .tensorE (A := .ref .unit) (B := kTy [] .unit .lin .unit)
    (.left (.dead (.right (.dead (deadSplit hΓ)))))
    (appW (.unitI (by cdead)) (appW (.var (by csolo)) (.swap (by cdead)))) ?_
  refine .tensorE (A := .ref (kTy [] .unit .lin .unit)) (B := .unit)
    (.left (.left (.dead (.dead (.right (.dead (deadSplit hΓ)))))))
    (appW (.var (by csolo)) (appW (.var (by csolo)) (.swap (by cdead)))) ?_
  refine .bind (A := kTy [] .unit .lin .unit)
    (.right (.left (.dead (.dead (.dead (.dead (.right (.dead (deadSplit hΓ)))))))))
    (.ret (appW (.var (by csolo)) (.free (by cdead)))) ?_
  refine .unitE (.right (.left (.dead (.dead (.dead (.dead (.dead (.right (.dead
    (deadSplit hΓ)))))))))) (.var (by csolo)) ?_
  exact .app (.left (.dead (.dead (.dead (.dead (.dead (.dead (.right (.dead
      (deadSplit hΓ))))))))))
    (.proj₁ (.force (C := .amp (.arr .unit (CTy.effOf [] .unit)) .top) (.here (by cdead))))
    (by csolo)

/-- **AT08 with the copy used once is typed** by Core's kernel at `F 1`: the cell's reads and
writes at `κ`'s type are typed, and AT08 differs from it only by the copy's second use. -/
theorem d_at08Once : CDerives LifeCtx.empty [] at08Once (.comp (.ret .unit)) := by
  refine .bind .nil (.ret (.tensorI .nil (d_at08OnceCl .nil) (.unitI .nil))) ?_
  refine .bind (.right .nil) (.ret (d_hrS (.cons .nil))) ?_
  exact .effHandle (S := []) (E := [(.lin, .unit, .unit)]) (n := 5) (A := .unit) (R := .unit)
    (.left (.left .nil)) (.left (.right .nil)) (.here (.cons .nil)) (.there (.here .nil))
    (by decide) (by simp) (by simp) (.effPerform (o := fooSig) rfl rfl (.unitI (by cdead)))

/-- **AT08 with the copy used once runs**: every run, under every allocator, ends at `()` with the
empty memory. -/
theorem at08Once_runs {μ₁ : BoCa.BoLo.Heap} {e₁ : Expr}
    (hs : BoCa.BoLo.Steps Adequacy.emptyMem at08Once μ₁ e₁) :
    BoCa.BoLo.Steps μ₁ e₁ Adequacy.emptyMem (.val .unit) :=
  adequacyD d_at08Once hs

/-! ### AT05: the callback uses its borrow twice -/

/-- `withborU`'s inner λ: `λf. (f [] r) then b. (r, b) unwind d r`. -/
abbrev wbInner (d : Expr) : Expr :=
  thenE (.pair (.var 2) (.var 0)) (.app d (.var 2)) (.app (.app (.var 0) (.val .unit)) (.var 1))

/-- **`withborU d`'s source is used on both sides of its `then`**: typed as a λ, its binder's slot
is persistent. -/
theorem then_src {Δ : LifeCtx} {Γ : Ctx VTy} {d : Expr} {j : Jdg}
    (h : CDerives Δ Γ (wbInner d) j) : ∃ T, Γ[1]? = some ⟨T, true⟩ ∧ T.Persistent := by
  obtain ⟨Γ₁, Γ₂, A, j₁, j₂, hs, hM, hN⟩ := der_then h _ _ _ rfl
  obtain ⟨T, hT⟩ := fv_live hM 1 (by simp [Expr.HasVar, Expr.val, Val.unit])
  obtain ⟨T', hT'⟩ := fv_live hN 2 (by simp [Expr.HasVar])
  exact ⟨T, splitP_le_left hs _ _ hT, splitP_both hs hT (by simpa using hT')⟩

/-- **`withborU d` typed as a λ** at `A ⊸ D`: `A` is persistent. -/
theorem wb_generic {Δ : LifeCtx} {Γ : Ctx VTy} {d : Expr} {A : VTy} {j : Jdg}
    (h : CDerives Δ (⟨A, true⟩ :: Γ) (.lam (wbInner d)) j) : A.Persistent := by
  have key : ∀ (s : Slot VTy) Δ' j', CDerives Δ' (s :: ⟨A, true⟩ :: Γ) (wbInner d) j' →
      A.Persistent := by
    intro s Δ' j' h'
    obtain ⟨T, hT, hp⟩ := then_src h'
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
      Slot.mk.injEq, and_true] at hT
    subst hT; exact hp
  rcases der_lam h _ rfl with ⟨A', D, hM, -⟩ | ⟨S, B, hM, -⟩ | ⟨x, b, Δ', S, C, hM, -⟩ |
    ⟨A', hM, -⟩ | ⟨M₁, M₂, hw⟩ | hx
  · exact key _ _ _ hM
  · exact key _ _ _ hM
  · exact key _ _ _ hM
  · exact key _ _ _ hM
  · simp [withPair, wbInner, thenE, Expr.val, Val.lam] at hw
  · rcases hx with ⟨he, -⟩ | ⟨d', he, -⟩ | ⟨ho, -⟩
    · simp [forget, wbInner, thenE, Expr.val, Val.lam, unit'] at he
    · simp [withborUE, wbInner, thenE, Expr.val, Val.lam] at he
    · simp only [wbInner] at ho; not_other ho

/-- **`withborU d`, read at a thunk of `A ⊸ C`** (at a value or at a row over it): as a λ, `A` is
persistent; as an unwinding constant, `A` is its source and `C` takes a callback whose argument is
a borrow. -/
theorem wb_view {Δ : LifeCtx} {Γ : Ctx VTy} {d : Expr} {j : Jdg} {T : VTy} {A : VTy} {C : CTy}
    (h : CDerives Δ Γ (withborUE d) j) (hj : j = .val T ∨ ∃ S, j = .comp (CTy.effOf S T))
    (hv : VView T (.thunk (.arr A C))) :
    A.Persistent ∨ ∃ x bnd L B S R, C = .arr (cbUTy x bnd L B S) (CTy.effOf S R) ∧
      L.persistent = false := by
  have hcls : ∀ D', Rigid D' → LamCls Γ D' j → D' = .arr A C := by
    intro D' hD hcl
    rcases hcl with rfl | hc | ⟨-, hc⟩
    · rcases hj with h' | ⟨S, h'⟩
      · cases h'
      · cases h'; exact (hD.1 _ _ rfl).elim
    · exact vview_thunk ((hc.at hj).trans hv)
    · exact vview_bang_thunk ((hc.at hj).trans hv)
  rcases der_lam h _ rfl with ⟨A', D, hM, hcl⟩ | ⟨S, B, hM, hcl⟩ | ⟨x, b, Δ', S, C', hM, hcl⟩ |
    ⟨A', hM, hcl⟩ | ⟨M₁, M₂, hw⟩ | hx
  · have := hcls _ (rigid_arr _ _) hcl
    simp only [CTy.arr.injEq] at this
    obtain ⟨rfl, -⟩ := this
    exact .inl (wb_generic hM)
  · have := hcls _ (rigid_arr _ _) hcl
    simp only [CTy.arr.injEq] at this
    obtain ⟨rfl, -⟩ := this
    exact .inl rfl
  · have := hcls _ (rigid_all _ _ _) hcl; cases this
  · rcases hcl with hc | ⟨-, hc⟩
    · have := vview_thunk ((hc.at hj).trans hv); cases this
    · have := vview_bang_thunk ((hc.at hj).trans hv); cases this
  · simp [withPair, Expr.val, Val.lam] at hw
  · rcases hx with ⟨he, -⟩ | ⟨d', -, T₀, ⟨src, x, bnd, L, B, S, R, rfl, hL⟩, hc⟩ | ⟨ho, -⟩
    · simp [forget, Expr.val, Val.lam, unit'] at he
    · have := vview_thunk ((hc.at hj).trans hv)
      simp only [CTy.arr.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      exact .inr ⟨x, bnd, L, B, S, R, rfl, hL⟩
    · not_other ho

/-- AT05's callback `Λ. λm. (m, m)`. -/
abbrev at05F : Expr := .lam (.lam (.pair (.var 0) (.var 0)))

/-- What AT05's innermost term knows of its context: the cell's slot (index `2`) is at a view of a
`Ref`; the slot of `w` (index `0`), when `w` is a variable, is at a type `withborU dFlag` is read
at;
the slot of `f` (index `1`), when `f` is a variable, at a type the callback is read at. -/
structure At05Ctx (Γ : Ctx VTy) (W F : Expr) : Prop where
  c : ∀ T, Γ[2]? = some ⟨T, true⟩ → ∃ A, VView (.ref A) T
  w : W = .var 0 ∨ W = withborUE dFlag
  wt : W = .var 0 → ∀ T, Γ[0]? = some ⟨T, true⟩ →
    ∃ Δ Γ' S, CDerives Δ Γ' (withborUE dFlag) (.comp (CTy.effOf S T))
  f : F = .var 1 ∨ F = at05F
  ft : F = .var 1 → ∀ T, Γ[1]? = some ⟨T, true⟩ →
    ∃ Δ Γ' S, CDerives Δ Γ' at05F (.comp (CTy.effOf S T))

theorem At05Ctx.le {Γ Γ' : Ctx VTy} {W F : Expr} (h : At05Ctx Γ W F) (hle : CtxLe Γ' Γ) :
    At05Ctx Γ' W F :=
  ⟨fun T hT => h.c T (hle _ _ hT), h.w, fun hW T hT => h.wt hW T (hle _ _ hT), h.f,
    fun hF T hT => h.ft hF T (hle _ _ hT)⟩

/-- A view of a `Ref` is not persistent. -/
theorem vview_ref_np {A T : VTy} (h : VView (.ref A) T) : T.persistent = false := by
  have hh := h.hnf_of (hnf_self (fun _ _ h => by cases h) (fun _ h => by cases h))
    (fun _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => by cases h)
  rw [hh.persistent]; rfl

/-- A view of a `Ref` is no thunk. -/
theorem vview_ref_thunk {A : VTy} {C : CTy} (h : VView (.ref A) (.thunk C)) : False := by
  have := (h.hnf_of (hnf_self (fun _ _ h => by cases h) (fun _ h => by cases h))
    (fun _ h => by cases h) (fun _ _ h => by cases h) (fun _ _ h => by cases h)).eq_self
    (fun _ _ h => by cases h) (fun _ h => by cases h)
  cases this

/-- **`w c`, the source applied** (`W` the variable `w` or `withborU dFlag` itself): read only at
`cb ⊸ F_Σ R`, `cb` an unwinding callback type whose argument is a borrow.  As a λ, `withborU dFlag`
takes a persistent source and the cell is a `Ref`. -/
theorem at05_M {Δ : LifeCtx} {Γ : Ctx VTy} {W F : Expr} {j : Jdg}
    (h : CDerives Δ Γ (.app W (.var 2)) j) (hc : At05Ctx Γ W F) :
    ∃ x bnd L B S R, L.persistent = false ∧
      j = .comp (.arr (cbUTy x bnd L B S) (CTy.effOf S R)) := by
  obtain ⟨j₀, hb, hr⟩ := der_app h _ _ rfl
  rcases hb with ⟨Γ₁, Γ₂, A, B, hs, hY, hf, rfl⟩ | ⟨Γ₁, Γ₂, i, A, C, hi, hs, hf, hx, rfl⟩ |
    ⟨N, Γ₁, Γ₂, A, S, C, hN, hs, hY, hU, rfl⟩ | ⟨N, b, C, -, hb, -⟩ |
    ⟨-, -, -, -, hu, -⟩ | ⟨-, -, -, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨hu, -⟩ | hX
  · -- `⊸E`: the source at `A`, a view of the cell's `Ref`; `W` at `A ⊸ B`
    obtain ⟨T, hT, hcT⟩ := der_var hY 2 rfl
    obtain ⟨A₀, hv⟩ := hc.c T (splitP_le_left hs _ _ hT)
    have hAp := vview_ref_np (hv.trans hcT.val)
    rcases hc.w with rfl | rfl
    · obtain ⟨T_w, hTw, hcw⟩ := der_var hf 0 rfl
      obtain ⟨Δ', Γ', S', hW⟩ := hc.wt rfl T_w (splitP_le_right hs _ _ hTw)
      rcases wb_view hW (.inr ⟨S', rfl⟩) hcw.val with hp | ⟨_, _, _, _, _, _, he, _⟩
      · simp [VTy.Persistent, hAp] at hp
      · cases he
    · rcases wb_view hf (.inl rfl) .refl with hp | ⟨_, _, _, _, _, _, he, _⟩
      · simp [VTy.Persistent, hAp] at hp
      · cases he
  · -- `[app]`: the source at the cell's slot's type
    cases hi
    obtain ⟨A₀, hv⟩ := hc.c A (splitP_le_right hs _ _ (soloP_le hx))
    have hAp := vview_ref_np hv
    rcases hc.w with rfl | rfl
    · obtain ⟨T_w, hTw, hcw⟩ := der_var hf 0 rfl
      rcases hcw with ⟨S', Y, he, -⟩ | ⟨C_w, rfl, hCw, hr'⟩
      · exact (effOf_ne_arr _ _ _ _ he.symm).elim
      · obtain rfl : C_w = .arr A C := by
          rcases rigid_or_ampNu hCw with hR | hN
          · have := hr'.rigid hR; cases this; rfl
          · obtain ⟨D', he, hD'⟩ := hr'.ampNu hN
            cases he
            rcases hD' with ⟨_, _, h'⟩ | ⟨_, h'⟩ <;> cases h'
        obtain ⟨Δ', Γ', S', hW⟩ := hc.wt rfl _ (splitP_le_left hs _ _ hTw)
        rcases wb_view hW (.inr ⟨S', rfl⟩) .refl with hp | ⟨x, bnd, L, B, S'', R, rfl, hL⟩
        · simp [VTy.Persistent, hAp] at hp
        · have := hr.rigid (rigid_arr _ _)
          exact ⟨x, bnd, L, B, S'', R, hL, this⟩
    · rcases der_lam hf _ rfl with ⟨A', D, hM, hcl⟩ | ⟨S', B', hM, hcl⟩ |
        ⟨x, b, Δ', S', C', hM, hcl⟩ | ⟨A', hM, hcl⟩ | ⟨M₁, M₂, hw⟩ | hx'
      · have := hcl.comp_rigid (rigid_arr _ _)
        simp only [CTy.arr.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        have := wb_generic hM
        simp [VTy.Persistent, hAp] at this
      · have := hcl.comp_rigid (rigid_arr _ _)
        simp only [CTy.arr.injEq] at this
        obtain ⟨rfl, -⟩ := this
        simp [VTy.persistent] at hAp
      · have := hcl.comp_rigid (rigid_arr _ _); cases this
      · rcases hcl with hcl | ⟨-, hcl⟩
        · obtain ⟨S'', Y, he, -⟩ := hcl; exact (effOf_ne_arr _ _ _ _ he.symm).elim
        · obtain ⟨S'', Y, he, -⟩ := hcl; exact (effOf_ne_arr _ _ _ _ he.symm).elim
      · simp [withPair, Expr.val, Val.lam] at hw
      · have := hx'.not_comp; simp [CTy.isRet] at this
  · -- `[let]`: `W` is `withborU dFlag` itself, its source at a row over `A`
    rcases hc.w with rfl | rfl
    · cases hN
    · simp only [withborUE, Expr.val, Val.lam, Expr.lam.injEq] at hN
      subst hN
      obtain ⟨T, hT, hcT⟩ := der_var hY 2 rfl
      obtain ⟨A₀, hv⟩ := hc.c T (splitP_le_left hs _ _ hT)
      rcases hcT with ⟨S'', Y, he, hY'⟩ | ⟨C', rfl, -, -⟩
      · obtain ⟨-, rfl⟩ := effOf_inj he
        have hAp := vview_ref_np (hv.trans hY')
        have := wb_generic (d := dFlag) hU
        simp [VTy.Persistent, hAp] at this
      · exact (vview_ref_thunk hv).elim
  · cases hb
  · cases hu
  · cases hu
  · cases hu
  · cases hu
  · cases hu
  · rcases hc.w with rfl | rfl <;>
      rcases hX with hX | hX | ⟨Z, hX⟩ | ⟨Z, hX⟩ <;> simp [withborUE, Expr.val, Val.lam] at hX

/-- **The callback is read at no unwinding callback type**: under `∀'x`, `λm. (m, m)` at `L ⊸ …`
uses `m` on both sides of a split, so `L` is persistent, while it is a borrow. -/
theorem not_at05F_cb {Δ : LifeCtx} {Γ : Ctx VTy} {S S' : Row} {x : BoCa.Lifetime.LifeVar}
    {bnd : Lifetime.Life} {L B : VTy} (hL : L.persistent = false)
    (h : CDerives Δ Γ at05F (.comp (CTy.effOf S (cbUTy x bnd L B S')))) : False := by
  have hcb : ∀ D, Rigid D → LamCls Γ D (.comp (CTy.effOf S (cbUTy x bnd L B S'))) →
      D = .all x bnd (.arr L (CTy.effOf S' (.box (.var x) B))) := by
    intro D hD hcl
    rcases hcl with he | hcl | ⟨-, hcl⟩
    · cases he; exact (hD.1 _ _ rfl).elim
    · exact vview_thunk (hcl.at (.inr ⟨S, rfl⟩))
    · exact vview_bang_thunk (hcl.at (.inr ⟨S, rfl⟩))
  rcases der_lam h _ rfl with ⟨A', D, hM, hcl⟩ | ⟨S₀, B₀, hM, hcl⟩ |
    ⟨x', b', Δ', S₀, C', hM, hcl⟩ | ⟨A', hM, hcl⟩ | ⟨M₁, M₂, hw⟩ | hx
  · have := hcb _ (rigid_arr _ _) hcl; cases this
  · have := hcb _ (rigid_arr _ _) hcl; cases this
  · have := hcb _ (rigid_all _ _ _) hcl
    simp only [CTy.all.injEq] at this
    obtain ⟨-, -, rfl⟩ := this
    -- the inner λ, `λm. (m, m)`, at `L ⊸ …`
    rcases der_lam hM _ rfl with ⟨A'', D'', hM', hcl'⟩ | ⟨S₁, B₁, hM', hcl'⟩ |
      ⟨_, _, _, _, _, _, hcl'⟩ | ⟨_, _, hcl'⟩ | ⟨M₁, M₂, hw⟩ | hx'
    · have := hcl'.comp_rigid (rigid_arr _ _)
      simp only [CTy.arr.injEq] at this
      obtain ⟨rfl, rfl⟩ := this
      rcases der_pair hM' _ _ rfl with ⟨Γ₁, Γ₂, A₁, A₂, hs, h₁, h₂, -⟩ | he
      · obtain ⟨T₁, hT₁, -⟩ := der_var h₁ 0 rfl
        obtain ⟨T₂, hT₂, -⟩ := der_var h₂ 0 rfl
        have hp := splitP_both hs hT₁ hT₂
        have := splitP_le_left hs 0 T₁ hT₁
        simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq, and_true] at this
        subst this
        simp [VTy.Persistent, hL] at hp
      · simp [emptyFamV, Val.arr, Val.pair, Val.loc, Val.i32] at he
    · have := hcl'.comp_rigid (rigid_arr _ _)
      simp only [CTy.arr.injEq] at this
      obtain ⟨rfl, -⟩ := this
      simp [VTy.persistent] at hL
    · have := hcl'.comp_rigid (rigid_arr _ _); cases this
    · rcases hcl' with hcl' | ⟨-, hcl'⟩
      · obtain ⟨S'', Y, he, -⟩ := hcl'; exact effOf_ne_arr _ _ _ _ he.symm
      · obtain ⟨S'', Y, he, -⟩ := hcl'; exact effOf_ne_arr _ _ _ _ he.symm
    · simp [withPair, Expr.val, Val.lam] at hw
    · have := hx'.not_comp; simp [CTy.isRet] at this
  · rcases hcl with hcl | ⟨-, hcl⟩
    · have := vview_thunk (hcl.at (.inr ⟨S, rfl⟩)); cases this
    · have := vview_bang_thunk (hcl.at (.inr ⟨S, rfl⟩)); cases this
  · simp [withPair, Expr.val, Val.lam] at hw
  · rcases hx with ⟨he, -⟩ | ⟨d, he, -⟩ | ⟨ho, -⟩
    · simp [forget, Expr.val, Val.lam, unit'] at he
    · simp [withborUE, Expr.val, Val.lam, thenE] at he
    · not_other ho

/-- **`w c f` has no derivation**: `w c` is read only at `cb ⊸ F_Σ R` (`at05_M`), so `f`'s slot is
`cb`, at which the callback is read at no type (`not_at05F_cb`). -/
theorem at05_core {Δ : LifeCtx} {Γ : Ctx VTy} {W F : Expr} {j : Jdg}
    (h : CDerives Δ Γ (.app (.app W (.var 2)) F) j) (hc : At05Ctx Γ W F) : False := by
  obtain ⟨j₀, hb, -⟩ := der_app h _ _ rfl
  rcases hb with ⟨Γ₁, Γ₂, A, B, hs, -, hM, -⟩ | ⟨Γ₁, Γ₂, i, A, C, hi, hs, hM, hx, -⟩ |
    ⟨N, -, -, -, -, -, hN, -⟩ | ⟨N, b, C, hN, -⟩ |
    ⟨-, -, -, -, hu, -⟩ | ⟨-, -, -, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨-, -, hu, -⟩ | ⟨hu, -⟩ | hX
  · obtain ⟨_, _, _, _, _, _, _, he⟩ := at05_M hM (hc.le (splitP_le_right hs))
    cases he
  · obtain ⟨x, bnd, L, B, S, R, hL, he⟩ := at05_M hM (hc.le (splitP_le_left hs))
    simp only [Jdg.comp.injEq, CTy.arr.injEq] at he
    obtain ⟨rfl, -⟩ := he
    rcases hc.f with rfl | rfl
    · cases hi
      obtain ⟨Δ', Γ', S', hf⟩ := hc.ft rfl _ (splitP_le_right hs _ _ (soloP_le hx))
      exact not_at05F_cb hL hf
    · cases hi
  · cases hN
  · cases hN
  · rcases hc.f with rfl | rfl <;> cases hu
  · rcases hc.f with rfl | rfl <;> cases hu
  · rcases hc.f with rfl | rfl <;> cases hu
  · rcases hc.f with rfl | rfl <;> cases hu
  · rcases hc.f with rfl | rfl <;> cases hu
  · rcases hc.w with rfl | rfl <;>
      rcases hX with hX | hX | ⟨Z, hX⟩ | ⟨Z, hX⟩ <;> simp [withborUE, Expr.val, Val.lam] at hX

/-- AT05's innermost term: `(c, r) ← w c f; (free c, r)`. -/
abbrev at05N₃ (W F : Expr) : Expr :=
  .app (.lam (.letpair (.var 0) (.pair (.app free' (.var 1)) (.var 0)))) (.app (.app W (.var 2)) F)

/-- **AT05**: an answering handler of a `Flag` state whose body uses its capability `m` twice,
`with h(inj₁ ()) { (m, m) }`: the state cell is lent to the body as `Mut 'h Flag` by `withborU`
(its finaliser `dFlag` releasing the cell on an unwind), and `Mut` has no copy rule.  In A-normal
form: `c ← alloc (inj₁ ()); f ← Λ. λm. (m, m); w ← withborU dFlag; (c, r) ← w c f; (free c, r)`. -/
def at05 : Expr :=
  bindE (.app alloc' (.inj₁ unit'))
    (bindE (.val (.lam (.val (.lam (.pair (.var 0) (.var 0))))))
      (bindE (withborUE dFlag)
        (.app (.val (.lam (.letpair (.var 0) (.pair (.app free' (.var 1)) (.var 0)))))
          (.app (.app (.var 0) (.var 2)) (.var 1)))))

theorem at05_eq : at05 = bindE (.app alloc' (.inj₁ unit'))
    (bindE at05F (bindE (withborUE dFlag) (at05N₃ (.var 0) (.var 1)))) := rfl

/-- **AT05 has no derivation**: through its three bindings (the cell, the callback,
`withborU dFlag`, each possibly the polymorphic let), `w c f` is typed in a context `At05Ctx`
describes, and has no derivation there (`at05_core`). -/
theorem not_der_at05 {Δ : LifeCtx} {Γ : Ctx VTy} {j : Jdg} : ¬ CDerives Δ Γ at05 j := by
  intro h
  rw [at05_eq] at h
  -- `c ← alloc (inj₁ ())`
  obtain ⟨Γ₁, Γ', T_c, b_c, S, j₁, -, -, hA, hN₂⟩ := der_bind (M := .app alloc' (.inj₁ unit')) h
    (fun i h => by cases h) (fun b h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (fun h => by cases h) (by not_withPairH) (by not_constH)
  obtain ⟨A₀, hvc⟩ := alloc_row hA
  have hc0 : ∀ T, (⟨T_c, b_c⟩ :: Γ')[0]? = some ⟨T, true⟩ → ∃ A, VView (.ref A) T := by
    intro T hT
    simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq] at hT
    obtain ⟨rfl, -⟩ := hT
    exact ⟨A₀, hvc⟩
  -- `f ← Λ. λm. (m, m)`
  obtain ⟨Γ₂, j₂, F, hF, hF', hc1, hN₃⟩ : ∃ Γ₂ j₂ F, (F = .var 1 ∨ F = at05F) ∧
      (F = .var 1 → ∀ T, Γ₂[0]? = some ⟨T, true⟩ →
        ∃ Δ Γ' S, CDerives Δ Γ' at05F (.comp (CTy.effOf S T))) ∧
      (∀ T, Γ₂[1]? = some ⟨T, true⟩ → ∃ A, VView (.ref A) T) ∧
      CDerives Δ Γ₂ (bindE (withborUE dFlag) (at05N₃ (.var 0) F)) j₂ := by
    rcases der_bindLam (N := bindE (withborUE dFlag) (at05N₃ (.var 0) (.var 1)))
        (b := .lam (.pair (.var 0) (.var 0))) hN₂ (by not_withPairH) (by not_constH) with
      ⟨Γf, Γ₂', T_f, b_f, S_f, j', -, hle₂, hf, hN⟩ | ⟨j', hN⟩
    · refine ⟨_, _, .var 1, .inl rfl, fun _ T hT => ?_, fun T hT => ?_, hN⟩
      · simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq] at hT
        obtain ⟨rfl, -⟩ := hT
        exact ⟨_, _, _, hf⟩
      · exact hc0 T (hle₂ 0 T (by simpa using hT))
    · refine ⟨⟨.unit, false⟩ :: ⟨T_c, b_c⟩ :: Γ', j', at05F, .inr rfl, (fun h => by cases h),
        (fun T hT => hc0 T (by simpa using hT)), ?_⟩
      have e : ((bindE (withborUE dFlag) (at05N₃ (.var 0) (.var 1))).subst 0
          (Val.lam (.lam (.pair (.var 0) (.var 0))))).shift 1 0 =
          bindE (withborUE dFlag) (at05N₃ (.var 0) at05F) := by rfl
      rw [e] at hN
      exact hN
  -- `w ← withborU dFlag`
  obtain ⟨Γ₃, j₃, W, hctx, hN₄⟩ : ∃ Γ₃ j₃ W, At05Ctx Γ₃ W F ∧ CDerives Δ Γ₃ (at05N₃ W F) j₃ := by
    rcases der_bindLam (N := at05N₃ (.var 0) F) (b := .lam (wbInner dFlag)) hN₃ (by not_withPairH)
        (by not_constH) with
      ⟨Γw, Γ₃', T_w, b_w, S_w, j', -, hle₃, hw, hN⟩ | ⟨j', hN⟩
    · refine ⟨_, _, .var 0, ⟨fun T hT => ?_, .inl rfl, fun _ T hT => ?_, hF, fun hF1 T hT => ?_⟩,
        hN⟩
      · exact hc1 T (hle₃ 1 T (by simpa using hT))
      · simp only [List.getElem?_cons_zero, Option.some.injEq, Slot.mk.injEq] at hT
        obtain ⟨rfl, -⟩ := hT
        exact ⟨_, _, _, hw⟩
      · exact hF' hF1 T (hle₃ 0 T (by simpa using hT))
    · refine ⟨⟨.unit, false⟩ :: Γ₂, j', withborUE dFlag, ⟨(fun T hT => hc1 T (by simpa using hT)),
        .inr rfl,
        (fun h => by cases h), hF, (fun hF1 T hT => hF' hF1 T (by simpa using hT))⟩, ?_⟩
      have e : ((at05N₃ (.var 0) F).subst 0 (Val.lam (.lam (wbInner dFlag)))).shift 1 0 =
          at05N₃ (withborUE dFlag) F := by
        rcases hF with rfl | rfl <;> rfl
      rw [e] at hN
      exact hN
  -- `(c, r) ← w c f; …`
  obtain ⟨Γ₄, _, _, _, _, _, hle₄, _, hY, _⟩ := der_bind hN₄ (fun i h => by cases h)
    (fun b h => by cases h) (fun h => by cases h) (fun h => by cases h) (fun h => by cases h)
    (by not_withPairH) (by not_constH)
  exact at05_core hY (hctx.le hle₄)

end BoCa.Fig16.LogRel.Core.Rejections

end
