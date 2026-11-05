import ExnGlue.Source

/-!
# ExnGlue — the consume-glue translation preserves typing  `[spec §12, §13, §19]`

`tr` inserts the glue SPEC §19 describes ("the elaborator inserts a `[then]` finaliser for every
owned local in scope at a possible abort"):

* `x ← M; N` becomes `M then x. N unwind D` (`[then]`, `CDerives.effThenA`), where `D` consumes
  every live slot of the rest's context (`consAll`);
* `raise_n V` becomes the consumes of the abandoned slots, then `[raise]`;
* `try` becomes `[handle]` (`effHandleV`) at the one abortive operation;
* `borrow xᵢ as m in M` becomes the unwinding `withbor` (`withbor1U`), its finaliser the source's
  consume `consumeE (Ref A)`.

**`tr_derives`**: every source derivation is a `CDerives` derivation of the translation, at the
same lifetime context, context, row and answer. **`sourceResourceSafety`** is `resourceSafety` of
that derivation: every run of a closed source program's translation from the empty memory continues
to a value at the empty memory, and every `free` it reaches finds its cell.

The kernel asks for `Ctx.OwnFree` only at `[let]`'s `hW`, and `tr` emits no `[let]`: what an abort
abandons has been consumed by the finaliser, by the consumes before a raise, or by the lender's
finaliser.
-/

namespace ExnGlue
open BoCa BoCa.Fig16 BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeCtx LifeVar)

/-- The consumes of the live slots of `Γ`, slot `k` first, in front of `e`. -/
def consAll : Ctx VTy → Nat → Expr → Expr
  | [], _, e => e
  | s :: Γ, k, e => if s.live then consumeSlotE s.ty k (consAll Γ (k + 1) e) else consAll Γ (k + 1) e

/-- The handler value of `try`: `(!λx. Nr, (!λe. Ne, ()))`. -/
def handlerE (Nr Ne : Expr) : Expr := .pair (.val (.lam Nr)) (.pair (.val (.lam Ne)) (.val .unit))

/-- **The translation**: the source term with its consume glue.  `[spec §19]` -/
def tr : STm → Expr
  | .ret V => V
  | .letv R M N => thenE (tr N) (consAll (⟨.unit, false⟩ :: R) 0 (.val .unit)) (tr M)
  | .letp V M => .letpair V (tr M)
  | .raise n R V => consAll R 0 (BoCa.BoLo.raiseE (opArgE n 0 V))
  | .tryCatch n Nr Ne M => hndExpr n [.cancel] (handlerE (tr Nr) (tr Ne)) (tr M)
  | .borrowI A i M => bindE (.val (.lam (.val (.lam (tr M)))))
      (bindE (withborUE (consumeE (.ref A))) (.app (.app (.var 0) (.var (i + 2))) (.var 1)))

/-! ### Contexts -/

theorem splitP_append : ∀ {a a₁ a₂ : Ctx VTy}, Ctx.SplitP a a₁ a₂ →
    ∀ {b b₁ b₂ : Ctx VTy}, Ctx.SplitP b b₁ b₂ → Ctx.SplitP (a ++ b) (a₁ ++ b₁) (a₂ ++ b₂)
  | _, _, _, .nil, _, _, _, hb => hb
  | _, _, _, .left h, _, _, _, hb => .left (splitP_append h hb)
  | _, _, _, .right h, _, _, _, hb => .right (splitP_append h hb)
  | _, _, _, .dead h, _, _, _, hb => .dead (splitP_append h hb)
  | _, _, _, .dup hT h, _, _, _, hb => .dup hT (splitP_append h hb)

theorem soloP_kill_append (T : VTy) {Γ : Ctx VTy} : ∀ pre : Ctx VTy,
    Ctx.SoloP (kill pre ++ ⟨T, true⟩ :: kill Γ) pre.length T
  | [] => .here (kill_dead Γ).toP
  | _ :: pre => .there (soloP_kill_append T pre)

theorem banged_deadP : ∀ {Γ : Ctx VTy}, Ctx.Banged Γ → Ctx.DeadP Γ
  | [], _ => .nil
  | ⟨T, l⟩ :: Γ, h => by
      have ih := banged_deadP (Γ := Γ) (fun s hs hl => h s (List.mem_cons_of_mem _ hs) hl)
      cases l with
      | false => exact .cons ih
      | true =>
          obtain ⟨A, hA⟩ := h ⟨T, true⟩ (List.mem_cons_self ..) rfl
          simp only at hA; subst hA; exact .weaken rfl ih

theorem banged_split : ∀ {Γ : Ctx VTy}, Ctx.Banged Γ → Ctx.SplitP Γ Γ Γ
  | [], _ => .nil
  | ⟨T, l⟩ :: Γ, h => by
      have ih := banged_split (Γ := Γ) (fun s hs hl => h s (List.mem_cons_of_mem _ hs) hl)
      cases l with
      | false => exact .dead ih
      | true =>
          obtain ⟨A, hA⟩ := h ⟨T, true⟩ (List.mem_cons_self ..) rfl
          simp only at hA; subst hA; exact .dup rfl ih

theorem ConsumableLive.tail {s : Slot VTy} {Γ : Ctx VTy} (h : ConsumableLive (s :: Γ)) :
    ConsumableLive Γ := fun s' hs hl => h s' (List.mem_cons_of_mem _ hs) hl

/-! ### The consumes of a context -/

/-- **The consumes of a part of the context.** At `Γ = Γa, Γb` with `Γb`'s live slots
consumable, the consumes of `Γb` in front of `e` are typed at `Γ` when `e` is typed at `Γa`: one
`consumeSlot_derives` per live slot, the slots before it in `pre`.  `[spec §12]` -/
theorem consAll_derives {Δ : LifeCtx} {Γ Γa Γb : Ctx VTy} (h : Ctx.SplitP Γ Γa Γb) :
    ConsumableLive Γb → ∀ (pre : Ctx VTy) {e : Expr} {C : CTy},
    CDerives Δ (pre ++ Γa) e (.comp C) → CDerives Δ (pre ++ Γ) (consAll Γb pre.length e) (.comp C) := by
  induction h with
  | nil => intro _ pre e C he; exact he
  | @left Γ Γa Γb T _ ih =>
      intro hC pre e C he
      have := ih hC.tail (pre ++ [⟨T, true⟩]) (by simpa using he)
      simpa [consAll] using this
  | @dead Γ Γa Γb T _ ih =>
      intro hC pre e C he
      have := ih hC.tail (pre ++ [⟨T, false⟩]) (by simpa using he)
      simpa [consAll] using this
  | @right Γ Γa Γb T hs ih =>
      intro hC pre e C he
      have hT : Consumable T := hC ⟨T, true⟩ (List.mem_cons_self ..) rfl
      have hrest := ih hC.tail (pre ++ [⟨T, false⟩]) (by simpa using he)
      simp only [consAll, if_true]
      refine consumeSlot_derives
        (splitP_append (split_kill pre).toP (Ctx.SplitP.left (split_kill Γ).toP))
        (soloP_kill_append T pre) hT ?_
      simpa using hrest
  | @dup Γ Γa Γb T hP hs ih =>
      intro hC pre e C he
      have hT : Consumable T := hC ⟨T, true⟩ (List.mem_cons_self ..) rfl
      have hrest := ih hC.tail (pre ++ [⟨T, true⟩]) (by simpa using he)
      simp only [consAll, if_true]
      refine consumeSlot_derives
        (splitP_append (split_kill pre).toP (Ctx.SplitP.dup hP (split_kill Γ).toP))
        (soloP_kill_append T pre) hT ?_
      simpa using hrest

/-- **The finaliser of a `let`**: the consumes of the rest's context, under `[then]`'s dead
binder, at `F 1`. -/
theorem fin_derives {Δ : LifeCtx} {Γ₂ : Ctx VTy} (hC : ConsumableLive Γ₂) :
    CDerives Δ (⟨.unit, false⟩ :: Γ₂) (consAll (⟨.unit, false⟩ :: Γ₂) 0 (.val .unit))
      (.comp (.ret .unit)) := by
  have hC' : ConsumableLive (⟨.unit, false⟩ :: Γ₂) := by
    intro s hs hl
    rcases List.mem_cons.mp hs with rfl | hs
    · cases hl
    · exact hC s hs hl
  exact consAll_derives (Δ := Δ) (split_kill _).toP hC' [] (.ret (.unitI (kill_dead _).toP))

/-! ### Typing preservation -/

theorem clausesTy_exn (S : Row) (R P : VTy) :
    clausesTy S R [(.cancel, P, .zero)] = .tensor (.bang (.thunk (.arr P (CTy.effOf S R)))) .unit := by
  rfl

/-- **Typing preservation** (`[CMD]` Prop 3's shape): every source derivation is a `CDerives`
derivation of its translation, at the same lifetime context, context, row and answer.
`[spec §12, §19]` -/
theorem tr_derives {Δ : LifeCtx} {Γ : Ctx VTy} {t : STm} {S : Row} {A : VTy}
    (h : SDerives Δ Γ t S A) : CDerives Δ Γ (tr t) (.comp (CTy.effOf S A)) := by
  induction h with
  | ret h => exact .effSub (RowLe.nil _) (.ret h)
  | letv hs hR hS hC _ _ ihM ihN =>
      subst hR
      exact CDerives.effThenA hs hS.1 hS.2.1 (fun hu => absurd hu hS.not_unrD) ihM ihN
        (fin_derives hC)
  | letp hs hV _ ihM => exact .tensorE hs hV ihM
  | @raise Δ Γ Γv Γr R n V S B o hs hR hS hC hf hV =>
      subst hR
      obtain ⟨hm, hn, hi⟩ := Row.find_mem hf
      obtain ⟨-, -, hrc, hd⟩ := hS.2.2 o hm
      have hr : CDerives Δ Γv (BoCa.BoLo.raiseE (opArgE o.n o.i V)) (.comp (CTy.effOf S B)) :=
        .effRaise (by rw [hn, hi]; exact hf) (hS.abort o hm) hrc hd hV
      rw [hn, hi] at hr
      exact consAll_derives hs hC [] hr
  | @tryCatch Δ Γ Γh Γb n P Nr Ne M S A R hs hB hn0 hnS hS _ _ _ ihM ihr ihe =>
      have hH : CDerives Δ Γh (handlerE (tr Nr) (tr Ne))
          (.val (.tensor (retTy S A R) (clausesTy S R [(.cancel, P, .zero)]))) := by
        rw [clausesTy_exn]
        exact .tensorI (banged_split hB) (.bangThunkV hB rfl (.lam ihr))
          (.tensorI (banged_split hB) (.bangThunkV hB rfl (.lam ihe)) (.unitI (banged_deadP hB)))
      exact .effHandleV (fs := finsNil) (cs := rcsNil) hs (banged_deadP hB)
        (.pair (.val _) (.pair (.val _) (.val _))) hH hn0 hnS (by simp)
        (Row.divB_of_abort hS.abort) ihM
  | @borrowI Δ Γ Γc Γv A B i M S x hs hi hA hΔ hx hsc hfA hfB hU hΓx _ ihM =>
      have hcb : CDerives Δ Γc (.val (.lam (.val (.lam (tr M)))))
          (.val (cbUTy x Δ.meetOfDom (.imm (.var x) A) B S)) :=
        .thunkV rfl (.allI (Lifetime.Life.mentions_false_of_wf hx (Lifetime.meetOfDomL_wf Δ.entries))
          (fun _ _ h => hΔ.bound_mentions_false hx h) hΓx (.lam ihM))
      have hW : CDerives Δ (⟨cbUTy x Δ.meetOfDom (.imm (.var x) A) B S, false⟩ :: kill Γv)
          (withborUE (consumeE (.ref A))) (.val (withbor1UTy x Δ.meetOfDom A B S)) :=
        .withbor1U x (Ctx.Dead.cons (kill_dead Γv)).toP hx hsc hfA hfB hU
          (consumeE_closed (.ref hA)) (consume_wf (.ref hA) (Ctx.Dead.cons (kill_dead Γv)))
      refine .bind hs (.ret hcb) (.bind (.right (split_kill Γv).toP) (.ret hW) ?_)
      refine .app (.left (.right (split_kill' Γv).toP)) ?_ (.there (.here (kill_dead Γv).toP))
      exact .app (.left (.dead (split_kill Γv).toP)) (.force (.here (Ctx.Dead.cons (kill_dead Γv)).toP))
        (.there (.there hi))

/-- **Source-level resource safety** (`[CMD]` Thm 4.1's shape): `resourceSafety` ∘ `tr_derives`.
Every run of a closed source program's translation from the empty memory, under every allocator,
continues to a value at the empty memory, and every `free` it reaches finds its cell.
`[spec §13, §19]` -/
theorem sourceResourceSafety {ℍ : BoCa.Host} [BoCa.HostIs ℍ] {t : STm} {A : VTy}
    (hA : A.Persistent) (h : SDerives LifeCtx.empty [] t [] A)
    {μ₁ : BoCa.BoLo.Heap} {e₁ : Expr}
    (hs : BoCa.BoLo.Steps (ℍ := ℍ) Adequacy.emptyMem (tr t) μ₁ e₁) :
    (∃ v : Val, BoCa.BoLo.Steps (ℍ := ℍ) μ₁ e₁ Adequacy.emptyMem (.val v)) ∧
    (∀ (K : BoCa.BoLo.Kont) (ℓ : Loc), e₁ = K.plug (BoCa.BoLo.freeE (.val (Val.loc ℓ))) →
      ∃ u, μ₁ ℓ = some u) :=
  resourceSafety hA (tr_derives h) hs

end ExnGlue
