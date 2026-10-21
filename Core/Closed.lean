import Core.Fundamental

/-!
# Core — a typed term is closed, and a run from a closed term stays closed  `[spec §3]`

`closedAt_of_derives`: a term `CDerives` types at the context `Γ` has every free variable below
`Γ.length`, so a closed program is closed.  Induction on `CDerives`: each rule's term is built from
its premises' terms under the binders its premises' contexts extend by, and its constants are
closed (`withborUE_closed`, `foldImmV_closed`, `unfoldV_closed`, …).  `[let-poly]`'s body is
closed where its filled premise term is (`closedAt_of_fill`).

`closed_steps`: a run from a closed term, with every stored value closed (`HeapClosed`), keeps both
closed.  A head step substitutes closed values (`closedAt_subst`) and builds its reduct and the
values it stores from closed parts: the continuation `[op]` hands at every tag
(`closedAt_kappaAt`), the clause it selects (`closedAt_clauseAt`), a host's answer
(`closedAt_host`), the terms the array steps build (`closedAt_tabFill`, `closedAt_dropFill`).  An
evaluation context binds nothing (`closedAt_plug_iff`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont performE raiseE opPayload hndE ubindE ccatchE cfinE
  hndVal cancelVal kappa)
open BoCa.Lifetime (LifeCtx)

/-! ### Typed terms -/

/-- A split keeps the context's length on both sides. -/
theorem splitP_length {Γ Γ₁ Γ₂ : Ctx VTy} (h : Ctx.SplitP Γ Γ₁ Γ₂) :
    Γ₁.length = Γ.length ∧ Γ₂.length = Γ.length := by
  induction h with
  | nil => exact ⟨rfl, rfl⟩
  | left _ ih | right _ ih | dead _ ih | dup _ _ ih =>
      simp only [List.length_cons]; exact ⟨by rw [ih.1], by rw [ih.2]⟩

/-- A variable a context is solo at is below its length. -/
theorem soloP_lt {Γ : Ctx VTy} {i : Nat} {T : VTy} (h : Ctx.SoloP Γ i T) : i < Γ.length := by
  induction h with
  | here => simp
  | there _ ih | skip _ _ ih => simp only [List.length_cons]; omega

/-- A term closed at `0` is closed at every bound. -/
theorem closedAt_of_zero {e : Expr} (h : closedAt 0 e = true) (k : Nat) : closedAt k e = true :=
  closedAt_mono e h (Nat.zero_le k)

/-- A handler's tags are closed. -/
theorem closedAt_qualsVal (k : Nat) : ∀ qs : List Qual, closedAt k (qualsVal qs).1 = true
  | [] => rfl
  | q :: qs => by
      simp only [qualsVal, Val.pair, Val.i32, closedAt, closedAt_qualsVal k qs, Bool.and_true]

/-- **`N` is closed where its filling is**: `(N.subst j V).shift 1 j`, `N` with the closed value
`V` for the variable `j` and every other variable where it was, closed at a bound above `j`. -/
theorem closedAt_of_fill {V : Val} (hV : closedAt 0 V.1 = true) :
    ∀ (N : Expr) (j m : Nat), j < m → closedAt m ((N.subst j V).shift 1 j) = true →
      closedAt m N = true
  | .var i, j, m, hjm, h => by
      simp only [closedAt, decide_eq_true_eq]
      by_cases h2 : i = j
      · omega
      · by_cases h3 : i > j
        · have h4 : ¬ (i - 1 < j) := by omega
          simp only [Expr.subst, if_neg h2, if_pos h3, Expr.shift, if_neg h4, closedAt,
            decide_eq_true_eq] at h
          omega
        · have h4 : i < j := by omega
          simp only [Expr.subst, if_neg h2, if_neg h3, Expr.shift, if_pos h4, closedAt,
            decide_eq_true_eq] at h
          omega
  | .unit, _, _, _, _ => rfl
  | .pair a b, j, m, hjm, h => by
      simp only [Expr.subst, Expr.shift, closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨closedAt_of_fill hV a j m hjm h.1, closedAt_of_fill hV b j m hjm h.2⟩
  | .inj₁ a, j, m, hjm, h => by
      simp only [Expr.subst, Expr.shift, closedAt] at h ⊢; exact closedAt_of_fill hV a j m hjm h
  | .inj₂ a, j, m, hjm, h => by
      simp only [Expr.subst, Expr.shift, closedAt] at h ⊢; exact closedAt_of_fill hV a j m hjm h
  | .lam b, j, m, hjm, h => by
      simp only [Expr.subst, Expr.shift, closedAt, val_shift_closed hV] at h ⊢
      exact closedAt_of_fill hV b (j + 1) (m + 1) (by omega) h
  | .loc _, _, _, _, _ => rfl
  | .prim _, _, _, _, _ => rfl
  | .seq a b, j, m, hjm, h => by
      simp only [Expr.subst, Expr.shift, closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨closedAt_of_fill hV a j m hjm h.1, closedAt_of_fill hV b j m hjm h.2⟩
  | .letpair a b, j, m, hjm, h => by
      simp only [Expr.subst, Expr.shift, closedAt, Bool.and_eq_true, val_shift_closed hV] at h ⊢
      exact ⟨closedAt_of_fill hV a j m hjm h.1, closedAt_of_fill hV b (j + 2) (m + 2) (by omega) h.2⟩
  | .case a b e, j, m, hjm, h => by
      simp only [Expr.subst, Expr.shift, closedAt, Bool.and_eq_true, val_shift_closed hV] at h ⊢
      exact ⟨⟨closedAt_of_fill hV a j m hjm h.1.1,
        closedAt_of_fill hV b (j + 1) (m + 1) (by omega) h.1.2⟩,
        closedAt_of_fill hV e (j + 1) (m + 1) (by omega) h.2⟩
  | .app f a, j, m, hjm, h => by
      simp only [Expr.subst, Expr.shift, closedAt, Bool.and_eq_true] at h ⊢
      exact ⟨closedAt_of_fill hV f j m hjm h.1, closedAt_of_fill hV a j m hjm h.2⟩

/-- **A typed term is closed at its context.** -/
theorem closedAt_of_derives {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerives Δ Γ e j) : closedAt Γ.length e = true := by
  induction h with
  | var h => simpa [closedAt] using soloP_lt h
  | force h =>
      rename_i C
      have := soloP_lt h
      cases C <;> simp [forceE, closedAt, Expr.val, Val.unit, this]
  | tensorI hs _ _ ih₁ ih₂ =>
      rw [(splitP_length hs).1] at ih₁; rw [(splitP_length hs).2] at ih₂
      simp [closedAt, ih₁, ih₂]
  | thunkF _ ih | lam _ ih | lamDead _ ih | allI _ _ _ _ ih | bangThunkF _ _ ih =>
      simpa [closedAt, Expr.val, Val.lam] using ih
  | bind hs _ _ ihM ihN | effLet hs _ _ _ _ ihM ihN =>
      rw [(splitP_length hs).1] at ihM; rw [List.length_cons, (splitP_length hs).2] at ihN
      simp [closedAt, Expr.val, Val.lam, ihM, ihN]
  | app hs _ hx ihM =>
      rw [(splitP_length hs).1] at ihM
      have := soloP_lt hx; rw [(splitP_length hs).2] at this
      simp [closedAt, ihM, this]
  | withI _ _ ihM ihN =>
      simp only [List.length_cons] at ihM ihN
      simp [withPair, closedAt, Expr.val, Val.lam, ihM, ihN]
  | proj₁ _ ih | proj₂ _ ih | allE _ _ ih | allEV _ _ ih =>
      simp [closedAt, Expr.val, Val.inj₁, Val.inj₂, Val.unit, ih]
  | unitE hs _ _ ihV ihM | lolliE hs _ _ ihV ihM =>
      rw [(splitP_length hs).1] at ihV; rw [(splitP_length hs).2] at ihM
      simp [closedAt, ihV, ihM]
  | tensorE hs _ _ ihV ihM =>
      rw [(splitP_length hs).1] at ihV; rw [List.length_cons, List.length_cons,
        (splitP_length hs).2] at ihM
      simp [closedAt, ihV, ihM]
  | sumE hs _ _ _ ihV ih₁ ih₂ =>
      rw [(splitP_length hs).1] at ihV
      rw [List.length_cons, (splitP_length hs).2] at ih₁ ih₂
      simp [closedAt, ihV, ih₁, ih₂]
  | zeroE hs _ ihV =>
      rw [(splitP_length hs).1] at ihV
      simp [absurdE, closedAt, ihV]
  | withbor1U _ _ _ _ _ _ _ hdc _ _ | withbor2U _ _ _ _ _ _ _ hdc _ _
  | withbor3U _ _ _ _ _ _ hdc _ _ | sliceBorrowMU _ _ _ _ _ _ _ hdc _ _
  | sliceBorrowIU _ _ _ _ _ _ _ _ hdc _ _ =>
      exact closedAt_of_zero (withborUE_closed hdc) _
  | foldImm => exact closedAt_of_zero (foldImmV_closed _) _
  | foldOwn => exact closedAt_of_zero (foldOwnV_closed _) _
  | foldReuse => exact closedAt_of_zero (foldReuseV_closed _) _
  | unfoldN => exact closedAt_of_zero (unfoldV_closed _) _
  | effPerform _ _ _ ih | effRaise _ _ _ _ ih =>
      simp [performE, raiseE, opArgE, closedAt, Expr.val, Val.prim, Val.i32, ih]
  | effThen hs _ _ _ _ _ _ _ _ _ _ _ ihM ihN ihD =>
      rw [(splitP_length hs).1] at ihM
      rw [List.length_cons, (splitP_length hs).2] at ihN ihD
      simp [thenE, closedAt, Expr.val, Val.prim, Val.lam, ihM, ihN, ihD]
  | effHandleV hs _ _ _ _ _ _ _ _ ihc ihe | effHandleVB hs _ _ _ _ _ _ _ _ _ _ ihc ihe =>
      rw [(splitP_length hs).1] at ihc; rw [(splitP_length hs).2] at ihe
      simp [hndExpr, closedAt, Expr.val, Val.prim, Val.i32, closedAt_qualsVal, ihc, ihe]
  | effHandleT hs _ _ _ _ _ _ _ _ _ _ _ _ ihc ihe =>
      rw [(splitP_length hs).1] at ihc; rw [(splitP_length hs).2] at ihe
      simp only [closedAt, Bool.and_eq_true] at ihc
      simp [hndExpr, closedAt, Expr.val, Val.prim, Val.i32, closedAt_qualsVal, ihc.1, ihe,
        closedAt_tailTuple ihc.2]
  | divFuel => exact closedAt_of_zero divFuelV_closed _
  | reify _ _ _ _ _ hcl => exact closedAt_of_zero (reifyV_closed hcl) _
  | @letPoly _ Γ' N _ _ b hcl _ _ _ ihN =>
      rw [List.length_cons] at ihN
      have hN := closedAt_of_fill hcl N 0 (Γ'.length + 1) (Nat.succ_pos _) ihN
      have hb : closedAt Γ'.length (Expr.lam b) = true := closedAt_of_zero hcl _
      simp only [closedAt, Expr.val, Val.lam, Bool.and_eq_true] at hb ⊢
      exact ⟨hN, hb⟩
  | _ =>
      first
        | assumption
        | exact closedAt_of_zero rfl _

/-! ### Closed runs -/

/-- Substituting a closed value for a variable below the bound lowers it by one. -/
theorem closedAt_subst : ∀ (e : Expr) {k j : ℕ} (s : Val), closedAt 0 s.1 = true →
    closedAt (k + 1) e = true → j ≤ k → closedAt k (e.subst j s) = true
  | .var i, k, j, s, hs, h, hj => by
      simp only [closedAt, decide_eq_true_eq] at h
      simp only [Expr.subst]
      split
      · exact closedAt_mono _ hs (Nat.zero_le _)
      · split
        · simp only [closedAt, decide_eq_true_eq]; omega
        · simp only [closedAt, decide_eq_true_eq]; omega
  | .unit, _, _, _, _, _, _ => rfl
  | .loc _, _, _, _, _, _, _ => rfl
  | .prim _, _, _, _, _, _, _ => rfl
  | .pair a b, k, j, s, hs, h, hj => by
      simp only [closedAt, Bool.and_eq_true, Expr.subst] at h ⊢
      exact ⟨closedAt_subst a s hs h.1 hj, closedAt_subst b s hs h.2 hj⟩
  | .seq a b, k, j, s, hs, h, hj => by
      simp only [closedAt, Bool.and_eq_true, Expr.subst] at h ⊢
      exact ⟨closedAt_subst a s hs h.1 hj, closedAt_subst b s hs h.2 hj⟩
  | .app a b, k, j, s, hs, h, hj => by
      simp only [closedAt, Bool.and_eq_true, Expr.subst] at h ⊢
      exact ⟨closedAt_subst a s hs h.1 hj, closedAt_subst b s hs h.2 hj⟩
  | .inj₁ a, k, j, s, hs, h, hj => by
      simp only [closedAt, Expr.subst] at h ⊢; exact closedAt_subst a s hs h hj
  | .inj₂ a, k, j, s, hs, h, hj => by
      simp only [closedAt, Expr.subst] at h ⊢; exact closedAt_subst a s hs h hj
  | .lam b, k, j, s, hs, h, hj => by
      simp only [closedAt, Expr.subst] at h ⊢
      rw [val_shift_closed hs]
      exact closedAt_subst b (k := k + 1) (j := j + 1) s hs h (by omega)
  | .letpair a b, k, j, s, hs, h, hj => by
      simp only [closedAt, Bool.and_eq_true, Expr.subst] at h ⊢
      rw [val_shift_closed hs]
      exact ⟨closedAt_subst a s hs h.1 hj,
        closedAt_subst b (k := k + 2) (j := j + 2) s hs h.2 (by omega)⟩
  | .case a b c, k, j, s, hs, h, hj => by
      simp only [closedAt, Bool.and_eq_true, Expr.subst] at h ⊢
      rw [val_shift_closed hs]
      exact ⟨⟨closedAt_subst a s hs h.1.1 hj, closedAt_subst b (k := k + 1) (j := j + 1) s hs h.1.2
        (by omega)⟩, closedAt_subst c (k := k + 1) (j := j + 1) s hs h.2 (by omega)⟩

/-- An evaluation context binds nothing: `K[x]` is closed at `k` as `K[()]` and `x` are. -/
theorem closedAt_plug_iff (k : ℕ) : ∀ (K : Kont) (x : Expr),
    closedAt k (K.plug x) = (closedAt k (K.plug .unit) && closedAt k x)
  | .hole, x => by simp [Kont.plug, closedAt]
  | .pairL K e, x => by
      simp only [Kont.plug, closedAt, closedAt_plug_iff k K x]; cases closedAt k x <;> simp
  | .pairR v K, x => by
      simp only [Kont.plug, closedAt, closedAt_plug_iff k K x]; cases closedAt k x <;> simp
  | .letpair K e, x => by
      simp only [Kont.plug, closedAt, closedAt_plug_iff k K x]; cases closedAt k x <;> simp
  | .case K e₁ e₂, x => by
      simp only [Kont.plug, closedAt, closedAt_plug_iff k K x]; cases closedAt k x <;> simp
  | .appR f K, x => by
      simp only [Kont.plug, closedAt, closedAt_plug_iff k K x]; cases closedAt k x <;> simp
  | .appL K v, x => by
      simp only [Kont.plug, closedAt, closedAt_plug_iff k K x]; cases closedAt k x <;> simp
  | .seq K e, x => by
      simp only [Kont.plug, closedAt, closedAt_plug_iff k K x]; cases closedAt k x <;> simp
  | .inj₁ K, x => by simp only [Kont.plug, closedAt, closedAt_plug_iff k K x]
  | .inj₂ K, x => by simp only [Kont.plug, closedAt, closedAt_plug_iff k K x]

/-- A closed context is fixed by every shift. -/
theorem kont_shift_closed (d : ℕ) : ∀ (K : Kont) (c : ℕ), closedAt 0 (K.plug .unit) = true →
    K.shift d c = K
  | .hole, _, _ => rfl
  | .pairL K e, c, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.shift, kont_shift_closed d K c h.1, shift_closedAt e d h.2 (Nat.zero_le c)]
  | .pairR v K, c, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.shift, kont_shift_closed d K c h.2, val_shift_closed h.1]
  | .letpair K e, c, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.shift, kont_shift_closed d K c h.1,
        shift_closedAt e (k := 0 + 2) (c := c + 2) d h.2 (by omega)]
  | .case K e₁ e₂, c, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.shift, kont_shift_closed d K c h.1.1,
        shift_closedAt e₁ (k := 0 + 1) (c := c + 1) d h.1.2 (by omega),
        shift_closedAt e₂ (k := 0 + 1) (c := c + 1) d h.2 (by omega)]
  | .appR f K, c, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.shift, kont_shift_closed d K c h.2, shift_closedAt f d h.1 (Nat.zero_le c)]
  | .appL K v, c, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.shift, kont_shift_closed d K c h.1, val_shift_closed h.2]
  | .seq K e, c, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.shift, kont_shift_closed d K c h.1, shift_closedAt e d h.2 (Nat.zero_le c)]
  | .inj₁ K, c, h => by
      simp only [Kont.plug, closedAt] at h; simp only [Kont.shift, kont_shift_closed d K c h]
  | .inj₂ K, c, h => by
      simp only [Kont.plug, closedAt] at h; simp only [Kont.shift, kont_shift_closed d K c h]

/-- Every stored value is closed. -/
def HeapClosed (μ : Heap) : Prop := ∀ ℓ v, μ ℓ = some v → closedAt 0 v.1 = true

theorem heapClosed_upd {μ : Heap} (hμ : HeapClosed μ) (ℓ : Loc) {v : Val}
    (hv : closedAt 0 v.1 = true) : HeapClosed (μ.upd ℓ v) := by
  intro k w h
  by_cases hk : k = ℓ
  · subst hk; simp at h; subst h; exact hv
  · rw [Heap.upd_other hk] at h; exact hμ k w h

theorem heapClosed_del {μ : Heap} (hμ : HeapClosed μ) (ℓ : Loc) : HeapClosed (μ.del ℓ) := by
  intro k w h
  by_cases hk : k = ℓ
  · subst hk; simp at h
  · rw [Heap.del_other hk] at h; exact hμ k w h

theorem heapClosed_fill {μ : Heap} (hμ : HeapClosed μ) (ℓ : Loc) (n : ℕ) {v : Val}
    (hv : closedAt 0 v.1 = true) : HeapClosed (μ.fill ℓ n v) := by
  intro k w h
  simp only [Heap.fill] at h
  split at h
  · cases h; exact hv
  · exact hμ k w h

theorem heapClosed_empty : HeapClosed Adequacy.emptyMem := fun _ _ h => by
  simp [Adequacy.emptyMem] at h

theorem closedAt_cancelVal {err : Option Val}
    (h : ∀ E, err = some E → closedAt 0 E.1 = true) : closedAt 0 (cancelVal err).1 = true := by
  cases err with
  | none =>
      simp [cancelVal, opPayload, Val.pair, Val.i32, BoCa.BoLo.errVal, Val.inj₁, Val.unit, closedAt]
  | some E =>
      have hE := h E rfl
      simp only [cancelVal, opPayload, Val.pair, Val.i32, BoCa.BoLo.errVal, Val.inj₂, closedAt]
        at hE ⊢
      simp [hE]

/-- A dead region keeps a part of the region's frames, so it is closed when the region is. -/
theorem closedAt_dead (k : ℕ) : ∀ (K : Kont), closedAt k (K.plug .unit) = true →
    closedAt k (K.dead.plug .unit) = true
  | .hole, h => h
  | .appR f K, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.dead]
      split
      · exact closedAt_dead k K h.2
      · simp only [Kont.plug, closedAt, Bool.and_eq_true]; exact ⟨h.1, closedAt_dead k K h.2⟩
  | .pairL K e, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.dead, Kont.plug, closedAt, Bool.and_eq_true]
      exact ⟨closedAt_dead k K h.1, h.2⟩
  | .pairR v K, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.dead, Kont.plug, closedAt, Bool.and_eq_true]
      exact ⟨h.1, closedAt_dead k K h.2⟩
  | .letpair K e, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.dead, Kont.plug, closedAt, Bool.and_eq_true]
      exact ⟨closedAt_dead k K h.1, h.2⟩
  | .case K e₁ e₂, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.dead, Kont.plug, closedAt, Bool.and_eq_true]
      exact ⟨⟨closedAt_dead k K h.1.1, h.1.2⟩, h.2⟩
  | .appL K v, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.dead, Kont.plug, closedAt, Bool.and_eq_true]
      exact ⟨closedAt_dead k K h.1, h.2⟩
  | .seq K e, h => by
      simp only [Kont.plug, closedAt, Bool.and_eq_true] at h
      simp only [Kont.dead, Kont.plug, closedAt, Bool.and_eq_true]
      exact ⟨closedAt_dead k K h.1, h.2⟩
  | .inj₁ K, h => by
      simp only [Kont.plug, closedAt] at h
      simp only [Kont.dead, Kont.plug, closedAt]; exact closedAt_dead k K h
  | .inj₂ K, h => by
      simp only [Kont.plug, closedAt] at h
      simp only [Kont.dead, Kont.plug, closedAt]; exact closedAt_dead k K h

/-- `κ` with no cell is closed. -/
theorem closedAt_kappa {H : Val} {K : Kont} (hH : closedAt 0 H.1 = true)
    (hK : closedAt 0 (K.plug .unit) = true) : closedAt 0 (kappa H K) = true := by
  have hK' := closedAt_dead 0 K hK
  simp only [kappa, val_shift_closed hH, kont_shift_closed _ K 0 hK,
    kont_shift_closed _ K.dead 0 hK']
  simp only [Expr.val, Val.lam, closedAt, hndE, ccatchE, raiseE, Val.prim, Bool.and_eq_true,
    decide_eq_true_eq]
  rw [closedAt_plug_iff 3, closedAt_plug_iff 2]
  simp only [closedAt, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, ?_⟩ <;> (repeat' constructor) <;>
    first
    | omega
    | trivial
    | exact closedAt_mono _ hH (by omega)
    | exact closedAt_mono _ hK (by omega)
    | exact closedAt_mono _ hK' (by omega)

/-- `κ` with its cell at `ℓ` is closed. -/
theorem closedAt_kappaC (aff : Bool) (ℓ : Loc) {H : Val} {K : Kont}
    (hH : closedAt 0 H.1 = true) (hK : closedAt 0 (K.plug .unit) = true) :
    closedAt 0 (BoCa.BoLo.kappaC aff ℓ H K) = true := by
  have hK' := closedAt_dead 0 K hK
  simp only [BoCa.BoLo.kappaC, val_shift_closed hH, kont_shift_closed _ K 0 hK,
    kont_shift_closed _ K.dead 0 hK']
  cases aff <;>
  simp only [Expr.val, Val.lam, closedAt, hndE, ccatchE, raiseE, Val.prim, Bool.and_eq_true,
    decide_eq_true_eq, BoCa.BoLo.freeE, BoCa.BoLo.stuckE, Val.loc, Val.unit, Bool.false_eq_true,
    if_true, if_false] <;>
  (try rw [closedAt_plug_iff 3]) <;> (try rw [closedAt_plug_iff 2]) <;>
  simp only [closedAt, Bool.and_eq_true, decide_eq_true_eq] <;>
  (repeat' constructor) <;>
    first
    | omega
    | trivial
    | exact closedAt_mono _ hH (by omega)
    | exact closedAt_mono _ hK (by omega)
    | exact closedAt_mono _ hK' (by omega)

/-- `κ` before its cell is closed. -/
theorem closedAt_kappaCell (aff : Bool) {H : Val} {K : Kont}
    (hH : closedAt 0 H.1 = true) (hK : closedAt 0 (K.plug .unit) = true) :
    closedAt 0 (BoCa.BoLo.kappaCell aff H K) = true := by
  have hK' := closedAt_dead 0 K hK
  simp only [BoCa.BoLo.kappaCell, BoCa.BoLo.kappaCBody, val_shift_closed hH,
    kont_shift_closed _ K 0 hK, kont_shift_closed _ K.dead 0 hK']
  cases aff <;>
  simp only [Expr.val, Val.lam, closedAt, hndE, ccatchE, raiseE, Val.prim, Bool.and_eq_true,
    decide_eq_true_eq, BoCa.BoLo.freeE, BoCa.BoLo.stuckE, Val.unit, Bool.false_eq_true,
    if_true, if_false] <;>
  (try rw [closedAt_plug_iff 4]) <;> (try rw [closedAt_plug_iff 3]) <;>
  simp only [closedAt, Bool.and_eq_true, decide_eq_true_eq] <;>
  (repeat' constructor) <;>
    first
    | omega
    | trivial
    | exact closedAt_mono _ hH (by omega)
    | exact closedAt_mono _ hK (by omega)
    | exact closedAt_mono _ hK' (by omega)

/-- The continuation `[op]` hands is closed, at every tag. -/
theorem closedAt_kappaAt (t : UInt32) {H : Val} {K : Kont}
    (hH : closedAt 0 H.1 = true) (hK : closedAt 0 (K.plug .unit) = true) :
    closedAt 0 (BoCa.BoLo.kappaAt t H K) = true := by
  unfold BoCa.BoLo.kappaAt
  split
  · exact closedAt_kappaCell false hH hK
  · split
    · exact closedAt_kappaCell true hH hK
    · exact closedAt_kappa hH hK

/-- A clause of a closed tuple of clauses is closed. -/
theorem closedAt_clauseAt : ∀ (e : Expr) (i : ℕ) {c : Val}, BoCa.BoLo.clauseAt e i = some c →
    closedAt 0 e = true → closedAt 0 c.1 = true
  | .pair c' _, 0, c, h, he => by
      simp only [BoCa.BoLo.clauseAt] at h
      split at h
      · cases h; simp only [closedAt, Bool.and_eq_true] at he; exact he.1
      · cases h
  | .pair _ r, i + 1, c, h, he => by
      simp only [closedAt, Bool.and_eq_true] at he
      exact closedAt_clauseAt r i h he.2
  | .var _, _, _, h, _ | .unit, _, _, h, _ | .inj₁ _, _, _, h, _ | .inj₂ _, _, _, h, _
  | .lam _, _, _, h, _ | .loc _, _, _, h, _ | .prim _, _, _, h, _ | .seq _ _, _, _, h, _
  | .letpair _ _, _, _, h, _ | .case _ _ _, _, _, h, _ | .app _ _, _, _, h, _ => by
      simp [BoCa.BoLo.clauseAt] at h

/-- A host's answer is closed. -/
theorem closedAt_host (H : Host) (op : HostOp) {v r : Val} (h : H.call op v = some r) :
    closedAt 0 r.1 = true := by
  have hi32 : ∀ n, closedAt 0 (Val.i32 n).1 = true := fun _ => rfl
  have hi64 : ∀ n, closedAt 0 (Val.i64 n).1 = true := fun _ => rfl
  have hu8 : ∀ n, closedAt 0 (Val.u8 n).1 = true := fun _ => rfl
  have hob : ∀ w n, closedAt 0 (Val.ofBits w n).1 = true := fun w _ => by cases w <;> rfl
  have hbool : ∀ b, closedAt 0 (Val.bool b).1 = true := fun b => by cases b <;> rfl
  have hopt : ∀ (o : Option Val), (∀ v, o = some v → closedAt 0 v.1 = true) →
      closedAt 0 (Val.opt o).1 = true := fun o ho => by
    cases o with
    | none => rfl
    | some v => simp only [Val.opt, Val.inj₁, closedAt]; exact ho v rfl
  cases op with
  | bin w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, _, -, rfl⟩ := h; exact hi32 _
      · obtain ⟨_, _, -, rfl⟩ := h; exact hi64 _
  | div w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, _, -, rfl⟩ := h
        exact hopt _ fun v hv => by
          simp only [Option.map_eq_some_iff] at hv; obtain ⟨_, -, rfl⟩ := hv; exact hi32 _
      · obtain ⟨_, _, -, rfl⟩ := h
        exact hopt _ fun v hv => by
          simp only [Option.map_eq_some_iff] at hv; obtain ⟨_, -, rfl⟩ := hv; exact hi64 _
  | un w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, -, rfl⟩ := h; exact hi32 _
      · obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | eqz w =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, -, rfl⟩ := h; exact hbool _
      · obtain ⟨_, -, rfl⟩ := h; exact hbool _
  | rel w o =>
      cases w <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> (try simp at h)
      · obtain ⟨_, _, -, rfl⟩ := h; exact hbool _
      · obtain ⟨_, _, -, rfl⟩ := h; exact hbool _
  | wrap =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi32 _
  | extend_s =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | extend_u =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | extend32_s =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi64 _
  | wrap8 =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hu8 _
  | extend8_u =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hi32 _
  | fbin f o =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, _, -, rfl⟩ := h; exact hob _ _
  | fun1 f o =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hob _ _
  | frel f o =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, _, -, rfl⟩ := h; exact hbool _
  | convert f i sx =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hob _ _
  | trunc i f sx =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h
      exact hopt _ fun v hv => by
        simp only [Option.map_eq_some_iff] at hv; obtain ⟨_, -, rfl⟩ := hv; exact hob _ _
  | trunc_sat i f sx =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hob _ _
  | demote =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hob .f32 _
  | promote =>
      simp only [Host.call, Option.map_eq_some_iff] at h; obtain ⟨_, -, rfl⟩ := h; exact hob .f64 _
  | reinterpret_i f =>
      cases f <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> obtain ⟨_, -, rfl⟩ := h
      · exact hi32 _
      · exact hi64 _
  | reinterpret_f f =>
      cases f <;> simp only [Host.call, Option.map_eq_some_iff] at h <;> obtain ⟨_, -, rfl⟩ := h
      · exact hob .f32 _
      · exact hob .f64 _

theorem closedAt_tabFill {f : Val} (hf : closedAt 0 f.1 = true) (ℓ : Loc) (n : UInt32) :
    ∀ i k, closedAt 0 (tabFill f ℓ n i k) = true
  | i, 0 => rfl
  | i, k + 1 => by
      simp only [tabFill, closedAt, Bool.and_eq_true, Expr.val, Val.i32, Val.loc, Val.prim]
      exact ⟨⟨⟨trivial, trivial⟩, hf, trivial⟩, closedAt_tabFill hf ℓ n (i + 1) k⟩

theorem closedAt_dropFill {f : Val} (hf : closedAt 0 f.1 = true) (ℓ : Loc) :
    ∀ i k, closedAt 0 (dropFill f ℓ i k) = true
  | i, 0 => rfl
  | i, k + 1 => by
      simp only [dropFill, closedAt, Bool.and_eq_true, Expr.val, Val.loc, Val.prim]
      exact ⟨⟨hf, trivial, trivial⟩, closedAt_dropFill hf ℓ (i + 1) k⟩

/-- **A head step keeps a closed redex closed**, and stores only closed values. -/
theorem closed_head {μ μ' : Heap} {a a' : Expr} (h : Head (ℍ := ℍ) μ a μ' a')
    (ha : closedAt 0 a = true) (hμ : HeapClosed μ) : closedAt 0 a' = true ∧ HeapClosed μ' := by
  cases h with
  | beta b v =>
      simp only [closedAt, Expr.val, Val.lam, Bool.and_eq_true] at ha
      exact ⟨closedAt_subst b v ha.2 ha.1 (le_refl 0), hμ⟩
  | alloc v ℓ hℓ =>
      simp only [closedAt, Expr.val, Val.prim, Bool.and_eq_true] at ha
      exact ⟨rfl, heapClosed_upd hμ ℓ ha.2⟩
  | free ℓ v hv => exact ⟨hμ ℓ v hv, heapClosed_del hμ ℓ⟩
  | load ℓ v hv => exact ⟨hμ ℓ v hv, hμ⟩
  | store ℓ v w hw =>
      simp only [closedAt, Expr.val, Val.prim, Val.loc, Bool.and_eq_true] at ha
      exact ⟨rfl, heapClosed_upd hμ ℓ ha.2⟩
  | seq e => simp only [closedAt, Expr.val, Val.unit, Bool.and_eq_true] at ha; exact ⟨ha.2, hμ⟩
  | letpair v₁ v₂ e =>
      simp only [closedAt, Expr.val, Val.pair, Bool.and_eq_true] at ha
      refine ⟨closedAt_subst _ v₁ ha.1.1 ?_ (le_refl 0), hμ⟩
      rw [val_shift_closed ha.1.2]
      exact closedAt_subst e (k := 1) (j := 0) v₂ ha.1.2 ha.2 (Nat.zero_le _)
  | case₁ v e₁ e₂ =>
      simp only [closedAt, Expr.val, Val.inj₁, Bool.and_eq_true] at ha
      exact ⟨closedAt_subst e₁ v ha.1.1 ha.1.2 (le_refl 0), hμ⟩
  | case₂ v e₁ e₂ =>
      simp only [closedAt, Expr.val, Val.inj₂, Bool.and_eq_true] at ha
      exact ⟨closedAt_subst e₂ v ha.1.1 ha.2 (le_refl 0), hμ⟩
  | host op v r hr => exact ⟨closedAt_host ℍ op hr, hμ⟩
  | tab c f ℓ hℓ =>
      simp only [closedAt, Expr.val, Val.prim, Val.pair, Val.i32, Bool.and_eq_true] at ha
      exact ⟨closedAt_tabFill ha.2.2 ℓ _ _ _, heapClosed_fill hμ ℓ _ rfl⟩
  | idx ℓ n i =>
      refine ⟨?_, hμ⟩
      simp only [idxAns]; split <;> rfl
  | split ℓ n i =>
      refine ⟨?_, hμ⟩
      simp only [splitAns]; split <;> rfl
  | drop f ℓ n =>
      simp only [closedAt, Expr.val, Val.prim, Val.pair, Val.arr, Bool.and_eq_true] at ha
      exact ⟨closedAt_dropFill ha.2.1 ℓ _ _, hμ⟩
  | count f n i s' =>
      simp only [closedAt, Expr.val, Val.prim, Val.pair, Val.i32, Bool.and_eq_true] at ha
      refine ⟨?_, hμ⟩
      simp only [countNext]; split
      · simp only [closedAt, Expr.val, Val.prim, Val.pair, Val.i32, Bool.and_eq_true]
        exact ⟨trivial, ha.2.1, trivial, trivial, ha.2.1, trivial, ha.2.2.2.2⟩
      · exact ha.2.2.2.2
  | countTry f n i s' =>
      simp only [closedAt, Expr.val, Val.prim, Val.pair, Val.i32, Bool.and_eq_true] at ha
      refine ⟨?_, hμ⟩
      simp only [countTryNext]; split
      · simp only [closedAt, Expr.val, Val.prim, Val.pair, Val.i32, Bool.and_eq_true,
          val_shift_closed ha.2.1, decide_eq_true_eq]
        exact ⟨⟨⟨ha.2.1, trivial, ha.2.2.2.2⟩, trivial, closedAt_mono _ ha.2.1 (by omega), trivial,
          trivial, by omega⟩, by omega⟩
      · simp only [closedAt, Expr.val, Val.inj₁]; exact ha.2.2.2.2
  | boundedFix s' k a =>
      simp only [closedAt, Expr.val, Val.prim, Val.pair, Val.i32, Bool.and_eq_true] at ha
      refine ⟨?_, hμ⟩
      simp only [boundedFixNext, closedAt, Expr.val, Val.pair, Bool.and_eq_true]
      refine ⟨ha.2.1, ?_, ha.2.2.2⟩
      simp only [fixSelf]; split
      · rfl
      · simp only [Val.inj₂, Val.lam, closedAt, Val.prim, Val.i32, Bool.and_eq_true,
          val_shift_closed ha.2.1, decide_eq_true_eq]
        exact ⟨trivial, closedAt_mono _ ha.2.1 (by omega), trivial, by omega⟩
  | iterate f s' =>
      simp only [closedAt, Expr.val, Val.prim, Val.pair, Bool.and_eq_true] at ha
      refine ⟨?_, hμ⟩
      have h₁ := closedAt_mono _ ha.2.1 (Nat.zero_le 3)
      simp only [iterNext, iterTurn, closedAt, Expr.val, Val.lam, Val.inj₁, Val.inj₂, Val.unit,
        Val.prim, nextV, closeV, inrV, tickE, Val.pair, Val.i32, val_shift_closed ha.2.1,
        Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨⟨⟨ha.2.1, ha.2.2⟩, trivial⟩, by omega⟩, ⟨⟨by omega, trivial, h₁, by omega⟩, by omega,
        ⟨h₁, by omega⟩, trivial⟩, trivial, trivial, trivial, trivial⟩
  | hret n qs hr hs w =>
      simp only [hndE, hndVal, closedAt, Expr.val, Val.prim, Val.pair, Val.i32,
        Bool.and_eq_true] at ha
      simp only [closedAt, Expr.val, Bool.and_eq_true]
      exact ⟨⟨ha.1.2.2.2.1, ha.2⟩, hμ⟩
  | hop n i qs hr hs c v K hc hK =>
      have ha' := ha
      simp only [hndE, hndVal, closedAt, Expr.val, Val.prim, Val.pair, Val.i32,
        Bool.and_eq_true] at ha'
      rw [closedAt_plug_iff] at ha'
      simp only [performE, opPayload, closedAt, Expr.val, Val.prim, Val.pair, Val.i32,
        Bool.and_eq_true] at ha'
      have hH : closedAt 0 (hndVal n qs hr hs).1 = true := by
        simp only [hndVal, closedAt, Val.pair, Val.i32, Bool.and_eq_true]
        exact ⟨trivial, ha'.1.2.2.1, ha'.1.2.2.2.1, ha'.1.2.2.2.2⟩
      refine ⟨?_, hμ⟩
      simp only [closedAt, Expr.val, Bool.and_eq_true]
      exact ⟨closedAt_clauseAt hs.1 i.toNat hc ha'.1.2.2.2.2, ha'.2.2.2.2.2,
        closedAt_kappaAt _ hH ha'.2.1⟩
  | hunwind n i qs hr hs c v K hc hK =>
      have ha' := ha
      simp only [hndE, hndVal, closedAt, Expr.val, Val.prim, Val.pair, Val.i32,
        Bool.and_eq_true] at ha'
      rw [closedAt_plug_iff] at ha'
      simp only [raiseE, opPayload, closedAt, Expr.val, Val.prim, Val.pair, Val.i32,
        Bool.and_eq_true] at ha'
      refine ⟨?_, hμ⟩
      simp only [closedAt, Expr.val, Bool.and_eq_true]
      exact ⟨closedAt_clauseAt hs.1 i.toNat hc ha'.1.2.2.2.2, ha'.2.2.2.2.2⟩
  | uthen N D w =>
      simp only [ubindE, closedAt, Expr.val, Val.prim, Val.pair, Bool.and_eq_true] at ha
      simp only [closedAt, Expr.val, Bool.and_eq_true]
      exact ⟨⟨ha.1.2.1, ha.2⟩, hμ⟩
  | ufin N D n i v K hn hK =>
      simp only [ubindE, closedAt, Expr.val, Val.prim, Val.pair, Bool.and_eq_true] at ha
      rw [closedAt_plug_iff] at ha
      simp only [Bool.and_eq_true] at ha
      simp only [closedAt, Expr.val, Val.unit, Bool.and_eq_true]
      exact ⟨⟨⟨ha.1.2.2, trivial⟩, ha.2.2⟩, hμ⟩
  | ufinC N D err K hK =>
      simp only [ubindE, closedAt, Expr.val, Val.prim, Val.pair, Bool.and_eq_true] at ha
      rw [closedAt_plug_iff] at ha
      simp only [raiseE, closedAt, Expr.val, Val.prim, Bool.and_eq_true] at ha
      simp only [cfinE, closedAt, Expr.val, Val.prim, Val.unit, Bool.and_eq_true]
      exact ⟨⟨⟨trivial, ha.2.2.2⟩, ha.1.2.2, trivial⟩, hμ⟩
  | cfret err w =>
      simp only [cfinE, closedAt, Expr.val, Val.prim, Bool.and_eq_true] at ha
      simp only [raiseE, closedAt, Expr.val, Val.prim, Bool.and_eq_true]
      exact ⟨⟨trivial, ha.1.2⟩, hμ⟩
  | cferr err m j w K hm hK =>
      simp only [cfinE, closedAt, Expr.val, Val.prim, Bool.and_eq_true] at ha
      rw [closedAt_plug_iff] at ha
      simp only [raiseE, closedAt, Expr.val, Val.prim, Bool.and_eq_true] at ha
      refine ⟨?_, hμ⟩
      simp only [raiseE, closedAt, Expr.val, Val.prim, Bool.and_eq_true]
      refine ⟨trivial, closedAt_cancelVal ?_⟩
      intro E hE
      have hs := ha.1.2
      cases err with
      | some E' =>
          simp only [BoCa.BoLo.errNext, Option.some_or, Option.some.injEq] at hE
          subst hE
          simp only [cancelVal, opPayload, Val.pair, Val.i32, BoCa.BoLo.errVal, Val.inj₂, closedAt,
            Bool.and_eq_true] at hs
          simp_all
      | none =>
          simp only [BoCa.BoLo.errNext, Option.none_or, Option.some.injEq] at hE
          subst hE; exact ha.2.2.2
  | cfcancel err err' K hK =>
      simp only [cfinE, closedAt, Expr.val, Val.prim, Bool.and_eq_true] at ha
      rw [closedAt_plug_iff] at ha
      simp only [raiseE, closedAt, Expr.val, Val.prim, Bool.and_eq_true] at ha
      refine ⟨?_, hμ⟩
      simp only [raiseE, closedAt, Expr.val, Val.prim, Bool.and_eq_true]
      refine ⟨trivial, closedAt_cancelVal ?_⟩
      intro E hE
      have hs := ha.1.2
      have hs' := ha.2.2
      cases err with
      | some E' =>
          simp only [Option.some_or, Option.some.injEq] at hE
          subst hE
          simp only [cancelVal, opPayload, Val.pair, Val.i32, BoCa.BoLo.errVal, Val.inj₂, closedAt,
            Bool.and_eq_true] at hs
          simp_all
      | none =>
          simp only [Option.none_or] at hE
          subst hE
          simp only [cancelVal, opPayload, Val.pair, Val.i32, BoCa.BoLo.errVal, Val.inj₂, closedAt,
            Bool.and_eq_true] at hs'
          simp_all
  | cancel K hK => exact ⟨rfl, hμ⟩
  | creraise E K hK =>
      simp only [ccatchE, closedAt, Expr.val, Val.prim, Bool.and_eq_true] at ha
      rw [closedAt_plug_iff] at ha
      simp only [raiseE, closedAt, Expr.val, Val.prim, Bool.and_eq_true] at ha
      have hs := ha.2.2.2
      simp only [cancelVal, opPayload, Val.pair, Val.i32, BoCa.BoLo.errVal, Val.inj₂, closedAt,
        Bool.and_eq_true] at hs
      simp only [raiseE, closedAt, Expr.val, Val.prim, Bool.and_eq_true]
      exact ⟨⟨trivial, hs.2.2⟩, hμ⟩

/-- A step keeps a closed term closed, and stores only closed values. -/
theorem closed_step1 {μ μ' : Heap} {e e' : Expr} (h : Step1 (ℍ := ℍ) μ e μ' e')
    (he : closedAt 0 e = true) (hμ : HeapClosed μ) : closedAt 0 e' = true ∧ HeapClosed μ' := by
  obtain ⟨K, a, a', rfl, rfl, hh⟩ := h
  rw [closedAt_plug_iff, Bool.and_eq_true] at he
  obtain ⟨ha', hμ'⟩ := closed_head hh he.2 hμ
  rw [closedAt_plug_iff, he.1, ha']
  exact ⟨rfl, hμ'⟩

/-- **A run from a closed term, with closed stored values, keeps both closed.** -/
theorem closed_steps {μ μ' : Heap} {e e' : Expr} (h : Steps (ℍ := ℍ) μ e μ' e')
    (he : closedAt 0 e = true) (hμ : HeapClosed μ) : closedAt 0 e' = true ∧ HeapClosed μ' := by
  induction h with
  | refl => exact ⟨he, hμ⟩
  | more h₁ _ ih =>
      obtain ⟨he₁, hμ₁⟩ := closed_step1 h₁ he hμ
      exact ih he₁ hμ₁

end BoCa.Fig16.LogRel.Core

end
