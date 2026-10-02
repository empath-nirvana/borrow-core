import GhostEnd.Chain

/-!
# GhostEnd — `withbor` with a lend spanning yields (O15.1 for straight-line borrowers)

The program

    withbor ℓ (Λ. λm. perform yield y₁; …; perform yield yₙ; N_f)

lends `ℓ` to a borrower that keeps `m` live across `n` yields, at a table whose `yield` entry
**resumes** (linear, non-abortive). `withbor` is the kernel's term, `[TR]` 6.173's constant.

`withbor_spans_yields`: from `ℓ ↦ v ⋆ 𝒱⟦T⟧(v)` the program satisfies `ewpTS` at that table with
answer `𝒱⟦Ref T ⊗ B⟧`. At the kernel's tables this is `𝒞⟦F_Σ (Ref T ⊗ B)⟧`
(`withbor_spans_yields_cC`). Downstream that is all a handler needs: `ewp_handle` takes exactly an
`ewpTS` of the body at the row's table.

The proof composes three things:

* `[TR]` 6.65 at a resuming table, re-applied at each resumption (`ewpTS_M_frameR`);
* the borrower re-lendable, its last segment re-derived from its typing at each new lifetime
  (`relend_chain`);
* the pair frame `(ℓ, [·])` of `withbor`'s body, carried through every stop (`ewp_frame_plain`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N Head performE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- The borrower `Λ. λm. chain`, as a value. -/
def cbV (n i : UInt32) (ys : List Val) (Nf : Expr) : Val :=
  ⟨.lam (.lam (chain n i ys Nf)), .lam⟩

/-- Substitution passes through a chain of closed payloads. -/
theorem chain_subst (n i : UInt32) (j : Nat) (s : Val) :
    ∀ (ys : List Val), (∀ y ∈ ys, closedAt 0 y.1 = true) → ∀ e : Expr,
      (chain n i ys e).subst j s = chain n i ys (e.subst j s)
  | [], _, e => rfl
  | y :: ys, hys, e => by
      have hy : Expr.subst j s y.1 = y.1 := closed_subst (hys y List.mem_cons_self) j s
      have ih := chain_subst n i j s ys (fun y' h' => hys y' (List.mem_cons_of_mem _ h')) e
      simp only [chain, yieldSeq, performE, opPayload, Expr.subst, Expr.val, Val.pair, Val.i32,
        hy, ih]
      rfl

/-- `substAll [v] e` is the one substitution `e[v/0]`. -/
theorem substAll_one (v : Val) (e : Expr) : substAll [v] e = e.subst 0 v := by
  show Expr.psub 0 [v] e = _
  rw [Expr.psub_cons 0 v [] e, Val.shift_zero, BoCa.Adequacy.psub_nil]

/-- The borrower applied: two β-steps to its chain at `m := ℓ`. -/
theorem relend_cbV {Tb : Table} (hTb : Tb.Mono) {l : BoCa.Loc} {T : VTy} {δ : LSub}
    {Q : List SRec → Val → WProp} (n i : UInt32) (ys : List Val)
    (hys : ∀ y ∈ ys, closedAt 0 y.1 = true) {Nf : Expr} (hNf : closedAt 1 Nf = true)
    {ls : List SRec} {ρ : WRes}
    (h : Relend Tb l T δ Q ls (chain n i ys (substAll [Val.loc l] Nf)) ρ) :
    Relend Tb l T δ Q ls
      (.app (.app (.val (cbV n i ys Nf)) (.val .unit)) (.val (.loc l))) ρ := by
  refine relend_step hTb (fun μ => (Step1N.head (Head.beta μ (.lam (chain n i ys Nf)) Val.unit)
    rfl).plug (Kont.appL .hole (Val.loc l))) ?_
  refine relend_step hTb (fun μ => Step1N.head (Head.beta μ _ (Val.loc l)) rfl) ?_
  rw [chain_subst n i _ _ ys hys, chain_subst n i _ _ ys hys,
    subst_closedAt Nf _ hNf le_rfl, ← substAll_one]
  exact h

/-- A borrower `Λ. λm. M`, applied: two β-steps to `M[ℓ/m]`. -/
theorem relend_lam2 {Tb : Table} (hTb : Tb.Mono) {l : BoCa.Loc} {T : VTy} {δ : LSub}
    {Q : List SRec → Val → WProp} {M : Expr} (hM : closedAt 1 M = true)
    {ls : List SRec} {ρ : WRes}
    (h : Relend Tb l T δ Q ls (substAll [Val.loc l] M) ρ) :
    Relend Tb l T δ Q ls
      (.app (.app (.val ⟨.lam (.lam M), .lam⟩) (.val .unit)) (.val (.loc l))) ρ := by
  refine relend_step hTb (fun μ => (Step1N.head (Head.beta μ (.lam M) Val.unit)
    rfl).plug (Kont.appL .hole (Val.loc l))) ?_
  refine relend_step hTb (fun μ => Step1N.head (Head.beta μ _ (Val.loc l)) rfl) ?_
  rw [subst_closedAt M _ hM le_rfl, ← substAll_one]
  exact h

/-- `withbor ℓ` after its first β-step. -/
def withborAt (l : BoCa.Loc) : Val :=
  Val.lam (.pair (.val (.loc l)) (.app (.app BoCa.v0 unit') (.val (.loc l))))

/-- `withbor ℓ f` steps to `(withbor ℓ) f`, and that to its body `(ℓ, f () ℓ)`. -/
theorem withbor_step₁ (l : BoCa.Loc) (f : Val) (μ : Heap) :
    Step1N μ (.app (.app withbor (.val (.loc l))) (.val f)) μ
      (.app (.val (withborAt l)) (.val f)) := by
  have hβ₁ : Expr.subst 0 (Val.loc l)
        (Expr.val (Val.lam (.pair BoCa.v1 (.app (.app BoCa.v0 unit') BoCa.v1))))
      = Expr.val (withborAt l) := by
    simp [withborAt, Expr.subst, Expr.shift, BoCa.v0, BoCa.v1, unit']
  have h1 := (Step1N.head (ℍ := ℍ) (Head.beta μ (.lam (.pair BoCa.v1
    (.app (.app BoCa.v0 unit') BoCa.v1))) (Val.loc l)) rfl).plug (Kont.appL .hole f)
  simp only [Kont.plug] at h1
  rw [show Expr.subst 0 (Val.loc l) (Expr.lam (.pair BoCa.v1 (.app (.app BoCa.v0 unit') BoCa.v1)))
    = Expr.val (withborAt l) from hβ₁] at h1
  exact h1

theorem withbor_step₂ (l : BoCa.Loc) (f : Val) (μ : Heap) :
    Step1N μ (.app (.val (withborAt l)) (.val f)) μ
      (.pair (.val (.loc l)) (.app (.app (.val f) (.val .unit)) (.val (.loc l)))) := by
  have hβ₂ : Expr.subst 0 f
        (Expr.pair (.val (.loc l)) (.app (.app BoCa.v0 unit') (.val (.loc l))))
      = Expr.pair (.val (.loc l)) (.app (.app (.val f) (.val .unit)) (.val (.loc l))) := by
    simp [Expr.subst, BoCa.v0, unit']
  have h2 := Step1N.head (ℍ := ℍ) (Head.beta μ (.pair (.val (.loc l))
    (.app (.app BoCa.v0 unit') (.val (.loc l)))) f) rfl
  rw [hβ₂] at h2
  exact h2

/-- **`withbor` at a resuming table, from a re-lendable borrower.** `withbor ℓ f` runs
`(ℓ, f () ℓ)`. The borrower runs under 6.65 at the resuming table (`ewpTS_M_frameR`), and the
pair frame `(ℓ, [·])` is carried through every stop (`ewp_frame_plain`). From
`ℓ ↦ v ⋆ 𝒱⟦T⟧(v)` the program answers in `𝒱⟦Ref T ⊗ B⟧`. -/
theorem withbor_relend (Tab : OpTab) {l : BoCa.Loc} {T B : VTy} {δ : LSub}
    {βP : Life} (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum βP) (f : Val)
    {ls : List SRec} (v : Val)
    (hR : Relend (opTable Tab) l T δ (finPost l T B δ) ls
      (.app (.app (.val f) (.val .unit)) (.val (.loc l))) PMap.empty) :
    Entails (ptoOwn l v ⋆ vC true T ls δ v)
      (ewpTS ls (.app (.app withbor (.val (.loc l))) (.val f)) (opTable Tab)
        (fun ls r => vC true (.tensor (.ref T) B) ls δ r)) := by
  intro ρ hρ
  -- 6.65 at the resuming table
  have hcb : ewpTS ls (.app (.app (.val f) (.val .unit)) (.val (.loc l)))
      (opTable Tab) (finPost l T B δ) ρ :=
    ewpTS_M_frameR (opTable Tab) (opTable_mono Tab) l T δ βP hP _ ls _ ρ
      ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, ⟨v, hρ⟩, hR⟩
  -- the pair frame `(ℓ, [·])`
  have hpair := ewp_frame_plain Tab (.pairR (Val.loc l) .hole)
    (fun _ => rfl) (fun _ => rfl) rfl (fun _ => emp)
    (fun _ _ _ _ h => h) (fun _ _ _ _ h => h)
    (fun _ _ _ _ _ _ _ h => by rw [h.1]; exact noOwn_empty)
    (fun _ _ _ _ _ _ _ h => h.1)
    (finPost l T B δ) (fun ls r => vC true (.tensor (.ref T) B) ls δ r) ?_ hcb
    (ρ₂ := PMap.empty) ⟨rfl, trivial⟩ (ResU.comp_empty_right ρ)
  · exact ewp_step (opTable_mono Tab) (withbor_step₁ l _) ls _ ρ
      (ewp_step (opTable_mono Tab) (withbor_step₂ l _) ls _ ρ hpair)
  · rintro ls' r σ ⟨σ₁, σ₂, hc, ⟨so, sb, hcs, ⟨w, ρl, ρP, hcl, hl, hw⟩, hBr⟩, hσ₂, -⟩
    subst hσ₂
    obtain rfl : σ = σ₁ := ResU.CompS.functional hc (ResU.comp_empty_right σ₁)
    show ewpTS ls' (.val (Val.pair (Val.loc l) r)) _ _ σ
    refine ewp_val (opTable_mono Tab) ⟨Val.loc l, r, pure_sep_mk rfl
      ⟨so, sb, hcs, ⟨l, w, pure_sep_mk rfl ⟨ρl, ρP, hcl, hl, hw⟩⟩, hBr⟩⟩

/-- **O15.1 for a straight-line borrower.** `withbor ℓ (Λ. λm. yield y₁; …; yield yₙ; N_f)` with
the lend of `ℓ` open at every yield, at a table whose `yield` entry resumes. From `ℓ ↦ v ⋆ 𝒱⟦T⟧(v)`
it runs to `𝒱⟦Ref T ⊗ B⟧`.

At each yield the borrower drops its view and the frame takes the owner back (freeze). The
continuation owes the owner and the rest of the borrower. At each resumption the frame lends
`ℓ` at a lifetime fresh for the resumer's list (`ewpTS_M_frameR`). `N_f` is re-derived from its
typing at that lifetime (`relend_fin`).

Hypotheses beyond the typing:

* `hP`: `P̂ ⊨ [β]P̂`, 6.65's premise, as `withbor2_compatX` reads it off `Δ ⊢ T ⊒ @b`;
* `hq`: the `yield` entry is linear. Cancelling a continuation that holds the owner would have to
  dispose of it, and the bare frame has no finaliser;
* `hPB`: its answer is `()`, which `;` consumes;
* `hy`: each payload holds at `∅`. -/
theorem withbor_spans_yields {Δ : LifeCtx} {δ : LSub} (hδ : Δ.Models δ) {x : LifeVar}
    {b : Lifetime.Life} (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {β : Life} (hβ : b.interp δ = some β)
    {T B : VTy} (hT : ¬ VFree x T) (hB : ¬ VFree x B)
    {βP : Life} (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum βP)
    {Nf : Expr} (hNf : closedAt 1 Nf = true)
    (hN : SemC (Δ.extend x b) [⟨.mut (.var x) T, true⟩] Nf (.ret (.box (.var x) B)))
    (Tab : OpTab) {n i : UInt32} {en : OpEnt} (hTn : Tab n i = some en)
    (ha : en.abort = false) (hq : en.q = .lin)
    (hPB : ∀ ls w ρ, en.PB ls w ρ → w = Val.unit ∧ ρ = PMap.empty)
    (ys : List Val) (hys : ∀ y ∈ ys, closedAt 0 y.1 = true)
    (hy : ∀ y ∈ ys, ∀ ls, en.PA ls y PMap.empty)
    (l : BoCa.Loc) (v : Val) (ls : List SRec) :
    Entails (ptoOwn l v ⋆ vC true T ls δ v)
      (ewpTS ls (.app (.app withbor (.val (.loc l))) (.val (cbV n i ys Nf))) (opTable Tab)
        (fun ls r => vC true (.tensor (.ref T) B) ls δ r)) :=
  withbor_relend Tab hP _ v (relend_cbV (opTable_mono Tab) n i ys hys hNf
    (relend_chain hδ hbx hΔx hβ hT hB hN Tab hTn ha hq hPB l ys hy ls))

/-- `withbor_spans_yields` at the kernel's relation: a row `Σ` whose `yield` is linear, resuming,
answered at `1`. The program is in `𝒞⟦F_Σ (Ref T ⊗ B)⟧`. -/
theorem withbor_spans_yields_cC {Δ : LifeCtx} {δ : LSub} (hδ : Δ.Models δ) {x : LifeVar}
    {b : Lifetime.Life} (hbx : b.mentions x = false)
    (hΔx : ∀ y u, Δ.find? y = some u → u.mentions x = false)
    {β : Life} (hβ : b.interp δ = some β)
    {T B : VTy} (hT : ¬ VFree x T) (hB : ¬ VFree x B)
    {βP : Life} (hP : ∀ ls w σ, vC true T ls δ w σ → σ.InStratum βP)
    {Nf : Expr} (hNf : closedAt 1 Nf = true)
    (hN : CDerives (Δ.extend x b) [⟨.mut (.var x) T, true⟩] Nf (.comp (.ret (.box (.var x) B))))
    (S : Row) (o : OpSig) (hf : Row.find S o.n o.i = some o) (ha : o.abort = false)
    (hq : o.q = .lin) (hoB : o.B = .unit)
    (ys : List Val) (hys : ∀ y ∈ ys, closedAt 0 y.1 = true)
    (hy : ∀ y ∈ ys, ∀ ls, vC true o.A ls δ y PMap.empty)
    (l : BoCa.Loc) (v : Val) (ls : List SRec) :
    Entails (ptoOwn l v ⋆ vC true T ls δ v)
      (cC (CTy.effOf S (.tensor (.ref T) B)) ls δ
        (.app (.app withbor (.val (.loc l))) (.val (cbV o.n o.i ys Nf)))) := by
  intro ρ hρ
  refine (cC_effOf S _ ls δ _ ρ).mpr ?_
  refine withbor_spans_yields hδ hbx hΔx hβ hT hB hP hNf (fundamentalC hN) (Row.tab S δ)
    (en := o.ent δ) (by simp [Row.tab, hf]) ha hq ?_ ys hys hy l v ls ρ hρ
  intro ls' w σ h
  simp only [OpSig.ent, hoB] at h
  exact ⟨h.2, h.1⟩

end GhostEnd
