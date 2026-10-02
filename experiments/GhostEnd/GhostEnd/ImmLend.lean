import GhostEnd.Frames
import GhostEnd.Instance

/-!
# GhostEnd — an `Imm` lend spanning a stop (#268, item 2)

`withbor` (1) lends `ℓ` as `Imm 'x T` through 6.64 (Imm Frame): the frame records the place, and
the callback receives `ℓ ↦ I_α`, the cell `imm({α}, v, ρ_P̂)`. An `imm` cell records a **set** of
lifetimes, and copies of a view compose by I Agree (`[TR]` 6.43: `imm(ᾱ) ● imm(β̄) = imm(ᾱ ∪ β̄)`).

**Ghost-ending is subtraction** (`[TR]` Definition 6.3, `⊟`). The internal lifetimes `t̄` are
removed from a cell's set `ᾱ`:

* if `ᾱ ∖ t̄ ≠ ∅`, the cell stays `imm(ᾱ ∖ t̄)`, shared with the outside, and
  `imm(ᾱ) = imm(ᾱ ∖ t̄) ● imm(t̄)` (`imm_ghostEnd_split`, 6.43 read back);
* if `ᾱ ∖ t̄ = ∅`, every copy was internal: `ᾱ = t̄` and the cell leaves the share
  (`imm_ghostEnd_empty`). At the lent place itself this is always the case, so 6.64's exit
  returns `ℓ ↦ own(v)` to the lender.

**Resume is union.** One fresh lifetime `α′` serves every internal copy: `imm(ᾱ ∖ t̄) ● imm({α′})
= imm((ᾱ ∖ t̄) ∪ {α′})` (`imm_relend_union`, 6.43), and the re-lent view is duplicated to each
position that held a copy (`relent_copies`, 6.116 `I-dup`). The value and witness never change,
so the lowered heap does not either (`imm_erase_sets`): the set changes which lifetimes share the
cell, never what the cell holds.

**The key step** is `ewpTS_I_frameR`: 6.64 at a resuming table, by induction on the callback's
own least fixed point (`RelendI`), with the printed proof `wpG_I_frameX` at each unfolding. Its
exit at a stop is the ghost end (the garbage at `ℓ` is exactly the internal view, removed:
6.38's H28), and each resumption re-applies its entry at a fresh lifetime. `relendI_yield` builds
such a callback, and `imm_spans_yield` discharges every hypothesis on one that yields with the lend
open.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace GhostEnd
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Kont Step1N Head performE opPayload)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Subtraction and union at one cell -/

section
variable {l : BoCa.Loc} {v : Val} {χ : WRes}

/-- **Ghost end, external copies left**: `imm(ᾱ) = imm(ᾱ ∖ t̄) ● imm(t̄)` when `t̄ ⊆ ᾱ` and
`ᾱ ∖ t̄ ≠ ∅` (`[TR]` 6.43 at `(ᾱ ∖ t̄) ∪ t̄ = ᾱ`), and `⊟` leaves exactly `imm(ᾱ ∖ t̄)`. -/
theorem imm_ghostEnd_split {s t u : LSet} (hts : ∀ x, t.mem x → s.mem x) (hu : LSet.Diff s t u)
    (hd : ¬ LSet.DiffEmpty s t) (hs : χ.InStratum s.join) (ht : χ.InStratum t.join) :
    ∃ hu' : χ.InStratum u.join,
      ResU.CompS (ResU.single l (CellU.immOf u v χ hu')) (ResU.single l (CellU.immOf t v χ ht))
        (ResU.single l (CellU.immOf s v χ hs)) ∧
      (CellU.immOf s v χ hs).subLS t = some (CellU.immOf u v χ hu') := by
  obtain ⟨hu', hsub⟩ := CellU.subLS_of_diff (v := v) (h := hs) hu hd
  refine ⟨hu', ?_, hsub⟩
  have h₃ : χ.InStratum (u ∪ t).join := by rw [LSet.diff_union hu hts]; exact hs
  have hc := ResU.compS_single_imm l u t v χ hu' ht h₃
  rwa [CellU.immOf_congr (LSet.diff_union hu hts) rfl rfl h₃ hs] at hc

/-- **Ghost end, every copy internal**: `ᾱ ∖ t̄ = ∅` with `t̄ ⊆ ᾱ` says `ᾱ = t̄`, and `⊟` removes
the cell. -/
theorem imm_ghostEnd_empty {s t : LSet} (hts : ∀ x, t.mem x → s.mem x)
    (hd : LSet.DiffEmpty s t) (hs : χ.InStratum s.join) :
    s = t ∧ (CellU.immOf s v χ hs).subLS t = none :=
  ⟨LSet.eq_of_diffEmpty hd hts, CellU.subLS_of_diffEmpty hd⟩

/-- **Re-lend is union**: one fresh lifetime `α′` beside what is left, by I Agree (`[TR]` 6.43). -/
theorem imm_relend_union (u : LSet) (α' : Life) (hu : χ.InStratum u.join)
    (h₁ : χ.InStratum (LSet.singleton α').join) (h₂ : χ.InStratum (u ∪ LSet.singleton α').join) :
    ResU.CompS (ResU.single l (CellU.immOf u v χ hu))
      (ResU.single l (CellU.immOf (LSet.singleton α') v χ h₁))
      (ResU.single l (CellU.immOf (u ∪ LSet.singleton α') v χ h₂)) :=
  ResU.compS_single_imm l u (LSet.singleton α') v χ hu h₁ h₂

/-- **The lowered value does not see the set**: `⟦imm(ᾱ, v, χ)⟧ = v` for every `ᾱ`, so
subtraction and union leave `⟦−⟧` unchanged while the cell stays `imm`. -/
theorem imm_erase_sets (s s' : LSet) (hs : χ.InStratum s.join) (hs' : χ.InStratum s'.join) :
    (CellU.immOf s v χ hs).erase = (CellU.immOf s' v χ hs').erase := rfl

end

/-- **One fresh lifetime for every internal copy**: the re-lent view splits into as many copies
as the frozen frames held (`[TR]` 6.116 `I-dup`, `ptoImmS_dup`). -/
theorem relent_copies {l : BoCa.Loc} {α : Life} {ls : List SRec} {P : List SRec → Val → WProp} :
    ∀ (n : ℕ) {ρ : WRes}, ptoImmS l α ls P ρ →
      ∃ τs : List WRes, τs.length = n + 1 ∧ (∀ τ ∈ τs, ptoImmS l α ls P τ) ∧
        ∀ τ ∈ τs, ∃ τ', ResU.CompS τ τ' ρ
  | 0, ρ, h => ⟨[ρ], rfl, by simpa using h, fun τ hτ => by
      simp only [List.mem_singleton] at hτ; subst hτ; exact ⟨PMap.empty, ResU.comp_empty_right τ⟩⟩
  | n + 1, ρ, h => by
      obtain ⟨τ₁, τ₂, hc, h₁, h₂⟩ := ptoImmS_dup h
      obtain ⟨τs, hlen, hall, hsub⟩ := relent_copies n h₂
      refine ⟨τ₁ :: τs, by simp [hlen], ?_, ?_⟩
      · intro τ hτ
        rcases List.mem_cons.mp hτ with rfl | hτ
        · exact h₁
        · exact hall τ hτ
      · intro τ hτ
        rcases List.mem_cons.mp hτ with rfl | hτ
        · exact ⟨τ₂, hc⟩
        · obtain ⟨τ', hτ'⟩ := hsub τ hτ
          obtain ⟨x, -, hx⟩ := compS_lcomm hτ' hc
          exact ⟨x, hx⟩

/-! ### 6.64 at a resuming table -/

/-- The lender's place while lent immutably: `ℓ ↦ v ⋆ 𝒱⟦T⟧(v)`, the value fixed. -/
def ownerI (l : BoCa.Loc) (v : Val) (T : VTy) (δ : LSub) (ls : List SRec) : WProp :=
  ptoOwn l v ⋆ vC true T ls δ v

theorem ownerI_local {l : BoCa.Loc} {v : Val} {T : VTy} {δ : LSub} {ls ls' : List SRec}
    {ρ : WRes} (he : Ext ls ls' ρ) (h : ownerI l v T δ ls ρ) : ownerI l v T δ ls' ρ := by
  obtain ⟨ρ₁, ρ₂, hc, ho, hv⟩ := h
  exact ⟨ρ₁, ρ₂, hc, ho, vC_local true T (he.right hc) hv⟩

/-- One unfolding of the immutably lent callback: 6.64's premise, the stop owing `ownerI ⋆ X`. -/
def relendIF (Tb : Table) (l : BoCa.Loc) (v : Val) (T : VTy) (δ : LSub)
    (Q : List SRec → Val → WProp) (X : List SRec → Expr → WProp) : List SRec → Expr → WProp :=
  fun ls e => fresh fun α ρ => ∀ ls', AddAt ls ls' α →
    (∃ r ∈ rsOf ls', r.le = l ∧ r.T = T ∧ r.δ = δ) →
    (ptoImmS l α ls' (fun ls₀ => vC true T ls₀ δ) ─⋆
      wpG ls' e (fun ls'' t => box α (ptoOwn l v ─⋆ (vC true T ls'' δ v ─⋆ fun ρ =>
        valPost Q ls'' t ρ ∨ Tb ls'' t (fun ls' e' => ownerI l v T δ ls' ⋆ X ls' e') ρ)))) ρ

/-- The immutably lent callback, re-lendable: the least fixed point of `relendIF`. -/
def RelendI (Tb : Table) (l : BoCa.Loc) (v : Val) (T : VTy) (δ : LSub)
    (Q : List SRec → Val → WProp) (ls : List SRec) (e : Expr) : WProp := fun ρ =>
  ∀ X : List SRec → Expr → WProp, (∀ ls e ρ, relendIF Tb l v T δ Q X ls e ρ → X ls e ρ) →
    X ls e ρ

section
variable {Tb : Table} {l : BoCa.Loc} {v : Val} {T : VTy} {δ : LSub} {Q : List SRec → Val → WProp}

theorem relendIF_mono (hTb : Tb.Mono) {X X' : List SRec → Expr → WProp}
    (hX : ∀ ls e ρ, X ls e ρ → X' ls e ρ) {ls : List SRec} {e : Expr} :
    Entails (relendIF Tb l v T δ Q X ls e) (relendIF Tb l v T δ Q X' ls e) := by
  rintro ρ ⟨γ, hγ⟩
  refine ⟨γ, fun α hα => ⟨fun ls' hadd hrec => ?_, (hγ α hα).2⟩⟩
  refine wand_mono_right (fun _ hw => wpG_mono (fun ls'' t σ hb => ?_) hw) ρ
    ((hγ α hα).1 ls' hadd hrec)
  refine ⟨fun ρa ρb ha hcab ρc ρd hv hccd => ?_, hb.2⟩
  rcases hb.1 ρa ρb ha hcab ρc ρd hv hccd with hq | hq
  · exact Or.inl hq
  · exact Or.inr (hTb _ _ _ _ _ (fun _ _ _ ⟨τ₁, τ₂, hc, ho, hx⟩ => ⟨τ₁, τ₂, hc, ho, hX _ _ _ hx⟩) hq)

theorem relendI_fold (hTb : Tb.Mono) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : relendIF Tb l v T δ Q (RelendI Tb l v T δ Q) ls e ρ) : RelendI Tb l v T δ Q ls e ρ :=
  fun X hX => hX ls e ρ (relendIF_mono hTb (fun _ _ _ h' => h' X hX) ρ h)

theorem relendI_unfold (hTb : Tb.Mono) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : RelendI Tb l v T δ Q ls e ρ) : relendIF Tb l v T δ Q (RelendI Tb l v T δ Q) ls e ρ :=
  h (fun ls e ρ => relendIF Tb l v T δ Q (RelendI Tb l v T δ Q) ls e ρ)
    (fun _ _ _ h' => relendIF_mono hTb (fun _ _ _ h'' => relendI_fold hTb h'') _ h')

theorem relendI_step (hTb : Tb.Mono) {ls : List SRec} {e e' : Expr}
    (hs : ∀ μ : Heap, Step1N μ e μ e') {ρ : WRes} (h : RelendI Tb l v T δ Q ls e' ρ) :
    RelendI Tb l v T δ Q ls e ρ := by
  refine relendI_fold hTb ?_
  obtain ⟨γ, hγ⟩ := relendI_unfold hTb h
  exact ⟨γ, fun α hα => ⟨fun ls' hadd hrec =>
    wand_mono_right (wpG_step hs ls' _) ρ ((hγ α hα).1 ls' hadd hrec), (hγ α hα).2⟩⟩

end

/-- **`[TR]` 6.64 at a resuming table: the ghost end and re-lend of an `Imm` lend spanning a
stop.** The owner and an immutably lent, re-lendable callback give the callback's `ewpTS`. At a
return this is 6.64. At a stop the lend ends as at a return (`wpG_I_frameX`, which never reads
the term): the internal view is the whole of the garbage at `ℓ` and is removed, the record is
dropped, and the owner is handed back. The continuation is owed the owner and the callback again;
when it is resumed, the frame re-applies 6.64 at a lifetime chosen fresh at that point, with a new
record. By induction on `RelendI`. `hTL`: the table's stops are carried along `Ext` (6.64's `hQ`
at a resuming table, `opTable_extR`). -/
theorem ewpTS_I_frameR (Tb : Table) (hTb : Tb.Mono)
    (hTL : ∀ ls₁ ls₂ t Φ ρ, Ext ls₁ ls₂ ρ → Tb ls₁ t Φ ρ → Tb ls₂ t Φ ρ)
    (l : BoCa.Loc) (v : Val) (T : VTy) (δ : LSub) (hadm : AdmWf T δ)
    (Q : List SRec → Val → WProp) (hQ : ∀ ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → Q ls₁ w ρ → Q ls₂ w ρ)
    (ls : List SRec) (e : Expr) :
    Entails (ownerI l v T δ ls ⋆ RelendI Tb l v T δ Q ls e) (ewpTS ls e Tb Q) := by
  rintro ρ ⟨ρo, ρr, hc, ho, hr⟩
  refine hr (fun ls e ρr => ∀ ρo ρ, ownerI l v T δ ls ρo → ResU.CompS ρo ρr ρ →
    ewpTS ls e Tb Q ρ) ?_ ρo ρ ho hc
  intro ls e ρr hF ρo ρ ho hc
  obtain ⟨ρl, ρP, hcl, hl, hv⟩ := ho
  obtain ⟨σ, hcσ, hcρ⟩ := compS_reassoc hcl hc
  refine ewp_fold hTb ?_
  refine wpG_I_frameX l T δ hadm v e ls _ ?_ ρ ⟨ρl, σ, hcρ, hl, ρP, ρr, hcσ, hv, ?_⟩
  · rintro ls₁ ls₂ t ρ' he (⟨w, rfl, hw⟩ | hw)
    · exact Or.inl ⟨w, rfl, hQ ls₁ ls₂ w ρ' he hw⟩
    · exact Or.inr (hTL ls₁ ls₂ t _ ρ' he hw)
  obtain ⟨γ, hγ⟩ := hF
  refine ⟨γ, fun α hα => ⟨fun ls' hadd hrec => ?_, (hγ α hα).2⟩⟩
  refine wand_mono_right (fun _ hw => wpG_mono (fun ls'' t τ hb => ?_) hw) ρr
    ((hγ α hα).1 ls' hadd hrec)
  refine ⟨fun ρa ρb ha hcab ρc ρd hv' hccd => ?_, hb.2⟩
  rcases hb.1 ρa ρb ha hcab ρc ρd hv' hccd with hq | hq
  · exact Or.inl hq
  · exact Or.inr (hTb _ _ _ _ _ (fun _ _ _ ⟨τ₁, τ₂, hcτ, ho', hx⟩ => hx τ₁ _ ho' hcτ) hq)

/-! ### Every hypothesis discharged -/

/-- The borrower's `imm` view owns nothing: it is a single `imm` cell. -/
theorem noOwn_ptoImmS {l : BoCa.Loc} {α : Life} {ls : List SRec}
    {P : List SRec → Val → WProp} {ρ : WRes} (h : ptoImmS l α ls P ρ) : NoOwn ρ := by
  obtain ⟨s, u, σ, hs, ls₀, rfl, -⟩ := h
  exact ResU.restrict_single_other (by simp)

/-- **An immutably lent callback at an answer**: its copies of the view are left behind. -/
theorem relendI_val {Tb : Table} (hTb : Tb.Mono) {l : BoCa.Loc} {v : Val} {T : VTy} {δ : LSub}
    {Q : List SRec → Val → WProp} {u : Val} (hu : ∀ ls, Entails (ownerI l v T δ ls) (Q ls u))
    (ls : List SRec) : RelendI Tb l v T δ Q ls (.val u) PMap.empty := by
  refine relendI_fold hTb ⟨⊤, fun α _ => ⟨fun ls' _ _ ρm ρ' hm hc => ?_,
    ResU.inStratum_empty α⟩⟩
  rw [eq_of_compS_empty_left hc]
  refine wpG_garbage (wpG_here ls' _ _ ρm ⟨PMap.empty, ρm, compS_empty_left ρm,
    noOwn_ptoImmS hm, ?_, ResU.inStratum_empty α⟩)
  intro ρa ρb ha hcab ρc ρd hv hccd
  rw [eq_of_compS_empty_left hcab] at hccd
  exact Or.inl ⟨u, rfl, hu _ ρd ⟨ρa, ρc, hccd, ha, hv⟩⟩

/-- **An immutably lent callback at a yield.** Its view is dropped (the ghost end), the owner
handed back joins the continuation, and at the resumption the frame re-lends at a fresh lifetime
with a new record. The yield is linear and resuming. -/
theorem relendI_yield (Tab : OpTab) {n i : UInt32} {en : OpEnt} (hTn : Tab n i = some en)
    (ha : en.abort = false) (hq : en.q = .lin)
    (hPB : ∀ ls w ρ, en.PB ls w ρ → w = Val.unit ∧ ρ = PMap.empty)
    {l : BoCa.Loc} {v : Val} {T : VTy} {δ : LSub} {Q : List SRec → Val → WProp}
    {y : Val} (hy : ∀ ls, en.PA ls y PMap.empty) {rest : Expr}
    (h : ∀ ls, RelendI (opTable Tab) l v T δ Q ls rest PMap.empty) (ls : List SRec) :
    RelendI (opTable Tab) l v T δ Q ls (yieldSeq n i y rest) PMap.empty := by
  refine relendI_fold (opTable_mono Tab) ⟨⊤, fun α _ => ⟨fun ls' _ _ ρm ρ' hm hc => ?_,
    ResU.inStratum_empty α⟩⟩
  rw [eq_of_compS_empty_left hc]
  refine wpG_garbage (wpG_here ls' _ _ ρm ⟨PMap.empty, ρm, compS_empty_left ρm,
    noOwn_ptoImmS hm, ?_, ResU.inStratum_empty α⟩)
  intro ρa ρb hown hcab ρc ρd hv hccd
  rw [eq_of_compS_empty_left hcab] at hccd
  refine Or.inr (Or.inl ⟨.seq .hole rest, n, i, y, en, pure_sep_mk ⟨rfl, rfl, hTn, ha⟩
    ⟨PMap.empty, ρd, compS_empty_left ρd, hy ls', ?_⟩⟩)
  refine ⟨fun hu => absurd (hq.symm.trans hu) (by decide),
    fun ls'' hext => ⟨fun w' τ₁ τ₂ hBw hcτ => ?_, fun hl => absurd hq hl⟩⟩
  obtain ⟨rfl, rfl⟩ := hPB _ _ _ hBw
  rw [ResU.CompS.functional hcτ (ResU.comp_empty_right ρd)]
  refine ⟨ρd, PMap.empty, ResU.comp_empty_right ρd,
    ownerI_local hext ⟨ρa, ρc, hccd, hown, hv⟩, ?_⟩
  exact relendI_step (opTable_mono Tab) (fun μ => Step1N.head (Head.seq μ rest) rfl) (h ls'')

open GhostEnd.Instance in
/-- **An `Imm` lend spanning a yield, every hypothesis discharged**, at the row
`{yield : I32 ↠ 1}`: the callback yields once with the lend open, then returns `()`. -/
theorem imm_spans_yield (δ : LSub) (l : BoCa.Loc) (v : Val) (ls : List SRec) :
    Entails (ownerI l v .unit δ ls)
      (ewpTS ls (yieldSeq yieldOp.n yieldOp.i (Val.i32 1) (.val .unit))
        (opTable (Row.tab [yieldOp] δ)) (fun ls _ => ownerI l v .unit δ ls)) := by
  have hL : (Row.tab [yieldOp] δ).Local := by
    intro n i en hT ls ls' w ρ he
    obtain ⟨o, hf, rfl⟩ := Row.tab_some hT
    exact ⟨fun h => vC_local true _ he h, fun h => vC_local true _ he h⟩
  intro ρ ho
  refine ewpTS_I_frameR _ (opTable_mono _) (fun _ _ _ _ _ he h => opTable_extR hL he h) l v .unit
    δ (fun _ h => absurd h (by simp [VFree])) _ (fun _ _ _ _ he h => ownerI_local he h) ls _ ρ
    ⟨ρ, PMap.empty, ResU.comp_empty_right ρ, ho, ?_⟩
  refine relendI_yield (Row.tab [yieldOp] δ) (en := yieldOp.ent δ)
    (by simp [Row.tab, Row.find, yieldOp]) rfl rfl ?_ (fun ls => ⟨rfl, 1, rfl⟩)
    (fun ls => relendI_val (opTable_mono _) (fun _ _ h => h) ls) ls
  intro ls w σ h
  simp only [OpSig.ent, yieldOp] at h
  exact ⟨h.2, h.1⟩

end GhostEnd
