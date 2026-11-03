import Support.Model.Tree.Reread
import Support.Model.Tree.Port.WalkSplitting

/-!
# Store types as syntactic codes read at the tree

`[spec §62]`. `Tree/Reread.lean`'s store typing `Θ : Loc → Option KSem` gives each location a
semantic type. Here, as Core's `FrameRec.T` is a syntactic type read at a substitution, a store
type is a code (`KTy`) and its meaning is read at the tree and at the code typing
(`KTy.interp`). The `Mut` clause reads `Θ ℓ = A` syntactically and stores `A`'s
meaning, so `interp` is structural in the code: there is no circularity to resolve.

* **The semantic typing is `sem Θ`** (`ℓ ↦ ⟦Θ ℓ⟧_Θ`); `Cov`, `RC`, `RR` are read at it unchanged,
  so every result of `Tree/Reread.lean` applies. The tree world (`World/World.lean`) carries a
  code typing and reads its cells at `sem`.
* **Every code is carried along re-reading** (`interp_retype`), at any re-typing that agrees
  on the locations the resource holds a `mut` cell at.
* **A location may be re-typed** when no `mut` cell at it is held (`RR.exists_retype`): a world
  covered at `sem Θ` has a re-reading covered at `sem Θ'` at any tree extension, for any `Θ'`
  agreeing with `Θ` on the locations the world holds a `mut` cell at (`HoldsMut`, at any depth).
  A freed location holds no cell, so it is re-typed by a re-reading. At `Θ' = Θ` and `K' = K` the
  re-reading is the identity (`RR.refl`).
* **Re-readings compose across re-typings** (`RR.trans_retype`): `RC` constrains only the
  re-read cell's invariant, so a re-reading at `sem Θ₁` followed by one at `sem Θ₂` is one at
  `sem Θ₂`. The held `mut` locations are kept by re-reading (`HoldsMut.rr`) and are those of the
  parts of a composite (`HoldsMut.of_compS_left`), so agreement passes along both.

The codes are `1`, `+`, `Imm`, `Mut`, `[a]` and `ref`; thunks are not coded here. `ref` is the
position a frame record's chain steps through (`World/Records.lean`).

**Departure (D9, `docs/new-core/scope-781.md` §8).** Store types are codes, with no substitution
`δ` and no `AdmWf`, by the ruling of condition 16 (`docs/new-core/conditions.md`). No printed
technique is left unbuilt by it.
-/

noncomputable section

namespace BoCa.Fig16.Tree.Wp
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree

/-- **A store type, as a code.** Departure D9 (`docs/new-core/scope-781.md` §8): codes, with no
substitution `δ` and no `AdmWf`, by the ruling of condition 16. -/
inductive KTy : Type where
  | unit
  | sum (A B : KTy)
  | imm (a : Life) (A : KTy)
  | mut (a : Life) (A : KTy)
  | box (a : Life) (A : KTy)
  | ref (A : KTy)

/-- A code typing of locations. -/
abbrev CodeTy : Type := BoCa.Loc → Option KTy

/-- **A code's meaning at the code typing `Θ`**, read at every tree. -/
def KTy.interp (Θ : CodeTy) : KTy → KSem
  | .unit => vUnit
  | .sum A B => vSum (A.interp Θ) (B.interp Θ)
  | .imm a A => vImm a (A.interp Θ)
  | .mut a A => ⟨fun K v ρ => ∃ (l : BoCa.Loc) (m : TMut K), v = BoCa.Val.loc l ∧
      ρ = PMap.sng l (.mut m) ∧ Θ l = some A ∧ (∀ x ∈ m.ls.set, K.le a x) ∧
      ∀ w r, m.P w r ↔ (A.interp Θ).P K w r.toU⟩
  | .box a A => vBox a (A.interp Θ)
  | .ref A => vRef (A.interp Θ)

/-- **The semantic store typing of a code typing.** -/
def sem (Θ : CodeTy) : LocTy := fun l => (Θ l).map (KTy.interp Θ)

theorem sem_of {Θ : CodeTy} {l : BoCa.Loc} {A : KTy} (h : Θ l = some A) :
    sem Θ l = some (A.interp Θ) := by simp [sem, h]

/-! ### Locations a world holds a `mut` cell at -/

/-- `ρ` holds a `mut` cell at `ℓ`, at any depth. -/
inductive HoldsMut {K : WCactus} : TRes K → BoCa.Loc → Prop where
  | top {ρ : TRes K} {l : BoCa.Loc} {m : TMut K} (e : ρ.get l = some (.mut m)) : HoldsMut ρ l
  | deep {ρ : TRes K} {k l : BoCa.Loc} {ψ : TCell K} (e : ρ.get k = some ψ)
      (h : HoldsMut ψ.wit l) : HoldsMut ρ l

/-- `Θ'` agrees with `Θ` wherever `ρ` holds a `mut` cell. -/
def AgreeOn {K : WCactus} (Θ Θ' : CodeTy) (ρ : TRes K) : Prop :=
  ∀ l, HoldsMut ρ l → Θ' l = Θ l

theorem AgreeOn.wit {K : WCactus} {Θ Θ' : CodeTy} {ρ : TRes K} (h : AgreeOn Θ Θ' ρ) {k : BoCa.Loc}
    {ψ : TCell K} (e : ρ.get k = some ψ) : AgreeOn Θ Θ' ψ.wit :=
  fun l hl => h l (.deep e hl)

theorem AgreeOn.refl {K : WCactus} (Θ : CodeTy) (ρ : TRes K) : AgreeOn Θ Θ ρ := fun _ _ => rfl

/-! ### Re-reading across a re-typing -/

/-- **A code's meaning is carried along a re-reading at a new tree and a new code typing**, when
the typings agree where the resource holds a `mut` cell. -/
theorem interp_retype {Θ Θ' : CodeTy} (A : KTy) :
    ∀ {K K' : WCactus}, K.Ext K' → ∀ (v : BoCa.Val) (ρ : TRes K) (ρ' : TRes K'),
      CovR (sem Θ) K ρ → RR (sem Θ') ρ ρ' → AgreeOn Θ Θ' ρ →
      (A.interp Θ).P K v ρ → (A.interp Θ').P K' v ρ' := by
  induction A with
  | unit =>
      rintro K K' - v ρ ρ' - hr - ⟨hv, rfl⟩
      exact ⟨hv, RR.of_empty hr⟩
  | sum A B ihA ihB =>
      rintro K K' hE v ρ ρ' hc hr hag (⟨v₁, rfl, h⟩ | ⟨v₂, rfl, h⟩)
      · exact Or.inl ⟨v₁, rfl, ihA hE v₁ ρ ρ' hc hr hag h⟩
      · exact Or.inr ⟨v₂, rfl, ihB hE v₂ ρ ρ' hc hr hag h⟩
  | imm a A ih =>
      rintro K K' hE v ρ ρ' hc hr hag ⟨l, i, rfl, rfl, hle, hP⟩
      obtain ⟨ψ', rfl, hrc⟩ := RR.of_sng hr
      have hci := hc.sng
      have e : (PMap.sng l (CellUT.imm i) : TRes K).get l = some (.imm i) := by
        simp [PMap.sng_get]
      cases hrc with
      | imm _ _ i' hs hv hdom hw =>
          cases hci with
          | imm _ _ hcw =>
              refine ⟨l, i', rfl, rfl, fun x hx => hE.le (hle x (hs ▸ hx)), ?_⟩
              rw [hv]
              exact ih hE _ _ _ hcw ⟨hdom, hw⟩ (hag.wit e) hP
  | «mut» a A _ =>
      rintro K K' hE v ρ ρ' - hr hag ⟨l, m, rfl, rfl, hΘ, hle, -⟩
      obtain ⟨ψ', rfl, hrc⟩ := RR.of_sng hr
      have hl : Θ' l = some A := by
        rw [hag l (.top (m := m) (by simp [PMap.sng_get]))]; exact hΘ
      cases hrc with
      | «mut» _ _ m' τ' hΘ' hs _ _ _ hP =>
          rw [sem_of hl] at hΘ'; cases Option.some.inj hΘ'
          refine ⟨l, m', rfl, rfl, hl, fun x hx => ?_, hP⟩
          rw [hs] at hx
          exact hE.le (hle x (K'.minS_sub hx))
  | box a A ih =>
      rintro K K' hE v ρ ρ' hc hr hag ⟨hP, hS⟩
      exact ⟨ih hE v ρ ρ' hc hr hag hP, hr.inStratum hE hS⟩
  | ref A ih =>
      classical
      rintro K K' hE v ρ ρ' hc hr hag ⟨l, w, ρ₁, rfl, hl, rfl, hP⟩
      obtain ⟨ψ', e', hrc⟩ := hr.get_some (m := l) (ψ := .own w) (by simp [PMap.ins_get])
      cases hrc
      have hr₁ : RR (sem Θ') ρ₁ (PMap.del ρ' l) := by
        refine ⟨fun m => ?_, fun m χ χ' e e'' => ?_⟩
        · rw [PMap.del_get]
          by_cases e : m = l
          · subst e; simp [hl]
          · rw [if_neg e]
            have := hr.1 m
            simp only [PMap.ins_get, if_neg e] at this
            exact this
        · rw [PMap.del_get] at e''
          by_cases em : m = l
          · rw [if_pos em] at e''; cases e''
          · rw [if_neg em] at e''
            exact hr.2 m χ χ' (by simp [PMap.ins_get, em, e]) e''
      have hne : ∀ m χ, ρ₁.get m = some χ → m ≠ l := fun m χ e h => by
        subst h; rw [hl] at e; cases e
      have hc₁ : CovR (sem Θ) K ρ₁ := fun m χ e => hc m χ (by simp [PMap.ins_get, hne m χ e, e])
      have hag₁ : AgreeOn Θ Θ' ρ₁ := fun m hm => hag m (by
        cases hm with
        | @top _ _ m₀ e =>
            exact HoldsMut.top (l := m) (m := m₀) (by simp [PMap.ins_get, hne _ _ e, e])
        | @deep _ k _ ψ e h =>
            exact HoldsMut.deep (k := k) (ψ := ψ) (by simp [PMap.ins_get, hne _ _ e, e]) h)
      refine ⟨l, w, PMap.del ρ' l, rfl, by simp [PMap.del_get], PMap.ext fun m => ?_,
        ih hE w ρ₁ _ hc₁ hr₁ hag₁ hP⟩
      rw [PMap.ins_get, PMap.del_get]
      by_cases e : m = l
      · subst e; simp [e']
      · simp [e]

/-- One cell's re-reading across a re-typing, from its witness's (`RC.exists_cell`'s proof). -/
theorem RC.exists_retype {Θ Θ' : CodeTy} {K K' : WCactus} (hE : K.Ext K') {l : BoCa.Loc}
    {ψ : TCell K} (hc : Cov (sem Θ) K l ψ) (hagl : ψ.kind = .mut → Θ' l = Θ l)
    (hagw : AgreeOn Θ Θ' ψ.wit) (hw : ∃ χ' : TRes K', RR (sem Θ') ψ.wit χ') :
    ∃ ψ' : TCell K', RC (sem Θ') l ψ ψ' := by
  cases hc with
  | own l v => exact ⟨_, .own l v⟩
  | imm l i _ =>
      obtain ⟨χ', hχ⟩ := hw
      have hs : χ'.InStratum i.ls := RR.inStratum hE hχ CellUT.wit_inStratum_imm
      let i' : TImm K' := ⟨i.ls, i.v, ResST.toRes ⟨χ', hs⟩⟩
      have hres : i'.res = χ' := ResST.toU_toRes ⟨χ', hs⟩
      refine ⟨.imm i', .imm l i i' rfl rfl ?_ ?_⟩
      · intro k; rw [hres]; exact hχ.1 k
      · intro k ψ ψ' e e'; rw [hres] at e'; exact hχ.2 k ψ ψ' e e'
  | «mut» l m τ hΘ hP hcw =>
      obtain ⟨χ', hχ⟩ := hw
      obtain ⟨A, hA, rfl⟩ := Option.map_eq_some_iff.mp hΘ
      have hA' : Θ' l = some A := (hagl rfl).trans hA
      have hs : χ'.InStratum (K'.minS m.ls) :=
        (RR.inStratum hE hχ CellUT.wit_inStratum_mut).minS
      have hτ : (A.interp Θ').P K' m.v χ' :=
        interp_retype A hE m.v m.res χ' hcw hχ hagw ((hP m.v m.ρ).mp m.hw)
      let m' : TMut K' := ⟨K'.minS m.ls, K'.minS_anti _, m.v, ResST.toRes ⟨χ', hs⟩,
        fun w r => (A.interp Θ').P K' w r.toU, by
          show (A.interp Θ').P K' m.v (ResST.toRes ⟨χ', hs⟩).toU
          rw [ResST.toU_toRes]; exact hτ⟩
      have hres : m'.res = χ' := ResST.toU_toRes ⟨χ', hs⟩
      refine ⟨.mut m', .mut l m m' _ (sem_of hA') rfl rfl ?_ ?_ fun _ _ => Iff.rfl⟩
      · intro k; rw [hres]; exact hχ.1 k
      · intro k ψ ψ' e e'; rw [hres] at e'; exact hχ.2 k ψ ψ' e e'

/-- Re-readings across a re-typing exist in every stratum (`RR.exists_stratum`'s proof). -/
theorem RR.exists_retype_stratum {Θ Θ' : CodeTy} {K K' : WCactus} (hE : K.Ext K') (T : TSet) :
    ∀ ρ : TRes K, ρ.InStratum T → CovR (sem Θ) K ρ → AgreeOn Θ Θ' ρ →
      ∃ ρ' : TRes K', RR (sem Θ') ρ ρ' := by
  induction T using K.above_wf.induction with
  | _ T ih =>
  intro ρ hT hc hag
  refine RR.exists_of fun l ψ e => RC.exists_retype hE (hc l ψ e) ?_ (hag.wit e) ?_
  · intro hk
    cases ψ with
    | «mut» m => exact hag l (.top e)
    | own => cases hk
    | imm => cases hk
  · have hcl := hc l ψ e
    cases hcl with
    | own => exact ⟨_, RR.empty⟩
    | imm _ i hw => exact ih i.ls (hT l _ e) i.res CellUT.wit_inStratum_imm hw (hag.wit e)
    | «mut» _ m _ _ _ hw => exact ih m.ls (hT l _ e) m.res CellUT.wit_inStratum_mut hw (hag.wit e)

/-- **A world re-read across a re-typing**: covered at `sem Θ`, with `Θ'` agreeing with `Θ`
wherever the world holds a `mut` cell, it has a re-reading at any tree extension, covered at
`sem Θ'`. -/
theorem RR.exists_retype {Θ Θ' : CodeTy} {K K' : WCactus} (hE : K.Ext K') {ρ : TRes K}
    (hc : CovR (sem Θ) K ρ) (hag : AgreeOn Θ Θ' ρ) :
    ∃ ρ' : TRes K', RR (sem Θ') ρ ρ' ∧ CovR (sem Θ') K' ρ' := by
  have : ∃ ρ' : TRes K', RR (sem Θ') ρ ρ' := by
    refine RR.exists_of fun l ψ e => RC.exists_retype hE (hc l ψ e) ?_ (hag.wit e) ?_
    · intro hk
      cases ψ with
      | «mut» m => exact hag l (.top e)
      | own => cases hk
      | imm => cases hk
    · have hcl := hc l ψ e
      cases hcl with
      | own => exact ⟨_, RR.empty⟩
      | imm _ i hw =>
          exact RR.exists_retype_stratum hE i.ls i.res CellUT.wit_inStratum_imm hw (hag.wit e)
      | «mut» _ m _ _ _ hw =>
          exact RR.exists_retype_stratum hE m.ls m.res CellUT.wit_inStratum_mut hw (hag.wit e)
  obtain ⟨ρ', hr⟩ := this
  exact ⟨ρ', hr, hr.cov⟩

/-! ### Held `mut` locations along re-reading and composition -/

/-- **A re-reading keeps the held `mut` locations.** -/
theorem HoldsMut.rr {Θ : LocTy} {K K' : WCactus} {ρ : TRes K} {l : BoCa.Loc} (h : HoldsMut ρ l) :
    ∀ {ρ' : TRes K'}, RR Θ ρ ρ' → HoldsMut ρ' l := by
  induction h with
  | top e =>
      intro ρ' hr
      obtain ⟨ψ', e', hc⟩ := hr.get_some e
      cases hc with
      | «mut» _ _ m' => exact .top e'
  | deep e _ ih =>
      intro ρ' hr
      obtain ⟨ψ', e', hc⟩ := hr.get_some e
      exact .deep e' (ih hc.wit)

/-- A `mut` cell held by a part is held by the composite. -/
theorem HoldsMut.of_compS_left {K : WCactus} {a b y : TRes K} (hc : ResUT.CompS a b y)
    {l : BoCa.Loc} (h : HoldsMut a l) : HoldsMut y l := by
  cases h with
  | top e => exact .top (hc.get_left_of_ne_imm e (by simp [CellUT.kind])).2
  | deep e h =>
      obtain ⟨ψ, e', -, hw⟩ := hc.get_left e
      exact .deep e' (hw ▸ h)

theorem HoldsMut.of_compS_right {K : WCactus} {a b y : TRes K} (hc : ResUT.CompS a b y)
    {l : BoCa.Loc} (h : HoldsMut b l) : HoldsMut y l :=
  HoldsMut.of_compS_left (ResUT.CompS.comm hc) h

theorem AgreeOn.of_compS_left {K : WCactus} {Θ Θ' : CodeTy} {a b y : TRes K}
    (hc : ResUT.CompS a b y) (h : AgreeOn Θ Θ' y) : AgreeOn Θ Θ' a :=
  fun l hl => h l (hl.of_compS_left hc)

theorem AgreeOn.of_compS_right {K : WCactus} {Θ Θ' : CodeTy} {a b y : TRes K}
    (hc : ResUT.CompS a b y) (h : AgreeOn Θ Θ' y) : AgreeOn Θ Θ' b :=
  fun l hl => h l (hl.of_compS_right hc)

/-- **Agreement composes along a re-reading.** -/
theorem AgreeOn.trans {Θ : LocTy} {K K' : WCactus} {Θ₁ Θ₂ Θ₃ : CodeTy} {ρ : TRes K}
    {ρ' : TRes K'} (h₁ : AgreeOn Θ₁ Θ₂ ρ) (hr : RR Θ ρ ρ') (h₂ : AgreeOn Θ₂ Θ₃ ρ') :
    AgreeOn Θ₁ Θ₃ ρ :=
  fun l hl => (h₂ l (hl.rr hr)).trans (h₁ l hl)

/-! ### Re-readings across re-typings compose -/

/-- One cell's re-readings composed, the second at another typing: `RC` constrains only the
re-read cell's invariant, so the composite is read at the second typing. -/
theorem RC.trans_retype {Θ₁ Θ₂ : LocTy} {K K' K'' : WCactus} (hE' : K'.Ext K'') {l : BoCa.Loc}
    {ψ : TCell K} {ψ' : TCell K'} (h : RC Θ₁ l ψ ψ') :
    ∀ {ψ'' : TCell K''}, RC Θ₂ l ψ' ψ'' → RC Θ₂ l ψ ψ'' := by
  induction h with
  | own l v => intro ψ'' h'; cases h'; exact .own l v
  | imm l i i' hs hv hdom hw ih =>
      intro ψ'' h'
      cases h' with
      | imm _ _ i'' hs' hv' hdom' hw' =>
          refine .imm l i i'' (hs'.trans hs) (hv'.trans hv) (fun k => (hdom k).trans (hdom' k))
            fun k ψ ψ'' e e'' => ?_
          obtain ⟨ψ', e', hr⟩ := RR.get_some (Θ := Θ₁) ⟨hdom, hw⟩ e
          exact ih k ψ ψ' e e' (hw' k ψ' ψ'' e' e'')
  | «mut» l m m' τ hΘ hs hv hdom hw hP ih =>
      intro ψ'' h'
      cases h' with
      | «mut» _ _ m'' τ' hΘ' hs' hv' hdom' hw' hP' =>
          refine .mut l m m'' τ' hΘ' (by rw [hs', hs, WCactus.minS_minS hE']) (hv'.trans hv)
            (fun k => (hdom k).trans (hdom' k)) (fun k ψ ψ'' e e'' => ?_) hP'
          obtain ⟨ψ', e', hr⟩ := RR.get_some (Θ := Θ₁) ⟨hdom, hw⟩ e
          exact ih k ψ ψ' e e' (hw' k ψ' ψ'' e' e'')

/-- **Re-readings across re-typings compose.** -/
theorem RR.trans_retype {Θ₁ Θ₂ : LocTy} {K K' K'' : WCactus} (hE' : K'.Ext K'') {ρ : TRes K}
    {ρ' : TRes K'} {ρ'' : TRes K''} (h : RR Θ₁ ρ ρ') (h' : RR Θ₂ ρ' ρ'') : RR Θ₂ ρ ρ'' := by
  refine ⟨fun k => (h.1 k).trans (h'.1 k), fun k ψ ψ'' e e'' => ?_⟩
  obtain ⟨ψ', e', hr⟩ := h.get_some e
  exact RC.trans_retype hE' hr (h'.2 k ψ' ψ'' e' e'')

end BoCa.Fig16.Tree.Wp

end
