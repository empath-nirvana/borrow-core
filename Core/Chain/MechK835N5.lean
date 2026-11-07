import Core.Chain.MechK835N3
import Core.Chain.Iter835N

/-!
# The loop rule with a close path, at `erwpK`  `[spec §14]`

`docs/new-core/scope-835-kripke-stop.md` §2, class M, continued from `MechK835N3.lean`
(`erwpK_iterate`). The tick is answered *next* or *close*: at *next* the loop goes round at the
world the tick is resumed at, below the tick's index; at *close* the close observation runs there
under `inr`. The invariant is read at a world and carried along the tick's order (`htick`'s last
clause). Each `erwp` statement is proved again at one world (`*_of_K`); its text is the
original's.

`erwpK_iterateCI` reads its runs at the worlds an invariant `Inv` holds at: a location family is
downward closed, and a table closed in the index and under the loop's contexts, only at those
(`OpTabK.DownI`, `OpTabK.CtxClosedI`, `erwpK_bind_leI`). The loop starts at such a world, and the
post order and every world a table's entry owes at keep it. At one world `Inv` is `True`; at the
typed world it is a downward-closed location typing (`IterKW835N.lean`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Head Kont performE raiseE cancelVal opPayload)

variable {ι : Type}

/-! ### Closure read at the worlds an invariant holds at -/

/-- **`OpTabK.Down` at the worlds `Inv` holds at**: payloads downward closed; cancel obligations
downward closed at every world `Inv` holds at; every world an entry owes at is one. -/
structure OpTabK.DownI (Inv : ι → Prop) (T : OpTabK ι) : Prop where
  pa : ∀ n i en, T n i = some en → ∀ k ls v ρ, en.PA (k + 1) ls v ρ → en.PA k ls v ρ
  fin : ∀ n i en P, T n i = some en → en.fin = some P → ∀ y, Inv y → ∀ k ls e ρ,
    P y (k + 1) ls e ρ → P y k ls e ρ
  wkI : ∀ n i en, T n i = some en → ∀ f y ρ, en.wk f y ρ → Inv y

theorem OpTabK.Down.downI {T : OpTabK ι} (h : T.Down) : T.DownI (fun _ => True) where
  pa := h.pa
  fin := fun n i en P hT hP y _ => h.fin n i en P hT hP y
  wkI := fun _ _ _ _ _ _ _ _ => trivial

theorem opTableK_downI {Inv : ι → Prop} {lo : Life} {T : OpTabK ι} (hT : T.DownI Inv) :
    (opTableK lo T).Down := by
  intro k ls t Ψ ρ h
  rcases h with ⟨K, n, i, v, en, h⟩ | ⟨K, n, i, v, en, h⟩
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρk, hc, hA, hu, f, hf, hcont⟩ := pure_sep_iff.mp h
    refine Or.inl ⟨K, n, i, v, en, pure_sep_mk ⟨h₁, h₂, h₃, h₄⟩ ⟨ρa, ρk, hc,
      hT.pa _ _ _ h₃ _ _ _ _ hA, hu, f, hf, fun y hy ls' he =>
      ⟨fun k' hk => (hcont y hy ls' he).1 k' (by omega), fun hq P hP =>
        hT.fin _ _ _ _ h₃ hP y (hT.wkI _ _ _ h₃ f y ρk hy) _ _ _ _
          ((hcont y hy ls' he).2 hq P hP)⟩⟩⟩
  · obtain ⟨⟨h₁, h₂, h₃, h₄⟩, ρa, ρn, hc, ⟨hA, hnA⟩, hnn⟩ := pure_sep_iff.mp h
    exact Or.inr ⟨K, n, i, v, en, pure_sep_mk ⟨h₁, h₂, h₃, h₄⟩
      ⟨ρa, ρn, hc, ⟨hT.pa _ _ _ h₃ _ _ _ _ hA, hnA⟩, hnn⟩⟩

/-- **`OpTabK.CtxClosed` at the worlds `Inv` holds at**: the cancel obligations of `T`'s entries
are kept when `K` is put around the continuation they cancel, at every world `Inv` holds at. -/
def OpTabK.CtxClosedI (Inv : ι → Prop) (T : OpTabK ι) (K : Kont) : Prop :=
  ∀ m i en P, T m i = some en → en.fin = some P → ∀ y, Inv y → ∀ k ls (K' : Kont) x ρ,
    P y k ls (K'.dead.plug x) ρ → P y k ls ((K.comp K').dead.plug x) ρ

theorem OpTabK.CtxClosed.ctxClosedI {T : OpTabK ι} {K : Kont} (h : T.CtxClosed K) :
    T.CtxClosedI (fun _ => True) K :=
  fun m i en P hT hP y _ => h m i en P hT hP y

/-- **Pure steps in front of an `erwpK`, for free** (`erwp_pureSteps`). -/
theorem erwpK_pureSteps {V : ι → ι → Prop} {Φ : ι → LocFam} {Tb : ι → TableK ι} {Q : ι → PostN}
    {x : ι} (hΦ : (Φ x).Down) (hTd : (Tb x).Down) (hQ : ∀ y, (Q y).Down) {e e' : Expr}
    (hs : PureSteps (ℍ := ℍ) e e') {n : Nat} {ls : List SRec} {ρ : WRes}
    (h : erwpK (ℍ := ℍ) V Φ Tb Q x n ls e' ρ) : erwpK (ℍ := ℍ) V Φ Tb Q x n ls e ρ := by
  induction hs using Relation.ReflTransGen.head_induction_on with
  | refl => exact h
  | head hab _ ih =>
      refine erwpK_det hΦ hTd hQ (fun μ => ?_) ih
      obtain ⟨K, a, a', he, he', hh, hn⟩ := hab μ
      rw [he, he']
      exact step1Only_plug hh hn K

/-- **The loop rule at `erwpK`, its tick answered *next* or *close*** (`erwp_iterateC`). A turn's
value is posted at the world its run chose; the tick there chooses the table's floor, and at every
world its entry owes the loop goes on, the invariant carried there (`htick`). -/
theorem erwpK_iterateC {V : ι → ι → Prop} (hV : ∀ y, V y y)
    (hVt : ∀ x y z, V x y → V y z → V x z) {Φ : ι → LocFam} (hΦ : ∀ x, (Φ x).Down)
    (hΦV : ∀ x y, V x y → Φ y = Φ x) {fl : ι → Life} {T : ι → OpTabK ι}
    (hTD : ∀ x, (T x).Down)
    (hTV : ∀ x y, V x y → (opTableK (fl y) (T y)).Le (opTableK (fl x) (T x)))
    {f : Val} (hK : ∀ x, (T x).CtxClosed (iterK f)) (hKi : ∀ x, (T x).CtxClosed inrK)
    {QL QR : ι → PostN} (hQL : ∀ y, (QL y).Down) (hf : closedAt 0 f.1 = true)
    {I : ι → Val → WProp}
    (htick : ∀ x, ∃ en, T x divEff 0 = some en ∧ en.abort = false ∧ en.q = .lin ∧
      (∀ k ls, en.PA k ls Val.unit PMap.empty) ∧
      (∀ y k ls w (ρ : WRes), en.PB y k ls w ρ → (w = nextV ∨ w = closeV) ∧ ρ = PMap.empty) ∧
      ∀ fl' y s ρ, en.wk fl' y ρ → I x s ρ → I y s ρ)
    (hIc : ∀ x s ρ, I x s ρ → closedAt 0 s.1 = true)
    (hturn : ∀ y k s ls ρ, I y s ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) (fun z => turnPostN (I z) (QL z)) y k
        ls (.app (.app (.val f) (.val s)) (.val nextV)) ρ)
    (hclose : ∀ y k s ls ρ, I y s ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) QR y k ls (obsCN f s) ρ)
    (hQLR : ∀ y k ls r ρ, QR y k ls r ρ → QL y k ls (Val.inj₂ r) ρ) :
    ∀ n x s ls ρ, I x s ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) QL x n ls (iterateE f s) ρ := by
  have hD : ∀ x, (opTableK (fl x) (T x)).Down := fun x => opTableK_down (hTD x)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro x s ls ρ hI
  refine erwpK_det (hΦ x) (hD x) hQL (fun μ => step1Only_plug (Head.iterate μ f s) rfl .hole) ?_
  simp only [Kont.plug_hole]
  rw [iterNext_eq]
  refine erwpK_bind_le hVt hΦ hΦV hTV (iterK f) (fun m => by simp [iterK, Kont.HasHnd])
    (fun m => by simp [iterK, Kont.Catches]) hK n ?_ n le_rfl x ls _ ρ (hturn x n s ls ρ hI)
  rintro y k ls' v σ hk (⟨x', rfl, hx⟩ | ⟨s', rfl, hs'⟩)
  · refine erwpK_det (hΦ y) (hD y) hQL
      (fun μ => step1Only_plug (Head.case₁ μ x' _ _) rfl .hole) ?_
    exact erwpK_val (v := Val.inj₁ x') (hV y) hx
  · refine erwpK_det (hΦ y) (hD y) hQL
      (fun μ => step1Only_plug (Head.case₂ μ s' _ _) rfl .hole) ?_
    simp only [Kont.plug_hole]
    rw [iterK_case₂]
    obtain ⟨en, htk, hab, hq, hta, htb, hIk⟩ := htick y
    refine erwpK_perform _ (by simp [Kont.HasHnd]) htk hab hq (compS_empty_left σ) (hta k ls')
      (fl y) le_rfl (fun y' hy' ls'' _ k' hk' w σB XB hB hXB => ?_)
    obtain ⟨hw, rfl⟩ := htb y' k' ls'' w σB hB
    obtain rfl : XB = σ := ResU.CompS.functional hXB (ResU.comp_empty_right σ)
    have hs'' : I y' s' XB := hIk (fl y) y' s' XB hy' hs'
    refine erwpK_det (hΦ y') (hD y') hQL
      (fun μ => step1Only_plug (Head.beta μ _ w) rfl .hole) ?_
    simp only [Kont.plug_hole]
    rw [iterTurn_subst hf (hIc y' s' XB hs'')]
    rcases hw with rfl | rfl
    · -- *next*: round again
      refine erwpK_det (hΦ y') (hD y') hQL
        (fun μ => step1Only_plug (Head.case₁ μ Val.unit _ _) rfl .hole) ?_
      simp only [Kont.plug_hole, Expr.subst, subst_closedAt _ _ hf (Nat.zero_le _),
        subst_closedAt _ _ (hIc y' s' XB hs'') (Nat.zero_le _)]
      exact ih k' (by omega) y' s' ls'' XB hs''
    · -- *close*: the close path, `inr ((f s′).2)`
      refine erwpK_det (hΦ y') (hD y') hQL
        (fun μ => step1Only_plug (Head.case₂ μ Val.unit _ _) rfl .hole) ?_
      simp only [Kont.plug_hole, Expr.subst, subst_closedAt _ _ hf (Nat.zero_le _),
        subst_closedAt _ _ (hIc y' s' XB hs'') (Nat.zero_le _)]
      change erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) QL y' k' ls''
        (inrK.plug (obsCN f s')) XB
      refine erwpK_bind hVt hΦ hΦV hTV inrK inrK_plain.1 inrK_plain.2 hKi
        (fun y₁ k₁ ls₁ r ρ₁ hr => ?_) k' y' ls'' _ XB (hclose y' k' s' ls'' XB hs'')
      refine erwpK_det (hΦ y₁) (hD y₁) hQL
        (fun μ => step1Only_plug (Head.beta μ _ r) rfl .hole) ?_
      simp only [Kont.plug_hole]
      exact erwpK_val (v := Val.inj₂ r) (hV y₁) (hQLR y₁ k₁ ls₁ r ρ₁ hr)

/-- `erwp_iterateC` from `erwpK_iterateC`. -/
theorem erwp_iterateC_of_K {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} (hTD : T.Down)
    {f : Val} (hK : T.CtxClosed (iterK f)) (hKi : T.CtxClosed inrK) {QL QR : PostN}
    (hQL : QL.Down) (hf : closedAt 0 f.1 = true) {I : Val → WProp} {en : OpEntN}
    (htick : T divEff 0 = some en) (hab : en.abort = false) (hq : en.q = .lin)
    (hta : ∀ k ls, en.PA k ls Val.unit PMap.empty)
    (htb : ∀ k ls w (ρ : WRes), en.PB k ls w ρ → (w = nextV ∨ w = closeV) ∧ ρ = PMap.empty)
    (hIc : ∀ s ρ, I s ρ → closedAt 0 s.1 = true)
    (hturn : ∀ k s ls ρ, I s ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) (turnPostN I QL) k ls
        (.app (.app (.val f) (.val s)) (.val nextV)) ρ)
    (hclose : ∀ k s ls ρ, I s ρ → erwp (ℍ := ℍ) Φ (opTableN T) QR k ls (obsCN f s) ρ)
    (hQLR : ∀ k ls r ρ, QR k ls r ρ → QL k ls (Val.inj₂ r) ρ) :
    ∀ n s ls ρ, I s ρ → erwp (ℍ := ℍ) Φ (opTableN T) QL n ls (iterateE f s) ρ := by
  intro n s ls ρ hI
  rw [erwp_opTableN_eq_erwpK 0]
  refine erwpK_iterateC (ℍ := ℍ) (V := fun _ _ => True) (fun _ => trivial)
    (fun _ _ _ _ _ => trivial) (Φ := fun _ => Φ) (fun _ => hΦ) (fun _ _ _ => rfl)
    (fl := fun _ => 0) (T := fun _ => liftTabK T) (fun _ => hTD.liftK)
    (fun _ _ _ _ _ _ _ _ h => h) (fun _ => liftTabK_ctxClosed hK)
    (fun _ => liftTabK_ctxClosed hKi) (QL := fun _ => QL) (QR := fun _ => QR)
    (fun _ => hQL) hf (I := fun _ => I)
    (fun _ => ⟨liftEntK en, liftTabK_of_some htick, hab, hq, hta,
      fun _ k ls w ρ hB => htb k ls w ρ hB, fun _ _ _ _ _ h => h⟩)
    (fun _ => hIc) ?_ ?_ (fun _ => hQLR) n () s ls ρ hI
  · intro y k s' ls' ρ' hI'
    have h := hturn k s' ls' ρ' hI'
    rw [erwp_opTableN_eq_erwpK 0] at h
    exact h
  · intro y k s' ls' ρ' hI'
    have h := hclose k s' ls' ρ' hI'
    rw [erwp_opTableN_eq_erwpK 0] at h
    exact h

/-- **Bind at `erwpK` up to an index, read at the worlds `Inv` holds at** (`erwpK_bind_le`): the
run starts at such a world, the post order and every world a stop owes at keep `Inv`, and the
context's closure under the tables is read there. -/
theorem erwpK_bind_leI {V : ι → ι → Prop} (hVt : ∀ x y z, V x y → V y z → V x z)
    {Φ : ι → LocFam} {Inv : ι → Prop} (hΦ : ∀ x, Inv x → (Φ x).Down)
    (hΦV : ∀ x y, V x y → Φ y = Φ x) (hVI : ∀ x y, V x y → Inv x → Inv y) {fl : ι → Life}
    {T : ι → OpTabK ι} (hTV : ∀ x y, V x y → (opTableK (fl y) (T y)).Le (opTableK (fl x) (T x)))
    {Q Q' : ι → PostN} (K : Kont) (hH : ∀ m, K.HasHnd m = false)
    (hC : ∀ m, K.Catches m = false) (hK : ∀ x, (T x).CtxClosedI Inv K)
    (hwkI : ∀ x m i en, T x m i = some en → ∀ f y ρ, en.wk f y ρ → Inv y) (N : Nat)
    (hcont : ∀ y, Inv y → ∀ k ls (v : Val) ρ, k ≤ N → Q' y k ls v ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q y k ls (K.plug v.1) ρ) :
    ∀ n, n ≤ N → ∀ x, Inv x → ∀ ls e ρ,
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q' x n ls e ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) Q x n ls (K.plug e) ρ := by
  have hL : ∀ z, (opTableK (fl z) (T z)).Local := fun z => opTableK_local _ _
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN x hx ls e ρ h
  rw [erwpK_eq]
  refine rwpG_bind (hΦ x hx) K ?_
  refine rwpG_mono_le (fun k hk ls' t σ ht => ?_) (erwpK_unfold_at hL le_rfl h)
  rcases ht with ⟨v, rfl, y, hy, hv⟩ | ht | ht
  · exact erwpK_shift hVt hΦV hTV hL hy hk (hcont y (hVI x y hy hx) k ls' v σ (by omega) hv)
  · obtain ⟨K₁, m, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, ρa, ρk, hcak, hA, hu, f, hf, hcont'⟩ := pure_sep_iff.mp hp
    have hKo : (K.comp K₁).HasHnd m = false := by simp [hasHnd_comp, hH, hK₁]
    have ht' : K.plug (K₁.plug (performE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE false (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    refine rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inl
      ⟨K.comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩
        ⟨ρa, ρk, hcak, hA, hu, f, hf, fun y hy ls'' he => ⟨fun k' hk' w τ₁ τ₂ hB hcτ => ?_,
          fun hq' P hP => ?_⟩⟩⟩))
    · rw [Kont.plug_comp]
      have hc := (hcont' y hy ls'' he).1 k' hk' w τ₁ τ₂ hB hcτ
      simp only [erwpCK, show k' < n by omega, if_true] at hc ⊢
      exact ih k' (by omega) (by omega) y (hwkI x m i en hT f y ρk hy) _ _ _ hc
    · exact hK x m i en P hT hP y (hwkI x m i en hT f y ρk hy) _ _ _ _ _
        ((hcont' y hy ls'' he).2 hq' P hP)
  · obtain ⟨K₁, m, i, v, en, hp⟩ := ht
    obtain ⟨⟨rfl, hK₁, hT, ha⟩, hrest⟩ := pure_sep_iff.mp hp
    have hKo : (K.comp K₁).Catches m = false := by simp [catches_comp, hC, hK₁]
    have ht' : K.plug (K₁.plug (raiseE (.val (opPayload m i v)))) =
        (K.comp K₁).plug (opE true (opPayload m i v)) := by
      rw [Kont.plug_comp]; rfl
    rw [ht']
    exact rwpG_here (final_opPlug (payloadName_opPayload m i v) hKo) (Or.inr (Or.inr
      ⟨K.comp K₁, m, i, v, en, pure_sep_mk ⟨rfl, hKo, hT, ha⟩ hrest⟩))

/-- **E14 at an invariant read at the index, at `erwpK`** (`erwp_iterateCI`): the invariant is read
at a world and an index; the turns and the close paths are owed up to the index `N`. The runs are
read at the worlds `Inv` holds at: the loop starts at one, and the post order and every world the
table's entries owe at keep it; the tables' closure in the index and under the loop's contexts is
read there (`OpTabK.DownI`, `OpTabK.CtxClosedI`). -/
theorem erwpK_iterateCI {V : ι → ι → Prop} (hV : ∀ y, V y y)
    (hVt : ∀ x y z, V x y → V y z → V x z) {Φ : ι → LocFam} {Inv : ι → Prop}
    (hΦ : ∀ x, Inv x → (Φ x).Down) (hΦV : ∀ x y, V x y → Φ y = Φ x)
    (hVI : ∀ x y, V x y → Inv x → Inv y) {fl : ι → Life} {T : ι → OpTabK ι}
    (hTD : ∀ x, (T x).DownI Inv)
    (hTV : ∀ x y, V x y → (opTableK (fl y) (T y)).Le (opTableK (fl x) (T x)))
    {f : Val} (hK : ∀ x, (T x).CtxClosedI Inv (iterK f)) (hKi : ∀ x, (T x).CtxClosedI Inv inrK)
    {QL QR : ι → PostN} (hQL : ∀ y, (QL y).Down) {I : ι → Nat → Val → WProp}
    (hIle : ∀ y k k' s ρ, k' ≤ k → I y k s ρ → I y k' s ρ)
    (htick : ∀ x, ∃ en, T x divEff 0 = some en ∧ en.abort = false ∧ en.q = .lin ∧
      (∀ k ls, en.PA k ls Val.unit PMap.empty) ∧
      (∀ y k ls w (ρ : WRes), en.PB y k ls w ρ → (w = nextV ∨ w = closeV) ∧ ρ = PMap.empty) ∧
      ∀ fl' y k s ρ, en.wk fl' y ρ → I x k s ρ → I y k s ρ)
    (N : Nat)
    (hturn : ∀ y, Inv y → ∀ k, k ≤ N → ∀ s ls ρ, I y k s ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) (fun z => turnPostNI (I z) (QL z)) y k
        ls (.app (.app (.val f) (.val s)) (.val nextV)) ρ)
    (hclose : ∀ y, Inv y → ∀ k, k ≤ N → ∀ s ls ρ, I y k s ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) QR y k ls (obsCN f s) ρ)
    (hQLR : ∀ y k ls r ρ, QR y k ls r ρ → QL y k ls (Val.inj₂ r) ρ) :
    ∀ n, n ≤ N → ∀ x, Inv x → ∀ s ls ρ, I x n s ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) QL x n ls (iterateE f s) ρ := by
  have hD : ∀ x, (opTableK (fl x) (T x)).Down := fun x => opTableK_downI (hTD x)
  have hwkI : ∀ x m i en, T x m i = some en → ∀ f y ρ, en.wk f y ρ → Inv y :=
    fun x => (hTD x).wkI
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN x hx s ls ρ hI
  refine erwpK_det (hΦ x hx) (hD x) hQL
    (fun μ => step1Only_plug (Head.iterate μ f s) rfl .hole) ?_
  simp only [Kont.plug_hole]
  rw [iterNext_eq]
  refine erwpK_bind_leI hVt hΦ hΦV hVI hTV (iterK f) (fun m => by simp [iterK, Kont.HasHnd])
    (fun m => by simp [iterK, Kont.Catches]) hK hwkI n ?_ n le_rfl x hx ls _ ρ
    (hturn x hx n hnN s ls ρ hI)
  rintro y hy k ls' v σ hk (⟨x', rfl, hx'⟩ | ⟨s', rfl, hs'⟩)
  · refine erwpK_det (hΦ y hy) (hD y) hQL
      (fun μ => step1Only_plug (Head.case₁ μ x' _ _) rfl .hole) ?_
    exact erwpK_val (v := Val.inj₁ x') (hV y) hx'
  · refine erwpK_det (hΦ y hy) (hD y) hQL
      (fun μ => step1Only_plug (Head.case₂ μ s' _ _) rfl .hole) ?_
    simp only [Kont.plug_hole]
    rw [iterK_case₂]
    obtain ⟨en, htk, hab, hq, hta, htb, hIk⟩ := htick y
    refine erwpK_perform _ (by simp [Kont.HasHnd]) htk hab hq (compS_empty_left σ) (hta k ls')
      (fl y) le_rfl (fun y' hy' ls'' _ k' hk' w σB XB hB hXB => ?_)
    have hy'I : Inv y' := hwkI y _ _ en htk (fl y) y' σ hy'
    obtain ⟨hw, rfl⟩ := htb y' k' ls'' w σB hB
    obtain rfl : XB = σ := ResU.CompS.functional hXB (ResU.comp_empty_right σ)
    have hs'' : I y' k' s' XB := hIle y' k k' s' XB (by omega) (hIk (fl y) y' k s' XB hy' hs')
    rcases hw with rfl | rfl
    · -- *next*: round again
      refine erwpK_pureSteps (hΦ y' hy'I) (hD y') hQL
        (BoCa.Fig16.LogRel.Core.turnK_next f s') ?_
      exact ih k' (by omega) (by omega) y' hy'I s' ls'' XB hs''
    · -- *close*: the close path, `inr ((f s′).2)`
      refine erwpK_pureSteps (hΦ y' hy'I) (hD y') hQL
        (BoCa.Fig16.LogRel.Core.turnK_close f s') ?_
      change erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) QL y' k' ls''
        (inrK.plug (obsCN f s')) XB
      refine erwpK_bind_leI hVt hΦ hΦV hVI hTV inrK inrK_plain.1 inrK_plain.2 hKi hwkI k'
        (fun y₁ hy₁ k₁ ls₁ r ρ₁ _ hr => ?_) k' le_rfl y' hy'I ls'' _ XB
        (hclose y' hy'I k' (by omega) s' ls'' XB hs'')
      refine erwpK_pureSteps (hΦ y₁ hy₁) (hD y₁) hQL (BoCa.Fig16.LogRel.Core.inrV_steps r) ?_
      exact erwpK_val (v := Val.inj₂ r) (hV y₁) (hQLR y₁ k₁ ls₁ r ρ₁ hr)

/-- `erwp_iterateCI` from `erwpK_iterateCI`. -/
theorem erwp_iterateCI_of_K {Φ : LocFam} (hΦ : Φ.Down) {T : OpTabN} (hTD : T.Down)
    {f : Val} (hK : T.CtxClosed (iterK f)) (hKi : T.CtxClosed inrK) {QL QR : PostN}
    (hQL : QL.Down) {I : Nat → Val → WProp}
    (hIle : ∀ k k' s ρ, k' ≤ k → I k s ρ → I k' s ρ) {en : OpEntN}
    (htick : T divEff 0 = some en) (hab : en.abort = false) (hq : en.q = .lin)
    (hta : ∀ k ls, en.PA k ls Val.unit PMap.empty)
    (htb : ∀ k ls w (ρ : WRes), en.PB k ls w ρ → (w = nextV ∨ w = closeV) ∧ ρ = PMap.empty)
    (N : Nat)
    (hturn : ∀ k, k ≤ N → ∀ s ls ρ, I k s ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) (turnPostNI I QL) k ls
        (.app (.app (.val f) (.val s)) (.val nextV)) ρ)
    (hclose : ∀ k, k ≤ N → ∀ s ls ρ, I k s ρ →
      erwp (ℍ := ℍ) Φ (opTableN T) QR k ls (obsCN f s) ρ)
    (hQLR : ∀ k ls r ρ, QR k ls r ρ → QL k ls (Val.inj₂ r) ρ) :
    ∀ n, n ≤ N → ∀ s ls ρ, I n s ρ → erwp (ℍ := ℍ) Φ (opTableN T) QL n ls (iterateE f s) ρ := by
  intro n hnN s ls ρ hI
  rw [erwp_opTableN_eq_erwpK 0]
  refine erwpK_iterateCI (ℍ := ℍ) (V := fun _ _ => True) (fun _ => trivial)
    (fun _ _ _ _ _ => trivial) (Φ := fun _ => Φ) (Inv := fun _ => True) (fun _ _ => hΦ)
    (fun _ _ _ => rfl) (fun _ _ _ _ => trivial)
    (fl := fun _ => 0) (T := fun _ => liftTabK T) (fun _ => hTD.liftK.downI)
    (fun _ _ _ _ _ _ _ _ h => h) (fun _ => (liftTabK_ctxClosed hK).ctxClosedI)
    (fun _ => (liftTabK_ctxClosed hKi).ctxClosedI) (QL := fun _ => QL) (QR := fun _ => QR)
    (fun _ => hQL) (I := fun _ => I) (fun _ => hIle)
    (fun _ => ⟨liftEntK en, liftTabK_of_some htick, hab, hq, hta,
      fun _ k ls w ρ hB => htb k ls w ρ hB, fun _ _ _ _ _ _ h => h⟩)
    N ?_ ?_ (fun _ => hQLR) n hnN () trivial s ls ρ hI
  · intro y _ k hk s' ls' ρ' hI'
    have h := hturn k hk s' ls' ρ' hI'
    rw [erwp_opTableN_eq_erwpK 0] at h
    exact h
  · intro y _ k hk s' ls' ρ' hI'
    have h := hclose k hk s' ls' ρ' hI'
    rw [erwp_opTableN_eq_erwpK 0] at h
    exact h

end BoCa.Fig16.LogRel.Core.Chain.SI

end
