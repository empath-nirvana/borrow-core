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

/-- **E14 at an invariant read at the index, at `erwpK`** (`erwp_iterateCI`): the invariant is read
at a world and an index; the turns and the close paths are owed up to the index `N`. -/
theorem erwpK_iterateCI {V : ι → ι → Prop} (hV : ∀ y, V y y)
    (hVt : ∀ x y z, V x y → V y z → V x z) {Φ : ι → LocFam} (hΦ : ∀ x, (Φ x).Down)
    (hΦV : ∀ x y, V x y → Φ y = Φ x) {fl : ι → Life} {T : ι → OpTabK ι}
    (hTD : ∀ x, (T x).Down)
    (hTV : ∀ x y, V x y → (opTableK (fl y) (T y)).Le (opTableK (fl x) (T x)))
    {f : Val} (hK : ∀ x, (T x).CtxClosed (iterK f)) (hKi : ∀ x, (T x).CtxClosed inrK)
    {QL QR : ι → PostN} (hQL : ∀ y, (QL y).Down) {I : ι → Nat → Val → WProp}
    (hIle : ∀ y k k' s ρ, k' ≤ k → I y k s ρ → I y k' s ρ)
    (htick : ∀ x, ∃ en, T x divEff 0 = some en ∧ en.abort = false ∧ en.q = .lin ∧
      (∀ k ls, en.PA k ls Val.unit PMap.empty) ∧
      (∀ y k ls w (ρ : WRes), en.PB y k ls w ρ → (w = nextV ∨ w = closeV) ∧ ρ = PMap.empty) ∧
      ∀ fl' y k s ρ, en.wk fl' y ρ → I x k s ρ → I y k s ρ)
    (N : Nat)
    (hturn : ∀ y k, k ≤ N → ∀ s ls ρ, I y k s ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) (fun z => turnPostNI (I z) (QL z)) y k
        ls (.app (.app (.val f) (.val s)) (.val nextV)) ρ)
    (hclose : ∀ y k, k ≤ N → ∀ s ls ρ, I y k s ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) QR y k ls (obsCN f s) ρ)
    (hQLR : ∀ y k ls r ρ, QR y k ls r ρ → QL y k ls (Val.inj₂ r) ρ) :
    ∀ n, n ≤ N → ∀ x s ls ρ, I x n s ρ →
      erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) QL x n ls (iterateE f s) ρ := by
  have hD : ∀ x, (opTableK (fl x) (T x)).Down := fun x => opTableK_down (hTD x)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hnN x s ls ρ hI
  refine erwpK_det (hΦ x) (hD x) hQL (fun μ => step1Only_plug (Head.iterate μ f s) rfl .hole) ?_
  simp only [Kont.plug_hole]
  rw [iterNext_eq]
  refine erwpK_bind_le hVt hΦ hΦV hTV (iterK f) (fun m => by simp [iterK, Kont.HasHnd])
    (fun m => by simp [iterK, Kont.Catches]) hK n ?_ n le_rfl x ls _ ρ
    (hturn x n hnN s ls ρ hI)
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
    have hs'' : I y' k' s' XB := hIle y' k k' s' XB (by omega) (hIk (fl y) y' k s' XB hy' hs')
    rcases hw with rfl | rfl
    · -- *next*: round again
      refine erwpK_pureSteps (hΦ y') (hD y') hQL (BoCa.Fig16.LogRel.Core.turnK_next f s') ?_
      exact ih k' (by omega) (by omega) y' s' ls'' XB hs''
    · -- *close*: the close path, `inr ((f s′).2)`
      refine erwpK_pureSteps (hΦ y') (hD y') hQL (BoCa.Fig16.LogRel.Core.turnK_close f s') ?_
      change erwpK (ℍ := ℍ) V Φ (fun z => opTableK (fl z) (T z)) QL y' k' ls''
        (inrK.plug (obsCN f s')) XB
      refine erwpK_bind hVt hΦ hΦV hTV inrK inrK_plain.1 inrK_plain.2 hKi
        (fun y₁ k₁ ls₁ r ρ₁ hr => ?_) k' y' ls'' _ XB (hclose y' k' (by omega) s' ls'' XB hs'')
      refine erwpK_pureSteps (hΦ y₁) (hD y₁) hQL (BoCa.Fig16.LogRel.Core.inrV_steps r) ?_
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
    (fun _ _ _ _ _ => trivial) (Φ := fun _ => Φ) (fun _ => hΦ) (fun _ _ _ => rfl)
    (fl := fun _ => 0) (T := fun _ => liftTabK T) (fun _ => hTD.liftK)
    (fun _ _ _ _ _ _ _ _ h => h) (fun _ => liftTabK_ctxClosed hK)
    (fun _ => liftTabK_ctxClosed hKi) (QL := fun _ => QL) (QR := fun _ => QR)
    (fun _ => hQL) (I := fun _ => I) (fun _ => hIle)
    (fun _ => ⟨liftEntK en, liftTabK_of_some htick, hab, hq, hta,
      fun _ k ls w ρ hB => htb k ls w ρ hB, fun _ _ _ _ _ _ h => h⟩)
    N ?_ ?_ (fun _ => hQLR) n hnN () s ls ρ hI
  · intro y k hk s' ls' ρ' hI'
    have h := hturn k hk s' ls' ρ' hI'
    rw [erwp_opTableN_eq_erwpK 0] at h
    exact h
  · intro y k hk s' ls' ρ' hI'
    have h := hclose k hk s' ls' ρ' hI'
    rw [erwp_opTableN_eq_erwpK 0] at h
    exact h

end BoCa.Fig16.LogRel.Core.Chain.SI

end
