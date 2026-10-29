import NestedFold.Array

/-!
# NestedFold — the owned traversal's spec, by induction on `P`

`trav_spec` is `Core/FoldOwn.lean`'s `travO_spec` at the class `P`, one case per former, with
an environment of handles: the call of binder `b` on a value `w` of `b`'s closed type is
`s (tag b w)`, and `IHL s n K r` says every such call meets its spec (`HS`) at every measure
below `(n, K, r)`, lexicographically (`Lt3`): `n` bounds the value's cells (`dsize`), `K` its
size, and `r` the binder's rank, the size of its body. The measure drops at every call:

- at a variable, after `⊗`/`⊕`: the value is smaller (`K`), since a body's head is not a
  variable (`Hd`);
- after `Ref` or an array slot: the content has fewer cells (`n`, `dsize_tail_lt`);
- at an inner `μ`, at the same value: the inner binder's body is smaller (`r`).

`hs_all` is strong induction on `n`, then `K`, then `r`: `hOSpec_all` with a third level and
one handle per binder. `fold_spec` is the fold of `μB₀` for every body in the class, at the
binders `reach B₀`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core.NestedFold
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Kont)
open BoCa.Lifetime (LSub)
open Classical

section
variable (ks : List Stack) (G : Algs) (δ : LSub)

/-- **The call of binder `B :: Bs`** on a value of its closed type with at most `n` cells and
size at most `K`. -/
def HS (s : Val) (B : VTy) (Bs : Stack) (n K : Nat) : Prop :=
  ∀ w χ ls, sizeOf w.1 ≤ K → vP (closedOf B Bs) ls δ w χ → dsize χ ≤ n →
    wpTS ls (.app (.val s) (.val (tagV (ks.idxOf (B :: Bs)) w)))
      (fun ls' => vP (G.Res (B :: Bs)) ls' δ) χ

/-- The lexicographic order on `(n, K, r)`. -/
def Lt3 (n' K' r' n K r : Nat) : Prop := n' < n ∨ (n' = n ∧ (K' < K ∨ (K' = K ∧ r' < r)))

/-- **The environment of handles**: every listed binder's call meets its spec below
`(n, K, r)`. -/
def IHL (s : Val) (n K r : Nat) : Prop :=
  ∀ B Bs, (B :: Bs) ∈ ks → Anc ks (B :: Bs) → ∀ n' K', Lt3 n' K' (sizeOf B) n K r →
    HS ks G δ s B Bs n' K'

/-- The algebra of binder `b` with body `B`: `!U(B⟨R⟩ ⊸ F R_b)`. -/
def AlgOK (b : Stack) (B : VTy) : Prop :=
  ∀ ls, vC true (.bang (.lolli (resO G b B) (G.Res b))) ls δ (G.alg b) PMap.empty

/-- The algebra of an array binder: `!U(1 ⊕ (R_a ⊗ S⟨R⟩) ⊸ F R_a)`. -/
def AlgAOK (Bs : Stack) (S : VTy) : Prop :=
  ∀ ls, vC true (.bang (.lolli (.sum .unit (.tensor (G.ResA Bs S) (resO G Bs S))) (G.ResA Bs S)))
    ls δ (G.algA Bs S) PMap.empty

theorem IHL.down {s : Val} {n K r n' : Nat} (h : IHL ks G δ s n K r) (hn : n' < n) (K' r' : Nat) :
    IHL ks G δ s n' K' r' := fun B Bs hm ha n'' K'' hlt =>
  h B Bs hm ha n'' K'' (Or.inl (by rcases hlt with h | ⟨rfl, -⟩ <;> omega))

/-- A closed position: the value itself. -/
theorem leaf_spec {s : Val} (Bs : Stack) {A : VTy} (hA : clB 0 A = true) (w : Val) (χ : WRes)
    (ls : List SRec) (hv : vP (A.subst (env Bs)) ls δ w χ) :
    wpTS ls (.app (.app (.val (trav ks G Bs A)) (.val s)) (.val w))
      (fun ls' => vP (resO G Bs A) ls' δ) χ := by
  refine travOf_app _ s w ls _ χ ?_
  rw [tE_leaf ks G Bs hA]
  have e : ((Expr.var 0).subst 1 (s.shift 1 0)).subst 0 w = .val w := by simp [Expr.subst]
  rw [e, resO_leaf G Bs hA]
  rw [VTy.subst_closed0 ((clB_iff 0 A).mp hA)] at hv
  exact wpTS_val ls w _ χ hv

attribute [local simp] Expr.subst Val.val_shift Expr.shift_shift Expr.shift_zero

/-- **The generic owned traversal**, by induction on the position `A ∈ P`. -/
theorem trav_spec {s : Val} (hs : closedAt 0 s.1 = true) :
    ∀ (A : VTy) (Bs : Stack) (n K r : Nat), IHL ks G δ s n K r → P Bs.length A →
      sizeOf A ≤ r → Anc ks Bs → (∀ c ∈ rIn Bs A, c ∈ ks) → (∀ S ∈ aIn A, AlgAOK G δ Bs S) →
      ∀ w χ ls, sizeOf w.1 ≤ K → (Hd A ∨ sizeOf w.1 < K) →
        vP (A.subst (env Bs)) ls δ w χ → dsize χ ≤ n →
        wpTS ls (.app (.app (.val (trav ks G Bs A)) (.val s)) (.val w))
          (fun ls' => vP (resO G Bs A) ls' δ) χ
  | .tvar i, Bs, n, K, r, hI, hP, _, hA, _, _, w, χ, ls, _, hhd, hv, hn => by
      have hi : i < Bs.length := hP
      have hlt : sizeOf w.1 < K := by
        rcases hhd with h | h
        · rcases h with h | h
          · exact absurd h (Nat.not_lt_zero _)
          · exact h.elim
        · exact h
      have e := List.drop_eq_getElem_cons hi
      set B' := Bs[i]
      set Bs' := Bs.drop (i + 1)
      have hm : (B' :: Bs') ∈ ks := e ▸ hA i hi
      have ha : Anc ks (B' :: Bs') := e ▸ anc_drop hA i
      have hH := hI B' Bs' hm ha n (sizeOf w.1) (Or.inr ⟨rfl, Or.inl hlt⟩)
      refine travOf_app _ s w ls _ χ ?_
      simp only [tE]
      rw [callE_subst ks _ hs w, e]
      have hv' : vP (closedOf B' Bs') ls δ w χ := by
        rw [← env_drop Bs i B' Bs' e]; exact hv
      simp only [resO, e]
      exact hH w χ ls le_rfl hv' hn
  | .tensor A₁ A₂, Bs, n, K, r, hI, hP, hr, hA, hk, ha, w, χ, ls, hK, _, hv, hn => by
      by_cases hcl : clB 0 (.tensor A₁ A₂) = true
      · exact leaf_spec ks G δ Bs hcl w χ ls hv
      obtain ⟨v₁, v₂, hs'⟩ := hv
      obtain ⟨hw, χ₁, χ₂, hc, h₁, h₂⟩ := pure_sep_iff.mp hs'
      subst hw
      have hs₁ : sizeOf v₁.1 < K := by rw [sizeOf_pair] at hK; omega
      have hs₂ : sizeOf v₂.1 < K := by rw [sizeOf_pair] at hK; omega
      have hr₁ : sizeOf A₁ ≤ r := by simp at hr; omega
      have hr₂ : sizeOf A₂ ≤ r := by simp at hr; omega
      have hk₁ : ∀ c ∈ rIn Bs A₁, c ∈ ks := fun c h => hk c (by simp [rIn, h])
      have hk₂ : ∀ c ∈ rIn Bs A₂, c ∈ ks := fun c h => hk c (by simp [rIn, h])
      have ha₁ : ∀ S ∈ aIn A₁, AlgAOK G δ Bs S := fun S h => ha S (by simp [aIn, h])
      have ha₂ : ∀ S ∈ aIn A₂, AlgAOK G δ Bs S := fun S h => ha S (by simp [aIn, h])
      have ht₁ := trav_closed ks G Bs A₁
      have ht₂ := trav_closed ks G Bs A₂
      refine travOf_app _ s _ ls _ χ ?_
      simp only [tE, if_neg hcl]
      rw [tensor_subst _ _ s v₁ v₂ ht₁ ht₂ hs]
      refine wpTS_tensor ls v₁ v₂ _ _ χ ?_
      rw [tensor_body _ _ s v₁ v₂ ht₁ ht₂ hs]
      simp only [resO, if_neg hcl]
      refine wpTS_bind_frame _ _ ls (fun ls' r => vP (resO G Bs A₁) ls' δ r)
        (fun ls' ρ => vP (A₂.subst (env Bs)) ls' δ v₂ ρ ∧ dsize ρ ≤ n)
        _ (fun ls' hls ρ hρ => ⟨vP_same hls hρ.1, hρ.2⟩) ?_ χ
        ⟨χ₁, χ₂, hc, trav_spec hs A₁ Bs n K r hI hP.1 hr₁ hA hk₁ ha₁ v₁ χ₁ ls (le_of_lt hs₁)
          (Or.inr hs₁) h₁ (le_trans (dsize_le_left hc) hn), h₂, le_trans (dsize_le_right hc) hn⟩
      rintro ls' hls r₁ σ ⟨σ₁, σ₂, hcσ, hr₁', hv₂, hn₂⟩
      simp only [Kont.plug]
      refine wpTS_lolli _ _ r₁ _ σ ?_
      rw [tensor_body₂ _ s v₂ r₁ ht₂ hs]
      refine wpTS_bind_frame _ _ ls' (fun ls'' r => vP (resO G Bs A₂) ls'' δ r)
        (fun ls'' => vP (resO G Bs A₁) ls'' δ r₁)
        _ (fun ls'' hls' ρ hρ => vP_same hls' hρ) ?_ σ
        ⟨σ₂, σ₁, ResU.CompS.comm hcσ, trav_spec hs A₂ Bs n K r hI hP.2 hr₂ hA hk₂ ha₂ v₂ σ₂ ls'
          (le_of_lt hs₂) (Or.inr hs₂) hv₂ hn₂, hr₁'⟩
      rintro ls'' - r₂ τ ⟨τ₁, τ₂, hcτ, hr₂', hr₁''⟩
      simp only [Kont.plug]
      refine wpTS_lolli _ _ r₂ _ τ ?_
      rw [tensor_body₃]
      exact wpTS_val ls'' _ _ τ
        ⟨r₁, r₂, pure_sep_iff.mpr ⟨rfl, τ₂, τ₁, ResU.CompS.comm hcτ, hr₁'', hr₂'⟩⟩
  | .sum A₁ A₂, Bs, n, K, r, hI, hP, hr, hA, hk, ha, w, χ, ls, hK, _, hv, hn => by
      by_cases hcl : clB 0 (.sum A₁ A₂) = true
      · exact leaf_spec ks G δ Bs hcl w χ ls hv
      have hr₁ : sizeOf A₁ ≤ r := by simp at hr; omega
      have hr₂ : sizeOf A₂ ≤ r := by simp at hr; omega
      have hk₁ : ∀ c ∈ rIn Bs A₁, c ∈ ks := fun c h => hk c (by simp [rIn, h])
      have hk₂ : ∀ c ∈ rIn Bs A₂, c ∈ ks := fun c h => hk c (by simp [rIn, h])
      have ha₁ : ∀ S ∈ aIn A₁, AlgAOK G δ Bs S := fun S h => ha S (by simp [aIn, h])
      have ha₂ : ∀ S ∈ aIn A₂, AlgAOK G δ Bs S := fun S h => ha S (by simp [aIn, h])
      have ht₁ := trav_closed ks G Bs A₁
      have ht₂ := trav_closed ks G Bs A₂
      refine travOf_app _ s _ ls _ χ ?_
      simp only [tE, if_neg hcl]
      rw [sum_subst _ _ s w ht₁ ht₂ hs]
      simp only [resO, if_neg hcl]
      rcases hv with ⟨v, hs'⟩ | ⟨v, hs'⟩
      · obtain ⟨hw, hv⟩ := pure_sep_iff.mp hs'
        subst hw
        have hsz : sizeOf v.1 < K := by
          have : sizeOf (Val.inj₁ v).1 = 1 + sizeOf v.1 := rfl
          omega
        refine wpTS_sum₁ ls v _ _ _ χ ?_
        rw [sum_branch _ s v ht₁ hs Expr.inj₁ (fun _ _ _ => rfl)]
        refine wpTS_bind _ _ ls _ χ ?_
        refine wpTS_mono (fun ls' r ρ hr => ?_) χ
          (trav_spec hs A₁ Bs n K r hI hP.1 hr₁ hA hk₁ ha₁ v χ ls (le_of_lt hsz) (Or.inr hsz) hv hn)
        simp only [Kont.plug]
        refine wpTS_lolli _ _ r _ ρ ?_
        exact wpTS_val ls' (Val.inj₁ r) _ ρ (Or.inl ⟨r, pure_sep_iff.mpr ⟨rfl, hr⟩⟩)
      · obtain ⟨hw, hv⟩ := pure_sep_iff.mp hs'
        subst hw
        have hsz : sizeOf v.1 < K := by
          have : sizeOf (Val.inj₂ v).1 = 1 + sizeOf v.1 := rfl
          omega
        refine wpTS_sum₂ ls v _ _ _ χ ?_
        rw [sum_branch _ s v ht₂ hs Expr.inj₂ (fun _ _ _ => rfl)]
        refine wpTS_bind _ _ ls _ χ ?_
        refine wpTS_mono (fun ls' r ρ hr => ?_) χ
          (trav_spec hs A₂ Bs n K r hI hP.2 hr₂ hA hk₂ ha₂ v χ ls (le_of_lt hsz) (Or.inr hsz) hv hn)
        simp only [Kont.plug]
        refine wpTS_lolli _ _ r _ ρ ?_
        exact wpTS_val ls' (Val.inj₂ r) _ ρ (Or.inr ⟨r, pure_sep_iff.mpr ⟨rfl, hr⟩⟩)
  | .ref S, Bs, n, K, r, hI, hP, hr, hA, hk, ha, w, χ, ls, _, _, hv, hn => by
      by_cases hcl : clB 0 (.ref S) = true
      · exact leaf_spec ks G δ Bs hcl w χ ls hv
      have hcl' : ¬ clB 0 S = true := hcl
      have hrS : sizeOf S ≤ r := by simp at hr; omega
      have htS := trav_closed ks G Bs S
      obtain ⟨ℓ, v', hs'⟩ := hv
      obtain ⟨rfl, ρa, ρb, hc, hown, hM⟩ := pure_sep_iff.mp hs'
      have hlt : dsize ρb < n := by
        rw [hown] at hc
        exact lt_of_lt_of_le (dsize_tail_lt hc ⟨PMap.empty, ResU.comp_empty_right _⟩) hn
      refine travOf_app _ s _ ls _ χ ?_
      simp only [tE, if_neg hcl']
      rw [ref_subst _ s _ htS hs]
      refine wpTS_bind _ _ ls _ χ ?_
      refine wpTS_free ls ℓ v' _ χ ⟨ρa, ρb, hc, hown, ?_⟩
      simp only [Kont.plug]
      refine wpTS_lolli _ _ v' _ ρb ?_
      rw [ref_body _ s v' htS hs]
      simp only [resO, if_neg hcl']
      exact trav_spec hs S Bs (dsize ρb) (sizeOf v'.1 + 1) r (hI.down ks G δ hlt _ _) hP hrS hA
        hk ha v' ρb ls (Nat.le_succ _) (Or.inr (Nat.lt_succ_self _)) hM le_rfl
  | .fam (.ref S), Bs, n, K, r, hI, hP, hr, hA, hk, ha, w, χ, ls, _, _, hv, hn => by
      by_cases hcl : clB 0 S = true
      · exact leaf_spec ks G δ Bs (A := .fam (.ref S)) hcl w χ ls hv
      have hrS : sizeOf S ≤ r := by simp at hr; omega
      have hk' : ∀ c ∈ rIn Bs S, c ∈ ks := hk
      have ha' : ∀ S' ∈ aIn S, AlgAOK G δ Bs S' := fun S' h => ha S' (by simp [aIn, hcl, h])
      have hgA : AlgAOK G δ Bs S := ha S (by simp [aIn, hcl])
      simp only [trav, tE, if_neg hcl, resO]
      exact arr_spec (trav_closed ks G Bs S) (G.algA_closed Bs S) hs
        (fun v ρ ls' hv' hlt => trav_spec hs S Bs (dsize ρ) (sizeOf v.1 + 1) r
          (hI.down ks G δ (lt_of_lt_of_le hlt le_rfl) _ _) hP hrS hA hk' ha' v ρ ls' (Nat.le_succ _)
          (Or.inr (Nat.lt_succ_self _)) hv' le_rfl)
        hgA w χ ls hv hn
  | .mu B, Bs, n, K, r, hI, _, hr, hA, hk, _, w, χ, ls, hK, _, hv, hn => by
      by_cases hcl : clB 0 (.mu B) = true
      · exact leaf_spec ks G δ Bs hcl w χ ls hv
      have hm : (B :: Bs) ∈ ks := hk _ (by simp [rIn, hcl])
      have hrB : sizeOf B < r := by simp at hr; omega
      have hH := hI B Bs hm (anc_cons hm hA) n K (Or.inr ⟨rfl, Or.inr ⟨rfl, hrB⟩⟩)
      refine travOf_app _ s w ls _ χ ?_
      simp only [tE, if_neg hcl]
      rw [callE_subst ks _ hs w]
      simp only [resO, if_neg hcl]
      exact hH w χ ls hK hv hn
  | .unit, Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .zero, Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .thunk _, Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .imm _ _, Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .mut _ _, Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .box _ _, Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .bang _, Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .unk, Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .int _, Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .opq _, Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .fam .unit, Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.tensor _ _), Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .fam .zero, Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.sum _ _), Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.thunk _), Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.imm _ _), Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.mut _ _), Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.box _ _), Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.bang _), Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .fam .unk, Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.tvar _), Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.mu _), Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.int _), Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.fam _), Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _
  | .fam (.opq _), Bs, _, _, _, _, hP, _, _, _, _, w, χ, ls, _, _, hv, _ =>
      leaf_spec ks G δ Bs (by exact (clB_iff 0 _).mpr hP) w χ ls hv

/-- One unrolling of binder `B :: Bs`: the dispatch, the traversal of the body, the algebra. -/
theorem hs_step (hok : KeysOK ks) (halg : ∀ B Bs, (B :: Bs) ∈ ks → AlgOK G δ (B :: Bs) B)
    (harr : ∀ B Bs, (B :: Bs) ∈ ks → ∀ S ∈ aIn B, AlgAOK G δ (B :: Bs) S)
    {B : VTy} {Bs : Stack} {n K : Nat} (hm : (B :: Bs) ∈ ks) (ha : Anc ks (B :: Bs))
    (hI : IHL ks G δ (selfD ks G) n K (sizeOf B)) : HS ks G δ (selfD ks G) B Bs n K := by
  intro w χ ls hK hv hn
  obtain ⟨hP, hH, hk⟩ := hok B Bs hm
  refine selfD_run ks G _ (B :: Bs) (List.getElem?_idxOf hm) w ls _ χ ?_
  refine wpTS_bind _ _ ls _ χ ?_
  have hv' : vP (B.subst (env (B :: Bs))) ls δ w χ := by
    rw [← inst_closedOf]; exact (vC_unfold hv).2.2
  refine wpTS_mono (fun ls' r ρ hr => ?_) χ
    (trav_spec ks G δ (selfD_closed ks G) B (B :: Bs) n K (sizeOf B) hI hP le_rfl ha hk
      (harr B Bs hm) w χ ls hK (Or.inl hH) hv' hn)
  simp only [Kont.plug]
  refine wpTS_lolli _ _ r _ ρ ?_
  rw [alg_subst _ r (G.alg_closed _)]
  exact alg_app (halg B Bs hm) hr

/-- **Every binder's call meets its spec**, at every measure: strong induction on the cells,
then the value's size, then the binder's rank. -/
theorem hs_all (hok : KeysOK ks) (halg : ∀ B Bs, (B :: Bs) ∈ ks → AlgOK G δ (B :: Bs) B)
    (harr : ∀ B Bs, (B :: Bs) ∈ ks → ∀ S ∈ aIn B, AlgAOK G δ (B :: Bs) S) :
    ∀ n K B Bs, (B :: Bs) ∈ ks → Anc ks (B :: Bs) → HS ks G δ (selfD ks G) B Bs n K := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
    intro K
    induction K using Nat.strong_induction_on with
    | _ K ihK =>
      suffices H : ∀ r B Bs, sizeOf B = r → (B :: Bs) ∈ ks → Anc ks (B :: Bs) →
          HS ks G δ (selfD ks G) B Bs n K from fun B Bs => H _ B Bs rfl
      intro r
      induction r using Nat.strong_induction_on with
      | _ r ihr =>
        intro B Bs hr hm ha
        refine hs_step ks G δ hok halg harr hm ha ?_
        intro B' Bs' hm' ha' n' K' hlt
        rcases hlt with h | ⟨rfl, h | ⟨rfl, h⟩⟩
        · exact ihn n' h K' B' Bs' hm' ha'
        · exact ihK K' h B' Bs' hm' ha'
        · exact ihr (sizeOf B') (hr ▸ h) B' Bs' rfl hm' ha'

end

/-- **The owned fold of `μB₀`**, for every body `B₀` in the class `P`: the handle of the root
binder takes a value of `μB₀` to a value of its result, given each binder's algebra. -/
theorem fold_spec {B₀ : VTy} (hB : PBody B₀) (G : Algs) (δ : LSub)
    (halg : ∀ B Bs, (B :: Bs) ∈ reach B₀ → AlgOK G δ (B :: Bs) B)
    (harr : ∀ B Bs, (B :: Bs) ∈ reach B₀ → ∀ S ∈ aIn B, AlgAOK G δ (B :: Bs) S)
    (w : Val) (χ : WRes) (ls : List SRec) (hv : vP (.mu B₀) ls δ w χ) :
    wpTS ls (.app (.val (hdl (reach B₀) G [B₀])) (.val w)) (fun ls' => vP (G.Res [B₀]) ls' δ) χ := by
  refine hdl_app (reach B₀) G [B₀] w ls _ χ ?_
  rw [← closedOf_root] at hv
  exact hs_all (reach B₀) G δ (reach_ok hB) halg harr (dsize χ) (sizeOf w.1) B₀ [] (root_mem B₀)
    (anc_root B₀) w χ ls le_rfl hv le_rfl

end BoCa.Fig16.LogRel.Core.NestedFold

end
