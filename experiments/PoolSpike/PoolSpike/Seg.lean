import PoolSpike.Inv

/-!
# Pool spike: a segment keeps the invariant for every other branch

`seg`: the head branch runs at `twp` with the other branches, parked ones included, as its frame,
to a final term. At every post-configuration `EndT` admits there is a world extending the start at
which `CInv` and `PoolEsc` hold with the head's end resource and records and the others re-read,
and each other branch keeps the records of the list it is relevant to (`KeepRel`).

* `CInv` is `cactusT_step`'s argument without the points.
* `PoolEsc`, the others against the head's end (`stepKeepsFdEsc`, R1); the head's end records
  against the others (`EndT`'s frame clause `MaskDiff` where the run opened or ended a record, and
  the start's `PoolEsc` re-read where it did not); the others among themselves (`fdEsc_rr`).
* **`KeepRel`**: a record of the list relevant to another branch is in the lineage of a record
  proper (`TIT`'s closure). That record proper is not the head's: the branch would hold part of
  the head's lend (`relFT_not_fdEsc` against `PoolEsc`). So it is a record of the frame, re-read
  at the end (`EndT`'s `RecsRR`), its lineage with it (`LinPathT.rr_fwd`), and the end list holds
  the re-read record (`TIT`'s closure at the end).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.Pool
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap)

theorem noneAt_compAll {K : WCactus} {P : BoCa.Loc → Prop} {ρs : List (TRes K)} {W : TRes K}
    (h : CompAllT ρs W) (hv : ResUT.Valid W) (hp : ∀ ρ ∈ ρs, NoneAt P ρ) : NoneAt P W := by
  induction h with
  | nil => exact noneAt_empty P
  | cons hr hc ih =>
      have hv' := ResUT.Valid.split hc hv
      exact NoneAt.compS hc hv'.1 hv'.2 (hp _ List.mem_cons_self)
        (ih hv'.2 fun ρ hρ => hp ρ (List.mem_cons_of_mem _ hρ))

theorem forall₂_and_mem_right {α β : Type} {R : α → β → Prop} {P : β → Prop} :
    ∀ {xs : List α} {ys : List β}, List.Forall₂ R xs ys → (∀ y ∈ ys, P y) →
      List.Forall₂ (fun x y => R x y ∧ P y) xs ys
  | _, _, .nil, _ => .nil
  | _, _, .cons h t, hP => .cons ⟨h, hP _ List.mem_cons_self⟩
      (forall₂_and_mem_right t fun x hx => hP x (List.mem_cons_of_mem _ hx))

/-- The relation a segment leaves between another branch at its start and at its end. -/
def SegRel {w w' : TWd} (ls : List (SRecT w.K)) (ls' : List (SRecT w'.K)) (a : TBranch w.K)
    (b : TBranch w'.K) : Prop :=
  w.Ext w' a.1 ∧ RRw (w := w) (w' := w') a.1 b.1 ∧ RecsRR w'.Θ a.2 b.2 ∧ KeepRel w'.Θ ls ls' a.1

/-- **A segment keeps the invariant for every other branch.** -/
theorem seg {F : TFrame} {Qp : TPost} {n : Nat} {w : TWd} {e : Expr} {ρ : TRes w.K}
    {O : List (FrameRecT w.K)} {rest : List (TBranch w.K)} {W : TRes w.K}
    {ps : List (FrameRecT w.K)} {ls : List (SRecT w.K)} {μ : Heap}
    (h : twp (ℍ := ℍ) F Qp n w ls O e ρ) (hI : CInv w ((ρ, O) :: rest) W ps ls μ)
    (hP : PoolEsc ((ρ, O) :: rest)) (hF : ∀ ρf, F w ρf) (hfd : FinDom μ)
    {j : Nat} {μ' : Heap} {e' : Expr} (hj : j < n) (hrun : StepsN (ℍ := ℍ) j μ e μ' e')
    (hfin : Final (ℍ := ℍ) μ' e') :
    ∃ (w' : TWd) (ρ' W' : TRes w'.K) (O' ps' : List (FrameRecT w'.K))
      (ls' : List (SRecT w'.K)) (rest' : List (TBranch w'.K)), w.K.Ext w'.K ∧
      List.Forall₂ (SegRel ls ls') rest rest' ∧ CInv w' ((ρ', O') :: rest') W' ps' ls' μ' ∧
      PoolEsc ((ρ', O') :: rest') ∧ Qp (n - j) w' ls' O' e' ρ' := by
  obtain ⟨hC, hps, hA, hR, hI'⟩ := hI
  obtain ⟨hhd, htl⟩ := List.pairwise_cons.mp hP
  simp only [List.map_cons] at hC hA
  cases hC with
  | cons hr hc =>
  rename_i ρf
  have hS : SplitT ps O (rest.map Prod.snd).flatten := by
    refine ⟨fun p => by simpa using hps p, fun p hp q hq => ?_⟩
    obtain ⟨O₂, hO₂, hq₂⟩ := List.mem_flatten.mp hq
    exact (List.pairwise_cons.mp hA).1 O₂ hO₂ p hp q hq₂
  have hc' : ResUT.CompS ρf ρ W := ResUT.CompS.comm hc
  have hvW : ResUT.Valid W := hI'.valid
  have hvf : ResUT.Valid ρf := covf_valid hc' hI'
  have hcov : CovR (sem w.Θ) w.K ρ := cov_of_comp hc' hI'
  have hvpart : ∀ a ∈ rest, ResUT.Valid a.1 := fun a ha => by
    obtain ⟨y, hy⟩ := compAllT_part hr (List.mem_map_of_mem ha)
    exact (ResUT.Valid.split hy hvf).1
  have hvesc : ∀ p ∈ ps, ResUT.Valid p.R := TWNT.esc_valid hR.1
  obtain ⟨w', ρf', ρ', fρ', psF', ps', O', ls', g₀, g₁, g₂, g₃, g₄, g₅, g₆, g₇, g₈, g₉, g₁₀,
      g₁₁⟩ :=
    h w ρ ρf W ls O ps _ μ (TWd.Ext.refl _ _) (RR.refl hcov) (SRecsRR.refl hR.cov_ls)
      (RecsRR.refl fun r hr' => hR.cov_ps r (hS.left r hr')) (hF ρf)
      (hash_of_inv hc' hI') hc' hS hR hI' hfd j μ' e' hj hrun hfin
  -- the others re-read, records with them (`cactusT_step`)
  obtain ⟨rs', h₁, h₂⟩ := CompAllT.reread hr g₀ (covf_of_comp hc' hI') g₁
  obtain ⟨Os', rfl, hOs⟩ := forall₂_flatten g₂
  have hrs := forall₂_map_left.mp h₁
  have hOs' := forall₂_map_left.mp hOs
  have hz := forall₂_zip (R := fun (a : TBranch w.K) (b : TBranch w'.K) =>
      w.Ext w' a.1 ∧ RRw (w := w) (w' := w') a.1 b.1 ∧ RecsRR w'.Θ a.2 b.2)
    (fun a b c hb hc' => ⟨hb.1, hb.2, hc'⟩) hrs hOs'
  have hlen : rs'.length = Os'.length := by
    rw [← h₁.length_eq, ← hOs.length_eq]; simp
  have e₁ : (rs'.zip Os').map Prod.fst = rs' := List.map_fst_zip (le_of_eq hlen)
  have e₂ : (rs'.zip Os').map Prod.snd = Os' := List.map_snd_zip (le_of_eq hlen.symm)
  obtain ⟨-, hAtl⟩ := List.pairwise_cons.mp hA
  set rest' := rs'.zip Os' with hrest'
  have hT' := g₆.1
  have hvf' : ResUT.Valid ρf' := covf_valid g₄ g₇
  have hmem' : ∀ b' ∈ rest', ∀ p' ∈ b'.2, p' ∈ ps' := by
    intro b' hb' p' hp'
    refine g₅.right p' (List.mem_flatten.mpr ⟨b'.2, ?_, hp'⟩)
    rw [← e₂]; exact List.mem_map_of_mem hb'
  -- the head's end records against the others
  have hmask : NoneAt (recMask O') ρf' := by
    intro τ hτ x hx
    by_cases hx₀ : recMask O x
    · have h₀ : NoneAt (recMask O) ρf :=
        noneAt_compAll hr hvf fun ρ₂ hρ₂ => by
          obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hρ₂
          exact noneAt_recMask (fun q hq => hvesc q (hS.left q hq)) fun q hq => (hhd a ha).1 q hq
      exact (h₀.rr g₀.1 hvf g₁) τ hτ x hx₀
    · exact g₁₀ τ hτ x (Or.inr ⟨hx, hx₀⟩)
  -- `KeepRel` for each other branch
  have hkeep : ∀ a ∈ rest, KeepRel w'.Θ ls ls' a.1 := by
    intro a ha r₁ hr₁ hrel
    obtain ⟨p₁, hp₁, hd⟩ := (hR.1.inv.2.2.2.2.2.2.1 r₁).mp hr₁
    rcases (hS.1 p₁).mp hp₁ with hp₁O | hp₁F
    · exact (relFT_not_fdEsc hd hrel (hvpart a ha) (hvesc p₁ hp₁) ((hhd a ha).1 p₁ hp₁O)).elim
    · obtain ⟨p₁', hp₁', hpp⟩ := forall₂_mem_left g₂ hp₁F
      obtain ⟨path, hpath⟩ := hd
      obtain ⟨r₂, hrr, hpath'⟩ := hpath.rr_fwd hpp
      exact ⟨r₂, (hT'.inv.2.2.2.2.2.2.1 r₂).mpr ⟨p₁', g₅.right p₁' hp₁', path, hpath'⟩, hrr⟩
  refine ⟨w', ρ', fρ', O', ps', ls', rest', g₀.1,
    (forall₂_and_mem hz hkeep).imp fun _ _ h => ⟨h.1.1, h.1.2.1, h.1.2.2, h.2⟩,
    ⟨?_, fun p => ?_, ?_, g₆, g₇⟩, List.pairwise_cons.mpr ⟨fun b' hb' => ⟨?_, ?_⟩, ?_⟩, g₈⟩
  · simp only [List.map_cons, e₁]
    exact .cons h₂ (ResUT.CompS.comm g₄)
  · simp only [List.map_cons, e₂, List.flatten_cons, List.mem_append]
    exact g₅.1 p
  · simp only [List.map_cons, e₂]
    refine List.pairwise_cons.mpr ⟨fun O₂ hO₂ p hp q hq => ?_, (Apart.rr hOs hAtl)⟩
    exact g₅.2 p hp q (List.mem_flatten.mpr ⟨O₂, hO₂, hq⟩)
  · -- the head's end records, against `b'`
    intro p' hp'
    have hb'm : b'.1 ∈ rs' := by rw [← e₁]; exact List.mem_map_of_mem hb'
    obtain ⟨y, hy⟩ := compAllT_part h₂ hb'm
    exact fdEsc_of_noneAt hT' hp' (g₅.left p' hp') (hmask.of_compS_left hy hvf')
  · -- `b'`'s records, against the head's end: R1
    intro p' hp'
    obtain ⟨b, hb, hbb⟩ := forall₂_mem_right hz hb'
    obtain ⟨p, hp, hpp⟩ := forall₂_mem_right hbb.2.2 hp'
    have hpF : p ∈ (rest.map Prod.snd).flatten :=
      List.mem_flatten.mpr ⟨b.2, List.mem_map_of_mem hb, hp⟩
    have hp'F : p' ∈ Os'.flatten := by
      refine List.mem_flatten.mpr ⟨b'.2, ?_, hp'⟩
      rw [← e₂]; exact List.mem_map_of_mem hb'
    exact stepKeepsFdEsc (ℍ := ℍ) w F Qp n ls O ps _ e ρ ρf W μ p h (hF ρf)
      (hash_of_inv hc' hI') hc' hS hR hI' hfd hpF ((hhd b hb).2 p hp) j μ' e' hj hrun hfin w' ρf'
      ρ' fρ' _ ps' O' ls' g₀ g₁ g₂ g₃ g₄ g₅ g₆ g₇ g₈ g₉ g₁₀ p' hp'F hpp
  · -- the others among themselves, re-read
    have hz₁ := forall₂_and_mem_right (forall₂_and_mem hz fun a ha =>
      (⟨hvpart a ha, fun p hp => hvesc p ((hps p).mpr (by
        simp only [List.map_cons, List.flatten_cons, List.mem_append, List.mem_flatten,
          List.mem_map]
        exact Or.inr ⟨a.2, ⟨a, ha, rfl⟩, hp⟩))⟩ :
        ResUT.Valid a.1 ∧ ∀ p ∈ a.2, ResUT.Valid p.R)) hmem'
    refine pairwise_forall₂ (fun a b a' b' ha hb hab => ?_) hz₁ htl
    obtain ⟨⟨⟨-, hra, hOa⟩, hva, hvea⟩, hma⟩ := ha
    obtain ⟨⟨⟨-, hrb, hOb⟩, hvb, hveb⟩, hmb⟩ := hb
    refine ⟨fun p' hp' => ?_, fun p' hp' => ?_⟩
    · obtain ⟨p, hp, hpp⟩ := forall₂_mem_right hOa hp'
      exact fdEsc_rr g₀.1 hT' hpp (hma p' hp') (hvea p hp) hvb hrb (hab.1 p hp)
    · obtain ⟨p, hp, hpp⟩ := forall₂_mem_right hOb hp'
      exact fdEsc_rr g₀.1 hT' hpp (hmb p' hp') (hveb p hp) hva hra (hab.2 p hp)

end BoCa.Fig16.Tree.Wp.Pool

end
