import Core.Chain.SI.CrossProg
import Core.Chain.SI.CaptureScopeM

/-!
# The test, `mut`: the borrow moved to exactly one child, returned at the join

The program is `CrossProg.mainE`, the specification different: the parent lends `c` `mut` (not
`imm`) around `spawn (λ_. y (); !c); join(c)`. The spawn passes the only borrow to the child
(`PAspawnM`: the `mut` cell itself, at `ℓ`); the parent keeps nothing at `c`; the child holds the
borrow across its `y`, reads through it, and returns it; the scheduler hands it back in the
join's answer (`joinEntM`'s `PBv`), and the lend ends (`cerwp_scopeM`). No record and no frame
condition: a `mut` cell composes with nothing, so holding it is holding it alone. The cancel: the
cancel run returns the borrow the same way.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.Chain.SI.CrossProgM
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.Fig16.LogRel.Core.Chain.SI
open BoCa.Fig16.LogRel.Core.Chain.SI.CrossProg
open BoCa.BoLo (Heap Step1 Steps Head Kont performE raiseE cancelVal opPayload freeE hndE hndVal
  clauseAt capTag ccatchE kappaC)

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

/-- The lend's lifetime. -/
def AM : Life := 0

/-- The lent cell's predicate: any value, an empty witness. -/
def PM : Val → SPropS Loc Val AM := fun _ r => r.1 = PMap.empty

/-- The borrow: `ℓ ↦ mut(A, u, ∅, P̂)`. -/
def mcell (l : Loc) (u : Val) : WRes :=
  ResU.single l (CellU.mutOf AM u PMap.empty (inStratumE AM) PM rfl)

/-- What the child holds and leaves: the borrow of `ℓ`. -/
def HoldM (l : Loc) (ρ : WRes) : Prop := ∃ u, ρ = mcell l u

/-- `load` through any cell: its value, the resource kept. -/
theorem crwpG_load1 {F : WRes → Prop} {Q : PostC} {n : Nat} {ls : List SRec}
    {O : List FrameRec} (l : Loc) {ψ : CellU Loc Val} {ρ ρR : WRes}
    (hc : ResU.CompS (ResU.single l ψ) ρR ρ) (hQ : Q (n - 1) ls O ψ.erase.1 ρ) :
    crwpG (ℍ := ℍ) F Q n ls O (.app (.val (.prim .load)) (.val (Val.loc l))) ρ := by
  refine crwpG_head1 (Head.load (fun _ => some Val.unit) l Val.unit rfl)
    (fun ρf τ ps psF μ _ hf hτ hS hT htg hμ hfin => ?_)
  obtain ⟨χ₁, hχ, heχ⟩ := compS_get_erase hc (ResU.single_get_self l _)
  obtain ⟨χ', hχ', heχ'⟩ := compS_get_erase (ResU.CompS.comm hτ) hχ
  have hlv : μ l = some ψ.erase := by
    rw [lower_get hμ hχ', heχ', heχ]
  refine ⟨⟨_, _, Head.load μ l _ hlv⟩, fun μ₁ e₁ hh => ?_⟩
  obtain ⟨w, hw, rfl, rfl⟩ := head_load_inv hh
  rw [hlv] at hw
  cases hw
  exact ⟨ψ.erase, rfl, ρ, τ, ps, O, ls, ResU.hash_symm hf, hτ, hμ, hS, hT, htg, hQ⟩

/-! ### The child -/

def QleftM (l : Loc) : PostCV := fun _ _ O v ρ => O = [] ∧ v = Val.unit ∧ HoldM l ρ
def QchildM (l : Loc) : PostCV := fun _ _ O _ ρ => O = [] ∧ HoldM l ρ

def PcanM (l : Loc) : Nat → List SRec → Expr → WProp := fun k ls e ρ =>
  ∀ F, cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) (QleftM l) F k ls [] (ccatchE e) ρ

def yEntM (l : Loc) : OpEntC :=
  { q := .cancel, abort := false, PA := fun _ _ v ρ => v = Val.unit ∧ ρ = PMap.empty,
    PB := fun _ _ w ρ => w = Val.unit ∧ ρ = PMap.empty, fin := some (PcanM (ℍ := ℍ) l),
    wc := fun _ _ _ => True, fd := fun _ _ => True,
    PBv := fun _ _ _ w ρ => w = Val.unit ∧ ρ = PMap.empty, oc := fun O => O = [] }

def TCM (l : Loc) : OpTabC := fun m i => if m = 8 ∧ i = 0 then some (yEntM (ℍ := ℍ) l) else none

theorem TCM_some {l : Loc} {m i : UInt32} {en : OpEntC} (h : TCM (ℍ := ℍ) l m i = some en) :
    m = 8 ∧ i = 0 ∧ en = yEntM (ℍ := ℍ) l := by
  unfold TCM at h
  split_ifs at h with h₁
  exact ⟨h₁.1, h₁.2, (Option.some.inj h).symm⟩

theorem QleftM_down (l : Loc) : (QleftM l).Down := fun _ _ _ _ _ h => h
theorem QchildM_down (l : Loc) : (QchildM l).Down := fun _ _ _ _ _ h => h

theorem TCM_down (l : Loc) : (TCM (ℍ := ℍ) l).Down where
  pa := fun _ _ en h _ _ _ _ hA => by obtain ⟨-, -, rfl⟩ := TCM_some h; exact hA
  fin := fun _ _ en P h hP k ls e ρ hk => by
    obtain ⟨-, -, rfl⟩ := TCM_some h
    cases hP
    exact fun F => cerwp_le (opTableC_local _) (opTableC_down opTabC_emptyC_down)
      (QleftM_down l) (Nat.le_succ k) (hk F)

/-- **The child, `mut`**: holds the borrow across `y`, reads through it, returns it; cancelled,
returns it. -/
theorem childM_ok (l : Loc) (u : Val) (F : WRes → Prop) (n : Nat) (ls : List SRec) :
    cerwp (ℍ := ℍ) (opTableC (TCM (ℍ := ℍ) l)) (QchildM l) F n ls []
      (.app (.val (fchild l)) (.val Val.unit)) (mcell l u) := by
  have hL := opTableC_local (TCM (ℍ := ℍ) l)
  have hD := opTableC_down (TCM_down (ℍ := ℍ) l)
  refine cerwp_det hD (QchildM_down l)
    (fun μ => step1Only_plug (Head.beta μ _ Val.unit) rfl .hole) ?_
  have e : Kont.hole.plug (Expr.subst 0 Val.unit (.seq yE (ldL l))) =
      (Kont.seq .hole (ldL l)).plug (performE (.val (opPayload 8 0 Val.unit))) := by
    simp [Expr.subst, Kont.plug, yE, ldL, performE, opPayload, Val.pair, Val.i32, Val.unit,
      Val.loc, Expr.val, Val.prim]
  rw [e]
  refine cerwp_perform (T := TCM (ℍ := ℍ) l) (en := yEntM (ℍ := ℍ) l) (Kont.seq .hole (ldL l))
    (by simp [Kont.HasHnd]) (by simp [TCM]) rfl rfl (compS_empty_left _) ⟨rfl, rfl⟩
    (fun hq => by simp [yEntM] at hq) (fun ls' _ k' hk' w σ₁ σ₂ hB hc => ?_)
    (fun ls' _ _ P hP => ?_)
  · obtain ⟨rfl, rfl⟩ := hB
    obtain rfl := ResU.CompS.functional hc (ResU.comp_empty_right _)
    refine cerwp_det hD (QchildM_down l) (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    rw [cerwp_eq]
    exact crwpG_bind .hole (crwpG_load1 l (ResU.comp_empty_right _)
      (cerwp_unfold_at hL (Nat.sub_le _ 1) (cerwp_val ⟨rfl, u, rfl⟩)))
  · cases hP
    intro F'
    show cerwp (ℍ := ℍ) _ _ _ _ _ _ (ccatchE ((Kont.seq .hole (ldL l)).dead.plug
      (raiseE (.val (cancelVal none))))) _
    refine cerwp_det (opTableC_down opTabC_emptyC_down) (QleftM_down l)
      (fun μ => step1Only_plug (Head.cancel μ (Kont.seq .hole (ldL l)).dead
        (by simp [Kont.dead, Kont.Catches])) rfl .hole) ?_
    exact cerwp_val ⟨rfl, rfl, u, rfl⟩

/-! ### The parent -/

/-- What `spawn` passes: the borrow itself, and a closure that runs as the child from it. -/
def PAspawnM (l : Loc) : Nat → List SRec → Val → WProp := fun k _ f ρ =>
  HoldM l ρ ∧ ∀ k', k' ≤ k → ∀ ls' F, cerwp (ℍ := ℍ) (opTableC (TCM (ℍ := ℍ) l)) (QchildM l) F
    k' ls' [] (.app (.val f) (.val Val.unit)) ρ

def spawnEntM (l : Loc) : OpEntN :=
  { q := .lin, abort := false, PA := PAspawnM (ℍ := ℍ) l,
    PB := fun _ _ w ρ => w = Val.unit ∧ ρ = PMap.empty, fin := none, wc := fun _ _ _ => True }

/-- The parent's table: `spawn`, and the scope's join. -/
def TPM (l : Loc) : OpTabC := fun m i =>
  if m = 7 ∧ i = 0 then some (liftEnt (spawnEntM (ℍ := ℍ) l))
  else if m = 7 ∧ i = 1 then some (joinEntM l AM PM) else none

theorem TPM_some {l : Loc} {m i : UInt32} {en : OpEntC} (h : TPM (ℍ := ℍ) l m i = some en) :
    (m = 7 ∧ i = 0 ∧ en = liftEnt (spawnEntM (ℍ := ℍ) l)) ∨
    (m = 7 ∧ i = 1 ∧ en = joinEntM l AM PM) := by
  unfold TPM at h
  split_ifs at h with h₁ h₂
  · exact .inl ⟨h₁.1, h₁.2, (Option.some.inj h).symm⟩
  · exact .inr ⟨h₂.1, h₂.2, (Option.some.inj h).symm⟩

theorem TPM_down (l : Loc) : (TPM (ℍ := ℍ) l).Down where
  pa := fun _ _ en h k ls v ρ hA => by
    rcases TPM_some h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
    · exact ⟨hA.1, fun k' hk' => hA.2 k' (by omega)⟩
    · exact hA
  fin := fun _ _ en P h hP => by
    rcases TPM_some h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> cases hP

theorem TPM_lin (l : Loc) : ∀ m i en, TPM (ℍ := ℍ) l m i = some en → en.q = .lin := by
  intro m i en h
  rcases TPM_some h with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ <;> rfl

/-- The body's postcondition: `()`, holding nothing, no records. -/
def Q₀M : PostCV := fun _ _ O w ρ => O = [] ∧ w = Val.unit ∧ ρ = PMap.empty

/-- The parent's postcondition: `()`, the cell owned again, no records. -/
def QscM (l : Loc) : PostCV := fun _ _ O w ρ =>
  O = [] ∧ w = Val.unit ∧ ∃ u, ρ = ResU.single l (CellU.ownOf u)

theorem QscM_down (l : Loc) : (QscM l).Down := fun _ _ _ _ _ h => h

/-- **The body, `mut`**: `spawn f` passes the borrow to the child; the body keeps nothing. -/
theorem bodyM_ok (l : Loc) (u : Val) (F : WRes → Prop) (n : Nat) (ls : List SRec) :
    cerwp (ℍ := ℍ) (opTableC (TPM (ℍ := ℍ) l)) Q₀M F n ls [] (spawnE l) (mcell l u) := by
  refine cerwp_perform (T := TPM (ℍ := ℍ) l) (en := liftEnt (spawnEntM (ℍ := ℍ) l)) .hole
    (by simp [Kont.HasHnd]) (by simp [TPM]) rfl trivial (ResU.comp_empty_right _)
    ⟨⟨u, rfl⟩, fun k' _ ls' F' => childM_ok l u F' k' ls'⟩ (fun h => by simp [liftEnt, spawnEntM] at h)
    (fun ls' _ k' _ w σ₁ σ₂ hB hc => ?_) (fun _ _ h => absurd rfl h)
  obtain ⟨rfl, rfl⟩ := hB
  obtain rfl := eq_of_compS_empty_left hc
  exact cerwp_val ⟨rfl, rfl, rfl⟩

/-- **The parent, `mut`**: the `mut` lend scope around the body. -/
theorem parentM_ok (l : Loc) (F : WRes → Prop) (n : Nat) (ls : List SRec) :
    cerwp (ℍ := ℍ) (opTableC (TPM (ℍ := ℍ) l)) (QscM l) F n ls [] (parentE l)
      (ResU.single l (CellU.ownOf Val.unit)) := by
  refine cerwp_scopeM (Q₀ := Q₀M) l Val.unit AM PM (inStratumE AM) rfl 7 1 (TPM_down l) (TPM_lin l)
    (by simp [TPM]) (QscM_down l) (fun _ _ _ _ _ (h : Q₀M _ _ _ _ _) => h.2.1) ?_ n F ls [] (spawnE l)
    (ResU.comp_empty_right _) (ResU.comp_empty_right _) (ResU.valid_single_own l _)
    (fun BM hBM => ?_)
  · intro k k₀ ls₀ ls' O w₀ ρ₀ u χ hχ hu W'' ρout _ hq hW'' hρ
    obtain ⟨rfl, -, rfl⟩ := hq
    have hχe : χ = PMap.empty := hu
    subst hχe
    obtain rfl := eq_of_compS_empty_left hW''
    obtain rfl := eq_of_compS_empty_left hρ
    exact ⟨rfl, rfl, u, rfl⟩
  · obtain rfl := eq_of_compS_empty_left hBM
    exact bodyM_ok l Val.unit F n ls

/-! ### The handlers -/

/-- What a run of the parent under `HP` hands the scheduler. -/
def QPM (l : Loc) (F : WRes → Prop) : PostCV := fun k ls O r ρ =>
  (∃ v : Val, r = Val.inj₂ v ∧ QscM l k ls O v ρ) ∨
  (∃ (ℓf ℓκ : Loc) (f : Val) (ρ₁ ρa ρ₂ : WRes),
    r = Val.inj₁ (Val.inj₁ (Val.pair (Val.loc ℓf) (Val.loc ℓκ))) ∧
    ResU.CompS (ResU.single ℓf (CellU.ownOf f)) ρa ρ₁ ∧ PAspawnM (ℍ := ℍ) l k ls f ρa ∧
    ResU.CompS ρ₁ ρ₂ ρ ∧
    KapStored (ℍ := ℍ) (TPM (ℍ := ℍ) l) (QscM l) HP (liftEnt (spawnEntM (ℍ := ℍ) l)) F k ls O f
      ℓκ ρ₂) ∨
  (∃ ℓκ : Loc, r = Val.inj₁ (Val.inj₂ (Val.loc ℓκ)) ∧
    KapStored (ℍ := ℍ) (TPM (ℍ := ℍ) l) (QscM l) HP (joinEntM l AM PM) F k ls O (Val.loc l) ℓκ ρ)

/-- What a run of the child under `HC` hands the scheduler. -/
def QCM (l : Loc) (F : WRes → Prop) : PostCV := fun k ls O r ρ =>
  (∃ v : Val, r = Val.inj₂ v ∧ QchildM l k ls O v ρ) ∨
  (∃ ℓκ : Loc, r = Val.inj₁ (Val.loc ℓκ) ∧ O = [] ∧
    KapStored (ℍ := ℍ) (TCM (ℍ := ℍ) l) (QchildM l) HC (yEntM (ℍ := ℍ) l) F k ls O Val.unit ℓκ ρ)

theorem QPM_down (l : Loc) (F : WRes → Prop) : (QPM (ℍ := ℍ) l F).Down := by
  intro k ls O r ρ h
  rcases h with h | ⟨ℓf, ℓκ, f, ρ₁, ρa, ρ₂, e, h₁, ⟨hh, hk⟩, h₃, h₄⟩ | ⟨ℓκ, e, h⟩
  · exact .inl h
  · exact .inr (.inl ⟨ℓf, ℓκ, f, ρ₁, ρa, ρ₂, e, h₁, ⟨hh, fun k' hk' => hk k' (by omega)⟩,
      h₃, kapStored_down h₄⟩)
  · exact .inr (.inr ⟨ℓκ, e, kapStored_down h⟩)

theorem QCM_down (l : Loc) (F : WRes → Prop) : (QCM (ℍ := ℍ) l F).Down := by
  intro k ls O r ρ h
  rcases h with h | ⟨ℓκ, e, hO, h⟩
  · exact .inl h
  · exact .inr ⟨ℓκ, e, hO, kapStored_down h⟩

/-- **`spawn`'s clause**: `f` and `κ` stored in fresh cells; the payload, the stored closure and
the stored continuation handed to the scheduler. -/
theorem spawnCl_okM (l : Loc) (F : WRes → Prop) {k : Nat} {ls : List SRec} {O : List FrameRec}
    {f : Val} {ℓc : Loc} {K : Kont} {ρa ρk ρak ρ : WRes}
    (hA : PAspawnM (ℍ := ℍ) l k ls f ρa)
    (hsh : contShareC (liftEnt (spawnEntM (ℍ := ℍ) l)) F k ls O K f
      (cerwpC (ℍ := ℍ) (opTableC (TPM (ℍ := ℍ) l)) (QscM l) k) ρk)
    (hak : ResU.CompS ρa ρk ρak) (hc : ResU.CompS ρak (ResU.single ℓc (CellU.ownOf Val.unit)) ρ) :
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) (QPM (ℍ := ℍ) l F) F (k - 1) ls O
      (.app (.val c₀) (.pair (.val f) (kappaC false ℓc HP K))) ρ := by
  have hD := opTableC_down opTabC_emptyC_down
  have hL := opTableC_local OpTabC.emptyC
  have hQ := QPM_down (ℍ := ℍ) l F
  set κV := kV false ℓc HP K with hκV
  refine cerwp_det hD hQ (fun μ => step1Only_plug (Head.beta μ _ (Val.pair f κV)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.pair f κV)
      (.letpair (.var 0) (.inj₁ (.inj₁ (.pair (allocE (.var 1)) (allocE (.var 0))))))) =
      Kont.hole.plug (.letpair (.val (Val.pair f κV))
        (.inj₁ (.inj₁ (.pair (allocE (.var 1)) (allocE (.var 0)))))) := by
    simp [Expr.subst, Kont.plug, allocE]
  rw [e₁]
  refine cerwp_det hD hQ (fun μ => step1Only_plug (Head.letpair μ f κV _) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 f (Expr.subst 0 (κV.shift 1 0)
      (.inj₁ (.inj₁ (.pair (allocE (.var 1)) (allocE (.var 0))))))) =
      (Kont.inj₁ (Kont.inj₁ (Kont.pairL .hole (allocE κV.1)))).plug
        (.app (.val (.prim .alloc)) (.val f)) := by
    simp only [Expr.subst, allocE, Kont.plug, if_true, Val.val_shift]
    rw [kV_subst]
    simp [Expr.subst]
  rw [e₂]
  refine cerwp_allocX hL _ f (fun ℓf ρ' hc₁ => ?_)
  have e₃ : (Kont.inj₁ (Kont.inj₁ (Kont.pairL .hole (allocE κV.1)))).plug (.val (Val.loc ℓf)) =
      (Kont.inj₁ (Kont.inj₁ (Kont.pairR (Val.loc ℓf) .hole))).plug
        (.app (.val (.prim .alloc)) (.val κV)) := rfl
  rw [e₃]
  refine cerwp_allocX hL _ κV (fun ℓκ ρ'' hc₂ => ?_)
  have e₄ : (Kont.inj₁ (Kont.inj₁ (Kont.pairR (Val.loc ℓf) .hole))).plug (.val (Val.loc ℓκ)) =
      (Val.inj₁ (Val.inj₁ (Val.pair (Val.loc ℓf) (Val.loc ℓκ)))).1 := rfl
  rw [e₄]
  obtain ⟨ρ₁, ρ₂, ρ₃, h₁, h₃, h₂, h₁₂⟩ := rearr5 hak hc hc₁ hc₂
  obtain ⟨hh, hk⟩ := hA
  exact cerwp_val (.inr (.inl ⟨ℓf, ℓκ, f, ρ₁, ρa, ρ₂, rfl, h₁,
    ⟨hh, fun k' hk' => hk k' (by omega)⟩, h₁₂,
    ⟨ℓc, K, ρk, ρ₃, k, by omega, h₃, h₂, hsh⟩⟩))

/-- **The join's clause**: `κ` stored in a fresh cell. -/
theorem joinCl_okM (l : Loc) (F : WRes → Prop) {k : Nat} {ls : List SRec} {O : List FrameRec}
    {v : Val} {ℓc : Loc} {K : Kont} {ρa ρk ρak ρ : WRes}
    (hA : (joinEntM l AM PM).PA k ls v ρa)
    (hsh : contShareC (joinEntM l AM PM) F k ls O K v
      (cerwpC (ℍ := ℍ) (opTableC (TPM (ℍ := ℍ) l)) (QscM l) k) ρk)
    (hak : ResU.CompS ρa ρk ρak) (hc : ResU.CompS ρak (ResU.single ℓc (CellU.ownOf Val.unit)) ρ) :
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) (QPM (ℍ := ℍ) l F) F (k - 1) ls O
      (.app (.val c₁) (.pair (.val v) (kappaC false ℓc HP K))) ρ := by
  have hD := opTableC_down opTabC_emptyC_down
  have hL := opTableC_local OpTabC.emptyC
  have hQ := QPM_down (ℍ := ℍ) l F
  obtain ⟨rfl, rfl⟩ := hA
  set κV := kV false ℓc HP K with hκV
  refine cerwp_det hD hQ
    (fun μ => step1Only_plug (Head.beta μ _ (Val.pair (Val.loc l) κV)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.pair (Val.loc l) κV)
      (.letpair (.var 0) (.inj₁ (.inj₂ (allocE (.var 0)))))) =
      Kont.hole.plug (.letpair (.val (Val.pair (Val.loc l) κV))
        (.inj₁ (.inj₂ (allocE (.var 0))))) := by
    simp [Expr.subst, Kont.plug, allocE]
  rw [e₁]
  refine cerwp_det hD hQ (fun μ => step1Only_plug (Head.letpair μ (Val.loc l) κV _) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 (Val.loc l) (Expr.subst 0 (κV.shift 1 0)
      (.inj₁ (.inj₂ (allocE (.var 0)))))) =
      (Kont.inj₁ (Kont.inj₂ .hole)).plug (.app (.val (.prim .alloc)) (.val κV)) := by
    simp only [Expr.subst, allocE, Kont.plug, if_true, Val.val_shift]
    rw [kV_subst]
    rfl
  rw [e₂]
  refine cerwp_allocX hL _ κV (fun ℓκ ρ' hc₁ => ?_)
  have e₃ : (Kont.inj₁ (Kont.inj₂ .hole)).plug (.val (Val.loc ℓκ)) =
      (Val.inj₁ (Val.inj₂ (Val.loc ℓκ))).1 := rfl
  rw [e₃]
  obtain ⟨ρ₃, h₃, h₂⟩ := rearr4 hak hc hc₁
  exact cerwp_val (.inr (.inr ⟨ℓκ, rfl, ⟨ℓc, K, ρk, ρ₃, k, by omega, h₃, h₂, hsh⟩⟩))

/-- **`y`'s clause**: `κ` stored in a fresh cell. -/
theorem yCl_okM (l : Loc) (F : WRes → Prop) {k : Nat} {ls : List SRec} {O : List FrameRec}
    {v : Val} {ℓc : Loc} {K : Kont} {ρa ρk ρak ρ : WRes} (hO : O = [])
    (hA : (yEntM (ℍ := ℍ) l).PA k ls v ρa)
    (hsh : contShareC (yEntM (ℍ := ℍ) l) F k ls O K v
      (cerwpC (ℍ := ℍ) (opTableC (TCM (ℍ := ℍ) l)) (QchildM l) k) ρk)
    (hak : ResU.CompS ρa ρk ρak) (hc : ResU.CompS ρak (ResU.single ℓc (CellU.ownOf Val.unit)) ρ) :
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) (QCM (ℍ := ℍ) l F) F (k - 1) ls O
      (.app (.val cy) (.pair (.val v) (kappaC true ℓc HC K))) ρ := by
  have hD := opTableC_down opTabC_emptyC_down
  have hL := opTableC_local OpTabC.emptyC
  have hQ := QCM_down (ℍ := ℍ) l F
  obtain ⟨rfl, rfl⟩ := hA
  set κV := kV true ℓc HC K with hκV
  refine cerwp_det hD hQ
    (fun μ => step1Only_plug (Head.beta μ _ (Val.pair Val.unit κV)) rfl .hole) ?_
  have e₁ : Kont.hole.plug (Expr.subst 0 (Val.pair Val.unit κV)
      (.letpair (.var 0) (.inj₁ (allocE (.var 0))))) =
      Kont.hole.plug (.letpair (.val (Val.pair Val.unit κV)) (.inj₁ (allocE (.var 0)))) := by
    simp [Expr.subst, Kont.plug, allocE]
  rw [e₁]
  refine cerwp_det hD hQ (fun μ => step1Only_plug (Head.letpair μ Val.unit κV _) rfl .hole) ?_
  have e₂ : Kont.hole.plug (Expr.subst 0 Val.unit (Expr.subst 0 (κV.shift 1 0)
      (.inj₁ (allocE (.var 0))))) =
      (Kont.inj₁ .hole).plug (.app (.val (.prim .alloc)) (.val κV)) := by
    simp only [Expr.subst, allocE, Kont.plug, if_true, Val.val_shift]
    rw [kV_subst]
    rfl
  rw [e₂]
  refine cerwp_allocX hL _ κV (fun ℓκ ρ' hc₁ => ?_)
  have e₃ : (Kont.inj₁ .hole).plug (.val (Val.loc ℓκ)) = (Val.inj₁ (Val.loc ℓκ)).1 := rfl
  rw [e₃]
  obtain ⟨ρ₃, h₃, h₂⟩ := rearr4 hak hc hc₁
  exact cerwp_val (.inr ⟨ℓκ, rfl, hO, ⟨ℓc, K, ρk, ρ₃, k, by omega, h₃, h₂, hsh⟩⟩)

/-- **A run of the parent under `HP`** (`cerwp_gen`): whatever it stops at, the scheduler gets
the event. -/
theorem genPM (l : Loc) (F : WRes → Prop) :
    ∀ n ls O e ρ, cerwp (ℍ := ℍ) (opTableC (TPM (ℍ := ℍ) l)) (QscM l) F n ls O e ρ →
      cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) (QPM (ℍ := ℍ) l F) F n ls O (hndE HP e) ρ := by
  refine cerwp_gen (QPM_down l F) 7 (qualsVal [.lin, .lin]) retV (Val.pair c₀ (Val.pair c₁ Val.unit))
    (fun m i en h => ?_) (fun k ls O v ρ hv => cerwp_retV (QPM_down l F) (.inl ⟨v, rfl, hv⟩))
    (fun i en h => ?_)
  · rcases TPM_some h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨rfl, by simp [liftEnt, spawnEntM], by simp [capTag, qualsVal, Val.pair, Val.i32,
        Qual.tag, liftEnt, spawnEntM]⟩
    · exact ⟨rfl, by simp [joinEntM], by simp [capTag, qualsVal, Val.pair, Val.i32, Qual.tag,
        joinEntM]⟩
  · rcases TPM_some h with ⟨-, rfl, rfl⟩ | ⟨-, rfl, rfl⟩
    · exact ⟨c₀, clauseAt0 _ _, fun k ls O v ℓ K ρa ρk ρak ρ _ hA hsh hak hc =>
        spawnCl_okM l F hA hsh hak hc⟩
    · exact ⟨c₁, clauseAt1 _ _ _, fun k ls O v ℓ K ρa ρk ρak ρ _ hA hsh hak hc =>
        joinCl_okM l F hA hsh hak hc⟩

/-- **A run of the child under `HC`.** -/
theorem genCM (l : Loc) (F : WRes → Prop) :
    ∀ n ls O e ρ, cerwp (ℍ := ℍ) (opTableC (TCM (ℍ := ℍ) l)) (QchildM l) F n ls O e ρ →
      cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) (QCM (ℍ := ℍ) l F) F n ls O (hndE HC e) ρ := by
  refine cerwp_gen (QCM_down l F) 8 (qualsVal [.cancel]) retV (Val.pair cy Val.unit)
    (fun m i en h => ?_) (fun k ls O v ρ hv => cerwp_retV (QCM_down l F) (.inl ⟨v, rfl, hv⟩))
    (fun i en h => ?_)
  · obtain ⟨rfl, rfl, rfl⟩ := TCM_some h
    exact ⟨rfl, by simp [yEntM], by simp [capTag, qualsVal, Val.pair, Val.i32, Qual.tag, yEntM]⟩
  · obtain ⟨-, rfl, rfl⟩ := TCM_some h
    exact ⟨cy, clauseAt0 _ _, fun k ls O v ℓ K ρa ρk ρak ρ hoc hA hsh hak hc => by
      exact yCl_okM l F hoc hA hsh hak hc⟩


/-! ### The scheduler -/

theorem mainM_ok (n : Nat) :
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Qmain (fun ρf => ρf = PMap.empty) n [] [] mainE
      (PMap.empty : WRes) := by
  have hLE := opTableC_local OpTabC.emptyC
  have hDE := opTableC_down opTabC_emptyC_down
  refine cerwp_allocX hLE (.appR (.val (Val.lam M1)) .hole) Val.unit (fun ℓ ρ' hc => ?_)
  obtain rfl := eq_of_compS_empty_left hc
  refine cerwp_det hDE Qmain_down (fun μ => step1Only_plug (Head.beta μ M1 (Val.loc ℓ)) rfl .hole) ?_
  simp only [M1, Expr.subst, HP_subst, omegaE_subst, hndE, Kont.plug, parentT_subst, loc_shift,
    prim_subst]
  simp (config := { decide := true }) only [if_false, Nat.reduceAdd]
  -- r₁: the parent, under `HP`, the cell its only resource
  refine cerwp_frameBindE (Q₁ := QPM (ℍ := ℍ) ℓ (fun _ => True)) (F₁ := fun _ => True)
    (fun ρ => ρ = PMap.empty) (.case .hole _ omegaE) (O₁ := []) (O₂ := [])
    (fun _ h => by simp at h) (ResU.comp_empty_right _) (fun _ _ _ _ _ => trivial)
    (genPM ℓ _ _ [] [] (parentE ℓ) _ (parentM_ok ℓ _ _ [])) rfl
    (fun k ls₁ O₁ v ρa ρb ρ' hk hq hR hc => ?_)
  subst hR
  obtain rfl := ResU.CompS.functional hc (ResU.comp_empty_right _)
  rcases hq with ⟨v₀, rfl, -⟩ | ⟨ℓf, ℓκ, f, ρ₁, ρv, ρ₂, rfl, h₁, hPA, h₁₂, hks⟩ | ⟨ℓκ, rfl, -⟩
  · refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₂ μ v₀ _ _) rfl .hole) ?_
    rw [omegaE_subst]
    exact cerwp_omega hLE _ _ _ _
  · -- the spawn: `(f, κ_p)` in their cells
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
      Kont.plug]
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
      inj₁_shift, pair_shift, loc_shift, Kont.plug]
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.letpair μ (Val.loc ℓf) (Val.loc ℓκ) _) rfl .hole) ?_
    simp (config := { decide := true }) only [M2, M3, M4, M5, Expr.subst, if_true, if_false,
      Nat.reduceAdd, Nat.reduceSub, inj₁_shift, pair_shift, loc_shift, Kont.plug, omegaE_subst,
      HC_subst, prim_subst, resumeT, hndE, freeE, locV_subst, unitV_subst, inj₁unitV_subst]
    rw [List.append_nil]
    -- r₂: the child, from the stored closure and its borrow; `κ_p` kept beside it
    obtain ⟨⟨uv, rfl⟩, hchild⟩ := hPA
    refine cerwp_frameBindE (Q₁ := QCM (ℍ := ℍ) ℓ (fun _ => True)) (F₁ := fun _ => True)
      (KapStored (ℍ := ℍ) (TPM (ℍ := ℍ) ℓ) (QscM ℓ) HP (liftEnt (spawnEntM (ℍ := ℍ) ℓ)) (fun _ => True)
        k ls₁ O₁ f ℓκ)
      (.case .hole _ omegaE) (O₁ := []) (O₂ := O₁) (fun _ h => by simp at h) h₁₂
      (fun _ _ _ _ _ => trivial) ?_ hks (fun k₂ ls₂ O₂ v ρa ρb ρ'' hk₂ hq hR hc₂ => ?_)
    · refine genCM ℓ _ _ _ _ _ _ ?_
      exact cerwp_freeX (opTableC_local _) (.appL .hole Val.unit) ℓf f h₁
        (hchild (k - 1) (by omega) ls₁ _)
    rcases hq with ⟨v₀, rfl, -⟩ | ⟨ℓκc, rfl, rfl, hkc⟩
    · refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₂ μ v₀ _ _) rfl .hole) ?_
      rw [omegaE_subst]
      exact cerwp_omega hLE _ _ _ _
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
      Nat.reduceSub, loc_shift, Kont.plug, omegaE_subst, prim_subst, locV_subst, unitV_subst,
      inj₁unitV_subst]
    -- r₃: the parent resumed, `κ_c` kept beside it
    rw [show ([] : List FrameRec) ++ O₁ = O₁ ++ [] by simp]
    refine cerwp_frameBindE (Q₁ := QPM (ℍ := ℍ) ℓ (fun ρf => True ∧ True))
      (F₁ := fun ρf => True ∧ True)
      (KapStored (ℍ := ℍ) (TCM (ℍ := ℍ) ℓ) (QchildM ℓ) HC (yEntM (ℍ := ℍ) ℓ) (fun _ => True) k₂ ls₂ []
        Val.unit ℓκc)
      (.case .hole _ omegaE) (O₁ := O₁) (O₂ := []) (fun _ _ h => by simp at h)
      (ResU.CompS.comm hc₂) (fun _ _ _ _ _ => ⟨trivial, trivial⟩)
      (cerwp_resumeStored (σ := PMap.empty) (QPM_down ℓ _) (genPM ℓ _) (kapStored_le hk₂ hR)
        (fun _ _ => ⟨rfl, rfl⟩) (ResU.comp_empty_right _) le_rfl (fun _ => trivial))
      hkc (fun k₃ ls₃ O₃ v ρa₃ ρb₃ ρ₃ hk₃ hq hR₃ hc₃ => ?_)
    rcases hq with ⟨v₀, rfl, -⟩ | ⟨ℓf', ℓκ', f', -, -, -, rfl, -⟩ | ⟨ℓκp, rfl, hkp⟩
    · refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₂ μ v₀ _ _) rfl .hole) ?_
      rw [omegaE_subst]
      exact cerwp_omega hLE _ _ _ _
    · refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
      simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
        Kont.plug, omegaE_subst]
      refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
      rw [omegaE_subst]
      exact cerwp_omega hLE _ _ _ _
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
      Nat.reduceSub, inj₂_shift, loc_shift, Kont.plug, omegaE_subst, prim_subst, locV_subst,
      unitV_subst, inj₁unitV_subst]
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₂ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, Nat.reduceAdd, Kont.plug, omegaE_subst,
      prim_subst, locV_subst, unitV_subst, inj₁unitV_subst]
    -- r₄: the child resumed, `κ′_p` kept beside it
    rw [List.append_nil]
    refine cerwp_frameBindE (Q₁ := QCM (ℍ := ℍ) ℓ (fun ρf => True ∧ True))
      (F₁ := fun ρf => True ∧ True)
      (KapStored (ℍ := ℍ) (TPM (ℍ := ℍ) ℓ) (QscM ℓ) HP (joinEntM ℓ AM PM) (fun ρf => True ∧ True) k₃
        ls₃ O₃ (Val.loc ℓ) ℓκp)
      (.case .hole omegaE _) (O₁ := []) (O₂ := O₃) (fun _ h => by simp at h)
      (ResU.CompS.comm hc₃) (fun _ _ _ _ _ => ⟨trivial, trivial⟩)
      (cerwp_resumeStored (σ := PMap.empty) (QCM_down ℓ _) (genCM ℓ _) (kapStored_le hk₃ hR₃)
        (fun _ _ => ⟨rfl, rfl⟩) (ResU.comp_empty_right _) le_rfl (fun _ => trivial))
      hkp (fun k₄ ls₄ O₄ v ρa₄ ρb₄ ρ₄ hk₄ hq hR₄ hc₄ => ?_)
    rcases hq with ⟨v₀, rfl, hO₄, hleft⟩ | ⟨ℓκ', rfl, -, -⟩
    swap
    · refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
      rw [omegaE_subst]
      exact cerwp_omega hLE _ _ _ _
    subst hO₄
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₂ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, Nat.reduceAdd, Kont.plug, omegaE_subst,
      prim_subst, locV_subst, unitV_subst, inj₁unitV_subst]
    -- r₅: the parent resumed from the join, with the borrow back
    obtain ⟨uc, rfl⟩ := hleft
    rw [show ([] : List FrameRec) ++ O₃ = O₃ ++ [] by simp]
    refine cerwp_frameBindE (Q₁ := QPM (ℍ := ℍ) ℓ (fun ρf => (True ∧ True) ∧ True))
      (F₁ := fun ρf => (True ∧ True) ∧ True) (fun ρ => ρ = PMap.empty)
      (.case .hole omegaE _) (O₁ := O₃) (O₂ := []) (fun _ _ h => by simp at h)
      (ResU.comp_empty_right _) (fun _ _ _ _ _ => ⟨⟨trivial, trivial⟩, trivial⟩)
      (cerwp_resumeStored (σ := mcell ℓ uc) (QPM_down ℓ _) (genPM ℓ _) (kapStored_le hk₄ hR₄)
        (fun _ _ => ⟨ℓ, rfl, rfl, uc, PMap.empty, inStratumE AM, rfl, rfl⟩)
        (ResU.CompS.comm hc₄) le_rfl (fun _ => trivial))
      rfl (fun k₅ ls₅ O₅ v ρa₅ ρb₅ ρ₅ hk₅ hq hR₅ hc₅ => ?_)
    subst hR₅
    rcases hq with ⟨v₀, rfl, rfl, rfl, u₅, rfl⟩ | ⟨-, -, -, -, -, -, rfl, -⟩ | ⟨-, rfl, -⟩
    · -- the parent finished: the cell owned again, freed; the scheduler's result
      refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₂ μ _ _ _) rfl .hole) ?_
      simp only [Expr.subst, prim_subst, locV_subst, Kont.plug]
      exact cerwp_freeX hLE .hole ℓ u₅ hc₅ (cerwp_val ⟨rfl, fun _ _ h => by simp at h⟩)
    · refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
      rw [omegaE_subst]
      exact cerwp_omega hLE _ _ _ _
    · refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
      rw [omegaE_subst]
      exact cerwp_omega hLE _ _ _ _
  · refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
      inj₂_shift, loc_shift, Kont.plug, omegaE_subst]
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₂ μ _ _ _) rfl .hole) ?_
    rw [omegaE_subst]
    exact cerwp_omega hLE _ _ _ _


/-- **The cross-task test, `mut`.** The program of `prog_orDiverges`, the lend `mut`: the borrow
moved to the child, held across its `y`, read through, returned at the join. No fuel. -/
theorem progM_orDiverges : OrDiverges (ℍ := ℍ) mainE :=
  cerwp_adequacy (fun _ _ _ _ _ h => h) mainM_ok

theorem mainDM_ok (n : Nat) :
    cerwp (ℍ := ℍ) (opTableC OpTabC.emptyC) Qmain (fun ρf => ρf = PMap.empty) n [] [] mainD
      (PMap.empty : WRes) := by
  have hLE := opTableC_local OpTabC.emptyC
  have hDE := opTableC_down opTabC_emptyC_down
  refine cerwp_allocX hLE (.appR (.val (Val.lam M1d)) .hole) Val.unit (fun ℓ ρ' hc => ?_)
  obtain rfl := eq_of_compS_empty_left hc
  refine cerwp_det hDE Qmain_down (fun μ => step1Only_plug (Head.beta μ M1d (Val.loc ℓ)) rfl .hole) ?_
  simp only [M1d, Expr.subst, HP_subst, omegaE_subst, hndE, Kont.plug, parentT_subst, loc_shift,
    prim_subst]
  simp (config := { decide := true }) only [if_false, Nat.reduceAdd]
  -- r₁: the parent, under `HP`, the cell its only resource
  refine cerwp_frameBindE (Q₁ := QPM (ℍ := ℍ) ℓ (fun _ => True)) (F₁ := fun _ => True)
    (fun ρ => ρ = PMap.empty) (.case .hole _ omegaE) (O₁ := []) (O₂ := [])
    (fun _ h => by simp at h) (ResU.comp_empty_right _) (fun _ _ _ _ _ => trivial)
    (genPM ℓ _ _ [] [] (parentE ℓ) _ (parentM_ok ℓ _ _ [])) rfl
    (fun k ls₁ O₁ v ρa ρb ρ' hk hq hR hc => ?_)
  subst hR
  obtain rfl := ResU.CompS.functional hc (ResU.comp_empty_right _)
  rcases hq with ⟨v₀, rfl, -⟩ | ⟨ℓf, ℓκ, f, ρ₁, ρv, ρ₂, rfl, h₁, hPA, h₁₂, hks⟩ | ⟨ℓκ, rfl, -⟩
  · refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₂ μ v₀ _ _) rfl .hole) ?_
    rw [omegaE_subst]
    exact cerwp_omega hLE _ _ _ _
  · -- the spawn: `(f, κ_p)` in their cells
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
      Kont.plug]
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
      inj₁_shift, pair_shift, loc_shift, Kont.plug]
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.letpair μ (Val.loc ℓf) (Val.loc ℓκ) _) rfl .hole) ?_
    simp (config := { decide := true }) only [M2d, M3d, M4d, Expr.subst, if_true, if_false,
      Nat.reduceAdd, Nat.reduceSub, inj₁_shift, pair_shift, loc_shift, Kont.plug, omegaE_subst,
      HC_subst, prim_subst, resumeT, hndE, freeE, locV_subst, unitV_subst, inj₁unitV_subst,
      inj₂unitV_subst]
    rw [List.append_nil]
    -- r₂: the child, from the stored closure and its borrow; `κ_p` kept beside it
    obtain ⟨⟨uv, rfl⟩, hchild⟩ := hPA
    refine cerwp_frameBindE (Q₁ := QCM (ℍ := ℍ) ℓ (fun _ => True)) (F₁ := fun _ => True)
      (KapStored (ℍ := ℍ) (TPM (ℍ := ℍ) ℓ) (QscM ℓ) HP (liftEnt (spawnEntM (ℍ := ℍ) ℓ)) (fun _ => True)
        k ls₁ O₁ f ℓκ)
      (.case .hole _ omegaE) (O₁ := []) (O₂ := O₁) (fun _ h => by simp at h) h₁₂
      (fun _ _ _ _ _ => trivial) ?_ hks (fun k₂ ls₂ O₂ v ρa ρb ρ'' hk₂ hq hR hc₂ => ?_)
    · refine genCM ℓ _ _ _ _ _ _ ?_
      exact cerwp_freeX (opTableC_local _) (.appL .hole Val.unit) ℓf f h₁
        (hchild (k - 1) (by omega) ls₁ _)
    rcases hq with ⟨v₀, rfl, -⟩ | ⟨ℓκc, rfl, rfl, hkc⟩
    · refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₂ μ v₀ _ _) rfl .hole) ?_
      rw [omegaE_subst]
      exact cerwp_omega hLE _ _ _ _
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
      Nat.reduceSub, loc_shift, Kont.plug, omegaE_subst, prim_subst, locV_subst, unitV_subst,
      inj₁unitV_subst]
    -- r₃: the parent resumed, `κ_c` kept beside it
    rw [show ([] : List FrameRec) ++ O₁ = O₁ ++ [] by simp]
    refine cerwp_frameBindE (Q₁ := QPM (ℍ := ℍ) ℓ (fun ρf => True ∧ True))
      (F₁ := fun ρf => True ∧ True)
      (KapStored (ℍ := ℍ) (TCM (ℍ := ℍ) ℓ) (QchildM ℓ) HC (yEntM (ℍ := ℍ) ℓ) (fun _ => True) k₂ ls₂ []
        Val.unit ℓκc)
      (.case .hole _ omegaE) (O₁ := O₁) (O₂ := []) (fun _ _ h => by simp at h)
      (ResU.CompS.comm hc₂) (fun _ _ _ _ _ => ⟨trivial, trivial⟩)
      (cerwp_resumeStored (σ := PMap.empty) (QPM_down ℓ _) (genPM ℓ _) (kapStored_le hk₂ hR)
        (fun _ _ => ⟨rfl, rfl⟩) (ResU.comp_empty_right _) le_rfl (fun _ => trivial))
      hkc (fun k₃ ls₃ O₃ v ρa₃ ρb₃ ρ₃ hk₃ hq hR₃ hc₃ => ?_)
    rcases hq with ⟨v₀, rfl, -⟩ | ⟨ℓf', ℓκ', f', -, -, -, rfl, -⟩ | ⟨ℓκp, rfl, hkp⟩
    · refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₂ μ v₀ _ _) rfl .hole) ?_
      rw [omegaE_subst]
      exact cerwp_omega hLE _ _ _ _
    · refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
      simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
        Kont.plug, omegaE_subst]
      refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
      rw [omegaE_subst]
      exact cerwp_omega hLE _ _ _ _
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
      Nat.reduceSub, inj₂_shift, loc_shift, Kont.plug, omegaE_subst, prim_subst, locV_subst,
      unitV_subst, inj₁unitV_subst]
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₂ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, Nat.reduceAdd, Kont.plug, omegaE_subst,
      prim_subst, locV_subst, unitV_subst, inj₁unitV_subst]
    -- r₄: the child cancelled while the lend is live, `κ′_p` kept beside it; the cancel run
    -- unwinds the child and returns its borrow
    rw [List.append_nil]
    refine cerwp_frameBindE (Q₁ := QleftM ℓ) (F₁ := fun _ => True)
      (KapStored (ℍ := ℍ) (TPM (ℍ := ℍ) ℓ) (QscM ℓ) HP (joinEntM ℓ AM PM) (fun ρf => True ∧ True)
        k₃ ls₃ O₃ (Val.loc ℓ) ℓκp)
      (.seq .hole _) (O₁ := []) (O₂ := O₃) (fun _ h => by simp at h)
      (ResU.CompS.comm hc₃) (fun _ _ _ _ _ => trivial)
      (cerwp_cancelStored (Qin := QchildM ℓ) (QleftM_down ℓ) rfl
        (fun _ _ _ _ h => h (PcanM (ℍ := ℍ) ℓ) rfl _)
        (kapStored_le hk₃ hR₃) le_rfl (fun _ => trivial)
        (fun P hP j k' ls' e' ρ'' hj h => by
          cases hP
          exact fun F => cerwp_le (opTableC_local _) (opTableC_down opTabC_emptyC_down)
            (QleftM_down ℓ) hj (h F)))
      hkp (fun k₄ ls₄ O₄ v ρa₄ ρb₄ ρ₄ hk₄ hq hR₄ hc₄ => ?_)
    obtain ⟨hO₄, rfl, hleft⟩ := hq
    subst hO₄
    refine cerwp_det hDE Qmain_down (fun μ => step1Only_plug (Head.seq μ _) rfl .hole) ?_
    -- r₅: the parent resumed from the join, with the borrow back
    obtain ⟨uc, rfl⟩ := hleft
    rw [show ([] : List FrameRec) ++ O₃ = O₃ ++ [] by simp]
    refine cerwp_frameBindE (Q₁ := QPM (ℍ := ℍ) ℓ (fun ρf => (True ∧ True) ∧ True))
      (F₁ := fun ρf => (True ∧ True) ∧ True) (fun ρ => ρ = PMap.empty)
      (.case .hole omegaE _) (O₁ := O₃) (O₂ := []) (fun _ _ h => by simp at h)
      (ResU.comp_empty_right _) (fun _ _ _ _ _ => ⟨⟨trivial, trivial⟩, trivial⟩)
      (cerwp_resumeStored (σ := mcell ℓ uc) (QPM_down ℓ _) (genPM ℓ _) (kapStored_le hk₄ hR₄)
        (fun _ _ => ⟨ℓ, rfl, rfl, uc, PMap.empty, inStratumE AM, rfl, rfl⟩)
        (ResU.CompS.comm hc₄) le_rfl (fun _ => trivial))
      rfl (fun k₅ ls₅ O₅ v ρa₅ ρb₅ ρ₅ hk₅ hq hR₅ hc₅ => ?_)
    subst hR₅
    rcases hq with ⟨v₀, rfl, rfl, rfl, u₅, rfl⟩ | ⟨-, -, -, -, -, -, rfl, -⟩ | ⟨-, rfl, -⟩
    · -- the parent finished: the cell owned again, freed; the scheduler's result
      refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₂ μ _ _ _) rfl .hole) ?_
      simp only [Expr.subst, prim_subst, locV_subst, Kont.plug]
      exact cerwp_freeX hLE .hole ℓ u₅ hc₅ (cerwp_val ⟨rfl, fun _ _ h => by simp at h⟩)
    · refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
      rw [omegaE_subst]
      exact cerwp_omega hLE _ _ _ _
    · refine cerwp_det hDE Qmain_down
        (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
      rw [omegaE_subst]
      exact cerwp_omega hLE _ _ _ _
  · refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₁ μ _ _ _) rfl .hole) ?_
    simp (config := { decide := true }) only [Expr.subst, if_true, if_false, Nat.reduceAdd,
      inj₂_shift, loc_shift, Kont.plug, omegaE_subst]
    refine cerwp_det hDE Qmain_down
      (fun μ => step1Only_plug (Head.case₂ μ _ _ _) rfl .hole) ?_
    rw [omegaE_subst]
    exact cerwp_omega hLE _ _ _ _



/-- **The cross-task test, `mut`, the cancel.** As `progD_orDiverges`, the lend `mut`: the
scheduler cancels the child while the lend is live; the cancel run returns the borrow, which the
join hands back. No fuel. -/
theorem progDM_orDiverges : OrDiverges (ℍ := ℍ) mainD :=
  cerwp_adequacy (fun _ _ _ _ _ h => h) mainDM_ok

end BoCa.Fig16.LogRel.Core.Chain.SI.CrossProgM

end
