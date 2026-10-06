import Targets.Defs.World

/-!
# Targets — Core is the σ = [] instance: the transports (DESIGN §1.4)

Each derived definition of `Defs/World.lean`, taken at `coreW`, is Core's: `wpGW` is `wpG`,
`ewpW` is `ewpTS`, `opTabW` is `opTable`, `cancelTabW` at the trivial closing clause is
`cancelTab`, `ptoMutSW`/`ptoImmSW` are `ptoMutS`/`ptoImmS`, `gDenW` is `gDenC`, and `SemW₀` is
`SemJ`.  Each is by unfolding.  `[Core σ=[]]`
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun performE raiseE opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- An index of `coreW` is a record list. -/
theorem idx_unit (i : Idx Unit) : i = (i.1, ()) := by rcases i with ⟨a, ⟨⟩⟩; rfl

/-- `wpGW` at `coreW` is `wpG`. -/
theorem wpGW_core {ls : List SRec} {e : Expr} {Q : Idx Unit → Expr → WProp} {ρ : WRes} :
    wpGW (ℍ := ℍ) (coreW (ℍ := ℍ)) (ls, ()) e Q ρ ↔ wpG (ℍ := ℍ) ls e (fun ls' t => Q (ls', ()) t) ρ := by
  constructor
  · intro h ρf fρ ps hf hc hT htg A k
    obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ⟨ls', ⟨⟩⟩, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀,
      ⟨hT', htg'⟩, ⟨hps, hls⟩, hQ⟩ := h ρf fρ ps hf hc ⟨hT, htg⟩ A k
    exact ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, hT',
      htg', hps, hls, hQ⟩
  · intro h ρf fρ ps hf hc hF A k
    obtain ⟨hT, htg⟩ := hF
    obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', ls', h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀,
      hT', htg', hps, hls, hQ⟩ := h ρf fρ ps hf hc hT htg A k
    exact ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', (ls', ()), h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀,
      ⟨hT', htg'⟩, ⟨hps, hls⟩, hQ⟩

/-- `ewpW` at `coreW` is `ewpTS`. -/
theorem ewpW_core {ls : List SRec} {e : Expr} {Tb : TableI (Idx Unit)} {Q : Idx Unit → Val → WProp}
    {ρ : WRes} :
    ewpW (ℍ := ℍ) (coreW (ℍ := ℍ)) (ls, ()) e Tb Q ρ ↔
      ewpTS (ℍ := ℍ) ls e (TableI.down Tb) (fun ls v => Q (ls, ()) v) ρ := by
  constructor
  · intro h P hP
    refine h (fun i e => P i.1 e) ?_
    intro i e ρ hw
    rw [idx_unit i] at hw
    exact hP i.1 e ρ (wpGW_core.mp hw)
  · intro h P hP
    refine h (fun ls e => P (ls, ()) e) ?_
    intro ls e ρ hs
    have hP' : (fun (i : Idx Unit) e => P (i.1, ()) e) = P := by
      funext i e; rcases i with ⟨a, ⟨⟩⟩; rfl
    refine hP (ls, ()) e ρ (wpGW_core.mpr ?_)
    have hs' : wpG (ℍ := ℍ) ls e (fun ls' t ρ' => valPostI Q (ls', ()) t ρ' ∨
        Tb (ls', ()) t (fun i e => P (i.1, ()) e) ρ') ρ := hs
    rw [hP'] at hs'
    exact hs'

/-- The entries of `coreW`'s tables read at Core's records. -/
theorem opTabI_down_some {T : OpTabI (Idx Unit)} {n j : UInt32} {en' : OpEnt} :
    OpTabI.down T n j = some en' ↔ ∃ en, T n j = some en ∧ en' = OpEntI.down en := by
  simp only [OpTabI.down, Option.map_eq_some_iff]
  exact ⟨fun ⟨en, h, e⟩ => ⟨en, h, e.symm⟩, fun ⟨en, h, e⟩ => ⟨en, h, e.symm⟩⟩

/-- `opTabW` at `coreW` is `opTable`. -/
theorem opTabW_core {T : OpTabI (Idx Unit)} {ls : List SRec} {t : Expr}
    {Φ : Idx Unit → Expr → WProp} {ρ : WRes} :
    opTabW (coreW (ℍ := ℍ)) T (ls, ()) t Φ ρ ↔
      opTable (OpTabI.down T) ls t (fun ls e => Φ (ls, ()) e) ρ := by
  constructor
  · rintro (⟨K, n, j, v, en, h⟩ | ⟨K, n, j, v, en, h⟩)
    · obtain ⟨⟨ht, hK, hT, ha⟩, hR⟩ := pure_sep_iff.mp h
      exact Or.inl ⟨K, n, j, v, OpEntI.down en,
        pure_sep_mk ⟨ht, hK, opTabI_down_some.mpr ⟨en, hT, rfl⟩, ha⟩ hR⟩
    · obtain ⟨⟨ht, hK, hT, ha⟩, hR⟩ := pure_sep_iff.mp h
      exact Or.inr ⟨K, n, j, v, OpEntI.down en,
        pure_sep_mk ⟨ht, hK, opTabI_down_some.mpr ⟨en, hT, rfl⟩, ha⟩ hR⟩
  · rintro (⟨K, n, j, v, en', h⟩ | ⟨K, n, j, v, en', h⟩)
    · obtain ⟨⟨ht, hK, hT, ha⟩, hR⟩ := pure_sep_iff.mp h
      obtain ⟨en, hT', rfl⟩ := opTabI_down_some.mp hT
      exact Or.inl ⟨K, n, j, v, en, pure_sep_mk ⟨ht, hK, hT', ha⟩ hR⟩
    · obtain ⟨⟨ht, hK, hT, ha⟩, hR⟩ := pure_sep_iff.mp h
      obtain ⟨en, hT', rfl⟩ := opTabI_down_some.mp hT
      exact Or.inr ⟨K, n, j, v, en, pure_sep_mk ⟨ht, hK, hT', ha⟩ hR⟩

/-- `opTabW` at `coreW`, as a table, is `opTable`. -/
theorem opTabW_core_down (T : OpTabI (Idx Unit)) :
    TableI.down (opTabW (coreW (ℍ := ℍ)) T) = opTable (OpTabI.down T) := by
  funext ls t Φ ρ
  exact propext opTabW_core

/-- `errOkW` at `coreW`'s tables is `errOk`. -/
theorem errOkW_core {T : OpTabI (Idx Unit)} {N : List UInt32} {ls : List SRec} :
    ∀ {err : Option Val} {ρ : WRes}, errOkW T N (ls, ()) err ρ ↔ errOk (OpTabI.down T) N ls err ρ
  | none, _ => Iff.rfl
  | some E, ρ => by
      constructor
      · rintro ⟨m, j, w, en, h⟩
        obtain ⟨⟨hE, hm, hT, ha⟩, hR⟩ := pure_sep_iff.mp h
        exact ⟨m, j, w, OpEntI.down en,
          pure_sep_mk ⟨hE, hm, opTabI_down_some.mpr ⟨en, hT, rfl⟩, ha⟩ hR⟩
      · rintro ⟨m, j, w, en', h⟩
        obtain ⟨⟨hE, hm, hT, ha⟩, hR⟩ := pure_sep_iff.mp h
        obtain ⟨en, hT', rfl⟩ := opTabI_down_some.mp hT
        exact ⟨m, j, w, en, pure_sep_mk ⟨hE, hm, hT', ha⟩ hR⟩

/-- `cancelTabW` at the trivial closing clause, at `coreW`'s tables, is `cancelTab`. -/
theorem cancelTabW_core {T : OpTabI (Idx Unit)} {N : List UInt32} {Cl : Idx Unit → Prop}
    (hCl : ∀ i, Cl i) {ls : List SRec} {t : Expr} {Φ : Idx Unit → Expr → WProp} {ρ : WRes} :
    cancelTabW T N Cl (ls, ()) t Φ ρ ↔
      cancelTab (OpTabI.down T) N ls t (fun ls e => Φ (ls, ()) e) ρ := by
  constructor
  · rintro ⟨K, err, h⟩
    obtain ⟨⟨ht, hK, -⟩, τ₁, τ₂, hc, he, hn⟩ := pure_sep_iff.mp h
    exact ⟨K, err, pure_sep_mk ⟨ht, hK⟩ ⟨τ₁, τ₂, hc, errOkW_core.mp he, hn⟩⟩
  · rintro ⟨K, err, h⟩
    obtain ⟨⟨ht, hK⟩, τ₁, τ₂, hc, he, hn⟩ := pure_sep_iff.mp h
    exact ⟨K, err, pure_sep_mk ⟨ht, hK, hCl _⟩ ⟨τ₁, τ₂, hc, errOkW_core.mpr he, hn⟩⟩

/-- A row's table at `coreW`, read at Core's records, is `Row.tab`. -/
theorem rowTabW_core (S : Row) (δ : LSub) :
    OpTabI.down (rowTabW (coreW (ℍ := ℍ)) S δ) = Row.tab (ℍ := ℍ) S δ := by
  funext n i
  simp only [OpTabI.down, rowTabW, Row.tab]
  cases Row.find S n i <;> rfl

/-- `ptoMutSW` at `coreW` is `ptoMutS`. -/
theorem ptoMutSW_core (l : Loc) (α : Life) (ls : List SRec) (P : List SRec → Val → WProp) :
    ptoMutSW (coreW (ℍ := ℍ)) l α (ls, ()) (fun i => P i.1) = ptoMutS l α ls P := by
  funext ρ
  apply propext
  constructor
  · rintro ⟨b, u, σ, h, Q, hw, ls₀, h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨b, u, σ, h, Q, hw, ls₀, h₁, h₂, h₃, h₄, fun ls' => h₅ (ls', ())⟩
  · rintro ⟨b, u, σ, h, Q, hw, ls₀, h₁, h₂, h₃, h₄, h₅⟩
    exact ⟨b, u, σ, h, Q, hw, ls₀, h₁, h₂, h₃, h₄, fun i' => h₅ i'.1⟩

/-- `ptoImmSW` at `coreW` is `ptoImmS`. -/
theorem ptoImmSW_core (l : Loc) (α : Life) (ls : List SRec) (P : List SRec → Val → WProp) :
    ptoImmSW (coreW (ℍ := ℍ)) l α (ls, ()) (fun i => P i.1) = ptoImmS l α ls P := rfl

/-- `gSepW` at `coreW` is `gSepC`. -/
theorem gSepW_core (ls : List SRec) (δ : LSub) : ∀ (Γ : Ctx VTy) (γ : List Val),
    gSepW (coreW (ℍ := ℍ)) (ls, ()) δ Γ γ = gSepC (ℍ := ℍ) ls δ Γ γ
  | [], _ => rfl
  | _ :: _, [] => rfl
  | s :: Γ, v :: γ => by
      simp only [gSepW, gSepC, gSepW_core ls δ Γ γ]

/-- `gDenW` at `coreW` is `gDenC`. -/
theorem gDenW_core (ls : List SRec) (δ : LSub) (Γ : Ctx VTy) (γ : List Val) :
    gDenW (coreW (ℍ := ℍ)) (ls, ()) δ Γ γ = gDenC (ℍ := ℍ) ls δ Γ γ := by
  simp only [gDenW, gDenC]
  rw [gSepW_core]

/-- `SemWC` at `coreW` is `SemC`. -/
theorem semWC_core {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {C : CTy} :
    SemWC (coreW (ℍ := ℍ)) Δ Γ e C ↔ SemC (ℍ := ℍ) Δ Γ e C := by
  constructor
  · intro h δ γ ls ρ hδ hg
    exact h δ γ (ls, ()) ρ hδ (by rw [gDenW_core]; exact hg)
  · intro h δ γ i ρ hδ hg
    rcases i with ⟨ls, ⟨⟩⟩
    rw [gDenW_core] at hg
    exact h δ γ ls ρ hδ hg

/-- `SemW₀` at `coreW` is `SemJ`. -/
theorem semW₀_core {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} :
    ∀ {j : Jdg}, SemW₀ (coreW (ℍ := ℍ)) Δ Γ e j ↔ SemJ (ℍ := ℍ) Δ Γ e j
  | .comp _ => semWC_core
  | .val _ => semWC_core

/-! ### The transports as equations at a variable index (for rewriting under binders) -/

theorem wpGW_core_eq (i : Idx (coreW (ℍ := ℍ)).Stk) (e : Expr)
    (Q : Idx (coreW (ℍ := ℍ)).Stk → Expr → WProp) :
    wpGW (ℍ := ℍ) (coreW (ℍ := ℍ)) i e Q = wpG (ℍ := ℍ) i.1 e (fun ls' t => Q (ls', ()) t) := by
  rcases i with ⟨ls, ⟨⟩⟩
  funext ρ; exact propext wpGW_core

theorem ewpW_core_eq (i : Idx (coreW (ℍ := ℍ)).Stk) (e : Expr) (Tb : TableI (Idx Unit))
    (Q : Idx (coreW (ℍ := ℍ)).Stk → Val → WProp) :
    ewpW (ℍ := ℍ) (coreW (ℍ := ℍ)) i e Tb Q =
      ewpTS (ℍ := ℍ) i.1 e (TableI.down Tb) (fun ls v => Q (ls, ()) v) := by
  rcases i with ⟨ls, ⟨⟩⟩
  funext ρ; exact propext ewpW_core

theorem ptoMutSW_core_eq (l : Loc) (α : Life) (i : Idx (coreW (ℍ := ℍ)).Stk) (A : VTy) (δ : LSub) :
    ptoMutSW (coreW (ℍ := ℍ)) l α i (fun i₀ => vCE (ℍ := ℍ) none true A i₀.1 δ) =
      ptoMutS l α i.1 (fun ls₀ => vCE (ℍ := ℍ) none true A ls₀ δ) := by
  rcases i with ⟨ls, ⟨⟩⟩
  exact ptoMutSW_core l α ls (fun ls₀ => vCE none true A ls₀ δ)

end Targets

end
