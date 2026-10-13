import Core.Fundamental
import GhostEnd.Frames
import Targets.B.World
import Targets.Base.Machine

/-!
# The interaction — its world, the effectful wp, and the transports (RESTRUCTURE §3.1)

`SemWorld extends B.BWorld` with what the interaction adds: `held` (what suspensions hold, OQ-9),
`Stop` (the stop condition, R-T1 at Core) and `share` (what a stop at a resuming operation owes its
continuation, Core's `contShare`).  `coreW` is Core's relation as such a world, `coreB` inside.

I owns the definitions that read `Stop`, `share` or `held`: `wpGW` (whose run end is `M.Upd`,
FIX-RUN-END §2.1), `ewpW`, `opTabW`, `errOkW`, `cancelTabW`, `entW`, `rowTabW`, and the transports
to `coreW`, with the step lemmas at every world.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun performE raiseE opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- Core's protocol tables (`Table`), at any index. -/
abbrev TableI (I : Type) := I → Expr → (I → Expr → WProp) → WProp

/-- A table is monotone in the continuations it owes. -/
def TableI.Mono {I : Type} (Tb : TableI I) : Prop :=
  ∀ i t (Φ Φ' : I → Expr → WProp) ρ, (∀ i e ρ, Φ i e ρ → Φ' i e ρ) → Tb i t Φ ρ → Tb i t Φ' ρ

/-- A table that owes no continuation. -/
def TableI.Abortive {I : Type} (Tb : TableI I) : Prop :=
  ∀ i t (Φ Φ' : I → Expr → WProp) ρ, Tb i t Φ ρ → Tb i t Φ' ρ

/-- An operation's entry (`OpEnt`), at any index. -/
structure OpEntI (I : Type) where
  q : Qual
  abort : Bool
  PA : I → Val → WProp
  PB : I → Val → WProp

/-- An operation table (`OpTab`), at any index. -/
abbrev OpTabI (I : Type) := UInt32 → UInt32 → Option (OpEntI I)


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun performE raiseE opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **The interaction's world**: B's borrow world, plus what suspensions hold (`held`, OQ-9), the
stop condition (R-T1 at Core), and what a stop at a resuming operation owes its continuation
(`share`, Core's `contShare`). -/
structure SemWorld extends B.BWorld where
  /-- What the suspended computations at an index hold: their open 6.64 frames and their tagged
  records.  Where they are kept is OQ-9's question; under its option (b) nothing is held.  A
  6.65 `Mut` lend adds no 6.64 frame or record, so `held` does not see it; a world that carries
  one open across a stop accounts for it through `Upd` and the index (OQ-9 (a), OQ-44). -/
  held  : Idx Stk → List FrameRec × List SRec
  /-- The stop condition: entry frames/index, exit frames/index, final term.  Core's is R-T1. -/
  Stop  : List FrameRec × Idx Stk → List FrameRec × Idx Stk → Expr → Prop
  /-- What a stop at a resuming operation owes its continuation (Core's `contShare`). -/
  share : OpTabI (Idx Stk) → OpEntI (Idx Stk) → UInt32 → Idx Stk → Kont →
            (Idx Stk → Expr → WProp) → WProp

/-- A world of the interaction is read as its borrow world wherever B's statements read one. -/
instance : Coe SemWorld B.BWorld := ⟨SemWorld.toBWorld⟩



end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun performE raiseE opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- W's one-run wp: `wpG` over `M.Fam`, ending under `M.Stop` and `M.Upd`. -/
def wpGW (M : SemWorld) (i : Idx M.Stk) (e : Expr) (Q : Idx M.Stk → Expr → WProp) : WProp :=
  fun ρ => ∀ (ρf fρ : WRes) (ps : List FrameRec), ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ →
    M.Fam fρ ps i → ∀ (A : Alloc) (k : Nat),
    ∃ (ρ' ρp fρ' fρ'p π : WRes) (t : Expr) (μ μ' : Heap) (ps' : List FrameRec)
      (i' : Idx M.Stk),
      ResU.Hash ρ' ρf ∧ ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧ ResU.Lower fρ μ ∧
      ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧ (∃ k', ARun (ℍ := ℍ) A k μ e k' μ' t) ∧
      ResU.CompS ρ' ρp π ∧ M.Upd i i' ρ ρ' π ∧ NoOwn ρp ∧
      M.Fam fρ'p ps' i' ∧ M.Stop (ps, i) (ps', i') t ∧ Q i' t ρ'

/-- The postcondition over terms that admits only values. -/
def valPostI {I : Type} (Q : I → Val → WProp) : I → Expr → WProp :=
  fun i t ρ => ∃ v : Val, t = .val v ∧ Q i v ρ

/-- W's effectful wp: the least fixed point of "run to a value in `Q` or to a stop `Tb` admits",
written in `Prop` as `ewpTS` is. -/
def ewpW (M : SemWorld) (i : Idx M.Stk) (e : Expr) (Tb : TableI (Idx M.Stk))
    (Q : Idx M.Stk → Val → WProp) : WProp := fun ρ =>
  ∀ P : Idx M.Stk → Expr → WProp,
    (∀ i e ρ, wpGW (ℍ := ℍ) M i e (fun i' t ρ' => valPostI Q i' t ρ' ∨ Tb i' t P ρ') ρ →
      P i e ρ) →
    P i e ρ

/-- A value in `Q`, or a stop owing nothing (`ewpPost`). -/
def ewpPostW {I : Type} (Tb : TableI I) (Q : I → Val → WProp) : I → Expr → WProp :=
  fun i t ρ => valPostI Q i t ρ ∨ Tb i t (fun _ _ _ => False) ρ

/-- The protocol of an operation table at W: `opTable` with `M.share` for `contShare`. -/
def opTabW (M : SemWorld) (T : OpTabI (Idx M.Stk)) : TableI (Idx M.Stk) := fun i t Φ =>
  BoLo.or
    (ex fun K => ex fun n => ex fun j => ex fun v => ex fun en =>
      ⌜t = Kont.plug K (performE (.val (opPayload n j v))) ∧ K.HasHnd n = false ∧
        T n j = some en ∧ en.abort = false⌝ ⋆ (en.PA i v ⋆ M.share T en n i K Φ))
    (ex fun K => ex fun n => ex fun j => ex fun v => ex fun en =>
      ⌜t = Kont.plug K (raiseE (.val (opPayload n j v))) ∧ K.Catches n = false ∧
        T n j = some en ∧ en.abort = true⌝ ⋆
        ((fun ρ => en.PA i v ρ ∧ NoOwn ρ) ⋆ fun ρ => NoOwn ρ))

/-- The error a cancel carries (`errOk`), at any index. -/
def errOkW {I : Type} (T : OpTabI I) (N : List UInt32) (i : I) : Option Val → WProp
  | none => emp
  | some E => ex fun m => ex fun j => ex fun w => ex fun (en : OpEntI I) =>
      ⌜E = opPayload m j w ∧ m ∉ N ∧ T m j = some en ∧ en.abort = true⌝ ⋆
        fun ρ => en.PA i w ρ ∧ NoOwn ρ

/-- The table of a cancel run (`cancelTab`), at any index.  `Cl` is a condition on the index the
cancel ends at (I3.a's closing clause); Core's `cancelTab` is `cancelTabW T N (fun _ => True)`. -/
def cancelTabW {I : Type} (T : OpTabI I) (N : List UInt32) (Cl : I → Prop) : TableI I :=
  fun i t _ =>
  ex fun (K : Kont) => ex fun (err : Option Val) =>
    ⌜t = K.plug (raiseE (.val (cancelVal N err))) ∧ K.Catches 0 = false ∧ Cl i⌝ ⋆
      (errOkW T N i err ⋆ fun ρ => NoOwn ρ)

/-- An operation's entry at W (`OpSig.ent`). -/
def entW (M : SemWorld) (δ : LSub) (o : OpSig) : OpEntI (Idx M.Stk) :=
  ⟨o.q, o.abort, fun i v => M.val true o.A i δ v, fun i v => M.val true o.B i δ v⟩

/-- The table of a row at W (`Row.tab`). -/
def rowTabW (M : SemWorld) (S : Row) (δ : LSub) : OpTabI (Idx M.Stk) :=
  fun n j => (Row.find S n j).map (entW M δ)

/-- An entry at Core's index read at Core's records. -/
def OpEntI.down (en : OpEntI (Idx Unit)) : OpEnt :=
  ⟨en.q, en.abort, fun ls v => en.PA (ls, ()) v, fun ls v => en.PB (ls, ()) v⟩

/-- A table at Core's index read at Core's records. -/
def OpTabI.down (T : OpTabI (Idx Unit)) : OpTab := fun n i => (T n i).map OpEntI.down

/-- A protocol table at Core's index read at Core's records. -/
def TableI.down (Tb : TableI (Idx Unit)) : Table := fun ls t Φ => Tb (ls, ()) t (fun i e => Φ i.1 e)


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun performE raiseE opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- **Core's relation as the interaction's world**: `coreB`, nothing held, R-T1 as the stop, and
Core's `contShare`.  Reducible, so that its index type is `Idx Unit` to every tactic. -/
@[reducible] def coreW : SemWorld where
  toBWorld := B.coreB (ℍ := ℍ)
  held _ := ([], [])
  Stop a b _ := (∀ p, p ∈ b.1 ↔ p ∈ a.1) ∧ (∀ x, x ∈ b.2.1 ↔ x ∈ a.2.1)
  share T en n i K Φ := contShare (OpTabI.down T) (OpEntI.down en) n i.1 K (fun ls t => Φ (ls, ()) t)

/-- `coreW`'s borrow world is `coreB`. -/
@[simp] theorem coreW_toBWorld : (coreW (ℍ := ℍ)).toBWorld = B.coreB (ℍ := ℍ) := rfl



end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun performE raiseE opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

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


end Targets

namespace Targets
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Steps Step1 Head Kont Alloc ARun Step1N performE raiseE opPayload cancelVal
  hndE hndVal kappa ccatchE)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

theorem wpGW_mono {M : SemWorld} {i : Idx M.Stk} {e : Expr} {Q Q' : Idx M.Stk → Expr → WProp}
    (hQ : ∀ i t ρ, Q i t ρ → Q' i t ρ) {ρ : WRes} (h : wpGW (ℍ := ℍ) M i e Q ρ) :
    wpGW (ℍ := ℍ) M i e Q' ρ := by
  intro ρf fρ ps h1 h2 h3 A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', i', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
    a12, a13⟩ := h ρf fρ ps h1 h2 h3 A k
  exact ⟨ρ', ρp, fρ', fρ'p, π, t, μ, μ', ps', i', a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11,
    a12, hQ _ _ _ a13⟩

/-- One pure step in front of a `wpGW` (`wpG_step` at W). -/
theorem wpGW_step {M : SemWorld} {e e' : Expr} (h : ∀ μ : Heap, Step1N (ℍ := ℍ) μ e μ e')
    (i : Idx M.Stk) (Q : Idx M.Stk → Expr → WProp) :
    Entails (wpGW (ℍ := ℍ) M i e' Q) (wpGW (ℍ := ℍ) M i e Q) := by
  intro ρ hw ρf fρ ps hf hc hF A k
  obtain ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', i', h₁, h₂, h₃, h₅, h₆, h₇, ⟨j, h₈⟩, h₉, hA, hB,
    hF', hS, hC⟩ := hw ρf fρ ps hf hc hF A k
  exact ⟨ρ', ρp, fρ', fρ'p, π, v, μ, μ', ps', i', h₁, h₂, h₃, h₅, h₆, h₇,
    ⟨j, BoCa.BoLo.ARun.cons (h μ) h₈⟩, h₉, hA, hB, hF', hS, hC⟩

theorem ewpW_fold {M : SemWorld} {Tb : TableI (Idx M.Stk)} (hTb : Tb.Mono)
    {Q : Idx M.Stk → Val → WProp} {i : Idx M.Stk} {e : Expr} {ρ : WRes}
    (h : wpGW (ℍ := ℍ) M i e (fun i' t ρ' => valPostI Q i' t ρ' ∨
      Tb i' t (fun i e => ewpW (ℍ := ℍ) M i e Tb Q) ρ') ρ) :
    ewpW (ℍ := ℍ) M i e Tb Q ρ := by
  intro P hP
  exact hP i e ρ (wpGW_mono (fun i' t ρ' hq => hq.imp id (hTb i' t _ P ρ'
    (fun _ _ _ h' => h' P hP))) h)

theorem ewpW_unfold {M : SemWorld} {Tb : TableI (Idx M.Stk)} (hTb : Tb.Mono)
    {Q : Idx M.Stk → Val → WProp} {i : Idx M.Stk} {e : Expr} {ρ : WRes}
    (h : ewpW (ℍ := ℍ) M i e Tb Q ρ) :
    wpGW (ℍ := ℍ) M i e (fun i' t ρ' => valPostI Q i' t ρ' ∨
      Tb i' t (fun i e => ewpW (ℍ := ℍ) M i e Tb Q) ρ') ρ :=
  h (fun i e ρ => wpGW (ℍ := ℍ) M i e (fun i' t ρ' => valPostI Q i' t ρ' ∨
      Tb i' t (fun i e => ewpW (ℍ := ℍ) M i e Tb Q) ρ') ρ)
    (fun _ _ _ h' => wpGW_mono (fun i' t ρ' hq => hq.imp id (hTb i' t _ _ ρ'
      (fun _ _ _ h'' => ewpW_fold hTb h''))) h')

/-- One pure step in front of an `ewpW` (`ewp_step` at W). -/
theorem ewpW_step {M : SemWorld} {Tb : TableI (Idx M.Stk)} (hTb : Tb.Mono) {e e' : Expr}
    (h : ∀ μ : Heap, Step1N (ℍ := ℍ) μ e μ e') (i : Idx M.Stk) (Q : Idx M.Stk → Val → WProp) :
    Entails (ewpW (ℍ := ℍ) M i e' Tb Q) (ewpW (ℍ := ℍ) M i e Tb Q) :=
  fun ρ h' => ewpW_fold hTb (wpGW_step h i _ ρ (ewpW_unfold hTb h'))

theorem tableI_down_mono {Tb : TableI (Idx Unit)} (h : Tb.Mono) : Table.Mono (TableI.down Tb) :=
  fun ls t _ _ ρ hΦ hp => h (ls, ()) t _ _ ρ (fun i e ρ hi => hΦ i.1 e ρ hi) hp

theorem tableI_down_abortive {Tb : TableI (Idx Unit)} (h : Tb.Abortive) :
    Table.Abortive (TableI.down Tb) :=
  fun ls t _ _ ρ hp => h (ls, ()) t _ _ ρ hp

/-- A table with no entry has no stop. -/
theorem opTabW_core_empty {T : OpTabI (Idx Unit)} (hT : ∀ n j, T n j = none) {ls : List SRec}
    {t : Expr} {Φ : List SRec → Expr → WProp} {ρ : WRes} :
    ¬ opTable (OpTabI.down T) ls t Φ ρ := by
  rintro (⟨K, n, j, v, en, h⟩ | ⟨K, n, j, v, en, h⟩) <;>
  · obtain ⟨⟨-, -, hT', -⟩, -⟩ := pure_sep_iff.mp h
    simp [OpTabI.down, hT n j] at hT'

end Targets

end
