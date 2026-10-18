import Core.World
import Core.Types

/-!
# Core — the effectful `wp`: definitions  `[spec §19]`

`wpG` (`wpTS` ending at any term), protocol tables and `ewpTS`, and §19's concrete tables over
`perform`/`raise`: `opTable` of an operation table, and `cancelTab`, the table of a cancel run.
The relation (`Core/Relation.lean`) reads `F_Σ A` through them; their lemmas are
`Core/EffWp.lean`'s.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.BoLo (Heap Steps Step1 Head Kont eLoad eStore Alloc ARun Step1N performE raiseE
  opPayload cancelVal)
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-- `wpTS` with its run ending at an arbitrary term, and the postcondition over that term.
Every other conjunct is `wpTS`'s verbatim.  `[spec §19]` -/
def wpG (ls : List SRec) (e : Expr) (Q : List SRec → Expr → WProp) : WProp := fun ρ =>
  ∀ (ρf fρ : WRes) (ps : List FrameRec), ResU.Hash ρf ρ → ResU.CompS ρf ρ fρ →
    TW fρ ps (rsOf ls) → Tagged fρ ps ls → ∀ (A : Alloc) (k : Nat),
    ∃ (ρ' ρp fρ' fρ'p π : WRes) (v : Expr) (μ μ' : Heap) (ps' : List FrameRec)
      (ls' : List SRec),
      ResU.Hash ρ' ρf ∧
      ResU.CompS ρf ρ' fρ' ∧ ResU.Hash ρp fρ' ∧
      ResU.Lower fρ μ ∧
      ResU.CompS fρ' ρp fρ'p ∧ ResU.Lower fρ'p μ' ∧
      (∃ k', ARun A k μ e k' μ' v) ∧
      ResU.CompS ρ' ρp π ∧ ResU.UpdV ρ π ∧
      NoOwn ρp ∧
      TW fρ'p ps' (rsOf ls') ∧ Tagged fρ'p ps' ls' ∧
      (∀ p, p ∈ ps' ↔ p ∈ ps) ∧ (∀ x, x ∈ ls' ↔ x ∈ ls) ∧ Q ls' v ρ'

/-- The postcondition over terms that admits only values. -/
def valPost (Q : List SRec → Val → WProp) : List SRec → Expr → WProp :=
  fun ls t ρ => ∃ v : Val, t = .val v ∧ Q ls v ρ


/-- A protocol table: which stopped terms are allowed, and what they owe their continuations
(`SPEC.md` §19).  `Π ls t Φ` reads: the configuration stopped at `t`, over the list `ls`, is
allowed, with every continuation it owes in `Φ`.  `[spec §19]` -/
abbrev Table := List SRec → Expr → (List SRec → Expr → WProp) → WProp

/-- A table is monotone in the continuations it owes. -/
def Table.Mono (Tb : Table) : Prop :=
  ∀ ls t (Φ Φ' : List SRec → Expr → WProp) ρ, (∀ ls e ρ, Φ ls e ρ → Φ' ls e ρ) →
    Tb ls t Φ ρ → Tb ls t Φ' ρ

/-- A table is abortive when it owes no continuation: its stops are final. -/
def Table.Abortive (Tb : Table) : Prop :=
  ∀ ls t (Φ Φ' : List SRec → Expr → WProp) ρ, Tb ls t Φ ρ → Tb ls t Φ' ρ

theorem Table.Abortive.mono {Tb : Table} (h : Tb.Abortive) : Tb.Mono :=
  fun ls t Φ Φ' ρ _ hp => h ls t Φ Φ' ρ hp

/-- The empty table: nothing may stop. -/
def Table.bot : Table := fun _ _ _ _ => False

/-- Two tables, either of which may stop the run. -/
def orTab (A B : Table) : Table := fun ls t Φ => BoLo.or (A ls t Φ) (B ls t Φ)

/-- A table that owes nothing to the run's least fixed point: its stops do not read the
continuations they are given. -/
def Table.Const (Px : Table) : Prop := ∀ ls t Φ Φ' ρ, Px ls t Φ ρ → Px ls t Φ' ρ

/-- One unfolding: run to a value in `Q`, or to a stop `Π` allows, owing `P`. -/
def ewpStep (Tb : Table) (Q : List SRec → Val → WProp) (P : List SRec → Expr → WProp) :
    List SRec → Expr → WProp :=
  fun ls e => wpG ls e (fun ls' t ρ => valPost Q ls' t ρ ∨ Tb ls' t P ρ)

/-- `ewpTS ls e Π Q`: the least fixed point of `ewpStep`, written in `Prop`.  `[spec §19]` -/
def ewpTS (ls : List SRec) (e : Expr) (Tb : Table) (Q : List SRec → Val → WProp) : WProp :=
  fun ρ => ∀ P : List SRec → Expr → WProp,
    (∀ ls e ρ, ewpStep Tb Q P ls e ρ → P ls e ρ) → P ls e ρ

theorem hasHnd_comp (n : UInt32) : ∀ (K K' : Kont),
    (K.comp K').HasHnd n = (K.HasHnd n || K'.HasHnd n) := by
  intro K K'
  induction K with
  | hole => simp [Kont.comp, Kont.HasHnd]
  | appR f K ih => simp only [Kont.comp, Kont.HasHnd, ih, Bool.or_assoc]
  | _ => simp_all [Kont.comp, Kont.HasHnd]

theorem catches_comp (n : UInt32) : ∀ (K K' : Kont),
    (K.comp K').Catches n = (K.Catches n || K'.Catches n) := by
  intro K K'
  induction K with
  | hole => simp [Kont.comp, Kont.Catches]
  | appR f K ih => simp only [Kont.comp, Kont.Catches, ih, Bool.or_assoc]
  | _ => simp_all [Kont.comp, Kont.Catches]

/-! ### The dead region  `[spec §19]` -/

theorem dead_comp : ∀ (K K' : Kont), (K.comp K').dead = K.dead.comp K'.dead := by
  intro K K'
  induction K with
  | hole => rfl
  | appR f K ih =>
      simp only [Kont.comp, Kont.dead, ih]
      split <;> rfl
  | _ => simp_all [Kont.comp, Kont.dead]

/-- A dead region holds no handler frame. -/
theorem hasHnd_dead (n : UInt32) : ∀ K : Kont, K.dead.HasHnd n = false := by
  intro K
  induction K with
  | hole => rfl
  | appR f K ih =>
      simp only [Kont.dead]
      split
      · exact ih
      · rename_i hf
        simp only [Kont.HasHnd, ih, Bool.or_false]
        split
        · rename_i m r
          simp [Kont.DeadFrame] at hf
        · rfl
  | _ => simp_all [Kont.dead, Kont.HasHnd]

/-- A dead region catches only at its finaliser frames, `ubind` and `cfin`, which catch every
name: whether it catches does not depend on the name. -/
theorem catches_dead (n m : UInt32) : ∀ K : Kont, K.dead.Catches n = K.dead.Catches m := by
  intro K
  induction K with
  | hole => rfl
  | appR f K ih =>
      simp only [Kont.dead]
      split
      · exact ih
      · rename_i hf
        simp only [Kont.Catches, ih]
        congr 1
        split <;> simp_all [Kont.DeadFrame]
  | _ => simp_all [Kont.dead, Kont.Catches]

/-- A region whose frames catch nothing and hold no handler is its own dead region. -/
theorem dead_plain : ∀ K : Kont, (∀ n, K.HasHnd n = false) → K.Catches 0 = false → K.dead = K := by
  intro K
  induction K with
  | hole => intro _ _; rfl
  | appR f K ih =>
      intro hH hC
      have hH' : ∀ n, K.HasHnd n = false := fun n => by
        have := hH n; simp only [Kont.HasHnd, Bool.or_eq_false_iff] at this; exact this.2
      have hC' : K.Catches 0 = false := by
        simp only [Kont.Catches, Bool.or_eq_false_iff] at hC; exact hC.2
      simp only [Kont.dead, ih hH' hC']
      split
      · rename_i hf
        exfalso
        unfold Kont.DeadFrame at hf
        split at hf
        · rename_i m r
          have := hH m
          simp [Kont.HasHnd] at this
        · simp [Kont.Catches] at hC
        · cases hf
      · rfl
  | _ =>
      intro hH hC
      simp_all [Kont.dead, Kont.HasHnd, Kont.Catches]

/-! ### Operation tables  `[spec §19]` -/

/-- An operation's entry: its continuation's qualifier, whether it is abortive (answer `0` at a
qualifier with weakening), the relations of its argument and answer types, and its cancel
obligation: `none` at the cancel row `⊤`, otherwise the run a cancel of a continuation captured
at the operation owes from the dead region's start (`cancelObl` of the cancel row's table).
`[spec §19, §27]` -/
structure OpEnt where
  q : Qual
  abort : Bool
  PA : List SRec → Val → WProp
  PB : List SRec → Val → WProp
  fin : Option (List SRec → Expr → WProp)

/-- An operation table: the entry of the operation `i` of the name `n`, if the row has it. -/
abbrev OpTab := UInt32 → UInt32 → Option OpEnt

/-- The empty row. -/
def OpTab.empty : OpTab := fun _ _ => none

/-- The row extended by one operation. -/
def OpTab.ext (n i : UInt32) (en : OpEnt) (T : OpTab) : OpTab :=
  fun n' i' => if n' = n ∧ i' = i then some en else T n' i'

/-- The error a cancel carries is admissible at the canceller: none, or an abortive operation of
the table, at its argument relation. -/
def errOk (T : OpTab) (ls : List SRec) : Option Val → WProp
  | none => emp
  | some E => ex fun (m : UInt32) => ex fun (j : UInt32) => ex fun (w : Val) =>
      ex fun (en : OpEnt) =>
        ⌜E = opPayload m j w ∧ T m j = some en ∧ en.abort = true⌝ ⋆
          fun ρ => en.PA ls w ρ ∧ NoOwn ρ

/-- What cancelling the continuation `K` of an operation whose entry is `en` owes: the dead region
`K†` run from the cancel's start at the entry's cancel obligation; nothing at the cancel row `⊤`
(`en.fin = none`), whose continuation cannot be cancelled.  `[spec §19, §27]` -/
def cancelOK (en : OpEnt) (ls : List SRec) (K : Kont) : WProp := fun ρ =>
  ∀ P, en.fin = some P → P ls (K.dead.plug (raiseE (.val (cancelVal none)))) ρ

/-- The continuation's share at a stopped operation: `∅` at `unr`; at every extension of the
list, resumed at every answer in `PB`; and, with weakening, cancelled (`cancelOK`).
`[spec §19, §27]` -/
def contShare (en : OpEnt) (ls : List SRec) (K : Kont) (Φ : List SRec → Expr → WProp) : WProp :=
  fun ρ =>
    (en.q = .unr → ρ = PMap.empty) ∧
    ∀ ls', Ext ls ls' ρ →
      (∀ w : Val, (en.PB ls' w ─⋆ Φ ls' (K.plug (.val w))) ρ) ∧
      (en.q ≠ .lin → cancelOK en ls' K ρ)

/-- A stop at a non-abortive operation of `T`, `perform (n, (i, v))` under a context free of `n`:
the argument, and the continuation's share.  `[spec §19]` -/
def performStop (T : OpTab) : Table := fun ls t Φ =>
  ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
    ex fun (en : OpEnt) =>
      ⌜t = K.plug (performE (.val (opPayload n i v))) ∧ K.HasHnd n = false ∧
        T n i = some en ∧ en.abort = false⌝ ⋆ (en.PA ls v ⋆ contShare en ls K Φ)

/-- The table of a cancel run whose kept errors and performed operations are `T`'s: the cancel's
end, having unwound every frame that catches it, with an admissible error and nothing owned left
behind; or an operation of `T` a running finaliser performs, which passes the dead region to a
live handler, owing its continuation's share.  `[spec §19, §27]` -/
def cancelTab (T : OpTab) : Table := fun ls t Φ =>
  BoLo.or
    (ex fun (K : Kont) => ex fun (err : Option Val) =>
      ⌜t = K.plug (raiseE (.val (cancelVal err))) ∧ K.Catches 0 = false⌝ ⋆
        (errOk T ls err ⋆ fun ρ => NoOwn ρ))
    (performStop T ls t Φ)

/-- The cancel obligation of a cancel row's table `T`: the cancel run at `cancelTab T`.
`[spec §27]` -/
def cancelObl (T : OpTab) : List SRec → Expr → WProp :=
  fun ls e => ewpTS ls e (cancelTab T) (fun _ _ _ => False)

/-- The cancel run of the continuation `K` at the empty cancel row: the dead region `K†` run to
the cancel's end, keeping no error and performing nothing.  `[spec §19]` -/
def cancelOwed (ls : List SRec) (K : Kont) : WProp :=
  cancelObl OpTab.empty ls (K.dead.plug (raiseE (.val (cancelVal none))))

/-- The protocol table of an operation table.  `[spec §19]`
* a non-abortive `perform (n, (i, v))` under a context free of `n`: the argument, and the
  continuation's share (`performStop`);
* an abortive `raise (n, (i, v))` under a context catching nothing of `n`: the argument, which
  holds nothing owned (an abandoned error is dropped), and the abandoned continuation, which holds
  nothing owned either. -/
def opTable (T : OpTab) : Table := fun ls t Φ =>
  BoLo.or (performStop T ls t Φ)
    (ex fun (K : Kont) => ex fun (n : UInt32) => ex fun (i : UInt32) => ex fun (v : Val) =>
      ex fun (en : OpEnt) =>
        ⌜t = K.plug (raiseE (.val (opPayload n i v))) ∧ K.Catches n = false ∧
          T n i = some en ∧ en.abort = true⌝ ⋆
          ((fun ρ => en.PA ls v ρ ∧ NoOwn ρ) ⋆ fun ρ => NoOwn ρ))

end BoCa.Fig16.LogRel.Core
