/-!
# Unsafe — how an assertion composes with the rules of a judgment  (`docs/unsafe.md` §4)

A judgment is the least predicate closed under a rule set, and its Fundamental Property is the
statement that a semantic predicate `Sem` is closed under every rule (each rule's compatibility
lemma). This file states, at that level of abstraction, the forms an assertion can take and how
each behaves when a rule is added to the base:

* `LawOver R L Sem`: a kind-R assertion as `PinLaw` states it, the law rule `L`'s compatibility
  lemma at premises that are derivations of the extended judgment `R + L` (`PinStop`'s
  `CDerivesP` premise). Adding a rule to `R` strengthens it (`lawOver_strengthens`), and adding a
  rule that is itself sound can make it false (`sound_rule_breaks_law`).
* `Closed L Sem`: the law stated semantically, at every related premise. It implies `LawOver` at
  every base (`lawOver_of_closed`), and can be false where `LawOver` holds, at a related premise no
  derivation builds (`junk_refutes_semantic_law`).
* A table of sites `T`: the relation at each site, a rule with no premises. The Fundamental
  Property over `R + T` needs `T ⊆ Sem` and the base's compatibility lemmas, and that hypothesis
  does not mention the base (`fundamental_sites`, `fundamental_sites_add`). A law implies each site
  it licenses (`sites_of_law`).
* An invariant `I` below `Sem`: the law asserted as `Closed L I`, every base rule closed under
  `I`. Adding a rule costs its compatibility lemma at `I`; the assertion's text does not mention
  the base (`fundamental_inv`).

Standalone: no Mathlib, no import of the library.
-/

namespace Unsafe

/-- A rule set over judgment instances `α`, as a monotone operator: `step X a` holds when some
rule concludes `a` from premises in `X`. -/
structure Rules (α : Type) where
  step : (α → Prop) → α → Prop
  mono : ∀ {X Y : α → Prop}, (∀ a, X a → Y a) → ∀ a, step X a → step Y a

variable {α : Type}

/-- The judgment the rules generate: the least predicate closed under them. -/
def Derives (R : Rules α) (a : α) : Prop :=
  ∀ X : α → Prop, (∀ b, R.step X b → X b) → X a

/-- `P` is closed under `R`: every rule of `R` has its compatibility lemma at `P`. -/
def Closed (R : Rules α) (P : α → Prop) : Prop := ∀ a, R.step P a → P a

theorem Derives.ind {R : Rules α} {P : α → Prop} (h : Closed R P) {a : α} (d : Derives R a) :
    P a := d P h

theorem Derives.intro {R : Rules α} {a : α} (h : R.step (Derives R) a) : Derives R a :=
  fun X hX => hX a (R.mono (fun _ d => d X hX) a h)

/-- Two rule sets side by side. -/
def Rules.add (R S : Rules α) : Rules α where
  step X a := R.step X a ∨ S.step X a
  mono h a := Or.imp (R.mono h a) (S.mono h a)

/-- A table of sites: one rule with no premise per site. -/
def Rules.sites (T : α → Prop) : Rules α where
  step _ a := T a
  mono _ _ h := h

/-- Every rule of `R` is a rule of `S`. -/
def Rules.Le (R S : Rules α) : Prop := ∀ X a, R.step X a → S.step X a

theorem Derives.mono {R S : Rules α} (h : R.Le S) {a : α} (d : Derives R a) : Derives S a :=
  d.ind (fun b hb => Derives.intro (h _ b hb))

theorem closed_add {R S : Rules α} {P : α → Prop} (hR : Closed R P) (hS : Closed S P) :
    Closed (R.add S) P :=
  fun a h => h.elim (hR a) (hS a)

/-- The Fundamental Property: a predicate closed under the rules holds at every derivation. -/
theorem fundamental {R : Rules α} {Sem : α → Prop} (hc : Closed R Sem) :
    ∀ a, Derives R a → Sem a :=
  fun _ d => d.ind hc

/-! ### Kind R stated over the extended judgment (`PinLaw`'s form) -/

/-- The law rule `L`'s compatibility lemma at premises that are derivations of `R + L`. -/
def LawOver (R L : Rules α) (Sem : α → Prop) : Prop :=
  ∀ a, L.step (Derives (R.add L)) a → Sem a

/-- `fundamentalC_pin`'s shape: the base's compatibility lemmas and the law give the
Fundamental Property of the extended judgment. -/
theorem fundamental_law {R L : Rules α} {Sem : α → Prop} (hc : Closed R Sem)
    (h : LawOver R L Sem) : ∀ a, Derives (R.add L) a → Sem a := by
  intro a d
  have hP : Closed (R.add L) (fun b => Derives (R.add L) b ∧ Sem b) := by
    intro b hb
    rcases hb with hb | hb
    · exact ⟨Derives.intro (Or.inl (R.mono (fun _ p => p.1) b hb)),
        hc b (R.mono (fun _ p => p.2) b hb)⟩
    · have hd := L.mono (fun _ p => p.1) b hb
      exact ⟨Derives.intro (Or.inr hd), h b hd⟩
  exact (d.ind hP).2

/-- **Adding a rule to the base strengthens the law.** `LawOver (R + r) L Sem` implies
`LawOver R L Sem`, and the assertion's text, `LawOver _ L Sem`, is the same. -/
theorem lawOver_strengthens {R r L : Rules α} {Sem : α → Prop}
    (h : LawOver (R.add r) L Sem) : LawOver R L Sem := by
  intro a hs
  have hle : (R.add L).Le ((R.add r).add L) := by
    intro X b hb
    rcases hb with hb | hb
    · exact Or.inl (Or.inl hb)
    · exact Or.inr hb
  exact h a (L.mono (fun _ d => Derives.mono hle d) a hs)

/-- The semantic law implies the law over every base whose rules are sound. -/
theorem lawOver_of_closed {R L : Rules α} {Sem : α → Prop} (hR : Closed R Sem)
    (hL : Closed L Sem) : LawOver R L Sem :=
  fun a hs => hL a (L.mono (fun b d => fundamental (closed_add hR hL) b d) a hs)

/-! ### Kind T, and kind R per site -/

/-- **Sites.** The base's compatibility lemmas and the relation at each site give the
Fundamental Property of the judgment extended by the table. -/
theorem fundamental_sites {R : Rules α} {Sem T : α → Prop} (hc : Closed R Sem)
    (hT : ∀ a, T a → Sem a) : ∀ a, Derives (R.add (Rules.sites T)) a → Sem a :=
  fundamental (closed_add hc hT)

/-- **Adding a rule leaves the sites' hypothesis as it was**: a new base rule needs its own
compatibility lemma, and `hT` is passed unchanged. -/
theorem fundamental_sites_add {R r : Rules α} {Sem T : α → Prop} (hc : Closed R Sem)
    (hr : Closed r Sem) (hT : ∀ a, T a → Sem a) :
    ∀ a, Derives ((R.add r).add (Rules.sites T)) a → Sem a :=
  fundamental_sites (closed_add hc hr) hT

/-- **A law implies every site it licenses**: a site whose premises are derivations of the
extended judgment is in the relation. -/
theorem sites_of_law {R L : Rules α} {Sem T : α → Prop}
    (hT : ∀ a, T a → L.step (Derives (R.add L)) a) (h : LawOver R L Sem) : ∀ a, T a → Sem a :=
  fun a ha => h a (hT a ha)

/-! ### Kind R over an invariant -/

/-- **An invariant.** If every base rule and the law rule are closed under `I`, and `I` is below
the relation, the extended judgment is sound. Adding a rule `r` costs `Closed r I`. -/
theorem fundamental_inv {R L : Rules α} {Sem I : α → Prop} (hR : Closed R I) (hL : Closed L I)
    (hI : ∀ a, I a → Sem a) : ∀ a, Derives (R.add L) a → Sem a :=
  fun a d => hI a (fundamental (closed_add hR hL) a d)

/-! ### Two witnesses

Judgment instances are numbers. The base `R0` concludes `0`; the law rule `Lten` concludes
`n + 10` from `n`; the rule `r1` concludes `1`. The relation `Sem0` holds everywhere but at `11`
and `15`. -/

/-- The base: one axiom, `0`. -/
def R0 : Rules Nat := Rules.sites (· = 0)

/-- A rule with no premise concluding `1`. -/
def r1 : Rules Nat := Rules.sites (· = 1)

/-- The law rule: from `n`, conclude `n + 10`. -/
def Lten : Rules Nat where
  step X a := ∃ n, X n ∧ a = n + 10
  mono h _ := fun ⟨n, hn, e⟩ => ⟨n, h n hn, e⟩

/-- The relation: every instance but `11` and `15`. -/
def Sem0 (a : Nat) : Prop := a ≠ 11 ∧ a ≠ 15

theorem derives_R0_Lten_mod {a : Nat} (d : Derives (R0.add Lten) a) : a % 10 = 0 := by
  refine d.ind (P := fun b => b % 10 = 0) ?_
  intro b hb
  rcases hb with hb | ⟨n, hn, rfl⟩
  · simp only [R0, Rules.sites] at hb; subst hb; rfl
  · omega

theorem lawOver_R0 : LawOver R0 Lten Sem0 := by
  rintro a ⟨n, hn, rfl⟩
  have := derives_R0_Lten_mod hn
  constructor <;> omega

/-- **A related premise no derivation builds refutes the semantic law** while the law over the
judgment holds: `5` is related, and `15` is not. -/
theorem junk_refutes_semantic_law :
    Closed R0 Sem0 ∧ LawOver R0 Lten Sem0 ∧ ¬ Closed Lten Sem0 := by
  refine ⟨?_, lawOver_R0, ?_⟩
  · intro a ha
    simp only [R0, Rules.sites] at ha
    subst ha
    exact ⟨by decide, by decide⟩
  · intro h
    exact (h 15 ⟨5, ⟨by decide, by decide⟩, rfl⟩).2 rfl

/-- **A sound rule added to the base makes the law false.** `r1` has its compatibility lemma at
`Sem0`, the law holds over `R0`, and it fails over `R0 + r1`: `1` is now derived, and `11` is
not related. So `Closed r Sem` is not an obligation that keeps `LawOver` true. -/
theorem sound_rule_breaks_law :
    Closed r1 Sem0 ∧ LawOver R0 Lten Sem0 ∧ ¬ LawOver (R0.add r1) Lten Sem0 := by
  refine ⟨?_, lawOver_R0, ?_⟩
  · intro a ha
    simp only [r1, Rules.sites] at ha
    subst ha
    exact ⟨by decide, by decide⟩
  · intro h
    have d1 : Derives ((R0.add r1).add Lten) 1 :=
      Derives.intro (Or.inl (Or.inr (show (1 : Nat) = 1 from rfl)))
    exact (h 11 ⟨1, d1, rfl⟩).1 rfl

end Unsafe
