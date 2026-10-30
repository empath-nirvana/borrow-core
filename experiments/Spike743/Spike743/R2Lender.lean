import GhostEnd.ImmLend

/-!
# Spike743 — a lender-side lemma for R2 (U8): how far GhostEnd's `ewpTS_I_frameR` reaches

R2 (`lendLoopR`) lends `ℓ` as `Imm 'x A` at every observation of a loop, at a fresh `'x`, to a
step whose state may hold views of `ℓ` from earlier observations. GhostEnd's `ewpTS_I_frameR`
is 6.64 at a resuming table: an `imm` lend of `ℓ` over a callback that is re-lendable
(`RelendI`, the least fixed point of `relendIF`), with the post `Q` read at the callback's return
**after** the lend has ended and the owner is back (`box α (ptoOwn ─⋆ … valPost Q)`).

Applied per observation, the post of an observation that goes on is the next observation's
obligation: the state `s'` it answers must again make the next observation's callback
re-lendable. Across observations this is a greatest fixed point (`R2Inv`): a loop is codata.

* `r2_next_obs`, `r2_close_obs` (PROVED): each observation of a loop whose state satisfies
  `R2Inv`, run under the owner, is an `ewpTS` whose post is again `R2Inv` (or the loop's answer):
  `ewpTS_I_frameR` at the observation, then the post weakened from the post-fixed point to
  `R2Inv`. The lender's half of R2 at one observation needs nothing new.
* Not here, and not stated in Lean: (1) the lender-side lemma at Core's relation, which needs
  an `unfold` related at a state *predicate*: Core's `unfold` is related at a state *type*
  (`envS S δ`, `candN … S δ` in `Core/Nu.lean`, the state read by `vC S`), and R2's state is
  related by `R2Inv`. The ν candidate takes the state's predicate as a `TEnt`, so this is a
  restatement of `candN` at a predicate. (2) The borrower side, `R2Inv` of the first state from
  the steps' `CDerivesP` derivations. This is Law 2's `relendOfTyped'` at the context
  `Imm 'x A ⊗ S` and with the state a *value* from an earlier run, not a typed term: the views it
  holds are bare locations after the ghost end, and each must be re-lent at the fresh lifetime
  (`relent_copies`). Law 2 has no such case (its context is `Mut 'x T` alone), and when `S` holds
  a `U` the route meets GhostEnd's own `thunkF_RL_fails_below_at` (`R2`'s state has no `NoThunkT`
  premise, unlike `B` and `R`).
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace Spike743
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Core GhostEnd
open BoCa.Lifetime (LSub LifeCtx LifeVar)

variable (Tb : Table) (l : BoCa.Loc) (v : Val) (A : VTy) (δ : LSub)

/-- The post of a `next` observation: the loop finishes with `QB` of its output, or goes on with
a state satisfying `X`. -/
def nextPost (QB X : List SRec → Val → WProp) : List SRec → Val → WProp := fun ls t ρ =>
  (∃ b : Val, t.1 = .inj₁ b.1 ∧ QB ls b ρ) ∨ (∃ s : Val, t.1 = .inj₂ s.1 ∧ X ls s ρ)

/-- One step of R2's invariant: at the state `s`, the `next` callback `eN s` and the `close`
callback `eK s` (each run with the view `ℓ`) are re-lendable for the `imm` lend of `ℓ`, the next
state again in `X`. -/
def R2F (eN eK : Val → Expr) (QB QR : List SRec → Val → WProp)
    (X : List SRec → Val → WProp) : List SRec → Val → WProp := fun ls s ρ =>
  RelendI Tb l v A δ (nextPost QB X) ls (eN s) ρ ∧ RelendI Tb l v A δ QR ls (eK s) ρ

/-- **R2's state invariant**: the greatest fixed point of `R2F`. -/
def R2Inv (eN eK : Val → Expr) (QB QR : List SRec → Val → WProp) :
    List SRec → Val → WProp := fun ls s ρ =>
  ∃ X : List SRec → Val → WProp,
    (∀ ls s ρ, X ls s ρ → R2F Tb l v A δ eN eK QB QR X ls s ρ) ∧ X ls s ρ

theorem nextPost_mono {QB X Y : List SRec → Val → WProp} (h : ∀ ls s ρ, X ls s ρ → Y ls s ρ)
    {ls : List SRec} {t : Val} {ρ : WRes} (hp : nextPost QB X ls t ρ) : nextPost QB Y ls t ρ := by
  rcases hp with ⟨b, hb, hq⟩ | ⟨s, hs, hx⟩
  · exact Or.inl ⟨b, hb, hq⟩
  · exact Or.inr ⟨s, hs, h _ _ _ hx⟩

/-- `relendIF` is monotone in its post. -/
theorem relendIF_mono_Q {Q Q' : List SRec → Val → WProp} (hQ : ∀ ls w ρ, Q ls w ρ → Q' ls w ρ)
    {X : List SRec → Expr → WProp} {ls : List SRec} {e : Expr} :
    Entails (relendIF Tb l v A δ Q X ls e) (relendIF Tb l v A δ Q' X ls e) := by
  rintro ρ ⟨γ, hγ⟩
  refine ⟨γ, fun α hα => ⟨fun ls' hadd hrec => ?_, (hγ α hα).2⟩⟩
  refine wand_mono_right (fun _ hw => wpG_mono (fun ls'' t σ hb => ?_) hw) ρ
    ((hγ α hα).1 ls' hadd hrec)
  refine ⟨fun ρa ρb ha hcab ρc ρd hv hccd => ?_, hb.2⟩
  rcases hb.1 ρa ρb ha hcab ρc ρd hv hccd with ⟨w, hw, hq⟩ | hq
  · exact Or.inl ⟨w, hw, hQ _ _ _ hq⟩
  · exact Or.inr hq

/-- `RelendI` is monotone in its post: by induction on the least fixed point. -/
theorem relendI_mono_Q (hTb : Tb.Mono) {Q Q' : List SRec → Val → WProp}
    (hQ : ∀ ls w ρ, Q ls w ρ → Q' ls w ρ) {ls : List SRec} {e : Expr} {ρ : WRes}
    (h : RelendI Tb l v A δ Q ls e ρ) : RelendI Tb l v A δ Q' ls e ρ :=
  h (fun ls e ρ => RelendI Tb l v A δ Q' ls e ρ) fun _ _ _ hF =>
    relendI_fold hTb (relendIF_mono_Q Tb l v A δ hQ _ hF)

/-- **The lender's half of R2 at a `next` observation** (`ewpTS_I_frameR` per observation): the
owner and a state in `R2Inv` give the observation's `ewpTS`, whose post is again `R2Inv` when the
loop goes on. `hInv`: `R2Inv` is carried along `Ext`, 6.64's `hQ` (not derived here). -/
theorem r2_next_obs (hTb : Tb.Mono)
    (hTL : ∀ ls₁ ls₂ t Φ ρ, Ext ls₁ ls₂ ρ → Tb ls₁ t Φ ρ → Tb ls₂ t Φ ρ)
    (hadm : AdmWf A δ) (eN eK : Val → Expr) (QB QR : List SRec → Val → WProp)
    (hQB : ∀ ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → QB ls₁ w ρ → QB ls₂ w ρ)
    (hInv : ∀ ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ →
      R2Inv Tb l v A δ eN eK QB QR ls₁ w ρ → R2Inv Tb l v A δ eN eK QB QR ls₂ w ρ)
    (ls : List SRec) (s : Val) :
    Entails (ownerI l v A δ ls ⋆ R2Inv Tb l v A δ eN eK QB QR ls s)
      (ewpTS ls (eN s) Tb (nextPost QB (R2Inv Tb l v A δ eN eK QB QR))) := by
  rintro ρ ⟨ρo, ρi, hc, ho, X, hX, hx⟩
  have hXI : ∀ ls s ρ, X ls s ρ → R2Inv Tb l v A δ eN eK QB QR ls s ρ :=
    fun ls s ρ h => ⟨X, hX, h⟩
  have hR : RelendI Tb l v A δ (nextPost QB (R2Inv Tb l v A δ eN eK QB QR)) ls (eN s) ρi :=
    relendI_mono_Q Tb l v A δ hTb (fun _ _ _ hp => nextPost_mono hXI hp) (hX _ _ _ hx).1
  exact ewpTS_I_frameR Tb hTb hTL l v A δ hadm _
    (fun ls₁ ls₂ w ρ he hp => by
      rcases hp with ⟨b, hb, hq⟩ | ⟨s', hs, hx'⟩
      · exact Or.inl ⟨b, hb, hQB _ _ _ _ he hq⟩
      · exact Or.inr ⟨s', hs, hInv _ _ _ _ he hx'⟩)
    ls (eN s) ρ ⟨ρo, ρi, hc, ho, hR⟩

/-- **The lender's half of R2 at a `close` observation**: as `r2_next_obs`, its post the loop's
answer. -/
theorem r2_close_obs (hTb : Tb.Mono)
    (hTL : ∀ ls₁ ls₂ t Φ ρ, Ext ls₁ ls₂ ρ → Tb ls₁ t Φ ρ → Tb ls₂ t Φ ρ)
    (hadm : AdmWf A δ) (eN eK : Val → Expr) (QB QR : List SRec → Val → WProp)
    (hQR : ∀ ls₁ ls₂ w ρ, Ext ls₁ ls₂ ρ → QR ls₁ w ρ → QR ls₂ w ρ)
    (ls : List SRec) (s : Val) :
    Entails (ownerI l v A δ ls ⋆ R2Inv Tb l v A δ eN eK QB QR ls s) (ewpTS ls (eK s) Tb QR) := by
  rintro ρ ⟨ρo, ρi, hc, ho, X, hX, hx⟩
  exact ewpTS_I_frameR Tb hTb hTL l v A δ hadm QR hQR ls (eK s) ρ
    ⟨ρo, ρi, hc, ho, (hX _ _ _ hx).2⟩

end Spike743

end
