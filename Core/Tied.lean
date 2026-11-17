import Core.Fundamental

/-!
# Core — decision R: a derivation tied to its program's effect context  `[spec §19]`

An **effect context** `Ξ` gives each operation name its signature: the `i`-th operation of the
name `n` is `(Ξ n)[i] = (q, A, B)`.  A row is **tied** to `Ξ` (`RowAt`) when every operation it
finds is of a nonzero name with at most `2³²` operations, at the signature `Ξ` gives it.

**`CDerivesAt Ξ`** is `CDerives` with the premise `RowAt Ξ` at the three rules that read an
operation's signature off a row: `[perform]` and `[raise]` (the row the operation is found in) and
`[handle]` (the handled row `(n)↑E ⊙ Σ`, whose qualifiers are the handler value's tags, §25).
An operation's argument and answer are the context's up to α (`OpSig.AtEntry`, §3).
Every other rule is `CDerives`'s verbatim, `[then]` with its finaliser's row and the cancel rows of
§27 among them; the tie reads no cancel row (`rowAt_ofEff_fs`).  So a name has one signature across
a derivation: every instance of a handler site has one protocol (§19 *Names*).

* `CDerivesAt.toCDerives`: a tied derivation is one of `CDerives`, so `fundamentalC` and the
  adequacy theorems hold of it.
* `CDerivesAt.ofEffFree`: a derivation of a term holding no `perform`, `raise` or `hnd`
  (`Expr.effFree`) is tied at every effect context.
* `CDerivesAt.effThenA`, `CDerivesAt.effHandle`: `CDerives.effThenA` and `CDerives.effHandle`,
  tied.
* At a handler the tie makes its signature `E` a prefix of `Ξ n` up to α (`sig_prefix_of_rowAt`), so the
  handler value's tags are a prefix of `Ξ`'s qualifiers of `n` (`hndTags_of_rowAt`).
* `SigsAt Ξ S`: every entry of the list `S` is at `Ξ`'s signature; it ties every row whose
  entries are among `S`'s (`rowAt_of_sigsAt`).
* `EffCtx.NoUnrExn`: no operation of `Ξ` is unrestricted and answers `0`.  An abortive operation
  is cancellable (decision 63's restriction, §18); in a row tied to such a context an unrestricted
  operation resumes (`abort_false_of_rowAt`).
-/

namespace BoCa.Fig16.LogRel.Core
open BoCa BoCa.Fig16 BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)

/-! ### Effect contexts and tied rows -/

theorem OpSig.AtEntry.self (o : OpSig) : o.AtEntry (o.q, o.A, o.B) :=
  ⟨rfl, VTy.alphaB_refl _, VTy.alphaB_refl _⟩

/-- A row tied to an effect context that gives `Div`'s name no operation does not hold `Div`. -/
theorem Row.divB_of_rowAt {Ξ : EffCtx} {S : Row} (hAt : RowAt Ξ S) (hΞ : Ξ divEff = []) :
    Row.divB S = false :=
  Row.divB_false_of_find fun o hf => by
    have := (hAt _ _ o hf).2.2
    rw [hΞ] at this
    simp at this

/-- The unwinding form of `withbor` (1) with its finaliser at the pure row: `withbor1UD` at
`Σ_D = ∅`, `Σ_M = Σ`.  `[spec §19, §72]` -/
theorem CDerivesAt.withbor1U {Ξ : EffCtx} {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ)
    (hx : Δ.find? x = none) (hsc₁ : VScoped Δ A) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B)
    (hS : S.Unwind x) (hd : CDerivesAt Ξ Δ Γ d (.val (.lolli (.ref A) .unit))) :
    CDerivesAt Ξ Δ Γ (withborUE d) (.val (withbor1UTy x Δ.meetOfDom A B S)) :=
  .withbor1UD (SD := []) x hΓ hx hsc₁ hfree₁ hfree₂ hS (RowLe.refl S) (RowLe.nil S) hS.divB
    (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil) hd

/-- The unwinding form of `withbor` (2) with its finaliser at the pure row: `withbor2UD` at
`Σ_D = ∅`, `Σ_M = Σ`.  `[spec §19, §23]` -/
theorem CDerivesAt.withbor2U {Ξ : EffCtx} {Δ Γ A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ)
    (hx : Δ.find? x = none) (hside : ∃ b, Δ.Defines b ∧ VOutlivesLe Δ b A)
    (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
    (hd : CDerivesAt Ξ Δ Γ d (.val (.lolli (.ref A) .unit))) :
    CDerivesAt Ξ Δ Γ (withborUE d) (.val (withbor2UTy x Δ.meetOfDom A B S)) :=
  .withbor2UD (SD := []) x hΓ hx hside hfree₁ hfree₂ hS (RowLe.refl S) (RowLe.nil S) hS.divB
    (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil) hd

/-- The unwinding form of `withbor` (3) with its finaliser at the pure row: `withbor3UD` at
`Σ_D = ∅`, `Σ_M = Σ`.  `[spec §19]` -/
theorem CDerivesAt.withbor3U {Ξ : EffCtx} {Δ Γ a A B d} {S : Row} (x : LifeVar) (hΓ : Ctx.DeadP Γ)
    (hx : Δ.find? x = none) (hfree₁ : ¬ VFree x A) (hfree₂ : ¬ VFree x B) (hS : S.Unwind x)
    (hd : CDerivesAt Ξ Δ Γ d (.val (.lolli (.mut a A) .unit))) :
    CDerivesAt Ξ Δ Γ (withborUE d) (.val (withbor3UTy a x Δ.meetOfDom A B S)) :=
  .withbor3UD (SD := []) x hΓ hx hfree₁ hfree₂ hS (RowLe.refl S) (RowLe.nil S) hS.divB
    (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil) hd

/-- **Every tied derivation is one of `CDerives`**: the tie dropped (`CDerivesX.mono`).
`[spec §19]` -/
theorem CDerivesAt.toCDerives {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerivesAt Ξ Δ Γ e j) : CDerives Δ Γ e j :=
  CDerivesX.mono ⟨Or.inl rfl, fun h => h⟩ h

/-- `[then]` with its finaliser at the pure row (§24, option A), tied: `effThen` at `Σ_M = Σ` and
`Σ_D = ∅`, as `CDerives.effThenA`.  `[spec §24, §27]` -/
theorem CDerivesAt.effThenA {Ξ : EffCtx} {Δ Γ Γ₁ Γ₂ M N D A B} {S : Row}
    (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hNZ : S.NZ) (hUq : S.Uniq) (hU : S.UnrD → Ctx.Banged Γ₂)
    (hM : CDerivesAt Ξ Δ Γ₁ M (.comp (CTy.effOf S A)))
    (hN : CDerivesAt Ξ Δ (⟨A, true⟩ :: Γ₂) N (.comp (CTy.effOf S B)))
    (hD : CDerivesAt Ξ Δ (⟨.unit, false⟩ :: Γ₂) D (.comp (.ret .unit))) :
    CDerivesAt Ξ Δ Γ (thenE N D M) (.comp (CTy.effOf S B)) :=
  .effThen (SD := []) hs hNZ hUq hU (RowLe.refl S) (RowLe.nil S)
    (fun _ _ o _ hf hf' _ => by rw [hf] at hf'; cases hf'; exact ThenLe.nil o.fin)
    (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil) rfl hM hN hD

/-- `[handle]` at two variables, tied: `CDerives.effHandle` with the handled row tied to `Ξ`.
`[spec §19]` -/
theorem CDerivesAt.effHandle {Ξ : EffCtx} {Δ Γ Γ₁ Γ₂ Γr Γc e} {S : Row}
    {E : List (Qual × VTy × VTy)} {n : UInt32} {A R : VTy} {ir ic : Nat}
    (hAt : RowAt Ξ (Row.ofEff n E 0 ++ S)) (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hs₁ : Ctx.SplitP Γ₁ Γr Γc)
    (hr : Ctx.SoloP Γr ir (retTy S A R)) (hc : Ctx.SoloP Γc ic (clausesTy S R E))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : Row.divB (Row.ofEff n E 0 ++ S) = false)
    (he : CDerivesAt Ξ Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 ++ S) A))) :
    CDerivesAt Ξ Δ Γ (hndTerm n (E.map Prod.fst) ir ic e) (.comp (CTy.effOf S R)) := by
  obtain ⟨sr, hsr, hlr⟩ := hr.live
  obtain ⟨sc, hsc, hlc⟩ := hc.live
  obtain ⟨sr', hsr', hlr'⟩ := hs₁.live_left hsr hlr
  obtain ⟨sc', hsc', hlc'⟩ := hs₁.live_right hsc hlc
  exact .effHandleV hAt hs
    (hs₁.deadP (hr.deadP (retTy_persistent S A R)) (hc.deadP (clausesTy_persistent S R E finsNil)))
    (.pair (.var hsr' hlr') (.var hsc' hlc')) (.tensorI hs₁ (.var hr) (.var hc)) hn0 hnS hlen hdv he

/-- BOXED-κ at two variables, tied: `CDerivesAt.effHandle` with the clauses at `clausesTyB`.
`[spec §28]` -/
theorem CDerivesAt.effHandleB {Ξ : EffCtx} {Δ Γ Γ₁ Γ₂ Γr Γc e} {S : Row}
    {E : List (Qual × VTy × VTy)} {n : UInt32} {A R : VTy} {ir ic : Nat} {d : Lifetime.Life}
    (hAt : RowAt Ξ (Row.ofEff n E 0 ++ S)) (hs : Ctx.SplitP Γ Γ₁ Γ₂) (hs₁ : Ctx.SplitP Γ₁ Γr Γc)
    (hr : Ctx.SoloP Γr ir (retTy S A R)) (hc : Ctx.SoloP Γc ic (clausesTyB S R d E))
    (hn0 : n ≠ 0) (hnS : ∀ o ∈ S, o.n ≠ n) (hlen : E.length ≤ 2 ^ 32)
    (hdv : Row.divB (Row.ofEff n E 0 ++ S) = false)
    (he : CDerivesAt Ξ Δ Γ₂ e (.comp (CTy.effOf (Row.ofEff n E 0 ++ S) A)))
    (hΓd : CtxOutlives Δ Γ₂ d) (hSd : Row.AnsOutlives Δ d (Row.ofEff n E 0 ++ S)) :
    CDerivesAt Ξ Δ Γ (hndTerm n (E.map Prod.fst) ir ic e) (.comp (CTy.effOf S R)) := by
  obtain ⟨sr, hsr, hlr⟩ := hr.live
  obtain ⟨sc, hsc, hlc⟩ := hc.live
  obtain ⟨sr', hsr', hlr'⟩ := hs₁.live_left hsr hlr
  obtain ⟨sc', hsc', hlc'⟩ := hs₁.live_right hsc hlc
  exact .effHandleVB hAt hs
    (hs₁.deadP (hr.deadP (retTy_persistent S A R))
      (hc.deadP (clausesTyB_persistent S R d E finsNil)))
    (.pair (.var hsr' hlr') (.var hsc' hlc')) (.tensorI hs₁ (.var hr) (.var hc)) hn0 hnS hlen hdv he
    hΓd hSd

/-! ### Tied rows -/

theorem rowAt_nil (Ξ : EffCtx) : RowAt Ξ [] := fun _ _ _ h => by simp [Row.find] at h

/-- Two rows tied to `Ξ` append to one. -/
theorem rowAt_append {Ξ : EffCtx} {S S' : Row} (h : RowAt Ξ S) (h' : RowAt Ξ S') :
    RowAt Ξ (S ++ S') := by
  intro n i o hf
  rw [Row.find_append] at hf
  cases hS : Row.find S n i with
  | none => rw [hS, Option.none_or] at hf; exact h' n i o hf
  | some o' => rw [hS, Option.some_or] at hf; cases hf; exact h n i o hS

/-- A row below a row tied to `Ξ` is tied to `Ξ`. -/
theorem rowAt_of_le {Ξ : EffCtx} {S S' : Row} (hle : RowLe S S') (h : RowAt Ξ S') :
    RowAt Ξ S := by
  intro n i o hf
  obtain ⟨o', hf', hs⟩ := RowLe.sig hle hf
  obtain ⟨h₁, h₂, p, h₃, h₄⟩ := h n i o' hf'
  exact ⟨h₁, h₂, p, h₃, by rw [OpSig.AtEntry, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1]; exact h₄⟩

/-- The front of a row tied to `Ξ` is tied to `Ξ`. -/
theorem rowAt_left {Ξ : EffCtx} {S S' : Row} (h : RowAt Ξ (S ++ S')) : RowAt Ξ S :=
  rowAt_of_le (RowLe.of_find fun n i o hf => by rw [Row.find_append, hf, Option.some_or]) h

/-- A name's row at the signature `Ξ` gives it is tied to `Ξ`. -/
theorem ofEff_wf (Ξ : EffCtx) (n : UInt32) (hn : n ≠ 0) (hlen : (Ξ n).length ≤ 2 ^ 32) :
    RowAt Ξ (Row.ofEff n (Ξ n) 0) := by
  intro m i o h
  obtain ⟨rfl, j, hj, rfl, rfl⟩ := Row.find_ofEff n (Ξ n) 0 finsNil m i o h
  refine ⟨hn, hlen, _, ?_, OpSig.AtEntry.self _⟩
  have hj' : (UInt32.ofNat (0 + j)).toNat = j := by
    rw [Nat.zero_add]; exact UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
  rw [hj']
  simp [List.getElem?_eq_getElem hj]

/-- A signature's row finds each of its operations by index. -/
theorem find_ofEff_isSome (n : UInt32) : ∀ (E : List (Qual × VTy × VTy)) (k j : Nat) (i : UInt32),
    i.toNat = k + j → k + j < 2 ^ 32 → j < E.length → (Row.find (Row.ofEff n E k) n i).isSome
  | [], _, _, _, _, _, h => absurd h (by simp)
  | (q, A, B) :: E, k, 0, i, hi, hk, _ => by
      have hik : i = UInt32.ofNat k := by
        apply UInt32.toNat.inj
        rw [hi, UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)]
        rfl
      subst hik
      simp [Row.ofEff, Row.find]
  | (q, A, B) :: E, k, j + 1, i, hi, hk, hj => by
      have hne : i ≠ UInt32.ofNat k := by
        intro h
        rw [h, UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)] at hi
        omega
      have ih := find_ofEff_isSome n E (k + 1) j i (by omega) (by omega)
        (by simp only [List.length_cons] at hj; omega)
      unfold Row.find at ih ⊢
      rw [Row.ofEff, List.find?_cons_of_neg (by simp [hne])]
      exact ih

/-- A signature's row finds its `j`-th operation at the index `j`, below `2³²`. -/
theorem find_ofEff_at (n : UInt32) (E : List (Qual × VTy × VTy)) (j : Nat) (hj : j < E.length)
    (hlen : E.length ≤ 2 ^ 32) :
    Row.find (Row.ofEff n E 0) n (UInt32.ofNat j) =
      some ⟨n, UInt32.ofNat j, E[j].1, E[j].2.1, E[j].2.2, .ret .unit, false⟩ := by
  have hj' : j < 2 ^ 32 := by omega
  have hi : (UInt32.ofNat j).toNat = 0 + j := by
    rw [Nat.zero_add]; exact UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)
  obtain ⟨o, ho⟩ := Option.isSome_iff_exists.mp
    (find_ofEff_isSome n E 0 j (UInt32.ofNat j) hi (by omega) hj)
  obtain ⟨-, j', hj'', hij, rfl⟩ := Row.find_ofEff n E 0 _ n _ o ho
  have : j' = j := by
    have h2 := congrArg UInt32.toNat hij
    rw [hi, Nat.zero_add, Nat.zero_add,
      UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)] at h2
    exact h2.symm
  subst this
  rw [ho, Nat.zero_add]

/-- A name's row at the signature `Ξ` gives it, before a row tied to `Ξ`, is tied to `Ξ`. -/
theorem rowAt_ofEff_append {Ξ : EffCtx} {n : UInt32} {E : List (Qual × VTy × VTy)} {S : Row}
    (hE : Ξ n = E) (hn : n ≠ 0) (hlen : E.length ≤ 2 ^ 32) (hS : RowAt Ξ S) :
    RowAt Ξ (Row.ofEff n E 0 ++ S) := by
  subst hE
  exact rowAt_append (ofEff_wf Ξ n hn hlen) hS

/-- **An effect's row finds, at each key, operations of the same signature at any cancel rows.** -/
theorem find_ofEff_sig (n : UInt32) : ∀ (E : List (Qual × VTy × VTy)) (k : Nat) (fs fs' : Nat → CTy)
    (m i : UInt32) (o : OpSig), Row.find (Row.ofEff n E k fs) m i = some o →
      ∃ o', Row.find (Row.ofEff n E k fs') m i = some o' ∧ o.Sig o'
  | [], _, _, _, _, _, _, h => by simp [Row.ofEff, Row.find] at h
  | (q, A, B) :: E, k, fs, fs', m, i, o, h => by
      by_cases hk : m = n ∧ i = UInt32.ofNat k
      · have h₁ : Row.find (Row.ofEff n ((q, A, B) :: E) k fs) m i =
            some ⟨n, UInt32.ofNat k, q, A, B, fs 0, false⟩ := by
          simp [Row.ofEff, Row.find, hk]
        have h₂ : Row.find (Row.ofEff n ((q, A, B) :: E) k fs') m i =
            some ⟨n, UInt32.ofNat k, q, A, B, fs' 0, false⟩ := by
          simp [Row.ofEff, Row.find, hk]
        rw [h₁] at h; cases h
        exact ⟨_, h₂, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · have hd : decide (m = n ∧ i = UInt32.ofNat k) = false := decide_eq_false hk
        have h₁ : Row.find (Row.ofEff n ((q, A, B) :: E) k fs) m i =
            Row.find (Row.ofEff n E (k + 1) (fun j => fs (j + 1))) m i := by
          simp only [Row.ofEff, Row.find, List.find?_cons, hd]
        have h₂ : Row.find (Row.ofEff n ((q, A, B) :: E) k fs') m i =
            Row.find (Row.ofEff n E (k + 1) (fun j => fs' (j + 1))) m i := by
          simp only [Row.ofEff, Row.find, List.find?_cons, hd]
        rw [h₁] at h; rw [h₂]
        exact find_ofEff_sig n E (k + 1) _ _ m i o h

/-- **The tie reads no cancel row**: an effect's row before a tied row is tied at any cancel rows
when it is at some. -/
theorem rowAt_ofEff_fs {Ξ : EffCtx} {n : UInt32} {E : List (Qual × VTy × VTy)}
    {fs fs' : Nat → CTy} {S : Row} (h : RowAt Ξ (Row.ofEff n E 0 fs ++ S)) :
    RowAt Ξ (Row.ofEff n E 0 fs' ++ S) := by
  intro m i o hf
  rw [Row.find_append] at hf
  cases hA : Row.find (Row.ofEff n E 0 fs') m i with
  | some o₁ =>
      rw [hA, Option.some_or] at hf
      have ho : o₁ = o := Option.some.inj hf
      subst ho
      obtain ⟨o', hf', hsig⟩ := find_ofEff_sig n E 0 fs' fs m i o₁ hA
      obtain ⟨h₁, h₂, p, h₃, h₄⟩ := h m i o' (by rw [Row.find_append, hf', Option.some_or])
      refine ⟨h₁, h₂, p, h₃, ?_⟩
      rw [OpSig.AtEntry, hsig.2.2.1, hsig.2.2.2.1, hsig.2.2.2.2.1]; exact h₄
  | none =>
      rw [hA, Option.none_or] at hf
      have hB : Row.find (Row.ofEff n E 0 fs) m i = none := by
        cases hB : Row.find (Row.ofEff n E 0 fs) m i with
        | none => rfl
        | some o₂ =>
            obtain ⟨o', hf', -⟩ := find_ofEff_sig n E 0 fs fs' m i o₂ hB
            rw [hA] at hf'; cases hf'
      exact h m i o (by rw [Row.find_append, hB, Option.none_or, hf])

/-- **A tied handler's signature is a prefix of the context's**, up to α: the handled row
`(n)↑E ⊙ Σ`, tied to `Ξ`, finds each operation of `E` at the signature `Ξ n` gives at its index.
`[spec §3, §19]` -/
theorem sig_prefix_of_rowAt {Ξ : EffCtx} {n : UInt32} {E : List (Qual × VTy × VTy)} {S : Row}
    (h : RowAt Ξ (Row.ofEff n E 0 ++ S)) (hlen : E.length ≤ 2 ^ 32) :
    ∀ j (hj : j < E.length), ∃ p, (Ξ n)[j]? = some p ∧ p.1 = E[j].1 ∧
      VTy.alphaB [] p.2.1 E[j].2.1 = true ∧ VTy.alphaB [] p.2.2 E[j].2.2 = true := by
  intro j hj
  have hf : Row.find (Row.ofEff n E 0 ++ S) n (UInt32.ofNat j) =
      some ⟨n, UInt32.ofNat j, E[j].1, E[j].2.1, E[j].2.2, .ret .unit, false⟩ := by
    rw [Row.find_append, find_ofEff_at n E j hj hlen, Option.some_or]
  obtain ⟨-, -, p, hg, hp⟩ := h n _ _ hf
  rw [UInt32.toNat_ofNat_of_lt' (by simp [UInt32.size]; omega)] at hg
  exact ⟨p, hg, hp⟩

/-- **A tied handler's tags are a prefix of the context's qualifiers** of its name (§25: a handler
value carries its operations' qualifiers, `E.map Prod.fst`).  `[spec §19, §25]` -/
theorem hndTags_of_rowAt {Ξ : EffCtx} {n : UInt32} {E : List (Qual × VTy × VTy)} {S : Row}
    (h : RowAt Ξ (Row.ofEff n E 0 ++ S)) (hlen : E.length ≤ 2 ^ 32) :
    E.map Prod.fst <+: (Ξ n).map Prod.fst := by
  have hp := sig_prefix_of_rowAt h hlen
  have hle : E.length ≤ (Ξ n).length := by
    rcases Nat.lt_or_ge (Ξ n).length E.length with hlt | hge
    · obtain ⟨p, hg, -⟩ := hp (Ξ n).length hlt
      simp at hg
    · exact hge
  rw [List.prefix_iff_eq_take]
  apply List.ext_getElem?
  intro j
  by_cases hj : j < E.length
  · obtain ⟨p, hg, h₁, -⟩ := hp j hj
    rw [List.getElem?_take_of_lt (by simpa using hj), List.getElem?_map, List.getElem?_map, hg,
      List.getElem?_eq_getElem hj]
    simp [h₁]
  · rw [List.getElem?_eq_none (by simpa using hj), List.getElem?_eq_none]
    simp only [List.length_take, List.length_map]
    omega

/-! ### Terms with no operation -/

/-- The term holds no `perform`, `raise`, `hnd` or `iterate`: none of its parts is typed by a rule
that reads an operation's signature off a row. -/
def _root_.BoCa.Expr.effFree : Expr → Bool
  | .prim p => p != .perform && p != .raise && p != .hnd && p != .iterate
  | .var _ | .unit | .loc _ => true
  | .pair a b | .seq a b | .letpair a b | .app a b => a.effFree && b.effFree
  | .inj₁ a | .inj₂ a | .lam a => a.effFree
  | .case a b c => a.effFree && b.effFree && c.effFree

theorem effFree_shift (d : Nat) (e : Expr) : ∀ c, (e.shift d c).effFree = e.effFree := by
  induction e with
  | var i => intro c; simp only [Expr.shift]; split <;> rfl
  | _ => intro c; simp_all [Expr.shift, Expr.effFree]

theorem effFree_subst (e : Expr) : ∀ (j : Nat) (s : Val), e.effFree = true → s.1.effFree = true →
    (e.subst j s).effFree = true := by
  induction e with
  | var i =>
      intro j s _ hs
      simp only [Expr.subst]
      split
      · exact hs
      · split <;> rfl
  | lam b ih =>
      intro j s he hs
      exact ih (j + 1) (s.shift 1 0) he (by rw [Val.val_shift, effFree_shift]; exact hs)
  | letpair a b iha ihb =>
      intro j s he hs
      simp only [Expr.effFree, Bool.and_eq_true] at he
      simp only [Expr.subst, Expr.effFree, Bool.and_eq_true]
      exact ⟨iha j s he.1 hs, ihb (j + 2) (s.shift 2 0) he.2
        (by rw [Val.val_shift, effFree_shift]; exact hs)⟩
  | case a b c iha ihb ihc =>
      intro j s he hs
      simp only [Expr.effFree, Bool.and_eq_true] at he
      have hs' : (s.shift 1 0).1.effFree = true := by rw [Val.val_shift, effFree_shift]; exact hs
      simp only [Expr.subst, Expr.effFree, Bool.and_eq_true]
      exact ⟨⟨iha j s he.1.1 hs, ihb (j + 1) _ he.1.2 hs'⟩, ihc (j + 1) _ he.2 hs'⟩
  | _ => intro j s he hs; simp_all [Expr.subst, Expr.effFree]

/-- The facts `effFree` gives about the parts of a term, for `CDerivesAt.ofEffFree`. -/
macro "eff_free" : tactic => `(tactic| (simp_all only [Expr.effFree, Expr.val, Val.lam, Val.prim,
    Val.unit, Val.inj₁, Val.inj₂, withPair, absurdE, thenE, withborUE, effFree_shift, Bool.and_eq_true,
    bne_iff_ne, ne_eq, reduceCtorEq, not_false_eq_true, and_self, and_true, true_and]))

/-- **A derivation of a term with no operation is tied at every effect context**: the three rules
that read a signature off a row type a `perform`, a `raise` or a `hnd`, and every other rule is the
same in both judgments.  `[spec §19]` -/
theorem CDerivesAt.ofEffFree {Ξ : EffCtx} {Δ : LifeCtx} {Γ : Ctx VTy} {e : Expr} {j : Jdg}
    (h : CDerives Δ Γ e j) (he : e.effFree = true) : CDerivesAt Ξ Δ Γ e j := by
  induction h with
  | var h => exact .var h
  | unitI h => exact .unitI h
  | tensorI hs _ _ ih1 ih2 => exact .tensorI hs (ih1 (by eff_free)) (ih2 (by eff_free))
  | sumI₁ _ ih1 => exact .sumI₁ (ih1 (by eff_free))
  | sumI₂ _ ih1 => exact .sumI₂ (ih1 (by eff_free))
  | thunkF _ ih1 => exact .thunkF (ih1 (by eff_free))
  | thunkV hC _ ih1 => exact .thunkV hC (ih1 he)
  | ret _ ih1 => exact .ret (ih1 he)
  | bind hs _ _ ih1 ih2 => exact .bind hs (ih1 (by eff_free)) (ih2 (by eff_free))
  | force h hT => exact .force h hT
  | lam _ ih1 => exact .lam (ih1 (by eff_free))
  | lamDead _ ih1 => exact .lamDead (ih1 (by eff_free))
  | app hs _ hx ih1 => exact .app hs (ih1 (by eff_free)) hx
  | withI _ _ ih1 ih2 => exact .withI (ih1 (by eff_free)) (ih2 (by eff_free))
  | proj₁ _ ih1 => exact .proj₁ (ih1 (by eff_free))
  | proj₂ _ ih1 => exact .proj₂ (ih1 (by eff_free))
  | topI => exact .topI
  | unitE hs _ _ ih1 ih2 => exact .unitE hs (ih1 (by eff_free)) (ih2 (by eff_free))
  | tensorE hs _ _ ih1 ih2 => exact .tensorE hs (ih1 (by eff_free)) (ih2 (by eff_free))
  | sumE hs _ _ _ ih1 ih2 ih3 =>
      exact .sumE hs (ih1 (by eff_free)) (ih2 (by eff_free)) (ih3 (by eff_free))
  | zeroE hs _ ih1 => exact .zeroE hs (ih1 (by eff_free))
  | allI hbx hΔx hΓx _ ih1 => exact .allI hbx hΔx hΓx (ih1 (by eff_free))
  | allE _ hlt ih1 => exact .allE (ih1 (by eff_free)) hlt
  | bangThunkF hp _ ih1 => exact .bangThunkF hp (ih1 (by eff_free))
  | bangThunkV hp hC _ ih1 => exact .bangThunkV hp hC (ih1 he)
  | codeI _ hok ih1 => exact .codeI (ih1 he) hok
  | codeIB hp _ hok ih1 => exact .codeIB hp (ih1 he) hok
  | codeErase _ ih1 => exact .codeErase (ih1 he)
  | codeEraseB _ ih1 => exact .codeEraseB (ih1 he)
  | bangE _ ih1 => exact .bangE (ih1 he)
  | copyBang hΓ => exact .copyBang hΓ
  | releaseBang hΓ => exact .releaseBang hΓ
  | boxI _ hΓ ih1 => exact .boxI (ih1 he) hΓ
  | boxE _ ih1 => exact .boxE (ih1 he)
  | immSub _ hle ih1 => exact .immSub (ih1 he) hle
  | mutSub _ hle ih1 => exact .mutSub (ih1 he) hle
  | alloc hΓ => exact .alloc hΓ
  | free hΓ => exact .free hΓ
  | tokMint hΓ => exact .tokMint hΓ
  | tokBurn hΓ => exact .tokBurn hΓ
  | swap hΓ => exact .swap hΓ
  | copy hΓ => exact .copy hΓ
  | releaseImm hΓ => exact .releaseImm hΓ
  | releaseMut hΓ => exact .releaseMut hΓ
  | releaseUnk hΓ => exact .releaseUnk hΓ
  | lit c hΓ => exact .lit c hΓ
  | hostOp op hΓ => exact .hostOp op hΓ
  | arrNew A hΓ => exact .arrNew A hΓ
  | arrFree A hΓ => exact .arrFree A hΓ
  | arrSize A hΓ => exact .arrSize A hΓ
  | arrReplace A hΓ => exact .arrReplace A hΓ
  | arrLen a A hΓ => exact .arrLen a A hΓ
  | arrGet a A hΓ => exact .arrGet a A hΓ
  | arrCopy a A hΓ => exact .arrCopy a A hΓ
  | arrRelease a A hΓ => exact .arrRelease a A hΓ
  | countFold S hΓ => exact .countFold S hΓ
  | countTry S E hΓ => exact .countTry S E hΓ
  | boundedFix A C hΓ => exact .boundedFix A C hΓ
  | sliceBorrowM x hΓ hsideA hsideB hfree₁ hfree₂ =>
      exact .sliceBorrowM x hΓ hsideA hsideB hfree₁ hfree₂
  | sliceBorrowI x hΓ hsc hsideA hsideB hfree₁ hfree₂ =>
      exact .sliceBorrowI x hΓ hsc hsideA hsideB hfree₁ hfree₂
  | sliceGetM a A hΓ => exact .sliceGetM a A hΓ
  | sliceLenM a A hΓ => exact .sliceLenM a A hΓ
  | sliceSplitI a A hΓ => exact .sliceSplitI a A hΓ
  | sliceSplitM a A hΓ => exact .sliceSplitM a A hΓ
  | sliceEmptyI a A hΓ => exact .sliceEmptyI a A hΓ
  | sliceEmptyM a A hΓ => exact .sliceEmptyM a A hΓ
  | arrEmpty A hΓ => exact .arrEmpty A hΓ
  | sliceReplaceM a A hΓ => exact .sliceReplaceM a A hΓ
  | sliceSwapM a A hΓ => exact .sliceSwapM a A hΓ
  | sliceCopyM a b A hΓ hA => exact .sliceCopyM a b A hΓ hA
  | withbor1 x hΓ hx hsc₁ hfree₁ hfree₂ => exact .withbor1 x hΓ hx hsc₁ hfree₁ hfree₂
  | withbor2 x hΓ hx hside hfree₁ hfree₂ => exact .withbor2 x hΓ hx hside hfree₁ hfree₂
  | withbor3 x hΓ hx hfree₁ hfree₂ => exact .withbor3 x hΓ hx hfree₁ hfree₂
  | withload x hΓ hx hfree₁ hfree₂ => exact .withload x hΓ hx hfree₁ hfree₂
  | withswap hΓ => exact .withswap hΓ
  | withbor1UD x hΓ hx hsc₁ hfree₁ hfree₂ hS hMS hDS hSv hP _ ih1 =>
      exact .withbor1UD x hΓ hx hsc₁ hfree₁ hfree₂ hS hMS hDS hSv hP (ih1 (by eff_free))
  | withbor2UD x hΓ hx hside hfree₁ hfree₂ hS hMS hDS hSv hP _ ih1 =>
      exact .withbor2UD x hΓ hx hside hfree₁ hfree₂ hS hMS hDS hSv hP (ih1 (by eff_free))
  | withbor3UD x hΓ hx hfree₁ hfree₂ hS hMS hDS hSv hP _ ih1 =>
      exact .withbor3UD x hΓ hx hfree₁ hfree₂ hS hMS hDS hSv hP (ih1 (by eff_free))
  | withloadU x hΓ hx hfree₁ hfree₂ hS => exact .withloadU x hΓ hx hfree₁ hfree₂ hS
  | sliceBorrowMU x hΓ hsideA hsideB hfree₁ hfree₂ hS _ ih1 =>
      exact .sliceBorrowMU x hΓ hsideA hsideB hfree₁ hfree₂ hS (ih1 (by eff_free))
  | sliceBorrowIU x hΓ hsc hsideA hsideB hfree₁ hfree₂ hS _ ih1 =>
      exact .sliceBorrowIU x hΓ hsc hsideA hsideB hfree₁ hfree₂ hS (ih1 (by eff_free))
  | lolliE hs _ _ ih1 ih2 => exact .lolliE hs (ih1 (by eff_free)) (ih2 (by eff_free))
  | allEV _ hlt ih1 => exact .allEV (ih1 (by eff_free)) hlt
  | ofRet _ ih1 => exact .ofRet (ih1 he)
  | roll hA hc _ ih1 => exact .roll hA hc (ih1 he)
  | unroll _ ih1 => exact .unroll (ih1 he)
  | foldImm F y c R hΓ hF hG hyM hyR hR => exact .foldImm F y c R hΓ hF hG hyM hyR hR
  | foldOwn F R hΓ hF hG => exact .foldOwn F R hΓ hF hG
  | foldOwnG B₀ Rs hΓ hB => exact .foldOwnG B₀ Rs hΓ hB
  | foldReuse F R hΓ hF hG => exact .foldReuse F R hΓ hF hG
  | nuIn hC _ ih1 => exact .nuIn hC (ih1 he)
  | nuOut hC _ ih1 => exact .nuOut hC (ih1 he)
  | unfoldN C S hC hS hΓ => exact .unfoldN C S hC hS hΓ
  | unfoldK C G S hC hG hS hΓ => exact .unfoldK C G S hC hG hS hΓ
  | nuOutK hC hG hS hGf h => exact .nuOutK hC hG hS hGf h
  | effSub hle _ ih1 => exact .effSub hle (ih1 he)
  | effPerform => simp [BoCa.BoLo.performE, Expr.effFree, Expr.val, Val.prim] at he
  | effAwait => simp [awaitE, BoCa.BoLo.performE, BoCa.BoLo.raiseE, Expr.effFree, Expr.val,
      Val.prim] at he
  | effRaise => simp [BoCa.BoLo.raiseE, Expr.effFree, Expr.val, Val.prim] at he
  | effLet hs hW hU _ _ ih1 ih2 => exact .effLet hs hW hU (ih1 (by eff_free)) (ih2 (by eff_free))
  | effThen hs hNZ hUq hU hMS hDS hfin hP hSD _ _ _ ih1 ih2 ih3 =>
      exact .effThen hs hNZ hUq hU hMS hDS hfin hP hSD (ih1 (by eff_free)) (ih2 (by eff_free))
        (ih3 (by eff_free))
  | effThenDiv hs hNZ hUq hU hMS hDS hfin hP hSD _ _ _ ih1 ih2 ih3 =>
      exact .effThenDiv hs hNZ hUq hU hMS hDS hfin hP hSD (ih1 (by eff_free)) (ih2 (by eff_free))
        (ih3 (by eff_free))
  | effHandleV | effHandleVB | effHandleT | effHandleL =>
      simp [hndExpr, Expr.effFree, Expr.val, Val.prim] at he
  | iterate => simp [Expr.effFree, Expr.val, Val.prim] at he
  | divFuel => simp [divFuelV, fuelH, BoCa.BoLo.hndVal, BoCa.BoLo.hndE, Expr.effFree, Expr.val, Val.prim,
      Val.lam] at he
  | reify => simp [reifyV, BoCa.BoLo.hndE, Expr.effFree, Expr.val, Val.prim, Val.lam] at he
  | @letPoly _ _ N _ _ b hcl _ _ ihV ihN =>
      simp only [Expr.effFree, Expr.val, Val.lam, Bool.and_eq_true] at he
      exact .letPoly b hcl (ihV he.2)
        (ihN (by rw [effFree_shift]; exact effFree_subst N 0 (Val.lam b) he.1 he.2))
  | alpha _ hα ih => exact .alpha (ih he) hα

/-! ### Signature lists -/

/-- The operation is at `Ξ`'s signature: of a nonzero name with at most `2³²` operations, whose
`o.i`-th is `o`'s qualifier, argument and answer. -/
def OpAt (Ξ : EffCtx) (o : OpSig) : Prop :=
  o.n ≠ 0 ∧ (Ξ o.n).length ≤ 2 ^ 32 ∧ ∃ p, (Ξ o.n)[o.i.toNat]? = some p ∧ o.AtEntry p

/-- An operation at the entry that is its own signature. -/
theorem OpAt.of_get {Ξ : EffCtx} {o : OpSig} (h₁ : o.n ≠ 0) (h₂ : (Ξ o.n).length ≤ 2 ^ 32)
    (h₃ : (Ξ o.n)[o.i.toNat]? = some (o.q, o.A, o.B)) : OpAt Ξ o :=
  ⟨h₁, h₂, _, h₃, OpSig.AtEntry.self o⟩

/-- Every entry of the list is at `Ξ`'s signature. -/
def SigsAt (Ξ : EffCtx) (S : Row) : Prop := ∀ o ∈ S, OpAt Ξ o

theorem sigsAt_nil (Ξ : EffCtx) : SigsAt Ξ [] := fun _ h => absurd h List.not_mem_nil

theorem SigsAt.left {Ξ : EffCtx} {S S' : Row} (h : SigsAt Ξ (S ++ S')) : SigsAt Ξ S :=
  fun o ho => h o (List.mem_append_left S' ho)

theorem SigsAt.right {Ξ : EffCtx} {S S' : Row} (h : SigsAt Ξ (S ++ S')) : SigsAt Ξ S' :=
  fun o ho => h o (List.mem_append_right S ho)

/-- **A row whose entries are among a list at `Ξ`'s signatures is tied to `Ξ`.** -/
theorem rowAt_of_sigsAt {Ξ : EffCtx} {S : Row} (h : SigsAt Ξ S) : RowAt Ξ S := by
  intro n i o hf
  obtain ⟨hm, rfl, rfl⟩ := Row.find_mem hf
  exact h o hm

/-! ### No unrestricted abortive operation -/

/-- **No abortive operation is unrestricted**: every operation `Ξ` gives at `unr` answers
something other than `0`, so an abortive operation (answer `0` at a qualifier with weakening) is
cancellable.  Decision 63's restriction: `multi ctl op(…) -> never` is not provided.
`[spec §18, §19]` -/
def EffCtx.NoUnrExn (Ξ : EffCtx) : Prop := ∀ n, ∀ p ∈ Ξ n, p.1 = .unr → p.2.2.isZero = false

/-- At such a context no name's signature is one unrestricted abortive operation. -/
theorem EffCtx.NoUnrExn.ne_exn {Ξ : EffCtx} (h : Ξ.NoUnrExn) (n : UInt32) (A : VTy) :
    Ξ n ≠ [(.unr, A, .zero)] := by
  intro he
  have := h n (.unr, A, .zero) (by rw [he]; exact List.mem_singleton_self _) rfl
  simp [VTy.isZero] at this

/-- **In a row tied to such a context an unrestricted operation resumes**: it is not abortive.
`[spec §19]` -/
theorem abort_false_of_rowAt {Ξ : EffCtx} (hx : Ξ.NoUnrExn) {S : Row} (h : RowAt Ξ S)
    {n i : UInt32} {o : OpSig} (hf : Row.find S n i = some o) (hq : o.q = .unr) :
    o.abort = false := by
  obtain ⟨-, -, p, hget, hp1, -, hpB⟩ := h n i o hf
  have hz := hx n p (List.mem_of_getElem? hget) (hp1.trans hq)
  have hB : o.B.isZero = false := by
    rw [← hz]
    cases hb : p.2.2 <;> cases hb' : o.B <;> rw [hb, hb'] at hpB <;>
      simp_all [VTy.alphaB, VTy.isZero]
  simp only [OpSig.abort, hB, Bool.false_and]

end BoCa.Fig16.LogRel.Core
