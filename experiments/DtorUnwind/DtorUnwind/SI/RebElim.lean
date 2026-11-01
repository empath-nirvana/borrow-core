import Core.EffBorrow

/-!
# Spike #770, route C: removing a reborrow live across a stop

**Not a transcription.** New definitions beside Core's, about which programs hold the `↺`
reborrow (`[TR]` 6.150) across a non-abortive operation, and what a reborrow-free program would
have to provide in its place.

## Which Core forms are a reborrow

`[TR]` 6.150's reborrow is read in Core by `withload` and `withloadU` (`withloadU_compatX`
applies `wpG_reborrow`), and by `foldImm`, whose algebra reads the images of an imm-borrowed
`μ`.  `withbor3` (`Mut @a A` lent as `Mut 'x A`, Rust's `&mut *r`) is not one: its proof
(`withbor3_compatX`) is the Anti-Frame (6.66) around the Mut Frame (6.65), and `withswap` is the
Anti-Frame alone.  So in Core the only way to read through an `Imm` is the reborrow: `copy` and
`forget` are the other eliminations of `Imm`.

## Fields: inline and boxed

A field stored inline in the borrowed cell is a component of its payload.  Core has no rule
projecting an `Imm`/`Mut` onto a component; the field is read through the reborrow as its image,
which at a data payload mentions no lifetime (`image_inline`), so nothing of the reborrow stays
live once the value is read.  Array elements are the exception that is a projection of the same
lend: `slice_borrow_*`/`slice_split_*` lend an owned array as a family of leaves (a plain lend).
A field reached through a `Ref` (a box) or a `Mut` inside the borrowed value is a genuine
reborrow: its image is `Imm 'x B` at the reborrow's lifetime (`image_selfTy`).  On the `mut`
side, a field of a `Mut`-borrowed value is reached by `withswap`, whose callback is `⊸`: a
`mut` field borrow cannot hold a stop in Core with or without a reborrow; carrying it across one
is the Anti-Frame (6.66) across a stop, not 6.150.

## Where a reborrow can hold a stop (§1)

Core today has none.  `withload`'s and `foldImm`'s callbacks are `⊸`, which has no row, and
`withloadU`'s row is `Row.Unwind`: abortive operations only (`unwind_not_hasStop`).  The
programs in question are those of the extension the step-indexed relation is built for: a lend's
callback at a row holding a must-resume or cancellable operation.  `RebAcrossStop` is the
instance of `withloadUTy` at such a row.

## What a reborrow is at run time (§2)

Nothing: `withload ℓ f` steps by two β-steps at the same memory to `f () (load ℓ)` (Core's
`withload_beta`).  A
translation that removes a reborrow therefore does not change what the reborrow computes; it has to
give the same values a different typing, or compute them differently.

## The obstruction stated (§4)

`progMin` is an `&self` method with `self : Imm 'a (Ref (Mut @c I32) ⊗ I32)`: a boxed field
`f` and an inline field `n`.  It borrows `self.f` (the reborrow's image of the box,
`Imm 'x (Mut @c I32)`) and hands it to an opaque `h : ∀'z. Imm 'z (Mut @c I32) ⊸ F_y 1`, which
holds it across `y`.  A reborrow-free program at the same
type must hand `h` a plain imm lend of an owned `Ref (Mut @c I32)`.  `PlainImmArg` is what that
lend needs: an owned source reached from the context without the reborrow (`Reach`), or a fresh
cell whose content is built from the image (`Forge`).  `not_plainImmArg_progMin` refutes it.

`Reach` and `Forge` are **models of Core's rule table**, written here; the step from them to
"no `CDerives` derivation of any such program" is not derived, and I have not verified that the
obstruction is real for every translation.  What the Lean shows is that each of the three
candidate translations of the brief fails at `progMin` for the reason stated.

## The frozen copy (§3)

When the target type of a held image is `Forge`, a plain imm lend of a fresh copy stands in for
the reborrow.  `frz` is the type translation that makes every target forgeable: under an `Imm`,
`Mut @c B` becomes `Ref B` and codata becomes `1`.  `immReborrow_frz`: the image of a frozen
copy is the translated image, so the translation commutes with `Imm̲` (at `μ`-free types).
`forge_frz`: every frozen type is forgeable.  The translation changes the callee's type and
copies the data it reads.
-/

noncomputable section

namespace BoCa.Fig16.LogRel.Core.DtorUnwind.SI.RebElim
open BoCa
open BoCa.Fig16
open BoCa.Fig16.LogRel.Core
open BoCa.Lifetime (LifeVar)

/-! ## 1. A reborrow live across a stop -/

/-- A row holds a stop: an operation that is not abortive, whose continuation is resumed or
cancelled. -/
def HasStop (S : Row) : Prop := ∃ o ∈ S, o.abort = false

/-- `withloadU`'s row holds no stop. -/
theorem unwind_not_hasStop {S : Row} {x : LifeVar} (h : S.Unwind x) : ¬ HasStop S := by
  rintro ⟨o, ho, hab⟩
  rw [(h o ho).1] at hab
  exact Bool.noConfusion hab

/-- **A reborrow live across a stop**: `withload` at an unwinding type whose callback's row holds
a stop.  The extension's instance of `[TR]` 6.150 that rounds 7–9 did not carry across a stop. -/
def RebAcrossStop (T : VTy) : Prop :=
  ∃ (a : Lifetime.Life) (x : LifeVar) (bnd : Lifetime.Life) (A B : VTy) (S : Row),
    T = withloadUTy a x bnd A B S ∧ HasStop S

theorem effOf_inj {S S' : Row} {R R' : VTy} (h : CTy.effOf S R = CTy.effOf S' R') :
    S = S' ∧ R = R' := by
  induction S generalizing S' with
  | nil =>
      cases S' with
      | nil => exact ⟨rfl, by simpa [CTy.effOf] using h⟩
      | cons o os => simp [CTy.effOf] at h
  | cons o os ih =>
      cases S' with
      | nil => simp [CTy.effOf] at h
      | cons o' os' =>
          simp only [CTy.effOf, CTy.eff.injEq] at h
          obtain ⟨hn, hi, hq, hA, hB, hfin, hrc, hrest⟩ := h
          obtain ⟨rfl, rfl⟩ := ih hrest
          refine ⟨?_, rfl⟩
          cases o; cases o'
          simp_all

/-- **Core's `withloadU` never types one.**  Its premise `S.Unwind x` excludes every stop from the
callback's row, so a type `CDerives` gives `withload` through `withloadU` is not `RebAcrossStop`.
(`withload`'s own callback is `⊸`, with no row.) -/
theorem withloadU_not_across {a : Lifetime.Life} {x : LifeVar} {bnd : Lifetime.Life} {A B : VTy}
    {S : Row} (hS : S.Unwind x) : ¬ RebAcrossStop (withloadUTy a x bnd A B S) := by
  rintro ⟨a', x', bnd', A', B', S', he, hst⟩
  simp only [withloadUTy, withborUTy, VTy.thunk.injEq, CTy.arr.injEq] at he
  obtain ⟨-, -, he⟩ := he
  exact unwind_not_hasStop hS ((effOf_inj he).1 ▸ hst)

/-! ## 3. Frozen copies -/

/-- `B` has no `μ`, no type variable and no family: the types the commuting lemma is stated at. -/
def Flat : VTy → Prop
  | .unit | .zero | .unk | .int _ | .thunk _ | .opq _ => True
  | .tensor A B | .sum A B => Flat A ∧ Flat B
  | .ref A | .imm _ A | .mut _ A | .box _ A => Flat A
  | .bang _ => True
  | .tvar _ | .mu _ | .fam _ => False

/-- **The frozen form** of a payload read under an `Imm`: what the payload shows through any
`Imm`, as an owned value.  `Mut @c B ↦ Ref B` (an `Imm` shows the target, never the `Mut`),
`U C`, `Unk` and opaque leaves `↦ 1` (an `Imm` shows them as `Unk`), boxes dropped, `!A` kept. -/
def frz : VTy → VTy
  | .unit => .unit
  | .tensor A B => .tensor (frz A) (frz B)
  | .zero => .zero
  | .sum A B => .sum (frz A) (frz B)
  | .thunk _ => .unit
  | .ref A => .ref (frz A)
  | .imm a A => .imm a (frz A)
  | .mut _ A => .ref (frz A)
  | .box _ A => frz A
  | .bang A => .bang A
  | .unk => .unit
  | .int w => .int w
  | .tvar n => .tvar n
  | .mu A => .mu A
  | .fam L => .fam L
  | .opq _ => .unit

/-- The translation of an image type: every `Imm @c B` points at a frozen copy, `Unk ↦ 1`. -/
def trImg : VTy → VTy
  | .unit => .unit
  | .tensor A B => .tensor (trImg A) (trImg B)
  | .zero => .zero
  | .sum A B => .sum (trImg A) (trImg B)
  | .thunk C => .thunk C
  | .ref A => .ref A
  | .imm a A => .imm a (frz A)
  | .mut a A => .mut a A
  | .box a A => .box a A
  | .bang A => .bang A
  | .unk => .unit
  | .int w => .int w
  | .tvar n => .tvar n
  | .mu A => .mu A
  | .fam L => .fam L
  | .opq k => .opq k

/-- **The frozen copy's image is the translated image**: `Imm̲ 'b (frz A) = trImg (Imm̲ 'b A)`.  A
callee given a plain lend of a frozen copy sees, through it, the translation of what it saw
through the reborrow. -/
theorem immReborrow_frz (b : Lifetime.Life) :
    ∀ A : VTy, Flat A → (frz A).immReborrow b = trImg (A.immReborrow b)
  | .unit, _ => rfl
  | .tensor A B, h => by
      simp only [frz, VTy.immReborrow, trImg, immReborrow_frz b A h.1, immReborrow_frz b B h.2]
  | .zero, _ => rfl
  | .sum A B, h => by
      simp only [frz, VTy.immReborrow, trImg, immReborrow_frz b A h.1, immReborrow_frz b B h.2]
  | .thunk _, _ => rfl
  | .ref _, _ => rfl
  | .imm _ _, _ => rfl
  | .mut _ _, _ => rfl
  | .box _ A, h => by simp only [frz, VTy.immReborrow]; exact immReborrow_frz b A h
  | .bang _, _ => rfl
  | .unk, _ => rfl
  | .int _, _ => rfl
  | .opq _, _ => rfl

/-- **Forgeable**: a fresh owned value of `B` can be built from what an `Imm` shows of `B`
(`Imm̲ 'x B`), by reads whose reborrows end before the next stop.  Data is copied, a `Ref` is a
fresh cell of a forged content, an `Imm` is copied (`copy`), `!A` is shown whole. -/
inductive Forge : VTy → Prop
  | unit : Forge .unit
  | zero : Forge .zero
  | int (w) : Forge (.int w)
  | tensor {A B} : Forge A → Forge B → Forge (.tensor A B)
  | sum {A B} : Forge A → Forge B → Forge (.sum A B)
  | ref {A} : Forge A → Forge (.ref A)
  | imm (a A) : Forge (.imm a A)
  | bang (A) : Forge (.bang A)

/-- An `Imm` shows a `Mut` only as an `Imm` of its target, and no rule makes a `Mut @c` at a
lifetime `@c` of the context: a `Mut` cannot be forged. -/
theorem not_forge_mut (c : Lifetime.Life) (B : VTy) : ¬ Forge (.mut c B) := fun h => nomatch h

/-- An `Imm` shows codata as `Unk`: a thunk cannot be forged. -/
theorem not_forge_thunk (C : CTy) : ¬ Forge (.thunk C) := fun h => nomatch h

/-- An `Imm` shows an opaque host value as `Unk`. -/
theorem not_forge_opq (k : Opaque) : ¬ Forge (.opq k) := fun h => nomatch h

/-- **Every frozen type is forgeable.** -/
theorem forge_frz : ∀ A : VTy, Flat A → Forge (frz A)
  | .unit, _ => .unit
  | .tensor A B, h => .tensor (forge_frz A h.1) (forge_frz B h.2)
  | .zero, _ => .zero
  | .sum A B, h => .sum (forge_frz A h.1) (forge_frz B h.2)
  | .thunk _, _ => .unit
  | .ref A, h => .ref (forge_frz A h)
  | .imm a A, _ => .imm a (frz A)
  | .mut _ A, h => .ref (forge_frz A h)
  | .box _ A, h => forge_frz A h
  | .bang A, _ => .bang A
  | .unk, _ => .unit
  | .int w, _ => .int w
  | .opq _, _ => .unit

/-! ## 4. The program and the obstruction -/

/-- The result types of a computation type: what applying and forcing it can return. -/
inductive Returns : CTy → VTy → Prop
  | ret (R) : Returns (.ret R) R
  | arr {A C R} : Returns C R → Returns (.arr A C) R
  | all {x b C R} : Returns C R → Returns (.all x b C) R
  | ampL {C D R} : Returns C R → Returns (.amp C D) R
  | ampR {C D R} : Returns D R → Returns (.amp C D) R
  | eff {n i q A B fin rc C R} : Returns C R → Returns (.eff n i q A B fin rc C) R

/-- **`Reach T U`**: an owned `U` is obtained from a `T` by Core's eliminations whose callback may
hold a stop, without the reborrow: components, boxes and `!`, the content of an owned cell
(`swap`, `free`), the plain lends of an owned cell (`withbor` 1 and 2) and of a `Mut`
(`withbor3`), and a thunk's results.  Out of `Imm` only `copy` (`refl`); out of `Mut` no content,
since `withswap`'s callback is `⊸`.  A model of the rule table, not derived from `CDerives`. -/
inductive Reach : VTy → VTy → Prop
  | refl (T) : Reach T T
  | tensorL {A B U} : Reach A U → Reach (.tensor A B) U
  | tensorR {A B U} : Reach B U → Reach (.tensor A B) U
  | sumL {A B U} : Reach A U → Reach (.sum A B) U
  | sumR {A B U} : Reach B U → Reach (.sum A B) U
  | box {a A U} : Reach A U → Reach (.box a A) U
  | bang {A U} : Reach A U → Reach (.bang A) U
  | refContent {A U} : Reach A U → Reach (.ref A) U
  | refImm {A U} (x : LifeVar) : Reach (.imm (.var x) A) U → Reach (.ref A) U
  | refMut {A U} (x : LifeVar) : Reach (.mut (.var x) A) U → Reach (.ref A) U
  | mutMut {a A U} (x : LifeVar) : Reach (.mut (.var x) A) U → Reach (.mut a A) U
  | thunk {C R U} : Returns C R → Reach R U → Reach (.thunk C) U

/-- **What a plain imm lend of `Imm 'z B` across a stop needs**: an owned `Ref B` to lend
(`withbor` 1), reached from a context type without the reborrow, or a fresh cell whose content is
forged from the image. -/
def PlainImmArg (Γ : List VTy) (B : VTy) : Prop :=
  (∃ T ∈ Γ, Reach T (.ref B)) ∨ Forge B

/-- `I32`. -/
abbrev i32 : VTy := .int .w32

/-- The lifetimes: `'c` the `Mut`'s, `'a` the borrow's, `'z` the callee's, `'x` the reborrow's. -/
abbrev lc : LifeVar := 0
abbrev la : LifeVar := 1
abbrev lz : LifeVar := 2
abbrev lx : LifeVar := 3

/-- `y : 1 ↠^lin 1`, a must-resume stop. -/
def yOp : OpSig := { n := 6, i := 0, q := .lin, A := .unit, B := .unit }

/-- `yOp`'s row holds a stop. -/
theorem hasStop_y : HasStop [yOp] := ⟨yOp, List.mem_singleton_self _, rfl⟩

/-- `self`'s payload: a boxed field `f : Ref (Mut 'c I32)` and an inline field `n : I32`. -/
def selfTy : VTy := .tensor (.ref (.mut (.var lc) i32)) i32

/-- The source: `self : Imm 'a selfTy`. -/
def rTy : VTy := .imm (.var la) selfTy

/-- The callee: `h : U(∀'z ⊏ 'a. Imm 'z (Mut 'c I32) ⊸ F_y 1)`. -/
def hC : CTy := .all lz (.var la) (.arr (.imm (.var lz) (.mut (.var lc) i32)) (CTy.effOf [yOp] .unit))
def hTy : VTy := .thunk hC

/-- The image of `self`: the boxed field is a borrow at the reborrow's `'x`, the inline field is
its value.  `Imm̲ 'x selfTy = Imm 'x (Mut 'c I32) ⊗ I32`. -/
theorem image_selfTy :
    selfTy.immReborrow (.var lx) = .tensor (.imm (.var lx) (.mut (.var lc) i32)) i32 := rfl

/-- **An inline field shows no lifetime**: at a payload with no `Ref`, `Mut` or `[@a]`, the image
does not mention the reborrow's lifetime, so after the `withload` returns nothing of it is live.
Core has no projection of an `Imm` onto a component (no rule types `Imm @a (A ⊗ B) ⊸ Imm @a A`):
an inline field is read as its image, and a callee wanting `Imm 'z A` of an inline field cannot be
given one by any rule, reborrow or not. -/
theorem image_inline (b : Lifetime.Life) : (VTy.tensor i32 i32).immReborrow b = .tensor i32 i32 := rfl

/-- The callback: `Λ. λi. let (p, n) = i in h [] p`, the image's boxed field handed to `h`.
Under the `letpair`: `n` is `0`, `p` is `1`, `i` is `2`, the dead `Λ` slot `3`, `r` is `4`, `h` is `5`. -/
def cbMin : Val :=
  Val.lam (.val (Val.lam (.letpair (.var 0) (.app (.app (forceE hC (.var 5)) (.val .unit)) (.var 1)))))

/-- **`progMin`** `= λh. λr. withload r cbMin`: an `&self` method borrowing the boxed field
`self.f` and handing it to `h`, which holds it across `y`. -/
def progMin : Val :=
  Val.lam (.val (Val.lam (.app (.app (.val withloadV) (.var 0)) (.val cbMin))))

/-- `progMin`'s `withload` is at the unwinding type at the row `[y]`, `B = 1`: a reborrow live
across a stop. -/
theorem progMin_rebAcrossStop :
    RebAcrossStop (withloadUTy (.var la) lx (.var la) selfTy .unit [yOp]) :=
  ⟨_, _, _, _, _, _, rfl, hasStop_y⟩

theorem returns_hC {R : VTy} (h : Returns hC R) : R = .unit := by
  cases h with
  | all h => cases h with
    | arr h => cases h with
      | eff h => cases h with
        | ret => rfl

theorem reach_imm {a : Lifetime.Life} {A U : VTy} (h : Reach (.imm a A) U) : U = .imm a A := by
  cases h; rfl

theorem reach_unit {U : VTy} (h : Reach .unit U) : U = .unit := by
  cases h; rfl

/-- **The obstruction at `progMin`**: no owned `Ref (Mut 'c I32)` is reached from `h` or `r`
without the reborrow, and `Mut 'c I32` cannot be forged.  So the plain lend that would replace the
reborrow at `h`'s argument has no source: lifting to the owner fails (no owner in scope: `r` is
an `Imm`, out of which only `copy` leads), move-and-return fails (no `Mut` holds the cell),
and a copy fails (the target is a `Mut`). -/
theorem not_plainImmArg_progMin : ¬ PlainImmArg [hTy, rTy] (.mut (.var lc) i32) := by
  rintro (⟨T, hT, hr⟩ | hf)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hT
    rcases hT with rfl | rfl
    · cases hr with
      | thunk hR hr' =>
          obtain rfl := returns_hC hR
          exact VTy.noConfusion (reach_unit hr')
    · exact VTy.noConfusion (reach_imm hr)
  · exact not_forge_mut _ _ hf

/-- The same program with an `I32` target in place of the `Mut`: the copy applies. -/
theorem plainImmArg_int : PlainImmArg [] i32 := Or.inr (.int _)

/-- The frozen translation of the callee's argument is forgeable: `frz (Mut 'c I32) = Ref I32`. -/
theorem plainImmArg_frz : PlainImmArg [] (frz (.mut (.var lc) i32)) :=
  Or.inr (forge_frz _ trivial)

end BoCa.Fig16.LogRel.Core.DtorUnwind.SI.RebElim

end
