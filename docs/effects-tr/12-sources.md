# §12 Sources and novelty

[← §11 Transcription guide](11-transcription.md) · [index](README.md)

## 12.1 How sources are marked

- **[verified]**: title, authors, venue and year checked against Crossref's record of the DOI
  given, during the writing of this document.
- **[via phase A]**, **[via #235]**: the passage was read and cited by phase A
  (`docs/effect-model.md` §2) or by the literature report posted on #235, and is cited here as they
  cite it; not re-read for this document.
- **[recalled]**: the content is from memory, not from a passage read for this document.
- **[unverified]**: the bibliographic record itself was not checked.

No cited paper is claimed to be wrong anywhere in this document. Where a result here differs from
one there, the difference is in the setting, and it is named.

## 12.2 References

| key | reference | mark | used for |
|---|---|---|---|
| [TR] | Wagner, Gierczak, Marshall, Li & Ahmed, *From Linearity to Borrowing*, PACMPL 9 (OOPSLA2), 2025, technical report `3764117-supplement.pdf` | read for this document (§§1–5, 6.8 extracted) | the resource world, `wp`, the frame theorems, the FP's structure (§§4, 5, 9.3, 11.3) |
| BPPS18 | Biernacki, Piróg, Polesiuk & Sieczkowski, *Handle with care: relational interpretation of algebraic effects and handlers*, PACMPL 2 (POPL 2018), DOI 10.1145/3158096 | [verified]; construction [recalled] | binary relations for handlers; step-indexed (§9.4) |
| BPPS19 | Biernacki, Piróg, Polesiuk & Sieczkowski, *Abstracting algebraic effects*, PACMPL 3 (POPL 2019), DOI 10.1145/3290319 | [verified]; content [recalled] | abstraction safety as parametricity (T7.16) |
| BPPS20 | Biernacki, Piróg, Polesiuk & Sieczkowski, *Binders by day, labels by night: effect instances via lexically scoped handlers*, PACMPL 4 (POPL 2020), DOI 10.1145/3371116 | [verified]; content [recalled] | instances and labels (§12.3) |
| CMD26 | Congard, Munch-Maccagnoni & Douence, *Linear effects, exceptions, and resource safety: a Curry–Howard correspondence for destructors*, ESOP 2026, arXiv 2510.23517 | abstract read for this document; sections [via phase A] | destructors restore the strength of `T(− ⊕ E)`; `K[raise] ≡ D_K; raise` (T7.3); weakening at static points (§8.1) |
| Sta13 | Staton, *Instances of computational effects: an algebraic perspective*, LICS 2013, DOI 10.1109/LICS.2013.58 | [verified]; laws [via phase A] | `ν` and its four laws (§7.4) |
| MS14 | Møgelberg & Staton, *Linear usage of state*, LMCS 10(1:17), 2014 | [verified]; content [via phase A], [via #235] | capabilities as comodels; state access operations (D1.9, §8.2) |
| PP08 | Plotkin & Power, *Tensors of comodels and models for operational semantics*, MFPS 2008, ENTCS 218, DOI 10.1016/j.entcs.2008.10.018 | [verified]; Thm 4.4 and the constant remark [via phase A] | running as the tensor (T7.8); a theory with a constant has only the empty comodel (§8.2) |
| PCPR18 | Pruiksma, Chargin, Pfenning & Reed, *Adjoint Logic*, manuscript, 2018 | [unverified record]; §1–2 [via phase A] | modes and independence (D1.1, D2.6, L5.4) |
| PP13 | Plotkin & Pretnar, *Handling algebraic effects*, LMCS 9(4:23), 2013 | [via phase A] | every computation type is a model; handlers as homomorphisms (D3.11, T7.1) |
| AB20 | Ahman & Bauer, *Runners in action*, ESOP 2020, LNCS 12075, DOI 10.1007/978-3-030-44914-8_2 | [verified]; content [via phase A] | signals versus exceptions (T7.10); where a runner's error goes (§8.2) |
| HPP06 | Hyland, Plotkin & Power, *Combining effects: sum and tensor*, TCS 357, 2006 | [via #235] | sum and tensor (§7.3) |
| ZM19 | Zhang & Myers, *Abstraction-safe effect handlers via tunneling*, PACMPL 3 (POPL 2019), DOI 10.1145/3290318 | [verified]; content [via #235] | no accidental handling (T7.16) |
| THLM24 | Tang, Hillerström, Lindley & Morris, *Soundly handling linearity*, PACMPL 8 (POPL 2024), DOI 10.1145/3632896 | [verified]; content [via #235] | multi-shot persistence (C5.3, first row) |
| MM18 | Munch-Maccagnoni, *Resource polymorphism*, arXiv 1803.02796, 2018 | [via #235]; `A & 1` [recalled] | the cancellable continuation as `A & 1` (D1.8) |
| PS93 | Pitts & Stark, *Observable properties of higher order functions that dynamically create local names, or: What's new?*, MFCS 1993, LNCS 711, DOI 10.1007/3-540-57182-5_8 | [verified]; content [recalled] | partial bijections of names as worlds (D4.7) |
| dVP21 | de Vilhena & Pottier, *A separation logic for effect handlers*, PACMPL 5 (POPL 2021), DOI 10.1145/3434314 | [verified]; content [recalled] | `ewp` with protocols, the shape SPEC §19 and D5.3 follow (§12.3) |
| SPEC | borrow-core `SPEC.md` §19 (native capture), §20 (`bounded_fix`) | read | `ewpTS`, protocols, the static continuation, drop glue, `bounded_fix` |
| PA | phase A: `experiments/EffModel/`, `docs/effect-model.md` | read; run | the calculus |
| PB | phase B: `experiments/EffModelRel/` (branch `effmodel-rel`, `~/repos/borrow-core-effmodel-rel` at `19d0ae9`) | read | the binary relation, the laws |

## 12.3 What is adapted, and what is new

**Adapted.**

| piece | from | how it is used here |
|---|---|---|
| the resource world, `wp` (total correctness, frame-quantified), compatibility-lemma structure of the FP | [TR] | §4.1, §5 (at the own fragment) |
| `ewp` with protocol tables, as a least fixed point in `Prop` | SPEC §19, borrow-core `Core/EffDefs.lean`; the idea of protocols is dVP21's [recalled] | D5.3, D4.6 |
| the static continuation `⟨resume, cancel⟩`, drop glue | SPEC §19; MM18's `A & 1`; CMD26's weakening as an effect | D1.8, §8.1 |
| every computation type a model; handlers as folds | PP13 | D3.11, D3.12 |
| the free-model tree semantics, the binary relation, its worlds, FP, adequacy, soundness, and most laws | phase B | §3.2, §6, §7 |
| partial bijections of names | PS93; Staton's `[Inj, Set]` | D4.7 |
| bounded recursion instead of general recursion | SPEC §20 | D1.9, L5.17, §9.4 |
| modes and independence | PCPR18, via phase A | D1.1, D2.6 |
| comodels as capabilities; the tensor | MS14, PP08, via phase A | D4.3, T7.8 |

**New to us** (as far as the sources above go; I have not surveyed the literature beyond them and
the #235 reports, so "new" means "not found there", not a claim of priority).

1. **Modes as sets of resources** (D4.2, L4.2): `W` as `⊆ NoOwn`, `C` as `⊆ Pers`, closed under
   composition, which turns adjoint logic's independence into a lemma about BoLo resources (L5.4)
   and makes it the one lemma behind every capture obligation (C5.3).
2. **Frame composition with compatibility** (D5.8, L5.6): the single place independence is used in
   the FP; the protocols ask only `Pers` at contraction and `Cancel` at weakening.
3. **One protocol per effect for both models and comodels** (D4.6): a handler and a runner of `E`
   are indistinguishable to a computation, semantically as phase A found them syntactically.
4. **A one-shot continuation as a heap cell freed by its use** (D3.2, D4.4): "resumed twice" is a
   use after free, and exactly-once finalisation is linearity (T5.2.3–4).
5. **The owning lend and the `Res` instance** (§10.1, §10.2) and the handler's own-bound capture
   (§10.3): rule changes forced by machine-checked counterexamples to phase A.
6. **Agreement of the CK machine with the free-model trees on moded programs** (T6.6), and with it
   soundness for the machine's contextual equivalence (T6.7).
7. **T1 located** (§9.3): unnecessary for an owning lend of an owned capability (T9.1); a
   sufficient condition for lifting [TR]'s frame theorems to `ewp` for a borrowed source, through
   the tail-resumption lemma (L9.2, T9.2).
8. **Fallible co-operations exactly at weakenable operations** (§8.2).
9. **ν/op's restriction to non-contractible qualifiers** (T7.15): phase B's counterexample, and the
   statement of what a proof needs (O1).
10. From phase B, new to us before this document: the pending and garbage name statuses
    (D4.7), `TreeRel.abE` (the destructor form built into the relation), and the relation's
    treatment of `ν/ν` and `idem-ν` by them.

**Relation to Biernacki et al.** Their relations (BPPS18–20) are binary relations for handlers in
calculi with general recursion, hence step-indexed [recalled]; BPPS20 treats instances through
lexically scoped handlers and labels [recalled]. This document's relation is not step-indexed
because the calculus terminates (§9.4), and its instances are Staton's generative `ν` with the
pending/garbage worlds of phase B. These are differences of setting, not improvements: a calculus
with general recursion would need their technique or another one (§9.4 item 1).
