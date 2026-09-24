# Index of `[TR]` and `[CONF]`

Every numbered result of `[TR]` §6 and `[CONF]` §3, and every printed definition of `[TR]` §§1–5 and Definitions 6.1–6.3 (the *definition rows*, numbered by section: row 5.30 is the 30th definition row of §5), with the file and the declarations that carry it.  Declaration names omit the `BoCa.` prefix; paths are relative to the repository root.  `§N` citations in the files are to `docs/adjudications.md`.

**Status of a numbered result.**

| status | meaning |
|---|---|
| `proved` | a Lean theorem whose statement is the printed one, tagged `[as printed]` (or `[encoding]`, a representation choice that changes nothing) |
| `proved*` | proved at a restriction stated in the theorem, tagged `[restricted: …]`; the record names the restriction |
| `variant` | a Lean theorem whose statement differs from the print in a way particular to that result (an added hypothesis, a direction, two results fused, a repaired relation), tagged `[variant: …]`; the record says how |
| `untranscribed` | no declaration; the record says so |

**Tags of a definition row.** `[as printed]`, `[encoding]`, `[repair]` (the Lean reads the print differently; the row's comment cites the `docs/adjudications.md` entry that argues the reading), `[about ours]` (not printed; needed by Lean).

**Rows 6.64–6.66 and 6.131–6.176.**  The `declaration` column and the `TR.lemma_*` alias name the lemma over the literal definitions of rows 4.4–4.14 and 5.33, and the status scores it.  The Fundamental Property (`Fig16.LogRel.Typed.fundamentalProperty`) is proved from the typed-world versions named in parentheses (`*_compatX`, `wpTS_*`, in `Support/TypedWorld/`), each stated at `SemX`/`wpTS`.

`[TR]` numbers Definitions and Lemmas in two sequences: Definitions 6.1, 6.2 and 6.3 are definition rows 5.61, 5.65 and 5.66, listed under *Definitions* below.

## Numbered results

| result | name | status | file | declaration | aliases |
|---|---|---|---|---|---|
| Lemma 6.1 |  | `proved` | `Paper/S6_1_StandardLemmas/Lemmas.lean` | `Fig16.ResU.compat_comm_iff` | `TR.lemma_6_1` |
| Lemma 6.2 |  | `proved` | `Paper/S6_1_StandardLemmas/Lemmas.lean` | `Fig16.ResU.Comp.comm` | `TR.lemma_6_2` |
| Lemma 6.3 |  | `proved` | `Paper/S6_1_StandardLemmas/Lemmas.lean` | `Fig16.ResU.Comp.assoc` | `TR.lemma_6_3` |
| Lemma 6.4 |  | `proved` | `Paper/S6_1_StandardLemmas/Lemmas.lean` | `Fig16.ResU.comp_empty_right` | `TR.lemma_6_4` |
| Lemma 6.5 |  | `proved` | `Paper/S6_1_StandardLemmas/Lemmas.lean` | `Fig16.ResU.hash_empty_right` | `TR.lemma_6_5` |
| Lemma 6.6 |  | `proved` | `Paper/S6_1_StandardLemmas/Lemmas.lean` | `Fig16.ResU.hash_symm_iff` | `TR.lemma_6_6` |
| Lemma 6.7 |  | `proved` | `Paper/S6_1_StandardLemmas/Lemmas.lean` | `Fig16.ResU.Lower.split` | `TR.lemma_6_7` |
| Lemma 6.8 |  | `proved` | `Paper/S6_1_StandardLemmas/Lemmas.lean` | `Fig16.ResU.Lower.congr` | `TR.lemma_6_8` |
| Lemma 6.9 |  | `proved` | `Paper/S6_1_StandardLemmas/Lemmas.lean` | `Fig16.ResU.compS_defined_iff` | `TR.lemma_6_9` |
| Lemma 6.10 |  | `proved` | `Paper/S6_1_StandardLemmas/Lemmas.lean` | `Fig16.ResU.Valid.split` | `TR.lemma_6_10` |
| Lemma 6.11 |  | `proved` | `Paper/S6_1_StandardLemmas/Lemmas.lean` | `Fig16.ResU.Hash.split` | `TR.lemma_6_11` |
| Lemma 6.12 |  | `proved` | `Paper/S6_1_StandardLemmas/Lemmas.lean` | `Fig16.ResU.compatS_of_compR` | `TR.lemma_6_12` |
| Lemma 6.13 |  | `proved` | `Paper/S6_1_StandardLemmas/Lemmas.lean` | `Fig16.ResU.compatS_of_pairwise` | `TR.lemma_6_13` |
| Lemma 6.14 |  | `proved` | `Paper/S6_1_StandardLemmas/Lemmas.lean` | `Fig16.ResU.compatR_of_pairwise` | `TR.lemma_6_14` |
| Lemma 6.15 |  | `proved` | `Paper/S6_1_StandardLemmas/Lemmas.lean` | `Fig16.ResU.hash_of_pairwise` | `TR.lemma_6_15` |
| Lemma 6.16 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.CompatS.of_flat` | `TR.lemma_6_16` |
| Lemma 6.17 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.compatS_of_hash_mut` | `TR.lemma_6_17` |
| Lemma 6.18 |  | `proved` | `Paper/S6_1_StandardLemmas/Lemmas.lean` | `Fig16.ExS.split` | `TR.lemma_6_18` |
| Lemma 6.19 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.flatR_idem` | `TR.lemma_6_19` |
| Lemma 6.20 |  | `proved` | `Paper/S6_1_StandardLemmas/Lemmas.lean` | `Fig16.AgW.split` | `TR.lemma_6_20` |
| Lemma 6.21 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six21` | `TR.lemma_6_21` |
| Lemma 6.22 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six22` | `TR.lemma_6_22` |
| Lemma 6.23 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six23` | `TR.lemma_6_23` |
| Lemma 6.24 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six24` | `TR.lemma_6_24` |
| Lemma 6.25 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six25` | `TR.lemma_6_25` |
| Lemma 6.26 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six26` | `TR.lemma_6_26` |
| Lemma 6.27 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six27` | `TR.lemma_6_27` |
| Lemma 6.28 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six28` | `TR.lemma_6_28` |
| Lemma 6.29 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six29` | `TR.lemma_6_29` |
| Lemma 6.30 |  | `proved` | `Paper/S6_1_StandardLemmas/Lemmas.lean` | `Fig16.ResU.CompatS.of_compR_left` | `TR.lemma_6_30` |
| Lemma 6.31 |  | `proved` | `Paper/S6_1_StandardLemmas/Lemmas.lean` | `Fig16.ResU.compR_iff_compS` | `TR.lemma_6_31` |
| Lemma 6.32 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ExS.toExR` | `TR.lemma_6_32` |
| Lemma 6.33 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six33` | `TR.lemma_6_33` |
| Lemma 6.34 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six34` | `TR.lemma_6_34` |
| Lemma 6.35 |  | `proved` | `Paper/S6_1_StandardLemmas/Lemmas.lean` | `Fig16.ResU.Valid.split` | `TR.lemma_6_35` |
| Lemma 6.36 |  | `proved` | `Paper/S6_1_StandardLemmas/Lemmas.lean` | `Fig16.ExW.immFree` | `TR.lemma_6_36` |
| Lemma 6.37 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six37` | `TR.lemma_6_37` |
| Lemma 6.38 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six38` | `TR.lemma_6_38` |
| Lemma 6.39 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six39` | `TR.lemma_6_39` |
| Lemma 6.40 |  | `untranscribed` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | **none — untranscribed** | — |
| Lemma 6.41 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.compatS_single_own` | `TR.lemma_6_41` |
| Lemma 6.42 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.compatS_single_mut` | `TR.lemma_6_42` |
| Lemma 6.43 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.compS_single_imm` | `TR.lemma_6_43` |
| Lemma 6.44 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.compatS_single_imm_inv` | `TR.lemma_6_44` |
| Lemma 6.45 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.atLife_comp_sqsupset` | `TR.lemma_6_45` |
| Lemma 6.46 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.BoLo.hash_shift` | `TR.lemma_6_46` |
| Lemma 6.47 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.Upd.refl`, `Fig16.ResU.UpdV.refl` | `TR.lemma_6_47` |
| Lemma 6.48 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.BoLo.updV_frame` | `TR.lemma_6_48` |
| Lemma 6.49 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.UpdV.trans`, `Fig16.ResU.Upd.trans` | `TR.lemma_6_49` |
| Lemma 6.50 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.BoLo.updV_outlives` | `TR.lemma_6_50` |
| Lemma 6.51 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six51` | `TR.lemma_6_51` |
| Lemma 6.52 |  | `variant` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six52` | `TR.lemma_6_52` |
| Lemma 6.53 |  | `proved*` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six53` | `TR.lemma_6_53` |
| Lemma 6.54 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six54` | `TR.lemma_6_54` |
| Lemma 6.55 |  | `proved*` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six55` | `TR.lemma_6_55` |
| Lemma 6.56 |  | `proved*` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six56` | `TR.lemma_6_56` |
| Lemma 6.57 |  | `proved*` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six57` | `TR.lemma_6_57` |
| Lemma 6.58 |  | `proved*` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six58_left`, `Fig16.ResU.six58_right` | `TR.lemma_6_58_left`, `TR.lemma_6_58_right` |
| Lemma 6.59 |  | `proved*` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six59` | `TR.lemma_6_59` |
| Lemma 6.60 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.LogRel.vDen_outlives` | `TR.lemma_6_60` |
| Lemma 6.61 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.ResU.six61` | `TR.lemma_6_61` |
| Lemma 6.62 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.LogRel.gDen_box` | `TR.lemma_6_62` |
| Lemma 6.63 |  | `proved` | `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.Life.down_sqsubset` | `TR.lemma_6_63` |
| Theorem 6.64 | Imm Frame | `proved` | `Paper/S6_3_FrameAndAntiFrame/Lemmas.lean` | `Fig16.LogRel.wp_I_frame` (typed world: `Fig16.LogRel.Typed.wpTS_I_frameX`) | `TR.lemma_6_64`, `TR.«Imm Frame»` |
| Theorem 6.65 | Mut Frame | `proved` | `Paper/S6_3_FrameAndAntiFrame/Lemmas.lean` | `Fig16.LogRel.wp_M_frame` (typed world: `Fig16.LogRel.Typed.wpTS_M_frameX`) | `TR.lemma_6_65`, `TR.«Mut Frame»` |
| Theorem 6.66 | Anti Frame | `proved` | `Paper/S6_3_FrameAndAntiFrame/Lemmas.lean` | `Fig16.LogRel.wp_M_antiFrame` (typed world: `Fig16.LogRel.Typed.wpTS_M_antiFrameX`) | `TR.lemma_6_66`, `TR.«Anti Frame»` |
| Lemma 6.67 | refl | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.Entails.refl` | `TR.lemma_6_67`, `TR.refl` |
| Lemma 6.68 | trans | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.Entails.trans` | `TR.lemma_6_68`, `TR.trans` |
| Lemma 6.69 | ⊤r | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.top_R` | `TR.lemma_6_69`, `TR.«⊤r»` |
| Lemma 6.70 | ⊥l | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.bot_L` | `TR.lemma_6_70`, `TR.«⊥l»` |
| Lemma 6.71 | ∧r | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.and_R` | `TR.lemma_6_71`, `TR.«∧r»` |
| Lemma 6.72 | ∧l | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.and_L₁`, `Fig16.BoLo.and_L₂` | `TR.lemma_6_72_1`, `TR.«∧l₁»`, `TR.lemma_6_72_2`, `TR.«∧l₂»` |
| Lemma 6.73 | ∨r | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.or_R₁`, `Fig16.BoLo.or_R₂` | `TR.lemma_6_73_1`, `TR.«∨r₁»`, `TR.lemma_6_73_2`, `TR.«∨r₂»` |
| Lemma 6.74 | ∨l | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.or_L` | `TR.lemma_6_74`, `TR.«∨l»` |
| Lemma 6.75 | ⇒r | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.imp_R` | `TR.lemma_6_75`, `TR.«⇒r»` |
| Lemma 6.76 | ⇒l | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.imp_L` | `TR.lemma_6_76`, `TR.«⇒l»` |
| Lemma 6.77 | ∀r | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.all_R` | `TR.lemma_6_77`, `TR.«∀r»` |
| Lemma 6.78 | ∀l | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.all_L` | `TR.lemma_6_78`, `TR.«∀l»` |
| Lemma 6.79 | ∃r | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.ex_R` | `TR.lemma_6_79`, `TR.«∃r»` |
| Lemma 6.80 | ∃l | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.ex_L` | `TR.lemma_6_80`, `TR.«∃l»` |
| Lemma 6.81 | ⌜⌝r | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.pure_R` | `TR.lemma_6_81`, `TR.«⌜⌝r»` |
| Lemma 6.82 | ⌜⌝l | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.pure_L` | `TR.lemma_6_82`, `TR.«⌜⌝l»` |
| Lemma 6.83 | !mono | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.bang_mono` | `TR.lemma_6_83`, `TR.«!mono»` |
| Lemma 6.84 | !l | `proved*` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.bang_L` | `TR.lemma_6_84`, `TR.«!l»` |
| Lemma 6.85 | !unr | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.bang_unr` | `TR.lemma_6_85`, `TR.«!unr»` |
| Lemma 6.86 | !∧ | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.bang_and` | `TR.lemma_6_86`, `TR.«!∧»` |
| Lemma 6.87 | !4 | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.bang_4` | `TR.lemma_6_87`, `TR.«!4»` |
| Lemma 6.88 | !∀ | `proved*` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.bang_all` | `TR.lemma_6_88`, `TR.«!∀»` |
| Lemma 6.89 | !∃ | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.bang_ex` | `TR.lemma_6_89`, `TR.«!∃»` |
| Lemma 6.90 | ⋆com | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.sep_comm` | `TR.lemma_6_90`, `TR.«⋆com»` |
| Lemma 6.91 | ⋆asc | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.sep_assoc` | `TR.lemma_6_91`, `TR.«⋆asc»` |
| Lemma 6.92 | ⋆mono | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.sep_mono` | `TR.lemma_6_92`, `TR.«⋆mono»` |
| Lemma 6.93 | –⋆r | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.wand_R` | `TR.lemma_6_93`, `TR.«–⋆r»` |
| Lemma 6.94 | –⋆l | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.wand_L` | `TR.lemma_6_94`, `TR.«–⋆l»` |
| Lemma 6.95 | ↦ex | `proved` | `Paper/S6_4_StandardEntailments/Lemmas.lean` | `Fig16.BoLo.ptoOwn_excl_own` | `TR.lemma_6_95`, `TR.«↦ex»` |
| Lemma 6.96 | []-mono | `proved` | `Paper/S6_5_NonStandardEntailments/Lemmas.lean` | `Fig16.BoLo.box_mono` | `TR.lemma_6_96`, `TR.«[]-mono»` |
| Lemma 6.97 | []l | `proved` | `Paper/S6_5_NonStandardEntailments/Lemmas.lean` | `Fig16.BoLo.box_L` | `TR.lemma_6_97`, `TR.«[]l»` |
| Lemma 6.98 | []r | `proved` | `Paper/S6_5_NonStandardEntailments/Lemmas.lean` | `Fig16.BoLo.box_R` | `TR.lemma_6_98`, `TR.«[]r»` |
| Lemma 6.99 | []4 | `proved` | `Paper/S6_5_NonStandardEntailments/Lemmas.lean` | `Fig16.BoLo.box_4` | `TR.lemma_6_99`, `TR.«[]4»` |
| Lemma 6.100 | []⊒ | `proved` | `Paper/S6_5_NonStandardEntailments/Lemmas.lean` | `Fig16.BoLo.box_antitone` | `TR.lemma_6_100`, `TR.«[]⊒»` |
| Lemma 6.101 | []∃r | `proved` | `Paper/S6_5_NonStandardEntailments/Lemmas.lean` | `Fig16.BoLo.box_ex_R` | `TR.lemma_6_101`, `TR.«[]∃r»` |
| Lemma 6.102 | []∀ | `proved*` | `Paper/S6_5_NonStandardEntailments/Lemmas.lean` | `Fig16.BoLo.box_all` | `TR.lemma_6_102`, `TR.«[]∀»` |
| Lemma 6.103 | []∃ | `proved` | `Paper/S6_5_NonStandardEntailments/Lemmas.lean` | `Fig16.BoLo.box_ex` | `TR.lemma_6_103`, `TR.«[]∃»` |
| Lemma 6.104 | []⋆ | `proved` | `Paper/S6_5_NonStandardEntailments/Lemmas.lean` | `Fig16.BoLo.box_sep` | `TR.lemma_6_104`, `TR.«[]⋆»` |
| Lemma 6.105 | []∨ | `proved` | `Paper/S6_5_NonStandardEntailments/Lemmas.lean` | `Fig16.BoLo.box_or` | `TR.lemma_6_105`, `TR.«[]∨»` |
| Lemma 6.106 | []! | `proved` | `Paper/S6_5_NonStandardEntailments/Lemmas.lean` | `Fig16.BoLo.box_bang` | `TR.lemma_6_106`, `TR.«[]!»` |
| Lemma 6.107 | []↦ | `proved` | `Paper/S6_5_NonStandardEntailments/Lemmas.lean` | `Fig16.BoLo.box_ptoOwn` | `TR.lemma_6_107`, `TR.«[]↦»` |
| Lemma 6.108 | И-mono | `proved` | `Paper/S6_5_NonStandardEntailments/Lemmas.lean` | `Fig16.BoLo.fresh_mono` | `TR.lemma_6_108`, `TR.«И-mono»` |
| Lemma 6.109 | Иl | `proved` | `Paper/S6_5_NonStandardEntailments/Lemmas.lean` | `Fig16.BoLo.fresh_L` | `TR.lemma_6_109`, `TR.«Иl»` |
| Lemma 6.110 | Иr | `proved` | `Paper/S6_5_NonStandardEntailments/Lemmas.lean` | `Fig16.BoLo.fresh_R` | `TR.lemma_6_110`, `TR.«Иr»` |
| Lemma 6.111 | И⋆ | `proved` | `Paper/S6_5_NonStandardEntailments/Lemmas.lean` | `Fig16.BoLo.fresh_sep` | `TR.lemma_6_111`, `TR.«И⋆»` |
| Lemma 6.112 | Иf | `proved` | `Paper/S6_3_FrameAndAntiFrame/Lemmas.lean` | `Fig16.BoLo.fresh_frame` | `TR.lemma_6_112`, `TR.«Иf»` |
| Lemma 6.113 | I-mono | `proved` | `Paper/S6_5_NonStandardEntailments/Lemmas.lean` | `Fig16.BoLo.ptoImm_mono` (typed world: `Fig16.LogRel.Typed.ptoImmS_mono`) | `TR.lemma_6_113`, `TR.«I-mono»` |
| Lemma 6.114 | I⊒ | `proved` | `Paper/S6_5_NonStandardEntailments/Lemmas.lean` | `Fig16.BoLo.ptoImm_antitone` | `TR.lemma_6_114`, `TR.«I⊒»` |
| Lemma 6.115 | I-ag | `variant` | `Paper/S6_5_NonStandardEntailments/Lemmas.lean` | `Fig16.BoLo.ptoImm_agree` | `TR.lemma_6_115`, `TR.«I-ag»` |
| Lemma 6.116 | I-dup | `proved` | `Paper/S6_5_NonStandardEntailments/Lemmas.lean` | `Fig16.BoLo.ptoImm_dup` | `TR.lemma_6_116`, `TR.«I-dup»` |
| Lemma 6.117 | M-inv | `proved` | `Paper/S6_5_NonStandardEntailments/Lemmas.lean` | `Fig16.BoLo.ptoMut_inv` | `TR.lemma_6_117`, `TR.«M-inv»` |
| Lemma 6.118 | M⊒ | `proved` | `Paper/S6_5_NonStandardEntailments/Lemmas.lean` | `Fig16.BoLo.ptoMut_antitone` | `TR.lemma_6_118`, `TR.«M⊒»` |
| Lemma 6.119 | M-ex | `proved` | `Paper/S6_5_NonStandardEntailments/Lemmas.lean` | `Fig16.BoLo.ptoMut_excl_own` | `TR.lemma_6_119`, `TR.«M-ex»` |
| Lemma 6.120 | ↺-mono | `proved` | `Paper/S6_6_ReborrowingEntailments/Lemmas.lean` | `Fig16.BoLo.reborrow_mono` | `TR.lemma_6_120`, `TR.«↺-mono»` |
| Lemma 6.121 | ↺↦ | `proved` | `Paper/S6_6_ReborrowingEntailments/Lemmas.lean` | `Fig16.BoLo.reborrow_ptoOwn` | `TR.lemma_6_121`, `TR.«↺↦»` |
| Lemma 6.122 | ↺m | `proved` | `Paper/S6_6_ReborrowingEntailments/Lemmas.lean` | `Fig16.BoLo.reborrow_ptoMut` | `TR.lemma_6_122`, `TR.«↺m»` |
| Lemma 6.123 | ↺i | `proved` | `Paper/S6_6_ReborrowingEntailments/Lemmas.lean` | `Fig16.BoLo.reborrow_ptoImm` | `TR.lemma_6_123`, `TR.«↺i»` |
| Lemma 6.124 | ↺⌜⌝ | `proved` | `Paper/S6_6_ReborrowingEntailments/Lemmas.lean` | `Fig16.BoLo.reborrow_pure` | `TR.lemma_6_124`, `TR.«↺⌜⌝»` |
| Lemma 6.125 | ↺⋆ | `proved` | `Paper/S6_6_ReborrowingEntailments/Lemmas.lean` | `Fig16.BoLo.reborrow_star` | `TR.lemma_6_125`, `TR.«↺⋆»` |
| Lemma 6.126 | ↺∨ | `proved` | `Paper/S6_6_ReborrowingEntailments/Lemmas.lean` | `Fig16.BoLo.reborrow_or` | `TR.lemma_6_126`, `TR.«↺∨»` |
| Lemma 6.127 | ↺-weak | `proved` | `Paper/S6_6_ReborrowingEntailments/Lemmas.lean` | `Fig16.BoLo.reborrow_weak` | `TR.lemma_6_127`, `TR.«↺-weak»` |
| Lemma 6.128 | ↺∃ | `proved` | `Paper/S6_6_ReborrowingEntailments/Lemmas.lean` | `Fig16.BoLo.reborrow_ex` | `TR.lemma_6_128`, `TR.«↺∃»` |
| Lemma 6.129 | ↺∀ | `variant` | `Paper/S6_6_ReborrowingEntailments/Lemmas.lean` | `Fig16.BoLo.reborrow_all` | `TR.lemma_6_129`, `TR.«↺∀»` |
| Lemma 6.130 |  | `proved*` | `Paper/S6_6_ReborrowingEntailments/Lemmas.lean` | `Fig16.BoLo.reborrow_emp` | `TR.lemma_6_130` |
| Lemma 6.131 | ↺V₁ | `proved` | `Paper/S6_6_ReborrowingEntailments/Lemmas.lean` | `Fig16.LogRel.reborrow_vDen_ne_unk` (typed world: `Fig16.LogRel.Typed.reborrow_vShape`, `Fig16.LogRel.Typed.image_vX_of_shape`) | `TR.lemma_6_131`, `TR.«↺V₁»` |
| Lemma 6.132 | ↺V₂ | `proved` | `Paper/S6_6_ReborrowingEntailments/Lemmas.lean` | `Fig16.LogRel.reborrow_vDen_fresh` (typed world: `Fig16.LogRel.Typed.six132_shape`, `Fig16.LogRel.Typed.six132_shape_fresh`) | `TR.lemma_6_132`, `TR.«↺V₂»` |
| Lemma 6.133 | ↺V₃ | `proved` | `Paper/S6_6_ReborrowingEntailments/Lemmas.lean` | `Fig16.LogRel.ptoImm_reborrow_vDen_fresh` | `TR.lemma_6_133`, `TR.«↺V₃»` |
| Lemma 6.134 |  | `proved` | `Paper/S6_6_ReborrowingEntailments/Lemmas.lean` | `Fig16.LogRel.pure_sep_reborrow_vDen_fresh` | `TR.lemma_6_134` |
| Lemma 6.135 | wp-bind | `proved` | `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` | `Fig16.BoLo.wp_bind` (typed world: `Fig16.LogRel.Typed.wpTS_bind`) | `TR.lemma_6_135`, `TR.«wp-bind»` |
| Lemma 6.136 | wp-val | `proved` | `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` | `Fig16.BoLo.wp_val` (typed world: `Fig16.LogRel.Typed.wpTS_val`) | `TR.lemma_6_136`, `TR.«wp-val»` |
| Lemma 6.137 | wp1 | `proved` | `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` | `Fig16.BoLo.wp_1` (typed world: `Fig16.LogRel.Typed.wpTS_head`, `Fig16.LogRel.Typed.wpTS_1`) | `TR.lemma_6_137`, `TR.wp1` |
| Lemma 6.138 | wp⊗ | `proved` | `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` | `Fig16.BoLo.wp_tensor` (typed world: `Fig16.LogRel.Typed.wpTS_tensor`) | `TR.lemma_6_138`, `TR.«wp⊗»` |
| Lemma 6.139 | wp⊕ | `proved` | `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` | `Fig16.BoLo.wp_sum₁`, `Fig16.BoLo.wp_sum₂` (typed world: `Fig16.LogRel.Typed.wpTS_sum₁`, `Fig16.LogRel.Typed.wpTS_sum₂`) | `TR.lemma_6_139_1`, `TR.«wp⊕₁»`, `TR.lemma_6_139_2`, `TR.«wp⊕₂»` |
| Lemma 6.140 | wp⊸ | `proved` | `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` | `Fig16.BoLo.wp_lolli` (typed world: `Fig16.LogRel.Typed.wpTS_lolli`) | `TR.lemma_6_140`, `TR.«wp⊸»` |
| Lemma 6.141 | wp-alloc | `proved` | `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` | `Fig16.BoLo.wp_alloc` (typed world: `Fig16.LogRel.Typed.wpTS_alloc`) | `TR.lemma_6_141`, `TR.«wp-alloc»` |
| Lemma 6.142 | wp-free | `proved` | `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` | `Fig16.BoLo.wp_free` (typed world: `Fig16.LogRel.Typed.wpTS_free`) | `TR.lemma_6_142`, `TR.«wp-free»` |
| Lemma 6.143 | wp-load | `proved` | `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` | `Fig16.BoLo.wp_load` (typed world: `Fig16.LogRel.Typed.wpTS_load`) | `TR.lemma_6_143`, `TR.«wp-load»` |
| Lemma 6.144 | wp-load-I | `proved` | `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` | `Fig16.BoLo.wp_load_I` (typed world: `Fig16.LogRel.Typed.wpTS_load_I`) | `TR.lemma_6_144`, `TR.«wp-load-I»` |
| Lemma 6.145 | wp-store | `proved` | `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` | `Fig16.BoLo.wp_store` (typed world: `Fig16.LogRel.Typed.wpTS_store`) | `TR.lemma_6_145`, `TR.«wp-store»` |
| Lemma 6.146 | wp-ramify | `proved` | `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` | `Fig16.BoLo.wp_ramify` (typed world: `Fig16.LogRel.Typed.wpTS_ramify`) | `TR.lemma_6_146`, `TR.«wp-ramify»` |
| Lemma 6.147 | wp[] | `proved` | `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` | `Fig16.BoLo.wp_box` (typed world: `Fig16.LogRel.Typed.wpTS_box`) | `TR.lemma_6_147`, `TR.«wp[]»` |
| Lemma 6.148 | wp-M-forget | `proved` | `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` | `Fig16.BoLo.wp_M_forget` (typed world: `Fig16.LogRel.Typed.wpTS_frame_noOwn`, `Fig16.LogRel.Typed.wpTS_M_forget`) | `TR.lemma_6_148`, `TR.«wp-M-forget»` |
| Lemma 6.149 | wp-I-forget | `proved` | `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` | `Fig16.BoLo.wp_I_forget` (typed world: `Fig16.LogRel.Typed.wpTS_I_forget`) | `TR.lemma_6_149`, `TR.«wp-I-forget»` |
| Theorem 6.150 | ↺ rule | `proved*` | `Paper/S6_7_WeakestPreconditionRules/Lemmas.lean` | `Fig16.BoLo.wp_reborrow` (typed world: `Fig16.LogRel.Typed.wpTS_reborrow`) | `TR.lemma_6_150`, `TR.«↺ rule»` |
| Lemma 6.151 | Fundamental Property | `variant` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.Typed.fundamentalProperty` | `TR.lemma_6_151`, `TR.«Fundamental Property»` |
| Lemma 6.152 | id-compat | `proved` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.id_compat` (typed world: `Fig16.LogRel.Typed.id_compatX`) | `TR.lemma_6_152`, `TR.«id-compat»` |
| Lemma 6.153 | 1I-compat | `proved` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.unitI_compat` (typed world: `Fig16.LogRel.Typed.unitI_compatX`) | `TR.lemma_6_153`, `TR.«1I-compat»` |
| Lemma 6.154 | 1E-compat | `proved` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.unitE_compat` (typed world: `Fig16.LogRel.Typed.unitE_compatX`) | `TR.lemma_6_154`, `TR.«1E-compat»` |
| Lemma 6.155 | ⊗I-compat | `proved` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.tensorI_compat` (typed world: `Fig16.LogRel.Typed.tensorI_compatX`) | `TR.lemma_6_155`, `TR.«⊗I-compat»` |
| Lemma 6.156 | ⊗E-compat | `proved` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.tensorE_compat` (typed world: `Fig16.LogRel.Typed.tensorE_compatX`) | `TR.lemma_6_156`, `TR.«⊗E-compat»` |
| Lemma 6.157 | ⊕I-compat | `proved` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.sumI₁_compat`, `Fig16.LogRel.sumI₂_compat` (typed world: `Fig16.LogRel.Typed.sumI₁_compatX`, `Fig16.LogRel.Typed.sumI₂_compatX`) | `TR.lemma_6_157_1`, `TR.«⊕I-compat₁»`, `TR.lemma_6_157_2`, `TR.«⊕I-compat₂»` |
| Lemma 6.158 | ⊕E-compat | `proved` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.sumE_compat` (typed world: `Fig16.LogRel.Typed.sumE_compatX`) | `TR.lemma_6_158`, `TR.«⊕E-compat»` |
| Lemma 6.159 | ⊸I-compat | `proved` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.lolliI_compat` (typed world: `Fig16.LogRel.Typed.lolliI_compatX`) | `TR.lemma_6_159`, `TR.«⊸I-compat»` |
| Lemma 6.160 | ⊸E-compat | `proved` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.lolliE_compat` (typed world: `Fig16.LogRel.Typed.lolliE_compatX`) | `TR.lemma_6_160`, `TR.«⊸E-compat»` |
| Lemma 6.161 | ∀I-compat | `variant` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.allI_compat` (typed world: `Fig16.LogRel.Typed.allI_compatX`) | `TR.lemma_6_161`, `TR.«∀I-compat»` |
| Lemma 6.162 | ∀E-compat | `proved` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.allE_compat` (typed world: `Fig16.LogRel.Typed.allE_compatX`) | `TR.lemma_6_162`, `TR.«∀E-compat»` |
| Lemma 6.163 | []I-compat | `proved` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.boxI_compat` (typed world: `Fig16.LogRel.Typed.boxI_compatX`) | `TR.lemma_6_163`, `TR.«[]I-compat»` |
| Lemma 6.164 | []E-compat | `proved` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.boxE_compat` (typed world: `Fig16.LogRel.Typed.boxE_compatX`) | `TR.lemma_6_164`, `TR.«[]E-compat»` |
| Lemma 6.165 | alloc-compat | `proved` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.alloc_compat` (typed world: `Fig16.LogRel.Typed.alloc_compatX`) | `TR.lemma_6_165`, `TR.«alloc-compat»` |
| Lemma 6.166 | free-compat | `proved` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.free_compat` (typed world: `Fig16.LogRel.Typed.free_compatX`) | `TR.lemma_6_166`, `TR.«free-compat»` |
| Lemma 6.167 | ⊑imm-compat | `proved` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.immSub_compat` (typed world: `Fig16.LogRel.Typed.immSub_compatX`) | `TR.lemma_6_167`, `TR.«⊑imm-compat»` |
| Lemma 6.168 | ⊑mut-compat | `proved` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.mutSub_compat` (typed world: `Fig16.LogRel.Typed.mutSub_compatX`) | `TR.lemma_6_168`, `TR.«⊑mut-compat»` |
| Lemma 6.169 | swap-compat | `proved` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.swap_compat` (typed world: `Fig16.LogRel.Typed.swap_compatX`) | `TR.lemma_6_169`, `TR.«swap-compat»` |
| Lemma 6.170 | copy-compat | `proved` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.copy_compat` (typed world: `Fig16.LogRel.Typed.copy_compatX`) | `TR.lemma_6_170`, `TR.«copy-compat»` |
| Lemma 6.171 | forget-compat | `proved` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.forgetImm_compat`, `Fig16.LogRel.forgetMut_compat`, `Fig16.LogRel.forgetUnk_compat` (typed world: `Fig16.LogRel.Typed.forgetImm_compatX`, `Fig16.LogRel.Typed.forgetMut_compatX`, `Fig16.LogRel.Typed.forgetUnk_compatX`) | `TR.lemma_6_171_1`, `TR.«forget-compat₁»`, `TR.lemma_6_171_2`, `TR.«forget-compat₂»`, `TR.lemma_6_171_3`, `TR.«forget-compat₃»` |
| Lemma 6.172 | withbor-compat1 | `variant` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.withbor1_compat` (typed world: `Fig16.LogRel.Typed.withbor1_compatX`) | `TR.lemma_6_172`, `TR.«withbor-compat1»` |
| Lemma 6.173 | withbor-compat2 | `variant` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.withbor2_compat` (typed world: `Fig16.LogRel.Typed.withbor2_compatX`) | `TR.lemma_6_173`, `TR.«withbor-compat2»` |
| Lemma 6.174 | withbor-compat3 | `variant` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.withbor3_compat` (typed world: `Fig16.LogRel.Typed.withbor3_compatX`) | `TR.lemma_6_174`, `TR.«withbor-compat3»` |
| Lemma 6.175 | withload-compat | `proved*` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.withload_compat` (typed world: `Fig16.LogRel.Typed.withload_compatX`) | `TR.lemma_6_175`, `TR.«withload-compat»` |
| Lemma 6.176 | withswap-compat | `proved` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.withswap_compat` (typed world: `Fig16.LogRel.Typed.withswap_compatX`) | `TR.lemma_6_176`, `TR.«withswap-compat»` |
| `[CONF]` Lemma 3.1 | Fundamental Property | `variant` | `Paper/S6_8_FundamentalProperty/Lemmas.lean` | `Fig16.LogRel.Typed.fundamentalProperty` | `CONF.lemma_3_1` |
| `[CONF]` Theorem 3.2 | Adequacy | `proved` | `Paper/CONF/Results.lean` | `Adequacy.theorem32` | `CONF.theorem_3_2` |
| `[CONF]` Corollary 3.3 | Adequacy at 1 | `proved` | `Paper/CONF/Results.lean` | `Adequacy.corollary33` | `CONF.corollary_3_3` |

## Definitions

| row | printed | tag | file | declarations |
|---|---|---|---|---|
| 1.1 | `Var ∋ x, y, …` | `[encoding]` | `Paper/S1_Syntax/Definitions.lean` | `Expr` |
| 1.2 | `Loc ∋ ℓ` | `[encoding]` | `Paper/S1_Syntax/Definitions.lean` | `Loc` |
| 1.3 | `Val ∋ v ::= ()` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Val.unit` |
| 1.4 | `Val ::= … ∣ (v₁, v₂)` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Val.pair` |
| 1.5 | `Val ::= … ∣ inj₁ v` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Val.inj₁` |
| 1.6 | `Val ::= … ∣ inj₂ v` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Val.inj₂` |
| 1.7 | `Val ::= … ∣ λx.e` | `[encoding]` | `Paper/S1_Syntax/Definitions.lean` | `Val.lam` |
| 1.8 | `Val ::= … ∣ Λ.e` | `[repair]` | `Paper/S1_Syntax/Definitions.lean` | `Val.lam` |
| 1.9 | `Val ::= … ∣ ℓ` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Val.loc` |
| 1.10 | `Val ::= … ∣ p` | `[encoding]` | `Paper/S1_Syntax/Definitions.lean` | `Val.prim`, `Val.storeV` |
| 1.11 | `Prim ∋ p ::= alloc` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Prim` |
| 1.12 | `Prim ::= … ∣ free` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Prim` |
| 1.13 | `Prim ::= … ∣ load` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Prim` |
| 1.14 | `Prim ::= … ∣ store` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Prim` |
| 1.15 | `Prim ::= … ∣ store v` | `[encoding]` | `Paper/S1_Syntax/Definitions.lean` | `Val.storeV` |
| 1.16 | `Expr ∋ e ::= x` | `[encoding]` | `Paper/S1_Syntax/Definitions.lean` | `Expr` |
| 1.17 | `Expr ::= … ∣ v` | `[encoding]` | `Paper/S1_Syntax/Definitions.lean` | `Expr.val` |
| 1.18 | `Expr ::= … ∣ (e₁, e₂)` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Expr` |
| 1.19 | `Expr ::= … ∣ inj₁ e` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Expr` |
| 1.20 | `Expr ::= … ∣ inj₂ e` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Expr` |
| 1.21 | `Expr ::= … ∣ e₁ ; e₂` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Expr` |
| 1.22 | `Expr ::= … ∣ let (x, y) = e₁ in e₂` | `[encoding]` | `Paper/S1_Syntax/Definitions.lean` | `Expr` |
| 1.23 | `Expr ::= … ∣ case e {inj₁ x.e₁ ∣ inj₂ y.e₂}` | `[encoding]` | `Paper/S1_Syntax/Definitions.lean` | `Expr` |
| 1.24 | `Expr ::= … ∣ e₂ e₁` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Expr` |
| 1.25 | `LifeVar ∋ 'a, 'b, …` | `[encoding]` | `Paper/S1_Syntax/Definitions.lean` | `Lifetime.LifeVar` |
| 1.26 | `Life ∋ @a, @b… ::= '` | `[encoding]` | `Paper/S1_Syntax/Definitions.lean` | `Lifetime.Life` |
| 1.27 | `Life ::= … ∣ ⊤` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Lifetime.Life` |
| 1.28 | `Life ::= … ∣ @a ⊔ @b` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Lifetime.Life` |
| 1.29 | `Life ::= … ∣ @a ⊓ @b` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Lifetime.Life` |
| 1.30 | `LifeCtx ∋ Δ : LifeVar ⇀ Life` | `[encoding]` | `Paper/S1_Syntax/Definitions.lean` | `Lifetime.LifeCtx` |
| 1.31 | `Type ∋ T ::= 𝟙` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Ty` |
| 1.32 | `Type ::= … ∣ T₁ ⊕ T₂` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Ty` |
| 1.33 | `Type ::= … ∣ T₁ ⊗ T₂` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Ty` |
| 1.34 | `Type ::= … ∣ T₁ ⊸ T₂` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Ty` |
| 1.35 | `Type ::= … ∣ Ref T` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Ty` |
| 1.36 | `Type ::= … ∣ [@a] T` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Ty` |
| 1.37 | `Type ::= … ∣ Imm @a T` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Ty` |
| 1.38 | `Type ::= … ∣ Mut @a T` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Ty` |
| 1.39 | `Type ::= … ∣ ∀ 'a ⊏ @b. T` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Ty` |
| 1.40 | `Type ::= … ∣ Unk` | `[as printed]` | `Paper/S1_Syntax/Definitions.lean` | `Ty` |
| 1.43 | — no printed counterpart — | `[about ours]` | `Support/Lifetimes/Substitution.lean`, `Support/Lifetimes/Terms.lean`, `Support/Syntax/Terms.lean` | `Expr.shift`, `Expr.subst`, `Lifetime.LSubst`, `Lifetime.Life.applySub`, `Lifetime.Life.depth`, `Lifetime.Life.mentions`, `Lifetime.Life.pp`, `Lifetime.Life.varBound`, `Lifetime.LifeCtx.dom`, `Lifetime.LifeCtx.pp`, `Lifetime.assocFind`, `Lifetime.varName`, `Ty.applyLSub`, `Ty.instLife`, `Ty.lifeBound`, `Val.shift`, `Val.subst` |
| 2.1 | `Δ; Γ ⊢ e : T` (boxed judgment form) | `[encoding]` | `Paper/S2_Statics/Definitions.lean` | `Derives` |
| 2.2 | ID: `Δ; x : T ⊢ x : T` | `[encoding]` | `Paper/S2_Statics/Definitions.lean` | `Derives` |
| 2.3 | 1I: `Δ; ● ⊢ () : 1` | `[encoding]` | `Paper/S2_Statics/Definitions.lean` | `Derives` |
| 2.4 | 1E: `Δ; Γ₁ ⊢ e₁ : 1`, `Δ; Γ₂ ⊢ e₂ : T` / `Δ; Γ₁,Γ₂ ⊢ e₁; e₂ : T` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `Derives` |
| 2.5 | ⊗I: `Δ; Γ₁ ⊢ e₁ : T₁`, `Δ; Γ₂ ⊢ e₂ : T₂` / `Δ; Γ₁,Γ₂ ⊢ (e₁,e₂) : T₁ ⊗ T₂` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `Derives` |
| 2.6 | ⊗E: `Δ; Γp ⊢ ep : T₁ ⊗ T₂`, `Δ; Γ, x₁:T₁, x₂:T₂ ⊢ e : T` / `Δ; Γp,Γ ⊢ let (x₁,x₂) = ep; e : T` | `[encoding]` | `Paper/S2_Statics/Definitions.lean` | `Derives` |
| 2.7 | ⊕I: `Δ; Γ ⊢ e : Tᵢ`, `i ∈ {1,2}` / `Δ; Γ ⊢ i e : T₁ ⊕ T₂` | `[encoding]` | `Paper/S2_Statics/Definitions.lean` | `Derives` |
| 2.8 | ⊕E: `Δ; Γs ⊢ es : T₁ ⊕ T₂`, `Δ; Γ, x_b : T_b ⊢ e_b : T` for `b ∈ {1,2}` / `Δ; Γs,Γ ⊢ match es {x₁ ⇒ e₁, x₂ ⇒ e₂} : T` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `Derives` |
| 2.9 | ⊸I: `Δ; Γ, x : T₁ ⊢ e : T₂` / `Δ; Γ ⊢ λx.e : T₁ ⊸ T₂` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `Derives` |
| 2.10 | ⊸E: `Δ; Γ₁ ⊢ e₁ : T₁`, `Δ; Γ₂ ⊢ e₂ : T₁ ⊸ T₂` / `Δ; Γ₁,Γ₂ ⊢ e₁ e₂ : T₂` | `[repair]` | `Paper/S2_Statics/Definitions.lean` | `Derives` |
| 2.11 | ∀I: `Δ, ('a ⊏ @b); Γ ⊢ e : T` / `Δ; Γ ⊢ Λ.e : ∀ 'a ⊏ @b. T` | `[repair]` | `Paper/S2_Statics/Definitions.lean` | `Derives` |
| 2.12 | ∀E: `Δ; Γ ⊢ e : ∀ 'a ⊏ @b. T`, `Δ ⊨ @a ⊏ @b` / `Δ; Γ ⊢ e[] : T[@a/'a]` | `[repair]` | `Paper/S2_Statics/Definitions.lean` | `Derives` |
| 2.13 | [l]I: `Δ; Γ ⊢ e : T`, `Δ ⊨ Γ ⊐ @a` / `Δ; Γ ⊢ □e : [@a] T` | `[repair]` | `Paper/S2_Statics/Definitions.lean` | `Derives` |
| 2.14 | [l]E: `Δ; Γ ⊢ □e : [@a] T` / `Δ; Γ ⊢ □e : T` | `[encoding]` | `Paper/S2_Statics/Definitions.lean` | `Derives` |
| 2.15 | alloc: `Δ; ● ⊢ alloc : T ⊸ Ref T` | `[encoding]` | `Paper/S2_Statics/Definitions.lean` | `Derives` |
| 2.16 | free: `Δ; ● ⊢ free : Ref T ⊸ T` | `[encoding]` | `Paper/S2_Statics/Definitions.lean` | `Derives` |
| 2.17 | ⊑Imm: `Δ; Γ ⊢ e : Imm @b T`, `Δ ⊨ @a ⊑ @b` / `Δ; Γ ⊢ e : Imm @b T` | `[repair]` | `Paper/S2_Statics/Definitions.lean` | `Derives` |
| 2.18 | ⊑Mut: `Δ; Γ ⊢ e : Mut @b T`, `Δ ⊨ @a ⊑ @b` / `Δ; Γ ⊢ e : Mut @b T` | `[repair]` | `Paper/S2_Statics/Definitions.lean` | `Derives` |
| 2.19 | `Δ ⊢ T` — "Presumes ⊨ Δ" (boxed judgment form) | `[encoding]` | `Paper/S2_Statics/Definitions.lean` | `WfTy` |
| 2.20 | `Δ ⊢ 1` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `WfTy` |
| 2.21 | `Δ ⊢ T₁`, `Δ ⊢ T₂` / `Δ ⊢ T₁ ⊗ T₂` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `WfTy` |
| 2.22 | `Δ ⊢ T₁`, `Δ ⊢ T₂` / `Δ ⊢ T₁ ⊕ T₂` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `WfTy` |
| 2.23 | `Δ ⊢ T₁`, `Δ ⊢ T₂` / `Δ ⊢ T₁ ⊸ T₂` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `WfTy` |
| 2.24 | `Δ ⊢ T` / `Δ ⊢ Ref T` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `WfTy` |
| 2.25 | `Δ, ('a ⊏ @b) ⊢ T`, `Δ ⊨ @b` / `Δ ⊢ ∀ ('a ⊏ @b).T` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `WfTy` |
| 2.26 | `Δ ⊢ T`, `Δ ⊨ @a` / `Δ ⊢ [@a] T` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `WfTy` |
| 2.27 | `Δ ⊢ T`, `Δ ⊨ @a` / `Δ ⊢ Imm @a T` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `WfTy` |
| 2.28 | `Δ ⊢ T`, `Δ ⊨ @a` / `Δ ⊢ Mut @a T` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `WfTy` |
| 2.29 | no rule for `Unk` anywhere in `Δ ⊢ T` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `WfTy` |
| 2.30 | `Δ ⊢ T ⊐ @a` — "Presumes ⊨ Δ and Δ ⊨ @a" (boxed judgment form) | `[encoding]` | `Paper/S2_Statics/Definitions.lean` | `Outlives`, `OutlivesRules` |
| 2.31 | `Δ ⊢ 1 ⊐ @a` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `OutlivesRules` |
| 2.32 | `Δ ⊢ T₁ ⊐ @a`, `Δ ⊢ T₂ ⊐ @a` / `Δ ⊢ T₁ ⊗ T₂ ⊐ @a` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `OutlivesRules` |
| 2.33 | `Δ ⊢ T₁ ⊐ @a`, `Δ ⊢ T₂ ⊐ @a` / `Δ ⊢ T₁ ⊕ T₂ ⊐ @a` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `OutlivesRules` |
| 2.34 | `Δ ⊢ T ⊐ @a` / `Δ ⊢ Ref T ⊐ @a` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `OutlivesRules` |
| 2.35 | `Δ ⊨ @b ⊐ @a` / `Δ ⊢ [@b] T ⊐ @a` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `OutlivesRules` |
| 2.36 | `Δ ⊨ @b ⊐ @a` / `Δ ⊢ Imm @b T ⊐ @a` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `OutlivesRules` |
| 2.37 | `Δ ⊨ @b ⊐ @a` / `Δ ⊢ Mut @b T ⊐ @a` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `OutlivesRules` |
| 2.38 | the axiom table's left column: `Δ ⊢ <term> : <type>`, with no Γ and no premise column | `[encoding]` | `Paper/S2_Statics/Definitions.lean` | `Ctx.Dead`, `Derives` |
| 2.39 | `Δ ⊢ swap : Ref T₁ ⊸ T₂ ⊸ Ref T₂ ⊗ T₁` | `[repair]` | `Paper/S2_Statics/Definitions.lean` | `Derives`, `axSwapTy`, `swap` |
| 2.40 | `Δ ⊢ copy : Imm @a T ⊸ Imm @a T ⊗ Imm @a T` | `[encoding]` | `Paper/S2_Statics/Definitions.lean` | `Derives`, `axCopyTy` |
| 2.41 | `Δ ⊢ forget : Imm @a T ⊸ 1` | `[encoding]` | `Paper/S2_Statics/Definitions.lean` | `Derives`, `axForgetImmTy` |
| 2.42 | `Δ ⊢ forget : Mut @a T ⊸ 1` | `[encoding]` | `Paper/S2_Statics/Definitions.lean` | `Derives`, `axForgetMutTy` |
| 2.43 | `Δ ⊢ forget : Unk ⊸ 1` | `[encoding]` | `Paper/S2_Statics/Definitions.lean` | `Derives`, `axForgetUnkTy` |
| 2.44 | `Δ ⊢ withbor : Ref T₁ ⊸ (∀ 'a ⊏ ⊓Δ. Imm 'a T₁ ⊸ ['a] T₂) ⊸ Ref T₁ ⊗ T₂` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `Derives`, `axWithbor1Ty`, `withbor` |
| 2.45 | `Δ ⊢ withbor : Ref T₁ ⊸ (∀ 'a ⊏ ⊓Δ. Mut 'a T₁ ⊸ ['a] T₂) ⊸ Ref T₁ ⊗ T₂`, side condition `Δ ⊢ T₁ ⊐ @b` on this line | `[repair]` | `Paper/S2_Statics/Definitions.lean` | `Derives`, `axWithbor2Ty` |
| 2.46 | `Δ ⊢ withbor : Mut @a T₁ ⊸ (∀ 'b ⊏ ⊓Δ. Mut 'b T₁ ⊸ ['b] T₂) ⊸ Mut @a T₁ ⊗ T₂` | `[repair]` | `Paper/S2_Statics/Definitions.lean` | `Derives`, `axWithbor3Ty` |
| 2.47 | `Δ ⊢ withload : Imm @a T₁ ⊸ (∀ 'b ⊏ ⊓Δ. Imm̲ 'b T₁ ⊸ ['b] T₂) ⊸ T₂` (leading `Imm` UNDERLINED) | `[repair]` | `Paper/S2_Statics/Definitions.lean` | `Derives`, `axWithloadTy`, `withload` |
| 2.48 | `Δ ⊢ withswap : Mut @a T₁ ⊸ (T₁ ⊸ T₁ ⊗ T₂) ⊸ Mut @a T₁ ⊗ T₂` | `[encoding]` | `Paper/S2_Statics/Definitions.lean` | `Derives`, `axWithswapTy` |
| 2.49 | `Imm̲ 'b 1 ≜ 1`; `Imm̲ 'b (T₁⊕T₂)`; `Imm̲ 'b (T₁⊗T₂)`; `Imm̲ 'b (T₁⊸T₂) ≜ Unk`; `Imm̲ 'b (Ref T) ≜ Imm 'b T`; `Imm̲ 'b (Imm @a T) ≜ Imm @a T`; `Imm̲ 'b ([@a]T) ≜ Imm̲ 'b T`; `Imm̲ 'b (∀ '.a ⊏ @a. T) ≜ Unk` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `Ty.immReborrow` |
| 2.50 | — no printed clause — | `[repair]` | `Paper/S2_Statics/Definitions.lean` | `Ty.immReborrow` |
| 2.51 | `LSub ∋ δ : LifeVar ⇀ Life` | `[encoding]` | `Paper/S2_Statics/Definitions.lean` | `Lifetime.LSub` |
| 2.52 | `⟦Δ⟧ ≜ {δ ∣ dom(Δ) ⊆ dom(δ) ∧ ∀'a ∈ dom(Δ). δ('a) ⊏ Δ('a)δ}` | `[encoding]` | `Paper/S2_Statics/Definitions.lean` | `Lifetime.LifeCtx.Models` |
| 2.53 | `⊨ Δ ≜ ⟦Δ⟧ ≠ ∅` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `Lifetime.LifeCtx.Sat` |
| 2.54 | `@aδ ≜ δ('a)`, `⊤`, `@b₁δ ⊓ @b₂δ` at `@a = @b₁ ⊔ @b₂`, `@b₁δ ⊔ @b₂δ` at `@a = @b₁ ⊔ @b₂` | `[repair]` | `Paper/S2_Statics/Definitions.lean` | `Lifetime.Life.interp` |
| 2.55 | `Δ ⊨ @a ≜ ∀δ ∈ ⟦Δ⟧. @aδ defined` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `Lifetime.LifeCtx.Defines` |
| 2.56 | `Δ ⊨ @a ⊏ @b ≜ ∀δ ∈ ⟦Δ⟧. @aδ ⊏ @bδ` | `[as printed]` | `Paper/S2_Statics/Definitions.lean` | `Lifetime.LifeCtx.EntailsLt` |
| 2.57 | `Δ ⊨ @a ⊑ @b` — premise of ⊑Imm and ⊑Mut, NEVER DEFINED | `[encoding]` | `Paper/S2_Statics/Definitions.lean` | `Lifetime.LifeCtx.EntailsLe` |
| 2.58 | `Δ ⊨ Γ ⊐ @a` — premise of [l]I, NEVER DEFINED | `[repair]` | `Paper/S2_Statics/Definitions.lean` | `Ctx.Outlives` |
| 2.59 | `⊓Δ` — the ∀ bound in all three `withbor` forms and in `withload`, never defined as an operation | `[encoding]` | `Paper/S2_Statics/Definitions.lean` | `Lifetime.LifeCtx.freshVar`, `Lifetime.LifeCtx.meetOfDom`, `Lifetime.meetOfDomL` |
| 3.1 | `Kont ∋ K ::= [ ]` | `[as printed]` | `Paper/S3_Dynamics/Definitions.lean` | `BoLo.Kont`, `TR3.Kont` |
| 3.2 | `Kont ::= … ∣ (K, e)` | `[as printed]` | `Paper/S3_Dynamics/Definitions.lean` | `BoLo.Kont`, `TR3.Kont` |
| 3.3 | `Kont ::= … ∣ (v, K)` | `[encoding]` | `Paper/S3_Dynamics/Definitions.lean` | `BoLo.Kont`, `TR3.Kont` |
| 3.4 | `Kont ::= … ∣ let (x, y) = K in e` | `[encoding]` | `Paper/S3_Dynamics/Definitions.lean` | `BoLo.Kont`, `TR3.Kont` |
| 3.5 | `Kont ::= … ∣ case K {inj₁ x.e₁ ∣ inj₂ y.e₂}` | `[encoding]` | `Paper/S3_Dynamics/Definitions.lean` | `BoLo.Kont`, `TR3.Kont` |
| 3.6 | `Kont ::= … ∣ e K` | `[as printed]` | `Paper/S3_Dynamics/Definitions.lean` | `BoLo.Kont`, `TR3.Kont` |
| 3.7 | `Kont ::= … ∣ K v` | `[encoding]` | `Paper/S3_Dynamics/Definitions.lean` | `BoLo.Kont`, `TR3.Kont` |
| 3.8 | `K[e]` (used in the context rule; the grammar fixes it implicitly) | `[encoding]` | `Paper/S3_Dynamics/Definitions.lean` | `BoLo.Kont.plug`, `TR3.Kont.plug` |
| 3.9 | `Mem ∋ µ : Loc ⇀ Val` | `[encoding]` | `Paper/S3_Dynamics/Definitions.lean` | `BoLo.Heap` |
| 3.10 | `Mem ∋ µ : Loc ⇀ Val` (the executable counterpart) | `[repair]` | `Support/Dynamics/Interpreter.lean` | `Mem` |
| 3.11 | the boxed judgments `(µ,e) → (µ′,e′)` and `(µ,e) ↦ (µ′,e′)` | `[encoding]` | `Paper/S3_Dynamics/Definitions.lean` | `BoLo.Head`, `BoLo.Step1`, `TR3.Head`, `TR3.Step1` |
| 3.12 | →: `(µ,e) ↦ (µ′,e′)` / `(µ, K[e]) → (µ′, K[e′])` | `[encoding]` | `Paper/S3_Dynamics/Definitions.lean` | `BoLo.Step1`, `TR3.Step1` |
| 3.13 | 1↦: `(µ, (); e) ↦ (µ, e)` | `[encoding]` | `Paper/S3_Dynamics/Definitions.lean` | `TR3.Head` |
| 3.14 | 1↦: `(µ, (); e) ↦ (µ, e)` | `[as printed]` | `Paper/S3_Dynamics/Definitions.lean` | `BoLo.Head` |
| 3.15 | ⊗↦: `(µ, let (x₁,x₂) = (v₁,v₂) in e) ↦ (µ, e[v₁/x₁, v₂/x₂])` | `[encoding]` | `Paper/S3_Dynamics/Definitions.lean` | `BoLo.Head`, `TR3.Head` |
| 3.16 | ⊕↦: `(µ, case (injᵢ v) {inj₁ x.e₁ ∣ inj₂ y.e₂}) ↦ (µ, eᵢ[v/xᵢ])` | `[encoding]` | `Paper/S3_Dynamics/Definitions.lean` | `BoLo.Head`, `TR3.Head` |
| 3.17 | ⊸↦: `(µ, (λx.e) v) ↦ (µ, e[v/x])` | `[encoding]` | `Paper/S3_Dynamics/Definitions.lean` | `BoLo.Head`, `TR3.Head` |
| 3.18 | alloc↦: `(µ, alloc v) ↦ (µ ⊎ ℓ ↦ v, ℓ)` | `[encoding]` | `Paper/S3_Dynamics/Definitions.lean` | `BoLo.Head`, `TR3.Head` |
| 3.19 | free↦: `(µ ⊎ ℓ ↦ v, free ℓ) ↦ (µ, v)` | `[encoding]` | `Paper/S3_Dynamics/Definitions.lean` | `BoLo.Head`, `TR3.Head` |
| 3.20 | load↦: `µ(ℓ) = v` / `(µ, load ℓ) ↦ (µ, v)` | `[encoding]` | `Paper/S3_Dynamics/Definitions.lean` | `BoLo.Head`, `TR3.Head` |
| 3.21 | store↦: `ℓ ∈ dom(µ)` / `(µ, store ℓ v) ↦ (µ[ℓ ↦ v], ())` | `[encoding]` | `Paper/S3_Dynamics/Definitions.lean` | `BoLo.Head` |
| 3.22 | store↦: `ℓ ∈ dom(µ)` / `(µ, store ℓ v) ↦ (µ[ℓ ↦ v], ())` | `[encoding]` | `Paper/S3_Dynamics/Definitions.lean` | `TR3.Head` |
| 3.23 | `µ[ℓ ↦ v]` (in store↦) | `[as printed]` | `Paper/S3_Dynamics/Definitions.lean` | `BoLo.Heap.upd` |
| 3.24 | `swap ≜ λx.λy.let z = load x; store x y; (x, y)` | `[repair]` | `Paper/S2_Statics/Definitions.lean` | `swap` |
| 3.25 | `copy ≜ λx.(x, x)` | `[encoding]` | `Paper/S3_Dynamics/Definitions.lean` | `copy` |
| 3.26 | `forget ≜ λx.()` | `[encoding]` | `Paper/S3_Dynamics/Definitions.lean` | `forget` |
| 3.27 | `withbor ≜ λx.λf.(x, f x)` | `[repair]` | `Paper/S2_Statics/Definitions.lean` | `withbor` |
| 3.28 | `withload ≜ λx.λf.(x, f (load x))` | `[repair]` | `Paper/S2_Statics/Definitions.lean` | `withload` |
| 3.29 | `withswap ≜ λx.λf.let (y, z) = f (load x); store x y; (x, z)` | `[encoding]` | `Paper/S3_Dynamics/Definitions.lean` | `withswap` |
| 3.30 | — no printed counterpart in §3 — | `[repair]` | `Paper/S3_Dynamics/Definitions.lean` | `BoLo.Kont` |
| 3.31 | — no printed counterpart in §3 — | `[repair]` | `Paper/S3_Dynamics/Definitions.lean` | `BoLo.Kont` |
| 3.34 | — no printed counterpart — | `[about ours]` | `Support/Dynamics/Machine.lean` | `BoLo.Kont.comp`, `TR3.Kont.comp` |
| 3.35 | — §3 prints no closure; `⟶*` appears only from §6.7 on — | `[about ours]` | `Support/Dynamics/Machine.lean` | `BoLo.Steps`, `TR3.Steps` |
| 3.36 | — no printed counterpart; [TR] §1 prints only `let (x,y) = e₁ in e₂` — | `[repair]` | `Paper/S3_Dynamics/Definitions.lean` | `elet`, `lam2` |
| 3.37 | — no printed counterpart; the print gives a relation — | `[repair]` | `Support/Dynamics/Interpreter.lean` | `delta`, `eval`, `run`, `step` |
| 4.1 | `𝒱⟦1⟧δ(v) ≜ ⌜v = ()⌝` | `[as printed]` | `Paper/S4_LogicalRelation/Definitions.lean` | `Fig16.LogRel.vDen`, `Fig16.LogRel.vDen_unit` |
| 4.2 | `𝒱⟦T₁ ⊗ T₂⟧δ(v) ≜ ∃v₁,v₂. ⌜v = (v₁,v₂)⌝ ⋆ 𝒱⟦T₁⟧δ(v₁) ⋆ 𝒱⟦T₂⟧δ(v₂)` | `[as printed]` | `Paper/S4_LogicalRelation/Definitions.lean` | `Fig16.LogRel.vDen_tensor` |
| 4.3 | `𝒱⟦T₁ ⊕ T₂⟧δ(v) ≜ (∃v₁. ⌜v = inj₁ v₁⌝ ⋆ 𝒱⟦T₁⟧δ(v₁)) ∨ (∃v₂. ⌜v = inj₂ v₂⌝ ⋆ 𝒱⟦T₂⟧δ(v₂))` | `[as printed]` | `Paper/S4_LogicalRelation/Definitions.lean` | `Fig16.LogRel.vDen_sum` |
| 4.4 | `𝒱⟦T₁ ⊸ T₂⟧δ(v) ≜ ∀v′. 𝒱⟦T₁⟧δ(v′) ─⋆ ℰ⟦T₂⟧δ(v v′)` | `[repair]` | `Paper/S4_LogicalRelation/Definitions.lean`, `Support/TypedWorld/Relation.lean` | `Fig16.LogRel.Typed.vX`, `Fig16.LogRel.vDen_lolli` |
| 4.5 | `𝒱⟦∀ 'a ⊏ @b. T⟧δ(v) ≜ ∀ α ⊏ @bδ. ℰ⟦T⟧δ(v ())` | `[repair]` | `Paper/S4_LogicalRelation/Definitions.lean`, `Support/TypedWorld/Relation.lean` | `Fig16.LogRel.Typed.vX`, `Fig16.LogRel.vDen_all` |
| 4.6 | `𝒱⟦[@a] T⟧δ(v) ≜ [@aδ] 𝒱⟦T⟧δ(v)` | `[encoding]` | `Paper/S4_LogicalRelation/Definitions.lean` | `Fig16.LogRel.atLife`, `Fig16.LogRel.vDen_box` |
| 4.7 | `𝒱⟦Ref T⟧δ(v) ≜ ∃ℓ,v′. ⌜v = ℓ⌝ ⋆ ℓ ↦ v′ ⋆ 𝒱⟦T⟧δ(v′)` | `[as printed]` | `Paper/S4_LogicalRelation/Definitions.lean` | `Fig16.LogRel.vDen_ref` |
| 4.8 | `𝒱⟦Imm @a T⟧δ(v) ≜ ∃ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦ Imm @aδ 𝒱⟦T⟧δ` | `[repair]` | `Paper/S4_LogicalRelation/Definitions.lean`, `Support/TypedWorld/Relation.lean` | `Fig16.LogRel.Typed.CohE`, `Fig16.LogRel.Typed.ptoImmS`, `Fig16.LogRel.Typed.vX`, `Fig16.LogRel.vDen_imm` |
| 4.9 | `𝒱⟦Mut @a T⟧δ(v) ≜ ∃ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦ Mut @aδ 𝒱⟦T⟧δ` | `[repair]` | `Paper/S4_LogicalRelation/Definitions.lean`, `Support/TypedWorld/Relation.lean` | `Fig16.LogRel.Typed.ptoMutS`, `Fig16.LogRel.Typed.vX`, `Fig16.LogRel.vDen_mut` |
| 4.10 | `𝒱⟦Unk⟧δ(v) ≜ emp` | `[as printed]` | `Paper/S4_LogicalRelation/Definitions.lean` | `Fig16.LogRel.vDen_unk` |
| 4.11 | `ℰ⟦T⟧δ(v) ≜ wp (e) {𝒱⟦T⟧δ}` | `[repair]` | `Paper/S4_LogicalRelation/Definitions.lean`, `Support/TypedWorld/World.lean` | `Fig16.LogRel.Typed.wpTS`, `Fig16.LogRel.eDen` |
| 4.12 | `𝒟⟦Δ⟧(δ) ≜ ⌜δ ∈ ⟦Δ⟧⌝` | `[encoding]` | `Paper/S2_Statics/Definitions.lean`, `Paper/S4_LogicalRelation/Definitions.lean` | `Fig16.LogRel.dDen`, `Lifetime.LifeCtx.Models` |
| 4.13 | `𝒢⟦Γ⟧(γ) ≜ ⌜dom(Γ) ⊆ dom(δ)⌝ ⋆ ⊛_{x∈dom(Γ)} 𝒱⟦Γ(x)⟧δ(γ(x))` | `[repair]` | `Paper/S4_LogicalRelation/Definitions.lean`, `Support/TypedWorld/Relation.lean` | `Ctx.LiveWithin`, `Fig16.LogRel.Typed.gDenX`, `Fig16.LogRel.Typed.gSepX`, `Fig16.LogRel.gDen`, `Fig16.LogRel.gSep` |
| 4.14 | `Δ; Γ ⊨ e : T ≜ !∀ δ,γ. 𝒟⟦Δ⟧(δ) ─⋆ 𝒢⟦Γ⟧δ(γ) ─⋆ ℰ⟦T⟧δ(γ(e))` | `[repair]` | `Paper/S4_LogicalRelation/Definitions.lean`, `Support/TypedWorld/Relation.lean` | `Fig16.LogRel.SemTy`, `Fig16.LogRel.Typed.SemX` |
| 4.15 | — no printed counterpart — | `[repair]` | `Paper/S4_LogicalRelation/Definitions.lean` | `Fig16.LogRel.LtLife`, `Fig16.LogRel.atLife` |
| 4.16 | — no printed counterpart — | `[repair]` | `Paper/S4_LogicalRelation/Definitions.lean`, `Paper/S4_LogicalRelation/Remarks.lean` | `Fig16.LogRel.Supported`, `Fig16.LogRel.supported_iff`, `Fig16.LogRel.vDen_mut_of_supported`, `Fig16.LogRel.vDen_mut_supported` |
| 4.17 | — no printed counterpart — | `[repair]` | `Paper/LiteralReadings/S4_LogicalRelation.lean` | `Fig16.LogRel.MutPayloadSubst.Tpayload`, `Fig16.LogRel.MutImmCell.cell`, `Fig16.LogRel.MutImmCell.inRel_same`, `Fig16.LogRel.MutImmCell.lset` |
| 4.18 | — no printed counterpart — | `[about ours]` | `Paper/S4_LogicalRelation/Remarks.lean`, `Support/LogicalRelation/ClosedJudgment.lean` | `Fig16.LogRel.Sem`, `Fig16.LogRel.sem_iff` |
| 5.1 | `SProp_α ≜ Res_α → ℙ` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.SProp` |
| 5.2 | `Res_α ≜ Loc ⇀ Cell_α` | `[repair]` | `Paper/S5_Model/Definitions.lean` | `Fig16.PMap`, `Fig16.Res` |
| 5.3 | `Cell_α ≜ own(Val) + imm(Imm_α) + mut(Mut_α)` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.Cell`, `Fig16.CellF`, `Fig16.Cell_eq` |
| 5.4 | `Imm_α ≜ {(ᾱ : ℘⁺(Life), v : Val, ρ : Res_⊔ᾱ) ∣ ⊓ᾱ ⊐ α}` | `[encoding]` | `Paper/S5_Model/Definitions.lean` | `Fig16.Imm`, `Fig16.ImmF` |
| 5.5 | `Mut_α ≜ {(β ⊐ α, v : Val, ρ : Res_β, P̂ : Val → SProp_β) ∣ P̂(v)(ρ)}` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.Mut`, `Fig16.MutF` |
| 5.6 | `P ∈ SProp ≜ Res → ℙ` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.SPropU` |
| 5.7 | `ρ ∈ Res ≜ Loc ⇀ᶠⁱⁿ Cell` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.PMap`, `Fig16.ResU` |
| 5.8 | `ψ ∈ Cell ≜ ⋃_α Cell_α` | `[encoding]` | `Paper/S5_Model/Definitions.lean` | `Fig16.CellU`, `Fig16.ImmU`, `Fig16.MutU` |
| 5.9 | `α, β ∈ Life ≜ (ℕ, ⊑ ≜ >, ⊔ ≜ min, ⊓ ≜ max, ⊤ ≜ 0)` | `[repair]` | `Paper/S5_Model/Definitions.lean` | `Fig16.Life`, `Fig16.Life.Sqsubset`, `Fig16.Life.Sqsupset`, `Fig16.Life.join`, `Fig16.Life.meet`, `Fig16.Life.top` |
| 5.10 | `@ψ ≜ ⊤` if own; `α` if `mut(α,_,_,_)`; `⊓ᾱ` if `imm(ᾱ,_,_,_)` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.CellU.at` |
| 5.11 | `@ρ ≜ ⊓_{ψ ∈ cod(ρ)} @ψ` | `[encoding]` | `Paper/S5_Model/Definitions.lean` | `Fig16.ResU.AtLife`, `Fig16.ResU.at`, `Fig16.ResU.atLife_atOn` |
| 5.12 | `↓α ≜ α + 1` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.Life.down` |
| 5.13 | `ψ₁ ▸◂ ψ₂ ≜ ∃ᾱ₁,ᾱ₂,v,ρ. ψ₁ = imm(ᾱ₁,v,ρ) ∧ ψ₂ = imm(ᾱ₂,v,ρ)` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.CellU.CompatS` |
| 5.14 | `ψ₁ ▷◁ ψ₂ ≜ ψ₁ ▸◂ ψ₂ ∨ ∃i,ᾱ,β,v,ρ,P̂. {ψ₁,ψ₂} ∈ {imm(ᾱ,v,ρ), own(v), mut(β,v,ρ,P̂)}` | `[repair]` | `Paper/S5_Model/Definitions.lean` | `Fig16.CellU.CompatR` |
| 5.15 | `ψ₁ ● ψ₂ ≜ imm(ᾱ₁ ∪ ᾱ₂, v, ρ)` when both are `imm` at the same `v`, ρ | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.CellU.CompS`, `Fig16.CellU.compS`, `Fig16.CellU.compS_immOf` |
| 5.16 | `ψ₁ ○ ψ₂ ≜` five clauses (`ψ₁`; `ψ₁ ● ψ₂`; `mut(α⊓β,v,ρ,P̂∧Q̂)`; `ψᵢ`; `ψᵢ`) | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.CellU.CompR` |
| 5.17 | `ρ₁ ▸◁ ρ₂ ≜ ∀ℓ ∈ dom(ρ₁) ∩ dom(ρ₂). ρ₁(ℓ) ▸◁ ρ₂(ℓ)` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.ResU.Compat`, `Fig16.ResU.CompatR`, `Fig16.ResU.CompatS` |
| 5.18 | `ρ₁ ◖ ρ₂ ≜ ρ₁/dom(ρ₂) ⊎ ρ₂/dom(ρ₁) ⊎ [ℓ ↦ ψ₁ ◖ ψ₂ ∣ …]`, guarded by `ρ₁ ▸◁ ρ₂` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.OptComp`, `Fig16.ResU.Comp`, `Fig16.ResU.CompR`, `Fig16.ResU.CompS`, `Fig16.ResU.compR`, `Fig16.ResU.compS` |
| 5.19 | `ρ∣ι ≜ [ℓ ↦ ψ ∣ ρ(ℓ) = ψ = ι(…)]`, `ι ∈ {own, mut, imm}` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.ResU.restrict` |
| 5.20 | `ex(ρ)_◖ ≜ ρ∣own ◖ ρ∣mut ◖ ⨀{ex(ρ′)_◖ ∣ ∃ℓ. ρ(ℓ) = mut(_,_,ρ′,_)}` | `[repair]` | `Paper/S5_Model/Definitions.lean` | `Fig16.ExR`, `Fig16.ExS`, `Fig16.ExW` |
| 5.21 | `ag(ρ)_◖ ≜ ρ∣imm ○ ◯{ag(ρ′) ∣ …mut…} ○ ◯{ex(ρ′)_○ ○ ag(ρ′) ∣ …imm…}` | `[repair]` | `Paper/S5_Model/Definitions.lean` | `Fig16.AgW` |
| 5.22 | `⦇ρ⦈ ≜ ex(ρ)_● ● ag(ρ)` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.ResU.Flat` |
| 5.23 | `✓ρ ≜ ⦇ρ⦈ defined` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.ResU.Valid` |
| 5.24 | `⟦ψ⟧ ≜ v` when `ψ` is `own(v)`, `mut(_,v,_,_)` or `imm(_,v,_)` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.CellU.erase` |
| 5.25 | `⟦ρ⟧ ≜ [ℓ ↦ v ∣ ⟦⦇ρ⦈(ℓ)⟧ = v]`, `✓ρ` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.ResU.Lower` |
| 5.26 | `ρ₁ # ρ₂ ≜ ρ₁ ▸◂ ρ₂ ∧ ✓(ρ₁ ● ρ₂)` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.ResU.Hash` |
| 5.27 | `ρ₁ ↭ ρ₂ ≜ {∀ℓ,… (⦇ρ₁⦈(ℓ)=mut(α,_,_,P̂) ⇔ ⦇ρ₂⦈(ℓ)=mut(α,_,_,P̂)) ∧ (⦇ρ₁⦈(ℓ)=imm(β̄,v,ρ) ⇔ ⦇ρ₂⦈(ℓ)=mut(β̄,v,ρ))}`, `✓ρ₁ ∧ ✓ρ₂` | `[repair]` | `Paper/S5_Model/Definitions.lean` | `Fig16.ResU.Upd`, `Fig16.ResU.UpdImm`, `Fig16.ResU.UpdMut`, `Fig16.ResU.UpdV` |
| 5.28 | `reb_α(ρ) ≜ {ρ′ ∣ @ρ ⊐ α ∧ ∃π : dom(ρ′) → Res. ρ ≥ ⨀_● π(ℓ) ∧ …}` | `[repair]` | `Paper/S5_Model/Definitions.lean` | `Fig16.ResU.Reb`, `Fig16.ResU.RebAt` |
| 5.29 | `ℓ ↦ v  (ρ) ≜ ρ = ℓ ↦ own(v)` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.BoLo.ptoOwn` |
| 5.30 | `ℓ ↦ Imm α P̂  (ρ) ≜ ∃β̄,v,ρ′. ρ = ℓ ↦ imm(β̄,v,ρ′) ∧ P̂(v)(ρ′) ∧ α ⊑ ⊔β̄` | `[repair]` | `Paper/S5_Model/Definitions.lean` | `Fig16.BoLo.ptoImm` |
| 5.31 | `ℓ ↦ Mut α P̂  (ρ) ≜ ∃β ⊒ α, v, ρ′. ρ = ℓ ↦ mut(β,v,ρ′,P̂)` | `[repair]` | `Paper/S5_Model/Definitions.lean` | `Fig16.BoLo.ptoMut` |
| 5.32 | `[α] P  (ρ) ≜ P(ρ) ∧ @ρ ⊐ α` | `[repair]` | `Paper/S5_Model/Definitions.lean` | `Fig16.BoLo.Outlives`, `Fig16.BoLo.box` |
| 5.33 | `wp (e) {Q̂} (ρ) ≜ ∀ρ_f # ρ. ∃ρ′ # ρ_f, ρ⁺ # (ρ_f ● ρ′), v. (⟦ρ_f ● ρ⟧,e) →* (⟦ρ_f ● ρ′ ● ρ⁺⟧,v) ∧ ρ ↭ ρ′ ● ρ⁺ ∧ ρ⁺∣own = ∅ ∧ Q̂(v)(ρ′)` | `[repair]` | `Paper/S5_Model/Definitions.lean`, `Support/TypedWorld/World.lean` | `Fig16.BoLo.wp`, `Fig16.LogRel.Typed.TW`, `Fig16.LogRel.Typed.Tagged`, `Fig16.LogRel.Typed.wpTS` |
| 5.34 | `⌜P_Meta⌝ (ρ) ≜ ρ = ∅ ∧ P_Meta` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.BoLo.pure` |
| 5.35 | `P₁ ⋆ P₂ (ρ) ≜ ∃ρ₁,ρ₂. ρ = ρ₁ ● ρ₂ ∧ P₁(ρ₁) ∧ P₂(ρ₂)` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.BoLo.sep` |
| 5.36 | `P₁ –⋆ P₂ (ρ) ≜ ∀ρ₁,ρ₂. P₁(ρ₁) ⇒ ρ ● ρ₁ = ρ₂ ⇒ P₂(ρ₂)` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.BoLo.wand` |
| 5.37 | `emp ≜ ⌜⊤⌝` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.BoLo.emp` |
| 5.38 | `!P ≜ emp ∧ P` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.BoLo.bang` |
| 5.39 | `⊤ (ρ) ≜ ⊤` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.BoLo.top` |
| 5.40 | `⊥ (ρ) ≜ ⊥` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.BoLo.bot` |
| 5.41 | `P₁ ∧ P₂ (ρ) ≜ P₁(ρ) ∧ P₂(ρ)` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.BoLo.and` |
| 5.42 | `P₁ ∨ P₂ (ρ) ≜ P₁(ρ) ∨ P₂(ρ)` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.BoLo.or` |
| 5.43 | `P₁ ⇒ P₂ (ρ) ≜ P₁(ρ) ⇒ P₂(ρ)` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.BoLo.imp` |
| 5.44 | `∀ P̂ (ρ) ≜ ∀x. P̂(x)(ρ)` | `[encoding]` | `Paper/S5_Model/Definitions.lean` | `Fig16.BoLo.all` |
| 5.45 | `∃ P̂ (ρ) ≜ ∃x. P̂(x)(ρ)` | `[encoding]` | `Paper/S5_Model/Definitions.lean` | `Fig16.BoLo.ex` |
| 5.46 | `И P̂ ≜ ∃β. ∀α ⊏ β. [α] P̂(α)` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.BoLo.fresh` |
| 5.47 | `↺_α P (ρ) ≜ ∃ρ′ ∈ reb_α(ρ). P(ρ′)` | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.BoLo.reborrow` |
| 5.48 | — presupposed, never written — | `[repair]` | `Paper/S5_Model/Definitions.lean` | `Fig16.Cell.stratumEquiv`, `Fig16.CellU.InStratum`, `Fig16.Res.stratumEquiv`, `Fig16.ResU.InStratum` |
| 5.49 | — tags named only inside `ι ∈ {own, mut, imm}` — | `[about ours]` | `Paper/S5_Model/Definitions.lean`, `Support/Model/Prelude.lean` | `Fig16.CellU.kind`, `Fig16.Kind` |
| 5.50 | — no printed counterpart — | `[about ours]` | `Paper/S5_Model/Definitions.lean` | `Fig16.CellU.wit` |
| 5.51 | — `ρ∣own,mut` is used from [TR] Def. 6.3 on with no defining row — | `[repair]` | `Paper/S5_Model/Definitions.lean` | `Fig16.ResU.exclPart`, `Fig16.ResU.restrictOn` |
| 5.52 | `ℓ ↦ ψ` — used from [TR] Lemma 6.17 on, defined nowhere | `[repair]` | `Paper/S5_Model/Definitions.lean` | `Fig16.ResU.single` |
| 5.53 | `ρ/ℓ` — the `/` of `ρ₁/dom(ρ₂)` and of `π(ℓ)/ℓ` | `[repair]` | `Paper/S5_Model/Definitions.lean` | `Fig16.ResU.del` |
| 5.54 | `ρ₁ ≤ ρ₃ ≜ ∃ρ₂ ▶◀ ρ₁. ρ₁ ● ρ₂ = ρ₃` — `≥` used in `reb_α`, `≤` in [TR] Def. 6.3 | `[as printed]` | `Paper/S5_Model/Definitions.lean` | `Fig16.ResU.Le` |
| 5.55 | — the index set of the `ex`/`ag` comprehensions and of `dom(ρ′)` — | `[repair]` | `Paper/S5_Model/Definitions.lean` | `Fig16.ResU.Dom`, `Fig16.ResU.Sites` |
| 5.56 | `⨀` — the iterated composition, with no printed empty case | `[repair]` | `Paper/S5_Model/Definitions.lean`, `Paper/S6_1_StandardLemmas/Lemmas.lean` | `Fig16.BigComp`, `Fig16.BigComp.perm` |
| 5.57 | — the paper's `SProp_α ⊆ SProp_{α′} ⊆ SProp` is a set inclusion — | `[repair]` | `Paper/S5_Model/Definitions.lean` | `Fig16.BoLo.ofS`, `Fig16.SPropS.conj`, `Fig16.SPropS.embed`, `Fig16.SPropS.toU`, `Fig16.SPropS.toU_range`, `Fig16.SPropU.toS` |
| 5.58 | — neither document prints the recursion, only the measure — | `[repair]` | `Paper/S5_Model/Definitions.lean` | `Fig16.Cell`, `Fig16.Cell.ofF`, `Fig16.Cell.toF`, `Fig16.Cell_eq` |
| 5.59 | — ⊑ appears in [TR] p. 4 row 9 as the STRICT `>` — | `[repair]` | `Paper/S5_Model/Definitions.lean` | `Fig16.Life.Sqsubseteq` |
| 5.60 | `⦇ρ⦈(ℓ)` — an application of a partial term | `[repair]` | `Paper/S5_Model/Definitions.lean` | `Fig16.ResU.FlatAt` |
| 5.61 (Definition 6.1) | `⦇ρ⦈_○ ≜ ag(ρ) ○ ex(ρ)_○` — [TR] Definition 6.1, not a p. 5 row | `[as printed]` | `Paper/S6_2_NonStandardLemmas/Definitions.lean` | `Fig16.ResU.FlatR` |
| 5.62 | — [CONF] Fig. 18b's unguarded ↭, and the `wp` row read at it — | `[repair]` | `Paper/S5_Model/Definitions.lean`, `Paper/S5_Model/Remarks.lean` | `Fig16.BoLo.wpU`, `Fig16.BoLo.wp_eq_wpU`, `Fig16.ResU.Upd` |
| 5.63 | `ρ⁺∣own = ∅` is named; `ℓ ↦ _` has no printed counterpart | `[repair]` | `Paper/S5_Model/Definitions.lean` | `Fig16.BoLo.NoOwn`, `Fig16.BoLo.noOwn_compS`, `Fig16.BoLo.ptoAny` |
| 5.64 | `ρ∣dom(ρ′)` — a domain restriction, used from [TR] Lemma 6.56 on with no defining row | `[repair]` | `Paper/S5_Model/Definitions.lean` | `Fig16.ResU.delDom`, `Fig16.ResU.restrictDom` |
| 5.65 (Definition 6.2) | `ψ ∼ ψ′ ≔ (ψ = mut(α,_,_,P̂) ∧ ψ′ = mut(α,_,_,P̂)) ∨ (ψ = ψ′ = imm(ᾱ,v,ρ))` — [TR] Definition 6.2, not a p. 5 row | `[as printed]` | `Paper/S6_2_NonStandardLemmas/Definitions.lean`, `Paper/S6_2_NonStandardLemmas/Remarks.lean` | `Fig16.CellU.Sim`, `Fig16.CellU.Sim.refl`, `Fig16.CellU.Sim.trans`, `Fig16.ResU.SimForm`, `Fig16.ResU.borrowPart`, `Fig16.ResU.upd_iff_sim` |
| 5.66 (Definition 6.3) | `ρ ⊟ ρ′ ≜ ρ∣own,mut ● ρ″ where …` — [TR] Definition 6.3, not a p. 5 row | `[repair]` | `Paper/S6_2_NonStandardLemmas/Definitions.lean` | `Fig16.ResU.Sub`, `Fig16.ResU.SubClause`, `Fig16.ResU.SubClauseL`, `Fig16.ResU.SubKeep`, `Fig16.ResU.SubL` |
| 5.67 | — [CONF] §4.3's characterisation of `✓`: *"in a valid resource, every pair of aliases map to the same object and each has an immutable ancestor"*, and *"aliasing of exclusive locations … not guarded by immutable cells … violates the mutability-xor-aliasing restriction"* — | `[as printed]` | `Paper/S5_Model/Definitions.lean`, `Paper/S6_1_StandardLemmas/Lemmas.lean`, `Paper/S6_2_NonStandardLemmas/Lemmas.lean` | `Fig16.AgW.nonimm_beneath_imm`, `Fig16.CellU.CompatS.imm_imm`, `Fig16.CellU.compatR_iff`, `Fig16.ExW.immFree`, `Fig16.ResU.CompatS.disjoint_of_immFree`, `Fig16.ResU.flat_eq_ag_at` |

## Repaired definitions

Every definition row tagged `[repair]`, with the printed text it reads differently; the row's comment cites its `docs/adjudications.md` entry.  The headline results are stated at the typed world, the repair of rows 4.4–4.14 and 5.33 (§12.69–§12.72), declared in `Support/TypedWorld/`.

* **1.8** `Val ::= … ∣ Λ.e` — `Paper/S1_Syntax/Definitions.lean`
* **2.10** ⊸E: `Δ; Γ₁ ⊢ e₁ : T₁`, `Δ; Γ₂ ⊢ e₂ : T₁ ⊸ T₂` / `Δ; Γ₁,Γ₂ ⊢ e₁ e₂ : T₂` — `Paper/S2_Statics/Definitions.lean`
* **2.11** ∀I: `Δ, ('a ⊏ @b); Γ ⊢ e : T` / `Δ; Γ ⊢ Λ.e : ∀ 'a ⊏ @b. T` — `Paper/S2_Statics/Definitions.lean`
* **2.12** ∀E: `Δ; Γ ⊢ e : ∀ 'a ⊏ @b. T`, `Δ ⊨ @a ⊏ @b` / `Δ; Γ ⊢ e[] : T[@a/'a]` — `Paper/S2_Statics/Definitions.lean`
* **2.13** [l]I: `Δ; Γ ⊢ e : T`, `Δ ⊨ Γ ⊐ @a` / `Δ; Γ ⊢ □e : [@a] T` — `Paper/S2_Statics/Definitions.lean`
* **2.17** ⊑Imm: `Δ; Γ ⊢ e : Imm @b T`, `Δ ⊨ @a ⊑ @b` / `Δ; Γ ⊢ e : Imm @b T` — `Paper/S2_Statics/Definitions.lean`
* **2.18** ⊑Mut: `Δ; Γ ⊢ e : Mut @b T`, `Δ ⊨ @a ⊑ @b` / `Δ; Γ ⊢ e : Mut @b T` — `Paper/S2_Statics/Definitions.lean`
* **2.39** `Δ ⊢ swap : Ref T₁ ⊸ T₂ ⊸ Ref T₂ ⊗ T₁` — `Paper/S2_Statics/Definitions.lean`
* **2.45** `Δ ⊢ withbor : Ref T₁ ⊸ (∀ 'a ⊏ ⊓Δ. Mut 'a T₁ ⊸ ['a] T₂) ⊸ Ref T₁ ⊗ T₂`, side condition `Δ ⊢ T₁ ⊐ @b` on this line — `Paper/S2_Statics/Definitions.lean`
* **2.46** `Δ ⊢ withbor : Mut @a T₁ ⊸ (∀ 'b ⊏ ⊓Δ. Mut 'b T₁ ⊸ ['b] T₂) ⊸ Mut @a T₁ ⊗ T₂` — `Paper/S2_Statics/Definitions.lean`
* **2.47** `Δ ⊢ withload : Imm @a T₁ ⊸ (∀ 'b ⊏ ⊓Δ. Imm̲ 'b T₁ ⊸ ['b] T₂) ⊸ T₂` (leading `Imm` UNDERLINED) — `Paper/S2_Statics/Definitions.lean`
* **2.50** — no printed clause — — `Paper/S2_Statics/Definitions.lean`
* **2.54** `@aδ ≜ δ('a)`, `⊤`, `@b₁δ ⊓ @b₂δ` at `@a = @b₁ ⊔ @b₂`, `@b₁δ ⊔ @b₂δ` at `@a = @b₁ ⊔ @b₂` — `Paper/S2_Statics/Definitions.lean`
* **2.58** `Δ ⊨ Γ ⊐ @a` — premise of [l]I, NEVER DEFINED — `Paper/S2_Statics/Definitions.lean`
* **3.10** `Mem ∋ µ : Loc ⇀ Val` (the executable counterpart) — `Support/Dynamics/Interpreter.lean`
* **3.24** `swap ≜ λx.λy.let z = load x; store x y; (x, y)` — `Paper/S2_Statics/Definitions.lean`
* **3.27** `withbor ≜ λx.λf.(x, f x)` — `Paper/S2_Statics/Definitions.lean`
* **3.28** `withload ≜ λx.λf.(x, f (load x))` — `Paper/S2_Statics/Definitions.lean`
* **3.30** — no printed counterpart in §3 — — `Paper/S3_Dynamics/Definitions.lean`
* **3.31** — no printed counterpart in §3 — — `Paper/S3_Dynamics/Definitions.lean`
* **3.36** — no printed counterpart; [TR] §1 prints only `let (x,y) = e₁ in e₂` — — `Paper/S3_Dynamics/Definitions.lean`
* **3.37** — no printed counterpart; the print gives a relation — — `Support/Dynamics/Interpreter.lean`
* **4.4** `𝒱⟦T₁ ⊸ T₂⟧δ(v) ≜ ∀v′. 𝒱⟦T₁⟧δ(v′) ─⋆ ℰ⟦T₂⟧δ(v v′)` — `Paper/S4_LogicalRelation/Definitions.lean`, `Support/TypedWorld/Relation.lean`
* **4.5** `𝒱⟦∀ 'a ⊏ @b. T⟧δ(v) ≜ ∀ α ⊏ @bδ. ℰ⟦T⟧δ(v ())` — `Paper/S4_LogicalRelation/Definitions.lean`, `Support/TypedWorld/Relation.lean`
* **4.8** `𝒱⟦Imm @a T⟧δ(v) ≜ ∃ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦ Imm @aδ 𝒱⟦T⟧δ` — `Paper/S4_LogicalRelation/Definitions.lean`, `Support/TypedWorld/Relation.lean`
* **4.9** `𝒱⟦Mut @a T⟧δ(v) ≜ ∃ℓ. ⌜v = ℓ⌝ ⋆ ℓ ↦ Mut @aδ 𝒱⟦T⟧δ` — `Paper/S4_LogicalRelation/Definitions.lean`, `Support/TypedWorld/Relation.lean`
* **4.11** `ℰ⟦T⟧δ(v) ≜ wp (e) {𝒱⟦T⟧δ}` — `Paper/S4_LogicalRelation/Definitions.lean`, `Support/TypedWorld/World.lean`
* **4.13** `𝒢⟦Γ⟧(γ) ≜ ⌜dom(Γ) ⊆ dom(δ)⌝ ⋆ ⊛_{x∈dom(Γ)} 𝒱⟦Γ(x)⟧δ(γ(x))` — `Paper/S4_LogicalRelation/Definitions.lean`, `Support/TypedWorld/Relation.lean`
* **4.14** `Δ; Γ ⊨ e : T ≜ !∀ δ,γ. 𝒟⟦Δ⟧(δ) ─⋆ 𝒢⟦Γ⟧δ(γ) ─⋆ ℰ⟦T⟧δ(γ(e))` — `Paper/S4_LogicalRelation/Definitions.lean`, `Support/TypedWorld/Relation.lean`
* **4.15** — no printed counterpart — — `Paper/S4_LogicalRelation/Definitions.lean`
* **4.16** — no printed counterpart — — `Paper/S4_LogicalRelation/Definitions.lean`, `Paper/S4_LogicalRelation/Remarks.lean`
* **4.17** — no printed counterpart — — `Paper/LiteralReadings/S4_LogicalRelation.lean`
* **5.2** `Res_α ≜ Loc ⇀ Cell_α` — `Paper/S5_Model/Definitions.lean`
* **5.9** `α, β ∈ Life ≜ (ℕ, ⊑ ≜ >, ⊔ ≜ min, ⊓ ≜ max, ⊤ ≜ 0)` — `Paper/S5_Model/Definitions.lean`
* **5.14** `ψ₁ ▷◁ ψ₂ ≜ ψ₁ ▸◂ ψ₂ ∨ ∃i,ᾱ,β,v,ρ,P̂. {ψ₁,ψ₂} ∈ {imm(ᾱ,v,ρ), own(v), mut(β,v,ρ,P̂)}` — `Paper/S5_Model/Definitions.lean`
* **5.20** `ex(ρ)_◖ ≜ ρ∣own ◖ ρ∣mut ◖ ⨀{ex(ρ′)_◖ ∣ ∃ℓ. ρ(ℓ) = mut(_,_,ρ′,_)}` — `Paper/S5_Model/Definitions.lean`
* **5.21** `ag(ρ)_◖ ≜ ρ∣imm ○ ◯{ag(ρ′) ∣ …mut…} ○ ◯{ex(ρ′)_○ ○ ag(ρ′) ∣ …imm…}` — `Paper/S5_Model/Definitions.lean`
* **5.27** `ρ₁ ↭ ρ₂ ≜ {∀ℓ,… (⦇ρ₁⦈(ℓ)=mut(α,_,_,P̂) ⇔ ⦇ρ₂⦈(ℓ)=mut(α,_,_,P̂)) ∧ (⦇ρ₁⦈(ℓ)=imm(β̄,v,ρ) ⇔ ⦇ρ₂⦈(ℓ)=mut(β̄,v,ρ))}`, `✓ρ₁ ∧ ✓ρ₂` — `Paper/S5_Model/Definitions.lean`
* **5.28** `reb_α(ρ) ≜ {ρ′ ∣ @ρ ⊐ α ∧ ∃π : dom(ρ′) → Res. ρ ≥ ⨀_● π(ℓ) ∧ …}` — `Paper/S5_Model/Definitions.lean`
* **5.30** `ℓ ↦ Imm α P̂  (ρ) ≜ ∃β̄,v,ρ′. ρ = ℓ ↦ imm(β̄,v,ρ′) ∧ P̂(v)(ρ′) ∧ α ⊑ ⊔β̄` — `Paper/S5_Model/Definitions.lean`
* **5.31** `ℓ ↦ Mut α P̂  (ρ) ≜ ∃β ⊒ α, v, ρ′. ρ = ℓ ↦ mut(β,v,ρ′,P̂)` — `Paper/S5_Model/Definitions.lean`
* **5.32** `[α] P  (ρ) ≜ P(ρ) ∧ @ρ ⊐ α` — `Paper/S5_Model/Definitions.lean`
* **5.33** `wp (e) {Q̂} (ρ) ≜ ∀ρ_f # ρ. ∃ρ′ # ρ_f, ρ⁺ # (ρ_f ● ρ′), v. (⟦ρ_f ● ρ⟧,e) →* (⟦ρ_f ● ρ′ ● ρ⁺⟧,v) ∧ ρ ↭ ρ′ ● ρ⁺ ∧ ρ⁺∣own = ∅ ∧ Q̂(v)(ρ′)` — `Paper/S5_Model/Definitions.lean`, `Support/TypedWorld/World.lean`
* **5.48** — presupposed, never written — — `Paper/S5_Model/Definitions.lean`
* **5.51** — `ρ∣own,mut` is used from [TR] Def. 6.3 on with no defining row — — `Paper/S5_Model/Definitions.lean`
* **5.52** `ℓ ↦ ψ` — used from [TR] Lemma 6.17 on, defined nowhere — `Paper/S5_Model/Definitions.lean`
* **5.53** `ρ/ℓ` — the `/` of `ρ₁/dom(ρ₂)` and of `π(ℓ)/ℓ` — `Paper/S5_Model/Definitions.lean`
* **5.55** — the index set of the `ex`/`ag` comprehensions and of `dom(ρ′)` — — `Paper/S5_Model/Definitions.lean`
* **5.56** `⨀` — the iterated composition, with no printed empty case — `Paper/S5_Model/Definitions.lean`, `Paper/S6_1_StandardLemmas/Lemmas.lean`
* **5.57** — the paper's `SProp_α ⊆ SProp_{α′} ⊆ SProp` is a set inclusion — — `Paper/S5_Model/Definitions.lean`
* **5.58** — neither document prints the recursion, only the measure — — `Paper/S5_Model/Definitions.lean`
* **5.59** — ⊑ appears in [TR] p. 4 row 9 as the STRICT `>` — — `Paper/S5_Model/Definitions.lean`
* **5.60** `⦇ρ⦈(ℓ)` — an application of a partial term — `Paper/S5_Model/Definitions.lean`
* **5.62** — [CONF] Fig. 18b's unguarded ↭, and the `wp` row read at it — — `Paper/S5_Model/Definitions.lean`, `Paper/S5_Model/Remarks.lean`
* **5.63** `ρ⁺∣own = ∅` is named; `ℓ ↦ _` has no printed counterpart — `Paper/S5_Model/Definitions.lean`
* **5.64** `ρ∣dom(ρ′)` — a domain restriction, used from [TR] Lemma 6.56 on with no defining row — `Paper/S5_Model/Definitions.lean`
* **5.66** `ρ ⊟ ρ′ ≜ ρ∣own,mut ● ρ″ where …` — [TR] Definition 6.3, not a p. 5 row — `Paper/S6_2_NonStandardLemmas/Definitions.lean`

## Examples

Not rows of the paper: derivations and runs that show the hypotheses of the
headline results are inhabited.

* `Paper/Examples/Derivations.lean` — `[TR]` p. 2's rules and p. 3's axiom table at
  concrete instances in `DerivesWf` (`Programs.d_*`).
* `Paper/Examples/Programs.lean` — closed programs typed at `DerivesWf ∅ [] e 1`,
  with `Fig16.LogRel.Typed.adequacy` applied (`Programs.allocFree_runs`,
  `Programs.fig2c_runs`, `Programs.immBorrow_runs`, `Programs.mutBorrow_runs`,
  `Programs.loadClosure_runs`, `Programs.aliasLoad_runs`, `Programs.swapTwo_runs`,
  `Programs.greetProg_runs`) and interpreter runs (`Programs.*_eval`).
* `Paper/Examples/Model.lean` — Lemmas 6.7 and 6.20 at a shared `imm` location
  (`Fig16.LowerExample.split_overlap`, `Fig16.SplitExample.overlap`) and
  inhabitants of §6.2 hypotheses (`Fig16.ResU.flatR_single_own`,
  `Fig16.ResU.hash_empty_single_mut`, `Fig16.escrowAgree_self`).

## Rows with no declaration

* Lemma 6.40 — none on the printed carrier: untranscribed (see its record in `Paper/S6_2_NonStandardLemmas/Lemmas.lean`).

## Spec additions

Declarations `SPEC.md` adds to the baseline, tagged `[spec §N]` in the source.

* **§2, closed code** — `Ty.fn` (`Paper/S1_Syntax/Definitions.lean`); `Ty.immReborrow`'s `fn`
  clause (`Paper/S2_Statics/Definitions.lean`); `vDen_fn` (`Paper/S4_LogicalRelation/Definitions.lean`);
  `vDen_immReborrow_fn` (`Support/LogicalRelation/Facts.lean`); `reborrow_vDen`'s `fn` case
  (`Paper/S6_6_ReborrowingEntailments/Lemmas.lean`); `Support/Model/Unr.lean`; `Typed.vX`'s
  `fn` clause (`Support/TypedWorld/Relation.lean`); `DerivesWf.fnI`, `fnE`, `copyFnAx`,
  `forgetFnAx` (`Support/Statics/Presupposed.lean`); `Typed.fnI_compatX`, `fnE_compatX`,
  `copyFn_compatX`, `forgetFn_compatX` (`Support/TypedWorld/Compatibility.lean`);
  `Programs.callBorrowed` (`Examples/CallBorrowed.lean`); `Programs.captures`
  (`Examples/Captures.lean`); `Programs.fnMut` (`Examples/FnMut.lean`).
