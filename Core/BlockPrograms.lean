import Core.BlockTrack
import Core.FamilyPrograms

/-!
# Core — programs over blocks  `[spec §5]`

Each program is closed and typed at `1`: a `CDerives` derivation run by `adequacyC` (no leak),
a kernel-checked interpreter run (`…_eval`) and an observation of the struct's contents
(`…Obs_eval`).  The interpreter allocates by bumping a counter, so its `allocS` lays the leaves
out at consecutive addresses.  `…_block` is the typed-world statement of the program's first
half: allocated as one block and borrowed through the family, the struct comes back as the
block's own handle, packed (`wpTS_allocBorrow`).

| program | struct | shows |
|---|---|---|
| `blockSwap` | `{a : B, b : B}` | `Mut 'c` at `s.a` and `s.b` together, both updated (`mem::swap`), the block freed whole |
| `nestSwap` | `{a : {x : B, y : B}, b : B}` | `s.a.x` borrowed alone at the lifetime of `s.b`; `s.a.y` dropped |
| `blockRead` | `{a : B, b : B}` | `Imm` of the whole struct at `'c`; `s.a` alone and the whole struct read at `'c` |
| `nestRead` | `{a : {x : B, y : B}, b : B}` | `Imm`: the sub-struct `s.a` and the leaf `s.b` each read at `'c` |
| `bagBlock` | `{n : N, items : L}` | a block with a list leaf: `Mut 'c` at `s.items`, a node pushed through it |
| `crossPack` | `{a : B, b : B}` | a handle joining leaves of two blocks: typed and run, but no block's handle |

`B = 1 ⊕ 1`, `L` the common list.  The callbacks are `FamilyPrograms.lean`'s: the family type of
`{a : B, b : B}` is `famTy2`.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Fig16.BoLo
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Programs (lam app2 alloc' free' unitNoLeak entailsLt_top)

/-! ### Structs -/

/-- `{a : B, b : B}`. -/
abbrev σ2 : Shape := .node (.leaf BB) (.leaf BB)

/-- `{a : {x : B, y : B}, b : B}`. -/
abbrev σ3 : Shape := .node (.node (.leaf BB) (.leaf BB)) (.leaf BB)

/-- `inj₁ ()` or `inj₂ ()`, as a value. -/
def bval : Bool → Val
  | false => .inj₁ .unit
  | true => .inj₂ .unit

theorem d_bval {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    ∀ b, CDerives Δ Γ (bval b).1 (.val BB)
  | false => .sumI₁ (.unitI hΓ)
  | true => .sumI₂ (.unitI hΓ)

theorem vP_bval {ls : List SRec} {δ : LSub} : ∀ b, vP BB ls δ (bval b) PMap.empty
  | false => Or.inl ⟨Val.unit, pure_sep_mk rfl ⟨rfl, rfl⟩⟩
  | true => Or.inr ⟨Val.unit, pure_sep_mk rfl ⟨rfl, rfl⟩⟩

theorem vP_pair {A B : VTy} {ls : List SRec} {δ : LSub} {v₁ v₂ : Val}
    (h₁ : vP A ls δ v₁ PMap.empty) (h₂ : vP B ls δ v₂ PMap.empty) :
    vP (.tensor A B) ls δ (.pair v₁ v₂) PMap.empty :=
  ⟨v₁, v₂, pure_sep_mk rfl ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, h₁, h₂⟩⟩

/-- The contents of a two-leaf struct. -/
def vals2 (a b : Bool) : Val := .pair (bval a) (bval b)

/-- The contents of `{a : {x, y}, b}`. -/
def vals3 (x y b : Bool) : Val := .pair (.pair (bval x) (bval y)) (bval b)

theorem d_vals2 {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (a b : Bool) :
    CDerives Δ Γ (vals2 a b).1 (.val σ2.valTy) :=
  .tensorI (deadSplit hΓ) (d_bval hΓ a) (d_bval hΓ b)

theorem d_vals3 {Δ : LifeCtx} {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) (x y b : Bool) :
    CDerives Δ Γ (vals3 x y b).1 (.val σ3.valTy) :=
  .tensorI (deadSplit hΓ) (.tensorI (deadSplit hΓ) (d_bval hΓ x) (d_bval hΓ y)) (d_bval hΓ b)

/-- `let (a, b) = freeS σ2 r; drop a; drop b`, with `r` at index `i`: the block freed whole. -/
def freeB2 (i : Nat) : Expr :=
  .letpair (.app (freeS σ2) (.var i)) (.seq (dropB (.var 1)) (dropB (.var 0)))

/-- `let (ab, c) = freeS σ3 r; let (a, b) = ab; drop a; drop b; drop c`. -/
def freeB3 (i : Nat) : Expr :=
  .letpair (.app (freeS σ3) (.var i))
    (.letpair (.var 1) (.seq (dropB (.var 1)) (.seq (dropB (.var 0)) (dropB (.var 2)))))

theorem d_withborS2 {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {T : VTy} (hT : plainV T = true) :
    CDerives LifeCtx.empty Γ (withborS σ2) (.val (wTy mutM 0 LifeCtx.empty.meetOfDom σ2 T)) :=
  withborSM_wf rfl 0 hT ok_empty rfl hΓ

theorem d_withborS3 {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {T : VTy} (hT : plainV T = true) :
    CDerives LifeCtx.empty Γ (withborS σ3) (.val (wTy mutM 0 LifeCtx.empty.meetOfDom σ3 T)) :=
  withborSM_wf rfl 0 hT ok_empty rfl hΓ

theorem d_withborSI2 {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {T : VTy} (hT : plainV T = true) :
    CDerives LifeCtx.empty Γ (withborS σ2) (.val (wTy immM 0 LifeCtx.empty.meetOfDom σ2 T)) :=
  withborSI_wf rfl 0 hT ok_empty rfl hΓ

theorem d_withborSI3 {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) {T : VTy} (hT : plainV T = true) :
    CDerives LifeCtx.empty Γ (withborS σ3) (.val (wTy immM 0 LifeCtx.empty.meetOfDom σ3 T)) :=
  withborSI_wf rfl 0 hT ok_empty rfl hΓ

theorem d_swapCbB : CDerives LifeCtx.empty [] swapCb
    (.val (cbT mutM 0 LifeCtx.empty.meetOfDom σ2 .unit)) :=
  d_swapCb (A := BB) (fun _ h => by simp [VFree] at h)

/-! ### Two mutable leaf borrows of one block, used together

    let (s, u) = withborS σ2 (allocS σ2 (inj₁ (), inj₂ ())) swapCb;
    u; let (a, b) = freeS σ2 s; drop a; drop b -/

def blockSwap : Expr :=
  .letpair (app2 (withborS σ2) (.app (allocS σ2) (vals2 false true).1) swapCb)
    (.seq (.var 0) (freeB2 1))

def blockSwapObs : Expr :=
  .letpair (app2 (withborS σ2) (.app (allocS σ2) (vals2 false true).1) swapCb)
    (.seq (.var 0) (.app (freeS σ2) (.var 1)))

theorem d_blockSwap : CDerives LifeCtx.empty [] blockSwap (.val .unit) :=
  letW (A := σ2.refTy) (B := .unit)
    (appW d_swapCbB (appW (appW (d_vals2 (by cdead) false true) (d_allocS σ2 (by cdead)))
      (d_withborS2 (by cdead) rfl))) <|
  seqW (.var (by csolo)) <|
  letW (A := BB) (B := BB) (appW (.var (by csolo)) (d_freeS σ2 (by cdead))) <|
  seqW (d_dropB (.var (by csolo)) (by cdead)) (d_dropB (.var (by csolo)) (by cdead))

theorem blockSwap_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem blockSwap Adequacy.emptyMem (.val .unit) :=
  adequacyC (.ret d_blockSwap)

theorem blockSwap_eval : unitNoLeak (eval blockSwap) = true := by decide

/-- `s.a` and `s.b` swapped: `(inj₂ (), inj₁ ())` from `(inj₁ (), inj₂ ())`. -/
theorem blockSwapObs_eval :
    (match eval blockSwapObs with
      | .value ⟨.pair (.inj₂ .unit) (.inj₁ .unit), _⟩ false => true
      | _ => false) = true := by decide

/-- The first half of `blockSwap` at the typed world: one block, and the handle the borrow
returns is that block's, packed. -/
theorem blockSwap_block :
    wpTS [] (app2 (withborS σ2) (.app (allocS σ2) (vals2 false true).1) swapCb)
      (fun ls w => fun ρ => ∃ b t, w = .pair (σ2.addr b) t ∧
        (Packed σ2 b ls LSub.empty (σ2.addr b) ⋆ vP .unit ls LSub.empty t) ρ) PMap.empty :=
  wpTS_allocBorrow (cb := ⟨swapCb, .lam⟩) (by decide)
    (d_call (d_withborS2 (by cdead) rfl) d_swapCbB) Adequacy.models_empty
    (vP_pair (vP_bval false) (vP_bval true))

/-! ### A nested struct: `s.a.x` alone at the lifetime of `s.b`

    nestCb ≜ Λ. λf. let (sa, mb) = f; let (mx, my) = sa; forget my;
                    let (mx′, mb′) = swapFn () (mx, mb); forget mx′; forget mb′; () -/

def nestCb : Expr :=
  lam2 (.letpair (.var 0) (.letpair (.var 1)
    (.seq (.app forget (.var 0))
      (.letpair (.app (.app swapFn unit') (.pair (.var 1) (.var 2)))
        (.seq (.app forget (.var 0)) (.seq (.app forget (.var 1)) unit'))))))

theorem d_nestCb :
    CDerives LifeCtx.empty [] nestCb (.val (cbT mutM 0 LifeCtx.empty.meetOfDom σ3 .unit)) :=
  callbackW ok_empty rfl .nil <|
    letW (A := .tensor (.mut (.var 0) BB) (.mut (.var 0) BB)) (B := .mut (.var 0) BB)
      (.var (by csolo)) <|
    letW (A := .mut (.var 0) BB) (B := .mut (.var 0) BB) (.var (by csolo)) <|
    seqW (appW (.var (by csolo)) (.forgetMut (by cdead))) <|
    letW (A := .mut (.var 0) BB) (B := .mut (.var 0) BB)
      (appW (pairW (.var (by csolo)) (.var (by csolo)))
        (d_swapFnAtVar d1_ok (by cdead) 0 5 (u := LifeCtx.empty.meetOfDom) rfl rfl rfl)) <|
    seqW (appW (.var (by csolo)) (.forgetMut (by cdead))) <|
    seqW (appW (.var (by csolo)) (.forgetMut (by cdead)))
      (.boxI (.unitI (by cdead)) ⟨LifeCtx.defines_of_wf rfl, dead_noLive (by cdead)⟩)

def nestSwap : Expr :=
  .letpair (app2 (withborS σ3) (.app (allocS σ3) (vals3 false false true).1) nestCb)
    (.seq (.var 0) (freeB3 1))

def nestSwapObs : Expr :=
  .letpair (app2 (withborS σ3) (.app (allocS σ3) (vals3 false false true).1) nestCb)
    (.seq (.var 0) (.app (freeS σ3) (.var 1)))

theorem d_nestSwap : CDerives LifeCtx.empty [] nestSwap (.val .unit) :=
  letW (A := σ3.refTy) (B := .unit)
    (appW d_nestCb (appW (appW (d_vals3 (by cdead) false false true) (d_allocS σ3 (by cdead)))
      (d_withborS3 (by cdead) rfl))) <|
  seqW (.var (by csolo)) <|
  letW (A := .tensor BB BB) (B := BB) (appW (.var (by csolo)) (d_freeS σ3 (by cdead))) <|
  letW (A := BB) (B := BB) (.var (by csolo)) <|
  seqW (d_dropB (.var (by csolo)) (by cdead)) <|
  seqW (d_dropB (.var (by csolo)) (by cdead)) (d_dropB (.var (by csolo)) (by cdead))

theorem nestSwap_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem nestSwap Adequacy.emptyMem (.val .unit) :=
  adequacyC (.ret d_nestSwap)

theorem nestSwap_eval : unitNoLeak (eval nestSwap) = true := by decide

/-- `s.a.x` and `s.b` swapped, `s.a.y` untouched: `((inj₂, inj₁), inj₁)` from
`((inj₁, inj₁), inj₂)`. -/
theorem nestSwapObs_eval :
    (match eval nestSwapObs with
      | .value ⟨.pair (.pair (.inj₂ .unit) (.inj₁ .unit)) (.inj₁ .unit), _⟩ false => true
      | _ => false) = true := by decide

theorem nestSwap_block :
    wpTS [] (app2 (withborS σ3) (.app (allocS σ3) (vals3 false false true).1) nestCb)
      (fun ls w => fun ρ => ∃ b t, w = .pair (σ3.addr b) t ∧
        (Packed σ3 b ls LSub.empty (σ3.addr b) ⋆ vP .unit ls LSub.empty t) ρ) PMap.empty :=
  wpTS_allocBorrow (cb := ⟨nestCb, .lam⟩) (by decide)
    (d_call (d_withborS3 (by cdead) rfl) d_nestCb) Adequacy.models_empty
    (vP_pair (vP_pair (vP_bval false) (vP_bval false)) (vP_bval true))

/-! ### Immutable: the whole struct at `'c`, and a leaf alone at `'c` -/

def blockRead : Expr :=
  .letpair (app2 (withborS σ2) (.app (allocS σ2) (vals2 false true).1) readCb)
    (.seq (dropB3 0) (freeB2 1))

def blockReadObs : Expr :=
  .letpair (app2 (withborS σ2) (.app (allocS σ2) (vals2 false true).1) readCb)
    (.seq (freeB2 1) (.var 0))

theorem d_blockRead : CDerives LifeCtx.empty [] blockRead (.val .unit) :=
  letW (A := σ2.refTy) (B := B3)
    (appW d_readCb (appW (appW (d_vals2 (by cdead) false true) (d_allocS σ2 (by cdead)))
      (d_withborSI2 (by cdead) rfl))) <|
  seqW (d_dropB3 (by cdead)) <|
  letW (A := BB) (B := BB) (appW (.var (by csolo)) (d_freeS σ2 (by cdead))) <|
  seqW (d_dropB (.var (by csolo)) (by cdead)) (d_dropB (.var (by csolo)) (by cdead))

theorem blockRead_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem blockRead Adequacy.emptyMem (.val .unit) :=
  adequacyC (.ret d_blockRead)

theorem blockRead_eval : unitNoLeak (eval blockRead) = true := by decide

/-- `s.a` read alone, then the whole struct: `(inj₁ (), (inj₁ (), inj₂ ()))`. -/
theorem blockReadObs_eval :
    (match eval blockReadObs with
      | .value ⟨.pair (.inj₁ .unit) (.pair (.inj₁ .unit) (.inj₂ .unit)), _⟩ false => true
      | _ => false) = true := by decide

theorem blockRead_block :
    wpTS [] (app2 (withborS σ2) (.app (allocS σ2) (vals2 false true).1) readCb)
      (fun ls w => fun ρ => ∃ b t, w = .pair (σ2.addr b) t ∧
        (Packed σ2 b ls LSub.empty (σ2.addr b) ⋆ vP B3 ls LSub.empty t) ρ) PMap.empty :=
  wpTS_allocBorrow (cb := ⟨readCb, .lam⟩) (by decide)
    (d_call (d_withborSI2 (by cdead) rfl) d_readCb) Adequacy.models_empty
    (vP_pair (vP_bval false) (vP_bval true))

/-! ### Immutable, nested: the sub-struct `s.a` and the leaf `s.b`, each at `'c`

    nestReadCb ≜ Λ. λf. let (sa, ib) = f;
                        let (u, w) = (readBoth () sa, readOne () ib); (u, w) -/

def nestReadCb : Expr :=
  lam2 (.letpair (.var 0)
    (.letpair (.pair (.app (.app readBoth unit') (.var 1)) (.app (.app readOne unit') (.var 0)))
      (.pair (.var 1) (.var 0))))

/-- `(B ⊗ B) ⊗ B`. -/
abbrev B21 : VTy := .tensor (.tensor BB BB) BB

theorem d_nestReadCb :
    CDerives LifeCtx.empty [] nestReadCb (.val (cbT immM 0 LifeCtx.empty.meetOfDom σ3 B21)) :=
  callbackW ok_empty rfl .nil <|
    letW (A := famTy2 immM (.var 0) BB BB) (B := .imm (.var 0) BB) (.var (by csolo)) <|
    letW (A := .tensor BB BB) (B := BB)
      (pairW
        (appW (.var (by csolo))
          (.allEV (x := 5) (b := .top) (A := .lolli (famTy2 immM (.var 5) BB BB) (.tensor BB BB))
            (a := .var 0) (d_readBoth d1_ok (by cdead) 5 6 7 rfl rfl rfl rfl) (entailsLt_top rfl)))
        (appW (.var (by csolo)) (d_readOneAt d1_ok (by cdead) 0 5 6 rfl rfl rfl rfl))) <|
    .boxI (pairW (.var (by csolo)) (.var (by csolo)))
      (outlives_two (LifeCtx.defines_of_wf rfl) (outlives_of_dataB rfl) (outlives_of_dataB rfl)
        (by cdead))

def dropB21 (i : Nat) : Expr :=
  .letpair (.var i) (.seq (dropB (.var 0)) (.letpair (.var 1) (.seq (dropB (.var 1)) (dropB (.var 0)))))

def nestRead : Expr :=
  .letpair (app2 (withborS σ3) (.app (allocS σ3) (vals3 false true true).1) nestReadCb)
    (.seq (dropB21 0) (freeB3 1))

def nestReadObs : Expr :=
  .letpair (app2 (withborS σ3) (.app (allocS σ3) (vals3 false true true).1) nestReadCb)
    (.seq (freeB3 1) (.var 0))

theorem d_nestRead : CDerives LifeCtx.empty [] nestRead (.val .unit) :=
  letW (A := σ3.refTy) (B := B21)
    (appW d_nestReadCb (appW (appW (d_vals3 (by cdead) false true true) (d_allocS σ3 (by cdead)))
      (d_withborSI3 (by cdead) rfl))) <|
  seqW
    (letW (A := .tensor BB BB) (B := BB) (.var (by csolo)) <|
      seqW (d_dropB (.var (by csolo)) (by cdead)) <|
      letW (A := BB) (B := BB) (.var (by csolo)) <|
      seqW (d_dropB (.var (by csolo)) (by cdead)) (d_dropB (.var (by csolo)) (by cdead))) <|
  letW (A := .tensor BB BB) (B := BB) (appW (.var (by csolo)) (d_freeS σ3 (by cdead))) <|
  letW (A := BB) (B := BB) (.var (by csolo)) <|
  seqW (d_dropB (.var (by csolo)) (by cdead)) <|
  seqW (d_dropB (.var (by csolo)) (by cdead)) (d_dropB (.var (by csolo)) (by cdead))

theorem nestRead_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem nestRead Adequacy.emptyMem (.val .unit) :=
  adequacyC (.ret d_nestRead)

theorem nestRead_eval : unitNoLeak (eval nestRead) = true := by decide

/-- `s.a` read through its sub-family, `s.b` through its leaf: `((inj₁, inj₂), inj₂)`. -/
theorem nestReadObs_eval :
    (match eval nestReadObs with
      | .value ⟨.pair (.pair (.inj₁ .unit) (.inj₂ .unit)) (.inj₂ .unit), _⟩ false => true
      | _ => false) = true := by decide

theorem nestRead_block :
    wpTS [] (app2 (withborS σ3) (.app (allocS σ3) (vals3 false true true).1) nestReadCb)
      (fun ls w => fun ρ => ∃ b t, w = .pair (σ3.addr b) t ∧
        (Packed σ3 b ls LSub.empty (σ3.addr b) ⋆ vP B21 ls LSub.empty t) ρ) PMap.empty :=
  wpTS_allocBorrow (cb := ⟨nestReadCb, .lam⟩) (by decide)
    (d_call (d_withborSI3 (by cdead) rfl) d_nestReadCb) Adequacy.models_empty
    (vP_pair (vP_pair (vP_bval false) (vP_bval true)) (vP_bval true))

/-! ### A block with a list leaf

    let (s, u) = withborS bagS (allocS bagS (0, [])) (Λ. λf. let (mn, ml) = f; forget mn;
                   let (ml′, t) = withswap ml (λl. (7 :: l, ())); t; forget ml′; ());
    u; let (n, l) = freeS bagS s; freeNat n; freeList l -/

/-- `{n : N, items : L}` as a block. -/
abbrev bagS : Shape := .node (.leaf natN) (.leaf clistL)

def bagCb : Expr :=
  lam2 (.letpair (.var 0) (.seq (.app forget (.var 1))
    (.letpair (app2 withswap (.var 0) pushG)
      (.seq (.var 0) (.seq (.app forget (.var 1)) unit')))))

theorem d_bagCb :
    CDerives LifeCtx.empty [] bagCb (.val (cbT mutM 0 LifeCtx.empty.meetOfDom bagS .unit)) :=
  callbackW ok_empty rfl .nil <|
    letW (A := .mut (.var 0) natN) (B := .mut (.var 0) clistL) (.var (by csolo)) <|
    seqW (appW (.var (by csolo)) (.forgetMut (by cdead))) <|
    letW (A := .mut (.var 0) clistL) (B := .unit)
      (appW (d_pushG (by cdead)) (appW (.var (by csolo)) (.withswap (by cdead)))) <|
    seqW (.var (by csolo)) <|
    seqW (appW (.var (by csolo)) (.forgetMut (by cdead)))
      (.boxI (.unitI (by cdead)) ⟨LifeCtx.defines_of_wf rfl, dead_noLive (by cdead)⟩)

def bagBlock : Expr :=
  .letpair (app2 (withborS bagS) (.app (allocS bagS) mkBag) bagCb)
    (.seq (.var 0) (.letpair (.app (freeS bagS) (.var 1))
      (.seq (.app freeNatE (.var 1)) (.app freeCE (.var 0)))))

def bagBlockObs : Expr :=
  .letpair (app2 (withborS bagS) (.app (allocS bagS) mkBag) bagCb)
    (.seq (.var 0) (.letpair (.app (freeS bagS) (.var 1))
      (.seq (.app freeNatE (.var 1)) (.app toPureCE (.var 0)))))

theorem d_bagBlock : CDerives LifeCtx.empty [] bagBlock (.val .unit) :=
  letW (A := bagS.refTy) (B := .unit)
    (appW d_bagCb (appW (appW (pairW (d_num (by cdead) 0) (d_nilC (by cdead)))
        (d_allocS bagS (by cdead)))
      (withborSM_wf rfl 0 rfl ok_empty rfl (by cdead)))) <|
  seqW (.var (by csolo)) <|
  letW (A := natN) (B := clistL) (appW (.var (by csolo)) (d_freeS bagS (by cdead))) <|
  seqW (appW (.var (by csolo)) (d_freeNat (by cdead))) (appW (.var (by csolo)) (d_freeC (by cdead)))

theorem bagBlock_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem bagBlock Adequacy.emptyMem (.val .unit) :=
  adequacyC (.ret d_bagBlock)

set_option maxRecDepth 100000 in
theorem bagBlock_eval : unitNoLeak (eval bagBlock) = true := by decide

set_option maxRecDepth 100000 in
/-- After the push through the leaf borrow the list is `[7]`, and no cell is left. -/
theorem bagBlockObs_eval : pureNoLeak (eval bagBlockObs) = some [7] := by decide

/-! ### A handle joining leaves of two blocks

    let s₁ = allocS σ2 (inj₁ (), inj₁ ()); let s₂ = allocS σ2 (inj₂ (), inj₂ ());
    let (a₁, b₁) = s₁; let (a₂, b₂) = s₂;
    withborS σ2 (a₁, b₂) swapCb; …; free both

`refTy σ2 = Ref B ⊗ Ref B` is the family's type, so `(a₁, b₂)`, one leaf of each block, is a
well-typed struct handle: the program is derivable, runs, and leaks nothing, but the handle is
no block's (`crossPack_not_packed`).  The model accepts it; a one-word lowering of the handle
does not.  Keeping leaves of different blocks from being joined is block provenance, an open
item of `SPEC.md` §5. -/

/-- `(allocS σ2 (inj₁, inj₁), allocS σ2 (inj₂, inj₂))`, cross-paired and borrowed. -/
def crossPrefix (k : Expr) : Expr :=
  .letpair (.pair (.app (allocS σ2) (vals2 false false).1) (.app (allocS σ2) (vals2 true true).1))
    (.letpair (.var 1) (.letpair (.var 2) k))

/-- The body: `a₁` at 3, `b₁` at 2, `a₂` at 1, `b₂` at 0. -/
def crossPack : Expr :=
  crossPrefix
    (.letpair (app2 (withborS σ2) (.pair (.var 3) (.var 0)) swapCb)
      (.seq (.var 0) (.seq (freeB2 1) (.letpair (.app (freeS σ2) (.pair (.var 3) (.var 4)))
        (.seq (dropB (.var 1)) (dropB (.var 0)))))))

/-- The cross-paired handle itself, returned (and so leaked). -/
def crossPackObs : Expr := crossPrefix (.pair (.var 3) (.var 0))

theorem d_crossPack : CDerives LifeCtx.empty [] crossPack (.val .unit) :=
  letW (A := σ2.refTy) (B := σ2.refTy)
    (pairW (appW (d_vals2 (by cdead) false false) (d_allocS σ2 (by cdead)))
      (appW (d_vals2 (by cdead) true true) (d_allocS σ2 (by cdead)))) <|
  letW (A := .ref BB) (B := .ref BB) (.var (by csolo)) <|
  letW (A := .ref BB) (B := .ref BB) (.var (by csolo)) <|
  letW (A := σ2.refTy) (B := .unit)
    (appW (CDerives.append_dead (by cdead) d_swapCbB)
      (appW (pairW (.var (by csolo)) (.var (by csolo))) (d_withborS2 (by cdead) rfl))) <|
  seqW (.var (by csolo)) <|
  seqW
    (letW (A := BB) (B := BB) (appW (.var (by csolo)) (d_freeS σ2 (by cdead))) <|
      seqW (d_dropB (.var (by csolo)) (by cdead)) (d_dropB (.var (by csolo)) (by cdead))) <|
  letW (A := BB) (B := BB)
    (appW (pairW (.var (by csolo)) (.var (by csolo))) (d_freeS σ2 (by cdead))) <|
  seqW (d_dropB (.var (by csolo)) (by cdead)) (d_dropB (.var (by csolo)) (by cdead))

theorem crossPack_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem crossPack Adequacy.emptyMem (.val .unit) :=
  adequacyC (.ret d_crossPack)

theorem crossPack_eval : unitNoLeak (eval crossPack) = true := by decide

/-- The interpreter's blocks are `{0, 1}` and `{2, 3}`; the cross-paired handle is `(0, 3)`. -/
theorem crossPackObs_eval :
    (match eval crossPackObs with
      | .value ⟨.pair (.loc 0) (.loc 3), _⟩ true => true
      | _ => false) = true := by decide

/-- `(0, 3)` is no block's handle. -/
theorem crossPack_not_packed : ∀ b : Loc, Val.pair (.loc 0) (.loc 3) ≠ σ2.addr b := by
  intro b h
  simp only [Shape.addr, Val.pair, Val.loc, Subtype.mk.injEq, Expr.pair.injEq,
    Expr.loc.injEq, Shape.size] at h
  obtain ⟨rfl, h⟩ := h
  exact absurd h (by decide)

end BoCa.Fig16.LogRel.Core

end
