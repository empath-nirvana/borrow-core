import LeafPlaces.Packed

/-!
# Programs over unboxed structs

Each program is closed and typed at `1`.  It has

* a derivation (`d_…`), so `Fig16.LogRel.Typed.adequacy` gives a run from the empty memory to
  `()` and the empty memory (`…_runs`): no leak;
* a kernel-checked interpreter run (`…_eval`) and an observation of the struct's contents
  (`…Obs_eval`).  The interpreter allocates by bumping a counter, so its `allocS` lays the
  leaves out at consecutive addresses: it is a block allocator;
* the typed-world statement of its first half (`…_block`): allocated as one block and borrowed
  through the family, the struct comes back as the block's own handle, packed
  (`wpTS_allocBorrow`).

| program | struct | shows |
|---|---|---|
| `blockSwap` | `{a : B, b : B}` | (b) `Mut 'c` at `s.a` and `s.b` together, both updated (`mem::swap`), the block freed whole |
| `nestSwap` | `{a : {x : B, y : B}, b : B}` | (c) `s.a.x` borrowed alone at the lifetime of `s.b`; `s.a.y` dropped |
| `blockRead` | `{a : B, b : B}` | (d) `Imm` of the whole struct at `'c`; `s.a` alone and the whole struct read at `'c` |
| `nestRead` | `{a : {x : B, y : B}, b : B}` | (d) `Imm`: the sub-struct `s.a` and the leaf `s.b` each read at `'c` |

`B = 1 ⊕ 1`.  The callbacks `swapCb` and `readCb` are `experiments/Places`'s, unchanged: the
family type of `{a : B, b : B}` is `Places.famTy`.
-/

noncomputable section

namespace BoCa.LeafPlaces
open BoCa BoCa.Lifetime BoCa.Programs BoCa.Records BoCa.Places
open BoCa.Fig16 BoCa.Fig16.BoLo BoCa.Fig16.LogRel BoCa.Fig16.LogRel.Typed

/-! ## Structs -/

/-- `{a : B, b : B}`. -/
abbrev σ2 : Shape := .node (.leaf B) (.leaf B)

/-- `{a : {x : B, y : B}, b : B}`. -/
abbrev σ3 : Shape := .node (.node (.leaf B) (.leaf B)) (.leaf B)

/-- `inj₁ ()` or `inj₂ ()`, as a value. -/
def bval : Bool → Val
  | false => .inj₁ .unit
  | true => .inj₂ .unit

theorem bval_val (b : Bool) : (bval b).1 = Places.bv b := by cases b <;> rfl

theorem vP_bval {ls : List Typed.SRec} {δ : LSub} : ∀ b, vP B ls δ (bval b) PMap.empty
  | false => Or.inl ⟨Val.unit, pure_sep_mk rfl ⟨rfl, rfl⟩⟩
  | true => Or.inr ⟨Val.unit, pure_sep_mk rfl ⟨rfl, rfl⟩⟩

theorem vP_pair {T₁ T₂ : Ty} {ls : List Typed.SRec} {δ : LSub} {v₁ v₂ : Val}
    (h₁ : vP T₁ ls δ v₁ PMap.empty) (h₂ : vP T₂ ls δ v₂ PMap.empty) :
    vP (.tensor T₁ T₂) ls δ (.pair v₁ v₂) PMap.empty :=
  ⟨v₁, v₂, pure_sep_mk rfl ⟨PMap.empty, PMap.empty, ResU.comp_empty_right _, h₁, h₂⟩⟩

/-- The contents of a two-leaf struct. -/
def vals2 (a b : Bool) : Val := .pair (bval a) (bval b)

/-- The contents of `{a : {x, y}, b}`. -/
def vals3 (x y b : Bool) : Val := .pair (.pair (bval x) (bval y)) (bval b)

theorem d_vals2 {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) (a b : Bool) :
    DerivesWf Δ Γ (vals2 a b).1 σ2.valTy := by
  show DerivesWf Δ Γ (.pair (bval a).1 (bval b).1) (.tensor B B)
  rw [bval_val, bval_val]
  exact .tensorI hΓ.split (d_bv hΓ a) (d_bv hΓ b)

theorem d_vals3 {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) (x y b : Bool) :
    DerivesWf Δ Γ (vals3 x y b).1 σ3.valTy := by
  show DerivesWf Δ Γ (.pair (.pair (bval x).1 (bval y).1) (bval b).1) (.tensor (.tensor B B) B)
  rw [bval_val, bval_val, bval_val]
  exact .tensorI hΓ.split (.tensorI hΓ.split (d_bv hΓ x) (d_bv hΓ y)) (d_bv hΓ b)

/-- `let (a, b) = freeS σ2 r; drop a; drop b`, with `r` at index `i`: the block freed whole. -/
def freeB2 (i : Nat) : Expr :=
  .letpair (.app (freeS σ2) (.var i)) (.seq (dropB (.var 1)) (dropB (.var 0)))

/-- `let (ab, c) = freeS σ3 r; let (a, b) = ab; drop a; drop b; drop c`. -/
def freeB3 (i : Nat) : Expr :=
  .letpair (.app (freeS σ3) (.var i))
    (.letpair (.var 1) (.seq (dropB (.var 1)) (.seq (dropB (.var 0)) (dropB (.var 2)))))

/-! ## (b) Two mutable leaf borrows of one block, used together

    let (s, u) = withborS σ2 (allocS σ2 (inj₁ (), inj₂ ())) swapCb;
    u; let (a, b) = freeS σ2 s; drop a; drop b

`swapCb` (from `Places`) holds `ma, mb : Mut 'c B` and swaps them: `mem::swap(&mut s.a,
&mut s.b)`.  The struct is one block; its handle comes back from the borrow unchanged and is
freed whole. -/

def blockSwap : Expr :=
  .letpair (app2 (withborS σ2) (.app (allocS σ2) (vals2 false true).1) swapCb)
    (.seq (.var 0) (freeB2 1))

def blockSwapObs : Expr :=
  .letpair (app2 (withborS σ2) (.app (allocS σ2) (vals2 false true).1) swapCb)
    (.seq (.var 0) (.app (freeS σ2) (.var 1)))

theorem d_withborS2 {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) {T : Ty} (hT : plainB T = true) :
    DerivesWf LifeCtx.empty Γ (withborS σ2) (wTy mutM 0 LifeCtx.empty.meetOfDom σ2 T) :=
  withborSM_wf rfl 0 hT rfl hΓ

theorem d_blockSwap : DerivesWf LifeCtx.empty [] blockSwap .unit :=
  letW (T₁ := σ2.refTy) (T₂ := .unit) rfl
    (appW d_swapCb (appW (appW (d_vals2 (by dead) false true) (allocS_wf rfl (by dead)))
      (d_withborS2 (by dead) rfl))) <|
  seqW (.var (by solo)) <|
  letW (T₁ := B) (T₂ := B) rfl (appW (.var (by solo)) (freeS_wf rfl (by dead))) <|
  seqW (d_dropB (.var (by solo)) (by dead)) (d_dropB (.var (by solo)) (by dead))

theorem blockSwap_runs :
    BoLo.Steps Adequacy.emptyMem blockSwap Adequacy.emptyMem (.val .unit) :=
  adequacy _ d_blockSwap

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
  wpTS_allocBorrow (cb := ⟨swapCb, .lam⟩) ok_empty (by decide)
    (d_call (d_withborS2 (by dead) rfl) d_swapCb) rfl Adequacy.models_empty
    (vP_pair (vP_bval false) (vP_bval true))

/-! ## (c) A nested struct: `s.a.x` alone at the lifetime of `s.b`

    nestCb ≜ Λ. λf. let (sa, mb) = f; let (mx, my) = sa; forget my;
                    let (mx′, mb′) = swapFn () (mx, mb); forget mx′; forget mb′; ()

    let (s, u) = withborS σ3 (allocS σ3 ((inj₁ (), inj₁ ()), inj₂ ())) nestCb;
    u; free s whole

The family is `(Mut 'c B ⊗ Mut 'c B) ⊗ Mut 'c B`.  `s.a.x` and `s.b` are passed together to
`swapFn : ∀'d. Mut 'd B ⊗ Mut 'd B ⊸ Mut 'd B ⊗ Mut 'd B` at `'c`; `s.a.y`'s borrow is dropped. -/

def nestCb : Expr :=
  lam (lam (.letpair (.var 0) (.letpair (.var 1)
    (.seq (.app forget (.var 0))
      (.letpair (.app (inst swapFn) (.pair (.var 1) (.var 2)))
        (.seq (.app forget (.var 0)) (.seq (.app forget (.var 1)) unit')))))))

theorem d_nestCb :
    DerivesWf LifeCtx.empty [] nestCb (cbT mutM 0 LifeCtx.empty.meetOfDom σ3 .unit) :=
  .allI (S := .unit) rfl rfl (nobinds rfl) <| .lolliI rfl <|
    letW (T₁ := .tensor (.mut (.var 0) B) (.mut (.var 0) B)) (T₂ := .mut (.var 0) B) rfl
      (.var (by solo)) <|
    letW (T₁ := .mut (.var 0) B) (T₂ := .mut (.var 0) B) rfl (.var (by solo)) <|
    seqW (appW (.var (by solo)) (.forgetMutAx (by dead))) <|
    letW (T₁ := .mut (.var 0) B) (T₂ := .mut (.var 0) B) rfl
      (appW (pairW (.var (by solo)) (.var (by solo))) (d_swapFnAt (by dead))) <|
    seqW (appW (.var (by solo)) (.forgetMutAx (by dead))) <|
    seqW (appW (.var (by solo)) (.forgetMutAx (by dead)))
      (.boxIctx (.unitI (by dead)) (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (by dead)))

def nestSwap : Expr :=
  .letpair (app2 (withborS σ3) (.app (allocS σ3) (vals3 false false true).1) nestCb)
    (.seq (.var 0) (freeB3 1))

def nestSwapObs : Expr :=
  .letpair (app2 (withborS σ3) (.app (allocS σ3) (vals3 false false true).1) nestCb)
    (.seq (.var 0) (.app (freeS σ3) (.var 1)))

theorem d_withborS3 {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) {T : Ty} (hT : plainB T = true) :
    DerivesWf LifeCtx.empty Γ (withborS σ3) (wTy mutM 0 LifeCtx.empty.meetOfDom σ3 T) :=
  withborSM_wf rfl 0 hT rfl hΓ

theorem d_nestSwap : DerivesWf LifeCtx.empty [] nestSwap .unit :=
  letW (T₁ := σ3.refTy) (T₂ := .unit) rfl
    (appW d_nestCb (appW (appW (d_vals3 (by dead) false false true) (allocS_wf rfl (by dead)))
      (d_withborS3 (by dead) rfl))) <|
  seqW (.var (by solo)) <|
  letW (T₁ := .tensor B B) (T₂ := B) rfl (appW (.var (by solo)) (freeS_wf rfl (by dead))) <|
  letW (T₁ := B) (T₂ := B) rfl (.var (by solo)) <|
  seqW (d_dropB (.var (by solo)) (by dead)) <|
  seqW (d_dropB (.var (by solo)) (by dead)) (d_dropB (.var (by solo)) (by dead))

theorem nestSwap_runs :
    BoLo.Steps Adequacy.emptyMem nestSwap Adequacy.emptyMem (.val .unit) :=
  adequacy _ d_nestSwap

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
  wpTS_allocBorrow (cb := ⟨nestCb, .lam⟩) ok_empty (by decide)
    (d_call (d_withborS3 (by dead) rfl) d_nestCb) rfl Adequacy.models_empty
    (vP_pair (vP_pair (vP_bval false) (vP_bval false)) (vP_bval true))

/-! ## (d) Immutable: the whole struct at `'c`, and a leaf alone at `'c`

`readCb` (from `Places`) receives `ia, ib : Imm 'c B`, copies `ia`, reads `s.a` alone with
`readOne : ∀'d. Imm 'd B ⊸ B` and the whole struct with `readBoth : ∀'d. Imm 'd B ⊗ Imm 'd B ⊸
B ⊗ B`, both at `'c`. -/

def blockRead : Expr :=
  .letpair (app2 (withborS σ2) (.app (allocS σ2) (vals2 false true).1) readCb)
    (.seq (dropB3 0) (freeB2 1))

def blockReadObs : Expr :=
  .letpair (app2 (withborS σ2) (.app (allocS σ2) (vals2 false true).1) readCb)
    (.seq (freeB2 1) (.var 0))

theorem d_withborSI2 {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) {T : Ty} (hT : plainB T = true) :
    DerivesWf LifeCtx.empty Γ (withborS σ2) (wTy immM 0 LifeCtx.empty.meetOfDom σ2 T) :=
  withborSI_wf rfl 0 hT rfl hΓ

theorem d_blockRead : DerivesWf LifeCtx.empty [] blockRead .unit :=
  letW (T₁ := σ2.refTy) (T₂ := B3) rfl
    (appW d_readCb (appW (appW (d_vals2 (by dead) false true) (allocS_wf rfl (by dead)))
      (d_withborSI2 (by dead) rfl))) <|
  seqW (d_dropB3 (by dead)) <|
  letW (T₁ := B) (T₂ := B) rfl (appW (.var (by solo)) (freeS_wf rfl (by dead))) <|
  seqW (d_dropB (.var (by solo)) (by dead)) (d_dropB (.var (by solo)) (by dead))

theorem blockRead_runs :
    BoLo.Steps Adequacy.emptyMem blockRead Adequacy.emptyMem (.val .unit) :=
  adequacy _ d_blockRead

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
  wpTS_allocBorrow (cb := ⟨readCb, .lam⟩) ok_empty (by decide)
    (d_call (d_withborSI2 (by dead) rfl) d_readCb) rfl Adequacy.models_empty
    (vP_pair (vP_bval false) (vP_bval true))

/-! ## (d) Immutable, nested: the sub-struct `s.a` and the leaf `s.b`, each at `'c`

    nestReadCb ≜ Λ. λf. let (sa, ib) = f;
                        let (u, w) = (readBoth () sa, readOne () ib); (u, w)

`sa : Imm 'c B ⊗ Imm 'c B` is the borrow of the sub-struct `s.a`: a sub-family of the struct's
family, at the struct's lifetime. -/

def nestReadCb : Expr :=
  lam (lam (.letpair (.var 0)
    (.letpair (.pair (.app (inst readBoth) (.var 1)) (.app (inst readOne) (.var 0)))
      (.pair (.var 1) (.var 0)))))

/-- `(B ⊗ B) ⊗ B`. -/
abbrev B21 : Ty := .tensor (.tensor B B) B

theorem d_nestReadCb :
    DerivesWf LifeCtx.empty [] nestReadCb (cbT immM 0 LifeCtx.empty.meetOfDom σ3 B21) :=
  .allI (S := .unit) rfl rfl (nobinds rfl) <| .lolliI rfl <|
    letW (T₁ := famTy immM (.var 0) B B) (T₂ := .imm (.var 0) B) rfl (.var (by solo)) <|
    letW (T₁ := .tensor B B) (T₂ := B) rfl
      (pairW
        (appW (.var (by solo))
          (.allE (x := 5) (b := .top) (T := .lolli (famTy immM (.var 5) B B) (.tensor B B))
            (a := .var 0) (d_readBoth (by dead) 5 6 7 rfl rfl rfl rfl) (entailsLt_top rfl)))
        (appW (.var (by solo)) (d_readOneAt (by dead) 0 5 6 rfl rfl rfl rfl))) <|
    .boxIctx (pairW (.var (by solo)) (.var (by solo))) (outlives_ctx rfl rfl)

def dropB21 (i : Nat) : Expr :=
  .letpair (.var i) (.seq (dropB (.var 0)) (.letpair (.var 1) (.seq (dropB (.var 1)) (dropB (.var 0)))))

def nestRead : Expr :=
  .letpair (app2 (withborS σ3) (.app (allocS σ3) (vals3 false true true).1) nestReadCb)
    (.seq (dropB21 0) (freeB3 1))

def nestReadObs : Expr :=
  .letpair (app2 (withborS σ3) (.app (allocS σ3) (vals3 false true true).1) nestReadCb)
    (.seq (freeB3 1) (.var 0))

theorem d_withborSI3 {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) {T : Ty} (hT : plainB T = true) :
    DerivesWf LifeCtx.empty Γ (withborS σ3) (wTy immM 0 LifeCtx.empty.meetOfDom σ3 T) :=
  withborSI_wf rfl 0 hT rfl hΓ

theorem d_nestRead : DerivesWf LifeCtx.empty [] nestRead .unit :=
  letW (T₁ := σ3.refTy) (T₂ := B21) rfl
    (appW d_nestReadCb (appW (appW (d_vals3 (by dead) false true true) (allocS_wf rfl (by dead)))
      (d_withborSI3 (by dead) rfl))) <|
  seqW
    (letW (T₁ := .tensor B B) (T₂ := B) rfl (.var (by solo)) <|
      seqW (d_dropB (.var (by solo)) (by dead)) <|
      letW (T₁ := B) (T₂ := B) rfl (.var (by solo)) <|
      seqW (d_dropB (.var (by solo)) (by dead)) (d_dropB (.var (by solo)) (by dead))) <|
  letW (T₁ := .tensor B B) (T₂ := B) rfl (appW (.var (by solo)) (freeS_wf rfl (by dead))) <|
  letW (T₁ := B) (T₂ := B) rfl (.var (by solo)) <|
  seqW (d_dropB (.var (by solo)) (by dead)) <|
  seqW (d_dropB (.var (by solo)) (by dead)) (d_dropB (.var (by solo)) (by dead))

theorem nestRead_runs :
    BoLo.Steps Adequacy.emptyMem nestRead Adequacy.emptyMem (.val .unit) :=
  adequacy _ d_nestRead

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
  wpTS_allocBorrow (cb := ⟨nestReadCb, .lam⟩) ok_empty (by decide)
    (d_call (d_withborSI3 (by dead) rfl) d_nestReadCb) rfl Adequacy.models_empty
    (vP_pair (vP_pair (vP_bval false) (vP_bval true)) (vP_bval true))

/-! ## Pack is not a typing rule on arbitrary leaves

    let s₁ = allocS σ2 (inj₁ (), inj₁ ()); let s₂ = allocS σ2 (inj₂ (), inj₂ ());
    let (a₁, b₁) = s₁; let (a₂, b₂) = s₂;
    withborS σ2 (a₁, b₂) swapCb; …; free both

The handle type `refTy σ2 = Ref B ⊗ Ref B` is the family's, so `(a₁, b₂)` — one leaf of each
block — is a well-typed struct handle: the program is derivable, runs, and leaks nothing.  But
it is not a block's handle (`crossPack_not_packed`).  The model accepts it, since a family is
all it needs; a one-word lowering of the handle does not.  A surface language whose struct
handles are one word must therefore keep owned leaf handles from being re-paired across blocks
(and from being freed alone), for instance by handing out leaves only as borrows (`withborS`).
That is a rule of the checker, not of the model. -/

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

theorem d_crossPack : DerivesWf LifeCtx.empty [] crossPack .unit :=
  letW (T₁ := σ2.refTy) (T₂ := σ2.refTy) rfl
    (pairW (appW (d_vals2 (by dead) false false) (allocS_wf rfl (by dead)))
      (appW (d_vals2 (by dead) true true) (allocS_wf rfl (by dead)))) <|
  letW (T₁ := .ref B) (T₂ := .ref B) rfl (.var (by solo)) <|
  letW (T₁ := .ref B) (T₂ := .ref B) rfl (.var (by solo)) <|
  letW (T₁ := σ2.refTy) (T₂ := .unit) rfl
    (appW (DerivesWf.append_dead (by dead) d_swapCb)
      (appW (pairW (.var (by solo)) (.var (by solo))) (d_withborS2 (by dead) rfl))) <|
  seqW (.var (by solo)) <|
  seqW
    (letW (T₁ := B) (T₂ := B) rfl (appW (.var (by solo)) (freeS_wf rfl (by dead))) <|
      seqW (d_dropB (.var (by solo)) (by dead)) (d_dropB (.var (by solo)) (by dead))) <|
  letW (T₁ := B) (T₂ := B) rfl
    (appW (pairW (.var (by solo)) (.var (by solo))) (freeS_wf rfl (by dead))) <|
  seqW (d_dropB (.var (by solo)) (by dead)) (d_dropB (.var (by solo)) (by dead))

theorem crossPack_runs :
    BoLo.Steps Adequacy.emptyMem crossPack Adequacy.emptyMem (.val .unit) :=
  adequacy _ d_crossPack

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

end BoCa.LeafPlaces

end
