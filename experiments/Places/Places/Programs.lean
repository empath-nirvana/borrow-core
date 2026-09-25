import Places.Family
import Records.Programs

/-!
# Programs over place families

Closed programs typed at `1`, each with its adequacy instance (`Fig16.LogRel.Typed.adequacy`)
and a kernel-checked interpreter run; each `…Obs` variant returns what the record holds at the
end.  The record `s = {a : 1 ⊕ 1, b : 1 ⊕ 1}` is the place-record `(ra, rb) : Ref B ⊗ Ref B`,
one reference per leaf.

| program | shows |
|---|---|
| `swapBoth` | `Mut 'c` at `s.a` and at `s.b` held together; `mem::swap(&mut s.a, &mut s.b)` |
| `familyCalls` | the family passed whole to a function at `'c`, a sub-family (`s.a`) to another at `'c`, and reassembled |
| `readFamily` | the `Imm` family: copied, one leaf read by one function, the whole family by another, all at `'c` |
| `splitFour` | a 4-leaf family split into two 2-leaf halves at one lifetime (`split_at_mut`, static `n`) |
-/

noncomputable section

namespace BoCa.Places
open BoCa BoCa.Lifetime BoCa.Programs BoCa.Records

/-! ## Shared pieces -/

/-- `inj₁ ()` or `inj₂ ()`. -/
def bv : Bool → Expr
  | false => .inj₁ unit'
  | true => .inj₂ unit'

theorem d_bv {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) : ∀ b, DerivesWf Δ Γ (bv b) B
  | false => .sumI₁ (.unitI hΓ)
  | true => .sumI₂ (.unitI hΓ)

/-- `(alloc v₁, alloc v₂)`: a fresh two-leaf place-record. -/
def allocPair (b₁ b₂ : Bool) : Expr := .pair (.app alloc' (bv b₁)) (.app alloc' (bv b₂))

theorem d_allocPair {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) (b₁ b₂ : Bool) :
    DerivesWf Δ Γ (allocPair b₁ b₂) (refs B B) :=
  pairW (appW (d_bv (by dead) b₁) (.allocAx (by dead)))
    (appW (d_bv (by dead) b₂) (.allocAx (by dead)))

/-- `let (ra, rb) = r; drop (free ra); drop (free rb)`, with `r` at index `i`. -/
def freePair (i : Nat) : Expr :=
  .letpair (.var i) (.seq (dropB (.app free' (.var 1))) (dropB (.app free' (.var 0))))

/-- `let (ra, rb) = r; (free ra, free rb)`: the record's contents. -/
def readPair (i : Nat) : Expr :=
  .letpair (.var i) (.pair (.app free' (.var 1)) (.app free' (.var 0)))

/-- `Side2` at `Δ = ∅`, binders `'c = 0`, `'a = 1`, `'b = 2`, payloads `1 ⊕ 1`. -/
theorem sideMut (T : Ty) (hT : T.scopedB LifeCtx.empty = true) (hTb : T.bindsB 1 = false)
    (hTb' : T.bindsB 2 = false)
    (hinst : Ty.instLife 0 (.var 2) (.lolli (famTy mutM (.var 0) B B) (.box (.var 0) T))
      = .lolli (famTy mutM (.var 2) B B) (.box (.var 2) T))
    (hcb : (cbTy mutM 0 LifeCtx.empty.meetOfDom B B T).scopedB LifeCtx.empty = true) :
    Side2 mutM LifeCtx.empty 0 1 2 B B T :=
  ⟨rfl, rfl, by decide, by decide, by decide, rfl, rfl, hT, rfl, rfl, hTb, rfl, rfl, hTb', hinst,
    hcb, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem sideImm (T : Ty) (hT : T.scopedB LifeCtx.empty = true) (hTb : T.bindsB 1 = false)
    (hTb' : T.bindsB 2 = false)
    (hinst : Ty.instLife 0 (.var 2) (.lolli (famTy immM (.var 0) B B) (.box (.var 0) T))
      = .lolli (famTy immM (.var 2) B B) (.box (.var 2) T))
    (hcb : (cbTy immM 0 LifeCtx.empty.meetOfDom B B T).scopedB LifeCtx.empty = true) :
    Side2 immM LifeCtx.empty 0 1 2 B B T :=
  ⟨rfl, rfl, by decide, by decide, by decide, rfl, rfl, hT, rfl, rfl, hTb, rfl, rfl, hTb', hinst,
    hcb, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- `withborM2` at `Δ = ∅`, payloads `1 ⊕ 1`, result `1`. -/
theorem d_withborM2 {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf LifeCtx.empty Γ withbor2 (withbor2Ty mutM 0 .top B B .unit) :=
  withborM2_wf (sideMut .unit rfl rfl rfl rfl rfl)
    ⟨.top, LifeCtx.defines_of_wf rfl, outlives_of_dataB rfl⟩ (outlives_of_dataB rfl) .unit hΓ

/-! ## (b) Two mutable borrows at one lifetime, used together

    let (s, u) = withborM2 (alloc (inj₁ ()), alloc (inj₂ ())) (Λ. λm.
                   let (ma, mb) = m;
                   let (ma′, u₁) = withswap ma (λva.
                                     let (mb′, vb) = withswap mb (λvb. (va, vb));
                                     forget mb′; (vb, ()));
                   u₁; forget ma′; ());
    u; let (ra, rb) = s; drop (free ra); drop (free rb)

The callback holds `ma : Mut 'c B` and `mb : Mut 'c B` at the same `'c`, and uses `mb` inside
`ma`'s `withswap`: this is `std::mem::swap(&mut s.a, &mut s.b)`. -/

/-- `λvb. (va, vb)`, `va` at index 1. -/
def swapIn : Expr := lam (.pair (.var 1) (.var 0))

/-- `λva. let (mb′, vb) = withswap mb swapIn; forget mb′; (vb, ())`, `mb` at index 1. -/
def swapOut : Expr :=
  lam (.letpair (app2 withswap (.var 1) swapIn) (.seq (.app forget (.var 1)) (.pair (.var 0) unit')))

/-- The swap on `ma` (index 1) and `mb` (index 0), ending in `forget ma′`. -/
def swapBody (k : Expr) : Expr :=
  .letpair (app2 withswap (.var 1) swapOut) (.seq (.var 0) (.seq (.app forget (.var 1)) k))

def swapCb : Expr := lam (lam (.letpair (.var 0) (swapBody unit')))

def swapBoth : Expr :=
  .letpair (app2 withbor2 (allocPair false true) swapCb) (.seq (.var 0) (freePair 1))

def swapBothObs : Expr :=
  .letpair (app2 withbor2 (allocPair false true) swapCb) (.seq (.var 0) (readPair 1))

theorem d_swapIn {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ (⟨B, true⟩ :: Γ) swapIn (.lolli B (.tensor B B)) :=
  .lolliI rfl (pairW (.var (by solo)) (.var (by solo)))

theorem d_swapOut {Δ : LifeCtx} {Γ : Ctx Ty} {a : Life} (ha : a.wf Δ = true) (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ (⟨.mut a B, true⟩ :: Γ) swapOut (.lolli B (.tensor B .unit)) :=
  .lolliI rfl <|
    letW (T₁ := .mut a B) (T₂ := B) (by simp [Ty.scopedB, ha])
      (appW (d_swapIn (by dead)) (appW (.var (by solo)) (.withswapAx (by dead)))) <|
    seqW (appW (.var (by solo)) (.forgetMutAx (by dead))) (pairW (.var (by solo)) (.unitI (by dead)))

/-- The swap, at `ma, mb : Mut @a B`, followed by `k`. -/
theorem d_swapBody {Δ : LifeCtx} {Γ : Ctx Ty} {a : Life} {k : Expr} {T : Ty} (ha : a.wf Δ = true)
    (hΓ : Ctx.Dead Γ)
    (hk : ∀ {Γ' : Ctx Ty}, Ctx.Dead Γ' → DerivesWf Δ Γ' k T) :
    DerivesWf Δ (⟨.mut a B, true⟩ :: ⟨.mut a B, true⟩ :: Γ) (swapBody k) T :=
  letW (T₁ := .mut a B) (T₂ := .unit) (by simp [Ty.scopedB, ha])
    (appW (d_swapOut ha (by dead)) (appW (.var (by solo)) (.withswapAx (by dead)))) <|
  seqW (.var (by solo)) <|
  seqW (appW (.var (by solo)) (.forgetMutAx (by dead))) (hk (by dead))

theorem d_swapCb :
    DerivesWf LifeCtx.empty [] swapCb (cbTy mutM 0 .top B B .unit) :=
  .allI (S := .unit) rfl rfl (nobinds rfl) <| .lolliI rfl <|
    letW (T₁ := .mut (.var 0) B) (T₂ := .mut (.var 0) B) rfl (.var (by solo)) <|
    d_swapBody rfl (by dead) fun hΓ' =>
      .boxIctx (.unitI hΓ') (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) hΓ')

theorem d_swapBoth : DerivesWf LifeCtx.empty [] swapBoth .unit :=
  letW (T₁ := refs B B) (T₂ := .unit) rfl
    (appW d_swapCb (appW (d_allocPair (by dead) false true) (d_withborM2 (by dead)))) <|
  seqW (.var (by solo)) <|
  letW (T₁ := .ref B) (T₂ := .ref B) rfl (.var (by solo)) <|
  seqW (d_dropB (appW (.var (by solo)) (.freeAx (by dead))) (by dead))
    (d_dropB (appW (.var (by solo)) (.freeAx (by dead))) (by dead))

theorem swapBoth_runs :
    BoLo.Steps Adequacy.emptyMem swapBoth Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_swapBoth

theorem swapBoth_eval : unitNoLeak (eval swapBoth) = true := by decide

/-- `s.a` and `s.b` swapped: `(inj₂ (), inj₁ ())` from `(inj₁ (), inj₂ ())`. -/
theorem swapBothObs_eval :
    (match eval swapBothObs with
      | .value ⟨.pair (.inj₂ .unit) (.inj₁ .unit), _⟩ false => true
      | _ => false) = true := by decide

/-! ## (c) The family passed whole, and a sub-family, to functions at the same lifetime

    swapFn : ∀'d ⊏ ⊤. Mut 'd B ⊗ Mut 'd B ⊸ Mut 'd B ⊗ Mut 'd B     -- the whole record
    setFn  : ∀'d ⊏ ⊤. Mut 'd B ⊸ Mut 'd B                            -- one field

    let (s, u) = withborM2 (alloc (inj₁ ()), alloc (inj₁ ())) (Λ. λm.
                   let (ma, mb) = swapFn () m;       -- whole family, at 'c
                   let ma′ = setFn () ma;             -- sub-family s.a, at 'c
                   let (ma″, mb″) = swapFn () (ma′, mb);   -- reassembled, at 'c
                   forget ma″; forget mb″; ());
    u; let (ra, rb) = s; drop (free ra); drop (free rb)

Every call is `∀E` at the callback's own `'c`: Rust's
`fn swap_fields<'d>(s: (&'d mut A, &'d mut B)) -> (&'d mut A, &'d mut B)` called with the
record's borrow, and `fn set<'d>(a: &'d mut A) -> &'d mut A` with the field's. -/

/-- `λva. let (mb′, vb) = withswap mb swapIn; (vb, mb′)`, `mb` at index 1. -/
def swapOutK : Expr := lam (.letpair (app2 withswap (.var 1) swapIn) (.pair (.var 0) (.var 1)))

/-- `Λ. λm. let (ma, mb) = m; withswap ma swapOutK`. -/
def swapFn : Expr := lam (lam (.letpair (.var 0) (app2 withswap (.var 1) swapOutK)))

/-- `Λ. λm. let (m′, u) = withswap m setG; u; m′`. -/
def setFn : Expr := lam (lam (.letpair (app2 withswap (.var 0) setG) (.seq (.var 0) (.var 1))))

/-- `M 'd B ⊗ M 'd B ⊸ M 'd B ⊗ M 'd B`. -/
abbrev famEndo (d : LifeVar) : Ty := .lolli (famTy mutM (.var d) B B) (famTy mutM (.var d) B B)

theorem d_swapOutK {Δ : LifeCtx} {Γ : Ctx Ty} {a : Life} (ha : a.wf Δ = true) (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ (⟨.mut a B, true⟩ :: Γ) swapOutK (.lolli B (.tensor B (.mut a B))) :=
  .lolliI rfl <|
    letW (T₁ := .mut a B) (T₂ := B) (by simp [Ty.scopedB, ha])
      (appW (d_swapIn (by dead)) (appW (.var (by solo)) (.withswapAx (by dead)))) <|
    pairW (.var (by solo)) (.var (by solo))

theorem d_swapFn {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) (d : LifeVar) (hd : Δ.find? d = none) :
    DerivesWf Δ Γ swapFn (.all d .top (famEndo d)) :=
  .allI (S := .unit) hd rfl (Ctx.Dead.noBinds hΓ d) <|
    .lolliI (by simp [famTy, Ty.scopedB, wf_var_self]) <|
    letW (T₁ := .mut (.var d) B) (T₂ := .mut (.var d) B) (by simp [Ty.scopedB, wf_var_self])
      (.var (by solo)) <|
    appW (d_swapOutK (wf_var_self _ _ _) (by dead)) (appW (.var (by solo)) (.withswapAx (by dead)))

theorem d_setFn {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) (d : LifeVar) (hd : Δ.find? d = none) :
    DerivesWf Δ Γ setFn (.all d .top (.lolli (.mut (.var d) B) (.mut (.var d) B))) :=
  .allI (S := .unit) hd rfl (Ctx.Dead.noBinds hΓ d) <|
    .lolliI (by simp [Ty.scopedB, wf_var_self]) <|
    letW (T₁ := .mut (.var d) B) (T₂ := .unit) (by simp [Ty.scopedB, wf_var_self])
      (appW (d_setG (by dead)) (appW (.var (by solo)) (.withswapAx (by dead)))) <|
    seqW (.var (by solo)) (.var (by solo))

/-- `swapFn ()` at `'c = 0`, in the callback's context `Δ = ['c ⊏ ⊤]`. -/
theorem d_swapFnAt {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf D1 Γ (inst swapFn) (famEndo 0) := by
  have h := DerivesWf.allE (a := .var 0) (d_swapFn (Δ := D1) hΓ 5 rfl) (entailsLt_top rfl)
  exact h

theorem d_setFnAt {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf D1 Γ (inst setFn) (.lolli (.mut (.var 0) B) (.mut (.var 0) B)) := by
  have h := DerivesWf.allE (a := .var 0) (d_setFn (Δ := D1) hΓ 5 rfl) (entailsLt_top rfl)
  exact h

/-- The callback body after the first call: `ma` at 1, `mb` at 0. -/
def famRest : Expr :=
  elet (.app (inst setFn) (.var 1))
    (.letpair (.app (inst swapFn) (.pair (.var 0) (.var 1)))
      (.seq (.app forget (.var 1)) (.seq (.app forget (.var 0)) unit')))

def famCb : Expr := lam (lam (.letpair (.app (inst swapFn) (.var 0)) famRest))

def familyCalls : Expr :=
  .letpair (app2 withbor2 (allocPair false false) famCb) (.seq (.var 0) (freePair 1))

def familyCallsObs : Expr :=
  .letpair (app2 withbor2 (allocPair false false) famCb) (.seq (.var 0) (readPair 1))

theorem d_famCb : DerivesWf LifeCtx.empty [] famCb (cbTy mutM 0 .top B B .unit) :=
  .allI (S := .unit) rfl rfl (nobinds rfl) <| .lolliI rfl <|
    letW (T₁ := .mut (.var 0) B) (T₂ := .mut (.var 0) B) rfl
      (appW (.var (by solo)) (d_swapFnAt (by dead))) <|
    appW (appW (.var (by solo)) (d_setFnAt (by dead))) <|
    .lolliI rfl <|
    letW (T₁ := .mut (.var 0) B) (T₂ := .mut (.var 0) B) rfl
      (appW (pairW (.var (by solo)) (.var (by solo))) (d_swapFnAt (by dead))) <|
    seqW (appW (.var (by solo)) (.forgetMutAx (by dead))) <|
    seqW (appW (.var (by solo)) (.forgetMutAx (by dead)))
      (.boxIctx (.unitI (by dead)) (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (by dead)))

theorem d_familyCalls : DerivesWf LifeCtx.empty [] familyCalls .unit :=
  letW (T₁ := refs B B) (T₂ := .unit) rfl
    (appW d_famCb (appW (d_allocPair (by dead) false false) (d_withborM2 (by dead)))) <|
  seqW (.var (by solo)) <|
  letW (T₁ := .ref B) (T₂ := .ref B) rfl (.var (by solo)) <|
  seqW (d_dropB (appW (.var (by solo)) (.freeAx (by dead))) (by dead))
    (d_dropB (appW (.var (by solo)) (.freeAx (by dead))) (by dead))

theorem familyCalls_runs :
    BoLo.Steps Adequacy.emptyMem familyCalls Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_familyCalls

theorem familyCalls_eval : unitNoLeak (eval familyCalls) = true := by decide

/-- From `(inj₁ (), inj₁ ())`: swap, set `a`, swap gives `(inj₁ (), inj₂ ())`. -/
theorem familyCallsObs_eval :
    (match eval familyCallsObs with
      | .value ⟨.pair (.inj₁ .unit) (.inj₂ .unit), _⟩ false => true
      | _ => false) = true := by decide

/-! ## (d) The `Imm` family

    readOne  : ∀'d ⊏ ⊤. Imm 'd B ⊸ B                          ≜ Λ. λi. withload i (Λ. λv. v)
    readBoth : ∀'d ⊏ ⊤. Imm 'd B ⊗ Imm 'd B ⊸ B ⊗ B          ≜ Λ. λp. let (i, j) = p; (readOne () i, readOne () j)

    let (s, w) = withborI2 (alloc (inj₁ ()), alloc (inj₂ ())) (Λ. λi.
                   let (ia, ib) = i;
                   let (ia₁, ia₂) = copy ia;
                   let v = readOne () ia₂;           -- sub-family s.a, at 'c
                   let w = readBoth () (ia₁, ib);     -- whole family, at 'c
                   (v, w));
    drop w; let (ra, rb) = s; drop (free ra); drop (free rb)

`Imm` borrows are copied (`copy`), so the family and its sub-family coexist. -/

/-- `Λ. λi. withload i (Λ. λv. v)`. -/
def readOne : Expr := lam (lam (app2 withload (.var 0) (lam (lam (.var 0)))))

/-- `Λ. λp. let (i, j) = p; (readOne () i, readOne () j)`. -/
def readBoth : Expr :=
  lam (lam (.letpair (.var 0) (.pair (.app (inst readOne) (.var 1)) (.app (inst readOne) (.var 0)))))

theorem d_readOne {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) (d e : LifeVar)
    (hd : Δ.find? d = none) (he : (Δ.extend d .top).find? e = none) :
    DerivesWf Δ Γ readOne (.all d .top (.lolli (.imm (.var d) B) B)) := by
  have hwf : (axWithloadTy (.var d) e (Δ.extend d .top).meetOfDom B B).scopedB (Δ.extend d .top)
      = true := by
    simp [axWithloadTy, Ty.scopedB, wf_var_self, meetOfDom_wf, he, Ty.immReborrow]
  refine .allI (S := .unit) hd rfl (Ctx.Dead.noBinds hΓ d) <|
    .lolliI (by simp [Ty.scopedB, wf_var_self]) ?_
  exact appW
    (.allI (S := .unit) he (meetOfDom_wf _) (Ctx.Dead.noBinds (by dead) e) <| .lolliI rfl <|
      .boxIctx (.var (by solo))
        (Ctx.Outlives.solo (LifeCtx.defines_of_wf (wf_var_self _ _ _)) (outlives_of_dataB rfl)
          (by dead)))
    (appW (.var (by solo)) (.withloadAx (a := .var d) (T₁ := B) (T₂ := B) (by dead) e he hwf))

/-- `readOne ()` at `'x`, in a context binding `'x` below `⊤`. -/
theorem d_readOneAt {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) (x d e : LifeVar) {u : Life}
    (hx : Δ.find? x = some u) (hd : Δ.find? d = none) (he : (Δ.extend d .top).find? e = none)
    (hinst : Ty.instLife d (.var x) (.lolli (.imm (.var d) B) B) = .lolli (.imm (.var x) B) B) :
    DerivesWf Δ Γ (inst readOne) (.lolli (.imm (.var x) B) B) := by
  have h := DerivesWf.allE (a := .var x) (d_readOne hΓ d e hd he) (entailsLt_top hx)
  rwa [hinst] at h

theorem d_readBoth {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) (d d' e : LifeVar)
    (hd : Δ.find? d = none) (hd' : (Δ.extend d .top).find? d' = none)
    (he : ((Δ.extend d .top).extend d' .top).find? e = none)
    (hinst : Ty.instLife d' (.var d) (.lolli (.imm (.var d') B) B) = .lolli (.imm (.var d) B) B) :
    DerivesWf Δ Γ readBoth
      (.all d .top (.lolli (famTy immM (.var d) B B) (.tensor B B))) :=
  .allI (S := .unit) hd rfl (Ctx.Dead.noBinds hΓ d) <|
    .lolliI (by simp [famTy, Ty.scopedB, wf_var_self]) <|
    letW (T₁ := .imm (.var d) B) (T₂ := .imm (.var d) B) (by simp [Ty.scopedB, wf_var_self])
      (.var (by solo)) <|
    pairW
      (appW (.var (by solo))
        (d_readOneAt (by dead) d d' e (u := .top) (by simp [LifeCtx.find?_extend]) hd' he hinst))
      (appW (.var (by solo))
        (d_readOneAt (by dead) d d' e (u := .top) (by simp [LifeCtx.find?_extend]) hd' he hinst))

/-- The callback body after `copy`: `ia₂` at 0, `ia₁` at 1, `ib` at 2. -/
def readRest : Expr :=
  elet (.app (inst readOne) (.var 0))
    (elet (.app (inst readBoth) (.pair (.var 2) (.var 3))) (.pair (.var 1) (.var 0)))

def readCb : Expr := lam (lam (.letpair (.var 0) (.letpair (.app copy (.var 1)) readRest)))

/-- `B ⊗ (B ⊗ B)`. -/
abbrev B3 : Ty := .tensor B (.tensor B B)

/-- `let (x, yz) = w; drop x; let (y, z) = yz; drop y; drop z`, with `w` at index `i`. -/
def dropB3 (i : Nat) : Expr :=
  .letpair (.var i) (.seq (dropB (.var 1)) (.letpair (.var 0) (.seq (dropB (.var 1)) (dropB (.var 0)))))

def readFamily : Expr :=
  .letpair (app2 withbor2 (allocPair false true) readCb) (.seq (dropB3 0) (freePair 1))

def readFamilyObs : Expr :=
  .letpair (app2 withbor2 (allocPair false true) readCb) (.seq (freePair 1) (.var 0))

theorem d_withborI2 {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf LifeCtx.empty Γ withbor2 (withbor2Ty immM 0 .top B B B3) :=
  withborI2_wf (sideImm B3 rfl rfl rfl rfl rfl) (outlives_of_dataB rfl) (outlives_of_dataB rfl) hΓ

theorem d_readCb : DerivesWf LifeCtx.empty [] readCb (cbTy immM 0 .top B B B3) :=
  .allI (S := .unit) rfl rfl (nobinds rfl) <| .lolliI rfl <|
    letW (T₁ := .imm (.var 0) B) (T₂ := .imm (.var 0) B) rfl (.var (by solo)) <|
    letW (T₁ := .imm (.var 0) B) (T₂ := .imm (.var 0) B) rfl
      (appW (.var (by solo)) (.copyAx (by dead))) <|
    appW (appW (.var (by solo)) (d_readOneAt (by dead) 0 5 6 rfl rfl rfl rfl)) <|
    .lolliI rfl <|
    appW (appW (pairW (.var (by solo)) (.var (by solo)))
      (.allE (x := 5) (b := .top) (T := .lolli (famTy immM (.var 5) B B) (.tensor B B)) (a := .var 0)
        (d_readBoth (by dead) 5 6 7 rfl rfl rfl rfl) (entailsLt_top rfl))) <|
    .lolliI rfl <|
    .boxIctx (pairW (.var (by solo)) (.var (by solo))) (outlives_ctx rfl rfl)

theorem d_dropB3 {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ (⟨B3, true⟩ :: Γ) (dropB3 0) .unit :=
  letW (T₁ := B) (T₂ := .tensor B B) rfl (.var (by solo)) <|
  seqW (d_dropB (.var (by solo)) (by dead)) <|
  letW (T₁ := B) (T₂ := B) rfl (.var (by solo)) <|
  seqW (d_dropB (.var (by solo)) (by dead)) (d_dropB (.var (by solo)) (by dead))

theorem d_readFamily : DerivesWf LifeCtx.empty [] readFamily .unit :=
  letW (T₁ := refs B B) (T₂ := B3) rfl
    (appW d_readCb (appW (d_allocPair (by dead) false true) (d_withborI2 (by dead)))) <|
  seqW (d_dropB3 (by dead)) <|
  letW (T₁ := .ref B) (T₂ := .ref B) rfl (.var (by solo)) <|
  seqW (d_dropB (appW (.var (by solo)) (.freeAx (by dead))) (by dead))
    (d_dropB (appW (.var (by solo)) (.freeAx (by dead))) (by dead))

theorem readFamily_runs :
    BoLo.Steps Adequacy.emptyMem readFamily Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_readFamily

theorem readFamily_eval : unitNoLeak (eval readFamily) = true := by decide

/-- `s.a` read alone, then `(s.a, s.b)` read as a family: `(inj₁ (), (inj₁ (), inj₂ ()))`. -/
theorem readFamilyObs_eval :
    (match eval readFamilyObs with
      | .value ⟨.pair (.inj₁ .unit) (.pair (.inj₁ .unit) (.inj₂ .unit)), _⟩ false => true
      | _ => false) = true := by decide

/-! ## (e) `split_at_mut` at a static length

A slice of four is the place-record `((r₀, r₁), (r₂, r₃))`.  Its family at one lifetime is
two `withborM2`s nested: the outer borrows `(r₀, r₁)` at `'c`, the inner borrows `(r₂, r₃)` at
`'e ⊏ 'c`, and `⊑Mut` shortens `r₀`'s and `r₁`'s borrows to `'e`.  `split_at_mut(2)` is then
`⊗E` on the family:

    swapHalves : ∀'d ⊏ ⊤. (Mut 'd B ⊗ Mut 'd B) ⊗ (Mut 'd B ⊗ Mut 'd B) ⊸ 1
    swapHalves ≜ Λ. λf. let (lo, hi) = f;              -- split_at_mut(2), at 'd
                        let (l₀, l₁) = swapFn () lo;   -- each half at 'd
                        let (h₀, h₁) = swapFn () hi;
                        forget l₀; forget l₁; forget h₀; forget h₁

    let (s₀₁, s₂₃) = ((alloc (inj₁ ()), alloc (inj₂ ())), (alloc (inj₁ ()), alloc (inj₂ ())));
    let (s₀₁′, r) = withborM2 s₀₁ (Λ. λm₀₁.
                      let (q, t) = withborM2 s₂₃ (Λ. λm₂₃.
                                     let (m₀, m₁) = m₀₁; swapHalves () ((m₀, m₁), m₂₃); ());
                      (q, t));
    let (s₂₃′, u) = r; u; free all four -/

/-- `(M @a B ⊗ M @a B) ⊗ (M @a B ⊗ M @a B)`. -/
abbrev fam4 (a : Life) : Ty := .tensor (famTy mutM a B B) (famTy mutM a B B)

def swapHalves : Expr :=
  lam (lam (.letpair (.var 0)
    (.letpair (.app (inst swapFn) (.var 1))
      (.letpair (.app (inst swapFn) (.var 2))
        (.seq (.app forget (.var 0)) (.seq (.app forget (.var 1))
          (.seq (.app forget (.var 2)) (.app forget (.var 3)))))))))

theorem d_swapFnAtVar {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) (x d : LifeVar) {u : Life}
    (hx : Δ.find? x = some u) (hd : Δ.find? d = none)
    (hinst : Ty.instLife d (.var x) (famEndo d) = famEndo x) :
    DerivesWf Δ Γ (inst swapFn) (famEndo x) := by
  have h := DerivesWf.allE (a := .var x) (d_swapFn hΓ d hd) (entailsLt_top hx)
  rwa [hinst] at h

theorem d_swapHalves {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) (d d' : LifeVar)
    (hd : Δ.find? d = none) (hd' : (Δ.extend d .top).find? d' = none)
    (hinst : Ty.instLife d' (.var d) (famEndo d') = famEndo d) :
    DerivesWf Δ Γ swapHalves (.all d .top (.lolli (fam4 (.var d)) .unit)) := by
  have hs : (famTy mutM (Life.var d) B B).scopedB (Δ.extend d .top) = true := by
    simp [famTy, Ty.scopedB, wf_var_self]
  have hx : (Δ.extend d .top).find? d = some .top := by simp [LifeCtx.find?_extend]
  exact .allI (S := .unit) hd rfl (Ctx.Dead.noBinds hΓ d) <|
    .lolliI (by simp [Ty.scopedB, hs]) <|
    letW (T₁ := famTy mutM (.var d) B B) (T₂ := famTy mutM (.var d) B B) (by simp [Ty.scopedB, hs])
      (.var (by solo)) <|
    letW (T₁ := .mut (.var d) B) (T₂ := .mut (.var d) B) (by simpa [famTy] using hs)
      (appW (.var (by solo)) (d_swapFnAtVar (by dead) d d' hx hd' hinst)) <|
    letW (T₁ := .mut (.var d) B) (T₂ := .mut (.var d) B) (by simpa [famTy] using hs)
      (appW (.var (by solo)) (d_swapFnAtVar (by dead) d d' hx hd' hinst)) <|
    seqW (appW (.var (by solo)) (.forgetMutAx (by dead))) <|
    seqW (appW (.var (by solo)) (.forgetMutAx (by dead))) <|
    seqW (appW (.var (by solo)) (.forgetMutAx (by dead)))
      (appW (.var (by solo)) (.forgetMutAx (by dead)))

/-- `'y ⊑ 'x` when `'y` is bound below `'x ⊓ u`. -/
theorem entailsLe_of_meet {Δ : LifeCtx} {x y : LifeVar} {u : Life}
    (h : Δ.find? y = some (.meet (.var x) u)) : Δ.EntailsLe (.var y) (.var x) := by
  intro δ hδ
  obtain ⟨m, n, hm, hn, hlt⟩ := hδ y _ h
  obtain ⟨p, hp, hpn⟩ := interp_meet_left hn
  exact ⟨m, p, hm, hp, Nat.le_of_lt (Nat.lt_of_le_of_lt hpn hlt)⟩

/-- The inner callback's context: `['e ⊏ 'c ⊓ ⊤, 'c ⊏ ⊤]`, `'e = 3`. -/
abbrev D1e : LifeCtx := D1.extend 3 D1.meetOfDom

def innerCb : Expr :=
  lam (lam (.letpair (.var 2)
    (.seq (.app (inst swapHalves) (.pair (.pair (.var 1) (.var 0)) (.var 2))) unit')))

def outerCb : Expr := lam (lam (.letpair (app2 withbor2 (.var 2) innerCb) (.pair (.var 1) (.var 0))))

def slice4 : Expr := .pair (allocPair false true) (allocPair false true)

def splitFour : Expr :=
  .letpair slice4
    (.letpair (app2 withbor2 (.var 1) outerCb)
      (.letpair (.var 0) (.seq (.var 0) (.seq (freePair 3) (freePair 1)))))

def splitFourObs : Expr :=
  .letpair slice4
    (.letpair (app2 withbor2 (.var 1) outerCb)
      (.letpair (.var 0) (.seq (.var 0) (.pair (readPair 3) (readPair 1)))))

theorem d_innerCb {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) {S₁ : Ty} :
    DerivesWf D1 (⟨famTy mutM (.var 0) B B, true⟩ :: ⟨S₁, false⟩ :: Γ) innerCb
      (cbTy mutM 3 D1.meetOfDom B B .unit) :=
  .allI (S := .unit) rfl rfl (by
      intro t ht hl
      simp only [List.mem_cons] at ht
      rcases ht with rfl | rfl | ht
      · rfl
      · simp at hl
      · exact Ctx.Dead.noBinds hΓ 3 t ht hl) <|
    .lolliI rfl <|
    letW (T₁ := .mut (.var 0) B) (T₂ := .mut (.var 0) B) rfl (.var (by solo)) <|
    seqW
      (appW
        (pairW
          (pairW (.mutSub (.var (by solo)) (entailsLe_of_meet (u := .top) rfl))
            (.mutSub (.var (by solo)) (entailsLe_of_meet (u := .top) rfl)))
          (.var (by solo)))
        (.allE (x := 6) (b := .top) (T := .lolli (fam4 (.var 6)) .unit) (a := .var 3)
          (d_swapHalves (by dead) 6 7 rfl rfl rfl) (entailsLt_top rfl)))
      (.boxIctx (.unitI (by dead)) (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (by dead)))

/-- The inner `withborM2`, at `D1`, binders `'e = 3`, `4`, `5`. -/
theorem d_withborM2In {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf D1 Γ withbor2 (withbor2Ty mutM 3 D1.meetOfDom B B .unit) :=
  withborM2_wf (Δ := D1) (c := 3) (x := 4) (y := 5) ⟨rfl, rfl, by decide, by decide, by decide, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
    ⟨.top, LifeCtx.defines_of_wf rfl, outlives_of_dataB rfl⟩ (outlives_of_dataB rfl) .unit hΓ

/-- `(Ref B ⊗ Ref B) ⊗ 1`, the outer family's result. -/
abbrev T4 : Ty := .tensor (refs B B) .unit

theorem d_outerCb {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) {S₁ : Ty} :
    DerivesWf LifeCtx.empty (⟨refs B B, true⟩ :: ⟨S₁, false⟩ :: Γ) outerCb
      (cbTy mutM 0 .top B B T4) :=
  .allI (S := .unit) rfl rfl (by
      intro t ht hl
      simp only [List.mem_cons] at ht
      rcases ht with rfl | rfl | ht
      · rfl
      · simp at hl
      · exact Ctx.Dead.noBinds hΓ 0 t ht hl) <|
    .lolliI rfl <|
    letW (T₁ := refs B B) (T₂ := .unit) rfl
      (appW (d_innerCb (by dead)) (appW (.var (by solo)) (d_withborM2In (by dead)))) <|
    .boxIctx (pairW (.var (by solo)) (.var (by solo)))
      (outlives_two (LifeCtx.defines_of_wf rfl) .unit
        (.tensor (.ref (outlives_of_dataB rfl)) (.ref (outlives_of_dataB rfl))) (by dead))

/-- The outer `withborM2`, at `∅`, with result `(Ref B ⊗ Ref B) ⊗ 1`. -/
theorem d_withborM2Out {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf LifeCtx.empty Γ withbor2 (withbor2Ty mutM 0 .top B B T4) :=
  withborM2_wf (sideMut T4 rfl rfl rfl rfl rfl)
    ⟨.top, LifeCtx.defines_of_wf rfl, outlives_of_dataB rfl⟩ (outlives_of_dataB rfl)
    (.tensor (.tensor (.ref (outlives_of_dataB rfl)) (.ref (outlives_of_dataB rfl))) .unit) hΓ

theorem d_splitFour : DerivesWf LifeCtx.empty [] splitFour .unit :=
  letW (T₁ := refs B B) (T₂ := refs B B) rfl
    (pairW (d_allocPair (by dead) false true) (d_allocPair (by dead) false true)) <|
  letW (T₁ := refs B B) (T₂ := T4) rfl
    (appW (d_outerCb (by dead)) (appW (.var (by solo)) (d_withborM2Out (by dead)))) <|
  letW (T₁ := refs B B) (T₂ := .unit) rfl (.var (by solo)) <|
  seqW (.var (by solo)) <|
  seqW
    (letW (T₁ := .ref B) (T₂ := .ref B) rfl (.var (by solo)) <|
      seqW (d_dropB (appW (.var (by solo)) (.freeAx (by dead))) (by dead))
        (d_dropB (appW (.var (by solo)) (.freeAx (by dead))) (by dead)))
    (letW (T₁ := .ref B) (T₂ := .ref B) rfl (.var (by solo)) <|
      seqW (d_dropB (appW (.var (by solo)) (.freeAx (by dead))) (by dead))
        (d_dropB (appW (.var (by solo)) (.freeAx (by dead))) (by dead)))

theorem splitFour_runs :
    BoLo.Steps Adequacy.emptyMem splitFour Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_splitFour

theorem splitFour_eval : unitNoLeak (eval splitFour) = true := by decide

/-- Each half swapped in place: `((inj₂, inj₁), (inj₂, inj₁))` from `((inj₁, inj₂), (inj₁, inj₂))`. -/
theorem splitFourObs_eval :
    (match eval splitFourObs with
      | .value ⟨.pair (.pair (.inj₂ .unit) (.inj₁ .unit)) (.pair (.inj₂ .unit) (.inj₁ .unit)), _⟩
          false => true
      | _ => false) = true := by decide

end BoCa.Places

end
