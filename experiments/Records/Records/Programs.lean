import Records.Borrows
import Records.Splits

/-!
# Programs: field access through borrows

Closed programs typed at `1`, each with its adequacy instance (`Fig16.LogRel.Typed.adequacy`)
and a kernel-checked run of the interpreter; each `…Obs` variant returns what was read or
written.

| program | shows |
|---|---|
| `readFields` | `Imm` borrow of a record: an unboxed field arrives as a copy, a `Ref` field as a view at the load's `'b` |
| `mutFields` | `Mut` borrow of a record: one field updated by `swapField`, the whole record moved out and back |
| `matchSome` | `Imm` borrow of a variant: `case` on the loaded image, the payload's cell read at `'b` |
| `getRefFn` | an `Imm 'c` field read through `Imm 'a` keeps `'c` (open derivation, `Δ = ['c ⊏ ⊤]`) |
-/

noncomputable section

namespace BoCa.Records
open BoCa BoCa.Lifetime BoCa.Programs

/-! ## Side conditions on concrete contexts -/

/-- Types built from `1`, `⊕`, `⊗` and `!`: they hold no borrow and outlive every lifetime. -/
def dataB : Ty → Bool
  | .unit => true
  | .sum T₁ T₂ => dataB T₁ && dataB T₂
  | .tensor T₁ T₂ => dataB T₁ && dataB T₂
  | .bang _ => true
  | _ => false

theorem outlives_of_dataB {Δ : LifeCtx} {a : Life} : ∀ {T : Ty}, dataB T = true → OutlivesRules Δ a T
  | .unit, _ => .unit
  | .sum _ _, h => by
      simp only [dataB, Bool.and_eq_true] at h
      exact .sum (outlives_of_dataB h.1) (outlives_of_dataB h.2)
  | .tensor _ _, h => by
      simp only [dataB, Bool.and_eq_true] at h
      exact .tensor (outlives_of_dataB h.1) (outlives_of_dataB h.2)
  | .bang _, _ => .bang

/-- `[]I`'s premise at a context whose live slots are data. -/
theorem outlives_ctx {Δ : LifeCtx} {Γ : Ctx Ty} {a : Life} (ha : a.wf Δ = true)
    (h : (Γ.all fun s => !s.live || dataB s.ty) = true) : Ctx.Outlives Δ Γ a := by
  refine ⟨LifeCtx.defines_of_wf ha, fun s hs hl => outlives_of_dataB ?_⟩
  have := List.all_eq_true.mp h s hs
  simpa [hl] using this

/-- `∀I`'s Barendregt premise at a concrete context. -/
theorem nobinds {Γ : Ctx Ty} {x : LifeVar}
    (h : (Γ.all fun s => !s.live || !s.ty.bindsB x) = true) :
    ∀ s ∈ Γ, s.live = true → s.ty.bindsB x = false := by
  intro s hs hl
  have := List.all_eq_true.mp h s hs
  simpa [hl] using this

/-! ## Reading fields through an immutable borrow

    let (r, p) = withbor (alloc {flag = inj₂ (), cell = alloc (inj₁ ())}) (Λ. λx.
                   let (x₁, x₂) = copy x;
                   let f = withload x₁ (Λ. λr. let y = r.flag in y);
                   let c = withload x₂ (Λ. λr. let v = r.cell in
                             let w = withload v (Λ. λz. z) in w);
                   (f, c));
    let (f, c) = p; drop f; drop c;
    let {flag, cell} = free r; drop flag; drop (free cell)

`r : Ref {flag : 1 ⊕ 1, cell : Ref (1 ⊕ 1)}` is borrowed at `'a`.  Each `withload` of the
borrow runs at a fresh `'b ⊏ 'a`, and its callback receives
`Imm̲ 'b {flag : 1 ⊕ 1, cell : Ref (1 ⊕ 1)} = {flag : 1 ⊕ 1, cell : Imm 'b (1 ⊕ 1)}`.

* The unboxed field arrives as a copy of its value, `1 ⊕ 1`, which outlives `'b` and
  leaves the callback.
* The boxed field arrives as a view `Imm 'b (1 ⊕ 1)` of its cell, at the load's `'b`, not at
  the borrow's `'a`.  It cannot leave the callback (`['b] (Imm 'b _)` needs `'b ⊏ 'b`); its
  contents are read by a second `withload`, at `'c ⊏ 'b`. -/

/-- `{flag : 1 ⊕ 1, cell : Ref (1 ⊕ 1)}`. -/
def ptF : List Field := [("flag", B), ("cell", .ref B)]

def mkPt : Expr := tuple [.inj₂ unit', .app alloc' (.inj₁ unit')]

/-- The load of `cell`'s view, at `'c` = variable `2`. -/
def readCell : Expr :=
  elet (app2 withload (.var 0) (lam (lam (.var 0)))) (.var 0)

def readBody : Expr :=
  .letpair (.app copy (.var 0))
    (elet (loadField ptF 0 1 (.var 1) (.var 0))
      (elet (loadField ptF 1 1 (.var 1) readCell) (.pair (.var 1) (.var 0))))

def readBorrower : Expr := lam (lam readBody)

/-- `let {flag, cell} = free r; drop flag; drop (free cell)`, with `r` at index `i`. -/
def freePt (i : Nat) : Expr :=
  recLet 2 (.app free' (.var i)) (.seq (dropB (.var 3)) (dropB (.app free' (.var 1))))

def readFields : Expr :=
  .letpair (app2 withbor (.app alloc' mkPt) readBorrower)
    (.letpair (.var 0) (.seq (dropB (.var 1)) (.seq (dropB (.var 0)) (freePt 3))))

/-- The same run, returning the pair read through the borrow. -/
def readFieldsObs : Expr :=
  .letpair (app2 withbor (.app alloc' mkPt) readBorrower)
    (.seq (freePt 1) (.var 0))

/-- `Δ' = ['b ⊏ ⊓D1, 'a ⊏ ⊤]`, the load's context. -/
abbrev D1b : LifeCtx := D1.extend 1 D1.meetOfDom

/-- `{flag : 1 ⊕ 1, cell : Ref (1 ⊕ 1)}`, the record type. -/
abbrev Pt : Ty := recTy ptF

/-- `dropB e`, typed. -/
theorem d_dropB {Δ : LifeCtx} {Γ : Ctx Ty} {e : Expr}
    (he : DerivesWf Δ (part e 0 Γ).1 e B) (hΓ : Ctx.Dead (part e 0 Γ).2) :
    DerivesWf Δ Γ (dropB e) .unit :=
  caseW rfl he (.var (.here hΓ)) (.var (.here hΓ))

theorem d_freePt {Γ : Ctx Ty} (h : DerivesWf LifeCtx.empty (part (.app free' (.var 3)) 0 Γ).1
      (.app free' (.var 3)) Pt)
    (hΓ : Ctx.Dead (part (.app free' (.var 3)) 0 Γ).2) :
    DerivesWf LifeCtx.empty Γ (freePt 3) .unit :=
  recE ptF (part_split (.app free' (.var 3)) 0 Γ) rfl h
    (seqW (d_dropB (.var (by solo)) (by dead))
      (d_dropB (appW (.var (by solo)) (.freeAx (by dead))) (by dead)))

/-- The borrower: `Λ. λx. …`, at `∀'a ⊏ ⊤. Imm 'a Pt ⊸ ['a] (1 ⊕ 1 ⊗ 1 ⊕ 1)`. -/
theorem d_readBorrower :
    DerivesWf LifeCtx.empty [] readBorrower
      (.all 0 .top (.lolli (.imm (.var 0) Pt) (.box (.var 0) (.tensor B B)))) :=
  .allI (S := .unit) rfl rfl (nobinds rfl) <| .lolliI rfl <|
    letW (T₁ := .imm (.var 0) Pt) (T₂ := .imm (.var 0) Pt) rfl
      (appW (.var (by solo)) (.copyAx (by dead))) <|
    appW
      (loadField_wf (a := .var 0) (T₂ := B) (.var (by solo)) rfl rfl rfl rfl
        (.boxIctx (.var (by solo)) (outlives_ctx rfl rfl)))
      (.lolliI rfl <| appW
        (loadField_wf (a := .var 0) (T₂ := B) (.var (by solo)) rfl rfl rfl rfl
          -- `readCell`: the view `Imm 'b (1 ⊕ 1)` read by a second `withload`, at `'c`.
          (appW
            (appW
              (.allI (S := .unit) rfl rfl (nobinds rfl)
                (.lolliI rfl (.boxIctx (.var (by solo)) (outlives_ctx rfl rfl))))
              (appW (.var (by solo))
                (.withloadAx (a := .var 1) (T₁ := B) (T₂ := B) (by dead) 2 rfl rfl)))
            (.lolliI rfl (.boxIctx (.var (by solo)) (outlives_ctx rfl rfl)))))
        (.lolliI rfl (.boxIctx (pairW (.var (by solo)) (.var (by solo))) (outlives_ctx rfl rfl))))

theorem d_readFields : DerivesWf LifeCtx.empty [] readFields .unit :=
  letW (T₁ := .ref Pt) (T₂ := .tensor B B) rfl
    (appW d_readBorrower
      (appW (appW (pairW (.sumI₂ (.unitI (by dead)))
          (pairW (appW (.sumI₁ (.unitI (by dead))) (.allocAx (by dead))) (.unitI (by dead))))
          (.allocAx (by dead)))
        (.withbor1Ax (T₁ := Pt) (T₂ := .tensor B B) (by dead) 0 rfl rfl))) <|
  letW (T₁ := B) (T₂ := B) rfl (.var (by solo)) <|
  seqW (d_dropB (.var (by solo)) (by dead)) <|
  seqW (d_dropB (.var (by solo)) (by dead)) <|
  d_freePt (appW (.var (by solo)) (.freeAx (by dead))) (by dead)

/-- The record is read through the borrow, and the program leaves no cell. -/
theorem readFields_runs :
    BoLo.Steps Adequacy.emptyMem readFields Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_readFields

theorem readFields_eval : unitNoLeak (eval readFields) = true := by decide

/-- The pair read: `flag`'s copy `inj₂ ()` and `cell`'s contents `inj₁ ()`. -/
theorem readFieldsObs_eval :
    (match eval readFieldsObs with
      | .value ⟨.pair (.inj₂ .unit) (.inj₁ .unit), _⟩ false => true
      | _ => false) = true := by decide

/-! ## Updating one field through a mutable borrow

    let (r, u) = withbor (alloc {flag = inj₂ (), cell = alloc (inj₁ ())}) (Λ. λm.
                   let (m₁, u₁) = withswap m (λp. let (x, rest) = p;
                                                  let (x′, t) = flip x; ((x′, rest), t));
                   u₁;
                   let (m₂, u₂) = withswap m₁ (λp. let (x, rest) = p;
                                                   let ((c, ()), t) = … pokeG c …;
                                                   ((x, (c, ())), t));
                   u₂; forget m₂; ());
    u; let {flag, cell} = free r; drop flag; drop (free cell)

Each update is `swapField` (`withswap` with `modAt`).  There is no `Mut` to a field: `withswap`
moves the whole record out of its cell, the callback rebuilds it with one field changed, and
`withswap` stores the whole record back.  The unboxed `flag` is replaced by value.  The boxed
`cell` is written through a `Mut 'c` borrow of its own cell, taken by `withbor` on the `Ref` the
callback holds (`pokeG`); that borrow ends inside the callback, and the record's own cell is
still loaded and stored around it. -/

/-- `λb. (case b {x ⇒ inj₂ x, y ⇒ inj₁ y}, ())`. -/
def flipG : Expr := lam (.pair (.case (.var 0) (.inj₂ (.var 0)) (.inj₁ (.var 0))) unit')

/-- `λb. (inj₂ (), drop b)`. -/
def setG : Expr := lam (.pair (.inj₂ unit') (dropB (.var 0)))

/-- `λc. withbor c (Λ. λm. let (m′, u) = withswap m setG; u; forget m′; ())`: the field's own
cell, borrowed mutably at a fresh `'c` inside the record's `withswap` callback. -/
def pokeG : Expr :=
  lam (app2 withbor (.var 0) (lam (lam (.letpair (app2 withswap (.var 0) setG)
    (.seq (.var 0) (.seq (.app forget (.var 1)) unit'))))))

theorem d_flipG {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ Γ flipG (.lolli B (.tensor B .unit)) :=
  .lolliI rfl (pairW (caseW rfl (.var (by solo)) (.sumI₂ (.var (by solo))) (.sumI₁ (.var (by solo))))
    (.unitI (by dead)))

theorem d_setG {Δ : LifeCtx} {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf Δ Γ setG (.lolli B (.tensor B .unit)) :=
  .lolliI rfl (pairW (.sumI₂ (.unitI (by dead))) (d_dropB (.var (by solo)) (by dead)))

theorem d_pokeG {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) :
    DerivesWf D1 Γ pokeG (.lolli (.ref B) (.tensor (.ref B) .unit)) :=
  .lolliI rfl <|
    appW
      (.allI (S := .unit) rfl rfl (Ctx.Dead.noBinds (by dead) 1) <| .lolliI rfl <|
        letW (T₁ := .mut (.var 1) B) (T₂ := .unit) rfl
          (appW (d_setG (by dead)) (appW (.var (by solo)) (.withswapAx (by dead)))) <|
        seqW (.var (by solo)) <|
        seqW (appW (.var (by solo)) (.forgetMutAx (by dead)))
          (.boxIctx (.unitI (by dead)) (Ctx.Dead.outlives (LifeCtx.defines_of_wf rfl) (by dead))))
      (appW (.var (by solo))
        (.withbor2Ax (T₁ := B) (T₂ := .unit) (by dead) 1 rfl
          ⟨.top, LifeCtx.defines_of_wf rfl, outlives_of_dataB rfl⟩ rfl))

def mutBody : Expr :=
  .letpair (swapField ptF 0 (.var 0) flipG)
    (.seq (.var 0) (.letpair (swapField ptF 1 (.var 1) pokeG)
      (.seq (.var 0) (.seq (.app forget (.var 1)) unit'))))

def mutBorrower : Expr := lam (lam mutBody)

def mutFields : Expr :=
  .letpair (app2 withbor (.app alloc' mkPt) mutBorrower) (.seq (.var 0) (freePt 1))

/-- The same run, returning the record's contents after the updates. -/
def mutFieldsObs : Expr :=
  .letpair (app2 withbor (.app alloc' mkPt) mutBorrower)
    (.seq (.var 0) (recLet 2 (.app free' (.var 1)) (.pair (.var 3) (.app free' (.var 1)))))

theorem d_mutBorrower :
    DerivesWf LifeCtx.empty [] mutBorrower
      (.all 0 .top (.lolli (.mut (.var 0) Pt) (.box (.var 0) .unit))) :=
  .allI (S := .unit) rfl rfl (nobinds rfl) <| .lolliI rfl <|
    letW (T₁ := .mut (.var 0) Pt) (T₂ := .unit) rfl
      (swapField_wf (.var (by solo)) rfl (fun h => d_flipG h) rfl rfl) <|
    seqW (.var (by solo)) <|
    letW (T₁ := .mut (.var 0) Pt) (T₂ := .unit) rfl
      (swapField_wf (.var (by solo)) rfl (fun h => d_pokeG h) rfl rfl) <|
    seqW (.var (by solo)) <|
    seqW (appW (.var (by solo)) (.forgetMutAx (by dead)))
      (.boxIctx (.unitI (by dead)) (outlives_ctx rfl rfl))

/-- `freePt 1` at the context `withbor`'s result leaves. -/
theorem d_mutFields : DerivesWf LifeCtx.empty [] mutFields .unit :=
  letW (T₁ := .ref Pt) (T₂ := .unit) rfl
    (appW d_mutBorrower
      (appW (appW (pairW (.sumI₂ (.unitI (by dead)))
          (pairW (appW (.sumI₁ (.unitI (by dead))) (.allocAx (by dead))) (.unitI (by dead))))
          (.allocAx (by dead)))
        (.withbor2Ax (T₁ := Pt) (T₂ := .unit) (by dead) 0 rfl
          ⟨.top, LifeCtx.defines_of_wf rfl, .tensor (outlives_of_dataB rfl)
            (.tensor (.ref (outlives_of_dataB rfl)) .unit)⟩ rfl))) <|
  seqW (.var (by solo)) <|
  recE ptF (part_split (.app free' (.var 1)) 0 _) rfl (appW (.var (by solo)) (.freeAx (by dead)))
    (seqW (d_dropB (.var (by solo)) (by dead))
      (d_dropB (appW (.var (by solo)) (.freeAx (by dead))) (by dead)))

theorem mutFields_runs :
    BoLo.Steps Adequacy.emptyMem mutFields Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_mutFields

theorem mutFields_eval : unitNoLeak (eval mutFields) = true := by decide

/-- After the two updates: `flag` flipped to `inj₁ ()`, `cell` holding `inj₂ ()`. -/
theorem mutFieldsObs_eval :
    (match eval mutFieldsObs with
      | .value ⟨.pair (.inj₁ .unit) (.inj₂ .unit), _⟩ false => true
      | _ => false) = true := by decide

/-! ## Matching on a variant through an immutable borrow

    let (r, o) = withbor (alloc (some (alloc (inj₁ ())))) (Λ. λx.
                   let w = withload x (Λ. λv. case v {
                             some c ⇒ let w = withload c (Λ. λz. z) in w,
                             none u ⇒ u; inj₁ () }) in w);
    drop o; case (free r) {some c ⇒ drop (free c), none u ⇒ u}

`⟨some : Ref (1 ⊕ 1) | none : 1⟩` loaded at `'b` is `⟨some : Imm 'b (1 ⊕ 1) | none : 1⟩`:
the `some` branch holds a view of the payload's cell at `'b` and reads it with a second
`withload`, as `readFields` reads `cell`. -/

/-- `⟨some : Ref (1 ⊕ 1) | none : 1⟩`. -/
def optF : Field := ("some", .ref B)
def optGs : List Field := [("none", .unit)]

abbrev Opt : Ty := varTy optF optGs

def someBranch : Expr := readCell
def noneBranch : Expr := .seq (.var 0) (.inj₁ unit')

def matchBorrower : Expr := lam (lam (elet (loadCase (.var 0) [someBranch, noneBranch]) (.var 0)))

def freeOpt (i : Nat) : Expr := .case (.app free' (.var i)) (dropB (.app free' (.var 0))) (.var 0)

def matchSome : Expr :=
  .letpair (app2 withbor (.app alloc' (injAt optGs 0 (.app alloc' (.inj₁ unit')))) matchBorrower)
    (.seq (dropB (.var 0)) (freeOpt 1))

/-- The same run, returning the value read in the `some` branch. -/
def matchSomeObs : Expr :=
  .letpair (app2 withbor (.app alloc' (injAt optGs 0 (.app alloc' (.inj₁ unit')))) matchBorrower)
    (.seq (freeOpt 1) (.var 0))

theorem d_matchBody :
    DerivesWf D1 [⟨.imm (.var 0) Opt, true⟩, ⟨.unit, false⟩]
      (elet (loadCase (.var 0) [someBranch, noneBranch]) (.var 0)) (.box (.var 0) B) :=
  appW
    (loadCase_wf (a := .var 0) (T₂ := B) (y := 1) (f := optF) (gs := optGs)
      (bs := [someBranch, noneBranch]) (.var (by solo)) rfl rfl rfl
      (.cons
        -- `some c`: the view `Imm 'b (1 ⊕ 1)`, read by a second `withload` at `'c`.
        (appW
          (appW
            (.allI (S := .unit) rfl rfl (nobinds rfl)
              (.lolliI rfl (.boxIctx (.var (by solo)) (outlives_ctx rfl rfl))))
            (appW (.var (by solo))
              (.withloadAx (a := .var 1) (T₁ := B) (T₂ := B) (by dead) 2 rfl rfl)))
          (.lolliI rfl (.boxIctx (.var (by solo)) (outlives_ctx rfl rfl))))
        -- `none u`.
        (.one (seqW (.var (by solo))
          (.boxIctx (.sumI₁ (.unitI (by dead))) (outlives_ctx rfl rfl))))))
    (.lolliI rfl (.boxIctx (.var (by solo)) (outlives_ctx rfl rfl)))

theorem d_matchBorrower :
    DerivesWf LifeCtx.empty [] matchBorrower
      (.all 0 .top (.lolli (.imm (.var 0) Opt) (.box (.var 0) B))) :=
  .allI (S := .unit) rfl rfl (nobinds rfl) (.lolliI rfl d_matchBody)

theorem d_matchSome : DerivesWf LifeCtx.empty [] matchSome .unit :=
  letW (T₁ := .ref Opt) (T₂ := B) rfl
    (appW d_matchBorrower
      (appW (appW (injAt_wf optF optGs 0 rfl (appW (.sumI₁ (.unitI (by dead))) (.allocAx (by dead))))
          (.allocAx (by dead)))
        (.withbor1Ax (T₁ := Opt) (T₂ := B) (by dead) 0 rfl rfl))) <|
  seqW (d_dropB (.var (by solo)) (by dead)) <|
  caseW rfl (appW (.var (by solo)) (.freeAx (by dead)))
    (d_dropB (appW (.var (by solo)) (.freeAx (by dead))) (by dead)) (.var (by solo))

theorem matchSome_runs :
    BoLo.Steps Adequacy.emptyMem matchSome Adequacy.emptyMem (.val .unit) :=
  Fig16.LogRel.Typed.adequacy _ d_matchSome

theorem matchSome_eval : unitNoLeak (eval matchSome) = true := by decide

/-- The `some` branch read the payload's contents, `inj₁ ()`. -/
theorem matchSomeObs_eval :
    (match eval matchSomeObs with
      | .value ⟨.inj₁ .unit, _⟩ false => true
      | _ => false) = true := by decide

/-! ## A borrow stored in a record keeps its own lifetime

    get : ∀'a ⊏ ⊓Δ. Imm 'a {r : Imm 'c (1 ⊕ 1), n : 1 ⊕ 1} ⊸ Imm 'c (1 ⊕ 1)
    get ≜ Λ. λx. withload x (Λ. λp. let y = p.r in y)

in `Δ = ['c ⊏ ⊤]`.  `Imm̲ 'b (Imm 'c T) = Imm 'c T` (clause (6)), so the loaded field is the
stored borrow itself, at `'c`; `[]I` at `'b` needs only `'b ⊏ 'c`, which `'b ⊏ ⊓Δ` gives.
This is Rust's `fn get<'a, 'c>(s: &'a S<'c>) -> &'c T { s.r }`.  A `Ref` field has no
such exit: its image `Imm 'b T` is at the load's own `'b`, and `[]I` at `'b` would need
`Δ ⊢ Imm 'b T ⊐ 'b`, which no satisfiable `Δ` entails (`not_outlives_own_view`). -/

/-- `{r : Imm 'c (1 ⊕ 1), n : 1 ⊕ 1}`, with `'c` the variable `0`. -/
def refF : List Field := [("r", .imm (.var 0) B), ("n", B)]

def getRefFn : Expr := lam (lam (loadField refF 0 2 (.var 0) (.var 0)))

/-- The load's context: `'b = 2 ⊏ ⊓['a ⊏ ⊓D1, 'c ⊏ ⊤]`. -/
abbrev D1ab : LifeCtx := (D1.extend 1 D1.meetOfDom).extend 2 (D1.extend 1 D1.meetOfDom).meetOfDom

theorem entailsLt_b_c : D1ab.EntailsLt (.var 2) (.var 0) :=
  entailsLt_of_bound (u := (D1.extend 1 D1.meetOfDom).meetOfDom) rfl fun _ _ h => by
    obtain ⟨q, hq, hqn⟩ := interp_meet_right h
    obtain ⟨p, hp, hpq⟩ := interp_meet_left hq
    exact ⟨p, hp, le_trans hpq hqn⟩

theorem d_getRefFn :
    DerivesWf D1 [] getRefFn
      (.all 1 D1.meetOfDom (.lolli (.imm (.var 1) (recTy refF)) (.imm (.var 0) B))) :=
  .allI (S := .unit) rfl rfl (nobinds rfl) <| .lolliI rfl <|
    loadField_wf (a := .var 1) (T₂ := .imm (.var 0) B) (y := 2) (.var (by solo)) rfl rfl rfl rfl
      (.boxIctx (.var (by solo))
        (Ctx.Outlives.solo (LifeCtx.defines_of_wf rfl) (.imm entailsLt_b_c) (by dead)))

/-- `[]I` at a load's lifetime `'y` cannot take the view `Imm 'y T` that load creates. -/
theorem not_outlives_own_view {Δ : LifeCtx} (hΔ : Δ.Sat) (y : LifeVar) (T : Ty) :
    ¬ OutlivesRules Δ (.var y) (.imm (.var y) T) := by
  intro h
  cases h with
  | imm hlt =>
      obtain ⟨δ, hδ⟩ := hΔ
      obtain ⟨m, n, hm, hn, hmn⟩ := hlt δ hδ
      rw [hm] at hn
      cases hn
      exact lt_irrefl _ hmn

end BoCa.Records

end
