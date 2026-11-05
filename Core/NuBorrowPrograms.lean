import Core.NuBorrow
import Core.IntPrograms

/-!
# Core — programs over codata whose observations take borrowed arguments  `[spec §7, §22, §23]`

A closed program over `File^⊤ = νX. ((∀'x ⊏ ⊤. Mut 'x I32 ⊸ F(I32 ⊗ [⊤] U X))
& (∀'x ⊏ ⊤. Imm 'x I32 ⊸ F(I32 ⊗ [⊤] U X))) & F I32` (`Core/NuBorrow.lean`'s `fileBody` at the
bound `⊤`), one `CDerives` derivation run by `adequacyC`:

    let b = alloc 7;  let g = unfold step;  let s = alloc 5;
    let (b', r) = withbor b (Λ'y. λm. let r = g s π₁ π₁ [] m in [r]);
    let (n, rest) = r;
    let (b'', r₂) = withbor b' (Λ'y. λi. let r = (let u = unbox rest in u π₁ π₂ [] i) in [r]);
    let (n₂, rest₂) = r₂;  let k = (unbox rest₂) π₂;  let v = free b'';  ()

`step` builds the object over the state `s : Ref I32`: `read` releases the buffer's `Mut 'x I32`
and answers `(1, [s])`, `write` releases its `Imm 'x I32` and answers `(2, [s])`, and `close` frees
the state and answers its content. The object is made by `unfold` (`CDerives.unfoldN`). Its
`read` is called inside a `withbor` of the buffer lent `mut` (`CDerives.withbor2`) at the lend's
`'y`: `∀E` at `'y` leaves the rest `[⊤] U File^⊤` free of `'y` (`fileTop_read_inst`), so the
callback's answer `(n, rest)` is boxed at `'y` by `[]I` (the rest outlives `'y` by the box rule)
and leaves the lend. The rest is then captured by a second callback, the buffer lent `imm`
(`CDerives.withbor1`), and its `write` called there the same way (`fileTop_write_inst`). The
rest that leaves the second lend is closed, and the buffer freed.

* `d_fileReadProg`: the closed derivation at `1`; `fileReadProg_runs`: `adequacyC` at it, from
  the empty memory to `()` and the empty memory; `fileReadProg_eval`: the interpreter, `()` with
  no cell left.
* `d_fileReadOut`, `fileReadOut_eval`: the variant that answers `(n, (n₂, (k, v)))`, run by the
  interpreter to `(1, (2, (5, 7)))` with no cell left.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa
open BoCa.Fig16
open BoCa.Lifetime (LSub LifeCtx LifeVar)
open BoCa.Programs (alloc' free' app2)

/-! ### The object -/

/-- The state, `Ref I32`. -/
abbrev fileS : VTy := .ref bufT

/-- `File^⊤`'s body, its observations' binder `'1`. -/
abbrev fileTopC : CTy := fileBody 1 .top

/-- `U(File^⊤)`. -/
abbrev fileTopU : VTy := fileT 1 .top

/-- `unfold step`'s value, `U(S ⊸ File^⊤)`. -/
abbrev fileGenT : VTy := .thunk (.arr fileS (.nu fileTopC))

/-- What `read` answers: `I32 ⊗ [⊤] U File^⊤`. -/
abbrev fileReadRes : VTy := .tensor bufT (.box .top fileTopU)

theorem fileTopC_nuOk : fileTopC.NuOk := fileBody_nuOk rfl

theorem fileTopC_bindsFresh : fileTopC.BindsFresh fileS := by
  intro x _; simp [VFree]

/-- Data, and cells of data: they outlive every lifetime. -/
def refDataB : VTy → Bool
  | .ref A => dataB A
  | A => dataB A

theorem outlives_of_refDataB {Δ : LifeCtx} {a : Lifetime.Life} {A : VTy}
    (h : refDataB A = true) : VOutlives Δ a A := by
  cases A <;> first
    | exact .ref (outlives_of_dataB (by simpa [refDataB] using h))
    | exact outlives_of_dataB (by simpa [refDataB] using h)

/-- `[]I`'s premise at a context whose live slots are data or cells of data. -/
theorem outlives_ctxR {Δ : LifeCtx} {Γ : Ctx VTy} {a : Lifetime.Life} (ha : Δ.Defines a)
    (h : (Γ.all fun s => !s.live || refDataB s.ty) = true) : CtxOutlives Δ Γ a := by
  refine ⟨ha, fun s hs hl => outlives_of_refDataB ?_⟩
  have := List.all_eq_true.mp h s hs
  simpa [hl] using this

/-- `λs. ⟨⟨Λ. λm. forget m; (1, s), Λ. λb. forget b; (2, s)⟩, free s⟩`. -/
def fileStep : Val :=
  .lam (withPair
    (withPair
      (.val (.lam (.val (.lam (.seq (.app forget (.var 0)) (.pair (i32E 1) (.var 6)))))))
      (.val (.lam (.val (.lam (.seq (.app forget (.var 0)) (.pair (i32E 2) (.var 6))))))))
    (.app free' (.var 2)))

/-- The step's observation at `Mut` or `Imm`: release the borrow, answer `(n, [s])`. -/
theorem d_fileObs (n : UInt32) (R : Lifetime.Life → VTy)
    (hR : ∀ {Γ : Ctx VTy}, Ctx.Dead Γ →
      CDerives (LifeCtx.empty.extend 1 .top) Γ forget (.val (.lolli (R (.var 1)) .unit))) :
    CDerives LifeCtx.empty
      (withCtx (withCtx [⟨fileS, true⟩, ⟨fileS, false⟩]))
      (.val (.lam (.val (.lam (.seq (.app forget (.var 0)) (.pair (i32E n) (.var 6)))))))
      (.comp (.all 1 .top (.arr (R (.var 1)) (.ret (.tensor bufT (.box .top fileS)))))) := by
  refine .allI (S := .unit) rfl
    (fun _ _ h => by simp [LifeCtx.empty, LifeCtx.find?, Lifetime.assocFind] at h)
    (fun s hs hl => ?_) (.lam (.ret ?_))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [VFree]
  · refine seqW (appW (.var (by csolo)) (hR (by cdead))) ?_
    refine pairW (d_i32 n (Ctx.Dead.toP (by cdead))) (.boxI (.var (by csolo)) ?_)
    exact outlives_ctxR (LifeCtx.defines_of_wf rfl) (by simp [part, occ, i32E, forget, unit', refDataB, dataB]; split <;> simp [dataB])

theorem d_fileStep :
    CDerives LifeCtx.empty [⟨fileS, false⟩] (.val fileStep)
      (.val (.bang (.thunk (.arr fileS (fileTopC.instT fileS))))) := by
  refine .bangThunkV (banged_dead (.cons .nil)) rfl (.lam (.withI (.withI ?_ ?_) ?_))
  · exact d_fileObs 1 (fun a => .mut a bufT) (fun hΓ => .releaseMut (Ctx.Dead.toP hΓ))
  · exact d_fileObs 2 (fun a => .imm a bufT) (fun hΓ => .releaseImm (Ctx.Dead.toP hΓ))
  · exact .ret (appW (.var (by csolo)) (.free (Ctx.Dead.toP (by cdead))))

/-! ### The call inside the lend -/

/-- The lend's context: `'0 ⊏ ⊤`. -/
abbrev ΔL : LifeCtx := LifeCtx.empty.extend 0 LifeCtx.empty.meetOfDom

/-- `∀E` at the lend's `'0` leaves the rest `[⊤] U File^⊤`. -/
theorem fileTop_read_inst :
    ((CTy.arr (.mut (.var 1) bufT) (.ret (fileRest .top))).instT fileTopU).instLife 1 (.var 0)
      = .arr (.mut (.var 0) bufT) (.ret fileReadRes) := by
  decide

/-- `g s π₁ π₁ [] m`, with `m` the lent buffer, `s` the state and `g = unfold step`. -/
def fileCallE : Expr :=
  .app (.app (.app (.app (.app (.var 3) (.var 2)) (.val (.inj₁ .unit))) (.val (.inj₁ .unit)))
    (.val .unit)) (.var 0)

theorem d_fileCall {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives ΔL (⟨.mut (.var 0) bufT, true⟩ :: ⟨.unit, false⟩ :: ⟨fileS, true⟩ ::
        ⟨fileGenT, true⟩ :: Γ) fileCallE (.comp (.ret fileReadRes)) := by
  have hg : CDerives ΔL (⟨.mut (.var 0) bufT, false⟩ :: ⟨.unit, false⟩ :: ⟨fileS, false⟩ ::
      ⟨fileGenT, true⟩ :: Γ) (.var 3) (.comp (.arr fileS (.nu fileTopC))) :=
    .force (.there (.there (.there (.here (Ctx.Dead.toP hΓ)))))
  have hgs : CDerives ΔL (⟨.mut (.var 0) bufT, false⟩ :: ⟨.unit, false⟩ :: ⟨fileS, true⟩ ::
      ⟨fileGenT, true⟩ :: Γ) (.app (.var 3) (.var 2)) (.comp (.nu fileTopC)) :=
    .app (.dead (.dead (.right (.left (deadSplit hΓ))))) hg
      (.there (.there (.here (.cons (Ctx.Dead.toP hΓ)))))
  have hu := CDerives.nuOut fileTopC_nuOk hgs
  have hp := CDerives.allE (a := .var 0) (CDerives.proj₁ (CDerives.proj₁ hu))
    (fun _ hδ => hδ 0 _ rfl)
  rw [fileTop_read_inst] at hp
  exact .app (.right (.dead (.left (.left (deadSplit hΓ))))) hp
    (.here (.cons (.cons (.cons (Ctx.Dead.toP hΓ)))))

/-- The callback `Λ'0. λm. let r = g s π₁ π₁ [] m in [r]`. -/
def fileCb : Expr := .val (.lam (.val (.lam (bindE fileCallE (.var 0)))))

theorem d_fileCb {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty (⟨fileS, true⟩ :: ⟨fileGenT, true⟩ :: Γ) fileCb
      (.val (.all 0 LifeCtx.empty.meetOfDom (.lolli (.mut (.var 0) bufT) (.box (.var 0) fileReadRes)))) := by
  refine .thunkV rfl (.allI (S := .unit) rfl (fun _ _ h => by simp [LifeCtx.empty, LifeCtx.find?,
    Lifetime.assocFind] at h) (fun s hs hl => ?_) (.ret (.lamV ?_)))
  · simp only [List.mem_cons] at hs
    rcases hs with rfl | rfl | hs
    · simp [VFree]
    · simp [VFree, CFree, Lifetime.Life.mentions]
    · exact dead_noLive (P := fun s => ¬ VFree 0 s.ty) hΓ s hs hl
  · have hle : ΔL.EntailsLe (.var 0) .top := entailsLe_of_entailsLt (fun _ hδ => hδ 0 _ rfl)
    refine .eletV (.left (.dead (.left (.left (deadSplit hΓ))))) (.ofRet (d_fileCall hΓ))
      (.boxI (.var (.here (.cons (.cons (.cons (.cons (Ctx.Dead.toP hΓ)))))))
        ⟨LifeCtx.defines_of_wf rfl, fun s hs hl => ?_⟩)
    simp only [List.mem_cons] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | hs
    · exact .tensor .int (.box hle)
    all_goals first | simp at hl | exact dead_noLive (P := fun s => VOutlives ΔL (.var 0) s.ty) hΓ s hs hl

/-- `∀E` at the lend's `'0` leaves the rest `[⊤] U File^⊤`: `write`. -/
theorem fileTop_write_inst :
    ((CTy.arr (.imm (.var 1) bufT) (.ret (fileRest .top))).instT fileTopU).instLife 1 (.var 0)
      = .arr (.imm (.var 0) bufT) (.ret fileReadRes) := by
  decide

/-- `u π₁ π₂ [] b`, with `u = unbox rest` the object and `b` the lent buffer. -/
def fileWriteCallE : Expr :=
  .app (.app (.app (.app (.var 0) (.val (.inj₁ .unit))) (.val (.inj₂ .unit))) (.val .unit)) (.var 1)

theorem d_fileWriteCall {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives ΔL (⟨fileTopU, true⟩ :: ⟨.imm (.var 0) bufT, true⟩ :: Γ) fileWriteCallE
      (.comp (.ret fileReadRes)) := by
  have hf : CDerives ΔL (⟨fileTopU, true⟩ :: ⟨.imm (.var 0) bufT, false⟩ :: Γ) (.var 0)
      (.comp (.nu fileTopC)) :=
    .force (.here (.cons (Ctx.Dead.toP hΓ)))
  have hu := CDerives.nuOut fileTopC_nuOk hf
  have hp := CDerives.allE (a := .var 0) (CDerives.proj₂ (CDerives.proj₁ hu))
    (fun _ hδ => hδ 0 _ rfl)
  rw [fileTop_write_inst] at hp
  exact .app (.left (.right (deadSplit hΓ))) hp (.there (.here (Ctx.Dead.toP hΓ)))

/-- The second callback `Λ'0. λb. let r = (let u = rest in u π₁ π₂ [] b) in [r]`, the rest
`rest : [⊤] U File^⊤` captured. -/
def fileCb₂ : Expr := .val (.lam (.val (.lam (bindE (bindE (.var 2) fileWriteCallE) (.var 0)))))

theorem d_fileCb₂ {Γ : Ctx VTy} (hΓ : Ctx.Dead Γ) :
    CDerives LifeCtx.empty (⟨.box .top fileTopU, true⟩ :: Γ) fileCb₂
      (.val (.all 0 LifeCtx.empty.meetOfDom (.lolli (.imm (.var 0) bufT) (.box (.var 0) fileReadRes)))) := by
  refine .thunkV rfl (.allI (S := .unit) rfl (fun _ _ h => by simp [LifeCtx.empty, LifeCtx.find?,
    Lifetime.assocFind] at h) (fun s hs hl => ?_) (.ret (.lamV ?_)))
  · simp only [List.mem_cons] at hs
    rcases hs with rfl | hs
    · simp [VFree, CFree, Lifetime.Life.mentions]
    · exact dead_noLive (P := fun s => ¬ VFree 0 s.ty) hΓ s hs hl
  · have hle : ΔL.EntailsLe (.var 0) .top := entailsLe_of_entailsLt (fun _ hδ => hδ 0 _ rfl)
    refine .eletV (.left (.dead (.left (deadSplit hΓ))))
      (.eletV (.right (.dead (.left (deadSplit hΓ)))) (.boxE (.var (.there (.there (.here
        (Ctx.Dead.toP hΓ)))))) (.ofRet (d_fileWriteCall (.cons (.cons hΓ)))))
      (.boxI (.var (.here (.cons (.cons (.cons (Ctx.Dead.toP hΓ))))))
        ⟨LifeCtx.defines_of_wf rfl, fun s hs hl => ?_⟩)
    simp only [List.mem_cons] at hs
    rcases hs with rfl | rfl | rfl | rfl | hs
    · exact .tensor .int (.box hle)
    all_goals first | simp at hl | exact dead_noLive (P := fun s => VOutlives ΔL (.var 0) s.ty) hΓ s hs hl

/-! ### The program -/

/-- After the first lend, at `r` index 0 and `b'` index 1: `let (n, rest) = r;
let (b'', r₂) = withbor b' (Λ. λi. [unbox rest π₁ π₂ [] i]); let (n₂, rest₂) = r₂;
let k = (unbox rest₂) π₂; let v = free b''; K`. -/
def fileAfter (K : Expr) : Expr :=
  .letpair (.var 0)
    (.letpair (app2 withbor (.var 3) fileCb₂)
      (.letpair (.var 0)
        (bindE (bindE (.var 0) (.app (.var 0) (.val (.inj₂ .unit))))
          (bindE (.app free' (.var 4)) K))))

/-- The program, its tail `K` under `v, k, rest₂, n₂, r₂, b'', rest, n, r, b', s, g, b`. -/
def fileReadWith (K : Expr) : Expr :=
  bindE (.app alloc' (i32E 7))
    (bindE (.app (.val (unfoldV fileTopC)) (.val fileStep))
      (bindE (.app alloc' (i32E 5))
        (.letpair (app2 withbor (.var 2) fileCb) (fileAfter K))))

/-- **`fileRead`**: the buffer lent `mut` to the object's `read`, the rest leaving the lend. -/
def fileReadProg : Expr := fileReadWith unit'

/-- The variant that answers `(n, (n₂, (k, v)))`. -/
def fileReadOut : Expr :=
  fileReadWith (.pair (.var 7) (.pair (.var 3) (.pair (.var 1) (.var 0))))

theorem d_fileReadWith {K : Expr} {A : VTy}
    (hK : CDerives LifeCtx.empty
      [⟨.i32, true⟩, ⟨.i32, true⟩, ⟨.box .top fileTopU, false⟩, ⟨.i32, true⟩,
        ⟨fileReadRes, false⟩, ⟨fileS, false⟩, ⟨.box .top fileTopU, false⟩, ⟨.i32, true⟩,
        ⟨fileReadRes, false⟩, ⟨fileS, false⟩, ⟨fileS, false⟩, ⟨fileGenT, false⟩, ⟨fileS, false⟩]
      K (.val A)) :
    CDerives LifeCtx.empty [] (fileReadWith K) (.val A) := by
  refine bindP (A := fileS) (appP (d_i32 7 (by cdeadP)) (.alloc (by cdeadP))) ?_
  refine bindP (A := fileGenT)
    (.bangE (appP d_fileStep (.unfoldN fileTopC fileS fileTopC_nuOk fileTopC_bindsFresh
      (by cdeadP)))) ?_
  refine bindP (A := fileS) (appP (d_i32 5 (by cdeadP)) (.alloc (by cdeadP))) ?_
  refine letP (A := fileS) (B := fileReadRes) (appP (d_fileCb (.cons .nil)) (appP (.var (by csoloP))
    (.withbor2 (A := bufT) (B := fileReadRes) 0 (by cdeadP) rfl
      ⟨.top, LifeCtx.defines_of_wf rfl, .int⟩ (by simp [VFree])
      (by simp [VFree, CFree, Lifetime.Life.mentions])))) ?_
  refine letP (A := .i32) (B := .box .top fileTopU) (.var (by csoloP)) ?_
  refine letP (A := fileS) (B := fileReadRes) (appW (d_fileCb₂ (by cdead)) (appP (.var (by csoloP))
    (.withbor1 (A := bufT) (B := fileReadRes) 0 (by cdeadP) rfl
      (fun _ h => by simp [VFree] at h) (by simp [VFree])
      (by simp [VFree, CFree, Lifetime.Life.mentions])))) ?_
  refine letP (A := .i32) (B := .box .top fileTopU) (.var (by csoloP)) ?_
  refine bindP (A := .i32) (bindP (A := fileTopU) (.boxE (.var (by csoloP)))
    (.ofRet (.proj₂ (.nuOut fileTopC_nuOk (.force (C := .nu fileTopC) (by csoloP)))))) ?_
  refine bindP (A := .i32) (appP (.var (by csoloP)) (.free (by cdeadP))) ?_
  exact hK

theorem d_fileReadProg : CDerives LifeCtx.empty [] fileReadProg (.val .unit) :=
  d_fileReadWith (.unitI (by cdeadP))

/-- **`fileRead` runs at every host**: from the empty memory to `()` and the empty memory. -/
theorem fileReadProg_runs :
    BoCa.BoLo.Steps Adequacy.emptyMem fileReadProg Adequacy.emptyMem (.val .unit) :=
  adequacyC (.ret d_fileReadProg)

set_option maxRecDepth 100000 in
/-- The interpreter at Wasm's host: `()`, no cell left. -/
theorem fileReadProg_eval : BoCa.Programs.unitNoLeak (eval fileReadProg) = true := by decide

/-- The answers `(n, (n₂, (k, v)))` of a run with no cell left. -/
def quadNoLeak : Outcome → Option (UInt32 × UInt32 × UInt32 × UInt32)
  | .value v false =>
    match v.1 with
    | .pair a (.pair b (.pair c d)) => do pure (← i32Of a, ← i32Of b, ← i32Of c, ← i32Of d)
    | _ => none
  | _ => none

theorem d_fileReadOut :
    CDerives LifeCtx.empty [] fileReadOut (.val (.tensor .i32 (.tensor .i32 (.tensor .i32 .i32)))) :=
  d_fileReadWith (pairP (.var (by csoloP)) (pairP (.var (by csoloP))
    (pairP (.var (by csoloP)) (.var (by csoloP)))))

set_option maxRecDepth 100000 in
/-- The interpreter at Wasm's host: `read`'s `1`, `write`'s `2`, the state's `5` that `close`
frees, and the buffer's `7`, given back by both lends and freed; no cell left. -/
theorem fileReadOut_eval : quadNoLeak (eval fileReadOut) = some (1, 2, 5, 7) := by decide

end BoCa.Fig16.LogRel.Core

end
