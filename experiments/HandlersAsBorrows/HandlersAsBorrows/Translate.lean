import HandlersAsBorrows.Combinators

/-!
# The translation, and typing preservation (theorem (a))

`tr s` is the BoLo term of a statement `s`, open in the threaded environment (de Bruijn `0`)
and the value context.  Under `K; Γ ⊢ s : C` it has type `C ⊗ EnvTy n K`
(`translate_typed`).  The clauses:

    ⟦e⟧                  = (⟦e⟧ᵥ, env)
    ⟦val x = s₀; s₁⟧     = let (x, env) = ⟦s₀⟧; ⟦s₁⟧
    ⟦e; s⟧               = ⟦e⟧ᵥ; ⟦s⟧
    ⟦let (x, y) = e; s⟧  = let (x, y) = ⟦e⟧ᵥ; (λenv. ⟦s⟧) env
    ⟦case e {x ⇒ s₁ | y ⇒ s₂}⟧ = case ⟦e⟧ᵥ {x ⇒ (λenv. ⟦s₁⟧) env | y ⇒ (λenv. ⟦s₂⟧) env}
    ⟦F_j(e)⟧             = opAt j (⟦e⟧ᵥ, env)
    ⟦f_j(e)⟧             = blockAt j (⟦e⟧ᵥ, env)
    ⟦def f = {x ⇒ b}; s⟧ = let (y, env′) = (λenv′. ⟦s⟧) (!λp. let (x, env) = p; ⟦b⟧, env);
                           let (f, env) = env′; forget f; (y, env)
    ⟦handle_S {F ⇒ s} with e₀, cl⟧ =
        let (c, r) = withbor (alloc ⟦e₀⟧ᵥ) (Λ. λm.
                       let (y, env′) = (λenv′. ⟦s⟧) ((m, clause), env);
                       let (ent, env) = env′; let (m, cl) = ent; forget m; forget cl; □(y, env));
        dropS (free c); r

`handle` is `withbor` form (2) ([TR] p. 3, row 2.45): the handler's state is allocated, lent
as `Mut 'x S` at a fresh `'x ⊏ ⊓Δ`, and taken back and freed when the handled statement returns.
The result `□(y, env)` is `[]I` (row 2.13) at `'x`: the value `y` and the outer environment
outlive `'x`; the capability `m : Mut 'x S` does not, and it is forgotten first.

`[about ours]`
-/

noncomputable section

namespace HandlersAsBorrows.Xi
open BoCa BoCa.Lifetime BoCa.Programs

/-! ## Contexts -/

/-- The value context, at its BoLo types. -/
def emb (Γ : Ctx VTy) : Ctx Ty := Γ.map fun s => ⟨s.ty.tr, s.live⟩

/-- Every slot consumed. -/
def kill (Γ : Ctx Ty) : Ctx Ty := Γ.map fun s => ⟨s.ty, false⟩

theorem emb_split {Γ Γ₁ Γ₂ : Ctx VTy} (h : Ctx.Split Γ Γ₁ Γ₂) :
    Ctx.Split (emb Γ) (emb Γ₁) (emb Γ₂) := by
  induction h with
  | nil => exact .nil
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | dead _ ih => exact .dead ih

theorem emb_dead {Γ : Ctx VTy} (h : Ctx.Dead Γ) : Ctx.Dead (emb Γ) := by
  induction h with
  | nil => exact .nil
  | cons _ ih => exact .cons ih

theorem emb_solo {Γ : Ctx VTy} {i : Nat} {A : VTy} (h : Ctx.Solo Γ i A) :
    Ctx.Solo (emb Γ) i A.tr := by
  induction h with
  | here hd => exact .here (emb_dead hd)
  | there _ ih => exact .there ih

theorem dead_kill : ∀ Γ : Ctx Ty, Ctx.Dead (kill Γ)
  | [] => .nil
  | _ :: Γ => .cons (dead_kill Γ)

theorem split_kill : ∀ Γ : Ctx Ty, Ctx.Split Γ Γ (kill Γ)
  | [] => .nil
  | ⟨_, true⟩ :: Γ => .left (split_kill Γ)
  | ⟨_, false⟩ :: Γ => .dead (split_kill Γ)

theorem split_kill' : ∀ Γ : Ctx Ty, Ctx.Split Γ (kill Γ) Γ
  | [] => .nil
  | ⟨_, true⟩ :: Γ => .right (split_kill' Γ)
  | ⟨_, false⟩ :: Γ => .dead (split_kill' Γ)

theorem split_symm {τ : Type} {Γ Γ₁ Γ₂ : Ctx τ} (h : Ctx.Split Γ Γ₁ Γ₂) : Ctx.Split Γ Γ₂ Γ₁ := by
  induction h with
  | nil => exact .nil
  | left _ ih => exact .right ih
  | right _ ih => exact .left ih
  | dead _ ih => exact .dead ih

theorem emb_noBinds (Γ : Ctx VTy) (x : LifeVar) :
    ∀ s ∈ emb Γ, s.live = true → s.ty.bindsB x = false := by
  intro s hs _
  simp only [emb, List.mem_map] at hs
  obtain ⟨t, _, rfl⟩ := hs
  exact VTy.noBinds _ _

theorem Ctx.Outlives.consD {Δ : LifeCtx} {Γ : Ctx Ty} {a : Life} {T : Ty}
    (h : Ctx.Outlives Δ Γ a) : Ctx.Outlives Δ (⟨T, false⟩ :: Γ) a := by
  refine ⟨h.1, fun s hs hl => ?_⟩
  rcases List.mem_cons.mp hs with rfl | hs'
  · exact absurd hl (by simp)
  · exact h.2 s hs' hl

theorem Ctx.Outlives.consL {Δ : LifeCtx} {Γ : Ctx Ty} {a : Life} {T : Ty}
    (hT : OutlivesRules Δ a T) (h : Ctx.Outlives Δ Γ a) : Ctx.Outlives Δ (⟨T, true⟩ :: Γ) a := by
  refine ⟨h.1, fun s hs hl => ?_⟩
  rcases List.mem_cons.mp hs with rfl | hs'
  · exact hT
  · exact h.2 s hs' hl

/-! ## Values and data -/

/-- `⟦e⟧ᵥ`: indices shift past the environment slot. -/
def trV : VExp → Expr
  | .var i => .var (i + 1)
  | .unit => unit'
  | .pair e₁ e₂ => .pair (trV e₁) (trV e₂)
  | .inj₁ e => .inj₁ (trV e)
  | .inj₂ e => .inj₂ (trV e)

theorem d_trV {Δ : LifeCtx} {Γ : Ctx VTy} {e : VExp} {A : VTy} (h : VDerives Γ e A) (U : Ty) :
    DerivesWf Δ (⟨U, false⟩ :: emb Γ) (trV e) A.tr := by
  induction h with
  | var hs => exact .var (.there (emb_solo hs))
  | unit hd => exact .unitI (.cons (emb_dead hd))
  | pair hs _ _ ih₁ ih₂ => exact .tensorI (.dead (emb_split hs)) ih₁ ih₂
  | inj₁ _ ih => exact .sumI₁ ih
  | inj₂ _ ih => exact .sumI₂ ih

/-- `dropS : S ⊸ 1`, consuming data. -/
def dropD : VTy → Expr
  | .unit => lam (.var 0)
  | .pair A B => lam (.letpair (.var 0) (.seq (.app (dropD A) (.var 1)) (.app (dropD B) (.var 0))))
  | .sum A B => lam (.case (.var 0) (.app (dropD A) (.var 0)) (.app (dropD B) (.var 0)))

theorem d_dropD {Δ : LifeCtx} : ∀ (A : VTy) {Γ : Ctx Ty}, Ctx.Dead Γ →
    DerivesWf Δ Γ (dropD A) (.lolli A.tr .unit)
  | .unit, Γ, hd => .lolliI rfl (.var (.here hd))
  | .pair A B, Γ, hd =>
      .lolliI (by simp [VTy.tr, Ty.scopedB])
        (.tensorE (T₁ := A.tr) (T₂ := B.tr) (.left hd.split) (by simp [Ty.scopedB])
          (.var (.here hd))
          (.unitE (.right (.left (.dead hd.split)))
            (.lolliE (.dead (.left (.dead hd.split))) (.var (.there (.here (.cons hd))))
              (d_dropD A (.cons (.cons (.cons hd)))))
            (.lolliE (.left (.dead (.dead hd.split))) (.var (.here (.cons (.cons hd))))
              (d_dropD B (.cons (.cons (.cons hd)))))))
  | .sum A B, Γ, hd =>
      .lolliI (by simp [VTy.tr, Ty.scopedB])
        (.sumE (T₁ := A.tr) (T₂ := B.tr) (.left hd.split) (by simp [Ty.scopedB]) (.var (.here hd))
          (.lolliE (.left (.dead hd.split)) (.var (.here (.cons hd))) (d_dropD A (.cons (.cons hd))))
          (.lolliE (.left (.dead hd.split)) (.var (.here (.cons hd))) (d_dropD B (.cons (.cons hd)))))

/-! ## Statements -/

/-- A block's code: `!λp. let (x, env) = p; ⟦body⟧`. -/
def blockCode (b : Expr) : Expr := lam (.letpair (.var 0) b)

/-- A clause's code: `!λp. let (r, u) = (λenv. ⟦cl⟧) (); u; r`, the clause run at the empty
environment. -/
def clauseCode (c : Expr) : Expr := lam (.letpair (.app (lam c) unit') (.seq (.var 0) (.var 1)))

/-- After the handled statement: drop the capability, return the value and the outer
environment. -/
def handleFin : Expr :=
  .letpair (.var 0) (.letpair (.var 1)
    (.seq (.app forget (.var 1)) (.seq (.app forget (.var 0)) (.pair (.var 5) (.var 2)))))

/-- The body of the borrow callback `Λ. λm. …`. -/
def handleBody (code t : Expr) : Expr :=
  .letpair (.app (lam t) (.pair (.pair (.var 0) code) (.var 2))) handleFin

/-- After the scope of a block: drop its code, return the value and the outer environment. -/
def defnFin : Expr :=
  .letpair (.var 0) (.seq (.app forget (.var 1)) (.pair (.var 3) (.var 0)))

def tr : Stmt → Expr
  | .ret e => .pair (trV e) (.var 0)
  | .val s₀ s₁ => .letpair (tr s₀) (tr s₁)
  | .drop e s => .seq (trV e) (tr s)
  | .split e s => .letpair (trV e) (.app (lam (tr s)) (.var 2))
  | .case e s₁ s₂ => .case (trV e) (.app (lam (tr s₁)) (.var 1)) (.app (lam (tr s₂)) (.var 1))
  | .op j e => .app (opAt j) (.pair (trV e) (.var 0))
  | .call j e => .app (blockAt j) (.pair (trV e) (.var 0))
  | .defn b s => .letpair (.app (lam (tr s)) (.pair (blockCode (tr b)) (.var 0))) defnFin
  | .handle S e₀ cl s =>
      .letpair (app2 withbor (.app alloc' (trV e₀)) (lam (lam (handleBody (clauseCode (tr cl)) (tr s)))))
        (.seq (.app (dropD S) (.app free' (.var 1))) (.var 0))

/-- **Theorem (a): the translation preserves typing.**  A statement typed in the fragment
translates to a BoLo + `!` derivation (`DerivesWf`, [TR] p. 2 with SPEC §2's `!` rules) at
`C ⊗ EnvTy n K`, in the context of the threaded environment and the value context, at every
lifetime context `Δ` that binds the handlers' lifetimes (`Good`). -/
theorem translate_typed {K : List Entry} {Γ : Ctx VTy} {s : Stmt} {C : VTy}
    (h : XDerives K Γ s C) : ∀ (n : Nat) (Δ : LifeCtx), Good n K Δ →
      DerivesWf Δ (⟨EnvTy n K, true⟩ :: emb Γ) (tr s) (.tensor C.tr (EnvTy n K)) := by
  induction h with
  | ret hv =>
      intro n Δ hG
      exact .tensorI (.right (split_kill _)) (d_trV hv _) (.var (.here (dead_kill _)))
  | @val K Γ Γ₁ Γ₂ s₀ s₁ A B hs _ _ ih₀ ih₁ =>
      intro n Δ hG
      exact .tensorE (T₁ := A.tr) (T₂ := EnvTy n K) (.left (emb_split hs))
        (by simp [Ty.scopedB, hG.scoped]) (ih₀ n Δ hG)
        ((ih₁ n Δ hG).dwk (.live (.live (.dead (DWk.refl _)))))
  | drop hs hv _ ih =>
      intro n Δ hG
      exact .unitE (.right (emb_split hs)) (d_trV hv _) (ih n Δ hG)
  | @split K Γ Γ₁ Γ₂ e s A₁ A₂ B hs hv _ ih =>
      intro n Δ hG
      exact .tensorE (T₁ := A₁.tr) (T₂ := A₂.tr) (.right (emb_split hs))
        (by simp [Ty.scopedB]) (d_trV hv _)
        (.lolliE (T₁ := EnvTy n K) (.right (.right (.left (split_kill' _))))
          (.var (.there (.there (.here (dead_kill _)))))
          (.lolliI hG.scoped ((ih n Δ hG).dwk (.live (.live (.live (.dead (DWk.refl _))))))))
  | @case K Γ Γ₁ Γ₂ e s₁ s₂ A₁ A₂ B hs hv _ _ ih₁ ih₂ =>
      intro n Δ hG
      exact .sumE (T₁ := A₁.tr) (T₂ := A₂.tr) (.right (emb_split hs)) (by simp [Ty.scopedB])
        (d_trV hv _)
        (.lolliE (T₁ := EnvTy n K) (.right (.left (split_kill' _)))
          (.var (.there (.here (dead_kill _))))
          (.lolliI hG.scoped ((ih₁ n Δ hG).dwk (.live (.live (.dead (DWk.refl _)))))))
        (.lolliE (T₁ := EnvTy n K) (.right (.left (split_kill' _)))
          (.var (.there (.here (dead_kill _))))
          (.lolliI hG.scoped ((ih₂ n Δ hG).dwk (.live (.live (.dead (DWk.refl _)))))))
  | @op K Γ j e S A B hj hv =>
      intro n Δ hG
      exact .lolliE (split_kill _)
        (.tensorI (.right (split_kill _)) (d_trV hv _) (.var (.here (dead_kill _))))
        (d_opAt K j hj hG.scoped (dead_kill _))
  | @call K Γ j e A B hj hv =>
      intro n Δ hG
      exact .lolliE (split_kill _)
        (.tensorI (.right (split_kill _)) (d_trV hv _) (.var (.here (dead_kill _))))
        (d_blockAt K j hj hG.scoped (dead_kill _))
  | @defn K Γ body s A B C _ _ ihb ihs =>
      intro n Δ hG
      have hE := hG.scoped
      have hcode : ∀ {D : Ctx Ty}, Ctx.Dead D → DerivesWf Δ D (blockCode (tr body))
          (.bang (.lolli (.tensor A.tr (EnvTy n K)) (.tensor B.tr (EnvTy n K)))) := by
        intro D hD
        exact .bangLamI hD.persistent (by simp [Ty.scopedB, hE])
          (.tensorE (T₁ := A.tr) (T₂ := EnvTy n K) (.left hD.split) (by simp [Ty.scopedB, hE])
            (.var (.here hD)) ((ihb n Δ hG).dwk (.live (.live (.dead (.nil hD))))))
      have hK := dead_kill (⟨EnvTy n K, true⟩ :: emb Γ)
      refine .tensorE (T₁ := C.tr) (T₂ := EnvTy n (.blk A B :: K)) (split_kill _)
        (by simp [Ty.scopedB, (hG.blk A B).scoped]) ?_ ?_
      · exact .lolliE (T₁ := EnvTy n (.blk A B :: K)) (.left (split_kill' _))
          (.tensorI (.right (dead_kill _).split) (hcode (.cons (dead_kill _)))
            (.var (.here (dead_kill _))))
          (.lolliI (hG.blk A B).scoped ((ihs n Δ (hG.blk A B)).dwk (.live (.dead (DWk.refl _)))))
      · refine .tensorE (T₁ := .bang (.lolli (.tensor A.tr (EnvTy n K)) (.tensor B.tr (EnvTy n K))))
          (T₂ := EnvTy n K) (.left (.right hK.split)) (by simp [Ty.scopedB, hE])
          (.var (.here (.cons hK))) ?_
        exact .unitE (.right (.left (.dead (.right hK.split))))
          (.lolliE (.dead (.left (.dead (.dead hK.split)))) (.var (.there (.here (.cons (.cons hK)))))
            (.forgetBangAx (.cons (.cons (.cons (.cons hK))))))
          (.tensorI (.right (.dead (.dead (.left hK.split))))
            (.var (.there (.there (.there (.here hK))))) (.var (.here (.cons (.cons (.cons hK))))))
  | @handle K Γ Γ₁ Γ₂ e₀ cl s S A B C hs hv _ _ ihcl ihs =>
      intro n Δ hG
      -- the handler's lifetime, its context, and the environment inside it
      have hE := hG.scoped
      have hx : Δ.find? (n + ncaps K) = none := hG.fresh _ (Nat.le_refl _)
      have hG' := hG.handle S A B
      have hE' := hG'.scoped
      have hxwf : (Life.var (n + ncaps K)).wf (hΔ n K Δ) = true := by
        simp [Life.wf, LifeCtx.find?_extend]
      have hEext : (EnvTy n K).scopedB (hΔ n K Δ) = true :=
        Ty.scopedB_extend (EnvTy.noBinds n _ K) hE
      have hdef : (hΔ n K Δ).Defines (.var (n + ncaps K)) := LifeCtx.defines_of_wf hxwf
      -- the clause, as `!` code in any consumed context
      have hcode : ∀ {D : Ctx Ty}, Ctx.Dead D →
          DerivesWf (hΔ n K Δ) D (clauseCode (tr cl)) (codeTy S A B) := by
        intro D hD
        exact .bangLamI hD.persistent (by simp [Ty.scopedB])
          (.tensorE (T₁ := (VTy.pair S B).tr) (T₂ := .unit) (.left hD.split)
            (by simp [Ty.scopedB])
            (.lolliE (.right hD.split) (.unitI (.cons hD))
              (.lolliI rfl ((ihcl (n + ncaps K + 1) (hΔ n K Δ) hG.clause).dwk
                (.live (.live (.nil hD))))))
            (.unitE (.left (.right (.dead hD.split))) (.var (.here (.cons (.cons hD))))
              (.var (.there (.here (.cons hD))))))
      -- after the handled statement
      have hfin : ∀ {K' : Ctx Ty}, Ctx.Dead K' →
          DerivesWf (hΔ n K Δ) (⟨EnvTy n (.cap S A B :: K), true⟩ :: ⟨C.tr, true⟩ :: K') handleFin
            (.box (.var (n + ncaps K)) (.tensor C.tr (EnvTy n K))) := by
        intro K' hK
        refine .tensorE (T₁ := .tensor (.mut (.var (n + ncaps K)) S.tr) (codeTy S A B))
          (T₂ := EnvTy n K) (.left (.right hK.split)) (by simp [Ty.scopedB, hxwf, hEext])
          (.var (.here (.cons hK))) ?_
        refine .tensorE (T₁ := .mut (.var (n + ncaps K)) S.tr) (T₂ := codeTy S A B)
          (.right (.left (.dead (.right hK.split)))) (by simp [Ty.scopedB, hxwf])
          (.var (.there (.here (.cons (.cons hK))))) ?_
        refine .unitE (.right (.left (.right (.dead (.dead (.right hK.split))))))
          (.lolliE (.dead (.left (.dead (.dead (.dead (.dead hK.split))))))
            (.var (.there (.here (.cons (.cons (.cons (.cons hK)))))))
            (.forgetMutAx (.cons (.cons (.cons (.cons (.cons (.cons hK)))))))) ?_
        refine .unitE (.left (.dead (.right (.dead (.dead (.right hK.split))))))
          (.lolliE (.left (.dead (.dead (.dead (.dead (.dead hK.split))))))
            (.var (.here (.cons (.cons (.cons (.cons (.cons hK)))))))
            (.forgetBangAx (.cons (.cons (.cons (.cons (.cons (.cons hK)))))))) ?_
        refine .boxIctx
          (.tensorI (.dead (.dead (.right (.dead (.dead (.left hK.split))))))
            (.var (.there (.there (.there (.there (.there (.here hK)))))))
            (.var (.there (.there (.here (.cons (.cons (.cons hK))))))))
          ?_
        exact Ctx.Outlives.consD (Ctx.Outlives.consD (Ctx.Outlives.consL hG.outlives
          (Ctx.Outlives.consD (Ctx.Outlives.consD (Ctx.Outlives.consL (VTy.outlives _ _ _)
            (Ctx.Dead.outlives hdef hK))))))
      -- the borrow callback's body
      have hbody : DerivesWf (hΔ n K Δ)
          (⟨.mut (.var (n + ncaps K)) S.tr, true⟩ :: ⟨.unit, false⟩ :: ⟨EnvTy n K, true⟩ :: emb Γ₂)
          (handleBody (clauseCode (tr cl)) (tr s))
          (.box (.var (n + ncaps K)) (.tensor C.tr (EnvTy n K))) := by
        have hK := dead_kill (emb Γ₂)
        refine .tensorE (T₁ := C.tr) (T₂ := EnvTy n (.cap S A B :: K)) (split_kill _)
          (by simp [Ty.scopedB, hE']) ?_ (hfin (dead_kill _))
        refine .lolliE (T₁ := EnvTy n (.cap S A B :: K)) (.left (.dead (.left (split_kill' _))))
          ?_ (.lolliI hE' ((ihs n (hΔ n K Δ) hG').dwk (.live (.dead (.dead (.dead (DWk.refl _)))))))
        exact .tensorI (.left (.dead (.right hK.split)))
          (.tensorI (.left (.dead (.dead hK.split))) (.var (.here (.cons (.cons hK))))
            (hcode (.cons (.cons (.cons hK)))))
          (.var (.there (.there (.here hK))))
      -- the whole: `withbor` form (2), then free and drop the final state
      have hX := dead_kill (⟨EnvTy n K, true⟩ :: emb Γ)
      refine .tensorE (T₁ := .ref S.tr) (T₂ := .tensor C.tr (EnvTy n K)) (split_kill _)
        (by simp [Ty.scopedB, hE]) ?_ ?_
      · refine .lolliE (.left (split_symm (emb_split hs)))
          (.allI (S := .unit) hx (meetOfDomL_wf _) ?_ (.lolliI (by simp only [Ty.scopedB, VTy.scoped, Bool.and_true]; exact hxwf) hbody)) ?_
        · intro sl hsl hl
          rcases List.mem_cons.mp hsl with rfl | hsl'
          · exact EnvTy.noBinds n _ K
          · exact emb_noBinds Γ₂ _ sl hsl' hl
        · refine .lolliE (split_kill _)
            (.lolliE (split_kill _) (d_trV hv _) (.allocAx (dead_kill _)))
            (.withbor2Ax (dead_kill _) (n + ncaps K) hx
              ⟨.top, LifeCtx.defines_of_wf rfl, VTy.outlives _ _ _⟩ ?_)
          have hmw : Δ.meetOfDom.wf Δ = true := meetOfDomL_wf _
          simp only [axWithbor2Ty, Ty.scopedB, hx, hmw, hxwf, hEext, hE, VTy.scoped, Option.isNone_none,
            Bool.and_self]
      · exact .unitE (.right (.left hX.split))
          (.lolliE (.dead (.left hX.split))
            (.lolliE (.dead (.left hX.split)) (.var (.there (.here hX))) (.freeAx (.cons (.cons hX))))
            (d_dropD S (.cons (.cons hX))))
          (.var (.here (.cons hX)))

end HandlersAsBorrows.Xi
