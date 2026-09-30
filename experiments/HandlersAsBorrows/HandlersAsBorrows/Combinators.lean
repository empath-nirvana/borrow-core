import HandlersAsBorrows.Env

/-!
# Closed combinators: operation calls and block calls on the threaded environment

* `opHere : A ⊗ ((Mut 'x S ⊗ !code) ⊗ E) ⊸ B ⊗ ((Mut 'x S ⊗ !code) ⊗ E)` performs the
  operation of the capability at the head of the environment:

      λp. let (a, env) = p; let (ent, et) = env; let (m, c) = ent; let (c₁, c₂) = copy c;
          let (m′, b) = withswap m (λs. c₁ (s, a)); (b, ((m′, c₂), et))

  `withswap` ([TR] p. 3, row 2.48) hands the borrowed state to the clause and stores what the
  clause returns: the clause resumes exactly once, in tail position.
* `blockHere` calls the block at the head on the environment of its definition.
* `atSucc h` runs `h` one entry deeper, leaving the head untouched: lexical scoping, since a
  block or capability sees only the environment it was defined in.

Each is closed, and typed in every consumed context.

`[about ours]`
-/

noncomputable section

namespace HandlersAsBorrows.Xi
open BoCa BoCa.Lifetime BoCa.Programs

def opHere : Expr :=
  lam (.letpair (.var 0) (.letpair (.var 0) (.letpair (.var 1) (.letpair (.app copy (.var 0))
    (.letpair (app2 withswap (.var 3) (lam (.app (.var 2) (.pair (.var 0) (.var 8)))))
      (.pair (.var 0) (.pair (.pair (.var 1) (.var 2)) (.var 6))))))))

def blockHere : Expr :=
  lam (.letpair (.var 0) (.letpair (.var 0) (.letpair (.app copy (.var 1))
    (.letpair (.app (.var 1) (.pair (.var 5) (.var 2)))
      (.pair (.var 1) (.pair (.var 2) (.var 0)))))))

def atSucc (h : Expr) : Expr :=
  lam (.letpair (.var 0) (.letpair (.var 0)
    (.letpair (.app h (.pair (.var 3) (.var 0))) (.pair (.var 1) (.pair (.var 3) (.var 0))))))

/-- `h` at environment index `j`. -/
def atIdx (h : Expr) : Nat → Expr
  | 0 => h
  | j + 1 => atSucc (atIdx h j)

/-- `F_j(e)`. -/
abbrev opAt (j : Nat) : Expr := atIdx opHere j

/-- `f_j(e)`. -/
abbrev blockAt (j : Nat) : Expr := atIdx blockHere j

variable {Δ : LifeCtx}

/-- The operation at the head. -/
theorem d_opHere {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) (a : Life) (S A B : VTy) (Et : Ty)
    (hE : Et.scopedB Δ = true) (ha : a.wf Δ = true) :
    DerivesWf Δ Γ opHere
      (.lolli (.tensor A.tr (.tensor (.tensor (.mut a S.tr) (codeTy S A B)) Et))
        (.tensor B.tr (.tensor (.tensor (.mut a S.tr) (codeTy S A B)) Et))) := by
  have hd := hΓ
  refine .lolliI (by simp [Ty.scopedB, hE, ha]) ?_
  refine .tensorE (T₁ := A.tr) (T₂ := .tensor (.tensor (.mut a S.tr) (codeTy S A B)) Et)
    (.left hd.split) (by simp [Ty.scopedB, hE, ha]) (.var (.here hd)) ?_
  refine .tensorE (T₁ := .tensor (.mut a S.tr) (codeTy S A B)) (T₂ := Et)
    (.left (.right (.dead hd.split))) (by simp [Ty.scopedB, hE, ha]) (.var (.here (.cons (.cons hd)))) ?_
  refine .tensorE (T₁ := .mut a S.tr) (T₂ := codeTy S A B)
    (.right (.left (.dead (.right (.dead hd.split))))) (by simp [Ty.scopedB, ha])
    (.var (.there (.here (.cons (.cons (.cons hd)))))) ?_
  refine .tensorE (T₁ := codeTy S A B) (T₂ := codeTy S A B)
    (.left (.right (.right (.dead (.dead (.right (.dead hd.split)))))))
    (by simp [Ty.scopedB])
    (.lolliE (.left (.dead (.dead (.dead (.dead (.dead (.dead hd.split)))))))
      (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons hd))))))))
      (.copyBangAx (.cons (.cons (.cons (.cons (.cons (.cons (.cons hd))))))))) ?_
  -- ctx: c₂ 0, c₁ 1, c 2, m 3, et 4, ent 5, env 6, a 7, p 8
  refine .tensorE (T₁ := .mut a S.tr) (T₂ := B.tr)
    (.right (.left (.dead (.left (.right (.dead (.dead (.left (.dead hd.split)))))))))
    (by simp [Ty.scopedB, ha]) ?_ ?_
  · -- withswap m (λs. c₁ (s, a))
    refine .lolliE (T₁ := .lolli S.tr (.tensor S.tr B.tr)) (.dead (.left (.dead (.right (.dead (.dead (.dead (.left (.dead hd.split)))))))))
      ?_ ?_
    · refine .lolliI (by simp) ?_
      refine .lolliE (T₁ := .tensor S.tr A.tr) (.left (.dead (.right (.dead (.dead (.dead (.dead (.dead (.left (.dead hd.split))))))))))
        (.tensorI (.left (.dead (.dead (.dead (.dead (.dead (.dead (.dead (.right (.dead hd.split))))))))))
          (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons hd)))))))))))
          (.var (.there (.there (.there (.there (.there (.there (.there (.there
            (.here (.cons hd)))))))))))) ?_
      exact .bangE (.var (.there (.there (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons hd)))))))))))
    · refine .lolliE (.dead (.dead (.dead (.left (.dead (.dead (.dead (.dead (.dead hd.split)))))))))
        (.var (.there (.there (.there (.here (.cons (.cons (.cons (.cons (.cons hd))))))))))
        (.withswapAx (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons hd))))))))))
  · -- ctx: b 0, m′ 1, c₂ 2, c₁ 3, c 4, m 5, et 6, ent 7, env 8, a 9, p 10
    refine .tensorI (.left (.right (.right (.dead (.dead (.dead (.right (.dead (.dead (.dead (.dead hd.split)))))))))))
      (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons hd)))))))))))) ?_
    refine .tensorI (.dead (.left (.left (.dead (.dead (.dead (.right (.dead (.dead (.dead (.dead hd.split)))))))))))
      ?_ (.var (.there (.there (.there (.there (.there (.there
        (.here (.cons (.cons (.cons (.cons hd))))))))))))
    exact .tensorI (.dead (.left (.right (.dead (.dead (.dead (.dead (.dead (.dead (.dead (.dead hd.split)))))))))))
      (.var (.there (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons hd))))))))))))
      (.var (.there (.there (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons hd))))))))))))

/-- The block at the head, on the environment of its definition. -/
theorem d_blockHere {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) (A B : VTy) (Et : Ty)
    (hE : Et.scopedB Δ = true) :
    DerivesWf Δ Γ blockHere
      (.lolli (.tensor A.tr (.tensor (.bang (.lolli (.tensor A.tr Et) (.tensor B.tr Et))) Et))
        (.tensor B.tr (.tensor (.bang (.lolli (.tensor A.tr Et) (.tensor B.tr Et))) Et))) := by
  have hd := hΓ
  refine .lolliI (by simp [Ty.scopedB, hE]) ?_
  refine .tensorE (T₁ := A.tr) (T₂ := .tensor (.bang (.lolli (.tensor A.tr Et) (.tensor B.tr Et))) Et)
    (.left hd.split) (by simp [Ty.scopedB, hE]) (.var (.here hd)) ?_
  -- ctx: env 0, a 1, p 2
  refine .tensorE (T₁ := .bang (.lolli (.tensor A.tr Et) (.tensor B.tr Et))) (T₂ := Et)
    (.left (.right (.dead hd.split))) (by simp [Ty.scopedB, hE]) (.var (.here (.cons (.cons hd)))) ?_
  -- ctx: et 0, f 1, env 2, a 3, p 4
  refine .tensorE (T₁ := .bang (.lolli (.tensor A.tr Et) (.tensor B.tr Et)))
    (T₂ := .bang (.lolli (.tensor A.tr Et) (.tensor B.tr Et)))
    (.right (.left (.dead (.right (.dead hd.split))))) (by simp [Ty.scopedB, hE])
    (.lolliE (.dead (.left (.dead (.dead (.dead hd.split)))))
      (.var (.there (.here (.cons (.cons (.cons hd))))))
      (.copyBangAx (.cons (.cons (.cons (.cons (.cons hd))))))) ?_
  -- ctx: f₂ 0, f₁ 1, et 2, f 3, env 4, a 5, p 6
  refine .tensorE (T₁ := B.tr) (T₂ := Et)
    (.right (.left (.left (.dead (.dead (.left (.dead hd.split)))))))
    (by simp [Ty.scopedB, hE]) ?_ ?_
  · refine .lolliE (T₁ := .tensor A.tr Et) (.dead (.right (.left (.dead (.dead (.left (.dead hd.split)))))))
      (.tensorI (.dead (.dead (.right (.dead (.dead (.left (.dead hd.split)))))))
        (.var (.there (.there (.there (.there (.there (.here (.cons hd))))))))
        (.var (.there (.there (.here (.cons (.cons (.cons (.cons hd))))))))) ?_
    exact .bangE (.var (.there (.here (.cons (.cons (.cons (.cons (.cons hd))))))))
  · -- ctx: et′ 0, b 1, f₂ 2, f₁ 3, et 4, f 5, env 6, a 7, p 8
    exact .tensorI (.right (.left (.right (.dead (.dead (.dead (.dead (.dead (.dead hd.split)))))))))
      (.var (.there (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons hd))))))))))
      (.tensorI (.right (.dead (.left (.dead (.dead (.dead (.dead (.dead (.dead hd.split)))))))))
        (.var (.there (.there (.here (.cons (.cons (.cons (.cons (.cons (.cons hd))))))))))
        (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons (.cons (.cons hd)))))))))))

/-- One entry deeper. -/
theorem d_atSucc {Γ : Ctx Ty} (hΓ : Ctx.Dead Γ) {h : Expr} {A B Ent Et : Ty}
    (hh : ∀ {Γ' : Ctx Ty}, Ctx.Dead Γ' → DerivesWf Δ Γ' h (.lolli (.tensor A Et) (.tensor B Et)))
    (hA : A.scopedB Δ = true) (hB : B.scopedB Δ = true) (hEnt : Ent.scopedB Δ = true) (hEt : Et.scopedB Δ = true) :
    DerivesWf Δ Γ (atSucc h)
      (.lolli (.tensor A (.tensor Ent Et)) (.tensor B (.tensor Ent Et))) := by
  have hd := hΓ
  refine .lolliI (by simp [Ty.scopedB, hA, hEnt, hEt]) ?_
  refine .tensorE (T₁ := A) (T₂ := .tensor Ent Et)
    (.left hd.split) (by simp [Ty.scopedB, hA, hEnt, hEt]) (.var (.here hd)) ?_
  -- ctx: env 0, a 1, p 2
  refine .tensorE (T₁ := Ent) (T₂ := Et)
    (.left (.right (.dead hd.split))) (by simp [Ty.scopedB, hEnt, hEt]) (.var (.here (.cons (.cons hd)))) ?_
  -- ctx: et 0, ent 1, env 2, a 3, p 4
  refine .tensorE (T₁ := B) (T₂ := Et)
    (.left (.right (.dead (.left (.dead hd.split))))) (by simp [Ty.scopedB, hEt, hB])
    (.lolliE (.left (.dead (.dead (.left (.dead hd.split)))))
      (.tensorI (.right (.dead (.dead (.left (.dead hd.split)))))
        (.var (.there (.there (.there (.here (.cons hd))))))
        (.var (.here (.cons (.cons (.cons (.cons hd)))))))
      (hh (.cons (.cons (.cons (.cons (.cons hd))))))) ?_
  -- ctx: et′ 0, b 1, et 2, ent 3, env 4, a 5, p 6
  exact .tensorI (.right (.left (.dead (.right (.dead (.dead (.dead hd.split)))))))
    (.var (.there (.here (.cons (.cons (.cons (.cons (.cons hd))))))))
    (.tensorI (.right (.dead (.dead (.left (.dead (.dead (.dead hd.split)))))))
      (.var (.there (.there (.there (.here (.cons (.cons (.cons hd))))))))
      (.var (.here (.cons (.cons (.cons (.cons (.cons (.cons hd)))))))))

/-- The operation of the capability at index `j`. -/
theorem d_opAt {n : Nat} : ∀ (K : List Entry) (j : Nat) {S A B : VTy},
    K[j]? = some (.cap S A B) → (EnvTy n K).scopedB Δ = true → ∀ {Γ : Ctx Ty}, Ctx.Dead Γ →
      DerivesWf Δ Γ (opAt j) (.lolli (.tensor A.tr (EnvTy n K)) (.tensor B.tr (EnvTy n K)))
  | [], _, _, _, _, hj, _, _, _ => by simp at hj
  | .cap S' A' B' :: t, 0, S, A, B, hj, hE, Γ, hΓ => by
      simp only [List.getElem?_cons_zero, Option.some.injEq, Entry.cap.injEq] at hj
      obtain ⟨rfl, rfl, rfl⟩ := hj
      simp only [EnvTy, Ty.scopedB, Bool.and_eq_true] at hE
      exact d_opHere hΓ _ _ _ _ _ hE.2 hE.1.1.1
  | .blk _ _ :: t, 0, _, _, _, hj, _, _, _ => by simp at hj
  | e :: t, j + 1, S, A, B, hj, hE, Γ, hΓ => by
      simp only [List.getElem?_cons_succ] at hj
      have hsc : ∀ {E₀ : Ty}, (Ty.tensor E₀ (EnvTy n t)).scopedB Δ = true →
          E₀.scopedB Δ = true ∧ (EnvTy n t).scopedB Δ = true := by
        intro E₀ h; simpa [Ty.scopedB] using h
      cases e with
      | cap S' A' B' =>
          obtain ⟨h1, h2⟩ := hsc hE
          exact d_atSucc hΓ (fun hΓ' => d_opAt t j hj h2 hΓ') (VTy.scoped _ _) (VTy.scoped _ _) h1 h2
      | blk A' B' =>
          obtain ⟨h1, h2⟩ := hsc hE
          exact d_atSucc hΓ (fun hΓ' => d_opAt t j hj h2 hΓ') (VTy.scoped _ _) (VTy.scoped _ _) h1 h2

/-- The block at index `j`, on the environment of its definition. -/
theorem d_blockAt {n : Nat} : ∀ (K : List Entry) (j : Nat) {A B : VTy},
    K[j]? = some (.blk A B) → (EnvTy n K).scopedB Δ = true → ∀ {Γ : Ctx Ty}, Ctx.Dead Γ →
      DerivesWf Δ Γ (blockAt j) (.lolli (.tensor A.tr (EnvTy n K)) (.tensor B.tr (EnvTy n K)))
  | [], _, _, _, hj, _, _, _ => by simp at hj
  | .blk A' B' :: t, 0, A, B, hj, hE, Γ, hΓ => by
      simp only [List.getElem?_cons_zero, Option.some.injEq, Entry.blk.injEq] at hj
      obtain ⟨rfl, rfl⟩ := hj
      simp only [EnvTy, Ty.scopedB, Bool.and_eq_true] at hE
      exact d_blockHere hΓ _ _ _ hE.2
  | .cap _ _ _ :: t, 0, _, _, hj, _, _, _ => by simp at hj
  | e :: t, j + 1, A, B, hj, hE, Γ, hΓ => by
      simp only [List.getElem?_cons_succ] at hj
      have hsc : ∀ {E₀ : Ty}, (Ty.tensor E₀ (EnvTy n t)).scopedB Δ = true →
          E₀.scopedB Δ = true ∧ (EnvTy n t).scopedB Δ = true := by
        intro E₀ h; simpa [Ty.scopedB] using h
      cases e with
      | cap S' A' B' =>
          obtain ⟨h1, h2⟩ := hsc hE
          exact d_atSucc hΓ (fun hΓ' => d_blockAt t j hj h2 hΓ') (VTy.scoped _ _) (VTy.scoped _ _) h1 h2
      | blk A' B' =>
          obtain ⟨h1, h2⟩ := hsc hE
          exact d_atSucc hΓ (fun hΓ' => d_blockAt t j hj h2 hΓ') (VTy.scoped _ _) (VTy.scoped _ _) h1 h2

end HandlersAsBorrows.Xi
