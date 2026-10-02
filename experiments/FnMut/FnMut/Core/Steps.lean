import FnMut.Core.Fundamental
import Paper.Examples.Programs

/-!
# Core — runs through an evaluation context  `[spec §3]`

The machine's steps decompose uniquely: a step of `K[e]`, with `e` not a value, is a step of
`e` under `K` (`step1_plug_inv`), so a run of `K[e]` to a value first runs `e` to a value
(`steps_plug_inv`).  These are the facts a statement about *every* run of a term needs; the
`wp` development only ever builds runs, so the library does not state them.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.LogRel.Core
open BoCa BoCa.BoLo

/-- A value, at each of the forms a redex holds one in. -/
syntax "isv" : tactic
macro_rules
  | `(tactic| isv) => `(tactic| first
      | exact Subtype.property _ | exact IsVal.lam | exact IsVal.prim | exact IsVal.loc
      | exact IsVal.unit | exact IsVal.pair (Subtype.property _) (Subtype.property _)
      | exact IsVal.inj₁ (Subtype.property _) | exact IsVal.inj₂ (Subtype.property _)
      | exact IsVal.storeV IsVal.loc)

/-! ### Comparable decompositions -/

/-- Two decompositions of one term at non-values are comparable: one hole lies inside the
other's filling. -/
theorem plug_cmp : ∀ (K K' : Kont) {e e' : Expr}, ¬ IsVal e → ¬ IsVal e' →
    K.plug e = K'.plug e' →
      (∃ K'', e = K''.plug e' ∧ K' = K.comp K'') ∨ (∃ K'', e' = K''.plug e ∧ K = K'.comp K'') := by
  intro K
  induction K with
  | hole => intro K' e e' _ _ h; exact .inl ⟨K', h, rfl⟩
  | pairL K e₂ ih =>
      intro K' e e' hnv hnv' h
      cases K' with
      | hole => exact .inr ⟨.pairL K e₂, h.symm, rfl⟩
      | pairL K' e₂' =>
          simp only [Kont.plug, Expr.pair.injEq] at h
          rcases ih K' hnv hnv' h.1 with ⟨K'', h₁, h₂⟩ | ⟨K'', h₁, h₂⟩
          · exact .inl ⟨K'', h₁, by rw [h₂, h.2]; rfl⟩
          · exact .inr ⟨K'', h₁, by rw [h₂, h.2]; rfl⟩
      | pairR v K' =>
          simp only [Kont.plug, Expr.pair.injEq] at h
          exact absurd (K.isVal_of_plug (h.1 ▸ v.2)) hnv
      | _ => simp [Kont.plug] at h
  | pairR v K ih =>
      intro K' e e' hnv hnv' h
      cases K' with
      | hole => exact .inr ⟨.pairR v K, h.symm, rfl⟩
      | pairL K' e₂' =>
          simp only [Kont.plug, Expr.pair.injEq] at h
          exact absurd (K'.isVal_of_plug (h.1 ▸ v.2)) hnv'
      | pairR v' K' =>
          simp only [Kont.plug, Expr.pair.injEq] at h
          have hv : v = v' := Subtype.ext h.1
          subst hv
          rcases ih K' hnv hnv' h.2 with ⟨K'', h₁, h₂⟩ | ⟨K'', h₁, h₂⟩
          · exact .inl ⟨K'', h₁, by rw [h₂]; rfl⟩
          · exact .inr ⟨K'', h₁, by rw [h₂]; rfl⟩
      | _ => simp [Kont.plug] at h
  | letpair K e₂ ih =>
      intro K' e e' hnv hnv' h
      cases K' with
      | hole => exact .inr ⟨.letpair K e₂, h.symm, rfl⟩
      | letpair K' e₂' =>
          simp only [Kont.plug, Expr.letpair.injEq] at h
          rcases ih K' hnv hnv' h.1 with ⟨K'', h₁, h₂⟩ | ⟨K'', h₁, h₂⟩
          · exact .inl ⟨K'', h₁, by rw [h₂, h.2]; rfl⟩
          · exact .inr ⟨K'', h₁, by rw [h₂, h.2]; rfl⟩
      | _ => simp [Kont.plug] at h
  | case K e₁ e₂ ih =>
      intro K' e e' hnv hnv' h
      cases K' with
      | hole => exact .inr ⟨.case K e₁ e₂, h.symm, rfl⟩
      | case K' e₁' e₂' =>
          simp only [Kont.plug, Expr.case.injEq] at h
          rcases ih K' hnv hnv' h.1 with ⟨K'', h₁, h₂⟩ | ⟨K'', h₁, h₂⟩
          · exact .inl ⟨K'', h₁, by rw [h₂, h.2.1, h.2.2]; rfl⟩
          · exact .inr ⟨K'', h₁, by rw [h₂, h.2.1, h.2.2]; rfl⟩
      | _ => simp [Kont.plug] at h
  | seq K e₂ ih =>
      intro K' e e' hnv hnv' h
      cases K' with
      | hole => exact .inr ⟨.seq K e₂, h.symm, rfl⟩
      | seq K' e₂' =>
          simp only [Kont.plug, Expr.seq.injEq] at h
          rcases ih K' hnv hnv' h.1 with ⟨K'', h₁, h₂⟩ | ⟨K'', h₁, h₂⟩
          · exact .inl ⟨K'', h₁, by rw [h₂, h.2]; rfl⟩
          · exact .inr ⟨K'', h₁, by rw [h₂, h.2]; rfl⟩
      | _ => simp [Kont.plug] at h
  | inj₁ K ih =>
      intro K' e e' hnv hnv' h
      cases K' with
      | hole => exact .inr ⟨.inj₁ K, h.symm, rfl⟩
      | inj₁ K' =>
          simp only [Kont.plug, Expr.inj₁.injEq] at h
          rcases ih K' hnv hnv' h with ⟨K'', h₁, h₂⟩ | ⟨K'', h₁, h₂⟩
          · exact .inl ⟨K'', h₁, by rw [h₂]; rfl⟩
          · exact .inr ⟨K'', h₁, by rw [h₂]; rfl⟩
      | _ => simp [Kont.plug] at h
  | inj₂ K ih =>
      intro K' e e' hnv hnv' h
      cases K' with
      | hole => exact .inr ⟨.inj₂ K, h.symm, rfl⟩
      | inj₂ K' =>
          simp only [Kont.plug, Expr.inj₂.injEq] at h
          rcases ih K' hnv hnv' h with ⟨K'', h₁, h₂⟩ | ⟨K'', h₁, h₂⟩
          · exact .inl ⟨K'', h₁, by rw [h₂]; rfl⟩
          · exact .inr ⟨K'', h₁, by rw [h₂]; rfl⟩
      | _ => simp [Kont.plug] at h
  | appR f K ih =>
      intro K' e e' hnv hnv' h
      cases K' with
      | hole => exact .inr ⟨.appR f K, h.symm, rfl⟩
      | appR f' K' =>
          simp only [Kont.plug, Expr.app.injEq] at h
          rcases ih K' hnv hnv' h.2 with ⟨K'', h₁, h₂⟩ | ⟨K'', h₁, h₂⟩
          · exact .inl ⟨K'', h₁, by rw [h₂, h.1]; rfl⟩
          · exact .inr ⟨K'', h₁, by rw [h₂, h.1]; rfl⟩
      | appL K' v =>
          simp only [Kont.plug, Expr.app.injEq] at h
          exact absurd (K.isVal_of_plug (h.2 ▸ v.2)) hnv
      | _ => simp [Kont.plug] at h
  | appL K v ih =>
      intro K' e e' hnv hnv' h
      cases K' with
      | hole => exact .inr ⟨.appL K v, h.symm, rfl⟩
      | appR f' K' =>
          simp only [Kont.plug, Expr.app.injEq] at h
          exact absurd (K'.isVal_of_plug (h.2 ▸ v.2)) hnv'
      | appL K' v' =>
          simp only [Kont.plug, Expr.app.injEq] at h
          have hv : v = v' := Subtype.ext h.2
          subst hv
          rcases ih K' hnv hnv' h.1 with ⟨K'', h₁, h₂⟩ | ⟨K'', h₁, h₂⟩
          · exact .inl ⟨K'', h₁, by rw [h₂]; rfl⟩
          · exact .inr ⟨K'', h₁, by rw [h₂]; rfl⟩
      | _ => simp [Kont.plug] at h

theorem _root_.BoCa.BoLo.Kont.comp_hole (K : Kont) : K.comp .hole = K := by
  induction K <;> simp_all [BoCa.BoLo.Kont.comp]

theorem comp_eq_hole {K K' : Kont} (h : K.comp K' = .hole) : K = .hole ∧ K' = .hole := by
  cases K <;> simp_all [Kont.comp]

/-! ### Operations and catchers hold no redex -/

/-- A plugged `app (prim p) (val v)` with `p` a primitive that takes no step at one argument. -/
theorem plug_primApp {K : Kont} {a : Expr} {p : Prim} {v : Val}
    (h : K.plug a = .app (.val (.prim p)) (.val v)) (hna : ¬ IsVal a) :
    K = .hole := by
  cases K with
  | hole => rfl
  | appR f K =>
      simp only [Kont.plug, Expr.app.injEq] at h
      exact absurd (K.isVal_of_plug (h.2 ▸ v.2)) hna
  | appL K w =>
      simp only [Kont.plug, Expr.app.injEq] at h
      exact absurd (K.isVal_of_plug (h.1 ▸ IsVal.prim)) hna
  | _ => simp [Kont.plug] at h

/-- The primitives that are not head redexes at one argument. -/
def _root_.BoCa.Prim.Inert : Prim → Prop
  | .perform | .raise | .hnd | .ubind | .ccatch | .cfin => True
  | _ => False

theorem head_not_inertApp {μ μ' : Heap} {p : Prim} {v : Val} {a' : Expr} (hp : p.Inert)
    (h : Head μ (.app (.val (.prim p)) (.val v)) μ' a') : False := by
  generalize hE : Expr.app (.val (.prim p)) (.val v) = E at h
  cases h with
  | cancel Ns K hK =>
      simp only [ccatchE, Expr.app.injEq] at hE
      obtain ⟨-, hE⟩ := hE
      have hv : IsVal (K.plug (raiseE (.val (cancelVal Ns none)))) := by rw [← hE]; exact v.2
      have := K.isVal_of_plug hv
      simp [raiseE] at this
  | creraise Ns E K hK =>
      simp only [ccatchE, Expr.app.injEq] at hE
      obtain ⟨-, hE⟩ := hE
      have hv : IsVal (K.plug (raiseE (.val (cancelVal Ns (some E))))) := by rw [← hE]; exact v.2
      have := K.isVal_of_plug hv
      simp [raiseE] at this
  | _ => cases p <;> simp_all [Prim.Inert, hndE, ubindE, cfinE, Expr.val, Val.prim, Val.lam]

/-- A context free of the catchers of an operation holds no redex around it. -/
def OpFree (isRaise : Bool) (n : UInt32) (K : Kont) : Prop :=
  if isRaise then K.Catches n = false else K.HasHnd n = false

/-- The operation expression. -/
def opE (isRaise : Bool) (p : Val) : Expr :=
  if isRaise then raiseE (.val p) else performE (.val p)

theorem opE_not_isVal (r : Bool) (p : Val) : ¬ IsVal (opE r p) := by
  cases r <;> simp [opE, raiseE, performE] <;> intro h <;> cases h

theorem opFree_right {r : Bool} {n : UInt32} {K K' : Kont} (h : OpFree r n (K.comp K')) :
    OpFree r n K' := by
  cases r <;> simp_all [OpFree, hasHnd_comp, catches_comp]

theorem opE_eq_app (r : Bool) (p : Val) :
    opE r p = .app (.val (.prim (if r then .raise else .perform))) (.val p) := by
  cases r <;> rfl

/-- Two plugged operations: the same context and the same operation. -/
theorem plug_opE_eq {K K' : Kont} {r r' : Bool} {p p' : Val}
    (h : K.plug (opE r p) = K'.plug (opE r' p')) : K = K' ∧ r = r' ∧ p = p' := by
  rcases plug_cmp K K' (opE_not_isVal r p) (opE_not_isVal r' p') h with
    ⟨K'', h₁, h₂⟩ | ⟨K'', h₁, h₂⟩
  · have hK := plug_primApp (h₁.symm.trans (opE_eq_app r p)) (opE_not_isVal r' p')
    subst hK
    simp only [Kont.plug] at h₁
    rw [Kont.comp_hole] at h₂
    subst h₂
    rw [opE_eq_app, opE_eq_app] at h₁
    simp only [Expr.app.injEq] at h₁
    refine ⟨rfl, ?_, Subtype.ext h₁.2⟩
    cases r <;> cases r' <;> simp_all
  · have hK := plug_primApp (h₁.symm.trans (opE_eq_app r' p')) (opE_not_isVal r p)
    subst hK
    simp only [Kont.plug] at h₁
    rw [Kont.comp_hole] at h₂
    subst h₂
    rw [opE_eq_app, opE_eq_app] at h₁
    simp only [Expr.app.injEq] at h₁
    refine ⟨rfl, ?_, (Subtype.ext h₁.2).symm⟩
    cases r <;> cases r' <;> simp_all

/-- The name of an operation's payload. -/
def payloadName : Val → Option UInt32
  | ⟨.pair (.prim (.lit (.i32 n))) _, _⟩ => some n
  | _ => none

@[simp] theorem payloadName_opPayload (n i : UInt32) (v : Val) :
    payloadName (opPayload n i v) = some n := rfl

theorem hndVal_inj {n n' : UInt32} {hr hs hr' hs' : Val}
    (h : (hndVal n hr hs).1 = (hndVal n' hr' hs').1) : n = n' ∧ hr = hr' ∧ hs = hs' := by
  simp only [hndVal, Val.pair, Val.i32, Expr.pair.injEq, Expr.prim.injEq, Prim.lit.injEq,
    IntLit.i32.injEq] at h
  exact ⟨h.1, Subtype.ext h.2.1, Subtype.ext h.2.2⟩

theorem opPayload_inj {n n' i i' : UInt32} {v v' : Val} (h : opPayload n i v = opPayload n' i' v') :
    n = n' ∧ i = i' ∧ v = v' := by
  have h := congrArg Subtype.val h
  simp only [opPayload, Val.pair, Val.i32, Expr.pair.injEq, Expr.prim.injEq, Prim.lit.injEq,
    IntLit.i32.injEq] at h
  exact ⟨h.1, h.2.1, Subtype.ext h.2.2⟩

theorem valPair_inj {a b c d : Val} (h : (Val.pair a b).1 = (Val.pair c d).1) : a = c ∧ b = d := by
  simp only [Val.pair, Expr.pair.injEq] at h
  exact ⟨Subtype.ext h.1, Subtype.ext h.2⟩

theorem plug_perform_ne_val (K : Kont) (p w : Val) : K.plug (performE (.val p)) ≠ Expr.val w :=
  fun h => opE_not_isVal false p (K.isVal_of_plug (show IsVal (K.plug (opE false p)) from h ▸ w.2))

theorem plug_raise_ne_val (K : Kont) (p w : Val) : K.plug (raiseE (.val p)) ≠ Expr.val w :=
  fun h => opE_not_isVal true p (K.isVal_of_plug (show IsVal (K.plug (opE true p)) from h ▸ w.2))

theorem plug_perform_ne_raise (K K' : Kont) (p p' : Val) :
    K.plug (performE (.val p)) ≠ K'.plug (raiseE (.val p')) := fun h =>
  absurd (plug_opE_eq (r := false) (r' := true) h).2.1 (by simp)

theorem plug_perform_inj {K K' : Kont} {p p' : Val}
    (h : K.plug (performE (.val p)) = K'.plug (performE (.val p'))) : K = K' ∧ p = p' :=
  let h' := plug_opE_eq (r := false) (r' := false) h; ⟨h'.1, h'.2.2⟩

theorem plug_raise_inj {K K' : Kont} {p p' : Val}
    (h : K.plug (raiseE (.val p)) = K'.plug (raiseE (.val p'))) : K = K' ∧ p = p' :=
  let h' := plug_opE_eq (r := true) (r' := true) h; ⟨h'.1, h'.2.2⟩

theorem namesVal_inj : ∀ {N N' : List UInt32}, namesVal N = namesVal N' → N = N'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [namesVal, Val.inj₁, Val.inj₂] at h
  | _ :: _, [], h => by simp [namesVal, Val.inj₁, Val.inj₂] at h
  | m :: N, m' :: N', h => by
      have h := congrArg Subtype.val h
      simp only [namesVal, Val.inj₂, Val.pair, Val.i32, Expr.inj₂.injEq, Expr.pair.injEq,
        Expr.prim.injEq, Prim.lit.injEq, IntLit.i32.injEq] at h
      rw [h.1, namesVal_inj (Subtype.ext h.2)]

theorem errVal_inj {e e' : Option Val} (h : errVal e = errVal e') : e = e' := by
  have h := congrArg Subtype.val h
  cases e <;> cases e' <;> simp [errVal, Val.inj₁, Val.inj₂] at h ⊢
  exact Subtype.ext h

theorem cancelVal_inj {N N' : List UInt32} {e e' : Option Val}
    (h : cancelVal N e = cancelVal N' e') : N = N' ∧ e = e' := by
  obtain ⟨-, -, h⟩ := opPayload_inj h
  obtain ⟨h₁, h₂⟩ := valPair_inj (congrArg Subtype.val h)
  exact ⟨namesVal_inj h₁, errVal_inj h₂⟩

@[simp] theorem payloadName_cancelVal (N : List UInt32) (e : Option Val) :
    payloadName (cancelVal N e) = some 0 := rfl

/-- The evaluation positions strictly inside a redex that do not hold a value: the body of a
handler, a finaliser or a `ccatch`, and the function part `hnd H` or `ubind ND` of a handler or
finaliser whose body is a value. -/
def CatcherPos (K : Kont) (e : Expr) : Prop :=
  (∃ n hr hs K', K = .appR (.app (.val (.prim .hnd)) (.val (hndVal n hr hs))) K') ∨
  (∃ N D K', K = .appR (.app (.val (.prim .ubind)) (.val (Val.pair N D))) K') ∨
  (∃ K', K = .appR (.val (.prim .ccatch)) K') ∨
  (∃ (w H : Val) (p : Prim), p.Inert ∧ K = .appL .hole w ∧ e = .app (.val (.prim p)) (.val H)) ∨
  (∃ Ns err K', K = .appR (.app (.val (.prim .cfin)) (.val (cancelVal Ns err))) K')

/-- A strict evaluation position of a redex that holds a non-value is a catcher position. -/
theorem head_plug {μ μ' : Heap} {E a' : Expr} (hh : Head μ E μ' a') :
    ∀ (K : Kont) {e : Expr}, ¬ IsVal e → E = K.plug e → K ≠ .hole → CatcherPos K e := by
  intro K e hnv hE hK
  cases K with
  | hole => exact absurd rfl hK
  | appR f K =>
      cases hh with
      | hret n hr hs w =>
          simp only [hndE, Kont.plug, Expr.app.injEq] at hE
          exact absurd (K.isVal_of_plug (hE.2 ▸ w.2)) hnv
      | uthen N D w =>
          simp only [ubindE, Kont.plug, Expr.app.injEq] at hE
          exact absurd (K.isVal_of_plug (hE.2 ▸ w.2)) hnv
      | hop n i hr hs c v K₀ hc hK₀ =>
          simp only [hndE, Kont.plug, Expr.app.injEq] at hE
          exact .inl ⟨n, hr, hs, K, by rw [hE.1]⟩
      | hunwind n i hr hs c v K₀ hc hK₀ =>
          simp only [hndE, Kont.plug, Expr.app.injEq] at hE
          exact .inl ⟨n, hr, hs, K, by rw [hE.1]⟩
      | ufin N D n i v K₀ hn hK₀ =>
          simp only [ubindE, Kont.plug, Expr.app.injEq] at hE
          exact .inr (.inl ⟨N, D, K, by rw [hE.1]⟩)
      | ufinC N D Ns err K₀ hK₀ =>
          simp only [ubindE, Kont.plug, Expr.app.injEq] at hE
          exact .inr (.inl ⟨N, D, K, by rw [hE.1]⟩)
      | cancel Ns K₀ hK₀ =>
          simp only [ccatchE, Kont.plug, Expr.app.injEq] at hE
          exact .inr (.inr (.inl ⟨K, by rw [hE.1]⟩))
      | creraise Ns E K₀ hK₀ =>
          simp only [ccatchE, Kont.plug, Expr.app.injEq] at hE
          exact .inr (.inr (.inl ⟨K, by rw [hE.1]⟩))
      | cferr Ns err m j w K₀ hK₀ =>
          simp only [cfinE, Kont.plug, Expr.app.injEq] at hE
          exact .inr (.inr (.inr (.inr ⟨Ns, err, K, by rw [hE.1]⟩)))
      | cfret Ns err w =>
          simp only [cfinE, Kont.plug, Expr.app.injEq] at hE
          exact absurd (K.isVal_of_plug (hE.2 ▸ w.2)) hnv
      | _ =>
          exfalso; apply hnv; apply K.isVal_of_plug
          simp only [Kont.plug] at hE
          first | (simp at hE; done) | (injection hE with h1 h2; rw [← h2]; isv)
  | appL K v =>
      cases hh with
      | hret n hr hs w =>
          simp only [hndE, Kont.plug, Expr.app.injEq] at hE
          obtain ⟨h1, -⟩ := hE
          obtain rfl := plug_primApp h1.symm hnv
          exact .inr (.inr (.inr (.inl ⟨v, hndVal n hr hs, .hnd, trivial, rfl, by simpa [Kont.plug] using h1.symm⟩)))
      | uthen N D w =>
          simp only [ubindE, Kont.plug, Expr.app.injEq] at hE
          obtain ⟨h1, -⟩ := hE
          obtain rfl := plug_primApp h1.symm hnv
          exact .inr (.inr (.inr (.inl ⟨v, .pair N D, .ubind, trivial, rfl, by simpa [Kont.plug] using h1.symm⟩)))
      | hop n i hr hs c w K₀ hc hK₀ =>
          simp only [hndE, Kont.plug, Expr.app.injEq] at hE
          exact (opE_not_isVal false (opPayload n i w) (K₀.isVal_of_plug (show IsVal (K₀.plug (performE (.val (opPayload n i w)))) from by rw [hE.2]; exact v.2))).elim
      | hunwind n i hr hs c w K₀ hc hK₀ =>
          simp only [hndE, Kont.plug, Expr.app.injEq] at hE
          exact (opE_not_isVal true (opPayload n i w) (K₀.isVal_of_plug (show IsVal (K₀.plug (raiseE (.val (opPayload n i w)))) from by rw [hE.2]; exact v.2))).elim
      | ufin N D n i w K₀ hn hK₀ =>
          simp only [ubindE, Kont.plug, Expr.app.injEq] at hE
          exact (opE_not_isVal true (opPayload n i w) (K₀.isVal_of_plug (show IsVal (K₀.plug (raiseE (.val (opPayload n i w)))) from by rw [hE.2]; exact v.2))).elim
      | ufinC N D Ns err K₀ hK₀ =>
          simp only [ubindE, Kont.plug, Expr.app.injEq] at hE
          exact (plug_raise_ne_val K₀ _ v hE.2).elim
      | cancel Ns K₀ hK₀ =>
          simp only [ccatchE, Kont.plug, Expr.app.injEq] at hE
          exact (plug_raise_ne_val K₀ _ v hE.2).elim
      | creraise Ns E K₀ hK₀ =>
          simp only [ccatchE, Kont.plug, Expr.app.injEq] at hE
          exact (plug_raise_ne_val K₀ _ v hE.2).elim
      | cferr Ns err m j w K₀ hK₀ =>
          simp only [cfinE, Kont.plug, Expr.app.injEq] at hE
          exact (plug_raise_ne_val K₀ _ v hE.2).elim
      | cfret Ns err w =>
          simp only [cfinE, Kont.plug, Expr.app.injEq] at hE
          obtain ⟨h1, -⟩ := hE
          obtain rfl := plug_primApp h1.symm hnv
          exact .inr (.inr (.inr (.inl ⟨v, cancelVal Ns err, .cfin, trivial, rfl, by simpa [Kont.plug] using h1.symm⟩)))
      | _ =>
          exfalso; apply hnv; apply K.isVal_of_plug
          simp only [Kont.plug] at hE
          first | (simp at hE; done) | (injection hE with h1 h2; rw [← h1]; isv)
  | letpair K e₂ =>
      exfalso; apply hnv; apply K.isVal_of_plug
      cases hh <;> simp only [Kont.plug, hndE, ubindE, ccatchE, cfinE] at hE <;>
        first | (simp at hE; done) | (injection hE with h1 h2; rw [← h1]; isv)
  | case K e₁ e₂ =>
      exfalso; apply hnv; apply K.isVal_of_plug
      cases hh <;> simp only [Kont.plug, hndE, ubindE, ccatchE, cfinE] at hE <;>
        first | (simp at hE; done) | (injection hE with h1 h2 h3; rw [← h1]; isv)
  | seq K e₂ =>
      exfalso; apply hnv; apply K.isVal_of_plug
      cases hh <;> simp only [Kont.plug, hndE, ubindE, ccatchE, cfinE] at hE <;>
        first | (simp at hE; done) | (injection hE with h1 h2; rw [← h1]; isv)
  | pairL K e₂ =>
      exfalso; cases hh <;> simp [Kont.plug, hndE, ubindE, ccatchE, cfinE] at hE
  | pairR v K =>
      exfalso; cases hh <;> simp [Kont.plug, hndE, ubindE, ccatchE, cfinE] at hE
  | inj₁ K =>
      exfalso; cases hh <;> simp [Kont.plug, hndE, ubindE, ccatchE, cfinE] at hE
  | inj₂ K =>
      exfalso; cases hh <;> simp [Kont.plug, hndE, ubindE, ccatchE, cfinE] at hE

/-- **A redex holds no redex around an operation its context does not catch.** -/
theorem head_not_opPlug {μ μ' : Heap} {a' : Expr} {K₁ : Kont} {r : Bool} {p : Val} {n : UInt32}
    (hn : payloadName p = some n) (hK : OpFree r n K₁)
    (h : Head μ (K₁.plug (opE r p)) μ' a') : False := by
  by_cases h0 : K₁ = .hole
  · subst h0
    cases r
    · exact head_not_inertApp (p := .perform) trivial (by simpa [opE, performE] using h)
    · exact head_not_inertApp (p := .raise) trivial (by simpa [opE, raiseE] using h)
  rcases head_plug h K₁ (opE_not_isVal r p) rfl h0 with
    ⟨n₀, hr₀, hs₀, K', rfl⟩ | ⟨N₀, D₀, K', rfl⟩ | ⟨K', rfl⟩ | ⟨w, H, q, hq, rfl, he⟩ |
      ⟨Ns₀, err₀, K', rfl⟩
  · generalize hE : (Kont.appR (.app (.val (.prim .hnd)) (.val (hndVal n₀ hr₀ hs₀))) K').plug (opE r p) = E at h
    cases h with
    | hop n' i hr hs c v K₀ hc hK₀ =>
        simp only [hndE, Kont.plug, Expr.app.injEq] at hE
        obtain ⟨⟨-, hH⟩, hE⟩ := hE
        obtain ⟨rfl, rfl, rfl⟩ := plug_opE_eq (r' := false) (p' := opPayload n' i v)
          (by simpa [opE] using hE)
        obtain rfl : n₀ = n' := by simp [hndVal, Val.pair, Val.i32, Expr.val] at hH; exact hH.1
        simp at hn; subst hn
        simp [OpFree, Kont.HasHnd, hndVal, Val.i32, Val.pair] at hK
    | hunwind n' i hr hs c v K₀ hc hK₀ =>
        simp only [hndE, Kont.plug, Expr.app.injEq] at hE
        obtain ⟨⟨-, hH⟩, hE⟩ := hE
        obtain ⟨rfl, rfl, rfl⟩ := plug_opE_eq (r' := true) (p' := opPayload n' i v)
          (by simpa [opE] using hE)
        obtain rfl : n₀ = n' := by simp [hndVal, Val.pair, Val.i32, Expr.val] at hH; exact hH.1
        simp at hn; subst hn
        simp [OpFree, Kont.Catches, hndVal, Val.i32, Val.pair] at hK
    | hret n' hr hs w =>
        simp only [hndE, Kont.plug, Expr.app.injEq] at hE
        exact opE_not_isVal r p (K'.isVal_of_plug (hE.2 ▸ w.2))
    | _ => simp_all [Kont.plug, hndE, ubindE, ccatchE, cfinE, opE, raiseE, performE]
  · generalize hE : (Kont.appR (.app (.val (.prim .ubind)) (.val (Val.pair N₀ D₀))) K').plug (opE r p) = E at h
    cases h with
    | ufin N D n' i v K₀ hn' hK₀ =>
        simp only [ubindE, Kont.plug, Expr.app.injEq] at hE
        obtain ⟨-, hE⟩ := hE
        obtain ⟨rfl, rfl, rfl⟩ := plug_opE_eq (r' := true) (p' := opPayload n' i v)
          (by simpa [opE] using hE)
        simp [OpFree, Kont.Catches] at hK
    | ufinC N D Ns err K₀ hK₀ =>
        simp only [ubindE, Kont.plug, Expr.app.injEq] at hE
        obtain ⟨-, hE⟩ := hE
        obtain ⟨rfl, rfl, rfl⟩ := plug_opE_eq (r' := true) (p' := cancelVal Ns err)
          (by simpa [opE] using hE)
        simp [OpFree, Kont.Catches] at hK
    | uthen N D w =>
        simp only [ubindE, Kont.plug, Expr.app.injEq] at hE
        exact opE_not_isVal r p (K'.isVal_of_plug (hE.2 ▸ w.2))
    | _ => simp_all [Kont.plug, hndE, ubindE, ccatchE, cfinE, opE, raiseE, performE]
  · generalize hE : (Kont.appR (.val (.prim .ccatch)) K').plug (opE r p) = E at h
    cases h with
    | cancel Ns K₀ hK₀ =>
        simp only [ccatchE, Kont.plug, Expr.app.injEq] at hE
        obtain ⟨-, hE⟩ := hE
        obtain ⟨rfl, rfl, rfl⟩ := plug_opE_eq (r' := true) (p' := cancelVal Ns none)
          (by simpa [opE] using hE)
        simp at hn; subst hn
        simp [OpFree, Kont.Catches] at hK
    | creraise Ns E K₀ hK₀ =>
        simp only [ccatchE, Kont.plug, Expr.app.injEq] at hE
        obtain ⟨-, hE⟩ := hE
        obtain ⟨rfl, rfl, rfl⟩ := plug_opE_eq (r' := true) (p' := cancelVal Ns (some E))
          (by simpa [opE] using hE)
        simp at hn; subst hn
        simp [OpFree, Kont.Catches] at hK
    | _ => simp_all [Kont.plug, hndE, ubindE, ccatchE, cfinE, opE, raiseE, performE]
  · generalize hE : (Kont.appL .hole w).plug (opE r p) = E at h
    cases h <;> cases r <;> simp_all [Kont.plug, hndE, ubindE, ccatchE, cfinE, opE, raiseE, performE]
  · generalize hE : (Kont.appR (.app (.val (.prim .cfin)) (.val (cancelVal Ns₀ err₀))) K').plug (opE r p) = E at h
    cases h with
    | cferr Ns err m j v K₀ hK₀ =>
        simp only [cfinE, Kont.plug, Expr.app.injEq] at hE
        obtain ⟨-, hE⟩ := hE
        obtain ⟨rfl, rfl, rfl⟩ := plug_opE_eq (r' := true) (p' := opPayload m j v)
          (by simpa [opE] using hE)
        simp [OpFree, Kont.Catches] at hK
    | cfret Ns err w =>
        simp only [cfinE, Kont.plug, Expr.app.injEq] at hE
        exact opE_not_isVal r p (K'.isVal_of_plug (hE.2 ▸ w.2))
    | _ => simp_all [Kont.plug, hndE, ubindE, ccatchE, cfinE, opE, raiseE, performE]

/-- The two ways a redex `a` meets an operation under a context free of it. -/
theorem nested_op {μ₂ μ₂' : Heap} {a a' : Expr} {K' K₀ : Kont} {r : Bool} {p : Val} {n : UInt32}
    (hn : payloadName p = some n) (hK₀ : OpFree r n K₀) (ha : Head μ₂ a μ₂' a')
    (h : K'.plug a = K₀.plug (opE r p)) : False := by
  rcases plug_cmp K' K₀ ha.not_isVal (opE_not_isVal r p) h with ⟨K'', h₁, h₂⟩ | ⟨K'', h₁, h₂⟩
  · subst h₁
    exact head_not_opPlug hn (opFree_right (h₂ ▸ hK₀)) ha
  · have hK := plug_primApp (h₁.symm.trans (opE_eq_app r p)) ha.not_isVal
    subst hK
    simp only [Kont.plug] at h₁
    subst h₁
    rw [opE_eq_app] at ha
    cases r
    · exact head_not_inertApp (p := .perform) trivial ha
    · exact head_not_inertApp (p := .raise) trivial ha

/-- **No redex strictly holds another at an evaluation position.** -/
theorem head_nested {μ μ' μ₂ μ₂' : Heap} {E E' a a' : Expr} (hh : Head μ E μ' E')
    (K : Kont) (hE : E = K.plug a) (ha : Head μ₂ a μ₂' a') : K = .hole := by
  by_contra hK
  rcases head_plug hh K ha.not_isVal hE hK with
    ⟨n₀, hr₀, hs₀, K', rfl⟩ | ⟨N₀, D₀, K', rfl⟩ | ⟨K', rfl⟩ | ⟨w, H, q, hq, rfl, rfl⟩ |
      ⟨Ns₀, err₀, K', rfl⟩
  · subst hE
    generalize hE : (Kont.appR (.app (.val (.prim .hnd)) (.val (hndVal n₀ hr₀ hs₀))) K').plug a = X at hh
    cases hh with
    | hop n i hr hs c v K₀ hc hK₀ =>
        simp only [hndE, Kont.plug, Expr.app.injEq] at hE
        exact nested_op (r := false) (payloadName_opPayload n i v) (by simpa [OpFree] using hK₀) ha
          (by simpa [opE] using hE.2)
    | hunwind n i hr hs c v K₀ hc hK₀ =>
        simp only [hndE, Kont.plug, Expr.app.injEq] at hE
        exact nested_op (r := true) (payloadName_opPayload n i v) (by simpa [OpFree] using hK₀) ha
          (by simpa [opE] using hE.2)
    | hret n hr hs w =>
        simp only [hndE, Kont.plug, Expr.app.injEq] at hE
        exact ha.not_isVal (K'.isVal_of_plug (by rw [hE.2]; exact w.2))
    | _ => simp_all [Kont.plug, hndE, ubindE, ccatchE, cfinE]
  · subst hE
    generalize hE : (Kont.appR (.app (.val (.prim .ubind)) (.val (Val.pair N₀ D₀))) K').plug a = X at hh
    cases hh with
    | ufin N D n i v K₀ hn hK₀ =>
        simp only [ubindE, Kont.plug, Expr.app.injEq] at hE
        exact nested_op (r := true) (payloadName_opPayload n i v) (by simpa [OpFree] using hK₀) ha
          (by simpa [opE] using hE.2)
    | ufinC N D Ns err K₀ hK₀ =>
        simp only [ubindE, Kont.plug, Expr.app.injEq] at hE
        exact nested_op (r := true) (payloadName_cancelVal Ns err) (by simpa [OpFree] using hK₀) ha
          (by simpa [opE] using hE.2)
    | uthen N D w =>
        simp only [ubindE, Kont.plug, Expr.app.injEq] at hE
        exact ha.not_isVal (K'.isVal_of_plug (by rw [hE.2]; exact w.2))
    | _ => simp_all [Kont.plug, hndE, ubindE, ccatchE, cfinE]
  · subst hE
    generalize hE : (Kont.appR (.val (.prim .ccatch)) K').plug a = X at hh
    cases hh with
    | cancel Ns K₀ hK₀ =>
        simp only [ccatchE, Kont.plug, Expr.app.injEq] at hE
        exact nested_op (r := true) (payloadName_cancelVal Ns none) (by simpa [OpFree] using hK₀) ha
          (by simpa [opE] using hE.2)
    | creraise Ns E K₀ hK₀ =>
        simp only [ccatchE, Kont.plug, Expr.app.injEq] at hE
        exact nested_op (r := true) (payloadName_cancelVal Ns (some E)) (by simpa [OpFree] using hK₀)
          ha (by simpa [opE] using hE.2)
    | _ => simp_all [Kont.plug, hndE, ubindE, ccatchE, cfinE]
  · exact head_not_inertApp hq ha
  · subst hE
    generalize hE : (Kont.appR (.app (.val (.prim .cfin)) (.val (cancelVal Ns₀ err₀))) K').plug a = X at hh
    cases hh with
    | cferr Ns err m j v K₀ hK₀ =>
        simp only [cfinE, Kont.plug, Expr.app.injEq] at hE
        exact nested_op (r := true) (payloadName_opPayload m j v) (by simpa [OpFree] using hK₀) ha
          (by simpa [opE] using hE.2)
    | cfret Ns err w =>
        simp only [cfinE, Kont.plug, Expr.app.injEq] at hE
        exact ha.not_isVal (K'.isVal_of_plug (by rw [hE.2]; exact w.2))
    | _ => simp_all [Kont.plug, hndE, ubindE, ccatchE, cfinE]

/-- Unique decomposition: `K[e] = K′[a]` with `a` a redex and `e` a redex puts `a` at `e`. -/
theorem plug_decomp {μ μ' : Heap} {a a' : Expr} (hh : Head μ a μ' a') (K : Kont)
    (K' : Kont) {e : Expr} {μ₂ μ₂' : Heap} {e' : Expr} (he : Head μ₂ e μ₂' e')
    (h : K.plug e = K'.plug a) : e = a ∧ K' = K := by
  rcases plug_cmp K K' he.not_isVal hh.not_isVal h with ⟨K'', h₁, h₂⟩ | ⟨K'', h₁, h₂⟩
  · obtain rfl := head_nested he K'' h₁ hh
    simp only [Kont.plug] at h₁
    exact ⟨h₁, by rw [h₂, Kont.comp_hole]⟩
  · obtain rfl := head_nested hh K'' h₁ he
    simp only [Kont.plug] at h₁
    exact ⟨h₁.symm, by rw [h₂, Kont.comp_hole]⟩

/-- A redex of a capture rule: a handler, a finaliser or a `ccatch`.  `[spec §19]` -/
def EffRedex (a : Expr) : Prop :=
  (∃ H e, a = hndE H e) ∨ (∃ ND e, a = ubindE ND e) ∨ (∃ e, a = ccatchE e) ∨
    (∃ st e, a = cfinE st e)

/-- A capture redex steps in one way.  `[spec §19]` -/
theorem head_det_eff {μ μ₁ μ₂ : Heap} {a a₁ a₂ : Expr} (h₁ : Head μ a μ₁ a₁) (hE : EffRedex a) :
    ∀ {x : Expr}, Head μ x μ₂ a₂ → a = x → μ₁ = μ₂ ∧ a₁ = a₂ := by
  intro x h₂ hx
  cases h₁ <;> (try (exfalso; rcases hE with ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, h⟩ | ⟨_, _, h⟩ <;>
    simp [hndE, ubindE, ccatchE, cfinE] at h; done))
  all_goals (cases h₂ <;> simp only [hndE, ubindE, ccatchE, cfinE, Expr.app.injEq] at hx ⊢ <;>
    (try (simp at hx; done)))
  all_goals (simp only [true_and, and_true] at hx ⊢)
  all_goals first
    | trivial
    | (obtain ⟨h1, h2⟩ := hx
       first
          | exact absurd h2 (plug_perform_ne_val _ _ _)
          | exact absurd h2.symm (plug_perform_ne_val _ _ _)
          | exact absurd h2 (plug_raise_ne_val _ _ _)
          | exact absurd h2.symm (plug_raise_ne_val _ _ _)
          | exact absurd h2 (plug_perform_ne_raise _ _ _ _)
          | exact absurd h2.symm (plug_perform_ne_raise _ _ _ _)
          | (obtain ⟨rfl, hp⟩ := plug_perform_inj h2
             obtain ⟨rfl, rfl, rfl⟩ := opPayload_inj hp)
          | (obtain ⟨rfl, hp⟩ := plug_raise_inj h2
             first
              | (obtain ⟨rfl, hc⟩ := cancelVal_inj hp
                 first | subst hc | simp at hc)
              | (obtain ⟨rfl, rfl, rfl⟩ := opPayload_inj hp)
              | (have := (opPayload_inj hp).1; simp_all; done))
          | skip
       all_goals first
        | (obtain ⟨-, rfl, rfl⟩ := hndVal_inj h1)
        | (obtain ⟨rfl, rfl⟩ := valPair_inj h1)
        | (obtain ⟨rfl, rfl⟩ := cancelVal_inj (Subtype.ext h1))
        | skip
       all_goals (simp_all; done))
    | (first
          | exact absurd hx (plug_perform_ne_val _ _ _)
          | exact absurd hx.symm (plug_perform_ne_val _ _ _)
          | exact absurd hx (plug_raise_ne_val _ _ _)
          | exact absurd hx.symm (plug_raise_ne_val _ _ _)
          | exact absurd hx (plug_perform_ne_raise _ _ _ _)
          | exact absurd hx.symm (plug_perform_ne_raise _ _ _ _)
          | (obtain ⟨rfl, hp⟩ := plug_perform_inj hx
             obtain ⟨rfl, rfl, rfl⟩ := opPayload_inj hp)
          | (obtain ⟨rfl, hp⟩ := plug_raise_inj hx
             first
              | (obtain ⟨rfl, hc⟩ := cancelVal_inj hp
                 first | subst hc | simp at hc)
              | (obtain ⟨rfl, rfl, rfl⟩ := opPayload_inj hp)
              | (have := (opPayload_inj hp).1; simp_all; done))
          | skip
       all_goals (simp_all; done))

/-- A context with no catcher frame, whose innermost frame is not `[·] v`: a step of `K[e]` is
then a step of `e`.  `[spec §19]` -/
def _root_.BoCa.BoLo.Kont.Plain : Kont → Bool
  | .hole => true
  | .pairL K _ | .pairR _ K | .letpair K _ | .case K _ _ | .seq K _ | .inj₁ K | .inj₂ K => K.Plain
  | .appL K _ => (match K with | .hole => false | _ => true) && K.Plain
  | .appR f K =>
      (match f with
        | .app (.prim .hnd) (.pair _ _) => false
        | .app (.prim .ubind) (.pair _ _) => false
        | .prim .ccatch => false
        | .app (.prim .cfin) (.pair _ _) => false
        | _ => true) && K.Plain

theorem plain_comp_right : ∀ (K K' : Kont), (K.comp K').Plain = true → K'.Plain = true := by
  intro K K' h
  induction K with
  | hole => simpa [Kont.comp] using h
  | appL K v ih =>
      apply ih
      simp only [Kont.comp, Kont.Plain, Bool.and_eq_true] at h
      exact h.2
  | appR f K ih =>
      apply ih
      simp only [Kont.comp, Kont.Plain, Bool.and_eq_true] at h
      exact h.2
  | _ => simp_all [Kont.comp, Kont.Plain]

theorem catcherPos_not_plain {K : Kont} {e : Expr} (h : CatcherPos K e) : K.Plain = false := by
  rcases h with ⟨n, hr, hs, K', rfl⟩ | ⟨N, D, K', rfl⟩ | ⟨K', rfl⟩ | ⟨w, H, q, -, rfl, -⟩ |
    ⟨Ns, err, K', rfl⟩ <;>
    simp [Kont.Plain, Expr.val, Val.prim, hndVal, Val.pair, Val.i32, cancelVal, opPayload]

/-- A step of `K[e]`, `e` holding a redex, is a step of `e` under `K`. -/
theorem step1_plug_inv_active {μ μ₁ μ₀ μ₀' : Heap} {e e₁ a₀ a₀' : Expr} (K K₀ : Kont)
    (he : e = K₀.plug a₀) (h₀ : Head μ₀ a₀ μ₀' a₀')
    (h : Step1 μ (K.plug e) μ₁ e₁) : ∃ e', e₁ = K.plug e' ∧ Step1 μ e μ₁ e' := by
  obtain ⟨K', a, a', hE, rfl, hh⟩ := h
  have hnv : ¬ IsVal e := fun hv => h₀.not_isVal (K₀.isVal_of_plug (he ▸ hv))
  rcases plug_cmp K K' hnv hh.not_isVal hE with ⟨K'', h₁, h₂⟩ | ⟨K'', h₁, h₂⟩
  · subst h₂
    exact ⟨K''.plug a', Kont.plug_comp K K'' a', ⟨K'', a, a', h₁, rfl, hh⟩⟩
  · subst he
    rw [← Kont.plug_comp] at h₁
    obtain ⟨rfl, rfl⟩ := comp_eq_hole (head_nested hh _ h₁ h₀)
    simp only [Kont.comp, Kont.plug] at h₁
    rw [h₂, Kont.comp_hole]
    exact ⟨a', rfl, ⟨.hole, a, a', by simp [Kont.plug, h₁], rfl, hh⟩⟩

/-- A step of `K[e]`, `e` not a value and `K` plain, is a step of `e` under `K`. -/
theorem step1_plug_inv {μ μ₁ : Heap} {e e₁ : Expr} (K : Kont) (hK : K.Plain = true)
    (hnv : ¬ IsVal e)
    (h : Step1 μ (K.plug e) μ₁ e₁) : ∃ e', e₁ = K.plug e' ∧ Step1 μ e μ₁ e' := by
  obtain ⟨K', a, a', hE, rfl, hh⟩ := h
  rcases plug_cmp K K' hnv hh.not_isVal hE with ⟨K'', h₁, h₂⟩ | ⟨K'', h₁, h₂⟩
  · subst h₂
    exact ⟨K''.plug a', Kont.plug_comp K K'' a', ⟨K'', a, a', h₁, rfl, hh⟩⟩
  · by_cases h0 : K'' = .hole
    · subst h0
      simp only [Kont.plug] at h₁
      subst h₁
      rw [h₂, Kont.comp_hole]
      exact ⟨a', rfl, ⟨.hole, a, a', rfl, rfl, hh⟩⟩
    · have hp := plain_comp_right K' K'' (h₂ ▸ hK)
      rw [catcherPos_not_plain (head_plug hh K'' hnv h₁ h0)] at hp
      exact absurd hp (by simp)

/-- A run of `K[e]` to a value, `K` plain, runs `e` to a value first. -/
theorem steps_plug_inv (K : Kont) (hK : K.Plain = true) {μ μ' : Heap} {E E' : Expr}
    (hs : Steps μ E μ' E') :
    ∀ {e : Expr} {w : Val}, E = K.plug e → E' = w.1 →
      ∃ (μm : Heap) (v : Val), Steps μ e μm v.1 ∧ Steps μm (K.plug v.1) μ' w.1 := by
  induction hs with
  | refl μ E =>
      intro e w hE hw
      subst hE
      have hv : IsVal e := K.isVal_of_plug (hw ▸ w.2)
      exact ⟨μ, ⟨e, hv⟩, .refl _ _, hw ▸ .refl _ _⟩
  | more h t ih =>
      intro e w hE hw
      subst hE
      by_cases hv : IsVal e
      · exact ⟨_, ⟨e, hv⟩, .refl _ _, .more h (hw ▸ t)⟩
      · obtain ⟨e', rfl, h'⟩ := step1_plug_inv K hK hv h
        obtain ⟨μm, v, h₁, h₂⟩ := ih rfl hw
        exact ⟨μm, v, .more h' h₁, h₂⟩

/-- A run from a term whose every step is determined continues from the step's result. -/
theorem steps_peel {μ μ' m : Heap} {e e' : Expr} {w : Val} (hs : Steps μ e μ' w.1)
    (hnv : ¬ IsVal e) (hu : ∀ μ₁ e₁, Step1 μ e μ₁ e₁ → μ₁ = m ∧ e₁ = e') :
    Steps m e' μ' w.1 := by
  cases hs with
  | refl => exact absurd w.2 hnv
  | more h t => obtain ⟨rfl, rfl⟩ := hu _ _ h; exact t

/-- A run from a value is empty. -/
theorem steps_from_val {μ μ' : Heap} {v w : Val} (h : Steps μ v.1 μ' w.1) : μ' = μ ∧ w = v := by
  obtain ⟨h₁, h₂⟩ := steps_val_inv h
  exact ⟨h₁, Subtype.ext h₂⟩

/-- The only step of a redex all of whose parts are values is its head step. -/
theorem step1_top {μ μ₁ : Heap} {a e₁ : Expr} (h : Step1 μ a μ₁ e₁)
    (hsub : ∀ (K : Kont) (b : Expr), a = K.plug b → K ≠ .hole → IsVal b) : Head μ a μ₁ e₁ := by
  obtain ⟨K, b, b', rfl, rfl, hh⟩ := h
  by_cases hK : K = .hole
  · subst hK; exact hh
  · exact absurd (hsub K b rfl hK) hh.not_isVal

/-- `(λb) v` steps only to `b[v]`. -/
theorem step1_beta_inv {μ μ₁ : Heap} {b e₁ : Expr} {v : Val}
    (h : Step1 μ (.app (.lam b) v.1) μ₁ e₁) : μ₁ = μ ∧ e₁ = b.subst 0 v := by
  have hh := step1_top h fun K c hE hK => by
    cases K with
    | hole => exact absurd rfl hK
    | appR f K =>
        simp only [Kont.plug, Expr.app.injEq] at hE
        exact K.isVal_of_plug (hE.2 ▸ v.2)
    | appL K u =>
        simp only [Kont.plug, Expr.app.injEq] at hE
        exact K.isVal_of_plug (hE.1 ▸ IsVal.lam)
    | _ => simp [Kont.plug] at hE
  generalize hE : Expr.app (.lam b) v.1 = E at hh
  cases hh with
  | beta b' v' =>
      simp only [Expr.app.injEq, Expr.val, Val.lam, Expr.lam.injEq] at hE
      obtain ⟨rfl, hv⟩ := hE
      have : v = v' := Subtype.ext hv
      subst this; exact ⟨rfl, rfl⟩
  | _ => simp_all [hndE, ubindE, ccatchE, cfinE]

/-- `let (x, y) = v; b` steps only at a pair, to `b[v₁, v₂]`. -/
theorem step1_letpair_inv {μ μ₁ : Heap} {b e₁ : Expr} {v : Val}
    (h : Step1 μ (.letpair v.1 b) μ₁ e₁) :
    ∃ v₁ v₂ : Val, v = .pair v₁ v₂ ∧ μ₁ = μ ∧ e₁ = (b.subst 0 (v₂.shift 1 0)).subst 0 v₁ := by
  have hh := step1_top h fun K c hE hK => by
    cases K with
    | hole => exact absurd rfl hK
    | letpair K u =>
        simp only [Kont.plug, Expr.letpair.injEq] at hE
        exact K.isVal_of_plug (hE.1 ▸ v.2)
    | _ => simp [Kont.plug] at hE
  generalize hE : Expr.letpair v.1 b = E at hh
  cases hh with
  | letpair v₁ v₂ b' =>
      simp only [Expr.letpair.injEq] at hE
      obtain ⟨hv, rfl⟩ := hE
      exact ⟨v₁, v₂, Subtype.ext hv, rfl, rfl⟩
  | _ => simp_all [hndE, ubindE, ccatchE, cfinE]

/-- `f a b` with `f = λλX` and `a`, `b` values: every run continues from `X[a, b]`. -/
theorem steps_app2_lam2 {μ μ' : Heap} {X : Expr} {a b w : Val}
    (hs : Steps μ (BoCa.Programs.app2 (lam2 X) a.1 b.1) μ' w.1) :
    Steps μ ((X.subst 1 (a.shift 1 0)).subst 0 b) μ' w.1 := by
  have hs' := steps_peel (e' := Expr.app (Expr.lam (X.subst 1 (a.shift 1 0))) b.1) (m := μ) hs
    (by simp [BoCa.Programs.app2, lam2])
    (fun μ₁ e₁ h => by
      obtain ⟨e', rfl, h'⟩ := step1_plug_inv_active (.appL .hole b) .hole rfl
        (Head.beta μ (Expr.lam X) a) h
      have := step1_beta_inv (b := Expr.lam X) (v := a) h'
      simp only [Kont.plug]
      simpa [Expr.subst] using this)
  exact steps_peel hs' (by simp) fun μ₁ e₁ h => step1_beta_inv h

/-- A run of `let (x, y) = e; b` to a value: `e` runs to a pair, then `b` runs at its parts. -/
theorem steps_letpair_inv {μ μ' : Heap} {e b : Expr} {w : Val}
    (hs : Steps μ (.letpair e b) μ' w.1) :
    ∃ (μm : Heap) (v₁ v₂ : Val), Steps μ e μm (Val.pair v₁ v₂).1 ∧
      Steps μm ((b.subst 0 (v₂.shift 1 0)).subst 0 v₁) μ' w.1 := by
  obtain ⟨μm, v, h₁, h₂⟩ := steps_plug_inv (.letpair .hole b) (by simp [Kont.Plain]) hs rfl rfl
  simp only [Kont.plug] at h₂
  generalize hE : Expr.letpair v.1 b = E at h₂
  cases h₂ with
  | refl => exact absurd (hE ▸ w.2) (by simp)
  | more h t =>
      subst hE
      obtain ⟨v₁, v₂, rfl, rfl, rfl⟩ := step1_letpair_inv h
      exact ⟨_, v₁, v₂, h₁, t⟩

/-- A run of `(v, e)` to a value runs `e` to a value `u`, and the result is `(v, u)`. -/
theorem steps_pairR_inv {μ μ' : Heap} {v : Val} {e : Expr} {w : Val}
    (hs : Steps μ (.pair v.1 e) μ' w.1) :
    ∃ u : Val, w = .pair v u ∧ ∃ μm : Heap, Steps μ e μm u.1 := by
  obtain ⟨μm, u, h₁, h₂⟩ := steps_plug_inv (.pairR v .hole) (by simp [Kont.Plain]) hs rfl rfl
  obtain ⟨-, rfl⟩ := steps_from_val (v := Val.pair v u) h₂
  exact ⟨u, rfl, μm, h₁⟩

/-- A run of `(e₁, e₂)` to a value runs `e₁`, then `e₂`. -/
theorem steps_pair_inv {μ μ' : Heap} {e₁ e₂ : Expr} {w : Val}
    (hs : Steps μ (.pair e₁ e₂) μ' w.1) :
    ∃ u₁ u₂ : Val, w = .pair u₁ u₂ ∧ ∃ μ₁ μ₂ : Heap, Steps μ e₁ μ₁ u₁.1 ∧ Steps μ₁ e₂ μ₂ u₂.1 := by
  obtain ⟨μm, u₁, h₁, h₂⟩ := steps_plug_inv (.pairL .hole e₂) (by simp [Kont.Plain]) hs rfl rfl
  obtain ⟨u₂, rfl, μ₂, h₃⟩ := steps_pairR_inv (v := u₁) h₂
  exact ⟨u₁, u₂, rfl, μm, μ₂, h₁, h₃⟩

/-- A run of `f a` with `a` a term: `a` runs to a value first. -/
theorem steps_appR_inv {μ μ' : Heap} {f a : Expr} {w : Val}
    (hf : (Kont.appR f .hole).Plain = true)
    (hs : Steps μ (.app f a) μ' w.1) :
    ∃ (μm : Heap) (v : Val), Steps μ a μm v.1 ∧ Steps μm (.app f v.1) μ' w.1 :=
  steps_plug_inv (.appR f .hole) hf hs rfl rfl

end BoCa.Fig16.LogRel.Core

end
