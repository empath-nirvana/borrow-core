import EffModelRel.Unary

/-!
# EffModelRel — the unary relation is preserved by the model and the folds

The operations of every computation type's model keep a computation safe (`opA_safe`, ...), and
so do sequencing (`bindC_safe`), handling (`hnd_safe`) and destructor frames (`addFin_safe`).
Each fold lemma has the side conditions of phase A's typing, as hypotheses on ownership:

- what a frame holds while the computation inside it performs (`F`, the rest of a `to`; `OH`, a
  handler's clauses) may own something only if no operation performed meanwhile may be dropped
  or copied;
- a `using` frame cannot be copied: nothing inside it may be multi-shot.
-/

namespace EffRel

variable {S : Sig}

/-! ## Unfolding -/

theorem CS_F {A : VTy S} {bnd : Bnd S} {O : Own} {t : (CTy.F A).den} :
    CS (.F A) bnd O t ↔ TS bnd (fun O' a => VS A O' a) O t := by simp only [CS]
theorem CS_arr {A : VTy S} {b : Eb} {C : CTy S} {bnd : Bnd S} {O : Own} {f : (CTy.arr A b C).den} :
    CS (.arr A b C) bnd O f ↔
      ∀ Oa a, VS A Oa a → ArgOK bnd Oa → CS C (bnd.join b.req) (O + Oa) (f a) := by simp only [CS]
theorem CS_wth {C D : CTy S} {bnd : Bnd S} {O : Own} {p : (CTy.wth C D).den} :
    CS (.wth C D) bnd O p ↔ CS C bnd O p.1 ∧ CS D bnd O p.2 := by simp only [CS]
theorem CS_pi {e : S.E} {C : CTy S} {bnd : Bnd S} {O : Own} {f : (CTy.pi e C).den} :
    CS (.pi e C) bnd O f ↔ ∀ i, CS C bnd O (f i) := by simp only [CS]

/-! ## Arithmetic -/

theorem Own.add_right_comm (a b c : Own) : a + b + c = a + c + b := by
  rw [Own.add_assoc, Own.add_comm b c, ← Own.add_assoc]

theorem Mode.isLin_of_ge_lin {m q : Mode} (hm : m.IsLin) (h : m.ge q = true) : q.IsLin := by
  obtain ⟨hw, hc⟩ := hm
  cases m; cases q; simp_all [Mode.ge, Mode.IsLin]

theorem Mode.not_isLin_aff {m : Mode} (hm : m.IsLin) (h : m.ge Mode.aff = true) : False := by
  obtain ⟨hw, hc⟩ := hm
  cases m; simp_all [Mode.ge, Mode.aff]

theorem ActOK.frame {g : G} {a : Act g} {O O' : Own} (h : ActOK a O O') (F : Own) :
    ActOK a (O + F) (O' + F) := by
  cases h with
  | out => exact .out
  | free => rw [Own.add_right_comm]; exact .free
  | use => exact .use
  | kill => rw [Own.add_right_comm]; exact .kill
  | rd hr => exact .rd (by simp; omega)
  | wr hr => exact .wr (by simp; omega)

theorem DropOK.append {O O' : Own} {d d' : List Dtor} (h : DropOK O d) (h' : DropOK O' d') :
    DropOK (O + O') (d ++ d') := by
  induction h with
  | nil => simpa using h'
  | free _ ih => rw [Own.add_right_comm]; exact .free ih

theorem DropOK.snoc {O : Own} {d : List Dtor} (h : DropOK O d) (ℓ r : Nat) :
    DropOK (O + Own.one .res r) (d ++ [.free ℓ r]) := by
  have := h.append (DropOK.free (ℓ := ℓ) (r := r) .nil)
  simpa using this

theorem CancelOK.frame {q : Mode} {O F : Own} {d : List Dtor} {m : Mode}
    (h : CancelOK q O d) (hq : m.ge q = true) (hF : F = 0 ∨ m.IsLin) : CancelOK q (O + F) d := by
  rcases hF with rfl | hl
  · simpa using h
  · have := Mode.isLin_of_ge_lin hl hq
    exact ⟨fun hc => absurd hc (by simp [this.2]), fun hw => absurd hw (by simp [this.1])⟩

theorem ArgOK.at {bnd : Bnd S} {F : Own} (h : ArgOK bnd F) (i : Nat) (e : S.E) :
    F = 0 ∨ (bnd i e).IsLin := h.imp id (fun hl => hl i e)

theorem ArgOK.mono {bnd bnd' : Bnd S} {F : Own} (hb : bnd.le bnd') (h : ArgOK bnd' F) : ArgOK bnd F := by
  rcases h with h | hl
  · exact .inl h
  · refine .inr (fun i e => ?_)
    exact Mode.isLin_of_ge_lin (hl i e) (hb i e)

theorem Bnd.le_join (b : Bnd S) (m : Mode) : b.le (b.join m) := fun i e => by
  simp only [Bnd.join, Mode.join, Mode.ge]; cases (b i e).w <;> cases (b i e).c <;> simp

theorem Bnd.join_mono {b b' : Bnd S} (h : b.le b') (m : Mode) : (b.join m).le (b'.join m) := fun i e => by
  have := h i e
  simp only [Bnd.join, Mode.join, Mode.ge] at this ⊢
  cases hw : (b i e).w <;> cases hc : (b i e).c <;> cases hw' : (b' i e).w <;>
    cases hc' : (b' i e).c <;> simp_all

theorem Bnd.le_refl (b : Bnd S) : b.le b := fun i e => by
  simp only [Mode.ge]; cases (b i e).w <;> cases (b i e).c <;> simp

theorem Mode.ge_trans {a b c : Mode} (h₁ : a.ge b = true) (h₂ : b.ge c = true) : a.ge c = true := by
  obtain ⟨aw, ac⟩ := a; obtain ⟨bw, bc⟩ := b; obtain ⟨cw, cc⟩ := c
  cases aw <;> cases ac <;> cases bw <;> cases bc <;> cases cw <;> cases cc <;> simp_all [Mode.ge]

theorem Bnd.le_trans {a b c : Bnd S} (h₁ : a.le b) (h₂ : b.le c) : a.le c :=
  fun i e => Mode.ge_trans (h₂ i e) (h₁ i e)

/-! ## Monotonicity in the bound -/

theorem TS.mono {bnd bnd' : Bnd S} {P : Own → X → Prop} {O : Own} {t : Tree S X}
    (h : TS bnd P O t) (hb : bnd.le bnd') : TS bnd' P O t := by
  induction h with
  | ret hx => exact .ret hx
  | op hq hc _ ih => exact .op (Mode.ge_trans (hb _ _) hq) hc ih
  | ab hq hd => exact .ab (Mode.ge_trans (hb _ _) hq) hd
  | nu _ ih => exact .nu ih
  | nuNew _ ih => exact .nuNew ih
  | nuAcq _ ih => exact .nuAcq ih
  | act ha _ ih => exact .act ha ih

theorem TS.mapP {bnd : Bnd S} {P P' : Own → X → Prop} {O : Own} {t : Tree S X}
    (h : TS bnd P O t) (hP : ∀ O x, P O x → P' O x) : TS bnd P' O t := by
  induction h with
  | ret hx => exact .ret (hP _ _ hx)
  | op hq hc _ ih => exact .op hq hc ih
  | ab hq hd => exact .ab hq hd
  | nu _ ih => exact .nu ih
  | nuNew _ ih => exact .nuNew ih
  | nuAcq _ ih => exact .nuAcq ih
  | act ha _ ih => exact .act ha ih

theorem CS.mono : (C : CTy S) → ∀ {bnd bnd' : Bnd S} {O : Own} {c : C.den},
    CS C bnd O c → bnd.le bnd' → CS C bnd' O c
  | .F _, _, _, _, _, h, hb => CS_F.2 ((CS_F.1 h).mono hb)
  | .arr _ _ C, _, _, _, _, h, hb => CS_arr.2 (fun Oa a ha hA =>
      CS.mono C (CS_arr.1 h Oa a ha (hA.mono hb)) (Bnd.join_mono hb _))
  | .wth C D, _, _, _, _, h, hb => CS_wth.2 ⟨CS.mono C (CS_wth.1 h).1 hb, CS.mono D (CS_wth.1 h).2 hb⟩
  | .pi _ C, _, _, _, _, h, hb => CS_pi.2 (fun i => CS.mono C (CS_pi.1 h i) hb)

/-! ## Every computation type's model keeps a computation safe -/

theorem opA_safe : (C : CTy S) → ∀ {bnd : Bnd S} {O : Own} {i : Nat} {e : S.E} {o : S.O e}
    {v : (S.arg e o).den} {k : (S.res e o).den → C.den} {d : List Dtor},
    (bnd i e).ge (S.q e o) = true → CancelOK (S.q e o) O d → (∀ y, CS C bnd O (k y)) →
    CS C bnd O (C.opA i e o v k d)
  | .F _, _, _, _, _, _, _, _, _, hq, hc, hk => CS_F.2 (.op hq hc (fun y => CS_F.1 (hk y)))
  | .arr _ _ C, bnd, _, i, e, _, _, _, _, hq, hc, hk => CS_arr.2 (fun Oa a ha hA =>
      opA_safe C (Mode.ge_trans (Bnd.le_join bnd _ i e) hq) (hc.frame hq (hA.at i e))
        (fun y => CS_arr.1 (hk y) Oa a ha hA))
  | .wth C D, _, _, _, _, _, _, _, _, hq, hc, hk =>
      CS_wth.2 ⟨opA_safe C hq hc (fun y => (CS_wth.1 (hk y)).1),
        opA_safe D hq hc (fun y => (CS_wth.1 (hk y)).2)⟩
  | .pi _ C, _, _, _, _, _, _, _, _, hq, hc, hk =>
      CS_pi.2 (fun j => opA_safe C hq hc (fun y => CS_pi.1 (hk y) j))

theorem abA_safe : (C : CTy S) → ∀ {bnd : Bnd S} {O : Own} {i : Nat} {e : S.E} {a : S.A e}
    {v : (S.aarg e a).den} {d : List Dtor},
    (bnd i e).ge Mode.aff = true → DropOK O d → CS C bnd O (C.abA i e a v d)
  | .F _, _, _, _, _, _, _, _, hq, hd => CS_F.2 (.ab hq hd)
  | .arr _ _ C, bnd, _, i, e, _, _, _, hq, hd => CS_arr.2 (fun Oa _ _ hA => by
      rcases hA.at i e with rfl | hl
      · exact abA_safe C (Mode.ge_trans (Bnd.le_join bnd _ i e) hq) (by simpa using hd)
      · exact (Mode.not_isLin_aff hl hq).elim)
  | .wth C D, _, _, _, _, _, _, _, hq, hd => CS_wth.2 ⟨abA_safe C hq hd, abA_safe D hq hd⟩
  | .pi _ C, _, _, _, _, _, _, _, hq, hd => CS_pi.2 (fun _ => abA_safe C hq hd)

theorem nuA_safe : (C : CTy S) → ∀ {bnd : Bnd S} {O : Own} {k : Nat → C.den},
    (∀ n, CS C bnd O (k n)) → CS C bnd O (C.nuA k)
  | .F _, _, _, _, hk => CS_F.2 (.nu (fun n => CS_F.1 (hk n)))
  | .arr _ _ C, _, _, _, hk => CS_arr.2 (fun Oa a ha hA =>
      nuA_safe C (fun n => CS_arr.1 (hk n) Oa a ha hA))
  | .wth C D, _, _, _, hk => CS_wth.2 ⟨nuA_safe C (fun n => (CS_wth.1 (hk n)).1),
      nuA_safe D (fun n => (CS_wth.1 (hk n)).2)⟩
  | .pi _ C, _, _, _, hk => CS_pi.2 (fun j => nuA_safe C (fun n => CS_pi.1 (hk n) j))

theorem nuNewA_safe : (C : CTy S) → ∀ {bnd : Bnd S} {O : Own} {s : Nat → GVal}
    {k : Nat → Unit → C.den},
    (∀ n y, CS C bnd (O + Own.one (.cap (s n).1) n) (k n y)) →
    CS C bnd O (C.nuA (fun n => C.actA (.new n (s n)) (k n)))
  | .F _, _, _, _, _, hk => CS_F.2 (.nuNew (fun n y => CS_F.1 (hk n y)))
  | .arr _ _ C, _, _, _, _, hk => CS_arr.2 (fun Oa a ha hA =>
      nuNewA_safe C (fun n y => by
        have := CS_arr.1 (hk n y) Oa a ha hA
        rwa [Own.add_right_comm] at this))
  | .wth C D, _, _, _, _, hk => CS_wth.2 ⟨nuNewA_safe C (fun n y => (CS_wth.1 (hk n y)).1),
      nuNewA_safe D (fun n y => (CS_wth.1 (hk n y)).2)⟩
  | .pi _ C, _, _, _, _, hk => CS_pi.2 (fun j => nuNewA_safe C (fun n y => CS_pi.1 (hk n y) j))

theorem nuAcqA_safe : (C : CTy S) → ∀ {bnd : Bnd S} {O : Own} {ℓ : Nat} {k : Nat → Unit → C.den},
    (∀ n y, CS C bnd (O + Own.one .res n) (k n y)) →
    CS C bnd O (C.nuA (fun n => C.actA (.acq ℓ n) (k n)))
  | .F _, _, _, _, _, hk => CS_F.2 (.nuAcq (fun n y => CS_F.1 (hk n y)))
  | .arr _ _ C, _, _, _, _, hk => CS_arr.2 (fun Oa a ha hA =>
      nuAcqA_safe C (fun n y => by
        have := CS_arr.1 (hk n y) Oa a ha hA
        rwa [Own.add_right_comm] at this))
  | .wth C D, _, _, _, _, hk => CS_wth.2 ⟨nuAcqA_safe C (fun n y => (CS_wth.1 (hk n y)).1),
      nuAcqA_safe D (fun n y => (CS_wth.1 (hk n y)).2)⟩
  | .pi _ C, _, _, _, _, hk => CS_pi.2 (fun j => nuAcqA_safe C (fun n y => CS_pi.1 (hk n y) j))

theorem actA_safe : (C : CTy S) → ∀ {bnd : Bnd S} {O O' : Own} {g : G} {a : Act g}
    {k : g.den → C.den}, ActOK a O O' → (∀ y, CS C bnd O' (k y)) → CS C bnd O (C.actA a k)
  | .F _, _, _, _, _, _, _, ha, hk => CS_F.2 (.act ha (fun y => CS_F.1 (hk y)))
  | .arr _ _ C, _, _, _, _, _, _, ha, hk => CS_arr.2 (fun Oa x hx hA =>
      actA_safe C (ha.frame Oa) (fun y => CS_arr.1 (hk y) Oa x hx hA))
  | .wth C D, _, _, _, _, _, _, ha, hk => CS_wth.2 ⟨actA_safe C ha (fun y => (CS_wth.1 (hk y)).1),
      actA_safe D ha (fun y => (CS_wth.1 (hk y)).2)⟩
  | .pi _ C, _, _, _, _, _, _, ha, hk => CS_pi.2 (fun j => actA_safe C ha (fun y => CS_pi.1 (hk y) j))

theorem dtorsA_safe (C : CTy S) {bnd : Bnd S} {O F : Own} {d : List Dtor} (hd : DropOK O d)
    {x : C.den} (hx : CS C bnd F x) : CS C bnd (O + F) (C.dtorsA d x) := by
  induction hd with
  | nil => simp only [CTy.dtorsA]; simpa using hx
  | free _ ih =>
      simp only [CTy.dtorsA, Dtor.act]
      exact actA_safe C (by rw [Own.add_right_comm]; exact .free) (fun _ => ih)

/-! ## The folds -/

theorem bindC_safe (C : CTy S) {bnd bnd' : Bnd S} {P : Own → X → Prop} {O : Own}
    {t : Tree S X} (h : TS bnd P O t) {F : Own} {f : X → C.den}
    (hf : ∀ O' x, P O' x → CS C bnd' (O' + F) (f x)) (hF : ArgOK bnd F) (hb : bnd.le bnd') :
    CS C bnd' (O + F) (t.bindC C f) := by
  induction h with
  | ret hx => exact hf _ _ hx
  | op hq hc _ ih =>
      exact opA_safe C (Mode.ge_trans (hb _ _) hq) (hc.frame hq (hF.at _ _)) ih
  | ab hq hd =>
      rcases hF.at _ _ with rfl | hl
      · exact abA_safe C (Mode.ge_trans (hb _ _) hq) (by simpa using hd)
      · exact (Mode.not_isLin_aff hl hq).elim
  | nu _ ih => exact nuA_safe C ih
  | nuNew _ ih =>
      exact nuNewA_safe C (fun n y => by have := ih n y; rwa [Own.add_right_comm] at this)
  | nuAcq _ ih =>
      exact nuAcqA_safe C (fun n y => by have := ih n y; rwa [Own.add_right_comm] at this)
  | act ha _ ih => exact actA_safe C (ha.frame F) ih

/-- A `using` frame: free the resource on return, add its destructor to every continuation.
Nothing inside may be copied (`hc`). -/
theorem addFin_safe {bnd : Bnd S} {P : Own → X → Prop} {O : Own} {t : Tree S X}
    (h : TS bnd P O t) (hc : ∀ i e, (bnd i e).c = false) (ℓ r : Nat) :
    TS bnd P (O + Own.one .res r) (t.addFin ℓ r) := by
  induction h with
  | ret hx => exact .act .free (fun _ => .ret hx)
  | @op O i e o v k d hq hcan _ ih =>
      refine .op hq ⟨fun hqc => ?_, fun hqw => (hcan.2 hqw).snoc ℓ r⟩ ih
      have := Mode.ge_trans hq (show (S.q e o).ge ⟨false, true⟩ = true by simp [Mode.ge, hqc])
      simp [Mode.ge, hc i e] at this
  | ab hq hd => exact .ab hq (hd.snoc ℓ r)
  | nu _ ih => exact .nu ih
  | nuNew _ ih => exact .nuNew (fun n y => by have := ih n y; rwa [Own.add_right_comm] at this)
  | nuAcq _ ih => exact .nuAcq (fun n y => by have := ih n y; rwa [Own.add_right_comm] at this)
  | act ha _ ih => exact .act (ha.frame _) ih

/-! ## Handling -/

theorem dtors_safe {bnd : Bnd S} {P : Own → X → Prop} {O F : Own} {d : List Dtor}
    (hd : DropOK O d) {t : Tree S X} (ht : TS bnd P F t) : TS bnd P (O + F) (Tree.dtors d t) := by
  induction hd with
  | nil => simpa [Tree.dtors] using ht
  | free _ ih => exact .act (by rw [Own.add_right_comm]; exact .free) (fun _ => ih)

theorem dtorsT_safe {bnd : Bnd S} {O : Own} {d : List Dtor} (hd : DropOK O d) :
    TS bnd (fun O' (_ : Unit) => O' = 0) O (dtorsT d) := by
  have := dtors_safe hd (F := 0) (TS.ret (bnd := bnd) (P := fun O' (_ : Unit) => O' = 0) (x := ()) rfl)
  simpa [dtorsT] using this

theorem Bnd.const_join_lin (m : Mode) : (Bnd.const (S := S) Mode.lin).join m = Bnd.const m := by
  funext i e; simp [Bnd.const, Bnd.join, Mode.join, Mode.lin]

/-- The continuation a clause receives owns what the captured continuation owns. -/
theorem mkK_safe {q : Mode} {bk : Eb} {r : G} {C : CTy S} {Oκ : Own} {k : r.den → C.den}
    {d : List Dtor} (hk : ∀ y, CS C (Bnd.const bk.req) Oκ (k y))
    (hd : q.w = true → DropOK Oκ d) (hc : q.c = true → Oκ = 0) :
    VS (kty q bk r C) Oκ (mkK q.w q bk r C k (dtorsT d)) := by
  have harr : CS (.arr (.g r) bk C) (Bnd.const Mode.lin) Oκ k := CS_arr.2 (fun Oa y hy _ => by
    have : Oa = 0 := by simpa [VS] using hy
    subst this; rw [Own.add_zero, Bnd.const_join_lin]; exact hk y)
  obtain ⟨w, c⟩ := q
  cases w with
  | true =>
      simp only [kty, ktyB, mkK, VS]
      refine ⟨fun h => hc (by cases c <;> simp_all [Mode.unr, Mode.lin]), CS_wth.2 ⟨harr, ?_⟩⟩
      exact CS_F.2 ((dtorsT_safe (hd rfl)).mapP (fun _ _ h => by simp [VS, h]))
  | false =>
      simp only [kty, ktyB, mkK, VS]
      exact ⟨fun h => hc (by simpa using h), harr⟩

/-- **Handling keeps a computation safe.** The return and abortive clauses are alternatives and
own `OH`; resuming clauses own nothing but the continuation. `OH` may be nonzero only if every
resuming operation is linear (`hOH`: otherwise the return clause may never run, or run twice)
and every operation the handler passes on is linear (`hfwd`: otherwise the frame holding the
clauses may be dropped or copied). -/
theorem hnd_safe (C : CTy S) {bndB bnd' : Bnd S} {P : Own → X → Prop} {O : Own} {t : Tree S X}
    (h : TS bndB P O t) {i : Nat} {e : S.E} {bk : Eb} {hr : X → C.den}
    {hop : (o : S.O e) → (S.arg e o).den → ((S.res e o).den → C.den) → List Dtor → C.den}
    {hab : (a : S.A e) → (S.aarg e a).den → C.den} {OH : Own}
    (hR : ∀ O' x, P O' x → CS C bnd' (O' + OH) (hr x))
    (hO : ∀ o v Oκ (k : (S.res e o).den → C.den) d,
      VS (kty (S.q e o) bk (S.res e o) C) Oκ (mkK (S.q e o).w (S.q e o) bk (S.res e o) C k (dtorsT d)) →
      CS C bnd' Oκ (hop o v k d))
    (hA : ∀ a v, CS C bnd' OH (hab a v))
    (hOH : OH = 0 ∨ ∀ o, (S.q e o).IsLin)
    (hfwd : OH = 0 ∨ ∀ j e', ¬ (j = i ∧ e' = e) → (bndB j e').IsLin)
    (hfw' : ∀ j e', ¬ (j = i ∧ e' = e) → (bnd' j e').ge (bndB j e') = true)
    (hk : bnd'.le (Bnd.const bk.req)) :
    CS C bnd' (O + OH) (t.hnd C i e hr hop hab) := by
  induction h with
  | ret hx => exact hR _ _ hx
  | @op O j e' o v k d hq hc _ ih =>
      simp only [Tree.hnd]
      have fwd : ¬ (j = i ∧ e' = e) → CS C bnd' (O + OH)
          (C.opA j e' o v (fun y => (k y).hnd C i e hr hop hab) d) := fun hne =>
        opA_safe C (Mode.ge_trans (hfw' j e' hne) hq)
          (hc.frame hq (hfwd.imp id (fun hl => hl j e' hne))) ih
      by_cases hji : j = i
      · rw [if_pos hji]
        by_cases he : e' = e
        · subst he; subst hji
          rw [catchOp_self]
          apply hO
          apply mkK_safe
          · intro y; exact CS.mono C (ih y) hk
          · intro hw
            rcases hOH with h0 | hl
            · rw [h0, Own.add_zero]; exact hc.2 hw
            · exact absurd hw (by simp [(hl o).1])
          · intro hcc
            have hO0 := (hc.1 hcc).1
            rcases hOH with h0 | hl
            · rw [hO0, h0]; rfl
            · exact absurd hcc (by simp [(hl o).2])
        · rw [catchOp_ne he]; exact fwd (fun h => he h.2)
      · rw [if_neg hji]; exact fwd (fun h => hji h.1)
  | @ab O j e' a v d hq hd =>
      simp only [Tree.hnd]
      have fwd : ¬ (j = i ∧ e' = e) → CS C bnd' (O + OH) (C.abA j e' a v d) := fun hne => by
        rcases hfwd with h0 | hl
        · rw [h0, Own.add_zero]; exact abA_safe C (Mode.ge_trans (hfw' j e' hne) hq) hd
        · exact (Mode.not_isLin_aff (hl j e' hne) hq).elim
      by_cases hji : j = i
      · rw [if_pos hji]
        by_cases he : e' = e
        · subst he; rw [catchAb_self]; exact dtorsA_safe C hd (hA a v)
        · rw [catchAb_ne he]; exact fwd (fun h => he h.2)
      · rw [if_neg hji]; exact fwd (fun h => hji h.1)
  | nu _ ih => exact nuA_safe C ih
  | nuNew _ ih =>
      exact nuNewA_safe C (fun n y => by have := ih n y; rwa [Own.add_right_comm] at this)
  | nuAcq _ ih =>
      exact nuAcqA_safe C (fun n y => by have := ih n y; rwa [Own.add_right_comm] at this)
  | act ha _ ih => exact actA_safe C (ha.frame OH) ih

end EffRel
