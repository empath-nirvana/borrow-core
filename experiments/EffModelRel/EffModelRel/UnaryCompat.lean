import EffModelRel.Unary

/-!
# EffModelRel — the unary relation is preserved by the model and the folds

The operations of every computation type's model keep a computation safe (`opA_safe`, ...), and
so do sequencing (`bindC_safe`), handling (`hnd_safe`), lending (`runL_safe`) and destructor
frames (`addFin_safe`). Each fold lemma has the side conditions of the typing, as hypotheses on
ownership and permissions:

- what a frame holds while the computation inside it performs (`F`, the rest of a `to`; `OH`, a
  handler's clauses; the lent capability, a `run` frame) may own something only if no operation
  performed meanwhile may be dropped or copied;
- a `using` frame cannot be copied: nothing inside it may be multi-shot;
- a frame removes the instance it answers from the permissions it passes out.
-/

namespace EffRel

variable {S : Sig}

/-! ## Unfolding -/

theorem CS_F {A : VTy S} {θ : LEnv S} {ok : Ok S} {O : Own} {t : (CTy.F A).den} :
    CS (.F A) θ ok O t ↔ TS ok (fun O' a => VS A θ O' a) O t := by simp only [CS]
theorem CS_arr {A : VTy S} {b : Rw} {C : CTy S} {θ : LEnv S} {ok : Ok S} {O : Own}
    {f : (CTy.arr A b C).den} :
    CS (.arr A b C) θ ok O f ↔
      ∀ Oa a, VS A θ Oa a → ArgOK ok Oa → CS C θ (ok.union (b.ok θ)) (O + Oa) (f a) := by
  simp only [CS]
theorem CS_wth {C D : CTy S} {θ : LEnv S} {ok : Ok S} {O : Own} {p : (CTy.wth C D).den} :
    CS (.wth C D) θ ok O p ↔ CS C θ ok O p.1 ∧ CS D θ ok O p.2 := by simp only [CS]
theorem CS_pi {e : S.E} {C : CTy S} {θ : LEnv S} {ok : Ok S} {O : Own} {f : (CTy.pi e C).den} :
    CS (.pi e C) θ ok O f ↔ ∀ i, CS C θ (ok.add i e) O (f i) := by simp only [CS]

/-! ## Arithmetic -/

theorem Own.add_right_comm (a b c : Own) : a + b + c = a + c + b := by
  rw [Own.add_assoc, Own.add_comm b c, ← Own.add_assoc]

theorem Mode.isLin_of_ge_lin {m q : Mode} (hm : m.IsLin) (h : m.ge q = true) : q.IsLin := by
  obtain ⟨hw, hc⟩ := hm
  cases m; cases q; simp_all [Mode.ge, Mode.IsLin]

theorem Mode.not_isLin_aff {m : Mode} (hm : m.IsLin) (h : m.ge Mode.aff = true) : False := by
  obtain ⟨hw, hc⟩ := hm
  cases m; simp_all [Mode.ge, Mode.aff]

theorem Mode.ge_trans {a b c : Mode} (h₁ : a.ge b = true) (h₂ : b.ge c = true) : a.ge c = true := by
  obtain ⟨aw, ac⟩ := a; obtain ⟨bw, bc⟩ := b; obtain ⟨cw, cc⟩ := c
  cases aw <;> cases ac <;> cases bw <;> cases bc <;> cases cw <;> cases cc <;> simp_all [Mode.ge]

/-- An operation's qualifier is linear when its effect's bound is. -/
theorem q_isLin {e : S.E} (o : S.O e) (h : (S.bnd e).IsLin) : (S.q e o).IsLin :=
  Mode.isLin_of_ge_lin h (S.bnd_q e o)

theorem q_noC {e : S.E} (o : S.O e) (h : (S.bnd e).c = false) : (S.q e o).c = false := by
  have := S.bnd_q e o
  revert this h; obtain ⟨w, c⟩ := S.bnd e; obtain ⟨w', c'⟩ := S.q e o
  cases c <;> cases c' <;> cases w <;> cases w' <;> simp [Mode.ge]

/-- An effect that may abort has a bound that is not linear. -/
theorem ab_not_lin {e : S.E} (a : S.A e) (h : (S.bnd e).IsLin) : False :=
  Mode.not_isLin_aff h (S.bnd_ab e a)

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

theorem CancelOK.frame {q : Mode} {O F : Own} {d : List Dtor}
    (h : CancelOK q O d) (hF : F = 0 ∨ q.IsLin) : CancelOK q (O + F) d := by
  rcases hF with rfl | hl
  · simpa using h
  · exact ⟨fun hc => absurd hc (by simp [hl.2]), fun hw => absurd hw (by simp [hl.1])⟩

theorem CancelOK.lin {q : Mode} {O : Own} {d : List Dtor} (hl : q.IsLin) : CancelOK q O d :=
  ⟨fun hc => absurd hc (by simp [hl.2]), fun hw => absurd hw (by simp [hl.1])⟩

theorem ArgOK.at {ok : Ok S} {F : Own} (h : ArgOK ok F) {i : Nat} {e : S.E} (hok : ok i e)
    (o : S.O e) : F = 0 ∨ (S.q e o).IsLin :=
  h.imp id (fun hl => q_isLin o (hl i e hok))

theorem ArgOK.mono {ok ok' : Ok S} {F : Own} (hb : ok.le ok') (h : ArgOK ok' F) : ArgOK ok F :=
  h.imp id (fun hl => hl.mono hb)

theorem ArgOK.bot (F : Own) : ArgOK (Ok.bot (S := S)) F := .inr Ok.bot_isLin

/-! ## Monotonicity in the permissions -/

theorem TS.mono {ok ok' : Ok S} {P : Own → X → Prop} {O : Own} {t : Tree S X}
    (h : TS ok P O t) (hb : ok.le ok') : TS ok' P O t := by
  induction h with
  | ret hx => exact .ret hx
  | op hq hc _ ih => exact .op (hb _ _ hq) hc ih
  | ab hq hd => exact .ab (hb _ _ hq) hd
  | nu _ ih => exact .nu ih
  | nuNew _ ih => exact .nuNew ih
  | nuAcq _ ih => exact .nuAcq ih
  | act ha _ ih => exact .act ha ih

theorem TS.mapP {ok : Ok S} {P P' : Own → X → Prop} {O : Own} {t : Tree S X}
    (h : TS ok P O t) (hP : ∀ O x, P O x → P' O x) : TS ok P' O t := by
  induction h with
  | ret hx => exact .ret (hP _ _ hx)
  | op hq hc _ ih => exact .op hq hc ih
  | ab hq hd => exact .ab hq hd
  | nu _ ih => exact .nu ih
  | nuNew _ ih => exact .nuNew ih
  | nuAcq _ ih => exact .nuAcq ih
  | act ha _ ih => exact .act ha ih

theorem CS.mono : (C : CTy S) → ∀ {θ : LEnv S} {ok ok' : Ok S} {O : Own} {c : C.den},
    CS C θ ok O c → ok.le ok' → CS C θ ok' O c
  | .F _, _, _, _, _, _, h, hb => CS_F.2 ((CS_F.1 h).mono hb)
  | .arr _ _ C, _, _, _, _, _, h, hb => CS_arr.2 (fun Oa a ha hA =>
      CS.mono C (CS_arr.1 h Oa a ha (hA.mono hb)) (Ok.union_mono hb (Ok.le_refl _)))
  | .wth C D, _, _, _, _, _, h, hb =>
      CS_wth.2 ⟨CS.mono C (CS_wth.1 h).1 hb, CS.mono D (CS_wth.1 h).2 hb⟩
  | .pi _ C, _, _, _, _, _, h, hb => CS_pi.2 (fun i => CS.mono C (CS_pi.1 h i) (Ok.add_mono hb _ _))

/-! ## Every computation type's model keeps a computation safe -/

theorem opA_safe : (C : CTy S) → ∀ {θ : LEnv S} {ok : Ok S} {O : Own} {i : Nat} {e : S.E}
    {o : S.O e} {v : (S.arg e o).den} {k : (S.res e o).den → C.den} {d : List Dtor},
    ok i e → CancelOK (S.q e o) O d → (∀ y, CS C θ ok O (k y)) →
    CS C θ ok O (C.opA i e o v k d)
  | .F _, _, _, _, _, _, _, _, _, _, hq, hc, hk => CS_F.2 (.op hq hc (fun y => CS_F.1 (hk y)))
  | .arr _ _ C, _, _, _, _, _, o, _, _, _, hq, hc, hk => CS_arr.2 (fun Oa a ha hA =>
      opA_safe C (Ok.le_union_l _ _ _ _ hq) (hc.frame (hA.at hq o))
        (fun y => CS_arr.1 (hk y) Oa a ha hA))
  | .wth C D, _, _, _, _, _, _, _, _, _, hq, hc, hk =>
      CS_wth.2 ⟨opA_safe C hq hc (fun y => (CS_wth.1 (hk y)).1),
        opA_safe D hq hc (fun y => (CS_wth.1 (hk y)).2)⟩
  | .pi _ C, _, _, _, _, _, _, _, _, _, hq, hc, hk =>
      CS_pi.2 (fun j => opA_safe C (Ok.le_add _ _ _ _ _ hq) hc (fun y => CS_pi.1 (hk y) j))

theorem abA_safe : (C : CTy S) → ∀ {θ : LEnv S} {ok : Ok S} {O : Own} {i : Nat} {e : S.E}
    {a : S.A e} {v : (S.aarg e a).den} {d : List Dtor},
    ok i e → DropOK O d → CS C θ ok O (C.abA i e a v d)
  | .F _, _, _, _, _, _, _, _, _, hq, hd => CS_F.2 (.ab hq hd)
  | .arr _ _ C, _, _, _, i, e, a, _, _, hq, hd => CS_arr.2 (fun Oa _ _ hA => by
      rcases hA with rfl | hl
      · exact abA_safe C (Ok.le_union_l _ _ _ _ hq) (by simpa using hd)
      · exact (ab_not_lin a (hl i e hq)).elim)
  | .wth C D, _, _, _, _, _, _, _, _, hq, hd => CS_wth.2 ⟨abA_safe C hq hd, abA_safe D hq hd⟩
  | .pi _ C, _, _, _, _, _, _, _, _, hq, hd =>
      CS_pi.2 (fun _ => abA_safe C (Ok.le_add _ _ _ _ _ hq) hd)

theorem nuA_safe : (C : CTy S) → ∀ {θ : LEnv S} {ok : Ok S} {O : Own} {k : Nat → C.den},
    (∀ n, CS C θ ok O (k n)) → CS C θ ok O (C.nuA k)
  | .F _, _, _, _, _, hk => CS_F.2 (.nu (fun n => CS_F.1 (hk n)))
  | .arr _ _ C, _, _, _, _, hk => CS_arr.2 (fun Oa a ha hA =>
      nuA_safe C (fun n => CS_arr.1 (hk n) Oa a ha hA))
  | .wth C D, _, _, _, _, hk => CS_wth.2 ⟨nuA_safe C (fun n => (CS_wth.1 (hk n)).1),
      nuA_safe D (fun n => (CS_wth.1 (hk n)).2)⟩
  | .pi _ C, _, _, _, _, hk => CS_pi.2 (fun j => nuA_safe C (fun n => CS_pi.1 (hk n) j))

theorem nuNewA_safe : (C : CTy S) → ∀ {θ : LEnv S} {ok : Ok S} {O : Own} {s : Nat → GVal}
    {k : Nat → Unit → C.den},
    (∀ n y, CS C θ ok (O + Own.one (.cap (s n).1) n) (k n y)) →
    CS C θ ok O (C.nuA (fun n => C.actA (.new n (s n)) (k n)))
  | .F _, _, _, _, _, _, hk => CS_F.2 (.nuNew (fun n y => CS_F.1 (hk n y)))
  | .arr _ _ C, _, _, _, _, _, hk => CS_arr.2 (fun Oa a ha hA =>
      nuNewA_safe C (fun n y => by
        have := CS_arr.1 (hk n y) Oa a ha hA
        rwa [Own.add_right_comm] at this))
  | .wth C D, _, _, _, _, _, hk => CS_wth.2 ⟨nuNewA_safe C (fun n y => (CS_wth.1 (hk n y)).1),
      nuNewA_safe D (fun n y => (CS_wth.1 (hk n y)).2)⟩
  | .pi _ C, _, _, _, _, _, hk => CS_pi.2 (fun j => nuNewA_safe C (fun n y => CS_pi.1 (hk n y) j))

theorem nuAcqA_safe : (C : CTy S) → ∀ {θ : LEnv S} {ok : Ok S} {O : Own} {ℓ : Nat}
    {k : Nat → Unit → C.den},
    (∀ n y, CS C θ ok (O + Own.one .res n) (k n y)) →
    CS C θ ok O (C.nuA (fun n => C.actA (.acq ℓ n) (k n)))
  | .F _, _, _, _, _, _, hk => CS_F.2 (.nuAcq (fun n y => CS_F.1 (hk n y)))
  | .arr _ _ C, _, _, _, _, _, hk => CS_arr.2 (fun Oa a ha hA =>
      nuAcqA_safe C (fun n y => by
        have := CS_arr.1 (hk n y) Oa a ha hA
        rwa [Own.add_right_comm] at this))
  | .wth C D, _, _, _, _, _, hk => CS_wth.2 ⟨nuAcqA_safe C (fun n y => (CS_wth.1 (hk n y)).1),
      nuAcqA_safe D (fun n y => (CS_wth.1 (hk n y)).2)⟩
  | .pi _ C, _, _, _, _, _, hk => CS_pi.2 (fun j => nuAcqA_safe C (fun n y => CS_pi.1 (hk n y) j))

theorem actA_safe : (C : CTy S) → ∀ {θ : LEnv S} {ok : Ok S} {O O' : Own} {g : G} {a : Act g}
    {k : g.den → C.den}, ActOK a O O' → (∀ y, CS C θ ok O' (k y)) → CS C θ ok O (C.actA a k)
  | .F _, _, _, _, _, _, _, _, ha, hk => CS_F.2 (.act ha (fun y => CS_F.1 (hk y)))
  | .arr _ _ C, _, _, _, _, _, _, _, ha, hk => CS_arr.2 (fun Oa x hx hA =>
      actA_safe C (ha.frame Oa) (fun y => CS_arr.1 (hk y) Oa x hx hA))
  | .wth C D, _, _, _, _, _, _, _, ha, hk =>
      CS_wth.2 ⟨actA_safe C ha (fun y => (CS_wth.1 (hk y)).1),
        actA_safe D ha (fun y => (CS_wth.1 (hk y)).2)⟩
  | .pi _ C, _, _, _, _, _, _, _, ha, hk =>
      CS_pi.2 (fun j => actA_safe C ha (fun y => CS_pi.1 (hk y) j))

theorem dtorsA_safe (C : CTy S) {θ : LEnv S} {ok : Ok S} {O F : Own} {d : List Dtor}
    (hd : DropOK O d) {x : C.den} (hx : CS C θ ok F x) : CS C θ ok (O + F) (C.dtorsA d x) := by
  induction hd with
  | nil => simp only [CTy.dtorsA]; simpa using hx
  | free _ ih =>
      simp only [CTy.dtorsA, Dtor.act]
      exact actA_safe C (by rw [Own.add_right_comm]; exact .free) (fun _ => ih)

/-! ## The folds -/

theorem bindC_safe (C : CTy S) {θ : LEnv S} {ok ok' : Ok S} {P : Own → X → Prop} {O : Own}
    {t : Tree S X} (h : TS ok P O t) {F : Own} {f : X → C.den}
    (hf : ∀ O' x, P O' x → CS C θ ok' (O' + F) (f x)) (hF : ArgOK ok F) (hb : ok.le ok') :
    CS C θ ok' (O + F) (t.bindC C f) := by
  induction h with
  | ret hx => exact hf _ _ hx
  | @op O i e o v k d hq hc _ ih => exact opA_safe C (hb _ _ hq) (hc.frame (hF.at hq o)) ih
  | @ab O i e a v d hq hd =>
      rcases hF with rfl | hl
      · exact abA_safe C (hb _ _ hq) (by simpa using hd)
      · exact (ab_not_lin a (hl i e hq)).elim
  | nu _ ih => exact nuA_safe C ih
  | nuNew _ ih =>
      exact nuNewA_safe C (fun n y => by have := ih n y; rwa [Own.add_right_comm] at this)
  | nuAcq _ ih =>
      exact nuAcqA_safe C (fun n y => by have := ih n y; rwa [Own.add_right_comm] at this)
  | act ha _ ih => exact actA_safe C (ha.frame F) ih

/-- Sequencing on trees, with a frame `F` held across. -/
theorem TS.bind {ok ok' : Ok S} {P : Own → X → Prop} {Q : Own → Y → Prop} {O : Own}
    {t : Tree S X} (h : TS ok P O t) {F : Own} {f : X → Tree S Y}
    (hf : ∀ O' x, P O' x → TS ok' Q (O' + F) (f x)) (hF : ArgOK ok F) (hb : ok.le ok') :
    TS ok' Q (O + F) (t.bind f) := by
  induction h with
  | ret hx => exact hf _ _ hx
  | @op O i e o v k d hq hc _ ih => exact .op (hb _ _ hq) (hc.frame (hF.at hq o)) ih
  | @ab O i e a v d hq hd =>
      rcases hF with rfl | hl
      · exact .ab (hb _ _ hq) (by simpa using hd)
      · exact (ab_not_lin a (hl i e hq)).elim
  | nu _ ih => exact .nu ih
  | nuNew _ ih => exact .nuNew (fun n y => by have := ih n y; rwa [Own.add_right_comm] at this)
  | nuAcq _ ih => exact .nuAcq (fun n y => by have := ih n y; rwa [Own.add_right_comm] at this)
  | act ha _ ih => exact .act (ha.frame F) ih

/-- A `using` frame: answer `use` on its instance in place, free the resource on return, add its
destructor to every continuation. Nothing inside may be copied (`hc`); the frame's instance
leaves the permissions. -/
theorem addFin_safe {ok : Ok S} {P : Own → X → Prop} {O : Own} {t : Tree S X}
    (h : TS ok P O t) {r : Nat}
    (hc : ∀ j e, ¬ (j = r ∧ e = S.Res) → ok j e → (S.bnd e).c = false) (ℓ : Nat) :
    TS (ok.rem r S.Res) P (O + Own.one .res r) (t.addFin ℓ r) := by
  induction h with
  | ret hx => exact .act .free (fun _ => .ret hx)
  | @op O i e o v k d hq hcan _ ih =>
      simp only [Tree.addFin]
      by_cases hh : i = r ∧ e = S.Res
      · rw [dif_pos hh]; exact .act .use (fun _ => ih _)
      · rw [dif_neg hh]
        refine .op ⟨hq, hh⟩ ⟨fun hqc => ?_, fun hqw => (hcan.2 hqw).snoc ℓ r⟩ ih
        exact absurd hqc (by simp [q_noC o (hc i e hh hq)])
  | @ab O i e a v d hq hd =>
      refine .ab ⟨hq, fun hh => ?_⟩ (hd.snoc ℓ r)
      obtain ⟨-, rfl⟩ := hh
      exact S.res_noab a
  | nu _ ih => exact .nu ih
  | nuNew _ ih => exact .nuNew (fun n y => by have := ih n y; rwa [Own.add_right_comm] at this)
  | nuAcq _ ih => exact .nuAcq (fun n y => by have := ih n y; rwa [Own.add_right_comm] at this)
  | act ha _ ih => exact .act (ha.frame _) ih

/-! ## Handling -/

theorem dtors_safe {ok : Ok S} {P : Own → X → Prop} {O F : Own} {d : List Dtor}
    (hd : DropOK O d) {t : Tree S X} (ht : TS ok P F t) : TS ok P (O + F) (Tree.dtors d t) := by
  induction hd with
  | nil => simpa [Tree.dtors] using ht
  | free _ ih => exact .act (by rw [Own.add_right_comm]; exact .free) (fun _ => ih)

theorem dtorsT_safe {ok : Ok S} {O : Own} {d : List Dtor} (hd : DropOK O d) :
    TS ok (fun O' (_ : Unit) => O' = 0) O (dtorsT d) := by
  have := dtors_safe hd (F := 0) (TS.ret (ok := ok) (P := fun O' (_ : Unit) => O' = 0) (x := ()) rfl)
  simpa [dtorsT] using this

theorem Rw.ok_nil (θ : LEnv S) : Rw.nil.ok θ = Ok.bot := by
  funext i e; simp [Rw.ok, Rw.nil, Ok.bot]

/-- The continuation a clause receives owns what the captured continuation owns. -/
theorem mkK_safe {q : Mode} {bk : Rw} {r : G} {C : CTy S} {θ : LEnv S} {Oκ : Own}
    {k : r.den → C.den} {d : List Dtor} (hk : ∀ y, CS C θ (bk.ok θ) Oκ (k y))
    (hd : q.w = true → DropOK Oκ d) (hc : q.c = true → Oκ = 0) :
    VS (kty q bk r C) θ Oκ (mkK q.w q bk r C k (dtorsT d)) := by
  have harr : CS (.arr (.g r) bk C) θ (Rw.nil.ok θ) Oκ k := CS_arr.2 (fun Oa y hy _ => by
    have : Oa = 0 := by simpa [VS] using hy
    subst this; rw [Own.add_zero]
    exact CS.mono C (hk y) (Ok.le_union_r _ _))
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
clauses may be dropped or copied). The handler passes on every permission of the body but its
own instance (`hfw'`), and its continuations perform within `bk` (`hk`). -/
theorem hnd_safe (C : CTy S) {θ : LEnv S} {okB ok' : Ok S} {P : Own → X → Prop} {O : Own}
    {t : Tree S X} (h : TS okB P O t) {i : Nat} {e : S.E} {bk : Rw} {hr : X → C.den}
    {hop : (o : S.O e) → (S.arg e o).den → ((S.res e o).den → C.den) → List Dtor → C.den}
    {hab : (a : S.A e) → (S.aarg e a).den → C.den} {OH : Own}
    (hR : ∀ O' x, P O' x → CS C θ ok' (O' + OH) (hr x))
    (hO : ∀ o v Oκ (k : (S.res e o).den → C.den) d,
      VS (kty (S.q e o) bk (S.res e o) C) θ Oκ
        (mkK (S.q e o).w (S.q e o) bk (S.res e o) C k (dtorsT d)) →
      CS C θ ok' Oκ (hop o v k d))
    (hA : ∀ a v, CS C θ ok' OH (hab a v))
    (hOH : OH = 0 ∨ ∀ o, (S.q e o).IsLin)
    (hfwd : OH = 0 ∨ ∀ j e', ¬ (j = i ∧ e' = e) → okB j e' → (S.bnd e').IsLin)
    (hfw' : ∀ j e', ¬ (j = i ∧ e' = e) → okB j e' → ok' j e')
    (hk : ok'.le (bk.ok θ)) :
    CS C θ ok' (O + OH) (t.hnd C i e hr hop hab) := by
  induction h with
  | ret hx => exact hR _ _ hx
  | @op O j e' o v k d hq hc _ ih =>
      simp only [Tree.hnd]
      have fwd : ¬ (j = i ∧ e' = e) → CS C θ ok' (O + OH)
          (C.opA j e' o v (fun y => (k y).hnd C i e hr hop hab) d) := fun hne =>
        opA_safe C (hfw' j e' hne hq)
          (hc.frame (hfwd.imp id (fun hl => q_isLin o (hl j e' hne hq)))) ih
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
      have fwd : ¬ (j = i ∧ e' = e) → CS C θ ok' (O + OH) (C.abA j e' a v d) := fun hne => by
        rcases hfwd with h0 | hl
        · rw [h0, Own.add_zero]; exact abA_safe C (hfw' j e' hne hq) hd
        · exact (ab_not_lin a (hl j e' hne hq)).elim
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

/-! ## Lending -/

/-- An error code at an operation that is not fallible does not exist. -/
theorem errG_w {e : S.E} {o : S.O e} (n : (S.errG e o).den) : (S.q e o).w = true := by
  unfold Sig.errG at n
  revert n; cases (S.q e o).w
  · intro n; exact (n : Empty).elim
  · intro _; rfl

/-- **A lend keeps a computation safe.** The `run` frame holds the capability's token `Oc` while
the body runs: every operation it passes on must be linear (`hlin`, the `[lend]` premise), so the
token travels with a continuation that is resumed exactly once. An operation on the lent instance
is answered in place by a co-operation, which performs nothing; on a co-operation's failure, which
only a fallible operation admits, the client's continuation is cancelled (its destructors free
what it owns) and the token comes back with the error. The capability's effect has no abortive
operation (`hnoab`), and the frame's instance leaves the permissions. -/
theorem runL_safe {okB : Ok S} {P : Own → X → Prop} {Q : Own → (X ⊕ Int) → Prop} {O : Own}
    {t : Tree S X} (h : TS okB P O t) {i : Nat} {e : S.E} {c : Nat} {sg : G} {co : CoSem S e sg}
    (hco : ∀ o a st, TS Ok.bot (fun O' _ => O' = 0) 0 (co o a st)) (hnoab : S.A e → False)
    (hlin : ∀ j e', ¬ (j = i ∧ e' = e) → okB j e' → (S.bnd e').IsLin)
    (hret : ∀ O x, P O x → Q (O + Own.one (.cap sg) c) (.inl x))
    (herr : ∀ n, Q (Own.one (.cap sg) c) (.inr n)) :
    ∀ s, TS (okB.rem i e) Q (O + Own.one (.cap sg) c) (t.runL i e c sg co s) := by
  have hcell : ∀ O : Own, (O + Own.one (.cap sg) c) (.cap sg) c ≠ 0 := by
    intro O; simp [Own.one]
  induction h with
  | ret hx => intro s; exact .act (.wr (hcell _)) (fun _ => .ret (hret _ _ hx))
  | @op O j e' o v k d hq hc _ ih =>
      intro s
      simp only [Tree.runL]
      have fwd : ¬ (j = i ∧ e' = e) → TS (okB.rem i e) Q (O + Own.one (.cap sg) c)
          (Tree.op j e' o v (fun y => (k y).runL i e c sg co s) (d ++ [.wb c ⟨sg, s⟩])) :=
        fun hne => .op ⟨hq, hne⟩ (CancelOK.lin (q_isLin o (hlin j e' hne hq))) (fun y => ih y s)
      by_cases hji : j = i
      · rw [if_pos hji]
        by_cases he : e' = e
        · subst he; subst hji
          rw [coStep_self]
          have := TS.bind (hco o v s) (F := O + Own.one (.cap sg) c) (ok' := okB.rem j e')
            (Q := Q) (f := coK sg c d (fun y s' => (k y).runL j e' c sg co s'))
            (fun O' x hx => by
              subst hx; rw [Own.zero_add]
              rcases x with ⟨y, s'⟩ | ⟨n, s'⟩
              · exact ih y s'
              · simp only [coK]
                have hw := errG_w (o := o) n
                exact dtors_safe (hc.2 hw) (.act (.wr (by simp [Own.one]))
                  (fun _ => .ret (herr _))))
            (ArgOK.bot _) (Ok.bot_le _)
          simpa using this
        · rw [coStep_ne he]; exact fwd (fun h => he h.2)
      · rw [if_neg hji]; exact fwd (fun h => hji h.1)
  | @ab O j e' a v d hq hd =>
      intro s
      by_cases hh : j = i ∧ e' = e
      · obtain ⟨-, rfl⟩ := hh; exact (hnoab a).elim
      · exact (ab_not_lin a (hlin j e' hh hq)).elim
  | nu _ ih => intro s; exact .nu (fun n => ih n s)
  | nuNew _ ih =>
      intro s
      exact .nuNew (fun n y => by have := ih n y s; rwa [Own.add_right_comm] at this)
  | nuAcq _ ih =>
      intro s
      exact .nuAcq (fun n y => by have := ih n y s; rwa [Own.add_right_comm] at this)
  | act ha _ ih => intro s; exact .act (ha.frame _) (fun y => ih y s)

end EffRel
