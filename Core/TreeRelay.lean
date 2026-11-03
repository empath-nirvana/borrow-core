import Core.TreeSchedRelay
import Core.TreeHeadlines

/-!
# Relay adequacy: a scheduler that keeps its stored tasks as a pool  `[spec §62]`

**The guarantee** (`RelayAdequacyT`, `relayAdequacyT`). A closed program `relay pre post`
(`relayE`): the relay's setup `pre` runs tasks under the park stepper and leaves one task's
answer `r` to drive, beside a pool of any number of other parked tasks (`PoolT`) and a state of its
own, the three apart; the loop `drive r` resumes the task each time it parks until it answers
(`drive_twp`); `post` runs on its answer. If `pre` ends that way and `post` is verified from every
end of the loop, the program is safe or diverges, reaches a value only at the empty memory, and
every `free` finds its cell.

Nothing fixes how many tasks the pool holds, which lends they hold, or what the relay does between
runs: `pre` and `post` are any code verified at `twp`, which may park tasks (`poolT_park`), run
other tasks beside the pool, those opening and ending lends of their own, the ones open when a
stored task parked included (`twp_keepsPool`), cancel a stored task under the stepper again
(`poolT_cancel`), resume one (`poolT_resume`) or drive one (`drive_twp`). The tasks run at frame
conditions met by every frame avoiding their records, not at `⊤`, so a task may end a lend.

**One fixed scheduler form, not an instance of `PoolSchedAdequacyT`.** The relay is setup, the
loop driving one task, and the code after it. Its scheduler is code outside a handler: the park
stepper `HP` hands each stop back as `inj₁ κ` (`QP`), and the relay's code holds the pool. The
general headline (`PoolSchedAdequacyT`, `Core/TreePoolSched.lean`) is about a program
`(hnd H e₀) (H, [])` whose scheduler is the handler and whose answers are functions of its state
(`PoolAns`). `relayE pre post` is not of that form, and `QP` is not `PoolAns`, so this theorem is
kept beside it as a check of the pool's moves from code outside the handler.

**How it is proved.** The setup ends in `RelayMidT`; the loop runs beside the relay's state
(`twp_frame_keep`, the state holding nothing at the pool's and the task's records,
`pool_frame`), and `drive_twp` keeps the pool by strong induction on the index; `post` runs from
the loop's end; `topAdequacyT` closes the program.
-/

noncomputable section

variable {ℍ : BoCa.Host} [BoCa.HostIs ℍ]

namespace BoCa.Fig16.Tree.Wp.SchedProgs.Park
open BoCa
open BoCa.Fig16
open BoCa.Fig16.Tree
open BoCa.Fig16.Tree.Wp
open BoCa.Fig16.Tree.Wp.SchedProgs.PingPong (QtStable)
open BoCa.Fig16.BoLo
open BoCa.Fig16.LogRel.Core
open BoCa.BoLo (Heap Step1 Head Kont)

/-- **The relay**: `(λx. post) (drive pre)`. -/
def relayE (pre post : Expr) : Expr := .app (.lam post) (.app driveV.1 pre)

/-- **What the relay's code after the loop must do**: from every end of the loop (the driven
task's answer in `Qt` beside the pool `ts`, `PoolPost`, owning `O₁`), beside the relay's state
re-read (`f`, owning `O₂`), the two apart, `post[x]` answers in `Q` under every frame condition
whose frames are empty. -/
def RelayPostT (Q : TPostV) (post : Expr) (Qt : TPostV) (ts : List StoredT) (w : TWd)
    (Oc : List (FrameRecT w.K)) (c : TRes w.K) : Prop :=
  ∀ (k : Nat) (w' : TWd) (ls' : List (SRecT w'.K)) (O₁ O₂ : List (FrameRecT w'.K)) (x : Val)
    (d f ρ' : TRes w'.K), w.Ext w' c → RRw (w := w) (w' := w') c f → RecsRR w'.Θ Oc O₂ →
    PoolPost (ℍ := ℍ) (valPost Qt) ts k w' ls' O₁ x.1 d → ResUT.CompS d f ρ' →
    NoneAt (recMask O₁) f → NoneAt (recMask O₂) d → (∀ p ∈ O₁, ∀ q ∈ O₂, p.le ≠ q.le) →
    ∀ F : TFrame, F.Mono → (∀ w ρf, F w ρf → ρf = PMap.empty) →
    twp (ℍ := ℍ) F (valPost Q) k w' ls' (O₁ ++ O₂) (post.subst 0 x) ρ'

/-- **Where the relay's setup ends**: at a task's answer `r` under the park stepper (`QP Qt`,
owning `Oa`), beside a pool `ts` (owning `Ob`), the two beside the relay's state `c` (owning `Oc`),
each two apart at each other's record masks and their records at distinct lent locations; and the
code after the loop verified from there (`RelayPostT`). -/
def RelayMidT (Q : TPostV) (post : Expr) : TPost := fun k w ls O t ρ =>
  ∃ (Qt : TPostV) (ts : List StoredT) (r : Val) (Oa Ob Oc : List (FrameRecT w.K))
    (a b d c : TRes w.K), Qt.Down ∧ QtStable Qt ∧ t = r.1 ∧ O = (Oa ++ Ob) ++ Oc ∧
    ResUT.CompS a b d ∧ ResUT.CompS d c ρ ∧ QP (ℍ := ℍ) Qt k w ls Oa r a ∧
    PoolT (ℍ := ℍ) ts w ls Ob b ∧ NoneAt (recMask Oa) b ∧ NoneAt (recMask Ob) a ∧
    (∀ p ∈ Oa, ∀ q ∈ Ob, p.le ≠ q.le) ∧ NoneAt (recMask (Oa ++ Ob)) c ∧
    NoneAt (recMask Oc) d ∧ (∀ p ∈ Oa ++ Ob, ∀ q ∈ Oc, p.le ≠ q.le) ∧
    RelayPostT (ℍ := ℍ) Q post Qt ts w Oc c

/-- **The relay at `twp`**: the setup ending in `RelayMidT`, under empty frames, the relay answers
in `Q`. -/
theorem relay_twp {Q : TPostV} {post : Expr} {F : TFrame} (hFm : F.Mono)
    (hF0 : ∀ w ρf, F w ρf → ρf = PMap.empty) {n : Nat} {w : TWd} {ls : List (SRecT w.K)}
    {O : List (FrameRecT w.K)} {pre : Expr} {ρ : TRes w.K}
    (h : twp (ℍ := ℍ) F (RelayMidT (ℍ := ℍ) Q post) n w ls O pre ρ) :
    twp (ℍ := ℍ) F (valPost Q) n w ls O (relayE pre post) ρ := by
  show twp (ℍ := ℍ) F _ n w ls O ((Kont.appR (.lam post) (.appR driveV.1 .hole)).plug pre) ρ
  refine twp_bind_fd hFm (fun _ _ h => h) _
    (fun w₀ ρf hf => by rw [hF0 _ _ hf]; exact noneAt_empty _) h ?_
  intro k _ w' ls' O' t ρ' hcov hv hls hO hmid
  obtain ⟨Qt, ts, r, Oa, Ob, Oc, a, b, d, c, hQd, hst, rfl, rfl, hab, hdc, hQ, hP, hb, ha, hap,
    hc, hd, hap₂, hpost⟩ := hmid
  show twp (ℍ := ℍ) _ _ k w' ls' _ ((Kont.appR (.lam post) .hole).plug (.app driveV.1 r.1)) ρ'
  have hF'm := TFrame.and_mono hFm (fdMask_mono (recMask ((Oa ++ Ob) ++ Oc)))
  have hcovd : CovR (sem w'.Θ) w'.K d := CovR.of_compS_left hdc hcov
  have hcovc : CovR (sem w'.Θ) w'.K c := CovR.of_compS_right hdc hcov
  have hvd := (ResUT.Valid.split hdc hv).1
  have hvc := (ResUT.Valid.split hdc hv).2
  let R : TRProp := fun w₁ O₂ ρ₂ =>
    w'.Ext w₁ c ∧ RRw (w := w') (w' := w₁) c ρ₂ ∧ RecsRR w₁.Θ Oc O₂
  have hRm : R.Mono := fun _ _ _ _ _ _ hE hr hO ⟨e₁, e₂, e₃⟩ =>
    ⟨e₁.trans e₂ hE, RRw.trans hE.1 e₂ hr, e₃.trans hE.1 hO⟩
  have hdrive := drive_twp hQd hst k ts (fdMask (recMask (Oa ++ Ob))) w' ls' Oa Ob a b d r
    (fdMask_mono _) (fun _ _ h => h) hQ hP hab hb ha hap hcovd hvd hls
    (fun x hx => hO x (List.mem_append_left _ (List.mem_append_left _ hx)))
  have hloop := twp_frame_keep (R := R) hRm hap₂ hdc hcov hv hc hd
    (pool_frame (M := recMask (Oa ++ Ob)) (F := F.and (fdMask (recMask ((Oa ++ Ob) ++ Oc))))
      (fun w₀ ρf hf => fdMask_le (fun x hx => (recMask_append x).mpr (Or.inl hx)) hf.2)
      (fun _ => Iff.rfl) hvc hc) hdrive
    ⟨TWd.Ext.refl _ _, RR.refl hcovc,
      RecsRR.refl fun x hx => hO x (List.mem_append_right _ hx)⟩
  refine twp_bind_fd hF'm (fun _ _ h => h) _ (fun w₀ ρf hf => hf.2.2) hloop ?_
  intro k₁ _ w₁ ls₁ O₁ t₁ ρ₁ _ _ _ _ hend
  obtain ⟨O₁', O₂', d', f', rfl, hcf, hdr, ⟨hE, hr, hOr⟩, -, hb', ha', hap'⟩ := hend
  obtain ⟨Oa', Ob', a', b', hO₁', hc', ⟨x, rfl, hx⟩, hrest⟩ := hdr
  cases k₁ with
  | zero => exact twp_zero
  | succ k₂ =>
  refine twp_step (fun μ => step1Only_plug (Head.beta μ post x) rfl .hole) ?_
  exact hpost k₂ w₁ ls₁ O₁' O₂' x d' f' ρ₁ hE hr hOr
    ⟨Oa', Ob', a', b', hO₁', hc', ⟨x, rfl, hQd _ _ _ _ _ _ hx⟩, hrest⟩ hcf hb' ha' hap' _
    (TFrame.and_mono hF'm (fdMask_mono _)) (fun w ρf hf => hF0 w ρf hf.1.1)

/-- **Relay adequacy.** A closed program `relay pre post` whose setup, from the empty world at any
tree, under the empty frame, ends in `RelayMidT` (a task's answer to drive beside a pool of any
number of parked tasks and the relay's state, and the code after the loop verified from every end
of the loop), the program's answers holding nothing, is safe or diverges. -/
def RelayAdequacyT : Prop :=
  ∀ (P : ParentFn) (Q : TPostV) (pre post : Expr),
    (∀ k w ls O v ρ, Q k w ls O v ρ → ρ = PMap.empty) →
    (∀ n, twp (ℍ := ℍ) (fun _ ρf => ρf = PMap.empty) (RelayMidT (ℍ := ℍ) Q post) n (w₀ P) [] []
      pre (PMap.empty : TRes (WCactus.ofParent P))) →
    OrDiverges (ℍ := ℍ) (relayE pre post)

theorem relayAdequacyT : RelayAdequacyT (ℍ := ℍ) :=
  fun P Q pre post hQ hpre => topAdequacyT P Q (relayE pre post) hQ fun n =>
    cerwpTE_iff.mpr (relay_twp emptyFrame_mono (fun _ _ h => h) (hpre n))

end BoCa.Fig16.Tree.Wp.SchedProgs.Park

end
