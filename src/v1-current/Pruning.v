Require Export XBehaviour.

Section SP_Prune.

Variable Sig : Signature.

Notation Pid := (pid Sig).
Notation Var := (var Sig).
Notation Value := (value Sig).
Notation Expr := (expr Sig).
Notation BExpr := (bexpr Sig).
Notation RecVar := (recvar Sig).
Notation Ann := (ann Sig).
Notation Ev := (ev Sig).
Notation BEv := (bev Sig).

Section MoreBranches.
(** ** Pruning
  The pruning relation is defined as: B can be pruned to B' if B' is obtained
  from B by removing some branches in branching terms. *)

Inductive more_branches : Behaviour Sig -> Behaviour Sig -> Prop :=
| MB_End : more_branches bnil bnil
| MB_Send p e a B B': more_branches B B' -> more_branches (p ! e @! a; B) (p ! e @! a; B')
| MB_Recv p x a B B': more_branches B B' -> more_branches (p ? x @? a; B) (p ? x @? a; B')
| MB_Sel p l a B B': more_branches B B' -> more_branches (p (+) l @+ a; B) (p (+) l @+ a; B')
| MB_Branching_None_None p mBl mBr : more_branches (p & mBl // mBr) (p & None // None)
| MB_Branching_None_Some p mBl a Br Br' : more_branches Br Br' ->
    more_branches (p & mBl // Some (a,Br)) (p & None // Some (a,Br'))
| MB_Branching_Some_None p a Bl Bl' mBr : more_branches Bl Bl' ->
    more_branches (p & Some (a,Bl) // mBr) (p & Some (a,Bl') // None)
| MB_Branching_Some_Some p a Bl Bl' a' Br Br' : more_branches Bl Bl' -> more_branches Br Br' ->
    more_branches (p & Some (a,Bl) // Some (a',Br)) (p & Some (a,Bl') // Some (a',Br'))
| MB_Cond b B1 B1' B2 B2' : more_branches B1 B1' -> more_branches B2 B2' ->
    more_branches (If b Then B1 Else B2) (If b Then B1' Else B2')
| MB_Call X : more_branches (Call _ X) (Call _ X)
.

Lemma more_branches_refl : forall B, more_branches B B.
Proof. BInduction B; try constructor; auto. Qed.

Lemma more_branches_refl' : forall B B', B = B' -> more_branches B B'.
Proof. intros. rewrite H. apply more_branches_refl. Qed.

Local Ltac rew_inv H H' := rewrite <- H in H'; inversion H'.

Lemma more_branches_trans : forall B B' B'',
  more_branches B B' -> more_branches B' B'' -> more_branches B B''.
Proof.
BInduction B; intros; try (inversion H; rewrite <- H2 in H0; inversion H0; constructor; eauto).
+ inversion H. rew_inv H1 H0. constructor.
+ inversion H. 1: rew_inv H1 H0; constructor.
  rew_inv H2 H0; constructor. eauto.
+ inversion H. 1: rew_inv H1 H0. constructor.
  rew_inv H2 H0; constructor. eauto.
+ inversion H.
  - rew_inv H1 H0. constructor.
  - rew_inv H2 H0; constructor; eauto.
  - rew_inv H2 H0; constructor; eauto.
  - rew_inv H3 H0; constructor; eauto.
+ inversion H. rew_inv H3 H0; constructor; eauto.
+ inversion H. rew_inv H1 H0; constructor.
Qed.

Lemma more_branches_antisym : forall (B B':Behaviour Sig),
  more_branches B B' -> more_branches B' B -> B = B'.
Proof.
BInduction B; intros.
all: inversion H; inversion H0; auto.
1,2,3: rew_inv H2 H8;
       rewrite IHB with B'0; auto;
       rewrite <- H17; auto.
+ rew_inv H1 H6.
+ rewrite (IHB Bl'); auto.
  rew_inv H8 H2; auto.
+ rew_inv H1 H6.
+ rewrite (IHB Br'); auto.
  rew_inv H8 H2; auto.
+ rew_inv H1 H7.
+ rew_inv H2 H9.
+ rew_inv H2 H9.
+ rew_inv H11 H3.
  rewrite (IHB1 Bl0); auto. rewrite (IHB2 Br0); auto.
  rewrite <- H22; auto. rewrite <- H20; auto.
+ rew_inv H3 H9.
  rewrite IHB1 with B1', IHB2 with B2'; auto.
  rewrite <- H16; auto. rewrite <- H15; auto.
Qed.

End MoreBranches.

Definition more_branches_N (N N':Network Sig) :=
  forall p, more_branches (N p) (N' p).

Notation "N >> N'" := (more_branches_N N N') (at level 50).

Open Scope SP.

Section MoreBranchesN.

Lemma more_branches_N_refl : forall N, N >> N.
Proof. intros; intro. apply more_branches_refl. Qed.

Lemma more_branches_N_refl' : forall (N N':Network Sig),
  (N == N') -> N >> N'.
Proof. intros; intro. apply more_branches_refl'; auto. Qed.

Lemma more_branches_N_trans : forall N N' N'',
  N >> N' -> N' >> N'' -> N >> N''.
Proof. intros; intro. eapply more_branches_trans; eauto. Qed.

Lemma SP_To_more_branches_N : forall Defs N1 s N2 s' Defs' N1' tl,
  SP_To _ Defs N1 s tl N2 s' -> N1' >> N1 -> (forall X, Defs X = Defs' X) ->
  exists N2', SP_To _ Defs' N1' s tl N2' s' /\ N2' >> N2.
Proof.
intros. rename H1 into HX. induction H.
- generalize (H0 p) (H0 q). rewrite H, H1; intros.
  inversion H4. clear H10; rename H11 into H10.
  inversion H5. clear H15; rename H16 into H15.
  rewrite H12, H14 in H11; clear B'1 H15 x0 H14 p1 H12.
  rewrite H7, H9 in H6; clear p0 H7 e0 H9 B'0 H10. clear H4 H5.
  rename B0 into Bp, B1 into Bq.
  assert (p <> q). intro. rewrite H4, H1 in H; inversion H.
  exists (Network_rm _ (Network_rm _ N1' p) q | p[Bp] | q[Bq]); split.
  apply S_Com with a0 Bp a1 Bq; auto. apply Network_eq_refl.
  intro r. rewrite H2.
  elim (eq_dec r p); intro Hp. 2: elim (eq_dec r q); intro Hq.
  rewrite Hp, Network_rm_add_2_p, Network_rm_add_2_p; auto.
  rewrite Hq, Network_rm_add_2_q, Network_rm_add_2_q; auto.
  rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
- generalize (H0 p) (H0 q). rewrite H, H1; intros.
  assert (p <> q) as Hpq. intro. rewrite H6, H1 in H; inversion H.
  inversion H4. rewrite H10 in *; clear a0 H10; rename H11 into H10.
  rewrite H7, H9 in H6; clear p0 H7 l H9 B' H10 H4.
  inversion H5.
  + rewrite H10 in *; clear a0 H10; rename H11 into H10, H12 into H11.
    rewrite H7 in H4. rewrite <- H11 in H1. clear p0 H7 Bl' H10 Br H11 H5.
    rename Bl0 into Bl', B0 into Bp.
    exists (Network_rm _ (Network_rm _ N1' p) q | p[Bp] | q[Bl']); split.
    apply S_LSel with a Bp a' Bl' mBr; auto. apply Network_eq_refl.
    intro r. rewrite H2.
    elim (eq_dec r p); intro Hp. 2: elim (eq_dec r q); intro Hq.
    rewrite Hp, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    rewrite Hq, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
  + rewrite H9 in *; clear a0 H9. rename H11 into H9, H12 into H11.
    rewrite H7 in H4. rewrite <- H11 in H1. clear p0 H7 Bl' H9 Br H11 H5.
    rename Bl0 into Bl', B0 into Bp.
    exists (Network_rm _ (Network_rm _ N1' p) q | p[Bp] | q[Bl']); split.
    apply S_LSel with a Bp a' Bl' (Some (a'0,Br0)); auto. apply Network_eq_refl.
    intro r. rewrite H2.
    elim (eq_dec r p); intro Hp. 2: elim (eq_dec r q); intro Hq.
    rewrite Hp, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    rewrite Hq, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
- generalize (H0 p) (H0 q). rewrite H, H1; intros.
  assert (p <> q) as Hpq. intro. rewrite H6, H1 in H; inversion H.
  inversion H4. rewrite H10 in *; clear a0 H10; rename H11 into H10.
  rewrite H7, H9 in H6; clear p0 H7 l H9 B' H10 H4.
  inversion H5.
  + rewrite H11 in *; clear a0 H11; rename H12 into H11.
    rewrite H7 in H4. rewrite <- H10 in H1. clear p0 H7 Br' H10 Bl H11 H5.
    rename Br0 into Br', B0 into Bp.
    exists (Network_rm _ (Network_rm _ N1' p) q | p[Bp] | q[Br']); split.
    apply S_RSel with a Bp a' mBl Br'; auto. apply Network_eq_refl.
    intro r. rewrite H2.
    elim (eq_dec r p); intro Hp. 2: elim (eq_dec r q); intro Hq.
    rewrite Hp, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    rewrite Hq, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
  + rewrite H11 in *; clear a'0 H11; rename H12 into H11.
    rewrite H7 in H4. rewrite <- H9 in H1. clear p0 H7 Br' H9 Bl H11 H5.
    rename Br0 into Br', B0 into Bp.
    exists (Network_rm _ (Network_rm _ N1' p) q | p[Bp] | q[Br']); split.
    apply S_RSel with a Bp a' (Some (a0,Bl0)) Br'; auto. apply Network_eq_refl.
    intro r. rewrite H2.
    elim (eq_dec r p); intro Hp. 2: elim (eq_dec r q); intro Hq.
    rewrite Hp, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    rewrite Hq, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
- generalize (H0 p). rewrite H; intros.
  inversion H4.
  rewrite H6 in H5; clear B2' B1' b0 H6 H7 H9 H4.
  rename B0 into B1', B3 into B2'.
  exists (Network_rm _ N1' p | p[B1']); split.
  apply S_Then with b B1' B2'; auto. apply Network_eq_refl.
  intro r. rewrite H2.
  elim (eq_dec r p); intro Hp.
  rewrite Hp, Par_proj2, Par_proj2; auto.
  unfold Process. repeat rewrite DecType_eq; auto.
  1,2: apply Network_rm_In.
  rewrite Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto.
  all: unfold Process; repeat rewrite DecType_neq; auto.
- generalize (H0 p). rewrite H; intros.
  inversion H4.
  rewrite H6 in H5; clear B2' B1' b0 H6 H7 H9 H4.
  rename B0 into B1', B3 into B2'.
  exists (Network_rm _ N1' p | p[B2']); split.
  apply S_Else with b B1' B2'; auto. apply Network_eq_refl.
  intro r. rewrite H2.
  elim (eq_dec r p); intro Hp.
  rewrite Hp, Par_proj2, Par_proj2; auto.
  unfold Process. repeat rewrite DecType_eq; auto.
  1,2: apply Network_rm_In.
  rewrite Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto.
  all: unfold Process; repeat rewrite DecType_neq; auto.
- generalize (H0 p). rewrite H; intros.
  inversion H3.
  rewrite H6 in H5; clear X0 H6 H3.
  exists (Network_rm _ N1' p | p[Defs X]); split.
  apply S_Call; auto. rewrite HX. apply Network_eq_refl.
  intro r. rewrite H1.
  elim (eq_dec r p); intro Hp.
  rewrite Hp, Par_proj2, Par_proj2; auto.
  unfold Process. repeat rewrite DecType_eq. apply more_branches_refl.
  1,2: apply Network_rm_In.
  rewrite Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto.
  all: unfold Process; repeat rewrite DecType_neq; auto.
Qed.

Lemma SPP_To_more_branches_N : forall P1 s P2 s' P1' tl,
  Net P1' >> Net P1 -> (forall X, Procs P1 X = Procs P1' X) ->
  (P1,s) --[tl]--> (P2,s') ->
  exists P2', (P1',s) --[tl]--> (P2',s') /\ Net P2' >> Net P2
    /\ forall X, Procs P2 X = Procs P2' X.
Proof.
intros.
inversion H1.
apply SP_To_more_branches_N with (Defs':= Procs P1') (N1':=Net P1') in H5; auto.
2: replace N with (Net P1); auto; rewrite <- H2; auto.
destroy H5. exists (Build_Program _ (Procs P1') x).
repeat split; auto.
rewrite (SP_eta _ P1').
constructor; auto.
replace Defs with (Procs P1); auto.
rewrite <- H2; auto.
intro. rewrite <- H0, <- H2; auto.
Qed.

Lemma SPP_ToStar_more_branches_N : forall P1 s P2 s' P1' tl,
  Net P1' >> Net P1 -> (forall X, Procs P1 X = Procs P1' X) ->
  (P1,s) --[tl]-->* (P2,s') ->
  exists P2', (P1',s) --[tl]-->* (P2',s') /\ Net P2' >> Net P2
  /\ forall X, Procs P1' X = Procs P2' X.
Proof.
intros. revert P1 s P2 s' P1' H H0 H1.
induction tl; intros; inversion H1.
+ rewrite <- H3. exists P1'; repeat split; auto. constructor.
+ induction c2.
  apply SPP_To_more_branches_N with (P1':=P1') in H5; auto.
  destroy H5.
  clear c1 H4 t H2 l H3 c3 H6.
  apply IHtl with (P1':=x) in H7; auto.
  destroy H7.
  exists x0; repeat split; auto.
  apply SPT_Step with (x,b); auto.
  intro. transitivity (Procs x X); auto.
  rewrite (SP_eta _ P1'), (SP_eta _ x) in H8.
  rewrite (SPP_To_Defs_stable _ _ _ _ _ _ _ _ H8); auto.
Qed.

End MoreBranchesN.

End SP_Prune.

Notation "N >> N'" := (more_branches_N _ N N') (at level 50).
Notation "B [>] B'" := (more_branches _ B B') (at level 50).
