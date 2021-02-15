Require Export Merge.

Module SP_Prune (P X V E B R:DecType) (Ev:Eval E X V V) (BEv:Eval B X V Bool).

Module Export SPP := SP_Merge P X V E B R Ev BEv.

Section MoreBranches.
(** ** Pruning
  The pruning relation is defined as: B can be pruned to B' if B' is obtained
  from B by removing some branches in branching terms. *)

Inductive more_branches : Behaviour -> Behaviour -> Prop :=
| MB_End : more_branches End End
| MB_Send p e B B': more_branches B B' -> more_branches (p ! e; B) (p ! e; B')
| MB_Recv p x B B': more_branches B B' -> more_branches (p ? x; B) (p ? x; B')
| MB_Sel p l B B': more_branches B B' -> more_branches (p (+) l; B) (p (+) l; B')
| MB_Branching_None_None p mBl mBr : more_branches (p & mBl // mBr) (p & None // None)
| MB_Branching_None_Some p mBl Br Br' : more_branches Br Br' ->
    more_branches (p & mBl // Some Br) (p & None // Some Br')
| MB_Branching_Some_None p Bl Bl' mBr : more_branches Bl Bl' ->
    more_branches (p & Some Bl // mBr) (p & Some Bl' // None)
| MB_Branching_Some_Some p Bl Bl' Br Br' : more_branches Bl Bl' -> more_branches Br Br' ->
    more_branches (p & Some Bl // Some Br) (p & Some Bl' // Some Br')
| MB_Cond b B1 B1' B2 B2' : more_branches B1 B1' -> more_branches B2 B2' ->
    more_branches (If b Then B1 Else B2) (If b Then B1' Else B2')
| MB_Call X : more_branches (Call X) (Call X)
.

Lemma more_branches_char_1 : forall B1 B2,
  more_branches B1 B2 -> merge B1 B2 = inject B1.
Proof.
unfold merge; intros.
induction H; simpl; auto;
  try case mBl; try case mBr; simpl; intros;
  try rewrite Pdec.eqb_refl;
  try rewrite Edec.eqb_refl;
  try rewrite Vdec.eqb_refl;
  try rewrite Xdec.eqb_refl;
  try rewrite label_eqb_refl;
  try rewrite Bdec.eqb_refl;
  try rewrite Rdec.eqb_refl;
  try rewrite IHmore_branches;
  repeat rewrite inject_match;
  simpl; auto.
+ rewrite IHmore_branches1, IHmore_branches2, inject_match, inject_match. auto.
+ rewrite IHmore_branches1, IHmore_branches2.
  case_eq (inject B1); case_eq (inject B2); simpl; auto; intros;
    try elim (inject_not_undefined _ H1);
    elim (inject_not_undefined _ H2).
Qed.

Lemma more_branches_char_2 : forall B1 B2,
  merge B1 B2 = inject B1 -> more_branches B1 B2.
Proof.
unfold merge.
induction B1 using Behaviour_ind'; induction B2 using Behaviour_ind'; simpl;
  try case_eq mB; try case_eq mB'; try case mB0; try case mB'0; simpl;
  intros; try constructor;
  try (inversion H; fail); try (inversion H3; fail).
10,13,16,17,18: exfalso; revert H5;
  case_eq (Pid_dec p p0); intro Hp; simpl; [idtac | intro H'; inversion H'];
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp;
  repeat rewrite inject_match; intro; inversion H5.
7,10,13,14:  revert H5;
  case_eq (Pid_dec p p0); intro Hp; simpl; [idtac | intro H'; inversion H'];
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp;
  intros; constructor.
+ revert H.
  case_eq (Pid_dec p p0); intro Hp; simpl. 2: intro H'; inversion H'.
  case_eq (Expr_dec e e0); intro He; simpl. 2: intro H'; inversion H'.
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp.
  unfold Expr_dec in He; rewrite Edec.eqb_eq in He; rewrite He.
  intros; constructor.
  apply IHB1.
  elim (XUndefined_dec (Xmerge (inject B1) (inject B2))); intro.
  1: rewrite a in H; inversion H.
  rewrite Xmatch_elim in H; auto.
  inversion H. rewrite H1; auto.
+ revert H.
  case_eq (Pid_dec p p0); intro Hp; simpl. 2: intro H'; inversion H'.
  case_eq (Var_dec v v0); intro Hv; simpl. 2: intro H'; inversion H'.
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp.
  unfold Var_dec in Hv; rewrite Xdec.eqb_eq in Hv. rewrite Hv.
  intros; constructor.
  apply IHB1.
  elim (XUndefined_dec (Xmerge (inject B1) (inject B2))); intro.
  1: rewrite a in H; inversion H.
  rewrite Xmatch_elim in H; auto.
  inversion H. rewrite H1; auto.
+ revert H.
  case_eq (Pid_dec p p0); intro Hp; simpl. 2: intro H'; inversion H'.
  case_eq (eqb_label l l0); intro Hl; simpl. 2: intro H'; inversion H'.
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp.
  rewrite label_eqb_eq in Hl; rewrite Hl.
  intros; constructor.
  apply IHB1.
  elim (XUndefined_dec (Xmerge (inject B1) (inject B2))); intro.
  1: rewrite a in H; inversion H.
  rewrite Xmatch_elim in H; auto.
  inversion H. rewrite H1; auto.
+ revert H5.
  case_eq (Pid_dec p p0); intro Hp; simpl. 2: intro H'; inversion H'.
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp.
  intros.
  assert (Xmerge (inject b1) (inject b) = inject b1 /\ Xmerge (inject b2) (inject b0) = inject b2).
  1: {
    elim (XUndefined_dec (Xmerge (inject b2) (inject b0))); intro.
    1: rewrite a in H5; inversion H5. 
    rewrite Xmatch_elim in H5; auto.
    elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro.
    1: rewrite a in H5; inversion H5.
    rewrite Xmatch_elim in H5; auto.
    inversion H5. rewrite H7, H8; auto.
  }
  inversion_clear H6.
  constructor; auto.
+ revert H5.
  case_eq (Pid_dec p p0); intro Hp; simpl. 2: intro H'; inversion H'.
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp.
  intros; constructor.
  apply H; auto.
  elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro.
  rewrite a in H5; inversion H5.
  rewrite Xmatch_elim, inject_match in H5; auto.
  inversion H5. rewrite H7; auto.
+ revert H5.
  case_eq (Pid_dec p p0); intro Hp; simpl. 2: intro H'; inversion H'.
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp.
  intros; constructor.
  apply H0; auto. rewrite inject_match in H5.
  elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro.
  rewrite a in H5; inversion H5.
  rewrite Xmatch_elim in H5; auto.
  inversion H5. rewrite H7; auto.
+ exfalso. revert H5.
  case_eq (Pid_dec p p0); intro Hp; simpl. 2: intro H'; inversion H'.
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp.
  rewrite inject_match.
  elim (XUndefined_dec (Xmerge (inject b1) (inject b0))); intro.
  rewrite a; intro; inversion H5.
  rewrite Xmatch_elim; auto. intro; inversion H5.
+ revert H5.
  case_eq (Pid_dec p p0); intro Hp; simpl. 2: intro H'; inversion H'.
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp.
  intros; constructor.
  apply H; auto.
  elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro.
  rewrite a in H5; inversion H5.
  rewrite Xmatch_elim in H5; auto.
  inversion H5. rewrite H7; auto.
+ exfalso. revert H5.
  case_eq (Pid_dec p p0); intro Hp; simpl. 2: intro H'; inversion H'.
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp.
  rewrite inject_match.
  elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro.
  rewrite a; intro; inversion H5.
  rewrite Xmatch_elim; auto. intro; inversion H5.
+ revert H5.
  case_eq (Pid_dec p p0); intro Hp; simpl. 2: intro H'; inversion H'.
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp.
  intros; constructor.
  apply H0; auto.
  elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro.
  rewrite a in H5; inversion H5.
  rewrite Xmatch_elim in H5; auto.
  inversion H5. rewrite H7; auto.
+ revert H.
  case_eq (BExpr_dec b b0); intro Hb; simpl. 2: intro H'; inversion H'.
  unfold BExpr_dec in Hb; rewrite Bdec.eqb_eq in Hb; rewrite Hb.
  rename B1_1 into Bt, B1_2 into Be, B2_1 into Bt', B2_2 into Be'.
  intro.
  assert (Xmerge (inject Bt) (inject Bt') = inject Bt /\ Xmerge (inject Be) (inject Be') = inject Be).
  1: {
    elim (XUndefined_dec (Xmerge (inject Bt) (inject Bt'))); intro.
    1: rewrite a in H; inversion H. 
    elim (XUndefined_dec (Xmerge (inject Be) (inject Be'))); intro.
    1: rewrite a, Xmatch_elim in H; auto; inversion H.
    revert H.
    case (Xmerge (inject Bt) (inject Bt')); case (Xmerge (inject Be) (inject Be'));
      intros; try inversion H; auto.
  }
  inversion_clear H0. constructor; auto.
+ revert H.
  case_eq (RecVar_dec X X0); intro HX; simpl. 2: intro H'; inversion H'.
  unfold RecVar_dec in HX; rewrite Rdec.eqb_eq in HX; rewrite HX.
  constructor.
Qed.

Lemma more_branches_char : forall B1 B2,
  more_branches B1 B2 <-> merge B1 B2 = inject B1.
Proof.
split.
+ apply more_branches_char_1.
+ apply more_branches_char_2.
Qed.

Lemma merge_more_branches : forall B1 B2 B,
  merge B1 B2 = inject B -> more_branches B B1.
Proof.
unfold merge; intros.
rename H into Hinj; revert B1 B2 Hinj.
induction B using Behaviour_ind'; simpl; intros.
+ elim (merge_inv_End _ _ Hinj); intros.
  rewrite H; constructor.
+ elim (merge_inv_Send _ _ _ _ _ Hinj); intros.
  rename x into B1'; inversion_clear H.
  rename x into B2'; inversion_clear H0.
  inversion_clear H1.
  rewrite H; constructor; eauto.
+ elim (merge_inv_Recv _ _ _ _ _ Hinj); intros.
  rename x into B1'; inversion_clear H.
  rename x into B2'; inversion_clear H0.
  inversion_clear H1.
  rewrite H; constructor; eauto.
+ elim (merge_inv_Sel _ _ _ _ _ Hinj); intros.
  rename x into B1'; inversion_clear H.
  rename x into B2'; inversion_clear H0.
  inversion_clear H1.
  rewrite H; constructor; eauto.
+ revert Hinj. case_eq mB; case_eq mB'; intros;
  elim (merge_inv_Branching _ _ _ _ _ Hinj); intros;
  rename x into Bl'; inversion_clear H3;
  rename x into Bl''; inversion_clear H4;
  rename x into Br'; inversion_clear H3;
  rename x into Br''; inversion_clear H4;
  destroy H5; rewrite H3.
  - elim (H8 (inject b0)); auto; intros; inversion_clear H10.
    elim (H5 (inject b)); auto; intros; inversion_clear H13.
    case_eq Bl'; case_eq Bl''; case_eq Br'; case_eq Br''; constructor.
    3,5: apply (H _ H2 b3 b2); apply H12; auto.
    2,6,11,13: apply (H0 _ H1 b2 b1); apply H15; auto.
    2,6,9,10: apply (H0 _ H1 b1 b);
      elim H14; auto; intros; destroy H19;
      rewrite H16 in H20; inversion H20;
      rewrite <- H19; apply merge_idempotent.
    4,5: apply (H _ H2 b2 b0);
      elim H11; auto; intros; destroy H19;
      rewrite H18 in H20; inversion H20;
      rewrite <- H19; apply merge_idempotent.
    * apply (H _ H2 b4 b3). apply H12; auto.
    * apply (H _ H2 b2 b1). apply H12; auto.
    * apply (H _ H2 b3 b0).
      elim H11; auto. intros. destroy H19.
      rewrite H18 in H20; inversion H20.
      rewrite <- H19. apply merge_idempotent.
    * apply (H _ H2 b1 b0).
      elim H11; auto. intros. destroy H19.
      rewrite H18 in H20; inversion H20.
      rewrite <- H19. apply merge_idempotent.
  - elim (H8 (inject b)); auto; intros; inversion_clear H10.
    elim H7; auto; intros. rewrite H10.
    case_eq Bl'; case_eq Bl''; constructor.
    * apply (H _ H2 b1 b0). apply H12; auto.
    * apply (H _ H2 b0 b).
      elim H11; auto; intros. destroy H16.
      rewrite H15 in H17; inversion H17.
      rewrite <- H16; apply merge_idempotent.
  - elim (H5 (inject b)); auto; intros; inversion_clear H10.
    elim H6; auto; intros. rewrite H10.
    case_eq Br'; case_eq Br''; constructor.
    * apply (H0 _ H1 b1 b0). apply H12; auto.
    * apply (H0 _ H1 b0 b).
      elim H11; auto; intros. destroy H16.
      rewrite H15 in H17; inversion H17.
      rewrite <- H16; apply merge_idempotent.
  - elim H6; auto; intros. rewrite H9.
    elim H7; auto; intros. rewrite H11.
    constructor.
+ elim (merge_inv_Cond _ _ _ _ _ Hinj); intros.
  rename x into Be'; inversion_clear H.
  rename x into Be''; inversion_clear H0.
  rename x into Bt; inversion_clear H.
  rename x into Bt''; destroy H0.
  rewrite H; constructor; eauto.
+ elim (merge_inv_Call _ _ _ Hinj); intros.
  rewrite H; constructor; eauto.
Qed.

Lemma merge_more_branches' : forall B1 B2 B,
  merge B1 B2 = inject B -> more_branches B B2.
Proof.
intros.
apply merge_more_branches with B1.
rewrite merge_comm; auto.
Qed.

Lemma more_branches_refl : forall B, more_branches B B.
Proof.
induction B using Behaviour_ind'; try constructor; auto.
induction mB, mB'; constructor; auto.
Qed.

Lemma more_branches_refl' : forall B B', B = B' -> more_branches B B'.
Proof. intros. rewrite H. apply more_branches_refl. Qed.

Lemma more_branches_trans : forall B B' B'',
  more_branches B B' -> more_branches B' B'' -> more_branches B B''.
Proof.
induction B using Behaviour_ind'; intros;
  try (inversion H; rewrite <- H2 in H0; inversion H0; constructor; eauto).
+ inversion H1.
  - rewrite <- H3 in H2. inversion H2. constructor.
  - rewrite <- H4 in H2. inversion H2; constructor; eauto.
  - rewrite <- H4 in H2. inversion H2; constructor; eauto.
  - rewrite <- H5 in H2. inversion H2; constructor; eauto.
+ inversion H. rewrite <- H3 in H0; inversion H0; constructor; eauto.
+ inversion H. rewrite <- H1 in H0; inversion H0; constructor.
Qed.

Local Ltac lelim X B H H':=
  elim (XUndefined_dec X); intro H;
  [ rewrite H in H'; elim (inject_not_undefined B); auto
  | rewrite Xmatch_elim in H'; auto ].

Local Ltac lelim2 X Y B H H' H'' := lelim X B H H''; lelim Y B H' H''.

Local Ltac mbsolve B B' := apply more_branches_trans with B;
  [apply merge_more_branches with B' | idtac]; auto.

Local Ltac mbsolve'' B B' := apply more_branches_trans with B;
  [apply merge_more_branches' with B' | idtac]; auto.

Local Ltac mbsolve' H := apply inject_inj in H; rewrite <- H; auto.

Lemma more_branches_merge_extend : forall B1 B2 B1' B2' B,
  more_branches B1 B1' -> more_branches B2 B2' -> merge B1 B2 = inject B ->
  exists B', merge B1' B2' = inject B' /\ more_branches B B'.
Proof.
induction B1 using Behaviour_ind'.
1,2,3,4,6,7: intros; inversion H; revert H0 H1.
+ unfold merge; simpl; case_eq B2; simpl; intros.
  5: induction o, o0.
  all: try (elim (inject_not_undefined B); auto; fail).
  inversion H1. simpl. exists End; repeat split.
  revert H2; case_eq B; intros; inversion H4.
  constructor. induction o, o0; inversion H7.
+ unfold merge; simpl; case_eq B2; simpl; intros.
  5: induction o, o0.
  all: try (elim (inject_not_undefined B); auto; fail).
  inversion H1. simpl.
  clear B3 H11 e2 H10 p2 H8 H1 B2' H9 B2 H0 B1' H3 H B0 H5 e0 H4 p0 H2.
  revert H7. elim Pid_dec. elim Expr_dec. all: simpl; intros.
  2,3: elim (inject_not_undefined B); auto.
  lelim (Xmerge (inject B1) (inject b)) B H' H7.
  revert H7. case_eq B; intros; try inversion H7.
  2: induction o, o0; inversion H7.
  rewrite <- H2, <- H1; rewrite <- H2, <- H1 in H7, H; clear e0 p0 H2 H1 B H.
  elim IHB1 with b B' B'0 b0; auto. intros.
  rename x into B; destroy H.
  unfold merge in H0; rewrite H0.
  exists (p!e;B); split.
  rewrite Xmatch_elim; auto. apply inject_not_undefined.
  constructor; auto.
+ unfold merge; simpl; case_eq B2; simpl; intros.
  5: induction o, o0.
  all: try (elim (inject_not_undefined B); auto; fail).
  inversion H1. simpl.
  clear B3 H11 x0 H10 p2 H8 H1 B2' H9 B2 H0 B1' H3 H B0 H5 x H4 p0 H2.
  revert H7. elim Pid_dec. elim Var_dec. all: simpl; intros.
  2,3: elim (inject_not_undefined B); auto.
  lelim (Xmerge (inject B1) (inject b)) B H' H7.
  revert H7. case_eq B; intros; try inversion H7.
  2: induction o, o0; inversion H7.
  rewrite <- H2, <- H1; rewrite <- H2, <- H1 in H7, H; clear v1 p0 H2 H1 B H.
  elim IHB1 with b B' B'0 b0; auto. intros.
  rename x into B; destroy H.
  unfold merge in H0; rewrite H0.
  exists (p ? v;B); split.
  rewrite Xmatch_elim; auto. apply inject_not_undefined.
  constructor; auto.
+ unfold merge; simpl; case_eq B2; simpl; intros.
  5: induction o, o0.
  all: try (elim (inject_not_undefined B); auto; fail).
  inversion H1. simpl.
  clear B3 H11 l2 H10 p2 H8 H1 B2' H9 B2 H0 B1' H3 H B0 H5 l0 H4 p0 H2.
  revert H7. elim Pid_dec. elim eqb_label. all: simpl; intros.
  2,3: elim (inject_not_undefined B); auto.
  lelim (Xmerge (inject B1) (inject b)) B H' H7.
  revert H7. case_eq B; intros; try inversion H7.
  2: induction o, o0; inversion H7.
  rewrite <- H2, <- H1; rewrite <- H2, <- H1 in H7, H; clear l0 p0 H2 H1 B H.
  elim IHB1 with b B' B'0 b0; auto. intros.
  rename x into B; destroy H.
  unfold merge in H0; rewrite H0.
  exists (p(+)l;B); split.
  rewrite Xmatch_elim; auto. apply inject_not_undefined.
  constructor; auto.
+ clear B1' H4 B0 H5 B1 H3 b0 H2 H.
  rename B1_1 into Bt, B1_2 into Be, B1'0 into Bt', B2'0 into Be'.
  intro. unfold merge. case_eq B2; intros.
  5: induction o, o0.
  all: try (simpl in H1; elim (inject_not_undefined B); auto; fail).
  rewrite H in H0; clear B2 H; inversion H0.
  clear B2 H4 B1 H2 b3 H B2' H3 H0.
  assert (b = b0).
  1: {
    revert H1; simpl. case_eq (BExpr_dec b b0); intros.
    unfold BExpr_dec in H; rewrite Bdec.eqb_eq in H; auto.
    elim (inject_not_undefined B); auto.
  }
  rewrite <- H in H1; rewrite <- H; clear H.
  change (Xmerge (XCond b (inject Bt) (inject Be)) (XCond b (inject b1) (inject b2)) = inject B) in H1.
  rewrite Xmerge_Cond_inv in H1; auto.
  revert H1. case_eq B; intros; inversion H1.
  revert H2. induction o, o0; intro; inversion H2.
  clear B H. rewrite <- H2; clear b3 H2 H1.
  elim IHB1_1 with b1 Bt' B1' b4; auto.
  elim IHB1_2 with b2 Be' B2'0 b5; auto.
  intros. destroy H; destroy H0. exists (Cond b x0 x); split.
  - simpl. Beq. unfold merge in H2, H1; rewrite H1, H2; simpl.
    case_eq (inject x0); case_eq (inject x); auto; intros;
      eelim inject_not_undefined; eauto.
  - constructor; auto.
  - intro. revert H1; simpl; rewrite H. Beq.
    intro. apply (inject_not_undefined B); auto.
  - intro. revert H1; simpl; rewrite H. Beq.
    case (Xmerge (inject Bt) (inject b1)); intros; apply (inject_not_undefined B); auto.
+ unfold merge; simpl. case_eq B2; simpl; intros.
  5: induction o, o0.
  all: try (elim (inject_not_undefined B); auto; fail).
  inversion H1. simpl.
  revert H4. elim RecVar_dec. all: simpl; intros.
  exists B; split; auto. apply more_branches_refl.
  elim (inject_not_undefined B); auto.
+ intros.
  revert H3. unfold merge; case_eq B2; simpl; intros.
  all: induction mB, mB'; try (elim (inject_not_undefined B); auto; fail).
  all: rewrite H3 in H2; clear B2 H3.
  all: inversion H2.
  all: induction o, o0; try (elim (inject_not_undefined B); auto; fail).
  all: elim (P.eq_dec p p0); intro Hpp0;
  [ try rewrite <- Hpp0 in H2;
    try rewrite <- Hpp0 in H3;
    try rewrite <- Hpp0 in H4;
    try rewrite <- Hpp0 in H5;
    try rewrite <- Hpp0 in H6; rewrite <- Hpp0; clear p0 Hpp0
  | rewrite <- Pdec.eqb_neq in Hpp0;
    simpl in H4; unfold Pid_dec in H4; rewrite Hpp0 in H4;
    elim (inject_not_undefined B); auto ].
  all: revert H4; simpl; Peq; intro.
  all: inversion H1; simpl; Peq.
  all: try (inversion H7; fail).
  all: try (inversion H6; fail).
  all: try (inversion H5; fail).
  (* 81 goals left *)
  all: do 2 try (rewrite Xmatch_elim; [idtac | apply inject_not_undefined]).
  all: try lelim (Xmerge (inject a) (inject a0)) B Ha H4.
  all: try lelim (inject a) B Ha H4.
  all: try lelim (Xmerge (inject b) (inject b0)) B Hb H4.
  all: try lelim (inject b) B Hb H4.
  1,5,9,13,37,39,41,43,55,57,59,61,73,74,75,76:
    exists (p & None // None); split; auto.
  1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16:
    revert H4; case_eq B; intros; inversion H12;
    replace p with p2; [constructor |
      induction o, o0; inversion H12; auto].
  (* 65 cases left *)
  1,4,7,10,13,17,37,39,47,48,49,50,51,53,61,62:
    exists (p & None // Some Br'); split; auto.
  1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16:
    revert H4; case_eq B; intros; inversion H13;
    induction o, o0; inversion H13; constructor.
  1,3,9,11: mbsolve b b0.
  1,2,7: mbsolve' H18.
  1,2,6,7: mbsolve'' Br b; inversion H7; auto.
  1,2,4: mbsolve' H18; inversion H7; rewrite <- H19; auto.
  1: mbsolve' H17.
  1: mbsolve' H17; inversion H7; rewrite <- H18; auto.
  (* 49 cases left *)
  1,3,5,7,15,19,27,28,29,30,33,35,41,43,47,48:
    exists (p & Some Bl' // None); split; auto;
    revert H4; case_eq B; intros; inversion H13;
    induction o, o0; inversion H13; constructor.
  1,2,7,8: mbsolve a a0; fail.
  1,2,5,6: mbsolve' H17.
  1,2,3,4: mbsolve'' Bl a; inversion H6; auto.
  1,2,3: mbsolve' H17; inversion H6; rewrite <- H19; auto.
  1: mbsolve' H17; inversion H6; rewrite <- H18; auto.
  (* 33 cases left *)
  1,2,3,4,6,9,11,14,17,21,22,25,29,30,31,33:
    exists (p & Some Bl' // Some Br'); split; auto;
    revert H4; case_eq B; intros; inversion H14;
    induction o, o0; inversion H14; constructor.
  1,3,9,19: mbsolve a a0.
  1,4,11,22: mbsolve b b0.
  1,4,10,20: mbsolve' H19.
  1,2,4,11: mbsolve' H18; fail.
  1,2,6,14: mbsolve'' Br b; inversion H7; auto.
  1,2: mbsolve'' Bl a; inversion H6; auto.
  1,4: mbsolve'' Bl a; inversion H5; auto.
  1,2,3,8: mbsolve' H19; inversion H7; rewrite <- H20; auto.
  1,2: mbsolve' H18; inversion H6; rewrite <- H20; auto.
  1,2: mbsolve' H18; inversion H5; rewrite <- H20; auto.
 (* 17 cases left *)
  all: try (apply merge_not_undefined in Ha; destroy Ha;
    elim H with a Bl Bl'0 Bl' x; auto;
   [intros | try (inversion H6; auto; fail); inversion H5; auto]).
  all: try (apply merge_not_undefined in Hb; destroy Hb;
    elim H0 with b Br Br'0 Br' x; auto; [intros | inversion H7; auto; fail]).
  11: apply merge_not_undefined in Hb; destroy Hb;
    elim H0 with b Br Br'0 Br' x1; auto; [intros | inversion H7; auto; fail].
  all: try (destroy H14; unfold merge in H15; rewrite H15).
  all: try (destroy H15; unfold merge in H16; rewrite H16).
  11: destroy H16; unfold merge in H18; rewrite H18.
  11: destroy H17; unfold merge in H19; rewrite H19.
  all: rewrite Xmatch_elim; [idtac | apply inject_not_undefined].
  all: try (rewrite Xmatch_elim; [idtac | apply inject_not_undefined]).
  1,3,15,16: exists (p & None // Some x0); split; auto;
    revert H4; case_eq B; intros; inversion H16;
    induction o, o0; inversion H16; constructor.
  1,2,3: unfold merge in Hb; rewrite Hb in H21; mbsolve' H21.
  1: unfold merge in Hb; rewrite Hb in H20; mbsolve' H20.
  3,5,10,11: exists (p & Some x0 // None); split; auto;
    revert H4; case_eq B; intros; inversion H16;
    induction o, o0; inversion H16; constructor;
    unfold merge in Ha; rewrite Ha in H20; mbsolve' H20.
  1,2,5,9: exists (p & Some Bl' // Some x0); split; auto;
    revert H4; case_eq B; intros; inversion H17;
    induction o, o0; inversion H17; constructor;
    [idtac | unfold merge in Hb; rewrite Hb in H22; mbsolve' H22].
  1: mbsolve a a0.
  1: mbsolve' H21.
  1: mbsolve'' Bl a; inversion H5; auto.
  1: mbsolve' H21; inversion H5; rewrite <- H23; auto.
  1,2,3,5: exists (p & Some x0 // Some Br'); split; auto;
    revert H4; case_eq B; intros; inversion H17;
    induction o, o0; inversion H17; constructor;
    [ unfold merge in Ha; rewrite Ha in H21; mbsolve' H21 | idtac].
  1: mbsolve b b0.
  1: mbsolve' H22.
  1: mbsolve'' Br b; inversion H7; auto.
  1: mbsolve' H22; inversion H7; rewrite <- H23; auto.
  exists (p & Some x0 // Some x2); split; auto;
  revert H4; case_eq B; intros. all: inversion H20.
  induction o, o0; inversion H20. constructor.
  unfold merge in Ha; rewrite Ha in H24. mbsolve' H24.
  unfold merge in Hb; rewrite Hb in H25. mbsolve' H25.
Qed.

Lemma more_branches_merge : forall B B1 B2,
  more_branches B B1 -> more_branches B B2 ->
  exists B', merge B1 B2 = inject B' /\ more_branches B B'.
Proof.
induction B using Behaviour_ind'; intros.
+ inversion H; inversion H0.
  exists End; split; auto. constructor.
+ inversion H; inversion H0.
  elim (IHB _ _ H5 H10); intros. destroy H11.
  exists (p!e; x); split.
  - unfold merge; simpl. Peq. Eeq.
    unfold merge in H12; rewrite H12, Xmatch_elim; auto.
    apply inject_not_undefined.
  - constructor; auto.
+ inversion H; inversion H0.
  elim (IHB _ _ H5 H10); intros. destroy H11.
  exists (p ? v; x1); split.
  - unfold merge; simpl. Peq. Veq.
    unfold merge in H12; rewrite H12, Xmatch_elim; auto.
    apply inject_not_undefined.
  - constructor; auto.
+ inversion H; inversion H0.
  elim (IHB _ _ H5 H10); intros. destroy H11.
  exists (p(+)l; x); split.
  - unfold merge; simpl. Peq. rewrite label_eqb_refl.
    unfold merge in H12; rewrite H12, Xmatch_elim; auto.
    apply inject_not_undefined.
  - constructor; auto.
+ inversion H1; inversion H2. all: unfold merge; simpl; Peq.
  - exists (p & None // None); split; auto.
    constructor.
  - exists (p & None // Some Br'); split.
    rewrite Xmatch_elim; auto. apply inject_not_undefined.
    constructor; auto.
  - exists (p & Some Bl' // None); split.
    rewrite Xmatch_elim; auto. apply inject_not_undefined.
    constructor; auto.
  - exists (p & Some Bl' // Some Br'); split.
    repeat rewrite Xmatch_elim; auto. 1,2: apply inject_not_undefined.
    constructor; auto.
  - exists (p & None // Some Br'); split.
    rewrite Xmatch_elim; auto. apply inject_not_undefined.
    constructor; auto.
  - rewrite <- H6 in H11; inversion H11.
    rewrite H14 in H12.
    elim H0 with Br Br' Br'0; auto. intros. destroy H13.
    exists (p & None // Some x); split.
    unfold merge in H15; rewrite H15, Xmatch_elim.
    simpl; auto. apply inject_not_undefined.
    constructor; auto.
  - repeat rewrite Xmatch_elim. 2,3: apply inject_not_undefined.
    exists (p & Some Bl' // Some Br'); split; auto.
    constructor; auto.
  - rewrite Xmatch_elim. 2: apply inject_not_undefined.
    rewrite <- H6 in H11; inversion H11.
    rewrite H15 in H13.
    elim H0 with Br Br' Br'0; auto. intros. destroy H14.
    unfold merge in H16; rewrite H16, Xmatch_elim.
    2: apply inject_not_undefined.
    exists (p & Some Bl' // Some x); split; auto.
    constructor; auto.
  - rewrite Xmatch_elim. 2: apply inject_not_undefined.
    exists (p & Some Bl' // None); split; auto.
    constructor; auto.
  - repeat rewrite Xmatch_elim. 2,3: apply inject_not_undefined.
    exists (p & Some Bl' // Some Br'); split; auto.
    constructor; auto.
  - rewrite <- H5 in H10. inversion H10.
    rewrite H14 in H12.
    elim H with Bl Bl' Bl'0; auto. intros. destroy H13.
    unfold merge in H15; rewrite H15, Xmatch_elim.
    2: apply inject_not_undefined.
    exists (p & Some x // None); split; auto.
    constructor; auto.
  - rewrite <- H5 in H9. inversion H9.
    rewrite H15 in H12.
    elim H with Bl Bl' Bl'0; auto. intros. destroy H14.
    unfold merge in H16; rewrite H16, Xmatch_elim, Xmatch_elim.
    2,3: apply inject_not_undefined.
    exists (p & Some x // Some Br'); split; auto.
    constructor; auto.
  - repeat rewrite Xmatch_elim. 2,3: apply inject_not_undefined.
    exists (p & Some Bl' // Some Br'); split; auto.
    constructor; auto.
  - rewrite Xmatch_elim. 2: apply inject_not_undefined.
    rewrite <- H6 in H12; inversion H12.
    rewrite H15 in H13.
    elim H0 with Br Br' Br'0; auto. intros. destroy H14.
    unfold merge in H16; rewrite H16, Xmatch_elim.
    2: apply inject_not_undefined.
    exists (p & Some Bl' // Some x); split; auto.
    constructor; auto.
  - rewrite <- H4 in H11. inversion H11.
    rewrite H15 in H13.
    elim H with Bl Bl' Bl'0; auto. intros. destroy H14.
    unfold merge in H16; rewrite H16, Xmatch_elim, Xmatch_elim.
    2,3: apply inject_not_undefined.
    exists (p & Some x // Some Br'); split; auto.
    constructor; auto.
  - rewrite <- H4 in H10. inversion H10.
    rewrite H16 in H13.
    elim H with Bl Bl' Bl'0; auto. intros. destroy H15.
    rewrite <- H6 in H12. inversion H12.
    rewrite H19 in H14.
    elim H0 with Br Br' Br'0; auto. intros. destroy H18.
    unfold merge in H17, H20; rewrite H17, H20, Xmatch_elim, Xmatch_elim.
    2,3: apply inject_not_undefined.
    exists (p & Some x // Some x0); split; auto.
    constructor; auto.
+ inversion H; inversion H0.
  elim (IHB1 B1' B1'0); auto; intros. destroy H13.
  elim (IHB2 B2' B2'0); auto; intros. destroy H15.
  exists (If b Then x Else x0); split. unfold merge.
  simpl (inject (If b Then B1' Else B2')). simpl (inject (If b Then B1'0 Else B2'0)).
  rewrite Xmerge_Cond_inv.
  - simpl. rewrite <- H14, <- H16; auto.
  - unfold merge in H14; rewrite H14. apply inject_not_undefined.
  - unfold merge in H16; rewrite H16. apply inject_not_undefined.
  - constructor; auto.
+ inversion H; inversion H0.
  exists (Call X); split.
  unfold merge; simpl. Xeq; auto.
  constructor.
Qed.

(** The same relation on extended behaviours, and corresponding lemmas. *)
Definition Xmore_branches XB XB' := exists B B',
  XB = inject B /\ XB' = inject B' /\ more_branches B B'.

Lemma more_branches_X : forall B B',
 more_branches B B' -> Xmore_branches (inject B) (inject B').
Proof. red. eauto. Qed.

Lemma X_more_branches : forall B B',
 Xmore_branches (inject B) (inject B') -> more_branches B B'.
Proof.
intros.
destroy H.
apply inject_inj in H0; apply inject_inj in H1.
rewrite H0, H1; auto.
Qed.

Lemma Xmore_branches_refl : forall X B, X = inject B ->
  Xmore_branches X X.
Proof. intros. rewrite H. apply more_branches_X, more_branches_refl. Qed.

Lemma Xmore_branches_trans : forall X X' X'',
  Xmore_branches X X' -> Xmore_branches X' X'' -> Xmore_branches X X''.
Proof.
intros.
destroy H; destroy H0.
exists x, x2; repeat split; auto.
apply more_branches_trans with x0; auto.
rewrite H3 in H2. apply inject_inj in H2. inversion H2. 
rewrite <- H5; auto.
Qed.

Lemma Xmore_branches_merge : forall B B1 B2,
  Xmore_branches B B1 -> Xmore_branches B B2 -> Xmore_branches B (Xmerge B1 B2).
Proof.
intros.
destroy H; destroy H0.
rewrite H1 in H3; apply inject_inj in H3.
rewrite <- H3 in H0; clear x1 H3.
elim (more_branches_merge _ _ _ H H0).
intros. destroy H3.
rewrite H1, H2, H4. red; eauto.
Qed.

Lemma Xmore_branches_merge_extend : forall B1 B2 B1' B2' B,
  Xmore_branches B1 B1' -> Xmore_branches B2 B2' ->
  Xmerge B1 B2 = inject B ->
  Xmore_branches (Xmerge B1 B2) (Xmerge B1' B2').
Proof.
intros. destroy H. destroy H0.
rewrite H2, H4 in H1.
elim (more_branches_merge_extend _ _ _ _ _ H H0 H1); intros.
destroy H6.
rewrite H2, H3, H4, H5.
eexists; eexists; repeat split; eauto.
Qed.

Lemma Xmore_branches_char : forall B1 B2,
  Xmore_branches B1 B2 <-> (collapse B1 <> XUndefined /\ Xmerge B1 B2 = B1).
Proof.
split; intros; destroy H.
+ rewrite H0, H1, collapse_inject; split.
  apply inject_not_undefined.
  apply more_branches_char; auto.
+ elim (collapse_char' B2); intro H2.
  destroy H2. apply collapse_exists in H0. destroy H0.
  exists x0, x; repeat split; auto.
  rewrite more_branches_char.
  unfold merge. rewrite <- H0, <- H2; auto.
  apply collapse_merge' with B1 B2 in H2.
  rewrite H in H2. elim H0; auto.
Qed.

Lemma Xmerge_more_branches : forall B1 B2,
  collapse (Xmerge B1 B2) <> XUndefined -> Xmore_branches (Xmerge B1 B2) B1.
Proof.
intros.
apply collapse_exists in H. destroy H.
elim (collapse_char' B1); intro. induction a.
elim (collapse_char' B2); intro. induction a.
+ rewrite H, p.
  apply more_branches_X, merge_more_branches with x1.
  unfold merge. rewrite <- p, <- p0; auto.
+ exfalso. apply Xmerge_inv_inject' in H.
  destroy H. rewrite H, collapse_inject in b.
  apply inject_not_undefined in b; auto.
+ exfalso. apply Xmerge_inv_inject in H.
  destroy H.  rewrite H, collapse_inject in b.
  apply inject_not_undefined in b; auto.
Qed.

Lemma Xmerge_more_branches' : forall B1 B2,
  collapse (Xmerge B1 B2) <> XUndefined -> Xmore_branches (Xmerge B1 B2) B2.
Proof.
intros.
apply collapse_exists in H. destroy H.
elim (collapse_char' B1); intro. induction a.
elim (collapse_char' B2); intro. induction a.
+ rewrite H, p0.
  apply more_branches_X, merge_more_branches' with x0.
  unfold merge. rewrite <- p, <- p0; auto.
+ exfalso. apply Xmerge_inv_inject' in H.
  destroy H. rewrite H, collapse_inject in b.
  apply inject_not_undefined in b; auto.
+ exfalso. apply Xmerge_inv_inject in H.
  destroy H.  rewrite H, collapse_inject in b.
  apply inject_not_undefined in b; auto.
Qed.

End MoreBranches.

Definition more_branches_N (N N':Network) :=
  forall p, more_branches (N p) (N' p).

Notation "N >> N'" := (more_branches_N N N') (at level 50).

Section MoreBranchesN.

Lemma Network_eq_more_branches : forall (N N':Network),
  (N == N') -> N >> N'.
Proof. intros; intro. apply more_branches_refl'; auto. Qed.

Lemma more_branches_N_trans : forall N N' N'',
  N >> N' -> N' >> N'' -> N >> N''.
Proof. intros; intro. eapply more_branches_trans; eauto. Qed.

Lemma SP_To_more_branches_N : forall Defs N1 s N2 s' Defs' N1' tl,
  SP_To Defs N1 s tl N2 s' -> N1' >> N1 -> (forall X, Defs X = Defs' X) ->
  exists N2', SP_To Defs' N1' s tl N2' s' /\ N2' >> N2.
Proof.
intros. rename H1 into HX. induction H.
- generalize (H0 p) (H0 q). rewrite H, H1; intros.
  inversion H4. inversion H5.
  rewrite H12, H14 in H11; clear B'1 H15 x0 H14 p1 H12.
  rewrite H7, H9 in H6; clear p0 H7 e0 H9 B'0 H10. clear H4 H5.
  rename B0 into Bp, B1 into Bq.
  assert (p <> q). intro. rewrite H4, H1 in H; inversion H.
  exists (Network_rm (Network_rm N1' p) q | p[Bp] | q[Bq]); split.
  apply S_Com with Bp Bq; auto. reflexivity.
  intro r. rewrite H2.
  elim (P.eq_dec r p); intro Hp. 2: elim (P.eq_dec r q); intro Hq.
  rewrite Hp, Network_rm_add_2_p, Network_rm_add_2_p; auto.
  rewrite Hq, Network_rm_add_2_q, Network_rm_add_2_q; auto.
  rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
- generalize (H0 p) (H0 q). rewrite H, H1; intros.
  assert (p <> q) as Hpq. intro. rewrite H6, H1 in H; inversion H.
  inversion H4.
  rewrite H7, H9 in H6; clear p0 H7 l H9 B' H10 H4.
  inversion H5.
  + rewrite H7 in H4. rewrite <- H11 in H1. clear p0 H7 Bl' H10 Br H11 H5.
    rename Bl0 into Bl', B0 into Bp.
    exists (Network_rm (Network_rm N1' p) q | p[Bp] | q[Bl']); split.
    apply S_LSel with Bp Bl' mBr; auto. reflexivity.
    intro r. rewrite H2.
    elim (P.eq_dec r p); intro Hp. 2: elim (P.eq_dec r q); intro Hq.
    rewrite Hp, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    rewrite Hq, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
  + rewrite H7 in H4. rewrite <- H11 in H1. clear p0 H7 Bl' H9 Br H11 H5.
    rename Bl0 into Bl', B0 into Bp.
    exists (Network_rm (Network_rm N1' p) q | p[Bp] | q[Bl']); split.
    apply S_LSel with Bp Bl' (Some Br0); auto. reflexivity.
    intro r. rewrite H2.
    elim (P.eq_dec r p); intro Hp. 2: elim (P.eq_dec r q); intro Hq.
    rewrite Hp, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    rewrite Hq, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
- generalize (H0 p) (H0 q). rewrite H, H1; intros.
  assert (p <> q) as Hpq. intro. rewrite H6, H1 in H; inversion H.
  inversion H4.
  rewrite H7, H9 in H6; clear p0 H7 l H9 B' H10 H4.
  inversion H5.
  + rewrite H7 in H4. rewrite <- H10 in H1. clear p0 H7 Br' H10 Bl H11 H5.
    rename Br0 into Br', B0 into Bp.
    exists (Network_rm (Network_rm N1' p) q | p[Bp] | q[Br']); split.
    apply S_RSel with Bp mBl Br'; auto. reflexivity.
    intro r. rewrite H2.
    elim (P.eq_dec r p); intro Hp. 2: elim (P.eq_dec r q); intro Hq.
    rewrite Hp, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    rewrite Hq, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
  + rewrite H7 in H4. rewrite <- H9 in H1. clear p0 H7 Br' H9 Bl H11 H5.
    rename Br0 into Br', B0 into Bp.
    exists (Network_rm (Network_rm N1' p) q | p[Bp] | q[Br']); split.
    apply S_RSel with Bp (Some Bl0) Br'; auto. reflexivity.
    intro r. rewrite H2.
    elim (P.eq_dec r p); intro Hp. 2: elim (P.eq_dec r q); intro Hq.
    rewrite Hp, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    rewrite Hq, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
- generalize (H0 p). rewrite H; intros.
  inversion H4.
  rewrite H6 in H5; clear B2' B1' b0 H6 H7 H9 H4.
  rename B0 into B1', B3 into B2'.
  exists (Network_rm N1' p | p[B1']); split.
  apply S_Then with b B1' B2'; auto. reflexivity.
  intro r. rewrite H2.
  elim (P.eq_dec r p); intro Hp.
  rewrite Hp, Par_proj2, Par_proj2; auto.
  unfold Process, Pid_dec. Peq; auto.
  1,2: apply Network_rm_In.
  rewrite Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto.
  all: unfold Process, Pid_dec; Pneq Hp; auto.
- generalize (H0 p). rewrite H; intros.
  inversion H4.
  rewrite H6 in H5; clear B2' B1' b0 H6 H7 H9 H4.
  rename B0 into B1', B3 into B2'.
  exists (Network_rm N1' p | p[B2']); split.
  apply S_Else with b B1' B2'; auto. reflexivity.
  intro r. rewrite H2.
  elim (P.eq_dec r p); intro Hp.
  rewrite Hp, Par_proj2, Par_proj2; auto.
  unfold Process, Pid_dec. Peq; auto.
  1,2: apply Network_rm_In.
  rewrite Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto.
  all: unfold Process, Pid_dec; Pneq Hp; auto.
- generalize (H0 p). rewrite H; intros.
  inversion H3.
  rewrite H6 in H5; clear X0 H6 H3.
  exists (Network_rm N1' p | p[Defs X]); split.
  apply S_Call; auto. rewrite HX. reflexivity.
  intro r. rewrite H1.
  elim (P.eq_dec r p); intro Hp.
  rewrite Hp, Par_proj2, Par_proj2; auto.
  unfold Process, Pid_dec. Peq. apply more_branches_refl.
  1,2: apply Network_rm_In.
  rewrite Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto.
  all: unfold Process, Pid_dec; Pneq Hp; auto.
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
destroy H5. exists (Build_Program (Procs P1') x).
repeat split; auto.
rewrite (SP_eta P1').
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
  rewrite (SP_eta P1'), (SP_eta x) in H8.
  rewrite (SPP_To_Defs_stable _ _ _ _ _ _ _ H8); auto.
Qed.

End MoreBranchesN.

End SP_Prune.
