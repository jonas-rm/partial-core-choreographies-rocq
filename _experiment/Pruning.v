Require Export Merge.

Section SP_Prune.

Variable Sig : Signature.

Local Definition Pid := pid Sig.
Local Definition Var := var Sig.
Local Definition Value := value Sig.
Local Definition Expr := expr Sig.
Local Definition BExpr := bexpr Sig.
Local Definition RecVar := recvar Sig.
Local Definition Ann := ann Sig.
Local Definition Ev := ev Sig.
Local Definition BEv := bev Sig.

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
Proof.
induction B using Behaviour_ind'; try constructor; auto.
induction mB, mB'; repeat induction a; repeat induction p0; constructor; eauto.
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

Lemma more_branches_char_1 : forall B1 B2,
  more_branches B1 B2 -> merge Sig B1 B2 = inject _ B1.
Proof.
unfold merge; intros.
induction H; simpl; auto;
  try case mBl; try case mBr; repeat induction p0; try induction p1; simpl; intros;
  repeat rewrite eqb_refl;
  try rewrite label_eqb_refl;
  try rewrite IHmore_branches;
  repeat rewrite inject_match;
  simpl; auto.
+ rewrite IHmore_branches1, IHmore_branches2, inject_match, inject_match. auto.
+ rewrite IHmore_branches1, IHmore_branches2.
  case_eq (inject _ B1); case_eq (inject _ B2); simpl; auto; intros;
    try elim (inject_not_undefined _ _ H1);
    elim (inject_not_undefined _ _ H2).
Qed.

Lemma more_branches_char_2 : forall B1 B2,
  merge _ B1 B2 = inject _ B1 -> more_branches B1 B2.
Proof.
unfold merge.
induction B1 using Behaviour_ind'; induction B2 using Behaviour_ind'; simpl;
  try case_eq mB; try case_eq mB'; try case mB0; try case mB'0;
  repeat induction p0; repeat induction p1; repeat induction p2; repeat induction p3;
  simpl;
  intros; try constructor;
  try (inversion H; fail); try (inversion H3; fail).
10,13,16,17,18: exfalso; elim (if_elim _ _ _ _ _ H5); clear H5; intro H';
  inversion_clear H'; repeat rewrite inject_match in H6; inversion H6.
7,10,13,14: elim (if_elim _ _ _ _ _ H5); clear H5; intro H';
  inversion_clear H'; repeat rewrite inject_match in H6; inversion H6;
  rewrite eqb_eq in H5; rewrite H5; constructor.
1,2: elim (if_elim _ _ _ _ _ H); intro H'; inversion_clear H'; clear H;
  [idtac | inversion H1];
  elim (andb_prop _ _ H0); intros; clear H0; rename H into H0;
  elim (andb_prop _ _ H0); intros; clear H0;
  rewrite eqb_eq in H, H2, H3; rewrite H, H2, H3; constructor;
  apply IHB1;
  elim (XUndefined_dec _ (Xmerge _ (inject _ B1) (inject _ B2))); intro;
  [ rewrite a1 in H1; inversion H1
  | rewrite Xmatch_elim in H1; auto;
    inversion H1; auto].
+ elim (if_elim _ _ _ _ _ H); intro H'; inversion_clear H'; clear H.
  2: inversion H1.
  elim (andb_prop _ _ H0); intros; clear H0; rename H into H0;
  elim (andb_prop _ _ H0); intros; clear H0.
  rewrite eqb_eq in H, H2; rewrite label_eqb_eq in H3;
  rewrite H, H2, H3; constructor. apply IHB1.
  elim (XUndefined_dec _ (Xmerge _ (inject _ B1) (inject _ B2))); intro.
  1: rewrite a1 in H1; inversion H1.
  rewrite Xmatch_elim in H1; auto.
  inversion H1; auto.
+ elim (if_elim _ _ _ _ _ H5); intro H'; inversion_clear H'.
  2: inversion H7.
  rewrite H6 in H5; clear H7.
  assert (a = a1 /\ a0 = a2 /\ Xmerge _ (inject _ b1) (inject _ b) = inject _ b1 /\ Xmerge _ (inject _ b2) (inject _ b0) = inject _ b2).
  1: {
    revert H5. case_eq (eqb (Merge.Ann Sig) a2 a0); simpl. 2: discriminate.
    case_eq (eqb (Merge.Ann Sig) a1 a); simpl. all: intros H' H'' H7.
    split. 2: split.
    - symmetry; apply eqb_eq; auto.
    - symmetry; apply eqb_eq; auto.
    - elim (XUndefined_dec _ (Xmerge _ (inject _ b2) (inject _ b0))); intro.
      1: rewrite a3 in H7; inversion H7.
      rewrite Xmatch_elim in H7; auto.
      elim (XUndefined_dec _ (Xmerge _ (inject _ b1) (inject _ b))); intro.
      1: rewrite a3 in H7; inversion H7.
      rewrite Xmatch_elim in H7; auto.
      inversion H7. rewrite H8, H9; auto.
    - revert H7. case (Xmerge _ (inject _ b2) (inject _ b0)); discriminate.
  }
  destroy H7.
  rewrite eqb_eq in H6; rewrite H6, H8, H9.
  constructor; eauto.
+ elim (if_elim _ _ _ _ _ H5); intro H'; inversion_clear H'.
  2: inversion H7.
  rewrite H6 in H5; clear H7.
  rewrite eqb_eq in H6; rewrite H6.
  revert H5. case_eq (eqb (Merge.Ann Sig) a1 a); intro H'; intros.
  2: inversion H5.
  rewrite eqb_eq in H'; rewrite H'.
  constructor.
  eapply H; eauto.
  elim (XUndefined_dec _ (Xmerge _ (inject _ b1) (inject _ b))); intro.
  rewrite a2 in H5; inversion H5.
  rewrite Xmatch_elim, inject_match in H5; auto.
  inversion H5. rewrite H8; auto.
+ elim (if_elim _ _ _ _ _ H5); intro H'; inversion_clear H'.
  2: inversion H7.
  rewrite H6 in H5; clear H7.
  rewrite eqb_eq in H6; rewrite H6.
  revert H5. case_eq (eqb (Merge.Ann Sig) a1 a); intro H'; intros.
  2: rewrite inject_match in H5.
  rewrite eqb_eq in H'; rewrite H'.
  all: revert H5; case_eq (eqb (Merge.Ann Sig) a0 a); intro H''; intros.
  2: rewrite inject_match in H5; inversion H5.
  3: inversion H5.
  all: rewrite eqb_eq in H''; rewrite H''.
  constructor.
  eapply H0; eauto. rewrite inject_match in H5.
  - elim (XUndefined_dec _ (Xmerge _ (inject _ b0) (inject _ b))); intro.
    rewrite a2 in H5; inversion H5.
    rewrite Xmatch_elim in H5; auto.
    inversion H5. rewrite H8; auto.
  - elim (XUndefined_dec _ (Xmerge _ (inject _ b0) (inject _ b))); intro.
    rewrite a2 in H5; inversion H5.
    rewrite Xmatch_elim in H5; auto.
    inversion H5. constructor; eauto.
+ exfalso.
  elim (if_elim _ _ _ _ _ H5); intro H'; inversion_clear H'.
  2: inversion H7.
  rewrite H6 in H5; clear H7.
  rewrite inject_match in H5.
  revert H5. case_eq (eqb (Merge.Ann Sig) a1 a0); intro H'; intros.
  2: inversion H5.
  elim (XUndefined_dec _ (Xmerge _ (inject _ b1) (inject _ b0))); intro.
  rewrite a2 in H5; inversion H5.
  rewrite Xmatch_elim in H5; auto. inversion H5.
+ elim (if_elim _ _ _ _ _ H5); intro H'; inversion_clear H'.
  2: inversion H7.
  rewrite H6 in H5; clear H7.
  rewrite eqb_eq in H6; rewrite H6.
  revert H5. case_eq (eqb (Merge.Ann Sig) a0 a); intro H'; intros.
  2: inversion H5.
  rewrite eqb_eq in H'; rewrite H'.
  constructor.
  eapply H; eauto.
  elim (XUndefined_dec _ (Xmerge _ (inject _ b0) (inject _ b))); intro.
  rewrite a1 in H5; inversion H5.
  rewrite Xmatch_elim in H5; auto.
  inversion H5. rewrite H8; auto.
+ exfalso.
  elim (if_elim _ _ _ _ _ H5); intro H'; inversion_clear H'.
  2: inversion H7.
  rewrite H6 in H5; clear H7.
  rewrite inject_match in H5.
  revert H5. case_eq (eqb (Merge.Ann Sig) a1 a); intro H'; intros.
  2: inversion H5.
  elim (XUndefined_dec _ (Xmerge _ (inject _ b1) (inject _ b))); intro.
  rewrite a2 in H5; inversion H5.
  rewrite Xmatch_elim in H5; auto. inversion H5.
+ elim (if_elim _ _ _ _ _ H5); intro H'; inversion_clear H'.
  2: inversion H7.
  rewrite H6 in H5; clear H7.
  rewrite eqb_eq in H6; rewrite H6.
  revert H5. case_eq (eqb (Merge.Ann Sig) a0 a); intro H'; intros.
  2: inversion H5.
  rewrite eqb_eq in H'; rewrite H'.
  constructor.
  eapply H0; eauto.
  elim (XUndefined_dec _ (Xmerge _ (inject _ b0) (inject _ b))); intro.
  rewrite a1 in H5; inversion H5.
  rewrite Xmatch_elim in H5; auto.
  inversion H5. rewrite H8; auto.
+ elim (if_elim _ _ _ _ _ H); intro H'; inversion_clear H'; clear H.
  2: inversion H1.
  rewrite eqb_eq in H0; rewrite <- H0; clear b0 H0.
  rename B1_1 into Bt, B1_2 into Be, B2_1 into Bt', B2_2 into Be'.
  assert (Xmerge _ (inject _ Bt) (inject _ Bt') = inject _ Bt /\ Xmerge _ (inject _ Be) (inject _ Be') = inject _ Be).
  1: {
    elim (XUndefined_dec _ (Xmerge _ (inject _ Bt) (inject _ Bt'))); intro.
    1: rewrite a in H1; inversion H1. 
    elim (XUndefined_dec _ (Xmerge _ (inject _ Be) (inject _ Be'))); intro.
    1: rewrite a, Xmatch_elim in H1; auto; inversion H1.
    revert H1.
    case (Xmerge _ (inject _ Bt) (inject _ Bt')); case (Xmerge _ (inject _ Be) (inject _ Be'));
      intros; try inversion H1; auto.
  }
  inversion_clear H. constructor; auto.
+ elim (if_elim _ _ _ _ _ H); intro H'; inversion_clear H'; clear H.
  2: inversion H1.
  rewrite eqb_eq in H0; rewrite H0; constructor.
Qed.

Lemma more_branches_char : forall B1 B2,
  more_branches B1 B2 <-> merge _ B1 B2 = inject _ B1.
Proof.
split.
+ apply more_branches_char_1.
+ apply more_branches_char_2.
Qed.

Lemma merge_more_branches : forall B1 B2 B,
  merge _ B1 B2 = inject Sig B -> more_branches B B1.
Proof.
unfold merge; intros.
rename H into Hinj; revert B1 B2 Hinj.
induction B using Behaviour_ind'; simpl; intros.
+ elim (merge_inv_End _ _ _ Hinj); intros.
  rewrite H; constructor.
+ elim (merge_inv_Send _ _ _ _ _ _ _ Hinj); intros.
  rename x into B1'; inversion_clear H.
  rename x into B2'; inversion_clear H0.
  inversion_clear H1.
  rewrite H; constructor; eauto.
+ elim (merge_inv_Recv _ _ _ _ _ _ _ Hinj); intros.
  rename x into B1'; inversion_clear H.
  rename x into B2'; inversion_clear H0.
  inversion_clear H1.
  rewrite H; constructor; eauto.
+ elim (merge_inv_Sel _ _ _ _ _ _ _ Hinj); intros.
  rename x into B1'; inversion_clear H.
  rename x into B2'; inversion_clear H0.
  inversion_clear H1.
  rewrite H; constructor; eauto.
+ revert Hinj. case_eq mB; case_eq mB'; repeat induction p0; repeat induction p1; intros;
  elim (merge_inv_Branching _ _ _ _ _ _ Hinj); intros;
  rename x into Bl'; inversion_clear H3;
  rename x into Bl''; inversion_clear H4;
  rename x into Br'; inversion_clear H3;
  rename x into Br''; inversion_clear H4;
  destroy H5; rewrite H3.
  - eelim H8; eauto; intros; inversion_clear H10.
    eelim H5; eauto; intros; inversion_clear H13.
    case_eq Bl'; case_eq Bl''; case_eq Br'; case_eq Br'';
    repeat induction p0; repeat induction p1; repeat induction p2; repeat induction p3.
    all: try constructor; intros.
    1,2,3,4: eelim H12; eauto; intros H12' H12''; destroy H12''.
    5,6,7,8: eelim H11; eauto; intros H11' H11''; destroy H11'';
             apply inject_inj in H11''; rewrite H18 in H19; inversion H19.
    9,10,11,12: eelim H9; eauto; intros H9' H9''; destroy H9'';
             apply inject_inj in H9''; rewrite H17 in H19; inversion H19.
    1,5,9: eelim H15; eauto; intros H15' H15''; destroy H15''.
    4,7,10: eelim H14; eauto; intros H14' H14''; destroy H14'';
            apply inject_inj in H14''; rewrite H16 in H20; inversion H20.
    7,8,9,10: eelim H10; eauto; intros H10' H10''; destroy H10'';
            apply inject_inj in H10''; rewrite H13 in H20; inversion H20.
    all: try rewrite H12'; try rewrite H15'; try rewrite H11'';
         try rewrite H9''; try rewrite H14''; try rewrite H10''.
    all: try constructor; eauto.
    all: apply more_branches_refl.
  - eelim H8; eauto; intros; inversion_clear H10.
    elim H7; auto; intros. rewrite H10.
    case_eq Bl'; case_eq Bl''; repeat induction p0; repeat induction p1.
    all: try constructor; intros.
    * eelim H12; eauto; intros. destroy H17.
      rewrite H16; constructor. eauto.
    * elim H11; auto; intros. destroy H16. apply inject_inj in H16.
      rewrite H15 in H17; inversion H17.
      rewrite H16; apply more_branches_refl.
  - eelim H5; eauto; intros. inversion_clear H10.
    elim H6; auto; intros. rewrite H10.
    case_eq Br'; case_eq Br''; repeat induction p0; repeat induction p1.
    all: try constructor; intros.
    * eelim H12; eauto; intros. destroy H17.
      rewrite H16; constructor. eauto.
    * elim H11; auto; intros. destroy H16. apply inject_inj in H16.
      rewrite H15 in H17; inversion H17.
      rewrite <- H16; apply more_branches_refl.
  - elim H6; auto; intros. rewrite H9.
    elim H7; auto; intros. rewrite H11.
    constructor.
+ elim (merge_inv_Cond _ _ _ _ _ _ Hinj); intros.
  rename x into Be'; inversion_clear H.
  rename x into Be''; inversion_clear H0.
  rename x into Bt; inversion_clear H.
  rename x into Bt''; destroy H0.
  rewrite H; constructor; eauto.
+ elim (merge_inv_Call _ _ _ _ Hinj); intros.
  rewrite H; constructor; eauto.
Qed.

Lemma merge_more_branches' : forall B1 B2 B,
  merge _ B1 B2 = inject _ B -> more_branches B B2.
Proof.
intros.
apply merge_more_branches with B1.
rewrite merge_comm; auto.
Qed.

Local Ltac lelim X B H H':=
  elim (XUndefined_dec _ X); intro H;
  [ rewrite H in H'; elim (inject_not_undefined _ B); auto
  | rewrite Xmatch_elim in H'; auto ].

Local Ltac lelim2 X Y B H H' H'' := lelim X B H H''; lelim Y B H' H''.

Local Ltac mbsolve B B' := apply more_branches_trans with B;
  [apply merge_more_branches with B' | idtac]; auto.

Local Ltac mbsolve'' B B' := apply more_branches_trans with B;
  [apply merge_more_branches' with B' | idtac]; auto.

Local Ltac mbsolve' H := apply inject_inj in H; rewrite H; auto.

Lemma more_branches_merge_extend : forall B1 B2 B1' B2' B,
  more_branches B1 B1' -> more_branches B2 B2' -> merge _ B1 B2 = inject _ B ->
  exists B', merge _ B1' B2' = inject _ B' /\ more_branches B B'.
Proof.
intros. revert B1 B2 B1' B2' H H0 H1.
induction B using Behaviour_ind'; intros.
+ apply merge_inv_End in H1; destroy H1.
  rewrite H2, H1 in *.
  inversion H; inversion H0.
  exists (End _)%SP; split; auto.
  apply more_branches_refl.
+ apply merge_inv_Send in H1; destroy H1.
  fold (inject _ B) in H1.
  rewrite H2, H3 in *; clear H2 H3 B1 B2.
  inversion H; inversion H0.
  elim (IHB _ _ _ _ H7 H13 H1); intros. destroy H14.
  exists (p!e@!a;x1)%SP; repeat split.
  - unfold merge; simpl. repeat rewrite eqb_refl; simpl.
    unfold merge in H15; rewrite H15.
    rewrite inject_match; auto.
  - constructor; auto.
+ apply merge_inv_Recv in H1; destroy H1.
  fold (inject _ B) in H1.
  rewrite H2, H3 in *; clear H2 H3 B1 B2.
  inversion H; inversion H0.
  elim (IHB _ _ _ _ H7 H13 H1); intros. destroy H14.
  exists (p ? v @? a;x3)%SP; repeat split.
  - unfold merge; simpl. repeat rewrite eqb_refl; simpl.
    unfold merge in H15; rewrite H15.
    rewrite inject_match; auto.
  - constructor; auto.
+ apply merge_inv_Sel in H1; destroy H1.
  fold (inject _ B) in H1.
  rewrite H2, H3 in *; clear H2 H3 B1 B2.
  inversion H; inversion H0.
  elim (IHB _ _ _ _ H7 H13 H1); intros. destroy H14.
  exists (p(+)l@+a;x1)%SP; repeat split.
  - unfold merge; simpl. rewrite label_eqb_refl; repeat rewrite eqb_refl; simpl.
    unfold merge in H15; rewrite H15.
    rewrite inject_match; auto.
  - constructor; auto.
+ induction mB, mB'; try induction a; try induction p0;
  apply merge_inv_Branching in H3; destroy H3.
  all: try fold (inject _ b) in *; try fold (inject _ b0) in *.
  all: rewrite H4, H5 in *; clear H4 H5 B1 B2.
  - eelim H8; eauto; intros. eelim H3; eauto; intros.
    clear H3 H8 H6 H7; destroy H5; destroy H10.
    generalize (H _ _ (eq_refl _)); clear H; intro.
    generalize (H0 _ _ (eq_refl _)); clear H0; intro.
    rename H1 into H1', H2 into H2'.
    induction x.
    1: induction a1; clear H4.
    2: clear H3; elim H4; clear H4; auto; intros B HB;
         destroy HB; apply inject_inj in HB;
         rewrite H1, HB in *; clear b HB x0 H1.
    induction x0.
    1: induction a2; clear H3;
       eelim H5; eauto; clear H5; intros; destroy H2;
       rewrite H1, H3 in *; clear a1 a2 H1 H3; rename H2 into H5.
    2: elim H3; clear H3; auto; intros B HB;
         destroy HB; apply inject_inj in HB;
         rewrite H1, HB in *; clear b HB a1 b1 H1.
    all: induction x1.
    1,3,5: induction a1; clear H9.
    4,5,6: clear H6; elim H9; clear H9; auto; intros B' HB';
         destroy HB'; apply inject_inj in HB';
         rewrite H1, HB' in *; clear b0 HB' x2 H1.
    1,2,3: induction x2.
    1,3,5: induction a2; clear H6;
        eelim H10; eauto; clear H10; intros; destroy H2;
        rewrite H1, H3 in *; clear a1 a2 H1 H3.
    4,5,6: elim H6; clear H6; auto; intros B' HB';
         destroy HB'; apply inject_inj in HB';
         rewrite H1, HB' in *; clear b0 HB' a1 H1.
(* AGH *)
    all: inversion H1'; inversion H2'.
    1,17,25,33,41,45,49,57,61: exists (p & None // None)%SP; split;
      [ unfold merge; simpl; rewrite eqb_refl; auto
      | constructor].
    1,4,16,17,23,26,31,37,41,43,50,53: exists (p & None // Some (a0, Br'))%SP; split;
      [ unfold merge; simpl; rewrite eqb_refl, inject_match; auto
      | constructor; auto ].
    1: mbsolve'' b4 b3.
    1: mbsolve b3 b4.
    1,3: mbsolve'' b1 b.
    1,2: mbsolve b b1.
    1,6,15,19,24,26,30,32,34,36,40,42: exists (p & Some (a,Bl') // None)%SP; split;
      [ unfold merge; simpl; rewrite eqb_refl, inject_match; auto
      | constructor; auto ].
    1,3: mbsolve'' b2 b1.
    1,2: mbsolve b1 b2.
    1: mbsolve'' b2 b1.
    1: mbsolve b1 b2.
    1,3,5,8,13,14,16,18,20,22,24,25,26,27,30,31: exists (p & Some (a,Bl') // Some (a0,Br'))%SP; split;
      [ unfold merge; simpl; rewrite eqb_refl, inject_match, inject_match; auto
      | constructor; auto].
    1,3,13,15: mbsolve'' b2 b1.
    1,4: mbsolve'' b4 b3.
    1,4: mbsolve b3 b4.
    1,2,7,8: mbsolve b1 b2.
    1,3: mbsolve'' b1 b.
    1,2: mbsolve b b1.
    * elim (H0 _ _ _ _ H8 H14 H2); clear H0; intros BR H0; inversion_clear H0 as (HR',HR'').
      unfold merge in HR'.
      exists (p & None // Some (a0,BR))%SP; split.
      unfold merge; simpl; rewrite eqb_refl, eqb_refl, Xmatch_elim;
      rewrite HR'; [ auto | apply inject_not_undefined].
      constructor; auto.
    * elim (H0 _ _ _ _ H8 H16 H2); clear H0; intros BR H0; inversion_clear H0 as (HR',HR'').
      unfold merge in HR'.
      exists (p & Some (a,Bl') // Some (a0,BR))%SP; split.
      unfold merge; simpl; rewrite eqb_refl, eqb_refl, inject_match, Xmatch_elim;
      rewrite HR'; [ auto | apply inject_not_undefined].
      constructor; auto. mbsolve'' b2 b1.
    * elim (H _ _ _ _ H8 H14 H5); clear H; intros BL H; inversion_clear H as (HL',HL'').
      unfold merge in HL'.
      exists (p & Some (a,BL) // None)%SP; split.
      unfold merge; simpl; rewrite eqb_refl, eqb_refl, Xmatch_elim;
      rewrite HL'; [ auto | apply inject_not_undefined].
      constructor; auto.
    * elim (H _ _ _ _ H8 H15 H5); clear H; intros BL H; inversion_clear H as (HL',HL'').
      unfold merge in HL'.
      exists (p & Some (a,BL) // Some (a0,Br'))%SP; split.
      unfold merge; simpl; rewrite eqb_refl, eqb_refl, inject_match, Xmatch_elim;
      rewrite HL'; [ auto | apply inject_not_undefined].
      constructor; auto. mbsolve'' b4 b3.
    * elim (H0 _ _ _ _ H10 H16 H2); clear H0; intros BR H0; inversion_clear H0 as (HR',HR'').
      unfold merge in HR'.
      exists (p & Some (a,Bl') // Some (a0,BR))%SP; split.
      unfold merge; simpl; rewrite eqb_refl, eqb_refl, inject_match, Xmatch_elim;
      rewrite HR'; [ auto | apply inject_not_undefined].
      constructor; auto. mbsolve b1 b2.
    * elim (H _ _ _ _ H9 H16 H5); clear H; intros BL H; inversion_clear H as (HL',HL'').
      unfold merge in HL'.
      exists (p & Some (a,BL) // Some (a0,Br'))%SP; split.
      unfold merge; simpl; rewrite eqb_refl, eqb_refl, inject_match, Xmatch_elim;
      rewrite HL'; [ auto | apply inject_not_undefined].
      constructor; auto. mbsolve b3 b4.
    * elim (H _ _ _ _ H9 H17 H5); clear H; intros BL H; inversion_clear H as (HL',HL'').
      unfold merge in HL'.
      elim (H0 _ _ _ _ H10 H18 H2); clear H0; intros BR H0; inversion_clear H0 as (HR',HR'').
      unfold merge in HR'.
      exists (p & Some (a,BL) // Some (a0,BR))%SP; split.
      unfold merge; simpl; rewrite eqb_refl, eqb_refl, eqb_refl, Xmatch_elim, Xmatch_elim;
      try rewrite HL'; try rewrite HR'; auto. 1,2: apply inject_not_undefined.
      constructor; auto.
    * elim (H0 _ _ _ _ H8 H14 H2); clear H0; intros BR H0; inversion_clear H0 as (HR',HR'').
      unfold merge in HR'.
      exists (p & None // Some (a0,BR))%SP; split.
      unfold merge; simpl; rewrite eqb_refl, eqb_refl, Xmatch_elim;
      rewrite HR'; [ auto | apply inject_not_undefined].
      constructor; auto.
    * elim (H0 _ _ _ _ H10 H16 H2); clear H0; intros BR H0; inversion_clear H0 as (HR',HR'').
      unfold merge in HR'.
      exists (p & Some (a,Bl') // Some (a0,BR))%SP; split.
      unfold merge; simpl; rewrite eqb_refl, eqb_refl, inject_match, Xmatch_elim;
      rewrite HR'; [ auto | apply inject_not_undefined].
      constructor; auto.
    * elim (H0 _ _ _ _ H8 H14 H2); clear H0; intros BR H0; inversion_clear H0 as (HR',HR'').
      unfold merge in HR'.
      exists (p & None // Some (a0,BR))%SP; split.
      unfold merge; simpl; rewrite eqb_refl, eqb_refl, Xmatch_elim;
      rewrite HR'; [ auto | apply inject_not_undefined].
      constructor; auto.
    * elim (H0 _ _ _ _ H8 H16 H2); clear H0; intros BR H0; inversion_clear H0 as (HR',HR'').
      unfold merge in HR'.
      exists (p & Some (a,Bl') // Some (a0,BR))%SP; split.
      unfold merge; simpl; rewrite eqb_refl, eqb_refl, inject_match, Xmatch_elim;
      rewrite HR'; [ auto | apply inject_not_undefined].
      constructor; auto.
    * elim (H _ _ _ _ H7 H14 H5); clear H; intros BL H; inversion_clear H as (HL',HL'').
      unfold merge in HL'.
      exists (p & Some (a,BL) // None)%SP; split.
      unfold merge; simpl; rewrite eqb_refl, eqb_refl, Xmatch_elim;
      rewrite HL'; [ auto | apply inject_not_undefined].
      constructor; auto.
    * elim (H _ _ _ _ H8 H16 H5); clear H; intros BL H; inversion_clear H as (HL',HL'').
      unfold merge in HL'.
      exists (p & Some (a,BL) // Some (a0,Br'))%SP; split.
      unfold merge; simpl; rewrite eqb_refl, eqb_refl, inject_match, Xmatch_elim;
      rewrite HL'; [ auto | apply inject_not_undefined].
      constructor; auto.
    * elim (H _ _ _ _ H7 H14 H5); clear H; intros BL H; inversion_clear H as (HL',HL'').
      unfold merge in HL'.
      exists (p & Some (a,BL) // None)%SP; split.
      unfold merge; simpl; rewrite eqb_refl, eqb_refl, Xmatch_elim;
      rewrite HL'; [ auto | apply inject_not_undefined].
      constructor; auto.
    * elim (H _ _ _ _ H7 H15 H5); clear H; intros BL H; inversion_clear H as (HL',HL'').
      unfold merge in HL'.
      exists (p & Some (a,BL) // Some (a0,Br'))%SP; split.
      unfold merge; simpl; rewrite eqb_refl, eqb_refl, inject_match, Xmatch_elim;
      rewrite HL'; [ auto | apply inject_not_undefined].
      constructor; auto.
  - clear H3 H6. elim H7; auto; intros.
    rewrite H3, H4 in *; clear x1 x2 H3 H4 H7.
    eelim H8; eauto; intros. destroy H4.
    generalize (H _ _ (eq_refl _)); clear H H0; intro.
    rename H1 into H1', H2 into H2'.
    induction x.
    1: induction a0; clear H8.
    2: clear H5 H8; elim H3; clear H3; auto; intros B HB;
         destroy HB; apply inject_inj in HB;
         rewrite H0, HB in *; clear b HB x0 H0.
    induction x0.
    1: induction a1; clear H3 H5;
       eelim H4; eauto; clear H4; intros; destroy H1;
       rewrite H0, H2 in *; clear a1 a0 H0 H2; rename H1 into H4.
    2: elim H5; clear H5; auto; intros B HB;
         destroy HB; apply inject_inj in HB;
         rewrite H0, HB in *; clear b HB a0 b0 H0 H3 H4.
    all: inversion H1'; inversion H2'.
    1,5,7: exists (p & None // None)%SP; split;
      [ unfold merge; simpl; rewrite eqb_refl; auto
      | constructor].
    1,2,4,5: exists (p & Some (a,Bl') // None)%SP; split;
      [ unfold merge; simpl; rewrite eqb_refl, inject_match; auto
      | constructor; auto ].
    1: mbsolve'' b1 b0.
    1: mbsolve b0 b1.
    elim (H _ _ _ _ H6 H12 H4); clear H; intros BL H; inversion_clear H as (HL',HL'').
    unfold merge in HL'.
    exists (p & Some (a,BL) // None)%SP; split.
    unfold merge; simpl; rewrite eqb_refl, eqb_refl, Xmatch_elim;
    rewrite HL'; [ auto | apply inject_not_undefined].
    constructor; auto.
  - clear H7 H8. elim H6; auto; intros.
    rewrite H4, H5 in *; clear x x0 H4 H5 H6.
    eelim H3; eauto; intros. destroy H5.
    generalize (H0 _ _ (eq_refl _)); clear H H0; intro.
    rename H1 into H1', H2 into H2'.
    induction x1.
    1: induction a0; clear H4.
    2: clear H3 H6; elim H4; clear H4; auto; intros B HB;
         destroy HB; apply inject_inj in HB;
         rewrite H0, HB in *; clear b HB x2 H0.
    induction x2.
    1: induction a1; clear H3 H6;
       eelim H5; eauto; clear H5; intros; destroy H1;
       rewrite H0, H2 in *; clear a1 a0 H0 H2; rename H1 into H4.
    2: elim H6; clear H6; auto; intros B HB;
         destroy HB; apply inject_inj in HB;
         rewrite H0, HB in *; clear b HB a0 b0 H0 H3 H5.
    all: inversion H1'; inversion H2'.
    1,5,7: exists (p & None // None)%SP; split;
      [ unfold merge; simpl; rewrite eqb_refl; auto
      | constructor].
    1,2,4,5: exists (p & None // Some (a,Br'))%SP; split;
      [ unfold merge; simpl; rewrite eqb_refl, inject_match; auto
      | constructor; auto ].
    1: mbsolve'' b1 b0.
    1: mbsolve b0 b1.
    elim (H _ _ _ _ H6 H12 H4); clear H; intros BR H; inversion_clear H as (HR',HR'').
    unfold merge in HR'.
    exists (p & None // Some (a,BR))%SP; split.
    unfold merge; simpl; rewrite eqb_refl, eqb_refl, Xmatch_elim;
    rewrite HR'; [ auto | apply inject_not_undefined].
    constructor; auto.
  - elim H6; elim H7; intros; auto.
    rewrite H4, H5, H9, H10 in *.
    inversion H1; inversion H2.
    eexists; repeat split; eauto.
    rewrite <- H15.
    unfold merge; simpl. rewrite eqb_refl; auto.
+ apply merge_inv_Cond in H1; destroy H1.
  fold (inject _ B2) in H1; fold (inject _ B1) in H4.
  rewrite H2, H3 in *; clear H2 H3 B0 B3.
  inversion H; inversion H0.
  elim (IHB1 _ _ _ _ H7 H13 H4); intros. destroy H15.
  elim (IHB2 _ _ _ _ H8 H14 H1); intros. destroy H17.
  exists (If b Then x3 Else x4)%SP; repeat split.
  - unfold merge; simpl. rewrite eqb_refl; simpl.
    unfold merge in H16, H18; rewrite H16, H18.
    case_eq (inject _ x3); case_eq (inject _ x4); auto; intros.
    all: try (elim (inject_not_undefined _ x4); auto; fail).
    all: try (elim (inject_not_undefined _ x3); auto; fail).
  - constructor; auto.
+ apply merge_inv_Call in H1; destroy H1.
  rewrite H2, H1 in *; clear B1 B2 H1 H2.
  inversion H; inversion H0.
  exists (Call Sig X); split.
  - unfold merge; simpl; rewrite eqb_refl; auto.
  - apply more_branches_refl.
Qed.

Open Scope SP.

Lemma more_branches_merge : forall B B1 B2,
  more_branches B B1 -> more_branches B B2 ->
  exists B', merge _ B1 B2 = inject _ B' /\ more_branches B B'.
Proof.
induction B using Behaviour_ind'; intros.
+ inversion H; inversion H0.
  exists bnil%SP; split; auto. constructor.
+ inversion H; inversion H0.
  elim (IHB _ _ H6 H12); intros. destroy H13.
  exists (p!e@!a; x)%SP; split.
  - unfold merge; simpl; repeat rewrite eqb_refl.
    unfold merge in H14; rewrite H14, Xmatch_elim; auto.
    apply inject_not_undefined.
  - constructor; auto.
+ inversion H; inversion H0.
  elim (IHB _ _ H6 H12); intros. destroy H13.
  exists (p ? v @? a; x1)%SP; split.
  - unfold merge; simpl. repeat rewrite eqb_refl.
    unfold merge in H14; rewrite H14, Xmatch_elim; auto.
    apply inject_not_undefined.
  - constructor; auto.
+ inversion H; inversion H0.
  elim (IHB _ _ H6 H12); intros. destroy H13.
  exists (p(+)l@+a; x)%SP; split.
  - unfold merge; simpl. rewrite eqb_refl, label_eqb_refl, eqb_refl.
    unfold merge in H14; rewrite H14, Xmatch_elim; auto.
    apply inject_not_undefined.
  - constructor; auto.
+ inversion H1; inversion H2. all: unfold merge; simpl; rewrite eqb_refl.
  - exists (p & None // None); split; auto.
    constructor.
  - exists (p & None // Some (a,Br')); split.
    rewrite Xmatch_elim; auto. apply inject_not_undefined.
    constructor; auto.
  - exists (p & Some (a,Bl') // None); split.
    rewrite Xmatch_elim; auto. apply inject_not_undefined.
    constructor; auto.
  - exists (p & Some (a,Bl') // Some (a',Br')); split.
    repeat rewrite Xmatch_elim; auto. 1,2: apply inject_not_undefined.
    constructor; auto.
  - exists (p & None // Some (a,Br')); split.
    rewrite Xmatch_elim; auto. apply inject_not_undefined.
    constructor; auto.
  - rewrite <- H6 in H11; inversion H11.
    rewrite H15 in H12.
    elim H0 with a Br Br' Br'0; auto. intros. destroy H13.
    exists (p & None // Some (a,x)); split.
    unfold merge in H16; rewrite eqb_refl, H16, Xmatch_elim.
    simpl; auto. apply inject_not_undefined.
    constructor; auto.
  - repeat rewrite Xmatch_elim. 2,3: apply inject_not_undefined.
    exists (p & Some (a0,Bl') // Some (a,Br')); split; auto.
    constructor; auto.
  - rewrite Xmatch_elim. 2: apply inject_not_undefined.
    rewrite <- H6 in H11; inversion H11.
    rewrite H16 in H13.
    elim H0 with a Br Br' Br'0; auto. intros. destroy H14.
    unfold merge in H17; rewrite eqb_refl, H17, Xmatch_elim.
    2: apply inject_not_undefined.
    exists (p & Some (a0,Bl') // Some (a,x)); split; auto.
    constructor; auto.
  - rewrite Xmatch_elim. 2: apply inject_not_undefined.
    exists (p & Some (a,Bl') // None); split; auto.
    constructor; auto.
  - repeat rewrite Xmatch_elim. 2,3: apply inject_not_undefined.
    exists (p & Some (a,Bl') // Some (a0,Br')); split; auto.
    constructor; auto.
  - rewrite <- H5 in H10. inversion H10.
    rewrite H15 in H12.
    elim H with a Bl Bl' Bl'0; auto. intros. destroy H13.
    unfold merge in H16; rewrite eqb_refl, H16, Xmatch_elim.
    2: apply inject_not_undefined.
    exists (p & Some (a,x) // None); split; auto.
    constructor; auto.
  - rewrite <- H5 in H9. inversion H9.
    rewrite H16 in H12.
    elim H with a Bl Bl' Bl'0; auto. intros. destroy H14.
    unfold merge in H17; rewrite eqb_refl, H17, Xmatch_elim, Xmatch_elim.
    2,3: apply inject_not_undefined.
    exists (p & Some (a,x) // Some (a',Br')); split; auto.
    constructor; auto.
  - repeat rewrite Xmatch_elim. 2,3: apply inject_not_undefined.
    exists (p & Some (a,Bl') // Some (a',Br')); split; auto.
    constructor; auto.
  - rewrite Xmatch_elim. 2: apply inject_not_undefined.
    rewrite <- H6 in H12; inversion H12.
    rewrite H16 in H13.
    elim H0 with a' Br Br' Br'0; auto. intros. destroy H14.
    unfold merge in H17; rewrite eqb_refl, H17, Xmatch_elim.
    2: apply inject_not_undefined.
    exists (p & Some (a,Bl') // Some (a',x)); split; auto.
    constructor; auto.
  - rewrite <- H4 in H11. inversion H11.
    rewrite H16 in H13.
    elim H with a Bl Bl' Bl'0; auto. intros. destroy H14.
    unfold merge in H17; rewrite eqb_refl, H17, Xmatch_elim, Xmatch_elim.
    2,3: apply inject_not_undefined.
    exists (p & Some (a,x) // Some (a',Br')); split; auto.
    constructor; auto.
  - rewrite <- H4 in H10. inversion H10.
    rewrite H17 in H13.
    elim H with a Bl Bl' Bl'0; auto. intros. destroy H15.
    rewrite <- H6 in H12. inversion H12.
    rewrite H21 in H14.
    elim H0 with a' Br Br' Br'0; auto. intros. destroy H19.
    unfold merge in H18, H22; repeat rewrite eqb_refl.
    rewrite H18, H22, Xmatch_elim, Xmatch_elim.
    2,3: apply inject_not_undefined.
    exists (p & Some (a,x) // Some (a',x0)); split; auto.
    constructor; auto.
+ inversion H; inversion H0.
  elim (IHB1 B1' B1'0); auto; intros. destroy H13.
  elim (IHB2 B2' B2'0); auto; intros. destroy H15.
  exists (If b Then x Else x0); split. unfold merge.
  simpl (inject _ (If b Then B1' Else B2')). simpl (inject _ (If b Then B1'0 Else B2'0)).
  rewrite Xmerge_Cond_inv.
  - simpl. rewrite <- H14, <- H16; auto.
  - unfold merge in H14; rewrite H14. apply inject_not_undefined.
  - unfold merge in H16; rewrite H16. apply inject_not_undefined.
  - constructor; auto.
+ inversion H; inversion H0.
  exists (Call _ X); split.
  unfold merge; simpl. rewrite eqb_refl; auto.
  constructor.
Qed.

(** The same relation on extended behaviours, and corresponding lemmas. *)
Definition Xmore_branches XB XB' := exists B B',
  XB = inject _ B /\ XB' = inject _ B' /\ more_branches B B'.

Lemma more_branches_X : forall B B',
 more_branches B B' -> Xmore_branches (inject _ B) (inject _ B').
Proof. red. eauto. Qed.

Lemma X_more_branches : forall B B',
 Xmore_branches (inject _ B) (inject _ B') -> more_branches B B'.
Proof.
intros.
destroy H.
apply inject_inj in H0; apply inject_inj in H1.
rewrite H0, H1; auto.
Qed.

Lemma Xmore_branches_refl : forall X B, X = inject _ B ->
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
  Xmore_branches B B1 -> Xmore_branches B B2 -> Xmore_branches B (Xmerge _ B1 B2).
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
  Xmerge _ B1 B2 = inject _ B ->
  Xmore_branches (Xmerge _ B1 B2) (Xmerge _ B1' B2').
Proof.
intros. destroy H. destroy H0.
rewrite H2, H4 in H1.
elim (more_branches_merge_extend _ _ _ _ _ H H0 H1); intros.
destroy H6.
rewrite H2, H3, H4, H5.
eexists; eexists; repeat split; eauto.
Qed.

Lemma Xmore_branches_char : forall B1 B2,
  Xmore_branches B1 B2 <-> (collapse _ B1 <> XUndefined _ /\ Xmerge _ B1 B2 = B1).
Proof.
split; intros; destroy H.
+ rewrite H0, H1, collapse_inject; split.
  apply inject_not_undefined.
  apply more_branches_char; auto.
+ elim (collapse_char' _ B2); intro H2.
  destroy H2. apply collapse_exists in H0. destroy H0.
  exists x0, x; repeat split; auto.
  rewrite more_branches_char.
  unfold merge. rewrite <- H0, <- H2; auto.
  apply collapse_merge' with Sig B1 B2 in H2.
  rewrite H in H2. elim H0; auto.
Qed.

Lemma Xmerge_more_branches : forall B1 B2,
  collapse _ (Xmerge _ B1 B2) <> XUndefined _ -> Xmore_branches (Xmerge _ B1 B2) B1.
Proof.
intros.
apply collapse_exists in H. destroy H.
elim (collapse_char' _ B1); intro. induction a.
elim (collapse_char' _ B2); intro. induction a.
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
  collapse _ (Xmerge _ B1 B2) <> XUndefined _ -> Xmore_branches (Xmerge _ B1 B2) B2.
Proof.
intros.
apply collapse_exists in H. destroy H.
elim (collapse_char' _ B1); intro. induction a.
elim (collapse_char' _ B2); intro. induction a.
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
  Net _ P1' >> Net _ P1 -> (forall X, Procs _ P1 X = Procs _ P1' X) ->
  SPP_To Sig (P1,s) tl (P2,s') ->
  exists P2', SPP_To _ (P1',s) tl (P2',s') /\ Net _ P2' >> Net _ P2
    /\ forall X, Procs _ P2 X = Procs _ P2' X.
Proof.
intros.
inversion H1.
apply SP_To_more_branches_N with (Defs':= Procs _ P1') (N1':=Net _ P1') in H5; auto.
2: replace N with (Net _ P1); auto; rewrite <- H2; auto.
destroy H5. exists (Build_Program _ (Procs _ P1') x).
repeat split; auto.
rewrite (SP_eta _ P1').
constructor; auto.
replace Defs with (Procs _ P1); auto.
rewrite <- H2; auto.
intro. rewrite <- H0, <- H2; auto.
Qed.

Lemma SPP_ToStar_more_branches_N : forall P1 s P2 s' P1' tl,
  Net _ P1' >> Net _ P1 -> (forall X, Procs _ P1 X = Procs _ P1' X) ->
  SPP_ToStar _ (P1,s) tl (P2,s') ->
  exists P2', SPP_ToStar _ (P1',s) tl (P2',s') /\ Net _ P2' >> Net _ P2
  /\ forall X, Procs _ P1' X = Procs _ P2' X.
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
  intro. transitivity (Procs _ x X); auto.
  rewrite (SP_eta _ P1'), (SP_eta _ x) in H8.
  rewrite (SPP_To_Defs_stable _ _ _ _ _ _ _ _ H8); auto.
Qed.

End MoreBranchesN.

End SP_Prune.

Notation "N >> N'" := (more_branches_N _ N N') (at level 50).
