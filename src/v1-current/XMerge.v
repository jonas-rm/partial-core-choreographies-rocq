Require Export Merge.

Ltac collapse_check B B' H :=
  assert ({ collapse B = XUndefined } + { collapse B' = XUndefined });
  [ elim (XUndefined_dec _ (collapse B)); auto; intros;
    elim (XUndefined_dec _ (collapse B')); auto; intros;
    do 2 rewrite Xmatch_elim in H; auto; inversion H | idtac].

Ltac case_eq_dec t1 t2 H := case (eq_dec t1 t2); intro H;
    [rewrite <- eqb_eq in H | rewrite <- eqb_neq in H]; rewrite H; auto.

Section XMerge.

Variable Sig : Signature.

Local Definition Pid := XBehaviour.Pid Sig.
Local Definition Var := XBehaviour.Var Sig.
Local Definition Value := XBehaviour.Value Sig.
Local Definition Expr := XBehaviour.Expr Sig.
Local Definition BExpr := XBehaviour.BExpr Sig.
Local Definition RecVar := XBehaviour.RecVar Sig.
Local Definition Ann := XBehaviour.Ann Sig.
Local Definition Ev := XBehaviour.Ev Sig.
Local Definition BEv := XBehaviour.BEv Sig.

(** ** Properties of [Xmerge]
  This section contains properties of [Xmerge] that are needed for some later proofs.
  [Xmerge] is also associative, but the proof is too large and is maintained separately.
*)

Lemma collapse_merge : forall (B B':XBehaviour Sig),
  collapse B = XUndefined -> collapse (B [[\/]] B') = XUndefined.
Proof.
XBDInduction B B'; auto; simpl; intros.
4,5,6,7: inversion H.
all: try not_XUndef_with (collapse B) HB H.
all: try case_eq_dec p p0 Hpp0.
+ case_eq_dec e e0 Hee0. case_eq_dec a a0 Haa0.
  simpl. not_XUndef (B [[\/]] B') HX.
  simpl; rewrite IHB; auto.
+ case_eq_dec v v0 Hvv0. case_eq_dec a a0 Haa0.
  simpl. not_XUndef (B [[\/]] B') HX.
  simpl; rewrite IHB; auto.
+ case_eq_dec l l0 Hll0. case_eq_dec a a0 Haa0.
  simpl. not_XUndef (B [[\/]] B') HX.
  simpl; rewrite IHB; auto.
+ not_XUndef B HB'.
  simpl; rewrite HB; auto.
+ case_eq_dec a a0 Haa0.
  not_XUndef (B [[\/]] B') HX.
  simpl; rewrite IHB; auto.
+ not_XUndef B HB'. not_XUndef B' HB''.
  simpl; rewrite HB; auto.
+ case_eq_dec a a0 Haa0.
  not_XUndef (B [[\/]] B'1) HB'. not_XUndef B'2 HB''.
  simpl; rewrite IHB; auto.
+ not_XUndef B HB'.
  simpl; rewrite HB; auto.
+ not_XUndef B' HB'. not_XUndef B HB''.
  simpl. rewrite HB; auto.
  case (collapse B'); auto.
+ case_eq_dec a a0 Haa0. 
  not_XUndef (B [[\/]] B') HX.
  simpl; rewrite IHB; auto.
+ not_XUndef B'1 HB'.
  case_eq_dec a a' Haa'.
  not_XUndef (B [[\/]] B'2) HB''.
  simpl. rewrite IHB; auto.
  case (collapse B'1); auto.
+ not_XUndef B1 HB'. not_XUndef B2 HB''.
+ case_eq_dec a a0 Haa0.
  not_XUndef (B1 [[\/]] B') HB'. not_XUndef B2 HB''.
  collapse_check B1 B2 H. inversion_clear H0; simpl.
  rewrite IHB1; auto.
  rewrite H1; auto. case (collapse (B1 [[\/]] B')); auto.
+ not_XUndef B1 HB'. case_eq_dec a' a0 Ha'a0.
  not_XUndef (B2 [[\/]] B') HB''.
  collapse_check B1 B2 H. inversion_clear H0; simpl.
  rewrite H1; auto. rewrite IHB2; auto.
  case (collapse B1); auto.
+ case_eq_dec a a0 Haa0. not_XUndef (B1 [[\/]] B'1) HB'.
  case_eq_dec a' a'0 Ha'a'0. not_XUndef (B2 [[\/]] B'2) HB''.
  collapse_check B1 B2 H. inversion_clear H0; simpl.
  rewrite IHB1; auto.
  rewrite IHB2; auto. case (collapse (B1 [[\/]] B'1)); auto.
+ case_eq_dec b b0 Hbb0.
  collapse_check B1 B2 H. clear H IHB'1 IHB'2.
  inversion_clear H0.
  - generalize (IHB1 B'1 H); clear IHB1 IHB2.
    case (B1 [[\/]] B'1); simpl; intros; auto.
    1,7: inversion H0.
    1,2,3: elim (XUndefined_dec _ (collapse x)); intros;
      [ case (B2 [[\/]] B'2); simpl; try rewrite a; auto
      | rewrite Xmatch_elim in H0; auto; inversion H0 ].
    * revert H0. opt_elim o p; opt_elim o0 p; intros.
      4: inversion H2.
      2,3: elim (XUndefined_dec _ (collapse b1)); intros;
        [ case (B2 [[\/]] B'2); simpl; try rewrite a0; auto
        | rewrite Xmatch_elim in H2; auto; inversion H2 ].
      collapse_check b1 b2 H2.
      inversion_clear H3.
      case (B2 [[\/]] B'2); simpl; try rewrite H4; auto.
      case (B2 [[\/]] B'2); simpl; case (collapse b1); try rewrite H4; auto.
    * collapse_check x x0 H0. clear H0.
      inversion_clear H1.
      case (B2 [[\/]] B'2); simpl; try rewrite H0; auto.
      case (B2 [[\/]] B'2); simpl; case (collapse x); try rewrite H0; auto.
  - generalize (IHB2 B'2 H); clear IHB1 IHB2.
    case (B2 [[\/]] B'2); simpl; intros; auto.
    1,7: inversion H0.
    6: case (B1 [[\/]] B'1); auto.
    1,2,3: elim (XUndefined_dec _ (collapse x)); intros;
      [ case (B1 [[\/]] B'1); simpl; try rewrite H0; auto;
        intros; try opt_elim o p; try opt_elim o0 p;
          try case (collapse x0); try case (collapse x1);
          try case (collapse b1); try case (collapse b2); auto
      | rewrite Xmatch_elim in H0; auto; inversion H0].
    * revert H0. opt_elim o p; opt_elim o0 p; intros.
      4: inversion H2.
      2,3: elim (XUndefined_dec _ (collapse b1)); intros;
      [ case (B1 [[\/]] B'1); simpl; try rewrite a0; auto;
        intros; try case o1, o2; try induction p; try induction p0;
          try case (collapse x); try case (collapse x0);
          try case (collapse b2); try case (collapse b3); auto
      | rewrite Xmatch_elim in H2; auto; inversion H2].
      collapse_check b1 b2 H2. clear H2.
      inversion_clear H3.
      case (B1 [[\/]] B'1); simpl; try rewrite H2; auto;
        intros; try case o1, o2; try induction p; try induction p0;
          try case (collapse x); try case (collapse x0);
          try case (collapse b3); try case (collapse b4); auto.
      case (B1 [[\/]] B'1); simpl; try rewrite H2; auto;
        intros; try case o1, o2; try induction p; try induction p0;
          try case (collapse x); try case (collapse x0);
          try case (collapse b1); try case (collapse b3); try case (collapse b4); auto.
    * collapse_check x x0 H0. clear H0.
      inversion_clear H1.
      case (B1 [[\/]] B'1); simpl; try rewrite H0; auto;
        intros; try case o, o0; try induction p; try induction p0;
          try case (collapse x0); try case (collapse x1); try case (collapse x2);
          try case (collapse b1); try case (collapse b2); auto.
      case (B1 [[\/]] B'1); simpl; try rewrite H0; auto;
        intros; try case o, o0; try induction p; try induction p0;
          try case (collapse x); try case (collapse x1); try case (collapse x2);
          try case (collapse b1); try case (collapse b2); auto.
+ simpl; intros. inversion H.
Qed.

Lemma collapse_merge' : forall (B B':XBehaviour Sig),
  collapse B' = XUndefined -> collapse (B [[\/]] B') = XUndefined.
Proof. intros. rewrite Xmerge_comm. apply collapse_merge; auto. Qed.

Lemma Xmerge_idempotent : forall (B:XBehaviour Sig),
  collapse B <> XUndefined -> B [[\/]] B = B.
Proof.
intros. elim (collapse_char' _ B). 2: tauto.
intro. inversion_clear a. rewrite H0.
fold (x [\/] x). apply merge_idempotent.
Qed.

Ltac eq_dec_inj_elim t1 t2 H H' := case (eq_dec t1 t2); intro H;
    [rewrite <- eqb_eq in H | rewrite <- eqb_neq in H]; rewrite H in H'; simpl in H';
    [idtac | elim (inject_not_undefined _ _ H')].

Local Ltac Undef_elim x H' H :=
    elim (XUndefined_dec _ x); intro H';
    [ rewrite H' in H; elim (inject_not_undefined _ _ H)
    | rewrite Xmatch_elim in H; auto].

Local Ltac opt_kill B H H' o o' p :=
  revert H; case B; intros; inversion H;
  revert H'; opt_elim o p; opt_elim o' p; try discriminate.

Open Scope SP_scope.

Lemma Xmerge_inv_inject : forall (B1 B2:XBehaviour Sig) B,
  B1 [[\/]] B2 = inject B -> exists B', B1 = inject B'.
Proof.
intros. symmetry in H.
revert B1 B2 B H.
XBDInduction B1 B2; simpl; intros;
try (elim (inject_not_undefined _ _ H); auto; fail).
all: try eq_dec_inj_elim p p0 Hpp0 H.
+ exists (End _); auto.
+ eq_dec_inj_elim e e0 Hee0 H.
  eq_dec_inj_elim a a0 Haa0 H.
  Undef_elim (B1 [[\/]] B2) H' H.
  revert H. case B; intros; inversion H.
  2: revert H1; opt_elim o p0; opt_elim o0 p1; discriminate.
  elim IHB1 with B2 b; auto. intros.
  exists (p!e@!a;x). rewrite H0; auto.
+ eq_dec_inj_elim v v0 Hvv0 H.
  eq_dec_inj_elim a a0 Haa0 H.
  Undef_elim (B1 [[\/]] B2) H' H.
  revert H. case B; intros; inversion H.
  2: revert H1; opt_elim o p0; opt_elim o0 p1; discriminate.
  elim IHB1 with B2 b; auto. intros.
  exists (p ? v@?a;x). rewrite H0; auto.
+ eq_dec_inj_elim l l0 Hll0 H.
  eq_dec_inj_elim a a0 Haa0 H.
  Undef_elim (B1 [[\/]] B2) H' H.
  revert H. case B; intros; inversion H.
  2: revert H1; opt_elim o p1; opt_elim o0 p1; discriminate.
  elim IHB1 with B2 b; auto. intros.
  exists (p(+)l@+a;x). rewrite H0; auto.
+ exists (p & None // None); auto.
+ exists (p & None // None); auto.
+ exists (p & None // None); auto.
+ exists (p & None // None); auto.
+ Undef_elim B1 H' H; eauto.
+ eq_dec_inj_elim a a0 Haa0 H.
  Undef_elim (B1 [[\/]] B2) H' H.
  revert H. case B; intros; inversion H.
  revert H1; opt_elim o p1; opt_elim o0 p1; try discriminate.
  intros. inversion H2.
  elim IHB1 with B2 b; auto. intros.
  exists (p & Some (a,x) // None). rewrite H3; auto.
+ Undef_elim B1 H' H.
  Undef_elim B2 H'' H.
  opt_kill B H H1 o o0 p1.
  intros. inversion H2.
  exists (p & Some (a,b) // None); auto.
+ eq_dec_inj_elim a a0 Haa0 H.
  Undef_elim (B1 [[\/]] B2_1) H' H.
  Undef_elim B2_2 H'' H.
  opt_kill B H H1 o o0 p1.
  intros. inversion H2.
  elim IHB1 with B2_1 b; auto. intros.
  exists (p & Some (a,x) // None). rewrite H3; auto.
+ Undef_elim B1 H' H; eauto.
+ Undef_elim B2 H' H.
  Undef_elim B1 H'' H.
  opt_kill B H H1 o o0 p1.
  intros. inversion H2.
  exists (p & None // Some (a,b0)); auto.
+ eq_dec_inj_elim a a0 Haa0 H.
  Undef_elim (B1 [[\/]] B2) H' H.
  opt_kill B H H1 o o0 p1.
  intros. inversion H2.
  elim IHB1 with B2 b; auto. intros.
  exists (p & None // Some (a,x)). rewrite H3; auto.
+ Undef_elim B2_1 H' H.
  eq_dec_inj_elim a a' Haa' H.
  Undef_elim (B1 [[\/]] B2_2) H'' H.
  opt_kill B H H1 o o0 p1.
  intros. inversion H2.
  elim IHB1 with B2_2 b0; auto. intros.
  exists (p & None // Some (a,x)). rewrite H3; auto.
+ Undef_elim B1_1 H' H.
  Undef_elim B1_2 H'' H; eauto.
+ eq_dec_inj_elim a a0 Haa0 H.
  Undef_elim (B1_1 [[\/]] B2) H' H.
  Undef_elim B1_2 H'' H.
  opt_kill B H H1 o o0 p1.
  intros. inversion H2.
  elim IHB1_1 with B2 b; auto. intros.
  exists (p & Some (a,x) // Some (a',b0)). rewrite H3; auto.
+ Undef_elim B1_1 H' H.
  eq_dec_inj_elim a' a0 Ha'a0 H.
  Undef_elim (B1_2 [[\/]] B2) H'' H.
  opt_kill B H H1 o o0 p1.
  intros. inversion H2.
  elim IHB1_2 with B2 b0; auto. intros.
  exists (p & Some (a,b) // Some (a',x)). rewrite H3; auto.
+ eq_dec_inj_elim a a0 Haa0 H.
  Undef_elim (B1_1 [[\/]] B2_1) H' H.
  eq_dec_inj_elim a' a'0 Ha'a'0 H.
  Undef_elim (B1_2 [[\/]] B2_2) H'' H.
  opt_kill B H H1 o o0 p1.
  intros; inversion H2.
  elim IHB1_1 with B2_1 b; auto. elim IHB1_2 with B2_2 b0; auto. intros.
  exists (p & Some (a,x0) // Some (a',x)). rewrite H3, H9; auto.
+ eq_dec_inj_elim b b0 Hbb0 H. clear Hbb0.
  clear IHB2_1 IHB2_2.
  elim (collapse_char' _ (B1_1 [[\/]] B2_1)); intros.
  elim (collapse_char' _ (B1_2 [[\/]] B2_2)); intros.
  destroy a; destroy a0. rename x into B1, x0 into B2, a into HB1, a0 into HB2.
  elim IHB1_1 with B2_1 B1; auto. intros.
  elim IHB1_2 with B2_2 B2; auto. intros.
  clear IHB1_1 IHB1_2.
  1: exists (If b Then x Else x0); rewrite H1, H0; auto.
  all: assert (collapse (XCond b (B1_1 [[\/]] B2_1) (B1_2 [[\/]] B2_2)) = XUndefined).
  1,3: simpl; rewrite b1; auto.
  1: case collapse; auto.
  clear a. all: clear b1.
  - assert (inject B = collapse (XCond b (B1_1 [[\/]] B2_1) (B1_2 [[\/]] B2_2))).
    rewrite <- collapse_inject, H. case Xmerge; case Xmerge; simpl; auto.
    all: intros.
    4: opt_elim o p; opt_elim o0 p; auto.
    4,5,6: rename b1 into x. 4: rename b2 into x0.
    1,2,3,4,5,6,7: case (collapse x); auto; case (collapse x0); auto.
    elim (inject_not_undefined _ B). etransitivity; eauto.
  - assert (inject B = collapse (XCond b (B1_1 [[\/]] B2_1) (B1_2 [[\/]] B2_2))).
    rewrite <- collapse_inject, H. case Xmerge; case Xmerge; simpl; auto.
    all: intros.
    4: opt_elim o p; opt_elim o0 p; auto.
    4,5,6: rename b1 into x. 4: rename b2 into x0.
    1,2,3,4,5,6,7: case (collapse x); auto; case (collapse x0); auto.
    elim (inject_not_undefined _ B). etransitivity; eauto.
+ exists (Call _ X); auto.
Qed.

Lemma Xmerge_inv_inject' : forall (B1 B2:XBehaviour Sig) B,
  B1 [[\/]] B2 = inject B -> exists B', B2 = inject B'.
Proof.
intros.
apply Xmerge_inv_inject with B1 B.
rewrite Xmerge_comm; auto.
Qed.

Lemma Xmerge_inv : forall (B1 B2:XBehaviour Sig) B,
  B1 [[\/]] B2 = inject B -> exists B'1 B'2,
    B1 = inject B'1 /\ B2 = inject B'2 /\ B'1 [\/] B'2 = inject B.
Proof.
intros.
elim (Xmerge_inv_inject _ _ _ H). intros B1' HB1.
elim (Xmerge_inv_inject' _ _ _ H). intros B2' HB2.
exists B1', B2'; repeat split; auto.
unfold merge. rewrite <- HB1, <- HB2; auto.
Qed.


(** ** Pruning on extended behaviours *)

Definition Xmore_branches (XB XB':XBehaviour Sig) :=
  exists B B', XB = inject B /\ XB' = inject B' /\ B [>] B'.

Infix "[[>]]" := Xmore_branches (at level 70).

Lemma more_branches_X : forall B B', B [>] B' -> inject B [[>]] inject B'.
Proof. red. eauto. Qed.

Lemma X_more_branches : forall B B', inject B [[>]] inject B' -> B [>] B'.
Proof.
intros.
destroy H.
apply inject_inj in H0; apply inject_inj in H1.
rewrite H0, H1; auto.
Qed.

(** The corresponding lemmas. *)

Lemma Xmore_branches_refl : forall X B, X = inject B -> X [[>]] X.
Proof. intros. rewrite H. apply more_branches_X, more_branches_refl. Qed.

Lemma Xmore_branches_trans : forall X X' X'', X [[>]] X' -> X' [[>]] X'' -> X [[>]] X''.
Proof.
intros.
destroy H; destroy H0.
exists x, x2; repeat split; auto.
apply more_branches_trans with x0; auto.
rewrite H3 in H2. apply inject_inj in H2. inversion H2. 
rewrite <- H5; auto.
Qed.

Lemma Xmerge_is_lub : forall B B1 B2, B [[>]] B1 -> B [[>]] B2 -> B [[>]] B1 [[\/]] B2.
Proof.
intros.
destroy H; destroy H0.
rewrite H1 in H3; apply inject_inj in H3.
rewrite <- H3 in H0; clear x1 H3.
elim (more_branches_has_lub _ _ _ _ H H0).
intros. destroy H3.
rewrite H1, H2, H4. red; eauto.
Qed.

Lemma Xmore_branches_merge_extend : forall B1 B2 B1' B2' B, B1 [[>]] B1' -> B2 [[>]] B2' ->
  B1 [[\/]] B2 = inject B -> B1 [[\/]] B2 [[>]] B1' [[\/]] B2'.
Proof.
intros. destroy H. destroy H0.
rewrite H2, H4 in H1.
elim (more_branches_merge_extend _ _ _ _ _ _ H H0 H1); intros.
destroy H6.
rewrite H2, H3, H4, H5.
eexists; eexists; repeat split; eauto.
Qed.

Lemma Xmore_branches_merge : forall B1 B2,
  B1 [[>]] B2 <-> (collapse B1 <> XUndefined /\ B1 [[\/]] B2 = B1).
Proof.
split; intros; destroy H.
+ rewrite H0, H1, collapse_inject; split.
  apply inject_not_undefined.
  apply more_branches_merge; auto.
+ elim (collapse_char' _ B2); intro H2.
  destroy H2. apply collapse_exists in H0. destroy H0.
  exists x0, x; repeat split; auto.
  apply more_branches_merge.
  unfold merge. rewrite <- H0, <- H2; auto.
  apply collapse_merge' with B1 B2 in H2.
  rewrite H in H2. elim H0; auto.
Qed.

Lemma Xmerge_is_larger : forall B1 B2,
  collapse (B1 [[\/]] B2) <> XUndefined -> B1 [[\/]] B2 [[>]] B1.
Proof.
intros.
apply collapse_exists in H. destroy H.
elim (collapse_char' _ B1); intro. induction a.
elim (collapse_char' _ B2); intro. induction a.
+ rewrite H, p.
  apply more_branches_X, merge_is_upper_bound with x1.
  unfold merge. rewrite <- p, <- p0; auto.
+ exfalso. apply Xmerge_inv_inject' in H.
  destroy H. rewrite H, collapse_inject in b.
  apply inject_not_undefined in b; auto.
+ exfalso. apply Xmerge_inv_inject in H.
  destroy H.  rewrite H, collapse_inject in b.
  apply inject_not_undefined in b; auto.
Qed.

Lemma Xmerge_is_larger' : forall B1 B2,
  collapse (B1 [[\/]] B2) <> XUndefined -> B1 [[\/]] B2 [[>]] B2.
Proof.
intros B1 B2.
rewrite Xmerge_comm.
apply Xmerge_is_larger; auto.
Qed.

End XMerge.

Notation "B [[>]] B'" := (Xmore_branches _ B B') (at level 50).
