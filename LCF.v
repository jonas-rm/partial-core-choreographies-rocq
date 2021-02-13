Require Import SP.

Module Blah (P X V E B R:DecType) (Ev:Eval E X V V) (BEv:Eval B X V Bool).

Module Import SP_LCF := SPBase P X V E B R Ev BEv.

Local Ltac solve B B' H := try (elim (XUndefined_dec (Xmerge B B')); intro H;
  [rewrite H| rewrite Xmatch_elim]; auto).

Local Ltac solve' B H := try (elim (XUndefined_dec B); intro H;
  [rewrite H| rewrite Xmatch_elim]; auto).

Ltac Peq := unfold Pid_dec; rewrite Pdec.eqb_refl; simpl.

Lemma Xmerge_Branching_elim : forall p mBl mBr q mBl' mBr',
  {Xmerge (XBranching p mBl mBr) (XBranching q mBl' mBr') = XUndefined } +
  {p = q /\ exists mB mB', Xmerge (XBranching p mBl mBr) (XBranching q mBl' mBr') = XBranching p mB mB'}.
Proof.
intros.
simpl. case_eq (Pid_dec p q); intro Hpq; simpl; auto.
unfold Pid_dec; apply Pdec.eqb_eq in Hpq.
case mBl, mBr, mBl', mBr'; simpl.
1,2: solve x x1 Hxx1.
3,4,7,8,12,13,14,15: solve' x Hx.
2,4,5,8,13,14: solve' x0 Hx0.
1: solve x0 x2 Hx0x2.
6: solve x x1 Hxx1.
7: solve' x Hx.
8: solve x0 x1 Hx0x1.
13,14,15: solve x x0 Hxx0.
13: solve' x1 Hx1.
all: right; eauto.
Qed.

Lemma Xmerge_Cond_1 : forall b b' Bt Bt' Be Be',
       b <> b' -> Xmerge (XCond b Bt Be) (XCond b' Bt' Be') = XUndefined.
Proof.
intros.
rewrite <- Bdec.eqb_neq in H.
simpl; unfold BExpr_dec; rewrite H.
auto.
Qed.

Lemma Xmerge_Cond_2 : forall b b' Bt Bt' Be Be',
   Xmerge Bt Bt' = XUndefined -> Xmerge (XCond b Bt Be) (XCond b' Bt' Be') = XUndefined.
Proof.
intros.
simpl. elim BExpr_dec; auto.
rewrite H; auto.
Qed.

Lemma Xmerge_Cond_3 : forall b b' Bt Bt' Be Be',
   Xmerge Be Be' = XUndefined -> Xmerge (XCond b Bt Be) (XCond b' Bt' Be') = XUndefined.
Proof.
intros.
simpl. elim BExpr_dec; auto.
case (Xmerge Bt Bt'); try rewrite H; auto.
Qed.





Lemma Xmerge_assoc : forall B B' B'',
  Xmerge (Xmerge B B') B'' = Xmerge B (Xmerge B' B'').
Proof.
induction B using XBehaviour_ind';
induction B' using XBehaviour_ind';
induction B'' using XBehaviour_ind'; simpl; auto.
(* 84 cases *)
(* Call *)
6,19,32,45,58,71,77,78,79,80,81,82,83,84: case_eq (RecVar_dec X X0); intro HXX0; auto; simpl.
6,7: case_eq (RecVar_dec X0 X1); intro HX0X1; auto; simpl.
6: unfold RecVar_dec; rewrite (Rdec.eqb_trans _ _ _ HXX0 HX0X1); auto.
7: unfold RecVar_dec; rewrite (Rdec.eqb_ntrans _ _ _ HXX0 HX0X1); auto.
6,7: fold RecVar_dec; rewrite HXX0; auto.
(* 70 cases left *)
(* Pid *)
1,2,3,6,7,8,9,10,11,12,13,19,20,21,22,23,24,25,26,32,33,34,35,36,37,38,39,54,55,56,66,67,68:
  case_eq (Pid_dec p p0); intro Hpp0; auto; simpl.
5,6,15,16,25,26,39,40,43,44,47,48,51,52,53:
  case_eq (Pid_dec p0 p1); intro Hp0p1; auto; simpl.
1,4,5,6,16,18,20,23,24,25,26,27,28,43,46:
  case_eq (Expr_dec e e0); intro Hee0; auto; simpl.
17,20,21,26,29,30,32,33,34,35,36,37,38,46,48:
  case_eq (Var_dec v v0); intro Hvv0; auto; simpl.
33,36,37,39,40,41,42,43,44,45,46,47,48,50:
  case_eq (eqb_label l l0); intro Hll0; auto; simpl.
all: try (solve B B' HBB'; fail). (* 21 cases *)
4: { elim (XUndefined_dec (Xmerge B B')); intro. rewrite a; auto.
  rewrite Xmatch_elim; auto.
  simpl. unfold Pid_dec; rewrite (Pdec.eqb_ntrans _ _ _ Hpp0 Hp0p1); auto.
}
all: try (solve B' B'' HBB'; fail). (* 18 cases *)
1,2,9:
  case_eq (Expr_dec e0 e1); intro He0e1; auto; simpl.
5,6,11:
  case_eq (Var_dec v0 v1); intro Hv0v1; auto; simpl.
10,11,13:
  case_eq (eqb_label l0 l1); intro Hl0l1; auto; simpl.
15: case_eq (eqb_label l l0); intro Hll0; auto; simpl.
(* 43 cases left *)
1: { elim (XUndefined_dec (Xmerge B B')); intro HBB';
  [rewrite HBB' | rewrite Xmatch_elim; auto].
  all: elim (XUndefined_dec (Xmerge B' B'')); intro HB'B'';
    [rewrite HB'B'' | rewrite Xmatch_elim; auto]; simpl; auto.
  - rewrite Hpp0, Hee0, <- IHB, HBB'; auto.
  - unfold Pid_dec; rewrite (Pdec.eqb_trans _ _ _ Hpp0 Hp0p1).
    unfold Expr_dec; rewrite (Edec.eqb_trans _ _ _ Hee0 He0e1).
    rewrite IHB, HB'B'', Xmerge_comm; simpl; auto.
  - rewrite Hpp0, Hee0.
    unfold Pid_dec; rewrite (Pdec.eqb_trans _ _ _ Hpp0 Hp0p1).
    unfold Expr_dec; rewrite (Edec.eqb_trans _ _ _ Hee0 He0e1).
    rewrite IHB; auto.
}
1: { elim (XUndefined_dec (Xmerge B B')); intro HBB';
  [rewrite HBB' | rewrite Xmatch_elim; auto]; simpl; auto.
  unfold Pid_dec; rewrite (Pdec.eqb_trans _ _ _ Hpp0 Hp0p1).
  unfold Expr_dec; rewrite (Edec.eqb_ntrans _ _ _ Hee0 He0e1).
  simpl; auto.
}
1: { elim (XUndefined_dec (Xmerge B' B'')); intro HB'B'';
  [rewrite HB'B'' | rewrite Xmatch_elim; auto]; simpl; auto.
  rewrite Hpp0, Hee0; auto.
}
1: { elim (XUndefined_dec (Xmerge B' B'')); intro HB'B'';
  [rewrite HB'B'' | rewrite Xmatch_elim; auto]; simpl; auto.
  rewrite Hpp0; auto.
}
1: { elim (XUndefined_dec (Xmerge B B')); intro HBB';
  [rewrite HBB' | rewrite Xmatch_elim; auto].
  all: elim (XUndefined_dec (Xmerge B' B'')); intro HB'B'';
    [rewrite HB'B'' | rewrite Xmatch_elim; auto]; simpl; auto.
  - rewrite Hpp0, Hvv0, <- IHB, HBB'; auto.
  - unfold Pid_dec; rewrite (Pdec.eqb_trans _ _ _ Hpp0 Hp0p1).
    unfold Var_dec; rewrite (Xdec.eqb_trans _ _ _ Hvv0 Hv0v1).
    rewrite IHB, HB'B'', Xmerge_comm; simpl; auto.
  - rewrite Hpp0, Hvv0.
    unfold Pid_dec; rewrite (Pdec.eqb_trans _ _ _ Hpp0 Hp0p1).
    unfold Var_dec; rewrite (Xdec.eqb_trans _ _ _ Hvv0 Hv0v1).
    rewrite IHB; auto.
}
1: { elim (XUndefined_dec (Xmerge B B')); intro HBB';
  [rewrite HBB' | rewrite Xmatch_elim; auto]; simpl; auto.
  unfold Pid_dec; rewrite (Pdec.eqb_trans _ _ _ Hpp0 Hp0p1).
  unfold Var_dec; rewrite (Xdec.eqb_ntrans _ _ _ Hvv0 Hv0v1).
  simpl; auto.
}
1: { elim (XUndefined_dec (Xmerge B' B'')); intro HB'B'';
  [rewrite HB'B'' | rewrite Xmatch_elim; auto]; simpl; auto.
  rewrite Hpp0, Hvv0; auto.
}
1: { elim (XUndefined_dec (Xmerge B' B'')); intro HB'B'';
  [rewrite HB'B'' | rewrite Xmatch_elim; auto]; simpl; auto.
  rewrite Hpp0; auto.
}
1: { elim (XUndefined_dec (Xmerge B B')); intro HBB';
  [rewrite HBB' | rewrite Xmatch_elim; auto]; simpl; auto.
  unfold Pid_dec; rewrite (Pdec.eqb_ntrans _ _ _ Hpp0 Hp0p1); auto.
}
1: { elim (XUndefined_dec (Xmerge B B')); intro HBB';
  [rewrite HBB' | rewrite Xmatch_elim; auto].
  all: elim (XUndefined_dec (Xmerge B' B'')); intro HB'B'';
    [rewrite HB'B'' | rewrite Xmatch_elim; auto]; simpl; auto.
  - rewrite Hpp0, Hll0, <- IHB, HBB'; auto.
  - unfold Pid_dec; rewrite (Pdec.eqb_trans _ _ _ Hpp0 Hp0p1).
    rewrite (label_eqb_trans _ _ _ Hll0 Hl0l1).
    rewrite IHB, HB'B'', Xmerge_comm; simpl; auto.
  - rewrite Hpp0, Hll0.
    unfold Pid_dec; rewrite (Pdec.eqb_trans _ _ _ Hpp0 Hp0p1).
    rewrite (label_eqb_trans _ _ _ Hll0 Hl0l1).
    rewrite IHB; auto.
}
1: { elim (XUndefined_dec (Xmerge B B')); intro HBB';
  [rewrite HBB' | rewrite Xmatch_elim; auto]; simpl; auto.
  unfold Pid_dec; rewrite (Pdec.eqb_trans _ _ _ Hpp0 Hp0p1).
  rewrite (label_eqb_ntrans _ _ _ Hll0 Hl0l1).
  simpl; auto.
}
1: { elim (XUndefined_dec (Xmerge B' B'')); intro HB'B'';
  [rewrite HB'B'' | rewrite Xmatch_elim; auto]; simpl; auto.
  rewrite Hpp0, Hll0; auto.
}
1: { elim (XUndefined_dec (Xmerge B' B'')); intro HB'B'';
  [rewrite HB'B'' | rewrite Xmatch_elim; auto]; simpl; auto.
  rewrite Hpp0; auto.
}
1: { elim (XUndefined_dec (Xmerge B B')); intro HBB';
  [rewrite HBB' | rewrite Xmatch_elim; auto]; simpl; auto.
  unfold Pid_dec; rewrite (Pdec.eqb_ntrans _ _ _ Hpp0 Hp0p1); auto.
}
1: { elim (XUndefined_dec (Xmerge B' B'')); intro HB'B'';
  [rewrite HB'B'' | rewrite Xmatch_elim; auto]; simpl; auto.
}
(* 28 cases left *)
(* Cond *)
2,4,6,8,17,28:
  case_eq (BExpr_dec b b0); intro Hbb0; auto; simpl;
  case (Xmerge B'1 B''1); case (Xmerge B'2 B''2); auto.
14,15,16,17,18,20,21:
  case_eq (BExpr_dec b b0); intro Hbb0; auto; simpl;
  case (Xmerge B1 B'1); case (Xmerge B2 B'2); auto.
14: {
  change (Xmerge (Xmerge (XCond b B1 B2) (XCond b0 B'1 B'2)) (XCond b1 B''1 B''2)
    = Xmerge (XCond b B1 B2) (Xmerge (XCond b0 B'1 B'2) (XCond b1 B''1 B''2))).
  case_eq (BExpr_dec b b0); intro Hbb0.
  2: rewrite Xmerge_Cond_1; [case_eq (BExpr_dec b0 b1); intro Hb0b1 | apply Bdec.eqb_neq; auto].
  unfold BExpr_dec in Hbb0; rewrite Bdec.eqb_eq in Hbb0; rewrite <- Hbb0.
  clear b0 Hbb0 IHB''1 IHB''2.
  case_eq (BExpr_dec b b1); intro Hbb1.
  2: rewrite (Xmerge_Cond_1 b b1); auto; [idtac | apply Bdec.eqb_neq; auto].
  unfold BExpr_dec in Hbb1; rewrite Bdec.eqb_eq in Hbb1; rewrite <- Hbb1.
  clear b1 Hbb1.
  - elim (XUndefined_dec (Xmerge B1 B'1)); intro H1.
    * rewrite Xmerge_Cond_2; auto.
      elim (XUndefined_dec (Xmerge B'1 B''1)); intro H1'.
      1: rewrite Xmerge_Cond_2; auto.
      elim (XUndefined_dec (Xmerge B'2 B''2)); intro H2'.
      1: rewrite Xmerge_Cond_3; auto.
      rewrite Xmerge_Cond_inv; auto.
      rewrite Xmerge_Cond_2; auto.
      rewrite <- IHB1, H1; auto.
    * elim (XUndefined_dec (Xmerge B2 B'2)); intro H2.
      ++ rewrite Xmerge_Cond_3; auto.
         elim (XUndefined_dec (Xmerge B'1 B''1)); intro H1'.
         1: rewrite Xmerge_Cond_2; auto.
         elim (XUndefined_dec (Xmerge B'2 B''2)); intro H2'.
         1: rewrite Xmerge_Cond_3; auto.
         rewrite Xmerge_Cond_inv; auto.
         rewrite Xmerge_Cond_3; auto.
         rewrite <- IHB2, H2; auto.
      ++ rewrite Xmerge_Cond_inv; auto.
         elim (XUndefined_dec (Xmerge B'1 B''1)); intro H1'.
         -- rewrite (Xmerge_Cond_2 b b B'1); auto.
            rewrite Xmerge_Cond_2; auto.
            rewrite IHB1, H1', Xmerge_comm; auto.
         -- elim (XUndefined_dec (Xmerge B'2 B''2)); intro H2'.
            repeat rewrite Xmerge_Cond_3; auto. rewrite IHB2, H2', Xmerge_comm; auto.
            elim (XUndefined_dec (Xmerge B1 (Xmerge B'1 B''1))); intro H1''.
            rewrite Xmerge_Cond_2; auto. 2: rewrite IHB1; auto.
            rewrite Xmerge_Cond_inv; auto. rewrite Xmerge_Cond_2; auto.
            elim (XUndefined_dec (Xmerge B2 (Xmerge B'2 B''2))); intro H2''.
            rewrite Xmerge_Cond_3; auto. 2: rewrite IHB2; auto.
            rewrite Xmerge_Cond_inv; auto. rewrite Xmerge_Cond_3; auto.
            repeat rewrite Xmerge_Cond_inv; auto. rewrite IHB1, IHB2; auto.
            rewrite IHB1; auto. rewrite IHB2; auto.
  - elim (XUndefined_dec (Xmerge B1 B'1)); intro H1.
    rewrite Xmerge_Cond_2; auto.
    elim (XUndefined_dec (Xmerge B2 B'2)); intro H2.
    rewrite Xmerge_Cond_3; auto.
    rewrite Xmerge_Cond_inv, Xmerge_Cond_1; auto.
    apply Bdec.eqb_neq; auto.
  - unfold BExpr_dec in Hb0b1; rewrite Bdec.eqb_eq in Hb0b1; rewrite <- Hb0b1.
    clear b1 Hb0b1.
    elim (XUndefined_dec (Xmerge B'1 B''1)); intro H1'.
    rewrite Xmerge_Cond_2; auto.
    elim (XUndefined_dec (Xmerge B'2 B''2)); intro H2'.
    rewrite Xmerge_Cond_3; auto.
    rewrite Xmerge_Cond_inv, Xmerge_Cond_1; auto.
    apply Bdec.eqb_neq; auto.
  - rewrite Xmerge_Cond_1; auto. apply Bdec.eqb_neq; auto.
}
1: change (XUndefined = 
  match (Xmerge (XBranching p mB mB') (XBranching p0 mB0 mB'0)) with
  XEnd => XEnd | _ => XUndefined end).
2: change (XUndefined = 
  match (Xmerge (XBranching p0 mB mB') (XBranching p1 mB0 mB'0)) with
  XSend p' e' B' => Xmerge (XSend p e B) (XSend p' e' B')
  | _ => XUndefined end).
3: change (XUndefined = 
  match (Xmerge (XBranching p0 mB mB') (XBranching p1 mB0 mB'0)) with
  XRecv p' v' B' => Xmerge (XRecv p v B) (XRecv p' v' B')
  | _ => XUndefined end).
4: change (XUndefined = 
  match (Xmerge (XBranching p0 mB mB') (XBranching p1 mB0 mB'0)) with
  XSel p' l' B' => Xmerge (XSel p l B) (XSel p' l' B')
  | _ => XUndefined end).
5: change (Xmerge (Xmerge (XBranching p mB mB') (XBranching p0 mB0 mB'0))
   XEnd = XUndefined).
6: change (Xmerge (Xmerge (XBranching p mB mB') (XBranching p0 mB0 mB'0))
   (XSend p1 e B'') = XUndefined).
7: change (Xmerge (Xmerge (XBranching p mB mB') (XBranching p0 mB0 mB'0))
   (XRecv p1 v B'') = XUndefined).
8: change (Xmerge (Xmerge (XBranching p mB mB') (XBranching p0 mB0 mB'0))
   (XSel p1 l B'') = XUndefined).
9: change (Xmerge (Xmerge (XBranching p mB mB') (XBranching p0 mB0 mB'0)) (XBranching p1 mB1 mB'1)
   = Xmerge (XBranching p mB mB') (Xmerge (XBranching p0 mB0 mB'0) (XBranching p1 mB1 mB'1))).
10: change (Xmerge (Xmerge (XBranching p mB mB') (XBranching p0 mB0 mB'0))
   (XCond b B''1 B''2) = XUndefined).
11: change (Xmerge (Xmerge (XBranching p mB mB') (XBranching p0 mB0 mB'0))
   (XCall X) = XUndefined).
12: change (Xmerge (Xmerge (XBranching p mB mB') (XBranching p0 mB0 mB'0))
   XUndefined = XUndefined).
13: change (XUndefined = 
  match (Xmerge (XBranching p mB mB') (XBranching p0 mB0 mB'0)) with
  XCond e' B1' B2' => Xmerge (XCond b B1 B2) (XCond e' B1' B2')
  | _ => XUndefined end).
14: change (XUndefined = 
  match (Xmerge (XBranching p mB mB') (XBranching p0 mB0 mB'0)) with
  XCall X' => Xmerge (XCall X) (XCall X')
  | _ => XUndefined end).
12: rewrite Xmerge_comm; auto.
1,5,6,7,8,10,11,12,13: elim (Xmerge_Branching_elim p mB mB' p0 mB0 mB'0); intro H'; [rewrite H'; auto | destroy H'; rewrite H'; auto].
1,2,3: elim (Xmerge_Branching_elim p0 mB mB' p1 mB0 mB'0); intro H'; [rewrite H'; auto | destroy H'; rewrite H'; auto].
clear H1 H2 H3 H4.
elim (P.eq_dec p p0); elim (P.eq_dec p0 p1); intros Hp0p1 Hpp0.
2: {
  rewrite <- Hpp0; rewrite <- Hpp0 in Hp0p1.
  rewrite <- Pdec.eqb_neq in Hp0p1.
  transitivity XUndefined. 2: simpl; unfold Pid_dec; rewrite Hp0p1; auto.
  elim (Xmerge_Branching_elim p mB mB' p mB0 mB'0); intros.
  rewrite a; auto.
  destroy b. rewrite b. simpl; unfold Pid_dec; rewrite Hp0p1; auto.
}
2: {
  rewrite <- Hp0p1.
  rewrite <- Pdec.eqb_neq in Hpp0.
  transitivity XUndefined. simpl; unfold Pid_dec; rewrite Hpp0; auto.
  elim (Xmerge_Branching_elim p0 mB0 mB'0 p0 mB1 mB'1); intros.
  rewrite a; auto.
  destroy b. rewrite b. simpl; unfold Pid_dec; rewrite Hpp0; auto.
}
2: { 
  rewrite <- Pdec.eqb_neq in Hpp0, Hp0p1.
  simpl; unfold Pid_dec; rewrite Hpp0, Hp0p1; auto.
}
rewrite <- Hp0p1, <- Hpp0; clear Hpp0 Hp0p1 p0 p1.

(*
elim (Xmerge_Branching_elim p mB mB' p mB0 mB'0); intro H1.
1,2: elim (Xmerge_Branching_elim p mB0 mB'0 p mB1 mB'1); intro H2.
1: { rewrite H1, H2. rewrite Xmerge_comm at 1. auto. }
rewrite H1. destroy H2; clear H3. rewrite H2.
elim (Xmerge_Branching_elim p mB mB' p x x0); intro H3.
1: { rewrite H3, Xmerge_comm at 1. auto. }
destroy H3. clear H4.
1: { exfalso.
  apply Xmerge_inv_Branching in H3; destroy H3.
  inversion H4; clear H4; inversion H5; clear H5.
  rewrite <- H10, <- H9 in H8, H6; clear x3 x4 H10 H9.
  rewrite <- H11, <- H12 in H7, H3; clear x5 x6 H11 H12.
  apply Xmerge_inv_Branching in H2; destroy H2.
  inversion H4; clear H4; inversion H5; clear H5.
  rewrite <- H12, <- H13 in H11, H9; clear x3 x4 H12 H13.
  rewrite <- H14, <- H15 in H2, H10; clear x5 x6 H14 H15.
  revert H1; simpl; Peq.
  induction x; [elim (H11 a); auto | elim H9; auto]; clear H11 H9;
    intros Hx1 Hx2; destroy Hx2; [idtac | set (a:=True)].
  all: induction x0; [elim (H2 a0); auto | elim H10; auto]; clear H10 H2;
    intros Hx3 Hx4; destroy Hx4; [idtac | set (a0:=True)].
  all: induction x1; [elim (H8 a1); auto | elim H6; auto]; clear H6 H8;
    intros Hx5 Hx6; destroy Hx6; [idtac | set (a1:=True)].
  all: induction x2; [elim (H3 a2); auto | elim H7; auto]; clear H7 H3;
    intros Hx7 Hx8; destroy Hx8.
  - clear H3 H4.
    induction mB. 
*)

(*
simpl. unfold Pid_dec; rewrite Pdec.eqb_refl.
induction mB, mB', mB0, mB'0, mB1, mB'1.
+ solve a x0 Ha0. 2: solve x x1 H_1. all: solve x0 x2 H02.
  1,2,4: solve x1 x3 H13. 1,2,4: Peq.
  - rewrite <- (H a), Ha0; auto.
  - rewrite <- (H0 x), H_1; simpl; auto. solve a (Xmerge x0 x2) Ha02.
  - Peq. rewrite <- (H a), <- (H0 x); auto.
  - simpl. Peq. solve (Xmerge a x0) x2 Ha02.
    solve x1 x3 H13. rewrite (H0 x), H13, Xmerge_comm; auto.
  - simpl. Peq. rewrite (H a), H02, Xmerge_comm; auto.
+ solve a x0 Ha0. 2: solve x x1 H_1. all: solve x0 x2 H02.
  1,2,4: solve' x1 H1. 1,2,4: Peq.
  - rewrite <- (H a), Ha0; auto.
  - rewrite <- (H a), H_1; simpl; auto. solve (Xmerge a x0) x2 Ha02.
  - Peq. rewrite <- (H a); auto.
  - simpl. Peq. solve (Xmerge a x0) x2 Ha02.
    rewrite Xmerge_comm; auto.
  - simpl. Peq. rewrite (H a), H02, Xmerge_comm; auto.
+ solve a x0 Ha0. 2: solve x x1 H_1. all: simpl; solve' x0 H'0.
  1,2,4: solve x1 x2 H12. all: try Peq.
  - rewrite Ha0; auto.
  - rewrite <- (H0 x), H_1, Xmerge_comm; simpl; auto. solve' (Xmerge x0 a) H_.
  - rewrite (H0 x), H12, Xmerge_comm; simpl; auto. solve' x0 H_.
  - solve (Xmerge x x1) x2 H_12. repeat rewrite Xmatch_elim; auto.
    Peq. rewrite <- (H x), H_12; auto.

solve' x0 H_.
  - simpl. Peq. solve (Xmerge a x0) x2 Ha02.
    rewrite Xmerge_comm; auto.
  - simpl. Peq. rewrite (H a), H02, Xmerge_comm; auto.
*)






Open Scope MC_scope.

(** MOVE ME *)

Section Soundness.


(*
Fixpoint seq_compose {m} {k} (fs:t (PRFunction m) k) (ps:t Pid m) (target init:nat) (X:RecVar)
  (Implement : forall (H:Fin.t k) (ps':t Pid m) (q' i':nat) (k':RecVar), RecVar -> Choreography) {struct fs} : RecVar -> Choreography.
(*
  match fs with
  | [] => End
  | f :: fs' => Implement m f d (Hd Fin.F1) ps target init ;; compose_args fs' ps (S target) (init + Pi f) Implement
  end.
*)
Proof.
destruct fs.
- apply (fun _ => End).
- pose (Implement (Fin.F1) ps target init X) as Ph.
  pose (seq_compose _ _ fs ps (S target) (init + Pi h) (X + Gamma h) (fun H => Implement (Fin.FS H))) as Pfs.
  apply (fun Y => if Y <? X + Gamma h then (Ph Y) else (Pfs Y)).
Defined.

Definition Implementation_aux {m} (f:PRFunction m) :
  t Pid m -> Pid -> nat -> RecVar -> RecVar -> Choreography
  :=
  PRFunction_recursion (fun m f => t Pid m -> Pid -> nat -> RecVar -> RecVar -> Choreography)
  (fun ps q _ X => Pack1 X (Send ps[@Fin.F1] zero q;; Call (S X)))
  (fun ps q _ X => Pack1 X (Send ps[@Fin.F1] succ_this q;; Call (S X)))
  (fun i j Hp ps q _ X => Pack1 X (Send ps[@Fin.of_nat_lt Hp] this q;; Call (S X)))
  (fun k m g fs Hfs Hg ps q init X => 
    (fun Y => if Y <? X + vsum (map Gamma fs)
      then seq_compose fs ps init (init+m) X Hfs Y
      else Hg (seq_labels init fs) q (init + m) (X + (vsum (map Gamma fs))) Y))
  (fun k g h Hg Hh ps q init X => 
    (fun Y =>
      if (Y <? X + Gamma g) then Hg (tl ps) init (init+3) X Y
      else if (RecVar_dec Y (X + Gamma g)) then
         Send (init+2) zero (S init);; Call (X + Gamma g + 1)
      else if (RecVar_dec Y (X + Gamma g + 1)) then 
         IfEq (S init) ps[@Fin.F1] (Send init this q;; Call (X + Gamma g + Gamma h + 3)) (Call (X + Gamma g + 2))
      else if (RecVar_dec Y (X + Gamma g + Gamma h + 2)) then
         Send (init+2) this init;; Send (S init) this (init+2);; Send (init+2) succ_this (S init);; Call (X + Gamma g + 1)
      else Hh (S init :: init :: tl ps) (init+2) (init+3 + Pi g) (X + Gamma g + 2) Y))
  (fun k h Hh ps q init X => 
    (fun Y =>
      if (RecVar_dec Y X) then
         Send (init+2) zero (init+1);; Call (X + 1)
      else if (RecVar_dec Y (X + Gamma h + 1)) then
         Send (init+1) zero (init+2);; IfEq (init+2) init
            (Send (init+1) this q;; Call (X + Gamma h + 2))
            (Send (init+1) this (init+2);; Send (init+2) succ_this (init+1);; Call (X + 1))
        else Hh (shiftin (init+1) ps) init (init+3) (X + 1) Y))
  m f.
*)

End Soundness.

Section ComputableReduction.

Require Import Sumbool.

Notation "A '&&&' B" := (sumbool_and _ _ _ _ A B).

Fixpoint compatible (Defs:DefSet) (s:State) (tl:RichLabel) (C:Choreography) : Prop :=
  (match C, tl with
  | Call X,           R_Call Y p       => X = Y /\ In p (fst (Defs X))
  | RT_Call X ps C',  R_Call Y p       => (X = Y /\ In p ps)
                                          \/ (~In p ps /\ compatible Defs s tl C')
  | RT_Call X ps C',  R_Com p _ q _    => disjoint (p::q::nil) ps /\ compatible Defs s tl C'
  | RT_Call X ps C',  R_Sel p q _      => disjoint (p::q::nil) ps /\ compatible Defs s tl C'
  | RT_Call X ps C',  R_Cond p         => ~In p ps /\ compatible Defs s tl C'
  | Com p e q x;; C', R_Com p' v q' x' => (p=p' /\ q=q' /\ x=x' /\ v=eval_on_state e s p)
                                          \/ (disjoint (p::q::nil) (p'::q'::nil) /\ compatible Defs s tl C')
  | Com p _ q _;; C', R_Sel p' q' _    => (disjoint (p::q::nil) (p'::q'::nil) /\ compatible Defs s tl C')
  | Com p _ q _;; C', R_Cond p'        => (~In p' (p::q::nil) /\ compatible Defs s tl C')
  | Com p _ q _;; C', R_Call Y p'      => (~In p' (p::q::nil) /\ compatible Defs s tl C')
  | Sel p q l;; C',   R_Sel p' q' l'   => (p=p' /\ q=q' /\ l=l')
                                          \/ (disjoint (p::q::nil) (p'::q'::nil) /\ compatible Defs s tl C')
  | Sel p q _;; C',   R_Com p' _ q' _  => (disjoint (p::q::nil) (p'::q'::nil) /\ compatible Defs s tl C')
  | Sel p q _;; C',   R_Cond p'        => (~In p' (p::q::nil) /\ compatible Defs s tl C')
  | Sel p q _;; C',   R_Call Y p'      => (~In p' (p::q::nil) /\ compatible Defs s tl C')
  | Cond p e C1 C2,   R_Cond p'        => (p=p')
                                          \/ (p<>p' /\ compatible Defs s tl C1 /\ compatible Defs s tl C2)
  | Cond p _ C1 C2,   R_Com p' _ q' _  => (~In p (p'::q'::nil) /\ compatible Defs s tl C1 /\ compatible Defs s tl C2)
  | Cond p _ C1 C2,   R_Sel p' q' _    => (~In p (p'::q'::nil) /\ compatible Defs s tl C1 /\ compatible Defs s tl C2)
  | Cond p _ C1 C2,   R_Call Y p'      => (p<>p' /\ compatible Defs s tl C1 /\ compatible Defs s tl C2)
  | _,                _                => False
end)%MC.

(*
Fixpoint reduce_C (Defs:DefSet) (C:Choreography) (s:State) (tl:RichLabel) :=
  (match C, tl with
  | Call X,           R_Call Y p       => if (R.eq_dec X Y &&& In_dec P.eq_dec p (fst (Defs X)))
                                            then (if (Nat.eq_dec (length (fst (Defs X))) 1)
                                                  then snd (Defs X)
                                                  else (RT_Call X (set_remove_pid p (fst (Defs X))) (snd (Defs X))))
                                            else End
  | RT_Call X ps C',  R_Call Y p       => if (R.eq_dec X Y &&& In_dec P.eq_dec p ps)
                                          then (if (Nat.eq_dec (length ps) 1)
                                                then C'
                                                else (RT_Call X (set_remove_pid p ps) C'))
                                          else End
  | Com p e q x;; C', R_Com p' v q' x' => if (P.eq_dec p p' &&& P.eq_dec q q' &&& V.eq_dec (eval_on_state e s p) v)
                                          then C'
                                          else if disjoint_dec _ P.eq_dec (p::q::nil) (p'::q'::nil)
                                               then reduce_C Defs C' s tl
                                               else End
  | Com p _ q _;; C', R_Sel p' q' _    => if (disjoint_dec _ P.eq_dec (p::q::nil) (p'::q'::nil))
                                          then reduce_C Defs C' s tl
                                          else End
  | Com p _ q _;; C', R_Cond p'        => if (In_dec P.eq_dec p' (p::q::nil))
                                          then End
                                          else reduce_C Defs C' s tl
  | Com p _ q _;; C', R_Call _ p'      => if (In_dec P.eq_dec p' (p::q::nil))
                                          then End
                                          else reduce_C Defs C' s tl
  | Sel p q l;; C',   R_Sel p' q' l'   => if (P.eq_dec p p' &&& P.eq_dec q q' &&& eq_label_dec l l')
                                          then C'
                                          else if disjoint_dec _ P.eq_dec (p::q::nil) (p'::q'::nil)
                                               then reduce_C Defs C' s tl
                                               else End
  | Sel p q _;; C',   R_Com p' _ q' _  => if (disjoint_dec _ P.eq_dec (p::q::nil) (p'::q'::nil))
                                          then reduce_C Defs C' s tl
                                          else End
  | Sel p q _;; C',   R_Cond p'        => if (In_dec P.eq_dec p' (p::q::nil))
                                          then End
                                          else reduce_C Defs C' s tl
  | Sel p q _;; C',   R_Call _ p'      => if (In_dec P.eq_dec p' (p::q::nil))
                                          then End
                                          else reduce_C Defs C' s tl
  | Cond p b C1 C2,   R_Cond p'        => if P.eq_dec p p'
                                          then if beval_on_state b s p
                                               then C1 else C2
                                          else If p ? b Then (reduce_C Defs C1 s tl) Else (reduce_C Defs C2 s tl)
  | Cond p b C1 C2,   R_Com p' _ q' _  => if In_dec P.eq_dec p (p'::q'::nil)
                                          then End
                                          else If p ? b Then (reduce_C Defs C1 s tl) Else (reduce_C Defs C2 s tl)
  | Cond p b C1 C2,   R_Sel p' q' _    => if In_dec P.eq_dec p (p'::q'::nil)
                                          then End
                                          else If p ? b Then (reduce_C Defs C1 s tl) Else (reduce_C Defs C2 s tl)
  | Cond p b C1 C2,   R_Call _ p'      => if P.eq_dec p p'
                                          then End
                                          else If p ? b Then (reduce_C Defs C1 s tl) Else (reduce_C Defs C2 s tl)
  | _, _ => End
end)%MC.
*)

Fixpoint reduce_C (Defs:DefSet) (C:Choreography) (s:State) (tl:RichLabel) :=
  (match C, tl with
  | Call X,           R_Call _ p       => if Nat.eq_dec (set_size_pid (fst (Defs X))) 1
                                          then snd (Defs X)
                                          else RT_Call X (set_remove_pid p (fst (Defs X))) (snd (Defs X))
  | RT_Call X ps C',  R_Call Y p       => if In_dec P.eq_dec p ps
                                          then if Nat.eq_dec (set_size_pid ps) 1
                                               then C'
                                               else RT_Call X (set_remove_pid p ps) C'
                                          else RT_Call X ps (reduce_C Defs C' s tl)
  | RT_Call X ps C',  _                => RT_Call X ps (reduce_C Defs C' s tl)
  | Com p e q x;; C', R_Com p' v q' x' => if (P.eq_dec p p' &&& P.eq_dec q q' &&& V.eq_dec (eval_on_state e s p) v)
                                          then C'
                                          else Com p e q x;; reduce_C Defs C' s tl
  | Com p e q x;; C', _                => Com p e q x;; reduce_C Defs C' s tl
  | Sel p q l;; C',   R_Sel p' q' l'   => if (P.eq_dec p p' &&& P.eq_dec q q' &&& eq_label_dec l l')
                                          then C'
                                          else Sel p q l;; reduce_C Defs C' s tl
  | Sel p q l;; C',   _                => Sel p q l;; reduce_C Defs C' s tl
  | Cond p b C1 C2,   R_Cond p'        => if P.eq_dec p p'
                                          then if beval_on_state b s p
                                               then C1 else C2
                                          else If p ? b Then (reduce_C Defs C1 s tl) Else (reduce_C Defs C2 s tl)
  | Cond p b C1 C2,   _                => If p ? b Then (reduce_C Defs C1 s tl) Else (reduce_C Defs C2 s tl)
  | _, _ => End
  end)%MC.

Definition reduce_S (s:State) (tl:RichLabel) :=
  match tl with
  | R_Com _ v q x => update s q x v
  | _             => s
  end.

Lemma reduce_sound : forall Defs C s tl, MCP_WF (Build_Program Defs C) ->
  compatible Defs s tl C -> MCC_To Defs C s tl (reduce_C Defs C s tl) (reduce_S s tl).
Proof.
induction C; intros; induction tl; try inversion H0; simpl.
- rewrite <- H1. elim Nat.eq_dec; intros.
  + apply C_Call_Local'; auto.
  + apply C_Call_Start'; auto.
    elim (not_eq _ _ b); intros; auto.
    inversion H3. 2: inversion H5.
    elim (MCP_WF_Vars _ H r); auto.
    red; simpl; auto. unfold Vars; simpl. eapply set_size_0; eauto.
- apply C_Delay_Call; auto.
    2: { apply IHC; auto. eapply MCP_WF_Call; eauto. }
    clear H2 H0 H s IHC C r Defs.
    induction l; simpl; auto.
    split. split; intro; eapply H1; simpl; eauto.
    apply IHl; repeat intro. inversion_clear H.
    apply (H1 a0); split; simpl; auto.
- apply C_Delay_Call; auto.
    2: { apply IHC; auto. eapply MCP_WF_Call; eauto. }
    clear H2 H0 H s IHC C r Defs.
    induction l; simpl; auto.
    split. split; intro; eapply H1; simpl; eauto.
    apply IHl; repeat intro. inversion_clear H.
    apply (H1 a0); split; simpl; auto.
- apply C_Delay_Call; auto.
    2: { apply IHC; auto. eapply MCP_WF_Call; eauto. }
    clear H2 H0 H s IHC C r Defs.
    induction l; simpl; auto.
    split. intro; eapply H1; simpl; eauto.
    apply IHl; repeat intro. apply H1; simpl; auto.
- inversion_clear H1. rewrite H2. elim in_dec; [elim Nat.eq_dec | idtac]; intros.
  + apply C_Call_Finish'; auto.
  + apply C_Call_Enter'; auto.
    elim (not_eq _ _ b); intros; auto.
    inversion H1. 2: inversion H5.
    generalize (MCP_WF_Main _ H); simpl; intros.
    inversion H4. inversion H7.
    apply set_size_0 in H5. elim H8; auto.
  + elim b; auto.
- inversion_clear H1. elim in_dec; intros.
  + exfalso; auto.
  + apply C_Delay_Call; auto.
    2: { apply IHC; auto. eapply MCP_WF_Call; eauto. }
    clear b H3 H0 H IHC.
    induction l; simpl; auto.
    simpl in H2. split; auto.
- induction e.
  + inversion H0. inversion_clear H1. inversion_clear H3. inversion_clear H4.
    * rewrite H5, H2, H1, H3. clear H2 H1 H3 H5 H0.
      elim P.eq_dec; intro Hp. 2: elim Hp; auto.
      elim P.eq_dec; intro Hq. 2: elim Hq; auto.
      elim V.eq_dec; intro Hv. 2: elim Hv; auto.
      apply C_Com'.
    * inversion_clear H1. red in H2.
      elim P.eq_dec; intro Hp. elim (H2 p); rewrite Hp; simpl; auto.
      elim P.eq_dec; intro Hq. elim (H2 q); rewrite Hq; simpl; auto.
      elim V.eq_dec; intro Hv; simpl; apply C_Delay_Eta; auto.
      ++ simpl. split; split; intro; auto; eapply H2; simpl; eauto.
      ++ eapply IHC; auto. eapply MCP_WF_eta; eauto.
      ++ simpl. split; split; intro; auto; eapply H2; simpl; eauto.
      ++ eapply IHC; auto. eapply MCP_WF_eta; eauto.
  + inversion_clear H0. apply C_Delay_Eta; auto.
      ++ simpl. split; split; intro; auto; eapply H1; simpl; eauto.
         split; right; left; eauto.
      ++ eapply IHC; auto. eapply MCP_WF_eta; eauto.
- induction e.
  + inversion_clear H0. apply C_Delay_Eta; auto.
      ++ simpl. split; split; intro; auto; eapply H1; simpl; eauto.
         split; right; left; eauto.
      ++ eapply IHC; auto. eapply MCP_WF_eta; eauto.
  + inversion H0. inversion_clear H1. inversion_clear H3. inversion_clear H4.
    * rewrite H2, H1. clear H2 H1.
      elim P.eq_dec; intro Hp. 2: elim Hp; auto.
      elim P.eq_dec; intro Hq. 2: elim Hq; auto.
      elim eq_label_dec; intro Hl. 2: elim Hl; auto.
      apply C_Sel'.
    * inversion_clear H1. red in H2.
      elim P.eq_dec; intro Hp. elim (H2 p); rewrite Hp; simpl; auto.
      elim P.eq_dec; intro Hq. elim (H2 q); rewrite Hq; simpl; auto.
      elim eq_label_dec; intro Hl; simpl; apply C_Delay_Eta; auto.
      ++ simpl. split; split; intro; auto; eapply H2; simpl; eauto.
      ++ eapply IHC; auto. eapply MCP_WF_eta; eauto.
      ++ simpl. split; split; intro; auto; eapply H2; simpl; eauto.
      ++ eapply IHC; auto. eapply MCP_WF_eta; eauto.
- induction e.
  + inversion H0. apply C_Delay_Eta.
    * simpl. split; intro; auto; eapply H1; simpl; eauto.
    * eapply IHC; auto. eapply MCP_WF_eta; eauto.
  + inversion H0. apply C_Delay_Eta.
    * simpl. split; intro; auto; eapply H1; simpl; eauto.
    * eapply IHC; auto. eapply MCP_WF_eta; eauto.
- induction e.
  + inversion H0. apply C_Delay_Eta.
    * simpl. split; intro; auto; eapply H1; simpl; eauto.
    * eapply IHC; auto. eapply MCP_WF_eta; eauto.
  + inversion H0. apply C_Delay_Eta.
    * simpl. split; intro; auto; eapply H1; simpl; eauto.
    * eapply IHC; auto. eapply MCP_WF_eta; eauto.
- inversion_clear H2.
  apply C_Delay_Cond.
  + split; intro; eapply H1; simpl; eauto.
  + eapply IHC1; auto. eapply MCP_WF_Then; eauto.
  + eapply IHC2; auto. eapply MCP_WF_Else; eauto.
- inversion_clear H2.
  apply C_Delay_Cond.
  + split; intro; eapply H1; simpl; eauto.
  + eapply IHC1; auto. eapply MCP_WF_Then; eauto.
  + eapply IHC2; auto. eapply MCP_WF_Else; eauto.
- elim P.eq_dec; intro Hp. 2: elim Hp; auto.
  case_eq (beval_on_state b s p); intro Hb; rewrite <- Hp.
  + apply C_Then'; auto.
  + apply C_Else'; auto.
- inversion_clear H1. inversion_clear H3.
  elim P.eq_dec; intro Hp. elim H2; auto.
  apply C_Delay_Cond; auto.
  + eapply IHC1; auto. eapply MCP_WF_Then; eauto.
  + eapply IHC2; auto. eapply MCP_WF_Else; eauto.
- inversion_clear H2.
  apply C_Delay_Cond; auto.
  + eapply IHC1; auto. eapply MCP_WF_Then; eauto.
  + eapply IHC2; auto. eapply MCP_WF_Else; eauto.
Qed.

Lemma reduce_compatible : forall Defs C s tl C' s',
  MCC_To Defs C s tl C' s' -> compatible Defs s tl C.
Proof.
intros.
induction H; simpl; auto.
+ induction eta; induction t; simpl; auto.
  * right; split; auto.
    apply disjoint_Com_Com in H; auto.
  * split; auto. apply disjoint_Com_Sel in H; auto.
  * split; auto. intro.
    inversion_clear H. inversion_clear H1; auto.
    inversion_clear H; auto.
  * split; auto. intro.
    inversion_clear H. inversion_clear H1; auto.
    inversion_clear H; auto.
  * split; auto. apply disjoint_Sel_Sel in H; auto.
  * right; split; auto.
    apply disjoint_Sel_Sel in H; auto.
  * split; auto. intro.
    inversion_clear H. inversion_clear H1; auto.
    inversion_clear H; auto.
  * split; auto. intro.
    inversion_clear H. inversion_clear H1; auto.
    inversion_clear H; auto.
+ induction t; simpl; auto.
  * repeat split; auto. intro.
    inversion_clear H. inversion_clear H2; auto.
    inversion_clear H; auto.
  * repeat split; auto. intro.
    inversion_clear H. inversion_clear H2; auto.
    inversion_clear H; auto.
+ induction t; simpl; auto.
  * split; auto. apply disjoint_ps_Com in H; auto.
  * split; auto. apply disjoint_ps_Sel in H; auto.
  * split; auto. apply disjoint_ps_Cond; auto.
  * apply disjoint_ps_Call in H; auto.
Qed.

Lemma reduce_unique_1 : forall Defs C s tl C' s',
  MCP_WF (Build_Program Defs C) ->
  MCC_To Defs C s tl C' s' -> C' = reduce_C Defs C s tl.
Proof.
intros.
eapply MCC_To_deterministic_1; eauto.
apply reduce_sound; auto.
eapply reduce_compatible; eauto.
Qed.
*)

End ComputableReduction.
