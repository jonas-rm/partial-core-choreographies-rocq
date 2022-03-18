Require Export Merge.

Variable Sig : Signature.

Arguments Xmerge [Sig].
Arguments XUndefined {Sig}.
Arguments XSend [Sig].
Arguments XRecv [Sig].
Arguments XSel [Sig].
Arguments XBranching [Sig].
Arguments XCond [Sig].
Arguments XCall [Sig].
Arguments XEnd {Sig}.

Local Definition Pid := Merge.Pid Sig.
Local Definition Ann := Merge.Ann Sig.

Local Ltac solve B B' H := try (elim (XUndefined_dec _ (Xmerge B B')); intro H;
  [rewrite H| rewrite Xmatch_elim]; auto).

Local Ltac solve' B H := try (elim (XUndefined_dec _ B); intro H;
  [rewrite H| rewrite Xmatch_elim]; auto).

Local Ltac eq_elim t t' H :=
  case (eq_dec t t'); intro H;
  [rewrite <- eqb_eq in H | rewrite <- eqb_neq in H];
  rewrite H; auto; simpl.

Local Ltac leq_elim t t' H :=
  case (eq_label_dec t t'); intro H;
  [rewrite <- label_eqb_eq in H | rewrite <- label_eqb_neq in H];
  rewrite H; auto; simpl.

Lemma Xmerge_Branching_elim : forall (p:Pid) mBl mBr (q:Pid) mBl' mBr',
  {Xmerge (XBranching p mBl mBr) (XBranching q mBl' mBr') = XUndefined } +
  {p = q /\ exists mB mB', Xmerge (XBranching p mBl mBr) (XBranching q mBl' mBr') = XBranching p mB mB'}.
Proof.
intros.
simpl. case (@eq_dec Pid p q); intro Hpq; simpl; auto.
1: rewrite Hpq, eqb_refl.
(* WTF? *)
2: rewrite <- eqb_neq in Hpq; rewrite Hpq; auto.
case mBl, mBr, mBl', mBr'; simpl.
all: try induction p0 as (a,x);
  try induction p1 as (a',x');
  try induction p2 as (a'',x'');
  try induction p3 as (a''',x''').
1,2: case_eq (eqb Ann a a''); intros; auto.
1,2: solve x x'' H02.
1: case_eq (eqb Ann a' a'''); intros; auto.
1: solve x' x''' H13.
3,4,7,8,12,13,14,15: solve' x H'0.
2,4,5,8,13,14: solve' x' H'1.
6: case_eq (eqb Ann a a''); intros; auto.
6: solve x x'' H02.
7: solve' x H'0.
8: case_eq (eqb Ann a' a''); intros; auto.
8: solve x' x'' H12.
13,14,15: case_eq (eqb Ann a a'); intros; auto.
13,14,15: solve x x' Hx01.
13: solve' x'' H'2.
all: right; eauto.
Qed.

Lemma Xmerge_Cond_1 : forall b b' Bt Bt' Be Be',
       b <> b' -> Xmerge (XCond b Bt Be) (XCond b' Bt' Be') = XUndefined.
Proof.
intros.
rewrite <- eqb_neq in H.
simpl; rewrite H; auto.
Qed.

Lemma Xmerge_Cond_2 : forall b b' Bt Bt' Be Be',
   Xmerge Bt Bt' = XUndefined -> Xmerge (XCond b Bt Be) (XCond b' Bt' Be') = XUndefined.
Proof.
intros.
simpl. case (eq_dec b b'); intro Hbb'.
rewrite <- eqb_eq in Hbb'; rewrite Hbb', H; auto.
rewrite <- eqb_neq in Hbb'; rewrite Hbb'; auto.
Qed.

Lemma Xmerge_Cond_3 : forall b b' Bt Bt' Be Be',
   Xmerge Be Be' = XUndefined -> Xmerge (XCond b Bt Be) (XCond b' Bt' Be') = XUndefined.
Proof.
intros.
simpl. case (eq_dec b b'); intro Hbb'.
rewrite <- eqb_eq in Hbb'; rewrite Hbb', H; auto.
case (Xmerge Bt Bt'); auto.
rewrite <- eqb_neq in Hbb'; rewrite Hbb'; auto.
Qed.

(** Statistics for this lemma:
  - triple induction with 512 cases
  - 428 trivial cases (both sides are undefined), 84 cases left
  - 14 simple cases with RecVar
  - 27 cases of Com dealt with by simple case analysis, 15 need rewriting
  - 13 simple cases of Cond, one expands and needs rewriting
  - 13 simple cases of Branching, one needs sextuple induction (!)
    last case generates 64 sub-cases that have to be done by hand
    (semi-systematically using tactics)
  - more than 500 lines of proof
*)
Lemma Xmerge_assoc : forall (B B' B'':XBehaviour Sig),
  Xmerge (Xmerge B B') B'' = Xmerge B (Xmerge B' B'').
Proof.
induction B using XBehaviour_ind';
induction B' using XBehaviour_ind';
induction B'' using XBehaviour_ind'; simpl; auto.
(* 84 cases *)
(* Call *)
6,19,32,45,58,71,77,78,79,80,81,82,83,84: eq_elim X X0 HXX0.
6,7: eq_elim X0 X1 HX0X1.
6: rewrite (eqb_trans _ _ _ _ HXX0 HX0X1); auto.
7: rewrite (eqb_ntrans _ _ _ _ HXX0 HX0X1); auto.
6,7: rewrite HXX0; auto.
(* 70 cases left *)
(* Pid *)
1,2,3,6,7,8,9,10,11,12,13,19,20,21,22,23,24,25,26,32,33,34,35,36,37,38,39,54,55,56,66,67,68:
  eq_elim p p0 Hpp0.
6,16,26,39,40,43,44,47,48: eq_elim p0 p1 Hp0p1.
1,4,5,11,13,15,16,17,18,19,20,37,40: eq_elim e e0 Hee0.
15,20,23,24,25,26,27,28,29,30,31,40,42: eq_elim v v0 Hvv0.
29,33,34,35,36,37,38,39,40,41,42,43,44: leq_elim l l0 Hll0.
1,2,3,7,8,9,10,11,12,13,14,15,18,19,20,22,23,24,25,26,27,28,29,32,33,34,35,37,38,39,40,41,42:
  eq_elim a a0 Haa0.
all: try (solve B B' HBB'; fail). (* 21 cases *)

2,3,7,8,12,13,16,21,24,36,37,38: eq_elim p0 p1 Hp0p1.
2,4,11,31: eq_elim e0 e1 He0e1.
8,10,14,33: eq_elim v0 v1 Hv0v1.
14,16,17,35: leq_elim l0 l1 Hl0l1.
2,4,5,6,8,10,11,12,14,16,17,18,31,32,33,34,35,36: eq_elim a0 a1 Ha0a1.
all: try (solve B' B'' HBB'; fail). (* 15 cases *)

(* 52 cases left *)
1: { solve B B' HBB'; solve B' B'' HB'B''; simpl.
  - rewrite Hpp0, Hee0, Haa0, <- IHB, HBB'; auto.
  - rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1), (eqb_trans _ _ _ _ Hee0 He0e1), (eqb_trans _ _ _ _ Haa0 Ha0a1).
    rewrite IHB, HB'B'', Xmerge_comm; simpl; auto.
  - rewrite Hpp0, Hee0, Haa0.
    rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1), (eqb_trans _ _ _ _ Hee0 He0e1), (eqb_trans _ _ _ _ Haa0 Ha0a1).
    rewrite IHB; auto.
}
1: { solve B B' HBB'; simpl.
  rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1), (eqb_trans _ _ _ _ Hee0 He0e1), (eqb_ntrans _ _ _ _ Haa0 Ha0a1).
  simpl; auto.
}
1: solve B' B'' HB'B''; rewrite Hpp0, Hee0, Haa0; auto.
1: solve B' B'' HB'B''; rewrite Hpp0, Hee0; auto.
1,6,11: solve B' B'' HB'B''; rewrite Hpp0; auto.
1: { solve B B' HBB'; solve B' B'' HB'B''; simpl.
  - rewrite Hpp0, Hvv0, Haa0, <- IHB, HBB'; auto.
  - rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1), (eqb_trans _ _ _ _ Hvv0 Hv0v1), (eqb_trans _ _ _ _ Haa0 Ha0a1).
    rewrite IHB, HB'B'', Xmerge_comm; simpl; auto.
  - rewrite Hpp0, Hvv0, Haa0.
    rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1), (eqb_trans _ _ _ _ Hvv0 Hv0v1), (eqb_trans _ _ _ _ Haa0 Ha0a1).
    rewrite IHB; auto.
}
1: { solve B B' HBB'; simpl.
  rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1), (eqb_trans _ _ _ _ Hvv0 Hv0v1), (eqb_ntrans _ _ _ _ Haa0 Ha0a1).
  simpl; auto.
}
1: solve B' B'' HB'B''; rewrite Hpp0, Hvv0, Haa0; auto.
1: solve B' B'' HB'B''; rewrite Hpp0, Hvv0; auto.
1: { solve B B' HBB'; solve B' B'' HB'B''; simpl.
  - rewrite Hpp0, Hll0, Haa0, <- IHB, HBB'; auto.
  - rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1), (eqb_trans _ _ _ _ Haa0 Ha0a1).
    rewrite (label_eqb_trans _ _ _ Hll0 Hl0l1).
    rewrite IHB, HB'B'', Xmerge_comm; simpl; auto.
  - rewrite Hpp0, Hll0, Haa0.
    rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1), (eqb_trans _ _ _ _ Haa0 Ha0a1).
    rewrite (label_eqb_trans _ _ _ Hll0 Hl0l1).
    rewrite IHB; auto.
}
1: { solve B B' HBB'; simpl.
  rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1), (eqb_ntrans _ _ _ _ Haa0 Ha0a1).
  rewrite (label_eqb_trans _ _ _ Hll0 Hl0l1).
  simpl; auto.
}
1: solve B' B'' HB'B''; rewrite Hpp0, Hll0, Haa0; auto.
1: solve B' B'' HB'B''; rewrite Hpp0, Hll0; auto.
1: { solve B B' HBB'; simpl.
  rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1), (eqb_ntrans _ _ _ _ Hee0 He0e1).
  simpl; auto.
}
1,3,5: solve B B' HBB'; simpl; unfold eq_dec; rewrite (eqb_ntrans _ _ _ _ Hpp0 Hp0p1); auto.
1: solve B B' HBB'; simpl; rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1), (eqb_ntrans _ _ _ _ Hvv0 Hv0v1); auto.
1: { solve B B' HBB'; simpl.
  rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1).
  rewrite (label_eqb_ntrans _ _ _ Hll0 Hl0l1).
  simpl; auto.
}
1: eq_elim e e0 Hee0; eq_elim a a0 Haa0; solve B' B'' HB'B''.
1: eq_elim v v0 Hvv0; eq_elim a a0 Haa0; solve B' B'' HB'B''.
1: leq_elim l l0 Hll0; eq_elim a a0 Haa0; solve B' B'' HB'B''.

(* 28 cases left *)
(* Cond *)
2,4,6,8,17,28: eq_elim b b0 Hbb0;
  case (Xmerge B'1 B''1); case (Xmerge B'2 B''2); auto.
14,15,16,17,18,20,21: eq_elim b b0 Hbb0;
  case (Xmerge B1 B'1); case (Xmerge B2 B'2); auto.
14: {
  change (Xmerge (Xmerge (XCond b B1 B2) (XCond b0 B'1 B'2)) (XCond b1 B''1 B''2)
    = Xmerge (XCond b B1 B2) (Xmerge (XCond b0 B'1 B'2) (XCond b1 B''1 B''2))).
  case (eq_dec b b0); intro Hbb0;
  [rewrite <- eqb_eq in Hbb0 | rewrite <- eqb_neq in Hbb0].
  2: rewrite Xmerge_Cond_1; [case (eq_dec b0 b1); intro Hb0b1 | apply eqb_neq; auto].
  rewrite eqb_eq in Hbb0; rewrite <- Hbb0.
  clear b0 Hbb0 IHB''1 IHB''2.
  case (eq_dec b b1); intro Hbb1;
  [rewrite <- eqb_eq in Hbb1 | rewrite <- eqb_neq in Hbb1].
  2: rewrite (Xmerge_Cond_1 b b1); auto; [idtac | apply eqb_neq; auto].
  rewrite eqb_eq in Hbb1; rewrite <- Hbb1.
  clear b1 Hbb1.
  - elim (XUndefined_dec _ (Xmerge B1 B'1)); intro H1.
    * rewrite Xmerge_Cond_2; auto.
      elim (XUndefined_dec _ (Xmerge B'1 B''1)); intro H1'.
      1: rewrite Xmerge_Cond_2; auto.
      elim (XUndefined_dec _ (Xmerge B'2 B''2)); intro H2'.
      1: rewrite Xmerge_Cond_3; auto.
      rewrite Xmerge_Cond_inv; auto.
      rewrite Xmerge_Cond_2; auto.
      rewrite <- IHB1, H1; auto.
    * elim (XUndefined_dec _ (Xmerge B2 B'2)); intro H2.
      ++ rewrite Xmerge_Cond_3; auto.
         elim (XUndefined_dec _ (Xmerge B'1 B''1)); intro H1'.
         1: rewrite Xmerge_Cond_2; auto.
         elim (XUndefined_dec _ (Xmerge B'2 B''2)); intro H2'.
         1: rewrite Xmerge_Cond_3; auto.
         rewrite Xmerge_Cond_inv; auto.
         rewrite Xmerge_Cond_3; auto.
         rewrite <- IHB2, H2; auto.
      ++ rewrite Xmerge_Cond_inv; auto.
         elim (XUndefined_dec _ (Xmerge B'1 B''1)); intro H1'.
         -- rewrite (Xmerge_Cond_2 b b B'1); auto.
            rewrite Xmerge_Cond_2; auto.
            rewrite IHB1, H1', Xmerge_comm; auto.
         -- elim (XUndefined_dec _ (Xmerge B'2 B''2)); intro H2'.
            repeat rewrite Xmerge_Cond_3; auto. rewrite IHB2, H2', Xmerge_comm; auto.
            elim (XUndefined_dec _ (Xmerge B1 (Xmerge B'1 B''1))); intro H1''.
            rewrite Xmerge_Cond_2; auto. 2: rewrite IHB1; auto.
            rewrite Xmerge_Cond_inv; auto. rewrite Xmerge_Cond_2; auto.
            elim (XUndefined_dec _ (Xmerge B2 (Xmerge B'2 B''2))); intro H2''.
            rewrite Xmerge_Cond_3; auto. 2: rewrite IHB2; auto.
            rewrite Xmerge_Cond_inv; auto. rewrite Xmerge_Cond_3; auto.
            repeat rewrite Xmerge_Cond_inv; auto. rewrite IHB1, IHB2; auto.
            rewrite IHB1; auto. rewrite IHB2; auto.
  - elim (XUndefined_dec _ (Xmerge B1 B'1)); intro H1.
    rewrite Xmerge_Cond_2; auto.
    elim (XUndefined_dec _ (Xmerge B2 B'2)); intro H2.
    rewrite Xmerge_Cond_3; auto.
    rewrite Xmerge_Cond_inv, Xmerge_Cond_1; auto.
    apply eqb_neq; auto.
  - rewrite Hb0b1.
    elim (XUndefined_dec _ (Xmerge B'1 B''1)); intro H1'.
    rewrite Xmerge_Cond_2; auto.
    elim (XUndefined_dec _ (Xmerge B'2 B''2)); intro H2'.
    rewrite Xmerge_Cond_3; auto.
    rewrite Xmerge_Cond_inv, Xmerge_Cond_1; auto.
    apply eqb_neq; rewrite <- Hb0b1; auto.
  - rewrite Xmerge_Cond_1; auto.
}
1: change (XUndefined = 
  match (Xmerge (XBranching p mB mB') (XBranching p0 mB0 mB'0)) with
  XEnd => XEnd | _ => XUndefined end).
2: change (XUndefined = 
  match (Xmerge (XBranching p0 mB mB') (XBranching p1 mB0 mB'0)) with
  XSend p' e' a' B' => Xmerge (XSend p e a B) (XSend p' e' a' B')
  | _ => XUndefined end).
3: change (XUndefined = 
  match (Xmerge (XBranching p0 mB mB') (XBranching p1 mB0 mB'0)) with
  XRecv p' v' a' B' => Xmerge (XRecv p v a B) (XRecv p' v' a' B')
  | _ => XUndefined end).
4: change (XUndefined = 
  match (Xmerge (XBranching p0 mB mB') (XBranching p1 mB0 mB'0)) with
  XSel p' l' a' B' => Xmerge (XSel p l a B) (XSel p' l' a' B')
  | _ => XUndefined end).
5: change (Xmerge (Xmerge (XBranching p mB mB') (XBranching p0 mB0 mB'0))
   XEnd = XUndefined).
6: change (Xmerge (Xmerge (XBranching p mB mB') (XBranching p0 mB0 mB'0))
   (XSend p1 e a B'') = XUndefined).
7: change (Xmerge (Xmerge (XBranching p mB mB') (XBranching p0 mB0 mB'0))
   (XRecv p1 v a B'') = XUndefined).
8: change (Xmerge (Xmerge (XBranching p mB mB') (XBranching p0 mB0 mB'0))
   (XSel p1 l a B'') = XUndefined).
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
elim (eq_dec p p0); elim (eq_dec p0 p1); intros Hp0p1 Hpp0.
2: {
  rewrite <- Hpp0; rewrite <- Hpp0 in Hp0p1.
  rewrite <- eqb_neq in Hp0p1.
  transitivity XUndefined. 2: simpl; unfold eq_dec; rewrite Hp0p1; auto.
  elim (Xmerge_Branching_elim p mB mB' p mB0 mB'0); intros.
  rewrite a; auto.
  destroy b. rewrite b. simpl; unfold eq_dec; rewrite Hp0p1; auto.
}
2: {
  rewrite <- Hp0p1.
  rewrite <- eqb_neq in Hpp0.
  transitivity XUndefined. simpl; unfold eq_dec; rewrite Hpp0; auto.
  elim (Xmerge_Branching_elim p0 mB0 mB'0 p0 mB1 mB'1); intros.
  rewrite a; auto.
  destroy b. rewrite b. simpl; unfold eq_dec; rewrite Hpp0; auto.
}
2: { 
  rewrite <- eqb_neq in Hpp0, Hp0p1.
  simpl; unfold eq_dec; rewrite Hpp0, Hp0p1; auto.
}
rewrite <- Hp0p1, <- Hpp0; clear Hpp0 Hp0p1 p0 p1.
(* Final case branches into 64... *)
simpl. rewrite eqb_refl.
induction mB, mB', mB0, mB'0, mB1, mB'1.
all: try induction a as (A,a); try induction p0 as (A0,x);
     try induction p1 as (A1,x0); try induction p2 as (A2,x1);
     try induction p3 as (A3,x2); try induction p4 as (A4,x3).
(* YEOUCH *)
+ case_eq (eqb Ann A A1); intro HAA1. solve a x0 Ha0.
  2: case_eq (eqb Ann A0 A2); intro HA0A2. 2: solve x x1 H_1.
  all: case_eq (eqb Ann A1 A3); intro HA1A3; auto. all: solve x0 x2 H02.
  1,2,4,6,7: case_eq (eqb Ann A2 A4); intro HA2A4; auto.
  1,2,5,6: solve x1 x3 H13; rewrite eqb_refl.
  all: simpl.
  - rewrite HAA1, <- (H A a), Ha0; auto.
  - rewrite HAA1, <- (H0 A0 x), H_1; simpl; auto.
    solve a (Xmerge x0 x2) Ha02. rewrite HA0A2; auto.
  - rewrite HAA1, <- (H A a), <- (H0 A0 x); simpl; auto.
    solve (Xmerge a x0) x2 Ha02. rewrite HA0A2; auto.
  - rewrite HAA1; auto.
  - rewrite eqb_refl, (eqb_trans _ _ _ _ HAA1 HA1A3).
    solve (Xmerge a x0) x2 Ha02. solve x1 x3 H13.
    rewrite eqb_refl, HAA1, <- (H A a), HA0A2, Ha02; auto.
    rewrite (eqb_trans _ _ _ _ HA0A2 HA2A4); auto.
    solve (Xmerge x x1) x3 H13. solve x1 x3 H1_3.
    rewrite eqb_refl, HAA1, HA0A2, <- (H0 A0 x), H13; auto.
    rewrite Xmatch_elim; auto. rewrite <- (H A a); auto.
    solve x1 x3 H1_3. rewrite (H0 A0 x), H1_3 in H13; auto.
    elim H13. simpl; rewrite Xmerge_comm; auto.
    rewrite eqb_refl, HAA1, HA0A2, Xmatch_elim, Xmatch_elim; auto.
    all: try rewrite <- (H A a); try rewrite <- (H0 A0 x); auto.
  - rewrite eqb_refl, (eqb_trans _ _ _ _ HAA1 HA1A3).
    rewrite (eqb_ntrans _ _ _ _ HA0A2 HA2A4).
    solve (Xmerge a x0) x2 H_2; auto.
  - rewrite eqb_refl, (eqb_trans _ _ _ _ HAA1 HA1A3).
    rewrite (H A a), H02, Xmerge_comm; auto.
  - rewrite eqb_refl, (eqb_ntrans _ _ _ _ HAA1 HA1A3); auto.
all: admit.
Admitted.

(* Doable, but... 

+ solve a x0 Ha0. 2: solve x x1 H_1. all: solve x0 x2 H02.
  1,2,4: solve' x1 H1. 1,2,4: rewrite eqb_refl.
  - rewrite <- (H a), Ha0; auto.
  - rewrite <- (H a), H_1; simpl; auto. solve (Xmerge a x0) x2 Ha02.
  - simpl. rewrite eqb_refl. rewrite <- (H a); auto.
  - simpl. rewrite eqb_refl. solve (Xmerge a x0) x2 Ha02.
    rewrite Xmerge_comm; auto.
  - simpl. rewrite eqb_refl. rewrite (H a), H02, Xmerge_comm; auto.
+ solve a x0 Ha0. 2: solve x x1 H_1. all: solve' x0 H'0.
  1,2,4: solve x1 x2 H12. all: simpl; rewrite eqb_refl.
  - rewrite Ha0; auto.
  - rewrite <- (H0 x), H_1, Xmerge_comm; simpl; auto. solve' (Xmerge x0 a) H_.
  - rewrite Xmatch_elim; auto. rewrite (H0 x), H12, Xmerge_comm; auto.
  - rewrite Xmatch_elim; auto. solve (Xmerge x x1) x2 H_12.
    rewrite Xmatch_elim; auto. rewrite <- (H0 x), H_12; auto.
    rewrite Xmatch_elim; auto. rewrite <- (H0 x), Xmatch_elim; auto.
  - rewrite Xmerge_comm; auto.
+ solve a x0 Ha0. 2: solve x x1 H_1. all: solve' x0 H'0.
  1,2,4: solve' x1 H1. all: simpl; rewrite eqb_refl.
  - rewrite Ha0; auto.
  - rewrite Xmatch_elim, H_1; auto.
  - rewrite Xmatch_elim, Xmerge_comm; auto.
  - rewrite Xmerge_comm; auto.
+ solve a x0 Ha0. 2: solve' x H'. all: solve x0 x1 H01.
  1,2,4: solve' x2 H2. all: simpl; rewrite eqb_refl.
  - rewrite <- (H a), Ha0; auto.
  - solve a (Xmerge x0 x1) Ha01.
  - solve (Xmerge a x0) x1 Ha01. rewrite Xmerge_comm; auto.
  - solve (Xmerge a x0) x1 Ha01. rewrite <- (H a), Ha01; auto.
    solve x x2 H_2. rewrite <- (H a), Xmatch_elim; auto.
    rewrite <- (H a), Xmatch_elim, Xmatch_elim; auto.
  - rewrite (H a), H01, Xmerge_comm; auto.
+ solve a x0 Ha0. 2: solve' x H'. all: solve x0 x1 H01.
  all: simpl; rewrite eqb_refl.
  - rewrite <- (H a), Ha0; auto.
  - solve a (Xmerge x0 x1) Ha01.
  - rewrite (H a), H01, Xmerge_comm; auto.
  - solve (Xmerge a x0) x1 Ha01. rewrite <- (H a), Ha01; auto.
    rewrite Xmatch_elim, <- (H a), Xmatch_elim, Xmatch_elim; auto.
+ solve a x0 Ha0. 2: solve' x H'. all: solve' x0 H'0.
  1,2,4: solve' x1 H1. all: simpl; rewrite eqb_refl.
  - rewrite Ha0; auto.
  - rewrite Xmatch_elim; auto.
  - rewrite Xmatch_elim, Xmerge_comm; auto.
  - rewrite Xmerge_comm; auto.
+ solve a x0 Ha0. 2: solve' x H'. all: solve' x0 H'0.
  all: simpl; rewrite eqb_refl.
  - rewrite Ha0; auto.
  - rewrite Xmatch_elim; auto.
  - rewrite Xmerge_comm; auto.
+ solve' a Ha. 2: solve x x0 H_0. all: solve' x1 H1.
  1,2,4: solve x0 x2 H02. all: simpl; rewrite eqb_refl; auto.
  - rewrite <- (H0 x), H_0; simpl; auto. solve a x1 Ha1.
  - rewrite (H0 x), H02, (Xmerge_comm x); simpl; auto. solve a x1 Ha1.
  - solve a x1 Ha1. solve (Xmerge x x0) x2 H_02.
    rewrite <- (H0 x), H_02; auto. rewrite Xmatch_elim; auto.
    rewrite Xmatch_elim, <- (H0 x), Xmatch_elim; auto.
  - rewrite Xmerge_comm; auto.
+ solve' a Ha. 2: solve x x0 H_0. all: solve' x1 H1.
  1,2,4: solve' x0 H'0. all: simpl; rewrite eqb_refl; auto.
  - solve a x1 Ha1. rewrite H_0; auto.
  - solve a x1 Ha1. rewrite Xmerge_comm; auto.
  - rewrite Xmerge_comm; auto.
+ solve' a Ha. 2: solve x x0 H_0. all: solve x0 x1 H01.
  all: simpl; rewrite eqb_refl; auto.
  - rewrite Xmatch_elim, <- (H0 x), H_0; auto.
  - rewrite Xmatch_elim, (H0 x), H01, Xmerge_comm; auto.
  - rewrite Xmatch_elim; auto. solve (Xmerge x x0) x1 H_01.
    rewrite Xmatch_elim, <- (H0 x), H_01; auto.
    rewrite Xmatch_elim, <- (H0 x), Xmatch_elim; auto.
+ solve' a Ha. 2: solve x x0 H_0. all: solve' x0 H'0.
  all: simpl; rewrite eqb_refl; auto.
  - rewrite Xmatch_elim, H_0; auto.
  - rewrite Xmatch_elim, Xmerge_comm; auto.
+ solve' a Ha. 2: solve' x H_. all: solve' x0 H'0.
  1,2,4: solve' x1 H1. all: simpl; rewrite eqb_refl; auto.
  - solve a x0 Ha0.
  - solve a x0 Ha0; rewrite Xmerge_comm; auto.
  - rewrite Xmerge_comm; auto.
+ solve' a Ha. 2: solve' x H_. all: solve' x0 H'0.
  all: simpl; rewrite eqb_refl; auto.
  - solve a x0 Ha0.
  - rewrite Xmerge_comm; auto.
+ solve' a Ha. 2: solve' x H_. all: solve' x0 H'0.
  all: simpl; rewrite eqb_refl; auto.
  - rewrite Xmatch_elim; auto.
  - rewrite Xmatch_elim, Xmerge_comm; auto.
+ solve' a Ha. 2: solve' x H_. all: simpl; rewrite eqb_refl; auto.
  rewrite Xmatch_elim, Xmatch_elim; auto.
+ solve a x Ha_. 2: solve' x0 H'0. all: solve x x1 H_1.
  1,3: solve x0 x2 H02. all: simpl; rewrite eqb_refl; auto.
  - rewrite <- (H a), Ha_; auto.
  - rewrite H02. solve (Xmerge a x) x1 Ha_1.
  - solve (Xmerge a x) x1 Ha_1.
    rewrite <- (H a), Ha_1; auto.
    rewrite Xmatch_elim, <- (H a), Xmatch_elim, Xmatch_elim; auto.
  - rewrite (H a), H_1, Xmerge_comm; auto.
+ solve a x Ha_. 2: solve' x0 H'0. all: solve x x1 H_1.
  1,3: solve' x0 H'0. all: simpl; rewrite eqb_refl; auto.
  - rewrite <- (H a), Ha_; auto.
  - solve (Xmerge a x) x1 Ha_1.
    rewrite Xmatch_elim; auto. rewrite eqb_refl. rewrite <- (H a), Ha_1; auto.
    rewrite Xmatch_elim, Xmatch_elim; auto. rewrite eqb_refl.
    rewrite <- (H a), Xmatch_elim, Xmatch_elim; auto.
  - rewrite (H a), H_1, Xmerge_comm; auto.
+ solve a x Ha_. 2: solve' x0 H'0. all: solve' x H_.
  1,3: solve x0 x1 H01. all: simpl; rewrite eqb_refl; auto.
  - rewrite Ha_; auto.
  - rewrite Xmatch_elim, H01; auto.
  - rewrite Xmerge_comm; auto.
+ solve a x Ha_. 2: solve' x0 H'0. all: solve' x H_.
  1,3: solve' x0 H'0. all: simpl; rewrite eqb_refl; auto.
  - rewrite Ha_; auto.
  - repeat rewrite Xmatch_elim; auto. rewrite eqb_refl; auto.
  - rewrite Xmerge_comm; auto.
+ solve a x Ha_. all: solve x x0 H_0. 1,3: solve' x1 H1.
  all: simpl; rewrite eqb_refl; auto.
  - rewrite <- (H a), Ha_; auto.
  - solve (Xmerge a x) x0 Ha_0.
  - solve (Xmerge a x) x0 Ha_0. rewrite <- (H a), Ha_0; auto.
    rewrite Xmatch_elim, <- (H a), Xmatch_elim, Xmatch_elim; auto.
  - rewrite (H a), H_0, Xmerge_comm; auto.
+ solve a x Ha_. all: solve x x0 H_0. all: simpl; rewrite eqb_refl; auto.
  - rewrite <- (H a), Ha_; auto.
  - rewrite (H a), H_0, Xmerge_comm; auto.
  - solve (Xmerge a x) x0 Ha_0. rewrite <- (H a), Ha_0; auto.
    rewrite <- (H a), Xmatch_elim; auto.
+ solve a x Ha_. all: solve' x H_. 1,3: solve' x0 H'0.
  all: simpl; rewrite eqb_refl; auto.
  - rewrite Ha_; auto.
  - rewrite Xmatch_elim; auto.
  - rewrite Xmerge_comm; auto.
+ solve a x Ha_. all: solve' x H_. all: simpl; rewrite eqb_refl; auto.
  - rewrite Ha_; auto.
  - rewrite Xmerge_comm; auto.
+ solve' a Ha. 2: solve' x H_. all: solve' x0 H'0.
  1,3: solve x x1 H_1. all: simpl; rewrite eqb_refl; auto.
  - rewrite H_1. solve a x0 Ha0.
  - rewrite Xmerge_comm; auto.
+ solve' a Ha. 2: solve' x H_. all: solve' x0 H'0.
  1,3: solve' x H_. all: simpl; rewrite eqb_refl; auto.
  - solve a x0 Ha0.
    rewrite Xmatch_elim; auto. rewrite eqb_refl. rewrite Ha0; auto.
    repeat rewrite Xmatch_elim; auto. rewrite eqb_refl; auto.
  - rewrite Xmerge_comm; auto.
+ solve' a Ha. 2: solve' x H_. all: solve x x0 H_0.
  all: simpl; rewrite eqb_refl; auto. rewrite Xmatch_elim, H_0; auto.
+ solve' a Ha. all: solve' x H_.
  - rewrite eqb_refl; auto.
  - rewrite Xmatch_elim; auto.
+ solve' a Ha. all: solve' x H_. 1,3: solve' x0 H'0.
  all: simpl; rewrite eqb_refl; auto.
  - solve a x Ha_.
  - rewrite Xmerge_comm; auto.
+ solve' a Ha. all: solve' x H_. all: simpl; rewrite eqb_refl; auto.
  rewrite Xmerge_comm; auto.
+ solve' a Ha. all: solve' x H_. all: simpl; rewrite eqb_refl; auto.
  rewrite Xmatch_elim; auto.
+ solve' a Ha. all: simpl; rewrite eqb_refl; auto. rewrite Xmatch_elim; auto.
+ solve' x0 H'0. solve x x1 H_1. all: solve x0 x2 H02.
  1,3: solve x1 x3 H13. all: simpl; rewrite eqb_refl; auto.
  - rewrite Xmatch_elim, <- (H0 x), H_1; auto.
  - rewrite Xmatch_elim, (H0 x), H13, Xmerge_comm; auto.
  - rewrite Xmatch_elim; auto. solve (Xmerge x x1) x3 H_13.
    rewrite Xmatch_elim, <- (H0 x), H_13; auto.
    rewrite Xmatch_elim, <- (H0 x), Xmatch_elim; auto.
  - rewrite H02; auto.
+ solve' x0 H'0. solve x x1 H_1. all: solve x0 x2 H02.
  1,3: solve' x1 H1. all: simpl; rewrite eqb_refl; auto.
  - rewrite Xmatch_elim, H_1; auto.
  - rewrite Xmatch_elim, Xmerge_comm; auto.
  - rewrite H02; auto.
+ solve' x0 H'0. solve x x1 H_1. all: solve' x0 H'0.
  all: rewrite Xmatch_elim; auto. all: solve x1 x2 H12.
  all: simpl; rewrite eqb_refl; auto.
  - rewrite Xmatch_elim, <- (H0 x), H_1; auto.
  - rewrite Xmatch_elim, (H0 x), H12, Xmerge_comm; auto.
  - rewrite Xmatch_elim; auto. solve (Xmerge x x1) x2 H_12.
    rewrite Xmatch_elim, <- (H0 x), H_12; auto.
    rewrite Xmatch_elim, <- (H0 x), Xmatch_elim; auto.
+ solve' x0 H'0. solve x x1 H_1. all: solve' x0 H'0.
  all: rewrite Xmatch_elim; auto. all: solve' x1 H1.
  all: simpl; rewrite eqb_refl; auto.
  - rewrite Xmatch_elim, H_1; auto.
  - rewrite Xmatch_elim, Xmerge_comm; auto.
+ solve' x0 H'0. solve' x H_. all: solve x0 x1 H01.
  1,3: solve' x2 H2. all: simpl; rewrite eqb_refl; auto.
  - rewrite Xmatch_elim; auto.
  - rewrite Xmatch_elim, Xmerge_comm; auto.
  - rewrite H01; auto.
+ solve' x0 H'0. solve' x H_. all: solve x0 x1 H01.
  all: simpl; rewrite eqb_refl; auto.
  - rewrite Xmatch_elim; auto.
  - rewrite H01; auto.
+ solve' x0 H'0. solve' x H_. all: solve' x0 H'0.
  all: rewrite Xmatch_elim; auto. all: solve' x1 H1.
  all: simpl; rewrite eqb_refl; auto.
  - rewrite Xmatch_elim; auto.
  - rewrite Xmatch_elim, Xmerge_comm; auto.
+ solve' x0 H'0. solve' x H_. all: rewrite Xmatch_elim; auto.
  rewrite eqb_refl. rewrite Xmatch_elim; auto.
+ solve x x0 H_0. all: solve' x1 H1. 1,3: solve x0 x2 H02.
  all: simpl; rewrite eqb_refl; auto.
  - rewrite Xmatch_elim, <- (H0 x), H_0; auto.
  - rewrite Xmatch_elim, (H0 x), H02, Xmerge_comm; auto.
  - rewrite Xmatch_elim; auto. solve (Xmerge x x0) x2 H_02.
    rewrite Xmatch_elim, <- (H0 x), H_02; auto.
    rewrite Xmatch_elim, <- (H0 x), Xmatch_elim; auto.
+ solve x x0 H_0. all: solve' x1 H1. 1,3: solve' x0 H'0.
  all: simpl; rewrite eqb_refl; auto.
  - rewrite Xmatch_elim, H_0; auto.
  - rewrite Xmatch_elim, Xmerge_comm; auto.
+ solve x x0 H_0. all: solve x0 x1 H01. all: simpl; rewrite eqb_refl; auto.
  - rewrite <- (H0 x), H_0; auto.
  - rewrite (H0 x), H01, Xmerge_comm; auto.
  - solve (Xmerge x x0) x1 H_01.
    rewrite <- (H0 x), H_01; auto.
    rewrite <- (H0 x), Xmatch_elim; auto.
+ solve x x0 H_0. all: solve' x0 H'0. all: simpl; rewrite eqb_refl; auto.
  - rewrite H_0; auto.
  - rewrite Xmerge_comm; auto.
+ solve' x H_. all: solve' x0 H'0. 1,3: solve' x1 H1.
  all: simpl; rewrite eqb_refl; auto.
  - rewrite Xmatch_elim; auto.
  - rewrite Xmatch_elim, Xmerge_comm; auto.
+ solve' x H_. all: solve' x0 H'0. all: simpl; rewrite eqb_refl; auto.
  rewrite Xmatch_elim; auto.
+ solve' x H_. all: solve' x0 H'0. all: simpl; rewrite eqb_refl; auto.
  rewrite Xmerge_comm; auto.
+ solve' x H_. all: simpl; rewrite eqb_refl; auto.
  rewrite Xmatch_elim; auto.
+ solve' x H_. all: solve' x0 H'0. all: solve x x1 H1.
  2: solve x0 x2 H02. all: simpl; rewrite eqb_refl; auto.
  - rewrite H1; auto.
  - rewrite Xmatch_elim, H02; auto.
+ solve' x H_. solve' x0 H'0. all: solve x x1 H_1.
  all: simpl; rewrite eqb_refl; auto.
  - rewrite H_1; auto.
  - repeat rewrite Xmatch_elim; auto. rewrite eqb_refl; auto.
+ solve' x H_. solve' x0 H'0. all: rewrite Xmatch_elim; auto.
  solve x0 x1 H01. simpl; rewrite eqb_refl. rewrite Xmatch_elim, H01; auto.
+ solve' x H_. solve' x0 H'0.
+ solve' x H_. solve x x0 H_0. 2: solve' x1 H1.
  all: simpl; rewrite eqb_refl; auto.
  - rewrite H_0; auto.
  - rewrite Xmatch_elim; auto.
+ solve' x H_. solve x x0 H_0. simpl; rewrite eqb_refl. rewrite H_0; auto.
+ solve' x H_. rewrite Xmatch_elim; auto.
  solve' x0 H'0. simpl; rewrite eqb_refl. rewrite Xmatch_elim; auto.
+ solve' x H_.
+ solve' x H_. all: solve' x0 H'0. 2: solve x x1 H_1.
  all: simpl; rewrite eqb_refl; auto. rewrite Xmatch_elim, H_1; auto.
+ solve' x H_. all: solve' x0 H'0. 2: rewrite Xmatch_elim; auto.
  simpl; rewrite eqb_refl; auto.
+ solve' x H_. solve x x0 H_0. simpl; rewrite eqb_refl. rewrite H_0; auto.
+ solve' x H_.
+ solve' x H_. 2: solve' x0 H'0. all: simpl; rewrite eqb_refl; auto.
  rewrite Xmatch_elim; auto.
+ solve' x H_. simpl; rewrite eqb_refl; auto.
+ solve' x H_. simpl; rewrite eqb_refl; auto.
+ simpl; rewrite eqb_refl; auto.
Qed.
*)