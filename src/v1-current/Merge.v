Require Export Pruning.

Ltac eq_dec_elim t1 t2 H := case (eq_dec t1 t2); intro H;
    [rewrite <- eqb_eq in H | rewrite <- eqb_neq in H]; rewrite H;
    [idtac | try discriminate].

Section SP_Merge.

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

(** * Merging of two behaviours *)

(** ** Definition of merge
  We first define merge as a (total) function on extended behaviours.
  Undefinedness can not occur as a subterm.
*)

Fixpoint Xmerge (B1 B2:XBehaviour Sig) : XBehaviour Sig :=
match B1, B2 with
| XEnd,                     XEnd              => XEnd
| XSend p e a B,            XSend p' e' a' B' =>
    if (p =? p') && (e =? e') && (a =? a')
    then match Xmerge B B' with XUndefined => XUndefined
                              | _          => XSend p e a (Xmerge B B') end
    else XUndefined
| XRecv p v a B,            XRecv p' v' a' B' =>
    if (p =? p') && (v =? v') && (a =? a')
    then match Xmerge B B' with XUndefined => XUndefined
                              | _          => XRecv p v a (Xmerge B B') end
    else XUndefined
| XSel p l a B,             XSel p' l' a' B' =>
    if (p =? p') && (l =? l') && (a =? a')
    then match Xmerge B B' with XUndefined => XUndefined
                              | _          => XSel p l a (Xmerge B B') end
    else XUndefined
| XBranching p Bl Br,     XBranching p' Bl' Br' =>
    if (p =? p')
    then let BL := match Bl, Bl' with
                     None      , _            => Bl'
                   | _         , None         => Bl
                   | Some (a,B), Some (a',B') => if (a =? a')
                                                 then Some (a,Xmerge B B')
                                                 else Some (a,XUndefined)
                   end
      in let BR := match Br, Br' with
                     None      , _            => Br'
                   | _         , None         => Br
                   | Some (a,B), Some (a',B') => if (a =? a')
                                                 then Some (a, Xmerge B B')
                                                 else Some (a,XUndefined)
                   end
      in match BL, BR with Some (_,XUndefined), _ => XUndefined
                         | _, Some (_,XUndefined) => XUndefined
                         | _, _                   => XBranching p BL BR
         end
    else XUndefined
| XCond e B1 B2,          XCond e' B1' B2'      =>
    if (e =? e')
    then match Xmerge B1 B1', Xmerge B2 B2' with XUndefined, _ => XUndefined
                                               | _, XUndefined => XUndefined
                                               | Bt, Be        => XCond e Bt Be end
    else XUndefined
| XCall X,                XCall X'              =>
    if (X =? X') then XCall X else XUndefined
| _,                         _                  => XUndefined
end.

(** To merge two behaviours, we first inject them into extended behaviours. *)

Infix "[[\/]]" := Xmerge (at level 60).

Definition merge B1 B2 := inject B1 [[\/]] inject B2.

Infix "[\/]" := merge (at level 60).

(** ** Relationship with pruning 
  We start by characterizing the relationship between [merge] and [more_branches].
*)
Lemma larger_is_merge : forall B1 B2, B1 [>] B2 -> B1 [\/] B2 = inject B1.
Proof.
unfold merge; intros.
revert B2 H; BInduction B1; intros; inversion H; auto.
all: simpl; repeat rewrite eqb_refl.
all: try rewrite IHB1; repeat rewrite inject_match; simpl; auto.
+ rewrite IHB1_2, inject_match; simpl; auto.
+ rewrite IHB1_1, inject_match; simpl; auto.
+ rewrite IHB1_1, IHB1_2, inject_match, inject_match; auto.
+ rewrite IHB1_1, IHB1_2; auto.
  case_eq (inject B1_1); case_eq (inject B1_2); simpl; auto; intros;
    try elim (inject_not_undefined _ _ H6);
    elim (inject_not_undefined _ _ H7).
Qed.

Local Ltac XBAnn_elim t1 t2 H := case (@eq_dec (XBehaviour.Ann Sig) t1 t2); intro H;
    [rewrite H in *; rewrite eqb_refl
    | rewrite <- eqb_neq in H; rewrite H; discriminate].

Lemma merge_is_larger : forall B1 B2, B1 [\/] B2 = inject B1 -> B1 [>] B2.
Proof.
unfold merge.
BDInduction B1 B2; simpl; intros; try (inversion H; fail).
1: constructor.
all: elim (if_elim _ _ _ _ _ H); clear H; intro H; inversion_clear H;
    [idtac | discriminate].
all: try (elim (andb_prop _ _ H0); clear H0; intros H0 H0').
all: try (elim (andb_prop _ _ H0); clear H0; intros H0 H0'').
all: rewrite eqb_eq in H0; rewrite <- H0.
all: try (rewrite eqb_eq in H0'; rewrite <- H0').
all: try (rewrite eqb_eq in H0''; rewrite <- H0'').
all: try not_XUndef_with (inject B1 [[\/]] inject B2) Hm H1.
all: try (repeat rewrite inject_match in H1; inversion H1; fail).
all: try (constructor; eauto; fail).
1,2,3,5,7: revert H1; XBAnn_elim a a0 Haa0.
+ intro. not_XUndef_with (inject B1 [[\/]] inject B2) Hm H1.
  constructor; eauto.
+ intro. not_XUndef_with (inject B1 [[\/]] inject B2_1) Hm H1.
  rewrite inject_match in H2; inversion H2.
+ intro. not_XUndef_with (inject B1 [[\/]] inject B2) Hm H1.
  constructor; eauto.
+ intro. not_XUndef_with (inject B1_1 [[\/]] inject B2) Hm H1.
  rewrite inject_match in H2; inversion H2.
  constructor; eauto.
+ intro. not_XUndef_with (inject B1_1 [[\/]] inject B2_1) Hm H1.
  revert H1; XBAnn_elim a' a'0 Ha'a'0.
  intro. not_XUndef_with (inject B1_2 [[\/]] inject B2_2) Hm' H1.
  constructor; eauto.
+ rewrite inject_match in H1.
  revert H1; XBAnn_elim a a' Haa'.
  intro. not_XUndef_with (inject B1 [[\/]] inject B2_2) Hm H1.
+ rewrite inject_match in H1.
  revert H1; XBAnn_elim a' a0 Ha'a0.
  intro. not_XUndef_with (inject B1_2 [[\/]] inject B2) Hm H1.
  constructor; eauto.
+ rename B1_1 into Bt, B1_2 into Be, B2_1 into Bt', B2_2 into Be'.
  assert (inject Bt [[\/]] inject Bt' = inject Bt /\ inject Be [[\/]] inject Be' = inject Be).
  1: {
    elim (XUndefined_dec _ (inject Bt [[\/]] inject Bt')); intro.
    1: rewrite a in H1; inversion H1. 
    elim (XUndefined_dec _ (inject Be [[\/]] inject Be')); intro.
    1: rewrite a, Xmatch_elim in H1; auto; inversion H1.
    revert H1.
    case (inject Bt [[\/]] inject Bt'); case (inject Be [[\/]] inject Be');
      intros; try inversion H1; auto.
  }
  inversion_clear H. constructor; eauto.
Qed.

(** Summary of the previous two lemmas. *)

Lemma more_branches_merge : forall B1 B2, B1 [>] B2 <-> B1 [\/] B2 = inject B1.
Proof.
split.
+ apply larger_is_merge.
+ apply merge_is_larger.
Qed.

(** Idempotence follows from this characterization.
    Commutativity is the only algebraic property that needs to be proven directly. *)
Lemma merge_idempotent : forall B, B [\/] B = inject B.
Proof. intro. apply more_branches_merge, more_branches_refl. Qed.

Lemma Xmerge_comm : forall B B', B [[\/]] B' = B' [[\/]] B.
Proof.
XBDInduction B B'; simpl; auto.
(* Call *)
21: { 
  rewrite (eqb_sym _ X0); case_eq (X =? X0); intro HX0X; auto.
  rewrite eqb_eq in HX0X; rewrite HX0X; auto.
}
(* Cond *)
20: {
  rewrite (eqb_sym _ b0); case_eq (b =? b0); intro Hb0b; simpl; auto.
  rewrite eqb_eq in Hb0b; rewrite Hb0b, IHB1, IHB2; auto.
}
all: rewrite (eqb_sym _ p0); case_eq (p =? p0); intro Hp0p; simpl; auto;
     rewrite eqb_eq in Hp0p; rewrite <- Hp0p in *; clear p0 Hp0p.
1: rewrite (eqb_sym _ e0); case_eq (e =? e0); intro He0e; simpl; auto;
   rewrite eqb_eq in He0e; rewrite <- He0e in *; clear e0 He0e.
2: rewrite (eqb_sym _ v0); case_eq (v =? v0); intro Hv0v; simpl; auto;
   rewrite eqb_eq in Hv0v; rewrite <- Hv0v in *; clear v0 Hv0v.
3: rewrite (eqb_sym _ l0); case_eq (l =? l0); intro Hl0l; simpl; auto;
   rewrite eqb_eq in Hl0l; rewrite <- Hl0l in *; clear l0 Hl0l.
1,2,3: rewrite (eqb_sym _ a0); case_eq (a =? a0); intro Ha0a; simpl; auto;
       rewrite eqb_eq in Ha0a; rewrite <- Ha0a in *; rewrite IHB; auto.
(* Branch *)
6,8,11,14,16: rewrite (eqb_sym _ a0); case_eq (a =? a0); intro Haa0; simpl; auto;
       rewrite eqb_eq in Haa0; rewrite <- Haa0 in *; clear a0 Haa0.
16: rewrite (eqb_sym _ a0); case_eq (a' =? a0); intro Ha'a0; simpl; auto;
       rewrite eqb_eq in Ha'a0; rewrite <- Ha'a0 in *; clear a0 Ha'a0.
all: auto.
6: not_XUndef B'1 HB'1.
7: not_XUndef B1 HB1.
1,3: rewrite <- IHB; not_XUndef (B [[\/]] B') HBB'.
1: rewrite <- IHB; not_XUndef (B [[\/]] B'1) HBB'1.
1: rewrite <- IHB1; not_XUndef (Xmerge B1 B') HB1B'.
1: rewrite <- IHB1; not_XUndef (Xmerge B1 B'1) HB1B'1.
- rewrite (eqb_sym _ a'0); case_eq (a' =? a'0); intro Ha'a'0; simpl.
  rewrite <- IHB2. not_XUndef (Xmerge B2 B'2) HB2B'2.
  all: repeat rewrite Xmatch_elim; auto.
  rewrite eqb_eq in Ha'a'0; rewrite <- Ha'a'0; auto.
- rewrite (eqb_sym _ a'); case_eq (a =? a'); intro Haa'; simpl.
  rewrite <- IHB. not_XUndef (B [[\/]] B'2) HBB'2.
  all: repeat rewrite Xmatch_elim; auto.
  rewrite eqb_eq in Haa'; rewrite <- Haa'; auto.
- rewrite <- IHB2; not_XUndef (Xmerge B2 B') HB2B'; auto.
  all: rewrite Xmatch_elim; auto.
Qed.

Lemma merge_comm : forall B B', B [\/] B' = B' [\/] B.
Proof. intros. apply Xmerge_comm. Qed.

(** ** Inversion lemmas
  We first show that [Xmerge] is homomorphically defined. *)

Local Ltac Ann_kill a a' H' H'' := 
    case_eq (eqb (XBehaviour.Ann Sig) a a');
    [intro H'; rewrite eqb_eq in H'
    | intros; inversion H''].

Open Scope SP_scope.

Lemma Xmerge_Cond_inv : forall b Bt Bt' Be Be',
  Bt [[\/]] Bt' <> XUndefined -> Be [[\/]] Be' <> XUndefined ->
  XCond b Bt Be [[\/]] XCond b Bt' Be' = XCond b (Bt [[\/]] Bt') (Be [[\/]] Be').
Proof.
intros. revert H H0.
simpl. rewrite eqb_refl.
case_eq (Xmerge Bt Bt'); case_eq (Xmerge Be Be'); simpl; auto.
all: intros; try (elim H1; auto; fail); try (elim H2; auto; fail).
Qed.

Lemma Xmerge_inv_End : forall B B', B [[\/]] B' = XEnd -> B = XEnd /\ B' = XEnd.
Proof.
intros B1 B2.
case B1; case B2; try discriminate; auto.
+ intros. revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec _ (Xmerge x0 x)); intro.
  rewrite a; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. rewrite eqb_eq in Ht2t, Ht3t0, Ht4t1.
  rewrite Ht2t, Ht3t0, Ht4t1; intros.
  inversion H; eauto.
+ intros. revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec _ (Xmerge x0 x)); intro.
  rewrite a; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. intro; inversion H.
+ intros. revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec _ (Xmerge x0 x)); intro.
  rewrite a; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. intro; inversion H.
+ intros. exfalso.
  revert H. simpl.
  eq_dec_elim t0 t Ht0t.
  opt_elim o p; opt_elim o0 p; opt_elim o1 p; opt_elim o2 p; try discriminate.
  1,2: eq_dec_elim a1 a Ha1a; not_XUndef (Xmerge b1 b) Hb1b; try discriminate.
  1: eq_dec_elim a2 a0 Ha2a0; not_XUndef (Xmerge b2 b0) Hb2b0; try discriminate.
  2,3,6,7,11,12,13,14: not_XUndef b Hb; try discriminate.
  1,3,4,5,8,9: not_XUndef b0 Hb0; try discriminate.
  2: not_XUndef b Hb; try discriminate.
  1: eq_dec_elim a1 a Ha1a; not_XUndef (Xmerge b1 b) Hb1b; try discriminate.
  2,3,4: eq_dec_elim a0 a Ha0a; not_XUndef (Xmerge b0 b) Hb0b; try discriminate.
  1: eq_dec_elim a1 a0 Ha1a0; not_XUndef (Xmerge b1 b0) Hb1b0; try discriminate.
  1: not_XUndef b1 Hb1; try discriminate.
+ intros. exfalso.
  elim (XUndefined_dec _ (Xmerge x1 x)); intro H1.
  2: elim (XUndefined_dec _ (Xmerge x2 x0)); intro H0.
  - revert H. simpl. eq_dec_elim t0 t Ht0t. rewrite H1; discriminate.
  - revert H. simpl. eq_dec_elim t0 t Ht0t. rewrite H0, Xmatch_elim; auto. discriminate.
  - elim (eq_dec t0 t); intro Ht0t.
    rewrite Ht0t, Xmerge_Cond_inv in H; auto. discriminate.
    revert H; simpl. rewrite <- eqb_neq in Ht0t; rewrite Ht0t; discriminate.
+ intros. exfalso.
  revert H. simpl.
  eq_dec_elim t0 t Ht0t; discriminate.
Qed.

Lemma Xmerge_inv_Send : forall B1 B2 p e a B,
  B1 [[\/]] B2 = XSend p e a B -> exists B1' B2',
  B1 = XSend p e a B1' /\ B2 = XSend p e a B2' /\ B1' [[\/]] B2' = B.
Proof.
intros B1 B2.
case B1; case B2; try discriminate.
+ intros. revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec _ (Xmerge x0 x)); intro.
  rewrite a0; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. rewrite eqb_eq in Ht2t, Ht3t0, Ht4t1.
  rewrite Ht2t, Ht3t0, Ht4t1; intros.
  inversion H; eauto.
+ intros. revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec _ (Xmerge x0 x)); intro.
  rewrite a0; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. intro; inversion H.
+ intros. revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec _ (Xmerge x0 x)); intro.
  rewrite a0; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. intro; inversion H.
+ intros. exfalso.
  revert H. simpl.
  eq_dec_elim t0 t Ht0t.
  opt_elim o p0; opt_elim o0 p0; opt_elim o1 p0; opt_elim o2 p0; try discriminate.
  1,2: eq_dec_elim a2 a0 Ha2a0; not_XUndef (Xmerge b1 b) Hb1b; try discriminate.
  1: eq_dec_elim a3 a1 Ha3a1; not_XUndef (Xmerge b2 b0) Hb2b0; try discriminate.
  2,3,6,7,11,12,13,14: not_XUndef b Hb; try discriminate.
  1,3,4,5,8,9: not_XUndef b0 Hb0; try discriminate.
  2: not_XUndef b Hb; try discriminate.
  1: eq_dec_elim a2 a0 Ha2a0; not_XUndef (Xmerge b1 b) Hb1b; try discriminate.
  2,3,4: eq_dec_elim a1 a0 Ha1a0; not_XUndef (Xmerge b0 b) Hb0b; try discriminate.
  1: eq_dec_elim a2 a1 Ha2a1; not_XUndef (Xmerge b1 b0) Hb1b0; try discriminate.
  1: not_XUndef b1 Hb1; try discriminate.
+ intros. exfalso.
  elim (XUndefined_dec _ (Xmerge x1 x)); intro H1.
  2: elim (XUndefined_dec _ (Xmerge x2 x0)); intro H0.
  - revert H. simpl. eq_dec_elim t0 t Ht0t. rewrite H1; discriminate.
  - revert H. simpl. eq_dec_elim t0 t Ht0t. rewrite H0, Xmatch_elim; auto. discriminate.
  - elim (eq_dec t0 t); intro Ht0t.
    rewrite Ht0t, Xmerge_Cond_inv in H; auto. discriminate.
    revert H; simpl. rewrite <- eqb_neq in Ht0t; rewrite Ht0t; discriminate.
+ intros. exfalso.
  revert H. simpl.
  eq_dec_elim t0 t Ht0t; discriminate.
Qed.

Lemma Xmerge_inv_Recv : forall B1 B2 p x a B,
  B1 [[\/]] B2 = XRecv p x a B -> exists B1' B2',
  B1 = XRecv p x a B1' /\ B2 = XRecv p x a B2' /\ B1' [[\/]] B2' = B.
Proof.
intros B1 B2.
case B1; case B2; try discriminate.
+ intros. revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec _ (Xmerge x0 x)); intro.
  rewrite a0; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. intro; inversion H.
+ intros. revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec _ (Xmerge x0 x)); intro.
  rewrite a0; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. rewrite eqb_eq in Ht2t, Ht3t0, Ht4t1.
  rewrite Ht2t, Ht3t0, Ht4t1; intros.
  inversion H; eauto.
+ intros. revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec _ (Xmerge x0 x)); intro.
  rewrite a0; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. intro; inversion H.
+ intros. exfalso.
  revert H. simpl.
  eq_dec_elim t0 t Ht0t.
  opt_elim o p0; opt_elim o0 p0; opt_elim o1 p0; opt_elim o2 p0; try discriminate.
  1,2: eq_dec_elim a2 a0 Ha2a0; not_XUndef (Xmerge b1 b) Hb1b; try discriminate.
  1: eq_dec_elim a3 a1 Ha3a1; not_XUndef (Xmerge b2 b0) Hb2b0; try discriminate.
  2,3,6,7,11,12,13,14: not_XUndef b Hb; try discriminate.
  1,3,4,5,8,9: not_XUndef b0 Hb0; try discriminate.
  2: not_XUndef b Hb; try discriminate.
  1: eq_dec_elim a2 a0 Ha2a0; not_XUndef (Xmerge b1 b) Hb1b; try discriminate.
  2,3,4: eq_dec_elim a1 a0 Ha1a0; not_XUndef (Xmerge b0 b) Hb0b; try discriminate.
  1: eq_dec_elim a2 a1 Ha2a1; not_XUndef (Xmerge b1 b0) Hb1b0; try discriminate.
  1: not_XUndef b1 Hb1; try discriminate.
+ intros. exfalso.
  elim (XUndefined_dec _ (Xmerge x1 x)); intro H1.
  2: elim (XUndefined_dec _ (Xmerge x2 x0)); intro H0.
  - revert H. simpl. eq_dec_elim t0 t Ht0t. rewrite H1; discriminate.
  - revert H. simpl. eq_dec_elim t0 t Ht0t. rewrite H0, Xmatch_elim; auto. discriminate.
  - elim (eq_dec t0 t); intro Ht0t.
    rewrite Ht0t, Xmerge_Cond_inv in H; auto. discriminate.
    revert H; simpl. rewrite <- eqb_neq in Ht0t; rewrite Ht0t; discriminate.
+ intros. exfalso.
  revert H. simpl.
  eq_dec_elim t0 t Ht0t; discriminate.
Qed.

Lemma Xmerge_inv_Sel : forall B1 B2 p l a B,
  B1 [[\/]] B2 = XSel p l a B -> exists B1' B2',
  B1 = XSel p l a B1' /\ B2 = XSel p l a B2' /\ B1' [[\/]] B2' = B.
Proof.
intros B1 B2. case B1; case B2; try discriminate; intros.
+ revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec _ (Xmerge x0 x)); intro.
  rewrite a0; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. intro; inversion H.
+ intros. revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec _ (Xmerge x0 x)); intro.
  rewrite a0; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. intro; inversion H.
+ intros. revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec _ (Xmerge x0 x)); intro.
  rewrite a0; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. intro; inversion H.
  simpl. rewrite eqb_eq in Ht2t, Ht3t0, Ht4t1.
  rewrite <- Ht2t, <- Ht3t0, <- Ht4t1.
  inversion H; eauto.
+ intros. exfalso.
  revert H. simpl.
  eq_dec_elim t0 t Ht0t.
  opt_elim o p0; opt_elim o0 p0; opt_elim o1 p0; opt_elim o2 p0; try discriminate.
  1,2: eq_dec_elim a2 a0 Ha2a0; not_XUndef (Xmerge b1 b) Hb1b; try discriminate.
  1: eq_dec_elim a3 a1 Ha3a1; not_XUndef (Xmerge b2 b0) Hb2b0; try discriminate.
  2,3,6,7,11,12,13,14: not_XUndef b Hb; try discriminate.
  1,3,4,5,8,9: not_XUndef b0 Hb0; try discriminate.
  2: not_XUndef b Hb; try discriminate.
  1: eq_dec_elim a2 a0 Ha2a0; not_XUndef (Xmerge b1 b) Hb1b; try discriminate.
  2,3,4: eq_dec_elim a1 a0 Ha1a0; not_XUndef (Xmerge b0 b) Hb0b; try discriminate.
  1: eq_dec_elim a2 a1 Ha2a1; not_XUndef (Xmerge b1 b0) Hb1b0; try discriminate.
  1: not_XUndef b1 Hb1; try discriminate.
+ intros. exfalso.
  elim (XUndefined_dec _ (Xmerge x1 x)); intro H1.
  2: elim (XUndefined_dec _ (Xmerge x2 x0)); intro H0.
  - revert H. simpl. eq_dec_elim t0 t Ht0t. rewrite H1; discriminate.
  - revert H. simpl. eq_dec_elim t0 t Ht0t. rewrite H0, Xmatch_elim; auto. discriminate.
  - elim (eq_dec t0 t); intro Ht0t.
    rewrite Ht0t, Xmerge_Cond_inv in H; auto. discriminate.
    revert H; simpl. rewrite <- eqb_neq in Ht0t; rewrite Ht0t; discriminate.
+ intros. exfalso.
  revert H. simpl.
  eq_dec_elim t0 t Ht0t; discriminate.
Qed.

Lemma Xmerge_inv_Branching : forall B B' p Bl Br, B [[\/]] B' = XBranching p Bl Br ->
  exists Bl' Bl'' Br' Br'', B = XBranching p Bl' Br' /\ B' = XBranching p Bl'' Br''
  /\ (Bl = None -> Bl' = None /\ Bl'' = None)
  /\ (Br = None -> Br' = None /\ Br'' = None)
  /\ (forall a BL, Bl = Some (a,BL) ->
         (Bl' = None -> Bl'' = Some (a,BL)) /\ (Bl'' = None -> Bl' = Some (a,BL))
      /\ (forall a' BL' a'' BL'', Bl' = Some (a',BL') /\ Bl'' = Some (a'',BL'') ->
          a' = a /\ a'' = a /\ BL' [[\/]] BL'' = BL))
  /\ (forall a BR, Br = Some (a,BR) ->
         (Br' = None -> Br'' = Some (a,BR)) /\ (Br'' = None -> Br' = Some (a,BR))
      /\ (forall a' BR' a'' BR'', Br' = Some (a',BR') /\ Br'' = Some (a'',BR'') ->
          a' = a /\ a'' = a /\ BR' [[\/]] BR'' = BR)).
Proof.
intros B B' P E X HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (case o; case o0); try (case o1; case o2);
  simpl; auto; intros; try (inversion HBB'; fail).
all: elim (if_elim _ _ _ _ _ HBB'); intro H0; inversion_clear H0; clear HBB';
  [ try apply andb_prop in H; inversion H;
    try (apply andb_prop in H0; inversion H0) | inversion H1 ].
1,2,3: not_XUndef_with (Xmerge x0 x) HM H1.
all: rename H1 into H0; apply eqb_eq in H; clear H2.
all: try induction p as (a, x);
     try induction p0 as (a0, x0);
     try induction p1 as (a1, x1);
     try induction p2 as (a2, x2); revert H0.
+ Ann_kill a0 a2 Ha0a2 H1. Ann_kill a a1 Haa1 H1.
  intros. not_XUndef_with (Xmerge x0 x2) HM H0.
  not_XUndef_with (Xmerge x x1) HM' H0.
  exists (Some (a0,x0)), (Some (a2,x2)), (Some (a,x)), (Some (a1,x1)); rewrite H;
  repeat (split; auto); intros; inversion H1;
  inversion H6; inversion H7; inversion H10; auto.
  2: transitivity a2; auto. 1,2: transitivity a0; auto.
  2: transitivity a1; auto. 1,2: transitivity a; auto.
  revert H1. case (Xmerge x0 x2); intros; inversion H1.
+ Ann_kill a a1 Haa1 H1.
  intro; not_XUndef_with (Xmerge x x1) HM H0; not_XUndef_with x0 HM' H0.
  exists (Some (a,x)), (Some (a1,x1)), None, (Some (a0,x0)); rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H6;
    try (inversion H7; inversion H10; auto).
  2: transitivity a1; auto. all: transitivity a; auto.
+ intro; not_XUndef_with x1 HM H0.
  revert H0. Ann_kill a a0 Haa0 H1.
  intro; not_XUndef_with (Xmerge x x0) HM' H0.
  exists None, (Some (a1,x1)), (Some (a,x)), (Some (a0,x0)); rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H6;
    try (inversion H7; inversion H10; auto).
  2: transitivity a0; auto. all: transitivity a; auto.
+ intro; not_XUndef_with x0 HM H0; not_XUndef_with x HM' H0;
  exists None, (Some (a0,x0)), None, (Some (a,x)); rewrite H;
  repeat (split; auto); try inversion H0; intros; try inversion H6;
    try (inversion H7; auto).
+ Ann_kill a0 a1 Ha0a1 H1.
  intro; not_XUndef_with (Xmerge x0 x1) HM H0; not_XUndef_with x HM' H0.
  exists (Some (a0,x0)), (Some (a1,x1)), (Some (a,x)), None; rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H6;
    try (inversion H7; inversion H10; auto).
  2: transitivity a1; auto. all: transitivity a0; auto.
+ Ann_kill a a0 Haa0 H1.
  intro; not_XUndef_with (Xmerge x x0) HM' H0.
  exists (Some (a,x)), (Some (a0,x0)), None, None; rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try (inversion H6; inversion H9; auto).
  2: transitivity a0; auto. all: transitivity a; auto.
+ intro; not_XUndef_with x0 HM H0; not_XUndef_with x HM' H0.
  exists None, (Some (a0,x0)), (Some (a,x)), None; rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H6;
    try (inversion H7; inversion H10; auto).
+ intro; not_XUndef_with x HM' H0.
  exists None, (Some (a,x)), None, None; rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try (inversion H6; auto).
+ intro; not_XUndef_with x0 HM H0.
  revert H0. Ann_kill a a1 Haa1 H1.
  intro; not_XUndef_with (Xmerge x x1) HM' H0.
  exists (Some (a0,x0)), None, (Some (a,x)), (Some (a1,x1)); rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H6;
    try (inversion H7; inversion H10; auto).
  2: transitivity a1; auto. all: transitivity a; auto.
+ intro; not_XUndef_with x HM H0; not_XUndef_with x0 HM' H0.
  exists (Some (a,x)), None, None, (Some (a0,x0)); rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H6;
    try (inversion H7; inversion H10; auto).
+ Ann_kill a a0 Haa0 H1.
  intro; not_XUndef_with (Xmerge x x0) HM' H0.
  exists None, None, (Some (a,x)), (Some (a0,x0)); rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try (inversion H6; inversion H9; auto).
  2: transitivity a0; auto. all: transitivity a; auto.
+ intro; not_XUndef_with x HM' H0.
  exists None, None, None, (Some (a,x)); rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try (inversion H6; auto).
+ intro; not_XUndef_with x0 HM H0; not_XUndef_with x HM' H0.
  exists (Some (a0,x0)), None, (Some (a,x)), None; rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H6;
    try (inversion H7; inversion H10; auto).
+ intro; not_XUndef_with x HM' H0.
  exists (Some (a,x)), None, None, None; rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try (inversion H9; auto).
+ intro; not_XUndef_with x HM' H0.
  exists None, None, (Some (a,x)), None; rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try (inversion H9; auto).
+ intro; exists None, None, None, None;
  repeat (split; auto); try inversion H0; auto.
  rewrite H; auto.
  all: try (rewrite H1 in H4; inversion H4).
  all: try (inversion H2; inversion H3).
  all: rewrite H1 in H5; inversion H5.
+ case (Xmerge x1 x); case (Xmerge x2 x0); intros; inversion H0.
+ intro; inversion H0.
Qed.

Lemma Xmerge_inv_Branching_None_None : forall B B' p, B [[\/]] B' = XBranching p None None ->
  B = XBranching p None None /\ B' = XBranching p None None.
Proof.
intros.
apply Xmerge_inv_Branching in H; destroy H.
elim H2; auto; elim H3; auto; intros.
rewrite H0, H1, H5, H6, H7, H8; auto.
Qed.

Lemma Xmerge_inv_Branching_Some_None : forall B B' p a Bl,
  B [[\/]] B' = XBranching p (Some (a,Bl)) None ->
  (B = XBranching p None None /\ B' = XBranching p (Some (a,Bl)) None)
  \/ (B = XBranching p (Some (a,Bl)) None /\ B' = XBranching p None None)
  \/ exists BL' BL'', B = XBranching p (Some (a,BL')) None
     /\ B' = XBranching p (Some (a,BL'')) None /\ BL' [[\/]] BL'' = Bl.
Proof.
intros.
apply Xmerge_inv_Branching in H; destroy H.
clear H H2. eelim H4; eauto. elim H3; auto.
clear H3 H4; intros. destroy H4.
rewrite H0, H1, H, H2 in *.
clear B B' x1 x2 H0 H1 H H2.
opt_elim x p0; opt_elim x0 p0; intros.
+ right. right. eelim H4; eauto.
  exists b, b0. destroy H2. rewrite H1, H6; auto.
+ right. left. rewrite H5 in H0; auto. inversion H0; auto.
+ left. rewrite H3 in H; auto. inversion H; auto.
+ rewrite H3 in H; auto. inversion H.
Qed.

Lemma Xmerge_inv_Branching_None_Some : forall B B' p a Br,
  B [[\/]] B' = XBranching p None (Some (a,Br)) ->
  (B = XBranching p None None /\ B' = XBranching p None (Some (a,Br)))
  \/ (B = XBranching p None (Some (a,Br)) /\ B' = XBranching p None None)
  \/ exists BR' BR'', B = XBranching p None(Some (a,BR'))
     /\ B' = XBranching p None (Some (a,BR'')) /\ BR' [[\/]] BR'' = Br.
Proof.
intros.
apply Xmerge_inv_Branching in H; destroy H.
clear H3 H4. eelim H; eauto. elim H2; auto.
clear H H2; intros. destroy H4.
rewrite H0, H1, H, H2 in *.
clear B B' x x0 H0 H1 H H2.
opt_elim x1 p0; opt_elim x2 p0; intros.
+ right. right. eelim H4; eauto.
  exists b, b0. destroy H2. rewrite H1, H6; auto.
+ right. left. rewrite H5 in H0; auto. inversion H0; auto.
+ left. rewrite H3 in H; auto. inversion H; auto.
+ rewrite H3 in H; auto. inversion H.
Qed.

Lemma Xmerge_inv_Cond : forall B B' b Be Bt, B [[\/]] B' = XCond b Be Bt ->
  exists Be' Be'' Bt' Bt'', B = XCond b Be' Bt' /\ B' = XCond b Be'' Bt''
    /\ Be' [[\/]] Be'' = Be /\ Bt' [[\/]] Bt'' = Bt.
Proof.
intros B B'; case B; case B'; try discriminate; intros.
+ revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec _ (Xmerge x0 x)); intro.
  rewrite a; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. intro; inversion H.
+ intros. revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec _ (Xmerge x0 x)); intro.
  rewrite a; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. intro; inversion H.
+ intros. revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec _ (Xmerge x0 x)); intro.
  rewrite a; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. intro; inversion H.
+ intros. exfalso.
  revert H. simpl.
  eq_dec_elim t0 t Ht0t.
  opt_elim o p; opt_elim o0 p; opt_elim o1 p; opt_elim o2 p; try discriminate.
  1,2: eq_dec_elim a1 a Ha1a; not_XUndef (Xmerge b2 b0) Hb2b0; try discriminate.
  1: eq_dec_elim a2 a0 Ha2a0; not_XUndef (Xmerge b3 b1) Hb3b1; try discriminate.
  2,3,6,7,11,12,13,14: not_XUndef b0 Hb0; try discriminate.
  1,3,4,5,8,9: not_XUndef b1 Hb1; try discriminate.
  2: not_XUndef b0 Hb0; try discriminate.
  1: eq_dec_elim a1 a Ha1a; not_XUndef (Xmerge b2 b0) Hb2b0; try discriminate.
  2,3,4: eq_dec_elim a0 a Ha0a; not_XUndef (Xmerge b1 b0) Hb1b0; try discriminate.
  1: eq_dec_elim a1 a0 Ha1a0; not_XUndef (Xmerge b2 b1) Hb2b1; try discriminate.
  1: not_XUndef b2 Hb2; try discriminate.
+ intros.
  revert H; simpl. eq_dec_elim t0 t Ht0t.
  elim (XUndefined_dec _ (Xmerge x1 x)); intro HM.
  rewrite HM; discriminate.
  elim (XUndefined_dec _ (Xmerge x2 x0)); intro HM'.
  rewrite HM', Xmatch_elim; auto; discriminate.
  exists x1, x, x2, x0.
  revert HM HM' H.
  rewrite eqb_eq in Ht0t; rewrite Ht0t.
  case (Xmerge x1 x); case (Xmerge x2 x0); intros;
  inversion H; auto.
+ intros. exfalso.
  revert H. simpl.
  eq_dec_elim t0 t Ht0t; discriminate.
Qed.

Lemma Xmerge_inv_Call : forall B B' X, B [[\/]] B' = XCall X -> B = XCall X /\ B' = XCall X.
Proof.
intros B1 B2.
case B1; case B2; try discriminate; auto.
+ intros. revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec _ (Xmerge x0 x)); intro.
  rewrite a; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. rewrite eqb_eq in Ht2t, Ht3t0, Ht4t1.
  rewrite Ht2t, Ht3t0, Ht4t1; intros.
  inversion H; eauto.
+ intros. revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec _ (Xmerge x0 x)); intro.
  rewrite a; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. intro; inversion H.
+ intros. revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec _ (Xmerge x0 x)); intro.
  rewrite a; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. intro; inversion H.
+ intros. exfalso.
  revert H. simpl.
  eq_dec_elim t0 t Ht0t.
  opt_elim o p; opt_elim o0 p; opt_elim o1 p; opt_elim o2 p; try discriminate.
  1,2: eq_dec_elim a1 a Ha1a; not_XUndef (Xmerge b1 b) Hb1b; try discriminate.
  1: eq_dec_elim a2 a0 Ha2a0; not_XUndef (Xmerge b2 b0) Hb2b0; try discriminate.
  2,3,6,7,11,12,13,14: not_XUndef b Hb; try discriminate.
  1,3,4,5,8,9: not_XUndef b0 Hb0; try discriminate.
  2: not_XUndef b Hb; try discriminate.
  1: eq_dec_elim a1 a Ha1a; not_XUndef (Xmerge b1 b) Hb1b; try discriminate.
  2,3,4: eq_dec_elim a0 a Ha0a; not_XUndef (Xmerge b0 b) Hb0b; try discriminate.
  1: eq_dec_elim a1 a0 Ha1a0; not_XUndef (Xmerge b1 b0) Hb1b0; try discriminate.
  1: not_XUndef b1 Hb1; try discriminate.
+ intros. exfalso.
  elim (XUndefined_dec _ (Xmerge x1 x)); intro H1.
  2: elim (XUndefined_dec _ (Xmerge x2 x0)); intro H0.
  - revert H. simpl. eq_dec_elim t0 t Ht0t. rewrite H1; discriminate.
  - revert H. simpl. eq_dec_elim t0 t Ht0t. rewrite H0, Xmatch_elim; auto. discriminate.
  - elim (eq_dec t0 t); intro Ht0t.
    rewrite Ht0t, Xmerge_Cond_inv in H; auto. discriminate.
    revert H; simpl. rewrite <- eqb_neq in Ht0t; rewrite Ht0t; discriminate.
+ intros.
  revert H; simpl.
  eq_dec_elim t0 t Ht0t; auto.
  rewrite eqb_eq in Ht0t; rewrite Ht0t; auto.
Qed.

(** From these we trivially obtain the corresponding lemmas for merge. *)

Lemma merge_inv_End : forall B B', B [\/] B' = XEnd -> B = End _ /\ B' = End _.
Proof.
unfold merge; intros.
apply Xmerge_inv_End in H; destroy H.
revert H0. case B; try discriminate; simpl; intros.
revert H. case B'; try discriminate; simpl; intros.
- auto.
- exfalso.
  revert H. opt_elim o p.
  all: opt_elim o0 p; discriminate.
- exfalso.
  revert H0. opt_elim o p.
  all: opt_elim o0 p; discriminate.
Qed.

Lemma merge_inv_Send : forall B B' p e a X, B [\/] B' = XSend p e a X ->
  exists B1 B1', B = p ! e @! a; B1 /\ B' = p ! e @! a; B1' /\ B1 [\/] B1' = X.
Proof.
unfold merge; intros.
apply Xmerge_inv_Send in H; destroy H.
revert H0. case B; try discriminate; simpl; intros.
revert H1. case B'; try discriminate; simpl; intros.
- exists b, b0; inversion H0; inversion H1.
  rewrite H6, H10; repeat split; auto.
- exfalso.
  revert H1. opt_elim o p0.
  all: opt_elim o0 p0; discriminate.
- exfalso.
  revert H0. opt_elim o p0.
  all: opt_elim o0 p0; discriminate.
Qed.

Lemma merge_inv_Recv : forall B B' p v a X, B [\/] B' = XRecv p v a X ->
  exists B1 B1', B = p ? v @?a ; B1 /\ B' = p ? v @?a ; B1' /\ B1 [\/] B1' = X.
Proof.
unfold merge; intros.
apply Xmerge_inv_Recv in H; destroy H.
revert H0. case B; try discriminate; simpl; intros.
revert H1. case B'; try discriminate; simpl; intros.
- exists b, b0; inversion H0; inversion H1.
  rewrite H6, H10; repeat split; auto.
- exfalso.
  revert H1. opt_elim o p0.
  all: opt_elim o0 p0; discriminate.
- exfalso.
  revert H0. opt_elim o p0.
  all: opt_elim o0 p0; discriminate.
Qed.

Lemma merge_inv_Sel : forall B B' p l a X, B [\/] B' = XSel p l a X ->
  exists B1 B1', B = p (+) l @+ a; B1 /\ B' = p (+) l @+ a; B1' /\ B1 [\/] B1' = X.
Proof.
unfold merge; intros.
apply Xmerge_inv_Sel in H. destroy H.
revert H0. case B; try discriminate; simpl; intros.
revert H1. case B'; try discriminate; simpl; intros.
- exists b, b0; inversion H0; inversion H1.
  rewrite H6, H10; repeat split; auto.
- exfalso.
  revert H1. opt_elim o p0.
  all: opt_elim o0 p0; discriminate.
- exfalso.
  revert H0. opt_elim o p0.
  all: opt_elim o0 p0; discriminate.
Qed.

(* The direct proof still seems simpler. *)
Lemma merge_inv_Branching : forall B B' p Bl Br, B [\/] B' = XBranching p Bl Br ->
  exists Bl' Bl'' Br' Br'', B = p & Bl' // Br' /\ B' = p & Bl'' // Br''
  /\ (Bl = None -> Bl' = None /\ Bl'' = None)
  /\ (Br = None -> Br' = None /\ Br'' = None)
  /\ (forall a BL, Bl = Some (a,BL) ->
         (Bl' = None -> exists BL'', Bl'' = Some (a,BL'') /\ BL = inject BL'')
      /\ (Bl'' = None -> exists BL', Bl' = Some (a,BL') /\ BL = inject BL')
      /\ (forall a' a'' BL' BL'', Bl' = Some (a',BL') /\ Bl'' = Some (a'',BL'') ->
            a' = a /\ a'' = a /\ BL' [\/] BL'' = BL))
  /\ (forall a BR, Br = Some (a,BR) ->
         (Br' = None -> exists BR'', Br'' = Some (a,BR'') /\ BR = inject BR'')
      /\ (Br'' = None -> exists BR', Br' = Some (a,BR') /\ BR = inject BR')
      /\ (forall a' a'' BR' BR'', Br' = Some (a',BR') /\ Br'' = Some (a'',BR'') ->
            a' = a /\ a'' = a /\ BR' [\/] BR'' = BR)).
Proof.
unfold merge.
intros B B' P E X HBB'; revert HBB'.
BDInduction B B'; simpl; auto; intros; try (inversion HBB'; fail).
all: elim (if_elim _ _ _ _ _ HBB'); intro H0; inversion_clear H0; clear HBB';
  [ repeat (apply andb_prop in H; destruct H) | inversion H1 ].
all: repeat rewrite inject_match in H1; try (inversion H1; fail).
1,2,3: not_XUndef_with (Xmerge (inject B) (inject B')) HM H1.
all: revert H1.
6,8,11,14,16: Ann_kill a a0 Haa0 H1.
14: Ann_kill a a' Haa' H1.
16: Ann_kill a' a0 Ha'a0 H1.
all: intros.
6,8: not_XUndef_with (Xmerge (inject B) (inject B')) HM H1.
8: not_XUndef_with (Xmerge (inject B) (inject B'1)) HM H1.
9: not_XUndef_with (Xmerge (inject B1) (inject B')) HM H1.
10: not_XUndef_with (Xmerge (inject B1) (inject B'1)) HM H1.
14: not_XUndef_with (Xmerge (inject B) (inject B'2)) HM H1.
16: not_XUndef_with (Xmerge (inject B2) (inject B')) HM H1.
10: revert H1. 10: Ann_kill a' a'0 Ha'a'0 H1.
10: intro; not_XUndef_with (Xmerge (inject B2) (inject B'2)) HM' H1.
all: inversion H1.
all: apply eqb_eq in H; rewrite <- H in *.
1: do 4 eexists; repeat split; eauto; inversion H0.
1,2,3,4,10,11,12,14: do 4 eexists; repeat split; eauto; inversion H0; eauto;
  inversion H5; inversion H6; inversion H9; auto.
1,2,3,4: do 4 eexists; repeat split; eauto; inversion H0; eauto; intros;
  inversion H8; inversion H9; inversion H12; auto;
  [idtac | transitivity a0; auto]; transitivity a; auto.
1:{ do 4 eexists; repeat split; eauto; inversion H0; eauto; intros;
  inversion H9; inversion H10; inversion H13; auto.
  2: transitivity a0; auto. 1,2: transitivity a; auto.
  2: transitivity a'0; auto. all: transitivity a'; auto.
}
1: do 4 eexists; repeat split; eauto; inversion H0; eauto; intros;
  inversion H8; inversion H9; inversion H12; auto;
  [idtac | transitivity a'; auto]; transitivity a; auto.
1: do 4 eexists; repeat split; eauto; inversion H0; eauto; intros;
  inversion H8; inversion H9; inversion H12; auto;
  [idtac | transitivity a0; auto]; transitivity a'; auto.
+ revert H1.
  case (Xmerge (inject B1) (inject B'1));
  case (Xmerge (inject B2) (inject B'2)); intros; inversion H1.
Qed.

Lemma merge_inv_Branching_None_None : forall B B' p,
  B [\/] B' = XBranching p None None ->
  B = p & None // None /\ B' = p & None // None.
Proof.
intros.
elim (merge_inv_Branching _ _ _ _ _ H); intros.
destroy H0.
elim H3; auto; elim H4; auto.
intros. rewrite H1, H2, H6, H7, H8, H9; auto.
Qed.

Lemma merge_inv_Branching_Some_None : forall B B' p a Bl,
  B [\/] B' = XBranching p (Some (a,Bl)) None ->
  (B = p & None // None /\ exists BL, B' = p & Some (a,BL) // None  /\ Bl = inject BL)
  \/ ((exists BL, B = p & Some (a,BL) // None /\ Bl = inject BL) /\ B' = p & None // None)
  \/ exists BL' BL'', B = p & Some (a,BL') // None /\ B' = p & Some (a,BL'') // None
    /\ BL' [\/] BL'' = Bl.
Proof.
intros.
elim (merge_inv_Branching _ _ _ _ _ H); intros.
destroy H0.
clear H3; elim H4; auto.
clear H0; elim (H5 _ _ (eq_refl _)).
intros. inversion_clear H3.
rewrite H1, H2, H6, H7 in *.
clear B B' x1 x2 H1 H2 H6 H7 H4 H5.
induction x. rename a0 into B. all: induction x0. 1,3: rename a0 into B'.
+ right. right. clear H0 H8. induction B, B'. exists b, b0.
  elim (H9 _ _ _ _ (conj (eq_refl _) (eq_refl _))); intros. inversion_clear H1.
  rewrite H0, H2; auto.
+ left. split; auto. induction B'. exists b.
  elim H0; auto; intros. destroy H1. inversion H2. auto.
+ right. left. split; auto. induction B. exists b.
  elim H8; auto; intros. destroy H1. inversion H2. auto.
+ exfalso.
  unfold merge in H; simpl in H.
  unfold eq_dec in H; rewrite eqb_refl in H. inversion H.
Qed.

Lemma merge_inv_Branching_None_Some : forall B B' p a Br,
  B [\/] B' = XBranching p None (Some (a,Br)) ->
  (B = p & None // None /\ exists BR, B' = p & None // Some (a,BR)  /\ Br = inject BR)
  \/ ((exists BR, B = p & None // Some (a,BR) /\ Br = inject BR) /\ B' = p & None // None)
  \/ exists BR' BR'', B = p & None // Some (a,BR') /\ B' = p & None // Some (a,BR'')
    /\ BR' [\/] BR'' = Br.
Proof.
intros.
elim (merge_inv_Branching _ _ _ _ _ H); intros.
destroy H0.
clear H4; elim H3; auto.
clear H5; elim (H0 _ _ (eq_refl _)).
intros. inversion_clear H5.
rewrite H1, H2, H6, H7 in *.
clear B B' x x0 H1 H2 H6 H7 H3.
induction x1. rename a0 into B. all: induction x2. 1,3: rename a0 into B'.
+ right. right. clear H0 H8. induction B, B'. exists b, b0.
  elim (H9 _ _ _ _ (conj (eq_refl _) (eq_refl _))); intros. inversion_clear H1.
  rewrite H0, H2; auto.
+ left. split; auto. induction B'. exists b.
  elim H4; auto; intros. destroy H1. inversion H2. auto.
+ right. left. split; auto. induction B. exists b.
  elim H8; auto; intros. destroy H1. inversion H2. auto.
+ exfalso.
  unfold merge in H; simpl in H.
  unfold eq_dec in H; rewrite eqb_refl in H. inversion H.
Qed.

Lemma merge_inv_Cond : forall B B' b Be Bt, merge B B' = XCond b Be Bt ->
  exists Be' Be'' Bt' Bt'', B = If b Then Be' Else Bt' /\ B' = If b Then Be'' Else Bt''
    /\ Be' [\/] Be'' = Be /\ Bt' [\/] Bt'' = Bt.
Proof.
unfold merge; intros.
apply Xmerge_inv_Cond in H. destroy H.
revert H0. case B; try discriminate; simpl; intros.
2: revert H1. 2: case B'; try discriminate; simpl; intros.
- exfalso.
  revert H0. opt_elim o p.
  all: opt_elim o0 p; discriminate.
- exfalso.
  revert H1. opt_elim o p.
  all: opt_elim o0 p; discriminate.
- inversion H0; inversion H1.
  exists b0, b2, b1, b3; repeat split; auto.
  rewrite H5, H8; auto. rewrite H6, H9; auto.
Qed.

Lemma merge_inv_Call : forall B B' X, B [\/] B' = XCall X -> B = Call _ X /\ B' = Call _ X.
Proof.
unfold merge; intros.
apply Xmerge_inv_Call in H. destroy H.
revert H0. case B; try discriminate; simpl; intros.
2: revert H. 2: case B'; try discriminate; simpl; intros.
- exfalso.
  revert H0. opt_elim o p.
  all: opt_elim o0 p; discriminate.
- exfalso.
  revert H. opt_elim o p.
  all: opt_elim o0 p; discriminate.
- inversion H0; inversion H. auto.
Qed.

(** We can now prove that [merge] is a partial lub. *)
Lemma merge_is_upper_bound : forall B1 B2 B, B1 [\/] B2 = inject B -> B [>] B1.
Proof.
unfold merge; intros.
rename H into Hinj; revert B1 B2 Hinj.
BInduction B; simpl; intros.
+ elim (merge_inv_End _ _ Hinj); intros.
  rewrite H; constructor.
+ elim (merge_inv_Send _ _ _ _ _ _ Hinj); intros.
  rename x into B1'; inversion_clear H.
  rename x into B2'; inversion_clear H0.
  inversion_clear H1.
  rewrite H; constructor; eauto.
+ elim (merge_inv_Recv _ _ _ _ _ _ Hinj); intros.
  rename x into B1'; inversion_clear H.
  rename x into B2'; inversion_clear H0.
  inversion_clear H1.
  rewrite H; constructor; eauto.
+ elim (merge_inv_Sel _ _ _ _ _ _ Hinj); intros.
  rename x into B1'; inversion_clear H.
  rename x into B2'; inversion_clear H0.
  inversion_clear H1.
  rewrite H; constructor; eauto.
+ elim (merge_inv_Branching_None_None _ _ _ Hinj); intros.
  rewrite H; apply more_branches_refl.
+ elim (merge_inv_Branching_Some_None _ _ _ _ _ Hinj); intros.
  - destroy H. rewrite H0. constructor.
  - inversion_clear H; destroy H0.
    destroy H. apply inject_inj in H.
    rewrite H1, H; apply more_branches_refl.
    rewrite H; constructor. eauto.
+ elim (merge_inv_Branching_None_Some _ _ _ _ _ Hinj); intros.
  - destroy H. rewrite H0. constructor.
  - inversion_clear H; destroy H0.
    destroy H. apply inject_inj in H.
    rewrite H1, H; apply more_branches_refl.
    rewrite H; constructor. eauto.
+ elim (merge_inv_Branching _ _ _ _ _ Hinj); intros;
  rename x into Bl'; inversion_clear H;
  rename x into Bl''; inversion_clear H0;
  rename x into Br'; inversion_clear H;
  rename x into Br''; inversion_clear H0;
  destroy H1; rewrite H.
  eelim H4; eauto; eelim H1; eauto; intros. destroy H6; destroy H8.
  opt_elim Bl' p0; opt_elim Bl'' p0; opt_elim Br' p0; opt_elim Br'' p0;
  try constructor.
  all: clear H1 H2 H3 H4; intros.
  1,2,3,4: eelim H8; eauto; clear H8; intros H8' H8; destroy H8; rewrite <- H8'.
  5,6,7,8: elim H10; auto; clear H10; intros BL' H10;
           elim H10; clear H10; intros H10 H10'; apply inject_inj in H10'.
  9,10,11,12: elim H7; auto; clear H7; intros BL'' H7;
              elim H7; clear H7; intros H7 H7'; apply inject_inj in H7'.
  1,5,9: eelim H6; eauto; clear H6; intros H6' H6; destroy H6; rewrite <- H6'.
  4,7,10: elim H9; auto; clear H9; intros BR' H9;
             elim H9; clear H9; intros H9 H9'; apply inject_inj in H9'.
  7,8,9,10: elim H5; auto; clear H5; intros BR'' H5;
            elim H5; clear H5; intros H5 H5'; apply inject_inj in H5'.
  all: try rewrite H10'; try rewrite H70; try rewrite H9'; try rewrite H5'.
  all: try constructor; eauto.
  1,5,6: rewrite H4 in H10; inversion H10; constructor; eauto; apply more_branches_refl.
  1,3: rewrite H2 in H9; inversion H9; constructor; eauto; apply more_branches_refl.
  1: rewrite H4 in H10; inversion H10; rewrite H2 in H9; inversion H9;
     constructor; eauto; apply more_branches_refl.
  1,2: rewrite H3 in H7; inversion H7.
+ elim (merge_inv_Cond _ _ _ _ _ Hinj); intros.
  rename x into Be'; inversion_clear H.
  rename x into Be''; inversion_clear H0.
  rename x into Bt; inversion_clear H.
  rename x into Bt''; destroy H0.
  rewrite H; constructor; eauto.
+ elim (merge_inv_Call _ _ _ Hinj); intros.
  rewrite H; constructor; eauto.
Qed.

Lemma merge_is_upper_bound' : forall B1 B2 B, B1 [\/] B2 = inject B -> B [>] B2.
Proof.
intros.
apply merge_is_upper_bound with B1.
rewrite merge_comm; auto.
Qed.

Local Ltac mb_trans B B' := apply more_branches_trans with B;
  [apply merge_is_upper_bound with B' | idtac]; auto.

Local Ltac mb_trans' B B' := apply more_branches_trans with B;
  [apply merge_is_upper_bound' with B' | idtac]; auto.

(** Pullbacks *)
Lemma more_branches_merge_extend : forall B1 B2 B1' B2' B,
  B1 [>] B1' -> B2 [>] B2' -> B1 [\/] B2 = inject B ->
  exists B', B1' [\/] B2' = inject B' /\ B [>] B'.
Proof.
intros. revert B1 B2 B1' B2' H H0 H1.
BInduction B; intros.
+ apply merge_inv_End in H1; destroy H1.
  rewrite H2, H1 in *.
  inversion H; inversion H0.
  exists (End _); split; auto.
  apply more_branches_refl.
+ apply merge_inv_Send in H1; destroy H1.
  fold (inject B) in H1.
  rewrite H2, H3 in *; clear H2 H3 B1 B2.
  inversion H; inversion H0.
  elim (IHB _ _ _ _ H7 H13 H1); intros. destroy H14.
  exists (p!e@!a;x1); split.
  - unfold merge; simpl. repeat rewrite eqb_refl; simpl.
    unfold merge in H15; rewrite H15.
    rewrite inject_match; auto.
  - constructor; auto.
+ apply merge_inv_Recv in H1; destroy H1.
  fold (inject B) in H1.
  rewrite H2, H3 in *; clear H2 H3 B1 B2.
  inversion H; inversion H0.
  elim (IHB _ _ _ _ H7 H13 H1); intros. destroy H14.
  exists (p ? v @? a;x3); split.
  - unfold merge; simpl. repeat rewrite eqb_refl; simpl.
    unfold merge in H15; rewrite H15.
    rewrite inject_match; auto.
  - constructor; auto.
+ apply merge_inv_Sel in H1; destroy H1.
  fold (inject B) in H1.
  rewrite H2, H3 in *; clear H2 H3 B1 B2.
  inversion H; inversion H0.
  elim (IHB _ _ _ _ H7 H13 H1); intros. destroy H14.
  exists (p(+)l@+a;x1); split.
  - unfold merge; simpl. repeat rewrite eqb_refl; simpl.
    unfold merge in H15; rewrite H15.
    rewrite inject_match; auto.
  - constructor; auto.
+ apply merge_inv_Branching_None_None in H1; destroy H1.
  rewrite H1, H2 in *; clear H1 H2.
  inversion H; inversion H0.
  exists (p & None // None); split.
  - unfold merge; simpl. rewrite eqb_refl; auto.
  - constructor.
+ apply merge_inv_Branching_Some_None in H1.
  fold (inject B) in H1. inversion_clear H1. 2: inversion_clear H2.
  - destroy H2. apply inject_inj in H2.
    rewrite <- H2, H1, H3 in *; clear H1 H2 H3 x.
    inversion H. inversion H0.
    * exists (p & None // None); split.
      unfold merge; simpl. rewrite eqb_refl; auto.
      constructor.
    * exists (p & Some (a,Bl') // None); split.
      unfold merge; simpl. rewrite eqb_refl, inject_match; auto.
      constructor; auto.
  - destroy H1. destroy H2. apply inject_inj in H2.
    rewrite <- H2, H1, H3 in *; clear H1 H2 H3 x.
    inversion H0. inversion H.
    * exists (p & None // None); split.
      unfold merge; simpl. rewrite eqb_refl; auto.
      constructor.
    * exists (p & Some (a,Bl') // None); split.
      unfold merge; simpl. rewrite eqb_refl, inject_match; auto.
      constructor; auto.
  - destroy H1.
    rewrite H2, H3 in *; clear H2 H3 B1 B2.
    rename x into B1, x0 into B2.
    inversion H; inversion H0.
    * exists (p & None // None); split.
      unfold merge; simpl. rewrite eqb_refl; auto.
      constructor.
    * exists (p & Some (a,Bl') // None); split.
      unfold merge; simpl. rewrite eqb_refl, inject_match; auto.
      constructor. apply more_branches_trans with B2; auto.
      eapply merge_is_upper_bound'; eauto.
    * exists (p & Some (a,Bl') // None); split.
      unfold merge; simpl. rewrite eqb_refl, inject_match; auto.
      constructor. apply more_branches_trans with B1; auto.
      eapply merge_is_upper_bound; eauto.
    * elim (IHB _ _ _ _ H7 H13); auto.
      intros BB H'; destroy H'.
      exists (p & Some (a,BB) // None); split.
      unfold merge; simpl. repeat rewrite eqb_refl.
      unfold merge in H14. rewrite H14, inject_match; auto.
      constructor; auto.
+ apply merge_inv_Branching_None_Some in H1.
  fold (inject B) in H1. inversion_clear H1. 2: inversion_clear H2.
  - destroy H2. apply inject_inj in H2.
    rewrite <- H2, H1, H3 in *; clear H1 H2 H3 x.
    inversion H. inversion H0.
    * exists (p & None // None); split.
      unfold merge; simpl. rewrite eqb_refl; auto.
      constructor.
    * exists (p & None // Some (a,Br')); split.
      unfold merge; simpl. rewrite eqb_refl, inject_match; auto.
      constructor; auto.
  - destroy H1. destroy H2. apply inject_inj in H2.
    rewrite <- H2, H1, H3 in *; clear H1 H2 H3 x.
    inversion H0. inversion H.
    * exists (p & None // None); split.
      unfold merge; simpl. rewrite eqb_refl; auto.
      constructor.
    * exists (p & None // Some (a,Br')); split.
      unfold merge; simpl. rewrite eqb_refl, inject_match; auto.
      constructor; auto.
  - destroy H1.
    rewrite H2, H3 in *; clear H2 H3 B1 B2.
    rename x into B1, x0 into B2.
    inversion H; inversion H0.
    * exists (p & None // None); split.
      unfold merge; simpl. rewrite eqb_refl; auto.
      constructor.
    * exists (p & None // Some (a,Br')); split.
      unfold merge; simpl. rewrite eqb_refl, inject_match; auto.
      constructor. apply more_branches_trans with B2; auto.
      eapply merge_is_upper_bound'; eauto.
    * exists (p & None // Some (a,Br')); split.
      unfold merge; simpl. rewrite eqb_refl, inject_match; auto.
      constructor. apply more_branches_trans with B1; auto.
      eapply merge_is_upper_bound; eauto.
    * elim (IHB _ _ _ _ H7 H13); auto.
      intros BB H'; destroy H'.
      exists (p & None // Some (a,BB)); split.
      unfold merge; simpl. repeat rewrite eqb_refl.
      unfold merge in H14. rewrite H14, inject_match; auto.
      constructor; auto.
+ apply merge_inv_Branching in H1; destroy H1.
  fold (inject B1) in *; fold (inject B2) in *.
  rewrite H2, H3 in *; clear H2 H3 B0 B3 H4 H5.
  eelim H1; eauto; intros. destroy H3.
  eelim H6; eauto; intros. destroy H7.
  clear H1 H6.
  induction x.
  1: induction a0; clear H5.
  2: elim H5; clear H5; auto; intros B HB;
     destroy HB; apply inject_inj in HB;
     rewrite H1, HB in *; clear B1 HB x0 H1.
  induction x0.
  1: induction a1; clear H8;
     eelim H7; eauto; clear H7; intros; destroy H5;
     rewrite H1, H6 in *; clear a1 a0 H1 H6; rename H5 into H6.
  2: elim H8; clear H8; auto; intros B HB;
     destroy HB; apply inject_inj in HB;
     rewrite H1, HB in *; clear B1 HB a0 b H1.
  all: induction x1.
  1,3,5: induction a0; clear H2.
  4,5,6: elim H2; auto; clear H2 H3; intros B' HB';
         destroy HB'; apply inject_inj in HB';
         rewrite H1, HB' in *; clear B2 HB' x2 H1.
  1,2,3: induction x2.
  1,3,5: induction a1; eelim H3; auto; clear H3; intros; destroy H2;
         rewrite H1, H3 in *; clear a1 a0 H1 H3.
  4,5,6: elim H4; clear H4; auto; intros B' HB';
       destroy HB'; apply inject_inj in HB';
       rewrite H1, HB' in *; clear B2 HB' a0 H1.
  all: inversion H0; inversion H.
  1,17,25,33,41,45,49,57,61: exists (p & None // None); split;
    [ unfold merge; simpl; rewrite eqb_refl; auto
    | constructor].
  1,4,16,19,23,24,30,37,40,44,51,53: exists (p & None // Some (a', Br')); split;
    [ unfold merge; simpl; rewrite eqb_refl, inject_match; auto
    | constructor; auto ].
  1: mb_trans b1 b2.
  1: mb_trans' b2 b1.
  1,3: mb_trans b b0.
  1,2: mb_trans' b0 b.
  1,6,14,20,24,26,30,32,34,36,40,42: exists (p & Some (a,Bl') // None)%SP; split;
    [ unfold merge; simpl; rewrite eqb_refl, inject_match; auto
    | constructor; auto ].
  1,3,5: mb_trans b b0.
  1,2,3: mb_trans' b0 b.
  1,3,5,8,12,14,17,18,20,21,24,25,26,28,30,31: exists (p & Some (a,Bl') // Some (a',Br'))%SP; split;
    [ unfold merge; simpl; rewrite eqb_refl, inject_match, inject_match; auto
    | constructor; auto].
  1,3,9,11,13,15: mb_trans b b0.
  1,4: mb_trans b1 b2.
  1,4: mb_trans' b2 b1.
  1,2,3,4,5,6: mb_trans' b0 b.
  3,4,6,7,12,13,14,15: elim (IHB1 b b0 Bl'0 Bl'); auto;
    intros BL HL; inversion_clear HL as (HL',HL''); unfold merge in HL'.
  1,2,6,11,12,13,14,15: eelim IHB2 with (B1':=Br'0) (B2':=Br'); eauto;
    intros BR HR; inversion_clear HR as (HR',HR''); unfold merge in HR'.
  9,12,14: exists (p & Some (a,BL) // None); split;
    [ unfold merge; simpl;
      repeat rewrite eqb_refl; rewrite HL'; repeat rewrite inject_match; auto
    | idtac]; constructor; auto.
  1,5,7: exists (p & None // Some (a',BR)); split;
    [ unfold merge; simpl;
      repeat rewrite eqb_refl; rewrite HR'; repeat rewrite inject_match; auto
    | idtac]; constructor; auto.
  1,3,4,5: exists (p & Some (a,Bl') // Some (a',BR)); split;
    [ unfold merge; simpl;
      repeat rewrite eqb_refl; rewrite HR'; repeat rewrite inject_match; auto
    | idtac]; constructor; auto.
  4,5,6,7: exists (p & Some (a,BL) // Some (a',Br')); split;
    [ unfold merge; simpl;
      repeat rewrite eqb_refl; rewrite HL'; repeat rewrite inject_match; auto
    | idtac]; constructor; auto.
  3: exists (p & Some (a,BL) // Some (a',BR)); split;
    [ unfold merge; simpl;
      repeat rewrite eqb_refl; rewrite HL', HR'; repeat rewrite inject_match; auto
    | idtac]; constructor; auto.
  * mb_trans b b0.
  * mb_trans' b0 b.
  * mb_trans b1 b2.
  * mb_trans' b2 b1.
+ apply merge_inv_Cond in H1; destroy H1.
  fold (inject B2) in H1; fold (inject B1) in H4.
  rewrite H2, H3 in *; clear H2 H3 B0 B3.
  inversion H; inversion H0.
  elim (IHB1 _ _ _ _ H7 H13 H4); intros. destroy H15.
  elim (IHB2 _ _ _ _ H8 H14 H1); intros. destroy H17.
  exists (If b Then x3 Else x4); repeat split.
  - unfold merge; simpl. rewrite eqb_refl; simpl.
    unfold merge in H16, H18; rewrite H16, H18.
    case_eq (inject x3); case_eq (inject x4); auto; intros.
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

(** Merge is an lub *)
Lemma more_branches_has_lub : forall B B1 B2, B [>] B1 -> B [>] B2 ->
  exists B', B1 [\/] B2 = inject B' /\ B [>] B'.
Proof.
intros.
elim (more_branches_merge_extend B B B1 B2 B); eauto.
apply merge_idempotent.
Qed.

Lemma merge_is_lub : forall B B1 B2, B [>] B1 -> B [>] B2 ->
  forall B', B1 [\/] B2 = inject B' -> B [>] B'.
Proof.
intros.
elim (more_branches_has_lub B B1 B2); auto.
intros b Hb; destroy Hb.
rewrite H2 in H1; apply inject_inj in H1.
rewrite <- H1; auto.
Qed.

(** The image of [merge] is isomorphic to [option Behaviour]. *)
Lemma merge_undefined_or_behaviour : forall B1 B2,
  { B1 [\/] B2 = XUndefined } + { exists B, B1 [\/] B2 = inject B }.
Proof.
unfold merge.
induction B1 using Behaviour_rec'; induction B2 using Behaviour_rec'; simpl; auto.
all: repeat (elim eqb; auto); simpl.
all: repeat rewrite inject_match; auto.
2,3,4,10,15: elim (IHB1 B2); intro HB2; try rewrite HB2; auto.
13: elim (IHB1 B2_1); intro HB1; try rewrite HB1; auto.
16: elim (IHB1 B2_2); intro HB1; try rewrite HB1; auto.
18: elim (IHB1_1 B2); intro HB2; try rewrite HB2; auto.
19: elim (IHB1_2 B2); intro HB2; try rewrite HB2; auto.
20,21,22: elim (IHB1_1 B2_1); intro HB1; try rewrite HB1; auto.
20,21,22: elim (IHB1_2 B2_2); intro HB2; try rewrite HB2; auto.
20,22,23,24: left; case (inject B1_1 [[\/]] inject B2_1); auto.
all: right.
all: destroy HB1; destroy HB2;
     try rewrite HB1; try rewrite HB2; repeat rewrite inject_match.
+ exists (End _); auto.
+ exists (p ! e @! a; x); auto.
+ exists (p ? v @? a; x); auto.
+ exists (p (+) l @+ a; x); auto.
+ exists (p & Some (a,x) // None); auto.
+ exists (p & None // Some (a,x)); auto.
+ exists (p & None // None); auto.
+ exists (p & Some (a,B2) // None); auto.
+ exists (p & None // Some (a,B2)); auto.
+ exists (p & Some (a,B2_1) // Some (a',B2_2)); auto.
+ exists (p & Some (a,B1) // None); auto.
+ exists (p & Some (a,B1) // Some (a0,B2)); auto.
+ exists (p & Some (a,x) // Some (a',B2_2)); auto.
+ exists (p & None // Some (a,B1)); auto.
+ exists (p & Some (a0,B2) // Some (a,B1)); auto.
+ exists (p & Some (a0,B2_1) // Some (a,x)); auto.
+ exists (p & Some (a,B1_1) // Some (a',B1_2)); auto.
+ exists (p & Some (a,x) // Some (a',B1_2)); auto.
+ exists (p & Some (a,B1_1) // Some (a',x)); auto.
+ exists (p & Some (a,x) // Some (a',x0)); auto.
+ exists (If b Then x Else x0); case x, x0; intros;
  try opt_elim o p; try opt_elim o0 p; try opt_elim o1 p; try opt_elim o2 p;
  simpl; auto.
+ exists (Call _ X); auto.
Qed.

Lemma merge_not_undefined : forall B B', B [\/] B' <> XUndefined ->
  exists B'', B [\/] B' = inject B''.
Proof.
intros.
elim (merge_undefined_or_behaviour B B'); auto.
tauto.
Qed.

(** Using these results we can prove associativity of merge. *)
Lemma merge_assoc : forall (B B' B'':Behaviour Sig),
  inject B [[\/]] (inject B' [[\/]] inject B'')
  = (inject B [[\/]] inject B') [[\/]] inject B''.
Proof.
intros.
elim (XUndefined_dec _ ((inject B [[\/]] inject B') [[\/]] inject B'')); intro H1.
all: elim (XUndefined_dec _ (inject B [[\/]] (inject B' [[\/]] inject B''))); intro H2.
+ rewrite H1, H2; auto.
+ elim (merge_undefined_or_behaviour B' B''); intro H3.
  2: inversion H3 as (b,Hb); clear H3; rename Hb into H3.
  all: unfold merge in H3; rewrite H3 in H2.
  1: elim H2; rewrite Xmerge_comm; auto.
  apply merge_not_undefined in H2.
  inversion H2 as (b',Hb'); clear H2; rename Hb' into H2.
  unfold merge in H2.
  pose (merge_is_upper_bound _ _ _ H3) as Hb1.
  pose (merge_is_upper_bound' _ _ _ H3) as Hb2.
  pose (merge_is_upper_bound _ _ _ H2) as Hb'1.
  pose (merge_is_upper_bound' _ _ _ H2) as Hb'2.
  clearbody Hb1 Hb2 Hb'1 Hb'2.
  pose (more_branches_trans _ _ _ _ Hb'2 Hb1) as Hb'3.
  pose (more_branches_trans _ _ _ _ Hb'2 Hb2) as Hb'4.
  clearbody Hb'3 Hb'4; clear dependent b.
  pose (more_branches_has_lub _ _ _ Hb'1 Hb'3) as H2.
  clearbody H2; destroy H2. rename x into B1.
  pose (more_branches_has_lub _ _ _ H2 Hb'4) as H3.
  clearbody H3; destroy H3. rename x into B2.
  clear H3 H2 Hb'1 Hb'3 Hb'4.
  unfold merge in H0, H; rewrite H, H0 in H1.
  apply inject_not_undefined in H1; tauto.
+ elim (merge_undefined_or_behaviour B B'); intro H3.
  2: inversion H3 as (b,Hb); clear H3; rename Hb into H3.
  all: unfold merge in H3; rewrite H3 in H1.
  1: elim H1; auto.
  apply merge_not_undefined in H1.
  inversion H1 as (b',Hb'); clear H1; rename Hb' into H1.
  unfold merge in H1.
  pose (merge_is_upper_bound _ _ _ H3) as Hb1.
  pose (merge_is_upper_bound' _ _ _ H3) as Hb2.
  pose (merge_is_upper_bound _ _ _ H1) as Hb'1.
  pose (merge_is_upper_bound' _ _ _ H1) as Hb'2.
  clearbody Hb1 Hb2 Hb'1 Hb'2.
  pose (more_branches_trans _ _ _ _ Hb'1 Hb1) as Hb'3.
  pose (more_branches_trans _ _ _ _ Hb'1 Hb2) as Hb'4.
  clearbody Hb'3 Hb'4; clear dependent b.
  pose (more_branches_has_lub _ _ _ Hb'4 Hb'2) as H1.
  clearbody H1; destroy H1. rename x into B1.
  pose (more_branches_has_lub _ _ _ Hb'3 H1) as H3.
  clearbody H3; destroy H3. rename x into B2.
  clear H1 H3 Hb'2 Hb'3 Hb'4.
  unfold merge in H0, H; rewrite H, H0 in H2.
  apply inject_not_undefined in H2; tauto.
+ elim (merge_undefined_or_behaviour B' B''); intro H3.
  2: pose H2 as H2'; clearbody H2'.
  2: inversion H3 as (b,Hb); clear H3; rename Hb into H3.
  all: unfold merge in H3; rewrite H3 in H2.
  1: elim H2; rewrite Xmerge_comm; auto.
  apply merge_not_undefined in H2.
  inversion H2 as (b',Hb'); clear H2; rename Hb' into H2.
  pose (merge_is_upper_bound _ _ _ H3) as Hb1.
  pose (merge_is_upper_bound' _ _ _ H3) as Hb2.
  pose (merge_is_upper_bound _ _ _ H2) as Hb'1.
  pose (merge_is_upper_bound' _ _ _ H2) as Hb'2.
  clearbody Hb1 Hb2 Hb'1 Hb'2.
  pose (more_branches_trans _ _ _ _ Hb'2 Hb1) as Hb'3.
  pose (more_branches_trans _ _ _ _ Hb'2 Hb2) as Hb'4.
  clearbody Hb'3 Hb'4; clear dependent b.
  pose (more_branches_has_lub _ _ _ Hb'1 Hb'3) as H2.
  clearbody H2; destroy H2. rename x into B1.
  pose (more_branches_has_lub _ _ _ H2 Hb'4) as H3.
  clearbody H3; destroy H3. rename x into B2.
  unfold merge in H0, H; rewrite H, H0.
  rename H1 into H1'.
  elim (merge_undefined_or_behaviour B B'); intro H1.
  2: inversion H1 as (b,Hb); clear H1; rename Hb into H1.
  all: unfold merge in H1; rewrite H1 in H1'.
  1: elim H1'; auto.
  apply merge_not_undefined in H1'.
  inversion H1' as (b'',Hb''); clear H1'; rename Hb'' into H4.
  unfold merge in H4.
  pose (merge_is_upper_bound _ _ _ H1) as Hb1.
  pose (merge_is_upper_bound' _ _ _ H1) as Hb2.
  pose (merge_is_upper_bound _ _ _ H4) as Hb''1.
  pose (merge_is_upper_bound' _ _ _ H4) as Hb''2.
  clearbody Hb1 Hb2 Hb''1 Hb''2.
  pose (more_branches_trans _ _ _ _ Hb''1 Hb1) as Hb''3.
  pose (more_branches_trans _ _ _ _ Hb''1 Hb2) as Hb''4.
  clearbody Hb''3 Hb''4; clear dependent b.
  pose (more_branches_has_lub _ _ _ Hb''4 Hb''2) as H1.
  clearbody H1; destroy H1. rename x into B3.
  pose (more_branches_has_lub _ _ _ Hb''3 H1) as H5.
  clearbody H5; destroy H5. rename x into B4.
  unfold merge in H4, H6; rewrite H4, H6.
  replace B2 with B4; auto.
  apply more_branches_antisym.
  - eapply merge_is_lub; eauto.
    eapply merge_is_lub; eauto.
    2,3: apply more_branches_trans with B3.
    2,4,5: eapply merge_is_upper_bound'; eauto.
    all: eapply merge_is_upper_bound; eauto.
  - eapply merge_is_lub; eauto.
    2: eapply merge_is_lub; eauto.
    1,2: apply more_branches_trans with B1; auto.
    1,2,3: eapply merge_is_upper_bound; eauto.
    all: eapply merge_is_upper_bound'; eauto.
Qed.

End SP_Merge.

Notation "B [\/] B'" := (merge _ B B') (at level 60).
Notation "B [[\/]] B'" := (Xmerge _ B B') (at level 60).
