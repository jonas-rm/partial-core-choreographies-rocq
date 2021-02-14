Require Export SP.

Module SP_Merge (P X V E B R:DecType) (Ev:Eval E X V V) (BEv:Eval B X V Bool).

Module Export SPM := SPBase P X V E B R Ev BEv.

Ltac Peq := unfold Pid_dec; rewrite Pdec.eqb_refl; simpl.
Ltac Eeq := unfold Expr_dec; rewrite Edec.eqb_refl; simpl.
Ltac Beq := unfold BExpr_dec; rewrite Bdec.eqb_refl; simpl.
Ltac Veq := unfold Var_dec; rewrite Xdec.eqb_refl; simpl.
Ltac Xeq := unfold RecVar_dec; rewrite Rdec.eqb_refl; simpl.

Ltac Pneq H := rewrite <- Pdec.eqb_neq in H; rewrite H.

Section Merge.

Inductive XBehaviour : Type :=
| XEnd : XBehaviour
| XSend : Pid -> Expr -> XBehaviour -> XBehaviour
| XRecv : Pid -> Var -> XBehaviour -> XBehaviour
| XSel : Pid -> Label -> XBehaviour -> XBehaviour
| XBranching : Pid -> option XBehaviour -> option XBehaviour -> XBehaviour
| XCond : BExpr -> XBehaviour -> XBehaviour -> XBehaviour
| XCall : RecVar -> XBehaviour
| XUndefined : XBehaviour
.

Lemma XUndefined_dec : forall B, {B = XUndefined} + {B <> XUndefined}.
Proof. induction B; auto; right; discriminate. Qed.

Lemma Xmatch_elim : forall B T (X1 X2:T), B <> XUndefined ->
  match B with XUndefined => X1 | _ => X2 end = X2.
Proof. induction B; try case o, o0; auto. intros; elim H; auto. Qed.

(* Sigh. *)

Fixpoint Xdepth (B:XBehaviour) : nat :=
match B with
 | XSend p e B' => 1 + Xdepth B'
 | XRecv p x B' => 1 + Xdepth B'
 | XSel p l B' => 1 + Xdepth B'
 | XBranching p mB mB' => 1
                          + (match mB with None => 0 | Some B => Xdepth B end)
                          + (match mB' with None => 0 | Some B => Xdepth B end)
 | XCond b B1 B2 => 1 + Nat.max (Xdepth B1) (Xdepth B2)
 | XCall X => 1
 | XEnd => 1
 | XUndefined => 0
end.

Theorem XBehaviour_ind' :
  forall P:XBehaviour -> Prop,
    P XEnd ->
    (forall p e B, P B -> P (XSend p e B)) ->
    (forall p v B, P B -> P (XRecv p v B)) ->
    (forall p l B, P B -> P (XSel p l B)) ->
    (forall p mB mB', (forall B, mB = Some B -> P B) ->
                      (forall B, mB' = Some B -> P B) ->
                      P (XBranching p mB mB')) ->
    (forall b B1 B2, P B1 -> P B2 -> P (XCond b B1 B2)) ->
    (forall X, P (XCall X)) ->
    P XUndefined ->
    forall B, P B.
Proof.
intros; revert B.
assert (forall d B, Xdepth B <= d -> P B).
2: eauto.
induction d; intros; case_eq B; intros; auto; rewrite H8 in H7; try (exfalso; inversion H7; fail); auto with arith.
+ clear H H0 H1 H2 H4 H5 H6 H8 B.
  apply H3.
  1,2: intros; apply IHd;
    rewrite H in H7; simpl in H7; apply le_S_n in H7;
    etransitivity; [idtac | apply H7]; auto with arith.
+ apply H4; apply IHd; apply le_S_n in H7.
  - etransitivity. eapply Nat.le_max_l. eauto.
  - etransitivity. eapply Nat.le_max_r. eauto.
Qed.

Theorem XBehaviour_rec' :
  forall P:XBehaviour -> Type,
    P XEnd ->
    (forall p e B, P B -> P (XSend p e B)) ->
    (forall p v B, P B -> P (XRecv p v B)) ->
    (forall p l B, P B -> P (XSel p l B)) ->
    (forall p mB mB', (forall B, mB = Some B -> P B) ->
                      (forall B, mB' = Some B -> P B) ->
                      P (XBranching p mB mB')) ->
    (forall b B1 B2, P B1 -> P B2 -> P (XCond b B1 B2)) ->
    (forall X, P (XCall X)) ->
    P XUndefined ->
    forall B, P B.
Proof.
intros; revert B.
assert (forall d B, Xdepth B <= d -> P B).
2: eauto.
induction d; intros; case_eq B; intros; auto; rewrite H0 in H; try (exfalso; inversion H; fail); auto with arith.
+ apply X3.
  1,2: intros; apply IHd;
    rewrite H1 in H; simpl in H; apply le_S_n in H;
    etransitivity; [idtac | apply H]; auto with arith.
+ apply X4; apply IHd; apply le_S_n in H.
  - etransitivity. eapply Nat.le_max_l. eauto.
  - etransitivity. eapply Nat.le_max_r. eauto.
Qed.

Fixpoint inject (B:Behaviour) : XBehaviour :=
match B with
| End                    => XEnd
| p ! e; B               => XSend p e (inject B)
| p ? v; B               => XRecv p v (inject B)
| p (+) l; B             => XSel p l (inject B)
| p & None // None       => XBranching p None None
| p & Some Bl // None    => XBranching p (Some (inject Bl)) None
| p & None // Some Br    => XBranching p None (Some (inject Br))
| p & Some Bl // Some Br => XBranching p (Some (inject Bl)) (Some (inject Br))
| If e Then B1 Else B2   => XCond e (inject B1) (inject B2)
| Call X                 => XCall X
end.

Lemma inject_not_undefined : forall B, inject B <> XUndefined.
Proof. induction B; try case o, o0; discriminate. Qed.

Lemma inject_elim : forall B, exists B', inject B = B' /\ B' <> XUndefined.
Proof.
intro; exists (inject B); split; auto.
apply inject_not_undefined.
Qed.

Lemma inject_match : forall B T (X1 X2:T),
  match inject B with XUndefined => X1 | _ => X2 end = X2.
Proof. induction B; try case o, o0; auto. Qed.

Lemma inject_inj : forall B B', inject B = inject B' -> B = B'.
Proof.
induction B using Behaviour_ind'; induction B' using Behaviour_ind';
  intros; auto; try inversion H;
  try (induction mB, mB'; inversion H1; fail);
  try (rewrite (IHB _ H3); auto).
+ induction mB, mB', mB0, mB'0; inversion H3; auto.
  rewrite H with a b0; auto. rewrite H0 with b b1; auto.
  rewrite H with a b; auto.
  rewrite H0 with b b0; auto.
+ rewrite (IHB1 _ H2), (IHB2 _ H3); auto.
+ inversion H1; auto.
Qed.

Fixpoint Xmerge (B1 B2:XBehaviour) : XBehaviour :=
match B1, B2 with
| XEnd,                   XEnd           => XEnd
| XSend p e B,            XSend p' e' B' =>
    if Pid_dec p p' && Expr_dec e e'
    then match Xmerge B B' with XUndefined => XUndefined
                              | _          => XSend p e (Xmerge B B') end
    else XUndefined
| XRecv p v B,            XRecv p' v' B' =>
    if Pid_dec p p' && Var_dec v v'
    then match Xmerge B B' with XUndefined => XUndefined
                              | _          => XRecv p v (Xmerge B B') end
    else XUndefined
| XSel p l B,             XSel p' l' B' =>
    if Pid_dec p p' && eqb_label l l'
    then match Xmerge B B' with XUndefined => XUndefined
                              | _          => XSel p l (Xmerge B B') end
    else XUndefined
| XBranching p Bl Br,     XBranching p' Bl' Br' =>
    if Pid_dec p p'
    then let BL := match Bl with None   => Bl'
                               | Some B => match Bl' with None    => Bl
                                                        | Some B' => Some (Xmerge B B')
                                           end
                   end
      in let BR := match Br with None   => Br'
                               | Some B => match Br' with None    => Br
                                                        | Some B' => Some (Xmerge B B')
                                           end
                   end
      in match BL, BR with Some XUndefined, _ => XUndefined
                         | _, Some XUndefined => XUndefined
                         | _, _               => XBranching p BL BR
         end
    else XUndefined
| XCond e B1 B2,          XCond e' B1' B2'      =>
    if BExpr_dec e e'
    then match Xmerge B1 B1', Xmerge B2 B2' with XUndefined, _ => XUndefined
                                               | _, XUndefined => XUndefined
                                               | Bt, Be        => XCond e Bt Be end
    else XUndefined
| XCall X,                XCall X'              =>
    if RecVar_dec X X' then XCall X else XUndefined
| _,                         _                  => XUndefined
end.

Definition merge B1 B2 := Xmerge (inject B1) (inject B2).

Lemma merge_undefined_or_behaviour : forall B1 B2,
  { merge B1 B2 = XUndefined } + { exists B, merge B1 B2 = inject B }.
Proof.
unfold merge.
induction B1 using Behaviour_rec'; induction B2 using Behaviour_rec'; auto;
  try (case mB; case mB'; auto; fail); simpl.
+ right. exists End; auto.
+ elim Pid_dec; auto. elim Expr_dec; auto. simpl.
  elim (IHB1 B2); intro. rewrite a; auto. 
  right. inversion_clear b. rewrite H, inject_match.
  exists (p ! e; x); auto.
+ elim Pid_dec; auto. elim Var_dec; auto. simpl.
  elim (IHB1 B2); intro. rewrite a; auto.
  right. inversion_clear b. rewrite H, inject_match.
  exists (p ? v; x); auto.
+ elim Pid_dec; auto. elim eqb_label; auto. simpl.
  elim (IHB1 B2); intro. rewrite a; auto.
  right. inversion_clear b. rewrite H, inject_match.
  exists (p (+) l; x); auto.
+ case_eq mB; case_eq mB0; case_eq mB'; case_eq mB'0; simpl; intros;
  elim Pid_dec; auto; do 2 try rewrite inject_match;
  try (right; exists (p & Some b0 // Some b); auto; fail);
  try (right; exists (p & Some b // None); auto; fail);
  try (right; exists (p & None // Some b); auto; fail).
  - elim (X _ H2 b1); intros. rewrite a; auto.
    elim (X0 _ H0 b); intros.
    * left. inversion_clear b3. rewrite H3, inject_match, a; auto.
    * right. inversion_clear b3; inversion_clear b4.
      rewrite H3, inject_match, H4, inject_match.
      exists (p & Some x // Some x0); auto.
  - elim (X _ H2 b0); intros. rewrite a; auto.
    right. inversion_clear b2. rewrite H3, inject_match.
    exists (p & Some x // Some b); auto.
  - elim (X _ H2 b0); intros. rewrite a; auto.
    right. inversion_clear b2. rewrite H3, inject_match.
    exists (p & Some x // Some b); auto.
  - elim (X _ H2 b); intros. rewrite a; auto.
    right. inversion_clear b1. rewrite H3, inject_match.
    exists (p & Some x // None); auto.
  - elim (X0 _ H0 b); intros. rewrite a; auto.
    right. inversion_clear b2. rewrite H3, inject_match.
    exists (p & Some b1 // Some x); auto.
  - elim (X0 _ H0 b); intros. rewrite a; auto.
    right. inversion_clear b2. rewrite H3, inject_match.
    exists (p & Some b1 // Some x); auto.
  - elim (X0 _ H0 b); intros. rewrite a; auto.
    right. inversion_clear b1. rewrite H3, inject_match.
    exists (p & None // Some x); auto.
  - right; exists (p & None // None); auto.
+ elim BExpr_dec; auto.
  elim (IHB1_1 B2_1); intro. rewrite a; auto.
  elim (IHB1_2 B2_2); intro.
  - left. inversion_clear b1. rewrite H, a; case x; intros; try case o, o0; auto.
  - right. inversion_clear b1. inversion_clear b2.
    rewrite H, H0.
    exists (If b Then x Else x0); case x, x0; intros; try case o, o0; try case o1, o2; simpl; auto.
+ elim RecVar_dec; auto.
  right. exists (Call X); auto.
Qed.

Lemma merge_not_undefined : forall B B', merge B B' <> XUndefined ->
  exists B'', merge B B' = inject B''.
Proof.
intros.
elim (merge_undefined_or_behaviour B B'); auto.
tauto.
Qed.

Lemma merge_idempotent : forall B, merge B B = inject B.
Proof.
unfold merge.
BInduction B mB mB'; simpl; intros;
  try rewrite Pdec.eqb_refl;
  try rewrite Edec.eqb_refl;
  try rewrite Vdec.eqb_refl;
  try rewrite Xdec.eqb_refl;
  try rewrite label_eqb_refl;
  try rewrite Bdec.eqb_refl;
  try rewrite Rdec.eqb_refl;
  try rewrite IHB, inject_match;
  simpl; auto.
+ rewrite H, H0, inject_match, inject_match; auto.
+ rewrite H, inject_match; auto.
+ rewrite H0, inject_match; auto.
+ rewrite IHB1, IHB2.
  case B1, B2; intros; try case o, o0; try case o1, o2; auto.
Qed.

Lemma Xmerge_comm : forall B B', Xmerge B B' = Xmerge B' B.
Proof.
induction B using XBehaviour_ind'; induction B' using XBehaviour_ind'; simpl; auto;
  try (case_eq mB; case_eq mB'; intros; auto);
  try (case_eq mB0; case_eq mB'0; intros; auto); simpl;
  unfold Pid_dec, Expr_dec, Var_dec, BExpr_dec, RecVar_dec; simpl;
  try rewrite Pdec.eqb_sym;
  try rewrite Edec.eqb_sym;
  try rewrite Vdec.eqb_sym;
  try rewrite Xdec.eqb_sym;
  try rewrite label_eqb_sym;
  try rewrite Bdec.eqb_sym;
  try rewrite Rdec.eqb_sym; auto;
  try (case_eq (Pdec.eqb p0 p); intro Hp0p; simpl; auto; rewrite Pdec.eqb_eq in Hp0p; rewrite Hp0p);
  try (case_eq (Edec.eqb e0 e); intro He0e; simpl; auto; rewrite Edec.eqb_eq in He0e; rewrite He0e);
  try (case_eq (Xdec.eqb v0 v); intro Hv0v; simpl; auto; rewrite Xdec.eqb_eq in Hv0v; rewrite Hv0v);
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; auto; rewrite label_eqb_eq in Hl0l; rewrite Hl0l);
  try (case_eq (Bdec.eqb b0 b); intro Hb0b; simpl; auto; rewrite Bdec.eqb_eq in Hb0b; rewrite Hb0b);
  try (case_eq (Rdec.eqb X0 X); intro HX0X; simpl; auto; rewrite Rdec.eqb_eq in HX0X; rewrite HX0X);
  try rewrite IHB; try rewrite (H _ H4); try rewrite (H0 _ H3); auto.
rewrite IHB1, IHB2; auto.
Qed.

Lemma merge_comm : forall B B', merge B B' = merge B' B.
Proof. intros. apply Xmerge_comm. Qed.

(** Inversion lemmas about merge. *)
Lemma merge_inv_End : forall B B', merge B B' = XEnd -> B = End /\ B' = End.
Proof.
unfold merge.
intros B B' HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (case o; case o0); try (case o1; case o2);
  simpl; auto; try (intros; inversion HBB'; fail);
  unfold Pid_dec, Expr_dec, Var_dec, BExpr_dec, RecVar_dec; simpl;
  try (case_eq (Pdec.eqb p0 p); intro Hp0p; simpl; try (rewrite Pdec.eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (Edec.eqb e0 e); intro He0e; simpl; try (rewrite Edec.eqb_eq in He0e; rewrite He0e));
  try (case_eq (Xdec.eqb v0 v); intro Hv0v; simpl; try (rewrite Xdec.eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (Bdec.eqb b2 b); intro Hb0b; simpl; try (rewrite Bdec.eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (Rdec.eqb r0 r); intro HX0X; simpl; try (rewrite Rdec.eqb_eq in HX0X; rewrite HX0X));
  intros; try inversion HBB';
  try (elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0).
4,7,13:
  elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
5,9: elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
5,8,9,10: elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b2))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b1)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b3) (inject b0))); intro HM.
  rewrite HM in H0; inversion H0.
  elim (XUndefined_dec (Xmerge (inject b4) (inject b1))); intro HM'.
  rewrite HM', Xmatch_elim in H0; auto; inversion H0.
  revert HM HM' H0.
  case (Xmerge (inject b3) (inject b0)); case (Xmerge (inject b4) (inject b1));
  intros; inversion H0.
Qed.

Lemma merge_inv_Send : forall B B' p e X, merge B B' = XSend p e X ->
  exists B1 B1', B = p ! e; B1 /\ B' = p ! e; B1' /\ merge B1 B1' = X.
Proof.
unfold merge.
intros B B' P E X HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (case o; case o0); try (case o1; case o2);
  simpl; auto; try (intros; inversion HBB'; fail);
  unfold Pid_dec, Expr_dec, Var_dec, BExpr_dec, RecVar_dec; simpl;
  try (case_eq (Pdec.eqb p0 p); intro Hp0p; simpl; try (rewrite Pdec.eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (Edec.eqb e0 e); intro He0e; simpl; try (rewrite Edec.eqb_eq in He0e; rewrite He0e));
  try (case_eq (Xdec.eqb v0 v); intro Hv0v; simpl; try (rewrite Xdec.eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (Bdec.eqb b2 b); intro Hb0b; simpl; try (rewrite Bdec.eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (Rdec.eqb r0 r); intro HX0X; simpl; try (rewrite Rdec.eqb_eq in HX0X; rewrite HX0X));
  intros; try inversion HBB';
  try (elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0).
1: exists b0, b; auto.
4,7,13:
  elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
5,9: elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
5,8,9,10: elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b2))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b1)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b3) (inject b0))); intro HM.
  rewrite HM in H0; inversion H0.
  elim (XUndefined_dec (Xmerge (inject b4) (inject b1))); intro HM'.
  rewrite HM', Xmatch_elim in H0; auto; inversion H0.
  revert HM HM' H0.
  case (Xmerge (inject b3) (inject b0)); case (Xmerge (inject b4) (inject b1));
  intros; inversion H0.
Qed.

Lemma merge_inv_Recv : forall B B' p v X, merge B B' = XRecv p v X ->
  exists B1 B1', B = p ? v; B1 /\ B' = p ? v; B1' /\ merge B1 B1' = X.
Proof.
unfold merge.
intros B B' P V X HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (case o; case o0); try (case o1; case o2);
  simpl; auto; try (intros; inversion HBB'; fail);
  unfold Pid_dec, Expr_dec, Var_dec, BExpr_dec, RecVar_dec; simpl;
  try (case_eq (Pdec.eqb p0 p); intro Hp0p; simpl; try (rewrite Pdec.eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (Edec.eqb e0 e); intro He0e; simpl; try (rewrite Edec.eqb_eq in He0e; rewrite He0e));
  try (case_eq (Xdec.eqb v0 v); intro Hv0v; simpl; try (rewrite Xdec.eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (Bdec.eqb b2 b); intro Hb0b; simpl; try (rewrite Bdec.eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (Rdec.eqb r0 r); intro HX0X; simpl; try (rewrite Rdec.eqb_eq in HX0X; rewrite HX0X));
  intros; try inversion HBB';
  try (elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0).
1: exists b0, b; auto.
4,7,13:
  elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
5,9: elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
5,8,9,10: elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b2))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b1)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b3) (inject b0))); intro HM.
  rewrite HM in H0; inversion H0.
  elim (XUndefined_dec (Xmerge (inject b4) (inject b1))); intro HM'.
  rewrite HM', Xmatch_elim in H0; auto; inversion H0.
  revert HM HM' H0.
  case (Xmerge (inject b3) (inject b0)); case (Xmerge (inject b4) (inject b1));
  intros; inversion H0.
Qed.

Lemma merge_inv_Sel : forall B B' p l X, merge B B' = XSel p l X ->
  exists B1 B1', B = p (+) l; B1 /\ B' = p (+) l; B1' /\ merge B1 B1' = X.
Proof.
unfold merge.
intros B B' P L X HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (case o; case o0); try (case o1; case o2);
  simpl; auto; try (intros; inversion HBB'; fail);
  unfold Pid_dec, Expr_dec, Var_dec, BExpr_dec, RecVar_dec; simpl;
  try (case_eq (Pdec.eqb p0 p); intro Hp0p; simpl; try (rewrite Pdec.eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (Edec.eqb e0 e); intro He0e; simpl; try (rewrite Edec.eqb_eq in He0e; rewrite He0e));
  try (case_eq (Xdec.eqb v0 v); intro Hv0v; simpl; try (rewrite Xdec.eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (Bdec.eqb b2 b); intro Hb0b; simpl; try (rewrite Bdec.eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (Rdec.eqb r0 r); intro HX0X; simpl; try (rewrite Rdec.eqb_eq in HX0X; rewrite HX0X));
  intros; try inversion HBB';
  try (elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0).
1: exists b0, b; auto.
4,7,13:
  elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
5,9: elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
5,8,9,10: elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b2))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b1)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b3) (inject b0))); intro HM.
  rewrite HM in H0; inversion H0.
  elim (XUndefined_dec (Xmerge (inject b4) (inject b1))); intro HM'.
  rewrite HM', Xmatch_elim in H0; auto; inversion H0.
  revert HM HM' H0.
  case (Xmerge (inject b3) (inject b0)); case (Xmerge (inject b4) (inject b1));
  intros; inversion H0.
Qed.

Lemma merge_inv_Branching : forall B B' p Bl Br, merge B B' = XBranching p Bl Br ->
  exists Bl' Bl'' Br' Br'', B = p & Bl' // Br' /\ B' = p & Bl'' // Br''
  /\ (Bl = None -> Bl' = None /\ Bl'' = None)
  /\ (Br = None -> Br' = None /\ Br'' = None)
  /\ (forall BL, Bl = Some BL ->
         (Bl' = None -> exists BL'', Bl'' = Some BL'' /\ BL = inject BL'')
      /\ (Bl'' = None -> exists BL', Bl' = Some BL' /\ BL = inject BL')
      /\ (forall BL' BL'', Bl' = Some BL' /\ Bl'' = Some BL'' -> merge BL' BL'' = BL))
  /\ (forall BR, Br = Some BR ->
         (Br' = None -> exists BR'', Br'' = Some BR'' /\ BR = inject BR'')
      /\ (Br'' = None -> exists BR', Br' = Some BR' /\ BR = inject BR')
      /\ (forall BR' BR'', Br' = Some BR' /\ Br'' = Some BR'' -> merge BR' BR'' = BR)).
Proof.
unfold merge.
intros B B' P Be Bt HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (case o; case o0); try (case o1; case o2);
  simpl; auto; try (intros; inversion HBB'; fail);
  unfold Pid_dec, Expr_dec, Var_dec, BExpr_dec, RecVar_dec; simpl;
  try (case_eq (Pdec.eqb p0 p); intro Hp0p; simpl; try (rewrite Pdec.eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (Edec.eqb e0 e); intro He0e; simpl; try (rewrite Edec.eqb_eq in He0e; rewrite He0e));
  try (case_eq (Xdec.eqb v0 v); intro Hv0v; simpl; try (rewrite Xdec.eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (Bdec.eqb b2 b); intro Hb0b; simpl; try (rewrite Bdec.eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (Rdec.eqb r0 r); intro HX0X; simpl; try (rewrite Rdec.eqb_eq in HX0X; rewrite HX0X));
  intros; try inversion HBB';
  try (elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0).
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b2))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some b0), (Some b2), (Some b), (Some b1);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    inversion H6; inversion H7; auto.
+ elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some b), (Some b1), None, (Some b0);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
  exists b0; auto.
+ elim (XUndefined_dec (inject b1)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, (Some b1), (Some b), (Some b0);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
  exists b1; auto.
+ elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0;
  exists None, (Some b0), None, (Some b);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto);
  [ exists b0 | exists b]; auto.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some b0), (Some b1), (Some b), None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
  exists b; auto.
+ elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some b), (Some b0), None, None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, (Some b0), (Some b), None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto);
  [ exists b0 | exists b]; auto.
+ elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, (Some b), None, None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
  exists b; auto.
+ elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some b0), None, (Some b), (Some b1);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
  exists b0; auto.
+ elim (XUndefined_dec (inject b)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some b), None, None, (Some b0);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto);
  [ exists b | exists b0]; auto.
+ elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, None, (Some b), (Some b0);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, None, None, (Some b);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
  exists b; auto.
+ elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some b0), None, (Some b), None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto);
  [ exists b0 | exists b]; auto.
+ elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some b), None, None, None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
  exists b; auto.
+ elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, None, (Some b), None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
  exists b; auto.
+ exists None, None, None, None;
  repeat (split; auto); try inversion H; intros; try inversion H4.
+ clear HBB'.
  elim (XUndefined_dec (Xmerge (inject b3) (inject b0))); intro HM.
  rewrite HM in H0; inversion H0.
  elim (XUndefined_dec (Xmerge (inject b4) (inject b1))); intro HM'.
  rewrite HM', Xmatch_elim in H0; auto; inversion H0.
  revert HM HM' H0.
  case (Xmerge (inject b3) (inject b0)); case (Xmerge (inject b4) (inject b1));
  intros; inversion H0.
Qed.

Lemma merge_inv_Branching_None_None : forall B B' p,
  merge B B' = XBranching p None None ->
  B = p & None // None /\ B' = p & None // None.
Proof.
intros.
elim (merge_inv_Branching _ _ _ _ _ H); intros.
destroy H0.
elim H3; auto; elim H4; auto.
intros. rewrite H1, H2, H6, H7, H8, H9; auto.
Qed.

Lemma merge_inv_Branching_Some_None : forall B B' p Bl,
  merge B B' = XBranching p (Some Bl) None ->
  (B = p & None // None /\ exists BL, B' = p & Some BL // None  /\ Bl = inject BL)
  \/ ((exists BL, B = p & Some BL // None /\ Bl = inject BL) /\ B' = p & None // None)
  \/ exists BL' BL'', B = p & Some BL' // None /\ B' = p & Some BL'' // None
    /\ merge BL' BL'' = Bl.
Proof.
intros.
elim (merge_inv_Branching _ _ _ _ _ H); intros.
destroy H0.
clear H3; elim H4; auto.
clear H0; elim (H5 Bl); auto.
intros. inversion_clear H3.
rewrite H1, H2, H6, H7; rewrite H1, H2, H6, H7 in H.
clear B B' x1 x2 H1 H2 H6 H7 H4 H5.
induction x. rename a into B. all: induction x0. 1,3: rename a into B'.
+ right. right. clear H0 H8. exists B, B'; auto.
+ left. split; auto. exists B'; split; auto.
  elim H0; intros; auto. inversion_clear H1. inversion H2; auto.
+ right. left. split; auto. exists B; split; auto.
  elim H8; intros; auto. inversion_clear H1. inversion H2; auto.
+ exfalso.
  unfold merge in H; simpl in H.
  unfold Pid_dec in H; rewrite Pdec.eqb_refl in H. inversion H.
Qed.

Lemma merge_inv_Branching_None_Some : forall B B' p Br,
  merge B B' = XBranching p None (Some Br) ->
  (B = p & None // None /\ exists BR, B' = p & None // Some BR  /\ Br = inject BR)
  \/ ((exists BR, B = p & None // Some BR /\ Br = inject BR) /\ B' = p & None // None)
  \/ exists BR' BR'', B = p & None // Some BR' /\ B' = p & None // Some BR''
    /\ merge BR' BR'' = Br.
Proof.
intros.
elim (merge_inv_Branching _ _ _ _ _ H); intros.
destroy H0.
clear H4; elim H3; auto.
clear H5; elim (H0 Br); auto.
intros. inversion_clear H5.
rewrite H1, H2, H6, H7; rewrite H1, H2, H6, H7 in H.
clear B B' x x0 H1 H2 H6 H7 H3.
induction x1. rename a into B. all: induction x2. 1,3: rename a into B'.
+ right. right. clear H0 H8. exists B, B'; auto.
+ left. split; auto. exists B'; split; auto.
  elim H4; intros; auto. inversion_clear H1. inversion H2; auto.
+ right. left. split; auto. exists B; split; auto.
  elim H8; intros; auto. inversion_clear H1. inversion H2; auto.
+ exfalso.
  unfold merge in H; simpl in H.
  unfold Pid_dec in H; rewrite Pdec.eqb_refl in H. inversion H.
Qed.

Lemma merge_inv_Cond : forall B B' b Be Bt, merge B B' = XCond b Be Bt ->
  exists Be' Be'' Bt' Bt'', B = Cond b Be' Bt' /\ B' = Cond b Be'' Bt''
    /\ merge Be' Be'' = Be /\ merge Bt' Bt'' = Bt.
Proof.
unfold merge.
intros B B' BB Be Bt HBB'; revert B B' BB Be Bt HBB'.
BDInduction B B' mB mB' mB0 mB'0;
  simpl; auto; try (intros; inversion HBB'; fail);
  unfold Pid_dec, Expr_dec, Var_dec, BExpr_dec, RecVar_dec; simpl;
  try (case_eq (Pdec.eqb p p0); intro Hp0p; simpl; try (rewrite Pdec.eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (Edec.eqb e e0); intro He0e; simpl; try (rewrite Edec.eqb_eq in He0e; rewrite He0e));
  try (case_eq (Xdec.eqb v v0); intro Hv0v; simpl; try (rewrite Xdec.eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l l0); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (Bdec.eqb b b0); intro Hb0b; simpl; try (rewrite Bdec.eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (Rdec.eqb X X0); intro HX0X; simpl; try (rewrite Rdec.eqb_eq in HX0X; rewrite HX0X));
  intros; try inversion HBB'.
1,2,3: elim (XUndefined_dec (Xmerge (inject B) (inject B'))); intro HM;
  [ rewrite HM in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
1: elim (XUndefined_dec (Xmerge (inject b2) (inject b0))); intro HT1;
  [ rewrite HT1 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
1,2: elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HT2;
  [ rewrite HT2 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
2,4,7,9,13: elim (XUndefined_dec (inject b0)); intro HT3;
  [ rewrite HT3 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
3,4,6,10,11,13,14,15: elim (XUndefined_dec (inject b)); intro HT4;
  [ rewrite HT4 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
7: elim (XUndefined_dec (inject b0)); intro HT5;
  [ rewrite HT5 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
11: elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HT6;
  [ rewrite HT6 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
12: elim (XUndefined_dec (inject b1)); intro HT7;
  [ rewrite HT7 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
12,14,15: elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HT8;
  [ rewrite HT8 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
15: elim (XUndefined_dec (Xmerge (inject b1) (inject b0))); intro HT8;
  [ rewrite HT8 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
15: elim (XUndefined_dec (inject b)); intro HT7;
  [ rewrite HT7 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
all: try inversion H8.
clear IHB'1 IHB'2 HBB' Hb0b b. rename b0 into b.
elim (XUndefined_dec (Xmerge (inject B1) (inject B'1))); intro HM.
rewrite HM in H0; inversion H0.
elim (XUndefined_dec (Xmerge (inject B2) (inject B'2))); intro HM'.
rewrite HM', Xmatch_elim in H0; auto; inversion H0.
exists B1, B'1, B2, B'2.
revert HM HM' H0.
case (Xmerge (inject B1) (inject B'1));
case (Xmerge (inject B2) (inject B'2)); intros;
inversion H0; auto.
Qed.

Lemma merge_inv_Call : forall B B' X, merge B B' = XCall X ->
  B = Call X /\ B' = Call X.
Proof.
unfold merge.
intros B B' X HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (case o; case o0); try (case o1; case o2);
  simpl; auto; try (intros; inversion HBB'; fail);
  unfold Pid_dec, Expr_dec, Var_dec, BExpr_dec, RecVar_dec; simpl;
  try (case_eq (Pdec.eqb p0 p); intro Hp0p; simpl; try (rewrite Pdec.eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (Edec.eqb e0 e); intro He0e; simpl; try (rewrite Edec.eqb_eq in He0e; rewrite He0e));
  try (case_eq (Xdec.eqb v0 v); intro Hv0v; simpl; try (rewrite Xdec.eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (Bdec.eqb b2 b); intro Hb0b; simpl; try (rewrite Bdec.eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (Rdec.eqb r0 r); intro HX0X; simpl; try (rewrite Rdec.eqb_eq in HX0X; rewrite HX0X));
  intros; try inversion HBB';
  try (elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0).
4,7,13:
  elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
5,9: elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
5,8,9,10: elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b2))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b1)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b3) (inject b0))); intro HM.
  rewrite HM in H0; inversion H0.
  elim (XUndefined_dec (Xmerge (inject b4) (inject b1))); intro HM'.
  rewrite HM', Xmatch_elim in H0; auto; inversion H0.
  revert HM HM' H0.
  case (Xmerge (inject b3) (inject b0)); case (Xmerge (inject b4) (inject b1));
  intros; inversion H0.
+ auto.
Qed.

(** Collapse an Undefined behaviour. *)
Fixpoint collapse (B:XBehaviour) : XBehaviour :=
let rec := fun B' => match collapse B' with XUndefined => XUndefined | _ => B end in
match B with
| XSend p e B' => rec B'
| XRecv p x B' => rec B'
| XSel p l B'  => rec B'
| XBranching p mB mB' => match mB, mB' with
                         | None,    None    => B
                         | Some Bl, None    => rec Bl
                         | None,    Some Br => rec Br
                         | Some Bl, Some Br => match collapse Bl, collapse Br with
                                               | XUndefined, _ => XUndefined
                                               | _, XUndefined => XUndefined
                                               | _, _          => B
                                               end
                         end
| XCond b B1 B2 => match collapse B1, collapse B2 with
                   | XUndefined, _ => XUndefined
                   | _, XUndefined => XUndefined
                   | _, _          => B
                   end
| _ => B
end.

(** Relationship with inject. *)
Lemma collapse_inject : forall B, collapse (inject B) = inject B.
Proof.
induction B using Behaviour_ind'; simpl; auto.
1,2,3: rewrite IHB, inject_match; auto.
2: rewrite IHB1, IHB2, inject_match, inject_match; auto.
case_eq mB; case_eq mB'; intros; simpl; auto.
+ rewrite (H _ H2), (H0 _ H1), inject_match, inject_match; auto.
+ rewrite (H _ H2), inject_match; auto.
+ rewrite (H0 _ H1), inject_match; auto.
Qed.

Lemma inject_exists : forall B,
  {B' | B = inject B'} -> collapse B <> XUndefined.
Proof.
intros. inversion_clear X.
rewrite H, collapse_inject; apply inject_not_undefined.
Qed.

Ltac XBeh_case B HB := elim (XUndefined_dec B); intro HB; try rewrite HB; auto;
  rewrite Xmatch_elim; auto.

(** Elimination lemmas. *)
Lemma collapse_char : forall B,
  {collapse B = XUndefined} + {collapse B = B}.
Proof.
induction B using XBehaviour_rec'; simpl; auto.
1,2,3: elim IHB; intro H; rewrite H; auto; XBeh_case B HB.
+ case_eq mB; case_eq mB'; intros; auto.
  - elim (X _ H0); intro HB; rewrite HB; auto; XBeh_case x0 Hx0.
    elim (X0 _ H); intro HB'; rewrite HB'; auto; XBeh_case x Hx.
  - elim (X _ H0); intro HB; rewrite HB; auto; XBeh_case x Hx.
  - elim (X0 _ H); intro HB'; rewrite HB'; auto; XBeh_case x Hx.
+ elim IHB1; intro H1; rewrite H1; auto; XBeh_case B1 HB1.
  elim IHB2; intro H2; rewrite H2; auto; XBeh_case B2 HB2.
Qed.

Lemma collapse_char' : forall B,
  ({B' | B = inject B'}) + {collapse B = XUndefined}.
Proof.
induction B using XBehaviour_rec'; simpl; auto.
+ left; exists End; auto.
+ elim IHB; intro H; try rewrite H; auto.
  left; elim H; clear H; intros B' HB'; rewrite HB'.
  exists (p ! e; B'); simpl; auto.
+ elim IHB; intro H; try rewrite H; auto.
  left; elim H; clear H; intros B' HB'; rewrite HB'.
  exists (p ? v; B'); simpl; auto.
+ elim IHB; intro H; try rewrite H; auto.
  left; elim H; clear H; intros B' HB'; rewrite HB'.
  exists (p (+) l; B'); simpl; auto.
+ case_eq mB; case_eq mB'; intros; auto.
  - elim (X _ H0); intro HB; try rewrite HB; auto.
    rewrite Xmatch_elim. 2: apply inject_exists; auto.
    elim (X0 _ H); intro HB'; try rewrite HB'; auto.
    rewrite Xmatch_elim. 2: apply inject_exists; auto.
    left; inversion_clear HB; inversion_clear HB'.
    exists (p & Some x1 // Some x2); rewrite H1, H2; auto.
  - elim (X _ H0); intro HB; try rewrite HB; auto.
    rewrite Xmatch_elim. 2: apply inject_exists; auto.
    left; inversion_clear HB.
    exists (p & Some x0 // None); rewrite H1; auto.
  - elim (X0 _ H); intro HB'; try rewrite HB'; auto.
    rewrite Xmatch_elim. 2: apply inject_exists; auto.
    left; inversion_clear HB'.
    exists (p & None // Some x0); rewrite H1; auto.
  - left. exists (p & None // None); auto.
+ elim IHB1; intro H1; try rewrite H1; auto.
  rewrite Xmatch_elim. 2: apply inject_exists; auto.
  elim IHB2; intro H2; try rewrite H2; auto.
  rewrite Xmatch_elim. 2: apply inject_exists; auto.
  left; inversion_clear H1; inversion_clear H2.
  exists (If b Then x Else x0); rewrite H, H0; auto.
+ left; exists (Call X); auto.
Qed.

Lemma collapse_char'' : forall B, collapse B = XUndefined ->
  forall B', B <> inject B'.
Proof.
induction B using XBehaviour_ind'; induction B' using Behaviour_ind'.
all: try inversion H.
all: try discriminate.
all: try (case mB, mB'; discriminate).
+ elim (XUndefined_dec (collapse B)); intro.
  intro; inversion H0; apply IHB with B'; auto.
  rewrite Xmatch_elim in H1; auto. inversion H1.
+ elim (XUndefined_dec (collapse B)); intro.
  intro; inversion H0; apply IHB with B'; auto.
  rewrite Xmatch_elim in H1; auto. inversion H1.
+ elim (XUndefined_dec (collapse B)); intro.
  intro; inversion H0; apply IHB with B'; auto.
  rewrite Xmatch_elim in H1; auto. inversion H1.
+ induction mB, mB', mB0, mB'0; try discriminate.
  all: simpl in H1.
  - elim (XUndefined_dec (collapse a)); intro.
    intro. inversion H4. apply H with a b; auto.
    rewrite Xmatch_elim in H1; auto.
    elim (XUndefined_dec (collapse x)); intro.
    intro. inversion H4. apply H0 with x b0; auto.
    rewrite Xmatch_elim in H1; auto. rewrite H1; discriminate.
  - elim (XUndefined_dec (collapse a)); intro.
    intro. inversion H4. apply H with a b; auto.
    rewrite Xmatch_elim in H1; auto. rewrite H1; discriminate.
  - elim (XUndefined_dec (collapse x)); intro.
    intro. inversion H4. apply H0 with x b; auto.
    rewrite Xmatch_elim in H1; auto. rewrite H1; discriminate.
+ elim (XUndefined_dec (collapse B1)); intro.
  intro; inversion H0; apply IHB1 with B'1; auto.
  rewrite Xmatch_elim in H1; auto.
  elim (XUndefined_dec (collapse B2)); intro.
  intro; inversion H0; apply IHB2 with B'2; auto.
  rewrite Xmatch_elim in H1; auto. inversion H1.
Qed.

Lemma collapse_exists : forall B, collapse B <> XUndefined ->
  exists B', B = inject B'.
Proof.
intros; elim (collapse_char' B); intros.
inversion_clear a; eauto.
elim H; auto.
Qed.

Lemma collapse_inv : forall B B', collapse B = inject B' -> B = inject B'.
Proof.
induction B using XBehaviour_ind'; auto; simpl; intros.
+ elim (collapse_char' B); intro.
  2: rewrite b in H; elim (inject_not_undefined B'); auto.
  inversion_clear a. rewrite H0 in H.
  rewrite Xmatch_elim, <- H0 in H; auto.
  rewrite collapse_inject; apply inject_not_undefined.
+ elim (collapse_char' B); intro.
  2: rewrite b in H; elim (inject_not_undefined B'); auto.
  inversion_clear a. rewrite H0 in H.
  rewrite Xmatch_elim, <- H0 in H; auto.
  rewrite collapse_inject; apply inject_not_undefined.
+ elim (collapse_char' B); intro.
  2: rewrite b in H; elim (inject_not_undefined B'); auto.
  inversion_clear a. rewrite H0 in H.
  rewrite Xmatch_elim, <- H0 in H; auto.
  rewrite collapse_inject; apply inject_not_undefined.
+ induction mB, mB'; auto.
  - elim (collapse_char' a); intro.
    2: rewrite b in H1; elim (inject_not_undefined B'); auto.
    inversion_clear a0. rewrite H2 in H1.
    rewrite Xmatch_elim, <- H2 in H1.
    elim (collapse_char' x); intro.
    2: rewrite b in H1; elim (inject_not_undefined B'); auto.
    inversion_clear a0. rewrite H3 in H1.
    rewrite Xmatch_elim, <- H3 in H1; auto.
    all: rewrite collapse_inject; apply inject_not_undefined.
  - elim (collapse_char' a); intro.
    2: rewrite b in H1; elim (inject_not_undefined B'); auto.
    inversion_clear a0. rewrite H2 in H1.
    rewrite Xmatch_elim, <- H2 in H1; auto.
    rewrite collapse_inject; apply inject_not_undefined.
  - elim (collapse_char' x); intro.
    2: rewrite b in H1; elim (inject_not_undefined B'); auto.
    inversion_clear a. rewrite H2 in H1.
    rewrite Xmatch_elim, <- H2 in H1; auto.
    rewrite collapse_inject; apply inject_not_undefined.
+ elim (collapse_char' B1); intro.
  2: rewrite b0 in H; elim (inject_not_undefined B'); auto.
  inversion_clear a. rewrite H0 in H.
  rewrite Xmatch_elim, <- H0 in H.
  elim (collapse_char' B2); intro.
  2: rewrite b0 in H; elim (inject_not_undefined B'); auto.
  inversion_clear a. rewrite H1 in H.
  rewrite Xmatch_elim, <- H1 in H; auto.
  all: rewrite collapse_inject; apply inject_not_undefined.
Qed.
(** Relationship with merge. *)
Local Ltac prove_this B HB := 
    elim (XUndefined_dec B); intro HB;
    [ rewrite HB; auto | rewrite Xmatch_elim; auto ].

Local Ltac assert_this B B' H :=
  assert ({ collapse B = XUndefined } + { collapse B' = XUndefined });
  [ elim (XUndefined_dec (collapse B)); auto; intros;
    elim (XUndefined_dec (collapse B')); auto; intros;
    do 2 rewrite Xmatch_elim in H; auto; inversion H | idtac].

Lemma collapse_merge : forall B B',
  collapse B = XUndefined -> collapse (Xmerge B B') = XUndefined.
Proof.
induction B using XBehaviour_ind'; induction B' using XBehaviour_ind';
  auto.
+ elim (XUndefined_dec (collapse B)); intros.
  2: { simpl in H. rewrite Xmatch_elim in H; auto. inversion H. }
  simpl. case Pid_dec; auto. case Expr_dec; auto.
  simpl. elim (XUndefined_dec (Xmerge B B')); intros.
  rewrite a0; auto. rewrite Xmatch_elim; auto.
  simpl. rewrite IHB; auto.
+ elim (XUndefined_dec (collapse B)); intros.
  2: { simpl in H. rewrite Xmatch_elim in H; auto. inversion H. }
  simpl. case Pid_dec; auto. case Var_dec; auto.
  simpl. elim (XUndefined_dec (Xmerge B B')); intros.
  rewrite a0; auto. rewrite Xmatch_elim; auto.
  simpl. rewrite IHB; auto.
+ elim (XUndefined_dec (collapse B)); intros.
  2: { simpl in H. rewrite Xmatch_elim in H; auto. inversion H. }
  simpl. case Pid_dec; auto. case eqb_label; auto.
  simpl. elim (XUndefined_dec (Xmerge B B')); intros.
  rewrite a0; auto. rewrite Xmatch_elim; auto.
  simpl. rewrite IHB; auto.
+ simpl. case Pid_dec; auto.
  case_eq mB; case_eq mB'; case_eq mB0; case_eq mB'0; intros;
  try (inversion H7; fail).
  - prove_this (Xmerge x2 x0) a. prove_this (Xmerge x1 x) a'.
    assert_this x1 x2 H7. inversion_clear H8; simpl.
    rewrite (H0 x1); auto. case (collapse (Xmerge x2 x0)); auto.
    rewrite H; auto.
  - prove_this (Xmerge x1 x) a. prove_this x0 a'.
    assert_this x1 x0 H7. inversion_clear H8; simpl.
    rewrite (H x1); auto.
    rewrite H9. case (collapse (Xmerge x1 x)); auto.
  - prove_this x1 a. prove_this (Xmerge x0 x) a'.
    assert_this x1 x0 H7. inversion_clear H8; simpl.
    rewrite H9; auto.
    rewrite (H0 x0); auto. case (collapse x1); auto.
  - prove_this x0 a. prove_this x a'.
  - prove_this (Xmerge x1 x0) a. prove_this x a'.
    elim (XUndefined_dec (collapse x1)); intro a''; simpl.
    rewrite (H x1); auto.
    rewrite Xmatch_elim in H7; auto. inversion H7.
  - prove_this (Xmerge x0 x) a. simpl.
    elim (XUndefined_dec (collapse x0)); intro a'; simpl.
    rewrite (H x0); auto.
    rewrite Xmatch_elim in H7; auto. inversion H7.
  - prove_this x0 a. prove_this x a'. simpl.
    elim (XUndefined_dec (collapse x0)); intro a''; simpl.
    rewrite a''; auto.
    rewrite Xmatch_elim; auto.
    rewrite Xmatch_elim in H7; auto; inversion H7.
  - prove_this x a.
  - prove_this x0 a. prove_this (Xmerge x1 x) a'.
    elim (XUndefined_dec (collapse x0)); intro a''; simpl.
    rewrite a''; auto.
    elim (XUndefined_dec (collapse x1)); intro; simpl.
    rewrite Xmatch_elim; auto. rewrite (H0 x1); auto.
    rewrite Xmatch_elim in H7; auto; inversion H7.
  - prove_this x a. prove_this x0 a'.
    simpl.
    elim (XUndefined_dec (collapse x0)); intro a''; simpl.
    rewrite a''; auto. case (collapse x); auto.
    elim (XUndefined_dec (collapse x)); intro; simpl.
    rewrite a0; auto.
    rewrite Xmatch_elim; auto.
    rewrite Xmatch_elim in H7; auto; inversion H7.
  - prove_this (Xmerge x0 x) a.
    simpl.
    elim (XUndefined_dec (collapse (Xmerge x0 x))); intro.
    rewrite a0; auto.
    elim (XUndefined_dec (collapse x0)); intro.
    elim b. apply H0; auto.
    rewrite Xmatch_elim in H7; auto. inversion H7.
  - prove_this x a.
+ simpl; intros.
  case BExpr_dec; auto.
  assert_this B1 B2 H. clear H IHB'1 IHB'2.
  inversion_clear H0.
  - generalize (IHB1 B'1 H); clear IHB1 IHB2.
    case (Xmerge B1 B'1); simpl; intros; auto.
    1,7: inversion H0.
    1,2,3: elim (XUndefined_dec (collapse x)); intros;
      [ case (Xmerge B2 B'2); simpl; try rewrite a; auto
      | rewrite Xmatch_elim in H0; auto; inversion H0 ].
    * revert H0. case o, o0; intros.
      4: inversion H0.
      2,3: elim (XUndefined_dec (collapse x)); intros;
        [ case (Xmerge B2 B'2); simpl; try rewrite a; auto
        | rewrite Xmatch_elim in H0; auto; inversion H0 ].
      assert_this x x0 H0.
      inversion_clear H1.
      case (Xmerge B2 B'2); simpl; try rewrite H2; auto.
      case (Xmerge B2 B'2); simpl; case (collapse x); try rewrite H2; auto.
    * assert_this x x0 H0. clear H0.
      inversion_clear H1.
      case (Xmerge B2 B'2); simpl; try rewrite H0; auto.
      case (Xmerge B2 B'2); simpl; case (collapse x); try rewrite H0; auto.
  - generalize (IHB2 B'2 H); clear IHB1 IHB2.
    case (Xmerge B2 B'2); simpl; intros; auto.
    1,7: inversion H0.
    6: case (Xmerge B1 B'1); auto.
    1,2,3: elim (XUndefined_dec (collapse x)); intros;
      [case (Xmerge B1 B'1); simpl; try rewrite a; auto;
        intros; try case o, o0; try case (collapse x0); try case (collapse x1); auto
      | rewrite Xmatch_elim in H0; auto; inversion H0].
    * revert H0. case o, o0; intros.
      4: inversion H0.
      2,3: elim (XUndefined_dec (collapse x)); intros;
        [ case (Xmerge B1 B'1); simpl; try rewrite a; auto;
          intros; try case o, o0; try case (collapse x0); try case (collapse x1); auto
        | rewrite Xmatch_elim in H0; auto; inversion H0].
      assert_this x x0 H0. clear H0.
      inversion_clear H1.
      case (Xmerge B1 B'1); simpl; try rewrite H0; auto;
        intros; try case o, o0; try case (collapse x1); try case (collapse x2); auto.
      case (Xmerge B1 B'1); simpl; try rewrite H0; auto;
        intros; try case o, o0; try case (collapse x); try case (collapse x1); try case (collapse x2); auto.
    * assert_this x x0 H0. clear H0.
      inversion_clear H1.
      case (Xmerge B1 B'1); simpl; try rewrite H0; auto;
        intros; try case o, o0; try case (collapse x1); try case (collapse x2); auto.
      case (Xmerge B1 B'1); simpl; try rewrite H0; auto;
        intros; try case o, o0; try case (collapse x); try case (collapse x1); try case (collapse x2); auto.
+ simpl; intros. inversion H.
Qed.

Lemma collapse_merge' : forall B B',
  collapse B' = XUndefined -> collapse (Xmerge B B') = XUndefined.
Proof. intros. rewrite Xmerge_comm. apply collapse_merge; auto. Qed.

Lemma Xmerge_idempotent : forall B, collapse B <> XUndefined ->
  Xmerge B B = B.
Proof.
intros. elim (collapse_char' B). 2: tauto.
intro. inversion_clear a. rewrite H0.
fold (merge x x). apply merge_idempotent.
Qed.

(** Inversion lemmas for Xmerge. *)
Lemma Xmerge_Cond_inv : forall b Bt Bt' Be Be',
  Xmerge Bt Bt' <> XUndefined -> Xmerge Be Be' <> XUndefined ->
  Xmerge (XCond b Bt Be) (XCond b Bt' Be') = XCond b (Xmerge Bt Bt') (Xmerge Be Be').
Proof.
intros. revert H H0.
simpl. unfold BExpr_dec; rewrite Bdec.eqb_refl.
case_eq (Xmerge Bt Bt'); case_eq (Xmerge Be Be'); simpl; auto.
all: intros; try (elim H1; auto; fail); try (elim H2; auto; fail).
Qed.

Lemma Xmerge_inv_Send : forall B1 B2 p e B,
  Xmerge B1 B2 = XSend p e B -> exists B1' B2',
  B1 = XSend p e B1' /\ B2 = XSend p e B2' /\ Xmerge B1' B2' = B.
Proof.
intros B1 B2.
case B1; case B2; try discriminate.
+ intros. revert H. simpl.
  case_eq (Pid_dec p0 p); intro. 2: discriminate.
  case_eq (Expr_dec e0 e); intro. 2: discriminate.
  elim (XUndefined_dec (Xmerge x0 x)); intro.
  rewrite a; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. unfold Pid_dec in H; unfold Expr_dec in H0.
  rewrite Pdec.eqb_eq in H; rewrite Edec.eqb_eq in H0.
  rewrite H, H0; intros.
  inversion H1; eauto.
+ intros. revert H. simpl.
  case_eq (Pid_dec p0 p); intro. 2: discriminate.
  case_eq (Var_dec v0 v); intro. 2: discriminate.
  elim (XUndefined_dec (Xmerge x0 x)); intro.
  rewrite a; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. unfold Pid_dec in H; unfold Var_dec in H0.
  rewrite Pdec.eqb_eq in H; rewrite Xdec.eqb_eq in H0.
  rewrite H, H0; intros.
  inversion H1; eauto.
+ intros. revert H. simpl.
  case_eq (Pid_dec p0 p); intro. 2: discriminate.
  case_eq (eqb_label l0 l); intro. 2: discriminate.
  elim (XUndefined_dec (Xmerge x0 x)); intro.
  rewrite a; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. unfold Pid_dec in H.
  rewrite Pdec.eqb_eq in H; rewrite label_eqb_eq in H0.
  rewrite H, H0; intros.
  inversion H1; eauto.
+ intros. exfalso.
  revert H. simpl.
  elim Pid_dec. 2: discriminate.
  case o, o0, o1, o2; try discriminate.
  1,2: elim (XUndefined_dec (Xmerge x1 x)); intro Hx1x;
    [rewrite Hx1x | rewrite Xmatch_elim; auto]; try discriminate.
  1: elim (XUndefined_dec (Xmerge x2 x0)); intro Hx2x0;
    [rewrite Hx2x0 | rewrite Xmatch_elim; auto]; try discriminate.
  2,3,6,7,11,12,13,14: elim (XUndefined_dec x); intro Hx;
    [rewrite Hx | rewrite Xmatch_elim; auto]; try discriminate.
  1,3,4,5,8,9: elim (XUndefined_dec x0); intro Hx0;
    [rewrite Hx0 | rewrite Xmatch_elim; auto]; try discriminate.
  2: elim (XUndefined_dec x); intro Hx;
    [rewrite Hx | rewrite Xmatch_elim; auto]; try discriminate.
  1: elim (XUndefined_dec (Xmerge x1 x)); intro Hx1x;
    [rewrite Hx1x | rewrite Xmatch_elim; auto]; try discriminate.
  2,3,4: elim (XUndefined_dec (Xmerge x0 x)); intro Hx0x;
    [rewrite Hx0x | rewrite Xmatch_elim; auto]; try discriminate.
  1: elim (XUndefined_dec (Xmerge x1 x0)); intro Hx1x0;
    [rewrite Hx1x0 | rewrite Xmatch_elim; auto]; try discriminate.
  1: elim (XUndefined_dec x1); intro Hx1;
    [rewrite Hx1 | rewrite Xmatch_elim; auto]; try discriminate.
+ intros. exfalso.
  elim (B.eq_dec b0 b); intro Hb.
  2: revert H; simpl; unfold BExpr_dec; rewrite <- Bdec.eqb_neq in Hb; rewrite Hb; discriminate.
  rewrite Hb in H; clear b0 Hb.
  elim (XUndefined_dec (Xmerge x1 x)); intro H1.
  2: elim (XUndefined_dec (Xmerge x2 x0)); intro H0.
  - revert H. simpl. Beq. rewrite H1; discriminate.
  - revert H. simpl. Beq. rewrite H0, Xmatch_elim. discriminate. auto.
  - rewrite Xmerge_Cond_inv in H; auto. discriminate.
+ intros. exfalso.
  revert H. simpl. elim RecVar_dec; discriminate.
Qed.

Lemma Xmerge_inv_Recv : forall B1 B2 p x B,
  Xmerge B1 B2 = XRecv p x B -> exists B1' B2',
  B1 = XRecv p x B1' /\ B2 = XRecv p x B2' /\ Xmerge B1' B2' = B.
Proof.
intros B1 B2.
case B1; case B2; try discriminate.
+ intros. revert H. simpl.
  case_eq (Pid_dec p0 p); intro. 2: discriminate.
  case_eq (Expr_dec e0 e); intro. 2: discriminate.
  elim (XUndefined_dec (Xmerge x0 x)); intro.
  rewrite a; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. unfold Pid_dec in H; unfold Expr_dec in H0.
  rewrite Pdec.eqb_eq in H; rewrite Edec.eqb_eq in H0.
  rewrite H, H0; intros. discriminate.
+ intros. revert H. simpl.
  case_eq (Pid_dec p0 p); intro. 2: discriminate.
  case_eq (Var_dec v0 v); intro. 2: discriminate.
  elim (XUndefined_dec (Xmerge x0 x)); intro.
  rewrite a; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. unfold Pid_dec in H; unfold Var_dec in H0.
  rewrite Pdec.eqb_eq in H; rewrite Xdec.eqb_eq in H0.
  rewrite H, H0; intros.
  inversion H1; eauto.
+ intros. revert H. simpl.
  case_eq (Pid_dec p0 p); intro. 2: discriminate.
  case_eq (eqb_label l0 l); intro. 2: discriminate.
  elim (XUndefined_dec (Xmerge x0 x)); intro.
  rewrite a; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. unfold Pid_dec in H.
  rewrite Pdec.eqb_eq in H; rewrite label_eqb_eq in H0.
  rewrite H, H0; intros.
  inversion H1; eauto.
+ intros. exfalso.
  revert H. simpl.
  elim Pid_dec. 2: discriminate.
  case o, o0, o1, o2; try discriminate.
  1,2: elim (XUndefined_dec (Xmerge x2 x0)); intro Hx1x;
    [rewrite Hx1x | rewrite Xmatch_elim; auto]; try discriminate.
  1: elim (XUndefined_dec (Xmerge x3 x1)); intro Hx2x0;
    [rewrite Hx2x0 | rewrite Xmatch_elim; auto]; try discriminate.
  2,3,6,7,11,12,13,14: elim (XUndefined_dec x0); intro Hx;
    [rewrite Hx | rewrite Xmatch_elim; auto]; try discriminate.
  1,3,4,5,8,9: elim (XUndefined_dec x1); intro Hx0;
    [rewrite Hx0 | rewrite Xmatch_elim; auto]; try discriminate.
  2: elim (XUndefined_dec x0); intro Hx;
    [rewrite Hx | rewrite Xmatch_elim; auto]; try discriminate.
  1: elim (XUndefined_dec (Xmerge x2 x0)); intro Hx1x;
    [rewrite Hx1x | rewrite Xmatch_elim; auto]; try discriminate.
  2,3,4: elim (XUndefined_dec (Xmerge x1 x0)); intro Hx0x;
    [rewrite Hx0x | rewrite Xmatch_elim; auto]; try discriminate.
  1: elim (XUndefined_dec (Xmerge x2 x1)); intro Hx1x0;
    [rewrite Hx1x0 | rewrite Xmatch_elim; auto]; try discriminate.
  1: elim (XUndefined_dec x2); intro Hx1;
    [rewrite Hx1 | rewrite Xmatch_elim; auto]; try discriminate.
+ intros. exfalso.
  elim (B.eq_dec b0 b); intro Hb.
  2: revert H; simpl; unfold BExpr_dec; rewrite <- Bdec.eqb_neq in Hb; rewrite Hb; discriminate.
  rewrite Hb in H; clear b0 Hb.
  elim (XUndefined_dec (Xmerge x1 x)); intro H1.
  2: elim (XUndefined_dec (Xmerge x2 x0)); intro H0.
  - revert H. simpl. Beq. rewrite H1; discriminate.
  - revert H. simpl. Beq. rewrite H0, Xmatch_elim. discriminate. auto.
  - rewrite Xmerge_Cond_inv in H; auto. discriminate.
+ intros. exfalso.
  revert H. simpl. elim RecVar_dec; discriminate.
Qed.

Lemma Xmerge_inv_Sel : forall B1 B2 p l B,
  Xmerge B1 B2 = XSel p l B -> exists B1' B2',
  B1 = XSel p l B1' /\ B2 = XSel p l B2' /\ Xmerge B1' B2' = B.
Proof.
intros B1 B2.
case B1; case B2; try discriminate.
+ intros. revert H. simpl.
  case_eq (Pid_dec p0 p); intro. 2: discriminate.
  case_eq (Expr_dec e0 e); intro. 2: discriminate.
  elim (XUndefined_dec (Xmerge x0 x)); intro.
  rewrite a; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. unfold Pid_dec in H; unfold Expr_dec in H0.
  rewrite Pdec.eqb_eq in H; rewrite Edec.eqb_eq in H0.
  rewrite H, H0; intros.
  inversion H1; eauto.
+ intros. revert H. simpl.
  case_eq (Pid_dec p0 p); intro. 2: discriminate.
  case_eq (Var_dec v0 v); intro. 2: discriminate.
  elim (XUndefined_dec (Xmerge x0 x)); intro.
  rewrite a; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. unfold Pid_dec in H; unfold Var_dec in H0.
  rewrite Pdec.eqb_eq in H; rewrite Xdec.eqb_eq in H0.
  rewrite H, H0; intros.
  inversion H1; eauto.
+ intros. revert H. simpl.
  case_eq (Pid_dec p0 p); intro. 2: discriminate.
  case_eq (eqb_label l0 l); intro. 2: discriminate.
  elim (XUndefined_dec (Xmerge x0 x)); intro.
  rewrite a; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. unfold Pid_dec in H.
  rewrite Pdec.eqb_eq in H; rewrite label_eqb_eq in H0.
  rewrite H, H0; intros.
  inversion H1; eauto.
+ intros. exfalso.
  revert H. simpl.
  elim Pid_dec. 2: discriminate.
  case o, o0, o1, o2; try discriminate.
  1,2: elim (XUndefined_dec (Xmerge x1 x)); intro Hx1x;
    [rewrite Hx1x | rewrite Xmatch_elim; auto]; try discriminate.
  1: elim (XUndefined_dec (Xmerge x2 x0)); intro Hx2x0;
    [rewrite Hx2x0 | rewrite Xmatch_elim; auto]; try discriminate.
  2,3,6,7,11,12,13,14: elim (XUndefined_dec x); intro Hx;
    [rewrite Hx | rewrite Xmatch_elim; auto]; try discriminate.
  1,3,4,5,8,9: elim (XUndefined_dec x0); intro Hx0;
    [rewrite Hx0 | rewrite Xmatch_elim; auto]; try discriminate.
  2: elim (XUndefined_dec x); intro Hx;
    [rewrite Hx | rewrite Xmatch_elim; auto]; try discriminate.
  1: elim (XUndefined_dec (Xmerge x1 x)); intro Hx1x;
    [rewrite Hx1x | rewrite Xmatch_elim; auto]; try discriminate.
  2,3,4: elim (XUndefined_dec (Xmerge x0 x)); intro Hx0x;
    [rewrite Hx0x | rewrite Xmatch_elim; auto]; try discriminate.
  1: elim (XUndefined_dec (Xmerge x1 x0)); intro Hx1x0;
    [rewrite Hx1x0 | rewrite Xmatch_elim; auto]; try discriminate.
  1: elim (XUndefined_dec x1); intro Hx1;
    [rewrite Hx1 | rewrite Xmatch_elim; auto]; try discriminate.
+ intros. exfalso.
  elim (B.eq_dec b0 b); intro Hb.
  2: revert H; simpl; unfold BExpr_dec; rewrite <- Bdec.eqb_neq in Hb; rewrite Hb; discriminate.
  rewrite Hb in H; clear b0 Hb.
  elim (XUndefined_dec (Xmerge x1 x)); intro H1.
  2: elim (XUndefined_dec (Xmerge x2 x0)); intro H0.
  - revert H. simpl. Beq. rewrite H1; discriminate.
  - revert H. simpl. Beq. rewrite H0, Xmatch_elim. discriminate. auto.
  - rewrite Xmerge_Cond_inv in H; auto. discriminate.
+ intros. exfalso.
  revert H. simpl. elim RecVar_dec; discriminate.
Qed.

Lemma Xmerge_inv_Branching : forall B B' p Bl Br, Xmerge B B' = XBranching p Bl Br ->
  exists Bl' Bl'' Br' Br'', B = XBranching p Bl' Br' /\ B' = XBranching p Bl'' Br''
  /\ (Bl = None -> Bl' = None /\ Bl'' = None)
  /\ (Br = None -> Br' = None /\ Br'' = None)
  /\ (forall BL, Bl = Some BL ->
         (Bl' = None -> Bl'' = Some BL) /\ (Bl'' = None -> Bl' = Some BL)
      /\ (forall BL' BL'', Bl' = Some BL' /\ Bl'' = Some BL'' -> Xmerge BL' BL'' = BL))
  /\ (forall BR, Br = Some BR ->
         (Br' = None -> Br'' = Some BR) /\ (Br'' = None -> Br' = Some BR)
      /\ (forall BR' BR'', Br' = Some BR' /\ Br'' = Some BR'' -> Xmerge BR' BR'' = BR)).
Proof.
intros B B' P Be Bt HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (case o; case o0); try (case o1; case o2);
  simpl; auto; try (intros; inversion HBB'; fail);
  unfold Pid_dec, Expr_dec, Var_dec, BExpr_dec, RecVar_dec; simpl;
  try (case_eq (Pdec.eqb p0 p); intro Hp0p; simpl; try (rewrite Pdec.eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (Edec.eqb e0 e); intro He0e; simpl; try (rewrite Edec.eqb_eq in He0e; rewrite He0e));
  try (case_eq (Xdec.eqb v0 v); intro Hv0v; simpl; try (rewrite Xdec.eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (Bdec.eqb b2 b); intro Hb0b; simpl; try (rewrite Bdec.eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (Rdec.eqb r0 r); intro HX0X; simpl; try (rewrite Rdec.eqb_eq in HX0X; rewrite HX0X));
  intros; try inversion HBB';
  try (elim (XUndefined_dec (Xmerge x0 x)); intro HM;
  [ rewrite HM in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0).
+ elim (XUndefined_dec (Xmerge x0 x2)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge x x1)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some x0), (Some x2), (Some x), (Some x1);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    inversion H6; inversion H7; auto.
+ elim (XUndefined_dec (Xmerge x x1)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec x0); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some x), (Some x1), None, (Some x0);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec x1); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge x x0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, (Some x1), (Some x), (Some x0);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec x0); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0;
  exists None, (Some x0), None, (Some x);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec (Xmerge x0 x1)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some x0), (Some x1), (Some x), None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec (Xmerge x x0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some x), (Some x0), None, None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec x0); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, (Some x0), (Some x), None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, (Some x), None, None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec x0); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge x x1)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some x0), None, (Some x), (Some x1);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec x); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec x0); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some x), None, None, (Some x0);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec (Xmerge x x0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, None, (Some x), (Some x0);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, None, None, (Some x);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec x0); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some x0), None, (Some x), None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some x), None, None, None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, None, (Some x), None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ exists None, None, None, None;
  repeat (split; auto); try inversion H; intros; try inversion H4.
+ clear HBB'.
  revert H0. case Bdec.eqb; intro. 2: inversion H0.
  elim (XUndefined_dec (Xmerge x1 x)); intro HM.
  rewrite HM in H0; inversion H0.
  elim (XUndefined_dec (Xmerge x2 x0)); intro HM'.
  rewrite HM', Xmatch_elim in H0; auto; inversion H0.
  revert HM HM' H0.
  case (Xmerge x1 x); case (Xmerge x2 x0);
  intros; inversion H0.
Qed.

Lemma Xmerge_inv_inject : forall B1 B2 B, Xmerge B1 B2 = inject B ->
  exists B', B1 = inject B'.
Proof.
intros. symmetry in H.
revert B1 B2 B H.
induction B1 using XBehaviour_ind'; induction B2 using XBehaviour_ind';
  simpl; intros;
  try (elim (inject_not_undefined _ H); fail);
  try (elim (inject_not_undefined _ H1); fail).
+ exists End; auto.
+ revert H. case_eq (Pid_dec p p0). case_eq (Expr_dec e e0).
  all: simpl; intros.
  2: elim (inject_not_undefined _ H1).
  2: elim (inject_not_undefined _ H0).
  elim (XUndefined_dec (Xmerge B1 B2)); intro H'.
  1: rewrite H' in H1; elim (inject_not_undefined _ H1).
  rewrite Xmatch_elim in H1; auto.
  clear H H0 e0 p0.
  revert H1. case B; intros; inversion H1.
  2: induction o, o0; inversion H1.
  elim IHB1 with B2 b; auto. intros. destroy H.
  exists (p!e;x); repeat split; simpl.
  rewrite H; auto.
+ revert H. case_eq (Pid_dec p p0). case_eq (Var_dec v v0).
  all: simpl; intros.
  2: elim (inject_not_undefined _ H1).
  2: elim (inject_not_undefined _ H0).
  elim (XUndefined_dec (Xmerge B1 B2)); intro H'.
  1: rewrite H' in H1; elim (inject_not_undefined _ H1).
  rewrite Xmatch_elim in H1; auto.
  clear H H0 v0 p0.
  revert H1. case B; intros; inversion H1.
  2: induction o, o0; inversion H1.
  elim IHB1 with B2 b; auto. intros. destroy H.
  exists (p ? v;x); repeat split; simpl.
  rewrite H; auto.
+ revert H. case_eq (Pid_dec p p0). case_eq (eqb_label l l0).
  all: simpl; intros.
  2: elim (inject_not_undefined _ H1).
  2: elim (inject_not_undefined _ H0).
  elim (XUndefined_dec (Xmerge B1 B2)); intro H'.
  1: rewrite H' in H1; elim (inject_not_undefined _ H1).
  rewrite Xmatch_elim in H1; auto.
  clear H H0 l0 p0.
  revert H1. case B; intros; inversion H1.
  2: induction o, o0; inversion H1.
  elim IHB1 with B2 b; auto. intros. destroy H.
  exists (p(+)l;x); repeat split; simpl.
  rewrite H; auto.
+ revert H3. case_eq (Pid_dec p p0); simpl; intros.
  2: elim (inject_not_undefined _ H4).
  induction mB, mB', mB0, mB'0.
  - elim (XUndefined_dec (Xmerge a x0)); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    elim (XUndefined_dec (Xmerge x x1)); intro H''.
    1: rewrite H'' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    elim H with a x0 a0; auto. intros.
    elim H0 with x x1 b; auto. intros.
    exists (p & Some x2 // Some x3); simpl.
    rewrite H5, H9; auto.
  - elim (XUndefined_dec (Xmerge a x0)); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    elim (XUndefined_dec x); intro H''.
    1: rewrite H'' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    elim H with a x0 a0; auto. intros.
    exists (p & Some x1 // Some b); simpl.
    rewrite H5; auto.
  - elim (XUndefined_dec a); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    elim (XUndefined_dec (Xmerge x x0)); intro H''.
    1: rewrite H'' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    elim H0 with x x0 b; auto. intros.
    exists (p & Some a0 // Some x1); simpl.
    rewrite H5; auto.
  - elim (XUndefined_dec a); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    elim (XUndefined_dec x); intro H''.
    1: rewrite H'' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    exists (p & Some a0 // Some b); auto.
  - elim (XUndefined_dec (Xmerge a x)); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    elim (XUndefined_dec x0); intro H''.
    1: rewrite H'' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    elim H with a x a0; auto. intros.
    exists (p & Some x1 // None); simpl.
    rewrite H5; auto.
  - elim (XUndefined_dec (Xmerge a x)); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    elim H with a x a0; auto. intros.
    exists (p & Some x0 // None); simpl.
    rewrite H5; auto.
  - elim (XUndefined_dec a); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    elim (XUndefined_dec x); intro H''.
    1: rewrite H'' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    exists (p & Some a0 // None); auto.
  - elim (XUndefined_dec a); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    exists (p & Some a0 // None); auto.
  - elim (XUndefined_dec x0); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    elim (XUndefined_dec (Xmerge x x1)); intro H''.
    1: rewrite H'' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    elim H0 with x x1 b; auto. intros.
    exists (p & None // Some x2); simpl.
    rewrite H5; auto.
  - elim (XUndefined_dec x0); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    elim (XUndefined_dec x); intro H''.
    1: rewrite H'' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    exists (p & None // Some b); auto.
  - elim (XUndefined_dec (Xmerge x x0)); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    elim H0 with x x0 b; auto. intros.
    exists (p & None // Some x1); simpl.
    rewrite H5; auto.
  - elim (XUndefined_dec x); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    exists (p & None // Some b); auto.
  - elim (XUndefined_dec x); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    elim (XUndefined_dec x0); intro H''.
    1: rewrite H'' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    exists (p & None // None); auto.
  - elim (XUndefined_dec x); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    exists (p & None // None); auto.
  - elim (XUndefined_dec x); intro H''.
    1: rewrite H'' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    exists (p & None // None); auto.
  - revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    exists (p & None // None); auto.
+ revert H. case_eq (BExpr_dec b b0); simpl; intros.
  2: elim (inject_not_undefined _ H0).
  clear IHB2_1 IHB2_2.
  elim (collapse_char' (Xmerge B1_1 B2_1)); intros.
  elim (collapse_char' (Xmerge B1_2 B2_2)); intros.
  destroy a; destroy a0. rename x into B1, x0 into B2, a into HB1, a0 into HB2.
  elim IHB1_1 with B2_1 B1; auto. intros.
  elim IHB1_2 with B2_2 B2; auto. intros.
  clear IHB1_1 IHB1_2.
  1: exists (If b Then x Else x0); rewrite H1, H2; auto.
  all: assert (collapse (XCond b (Xmerge B1_1 B2_1) (Xmerge B1_2 B2_2)) = XUndefined).
  1,3: simpl; rewrite b1; auto.
  1: case collapse; auto.
  clear a. all: clear b1.
  - assert (inject B = collapse (XCond b (Xmerge B1_1 B2_1) (Xmerge B1_2 B2_2))).
    rewrite <- collapse_inject, H0. case Xmerge; case Xmerge; simpl; auto.
    all: intros.
    4: case o, o0; auto. 1,2,3,4,5,6,7: case (collapse x); auto; case (collapse x0); auto.
    elim (inject_not_undefined B). etransitivity; eauto.
  - assert (inject B = collapse (XCond b (Xmerge B1_1 B2_1) (Xmerge B1_2 B2_2))).
    rewrite <- collapse_inject, H0. case Xmerge; case Xmerge; simpl; auto.
    all: intros.
    4: case o, o0; auto. 1,2,3,4,5,6,7: case (collapse x); auto; case (collapse x0); auto.
    elim (inject_not_undefined B). etransitivity; eauto.
+ exists (Call X); auto.
Qed.

Lemma Xmerge_inv_inject' : forall B1 B2 B, Xmerge B1 B2 = inject B ->
  exists B', B2 = inject B'.
Proof.
intros.
apply Xmerge_inv_inject with B1 B.
rewrite Xmerge_comm; auto.
Qed.

Lemma Xmerge_inv : forall B1 B2 B, Xmerge B1 B2 = inject B ->
  exists B'1 B'2, B1 = inject B'1 /\ B2 = inject B'2 /\ merge B'1 B'2 = inject B.
Proof.
intros.
elim (Xmerge_inv_inject _ _ _ H). intros B1' HB1.
elim (Xmerge_inv_inject' _ _ _ H). intros B2' HB2.
exists B1', B2'; repeat split; auto.
unfold merge. rewrite <- HB1, <- HB2; auto.
Qed.

Lemma Xmerge_inv_XCall : forall B B' X,
  Xmerge B B' = XCall X -> B = XCall X.
Proof.
intros.
elim (Xmerge_inv B B' (Call X)); auto.
intros. destroy H0.
elim (merge_inv_Call _ _ _ H0); intros.
rewrite H1, H3; auto.
Qed.

End Merge.

End SP_Merge.
