Require Export SP.

Section SP_Merge.

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

(* Ltac rewrite eqb_refl := unfold eq_dec; rewrite Pdec.eqb_refl; simpl.
Ltac Eeq := unfold Expr_dec; rewrite Edec.eqb_refl; simpl.
Ltac Beq := unfold BExpr_dec; rewrite Bdec.eqb_refl; simpl.
Ltac Veq := unfold Var_dec; rewrite Xdec.eqb_refl; simpl.
Ltac Xeq := unfold RecVar_dec; rewrite Rdec.eqb_refl; simpl.

Ltac Pneq H := rewrite <- Pdec.eqb_neq in H; rewrite H.
 *)

Section Merge.

Inductive XBehaviour : Type :=
| XEnd : XBehaviour
| XSend : Pid -> Expr -> Ann -> XBehaviour -> XBehaviour
| XRecv : Pid -> Var -> Ann -> XBehaviour -> XBehaviour
| XSel : Pid -> Label -> Ann -> XBehaviour -> XBehaviour
| XBranching : Pid -> option (Ann*XBehaviour) -> option (Ann*XBehaviour) -> XBehaviour
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
 | XSend p e a B' => 1 + Xdepth B'
 | XRecv p x a B' => 1 + Xdepth B'
 | XSel p l a B' => 1 + Xdepth B'
 | XBranching p mB mB' =>
              1 + (match mB with None => 0 | Some (_,B) => Xdepth B end)
                + (match mB' with None => 0 | Some (_,B) => Xdepth B end)
 | XCond b B1 B2 => 1 + Nat.max (Xdepth B1) (Xdepth B2)
 | XCall X => 1
 | XEnd => 1
 | XUndefined => 0
end.

Theorem XBehaviour_ind' :
  forall P:XBehaviour -> Prop,
    P XEnd ->
    (forall p e a B, P B -> P (XSend p e a B)) ->
    (forall p v a B, P B -> P (XRecv p v a B)) ->
    (forall p l a B, P B -> P (XSel p l a B)) ->
    (forall p mB mB', (forall a B, mB = Some (a,B) -> P B) ->
                      (forall a B, mB' = Some (a,B) -> P B) ->
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
    (forall p e a B, P B -> P (XSend p e a B)) ->
    (forall p v a B, P B -> P (XRecv p v a B)) ->
    (forall p l a B, P B -> P (XSel p l a B)) ->
    (forall p mB mB', (forall a B, mB = Some (a,B) -> P B) ->
                      (forall a B, mB' = Some (a,B) -> P B) ->
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

Open Scope SP_scope.

Fixpoint inject (B:Behaviour Sig) : XBehaviour :=
match B with
| End _                           => XEnd
| p ! e @! a; B                   => XSend p e a (inject B)
| p ? v @? a; B                   => XRecv p v a (inject B)
| p (+) l @+ a; B                 => XSel p l a (inject B)
| p & None // None                => XBranching p None None
| p & Some (a,Bl) // None         => XBranching p (Some (a,inject Bl)) None
| p & None // Some (a,Br)         => XBranching p None (Some (a,inject Br))
| p & Some (a,Bl) // Some (a',Br) => XBranching p (Some (a,inject Bl)) (Some (a',inject Br))
| If e Then B1 Else B2            => XCond e (inject B1) (inject B2)
| Call _ X                        => XCall X
end.

Lemma inject_not_undefined : forall B, inject B <> XUndefined.
Proof. induction B; try case o, o0; try case p; try case p0; discriminate. Qed.

Lemma inject_elim : forall B, exists B', inject B = B' /\ B' <> XUndefined.
Proof.
intro; exists (inject B); split; auto.
apply inject_not_undefined.
Qed.

Lemma inject_match : forall B T (X1 X2:T),
  match inject B with XUndefined => X1 | _ => X2 end = X2.
Proof. induction B; try case o, o0; try case p; try case p0; auto. Qed.

Lemma inject_inj : forall B B', inject B = inject B' -> B = B'.
Proof.
induction B using Behaviour_ind'; induction B' using Behaviour_ind';
  intros; auto; try inversion H;
  try (rewrite (IHB _ H4); auto).
all: try (induction mB, mB';
  try induction a; try induction p0; try induction a0; try induction p1;
  inversion H1; fail).
+ induction mB, mB', mB0, mB'0;
  try induction a; try induction p1; try induction p2;
  try induction p3; inversion H3; auto.
  rewrite H with a b b1; auto. rewrite H0 with a0 b0 b2; auto.
  rewrite H with a b b0; auto.
  rewrite H0 with a b b0; auto.
+ rewrite (IHB1 _ H2), (IHB2 _ H3); auto.
+ inversion H1; auto.
Qed.

Fixpoint Xmerge (B1 B2:XBehaviour) : XBehaviour :=
match B1, B2 with
| XEnd,                   XEnd           => XEnd
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
    if (p =? p') && eqb_label l l' && (a =? a')
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

Definition merge B1 B2 := Xmerge (inject B1) (inject B2).

Ltac elim_as mB p := case mB; try induction p.

Lemma merge_undefined_or_behaviour : forall B1 B2,
  { merge B1 B2 = XUndefined } + { exists B, merge B1 B2 = inject B }.
Proof.
unfold merge.
induction B1 using Behaviour_rec'; induction B2 using Behaviour_rec'; auto.
all: try (elim_as mB p0; try elim_as mB' p0; simpl; auto; fail); simpl.
all: try (elim_as mB p1; try elim_as mB' p1; simpl; auto; fail); simpl.
+ right. exists (End _); auto.
+ elim eqb; auto. elim eqb; auto. elim eqb; auto. simpl.
  elim (IHB1 B2); intro. rewrite a1; auto. 
  right. inversion_clear b. rewrite H, inject_match.
  exists (p ! e @! a; x); auto.
+ elim eqb; auto. elim eqb; auto. elim eqb; auto. simpl.
  elim (IHB1 B2); intro. rewrite a1; auto.
  right. inversion_clear b. rewrite H, inject_match.
  exists (p ? v @? a; x); auto.
+ elim eqb; auto. elim eqb_label; auto. elim eqb; auto. simpl.
  elim (IHB1 B2); intro. rewrite a1; auto.
  right. inversion_clear b. rewrite H, inject_match.
  exists (p (+) l @+ a; x); auto.
+ revert X X0 X1 X2.
  elim_as mB p1; elim_as mB' p1; elim_as mB'0 p1; elim_as mB0 p1; intros; simpl.
  all: elim eqb; clear p0; auto; repeat rewrite inject_match.
  - case_eq (eqb Ann a a2); intro; auto.
    elim (X _ _ (eq_refl _) b2); intro X'.
    1: rewrite X'; auto.
    rewrite Xmatch_elim; auto.
    2: destroy X'; rewrite X'; apply inject_not_undefined.
    case_eq (eqb Ann a0 a1); intro; auto.
    elim (X0 _ _ (eq_refl _) b1); intro X0'.
    1: rewrite X0'; auto.
    right. destroy X'; destroy X0'. rewrite X', X0', inject_match.
    exists (p & Some (a,x) // Some (a0,x0)); auto.
  - case_eq (eqb Ann a0 a1); intro; auto.
    elim (X0 _ _ (eq_refl _) b1); intro X0'.
    1: rewrite X0'; auto.
    right. destroy X0'. rewrite X0', inject_match.
    exists (p & Some (a,b) // Some (a0,x)); auto.
  - case_eq (eqb Ann a a1); intro; auto.
    elim (X _ _ (eq_refl _) b1); intro X'.
    1: rewrite X'; auto.
    right. destroy X'. rewrite X', inject_match.
    exists (p & Some (a,x) // Some (a0,b0)); auto.
  - right. exists (p & Some (a,b) // Some (a0,b0)); auto.
  - case_eq (eqb Ann a a1); intro; auto.
    elim (X _ _ (eq_refl _) b1); intro X'.
    1: rewrite X'; auto.
    right. destroy X'. rewrite X', inject_match.
    exists (p & Some (a,x) // Some (a0,b0)); auto.
  - right. exists (p & Some (a,b) // Some (a0,b0)); auto.
  - case_eq (eqb Ann a a0); intro; auto.
    elim (X _ _ (eq_refl _) b0); intro X'.
    1: rewrite X'; auto.
    right. destroy X'. rewrite X', inject_match.
    exists (p & Some (a,x) // None); auto.
  - right. exists (p & Some (a,b) // None); auto.
  - case_eq (eqb Ann a a0); intro; auto.
    elim (X0 _ _ (eq_refl _) b0); intro X0'.
    1: rewrite X0'; auto.
    right. destroy X0'. rewrite X0', inject_match.
    exists (p & Some (a1,b1) // Some (a,x)); auto.
  - case_eq (eqb Ann a a0); intro; auto.
    elim (X0 _ _ (eq_refl _) b0); intro X0'.
    1: rewrite X0'; auto.
    right. destroy X0'. rewrite X0', inject_match.
    exists (p & None // Some (a,x)); auto.
  - right. exists (p & Some (a0,b0) // Some (a,b)); auto.
  - right. exists (p & None // Some (a,b)); auto.
  - right. exists (p & Some (a0,b0) // Some (a,b)); auto.
  - right. exists (p & None // Some (a,b)); auto.
  - right. exists (p & Some (a,b) // None); auto.
  - right. exists (p & None // None); auto.
+ elim eqb; auto.
  elim (IHB1_1 B2_1); intro. rewrite a; auto.
  elim (IHB1_2 B2_2); intro.
  - left. inversion_clear b1. rewrite H, a; case x; intros; try case o, o0; try induction p; try induction p0; auto.
  - right. inversion_clear b1. inversion_clear b2.
    rewrite H, H0.
    exists (If b Then x Else x0); case x, x0; intros;
    try case o, o0; try case o1, o2; try induction p; try induction p0; try induction p1; try induction p2; simpl; auto.
+ elim eqb; auto.
  right. exists (Call _ X); auto.
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
  try rewrite eqb_refl;
  try rewrite eqb_refl;
  try rewrite eqb_refl;
  try rewrite label_eqb_refl;
  try rewrite IHB, inject_match;
  simpl; auto.
+ induction p0, p1. simpl. repeat rewrite eqb_refl.
  rewrite (H t), (H0 a), inject_match, inject_match; auto.
+ induction p0; simpl. repeat rewrite eqb_refl.
  rewrite (H a), inject_match; auto.
+ induction p0; simpl. repeat rewrite eqb_refl.
  rewrite (H0 a), inject_match; auto.
+ rewrite IHB1, IHB2.
  case B1, B2; intros; try case o, o0; try case o1, o2;
  try induction p; try induction p0; try induction p1; try induction p2;
  simpl; auto.
Qed.

Lemma Xmerge_comm : forall B B', Xmerge B B' = Xmerge B' B.
Proof.
induction B using XBehaviour_ind'; induction B' using XBehaviour_ind'; simpl; auto.
(* Call *)
6: {
  rewrite (eqb_sym _ X0); case_eq (X =? X0); intro HX0X; auto.
  rewrite eqb_eq in HX0X; rewrite HX0X; auto.
}
(* Cond *)
5: {
  rewrite (eqb_sym _ b0); case_eq (b =? b0); intro Hb0b; simpl; auto.
  rewrite eqb_eq in Hb0b; rewrite Hb0b, IHB1, IHB2; auto.
}
all: rewrite (eqb_sym _ p0); case_eq (p =? p0); intro Hp0p; simpl; auto;
     rewrite eqb_eq in Hp0p; rewrite <- Hp0p in *; clear p0 Hp0p.
1: rewrite (eqb_sym _ e0); case_eq (e =? e0); intro He0e; simpl; auto;
   rewrite eqb_eq in He0e; rewrite <- He0e in *; clear e0 He0e.
2: rewrite (eqb_sym _ v0); case_eq (v =? v0); intro Hv0v; simpl; auto;
   rewrite eqb_eq in Hv0v; rewrite <- Hv0v in *; clear v0 Hv0v.
3: rewrite (label_eqb_sym l0); case_eq (eqb_label l l0); intro Hl0l; simpl; auto;
   rewrite label_eqb_eq in Hl0l; rewrite <- Hl0l in *; clear l0 Hl0l.
1,2,3: rewrite (eqb_sym _ a0); case_eq (a =? a0); intro Ha0a; simpl; auto;
       rewrite eqb_eq in Ha0a; rewrite <- Ha0a in *; rewrite IHB; auto.
(* Branch *)
revert H H0 H1 H2.
case_eq mB; case_eq mB'; case_eq mB0; case_eq mB'0; intros; auto.
all: induction p0; try induction p1; try induction p2; try induction p3.
all: repeat rewrite eqb_refl.
all: try rewrite (H4 _ _ (eq_refl _)); try rewrite (H3 _ _ (eqb_refl)); auto.
1: rewrite (eqb_sym _ a2); case_eq (a0 =? a2); intro Ha0a2; simpl; auto;
       rewrite eqb_eq in Ha0a2; rewrite <- Ha0a2 in *; clear a2 Ha0a2.
1,2,6: rewrite (eqb_sym _ a1); case_eq (a =? a1); intro Haa1; simpl; auto;
       try (rewrite eqb_eq in Haa1; rewrite <- Haa1 in *; clear a1 Haa1).
5,7,8: rewrite (eqb_sym _ a0); case_eq (a =? a0); intro Haa0; simpl; auto;
       rewrite eqb_eq in Haa0; rewrite <- Haa0 in *; clear a0 Haa0.
8: rewrite (eqb_sym _ a1); case_eq (a0 =? a1); intro Ha0a1; simpl; auto;
       rewrite eqb_eq in Ha0a1; rewrite <- Ha0a1 in *; clear a1 Ha0a1.
all: try rewrite (H3 _ _ (eq_refl _)); try rewrite (H4 _ _ (eq_refl _)); auto.
Qed.

Lemma merge_comm : forall B B', merge B B' = merge B' B.
Proof. intros. apply Xmerge_comm. Qed.

(** Inversion lemmas about merge. *)
Lemma merge_inv_End : forall B B', merge B B' = XEnd -> B = End _ /\ B' = End _.
Proof.
unfold merge.
intros B B' HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (elim_as o p; elim_as o0 p); try (elim_as o1 p; elim_as o2 p);
  simpl; auto; try (intros; inversion HBB'; fail);
  try (case_eq (p0 =? p); intro Hp0p; simpl; try (rewrite eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (e0 =? e); intro He0e; simpl; try (rewrite eqb_eq in He0e; rewrite He0e));
  try (case_eq (v0 =? v); intro Hv0v; simpl; try (rewrite eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (b2 =? b); intro Hb0b; simpl; try (rewrite eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (r0 =? r); intro HX0X; simpl; try (rewrite eqb_eq in HX0X; rewrite HX0X));
  intros.
all: elim (if_case' _ _ _ _ _ HBB'); intro H0; [clear HBB' | inversion H0].
all: repeat rewrite inject_match in H0; try (inversion H0; fail).
1,2,3,4:
  elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
    [ rewrite HM in H0
    | rewrite Xmatch_elim in H0; auto ]; inversion H0.
all: revert H0.
1,2,6: case_eq (eqb Ann a1 a);
  [intro Ha1a; rewrite eqb_eq in Ha1a
  | intros; inversion H0].
5,6,7: case_eq (eqb Ann a0 a);
  [intro Ha0a; rewrite eqb_eq in Ha0a
  | intros; inversion H0].
4: case_eq (eqb Ann a1 a0);
  [intro Ha1a0; rewrite eqb_eq in Ha1a0
  | intros; inversion H0].
all: intros.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  revert H0.
  case_eq (eqb Ann a2 a0);
  [intro Ha2a0; rewrite eqb_eq in Ha2a0
  | intros; inversion H0].
  intros.
  elim (XUndefined_dec (Xmerge (inject b2) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b0))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ revert H0.
  case (Xmerge (inject b1) (inject b));
  case (Xmerge (inject b2) (inject b0)); intros; inversion H0.
Qed.

Lemma merge_inv_Send : forall B B' p e a X, merge B B' = XSend p e a X ->
  exists B1 B1', B = p ! e @! a; B1 /\ B' = p ! e @! a; B1' /\ merge B1 B1' = X.
Proof.
unfold merge.
intros B B' P E A X HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (elim_as o p; elim_as o0 p); try (elim_as o1 p; elim_as o2 p);
  simpl; auto; try (intros; inversion HBB'; fail);
  try (case_eq (p0 =? p); intro Hp0p; simpl; try (rewrite eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (e0 =? e); intro He0e; simpl; try (rewrite eqb_eq in He0e; rewrite He0e));
  try (case_eq (v0 =? v); intro Hv0v; simpl; try (rewrite eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (b2 =? b); intro Hb0b; simpl; try (rewrite eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (r0 =? r); intro HX0X; simpl; try (rewrite eqb_eq in HX0X; rewrite HX0X));
  intros.
all: elim (if_elim _ _ _ _ _ HBB'); intro H0; inversion_clear H0; clear HBB';
  [ repeat (apply andb_prop in H; destruct H) | inversion H1 ].
all: repeat rewrite inject_match in H1; try (inversion H1; fail).
1: {
  elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM; 
      [ rewrite HM in H1
      | rewrite Xmatch_elim in H1; auto ]; inversion H1; auto.
  exists b0, b; repeat split; auto.
  rewrite eqb_eq in H, H0, H2; rewrite H, H0, H2; auto.
}
1,2,3: elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM; 
      [ rewrite HM in H1
      | rewrite Xmatch_elim in H1; auto ]; inversion H1; auto.
all: revert H1.
1,2,6: case_eq (eqb Ann a1 a);
  [intro Ha1a; rewrite eqb_eq in Ha1a
  | intros; inversion H1].
5,6,7: case_eq (eqb Ann a0 a);
  [intro Ha0a; rewrite eqb_eq in Ha0a
  | intros; inversion H1].
4: case_eq (eqb Ann a1 a0);
  [intro Ha1a0; rewrite eqb_eq in Ha1a0
  | intros; inversion H1].
all: intros; rename H1 into H0.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  revert H0.
  case_eq (eqb Ann a2 a0);
  [intro Ha2a0; rewrite eqb_eq in Ha2a0
  | intros; inversion H1].
  intros.
  elim (XUndefined_dec (Xmerge (inject b2) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b0))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ revert H0.
  case (Xmerge (inject b1) (inject b));
  case (Xmerge (inject b2) (inject b0)); intros; inversion H0.
Qed.

Lemma merge_inv_Recv : forall B B' p v a X, merge B B' = XRecv p v a X ->
  exists B1 B1', B = p ? v @?a ; B1 /\ B' = p ? v @?a ; B1' /\ merge B1 B1' = X.
Proof.
unfold merge.
intros B B' P E A X HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (elim_as o p; elim_as o0 p); try (elim_as o1 p; elim_as o2 p);
  simpl; auto; try (intros; inversion HBB'; fail);
  try (case_eq (p0 =? p); intro Hp0p; simpl; try (rewrite eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (e0 =? e); intro He0e; simpl; try (rewrite eqb_eq in He0e; rewrite He0e));
  try (case_eq (v0 =? v); intro Hv0v; simpl; try (rewrite eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (b2 =? b); intro Hb0b; simpl; try (rewrite eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (r0 =? r); intro HX0X; simpl; try (rewrite eqb_eq in HX0X; rewrite HX0X));
  intros.
all: elim (if_elim _ _ _ _ _ HBB'); intro H0; inversion_clear H0; clear HBB';
  [ repeat (apply andb_prop in H; destruct H) | inversion H1 ].
all: repeat rewrite inject_match in H1; try (inversion H1; fail).
1,3,4: elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM; 
      [ rewrite HM in H1
      | rewrite Xmatch_elim in H1; auto ]; inversion H1; auto.
1: {
  elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM; 
      [ rewrite HM in H1
      | rewrite Xmatch_elim in H1; auto ]; inversion H1; auto.
  exists b0, b; repeat split; auto.
  rewrite eqb_eq in H, H0, H2; rewrite H, H0, H2; auto.
}
all: revert H1.
1,2,6: case_eq (eqb Ann a1 a);
  [intro Ha1a; rewrite eqb_eq in Ha1a
  | intros; inversion H1].
5,6,7: case_eq (eqb Ann a0 a);
  [intro Ha0a; rewrite eqb_eq in Ha0a
  | intros; inversion H1].
4: case_eq (eqb Ann a1 a0);
  [intro Ha1a0; rewrite eqb_eq in Ha1a0
  | intros; inversion H1].
all: intros; rename H1 into H0.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  revert H0.
  case_eq (eqb Ann a2 a0);
  [intro Ha2a0; rewrite eqb_eq in Ha2a0
  | intros; inversion H1].
  intros.
  elim (XUndefined_dec (Xmerge (inject b2) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b0))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ revert H0.
  case (Xmerge (inject b1) (inject b));
  case (Xmerge (inject b2) (inject b0)); intros; inversion H0.
Qed.

Lemma merge_inv_Sel : forall B B' p l a X, merge B B' = XSel p l a X ->
  exists B1 B1', B = p (+) l @+ a; B1 /\ B' = p (+) l @+ a; B1' /\ merge B1 B1' = X.
Proof.
unfold merge.
intros B B' P E A X HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (elim_as o p; elim_as o0 p); try (elim_as o1 p; elim_as o2 p);
  simpl; auto; try (intros; inversion HBB'; fail);
  try (case_eq (p0 =? p); intro Hp0p; simpl; try (rewrite eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (e0 =? e); intro He0e; simpl; try (rewrite eqb_eq in He0e; rewrite He0e));
  try (case_eq (v0 =? v); intro Hv0v; simpl; try (rewrite eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (b2 =? b); intro Hb0b; simpl; try (rewrite eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (r0 =? r); intro HX0X; simpl; try (rewrite eqb_eq in HX0X; rewrite HX0X));
  intros.
all: elim (if_elim _ _ _ _ _ HBB'); intro H0; inversion_clear H0; clear HBB';
  [ repeat (apply andb_prop in H; destruct H) | inversion H1 ].
all: repeat rewrite inject_match in H1; try (inversion H1; fail).
1,2: elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM; 
      [ rewrite HM in H1
      | rewrite Xmatch_elim in H1; auto ]; inversion H1; auto.
1: {
  elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM; 
      [ rewrite HM in H1
      | rewrite Xmatch_elim in H1; auto ]; inversion H1; auto.
  exists b0, b; repeat split; auto.
  rewrite eqb_eq in H, H0; rewrite H, H0; auto.
}
1: inversion H2.
all: revert H1.
1,2,6: case_eq (eqb Ann a1 a);
  [intro Ha1a; rewrite eqb_eq in Ha1a
  | intros; inversion H1].
5,6,7: case_eq (eqb Ann a0 a);
  [intro Ha0a; rewrite eqb_eq in Ha0a
  | intros; inversion H1].
4: case_eq (eqb Ann a1 a0);
  [intro Ha1a0; rewrite eqb_eq in Ha1a0
  | intros; inversion H1].
all: intros; rename H1 into H0.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  revert H0.
  case_eq (eqb Ann a2 a0);
  [intro Ha2a0; rewrite eqb_eq in Ha2a0
  | intros; inversion H1].
  intros.
  elim (XUndefined_dec (Xmerge (inject b2) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b0))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ revert H0.
  case (Xmerge (inject b1) (inject b));
  case (Xmerge (inject b2) (inject b0)); intros; inversion H0.
Qed.

Lemma merge_inv_Branching : forall B B' p Bl Br, merge B B' = XBranching p Bl Br ->
  exists Bl' Bl'' Br' Br'', B = p & Bl' // Br' /\ B' = p & Bl'' // Br''
  /\ (Bl = None -> Bl' = None /\ Bl'' = None)
  /\ (Br = None -> Br' = None /\ Br'' = None)
  /\ (forall a BL, Bl = Some (a,BL) ->
         (Bl' = None -> exists BL'', Bl'' = Some (a,BL'') /\ BL = inject BL'')
      /\ (Bl'' = None -> exists BL', Bl' = Some (a,BL') /\ BL = inject BL')
      /\ (forall a' a'' BL' BL'', Bl' = Some (a',BL') /\ Bl'' = Some (a'',BL'') ->
            a' = a /\ a'' = a /\ merge BL' BL'' = BL))
  /\ (forall a BR, Br = Some (a,BR) ->
         (Br' = None -> exists BR'', Br'' = Some (a,BR'') /\ BR = inject BR'')
      /\ (Br'' = None -> exists BR', Br' = Some (a,BR') /\ BR = inject BR')
      /\ (forall a' a'' BR' BR'', Br' = Some (a',BR') /\ Br'' = Some (a'',BR'') ->
            a' = a /\ a'' = a /\ merge BR' BR'' = BR)).
Proof.
unfold merge.
intros B B' P E X HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (elim_as o p; elim_as o0 p); try (elim_as o1 p; elim_as o2 p);
  simpl; auto; try (intros; inversion HBB'; fail);
  try (case_eq (p0 =? p); intro Hp0p; simpl; try (rewrite eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (e0 =? e); intro He0e; simpl; try (rewrite eqb_eq in He0e; rewrite He0e));
  try (case_eq (v0 =? v); intro Hv0v; simpl; try (rewrite eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (b2 =? b); intro Hb0b; simpl; try (rewrite eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (r0 =? r); intro HX0X; simpl; try (rewrite eqb_eq in HX0X; rewrite HX0X));
  intros.
all: elim (if_elim _ _ _ _ _ HBB'); intro H0; inversion_clear H0; clear HBB';
  [ repeat (apply andb_prop in H; destruct H) | inversion H1 ].
all: repeat rewrite inject_match in H1; try (inversion H1; fail).
1,3,4: elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM; 
      [ rewrite HM in H1
      | rewrite Xmatch_elim in H1; auto ]; inversion H1; auto.
1: {
  elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM; 
      [ rewrite HM in H1
      | rewrite Xmatch_elim in H1; auto ]; inversion H1; auto.
}
all: revert H1.
1,2,9: case_eq (eqb Ann a1 a);
  [intro Ha1a; rewrite eqb_eq in Ha1a
  | intros; inversion H1].
6,7,11: case_eq (eqb Ann a0 a);
  [intro Ha0a; rewrite eqb_eq in Ha0a
  | intros; inversion H1].
4: case_eq (eqb Ann a1 a0);
  [intro Ha1a0; rewrite eqb_eq in Ha1a0
  | intros; inversion H1].
all: intros; rename H1 into H0; apply eqb_eq in H.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  revert H0. case_eq (eqb Ann a2 a0);
  [intro Ha2a0; rewrite eqb_eq in Ha2a0
  | intros; inversion H1].
  intros.
  elim (XUndefined_dec (Xmerge (inject b2) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some (a1,b1)), (Some (a,b)), (Some (a2,b2)), (Some (a0,b0)); rewrite H;
  repeat (split; auto); intros; try inversion H5;
    inversion H1; inversion H6; inversion H7; auto.
  1,2: transitivity a1; auto. transitivity a; auto.
  1,2: transitivity a2; auto. transitivity a0; auto.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  exists (Some (a1,b1)), (Some (a,b)), None, (Some (a0,b0)); rewrite H.
  rewrite H in H0; inversion H0.
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try inversion H6; try inversion H8; try inversion H9; auto.
  1,2: transitivity a1; auto. transitivity a; auto.
  exists b0; auto.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some (a0,b0)), None, (Some (a1,b1)), (Some (a,b)); rewrite H.
  rewrite H in H0; inversion H0.
  repeat (split; auto); try inversion H1; intros; try inversion H8;
    try inversion H9; try inversion H12; auto.
  exists b0; auto.
  all: transitivity a1; auto. transitivity a; auto.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, (Some (a,b)), (Some (a1,b1)), (Some (a0,b0)); rewrite H.
  rewrite H in H0; inversion H0.
  repeat (split; auto); try inversion H1; intros; try inversion H8;
    try inversion H9; try inversion H11; try inversion H12; auto.
  exists b; auto.
  all: transitivity a1; auto. transitivity a0; auto.
+ exists None, (Some (a,b)), None, (Some (a0,b0)); rewrite H.
  rewrite H in H0; inversion H0.
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try inversion H6; try inversion H8; try inversion H9; auto.
  exists b; auto.
  exists b0; auto.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some (a0,b0)), (Some (a,b)), (Some (a1,b1)), None; rewrite H.
  rewrite H in H0; inversion H0.
  repeat (split; auto); try inversion H1; intros; try inversion H8;
    try inversion H9; try inversion H12; auto.
  1,2: transitivity a0; auto. transitivity a; auto.
  exists b1; auto.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some (a0,b0)), (Some (a,b)), None, None; rewrite H.
  rewrite H in H0; inversion H0.
  repeat (split; auto); try inversion H1; intros; try inversion H8;
    try inversion H9; try inversion H12; auto.
  1,2: transitivity a0; auto. transitivity a; auto.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, None, (Some (a0,b0)), (Some (a,b)); rewrite H.
  rewrite H in H0; inversion H0.
  repeat (split; auto); try inversion H1; intros; try inversion H8;
    try inversion H9; try inversion H11; try inversion H12; auto.
  all: transitivity a0; auto. transitivity a; auto.
+ exists None, (Some (a,b)), (Some (a0,b0)), None; rewrite H.
  rewrite H in H0; inversion H0.
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try inversion H6; try inversion H8; try inversion H9; auto.
  exists b; auto.
  exists b0; auto.
+ exists None, (Some (a,b)), None, None; rewrite H.
  rewrite H in H0; inversion H0.
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try inversion H6; try inversion H8; try inversion H9; auto.
  exists b; auto.
+ exists (Some (a0,b0)), None, None, (Some (a,b)); rewrite H.
  rewrite H in H0; inversion H0.
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try inversion H6; try inversion H8; try inversion H9; auto.
  exists b0; auto.
  exists b; auto.
+ exists None, None, None, (Some (a,b)); rewrite H.
  rewrite H in H0; inversion H0.
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try inversion H6; try inversion H8; try inversion H9; auto.
  exists b; auto.
+ exists (Some (a,b)), None, (Some (a0,b0)), None; rewrite H.
  rewrite H in H0; inversion H0.
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try inversion H8; try inversion H9; auto.
  exists b; auto.
  exists b0; auto.
+ exists (Some (a,b)), None, None, None; rewrite H.
  rewrite H in H0; inversion H0.
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try inversion H8; try inversion H9; auto.
  exists b; auto.
+ exists None, None, (Some (a,b)), None; rewrite H.
  rewrite H in H0; inversion H0.
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try inversion H8; try inversion H9; auto.
  exists b; auto.
+ exists None, None, None, None; inversion H0; rewrite H.
  repeat (split; auto); try inversion H1.
+ revert H0.
  case (Xmerge (inject b1) (inject b));
  case (Xmerge (inject b2) (inject b0)); intros; inversion H0.
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

Lemma merge_inv_Branching_Some_None : forall B B' p a Bl,
  merge B B' = XBranching p (Some (a,Bl)) None ->
  (B = p & None // None /\ exists BL, B' = p & Some (a,BL) // None  /\ Bl = inject BL)
  \/ ((exists BL, B = p & Some (a,BL) // None /\ Bl = inject BL) /\ B' = p & None // None)
  \/ exists BL' BL'', B = p & Some (a,BL') // None /\ B' = p & Some (a,BL'') // None
    /\ merge BL' BL'' = Bl.
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
  merge B B' = XBranching p None (Some (a,Br)) ->
  (B = p & None // None /\ exists BR, B' = p & None // Some (a,BR)  /\ Br = inject BR)
  \/ ((exists BR, B = p & None // Some (a,BR) /\ Br = inject BR) /\ B' = p & None // None)
  \/ exists BR' BR'', B = p & None // Some (a,BR') /\ B' = p & None // Some (a,BR'')
    /\ merge BR' BR'' = Br.
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
  exists Be' Be'' Bt' Bt'', B = Cond _ b Be' Bt' /\ B' = Cond _ b Be'' Bt''
    /\ merge Be' Be'' = Be /\ merge Bt' Bt'' = Bt.
Proof.
unfold merge.
intros B B' P E X HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (elim_as o p; elim_as o0 p); try (elim_as o1 p; elim_as o2 p);
  simpl; auto; try (intros; inversion HBB'; fail);
  try (case_eq (p0 =? p); intro Hp0p; simpl; try (rewrite eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (e0 =? e); intro He0e; simpl; try (rewrite eqb_eq in He0e; rewrite He0e));
  try (case_eq (v0 =? v); intro Hv0v; simpl; try (rewrite eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (b2 =? b); intro Hb0b; simpl; try (rewrite eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (r0 =? r); intro HX0X; simpl; try (rewrite eqb_eq in HX0X; rewrite HX0X));
  intros.
all: elim (if_elim _ _ _ _ _ HBB'); intro H0; inversion_clear H0; clear HBB';
  [ try apply andb_prop in H; destroy H; try apply andb_prop in H0; destroy H0 | inversion H1 ].
1,2,3: elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H1
  | rewrite Xmatch_elim in H1; auto ]; inversion H1.
1: inversion H0.
all: rename H1 into H8; revert H8.
all: repeat rewrite inject_match.
1,2,9: case_eq (eqb Ann a1 a);
  [intro Ha1a; rewrite eqb_eq in Ha1a
  | intros; inversion H8].
6,7,11: case_eq (eqb Ann a0 a);
  [intro Ha0a; rewrite eqb_eq in Ha0a
  | intros; inversion H8].
4: case_eq (eqb Ann a1 a0);
  [intro Ha1a0; rewrite eqb_eq in Ha1a0
  | intros; inversion H8].
all: intros.
1: elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HT1;
  [ rewrite HT1 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
1: revert H8; case_eq (eqb Ann a2 a0);
  [intro Ha2a0; intros; rewrite eqb_eq in Ha2a0
  | intros; inversion H8].
1: elim (XUndefined_dec (Xmerge (inject b2) (inject b0))); intro HT2;
  [ rewrite HT2 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
2,3: elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HT2;
  [ rewrite HT2 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
4: elim (XUndefined_dec (Xmerge (inject b1) (inject b0))); intro HT3;
  [ rewrite HT3 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
6,7,8: elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HT4;
  [ rewrite HT4 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
all: try inversion H8.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HM.
  rewrite HM in H8; inversion H8.
  elim (XUndefined_dec (Xmerge (inject b2) (inject b0))); intro HM'.
  rewrite HM', Xmatch_elim in H8; auto; inversion H8.
  exists b1, b, b2, b0.
  revert HM HM' H8.
  rewrite eqb_eq in H; rewrite H.
  case (Xmerge (inject b1) (inject b));
  case (Xmerge (inject b2) (inject b0)); intros;
  inversion H8; auto.
Qed.

Lemma merge_inv_Call : forall B B' X, merge B B' = XCall X ->
  B = Call _ X /\ B' = Call _ X.
Proof.
unfold merge.
intros B B' X HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (elim_as o p; elim_as o0 p); try (elim_as o1 p; elim_as o2 p);
  simpl; auto; try (intros; inversion HBB'; fail);
  try (case_eq (p0 =? p); intro Hp0p; simpl; try (rewrite eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (e0 =? e); intro He0e; simpl; try (rewrite eqb_eq in He0e; rewrite He0e));
  try (case_eq (v0 =? v); intro Hv0v; simpl; try (rewrite eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (b2 =? b); intro Hb0b; simpl; try (rewrite eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (r0 =? r); intro HX0X; simpl; try (rewrite eqb_eq in HX0X; rewrite HX0X));
  intros.
all: elim (if_elim _ _ _ _ _ HBB'); intro H0; inversion_clear H0; clear HBB';
  [ repeat (apply andb_prop in H; destruct H) | inversion H1 ].
all: repeat rewrite inject_match in H1; try (inversion H1; fail).
1,2,3,4: elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM; 
      [ rewrite HM in H1
      | rewrite Xmatch_elim in H1; auto ]; inversion H1; auto.
all: revert H1.
1,2,6: case_eq (eqb Ann a1 a);
  [intro Ha1a; rewrite eqb_eq in Ha1a
  | intros; inversion H1].
5,6,7: case_eq (eqb Ann a0 a);
  [intro Ha0a; rewrite eqb_eq in Ha0a
  | intros; inversion H1].
4: case_eq (eqb Ann a1 a0);
  [intro Ha1a0; rewrite eqb_eq in Ha1a0
  | intros; inversion H1].
all: intros; rename H1 into H0.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  revert H0.
  case_eq (eqb Ann a2 a0);
  [intro Ha2a0; rewrite eqb_eq in Ha2a0
  | intros; inversion H1].
  intros.
  elim (XUndefined_dec (Xmerge (inject b2) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b1) (inject b0))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  inversion H0.
+ revert H0.
  case (Xmerge (inject b1) (inject b));
  case (Xmerge (inject b2) (inject b0)); intros; inversion H0.
+ inversion H0. rewrite eqb_eq in H; rewrite H; auto.
Qed.

(** Collapse an Undefined behaviour. *)
Fixpoint collapse (B:XBehaviour) : XBehaviour :=
let rec := fun B' => match collapse B' with XUndefined => XUndefined | _ => B end in
match B with
| XSend p e a B' => rec B'
| XRecv p x a B' => rec B'
| XSel p l a B'  => rec B'
| XBranching p mB mB' => match mB, mB' with
                         | None,    None            => B
                         | Some (a,Bl), None        => rec Bl
                         | None,    Some (a,Br)     => rec Br
                         | Some (_,Bl), Some (_,Br) => match collapse Bl, collapse Br with
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
revert H H0.
elim_as mB p0; elim_as mB' p0; intros; simpl; auto.
+ rewrite (H _ _ (eq_refl)), (H0 _ _ (eq_refl)), inject_match, inject_match; auto.
+ rewrite (H _ _ (eq_refl)), inject_match; auto.
+ rewrite (H0 _ _ (eq_refl)), inject_match; auto.
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
+ revert X X0.
  elim_as mB p0; elim_as mB' p0; intros; auto.
  - elim (X _ _ (eq_refl)); intro HB; rewrite HB; auto; XBeh_case b Hx.
    elim (X0 _ _ (eq_refl)); intro HB'; rewrite HB'; auto; XBeh_case b0 Hx0.
  - elim (X _ _ (eq_refl)); intro HB; rewrite HB; auto; XBeh_case b Hx.
  - elim (X0 _ _ (eq_refl)); intro HB'; rewrite HB'; auto; XBeh_case b Hx.
+ elim IHB1; intro H1; rewrite H1; auto; XBeh_case B1 HB1.
  elim IHB2; intro H2; rewrite H2; auto; XBeh_case B2 HB2.
Qed.

Lemma collapse_char' : forall B,
  ({B' | B = inject B'}) + {collapse B = XUndefined}.
Proof.
induction B using XBehaviour_rec'; simpl; auto.
+ left; exists (End _); auto.
+ elim IHB; intro H; try rewrite H; auto.
  left; elim H; clear H; intros B' HB'; rewrite HB'.
  exists (p ! e @! a ; B'); simpl; auto.
+ elim IHB; intro H; try rewrite H; auto.
  left; elim H; clear H; intros B' HB'; rewrite HB'.
  exists (p ? v @? a; B'); simpl; auto.
+ elim IHB; intro H; try rewrite H; auto.
  left; elim H; clear H; intros B' HB'; rewrite HB'.
  exists (p (+) l @+a ; B'); simpl; auto.
+ revert X X0.
  elim_as mB p0; elim_as mB' p0; intros; auto.
  - elim (X _ _ (eq_refl)); intro HB; try rewrite HB; auto.
    rewrite Xmatch_elim. 2: apply inject_exists; auto.
    elim (X0 _ _ (eq_refl)); intro HB'; try rewrite HB'; auto.
    rewrite Xmatch_elim. 2: apply inject_exists; auto.
    left; inversion_clear HB; inversion_clear HB'.
    exists (p & Some (a,x) // Some (a0,x0)); rewrite H, H0; auto.
  - elim (X _ _ (eq_refl)); intro HB; try rewrite HB; auto.
    rewrite Xmatch_elim. 2: apply inject_exists; auto.
    left; inversion_clear HB.
    exists (p & Some (a,x) // None); rewrite H; auto.
  - elim (X0 _ _ (eq_refl)); intro HB'; try rewrite HB'; auto.
    rewrite Xmatch_elim. 2: apply inject_exists; auto.
    left; inversion_clear HB'.
    exists (p & None // Some (a,x)); rewrite H; auto.
  - left. exists (p & None // None); auto.
+ elim IHB1; intro H1; try rewrite H1; auto.
  rewrite Xmatch_elim. 2: apply inject_exists; auto.
  elim IHB2; intro H2; try rewrite H2; auto.
  rewrite Xmatch_elim. 2: apply inject_exists; auto.
  left; inversion_clear H1; inversion_clear H2.
  exists (If b Then x Else x0); rewrite H, H0; auto.
+ left; exists (Call _ X); auto.
Qed.

Lemma collapse_char'' : forall B, collapse B = XUndefined ->
  forall B', B <> inject B'.
Proof.
induction B using XBehaviour_ind'; induction B' using Behaviour_ind'.
all: try inversion H.
all: try discriminate.
all: try (elim_as mB p1; elim_as mB' p1; discriminate).
+ elim (XUndefined_dec (collapse B)); intro.
  intro; inversion H0; apply IHB with B'; auto.
  rewrite Xmatch_elim in H1; auto. inversion H1.
+ elim (XUndefined_dec (collapse B)); intro.
  intro; inversion H0; apply IHB with B'; auto.
  rewrite Xmatch_elim in H1; auto. inversion H1.
+ elim (XUndefined_dec (collapse B)); intro.
  intro; inversion H0; apply IHB with B'; auto.
  rewrite Xmatch_elim in H1; auto. inversion H1.
+ induction mB. induction a as (a,B).
  all: induction mB'. induction a0 as (a',B'). 3: induction a as (a',B').
  all: induction mB0. 1,3: induction a0 as (a0,B0). 5,7: induction a as (a0,B0).
  all: induction mB'0. 1,3: induction a1 as (a'0,B'0). 5,7: induction a0 as (a'0,B'0). 9,11,13,15: induction a as (a'0,B'0).
  all: try discriminate.
  all: simpl in H1.
  - elim (XUndefined_dec (collapse B)); intro.
    intro. inversion H4. apply H with (a0:=a) (B0:=B) (B':= B0); auto.
    rewrite Xmatch_elim in H1; auto.
    elim (XUndefined_dec (collapse B')); intro; auto.
    intro. inversion H4. apply H0 with (a:=a') (B:=B') (B':=B'0); auto.
    rewrite Xmatch_elim in H1; auto. rewrite H1; discriminate.
  - elim (XUndefined_dec (collapse B)); intro.
    intro. inversion H4. apply H with (a0:=a) (B0:=B) (B':= B0); auto.
    rewrite Xmatch_elim in H1; auto. rewrite H1; discriminate.
  - elim (XUndefined_dec (collapse B')); intro.
    intro. inversion H4. apply H0 with (a:=a'0) (B:=B') (B':= B'0); auto.
    rewrite H7; auto.
    rewrite Xmatch_elim in H1; auto. rewrite H1; discriminate.
+ elim_as mB p0; elim_as mB' p0; discriminate.
+ elim (XUndefined_dec (collapse B1)); intro.
  intro; inversion H0; apply IHB1 with B'1; auto.
  rewrite Xmatch_elim in H1; auto.
  elim (XUndefined_dec (collapse B2)); intro.
  intro; inversion H0; apply IHB2 with B'2; auto.
  rewrite Xmatch_elim in H1; auto. inversion H1.
+ elim_as mB p0; elim_as mB' p0; discriminate.
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
  inversion_clear a0. rewrite H0 in H.
  rewrite Xmatch_elim, <- H0 in H; auto.
  rewrite collapse_inject; apply inject_not_undefined.
+ elim (collapse_char' B); intro.
  2: rewrite b in H; elim (inject_not_undefined B'); auto.
  inversion_clear a0. rewrite H0 in H.
  rewrite Xmatch_elim, <- H0 in H; auto.
  rewrite collapse_inject; apply inject_not_undefined.
+ elim (collapse_char' B); intro.
  2: rewrite b in H; elim (inject_not_undefined B'); auto.
  inversion_clear a0. rewrite H0 in H.
  rewrite Xmatch_elim, <- H0 in H; auto.
  rewrite collapse_inject; apply inject_not_undefined.
+ induction mB, mB'; auto.
  induction a as (a',Bl); induction p0 as (a'',Br).
  - elim (collapse_char' Bl); intro.
    2: rewrite b in H1; elim (inject_not_undefined B'); auto.
    inversion_clear a. rewrite H2 in H1.
    rewrite Xmatch_elim, <- H2 in H1.
    elim (collapse_char' Br); intro.
    2: rewrite b in H1; elim (inject_not_undefined B'); auto.
    inversion_clear a. rewrite H3 in H1.
    rewrite Xmatch_elim, <- H3 in H1; auto.
    all: rewrite collapse_inject; apply inject_not_undefined.
  - induction a as (a',Bl).
    elim (collapse_char' Bl); intro.
    2: rewrite b in H1; elim (inject_not_undefined B'); auto.
    inversion_clear a. rewrite H2 in H1.
    rewrite Xmatch_elim, <- H2 in H1; auto.
    rewrite collapse_inject; apply inject_not_undefined.
  - induction p0 as (a'',Br).
    elim (collapse_char' Br); intro.
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
  simpl.
  case (eq_dec p p0); intro Hpp0;
    [rewrite <- eqb_eq in Hpp0 | rewrite <- eqb_neq in Hpp0]; rewrite Hpp0.
  2: auto.
  case (eq_dec e e0); intro Hee0;
    [rewrite <- eqb_eq in Hee0 | rewrite <- eqb_neq in Hee0]; rewrite Hee0.
  2: auto.
  case (eq_dec a a0); intro Haa0;
    [rewrite <- eqb_eq in Haa0 | rewrite <- eqb_neq in Haa0]; rewrite Haa0.
  2: auto.
  simpl. elim (XUndefined_dec (Xmerge B B')); intros.
  rewrite a2; auto. rewrite Xmatch_elim; auto.
  simpl. rewrite IHB; auto.
+ elim (XUndefined_dec (collapse B)); intros.
  2: { simpl in H. rewrite Xmatch_elim in H; auto. inversion H. }
  simpl.
  case (eq_dec p p0); intro Hpp0;
    [rewrite <- eqb_eq in Hpp0 | rewrite <- eqb_neq in Hpp0]; rewrite Hpp0.
  2: auto.
  case (eq_dec v v0); intro Hvv0;
    [rewrite <- eqb_eq in Hvv0 | rewrite <- eqb_neq in Hvv0]; rewrite Hvv0.
  2: auto.
  case (eq_dec a a0); intro Haa0;
    [rewrite <- eqb_eq in Haa0 | rewrite <- eqb_neq in Haa0]; rewrite Haa0.
  2: auto.
  simpl. elim (XUndefined_dec (Xmerge B B')); intros.
  rewrite a2; auto. rewrite Xmatch_elim; auto.
  simpl. rewrite IHB; auto.
+ elim (XUndefined_dec (collapse B)); intros.
  2: { simpl in H. rewrite Xmatch_elim in H; auto. inversion H. }
  simpl.
  case (eq_dec p p0); intro Hpp0;
    [rewrite <- eqb_eq in Hpp0 | rewrite <- eqb_neq in Hpp0]; rewrite Hpp0.
  2: auto.
  case eqb_label; auto.
  case (eq_dec a a0); intro Haa0;
    [rewrite <- eqb_eq in Haa0 | rewrite <- eqb_neq in Haa0]; rewrite Haa0.
  2: auto.
  simpl. elim (XUndefined_dec (Xmerge B B')); intros.
  rewrite a2; auto. rewrite Xmatch_elim; auto.
  simpl. rewrite IHB; auto.
+ simpl.
  case (eq_dec p p0); intro Hpp0;
    [rewrite <- eqb_eq in Hpp0 | rewrite <- eqb_neq in Hpp0]; rewrite Hpp0.
  2: auto.
  revert H H0 H1 H2.
  elim_as mB p1; elim_as mB' p1; elim_as mB0 p1; elim_as mB'0 p1; intros;
  try (inversion H3; fail).
  all: try (generalize (H _ _ (eq_refl _))); clear H; intros.
  all: try (generalize (H0 _ _ (eq_refl _))); clear H0; intros.
  all: try (generalize (H1 _ _ (eq_refl _))); clear H1; intros.
  all: try (generalize (H2 _ _ (eq_refl _))); clear H2; intros.
  - case_eq (a =? a1); auto. prove_this (Xmerge b b1) A.
    case_eq (a0 =? a2); auto. prove_this (Xmerge b0 b2) A'.
    assert_this b b0 H3. inversion_clear H4; simpl.
    rewrite H; auto. rewrite H0; auto.
    case (collapse (Xmerge b b1)); auto.
  - case_eq (a =? a1); auto. prove_this (Xmerge b b1) A.
    prove_this b0 A'.
    assert_this b b0 H3. inversion_clear H2; simpl.
    rewrite H; auto.
    rewrite H4. case (collapse (Xmerge b b1)); auto.
  - prove_this b A.
    case_eq (a0 =? a1); auto. prove_this (Xmerge b0 b1) A'.
    assert_this b b0 H3. inversion_clear H2; simpl.
    rewrite H4; auto.
    rewrite H0; auto. case (collapse b); auto.
  - prove_this b A. prove_this b0 A'.
  - case_eq (a =? a0); auto. prove_this (Xmerge b b0) A.
    prove_this b1 A'.
    elim (XUndefined_dec (collapse b)); intro a''; simpl.
    rewrite H; auto.
    rewrite Xmatch_elim in H3; auto. inversion H3.
  - case_eq (a =? a0); auto. prove_this (Xmerge b b0) A. simpl.
    elim (XUndefined_dec (collapse b)); intro a'; simpl.
    rewrite H; auto.
    rewrite Xmatch_elim in H3; auto. inversion H3.
  - prove_this b A. prove_this b0 A'. simpl.
    elim (XUndefined_dec (collapse b)); intro a''; simpl.
    rewrite a''; auto.
    rewrite Xmatch_elim; auto.
    rewrite Xmatch_elim in H3; auto; inversion H3.
  - prove_this b A.
  - prove_this b0 A.
    case_eq (a =? a1); auto. prove_this (Xmerge b b1) A'.
    elim (XUndefined_dec (collapse b0)); intro a''; simpl.
    rewrite a''; auto.
    elim (XUndefined_dec (collapse b)); intro; simpl.
    rewrite Xmatch_elim; auto. rewrite H; auto.
    rewrite Xmatch_elim in H3; auto; inversion H3.
  - prove_this b0 A. prove_this b A'.
    simpl.
    elim (XUndefined_dec (collapse b0)); intro a''; simpl.
    rewrite a''; auto. rewrite Xmatch_elim; auto.
    elim (XUndefined_dec (collapse b)); intro; simpl.
    rewrite a1; auto.
    rewrite Xmatch_elim in H3; auto; inversion H3.
  - case_eq (a =? a0); auto. prove_this (Xmerge b b0) A.
    simpl.
    elim (XUndefined_dec (collapse (Xmerge b b0))); intro.
    rewrite a1; auto.
    elim (XUndefined_dec (collapse b)); intro.
    elim b1; auto.
    rewrite Xmatch_elim in H3; auto. inversion H3.
  - prove_this b A.
+ simpl; intros.
  case (eq_dec b b0); intro Hbb0;
    [rewrite <- eqb_eq in Hbb0 | rewrite <- eqb_neq in Hbb0]; rewrite Hbb0.
  2: auto.
  assert_this B1 B2 H. clear H IHB'1 IHB'2.
  inversion_clear H0.
  - generalize (IHB1 B'1 H); clear IHB1 IHB2.
    case (Xmerge B1 B'1); simpl; intros; auto.
    1,7: inversion H0.
    1,2,3: elim (XUndefined_dec (collapse x)); intros;
      [ case (Xmerge B2 B'2); simpl; try rewrite a; auto
      | rewrite Xmatch_elim in H0; auto; inversion H0 ].
    * revert H0. case o, o0; try induction p; try induction p0; intros.
      4: inversion H0.
      2,3: elim (XUndefined_dec (collapse b1)); intros;
        [ case (Xmerge B2 B'2); simpl; try rewrite a0; auto
        | rewrite Xmatch_elim in H0; auto; inversion H0 ].
      assert_this b1 b2 H0.
      inversion_clear H1.
      case (Xmerge B2 B'2); simpl; try rewrite H2; auto.
      case (Xmerge B2 B'2); simpl; case (collapse b1); try rewrite H2; auto.
    * assert_this x x0 H0. clear H0.
      inversion_clear H1.
      case (Xmerge B2 B'2); simpl; try rewrite H0; auto.
      case (Xmerge B2 B'2); simpl; case (collapse x); try rewrite H0; auto.
  - generalize (IHB2 B'2 H); clear IHB1 IHB2.
    case (Xmerge B2 B'2); simpl; intros; auto.
    1,7: inversion H0.
    6: case (Xmerge B1 B'1); auto.
    1,2,3: elim (XUndefined_dec (collapse x)); intros;
      [ case (Xmerge B1 B'1); simpl; try rewrite H0; auto;
        intros; try case o, o0; try induction p; try induction p0;
          try case (collapse x0); try case (collapse x1);
          try case (collapse b1); try case (collapse b2); auto
      | rewrite Xmatch_elim in H0; auto; inversion H0].
    * revert H0. elim_as o p; elim_as o0 p; intros.
      4: inversion H0.
      2,3: elim (XUndefined_dec (collapse b1)); intros;
      [ case (Xmerge B1 B'1); simpl; try rewrite a0; auto;
        intros; try case o1, o2; try induction p; try induction p0;
          try case (collapse x); try case (collapse x0);
          try case (collapse b2); try case (collapse b3); auto
      | rewrite Xmatch_elim in H0; auto; inversion H0].
      assert_this b1 b2 H0. clear H0.
      inversion_clear H1.
      case (Xmerge B1 B'1); simpl; try rewrite H0; auto;
        intros; try case o1, o2; try induction p; try induction p0;
          try case (collapse x); try case (collapse x0);
          try case (collapse b3); try case (collapse b4); auto.
      case (Xmerge B1 B'1); simpl; try rewrite H0; auto;
        intros; try case o1, o2; try induction p; try induction p0;
          try case (collapse x); try case (collapse x0);
          try case (collapse b1); try case (collapse b3); try case (collapse b4); auto.
    * assert_this x x0 H0. clear H0.
      inversion_clear H1.
      case (Xmerge B1 B'1); simpl; try rewrite H0; auto;
        intros; try case o, o0; try induction p; try induction p0;
          try case (collapse x0); try case (collapse x1); try case (collapse x2);
          try case (collapse b1); try case (collapse b2); auto.
      case (Xmerge B1 B'1); simpl; try rewrite H0; auto;
        intros; try case o, o0; try induction p; try induction p0;
          try case (collapse x); try case (collapse x1); try case (collapse x2);
          try case (collapse b1); try case (collapse b2); auto.
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
simpl. rewrite eqb_refl.
case_eq (Xmerge Bt Bt'); case_eq (Xmerge Be Be'); simpl; auto.
all: intros; try (elim H1; auto; fail); try (elim H2; auto; fail).
Qed.

Ltac eq_dec_elim t1 t2 H := case (eq_dec t1 t2); intro H;
    [rewrite <- eqb_eq in H | rewrite <- eqb_neq in H]; rewrite H;
    [idtac | discriminate].

Lemma Xmerge_inv_Send : forall B1 B2 p e a B,
  Xmerge B1 B2 = XSend p e a B -> exists B1' B2',
  B1 = XSend p e a B1' /\ B2 = XSend p e a B2' /\ Xmerge B1' B2' = B.
Proof.
intros B1 B2.
case B1; case B2; try discriminate.
+ intros. revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec (Xmerge x0 x)); intro.
  rewrite a0; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. rewrite eqb_eq in Ht2t, Ht3t0, Ht4t1.
  rewrite Ht2t, Ht3t0, Ht4t1; intros.
  inversion H; eauto.
+ intros. revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec (Xmerge x0 x)); intro.
  rewrite a0; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. intro; inversion H.
+ intros. revert H. simpl.
  eq_dec_elim t1 t Ht1t.
  case_eq (eqb_label l0 l); intro. 2: discriminate.
  eq_dec_elim t2 t0 Ht2t.
  elim (XUndefined_dec (Xmerge x0 x)); intro.
  rewrite a0; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. intro; inversion H0.
+ intros. exfalso.
  revert H. simpl.
  eq_dec_elim t0 t Ht0t.
  elim_as o p0; elim_as o0 p0; elim_as o1 p0; elim_as o2 p0; try discriminate.
  1,2: eq_dec_elim a2 a0 Ha2a0; prove_this (Xmerge b1 b) Hb1b; try discriminate.
  1: eq_dec_elim a3 a1 Ha3a1; prove_this (Xmerge b2 b0) Hb2b0; try discriminate.
  2,3,6,7,11,12,13,14: prove_this b Hb; try discriminate.
  1,3,4,5,8,9: prove_this b0 Hb0; try discriminate.
  2: prove_this b Hb; try discriminate.
  1: eq_dec_elim a2 a0 Ha2a0; prove_this (Xmerge b1 b) Hb1b; try discriminate.
  2,3,4: eq_dec_elim a1 a0 Ha1a0; prove_this (Xmerge b0 b) Hb0b; try discriminate.
  1: eq_dec_elim a2 a1 Ha2a1; prove_this (Xmerge b1 b0) Hb1b0; try discriminate.
  1: prove_this b1 Hb1; try discriminate.
+ intros. exfalso.
  elim (XUndefined_dec (Xmerge x1 x)); intro H1.
  2: elim (XUndefined_dec (Xmerge x2 x0)); intro H0.
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
  Xmerge B1 B2 = XRecv p x a B -> exists B1' B2',
  B1 = XRecv p x a B1' /\ B2 = XRecv p x a B2' /\ Xmerge B1' B2' = B.
Proof.
intros B1 B2.
case B1; case B2; try discriminate.
+ intros. revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec (Xmerge x0 x)); intro.
  rewrite a0; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. intro; inversion H.
+ intros. revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec (Xmerge x0 x)); intro.
  rewrite a0; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. rewrite eqb_eq in Ht2t, Ht3t0, Ht4t1.
  rewrite Ht2t, Ht3t0, Ht4t1; intros.
  inversion H; eauto.
+ intros. revert H. simpl.
  eq_dec_elim t1 t Ht1t.
  case_eq (eqb_label l0 l); intro. 2: discriminate.
  eq_dec_elim t2 t0 Ht2t.
  elim (XUndefined_dec (Xmerge x0 x)); intro.
  rewrite a0; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. intro; inversion H0.
+ intros. exfalso.
  revert H. simpl.
  eq_dec_elim t0 t Ht0t.
  elim_as o p0; elim_as o0 p0; elim_as o1 p0; elim_as o2 p0; try discriminate.
  1,2: eq_dec_elim a2 a0 Ha2a0; prove_this (Xmerge b1 b) Hb1b; try discriminate.
  1: eq_dec_elim a3 a1 Ha3a1; prove_this (Xmerge b2 b0) Hb2b0; try discriminate.
  2,3,6,7,11,12,13,14: prove_this b Hb; try discriminate.
  1,3,4,5,8,9: prove_this b0 Hb0; try discriminate.
  2: prove_this b Hb; try discriminate.
  1: eq_dec_elim a2 a0 Ha2a0; prove_this (Xmerge b1 b) Hb1b; try discriminate.
  2,3,4: eq_dec_elim a1 a0 Ha1a0; prove_this (Xmerge b0 b) Hb0b; try discriminate.
  1: eq_dec_elim a2 a1 Ha2a1; prove_this (Xmerge b1 b0) Hb1b0; try discriminate.
  1: prove_this b1 Hb1; try discriminate.
+ intros. exfalso.
  elim (XUndefined_dec (Xmerge x1 x)); intro H1.
  2: elim (XUndefined_dec (Xmerge x2 x0)); intro H0.
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
  Xmerge B1 B2 = XSel p l a B -> exists B1' B2',
  B1 = XSel p l a B1' /\ B2 = XSel p l a B2' /\ Xmerge B1' B2' = B.
Proof.
intros B1 B2.
case B1; case B2; try discriminate.
+ intros. revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec (Xmerge x0 x)); intro.
  rewrite a0; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. intro; inversion H.
+ intros. revert H. simpl.
  eq_dec_elim t2 t Ht2t.
  eq_dec_elim t3 t0 Ht3t0.
  eq_dec_elim t4 t1 Ht4t1.
  elim (XUndefined_dec (Xmerge x0 x)); intro.
  rewrite a0; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. intro; inversion H.
+ intros. revert H. simpl.
  eq_dec_elim t1 t Ht1t.
  case_eq (eqb_label l0 l); intro. 2: discriminate.
  eq_dec_elim t2 t0 Ht2t.
  elim (XUndefined_dec (Xmerge x0 x)); intro.
  rewrite a0; discriminate.
  rewrite Xmatch_elim; auto.
  simpl. rewrite eqb_eq in Ht2t, Ht1t; rewrite label_eqb_eq in H.
  rewrite Ht2t, Ht1t, H; intros.
  inversion H0; eauto.
+ intros. exfalso.
  revert H. simpl.
  eq_dec_elim t0 t Ht0t.
  elim_as o p0; elim_as o0 p0; elim_as o1 p0; elim_as o2 p0; try discriminate.
  1,2: eq_dec_elim a2 a0 Ha2a0; prove_this (Xmerge b1 b) Hb1b; try discriminate.
  1: eq_dec_elim a3 a1 Ha3a1; prove_this (Xmerge b2 b0) Hb2b0; try discriminate.
  2,3,6,7,11,12,13,14: prove_this b Hb; try discriminate.
  1,3,4,5,8,9: prove_this b0 Hb0; try discriminate.
  2: prove_this b Hb; try discriminate.
  1: eq_dec_elim a2 a0 Ha2a0; prove_this (Xmerge b1 b) Hb1b; try discriminate.
  2,3,4: eq_dec_elim a1 a0 Ha1a0; prove_this (Xmerge b0 b) Hb0b; try discriminate.
  1: eq_dec_elim a2 a1 Ha2a1; prove_this (Xmerge b1 b0) Hb1b0; try discriminate.
  1: prove_this b1 Hb1; try discriminate.
+ intros. exfalso.
  elim (XUndefined_dec (Xmerge x1 x)); intro H1.
  2: elim (XUndefined_dec (Xmerge x2 x0)); intro H0.
  - revert H. simpl. eq_dec_elim t0 t Ht0t. rewrite H1; discriminate.
  - revert H. simpl. eq_dec_elim t0 t Ht0t. rewrite H0, Xmatch_elim; auto. discriminate.
  - elim (eq_dec t0 t); intro Ht0t.
    rewrite Ht0t, Xmerge_Cond_inv in H; auto. discriminate.
    revert H; simpl. rewrite <- eqb_neq in Ht0t; rewrite Ht0t; discriminate.
+ intros. exfalso.
  revert H. simpl.
  eq_dec_elim t0 t Ht0t; discriminate.
Qed.

Lemma Xmerge_inv_Branching : forall B B' p Bl Br, Xmerge B B' = XBranching p Bl Br ->
  exists Bl' Bl'' Br' Br'', B = XBranching p Bl' Br' /\ B' = XBranching p Bl'' Br''
  /\ (Bl = None -> Bl' = None /\ Bl'' = None)
  /\ (Br = None -> Br' = None /\ Br'' = None)
  /\ (forall a BL, Bl = Some (a,BL) ->
         (Bl' = None -> Bl'' = Some (a,BL)) /\ (Bl'' = None -> Bl' = Some (a,BL))
      /\ (forall a' BL' a'' BL'', Bl' = Some (a',BL') /\ Bl'' = Some (a'',BL'') ->
          a' = a /\ a'' = a /\ Xmerge BL' BL'' = BL))
  /\ (forall a BR, Br = Some (a,BR) ->
         (Br' = None -> Br'' = Some (a,BR)) /\ (Br'' = None -> Br' = Some (a,BR))
      /\ (forall a' BR' a'' BR'', Br' = Some (a',BR') /\ Br'' = Some (a'',BR'') ->
          a' = a /\ a'' = a /\ Xmerge BR' BR'' = BR)).
Proof.
intros B B' P E X HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (case o; case o0); try (case o1; case o2);
  simpl; auto; try (intros; inversion HBB'; fail);
  try (case_eq (p0 =? p); intro Hp0p; simpl; try (rewrite eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (e0 =? e); intro He0e; simpl; try (rewrite eqb_eq in He0e; rewrite He0e));
  try (case_eq (v0 =? v); intro Hv0v; simpl; try (rewrite eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (b2 =? b); intro Hb0b; simpl; try (rewrite eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (r0 =? r); intro HX0X; simpl; try (rewrite eqb_eq in HX0X; rewrite HX0X));
  intros.
all: elim (if_elim _ _ _ _ _ HBB'); intro H0; inversion_clear H0; clear HBB';
  [ try apply andb_prop in H; inversion H;
    try (apply andb_prop in H0; inversion H0) | inversion H1 ].
1,3,4: elim (XUndefined_dec (Xmerge x0 x)); intro HM; 
      [ rewrite HM in H1
      | rewrite Xmatch_elim in H1; auto ]; inversion H1; auto.
1: {
  elim (XUndefined_dec (Xmerge x0 x)); intro HM; 
      [ rewrite HM in H1
      | rewrite Xmatch_elim in H1; auto ]; inversion H1; auto.
}
all: rename H1 into H0; apply eqb_eq in H; clear H2.
all: try induction p as (a, x);
     try induction p0 as (a0, x0);
     try induction p1 as (a1, x1);
     try induction p2 as (a2, x2); revert H0.
+ case_eq (eqb Ann a0 a2);
  [intro Ha0a2; rewrite eqb_eq in Ha0a2
  | intros; inversion H1].
  case_eq (eqb Ann a a1);
  [intro Haa1; rewrite eqb_eq in Haa1; intros | idtac].
  intros; elim (XUndefined_dec (Xmerge x0 x2)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge x x1)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some (a0,x0)), (Some (a2,x2)), (Some (a,x)), (Some (a1,x1)); rewrite H;
  repeat (split; auto); intros; try inversion H5;
    inversion H1; inversion H6; inversion H7; auto.
  2: transitivity a2; auto. 1,2: transitivity a0; auto.
  2: transitivity a1; auto. 1,2: transitivity a; auto.
  case (Xmerge x0 x2); intros; inversion H1.
+ case_eq (eqb Ann a a1);
  [intro Haa1; rewrite eqb_eq in Haa1
  | intros; inversion H1].
  intro; elim (XUndefined_dec (Xmerge x x1)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec x0); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some (a,x)), (Some (a1,x1)), None, (Some (a0,x0)); rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try (inversion H6; inversion H9; auto).
  2: transitivity a1; auto. all: transitivity a; auto.
+ intro; elim (XUndefined_dec x1); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  revert H0. case_eq (eqb Ann a a0);
  [intro Haa0; rewrite eqb_eq in Haa0
  | intros; inversion H1].
  intro; elim (XUndefined_dec (Xmerge x x0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, (Some (a1,x1)), (Some (a,x)), (Some (a0,x0)); rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try (inversion H6; inversion H9; auto).
  2: transitivity a0; auto. all: transitivity a; auto.
+ intro; elim (XUndefined_dec x0); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0;
  exists None, (Some (a0,x0)), None, (Some (a,x)); rewrite H;
  repeat (split; auto); try inversion H0; intros; try inversion H5;
    try (inversion H6; auto).
+ case_eq (eqb Ann a0 a1);
  [intro Ha0a1; rewrite eqb_eq in Ha0a1
  | intros; inversion H1].
  intro; elim (XUndefined_dec (Xmerge x0 x1)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some (a0,x0)), (Some (a1,x1)), (Some (a,x)), None; rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try (inversion H6; inversion H9; auto).
  2: transitivity a1; auto. all: transitivity a0; auto.
+ case_eq (eqb Ann a a0);
  [intro Haa0; rewrite eqb_eq in Haa0
  | intros; inversion H1].
  intro; elim (XUndefined_dec (Xmerge x x0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some (a,x)), (Some (a0,x0)), None, None; rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try (inversion H6; inversion H9; auto).
  2: transitivity a0; auto. all: transitivity a; auto.
+ intro; elim (XUndefined_dec x0); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, (Some (a0,x0)), (Some (a,x)), None; rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try (inversion H6; inversion H9; auto).
+ intro; elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, (Some (a,x)), None, None; rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try (inversion H6; auto).
+ intro; elim (XUndefined_dec x0); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  revert H0.
  case_eq (eqb Ann a a1);
  [intro Haa1; rewrite eqb_eq in Haa1
  | intros; inversion H1].
  intro; elim (XUndefined_dec (Xmerge x x1)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some (a0,x0)), None, (Some (a,x)), (Some (a1,x1)); rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try (inversion H6; inversion H9; auto).
  2: transitivity a1; auto. all: transitivity a; auto.
+ intro; elim (XUndefined_dec x); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec x0); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some (a,x)), None, None, (Some (a0,x0)); rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try (inversion H6; inversion H9; auto).
+ case_eq (eqb Ann a a0);
  [intro Haa0; rewrite eqb_eq in Haa0
  | intros; inversion H1].
  intro; elim (XUndefined_dec (Xmerge x x0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, None, (Some (a,x)), (Some (a0,x0)); rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try (inversion H6; inversion H9; auto).
  2: transitivity a0; auto. all: transitivity a; auto.
+ intro; elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, None, None, (Some (a,x)); rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try (inversion H6; auto).
+ intro; elim (XUndefined_dec x0); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some (a0,x0)), None, (Some (a,x)), None; rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try (inversion H6; inversion H9; auto).
+ intro; elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some (a,x)), None, None, None; rewrite H;
  repeat (split; auto); try inversion H1; intros; try inversion H5;
    try (inversion H9; auto).
+ intro; elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
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

Local Ltac Ann_elim H a a' H' H'' := 
    revert H; case_eq (eqb Ann a a');
    [intro H'; rewrite eqb_eq in H'; intros
    | intros; elim (inject_not_undefined _ H'')].

Local Ltac Undef_elim x H' H :=
    elim (XUndefined_dec x); intro H';
    [ rewrite H' in H; elim (inject_not_undefined _ H)
    | rewrite Xmatch_elim in H; auto].

Local Ltac indu_kill H b H' o o' a a' :=
    revert H; case b; intros; inversion H;
    clear H'; induction o, o'; try induction a; try induction a'; inversion H.

Lemma Xmerge_inv_inject : forall B1 B2 B, Xmerge B1 B2 = inject B ->
  exists B', B1 = inject B'.
Proof.
intros. symmetry in H.
revert B1 B2 B H.
induction B1 using XBehaviour_ind'; induction B2 using XBehaviour_ind';
  simpl; intros;
  try (elim (inject_not_undefined _ H); fail);
  try (elim (inject_not_undefined _ H1); fail).
+ exists (End _); auto.
+ case (eq_dec p p0); intro Hpp0.
  rewrite <- eqb_eq in Hpp0; rewrite Hpp0 in H; simpl in H.
  case (eq_dec e e0); intro Hee0.
  rewrite <- eqb_eq in Hee0; rewrite Hee0 in H; simpl in H.
  clear Hpp0 Hee0.
  2: rewrite <- eqb_neq in Hee0; rewrite Hee0 in H; simpl in H; elim (inject_not_undefined _ H).
  2: rewrite <- eqb_neq in Hpp0; rewrite Hpp0 in H; simpl in H; elim (inject_not_undefined _ H).
  Ann_elim H a a0 Haa0 H0.
  Undef_elim (Xmerge B1 B2) H' H.
  revert H. case B; intros; inversion H.
  2: induction o, o0; try induction a1; try induction p1; inversion H1.
  elim IHB1 with B2 b; auto. intros.
  exists (p!e@!a;x); repeat split; simpl.
  rewrite H0; auto.
+ case (eq_dec p p0); intro Hpp0.
  rewrite <- eqb_eq in Hpp0; rewrite Hpp0 in H; simpl in H.
  case (eq_dec v v0); intro Hvv0.
  rewrite <- eqb_eq in Hvv0; rewrite Hvv0 in H; simpl in H.
  clear Hpp0 Hvv0.
  2: rewrite <- eqb_neq in Hvv0; rewrite Hvv0 in H; simpl in H; elim (inject_not_undefined _ H).
  2: rewrite <- eqb_neq in Hpp0; rewrite Hpp0 in H; simpl in H; elim (inject_not_undefined _ H).
  Ann_elim H a a0 Haa0 H0.
  Undef_elim (Xmerge B1 B2) H' H.
  revert H. case B; intros; inversion H.
  2: induction o, o0; try induction a1; try induction p1; inversion H1.
  elim IHB1 with B2 b; auto. intros.
  exists (p ? v@?a;x); repeat split; simpl.
  rewrite H0; auto.
+ case (eq_dec p p0); intro Hpp0.
  rewrite <- eqb_eq in Hpp0; rewrite Hpp0 in H; simpl in H.
  case_eq (eqb_label l l0); intro Hll0; rewrite Hll0 in H.
  clear Hpp0 Hll0.
  2: elim (inject_not_undefined _ H).
  2: rewrite <- eqb_neq in Hpp0; rewrite Hpp0 in H; simpl in H; elim (inject_not_undefined _ H).
  Ann_elim H a a0 Haa0 H0.
  Undef_elim (Xmerge B1 B2) H' H.
  revert H. case B; intros; inversion H.
  2: induction o, o0; try induction a1; try induction p1; inversion H1.
  elim IHB1 with B2 b; auto. intros.
  exists (p(+)l@+a;x); repeat split; simpl.
  rewrite H0; auto.
+ case (eq_dec p p0); intro Hpp0.
  rewrite <- eqb_eq in Hpp0; rewrite Hpp0 in H3; simpl in H3.
  clear Hpp0.
  2: rewrite <- eqb_neq in Hpp0; rewrite Hpp0 in H3; simpl in H3; elim (inject_not_undefined _ H3).
  induction mB, mB', mB0, mB'0.
  - induction a as (a,x), p1 as (a0,x0), p2 as (a1,x1), p3 as (a2,x2).
    Ann_elim H3 a a1 Haa1 H4.
    Undef_elim (Xmerge x x1) H' H3.
    Ann_elim H3 a0 a2 Ha0a2 H4.
    Undef_elim (Xmerge x0 x2) H'' H3.
    indu_kill H3 B H5 o o0 a3 p1.
    elim H with a x x1 b; auto. intros.
    elim H0 with a0 x0 x2 b0; auto. intros.
    exists (p & Some (a,x3) // Some (a0,x4)); simpl.
    rewrite H4, H10; auto.
  - induction a as (a,x), p1 as (a0,x0), p2 as (a1,x1).
    Ann_elim H3 a a1 Haa1 H4.
    Undef_elim (Xmerge x x1) H' H3.
    Undef_elim x0 H'' H3.
    indu_kill H3 B H5 o o0 a2 p1.
    elim H with a x x1 b; auto. intros.
    exists (p & Some (a,x2) // Some (a0,b0)); simpl.
    rewrite H4; auto.
  - induction a as (a,x), p1 as (a0,x0), p2 as (a1,x1).
    Undef_elim x H' H3.
    Ann_elim H3 a0 a1 Ha0a1 H4.
    Undef_elim (Xmerge x0 x1) H'' H3.
    indu_kill H3 B H5 o o0 a2 p1.
    elim H0 with a0 x0 x1 b0; auto. intros.
    exists (p & Some (a,b) // Some (a0,x2)); simpl.
    rewrite H4; auto.
  - induction a as (a,x), p1 as (a0,x0).
    Undef_elim x H' H3.
    Undef_elim x0 H'' H3.
    indu_kill H3 B H5 o o0 a1 p1.
    exists (p & Some (a,b) // Some (a0,b0)); auto.
  - induction a as (a,x), p1 as (a0,x0), p2 as (a1,x1).
    Ann_elim H3 a a0 Haa0 H4.
    Undef_elim (Xmerge x x0) H' H3.
    Undef_elim x1 H'' H3.
    indu_kill H3 B H5 o o0 a2 p1.
    elim H with a x x0 b; auto. intros.
    exists (p & Some (a,x2) // None); simpl.
    rewrite H4; auto.
  - induction a as (a,x), p1 as (a0,x0).
    Ann_elim H3 a a0 Haa0 H4.
    Undef_elim (Xmerge x x0) H' H3.
    indu_kill H3 B H5 o o0 p1 a1.
    elim H with a x x0 b; auto. intros.
    exists (p & Some (a,x1) // None); simpl.
    rewrite H4; auto.
  - induction a as (a,x), p1 as (a0,x0).
    Undef_elim x H' H3.
    Undef_elim x0 H'' H3.
    indu_kill H3 B H5 o o0 p1 a1.
    exists (p & Some (a,b0) // None); auto.
  - induction a as (a,x).
    Undef_elim x H' H3.
    indu_kill H3 B H5 o o0 a0 p1.
    exists (p & Some (a,b) // None); auto.
  - induction p1 as (a0,x0), p2 as (a1,x1), p3 as (a2,x2).
    Undef_elim x1 H' H3.
    Ann_elim H3 a0 a2 Ha0a2 H4.
    Undef_elim (Xmerge x0 x2) H'' H3.
    indu_kill H3 B H5 o o0 p1 a.
    elim H0 with a0 x0 x2 b; auto. intros.
    exists (p & None // Some (a0,x)); simpl.
    rewrite H4; auto.
  - induction p1 as (a0,x0), p2 as (a1,x1).
    Undef_elim x1 H' H3.
    Undef_elim x0 H'' H3.
    indu_kill H3 B H5 o o0 p1 a.
    exists (p & None // Some (a0,b)); auto.
  - induction p1 as (a0,x0), p2 as (a1,x1).
    Ann_elim H3 a0 a1 Ha0a1 H4.
    Undef_elim (Xmerge x0 x1) H' H3.
    indu_kill H3 B H5 o o0 p1 a.
    elim H0 with a0 x0 x1 b; auto. intros.
    exists (p & None // Some (a0,x)); simpl.
    rewrite H4; auto.
  - induction p1 as (a0,x0).
    Undef_elim x0 H' H3.
    indu_kill H3 B H5 o o0 p1 a.
    exists (p & None // Some (a0,b)); auto.
  - induction p1 as (a0,x0), p2 as (a1,x1).
    Undef_elim x0 H' H3.
    Undef_elim x1 H'' H3.
    indu_kill H3 B H5 o o0 p1 a.
    exists (p & None // None); auto.
  - induction p1 as (a0,x0).
    Undef_elim x0 H' H3.
    indu_kill H3 B H5 o o0 p1 a.
    exists (p & None // None); auto.
  - induction p1 as (a0,x0).
    Undef_elim x0 H' H3.
    indu_kill H3 B H5 o o0 p1 a.
    exists (p & None // None); auto.
  - indu_kill H3 B H5 o o0 p1 a.
    exists (p & None // None); auto.
+ case (eq_dec b b0); intro Hbb0.
  rewrite <- eqb_eq in Hbb0; rewrite Hbb0 in H; simpl in H.
  clear Hbb0.
  2: rewrite <- eqb_neq in Hbb0; rewrite Hbb0 in H; simpl in H; elim (inject_not_undefined _ H).
  clear IHB2_1 IHB2_2.
  elim (collapse_char' (Xmerge B1_1 B2_1)); intros.
  elim (collapse_char' (Xmerge B1_2 B2_2)); intros.
  destroy a; destroy a0. rename x into B1, x0 into B2, a into HB1, a0 into HB2.
  elim IHB1_1 with B2_1 B1; auto. intros.
  elim IHB1_2 with B2_2 B2; auto. intros.
  clear IHB1_1 IHB1_2.
  1: exists (If b Then x Else x0); rewrite H1, H0; auto.
  all: assert (collapse (XCond b (Xmerge B1_1 B2_1) (Xmerge B1_2 B2_2)) = XUndefined).
  1,3: simpl; rewrite b1; auto.
  1: case collapse; auto.
  clear a. all: clear b1.
  - assert (inject B = collapse (XCond b (Xmerge B1_1 B2_1) (Xmerge B1_2 B2_2))).
    rewrite <- collapse_inject, H. case Xmerge; case Xmerge; simpl; auto.
    all: intros.
    4: case o, o0; try induction p as (a,x); try induction p0 as (a0,x0); auto. 1,2,3,4,5,6,7: case (collapse x); auto; case (collapse x0); auto.
    elim (inject_not_undefined B). etransitivity; eauto.
  - assert (inject B = collapse (XCond b (Xmerge B1_1 B2_1) (Xmerge B1_2 B2_2))).
    rewrite <- collapse_inject, H. case Xmerge; case Xmerge; simpl; auto.
    all: intros.
    4: case o, o0; try induction p as (a,x); try induction p0 as (a0,x0); auto. 1,2,3,4,5,6,7: case (collapse x); auto; case (collapse x0); auto.
    elim (inject_not_undefined B). etransitivity; eauto.
+ exists (Call _ X); auto.
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
elim (Xmerge_inv B B' (Call _ X)); auto.
intros. destroy H0.
elim (merge_inv_Call _ _ _ H0); intros.
rewrite H1, H3; auto.
Qed.

Lemma Xmerge_inv_Call : forall B B' X,
  Xmerge B B' = XCall X -> B = XCall X /\ B' = XCall X.
Proof.
intros.
elim (Xmerge_inv B B' (Call _ X)); auto.
intros. destroy H0.
elim (merge_inv_Call _ _ _ H0); intros.
rewrite H1, H2, H3, H4; auto.
Qed.

Lemma Xmerge_inv_End : forall B B',
  Xmerge B B' = XEnd -> B = XEnd /\ B' = XEnd.
Proof.
intros.
elim (Xmerge_inv B B' (End _)); auto.
intros. destroy H0.
elim (merge_inv_End _ _ H0); intros.
rewrite H1, H2, H3, H4; auto.
Qed.

Lemma Xmerge_inv_Cond : forall B B' b Be Bt, Xmerge B B' = XCond b Be Bt ->
  exists Be' Be'' Bt' Bt'', B = XCond b Be' Bt' /\ B' = XCond b Be'' Bt''
    /\ Xmerge Be' Be'' = Be /\ Xmerge Bt' Bt'' = Bt.
Proof.
intros B B' P E X HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (elim_as o p; elim_as o0 p); try (elim_as o1 p; elim_as o2 p);
  simpl; auto; try (intros; inversion HBB'; fail);
  try (case_eq (p0 =? p); intro Hp0p; simpl; try (rewrite eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (e0 =? e); intro He0e; simpl; try (rewrite eqb_eq in He0e; rewrite He0e));
  try (case_eq (v0 =? v); intro Hv0v; simpl; try (rewrite eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (b2 =? b); intro Hb0b; simpl; try (rewrite eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (r0 =? r); intro HX0X; simpl; try (rewrite eqb_eq in HX0X; rewrite HX0X));
  intros.
all: elim (if_elim _ _ _ _ _ HBB'); intro H0; inversion_clear H0; clear HBB';
  [ try apply andb_prop in H; destroy H; try apply andb_prop in H0; destroy H0 | inversion H1 ].
1,2,3: elim (XUndefined_dec (Xmerge x0 x)); intro HM;
  [ rewrite HM in H1
  | rewrite Xmatch_elim in H1; auto ]; inversion H1.
1: inversion H0.
all: rename H1 into H8; revert H8.
all: repeat rewrite inject_match; intros.
1,2: revert H8; case_eq (eqb Ann a1 a);
  [intro Ha1a; rewrite eqb_eq in Ha1a; intros
  | intros; inversion H8].
3,4,7,8,12,13,14,15: intros; elim (XUndefined_dec b); intro HT1;
  [ rewrite HT1 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
3: revert H8; case_eq (eqb Ann a1 a0);
  [intro Ha1a0; rewrite eqb_eq in Ha1a0; intros
  | intros; inversion H8].
11,12,15: revert H8; case_eq (eqb Ann a0 a);
  [intro Ha0a; rewrite eqb_eq in Ha0a; intros
  | intros; inversion H8].
1,2: elim (XUndefined_dec (Xmerge b1 b)); intro HT2;
  [ rewrite HT2 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
2,4,5,8,14,15: intros; elim (XUndefined_dec b0); intro HT3;
  [ rewrite HT3 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
7: intros; elim (XUndefined_dec b); intro HT1;
  [ rewrite HT1 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
13,14,15: elim (XUndefined_dec (Xmerge b0 b)); intro HT2;
  [ rewrite HT2 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
all: try (inversion H8; fail).
all: revert H8.
+ case_eq (eqb Ann a2 a0);
  [intro Ha2a0; intros; rewrite eqb_eq in Ha2a0
  | intros; inversion H8].
  elim (XUndefined_dec (Xmerge b2 b0)); intro HT3;
  [ rewrite HT3 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
  inversion H8.
+ case_eq (eqb Ann a1 a);
  [intro Ha1a; rewrite eqb_eq in Ha1a
  | intros; inversion H8]; intros.
  elim (XUndefined_dec (Xmerge b1 b)); intro HT4;
  [ rewrite HT4 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
  inversion H8.
+ intros.
  elim (XUndefined_dec (Xmerge b1 b0)); intro HT4;
  [ rewrite HT4 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
  inversion H8.
+ intros.
  elim (XUndefined_dec b1); intro HT4;
  [ rewrite HT4 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
  inversion H8.
+ intros.
  elim (XUndefined_dec (Xmerge x1 x)); intro HM.
  rewrite HM in H8; inversion H8.
  elim (XUndefined_dec (Xmerge x2 x0)); intro HM'.
  rewrite HM', Xmatch_elim in H8; auto; inversion H8.
  exists x1, x, x2, x0.
  revert HM HM' H8.
  rewrite eqb_eq in H; rewrite H.
  case (Xmerge x1 x); case (Xmerge x2 x0); intros;
  inversion H8; auto.
Qed.

End Merge.

Section Associativity.

(** Associativity of merge: the nightmare proof. *)

Local Ltac solve B B' H := try (elim (XUndefined_dec (Xmerge B B')); intro H;
  [rewrite H| rewrite Xmatch_elim]; auto).

Local Ltac solve' B H := try (elim (XUndefined_dec B); intro H;
  [rewrite H| rewrite Xmatch_elim]; auto).

Lemma Xmerge_Branching_elim : forall p mBl mBr q mBl' mBr',
  {Xmerge (XBranching p mBl mBr) (XBranching q mBl' mBr') = XUndefined } +
  {p = q /\ exists mB mB', Xmerge (XBranching p mBl mBr) (XBranching q mBl' mBr') = XBranching p mB mB'}.
Proof.
intros.
simpl. case (eq_dec p q); intro Hpq; simpl; auto.
1: rewrite <- eqb_eq in Hpq; rewrite Hpq; rewrite eqb_eq in Hpq.
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
Lemma Xmerge_assoc : forall B B' B'',
  Xmerge (Xmerge B B') B'' = Xmerge B (Xmerge B' B'').
Proof.
induction B using XBehaviour_ind';
induction B' using XBehaviour_ind';
induction B'' using XBehaviour_ind'; simpl; auto.
(* 84 cases *)
(* Call *)
6,19,32,45,58,71,77,78,79,80,81,82,83,84:
  case (eq_dec X X0); intro HXX0;
  [rewrite <- eqb_eq in HXX0 | rewrite <- eqb_neq in HXX0];
  rewrite HXX0; auto; simpl.
6,7:
  case (eq_dec X0 X1); intro HX0X1;
  [rewrite <- eqb_eq in HX0X1 | rewrite <- eqb_neq in HX0X1];
  rewrite HX0X1; auto; simpl.
6: rewrite (eqb_trans _ _ _ _ HXX0 HX0X1); auto.
7: rewrite (eqb_ntrans _ _ _ _ HXX0 HX0X1); auto.
6,7: rewrite HXX0; auto.
(* 70 cases left *)
(* Pid *)
1,2,3,6,7,8,9,10,11,12,13,19,20,21,22,23,24,25,26,32,33,34,35,36,37,38,39,54,55,56,66,67,68:
  case (eq_dec p p0); intro Hpp0;
  [rewrite <- eqb_eq in Hpp0 | rewrite <- eqb_neq in Hpp0];
  rewrite Hpp0; auto; simpl.
6,16,26,39,40,43,44,47,48:
  case (eq_dec p0 p1); intro Hp0p1;
  [rewrite <- eqb_eq in Hp0p1 | rewrite <- eqb_neq in Hp0p1];
  rewrite Hp0p1; auto; simpl.
1,4,5,11,13,15,16,17,18,19,20,37,40:
  case (eq_dec e e0); intro Hee0;
  [rewrite <- eqb_eq in Hee0 | rewrite <- eqb_neq in Hee0];
  rewrite Hee0; auto; simpl.
15,20,23,24,25,26,27,28,29,30,31,40,42:
  case (eq_dec v v0); intro Hvv0;
  [rewrite <- eqb_eq in Hvv0 | rewrite <- eqb_neq in Hvv0];
  rewrite Hvv0; auto; simpl.
29,33,34,35,36,37,38,39,40,41,42,43,44:
  case_eq (eqb_label l l0); intro Hll0; auto; simpl.
1,2,3,7,8,9,10,11,12,13,14,15,18,19,20,22,23,24,25,26,27,28,29,32,33,34,35,37,38,39,40,41,42:
  case (eq_dec a a0); intro Haa0;
  [rewrite <- eqb_eq in Haa0 | rewrite <- eqb_neq in Haa0];
  rewrite Haa0; auto; simpl.
all: try (solve B B' HBB'; fail). (* 21 cases *)

2,3,7,8,12,13,16,21,24,36,37,38:
  case (eq_dec p0 p1); intro Hp0p1;
  [rewrite <- eqb_eq in Hp0p1 | rewrite <- eqb_neq in Hp0p1];
  rewrite Hp0p1; auto; simpl.
2,4,11,31:
  case (eq_dec e0 e1); intro He0e1;
  [rewrite <- eqb_eq in He0e1 | rewrite <- eqb_neq in He0e1];
  rewrite He0e1; auto; simpl.
8,10,14,33:
  case (eq_dec v0 v1); intro Hv0v1;
  [rewrite <- eqb_eq in Hv0v1 | rewrite <- eqb_neq in Hv0v1];
  rewrite Hv0v1; auto; simpl.
14,16,17,35:
  case_eq (eqb_label l0 l1); intro Hl0l1; auto; simpl.
2,4,5,6,8,10,11,12,14,16,17,18,31,32,33,34,35,36:
  case (eq_dec a0 a1); intro Ha0a1;
  [rewrite <- eqb_eq in Ha0a1 | rewrite <- eqb_neq in Ha0a1];
  rewrite Ha0a1; auto; simpl.
all: try (solve B' B'' HBB'; fail). (* 15 cases *)

(* 52 cases left *)
1: { elim (XUndefined_dec (Xmerge B B')); intro HBB';
  [rewrite HBB' | rewrite Xmatch_elim; auto].
  all: elim (XUndefined_dec (Xmerge B' B'')); intro HB'B'';
    [rewrite HB'B'' | rewrite Xmatch_elim; auto]; simpl; auto.
  - rewrite Hpp0, Hee0, Haa0, <- IHB, HBB'; auto.
  - rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1), (eqb_trans _ _ _ _ Hee0 He0e1), (eqb_trans _ _ _ _ Haa0 Ha0a1).
    rewrite IHB, HB'B'', Xmerge_comm; simpl; auto.
  - rewrite Hpp0, Hee0, Haa0.
    rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1), (eqb_trans _ _ _ _ Hee0 He0e1), (eqb_trans _ _ _ _ Haa0 Ha0a1).
    rewrite IHB; auto.
}
1: { elim (XUndefined_dec (Xmerge B B')); intro HBB';
  [rewrite HBB' | rewrite Xmatch_elim; auto]; simpl; auto.
  rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1), (eqb_trans _ _ _ _ Hee0 He0e1), (eqb_ntrans _ _ _ _ Haa0 Ha0a1).
  simpl; auto.
}
1: elim (XUndefined_dec (Xmerge B' B'')); intro HB'B'';
   [rewrite HB'B'' | rewrite Xmatch_elim; auto]; simpl; auto;
   rewrite Hpp0, Hee0, Haa0; auto.
1: elim (XUndefined_dec (Xmerge B' B'')); intro HB'B'';
   [rewrite HB'B'' | rewrite Xmatch_elim; auto]; simpl; auto;
   rewrite Hpp0, Hee0; auto.
1,6,11: elim (XUndefined_dec (Xmerge B' B'')); intro HB'B'';
   [rewrite HB'B'' | rewrite Xmatch_elim; auto]; simpl; auto;
   rewrite Hpp0; auto.
1: { elim (XUndefined_dec (Xmerge B B')); intro HBB';
  [rewrite HBB' | rewrite Xmatch_elim; auto].
  all: elim (XUndefined_dec (Xmerge B' B'')); intro HB'B'';
    [rewrite HB'B'' | rewrite Xmatch_elim; auto]; simpl; auto.
  - rewrite Hpp0, Hvv0, Haa0, <- IHB, HBB'; auto.
  - rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1), (eqb_trans _ _ _ _ Hvv0 Hv0v1), (eqb_trans _ _ _ _ Haa0 Ha0a1).
    rewrite IHB, HB'B'', Xmerge_comm; simpl; auto.
  - rewrite Hpp0, Hvv0, Haa0.
    rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1), (eqb_trans _ _ _ _ Hvv0 Hv0v1), (eqb_trans _ _ _ _ Haa0 Ha0a1).
    rewrite IHB; auto.
}
1: { elim (XUndefined_dec (Xmerge B B')); intro HBB';
  [rewrite HBB' | rewrite Xmatch_elim; auto]; simpl; auto.
  rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1), (eqb_trans _ _ _ _ Hvv0 Hv0v1), (eqb_ntrans _ _ _ _ Haa0 Ha0a1).
  simpl; auto.
}
1: { elim (XUndefined_dec (Xmerge B' B'')); intro HB'B'';
  [rewrite HB'B'' | rewrite Xmatch_elim; auto]; simpl; auto.
  rewrite Hpp0, Hvv0, Haa0; auto.
}
1: { elim (XUndefined_dec (Xmerge B' B'')); intro HB'B'';
  [rewrite HB'B'' | rewrite Xmatch_elim; auto]; simpl; auto.
  rewrite Hpp0, Hvv0; auto.
}
1: { elim (XUndefined_dec (Xmerge B B')); intro HBB';
  [rewrite HBB' | rewrite Xmatch_elim; auto].
  all: elim (XUndefined_dec (Xmerge B' B'')); intro HB'B'';
    [rewrite HB'B'' | rewrite Xmatch_elim; auto]; simpl; auto.
  - rewrite Hpp0, Hll0, Haa0, <- IHB, HBB'; auto.
  - rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1), (eqb_trans _ _ _ _ Haa0 Ha0a1).
    rewrite (label_eqb_trans _ _ _ Hll0 Hl0l1).
    rewrite IHB, HB'B'', Xmerge_comm; simpl; auto.
  - rewrite Hpp0, Hll0, Haa0.
    rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1), (eqb_trans _ _ _ _ Haa0 Ha0a1).
    rewrite (label_eqb_trans _ _ _ Hll0 Hl0l1).
    rewrite IHB; auto.
}
1: { elim (XUndefined_dec (Xmerge B B')); intro HBB';
  [rewrite HBB' | rewrite Xmatch_elim; auto]; simpl; auto.
  rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1), (eqb_ntrans _ _ _ _ Haa0 Ha0a1).
  rewrite (label_eqb_trans _ _ _ Hll0 Hl0l1).
  simpl; auto.
}
1: { elim (XUndefined_dec (Xmerge B' B'')); intro HB'B'';
  [rewrite HB'B'' | rewrite Xmatch_elim; auto]; simpl; auto.
  rewrite Hpp0, Hll0, Haa0; auto.
}
1: { elim (XUndefined_dec (Xmerge B' B'')); intro HB'B'';
  [rewrite HB'B'' | rewrite Xmatch_elim; auto]; simpl; auto.
  rewrite Hpp0, Hll0; auto.
}
1: { elim (XUndefined_dec (Xmerge B B')); intro HBB';
  [rewrite HBB' | rewrite Xmatch_elim; auto]; simpl; auto.
  rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1), (eqb_ntrans _ _ _ _ Hee0 He0e1).
  simpl; auto.
}
1,3,5: elim (XUndefined_dec (Xmerge B B')); intro HBB';
  [rewrite HBB' | rewrite Xmatch_elim; auto]; simpl; auto;
  unfold eq_dec; rewrite (eqb_ntrans _ _ _ _ Hpp0 Hp0p1); auto.
1: { elim (XUndefined_dec (Xmerge B B')); intro HBB';
  [rewrite HBB' | rewrite Xmatch_elim; auto]; simpl; auto.
  rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1), (eqb_ntrans _ _ _ _ Hvv0 Hv0v1).
  simpl; auto.
}
1: { elim (XUndefined_dec (Xmerge B B')); intro HBB';
  [rewrite HBB' | rewrite Xmatch_elim; auto]; simpl; auto.
  rewrite (eqb_trans _ _ _ _ Hpp0 Hp0p1).
  rewrite (label_eqb_ntrans _ _ _ Hll0 Hl0l1).
  simpl; auto.
}
1: {
  case (eq_dec e e0); intro Hee0;
  [rewrite <- eqb_eq in Hee0 | rewrite <- eqb_neq in Hee0];
  rewrite Hee0; auto; simpl.
  case (eq_dec a a0); intro Haa0;
  [rewrite <- eqb_eq in Haa0 | rewrite <- eqb_neq in Haa0];
  rewrite Haa0; auto; simpl.
  solve B' B'' HB'B''.
}
1: {
  case (eq_dec v v0); intro Hvv0;
  [rewrite <- eqb_eq in Hvv0 | rewrite <- eqb_neq in Hvv0];
  rewrite Hvv0; auto; simpl.
  case (eq_dec a a0); intro Haa0;
  [rewrite <- eqb_eq in Haa0 | rewrite <- eqb_neq in Haa0];
  rewrite Haa0; auto; simpl.
  solve B' B'' HB'B''.
}
1: {
  case_eq (eqb_label l l0); intro Hll0; auto; simpl.
  case (eq_dec a a0); intro Haa0;
  [rewrite <- eqb_eq in Haa0 | rewrite <- eqb_neq in Haa0];
  rewrite Haa0; auto; simpl.
  solve B' B'' HB'B''.
}

(* 28 cases left *)
(* Cond *)
2,4,6,8,17,28:
  case (eq_dec b b0); intro Hbb0;
  [rewrite <- eqb_eq in Hbb0 | rewrite <- eqb_neq in Hbb0];
  rewrite Hbb0; auto; simpl;
  case (Xmerge B'1 B''1); case (Xmerge B'2 B''2); auto.
14,15,16,17,18,20,21:
  case (eq_dec b b0); intro Hbb0;
  [rewrite <- eqb_eq in Hbb0 | rewrite <- eqb_neq in Hbb0];
  rewrite Hbb0; auto; simpl;
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
    apply eqb_neq; auto.
  - rewrite Hb0b1.
    elim (XUndefined_dec (Xmerge B'1 B''1)); intro H1'.
    rewrite Xmerge_Cond_2; auto.
    elim (XUndefined_dec (Xmerge B'2 B''2)); intro H2'.
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

End Associativity.

End SP_Merge.
