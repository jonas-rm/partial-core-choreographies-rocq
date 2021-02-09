Require Export CC.
Require Export SP.

Local Open Scope nat_scope.

Module EPPBase (P X V E B R:DecType) (Ev:Eval E X V V) (BEv:Eval B X V Bool).

Module PR := DecProd R P.

Module Export CCBase := CCBase P X V E B R Ev BEv.
Module Export SP_EPP := SPBase P X V E B PR Ev BEv.

Ltac Peq := unfold Pid_dec; rewrite Pdec.eqb_refl; simpl.
Ltac Eeq := unfold Expr_dec; rewrite Edec.eqb_refl; simpl.
Ltac Beq := unfold BExpr_dec; rewrite Bdec.eqb_refl; simpl.
Ltac Veq := unfold Var_dec; rewrite Xdec.eqb_refl; simpl.
Ltac Xeq := unfold RecVar_dec; rewrite Rdec.eqb_refl; simpl.

Ltac Pneq H := rewrite <- Pdec.eqb_neq in H; rewrite H.

Ltac sup := unfold set_union_pid; rewrite set_union_iff; auto.

(*
Ltac Pid_dec_rewrite p q Hpq :=
  try rewrite Pdec.eqb_refl;
  case_eq (Pid_dec p q); [
    auto; rewrite (Pdec.eqb_eq p q); intro Hpq; try rewrite Hpq; auto
    |
    auto; rewrite (Pdec.eqb_neq p q); intro Hpq; try rewrite Hpq; auto
  ].

Ltac NotIn_from_neq_1 H :=
  simpl; intro H; inversion H; auto.

Ltac assert_NotIn_from_neq_1 x y H :=
  assert (~ In x (y :: nil)); [NotIn_from_neq_1 H | ].

Ltac NotIn_from_neq_2 x y z H H' :=
  simpl; intro H; inversion H as [H' | H']; inversion H'; auto.

Ltac assert_NotIn_from_neq_2 x y z H H' :=
  assert (~ In x (y :: z :: nil)); [NotIn_from_neq_2 x y z H H' | ].
*)

Section EPP.

(** First step: returns an XBehaviour, possibly with XUndefined subcomponents. *)
Fixpoint bproj (Defs:DefSet) (C:Choreography) (r:Pid) : XBehaviour :=
match C with
| CCBase.End                => XEnd
| p#e --> q$x;; C'          => if Pid_dec p r
                               then XSend q e (bproj Defs C' r)
                               else if Pid_dec q r
                                    then XRecv p x (bproj Defs C' r)
                                    else bproj Defs C' r
| p --> q[left];; C'        => if Pid_dec p r
                               then XSel q left (bproj Defs C' r)
                               else if Pid_dec q r
                                    then XBranching p (Some (bproj Defs C' r)) None
                                    else bproj Defs C' r
| p --> q[right];; C'       => if Pid_dec p r
                               then XSel q right (bproj Defs C' r)
                               else if Pid_dec q r
                                    then XBranching p None (Some (bproj Defs C' r))
                                    else bproj Defs C' r
| If p ?? b Then C1 Else C2 => if Pid_dec p r
                               then XCond b (bproj Defs C1 r) (bproj Defs C2 r)
                               else Xmerge (bproj Defs C1 r) (bproj Defs C2 r)
| CCBase.Call X             => if In_dec P.eq_dec r (fst (Defs X))
                               then XCall (X,r)
                               else XEnd
| RT_Call X ps C'           => if In_dec P.eq_dec r ps
                               then XCall (X,r)
                               else bproj Defs C' r
end.

(** Second step: collapse all undefined behaviours. *)
Definition epp_list (Defs:DefSet) (C:Choreography) (ps:list Pid) : list (Pid * XBehaviour) :=
  map (fun p => (p, collapse (bproj Defs C p))) ps.

(** Definitions of projectability at all different levels. *)
Definition projectable_C Defs ps C :=
  Forall (fun X => snd X <> XUndefined) (epp_list Defs C ps).

Definition projectable_D Xs Defs :=
  Forall (fun X => projectable_C Defs (fst (Defs X)) (snd (Defs X)) ) Xs.

Definition projectable Xs ps P :=
  projectable_C (Procedures P) ps (Main P) /\
  projectable_D Xs (Procedures P) /\
  (forall p, In p (CCC_pn (Main P) (fun _ => nil)) -> In p ps) /\
  (forall p X, In X Xs -> In p (fst (Procedures P X)) -> In p ps) /\
  (forall p X, In X Xs -> In p (CCC_pn (snd (Procedures P X)) (fun _ => nil)) -> In p ps).

(** Not decidable, but in practice easy to compute. 
  Maybe we want to compute ps from Xs? *)
Definition Projectable P := exists Xs ps,
  projectable Xs ps P /\ Program_WF Xs P.

(** Now we can define EPP, again in a layered manner.
  Definitions are interactive because of the absurd cases. *)
Definition epp_C Defs ps C : projectable_C Defs ps C -> Network.
Proof.
intros; intro p.
elim (In_dec P.eq_dec p ps); intro Hp.
2: apply End.
elim (collapse_char' (bproj Defs C p)); intro.
1: inversion_clear a. apply x.
exfalso.
red in H. rewrite Forall_forall in H.
apply (H (p,collapse (bproj Defs C p))); auto.
unfold epp_list.
apply in_map_iff. exists p; auto.
Defined.

Definition epp_D Xs Defs : projectable_D Xs Defs -> DefSetB.
Proof.
intros; intro.
case_eq X; intros R p HX.
elim (In_dec R.eq_dec R Xs).
2: intros; apply End.
elim (In_dec P.eq_dec p (fst (Defs R))).
2: intros; apply End.
elim (collapse_char' (bproj Defs (snd (Defs R)) p)); intros.
induction a. apply x.
exfalso.
red in H. rewrite Forall_forall in H.
generalize (H _ a0); clear H; intro.
red in H. rewrite Forall_forall in H.
apply (H (p, collapse (bproj Defs (snd (Defs R)) p))); auto.
apply in_map_iff. exists p; auto.
Defined.

Definition epp Xs ps P : projectable Xs ps P -> Program.
Proof.
intro H; inversion_clear H. inversion_clear H1.
constructor.
apply (epp_D _ _ H).
apply (epp_C _ _ _ H0).
Defined.

(** Auxiliary results about behaviour projection. *)
Lemma bproj_not_In : forall Defs r C,
  ~In r (CCC_pn C (fun X => fst (Defs X))) -> bproj Defs C r = XEnd.
Proof.
induction C; simpl; auto; intros.
+ assert (bproj Defs C r = XEnd).
  1: apply IHC; intro; apply H; sup.
  induction e.
  - intros. case_eq (Pid_dec p r); [idtac | case_eq (Pid_dec p0 r)]; auto.
    all: intros; unfold Pid_dec in H1; rewrite Pdec.eqb_eq in H1.
    all: elim H; rewrite H1; simpl; sup; left.
    left; auto. right; left; auto.
  - case l; (case_eq (Pid_dec p r); [idtac | case_eq (Pid_dec p0 r)]); auto.
    all: intros; unfold Pid_dec in H1; rewrite Pdec.eqb_eq in H1.
    all: elim H; rewrite H1; simpl; sup; left.
    1,3: left; auto. all: right; left; auto.
+ assert (bproj Defs C1 r = XEnd).
  1: apply IHC1; intro; apply H; sup. left; sup.
  assert (bproj Defs C2 r = XEnd).
  1: apply IHC2; intro; apply H; sup.
  case_eq (Pid_dec p r).
  2: rewrite H0, H1; auto.
  intros; unfold Pid_dec in H2; rewrite Pdec.eqb_eq in H2.
  elim H; rewrite H2; simpl; sup. left; sup. left; left; auto.
+ elim in_dec; auto. intro; elim H; auto.
+ elim in_dec; intros.
  - elim H; sup.
  - apply IHC. intro; apply H; sup.
Qed.

Lemma bproj_Call_In : forall Defs C p X, bproj Defs C p = XCall (X, p) ->
  consistent (fun X => fst (Defs X)) C -> In p (fst (Defs X)).
Proof.
induction C; try induction e; simpl.
+ intros r X. elim Pid_dec. intro; inversion H.
  elim Pid_dec. intro; inversion H. auto.
+ intros p1 X. case l.
  - elim Pid_dec. intro; inversion H.
    elim Pid_dec. intro; inversion H. auto.
  - elim Pid_dec. intro; inversion H.
    elim Pid_dec. intro; inversion H. auto.
+ intros p0 X. elim Pid_dec. intro; inversion H.
  intros. apply Xmerge_inv_XCall in H. destroy H0. auto.
+ do 2 intro. elim in_dec; intros; inversion H.
  rewrite <- H2; auto.
+ do 2 intro. elim in_dec; intros; destroy H0; auto.
  inversion H. rewrite <- H3. apply (H1 p); auto.
+ intros. inversion H.
Qed.

Lemma bproj_disjoint : forall Defs e C p, ~In p (eta_pn e) ->
  bproj Defs (e;; C) p = bproj Defs C p.
Proof.
induction e; intros.
+ simpl in H. assert (p <> p1 /\ p0 <> p1). tauto.
  inversion_clear H0.
  rewrite <- Pdec.eqb_neq in H1, H2.
  simpl. unfold Pid_dec; rewrite H1, H2; auto.
+ simpl in H. assert (p <> p1 /\ p0 <> p1). tauto.
  inversion_clear H0.
  rewrite <- Pdec.eqb_neq in H1, H2.
  simpl. unfold Pid_dec; rewrite H1, H2; case l; auto.
Qed.

(** Proof irrelevance for EPP. *)
Lemma epp_C_wd : forall Defs C ps H H',
  Network_eq (epp_C Defs ps C H) (epp_C Defs ps C H').
Proof.
intros; intro. unfold epp_C.
elim In_dec; auto.
intros. elim collapse_char'; auto.
intros. exfalso.
red in H. rewrite Forall_forall in H.
apply (H (p, collapse (bproj Defs C p))); auto.
apply in_map_iff. exists p; auto.
Qed.

Lemma epp_C_out : forall Defs C ps H p, ~In p ps ->
  epp_C Defs ps C H p = End.
Proof. intros; unfold epp_C. elim In_dec; tauto. Qed.

Lemma epp_D_wd : forall Xs Defs H H' X, epp_D Xs Defs H X = epp_D Xs Defs H' X.
Proof.
intros; unfold epp_D.
induction X as (R,p).
elim In_dec; auto.
intros. elim In_dec; auto.
intros. elim collapse_char'; auto.
intros. exfalso.
red in H. rewrite Forall_forall in H.
generalize (H _ a0); clear H; intro.
red in H. rewrite Forall_forall in H.
apply (H (p, collapse (bproj Defs (snd (Defs R)) p))); auto.
apply in_map_iff. exists p; auto.
Qed.

Lemma epp_C_char : forall Xs ps Defs C HP HC,
  Network_eq (Net (epp Xs ps {| Procedures := Defs; Main := C |} HP))
  (epp_C Defs ps C HC).
Proof.
intros.
unfold epp.
case HP; intros. case a; intros.
apply epp_C_wd.
Qed.

Lemma epp_C_char' : forall Xs ps Defs C HP p, In p ps ->
  bproj Defs C p = inject (Net (epp Xs ps {| Procedures := Defs; Main := C |} HP) p).
Proof.
intros; unfold epp.
case HP; intros. case a; intros.
simpl.
unfold epp_C. elim in_dec; simpl.
elim collapse_char'; simpl.
+ induction a1; auto.
+ intros. exfalso.
  red in p0. rewrite Forall_forall in p0.
  apply (p0 (p, collapse (bproj Defs C p))); auto.
  apply in_map_iff. exists p; auto.
+ tauto.
Qed.

Lemma epp_D_char : forall Xs ps Defs C HP HD X p,
  Procs (epp Xs ps {| Procedures := Defs; Main := C |} HP) (X,p)
  = epp_D Xs Defs HD (X,p).
Proof.
intros.
unfold epp.
case HP; intros. case a; intros.
apply epp_D_wd.
Qed.

Lemma epp_D_char' : forall Xs ps Defs C HP X p,
  In X Xs -> set_incl_pid (CCC_pn (snd (Defs X)) (fun Y => fst (Defs Y))) (fst (Defs X)) ->
  bproj Defs (snd (Defs X)) p = inject (Procs (epp Xs ps {| Procedures := Defs; Main := C |} HP) (X,p)).
Proof.
intros.
unfold epp.
case HP; intros.
case a; simpl; intro HD. clear a; intros.
elim In_dec; simpl; intro Hp; elim In_dec; simpl; intro HX.
elim collapse_char'; simpl; intro Hb.
elim Hb; simpl; intros; auto.
+ exfalso. red in HD. rewrite Forall_forall in HD.
  generalize (HD X HX); intro HD'.
  red in HD'. rewrite Forall_forall in HD'.
  apply (HD' (p, collapse (bproj Defs (snd (Defs X)) p))); auto.
  apply in_map_iff. exists p; auto.
+ tauto.
+ apply bproj_not_In.
  intro; apply Hp, H0. auto.
+ tauto.
Qed.

Lemma epp_out : forall Xs ps Defs C HP p, ~In p ps ->
  Net (epp Xs ps {| Procedures := Defs; Main := C |} HP) p = End.
Proof.
intros; unfold epp.
unfold epp.
case HP; intros.
case a; simpl; intro HD. clear a; intros.
apply epp_C_out; auto.
Qed.

End EPP.

Section MoreBranches.

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

Definition Xmore_branches XB XB' := exists B B',
  XB = inject B /\ XB' = inject B' /\ more_branches B B'.

Lemma Xmore_branches_refl : forall X B, X = inject B ->
  Xmore_branches X X.
Proof. intros. exists B, B. repeat split; auto. apply more_branches_refl. Qed.

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

Definition more_branches_N (N N':Network) :=
  forall p, more_branches (N p) (N' p).

End MoreBranches.

Notation "N >> N'" := (more_branches_N N N') (at level 50).

Section Projectability.

(** ** Properties of projectability
  All variants of parameterized projectability are decidable. *)

Lemma projectable_C_dec : forall Defs ps C,
  { projectable_C Defs ps C } + { ~projectable_C Defs ps C }.
Proof.
intros. apply Forall_dec; intro.
induction x as (p,B).
simpl. elim (XUndefined_dec B); auto.
Qed.

Lemma projectable_D_dec : forall Xs Defs,
  { projectable_D Xs Defs } + { ~projectable_D Xs Defs }.
Proof.
intros. apply Forall_dec; intro.
apply projectable_C_dec.
Qed.

Lemma projectable_dec : forall Xs ps P,
  { projectable Xs ps P } + { ~projectable Xs ps P }.
Proof.
intros.
elim (projectable_C_dec (Procedures P) ps (Main P)); intro HC.
2: right; intro; inversion_clear H; auto.
elim (projectable_D_dec Xs (Procedures P)); intro HD.
2: right; intro; destroy H; auto.
generalize (fun p => In_dec P.eq_dec p ps); intro.
elim (Forall_dec (fun p => In p ps)) with (CCC_pn (Main P) (fun _ => nil)); auto; intro Hps.
1: elim (Forall_dec (fun X => forall p, In p (CCC_pn (snd (Procedures P X)) (fun _ => nil)) -> In p ps)) with Xs; intro HXs1.
1: elim (Forall_dec (fun X => forall p, In p (fst (Procedures P X)) -> In p ps)) with Xs; intro HXs2.
+ left. rewrite Forall_forall in Hps, HXs1, HXs2.
  repeat split; eauto.
+ right; intro; apply HXs2.
  destroy H. rewrite Forall_forall; eauto.
+ elim (Forall_dec (fun p => In p ps)) with (fst (Procedures P HXs2)); auto.
  - left; rewrite Forall_forall in a; auto.
  - right; intro. apply b; rewrite Forall_forall; auto.
+ right; intro; apply HXs1.
  destroy H. rewrite Forall_forall; eauto.
+ elim (Forall_dec (fun p => In p ps)) with (CCC_pn (snd (Procedures P HXs1)) (fun _ => nil)); auto.
  - left. rewrite Forall_forall in a; eauto.
  - right; intro. apply b; rewrite Forall_forall; eauto.
+ right; intro; apply Hps.
  destroy H. rewrite Forall_forall; eauto.
Qed.

(** Inversion lemmas for projectability. *)
Lemma projectable_inv_Com : forall Defs ps p e q x C,
  projectable_C Defs ps (p#e --> q$x;; C) -> projectable_C Defs ps C.
Proof.
intros. red; red in H.
rewrite Forall_forall; rewrite Forall_forall in H.
intros. induction x0 as (r,B). intro.
apply (H (r,XUndefined)); auto.
unfold epp_list in H0; rewrite in_map_iff in H0.
unfold epp_list; rewrite in_map_iff.
destroy H0. inversion H2.
rewrite H4 in H0. simpl in H1. clear x0 H4 H2.
exists r; simpl. split; auto.
case Pid_dec; [idtac | case Pid_dec]; simpl; rewrite H5, H1; auto.
Qed.

Lemma projectable_inv_Sel : forall Defs ps p q l C,
  projectable_C Defs ps (p --> q[l];; C) -> projectable_C Defs ps C.
Proof.
intros. red; red in H.
rewrite Forall_forall; rewrite Forall_forall in H.
intros. induction x as (r,B). intro.
apply (H (r,XUndefined)); auto.
unfold epp_list in H0; rewrite in_map_iff in H0.
unfold epp_list; rewrite in_map_iff.
destroy H0. inversion H2.
rewrite H4 in H0. simpl in H1. clear x H4 H2.
exists r; simpl. split; auto.
case l; (case Pid_dec; [idtac | case Pid_dec]); simpl; rewrite H5, H1; auto.
Qed.

Lemma projectable_inv_Eta : forall Defs ps eta C,
  projectable_C Defs ps (eta;; C) -> projectable_C Defs ps C.
Proof.
intros; induction eta.
eapply projectable_inv_Com; eauto.
eapply projectable_inv_Sel; eauto.
Qed.

Lemma projectable_inv_Cond : forall Defs ps p b C1 C2,
  projectable_C Defs ps (If p ?? b Then C1 Else C2) -> projectable_C Defs ps C1.
Proof.
intros. red; red in H.
rewrite Forall_forall; rewrite Forall_forall in H.
intros. induction x as (r,B). intro.
apply (H (r,XUndefined)); auto.
unfold epp_list in H0; rewrite in_map_iff in H0.
unfold epp_list; rewrite in_map_iff.
destroy H0. inversion H2.
rewrite H4 in H0. simpl in H1. clear x H4 H2.
exists r; simpl. split; auto.
case Pid_dec; simpl.
+ rewrite H5, H1; auto.
+ rewrite collapse_merge; auto. rewrite H5; auto.
Qed.

Lemma projectable_inv_Cond' : forall Defs ps p b C1 C2,
  projectable_C Defs ps (If p ?? b Then C1 Else C2) -> projectable_C Defs ps C2.
Proof.
intros. red; red in H.
rewrite Forall_forall; rewrite Forall_forall in H.
intros. induction x as (r,B). intro.
apply (H (r,XUndefined)); auto.
unfold epp_list in H0; rewrite in_map_iff in H0.
unfold epp_list; rewrite in_map_iff.
destroy H0. inversion H2.
rewrite H4 in H0. simpl in H1. clear x H4 H2.
exists r; simpl. split; auto.
case Pid_dec; simpl.
+ rewrite H5, H1. case (collapse (bproj Defs C1 r)); auto.
+ rewrite collapse_merge'; auto. rewrite H5; auto.
Qed.

Lemma projectable_C_use : forall Defs ps C, projectable_C Defs ps C ->
  forall p, In p ps -> exists B, collapse (bproj Defs C p) = inject B.
Proof.
intros.
red in H. rewrite Forall_forall in H.
elim (collapse_char' (bproj Defs C p)); intros.
inversion_clear a.
+ rewrite H1. rewrite collapse_inject. exists x; auto.
+ elim (H (p,collapse (bproj Defs C p))); auto.
  unfold epp_list; rewrite in_map_iff.
  exists p; auto.
Qed.

(** The corresponding lemmas for RT_Call do not hold.
  Therefore, projectability is not preserved by reductions,
  so we need an auxiliary notion. *)
Fixpoint strongly_projectable Defs (C:Choreography) (r:Pid) : Prop :=
match C with
| eta;; C'                  => strongly_projectable Defs C' r
| If p ?? b Then C1 Else C2 => strongly_projectable Defs C1 r
     /\ strongly_projectable Defs C2 r
     /\ collapse (bproj Defs C r) <> XUndefined
| RT_Call X ps C            => strongly_projectable Defs C r /\
     (forall p, In p ps -> In p (fst (Defs X))
          /\ Xmore_branches (bproj Defs (snd (Defs X)) p) (bproj Defs C p))
| _                         => True
end.

Lemma strongly_projectable_C : forall Defs C r,
  strongly_projectable Defs C r -> collapse (bproj Defs C r) <> XUndefined.
Proof.
induction C; simpl.
+ intro; induction e; elim Pid_dec;
  [idtac | elim Pid_dec | elim l | elim l; elim Pid_dec];
    auto; simpl; intros; try (rewrite Xmatch_elim; auto; discriminate).
+ intro; elim Pid_dec; tauto.
+ intro; elim in_dec; discriminate.
+ intro; elim in_dec; auto. discriminate.
  intros. inversion_clear H; auto.
+ discriminate.
Qed.

Lemma strongly_projectable_C' : forall Defs C ps,
  (forall r, In r ps -> strongly_projectable Defs C r) -> projectable_C Defs ps C.
Proof.
intros; red; rewrite Forall_forall.
induction x as (p,B); simpl; intros.
apply in_map_iff in H0; destroy H0. inversion H1.
rewrite H3 in H0; clear H3 H1 x.
apply strongly_projectable_C, H. auto.
Qed.

Lemma initial_strongly_projectable : forall C, initial C ->
  forall Defs ps, projectable_C Defs ps C ->
  forall r, In r ps -> strongly_projectable Defs C r.
Proof.
induction C; auto; simpl; intros.
+ induction e.
  - apply projectable_inv_Com in H0; eauto.
  - apply projectable_inv_Sel in H0; eauto.
+ inversion_clear H. repeat split.
  - apply projectable_inv_Cond in H0; eauto.
  - apply projectable_inv_Cond' in H0; eauto.
  - red in H0. rewrite Forall_forall in H0.
    generalize (H0 (r,collapse (bproj Defs (If p ?? b Then C1 Else C2) r))); intros.
    simpl in H; apply H.
    apply in_map_iff. exists r; auto.
+ inversion H.
Qed.

Lemma initial_strongly_projectable' : forall Defs C r, initial C ->
  ~In r (CCC_pn C (fun X => fst (Defs X))) -> strongly_projectable Defs C r.
Proof.
induction C; simpl; intros; auto.
+ apply IHC; auto. intro; apply H0. sup.
+ destroy H; repeat split.
  - apply IHC1; auto. intro; apply H0. sup; sup.
  - apply IHC2; auto. intro; apply H0. sup; sup.
  - revert H0. sup; sup; intros.
    repeat rewrite bproj_not_In; auto. elim Pid_dec; discriminate.
+ destroy H.
Qed.

(** ** Towards completeness
  Lemmas about reduction and projection. *)
Lemma bproj_reduce_Com_p : forall Defs C s C' s' p q v x,
  strongly_projectable Defs C p ->
  CCC_To Defs C s (CCBase.TL.R_Com p v q x) C' s' ->
  exists e Bp, bproj Defs C p = XSend q e Bp /\ bproj Defs C' p = Bp
    /\ v = eval_on_state e s p.
Proof.
intros.
rename H into HC, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ rewrite <- H3. unfold v1. rewrite H4, H6, H7 in H0. rename e0 into e'.
  clear s'0 H8 C' H3 x0 H7 q0 H6 v1 H5 p0 H4 s0 H1 C0 H2 IHC H9 s' H.
  simpl; unfold Pid_dec.
  Peq. exists e', (bproj Defs C p); auto.
+ elim IHC with C'0; auto.
  clear C' H5 s'0 H6 t H4 s0 H3 C0 H1 eta H0 H7 H.
  rename C'0 into C'; intros.
  destroy H.
  induction e; try (case l); destroy H2; destroy H3; simpl; repeat split; unfold Pid_dec.
  all: Pneq H4; Pneq H5; eauto.
+ clear H s'0 H7 C' H6 s0 H3 C3 H4 C0 H2 b0 H1 p1 H0 t H5.
  rename p into p', p0 into p. inversion_clear H8.
  elim IHC1 with C1'; auto. 2: apply HC.
  elim IHC2 with C2'; auto. 2: apply HC.
  clear IHC1 IHC2 H9 H10; intros.
  destroy H1; destroy H2.
  rename x0 into e, x1 into e', x2 into B2, x3 into B1.
  apply strongly_projectable_C with (r:=p') in HC; auto.
  revert HC. simpl; unfold Pid_dec. Pneq H.
  rewrite H2, H3, H4, H5, H6; simpl. Peq.
  case Expr_dec. 2: intros; elim HC; auto.
  exists e', (Xmerge B1 B2); repeat split; auto.
  rewrite Xmatch_elim; auto.
  intro. rewrite H7 in HC; auto.
+ elim IHC with C'0; auto; intros.
  2: apply HC; auto.
  apply CCBase.TL.disjoint_ps_Com in H7.
  destroy H9.
  simpl. elim in_dec; intros; eauto.
  elim (disjoint_not_in_fst _ _ _ H7 p); simpl; auto.
Qed.

Lemma bproj_reduce_Com_q : forall Defs C s C' s' p q v x,
  strongly_projectable Defs C q ->
  CCC_To Defs C s (CCBase.TL.R_Com p v q x) C' s' -> p <> q ->
  exists Bq, bproj Defs C q = XRecv p x Bq /\ bproj Defs C' q = Bq.
Proof.
intros.
rename H into HC, H1 into Hpq, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ rewrite <- H3. rewrite H4, H6, H7 in H0. rename e0 into e'.
  clear s'0 H8 C' H3 x0 H7 q0 H6 v1 H5 p0 H4 s0 H1 C0 H2 IHC H9 s' H.
  simpl; repeat split; unfold Pid_dec.
  Pneq Hpq. Peq. exists (bproj Defs C q); auto.
+ elim IHC with C'0; auto.
  clear C' H5 s'0 H6 t H4 s0 H3 C0 H1 eta H0 H7 H.
  rename C'0 into C'; intros.
  destroy H0.
  induction e; try (case l); destroy H2; destroy H0; simpl; repeat split; unfold Pid_dec.
  all: Pneq H0; Pneq H2; eauto.
+ clear H s'0 H7 C' H6 s0 H3 C3 H4 C0 H2 b0 H1 p1 H0 t H5.
  rename p into p', p0 into p. inversion_clear H8.
  elim IHC1 with C1'; auto. 2: apply HC.
  elim IHC2 with C2'; auto. 2: apply HC.
  clear IHC1 IHC2 H9 H10; intros.
  destroy H1; destroy H2.
  rename x0 into B2, x1 into B1.
  simpl; unfold Pid_dec.
  apply strongly_projectable_C with (r:=q) in HC; auto.
  revert HC. simpl; unfold Pid_dec.
  Pneq H0. rewrite H1, H2, H3, H4.
  simpl. Peq. Veq.
  exists (Xmerge B1 B2); split; auto.
  rewrite Xmatch_elim; auto.
  intro. rewrite H5 in HC; auto.
+ elim IHC with C'0; auto; intros.
  2: apply HC; auto.
  apply CCBase.TL.disjoint_ps_Com in H7.
  destroy H9. simpl.
  elim in_dec; intros; eauto.
  elim (disjoint_not_in_snd _ _ _ H7 q); simpl; auto.
Qed.

Lemma bproj_reduce_Com_r : forall Defs C s C' s' p q v x r,
  strongly_projectable Defs C r ->
  CCC_To Defs C s (CCBase.TL.R_Com p v q x) C' s' ->
  p <> r -> q <> r -> bproj Defs C' r = bproj Defs C r.
Proof.
intros.
rename H into HC, H1 into Hpr, H2 into Hqr, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ rewrite <- H3. rewrite H4, H6, H7 in H0. rename e0 into e'.
  clear s'0 H8 C' H3 x0 H7 q0 H6 v1 H5 p0 H4 s0 H1 C0 H2 IHC H9 s' H.
  simpl; repeat split; unfold Pid_dec.
  Pneq Hpr. Pneq Hqr. auto.
+ simpl; rewrite IHC; auto.
+ simpl. destroy HC.
  rewrite (IHC1 H11 C1'), (IHC2 H12 C2'); auto.
+ simpl. rewrite IHC; auto.
  apply HC.
Qed.

Lemma bproj_reduce_Sel_p : forall Defs C s C' s' p q l,
  strongly_projectable Defs C p ->
  CCC_To Defs C s (CCBase.TL.R_Sel p q l) C' s' ->
  exists Bp, bproj Defs C p = XSel q l Bp /\ bproj Defs C' p = Bp.
Proof.
intros.
rename H into HC, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ rewrite <- H3. rewrite H4, H5, H6 in H0.
  clear s'0 H7 C' H3 l0 H6 q0 H5 p0 H4 s0 H1 C0 H2 IHC H8 s' H.
  simpl; repeat split; unfold Pid_dec.
  Peq. exists (bproj Defs C p); case l; auto.
+ elim IHC with C'0; auto.
  clear C' H5 s'0 H6 t H4 s0 H3 C0 H1 eta H0 H7 H.
  rename C'0 into C'; intros.
  induction e; try (case l0); destroy H2; destroy H0; simpl; unfold Pid_dec.
  all: Pneq H3; Pneq H1; eauto.
+ clear H s'0 H7 C' H6 s0 H3 C3 H4 C0 H2 b0 H1 p1 H0 t H5.
  rename p into p', p0 into p. inversion_clear H8.
  elim IHC1 with C1'; auto. 2: apply HC.
  elim IHC2 with C2'; auto. 2: apply HC.
  clear IHC1 IHC2 H9 H10; intros.
  destroy H1; destroy H2.
  rename x into B2, x0 into B1.
  simpl; unfold Pid_dec.
  apply strongly_projectable_C with (r:=p') in HC; auto.
  revert HC. simpl; unfold Pid_dec. Pneq H.
  rewrite H1, H2, H3, H4; simpl. Peq.
  rewrite label_eqb_refl.
  exists (Xmerge B1 B2); auto.
  rewrite Xmatch_elim; auto.
  intro. rewrite H5 in HC; auto.
+ elim IHC with C'0; auto; intros.
  2: apply HC; auto.
  apply CCBase.TL.disjoint_ps_Sel in H7.
  destroy H9. simpl.
  elim in_dec; intros; eauto.
  elim (disjoint_not_in_fst _ _ _ H7 p); simpl; auto.
Qed.

Lemma bproj_reduce_Sel_ql : forall Defs C s C' s' p q,
  strongly_projectable Defs C q ->
  CCC_To Defs C s (CCBase.TL.R_Sel p q left) C' s' -> p <> q ->
  exists Bq, bproj Defs C q = XBranching p (Some Bq) None /\ bproj Defs C' q = Bq.
Proof.
intros.
rename H into HC, H1 into Hpq, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ rewrite <- H3. rewrite H4, H5, H6 in H0.
  simpl; repeat split; unfold Pid_dec.
  Pneq Hpq. Peq. exists (bproj Defs C q); auto.
+ elim IHC with C'0; auto.
  clear C' H5 s'0 H6 t H4 s0 H3 C0 H1 eta H0 H7 H.
  rename C'0 into C'; intros.
  induction e; try (case l); destroy H2; destroy H0; simpl; unfold Pid_dec.
  all: Pneq H2; Pneq H0; eauto.
+ clear H s'0 H7 C' H6 s0 H3 C3 H4 C0 H2 b0 H1 p1 H0 t H5.
  rename p into p', p0 into p. inversion_clear H8.
  elim IHC1 with C1'; auto. 2: apply HC.
  elim IHC2 with C2'; auto. 2: apply HC.
  clear IHC1 IHC2 H9 H10; intros.
  destroy H2; destroy H1.
  rename x into B2, x0 into B1.
  simpl; unfold Pid_dec.
  apply strongly_projectable_C with (r:=q) in HC; auto.
  revert HC. simpl; unfold Pid_dec.
  Pneq H0. rewrite H1, H2, H3, H4.
  simpl. Peq.
  exists (Xmerge B1 B2).
  rewrite Xmatch_elim; auto.
  intro. rewrite H5 in HC; auto.
+ elim IHC with C'0; auto; intros.
  2: apply HC; auto.
  apply CCBase.TL.disjoint_ps_Sel in H7.
  destroy H9; simpl.
  elim in_dec; intros; eauto.
  elim (disjoint_not_in_snd _ _ _ H7 q); simpl; auto.
Qed.

Lemma bproj_reduce_Sel_qr : forall Defs C s C' s' p q,
  strongly_projectable Defs C q ->
  CCC_To Defs C s (CCBase.TL.R_Sel p q right) C' s' -> p <> q ->
  exists Bq, bproj Defs C q = XBranching p None (Some Bq) /\ bproj Defs C' q = Bq.
Proof.
intros.
rename H into HC, H1 into Hpq, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ rewrite <- H3. rewrite H4, H5, H6 in H0.
  simpl; repeat split; unfold Pid_dec.
  Pneq Hpq. Peq. exists (bproj Defs C q); auto.
+ elim IHC with C'0; auto.
  clear C' H5 s'0 H6 t H4 s0 H3 C0 H1 eta H0 H7 H.
  rename C'0 into C'; intros.
  induction e; try (case l); destroy H2; destroy H0; simpl; unfold Pid_dec.
  all: Pneq H2; Pneq H0; eauto.
+ clear H s'0 H7 C' H6 s0 H3 C3 H4 C0 H2 b0 H1 p1 H0 t H5.
  rename p into p', p0 into p. inversion_clear H8.
  elim IHC1 with C1'; auto. 2: apply HC.
  elim IHC2 with C2'; auto. 2: apply HC.
  clear IHC1 IHC2 H9 H10; intros.
  destroy H2; destroy H1.
  rename x into B2, x0 into B1.
  simpl; unfold Pid_dec.
  apply strongly_projectable_C with (r:=q) in HC; auto.
  revert HC. simpl; unfold Pid_dec.
  Pneq H0. rewrite H1, H2, H3, H4.
  simpl. Peq.
  exists (Xmerge B1 B2).
  rewrite Xmatch_elim; auto.
  intro. rewrite H5 in HC; auto.
+ elim IHC with C'0; auto; intros.
  2: apply HC; auto.
  apply CCBase.TL.disjoint_ps_Sel in H7.
  destroy H9; simpl.
  elim in_dec; intros; eauto.
  elim (disjoint_not_in_snd _ _ _ H7 q); simpl; auto.
Qed.

Lemma bproj_reduce_Sel_r : forall Defs C s C' s' p q l r,
  strongly_projectable Defs C r ->
  CCC_To Defs C s (CCBase.TL.R_Sel p q l) C' s' ->
  p <> r -> q <> r -> bproj Defs C' r = bproj Defs C r.
Proof.
intros.
rename H into HC, H1 into Hpr, H2 into Hqr, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ rewrite <- H3. rewrite H4, H5, H6 in H0.
  clear s'0 H7 C' H3 l0 H6 q0 H5 p0 H4 s0 H1 C0 H2 IHC H8 s' H.
  simpl; repeat split; unfold Pid_dec.
  Pneq Hpr. Pneq Hqr. case l; auto.
+ induction e; try (case l0); simpl.
  all: case_eq (Pdec.eqb p0 r); intros.
  1,3,5: rewrite IHC; auto.
  all: case_eq (Pdec.eqb p1 r); auto.
  all: rewrite IHC; auto.
+ simpl. destroy HC. rewrite (IHC1 H11 C1'), (IHC2 H12 C2'); auto.
+ simpl. rewrite IHC; auto. apply HC.
Qed.

Lemma bproj_reduce_Cond_p : forall Defs C s C' s' p,
  strongly_projectable Defs C p ->
  CCC_To Defs C s (CCBase.TL.R_Cond p) C' s' ->
  exists b Bt Be, bproj Defs C p = XCond b Bt Be
    /\ (CCBase.beval_on_state b s p = true -> bproj Defs C' p = Bt)
    /\ (CCBase.beval_on_state b s p = false -> bproj Defs C' p = Be).
Proof.
intros.
rename H into HC, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ clear s'0 H6 C' H5 t H4 s0 H3 C0 H1 eta H0 H.
  elim IHC with C'0; intros; auto.
  rename C'0 into C'; clear IHC H7.
  destroy H. rename x into b, x0 into Bt, x1 into Be.
  induction e; destroy H2; simpl in H2, H3.
  all: exists b, Bt, Be; repeat split.
  all: simpl; unfold Pid_dec.
  4,5,6: case l.
  all: Pneq H3; Pneq H2; auto.
+ rewrite H6 in HC. rewrite <- H5.
  clear s'0 H7 C' H5 p0 H6 s0 H2 C3 H4 C0 H3 b0 H1 p1 H0 H IHC1 IHC2.
  apply strongly_projectable_C in HC; revert HC.
  simpl. Peq.
  elim (collapse_char' (bproj Defs C1 p)); intro HC1.
  2: rewrite HC1; intro HC; elim HC; auto.
  inversion_clear HC1. rename x into B1.
  rewrite Xmatch_elim. 2: rewrite H, collapse_inject; apply inject_not_undefined.
  elim (collapse_char' (bproj Defs C2 p)); intro HC2.
  2: rewrite HC2; intro HC; elim HC; auto.
  inversion_clear HC2. rename x into B2.
  rewrite Xmatch_elim. 2: rewrite H0, collapse_inject; apply inject_not_undefined.
  intros.
  exists b, (bproj Defs C1 p), (bproj Defs C2 p); repeat split; auto.
  intro. rewrite H9 in H1; inversion H1.
+ rewrite H6 in HC. rewrite <- H5.
  clear s'0 H7 C' H5 p0 H6 s0 H2 C3 H4 C0 H3 b0 H1 p1 H0 H IHC1 IHC2.
  apply strongly_projectable_C in HC; revert HC.
  simpl. Peq.
  elim (collapse_char' (bproj Defs C1 p)); intro HC1.
  2: rewrite HC1; intro HC; elim HC; auto.
  inversion_clear HC1. rename x into B1.
  rewrite Xmatch_elim. 2: rewrite H, collapse_inject; apply inject_not_undefined.
  elim (collapse_char' (bproj Defs C2 p)); intro HC2.
  2: rewrite HC2; intro HC; elim HC; auto.
  inversion_clear HC2. rename x into B2.
  rewrite Xmatch_elim. 2: rewrite H0, collapse_inject; apply inject_not_undefined.
  intros.
  exists b, (bproj Defs C1 p), (bproj Defs C2 p); repeat split; auto.
  intro. rewrite H9 in H1; inversion H1.
+ clear s'0 H7 C' H6 t H5 s0 H3 C3 H4 C0 H2 b0 H1 p1 H0 H.
  elim IHC1 with C1'; auto. 2: apply HC.
  elim IHC2 with C2'; auto. 2: apply HC.
  clear IHC1 IHC2 H9 H10. intros.
  destroy H; destroy H0. simpl in H8.
  rename x into b2, x1 into Bt2, x2 into Be2.
  rename x0 into b1, x3 into Bt1, x4 into Be1.
  apply strongly_projectable_C in HC; revert HC.
  simpl; unfold Pid_dec. Pneq H8.
  rewrite H3, H1.
  intros.
  elim (XUndefined_dec (Xmerge (XCond b1 Bt1 Be1) (XCond b2 Bt2 Be2))); intros.
  1: rewrite a in HC; elim HC; auto.
  revert HC; simpl. case_eq (BExpr_dec b1 b2). 2: intros; elim HC; auto.
  intro. unfold BExpr_dec in H5; rewrite Bdec.eqb_eq in H5.
  rename b1 into b'; rewrite <- H5 in H1, H, H2, b0; clear b2 H5.
  intro; clear HC.
  exists b', (Xmerge Bt1 Bt2), (Xmerge Be1 Be2); repeat split.
  rewrite <- Xmerge_Cond_inv; simpl. Beq; auto.
  1,2: intro; apply b0; simpl; rewrite H5; Beq; auto.
  case (Xmerge Bt1 Bt2); auto.
  intros. rewrite H4, H2; auto.
  intros. rewrite H, H0; auto.
+ elim IHC with C'0; auto.
  2: apply HC.
  intros. destroy H9. rename x into b, x0 into Bt, x1 into Be.
  apply CCBase.TL.disjoint_ps_Cond in H7.
  simpl. elim in_dec. intro; elim H7; auto.
  exists b, Bt, Be; repeat split; auto.
Qed.

Lemma bproj_reduce_Cond_r : forall Defs C s C' s' p r,
  strongly_projectable Defs C r ->
  CCC_To Defs C s (CCBase.TL.R_Cond p) C' s' ->
  p <> r -> Xmore_branches (bproj Defs C r) (bproj Defs C' r).
Proof.
intros.
rename H into HC, H1 into Hpr, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ clear s'0 H6 C' H5 t H4 s0 H3 C0 H1 eta H0 H.
  elim IHC with C'0; intros; auto.
  rename C'0 into C'; clear IHC H7.
  destroy H.
  induction e; try (case l); destroy H2; simpl in H2, H3.
  all: simpl.
  all: elim Pid_dec; auto.
  2,4,6: elim Pid_dec; auto.
  all: rewrite H0, H1; rename x into B, x0 into B'.
  3,5,7: exists B, B'; auto.
  - exists (p1!e; B), (p1!e; B'); repeat split; auto.
    constructor; auto.
  - exists (p0 ? v; B), (p0 ? v; B'); repeat split; auto.
    constructor; auto.
  - exists (p0 & Some B // None), (p0 & Some B' // None); repeat split; auto.
    constructor; auto.
  - exists (p0 & None // Some B), (p0 & None // Some B'); repeat split; auto.
    constructor; auto.
  - exists (p1(+)left;B), (p1(+)left;B'); repeat split; auto.
    constructor; auto.
  - exists (p1(+)right;B), (p1(+)right;B'); repeat split; auto.
    constructor; auto.
+ rewrite H6 in HC. rewrite <- H5.
  clear s'0 H7 C' H5 p0 H6 s0 H2 C3 H4 C0 H3 b0 H1 p1 H0 H IHC1 IHC2.
  apply strongly_projectable_C in HC; revert HC.
  simpl. unfold Pid_dec; Pneq Hpr.
  intro. apply collapse_exists in HC. destroy HC.
  rename x into B.
  elim (Xmerge_inv _ _ _ HC); intros. destroy H.
  rename x into B1, x0 into B2.
  exists B, B1.
  repeat split; auto.
  apply merge_more_branches with B2; auto.
+ rewrite H6 in HC. rewrite <- H5.
  clear s'0 H7 C' H5 p0 H6 s0 H2 C3 H4 C0 H3 b0 H1 p1 H0 H IHC1 IHC2.
  apply strongly_projectable_C in HC; revert HC.
  simpl. unfold Pid_dec; Pneq Hpr.
  intro. apply collapse_exists in HC. destroy HC.
  rename x into B.
  elim (Xmerge_inv _ _ _ HC); intros. destroy H.
  rename x into B1, x0 into B2.
  exists B, B2.
  repeat split; auto.
  apply merge_more_branches' with B1; auto.
+ clear s'0 H7 C' H6 t H5 s0 H3 C3 H4 C0 H2 b0 H1 p1 H0 H.
  elim IHC1 with C1'; auto. 2: apply HC.
  elim IHC2 with C2'; auto. 2: apply HC.
  clear IHC1 IHC2 H9 H10. intros.
  destroy H; destroy H0. simpl in H8.
  intros. simpl. case_eq (Pid_dec p0 r).
  * rewrite H1, H2, H3, H4.
    exists (Cond b x0 x), (Cond b x2 x1); simpl.
    repeat split; auto.
    constructor; auto.
  * intros.
    apply strongly_projectable_C in HC; revert HC.
    simpl; rewrite H5.
    intro.
    elim (collapse_exists _ HC); intros; clear HC.
    rewrite H3, H1 in H6. fold (merge x0 x) in H6.
    elim (more_branches_merge_extend _ _ _ _ _ H0 H H6).
    intros. destroy H7.
    exists x3, x4; repeat split; auto.
    rewrite H3, H1; auto. rewrite H2, H4; auto.
+ elim IHC with C'0; auto.
  2: apply HC.
  intros. destroy H9.
  apply CCBase.TL.disjoint_ps_Cond in H7.
  simpl. elim in_dec; intros; auto.
  apply Xmore_branches_refl with (Call (r0,r)); auto.
  rewrite H10, H11. exists x, x0; auto.
Qed.

Lemma bproj_reduce_Call_p : forall Defs C s C' s' p X Xs,
  strongly_projectable Defs C p ->
  (forall Y, In Y Xs -> strongly_projectable Defs (snd (Defs Y)) p) ->
  (forall Y, set_incl_pid (CCC_pn (snd (Defs Y)) (fun X => fst (Defs X))) (fst (Defs Y))) ->
  In X Xs ->
  CCC_To Defs C s (CCBase.TL.R_Call X p) C' s' ->
  bproj Defs C p = XCall (X,p) /\ Xmore_branches (bproj Defs (snd (Defs X)) p) (bproj Defs C' p).
Proof.
intros.
rename H into HC, H0 into HDefs, H2 into HX, H1 into Hnames, H3 into H.
revert C' H.
induction C; intros; inversion H.
+ elim IHC with C'0; auto.
  clear s'0 H6 C' H5 t H4 s0 H3 C0 H1 eta H0 H7 H.
  rename C'0 into C'; intros.
  induction e; try (case l); destroy H2; simpl in H2, H1; simpl; unfold Pid_dec.
  1,2,3: Pneq H1; Pneq H2; auto.
+ clear H s'0 H7 C' H6 s0 H3 C3 H4 C0 H2 b0 H1 p1 H0 t H5.
  destroy HC. rename H into HC', H0 into HC''.
  rename p into p', p0 into p. simpl in H8.
  elim IHC1 with C1'; auto.
  elim IHC2 with C2'; auto.
  clear IHC1 IHC2 H9 H10; intros.
  simpl; unfold Pid_dec; rewrite H, H1; repeat split.
  Pneq H8; apply Xmerge_idempotent; discriminate.
  Pneq H8. destroy H0; destroy H2.
  rewrite H3 in H5. apply inject_inj in H5. rewrite <- H5 in H2.
  elim (more_branches_merge _ _ _ H2 H0); intros. destroy H7.
  exists x, x3; repeat split; auto.
  rewrite H4, H6; unfold merge in H9; auto.
+ split; auto.
  simpl; elim in_dec; auto. tauto.
  generalize (strongly_projectable_C _ _ _ (HDefs X HX)); intros.
  elim (collapse_exists _ H9); intros.
  apply Xmore_branches_refl with x; auto.
+ simpl; split.
  - elim in_dec; auto. tauto.
  - elim in_dec; auto.
    intros. apply set_remove'_2 in a. elim a; auto.
    generalize (strongly_projectable_C _ _ _ (HDefs X HX)); intros.
    elim (collapse_exists _ H9); intros.
    apply Xmore_branches_refl with x; auto.
+ simpl. elim in_dec; auto.
  - apply CCBase.TL.disjoint_ps_Call in H7. tauto.
  - intros. apply IHC; auto. apply HC.
+ simpl; split.
  - elim in_dec; auto. tauto.
  - elim in_dec; auto.
    intro. apply set_remove'_2 in a. elim a; auto.
    intros. rewrite <- H3. apply HC; auto.
+ simpl; split.
  - elim in_dec; auto. tauto.
  - rewrite <- H5, <- H3. apply HC; auto.
Qed.

Lemma bproj_reduce_Call_r : forall Defs C s C' s' p X r,
  (forall X, set_incl_pid (CCC_pn (snd (Defs X)) (fun Y => fst (Defs Y))) (fst (Defs X))) ->
  CCC_To Defs C s (CCBase.TL.R_Call X p) C' s' ->
  p <> r -> bproj Defs C' r = bproj Defs C r.
Proof.
intros.
rename H into HDefs, H1 into Hpr, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ simpl. rewrite IHC; auto.
+ simpl. rewrite (IHC1 C1'), (IHC2 C2'); auto.
+ simpl. elim in_dec; auto.
  intros; elim Hpr. apply set_size_1 with P.eq_dec (fst (Defs X)); auto.
  intro. apply bproj_not_In.
  intro; apply b, HDefs; auto.
+ simpl. elim in_dec; elim in_dec; auto; intros.
  elim b. eapply set_remove'_1; eauto.
  elim b. apply set_remove'_3; auto.
  apply bproj_not_In. intro; apply b, HDefs; auto.
+ simpl. rewrite IHC with C'0; auto.
+ simpl. elim in_dec; elim in_dec; auto; intros.
  elim b. eapply set_remove'_1; eauto.
  elim b. apply set_remove'_3; auto.
+ simpl. elim in_dec; auto.
  intros. elim Hpr. apply set_size_1 with P.eq_dec l; auto.
Qed.

(** Strong projectability of well-formed programs is preserved by reductions. *)
Lemma strongly_projectable_reduces : forall P Xs ps,
  Program_WF Xs P -> well_ann P -> projectable Xs ps P ->
  (forall p, In p ps -> strongly_projectable (Procedures P) (Main P) p) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In X Xs -> In p (Vars P X) -> In p ps) ->
  forall s tl P' s', ((P,s) --[tl]--> (P',s'))%CC -> projectable Xs ps P'.
Proof.
intros. rename H2 into HSP, H3 into Hnames, H4 into HDefs, H5 into H2.
induction P as (Defs,C). induction P' as (Defs', C').
generalize (CCP_To_Defs_stable Defs Defs' C C' tl s s' H2); intro.
rewrite <- H3 in H2; rewrite <- H3; clear Defs' H3.
inversion H2. rewrite <- H4 in H2. clear s'0 H9 C'0 H8 tl H4 s0 H6 C0 H5 Defs0 H3.
rename H7 into Ht.
destroy H0; intros. repeat split; auto.
+ red. rewrite Forall_forall; intros.
  induction x as (p,B); simpl in H3.
  clear H2. unfold epp_list in H3.
  apply in_map_iff in H3; destroy H3.
  inversion H2; clear H2. rewrite H5 in H3; clear x B H5 H6.
  rename p into r. simpl.
  destroy H1. simpl in H2, H4, H5, H6, H1.
  assert (Choreography_WF C) as HC. destroy H; auto.
  induction t; generalize (CCC_To_pn _ _ _ _ _ _ Ht) as Ht'; simpl; intros.
  - assert (In p ps) as Hp. apply Hnames, Ht'; auto.
    assert (In q ps) as Hq. apply Hnames, Ht'; auto.
    assert (p <> q) as Hpq. eapply CCC_To_Com_neq; eauto.
    clear Ht'.
    apply projectable_C_use with Defs ps C r in H2; auto. destroy H2.
    case_eq (Pid_dec p r); intro Hpr.
    2: case_eq (Pid_dec q r); intro Hqr.
    * elim (bproj_reduce_Com_p Defs _ _ _ _ _ _ _ _ (HSP p Hp) Ht); intros.
      destroy H7. simpl in H8.
      revert H2. rewrite Pdec.eqb_eq in Hpr. rewrite <- Hpr, H8, H9.
      simpl; intros. elim (collapse_char' x2); intro.
      2: rewrite b in H2; eelim inject_not_undefined; eauto.
      inversion_clear a.
      rewrite H10, collapse_inject; apply inject_not_undefined.
    * elim (bproj_reduce_Com_q Defs _ _ _ _ _ _ _ _ (HSP q Hq) Ht Hpq); intros.
      destroy H7. simpl in H8.
      revert H2. rewrite Pdec.eqb_eq in Hqr. rewrite <- Hqr, H7, H8.
      simpl; intros. elim (collapse_char' x1); intro.
      2: rewrite b in H2; eelim inject_not_undefined; eauto.
      inversion_clear a.
      rewrite H9, collapse_inject; apply inject_not_undefined.
    * rewrite Pdec.eqb_neq in Hpr, Hqr.
      rewrite (bproj_reduce_Com_r Defs C s C' s' p q v x); auto.
      rewrite H2. apply inject_not_undefined.
  - assert (In p ps) as Hp. apply Hnames, Ht'; auto.
    assert (In q ps) as Hq. apply Hnames, Ht'; auto.
    assert (p <> q) as Hpq. eapply CCC_To_Sel_neq; eauto.
    clear Ht'.
    apply projectable_C_use with Defs ps C r in H2; auto. destroy H2.
    case_eq (Pid_dec p r); intro Hpr.
    2: case_eq (Pid_dec q r); intro Hqr.
    * elim (bproj_reduce_Sel_p Defs _ _ _ _ _ _ _ (HSP p Hp) Ht); intros.
      destroy H7. simpl in H8.
      revert H2. rewrite Pdec.eqb_eq in Hpr. rewrite <- Hpr, H7, H8.
      simpl; intros. elim (collapse_char' x0); intro.
      2: rewrite b in H2; eelim inject_not_undefined; eauto.
      inversion_clear a.
      rewrite H9, collapse_inject; apply inject_not_undefined.
    * induction l.
      1: elim (bproj_reduce_Sel_ql Defs _ _ _ _ _ _ (HSP q Hq) Ht Hpq); intros.
      2: elim (bproj_reduce_Sel_qr Defs _ _ _ _ _ _ (HSP q Hq) Ht Hpq); intros.
      all: destroy H7; simpl in H8.
      all: revert H2; rewrite Pdec.eqb_eq in Hqr; rewrite <- Hqr, H7, H8.
      all: simpl; intros; elim (collapse_char' x0); intro.
      2,4: rewrite b in H2; eelim inject_not_undefined; eauto.
      all: inversion_clear a.
      all: rewrite H9, collapse_inject; apply inject_not_undefined.
    * rewrite Pdec.eqb_neq in Hpr, Hqr.
      rewrite (bproj_reduce_Sel_r Defs C s C' s' p q l); auto.
      rewrite H2. apply inject_not_undefined.
  - assert (In p ps) as Hp. apply Hnames, Ht'; auto.
    clear Ht'.
    apply projectable_C_use with Defs ps C r in H2; auto. destroy H2.
    case_eq (Pid_dec p r); intro Hpr.
    * elim (bproj_reduce_Cond_p Defs _ _ _ _ _ (HSP p Hp) Ht); intros.
      destroy H7; destroy H8. simpl in H8, H9.
      revert H2. rewrite Pdec.eqb_eq in Hpr.
      case_eq (CCBase.beval_on_state x0 s p); intro.
      1: rewrite <- Hpr, H9, H8; auto. 2: rewrite <- Hpr, H7, H8; auto.
      all: simpl; intros.
      all: elim (collapse_char' x1); intro.
      2,4: rewrite b in H10; eelim inject_not_undefined; eauto.
      all: inversion_clear a.
      1: rewrite H11, collapse_inject; apply inject_not_undefined.
      rewrite Xmatch_elim in H10; auto.
      2: rewrite H11, collapse_inject; apply inject_not_undefined.
      elim (collapse_char' x2); intro.
      2: rewrite b in H10; eelim inject_not_undefined; eauto.
      inversion_clear a.
      rewrite H12, collapse_inject; apply inject_not_undefined.
    * rewrite Pdec.eqb_neq in Hpr.
      elim (bproj_reduce_Cond_r Defs _ _ _ _ _ _ (HSP r H3) Ht Hpr); intros.
      destroy H7. simpl in H8.
      rewrite H9, collapse_inject. apply inject_not_undefined.
  - assert (In p ps) as Hp. apply Hnames, Ht'; auto.
    assert (In X Xs) as HX. destroy H. eapply CCC_To_Xs; eauto.
    clear Ht'.
    simpl in Hnames.
    apply projectable_C_use with Defs ps C r in H2; auto. destroy H2.
    case_eq (Pid_dec p r); intro Hpr.
    * elim (bproj_reduce_Call_p Defs C s C' s' p X Xs (HSP p Hp)); intros; auto.
      rewrite Pdec.eqb_eq in Hpr. rewrite <- Hpr.
      destroy H8. rewrite H10, collapse_inject; apply inject_not_undefined.
      elim (In_dec P.eq_dec p (CCC_pn (snd (Defs Y)) (fun X : CCBase.RecVar => fst (Defs X)))); intro.
      1: {
        apply initial_strongly_projectable with (fst (Defs Y)); auto.
        destroy H. elim (H Y); tauto.
        red in H4; rewrite Forall_forall in H4; auto.
        apply H0; auto.
      }
      apply initial_strongly_projectable'; auto.
      destroy H. elim (H Y); tauto.
      apply H0.
    * rewrite (bproj_reduce_Call_r Defs C s C' s' p X r); auto.
      rewrite H2; apply inject_not_undefined.
      apply Pdec.eqb_neq; auto.
+ apply H1.
+ simpl. intros. elim (CCC_To_pn' _ _ _ _ _ _ Ht p); intros; auto.
  - destroy H4. apply HDefs with x.
    destroy H. apply within_Xs_char with C; auto.
    apply H0; auto.
  - eapply CCC_pn_mon; eauto.
    simpl. intros. inversion H4.
+ apply H1.
Qed.

Lemma bproj_reduces_disjoint : forall Defs C s tl C' s' ps p,
  (forall X, set_incl_pid (CCC_pn (snd (Defs X)) (fun Y => fst (Defs Y))) (fst (Defs X))) ->
  (forall r, In r ps -> strongly_projectable Defs C r) -> In p ps ->
  CCBase.TL.disjoint_p_rl p tl -> CCC_To Defs C s tl C' s' ->
  Xmore_branches (bproj Defs C p) (bproj Defs C' p).
Proof.
do 7 intro. intros r HDefs.
intros. induction tl.
- destroy H1.
  rewrite (bproj_reduce_Com_r Defs C s C' s' p q v x); auto.
  apply strongly_projectable_C' in H.
  apply projectable_C_use with (p:=r) in H; auto.
  destroy H. apply collapse_inv in H.
  exists x0, x0; repeat split; auto. apply more_branches_refl.
- destroy H1.
  rewrite (bproj_reduce_Sel_r Defs C s C' s' p q l); auto.
  apply strongly_projectable_C' in H.
  apply projectable_C_use with (p:=r) in H; auto.
  destroy H. apply collapse_inv in H.
  exists x, x; repeat split; auto. apply more_branches_refl.
- apply (bproj_reduce_Cond_r Defs C s C' s' p r); auto.
- rewrite (bproj_reduce_Call_r Defs C s C' s' p X); auto.
  apply strongly_projectable_C' in H.
  apply projectable_C_use with (p:=r) in H; auto.
  destroy H. apply collapse_inv in H.
  exists x, x; repeat split; auto. apply more_branches_refl.
Qed.

Lemma strongly_projectable_reduces' : forall P Xs ps,
  Program_WF Xs P -> well_ann P -> projectable Xs ps P ->
  (forall p, In p ps -> strongly_projectable (Procedures P) (Main P) p) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In X Xs -> In p (Vars P X) -> In p ps) ->
  forall s tl P' s', ((P,s) --[tl]--> (P',s'))%CC ->
  forall p, In p ps -> strongly_projectable (Procedures P') (Main P') p.
Proof.
intros. rename H2 into HSP, H3 into Hnames, H4 into HDefs, H5 into H2.
induction P as (Defs,C). induction P' as (Defs', C').
generalize (CCP_To_Defs_stable Defs Defs' C C' tl s s' H2); intro.
rewrite <- H3 in H2; rewrite <- H3; clear Defs' H3.
inversion H2. rewrite <- H4 in H2. clear s'0 H10 C'0 H9 tl H4 s0 H7 C0 H5 Defs0 H3.
rename H8 into Ht.
destroy H0; intros.
rename p into r.
revert dependent C'. induction C; intros; inversion Ht.
- rewrite <- H8; apply (HSP r); auto.
- rewrite <- H8; apply (HSP r); auto.
- simpl. apply IHC; auto.
  eapply Program_WF_eta; eauto.
  destroy H1; repeat split; simpl; auto.
  eapply projectable_inv_Eta; eauto.
  intro p; generalize (H14 p). simpl. sup; sup.
  intro p; generalize (Hnames p). simpl. sup; sup.
  constructor; auto.
- rewrite <- H10; apply (HSP r); auto.
- rewrite <- H10; apply (HSP r); auto.
- simpl. repeat split.
  * apply IHC1; auto.
    eapply Program_WF_Then; eauto.
    destroy H1; repeat split; simpl; auto.
    eapply projectable_inv_Cond; eauto.
    intro q; generalize (H17 q). simpl. sup; sup.
    apply HSP.
    intro q; generalize (Hnames q). simpl. sup; sup.
    constructor; auto.
  * apply IHC2; auto.
    eapply Program_WF_Else; eauto.
    destroy H1; repeat split; simpl; auto.
    eapply projectable_inv_Cond'; eauto.
    intro q; generalize (H17 q). simpl. sup; sup.
    apply HSP.
    intro q; generalize (Hnames q). simpl. sup; sup.
    constructor; auto.
  * clear IHC1 IHC2 s'0 H11 t0 H9 s0 H7 C3 H8 C0 H5 b0 H4 p0 H3.
    destroy H1. simpl in H3.
    assert (projectable_C Defs ps C').
    1:{
      change (projectable_C (Procedures (CCBase.Build_Program Defs C')) ps (Main (CCBase.Build_Program Defs C'))).
      apply (strongly_projectable_reduces (CCBase.Build_Program Defs (If p ?? b Then C1 Else C2))) with Xs s (CCBase.TL.forget t) s'; auto.
      repeat split; auto.
    }
    apply projectable_C_use with (p:=r) in H8; auto.
    inversion H8. rewrite <- H10 in H9; simpl in H9; rewrite H9.
    apply inject_not_undefined.
- assert (In r0 Xs).
  1: { destroy H. elim (H r0); intros; auto. }
  elim (In_dec P.eq_dec r (fst (Defs r0))); intro.
  * simpl. apply initial_strongly_projectable with (fst (Defs r0)); auto.
    destroy H. elim (H r0); auto. tauto.
    destroy H1. red in H13; rewrite Forall_forall in H13; simpl in H13.
    red. rewrite Forall_forall. intros. induction x as (q,B).
    unfold epp_list in H17; rewrite in_map_iff in H17. destroy H17.
    inversion H18. rewrite H20 in H17; clear H21 H20 H18 x.
    red in H14. rewrite Forall_forall in H14.
    generalize (H14 _ H12); clear H14; simpl; intro.
    apply projectable_C_use with (p:=q) in H14; auto.
    inversion H14. rewrite H18. apply inject_not_undefined.
  * simpl. apply initial_strongly_projectable'.
    destroy H. elim (H r0); auto. tauto.
    intro; apply b. apply H0; auto.
- assert (In r0 Xs).
  1: { destroy H. elim (H r0); intros; auto. }
  split; auto; simpl.
  1: elim (In_dec P.eq_dec r (fst (Defs r0))); intro.
  * apply initial_strongly_projectable with (fst (Defs r0)); auto.
    destroy H. elim (H r0); auto. tauto.
    destroy H1. red in H13; rewrite Forall_forall in H13; simpl in H13.
    red. rewrite Forall_forall. intros. induction x as (q,B).
    unfold epp_list in H17; rewrite in_map_iff in H17. destroy H17.
    inversion H18. rewrite H20 in H17; clear H21 H20 H18 x.
    red in H14. rewrite Forall_forall in H14.
    generalize (H14 _ H12); clear H14; simpl; intro.
    apply projectable_C_use with (p:=q) in H14; auto.
    inversion H14. rewrite H18. apply inject_not_undefined.
  * apply initial_strongly_projectable'.
    destroy H. elim (H r0); auto. tauto.
    intro; apply b. apply H0; auto.
  * simpl. intros.
    destroy H1. red in H15; rewrite Forall_forall in H15; simpl in H15.
    generalize (H15 _ H12); clear H15; simpl; intro.
    apply projectable_C_use with (p:=p0) in H15.
    destroy H15.
    split. eapply set_remove'_1; eauto.
    apply Xmore_branches_refl with x.
    apply collapse_inv; auto.
    eapply set_remove'_1; eauto.
- elim (HSP r); intros; auto.
  simpl in H13. split; simpl. apply IHC; auto.
  eapply Program_WF_Call; eauto.
  destroy H1; repeat split; auto.
  * apply strongly_projectable_C'; auto. simpl. apply HSP.
  * intro; generalize (H17 p). simpl. sup.
  * simpl. apply HSP.
  * intro; generalize (Hnames p). simpl; sup.
  * constructor; auto.
  * intros. elim (H14 p); intros; auto. split; auto.
    apply Xmore_branches_trans with (bproj Defs C p); auto.
    apply bproj_reduces_disjoint with s t s' l; auto.
    intros; apply HSP, Hnames. simpl; sup.
    apply CCBase.TL.disjoint_ps_rl_In with l; auto.
- intros. elim (HSP r H6). clear HSP IHC. simpl; intros.
  split; auto.
  intros. apply H15. eapply set_remove'_1; eauto.
- simpl. rewrite <- H10.
  apply HSP; auto.
Qed.

Lemma CCC_To_Call_ann : forall Defs C s X p C' s',
  CCC_To Defs C s (CCBase.TL.R_Call X p) C' s' ->
  strongly_projectable Defs C p -> In p (fst (Defs X)).
Proof.
induction C; intros; inversion H; eauto;
  try (destroy H0; eauto).
all: rewrite <- H4; elim (H0 p); auto.
Qed.

Lemma Program_WF_Defs_strongly_projectable : forall Xs ps P,
  CCBase.Program_WF Xs P -> projectable Xs ps P -> well_ann P ->
  forall X p, In X Xs -> In p ps -> strongly_projectable (Procedures P) (CCBase.Procs P X) p.
Proof.
intros. destroy H.
elim (H X); auto.
intros. clear H; destroy H8.
destroy H0.
elim (In_dec P.eq_dec p (Vars P X)); intros.
+ apply initial_strongly_projectable with (Vars P X); auto.
  red in H11. rewrite Forall_forall in H11. apply H11; auto.
+ apply initial_strongly_projectable'; auto.
  intro; apply b, H1. auto.
Qed.

Lemma EPP_Complete : forall P Xs ps,
  Program_WF Xs P -> well_ann P -> forall (HP:projectable Xs ps P),
  (forall p, In p ps -> strongly_projectable (Procedures P) (Main P) p) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In X Xs -> In p (Vars P X) -> In p ps) ->
  forall s tl P' s', ((P,s) --[tl]--> (P',s'))%CC ->
  exists N tl', (epp Xs ps P HP,s) --[tl']--> (N,s')
  /\ forall H, Net N >> Net (epp Xs ps P' H).
Proof.
intros P Xs ps HWF Hann HP Hsp HMain HXs s tl P' s' HTo.
induction P as (Defs,C), P' as (Defs',C').
generalize (CCP_To_Defs_stable Defs Defs' C C' tl s s' HTo); intro.
rewrite <- H in HTo; rewrite <- H; clear Defs' H.
simpl in Hsp, HMain.
set (N' := epp _ _ _ HP). assert (N' = epp _ _ _ HP) as HN; auto.
clearbody N'; induction N' as (Defs',N).
assert (forall r, {Br | bproj Defs C r = inject Br}) as Hout.
1: { intro.
  elim (In_dec P.eq_dec r ps); intro Hr.
  elim (collapse_char' (bproj Defs C r)); auto.
  intro. elim (strongly_projectable_C _ _ _ (Hsp r Hr)); auto.
  exists End; apply bproj_not_In.
  intro; apply Hr, HMain. auto.
}
assert (projectable_C Defs ps C) as HC.
1: apply strongly_projectable_C'; auto.
induction tl; intros; inversion HTo; induction t; inversion H3.
+ rewrite H9, H8, H7 in H0.
  clear q0 v0 p0 s'0 C'0 s0 C0 Defs0 H9 H8 H7 H5 H4 H3 H2 H1 H.
  generalize (CCC_To_pn _ _ _ _ _ _ H0); intro.
  assert (In p ps) as Hp.
  1: { apply HMain, H. simpl; auto. }
  assert (In q ps) as Hq.
  1: { apply HMain, H. simpl; auto. }
  assert (p <> q) as Hpq.
  1: { eapply CCC_To_Com_neq; eauto. apply HWF. }
  clear H.
  elim (bproj_reduce_Com_p Defs C s C' s' p q v x); intros; auto.
  destroy H. rename x0 into e.
  elim (Hout p); intro.
  rewrite H1; case x0; intros; try (inversion p0); try (inversion p1).
  2: case o, o0; inversion p1.
  rewrite H6 in H1, H2. rename b into Bp.
  clear x1 H6 e0 H5 p0 H4 p1 x0.
  elim (bproj_reduce_Com_q Defs C s C' s' p q v x); intros; auto.
  destroy H3.
  elim (Hout q); intro.
  rewrite H4; case x1; intros; try (inversion p1); try (inversion p0).
  2: case o, o0; inversion p1.
  rewrite H8 in H4, H3. rename b into Bq.
  clear x0 H8 v0 H7 p0 H6 p1 x1.
  exists (Build_Program Defs' (fun r =>
    if (Pid_dec r p) then Bp
    else if (Pid_dec r q) then Bq
    else N r)),
  (forget (R_Com p v q x)).
  repeat split; auto.
  - rewrite H. apply S_Com with Bp Bq.
    * replace N with (Net (Build_Program Defs' N)); auto.
      change (bproj Defs C p = inject (Send q e Bp)) in H1.
      rewrite epp_C_char' with (HP:=HP) in H1; auto.
      apply inject_inj in H1. rewrite <- H1, HN; auto.
    * replace N with (Net (Build_Program Defs' N)); auto.
      change (bproj Defs C q = inject (Recv p x Bq)) in H4.
      rewrite epp_C_char' with (HP:=HP) in H4; auto.
      apply inject_inj in H4. rewrite <- H4, HN; auto.
    * intro r. case_eq (Pid_dec r p); intro.
      rewrite Pdec.eqb_eq in H5; rewrite H5.
      symmetry; apply Network_rm_add_2_p; auto.
      case_eq (Pid_dec r q); intro.
      rewrite Pdec.eqb_eq in H6; rewrite H6.
      symmetry; apply Network_rm_add_2_q; auto.
      elim (Hout r); intros.
      rewrite Pdec.eqb_neq in H5, H6.
      rewrite Network_rm_add_2_out; auto.
    * apply CCC_To_Com_state with Defs C p C'.
      rewrite <- H; auto.
  - simpl; intros H5 r.
    replace N with (Net (Build_Program Defs' N)); auto.
    case_eq (Pid_dec r p); intro.
    2: case_eq (Pid_dec r q); intro.
    3: elim (In_dec P.eq_dec r ps); intro.
    * rewrite Pdec.eqb_eq in H6; rewrite H6.
      replace (Net (epp  _ _ _ H5) p) with Bp. apply more_branches_refl.
      rewrite epp_C_char' with (HP:=H5) in H2; auto.
      apply inject_inj in H2; auto.
    * rewrite Pdec.eqb_eq in H7; rewrite H7.
      replace (Net (epp  _ _ _ H5) q) with Bq. apply more_branches_refl.
      rewrite epp_C_char' with (HP:=H5) in H3; auto.
      apply inject_inj in H3; auto.
    * replace (Net (epp _ _ _ H5) r) with (N r). apply more_branches_refl.
      replace N with (Net (Build_Program Defs' N)); auto.
      rewrite HN.
      apply inject_inj.
      repeat rewrite <- epp_C_char'; auto.
      rewrite Pdec.eqb_neq in H6, H7.
      symmetry; apply bproj_reduce_Com_r with s s' p q v x; auto.
    * replace (Net (epp _ _ _ H5) r) with End.
      simpl. replace (N r) with End. constructor.
      replace N with (Net (Build_Program Defs' N)); auto.
      rewrite HN, epp_C_char with (HC:=HC), epp_C_out; auto.
      elim (strongly_projectable_reduces (CCBase.Build_Program Defs C) Xs ps)
        with s (CCBase.TL.L_Com p v q) (CCBase.Build_Program Defs C') s'; intros; auto.
      rewrite epp_C_char with (HC:=H8), epp_C_out; auto.
      eauto.
+ rewrite H9, H8, H7 in H0.
  clear q0 l0 p0 s'0 C'0 s0 C0 Defs0 H9 H8 H7 H5 H4 H3 H2 H1 H.
  generalize (CCC_To_pn _ _ _ _ _ _ H0); intro.
  assert (In p ps) as Hp.
  1: { apply HMain, H. simpl; auto. }
  assert (In q ps) as Hq.
  1: { apply HMain, H. simpl; auto. }
  assert (p <> q) as Hpq.
  1: { eapply CCC_To_Sel_neq; eauto. apply HWF. }
  clear H.
  elim (bproj_reduce_Sel_p Defs C s C' s' p q l); intros; auto.
  destroy H. rename x into e.
  elim (Hout p); intro.
  rewrite H1; case x; intros; try (inversion p0); try (inversion p1).
  2: case o, o0; inversion p1.
  rewrite H5 in H1, H. rename b into Bp.
  clear e H5 l0 H4 p0 H3 p1 x.
  induction l.
  1: elim (bproj_reduce_Sel_ql Defs C s C' s' p q); intros; auto.
  2: elim (bproj_reduce_Sel_qr Defs C s C' s' p q); intros; auto.
  all: destroy H2; elim (Hout q); intro.
  all: rewrite H3; case x0; intros; try (inversion p1); try (inversion p0).
  all: case o, o0; inversion p1.
  all: rewrite H7 in H3, H2; rename b into Bq.
  all: clear x H7 p0 H6 H5 p1 x0.
  exists (Build_Program Defs' (fun r =>
    if (Pid_dec r p) then Bp
    else if (Pid_dec r q) then Bq
    else N r)),
  (forget (R_Sel p q left)).
  2: exists (Build_Program Defs' (fun r =>
    if (Pid_dec r p) then Bp
    else if (Pid_dec r q) then Bq
    else N r)),
  (forget (R_Sel p q right)).
  all: repeat split; auto.
  3: apply S_RSel with Bp None Bq.
  1: apply S_LSel with Bp Bq None.
  1,6: replace N with (Net (Build_Program Defs' N)); auto.
  1: change (bproj Defs C p = inject (Sel q left Bp)) in H1.
  2: change (bproj Defs C p = inject (Sel q right Bp)) in H1.
  1,2: rewrite epp_C_char' with (HP:=HP) in H1; auto;
    apply inject_inj in H1; rewrite <- H1, HN; auto.
  1,5: replace N with (Net (Build_Program Defs' N)); auto.
  1: change (bproj Defs C q = inject (Branching p (Some Bq) None)) in H3.
  2: change (bproj Defs C q = inject (Branching p None (Some Bq))) in H3.
  1,2: rewrite epp_C_char' with (HP:=HP) in H3; auto;
    apply inject_inj in H3; rewrite <- H3, HN; auto.
  1,4: intro r; case_eq (Pid_dec r p); intro;
    [rewrite Pdec.eqb_eq in H4; rewrite H4;
      symmetry; apply Network_rm_add_2_p; auto
    | case_eq (Pid_dec r q); intro;
      [ rewrite Pdec.eqb_eq in H5; rewrite H5;
        symmetry; apply Network_rm_add_2_q; auto
        | elim (Hout r); intros;
          rewrite Pdec.eqb_neq in H4, H5;
          rewrite Network_rm_add_2_out; auto]].
  1: apply CCC_To_Sel_state with Defs C p q left C'; auto.
  2: apply CCC_To_Sel_state with Defs C p q right C'; auto.
  1,2: simpl; intros H5 r;
    replace N with (Net (Build_Program Defs' N)); auto;
    case_eq (Pid_dec r p); intro;
    [idtac | case_eq (Pid_dec r q); intro;
      [idtac | elim (In_dec P.eq_dec r ps); intro]].
    1,5: rewrite Pdec.eqb_eq in H4; rewrite H4;
      replace (Net (epp  _ _ _ H5) p) with Bp;
      [apply more_branches_refl |
        rewrite epp_C_char' with (HP:=H5) in H; auto;
        apply inject_inj in H; auto ].
    1,4: rewrite Pdec.eqb_eq in H6; rewrite H6;
      replace (Net (epp  _ _ _ H5) q) with Bq;
      [ apply more_branches_refl |
        rewrite epp_C_char' with (HP:=H5) in H2; auto;
        apply inject_inj in H2; auto].
    1,3: replace (Net (epp _ _ _ H5) r) with (N r);
      [ apply more_branches_refl
      | replace N with (Net (Build_Program Defs' N)); auto;
        rewrite HN; apply inject_inj;
        repeat rewrite <- epp_C_char'; auto;
        rewrite Pdec.eqb_neq in H4, H6].
    1: symmetry; apply bproj_reduce_Sel_r with s s' p q left; auto.
    1: symmetry; apply bproj_reduce_Sel_r with s s' p q right; auto.
    1,2: replace (Net (epp _ _ _ H5) r) with End.
    1,3: simpl; replace (N r) with End.
    1,3: constructor.
    1,2: replace N with (Net (Build_Program Defs' N)); auto;
      rewrite HN, epp_C_char with (HC:=HC), epp_C_out; auto.
    1: elim (strongly_projectable_reduces (CCBase.Build_Program Defs C) Xs ps)
        with s (CCBase.TL.L_Sel p q left) (CCBase.Build_Program Defs C') s'; intros;
       eauto; rewrite epp_C_char with (HC:=H7), epp_C_out; auto.
    1: elim (strongly_projectable_reduces (CCBase.Build_Program Defs C) Xs ps)
        with s (CCBase.TL.L_Sel p q right) (CCBase.Build_Program Defs C') s'; intros;
       eauto; rewrite epp_C_char with (HC:=H7), epp_C_out; auto.
+ rewrite H7 in H0.
  clear p0 s'0 C'0 s0 C0 H7 H5 H4 H3 H2 H1 Defs0 H.
  generalize (CCC_To_pn _ _ _ _ _ _ H0); intro.
  assert (In p ps) as Hp.
  1: { apply HMain, H. simpl; auto. }
  clear H.
  elim (bproj_reduce_Cond_p Defs C s C' s' p); intros; auto.
  destroy H. rename x into b.
  elim (Hout p); intro.
  rewrite H1; case x; intros; try (inversion p0); try (inversion p1).
  1: case o, o0; inversion p1.
  rewrite H5 in H1, H2; rewrite H6 in H1, H. rename b1 into Bt, b2 into Be.
  clear x1 H6 x0 H5 b0 H4 p0.
  case_eq (CCBase.beval_on_state b s p); intro Hb.
  1: exists (Build_Program Defs' (fun r =>
    if (Pid_dec r p) then Bt else N r)),
    (forget (R_Cond p)).
  2: exists (Build_Program Defs' (fun r =>
    if (Pid_dec r p) then Be else N r)),
    (forget (R_Cond p)).
  1,2: repeat split; auto.
  1: apply S_Then with b Bt Be; auto.
  5: apply S_Else with b Bt Be; auto.
  1,5: replace N with (Net (Build_Program Defs' N)); auto;
      change (bproj Defs C p = inject (Cond b Bt Be)) in H1;
      rewrite epp_C_char' with (HP:=HP) in H1; auto;
      apply inject_inj in H1; rewrite <- H1, HN; auto.
  1,4: intro r; case_eq (Pid_dec r p); intro;
      [ rewrite Pdec.eqb_eq in H3; rewrite H3, Par_proj2;
        [ unfold Process; Peq; auto | apply Network_rm_In]
      | symmetry; rewrite Pdec.eqb_neq in H3; rewrite Par_proj1';
        [apply Network_rm_out; auto
        | unfold Process, Pid_dec; Pneq H3; auto]].
  1,3: apply CCC_To_Cond_state with Defs C p C'; auto.
  all: simpl; intros H5 r; replace N with (Net (Build_Program Defs' N)); auto.
  all: case_eq (Pid_dec r p); intro; [idtac | elim (In_dec P.eq_dec r ps); intro].
  * rewrite Pdec.eqb_eq in H3; rewrite H3.
    replace (Net (epp _ _ _ H5) p) with Bt. apply more_branches_refl.
    rewrite epp_C_char' with (HP:=H5) in H2; auto.
    apply inject_inj in H2; auto.
  * rewrite HN. rewrite Pdec.eqb_neq in H3.
    assert (p <> r) as Hpr; auto.
    elim (bproj_reduce_Cond_r _ _ _ _ _ _ r (Hsp _ a) H0 Hpr).
    intros. destroy H4.
    replace (Net (epp _ _ _ HP) r) with x0.
    replace (Net (epp _ _ _ H5) r) with x1; auto.
    all: apply inject_inj.
    rewrite <- H7. apply epp_C_char'; auto.
    rewrite <- H6. apply epp_C_char'; auto.
  * replace (Net (epp _ _ _ H5) r) with End.
    simpl. replace (N r) with End. constructor.
    replace N with (Net (Build_Program Defs' N)); auto.
    rewrite HN, epp_C_char with (HC:=HC), epp_C_out; auto.
    elim (strongly_projectable_reduces (CCBase.Build_Program Defs C) Xs ps)
      with s (CCBase.TL.L_Tau p) (CCBase.Build_Program Defs C') s'; intros; auto.
    rewrite epp_C_char with (HC:=H4), epp_C_out; auto.
    eauto.
  * rewrite Pdec.eqb_eq in H3; rewrite H3.
    replace (Net (epp  _ _ _ H5) p) with Be. apply more_branches_refl.
    rewrite epp_C_char' with (HP:=H5) in H; auto.
    apply inject_inj in H; auto.
  * rewrite HN. rewrite Pdec.eqb_neq in H3.
    assert (p <> r) as Hpr; auto.
    elim (bproj_reduce_Cond_r _ _ _ _ _ _ r (Hsp _ a) H0 Hpr).
    intros. destroy H4.
    replace (Net (epp _ _ _ HP) r) with x0.
    replace (Net (epp _ _ _ H5) r) with x1; auto.
    all: apply inject_inj.
    rewrite <- H7. apply epp_C_char'; auto.
    rewrite <- H6. apply epp_C_char'; auto.
  * replace (Net (epp _ _ _ H5) r) with End.
    simpl. replace (N r) with End. constructor.
    replace N with (Net (Build_Program Defs' N)); auto.
    rewrite HN, epp_C_char with (HC:=HC), epp_C_out; auto.
    elim (strongly_projectable_reduces (CCBase.Build_Program Defs C) Xs ps)
      with s (CCBase.TL.L_Tau p) (CCBase.Build_Program Defs C') s'; intros; auto.
    rewrite epp_C_char with (HC:=H4), epp_C_out; auto.
    eauto.
+ rewrite H7 in H0.
  clear p0 s'0 C'0 s0 C0 Defs0 H7 H5 H4 H3 H2 H1 H.
  generalize (CCC_To_pn _ _ _ _ _ _ H0); intro.
  assert (In p ps) as Hp.
  1: { apply HMain, H. simpl; auto. }
  clear H.
  assert (In X Xs) as HX.
  1: { eapply CCC_To_Xs; eauto. destroy HWF; auto. }
  elim (bproj_reduce_Call_p Defs C s C' s' p X Xs); intros; auto.
  2: { eapply Program_WF_Defs_strongly_projectable with (P:=CCBase.Build_Program Defs C); eauto. }
  2: apply Hann.
  elim (Hout p); intro.
  rewrite H; case x; intros; try (inversion p0); try (inversion p1).
  1: case o, o0; inversion p1.
  rewrite H3 in H. rename r into Y, H3 into HY. clear p0 x.
  inversion_clear HP. destroy H3.
  red in H4; rewrite Forall_forall in H4.
  generalize (H4 _ HX); clear H3 H6 H5 H4 H2; intro H4.
  apply projectable_C_use with (p:=p) in H4.
  simpl in H4; destroy H4. rename x into Bp.
  2: { simpl. eapply CCC_To_Call_ann; eauto. }
  exists (Build_Program Defs' (fun r =>
    if (Pid_dec r p) then Bp else N r)),
  (forget (R_Call Y p)).
  repeat split.
  - apply S_Call.
    * replace N with (Net (Build_Program Defs' N)); auto.
      change (bproj Defs C p = inject (Call Y)) in H.
      rewrite epp_C_char' with (HP:=HP) in H; auto.
      apply inject_inj in H. rewrite <- H, HN; auto.
    * intro r. case_eq (Pid_dec r p); intro.
      rewrite Pdec.eqb_eq in H2; rewrite H2, Par_proj2.
      unfold Process; Peq; auto.
      replace Defs' with (Procs (Build_Program Defs' N)); auto.
      rewrite HN, <- HY. rewrite epp_D_char' with (HP:=HP) in H4; auto.
      2: apply Hann.
      rewrite collapse_inject in H4. apply inject_inj; auto.
      apply Network_rm_In.
      symmetry; rewrite Pdec.eqb_neq in H2; rewrite Par_proj1'.
      apply Network_rm_out; auto.
      unfold Process, Pid_dec; Pneq H2; auto.
    * apply CCC_To_Call_state with Defs C p X C'; auto.
  - simpl; intros H5 r.
    replace N with (Net (Build_Program Defs' N)); auto.
    case_eq (Pid_dec r p); intro.
    * rewrite Pdec.eqb_eq in H2; rewrite H2.
      elim (bproj_reduce_Call_p Defs C s C' s' p X Xs); auto.
      intros.
      destroy H6.
      replace Bp with x. replace (Net (epp _ _ _ H5) p) with x0; auto.
      apply inject_inj. rewrite <- H8, epp_C_char' with (HP:=H5); auto.
      apply inject_inj. apply collapse_inv in H4.
      rewrite <- H7; auto.
      intros. eapply Program_WF_Defs_strongly_projectable with (P:=CCBase.Build_Program Defs C); eauto.
    * rewrite Pdec.eqb_neq in H2.
      elim (In_dec P.eq_dec r ps); intro Hr.
      replace (Net (epp _ _ _ H5) r) with (N r). apply more_branches_refl.
      replace N with (Net (Build_Program Defs' N)); auto.
      rewrite HN.
      apply inject_inj.
      repeat rewrite <- epp_C_char'; auto.
      symmetry; apply bproj_reduce_Call_r with s s' p X; auto.
      rewrite HN.
      repeat rewrite epp_out; auto. constructor.
Qed.

End Projectability.

(*

More branches is behavioural equivalence.



Definition more_branches_beh (B1 B2:Behaviour) := (merge_beh B1 B2) = Some B1.


Definition more_branches_net (N N':Network) (ps:list Pid) :=
  forall p, In p ps -> more_branches_beh (N p) (N' p).

Definition more_branches_defs (SPDefs SPDefs' : RecVar -> Behaviour) :=
  forall X, more_branches_beh (SPDefs X) (SPDefs' X).

Inductive MoreBranches_net : Network -> Network -> list Pid -> Prop :=
| MBN_nil N N' : MoreBranches_net N N' nil
| MBN_cons N N' p ps :
  MoreBranches (N p) (N' p) -> MoreBranches_net N N' ps ->
  MoreBranches_net N N' (p::ps).

Lemma more_branches_beh_MoreBranches_1 :
  forall B B',
  more_branches_beh B B' -> MoreBranches B B'.
Proof.
intro.
induction B using Behaviour_ind_b; intro; induction B' using Behaviour_ind_b; try easy.
+ intro. constructor.
+ specialize (IHB B').
  intro.
  red in H. inversion H. clear H.
  generalize H1. clear H1.
  case_eq (Pid_dec p p0); case_eq (Expr_dec e e0); try easy.
  intro. intro.
  rewrite Pdec.eqb_eq in H0. rewrite <- H0.
  rewrite Edec.eqb_eq in H. rewrite <- H.
  simpl.
  case_eq (merge_beh B B'); try easy.
  intros.
  constructor.
  inversion H2. clear H2.
  rewrite H4 in H1.
  apply (IHB H1).
+ specialize (IHB B').
  intro.
  red in H. inversion H. clear H.
  generalize H1. clear H1.
  case_eq (Pid_dec p p0); case_eq (Var_dec v v0); try easy.
  intro. intro.
  rewrite Pdec.eqb_eq in H0. rewrite <- H0.
  rewrite Xdec.eqb_eq in H. rewrite <- H.
  simpl.
  case_eq (merge_beh B B'); try easy.
  intros.
  constructor.
  inversion H2. clear H2.
  rewrite H4 in H1.
  apply (IHB H1).
+ specialize (IHB B').
  intro.
  red in H. inversion H. clear H.
  generalize H1. clear H1.
  case_eq (Pid_dec p p0); case_eq (eqb_label l l0); try easy.
  intro. intro.
  rewrite Pdec.eqb_eq in H0. rewrite <- H0.
  rewrite label_eqb_eq in H. rewrite <- H.
  simpl.
  case_eq (merge_beh B B'); try easy.
  intros.
  constructor.
  inversion H2. clear H2.
  rewrite H4 in H1.
  apply (IHB H1).
+ clear H1 H2.
  rewrite more_branches_beh_char.
  intro. red in H1.
  generalize H1. clear H1.
  case_eq (Pid_dec p p0); try easy.
  intro.
  rewrite Pdec.eqb_eq in H1. rewrite <- H1.
  case_eq (o left); case_eq (o right); case_eq (o0 left); case_eq (o0 right); constructor; try easy.
  - intros. exists b2. split. apply H5.
    apply H; auto.
    rewrite more_branches_beh_char.
    rewrite H3 in H7. inversion H7. clear H7.
    rewrite <- H9.
    apply H6.
  - intros. exists b1. split. apply H4.
    apply H0; auto.
    rewrite more_branches_beh_char.
    rewrite H2 in H7. inversion H7. clear H7.
    rewrite <- H9.
    apply H6.
  - intros. exists b1. split. apply H5.
    apply H; auto.
    rewrite more_branches_beh_char.
    rewrite H3 in H7. inversion H7. clear H7.
    rewrite <- H9.
    apply H6.
  - intros. rewrite H2 in H7. inversion H7.
  - intros. rewrite H3 in H7. inversion H7.
  - intros. exists b0. split. apply H4.
    apply H0; auto.
    rewrite more_branches_beh_char.
    rewrite H2 in H7. inversion H7. clear H7.
    rewrite <- H9.
    apply H6.
  - intros. rewrite H3 in H7. inversion H7.
  - intros. rewrite H2 in H7. inversion H7.
  - intros. exists b0. split. apply H5.
    apply H; auto.
    rewrite more_branches_beh_char.
    rewrite H3 in H7. inversion H7. clear H7.
    rewrite <- H9.
    apply H6.
  - intros. rewrite H2 in H7. inversion H7.
  - intros. rewrite H3 in H7. inversion H7.
  - intros. rewrite H2 in H7. inversion H7.
  - intros. rewrite H3 in H7. inversion H7.
  - intros. exists b0. split. apply H4.
    apply H0; auto.
    rewrite more_branches_beh_char.
    rewrite H2 in H7. inversion H7. clear H7.
    rewrite <- H9.
    apply H6.
  - intros. rewrite H3 in H7. inversion H7.
  - intros. rewrite H2 in H7. inversion H7.
  - intros. rewrite H3 in H7. inversion H7.
  - intros. rewrite H2 in H7. inversion H7.
+ clear IHB'1 IHB'2.
  intro. rewrite more_branches_beh_char in H. red in H. generalize H. clear H.
  case_eq (BExpr_dec b b0).
  2: easy.
  intros.
  specialize (IHB1 B'1). specialize (IHB2 B'2).
  rewrite more_branches_beh_char in IHB1, IHB2.
  inversion H0. clear H0.
  pose (Hthen := IHB1 H1). pose (Helse := IHB2 H2).
  rewrite Bdec.eqb_eq in H.
  rewrite <- H.
  constructor; auto.
+ rewrite more_branches_beh_char.
  intro. red in H. generalize H. clear H.
  case_eq (RecVar_dec r r0).
  2: easy.
  intros.
  rewrite Rdec.eqb_eq in H.
  rewrite H.
  constructor.
Qed.

Lemma more_branches_beh_MoreBranches_2 :
  forall B B',
  MoreBranches B B' -> more_branches_beh B B'.
Proof.
intros. apply more_branches_beh_char. revert H. revert B'.
induction B using Behaviour_ind_b; intro; induction B' using Behaviour_ind_b; try (easy; fail).
all: intro HMB; inversion HMB; clear HMB.
+ (*rewrite <- H3. rewrite <- H4.*) clear H H1 H2 H3 H4 H5.
  simpl. rewrite Pdec.eqb_refl. rewrite Edec.eqb_refl. simpl.
  apply (IHB _ H0).
+ simpl. rewrite Pdec.eqb_refl. rewrite Xdec.eqb_refl. simpl.
  apply (IHB _ H0).
+ simpl. rewrite Pdec.eqb_refl. rewrite label_eqb_refl. simpl.
  apply (IHB _ H0).
+ simpl. rewrite Pdec.eqb_refl. split.
  - case_eq (o left); case_eq (o0 left); auto.
    * intros.
      apply (H _ H10).
      specialize (H6 _ H9). destruct H6. inversion H6.
      rewrite H10 in H11. inversion H11. apply H6.
    * intros. specialize (H6 _ H9). destruct H6. inversion H6. rewrite H11 in H10. inversion H10.
  - case_eq (o right); case_eq (o0 right); auto.
    * intros.
      apply (H0 _ H10).
      specialize (H8 _ H9). destruct H8. inversion H8.
      rewrite H10 in H11. inversion H11. apply H12.
    * intros. specialize (H8 _ H9). destruct H8. inversion H8. rewrite H11 in H10. inversion H10.
+ simpl. rewrite Bdec.eqb_refl. split.
  - apply (IHB1 _ H1).
  - apply (IHB2 _ H6).
+ simpl. rewrite Rdec.eqb_refl. trivial.
Qed.

Lemma more_branches_beh_MoreBranches :
  forall B B',
  more_branches_beh B B' <-> MoreBranches B B'.
Proof.
split. apply more_branches_beh_MoreBranches_1. apply more_branches_beh_MoreBranches_2.
Qed.

Lemma more_branches_net_MoreBranches_2 :
  forall N N' ps,
  MoreBranches_net N N' ps -> more_branches_net N N' ps.
Proof.
intro. intro.
induction ps.
1: { red. intros. inversion H0. }
intro.
inversion H.
red.
rewrite <- H0 in H4. rewrite <- H0.
intros.
inversion H6.
- rewrite <- H7. apply more_branches_beh_MoreBranches. apply H4.
- pose (H' := IHps H5).
  apply (H' _ H7).
Qed.

Lemma more_branches_net_mono :
  forall N N' p ps,
  more_branches_net N N' (p::ps) -> more_branches_net N N' ps.
Proof.
red. intros.
case (P.eq_dec p0 p); intros.
+ rewrite e.
  red in H. apply (H p). constructor. reflexivity.
+ red in H. apply (H p0). apply in_cons. assumption.
Qed.

Lemma more_branches_net_MoreBranches_1 :
  forall N N' ps,
  more_branches_net N N' ps -> MoreBranches_net N N' ps.
Proof.
intro. intro.
induction ps; intros.
1: constructor.
constructor.
- red in H. specialize (H a).
  assert (In a (a::ps)).
  1: constructor; trivial.
  pose (Ha := H H0).
  apply more_branches_beh_MoreBranches; auto.
- apply more_branches_net_mono in H.
  apply (IHps H).
Qed.

Lemma more_branches_net_MoreBranches :
  forall N N' ps,
  more_branches_net N N' ps <-> MoreBranches_net N N' ps.
Proof.
split. apply more_branches_net_MoreBranches_1. apply more_branches_net_MoreBranches_2.
Qed.

Lemma more_branches_completeness :
  forall N1 N2 N2' ps SPDefs1 SPDefs2 s s' t,
    within_ps ps N1 -> within_ps ps N2 ->
    more_branches_net N1 N2 ps ->
    more_branches_defs SPDefs1 SPDefs2 ->
    SP_To SPDefs1 N2 s t N2' s' ->
    exists N1', SP_To SPDefs2 N1 s t N1' s' /\ more_branches_net N1' N2' ps.
Proof.
intros.
red in H, H0, H1, H2.
inversion H3.
+ assert (In p ps) as Hp. elim (In_dec P.eq_dec p ps); auto. intro; rewrite H0 in H4; auto; inversion H4.
  assert (In q ps) as Hq. elim (In_dec P.eq_dec q ps); auto. intro; rewrite H0 in H5; auto; inversion H5.
  generalize (H1 _ Hp); generalize (H1 _ Hq); intros.
  apply more_branches_beh_MoreBranches_1 in H14.
  apply more_branches_beh_MoreBranches_1 in H15.
  rewrite H4 in H15; rewrite H5 in H14.
  inversion H14; inversion H15.
  rewrite H17, H19 in H16; clear p0 H17 x0 H19 B'0 H20.
  rewrite H22, H24 in H21; clear B'1 H25 e0 H24 p1 H22.
  exists (fun r => if (Pid_dec r p) then B1 else if (Pid_dec r q) then B0 else N1 r); split.
  - apply S_Com with B1 B0; auto.
    case_eq (Pid_dec p p); auto. intro. apply Pdec.eqb_neq in H17. elim H17; auto.
    assert (q <> p). intro. rewrite H17 in H16; rewrite <- H16 in H21; inversion H21.
    rewrite <- Pdec.eqb_neq in H17; unfold Pid_dec at 1; rewrite H17; auto.
    case_eq (Pid_dec q q); auto. intro. apply Pdec.eqb_neq in H19. elim H19; auto.
    red; intros.
    case_eq (Pid_dec p0 p); intros.
    1: { rewrite Pdec.eqb_eq in H19. rewrite H19 in H17. elim H17; simpl; auto. }
    case_eq (Pid_dec p0 q); intros.
    1: { rewrite Pdec.eqb_eq in H20. rewrite H20 in H17. elim H17; simpl; auto. }
    auto.
  - red. intros.
    case_eq (Pid_dec p0 p); intros.
    * rewrite Pdec.eqb_eq in H19. rewrite H19.
      rewrite H6. apply (more_branches_beh_MoreBranches). auto.
    * case_eq (Pid_dec p0 q); intros.
      ** rewrite Pdec.eqb_eq in H20. rewrite H20.
         rewrite H7. apply (more_branches_beh_MoreBranches). auto.
      ** rewrite Pdec.eqb_neq in H19, H20.
         red in H8. specialize (H8 p0).
         assert (~ In p0 (p::q::nil)).
         *** simpl. red. intros.
             inversion H22; auto.
             inversion H24; auto.
         *** pose (H' := H8 H22).
             rewrite H'. auto.
Admitted.

End EPP_Properties.
*)

End EPPBase.
