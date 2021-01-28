Require Export MC.
Require Export SP.

Local Open Scope nat_scope.

Module EPPBase (P X V E B R:DecType) (Ev:Eval E X V V) (BEv:Eval B X V Bool).

Module PR := DecProd R P.

Module Import MCBase := MCBase P X V E B R Ev BEv.
Module Import SP_EPP := SPBase P X V E B PR Ev BEv.

(*
Section Tactics.

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

End Tactics.
*)

Section EPP.

(** First step: returns an XBehaviour, possibly with XUndefined subcomponents. *)
Fixpoint bproj (Defs:DefSet) (C:Choreography) (r:Pid) : XBehaviour :=
match C with
| MCBase.End                => XEnd
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
| MCBase.Call X             => if In_dec P.eq_dec r (fst (Defs X))
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
  (forall p, In p (MCC_pn (Main P) (fun _ => nil)) -> In p ps) /\
  (forall p X, In X Xs -> In p (fst (Procedures P X)) -> In p ps) /\
  (forall p X, In X Xs -> In p (MCC_pn (snd (Procedures P X)) (fun _ => nil)) -> In p ps).

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

Lemma epp_D_char : forall Xs ps Defs C HP HD X p,
  Procs (epp Xs ps {| Procedures := Defs; Main := C |} HP) (X,p)
  = epp_D Xs Defs HD (X,p).
Proof.
intros.
unfold epp.
case HP; intros. case a; intros.
apply epp_D_wd.
Qed.

End EPP.

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
elim (Forall_dec (fun p => In p ps)) with (MCC_pn (Main P) (fun _ => nil)); auto; intro Hps.
1: elim (Forall_dec (fun X => forall p, In p (MCC_pn (snd (Procedures P X)) (fun _ => nil)) -> In p ps)) with Xs; intro HXs1.
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
+ elim (Forall_dec (fun p => In p ps)) with (MCC_pn (snd (Procedures P HXs1)) (fun _ => nil)); auto.
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
                               (forall p, In p ps -> bproj Defs C p = bproj Defs (snd (Defs X)) p)
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

Ltac Peq := unfold Pid_dec; rewrite Pdec.eqb_refl; simpl.
Ltac Eeq := unfold Expr_dec; rewrite Edec.eqb_refl; simpl.
Ltac Beq := unfold BExpr_dec; rewrite Bdec.eqb_refl; simpl.
Ltac Veq := unfold Var_dec; rewrite Xdec.eqb_refl; simpl.
Ltac Xeq := unfold RecVar_dec; rewrite Rdec.eqb_refl; simpl.

Lemma Xmerge_idempotent : forall B, collapse B <> XUndefined ->
  Xmerge B B = B.
Proof.
intros. elim (collapse_char' B). 2: tauto.
intro. inversion_clear a. rewrite H0.
fold (merge x x). apply merge_idempotent.
Qed.

Ltac sup := unfold set_union_pid; rewrite set_union_iff; auto.

Lemma bproj_not_In : forall Defs r C,
  ~In r (MCC_pn C (fun X => fst (Defs X))) -> bproj Defs C r = XEnd.
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

Lemma merge_Cond_reduce_1 : forall Defs C1 C2 s p v q x C1' C2' s',
  let t := MCBase.TL.R_Com p v q x in
  MCC_To Defs C1 s t C1' s' -> MCC_To Defs C2 s t C2' s' -> p <> q ->
  collapse (Xmerge (bproj Defs C1 p) (bproj Defs C2 p)) <> XUndefined ->
  exists e, collapse (Xmerge (bproj Defs C1 p) (bproj Defs C2 p))
  = XSend q e (Xmerge (bproj Defs C1' p) (bproj Defs C2' p)).
Proof.
intros. rename H2 into HC1C2.
revert C1 C1' s s' H C2 C2' H H0 H1 HC1C2.
induction C1.
(* End *) 5: intros; inversion H.
+ do 4 intro. inversion H; clear H.
  - clear s'0 H8 C1 H3 x0 H7 q0 H6 p0 H4 s0 H1 C H2 IHC1 e H0.
    rewrite H5 in H9; clear v1 H5. rename e0 into e.
    induction C2; intros; inversion H0; revert HC1C2.
    * rewrite <- H2; clear e0 H0 H2.
      rewrite H6, H8, H10.
      simpl. Peq. Peq. case_eq (Expr_dec e e1).
      2: intros; elim HC1C2; auto.
      exists e; simpl. revert HC1C2. rewrite H5.
      case_eq (Xmerge (bproj Defs C1' p) (bproj Defs C2' p)); simpl; auto.
      1,2,3: do 3 intro; case (collapse x1); auto; intros; elim HC1C2; auto.
      3: intros; elim HC1C2; auto.
      2: do 3 intro; case (collapse x1); case (collapse x2); auto; intros; elim HC1C2; auto.
      do 3 intro. case o; case o0; auto.
      2,3: intro; case (collapse x1); auto; intros; elim HC1C2; auto.
      do 2 intro; case (collapse x1); case (collapse x2); auto; intros; elim HC1C2; auto.
    * assert (~In p (eta_pn e0)).
      red; intro. unfold t in H4.
      induction e0; destroy H4; destroy H12; simpl in H11; tauto.
      rewrite (bproj_disjoint Defs e0 C' p); auto.
      rewrite (bproj_disjoint Defs e0 C2 p); auto.
    * elim (IHC2_1 C1'0); auto.
      elim (IHC2_2 C2'0); auto.
      intros.
      rename x0 into e', x1 into e'', p0 into p'.
      revert H14 H15. simpl. Peq.
      unfold t in H11; inversion_clear H11.
      rewrite <- Pdec.eqb_neq in H14; rewrite H14.
      case_eq (bproj Defs C2_2 p); simpl; intros; try (inversion H16; fail).
      revert H16 H17.
      case_eq (bproj Defs C2_1 p); simpl; intros; try (inversion H18; fail).
      revert H17 H18.
      case_eq (Pid_dec q p0); simpl. case_eq (Expr_dec e e0); simpl.
      2: intros H'' H''' H'; inversion H'.
      2: intros H'' H'; inversion H'.
      elim (XUndefined_dec (Xmerge (bproj Defs C1' p) x0)); intro.
      1: rewrite a; intros. inversion H19.
      rewrite Xmatch_elim; auto. do 3 intro.
      case_eq (Pid_dec q p2); simpl. case_eq (Expr_dec e e1); simpl.
      2: intros H'' H''' H'; inversion H'.
      2: intros H'' H'; inversion H'.
      elim (XUndefined_dec (Xmerge (bproj Defs C1' p) x1)); intro.
      1: rewrite a; intros. inversion H22.
      rewrite Xmatch_elim; auto. do 3 intro.
      unfold Pid_dec in H18, H21; rewrite Pdec.eqb_eq in H18, H21.
      unfold Expr_dec in H17, H20; rewrite Edec.eqb_eq in H17, H20.
      rewrite <- H17, <- H18, <- H20, <- H21. Peq. Eeq.
      rewrite <- H17, <- H18 in H11; rewrite <- H20, <- H21 in H16.
      clear p0 p2 e1 e0 H21 H20 H18 H17 s'0 H10 t0 H7 s0 H5 b0 H3 p1 H2 IHC2_1 IHC2_2.
      assert (e' = e).
      1: { revert H19. simpl. case_eq (collapse (Xmerge (bproj Defs C1' p) x0));
        intros; inversion H19; auto. }
      assert (e'' = e).
      1: { revert H22. simpl. case_eq (collapse (Xmerge (bproj Defs C1' p) x1));
        intros; inversion H22; auto. }
      rewrite H2 in H19; rewrite H3 in H22; clear H2 H3 e' e''.
      exists e.
      elim (XUndefined_dec (Xmerge x1 x0)); intro.
      1: { exfalso. revert HC1C2. simpl. Peq. rewrite H14, H11, H16.
        simpl. Peq. Eeq. rewrite a. intro. elim HC1C2; auto. }
      rewrite Xmatch_elim; auto. Peq. Eeq.
      elim (XUndefined_dec (Xmerge (bproj Defs C1' p) (Xmerge x1 x0))); intro.
      simpl in H19, H22.
      rewrite a.

merge B B1


, C2; intros.
(* C1 is End *) 21,22,23,24,25: inversion H.
(* C2 is End *) 5,10,15,20: inversion H0.
all: revert HC1C2.
+ (* Eta / Eta *)
  inversion H; inversion H0.
  - simpl. Peq. Peq. case_eq (Expr_dec e1 e2); simpl.
    2: intros HE H'; elim H'; auto.
    exists e1. revert HC1C2.
    case_eq (Xmerge (bproj Defs C1' p) (bproj Defs C2' p)); simpl; auto.
    1,2,3: do 3 intro; case (collapse x2); auto; intros; elim HC1C2; auto.
    3: intros; elim HC1C2; auto.
    * do 3 intro. case o; case o0; auto.
      2,3: intro; case (collapse x2); auto; intros; elim HC1C2; auto.
      do 2 intro; case (collapse x2); case (collapse x3); auto; intros; elim HC1C2; auto.
    * do 3 intro; case (collapse x2); case (collapse x3); auto; intros; elim HC1C2; auto.
  - apply IHC1.
Peq. induction e0; unfold t in H14; destroy H14; destroy H20.
    2: case l.
    all: rewrite <- Pdec.eqb_neq in H22; rewrite H22.
    all: rewrite <- Pdec.eqb_neq in H21; rewrite H21.
    all: case (bproj Defs C2 p); simpl; try (intros; elim HC1C2; auto; fail).
    all: do 3 intro; elim Pid_dec; elim Expr_dec; simpl; try (intros; elim HC1C2; auto; fail).
    all: exists e1; case_eq (Xmerge (bproj Defs C1' p) x1); simpl; auto.





Lemma merge_Cond_reduce : forall Defs Xs r C1 C2 s t C1' C2' s',
  projectable_D Xs Defs ->
  (forall X, set_incl_pid (MCC_pn (snd (Defs X)) (fun X => fst (Defs X))) (fst (Defs X))) ->
  (forall X ps C', (C1 = MCBase.Call X \/ C1 = RT_Call X ps C') -> In X Xs) ->
  (forall X ps C', (C2 = MCBase.Call X \/ C2 = RT_Call X ps C') -> In X Xs) ->
  consistent (fun X => fst (Defs X)) C1 -> consistent (fun X => fst (Defs X)) C2 -> 
  MCC_To Defs C1 s t C1' s' -> MCC_To Defs C2 s t C2' s' ->
  collapse (Xmerge (bproj Defs C1 r) (bproj Defs C2 r)) <> XUndefined
  -> collapse (Xmerge (bproj Defs C1' r) (bproj Defs C2' r)) <> XUndefined.
Proof.
intros. rename H into HD, H0 into HD', H1 into HC1, H2 into HC2.
rename H3 into HC1'', H4 into HC2'', H5 into HC1', H6 into HC2', H7 into HC1C2.
set (B := Xmerge (bproj Defs C1 r) (bproj Defs C2 r)). fold B in HC1C2.
assert (B = Xmerge (bproj Defs C1 r) (bproj Defs C2 r)) as HB. auto.
clearbody B.
revert C1 C2 s t C1' C2' HC1 HC2 HC1' HC2' HC1'' HC2'' B HB HC1C2.
double induction C1 C2; intros.
(* C1 is End *) 21,22,23,24,25: inversion HC1'.
(* C2 is End *) 5,10,15,20: inversion HC2'.
all: revert HC1C2; rewrite HB; clear B HB.
+ (* Eta / Eta *)
  simpl in HC1'', HC2''. clear HC1 HC2.
  inversion HC1'; inversion HC2'; clear HC1' HC2'.
  - clear H H0.
    clear s'1 H13 s1 H9 C0 H10 s'0 H6 s0 H2 C H3 e H8 e0 H1.
    rewrite H12 in HC2''; clear c H12.
    rewrite H5 in HC1''; clear c0 H5.
    rewrite <- H11 in H4; clear H11; inversion H4; clear H4.
    clear H14.
    rewrite <- H0, <- H2, <- H3. clear v0 H1 x0 H3 q0 H2 p0 H0.
    simpl. case_eq (Pid_dec p r); simpl; [case_eq (Expr_dec e1 e2) | case_eq (Pid_dec q r)]; simpl; auto.
    * Peq. intros. intro. apply HC1C2.
      elim (XUndefined_dec (Xmerge (bproj Defs C1' r) (bproj Defs C2' r))); intros.
      1: rewrite a; auto.
      rewrite Xmatch_elim; auto.
      simpl. rewrite H1; auto.
    * Peq. intros; elim HC1C2; auto.
    * Peq. Veq. intros. intro. apply HC1C2.
      elim (XUndefined_dec (Xmerge (bproj Defs C1' r) (bproj Defs C2' r))); intros.
      1: rewrite a; auto.
      rewrite Xmatch_elim; auto.
      simpl. rewrite H1; auto.
  - rewrite <- H4 in H11; inversion H11.
  - clear s'1 H14 t0 H12 s1 H11 C0 H9 eta H8 C2' H13 s'0 H6 s0 H2 C H3 e0 H1.
    rewrite H5 in HC1'', H0; clear c0 H5.
    induction e. all: rewrite <- H4 in H10; destroy H10; destroy H1.
    2: case l.
    all: simpl; case_eq (Pid_dec p r); case_eq (Pid_dec p0 r); simpl.
    1,5: intros; elim H3; unfold Pid_dec in H5, H6;
      rewrite Pdec.eqb_eq in H5, H6;rewrite H5, H6; auto.
    1,3,4,6,8,10: case_eq (Pid_dec p1 r); simpl.
    1,5,9,15: intros; elim HC1C2; auto.
    2,3,5,6,8,9,10,11,12: case_eq (Pid_dec q r); simpl.
    all: try (intros; elim HC1C2; auto; fail).
    2: intros; elim H10; unfold Pid_dec in H5, H6;
      rewrite Pdec.eqb_eq in H5, H6;rewrite H5, H6; auto.
    1,3,6,9,14,15: case_eq (bproj Defs c r); try (intros; elim HC1C2; auto; fail); do 3 intro.
    1,5,6: case_eq (Pid_dec q p2); simpl.
    case_eq (Expr_dec e1 e0); simpl.
    4,6: case_eq (Expr_dec e1 e); simpl.
    10,11,12: case_eq (Pid_dec p p2); simpl.
    all: try (intros; elim HC1C2; auto; fail).
    





+ revert HC1C2. rewrite HB; clear B HB.
  simpl; case in_dec; case in_dec; auto.
  - simpl. case_eq (RecVar_dec (r1,r) (r0,r)); auto.
    intros.
    unfold RecVar_dec in H; rewrite Rdec.eqb_eq in H. inversion H.
    rewrite H1 in HC1'.
    rewrite (MCC_To_deterministic_1 _ _ _ _ _ _ _ _ HC1' HC2').
    assert (In r0 Xs) as HX. apply HC2 with nil MCBase.End; auto.
    clear r1 H1 i0 HC1 HC2 H HC1C2 HC1'' HC2''. rename r0 into X.
    red in HD. rewrite Forall_forall in HD. generalize (HD _ HX); intro HC.
    red in HC. rewrite Forall_forall in HC.
    assert (collapse (bproj Defs (snd (Defs X)) r) <> XUndefined).
    1: {
      apply (HC (r,collapse (bproj Defs (snd (Defs X)) r))).
      unfold epp_list; rewrite in_map_iff.
      exists r; split; auto.
    }
    inversion HC1'; inversion HC2'.
    * rewrite Xmerge_idempotent; auto.
    * rewrite H2 in H10; inversion H10. inversion H17.
    * rewrite H10 in H2; inversion H2; inversion H17.
    * simpl. elim in_dec; simpl.
      1: Xeq. discriminate.
      rewrite Xmerge_idempotent; auto.
  - simpl.
    intros.
    replace (bproj Defs C1' r) with XEnd.
    replace (bproj Defs C2' r) with XEnd.
    discriminate.
    1: clear dependent r1; clear HC1C2; inversion HC2'.
    3: clear dependent r0; clear HC1C2; inversion HC1'.
    all: symmetry; apply bproj_not_In; intro.
    * apply n, HD'; auto.
    * simpl in H7. unfold set_union_pid in H7. elim (set_union_elim _ _ _ _ H7); intro.
      apply set_remove'_1 in a; auto.
      apply n, HD'; auto.
    * apply n0, HD'; auto.
    * simpl in H7. unfold set_union_pid in H7. elim (set_union_elim _ _ _ _ H7); intro.
      apply set_remove'_1 in a; auto.
      apply n0, HD'; auto.
+ rename c into C, l into ps.
  generalize HB; simpl. case in_dec; case in_dec; simpl.
  1,2: case_eq (RecVar_dec (r1,r) (r0,r)); simpl.
  all: intros; rewrite HB0 in HB, HC1C2; clear B HB0.
  all: try (elim HC1C2; auto; fail).
  - unfold RecVar_dec in H0; rewrite Rdec.eqb_eq in H0. inversion H0.
    rewrite H2 in HC1', HC1'', HB.
    assert (In r0 Xs) as HX. eauto.
    clear r1 H2 i0 HC1 HC2 H0 HC1C2. rename r0 into X.
    red in HD. rewrite Forall_forall in HD. generalize (HD _ HX); intro HC.
    red in HC. rewrite Forall_forall in HC.
    assert (collapse (bproj Defs (snd (Defs X)) r) <> XUndefined).
    1: {
      apply (HC (r,collapse (bproj Defs (snd (Defs X)) r))).
      unfold epp_list; rewrite in_map_iff.
      exists r; split; auto.
      apply HC2''; auto.
    }
    inversion_clear HC2''; clear HC1''.
    rename H1 into H', H2 into H''.
    inversion HC1'; inversion HC2'; clear HC1' HC2'.
    * clear s'1 H15 C2' H14 t0 H13 s1 H11 C0 H12 ps0 H10 X1 H9 s'0 H8 C1' H7 s0 H5 X0 H1.
      simpl. elim in_dec; auto.
      exfalso. rewrite <- H6 in H16. apply MCBase.TL.disjoint_ps_Call in H16.
      apply H16. replace p with r; auto.
      apply set_size_1 with P.eq_dec (fst (Defs X)); auto.
    * clear s'1 H16 C2' H15 s1 H13 C0 H11 ps0 H10 X1 H9 s'0 H8 C1' H7 s0 H5 X0 H1.
      rewrite <- H14 in H6; clear H14; inversion H6.
      rewrite <- H5 in H18; rewrite <- H5; clear p0 H5 H6.
      exfalso. generalize (set_size_incl_le (T_dec := P.eq_dec) H'); intro.
      fold set_size_pid in H1; rewrite H3 in H1.
      apply (Nat.lt_irrefl 1). apply lt_le_trans with (set_size_pid ps); auto.
    * clear s'1 H16 s1 H13 C0 H11 ps0 H10 X1 H9 s'0 H8 C1' H7 s0 H5 X0 H1.
      rewrite <- H15; clear C2' H15.
      rewrite <- H14 in H6; inversion H6; clear H14 H6 t.
      rewrite <- H5 in H18; clear p0 H5.
      generalize (set_size_1 P.eq_dec _ H17 _ _ i H18); intro.
      rewrite <- H1 in H4; clear H1 H18 p.
      (* Somehow: projecting (RT_Call X ps C) for something in ps should give the same as projecting the corresponding definition for X *)
Abort.






(** Strong projectability of well-formed programs is preserved by reductions. *)
Lemma strongly_projectable_reduces : forall P Xs ps,
  Program_WF Xs P -> well_ann P -> projectable Xs ps P ->
  (forall p, In p ps -> strongly_projectable (Procedures P) (Main P) p) ->
  forall s tl P' s', ((P,s) --[tl]--> (P',s'))%MC -> projectable Xs ps P'.
Proof.
intros.
induction P as (Defs,C). induction P' as (Defs', C').
generalize (MCP_To_Defs_stable Defs Defs' C C' tl s s' H2); intro.
rewrite <- H3 in H2; rewrite <- H3; clear Defs' H3.
inversion H2. rewrite <- H4 in H2. clear s'0 H9 C'0 H8 tl H4 s0 H6 C0 H5 Defs0 H3.
rename H7 into Ht.
destroy H0; intros. repeat split; auto.
+ apply strongly_projectable_C'.
  destroy H.
  clear H0 H6 H2 H3 H5 H7 H8.
  induction Ht; auto; simpl; intros.
  - elim (H1 r); auto.
  - elim (H1 r); auto. intros H' H''; destroy H''; auto.
  - auto.
  - assert (strongly_projectable Defs C1' r).
    1: apply IHHt1; auto; intros; elim (H1 p0); auto.
    assert (strongly_projectable Defs C2' r).
    1: {
      apply IHHt2; auto; intros; elim (H1 p0); auto.
      elim (H1 p0); auto. intros H' H''; destroy H''; auto.
    }
    repeat split; auto.
    elim (H1 r); auto. simpl; intros H' H''; destroy H''; auto.
    revert H''. case Pid_dec; simpl.
    * repeat rewrite Xmatch_elim. intro; discriminate.
      all: apply strongly_projectable_C; auto.
    * intro. apply merge_Cond_reduce with s t C1 C2 s'; auto.

(* *)

2: {  destroy H. clear H H1 H2 H3 H4 H7.
  induction Ht.
  1,2,3,4: intros; apply H5; auto;
    simpl; unfold set_union_pid; repeat rewrite set_union_iff; auto.
  - intros; elim (set_union_elim _ _ _ _ H1); intro.
    1: apply H5, set_union_iff; auto.
    apply IHHt; auto.
    intros; apply H5; simpl.
    unfold set_union_pid; repeat rewrite set_union_iff; auto.
  - intros; inversion_clear H8.
    elim (set_union_elim _ _ _ _ H1); intro.
    1: elim (set_union_elim _ _ _ _ a); intro.
    1: apply H5, set_union_iff; left. apply set_union_iff; auto.
    2: apply IHHt2; auto. 1: apply IHHt1; auto.
    all: intros; apply H5; simpl;
      unfold set_union_pid; repeat rewrite set_union_iff; auto.
  - intros; inversion_clear H8.
    elim (set_union_elim _ _ _ _ H1); intro.
    1: apply H5, set_union_iff; auto.
    apply IHHt; auto.
    intros; apply H5, set_union_iff; auto.
  - intros; apply H0 with X; auto.
  - simpl; simpl in H0, H5, H8; intros.
    elim (set_union_elim _ _ _ _ H3); clear H3; intro H3; eauto.
    apply set_remove'_1 in H3; eauto.
  - simpl; intros; apply H5; simpl.
    apply set_union_iff; elim (set_union_elim _ _ _ _ H3); auto.
    intro. apply set_remove'_1 in a; auto.
  - simpl; intros; apply H5; simpl.
    apply set_union_iff; auto.
}

  (* generalize (MCC_To_within_Xs _ _ _ _ _ _ H' H1); intros. *)
  clear H2 H3. set (H3 := True).
  (* set (H':=H). clearbody H'. *)
  red in H; unfold MCBase.Procs, Vars in H; simpl in H.
  destroy H. clear H2 H7. set (H2 := True). set (H7 := True).
  intros. induction Ht.
  1,2,3,4: apply H5; simpl;
    unfold set_union_pid; repeat rewrite set_union_iff; auto.
  - elim (set_union_elim _ _ _ _ H8); intro.
    1: apply H5, set_union_iff; auto.
    apply IHHt; auto.
    intros. apply H5; simpl.
    unfold set_union_pid; repeat rewrite set_union_iff; auto.
  - elim (set_union_elim _ _ _ _ H8); intro.
    1: elim (set_union_elim _ _ _ _ a); intro.
    1: apply H5, set_union_iff; left. apply set_union_iff; auto.
    2: apply IHHt2; auto. 1: apply IHHt1; auto.
    * intros; simpl; elim (H1 p1); auto.
    * intros. apply H5; simpl.
      unfold set_union_pid; repeat rewrite set_union_iff; auto.
    * intros; simpl; elim (H1 p1); auto; intros.
      inversion H12; auto.
    * intros. apply H5; simpl.
      unfold set_union_pid; repeat rewrite set_union_iff; auto.
  - elim (set_union_elim _ _ _ _ H8); intro.
    1: apply H5, set_union_iff; auto.
    fold MCC_pn in b.
    apply IHHt; auto.
    simpl.
    clear dependent p.
    simpl in H2.



    auto.
 Search In set_union. apply set_union.

  - rewrite <- H16 in H9; simpl in H9.
    apply H0 with r; auto.
  - rewrite <- H16 in H9; simpl in H9.
    elim (set_union_elim _ _ _ _ H9); eauto.
    intro; apply H5 with r; auto; simpl.
    apply set_remove'_1 with P.eq_dec p0; auto.
  - apply IHC; auto. 

inversion H1; clear H1.
rename H into HP, H2 into HC, H0 into HD, H7 into Ht.
destroy HP. unfold MCBase.Procs, Vars in HP.
simpl in H0, HC, HD, HP. rename H0 into HC'.
revert C HC HC' C' s s' t Ht.
induction C; intros; inversion Ht;
  clear dependent s0; clear dependent s'0.
+ red in HD. rewrite Forall_forall in HD.
  simpl. 

simpl in HC'.
projectable_C Defs (fst (Defs X)) (snd (Defs X)) -> projectable_C Defs ps (snd (Defs X))

(* Start of proof for old version.
induction H0.
+ intro; apply (H (p,XUndefined)); auto.
  unfold epp_list in H1; rewrite in_map_iff in H1.
  unfold epp_list; rewrite in_map_iff.
  destroy H1. inversion H3.
  rewrite H5 in H1. simpl in H2. clear x0 H5 H3.
  exists p; simpl. split; auto.
  case Pid_dec; [idtac | case Pid_dec]; simpl; rewrite H6, H2; auto.
+ intro; apply (H (p,XUndefined)); auto.
  unfold epp_list in H1; rewrite in_map_iff in H1.
  unfold epp_list; rewrite in_map_iff.
  destroy H1. inversion H3.
  rewrite H5 in H1. simpl in H2.
  exists p; simpl. split; auto.
  case l; (case Pid_dec; [idtac | case Pid_dec]); simpl; rewrite H6, H2; auto.
+ intro; apply (H (p,XUndefined)); auto.
  unfold epp_list in H1; rewrite in_map_iff in H1.
  unfold epp_list; rewrite in_map_iff.
  destroy H1. inversion H4.
  rewrite H6 in H1. simpl in H3.
  exists p; simpl. split; auto.
  case Pid_dec; simpl. rewrite H7, H3; auto.
  rewrite H3 in H7. rewrite (collapse_merge _ _ H7); auto.
+ intro; apply (H (p,XUndefined)); auto.
  unfold epp_list in H1; rewrite in_map_iff in H1.
  unfold epp_list; rewrite in_map_iff.
  destroy H1. inversion H4.
  rewrite H6 in H1. simpl in H3.
  exists p; simpl. split; auto.
  case Pid_dec; simpl. rewrite H7, H3; auto.
  case (collapse (bproj Defs C1 p)); auto.
  rewrite H3 in H7. rewrite (collapse_merge' _ _ H7); auto.
+ rename p into p'; rename B into B'.
  unfold epp_list in H1; rewrite in_map_iff in H1.  
  destroy H1.
  assert (x = p' /\ collapse (bproj Defs (eta;;C') x) = B').
  1: inversion H3; auto.
  inversion_clear H4. rewrite H5 in H6, H1. clear H5 x H3.
  simpl. rewrite <- H6; clear H6.
  assert (collapse (bproj Defs C' p') <> XUndefined).
  - change (snd (p',collapse (bproj Defs C' p')) <> XUndefined).
    apply IHMCC_To; auto.

  - case eta; intros; simpl;
    case Pid_dec; [idtac | case Pid_dec | case l | case l; case Pid_dec ];
    simpl; try rewrite Xmatch_elim; auto; discriminate.
  - apply IHMCC_To.
    intros; induction x as (p, B).
    simpl; intro.
  - apply (H (p',collapse (bproj Defs (eta;;C) p'))); auto.
    unfold epp_list in H3; rewrite in_map_iff in H3.
    unfold epp_list; rewrite in_map_iff.
    destroy H3. inversion H5.
    rewrite H7 in H3.
    exists p'; split; auto.
    assert (collapse (bproj Defs C p') = XUndefined).
    2: simpl; case eta; (intros; case Pid_dec; [idtac | case Pid_dec]; try case l; simpl); rewrite H5; auto.
    rewrite H7, H2; auto

*)

(* *)
[idtac | case Pid_dec]; simpl; rewrite H7, H3; auto.
+ 

  clear p0 e0 x0 H3 H5 H v H0; simpl in H2.
  exists p; simpl. split; auto.
  unfold Pid_dec; rewrite Pdec.eqb_refl.
  simpl. rewrite H6, H2; auto.
  - unfold epp_list in H1; rewrite in_map_iff in H1.
    unfold epp_list; rewrite in_map_iff.
    destroy H1. inversion H3.
    rewrite H5 in H1; rewrite <- e0.
    clear p0 e0 x0 H3 H5 H v H0; simpl in H2.
    exists p; simpl. split; auto.
    unfold Pid_dec; rewrite Pdec.eqb_refl.
    simpl. rewrite H6, H2; auto.
*)
Abort.


End Projectability.

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

End MoreBranches.

(** Needs: projectability preserved by reduction; characterization of EPP. *)

Lemma EPP_reduces : forall Xs ps P s tl P' s' HP,
  ((P,s) --[tl]--> (P',s'))%MC ->
  exists tl' N', (epp Xs ps P HP,s) --[tl']--> (N',s').
Proof.
intros.
induction P as (D,C), P' as (D',C').
generalize (MCP_To_Defs_stable _ _ _ _ _ _ _ H); intro.
rewrite <- H0 in H; clear D' H0.
inversion H.
clear s'0 H6 C'0 H5 s0 H3 C0 H2 Defs H0 tl H1 H.
inversion HP. simpl in H, H0. destroy H0.
induction H4.
+ exists (forget (R_Com p v q x)).
  exists (Build_Program (epp_D _ _ H1) EmptyNet).



(*
Theorem EPP_Complete : forall P s P' s' tl, projectable P ->
  ((P,s) --[tl]--> (P',s'))%MC ->
  exists N', ...
Proof.
induction P.
*)

(*

More branches is behavioural equivalence.

*)


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

End EPPBase.
