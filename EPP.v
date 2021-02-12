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

(** ** EndPoint projection
  First step: returns an XBehaviour, possibly with XUndefined subcomponents. *)
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

(** For simplifying future definitions. *)
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

Lemma projectable_C_use' : forall Defs ps C, projectable_C Defs ps C ->
  forall p, In p ps -> collapse (bproj Defs C p) <> XUndefined.
Proof.
intros. apply projectable_C_use with (p:=p) in H; auto.
inversion_clear H. rewrite H1.
apply inject_not_undefined.
Qed.

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
apply projectable_C_use' with (p:=p) in H; auto.
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
apply projectable_C_use' with (p:=p) in H; auto.
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

(** Sanity checks: EPP works as defined informally in the paper. *)
Lemma epp_C_Com_p : forall Defs ps C p e q x HC HC', In p ps ->
  epp_C Defs ps (p#e-->q$x;;C) HC p = q!e; epp_C Defs ps C HC' p.
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
revert p0; Peq. simpl; intros.
rewrite p1 in p0. induction x0; inversion p0.
2: case o, o0; inversion p0.
apply inject_inj in H3; rewrite H3; auto.
intro. exfalso. clear p0.
apply projectable_C_use' with (p:=p) in HC'; auto.
simpl. intro; exfalso.
revert b; Peq.
rewrite Xmatch_elim. discriminate.
apply projectable_C_use' with ps; auto.
Qed.

Lemma epp_C_Com_q : forall Defs ps C p e q x HC HC', p <> q -> In q ps ->
  epp_C Defs ps (p#e-->q$x;;C) HC q = p ? x; epp_C Defs ps C HC' q.
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
revert p0; Peq. Pneq H. simpl; intros.
rewrite p1 in p0. induction x0; inversion p0.
2: case o, o0; inversion p0.
apply inject_inj in H4; rewrite H4; auto.
intro. exfalso. clear p0.
apply projectable_C_use' with (p:=q) in HC'; auto.
simpl. intro; exfalso.
revert b; Peq. Pneq H. simpl.
rewrite Xmatch_elim. discriminate.
apply projectable_C_use' with ps; auto.
Qed.

Lemma epp_C_Com_r : forall Defs ps C p e q x HC HC' r, p <> r -> q <> r ->
  epp_C Defs ps (p#e-->q$x;;C) HC r = epp_C Defs ps C HC' r.
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl; auto.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
revert p0. unfold Pid_dec. Pneq H. Pneq H0. intros.
rewrite p1 in p0. apply inject_inj; auto.
intro. exfalso. clear p0.
apply projectable_C_use' with (p:=r) in HC'; auto.
simpl. intro; exfalso.
revert b; unfold Pid_dec. Pneq H. Pneq H0. simpl.
apply projectable_C_use' with ps; auto.
Qed.

Lemma epp_C_Sel_p : forall Defs ps C p q l HC HC', In p ps ->
  epp_C Defs ps (p-->q[l];;C) HC p = q(+)l; epp_C Defs ps C HC' p.
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
revert p0; Peq; simpl; intros.
rewrite p1 in p0; induction x, l; inversion p0.
1,2: apply inject_inj in H3; rewrite H3; auto.
1,2: case o, o0; inversion H1.
intro; exfalso; clear p0.
apply projectable_C_use' with (p:=p) in HC'; auto.
simpl. intro; exfalso.
revert b; Peq.
induction l; simpl; rewrite Xmatch_elim.
1,3: discriminate.
all: apply projectable_C_use' with ps; auto.
Qed.

Lemma epp_C_Sel_ql : forall Defs ps C p q HC HC', p <> q -> In q ps ->
  epp_C Defs ps (p-->q[left];;C) HC q = p & Some (epp_C Defs ps C HC' q) // None.
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
revert p0; Peq. Pneq H. simpl; intros.
rewrite p1 in p0. induction x; inversion p0.
case o, o0; inversion p0.
apply inject_inj in H4; rewrite H4; auto.
intro. exfalso. clear p0.
apply projectable_C_use' with (p:=q) in HC'; auto.
simpl. intro; exfalso.
revert b; Peq. Pneq H. simpl.
rewrite Xmatch_elim. discriminate.
apply projectable_C_use' with ps; auto.
Qed.

Lemma epp_C_Sel_qr : forall Defs ps C p q HC HC', p <> q -> In q ps ->
  epp_C Defs ps (p-->q[right];;C) HC q = p & None // Some (epp_C Defs ps C HC' q).
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
revert p0; Peq. Pneq H. simpl; intros.
rewrite p1 in p0. induction x; inversion p0.
case o, o0; inversion p0.
apply inject_inj in H4; rewrite H4; auto.
intro. exfalso. clear p0.
apply projectable_C_use' with (p:=q) in HC'; auto.
simpl. intro; exfalso.
revert b; Peq. Pneq H. simpl.
rewrite Xmatch_elim. discriminate.
apply projectable_C_use' with ps; auto.
Qed.

Lemma epp_C_Sel_r : forall Defs ps C p q l HC HC' r, p <> r -> q <> r ->
  epp_C Defs ps (p-->q[l];;C) HC r = epp_C Defs ps C HC' r.
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl; auto.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
revert p0. unfold Pid_dec. Pneq H. Pneq H0. intros.
rewrite p1 in p0. apply inject_inj; induction l; auto.
intro. exfalso. clear p0.
apply projectable_C_use' with (p:=r) in HC'; auto.
simpl. intro; exfalso.
revert b; unfold Pid_dec. Pneq H. Pneq H0. simpl.
induction l; apply projectable_C_use' with ps; auto.
Qed.

Lemma epp_C_Cond_p : forall Defs ps p b C1 C2 HC HC1 HC2, In p ps ->
  epp_C Defs ps (If p ?? b Then C1 Else C2) HC p
  = If b Then (epp_C Defs ps C1 HC1 p) Else (epp_C Defs ps C2 HC2 p).
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
+ revert p0. Peq; intros.
  apply inject_inj. simpl. rewrite <- p1, <- p2; auto.
+ intro; exfalso. revert p0.
  Peq. apply projectable_C_use' with (p:=p) in HC2; auto.
+ intro; exfalso. revert p0.
  Peq. apply projectable_C_use' with (p:=p) in HC1; auto.
+ intro; exfalso. revert b0.
  Peq. repeat rewrite Xmatch_elim.
  discriminate.
  apply projectable_C_use' with (p:=p) in HC2; auto.
  apply projectable_C_use' with (p:=p) in HC1; auto.
Qed.

Lemma epp_C_Cond_r : forall Defs ps p b C1 C2 HC HC1 HC2 r, p <> r ->
  inject (epp_C Defs ps (If p ?? b Then C1 Else C2) HC r)
  = merge (epp_C Defs ps C1 HC1 r) (epp_C Defs ps C2 HC2 r).
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl; unfold Pid_dec. 2: tauto.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
+ revert p0. Pneq H; intros.
  rewrite p1, p2 in p0; auto.
+ intro; exfalso. revert p0.
  Pneq H. apply projectable_C_use' with (p:=r) in HC2; auto.
+ intro; exfalso. revert p0.
  Pneq H. apply projectable_C_use' with (p:=r) in HC1; auto.
+ intro; exfalso. apply projectable_C_use' with (p:=r) in HC; auto.
Qed.

(*
Lemma epp_C_Then_r : forall Defs ps p b C1 C2 HC HC1 HC2 r, p <> r ->
  epp_C Defs ps C1 HC1 r = epp_C Defs ps C2 HC2 r ->
  epp_C Defs ps (If p ?? b Then C1 Else C2) HC r = epp_C Defs ps C1 HC1 r.
Proof.
intros.
apply inject_inj. rewrite epp_C_Cond_r with (HC1:=HC1) (HC2:=HC2); auto.
rewrite H0. apply merge_idempotent.
Qed.

Lemma epp_C_Else_r : forall Defs ps p b C1 C2 HC HC1 HC2 r, p <> r ->
  epp_C Defs ps C1 HC1 r = epp_C Defs ps C2 HC2 r ->
  epp_C Defs ps (If p ?? b Then C1 Else C2) HC r = epp_C Defs ps C2 HC2 r.
Proof.
intros.
rewrite epp_C_Then_r with (HC1:=HC1) (HC2:=HC2); auto.
Qed.
*)

Lemma epp_C_Call : forall Defs ps X p HC, In p ps -> In p (fst (Defs X)) ->
  epp_C Defs ps (CCBase.Call X) HC p = Call (X,p).
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim collapse_char'. induction a0; simpl.
revert p0. elim In_dec; intros.
induction x; auto; inversion p0.
case o, o0; inversion p0.
auto. tauto.
intro. exfalso.
revert b. elim in_dec; discriminate.
Qed.

Lemma epp_C_Call_out : forall Defs ps X p HC, ~In p (fst (Defs X)) ->
  epp_C Defs ps (CCBase.Call X) HC p = End.
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim collapse_char'. induction a0; simpl.
revert p0. elim In_dec; intros. tauto.
induction x; auto; inversion p0.
case o, o0; inversion p0.
intro. exfalso.
revert b. elim in_dec; discriminate.
Qed.

Lemma epp_C_RT_Call : forall Defs ps X p ps' C HC, In p ps -> In p ps' ->
  epp_C Defs ps (RT_Call X ps' C) HC p = Call (X,p).
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim collapse_char'. induction a0; simpl.
revert p0. elim In_dec; intros.
induction x; auto; inversion p0.
case o, o0; inversion p0.
auto. tauto.
intro. exfalso.
revert b. elim in_dec; auto. discriminate.
Qed.

Lemma epp_C_RT_Call_out : forall Defs ps X p ps' C HC HC', ~In p ps' ->
  epp_C Defs ps (RT_Call X ps' C) HC p = epp_C Defs ps C HC' p.
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
revert p0. elim In_dec; intros. tauto.
apply inject_inj; transitivity (bproj Defs C p); auto.
intro. exfalso.
revert p0. elim in_dec; auto.
intros. rewrite p0, collapse_inject in b.
eapply inject_not_undefined; eauto.
intro; exfalso. revert b.
elim In_dec; auto.
intros. apply projectable_C_use' with (p:=p) in HC'; auto.
Qed.

Lemma epp_C_End : forall Defs ps p HC,
  epp_C Defs ps CCBase.End HC p = End.
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim collapse_char'. induction a0; simpl.
induction x; auto; inversion p0.
case o, o0; inversion p0.
discriminate.
Qed.

(** Strange characterizations lemmas for branching. *)
Lemma bproj_not_Branching_None_None : forall Defs C r q,
  bproj Defs C r <> inject (q & None // None).
Proof.
intros. induction C; simpl. induction e. 2: induction l.
1,2,3,4: elim Pid_dec.
2,4,6: elim Pid_dec.
12,13: elim In_dec.
all: auto.
all: try discriminate.
intro. 
apply Xmerge_inv_Branching in H; destroy H.
clear H4 H.
elim H2; auto. clear H2; intros.
elim H3; auto. clear H3; intros.
apply IHC1. rewrite H, H3 in H0; auto.
Qed.

Lemma epp_C_not_Branching_None_None : forall Defs ps C HC p q,
  epp_C Defs ps C HC p <> q & None // None.
Proof.
intros.
unfold epp_C.
elim In_dec; intro; simpl. 2: discriminate.
elim collapse_char'; intro; simpl.
induction a0. intro. rewrite H in p0.
clear H x a HC ps.
revert p0. apply bproj_not_Branching_None_None.
exfalso. apply projectable_C_use' with (p:=p) in HC; auto.
Qed.

Lemma bproj_Sel_Branching_l : forall Defs C p q Bp Bl Br,
  bproj Defs C p = XSel q left Bp ->
  bproj Defs C q = XBranching p Bl Br -> Bl <> None /\ Br = None.
Proof.
induction C; simpl; intros; revert H H0; try discriminate.
induction e. 2: induction l.
1,2,3,4: case_eq (Pid_dec p0 p); intro; try discriminate.
1,2,3,4: case_eq (Pid_dec p0 q); intro; try discriminate.
1,3,4: case_eq (Pid_dec p1 p); intro; try discriminate.
1,2,3,4: case_eq (Pid_dec p1 q); intro; try discriminate.
8,9: case_eq (Pid_dec p p0); intro; try discriminate.
8,9: case_eq (Pid_dec p q); intro; try discriminate.
10,11: elim in_dec; intro; try discriminate.
10: elim in_dec; intro; try discriminate.
all: eauto; intros.
+ inversion H4; split; auto. discriminate.
+ inversion H4. exfalso.
  unfold Pid_dec in H. rewrite Pdec.eqb_neq in H. auto.
+ inversion H3; split; auto. discriminate.
+ inversion H2. exfalso.
  unfold Pid_dec in H1. rewrite Pdec.eqb_neq in H1. auto.
+ exfalso. unfold Pid_dec in H, H0.
  rewrite Pdec.eqb_neq in H0. rewrite Pdec.eqb_eq in H. auto.
+ clear p H H0 H1. rename p0 into p.
  apply Xmerge_inv_Sel in H2. destroy H2.
  rename x into B1, x0 into B2.
  apply Xmerge_inv_Branching in H3. destroy H3.
  rename x into B1l, x1 into B1r, x0 into B2l, x2 into B2r.
  elim (IHC1 _ _ _ _ _ H H1); intros.
  elim (IHC2 _ _ _ _ _ H0 H4); intros.
  split. intro. tauto.
  induction Br; auto.
  elim (H3 a); auto. intro. exfalso.
  apply H12 in H9. rewrite H9 in H11; inversion H11.
Qed.

Lemma epp_C_Sel_Branching_l : forall Defs ps C HC p q Bp Bl Br,
  epp_C Defs ps C HC p = q (+) left; Bp ->
  epp_C Defs ps C HC q = p & Bl // Br ->
  Bl <> None /\ Br = None.
Proof.
intros.
revert H H0. unfold epp_C.
elim In_dec. 2: discriminate.
elim In_dec. 2: discriminate.
elim (collapse_char'); intro Hc. induction Hc.
elim (collapse_char'); intro Hc. induction Hc.
simpl; intros.
rewrite H in p0; rewrite H0 in p1. simpl in p0.
induction Bl, Br; simpl in p1.
2: split; auto; discriminate.
1,2,3: elim (bproj_Sel_Branching_l _ _ _ _ _ _ _ p0 p1);
  simpl; intros. inversion H2. inversion H2. auto.
simpl. intro. exfalso. apply projectable_C_use' with (p:=q) in HC; auto.
simpl. intro. intro. exfalso. apply projectable_C_use' with (p:=p) in HC; auto.
Qed.

Lemma bproj_Sel_Branching_r : forall Defs C p q Bp Bl Br,
  bproj Defs C p = XSel q right Bp ->
  bproj Defs C q = XBranching p Bl Br -> Bl = None /\ Br <> None.
Proof.
induction C; simpl; intros; revert H H0; try discriminate.
induction e. 2: induction l.
1,2,3,4: case_eq (Pid_dec p0 p); intro; try discriminate.
1,2,3,4: case_eq (Pid_dec p0 q); intro; try discriminate.
1,2,4: case_eq (Pid_dec p1 p); intro; try discriminate.
1,2,3,4: case_eq (Pid_dec p1 q); intro; try discriminate.
8,9: case_eq (Pid_dec p p0); intro; try discriminate.
8,9: case_eq (Pid_dec p q); intro; try discriminate.
10,11: elim in_dec; intro; try discriminate.
10: elim in_dec; intro; try discriminate.
all: eauto; intros.
+ inversion H4. exfalso.
  unfold Pid_dec in H. rewrite Pdec.eqb_neq in H. auto.
+ inversion H4; split; auto. discriminate.
+ inversion H3; split; auto. discriminate.
+ inversion H2. exfalso.
  unfold Pid_dec in H1. rewrite Pdec.eqb_neq in H1. auto.
+ exfalso. unfold Pid_dec in H, H0.
  rewrite Pdec.eqb_neq in H0. rewrite Pdec.eqb_eq in H. auto.
+ clear p H H0 H1. rename p0 into p.
  apply Xmerge_inv_Sel in H2. destroy H2.
  rename x into B1, x0 into B2.
  apply Xmerge_inv_Branching in H3. destroy H3.
  rename x into B1l, x1 into B1r, x0 into B2l, x2 into B2r.
  elim (IHC1 _ _ _ _ _ H H1); intros.
  elim (IHC2 _ _ _ _ _ H0 H4); intros.
  split. 2: intro; tauto.
  induction Bl; auto.
  elim (H7 a); auto. intro. exfalso.
  apply H12 in H8. rewrite H8 in H10; inversion H10.
Qed.

Lemma epp_C_Sel_Branching_r : forall Defs ps C HC p q Bp Bl Br,
  epp_C Defs ps C HC p = q (+) right; Bp ->
  epp_C Defs ps C HC q = p & Bl // Br ->
  Bl = None /\ Br <> None.
Proof.
intros.
revert H H0. unfold epp_C.
elim In_dec. 2: discriminate.
elim In_dec. 2: discriminate.
elim (collapse_char'); intro Hc. induction Hc.
elim (collapse_char'); intro Hc. induction Hc.
simpl; intros.
rewrite H in p0; rewrite H0 in p1. simpl in p0.
induction Bl, Br; simpl in p1.
3: split; auto; discriminate.
1,2,3: elim (bproj_Sel_Branching_r _ _ _ _ _ _ _ p0 p1);
  simpl; intros. inversion H1. inversion H1. auto.
simpl. intro. exfalso. apply projectable_C_use' with (p:=q) in HC; auto.
simpl. intro. intro. exfalso. apply projectable_C_use' with (p:=p) in HC; auto.
Qed.

(** Strange inversion lemmas for conditionals. *)
Lemma epp_C_Cond_Send_inv : forall Defs ps p b C1 C2 HC HC1 HC2 r q e B,
  epp_C Defs ps (If p ?? b Then C1 Else C2) HC r = q ! e; B ->
  exists B1 B2, epp_C Defs ps C1 HC1 r = q ! e; B1
  /\ epp_C Defs ps C2 HC2 r = q ! e; B2 /\ merge B1 B2 = inject B.
Proof.
intros.
assert (p <> r).
1: {
  intro. revert HC H; rewrite H0. intro.
  elim (In_dec P.eq_dec r ps); intro.
  rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2); auto. discriminate.
  rewrite epp_C_out; auto. discriminate.
}
generalize (epp_C_Cond_r _ _ _ _ _ _ HC HC1 HC2 _ H0); intros.
rewrite H in H1.
apply merge_inv_Send; auto.
Qed.

Lemma epp_C_Cond_Recv_inv : forall Defs ps p b C1 C2 HC HC1 HC2 r q x B,
  epp_C Defs ps (If p ?? b Then C1 Else C2) HC r = q ? x; B ->
  exists B1 B2, epp_C Defs ps C1 HC1 r = q ? x; B1
  /\ epp_C Defs ps C2 HC2 r = q ? x; B2 /\ merge B1 B2 = inject B.
Proof.
intros.
assert (p <> r).
1: {
  intro. revert HC H; rewrite H0. intro.
  elim (In_dec P.eq_dec r ps); intro.
  rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2); auto. discriminate.
  rewrite epp_C_out; auto. discriminate.
}
generalize (epp_C_Cond_r _ _ _ _ _ _ HC HC1 HC2 _ H0); intros.
rewrite H in H1.
apply merge_inv_Recv; auto.
Qed.

Lemma epp_C_Cond_Sel_inv : forall Defs ps p b C1 C2 HC HC1 HC2 r q l B,
  epp_C Defs ps (If p ?? b Then C1 Else C2) HC r = q (+) l; B ->
  exists B1 B2, epp_C Defs ps C1 HC1 r = q (+) l; B1
  /\ epp_C Defs ps C2 HC2 r = q (+) l; B2 /\ merge B1 B2 = inject B.
Proof.
intros.
assert (p <> r).
1: {
  intro. revert HC H; rewrite H0. intro.
  elim (In_dec P.eq_dec r ps); intro.
  rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2); auto. discriminate.
  rewrite epp_C_out; auto. discriminate.
}
generalize (epp_C_Cond_r _ _ _ _ _ _ HC HC1 HC2 _ H0); intros.
rewrite H in H1.
apply merge_inv_Sel; auto.
Qed.

Lemma epp_C_Cond_Branching_l_inv : forall Defs ps p b C1 C2 HC HC1 HC2 r q B,
  epp_C Defs ps (If p ?? b Then C1 Else C2) HC r = q & Some B // None ->
  exists B1 B2, epp_C Defs ps C1 HC1 r = q & Some B1 // None
  /\ epp_C Defs ps C2 HC2 r = q & Some B2 // None /\ merge B1 B2 = inject B.
Proof.
intros.
assert (p <> r).
1: {
  intro. revert HC H; rewrite H0. intro.
  elim (In_dec P.eq_dec r ps); intro.
  rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2); auto. discriminate.
  rewrite epp_C_out; auto. discriminate.
}
generalize (epp_C_Cond_r _ _ _ _ _ _ HC HC1 HC2 _ H0); intros.
rewrite H in H1.
symmetry in H1. apply merge_inv_Branching_Some_None in H1.
inversion_clear H1; inversion_clear H2.
1: elim (epp_C_not_Branching_None_None _ _ _ _ _ _ H1).
1: inversion_clear H1. elim (epp_C_not_Branching_None_None _ _ _ _ _ _ H3).
destroy H1. eauto.
Qed.

Lemma epp_C_Cond_Branching_r_inv : forall Defs ps p b C1 C2 HC HC1 HC2 r q B,
  epp_C Defs ps (If p ?? b Then C1 Else C2) HC r = q & None // Some B ->
  exists B1 B2, epp_C Defs ps C1 HC1 r = q & None // Some B1
  /\ epp_C Defs ps C2 HC2 r = q & None // Some B2 /\ merge B1 B2 = inject B.
Proof.
intros.
assert (p <> r).
1: {
  intro. revert HC H; rewrite H0. intro.
  elim (In_dec P.eq_dec r ps); intro.
  rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2); auto. discriminate.
  rewrite epp_C_out; auto. discriminate.
}
generalize (epp_C_Cond_r _ _ _ _ _ _ HC HC1 HC2 _ H0); intros.
rewrite H in H1.
symmetry in H1. apply merge_inv_Branching_None_Some in H1.
inversion_clear H1; inversion_clear H2.
1: elim (epp_C_not_Branching_None_None _ _ _ _ _ _ H1).
1: inversion_clear H1. elim (epp_C_not_Branching_None_None _ _ _ _ _ _ H3).
destroy H1. eauto.
Qed.


End EPP.

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
Lemma projectable_C_inv_Com : forall Defs ps p e q x C,
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

Lemma projectable_C_inv_Sel : forall Defs ps p q l C,
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

Lemma projectable_C_inv_Eta : forall Defs ps eta C,
  projectable_C Defs ps (eta;; C) -> projectable_C Defs ps C.
Proof.
intros; induction eta.
eapply projectable_C_inv_Com; eauto.
eapply projectable_C_inv_Sel; eauto.
Qed.

Lemma projectable_C_inv_Then : forall Defs ps p b C1 C2,
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

Lemma projectable_C_inv_Else : forall Defs ps p b C1 C2,
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
  - apply projectable_C_inv_Com in H0; eauto.
  - apply projectable_C_inv_Sel in H0; eauto.
+ inversion_clear H. repeat split.
  - apply projectable_C_inv_Then in H0; eauto.
  - apply projectable_C_inv_Else in H0; eauto.
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

(** Inversion lemmas for strong projectability. *)
Lemma strongly_projectable_inv_Eta : forall Defs eta C p,
  strongly_projectable Defs (eta;;C) p -> strongly_projectable Defs C p.
Proof. auto. Qed.

Lemma strongly_projectable_inv_Then : forall Defs p b C1 C2 r,
  strongly_projectable Defs (If p ?? b Then C1 Else C2) r ->
  strongly_projectable Defs C1 r.
Proof. intros. destroy H. auto. Qed.

Lemma strongly_projectable_inv_Else : forall Defs p b C1 C2 r,
  strongly_projectable Defs (If p ?? b Then C1 Else C2) r ->
  strongly_projectable Defs C2 r.
Proof. intros. destroy H. auto. Qed.

Lemma strongly_projectable_inv_RT_Call : forall Defs ps X C p,
  strongly_projectable Defs (RT_Call ps X C) p ->
  strongly_projectable Defs C p.
Proof. intros. destroy H. auto. Qed.

(** Inversion lemmas about program projectability. *)
Lemma projectable_inv_Eta : forall Xs ps Defs eta C,
  projectable Xs ps (CCBase.Build_Program Defs (eta;;C)) ->
  projectable Xs ps (CCBase.Build_Program Defs C).
Proof.
intros.
destroy H; repeat split; auto.
apply projectable_C_inv_Eta with eta; auto.
intros. apply H2; simpl. sup.
Qed.

Lemma projectable_inv_Com : forall Xs ps Defs p e q x C,
  projectable Xs ps (CCBase.Build_Program Defs (p#e-->q$x;;C)) ->
  projectable Xs ps (CCBase.Build_Program Defs C).
Proof. intros; eapply projectable_inv_Eta; eauto. Qed.

Lemma projectable_inv_Sel : forall Xs ps Defs p q l C,
  projectable Xs ps (CCBase.Build_Program Defs (p-->q[l];;C)) ->
  projectable Xs ps (CCBase.Build_Program Defs C).
Proof. intros; eapply projectable_inv_Eta; eauto. Qed.

Lemma projectable_inv_Then : forall Xs ps Defs p b C1 C2,
  projectable Xs ps (CCBase.Build_Program Defs (If p ?? b Then C1 Else C2)) ->
  projectable Xs ps (CCBase.Build_Program Defs C1).
Proof.
intros.
destroy H; repeat split; auto.
apply projectable_C_inv_Then with p b C2; auto.
intros. apply H2; simpl. sup; sup.
Qed.

Lemma projectable_inv_Else : forall Xs ps Defs p b C1 C2,
  projectable Xs ps (CCBase.Build_Program Defs (If p ?? b Then C1 Else C2)) ->
  projectable Xs ps (CCBase.Build_Program Defs C2).
Proof.
intros.
destroy H; repeat split; auto.
apply projectable_C_inv_Else with p b C1; auto.
intros. apply H2; simpl. sup; sup.
Qed.

Lemma projectable_inv_RT_Call : forall Xs ps Defs X p ps' C,
  projectable Xs ps (CCBase.Build_Program Defs (RT_Call X ps' C)) ->
  collapse (bproj Defs C p) <> XUndefined ->
  projectable Xs ps (CCBase.Build_Program Defs (RT_Call X (set_remove_pid p ps') C)).
Proof.
intros.
destroy H; repeat split; auto.
+ clear H H4 H3 H2.
  intros. red; red in H1.
  rewrite Forall_forall; rewrite Forall_forall in H1.
  intros. induction x as (r,B). intro.
  apply (H1 (r,XUndefined)); auto.
  unfold epp_list in H; rewrite in_map_iff in H.
  unfold epp_list; rewrite in_map_iff.
  destroy H. inversion H3.
  rewrite H5 in H. simpl in H2. clear x H5 H3.
  exists r; simpl. split; auto.
  revert H6. case In_dec; case In_dec; simpl; intros.
  - rewrite H6, H2; auto.
  - elim n; eapply set_remove'_1; eauto.
  - rewrite H2 in H6. elim H0.
    rewrite <- (set_remove'_out P.eq_dec r p ps'); auto.
  - rewrite H6, H2; auto.
+ intro r. simpl; sup.
  intros. apply H3; simpl. sup.
  elim H5; auto.
  left. eapply set_remove'_1; eauto.
Qed.

(** Miscellaneous. *)
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

End Projectability.

Section Completeness.

(** ** Completeness of EPP
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

(** Projectability of well-formed programs is preserved by reductions. *)
Lemma projectable_C_reduces_Com : forall Defs ps C s C' s' p v q x,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  CCC_To Defs C s (CCBase.TL.R_Com p v q x) C' s' ->
  projectable_C Defs ps C'.
Proof.
intros.
red. rewrite Forall_forall; intro.
induction x0 as (r,B). unfold epp_list; rewrite in_map_iff.
simpl; intros. destroy H1. inversion H2.
rewrite H4 in H1; clear x0 H4 H2 B H5.
generalize (strongly_projectable_C _ _ _ (H _ H1)); intro.
elim (P.eq_dec p r); intro Hpr. 2: elim (P.eq_dec q r); intro Hqr.
+ rewrite Hpr in H0; clear p Hpr.
  elim (bproj_reduce_Com_p _ _ _ _ _ _ _ _ _ (H _ H1) H0).
  intros. destroy H3. intro.
  rewrite H4 in H2. simpl in H2.
  rewrite <- H5, H6 in H2. auto.
+ rewrite Hqr in H0; clear q Hqr.
  elim (bproj_reduce_Com_q _ _ _ _ _ _ _ _ _ (H _ H1) H0); auto.
  intros. destroy H3. intro.
  rewrite H4 in H2. simpl in H2.
  rewrite <- H3, H5 in H2. auto.
+ rewrite (bproj_reduce_Com_r _ _ _ _ _ _ _ _ _ _ (H _ H1) H0); auto.
Qed.

Lemma projectable_C_reduces_Sel : forall Defs ps C s C' s' p q l,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  CCC_To Defs C s (CCBase.TL.R_Sel p q l) C' s' ->
  projectable_C Defs ps C'.
Proof.
intros.
red. rewrite Forall_forall; intro.
induction x as (r,B). unfold epp_list; rewrite in_map_iff.
simpl; intros. destroy H1. inversion H2.
rewrite H4 in H1; clear x H4 H2 B H5.
generalize (strongly_projectable_C _ _ _ (H _ H1)); intro.
elim (P.eq_dec p r); intro Hpr. 2: elim (P.eq_dec q r); intro Hqr.
+ rewrite Hpr in H0; clear p Hpr.
  elim (bproj_reduce_Sel_p _ _ _ _ _ _ _ _ (H _ H1) H0).
  intros. destroy H3. intro.
  rewrite H4 in H2. simpl in H2.
  rewrite <- H3, H5 in H2. auto.
+ rewrite Hqr in H0; clear q Hqr.
  induction l.
  - elim (bproj_reduce_Sel_ql _ _ _ _ _ _ _ (H _ H1) H0); auto.
    intros. destroy H3. intro.
    rewrite H4 in H2. simpl in H2.
    rewrite <- H3, H5 in H2. auto.
  - elim (bproj_reduce_Sel_qr _ _ _ _ _ _ _ (H _ H1) H0); auto.
    intros. destroy H3. intro.
    rewrite H4 in H2. simpl in H2.
    rewrite <- H3, H5 in H2. auto.
+ rewrite (bproj_reduce_Sel_r _ _ _ _ _ _ _ _ _ (H _ H1) H0); auto.
Qed.

Lemma projectable_C_reduces_Cond : forall Defs ps C s C' s' p,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  CCC_To Defs C s (CCBase.TL.R_Cond p) C' s' ->
  projectable_C Defs ps C'.
Proof.
intros.
red. rewrite Forall_forall; intro.
induction x as (r,B). unfold epp_list; rewrite in_map_iff.
simpl; intros. destroy H1. inversion H2.
rewrite H4 in H1; clear x H4 H2 B H5.
generalize (strongly_projectable_C _ _ _ (H _ H1)); intro.
elim (P.eq_dec p r); intro Hpr.
+ rewrite Hpr in H0; clear p Hpr.
  elim (bproj_reduce_Cond_p _ _ _ _ _ _ (H _ H1) H0).
  intros. destroy H3. intro.
  rewrite H4 in H2. simpl in H2.
  case_eq (CCBase.beval_on_state x s r); intro.
  rewrite <- H5, H6 in H2; auto.
  rewrite <- H3, H6 in H2; auto.
  induction (collapse x0); auto.
+ generalize (bproj_reduce_Cond_r _ _ _ _ _ _ _ (H _ H1) H0 Hpr); intros.
  destroy H3. rewrite H5, collapse_inject. apply inject_not_undefined.
Qed.

Lemma projectable_C_reduces_Call : forall Defs ps C s C' s' X p Xs,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  (forall p Y, In p ps -> In Y Xs -> strongly_projectable Defs (snd (Defs Y)) p) ->
  (forall Y, set_incl_pid (CCC_pn (snd (Defs Y)) (fun Z => fst (Defs Z))) (fst (Defs Y))) ->
  In X Xs -> CCC_To Defs C s (CCBase.TL.R_Call X p) C' s' ->
  projectable_C Defs ps C'.
Proof.
intros Defs ps C s C' s' X p Xs H H' H'' HX H0.
red. rewrite Forall_forall; intro.
induction x as (r,B). unfold epp_list; rewrite in_map_iff.
simpl; intros. destroy H1. inversion H2.
rewrite H4 in H1; clear x H4 H2 B H5.
generalize (strongly_projectable_C _ _ _ (H _ H1)); intro.
elim (P.eq_dec p r); intro Hpr.
+ rewrite Hpr in H0; clear p Hpr.
  elim (bproj_reduce_Call_p Defs C s C' s' r X Xs); auto.
  intros; intro. destroy H4.
  rewrite H7, collapse_inject in H5. apply (inject_not_undefined x0); auto.
+ rewrite (bproj_reduce_Call_r Defs C s C' s' p X); auto.
Qed.

Lemma projectable_C_reduces : forall Defs ps C s C' s' t Xs,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  (forall p Y, In p ps -> In Y Xs -> strongly_projectable Defs (snd (Defs Y)) p) ->
  (forall Y, set_incl_pid (CCC_pn (snd (Defs Y)) (fun Z => fst (Defs Z))) (fst (Defs Y))) ->
  (forall p X, In X Xs -> In p (fst (Defs X)) -> In p ps) ->
  within_Xs Xs C -> CCC_To Defs C s t C' s' -> projectable_C Defs ps C'.
Proof.
induction t; intros.
eapply projectable_C_reduces_Com; eauto.
eapply projectable_C_reduces_Sel; eauto.
eapply projectable_C_reduces_Cond; eauto.
eapply projectable_C_reduces_Call; eauto.
eapply CCC_To_Xs; eauto.
Qed.

Lemma projectable_reduces : forall P Xs ps,
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
+ destroy H1.
  apply projectable_C_reduces with C s s' t Xs; auto.
  - simpl. intro r; intros.
    elim (In_dec P.eq_dec r (CCC_pn (snd (Defs Y)) (fun X : CCBase.RecVar => fst (Defs X)))); intro.
    * apply initial_strongly_projectable with (fst (Defs Y)); auto.
      destroy H. elim (H Y); tauto.
      red in H4; rewrite Forall_forall in H4; auto.
      apply H0; auto.
    * apply initial_strongly_projectable'; auto.
      destroy H. elim (H Y); tauto.
  - destroy H; auto.
+ apply H1.
+ simpl. intros. elim (CCC_To_pn' _ _ _ _ _ _ Ht p); intros; auto.
  - destroy H4. apply HDefs with x.
    destroy H. apply within_Xs_char with C; auto.
    apply H0; auto.
  - eapply CCC_pn_mon; eauto.
    simpl. intros. inversion H4.
+ apply H1.
Qed.

(** Strong projectability of well-formed programs is preserved by reductions
  - this is needed for chaining applications of the EPP theorem. *)
Lemma strongly_projectable_reduces_Com : forall Defs C s C' s' ps p v q x r,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) ->
  In r ps ->
  CCC_To Defs C s (CCBase.TL.R_Com p v q x) C' s' ->
  strongly_projectable Defs C' r.
Proof.
intros.
rename H into H0, H1 into Hr, H0 into Hnames, H2 into H.
revert C H0 Hnames r Hr C' H.
induction C; intros; inversion H.
+ rewrite <- H4; apply H0; auto.
+ simpl; apply IHC; auto.
  intros. apply Hnames. simpl; sup.
+ elim (H0 r); auto; intros. inversion_clear H13.
  assert (strongly_projectable Defs C1' r).
    apply IHC1; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  assert (strongly_projectable Defs C2' r).
    apply IHC2; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  repeat split; auto.
  destroy H9.
  simpl. case_eq (Pid_dec p0 r); intro.
  2: elim (P.eq_dec p r); intro Hpr.
  3: elim (P.eq_dec q r); intro Hqr.
  - apply strongly_projectable_C in H13.
    apply strongly_projectable_C in H16.
    simpl. repeat rewrite Xmatch_elim; auto. discriminate.
  - rewrite Hpr in H10, H11.
    elim (bproj_reduce_Com_p _ _ _ _ _ _ _ _ _ H12 H10); intros.
    destroy H19. rename x0 into e, x1 into B1. clear H19.
    elim (bproj_reduce_Com_p _ _ _ _ _ _ _ _ _ H14 H11); intros.
    destroy H19. rename x0 into e', x1 into B2. clear H19.
    rewrite H21, H23.
    generalize (H0 r Hr); clear H0; intro.
    apply strongly_projectable_C in H0; revert H0.
    simpl. rewrite H20, H22.
    rewrite H18.
    simpl. Peq. elim Expr_dec; auto.
    intros; intro.
    elim (XUndefined_dec (Xmerge B1 B2)); intro.
    rewrite a in H0. auto.
    rewrite Xmatch_elim in H0; auto.
    simpl in H0; rewrite H19 in H0. auto.
  - rewrite Hqr in H10, H11.
    elim (bproj_reduce_Com_q _ _ _ _ _ _ _ _ _ H12 H10); auto; intros.
    destroy H19. rename x0 into B1.
    elim (bproj_reduce_Com_q _ _ _ _ _ _ _ _ _ H14 H11); auto; intros.
    destroy H21. rename x0 into B2.
    rewrite H21, H19.
    generalize (H0 r Hr); clear H0; intro.
    apply strongly_projectable_C in H0; revert H0.
    simpl. rewrite H20, H22.
    rewrite H18.
    simpl. Peq. Veq.
    intros; intro.
    elim (XUndefined_dec (Xmerge B1 B2)); intro.
    rewrite a in H0. auto.
    rewrite Xmatch_elim in H0; auto.
    simpl in H0; rewrite H23 in H0. auto.
  - rewrite (bproj_reduce_Com_r _ _ _ _ _ _ _ _ _ _ H12 H10); auto.
    rewrite (bproj_reduce_Com_r _ _ _ _ _ _ _ _ _ _ H14 H11); auto.
    intro; apply H15.
    simpl. rewrite H18; auto.
+ destroy H0.
  rewrite <- H1 in H0, Hnames, H, H6. rewrite <- H1.
  clear r H1. rename r0 into r.
  repeat split; auto.
  apply IHC; auto. apply H0.
  intros; apply Hnames. simpl. sup.
  elim (H0 r); auto. intros. elim (H11 p0); auto.
  apply CCBase.TL.disjoint_ps_rl_In with (p:=p0) in H8; auto.
  destroy H8.
  rewrite (bproj_reduce_Com_r Defs C s C'0 s' p q v x); auto.
  elim (H0 r); auto. intros. elim (H12 p0); auto.
  apply H0. apply Hnames. simpl. sup.
Qed.

Lemma strongly_projectable_reduces_Sel : forall Defs C s C' s' ps p q l r,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) ->
  In r ps ->
  CCC_To Defs C s (CCBase.TL.R_Sel p q l) C' s' ->
  strongly_projectable Defs C' r.
Proof.
intros.
rename H into H0, H1 into Hr, H0 into Hnames, H2 into H.
revert C H0 Hnames r Hr C' H.
induction C; intros; inversion H.
+ rewrite <- H4; apply H0; auto.
+ simpl; apply IHC; auto.
  intros. apply Hnames. simpl; sup.
+ elim (H0 r); auto; intros. inversion_clear H13.
  assert (strongly_projectable Defs C1' r).
    apply IHC1; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  assert (strongly_projectable Defs C2' r).
    apply IHC2; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  repeat split; auto.
  destroy H9.
  simpl. case_eq (Pid_dec p0 r); intro.
  2: elim (P.eq_dec p r); intro Hpr.
  3: elim (P.eq_dec q r); intro Hqr.
  3: induction l.
  - apply strongly_projectable_C in H13.
    apply strongly_projectable_C in H16.
    simpl. repeat rewrite Xmatch_elim; auto. discriminate.
  - rewrite Hpr in H10, H11.
    elim (bproj_reduce_Sel_p _ _ _ _ _ _ _ _ H12 H10); intros.
    destroy H19. rename x into B1.
    elim (bproj_reduce_Sel_p _ _ _ _ _ _ _ _ H14 H11); intros.
    destroy H21. rename x into B2.
    rewrite H21, H19.
    generalize (H0 r Hr); clear H0; intro.
    apply strongly_projectable_C in H0; revert H0.
    simpl. rewrite H20, H22.
    rewrite H18.
    simpl. Peq. rewrite label_eqb_refl.
    intros; intro.
    elim (XUndefined_dec (Xmerge B1 B2)); intro.
    rewrite a in H0. auto.
    rewrite Xmatch_elim in H0; auto.
    simpl in H0; rewrite H23 in H0. auto.
  - rewrite Hqr in H10, H11.
    elim (bproj_reduce_Sel_ql _ _ _ _ _ _ _ H12 H10); auto; intros.
    destroy H19. rename x into B1.
    elim (bproj_reduce_Sel_ql _ _ _ _ _ _ _ H14 H11); auto; intros.
    destroy H21. rename x into B2.
    rewrite H21, H19.
    generalize (H0 r Hr); clear H0; intro.
    apply strongly_projectable_C in H0; revert H0.
    simpl. rewrite H20, H22.
    rewrite H18.
    simpl. Peq.
    intros; intro.
    elim (XUndefined_dec (Xmerge B1 B2)); intro.
    rewrite a in H0. auto.
    rewrite Xmatch_elim in H0; auto.
    simpl in H0; rewrite H23 in H0. auto.
  - rewrite Hqr in H10, H11.
    elim (bproj_reduce_Sel_qr _ _ _ _ _ _ _ H12 H10); auto; intros.
    destroy H19. rename x into B1.
    elim (bproj_reduce_Sel_qr _ _ _ _ _ _ _ H14 H11); auto; intros.
    destroy H21. rename x into B2.
    rewrite H21, H19.
    generalize (H0 r Hr); clear H0; intro.
    apply strongly_projectable_C in H0; revert H0.
    simpl. rewrite H20, H22.
    rewrite H18.
    simpl. Peq.
    intros; intro.
    elim (XUndefined_dec (Xmerge B1 B2)); intro.
    rewrite a in H0. auto.
    rewrite Xmatch_elim in H0; auto.
    simpl in H0; rewrite H23 in H0. auto.
  - rewrite (bproj_reduce_Sel_r _ _ _ _ _ _ _ _ _ H12 H10); auto.
    rewrite (bproj_reduce_Sel_r _ _ _ _ _ _ _ _ _ H14 H11); auto.
    intro; apply H15.
    simpl. rewrite H18; auto.
+ destroy H0.
  rewrite <- H1 in H0, Hnames, H, H6. rewrite <- H1.
  clear r H1. rename r0 into r.
  repeat split; auto.
  apply IHC; auto. apply H0.
  intros; apply Hnames. simpl. sup.
  elim (H0 r); auto. intros. elim (H11 p0); auto.
  apply CCBase.TL.disjoint_ps_rl_In with (p:=p0) in H8; auto.
  destroy H8.
  rewrite (bproj_reduce_Sel_r Defs C s C'0 s' p q l); auto.
  elim (H0 r); auto. intros. elim (H12 p0); auto.
  apply H0. apply Hnames. simpl. sup.
Qed.

Lemma strongly_projectable_reduces_Cond : forall Defs C s C' s' ps p r,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) ->
  In r ps ->
  CCC_To Defs C s (CCBase.TL.R_Cond p) C' s' ->
  strongly_projectable Defs C' r.
Proof.
intros.
rename H into H0, H1 into Hr, H0 into Hnames, H2 into H.
revert C H0 Hnames r Hr C' H.
induction C; intros; inversion H.
+ simpl; apply IHC; auto.
  intros. apply Hnames. simpl; sup.
+ rewrite <- H6; eapply strongly_projectable_inv_Then; eauto.
+ rewrite <- H6; eapply strongly_projectable_inv_Else; eauto.
+ rename p0 into q.
  elim (H0 r); auto; intros. inversion_clear H13.
  assert (strongly_projectable Defs C1' r).
    apply IHC1; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  assert (strongly_projectable Defs C2' r).
    apply IHC2; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  repeat split; auto.
  destroy H9.
  simpl. case_eq (Pid_dec q r); intro Hqr.
  2: elim (P.eq_dec p r); intro Hpr.
  - apply strongly_projectable_C in H13.
    apply strongly_projectable_C in H16.
    simpl. repeat rewrite Xmatch_elim; auto. discriminate.
  - rewrite Hpr in H10, H11.
    elim (bproj_reduce_Cond_p _ _ _ _ _ _ H12 H10); intros.
    destroy H17. rename x into b1, x0 into B1t, x1 into B1e.
    elim (bproj_reduce_Cond_p _ _ _ _ _ _ H14 H11); intros.
    destroy H20. rename x into b2, x0 into B2t, x1 into B2e.
    revert H15; simpl.
    rewrite Hqr, H18, H21.
    elim (B.eq_dec b1 b2); intro Hb.
    2: {
      simpl.
      unfold BExpr_dec; rewrite <- Bdec.eqb_neq in Hb; rewrite Hb.
      simpl; auto.
    }
    rewrite <- Hb. rewrite <- Hb in H20, H22. intro.
    assert (Xmerge B1t B2t <> XUndefined).
    1: { intro. revert H15. simpl; rewrite H23. Beq. auto. }
    assert (Xmerge B1e B2e <> XUndefined).
    1: { intro. revert H15. simpl; rewrite H24, Xmatch_elim; auto. Beq. auto. }
    rewrite Xmerge_Cond_inv in H15; auto.
    case_eq (CCBase.beval_on_state b1 s r); intro Hb'.
    rewrite H19, H22; auto. intro.
    simpl in H15. rewrite H25 in H15. auto.
    rewrite H20, H17; auto. intro.
    revert H15. simpl. rewrite H25. case (collapse (Xmerge B1t B2t)); auto.
  - generalize (bproj_reduce_Cond_r _ _ _ _ _ _ _ H12 H10 Hpr); intro.
    generalize (bproj_reduce_Cond_r _ _ _ _ _ _ _ H14 H11 Hpr); intro.
    simpl in H15. rewrite Hqr in H15.
    apply collapse_exists in H15. destroy H15.
    generalize (Xmore_branches_merge_extend _ _ _ _ _ H17 H18 H15); intro.
    destroy H19. rewrite H21, collapse_inject; apply inject_not_undefined.
+ destroy H0.
  rewrite <- H1 in H0, Hnames, H, H6. rewrite <- H1.
  clear r H1. rename r0 into r.
  repeat split; auto.
  apply IHC; auto. apply H0.
  intros; apply Hnames. simpl. sup.
  elim (H0 r); auto. intros. elim (H11 p0); auto.
  apply CCBase.TL.disjoint_ps_rl_In with (p:=p0) in H8; auto.
  destroy H8.
  apply Xmore_branches_trans with (bproj Defs C p0).
  elim (H0 r); auto. intros. elim (H11 p0); auto.
  apply (bproj_reduce_Cond_r Defs C s C'0 s' p); auto.
  apply H0. apply Hnames. simpl. sup.
Qed.

Lemma strongly_projectable_reduces_Call : forall Defs C s C' s' ps p X r Xs,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  (forall p Y, In p ps -> In Y Xs -> strongly_projectable Defs (snd (Defs Y)) p) ->
  (forall Y, set_incl_pid (CCC_pn (snd (Defs Y)) (fun Z => fst (Defs Z))) (fst (Defs Y))) ->
  (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) ->
  In r ps -> In X Xs -> 
  CCC_To Defs C s (CCBase.TL.R_Call X p) C' s' ->
  strongly_projectable Defs C' r.
Proof.
intros.
rename H into H0, H3 into Hr, H2 into Hnames, H1 into HDefs, H4 into HX, H5 into H, H0 into Hsp.
revert C H0 Hnames r Hr C' H.
induction C; intros; inversion H.
+ simpl; apply IHC; auto.
  intros. apply Hnames. simpl; sup.
+ rename p0 into q.
  elim (H0 r); auto; intros. inversion_clear H13.
  assert (strongly_projectable Defs C1' r).
    apply IHC1; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  assert (strongly_projectable Defs C2' r).
    apply IHC2; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  repeat split; auto.
  simpl in H9.
  simpl. case_eq (Pid_dec q r); intro.
  2: elim (P.eq_dec p r); intro Hpr.
  - apply strongly_projectable_C in H13.
    apply strongly_projectable_C in H16.
    simpl. repeat rewrite Xmatch_elim; auto. discriminate.
  - rewrite Hpr in H10, H11.
    elim (bproj_reduce_Call_p _ _ _ _ _ _ _ _ H12 (fun Y => Hsp r Y Hr) HDefs HX H10); intros.
    elim (bproj_reduce_Call_p _ _ _ _ _ _ _ _ H14 (fun Y => Hsp r Y Hr) HDefs HX H11); intros.
    elim (Xmore_branches_merge _ _ _ H19 H21); intros.
    destroy H22. rewrite H24, collapse_inject.
    apply inject_not_undefined.
  - rewrite (bproj_reduce_Call_r _ _ _ _ _ _ _ _ HDefs H10); auto.
    rewrite (bproj_reduce_Call_r _ _ _ _ _ _ _ _ HDefs H11); auto.
    intro; apply H15.
    simpl. rewrite H17; auto.
+ auto.
+ repeat split; auto.
  eapply set_remove'_1; eauto.
  generalize (Hsp p1 X); intros.
  apply strongly_projectable_C, collapse_exists in H11; auto.
  destroy H11. apply Xmore_branches_refl with x; auto.
  apply Hnames; simpl. rewrite H2. eapply set_remove'_1; eauto.
+ repeat split.
  eapply IHC; eauto. apply H0.
  intros; apply Hnames. simpl; sup.
  elim (H0 r0); auto. intros. elim (H12 p0); auto.
  elim (H0 r0); auto. intros. elim (H12 p0); auto. intros.
  apply CCBase.TL.disjoint_ps_rl_In with (p:=p0) in H8; auto.
  destroy H8.
  rewrite (bproj_reduce_Call_r Defs C s C'0 s' p X p0); auto.
+ rewrite H4 in H0, Hnames, H, H1; clear r H4.
  rename r0 into r.
  elim (H0 r); auto; intros.
  split; auto; intros.
  assert (In p1 l). eapply set_remove'_1; eauto.
  elim (H12 p1); auto.
+ rewrite <- H6. apply H0; auto.
Qed.

Lemma strongly_projectable_reduces : forall Defs ps C s C' s' t Xs,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) ->
  (forall p Y, In p ps -> In Y Xs -> strongly_projectable Defs (snd (Defs Y)) p) ->
  (forall Y, set_incl_pid (CCC_pn (snd (Defs Y)) (fun Z => fst (Defs Z))) (fst (Defs Y))) ->
  (forall p X, In X Xs -> In p (fst (Defs X)) -> In p ps) ->
  within_Xs Xs C -> CCC_To Defs C s t C' s' ->
  forall p, In p ps -> strongly_projectable Defs C' p.
Proof.
induction t; intros.
+ eapply strongly_projectable_reduces_Com; eauto.
+ eapply strongly_projectable_reduces_Sel; eauto.
+ eapply strongly_projectable_reduces_Cond; eauto.
+ eapply strongly_projectable_reduces_Call; eauto.
  eapply CCC_To_Xs; eauto.
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
destroy H1.
simpl. eapply strongly_projectable_reduces; eauto.
+ intros. red in H4; rewrite Forall_forall in H4.
  destroy H. elim (H Y); auto. clear H. simpl; intros; destroy H13.
  elim (In_dec P.eq_dec p (fst (Defs Y))); intro.
  apply initial_strongly_projectable with (fst (Defs Y)); auto.
  apply initial_strongly_projectable'; auto.
  intro. apply b, H0; auto.
+ apply Program_WF_Main_within_Xs; auto.
Qed.

(** The completeness part of the EPP theorem. *)
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
      elim (projectable_reduces (CCBase.Build_Program Defs C) Xs ps)
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
    1: elim (projectable_reduces (CCBase.Build_Program Defs C) Xs ps)
        with s (CCBase.TL.L_Sel p q left) (CCBase.Build_Program Defs C') s'; intros;
       eauto; rewrite epp_C_char with (HC:=H7), epp_C_out; auto.
    1: elim (projectable_reduces (CCBase.Build_Program Defs C) Xs ps)
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
    elim (projectable_reduces (CCBase.Build_Program Defs C) Xs ps)
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
    elim (projectable_reduces (CCBase.Build_Program Defs C) Xs ps)
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

(* Future wish: same with ToStar (requires: N1 >> N2 and N2 --> N2' implies
 exists N1' st N1 --> N1' >> N2'. *)

End Completeness.

Section Soundness.

(** ** Soundness of EPP
  Lemmas about reduction and projection. *)

Definition SP_eq (P P':Program) : Prop :=
  forall X, Procs P X = Procs P' X /\ Network_eq (Net P) (Net P').

Lemma bproj_Com_reduce : forall Defs Defs' ps C HC s N' s' p x q v,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) ->
  SP_To Defs' (epp_C Defs ps C HC) s (R_Com p v q x) N' s' ->
  exists C', CCC_To Defs C s (CCBase.TL.R_Com p v q x) C' s'
  /\ forall HC', Network_eq N' (epp_C Defs ps C' HC').
Proof.
intros.
rename H into Hsp, H0 into Hin, H1 into H.
revert v N' H.
induction C; intros. induction e.
+ inversion H. rewrite <- H1 in H. unfold v2; unfold v2 in H, H11.
  clear s'0 H8 N'0 H7 x0 H3 q0 H2 v v2 H1 p2 H0 s0 H5.
  rename p0 into p', p1 into q', v0 into v'.
  elim (P.eq_dec p p'); intro Hpp'.
  - clear IHC Hsp Hin.
    revert HC H H6 H9 H10 H4. rewrite <- Hpp'. clear p' Hpp'. intros.
    (* get the remaining equalities *)
    assert (In p ps /\ q = q' /\ e = e0).
    1: {
      revert H6.
      unfold epp_C. elim In_dec; simpl; intro.
      2: discriminate.
      elim (collapse_char'); simpl; intro.
      induction a0. revert p0. Peq.
      intros. induction x0; inversion p0.
      2: case o, o0; inversion p0.
      inversion H6. auto.
      (* absurd case *)
      exfalso. clear H H9 H10 H4.
      apply projectable_C_use' with (p:=p) in HC; auto.
    }
    destroy H0. rename H1 into Hpps.
    revert HC H4 H10 H9 H6 H H11. rewrite <- H2, <- H0.
    clear q' H2 e0 H0; intros.
    assert (p <> q) as Hpq.
    1: {
      pattern p at 2 in H6.
      intro H'; rewrite H', H9 in H6; inversion H6.
    }
    assert (In q ps /\ x = v').
    1: {
      revert H9.
      unfold epp_C. elim In_dec; simpl; intro.
      2: discriminate.
      elim (collapse_char'); simpl; intro.
      induction a0. revert p0. Peq. Pneq Hpq.
      intros. induction x0; inversion p0.
      2: case o, o0; inversion p0.
      inversion H9. auto.
      (* absurd case *)
      exfalso. clear H H6 H10 H4.
      apply projectable_C_use' with (p:=q) in HC; auto.
    }
    destroy H0.
    revert dependent HC. rewrite <- H0. clear v' H0; intros.
    rename H1 into Hqps.
    exists C; repeat split.
    1: constructor; auto.
    intros. rewrite H10.
    intro r.
    case (P.eq_dec p r); intro Hpr.
    2: case (P.eq_dec q r); intro Hqr.
    * rewrite <- Hpr, Network_rm_add_2_p; auto.
      rewrite epp_C_Com_p with (HC':=HC') in H6; auto.
      inversion H6; auto.
    * rewrite <- Hqr, Network_rm_add_2_q; auto.
      rewrite epp_C_Com_q with (HC':=HC') in H9; auto.
      inversion H9; auto.
    * rewrite Network_rm_add_2_out; auto.
      apply epp_C_Com_r; auto.
  - generalize (projectable_C_inv_Com Defs ps p' e q' v' C HC); intro HC'.
    (* get the remaining equalities *)
    assert (In p ps) as Hpps.
    1: { revert H6. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
    assert (In q ps) as Hqps.
    1: { revert H9. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
    assert (p' <> q) as Hp'q.
    1: intro. rewrite <- H0, epp_C_Com_p with (HC':=HC') in H9; auto.
      inversion H9. rewrite H0; auto.
    assert (q' <> p) as Hq'p.
    1: intro. rewrite <- H0, epp_C_Com_q with (HC':=HC') in H6.
      inversion H6. rewrite H0; auto. rewrite H0; auto.
    assert (q' <> q) as Hq'q.
    1: intro. rewrite <- H0, epp_C_Com_q with (HC':=HC') in H9.
      inversion H9. apply Hpp'; auto. 1,2: rewrite H0; auto.
    assert (p <> q) as Hpq.
    1: { intro H'; rewrite H', H9 in H6; inversion H6. }
    assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
    1: intros. apply Hin. simpl; sup.
    elim (IHC HC' Hsp Hin' (eval_on_state e0 s p) (Network_rm (Network_rm (epp_C Defs ps C HC') p) q | p[B] | q[B'])); intros.
    rename x0 into C'. destroy H0.
    exists (p' # e --> q' $ v';; C'); repeat split.
    * apply C_Delay_Eta; repeat split; auto.
    * intros. rewrite H10, <- H4.
      intro r. elim (P.eq_dec p r); intro Hpr.
      2: elim (P.eq_dec q r); intro Hqr.
      3: rewrite Network_rm_add_2_out, H4; auto.
      3: elim (In_dec P.eq_dec r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
      3: elim (P.eq_dec p' r); intro Hp'r.
      4: elim (P.eq_dec q' r); intro Hq'r.
      ++ rewrite <- Hpr, Network_rm_add_2_p; auto.
         rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC'0); auto.
         rewrite <- H0, Network_rm_add_2_p; auto.
      ++ rewrite <- Hqr, Network_rm_add_2_q; auto.
         rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC'0); auto.
         rewrite <- H0, Network_rm_add_2_q; auto.
      ++ rewrite <- Hp'r; intro.
         rewrite epp_C_Com_p with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC'0); auto.
         rewrite epp_C_Com_p with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
      ++ rewrite <- Hq'r; intro. rewrite <- Hq'r in Hp'r.
         rewrite epp_C_Com_q with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC'0); auto.
         rewrite epp_C_Com_q with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
      ++ rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC'0); auto.
         rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
    * apply S_Com with B B'; auto.
      rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC) in H6; inversion H6; auto.
      apply epp_C_wd.
      rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC) in H9; inversion H9; auto.
      apply epp_C_wd.
      reflexivity.
+ inversion H. rewrite <- H1 in H. unfold v1; unfold v1 in H, H11.
  clear s'0 H8 N'0 H7 x0 H3 q0 H2 v v1 H1 p2 H0 s0 H5.
  rename p0 into p', p1 into q'.
  generalize (projectable_C_inv_Sel _ _ _ _ _ _ HC); intro HC'.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H6. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (In q ps) as Hqps.
  1: { revert H9. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H0, epp_C_Sel_p with (HC':=HC') in H6; auto.
    inversion H6. rewrite H0; auto.
  assert (p' <> q) as Hp'q.
  1: intro. rewrite <- H0, epp_C_Sel_p with (HC':=HC') in H9; auto.
    inversion H9. rewrite H0; auto.
  assert (q' <> p) as Hq'p.
  1: intro. induction l.
    1: rewrite <- H0, epp_C_Sel_ql with (HC':=HC') in H6.
    4: rewrite <- H0, epp_C_Sel_qr with (HC':=HC') in H6.
    1,4: inversion H6. 1,2,3,4: rewrite H0; auto.
  assert (q' <> q) as Hq'q.
  1: intro. induction l.
    1: rewrite <- H0, epp_C_Sel_ql with (HC':=HC') in H9.
    4: rewrite <- H0, epp_C_Sel_qr with (HC':=HC') in H9.
    1,4: inversion H9. 1,2,3,4: rewrite H0; auto.
  assert (p <> q) as Hpq.
  1: { intro H'; rewrite H', H9 in H6; inversion H6. }
  assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (eval_on_state e s p) (Network_rm (Network_rm (epp_C Defs ps C HC') p) q | p[B] | q[B'])); intros.
  rename x0 into C'. destroy H0.
  exists (p' --> q'[l];; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros. rewrite H10, <- H4.
    intro r. elim (P.eq_dec p r); intro Hpr.
    2: elim (P.eq_dec q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec P.eq_dec r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
    3: elim (P.eq_dec p' r); intro Hp'r.
    4: elim (P.eq_dec q' r); intro Hq'r.
    - rewrite <- Hpr, Network_rm_add_2_p; auto.
      rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC'0); auto.
      rewrite <- H0, Network_rm_add_2_p; auto.
    - rewrite <- Hqr, Network_rm_add_2_q; auto.
      rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC'0); auto.
      rewrite <- H0, Network_rm_add_2_q; auto.
    - rewrite <- Hp'r; intro.
      rewrite epp_C_Sel_p with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC'0); auto.
      rewrite epp_C_Sel_p with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC); auto.
      rewrite <- H0; auto.
      rewrite Network_rm_add_2_out; auto.
      rewrite epp_C_wd with (H':=HC'); auto.
    - rewrite <- Hq'r; intro. rewrite <- Hq'r in Hp'r.
      induction l.
      1: rewrite epp_C_Sel_ql with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC'0); auto.
      1: rewrite epp_C_Sel_ql with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC); auto.
      2: rewrite epp_C_Sel_qr with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC'0); auto.
      2: rewrite epp_C_Sel_qr with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC); auto.
      all: rewrite <- H0, Network_rm_add_2_out; auto.
      all: rewrite epp_C_wd with (H':=HC'); auto.
    - rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC'0); auto.
      rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC); auto.
      rewrite <- H0; auto.
      rewrite Network_rm_add_2_out; auto.
      rewrite epp_C_wd with (H':=HC'); auto.
  * apply S_Com with B B'; auto.
    rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC) in H6; inversion H6; auto.
    apply epp_C_wd.
    rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC) in H9; inversion H9; auto.
    apply epp_C_wd.
    reflexivity.
+ inversion H. rewrite <- H1 in H. unfold v1; unfold v1 in H, H11.
  clear s'0 H8 N'0 H7 x0 H3 q0 H2 v v1 H1 p1 H0 s0 H5.
  rename p0 into p'.
  generalize (projectable_C_inv_Then _ _ _ _ _ _ HC); intro HC1.
  generalize (projectable_C_inv_Else _ _ _ _ _ _ HC); intro HC2.
  assert (forall p, In p ps -> strongly_projectable Defs C1 p) as Hsp1.
  1: apply Hsp.
  assert (forall p, In p ps -> strongly_projectable Defs C2 p) as Hsp2.
  1: apply Hsp.
  clear Hsp.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H6. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (In q ps) as Hqps.
  1: { revert H9. unfold epp_C. elim In_dec; simpl; auto.
    discriminate.
  }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H0, epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H6; auto.
    inversion H6. rewrite H0; auto.
  assert (p' <> q) as Hp'q.
  1: intro. rewrite <- H0, epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H9; auto.
    inversion H9. rewrite H0; auto.
  assert (p <> q) as Hpq.
  1: { intro H'; rewrite H', H9 in H6; inversion H6. }
  generalize (projectable_C_inv_Then _ _ _ _ _ _ HC) as HC1'; intro.
  generalize (projectable_C_inv_Else _ _ _ _ _ _ HC) as HC2'; intro.
  elim (epp_C_Cond_Send_inv _ _ _ _ _ _ HC HC1' HC2' _ _ _ _ H6).
  intros. destroy H0. rename x0 into Bp1, x1 into Bp2, H1 into Hp1, H2 into Hp2, H0 into Hp'.
  elim (epp_C_Cond_Recv_inv _ _ _ _ _ _ HC HC1' HC2' _ _ _ _ H9).
  intros. destroy H0. rename x0 into Bq1, x1 into Bq2, H1 into Hq1, H2 into Hq2, H0 into Hq'.
  assert (forall p, In p (CCC_pn C1 (fun X => fst (Defs X))) -> In p ps) as Hin1.
  1: intros. apply Hin. simpl; sup; sup.
  assert (forall p, In p (CCC_pn C2 (fun X => fst (Defs X))) -> In p ps) as Hin2.
  1: intros. apply Hin. simpl; sup; sup.
  elim (IHC1 HC1 Hsp1 Hin1 (eval_on_state e s p) (Network_rm (Network_rm (epp_C Defs ps C1 HC1) p) q | p[Bp1] | q[Bq1])); intros.
  rename x0 into C1'. destroy H0.
  elim (IHC2 HC2 Hsp2 Hin2 (eval_on_state e s p) (Network_rm (Network_rm (epp_C Defs ps C2 HC2) p) q | p[Bp2] | q[Bq2])); intros.
  rename x0 into C2'. destroy H2. clear IHC1 IHC2.
  exists (If p' ?? b Then C1' Else C2'); repeat split.
  * apply C_Delay_Cond; repeat split; auto.
  * intros. rewrite H10, <- H4.
    intro r. elim (P.eq_dec p r); intro Hpr.
    2: elim (P.eq_dec q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec P.eq_dec r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
    3: elim (P.eq_dec p' r); intro Hp'r.
    - rewrite <- Hpr, Network_rm_add_2_p; auto.
      apply inject_inj.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H2, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    - rewrite <- Hqr, Network_rm_add_2_q; auto.
      apply inject_inj.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H2, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    - rewrite <- Hp'r; intro.
      apply inject_inj.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H2; auto.
      rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC)
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC); auto.
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2); auto.
    - intro. apply inject_inj.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC)
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC); auto.
      rewrite <- H0, <- H2; auto.
      rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2); auto.
  * apply S_Com with Bp2 Bq2; auto.
    rewrite <- Hp2; apply epp_C_wd.
    rewrite <- Hq2; apply epp_C_wd.
    reflexivity.
  * apply S_Com with Bp1 Bq1; auto.
    rewrite <- Hp1; apply epp_C_wd.
    rewrite <- Hq1; apply epp_C_wd.
    reflexivity.
+ exfalso.
  inversion H.
  elim (In_dec P.eq_dec p ps); intros.
  elim (In_dec P.eq_dec p (fst (Defs r))); intros.
  rewrite epp_C_Call in H6; auto. inversion H6.
  rewrite epp_C_Call_out in H6; auto. inversion H6.
  rewrite epp_C_out in H6; auto. inversion H6.
+ inversion H. rewrite <- H1 in H. unfold v1; unfold v1 in H, H11.
  clear s'0 H8 N'0 H7 x0 H3 q0 H2 v v1 H1 p0 H0 s0 H5.
  rename l into ps', r into X.
  assert (projectable_C Defs ps C) as HC'.
  1: { red. rewrite Forall_forall. intro.
    induction x0 as (r,Br). unfold epp_list; rewrite in_map_iff.
    intro. destroy H0. inversion H1. simpl.
    elim (Hsp r); auto; intros.
    apply strongly_projectable_C; auto.
    rewrite <- H3; auto.
  }
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H6. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (In q ps) as Hqps.
  1: { revert H9. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (~In p ps') as Hp.
  1: intro. rewrite epp_C_RT_Call in H6; auto. inversion H6.
  assert (~In q ps') as Hq.
  1: intro. rewrite epp_C_RT_Call in H9; auto. inversion H9.
  assert (p <> q) as Hpq.
  1: { intro H'; rewrite H', H9 in H6; inversion H6. }
  assert (forall p, In p ps -> strongly_projectable Defs C p) as Hsp'.
  1: apply Hsp.
  assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp' Hin' (eval_on_state e s p) (Network_rm (Network_rm (epp_C Defs ps C HC') p) q | p[B] | q[B'])); intros.
  rename x0 into C'. destroy H0.
  exists (RT_Call X ps' C'); repeat split.
  * apply C_Delay_Call; repeat split; auto.
    apply CCBase.TL.disjoint_ps_char. simpl.
    intros r Hr. split; intro H'; rewrite H' in Hr; auto.
  * intros. rewrite H10, <- H4.
    assert (projectable_C Defs ps C').
    1: apply strongly_projectable_C'; intros. eapply strongly_projectable_reduces_Com; eauto.
    intro r. elim (P.eq_dec p r); intro Hpr.
    2: elim (P.eq_dec q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec P.eq_dec r ps); intro Hr1.
    3: elim (In_dec P.eq_dec r ps'); intro Hr2.
    - rewrite <- Hpr, Network_rm_add_2_p; auto.
      rewrite epp_C_RT_Call_out with (HC':=H2); auto.
      rewrite <- H0, Network_rm_add_2_p; auto.
    - rewrite <- Hqr, Network_rm_add_2_q; auto.
      rewrite epp_C_RT_Call_out with (HC':=H2); auto.
      rewrite <- H0, Network_rm_add_2_q; auto.
    - repeat rewrite epp_C_RT_Call; auto.
    - rewrite epp_C_RT_Call_out with (HC':=H2); auto.
      rewrite epp_C_RT_Call_out with (HC':=HC'); auto.
      rewrite <- H0; auto.
      rewrite Network_rm_add_2_out; auto.
    - repeat rewrite epp_C_out; auto.
  * apply S_Com with B B'; auto.
    rewrite epp_C_RT_Call_out with (HC':=HC') in H6; inversion H6; auto.
    rewrite epp_C_RT_Call_out with (HC':=HC') in H9; inversion H9; auto.
    reflexivity.
+ exfalso.
  inversion H.
  rewrite epp_C_End in H6. inversion H6.
Qed.

Lemma bproj_Sel_reduce_l : forall Defs Defs' ps C HC s N' s' p q,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) ->
  SP_To Defs' (epp_C Defs ps C HC) s (R_Sel p q left) N' s' ->
  exists C', CCC_To Defs C s (CCBase.TL.R_Sel p q left) C' s'
  /\ forall HC', Network_eq N' (epp_C Defs ps C' HC').
Proof.
intros.
rename H into Hsp, H0 into Hin, H1 into H.
revert N' H.
induction C; intros. induction e.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p2 H0 s0 H5.
  rename p0 into p', p1 into q', v into v'.
  generalize (projectable_C_inv_Com Defs ps p' e q' v' C HC); intro HC'.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H2. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (In q ps) as Hqps.
  1: { revert H3. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H0, epp_C_Com_p with (HC':=HC') in H2; auto.
    inversion H2. rewrite H0; auto.
  assert (p' <> q) as Hp'q.
  1: intro. rewrite <- H0, epp_C_Com_p with (HC':=HC') in H3; auto.
    inversion H3. rewrite H0; auto.
  assert (q' <> q) as Hq'q.
  1: intro. rewrite <- H0, epp_C_Com_q with (HC':=HC') in H3.
    inversion H3. 1,2: rewrite H0; auto.
  assert (q' <> p) as Hq'p.
  1: intro. rewrite <- H0, epp_C_Com_q with (HC':=HC') in H2.
    inversion H2. 1,2: rewrite H0; auto.
  assert (p <> q) as Hpq.
  1: { intro H'; rewrite H', H3 in H2; inversion H2. }
  assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (Network_rm (Network_rm (epp_C Defs ps C HC') p) q | p[B] | q[Bl])); intros.
  rename x into C'. destroy H0.
  exists (p' # e --> q' $ v';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros. rewrite H6, <- H4.
    intro r. elim (P.eq_dec p r); intro Hpr.
    2: elim (P.eq_dec q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec P.eq_dec r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
    3: elim (P.eq_dec p' r); intro Hp'r.
    4: elim (P.eq_dec q' r); intro Hq'r.
    ++ rewrite <- Hpr, Network_rm_add_2_p; auto.
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC'0); auto.
       rewrite <- H0, Network_rm_add_2_p; auto.
    ++ rewrite <- Hqr, Network_rm_add_2_q; auto.
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC'0); auto.
       rewrite <- H0, Network_rm_add_2_q; auto.
    ++ rewrite <- Hp'r; intro.
       rewrite epp_C_Com_p with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_p with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
    ++ rewrite <- Hq'r; intro. rewrite <- Hq'r in Hp'r.
       rewrite epp_C_Com_q with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_q with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
    ++ rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
  * apply S_LSel with B Bl Br; auto.
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC) in H2; inversion H2; auto.
    apply epp_C_wd.
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC) in H3; inversion H3; auto.
    apply epp_C_wd.
    reflexivity.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p2 H0 s0 H5.
  rename p0 into p', p1 into q'.
  elim (P.eq_dec p p'); intro Hpp'.
  - clear IHC Hsp Hin.
    revert HC H H2 H3 H6 H4. rewrite <- Hpp'. clear p' Hpp'. intros.
    (* get the remaining equalities *)
    assert (In p ps /\ q = q' /\ l = left).
    1: {
      revert H2.
      unfold epp_C. elim In_dec; simpl; intro.
      2: discriminate.
      elim (collapse_char'); simpl; intro.
      induction a0. revert p0. Peq.
      intros. induction x, l; inversion p0.
      1,2: inversion H2. auto. rewrite H10 in H5; inversion H5.
      1,2: case o, o0; inversion H1.
      (* absurd case *)
      exfalso. clear H H3 H6 H4.
      apply projectable_C_use' with (p:=p) in HC; auto.
    }
    destroy H0. rename H1 into Hpps.
    revert HC H4 H6 H2 H3 H. rewrite H0, <- H5.
    clear q' H0 l H5; intros.
    assert (p <> q) as Hpq.
    1: {
      pattern p at 2 in H2.
      intro H'; rewrite H', H3 in H2; inversion H2.
    }
    assert (In q ps) as Hqps.
    1: { revert H3. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
    exists C; repeat split.
    1: constructor; auto.
    intros. rewrite H6.
    intro r.
    case (P.eq_dec p r); intro Hpr.
    2: case (P.eq_dec q r); intro Hqr.
    * rewrite <- Hpr, Network_rm_add_2_p; auto.
      rewrite epp_C_Sel_p with (HC':=HC') in H2; auto.
      inversion H2; auto.
    * rewrite <- Hqr, Network_rm_add_2_q; auto.
      rewrite epp_C_Sel_ql with (HC':=HC') in H3; auto.
      inversion H3; auto.
    * rewrite Network_rm_add_2_out; auto.
      apply epp_C_Sel_r; auto.
  - generalize (projectable_C_inv_Sel _ _ _ _ _ _ HC); intro HC'.
    (* get the remaining equalities *)
    assert (In p ps) as Hpps.
    1: { revert H2. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
    assert (In q ps) as Hqps.
    1: { revert H3. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
    assert (p' <> p) as Hp'p.
    1: intro. rewrite <- H0, epp_C_Sel_p with (HC':=HC') in H2; auto.
      inversion H2. rewrite H0; auto.
    assert (p' <> q) as Hp'q.
    1: intro. rewrite <- H0, epp_C_Sel_p with (HC':=HC') in H3; auto.
      inversion H3. rewrite H0; auto.
    assert (q' <> p) as Hq'p.
    1: intro. induction l.
      1: rewrite <- H0, epp_C_Sel_ql with (HC':=HC') in H2.
      4: rewrite <- H0, epp_C_Sel_qr with (HC':=HC') in H2.
      1,4: inversion H2. 1,2,3,4: rewrite H0; auto.
    assert (q' <> q) as Hq'q.
    1: intro. induction l.
      1: rewrite <- H0, epp_C_Sel_ql with (HC':=HC') in H3.
      4: rewrite <- H0, epp_C_Sel_qr with (HC':=HC') in H3.
      1,4: inversion H3; auto. 1,2,3,4: rewrite H0; auto.
    assert (p <> q) as Hpq.
    1: { intro H'; rewrite H', H3 in H2; inversion H2. }
    assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
    1: intros. apply Hin. simpl; sup.
    elim (IHC HC' Hsp Hin' (Network_rm (Network_rm (epp_C Defs ps C HC') p) q | p[B] | q[Bl])); intros.
    rename x into C'. destroy H0.
    exists (p' --> q'[l];; C'); repeat split.
    * apply C_Delay_Eta; repeat split; auto.
    * intros. rewrite H6, <- H4.
      intro r. elim (P.eq_dec p r); intro Hpr.
      2: elim (P.eq_dec q r); intro Hqr.
      3: rewrite Network_rm_add_2_out, H4; auto.
      3: elim (In_dec P.eq_dec r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
      3: elim (P.eq_dec p' r); intro Hp'r.
      4: elim (P.eq_dec q' r); intro Hq'r.
      ++ rewrite <- Hpr, Network_rm_add_2_p; auto.
         rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC'0); auto.
         rewrite <- H0, Network_rm_add_2_p; auto.
      ++ rewrite <- Hqr, Network_rm_add_2_q; auto.
        rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC'0); auto.
        rewrite <- H0, Network_rm_add_2_q; auto.
      ++ rewrite <- Hp'r; intro.
         rewrite epp_C_Sel_p with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC'0); auto.
         rewrite epp_C_Sel_p with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
      ++ rewrite <- Hq'r; intro. rewrite <- Hq'r in Hp'r.
          induction l.
         1: rewrite epp_C_Sel_ql with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC'0); auto.
         1: rewrite epp_C_Sel_ql with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC); auto.
         2: rewrite epp_C_Sel_qr with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC'0); auto.
         2: rewrite epp_C_Sel_qr with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC); auto.
         all: rewrite <- H0, Network_rm_add_2_out; auto.
         all: rewrite epp_C_wd with (H':=HC'); auto.
      ++ rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC'0); auto.
         rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
    * apply S_LSel with B Bl Br; auto.
      rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC) in H2; inversion H2; auto.
      apply epp_C_wd.
      rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC) in H3; inversion H3; auto.
      apply epp_C_wd.
      reflexivity.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p1 H0 s0 H5.
  elim (epp_C_Sel_Branching_l _ _ _ _ _ _ _ _ _ H2 H3); intros.
  rewrite H1 in H3; clear Br H1 H0.
  rename p0 into p'.
  generalize (projectable_C_inv_Then _ _ _ _ _ _ HC); intro HC1.
  generalize (projectable_C_inv_Else _ _ _ _ _ _ HC); intro HC2.
  assert (forall p, In p ps -> strongly_projectable Defs C1 p) as Hsp1.
  1: apply Hsp.
  assert (forall p, In p ps -> strongly_projectable Defs C2 p) as Hsp2.
  1: apply Hsp.
  clear Hsp.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H2. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (In q ps) as Hqps.
  1: { revert H3. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H0, epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H2; auto.
    inversion H2. rewrite H0; auto.
  assert (p' <> q) as Hp'q.
  1: intro. rewrite <- H0, epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H3; auto.
    inversion H3. rewrite H0; auto.
  assert (p <> q) as Hpq.
  1: { intro H'; rewrite H', H3 in H2; inversion H2. }
  generalize (projectable_C_inv_Then _ _ _ _ _ _ HC) as HC1'; intro.
  generalize (projectable_C_inv_Else _ _ _ _ _ _ HC) as HC2'; intro.
  elim (epp_C_Cond_Sel_inv _ _ _ _ _ _ HC HC1' HC2' _ _ _ _ H2).
  intros. destroy H0. rename x into Bp1, x0 into Bp2, H1 into Hp1, H5 into Hp2, H0 into Hp'.
  elim (epp_C_Cond_Branching_l_inv _ _ _ _ _ _ HC HC1' HC2' _ _ _ H3).
  intros. destroy H0. rename x into Bq1, x0 into Bq2, H1 into Hq1, H5 into Hq2, H0 into Hq'.
  assert (forall p, In p (CCC_pn C1 (fun X => fst (Defs X))) -> In p ps) as Hin1.
  1: intros. apply Hin. simpl; sup; sup.
  assert (forall p, In p (CCC_pn C2 (fun X => fst (Defs X))) -> In p ps) as Hin2.
  1: intros. apply Hin. simpl; sup; sup.
  elim (IHC1 HC1 Hsp1 Hin1 (Network_rm (Network_rm (epp_C Defs ps C1 HC1) p) q | p[Bp1] | q[Bq1])); intros.
  rename x into C1'. destroy H0.
  elim (IHC2 HC2 Hsp2 Hin2 (Network_rm (Network_rm (epp_C Defs ps C2 HC2) p) q | p[Bp2] | q[Bq2])); intros.
  rename x into C2'. destroy H5. clear IHC1 IHC2.
  exists (If p' ?? b Then C1' Else C2'); repeat split.
  * apply C_Delay_Cond; repeat split; auto.
  * intros. rewrite H6, <- H4.
    intro r. elim (P.eq_dec p r); intro Hpr.
    2: elim (P.eq_dec q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec P.eq_dec r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
    3: elim (P.eq_dec p' r); intro Hp'r.
    - rewrite <- Hpr, Network_rm_add_2_p; auto.
      apply inject_inj.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H5, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    - rewrite <- Hqr, Network_rm_add_2_q; auto.
      apply inject_inj.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H5, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    - rewrite <- Hp'r; intro.
      apply inject_inj.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H5; auto.
      rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC)
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC); auto.
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2); auto.
    - intro. apply inject_inj.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC)
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC); auto.
      rewrite <- H0, <- H5; auto.
      rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2); auto.
  * apply S_LSel with Bp2 Bq2 None; auto.
    rewrite <- Hp2; apply epp_C_wd.
    rewrite <- Hq2; apply epp_C_wd.
    reflexivity.
  * apply S_LSel with Bp1 Bq1 None; auto.
    rewrite <- Hp1; apply epp_C_wd.
    rewrite <- Hq1; apply epp_C_wd.
    reflexivity.
+ exfalso.
  inversion H.
  elim (In_dec P.eq_dec p ps); intros.
  elim (In_dec P.eq_dec p (fst (Defs r))); intros.
  rewrite epp_C_Call in H2; auto. inversion H2.
  rewrite epp_C_Call_out in H2; auto. inversion H2.
  rewrite epp_C_out in H2; auto. inversion H2.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  rename l into ps', r into X.
  assert (projectable_C Defs ps C) as HC'.
  1: { red. rewrite Forall_forall. intro.
    induction x as (r,B'). unfold epp_list; rewrite in_map_iff.
    intro. destroy H0. inversion H1. simpl.
    elim (Hsp r); auto; intros.
    apply strongly_projectable_C; auto.
    rewrite <- H7; auto.
  }
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H2. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (In q ps) as Hqps.
  1: { revert H3. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (~In p ps') as Hp.
  1: intro. rewrite epp_C_RT_Call in H2; auto. inversion H2.
  assert (~In q ps') as Hq.
  1: intro. rewrite epp_C_RT_Call in H3; auto. inversion H3.
  assert (p <> q) as Hpq.
  1: { intro H'; rewrite H', H3 in H2; inversion H2. }
  assert (forall p, In p ps -> strongly_projectable Defs C p) as Hsp'.
  1: apply Hsp.
  assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp' Hin' (Network_rm (Network_rm (epp_C Defs ps C HC') p) q | p[B] | q[Bl])); intros.
  rename x into C'. destroy H0.
  exists (RT_Call X ps' C'); repeat split.
  * apply C_Delay_Call; repeat split; auto.
    apply CCBase.TL.disjoint_ps_char. simpl.
    intros r Hr. split; intro H'; rewrite H' in Hr; auto.
  * intros. rewrite H6, <- H4.
    assert (projectable_C Defs ps C').
    1: apply strongly_projectable_C'; intros. eapply strongly_projectable_reduces_Sel; eauto.
    intro r. elim (P.eq_dec p r); intro Hpr.
    2: elim (P.eq_dec q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec P.eq_dec r ps); intro Hr1.
    3: elim (In_dec P.eq_dec r ps'); intro Hr2.
    - rewrite <- Hpr, Network_rm_add_2_p; auto.
      rewrite epp_C_RT_Call_out with (HC':=H5); auto.
      rewrite <- H0, Network_rm_add_2_p; auto.
    - rewrite <- Hqr, Network_rm_add_2_q; auto.
      rewrite epp_C_RT_Call_out with (HC':=H5); auto.
      rewrite <- H0, Network_rm_add_2_q; auto.
    - repeat rewrite epp_C_RT_Call; auto.
    - rewrite epp_C_RT_Call_out with (HC':=H5); auto.
      rewrite epp_C_RT_Call_out with (HC':=HC'); auto.
      rewrite <- H0; auto.
      rewrite Network_rm_add_2_out; auto.
    - repeat rewrite epp_C_out; auto.
  * apply S_LSel with B Bl Br; auto.
    rewrite epp_C_RT_Call_out with (HC':=HC') in H2; inversion H2; auto.
    rewrite epp_C_RT_Call_out with (HC':=HC') in H3; inversion H3; auto.
    reflexivity.
+ exfalso.
  inversion H.
  rewrite epp_C_End in H2. inversion H2.
Qed.

Lemma bproj_Sel_reduce_r : forall Defs Defs' ps C HC s N' s' p q,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) ->
  SP_To Defs' (epp_C Defs ps C HC) s (R_Sel p q right) N' s' ->
  exists C', CCC_To Defs C s (CCBase.TL.R_Sel p q right) C' s'
  /\ forall HC', Network_eq N' (epp_C Defs ps C' HC').
Proof.
intros.
rename H into Hsp, H0 into Hin, H1 into H.
revert N' H.
induction C; intros. induction e.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p2 H0 s0 H5.
  rename p0 into p', p1 into q', v into v'.
  generalize (projectable_C_inv_Com Defs ps p' e q' v' C HC); intro HC'.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H2. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (In q ps) as Hqps.
  1: { revert H3. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H0, epp_C_Com_p with (HC':=HC') in H2; auto.
    inversion H2. rewrite H0; auto.
  assert (p' <> q) as Hp'q.
  1: intro. rewrite <- H0, epp_C_Com_p with (HC':=HC') in H3; auto.
    inversion H3. rewrite H0; auto.
  assert (q' <> q) as Hq'q.
  1: intro. rewrite <- H0, epp_C_Com_q with (HC':=HC') in H3.
    inversion H3. 1,2: rewrite H0; auto.
  assert (q' <> p) as Hq'p.
  1: intro. rewrite <- H0, epp_C_Com_q with (HC':=HC') in H2.
    inversion H2. 1,2: rewrite H0; auto.
  assert (p <> q) as Hpq.
  1: { intro H'; rewrite H', H3 in H2; inversion H2. }
  assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (Network_rm (Network_rm (epp_C Defs ps C HC') p) q | p[B] | q[Br])); intros.
  rename x into C'. destroy H0.
  exists (p' # e --> q' $ v';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros. rewrite H6, <- H4.
    intro r. elim (P.eq_dec p r); intro Hpr.
    2: elim (P.eq_dec q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec P.eq_dec r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
    3: elim (P.eq_dec p' r); intro Hp'r.
    4: elim (P.eq_dec q' r); intro Hq'r.
    ++ rewrite <- Hpr, Network_rm_add_2_p; auto.
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC'0); auto.
       rewrite <- H0, Network_rm_add_2_p; auto.
    ++ rewrite <- Hqr, Network_rm_add_2_q; auto.
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC'0); auto.
       rewrite <- H0, Network_rm_add_2_q; auto.
    ++ rewrite <- Hp'r; intro.
       rewrite epp_C_Com_p with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_p with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
    ++ rewrite <- Hq'r; intro. rewrite <- Hq'r in Hp'r.
       rewrite epp_C_Com_q with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_q with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
    ++ rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
  * apply S_RSel with B Bl Br; auto.
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC) in H2; inversion H2; auto.
    apply epp_C_wd.
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ HC) in H3; inversion H3; auto.
    apply epp_C_wd.
    reflexivity.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p2 H0 s0 H5.
  rename p0 into p', p1 into q'.
  elim (P.eq_dec p p'); intro Hpp'.
  - clear IHC Hsp Hin.
    revert HC H H2 H3 H6 H4. rewrite <- Hpp'. clear p' Hpp'. intros.
    (* get the remaining equalities *)
    assert (In p ps /\ q = q' /\ l = right).
    1: {
      revert H2.
      unfold epp_C. elim In_dec; simpl; intro.
      2: discriminate.
      elim (collapse_char'); simpl; intro.
      induction a0. revert p0. Peq.
      intros. induction x, l; inversion p0.
      1,2: inversion H2. rewrite H10 in H5; inversion H5. auto.
      1,2: case o, o0; inversion H1.
      (* absurd case *)
      exfalso. clear H H3 H6 H4.
      apply projectable_C_use' with (p:=p) in HC; auto.
    }
    destroy H0. rename H1 into Hpps.
    revert HC H4 H6 H2 H3 H. rewrite H0, <- H5.
    clear q' H0 l H5; intros.
    assert (p <> q) as Hpq.
    1: {
      pattern p at 2 in H2.
      intro H'; rewrite H', H3 in H2; inversion H2.
    }
    assert (In q ps) as Hqps.
    1: { revert H3. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
    exists C; repeat split.
    1: constructor; auto.
    intros. rewrite H6.
    intro r.
    case (P.eq_dec p r); intro Hpr.
    2: case (P.eq_dec q r); intro Hqr.
    * rewrite <- Hpr, Network_rm_add_2_p; auto.
      rewrite epp_C_Sel_p with (HC':=HC') in H2; auto.
      inversion H2; auto.
    * rewrite <- Hqr, Network_rm_add_2_q; auto.
      rewrite epp_C_Sel_qr with (HC':=HC') in H3; auto.
      inversion H3; auto.
    * rewrite Network_rm_add_2_out; auto.
      apply epp_C_Sel_r; auto.
  - generalize (projectable_C_inv_Sel _ _ _ _ _ _ HC); intro HC'.
    (* get the remaining equalities *)
    assert (In p ps) as Hpps.
    1: { revert H2. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
    assert (In q ps) as Hqps.
    1: { revert H3. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
    assert (p' <> p) as Hp'p.
    1: intro. rewrite <- H0, epp_C_Sel_p with (HC':=HC') in H2; auto.
      inversion H2. rewrite H0; auto.
    assert (p' <> q) as Hp'q.
    1: intro. rewrite <- H0, epp_C_Sel_p with (HC':=HC') in H3; auto.
      inversion H3. rewrite H0; auto.
    assert (q' <> p) as Hq'p.
    1: intro. induction l.
      1: rewrite <- H0, epp_C_Sel_ql with (HC':=HC') in H2.
      4: rewrite <- H0, epp_C_Sel_qr with (HC':=HC') in H2.
      1,4: inversion H2. 1,2,3,4: rewrite H0; auto.
    assert (q' <> q) as Hq'q.
    1: intro. induction l.
      1: rewrite <- H0, epp_C_Sel_ql with (HC':=HC') in H3.
      4: rewrite <- H0, epp_C_Sel_qr with (HC':=HC') in H3.
      1,4: inversion H3; auto. 1,2,3,4: rewrite H0; auto.
    assert (p <> q) as Hpq.
    1: { intro H'; rewrite H', H3 in H2; inversion H2. }
    assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
    1: intros. apply Hin. simpl; sup.
    elim (IHC HC' Hsp Hin' (Network_rm (Network_rm (epp_C Defs ps C HC') p) q | p[B] | q[Br])); intros.
    rename x into C'. destroy H0.
    exists (p' --> q'[l];; C'); repeat split.
    * apply C_Delay_Eta; repeat split; auto.
    * intros. rewrite H6, <- H4.
      intro r. elim (P.eq_dec p r); intro Hpr.
      2: elim (P.eq_dec q r); intro Hqr.
      3: rewrite Network_rm_add_2_out, H4; auto.
      3: elim (In_dec P.eq_dec r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
      3: elim (P.eq_dec p' r); intro Hp'r.
      4: elim (P.eq_dec q' r); intro Hq'r.
      ++ rewrite <- Hpr, Network_rm_add_2_p; auto.
         rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC'0); auto.
         rewrite <- H0, Network_rm_add_2_p; auto.
      ++ rewrite <- Hqr, Network_rm_add_2_q; auto.
        rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC'0); auto.
        rewrite <- H0, Network_rm_add_2_q; auto.
      ++ rewrite <- Hp'r; intro.
         rewrite epp_C_Sel_p with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC'0); auto.
         rewrite epp_C_Sel_p with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
      ++ rewrite <- Hq'r; intro. rewrite <- Hq'r in Hp'r.
          induction l.
         1: rewrite epp_C_Sel_ql with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC'0); auto.
         1: rewrite epp_C_Sel_ql with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC); auto.
         2: rewrite epp_C_Sel_qr with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC'0); auto.
         2: rewrite epp_C_Sel_qr with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC); auto.
         all: rewrite <- H0, Network_rm_add_2_out; auto.
         all: rewrite epp_C_wd with (H':=HC'); auto.
      ++ rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC'0); auto.
         rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
    * apply S_RSel with B Bl Br; auto.
      rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC) in H2; inversion H2; auto.
      apply epp_C_wd.
      rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ HC) in H3; inversion H3; auto.
      apply epp_C_wd.
      reflexivity.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p1 H0 s0 H5.
  elim (epp_C_Sel_Branching_r _ _ _ _ _ _ _ _ _ H2 H3); intros.
  rewrite H0 in H3; clear Bl H1 H0.
  rename p0 into p'.
  generalize (projectable_C_inv_Then _ _ _ _ _ _ HC); intro HC1.
  generalize (projectable_C_inv_Else _ _ _ _ _ _ HC); intro HC2.
  assert (forall p, In p ps -> strongly_projectable Defs C1 p) as Hsp1.
  1: apply Hsp.
  assert (forall p, In p ps -> strongly_projectable Defs C2 p) as Hsp2.
  1: apply Hsp.
  clear Hsp.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H2. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (In q ps) as Hqps.
  1: { revert H3. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H0, epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H2; auto.
    inversion H2. rewrite H0; auto.
  assert (p' <> q) as Hp'q.
  1: intro. rewrite <- H0, epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H3; auto.
    inversion H3. rewrite H0; auto.
  assert (p <> q) as Hpq.
  1: { intro H'; rewrite H', H3 in H2; inversion H2. }
  generalize (projectable_C_inv_Then _ _ _ _ _ _ HC) as HC1'; intro.
  generalize (projectable_C_inv_Else _ _ _ _ _ _ HC) as HC2'; intro.
  elim (epp_C_Cond_Sel_inv _ _ _ _ _ _ HC HC1' HC2' _ _ _ _ H2).
  intros. destroy H0. rename x into Bp1, x0 into Bp2, H1 into Hp1, H5 into Hp2, H0 into Hp'.
  elim (epp_C_Cond_Branching_r_inv _ _ _ _ _ _ HC HC1' HC2' _ _ _ H3).
  intros. destroy H0. rename x into Bq1, x0 into Bq2, H1 into Hq1, H5 into Hq2, H0 into Hq'.
  assert (forall p, In p (CCC_pn C1 (fun X => fst (Defs X))) -> In p ps) as Hin1.
  1: intros. apply Hin. simpl; sup; sup.
  assert (forall p, In p (CCC_pn C2 (fun X => fst (Defs X))) -> In p ps) as Hin2.
  1: intros. apply Hin. simpl; sup; sup.
  elim (IHC1 HC1 Hsp1 Hin1 (Network_rm (Network_rm (epp_C Defs ps C1 HC1) p) q | p[Bp1] | q[Bq1])); intros.
  rename x into C1'. destroy H0.
  elim (IHC2 HC2 Hsp2 Hin2 (Network_rm (Network_rm (epp_C Defs ps C2 HC2) p) q | p[Bp2] | q[Bq2])); intros.
  rename x into C2'. destroy H5. clear IHC1 IHC2.
  exists (If p' ?? b Then C1' Else C2'); repeat split.
  * apply C_Delay_Cond; repeat split; auto.
  * intros. rewrite H6, <- H4.
    intro r. elim (P.eq_dec p r); intro Hpr.
    2: elim (P.eq_dec q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec P.eq_dec r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
    3: elim (P.eq_dec p' r); intro Hp'r.
    - rewrite <- Hpr, Network_rm_add_2_p; auto.
      apply inject_inj.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H5, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    - rewrite <- Hqr, Network_rm_add_2_q; auto.
      apply inject_inj.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H5, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    - rewrite <- Hp'r; intro.
      apply inject_inj.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H5; auto.
      rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC)
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC); auto.
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2); auto.
    - intro. apply inject_inj.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC)
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC); auto.
      rewrite <- H0, <- H5; auto.
      rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2); auto.
  * apply S_RSel with Bp2 None Bq2; auto.
    rewrite <- Hp2; apply epp_C_wd.
    rewrite <- Hq2; apply epp_C_wd.
    reflexivity.
  * apply S_RSel with Bp1 None Bq1; auto.
    rewrite <- Hp1; apply epp_C_wd.
    rewrite <- Hq1; apply epp_C_wd.
    reflexivity.
+ exfalso.
  inversion H.
  elim (In_dec P.eq_dec p ps); intros.
  elim (In_dec P.eq_dec p (fst (Defs r))); intros.
  rewrite epp_C_Call in H2; auto. inversion H2.
  rewrite epp_C_Call_out in H2; auto. inversion H2.
  rewrite epp_C_out in H2; auto. inversion H2.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  rename l into ps', r into X.
  assert (projectable_C Defs ps C) as HC'.
  1: { red. rewrite Forall_forall. intro.
    induction x as (r,B'). unfold epp_list; rewrite in_map_iff.
    intro. destroy H0. inversion H1. simpl.
    elim (Hsp r); auto; intros.
    apply strongly_projectable_C; auto.
    rewrite <- H7; auto.
  }
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H2. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (In q ps) as Hqps.
  1: { revert H3. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (~In p ps') as Hp.
  1: intro. rewrite epp_C_RT_Call in H2; auto. inversion H2.
  assert (~In q ps') as Hq.
  1: intro. rewrite epp_C_RT_Call in H3; auto. inversion H3.
  assert (p <> q) as Hpq.
  1: { intro H'; rewrite H', H3 in H2; inversion H2. }
  assert (forall p, In p ps -> strongly_projectable Defs C p) as Hsp'.
  1: apply Hsp.
  assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp' Hin' (Network_rm (Network_rm (epp_C Defs ps C HC') p) q | p[B] | q[Br])); intros.
  rename x into C'. destroy H0.
  exists (RT_Call X ps' C'); repeat split.
  * apply C_Delay_Call; repeat split; auto.
    apply CCBase.TL.disjoint_ps_char. simpl.
    intros r Hr. split; intro H'; rewrite H' in Hr; auto.
  * intros. rewrite H6, <- H4.
    assert (projectable_C Defs ps C').
    1: apply strongly_projectable_C'; intros. eapply strongly_projectable_reduces_Sel; eauto.
    intro r. elim (P.eq_dec p r); intro Hpr.
    2: elim (P.eq_dec q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec P.eq_dec r ps); intro Hr1.
    3: elim (In_dec P.eq_dec r ps'); intro Hr2.
    - rewrite <- Hpr, Network_rm_add_2_p; auto.
      rewrite epp_C_RT_Call_out with (HC':=H5); auto.
      rewrite <- H0, Network_rm_add_2_p; auto.
    - rewrite <- Hqr, Network_rm_add_2_q; auto.
      rewrite epp_C_RT_Call_out with (HC':=H5); auto.
      rewrite <- H0, Network_rm_add_2_q; auto.
    - repeat rewrite epp_C_RT_Call; auto.
    - rewrite epp_C_RT_Call_out with (HC':=H5); auto.
      rewrite epp_C_RT_Call_out with (HC':=HC'); auto.
      rewrite <- H0; auto.
      rewrite Network_rm_add_2_out; auto.
    - repeat rewrite epp_C_out; auto.
  * apply S_RSel with B Bl Br; auto.
    rewrite epp_C_RT_Call_out with (HC':=HC') in H2; inversion H2; auto.
    rewrite epp_C_RT_Call_out with (HC':=HC') in H3; inversion H3; auto.
    reflexivity.
+ exfalso.
  inversion H.
  rewrite epp_C_End in H2. inversion H2.
Qed.




Lemma EPP_Com : forall P Xs ps,
  Program_WF Xs P -> well_ann P -> forall (HP:projectable Xs ps P),
  (forall p, In p ps -> strongly_projectable (Procedures P) (Main P) p) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In X Xs -> In p (Vars P X) -> In p ps) ->
  forall s p v q N' s', (epp Xs ps P HP,s) --[L_Com p v q]-->(N',s') ->
  exists P', ((P,s) --[CCBase.TL.L_Com p v q]--> (P',s'))%CC /\
    forall H, Net N' >> Net (epp Xs ps P' H).
Proof.
intros P Xs ps HWF Hann HP Hsp HMain HVars s p v q N' s' HTo.
induction P as (Defs,C).
inversion HTo. induction t; inversion H2.
rewrite H8, H7, H6 in H0.
clear q0 H8 v0 H7 p0 H6 s'0 H4 N' H3 H2 s0 H1 HTo.
rename N'0 into N', Defs0 into Defs', H into HN, H0 into HTo.
induction C.
2: {
  rename p0 into r. simpl in Hsp, HMain, HVars.
  elim IHC1 with (projectable_inv_Then _ _ _ _ _ _ _ HP); auto; intros.
  elim IHC2 with (projectable_inv_Else _ _ _ _ _ _ _ HP); auto; intros.
  clear IHC1 IHC2.
  induction x0 as (Defs1,C1'). simpl in H; destroy H.
  induction x1 as (Defs2,C2'). simpl in H0; destroy H0.
  rewrite <- (CCP_To_Defs_stable _ _ _ _ _ _ _ H1) in H, H1; clear Defs1.
  rewrite <- (CCP_To_Defs_stable _ _ _ _ _ _ _ H2) in H0, H2; clear Defs2.
  inversion H1. induction t; inversion H7.
  clear H1 s0 H6 C H5 Defs0 H3.
  rewrite H13, H12, H11 in H7, H4. clear q0 H13 v0 H12 p0 H11 s'0 H9 C' H8.
  inversion H2. induction t; inversion H8.
  clear H2 s0 H6 C H5 Defs0 H1.
  rewrite H14, H13, H12 in H8, H3. clear q0 H14 v0 H13 p0 H12 s'0 H10 C' H9.
  rename H4 into H1, H7 into H1', H3 into H2, H8 into H2', x0 into x', x1 into x''.
  inversion HTo. rewrite H4.
  clear s'0 H11 N'0 H10 x0 H6 q0 H5 v1 H4 p0 H3 s0 H8 N0 H7 H14 Hann HMain.
  rename H13 into HN'.
  assert (forall r, Net (Build_Program Defs' N) r = (Net (epp _ _ _ HP) r)). rewrite HN; auto.
  clear HN; simpl in H3.
  assert (In p ps) as Hp.
  1:{
    elim (In_dec P.eq_dec p ps); auto.
    intro. generalize (H3 p); clear H3; intro.
    rewrite epp_out in H3; auto. rewrite H9 in H3; inversion H3.
  }
  assert (In q ps) as Hq.
  1:{
    elim (In_dec P.eq_dec q ps); auto.
    intro. generalize (H3 q); clear H3; intro.
    rewrite epp_out in H3; auto. rewrite H12 in H3; inversion H3.
  }
  assert (p <> q) as Hpq.
  1: {
    eapply CCC_To_Com_neq; eauto.
    generalize (Program_WF_Else _ _ _ _ _ _ HWF); intro.
    apply Program_WF_Main in H4. auto.
  }
  exists (CCBase.Build_Program Defs (If r ?? b Then C1' Else C2')); repeat split.
  - assert (r <> p /\ r <> q).
    1: {
      inversion HP; simpl; intros. clear H5.
      generalize (H3 r); clear H3; intro.
      rewrite epp_C_char with (HC:=H4) in H3. simpl in H3.
      split; intro Hr; revert H4 H3; rewrite Hr; intro.
      ++ rewrite H9; unfold epp_C.
         elim in_dec; simpl; intro. 2: discriminate.
         elim collapse_char'; simpl; intro. induction a0.
         revert p0; Peq; intro.
         induction x0; inversion p0. case o, o0; inversion p0.
         discriminate.
         intro; clear H3. apply projectable_C_use with (p:=p) in H4; auto.
         destroy H4; simpl in H4; rewrite H4 in b0.
         apply (inject_not_undefined x0); auto.
      ++ rewrite H12; unfold epp_C.
         elim in_dec; simpl; intro. 2: discriminate.
         elim collapse_char'; simpl; intro. induction a0.
         revert p0; Peq; intro.
         induction x0; inversion p0. case o, o0; inversion p0.
         discriminate.
         intro; clear H3. apply projectable_C_use with (p:=q) in H4; auto.
         destroy H4; simpl in H4; rewrite H4 in b0.
         apply (inject_not_undefined x0); auto.
    }
    constructor; auto.
    replace x' with x''; auto.
    elim (bproj_reduce_Com_q Defs C1 s C1' s' p q v x'); auto.
    elim (bproj_reduce_Com_q Defs C2 s C2' s' p q v x''); auto.
    * generalize (H3 q); clear H3; intro.
      inversion HP; intros. clear H6. simpl in H5.
      rewrite epp_C_char with (HC:=H5) in H3.
      revert H3. rewrite H12; unfold epp_C.
      elim in_dec; simpl; intro. 2: discriminate.
      elim collapse_char'; simpl; intro. induction a0.
      destroy H4; destroy H7; destroy H8.
      revert p0; unfold Pid_dec; Pneq H4.
      rewrite H6, H10; simpl. Peq.
      case_eq (Var_dec x' x''); simpl.
      intros; symmetry; apply Xdec.eqb_eq; auto.
      intros; elim (inject_not_undefined x2); auto.
      exfalso. apply projectable_C_use with (p:=q) in H5; auto.
      destroy H5; simpl in H5; rewrite H5 in b0.
      apply (inject_not_undefined x2); auto.
    * elim (Hsp q); tauto.
    * elim (Hsp q); tauto.
  - intros; intro p'.
    inversion H4. clear H6; simpl in H5.
    rewrite epp_C_char with (HC:=H5).
    inversion HP. simpl in H6; clear H7.
    simpl. rewrite HN'.
    elim (In_dec P.eq_dec p' ps); intro Hp'.
    * elim (P.eq_dec p' p); intro.
      rewrite a, Network_rm_add_2_p; auto.
      



rewrite epp_C_char with (HC:=H5).

    * simpl. rewrite epp_C_out, HN', Network_rm_add_2_out; auto.
      2,3: intro Hp'; rewrite <- Hp' in b0; tauto.
      rewrite epp_C_out; auto. apply more_branches_refl.


Lemma EPP_Sound : forall P Xs ps,
  Program_WF Xs P -> well_ann P -> forall (HP:projectable Xs ps P),
  (forall p, In p ps -> strongly_projectable (Procedures P) (Main P) p) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In X Xs -> In p (Vars P X) -> In p ps) ->
  forall s tl N' s', (epp Xs ps P HP,s) --[tl]-->(N',s') ->
  exists P' tl', ((P,s) --[tl']--> (P',s'))%CC /\
    forall H, Net N' >> Net (epp Xs ps P' H).
Proof.
intros.
inversion H4.
clear tl H4 s'0 H10 H6 s0 H7 s'0 N' H9. rename N'0 into N'.
inversion H8.
+ clear s'0 H14 N'0 H13 s0 H11 N0 H10.
  


End Soundness.

End EPPBase.