Require Export CC.
Require Export Merge.

Local Open Scope nat_scope.

Arguments Names [Sig].

(** ** EndPoint projection *)

Section EndPointProjection.

Local Ltac sup := rewrite set_union_iff; auto.
Local Ltac eq_elim t t' H := case (eq_dec t t'); intro H;
  [ rewrite <- H in *; clear t' H | idtac].
Local Ltac fail_with H := right; intro H; induction H as [B HB];
    inversion HB; eauto.

Variable Sig : Signature.

Notation Pid := (pid Sig).
Notation Var := (var Sig).
Notation Value := (value Sig).
Notation Expr := (expr Sig).
Notation BExpr := (bexpr Sig).
Notation RecVar := (recvar Sig).
Notation Ann := (ann Sig).
Notation Ev := (ev Sig).
Notation BEv := (bev Sig).

(** The signature for the target calculus. *)

Notation PR := (DecProd RecVar Pid).

Definition Sig' := Build_Signature Pid Var Value Expr BExpr PR Ann Ev BEv.

Open Scope CC.

(** First step: local projection. *)

Inductive bproj : DefSet Sig -> Choreography Sig -> Pid -> Behaviour Sig' -> Prop :=
| bproj_End D p : bproj D CC.End p (End _)
| bproj_Send D p e q x a C B : bproj D C p B ->
                               bproj D (p#e --> q$x @ a ;; C) p
                                       (@Send Sig' q e a B)
| bproj_Recv D p e q x a C B : bproj D C q B -> p <> q ->
                               bproj D (p#e --> q$x @ a ;; C) q
                                       (@Recv Sig' p x a B)
| bproj_Com D p e q x a C r B : bproj D C r B -> p <> r -> q <> r ->
                                bproj D (p#e --> q$x @ a ;; C) r B
| bproj_Pick D p l q a C B : bproj D C p B ->
                             bproj D (p --> q[l] @ a ;; C) p
                                     (@Sel Sig' q l a B)
| bproj_Left D p q a C B : bproj D C q B -> p <> q ->
                           bproj D (p --> q[left] @ a ;; C) q
                                   (@Branching Sig' p (Some (a,B)) None)
| bproj_Right D p q a C B : bproj D C q B -> p <> q ->
                            bproj D (p --> q[right] @ a ;; C) q
                                    (@Branching Sig' p None (Some (a,B)))
| bproj_Sel D p l q a C r B : bproj D C r B -> p <> r -> q <> r ->
                              bproj D (p --> q[l] @ a ;; C) r B
| bproj_Cond D p b C1 C2 B1 B2 : bproj D C1 p B1 -> bproj D C2 p B2 ->
                                 bproj D (If p ?? b Then C1 Else C2) p
                                         (@Cond Sig' b B1 B2)
| bproj_Cond' D p b C1 C2 r B1 B2 B : bproj D C1 r B1 -> bproj D C2 r B2 ->
                                      p <> r -> B1 [V] B2 == B ->
                                      bproj D (If p ?? b Then C1 Else C2) r B
| bproj_Call_in D X p : In p (fst (D X)) -> bproj D (CC.Call X) p
                                                    (@Call Sig' (X,p))
| bproj_Call_out D X p : ~In p (fst (D X)) -> bproj D (CC.Call X) p (End _)
| bproj_RT_Call_in D X ps C p : In p ps -> bproj D (RT_Call X ps C) p
                                                   (@Call Sig' (X,p))
| bproj_RT_Call_out D X ps C p B : ~In p ps -> bproj D C p B ->
                                   bproj D (RT_Call X ps C) p B.

Notation "[[ D , C | p ]] == B" := (bproj D C p B) (at level 20).

(** Again, this relation is functional... *)

Lemma bproj_unique : forall D C p B B',
  [[D,C | p ]] == B -> [[D,C | p]] == B' -> B = B'.
Proof.
intros. revert dependent B'.
induction H; intros.
- inversion_clear H0; auto.
- inversion H0; auto. 2,3: tauto.
  rewrite IHbproj with B0; auto.
- inversion H1; auto. 1,3: tauto.
  rewrite IHbproj with B0; auto.
- inversion H2; auto. all: tauto.
- inversion H0; auto. 2,3,4: tauto.
  rewrite IHbproj with B0; auto.
- inversion H1; auto. 1,3: tauto.
  rewrite IHbproj with B0; auto.
- inversion H1; auto. 1,3: tauto.
  rewrite IHbproj with B0; auto.
- inversion H2; auto. all: tauto.
- inversion H1; auto. 2: tauto.
  rewrite IHbproj1 with B0, IHbproj2 with B3; auto.
- inversion H3. tauto.
  apply merge_unique with B0 B3; auto.
  rewrite <- IHbproj1 with B0, <- IHbproj2 with B3; auto.
- inversion H0; auto. tauto.
- inversion H0; auto. tauto.
- inversion H0; auto. tauto.
- inversion H1; auto. tauto.
Qed.

(** ...and computable. The decidability statement is a bit stronger than
  usual because we will use it in later definitions. *)

Definition projectable_B D C p := exists B, [[D,C | p]] == B.

Lemma bproj_dec : forall D C p,
  { B | [[D,C | p]] == B } + {~projectable_B D C p}.
Proof.
unfold projectable_B.
induction C. induction e. all: intros.
+ induction (IHC p) as [ [B HB] | HC]; clear IHC. 2: fail_with H.
  case (eq_dec p t0); intro Hp. rewrite <- Hp in *; clear t0 Hp.
  2: case (eq_dec p t2); intro Hq. 2: rewrite <- Hq in *; clear t2 Hq.
  all: left.
  - (* Send *) exists (@Send Sig' t2 t1 t B); constructor; auto.
  - (* Recv *) exists (@Recv Sig' t0 t3 t B); constructor; auto.
  - (* other *) exists B; constructor; auto.
+ induction (IHC p) as [ [B HB] | HC]; clear IHC. 2: fail_with H.
  case (eq_dec p t0); intro Hp. rewrite <- Hp in *; clear t0 Hp.
  2: case (eq_dec p t1); intro Hq. 2: rewrite <- Hq in *; clear t1 Hq.
  2: induction t2.
  1,2,3,4: left.
  - (* Sel *) exists (@Sel Sig' t1 t2 t B); constructor; auto.
  - (* Left *) exists (@Branching Sig' t0 (Some (t,B)) None); constructor; auto.
  - (* Right *) exists (@Branching Sig' t0 None (Some (t,B))); constructor; auto.
  - (* other *) exists B; constructor; auto.
+ induction (IHC1 p) as [ [BT HT] | HC]; clear IHC1. 2: fail_with H.
  induction (IHC2 p) as [ [BE HE] | HC]; clear IHC2. 2: fail_with H.
  case (eq_dec p t); intro Hp. rewrite <- Hp in *; clear t Hp.
  2: induction (merge_dec _ BT BE) as [ [B HB] | HB ].
  1,2: left.
  - (* Cond *) exists (@Cond Sig' t0 BT BE); constructor; auto.
  - (* other *) exists B. apply bproj_Cond' with BT BE; auto.
  - (* unmergeable *) right; intro.
    induction H as [B HB']. apply HB. inversion HB'.
    exfalso; auto.
    exists B.
    rewrite (bproj_unique _ _ _ _ _ HT H4).
    rewrite (bproj_unique _ _ _ _ _ HE H7). auto.
+ elim (In_dec (@eq_dec Pid) p (fst (D t))); left.
  - (* In *) exists (Call Sig' (t,p)); constructor; auto.
  - (* Out *) exists (End _); constructor; auto.
+ elim (In_dec (@eq_dec Pid) p l).
  2: induction (IHC p) as [ [B HB] | HC]; clear IHC; auto. 3: fail_with H'.
  all: left.
  - (* In *) exists (Call Sig' (t,p)); constructor; auto.
  - (* Out *) exists B; constructor; auto.
+ left. exists (End _ ); constructor.
Qed.

(** Projections are always well-formed. *)

Lemma bproj_WF : forall D C p B, no_self_comm _ C ->
  [[D,C | p]] == B -> Behaviour_WF Sig' p B.
Proof.
intros. induction H0; try inversion H; simpl; auto.
eapply merge_WF; eauto.
Qed.

Definition projectable_C D C ps :=
  Forall (fun p => projectable_B D C p) ps.

Definition projectable_D Xs D :=
  Forall (fun X => projectable_C D (snd (D X)) (fst (D X))) Xs.

Definition projectable Xs ps P :=
  projectable_C (Procedures Sig P) (Main P) ps /\
  projectable_D Xs (Procedures _ P) /\
  (forall p, In p (CCC_pn (Main P) (fun _ => nil)) -> In p ps) /\
  (forall p X, In X Xs -> In p (fst (Procedures _ P X)) -> In p ps) /\
  (forall p X, In X Xs ->
               In p (CCC_pn (snd (Procedures _ P X)) (fun _ => nil)) -> In p ps).

(** Not decidable, but in practice easy to compute. 
  Maybe we want to compute ps from Xs? *)

Definition Projectable P := exists Xs ps, projectable Xs ps P /\ Program_WF _ Xs P.

(** For tackling contradictions in the absurd cases of the definitions below. *)

Ltac contr_aux H := red in H; rewrite Forall_forall in H; auto.
Ltac contr H := intros; exfalso; contr_aux H.
Ltac contr2 H H' := contr H; specialize (H _ H'); contr_aux H.

(** Now we can define EPP, again in a layered manner.
  Definitions are interactive because of the absurd cases. *)

Definition epp_C D ps C : projectable_C D C ps -> Network Sig'.
Proof.
intros; intro p.
elim (In_dec (@eq_dec Pid) p ps); intro Hp.
2: apply End.
induction (bproj_dec D C p) as [ [B HB] | HC].
apply B.
contr H.
Defined.

Definition epp_D Xs D : projectable_D Xs D -> DefSetB Sig'.
Proof.
intros; intro.
case_eq X; intros R p HX.
elim (In_dec (@eq_dec RecVar) R Xs).
2: intros; apply End.
elim (In_dec (@eq_dec Pid) p (fst (D R))).
2: intros; apply End.
induction (bproj_dec D (snd (D R)) p) as [ [B HB] | HC]; intros.
apply B.
contr2 H a0.
Defined.

Definition epp Xs ps P : projectable Xs ps P -> Program Sig'.
Proof.
intro H; inversion_clear H. inversion_clear H1.
constructor.
apply (epp_D _ _ H).
apply (epp_C _ _ _ H0).
Defined.

(** Auxiliary results about behaviour projection. *)

Lemma bproj_not_In : forall D r C, ~In r (CCC_pn C (Names D)) ->
  [[D,C | r]] == End _.
Proof.
induction C; simpl; auto; intros. induction e.
+ simpl in H.
  apply set_union_not_In in H; inversion_clear H.
  constructor; auto.
  intro. rewrite H in *. simpl in H0. tauto.
  intro. rewrite H in *. simpl in H0. tauto.
+ simpl in H.
  apply set_union_not_In in H; inversion_clear H.
  constructor; auto.
  intro. rewrite H in *. simpl in H0. tauto.
  intro. rewrite H in *. simpl in H0. tauto.
+ simpl in H.
  apply set_union_not_In in H; inversion_clear H.
  apply set_union_not_In in H0; inversion_clear H0.
  apply bproj_Cond' with (End _) (End _); auto.
  simpl in H; tauto. constructor.
+ constructor; auto.
+ apply set_union_not_In in H; inversion_clear H.
  constructor; auto.
+ constructor.
Qed.

Lemma bproj_Call_In : forall D C p X, [[D,C | p]] == Call Sig' (X, p) ->
  consistent _ (Names D) C -> In p (fst (D X)).
Proof.
induction C; try induction e; simpl.
+ intros r X H. inversion_clear H. auto.
+ intros r X H. inversion_clear H. auto.
+ intros r X H H0. inversion_clear H. inversion_clear H0.
  inversion H4. rewrite <- H0, H8 in H1. auto.
+ intros r X H. inversion_clear H. auto.
+ intros r X H H0. inversion H; inversion_clear H0.
  rewrite H7 in *; auto.
  auto.
+ intros r X H. inversion H.
Qed.

Lemma bproj_disjoint : forall D e a C p, ~In p (eta_pn _ e) ->
  forall B, [[D,e @ a;; C | p]] == B -> [[D,C | p]] == B.
Proof.
induction e; intros.
all: simpl in H; inversion H0; tauto.
Qed.

Open Scope SP_scope.

(** Proof irrelevance for EPP. *)

Lemma epp_C_wd : forall D C ps H H', epp_C D ps C H (==) epp_C D ps C H'.
Proof.
intros; intro. unfold epp_C.
elim In_dec; auto.
elim bproj_dec; auto.
contr H.
Qed.

(** More about EPP. *)

Lemma epp_C_out : forall D C ps H p, ~In p ps -> epp_C D ps C H p = End _.
Proof. intros; unfold epp_C. elim In_dec; tauto. Qed.

Lemma epp_C_out' : forall D ps C HC p,
  ~In p (CCC_pn C (Names D)) -> epp_C D ps C HC p = End _.
Proof.
intros.
unfold epp_C; simpl.
elim In_dec; auto.
elim bproj_dec; simpl.
2: contr HC.
induction a. clear HC.
intro Hp. induction p0; auto.
all: try (elim H; simpl; repeat rewrite set_union_iff; simpl; auto; fail).
all: try (apply IHp0; auto;
          intro; elim H; simpl; rewrite set_union_iff; auto; fail).
+ rewrite IHp0_1, IHp0_2 in H1; auto. inversion H1; auto.
  all: intro; elim H; simpl; repeat rewrite set_union_iff; auto.
Qed.

Lemma epp_C_char : forall Xs ps D C HP HC,
  Net (epp Xs ps (D,C) HP) (==) (epp_C D ps C HC).
Proof.
intros.
unfold epp.
case HP; intros. case a; intros.
apply epp_C_wd.
Qed.

Lemma epp_C_char' : forall Xs ps D C HP p, In p ps ->
  [[D,C | p]] == Net (epp Xs ps (D, C) HP) p.
Proof.
intros; unfold epp.
case HP; intros. case a; intros.
simpl.
unfold epp_C. elim in_dec; simpl.
elim bproj_dec; simpl.
+ induction a1; auto.
+ contr p0.
+ tauto.
Qed.

Lemma epp_C_bproj : forall D ps C HC p, In p ps ->
  [[D,C | p]] == epp_C D ps C HC p.
Proof.
intros. unfold epp_C; simpl.
elim In_dec; simpl. 2: tauto.
elim bproj_dec. induction a; auto.
contr HC.
Qed.

Lemma epp_C_WF : forall D ps C HC, no_self_comm _ C ->
  Network_WF _ (epp_C D ps C HC).
Proof.
intros; intro.
elim (In_dec (@eq_dec Pid) p ps); intro Hp.
apply bproj_WF with D C, epp_C_bproj; auto.
rewrite epp_C_out; simpl; auto.
Qed.

Lemma epp_D_wd : forall Xs D H H' X, epp_D Xs D H X = epp_D Xs D H' X.
Proof.
intros; unfold epp_D.
induction X as (R,p).
elim In_dec; auto.
intros. elim In_dec; auto.
intros. elim bproj_dec; auto.
contr2 H a0.
Qed.

Lemma epp_D_char : forall Xs ps D C HP HD X p,
  Procs (epp Xs ps (D,C) HP) (X,p) = epp_D Xs D HD (X,p).
Proof.
intros.
unfold epp.
case HP; intros. case a; intros.
apply epp_D_wd.
Qed.

Lemma epp_D_char' : forall Xs ps D C HP X p,
  In X Xs -> (CCC_pn (snd (D X)) (Names D) [C] fst (D X)) ->
  [[D,snd (D X) | p]] == Procs (epp Xs ps (D,C) HP) (X,p).
Proof.
intros.
unfold epp.
case HP; intros.
case a; simpl; intro HD. clear a; intros.
elim In_dec; simpl; intro Hp; elim In_dec; simpl; intro HX.
elim bproj_dec; simpl; intro Hb.
elim Hb; simpl; intros; auto.
+ contr2 HD HX.
+ tauto.
+ apply bproj_not_In.
  intro; apply Hp, H0. auto.
+ tauto.
Qed.

Lemma epp_D_char'' : forall Xs ps D C HP X p HX, In X Xs ->
   Procs (epp Xs ps (D,C) HP) (X, p) = epp_C D (fst (D X)) (snd (D X)) HX p.
Proof.
intros Xs ps D C HP X p HX HX'.
inversion HP. clear H. destroy H0. clear H1 H2 H0.
rewrite epp_D_char with (HD:=H).
simpl. elim In_dec; intro.
2: simpl; rewrite epp_C_out; auto.
all: elim In_dec; simpl; auto. 2: intro H'; elim H'; auto.
elim bproj_dec. induction a0; simpl; intros.
eapply bproj_unique; eauto. apply epp_C_bproj; auto.
contr HX.
Qed.

Lemma epp_out : forall Xs ps D C HP p, ~In p ps ->
  Net (epp Xs ps (D,C) HP) p = End _.
Proof.
intros; unfold epp.
unfold epp.
case HP; intros.
case a; simpl; intro HD. clear a; intros.
apply epp_C_out; auto.
Qed.

(** Sanity checks: EPP works as defined informally in the paper. *)

Lemma epp_C_Com_p : forall D ps C p e q x a HC HC', In p ps ->
  epp_C D ps (p # e --> q $ x @ a;;C) HC p = Send Sig' q e a (epp_C D ps C HC' p).
Proof.
intros. rename a into A. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim bproj_dec. induction a0; simpl. 2: contr HC.
elim bproj_dec. induction a0; simpl. 2: contr HC'.
inversion_clear p0; try tauto.
rewrite (bproj_unique _ _ _ _ _ p1 H0); auto.
Qed.

Lemma epp_C_Com_q : forall D ps C p e q x a HC HC', p <> q -> In q ps ->
  epp_C D ps (p # e --> q $ x @ a;;C) HC q = Recv Sig' p x a (epp_C D ps C HC' q).
Proof.
intros. rename a into A. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim bproj_dec. induction a0; simpl. 2: contr HC.
elim bproj_dec. induction a0; simpl. 2: contr HC'.
inversion p0; try tauto.
rewrite (bproj_unique _ _ _ _ _ p1 H10); auto.
Qed.

Lemma epp_C_Com_r : forall D ps C p e q x a HC HC' r, p <> r -> q <> r ->
  epp_C D ps (p # e --> q $ x @ a;;C) HC r = epp_C D ps C HC' r.
Proof.
intros. rename a into A. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim bproj_dec. induction a0; simpl. 2: contr HC.
elim bproj_dec. induction a0; simpl. 2: contr HC'.
inversion p0; try tauto.
rewrite (bproj_unique _ _ _ _ _ p1 H10); auto.
Qed.

Lemma epp_C_Sel_p : forall D ps C p q l a HC HC', In p ps ->
  epp_C D ps (p --> q[l] @ a;;C) HC p = Sel Sig' q l a (epp_C D ps C HC' p).
Proof.
intros. rename a into A. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim bproj_dec. induction a0; simpl. 2: contr HC.
elim bproj_dec. induction a0; simpl. 2: contr HC'.
inversion p0; try tauto.
rewrite (bproj_unique _ _ _ _ _ p1 H8); auto.
Qed.

Lemma epp_C_Sel_ql : forall D ps C p q a HC HC', p <> q -> In q ps ->
  epp_C D ps (p --> q[left] @ a;;C) HC q
  = Branching Sig' p (Some (a,epp_C D ps C HC' q)) None.
Proof.
intros. rename a into A. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim bproj_dec. induction a0; simpl. 2: contr HC.
elim bproj_dec. induction a0; simpl. 2: contr HC'.
inversion p0; try tauto.
rewrite (bproj_unique _ _ _ _ _ p1 H8); auto.
Qed.

Lemma epp_C_Sel_qr : forall D ps C p q a HC HC', p <> q -> In q ps ->
  epp_C D ps (p --> q[right] @ a;;C) HC q
  = Branching Sig' p None (Some (a,epp_C D ps C HC' q)).
Proof.
intros. rename a into A. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim bproj_dec. induction a0; simpl. 2: contr HC.
elim bproj_dec. induction a0; simpl. 2: contr HC'.
inversion p0; try tauto.
rewrite (bproj_unique _ _ _ _ _ p1 H8); auto.
Qed.

Lemma epp_C_Sel_r : forall D ps C p q l a HC HC' r, p <> r -> q <> r ->
  epp_C D ps (p --> q[l] @ a;;C) HC r = epp_C D ps C HC' r.
Proof.
intros. rename a into A. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim bproj_dec. induction a0; simpl. 2: contr HC.
elim bproj_dec. induction a0; simpl. 2: contr HC'.
inversion p0; try tauto.
rewrite (bproj_unique _ _ _ _ _ p1 H9); auto.
Qed.

Lemma epp_C_Cond_p : forall D ps p b C1 C2 HC HC1 HC2, In p ps ->
  epp_C D ps (If p ?? b Then C1 Else C2) HC p
  = Cond Sig' b (epp_C D ps C1 HC1 p) (epp_C D ps C2 HC2 p).
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim bproj_dec. induction a0; simpl. 2: contr HC.
elim bproj_dec. induction a0; simpl. 2: contr HC1.
elim bproj_dec. induction a0; simpl. 2: contr HC2.
inversion p0; try tauto.
rewrite (bproj_unique _ _ _ _ _ p1 H7), (bproj_unique _ _ _ _ _ p2 H8); auto.
Qed.

Lemma epp_C_Cond_r : forall D ps (p:Pid) b C1 C2 HC HC1 HC2 r, p <> r ->
  epp_C D ps C1 HC1 r [V] epp_C D ps C2 HC2 r
  == epp_C D ps (If p ?? b Then C1 Else C2) HC r.
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: constructor.
elim bproj_dec. induction a0; simpl. 2: contr HC1.
elim bproj_dec. induction a0; simpl. 2: contr HC2.
elim bproj_dec. induction a0; simpl. 2: contr HC.
inversion p2; try tauto.
rewrite (bproj_unique _ _ _ _ _ p0 H5), (bproj_unique _ _ _ _ _ p1 H8); auto.
Qed.

(*
Lemma epp_C_Then_r : forall D ps (p:Pid) b C1 C2 HC HC1 HC2 r, p <> r ->
  epp_C D ps C1 HC1 r = epp_C D ps C2 HC2 r ->
  epp_C D ps (If p ?? b Then C1 Else C2) HC r = epp_C D ps C1 HC1 r.
Proof.
intros.
eapply merge_unique.
apply epp_C_Cond_r with (HC1:=HC1) (HC2:=HC2); auto.
rewrite H0. apply merge_idempotent.
Qed.

Lemma epp_C_Else_r : forall D ps (p:Pid) b C1 C2 HC HC1 HC2 r, p <> r ->
  epp_C D ps C1 HC1 r = epp_C D ps C2 HC2 r ->
  epp_C D ps (If p ?? b Then C1 Else C2) HC r = epp_C D ps C2 HC2 r.
Proof.
intros.
rewrite epp_C_Then_r with (HC1:=HC1) (HC2:=HC2); auto.
Qed.
*)

Lemma epp_C_Call : forall D ps X p HC, In p ps -> In p (fst (D X)) ->
  epp_C D ps (CC.Call X) HC p = Call Sig' (X,p).
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim bproj_dec. induction a0; simpl. 2: contr HC.
inversion p0; try tauto.
Qed.

Lemma epp_C_Call_out : forall D ps X p HC, ~In p (fst (D X)) ->
  epp_C D ps (CC.Call X) HC p = End _.
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim bproj_dec. induction a0; simpl. 2: contr HC.
inversion p0; try tauto.
Qed.

Lemma epp_C_RT_Call : forall D ps X p ps' C HC, In p ps -> In p ps' ->
  epp_C D ps (RT_Call X ps' C) HC p = Call Sig' (X,p).
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim bproj_dec. induction a0; simpl. 2: contr HC.
inversion p0; try tauto.
Qed.

Lemma epp_C_RT_Call_out : forall D ps X p ps' C HC HC', ~In p ps' ->
  epp_C D ps (RT_Call X ps' C) HC p = epp_C D ps C HC' p.
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim bproj_dec. induction a0; simpl. 2: contr HC.
elim bproj_dec. induction a0; simpl. 2: contr HC'.
inversion p0; try tauto.
rewrite (bproj_unique _ _ _ _ _ p1 H7); auto.
Qed.

Lemma epp_C_End : forall D ps p HC, epp_C D ps CC.End HC p = End _.
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim bproj_dec. induction a0; simpl. 2: contr HC.
inversion p0; try tauto.
Qed.

(** Characterizations lemmas for branching. *)

Lemma bproj_not_Branching_None_None : forall D C r q,
  ~ [[D,C | r]] == (q & None // None).
Proof.
intros; intro. induction C; simpl. induction e. 2: induction t2.
all: inversion H; try tauto.
inversion H10.
rewrite H14, <- H11, <- H12 in *; tauto.
Qed.

Lemma epp_C_not_Branching_None_None : forall D ps C HC p q,
  epp_C D ps C HC p <> Branching Sig' q None None.
Proof.
intros.
unfold epp_C.
elim In_dec; intro; simpl. 2: discriminate.
elim bproj_dec; simpl. induction a0; intro. 2: contr HC.
rewrite H in p0.
revert p0. apply bproj_not_Branching_None_None.
Qed.

Lemma bproj_Sel_Branching_l : forall D C p q a Bp Bl Br,
  [[D,C | p]] == @Sel Sig' q left a Bp ->
  [[D,C | q]] == @Branching Sig' p Bl Br -> Bl <> None /\ Br = None.
Proof.
induction C; simpl; intros.
rename t into a'. induction e. 2: induction t1.
all: inversion H; inversion H0; eauto.
+ split; auto; discriminate.
+ tauto.
+ tauto.
+ revert H6 H9. inversion_clear H11; intros.
  revert H17 H20; inversion_clear H22; intros.
  all: try (split; auto; discriminate; fail).
  all: exfalso.
  all: try (specialize (IHC1 _ _ _ _ _ _ H9 H17); tauto).
  all: try (specialize (IHC1 _ _ _ _ _ _ H9 H20); tauto).
  all: try (specialize (IHC2 _ _ _ _ _ _ H11 H20); tauto).
  all: try (specialize (IHC2 _ _ _ _ _ _ H11 H22); tauto).
  - specialize (IHC2 _ _ _ _ _ _ H11 H22).
    inversion_clear IHC2; discriminate.
  - specialize (IHC1 _ _ _ _ _ _ H9 H20).
    inversion_clear IHC1; discriminate.
  - specialize (IHC1 _ _ _ _ _ _ H9 H22).
    inversion_clear IHC1; discriminate.
Qed.

Lemma epp_C_Sel_Branching_l : forall D ps C HC p q a Bp Bl Br,
  epp_C D ps C HC p = Sel Sig' q left a Bp ->
  epp_C D ps C HC q = Branching Sig' p Bl Br -> Bl <> None /\ Br = None.
Proof.
intros.
revert H H0. unfold epp_C.
elim In_dec. 2: discriminate.
elim In_dec. 2: discriminate.
elim bproj_dec; intro Hc. induction Hc.
elim bproj_dec; intro Hc. induction Hc.
simpl; intros.
rewrite H in p0; rewrite H0 in p1.
apply (bproj_Sel_Branching_l _ _ _ _ _ _ _ _ p0 p1).
do 2 intro. exfalso. contr_aux HC.
do 2 intro. exfalso. contr_aux HC.
Qed.

Lemma bproj_Sel_Branching_r : forall D C p q a Bp Bl Br,
  [[D,C | p]] == @Sel Sig' q right a Bp ->
  [[D,C | q]] == @Branching Sig' p Bl Br -> Bl = None /\ Br <> None.
Proof.
induction C; simpl; intros.
rename t into a'. induction e. 2: induction t1.
all: inversion H; inversion H0; eauto.
+ tauto.
+ split; auto; discriminate.
+ tauto.
+ revert H6 H9. inversion_clear H11; intros.
  revert H17 H20; inversion_clear H22; intros.
  all: try (split; auto; discriminate; fail).
  all: exfalso.
  all: try (specialize (IHC1 _ _ _ _ _ _ H9 H17); tauto).
  all: try (specialize (IHC1 _ _ _ _ _ _ H9 H20); tauto).
  all: try (specialize (IHC2 _ _ _ _ _ _ H11 H20); tauto).
  all: try (specialize (IHC2 _ _ _ _ _ _ H11 H22); tauto).
  - specialize (IHC2 _ _ _ _ _ _ H11 H22).
    inversion_clear IHC2; discriminate.
  - specialize (IHC1 _ _ _ _ _ _ H9 H20).
    inversion_clear IHC1; discriminate.
  - specialize (IHC1 _ _ _ _ _ _ H9 H22).
    inversion_clear IHC1; discriminate.
Qed.

Lemma epp_C_Sel_Branching_r : forall D ps C HC p q a Bp Bl Br,
  epp_C D ps C HC p = Sel Sig' q right a Bp ->
  epp_C D ps C HC q = Branching Sig' p Bl Br -> Bl = None /\ Br <> None.
Proof.
intros.
revert H H0. unfold epp_C.
elim In_dec. 2: discriminate.
elim In_dec. 2: discriminate.
elim bproj_dec; intro Hc. induction Hc.
elim bproj_dec; intro Hc. induction Hc.
simpl; intros.
rewrite H in p0; rewrite H0 in p1.
apply (bproj_Sel_Branching_r _ _ _ _ _ _ _ _ p0 p1).
do 2 intro. exfalso. contr_aux HC.
do 2 intro. exfalso. contr_aux HC.
Qed.

(** Inversion lemmas for conditionals. *)

Lemma epp_C_Cond_Send_inv : forall D ps p b C1 C2 HC HC1 HC2 r q e a B,
  epp_C D ps (If p ?? b Then C1 Else C2) HC r = Send Sig' q e a B ->
  exists B1 B2, epp_C D ps C1 HC1 r = Send Sig' q e a B1
  /\ epp_C D ps C2 HC2 r = Send Sig' q e a B2 /\ B1 [V] B2 == B.
Proof.
intros.
assert (p <> r).
1: {
  intro. revert HC H; rewrite H0. intro.
  elim (In_dec (@eq_dec Pid) r ps); intro.
  rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2); auto. discriminate.
  rewrite epp_C_out; auto. discriminate.
}
generalize (epp_C_Cond_r _ _ _ _ _ _ HC HC1 HC2 _ H0); intros.
rewrite H in H1.
inversion_clear H1; eauto.
Qed.

Lemma epp_C_Cond_Recv_inv : forall D ps p b C1 C2 HC HC1 HC2 r q x a B,
  epp_C D ps (If p ?? b Then C1 Else C2) HC r = Recv Sig' q x a B ->
  exists B1 B2, epp_C D ps C1 HC1 r = Recv Sig' q x a B1
  /\ epp_C D ps C2 HC2 r = Recv Sig' q x a B2 /\ B1 [V] B2 == B.
Proof.
intros.
assert (p <> r).
1: {
  intro. revert HC H; rewrite H0. intro.
  elim (In_dec (@eq_dec Pid) r ps); intro.
  rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2); auto. discriminate.
  rewrite epp_C_out; auto. discriminate.
}
generalize (epp_C_Cond_r _ _ _ _ _ _ HC HC1 HC2 _ H0); intros.
rewrite H in H1.
inversion_clear H1; eauto.
Qed.

Lemma epp_C_Cond_Sel_inv : forall D ps p b C1 C2 HC HC1 HC2 r q l a B,
  epp_C D ps (If p ?? b Then C1 Else C2) HC r = Sel Sig' q l a B ->
  exists B1 B2, epp_C D ps C1 HC1 r = Sel Sig' q l a B1
  /\ epp_C D ps C2 HC2 r = Sel Sig' q l a B2 /\ B1 [V] B2 == B.
Proof.
intros.
assert (p <> r).
1: {
  intro. revert HC H; rewrite H0. intro.
  elim (In_dec (@eq_dec Pid) r ps); intro.
  rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2); auto. discriminate.
  rewrite epp_C_out; auto. discriminate.
}
generalize (epp_C_Cond_r _ _ _ _ _ _ HC HC1 HC2 _ H0); intros.
rewrite H in H1.
inversion H1; eauto.
Qed.

Lemma epp_C_Cond_Branching_l_inv : forall D ps p b C1 C2 HC HC1 HC2 r q a B,
  epp_C D ps (If p ?? b Then C1 Else C2) HC r = Branching Sig' q (Some (a,B)) None ->
  exists B1 B2, epp_C D ps C1 HC1 r = Branching Sig' q (Some (a,B1)) None
  /\ epp_C D ps C2 HC2 r = Branching Sig' q (Some (a,B2)) None /\ B1 [V] B2 == B.
Proof.
intros.
assert (p <> r).
1: {
  intro. revert HC H; rewrite H0. intro.
  elim (In_dec (@eq_dec Pid) r ps); intro.
  rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2); auto. discriminate.
  rewrite epp_C_out; auto. discriminate.
}
generalize (epp_C_Cond_r _ _ _ _ _ _ HC HC1 HC2 _ H0); intros.
rewrite H in H1.
inversion H1; eauto.
all: eelim epp_C_not_Branching_None_None; eauto.
Qed.

Lemma epp_C_Cond_Branching_r_inv : forall D ps p b C1 C2 HC HC1 HC2 r q a B,
  epp_C D ps (If p ?? b Then C1 Else C2) HC r = Branching Sig' q None (Some (a,B)) ->
  exists B1 B2, epp_C D ps C1 HC1 r = Branching Sig' q None (Some (a,B1))
  /\ epp_C D ps C2 HC2 r = Branching Sig' q None (Some (a,B2)) /\ B1 [V] B2 == B.
Proof.
intros.
assert (p <> r).
1: {
  intro. revert HC H; rewrite H0. intro.
  elim (In_dec (@eq_dec Pid) r ps); intro.
  rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2); auto. discriminate.
  rewrite epp_C_out; auto. discriminate.
}
generalize (epp_C_Cond_r _ _ _ _ _ _ HC HC1 HC2 _ H0); intros.
rewrite H in H1.
inversion H1; eauto.
all: eelim epp_C_not_Branching_None_None; eauto.
Qed.

Lemma epp_C_Cond_Cond_inv : forall D ps p b b' C1 C2 HC HC1 HC2 r Bt Be,
  p <> r -> epp_C D ps (If p ?? b Then C1 Else C2) HC r = Cond Sig' b' Bt Be ->
  exists B1t B1e B2t B2e, epp_C D ps C1 HC1 r = Cond Sig' b' B1t B1e
                       /\ epp_C D ps C2 HC2 r = Cond Sig' b' B2t B2e
                       /\ B1t [V] B2t == Bt /\ B1e [V] B2e == Be.
Proof.
intros.
generalize (epp_C_Cond_r _ _ _ _ _ _ HC HC1 HC2 _ H); intros.
rewrite H0 in H1.
inversion H1.
exists Bt1, Be1, Bt2, Be2; auto.
Qed.

Open Scope CC_scope.

Section Projectability.

(** ** Properties of projectability
  All variants of parameterized projectability are decidable. *)

Lemma projectable_B_dec : forall D C p,
  { projectable_B D C p } + { ~projectable_B D C p }.
Proof.
intros. elim (bproj_dec D C p); auto.
left. induction a. red. eauto.
Qed.

Lemma projectable_C_dec : forall D ps C,
  { projectable_C D C ps } + { ~projectable_C D C ps }.
Proof.
intros. apply Forall_dec; intro.
elim (projectable_B_dec D C x); auto.
Qed.

Lemma projectable_D_dec : forall Xs D,
  { projectable_D Xs D } + { ~projectable_D Xs D }.
Proof.
intros. apply Forall_dec; intro.
apply projectable_C_dec.
Qed.

Lemma projectable_dec : forall Xs ps P,
  { projectable Xs ps P } + { ~projectable Xs ps P }.
Proof.
intros.
elim (projectable_C_dec (Procedures _ P) ps (Main P)); intro HC.
2: right; intro; inversion_clear H; auto.
elim (projectable_D_dec Xs (Procedures _ P)); intro HD.
2: right; intro; destroy H; auto.
generalize (fun p => In_dec (@eq_dec Pid) p ps); intro.
elim (Forall_dec (fun p => In p ps)) with (CCC_pn (Main P) (fun _ => nil)); auto; intro Hps.
1: elim (Forall_dec (fun X => forall p, In p (CCC_pn (snd (Procedures _ P X)) (fun _ => nil)) -> In p ps)) with Xs; intro HXs1.
1: elim (Forall_dec (fun X => forall p, In p (fst (Procedures _ P X)) -> In p ps)) with Xs; intro HXs2.
+ left. rewrite Forall_forall in Hps, HXs1, HXs2.
  repeat split; eauto.
+ right; intro; apply HXs2.
  destroy H. rewrite Forall_forall; eauto.
+ elim (Forall_dec (fun p => In p ps)) with (fst (Procedures _ P HXs2)); auto.
  - left; rewrite Forall_forall in a; auto.
  - right; intro. apply b; rewrite Forall_forall; auto.
+ right; intro; apply HXs1.
  destroy H. rewrite Forall_forall; eauto.
+ elim (Forall_dec (fun p => In p ps)) with (CCC_pn (snd (Procedures _ P HXs1)) (fun _ => nil)); auto.
  - left. rewrite Forall_forall in a; eauto.
  - right; intro. apply b; rewrite Forall_forall; eauto.
+ right; intro; apply Hps.
  destroy H. rewrite Forall_forall; eauto.
Qed.

(** Inversion lemmas for projectability. *)

Lemma projectable_C_inv_Com : forall D ps p e q x a C,
  projectable_C D (p#e --> q$x@a;; C) ps -> projectable_C D C ps.
Proof.
intros. red; red in H.
rewrite Forall_forall; rewrite Forall_forall in H.
intros. induction (H _ H0) as [B HB]; clear H.
red; inversion HB; eauto.
Qed.

Lemma projectable_C_inv_Sel : forall D ps p q l a C,
  projectable_C D (p --> q[l]@a;; C) ps -> projectable_C D C ps.
Proof.
intros. red; red in H.
rewrite Forall_forall; rewrite Forall_forall in H.
intros. induction (H _ H0) as [B HB]; clear H.
red; inversion HB; eauto.
Qed.

Lemma projectable_C_inv_Eta : forall D ps eta a C,
  projectable_C D (eta@a;; C) ps -> projectable_C D C ps.
Proof.
intros; induction eta.
eapply projectable_C_inv_Com; eauto.
eapply projectable_C_inv_Sel; eauto.
Qed.

Lemma projectable_C_inv_Then : forall D ps p b C1 C2,
  projectable_C D (If p ?? b Then C1 Else C2) ps -> projectable_C D C1 ps.
Proof.
intros. red; red in H.
rewrite Forall_forall; rewrite Forall_forall in H.
intros. induction (H _ H0) as [B HB]; clear H.
red; inversion HB; eauto.
Qed.

Lemma projectable_C_inv_Else : forall D ps p b C1 C2,
  projectable_C D (If p ?? b Then C1 Else C2) ps -> projectable_C D C2 ps.
Proof.
intros. red; red in H.
rewrite Forall_forall; rewrite Forall_forall in H.
intros. induction (H _ H0) as [B HB]; clear H.
red; inversion HB; eauto.
Qed.

(** More inversion lemmas about program projectability. *)

Lemma projectable_inv_Eta : forall Xs ps D eta a C,
  projectable Xs ps (D,eta@a;;C) -> projectable Xs ps (D,C).
Proof.
intros.
destroy H; repeat split; auto.
apply projectable_C_inv_Eta with eta a; auto.
intros. apply H2; simpl. sup.
Qed.

Lemma projectable_inv_Com : forall Xs ps D p e q x a C,
  projectable Xs ps (D,p#e-->q$x@a;;C) -> projectable Xs ps (D,C).
Proof. intros; eapply projectable_inv_Eta; eauto. Qed.

Lemma projectable_inv_Sel : forall Xs ps D p q l a C,
  projectable Xs ps (D,p-->q[l]@a;;C) -> projectable Xs ps (D,C).
Proof. intros; eapply projectable_inv_Eta; eauto. Qed.

Lemma projectable_inv_Then : forall Xs ps D p b C1 C2,
  projectable Xs ps (D,If p ?? b Then C1 Else C2) -> projectable Xs ps (D,C1).
Proof.
intros.
destroy H; repeat split; auto.
apply projectable_C_inv_Then with p b C2; auto.
intros. apply H2; simpl. sup; sup.
Qed.

Lemma projectable_inv_Else : forall Xs ps D p b C1 C2,
  projectable Xs ps (D,If p ?? b Then C1 Else C2) -> projectable Xs ps (D,C2).
Proof.
intros.
destroy H; repeat split; auto.
apply projectable_C_inv_Else with p b C1; auto.
intros. apply H2; simpl. sup; sup.
Qed.

Lemma projectable_inv_RT_Call : forall Xs ps D X p ps' C,
  projectable Xs ps (D,RT_Call X ps' C) -> (exists B, [[D,C | p]] == B) ->
  projectable Xs ps (D,RT_Call X (ps' [\] p) C).
Proof.
intros.
destroy H; repeat split; auto.
+ clear H H4 H3 H2.
  intros. red; red in H1.
  rewrite Forall_forall; rewrite Forall_forall in H1.
  intros. case (eq_dec x p); intro Hx.
  - rewrite Hx in *; clear x Hx.
    induction H0 as [B HB]; clear H1 H.
    exists B. constructor; auto.
    intro. apply set_remove'_2 in H; auto.
  - induction (H1 _ H) as [B HB]; clear H1.
    exists B. simpl in *.
    inversion HB. all: constructor; auto.
    apply set_remove'_3; auto.
    intro; apply H7. apply set_remove'_1 in H9; auto.
+ intro r. simpl; sup.
  intros. apply H3; simpl. sup.
  elim H5; auto.
  left. eapply set_remove'_1; eauto.
Qed.

(** The corresponding lemmas for [RT_Call] do not hold, and indeed projectability
  is not preserved by reductions, so we need a stronger notion. *)

Fixpoint str_proj D (C:Choreography Sig) (r:Pid) : Prop :=
match C with
| eta @ a;; C' => str_proj D C' r
| If p ?? b Then C1 Else C2 =>
     str_proj D C1 r /\ str_proj D C2 r /\ projectable_B D C r
| RT_Call X ps C =>
     str_proj D C r /\ (forall p, In p ps -> In p (fst (D X))
  /\ forall B B', [[D,snd (D X) | p]] == B -> [[D,C | p]] == B' -> B [>>] B')
| _                         => True
end.

Lemma str_proj_C : forall D C r, str_proj D C r -> projectable_B D C r.
Proof.
induction C; simpl.
+ intros. induction (IHC _ H) as [B HB]; auto. clear H.
  induction e.
  all: eq_elim r t0 Hr1. 2: eq_elim r t2 Hr2. 5: eq_elim r t1 Hr2. 5: induction t2.
  exists (@Send Sig' t2 t1 t B); constructor; auto.
  exists (@Recv Sig' t0 t3 t B); constructor; auto.
  exists B; constructor; auto.
  exists (@Sel Sig' t1 t2 t B); constructor; auto.
  exists (@Branching Sig' t0 (Some (t,B)) None); constructor; auto.
  exists (@Branching Sig' t0 None (Some (t,B))); constructor; auto.
  exists B; constructor; auto.
+ tauto.
+ intro. elim (In_dec (@eq_dec Pid) r (fst (D t))).
  exists (Call Sig' (t,r)); constructor; auto.
  exists (End _); constructor; auto.
+ intro. elim (In_dec (@eq_dec Pid) r l).
  exists (Call Sig' (t,r)); constructor; auto.
  intros. destruct H. induction (IHC _ H) as [B HB].
  exists B. constructor; auto.
+ exists (End _); constructor.
Qed.

Lemma str_proj_C' : forall D C ps,
  (forall r, In r ps -> str_proj D C r) -> projectable_C D C ps.
Proof.
intros; red; rewrite Forall_forall.
intros. apply str_proj_C; auto.
Qed.

Lemma initial_str_proj : forall C, initial C ->
  forall D ps, projectable_C D C ps -> forall r, In r ps -> str_proj D C r.
Proof.
induction C; auto; simpl; intros.
+ induction e.
  - apply projectable_C_inv_Com in H0; eauto.
  - apply projectable_C_inv_Sel in H0; eauto.
+ inversion_clear H. repeat split.
  - apply projectable_C_inv_Then in H0; eauto.
  - apply projectable_C_inv_Else in H0; eauto.
  - red in H0. rewrite Forall_forall in H0; auto.
+ inversion H.
Qed.

Lemma initial_str_proj' : forall D C r, initial C ->
  ~In r (CCC_pn C (Names D)) -> str_proj D C r.
Proof.
induction C; simpl; intros; auto.
+ apply IHC; auto. intro; apply H0. sup.
+ destroy H; repeat split.
  - apply IHC1; auto. intro; apply H0. sup; sup.
  - apply IHC2; auto. intro; apply H0. sup; sup.
  - revert H0. intros.
    exists (End _). apply bproj_not_In; simpl; auto.
+ destroy H.
Qed.

(** Inversion lemmas for strong projectability. *)

Lemma str_proj_inv_Eta : forall D eta C a p,
  str_proj D (eta@a;;C) p -> str_proj D C p.
Proof. auto. Qed.

Lemma str_proj_inv_Then : forall D p b C1 C2 r,
  str_proj D (If p ?? b Then C1 Else C2) r -> str_proj D C1 r.
Proof. intros. red in H. tauto. Qed.

Lemma str_proj_inv_Else : forall D p b C1 C2 r,
  str_proj D (If p ?? b Then C1 Else C2) r -> str_proj D C2 r.
Proof. intros. red in H. tauto. Qed.

Lemma str_proj_inv_RT_Call : forall D ps X C p,
  str_proj D (RT_Call ps X C) p -> str_proj D C p.
Proof. intros. red in H. tauto. Qed.

(** Miscellaneous. *)

Lemma CCC_To_Call_ann : forall D C s X p C' s',
  <<C,s>> --[RL_Call X p,D]--> <<C',s'>> -> str_proj D C p -> In p (fst (D X)).
Proof.
induction C; intros; inversion H; eauto; inversion H0; eauto.
all: rewrite <- H4; specialize (H13 _ H11); tauto.
Qed.

Lemma Program_WF_D_str_proj : forall Xs ps P,
  CC.Program_WF _ Xs P -> projectable Xs ps P -> well_ann _ P ->
  forall X p, In X Xs -> In p ps -> str_proj (Procedures _ P) (CC.Procs P X) p.
Proof.
intros. destroy H.
elim (H X); auto.
intros. clear H; destroy H8.
destroy H0.
elim (In_dec (@eq_dec Pid) p (Vars P X)); intros.
+ apply initial_str_proj with (Vars P X); auto.
  red in H11. rewrite Forall_forall in H11. apply H11; auto.
+ apply initial_str_proj'; auto.
  intro; apply b, H1. auto.
Qed.

End Projectability.

Section EPP_Theorem.

(** ** The EPP Theorem
  Lemmas about reduction and projection. *)

Lemma CCC_To_bproj_Com_p : forall D C s C' s' p q v x,
  str_proj D C p -> <<C,s>> --[RL_Com p v q x,D]--> <<C',s'>> ->
  exists e a Bp, [[D,C | p]] == @Send Sig' q e a Bp /\ [[D,C' | p]] == Bp
              /\ v = eval_on_state Ev e s p.
Proof.
intros.
rename H into HC, H0 into H.
revert C' HC H.
induction C; intros; inversion H.
+ unfold v1. rename e0 into e', t into a'.
  apply str_proj_inv_Eta, str_proj_C in HC.
  induction HC as [B HB]. rewrite <- H4 in *.
  exists e', a', B; repeat split; auto.
  constructor; auto.
+ elim IHC with C'0; auto.
  clear C' H5 s'0 H6 ann H0 t0 H4 s0 H2 C0 H3 eta H1 H8 H.
  rename C'0 into C'; intros.
  induction H as [a [Bp [H1 [H2 H3] ] ] ].
  induction e; destroy H7; destroy H; simpl; repeat split.
  exists x0, a, Bp. repeat split; try constructor; auto.
  exists x0, a, Bp. repeat split; try constructor; auto.
+ clear H s'0 H7 C' H6 s0 H3 C3 H4 C0 H2 b H1 p0 H0 t1 H5.
  rename t into p', t0 into b. inversion_clear H8.
  elim IHC1 with C1'; auto. 2: apply HC.
  elim IHC2 with C2'; auto. 2: apply HC.
  clear IHC1 IHC2 H9 H10; intros.
  destroy H1; destroy H2.
  rename x0 into e, x1 into e', x2 into a, x3 into B2, x4 into a', x5 into B1.
  apply str_proj_C in HC; auto.
  induction HC as [B HB]. inversion HB.
  rewrite H10 in *. exfalso; auto.
  clear B4 H14 r H13 C3 H10 C0 H9 b0 H8 p0 H7 D0 H11.
  rewrite (bproj_unique _ _ _ _ _ H12 H5) in H17.
  rewrite (bproj_unique _ _ _ _ _ H15 H3) in H17.
  inversion H17. rewrite H13, H14 in *.
  exists e, a, B6; repeat split; auto.
  apply bproj_Cond' with (@Send Sig' q e a B1) (@Send Sig' q e a B2); auto.
  rewrite H8; auto.
  apply bproj_Cond' with B1 B2; auto.
+ elim IHC with C'0; auto; intros.
  2: apply HC; auto.
  apply disjoint_ps_Com in H7.
  destroy H9.
  assert (~In p l).
  1: specialize (H7 p). intro; apply H7; simpl; auto.
  exists x0, x1, x2; repeat split; try constructor; auto. 
Qed.

Lemma CCC_To_bproj_Com_q : forall D C s C' s' p q v x,
  str_proj D C q -> <<C,s>> --[RL_Com p v q x,D]--> <<C',s'>> ->
  p <> q -> exists a Bq, [[D,C | q]] == Recv Sig' p x a Bq /\ [[D,C' | q]] == Bq.
Proof.
intros.
rename H into HC, H0 into H.
revert C' HC H.
induction C; intros; inversion H.
+ unfold v1. rename e0 into e', t into a'.
  apply str_proj_inv_Eta, str_proj_C in HC.
  induction HC as [B HB]. rewrite <- H5 in *.
  exists a', B; repeat split; auto.
  constructor; auto.
+ elim IHC with C'0; auto.
  clear dependent C'.
  rename C'0 into C'; intros.
  induction H as [Bp [HB HB'] ].
  induction e; destroy H8; destroy H; simpl; repeat split.
  exists x0, Bp. repeat split; try constructor; auto.
  exists x0, Bp. repeat split; try constructor; auto.
+ clear H s'0 H8 C' H7 t1 H6 s0 H4 C3 H5 C0 H3 b H2 p0 H0.
  rename t into p', t0 into b. inversion_clear H9.
  elim IHC1 with C1'; auto. 2: apply HC.
  elim IHC2 with C2'; auto. 2: apply HC.
  clear IHC1 IHC2 H11 H10; intros.
  induction H2 as [Bq [Hq1 Hq2] ].
  induction H3 as [Bq' [Hq'1 Hq'2] ].
  apply str_proj_C in HC; auto.
  induction HC as [B HB]. inversion HB.
  rewrite H5 in *. exfalso; auto.
  rewrite (bproj_unique _ _ _ _ _ H7 Hq'1) in H12.
  rewrite (bproj_unique _ _ _ _ _ H10 Hq1) in H12.
  inversion H12. rewrite <- H16, <- H18 in *.
  exists a, B5; repeat split; auto.
  apply bproj_Cond' with (@Recv Sig' p x a Bq') (@Recv Sig' p x a Bq); auto.
  constructor; auto.
  apply bproj_Cond' with Bq' Bq; auto.
+ elim IHC with C'0; auto; intros.
  2: apply HC; auto.
  apply disjoint_ps_Com in H8.
  induction H10 as [Bq [H' H''] ].
  assert (~In q l).
  1: specialize (H8 q). intro; apply H8; simpl; auto.
  exists x0, Bq; repeat split; try constructor; auto.
Qed.

Lemma CCC_To_bproj_Com_r : forall D C s C' s' p q v x r,
  str_proj D C r -> <<C,s>> --[RL_Com p v q x,D]--> <<C',s'>> ->
  p <> r -> q <> r -> exists B, [[D,C | r]] == B /\ [[D,C' | r]] == B.
Proof.
intros.
rename H into HC, H1 into Hpr, H2 into Hqr, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ rewrite <- H4. rewrite H5, H7, H8 in H0. rename e0 into e'.
  apply str_proj_inv_Eta, str_proj_C in HC.
  induction HC as [B HB]. rewrite <- H4 in *.
  exists B; repeat split; auto. constructor; auto.
+ simpl; elim IHC with C'0; auto.
  intros. inversion_clear H9.
  induction e.
  all: eq_elim r t1 Hr1. 2: eq_elim r t3 Hr2. 5: eq_elim r t2 Hr2. 5: induction t3.
  all: eexists; repeat split; constructor; eauto.
+ simpl. inversion_clear HC. inversion_clear H12.
  induction H14 as [B HB].
  induction (IHC1 H11 C1') as [Bt [HBt HBt'] ]; auto.
  induction (IHC2 H13 C2') as [Be [HBe HBe'] ]; auto.
  exists B; split; auto.
  inversion_clear HB. constructor; auto.
  1,2: erewrite bproj_unique; eauto.
  apply bproj_Cond' with B1 B2; auto.
  1,2: erewrite bproj_unique; eauto.
+ elim IHC with C'0; auto.
  intros. inversion_clear H9.
  2: apply str_proj_inv_RT_Call with t l; auto.
  elim (In_dec (@eq_dec Pid) r l); intro Hr.
  exists (Call Sig' (t,r)); split; constructor; auto.
  exists x0; split; constructor; auto.
Qed.

Lemma CCC_To_bproj_Sel_p : forall D C s C' s' p q l,
  str_proj D C p -> <<C,s>> --[RL_Sel p q l,D]--> <<C',s'>> ->
  exists a Bp, [[D,C | p]] == @Sel Sig' q l a Bp /\ [[D,C' | p]] == Bp.
Proof.
intros.
rename H into HC, H0 into H.
revert C' HC H.
induction C; intros; inversion H.
+ rename l0 into l', t into a'.
  apply str_proj_inv_Eta, str_proj_C in HC.
  induction HC as [B HB]. rewrite <- H4 in *.
  exists a', B; repeat split; auto.
  constructor; auto.
+ elim IHC with C'0; auto.
  clear C' H5 s'0 H6 ann H0 t0 H4 s0 H2 C0 H3 eta H1 H8 H.
  rename C'0 into C'; intros.
  induction H as [Bp [H1 H3] ].
  induction e; destroy H7; destroy H; simpl; repeat split.
  exists x, Bp. repeat split; try constructor; auto.
  exists x, Bp. repeat split; try constructor; auto.
+ clear H s'0 H7 C' H6 s0 H3 C3 H4 C0 H2 b H1 p0 H0 t1 H5.
  rename t into p', t0 into b. inversion_clear H8.
  elim IHC1 with C1'; auto. 2: apply HC.
  elim IHC2 with C2'; auto. 2: apply HC.
  clear IHC1 IHC2 H9 H10; intros.
  induction H1 as [B2 [HC2 HC2'] ].
  induction H2 as [B1 [HC1 HC1'] ].
  apply str_proj_C in HC; auto.
  induction HC as [B HB]. inversion HB.
  rewrite H4 in *. exfalso; auto.
  rewrite (bproj_unique _ _ _ _ _ H6 HC1) in H11.
  rewrite (bproj_unique _ _ _ _ _ H9 HC2) in H11.
  inversion H11. rewrite <- H15, <- H17 in *.
  exists a, B7; repeat split; auto.
  apply bproj_Cond' with (@Sel Sig' q l a B1) (@Sel Sig' q l a B2); auto.
  constructor; auto.
  apply bproj_Cond' with B1 B2; auto.
+ elim IHC with C'0; auto; intros.
  2: apply HC; auto.
  apply disjoint_ps_Sel in H7.
  induction H9 as [Bp [HC' HC''] ].
  assert (~In p l0).
  1: specialize (H7 p). intro; apply H7; simpl; auto.
  exists x, Bp; repeat split; try constructor; auto.
Qed.

Lemma CCC_To_bproj_Sel_ql : forall D C s C' s' p q,
  str_proj D C q -> <<C,s>> --[RL_Sel p q left,D]--> <<C',s'>> ->
  p <> q -> exists a Bq, [[D,C | q]] == @Branching Sig' p (Some (a,Bq)) None
            /\ [[D,C' | q]] == Bq.
Proof.
intros.
rename H into HC, H0 into H.
revert C' HC H.
induction C; intros; inversion H.
+ apply str_proj_inv_Eta, str_proj_C in HC.
  induction HC as [B HB]. rewrite <- H5 in *.
  exists t, B; repeat split; auto.
  constructor; auto.
+ elim IHC with C'0; auto.
  clear dependent C'.
  rename C'0 into C'; intros.
  induction H as [Bp [HB HB'] ].
  induction e; destroy H8; destroy H; simpl; repeat split.
  exists x, Bp. repeat split; try constructor; auto.
  exists x, Bp. repeat split; try constructor; auto.
+ clear H s'0 H8 C' H7 t1 H6 s0 H4 C3 H5 C0 H3 b H2 p0 H0.
  rename t into p', t0 into b. inversion_clear H9.
  elim IHC1 with C1'; auto. 2: apply HC.
  elim IHC2 with C2'; auto. 2: apply HC.
  clear IHC1 IHC2 H11 H10; intros.
  induction H2 as [Bq [Hq1 Hq2] ].
  induction H3 as [Bq' [Hq'1 Hq'2] ].
  apply str_proj_C in HC; auto.
  induction HC as [B HB]. inversion HB.
  rewrite H5 in *. exfalso; auto.
  rewrite (bproj_unique _ _ _ _ _ H7 Hq'1) in H12.
  rewrite (bproj_unique _ _ _ _ _ H10 Hq1) in H12.
  inversion H12. rewrite <- H15, <- H17 in *.
  exists aL, bL; repeat split; auto.
  apply bproj_Cond' with (@Branching Sig' p (Some (aL,Bq')) None)
                         (@Branching Sig' p (Some (aL,Bq)) None); auto.
  constructor; auto.
  apply bproj_Cond' with Bq' Bq; auto.
+ elim IHC with C'0; auto; intros.
  2: apply HC; auto.
  apply disjoint_ps_Sel in H8.
  induction H10 as [Bq [H' H''] ].
  assert (~In q l).
  1: specialize (H8 q). intro; apply H8; simpl; auto.
  exists x, Bq; repeat split; try constructor; auto.
Qed.

Lemma CCC_To_bproj_Sel_qr : forall D C s C' s' p q,
  str_proj D C q -> <<C,s>> --[RL_Sel p q right,D]--> <<C',s'>> ->
  p <> q -> exists a Bq, [[D,C | q]] == @Branching Sig' p None (Some (a,Bq))
            /\ [[D,C' | q]] == Bq.
Proof.
intros.
rename H into HC, H0 into H.
revert C' HC H.
induction C; intros; inversion H.
+ apply str_proj_inv_Eta, str_proj_C in HC.
  induction HC as [B HB]. rewrite <- H5 in *.
  exists t, B; repeat split; auto.
  constructor; auto.
+ elim IHC with C'0; auto.
  clear dependent C'.
  rename C'0 into C'; intros.
  induction H as [Bp [HB HB'] ].
  induction e; destroy H8; destroy H; simpl; repeat split.
  exists x, Bp. repeat split; try constructor; auto.
  exists x, Bp. repeat split; try constructor; auto.
+ clear H s'0 H8 C' H7 t1 H6 s0 H4 C3 H5 C0 H3 b H2 p0 H0.
  rename t into p', t0 into b. inversion_clear H9.
  elim IHC1 with C1'; auto. 2: apply HC.
  elim IHC2 with C2'; auto. 2: apply HC.
  clear IHC1 IHC2 H11 H10; intros.
  induction H2 as [Bq [Hq1 Hq2] ].
  induction H3 as [Bq' [Hq'1 Hq'2] ].
  apply str_proj_C in HC; auto.
  induction HC as [B HB]. inversion HB.
  rewrite H5 in *. exfalso; auto.
  rewrite (bproj_unique _ _ _ _ _ H7 Hq'1) in H12.
  rewrite (bproj_unique _ _ _ _ _ H10 Hq1) in H12.
  inversion H12. rewrite <- H15, <- H17 in *.
  exists aR, bR; repeat split; auto.
  apply bproj_Cond' with (@Branching Sig' p None (Some (aR,Bq')))
                         (@Branching Sig' p None (Some (aR,Bq))); auto.
  constructor; auto.
  apply bproj_Cond' with Bq' Bq; auto.
+ elim IHC with C'0; auto; intros.
  2: apply HC; auto.
  apply disjoint_ps_Sel in H8.
  induction H10 as [Bq [H' H''] ].
  assert (~In q l).
  1: specialize (H8 q). intro; apply H8; simpl; auto.
  exists x, Bq; repeat split; try constructor; auto.
Qed.

Lemma CCC_To_bproj_Sel_r : forall D C s C' s' p q l r,
  str_proj D C r -> <<C,s>> --[RL_Sel p q l,D]--> <<C',s'>> ->
  p <> r -> q <> r -> exists B, [[D,C | r]] == B /\ [[D,C' | r]] == B.
Proof.
intros.
rename H into HC, H1 into Hpr, H2 into Hqr, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ rewrite <- H4. rewrite H7, H6, H5 in H0.
  apply str_proj_inv_Eta, str_proj_C in HC.
  induction HC as [B HB]. rewrite <- H4 in *.
  exists B; repeat split; auto. constructor; auto.
+ simpl; elim IHC with C'0; auto.
  intros. inversion_clear H9.
  induction e.
  all: eq_elim r t1 Hr1. 2: eq_elim r t3 Hr2. 5: eq_elim r t2 Hr2. 5: induction t3.
  all: eexists; repeat split; constructor; eauto.
+ simpl. inversion_clear HC. inversion_clear H12.
  induction H14 as [B HB].
  induction (IHC1 H11 C1') as [Bt [HBt HBt'] ]; auto.
  induction (IHC2 H13 C2') as [Be [HBe HBe'] ]; auto.
  exists B; split; auto.
  inversion_clear HB. constructor; auto.
  1,2: erewrite bproj_unique; eauto.
  apply bproj_Cond' with B1 B2; auto.
  1,2: erewrite bproj_unique; eauto.
+ elim IHC with C'0; auto.
  intros. inversion_clear H9.
  2: apply str_proj_inv_RT_Call with t l0; auto.
  elim (In_dec (@eq_dec Pid) r l0); intro Hr.
  exists (Call Sig' (t,r)); split; constructor; auto.
  exists x; split; constructor; auto.
Qed.

Lemma CCC_To_bproj_Cond_p : forall D C s C' s' p,
  str_proj D C p -> <<C,s>> --[RL_Cond p,D]--> <<C',s'>> ->
  exists b Bt Be, [[D,C | p]] == @Cond Sig' b Bt Be
    /\ (eval_on_state BEv b s p = true -> [[D,C' | p]] == Bt)
    /\ (eval_on_state BEv b s p = false -> [[D,C' | p]] == Be).
Proof.
intros.
rename H into HC, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ elim IHC with C'0; intros; auto.
  induction H9 as [Bt [Be [HC' [Ht He] ] ] ]. rename x into b.
  induction e; destroy H7; simpl in H9, H7.
  all: exists b, Bt, Be; repeat split.
  all: simpl.
  4,5,6: case t3.
  all: constructor; auto.
+ rewrite H6 in HC. rewrite <- H5.
  clear s'0 H7 C' H5 p0 H6 s0 H2 C3 H4 C0 H3 b H1 p0 H0 H IHC1 IHC2.
  apply str_proj_C in HC.
  induction HC as [B HB]. inversion_clear HB. 2: tauto.
  exists t0, B1, B2. repeat split; auto.
  constructor; auto.
  intro. rewrite H9 in H1; inversion H1.
+ rewrite H6 in HC. rewrite <- H5.
  clear s'0 H7 C' H5 p0 H6 s0 H2 C3 H4 C0 H3 b H1 p0 H0 H IHC1 IHC2.
  apply str_proj_C in HC.
  induction HC as [B HB]. inversion_clear HB. 2: tauto.
  exists t0, B1, B2. repeat split; auto.
  constructor; auto.
  intro. rewrite H9 in H1; inversion H1.
+ clear s'0 H7 C' H6 t1 H5 s0 H3 C3 H4 C0 H2 b H1 p0 H0 H.
  elim IHC1 with C1'; auto. 2: apply HC.
  elim IHC2 with C2'; auto. 2: apply HC.
  clear IHC1 IHC2 H9 H10. intros.
  induction H as [Bt2 [Be2 [H1 [H2 H] ] ] ]; rename x into b2.
  induction H0 as [Bt1 [Be1 [H3 [H4 H0] ] ] ]; rename x0 into b1.
  apply str_proj_C in HC. induction HC as [B HB].
  revert H8. inversion_clear HB. intro; simpl in H8. tauto.
  simpl; intros.
  rewrite (bproj_unique _ _ _ _ _ H5 H3) in H8.
  rewrite (bproj_unique _ _ _ _ _ H6 H1) in H8.
  inversion H8. rewrite <- H14, <- H10 in *; clear b1 b2 H14 H10.
  rewrite <- H12 in *; clear Bt0 H11 Be0 H13 Bt3 H15 Be3 H16 B H12.
  exists b, Bt, Be. repeat split.
  - apply bproj_Cond' with B1 B2; auto.
    rewrite (bproj_unique _ _ _ _ _ H5 H3).
    rewrite (bproj_unique _ _ _ _ _ H6 H1).
    auto.
  - intro. apply bproj_Cond' with Bt1 Bt2; auto.
  - intro. apply bproj_Cond' with Be1 Be2; auto.
+ elim IHC with C'0; auto.
  intros. induction H9 as [Bt [Be [H9 [Ht He] ] ] ]. rename x into b.
  2: apply str_proj_inv_RT_Call with t l; auto.
  apply disjoint_ps_Cond in H7.
  exists b, Bt, Be. repeat split.
  all: constructor; auto.
Qed.

Lemma CCC_To_bproj_Cond_r : forall D C s C' s' p r,
  str_proj D C r -> <<C,s>> --[RL_Cond p,D]--> <<C',s'>> ->
  p <> r -> exists B B', [[D,C | r]] == B /\ [[D,C' | r]] == B' /\ B [>>] B'.
Proof.
intros.
rename H into HC, H1 into Hpr, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ clear s'0 H6 C' H5 t0 H4 s0 H2 C0 H3 eta H1 ann H0 H.
  elim IHC with C'0; intros; auto.
  rename C'0 into C'; clear IHC H8.
  destroy H.
  induction e; try (case t2); destroy H7; simpl in H2, H7.
  all: simpl.
  all: eq_elim r t0 Hr1. 2: eq_elim r t2 Hr2. 5,7: eq_elim r t1 Hr2.
  all: eexists; eexists; repeat split; [constructor; eauto | constructor; eauto | auto ].
  all: constructor; auto.
+ rewrite H6 in HC. rewrite <- H5.
  clear s'0 H7 C' H5 p0 H6 s0 H2 C3 H4 C0 H3 b H1 p0 H0 H IHC1 IHC2.
  apply str_proj_C in HC; induction HC as [B HB].
  inversion HB. tauto.
  exists B, B1; repeat split; auto.
  apply merge_is_upper_bound with B2; auto.
+ rewrite H6 in HC. rewrite <- H5.
  clear s'0 H7 C' H5 p0 H6 s0 H2 C3 H4 C0 H3 b H1 p0 H0 H IHC1 IHC2.
  apply str_proj_C in HC; induction HC as [B HB].
  inversion HB. tauto.
  exists B, B2; repeat split; auto.
  apply merge_is_upper_bound' with B1; auto.
+ clear s'0 H7 C' H6 t1 H5 s0 H3 C3 H4 C0 H2 b H1 p0 H0 H.
  elim IHC1 with C1'; auto. 2: apply HC.
  elim IHC2 with C2'; auto. 2: apply HC.
  clear IHC1 IHC2 H9 H10. intros.
  induction H as [B2 [H1 [H2 H] ] ]; rename x into b2.
  induction H0 as [B1 [H3 [H4 H0] ] ]; rename x0 into b1.
  apply str_proj_C in HC. induction HC as [B HB].
  inversion_clear HB.
  * exists (Cond Sig' t0 b1 b2), (Cond Sig' t0 B1 B2); simpl.
    repeat split; constructor; auto.
  * rewrite (bproj_unique _ _ _ _ _ H5 H3) in *; clear B0 H5.
    rewrite (bproj_unique _ _ _ _ _ H6 H1) in *; clear B3 H6.
    induction (MB_yields_merge _ _ _ _ _ _ H0 H H9) as [B' [HB HB'] ].
    exists B, B'; repeat split; auto.
    apply bproj_Cond' with b1 b2; auto.
    apply bproj_Cond' with B1 B2; auto.
+ elim (In_dec (@eq_dec Pid) r l); intro Hr.
  exists (Call Sig' (t,r)), (Call Sig' (t,r)); repeat split; constructor; auto.
  elim IHC with C'0; auto.
  2: apply HC.
  intros. destroy H9.
  apply disjoint_ps_Cond in H7.
  exists x, x0; repeat split; try constructor; auto.
Qed.

Lemma CCC_To_bproj_Call_p : forall D C s C' s' p X Xs,
  str_proj D C p ->
  (forall Y, In Y Xs -> str_proj D (snd (D Y)) p) ->
  (forall Y, CCC_pn (snd (D Y)) (Names D) [C] fst (D Y)) ->
  In X Xs -> <<C,s>> --[RL_Call X p,D]--> <<C',s'>> ->
  [[D,C | p]] == Call Sig' (X,p) /\
  exists B B', [[D,snd (D X) | p]] == B /\ [[D,C' | p]] == B' /\ B [>>] B'.
Proof.
intros.
rename H into HC, H0 into HD, H2 into HX, H1 into Hnames, H3 into H.
revert C' H.
induction C; intros; inversion H.
+ elim IHC with C'0; auto.
  induction e; try (case t3); destroy H7; simpl in H9, H7; simpl.
  all: intros; induction H11 as [B1 [B2 [HB1 [HB2 H'] ] ] ].
  all: split; [constructor; auto | eexists; eexists; repeat split; eauto].
  all: constructor; auto.
+ clear H s'0 H7 C' H6 s0 H3 C3 H4 C0 H2 b H1 p0 H0 t1 H5.
  induction HC as [HC' [HC'' [B HB] ] ].
  rename p into p', t into p, t0 into b. simpl in H8.
  elim IHC1 with C1'; auto.
  elim IHC2 with C2'; auto.
  clear IHC1 IHC2 H9 H10; intros.
  simpl.
  induction H0 as [B2 [B2' [H21 [H22 H23] ] ] ].
  induction H2 as [B1 [B1' [H11 [H12 H13] ] ] ].
  split. eapply bproj_Cond'; eauto. constructor.
  rewrite (bproj_unique _ _ _ _ _ H21 H11) in *; clear B2 H21.
  induction (MB_has_lub _ _ _ _ H13 H23) as [B' [HB'1 HB'2] ].
  exists B1, B'; repeat split; auto.
  apply bproj_Cond' with B1' B2'; auto.
+ split. constructor; auto.
  induction (str_proj_C _ _ _ (HD X HX)) as [B HB].
  exists B, B; repeat split; auto.
  apply MB_refl; auto.
+ simpl; split. constructor; auto.
  induction (str_proj_C _ _ _ (HD X HX)) as [B HB].
  exists B, B; repeat split; auto.
  constructor; auto. intro. apply set_remove'_2 in H9; auto.
  apply MB_refl.
+ apply disjoint_ps_Call in H7.
  elim IHC with C'0; auto. intros.
  split. constructor; auto.
  induction H10 as [B [B' [HB [HB' H'] ] ] ].
  exists B, B'; repeat split; auto.
  constructor; auto.
  apply HC; auto.
+ split. constructor; auto.
  induction (str_proj_C _ _ _ (HD X HX)) as [B HB].
  inversion_clear HC.
  induction (str_proj_C _ _ _ H11) as [B' HB'].
  exists B, B'; repeat split; auto.
  constructor; auto. intro. apply set_remove'_2 in H13; auto.
  apply (H12 p); auto. rewrite H3; auto.
+ simpl; split. constructor; auto.
  rewrite <- H5, <- H1, H3 in *; clear X0 H0 l H1 C0 H2 s0 H4 p0 H6 C' H5 s'0 H7 t H3.
  induction (str_proj_C _ _ _ (HD X HX)) as [B HB].
  inversion_clear HC.
  induction (str_proj_C _ _ _ H0) as [B' HB'].
  exists B, B'; repeat split; auto.
  apply (H1 p); auto.
Qed.

Lemma CCC_To_bproj_Call_r : forall D C s C' s' p X r,
  str_proj D C r ->
  (forall X, CCC_pn (snd (D X)) (Names D) [C] fst (D X)) ->
  <<C,s>> --[RL_Call X p,D]--> <<C',s'>> ->
  p <> r -> exists B, [[D,C | r]] == B /\ [[D,C' | r]] == B.
Proof.
intros.
rename H into HC, H0 into HD, H2 into Hpr, H1 into H.
revert C' H.
induction C; intros; inversion H.
+ elim IHC with C'0; auto.
  intros B [HB1 HB2].
  induction e. all: eq_elim r t1 Ht1.
  2: eq_elim r t3 Ht2. 5: eq_elim r t2 Ht2. 5: induction t3.
  all: eexists; split; econstructor; eauto.
+ induction HC as [HC1 [HC2 HC] ].
  elim IHC1 with C1'; auto. intros B1 [HB1 HB1'].
  elim IHC2 with C2'; auto. intros B2 [HB2 HB2'].
  eq_elim t r Hr.
  eexists; split; econstructor; eauto.
  simpl in H8.
  induction HC as [B HB]. inversion HB. tauto.
  exists B. split.
  apply bproj_Cond' with B0 B3; auto.
  apply bproj_Cond' with B1 B2; auto.
  rewrite (bproj_unique _ _ _ _ _ HB1 H16), (bproj_unique _ _ _ _ _ HB2 H19); auto.
+ rewrite H1 in *; clear s'0 H7 p0 H2 t H1 s0 H4 X0 H0.
  induction (str_proj_C _ _ _ HC) as [B HB].
  exists B; split; auto.
  inversion HB.
  elim Hpr. apply set_size_1 with (@eq_dec Pid) (fst (D X)); auto.
  apply bproj_not_In.
  intro. apply H2, HD; auto.
+ rewrite H1 in *; clear s'0 H7 p0 H2 t H1 s0 H4 X0 H0.
  induction (str_proj_C _ _ _ HC) as [B HB].
  exists B; split; auto.
  inversion HB.
  constructor. apply set_remove'_3; auto.
  apply bproj_not_In. intro.
  simpl in H9. rewrite set_union_iff in H9; induction H9.
  apply H2. eapply set_remove'_1; eauto.
  apply H2, HD; auto.
+ elim IHC with C'0; auto.
  2: apply HC.
  intros B [HB HB'].
  elim (in_dec (@eq_dec Pid) r l); intro Hr.
  eexists; split; constructor; auto.
  eexists; split; apply bproj_RT_Call_out; eauto.
+ rewrite H3, <- H1 in *; clear t H3 X0 H0 s'0 H7 p0 H6 s0 H4 C0 H2 l H1.
  induction (str_proj_C _ _ _ HC) as [B HB].
  exists B; split; auto.
  inversion HB.
  constructor. apply set_remove'_3; auto.
  constructor; auto.
  intro. apply H7. eapply set_remove'_1; eauto.
+ rewrite <- H5, <- H3 in *.
  induction (str_proj_C _ _ _ HC) as [B HB].
  exists B; split; auto.
  inversion HB; auto.
  elim Hpr. apply set_size_1 with (@eq_dec Pid) l; auto.
Qed.

Lemma CCC_To_bproj_disjoint : forall D C s tl C' s' ps p,
  (forall X, CCC_pn (snd (D X)) (Names D) [C] fst (D X)) ->
  (forall r, In r ps -> str_proj D C r) -> In p ps ->
  disjoint_p_rl p tl -> <<C,s>> --[tl,D]--> <<C',s'>> ->
  exists B B', [[D,C | p]] == B /\ [[D,C' | p]] == B' /\ B [>>] B'.
Proof.
do 7 intro. intros r HD.
intros. induction tl.
- destroy H1.
  induction (CCC_To_bproj_Com_r D C s C' s' p q v x r) as [B [HB1 HB2] ]; auto.
  exists B, B; repeat split; auto.
  apply MB_refl.
- destroy H1.
  induction (CCC_To_bproj_Sel_r D C s C' s' p q l r) as [B [HB1 HB2] ]; auto.
  exists B, B; repeat split; auto.
  apply MB_refl.
- apply (CCC_To_bproj_Cond_r D C s C' s' p r); auto.
- induction (CCC_To_bproj_Call_r D C s C' s' p X r) as [B [HB1 HB2] ]; auto.
  exists B, B; repeat split; auto.
  apply MB_refl.
Qed.

(** Projectability of well-formed programs is preserved by reductions. *)

Lemma CCC_To_projectable_C_Com : forall D ps C s C' s' p v q x,
  (forall p, In p ps -> str_proj D C p) ->
  <<C,s>> --[RL_Com p v q x,D]--> <<C',s'>> -> projectable_C D C' ps.
Proof.
intros.
red. rewrite Forall_forall; intro.
rename x0 into r. intro Hr. specialize (H _ Hr); clear Hr.
generalize (str_proj_C _ _ _ H); intro.
eq_elim p r Hpr. 2: eq_elim q r Hqr.
+ elim (CCC_To_bproj_Com_p _ _ _ _ _ _ _ _ _ H H0).
  intros. destroy H2. red; eauto.
+ elim (CCC_To_bproj_Com_q _ _ _ _ _ _ _ _ _ H H0); auto.
  intros. induction H2 as [Bq [H' H''] ]. red; eauto.
+ elim (CCC_To_bproj_Com_r _ _ _ _ _ _ _ _ _ _  H H0); auto.
  intros. inversion_clear H2. red; eauto.
Qed.

Lemma CCC_To_projectable_C_Sel : forall D ps C s C' s' p q l,
  (forall p, In p ps -> str_proj D C p) ->
  <<C,s>> --[RL_Sel p q l,D]--> <<C',s'>> -> projectable_C D C' ps.
Proof.
intros.
red. rewrite Forall_forall; intro.
rename x into r. intro Hr. specialize (H _ Hr); clear Hr.
generalize (str_proj_C _ _ _ H); intro.
eq_elim p r Hpr. 2: eq_elim q r Hqr.
+ elim (CCC_To_bproj_Sel_p _ _ _ _ _ _ _ _ H H0).
  intros. induction H2 as [Bp [H2 H2'] ]. red; eauto.
+ induction l.
  - elim (CCC_To_bproj_Sel_ql _ _ _ _ _ _ _ H H0); auto.
    intros. induction H2 as [Bq [H' H''] ]. red; eauto.
  - elim (CCC_To_bproj_Sel_qr _ _ _ _ _ _ _ H H0); auto.
    intros. induction H2 as [Bq [H' H''] ]. red; eauto.
+ elim (CCC_To_bproj_Sel_r _ _ _ _ _ _ _ _ _  H H0); auto.
  intros. inversion_clear H2. red; eauto.
Qed.

Lemma CCC_To_projectable_C_Cond : forall D ps C s C' s' p,
  (forall p, In p ps -> str_proj D C p) ->
  <<C,s>> --[RL_Cond p,D]--> <<C',s'>> -> projectable_C D C' ps.
Proof.
intros.
red. rewrite Forall_forall; intro.
rename x into r. intro Hr. specialize (H _ Hr); clear Hr.
generalize (str_proj_C _ _ _ H); intro.
eq_elim p r Hpr.
+ elim (CCC_To_bproj_Cond_p _ _ _ _ _ _ H H0).
  intros. destroy H2.
  case_eq (eval_on_state BEv x s p); red; eauto.
+ elim (CCC_To_bproj_Cond_r _ _ _ _ _ _ _ H H0); auto.
  intros. destroy H2. red; eauto.
Qed.

Lemma CCC_To_projectable_C_Call : forall D ps C s C' s' X p Xs,
  (forall p, In p ps -> str_proj D C p) ->
  (forall p Y, In p ps -> In Y Xs -> str_proj D (snd (D Y)) p) ->
  (forall Y, CCC_pn (snd (D Y)) (Names D) [C] fst (D Y)) ->
  In X Xs -> <<C,s>> --[RL_Call X p,D]--> <<C',s'>> -> projectable_C D C' ps.
Proof.
intros D ps C s C' s' X p Xs H H' H'' HX H0.
red. rewrite Forall_forall; intros r Hr.
generalize (str_proj_C _ _ _ (H _ Hr)); intro.
eq_elim p r Hpr.
+ elim (CCC_To_bproj_Call_p D C s C' s' p X Xs); auto.
  intros. induction H3 as [B [B' [HB [HB' H3] ] ] ].
  eexists; eauto.
+ elim (CCC_To_bproj_Call_r D C s C' s' p X r); auto.
  intros B [HB HB']. eexists; eauto.
Qed.

Lemma CCC_To_projectable_C : forall D ps C s C' s' t Xs,
  (forall p, In p ps -> str_proj D C p) ->
  (forall p Y, In p ps -> In Y Xs -> str_proj D (snd (D Y)) p) ->
  (forall Y, CCC_pn (snd (D Y)) (Names D) [C] fst (D Y)) ->
  (forall p X, In X Xs -> In p (fst (D X)) -> In p ps) ->
  within_Xs Xs C -> <<C,s>> --[t,D]--> <<C',s'>> -> projectable_C D C' ps.
Proof.
induction t; intros.
eapply CCC_To_projectable_C_Com; eauto.
eapply CCC_To_projectable_C_Sel; eauto.
eapply CCC_To_projectable_C_Cond; eauto.
eapply CCC_To_projectable_C_Call; eauto.
eapply CCC_To_Xs; eauto.
Qed.

Lemma CCC_To_projectable : forall P Xs ps,
  Program_WF _ Xs P -> well_ann _ P -> projectable Xs ps P ->
  (forall p, In p ps -> str_proj (Procedures _ P) (Main P) p) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In X Xs -> In p (Vars P X) -> In p ps) ->
  forall s tl P' s', (P,s) --[tl]--> (P',s') -> projectable Xs ps P'.
Proof.
intros. rename H2 into HSP, H3 into Hnames, H4 into HD, H5 into H2.
induction P as (D,C). induction P' as (D', C').
generalize (CCP_To_Defs_stable _ D D' C C' tl s s' H2); intro.
rewrite <- H3 in H2; rewrite <- H3; clear D' H3.
inversion H2. rewrite <- H4 in H2. clear s'0 H9 C'0 H8 tl H4 s0 H6 C0 H5 D0 H3.
rename H7 into Ht.
destroy H0; intros. repeat split; auto.
+ destroy H1.
  apply CCC_To_projectable_C with C s s' t Xs; auto.
  - simpl. intro r; intros.
    elim (In_dec (@eq_dec Pid) r (CCC_pn (snd (D Y)) (Names D))); intro.
    * apply initial_str_proj with (fst (D Y)); auto.
      destroy H. elim (H Y); tauto.
      red in H4; rewrite Forall_forall in H4; auto.
      apply H0; auto.
    * apply initial_str_proj'; auto.
      destroy H. elim (H Y); tauto.
  - destroy H; auto.
+ apply H1.
+ simpl. intros. elim (CCC_To_pn' _ _ _ _ _ _ _ Ht p); intros; auto.
  - destroy H4. apply HD with x.
    destroy H. apply within_Xs_char with C; auto.
    apply H0; auto.
  - unfold Names. eapply CCC_pn_mon; eauto.
    intros. inversion H4.
+ apply H1.
Qed.

(** Strong projectability of well-formed programs is also preserved by reductions:
  this is needed for chaining applications of the EPP theorem. *)

Lemma CCC_To_str_proj_Com : forall D C s C' s' ps p v q x r,
  (forall p, In p ps -> str_proj D C p) ->
  (forall p, In p (CCC_pn C (Names D)) -> In p ps) ->
  In r ps ->
  <<C,s>> --[RL_Com p v q x,D]--> <<C',s'>> -> str_proj D C' r.
Proof.
intros.
rename H into H0, H1 into Hr, H0 into Hnames, H2 into H.
revert C H0 Hnames r Hr C' H.
induction C; intros; inversion H.
+ rewrite <- H5; eauto.
+ simpl; apply IHC; auto.
  intros. apply Hnames. simpl; sup.
+ elim (H0 r); auto; intros. inversion_clear H13.
  assert (str_proj D C1' r).
    apply IHC1; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  assert (str_proj D C2' r).
    apply IHC2; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  repeat split; auto.
  destroy H9.
  simpl. case (eq_dec t r); intro.
  2: elim ((@eq_dec Pid) p r); intro Hpr.
  3: elim ((@eq_dec Pid) q r); intro Hqr.
  - apply str_proj_C in H13.
    apply str_proj_C in H16.
    induction H13 as [B1 HB1]. induction H16 as [B2 HB2].
    induction H15 as [B HB].
    rewrite e. exists (Cond Sig' t0 B1 B2); constructor; auto.
  - rewrite Hpr in H10, H11.
    elim (CCC_To_bproj_Com_p _ _ _ _ _ _ _ _ _ H12 H10); intros.
    destroy H18. rename x0 into e, x1 into a, x2 into B1. clear H18.
    elim (CCC_To_bproj_Com_p _ _ _ _ _ _ _ _ _ H14 H11); intros.
    destroy H18. rename x0 into e', x1 into a', x2 into B2. clear H18.
    induction H15 as [B HB]. inversion HB. tauto.
    rewrite (bproj_unique _ _ _ _ _ H26 H19) in H31.
    rewrite (bproj_unique _ _ _ _ _ H29 H21) in H31.
    inversion_clear H31.
    exists B7. apply bproj_Cond' with B1 B2; auto.
  - rewrite Hqr in H10, H11.
    elim (CCC_To_bproj_Com_q _ _ _ _ _ _ _ _ _ H12 H10); auto; intros.
    induction H18 as [B1 [H1' H1''] ].
    elim (CCC_To_bproj_Com_q _ _ _ _ _ _ _ _ _ H14 H11); auto; intros.
    induction H18 as [B2 [H2' H2''] ].
    induction H15 as [B HB]. inversion HB. tauto.
    rewrite (bproj_unique _ _ _ _ _ H22 H1') in H27.
    rewrite (bproj_unique _ _ _ _ _ H25 H2') in H27.
    inversion_clear H27.
    exists B7. apply bproj_Cond' with B1 B2; auto.
  - induction (CCC_To_bproj_Com_r _ _ _ _ _ _ _ _ _ _ H12 H10) as [Bt [Ht1 Ht2] ]; auto.
    induction (CCC_To_bproj_Com_r _ _ _ _ _ _ _ _ _ _ H14 H11) as [Be [He1 He2] ]; auto.
    induction H15 as [B HB]. inversion HB. tauto.
    exists B. apply bproj_Cond' with Bt Be; auto.
    rewrite (bproj_unique _ _ _ _ _ Ht1 H22).
    rewrite (bproj_unique _ _ _ _ _ He1 H25).
    auto.
+ rewrite <- H1 in *. clear t H1.
  repeat split; auto.
  apply IHC; auto. apply H0.
  intros; apply Hnames. simpl. sup.
  elim (H0 r); auto. intros. elim (H11 p0); auto.
  apply disjoint_ps_rl_In with (p:=p0) in H8; auto.
  destroy H8; intros.
  elim (CCC_To_bproj_Com_r D C s C'0 s' p q v x p0); intros; auto.
  inversion_clear H13.
  rewrite (bproj_unique _ _ _ _ _ H15 H12) in *. clear x0 H15.
  elim (H0 r); auto. intros. elim (H15 p0); auto.
  apply H0. apply Hnames. simpl. sup.
Qed.

Lemma CCC_To_str_proj_Sel : forall D C s C' s' ps p q l r,
  (forall p, In p ps -> str_proj D C p) ->
  (forall p, In p (CCC_pn C (Names D)) -> In p ps) ->
  In r ps ->
  <<C,s>> --[RL_Sel p q l,D]--> <<C',s'>> -> str_proj D C' r.
Proof.
intros.
rename H into H0, H1 into Hr, H0 into Hnames, H2 into H.
revert C H0 Hnames r Hr C' H.
induction C; intros; inversion H.
+ rewrite <- H5; eauto.
+ simpl; apply IHC; auto.
  intros. apply Hnames. simpl; sup.
+ elim (H0 r); auto; intros. inversion_clear H13.
  assert (str_proj D C1' r).
    apply IHC1; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  assert (str_proj D C2' r).
    apply IHC2; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  repeat split; auto.
  destroy H9.
  simpl. case (eq_dec t r); intro.
  2: elim ((@eq_dec Pid) p r); intro Hpr.
  3: elim ((@eq_dec Pid) q r); intro Hqr.
  - apply str_proj_C in H13.
    apply str_proj_C in H16.
    induction H13 as [B1 HB1]. induction H16 as [B2 HB2].
    induction H15 as [B HB].
    rewrite e. exists (Cond Sig' t0 B1 B2); constructor; auto.
  - rewrite Hpr in H10, H11.
    elim (CCC_To_bproj_Sel_p _ _ _ _ _ _ _ _ H12 H10); intros.
    induction H18 as [B1 [H1' H1''] ]. rename x into a.
    elim (CCC_To_bproj_Sel_p _ _ _ _ _ _ _ _ H14 H11); intros.
    induction H18 as [B2 [H2' H2''] ]. rename x into a'.
    induction H15 as [B HB]. inversion HB. tauto.
    rewrite (bproj_unique _ _ _ _ _ H22 H1') in H27.
    rewrite (bproj_unique _ _ _ _ _ H25 H2') in H27.
    inversion_clear H27.
    exists B7. apply bproj_Cond' with B1 B2; auto.
  - rewrite Hqr in H10, H11.
    induction H15 as [B HB]. inversion HB. tauto.
    induction l.
    * elim (CCC_To_bproj_Sel_ql _ _ _ _ _ _ _ H12 H10); auto; intros.
      induction H28 as [Bq1 [H1' H1''] ].
      elim (CCC_To_bproj_Sel_ql _ _ _ _ _ _ _ H14 H11); auto; intros.
      induction H28 as [Bq2 [H2' H2''] ].
      rewrite (bproj_unique _ _ _ _ _ H22 H1') in H27.
      rewrite (bproj_unique _ _ _ _ _ H25 H2') in H27.
      inversion_clear H27.
      exists bL. apply bproj_Cond' with Bq1 Bq2; auto.
    * elim (CCC_To_bproj_Sel_qr _ _ _ _ _ _ _ H12 H10); auto; intros.
      induction H28 as [Bq1 [H1' H1''] ].
      elim (CCC_To_bproj_Sel_qr _ _ _ _ _ _ _ H14 H11); auto; intros.
      induction H28 as [Bq2 [H2' H2''] ].
      rewrite (bproj_unique _ _ _ _ _ H22 H1') in H27.
      rewrite (bproj_unique _ _ _ _ _ H25 H2') in H27.
      inversion_clear H27.
      exists bR. apply bproj_Cond' with Bq1 Bq2; auto.
  - induction (CCC_To_bproj_Sel_r _ _ _ _ _ _ _ _ _ H12 H10) as [Bt [Ht1 Ht2] ]; auto.
    induction (CCC_To_bproj_Sel_r _ _ _ _ _ _ _ _ _ H14 H11) as [Be [He1 He2] ]; auto.
    induction H15 as [B HB]. inversion HB. tauto.
    exists B. apply bproj_Cond' with Bt Be; auto.
    rewrite (bproj_unique _ _ _ _ _ Ht1 H22).
    rewrite (bproj_unique _ _ _ _ _ He1 H25).
    auto.
+ rewrite <- H1 in *. clear t H1.
  repeat split; auto.
  apply IHC; auto. apply H0.
  intros; apply Hnames. simpl. sup.
  elim (H0 r); auto. intros. elim (H11 p0); auto.
  apply disjoint_ps_rl_In with (p:=p0) in H8; auto.
  destroy H8; intros.
  elim (CCC_To_bproj_Sel_r D C s C'0 s' p q l p0); intros; auto.
  inversion_clear H13.
  rewrite (bproj_unique _ _ _ _ _ H15 H12) in *. clear x H15.
  elim (H0 r); auto. intros. elim (H15 p0); auto.
  apply H0. apply Hnames. simpl. sup.
Qed.

Lemma CCC_To_str_proj_Cond : forall D C s C' s' ps p r,
  (forall p, In p ps -> str_proj D C p) ->
  (forall p, In p (CCC_pn C (Names D)) -> In p ps) ->
  In r ps ->
  <<C,s>> --[RL_Cond p,D]--> <<C',s'>> -> str_proj D C' r.
Proof.
intros.
rename H into H0, H1 into Hr, H0 into Hnames, H2 into H.
revert C H0 Hnames r Hr C' H.
induction C; intros; inversion H.
+ simpl; apply IHC; auto.
  intros. apply Hnames. simpl; sup.
+ rewrite <- H6; eapply str_proj_inv_Then; eauto.
+ rewrite <- H6; eapply str_proj_inv_Else; eauto.
+ rename p0 into q.
  rewrite <- H1, <- H2 in *.
  clear t H1 t0 H2 C0 H3 C3 H5 s0 H4 t1 H6 C' H7 H s'0 H8.
  elim (H0 r); auto; intros. inversion_clear H1.
  assert (str_proj D C1' r).
    apply IHC1; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  assert (str_proj D C2' r).
    apply IHC2; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  repeat split; auto.
  eq_elim q r Hqr. 2: eq_elim p r Hpr.
  - induction H3 as [B HB]. inversion_clear HB. 2: tauto.
    apply str_proj_C in H, H1, H2, H4.
    induction H1 as [B1' HC1']. induction H4 as [B2' HC2'].
    exists (Cond Sig' b B1' B2'); constructor; auto.
  - induction (CCC_To_bproj_Cond_p _ _ _ _ _ _ H H10) as [b1 [B1t [B1e [HC1 [HB1t HB1e] ] ] ] ].
    induction (CCC_To_bproj_Cond_p _ _ _ _ _ _ H2 H11) as [b2 [B2t [B2e [HC2 [HB2t HB2e] ] ] ] ].
    induction H3 as [B HB]. inversion HB. tauto.
    rewrite (bproj_unique _ _ _ _ _ H12 HC1) in H17.
    rewrite (bproj_unique _ _ _ _ _ H15 HC2) in H17.
    inversion H17.
    rewrite <- H22 in *; clear b2 b3 H18 H22.
    case_eq (eval_on_state BEv b1 s p); intro Hb'.
    exists Bt. apply bproj_Cond' with B1t B2t; auto.
    exists Be. apply bproj_Cond' with B1e B2e; auto.
  - induction (CCC_To_bproj_Cond_r _ _ _ _ _ _ _ H H10 Hpr) as [B1 [B1' [HB1 [HB1' H'] ] ] ].
    induction (CCC_To_bproj_Cond_r _ _ _ _ _ _ _ H2 H11 Hpr) as [B2 [B2' [HB2 [HB2' H''] ] ] ].
    induction H3 as [B HB]. revert Hqr. inversion_clear HB. tauto.
    rewrite (bproj_unique _ _ _ _ _ H3 HB1) in *; clear B0 H3.
    rewrite (bproj_unique _ _ _ _ _ H5 HB2) in *; clear B3 H5.
    induction (MB_yields_merge _ _ _ _ _ _ H' H'' H7) as [B' [HB' HB''] ].
    exists B'. apply bproj_Cond' with B1' B2'; auto.
+ rewrite <- H1 in *. clear t H1.
  repeat split; auto.
  apply IHC; auto. apply H0.
  intros; apply Hnames. simpl. sup.
  elim (H0 r); auto. intros. elim (H11 p0); auto.
  apply disjoint_ps_rl_In with (p:=p0) in H8; auto.
  destroy H8; intros.
  induction (CCC_To_bproj_Cond_r D C s C'0 s' p p0) as [B1 [B2 [HB1 [HB2 H'] ] ] ]; auto.
  rewrite (bproj_unique _ _ _ _ _ H11 HB2) in *. clear B' H11.
  apply MB_trans with B1; auto.
  elim (H0 r); auto. intros. elim (H12 p0); auto.
  apply H0. apply Hnames. simpl. sup.
Qed.

Lemma CCC_To_str_proj_Call : forall D C s C' s' ps p X r Xs,
  (forall p, In p ps -> str_proj D C p) ->
  (forall p Y, In p ps -> In Y Xs -> str_proj D (snd (D Y)) p) ->
  (forall Y, CCC_pn (snd (D Y)) (Names D) [C] fst (D Y)) ->
  (forall p, In p (CCC_pn C (Names D)) -> In p ps) ->
  In r ps -> In X Xs -> 
  <<C,s>> --[RL_Call X p,D]--> <<C',s'>> -> str_proj D C' r.
Proof.
intros.
rename H into H0, H3 into Hr, H2 into Hnames, H1 into HD, H4 into HX, H5 into H, H0 into Hsp.
revert C H0 Hnames r Hr C' H.
induction C; intros; inversion H.
+ simpl; apply IHC; auto.
  intros. apply Hnames. simpl; sup.
+ rename p0 into q.
  elim (H0 r); auto; intros. inversion_clear H13.
  assert (str_proj D C1' r).
    apply IHC1; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  assert (str_proj D C2' r).
    apply IHC2; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  repeat split; auto.
  simpl in H9.
  eq_elim t r Htr. 2: eq_elim p r Hpr.
  - apply str_proj_C in H13.
    apply str_proj_C in H16.
    induction H13 as [B1 HB1]. induction H16 as [B2 HB2].
    eexists; constructor; eauto.
  - elim (CCC_To_bproj_Call_p _ _ _ _ _ _ _ _ H12 (fun Y => Hsp _ Y Hr) HD HX H10); intros.
    induction H18 as [B1 [B1' [HB1 [HB1' H18] ] ] ].
    elim (CCC_To_bproj_Call_p _ _ _ _ _ _ _ _ H14 (fun Y => Hsp _ Y Hr) HD HX H11); intros.
    induction H20 as [B2 [B2' [HB2 [HB2' H20] ] ] ].
    rewrite (bproj_unique _ _ _ _ _ HB2 HB1) in *; clear B2 HB2.
    elim (MB_has_lub _ _ _ _ H18 H20).
    intros B' [HB' HB1''].
    eexists. apply bproj_Cond' with B1' B2'; eauto.
  - induction (H0 r) as [H01 [H02 H0'] ]; auto.
    induction (CCC_To_bproj_Call_r _ _ _ _ _ _ _ _ H01 HD H10) as [B1 [HB1 HB1'] ].
    induction (CCC_To_bproj_Call_r _ _ _ _ _ _ _ _ H02 HD H11) as [B2 [HB2 HB2'] ].
    all: auto.
    induction H0' as [B HB]. inversion HB. tauto.
    rewrite (bproj_unique _ _ _ _ _ H22 HB1) in *; clear B0 H22.
    rewrite (bproj_unique _ _ _ _ _ H25 HB2) in *; clear B3 H25.
    eexists; apply bproj_Cond' with B1 B2; eauto.
+ auto.
+ repeat split; auto.
  eapply set_remove'_1; eauto.
  generalize (Hsp p1 X); intros.
  apply str_proj_C in H11; auto.
  apply MB_refl'. eapply bproj_unique; eauto.
  apply Hnames; simpl. rewrite H2. eapply set_remove'_1; eauto.
+ repeat split.
  eapply IHC; eauto. apply H0.
  intros; apply Hnames. simpl; sup.
  elim (H0 r); auto. intros. elim (H12 p0); auto.
  elim (H0 r); auto. intros. elim (H12 p0); auto. intros.
  apply disjoint_ps_rl_In with (p:=p0) in H8; auto.
  destroy H8.
  elim (CCC_To_bproj_Call_r D C s C'0 s' p X p0); auto.
  intros B'' [HB''1 HB''2]. apply H16; auto.
  rewrite (bproj_unique _ _ _ _ _ H14 HB''2); auto.
  apply H0, Hnames. simpl. sup.
+ rewrite H4 in H0, Hnames, H, H1; clear t H4.
  elim (H0 r); auto; intros.
  split; auto; intros.
  assert (In p1 l). eapply set_remove'_1; eauto.
  elim (H12 p1); auto.
+ rewrite <- H6. apply H0; auto.
Qed.

Lemma CCC_To_str_proj : forall D ps C s C' s' t Xs,
  (forall p, In p ps -> str_proj D C p) ->
  (forall p, In p (CCC_pn C (Names D)) -> In p ps) ->
  (forall p Y, In p ps -> In Y Xs -> str_proj D (snd (D Y)) p) ->
  (forall Y, CCC_pn (snd (D Y)) (Names D) [C] fst (D Y)) ->
  (forall p X, In X Xs -> In p (fst (D X)) -> In p ps) ->
  within_Xs Xs C -> <<C,s>> --[t,D]--> <<C',s'>> ->
  forall p, In p ps -> str_proj D C' p.
Proof.
induction t; intros.
+ eapply CCC_To_str_proj_Com; eauto.
+ eapply CCC_To_str_proj_Sel; eauto.
+ eapply CCC_To_str_proj_Cond; eauto.
+ eapply CCC_To_str_proj_Call; eauto.
  eapply CCC_To_Xs; eauto.
Qed.

Lemma CCP_To_str_proj : forall P Xs ps,
  Program_WF _ Xs P -> well_ann _ P -> projectable Xs ps P ->
  (forall p, In p ps -> str_proj (Procedures _ P) (Main P) p) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In X Xs -> In p (Vars P X) -> In p ps) ->
  forall s tl P' s', (P,s) --[tl]--> (P',s') ->
  forall p, In p ps -> str_proj (Procedures _ P') (Main P') p.
Proof.
intros. rename H2 into HSP, H3 into Hnames, H4 into HD, H5 into H2.
induction P as (D,C). induction P' as (D', C').
generalize (CCP_To_Defs_stable _ D D' C C' tl s s' H2); intro.
rewrite <- H3 in H2; rewrite <- H3; clear D' H3.
inversion H2. rewrite <- H4 in H2. clear s'0 H10 C'0 H9 tl H4 s0 H7 C0 H5 D0 H3.
rename H8 into Ht.
destroy H0; intros.
rename p into r.
destroy H1.
simpl. eapply CCC_To_str_proj; eauto.
+ intros. red in H4; rewrite Forall_forall in H4.
  destroy H. elim (H Y); auto. clear H. simpl; intros; destroy H13.
  elim (In_dec (@eq_dec Pid) p (fst (D Y))); intro.
  apply initial_str_proj with (fst (D Y)); auto.
  apply initial_str_proj'; auto.
  intro. apply b, H0; auto.
+ apply Program_WF_Main_within_Xs; auto.
Qed.

(** ** Completeness
  The completeness part of the EPP theorem. *)

Lemma EPP_Complete : forall P Xs ps,
  Program_WF _ Xs P -> well_ann _ P -> forall (HP:projectable Xs ps P),
  (forall p, In p ps -> str_proj (Procedures _ P) (Main P) p) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In X Xs -> In p (Vars P X) -> In p ps) ->
  forall s tl P' s', (P,s) --[tl]--> (P',s') ->
  exists N tl', ((epp Xs ps P HP,s) --[tl']--> (N,s'))%SP
    /\ Procs N = Procs (epp Xs ps P HP)
    /\ forall H, Net N (>>) Net (epp Xs ps P' H).
Proof.
intros P Xs ps HWF Hann HP Hsp HMain HXs s tl P' s' HTo.
induction P as (D,C), P' as (D',C').
generalize (CCP_To_Defs_stable _ D D' C C' tl s s' HTo); intro.
rewrite <- H in HTo; rewrite <- H; clear D' H.
simpl in Hsp, HMain.
set (N' := epp _ _ _ HP). assert (N' = epp _ _ _ HP) as HN; auto.
clearbody N'; induction N' as (D',N).
assert (projectable_C D C ps) as HC.
1: apply str_proj_C'; auto.
induction tl; intros; inversion HTo; induction t; inversion H3.
+ rewrite H9, H8, H7 in H0.
  clear q0 v0 p0 s'0 C'0 s0 C0 D0 H9 H8 H7 H5 H4 H3 H2 H1 H.
  generalize (CCC_To_pn _ _ _ _ _ _ _ H0); intro.
  assert (In p ps) as Hp.
  1: { apply HMain, H. simpl; auto. }
  assert (In q ps) as Hq.
  1: { apply HMain, H. simpl; auto. }
  assert (p <> q) as Hpq.
  1: { eapply CCC_To_Com_neq; eauto. apply HWF. }
  clear H.
  elim (CCC_To_bproj_Com_p D C s C' s' p q v x); auto.
  intros e [a [Bp [HBp [HBp' Hv] ] ] ].
  elim (CCC_To_bproj_Com_q D C s C' s' p q v x); auto.
  intros a' [Bq [HBq HBq'] ].
  exists (D',fun r => if (eq_dec r p) then Bp else if (eq_dec r q) then Bq else N r),
  (@forget Pid Value Var PR (RL_Com p v q x)).
  repeat split; auto.
  - apply (@SPP_To_intro Sig'). rewrite Hv. apply S_Com with (a:ann Sig') Bp a' Bq.
    * replace N with (Net (D',N)); auto.
      rewrite HN. eapply bproj_unique; eauto.
      apply epp_C_char'; auto.
    * replace N with (Net (D',N)); auto.
      rewrite HN. eapply bproj_unique; eauto.
      apply epp_C_char'; auto.
    * intro r. elim eq_dec; intro H5.
      rewrite H5. symmetry; apply Network_rm_add_2_p; auto.
      elim eq_dec; intro H6. rewrite H6.
      symmetry; apply Network_rm_add_2_q; auto.
      rewrite Network_rm_add_2_out; auto.
    * apply CCC_To_Com_state with D C p C'.
      rewrite Hv in H0; auto.
  - simpl; intros H5 r.
    replace N with (Net (D',N)); auto.
    elim eq_dec; intro H6.
    2: elim eq_dec; intro H7.
    3: elim (In_dec (@eq_dec Pid) r ps); intro.
    * rewrite H6.
      apply MB_refl'.
      eapply bproj_unique; eauto.
      apply epp_C_char'; auto.
    * rewrite H7.
      apply MB_refl'.
      eapply bproj_unique; eauto.
      apply epp_C_char'; auto.
    * replace (Net (epp _ _ _ H5) r) with (N r).
      apply MB_refl.
      replace N with (Net (D',N)); auto.
      rewrite HN.
      elim (CCC_To_bproj_Com_r D C s C' s' p q v x r); auto.
      intros B [HB HB'].
      etransitivity; eapply bproj_unique.
      1,4: apply epp_C_char'; auto. all: eauto.
    * replace (Net (epp _ _ _ H5) r) with (End Sig').
      simpl. replace (N r) with (End Sig'). constructor.
      replace N with (Net (D',N)); auto.
      rewrite HN, epp_C_char with (HC:=HC), epp_C_out; auto.
      elim (CCC_To_projectable (D,C) Xs ps)
        with s (TL_Com p v q) (D,C') s'; intros; auto.
      rewrite epp_C_char with (HC:=H), epp_C_out; auto.
      eauto.
+ rewrite H9, H8, H7 in H0.
  clear q0 l0 p0 s'0 C'0 s0 C0 D0 H9 H8 H7 H5 H4 H3 H2 H1 H.
  generalize (CCC_To_pn _ _ _ _ _ _ _ H0); intro.
  assert (In p ps) as Hp.
  1: { apply HMain, H. simpl; auto. }
  assert (In q ps) as Hq.
  1: { apply HMain, H. simpl; auto. }
  assert (p <> q) as Hpq.
  1: { eapply CCC_To_Sel_neq; eauto. apply HWF. }
  clear H.
  elim (CCC_To_bproj_Sel_p D C s C' s' p q l); auto.
  intros a [Bp [HBp HBp'] ].
  induction l.
  1: elim (CCC_To_bproj_Sel_ql D C s C' s' p q); auto.
  2: elim (CCC_To_bproj_Sel_qr D C s C' s' p q); auto.
  all: intros a' [Bq [HBq1 HBq2] ].
  exists (D',fun r => if (eq_dec r p) then Bp else if (eq_dec r q) then Bq else N r),
  (@forget Pid Value Var PR (RL_Sel p q left)).
  2: exists (D',fun r => if (eq_dec r p) then Bp else if (eq_dec r q) then Bq else N r),
  (@forget Pid Value Var PR (RL_Sel p q right)).
  all: repeat split; auto.
  1,3: apply (@SPP_To_intro Sig').
  2: apply S_RSel with (a:ann Sig') Bp a' None Bq.
  1: apply S_LSel with (a:ann Sig') Bp a' Bq None.
  1,2,5,6: replace N with (Net (D',N)); auto.
  1,2,3,4: eapply bproj_unique; eauto.
  1,2,3,4: rewrite HN; apply epp_C_char'; auto.
  1,3: intro r; case eq_dec; intro H4;
    [rewrite H4; symmetry; apply Network_rm_add_2_p; auto
    | case eq_dec; intro H5;
      [ rewrite H5; auto; symmetry; apply Network_rm_add_2_q; auto
        | rewrite Network_rm_add_2_out; auto] ].
  1: apply CCC_To_Sel_state with D C p q left C'; auto.
  1: apply CCC_To_Sel_state with D C p q right C'; auto.
  1,2: simpl; intros H5 r;
    replace N with (Net (D',N)); auto;
    case eq_dec; intro H4;
    [idtac | case eq_dec; intro H6;
      [idtac | elim (In_dec (@eq_dec Pid) r ps); intro] ].
    all: try rewrite H4.
    all: try rewrite H6.
    1,2,5,6: apply MB_refl'; eapply bproj_unique; eauto.
    1,2,3,4: apply epp_C_char'; auto.
    1: induction (CCC_To_bproj_Sel_r D C s C' s' p q left r) as [B [HB HB'] ]; auto.
    3: induction (CCC_To_bproj_Sel_r D C s C' s' p q right r) as [B [HB HB'] ]; auto.
    1,3: apply MB_refl'; transitivity (N r); auto;
        replace N with (Net (D',N)); auto; rewrite HN;
        etransitivity; eapply bproj_unique.
    1,4,5,8: apply epp_C_char'; auto. 1,2,3,4: eauto.
    1,2: replace (Net (epp _ _ _ H5) r) with (End Sig').
    1,3: simpl; replace (N r) with (End Sig').
    1,3: constructor.
    1,2: replace N with (Net (D',N)); auto;
      rewrite HN, epp_C_char with (HC:=HC), epp_C_out; auto.
    1: elim (CCC_To_projectable (D,C) Xs ps)
        with s (TL_Sel p q left) (D,C') s'; intros;
       eauto; rewrite epp_C_char with (HC:=H), epp_C_out; auto.
    1: elim (CCC_To_projectable (D,C) Xs ps)
        with s (TL_Sel p q right) (D,C') s'; intros;
       eauto; rewrite epp_C_char with (HC:=H), epp_C_out; auto.
+ rewrite H7 in H0.
  clear p0 s'0 C'0 s0 C0 H7 H5 H4 H3 H2 H1 D0 H.
  generalize (CCC_To_pn _ _ _ _ _ _ _ H0); intro.
  assert (In p ps) as Hp.
  1: { apply HMain, H. simpl; auto. }
  clear H.
  elim (CCC_To_bproj_Cond_p D C s C' s' p); auto.
  intros b [Bt [Be [HB [HBt HBe] ] ] ].
  case_eq (eval_on_state BEv b s p); intro Hb.
  1: exists (D',fun r => if (eq_dec r p) then Bt else N r),
    (@forget Pid Value Var PR (RL_Cond p)).
  2: exists (D',fun r => if (eq_dec r p) then Be else N r),
    (@forget Pid Value Var PR (RL_Cond p)).
  1,2: repeat split; auto.
  1,3: apply (@SPP_To_intro Sig').
  1: apply (@S_Then Sig') with b Bt Be; auto.
  4: apply (@S_Else Sig') with b Bt Be; auto.
  1,4: replace N with (Net (D',N)); auto;
       eapply bproj_unique; eauto;
       rewrite HN; apply epp_C_char'; auto.
  1,3: intro r; case eq_dec; intro H3;
      [ rewrite H3, Par_proj2;
        [ symmetry; apply Process_refl | apply Network_rm_In]
      | symmetry; rewrite Par_proj1'; auto;
        [apply Network_rm_out; auto
        | apply Process_out; auto] ].
  1,2: apply CCC_To_Cond_state with D C p C'; auto.
  all: simpl; intros H5 r; replace N with (Net (D',N)); auto.
  all: case eq_dec; intro H3; [idtac | elim (In_dec (@eq_dec Pid) r ps); intro].
  all: try rewrite H3.
  * apply MB_refl'.
    eapply bproj_unique; eauto.
    apply epp_C_char'; auto.
  * rewrite HN. assert (p <> r) as Hpr; auto.
    elim (CCC_To_bproj_Cond_r _ _ _ _ _ _ r (Hsp _ a) H0 Hpr).
    intros B [B' [HB'' [HB' H'] ] ].
    replace (Net (epp _ _ _ HP) r) with B.
    replace (Net (epp _ _ _ H5) r) with B'; auto.
    eapply bproj_unique; eauto. apply epp_C_char'; auto.
    eapply bproj_unique; eauto. apply epp_C_char'; auto.
  * replace (Net (epp _ _ _ H5) r) with (End Sig').
    simpl. replace (N r) with (End Sig'). constructor.
    replace N with (Net (D',N)); auto.
    rewrite HN, epp_C_char with (HC:=HC), epp_C_out; auto.
    elim (CCC_To_projectable (D,C) Xs ps)
      with s (TL_Tau p) (D,C') s'; intros; auto.
    rewrite epp_C_char with (HC:=H), epp_C_out; auto.
    eauto.
  * apply MB_refl'.
    eapply bproj_unique; eauto.
    apply epp_C_char'; auto.
  * rewrite HN. assert (p <> r) as Hpr; auto.
    elim (CCC_To_bproj_Cond_r _ _ _ _ _ _ r (Hsp _ a) H0 Hpr).
    intros B [B' [HB'' [HB' H'] ] ].
    replace (Net (epp _ _ _ HP) r) with B.
    replace (Net (epp _ _ _ H5) r) with B'; auto.
    eapply bproj_unique; eauto. apply epp_C_char'; auto.
    eapply bproj_unique; eauto. apply epp_C_char'; auto.
  * replace (Net (epp _ _ _ H5) r) with (End Sig').
    simpl. replace (N r) with (End Sig'). constructor.
    replace N with (Net (D',N)); auto.
    rewrite HN, epp_C_char with (HC:=HC), epp_C_out; auto.
    elim (CCC_To_projectable (D,C) Xs ps)
      with s (TL_Tau p) (D,C') s'; intros; auto.
    rewrite epp_C_char with (HC:=H), epp_C_out; auto.
    eauto.
+ rewrite H7 in H0.
  clear p0 s'0 C'0 s0 C0 D0 H7 H5 H4 H3 H2 H1 H.
  generalize (CCC_To_pn _ _ _ _ _ _ _ H0); intro.
  assert (In p ps) as Hp.
  1: { apply HMain, H. simpl; auto. }
  clear H.
  assert (In X Xs) as HX.
  1: { eapply CCC_To_Xs; eauto. destroy HWF; auto. }
  elim (CCC_To_bproj_Call_p D C s C' s' p X Xs); auto.
  2: { intros; eapply Program_WF_D_str_proj with (P:=(D,C)); eauto. }
  intros HX' [B [B' [HB [HB' H'] ] ] ].
  inversion_clear HP. destroy H1.
  red in H2; rewrite Forall_forall in H2.
  specialize (H2 _ HX); clear H3 H4 H1.
  exists (D',fun r => if (eq_dec r p) then B else N r),
    (forget (@RL_Call Pid Value Var PR (X,p) p)).
  repeat split.
  - apply (@SPP_To_intro Sig'), (@S_Call Sig').
    * replace N with (Net (D',N)); auto.
      eapply bproj_unique; eauto.
      rewrite HN. apply epp_C_char'; auto.
    * intro r. case eq_dec; intro Hr.
      rewrite Hr, Par_proj2, Process_refl.
      replace D' with (Procs (D',N)); auto.
      rewrite HN. eapply bproj_unique; eauto.
      apply epp_D_char'; auto. apply Hann.
      apply Network_rm_In.
      symmetry; rewrite Par_proj1'; auto.
      apply Network_rm_out; auto.
      apply Process_out; auto.
    * apply CCC_To_Call_state with D C p X C'; auto.
  - simpl; intros H5 r.
    replace N with (Net (D',N)); auto.
    case eq_dec; intro Hr.
    * rewrite Hr.
      elim (CCC_To_bproj_Call_p D C s C' s' p X Xs); auto.
      intros HX'' [B1 [B2 [HB1 [HB2 HB12] ] ] ].
      rewrite (bproj_unique _ _ _ _ _ HB1 HB) in *; clear B1 HB1.
      rewrite (bproj_unique _ _ _ _ _ HB2 HB') in *; clear B2 HB2.
      erewrite bproj_unique; eauto.
      apply epp_C_char'; auto.
      intros. eapply Program_WF_D_str_proj with (P:=(D,C)); eauto.
    * elim (In_dec (@eq_dec Pid) r ps); intro Hr'.
      apply MB_refl'. transitivity (N r); auto.
      replace N with (Net (D',N)); auto.
      elim (CCC_To_bproj_Call_r D C s C' s' p X r); auto.
      intros B0 [HB0 HB0'].
      rewrite HN. etransitivity; eapply bproj_unique.
      1,4: apply epp_C_char'; auto. 1,2: eauto.
      rewrite HN.
      repeat rewrite epp_out; auto. constructor.
Qed.

Lemma EPP_Complete' : forall P Xs ps,
  Program_WF _ Xs P -> well_ann _ P -> forall (HP:projectable Xs ps P),
  initial (Main P) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In X Xs -> In p (Vars P X) -> In p ps) ->
  forall s tl P' s', (P,s) --[tl]-->* (P',s') ->
  exists N tl', ((epp Xs ps P HP,s) --[tl']-->* (N,s'))%SP
  /\ forall H, Net N (>>) Net (epp Xs ps P' H).
Proof.
intros P Xs ps HWF Hann HP Hinit HMain HXs s tl P' s' HTo.
assert (forall p, In p ps -> str_proj (Procedures _ P) (Main P) p) as Hsp.
1: { intros. apply initial_str_proj with ps; auto. apply HP. }
induction P as (D,C), P' as (D',C').
generalize (CCP_ToStar_Defs_stable _ D D' C C' tl s s' HTo); intro.
rewrite <- H in HTo; rewrite <- H; clear D' H.
simpl in Hsp, HMain. clear Hinit.
revert dependent C'. revert dependent C. revert s s'. induction tl.
+ intros. inversion HTo.
  exists (epp _ _ _ HP), nil; repeat split.
  constructor; auto.
  rewrite <- H0. intros; apply MBN_refl'.
  intro. inversion HP.
  rewrite epp_C_char with (HC:=H3). rewrite epp_C_char with (HC:=H3).
  auto.
+ intros. inversion HTo. clear HTo.
  rewrite <- H in H2; clear a H l H0 c1 H1 c3 H3.
  induction c2 as ((D',C''),s'').
  generalize (CCP_To_Defs_stable _ D D' _ _ _ _ _ H2); intro.
  rewrite <- H in H2, H4; clear D' H.
  elim EPP_Complete with (HP:=HP) (s:=s) (s':=s'') (tl:=t)
    (P':=(D,C'')); auto.
  intros. destroy H. rename x into pP, x0 into t'.
  assert (projectable Xs ps (D,C'')) as HP''.
  1: {
    inversion HP. simpl in H5; destroy H5.
    repeat split; auto.
    apply str_proj_C'.
    eapply CCP_To_str_proj; eauto.
    intros. apply HMain. change C with (Main (D,C)).
    eapply CCC_To_pn''; eauto.
    eapply CCC_pn_mon. 2: apply H9. simpl; tauto.
  }
  elim IHtl with (s:=s'') (s':=s') (C:=C'') (C':=C') (HP:=HP''); auto.
  - intros. destroy H3. rename x into pP', x0 into tl'.
    apply SPP_ToStar_MBN with (P1':=pP) in H5.
    destroy H5.
    exists x, (t'::tl'). repeat split; auto.
    apply SPT_Step with (pP,s''); auto.
    intro. apply MBN_trans with (Net pP'); auto.
    auto.
    intro. rewrite H1.
    inversion HP''. simpl in H7; clear H6; destroy H7.
    induction X. repeat rewrite epp_D_char with (HD:=H6); auto.
  - eapply CCC_To_Program_WF; eauto.
  - intros. apply HMain. change C with (Main (D,C)).
    eapply CCC_To_pn''; eauto.
  - change C'' with (Main (D,C'')).
    change D with (Procedures _ (D,C'')).
    intros. eapply CCP_To_str_proj; eauto.
Qed.

(** ** Soundness of EPP
  Soundness is proven by case analysis on the label of the reduction, and
  then by induction on the choreography. We split the proofs for each label
  in separate results, as we get some stronger statements. *)

Open Scope SP_scope.

Definition SP_eq (P P':Program Sig') : Prop :=
  forall X, Procs P X = Procs P' X /\ (Net P (==) Net P')%SP.

Lemma SP_To_bproj_Com : forall D D' ps C HC s N' s' p x q v,
  (forall p, In p ps -> str_proj D C p) ->
  (forall p, In p (CCC_pn C (Names D)) -> In p ps) ->
  <<epp_C D ps C HC,s>> --[RL_Com p v q x,D']--> <<N',s'>> ->
  exists C', (<<C,s>> --[RL_Com p v q x,D]--> <<C',s'>>)%CC
  /\ forall HC', (N' (==) (epp_C D ps C' HC')).
Proof.
intros.
rename H into Hsp, H0 into Hin, H1 into H.
revert v N' H.
induction C; intros. induction e.
+ inversion H. rewrite <- H1 in H. unfold v1; unfold v1 in H, H11.
  clear s'0 H8 N'0 H7 x0 H3 q0 H2 v v1 H1 p0 H0 s0 H5.
  rename t into a'', t0 into p', t2 into q', t1 into e0, t3 into v'.
  elim ((@eq_dec Pid) p p'); intro Hpp'.
  - clear IHC Hsp Hin.
    revert HC H H6 H9 H10 H4. rewrite <- Hpp'. clear p' Hpp'. intros.
    (* get the remaining equalities *)
    assert (In p ps /\ q = q' /\ e = e0).
    1: {
      revert H6.
      unfold epp_C. elim In_dec; simpl; intro.
      2: discriminate.
      elim bproj_dec. induction a1; simpl; intro.
      rewrite H6 in p0; inversion p0; tauto.
      (* absurd case *)
      clear H H9 H10 H4. intro; exfalso; contr_aux HC.
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
      elim bproj_dec. induction a1; simpl; intro.
      rewrite H9 in p0; inversion p0; tauto.
      (* absurd case *)
      clear H H6 H10 H4. intro. exfalso. contr_aux HC.
    }
    destroy H0.
    revert dependent HC. rewrite <- H0. clear v' H0; intros.
    rename H1 into Hqps.
    exists C; repeat split.
    1: apply (@C_Com Sig); auto.
    intros. eapply Network_eq_trans. apply H10.
    intro r.
    case ((@eq_dec Pid) p r); intro Hpr.
    2: case ((@eq_dec Pid) q r); intro Hqr.
    * rewrite <- Hpr, Network_rm_add_2_p; auto.
      rewrite epp_C_Com_p with (HC':=HC') in H6; auto.
      inversion H6; auto.
    * rewrite <- Hqr, Network_rm_add_2_q; auto.
      rewrite epp_C_Com_q with (HC':=HC') in H9; auto.
      inversion H9; auto.
    * rewrite Network_rm_add_2_out; auto.
      apply epp_C_Com_r; auto.
  - generalize (projectable_C_inv_Com D ps p' e0 q' v' a'' C HC); intro HC'.
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
    assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
    1: intros. apply Hin. simpl; sup.
    elim (IHC HC' Hsp Hin' (eval_on_state Ev e s p) ((epp_C D ps C HC' \ p \ q | p[B] | q[B'])%SP)); intros.
    rename x0 into C'. destroy H0.
    exists (p' # e0 --> q' $ v' @ a'';; C'); repeat split.
    * apply (@C_Delay_Eta Sig); repeat split; auto.
    * intros. eapply Network_eq_trans. apply H10. rewrite <- H4.
      set (H':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0).
      set (H'':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC).
      intro r. elim ((@eq_dec Pid) p r); intro Hpr.
      2: elim ((@eq_dec Pid) q r); intro Hqr.
      3: rewrite Network_rm_add_2_out, H4; auto.
      3: elim (In_dec (@eq_dec Pid) r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
      3: elim ((@eq_dec Pid) p' r); intro Hp'r.
      4: elim ((@eq_dec Pid) q' r); intro Hq'r.
      ++ rewrite <- Hpr, Network_rm_add_2_p; auto.
         rewrite epp_C_Com_r with (HC':=H'); auto.
         rewrite <- H0, Network_rm_add_2_p; auto.
      ++ rewrite <- Hqr, Network_rm_add_2_q; auto.
         rewrite epp_C_Com_r with (HC':=H'); auto.
         rewrite <- H0, Network_rm_add_2_q; auto.
      ++ rewrite <- Hp'r; intro.
         rewrite epp_C_Com_p with (HC':=H'), epp_C_Com_p with (HC':=H''); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
      ++ rewrite <- Hq'r; intro. rewrite <- Hq'r in Hp'r.
         rewrite epp_C_Com_q with (HC':=H'), epp_C_Com_q with (HC':=H''); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
      ++ rewrite epp_C_Com_r with (HC':=H'), epp_C_Com_r with (HC':=H''); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
    * apply S_Com with (a:ann Sig') B a' B'; auto.
      rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC) in H6; inversion H6; auto.
      apply epp_C_wd.
      rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC) in H9; inversion H9; auto.
      apply epp_C_wd.
      apply Network_eq_refl.
+ inversion H. rewrite <- H1 in H. unfold v1; unfold v1 in H, H11.
  clear s'0 H8 N'0 H7 x0 H3 q0 H2 v v1 H1 p0 H0 s0 H5.
  rename t into a'', t0 into p', t1 into q', t2 into l.
  generalize (projectable_C_inv_Sel _ _ _ _ _ _ _ HC); intro HC'.
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
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (eval_on_state Ev e s p) (epp_C D ps C HC' \ p \ q | p[B] | q[B']))%SP; intros.
  rename x0 into C'. destroy H0.
  exists (p' --> q'[l] @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros. eapply Network_eq_trans. apply H10. rewrite <- H4.
    set (H' := projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0).
    set (H'' := projectable_C_inv_Sel _ _ _ _ _ _ _ HC).
    intro r. elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim ((@eq_dec Pid) q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec (@eq_dec Pid) r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
    3: elim ((@eq_dec Pid) p' r); intro Hp'r.
    4: elim ((@eq_dec Pid) q' r); intro Hq'r.
    - rewrite <- Hpr, Network_rm_add_2_p; auto.
      rewrite epp_C_Sel_r with (HC':=H'); auto.
      rewrite <- H0, Network_rm_add_2_p; auto.
    - rewrite <- Hqr, Network_rm_add_2_q; auto.
      rewrite epp_C_Sel_r with (HC':=H'); auto.
      rewrite <- H0, Network_rm_add_2_q; auto.
    - rewrite <- Hp'r; intro.
      rewrite epp_C_Sel_p with (HC':=H'), epp_C_Sel_p with (HC':=H''); auto.
      rewrite <- H0; auto.
      rewrite Network_rm_add_2_out; auto.
      rewrite epp_C_wd with (H':=HC'); auto.
    - rewrite <- Hq'r; intro. rewrite <- Hq'r in Hp'r.
      induction l.
      1: rewrite epp_C_Sel_ql with (HC':=H'), epp_C_Sel_ql with (HC':=H''); auto.
      2: rewrite epp_C_Sel_qr with (HC':=H'), epp_C_Sel_qr with (HC':=H''); auto.
      all: rewrite <- H0, Network_rm_add_2_out; auto.
      all: rewrite epp_C_wd with (H':=HC'); auto.
    - rewrite epp_C_Sel_r with (HC':=H'), epp_C_Sel_r with (HC':=H''); auto.
      rewrite <- H0; auto.
      rewrite Network_rm_add_2_out; auto.
      rewrite epp_C_wd with (H':=HC'); auto.
  * apply S_Com with (a:ann Sig') B a' B'; auto.
    rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC) in H6; inversion H6; auto.
    apply epp_C_wd.
    rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC) in H9; inversion H9; auto.
    apply epp_C_wd.
    apply Network_eq_refl.
+ inversion H. rewrite <- H1 in H. unfold v1; unfold v1 in H, H11.
  clear s'0 H8 N'0 H7 x0 H3 q0 H2 v v1 H1 p0 H0 s0 H5.
  rename t into p', t0 into b.
  generalize (projectable_C_inv_Then _ _ _ _ _ _ HC); intro HC1.
  generalize (projectable_C_inv_Else _ _ _ _ _ _ HC); intro HC2.
  assert (forall p, In p ps -> str_proj D C1 p) as Hsp1.
  1: apply Hsp.
  assert (forall p, In p ps -> str_proj D C2 p) as Hsp2.
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
  elim (epp_C_Cond_Send_inv _ _ _ _ _ _ HC HC1 HC2 _ _ _ _ _ H6).
  intros. destroy H0. rename x0 into Bp1, x1 into Bp2, H1 into Hp1, H2 into Hp2, H0 into Hp'.
  elim (epp_C_Cond_Recv_inv _ _ _ _ _ _ HC HC1 HC2 _ _ _ _ _ H9).
  intros. destroy H0. rename x0 into Bq1, x1 into Bq2, H1 into Hq1, H2 into Hq2, H0 into Hq'.
  assert (forall p, In p (CCC_pn C1 (Names D)) -> In p ps) as Hin1.
  1: intros. apply Hin. simpl; sup; sup.
  assert (forall p, In p (CCC_pn C2 (Names D)) -> In p ps) as Hin2.
  1: intros. apply Hin. simpl; sup; sup.
  elim (IHC1 HC1 Hsp1 Hin1 (eval_on_state Ev e s p) (epp_C D ps C1 HC1 \ p \ q | p[Bp1] | q[Bq1]))%SP; intros.
  rename x0 into C1'. destroy H0.
  elim (IHC2 HC2 Hsp2 Hin2 (eval_on_state Ev e s p) (Network_rm _ (Network_rm _ (epp_C D ps C2 HC2) p) q | p[Bp2] | q[Bq2]))%SP; intros.
  rename x0 into C2'. destroy H2. clear IHC1 IHC2.
  exists (If p' ?? b Then C1' Else C2'); repeat split.
  * apply C_Delay_Cond; repeat split; auto.
  * intros. eapply Network_eq_trans. apply H10. rewrite <- H4.
    intro r. elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim ((@eq_dec Pid) q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec (@eq_dec Pid) r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
    3: elim ((@eq_dec Pid) p' r); intro Hp'r.
    - rewrite <- Hpr in *; clear r Hpr.
      rewrite Network_rm_add_2_p; auto.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                   (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      intros. specialize (H5 _ _ HC' _ Hp'p).
      rewrite <- H0, <- H2, Network_rm_add_2_p, Network_rm_add_2_p in H5; auto.
      eapply merge_unique; eauto.
    - rewrite <- Hqr in *; clear r Hqr.
      rewrite Network_rm_add_2_q; auto.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                   (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      intros. specialize (H5 _ _ HC' _ Hp'q).
      rewrite <- H0, <- H2, Network_rm_add_2_q, Network_rm_add_2_q in H5; auto.
      eapply merge_unique; eauto.
    - rewrite <- Hp'r in *; clear r Hp'r; intros.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H2, Network_rm_add_2_out, Network_rm_add_2_out; auto.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC)
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC); auto.
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2); auto.
    - intro.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                   (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      intros. specialize (H5 _ _ HC' _ Hp'r).
      rewrite <- H0, <- H2, Network_rm_add_2_out, Network_rm_add_2_out in H5; auto.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC)
                                   (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC); auto.
      intros. specialize (H7 _ _ HC _ Hp'r).
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2) in H7; auto.
      eapply merge_unique; eauto.
  * apply S_Com with (a:ann Sig') Bp2 a' Bq2; auto.
    apply Network_eq_refl.
  * apply S_Com with (a:ann Sig') Bp1 a' Bq1; auto.
    apply Network_eq_refl.
+ exfalso.
  inversion H.
  elim (In_dec (@eq_dec Pid) p ps); intros.
  elim (In_dec (@eq_dec Pid) p (fst (D t))); intros.
  rewrite epp_C_Call in H6; auto. inversion H6.
  rewrite epp_C_Call_out in H6; auto. inversion H6.
  rewrite epp_C_out in H6; auto. inversion H6.
+ inversion H. rewrite <- H1 in H. unfold v1; unfold v1 in H, H11.
  clear s'0 H8 N'0 H7 x0 H3 q0 H2 v v1 H1 p0 H0 s0 H5.
  rename l into ps', t into X.
  assert (projectable_C D C ps) as HC'.
  1: { red. rewrite Forall_forall. intros.
    elim (Hsp x0); auto; intros.
    apply str_proj_C; auto.
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
  assert (forall p, In p ps -> str_proj D C p) as Hsp'.
  1: apply Hsp.
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp' Hin' (eval_on_state Ev e s p) (Network_rm _ (Network_rm _ (epp_C D ps C HC') p) q | p[B] | q[B']))%SP; intros.
  rename x0 into C'. destroy H0.
  exists (RT_Call X ps' C'); repeat split.
  * apply C_Delay_Call; repeat split; auto.
    apply disjoint_ps_char. simpl.
    intros r Hr. split; intro H'; rewrite H' in Hr; auto.
  * intros. eapply Network_eq_trans. apply H10. rewrite <- H4.
    assert (projectable_C D C' ps).
    1: apply str_proj_C'; intros. eapply CCC_To_str_proj_Com; eauto.
    intro r. elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim ((@eq_dec Pid) q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec (@eq_dec Pid) r ps); intro Hr1.
    3: elim (In_dec (@eq_dec Pid) r ps'); intro Hr2.
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
  * apply S_Com with (a:ann Sig') B a' B'; auto.
    rewrite epp_C_RT_Call_out with (HC':=HC') in H6; inversion H6; auto.
    rewrite epp_C_RT_Call_out with (HC':=HC') in H9; inversion H9; auto.
    apply Network_eq_refl.
+ exfalso.
  inversion H.
  rewrite epp_C_End in H6. inversion H6.
Qed.

Lemma SP_To_bproj_Sel_l : forall D D' ps C HC s N' s' p q,
  (forall p, In p ps -> str_proj D C p) ->
  (forall p, In p (CCC_pn C (Names D)) -> In p ps) ->
  <<epp_C D ps C HC,s>> --[RL_Sel p q left,D']--> <<N',s'>> ->
  exists C', (<<C,s>> --[RL_Sel p q left,D]--> <<C',s'>>)%CC
  /\ forall HC', (N' (==) (epp_C D ps C' HC')).
Proof.
intros.
rename H into Hsp, H0 into Hin, H1 into H.
revert N' H.
induction C; intros. induction e.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  rename t into a'', t0 into p', t2 into q', t1 into e, t3 into v'.
  generalize (projectable_C_inv_Com D ps p' e q' v' a'' C HC); intro HC'.
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
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (Network_rm _ (Network_rm _ (epp_C D ps C HC') p) q | p[B] | q[Bl])); intros.
  rename x into C'. destroy H0.
  exists (p' # e --> q' $ v' @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros. eapply Network_eq_trans. apply H6. rewrite <- H4.
    intro r. elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim ((@eq_dec Pid) q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec (@eq_dec Pid) r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
    3: elim ((@eq_dec Pid) p' r); intro Hp'r.
    4: elim ((@eq_dec Pid) q' r); intro Hq'r.
    ++ rewrite <- Hpr, Network_rm_add_2_p; auto.
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite <- H0, Network_rm_add_2_p; auto.
    ++ rewrite <- Hqr, Network_rm_add_2_q; auto.
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite <- H0, Network_rm_add_2_q; auto.
    ++ rewrite <- Hp'r; intro.
       rewrite epp_C_Com_p with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_p with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
    ++ rewrite <- Hq'r; intro. rewrite <- Hq'r in Hp'r.
       rewrite epp_C_Com_q with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_q with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
    ++ rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
  * apply S_LSel with (a:ann Sig') B a' Bl Br; auto.
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC) in H2; inversion H2; auto.
    apply epp_C_wd.
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC) in H3; auto.
    etransitivity. 2: apply H3.
    apply epp_C_wd.
    apply Network_eq_refl.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  rename t into a'', t0 into p', t1 into q', t2 into l.
  elim ((@eq_dec Pid) p p'); intro Hpp'.
  - clear IHC Hsp Hin.
    revert HC H H2 H3 H6 H4. rewrite <- Hpp'. clear p' Hpp'. intros.
    (* get the remaining equalities *)
    assert (In p ps /\ q = q' /\ l = left).
    1: {
      revert H2.
      unfold epp_C. elim In_dec; simpl; intro.
      2: discriminate.
      elim bproj_dec. induction a1; simpl; intro.
      rewrite H2 in p0; inversion p0; tauto.
      (* absurd case *)
      clear H H3 H6 H4. intro; exfalso; contr_aux HC.
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
    1: apply (@C_Sel Sig); auto.
    intros. eapply Network_eq_trans; eauto.
    intro r.
    case ((@eq_dec Pid) p r); intro Hpr.
    2: case ((@eq_dec Pid) q r); intro Hqr.
    * rewrite <- Hpr, Network_rm_add_2_p; auto.
      rewrite epp_C_Sel_p with (HC':=HC') in H2; auto.
      inversion H2; auto.
    * rewrite <- Hqr, Network_rm_add_2_q; auto.
      rewrite epp_C_Sel_ql with (HC':=HC') in H3; auto.
      inversion H3; auto.
    * rewrite Network_rm_add_2_out; auto.
      apply epp_C_Sel_r; auto.
  - generalize (projectable_C_inv_Sel _ _ _ _ _ _ _ HC); intro HC'.
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
    assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
    1: intros. apply Hin. simpl; sup.
    elim (IHC HC' Hsp Hin' (Network_rm _ (Network_rm _ (epp_C D ps C HC') p) q | p[B] | q[Bl])); intros.
    rename x into C'. destroy H0.
    exists (p' --> q'[l] @ a'';; C'); repeat split.
    * apply C_Delay_Eta; repeat split; auto.
    * intros. eapply Network_eq_trans. apply H6. rewrite <- H4.
      intro r. elim ((@eq_dec Pid) p r); intro Hpr.
      2: elim ((@eq_dec Pid) q r); intro Hqr.
      3: rewrite Network_rm_add_2_out, H4; auto.
      3: elim (In_dec (@eq_dec Pid) r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
      3: elim ((@eq_dec Pid) p' r); intro Hp'r.
      4: elim ((@eq_dec Pid) q' r); intro Hq'r.
      ++ rewrite <- Hpr, Network_rm_add_2_p; auto.
         rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
         rewrite <- H0, Network_rm_add_2_p; auto.
      ++ rewrite <- Hqr, Network_rm_add_2_q; auto.
        rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
        rewrite <- H0, Network_rm_add_2_q; auto.
      ++ rewrite <- Hp'r; intro.
         rewrite epp_C_Sel_p with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
         rewrite epp_C_Sel_p with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
      ++ rewrite <- Hq'r; intro. rewrite <- Hq'r in Hp'r.
          induction l.
         1: rewrite epp_C_Sel_ql with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
         1: rewrite epp_C_Sel_ql with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC); auto.
         2: rewrite epp_C_Sel_qr with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
         2: rewrite epp_C_Sel_qr with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC); auto.
         all: rewrite <- H0, Network_rm_add_2_out; auto.
         all: rewrite epp_C_wd with (H':=HC'); auto.
      ++ rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
         rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
    * apply S_LSel with (a:ann Sig') B a' Bl Br; auto.
      rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC) in H2; inversion H2; auto.
      apply epp_C_wd.
      rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC) in H3; auto.
      etransitivity. 2: apply H3.
      apply epp_C_wd.
      apply Network_eq_refl.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  elim (epp_C_Sel_Branching_l _ _ _ _ _ _ _ _ _ _ H2 H3); intros.
  rewrite H1 in H3; clear Br H1 H0.
  rename t into p', t0 into b.
  generalize (projectable_C_inv_Then _ _ _ _ _ _ HC); intro HC1.
  generalize (projectable_C_inv_Else _ _ _ _ _ _ HC); intro HC2.
  assert (forall p, In p ps -> str_proj D C1 p) as Hsp1.
  1: apply Hsp.
  assert (forall p, In p ps -> str_proj D C2 p) as Hsp2.
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
  elim (epp_C_Cond_Sel_inv _ _ _ _ _ _ HC HC1 HC2 _ _ _ _ _ H2).
  intros. destroy H0. rename x into Bp1, x0 into Bp2, H1 into Hp1, H5 into Hp2, H0 into Hp'.
  elim (epp_C_Cond_Branching_l_inv _ _ _ _ _ _ HC HC1 HC2 _ _ _ _ H3).
  intros. destroy H0. rename x into Bq1, x0 into Bq2, H1 into Hq1, H5 into Hq2, H0 into Hq'.
  assert (forall p, In p (CCC_pn C1 (Names D)) -> In p ps) as Hin1.
  1: intros. apply Hin. simpl; sup; sup.
  assert (forall p, In p (CCC_pn C2 (Names D)) -> In p ps) as Hin2.
  1: intros. apply Hin. simpl; sup; sup.
  elim (IHC1 HC1 Hsp1 Hin1 (epp_C D ps C1 HC1 \ p \ q | p[Bp1] | q[Bq1])); intros.
  rename x into C1'. destroy H0.
  elim (IHC2 HC2 Hsp2 Hin2 (Network_rm _ (Network_rm _ (epp_C D ps C2 HC2) p) q | p[Bp2] | q[Bq2])); intros.
  rename x into C2'. destroy H5. clear IHC1 IHC2.
  exists (If p' ?? b Then C1' Else C2'); repeat split.
  * apply C_Delay_Cond; repeat split; auto.
  * intros. eapply Network_eq_trans. apply H6. rewrite <- H4.
    intro r. elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim ((@eq_dec Pid) q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec (@eq_dec Pid) r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
    3: elim ((@eq_dec Pid) p' r); intro Hp'r.
    - rewrite <- Hpr in *; clear r Hpr.
      rewrite Network_rm_add_2_p; auto.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                   (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      intros. specialize (H8 _ _ HC' _ Hp'p).
      rewrite <- H0, <- H5, Network_rm_add_2_p, Network_rm_add_2_p in H8; auto.
      eapply merge_unique; eauto.
    - rewrite <- Hqr in *; clear r Hqr.
      rewrite Network_rm_add_2_q; auto.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                   (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      intros. specialize (H8 _ _ HC' _ Hp'q).
      rewrite <- H0, <- H5, Network_rm_add_2_q, Network_rm_add_2_q in H8; auto.
      eapply merge_unique; eauto.
    - rewrite <- Hp'r in *; clear r Hp'r; intros.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H5, Network_rm_add_2_out, Network_rm_add_2_out; auto.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC)
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC); auto.
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2); auto.
    - intro.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                   (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      intros. specialize (H8 _ _ HC' _ Hp'r).
      rewrite <- H0, <- H5, Network_rm_add_2_out, Network_rm_add_2_out in H8; auto.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC)
                                   (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC); auto.
      intros. specialize (H10 _ _ HC _ Hp'r).
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2) in H10; auto.
      eapply merge_unique; eauto.
  * apply S_LSel with (a:ann Sig') Bp2 a' Bq2 None; auto.
    apply Network_eq_refl.
  * apply S_LSel with (a:ann Sig') Bp1 a' Bq1 None; auto.
    apply Network_eq_refl.
+ exfalso.
  inversion H.
  elim (In_dec (@eq_dec Pid) p ps); intros.
  elim (In_dec (@eq_dec Pid) p (fst (D t))); intros.
  rewrite epp_C_Call in H2; auto. inversion H2.
  rewrite epp_C_Call_out in H2; auto. inversion H2.
  rewrite epp_C_out in H2; auto. inversion H2.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  rename l into ps', t into X.
  assert (projectable_C D C ps) as HC'.
  1: { red. rewrite Forall_forall. intros.
    elim (Hsp x); auto; intros.
    apply str_proj_C; auto.
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
  assert (forall p, In p ps -> str_proj D C p) as Hsp'.
  1: apply Hsp.
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp' Hin' (Network_rm _ (Network_rm _ (epp_C D ps C HC') p) q | p[B] | q[Bl])); intros.
  rename x into C'. destroy H0.
  exists (RT_Call X ps' C'); repeat split.
  * apply C_Delay_Call; repeat split; auto.
    apply disjoint_ps_char. simpl.
    intros r Hr. split; intro H'; rewrite H' in Hr; auto.
  * intros. eapply Network_eq_trans. apply H6. rewrite <- H4.
    assert (projectable_C D C' ps).
    1: apply str_proj_C'; intros. eapply CCC_To_str_proj_Sel; eauto.
    intro r. elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim ((@eq_dec Pid) q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec (@eq_dec Pid) r ps); intro Hr1.
    3: elim (In_dec (@eq_dec Pid) r ps'); intro Hr2.
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
  * apply S_LSel with (a:ann Sig') B a' Bl Br; auto.
    rewrite epp_C_RT_Call_out with (HC':=HC') in H2; inversion H2; auto.
    rewrite epp_C_RT_Call_out with (HC':=HC') in H3; inversion H3; auto.
    apply Network_eq_refl.
+ exfalso.
  inversion H.
  rewrite epp_C_End in H2. inversion H2.
Qed.

Lemma SP_To_bproj_Sel_r : forall D D' ps C HC s N' s' p q,
  (forall p, In p ps -> str_proj D C p) ->
  (forall p, In p (CCC_pn C (Names D)) -> In p ps) ->
  <<epp_C D ps C HC,s>> --[RL_Sel p q right,D']--> <<N',s'>> ->
  exists C', (<<C,s>> --[RL_Sel p q right,D]--> <<C',s'>>)%CC
  /\ forall HC', (N' (==) (epp_C D ps C' HC')).
Proof.
intros.
rename H into Hsp, H0 into Hin, H1 into H.
revert N' H.
induction C; intros. induction e.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  rename t into a'', t0 into p', t2 into q', t1 into e, t3 into v'.
  generalize (projectable_C_inv_Com D ps p' e q' v' a'' C HC); intro HC'.
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
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (Network_rm _ (Network_rm _ (epp_C D ps C HC') p) q | p[B] | q[Br])); intros.
  rename x into C'. destroy H0.
  exists (p' # e --> q' $ v' @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros. eapply Network_eq_trans. apply H6. rewrite <- H4.
    intro r. elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim ((@eq_dec Pid) q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec (@eq_dec Pid) r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
    3: elim ((@eq_dec Pid) p' r); intro Hp'r.
    4: elim ((@eq_dec Pid) q' r); intro Hq'r.
    ++ rewrite <- Hpr, Network_rm_add_2_p; auto.
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite <- H0, Network_rm_add_2_p; auto.
    ++ rewrite <- Hqr, Network_rm_add_2_q; auto.
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite <- H0, Network_rm_add_2_q; auto.
    ++ rewrite <- Hp'r; intro.
       rewrite epp_C_Com_p with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_p with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
    ++ rewrite <- Hq'r; intro. rewrite <- Hq'r in Hp'r.
       rewrite epp_C_Com_q with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_q with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
    ++ rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
  * apply S_RSel with (a:ann Sig') B a' Bl Br; auto.
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC) in H2; inversion H2; auto.
    apply epp_C_wd.
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC) in H3; auto.
    etransitivity. 2: apply H3.
    apply epp_C_wd.
    apply Network_eq_refl.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  rename t into a'', t0 into p', t1 into q', t2 into l.
  elim ((@eq_dec Pid) p p'); intro Hpp'.
  - clear IHC Hsp Hin.
    revert HC H H2 H3 H6 H4. rewrite <- Hpp'. clear p' Hpp'. intros.
    (* get the remaining equalities *)
    assert (In p ps /\ q = q' /\ l = right).
    1: {
      revert H2.
      unfold epp_C. elim In_dec; simpl; intro.
      2: discriminate.
      elim bproj_dec. induction a1; simpl; intro.
      rewrite H2 in p0; inversion p0; tauto.
      (* absurd case *)
      clear H H3 H6 H4. intro; exfalso; contr_aux HC.
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
    1: apply (@C_Sel Sig); auto.
    intros. eapply Network_eq_trans; eauto.
    intro r.
    case ((@eq_dec Pid) p r); intro Hpr.
    2: case ((@eq_dec Pid) q r); intro Hqr.
    * rewrite <- Hpr, Network_rm_add_2_p; auto.
      rewrite epp_C_Sel_p with (HC':=HC') in H2; auto.
      inversion H2; auto.
    * rewrite <- Hqr, Network_rm_add_2_q; auto.
      rewrite epp_C_Sel_qr with (HC':=HC') in H3; auto.
      inversion H3; auto.
    * rewrite Network_rm_add_2_out; auto.
      apply epp_C_Sel_r; auto.
  - generalize (projectable_C_inv_Sel _ _ _ _ _ _ _ HC); intro HC'.
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
    assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
    1: intros. apply Hin. simpl; sup.
    elim (IHC HC' Hsp Hin' (Network_rm _ (Network_rm _ (epp_C D ps C HC') p) q | p[B] | q[Br])); intros.
    rename x into C'. destroy H0.
    exists (p' --> q'[l] @ a'';; C'); repeat split.
    * apply C_Delay_Eta; repeat split; auto.
    * intros. eapply Network_eq_trans. apply H6. rewrite <- H4.
      intro r. elim ((@eq_dec Pid) p r); intro Hpr.
      2: elim ((@eq_dec Pid) q r); intro Hqr.
      3: rewrite Network_rm_add_2_out, H4; auto.
      3: elim (In_dec (@eq_dec Pid) r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
      3: elim ((@eq_dec Pid) p' r); intro Hp'r.
      4: elim ((@eq_dec Pid) q' r); intro Hq'r.
      ++ rewrite <- Hpr, Network_rm_add_2_p; auto.
         rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
         rewrite <- H0, Network_rm_add_2_p; auto.
      ++ rewrite <- Hqr, Network_rm_add_2_q; auto.
        rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
        rewrite <- H0, Network_rm_add_2_q; auto.
      ++ rewrite <- Hp'r; intro.
         rewrite epp_C_Sel_p with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
         rewrite epp_C_Sel_p with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
      ++ rewrite <- Hq'r; intro. rewrite <- Hq'r in Hp'r.
          induction l.
         1: rewrite epp_C_Sel_ql with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
         1: rewrite epp_C_Sel_ql with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC); auto.
         2: rewrite epp_C_Sel_qr with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
         2: rewrite epp_C_Sel_qr with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC); auto.
         all: rewrite <- H0, Network_rm_add_2_out; auto.
         all: rewrite epp_C_wd with (H':=HC'); auto.
      ++ rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
         rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
    * apply S_RSel with (a:ann Sig') B a' Bl Br; auto.
      rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC) in H2; inversion H2; auto.
      apply epp_C_wd.
      rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC) in H3; auto.
      etransitivity. 2: apply H3.
      apply epp_C_wd.
      apply Network_eq_refl.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  elim (epp_C_Sel_Branching_r _ _ _ _ _ _ _ _ _ _ H2 H3); intros.
  rewrite H0 in H3; clear Bl H1 H0.
  rename t into p', t0 into b.
  generalize (projectable_C_inv_Then _ _ _ _ _ _ HC); intro HC1.
  generalize (projectable_C_inv_Else _ _ _ _ _ _ HC); intro HC2.
  assert (forall p, In p ps -> str_proj D C1 p) as Hsp1.
  1: apply Hsp.
  assert (forall p, In p ps -> str_proj D C2 p) as Hsp2.
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
  elim (epp_C_Cond_Sel_inv _ _ _ _ _ _ HC HC1 HC2 _ _ _ _ _ H2).
  intros. destroy H0. rename x into Bp1, x0 into Bp2, H1 into Hp1, H5 into Hp2, H0 into Hp'.
  elim (epp_C_Cond_Branching_r_inv _ _ _ _ _ _ HC HC1 HC2 _ _ _ _ H3).
  intros. destroy H0. rename x into Bq1, x0 into Bq2, H1 into Hq1, H5 into Hq2, H0 into Hq'.
  assert (forall p, In p (CCC_pn C1 (Names D)) -> In p ps) as Hin1.
  1: intros. apply Hin. simpl; sup; sup.
  assert (forall p, In p (CCC_pn C2 (Names D)) -> In p ps) as Hin2.
  1: intros. apply Hin. simpl; sup; sup.
  elim (IHC1 HC1 Hsp1 Hin1 (epp_C D ps C1 HC1 \ p \ q | p[Bp1] | q[Bq1])); intros.
  rename x into C1'. destroy H0.
  elim (IHC2 HC2 Hsp2 Hin2 (Network_rm _ (Network_rm _ (epp_C D ps C2 HC2) p) q | p[Bp2] | q[Bq2])); intros.
  rename x into C2'. destroy H5. clear IHC1 IHC2.
  exists (If p' ?? b Then C1' Else C2'); repeat split.
  * apply C_Delay_Cond; repeat split; auto.
  * intros. eapply Network_eq_trans. apply H6. rewrite <- H4.
    intro r. elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim ((@eq_dec Pid) q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec (@eq_dec Pid) r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
    3: elim ((@eq_dec Pid) p' r); intro Hp'r.
    - rewrite <- Hpr in *; clear r Hpr.
      rewrite Network_rm_add_2_p; auto.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                   (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      intros. specialize (H8 _ _ HC' _ Hp'p).
      rewrite <- H0, <- H5, Network_rm_add_2_p, Network_rm_add_2_p in H8; auto.
      eapply merge_unique; eauto.
    - rewrite <- Hqr in *; clear r Hqr.
      rewrite Network_rm_add_2_q; auto.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                   (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      intros. specialize (H8 _ _ HC' _ Hp'q).
      rewrite <- H0, <- H5, Network_rm_add_2_q, Network_rm_add_2_q in H8; auto.
      eapply merge_unique; eauto.
    - rewrite <- Hp'r in *; clear r Hp'r; intros.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H5, Network_rm_add_2_out, Network_rm_add_2_out; auto.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC)
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC); auto.
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2); auto.
    - intro.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                   (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      intros. specialize (H8 _ _ HC' _ Hp'r).
      rewrite <- H0, <- H5, Network_rm_add_2_out, Network_rm_add_2_out in H8; auto.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC)
                                   (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC); auto.
      intros. specialize (H10 _ _ HC _ Hp'r).
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2) in H10; auto.
      eapply merge_unique; eauto.
  * apply S_RSel with (a:ann Sig') Bp2 a' None Bq2; auto.
    apply Network_eq_refl.
  * apply S_RSel with (a:ann Sig') Bp1 a' None Bq1; auto.
    apply Network_eq_refl.
+ exfalso.
  inversion H.
  elim (In_dec (@eq_dec Pid) p ps); intros.
  elim (In_dec (@eq_dec Pid) p (fst (D t))); intros.
  rewrite epp_C_Call in H2; auto. inversion H2.
  rewrite epp_C_Call_out in H2; auto. inversion H2.
  rewrite epp_C_out in H2; auto. inversion H2.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  rename l into ps', t into X.
  assert (projectable_C D C ps) as HC'.
  1: { red. rewrite Forall_forall. intros.
    elim (Hsp x); auto; intros.
    apply str_proj_C; auto.
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
  assert (forall p, In p ps -> str_proj D C p) as Hsp'.
  1: apply Hsp.
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp' Hin' (Network_rm _ (Network_rm _ (epp_C D ps C HC') p) q | p[B] | q[Br])); intros.
  rename x into C'. destroy H0.
  exists (RT_Call X ps' C'); repeat split.
  * apply C_Delay_Call; repeat split; auto.
    apply disjoint_ps_char. simpl.
    intros r Hr. split; intro H'; rewrite H' in Hr; auto.
  * intros. eapply Network_eq_trans. apply H6. rewrite <- H4.
    assert (projectable_C D C' ps).
    1: apply str_proj_C'; intros. eapply CCC_To_str_proj_Sel; eauto.
    intro r. elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim ((@eq_dec Pid) q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec (@eq_dec Pid) r ps); intro Hr1.
    3: elim (In_dec (@eq_dec Pid) r ps'); intro Hr2.
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
  * apply S_RSel with (a:ann Sig') B a' Bl Br; auto.
    rewrite epp_C_RT_Call_out with (HC':=HC') in H2; inversion H2; auto.
    rewrite epp_C_RT_Call_out with (HC':=HC') in H3; inversion H3; auto.
    apply Network_eq_refl.
+ exfalso.
  inversion H.
  rewrite epp_C_End in H2. inversion H2.
Qed.

Lemma SP_To_bproj_Cond : forall D D' ps C HC s N' s' p,
  (forall p, In p ps -> str_proj D C p) ->
  (forall p, In p (CCC_pn C (Names D)) -> In p ps) ->
  <<epp_C D ps C HC,s>> --[RL_Cond p,D']--> <<N',s'>> ->
  exists C', (<<C,s>> --[RL_Cond p,D]--> <<C',s'>>)%CC
  /\ forall HC', (N' (>>) (epp_C D ps C' HC')).
Proof.
intros.
rename H into Hsp, H0 into Hin, H1 into H.
revert N' H.
induction C; intros. induction e. 1,2,3,5: inversion H. (* double cases *)
+ clear s'0 H8 N'0 H7 p0 H0 s0 H5 H.
  rename t into a'', t0 into p', t2 into q', t3 into v', t1 into e.
  generalize (projectable_C_inv_Com D ps p' e q' v' a'' C HC); intro HC'.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H1. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H, epp_C_Com_p with (HC':=HC') in H1; auto.
    inversion H1. rewrite H; auto.
  assert (q' <> p) as Hq'p.
  1: intro. rewrite <- H, epp_C_Com_q with (HC':=HC') in H1.
    inversion H1. 1,2: rewrite H; auto.
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (Network_rm _ (epp_C D ps C HC') p | p[B1])) ; intros.
  rename x into C'. destroy H.
  exists (p' # e --> q' $ v' @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros; intro r. rewrite H3.
    set (H':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0). clearbody H'.
    generalize (H H' r); clear H; intro.
    elim ((@eq_dec Pid) r p); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
    2: elim ((@eq_dec Pid) p' r); intro Hp'r.
    3: elim ((@eq_dec Pid) q' r); intro Hq'r.
    - rewrite Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite Hpr, Par_proj2 in H. 2: apply Network_rm_In.
      rewrite epp_C_Com_r with (HC':=H'); auto.
    - rewrite <- Hp'r, Par_proj1', Network_rm_out; auto.
      rewrite <- Hp'r, Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_Com_p with (HC':=H'), epp_C_Com_p with (HC':=HC'); auto.
      constructor; auto. all: rewrite Hp'r; auto.
      all: apply Process_out; auto.
    - rewrite <- Hq'r, Par_proj1', Network_rm_out; auto.
      rewrite <- Hq'r, Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_Com_q with (HC':=H'), epp_C_Com_q with (HC':=HC'); auto.
      constructor; auto. all: rewrite Hq'r; auto.
      all: apply Process_out; auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_Com_r with (HC':=H'), epp_C_Com_r with (HC':=HC'); auto.
      all: apply Process_out; auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_out, epp_C_out; auto. constructor.
      all: apply Process_out; auto.
  * apply (@S_Then Sig') with b B1 B2; auto.
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC) in H1; inversion H1; auto.
    apply epp_C_wd.
    apply Network_eq_refl.
+ clear s'0 H8 N'0 H7 p0 H0 s0 H5 H.
  rename t into a'', t0 into p', t2 into q', t3 into v', t1 into e.
  generalize (projectable_C_inv_Com D ps p' e q' v' a'' C HC); intro HC'.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H1. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H, epp_C_Com_p with (HC':=HC') in H1; auto.
    inversion H1. rewrite H; auto.
  assert (q' <> p) as Hq'p.
  1: intro. rewrite <- H, epp_C_Com_q with (HC':=HC') in H1.
    inversion H1. 1,2: rewrite H; auto.
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (Network_rm _ (epp_C D ps C HC') p | p[B2])); intros.
  rename x into C'. destroy H.
  exists (p' # e --> q' $ v' @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros; intro r. rewrite H3.
    set (H':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0). clearbody H'.
    generalize (H H' r); clear H; intro.
    elim ((@eq_dec Pid) r p); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
    2: elim ((@eq_dec Pid) p' r); intro Hp'r.
    3: elim ((@eq_dec Pid) q' r); intro Hq'r.
    - rewrite Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite Hpr, Par_proj2 in H. 2: apply Network_rm_In.
      rewrite epp_C_Com_r with (HC':=H'); auto.
    - rewrite <- Hp'r, Par_proj1', Network_rm_out; auto.
      rewrite <- Hp'r, Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_Com_p with (HC':=H'), epp_C_Com_p with (HC':=HC'); auto.
      constructor; auto. all: rewrite Hp'r; auto.
      all: apply Process_out; auto.
    - rewrite <- Hq'r, Par_proj1', Network_rm_out; auto.
      rewrite <- Hq'r, Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_Com_q with (HC':=H'), epp_C_Com_q with (HC':=HC'); auto.
      constructor; auto. all: rewrite Hq'r; auto.
      all: apply Process_out; auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_Com_r with (HC':=H'), epp_C_Com_r with (HC':=HC'); auto.
      all: apply Process_out; auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_out, epp_C_out; auto. constructor.
      all: apply Process_out; auto.
  * apply (@S_Else Sig') with b B1 B2; auto.
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC) in H1; inversion H1; auto.
    apply epp_C_wd.
    apply Network_eq_refl.
+ clear s'0 H8 N'0 H7 p0 H0 s0 H5 H.
  rename t into a'', t0 into p', t1 into q', t2 into l.
  generalize (projectable_C_inv_Sel D ps p' q' l a'' C HC); intro HC'.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H1. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H, epp_C_Sel_p with (HC':=HC') in H1; auto.
    inversion H1. rewrite H; auto.
  assert (q' <> p) as Hq'p.
  1: intro. induction l.
    rewrite <- H, epp_C_Sel_ql with (HC':=HC') in H1. inversion H1.
    3: rewrite <- H, epp_C_Sel_qr with (HC':=HC') in H1. 3: inversion H1.
    1,2,3,4: rewrite H; auto.
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (Network_rm _ (epp_C D ps C HC') p | p[B1])); intros.
  rename x into C'. destroy H.
  exists (p' --> q' [l] @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros; intro r. rewrite H3.
    set (H':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0). clearbody H'.
    generalize (H H' r); clear H; intro.
    elim ((@eq_dec Pid) r p); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
    2: elim ((@eq_dec Pid) p' r); intro Hp'r.
    3: elim ((@eq_dec Pid) q' r); intro Hq'r.
    - rewrite Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite Hpr, Par_proj2 in H. 2: apply Network_rm_In.
      rewrite epp_C_Sel_r with (HC':=H'); auto.
    - rewrite <- Hp'r, Par_proj1', Network_rm_out; auto.
      rewrite <- Hp'r, Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_Sel_p with (HC':=H'), epp_C_Sel_p with (HC':=HC'); auto.
      constructor; auto. all: rewrite Hp'r; auto.
      all: apply Process_out; auto.
    - rewrite <- Hq'r, Par_proj1', Network_rm_out; auto.
      rewrite <- Hq'r, Par_proj1', Network_rm_out in H; auto.
      induction l.
      rewrite epp_C_Sel_ql with (HC':=H'), epp_C_Sel_ql with (HC':=HC'); auto.
      6: rewrite epp_C_Sel_qr with (HC':=H'), epp_C_Sel_qr with (HC':=HC'); auto.
      1: apply MB_Branching_Some_None with (Sig:=Sig'); auto.
      5: apply MB_Branching_None_Some with (Sig:=Sig'); auto.
      all: rewrite Hq'r; auto.
      all: apply Process_out; auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_Sel_r with (HC':=H'), epp_C_Sel_r with (HC':=HC'); auto.
      all: apply Process_out; auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_out, epp_C_out; auto. constructor.
      all: apply Process_out; auto.
  * apply (@S_Then Sig') with b B1 B2; auto.
    rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC) in H1; inversion H1; auto.
    apply epp_C_wd.
    apply Network_eq_refl.
+ clear s'0 H8 N'0 H7 p0 H0 s0 H5 H.
  rename t into a'', t0 into p', t1 into q', t2 into l.
  generalize (projectable_C_inv_Sel D ps p' q' l a'' C HC); intro HC'.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H1. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H, epp_C_Sel_p with (HC':=HC') in H1; auto.
    inversion H1. rewrite H; auto.
  assert (q' <> p) as Hq'p.
  1: intro. induction l.
    rewrite <- H, epp_C_Sel_ql with (HC':=HC') in H1. inversion H1.
    3: rewrite <- H, epp_C_Sel_qr with (HC':=HC') in H1. 3: inversion H1.
    1,2,3,4: rewrite H; auto.
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (Network_rm _ (epp_C D ps C HC') p | p[B2])); intros.
  rename x into C'. destroy H.
  exists (p' --> q' [l] @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros; intro r. rewrite H3.
    set (H':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0). clearbody H'.
    generalize (H H' r); clear H; intro.
    elim ((@eq_dec Pid) r p); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
    2: elim ((@eq_dec Pid) p' r); intro Hp'r.
    3: elim ((@eq_dec Pid) q' r); intro Hq'r.
    - rewrite Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite Hpr, Par_proj2 in H. 2: apply Network_rm_In.
      rewrite epp_C_Sel_r with (HC':=H'); auto.
    - rewrite <- Hp'r, Par_proj1', Network_rm_out; auto.
      rewrite <- Hp'r, Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_Sel_p with (HC':=H'), epp_C_Sel_p with (HC':=HC'); auto.
      constructor; auto. all: rewrite Hp'r; auto.
      all: apply Process_out; auto.
    - rewrite <- Hq'r, Par_proj1', Network_rm_out; auto.
      rewrite <- Hq'r, Par_proj1', Network_rm_out in H; auto.
      induction l.
      rewrite epp_C_Sel_ql with (HC':=H'), epp_C_Sel_ql with (HC':=HC'); auto.
      6: rewrite epp_C_Sel_qr with (HC':=H'), epp_C_Sel_qr with (HC':=HC'); auto.
      1: apply MB_Branching_Some_None with (Sig:=Sig'); auto.
      5: apply MB_Branching_None_Some with (Sig:=Sig'); auto.
      all: rewrite Hq'r; auto.
      all: apply Process_out; auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_Sel_r with (HC':=H'), epp_C_Sel_r with (HC':=HC'); auto.
      all: apply Process_out; auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_out, epp_C_out; auto. constructor.
      all: apply Process_out; auto.
  * apply (@S_Else Sig') with b B1 B2; auto.
    rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC) in H1; inversion H1; auto.
    apply epp_C_wd.
    apply Network_eq_refl.
+ clear s'0 H8 N'0 H7 p0 H0 s0 H5 H.
  rename t into p', t0 into b0.
  assert (projectable_C D C1 ps) as HC1.
  1: eapply projectable_C_inv_Then; eauto.
  assert (projectable_C D C2 ps) as HC2.
  1: eapply projectable_C_inv_Else; eauto.
  assert (In p ps) as Hpps.
  1: { revert H1. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  elim ((@eq_dec Pid) p p'); intro Hpp'.
  - revert dependent HC. revert Hsp Hin.
    rewrite <- Hpp'; clear p' Hpp'; intros.
    assert (b = b0).
    1: rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H1; inversion H1; auto.
    revert H2 H1. rewrite H. clear b H. rename b0 into b; intros.
    exists C1. repeat split.
    apply (@C_Then Sig); auto.
    intros; intro r. rewrite H3.
    elim ((@eq_dec Pid) r p); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
    * rewrite Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H1; auto.
      inversion H1. apply MB_refl'.
      rewrite Process_refl. apply epp_C_wd.
    * rewrite Par_proj1', Network_rm_out; auto.
      eapply merge_is_upper_bound, epp_C_Cond_r; eauto.
      apply Process_out; auto.
    * rewrite Par_proj1', Network_rm_out; auto.
      apply MB_refl'. repeat rewrite epp_C_out; auto.
      apply Process_out; auto.
  - assert (forall p, In p ps -> str_proj D C1 p) as Hsp1.
    1: apply Hsp.
    assert (forall p, In p ps -> str_proj D C2 p) as Hsp2.
    1: apply Hsp.
    clear Hsp.
    assert (p' <> p) as Hp'p. auto.
    (* get the remaining equalities *)
    elim (epp_C_Cond_Cond_inv _ _ _ _ _ _ _ HC HC1 HC2 _ _ _ Hp'p H1); auto.
    intros. destroy H. rename x into B1t, x0 into B1e, x1 into B2t, x2 into B2e, H0 into Hp1, H5 into Hp2, H7 into Ht, H into He.
    assert (forall p, In p (CCC_pn C1 (Names D)) -> In p ps) as Hin1.
    1: intros. apply Hin. simpl; sup; sup.
    assert (forall p, In p (CCC_pn C2 (Names D)) -> In p ps) as Hin2.
    1: intros. apply Hin. simpl; sup; sup.
    elim (IHC1 HC1 Hsp1 Hin1 (epp_C D ps C1 HC1 \ p | p[B1t])); intros.
    rename x into C1'. destroy H.
    elim (IHC2 HC2 Hsp2 Hin2 (Network_rm _ (epp_C D ps C2 HC2) p | p[B2t])); intros.
    rename x into C2'. destroy H5. clear IHC1 IHC2.
    exists (If p' ?? b0 Then C1' Else C2'); repeat split.
    * apply (@C_Delay_Cond Sig); repeat split; simpl; auto.
    * intros. intro r. rewrite H3.
      assert (projectable_C D C1' ps) as HC1'.
      1: eapply projectable_C_inv_Then; eauto.
      assert (projectable_C D C2' ps) as HC2'.
      1: eapply projectable_C_inv_Else; eauto.
      elim ((@eq_dec Pid) r p); intro Hpr.
      2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
      2: elim ((@eq_dec Pid) p' r); intro Hp'r.
      ++ generalize (H HC1' r) (H5 HC2' r).
         rewrite Hpr, Par_proj2, Par_proj2, Par_proj2; auto.
         2,3,4: apply Network_rm_In.
         repeat rewrite Process_refl. intros.
         elim (MB_yields_merge _ _ _ _ _ _ H8 H9 Ht); auto.
         intros B' [HB'1 HB1].
         apply MB_trans with B'; auto.
         apply MB_refl'. eapply merge_unique; eauto.
         apply epp_C_Cond_r; auto.
      ++ generalize (H HC1' r) (H5 HC2' r).
         rewrite <- Hp'r. rewrite <- Hp'r in Hr, Hpr. clear r Hp'r.
         rewrite Par_proj1', Par_proj1', Par_proj1', Network_rm_out, Network_rm_out, Network_rm_out; auto.
         rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2); auto.
         rewrite epp_C_Cond_p with (HC1:=HC1') (HC2:=HC2'); auto.
         constructor; auto.
         all: apply Process_out; auto.
      ++ generalize (epp_C_Cond_r _ _ _ _ _ _ HC HC1 HC2 _ Hp'r); intro.
         generalize (epp_C_Cond_r _ _ _ _ _ _ HC' HC1' HC2' _ Hp'r); intro.
         rewrite Par_proj1', Network_rm_out; auto.
         specialize (H5 HC2' r). specialize (H HC1' r).
         rewrite Par_proj1', Network_rm_out in H, H5; auto.
         eapply merge_is_lub; eauto.
         1,2: eapply MB_trans; eauto.
         eapply merge_is_upper_bound; eauto.
         eapply merge_is_upper_bound'; eauto.
         all: apply Process_out; auto.
      ++ rewrite Par_proj1', Network_rm_out; auto.
         repeat rewrite epp_C_out; auto. constructor.
         apply Process_out; auto.
    * apply (@S_Then Sig') with b B2t B2e; auto.
      apply Network_eq_refl.
    * apply (@S_Then Sig') with b B1t B1e; auto.
      apply Network_eq_refl.
+ clear s'0 H8 N'0 H7 p0 H0 s0 H5 H.
  rename t into p', t0 into b0.
  assert (projectable_C D C1 ps) as HC1.
  1: eapply projectable_C_inv_Then; eauto.
  assert (projectable_C D C2 ps) as HC2.
  1: eapply projectable_C_inv_Else; eauto.
  assert (In p ps) as Hpps.
  1: { revert H1. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  elim ((@eq_dec Pid) p p'); intro Hpp'.
  - revert dependent HC. revert Hsp Hin.
    rewrite <- Hpp'; clear p' Hpp'; intros.
    assert (b = b0).
    1: rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H1; inversion H1; auto.
    revert H2 H1. rewrite H. clear b H. rename b0 into b; intros.
    exists C2. repeat split.
    apply (@C_Else Sig); auto.
    intros; intro r. rewrite H3.
    elim ((@eq_dec Pid) r p); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
    * rewrite Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H1; auto.
      inversion H1. apply MB_refl'.
      rewrite Process_refl. apply epp_C_wd.
    * rewrite Par_proj1', Network_rm_out; auto.
      eapply merge_is_upper_bound', epp_C_Cond_r; auto.
      apply Process_out; auto.
    * rewrite Par_proj1', Network_rm_out; auto.
      apply MB_refl'. repeat rewrite epp_C_out; auto.
      apply Process_out; auto.
  - assert (forall p, In p ps -> str_proj D C1 p) as Hsp1.
    1: apply Hsp.
    assert (forall p, In p ps -> str_proj D C2 p) as Hsp2.
    1: apply Hsp.
    clear Hsp.
    assert (p' <> p) as Hp'p. auto.
    (* get the remaining equalities *)
    elim (epp_C_Cond_Cond_inv _ _ _ _ _ _ _ HC HC1 HC2 _ _ _ Hp'p H1); auto.
    intros. destroy H. rename x into B1t, x0 into B1e, x1 into B2t, x2 into B2e, H0 into Hp1, H5 into Hp2, H7 into Ht, H into He.
    assert (forall p, In p (CCC_pn C1 (Names D)) -> In p ps) as Hin1.
    1: intros. apply Hin. simpl; sup; sup.
    assert (forall p, In p (CCC_pn C2 (Names D)) -> In p ps) as Hin2.
    1: intros. apply Hin. simpl; sup; sup.
    elim (IHC1 HC1 Hsp1 Hin1 (epp_C D ps C1 HC1 \ p | p[B1e])); intros.
    rename x into C1'. destroy H.
    elim (IHC2 HC2 Hsp2 Hin2 (Network_rm _ (epp_C D ps C2 HC2) p | p[B2e])); intros.
    rename x into C2'. destroy H5. clear IHC1 IHC2.
    exists (If p' ?? b0 Then C1' Else C2'); repeat split.
    * apply (@C_Delay_Cond Sig); repeat split; simpl; auto.
    * intros. intro r. rewrite H3.
      assert (projectable_C D C1' ps) as HC1'.
      1: eapply projectable_C_inv_Then; eauto.
      assert (projectable_C D C2' ps) as HC2'.
      1: eapply projectable_C_inv_Else; eauto.
      elim ((@eq_dec Pid) r p); intro Hpr.
      2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
      2: elim ((@eq_dec Pid) p' r); intro Hp'r.
      ++ generalize (H HC1' r) (H5 HC2' r).
         rewrite Hpr, Par_proj2, Par_proj2, Par_proj2; auto.
         2,3,4: apply Network_rm_In.
         repeat rewrite Process_refl. intros.
         elim (MB_yields_merge _ _ _ _ _ _ H8 H9 He); auto.
         intros B' [HB'1 HB1].
         apply MB_trans with B'; auto.
         apply MB_refl'. eapply merge_unique; eauto.
         apply epp_C_Cond_r; auto.
      ++ generalize (H HC1' r) (H5 HC2' r).
         rewrite <- Hp'r. rewrite <- Hp'r in Hr, Hpr. clear r Hp'r.
         rewrite Par_proj1', Par_proj1', Par_proj1', Network_rm_out, Network_rm_out, Network_rm_out; auto.
         rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2); auto.
         rewrite epp_C_Cond_p with (HC1:=HC1') (HC2:=HC2'); auto.
         constructor; auto.
         all: apply Process_out; auto.
      ++ generalize (epp_C_Cond_r _ _ _ _ _ _ HC HC1 HC2 _ Hp'r); intro.
         generalize (epp_C_Cond_r _ _ _ _ _ _ HC' HC1' HC2' _ Hp'r); intro.
         rewrite Par_proj1', Network_rm_out; auto.
         specialize (H5 HC2' r). specialize (H HC1' r).
         rewrite Par_proj1', Network_rm_out in H, H5; auto.
         eapply merge_is_lub; eauto.
         1,2: eapply MB_trans; eauto.
         eapply merge_is_upper_bound; eauto.
         eapply merge_is_upper_bound'; eauto.
         all: apply Process_out; auto.
      ++ rewrite Par_proj1', Network_rm_out; auto.
         repeat rewrite epp_C_out; auto. constructor.
         apply Process_out; auto.
    * apply (@S_Else Sig') with b B2t B2e; auto.
      apply Network_eq_refl.
    * apply (@S_Else Sig') with b B1t B1e; auto.
      apply Network_eq_refl.
(* RT_Call - order switched because of inversion *)
+ clear s'0 H8 N'0 H7 p0 H0 s0 H5 H.
  rename t into X, l into ps'.
  assert (projectable_C D C ps) as HC'.
  1: apply str_proj_C'. apply Hsp.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H1. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (~In p ps').
  1: intro. rewrite epp_C_RT_Call in H1; auto; inversion H1.
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  assert (forall p, In p ps -> str_proj D C p) as Hsp'. apply Hsp.
  elim (IHC HC' Hsp' Hin' (Network_rm _ (epp_C D ps C HC') p | p[B1])); intros.
  rename x into C'. destroy H0.
  exists (RT_Call X ps' C'); repeat split.
  * apply C_Delay_Call; repeat split; auto.
    apply disjoint_ps_char.
    intros; intro. rewrite H8 in H7; auto.
  * intros; intro r. rewrite H3.
    assert (projectable_C D C' ps) as H'.
    1: apply str_proj_C'; intros. eapply CCC_To_str_proj_Cond; eauto.
    specialize (H0 H' r).
    elim ((@eq_dec Pid) r p); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps'); intro Hr.
    - rewrite Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite Hpr, Par_proj2 in H0. 2: apply Network_rm_In.
      rewrite epp_C_RT_Call_out with (HC':=H'); auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H0; auto.
      apply MB_refl'.
      repeat rewrite epp_C_RT_Call; auto.
      1,2: apply Hin; simpl; sup.
      all: apply Process_out; auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H0; auto.
      rewrite epp_C_RT_Call_out with (HC':=H'); auto.
      rewrite epp_C_RT_Call_out with (HC':=HC'); auto.
      all: apply Process_out; auto.
  * apply (@S_Then Sig') with b B1 B2; auto.
    rewrite epp_C_RT_Call_out with (HC':=HC') in H1; inversion H1; auto.
    apply Network_eq_refl.
+ clear s'0 H8 N'0 H7 p0 H0 s0 H5 H.
  rename t into X, l into ps'.
  assert (projectable_C D C ps) as HC'.
  1: apply str_proj_C'. apply Hsp.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H1. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (~In p ps').
  1: intro. rewrite epp_C_RT_Call in H1; auto; inversion H1.
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  assert (forall p, In p ps -> str_proj D C p) as Hsp'. apply Hsp.
  elim (IHC HC' Hsp' Hin' (Network_rm _ (epp_C D ps C HC') p | p[B2])); intros.
  rename x into C'. destroy H0.
  exists (RT_Call X ps' C'); repeat split.
  * apply C_Delay_Call; repeat split; auto.
    apply disjoint_ps_char.
    intros; intro. rewrite H8 in H7; auto.
  * intros; intro r. rewrite H3.
    assert (projectable_C D C' ps) as H'.
    1: apply str_proj_C'; intros. eapply CCC_To_str_proj_Cond; eauto.
    specialize (H0 H' r).
    elim ((@eq_dec Pid) r p); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps'); intro Hr.
    - rewrite Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite Hpr, Par_proj2 in H0. 2: apply Network_rm_In.
      rewrite epp_C_RT_Call_out with (HC':=H'); auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H0; auto.
      apply MB_refl'.
      repeat rewrite epp_C_RT_Call; auto.
      1,2: apply Hin; simpl; sup.
      all: apply Process_out; auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H0; auto.
      rewrite epp_C_RT_Call_out with (HC':=H'); auto.
      rewrite epp_C_RT_Call_out with (HC':=HC'); auto.
      all: apply Process_out; auto.
  * apply (@S_Else Sig') with b B1 B2; auto.
    rewrite epp_C_RT_Call_out with (HC':=HC') in H1; inversion H1; auto.
    apply Network_eq_refl.
+ exfalso.
  inversion H.
  1,2: elim (In_dec (@eq_dec Pid) p ps); intros.
  1,3: elim (In_dec (@eq_dec Pid) p (fst (D t))); intros.
  1,3: rewrite epp_C_Call in H1; auto.
  3,4: rewrite epp_C_Call_out in H1; auto.
  5,6: rewrite epp_C_out in H1; auto.
  all: inversion H1.
+ exfalso.
  inversion H.
  all: rewrite epp_C_End in H1; inversion H1.
Unshelve. auto. auto.
Qed.

Lemma SP_To_bproj_Call : forall D (D':DefSetB Sig') ps C HC s N' s' p X Xs,
  Choreography_WF C -> within_Xs Xs C -> In X Xs ->
  (forall p, In p ps -> str_proj D C p) ->
  (forall p, In p (CCC_pn C (Names D)) -> In p ps) ->
  (forall p HX, D' (X,p) = epp_C D ps (snd (D X)) HX p) ->
  (forall p X, In p (CCC_pn (snd (D X)) (Names D))
            -> In p (fst (D X))) ->
  (forall X, In X Xs -> projectable_C D (snd (D X)) ps) ->
  (forall X, In X Xs -> initial (snd (D X))
    /\ forall p, In p (fst (D X)) -> In p ps) ->
  <<epp_C D ps C HC,s>> --[RL_Call ((X,p):recvar Sig') p,D']--> <<N',s'>> ->
  exists C', (<<C,s>> --[RL_Call X p,D]--> <<C',s'>>)%CC
  /\ forall HC', (N' (>>) epp_C D ps C' HC').
Proof.
intros.
rename H into HWF, H0 into HCXs, H1 into HXs, H2 into Hsp, H3 into Hin,
  H4 into HD, H5 into Hnames, H6 into HD', H7 into Hinit, H8 into H.
revert N' H.
induction C; intros. induction e.
+ inversion H.
  clear s'0 H7 N'0 H6 X0 H0 s0 H4 p0 H1.
  rename t into a'', t0 into p', t2 into q', t1 into e, t3 into v.
  generalize (projectable_C_inv_Com D ps p' e q' v a'' C HC); intro HC'.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H2. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H0, epp_C_Com_p with (HC':=HC') in H2; auto.
    inversion H2. rewrite H0; auto.
  assert (q' <> p) as Hq'p.
  1: intro. rewrite <- H0, epp_C_Com_q with (HC':=HC') in H2.
    inversion H2. rewrite H0; auto. rewrite H0; auto.
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  apply Choreography_WF_eta in HWF.
  elim (IHC HC' HWF HCXs Hsp Hin' (Network_rm _ (epp_C D ps C HC') p | Process Sig' p (D' (X,p)))); intros.
  rename x into C'. destroy H0.
  exists (p' # e --> q' $ v @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros. intro r. rewrite H5. 
    set (H':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0).
    generalize (H0 H' r); clear H0.
    elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
    2: elim ((@eq_dec Pid) p' r); intro Hp'r.
    3: elim ((@eq_dec Pid) q' r); intro Hq'r.
    - rewrite <- Hpr, Par_proj2, Par_proj2. 2,3: apply Network_rm_In.
      rewrite epp_C_Com_r with (HC':=H'); auto.
    - rewrite <- Hp'r, Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto.
      2,3: apply Process_out; auto.
      rewrite epp_C_Com_p with (HC':=H'), epp_C_Com_p with (HC':=HC'); auto.
      constructor; auto. all: rewrite Hp'r; auto.
    - rewrite <- Hq'r, Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto.
      2,3: apply Process_out; auto.
      rewrite epp_C_Com_q with (HC':=H'), epp_C_Com_q with (HC':=HC'); auto.
      constructor; auto. all: rewrite Hq'r; auto.
    - rewrite Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto.
      2,3: apply Process_out; auto.
      rewrite epp_C_Com_r with (HC':=H'), epp_C_Com_r with (HC':=HC'); auto.
    - intro. apply MB_refl'.
      rewrite Par_proj1', Network_rm_out; auto.
      2: apply Process_out; auto.
      rewrite epp_C_out, epp_C_out; auto.
  * apply (@S_Call Sig'); auto.
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC) in H2; inversion H2; auto.
    apply epp_C_wd.
    apply Network_eq_refl.
+ inversion H.
  clear s'0 H7 N'0 H6 X0 H0 s0 H4 p0 H1.
  rename t into a'', t0 into p', t1 into q', t2 into l.
  generalize (projectable_C_inv_Sel D ps p' q' l a'' C HC); intro HC'.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H2. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H0, epp_C_Sel_p with (HC':=HC') in H2; auto.
    inversion H2. rewrite H0; auto.
  assert (q' <> p) as Hq'p.
  1: intro. induction l.
    rewrite <- H0, epp_C_Sel_ql with (HC':=HC') in H2.
    inversion H2. rewrite H0; auto. rewrite H0; auto.
    rewrite <- H0, epp_C_Sel_qr with (HC':=HC') in H2.
    inversion H2. rewrite H0; auto. rewrite H0; auto.
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  apply Choreography_WF_eta in HWF.
  elim (IHC HC' HWF HCXs Hsp Hin' (Network_rm _ (epp_C D ps C HC') p | (Process Sig' p (D' (X,p))))); intros.
  rename x into C'. destroy H0.
  exists (p' --> q'[l] @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros. intro r. rewrite H5.
    set (H':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0).
    generalize (H0 H' r); clear H0.
    elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
    2: elim ((@eq_dec Pid) p' r); intro Hp'r.
    3: elim ((@eq_dec Pid) q' r); intro Hq'r.
    - rewrite <- Hpr, Par_proj2, Par_proj2. 2,3: apply Network_rm_In.
      rewrite epp_C_Sel_r with (HC':=H'); auto.
    - rewrite <- Hp'r, Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto.
      2,3: apply Process_out; auto.
      rewrite epp_C_Sel_p with (HC':=H'), epp_C_Sel_p with (HC':=HC'); auto.
      constructor; auto. all: rewrite Hp'r; auto.
    - rewrite <- Hq'r, Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto.
      2,3: apply Process_out; auto.
      induction l.
      rewrite epp_C_Sel_ql with (HC':=H'), epp_C_Sel_ql with (HC':=HC'); auto.
      apply MB_Branching_Some_None with (Sig := Sig'); auto.
      1,2,3,4: rewrite Hq'r; auto.
      rewrite epp_C_Sel_qr with (HC':=H'), epp_C_Sel_qr with (HC':=HC'); auto.
      apply MB_Branching_None_Some with (Sig := Sig'); auto.
      1,2,3,4: rewrite Hq'r; auto.
    - rewrite Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto.
      2,3: apply Process_out; auto.
      rewrite epp_C_Sel_r with (HC':=H'), epp_C_Sel_r with (HC':=HC'); auto.
    - intro. apply MB_refl'.
      rewrite Par_proj1', Network_rm_out; auto.
      2: apply Process_out; auto.
      rewrite epp_C_out, epp_C_out; auto.
  * apply (S_Call Sig'); auto.
    rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC) in H2; inversion H2; auto.
    apply epp_C_wd.
    apply Network_eq_refl.
+ inversion H.
  clear s'0 H7 N'0 H6 p0 H1 X0 H0 s0 H4.
  rename t into p', t0 into b.
  generalize (projectable_C_inv_Then _ _ _ _ _ _ HC); intro HC1.
  generalize (projectable_C_inv_Else _ _ _ _ _ _ HC); intro HC2.
  assert (forall p, In p ps -> str_proj D C1 p) as Hsp1.
  1: apply Hsp.
  assert (forall p, In p ps -> str_proj D C2 p) as Hsp2.
  1: apply Hsp.
  clear Hsp.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H2. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H0, epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H2; auto.
    inversion H2. rewrite H0; auto.
  generalize (Choreography_WF_Then _ _ _ _ _ HWF) as HWF1.
  generalize (Choreography_WF_Else _ _ _ _ _ HWF) as HWF2.
  intros; clear HWF.
  assert (forall p, In p (CCC_pn C1 (Names D)) -> In p ps) as Hin1.
  1: intros. apply Hin. simpl; sup; sup.
  assert (forall p, In p (CCC_pn C2 (Names D)) -> In p ps) as Hin2.
  1: intros. apply Hin. simpl; sup; sup.
  inversion HCXs. rename H0 into HCXs1, H1 into HCXs2.
  elim (IHC1 HC1 HWF1 HCXs1 Hsp1 Hin1 (epp_C D ps C1 HC1 \ p | Process Sig' p (D' (X,p)))); intros.
  rename x into C1'. destroy H0.
  elim (IHC2 HC2 HWF2 HCXs2 Hsp2 Hin2 (Network_rm _ (epp_C D ps C2 HC2) p | Process Sig' p (D' (X,p)))); intros.
  rename x into C2'. destroy H4. clear IHC1 IHC2.
  exists (If p' ?? b Then C1' Else C2'); repeat split.
  * apply C_Delay_Cond; repeat split; auto.
  * intros. intro r. rewrite H5.
    set (H1':=projectable_C_inv_Then _ _ _ _ _ _ HC').
    generalize (H0 H1' r); clear H0.
    set (H2':=projectable_C_inv_Else _ _ _ _ _ _ HC').
    generalize (H4 H2' r); clear H4.
    elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
    2: elim ((@eq_dec Pid) p' r); intro Hp'r.
    - rewrite <- Hpr, Par_proj2, Par_proj2, Par_proj2. 2,3,4: apply Network_rm_In.
      intros. eapply merge_is_lub. apply H4. apply H0.
      apply epp_C_Cond_r; auto.
    - rewrite <- Hp'r, Par_proj1', Par_proj1', Par_proj1', Network_rm_out, Network_rm_out, Network_rm_out; auto.
      2,3,4: apply Process_out; auto.
      rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2). 2: rewrite Hp'r; auto.
      rewrite epp_C_Cond_p with (HC1:=H1') (HC2:=H2'). 2: rewrite Hp'r; auto.
      constructor; auto.
    - rewrite Par_proj1', Par_proj1', Par_proj1', Network_rm_out, Network_rm_out, Network_rm_out; auto.
      2,3,4: apply Process_out; auto.
      intros. eapply merge_is_lub.
      3: apply epp_C_Cond_r; auto.
      1,2: eapply MB_trans; eauto.
      eapply merge_is_upper_bound, epp_C_Cond_r; auto.
      eapply merge_is_upper_bound', epp_C_Cond_r; auto.
    - intros. apply MB_refl'.
      rewrite Par_proj1', Network_rm_out; auto.
      2: apply Process_out; auto.
      rewrite epp_C_out, epp_C_out; auto.
  * apply (S_Call Sig'); auto.
    eapply bproj_unique. apply epp_C_bproj; auto.
    generalize (epp_C_bproj _ _ _ HC _ Hpps); intro.
    rewrite H2 in H4.
    inversion H4. inversion H17. rewrite <- H21, H19; auto.
    apply Network_eq_refl.
  * apply (S_Call Sig'); auto.
    eapply bproj_unique. apply epp_C_bproj; auto.
    generalize (epp_C_bproj _ _ _ HC _ Hpps); intro.
    rewrite H2 in H0.
    inversion H0. inversion H15. rewrite <- H19, H16; auto.
    apply Network_eq_refl.
+ inversion H.
  clear s'0 H7 N'0 H6 p0 H1 X0 H0 s0 H4. rename t into r.
  assert (In p ps /\ In p (fst (D r)) /\ r = X).
  1: { clear H3 H8 H5 N H N' Hin Hsp s s'.
    revert H2. unfold epp_C. elim In_dec. 2: discriminate.
    elim bproj_dec. induction a; simpl; intros.
    rewrite H2 in p0; inversion_clear p0; auto.
    intros H H'. exfalso. contr_aux HC.
  }
  destroy H0. rename H1 into Hpps, H4 into HX.
  revert dependent HC. rewrite H0.
  rewrite H0 in HX, Hsp, Hin, HWF, HCXs; clear r H0; intros.
  assert (0 < [#] (fst (D X))).
  1: {
    elim (Nat.lt_ge_cases 0 ([#] (fst (D X)))); auto.
    intro. inversion H0. apply set_size_0 in H4. rewrite H4 in HX; inversion HX.
  }
  inversion H0.
  - exists (snd (D X)); split.
    apply C_Call_Local; auto.
    intro. intro r. rewrite H5.
    apply MB_refl'.
    elim ((@eq_dec Pid) p r); intro Hpr.
    * rewrite <- Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite Process_refl; auto.
    * rewrite Par_proj1', Network_rm_out; auto.
      rewrite epp_C_Call_out, epp_C_out'; auto.
      ++ intro. apply Hpr.
         apply Hnames in H1.
         eapply set_size_1; eauto.
      ++ intro. apply Hpr. eapply set_size_1; eauto.
      ++ apply Process_out; auto.
  - exists (RT_Call X (fst (D X) [\] p) (snd (D X))).
    split.
    apply C_Call_Start; auto. rewrite <- H1; auto with arith.
    intro. intro r. rewrite H5.
    elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r (fst (D X))); intro Hr.
    * rewrite <- Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite Process_refl.
      apply MB_refl'.
      rewrite epp_C_RT_Call_out with (HC':=HD' X HXs); auto.
      intro Hp; apply set_remove'_2 in Hp; auto.
    * rewrite Par_proj1', Network_rm_out; auto.
      apply MB_refl'.
      rewrite epp_C_RT_Call, epp_C_Call; auto.
      apply set_remove'_3; auto.
      apply Process_out; auto.
    * rewrite Par_proj1', Network_rm_out; auto.
      apply MB_refl'.
      rewrite epp_C_out', epp_C_out'; auto.
      simpl. sup. intro; apply Hr.
      inversion_clear H6. eapply set_remove'_1; eauto.
      apply Hnames; auto.
      apply Process_out; auto.
+ inversion H.
  clear s'0 H7 N'0 H6 p0 H1 X0 H0 s0 H4. rename t into r.
  assert (In p ps) as Hpps.
  1: { revert H2. unfold epp_C. elim In_dec; auto. discriminate. }
  generalize (Choreography_WF_no_empty_ann _ _ HWF) as Hann.
  apply Choreography_WF_Call_1 in HWF.
  intro. destroy Hann. clear Hann.
  assert (projectable_C D C ps) as HCp.
  1: apply str_proj_C'; apply Hsp.
  elim (eq_dec r X); intro Hr. (* case 2 pending *)
  revert dependent HC. rewrite Hr.
  rewrite Hr in Hsp, Hin, HCXs; clear r Hr; intros.
  assert (0 < [#] l).
  1: {
    elim (Nat.lt_ge_cases 0 ([#] l)); auto.
    intro. exfalso. inversion H1. apply set_size_0 in H6; auto.
  }
  elim (In_dec (@eq_dec Pid) p l); intro Hpl. (* weird edge case *)
  1: elim (Nat.eq_dec ([#] l) 1); clear H0; intro H0.
  - exists C; split.
    apply C_Call_Finish; auto.
    intro. intro r. rewrite H5.
    elim ((@eq_dec Pid) p r); intro Hpr.
    * rewrite <- Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite Process_refl.
      elim (Hsp p); auto; intros. elim (H6 p); auto; intros; clear H6.
      rewrite (HD _ (HD' _ HXs)); auto.
      apply H9; apply epp_C_bproj; auto.
    * rewrite Par_proj1', Network_rm_out; auto.
      rewrite epp_C_RT_Call_out with (HC':=HC'). apply MB_refl.
      intro. apply Hpr. eapply set_size_1; eauto.
      apply Process_out; auto.
  - exists (RT_Call X (l [\] p) C).
    split.
    apply C_Call_Enter; auto.
    1: inversion H1; auto. elim H0; auto. apply le_n_S in H6; auto.
    intro. intro r. rewrite H5.
    elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r l); intro Hr.
    * rewrite <- Hpr, Par_proj2, Process_refl. 2: apply Network_rm_In.
      elim (Hsp p); auto; intros.
      rewrite epp_C_RT_Call_out with (HC':=HCp); auto.
      elim (H6 p); auto; clear H6; intros.
      rewrite (HD _ (HD' _ HXs)).
      apply H7; apply epp_C_bproj; auto.
      intro Hp; apply set_remove'_2 in Hp; auto.
    * rewrite Par_proj1', Network_rm_out; auto.
      apply MB_refl'.
      rewrite epp_C_RT_Call, epp_C_RT_Call; auto.
      1,3: apply Hin; simpl; sup.
      apply set_remove'_3; auto.
      apply Process_out; auto.
    * rewrite Par_proj1', Network_rm_out; auto.
      apply MB_refl'.
      rewrite epp_C_RT_Call_out with (HC':=HCp); auto.
      rewrite epp_C_RT_Call_out with (HC':=HCp); auto.
      intro. apply Hr. eapply set_remove'_1; eauto.
      apply Process_out; auto.
  - elim (IHC HCp) with (N':=(Network_rm _ (epp_C _ _ _ HCp) p | Process Sig' p (D'(X,p)))); auto.
    2: elim HCXs; auto.
    2: intros; elim (Hsp p0); auto.
    2: intros; apply Hin; simpl; sup.
    intros. destroy H4. rename x into C'.
    exists (RT_Call X l C'); split.
    * apply C_Delay_Call; auto.
      apply disjoint_ps_char.
      simpl; intros. intro. rewrite H9 in H7; auto.
    * intros.
      assert (projectable_C D C' ps).
      1: {
        eapply (CCC_To_projectable_C D ps C s C' s' (RL_Call X p) Xs); eauto.
        apply Hsp. intros; eapply initial_str_proj; eauto.
        apply Hinit; auto.
        intros. intro. apply Hnames.
        intros r Z. intros. elim (Hinit Z); auto.
        elim HCXs; auto.
      }
      intro r. rewrite H5. clear N N' H H3 H5. rename l into ps'.
      generalize (H4 H7 r); clear H4; intro.
      elim ((@eq_dec Pid) p r); intro Hpr.
      2: rewrite Par_proj1', Network_rm_out; auto.
      2: elim (In_dec (@eq_dec Pid) r ps'); intro Hr.
      ++ rewrite <- Hpr, Par_proj2. 2: apply Network_rm_In.
         rewrite epp_C_RT_Call_out with (HC':=H7); auto.
         rewrite <- Hpr, Par_proj2 in H; auto.
         apply Network_rm_In.
      ++ repeat rewrite epp_C_RT_Call; auto.
         apply MB_refl.
         all: apply Hin; simpl; sup.
      ++ rewrite epp_C_RT_Call_out with (HC':=H7); auto.
         rewrite epp_C_RT_Call_out with (HC':=HCp); auto.
         rewrite Par_proj1', Network_rm_out in H; auto.
         apply Process_out; auto.
      ++ apply Process_out; auto.
    * apply (S_Call Sig'); auto.
      rewrite epp_C_RT_Call_out with (HC':=HCp) in H2; auto.
      apply Network_eq_refl.
  - assert (~In p l) as Hp.
    1: { intro. rewrite epp_C_RT_Call in H2; auto. inversion H2; auto. }
    elim (IHC HCp) with (N':=(Network_rm _ (epp_C _ _ _ HCp) p | Process Sig' p (D'(X,p)))); auto.
    2: elim HCXs; auto.
    2: intros; elim (Hsp p0); auto.
    2: intros; apply Hin; simpl; sup.
    intros. destroy H1. rename x into C', r into Y.
    exists (RT_Call Y l C'); split.
    * apply C_Delay_Call; auto.
      apply disjoint_ps_char.
      simpl; intros. intro. rewrite H7 in H6; auto.
    * intros.
      assert (projectable_C D C' ps).
      1: {
        eapply (CCC_To_projectable_C D ps C s C' s' (RL_Call X p) Xs); eauto.
        apply Hsp. intros; eapply initial_str_proj; eauto.
        apply Hinit; auto.
        intros. intro. apply Hnames.
        intros r Z. intros. elim (Hinit Z); auto.
        elim HCXs; auto.
      }
      intro r. rewrite H5. clear N N' H H3 H5. rename l into ps'.
      generalize (H1 H6 r); clear H1; intro.
      elim ((@eq_dec Pid) p r); intro Hpr.
      2: rewrite Par_proj1', Network_rm_out; auto.
      2: elim (In_dec (@eq_dec Pid) r ps'); intro Hr'.
      ++ rewrite <- Hpr, Par_proj2. 2: apply Network_rm_In.
         rewrite epp_C_RT_Call_out with (HC':=H6); auto.
         rewrite <- Hpr, Par_proj2 in H; auto.
         apply Network_rm_In.
      ++ repeat rewrite epp_C_RT_Call; auto.
         apply MB_refl.
         all: apply Hin; simpl; sup.
      ++ rewrite epp_C_RT_Call_out with (HC':=H6); auto.
         rewrite epp_C_RT_Call_out with (HC':=HCp); auto.
         rewrite Par_proj1', Network_rm_out in H; auto.
         apply Process_out; auto.
      ++ apply Process_out; auto.
    * apply (S_Call Sig'); auto.
      rewrite epp_C_RT_Call_out with (HC':=HCp) in H2; auto.
      apply Network_eq_refl.
+ exfalso.
  inversion H.
  rewrite epp_C_End in H2. inversion H2.
Unshelve. auto. auto.
Qed.

Lemma SP_To_bproj_Call_name : forall D D' ps C HC s N' s' p X,
  <<epp_C D ps C HC,s>> --[RL_Call X p,D']--> <<N',s'>> ->
  exists Y, X = (Y,p) /\ X_Free _ Y C.
Proof.
intros.
inversion H.
clear s'0 H7 N'0 H6 p0 H1 X0 H0 s0 H4 N H3 H s s' H8 N' H5 D'.
revert H2. unfold epp_C.
elim In_dec. 2: discriminate.
elim bproj_dec. induction a; simpl; intros.
rewrite H2 in p0. clear a x H2.
clear HC. rename p0 into HC. revert HC; simpl.
induction C; simpl; try discriminate.
induction e. 2: induction t2. all: intros.
all: inversion HC; try tauto.
all: unfold X_Free; simpl; unfold set_union_rv.
- inversion H9.
  elim IHC1; auto; intros. destroy H12.
  exists x; repeat split; auto. sup.
  rewrite <- H13, H10; auto.
- exists t; auto.
- exists t; repeat split. sup; simpl; auto.
- elim IHC; auto; intros. destroy H7.
  exists x. split; auto. sup; simpl; auto.
- clear H2. rewrite <- H in a; inversion a.
- clear H2. contr HC.
Qed.

Lemma EPP_Sound : forall P Xs ps,
  Program_WF _ Xs P -> well_ann _ P -> forall (HP:projectable Xs ps P),
  (forall p, In p ps -> str_proj (Procedures _ P) (Main P) p) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In X Xs -> In p (Vars P X) -> In p ps) ->
  forall s tl N' s', (epp Xs ps P HP,s) --[tl]--> (N',s') ->
  exists P' tl', ((P,s) --[tl']--> (P',s'))%CC /\
    forall H, Net N' (>>) Net (epp Xs ps P' H).
Proof.
intros.
inversion H4.
clear tl H4 s'0 H10 H6 s0 H7 s'0 N' H9. rename N'0 into N'.
rename D into D'.
induction P as (D,C).
assert (projectable_C D C ps) as HC.
1: inversion HP; auto.
assert (SP_To _ D' (epp_C _ _ _ HC) s t N' s').
1: {
  eapply SP_To_Network_eq; eauto. eapply Network_eq_trans.
  2: apply epp_C_char. rewrite <- H5. apply Network_eq_refl.
}
destroy H. simpl in H6, H7, H9.
  unfold CC.Procs in H; simpl in H.
inversion HP. simpl in H10, H11. destroy H11.
simpl in H1, H2, H3.
red in H12; rewrite Forall_forall in H12.
assert (forall X p, In X Xs -> In p ps -> str_proj D (snd (D X)) p).
1: {
  intros. elim (In_dec (@eq_dec Pid) p (fst (D X))); intro.
  eapply initial_str_proj; eauto. apply (H X); auto.
  eapply initial_str_proj'; eauto. apply (H X); auto.
  intro; apply b, H0; auto.
}
induction t. 2: induction l.
+ apply SP_To_bproj_Com in H4.
  destroy H4. rename x0 into C'.
  assert (projectable_C D C' ps).
  1: { eapply CCC_To_projectable_C; eauto. }
  exists (D,C'),
     (@forget Pid Value Var RecVar (RL_Com p v q x)); repeat split; auto.
  - apply (@CCP_To_intro Sig); auto.
  - simpl. intros. apply MBN_refl'.
    eapply Network_eq_trans. apply (H4 H17); auto.
    apply Network_eq_sym; apply epp_C_char.
  - apply H1.
  - apply H2.
+ apply SP_To_bproj_Sel_l in H4.
  destroy H4. rename x into C'.
  assert (projectable_C D C' ps).
  1: { eapply CCC_To_projectable_C; eauto. }
  exists (D,C'),
     (@forget Pid Value Var RecVar (RL_Sel p q left)); repeat split; auto.
  - apply (@CCP_To_intro Sig); auto.
  - simpl. intros. apply MBN_refl'.
    eapply Network_eq_trans. apply (H4 H17); auto.
    apply Network_eq_sym; apply epp_C_char.
  - apply H1.
  - apply H2.
+ apply SP_To_bproj_Sel_r in H4.
  destroy H4. rename x into C'.
  assert (projectable_C D C' ps).
  1: { eapply CCC_To_projectable_C; eauto. }
  exists (D,C'),
     (@forget Pid Value Var RecVar (RL_Sel p q right)); repeat split; auto.
  - apply (@CCP_To_intro Sig); auto.
  - simpl. intros. apply MBN_refl'.
    eapply Network_eq_trans. apply (H4 H17); auto.
    apply Network_eq_sym; apply epp_C_char.
  - apply H1.
  - apply H2.
+ apply SP_To_bproj_Cond in H4.
  destroy H4. rename x into C'.
  assert (projectable_C D C' ps).
  1: { eapply CCC_To_projectable_C; eauto. }
  exists (D,C'),
     (@forget Pid Value Var RecVar (RL_Cond p)); repeat split; auto.
  - apply (@CCP_To_intro Sig); auto.
  - simpl. intros. eapply MBN_trans. apply (H4 H17).
    apply MBN_refl'.
    apply Network_eq_sym. apply epp_C_char.
  - apply H1.
  - apply H2.
+ elim (SP_To_bproj_Call_name _ _ _ _ _ _ _ _ _ _ H4); intros.
  destroy H16. rename x into Y. rewrite H17 in H4, H8; clear X H17.
  assert (In Y Xs).
  1: apply within_Xs_char with (X:=Y) in H7; auto.
  apply SP_To_bproj_Call with (Xs:=Xs) in H4; auto.
  destroy H4. rename x into C'.
  assert (projectable_C D C' ps).
  1: { eapply CCC_To_projectable_C; eauto. }
  exists (D,C'),
     (@forget Pid Value Var RecVar (RL_Call Y p)); repeat split; auto.
  - apply (@CCP_To_intro Sig); auto.
  - simpl. intros. eapply MBN_trans. apply (H4 H19).
    apply MBN_refl'.
    apply Network_eq_sym. apply epp_C_char.
  - replace D' with (Procs (epp _ _ _ HP)).
    2: rewrite <- H5; auto.
    intro r; intros. rewrite epp_D_char'' with (HX:=H12 _ H17); auto.
    elim (In_dec (@eq_dec Pid) r (fst (D Y))); intro Hr.
    eapply bproj_unique; apply epp_C_bproj; eauto.
    rewrite epp_C_out; auto. rewrite epp_C_out'; auto.
    intro. apply Hr, H0; auto.
  - intros; apply H0; auto.
  - intros. apply Forall_forall; intros.
    apply str_proj_C; auto.
  - split; eauto. apply H; auto.
Qed.

Lemma SP_To_MBN_epp : forall D N1 s N2 s' tl D' ps C HC,
  N1 (>>) epp_C D' ps C HC -> <<N1,s>> --[tl,D]--> <<N2,s'>> ->
  exists N2', <<epp_C D' ps C HC,s>> --[tl,D]--> <<N2',s'>> /\ N2 (>>) N2'.
Proof.
intros.
rename H into Hmb, H0 into HTo.
inversion HTo.
+ clear s'0 H7 N' H6 tl H5 N H3 s0 H4 HTo.
  generalize (Hmb p); intro.
  rewrite H in H3; inversion H3.
  rename B'0 into Bp; clear B0 H8 a0 H7 e0 H6 p0 H4.
  rename H9 into H8. symmetry in H8.
  generalize (Hmb q); intro.
  rewrite H0 in H4; inversion H4.
  rename B'0 into Bq; clear B0 H11 x0 H10 a0 H9 p0 H6.
  rename H12 into H11. symmetry in H11.
  assert (p <> q) as Hpq.
  1: intro. rewrite H6, H0 in H; inversion H.
  exists (Network_rm _ (Network_rm _ (epp_C D' ps C HC) p) q | p[Bp] | q[Bq]).
  repeat split.
  1: apply S_Com with (a:ann Sig') Bp a' Bq; auto. apply Network_eq_refl.
  eapply MBN_trans. apply MBN_refl'; eauto.
  intro r. elim ((@eq_dec Pid) r p); intro Hp.
  2: elim ((@eq_dec Pid) r q); intro Hq.
  - rewrite Hp, Network_rm_add_2_p, Network_rm_add_2_p; auto.
  - rewrite Hq, Network_rm_add_2_q, Network_rm_add_2_q; auto.
  - rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
+ clear s'0 H7 N' H6 tl H5 N H3 s0 H4 HTo.
  assert (p <> q) as Hpq.
  1: intro. rewrite H3, H0 in H; inversion H.
  generalize (Hmb p); intro.
  rewrite H in H3; inversion H3.
  rename B' into Bp; clear B0 H8 a0 H7 l H6 p0 H4.
  rename H9 into H8; symmetry in H8.
  generalize (Hmb q); intro.
  rewrite H0 in H4; inversion H4.
  - symmetry in H11. apply epp_C_not_Branching_None_None in H11. inversion H11.
  - symmetry in H11. eapply epp_C_Sel_Branching_l in H11; eauto. tauto.
  - symmetry in H11. clear mBr H11 Bl0 H10 a0 H9 p0 H6.
    exists (epp_C D' ps C HC \ p \ q | p[Bp] | q[Bl']).
    repeat split.
    1: apply S_LSel with (a:ann Sig') Bp a' Bl' None; auto. apply Network_eq_refl.
    eapply MBN_trans. apply MBN_refl'; eauto.
    intro r. elim ((@eq_dec Pid) r p); intro Hp.
    2: elim ((@eq_dec Pid) r q); intro Hq.
    * rewrite Hp, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    * rewrite Hq, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    * rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
  - symmetry in H12. rewrite <- H11 in H0. clear Br H11 Bl0 H10 a0 H7 p0 H6 H4. rename Br0 into Br.
    exists (epp_C D' ps C HC \ p \ q | p[Bp] | q[Bl']).
    repeat split.
    1: apply S_LSel with (a:ann Sig') Bp a' Bl' (Some (a'0,Br')); auto. apply Network_eq_refl.
    eapply MBN_trans. apply MBN_refl'; eauto.
    intro r. elim ((@eq_dec Pid) r p); intro Hp.
    2: elim ((@eq_dec Pid) r q); intro Hq.
    * rewrite Hp, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    * rewrite Hq, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    * rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
+ clear s'0 H7 N' H6 tl H5 N H3 s0 H4 HTo.
  assert (p <> q) as Hpq.
  1: intro. rewrite H3, H0 in H; inversion H.
  generalize (Hmb p); intro.
  rewrite H in H3; inversion H3.
  rename B' into Bp; clear B0 H8 a0 H7 l H6 p0 H4.
  rename H9 into H8. symmetry in H8.
  generalize (Hmb q); intro.
  rewrite H0 in H4; inversion H4.
  - symmetry in H11. apply epp_C_not_Branching_None_None in H11. inversion H11.
  - symmetry in H12. clear mBl H9 Br0 H11 a0 H10 p0 H6.
    exists (epp_C D' ps C HC \ p \ q | p[Bp] | q[Br']).
    repeat split.
    1: apply S_RSel with (a:ann Sig') Bp a' None Br'; auto. apply Network_eq_refl.
    eapply MBN_trans. apply MBN_refl'; eauto.
    intro r. elim ((@eq_dec Pid) r p); intro Hp.
    2: elim ((@eq_dec Pid) r q); intro Hq.
    * rewrite Hp, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    * rewrite Hq, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    * rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
  - symmetry in H11. eapply epp_C_Sel_Branching_r in H11; eauto. tauto.
  - symmetry in H12. rewrite <- H7 in H0. clear Bl H7 Br0 H11 a'0 H10 p0 H6 H4. rename Bl0 into Bl.
    exists (epp_C D' ps C HC \ p \ q | p[Bp] | q[Br']).
    repeat split.
    1: apply S_RSel with (a:ann Sig') Bp a' (Some (a0,Bl')) Br'; auto. apply Network_eq_refl.
    eapply MBN_trans. apply MBN_refl'; eauto.
    intro r. elim ((@eq_dec Pid) r p); intro Hp.
    2: elim ((@eq_dec Pid) r q); intro Hq.
    * rewrite Hp, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    * rewrite Hq, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    * rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
+ clear s'0 H7 N' H6 tl H5 N H3 s0 H4 HTo.
  generalize (Hmb p); intro.
  rewrite H in H3; inversion H3.
  clear B3 H7 B0 H5 b0 H4. symmetry in H8.
  exists (Network_rm _ (epp_C D' ps C HC) p | p[B1']).
  repeat split.
  1: apply (@S_Then Sig') with b B1' B2'; auto. apply Network_eq_refl.
  eapply MBN_trans. apply MBN_refl'; eauto.
  intro r. elim ((@eq_dec Pid) r p); intro Hp.
  - rewrite Hp, Par_proj2, Par_proj2, Process_refl, Process_refl; auto;
      apply Network_rm_In.
  - rewrite Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto;
      apply Process_out; auto.
+ clear s'0 H7 N' H6 tl H5 N H3 s0 H4 HTo.
  generalize (Hmb p); intro.
  rewrite H in H3; inversion H3.
  clear B3 H7 B0 H5 b0 H4. symmetry in H8.
  exists (epp_C D' ps C HC \ p | p[B2']).
  repeat split. 
  1: apply (@S_Else Sig') with b B1' B2'; auto. apply Network_eq_refl.
  eapply MBN_trans. apply MBN_refl'; eauto.
  intro r. elim ((@eq_dec Pid) r p); intro Hp.
  - rewrite Hp, Par_proj2, Par_proj2, Process_refl, Process_refl; auto;
      apply Network_rm_In.
  - rewrite Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto;
      apply Process_out; auto.
+ clear s'0 H6 N' H5 tl H4 s0 H3 N H2 HTo.
  generalize (Hmb p); intro.
  rewrite H in H2; inversion H2.
  clear X0 H4. symmetry in H5.
  exists (epp_C D' ps C HC \ p | p [D X]).
  repeat split.
  1: apply S_Call; auto. apply Network_eq_refl.
  eapply MBN_trans. apply MBN_refl'; eauto.
  intro r. elim ((@eq_dec Pid) r p); intro Hp.
  - rewrite Hp, Par_proj2, Par_proj2. 2,3: apply Network_rm_In.
    apply MB_refl.
  - rewrite Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto;
      apply Process_out; auto.
Qed.

Lemma SPP_To_MBN_epp : forall P1 s P2 s' tl Xs ps P HP,
  (forall X, Procs P1 X = Procs (epp Xs ps P HP) X) ->
  Net P1 (>>) Net (epp Xs ps P HP) -> SPP_To _ (P1,s) tl (P2,s') ->
  exists P2', ((epp Xs ps P HP,s) --[tl]--> (P2',s')) /\ Net P2 (>>) Net P2'
  /\ forall X, Procs P2 X = Procs P2' X.
Proof.
intros.
induction P1 as (D,N1), P2 as (D2,N2).
rewrite <- (SPP_To_Defs_stable _ _ _ _ _ _ _ _ H1);
rewrite <- (SPP_To_Defs_stable _ _ _ _ _ _ _ _ H1) in H1; clear D2.
induction P as (D',C).
inversion HP. inversion_clear H3. clear H5. simpl in H2, H4.
inversion H1. clear s'0 H10 N' H9 tl H5 s0 H7 N H6 D0 H3 H1.
eapply SP_To_MBN_epp with (HC:=H2) in H8; eauto.
2: intro r; rewrite <- epp_C_char with (HP:=HP); auto.
destroy H8. rename x into N2'.
exists (Procs (epp _ _ _ HP),N2'); repeat split; auto.
rewrite (SP_eta _ (epp _ _ _ HP)); constructor.
simpl. apply SP_To_Defs_wd with D; auto.
eapply SP_To_Network_eq; eauto.
apply Network_eq_sym; apply epp_C_char.
Qed.

(** Generalizing the last result to -->* already requires the EPP Theorem. *)

Lemma SPP_ToStar_MBN_epp : forall P1 s P2 s' tl Xs ps P,
  Program_WF _ Xs P -> well_ann _ P -> forall (HP:projectable Xs ps P),
  (forall p, In p ps -> str_proj (Procedures _ P) (Main P) p) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In X Xs -> In p (Vars P X) -> In p ps) ->
  (forall X, Procs P1 X = Procs (epp Xs ps P HP) X) ->
  Net P1 (>>) Net (epp Xs ps P HP) -> (P1,s) --[tl]-->* (P2,s') ->
  exists P2', (epp Xs ps P HP,s) --[tl]-->* (P2',s') /\ Net P2 (>>) Net P2'
  /\ forall X, Procs P2 X = Procs P2' X.
Proof.
intros.
induction P1 as (D,N1), P2 as (D2,N2).
rewrite <- (SPP_ToStar_Defs_stable _ _ _ _ _ _ _ _ H6);
rewrite <- (SPP_ToStar_Defs_stable _ _ _ _ _ _ _ _ H6) in H6; clear D2.
induction P as (D',C).
revert dependent C. revert s s' N1 N2 H6. induction tl; intros.
+ inversion H6. rewrite <- H8.
  exists (epp _ _ _ HP); repeat split; auto. constructor.
+ inversion H6. clear c3 H11 l H8 t H7 c1 H9 H6. rename a into t.
  induction c2 as ((D2,N3),s'').
  rewrite <- (SPP_To_Defs_stable _ _ _ _ _ _ _ _ H10) in H12, H10. clear D2.
  apply SPP_To_MBN_epp with (HP:=HP) in H10; auto.
  destroy H10. induction x as (D3,N3'). simpl in H7, H10.
  generalize H6 as H6'; intro.
  rewrite (SP_eta _ (epp _ _ _ HP)) in H6'.
  rewrite <- (SPP_To_Defs_stable _ _ _ _ _ _ _ _ H6') in H6, H10, H6'. clear D3.
  rewrite <- SP_eta in H6'.
  apply EPP_Sound in H6; auto. destroy H6. rename x0 into t'.
  induction x as (D'3,C'').
  rewrite <- (CCP_To_Defs_stable _ _ _ _ _ _ _ _ H8) in H6, H8. clear D'3.
  assert (projectable Xs ps (D',C'')).
  1: eapply CCC_To_projectable; eauto.
  generalize (H6 H9); clear H6; intro. simpl in H6.
  generalize H12 as H12'; intro.
  inversion HP. clear H11; inversion_clear H13. simpl in H11; clear H14.
  rename H11 into HD.
  apply IHtl with (HP:=H9) in H12; auto. clear IHtl.
  destroy H12. rename x into P2'. induction P2' as (D2',N2').
  rewrite (SP_eta _ (epp _ _ _ H9)) in H11.
  rewrite <- (SPP_ToStar_Defs_stable _ _ _ _ _ _ _ _ H11) in H13, H12, H11.
  clear D2'. rewrite <- SP_eta in H11. simpl in H11, H12, H13.
  apply SPP_ToStar_MBN with (P1':=(Procs (epp _ _ _ HP),N3')) in H11; auto.
  destroy H11. rename x into P2'. simpl in H11, H15.
  exists P2'; repeat split; auto.
  - econstructor; eauto.
  - simpl.
    apply SPP_ToStar_MBN with (P1':=(D,N3)) in H14; auto.
    destroy H14. apply MBN_trans with (Net x); auto.
    apply MBN_refl'.
    change N2 with (Net (D,N2)).
    eapply SPP_ToStar_deterministic_1; eauto.
    simpl; intro.
    rewrite H12. induction X. repeat rewrite epp_D_char with (HD:=HD); auto.
  - simpl; intro. rewrite H12, <- H11.
    induction X. repeat rewrite epp_D_char with (HD:=HD); auto.
  - simpl; intro. induction X; repeat rewrite epp_D_char with (HD:=HD); auto.
  - eapply CCC_To_Program_WF; eauto.
  - eapply CCP_To_str_proj; eauto.
  - intros. apply H2. eapply CCC_To_pn''; eauto.
  - intro; rewrite H10. induction X; repeat rewrite epp_D_char with (HD:=HD); auto.
  - apply MBN_trans with N3'; auto.
Qed.

Lemma EPP_Sound' : forall P Xs ps,
  Program_WF _ Xs P -> well_ann _ P -> forall (HP:projectable Xs ps P),
  (forall p, In p ps -> str_proj (Procedures _ P) (Main P) p) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In X Xs -> In p (Vars P X) -> In p ps) ->
  forall s tl P' s', (epp Xs ps P HP,s) --[tl]-->* (P',s') ->
  exists P'' tl', ((P,s) --[tl']-->* (P'',s'))%CC /\
    forall H, Net P' (>>) Net (epp Xs ps P'' H).
Proof.
intros.
induction P as (D,C), P' as (D',N).
revert dependent N. revert dependent C. revert D' s s'.
induction tl; intros; inversion H4.
+ eexists; exists nil. repeat split. constructor.
  intro. apply MBN_refl'.
  inversion HP. simpl in H9.
  apply Network_eq_trans with (epp_C D ps C H9).
  2: apply Network_eq_sym. all: apply epp_C_char.
+ clear c3 H9 l H6 t H5 c1 H7 H4. rename a into t.
  induction c2 as (P'', s'').
  eapply SPP_To_MBN_epp in H8; eauto. destroy H8.
  rename x into P'. 2: apply MBN_refl.
  rewrite (SP_eta _ (epp _ _ _ HP)), (SP_eta _ P') in H4.
  generalize (SPP_To_Defs_stable _ _ _ _ _ _ _ _ H4); intro H4'.
  rewrite <- SP_eta, <- SP_eta in H4.
  apply EPP_Sound in H4; auto. destroy H4.
  rename x into P1, x0 into t'.
  assert (projectable Xs ps P1).
  1: eapply CCC_To_projectable; eauto.
  induction P1 as (D1, C1).
  rewrite <- (CCP_To_Defs_stable _ _ _ _ _ _ _ _ H6) in H4, H7, H6. clear D1.
  generalize (H4 H7); clear H4; intro.
  assert (Program_WF _ Xs (D,C1)).
  1: eapply CCC_To_Program_WF; eauto.
  assert (forall p, In p ps -> str_proj D C1 p).
  1: {
    change D with (Procedures _ (D,C1)).
    change C1 with (Main (D,C1)) at 2.
    intros. inversion HP. destroy H13.
    eapply CCP_To_str_proj with (P:=(D,C)); eauto.
  }
  assert (forall p, In p (CCC_pn C1 (Vars (D,C1))) -> In p ps).
  1:{
    change C1 with (Main (D,C1)) at 1.
    intros. apply H2. eapply CCC_To_pn''; eauto.
  }
  apply SPP_ToStar_MBN_epp with (HP:=H7) in H10; auto.
  - destroy H10.
    rename x into P1. induction P1 as (D1,N1).
    eapply IHtl in H9; auto. 2: apply H13.
    destroy H9. rename x into P2, x0 into tl'.
    clear IHtl. exists P2, (t'::tl').
    repeat split.
    eapply CCT_Step; eauto.
    intro. apply MBN_trans with N1; auto.
  - intro. rewrite H8, <- H4'.
    inversion HP. destroy H14. induction X.
    simpl in H15; repeat rewrite epp_D_char with (HD:=H15); auto.
  - apply MBN_trans with (Net P'); auto.
Qed.

End EPP_Theorem.

End EndPointProjection.
