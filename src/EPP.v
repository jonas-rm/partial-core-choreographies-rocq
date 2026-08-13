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

(** Like [merge], this relation is functional... *)

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

Definition projectable_D D :=
  forall X, projectable_C D (snd (D X)) (fst (D X)).

Definition projectable_P P :=
  projectable_C (Procedures P) (Main P) (CCP_pn P) /\
  projectable_D (Procedures P).

(* Definition projectable P := Program_WF P /\ projectable_P P. *)

(** For tackling contradictions in the absurd cases of the definitions below. *)

Ltac contr_aux H := red in H; rewrite Forall_forall in H; auto.
Ltac contr H := intros; exfalso; contr_aux H.
Ltac contr2 H H' := intros; exfalso; specialize (H H'); contr_aux H.

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

Definition epp_D D : projectable_D D -> DefSetB Sig'.
Proof.
intros; intro.
case_eq X; intros R p HX.
elim (In_dec (@eq_dec Pid) p (fst (D R))).
2: intros; apply End.
induction (bproj_dec D (snd (D R)) p) as [ [B HB] | HC]; intros.
apply B.
contr2 H R.
Defined.

Definition epp P : projectable_P P -> Program Sig'.
Proof.
intro H. induction H as (HC,HD).
constructor.
apply (epp_D _ HD).
apply (epp_C _ _ _ HC).
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

Lemma bproj_stable : forall D D' p C B,
  (forall X, fst (D X) = fst (D' X)) ->
  [[D,C | p]] == B -> [[D',C | p]] == B.
Proof.
intros. induction H0; auto.
all: try constructor; auto.
2,3: rewrite <- H; auto.
apply bproj_Cond' with B1 B2; auto.
Qed.

Lemma projectable_B_stable : forall D D' p C,
  (forall X, fst (D X) = fst (D' X)) ->
  projectable_B D p C -> projectable_B D' p C.
Proof.
intros. induction H0 as [B HB].
exists B. apply bproj_stable with D; auto.
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

Lemma epp_C_char : forall D C HP HC,
  Net (epp (D,C) HP) (==) (epp_C D (CCP_pn (D,C)) C HC).
Proof.
intros.
unfold epp.
case HP; intros.
apply epp_C_wd.
Qed.

Lemma epp_C_char' : forall ps D C HP p, In p ps ->
  [[D,C | p]] == Net (epp (D, C) HP) p.
Proof.
intros; unfold epp.
case HP; intros.
simpl.
unfold epp_C. elim in_dec; simpl.
elim bproj_dec; simpl.
+ induction a; auto.
+ contr p0.
+ apply bproj_not_In.
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

Lemma epp_D_wd : forall D H H' X, epp_D D H X = epp_D D H' X.
Proof.
intros; unfold epp_D.
induction X as (R,p).
elim In_dec; auto.
intros. elim bproj_dec; auto.
contr2 H R.
Qed.

Lemma epp_D_char : forall D C HP HD X p,
  Procs (epp (D,C) HP) (X,p) = epp_D D HD (X,p).
Proof.
intros.
unfold epp.
case HP; intros.
apply epp_D_wd.
Qed.

Lemma epp_D_char' : forall D C HP X p,
  CCC_pn (snd (D X)) (Names D) [C] fst (D X) ->
  [[D,snd (D X) | p]] == Procs (epp (D,C) HP) (X,p).
Proof.
intros.
unfold epp.
case HP as (HC,HD).
simpl.
elim In_dec; simpl; intro Hp.
elim bproj_dec; simpl; intro Hb.
elim Hb; simpl; intros; auto.
+ contr2 HD X.
+ apply bproj_not_In.
  intro; apply Hp, H. auto.
Qed.

Lemma epp_D_char'' : forall D C HP X p HX,
   Procs (epp (D,C) HP) (X, p) = epp_C D (fst (D X)) (snd (D X)) HX p.
Proof.
intros D C HP X p HX.
case HP as (HC,HD).
rewrite epp_D_char with (HD:=HD).
simpl. elim In_dec; intro.
2: simpl; rewrite epp_C_out; auto.
elim bproj_dec. induction a0; simpl; intros.
eapply bproj_unique; eauto. apply epp_C_bproj; auto.
contr HX.
Qed.

Lemma epp_out : forall P HP p, ~In p (CCP_pn P) ->
  Net (epp P HP) p = End _.
Proof.
intros; unfold epp.
unfold epp.
case HP as (HC,HD); simpl; intros.
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

(** ** Properties of projectability *)

Section Projectability.

(** Projectability is decidable - for programs, with the same proviso
  as well-formedness. *)

Lemma projectable_B_dec : forall D C p,
  { projectable_B D C p } + { ~projectable_B D C p }.
Proof.
intros. elim (bproj_dec D C p); auto.
left. induction a. red. eauto.
Qed.

Lemma projectable_C_dec : forall D C ps,
  { projectable_C D C ps } + { ~projectable_C D C ps }.
Proof.
intros. apply Forall_dec; intro.
elim (projectable_B_dec D C x); auto.
Qed.

Lemma projectable_P_dec : forall P Xs, used_procedures _ P Xs ->
  { projectable_P P } + { ~projectable_P P }.
Proof.
intros.
(* elim (Program_WF_dec _ P Xs); auto. intro HWF.
2: right; intro HP; destruct HP; auto. *)
elim (projectable_C_dec (Procedures P) (Main P) (CCP_pn P)); intro HC.
2: right; intro HP; destruct HP; tauto.
assert ({forall X, In X Xs -> projectable_C (Procedures P) (snd (Procedures P X)) (fst (Procedures P X))}
         + {~forall X, In X Xs -> projectable_C (Procedures P) (snd (Procedures P X)) (fst (Procedures P X))}).
2: inversion_clear H0.
+ clear H HC.
  set (D := Procedures P). clearbody D; clear P.
  induction Xs. simpl; tauto.
  elim IHXs; intro.
  2: { right. intro. apply b; intros. apply H; simpl; auto. }
  elim (projectable_C_dec D (snd (D a)) (fst (D a))); intros.
  left; simpl; intros. inversion_clear H; auto. rewrite <- H0; auto.
  right. simpl; intro; apply b; auto.
+ left. repeat (split; auto).
  intro X; elim (In_dec (@eq_dec RecVar) X Xs); intro; auto.
  generalize (used_procedures_End _ _ _ H _ b); intro.
  unfold CC.Procs in H0. rewrite H0.
  red; rewrite Forall_forall. exists bnil; constructor.
+ right.
  intro. apply H1. intros; apply H0.
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

(** Meh. *)

Lemma projectable_C_incl : forall D C ps ps', ps [C] ps' ->
  projectable_C D C ps' -> projectable_C D C ps.
Proof.
intros D C ps ps'.
unfold projectable_C; repeat rewrite Forall_forall.
intros. apply H0; auto.
Qed.

(** More inversion lemmas about program projectability. *)

Lemma projectable_P_inv_Eta : forall D eta a C,
  projectable_P (D,eta@a;;C) -> projectable_P (D,C).
Proof.
intros.
induction H as (HC,HD).
split; auto.
apply projectable_C_inv_Eta with eta a.
eapply projectable_C_incl; eauto.
unfold CCP_pn, Vars; simpl.
red. intros. sup.
Qed.

Lemma projectable_P_inv_Com : forall D p e q x a C,
  projectable_P (D,p#e-->q$x@a;;C) -> projectable_P (D,C).
Proof. intros; eapply projectable_P_inv_Eta; eauto. Qed.

Lemma projectable_P_inv_Sel : forall D p q l a C,
  projectable_P (D,p-->q[l]@a;;C) -> projectable_P (D,C).
Proof. intros; eapply projectable_P_inv_Eta; eauto. Qed.

Lemma projectable_inv_Then : forall D p b C1 C2,
  projectable_P (D,If p ?? b Then C1 Else C2) -> projectable_P (D,C1).
Proof.
intros.
induction H as (HC,HD).
split; auto.
apply projectable_C_inv_Then with p b C2.
eapply projectable_C_incl; eauto.
unfold CCP_pn, Vars; simpl. red. intros. repeat sup.
Qed.

Lemma projectable_P_inv_Else : forall D p b C1 C2,
  projectable_P (D,If p ?? b Then C1 Else C2) -> projectable_P (D,C2).
Proof.
intros.
induction H as (HC,HD).
split; auto.
apply projectable_C_inv_Else with p b C1.
eapply projectable_C_incl; eauto.
unfold CCP_pn, Vars; simpl. red. intros. repeat sup.
Qed.

Lemma projectable_P_inv_RT_Call : forall D X p ps C, [#]ps > 1 -> 
  projectable_P (D,RT_Call X ps C) -> (exists B, [[D,C | p]] == B) ->
  projectable_P (D,RT_Call X (ps [\] p) C).
Proof.
intros.
induction H0 as (HC,DC).
split; auto.
(* + induction HWF as (HC',((Hincl,Hcons),HX)).
  split. 2: split; auto; split.
  all: clear HX; simpl in *.
  - inversion_clear HC'; split; auto.
    inversion_clear H2; split; auto.
    intro. elim (In_dec (@eq_dec Pid) p ps); intro Hp.
    rewrite set_size_remove' with (x:=p) in H; auto.
    rewrite H2 in H; inversion H. inversion H6.
    rewrite set_remove'_not_In in H2; auto.
  - revert Hincl. unfold Vars; simpl.
    red; intros. apply Hincl.
    eapply set_remove'_1; eauto.
  - apply Hcons. *)
red; red in HC.
rewrite Forall_forall; rewrite Forall_forall in HC.
intros. case (eq_dec x p); intro Hx.
- rewrite Hx in *; clear x Hx.
  induction H1 as [B HB]; clear H0 H.
  exists B. constructor; auto.
  intro. apply set_remove'_2 in H; auto.
- induction (HC x) as [B HB]; clear HC.
  exists B. simpl in *.
  inversion HB. all: try constructor; auto.
  apply set_remove'_3; auto.
  intro; apply H8. apply set_remove'_1 in H10; auto.
  revert H0. unfold CCP_pn; simpl.
  repeat sup. unfold Vars. simpl; intros.
  inversion_clear H0; auto.
  left. eapply set_remove'_1; eauto.
Qed.

(** ** Strong projectability
  The corresponding lemmas for [RT_Call] do not hold, and indeed projectability
  is not preserved by reductions, so we need a stronger notion. *)

Fixpoint str_proj D (C:Choreography Sig) (r:Pid) : Prop :=
match C with
| eta @ a;; C' => str_proj D C' r
| If p ?? b Then C1 Else C2 =>
     str_proj D C1 r /\ str_proj D C2 r /\ projectable_B D C r
| RT_Call X ps C =>
     str_proj D C r /\ (forall p, In p ps ->
     forall B B', [[D,snd (D X) | p]] == B -> [[D,C | p]] == B' -> B [>>] B')
| _  => True
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

Definition str_proj_P P := Program_WF P /\ projectable_D (Procedures P) /\
  forall r, str_proj (Procedures P) (Main P) r.

Lemma str_proj_P_Program_WF : forall P, str_proj_P P -> Program_WF P.
Proof. intros. apply H. Qed.

Lemma str_proj_P_str_proj : forall P, str_proj_P P ->
  forall r, str_proj (Procedures P) (Main P) r.
Proof. intros. apply H. Qed.

Lemma str_proj_P_str_proj' : forall P, str_proj_P P ->
  forall r X, str_proj (Procedures P) (CC.Procs P X) r.
Proof.
intros. elim (In_dec (@eq_dec Pid) r (Vars P X)).
apply initial_str_proj; apply H.
intros. apply initial_str_proj'. apply H.
intro; apply b, H; auto.
Qed.

Lemma str_proj_P_projectable_P : forall P,
  str_proj_P P -> projectable_P P.
Proof.
repeat split.
+ red. rewrite Forall_forall; intros.
  apply str_proj_C, H.
+ apply H.
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

Lemma str_proj_P_inv_Eta : forall D eta C a,
  str_proj_P (D,eta@a;;C) -> str_proj_P (D,C).
Proof.
split. 2: split. 2,3: apply H.
eapply Program_WF_eta; apply H.
Qed.

Lemma str_proj_P_inv_Then : forall D p b C1 C2,
  str_proj_P (D,If p ?? b Then C1 Else C2) -> str_proj_P (D,C1).
Proof.
split. 2: split. 2,3: apply H.
eapply Program_WF_Then; apply H.
Qed.

Lemma str_proj_P_inv_Else : forall D p b C1 C2,
  str_proj_P (D,If p ?? b Then C1 Else C2) -> str_proj_P (D,C2).
Proof.
split. 2: split. 2,3: apply H.
eapply Program_WF_Else; apply H.
Qed.

Lemma str_proj_P_inv_RT_Call : forall D ps X C,
  str_proj_P (D,RT_Call ps X C) -> str_proj_P (D,C).
Proof.
split. 2: split. 2,3: apply H.
eapply Program_WF_Call; apply H.
Qed.

(** Miscellaneous. *)

Lemma CCC_To_Call_ann : forall D C s X p C' s', consistent Sig (Names D) C ->
  <<C,s>> --[RL_Call X p,D]--> <<C',s'>> -> In p (fst (D X)).
Proof.
induction C; intros; inversion H0; eauto; inversion H; eauto.
all: rewrite <- H4; specialize (H12 _ H11); tauto.
Qed.

Lemma Program_WF_str_proj : forall P, Program_WF P -> projectable_P P ->
  forall X p, str_proj (Procedures P) (CC.Procs P X) p.
Proof.
intros. induction H as (HC,(HVars,HX)).
specialize (HX X); destroy HX.
elim (In_dec (@eq_dec Pid) p (Vars P X)); intros.
+ apply initial_str_proj with (Vars P X); auto.
  apply H0.
+ apply initial_str_proj'; auto.
Qed.

Lemma epp_EmptyNet' : forall P HP N, Program_WF P ->
  N (==) nnil -> N (>>) Net (epp P HP) -> Main P = CC.End.
Proof.
intros. rename H1 into HN, H0 into HN', H into HWF.
induction P as (D,C).
inversion HP as (HC,HD).
generalize (epp_C_char _ _ HP HC); intro.
destruct C; auto. induction e.
1,2: rename t0 into p. 3: rename t into p.
1,2,3: specialize (HN p); rewrite HN', H in HN; simpl in HN.
- rewrite epp_C_Com_p with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC) in HN.
  inversion HN; auto.
  unfold CCP_pn; simpl. sup. simpl; auto.
- rewrite epp_C_Sel_p with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC) in HN.
  inversion HN; auto.
  unfold CCP_pn; simpl. sup. simpl; auto.
- rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC)
        (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC) in HN.
  inversion HN; auto.
  unfold CCP_pn; simpl. repeat sup. simpl; auto.
- generalize (Program_WF_Vars _ _ HWF t); intros.
  case_eq (Vars (D,CC.Call t) t); intro. tauto.
  rename t0 into p. intros. clear H0.
  specialize (HN p). rewrite HN', H, epp_C_Call in HN.
  + inversion HN; auto.
  + unfold CCP_pn. simpl.
    rewrite H1; simpl; auto.
  + unfold Vars in H1. simpl in H1.
    rewrite H1; simpl; auto.
- apply Program_WF_Main, Choreography_WF_no_empty_ann in HWF.
  induction HWF as [H2 H2'].
  case_eq l; intro. tauto.
  rename t0 into p. intros.
  specialize (HN p). rewrite HN', H, epp_C_RT_Call in HN.
  3: rewrite H0; simpl; auto.
  inversion HN; auto.
  unfold CCP_pn. simpl. sup. rewrite H0; simpl; auto.
Qed.

Lemma epp_EmptyNet : forall P HP, Program_WF P ->
  nnil (>>) Net (epp P HP) -> Main P = CC.End.
Proof.
intros.
apply epp_EmptyNet' with (N:=nnil) (HP:=HP); auto.
apply Network_eq_refl.
Qed.

End Projectability.

(** ** Characterization of projection *)

Section ProjectionChar.

Lemma CCC_To_bproj_Com_p : forall D C s C' s' p q v x,
  str_proj D C p -> <<C,s>> --[RL_Com p v q x,D]--> <<C',s'>> ->
  exists e a Bp, [[D,C | p]] == Send Sig' q e a Bp /\ [[D,C' | p]] == Bp
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

Lemma CCC_To_bproj_Call_p : forall D C s C' s' p X,
  str_proj D C p ->
  (forall Y, str_proj D (snd (D Y)) p) ->
  (forall Y, CCC_pn (snd (D Y)) (Names D) [C] fst (D Y)) ->
  <<C,s>> --[RL_Call X p,D]--> <<C',s'>> ->
  [[D,C | p]] == Call Sig' (X,p) /\
  exists B B', [[D,snd (D X) | p]] == B /\ [[D,C' | p]] == B' /\ B [>>] B'.
Proof.
intros.
rename H into HC, H0 into HD, H2 into H, H1 into Hnames.
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
  induction (str_proj_C _ _ _ (HD X)) as [B HB].
  exists B, B; repeat split; auto.
  apply MB_refl; auto.
+ simpl; split. constructor; auto.
  induction (str_proj_C _ _ _ (HD X)) as [B HB].
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
  induction (str_proj_C _ _ _ (HD X)) as [B HB].
  inversion_clear HC.
  induction (str_proj_C _ _ _ H11) as [B' HB'].
  exists B, B'; repeat split; auto.
  constructor; auto. intro. apply set_remove'_2 in H13; auto.
  apply (H12 p); auto. rewrite H3; auto.
+ simpl; split. constructor; auto.
  rewrite <- H5, <- H1, H3 in *; clear X0 H0 l H1 C0 H2 s0 H4 p0 H6 C' H5 s'0 H7 t H3.
  induction (str_proj_C _ _ _ (HD X)) as [B HB].
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

Lemma CCC_To_bproj_disjoint : forall D C s tl C' s' p,
  (forall X, CCC_pn (snd (D X)) (Names D) [C] fst (D X)) ->
  str_proj D C p ->
  disjoint_p_rl p tl -> <<C,s>> --[tl,D]--> <<C',s'>> ->
  exists B B', [[D,C | p]] == B /\ [[D,C' | p]] == B' /\ B [>>] B'.
Proof.
do 6 intro. intros r HD.
intros. induction tl.
- destroy H0.
  induction (CCC_To_bproj_Com_r D C s C' s' p q v x r) as [B [HB1 HB2] ]; auto.
  exists B, B; repeat split; auto.
  apply MB_refl.
- destroy H0.
  induction (CCC_To_bproj_Sel_r D C s C' s' p q l r) as [B [HB1 HB2] ]; auto.
  exists B, B; repeat split; auto.
  apply MB_refl.
- apply (CCC_To_bproj_Cond_r D C s C' s' p r); auto.
- induction (CCC_To_bproj_Call_r D C s C' s' p X r) as [B [HB1 HB2] ]; auto.
  exists B, B; repeat split; auto.
  apply MB_refl.
Qed.

End ProjectionChar.

(** Projectability of well-formed programs is preserved by transitions. *)

Section ProjectionLemmas.

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

Lemma CCC_To_projectable_C_Call : forall D ps C s C' s' X p,
  (forall p, In p ps -> str_proj D C p) ->
  (forall p Y, In p ps -> str_proj D (snd (D Y)) p) ->
  (forall Y, CCC_pn (snd (D Y)) (Names D) [C] fst (D Y)) ->
  <<C,s>> --[RL_Call X p,D]--> <<C',s'>> -> projectable_C D C' ps.
Proof.
intros D ps C s C' s' X p H H' H'' HX.
red. rewrite Forall_forall; intros r Hr.
generalize (str_proj_C _ _ _ (H _ Hr)); intro.
eq_elim p r Hpr.
+ elim (CCC_To_bproj_Call_p D C s C' s' p X); auto.
  intros. induction H2 as [B [B' [HB [HB' H3] ] ] ].
  eexists; eauto.
+ elim (CCC_To_bproj_Call_r D C s C' s' p X r); auto.
  intros B [HB HB']. eexists; eauto.
Qed.

Lemma CCC_To_projectable_C : forall D ps C s C' s' t,
  (forall p, In p ps -> str_proj D C p) ->
  (forall p Y, In p ps -> str_proj D (snd (D Y)) p) ->
  (forall Y, CCC_pn (snd (D Y)) (Names D) [C] fst (D Y)) ->
  <<C,s>> --[t,D]--> <<C',s'>> -> projectable_C D C' ps.
Proof.
induction t; intros.
eapply CCC_To_projectable_C_Com; eauto.
eapply CCC_To_projectable_C_Sel; eauto.
eapply CCC_To_projectable_C_Cond; eauto.
eapply CCC_To_projectable_C_Call; eauto.
Qed.

Lemma CCP_To_projectable_P : forall P, projectable_P P -> str_proj_P P ->
  forall s tl P' s', (P,s) --[tl]--> (P',s') -> projectable_P P'.
Proof.
intros. rename H0 into HSP, H into HP, H1 into H2.
induction P as (D,C). induction P' as (D', C').
generalize (CCP_To_Defs_stable _ D D' C C' tl s s' H2); intro.
rewrite <- H in *; clear D' H.
inversion H2. rewrite <- H0 in H2. clear s'0 H6 C'0 H5 tl H0 s0 H3 C0 H1 D0 H.
rename H4 into Ht.
induction HP as (HC,HD).
split; auto.
simpl in *.
apply CCC_To_projectable_C with C s s' t; auto.
- intros; apply HSP.
- intro r; intros.
  elim (In_dec (@eq_dec Pid) r (fst (D Y))); intro.
  * apply initial_str_proj with (fst (D Y)); auto.
    apply HSP.
  * apply initial_str_proj'; auto.
    apply HSP.
    intro. apply b. apply HSP; auto.
- simpl. apply HSP.
Qed.

(** Strong projectability of well-formed programs is also preserved by reductions:
  this is needed for chaining applications of the EPP theorem. *)

Lemma CCC_To_str_proj_Com : forall D C s C' s' p v q x,
  (forall r, str_proj D C r) -> <<C,s>> --[RL_Com p v q x,D]--> <<C',s'>> ->
  forall r, str_proj D C' r.
Proof.
intros.
rename H into Hr, H0 into H.
revert C C' H r Hr.
induction C; intros; inversion H.
+ rewrite <- H4; eauto.
+ simpl; apply IHC; auto.
+ induction (Hr r) as (HC1,(HC2,Hr')).
  assert (str_proj D C1' r). eapply IHC1; eauto. apply Hr.
  assert (str_proj D C2' r). eapply IHC2; eauto. apply Hr.
  repeat split; auto.
  destroy H8.
  simpl. case (eq_dec t r); intro.
  2: elim ((@eq_dec Pid) p r); intro Hpr.
  3: elim ((@eq_dec Pid) q r); intro Hqr.
  - apply str_proj_C in H11.
    apply str_proj_C in H12.
    induction H11 as [B1 HB1]. induction H12 as [B2 HB2].
    induction Hr' as [B HB].
    rewrite e. exists (Cond Sig' t0 B1 B2); constructor; auto.
  - rewrite Hpr in *; clear p Hpr.
    elim (CCC_To_bproj_Com_p _ _ _ _ _ _ _ _ _ HC1 H9); intros.
    induction H14 as [a [B1 [HB1 [HB1' HB1''] ] ] ]. clear HB1''.
    elim (CCC_To_bproj_Com_p _ _ _ _ _ _ _ _ _ HC2 H10); intros.
    induction H14 as [a' [B2 [HB2 [HB2' HB2''] ] ] ]. clear HB2''.
    induction Hr' as [B HB]. inversion HB. tauto.
    rewrite (bproj_unique _ _ _ _ _ H19 HB1) in H24.
    rewrite (bproj_unique _ _ _ _ _ H22 HB2) in H24.
    inversion_clear H24.
    exists B7. apply bproj_Cond' with B1 B2; auto.
  - rewrite Hqr in *; clear q Hqr.
    elim (CCC_To_bproj_Com_q _ _ _ _ _ _ _ _ _ HC1 H9); auto; intros.
    induction H14 as [B1 [H1' H1''] ].
    elim (CCC_To_bproj_Com_q _ _ _ _ _ _ _ _ _ HC2 H10); auto; intros.
    induction H14 as [B2 [H2' H2''] ].
    induction Hr' as [B HB]. inversion HB. tauto.
    rewrite (bproj_unique _ _ _ _ _ H19 H1') in H24.
    rewrite (bproj_unique _ _ _ _ _ H22 H2') in H24.
    inversion_clear H24.
    exists B7. apply bproj_Cond' with B1 B2; auto.
  - induction (CCC_To_bproj_Com_r _ _ _ _ _ _ _ _ _ _ HC1 H9) as [Bt [Ht1 Ht2] ]; auto.
    induction (CCC_To_bproj_Com_r _ _ _ _ _ _ _ _ _ _ HC2 H10) as [Be [He1 He2] ]; auto.
    induction Hr' as [B HB]. inversion HB. tauto.
    exists B. apply bproj_Cond' with Bt Be; auto.
    rewrite (bproj_unique _ _ _ _ _ Ht1 H19).
    rewrite (bproj_unique _ _ _ _ _ He1 H22).
    auto.
+ rewrite <- H0, <- H1, <- H5 in *. clear t H0 l H1 C' H5 t0 H4 s0 H2 C0 H3 s'0 H6.
  split. apply IHC; auto. apply Hr.
  intros r' Hr'. elim (Hr r'); intros.
  specialize (H1 r' Hr').
  apply disjoint_ps_Com in H7.
  assert (p <> r') as Hpr'.
  1: specialize (H7 p); simpl in H7. intro. rewrite H4 in H7; tauto.
  assert (q <> r') as Hqr'.
  1: specialize (H7 q); simpl in H7. intro. rewrite H4 in H7; tauto.
  clear H7.
  elim (CCC_To_bproj_Com_r D C s C'0 s' p q v x r'); intros; auto.
  inversion_clear H4.
  rewrite (bproj_unique _ _ _ _ _ H3 H6) in *; auto.
Qed.

Lemma CCC_To_str_proj_Sel : forall D C s C' s' p q l,
  (forall r, str_proj D C r) -> forall r,
  <<C,s>> --[RL_Sel p q l,D]--> <<C',s'>> -> str_proj D C' r.
Proof.
intros.
rename H into Hr, H0 into H.
revert C C' H r Hr.
induction C; intros; inversion H.
+ rewrite <- H4; eauto.
+ simpl; apply IHC; auto.
+ induction (Hr r) as (HC1,(HC2,Hr')).
  assert (str_proj D C1' r). eapply IHC1; eauto. apply Hr.
  assert (str_proj D C2' r). eapply IHC2; eauto. apply Hr.
  repeat split; auto.
  destroy H8.
  simpl. case (eq_dec t r); intro.
  2: elim ((@eq_dec Pid) p r); intro Hpr.
  3: elim ((@eq_dec Pid) q r); intro Hqr.
  3: induction l.
  - apply str_proj_C in H11.
    apply str_proj_C in H12.
    induction H11 as [B1 HB1]. induction H12 as [B2 HB2].
    induction Hr' as [B HB].
    rewrite e. exists (Cond Sig' t0 B1 B2); constructor; auto.
  - rewrite Hpr in *; clear p Hpr.
    elim (CCC_To_bproj_Sel_p _ _ _ _ _ _ _ _ HC1 H9).
    intros a (B1,(HB1,HB1')).
    elim (CCC_To_bproj_Sel_p _ _ _ _ _ _ _ _ HC2 H10).
    intros a' (B2,(HB2,HB2')).
    induction Hr' as [B HB]. inversion HB. tauto.
    rewrite (bproj_unique _ _ _ _ _ H19 HB1) in H24.
    rewrite (bproj_unique _ _ _ _ _ H22 HB2) in H24.
    inversion_clear H24.
    exists B7. apply bproj_Cond' with B1 B2; auto.
  - rewrite Hqr in *; clear q Hqr.
    elim (CCC_To_bproj_Sel_ql _ _ _ _ _ _ _ HC1 H9); auto; intros.
    induction H14 as [B1 [H1' H1''] ].
    elim (CCC_To_bproj_Sel_ql _ _ _ _ _ _ _ HC2 H10); auto; intros.
    induction H14 as [B2 [H2' H2''] ].
    induction Hr' as [B HB]. inversion HB. tauto.
    rewrite (bproj_unique _ _ _ _ _ H19 H1') in H24.
    rewrite (bproj_unique _ _ _ _ _ H22 H2') in H24.
    inversion_clear H24.
    exists bL. apply bproj_Cond' with B1 B2; auto.
  - rewrite Hqr in *; clear q Hqr.
    elim (CCC_To_bproj_Sel_qr _ _ _ _ _ _ _ HC1 H9); auto; intros.
    induction H14 as [B1 [H1' H1''] ].
    elim (CCC_To_bproj_Sel_qr _ _ _ _ _ _ _ HC2 H10); auto; intros.
    induction H14 as [B2 [H2' H2''] ].
    induction Hr' as [B HB]. inversion HB. tauto.
    rewrite (bproj_unique _ _ _ _ _ H19 H1') in H24.
    rewrite (bproj_unique _ _ _ _ _ H22 H2') in H24.
    inversion_clear H24.
    exists bR. apply bproj_Cond' with B1 B2; auto.
  - induction (CCC_To_bproj_Sel_r _ _ _ _ _ _ _ _ _ HC1 H9) as [Bt [Ht1 Ht2] ]; auto.
    induction (CCC_To_bproj_Sel_r _ _ _ _ _ _ _ _ _ HC2 H10) as [Be [He1 He2] ]; auto.
    induction Hr' as [B HB]. inversion HB. tauto.
    exists B. apply bproj_Cond' with Bt Be; auto.
    rewrite (bproj_unique _ _ _ _ _ Ht1 H19).
    rewrite (bproj_unique _ _ _ _ _ He1 H22).
    auto.
+ rewrite <- H0, <- H1, <- H5 in *. clear t H0 l0 H1 C' H5 t0 H4 s0 H2 C0 H3 s'0 H6.
  split. apply IHC; auto. apply Hr.
  intros r' Hr'. elim (Hr r'); intros.
  specialize (H1 r' Hr').
  apply disjoint_ps_Sel in H7.
  assert (p <> r') as Hpr'.
  1: specialize (H7 p); simpl in H7. intro. rewrite H4 in H7; tauto.
  assert (q <> r') as Hqr'.
  1: specialize (H7 q); simpl in H7. intro. rewrite H4 in H7; tauto.
  clear H7.
  elim (CCC_To_bproj_Sel_r D C s C'0 s' p q l r'); intros; auto.
  inversion_clear H4.
  rewrite (bproj_unique _ _ _ _ _ H3 H6) in *; auto.
Qed.

Lemma CCC_To_str_proj_Cond : forall D C s C' s' p,
  (forall r, str_proj D C r) -> forall r,
  <<C,s>> --[RL_Cond p,D]--> <<C',s'>> -> str_proj D C' r.
Proof.
intros.
rename H into Hr, H0 into H.
revert C C' H r Hr.
induction C; intros; inversion H.
+ simpl; apply IHC; auto.
+ rewrite <- H5; eapply str_proj_inv_Then; eauto.
+ rewrite <- H5; eapply str_proj_inv_Else; eauto.
+ rename p0 into q.
  rewrite <- H1, <- H0 in *.
  clear t H0 t0 H1 C0 H2 C3 H4 s0 H3 t1 H5 C' H6 H s'0 H7.
  induction (Hr r) as (HC1,(HC2,Hr')).
  assert (str_proj D C1' r). eapply IHC1; eauto. apply Hr.
  assert (str_proj D C2' r). eapply IHC2; eauto. apply Hr.
  repeat split; auto.
  eq_elim q r Hqr. 2: eq_elim p r Hpr.
  - induction Hr' as [B HB]. inversion_clear HB. 2: tauto.
    apply str_proj_C in H, H0, HC1, HC2.
    induction H as [B1' HC1']. induction H0 as [B2' HC2'].
    exists (Cond Sig' b B1' B2'); constructor; auto.
  - induction (CCC_To_bproj_Cond_p _ _ _ _ _ _ HC1 H9) as [b1 [B1t [B1e [HC1' [HB1t HB1e] ] ] ] ].
    induction (CCC_To_bproj_Cond_p _ _ _ _ _ _ HC2 H10) as [b2 [B2t [B2e [HC2' [HB2t HB2e] ] ] ] ].
    induction Hr' as [B HB]. inversion HB. tauto.
    rewrite (bproj_unique _ _ _ _ _ H6 HC1') in H14.
    rewrite (bproj_unique _ _ _ _ _ H12 HC2') in H14.
    inversion H14.
    rewrite <- H19 in *; clear b2 b3 H15 H19.
    case_eq (eval_on_state BEv b1 s p); intro Hb'.
    exists Bt. apply bproj_Cond' with B1t B2t; auto.
    exists Be. apply bproj_Cond' with B1e B2e; auto.
  - induction (CCC_To_bproj_Cond_r _ _ _ _ _ _ _ HC1 H9 Hpr) as [B1 [B1' [HB1 [HB1' H'] ] ] ].
    induction (CCC_To_bproj_Cond_r _ _ _ _ _ _ _ HC2 H10 Hpr) as [B2 [B2' [HB2 [HB2' H''] ] ] ].
    induction Hr' as [B HB]. revert Hqr. inversion_clear HB. tauto.
    rewrite (bproj_unique _ _ _ _ _ H1 HB1) in *; clear B0 H1.
    rewrite (bproj_unique _ _ _ _ _ H2 HB2) in *; clear B3 H2.
    induction (MB_yields_merge _ _ _ _ _ _ H' H'' H4) as [B' [HB' HB''] ].
    exists B'. apply bproj_Cond' with B1' B2'; auto.
+ rewrite <- H0, <- H1 in *. clear t H0 l H1 C0 H3 s0 H2 C' H5 s'0 H6 H.
  repeat split; auto.
  apply IHC; auto. apply Hr.
  destroy H7; intros.
  induction (CCC_To_bproj_Cond_r D C s C'0 s' p p0) as [B1 [B2 [HB1 [HB2 H'] ] ] ]; auto.
  rewrite (bproj_unique _ _ _ _ _ H1 HB2) in *. clear B' H1.
  apply MB_trans with B1; auto.
  elim (Hr r); auto. intros. specialize (H2 p0); auto.
  apply Hr.
  apply disjoint_ps_Cond in H7. intro.
  rewrite H2 in H7; auto.
Qed.

Lemma CCC_To_str_proj_Call : forall D C s C' s' p X,
  (forall r, str_proj D C r) ->
  (forall r Y, str_proj D (snd (D Y)) r) ->
  (forall Y, CCC_pn (snd (D Y)) (Names D) [C] fst (D Y)) ->
  forall r, <<C,s>> --[RL_Call X p,D]--> <<C',s'>> -> str_proj D C' r.
Proof.
intros.
rename H into Hr, H1 into Hnames, H0 into HD, H2 into H.
revert C r Hr C' H.
induction C; intros; inversion H.
+ simpl; apply IHC; auto.
+ rename p0 into q.
  rewrite <- H1, <- H0 in *.
  clear t H0 t0 H1 C0 H2 C3 H4 s0 H3 t1 H5 C' H6 H s'0 H7.
  induction (Hr r) as (HC1,(HC2,Hr')).
  assert (str_proj D C1' r). eapply IHC1; eauto. apply Hr.
  assert (str_proj D C2' r). eapply IHC2; eauto. apply Hr.
  repeat split; auto.
  eq_elim q r Hqr. 2: eq_elim p r Hpr.
  - induction Hr' as [B HB]. inversion_clear HB. 2: tauto.
    apply str_proj_C in H, H0, HC1, HC2.
    induction H as [B1' HC1']. induction H0 as [B2' HC2'].
    exists (Cond Sig' b B1' B2'); constructor; auto.
  - induction (CCC_To_bproj_Call_p _ _ _ _ _ _ _ HC1 (fun Y => HD p Y) Hnames H9)
      as [HC1' [B1 [B1' [HB1 [HB1' HB1''] ] ] ] ].
    induction (CCC_To_bproj_Call_p _ _ _ _ _ _ _ HC2 (fun Y => HD p Y) Hnames H10)
      as [HC2' [B2 [B2' [HB2 [HB2' HB2''] ] ] ] ].
    induction Hr' as [B HB]. inversion HB. tauto.
    rewrite (bproj_unique _ _ _ _ _ HB2 HB1) in *; clear B2 HB2.
    elim (MB_has_lub _ _ _ _ HB1'' HB2'').
    intros B' [HB' HB''].
    eexists. apply bproj_Cond' with B1' B2'; eauto.
  - induction (Hr r) as [H01 [H02 H0'] ]; auto.
    induction (CCC_To_bproj_Call_r _ _ _ _ _ _ _ _ H01 Hnames H9) as [B1 [HB1 HB1'] ].
    induction (CCC_To_bproj_Call_r _ _ _ _ _ _ _ _ H02 Hnames H10) as [B2 [HB2 HB2'] ].
    all: auto.
    induction H0' as [B HB]. inversion HB. tauto.
    rewrite (bproj_unique _ _ _ _ _ H6 HB1) in *; clear B0 H6.
    rewrite (bproj_unique _ _ _ _ _ H12 HB2) in *; clear B3 H12.
    eexists; apply bproj_Cond' with B1 B2; eauto.
+ auto.
+ repeat split; intros; auto.
  specialize (HD p1 X); intros.
  apply str_proj_C in HD; auto.
  apply MB_refl'. eapply bproj_unique; eauto.
+ repeat split; intros.
  eapply IHC; eauto. apply Hr.
  apply disjoint_ps_rl_In with (p:=p0) in H7; auto.
  intros.
  elim (CCC_To_bproj_Call_r D C s C'0 s' p X p0); auto.
  intros B'' [HB''1 HB''2].
  rewrite (bproj_unique _ _ _ _ _ H11 HB''2); auto.
  induction (Hr r). eapply H13; eauto.
  apply Hr.
+ rewrite H3, <- H1 in *; clear t H3 l H1.
  elim (Hr r); auto; intros.
  split; auto; intros.
  assert (In p1 ps). eapply set_remove'_1; eauto.
  specialize (H3 p1 H14); auto.
+ rewrite <- H5. apply Hr; auto.
Qed.

Lemma CCC_To_str_proj : forall D C s C' s' t,
  (forall p, str_proj D C p) ->
  (forall p Y, str_proj D (snd (D Y)) p) ->
  (forall Y, CCC_pn (snd (D Y)) (Names D) [C] fst (D Y)) ->
  <<C,s>> --[t,D]--> <<C',s'>> -> forall p, str_proj D C' p.
Proof.
induction t; intros.
+ eapply CCC_To_str_proj_Com; eauto.
+ eapply CCC_To_str_proj_Sel; eauto.
+ eapply CCC_To_str_proj_Cond; eauto.
+ eapply CCC_To_str_proj_Call; eauto.
Qed.

Lemma CCP_To_str_proj : forall P, str_proj_P P ->
  forall s tl P' s', (P,s) --[tl]--> (P',s') -> str_proj_P P'.
Proof.
intros. rename H into Hsp, H0 into H2.
induction P as (D,C). induction P' as (D', C').
generalize (CCP_To_Defs_stable _ D D' C C' tl s s' H2); intro.
rewrite <- H in *; clear D' H.
inversion H2. rewrite <- H1 in H2. clear s'0 H6 C'0 H5 tl H0 s0 H3 C0 H1 D0 H H2.
rename H4 into Ht.
split. 2: split. 3: eapply CCC_To_str_proj; eauto.
all: try (apply Hsp).
+ eapply CCP_To_Program_WF. apply Hsp.
  apply CCP_Base; eauto.
+ intros.
  elim (In_dec (@eq_dec Pid) p (fst (D Y))).
  apply initial_str_proj. apply Hsp. apply Hsp.
  intro; apply initial_str_proj'. apply Hsp.
  intro; apply b, Hsp; auto.
Qed.

Lemma CCP_ToStar_str_proj : forall P, str_proj_P P ->
  forall s tl P' s', (P,s) --[tl]-->* (P',s') -> str_proj_P P'.
Proof.
intros. revert P H s P' s' H0.
induction tl; intros; inversion H0.
+ rewrite <- H2; auto.
+ induction c2 as (P'',s'').
  apply IHtl with P'' s'' s'; auto.
  apply CCP_To_str_proj in H4; auto.
Qed.

Lemma CCP_ToStar_projectable: forall P, str_proj_P P ->
  forall s tl P' s', (P,s) --[tl]-->* (P',s') -> projectable_P P'.
Proof.
intros.
apply str_proj_P_projectable_P.
eapply CCP_ToStar_str_proj; eauto.
Qed.

End ProjectionLemmas.

End EndPointProjection.

Arguments bproj [Sig].
Arguments projectable_B [Sig].
Arguments projectable_C [Sig].
Arguments projectable_D [Sig].
Arguments projectable_P [Sig].
Arguments epp_C [Sig].
Arguments epp_D [Sig].
Arguments epp [Sig].
Arguments str_proj [Sig].
Arguments str_proj_P [Sig].

Notation "[[ D , C | p ]] == B" := (bproj D C p B) (at level 20).

Ltac contr_aux H := red in H; rewrite Forall_forall in H; auto.
Ltac contr H := intros; exfalso; contr_aux H.
Ltac contr2 H H' := exfalso; specialize (H H'); contr_aux H.
