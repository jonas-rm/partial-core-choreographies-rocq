Require Export Basic.
Require Export Common.
Require Export MC.
Require Import Sumbool.

Require Export Kleene.
Require Export Implementation.

Module Export MC_Nat := Implementation.MC_Nat.

Notation "A '&&&' B" := (sumbool_and _ _ _ _ A B).

(** MOVE ME *)

(** List of recursion variables up to a given bound. *)
Fixpoint RecVarList n : list RecVar :=
match n with
| 0 => (0::List.nil)%list
| S m => (n::RecVarList m)
end.

Lemma RecVarList_In : forall m n, m <= n -> List.In m (RecVarList n).
Proof.
induction n; simpl; auto with arith.
intros.
inversion H; auto.
Qed.

Lemma In_RecVarList : forall m n, List.In m (RecVarList n) -> m <= n.
Proof.
induction n; simpl; intros.
+ inversion_clear H; inversion H0; auto.
+ inversion H; auto. rewrite H0; auto.
Qed.

Lemma RecVarList_incl : forall m n, m <= n ->
  (forall X, List.In X (RecVarList m) -> List.In X (RecVarList n)).
Proof.
intros.
apply RecVarList_In.
transitivity m; auto.
apply In_RecVarList; auto.
Qed.

Open Scope MC_scope.


(** Choreography implementations are well-formed. *)
Lemma Implementation_Main_WF : forall {n} (f:PRFunction n) ps q,
  Choreography_WF (Main (Implementation f ps q)).
Proof. intros. simpl. split; simpl; auto. Qed.

Lemma Implementation_Main_within_Xs : forall {n} (f:PRFunction n) ps q Xs,
  List.In 0 Xs -> within_Xs Xs (Main (Implementation f ps q)).
Proof. auto. Qed.

Lemma seq_compose_WF : forall {k m} (fs:t (PRFunction m) k) d Hd ps n q X Implement Y,
  (forall p, In p ps -> p < n) -> n + k <= q ->
  (forall k f ps' m' n' H X Y, (forall p, In p ps' -> p < m') -> m' < n' -> Choreography_WF (Implement k f H ps' m' n' X Y)) ->
  Choreography_WF (seq_compose fs d Hd ps n q X Implement Y).
Proof.
induction k; intro.
+ refine (@case0 _ _ _ ); simpl; intros.
  split; simpl; auto.
+ intro; revert k fs IHk. refine (@caseS _ _ _); simpl; intros.
  elim Nat.ltb; auto.
  - assert (n0 < n0 + S n). rewrite <- plus_Snm_nSm; auto with arith.
    apply H1; auto.
    intros. apply lt_le_trans with (n0 + S n); auto.
  - apply IHk; auto. intros; transitivity n0; auto.
    rewrite plus_Snm_nSm. transitivity q; auto with arith.
Qed.

Lemma Implementation_aux_WF : forall m (f:PRFunction m) d Hd ps q n X Y,
  ~In q ps -> (forall p, In p ps -> p < n) -> q < n ->
  Choreography_WF (Implementation_aux f d Hd ps q n X Y).
Proof.
intros m f d; revert m f.
induction d. inversion Hd.
do 2 intro; case f; intros.
+ (* Zero *)
  simpl. unfold Pack1; simpl.
  elim RecVar_dec; repeat split; simpl; auto.
  intro; apply H. eapply nth_In; eauto.
+ (* Successor *)
  simpl. unfold Pack1; simpl.
  elim RecVar_dec; repeat split; simpl; auto.
  intro; apply H. eapply nth_In; eauto.
+ (* Projection *)
  simpl. unfold Pack1; simpl.
  elim RecVar_dec; repeat split; simpl; auto.
  intro; apply H. eapply nth_In; eauto.
+ (* Composition *)
  simpl. elim Nat.ltb.
  - apply seq_compose_WF; intros; auto.
    apply IHd; auto.
    intro. apply (lt_irrefl m'); auto.
    intros; transitivity m'; auto.
  - apply IHd.
    * intro. elim (seq_labels_lt _ _ _ H2); intros. apply (lt_irrefl n).
      apply le_lt_trans with q; auto.
    * intros. elim (seq_labels_lt _ _ _ H2); auto.
    * apply lt_le_trans with n; auto with arith.
+ (* Recursion *)
  assert (n+2 <> n). apply gt_neq; rewrite plus_comm; simpl; auto.
  assert (n+3 <> n). apply gt_neq; rewrite plus_comm; simpl; auto.
  assert (n+2 <> S n). apply gt_neq; rewrite plus_comm; simpl; auto.
  simpl. elim Nat.ltb. 2: elim RecVar_dec. 3: elim RecVar_dec.  4: elim RecVar_dec.
  - apply IHd; auto.
    * intro. elim (lt_irrefl n). apply H0, In_tail; auto.
    * transitivity n. apply H0, In_tail; auto. rewrite plus_comm; simpl; auto.
    * rewrite plus_comm; simpl; auto.
  - split; simpl; split; auto.
  - split; simpl; repeat split; auto.
    * apply lt_neq. transitivity n; auto. apply H0. apply nth_In with Fin.F1; auto.
    * apply gt_neq; auto.
  - split; simpl; repeat split; auto.
  - apply IHd; auto with arith.
    * intro. rewrite plus_comm in H5; simpl in H5.
      elim (In_elim H5); intros. elim (lt_irrefl (S n)). rewrite H6 at 2; auto.
      elim (In_elim H6); intros. elim (lt_irrefl n). rewrite H7 at 2; auto.
      apply (lt_irrefl n). transitivity (S (S n)); auto. apply H0, In_tail; auto.
    * intros. transitivity (n+2); auto with arith. rewrite plus_comm; simpl.
      elim (In_elim H5); intros. rewrite <- H6; auto.
      elim (In_elim H6); intros. rewrite <- H7; auto.
      transitivity n; auto. apply H0, In_tail; auto.
+ (* Minimization *)
  assert (n+1 <> n+2). apply lt_neq. rewrite plus_comm; rewrite (plus_comm n 2); auto.
  assert (n <> n+2). apply lt_neq. rewrite plus_comm; simpl; auto.
  simpl. elim RecVar_dec. 2: elim RecVar_dec.
  - split; simpl; split; auto.
  - split; simpl; repeat split; auto.
    apply gt_neq; red. rewrite plus_comm. transitivity n; auto.
  - assert (n < n+3). rewrite plus_comm; simpl; auto.
    apply IHd; auto.
    * intro. elim (shiftin_elim _ _ H5); intro. apply (lt_irrefl n). rewrite <- H6 at 2; auto. rewrite plus_comm; auto.
      apply (lt_irrefl n); auto.
    * intros; transitivity (S (S n)). 2: rewrite plus_comm; simpl; auto.
      elim (shiftin_elim _ _ H5); auto with arith. intro. rewrite <- H6, plus_comm; auto.
Qed.

Lemma seq_compose_initial : forall {k m} (fs:t (PRFunction m) k) d Hd ps n q X Implement Y,
  (forall k f ps' m' n' H X Y, initial (Implement k f H ps' m' n' X Y)) ->
  initial (seq_compose fs d Hd ps n q X Implement Y).
Proof.
induction k; intro.
+ refine (@case0 _ _ _ ); simpl; intros.
  split; simpl; auto.
+ intro; revert k fs IHk. refine (@caseS _ _ _); simpl; intros.
  elim Nat.ltb; auto.
Qed.

Lemma Implementation_aux_initial : forall m (f:PRFunction m) d Hd ps q n X Y,
  initial (Implementation_aux f d Hd ps q n X Y).
Proof.
intros m f d; revert m f.
induction d. inversion Hd.
do 2 intro; case f; intros; simpl;
  unfold Pack1; try (elim RecVar_dec; simpl; auto; fail);
  try elim Nat.ltb; try (apply seq_compose_initial); auto;
  repeat (elim RecVar_dec; simpl; auto).
Qed.

Lemma Implementation_Procs_Vars_not_nil : forall {n} (f:PRFunction n) ps q X,
  Vars (Implementation f ps q) X <> List.nil.
Proof.
intros. unfold Vars; simpl.
apply all_pids_not_nil.
Qed.

Lemma seq_compose_within_Xs : forall {k m} (fs:t (PRFunction m) k) d Hd ps n q X Implement Y,
  (forall k f ps' m' n' H X Y, within_Xs (RecVarList (X+Gamma f)) (Implement k f H ps' m' n' X Y)) ->
  within_Xs (RecVarList (X+vsum (map Gamma fs))) (seq_compose fs d Hd ps n q X Implement Y).
Proof.
induction k; intro.
+ refine (@case0 _ _ _ ); simpl; intros.
  split; simpl; auto.
+ intro; revert k fs IHk. refine (@caseS _ _ _); simpl; intros.
  elim Nat.ltb; auto.
  - apply within_Xs_incl with (RecVarList (X + Gamma h)); auto.
    apply RecVarList_incl; auto with arith.
  - eapply within_Xs_incl.
    2: apply IHk; auto.
    apply RecVarList_incl.
    rewrite plus_assoc; auto with arith.
Qed.

Lemma Implementation_aux_within_Xs : forall m (f:PRFunction m) d Hd ps q n X,
  forall Y, within_Xs (RecVarList (X+Gamma f)) (Implementation_aux f d Hd ps q n X Y).
Proof.
intros m f d; revert m f.
induction d. inversion Hd.
do 2 intro; case f; intros; simpl.
+ (* Zero *)
  simpl. unfold Pack1; simpl; intros.
  elim RecVar_dec; simpl; auto.
  apply RecVarList_In; rewrite plus_comm; auto with arith.
+ (* Successor *)
  simpl. unfold Pack1; simpl; intros.
  elim RecVar_dec; simpl; auto.
  apply RecVarList_In; rewrite plus_comm; auto with arith.
+ (* Projection *)
  simpl. unfold Pack1; simpl; intros.
  elim RecVar_dec; simpl; auto.
  apply RecVarList_In; rewrite plus_comm; auto with arith.
+ (* Composition *)
  elim Nat.ltb.
  - eapply within_Xs_incl.
    2: apply seq_compose_within_Xs; auto.
    apply RecVarList_incl. auto with arith.
  - apply within_Xs_incl with (RecVarList (X + vsum (map Gamma fs) + Gamma g)); auto.
    apply RecVarList_incl. rewrite (plus_comm (Gamma g)), plus_assoc; auto with arith.
+ (* Recursion *)
  elim Nat.ltb; [idtac | elim RecVar_dec; [idtac | elim RecVar_dec; [idtac | elim RecVar_dec]]]; simpl.
  - apply within_Xs_incl with (RecVarList (X + Gamma g)); auto.
    apply RecVarList_incl. auto with arith.
  - apply RecVarList_In.
    rewrite <- plus_assoc. apply plus_le_compat_l.
    rewrite <- plus_assoc. apply plus_le_compat_l.
    rewrite plus_comm; auto with arith.
  - split; apply RecVarList_In.
    do 2 rewrite (plus_assoc X); auto with arith.
    rewrite <- plus_assoc. apply plus_le_compat_l.
    rewrite <- plus_assoc. apply plus_le_compat_l.
    rewrite plus_comm; auto with arith.
  - apply RecVarList_In.
    rewrite <- plus_assoc. apply plus_le_compat_l.
    rewrite <- plus_assoc. apply plus_le_compat_l.
    rewrite plus_comm; auto with arith.
  - apply within_Xs_incl with (RecVarList (X + Gamma g + 2 + Gamma h)); auto.
    apply RecVarList_incl.
    do 2 rewrite <- plus_assoc. apply plus_le_compat_l.
    rewrite <- plus_assoc. apply plus_le_compat_l.
    rewrite plus_comm; auto with arith.
+ (* Minimization *)
  elim RecVar_dec; [idtac | elim RecVar_dec]; simpl.
  - apply RecVarList_In. apply plus_le_compat_l.
    rewrite plus_comm; auto with arith.
  - split; apply RecVarList_In.
    rewrite (plus_assoc X); auto with arith.
    apply plus_le_compat_l; auto with arith.
  - apply within_Xs_incl with (RecVarList (X + 1 + Gamma h)); auto.
    apply RecVarList_incl.
    rewrite <- plus_assoc. apply plus_le_compat_l.
    rewrite plus_comm; auto with arith.
Qed.

(*
Lemma Zero_Procs_WF : forall d Hd ps q n X Y,
  ~In q ps -> Choreography_WF (Implementation_aux Zero d Hd ps q n X Y).
Proof.
intros; induction d. inversion Hd.
simpl. unfold Pack1; simpl.
elim RecVar_dec; repeat split; simpl; auto.
intro; apply H. eapply nth_In; eauto.
Qed.

Lemma Zero_Procs_initial : forall d Hd ps q n X Y,
  initial (Implementation_aux Zero d Hd ps q n X Y).
Proof.
intros; induction d. inversion Hd.
simpl. unfold Pack1; simpl.
elim RecVar_dec; simpl; auto.
Qed.

Lemma Zero_Procs_within_Xs : forall d Hd ps q n X Y Xs,
  List.In X Xs -> List.In (S X) Xs ->
  within_Xs Xs (Implementation_aux Zero d Hd ps q n X Y).
Proof.
intros; induction d. inversion Hd.
simpl. unfold Pack1; simpl.
elim RecVar_dec; simpl; auto.
Qed.

Lemma Succ_Procs_WF : forall d Hd ps q n X Y,
  ~In q ps -> Choreography_WF (Implementation_aux Successor d Hd ps q n X Y).
Proof.
intros; induction d. inversion Hd.
simpl. unfold Pack1; simpl.
elim RecVar_dec; repeat split; simpl; auto.
intro; apply H. eapply nth_In; eauto.
Qed.

Lemma Succ_Procs_initial : forall d Hd ps q n X Y,
  initial (Implementation_aux Successor d Hd ps q n X Y).
Proof.
intros; induction d. inversion Hd.
simpl. unfold Pack1; simpl.
elim RecVar_dec; simpl; auto.
Qed.

Lemma Succ_Procs_within_Xs : forall d Hd ps q n X Y Xs,
  List.In X Xs -> List.In (S X) Xs ->
  within_Xs Xs (Implementation_aux Successor d Hd ps q n X Y).
Proof.
intros; induction d. inversion Hd.
simpl. unfold Pack1; simpl.
elim RecVar_dec; simpl; auto.
Qed.

Lemma Proj_Procs_WF : forall k m (Hp:k<m) d Hd ps q n X Y,
  ~In q ps -> Choreography_WF (Implementation_aux (Projection Hp) d Hd ps q n X Y).
Proof.
intros; induction d. inversion Hd.
simpl. unfold Pack1; simpl.
elim RecVar_dec; repeat split; simpl; auto.
intro; apply H. eapply nth_In; eauto.
Qed.

Lemma Proj_Procs_initial : forall k m (Hp:k<m) d Hd ps q n X Y,
  initial (Implementation_aux (Projection Hp) d Hd ps q n X Y).
Proof.
intros; induction d. inversion Hd.
simpl. unfold Pack1; simpl.
elim RecVar_dec; simpl; auto.
Qed.

Lemma Proj_Procs_within_Xs : forall k m (Hp:k<m) d Hd ps q n X Y Xs,
  List.In X Xs -> List.In (S X) Xs ->
  within_Xs Xs (Implementation_aux (Projection Hp) d Hd ps q n X Y).
Proof.
intros; induction d. inversion Hd.
simpl. unfold Pack1; simpl.
elim RecVar_dec; simpl; auto.
Qed.

Lemma Recursion_Procs_WF : forall m (f:PRFunction m) g d Hd ps q n X Y,
  ~In q ps -> Choreography_WF (Implementation_aux (Recursion f g) d Hd ps q n X Y).
Proof.
intros; induction d. inversion Hd.
simpl. elim Nat.ltb.
elim RecVar_dec; repeat split; simpl; auto.
intro; apply H. eapply nth_In; eauto.
Qed.
*)

Lemma Implements_WF : forall {n} (f:PRFunction n) ps q,
  ~In q ps -> MCP_WF (Implementation f ps q).
Proof.
intros.
exists (RecVarList (0+Gamma f)); split.
+ split. apply Implementation_Main_WF.
  split. apply Implementation_Main_within_Xs; apply RecVarList_In; auto with arith.
  split.
  1: { apply Implementation_aux_WF; intros; auto; apply le_n_S.
    2: apply Nat.le_max_l.
    transitivity (vmax ps). 2: apply Nat.le_max_r. apply vmax_In; auto.
  }
  split. apply Implementation_aux_initial.
  split. apply Implementation_Procs_Vars_not_nil.
  apply Implementation_aux_within_Xs; simpl; auto.
+ red.
  unfold Vars; simpl.
Admitted.

Lemma Implements'_WF : forall {n} (f:PRFunction n),
  MCP_WF (Implementation' f).
Proof.
intros; apply Implements_WF.
intro. elim (in_vec_k_to_n _ H); intros.
inversion H0.
Qed.

Lemma Implementation_aux_converges : forall {n} (f:PRFunction n) d Hd ps q i X Defs ns y,
  ~In q ps -> (forall p, In p ps -> p < i) -> q < i ->
  (forall Y, X <= Y < X + Gamma f -> fst (Defs Y) <> List.nil) ->
  (forall Y, X <= Y < X + Gamma f -> snd (Defs Y) = Implementation_aux f d Hd ps q i X Y) ->
  converges f ns y -> 
  forall (s:State), (forall H, s ps[@H] xx = ns[@H]) ->
  exists s' tl, s' q xx = y /\ (forall p, p < i -> p <> q -> s' p xx = s p xx) /\
  (Build_Program Defs (Call X),s) --[tl]-->* (Build_Program Defs (Call (X + Gamma f)),s').
Proof.
intros n f d; revert n f. induction d. inversion Hd.
intros n f; case f; intros; rename H into Hqps, H0 into Hps, H1 into Hqn, H2 into HDefs, H3 into HDefs', H4 into Hf, H5 into Hinput.
+ (* Zero *)
  assert (X <= X < X + Gamma Zero). split; auto; rewrite plus_comm; auto with arith.
  generalize (HDefs _ H), (HDefs' _ H).
  simpl; unfold Pack1; simpl.
  rewrite Rdec.eqb_refl. intros HX HX'.
  elim (Call_reduce _ _ s HX); intros tl Htl.
  rewrite HX' in Htl.
  set (s' := update s q xx 0).
  exists s', (tl ++ (L_Com ps[@Fin.F1] 0 q :: List.nil))%list.
  rewrite (converges_Zero _ _ Hf).
  split. apply update_read.
  split. intros; apply update_read'. auto.
  eapply MCT_Trans; eauto.
  replace (L_Com ps[@Fin.F1] 0 q) with (forget (R_Com ps[@Fin.F1] 0 q xx)); auto.
  econstructor; constructor. rewrite plus_comm; simpl. apply C_Com'.
+ (* Successor *)
  set (x := s ps[@Fin.F1] xx).
  assert (X <= X < X + Gamma Zero). split; auto; rewrite plus_comm; auto with arith.
  generalize (HDefs _ H), (HDefs' _ H).
  simpl; unfold Pack1; simpl.
  rewrite Rdec.eqb_refl. intros HX HX'.
  elim (Call_reduce _ _ s HX); intros tl Htl.
  rewrite HX' in Htl.
  set (s' := update s q xx (S x)).
  exists s', (tl ++ (L_Com ps[@Fin.F1] (S x) q :: List.nil))%list.
  rewrite (converges_Successor _ _ Hf).
  split. rewrite <- nth_hd, <- Hinput. apply update_read.
  split. intros; apply update_read'. auto.
  eapply MCT_Trans; eauto.
  replace (L_Com ps[@Fin.F1] (S x) q) with (forget (R_Com ps[@Fin.F1] (S x) q xx)); auto.
  econstructor; constructor. rewrite plus_comm; simpl. apply C_Com'.
+ (* Projection *)
  set (x := s ps[@Fin.of_nat_lt l] xx).
  assert (X <= X < X + Gamma Zero). split; auto; rewrite plus_comm; auto with arith.
  generalize (HDefs _ H), (HDefs' _ H).
  simpl; unfold Pack1; simpl.
  rewrite Rdec.eqb_refl. intros HX HX'.
  elim (Call_reduce _ _ s HX); intros tl Htl.
  rewrite HX' in Htl.
  set (s' := update s q xx x).
  exists s', (tl ++ (L_Com ps[@Fin.of_nat_lt l] x q :: List.nil))%list.
  rewrite (converges_Projection _ _ _ _ _ Hf).
  split. rewrite <- Hinput. apply update_read.
  split. intros; apply update_read'. auto.
  eapply MCT_Trans; eauto.
  replace (L_Com ps[@Fin.of_nat_lt l] x q) with (forget (R_Com ps[@Fin.of_nat_lt l] x q xx)); auto.
  econstructor; constructor. rewrite plus_comm; simpl. apply C_Com'.
+ (* Composition *)
  (* Here we start directly with the loop *)

+ (* Recursion *)
  set (Hd' := lt_S_n (Nat.max (depth g) (depth h)) d Hd).
  set (Hg := (max_lt_l _ _ _ Hd')).
  set (Hh := (max_lt_r _ _ _ Hd')).
  assert (forall H, ps[@H] < i) as Hpsi.
  1: { intros. apply Hps. eapply nth_In; auto. }
  (* Setting up for the base case, using the induction hypothesis on g *)
  (* Call X,s -> Call (X + Gamma g),sg sg(ps) = s(ps), sg(init) = f(s(tl ps)) *)
  assert (forall Y, X <= Y < X + Gamma g -> X <= Y < X + (Gamma g + Gamma h + 3)) as H'.
  1: {
    intros. inversion_clear H; split; simpl; auto.
    transitivity (X + Gamma g); auto.
    apply plus_lt_compat_l; auto with arith.
    apply le_lt_trans with (Gamma g + Gamma h); auto with arith.
    rewrite <- (plus_comm 3); simpl; auto.
  }
  assert (forall Y, X <= Y < X + Gamma g -> fst (Defs Y) <> List.nil) as HgDefs. eauto.
  assert (forall Y, X <= Y < X + Gamma g -> snd (Defs Y) = Implementation_aux g _ Hg (tl ps) i (i+3) X Y) as HgDefs'.
  1: {
    intros. elim H; intros. generalize (HDefs' _ (H' _ H)).
    rewrite Recursion_Procs_g; auto.
  }
  assert (~In i (tl ps)) as Hi.
  1: { intro. apply (lt_irrefl i). apply Hps. apply In_tail; auto. }
  assert (i < i+3) as Hi'. rewrite plus_comm; simpl; auto.
  assert (forall p, In p (tl ps) -> p < i+3) as Hpsg.
  1: { intros. transitivity i; auto. apply Hps, In_tail; auto. }
  elim (converges_Recursion_full _ _ _ _ Hf 0); auto with arith.
  intros g0 Hg0.
  assert (forall H, s (tl ps)[@H] xx = (tl ns)[@H]) as Hinput'.
  1: intro; repeat rewrite <- nth_tl; auto.
  elim (IHd _ _ Hg (tl ps) i (i+3) _ _ (tl ns) _ Hi Hpsg Hi' HgDefs HgDefs' Hg0 s Hinput'); intros.
  destroy H.
  rename x into sg, x0 into tlg, H0 into Hsg, H1 into Hsg', H into Htlg.
  clear Hi HgDefs HgDefs' H' Hpsg Hg.
  (* Call X + Gamma g,sg -> Call (X + Gamma g + 1),s' s'(ps) = s(ps), s'(S init) = 0, s'(init) = f(s(tl ps)) *)
  assert (X <= X + Gamma g < X + Gamma (Recursion g h)).
  1: {
    split; auto with arith.
    apply plus_lt_compat_l. simpl. rewrite <- (plus_comm 3).
    transitivity (2 + Gamma g); simpl; auto with arith.
  }
  elim (Call_reduce Defs (X + Gamma g) sg); auto. intros.
  rename x into tlg'.
  rewrite HDefs', Recursion_Procs_0 in H0; auto.
  generalize (C_Com' Defs (i+2) zero (S i) xx (Call (X + Gamma g + 1)) sg); intro.
  simpl in H1. generalize (MCP_To_intro _ _ _ _ _ _ H1).
  clear H1; simpl; intro.
  set (P := Build_Program Defs (Call (X + Gamma g + 1))).
  generalize (MCT_Trans _ _ _ _ _ Htlg (MCT_Trans _ _ _ _ _ H0 (MCT_Step _ _ _ _ _ H1 (MCT_Refl _)))).
  clear H0 H1; fold P; intro HP.
  set (t := (tlg ++ tlg' ++ L_Com (i+2) 0 (S i) :: List.nil)%list).
  set (s0 := update sg (S i) xx 0).
  fold t s0 in HP.
  assert (s0 i xx = g0) as Hs0i. rewrite <- Hsg. apply update_read'; auto.
  assert (s0 (S i) xx = 0) as Hs0Si. apply update_read.
  assert (forall H, s0 ps[@H] xx = ns[@H]) as Hs0.
  1: {
    intros. rewrite <- Hinput, <- Hsg'; auto.
    apply update_read'; auto.
    apply gt_neq; red; transitivity i; auto.
    transitivity i; auto.
    apply lt_neq; auto.
  }
  assert (forall p, p < i -> s0 p xx = s p xx) as Hs0'.
  1: {
    intros; unfold s0; rewrite update_read'.
    apply Hsg'; auto with arith. apply lt_neq; auto.
    apply gt_neq; red; transitivity i; auto.
  }
  clearbody t s0. clear sg Hsg Hsg' Htlg.
  (* Loop invariant *)
  assert (forall m, m <= hd ns -> exists t' s' y', (P,s0) --[ t' ]-->* (P,s')
    /\ converges (Recursion g h) (m::tl ns) y' /\ s' i xx = y' /\ s' (S i) xx = m /\ forall j, j < i -> s' j xx = s0 j xx).
  - induction m; intros.
    * exists List.nil, s0, g0; repeat split; auto. constructor.
    * elim IHm; auto with arith; clear IHm.
      intros tlI H'; destroy H'.
      rename x into sI, x0 into yI, H1 into HI.
      assert (X <= X + Gamma g + 1 < X + Gamma (Recursion g h)).
      1: { split; simpl; auto with arith.  repeat (rewrite <- plus_assoc; apply plus_lt_compat_l); auto with arith. }
      elim (Call_reduce Defs (X + Gamma g + 1) sI); intros; auto.
      rename x into tlU, H5 into HU.
      rewrite HDefs', Recursion_Procs_1 in HU; auto.
      unfold IfEq in HU.
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs ps[@Fin.F1] this (S i) yy (If (S i) ? compare Then Send i this q;; Call (X + Gamma g + Gamma h + 3) Else Call (X + Gamma g + 2)) sI)).
      simpl; intro.
      assert (beval_on_state compare (update sI (S i) yy (sI ps[@Fin.F1] xx)) (S i) = false).
      1: { 
        unfold beval_on_state, beval, MC_BEval.eval.
        rewrite update_read. rewrite update_read''. 2: discriminate.
        rewrite H4. rewrite H'; auto. rewrite Hs0.
        rewrite Nat.eqb_neq. apply lt_neq.
        rewrite nth_hd; auto.
      }
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Else' Defs (S i) compare (Send i this q;; Call (X + Gamma g + Gamma h + 3)) (Call (X + Gamma g + 2)) _ H6)).
      simpl; clear H6; intro.
      assert (X <= X + Gamma g + 2 < X + Gamma (Recursion g h)).
      1: { split; simpl; auto with arith.  repeat (rewrite <- plus_assoc; apply plus_lt_compat_l); auto with arith. }
      set (sU := update sI (S i) yy (sI ps[@Fin.F1] xx)).
      generalize (MCT_Trans _ _ _ _ _ HU (MCT_Step _ _ _ _ _ H5 (MCT_Step _ _ _ _ _ H6 (MCT_Refl _)))).
      clear HU H5 H6; intro.
      (* Setting up for the induction hypothesis on h *)
      assert (i+2 < i+3+Pi g) as Hi''; intros. auto with arith.
      assert (forall p, In p (S i::i::tl ps) -> p < i+3+Pi g) as Hpsh; intros.
      1: { elim (In_elim H6); intro.
        rewrite <- H8. rewrite <- plus_assoc. rewrite plus_comm; simpl.
        rewrite plus_comm; auto with arith.
        elim (In_elim H8); intro.
        rewrite H9; apply le_lt_trans with (p+0); auto with arith.
        transitivity i. apply Hps, In_tail; auto.
        apply le_lt_trans with (i+0); auto with arith.
      }
      assert (~In (i+2) (S i::i::tl ps)) as Hi; intros.
      1: { intro. elim (In_elim H6).
        apply lt_neq. rewrite plus_comm; auto.
        intro; elim (In_elim H8).
        apply lt_neq; rewrite plus_comm; simpl; auto.
        intro. apply (lt_irrefl i).
        transitivity (i+2). rewrite plus_comm; simpl; auto.
        apply Hps, In_tail; auto.
      }
      assert (forall Y, X + Gamma g + 2 <= Y < X + Gamma g + 2 + Gamma h -> X <= Y < X + (Gamma g + Gamma h + 3)) as H''.
      1: {
        intros. inversion_clear H6; split; simpl.
        transitivity (X + Gamma g + 2); auto with arith.
        repeat rewrite <- plus_assoc.
        repeat rewrite <- plus_assoc in H9.
        rewrite (plus_comm 2) in H9.
        etransitivity; eauto.
        repeat apply plus_lt_compat_l; auto with arith.
      }
      assert (forall Y, X + Gamma g + 2 <= Y < X + Gamma g + 2 + Gamma h -> fst (Defs Y) <> List.nil) as HhDefs; auto.
      assert (forall Y, X + Gamma g + 2 <= Y < X + Gamma g + 2 + Gamma h -> snd (Defs Y) = Implementation_aux h d Hh (S i :: i :: tl ps) (i + 2) (i + 3 + Pi g) (X + Gamma g + 2) Y) as HhDefs'; auto.
      1: {
        intros. unfold Hh, Hd'; rewrite <- Recursion_Procs_h with (q:=q); auto.
        replace (X + Gamma g + Gamma h + 2) with (X + Gamma g + 2 + Gamma h); auto.
        repeat rewrite <- plus_assoc. rewrite (plus_comm 2); auto.
      }
      assert (forall H, sU (S i::i::tl ps)[@H] xx = (m::yI::tl ns)[@H]) as Hinput''; intros.
      1: {
        replace (sU (S i::i::tl ps)[@H6] xx) with (map (fun y => sU y xx) (S i::i::tl ps))[@H6].
        2: rewrite (nth_map _ _ _ _ (eq_refl _)); auto.
        apply hd_tl_eq. 2: apply hd_tl_eq.
        * simpl. unfold sU; rewrite update_read''; auto. discriminate.
        * simpl. unfold sU; rewrite update_read'; auto.
        * simpl. intros. rewrite (nth_map _ _ _ _ (eq_refl _)).
          unfold sU; rewrite update_read'; auto.
          repeat rewrite <- nth_tl. rewrite <- Hs0; auto.
          apply gt_neq; red.
          transitivity i; auto. rewrite <- nth_tl; auto.
      }
      elim (converges_Recursion_full _ _ _ _ Hf (S m)); auto; intros.
      elim (converges_Recursion_step _ _ _ m _ H6); simpl; auto. intros.
      inversion_clear H8.
      rewrite (converges_inj _ _ _ _ H9 H2) in H10; clear x0 H9.
      elim (IHd _ _ Hh _ _ _ _ _ _ _ Hi Hpsh Hi'' HhDefs HhDefs' H10 _ Hinput''); intros.
      rename x0 into sF; destroy H8.
      rename x0 into tlF.
      (* After calling h *)
      repeat rewrite <- plus_assoc in H8; rewrite (plus_comm 2) in H8.
      repeat rewrite plus_assoc in H8.
      assert (X <= X + Gamma g + Gamma h + 2 < X + (Gamma g + Gamma h + 3)).
      1: { split; auto with arith.
        repeat rewrite <- plus_assoc; repeat apply plus_lt_compat_l; auto.
      }
      elim (Call_reduce Defs (X + Gamma g + Gamma h + 2) sF); auto; intros.
      rewrite HDefs', Recursion_Procs_2 in H13; auto.
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (i+2) this i xx (Send (S i) this (i+2);; Send (i+2) succ_this (S i);; Call (X + Gamma g + 1)) sF)).
      simpl. set (sF' := update sF i xx (sF (i+2) xx)); intros.
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (S i) this (i+2) xx (Send (i+2) succ_this (S i);; Call (X + Gamma g + 1)) sF')).
      simpl. set (sF'' := update sF' (i+2) xx (sF' (S i) xx)); intros.
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (i+2) succ_this (S i) xx (Call (X + Gamma g + 1)) sF'')).
      simpl. set (sF''' := update sF'' (S i) xx (S (sF'' (i+2) xx))); intros.
      exists (tlI ++ (tlU ++ L_Com ps[@Fin.F1] (sI ps[@Fin.F1] xx) (S i) :: L_Tau (S i) :: List.nil) ++ tlF ++ x0 ++ L_Com (i+2) (sF (i+2) xx) i :: L_Com (S i) (sF' (S i) xx) (i+2) :: L_Com (i+2) (S (sF'' (i+2) xx)) (S i) :: List.nil)%list.
      exists sF''', x. repeat split; auto.
      ++ do 4 (eapply MCT_Trans; eauto).
         do 3 (eapply MCT_Step; eauto).
         constructor.
      ++ unfold sF''', sF'', sF'.
         do 2 (rewrite update_read'; auto).
         rewrite update_read; auto.
         apply gt_neq; rewrite plus_comm; simpl; auto.
      ++ unfold sF''', sF'', sF'.
         rewrite update_read.
         rewrite update_read.
         rewrite update_read'; auto.
         rewrite H11; auto.
         2: {
           rewrite <- plus_assoc; rewrite (plus_comm 3).
           rewrite plus_assoc; rewrite plus_comm.
           simpl; auto with arith.
         }
         2: { apply lt_neq; rewrite plus_comm; auto. }
         unfold sU. rewrite update_read''; auto. discriminate.
      ++ unfold sF''', sF'', sF'; intros.
         rewrite update_read.
         repeat rewrite update_read'.
         rewrite H11; auto with arith.
         unfold sU. rewrite update_read'; auto.
         apply gt_neq; red; transitivity i; auto.
         apply lt_neq; red; transitivity i; auto with arith.
         apply gt_neq; auto.
         apply gt_neq; red; transitivity i; auto. rewrite plus_comm; simpl; auto.
         apply gt_neq; red; transitivity i; auto with arith.
  - elim (H0 _ (le_refl _)); clear H0; intros tl Htl.
    destroy Htl.
    rename x into sF.
    rewrite <- eta in H1.
    rewrite <- (converges_inj _ _ _ _ Hf H1) in H2; clear H1 x0.
    assert (X <= X + Gamma g + 1 < X + Gamma (Recursion g h)).
    1: {
      split; auto with arith.
      simpl. repeat rewrite <- plus_assoc; repeat apply plus_lt_compat_l.
      rewrite plus_comm; auto with arith.
    }
    elim (Call_reduce Defs (X + Gamma g + 1) sF); auto; intros.
    rewrite HDefs', Recursion_Procs_1 in H4; auto.
    rename x into tlU, H4 into HU.
    unfold IfEq in HU.
    generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs ps[@Fin.F1] this (S i) yy (If (S i) ? compare Then Send i this q;; Call (X + Gamma g + Gamma h + 3) Else Call (X + Gamma g + 2)) sF)).
    simpl; intro.
    assert (beval_on_state compare (update sF (S i) yy (sF ps[@Fin.F1] xx)) (S i) = true).
    1: { 
      unfold beval_on_state, beval, MC_BEval.eval.
      rewrite update_read. rewrite update_read''. 2: discriminate.
      rewrite H3. rewrite Htl; auto. rewrite Hs0.
        rewrite Nat.eqb_eq. rewrite nth_hd; auto.
    }
    generalize (MCP_To_intro _ _ _ _ _ _ (C_Then' Defs (S i) compare (Send i this q;; Call (X + Gamma g + Gamma h + 3)) (Call (X + Gamma g + 2)) _ H5)).
    set (sF' := update sF (S i) yy (sF ps[@Fin.F1] xx)).
    simpl; clear H5; intro.
    generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs i this q xx (Call (X + Gamma g + Gamma h + 3)) sF')).
    simpl; set (sF'' := update sF' q xx (sF' i xx)); intro.
    exists sF'', (t ++ tl ++ (tlU ++ L_Com ps[@Fin.F1] (sF ps[@Fin.F1] xx) (S i) :: L_Tau (S i) :: L_Com i (sF' i xx) q :: List.nil))%list.
    repeat split; auto.
    * unfold sF'', sF'. rewrite update_read.
      rewrite update_read'; auto.
    * unfold sF'', sF'. intros; repeat rewrite update_read'; auto.
      2: apply gt_neq; red; transitivity i; auto.
      rewrite Htl; auto.
    * do 3 (eapply MCT_Trans; eauto).
      do 3 (eapply MCT_Step; eauto).
      do 2 rewrite <- (plus_assoc X). constructor.
+ (* Minimization *)
  set (Hd' := lt_S_n (depth h) d Hd).
  assert (forall H, ps[@H] < i) as Hpsi.
  1: { intros. apply Hps. eapply nth_In; auto. }
  assert (S X = X + 1) as HXSX. rewrite plus_comm; auto.
  (* Initialization *)
  assert (X <= X < X + Gamma (Minimization h)).
  1: {
    split; auto with arith.
    apply le_lt_trans with (X + 0); auto with arith.
    apply plus_lt_compat_l; apply Gamma_neq_zero.
  }
  elim (Call_reduce Defs X s); auto. intros tl0 H00.
  rewrite HDefs' in H00; auto.
  rewrite Minimization_Procs_0 in H00.
  generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (i+2) zero (i+1) xx (Call (X+1)) s)).
  simpl. set (s0 := update s (i+1) xx 0); intro.
  (* Setting up for the induction hypothesis on h *)
  assert (forall Y, X + 1 <= Y < X + 1 + Gamma h -> X <= Y < X + (Gamma h + 2)) as H'.
  1: {
    intros. inversion_clear H1; split; simpl.
    transitivity (X + 1); auto with arith.
    transitivity (X + 1 + Gamma h); auto.
    rewrite <- (plus_comm 2), plus_assoc.
    auto with arith.
  }
  assert (forall Y, X + 1 <= Y < X + 1 + Gamma h -> fst (Defs Y) <> List.nil) as HhDefs. eauto.
  assert (forall Y, X + 1 <= Y < X + 1 + Gamma h -> snd (Defs Y) = Implementation_aux h _ Hd' (shiftin (i+1) ps) i (i+3) (X+1) Y) as HhDefs'.
  1: {
    intros. elim H1; intros. generalize (HDefs' _ (H' _ H1)).
    rewrite Minimization_Procs_h; auto.
    split; auto.
    rewrite <- plus_assoc, <- (plus_comm 1), plus_assoc; auto.
  }
  assert (~In i (shiftin (i+1) ps)) as Hi.
  1: {
    intro. apply (lt_irrefl i). elim (shiftin_elim _ _ H1); auto.
    intros; rewrite <- H2 at 2; auto. rewrite plus_comm; auto.
  }
  assert (i < i+3) as Hi'. rewrite plus_comm; simpl; auto.
  assert (forall p, In p (shiftin (i+1) ps) -> p < i+3) as Hpsh.
  1: {
    intros. elim (shiftin_elim _ _ H1); auto.
    intro. rewrite <- H2; simpl; auto with arith.
    transitivity i; auto.
  }
  assert (exists z, converges h (shiftin 0 ns) z).
  1: {
    elim (eq_nat_dec y 0); intros.
    + exists 0. apply converges_Minimization.
      rewrite <- a; auto.
    + elim (converges_Minimization_mon _ _ _ Hf) with 0; eauto.
      apply neq_0_lt; auto.
  }
  inversion_clear H1.
  assert (forall H, s0 (shiftin (i+1) ps)[@H] xx = (shiftin 0 ns)[@H]) as Hinput'.
  1: {
    intro.
    replace (s0 (shiftin (i+1) ps)[@H1] xx) with (map (fun y => s0 y xx) (shiftin (i+1) ps))[@H1]; auto.
    2: rewrite (nth_map _ _ _ _ (eq_refl _)); auto.
    rewrite map_shiftin.
    apply shiftin_eq.
    unfold s0. rewrite plus_comm; apply update_read.
    intro. rewrite nth_map'. unfold s0; rewrite update_read'; auto.
    apply gt_neq; red. transitivity i; auto. rewrite plus_comm; auto.
  }
  elim (IHd _ _ Hd' _ _ _ _ _ _ _ Hi Hpsh Hi' HhDefs HhDefs' H2 _ Hinput'); intros.
  rename x0 into sI; destroy H1.
  rename x0 into tlI, H1 into HI.
  replace (X + 1 + Gamma h) with (X + Gamma h + 1) in HI.
  2: repeat rewrite <- plus_assoc; rewrite <- (plus_comm 1); auto.
  generalize (MCT_Trans _ _ _ _ _ H00 (MCT_Step _ _ _ _ _ H0 HI)).
  set (P := Build_Program Defs (Call (X + Gamma h + 1))).
  clear H0 H00 HI; intro HI.
  assert (X <= X + Gamma h + 1 < X + Gamma (Minimization h)).
  1: { split; simpl; auto with arith. rewrite plus_assoc; auto with arith. }
  (* Loop *)
  assert (forall m, m <= y -> exists t' s' y', (P,sI) --[ t' ]-->* (P,s')
    /\ converges h (shiftin m ns) y' /\ s' i xx = y' /\ s' (i+1) xx = m /\ forall j, j < i -> s' j xx = s0 j xx).
  - induction m; intros.
    * exists List.nil, sI, x; repeat split; auto. constructor.
      rewrite H4; auto with arith. unfold s0. rewrite plus_comm, update_read; auto.
      apply gt_neq. red; rewrite plus_comm; auto.
      intros; apply H4. transitivity i; auto. apply lt_neq; auto.
    * elim IHm; auto with arith; clear IHm.
      intros tlI' H''; destroy H''.
      rename x1 into yI, x0 into sI', H5 into HI'.
      elim (Call_reduce Defs (X + Gamma h + 1) sI'); intros; auto.
      rename x0 into tlU, H5 into HU.
      rewrite HDefs', Minimization_Procs_1 in HU; auto.
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (i+1) zero (i+2) xx (IfEq (i+2) i (Send (i+1) this q;; Call (X + Gamma h + 2)) (Send (i+1) this (i+2);; Send (i+2) succ_this (i+1);; Call (X+1))) sI')).
      simpl. set (s1 := update sI' (i+2) xx 0); intro.
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs i this (i+2) yy (Cond (i+2) compare (Send (i+1) this q;; Call (X + Gamma h + 2)) (Send (i+1) this (i+2);; Send (i+2) succ_this (i+1);; Call (X+1))) s1)).
      simpl. set (s2 := update s1 (i+2) yy (s1 i xx)); intro.
      assert (beval_on_state compare s2 (i+2) = false).
      1: {
        unfold beval_on_state, beval, MC_BEval.eval.
        apply Nat.eqb_neq.
        unfold s2, s1.
        rewrite update_read, update_read''; auto. 2: discriminate.
        rewrite update_read, update_read'.
        rewrite H7.
        elim (converges_Minimization_mon _ _ _ Hf m); auto.
        intros. rewrite (converges_inj _ _ _ _ H6 H10); discriminate.
        apply gt_neq; rewrite plus_comm; simpl; auto.
      }
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Else' Defs _ _ (Send (i+1) this q;; Call (X+Gamma h+2)) (Send (i+1) this (i+2);; Send (i+2) succ_this (i+1);; Call (X+1)) _ H10)).
      simpl; clear H10; intro.
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (i+1) this (i+2) xx (Send (i+2) succ_this (i+1);; Call (X+1)) s2)).
      simpl. set (s3 := update s2 (i+2) xx (s2 (i+1) xx)); intro.
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (i+2) succ_this (i+1) xx (Call (X+1)) s3)).
      simpl. set (s4 := update s3 (i+1) xx (S (s3 (i+2) xx))); intro.
      (* IH on H again *)
      assert (exists z, converges h (shiftin (S m) ns) z).
      1: {
        inversion H1; intros.
        + rewrite H13. elim (converges_Minimization _ _ _ Hf); intros.
          exists 0, x0; eauto.
        + elim (converges_Minimization_mon _ _ _ Hf) with (S m); eauto.
          rewrite <- H14; auto with arith.
      }
      inversion_clear H13. rename x0 into x'.
      assert (forall H, s4 (shiftin (i+1) ps)[@H] xx = (shiftin (S m) ns)[@H]) as Hinput''.
      1: {
        intro.
        replace (s4 (shiftin (i+1) ps)[@H13] xx) with (map (fun y => s4 y xx) (shiftin (i+1) ps))[@H13]; auto.
        2: rewrite (nth_map _ _ _ _ (eq_refl _)); auto.
        rewrite map_shiftin.
        apply shiftin_eq.
        + unfold s4, s3, s2, s1.
          repeat rewrite update_read. repeat rewrite update_read'.
          2: apply gt_neq; red; auto with arith.
          2: apply gt_neq; red; auto with arith.
          rewrite <- H8; auto.
        + intro. rewrite nth_map'. unfold s4, s3, s2, s1.
          assert (i+2<>ps[@H15]). apply gt_neq; red; transitivity i; auto. rewrite plus_comm; simpl; auto.
          repeat rewrite update_read'; auto.
          2: apply gt_neq; red; auto with arith.
          rewrite H'', <- Hinput; auto.
          unfold s0. apply update_read'; auto.
          apply gt_neq; red; rewrite plus_comm. transitivity i; auto.
      }
      elim (IHd _ _ Hd' _ _ _ _ _ _ _ Hi Hpsh Hi' HhDefs HhDefs' H14 _ Hinput''); intros.
      rename x0 into sL; destroy H13.
      rename x0 into tlL, H13 into HL.
      replace (X + 1 + Gamma h) with (X + Gamma h + 1) in HL.
      2: repeat rewrite <- plus_assoc; rewrite <- (plus_comm 1); auto.
      fold P in HL, HU.
      eexists; exists sL, x'; repeat split; auto.
      -- do 2 (eapply MCT_Trans; eauto).
         do 5 (eapply MCT_Step; eauto).
      -- rewrite H16; auto with arith. 2: rewrite plus_comm; simpl; auto.
         unfold s4, s3, s2, s1.
         do 2 rewrite update_read. repeat rewrite update_read'.
         2: apply gt_neq; red; auto with arith.
         2: apply gt_neq; red; auto with arith.
         rewrite <- H8; auto.
      -- intros. rewrite H16. 2: transitivity i; auto with arith. 2: apply lt_neq; auto.
         assert (i+2 <> j). apply gt_neq; red; rewrite plus_comm. transitivity i; simpl; auto.
         unfold s4, s3, s2, s1. rewrite <- (plus_comm 1).
         rewrite update_read. repeat rewrite update_read'; auto.
         apply gt_neq; red; transitivity i; auto.
  - elim (H1 y); auto.
    intros tlL HL; destroy HL.
    rename x0 into sL.
    rewrite (converges_inj _ _ _ _ H6 (converges_Minimization _ _ _ Hf)) in H7; clear x1 H6.
    elim (Call_reduce Defs (X + Gamma h + 1) sL); intros; auto.
    rename x0 into tlU, H6 into HU.
    rewrite HDefs', Minimization_Procs_1 in HU; auto.
    generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (i+1) zero (i+2) xx (IfEq (i+2) i (Send (i+1) this q;; Call (X + Gamma h + 2)) (Send (i+1) this (i+2);; Send (i+2) succ_this (i+1);; Call (X+1))) sL)).
    simpl. set (s1 := update sL (i+2) xx 0); intro.
    generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs i this (i+2) yy (Cond (i+2) compare (Send (i+1) this q;; Call (X + Gamma h + 2)) (Send (i+1) this (i+2);; Send (i+2) succ_this (i+1);; Call (X+1))) s1)).
    simpl. set (s2 := update s1 (i+2) yy (s1 i xx)); intro.
    assert (beval_on_state compare s2 (i+2) = true).
    1: {
      unfold beval_on_state, beval, MC_BEval.eval.
      apply Nat.eqb_eq.
      unfold s2, s1.
      rewrite update_read, update_read''; auto. 2: discriminate.
      rewrite update_read, update_read'; auto.
      apply gt_neq; rewrite plus_comm; simpl; auto.
    }
    generalize (MCP_To_intro _ _ _ _ _ _ (C_Then' Defs _ _ (Send (i+1) this q;; Call (X+Gamma h+2)) (Send (i+1) this (i+2);; Send (i+2) succ_this (i+1);; Call (X+1)) _ H10)).
    simpl; clear H10; intro.
    generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (i+1) this q xx (Call (X+Gamma h+2)) s2)).
    simpl. set (s3 := update s2 q xx (s2 (i+1) xx)); intro.
    exists s3; eexists. repeat split; auto.
    * unfold s3, s2, s1.
      rewrite update_read.
      rewrite update_read'. 2: apply gt_neq; auto with arith.
      rewrite update_read'; auto. apply gt_neq; auto with arith.
    * intros. unfold s3, s2, s1.
      rewrite update_read'; auto.
      rewrite update_read'. 2: apply gt_neq; auto with arith.
      rewrite update_read'. 2: apply gt_neq; auto with arith.
      rewrite HL; auto.
      unfold s0. apply update_read'. apply gt_neq; auto with arith.
    * do 3 (eapply MCT_Trans; eauto).
      do 4 (eapply MCT_Step; eauto).
      rewrite plus_assoc; constructor.
Qed.

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

End Temp.
