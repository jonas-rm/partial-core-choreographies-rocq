Require Import Arith.
Require Export Basic.
Require Export Common.
Require Export MC.
Require Export Implementation.

Module Export MC_Nat := Implementation.MC_Nat.

(** MOVE ME *)
Lemma diverges_Composition_arg : forall {m k} fs g ns H,
  diverges fs[@H] ns -> diverges (@Composition m k g fs) ns.
Proof.
intros; intro.
case_eq (Kleene.eval (Composition g fs) steps ns); auto.
intros; exfalso.
elim (converges_Composition' fs g ns n); intros.
2: exists steps; auto.
elim (H2 H); intros.
rewrite H0 in H3; inversion H3.
Qed.

Lemma diverges_Composition_fun : forall {m k} fs g ns x,
  (forall H, converges fs[@H] ns x[@H]) ->
  diverges g x -> diverges (@Composition m k g fs) ns.
Proof.
intros; intro.
case_eq (Kleene.eval (Composition g fs) steps ns); auto.
intros; exfalso.
elim (converges_Composition fs g ns n); intros.
2: exists steps; auto.
inversion_clear H2.
replace x0 with x in H4. inversion_clear H4. rewrite H0 in H2; inversion H2.
apply eq_nth_iff'; intro.
apply converges_inj with fs[@p] ns; auto.
Qed.

Lemma diverges_Recursion_ind : forall {m} (g:PRFunction m) h x ns,
  diverges (Recursion g h) (x::ns) ->
  forall y, x<y -> diverges (Recursion g h) (y::ns).
Proof.
induction y; intros. inversion H0.
assert (diverges (Recursion g h) (y::ns)).
+ inversion H0; auto. rewrite <- H2; auto.
+ intro. revert H1.
  unfold diverges, Kleene.eval.
  simpl.
  intro; rewrite H1; auto.
Qed.

Lemma diverges_Recursion_base : forall {m} (g:PRFunction m) h ns,
  diverges g (tl ns) -> diverges (Recursion g h) ns.
Proof.
intros.
set (n := hd ns : nat). assert (hd ns = n); auto.
clearbody n. revert ns H H0.
induction n; intros.
+ intro. revert H.
  rewrite (eta ns), H0.
  unfold diverges, Kleene.eval; simpl; auto.
+ rewrite (eta ns). apply diverges_Recursion_ind with 0; auto.
  rewrite H0; auto with arith.
Qed.

Lemma diverges_Recursion_step : forall {m} (g:PRFunction m) h x y ns,
  converges (Recursion g h) (x::ns) y -> diverges h (x::y::ns)
  -> forall z, x<z -> diverges (Recursion g h) (z::ns).
Proof.
induction z; intros. inversion H1.
inversion H1.
2: apply diverges_Recursion_ind with z; auto.
intro.
rewrite H3 in H, H0; clear IHz H1 H3 x.
case_eq (Kleene.eval (Recursion g h) steps (z::ns)); intros.
+ inversion_clear H. unfold Kleene.eval in H1, H2.
  rewrite (eval_opt_inj _ _ _ _ _ _ _ H1 H2) in H1. clear n H2.
  generalize (H0 steps); clear H0; revert H1.
  unfold diverges, Kleene.eval; simpl.
  intros. rewrite H1; auto.
+ clear H; generalize (H0 steps). clear H0; revert H1.
  unfold diverges, Kleene.eval; simpl.
  intros. rewrite H1; auto.
Qed.

Lemma diverges_Minimization : forall {m} (h:PRFunction (1+m)) ns x,
  (forall y, y < x -> exists z, converges h (shiftin y ns) (S z)) ->
  diverges h (shiftin x ns) -> diverges (Minimization h) ns.
Proof.
red; intros.
case_eq (Kleene.eval (Minimization h) steps ns); auto.
intros; exfalso.
assert (converges (Minimization h) ns n). exists steps; auto.
elim (converges_Minimization _ _ _ H2); intros.
generalize (converges_Minimization_mon _ _ _ H2); intros.
elim (lt_eq_lt_dec x n); intros. inversion_clear a.
+ elim (H4 _ H5); intros. inversion_clear H6.
  rewrite H0 in H7; inversion H7.
+ rewrite <- H5, H0 in H3; inversion H3.
+ elim (H _ b); intros. inversion_clear H5.
  generalize (eval_inj_Some _ _ _ _ _ _ _ H3 H6). discriminate.
Qed.

(* STRATEGY
  It is undecidable whether a function converges or not on a value.
  We also cannot get inversion results on divergence.
  So we prove that the choreography ending implies convergence.
  From determinism we can get that divergence implies non-termination. *)

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
  intro; apply H. eapply nth_In. rewrite nth_hd; auto.
+ (* Successor *)
  simpl. unfold Pack1; simpl.
  elim RecVar_dec; repeat split; simpl; auto.
  intro; apply H. eapply nth_In. rewrite nth_hd; auto.
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
    * apply lt_neq. transitivity n; auto. apply H0. apply nth_In with Fin.F1; apply nth_hd.
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

Lemma all_pids_In : forall m n, m <= n -> List.In m (all_pids n).
Proof.
induction n; simpl; auto with arith.
intro. inversion_clear H; auto.
Qed.

Lemma In_all_pids : forall m n, List.In m (all_pids n) -> m <= n.
Proof.
induction n; simpl; intros; inversion_clear H; auto; inversion H0; auto.
Qed.

Lemma all_pids_incl : forall m n, m <= n -> set_incl_Pid (all_pids m) (all_pids n).
red; red; intros.
apply all_pids_In. transitivity m; auto. apply In_all_pids; auto.
Qed.

Lemma MCC_pn_all_pids_incl : forall C m n, m <= n ->
  (set_incl_Pid (MCC_pn C (fun _ => all_pids m)) (all_pids m))
  -> (set_incl_Pid (MCC_pn C (fun _ => all_pids n)) (all_pids n)).
Proof.
induction C; simpl; unfold set_incl_Pid, set_incl; intros; auto.
- inversion H1.
- unfold set_incl_Pid, set_incl in IHC.
  elim (set_union_elim _ _ _ _ H1); intros.
  apply (all_pids_incl m); auto. apply H0. apply set_union_iff; auto.
  apply IHC with m; auto. intros; apply H0. apply set_union_iff; auto.
- unfold set_incl_Pid, set_incl in IHC.
  elim (set_union_elim _ _ _ _ H1); intros.
  apply (all_pids_incl m); auto. apply H0. apply set_union_iff; auto.
  apply IHC with m; auto. intros; apply H0. apply set_union_iff; auto.
- unfold set_incl_Pid, set_incl in IHC1, IHC2.
  elim (set_union_elim _ _ _ _ H1); intros. elim (set_union_elim _ _ _ _ a); intros.
  apply (all_pids_incl m); auto. apply H0. apply set_union_iff; left. apply set_union_iff; auto.
  apply IHC1 with m; auto. intros; apply H0. apply set_union_iff; left. apply set_union_iff; auto.
  apply IHC2 with m; auto. intros; apply H0. apply set_union_iff; auto.
Qed.

(*
Lemma seq_compose_well_ann : forall {k m} (fs:t (PRFunction m) k) d Hd ps q i X Impl Y,
  (forall p, In p ps -> p <= i) -> q + k <= i ->
  (forall H p Hd' i' X' Y' n q', i <= i' -> q' + k <= i' -> List.In p (MCC_pn (Impl m fs[@H] Hd' ps q' (S i') X' Y') (fun _ => all_pids (i' + Pi fs[@H] + n))) -> p <= i' + Pi fs[@H] + n) ->
 forall p,
  List.In p (MCC_pn (seq_compose fs d Hd ps q (S i) X Impl Y) (fun _ => all_pids (i + vsum (map Pi fs)))) -> p <= i + vsum (map Pi fs).
Proof.
induction k; intro.
+ refine (@case0 _ _ _ ); simpl; intros. inversion H2.
+ intro. revert k fs IHk. refine (@caseS _ _ _); intros.
  revert H2; simpl. rewrite plus_assoc. elim Nat.ltb; intros.
  - apply (H1 Fin.F1 p (Hd Fin.F1) i X Y _ q); auto with arith.
    (* transitivity (q + S n); auto with arith. *)
  - apply IHk with d (fun H => Hd (Fin.FS H)) ps (S q) (X+Gamma h) Impl Y; auto.
    * intros; transitivity i; auto with arith.
    * rewrite <- plus_n_Sm in H0; transitivity i; auto with arith.
    * intros. apply (H1 (Fin.FS H3) _ Hd' i' X' Y' _ q'); auto.
      transitivity (i + Pi h); auto with arith.
Qed.

Lemma Implements_aux_well_ann : forall {m} (f:PRFunction m) d Hd ps q i X Y,
  (forall p, In p ps -> p <= i) -> q <= i -> forall p,
  List.In p (MCC_pn (Implementation_aux f d Hd ps q (S i) X Y) (fun _ => all_pids (i + Pi f))) -> p <= i + Pi f.
Proof.
intros m f d; revert m f.
induction d. inversion Hd.
do 2 intro; case f; simpl; intros; revert H1.
- unfold Pack1. rewrite plus_0_r.
  elim RecVar_dec; simpl; intros. 2: inversion H1.
  elim (set_union_elim _ _ _ _ H1); intros. inversion_clear a.
  * apply H; eapply nth_In; eauto.
  * revert H0. inversion_clear H2; inversion H0; auto.
  * apply In_all_pids; auto.
- unfold Pack1. rewrite plus_0_r.
  elim RecVar_dec; simpl; intros. 2: inversion H1.
  elim (set_union_elim _ _ _ _ H1); intros. inversion_clear a.
  * apply H; eapply nth_In; eauto.
  * revert H0. inversion_clear H2; inversion H0; auto.
  * apply In_all_pids; auto.
- unfold Pack1. rewrite plus_0_r.
  elim RecVar_dec; simpl; intros. 2: inversion H1.
  elim (set_union_elim _ _ _ _ H1); intros. inversion_clear a.
  * apply H; eapply nth_In; eauto.
  * revert H0. inversion_clear H2; inversion H0; auto.
  * apply In_all_pids; auto.
- set (Hd' := lt_S_n (Nat.max (depth g) (vmax (map depth fs))) d Hd).
  set (Hfs := vmax_lt_map _ _ (max_lt_r _ _ _ Hd')).
  set (Hg := max_lt_l _ _ _ Hd').
  rename m into n; rename m0 into m.
  elim Nat.ltb; intro.
  * generalize (seq_compose_well_ann fs d Hfs ps (S i) (i+m) X (fun m f => Implementation_aux f d) Y); intros.
    transitivity (S (i + m) + vsum (map Pi fs)). apply H2; auto.
    + transitivity i; auto with arith.
    + intros.
      assert (forall p, In p ps -> p <= i'). transitivity i; auto. transitivity (S (i+m)); auto with arith.
      assert (q' <= i'). transitivity (S i + m); auto.
      generalize (IHd _ fs[@H3] Hd'0 ps q' i' X Y H7 H8).
      intro.
      apply In_all_pids. revert H6.
      apply MCC_pn_all_pids_incl with (i' + Pi fs[@H3]); auto with arith.
      red; red; intros. apply all_pids_In; eauto.
    + 

(* *)

- set (Hd' := lt_S_n (Nat.max (depth g) (depth h)) d Hd).
  set (Hg := (max_lt_l _ _ _ Hd')).
  set (Hh := (max_lt_r _ _ _ Hd')).
  assert (forall p, In p (tl ps) -> p <= i+3).
  1:{ intros. transitivity i; auto with arith. apply H, In_tail; auto. }
  assert (S i <= i+3). rewrite plus_comm; simpl; auto.
  generalize (IHd _ _ Hg (tl ps) (S i) (i+3) X Y H1 H2 p).
  assert (forall p, In p (S (S i) :: S i :: tl ps) -> p <= i + 3 + Pi g).
  1: {
    intros. elim (In_elim H3); intros. rewrite <- H4, <- (plus_comm 3). auto with arith.
    elim (In_elim H4); intros. rewrite <- H5, <- (plus_comm 3). simpl; auto with arith.
    transitivity i; auto with arith. apply H, In_tail; auto.
  }
  assert (S (i + 2) <= i + 3 + Pi g). auto with arith.
  generalize (IHd _ _ Hh (S (S i) :: S i :: tl ps) (S (i + 2)) (i+3+Pi g) (X+Gamma g+2) Y H3 H4 p).
  do 2 intro.
  assert (S (S i) <= i + (Pi g + Pi h + 3)) as Hi. transitivity (i+3); auto with arith. rewrite plus_comm; simpl; auto.
  assert (S i <= i + (Pi g + Pi h + 3)) as Hi'. transitivity (i+3); auto with arith.
  assert (S (i+2) <= i + (Pi g + Pi h + 3)) as Hi''. transitivity (i+3); auto with arith.
  elim Nat.ltb. 2: elim RecVar_dec. 3: elim RecVar_dec. 4: elim RecVar_dec.
  * intros.
    apply In_all_pids. revert H7. apply MCC_pn_all_pids_incl with (i+3+Pi g).
    rewrite <- plus_assoc, (plus_comm 3). auto with arith.
    red; red; intros. apply all_pids_In; eauto.
  * simpl; intros.
    elim (set_union_elim _ _ _ _ H7); intro. inversion_clear a; inversion H8; auto.
    + rewrite <- H9; auto.
    + inversion H9.
    + apply In_all_pids; auto.
  * simpl; intros.
    elim (set_union_elim _ _ _ _ H7); intro. inversion_clear a; inversion H8.
    + transitivity i; auto with arith. eapply H, nth_In; auto.
    + rewrite <- H9; auto.
    + inversion H9.
    + elim (set_union_elim _ _ _ _ b); intro. elim (set_union_elim _ _ _ _ a); intro.
      ++ inversion_clear a0; inversion H8; auto.
      ++ elim (set_union_elim _ _ _ _ b0); intro. inversion_clear a0.
         rewrite <- H8; auto.
         inversion_clear H8; inversion H9. rewrite <- H9. transitivity i; auto with arith.
         apply In_all_pids; auto.
      ++ apply In_all_pids; auto.
  * simpl; intros.
    elim (set_union_elim _ _ _ _ H7); intro. inversion_clear a; inversion H8; auto.
    + rewrite <- H9; auto.
    + inversion H9.
    + elim (set_union_elim _ _ _ _ b); intro. inversion_clear a.
      ++ rewrite <- H8; auto.
      ++ inversion_clear H8; inversion H9; auto.
      ++ elim (set_union_elim _ _ _ _ b0); intro. inversion_clear a.
         rewrite <- H8; auto.
         inversion_clear H8; inversion H9; auto.
         apply In_all_pids; auto.
  * rewrite (plus_comm (Pi g + Pi h)), plus_assoc, plus_assoc.
    auto.
- set (Hd' := lt_S_n (depth h) d Hd).
  assert (forall p, In p (shiftin (S (i+1)) ps) -> p <= i+3).
  1:{ intros. elim (shiftin_elim _ _ H1); auto with arith.
      intro; rewrite <- H2, plus_comm, <- (plus_comm 3); simpl; auto. }
  assert (S i <= i+3). rewrite plus_comm; simpl; auto.
  generalize (IHd _ _ Hd' _ _ _ (X+1) Y H1 H2 p); intro.
  assert (S (i+2) <= i + (Pi h + 3)) as Hi. rewrite <- (plus_comm 3); simpl; auto with arith.
  assert (S i <= i + (Pi h + 3)) as Hi'. transitivity (S (i+2)); auto with arith.
  assert (S (i+1) <= i + (Pi h + 3)) as Hi''. transitivity (S (i+2)); auto with arith.
  elim RecVar_dec. 2: elim RecVar_dec.
  * simpl; intro. elim (set_union_elim _ _ _ _ H4); intro. inversion_clear a; inversion H5; auto.
    + rewrite <- H6; auto.
    + inversion H6.
    + apply In_all_pids; auto.
  * simpl; intro. elim (set_union_elim _ _ _ _ H4); intro.
    1: { inversion_clear a; inversion H5; auto; inversion H6; auto. }
    elim (set_union_elim _ _ _ _ b); intro.
    1: { inversion_clear a; inversion H5; auto; inversion H6; auto. }
    elim (set_union_elim _ _ _ _ b0); intro.
    1: { elim (set_union_elim _ _ _ _ a); intro.
        inversion_clear a0; inversion H5; auto.
        elim (set_union_elim _ _ _ _ b1); intro.
        inversion_clear a0; inversion H5; auto; inversion H6; auto.
        rewrite <- H6. transitivity i; auto with arith.
        apply In_all_pids; auto. }
    elim (set_union_elim _ _ _ _ b1); intro.
    1: { inversion_clear a; inversion H5; auto; inversion H6; auto. }
    elim (set_union_elim _ _ _ _ b2); intro.
    1: { inversion_clear a; inversion H5; auto; inversion H6; auto. }
    apply In_all_pids; auto.
  * rewrite (plus_comm (Pi h)), plus_assoc; auto.
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
+ red; intro. unfold Vars; simpl.
  do 2 red; intros.
  unfold Procs, Implementation, Procedures in H0.
  admit.
  (* apply Implements_aux_well_ann in H0.
  - apply all_pids_In; auto.
  - intros. apply Nat.max_le_iff. right; apply vmax_In; auto.
  - apply Nat.le_max_l. *)
Admitted.

Lemma Implements'_WF : forall {n} (f:PRFunction n),
  MCP_WF (Implementation' f).
Proof.
intros; apply Implements_WF.
intro. elim (in_vec_k_to_n _ H); intros.
inversion H0.
Qed.

Lemma Implementation_aux_ge : forall {n} (f:PRFunction n) d Hd ps q i X Y,
  Y >= X + Gamma f -> Implementation_aux f d Hd ps q i X Y = End.
Proof.
intros n f d; revert n f. induction d. inversion Hd.
intros n f. case f; intros.
+ simpl in H; red in H. rewrite plus_comm in H.
  simpl. unfold Pack1, RecVar_dec; simpl.
  assert (Y <> X). apply gt_neq; auto with arith.
  rewrite <- Rdec.eqb_neq in H0. rewrite H0; auto.
+ simpl in H; red in H. rewrite plus_comm in H.
  simpl. unfold Pack1, RecVar_dec; simpl.
  assert (Y <> X). apply gt_neq; auto with arith.
  rewrite <- Rdec.eqb_neq in H0. rewrite H0; auto.
+ simpl in H; red in H. rewrite plus_comm in H.
  simpl. unfold Pack1, RecVar_dec; simpl.
  assert (Y <> X). apply gt_neq; auto with arith.
  rewrite <- Rdec.eqb_neq in H0. rewrite H0; auto.
+ red in H.
  simpl.
  assert (Y >= X + vsum (map Gamma fs)). red. transitivity (X + (Gamma (Composition g fs))); simpl; auto with arith.
  apply le_not_lt in H0. rewrite <- Nat.ltb_nlt in H0. rewrite H0.
  apply IHd; rewrite <- plus_assoc, <- (plus_comm (Gamma g)); auto.
+ red in H.
  simpl; unfold RecVar_dec.
  assert (Y > X + Gamma g + 1).
  1: { red. apply lt_le_trans with (X + (Gamma (Recursion g h))); simpl; auto.
       repeat (rewrite <- plus_assoc; apply plus_lt_compat_l). rewrite plus_comm. simpl; auto with arith. }
  assert (Y >= X + Gamma g). red; red in H0. transitivity (X + Gamma g + 1); auto with arith.
  apply le_not_lt in H1. rewrite <- Nat.ltb_nlt in H1. rewrite H1.
  assert (Y <> X + Gamma g). apply gt_neq; auto. red. transitivity (X + Gamma g + 1); auto. rewrite <- (plus_comm 1); auto.
  rewrite <- Rdec.eqb_neq in H2. rewrite H2.
  assert (Y <> X + Gamma g + 1).
  1: apply gt_neq; auto.
  rewrite <- Rdec.eqb_neq in H3. rewrite H3.
  assert (Y <> X + Gamma g + Gamma h + 2).
  1: { apply gt_neq; simpl in H. red; apply lt_le_trans with (X + Gamma g + Gamma h + 3).
       apply plus_lt_compat_l; auto. rewrite (plus_assoc X) in H; rewrite <- (plus_assoc X); auto. }
  rewrite <- Rdec.eqb_neq in H4. simpl in H4. rewrite H4.
  apply IHd; red. transitivity (X + (Gamma (Recursion g h))); auto.
  simpl. repeat rewrite <- plus_assoc; repeat apply plus_le_compat_l.
  rewrite plus_comm; auto with arith.
+ red in H.
  simpl; unfold RecVar_dec.
  assert (Y <> X).
  1: { apply gt_neq; red. apply lt_le_trans with (X + Gamma (Minimization h)); auto with arith. 
       rewrite <- plus_0_r at 1. apply plus_lt_compat_l, Gamma_neq_zero. }
  rewrite <- Rdec.eqb_neq in H0. rewrite H0.
  assert (Y <> X + (@Gamma (S k) h) + 1).
  1: { apply gt_neq; red. apply lt_le_trans with (X + (Gamma (Minimization h))); simpl; auto.
       rewrite <- plus_assoc; apply plus_lt_compat_l. auto with arith. }
  rewrite <- Rdec.eqb_neq in H1. rewrite H1.
  apply IHd; red. transitivity (X + (Gamma (Minimization h))); auto.
  simpl. repeat rewrite <- plus_assoc; repeat apply plus_le_compat_l.
  rewrite plus_comm; auto with arith.
Qed.

Theorem Implementation_converges : forall {n} (f:PRFunction n) ps q ns y,
  ~In q ps -> converges f ns y -> 
  forall (s:State), (forall H, s ps[@H] xx = ns[@H]) ->
  exists c' tl, (Implementation f ps q, s) --[tl]-->* c' /\ Main (fst c') = End /\ snd c' q xx = y.
Proof.
intros.
set (Hd := Nat.lt_succ_diag_r (depth f)).
set (i := (S (max q (vmax ps)))).
elim (Implementation_aux_converges f _ Hd ps q i 0 (Procedures (Implementation f ps q)) ns y H) with s; intros; auto.
+ destroy H2. rename x into s', x0 into tl.
  simpl (0 + Gamma f) in H2.
  elim (Call_reduce (Procedures (Implementation f ps q)) (Gamma f) s'); intros.
  2: apply all_pids_not_nil.
  rename x into tl'.
  eexists. exists (tl++tl')%list; repeat split.
  * eapply MCT_Trans; eauto.
  * change (snd (Procedures (Implementation f ps q) (Gamma f)) = End).
    apply Implementation_aux_ge; auto with arith.
  * auto.
+ apply le_n_S. transitivity (vmax ps). apply vmax_In; auto. apply Nat.le_max_r.
+ apply le_n_S. apply Nat.le_max_l.
+ apply all_pids_not_nil.
Qed.

Lemma converges_Implementation_aux : forall {n} (f:PRFunction n) d Hd ps q i X Defs ns y,
  (forall Y, X <= Y < X + Gamma f -> fst (Defs Y) <> List.nil) ->
  (forall Y, X <= Y < X + Gamma f -> snd (Defs Y) = Implementation_aux f d Hd ps q i X Y) ->
  (forall p, In p ps -> p < i) -> ~In q ps -> q < i ->
  forall (s:State), (forall H, s ps[@H] xx = ns[@H]) ->
  forall s' tl, s' q xx = y -> (Build_Program Defs (Call X),s) --[tl]-->* (Build_Program Defs (Call (X + Gamma f)),s')
  -> (forall p, p < i -> p <> q -> s' p xx = s p xx) /\ converges f ns y.
Admitted.
(* Hmmm.
Proof.
intros n f d; revert n f. induction d. inversion Hd.
intros n f; case f; intros; rename H into HDefs, H0 into HDefs', H1 into Hps, H2 into Hq, H3 into Hq', H4 into Htl.
+ (* Zero *)
  assert (X <= X < X + Gamma Zero). split; auto; rewrite plus_comm; auto with arith.
  generalize (HDefs _ H), (HDefs' _ H).
  simpl; unfold Pack1; simpl.
  rewrite Rdec.eqb_refl. intros HX HX'.
  elim (Call_reduce _ _ s HX); intros tl' Htl'.
  rewrite HX' in Htl'.
  generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (hd ps) zero q xx (Call (S X)) s)).
  simpl; set (s'' := update s q xx 0); intros.
  generalize (MCT_Trans _ _ _ _ _ Htl' (MCT_Step _ _ _ _ _ H0 (MCT_Refl _))); intros.
  clear Htl' H0.
  elim (diamond_4 _ _ _ _ _ _ _ _ H6 H1); intros.
*)

(** This proof is a refactoring of the proof of Implementation_aux_converges. However,
  we can't reuse that lemma because there is no assumption on f converging.
  For recursion and minimization, we need to know that the input never changes. *)
Lemma Implementation_aux_End : forall {n} (f:PRFunction n) d Hd ps q i X Defs,
  (forall Y, X <= Y < X + Gamma f -> fst (Defs Y) <> List.nil) ->
  (forall Y, X <= Y < X + Gamma f -> snd (Defs Y) = Implementation_aux f d Hd ps q i X Y) ->
  (forall p, In p ps -> p < i) -> q < i -> ~In q ps ->
  forall s s' t, (Build_Program Defs (Call X),s) --[t]-->* (Build_Program Defs End,s')
  -> exists t' s'', (Build_Program Defs (Call X),s) --[t']-->* (Build_Program Defs (Call (X + Gamma f)),s'')
  /\ forall p, p < i -> p <> q -> s p xx = s'' p xx.
Proof.
intros n f d; revert n f. induction d. inversion Hd.
intros n f; case f; intros; rename H into HDefs, H0 into HDefs', H1 into Hps, H2 into Hq, H3 into Hq', H4 into Htl.
+ (* Zero *)
  assert (X <= X < X + Gamma Zero). split; auto; rewrite plus_comm; auto with arith.
  generalize (HDefs _ H), (HDefs' _ H).
  simpl; unfold Pack1; simpl.
  rewrite Rdec.eqb_refl. intros HX HX'.
  elim (Call_reduce _ _ s HX); intros tl' Htl'.
  rewrite HX' in Htl'.
  generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (hd ps) zero q xx (Call (S X)) s)).
  simpl; set (s'' := update s q xx 0); intros.
  generalize (MCT_Trans _ _ _ _ _ Htl' (MCT_Step _ _ _ _ _ H0 (MCT_Refl _))); intros.
  exists (tl' ++ (L_Com (hd ps) 0 q :: List.nil))%list, s''; split.
  - eapply MCT_Trans; eauto. eapply MCT_Step; eauto. rewrite plus_comm; constructor.
  - intros. unfold s''. rewrite update_read'; auto.
+ (* Successor *)
  set (x := s (hd ps) xx).
  assert (X <= X < X + Gamma Successor). split; auto; rewrite plus_comm; auto with arith.
  generalize (HDefs _ H), (HDefs' _ H).
  simpl; unfold Pack1; simpl.
  rewrite Rdec.eqb_refl. intros HX HX'.
  elim (Call_reduce _ _ s HX); intros tl' Htl'.
  rewrite HX' in Htl'.
  generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (hd ps) succ_this q xx (Call (S X)) s)).
  simpl; fold x; set (s'' := update s q xx (S x)); intros.
  exists (tl' ++ (L_Com (hd ps) (S x) q :: List.nil))%list, s''; split.
  - eapply MCT_Trans; eauto. eapply MCT_Step; eauto. rewrite plus_comm; constructor.
  - intros. unfold s''. rewrite update_read'; auto.
+ (* Projection *)
  set (x := s ps[@Fin.of_nat_lt l] xx).
  assert (X <= X < X + Gamma (Projection l)). split; auto; rewrite plus_comm; auto with arith.
  generalize (HDefs _ H), (HDefs' _ H).
  simpl; unfold Pack1; simpl.
  rewrite Rdec.eqb_refl. intros HX HX'.
  elim (Call_reduce _ _ s HX); intros tl' Htl'.
  rewrite HX' in Htl'.
  generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs ps[@Fin.of_nat_lt l] this q xx (Call (S X)) s)).
  simpl; fold x; set (s'' := update s q xx x); intros.
  exists (tl' ++ (L_Com ps[@Fin.of_nat_lt l] x q :: List.nil))%list, s''; split.
  - eapply MCT_Trans; eauto. eapply MCT_Step; eauto. rewrite plus_comm; constructor.
  - intros. unfold s''. rewrite update_read'; auto.
+ (* Composition *)
  set (Hd' := lt_S_n (Nat.max (depth g) (vmax (map depth fs))) d Hd).
  set (Hfs := vmax_lt_map _ _ (max_lt_r _ _ _ Hd')).
  set (Hg := max_lt_l _ _ _ Hd').
  (* Here we start directly with the loop *)
  assert (exists sF tlF, (Build_Program Defs (Call X),s) --[tlF]-->* (Build_Program Defs (Call (X + vsum (map Gamma fs))),sF)
    /\ forall p, p < i -> p <> q -> sF p xx = s p xx).
  - assert (forall Y, X <= Y < X + vsum (map Gamma fs) -> X <= Y < X + Gamma (Composition g fs)).
    1: {
      intros. inversion_clear H; split; auto.
      simpl. rewrite (plus_comm (Gamma g)).
      etransitivity; eauto.
      rewrite <- plus_0_r at 1. rewrite plus_assoc.
      apply plus_lt_compat_l. apply Gamma_neq_zero.
    }
    generalize (fun Y HY => HDefs Y (H Y HY)).
    clear HDefs; intro HDefs.
    assert (exists k, forall Y, X <= Y < X + vsum (map Gamma fs) ->
      snd (Defs Y) = seq_compose fs _ Hfs ps i (i+m+k) X (fun m f => Implementation_aux f d) Y).
    1: { exists 0; intros. rewrite HDefs'; auto. rewrite Composition_Procs_fs, plus_0_r; auto. }
    clearbody Hd' Hfs.
    clear g H Hd Hd' Hg HDefs'; rename H0 into HDefs'.
    revert dependent X. revert dependent i. revert dependent s.
    revert t s'; induction m.
    * intros. exists s, List.nil.
      rewrite <- (vector_0_inv fs).
      simpl. split; auto. rewrite plus_comm; constructor.
    * intros.
      revert IHm.
      revert dependent fs. revert m. refine (@caseS _ _ _); intros.
      clear f. rename h into f, t0 into fs, n0 into m.
      (* First f... *)
      assert (forall Y, X <= Y < X + Gamma f -> X <= Y < X + vsum (map Gamma (f::fs))).
      1: { intros. inversion_clear H; split; auto. simpl. rewrite plus_assoc; auto with arith. }
      elim HDefs'; clear HDefs'; intros k' HDefs'.
      assert (i < i + S m + k').
      1: { apply lt_le_trans with (i + S m); auto with arith. rewrite <- plus_n_Sm; auto with arith. }
      elim IHd with k f (Hfs Fin.F1) ps i (i + S m + k') X Defs s s' t; auto.
      2: {
        intros.
        rewrite HDefs'; auto.
        simpl. inversion_clear H1.
        apply Nat.ltb_lt in H3; rewrite H3. auto.
      }
      2: { transitivity i; auto with arith. }
      2: { intro. apply (lt_irrefl i); auto. }
      intros. destroy H1. rename x0 into sf, x into tlf.
      elim (diamond_5 _ _ _ _ _ _ _ _ H2 Htl (eq_refl _)).
      intros. destroy H3. clear H3.
      (* ... then the rest. *)
      elim IHm with fs (fun H => Hfs (Fin.FS H)) x x0 sf (S i) (X + Gamma f); intros; auto.
      destroy H3. rename x1 into sfs, x2 into tlfs. clear x x0 H4.
      2: { transitivity i; auto. }
      2: {
        apply HDefs. simpl. inversion_clear HY; split.
        transitivity (X + Gamma f); auto with arith.
        rewrite plus_assoc; auto.
      }
      2: {
        exists (k' + Pi f); intros.
        inversion_clear H3. rewrite <- plus_assoc in H6.
        rewrite (HDefs' Y). 2: split; auto; transitivity (X + Gamma f); auto with arith.
        simpl. generalize H5; intro.
        apply le_not_lt, Nat.ltb_nlt in H5. rewrite H5.
        replace (i + S m + k' + Pi f) with (S (i + m + (k' + Pi f))); auto.
        repeat rewrite plus_assoc. rewrite <- plus_n_Sm; auto.
      }
      simpl (vsum (map Gamma (f::fs))).
      (* Wheee. *)
      exists sfs, (tlf ++ tlfs)%list; split.
      rewrite plus_assoc. eapply MCT_Trans; eauto.
      intros; rewrite H3, H1; auto. transitivity i; auto. apply lt_neq; auto.
  - destroy H. rename x into sF, x0 into tlF.
    assert (X + Gamma (Composition g fs) = X + vsum (map Gamma fs) + Gamma g) as HX.
    simpl. rewrite (plus_comm (Gamma g)), plus_assoc; auto.
    elim (diamond_5 _ _ _ _ _ _ _ _ H0 Htl (eq_refl _)).
    intros. destroy H1.
    elim IHd with m g Hg (seq_labels i fs) q (i+m) (X + vsum (map Gamma fs)) Defs sF x0 x; auto.
    * intros. destroy H3. rename x2 into s'', x1 into tl'.
      exists (tlF++tl')%list, s''; split.
      eapply MCT_Trans; eauto. rewrite HX; auto.
      intros; rewrite <- H3, H; auto. apply lt_le_trans with i; auto with arith.
    * intros. inversion_clear H3. apply HDefs; split; auto.
      transitivity (X + vsum (map Gamma fs)); auto with arith.
      rewrite HX; auto.
    * intros. inversion_clear H3. rewrite HDefs'.
      rewrite Composition_Procs_g; auto. rewrite HX; auto.
      split; auto. transitivity (X + vsum (map Gamma fs)); auto with arith.
      rewrite HX; auto.
    * intros. elim (seq_labels_lt _ _ _ H3); auto.
    * apply lt_le_trans with i; auto with arith.
    * intro. elim (seq_labels_lt _ _ _ H3); intros.
      elim (lt_irrefl q). apply lt_le_trans with i; auto.
+ (* Recursion *)
  set (Hd' := lt_S_n (Nat.max (depth g) (depth h)) d Hd).
  set (Hg := (max_lt_l _ _ _ Hd')).
  set (Hh := (max_lt_r _ _ _ Hd')).
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
  assert (i < i+3) as Hi'. rewrite plus_comm; simpl; auto.
  elim IHd with k g Hg (tl ps) i (i+3) X Defs s s' t; intros; auto.
  2: { transitivity i; auto. apply Hps, In_tail; auto. }
  2: { intro. apply (lt_irrefl i), Hps, In_tail; auto. }
  destroy H.
  rename x0 into sg, x into tlg, H0 into Htlg, H into Hps'.
  clear HgDefs HgDefs' H' Hg.
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
  generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (i+2) zero (S i) xx (Call (X + Gamma g + 1)) sg)).
  simpl; intro.
  set (P := Build_Program Defs (Call (X + Gamma g + 1))).
  generalize (MCT_Trans _ _ _ _ _ Htlg (MCT_Trans _ _ _ _ _ H0 (MCT_Step _ _ _ _ _ H1 (MCT_Refl _)))).
  clear H0 H1; fold P; intro HP.
  set (t' := (tlg ++ tlg' ++ L_Com (i+2) 0 (S i) :: List.nil)%list).
  set (s0 := update sg (S i) xx 0).
  fold t' s0 in HP.
  clearbody t'. clear Htlg.
  (* Loop invariant *)
  assert (forall m, m <= s0 (hd ps) xx -> exists t' s', (P,s0) --[ t' ]-->* (P,s')
    /\ s' (S i) xx = m /\ forall p, p < i -> s' p xx = s0 p xx).
  - induction m; intros.
    * exists List.nil, s0; repeat split; auto. constructor. apply update_read.
    * elim IHm; auto with arith; clear IHm.
      intros tlI H'; destroy H'.
      rename x into sI, H1 into HI.
      assert (X <= X + Gamma g + 1 < X + Gamma (Recursion g h)).
      1: { split; simpl; auto with arith.  repeat (rewrite <- plus_assoc; apply plus_lt_compat_l); auto with arith. }
      elim (Call_reduce Defs (X + Gamma g + 1) sI); intros; auto.
      rename x into tlU, H3 into HU.
      rewrite HDefs', Recursion_Procs_1 in HU; auto.
      unfold IfEq in HU.
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (hd ps) this (S i) yy (If (S i) ? compare Then Send i this q;; Call (X + Gamma g + Gamma h + 3) Else Call (X + Gamma g + 2)) sI)).
      simpl; intro.
      assert (beval_on_state compare (update sI (S i) yy (sI (hd ps) xx)) (S i) = false).
      1: { 
        unfold beval_on_state, beval, MC_BEval.eval.
        rewrite update_read. rewrite update_read''. 2: discriminate.
        rewrite H2, H', Nat.eqb_neq. apply lt_neq; auto.
        eapply Hps, nth_In, nth_hd.
      }
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Else' Defs (S i) compare (Send i this q;; Call (X + Gamma g + Gamma h + 3)) (Call (X + Gamma g + 2)) _ H4)).
      simpl; clear H4; intro.
      assert (X <= X + Gamma g + 2 < X + Gamma (Recursion g h)).
      1: { split; simpl; auto with arith.  repeat (rewrite <- plus_assoc; apply plus_lt_compat_l); auto with arith. }
      set (sU := update sI (S i) yy (sI (hd ps) xx)).
      generalize (MCT_Trans _ _ _ _ _ HU (MCT_Step _ _ _ _ _ H3 (MCT_Step _ _ _ _ _ H4 (MCT_Refl _)))).
      clear HU H3 H4; intro.
      (* Setting up for the induction hypothesis on h *)
      assert (i+2 < i+3+Pi g) as Hi''; intros. auto with arith.
      assert (forall Y, X + Gamma g + 2 <= Y < X + Gamma g + 2 + Gamma h -> X <= Y < X + (Gamma g + Gamma h + 3)) as H''.
      1: {
        intros. inversion_clear H4; split; simpl.
        transitivity (X + Gamma g + 2); auto with arith.
        repeat rewrite <- plus_assoc.
        repeat rewrite <- plus_assoc in H7.
        rewrite (plus_comm 2) in H7.
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
      elim (diamond_5 _ _ _ _ _ _ _ _ (MCT_Trans _ _ _ _ _ HP (MCT_Trans _ _ _ _ _ HI H3)) Htl (eq_refl _)).
      intros. destroy H4. clear H4.
      elim IHd with (2+k) h Hh (S i::i::tl ps) (i+2) (i+3+Pi g) (X + Gamma g + 2) Defs sU x0 x; intros; auto.
      2: {
        elim (In_elim H4); intro.
        rewrite <- H7. rewrite <- plus_assoc. rewrite plus_comm; simpl.
        rewrite plus_comm; auto with arith.
        elim (In_elim H7); intro.
        rewrite H8; apply le_lt_trans with (p+0); auto with arith.
        transitivity i. apply Hps, In_tail; auto.
        apply le_lt_trans with (i+0); auto with arith.
      }
      2: {
        intro. elim (In_elim H4).
        apply lt_neq. rewrite plus_comm; auto.
        intro; elim (In_elim H7).
        apply lt_neq; rewrite plus_comm; simpl; auto.
        intro. apply (lt_irrefl i).
        transitivity (i+2). rewrite plus_comm; simpl; auto.
        apply Hps, In_tail; auto.
      }
      rename x1 into tlF; destroy H4. rename x1 into sF.
      (* After calling h *)
      repeat rewrite <- plus_assoc in H7; rewrite (plus_comm 2) in H7.
      repeat rewrite plus_assoc in H7.
      assert (X <= X + Gamma g + Gamma h + 2 < X + (Gamma g + Gamma h + 3)).
      1: { split; auto with arith.
        repeat rewrite <- plus_assoc; repeat apply plus_lt_compat_l; auto.
      }
      elim (Call_reduce Defs (X + Gamma g + Gamma h + 2) sF); auto; intros.
      rewrite HDefs', Recursion_Procs_2 in H9; auto.
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (i+2) this i xx (Send (S i) this (i+2);; Send (i+2) succ_this (S i);; Call (X + Gamma g + 1)) sF)).
      simpl. set (sF' := update sF i xx (sF (i+2) xx)); intros.
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (S i) this (i+2) xx (Send (i+2) succ_this (S i);; Call (X + Gamma g + 1)) sF')).
      simpl. set (sF'' := update sF' (i+2) xx (sF' (S i) xx)); intros.
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (i+2) succ_this (S i) xx (Call (X + Gamma g + 1)) sF'')).
      simpl. set (sF''' := update sF'' (S i) xx (S (sF'' (i+2) xx))); intros.
      exists (tlI ++ (tlU ++ L_Com (hd ps) (sI (hd ps) xx) (S i) :: L_Tau (S i) :: List.nil) ++ tlF ++ x1 ++ L_Com (i+2) (sF (i+2) xx) i :: L_Com (S i) (sF' (S i) xx) (i+2) :: L_Com (i+2) (S (sF'' (i+2) xx)) (S i) :: List.nil)%list, sF'''.
      repeat split; auto.
      ++ do 4 (eapply MCT_Trans; eauto).
         do 3 (eapply MCT_Step; eauto).
         constructor.
      ++ unfold sF''', sF'', sF'.
         repeat rewrite update_read.
         rewrite update_read'; auto.
         rewrite <- H4; auto. unfold sU. rewrite update_read''; auto. discriminate.
         rewrite <- (plus_comm 3); simpl; auto with arith.
         apply lt_neq; rewrite plus_comm; simpl; auto.
      ++ intros; unfold sF''', sF'', sF'.
         assert (hd ps < i). eapply Hps, nth_In, nth_hd.
         rewrite update_read.
         rewrite update_read'.
         2: { apply gt_neq; auto. }
         rewrite update_read'.
         2: { apply gt_neq. red; transitivity i; auto. rewrite plus_comm; simpl; auto. }
         rewrite update_read'. 2: apply gt_neq; auto.
         rewrite <- H4; auto with arith.
         2: { apply lt_neq; transitivity i; auto. rewrite plus_comm; simpl; auto. }
         unfold sU. rewrite update_read'; auto.
         apply gt_neq. red; transitivity i; auto.
  - elim (H0 _ (le_refl _)); clear H0; intros tl' Htl'.
    destroy Htl'.
    rename x into sF.
    assert (X <= X + Gamma g + 1 < X + Gamma (Recursion g h)).
    1: {
      split; auto with arith.
      simpl. repeat rewrite <- plus_assoc; repeat apply plus_lt_compat_l.
      rewrite plus_comm; auto with arith.
    }
    elim (Call_reduce Defs (X + Gamma g + 1) sF); auto; intros.
    rewrite HDefs', Recursion_Procs_1 in H3; auto.
    rename x into tlU, H3 into HU.
    unfold IfEq in HU.
    generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (hd ps) this (S i) yy (If (S i) ? compare Then Send i this q;; Call (X + Gamma g + Gamma h + 3) Else Call (X + Gamma g + 2)) sF)).
    simpl; intro.
    assert (beval_on_state compare (update sF (S i) yy (sF (hd ps) xx)) (S i) = true).
    1: { 
      unfold beval_on_state, beval, MC_BEval.eval.
      rewrite update_read. rewrite update_read''. 2: discriminate.
      rewrite H1, Htl', Nat.eqb_eq; auto. eapply Hps, nth_In, nth_hd.
    }
    generalize (MCP_To_intro _ _ _ _ _ _ (C_Then' Defs (S i) compare (Send i this q;; Call (X + Gamma g + Gamma h + 3)) (Call (X + Gamma g + 2)) _ H4)).
    set (sF' := update sF (S i) yy (sF (hd ps) xx)).
    simpl; intro.
    generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs i this q xx (Call (X + Gamma g + Gamma h + 3)) sF')).
    simpl; set (sF'' := update sF' q xx (sF' i xx)); intro.
    exists (t' ++ tl' ++ (tlU ++ L_Com (hd ps) (sF (hd ps) xx) (S i) :: L_Tau (S i) :: L_Com i (sF' i xx) q :: List.nil))%list, sF''; split.
    * do 3 (eapply MCT_Trans; eauto).
      do 3 (eapply MCT_Step; eauto).
      do 2 rewrite <- (plus_assoc X). constructor.
    * intros.
      unfold sF'', sF'.
      repeat rewrite update_read'. 2: apply gt_neq; auto with arith. 2: auto.
      rewrite Htl'; auto.
      unfold s0. rewrite update_read'. 2: apply gt_neq; auto.
      apply Hps'; auto. transitivity i; auto. apply lt_neq; auto.
+ (* Minimization *)
  set (Hd' := lt_S_n (depth h) d Hd).
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
  elim (diamond_5 _ _ _ _ _ _ _ _ (MCT_Trans _ _ _ _ _ H00 (MCT_Step _ _ _ _ _ H0 (MCT_Refl _))) Htl (eq_refl _)); intros.
  destroy H1. clear H1.
  elim IHd with (1+k) h Hd' (shiftin (i+1) ps) i (i+3) (X+1) Defs s0 x0 x; auto; intros.
  destroy H1. rename x1 into tlI, x2 into sI, H3 into HI.
  clear x x0 H2.
  replace (X + 1 + Gamma h) with (X + Gamma h + 1) in HI.
  2: repeat rewrite <- plus_assoc; rewrite <- (plus_comm 1); auto.
  generalize (MCT_Trans _ _ _ _ _ H00 (MCT_Step _ _ _ _ _ H0 HI)).
  clear H0 H00 HI; intro HI.
  assert (X <= X + Gamma h + 1 < X + Gamma (Minimization h)).
  1: { split; simpl; auto with arith. rewrite plus_assoc; auto with arith. }
  elim (Call_reduce Defs (X + Gamma h + 1) sI); intros; auto.
  rename x into tlh.
  rewrite HDefs', Minimization_Procs_1 in H2; auto.
  generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (i+1) zero (i+2) xx (IfEq (i+2) i (Send (i+1) this q;; Call (X + Gamma h + 2)) (Send (i+1) this (i+2);; Send (i+2) succ_this (i+1);; Call (X+1))) sI)).
  simpl. set (s1 := update sI (i+2) xx 0); intro.
  generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs i this (i+2) yy (Cond (i+2) compare (Send (i+1) this q;; Call (X + Gamma h + 2)) (Send (i+1) this (i+2);; Send (i+2) succ_this (i+1);; Call (X+1))) s1)).
  simpl. set (s2 := update s1 (i+2) yy (s1 i xx)); intro.
  generalize (MCT_Trans _ _ _ _ _ HI (MCT_Trans _ _ _ _ _ H2 (MCT_Step _ _ _ _ _ H3 (MCT_Step _ _ _ _ _ H4 (MCT_Refl _))))).
  set (P := Build_Program Defs (If i+2 ? compare Then (Send (i+1) this q;; Call (X + Gamma h + 2)) Else (Send (i+1) this (i+2);; Send (i+2) succ_this (i+1);; Call (X+1)))).
  set (tlP := ((tl0 ++ L_Com (i+2) 0 (i+1) :: tlI) ++ tlh ++ L_Com (i+1) 0 (i+2) :: (L_Com i (s1 i xx) (i+2) :: List.nil))%list).
  simpl in P; fold tlP P.
  unfold s1 in s2, tlP; unfold s1; clear H2 H3 H4 HI s1; intro HP.
  rename s2 into sP.
  elim (diamond_5 _ _ _ _ _ _ _ _ HP Htl (eq_refl _)); intros.
  destroy H2. rename x into tlP', x0 into sP'; clear H2.
  assert (forall s,
    (beval_on_state compare s (i+2) = true -> (P,s) --[(L_Tau (i+2) :: L_Com (i+1) (s (i+1) xx) q :: List.nil)%list]-->* (Build_Program Defs (Call (X+Gamma h+2)), update s q xx (s (i+1) xx)))
    /\ (beval_on_state compare s (i+2) = false -> forall tlP sP, (P,s) --[tlP]-->*(Build_Program Defs End,sP) -> exists tlP' s', (P,s) --[tlP']-->* (P,s') /\ (forall p, p < i -> s' p xx = s p xx) /\ length tlP' > 3)).
  clear H3 HP tlP sP tlh s0 tl0 Htl H1; split.
  - intros.
    apply (MCT_Step _ _ _ _ _ (MCP_To_intro _ _ _ _ _ _ (C_Then' Defs _ _ (Send (i+1) this q;; Call (X+Gamma h+2)) (Send (i+1) this (i+2);; Send (i+2) succ_this (i+1);; Call (X+1)) _ H1))).
    eapply MCT_Step. 2: constructor.
    replace (L_Com (i+1) (s0 (i+1) xx) q) with (forget (R_Com (i+1) (eval_on_state this s0 (i+1)) q xx)).
    2: auto. apply MCP_To_intro. apply C_Com'.
  - intros.
    generalize (MCP_To_intro _ _ _ _ _ _ (C_Else' Defs _ _ (Send (i+1) this q;; Call (X+Gamma h+2)) (Send (i+1) this (i+2);; Send (i+2) succ_this (i+1);; Call (X+1)) _ H1)).
    simpl; clear H1; intro.
    generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (i+1) this (i+2) xx (Send (i+2) succ_this (i+1);; Call (X+1)) s0)).
    simpl. set (s1 := update s0 (i+2) xx (s0 (i+1) xx)); intro.
    generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (i+2) succ_this (i+1) xx (Call (X+1)) s1)).
    simpl. set (s2 := update s1 (i+1) xx (S (s1 (i+2) xx))); intro.
    (* IH on H again *)
    elim (diamond_5 _ _ _ _ _ _ _ _ (MCT_Step _ _ _ _ _ H1 (MCT_Step _ _ _ _ _ H3 (MCT_Step _ _ _ _ _ H4 (MCT_Refl _)))) H2 (eq_refl _)); intros.
    destroy H5. clear H5.
    elim IHd with (1+k) h Hd' (shiftin (i+1) ps) i (i+3) (X+1) Defs s2 x0 x; auto; intros.
    destroy H5. rename x1 into tlh, x2 into sh, H7 into Hh.
    replace (X + 1 + Gamma h) with (X + Gamma h + 1) in Hh.
    2: repeat rewrite <- plus_assoc; rewrite <- (plus_comm 1); auto.
    generalize (MCT_Trans _ _ _ _ _ (MCT_Step _ _ _ _ _ H1 (MCT_Step _ _ _ _ _ H3 (MCT_Step _ _ _ _ _ H4 (MCT_Refl _)))) Hh).
    clear H1 H3 H4 Hh; intro Hh.
    elim (Call_reduce Defs (X + Gamma h + 1) sh); intros; auto.
    rename x1 into tlh'.
    rewrite HDefs', Minimization_Procs_1 in H1; auto.
    generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (i+1) zero (i+2) xx (IfEq (i+2) i (Send (i+1) this q;; Call (X + Gamma h + 2)) (Send (i+1) this (i+2);; Send (i+2) succ_this (i+1);; Call (X+1))) sh)).
    simpl. set (s3 := update sh (i+2) xx 0); intro.
    generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs i this (i+2) yy (Cond (i+2) compare (Send (i+1) this q;; Call (X + Gamma h + 2)) (Send (i+1) this (i+2);; Send (i+2) succ_this (i+1);; Call (X+1))) s3)).
    simpl. set (s4 := update s3 (i+2) yy (s1 i xx)); intro.
    generalize (MCT_Trans _ _ _ _ _ Hh (MCT_Trans _ _ _ _ _ H1 (MCT_Step _ _ _ _ _ H3 (MCT_Step _ _ _ _ _ H4 (MCT_Refl _))))).
    fold P; intro.
    do 2 eexists; split; eauto. split; simpl.
    * intros. unfold s3, s2.
      assert (i+2 <> p). apply gt_neq; red; transitivity i; auto. rewrite plus_comm; simpl; auto.
      repeat rewrite update_read'; auto.
      rewrite <- H5. 2: transitivity i; auto; rewrite plus_comm; auto. 2: apply lt_neq; auto.
      unfold s2, s1.
      rewrite update_read. repeat rewrite update_read'; auto.
      apply gt_neq; red; transitivity i; auto. rewrite plus_comm; auto.
    * repeat apply lt_n_S. repeat rewrite app_length; simpl.
      rewrite <- (plus_comm 2). rewrite plus_comm. simpl; auto with arith.
  - assert (forall n, length tlP' <= n -> exists s tl, (P,sP) --[ tl ]-->* (P,s) /\ beval_on_state compare s (i+2) = true /\ forall p, p<i -> s p xx = sP p xx).
    * intro. revert dependent tlP'. revert dependent sP. clearbody tlP; revert tlP sP'.
      rename n0 into z; induction z.
      ++ intros. exfalso. inversion H4. rewrite length_zero_iff_nil in H6.
         rewrite H6 in H3. inversion H3.
      ++ intros. case_eq (beval_on_state compare sP (i+2)).
         exists sP, List.nil; split; auto. constructor.
         intros. elim (H2 sP); clear H2; intros.
         elim (H6 H5 _ _ H3); clear H6; intros. destroy H6.
         elim (diamond_5a _ _ _ _ _ _ _ _ H7 H3 (eq_refl _)); intros.
         destroy H9. elim (IHz _ _ _ (MCT_Trans _ _ _ _ _ HP H7) _ H10); intros.
         destroy H12. exists x3, (x++x4)%list; repeat split; auto. eapply MCT_Trans; eauto.
         intros. rewrite H12, H8; auto.
         clear H11 H10 x2 H8 H7 x0 H2 H5.
         rewrite <- H9 in H4. apply le_S_n. transitivity (length x + length x1); auto.
         change (0 + length x1 < length x + length x1). apply plus_lt_compat_r.
         transitivity 3; auto with arith.
    * elim (H4 (length tlP')); auto. intros. clear H4. destroy H5.
      elim (H2 x); intros. clear H2 H8. generalize (H7 H6); clear H7; intros.
      exists (tlP ++ x0 ++ (L_Tau (i+2) :: L_Com (i+1) (x (i+1) xx) q :: List.nil))%list, (update x q xx (x (i+1) xx)).
      repeat split; auto. do 2 (eapply MCT_Trans; eauto). rewrite plus_assoc; auto.
      intros. rewrite update_read', H5; auto.
      assert (i+2 <> p). apply gt_neq; red. transitivity i; auto. rewrite plus_comm; simpl; auto.
      unfold sP. repeat rewrite update_read'; auto.
      rewrite <- H1; auto. unfold s0. rewrite update_read'; auto.
      apply gt_neq; red. transitivity i; auto. rewrite plus_comm; auto. transitivity i; auto. apply lt_neq; auto.
Qed.

Theorem Implementation_diverges : forall {n} (f:PRFunction n) ps q ns,
  ~In q ps -> diverges f ns -> 
  forall (s:State), (forall H, s ps[@H] xx = ns[@H]) ->
  forall c tl, (Implementation f ps q, s) --[tl]-->* c -> Main (fst c) <> End.
Proof.
intros.
red; intro.
set (Hd := Nat.lt_succ_diag_r (depth f)).
set (i := (S (max q (vmax ps)))).
induction c; induction a.
simpl in H3; rewrite H3 in H2; clear Main0 H3. rename b into s'.
elim (Implementation_aux_End f _ Hd ps q i 0 (Procedures (Implementation f ps q))) with s s' tl; intros; auto.
destroy H3. clear H2 s' tl. rename x into tl, x0 into s'.
elim (converges_Implementation_aux f _ Hd ps q i 0 (Procedures (Implementation f ps q)) ns (s' q xx)) with s s' tl; intros; auto.
+ destroy H5. rewrite H0 in H5. inversion H5.
+ apply all_pids_not_nil.
+ apply le_n_S. transitivity (vmax ps). apply vmax_In; auto. apply Nat.le_max_r.
+ apply le_n_S. apply Nat.le_max_l.
+ apply all_pids_not_nil.
+ apply le_n_S. transitivity (vmax ps). apply vmax_In; auto. apply Nat.le_max_r.
+ apply le_n_S. apply Nat.le_max_l.
+ unfold Implementation in H2. rewrite <- (MCP_ToStar_Defs_stable _ _ _ _ _ _ _ H2) in H2; auto.
Qed.

(*
Fixpoint seq_compose {m} {k} (fs:t (PRFunction m) k) (ps:t Pid m) (target init:nat) (X:RecVar)
  (Implement : forall (H:Fin.t k) (ps':t Pid m) (q' i':nat) (k':RecVar), RecVar -> Choreography) {struct fs} : RecVar -> Choreography.
(*
  match fs with
  | [] => End
  | f :: fs' => Implement m f d (Hd Fin.F1) ps target init ;; compose_args fs' ps (S target) (init + Pi f) Implement
  end.
*)
Proof.
destruct fs.
- apply (fun _ => End).
- pose (Implement (Fin.F1) ps target init X) as Ph.
  pose (seq_compose _ _ fs ps (S target) (init + Pi h) (X + Gamma h) (fun H => Implement (Fin.FS H))) as Pfs.
  apply (fun Y => if Y <? X + Gamma h then (Ph Y) else (Pfs Y)).
Defined.

Definition Implementation_aux {m} (f:PRFunction m) :
  t Pid m -> Pid -> nat -> RecVar -> RecVar -> Choreography
  :=
  PRFunction_recursion (fun m f => t Pid m -> Pid -> nat -> RecVar -> RecVar -> Choreography)
  (fun ps q _ X => Pack1 X (Send ps[@Fin.F1] zero q;; Call (S X)))
  (fun ps q _ X => Pack1 X (Send ps[@Fin.F1] succ_this q;; Call (S X)))
  (fun i j Hp ps q _ X => Pack1 X (Send ps[@Fin.of_nat_lt Hp] this q;; Call (S X)))
  (fun k m g fs Hfs Hg ps q init X => 
    (fun Y => if Y <? X + vsum (map Gamma fs)
      then seq_compose fs ps init (init+m) X Hfs Y
      else Hg (seq_labels init fs) q (init + m) (X + (vsum (map Gamma fs))) Y))
  (fun k g h Hg Hh ps q init X => 
    (fun Y =>
      if (Y <? X + Gamma g) then Hg (tl ps) init (init+3) X Y
      else if (RecVar_dec Y (X + Gamma g)) then
         Send (init+2) zero (S init);; Call (X + Gamma g + 1)
      else if (RecVar_dec Y (X + Gamma g + 1)) then 
         IfEq (S init) ps[@Fin.F1] (Send init this q;; Call (X + Gamma g + Gamma h + 3)) (Call (X + Gamma g + 2))
      else if (RecVar_dec Y (X + Gamma g + Gamma h + 2)) then
         Send (init+2) this init;; Send (S init) this (init+2);; Send (init+2) succ_this (S init);; Call (X + Gamma g + 1)
      else Hh (S init :: init :: tl ps) (init+2) (init+3 + Pi g) (X + Gamma g + 2) Y))
  (fun k h Hh ps q init X => 
    (fun Y =>
      if (RecVar_dec Y X) then
         Send (init+2) zero (init+1);; Call (X + 1)
      else if (RecVar_dec Y (X + Gamma h + 1)) then
         Send (init+1) zero (init+2);; IfEq (init+2) init
            (Send (init+1) this q;; Call (X + Gamma h + 2))
            (Send (init+1) this (init+2);; Send (init+2) succ_this (init+1);; Call (X + 1))
        else Hh (shiftin (init+1) ps) init (init+3) (X + 1) Y))
  m f.
*)

Require Import Sumbool.

Notation "A '&&&' B" := (sumbool_and _ _ _ _ A B).

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
