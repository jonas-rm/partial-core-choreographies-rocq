Require Export Basic.
Require Export Common.
Require Export MC.
Require Import Sumbool.

Require Export Kleene.
Require Export Implementation.
Require Import Arith.

Module Export MC_Nat := Implementation.MC_Nat.

Notation "A '&&&' B" := (sumbool_and _ _ _ _ A B).

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
  ~In q ps -> (forall p, In p ps -> p < i) -> q < i ->
  (forall Y, X <= Y < X + Gamma f -> fst (Defs Y) <> List.nil) ->
  (forall Y, X <= Y < X + Gamma f -> snd (Defs Y) = Implementation_aux f d Hd ps q i X Y) ->
  forall (s:State), (forall H, s ps[@H] xx = ns[@H]) ->
  forall s' tl, s' q xx = y -> (forall p, p < i -> p <> q -> s' p xx = s p xx) ->
  (Build_Program Defs (Call X),s) --[tl]-->* (Build_Program Defs (Call (X + Gamma f)),s')
  -> converges f ns y.
(* Ugh *)
Admitted.

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
elim (converges_Implementation_aux f _ Hd ps q i 0 (Procedures (Implementation f ps q)) ns (s' q xx) H) with s s' tl; intros; auto.
+ rewrite H0 in H3. inversion H3.
+ apply le_n_S. transitivity (vmax ps). apply vmax_In; auto. apply Nat.le_max_r.
+ apply le_n_S. apply Nat.le_max_l.
+ apply all_pids_not_nil.
+ 




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
