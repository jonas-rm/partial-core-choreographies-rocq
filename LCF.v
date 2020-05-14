Require Export Basic.
Require Export Common.
Require Export MC.
Require Import Sumbool.

Require Export Kleene.
Require Export Implementation.

Module Export MC_Nat := Implementation.MC_Nat.

Notation "A '&&&' B" := (sumbool_and _ _ _ _ A B).

(** MOVE ME *)

Lemma seq_labels_lt : forall x {m k} (fs:t (PRFunction m) k) n,
  In x (seq_labels n fs) -> n <= x < n + k.
Proof.
induction k.
+ refine (@case0 _ _ _); simpl; intros. inversion H.
+ intro. revert k fs IHk. refine (@caseS _ _ _); simpl; intros.
  elim (In_elim H); clear H; intro.
  - rewrite H; split; auto with arith.
    rewrite <- plus_Snm_nSm. apply le_plus_l.
  - elim (IHk _ _ H); intros.
    split; auto with arith. rewrite <- plus_Snm_nSm; auto.
Qed.

(** The stuff. *)
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
  intro; apply H. eapply In_nth; eauto.
+ (* Successor *)
  simpl. unfold Pack1; simpl.
  elim RecVar_dec; repeat split; simpl; auto.
  intro; apply H. eapply In_nth; eauto.
+ (* Projection *)
  simpl. unfold Pack1; simpl.
  elim RecVar_dec; repeat split; simpl; auto.
  intro; apply H. eapply In_nth; eauto.
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
    * apply lt_neq. transitivity n; auto. apply H0. apply In_nth with Fin.F1; auto.
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
    * intro. elim (shiftin_elim _ _ H5); intro. apply (lt_irrefl n); rewrite <- H6 at 2; auto.
      apply (lt_irrefl n); auto.
    * intros; transitivity (S (S n)). 2: rewrite plus_comm; simpl; auto.
      elim (shiftin_elim _ _ H5); auto with arith. intro. rewrite <- H6; auto.
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

Lemma all_pids_not_nil : forall n, all_pids n <> List.nil.
Proof. intros; case n; discriminate. Qed.

Lemma Implementation_Procs_Vars_not_nil : forall {n} (f:PRFunction n) ps q X,
  Vars (Implementation f ps q) X <> List.nil.
Proof.
intros. unfold Vars; simpl.
apply all_pids_not_nil.
Qed.

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

Lemma within_Xs_incl : forall C Xs Ys, (forall X, List.In X Xs -> List.In X Ys) ->
  within_Xs Xs C -> within_Xs Ys C.
Proof.
induction C; simpl; auto.
+ intros. inversion_clear H0. split; eauto.
+ intros. inversion_clear H0. split; eauto.
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
intro; apply H. eapply In_nth; eauto.
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
intro; apply H. eapply In_nth; eauto.
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
intro; apply H. eapply In_nth; eauto.
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
intro; apply H. eapply In_nth; eauto.
Qed.
*)

Lemma vmax_In : forall n v p, In p v -> p <= vmax (n:=n) v.
Proof.
induction n.
* refine (@case0 _ _ _); simpl; intros. inversion H.
* intro; revert n v IHn; refine (@caseS _ _ _); simpl; intros.
  elim (In_elim H); intro.
  - rewrite H0. apply Nat.le_max_l.
  - transitivity (vmax t); auto. apply Nat.le_max_r.
Qed.

Lemma implements_WF : forall {n} (f:PRFunction n) ps q,
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
