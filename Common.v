Require Export List.
Require Export ListSet.
Require Export Permutation.
Require Export Setoid.
Require Export Basic.

(** * Labels
    We require that there be exactly two labels (left and right), as this
    is the default practice in many choreography languages. *)

Section Labels.

Inductive Label : Type :=
 | left : Label
 | right : Label
.
Lemma eq_label_dec : forall (l l' : Label), { l = l' } + { l <> l' }.
Proof.
decide equality.
Qed.

Definition eqb_label (l l':Label) : bool :=
match l, l' with
 | left, left => true
 | right, right => true
 | _, _ => false
end.

End Labels.

(** * Decidable types
    Several structures need to be decidable.
    For some annoying reason, the standard library version does not work. *)

Module Type DecType.

Parameter t : Type.
Parameter eq_dec : forall x y:t, {x = y} + {x <> y}.

End DecType.

(** * Booleans as a decidable type *)

Module Bool : DecType.

Definition t := bool.
Definition eq_dec := bool_dec.

End Bool.

Module DecidableType (Import M:DecType).

Definition eqb (x y:t) := if (eq_dec x y) then true else false.

Notation "x '=?' y" := (eqb x y).

Lemma eqb_eq : forall x y, (x =? y) = true <-> x = y.
Proof.
intros; unfold eqb; elim (eq_dec x y); intros; split; auto.
intro; discriminate H.
Qed.

Lemma eqb_neq : forall x y, (x =? y) = false <-> x <> y.
Proof.
intros; split; intro.
+ contradict H. rewrite <- eqb_eq in H. rewrite H. discriminate.
+ case_eq (x =? y); auto. intro. rewrite eqb_eq in H0. elim H; auto.
Qed.

Lemma eqb_refl : forall x, (x =? x) = true.
Proof.
intro. rewrite eqb_eq. auto.
Qed.

Lemma eqb_sym : forall x y, (x =? y) = (y =? x).
Proof.
intros. case_eq (x =? y); intro; symmetry.
+ rewrite eqb_eq. symmetry. rewrite <- eqb_eq. auto.
+ rewrite eqb_neq. rewrite eqb_neq in H. auto.
Qed.

End DecidableType.

(** * Evaluation
    Evaluation is parameterized on the types of expressions and values.
    Decidability of expressions makes choreography equality decidable. *)

Module Type Eval (Expression Value : DecType).
Parameter eval : Expression.t -> Value.t -> Value.t.

End Eval.

(*
Module GState (P V X : DecType).

Module Pdec := DecidableType P.
Module Vdec := DecidableType V.
Module Xdec := DecidableType X.

Definition Pid := P.t.
Definition Pid_dec := Pdec.eqb.
Definition Value := V.t.
Definition Value_dec := Vdec.eqb.
Definition Var := X.t.
Definition Var_dec := Xdec.eqb.

Definition State := Pid -> Var -> Value.

(** Equivalence of states up to a set of processes *)
Definition eq_state (P : list Pid) (s: State) (s': State) : Prop := 
  forall p, In p P -> forall x, s p x = s' p x.

(*
Definition eq_state (P : set Pid) (s1: State) (s2: State) : Prop :=
set_fold_right (fun p => fun b => b /\ (s1 p = s2 p)) P True.
*)

Lemma eq_state_neq : forall p x P s s',
  s p x <> s' p x -> In p P -> ~ eq_state P s s'.
Proof.
intros. red. intros.
apply H; auto.
Qed.

Lemma eq_state_nil : forall s s', eq_state nil s s'.
Proof.
intros. red. intros. contradiction.
Qed.

Lemma eq_state_cons : forall p P s s',
  (forall x, s p x = s' p x) -> eq_state P s s' -> eq_state (p::P) s s'.
Proof.
intros. red. intros.
inversion H1.
(* head *)
+ rewrite <- H2. auto.
(* tail *)
+ apply H0, H2.
Qed.

Lemma eq_state_hd : forall p P s s',
  eq_state (p::P) s s' -> forall x, s p x = s' p x.
Proof.
intros. apply H, in_eq.
Qed.

Lemma eq_state_tl : forall p P s s',
  eq_state (p::P) s s' -> eq_state P s s'.
Proof.
intros. red. intros. apply H, in_cons, H0.
Qed.

Lemma eq_state_cons_iff : forall p P s s',
  eq_state (p::P) s s' <-> (forall x, s p x = s' p x) /\ eq_state P s s'.
Proof.
split.
+ split; [apply eq_state_hd with P|apply eq_state_tl with p]; apply H.
+ intros. destruct H. apply eq_state_cons; auto.
Qed.

Lemma eq_state_app : forall P P' s s',
  eq_state P s s' -> eq_state P' s s' -> eq_state (P ++ P') s s'.
Proof.
intros. red. intros.
apply in_app_or in H1.
destruct H1.
(* p in P *)
+ apply H, H1.
(* p in P' *)
+ apply H0, H1.
Qed.

Lemma eq_state_split : forall P P' s s',
  eq_state (P ++ P') s s' -> eq_state P s s' /\ eq_state P' s s'.
Proof.
intros. split; red; intros; apply H, in_or_app; auto.
Qed.

(* Not true: requires a finite set of variables.
Lemma eq_state_dec : forall P s1 s2,
  { eq_state P s1 s2 } + { ~eq_state P s1 s2}.
Proof.
intros.
induction P.
(* P is empty *)
+ left. red. intros. contradiction.
(* a :: P *)
+ case IHP; clear IHP; intro.
  - case_eq (Value_dec (s1 a) (s2 a)).
    * left. apply eq_state_cons; auto. apply (Vdec.eqb_eq); auto.
    * right. contradict H. rewrite not_false_iff_true. rewrite Vdec.eqb_eq. apply eq_state_hd with P, H.
  - right. contradict n. apply eq_state_tl with a, n.
Qed.
*)

Lemma eq_state_refl : forall P, reflexive _ (eq_state P).
Proof.
repeat (red; intros). auto.
Qed.

Lemma eq_state_sym : forall P, symmetric _ (eq_state P).
Proof.
repeat (red; intros).
apply symmetry, H, H0.
Qed.

Lemma eq_state_trans : forall P, transitive _ (eq_state P).
Proof.
red.
intros.
red.
red in H, H0.
intros.
specialize (H p H1).
specialize (H0 p H1).
rewrite H. apply H0.
Qed.

Add Parametric Relation P : State (eq_state P)
  reflexivity proved by (eq_state_refl P)
  symmetry proved by (eq_state_sym P)
  transitivity proved by (eq_state_trans P)
  as eq_state_rel.

(* TODO: Perhaps Add Parametric Morphism *)

Definition update (s:State) (p:Pid) (x:Var) (v:Value) : State :=
  fun (q:Pid) (y:Var) => if ((Pid_dec p q) && (Var_dec x y))
                         then v
                         else (s q y).

Lemma update_read : forall s p x v, update s p x v p x = v.
Proof.
  intros.
  unfold update.
  rewrite Pdec.eqb_refl, Xdec.eqb_refl.
  auto.
Qed.

Lemma update_read' : forall s p q x y v, p <> q ->
  update s p x v q y = s q y.
Proof.
  intros.
  unfold update, Pid_dec.
  rewrite <- Pdec.eqb_neq in H; rewrite H, andb_false_l; auto.
Qed.

Lemma update_read'' : forall s p x y v, x <> y ->
  update s p x v p y = s p y.
Proof.
  intros.
  unfold update, Var_dec.
  rewrite <- Xdec.eqb_neq in H; rewrite Pdec.eqb_refl, H, andb_false_r; auto.
Qed.

Lemma update_update : forall s p x v w P,
  eq_state P (update (update s p x w) p x v) (update s p x v).
Proof.
intros.
red.
unfold update.
unfold update.
intro q.
case_eq (Pid_dec p q); trivial.
intros; case_eq (Var_dec x x0); trivial.
Qed.

Lemma update_not_in : forall s p x v P,
  ~In p P -> eq_state P s (update s p x v).
Proof.
intros.
induction P.
+ apply eq_state_nil.
+ apply eq_state_cons_iff. 
  apply not_in_cons in H.
  destruct H.
  split.
  - unfold update. 
    case_eq (Pid_dec p a); auto. 
    intro H1. rewrite Pdec.eqb_eq in H1. 
    elim H. contradiction. 
  - apply IHP, H0.
Qed.

Definition eq_state_ext (s s': State) : Prop := forall p x, s p x = s' p x.

Lemma update_update_ext : forall s p x v1 v2,
  eq_state_ext (update (update s p x v2) p x v1) (update s p x v1).
Proof.
intros.
red.
unfold update.
intro q; elim Pid_dec; auto.
intro y; elim Var_dec; auto.
Qed.

Lemma update_independent : forall s p q x y v v', p <> q ->
  eq_state_ext (update (update s q y v') p x v) (update (update s p x v) q y v').
Proof.
red; intros.
unfold update.
case_eq (Pid_dec p p0); case_eq (Pid_dec q p0); auto; intros.
elim H; rewrite Pdec.eqb_eq in H0; rewrite Pdec.eqb_eq in H1.
transitivity p0; auto.
Qed.

Lemma update_independent' : forall s p x y v v', x <> y ->
  eq_state_ext (update (update s p y v') p x v) (update (update s p x v) p y v').
Proof.
red; intros.
unfold update.
elim Pid_dec; auto.
case_eq (Var_dec x x0); case_eq (Var_dec y x0); auto; intros.
elim H; rewrite Xdec.eqb_eq in H0; rewrite Xdec.eqb_eq in H1.
transitivity x0; auto.
Qed.

End GState.
*)

(** * Local states
    This is the state of a particular process. It maps the values in the
    process's local set of variables to values.
    The set of variables needs to be decidable. *)

Module LState (V X : DecType).

Module Vdec := DecidableType V.
Module Xdec := DecidableType X.

Definition Value := V.t.
Definition Value_dec := Vdec.eqb.
Definition Var := X.t.
Definition Var_dec := Xdec.eqb.

Definition State := Var -> Value.

(** ** Equivalence of states *)

Definition eq_state (s s': State) : Prop := forall x, s x = s' x.

Lemma eq_state_neq : forall x s s', s x <> s' x -> ~ eq_state s s'.
Proof.
intros. red. intros.
apply H; auto.
Qed.

(* Not true: requires a finite set of variables.
Lemma eq_state_dec : forall s1 s2,
  { eq_state s1 s2 } + { ~eq_state s1 s2}.
Proof.
intros.
induction P.
(* P is empty *)
+ left. red. intros. contradiction.
(* a :: P *)
+ case IHP; clear IHP; intro.
  - case_eq (Value_dec (s1 a) (s2 a)).
    * left. apply eq_state_cons; auto. apply (Vdec.eqb_eq); auto.
    * right. contradict H. rewrite not_false_iff_true. rewrite Vdec.eqb_eq. apply eq_state_hd with P, H.
  - right. contradict n. apply eq_state_tl with a, n.
Qed.
*)

Lemma eq_state_refl : reflexive _ eq_state.
Proof.
repeat (red; intros). auto.
Qed.

Lemma eq_state_sym : symmetric _ eq_state.
Proof.
repeat (red; intros).
apply symmetry, H.
Qed.

Lemma eq_state_trans : transitive _ eq_state.
Proof.
red.
intros.
red.
red in H, H0.
intros.
specialize (H x0).
specialize (H0 x0).
rewrite H. apply H0.
Qed.

Add Parametric Relation : State eq_state
  reflexivity proved by eq_state_refl
  symmetry proved by eq_state_sym
  transitivity proved by eq_state_trans
  as eq_state_rel.

(* TODO: Perhaps Add Parametric Morphism *)

(** ** Updating states *)

Definition update (s:State) (x:Var) (v:Value) : State :=
  fun (y:Var) => if (Var_dec x y) then v else (s y).

Lemma update_read : forall s x v, update s x v x = v.
Proof.
  intros.
  unfold update.
  rewrite Xdec.eqb_refl.
  auto.
Qed.

Lemma update_read'' : forall s x y v, x <> y ->
  update s x v y = s y.
Proof.
  intros.
  unfold update, Var_dec.
  rewrite <- Xdec.eqb_neq in H; rewrite H; auto.
Qed.

Lemma update_update : forall s x v w,
  eq_state (update (update s x w) x v) (update s x v).
Proof.
intros.
red.
unfold update.
intro y.
case_eq (Var_dec x y); trivial.
Qed.

Lemma update_independent' : forall s x y v v', x <> y ->
  eq_state (update (update s y v') x v) (update (update s x v) y v').
Proof.
red; intros.
unfold update.
case_eq (Var_dec x x0); case_eq (Var_dec y x0); auto; intros.
elim H; rewrite Xdec.eqb_eq in H0; rewrite Xdec.eqb_eq in H1.
transitivity x0; auto.
Qed.

End LState.

(** * Global states
    These are states for a choreography, or for a network as a whole:
    they map each process name to its state.
    Note that all processes are required to use the same sets of variables
    and values. *)

Module GState (P V X : DecType).

Module Import LSt := LState V X.

Module Pdec := DecidableType P.

Definition Pid := P.t.
Definition Pid_dec := Pdec.eqb.

Definition State := Pid -> LSt.State.

(** ** Equivalence of states
    We now define equivalence up to a set of processes: we are often only
    interested in some of those. *)

Definition eq_state (P : list Pid) (s: State) (s': State) : Prop := 
  forall p, In p P -> LSt.eq_state (s p) (s' p).

(*
Definition eq_state (P : set Pid) (s1: State) (s2: State) : Prop :=
set_fold_right (fun p => fun b => b /\ (s1 p = s2 p)) P True.
*)

Lemma eq_state_neq : forall p P (s s':State),
  ~LSt.eq_state (s p) (s' p) -> In p P -> ~ eq_state P s s'.
Proof.
intros. red. intros.
apply H; auto.
Qed.

Lemma eq_state_nil : forall s s', eq_state nil s s'.
Proof.
intros. red. intros. contradiction.
Qed.

Lemma eq_state_cons : forall p P s s',
  (LSt.eq_state (s p) (s' p)) -> eq_state P s s' -> eq_state (p::P) s s'.
Proof.
intros. red. intros.
inversion H1.
(* head *)
+ rewrite <- H2. auto.
(* tail *)
+ apply H0, H2.
Qed.

Lemma eq_state_hd : forall p P s s',
  eq_state (p::P) s s' -> LSt.eq_state (s p) (s' p).
Proof.
intros. apply H, in_eq.
Qed.

Lemma eq_state_tl : forall p P s s',
  eq_state (p::P) s s' -> eq_state P s s'.
Proof.
intros. red. intros. apply H, in_cons, H0.
Qed.

Lemma eq_state_cons_iff : forall p P s s',
  eq_state (p::P) s s' <-> (LSt.eq_state (s p) (s' p)) /\ eq_state P s s'.
Proof.
split.
+ split; [apply eq_state_hd with P|apply eq_state_tl with p]; apply H.
+ intros. destruct H. apply eq_state_cons; auto.
Qed.

Lemma eq_state_app : forall P P' s s',
  eq_state P s s' -> eq_state P' s s' -> eq_state (P ++ P') s s'.
Proof.
intros. red. intros.
apply in_app_or in H1.
destruct H1.
(* p in P *)
+ apply H, H1.
(* p in P' *)
+ apply H0, H1.
Qed.

Lemma eq_state_split : forall P P' s s',
  eq_state (P ++ P') s s' -> eq_state P s s' /\ eq_state P' s s'.
Proof.
intros. split; red; intros; apply H, in_or_app; auto.
Qed.

(* Not true: requires a finite set of variables.
Lemma eq_state_dec : forall P s1 s2,
  { eq_state P s1 s2 } + { ~eq_state P s1 s2}.
Proof.
intros.
induction P.
(* P is empty *)
+ left. red. intros. contradiction.
(* a :: P *)
+ case IHP; clear IHP; intro.
  - case_eq (Value_dec (s1 a) (s2 a)).
    * left. apply eq_state_cons; auto. apply (Vdec.eqb_eq); auto.
    * right. contradict H. rewrite not_false_iff_true. rewrite Vdec.eqb_eq. apply eq_state_hd with P, H.
  - right. contradict n. apply eq_state_tl with a, n.
Qed.
*)

Lemma eq_state_refl : forall P, reflexive _ (eq_state P).
Proof.
repeat (red; intros). auto.
Qed.

Lemma eq_state_sym : forall P, symmetric _ (eq_state P).
Proof.
repeat (red; intros).
apply symmetry, H, H0.
Qed.

Lemma eq_state_trans : forall P, transitive _ (eq_state P).
Proof.
red.
intros.
red.
red in H, H0.
intros.
specialize (H p H1).
specialize (H0 p H1).
rewrite H. apply H0.
Qed.

Add Parametric Relation P : State (eq_state P)
  reflexivity proved by (eq_state_refl P)
  symmetry proved by (eq_state_sym P)
  transitivity proved by (eq_state_trans P)
  as eq_state_rel.

(* TODO: Perhaps Add Parametric Morphism *)

(** ** Updating the state
    This function updates the local state of the given process. *)

Definition update (s:State) (p:Pid) (x:Var) (v:Value) : State :=
  fun (q:Pid) => if (Pid_dec p q) then (LSt.update (s p) x v)
                                  else (s q).

Lemma update_read : forall s p x v, update s p x v p x = v.
Proof.
  intros.
  unfold update.
  rewrite Pdec.eqb_refl.
  apply LSt.update_read; auto.
Qed.

Lemma update_read' : forall s p q x y v, p <> q ->
  update s p x v q y = s q y.
Proof.
  intros.
  unfold update, Pid_dec.
  rewrite <- Pdec.eqb_neq in H; rewrite H; auto.
Qed.

Lemma update_read'' : forall s p x y v, x <> y ->
  update s p x v p y = s p y.
Proof.
  intros.
  unfold update.
  rewrite Pdec.eqb_refl.
  apply LSt.update_read''; auto.
Qed.

Lemma update_update : forall s p x v w P,
  eq_state P (update (update s p x w) p x v) (update s p x v).
Proof.
intros.
red.
unfold update.
intro q.
case_eq (Pid_dec p q).
+ rewrite Pdec.eqb_refl; intros.
  apply LSt.update_update.
+ reflexivity.
Qed.

Lemma update_not_in : forall s p x v P,
  ~In p P -> eq_state P s (update s p x v).
Proof.
intros.
induction P.
+ apply eq_state_nil.
+ apply eq_state_cons_iff.
  apply not_in_cons in H.
  destruct H.
  split.
  - unfold update.
    case_eq (Pid_dec p a).
    2: reflexivity.
    intro H1. rewrite Pdec.eqb_eq in H1.
    elim H. contradiction.
  - apply IHP, H0.
Qed.

(** ** Extensional equivalence
    Equivalence of states not up to. *)

Definition eq_state_ext (s s': State) : Prop :=
  forall p, LSt.eq_state (s p) (s' p).

Lemma update_update_ext : forall s p x v1 v2,
  eq_state_ext (update (update s p x v2) p x v1) (update s p x v1).
Proof.
intros.
red.
unfold update.
rewrite Pdec.eqb_refl.
intro q; elim Pid_dec; auto.
+ apply LSt.update_update.
+ reflexivity.
Qed.

Lemma update_independent : forall s p q x y v v', p <> q ->
  eq_state_ext (update (update s q y v') p x v) (update (update s p x v) q y v').
Proof.
red; intros.
unfold update.
unfold Pid_dec.
rewrite <- Pdec.eqb_neq in H; rewrite H.
rewrite Pdec.eqb_sym in H; rewrite H.
case_eq (Pdec.eqb p p0); case_eq (Pdec.eqb q p0); try reflexivity; intros.
rewrite Pdec.eqb_eq in H0, H1.
rewrite Pdec.eqb_neq in H.
elim H; transitivity p0; auto.
Qed.

Lemma update_independent' : forall s p x y v v', x <> y ->
  eq_state_ext (update (update s p y v') p x v) (update (update s p x v) p y v').
Proof.
red; intros.
unfold update.
rewrite Pdec.eqb_refl.
elim Pid_dec.
+ apply LSt.update_independent'; auto.
+ reflexivity.
Qed.

End GState.
