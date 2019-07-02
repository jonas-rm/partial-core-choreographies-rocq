Require Export List.
Require Export Coq.Lists.ListSet.
Require Export Sorting.Permutation.
Require Export Setoid.
Require Export Basic.

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

Module Type DecType.

Parameter t : Type.
Parameter eq_dec : forall x y:t, {x = y} + {x <> y}.

End DecType.

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

Module Type Eval (Expression Value : DecType).

Parameter eval : Expression.t -> Value.t -> Value.t.

End Eval.

(*
Definition set_add_pid := set_add eq_pid_dec.
Definition set_inter_pid := set_inter eq_pid_dec.

Definition eq_pidset (s:set Pid) (s':set Pid) : Prop := Permutation s s'.
*)

Module State (P V : DecType).

Module Pdec := DecidableType P.
Module Vdec := DecidableType V.

Definition Pid := P.t.
Definition Pid_dec := Pdec.eqb.
Definition Value := V.t.
Definition Value_dec := Vdec.eqb.

Definition State := Pid -> Value.

(** Equivalence of states up to a set of processes *)
Definition eq_state (P : list Pid) (s1: State) (s2: State) : Prop := 
  forall p, In p P -> s1 p = s2 p.

(*
Definition eq_state (P : set Pid) (s1: State) (s2: State) : Prop :=
set_fold_right (fun p => fun b => b /\ (s1 p = s2 p)) P True.
*)

Lemma eq_state_neq : forall p P s1 s2, 
  s1 p <> s2 p -> In p P -> ~ eq_state P s1 s2.
Proof.
intros. red. intros.
red in H1.
apply H1 in H0.
contradiction.
Qed.

Lemma eq_state_nil : forall s1 s2, eq_state nil s1 s2.
Proof.
intros. red. intros. contradiction.
Qed.

Lemma eq_state_cons : forall p P s1 s2, 
  s1 p = s2 p -> eq_state P s1 s2 -> eq_state (p::P) s1 s2.
Proof.
intros. red. intros.
inversion H1.
(* head *)
+ rewrite <- H2. assumption.
(* tail *)
+ apply H0, H2.
Qed.

Lemma eq_state_hd : forall p P s1 s2, 
  eq_state (p::P) s1 s2 -> s1 p = s2 p.
Proof.
intros. apply H, in_eq.
Qed.

Lemma eq_state_tl : forall p P s1 s2, 
  eq_state (p::P) s1 s2 -> eq_state P s1 s2.
Proof.
intros. red. intros. apply H, in_cons, H0.
Qed.

Lemma eq_state_cons_iff : forall p P s1 s2, 
  eq_state (p::P) s1 s2 <-> s1 p = s2 p /\ eq_state P s1 s2.
Proof.
split.
+ split; [apply eq_state_hd with P|apply eq_state_tl with p]; apply H.
+ intros. destruct H. apply eq_state_cons; auto.
Qed.

Lemma eq_state_app : forall P1 P2 s1 s2,
  eq_state P1 s1 s2 -> eq_state P2 s1 s2 -> eq_state (P1 ++ P2) s1 s2.
Proof.
intros. red. intros.
apply in_app_or in H1.
destruct H1.
(* p in P1 *)
+ apply H, H1.
(* p in P2 *)
+ apply H0, H1.
Qed.

Lemma eq_state_split : forall P1 P2 s1 s2,
  eq_state (P1 ++ P2) s1 s2 -> eq_state P1 s1 s2 /\ eq_state P2 s1 s2.
Proof.
intros. split; red; intros; apply H, in_or_app; auto.
Qed.

Lemma eq_state_dec : forall P s1 s2, 
  { eq_state P s1 s2 } + { ~eq_state P s1 s2}. 
Proof.
intros.
induction P.
(* P is empty *)
+ left. red. intros. contradiction.
(* a :: P *)
+ case IHP.
  - case_eq (Value_dec (s1 a) (s2 a)).
    * left. apply eq_state_cons; auto. apply (Vdec.eqb_eq); auto.
    * right. contradict H. rewrite not_false_iff_true. rewrite Vdec.eqb_eq. apply eq_state_hd with P, H.
  - right. contradict n. apply eq_state_tl with a, n.
Qed.

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

Definition update (s:State) (p:Pid) (v:Value) : State :=
  fun (q:Pid) => if (Pid_dec p q) then v else (s q).

Lemma update_read : forall (s:State) (p:Pid) (v:Value), update s p v p = v.
Proof.
  intros.
  unfold update.
  rewrite Pdec.eqb_refl; auto.
Qed.

Lemma update_read' : forall (s:State) (p q:Pid) (v:Value), p <> q -> update s p v q = s q.
Proof.
  intros.
  unfold update, Pid_dec.
  rewrite <- Pdec.eqb_neq in H; rewrite H; auto.
Qed.

Lemma update_update : forall (s:State) (p:Pid) (v1 v2:Value) (P : list Pid),
  eq_state P (update (update s p v2) p v1) (update s p v1).
Proof.
intros.
red.
unfold update.
unfold update.
intro q.
case_eq (Pid_dec p q); trivial.
Qed.

Definition eq_state_ext (s1 s2: State) : Prop := forall p, s1 p = s2 p.

Lemma update_update_ext : forall (s:State) (p:Pid) (v1 v2:Value),
  eq_state_ext (update (update s p v2) p v1) (update s p v1).
Proof.
intros.
red.
unfold update.
unfold update.
intro q.
case_eq (Pid_dec p q); trivial.
Qed.

Lemma update_independent : forall s p q e e', p<>q ->
  eq_state_ext (update (update s q e') p e) (update (update s p e) q e').
Proof.
red; intros.
unfold update.
case_eq (Pid_dec p p0); case_eq (Pid_dec q p0); auto; intros.
elim H; rewrite Pdec.eqb_eq in H0; rewrite Pdec.eqb_eq in H1.
transitivity p0; auto.
Qed.

Lemma update_not_in : forall (s:State) (p:Pid) (v:Value) (P:list Pid),
  ~In p P -> eq_state P s (update s p v).
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

End State.
