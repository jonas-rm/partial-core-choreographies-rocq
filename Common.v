Require Import FunctionalExtensionality.
Require Import Nat.
Require Export List.
Require Export Coq.Lists.ListSet.
Require Export Sorting.Permutation.
Require Export Setoid.
Local Open Scope nat_scope.

Require Import Basic.

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

Section Expressions.

Definition Value := nat.

Lemma eq_value_dec : forall (e e' : Value), { e = e' } + { e <> e' }.
Proof.
decide equality.
Qed.


Inductive Expr : Type :=
 | this : Expr
 | zero : Expr
 | succ_this : Expr
.

Lemma eq_expr_dec : forall (e e' : Expr), { e = e' } + { e <> e' }.
Proof.
decide equality.
Qed.

Definition eqb_expr (e:Expr) (e':Expr) : bool :=
match e, e' with
 | this, this => true
 | zero, zero => true
 | succ_this, succ_this => true
 | _, _ => false
end.

End Expressions.

Section Pids.

Definition Pid := nat.

Definition eq_pid := Nat.eq.

Definition eqb_pid := Nat.eqb.

Lemma eq_pid_dec : forall (p p':Pid), { p = p' } + { p <> p' }.
Proof.
decide equality.
Qed.

Definition set_add_pid := set_add eq_pid_dec.
Definition set_union_pid := set_union eq_pid_dec.
Definition set_inter_pid := set_inter eq_pid_dec.

Definition eq_pidset (s:set Pid) (s':set Pid) : Prop := Permutation s s'.

(*
Lemma set_add_pid_char :
  forall (p:Pid) (P:set Pid),
  ~(In p P) -> (set_add_pid p P) = P ++ p::nil.
Proof.
intros.
induction P.
easy.
simpl in H.
apply deMorganNotOr in H.
inversion H.
set (myH := IHP H1).
simpl.
rewrite myH.
induction eq_pid_dec.
symmetry in a0.
contradiction.
trivial.
Qed.

Lemma not_in_rev_pid : forall (p:Pid) (P:set Pid), ~(In p P) -> ~(In p (rev P)).
Proof.
intros.
red.
red in H.
induction P.
trivial.
simpl.
simpl in H.
apply or_over_impl in H.
inversion_clear H.
set (H3 := (IHP H1)).
intros.
apply in_app_iff in H.
inversion H.
apply (H3 H2).
inversion H2.
apply (H0 H4).
inversion H4.
Qed.

Lemma set_union_pid_nil :
  forall (P:set Pid), (NoDup P) ->
  (set_union eq_pid_dec nil P) = (rev P).
Proof.
intros.
induction P.
trivial.
simpl.
inversion H.
rewrite IHP.
apply set_add_pid_char.
set (myH := (in_rev P a)).
inversion myH.
apply (not_in_rev_pid a P H2).
trivial.
Qed.

Lemma pidseteq_perm :
  forall (p q:Pid) (P:set Pid),
  eq_pidset (p :: P ++ q :: nil) (q :: p :: P).
Proof.
intros.
red.
induction P.
simpl (p :: nil ++ q :: nil).
apply perm_swap.
simpl (p :: (a :: P) ++ q :: nil).
apply Permutation_sym.
rewrite perm_swap.
apply perm_skip.
rewrite perm_swap.
apply perm_skip.
apply Permutation_cons_append.
Qed.

Lemma set_union_pid_el :
  forall (p:Pid) (P:set Pid),
  ~(In p P) -> (eq_pidset (set_add_pid p P) (p::P)).
Proof.
intros.
induction P.
easy.
simpl.
simpl in H.
apply deMorganNotOr in H.
inversion H.
destruct eq_pid_dec.
rewrite e in H0.
contradiction.
set (myH := IHP H1).
rewrite set_add_pid_char.
rewrite set_add_pid_char in myH.
apply pidseteq_perm.
trivial.
trivial.
Qed.

Lemma nodup_pid_app :
  forall (P Q:set Pid),
  (NoDup (P ++ Q)) -> (NoDup P) /\ (NoDup Q).
Proof.
intros.
induction P.
split.
apply NoDup_nil.
trivial.
split.
simpl in H.
apply NoDup_cons_iff in H.
inversion_clear H.
apply NoDup_cons.
(* ~ In a (P ++ Q) -> ~ In a P *)
set (myH := (in_or_app P Q a)).
apply or_over_impl in myH; inversion_clear myH.
intro.
apply H0.
apply in_or_app.
auto.
elim IHP; auto.
simpl in H.
inversion H.
elim IHP; auto.
Qed.

Lemma set_union_pid_char : forall (P Q:set Pid),
  (NoDup (P ++ Q)) ->
  (set_union_pid P Q) = P ++ rev Q.
Proof.
intros.
elim (nodup_pid_app _ _ H); intros.
induction Q.
simpl.
symmetry; apply app_nil_r.
simpl.
inversion_clear H1; rewrite IHQ; auto.
rewrite set_add_pid_char; auto.
rewrite app_assoc; auto.
apply NoDup_remove_2.
apply (Permutation_NoDup Pid (P ++ a :: Q) (P ++ a :: rev Q)); auto.
apply Permutation_app_head.
apply Permutation_cons; auto.
apply Permutation_rev.
apply NoDup_remove_1 with a; auto.
Qed.

Lemma set_union_pid_sets : forall (P Q:set Pid),
  (NoDup (P ++ Q)) ->
  (eq_pidset (set_union_pid P Q) (set_union_pid Q P)).
Proof.
intros.
repeat rewrite set_union_pid_char; auto.
apply Permutation_trans with (rev P ++ Q).
apply Permutation_app.
apply Permutation_rev.
symmetry; apply Permutation_rev.
apply Permutation_app_comm.
apply Permutation_NoDup with (P ++ Q); auto.
apply Permutation_app_comm.
Qed.
*)

End Pids.

Section State.

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
+ assert (SHP := eq_value_dec (s1 a) (s2 a)).
  case IHP, SHP.
  - left. apply eq_state_cons; assumption.
  - right. contradict n. apply eq_state_hd with P, n.
  - right. contradict n. apply eq_state_tl with a, n.
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
  as eq_setate_rel.

(* TODO: Perhaps Add Parametric Morphism *)

(** Expression evaluation given a value for the place-holder this *)
Definition evaluate_on_value (e:Expr) (v:Value) : Value :=
match e with
 | zero => 0
 | this => v
 | succ_this => S v
end.

(** Expression evaluation on the state of a process *)
Definition evaluate_on_state (e:Expr) (s:State) (p:Pid) : Value := evaluate_on_value e (s p).

Definition update (s:State) (p:Pid) (v:Value) : State :=
  fun (q:Pid) => if (p =? q) then v else (s q).

Lemma update_read : forall (s:State) (p:Pid) (v:Value),
  update s p v p = v.
Proof.
  intros.
  unfold update.
  rewrite <- beq_nat_refl; auto.
Qed.

Lemma read_update : forall s p q v e, p<>q -> evaluate_on_state e (update s q v) p = evaluate_on_state e s p.
intros.
assert (q<>p); auto.
induction e; simpl; unfold update; auto; rewrite <- Nat.eqb_neq in H0; rewrite H0; auto.
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
    case_eq (p =? a); auto. 
    intro H1. apply beq_nat_true in H1. 
    elim H. contradiction. 
  - apply IHP, H0.
Qed.

Lemma update_update : forall (s:State) (p:Pid) (v1 v2:Value) (P : list Pid),
  eq_state P (update (update s p v2) p v1) (update s p v1).
Proof.
intros.
red.
unfold update.
unfold update.
intro q.
case_eq (p =? q); trivial.
Qed.

(* Lemma updrate_swap :  forall (s: State) *)

Fixpoint list_to_state (l : list (Pid * Value)) : State :=
match l with
| nil => fun _ => 0
| (p,v)::l' => update (list_to_state l') p v
end.

(* Eval compute in (list_to_state ((0,0)::(1,2)::(0,1)::nil)). *)

Definition eq_state_ext (s1 s2: State) : Prop := forall p, s1 p = s2 p.

Lemma update_update_ext : forall (s:State) (p:Pid) (v1 v2:Value),
  eq_state_ext (update (update s p v2) p v1) (update s p v1).
Proof.
intros.
red.
unfold update.
unfold update.
intro q.
case_eq (p =? q); trivial.
Qed.

Lemma update_independent : forall s p q e e', p<>q ->
  eq_state_ext (update (update s q e') p e) (update (update s p e) q e').
Proof.
red; intros.
unfold update.
case_eq (p =? p0); case_eq (q =? p0); auto; intros.
elim H; rewrite Nat.eqb_eq in H0; rewrite Nat.eqb_eq in H1.
transitivity p0; auto.
Qed.

End State.