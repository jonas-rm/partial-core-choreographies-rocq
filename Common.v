Require Import FunctionalExtensionality.
Require Import Bool.
Require Import List.
Require Import Coq.Lists.ListSet.
Require Import Arith.
Require Import Sorting.Permutation.
Require Import Nat.
Require Import EqNat.
Require Import PeanoNat.
Local Open Scope nat_scope.

Require Import Basic.

Section Labels.

Inductive Label : Type :=
 | left : Label
 | right : Label
.

End Labels.

Section Expressions.

Definition Value := nat.

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
match (e, e') with
 | (this, this) => true
 | (zero, zero) => true
 | (succ_this, succ_this) => true
 | (_, _) => false
end.

End Expressions.

Section Pids.

Definition Pid := nat.

Definition eqb_pid := Nat.eqb.

Lemma eq_pid_dec : forall (p p':Pid), { p = p' } + { p <> p' }.
Proof.
decide equality.
Qed.

Definition set_add_pid := set_add eq_nat_dec.
Definition set_union_pid := set_union eq_nat_dec.
Definition set_inter_pid := set_inter eq_nat_dec.

Definition eq_pidset (s:set Pid) (s':set Pid) : Prop := Permutation s s'.

(* Lemma set_union_pid_el : forall (p:Pid) (P:set Pid), ~(In p P) -> set_add eq_nat_dec p (P ++ nil) = (P ++ p::nil).
Proof.
intros.
 *)

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
induction Nat.eq_dec.
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
  (set_union eq_nat_dec nil P) = (rev P).
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
destruct Nat.eq_dec.
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

End Pids.

Section Store.

Definition Store := Pid -> Value.

Definition evaluate (e:Expr) (s:Store) (p:Pid) : Value :=
match e with
 | zero => 0
 | this => s p
 | succ_this => S (s p)
end.

Definition update (s:Store) (p:Pid) (v:Value) : Store :=
fun (q:Pid) => if (p =? q) then v else (s q)
.

Lemma update_read : forall (s:Store) (p:Pid) (v:Value),
  update s p v p = v.
Proof.
  intros.
  unfold update.
  rewrite <- beq_nat_refl; auto.
Qed.

Lemma update_monotonicity : forall (s:Store) (p q:Pid) (v:Value),
  p <> q -> update s p v q = s q.
Proof.
intros.
unfold update.
case_eq (p =? q); auto.
intro.
generalize (beq_nat_true _ _ H0); intros.
elim H; auto.
Qed.

Lemma update_update : forall (s:Store) (p:Pid) (v1 v2:Value),
  update (update s p v2) p v1 = update s p v1.
Proof.
intros.
unfold update.
apply FunctionalExtensionality.functional_extensionality. (* TODO avoid this *)
unfold update; intro q.
case_eq (p =? q); trivial.
Qed.

End Store.
