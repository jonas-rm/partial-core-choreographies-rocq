Require Import Bool.
Require Import List.
Require Import Coq.Lists.ListSet.
Require Import Arith.
Require Import Sorting.Permutation.
Require Export MC.

Definition set_add_pid := set_add eq_nat_dec.
Definition set_union_pid := set_union eq_nat_dec.
Definition set_inter_pid := set_inter eq_nat_dec.


Definition pidseteq (s:set Pid) (s':set Pid) : Prop := Permutation s s'.

(** De Morgan law *)
Theorem deMorganNotOr : forall P Q : Prop,
  ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  unfold not.
  intros P Q PorQ_imp_false.
  split.
  - intros P_holds. apply PorQ_imp_false. left. assumption.
  - intros Q_holds. apply PorQ_imp_false. right. assumption.
Qed.

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

Lemma or_over_impl : forall (a b c:Prop), ((a \/ b) -> c) -> ((a -> c) /\ (b -> c)).
Proof.
intros a b c.
intros H.
split.
tauto.
tauto.
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
  pidseteq (p :: P ++ q :: nil) (q :: p :: P).
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
  ~(In p P) -> (pidseteq (set_add_pid p P) (p::P)).
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
apply (Permutation_NoDup (l := P ++ a :: Q) (l' := P ++ a :: rev Q)); auto.
apply Permutation_app_head.
apply Permutation_cons; auto.
apply Permutation_rev.
apply NoDup_remove_1 with a; auto.
Qed.

Lemma Permutation_NoDup : forall A, forall P Q: list A, Permutation P Q ->
                                                        NoDup P -> NoDup Q.
intros.
induction H; auto.
inversion_clear H0; apply NoDup_cons; auto.
intro; apply H1; apply Permutation_in with l'; auto.
apply Permutation_sym; auto.
inversion_clear H0; inversion_clear H1.
apply NoDup_cons.
intro; inversion_clear H1; auto.
apply H; left; auto.
apply NoDup_cons; auto.
intro; apply H; right; auto.
Qed.

Lemma set_union_pid_sets : forall (P Q:set Pid),
  (NoDup (P ++ Q)) ->
  (pidseteq (set_union_pid P Q) (set_union_pid Q P)).
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

