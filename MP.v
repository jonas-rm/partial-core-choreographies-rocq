Require Export MC.
Require Export Arith.
Require Import Coq.Arith.Arith. 

Module Import MC_Plus (P E V R: DecType) (Ev : Eval E V).

Module Import agh := MCBase P E V R Ev.

Inductive MCToStar_weighted : nat -> Configuration -> Configuration  -> Prop :=
  | MCT_W_Refl : forall {c}, MCToStar_weighted 0 c c
  | MCT_W_Step : forall {c1 c2 c3 n1 n2}, MCTo_weighted n1 c1 c2 -> MCToStar_weighted n2 c2 c3 -> MCToStar_weighted (S (n1+n2)) c1 c3
.

Lemma MCToStar_to_weighted : forall {c c'}, c --->* c' -> exists n, MCToStar_weighted n c c'.
Proof.
intros; induction H.
+ exists 0. constructor.
+ elim IHMCToStar. 
  elim (MCTo_to_weighted H). 
  intros.
  exists (S (x+x0)).
  apply (MCT_W_Step H1 H2).
Qed.

Lemma MCToStar_weighted_wf : forall (C: Choreography), WellFormed C -> forall n s C' s', MCToStar_weighted n (C, s) (C', s') -> WellFormed C'.
Proof.
(* aux lemmas *)
assert (MCToStar_weighted_Refl : forall n c1 c2, MCToStar_weighted n c1 c2 -> n = 0 -> c1=c2).
  intros. induction H.
  trivial.
  contradict H0.
  auto.
assert (MCToStar_weighted_wf' : forall n, forall k, k<=n -> forall (C: Choreography), WellFormed C -> forall s C' s', MCToStar_weighted k (C, s) (C', s') -> WellFormed C').
induction n.
  - intros.
    apply MCToStar_weighted_Refl in H1.
    inversion H1.
    rewrite H3 in H0. auto. apply le_n_0_eq in H. auto.
  - intros.
    inversion H1. 
    + apply MCToStar_weighted_Refl in H1.
      rewrite H5 in H0. auto. auto.    
    + rewrite <- H4 in H.
      apply le_S_n in H.
      destruct c2.
      apply (MCTo_weighted_to) in H2.
      apply (MCTo_wf C H0) in H2.    
      rewrite <- Nat.add_comm in H.
      rewrite <- Nat.le_add_r in H.
      apply IHn in H3; trivial.
(* end *)
- intros C HC n.
apply (MCToStar_weighted_wf' n n); auto.
Qed.

(** Transitive reduction preserve well-formedness. *)
Lemma MCToStar_wf : forall C, WellFormed C -> forall s C' s',
  (C,s) --->* (C',s') -> WellFormed C'.
Proof.
intros.
elim (MCToStar_to_weighted H0). intro n.
apply MCToStar_weighted_wf. assumption.
Qed.