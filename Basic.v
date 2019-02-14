Require Import Bool.
Require Import List.
Require Import Sorting.Permutation.

(** De Morgan law *)
Lemma deMorganNotOr : forall P Q : Prop,
  ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  unfold not.
  intros P Q PorQ_imp_false.
  split.
  - intros P_holds. apply PorQ_imp_false. left. assumption.
  - intros Q_holds. apply PorQ_imp_false. right. assumption.
Qed.

Lemma or_over_impl : forall (a b c:Prop), ((a \/ b) -> c) -> ((a -> c) /\ (b -> c)).
Proof.
intros a b c.
intros H.
split.
tauto.
tauto.
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
