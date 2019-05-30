Require Import MC.
Require Import Arith.
Require Import Coq.Arith.Arith. 
Require Import Coq.Lists.List.

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

(** The transitive and reflexive closure of reductions preserve well-formedness. *)
Lemma MCToStar_wf : forall C, WellFormed C -> forall s C' s',
  (C,s) --->* (C',s') -> WellFormed C'.
Proof.
intros.
elim (MCToStar_to_weighted H0). intro n.
apply MCToStar_weighted_wf. assumption.
Qed.

Fixpoint MC_Precongr_ctx (l : list (RecVar*Choreography)) (C1 C2 : Choreography) : Prop :=
let CTX := (fun C => fold_right (fun D C' => match D with | (X,CX) => (Def X == CX In C') end) C l)
in MC_Precongr (CTX C1) (CTX C2).

Definition terminated_ctx (l : list (RecVar*Choreography)) (C:Choreography) : Prop := MC_Precongr_ctx l C End.

Lemma terminated_nil : forall C, terminated C <-> terminated_ctx nil C.
Proof.
intro C. split; intro H; apply H.
Qed.

Lemma terminated_cons : forall C l D, terminated_ctx l C -> terminated_ctx (D::l) C.
Proof.
intros.
induction l; compute; compute in H; destruct D; apply CtxRec'; assumption.
Qed.

Lemma terminated_app : forall C l l', terminated_ctx l C -> terminated_ctx (l'++l) C.
Proof.
intros.
induction l'.
simpl. assumption.
simpl. apply terminated_cons. assumption.
Qed.

(*
Lemma terminated_ctx_dec : forall C l, {terminated_ctx l C} + {~terminated_ctx l C}.
Proof.
intro C. induction C.
- left. induction l.
  constructor.
  apply terminated_cons. assumption.
- admit.
- induction l.
  right. apply eta_not_terminated.
  right. compute.
  
Qed.
*)

Fixpoint terminated_ctx_char (C:Choreography) (l : list (RecVar*Prop)) : Prop :=
match C with
| End => True
| Call X => List.In (X,True) l
| Interaction eta C' => False
| Cond p q C1 C2 => False
| Rec X C1 C2 => 
  let l1 := ((X,True)::l) in
  let l2 := ((X,False)::l) in
  (terminated_ctx_char C1 l1 /\ terminated_ctx_char C2 l1)
  \/ (~terminated_ctx_char C1 l2 /\ terminated_ctx_char C2 l2)
end.


Lemma terminated_ctx_base_char : forall C l, terminated_ctx C
  -> (forall eta C', C <> (eta; C'))
  /\ (forall p q C1 C2, C <> If p == q Then C1 Else C2)
  /\ (forall X, C <> Call X).
Proof.

Lemma terminated_if : forall C, terminated_ctx C nil -> terminated C.
Proof.
intro C. 
induction C; intro H.
- simpl in H. red. constructor.
- contradict H.
- contradict H.
- contradict H.
- elim H. 
  + intro. 

Qed.

Lemma terminated_onlyif : forall C, terminated C  -> terminated_ctx C nil.
Proof.

Qed.