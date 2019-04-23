Require Import Bool.
Require Import List.
Require Import Coq.Lists.ListSet.
Require Import Arith.
Require Import Sorting.Permutation.
Require Import Common.
Require Import MC.
Require Import Basic.
Require Import FunInd.

Local Open Scope nat_scope.

Section Syntax.

Inductive Behaviour : Type :=
 | End : Behaviour
 | Send : Pid -> Expr -> Behaviour -> Behaviour
 | Recv : Pid -> Behaviour -> Behaviour
 | Sel : Pid -> Label -> Behaviour -> Behaviour
 | Branching : Pid -> (Label -> (Behaviour + unit)) -> Behaviour
 | Cond : Pid -> Behaviour -> Behaviour -> Behaviour
.

Definition Branch : Set := (Behaviour + unit).

Inductive Network : Type :=
 | Empty : Network
 | Process : Pid -> Value -> Behaviour -> Network
 | Par : Network -> Network -> Network
.

(** The process names in a network *)
Fixpoint SPpn (N:Network) : list Pid :=
match N with
| Empty => nil
| Process p v B => (p :: nil)
| Par N N' => (SPpn N) ++ (SPpn N')
end
.

(** A well-formed network has no duplicate process names and no self-communications. *)
Definition WellFormedNetwork (N:Network) : Prop := NoDup(SPpn N).
(* Enrich with no self-communications *)

End Syntax.

Delimit Scope SP_scope with SP.

Bind Scope SP_scope with Behaviour.
Bind Scope SP_scope with Network.

Notation "N | N'" := (Par N N') (at level 202, right associativity) : SP_scope.
Notation "p [ v , B ]" := (Process p v B) (at level 201, v at level 9, no associativity) : SP_scope.
Notation "p ! e ; B" := (Send p e B) (at level 60, e at level 9, right associativity) : SP_scope.
Notation "p ? ; B" := (Recv p B) (at level 60, right associativity) : SP_scope.
Notation "p + l ; B" := (Sel p l B) (at level 49, l at level 9, right associativity) : SP_scope.
Notation "p & f" := (Branching p f) (at level 60, no associativity) : SP_scope.
Notation "'If' p 'Then' B1 'Else' B2" := (Cond p B1 B2) (at level 60) : SP_scope.
Notation "'bnil'" := (End) : SP_scope.
Notation "'nnil'" := (Empty) : SP_scope.

(* 
Check (Empty | Empty)%SP.
Check (0 [1, bnil])%SP.
Check (Empty | 0 [1, bnil])%SP.
Check (If 0 Then bnil Else bnil)%SP.
Check (0!zero; 0?; 1+left; bnil)%SP.
*)

Section Semantics.

(** Precongruence of behaviours. Will be used to define unfolding. *)
Definition PrecongrB := (eq (A := Behaviour)).

(** Sugar for (value, behaviour). Makes the definition of congr readable. *)
Definition ProcessTerm : Type := Value * Behaviour.

(** Returns the value and behaviour of process p in a network, if the process exists in the network. *)
Fixpoint get_proc (p:Pid) (N:Network) : option ProcessTerm :=
match N with
| nnil%SP => None
| (q [ v, B ])%SP => if (p =? q) then Some (v, B) else None
| (Par N1 N2) => match (get_proc p N1), (get_proc p N2) with
                  | Some (v,B), _ => Some (v,B)
                  | None, Some (v,B) => Some (v,B)
                  | _, _ => None
                  end
end.

(** get_proc makes sense wrt SPpn. Case 1/2: the process is not there. *)
Lemma get_proc_None : forall (p:Pid) (N:Network), ~(In p (SPpn N)) -> (get_proc p N) = None.
intros.
induction N.
+ auto.
+ simpl.
  simpl SPpn in H.
  apply not_in_cons in H.
  destruct H.
  rewrite <- Nat.eqb_eq in H.
  rewrite not_true_iff_false in H.
  rewrite H.
  trivial.
+ simpl in H.
  simpl.
  rewrite IHN1.
  rewrite IHN2.
  auto.
  intro; apply H.
  apply in_or_app; auto.
  intro; apply H.
  apply in_or_app; auto.
Qed.

(** get_proc makes sense wrt SPpn. Case 2/2: the process is there. *)
Lemma get_proc_Some : forall (p:Pid) (N:Network), In p (SPpn N) -> exists T, (get_proc p N) = Some T.
induction N; simpl; intros.
+ inversion H.
+ inversion_clear H.
  symmetry in H0; rewrite <- Nat.eqb_eq in H0.
  rewrite H0.
  exists (v,b); auto.
  inversion H0.
+ elim (in_dec eq_pid_dec p (SPpn N1)); intros.
  elim IHN1; auto; intros.
  rewrite H0.
  exists x; destruct x; auto.
  rewrite (get_proc_None _ _ b).
  elim (in_app_or _ _ _ H); intros.
  elim b; auto.
  elim IHN2; auto; intros.
  rewrite H1.
  exists x; destruct x; auto.
Qed.

Lemma Some_get_proc : forall (p:Pid) (N:Network) T, (get_proc p N) = Some T -> In p (SPpn N).
intros.
elim (in_dec eq_pid_dec p (SPpn N)); auto.
intro.
rewrite get_proc_None in H; auto.
inversion H.
Qed.

Inductive Precongr : Network -> Network -> Prop :=
 | Lift p v B B' : PrecongrB B B' -> Precongr (p [v, B])%SP (p [v, B'])%SP
 | Refl N : Precongr N N
 | Sym N1 N2 : Precongr (N1 | N2) (N2 | N1)
 | AssocL N1 N2 N3 : Precongr (N1|(N2|N3)) ((N1|N2)|N3)
 | AssocR N1 N2 N3 : Precongr ((N1|N2)|N3) (N1|(N2|N3))
 | CtxL N1 N2 N3 (P1:Precongr N1 N2) : Precongr (N1 | N3) (N2 | N3)
 | CtxR N1 N2 N3 (P1:Precongr N2 N3) : Precongr (N1 | N2) (N1 | N3)
 | Trans N1 N2 N3 (P1:Precongr N1 N2) (P2:Precongr N2 N3) : Precongr N1 N3
 | PZero p v : Precongr (Process p v End) Empty
 | NZero N : Precongr (Par N Empty) N
.

Definition PrecongrPT (P P': option ProcessTerm) : Prop :=
match P, P' with
| Some (v, B), Some (v', B')%SP => if v =? v' then PrecongrB B B' else False
| Some (v, B), None => PrecongrB B bnil%SP
| None, None => True
| _, _ => False
end.

Lemma PrecongrPT_sym_Some : forall (P:ProcessTerm), PrecongrPT (Some P) (Some P).
intros.
simpl.
destruct P.
case_eq (v =? v).
- intros.
  reflexivity.
- intro.
  rewrite Nat.eqb_neq in H.
  contradiction.
Qed.

Lemma PrecongrPT_sym : forall (op: option ProcessTerm), PrecongrPT op op.
intros.
case op.
- apply PrecongrPT_sym_Some.
- simpl; auto.
Qed.

Definition Precongr_op (N N': Network) : Prop := forall p, PrecongrPT (get_proc p N) (get_proc p N').

Lemma WellFormedNetwork_par :
  forall (N N': Network), WellFormedNetwork (N | N')%SP -> WellFormedNetwork N /\ WellFormedNetwork N'.
intros.
red in H.
split.
- red.
  simpl in H.
  set (H' := NoDup_app Pid (SPpn N) (SPpn N')).
  apply (H' H).
- red.
  simpl in H.
  set (H' := NoDup_app Pid (SPpn N) (SPpn N')).
  apply (H' H).
Qed.

Lemma get_proc_wf_par :
forall (N N': Network), WellFormedNetwork (N | N')%SP -> forall p, (get_proc p (N | N')%SP) = (get_proc p (N' | N)%SP).
intros.
simpl.
case_eq (get_proc p N); case_eq (get_proc p N'); auto.
intros.
exfalso.
red in H.
simpl in H.
apply (NoDup_app_not_in Pid (SPpn N) (SPpn N') H p).
+ apply Some_get_proc with p1; auto.
+ apply Some_get_proc with p0; auto.
Qed.

Lemma get_proc_wf_assoc :
forall (N1 N2 N3: Network), WellFormedNetwork (N1 | N2 | N3)%SP -> forall p, (get_proc p (N1 | N2 | N3)%SP) = (get_proc p ((N1 | N2) | N3)%SP).
intros.
red in H.
simpl in H.
set (Hin := (in_dec Nat.eq_dec p (SPpn N1 ++ SPpn N2 ++ SPpn N3))).
inversion Hin.
+ set (myH := (NoDup_pid_app_or p (SPpn N1) (SPpn N2 ++ SPpn N3) H H0)).
  destruct myH.
  - simpl.
    rewrite (get_proc_None p N2).
    rewrite (get_proc_None p N3).
    destruct (get_proc p N1); auto.
    destruct p0; auto.
    set (myH := (NoDup_app_not_in Pid (SPpn N1) (SPpn N2 ++ SPpn N3) H p H1)).
    apply (not_in_app Pid p (SPpn N2) (SPpn N3) Nat.eq_dec myH).
    set (myH := (NoDup_app_not_in Pid (SPpn N1) (SPpn N2 ++ SPpn N3) H p H1)).
    apply (not_in_app Pid p (SPpn N2) (SPpn N3) Nat.eq_dec myH).
  - simpl.
    rewrite (get_proc_None p N1).
    set (ndp := (NoDup_app Pid (SPpn N1) (SPpn N2 ++ SPpn N3)) H).
    destruct ndp.
    set (myH := (NoDup_pid_app_or p (SPpn N2) (SPpn N3)) H3 H1).
    inversion myH.
    * rewrite (get_proc_None p N3).
      destruct (get_proc p N2); auto.
      apply (NoDup_app_not_in Pid (SPpn N2)); auto.
    * rewrite (get_proc_None p N2).
      destruct (get_proc p N3); auto.
      destruct p0; auto.
      set (H5 := (NoDup_app_comm Pid (SPpn N2) (SPpn N3) H3)).
      apply (NoDup_app_not_in Pid (SPpn N3)); auto.
    * rewrite in_app_iff in H0.
      rewrite or_comm in H0.
      rewrite <- in_app_iff in H0.
      set (myH := NoDup_app_not_in Pid (SPpn N2 ++ SPpn N3) (SPpn N1)).
      set (myH2 := NoDup_app_comm Pid (SPpn N1) (SPpn N2 ++ SPpn N3) H).
      apply (myH myH2 p H1).
+ simpl.
  rewrite (get_proc_None p N1).
  rewrite (get_proc_None p N2).
  rewrite (get_proc_None p N3); auto.
  set (myH := elim_not_In_app Pid (SPpn N1) (SPpn N2 ++ SPpn N3) p H0).
  inversion_clear myH.
  set (myH := NoDup_app Pid (SPpn N1) (SPpn N2 ++ SPpn N3) H).
  inversion_clear myH.
  set (myH := elim_not_In_app Pid (SPpn N2) (SPpn N3) p H2).
  inversion_clear myH.
  auto.
  set (myH := elim_not_In_app Pid (SPpn N1) (SPpn N2 ++ SPpn N3) p H0).
  inversion_clear myH.
  set (myH := NoDup_app Pid (SPpn N1) (SPpn N2 ++ SPpn N3) H).
  inversion_clear myH.
  set (myH := elim_not_In_app Pid (SPpn N2) (SPpn N3) p H2).
  inversion_clear myH.
  auto.
  set (myH := elim_not_In_app Pid (SPpn N1) (SPpn N2 ++ SPpn N3) p H0).
  inversion_clear myH; auto.
Qed.

Lemma Precongr_char_if : forall (N N': Network), WellFormedNetwork N -> WellFormedNetwork N' -> Precongr N N' -> Precongr_op N N'.
intros; induction H1; intro.
+ red; unfold get_proc.
  case_eq (Nat.eqb p0 p); auto.
  rewrite Nat.eqb_refl; auto.
+ case_eq (get_proc p N); intros; simpl; auto.
  destruct p0; rewrite Nat.eqb_refl; red; auto.
+ set (H1 := (get_proc_wf_par N1 N2 H)).
  rewrite <- (H1 p).
  apply PrecongrPT_sym.
+ rewrite <- get_proc_wf_assoc.
  destruct (get_proc p (N1 | N2 | N3)).
  simpl.
  destruct p0.
  case_eq (Nat.eqb v v).
  rewrite Nat.eqb_eq.
  intro.
  red; auto.
  rewrite Nat.eqb_neq.
  intro.
  contradiction.
  simpl; auto.
  assumption.
+ rewrite get_proc_wf_assoc.
  destruct (get_proc p ((N1 | N2) | N3)).
  simpl.
  destruct p0.
  case_eq (v =? v).
  rewrite Nat.eqb_eq.
  intro; red; auto.
  rewrite Nat.eqb_neq; intro; contradiction.
  simpl; auto.
  assumption.
+ admit.
+ admit.
+ admit.
+ simpl.
  case_eq (p0 =? p).
  intro.
  simpl; red; auto.
  intro.
  red; auto.
+ simpl.
  destruct (get_proc p N).
  destruct p0.
  simpl.
  case_eq (v =? v).
  intro; red; auto.
  rewrite Nat.eqb_neq; intro; contradiction.
  simpl; auto.
Admitted.

Lemma Precongr_op_SPpn : forall N N', Precongr_op N N' -> forall p, In p (SPpn N') -> In p (SPpn N).
induction N, N'.
+ easy.
+ intros.
  simpl.
  specialize (H p0).
  simpl in H.
  case_eq (p0 =? p).
  - intro.
    rewrite H1 in H; assumption.
  - intro.
    simpl in H0.
    rewrite Nat.eqb_neq in H1.
    inversion_clear H0; auto.
+ intros.
  simpl.
  specialize (H p).
  simpl (get_proc p nnil) in H.
  red in H.
  set (myH := get_proc_Some p (N'1 | N'2) H0).
  inversion_clear myH.
  rewrite H1 in H; assumption.
+ intros.
  simpl in H0; exfalso; assumption.
+ intros.
  simpl (SPpn (p0 [v0, b0])) in H0.
  simpl in H0.
  inversion_clear H0; auto.
  - case_eq (p =? p0).
    * intro.
      specialize (H p).
      simpl in H.
      rewrite <- beq_nat_refl in H.
      rewrite H0 in H.
      simpl in H.
      case_eq (v =? v0).
      *** intro.
          rewrite Nat.eqb_eq in H0.
          rewrite <- H1.
          rewrite H0.
          simpl; auto.
      *** intro.
          rewrite Nat.eqb_eq in H0.
          rewrite <- H1.
          rewrite <- H0.
          simpl; auto.
    * intro.
      specialize (H p0).
      simpl in H.
      rewrite <- beq_nat_refl in H.
      rewrite <- beq_sym in H.
      rewrite H0 in H.
      simpl in H; exfalso; assumption.
  - exfalso; assumption.
+ intros.
  set (dec := dec_eq_nat p0 p).
  destruct dec.
  - simpl; left; auto.
  - simpl.
    right.
    specialize (H p0).
    set (myH := get_proc_Some p0 (N'1 | N'2) H0).
    inversion_clear myH.
    rewrite H2 in H.
    simpl in H.
    rewrite <- Nat.eqb_neq in H1.
    rewrite H1 in H.
    simpl in H.
    assumption.
+ intros.
  simpl in H0; exfalso; assumption.
+ admit.
+ admit.
Admitted.

Lemma Precongr_char_only_if : forall N N', WellFormedNetwork N -> WellFormedNetwork N' -> Precongr_op N N' -> Precongr N N'.
intros.
red in H1.
induction N.
(* + cut (N' = nnil%SP).
  intro.
  rewrite H2; apply Refl.
  specialize (H1 0).
  case_eq (get_proc 0 N').
  - intros.

  destruct (get_proc 0 N').

assumption N' nnil%SP.
apply Refl.

specialize (H1 0).
  simpl in H1.
  case (get_proc 0 N') in H1.
  - exfalso; auto.
  - 
induction N.
+ induction N'.
  - apply Refl.
  - exfalso.
    red in H1.
 *)
Admitted.

Lemma Precongr_char_iff : forall N N', WellFormedNetwork N -> WellFormedNetwork N' -> (Precongr_op N N' <-> Precongr N N').
split.
apply Precongr_char_only_if; auto.
apply Precongr_char_if; auto.
Qed.

(* See https://imada.sdu.dk/~petersk/sn/doc/BinaryTrees.html for Variable and Hypothesis. *)
(* (* 
Lemma congr_refl : forall N:Network, congr N N.
intros.
induction N; unfold congr; intros; simpl; auto.
Qed. *)

(** Symmetry of congr *)
Lemma congr_sym : forall N N':Network, congr N N' -> congr N' N.
intros.
unfold congr in H.
unfold congr.
symmetry in H.
apply H.
Qed.

(** Parallel law of congr *)
Lemma congr_par : forall N N':Network, WellFormedNetwork (N|N') -> congr (N|N') (N'|N).
intros.
red. simpl.
intros.
case_eq (get_proc p N).

(** congr is preserved by parallel composition. *)
Lemma congr_par_ctx : forall N1 N2 N'1 N'2: Network, WellFormedNetwork (N1|N2) -> congr N1 N'1 -> congr N2 N'2 -> congr (N1|N2) (N'1 | N'2).
intros.
red; intros.
red in H0, H1.
simpl.
rewrite H0.
rewrite H1.
trivial.
Qed.

Lemma congr_nil : forall (N:Network), WellFormedNetwork (N|nnil) -> congr (N|nnil) N.
intros.
red; intros.
simpl.
case_eq (get_proc p N); auto.
intros.
induction p0.
trivial.
Qed.

(** Transivity of congr. *)
Lemma congr_trans : forall (N1 N2 N3:Network), congr N1 N2 -> congr N2 N3 -> congr N1 N3.
unfold congr; intros.
rewrite H.
apply H0.
Qed.

(** Associativity of congr *)
Lemma congr_assocL : forall (N1 N2 N3:Network), WellFormedNetwork (N1|N2|N3) -> congr (N1|(N2|N3)) ((N1|N2)|N3).
intros.
induction N1.
+ apply (congr_trans (nnil|(N2|N3)) (N2|N3) ((nnil|N2)|N3)).
  apply 
  red.
  simpl.
  apply congr_refl.
 *)

(** Associativity of Precongr *)
(* Lemma Precongr_assocL : forall (N1 N2 N3:Network), Precongr (N1|(N2|N3)) ((N1|N2)|N3).
intros.
apply Equiv.
 *)

Inductive SPTo : Network -> Network -> Prop :=
 | S_Com p v q u e B B' : SPTo ( p [v, q!e;B] | q [u, p?;B'] )%SP
                               ( p [v, B] | q [(evaluate_on_value e v), B'] )%SP
 | S_Sel p v q u l B f {B':Behaviour}: (f l = inl B') -> SPTo ( Par (Process p v (Sel q l B)) (Process q u (Branching p f)) )
                               ( Par (Process p v B) (Process q u B') )
 | S_Then p v q u e B B1 B2 : ((evaluate_on_value e v) = u) -> SPTo ( Par (Process p v (Send q e B)) (Process q u (Cond p B1 B2)) )
                               ( Par (Process p v B) (Process q u B1) )
 | S_Else p v q u e B1 B2 B : ((evaluate_on_value e v) <> u) -> SPTo ( Par (Process p v (Send q e B)) (Process q u (Cond p B1 B2)) )
                               ( Par (Process p v B) (Process q u B2) )
 | S_Par N M N' : SPTo N N' -> SPTo (Par N M) (Par N' M)
 | S_Struct N1 N1' N2' N2 : Precongr N1 N1' -> SPTo N1' N2' -> Precongr N2' N2 -> SPTo N1 N2
.

Inductive SPToStar : Network -> Network -> Prop :=
 | ToRefl N : SPToStar N N
 | ToSingle N1 N2 (P:SPTo N1 N2) : SPToStar N1 N2
 | ToTran N1 N2 N3 (P1:SPToStar N1 N2) (P2:SPToStar N2 N3) : SPToStar N1 N3
.

Bind Scope SP_scope with SPTo.
Notation "N ---> N'" := (SPTo N N') (at level 50, left associativity) : SP_scope.
Notation "N --->* N'" := (SPToStar N N') (at level 50, left associativity) : SP_scope.

End Semantics.


