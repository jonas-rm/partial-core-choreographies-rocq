Require Export MC.
Require Export Coq.Lists.ListSet.
Require Export Sorting.Permutation.
Require Export FunInd.

Local Open Scope nat_scope.

Module SPBase (P E V:DecType) (Import Ev:Eval E V).

Module Import MCBase := MCBase P E V Ev.

Section Syntax.

Inductive Behaviour : Type :=
| End : Behaviour
| Send : Pid -> Expr -> Behaviour -> Behaviour
| Recv : Pid -> Behaviour -> Behaviour
| Sel : Pid -> Label -> Behaviour -> Behaviour
| Branching : Pid -> (Label -> (Behaviour + unit)) -> Behaviour
| Cond : Pid -> Behaviour -> Behaviour -> Behaviour
.

Definition Branch : Type := (Behaviour + unit).

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
end.

End Syntax.

Delimit Scope SP_scope with SP.

Bind Scope SP_scope with Behaviour.
Bind Scope SP_scope with Network.

Notation "N | N'" := (Par N N') (at level 202, right associativity) : SP_scope.
Notation "p [ v , B ]" := (Process p v B) (at level 201, v at level 9, no associativity) : SP_scope.
Notation "p ! e ; B" := (Send p e B) (at level 60, e at level 9, right associativity) : SP_scope.
Notation "p ? ; B" := (Recv p B) (at level 60, right associativity) : SP_scope.
Notation "p (+) l ; B" := (Sel p l B) (at level 49, l at level 9, right associativity) : SP_scope.
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

Section SyntacticProperties.

Fixpoint WellFormedBehaviour (p:Pid) (B:Behaviour) : Prop :=
match B with
| bnil%SP => True
| (q!e; B)%SP => p <> q /\ WellFormedBehaviour p B
| (q?; B)%SP => p <> q /\ WellFormedBehaviour p B
| (q (+) l; B)%SP => p <> q /\ WellFormedBehaviour p B
| (If q Then B1 Else B2)%SP => p <> q /\ WellFormedBehaviour p B1 /\ WellFormedBehaviour p B2
| (q & f)%SP => p <> q /\ forall l, match (f l) with | inl B' => WellFormedBehaviour p B' | _ => True end
end.

Fixpoint NoSelfCommunications (N:Network) : Prop :=
match N with
| nnil%SP => True
| (p [ v, B ])%SP => WellFormedBehaviour p B
| Par M M' => NoSelfCommunications M /\ NoSelfCommunications M'
end.

(** A well-formed network has no duplicate process names and no self-communications. *)
Definition WellFormedNetwork (N:Network) : Prop := NoDup (SPpn N) /\ NoSelfCommunications N.

End SyntacticProperties.

Section Semantics.

(** Precongruence of behaviours. Will be used to define unfolding. *)
Definition PrecongrB := (eq (A := Behaviour)).

(** Sugar for (value, behaviour). Makes the definition of congr readable. *)
(* Definition ProcessTerm : Type := Value * Behaviour. *)

Fixpoint get_proc_behaviour (p:Pid) (N:Network) : Behaviour :=
match N with
| nnil%SP => bnil%SP
| (q [ v, B ])%SP => if (Pid_dec p q) then B else bnil%SP
| (Par N1 N2) => match (get_proc_behaviour p N1), (get_proc_behaviour p N2) with
                  | bnil%SP, B' => B'
                  | B, _ => B
                  end
end.

Fixpoint get_proc_value (p:Pid) (N:Network) : option Value :=
match N with
| nnil%SP => None
| (q [ v, B ])%SP => if (Pid_dec p q) then Some v else None
| (Par N1 N2) => match (get_proc_value p N1), (get_proc_value p N2) with
                  | Some v, _ => Some v
                  | None, Some v => Some v
                  | _, _ => None
                  end
end.

(** Returns the value and behaviour of process p in a network, if the process exists in the network. *)
(* Fixpoint get_proc (p:Pid) (N:Network) : option ProcessTerm :=
match N with
| nnil%SP => None
| (q [ v, B ])%SP => if (p =? q) then Some (v, B) else None
| (Par N1 N2) => match (get_proc p N1), (get_proc p N2) with
                  | Some (v,B), _ => Some (v,B)
                  | None, Some (v,B) => Some (v,B)
                  | _, _ => None
                  end
end.
 *)

Lemma not_in_get_proc_behaviour : forall (p:Pid) (N:Network),
  ~(In p (SPpn N)) -> (get_proc_behaviour p N) = bnil%SP.
Proof.
intros.
induction N; auto.
+ simpl.
  apply not_in_cons in H.
  inversion_clear H.
  rewrite <- Pdec.eqb_neq in H0.
  unfold Pid_dec; rewrite H0; auto.
+ simpl.
  rewrite IHN1.
  rewrite IHN2.
  auto.
  intro; apply H.
  apply in_or_app; auto.
  intro; apply H.
  apply in_or_app; auto.
Qed.

Lemma not_in_get_proc_value : forall (p:Pid) (N:Network),
  ~(In p (SPpn N)) -> (get_proc_value p N) = None.
Proof.
intros.
induction N; auto.
+ simpl.
  apply not_in_cons in H.
  inversion_clear H.
  rewrite <- Pdec.eqb_neq in H0.
  unfold Pid_dec; rewrite H0; auto.
+ simpl.
  rewrite IHN1.
  rewrite IHN2.
  auto.
  intro; apply H.
  apply in_or_app; auto.
  intro; apply H.
  apply in_or_app; auto.
Qed.

Lemma get_proc_value_none : forall p N,
  get_proc_value p N = None -> ~ In p (SPpn N).
Proof.
induction N; auto; simpl; intros; intro.
+ inversion_clear H0; auto.
  unfold Pid_dec in H.
  symmetry in H1.
  rewrite <- Pdec.eqb_eq in H1.
  rewrite H1 in H.
  inversion H.
+ destruct (get_proc_value p N1).
  1: inversion H.
  destruct (get_proc_value p N2).
  1: inversion H.
  pose (IHN1 H) as H1.
  pose (IHN2 H) as H2.
  elim (in_app_or _ _ _ H0); auto.
Qed.

Lemma get_proc_value_none_not_in_iff : forall p N,
  get_proc_value p N = None <-> ~ In p (SPpn N).
Proof.
split.
apply get_proc_value_none.
apply not_in_get_proc_value.
Qed.

Lemma in_get_proc_value : forall (p:Pid) (N:Network),
  In p (SPpn N) -> exists T, (get_proc_value p N) = Some T.
Proof.
induction N; simpl; intros.
+ inversion H.
+ inversion_clear H.
  2: inversion H0.
  exists v.
  rewrite H0.
  rewrite Pdec.eqb_refl; auto.
+ elim (In_dec P.eq_dec p (SPpn N1)).
  - intros.
    elim IHN1; auto.
    intros; exists x.
    rewrite H0; auto.
  - intros.
    elim IHN2; auto.
    * intros; exists x.
      rewrite H0; rewrite not_in_get_proc_value; auto.
    * elim (in_app_or _ _ _ H); auto.
      intro; elim b; auto.
Qed.

Lemma get_proc_value_some : forall p N v,
  get_proc_value p N = Some v -> In p (SPpn N).
Proof.
induction N; auto; simpl; intros.
+ inversion H.
+ unfold Pid_dec in H.
  left.
  revert H.
  case_eq (Pdec.eqb p p0); intros.
  - symmetry.
    apply Pdec.eqb_eq; auto.
  - inversion H0.
+ destruct (get_proc_value p N1).
  1: apply in_or_app; eauto.
  destruct (get_proc_value p N2).
  1: apply in_or_app; eauto.
  inversion H.
Qed.

Lemma get_proc_behaviour_in : forall (p:Pid) (N:Network), (get_proc_behaviour p N) <> bnil%SP -> In p (SPpn N).
Proof.
intros.
elim (in_dec P.eq_dec p (SPpn N)); auto.
intro.
rewrite not_in_get_proc_behaviour in H; auto.
elim H; auto.
Qed.

Inductive SP_Precongr : Network -> Network -> Prop :=
| PN_Lift p v B B' : PrecongrB B B' -> SP_Precongr (p [v, B])%SP (p [v, B'])%SP
| PN_Refl N : SP_Precongr N N
| PN_Sym N1 N2 : SP_Precongr (N1 | N2) (N2 | N1)
| PN_AssocL N1 N2 N3 : SP_Precongr (N1|(N2|N3)) ((N1|N2)|N3)
| PN_AssocR N1 N2 N3 : SP_Precongr ((N1|N2)|N3) (N1|(N2|N3))
| PN_CtxL N1 N2 N3 : SP_Precongr N1 N2 -> SP_Precongr (N1 | N3) (N2 | N3)
| PN_CtxR N1 N2 N3 : SP_Precongr N2 N3 -> SP_Precongr (N1 | N2) (N1 | N3)
| PN_Trans N1 N2 N3 : SP_Precongr N1 N2 -> SP_Precongr N2 N3 -> SP_Precongr N1 N3
| PN_PZero p v : SP_Precongr (Process p v End) Empty
| PN_NZero N : SP_Precongr (Par N Empty) N
.

Definition Precongr_op (N N': Network) : Prop :=
  forall p, PrecongrB (get_proc_behaviour p N) (get_proc_behaviour p N')
            /\ (forall x, get_proc_value p N' = Some x -> get_proc_value p N = Some x).

Lemma WellFormedNetwork_par : forall (N N': Network),
  WellFormedNetwork (N | N')%SP -> WellFormedNetwork N /\ WellFormedNetwork N'.
Proof.
intros.
inversion_clear H.
inversion_clear H1.
simpl in H0.
elim (NoDup_app _ _ _ H0); intros.
repeat split; auto.
Qed.

Lemma WellFormedNetwork_comm : forall (N N': Network),
  WellFormedNetwork (N | N')%SP -> WellFormedNetwork (N' | N)%SP.
Proof.
intros.
elim (WellFormedNetwork_par N N' H); intros.
inversion_clear H.
inversion_clear H0.
inversion_clear H1.
repeat split; auto.
apply NoDup_app_sym; auto.
Qed.

Lemma get_proc_behaviour_wf_par : forall (N N': Network),
  WellFormedNetwork (N | N')%SP ->
  forall p, (get_proc_behaviour p (N | N')%SP) = (get_proc_behaviour p (N' | N)%SP).
Proof.
intros.
inversion_clear H.
elim (In_dec P.eq_dec p (SPpn N ++ SPpn N')); intro.
+ elim (in_app_or _ _ _ a); intro; simpl.
  - pose (NoDup_app_not_in _ _ _ H0 _ H) as Hp; clearbody Hp.
    rewrite (not_in_get_proc_behaviour _ _ Hp).
    case_eq (get_proc_behaviour p N); auto.
  - pose (NoDup_app_not_in _ _ _ (NoDup_app_sym _ _ _ H0) _ H) as Hp; clearbody Hp.
    rewrite (not_in_get_proc_behaviour _ _ Hp).
    case_eq (get_proc_behaviour p N'); auto.
+ simpl.
  elim (not_in_app _ _ _ _ b); intros.
  repeat rewrite not_in_get_proc_behaviour; auto.
Qed.

Lemma get_proc_value_wf_par : forall (N N': Network),
  WellFormedNetwork (N | N')%SP -> forall p, (get_proc_value p (N | N')%SP) = (get_proc_value p (N' | N)%SP).
Proof.
intros.
inversion_clear H.
elim (In_dec P.eq_dec p (SPpn N ++ SPpn N')); intro.
+ elim (in_app_or _ _ _ a); intro; simpl.
  - pose (NoDup_app_not_in _ _ _ H0 _ H) as Hp; clearbody Hp.
    rewrite (not_in_get_proc_value _ _ Hp).
    case_eq (get_proc_value p N); auto.
  - pose (NoDup_app_not_in _ _ _ (NoDup_app_sym _ _ _ H0) _ H) as Hp; clearbody Hp.
    rewrite (not_in_get_proc_value _ _ Hp).
    case_eq (get_proc_value p N'); auto.
+ simpl.
  elim (not_in_app _ _ _ _ b); intros.
  repeat rewrite not_in_get_proc_value; auto.
Qed.

Lemma get_proc_behaviour_wf_assoc : forall (N1 N2 N3: Network),
  WellFormedNetwork (N1 | N2 | N3)%SP ->
  forall p, (get_proc_behaviour p (N1 | N2 | N3)%SP) = (get_proc_behaviour p ((N1 | N2) | N3)%SP).
Proof.
intros.
inversion_clear H.
set (Hin := (in_dec P.eq_dec p (SPpn N1 ++ SPpn N2 ++ SPpn N3))).
inversion Hin.
+ elim (in_app_or _ _ _ H); intro.
  - generalize (NoDup_app_not_in _ _ _ H0 _ H2); intro.
    elim (not_in_app _ _ _ _ H3); intros.
    simpl.
    rewrite (not_in_get_proc_behaviour p N2); auto.
    destruct (get_proc_behaviour p N1); auto.
  - generalize (NoDup_app_not_in _ _ _ (NoDup_app_sym _ _ _ H0) _ H2); intro.
    simpl.
    rewrite (not_in_get_proc_behaviour p N1); auto.
+ elim (not_in_app _ _ _ _ H); intros.
  elim (not_in_app _ _ _ _ H3); intros.
  simpl; repeat rewrite not_in_get_proc_behaviour; auto.
Qed.

Lemma get_proc_value_wf_assoc : forall (N1 N2 N3: Network),
  WellFormedNetwork (N1 | N2 | N3)%SP ->
  forall p, (get_proc_value p (N1 | N2 | N3)%SP) = (get_proc_value p ((N1 | N2) | N3)%SP).
Proof.
intros.
inversion_clear H.
set (Hin := (in_dec P.eq_dec p (SPpn N1 ++ SPpn N2 ++ SPpn N3))); clearbody Hin.
inversion Hin.
+ elim (in_app_or _ _ _ H); intro.
  - generalize (NoDup_app_not_in _ _ _ H0 _ H2); intro.
    elim (not_in_app _ _ _ _ H3); intros.
    simpl.
    rewrite (not_in_get_proc_value p N2); auto.
    rewrite (not_in_get_proc_value p N3); auto.
    destruct (get_proc_value p N1); auto.
  - generalize (NoDup_app_not_in _ _ _ (NoDup_app_sym _ _ _ H0) _ H2); intro.
    simpl.
    rewrite (not_in_get_proc_value p N1); auto.
    elim (in_app_or _ _ _ H2); intro.
    * generalize (NoDup_app_elim_2 _ _ _ H0); intros.
      generalize (NoDup_app_not_in _ _ _ H5 _ H4); intro.
      rewrite (not_in_get_proc_value p N3); auto.
    * generalize (NoDup_app_elim_2 _ _ _ H0); intros.
      generalize (NoDup_app_not_in _ _ _ (NoDup_app_sym _ _ _ H5) _ H4); intro.
      rewrite (not_in_get_proc_value p N2); auto.
      destruct (get_proc_value p N3); auto.
+ elim (not_in_app _ _ _ _ H); intros.
  elim (not_in_app _ _ _ _ H3); intros.
  simpl; repeat rewrite not_in_get_proc_value; auto.
Qed.

Lemma in_network_par_xor : forall p N N',
  WellFormedNetwork (N | N')%SP -> In p (SPpn (N | N')%SP) ->
  ( In p (SPpn N) /\ ~ In p (SPpn N') ) \/ ( In p (SPpn N') /\ ~ In p (SPpn N) ).
Proof.
intros.
inversion_clear H.
elim (in_app_or _ _ _ H0); intro.
+ left; split; auto.
  apply NoDup_app_not_in with (SPpn N); auto.
+ right; split; auto.
  apply NoDup_app_not_in with (SPpn N'); auto.
  apply NoDup_app_sym; auto.
Qed.

Lemma get_proc_behaviour_nnil : forall p N, get_proc_behaviour p (N | nnil) = get_proc_behaviour p N.
Proof.
intros.
simpl.
destruct (get_proc_behaviour p N); auto.
Qed.

Lemma SP_Precongr_NoDup : forall N1 N2,
  NoDup (SPpn N1) -> SP_Precongr N1 N2 -> NoDup (SPpn N2).
Proof.
(* intros.
inversion H.
induction H0; auto.
+ split; auto.
  rewrite <- H0; auto.
+ apply (WellFormedNetwork_comm); auto.
+ split.
  1: simpl; rewrite <- app_assoc; auto.
  
  assumption.
+ red.
  simpl.
  rewrite app_assoc.
  assumption.
+ red.
  simpl.
  Search NoDup.
 *)
Admitted.

Lemma SP_Precongr_NoSelfCommunications : forall N1 N2,
  NoSelfCommunications N1 -> SP_Precongr N1 N2 -> NoSelfCommunications N2.
Proof.
Admitted.

Lemma SP_Precongr_wf : forall N1 N2,
  WellFormedNetwork N1 -> SP_Precongr N1 N2 -> WellFormedNetwork N2.
Proof.
Admitted.

Lemma Precongr_char_if : forall (N N': Network), WellFormedNetwork N -> WellFormedNetwork N' -> SP_Precongr N N' -> Precongr_op N N'.
Proof.
red.
intros.
induction H1.
+ simpl.
  inversion_clear H1.
  case_eq (Pid_dec p p0).
  intros; split; auto; reflexivity.
  intros; split; auto; reflexivity.
+ split; auto. reflexivity.
+ split.
  rewrite <- (get_proc_behaviour_wf_par N1 N2 H p).
  reflexivity.
  rewrite <- (get_proc_value_wf_par N1 N2 H p).
  intros; auto.
+ split.
  rewrite <- (get_proc_behaviour_wf_assoc N1 N2 N3 H p).
  reflexivity.
  rewrite <- (get_proc_value_wf_assoc N1 N2 N3 H p).
  intros; auto.
+ split.
  rewrite (get_proc_behaviour_wf_assoc N1 N2 N3 H0 p).
  reflexivity.
  rewrite (get_proc_value_wf_assoc N1 N2 N3 H0 p).
  intros; auto.
+ (* CtxL *)
  pose (WellFormedNetwork_par _ _ H) as WFN13.
  inversion_clear WFN13.
  pose (WellFormedNetwork_par _ _ H0) as WFN12.
  inversion_clear WFN12.
  clear H5.
  pose (IHSP_Precongr H2 H4).
  inversion_clear a.
  split.
  - inversion H5.
    simpl.
    rewrite H8.
    reflexivity.
  - rewrite (get_proc_value_wf_par _ _ H0).
    rewrite (get_proc_value_wf_par N1 N3 H).
    simpl.
    case_eq (get_proc_value p N3); auto.
    intro.
    case_eq (get_proc_value p N2).
    2: {
      intros.
      inversion H9.
    }
    intros.
    rewrite H9 in H8.
    specialize (H6 x).
    pose (H6 H8).
    rewrite e; auto.
+ (* CtxR *)
  pose (WellFormedNetwork_par _ _ H) as WFN13.
  inversion_clear WFN13.
  pose (WellFormedNetwork_par _ _ H0) as WFN12.
  inversion_clear WFN12.
  clear H4.
  pose (IHSP_Precongr H3 H5).
  inversion_clear a.
  split.
  - inversion H4.
    simpl.
    rewrite H8.
    reflexivity.
  - simpl.
    case_eq (get_proc_value p N1); auto.
    intro.
    case_eq (get_proc_value p N3).
    2: {
      intros.
      inversion H9.
    }
    intros.
    rewrite H9 in H8.
    specialize (H6 x).
    pose (H6 H8).
    rewrite e; auto.
+ (* Trans *)
  pose (SP_Precongr_wf _ _ H H1_).
  pose (IHSP_Precongr1 H w) as IH; inversion_clear IH.
  red in H1.
  pose (IHSP_Precongr2 w H0) as IH; inversion_clear IH.
  red in H3.
  split.
  * rewrite H1. rewrite H3. reflexivity.
  * intros.
    specialize (H2 x).
    specialize (H4 x).
    pose (H4 H5).
    pose (H2 e).
    rewrite e0; auto.
+ split.
  simpl.
  red.
  case_eq (Pid_dec p p0); auto.
  intros.
  inversion H1.
+ split.
  red.
  apply (get_proc_behaviour_nnil _ _).
  intros.
  simpl.
  rewrite H1; auto.
Qed.

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

End SPBase.
