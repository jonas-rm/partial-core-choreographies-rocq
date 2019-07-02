Require Import MC.
Require Import Arith.
Require Import Coq.Arith.Arith. 
Require Import Coq.Lists.List.

Module Import MC_Plus (P E V R: DecType) (Ev : Eval E V).
(* Module Import MC_Plus (P E R V: DecentType) (Ev : Eval E V). *)

Module Import agh := MCBase P E V R Ev.


Lemma Precongr_garbage_EtaEta_comm : forall eta1 eta2 n C1 C2, 
  C1 $ n g>~ (eta1; eta2; C2) ->
  exists C3, C1 = (eta1; eta2; C3) /\ (eta2; eta1; C3) $ n g>~ (eta2; eta1; C2).
Proof.
intros.
inversion H. 
+ inversion H0.
+ inversion H3. 
  - inversion H5.
  - eexists. split. auto. repeat constructor. trivial.
Qed.

Lemma Precongr_garbage_EtaCond_comm : forall eta p q n C1 C2 C2', 
  C1 $ n g>~ (eta; If p == q Then C2 Else C2') ->
    exists C3 C3', C1 = (eta; If p == q Then C3 Else C3') /\ 
      (If p == q Then (eta; C3) Else (eta; C3')) $ n g>~ (If p == q Then (eta; C2) Else (eta; C2')).
Proof.
intros.
inversion H. 
+ inversion H0.
+ inversion H3. 
  - inversion H5.
  - repeat eexists. repeat constructor. trivial.
  - repeat eexists. repeat constructor. trivial.
Qed.

Lemma Precongr_garbage_CondEta_comm : forall eta p q n C1 C2 C2', 
  C1 $ n g>~ (If p == q Then (eta; C2) Else (eta; C2')) ->
    exists C3 C3', C1 = (If p == q Then (eta; C3) Else (eta; C3')) /\ 
       (eta; If p == q Then C3 Else C3') $ n g>~ (eta; If p == q Then C2 Else C2').
Proof.
intros.
inversion H. 
+ inversion H0.
+ inversion H3. 
  - inversion H7.
  - repeat eexists. try (repeat constructor; trivial; fail).
+ inversion H3. 
  - inversion H7.
  - repeat eexists. try (repeat constructor; trivial; fail).
Qed.


Lemma Precongr_garbage_CondCond_comm : forall p q r s n C1 C2 C2' C3 C3', 
  C1 $ n g>~ (If p == q Then (If r == s Then C2 Else C2') Else (If r == s Then C3 Else C3')) ->
    exists C4 C4' C5 C5', C1 = (If p == q Then (If r == s Then C4 Else C4') Else (If r == s Then C5 Else C5')) /\ 
      (If r == s Then (If p == q Then C4 Else C5) Else (If p == q Then C4' Else C5')) $ n g>~
        (If r == s Then (If p == q Then C2 Else C3) Else (If p == q Then C2' Else C3')).
Proof.
intros.
inversion H. 
+ inversion H0.
+ inversion H3. 
  - inversion H7.
  - repeat eexists. try (repeat constructor; trivial; fail).
  - repeat eexists. try (repeat constructor; trivial; fail).
+ inversion H3. 
  - inversion H7.
  - repeat eexists. try (repeat constructor; trivial; fail).
  - repeat eexists. try (repeat constructor; trivial; fail).
Qed.

Lemma Precongr_garbage_EtaRec_comm : forall eta X CX n C1 C2, 
  C1 $ n g>~ (eta; Def X == CX In C2) ->
    exists C3, C1 = (eta; Def X == CX In C3) /\ (Def X == CX In (eta; C3)) $ n g>~ (Def X == CX In (eta; C2)).
Proof.
intros.
inversion H. 
+ inversion H0.
+ inversion H3.
  - inversion H5.
  - eexists. repeat constructor. trivial.
Qed.

Lemma Precongr_garbage_RecEta_comm : forall eta X CX n C1 C2, 
  C1 $ n g>~ (Def X == CX In (eta; C2)) ->
    exists C3, C1 = (Def X == CX In (eta; C3)) /\ (eta; Def X == CX In C3) $ n g>~ (eta; Def X == CX In C2).
Proof.
intros.
inversion H. 
+ inversion H0.
+ inversion H3.
  - inversion H6.
  - eexists. repeat constructor. trivial.
Qed.

Lemma Precongr_garbage_CondRec_comm : forall p q X CX n C1 C2 C2', 
  C1 $ n g>~ (If p == q Then Def X == CX In C2 Else Def X == CX In C2') ->
    exists C3 C3',  C1 = (If p == q Then Def X == CX In C3 Else Def X == CX In C3') /\ 
      (Def X == CX In If p == q Then C3 Else C3') $ n g>~ (Def X == CX In If p == q Then C2 Else C2').
Proof.
intros. inversion H.
+ inversion H0.
+ inversion_clear H3.
  - inversion H7.
  - eexists. eexists.
    split; auto.
    repeat constructor. trivial.
+ inversion_clear H3.
  - inversion H7.
  - eexists. eexists.
    split; auto.
    repeat constructor. trivial.
Qed.

Lemma Precongr_garbage_RecCond_comm : forall p q X CX n C1 C2 C2', 
  C1 $ n g>~ (Def X == CX In If p == q Then C2 Else C2') ->
    exists C3 C3', C1 = (Def X == CX In If p == q Then C3 Else C3') /\ 
      (If p == q Then Def X == CX In C3 Else Def X == CX In C3') $ n g>~ (If p == q Then Def X == CX In C2 Else Def X == CX In C2').
Proof.
intros. inversion H.
+ inversion H0.
+ inversion_clear H3.
  - inversion H6.
  - eexists. eexists.
    split; auto.
    repeat constructor. trivial.
  - eexists. eexists.
    split; auto.
    repeat constructor. trivial.
Qed.

Lemma Precongr_garbage_DefDef_comm : forall X CX Y CY n C1 C2, 
  C1 $ n g>~ (Def X == CX In Def Y == CY In C2) ->
    exists C3, C1 = (Def X == CX In Def Y == CY In C3) /\ 
      (Def Y == CY In Def X == CX In C3) $ n g>~ (Def Y == CY In Def X == CX In C2).
Proof.
intros. inversion H.
+ inversion H0.
+ inversion_clear H3.
  - inversion H6.
  - eexists. 
    split; auto.
    repeat constructor. trivial.
Qed.


Lemma Precongr_garbage_sym_base : forall n C1 C2 C3, C1 $ n g>~ C2 -> Precongr_sym C2 C3 ->
  exists C2', Precongr_sym C1 C2' /\ C2' $ n g>~ C3.
Proof.
intros.
inversion H0.
+ rewrite <- H2 in H.
  apply Precongr_garbage_EtaEta_comm in H.
  inversion_clear H.
  eexists.
  inversion_clear H4.
  rewrite H.
  split; repeat constructor; trivial.
+ rewrite <- H3 in H.
  apply Precongr_garbage_EtaCond_comm in H.
  inversion_clear H.
  inversion_clear H5.
  eexists.
  inversion_clear H.
  rewrite H5.
  split; repeat constructor; trivial.
+ rewrite <- H3 in H.
  apply Precongr_garbage_CondEta_comm in H.
  repeat (inversion_clear H; inversion_clear H5).
  eexists.
  split; repeat constructor; trivial.
+ rewrite <- H2 in H.
  apply Precongr_garbage_CondCond_comm in H.
  repeat (inversion_clear H; inversion_clear H4).
  eexists.
  split; repeat constructor; auto; apply H1.
+ rewrite <- H1 in H.
  apply Precongr_garbage_EtaRec_comm in H.
  inversion_clear H. 
  inversion_clear H3.
  eexists.
  rewrite H.
  split; repeat constructor; auto. 
+ rewrite <- H1 in H.
  apply Precongr_garbage_RecEta_comm in H.
  inversion_clear H. 
  inversion_clear H3.
  eexists.
  rewrite H.
  split; repeat constructor; auto.
+ rewrite <- H1 in H.
  apply Precongr_garbage_CondRec_comm in H.
  inversion_clear H.
  inversion_clear H3.
  eexists.
  inversion_clear H.
  rewrite H3.
  split; repeat constructor; trivial.
+ rewrite <- H1 in H.
  apply Precongr_garbage_RecCond_comm in H.
  inversion_clear H.
  inversion_clear H3.
  eexists.
  inversion_clear H.
  rewrite H3.
  split; repeat constructor; trivial.
+ rewrite <- H4 in H.
  apply Precongr_garbage_DefDef_comm in H.
  inversion_clear H.
  inversion_clear H6.
  eexists.
  inversion_clear H.
  split; repeat constructor; trivial.
Qed.

Lemma Precongr_garbage_sym_comm : forall n1 n2 C1 C2 C3, C1 $ n1 g>~ C2 -> C2 $ n2 ~<>~ C3 ->
  exists C2', C1 $ n2 ~<>~ C2' /\ C2' $ n1 g>~ C3.
Proof.
intros n1 n2.
revert n1.
induction n2.
+ intros.
  elim (Precongr_garbage_sym_base n1 C1 C2 C3); intros.
  inversion_clear H1.
  exists x; split; [constructor;trivial|trivial].
  trivial.
  inversion_clear H0.
  trivial.
+ intro n1.
  induction n1.
  - intros.
    inversion_clear H.
    inversion H1.
    rewrite <- H2 in H0.
    inversion H0.
  - intros. 
    inversion H; inversion H0; rewrite <- H4 in H7; inversion H7. 
    * fold GPrecongr_step in H2.
      fold SPrecongr_step in H6.
      rewrite H11 in H6.
      elim (IHn2 _ _ _ _ H2 H6).
      intros.
      exists (eta; x).
      inversion H9.
      split; constructor; trivial.
    * fold GPrecongr_step in H2.
      fold SPrecongr_step in H6.
      rewrite H12 in H6.
      elim (IHn2 _ _ _ _ H2 H6).
      intros.
      eexists (If p == q Then x Else C).
      inversion H9.
      split; constructor; trivial.
    * eexists (If p == q Then C' Else C''0).
      rewrite H13 in H6.
      split; constructor; trivial.
    * eexists (If p == q Then C''0 Else C').
      rewrite H12 in H6.
      split; constructor; trivial.
    * fold GPrecongr_step in H2.
      fold SPrecongr_step in H6.
      rewrite H13 in H6.
      elim (IHn2 _ _ _ _ H2 H6).
      intros.
      eexists (If p == q Then C Else x).
      inversion H9.
      split; constructor; trivial.
    * fold GPrecongr_step in H2.
      fold SPrecongr_step in H6.
      rewrite H12 in H6.
      elim (IHn2 _ _ _ _ H2 H6).
      intros.
      eexists (Def X == C0 In x).
      inversion H9.
      split; constructor; trivial.
Qed.

(*
Lemma Precongr_garbage_dec : forall C C', (Precongr_garbage C C') + ~((Precongr_garbage C C')).
Proof. 
intros C C'. case C,C'; try (right; intro; inversion H; fail).
case C2; try (right; intro; inversion H; fail).
left. constructor.
Qed.

Lemma Precongr_sym_dec : forall C C', (Precongr_sym C C') + ~((Precongr_sym C C')).
Proof. 
intros C C'. 
case C,C'; try (right; intro; inversion H; auto; fail).
case (exists C'', C = e;e0)

induction C2; try (right; intro; inversion H; fail).
left. constructor.
Qed.


Lemma Precongr_unfold_dec : forall C C', (Precongr_unfold C C') + ~((Precongr_unfold C C')).
Proof. 
induction C, C'; try (right; intro; inversion H; fail).
case (R.eq_dec r r0).
+ 
+ right. intro; inversion H; auto.
Qed.


(*
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