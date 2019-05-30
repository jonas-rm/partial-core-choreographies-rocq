Require Export Implementation.

Import MC_Nat.
Import St.

Fixpoint list_to_state (l : list (Pid * Value)) : State :=
match l with
| nil => fun _ => 0
| (p,v)::l' => update (list_to_state l') p v
end.

Fixpoint Definitional_Context (l:list (RecVar * Choreography)) (C:Choreography) : Choreography :=
match l with
| nil => C
| (X,CX)::l' => Def X == CX In (Definitional_Context l' C)
end.

Lemma MCP_step_End_char : forall C, C ~<a End -> exists l, C = Definitional_Context l End.
Proof.
intros.
inversion H; simpl.
+ exists nil; auto.
+ exists ((X,C0)::nil); auto.
Qed.

Lemma MCP_Congruent_End_char : forall C, C ~<>~ End -> C = End.
Proof.
intros.
elim (Congruent_to_weighted H); clear H; intro n; revert C.
assert (forall k, k <= n -> forall C, C$k ~<n>~ End -> C = End); eauto.
induction n; intros; [inversion H | case_eq k; intros]; rewrite H1 in H0; inversion H0; auto.
rewrite H1 in H; apply le_S_n in H; clear k H1.
rename n0 into n'; rename n1 into m; rename k0 into k.
clear C3 H6 C1 H5.
assert (C2 = End).
+ apply IHn with k; auto.
  transitivity n'; auto.
  rewrite <- H2; auto with arith.
+ rewrite H1 in H3.
  apply IHn with m; auto.
  transitivity n'; auto.
  rewrite <- H2; auto with arith.
Qed.

Lemma MCP_terminated_char : forall C, C ~<= End -> exists l, C = Definitional_Context l End.
Proof.
intros.
elim (MCP_to_weighted H); clear H; intro n; revert C.
induction n; intros; inversion H.
+ exists nil; apply MCP_Congruent_End_char; auto.
+ clear C'' H4 C0 H3 n0 H0 H.
  elim (IHn C'); auto.
  intros l Hl.
  rewrite Hl in H1; clear Hl H2 C' n IHn.

Abort.

Lemma fatsemi_End : forall C, (C;;End) = C.
Proof.
induction C; simpl; auto.
+ rewrite IHC; auto.
+ rewrite IHC1; rewrite IHC2; auto.
+ rewrite IHC1; rewrite IHC2; auto.
Qed.

Lemma fatsemi_End_inv : forall C C', (C;;C') = End -> C = End /\ C' = End.
Proof.
induction C; split; auto; try inversion H.
Qed.

(*
Lemma fatsemi_To : forall C C' C'' s s', (C,s) ---> (C'',s') -> (C;;C',s) ---> (C'';;C',s').
Proof.
intros.
elim (MCTo_to_weighted H); clear H; intros n Hn.
revert C C' C'' s s' Hn.
induction n; intros; inversion Hn.
- induction C; try inversion H; inversion H0; simpl.
  + induction e; inversion H4; [apply C_Com | apply C_Sel].
  + revert H4; case_eq (MC_Nat.Value_dec (s p) (s p0)); intros; inversion H4.
    * apply C_Then; apply MC_Nat.Vdec.eqb_eq; rewrite <- H7; auto.
    * apply C_Else; apply MC_Nat.Vdec.eqb_neq; rewrite <- H7; auto.
  + revert H4; simpl in H0; rewrite H0.
    intro; simpl.

*)

(*
Lemma fatsemi_ToStar : forall C C' C'' s s', (C,s) --->* (C', s') -> (C;;C'',s) --->* (C';;C'', s').
intros.
dependent induction H.
+ apply ToRefl.
+ induction c2.
  apply ToStep with (a;;C'', b); auto.
  - apply fatsemi_To; auto.
Qed.
*)

Fixpoint size (C:Choreography) : nat :=
  match C with
  | End => 0
  | Call X => 1
  | eta; C' => 1 + size C'
  | If p == q Then C1 Else C2 => 1 + min (size C1) (size C2)
  | Def X == C1 In C2 => 1 + size C2
  end.

(*
Lemma fatsemi_size : forall C C', size C + size C' <= size (C;;C').
Proof.
induction C. simpl; auto with arith.
intros.
apply le_n_S.
rewrite <- Nat.add_min_distr_r.
apply Nat.min_glb.
+ etransitivity; [apply Nat.le_min_l | apply IHC1].
+ etransitivity; [apply Nat.le_min_r | apply IHC2].
Qed.
*)

Lemma has_head_action_not_terminated : forall C, has_head_action C -> ~terminated C.
Proof.
induction C; intros; simpl; auto.
+ apply eta_not_terminated.
+ apply cond_not_terminated.
+ simpl in H.



Lemma terminated_has_head_action : forall C, ~(terminated C /\ has_head_action C).
Proof.
induction C; simpl; intro; inversion_clear H; auto.
+ 


Lemma terminated_does_not_reduce : forall C C' s s', terminated C -> ~(C,s) ---> (C',s').
Proof.
intros; intro.
elim (MCTo_to_weighted H0); clear H0; intros n Hn.
assert (forall k, k <= n -> ~(C,s)$k -n-> (C',s')); intros.
2: apply H0 with n; auto.
clear Hn; revert k H0 C H s C' s'.
induction n; intros; intro; [inversion H0 | case_eq k; intros]; rewrite H2 in H1; inversion H1.

+ rewrite <- H4 in H; inversion H.
+ clear C1 H1 s1 H2 C2 H3 s2 H5.
  generalize (Precongr_weighted_to _ _ _ H6); clear H6; intro.
  generalize (End_MCP _ H1); clear H1; intro.
  rewrite H1 in H7.
  eapply (IHn k0).
  2: apply H7.
  rewrite <- H4 in H; apply le_S_n in H.
  transitivity (n0+k0+m); auto with arith.
Qed.

Lemma fatsemi_ToEnd : forall C C' s s', (C;;C',s) ---> (End,s') ->
  {C = End /\ (C',s) ---> (End,s')} + {C' = End /\ (C,s) ---> (End,s')}.
Proof.
double induction C C'; intros; auto;
  try (right; rewrite fatsemi_End in H; auto).
- exfalso.
  generalize (MCTo_End_size _ _ _ H); simpl; intros.



- exfalso; clear X X0.
  generalize (MCTo_End_size _ _ _ H); simpl; intros.
  inversion H0.
  apply lt_irrefl with 0.
  apply lt_le_trans with 1; auto.
  rewrite <- H2 at 2.
  etransitivity.
  2: apply fatsemi_size.
  replace 1 with (0+1); auto.
  apply plus_le_compat; simpl; auto with arith.
- exfalso; clear X X0.
  generalize (MCTo_End_size _ _ _ H); simpl; clear H X1; intros.
  inversion H.
  apply lt_irrefl with 0.
  apply lt_le_trans with 1; auto.
  rewrite <- H1 at 2.
  etransitivity.
  2: apply fatsemi_size.
  replace 1 with (0+1); auto.
  apply plus_le_compat; simpl; auto with arith.
- exfalso; clear X X0.
  generalize (MCTo_End_size _ _ _ H); simpl; clear H X1; intros.
  inversion H.
  apply lt_irrefl with 0.
  apply lt_le_trans with 1; auto.
  rewrite <- H1 at 2.
  apply Nat.min_glb.
  + etransitivity.
    2: apply fatsemi_size.
    replace 1 with (0+1); auto.
    apply plus_le_compat; simpl; auto with arith.
  + etransitivity.
    2: apply fatsemi_size.
    replace 1 with (0+1); auto.
    apply plus_le_compat; simpl; auto with arith.
- exfalso; clear X X0.
  generalize (MCTo_End_size _ _ _ H); simpl; clear H X1 X2; intros.
  inversion H.
  apply lt_irrefl with 0.
  apply lt_le_trans with 1; auto.
  rewrite <- H1 at 2.
  apply Nat.min_glb.
  + etransitivity.
    2: apply fatsemi_size.
    replace 1 with (0+1); auto.
    apply plus_le_compat; simpl; auto with arith.
  + etransitivity.
    2: apply fatsemi_size.
    replace 1 with (0+1); auto.
    apply plus_le_compat; simpl; auto with arith.
Qed.

(** Semantic characterization - Lemma 1. *)
Lemma Lemma_1_1 : forall C C' s s' s'',
  MCToStar (C,s) (End,s') -> MCToStar (C',s') (End,s'') -> MCToStar (C;;C',s) (End,s'').
intros.
apply MCToStar_trans with (C',s'); auto.
replace (C',s') with (End;;C',s'); auto; apply fatsemi_ToStar; auto.
Qed.
*)

(*

Lemma Precongr_pn : forall C C', C ~<= C' ->
  forall p, In p (pn C') -> In p (pn C).




Lemma not_terminated_weird : forall {C s C' s' C''}, (C,s) ---> (C',s') -> C ~<= C'' -> ~terminated C''.
Proof.
intros; intro.
red in H1; simpl in H1; rewrite (not_End_MCP' _ H1) in H0.
rewrite (not_End_MCP' _ H0) in H.
revert H; apply terminated_does_not_reduce; apply Refl.
Qed.

(** Useful induction principle. *)
Lemma MCTo_induction : forall (P:Choreography -> State -> Choreography -> State -> Prop),
  (forall p e q C s, P (p#e --> q; C) s C (update s q (evaluate_on_state e s p))) ->
  (forall p q l C s, P (Sel p q l; C) s C s) ->
  (forall p q C1 C2 s, s p = s q -> P (If p == q Then C1 Else C2) s C1 s) ->
  (forall p q C1 C2 s, s p <> s q -> P (If p == q Then C1 Else C2) s C2 s) ->
  (forall C1 C1' C2 C2' s1 s2, Precongr C1 C1' -> Precongr C2' C2 -> P C1' s1 C2' s2 -> P C1 s1 C2 s2) ->
  forall C s C' s', (C,s) ---> (C',s') -> P C s C' s'.
Proof.
intros.
elim (MCTo_to_weighted _ _ H4); intros n Hn; clear H4.
assert (forall k, k <= n -> (C,s)$k -n-> (C',s') -> P C s C' s'); intros.
2: apply H4 with n; auto.
clear Hn; revert k H4 C s C' s' H5; induction n; intros.
+ rewrite <- (le_n_0_eq _ H4) in H5; inversion H5.
  induction C.
  - contradiction H6; red; simpl; apply Refl.
  - induction e; inversion H7; auto.
  - inversion H7; revert H11.
    case_eq (Value_dec (s p) (s p0)); intros Hs Hc'; inversion Hc'; rewrite <- H12.
    * rewrite Vdec.eqb_eq in Hs; auto.
    * rewrite Vdec.eqb_neq in Hs; auto.
+ inversion H5.
  induction C.
  - contradiction H6; red; simpl; apply Refl.
  - induction e; inversion H7; auto.
  - inversion H7; revert H12.
    case_eq (Value_dec (s p) (s p0)); intros Hs Hc'; inversion Hc'; rewrite <- H13.
    * rewrite Vdec.eqb_eq in Hs; auto.
    * rewrite Vdec.eqb_neq in Hs; auto.
 - apply H3 with C1' C2'; auto.
    * apply Precongr_weighted_to with n0; auto.
    * apply Precongr_weighted_to with m; auto.
    * apply IHn with k0; auto.
      rewrite <- H9 in H4.
      apply le_S_n in H4.
      transitivity (n0+k0+m); auto with arith.
Qed.

(** Some useful characterizations using size. *)
Lemma size_0_End : forall C, size C = 0 -> C = End.
Proof.
induction C; simpl; auto; intros; inversion H.
Qed.

Lemma MCTo_End_size : forall C s s', (C,s) ---> (End, s') -> size C = 1.
Proof.
intros.
assert (size C <> 0).
* intro.
  rewrite (size_0_End _ H0) in H.
  apply (terminated_does_not_reduce _ _ _ _ (Refl _) H).
* generalize (eq_refl End).
  generalize H0.
  apply MCTo_induction with (P:=fun C _ C' _ => size C <> 0 -> C' = End -> size C = 1) (s:=s) (C':=End) (s':=s'); simpl; auto; intros.
  + rewrite H2; auto.
  + rewrite H2; auto.
  + rewrite H3; auto.
  + rewrite H3; rewrite Nat.min_comm; auto.
  + rewrite H5 in H2; clear H5.
    generalize (not_End_MCP' _ H2); clear H2; intro.
    generalize (precongr_size_ge _ _ H1); intro.
    rewrite H3 in H5; auto.
    - inversion H5; auto.
      elim H4; auto with arith.
    - intro; apply H4.
      rewrite H6 in H5; auto with arith.
Qed.

End Applications.

Require Import Coq.Program.Equality.

Section Representation_principles.

(** Head reductions propagate by precongruence. *)
Lemma HeadTo_precongr_one : forall {C C' C'' s s' H}, (C,s)$H -H-> (C',s') -> C' ~< C'' ->
  exists C''', C ~< C''' /\ forall H', (C''',s)$H' -H-> (C'',s').
Proof.
intros.
revert C H H0.
dependent induction H1; intros.
(* EtaEta *)
+ induction C0; try induction e; inversion H1.
  - elim H0; apply Refl.
  - exists (p#e-->p0; eta2; eta1; C); split; auto.
    apply CtxEta; apply EtaEta; auto.
  - exists (Sel p p0 l; eta2; eta1; C); split; auto.
    apply CtxEta; apply EtaEta; auto.
  - case_eq (Value_dec (s p) (s p0)); intro; rewrite H2 in H3; inversion H3.
    * exists (If p == p0 Then eta2; eta1; C Else C0_2); split.
      apply CtxThen; apply EtaEta; auto.
      intro; simpl; rewrite <- H6; rewrite H2; auto.
    * exists (If p == p0 Then C0_1 Else (eta2; eta1; C)); split.
      apply CtxElse; apply EtaEta; auto.
      intro; simpl; rewrite <- H6; rewrite H2; auto.
(* EtaCond *)
+ induction C; try induction e; inversion H2.
  - elim H1; apply Refl.
  - exists (p0#e-->p1; If p == q Then eta; C1 Else (eta; C2)); split; auto.
    apply CtxEta; apply EtaCond; auto.
  - exists (Sel p0 p1 l; If p == q Then eta; C1 Else (eta; C2)); split; auto.
    apply CtxEta; apply EtaCond; auto.
  - case_eq (Value_dec (s p0) (s p1)); intro; rewrite H3 in H4; inversion H4.
    * exists (If p0 == p1 Then If p == q Then eta; C1 Else (eta; C2) Else C4); split.
      apply CtxThen; apply EtaCond; auto.
      intro; simpl; rewrite <- H7; rewrite H3; auto.
    * exists (If p0 == p1 Then C3 Else (If p == q Then eta; C1 Else (eta; C2))); split.
      apply CtxElse; apply EtaCond; auto.
      intro; simpl; rewrite <- H7; rewrite H3; auto.
(* CondEta *)
+ induction C; try induction e; inversion H2.
  - elim H1; apply Refl.
  - exists (p0#e-->p1; eta; If p == q Then C1 Else C2); split; auto.
    apply CtxEta; apply CondEta; auto.
  - exists (Sel p0 p1 l; eta; If p == q Then C1 Else C2); split; auto.
    apply CtxEta; apply CondEta; auto.
  - case_eq (Value_dec (s p0) (s p1)); intro; rewrite H3 in H4; inversion H4.
    * exists (If p0 == p1 Then eta; If p == q Then C1 Else C2 Else C4); split.
      apply CtxThen; apply CondEta; auto.
      intro; simpl; rewrite <- H7; rewrite H3; auto.
    * exists (If p0 == p1 Then C3 Else (eta; If p == q Then C1 Else C2)); split.
      apply CtxElse; apply CondEta; auto.
      intro; simpl; rewrite <- H7; rewrite H3; auto.
(* CondCond *)
+ induction C; try induction e; inversion H1.
  - elim H0; apply Refl.
  - exists (p0#e-->p1; (If r == s0 Then If p == q Then C1 Else C3 Else (If p == q Then C2 Else C4))); split; auto.
    apply CtxEta; apply CondCond; auto.
  - exists (Sel p0 p1 l;(If r == s0 Then If p == q Then C1 Else C3 Else (If p == q Then C2 Else C4))); split; auto.
    apply CtxEta; apply CondCond; auto.
  - case_eq (Value_dec (s p0) (s p1)); intro; rewrite H2 in H3; inversion H3.
    * exists (If p0 == p1 Then (If r == s0 Then If p == q Then C1 Else C3 Else (If p == q Then C2 Else C4)) Else C6); split; auto.
      apply CtxThen; apply CondCond; auto.
      intro; simpl; rewrite <- H6; rewrite H2; auto.
    * exists (If p0 == p1 Then C5 Else (If r == s0 Then If p == q Then C1 Else C3 Else (If p == q Then C2 Else C4))); split; auto.
      apply CtxElse; apply CondCond; auto.
      intro; simpl; rewrite <- H6; rewrite H2; auto.
(* CtxEta *)
+ induction C; try induction e; inversion H0.
  - elim H; apply Refl.
  - exists (p#e-->p0; eta; C2); split; auto.
    apply CtxEta; apply CtxEta; auto.
  - exists (Sel p p0 l; eta; C2); split; auto.
    apply CtxEta; apply CtxEta; auto.
  - case_eq (Value_dec (s p) (s p0)); intro; rewrite H2 in H3; inversion H3.
    * exists (If p == p0 Then eta; C2 Else C4); split; auto.
      apply CtxThen; apply CtxEta; auto.
      intro; simpl; rewrite <- H6; rewrite H2; auto.
    * exists (If p == p0 Then C3 Else (eta; C2)); split; auto.
      apply CtxElse; apply CtxEta; auto.
      intro; simpl; rewrite <- H6; rewrite H2; auto.
(* CtxThen *)
+ induction C0; try induction e; inversion H0.
  - elim H; apply Refl.
  - exists (p0#e-->p1; If p == q Then C'' Else C); split; auto.
    apply CtxEta; apply CtxThen; auto.
  - exists (Sel p0 p1 l; If p == q Then C'' Else C); split; auto.
    apply CtxEta; apply CtxThen; auto.
  - case_eq (Value_dec (s p0) (s p1)); intro; rewrite H2 in H3; inversion H3.
    * exists (If p0 == p1 Then If p == q Then C'' Else C Else C0_2); split; auto.
      apply CtxThen; apply CtxThen; auto.
      intro; simpl; rewrite <- H6; rewrite H2; auto.
    * exists (If p0 == p1 Then C0_1 Else (If p == q Then C'' Else C)); split; auto.
      apply CtxElse; apply CtxThen; auto.
      intro; simpl; rewrite <- H6; rewrite H2; auto.
(* CtxElse *)
+ induction C0; try induction e; inversion H0.
  - elim H; apply Refl.
  - exists (p0#e-->p1; If p == q Then C Else C''); split; auto.
    apply CtxEta; apply CtxElse; auto.
  - exists (Sel p0 p1 l; If p == q Then C Else C''); split; auto.
    apply CtxEta; apply CtxElse; auto.
  - case_eq (Value_dec (s p0) (s p1)); intro; rewrite H2 in H3; inversion H3.
    * exists (If p0 == p1 Then If p == q Then C Else C'' Else C0_2); split; auto.
      apply CtxThen; apply CtxElse; auto.
      intro; simpl; rewrite <- H6; rewrite H2; auto.
    * exists (If p0 == p1 Then C0_1 Else (If p == q Then C Else C'')); split; auto.
      apply CtxElse; apply CtxElse; auto.
      intro; simpl; rewrite <- H6; rewrite H2; auto.
Qed.

Lemma HeadTo_precongr : forall {C C' C'' s s' H}, (C,s)$H -H-> (C',s') -> C' ~<= C'' ->
  exists C''', C ~<= C''' /\ forall H', (C''',s)$H' -H-> (C'',s').
(* Obsolete proof - follows from stronger lemma in LCF.v *)
Proof.
intros.
revert C H H0.
dependent induction H1; intros.
+ exists C0; repeat split; intros; try apply Refl.
  rewrite (HeadTo_wd (C0,s) H' H); auto.
+ elim (HeadTo_precongr_one H2 H); intros.
  rename x into C'; inversion_clear H3.
  assert (~terminated C').
  - apply (not_terminated_weird (C:=C) (C':=C1) (s:=s) (s':=s')); auto.
    rewrite <- H2; apply HeadTo_Soundness.
    apply Precongr_step_to; auto.
  - elim (IHPrecongr _ _ (H5 H3)); clear IHPrecongr; intros.
    rename x into C''; inversion_clear H6.
    exists C''; split; auto.
    apply MCP_Step with C'; auto.
Qed.

(** Currently this lemma could be stronger, but once unfolding is around things get different. *)
Lemma MCTo_square : forall C C' s s' H, (C,s)$H -H-> (C',s') ->
  forall C'', C ~< C'' -> exists C''', (C'',s) ---> (C''',s') /\ (C' = C''' \/ C' ~< C''').
Proof.
intros.
revert C' s' H0; induction H1; intros.
+ exists C'; split; auto; inversion H1; induction eta1.
  - eapply C_Struct.
    * apply Precongr_step_to; apply EtaEta; apply independent_sym; auto.
    * apply Refl.
    * apply C_Com.
  - eapply C_Struct.
    * apply Precongr_step_to; apply EtaEta; apply independent_sym; auto.
    * apply Refl.
    * apply C_Sel.
+ exists C'; inversion H2; induction eta; split; auto.
  - eapply C_Struct.
    * apply Precongr_step_to; apply CondEta; auto.
    * apply Refl.
    * apply C_Com.
  - eapply C_Struct.
    * apply Precongr_step_to; apply CondEta; auto.
    * apply Refl.
    * apply C_Sel.
+ exists C'; split; auto; inversion H2; revert H4; case_eq (Value_dec (s p) (s q)); intros.
  - eapply C_Struct.
    * apply Precongr_step_to; apply EtaCond; auto.
    * apply Refl.
    * apply C_Then; apply Vdec.eqb_eq; auto.
  - eapply C_Struct.
    * apply Precongr_step_to; apply EtaCond; auto.
    * apply Refl.
    * apply C_Else; apply Vdec.eqb_neq; auto.
+ exists C'; split; auto; inversion H1; revert H3; case_eq (Value_dec (s p) (s q)); intros.
  - eapply C_Struct.
    * apply Precongr_step_to; apply CondCond; apply disjoint_sym; auto.
    * apply Refl.
    * apply C_Then; apply Vdec.eqb_eq; auto.
  - eapply C_Struct.
    * apply Precongr_step_to; apply CondCond; apply disjoint_sym; auto.
    * apply Refl.
    * apply C_Else; apply Vdec.eqb_neq; auto.
+ exists C2; inversion H0; induction eta; inversion H3; split; auto.
  - apply C_Com.
  - rewrite <- H4; auto.
  - apply C_Sel.
  - rewrite <- H4; auto.
+ inversion H0; revert H3; case_eq (Value_dec (s p) (s q)); intros; inversion H3.
  - exists C''; split.
    * apply C_Then; apply Vdec.eqb_eq; rewrite <- H6; auto.
    * rewrite <- H5; auto.
  - exists C; split.
    * rewrite <- H5; apply C_Else; rewrite <- Vdec.eqb_neq; rewrite <- H6; auto.
    * rewrite H5; auto.
+ inversion H0; revert H3; case_eq (Value_dec (s p) (s q)); intros; inversion H3.
  - exists C; split.
    * rewrite <- H5; apply C_Then; apply Vdec.eqb_eq; rewrite <- H6; auto.
    * rewrite H5; auto.
  - exists C''; split.
    * apply C_Else; apply Vdec.eqb_neq; rewrite <- H6; auto.
    * rewrite <- H5; auto.
Qed.

Lemma MCTo_head_precongr : forall C s H C' s' C'' H'' C''' s''', (C,s)$H -H-> (C',s') ->
  C ~< C'' -> (C'',s)$H'' -H-> (C''',s''') -> (s' = s''' /\ (C' = C''' \/ C' ~< C''')) \/
  exists C0 s1 s2, (C',s') ---> (C0,s1) /\ (C''',s''') ---> (C0,s2) /\ eq_state_ext s1 s2.
Proof.
intros.
induction H1.
+ right.
  induction eta1; induction eta2; inversion H0; inversion H2; clear H H'' H0 H2 H4 H6.
  - (* Com/Com *)
    rename p0 into q; rename p1 into p'; rename p2 into q'; rename e0 into e'.
    set (H := eta_not_terminated (p'#e'-->q') C).
    exists C; eexists; eexists; split; [apply C_Com | split; [apply C_Com | intro]].
    rename p0 into r; destroy_as H1 H'.
    rewrite update_independent; auto.
    repeat rewrite read_update; auto.
  - (* Com/Sel *)
    rename p0 into q; rename p1 into p'; rename p2 into q'.
    set (H := eta_not_terminated (Sel p' q' l) C).
    exists C; eexists; eexists; split; [apply C_Sel | split; [apply C_Com | intro; auto]].
  - (* Sel/Com *)
    rename p0 into q; rename p1 into p'; rename p2 into q'.
    set (H := eta_not_terminated (p'#e-->q') C).
    exists C; eexists; eexists; split; [apply C_Com | split; [apply C_Sel | intro]].
    rewrite H5; auto.
  - (* Sel/Sel *)
    rename p0 into q; rename p1 into p'; rename p2 into q'; rename l0 into l'.
    set (H := eta_not_terminated (Sel p' q' l') C).
    exists C; eexists; eexists; split; [apply C_Sel | split; [apply C_Sel | intro]].
    rewrite <- H5, H7; auto.
+ right.
  induction eta; inversion H0; revert H2; simpl; case_eq (Value_dec (s p) (s q)); intros; inversion H4.
  - (* Then/Com *)
    exists C1, s', s'.
    split; [idtac | split; [idtac | intro; reflexivity]].
    * rewrite <- H9, <- H6; apply C_Then; auto.
      inversion_clear H1; inversion_clear H3.
      repeat rewrite update_read'; auto.
      apply Vdec.eqb_eq; auto.
    * rewrite <- H9, <- H6; apply C_Com.
  - (* Else/Com *)
    exists C2, s', s'.
    split; [idtac | split; [idtac | intro; reflexivity]].
    * rewrite <- H9; rewrite <- H6; apply C_Else; auto.
      inversion_clear H1; inversion_clear H3.
      repeat rewrite update_read'; auto.
      apply Vdec.eqb_neq; auto.
    * rewrite <- H9, <- H6; apply C_Com.
  - (* Then/Sel *)
    exists C1, s', s'.
    split; [idtac | split; [idtac | intro; reflexivity]].
    * apply C_Then; auto.
      inversion_clear H1; inversion_clear H3.
      rewrite <- H6; apply Vdec.eqb_eq; auto.
    * rewrite <- H9, <- H6; apply C_Sel.
  - (* Else/Sel *)
    exists C2, s', s'.
    split; [idtac | split; [idtac | intro; reflexivity]].
    * rewrite <- H6; apply C_Else; auto.
      inversion_clear H1; inversion_clear H3.
      apply Vdec.eqb_neq; auto.
    * rewrite <- H9, <- H6; apply C_Sel.
+ right.
  induction eta; inversion H2; revert H0; simpl; case_eq (Value_dec (s p) (s q)); intros; inversion H4.
  - (* Com/Then *)
    exists C1, s''', s'''.
    split; [idtac | split; [idtac | intro; reflexivity]].
    * rewrite <- H9, <- H6; apply C_Com.
    * rewrite <- H9; rewrite <- H6; apply C_Then; auto.
      inversion_clear H1; inversion_clear H3.
      repeat rewrite update_read'; auto.
      apply Vdec.eqb_eq; auto.
  - (* Com/Else *)
    exists C2, s''', s'''.
    split; [idtac | split; [idtac | intro; reflexivity]].
    * rewrite <- H9, <- H6; apply C_Com.
    * rewrite <- H9; rewrite <- H6; apply C_Else; auto.
      inversion_clear H1; inversion_clear H3.
      repeat rewrite update_read'; auto.
      apply Vdec.eqb_neq; auto.
  - (* Sel/Then *)
    exists C1, s''', s'''.
    split; [idtac | split; [idtac | intro; reflexivity]].
    * rewrite <- H9, <- H6; apply C_Sel.
    * apply C_Then; auto.
      inversion_clear H1; inversion_clear H3.
      rewrite <- H6; apply Vdec.eqb_eq; auto.
  - (* Sel/Else *)
    exists C2, s''', s'''.
    split; [idtac | split; [idtac | intro; reflexivity]].
    * rewrite <- H9, <- H6; apply C_Sel.
    * rewrite <- H6; apply C_Else; auto.
      inversion_clear H1; inversion_clear H3.
      apply Vdec.eqb_neq; auto.
+ right.
  revert H0 H2; destroy_as H1 H'.
  simpl; case_eq (Value_dec (s p) (s q)); simpl; case_eq (Value_dec (s r) (s s0)); intros;
  inversion H5; clear H5; inversion H6; clear H6.
  - (* Then/Then *)
    rewrite <- H10, <- H9; exists C1, s, s; split;
    [apply C_Then | split; [apply C_Then | intro; auto]];
    rewrite Vdec.eqb_eq in H3, H4; auto.
  - (* Else/Then *)
    rewrite <- H10, <- H9; exists C2, s, s; split;
    [apply C_Else | split; [apply C_Then | intro; auto]];
    rewrite Vdec.eqb_neq in H3; rewrite Vdec.eqb_eq in H4; auto.
  - (* Then/Else *)
    rewrite <- H10, <- H9; exists C3, s, s; split;
    [apply C_Then | split; [apply C_Else | intro; auto]];
    rewrite Vdec.eqb_eq in H3; rewrite Vdec.eqb_neq in H4; auto.
  - (* Else/Else *)
    rewrite <- H10, <- H9; exists C4, s, s; split;
    [apply C_Else | split; [apply C_Else | intro; auto]];
    rewrite Vdec.eqb_neq in H3, H4; auto.
+ (* Com *)
  left; clear IHPrecongr_step.
  induction eta; inversion H0; inversion H2; split; try rewrite <- H4, <- H6; auto.
  transitivity s; auto.
+ left; clear IHPrecongr_step.
  inversion H0; inversion H2; revert H4 H5.
  case_eq (Value_dec (s p) (s q)); intros; inversion H4; inversion H5; split; try (transitivity s; auto);
  rewrite <- H7, <- H9; auto.
+ left; clear IHPrecongr_step.
  inversion H0; inversion H2; revert H4 H5.
  case_eq (Value_dec (s p) (s q)); intros; inversion H4; inversion H5; split; try (transitivity s; auto);
  rewrite <- H7; rewrite <- H9; auto.
Qed.

(** Canonical representation for reductions. *)
Lemma MCTo_canonical_weak : forall {C s C' s'}, (C,s) ---> (C',s') -> exists C'' C''', C ~<= C'' /\ C''' ~<= C' /\ forall H, (C'',s)$H -H-> (C''',s').
Proof.
intros.
dependent induction H.
+ exists (p#e-->q;C'); exists C'; repeat split; auto; apply Refl.
+ exists (Sel p q l; C'); exists C'; repeat split; auto; apply Refl.
+ exists (If p == q Then C' Else C2); exists C'; repeat split; try apply Refl.
  intros; simpl; rewrite <- Vdec.eqb_eq in H; unfold Value_dec; rewrite H; auto.
+ exists (If p == q Then C1 Else C'); exists C'; repeat split; try apply Refl.
  intros; simpl; rewrite <- Vdec.eqb_eq in H.
  unfold Value_dec; rewrite (not_true_is_false _ H); auto.
+ elim (IHMCTo _ _ _ _ (JMeq_refl _) (JMeq_refl _)); clear IHMCTo; intros.
  rename x into C''; inversion_clear H2.
  rename x into C'''; inversion_clear H3.
  inversion_clear H4.
  exists C''; exists C'''; repeat split; auto.
  - apply Precongr_Trans with C1'; auto.
  - apply Precongr_Trans with C2'; auto.
Qed.

Lemma MCTo_canonical : forall {C s C' s'}, (C,s) ---> (C',s') -> exists C'', C ~<= C'' /\ forall H, (C'',s)$H -H-> (C',s').
Proof.
intros.
elim (MCTo_canonical_weak H); intros.
rename x into C1; inversion_clear H0.
rename x into C2; inversion_clear H1.
inversion_clear H2.
generalize (not_terminated_weird H H0); intro.
generalize (H3 H2); clear H3; intro.
elim (HeadTo_precongr H3 H1); intros.
rename x into C3; inversion_clear H4.
exists C3; split; auto.
apply Precongr_Trans with C1; auto.
Qed.

End Representation_principles.
*)

(** There are several interesting notions of size of a choreography: size of the AST,
    minimal number of reductions until we reach a terminal, ... *)
Fixpoint AST_size (C:Choreography) : nat :=
  match C with
  | End => 1
  | Call X => 1
  | eta; C' => 1 + AST_size C'
  | If p == q Then C1 Else C2 => 1 + AST_size C1 + AST_size C2
  | Def X == C1 In C2 => 1 + AST_size C1 + AST_size C2
  end.


Lemma fatsemi_To_inv : forall C C' s C'' s'', (C;;C',s) ---> (C'',s'') ->
  (exists C0, (C,s) ---> (C0,s'') /\ (C0;;C') ~<= C'')
  \/ (exists C0', (C',s) ---> (C0',s'') /\ (C;;C0') ~<= C'').
Proof.
intros.
elim (MCTo_canonical H); intros CC HCC; destroy HCC.
Abort.


Section Applications.

(** Stronger versions of existing lemmas. *)

Lemma HeadTo_precongr : forall {C C' s s' H}, (C,s)$H -H-> (C',s') ->
  forall {n C''}, C'$n ~<n C'' ->
  exists C''', C$n ~<n C''' /\ forall H', (C''',s)$H' -H-> (C'',s').
Proof.
intros.
revert C C' C'' H H0 H1.
induction n; intros; inversion H1.
+ rewrite <- H4; clear C'' H1 H4 C0 H3.
  exists C; repeat split; intros; try apply PBase.
  rewrite (HeadTo_wd (_,s) H' H); auto.
+ clear n0 H2 C0 H5 C''0 H6; rename C'0 into C0.
  elim (HeadTo_precongr_one H0 H3); intros.
  rename x into C0'; inversion_clear H2.
  assert (~terminated C0').
  - apply (not_terminated_weird (C:=C) (C':=C') (s:=s) (s':=s')); auto.
    * rewrite <- H0; apply HeadTo_Soundness.
    * apply Precongr_step_to; auto.
  - elim (IHn _ _ _ _ (H6 H2) H4); clear IHn; intros.
    rename x into C0''; inversion_clear H7.
    exists C0''; split; auto.
    apply PStep with C0'; auto.
Qed.

Lemma MCTo_square : forall C C' s s' H, (C,s)$H -H-> (C',s') ->
  forall C'', C ~< C'' -> (exists n, n <= 2 /\ (C'',s)$n -n-> (C',s')) \/
  exists C''' HC'', (C'',s)$HC'' -H-> (C''',s') /\ C' ~< C'''.
Proof.
intros.
revert C' s' H0; induction H1; intros.
+ left; exists 2; split; auto; inversion H1; induction eta1.
  - replace 2 with (S (1 + 0 + 0)); auto; eapply Cons.
    * eapply PStep; [apply EtaEta; apply independent_sym; auto | apply PBase].
    * apply Base with (eta_not_terminated (p#e-->p0) (eta2;C)); simpl; auto.
    * apply PBase.
  - replace 2 with (S (1 + 0 + 0)); auto; eapply Cons.
    * eapply PStep; [apply EtaEta; apply independent_sym; auto | apply PBase].
    * apply Base with (eta_not_terminated (Sel p p0 l) (eta2;C)); simpl; auto.
    * apply PBase.
+ left; exists 2; split; auto; inversion H2; induction eta.
  - replace 2 with (S (1 + 0 + 0)); auto; eapply Cons.
    * eapply PStep; [apply CondEta; auto | apply PBase].
    * apply Base with (eta_not_terminated (p0#e-->p1) (If p == q Then C1 Else C2)); simpl; auto.
    * apply PBase.
  - replace 2 with (S (1 + 0 + 0)); auto; eapply Cons.
    * eapply PStep; [apply CondEta; auto | apply PBase].
    * apply Base with (eta_not_terminated (Sel p0 p1 l) (If p == q Then C1 Else C2)); simpl; auto.
    * apply PBase.
+ left; exists 2; split; auto; inversion H2; revert H4; case_eq (s p =? s q); intros.
  - replace 2 with (S (1 + 0 + 0)); auto; eapply Cons.
    * eapply PStep; [apply EtaCond; auto | apply PBase].
    * apply Base with (cond_not_terminated p q (eta;C1) (eta;C2)); simpl; rewrite H3; auto.
    * apply PBase.
  - replace 2 with (S (1 + 0 + 0)); auto; eapply Cons.
    * eapply PStep; [apply EtaCond; auto | apply PBase].
    * apply Base with (cond_not_terminated p q (eta;C1) (eta;C2)); simpl; rewrite H3; auto.
    * apply PBase.
+ left; exists 2; split; auto; inversion H1; revert H3; case_eq (s p =? s q); intros.
  - replace 2 with (S (1 + 0 + 0)); auto; eapply Cons.
    * eapply PStep; [apply CondCond; apply disjoint_sym; auto | apply PBase].
    * apply Base with (cond_not_terminated p q (If r == s0 Then C1 Else C2) (If r == s0 Then C3 Else C4)); simpl; rewrite H2; auto.
    * apply PBase.
  - replace 2 with (S (1 + 0 + 0)); auto; eapply Cons.
    * eapply PStep; [apply CondCond; apply disjoint_sym; auto | apply PBase].
    * apply Base with (cond_not_terminated p q (If r == s0 Then C1 Else C2) (If r == s0 Then C3 Else C4)); simpl; rewrite H2; auto.
    * apply PBase.
+ right; inversion H0; induction eta; inversion H3; rewrite <- H4.
  - exists C2, (eta_not_terminated (p#e-->p0) C2); split; auto.
  - exists C2, (eta_not_terminated (Sel p p0 l) C2); split; auto.
+ inversion H0; revert H3; case_eq (s p =? s q); intros; inversion H3; rewrite <- H5.
  - right; exists C'', (cond_not_terminated p q C'' C); split; simpl; auto.
    rewrite H6 in H2; rewrite H2; auto.
  - left; exists 0; split; auto.
    apply Base with (cond_not_terminated p q C'' C); simpl.
    rewrite H6 in H2; rewrite H2; auto.
+ inversion H0; revert H3; case_eq (s p =? s q); intros; inversion H3; rewrite <- H5.
  - left; exists 0; split; auto.
    apply Base with (cond_not_terminated p q C C''); simpl.
    rewrite H6 in H2; rewrite H2; auto.
  - right; exists C'', (cond_not_terminated p q C C''); split; simpl; auto.
    rewrite H6 in H2; rewrite H2; auto.
Qed.

Lemma O_plus_O : forall m n, m + n = 0 -> m = 0.
induction m; auto.
intros.
simpl in H; inversion H.
Qed.

Lemma MCTo_Precongr : forall C s C' s' C'' s'', (C,s) ---> (C',s') -> (C,s) ---> (C'',s'') ->
  (C' ~<= C'' /\ eq_state_ext s' s'') \/ exists C''' s''', (C',s') ---> (C''',s''') /\ (C'',s'') ---> (C''',s''').
intros.
elim (MCTo_canonical H); intros C1 HC1; destroy HC1.
elim (MCTo_canonical H0); intros C2 HC2; destroy HC2.
pose (not_terminated_weird H H1) as C1t; clearbody C1t.
generalize (HC1 C1t); clear H HC1; intro HC1.
pose (not_terminated_weird H0 H2) as C2t; clearbody C2t.
generalize (HC2 C2t); clear H0 HC2; intro HC2.
elim (Precongr_to_weighted _ _ H1); clear H1; intros n1 Hn1.
elim (Precongr_to_weighted _ _ H2); clear H2; intros n2 Hn2.
set (n := S (n1+n2)).
assert (n1+n2<n) as Hn; auto; clearbody n.
assert ((exists k, k<=n /\ C'$k ~<n C'' /\ eq_state_ext s' s'') \/
        (exists C1' C2' C''' s''' n1' n2',
         n1'+n2'<=n /\ C'$n1' ~<n C1' /\ C''$n2' ~<n C2' /\
         ~terminated C1' /\ ~terminated C2' /\
        (forall H1, (C1',s')$H1 -H-> (C''',s''')) /\ forall H2, (C2',s'')$H2 -H-> (C''',s'''))).
2: {
  inversion_clear H.
  + left; rename H0 into H'; destroy H'.
    split; auto.
    apply Precongr_weighted_to with x; auto.
  + right; elim H0; clear H0; intros C1' HC1'.
    elim HC1'; clear HC1'; intros C2' HC2'.
    elim HC2'; clear HC2'; intros C''' HC'''.
    elim HC'''; clear HC'''; intros s''' Hs'''.
    elim Hs'''; clear Hs'''; intros n1' Hn1'.
    elim Hn1'; clear Hn1'; intros n2' Hn2'.
    destroy Hn2'.
    exists C''', s'''; split.
    * apply C_Struct with C1' C'''; [
        apply Precongr_weighted_to with n1'; auto
     | apply Refl
     | rewrite <- (H4 H2) ; apply HeadTo_Soundness].
    * apply C_Struct with C2' C'''; [
        apply Precongr_weighted_to with n2'; auto
     | apply Refl
     | rewrite <- (Hn2' H3) ; apply HeadTo_Soundness].
  }
revert n1 n2 Hn C C1 Hn1 C2 Hn2 s C' s' C1t HC1 C'' s'' C2t HC2; induction n; intros;
  try (inversion Hn; fail).
inversion Hn1; inversion Hn2.
- (* Head / Head *)
  revert Hn1 Hn2.
  revert C1t HC1; rewrite <- H, <- H1; clear Hn n1 H C0 H0 C1 H1.
  revert C2t HC2; rewrite <- H2, <- H4; clear n2 H2 C3 H3 C2 H4.
  left; exists 0; split; auto with arith.
  rewrite <- (HeadTo_wd (_,s) C1t C2t) in HC2; rewrite HC1 in HC2; inversion HC2.
  split; try intro; auto.
  apply PBase.
- revert Hn C1t HC1; rewrite <- H, <- H1, <- H4; clear n1 H C0 H0 C1 H1 n2 H4 C''0 H6 C3 H5 Hn1 Hn2.
  rename C'0 into C0; intros.
  simpl in Hn; apply lt_S_n in Hn.
  inversion H2; clear H2.
  + revert H3 C1t HC1; rewrite <- H0, <- H1; clear C C0 H0 H1; intros.
    induction eta1; inversion HC1.
    * revert C1t HC1; rewrite <- H1, <- H2; clear C' H1 s' H2; intros.
      rename p0 into q; set (s' := update s q (evaluate_on_state e s p)).
      pose (eta_not_terminated eta2 (p#e-->q;C1)) as HC1'; clearbody HC1'.
      set (c := (HeadTo (_,s) HC1')).
      assert (HeadTo (_,s) HC1' = c); auto; clearbody c; induction c.
      rename a into C3; rename b into s3.
      elim (IHn 0 _ Hn _ _ PBase _ H3 s _ _ _ H0 _ _ _ HC2); clear IHn; intro IHn.
      ++ elim IHn; clear IHn; intros k Hk; destroy Hk.
         right; exists (eta2; C1), C'', C'', s'', 0, 0.
         repeat split; auto with arith.
(* Hmmm. *)

(* old attempt *)
elim (MCTo_to_weighted _ _ H); intros n' Hn'; clear H.
elim (MCTo_to_weighted _ _ H0); intros n'' Hn''; clear H0.
set (n := S (n'+n'')).
assert (n'+n''<n) as Hn; auto; clearbody n.
assert ((exists k, k<=n /\ C'$k ~<n C'' /\ eq_state_ext s' s'') \/
        (exists C''' s''' m' m'', m'+m''<=n /\ (C',s')$m' -n-> (C''',s''') /\ (C'',s'')$m'' -n-> (C''',s'''))).
2: {
  inversion_clear H.
  + left; rename H0 into H'; destroy H'.
    split; auto.
    apply Precongr_weighted_to with x; auto.
  + right; elim H0; clear H0; intros C''' HC'''.
    elim HC'''; clear HC'''; intros s''' Hs'''.
    elim Hs'''; clear Hs'''; intros m' Hm'.
    elim Hm'; clear Hm'; intros m'' Hm''.
    inversion_clear Hm''.
    inversion_clear H0.
    exists C''', s'''; split.
    * apply MCTo_weighted_to with m'; auto.
    * apply MCTo_weighted_to with m''; auto.
  }
revert n' n'' Hn C s C' s' C'' s'' Hn' Hn''; induction n; intros;
  try (inversion Hn; fail).
inversion Hn'; inversion Hn''.
- (* Head / Head *)
  revert Hn' Hn''.
  rewrite <- H1; clear Hn n' H1 c H2 c' H3.
  rewrite <- H6; clear n'' H6 c0 H7 c'0 H8.
  left; exists 0; split; auto with arith.
  rewrite <- (HeadTo_wd _ H H4) in H5; rewrite H0 in H5; inversion H5.
  split; try intro; auto.
  apply PBase.
- revert Hn Hn'; rewrite <- H1; clear n' H1 c H2 c' H3; simpl; intros.
  clear C1 H4 s1 H5 C2 H6 s2 H8.
  set (Hx := Cons _ _ H9 H10 PBase); clearbody Hx.
  assert (S (n0+k+0) < n).
  elim (IHn _ _ _ _ _ _ _ _ _ Hn' Hx).



Lemma MCTo_head_precongr : forall C s H C' s' C'' H'' C''' s''', (C,s)$H -H-> (C',s') ->
  C ~< C'' -> (C'',s)$H'' -H-> (C''',s''') -> (s' = s''' /\ (C' = C''' \/ C' ~< C''')) \/
  exists C0 s1 s2, (C',s') ---> (C0,s1) /\ (C''',s''') ---> (C0,s2) /\ eq_state_ext s1 s2.
Proof.
intros.
induction H1.
+ right.
  induction eta1; induction eta2; inversion H0; inversion H2; clear H H'' H0 H2 H4 H6.
  - (* Com/Com *)
    rename p0 into q; rename p1 into p'; rename p2 into q'; rename e0 into e'.
    set (H := eta_not_terminated (p'#e'-->q') C).
    exists C; eexists; eexists; split; [apply C_Com | split; [apply C_Com | intro]].
    rename p0 into r; rename H1 into H'; destroy H'.
    rewrite update_independent; auto.
    repeat rewrite read_update; auto.
  - (* Com/Sel *)
    rename p0 into q; rename p1 into p'; rename p2 into q'.
    set (H := eta_not_terminated (Sel p' q' l) C).
    exists C; eexists; eexists; split; [apply C_Sel | split; [apply C_Com | intro; auto]].
  - (* Sel/Com *)
    rename p0 into q; rename p1 into p'; rename p2 into q'.
    set (H := eta_not_terminated (p'#e-->q') C).
    exists C; eexists; eexists; split; [apply C_Com | split; [apply C_Sel | intro]].
    rewrite H5; auto.
  - (* Sel/Sel *)
    rename p0 into q; rename p1 into p'; rename p2 into q'; rename l0 into l'.
    set (H := eta_not_terminated (Sel p' q' l') C).
    exists C; eexists; eexists; split; [apply C_Sel | split; [apply C_Sel | intro]].
    rewrite <- H5, H7; auto.
+ right.
  induction eta; inversion H0; revert H2; simpl; case_eq (s p =? s q); intros; inversion H4.
  - (* Then/Com *)
    exists C1, s', s'.
    split; [idtac | split; [idtac | intro; reflexivity]].
    * rewrite <- H9, <- H6; apply C_Then; auto.
      inversion_clear H1; inversion_clear H3.
      rewrite H6.
      change (evaluate_on_state this s' p = evaluate_on_state this s' q).
      rewrite <- H6; repeat rewrite read_update with (e:=this); auto.
      rewrite Nat.eqb_eq in H2; auto.
    * rewrite <- H9, <- H6; apply C_Com.
  - (* Else/Com *)
    exists C2, s', s'.
    split; [idtac | split; [idtac | intro; reflexivity]].
    * rewrite <- H9; rewrite <- H6; apply C_Else; auto.
      inversion_clear H1; inversion_clear H3.
      rewrite H6.
      change (evaluate_on_state this s' p <> evaluate_on_state this s' q).
      rewrite <- H6; repeat rewrite read_update with (e:=this); auto.
      rewrite Nat.eqb_neq in H2; auto.
    * rewrite <- H9, <- H6; apply C_Com.
  - (* Then/Sel *)
    exists C1, s', s'.
    split; [idtac | split; [idtac | intro; reflexivity]].
    * apply C_Then; auto.
      inversion_clear H1; inversion_clear H3.
      rewrite <- H6; rewrite Nat.eqb_eq in H2; auto.
    * rewrite <- H9, <- H6; apply C_Sel.
  - (* Else/Sel *)
    exists C2, s', s'.
    split; [idtac | split; [idtac | intro; reflexivity]].
    * rewrite <- H6; apply C_Else; auto.
      inversion_clear H1; inversion_clear H3.
      rewrite Nat.eqb_neq in H2; auto.
    * rewrite <- H9, <- H6; apply C_Sel.
+ right.
  induction eta; inversion H2; revert H0; simpl; case_eq (s p =? s q); intros; inversion H4.
  - (* Com/Then *)
    exists C1, s''', s'''.
    split; [idtac | split; [idtac | intro; reflexivity]].
    * rewrite <- H9, <- H6; apply C_Com.
    * rewrite <- H9; rewrite <- H6; apply C_Then; auto.
      inversion_clear H1; inversion_clear H3.
      rewrite H6.
      change (evaluate_on_state this s''' p = evaluate_on_state this s''' q).
      rewrite <- H6; repeat rewrite read_update with (e:=this); auto.
      rewrite Nat.eqb_eq in H0; auto.
  - (* Com/Else *)
    exists C2, s''', s'''.
    split; [idtac | split; [idtac | intro; reflexivity]].
    * rewrite <- H9, <- H6; apply C_Com.
    * rewrite <- H9; rewrite <- H6; apply C_Else; auto.
      inversion_clear H1; inversion_clear H3.
      rewrite H6.
      change (evaluate_on_state this s''' p <> evaluate_on_state this s''' q).
      rewrite <- H6; repeat rewrite read_update with (e:=this); auto.
      rewrite Nat.eqb_neq in H0; auto.
  - (* Sel/Then *)
    exists C1, s''', s'''.
    split; [idtac | split; [idtac | intro; reflexivity]].
    * rewrite <- H9, <- H6; apply C_Sel.
    * apply C_Then; auto.
      inversion_clear H1; inversion_clear H3.
      rewrite <- H6; rewrite Nat.eqb_eq in H0; auto.
  - (* Sel/Else *)
    exists C2, s''', s'''.
    split; [idtac | split; [idtac | intro; reflexivity]].
    * rewrite <- H9, <- H6; apply C_Sel.
    * rewrite <- H6; apply C_Else; auto.
      inversion_clear H1; inversion_clear H3.
      rewrite Nat.eqb_neq in H0; auto.
+ right.
  revert H0 H2; rename H1 into H'; destroy H'.
  simpl; case_eq (s p =? s q); simpl; case_eq (s r =? s s0); intros;
  inversion H5; clear H5; inversion H6; clear H6.
  - (* Then/Then *)
    rewrite <- H10, <- H9; exists C1, s, s; split;
    [apply C_Then | split; [apply C_Then | intro; auto]];
    rewrite Nat.eqb_eq in H3, H4; auto.
  - (* Else/Then *)
    rewrite <- H10, <- H9; exists C2, s, s; split;
    [apply C_Else | split; [apply C_Then | intro; auto]];
    rewrite Nat.eqb_neq in H3; rewrite Nat.eqb_eq in H4; auto.
  - (* Then/Else *)
    rewrite <- H10, <- H9; exists C3, s, s; split;
    [apply C_Then | split; [apply C_Else | intro; auto]];
    rewrite Nat.eqb_eq in H3; rewrite Nat.eqb_neq in H4; auto.
  - (* Else/Else *)
    rewrite <- H10, <- H9; exists C4, s, s; split;
    [apply C_Else | split; [apply C_Else | intro; auto]];
    rewrite Nat.eqb_neq in H3, H4; auto.
+ (* Com *)
  left; clear IHPrecongr_step.
  induction eta; inversion H0; inversion H2; split; try rewrite <- H4, <- H6; auto.
  transitivity s; auto.
+ left; clear IHPrecongr_step.
  inversion H0; inversion H2; revert H4 H5.
  case_eq (s p =? s q); intros; inversion H4; inversion H5; split; try (transitivity s; auto);
  rewrite <- H7, <- H9; auto.
+ left; clear IHPrecongr_step.
  inversion H0; inversion H2; revert H4 H5.
  case_eq (s p =? s q); intros; inversion H4; inversion H5; split; try (transitivity s; auto);
  rewrite <- H7; rewrite <- H9; auto.
Qed.

End Applications.

(*
Section unneeded.

Lemma Precongr_step_confluent_lemma_1 : forall C, exists C', (C ~<= C' /\ C ~<= C').
intro; exists C; split; apply Refl.
Qed.

Lemma Precongr_step_confluent_lemma_2 : forall C C', C ~<= C' -> exists C'', C ~<= C'' /\ C' ~<= C''.
intros; exists C'; split; auto; apply Refl.
Qed.

Lemma Precongr_step_confluent_lemma_3 : forall C C', C' ~<= C -> exists C'', C ~<= C'' /\ C' ~<= C''.
intros; exists C; split; auto; apply Refl.
Qed.

Lemma Precongr_step_Trans : forall C1 C2 C3, C1 ~< C2 -> C2 ~< C3 -> C1 ~<= C3.
intros; apply Trans with C2; auto.
apply Precongr_step_to; auto.
Qed.

Lemma Precongr_step_confluent : forall C C' C'', C ~< C' -> C ~< C'' ->
  exists C''', C' ~<= C''' /\ C'' ~<= C'''.
induction C; intros.
+ rewrite (End_precongr _ (Precongr_step_to _ _ H)).
  rewrite (End_precongr _ (Precongr_step_to _ _ H0)).
  apply Precongr_step_confluent_lemma_1.
+ inversion H.
  - apply Precongr_step_confluent_lemma_2; eapply Precongr_step_Trans.
    * apply EtaEta; apply independent_sym; auto.
    * rewrite H3; auto.
  - apply Precongr_step_confluent_lemma_2; eapply Precongr_step_Trans.
    * apply CondEta; auto.
    * rewrite H2; auto.
  - inversion H0.
    * apply Precongr_step_confluent_lemma_3; eapply Precongr_step_Trans.
      ++ apply EtaEta; apply independent_sym; auto.
      ++ rewrite H7; apply CtxEta; auto.
    * apply Precongr_step_confluent_lemma_3; eapply Precongr_step_Trans.
      ++ apply CondEta; auto.
      ++ rewrite H6; apply CtxEta; auto.
    * elim (IHC C2 C3); auto; intros C_ HC_; inversion_clear HC_.
      exists (e; C_); split; apply CtxEta'; auto.
+ inversion H.
  - apply Precongr_step_confluent_lemma_2; eapply Precongr_step_Trans.
    * apply EtaCond; auto.
    * rewrite H4; rewrite H5; auto.
  - apply Precongr_step_confluent_lemma_2; eapply Precongr_step_Trans.
    * apply CondCond; apply disjoint_sym; auto.
    * rewrite H4; rewrite H5; auto.
  - inversion H0.
    * apply Precongr_step_confluent_lemma_3; eapply Precongr_step_Trans.
      ++ apply EtaCond; auto.
      ++ rewrite H10; rewrite H11; rewrite H2; auto.
    * apply Precongr_step_confluent_lemma_3; eapply Precongr_step_Trans.
      ++ apply CondCond; apply disjoint_sym; auto.
      ++ rewrite H10; rewrite H11; rewrite H2; auto.
    * clear C0 C'1 p2 q0 C C'0 q p1 H1 H3 H4 H5 H9 H7 H10 H11.
      elim (IHC1 _ _ H6 H12); clear IHC1 H6 H12; intros C_ HC_; inversion_clear HC_.
      exists (If p == p0 Then C_ Else C2); split; apply CtxThen'; auto.
    * clear C0 C'1 p2 q0 C C'0 q p1 H1 H3 H4 H5 H9 H7 H10 H11.
      exists (If p == p0 Then C''0 Else C''1); split; apply Precongr_step_to; [apply CtxElse | apply CtxThen]; auto.
  - inversion H0.
    * apply Precongr_step_confluent_lemma_3; eapply Precongr_step_Trans.
      ++ apply EtaCond; auto.
      ++ rewrite H10; rewrite H11; rewrite H2; auto.
    * apply Precongr_step_confluent_lemma_3; eapply Precongr_step_Trans.
      ++ apply CondCond; apply disjoint_sym; auto.
      ++ rewrite H10; rewrite H11; rewrite H2; auto.
    * clear C0 C'1 p2 q0 C C'0 q p1 H1 H3 H4 H5 H9 H7 H10 H11.
      exists (If p == p0 Then C''1 Else C''0); split; apply Precongr_step_to; [apply CtxThen | apply CtxElse]; auto.
    * clear C0 C'1 p2 q0 C C'0 q p1 H1 H3 H4 H5 H9 H7 H10 H11.
      elim (IHC2 _ _ H6 H12); clear IHC1 H6 H12; intros C_ HC_; inversion_clear HC_.
      exists (If p == p0 Then C1 Else C_); split; apply CtxElse'; auto.
Qed.

(** All expected properties also hold for the transitive closure. *)
Lemma Precongr_Trans : forall C1 C2 C3, Precongr C1 C2 -> Precongr C2 C3 -> Precongr C1 C3.
intros; induction H; auto.
apply Trans with C2; auto.
Qed.

Lemma CtxEta': forall eta C1 C2, Precongr C1 C2 -> Precongr (eta; C1) (eta; C2).
intros.
induction H.
+ apply Refl.
+ apply Trans with (eta; C2); auto.
  apply CtxEta; auto.
Qed.

Lemma CtxThen': forall p q C' C'' C, Precongr C' C'' -> Precongr (If p == q Then C' Else C) (If p == q Then C'' Else C).
intros.
induction H.
+ apply Refl.
+ apply Trans with (If p == q Then C2 Else C); auto.
  apply CtxThen; auto.
Qed.

Lemma CtxElse': forall p q C C' C'', Precongr C' C'' -> Precongr (If p == q Then C Else C') (If p == q Then C Else C'').
intros.
induction H.
+ apply Refl.
+ apply Trans with (If p == q Then C Else C2); auto.
  apply CtxElse; auto.
Qed.

Lemma CtxCond': forall p q C1 C2 C3 C4, Precongr C1 C2 -> Precongr C3 C4 -> Precongr (If p == q Then C1 Else C3) (If p == q Then C2 Else C4).
intros.
apply Precongr_Trans with (If p == q Then C1 Else C4); [apply CtxElse' | apply CtxThen']; auto.
Qed.

Lemma Precongr_step_to : forall C C', Precongr_step C C' -> Precongr C C'.
intros; apply Trans with C'; auto; apply Refl.
Qed.

End unneeded.
*)

Section confluence.


Lemma Congruent_Precongr : forall C C', Congruent C C' -> C ~<= C'.
Proof.
intros.
induction H.
+ apply Refl.
+ apply Precongr_Trans with C2; auto.
+ apply Precongr_step_to; apply EtaEta; auto.
+ apply Precongr_step_to; apply EtaCond; auto.
+ apply Precongr_step_to; apply CondEta; auto.
+ apply Precongr_step_to; apply CondCond; auto.
+ apply CtxEta'; auto.
+ apply CtxThen'; auto.
+ apply CtxElse'; auto.
Qed.

Lemma Precongr_Congruent : forall C C', C ~<= C' -> Congruent C C'.
Proof.
intros; induction H.
+ apply CRefl.
+ apply CTrans with C2; auto.
  clear IHPrecongr H0 C3; induction H.
  - apply CEtaEta; auto.
  - apply CEtaCond; auto.
  - apply CCondEta; auto.
  - apply CCondCond; auto.
  - apply CCtxEta; auto.
  - apply CCtxThen; auto.
  - apply CCtxElse; auto.
Qed.

(* When Unfold is introduced, there will be a lemma about head reductions.
   We sketch the structure.

Inductive Precongruent : Choreography -> Choreography -> Prop :=
  PUnfold : ...
  [all Ctx rules]

Inductive HeadPrecongr : Choreography -> Choreography -> Prop :=
  End : Congruent C C
  Step C1 C2 C3 : Precongruent C1 C2 -> HeadPrecongr C2 C3 -> HeadPrecongr C1 C3

Notation "C '~<' C'" := (Precongruent C C') (at level 50).

*)

Definition HeadPrecongr := Congruent.

Notation "C '~<H=' C'" := (HeadPrecongr C C') (at level 50).

Lemma Precongr_HeadCongruent : forall C C', C ~<= C' -> C ~<H= C'.
Proof.
exact Precongr_Congruent.
Qed.

Lemma HeadCongruent_Precongr : forall C C', C ~<H= C' -> C ~<= C'.
Proof.
exact Congruent_Precongr.
Qed.

(*
Lemma Precongruent_confluent
*)

Lemma HeadCongruent_confluent : forall C C' C'', C ~<H= C' -> C ~<H= C'' ->
  exists C''', C' ~<H= C''' /\ C'' ~<H= C'''.
Proof.
intros.
exists C''; split.
+ apply CTrans with C; auto.
  apply Congruent_sym; auto.
+ apply CRefl.
Qed.

Lemma Precongr_confluent : forall C C' C'', C ~<= C' -> C ~<= C'' ->
  exists C''', C' ~<= C''' /\ C'' ~<= C'''.
Proof.
intros.
elim (HeadCongruent_confluent C C' C''); intros; try (apply Precongr_HeadCongruent; auto).
inversion_clear H1; exists x; split; apply HeadCongruent_Precongr; auto.
Qed.

Lemma MCTo_square' : forall C C' s s', (C,s) ---> (C',s') ->
  forall C'', C ~<= C'' -> exists C''', (C'',s) ---> (C''',s') /\ C' ~<= C'''.
Proof.
intros.
exists C'; split.
2: apply Refl.
apply C_Struct with C C'; auto.
2: apply Refl.
apply Congruent_Precongr; apply Congruent_sym.
apply Precongr_Congruent; auto.
Qed.




(*
Section test1 - working.

Hypothesis Precongr_step_confl : forall C C' C'', C ~< C' -> C ~< C'' -> exists C''', C' ~< C''' /\ C'' ~< C'''.

Lemma Precongr_confl_step : forall C C' C'', C ~< C' -> C ~<= C'' -> exists C''', C' ~<= C''' /\ C'' ~<= C'''.
intros.
revert C' H; induction H0; intros.
+ exists C'; split.
  - apply Refl.
  - apply Trans with C'; auto; apply Refl.
+ elim (Precongr_step_confl _ _ _ H H1); intros C4 HC4; inversion_clear HC4.
    elim (IHPrecongr C4); auto; intros.
    rename x into C'''; inversion_clear H4; exists C'''; split; auto.
    apply Trans with C4; auto.
Qed.

Lemma Precongr_confl : forall C C' C'', C ~<= C' -> C ~<= C'' -> exists C''', C' ~<= C''' /\ C'' ~<= C'''.
intros.
revert C' H; induction H0; intros.
+ exists C'; split; auto; apply Refl.
+ elim (Precongr_confl_step C1 C2 C'); auto; intros C4 HC4; inversion_clear HC4.
  elim (IHPrecongr C4); auto; intros C''' Hx; inversion_clear Hx; exists C'''; split; auto.
  apply Precongr_Trans with C4; auto.
Qed.

End test1.
*)

(*
Section test2.

Inductive MCTo_T : Configuration -> Configuration -> Set :=
 | TC_Com p e q C s : MCTo_T ( Com p e q; C, s ) ( C, (update s q (evaluate_on_state e s p)) )
 | TC_Sel p q l C s : MCTo_T ( Sel p q l; C, s ) ( C, s )
 | TC_Then p q C1 C2 s : (s p = s q) -> MCTo_T ( If p == q Then C1 Else C2, s ) ( C1, s )
 | TC_Else p q C1 C2 s : (s p <> s q) -> MCTo_T ( If p == q Then C1 Else C2, s ) ( C2, s )
 | TC_Struct C1 C1' C2 C2' s1 s2 : Precongr C1 C1' -> Precongr C2' C2 -> MCTo_T (C1', s1) (C2', s2) -> MCTo_T (C1, s1) (C2, s2)
.

Inductive MCToStar_T : Configuration -> Configuration -> Type :=
 | TToRefl c : MCToStar_T c c
 | TToStep c1 c2 c3 (P1:MCTo_T c1 c2) (P2:MCToStar_T c2 c3) : MCToStar_T c1 c3
.

Lemma MCTo_strongify : forall c c', MCTo_T c c' -> c ---> c'.
intros.
induction H; auto.
+ apply C_Com.
+ apply C_Sel.
+ apply C_Then; auto.
+ apply C_Else; auto.
+ apply C_Struct with C1' C2'; auto.
Qed.

Lemma MCToStar_strongify : forall c c', MCToStar_T c c' -> c --->* c'.
intros.
induction X; auto.
+ apply ToRefl.
+ apply ToStep with c2; auto.
  apply MCTo_strongify; auto.
Qed.

Fixpoint ToDepth {c c'} (H:MCTo_T c c') : nat :=
  match H with
  | TC_Com _ _ _ _ _ => 0
  | TC_Sel _ _ _ _ _ => 0
  | TC_Then _ _ _ _ _ _ => 0
  | TC_Else _ _ _ _ _ _ => 0
  | TC_Struct _ _ _ _ _ _ _ _ H' => 1 + ToDepth H'
end.

Fixpoint ToStarDepth {c c'} (H:MCToStar_T c c') : nat :=
  match H with
  | TToRefl _ => 0
  | TToStep _ _ _ H' H'' => 1 + max (ToDepth H') (ToStarDepth H'')
  end.

Lemma MCTo_inv : forall c c', c ---> c' ->
    (exists p e q C s, c = (p#e-->q; C, s) /\ c' = (C,update s q (evaluate_on_state e s p)))
    \/ (exists p q l C s, c = (Sel p q l; C, s) /\ c' = (C,s))
    \/ (exists p q C1 C2 s, c = (If p == q Then C1 Else C2, s) /\ s p = s q /\ c' = (C1,s))
    \/ (exists p q C1 C2 s, c = (If p == q Then C1 Else C2, s) /\ s p <> s q /\ c' = (C2,s))
    \/ (exists C s C' s' C1 C2, c = (C,s) /\ c' = (C',s') /\ Precongr C C1 /\ Precongr C2 C' /\ (C1,s) ---> (C2,s')).
intros; inversion H; auto.
+ left.
  exists p; exists e; exists q; exists C; exists s; split; auto.
+ right; left.
  exists p; exists q; exists l; exists C; exists s; split; auto.
+ right; right; left.
  exists p; exists q; exists C1; exists C2; exists s; split; auto.
+ right; right; right; left.
  exists p; exists q; exists C1; exists C2; exists s; split; auto.
+ repeat right.
  exists C1; exists s1; exists C2; exists s2; exists C1'; exists C2'; auto.
Qed.

(*
Lemma MCToStar_inv : forall c c', c --->* c' -> c = c' \/ c ---> c' \/ exists c'', c --->* c'' /\ c'' --->* c'.
intros; inversion H; auto.
repeat right; exists c2; auto.
Qed.
*)

End test2.

Notation "c ===> c'" := (MCTo_T c c') (at level 50, left associativity).
Notation "c ===>* c'" := (MCToStar_T c c') (at level 50, left associativity).

Ltac strongify := first [apply MCTo_strongify | apply MCToStar_strongify].
*)

Section confluence.

(** For induction on reductions. *)

Inductive MCTo_weighted : nat -> Configuration -> Configuration  -> Prop :=
  | Base : forall c c' H, c$H -H-> c' -> MCTo_weighted 0 c c'
  | Cons : forall k C1 C1' C2' C2 s1 s2, C1 ~<= C1' -> MCTo_weighted k (C1',s1) (C2',s2) -> C2' ~<= C2 -> MCTo_weighted (S k) (C1,s1) (C2,s2)
.

Lemma MCTo_weighted_to : forall n c c', MCTo_weighted n c c' -> c ---> c'.
Proof.
induction n; intros; inversion H.
+ rewrite <- H1; apply HeadTo_Soundness.
+ apply C_Struct with C1' C2'; auto.
Qed.

Lemma MCTo_to_weighted : forall c c', c ---> c' -> MCTo_weighted 0 c c' \/ MCTo_weighted 1 c c'.
Proof.
intros; induction H.
+ left.
  set (H := eta_not_terminated (p#e-->q) C); apply Base with H; auto.
+ left.
  set (H := eta_not_terminated (Sel p q l) C); apply Base with H; auto.
+ left.
  set (H0 := cond_not_terminated p q C1 C2); apply Base with H0.
  simpl; rewrite <- Nat.eqb_eq in H; rewrite H; auto.
+ left.
  set (H0 := cond_not_terminated p q C1 C2); apply Base with H0.
  simpl; rewrite <- Nat.eqb_neq in H; rewrite H; auto.
+ right.
  elim IHMCTo; clear IHMCTo; intro.
  - apply Cons with C1' C2'; auto.
  - inversion H2.
    apply Cons with C1'0 C2'0; auto.
    * apply Precongr_Trans with C1'; auto.
    * apply Precongr_Trans with C2'; auto.
Qed.

Lemma MCTo_head_precongr' : forall C C1 C2 C1' C2' s s' s'' H1 H2,
  C ~<= C1 -> C ~<= C2 ->
  (C1,s)$H1 -H-> (C1',s') -> (C2,s)$H2 -H-> (C2',s'') ->
  (s' = s'' /\ exists C', C1' ~<= C' /\ C2' ~<= C') \/
  (exists C' s1 s2, (C1',s') ---> (C',s1) /\ (C2',s'') ---> (C',s2) /\ eq_state_ext s1 s2).
intros.
elim (Precongr_to_weighted _ _ H); clear H; intros n1 Hn1.
elim (Precongr_to_weighted _ _ H0); clear H0; intros n2 Hn2.
rename H3 into HC1; rename H4 into HC2.
revert n1 n2 C C1 C2 C1' C2' s s' s'' H1 H2 HC1 HC2 Hn1 Hn2.
double induction n1 n2; intros; inversion Hn1; clear Hn1; inversion Hn2; clear Hn2.
+ left.
  revert H1 HC1 H2 HC2; rewrite <- H3, <- H5; intros.
  pose (HeadTo_wd _ H1 H2) as H'.
  rewrite HC1, HC2 in H'.
  inversion H'; split; auto.
  exists C2'; split; apply Refl.
+ revert H1 HC1; rewrite <- H4; clear C1 H4 H8 C'' H7 C3 n0 H0 C0 H3; intros.
  rename C' into C0; rename C1' into C'.
  pose (not_terminated_precongr' _ _ H1 H5) as HC'; clearbody HC'.
  case_eq (HeadTo (C0,s) HC'); intros C0' s0 HC0.
  elim (H C0 C0 C2 C0' C2' _ _ _ _ _ HC0 HC2); intros; auto.
  - inversion_clear H0.
    rewrite H3 in HC0; clear s0 H3.
    elim H4; intros C1 HX; inversion_clear HX.
    elim (MCTo_head_precongr _ _ _ _ _ _ _ _ _ HC1 H5 HC0); intros.
    * left; inversion_clear H7; split; auto.
      exists C1; split; auto.
      apply Precongr_Trans with C0'; auto.
      inversion_clear H9; [rewrite H7; apply Refl | apply Precongr_step_to; auto].
    * rename H7 into Hs0s1; destroy Hs0s1.
      rename x into CC; rename x0 into s0; rename x1 into s1.
      right.
      elim (MCTo_square' _ _ _ _ H8 _ H0); intros CC' HCC'; destroy HCC'.
      exists CC', s0, s1; split; try split; auto.
      ++ apply C_Struct with C' CC; auto; try apply Refl.
      ++ apply C_Struct with C1 CC'; auto; try apply Refl.
  - rename H0 into H'; destroy H'.
    rename x into CC; rename x0 into s0'; rename x1 into s2'.
    elim (MCTo_head_precongr _ _ _ _ _ _ _ _ _ HC1 H5 HC0); intros.
    * right; exists CC, s0', s2'; split; auto.
      inversion_clear H4.
      rewrite H7; apply C_Struct with C0' CC; auto; try (apply Refl).
      inversion_clear H8; [rewrite H4; apply Refl | apply Precongr_step_to; auto].
    * rename H4 into H''; destroy H''.
      rename x into CC'; rename x0 into s'''; rename x1 into s0''.
      

(*
Lemma MCTo_confluent_head : forall C s H C' s' C'' s'', (C,s)$H -H-> (C',s') ->
  (C,s) ---> (C'',s'') -> C' <> C'' -> exists c, (C',s') ---> c /\ (C'',s'') ---> c.
intros.
elim (MCTo_to_weighted _ _ H1); clear H1; intro.
+ elim H2; inversion H1.
  generalize (HeadTo_wd _ H H3); intro.
  rewrite H0 in H5; rewrite H4 in H5; inversion H5; auto.
+ inversion H1; inversion H9.
  clear H1 H9 H3 c H14 c' H15 s2 H7 C2 H6 s1 H5 C1 H4.
*)

(*
Lemma MCTo_confluent : forall C C' C'' s s' s'', (C,s) ---> (C',s') ->
  (C,s) ---> (C'',s'') -> C' <> C'' -> exists c, (C',s') ---> c /\ (C'',s'') ---> c.
intros.
elim (MCTo_canonical H); intros C1 HC1.
elim HC1; clear HC1; intros HC1 HC1'.
elim (MCTo_canonical H0); intros C2 HC2.
elim HC2; clear HC2; intros HC2 HC2'.
generalize (not_terminated_weird H HC1); intro HC1''.
generalize (not_terminated_weird H HC2); intro HC2''.
generalize (HC1' HC1''); clear HC1'; intro HC1'.
generalize (HC2' HC2''); clear HC2'; intro HC2'.
elim (Precongr_confluent _ _ _ HC1 HC2); intros CC HCC; inversion_clear HCC.
elim (MCTo_square _ _ _ _ _ HC1') with CC; intros; auto.
inversion_clear H4.
elim (MCTo_square _ _ _ _ _ HC2') with CC; intros; auto.
inversion_clear H4.
rename x into C1'; rename x0 into C2'.
*)


End confluence.



(*
Lemma Lemma_1_2 : forall C C' s,
  (forall s', ~MCToStar (C,s) (End,s')) -> forall s', ~MCToStar (C;;C',s) (End,s').
intros; intro.
dependent induction H0.
+ apply (H s').
  elim (fatsemi_End_inv _ _ x); intros.
  rewrite H0; apply ToRefl.
+ induction c2.
  rename a into C''; rename b into s''.

  generalize (IHMCToStar s s C' C
  elim (fatsemi_ToEnd _ _ _ _ P); intros.
  - inversion_clear a; apply (H s).
    rewrite H0; apply ToRefl; auto.
  - inversion_clear b; apply (H s'); apply ToSingle; auto.
+ 
*)
Abort.

(*** Very old stuff

(* Tem de ser: 0 para refl; 1 para base *)

(* NEW VERSION *)

Inductive BP : nat -> Choreography -> Choreography -> Prop :=
 | BRefl C : BP 0 C C
 | BTrans m n C1 C2 C3 : BP m C1 C2 -> BP n C2 C3 -> BP (m+n) C1 C3
 | BEtaEta eta1 eta2 C : independent eta1 eta2 -> BP 1 (eta1; eta2; C) (eta2; eta1; C)
 | BEtaCond eta p q C1 C2 : unused p eta -> unused q eta -> BP 1 (eta; (If p == q Then C1 Else C2)) (If p == q Then (eta; C1) Else (eta; C2))
 | BCondEta eta p q C1 C2 : unused p eta -> unused q eta -> BP 1 (If p == q Then (eta; C1) Else (eta; C2)) (eta; (If p == q Then C1 Else C2))
 | BCondCond p q r s C1 C2 C3 C4 : disjoint p q r s -> BP 1 (If p == q Then (If r == s Then C1 Else C2) Else (If r == s Then C3 Else C4))
                                                               (If r == s Then (If p == q Then C1 Else C3) Else (If p == q Then C2 Else C4))
 | BCtxEta m eta C1 C2 : BP m C1 C2 -> BP (S m) (eta; C1) (eta; C2)
 | BCtxThen m p q C' C'' C : BP m C' C'' -> BP (S m) (If p == q Then C' Else C) (If p == q Then C'' Else C)
 | BCtxElse m p q C C' C'' : BP m C' C'' -> BP (S m) (If p == q Then C Else C') (If p == q Then C Else C'')
.

Lemma BP_precongr : forall n C C', BP n C C' -> C ~<= C'.
intros.
induction H.
+ apply Refl.
+ apply Precongr_Trans with C2; auto.
+ eapply Trans; [apply EtaEta; auto | apply Refl].
+ eapply Trans; [apply EtaCond; auto | apply Refl].
+ eapply Trans; [apply CondEta; auto | apply Refl].
+ eapply Trans; [apply CondCond; auto | apply Refl].
+ eapply Precongr_Trans; [apply CtxEta' | apply Refl]; auto.
+ eapply Precongr_Trans; [apply CtxThen' | apply Refl]; auto.
+ eapply Precongr_Trans; [apply CtxElse' | apply Refl]; auto.
Qed.

Lemma precongr_step : forall C C', C ~< C' -> exists n, BP n C C'.
intros; induction H.
+ exists 0; apply BRefl.
+ exists 1; apply BEtaEta; auto.
+ exists 1; apply BEtaCond; auto.
+ exists 1; apply BCondEta; auto.
+ exists 1; apply BCondCond; auto.
+ inversion_clear IHPrecongr_step.
  exists (S x); apply BCtxEta; auto.
+ inversion_clear IHPrecongr_step.
  exists (S x); apply BCtxThen; auto.
+ inversion_clear IHPrecongr_step.
  exists (S x); apply BCtxElse; auto.
Qed.

Lemma precongr_BP : forall C C', C ~<= C' -> exists n, BP n C C'.
intros.
induction H.
+ exists 0; apply BRefl.
+ clear H0; inversion_clear IHPrecongr; rename x into k.
  elim (precongr_step _ _ H); intros m Hm.
  exists (m+k); apply BTrans with C2; auto.
Qed.

Lemma O_plus_O : forall m n, m + n = 0 -> m = 0.
induction m; auto.
intros.
simpl in H; inversion H.
Qed.

Lemma BP_0 : forall {C C'}, BP 0 C C' -> C = C'.
intros.
dependent induction H; auto.
generalize (O_plus_O _ _ x); intro.
rewrite plus_comm in x; generalize (O_plus_O _ _ x); intro.
transitivity C2; auto.
Qed.

Lemma BP_confl_0_S : forall n C C' C'', BP 0 C C' -> BP n C C'' -> BP n C' C'' .
intros.
rewrite <- (BP_0 H); auto.
Qed.

(*
Lemma BP_confl_0_S : forall n C C' C'', BP 0 C C' -> BP n C C'' ->
  exists C''', BP n C' C''' /\ BP 0 C'' C'''.
intros; revert C'' H0; dependent induction H; intros.
- exists C''; split; auto; apply BRefl.
- generalize (O_plus_O _ _ x); intro.
  rewrite plus_comm in x; generalize (O_plus_O _ _ x); intro.
  rewrite H2 in H; rewrite H3 in H0; clear x.
  elim IHBP1 with C''; auto; intros CC HCC; inversion_clear HCC.
  elim IHBP2 with CC; auto; intros CC' HCC'; inversion_clear HCC'.
  exists CC'; split; auto.
  replace 0 with (0+0); auto; apply BTrans with CC; auto.
Qed.
*)

(* Old attempt.

Lemma BP_confl : forall m n C C' C'', BP m C C' -> BP n C C'' ->
  exists k k' C''', k+k' = m+n /\ BP k C' C''' /\ BP k' C'' C'''.
assert (forall w m n C C' C'', m+n<w -> BP m C C' -> BP n C C'' ->
  exists k k' C''', k+k' = m+n /\ BP k C' C''' /\ BP k' C'' C''').
2: intros; apply H with (S (m+n)) C; auto.
induction w; intros; [idtac | case_eq m; intros].
+ inversion H.
(*
+ rewrite H2 in H0; elim (BP_confl_0_S _ _ _ _ H0 H1); intros CC HCC.
  inversion_clear HCC; exists n, 0, CC; repeat split; auto.
*)
+ exists n, 0, C''; repeat split; auto.
  - rewrite H2 in H0; apply BP_confl_0_S with C; auto.
  - apply BRefl.
+ rewrite H2 in H, H0; clear m H2; rename n0 into m.
  simpl in H; apply lt_S_n in H.
  case_eq n; intros.
  - rewrite H2 in H1; clear n H2 H.
    exists 0, (S m), C'; repeat split; try apply BRefl; auto.
    apply BP_confl_0_S with C; auto.
  - rewrite H2 in H1, H; clear n H2; rename n0 into n.
    revert n C'' H H1; dependent induction H0; intros.
    * (* Trans *)
      rename m0 into p; rename n0 into q.
      generalize (IHBP1 IHw); clear IHBP1; intro IHBP1.
      generalize (IHBP2 IHw); clear IHBP2; intro IHBP2.
      case_eq p; [idtac | case_eq n]; intros.
      ++ rewrite H0 in H0_, x; clear p IHBP1 H0.
         simpl in x; rewrite x in H0_0, IHBP2; clear n x.
         generalize (BP_confl_0_S _ _ _ _ H0_ H1); intro.
         elim IHBP2 with m q C''; auto.
      ++ rewrite H0 in H0_0, x; clear n IHBP2 H0.
         rewrite plus_comm in x; simpl in x; rewrite x in H0_, IHBP1; clear p n0 H2 x.
         elim IHBP1 with m q C''; auto.
         intros k' Hk'; elim Hk'; intros k'' Hk''; elim Hk''; intros CC HCC; inversion_clear HCC.
         inversion_clear H2; clear Hk' Hk''.
         generalize (BP_confl_0_S _ _ _ _ H0_0 H3); intros.
         exists k', k'', CC; repeat split; auto.
      ++ rewrite H0 in H0_0, x, IHBP2; clear n H0; rename n0 into n.
         rewrite H2 in H0_, x, IHBP1; clear p H2; rename n1 into p.
         elim IHBP1 with p q C''; auto.
         2: { apply le_lt_trans with (m + S q); auto.
              apply plus_le_compat_r.
              simpl in x; inversion x; auto with arith.
         }
         intros k' Hk'; elim Hk'; intros k'' Hk''; elim Hk''; intros CC HCC; inversion_clear HCC.
         inversion_clear H2; clear Hk' Hk''.
         case_eq k'; intros. (* MEGA AGH *)
         -- rewrite H2 in H0, H3; clear k' H2.
            generalize (BP_confl_0_S _ _ _ _ H3 H0_0); intros.
            exists 0, (k'' + S n), C3; repeat split; auto.
            2: apply BRefl.
            2: apply BTrans with CC; auto.
            rewrite <- x; simpl; simpl in H0; rewrite H0; simpl.
            rewrite <- plus_assoc; rewrite (plus_comm (S q)); auto with arith.
         -- rewrite H2 in H0, H3; clear k' H2; rename n0 into k'.
            elim IHBP2 with n k' CC; auto.
            2: { apply le_lt_trans with (m + S q); auto.
                 repeat rewrite <- plus_Snm_nSm; rewrite <- x.
                 simpl in H0; inversion H0; simpl.
                 replace (p + S n + q) with (n + (p + S q)).
                 2: ring.
                 rewrite <- H5; auto with arith.
            }
            intros n' Hn'; elim Hn'; intros n'' Hn''; elim Hn''; intros CC' HCC'; inversion_clear HCC'.
            inversion_clear H5; clear Hn' Hn''.
            exists n', (k''+n''), CC'; repeat split; auto.
            2: apply BTrans with CC; auto.
            clear IHBP1 IHBP2 H7 H6 H4 H3 CC CC' H1 H0_0 H0_ C1 C2 C3 C''.
            rewrite <- x; clear x m H.
            rewrite (plus_comm k''); rewrite plus_assoc; rewrite H2.
            rewrite <- plus_assoc; rewrite H0; ring.
    * (* EtaEta *)
      simpl in H0.
      exists (1 + (S n)), 0, C''; repeat split; auto.
      2: apply BRefl.
      eapply BTrans; [apply BEtaEta; auto | auto].
      apply independent_sym; auto.
    * (* EtaCond *)
      simpl in H0.
      exists (1 + (S n)), 0, C''; repeat split; auto.
      2: apply BRefl.
      eapply BTrans; [apply BCondEta; auto | auto].
    * (* CondEta *)
      simpl in H0.
      exists (1 + (S n)), 0, C''; repeat split; auto.
      2: apply BRefl.
      eapply BTrans; [apply BEtaCond; auto | auto].
    * (* CondCond *)
      simpl in H0.
      exists (1 + (S n)), 0, C''; repeat split; auto.
      2: apply BRefl.
      eapply BTrans; [apply BCondCond; auto | auto].
      apply disjoint_sym; auto.
    * (* CtxEta *)
      clear IHBP; revert m C2 H H0; dependent induction H1; intros.
      ++ rename m into m'; rename m0 into m; rename n0 into n'.
         case_eq m'; [idtac | case_eq n']; intros.
         -- rewrite H1 in x, H1_; clear m' H1 IHBP1.
            generalize (BP_0 H1_); intros.
            apply IHBP2 with C1; auto.
         -- rewrite H1 in x, H1_0; clear n' H1 IHBP2.
            rewrite <- (BP_0 H1_0).
            apply IHBP1 with C1; auto.
            rewrite plus_comm in x; auto.
         -- rename n0 into p; rename n1 into q.
            rewrite H1 in H1_0, x, IHBP2; clear n' H1.
            rewrite H2 in H1_, x, IHBP1; clear m' H2.
            elim (IHw (S q) (S m) (eta; C1) C2 (eta; C0)); auto.
            3: apply BCtxEta; auto.
            2: { apply le_lt_trans with (m + S n); auto.
                 rewrite <- x.
                 replace (m + (S q + S p)) with (S q + S p + m); try ring.
                 rewrite <- plus_assoc; apply plus_le_compat_l.
                 simpl; auto with arith.
            }
            intros k' Hk'; elim Hk'; intros k'' Hk''; elim Hk''; intros CC HCC; inversion_clear HCC.
            inversion_clear H2; clear Hk' Hk''.
            (* if k'' = 0 we can't use IHw *)
            case_eq k''; intros.
            2: {
               rewrite H2 in H4, H1; clear k'' H2; rename n0 into k''.
               elim (IHw k' (S p) C2 CC C3); auto.
               2: { apply le_lt_trans with (m + S n); auto.
                    rewrite <- x.
                    replace (m + (S q + S p)) with (q + S m + S p); try ring.
                    rewrite plus_comm in H1; simpl in H1; inversion H1.
                    auto with arith.
               }
               intros p' Hp'; elim Hp'; intros p'' Hp''; elim Hp''; intros CC' HCC'; inversion_clear HCC'.
               inversion_clear H5; clear Hp' Hp''.
               exists (S k'' + p'), p'', CC'; repeat split; auto.
               2: apply BTrans with CC; auto.
               rewrite <- plus_assoc; rewrite H2.
               rewrite plus_assoc; rewrite plus_comm at 1.
               rewrite (plus_comm (S k'')); rewrite H1.
               rewrite <- x; ring.
            }
             (* BUT... *)
            1: {
               rewrite H2 in H1, H4; clear k'' H2.
               replace (k' + 0) with k' in H1; auto with arith.
               rewrite H1 in H3; clear k' H1.

*)
Lemma BP_confl : forall m n C C' C'', BP m C C' -> BP n C C'' ->
  exists k k' C''', k+k' = m+n /\ BP k C' C''' /\ BP k' C'' C'''.
assert (forall w m n C C' C'', m+n<w -> BP m C C' -> BP n C C'' ->
  exists k k' C''', k+k' = m+n /\ BP k C' C''' /\ BP k' C'' C'''
  /\ (k = 0 -> BP n C'' C) /\ (k' = 0 -> BP m C' C)).
2: {
   intros; elim (H (S (m+n)) m n C C' C''); auto; intros k Hk.
   elim Hk; intros k' Hk'; elim Hk'; intros CC HCC.
   clear Hk Hk'; destroy HCC.
   exists k, k', CC; repeat split; auto.
}
induction w; intros; [idtac | case_eq m; intros].
+ inversion H.
(*
+ rewrite H2 in H0; elim (BP_confl_0_S _ _ _ _ H0 H1); intros CC HCC.
  inversion_clear HCC; exists n, 0, CC; repeat split; auto.
*)
+ exists n, 0, C''; repeat split; auto; intros.
  - rewrite H2 in H0; rewrite <- (BP_0 H0); auto.
  - apply BRefl.
  - rewrite H3 in H1; rewrite (BP_0 H1); rewrite H3; apply BRefl.
  - rewrite H2 in H0; rewrite (BP_0 H0); apply BRefl.
+ rewrite H2 in H, H0; clear m H2; rename n0 into m.
  simpl in H; apply lt_S_n in H.
  case_eq n; intros.
  - rewrite H2 in H1; clear n H2 H.
    exists 0, (S m), C'; repeat split; try apply BRefl; auto.
    apply BP_confl_0_S with C; auto.
    * rewrite (BP_0 H1); intros; apply BRefl.
    * intro; inversion H.
  - rewrite H2 in H1, H; clear n H2; rename n0 into n.
    revert n C'' H H1; dependent induction H0; intros.
    5: {

(* ... skipping for now
    * (* Trans *)
      rename m0 into p; rename n0 into q.
      generalize (IHBP1 IHw); clear IHBP1; intro IHBP1.
      generalize (IHBP2 IHw); clear IHBP2; intro IHBP2.
      case_eq p; [idtac | case_eq n]; intros.
      ++ rewrite H0 in H0_, x; clear p IHBP1 H0.
         simpl in x; rewrite x in H0_0, IHBP2; clear n x.
         generalize (BP_confl_0_S _ _ _ _ H0_ H1); intro.
         elim IHBP2 with m q C''; auto.
      ++ rewrite H0 in H0_0, x; clear n IHBP2 H0.
         rewrite plus_comm in x; simpl in x; rewrite x in H0_, IHBP1; clear p n0 H2 x.
         elim IHBP1 with m q C''; auto.
         intros k' Hk'; elim Hk'; intros k'' Hk''; elim Hk''; intros CC HCC; inversion_clear HCC.
         inversion_clear H2; clear Hk' Hk''.
         generalize (BP_confl_0_S _ _ _ _ H0_0 H3); intros.
         exists k', k'', CC; repeat split; auto.
      ++ rewrite H0 in H0_0, x, IHBP2; clear n H0; rename n0 into n.
         rewrite H2 in H0_, x, IHBP1; clear p H2; rename n1 into p.
         elim IHBP1 with p q C''; auto.
         2: { apply le_lt_trans with (m + S q); auto.
              apply plus_le_compat_r.
              simpl in x; inversion x; auto with arith.
         }
         intros k' Hk'; elim Hk'; intros k'' Hk''; elim Hk''; intros CC HCC; inversion_clear HCC.
         inversion_clear H2; clear Hk' Hk''.
         case_eq k'; intros. (* MEGA AGH *)
         -- rewrite H2 in H0, H3; clear k' H2.
            generalize (BP_confl_0_S _ _ _ _ H3 H0_0); intros.
            exists 0, (k'' + S n), C3; repeat split; auto.
            2: apply BRefl.
            2: apply BTrans with CC; auto.
            rewrite <- x; simpl; simpl in H0; rewrite H0; simpl.
            rewrite <- plus_assoc; rewrite (plus_comm (S q)); auto with arith.
         -- rewrite H2 in H0, H3; clear k' H2; rename n0 into k'.
            elim IHBP2 with n k' CC; auto.
            2: { apply le_lt_trans with (m + S q); auto.
                 repeat rewrite <- plus_Snm_nSm; rewrite <- x.
                 simpl in H0; inversion H0; simpl.
                 replace (p + S n + q) with (n + (p + S q)).
                 2: ring.
                 rewrite <- H5; auto with arith.
            }
            intros n' Hn'; elim Hn'; intros n'' Hn''; elim Hn''; intros CC' HCC'; inversion_clear HCC'.
            inversion_clear H5; clear Hn' Hn''.
            exists n', (k''+n''), CC'; repeat split; auto.
            2: apply BTrans with CC; auto.
            clear IHBP1 IHBP2 H7 H6 H4 H3 CC CC' H1 H0_0 H0_ C1 C2 C3 C''.
            rewrite <- x; clear x m H.
            rewrite (plus_comm k''); rewrite plus_assoc; rewrite H2.
            rewrite <- plus_assoc; rewrite H0; ring.
    * (* EtaEta *)
      simpl in H0.
      exists (1 + (S n)), 0, C''; repeat split; auto.
      2: apply BRefl.
      eapply BTrans; [apply BEtaEta; auto | auto].
      apply independent_sym; auto.
    * (* EtaCond *)
      simpl in H0.
      exists (1 + (S n)), 0, C''; repeat split; auto.
      2: apply BRefl.
      eapply BTrans; [apply BCondEta; auto | auto].
    * (* CondEta *)
      simpl in H0.
      exists (1 + (S n)), 0, C''; repeat split; auto.
      2: apply BRefl.
      eapply BTrans; [apply BEtaCond; auto | auto].
    * (* CondCond *)
*)
      simpl in H0.
      exists (1 + (S n)), 0, C''; repeat split; auto.
      ++ eapply BTrans; [apply BCondCond; auto | auto].
         apply disjoint_sym; auto.
      ++ apply BRefl.
      ++ intro; inversion H2.
      ++ intro; apply BCondCond; apply disjoint_sym; auto.
}
5: {
(*
    * (* CtxEta *)
*)
      clear IHBP; revert m C2 H H0; dependent induction H1; intros.
      ++ rename m into m'; rename m0 into m; rename n0 into n'.
         case_eq m'; [idtac | case_eq n']; intros.
         -- rewrite H1 in x, H1_; clear m' H1 IHBP1.
            generalize (BP_0 H1_); intros.
            apply IHBP2; auto.
         -- rewrite H1 in x, H1_0; clear n' H1 IHBP2.
            rewrite <- (BP_0 H1_0).
            apply IHBP1; auto.
            rewrite plus_comm in x; auto.
         -- rename n0 into p; rename n1 into q.
            rewrite H1 in H1_0, x, IHBP2; clear n' H1.
            rewrite H2 in H1_, x, IHBP1; clear m' H2.
            elim (IHw (S q) (S m) (eta; C1) C2 (eta; C0)); auto.
            3: apply BCtxEta; auto.
            2: { apply le_lt_trans with (m + S n); auto.
                 rewrite <- x.
                 replace (m + (S q + S p)) with (S q + S p + m); try ring.
                 rewrite <- plus_assoc; apply plus_le_compat_l.
                 simpl; auto with arith.
            }
            intros k' Hk''; destroy Hk''.
            rename x0 into k''; rename x1 into CC; rename H4 into Hk'.
            (* if k'' = 0 we can't use IHw *)
            case_eq k''; intros.
            2: {
               rewrite H4 in H3, H1, Hk''; clear k'' H4; rename n0 into k''.
               elim (IHw k' (S p) C2 CC C3); auto.
               2: { apply le_lt_trans with (m + S n); auto.
                    rewrite <- x.
                    replace (m + (S q + S p)) with (q + S m + S p); try ring.
                    rewrite plus_comm in H1; simpl in H1; inversion H1.
                    auto with arith.
               }
               intros p' Hp''; destroy Hp''.
               rename x0 into p''; rename x1 into CC'; rename H7 into Hp'.
               exists (S k'' + p'), p'', CC'; repeat split; auto.
               -- rewrite <- plus_assoc; rewrite H4.
                  rewrite plus_assoc; rewrite plus_comm at 1.
                  rewrite (plus_comm (S k'')); rewrite H1.
                  rewrite <- x; ring.
               -- apply BTrans with CC; auto.
               -- simpl; intro; inversion H7.
               -- intro; apply Hk'.
                  clear Hp'' Hp' H6 H5 CC' Hk'' Hk' H3 H2 CC H0 C0 IHBP1 IHBP2.
            }
             (* BUT... *)
            1: {
               rewrite H2 in H1, H4; clear k'' H2.
               replace (k' + 0) with k' in H1; auto with arith.
               rewrite H1 in H3; clear k' H1.





(* OLD VERSION *)
Inductive BP : nat -> Choreography -> Choreography -> Prop :=
 | BRefl C : BP 0 C C
 | BTrans m n C1 C2 C3 : BP m C1 C2 -> BP n C2 C3 -> BP (S (m+n)) C1 C3
 | BEtaEta eta1 eta2 C : independent eta1 eta2 -> BP 0 (eta1; eta2; C) (eta2; eta1; C)
 | BEtaCond eta p q C1 C2 : unused p eta -> unused q eta -> BP 0 (eta; (If p == q Then C1 Else C2)) (If p == q Then (eta; C1) Else (eta; C2))
 | BCondEta eta p q C1 C2 : unused p eta -> unused q eta -> BP 0 (If p == q Then (eta; C1) Else (eta; C2)) (eta; (If p == q Then C1 Else C2))
 | BCondCond p q r s C1 C2 C3 C4 : disjoint p q r s -> BP 0 (If p == q Then (If r == s Then C1 Else C2) Else (If r == s Then C3 Else C4))
                                                               (If r == s Then (If p == q Then C1 Else C3) Else (If p == q Then C2 Else C4))
 | BCtxEta m eta C1 C2 : BP m C1 C2 -> BP (S m) (eta; C1) (eta; C2)
 | BCtxThen m p q C' C'' C : BP m C' C'' -> BP (S m) (If p == q Then C' Else C) (If p == q Then C'' Else C)
 | BCtxElse m p q C C' C'' : BP m C' C'' -> BP (S m) (If p == q Then C Else C') (If p == q Then C Else C'')
.

Lemma BP_precongr : forall n C C', BP n C C' -> C ~<= C'.
intros.
induction H.
+ apply Refl.
+ apply Precongr_Trans with C2; auto.
+ eapply Trans; [apply EtaEta; auto | apply Refl].
+ eapply Trans; [apply EtaCond; auto | apply Refl].
+ eapply Trans; [apply CondEta; auto | apply Refl].
+ eapply Trans; [apply CondCond; auto | apply Refl].
+ eapply Precongr_Trans; [apply CtxEta' | apply Refl]; auto.
+ eapply Precongr_Trans; [apply CtxThen' | apply Refl]; auto.
+ eapply Precongr_Trans; [apply CtxElse' | apply Refl]; auto.
Qed.

Lemma precongr_step : forall C C', C ~< C' -> exists n, BP n C C'.
intros; induction H.
+ exists 0; apply BRefl.
+ exists 0; apply BEtaEta; auto.
+ exists 0; apply BEtaCond; auto.
+ exists 0; apply BCondEta; auto.
+ exists 0; apply BCondCond; auto.
+ inversion_clear IHPrecongr_step.
  exists (S x); apply BCtxEta; auto.
+ inversion_clear IHPrecongr_step.
  exists (S x); apply BCtxThen; auto.
+ inversion_clear IHPrecongr_step.
  exists (S x); apply BCtxElse; auto.
Qed.

Lemma precongr_BP : forall C C', C ~<= C' -> exists n, BP n C C'.
intros.
induction H.
+ exists 0; apply BRefl.
+ clear H0; inversion_clear IHPrecongr; rename x into k.
  elim (precongr_step _ _ H); intros m Hm.
  exists (S (m+k)); apply BTrans with C2; auto.
Qed.

Lemma O_plus_O : forall m n, m + n = 0 -> m = 0.
induction m; auto.
intros.
simpl in H; inversion H.
Qed.

Lemma BP_confl_0_0 : forall C C' C'', BP 0 C C' -> BP 0 C C'' ->
  exists C''', BP 0 C' C''' /\ BP 0 C'' C'''.
intros.
revert C'' H0; dependent induction H; intros.
- exists C''; split; auto; apply BRefl.
(*
- generalize (O_plus_O _ _ x); intro.
  rewrite plus_comm in x; generalize (O_plus_O _ _ x); intro.
  elim IHBP1 with C''; auto; intros CC HCC; inversion_clear HCC.
  elim IHBP2 with CC; auto; intros CC' HCC'; inversion_clear HCC'.
  exists CC'; split; auto.
  replace 0 with (0 + 0); auto.
  apply BTrans with CC; auto.
*)
- dependent induction H0.
  * eexists; split.
    + apply BRefl.
    + apply BEtaEta; auto.
(*
  * exists C3; split; try apply BRefl.
    generalize (O_plus_O _ _ x); intro.
    rewrite plus_comm in x; generalize (O_plus_O _ _ x); intro.
    replace 0 with (0+0); auto; eapply BTrans.
    + apply BEtaEta; apply independent_sym; auto.
    + replace 0 with (n+m); auto; rewrite plus_comm; apply BTrans with C2; auto.
*)
  * eexists; split; apply BRefl.
- dependent induction H1.
  * eexists; split.
    + apply BRefl.
    + apply BEtaCond; auto.
(*
  * exists C3; split; try apply BRefl.
    generalize (O_plus_O _ _ x); intro.
    rewrite plus_comm in x; generalize (O_plus_O _ _ x); intro.
    replace 0 with (0+0); auto; eapply BTrans.
    + apply BCondEta; auto.
    + replace 0 with (n+m); auto; rewrite plus_comm; apply BTrans with C0; auto.
*)
  * eexists; split; apply BRefl.
- dependent induction H1.
  * eexists; split.
    + apply BRefl.
    + apply BCondEta; auto.
(*
  * exists C3; split; try apply BRefl.
    generalize (O_plus_O _ _ x); intro.
    rewrite plus_comm in x; generalize (O_plus_O _ _ x); intro.
    replace 0 with (0+0); auto; eapply BTrans.
    + apply BEtaCond; auto.
    + replace 0 with (n+m); auto; rewrite plus_comm; apply BTrans with C0; auto.
*)
  * eexists; split; apply BRefl.
- dependent induction H0.
  * eexists; split.
    + apply BRefl.
    + apply BCondCond; auto.
(*
  * exists C0; split; try apply BRefl.
    generalize (O_plus_O _ _ x); intro.
    rewrite plus_comm in x; generalize (O_plus_O _ _ x); intro.
    replace 0 with (0+0); auto; eapply BTrans.
    + apply BCondCond; apply disjoint_sym; auto.
    + replace 0 with (n+m); auto; rewrite plus_comm; apply BTrans with C5; auto.
*)
  * eexists; split; apply BRefl.
Qed.

(*
Lemma BP_confl_0_S : forall n C C' C'', BP 0 C C' -> BP (S n) C C'' ->
  exists C''', BP (S n) C' C''' /\ BP 0 C'' C'''.
intros.
revert C' H; dependent induction H0; intros.
- rename n0 into k.
  case_eq m; [idtac | case_eq k]; intros.
  + rewrite H0 in H0_; elim (BP_confl_0_0 _ _ _ H0_ H); auto.
    intros CC HCC; inversion_clear HCC.
    rewrite H0 in x; simpl in x.
    elim IHBP2 with n CC; auto; intros CC' HCC'; inversion_clear HCC'.
    exists CC'; split; auto.
    replace (S n) with (0 + S n); auto; apply BTrans with CC; auto.
  + rewrite H0 in x; rewrite plus_comm in x; simpl in x.
    elim IHBP1 with n C'; auto; intros CC HCC; inversion_clear HCC.
    rewrite H0 in H0_0; elim (BP_confl_0_0 _ _ _ H0_0 H3); auto.
    intros CC' HCC'; inversion_clear HCC'.
    exists CC'; split; auto.
    replace (S n) with (S n + 0); auto; apply BTrans with CC; auto.
  + elim IHBP1 with n1 C'; auto; intros CC HCC; inversion_clear HCC.
    elim IHBP2 with n0 CC; auto; intros CC' HCC'; inversion_clear HCC'.
    exists CC'; split; auto.
    rewrite <- x; apply BTrans with CC; [rewrite H1 | rewrite H0]; auto.
- dependent induction H.
  + exists (eta; C2); split.
    * apply BCtxEta; auto.
    * apply BRefl.
  + generalize (O_plus_O _ _ x); intro.
    rewrite plus_comm in x; generalize (O_plus_O _ _ x); intro.
    clear x; rewrite H2 in H, IHBP1; clear m H2.
    rewrite H3 in H1, IHBP2; clear n0 H3.
    elim (IHBP1 eta C1); auto; intros CC HCC; inversion_clear HCC.

    * dependent induction H.
      ++ apply IHBP2 with C1; auto.
      ++ generalize (O_plus_O _ _ x); intro.
         rewrite plus_comm in x; generalize (O_plus_O _ _ x); intro.
         clear x; rewrite H3 in H, IHBP1; clear m H3.
         rewrite H4 in H0, IHBP2; clear n0 H4.
         case_eq n; intro.
         -- elim (


Lemma BP_confl_S_S : forall m n C C' C'', BP (S m) C C' -> BP (S n) C C'' ->
  exists C''', BP (S n) C' C''' /\ BP (S m) C'' C'''.
*)

Lemma BP_confl : forall m n C C' C'', BP m C C' -> BP n C C'' ->
  exists k k' C''', k+k' = m+n /\ BP k C' C''' /\ BP k' C'' C'''.
assert (forall w m n C C' C'', m+n<w -> BP m C C' -> BP n C C'' ->
  exists k k' C''', k+k' = m+n /\ BP k C' C''' /\ BP k' C'' C''').
2: intros; apply H with (S (m+n)) C; auto.
induction w; intros.
+ inversion H.
(*
+ apply Nat.eq_sym in H.
  generalize (O_plus_O _ _ H); intro.
  rewrite plus_comm in H; generalize (O_plus_O _ _ H); intro.
  rewrite H2 in H0; rewrite H3 in H1.
  elim (BP_confl_0_0 _ _ _ H0 H1); auto.
  intros CC HCC; inversion_clear HCC.
  exists 0; exists 0; exists CC; repeat split; auto.
*)
+ revert n H H1; dependent induction H0; intros.
  - exists n, 0, C''; repeat split; auto.
    apply BRefl.
  - rename n0 into k.
    elim IHBP1 with k; auto.
    2: apply le_lt_trans with (m+n+k); auto with arith.
    intros k1 Hk1; elim Hk1; clear Hk1.
    intros k2 Hk2; elim Hk2; clear Hk2.
    intros CC HCC; inversion_clear HCC; inversion_clear H2.
    elim (IHw k1 n C2 CC C3); auto.
    * intros k' Hk'; elim Hk'; intros k'' Hk''; elim Hk''; intros CC' HCC'; inversion_clear HCC'.
      inversion_clear H5.
      exists k'', (S (k2+k')), CC'; repeat split; auto.
      ++ rewrite plus_comm; simpl.
         rewrite <- plus_assoc; rewrite H2.
         rewrite plus_assoc; rewrite (plus_comm k2).
         rewrite H0; rewrite <- plus_assoc; rewrite (plus_comm k); auto with arith.
      ++ apply BTrans with CC; auto.
    * apply le_lt_trans with ((m+k)+n).
      ++ rewrite <- H0; auto with arith.
      ++ simpl in H; apply lt_S_n in H.
         rewrite <- plus_assoc; rewrite (plus_comm k); rewrite plus_assoc; auto.
  - simpl in H0; simpl.
    dependent induction H1.
    * exists 0, 0; eexists; repeat split; [apply BRefl | apply BEtaEta; auto].
    * apply lt_S_n in H0.
      exists (S (m+n)), 0, C3; repeat split; auto.
      apply BTrans with C2; auto.
      apply BEtaEta.

(*
Lemma Precongr_step_confluent : forall C C' C'', C ~< C' -> C ~< C'' ->
  exists C''', C' ~< C''' /\ C'' ~< C'''.
induction C; intros.
+ rewrite (End_precongr _ (Precongr_step_to _ _ H)).
  rewrite (End_precongr _ (Precongr_step_to _ _ H0)).
  apply Precongr_step_confluent_lemma_1.
+ dependent induction H.
  - apply Precongr_step_confluent_lemma_2; auto.
  - dependent induction H0.
    * apply Precongr_step_confluent_lemma_2.
      apply EtaEta; apply independent_sym; auto.
    * apply Precongr_step_confluent_lemma_1.
    * 


Lemma Precongr_step_confluent : forall C C' C'', C ~< C' -> C ~< C'' ->
  exists C''', C' ~< C''' /\ C'' ~< C'''.
intros.
revert H0; induction H; intro H'.
+ apply Precongr_step_confluent_lemma_2; auto.
+ dependent induction H'.
  * apply Precongr_step_confluent_lemma_2.
    apply EtaEta; apply independent_sym; auto.
  * apply Precongr_step_confluent_lemma_1.
  * dependent induction H'.
    - apply Precongr_step_confluent_lemma_2.
      apply EtaEta; apply independent_sym; auto.
    - eexists; split.
      ++ apply EtaEta; apply independent_sym; auto.
      ++ apply CtxEta; apply EtaEta; apply independent_sym; auto.
    - eexists; split.
      ++ apply EtaEta; apply independent_sym; auto.
      ++ apply CtxEta; apply CondEta; auto.
    - eexists; split.
      ++ do 2 apply CtxEta; apply H'.
      ++ apply EtaEta; auto.
+ dependent induction H'.
  * apply Precongr_step_confluent_lemma_2.
    apply CondEta; auto.
  * apply Precongr_step_confluent_lemma_1.
  * dependent induction H'.
    - apply Precongr_step_confluent_lemma_2.
      apply CondEta; auto.
    - eexists; split.
      ++ apply CondEta; auto.
      ++ apply CtxEta; apply EtaCond; auto.
    - eexists; split.
      ++ apply CondEta; auto.
      ++ apply CtxEta; apply CondCond; apply disjoint_sym; auto.
    - eexists; split.
      ++ apply CtxThen; apply CtxEta; apply H'.
      ++ apply EtaCond; auto.
    - eexists; split.
      ++ apply CtxElse; apply CtxEta; apply H'.
      ++ apply EtaCond; auto.
+ dependent induction H'.
  * apply Precongr_step_confluent_lemma_2.
    apply EtaCond; auto.
  * apply Precongr_step_confluent_lemma_1.
  * dependent induction H'.
    - apply Precongr_step_confluent_lemma_2.
      apply EtaCond; auto.
    - eexists; split.
      ++ apply EtaCond; auto.
      ++ apply CtxThen; apply EtaEta; apply independent_sym; auto.
    - eexists; split.
      ++ apply EtaCond; auto.
      ++ apply CtxThen; apply CondEta; auto.
    - eexists; split.
      ++ apply CtxEta; apply CtxThen; apply H'.
      ++ apply CondEta; auto.
  * dependent induction H'.
    - apply Precongr_step_confluent_lemma_2.
      apply EtaCond; auto.
    - eexists; split.
      ++ apply EtaCond; auto.
      ++ apply CtxElse; apply EtaEta; apply independent_sym; auto.
    - eexists; split.
      ++ apply EtaCond; auto.
      ++ apply CtxElse; apply CondEta; auto.
    - eexists; split.
      ++ apply CtxEta; apply CtxElse; apply H'.
      ++ apply CondEta; auto.
+ dependent induction H'.
  * apply Precongr_step_confluent_lemma_2.
    apply CondCond; apply disjoint_sym; auto.
  * apply Precongr_step_confluent_lemma_1.
  * dependent induction H'.
    - apply Precongr_step_confluent_lemma_2.
      ++ apply CondCond; apply disjoint_sym; auto.
    - eexists; split.
      ++ apply CondCond; apply disjoint_sym; auto.
      ++ apply CtxThen; apply EtaCond; auto.
    - eexists; split.
      ++ apply CondCond; apply disjoint_sym; auto.
      ++ apply CtxThen; apply CondCond; apply disjoint_sym; auto.
    - eexists; split.
      ++ do 2 apply CtxThen; apply H'.
      ++ apply CondCond; auto.
    - eexists; split.
      ++ apply CtxElse; apply CtxThen; apply H'.
      ++ apply CondCond; auto.
  * dependent induction H'.
    - apply Precongr_step_confluent_lemma_2.
      ++ apply CondCond; apply disjoint_sym; auto.
    - eexists; split.
      ++ apply CondCond; apply disjoint_sym; auto.
      ++ apply CtxElse; apply EtaCond; auto.
    - eexists; split.
      ++ apply CondCond; apply disjoint_sym; auto.
      ++ apply CtxElse; apply CondCond; apply disjoint_sym; auto.
    - eexists; split.
      ++ apply CtxThen; apply CtxElse; apply H'.
      ++ apply CondCond; auto.
    - eexists; split.
      ++ do 2 apply CtxElse; apply H'.
      ++ apply CondCond; auto.
+ clear IHPrecongr_step.
  induction C''.
  * inversion H'.
  * clear IHC''; dependent induction H'.
    - apply Precongr_step_confluent_lemma_3.
      apply CtxEta; auto.
    - dependent induction H.
      ++ apply Precongr_step_confluent_lemma_3.
         apply EtaEta; apply independent_sym; auto.
      ++ eexists; split.
         ** apply CtxEta; apply EtaEta; apply independent_sym; auto.
         ** apply EtaEta; apply independent_sym; auto.
      ++ eexists; split.
         ** apply CtxEta; apply CondEta; auto.
         ** apply EtaEta; apply independent_sym; auto.
      ++ eexists; split.
         ** apply EtaEta; auto.
         ** repeat apply CtxEta; auto.
    - 


  revert C2 H; induction H'; intros.
  * apply Precongr_step_confluent_lemma_3.
    apply CtxEta; auto.
  * dependent induction H0.
    - apply Precongr_step_confluent_lemma_2.
      apply EtaEta; auto.
    - eexists; split.
      ++ apply CtxEta; apply EtaEta; apply independent_sym; auto.
      ++ apply EtaEta; apply independent_sym; auto.
    - eexists; split.
      ++ apply CtxEta; apply CondEta; auto.
      ++ apply EtaEta; apply independent_sym; auto.
    - eexists; split.
      ++ apply EtaEta; auto.
      ++ repeat apply CtxEta; auto.
  * dependent induction H1.
    - apply Precongr_step_confluent_lemma_2.
      apply EtaCond; auto.
    - eexists; split.
      ++ apply CtxEta; apply EtaCond; auto.
      ++ apply CondEta; auto.
    - eexists; split.
      ++ apply CtxEta; apply CondCond; apply disjoint_sym; auto.
      ++ apply CondEta; auto.
    - eexists; split.
      ++ apply EtaCond; auto.
      ++ apply CtxThen; apply CtxEta; auto.
    - eexists; split.
      ++ apply EtaCond; auto.
      ++ apply CtxElse; apply CtxEta; auto.
  * revert H0; dependent induction H; intro.
    - apply Precongr_step_confluent_lemma_2.
      apply CtxEta; auto.
    - elim (IHPrecongr_step eta1 (eta2; C)); auto.





+ clear IHPrecongr_step.
  revert C2 H; induction H'; intros.
  * apply Precongr_step_confluent_lemma_3.
    apply CtxEta; auto.
  * dependent induction H0.
    - apply Precongr_step_confluent_lemma_2.
      apply EtaEta; auto.
    - eexists; split.
      ++ apply CtxEta; apply EtaEta; apply independent_sym; auto.
      ++ apply EtaEta; apply independent_sym; auto.
    - eexists; split.
      ++ apply CtxEta; apply CondEta; auto.
      ++ apply EtaEta; apply independent_sym; auto.
    - eexists; split.
      ++ apply EtaEta; auto.
      ++ repeat apply CtxEta; auto.
  * dependent induction H1.
    - apply Precongr_step_confluent_lemma_2.
      apply EtaCond; auto.
    - eexists; split.
      ++ apply CtxEta; apply EtaCond; auto.
      ++ apply CondEta; auto.
    - eexists; split.
      ++ apply CtxEta; apply CondCond; apply disjoint_sym; auto.
      ++ apply CondEta; auto.
    - eexists; split.
      ++ apply EtaCond; auto.
      ++ apply CtxThen; apply CtxEta; auto.
    - eexists; split.
      ++ apply EtaCond; auto.
      ++ apply CtxElse; apply CtxEta; auto.
  * revert H0; dependent induction H; intro.
    - apply Precongr_step_confluent_lemma_2.
      apply CtxEta; auto.
    - elim (IHPrecongr_step eta1 (eta2; C)); auto.
*)

*)