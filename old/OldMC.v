(** *  Weighted Relations *)

Section Weighted_Relations.

(** Many proofs in MC are by induction on the proof of precongruence/reduction.
    However, since these are dependent types, formalizing them directly requires using
    Coq.Program.Equality, which imports axioms.
    In order to do these proofs faithfully, we clone these types with a weight - the
    size of the derivation.

    For precongruence, we also get a canonical representation: any precongruence proof
    can be split into a sequence of unfoldings and garbage collection followed by
    reversible rewritings. *)

Inductive Asym_Precongr : Choreography -> Choreography -> Prop :=
| ARefl C : Asym_Precongr C C
| AUnfold X CX C1 C2 : Unfolded X CX C1 C2 -> Asym_Precongr (Def X == CX In C1) (Def X == CX In C2)
| AGarbage X C : Asym_Precongr (Def X == C In End) End
| ACtxEta eta C1 C2 : Asym_Precongr C1 C2 -> Asym_Precongr (eta; C1) (eta; C2)
| ACtxThen p q C' C'' C : Asym_Precongr C' C'' -> Asym_Precongr (If p == q Then C' Else C) (If p == q Then C'' Else C)
| ACtxElse p q C C' C'' : Asym_Precongr C' C'' -> Asym_Precongr (If p == q Then C Else C') (If p == q Then C Else C'')
| ACtxDef X C1 C1' C2 : Asym_Precongr C1 C1' -> Asym_Precongr (Def X == C1 In C2) (Def X == C1' In C2)
| ACtxRec X C1 C2 C2' : Asym_Precongr C2 C2' -> Asym_Precongr (Def X == C1 In C2) (Def X == C1 In C2')
.

Inductive Congruent : Choreography -> Choreography -> Prop :=
| CRefl C : Congruent C C
| CTrans C1 C2 C3 : Congruent C1 C2 -> Congruent C2 C3 -> Congruent C1 C3
| CEtaEta eta1 eta2 C : independent eta1 eta2 -> Congruent (eta1; eta2; C) (eta2; eta1; C)
| CEtaCond eta p q C1 C2 : unused p eta -> unused q eta -> Congruent (eta; (If p == q Then C1 Else C2)) (If p == q Then (eta; C1) Else (eta; C2))
| CCondEta eta p q C1 C2 : unused p eta -> unused q eta -> Congruent (If p == q Then (eta; C1) Else (eta; C2)) (eta; (If p == q Then C1 Else C2))
| CCondCond p q r s C1 C2 C3 C4 : disjoint p q r s -> Congruent (If p == q Then (If r == s Then C1 Else C2) Else (If r == s Then C3 Else C4))
                                                              (If r == s Then (If p == q Then C1 Else C3) Else (If p == q Then C2 Else C4))
| CCtxEta eta C1 C2 : Congruent C1 C2 -> Congruent (eta; C1) (eta; C2)
| CCtxThen p q C' C'' C : Congruent C' C'' -> Congruent (If p == q Then C' Else C) (If p == q Then C'' Else C)
| CCtxElse p q C C' C'' : Congruent C' C'' -> Congruent (If p == q Then C Else C') (If p == q Then C Else C'')
| CCtxDef X C1 C1' C2 : Congruent C1 C1' -> Congruent (Def X == C1 In C2) (Def X == C1' In C2)
| CCtxRec X C1 C2 C2' : Congruent C2 C2' -> Congruent (Def X == C1 In C2) (Def X == C1 In C2')
.

(** Occasionaly we need even finer control of the derivation size. *)

Inductive Congruent_weighted : nat -> Choreography -> Choreography -> Prop :=
| CWRefl C : Congruent_weighted 0 C C
| CWTrans n k C1 C2 C3 : Congruent_weighted n C1 C2 -> Congruent_weighted k C2 C3 -> Congruent_weighted (S (n+k)) C1 C3
| CWEtaEta eta1 eta2 C : independent eta1 eta2 -> Congruent_weighted 1 (eta1; eta2; C) (eta2; eta1; C)
| CWEtaCond eta p q C1 C2 : unused p eta -> unused q eta -> Congruent_weighted 1 (eta; (If p == q Then C1 Else C2)) (If p == q Then (eta; C1) Else (eta; C2))
| CWCondEta eta p q C1 C2 : unused p eta -> unused q eta -> Congruent_weighted 1 (If p == q Then (eta; C1) Else (eta; C2)) (eta; (If p == q Then C1 Else C2))
| CWCondCond p q r s C1 C2 C3 C4 : disjoint p q r s -> Congruent_weighted 1 (If p == q Then (If r == s Then C1 Else C2) Else (If r == s Then C3 Else C4))
                                                              (If r == s Then (If p == q Then C1 Else C3) Else (If p == q Then C2 Else C4))
| CWCtxEta n eta C1 C2 : Congruent_weighted n C1 C2 -> Congruent_weighted (S n) (eta; C1) (eta; C2)
| CWCtxThen n p q C' C'' C : Congruent_weighted n C' C'' -> Congruent_weighted (S n) (If p == q Then C' Else C) (If p == q Then C'' Else C)
| CWCtxElse n p q C C' C'' : Congruent_weighted n C' C'' -> Congruent_weighted (S n) (If p == q Then C Else C') (If p == q Then C Else C'')
| CWCtxDef n X C1 C1' C2 : Congruent_weighted n C1 C1' -> Congruent_weighted (S n) (Def X == C1 In C2) (Def X == C1' In C2)
| CWCtxRec n X C1 C2 C2' : Congruent_weighted n C2 C2' -> Congruent_weighted (S n) (Def X == C1 In C2) (Def X == C1 In C2')
.

Inductive MC_Precongr_weighted : nat -> Choreography -> Choreography -> Prop :=
  | PBase : forall {C C'}, Congruent C C' -> MC_Precongr_weighted 0 C C'
  | PStep : forall {n C} C' {C''}, Asym_Precongr C C' -> MC_Precongr_weighted n C' C'' -> MC_Precongr_weighted (S n) C C''
.

Inductive MCTo_weighted : nat -> Configuration -> Configuration  -> Prop :=
  | MBase : forall {c c'} H, c$H -H-> c' -> MCTo_weighted 0 c c'
  | MStep : forall {n k m C1} C1' C2' {C2 s1 s2}, MC_Precongr_weighted n C1 C1' -> MCTo_weighted k (C1',s1) (C2',s2) -> MC_Precongr_weighted m C2' C2 -> MCTo_weighted (S (n+k+m)) (C1,s1) (C2,s2)
.

End Weighted_Relations.

(** Pretty-printing. *)

Notation "C '~<a' C'" := (Asym_Precongr C C') (at level 50).
Notation "C $ n '~<n' C'" := (MC_Precongr_weighted n C C') (at level 50).
Notation "C '~<>~' C'" := (Congruent C C') (at level 50).
Notation "C $ n '~<n>~' C'" := (Congruent_weighted n C C') (at level 50).
Notation "c $ n -n-> c'" := (MCTo_weighted n c c') (at level 50).

(** We first show that these relations precisely correspond to the unweighted ones. *)

Section Weighted_Reductions.

(** ** Soundness
       Weighted relations imply non-weighted ones. *)

Lemma MCTo_weighted_to : forall n {c c'}, c$n -n-> c' -> c ---> c'.
Proof.
assert (forall n k, k < n -> forall c c', c$k -n-> c' -> c ---> c').
2: intro; apply H with (S n); auto.
induction n; intros.
+ inversion H.
+ inversion H0.
  - rewrite <- H2; apply HeadTo_Soundness.
  - apply C_Struct with C1' C2'.
    * apply MCP_weighted_to with n0; auto.
    * apply MCP_weighted_to with m; auto.
    * apply IHn with k0; auto.
      rewrite <- H4 in H; red in H.
      apply lt_le_trans with (S (n0+k0+m)); auto with arith.
Qed.

(** ** Completeness
       Non-weighted relations can be made weighted. *)


Lemma MCP_step_to_weighted : forall C C', C ~< C' -> C ~<a C' \/ C ~<>~ C'.
Proof.
intros; induction H; try inversion IHMC_Precongr_step.
+ right; apply CRefl; auto.
+ right; apply CEtaEta; auto.
+ right; apply CEtaCond; auto.
+ right; apply CCondEta; auto.
+ right; apply CCondCond; auto.
+ left; apply AUnfold; auto.
+ left; apply AGarbage; auto.
+ left; apply ACtxEta; auto.
+ right; apply CCtxEta; auto.
+ left; apply ACtxThen; auto.
+ right; apply CCtxThen; auto.
+ left; apply ACtxElse; auto.
+ right; apply CCtxElse; auto.
+ left; apply ACtxDef; auto.
+ right; apply CCtxDef; auto.
+ left; apply ACtxRec; auto.
+ right; apply CCtxRec; auto.
Qed.


(** Every precongruence proof can be made canonical. *)

Lemma MCP_to_weighted : forall {C C'}, C ~<= C' -> exists n, C$n ~<n C'.
Proof.
intros; induction H.
+ exists 0; apply PBase; apply CRefl.
+ elim IHMC_Precongr; intros n Hn; clear IHMC_Precongr.
  elim (MCP_step_to_weighted _ _ H); intros.
  - exists (S n); apply PStep with C2; auto.
  - exists n.
    apply MCP_precongruent_congruent_comm with C2; auto.
    apply Congruent_sym; auto.
Qed.

Lemma Congruent_to_weighted : forall {C C'}, C ~<>~ C' -> exists n, C$n ~<n>~ C'.
Proof.
intros.
induction H;
  try inversion_clear IHCongruent1; try inversion_clear IHCongruent2; try inversion_clear IHCongruent;
  try (eexists; econstructor; eauto; fail).
Qed.

(** For reductions, the corresponding result requires rewriting any reduction
    as structural congruences plus a head reduction. This is tricky because of
    unfolding. *)

Lemma MCP_weighted_Def : forall n C C', C$n ~<n C'
  -> forall X CX, (Def X == CX In C)$n ~<n (Def X == CX In C').
Proof.
induction n; intros; inversion H.
+ apply PBase.
  apply CCtxRec; auto.
+ clear n0 C0 C'' H0 H3 H4.
  apply PStep with (Def X == CX In C'0); auto.
  apply ACtxRec; auto.
Qed.

Lemma MCTo_weighted_Def : forall C C' s s' n, (C,s)$n -n-> (C',s')
  -> forall X CX, (Def X == CX In C,s)$n -n-> (Def X == CX In C',s').
Proof.
intros.
revert C C' s s' H X CX.
assert (forall k, k <= n -> forall C C' s s', MCTo_weighted k (C,s) (C',s')
  -> forall X CX, MCTo_weighted k (Def X == CX In C,s) (Def X == CX In C',s')); auto.
induction n; simpl; intros.
+ inversion H.
  rewrite H1 in H0; inversion H0.
  apply (MBase _ (HeadTo_Def_forward _ _ _ _ _ H3 X CX)).
+ case_eq k; intros.
  - rewrite H1 in H0; inversion H0.
    apply (MBase _ (HeadTo_Def_forward _ _ _ _ _ H3 X CX)).
  - rewrite H1 in H0, H; clear k H1; rename n0 into k'.
    apply le_S_n in H; inversion H0.
    rename n0 into n'.
    clear C1 s1 C2 s2 H2 H3 H4 H5.
    rewrite <- H1 in H; clear k' H0 H1.
    assert (k <= n).
    1: transitivity (n' + k + m); auto with arith.
    generalize (IHn _ H0 _ _ _ _ H7 X CX); clear IHn; intro.
    apply MStep with (Def X == CX In C1') (Def X == CX In C2');
      try apply MCP_weighted_Def; auto.
Qed.

Lemma MCTo_to_weighted : forall {c c'}, c ---> c' -> exists n, MCTo_weighted n c c'.
Proof.
intros; induction H.
+ exists 0; apply MBase with I; auto.
+ exists 0; apply MBase with I; auto.
+ exists 0; apply MBase with I.
  simpl; rewrite <- Vdec.eqb_eq in H.
  unfold Value_dec; rewrite H; auto.
+ exists 0; apply MBase with I.
  simpl; rewrite <- Vdec.eqb_neq in H.
  unfold Value_dec; rewrite H; auto.
+ elim IHMCTo; clear IHMCTo; intros k Hk.
  elim (O_or_S k); intro.
  inversion_clear a.
  - rewrite <- H0 in Hk; clear k H0; inversion Hk.
    clear C0 s1 C3 s2 H1 H2 H3 H4 Hk.
    rename C2'0 into C0.
    exists (S (n+k+m)); apply MStep with (Def X == C1 In C1') (Def X == C1 In C0).
    * apply MCP_weighted_Def; auto.
    * apply MCTo_weighted_Def; auto.
    * apply MCP_weighted_Def; auto.
  - rewrite <- b in Hk; inversion Hk.
    exists 0; apply (MBase _ (HeadTo_Def _ _ _ _ _ H1 _ _ H0)).
+ elim IHMCTo; clear IHMCTo; intros k Hk.
  elim (MCP_to_weighted H); intros n Hn.
  elim (MCP_to_weighted H0); intros m Hm.
  exists (S (n+k+m)).
  apply MStep with C1' C2'; auto.
Qed.

End Weighted_Reductions.

(** * Applications *)

Section Applications.

(** We now can prove some more results by induction on canonical proofs
    of precongruence or reduction. *)

(** Properties of termination. *)

Lemma MCP_step_not_terminated : forall C C', ~terminated C -> C ~< C' -> ~terminated C'.
Proof.
intros; intro.
apply H.
apply MCP_Step with C'; auto.
Qed.

Lemma MCP_not_terminated : forall C C', ~terminated C -> C ~<= C' -> ~terminated C'.
Proof.
intros; intro.
apply H.
apply MCP_Trans with C'; auto.
Qed.

Lemma terminated_base_char : forall C, terminated C
  -> (forall eta C', C <> (eta; C'))
  /\ (forall p q C1 C2, C <> If p == q Then C1 Else C2)
  /\ (forall X, C <> Call X).
Proof.
intros.
red in H.
elim (MCP_to_weighted H); intros n Hn.
clear H.
revert C Hn; induction n; intros; inversion Hn.
- clear C0 C' Hn H1 H2.
  assert (C = End).
  2: rewrite H0; repeat split; intros; discriminate.
  elim (Congruent_to_weighted H); intros n Hn.
  clear H; revert C Hn.
  assert (forall k C, k <= n -> C $ k ~<n>~ End -> C = End).
  2: eauto.
  induction n; intros.
  + inversion H; rewrite H1 in H0; inversion H0; auto.
  + case_eq k; intros; rewrite H1 in H0; inversion H0; auto.
    rewrite H1 in H; apply le_S_n in H; clear k H1.
    rewrite (IHn k0 C2) in H3; auto.
  2: transitivity (n1+k0); auto with arith; rewrite H2; auto.
  apply (IHn n1); auto.
  transitivity (n1+k0); auto with arith; rewrite H2; auto.
- clear C'' H3 C0 H2 n0 H.
  generalize (IHn _ H1); clear IHn; intro IHn; destroy IHn.
  repeat split; intros; try intro.
  + rewrite H3 in H0; inversion H0.
    * contradiction (H eta C'0); auto.
    * contradiction (H eta C2); auto.
  + rewrite H3 in H0; inversion H0.
    * contradiction (H2 p q C1 C2); auto.
    * contradiction (H2 p q C'' C2); auto.
    * contradiction (H2 p q C1 C''); auto.
  + rewrite H3 in H0; inversion H0.
    contradiction (IHn X); auto.
Qed.

Lemma eta_not_terminated : forall eta C, ~terminated (eta; C).
Proof.
intros; intro.
elim (terminated_base_char _ H); intros.
apply (H0 _ _ eq_refl).
Qed.

Lemma Call_not_terminated : forall X, ~terminated (Call X).
Proof.
intros; intro.
elim (terminated_base_char _ H); intros.
inversion_clear H1.
apply (H3 _ eq_refl).
Qed.

Lemma cond_not_terminated : forall p q C1 C2, ~terminated (If p == q Then C1 Else C2).
Proof.
intros; intro.
elim (terminated_base_char _ H); intros.
inversion_clear H1.
apply (H2 _ _ _ _ eq_refl).
Qed.

Lemma terminated_Def : forall X C1 C2, terminated C2 -> terminated (Def X == C1 In C2).
Proof.
intros.
eapply MCP_Trans.
2: apply MCP_step_to; apply Garbage.
apply CtxRec'; auto.
Qed.

(** Reductions preserve well-formedness. *)

Lemma MCTo_wf : forall C, WellFormed C -> forall s C' s',
  (C,s) ---> (C',s') -> WellFormed C'.
Proof.
intros.
elim (MCTo_to_weighted H0); intros n Hn; clear H0.
revert C H s C' s' Hn.
assert (forall k, k <= n -> forall C s C' s', (C,s)$k -n-> (C',s') -> forall l, WellFormed_ctx C l -> WellFormed_ctx C' l); intros.
2: apply H with n C s s'; auto.
revert k H C s C' s' H0 l H1.
induction n; intros; [inversion H | case_eq k; intros]; rewrite H2 in H0; inversion H0.
- clear H0 H2 H6 H7 c c' H.
  revert s C' s' l H1 H3 H4; induction C; intros; inversion H4.
  + inversion H3.
  + inversion H3.
  + induction e; inversion H4; inversion H1; rewrite <- H2; auto.
  + destroy_as H1 H'; revert H0; case_eq (Value_dec (s p) (s p0)); intros; inversion H5; rewrite <- H7; auto.
  + destroy_as H1 H'.
    set (c := HeadTo (C2,s) H3).
    assert ((C2,s)$H3 -H-> c); auto; clearbody c.
    induction c.
    simpl in H5; rewrite H5 in H0.
    change ((C2,s)$H3 -H-> (a,b)) in H5.
    inversion H0; repeat split; auto.
    eapply IHC2; eauto.
- clear H0 H2 H6 H7 c c' H IHn.
  revert s C' s' l H1 H3 H4; induction C; intros; inversion H4.
  + inversion H3.
  + inversion H3.
  + induction e; inversion H4; inversion H1; rewrite <- H2; auto.
  + destroy_as H1 H'; revert H0; case_eq (Value_dec (s p) (s p0)); intros; inversion H5; rewrite <- H7; auto.
  + destroy_as H1 H'.
    set (c := HeadTo (C2,s) H3).
    assert ((C2,s)$H3 -H-> c); auto; clearbody c.
    induction c.
    simpl in H5; rewrite H5 in H0.
    change ((C2,s)$H3 -H-> (a,b)) in H5.
    inversion H0; repeat split; auto.
    eapply IHC2; eauto.
- rewrite H2 in H; apply le_S_n in H; clear H2 k.
  clear s2 C2 s1 C2 H7 H6 H5 H4.
  apply MCP_wf_ctx with C2'.
  2: apply MCP_weighted_to with m; auto.
  apply IHn with k0 C1' s s'; auto.
  1: transitivity n0; auto; rewrite <- H3; auto with arith.
  apply MCP_wf_ctx with C; auto.
  apply MCP_weighted_to with n1; auto.
Qed.

End Applications.

(** * Deadlock-freedom-by-design

  We now prove Theorem 1: every non-terminated choreography can reduce. *)

Section Progress.

(** We start with useful characterizations of being guarded and being a pure call. *)

Lemma guarded_char : forall C, guarded C -> C ~<= End \/ has_head_action C.
Proof.
induction C; intros; auto.
+ left; constructor.
+ inversion_clear H.
  elim IHC2; intros; auto.
  left; apply terminated_Def; auto.
Qed.

Lemma pure_call_char : forall C, ~terminated C -> ~has_head_action C -> pure_call C.
Proof.
induction C; simpl; auto; intros.
+ contradiction H; constructor.
+ apply IHC2; auto.
  intro; contradiction H.
  apply terminated_Def; auto.
Qed.

(** The idea of the proof is: if C is not terminated, then we can always apply
    a reduction rule, eventually by unfolding some procedure definition.
    To take care of this case, we need to be able to unfold a procedure call within the
    context of the choreography (relation Ctx_Unfolded below). *)

(** A specialization of the remove function from the standard library. *)

Fixpoint remove_Def (X:RecVar) (l:list (RecVar*Choreography)) : list (RecVar*Choreography) :=
match l with
| nil => nil
| (Y,CY) :: l' => if RecVar_dec X Y then remove_Def Y l' else (Y,CY) :: remove_Def X l'
end.

Definition add_or_replace (X:RecVar) (CX:Choreography) l := (X,CX) :: remove_Def X l.

Inductive Ctx_Unfolded : list (RecVar*Choreography) -> Choreography -> Choreography -> Prop :=
| Ctx_Unfold X CX l : List.In (X,CX) l -> Ctx_Unfolded l (Call X) CX
| Ctx_Eta eta C C' l : Ctx_Unfolded l C C' -> Ctx_Unfolded l (eta;C) (eta;C')
| Ctx_Then p q C C' CE l : Ctx_Unfolded l C C' -> Ctx_Unfolded l (If p == q Then C Else CE) (If p == q Then C' Else CE)
| Ctx_Else p q CT C C' l : Ctx_Unfolded l C C' -> Ctx_Unfolded l (If p == q Then CT Else C) (If p == q Then CT Else C')
| Ctx_Rec X CX C C' l : Ctx_Unfolded (add_or_replace X CX l) C C' -> Ctx_Unfolded l (Def X == CX In C) (Def X == CX In C')
.

(** Membership characterizations for these list functions. *)

Lemma remove_Def_not_in : forall X CX l, ~List.In (X,CX) (remove_Def X l).
Proof.
induction l; simpl; auto.
induction a.
case_eq (RecVar_dec X a); intros; intro; contradiction IHl.
- rewrite Rdec.eqb_eq in H; rewrite <- H in H0; auto.
- inversion_clear H0; auto.
  revert H; inversion H1; rewrite Rdec.eqb_refl.
  intro; inversion H.
Qed.

Lemma remove_Def_in : forall X Y CY l, X <> Y -> List.In (Y,CY) l -> List.In (Y,CY) (remove_Def X l).
Proof.
induction l; simpl; auto; intros.
induction a.
case_eq (RecVar_dec X a); intros.
- rewrite Rdec.eqb_eq in H1.
  rewrite <- H1; apply IHl; auto.
  inversion_clear H0; auto.
  contradiction H; inversion H2.
  transitivity a; auto.
- simpl; inversion_clear H0; auto.
Qed.

Lemma in_remove_Def : forall X Y CY l, List.In (Y,CY) (remove_Def X l) -> List.In (Y,CY) l.
Proof.
induction l; simpl; auto.
induction a.
case_eq (RecVar_dec X a); intros.
- right; apply IHl.
  rewrite Rdec.eqb_eq in H; rewrite <- H in H0; auto.
- inversion_clear H0; auto.
Qed.

Lemma remove_Def_neq : forall X Y CY l, List.In (Y,CY) (remove_Def X l) -> X <> Y.
Proof.
induction l; simpl; auto.
induction a.
case_eq (RecVar_dec X a); intros.
- apply IHl.
  rewrite Rdec.eqb_eq in H; rewrite <- H in H0; auto.
- inversion_clear H0; auto.
  rewrite Rdec.eqb_neq in H; revert H; inversion H1; auto.
Qed.

Lemma in_add_or_replace : forall l X CX Y CY,
  List.In (X,CX) (add_or_replace Y CY l) <-> (X = Y /\ CX = CY) \/ (X <> Y /\ List.In (X,CX) l).
Proof.
simpl; split; intros; inversion_clear H.
- inversion H0; auto.
- right; split.
  + intro; symmetry in H; revert H.
    eapply remove_Def_neq; eauto.
  + eapply in_remove_Def; eauto.
- inversion H0.
  rewrite H; rewrite H1; auto.
- inversion_clear H0; right; apply remove_Def_in; auto.
Qed.

(** Unlike regular unfolding, contextual unfolding is guaranteed to return something
    precongruent to the original choreography. *)

Lemma MCP_Ctx_Unfolded_asym : forall C C', Ctx_Unfolded nil C C' -> C ~<a C'.
Proof.
assert (forall C C' l, Ctx_Unfolded l C C' ->
  C ~<a C' \/ exists X CX, List.In (X,CX) l /\ Unfolded X CX C C').
2: { intros.
     elim (H C C' nil); intros; auto.
     destroy_as H1 H'; inversion H2.
   }
induction C; intros; inversion H.
+ right.
  exists r, C'; split; auto; constructor.
+ clear l0 eta C0 H1 H0 H3; rename C'0 into C0.
  elim (IHC _ _ H4); intros.
  - left; constructor; auto.
  - right; destroy_as H0 H'.
    exists x, x0; split; try constructor; auto.
+ clear l0 p1 q C CE H1 H0 H3 H4 H5.
  elim (IHC1 _ _ H6); intros.
  - left; constructor; auto.
  - right; destroy_as H0 H'.
    exists x, x0; split; try constructor; auto.
+ clear l0 p1 q C CT H1 H0 H3 H4 H5.
  elim (IHC2 _ _ H6); intros.
  - left; constructor; auto.
  - right; destroy_as H0 H'.
    exists x, x0; split; try constructor; auto.
+ clear l0 X CX C H1 H0 H3 H4.
  elim (IHC2 _ _ H5); intros.
  - left; apply ACtxRec; auto.
  - destroy_as H0 H'.
    elim (in_add_or_replace l x x0 r C1); intros.
    clear H4; elim H3; auto; clear H3 H1; intros.
    * left; constructor.
      inversion_clear H1.
      rewrite <- H3, <- H4; auto.
    * right; inversion_clear H1; exists x, x0; split; try constructor; auto.
Qed.

Lemma MCP_Ctx_Unfolded : forall C C', Ctx_Unfolded nil C C' -> C ~<= C'.
Proof.
intros.
apply MCP_weighted_to with 1.
apply PStep with C'; repeat constructor.
apply MCP_Ctx_Unfolded_asym; auto.
Qed.

(** Furthermore, it is not a pure function call. *)

Lemma Ctx_Unfolded_guarded : forall C C' l,
  (forall X CX, List.In (X,CX) l -> guarded CX) ->
  Ctx_Unfolded l C C' -> WellFormed_ctx C (map fst l) -> guarded C'.
Proof.
induction C; intros; inversion H0; simpl; eauto.
clear C H6 CX H5 X H2 l0 H3.
rename C'0 into C0.
destroy_as H1 H'; split; auto.
apply IHC2 with (add_or_replace r C1 l); auto.
+ intros.
  inversion_clear H5.
  - inversion H6.
    rewrite <- H9; auto.
  - apply H with X.
    apply in_remove_Def with r; auto.
+ apply WellFormed_ctx_mon with (r:: map fst l); auto.
  simpl; intros.
  inversion_clear H5; auto.
  rewrite in_map_iff in H6.
  destroy H6; induction x.
  elim (R.eq_dec r X); auto.
  right; replace X with (fst (a,b)).
  apply in_map; apply remove_Def_in; auto.
  simpl in H5; rewrite H5; auto.
Qed.

Lemma Ctx_Unfolded_has_head : forall C C',
  Ctx_Unfolded nil C C' -> WellFormed C -> ~terminated C -> has_head_action C'.
Proof.
intros.
generalize (MCP_Ctx_Unfolded _ _ H); intro.
assert (forall (X:RecVar) CX, List.In (X,CX) nil -> guarded CX).
1: intros; inversion H3.
generalize (Ctx_Unfolded_guarded _ _ _ H3 H H0); intro.
assert (~terminated C').
1: intro; apply H1; apply MCP_Trans with C'; auto.
induction C'; auto.
1: inversion H; inversion H6.
inversion H.
1: inversion H6.
clear H11 C'; rename C'2 into C'.
rewrite H10 in H8; clear H10 CX; rename C'1 into CX.
rewrite H6 in H8; clear H6 X; rename r into X.
clear H7 l.
unfold add_or_replace in H9; simpl in H9.
inversion_clear H4.
elim (guarded_char _ H7); intros; auto.
contradiction H5.
apply terminated_Def; auto.
Qed.

Lemma pure_call_Ctx_Unfolded : forall C, pure_call C -> WellFormed C ->
  exists C', Ctx_Unfolded nil C C'.
Proof.
assert (forall C l, pure_call C -> WellFormed_ctx C (map fst l) -> exists C', Ctx_Unfolded l C C'); auto.
induction C; simpl; intros; try inversion H.
+ rewrite in_map_iff in H0; destroy_as H0 H'.
  induction x.
  exists b; constructor.
  simpl in H1; rewrite <- H1; auto.
+ destroy_as H0 H'.
  elim IHC2 with (add_or_replace r C1 l); auto.
  - intros; exists (Def r == C1 In x); constructor; auto.
  - apply WellFormed_ctx_mon with (r :: map fst l); auto.
    clear H0 H2 H1 H IHC1 IHC2 C2.
    simpl; intros.
    inversion_clear H; auto.
    elim (R.eq_dec r X); auto.
    rewrite in_map_iff in H0; destroy H0.
    induction x.
    rewrite <- H; right.
    apply in_map; apply remove_Def_in; auto.
Qed.

(** Now we can prove that any non-terminated choreography is precongruent
    to a choreography with head action, which has a head reduction. *)

Lemma not_terminated_has_head_action : forall C, ~terminated C ->
  WellFormed C -> exists C', has_head_action C' /\ C ~<= C'.
Proof.
intros.
elim (has_head_action_dec C); intro.
+ exists C; split; auto; constructor.
+ elim (pure_call_Ctx_Unfolded C); auto.
  2: apply pure_call_char; auto.
  intro C'; intros.
  exists C'; split; auto.
  - apply Ctx_Unfolded_has_head with C; auto.
  - apply MCP_Ctx_Unfolded; auto.
Qed.

Theorem progress : forall C s, ~(terminated C) -> WellFormed C -> exists c', (C,s) ---> c'.
Proof.
intros.
elim (not_terminated_has_head_action C); auto.
intros C' HC'; destroy HC'.
set (c := HeadTo (C',s) H1).
assert (c = HeadTo (C',s) H1); auto; clearbody c.
exists c; induction c.
rename a into C''; rename b into s'.
apply C_Struct with C' C''; auto.
+ constructor.
+ rewrite H2; apply HeadTo_Soundness.
Qed.

End Progress.

End MCBase.
