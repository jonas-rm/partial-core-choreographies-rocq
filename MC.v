Require Export Basic.
Require Export Common.

(* Can we get rid of this? *)
Require Export Coq.Program.Equality.

Local Open Scope nat_scope.

Section Syntax.

(** Communication actions. *)
Inductive Eta : Type :=
 | Com : Pid -> Expr -> Pid -> Eta
 | Sel : Pid -> Pid -> Label -> Eta
.

Lemma eq_eta_dec : forall (eta eta':Eta), { eta = eta' } + { eta <> eta' }.
Proof.
repeat decide equality.
Qed.

Definition disjoint (p q r s:Pid) :=  p <> r /\ p <> s /\ q <> r /\ q <> s.

Lemma disjoint_sym : forall p q r s, disjoint p q r s -> disjoint r s p q.
Proof.
intros; inversion H; inversion_clear H1; inversion_clear H3; repeat split; auto.
Qed.

Definition independent (eta1 eta2:Eta) : Prop :=
match eta1, eta2 with
 | Com p _ q, Com r _ s => disjoint p q r s
 | Com p _ q, Sel r s _ => disjoint p q r s
 | Sel p q _, Com r _ s => disjoint p q r s
 | Sel p q _, Sel r s _ => disjoint p q r s
end.

Lemma independent_sym : forall eta eta', independent eta eta' -> independent eta' eta.
Proof.
intros; induction eta; induction eta'; inversion H; inversion_clear H1; inversion_clear H3; repeat split; auto.
Qed.

Definition unused (r:Pid) (eta:Eta) : Prop :=
match eta with
 | Com p _ q => p <> r /\ q <> r
 | Sel p q _ => p <> r /\ q <> r
end.

(** Choreographies. *)
Inductive Choreography : Type :=
 | End : Choreography
 | Interaction : Eta -> Choreography -> Choreography
 | Cond : Pid -> Pid -> Choreography -> Choreography -> Choreography
.

Lemma eq_chor_dec : forall (C C':Choreography), { C = C' } + { C <> C' }.
Proof.
repeat decide equality.
Qed.

(** A choreography is well-formed if it does not contain self-communications. *)
Fixpoint WellFormed (C:Choreography) : Prop :=
match C with
| End => True
| Interaction eta C' => match eta with Com p _ q => p <> q /\ WellFormed C'
                          | Sel p q _ => p <> q /\ WellFormed C' end
| Cond p q C1 C2 => p <> q /\ WellFormed C1 /\ WellFormed C2
end.

(** Set of process names in a choreography. *)
Fixpoint pn_eta (e:Eta) : list Pid :=
match e with
| Com p _ q => (cons p (cons q nil))
| Sel p q _ => (cons p (cons q nil))
end
.

Fixpoint pn (C:Choreography) : list Pid :=
match C with
| End => nil
| Interaction eta C' => (set_union_pid (pn_eta eta) (pn C'))
| Cond p q C1 C2 => (set_union_pid (set_union_pid (cons p (cons q nil)) (pn C1)) (pn C2))
end
.

Lemma pn_is_set (C:Choreography) : WellFormed C -> NoDup(pn C).
Proof.
induction C; intros.
(* End *)
apply NoDup_nil.
(* e; C *)
simpl.
apply set_union_nodup.
simpl in H.
induction e; inversion_clear H.
(* Com *)
simpl; repeat apply NoDup_cons; simpl; auto.
intro.
inversion_clear H; auto.
apply NoDup_nil.
(* Sel *)
simpl; repeat apply NoDup_cons; simpl; auto.
intro.
inversion_clear H; auto.
apply NoDup_nil.
induction e; inversion H; auto.
(* Cond *)
inversion H.
inversion_clear H1.
simpl.
repeat apply set_union_nodup; auto.
simpl; repeat apply NoDup_cons; simpl; auto.
intro.
inversion_clear H1; auto.
apply NoDup_nil.
Qed.

End Syntax.

Notation "p # e --> q" := (Com p e q) (at level 50, e at level 9, format "p # e --> q").
Notation "p --> q [ l ]" := (Sel p q l) (at level 50, format "p --> q [ l ]").
Notation "eta ';' C" := (Interaction eta C) (at level 60, right associativity).
Notation "'If' p '==' q 'Then' C1 'Else' C2" := (Cond p q C1 C2) (at level 60).

(* Check (1-->2[left]). *)
(* Check (1#this--> 2). *)

Section Semantics_Definitions.

(** Structural precongruence is defined in two steps. One-step congruence contains exactly one swap;
    then we close under reflexivity and transitivity. *)
Inductive Precongr_step : Choreography -> Choreography -> Prop :=
 | EtaEta eta1 eta2 C : independent eta1 eta2 -> Precongr_step (eta1; eta2; C) (eta2; eta1; C)
 | EtaCond eta p q C1 C2 : unused p eta -> unused q eta -> Precongr_step (eta; (If p == q Then C1 Else C2)) (If p == q Then (eta; C1) Else (eta; C2))
 | CondEta eta p q C1 C2 : unused p eta -> unused q eta -> Precongr_step (If p == q Then (eta; C1) Else (eta; C2)) (eta; (If p == q Then C1 Else C2))
 | CondCond p q r s C1 C2 C3 C4 : disjoint p q r s -> Precongr_step (If p == q Then (If r == s Then C1 Else C2) Else (If r == s Then C3 Else C4))
                                                               (If r == s Then (If p == q Then C1 Else C3) Else (If p == q Then C2 Else C4))
 | CtxEta eta C1 C2 : Precongr_step C1 C2 -> Precongr_step (eta; C1) (eta; C2)
 | CtxThen p q C' C'' C : Precongr_step C' C'' -> Precongr_step (If p == q Then C' Else C) (If p == q Then C'' Else C)
 | CtxElse p q C C' C'' : Precongr_step C' C'' -> Precongr_step (If p == q Then C Else C') (If p == q Then C Else C'')
.

Inductive Precongr : Choreography -> Choreography -> Prop :=
 | Refl C : Precongr C C
 | Trans C1 C2 C3: Precongr_step C1 C2 -> Precongr C2 C3 -> Precongr C1 C3
.

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

Example sanity_check : Precongr ( Com 0 this 1; If 2 == 3 Then (Com 4 succ_this 3; End) Else (Com 3 zero 2; End) )
                                ( If 2 == 3 Then (Com 0 this 1; Com 4 succ_this 3; End) Else (Com 3 zero 2; Com 0 this 1; End) ).
Proof.
 eapply Trans.
 apply EtaCond; split; auto.
 apply CtxCond'.
 apply Refl.
 apply Precongr_step_to; apply EtaEta.
 split; auto.
Qed.

Definition Configuration : Type := Choreography * State.

Definition WellFormedConf (conf:Configuration) : Prop := WellFormed( fst conf ).

(** One-step and multi-step reduction. Multi-step reduction is simply a reflexive and transitive closure. *)
Inductive MCTo : Configuration -> Configuration -> Prop :=
 | C_Com p e q C s : MCTo ( Com p e q; C, s ) ( C, (update s q (evaluate_on_state e s p)) )
 | C_Sel p q l C s : MCTo ( Sel p q l; C, s ) ( C, s )
 | C_Then p q C1 C2 s : (s p = s q) -> MCTo ( If p == q Then C1 Else C2, s ) ( C1, s )
 | C_Else p q C1 C2 s : (s p <> s q) -> MCTo ( If p == q Then C1 Else C2, s ) ( C2, s )
 | C_Struct C1 C1' C2 C2' s1 s2 : Precongr C1 C1' -> Precongr C2' C2 -> MCTo (C1', s1) (C2', s2) -> MCTo (C1, s1) (C2, s2)
.

(*
Inductive MCToStar : Configuration -> Configuration -> Prop :=
 | ToRefl c : MCToStar c c
 | ToSingle c1 c2 (P:MCTo c1 c2) : MCToStar c1 c2
 | ToTran c1 c2 c3 (P1:MCToStar c1 c2) (P2:MCToStar c2 c3) : MCToStar c1 c3
.

Definition MCToStar : Configuration -> Configuration -> Prop := clos_refl_trans_1n _ MCTo.
*)

(** We'd love to use the library definitions, but they just don't work -- and give horrible names. *)
Inductive MCToStar : Configuration -> Configuration -> Prop :=
 | ToRefl c : MCToStar c c
 | ToStep c1 c2 c3 : MCTo c1 c2 -> MCToStar c2 c3 -> MCToStar c1 c3
.

Lemma MCToStar_trans : forall c1 c2 c3, MCToStar c1 c2 -> MCToStar c2 c3 -> MCToStar c1 c3.
intros; induction H; auto.
apply ToStep with c2; auto.
Qed.

Definition terminated (C:Choreography) : Prop := Precongr C End.

End Semantics_Definitions.

Notation "c ---> c'" := (MCTo c c') (at level 50, left associativity).
Notation "c --->* c'" := (MCToStar c c') (at level 50, left associativity).

Notation "C1 ~<= C2" := (Precongr C1 C2) (at level 50, left associativity).
Notation "C1 ~< C2" := (Precongr_step C1 C2) (at level 50, left associativity).

(* Notation "C1 \u22e0 C2" := (not (C1 \u227c C2)) (at level 50). *)

Section Semantics_Props.

(** * Induction principles for one-step reduction in MC. *)
Lemma MCTo_induction : forall (P:Choreography -> State -> Choreography -> State -> Prop),
  (forall p e q C s, P (p#e --> q; C) s C (update s q (evaluate_on_state e s p))) ->
  (forall p q l C s, P (Sel p q l; C) s C s) ->
  (forall p q C1 C2 s, s p = s q -> P (If p == q Then C1 Else C2) s C1 s) ->
  (forall p q C1 C2 s, s p <> s q -> P (If p == q Then C1 Else C2) s C2 s) ->
  (forall C1 C1' C2 C2' s1 s2, Precongr C1 C1' -> Precongr C2' C2 -> P C1' s1 C2' s2 -> P C1 s1 C2 s2) ->
  forall C s C' s', (C,s) ---> (C',s') -> P C s C' s'.
Proof.
intros.
dependent induction H4; auto.
apply H3 with C1' C2'; auto.
Qed.

(** * Properties of precongruence. *)
Lemma End_precongr' : forall C C', C' ~<= C -> C' = End -> C = End.
Proof.
intros.
induction H; auto.
apply IHPrecongr; clear C3 H1 IHPrecongr.
induction H; auto; try inversion H0.
Qed.

Lemma End_precongr : forall C, End ~<= C -> C = End.
Proof.
intros; apply End_precongr' with End; auto.
Qed.

Lemma not_End_precongr : forall (C C':Choreography), C <> End -> C' = End -> ~ C ~<= C'.
Proof.
intros; intro.
induction H1; auto.
apply IHPrecongr; auto; intro; clear IHPrecongr H2 C3 H0.
induction H1; auto; try inversion H3.
Qed.

Lemma not_End_precongr' : forall C:Choreography, C ~<= End -> C = End.
Proof.
intros.
elim (eq_chor_dec C End); auto.
intro.
elim not_End_precongr with C End; auto.
Qed.

Lemma precongr_eta' : forall eta C C', C' = (eta; End) -> C' ~<= C -> C = eta; End.
intros.
induction H0; auto.
apply IHPrecongr; clear IHPrecongr H1 C3.
induction H0; auto; try inversion H.
rewrite H3 in H0; rewrite (End_precongr _ (Precongr_step_to _ _ H0)); auto.
Qed.

Lemma precongr_eta : forall eta C, (eta; End) ~<= C -> C = eta; End.
Proof.
intros.
apply precongr_eta' with (eta;End); auto.
Qed.

(** More on termination. *)
Lemma terminated_iff_End : forall C:Choreography, terminated C <-> C = End.
Proof.
unfold terminated; simpl.
split.
apply not_End_precongr'.
intro; rewrite H.
constructor.
Qed.

Lemma eta_not_terminated : forall eta C, ~terminated (eta; C).
Proof.
intros; intro.
red in H; simpl in H.
generalize (not_End_precongr' _ H); intro.
inversion H0.
Qed.

Lemma cond_not_terminated : forall p q C1 C2, ~terminated (If p == q Then C1 Else C2).
Proof.
intros; intro.
red in H; simpl in H.
generalize (not_End_precongr' _ H); intro.
inversion H0.
Qed.

Lemma not_terminated_precongr' : forall C C', ~terminated C -> C ~< C' -> ~terminated C'.
Proof.
intros.
induction H0; try apply eta_not_terminated; try apply cond_not_terminated.
Qed.

Lemma not_terminated_precongr : forall C C', ~terminated C -> C ~<= C' -> ~terminated C'.
Proof.
intros.
induction H0; auto.
apply IHPrecongr; apply not_terminated_precongr' with C1; auto.
Qed.

Lemma terminated_does_not_reduce : forall C C' s s', terminated C -> ~(C,s) ---> (C',s').
Proof.
intros; intro.
rewrite (not_End_precongr' _ H) in H0; clear H.
dependent induction H0.
assert (C1' = End).
+ clear H1 IHMCTo C2' C' H0 s s'.
  dependent induction H; auto.
  apply IHPrecongr; inversion H.
+ rewrite H2 in IHMCTo, H1; clear H C1' H2.
  apply IHMCTo with C2' s s'; auto.
Qed.

Lemma not_terminated_weird : forall {C s C' s' C''}, (C,s) ---> (C',s') -> C ~<= C'' -> ~terminated C''.
Proof.
intros; intro.
red in H1; simpl in H1; rewrite (not_End_precongr' _ H1) in H0.
rewrite (not_End_precongr' _ H0) in H.
revert H; apply terminated_does_not_reduce; apply Refl.
Qed.

(** The size of a choreography, as the minimal number of reductions until we reach a terminal. *)
Fixpoint size (C:Choreography) : nat :=
  match C with
  | End => 0
  | eta; C' => 1 + size C'
  | If p == q Then C1 Else C2 => 1 + min (size C1) (size C2)
  end.

Lemma precongr_size_ge : forall C C', C ~<= C' -> size C <= size C'.
intros.
induction H; simpl; auto with arith.
+ transitivity (size C2); auto.
  clear IHPrecongr H0; induction H; simpl; auto with arith.
  - set (s1 := size C1); set (s2 := size C2); set (s0 := size C0); set (s4 := size C4).
    repeat apply le_n_S.
    rewrite Nat.min_assoc.
    rewrite <- (Nat.min_assoc s1 s2 s0).
    rewrite (Nat.min_comm s2 s0).
    repeat rewrite Nat.min_assoc; auto.
  - apply le_n_S.
    apply Nat.min_glb.
    * transitivity (size C'); auto; apply Nat.le_min_l.
    * apply Nat.le_min_r.
  - apply le_n_S.
    apply Nat.min_glb.
    * apply Nat.le_min_l.
    * transitivity (size C'); auto; apply Nat.le_min_r.
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
    generalize (not_End_precongr' _ H2); clear H2; intro.
    generalize (precongr_size_ge _ _ H1); intro.
    rewrite H3 in H5; auto.
    - inversion H5; auto.
      elim H4; auto with arith.
    - intro; apply H4.
      rewrite H6 in H5; auto with arith.
Qed.

(** Head reductions (do not use structural precongruence). *)

Definition HeadTo (c:Configuration) : ~ (terminated (fst c)) -> Configuration.
destruct c; destruct c; intros.
elim H; apply terminated_iff_End; auto.
destruct e.
apply (c, update s p0 (evaluate_on_state e s p)).
apply (c, s).
apply (if ((s p) =? (s p0)) then (c1, s) else (c2, s)).
Defined.

Lemma HeadTo_wd : forall c H H', HeadTo c H = HeadTo c H'.
Proof.
induction c.
induction a; intros; auto.
+ elim H; red; simpl; apply Refl.
+ induction e; simpl; auto.
Qed.

Example HeadTo_Com : forall p e q C s HC, 
HeadTo (p # e --> q ; C, s) HC = (C, update s q (evaluate_on_state e s p)).
Proof.
intros.
simpl.
trivial.
Qed.

Example HeadTo_Sel : forall p q l C s HC, 
HeadTo (p --> q [l]; C, s) HC = (C, s).
Proof.
intros.
simpl.
trivial.
Qed.

Lemma HeadTo_Soundness : forall c Hc, c ---> (HeadTo c Hc).
Proof.
destruct c; intros.
induction c.
elim Hc; apply terminated_iff_End; trivial.
induction e.
apply C_Com.
apply C_Sel.
simpl.
case_eq (Nat.eqb (s p) (s p0)); intros.
apply C_Then.
apply beq_nat_true; auto.
apply C_Else.
apply beq_nat_false; auto.
Qed.

(*
Example MCToStar_sanity_check : forall p e q s1 C, exists s2,
  (Com p e q ; Com p zero q ; C, s1) --->* (C, s2) /\  (eq_state_ext s2 (update s1 q 0)).
Proof.
intros.
set (c0 := (Com p e q ; Com p zero q ; C, s)).
pose proof terminated_iff_end as T.
assert (NTc0 : not (terminated c0)).
rewrite T. discriminate.
set (c1 := HeadTo c0 NTc0).
apply ToTran with c1. apply ToSingle. apply HeadTo_Soundness.
assert (NTc1 : not (terminated c1)).
rewrite T. discriminate.
set (c2 := HeadTo c1 NTc1).
set (c3 := (C, update s q 0)).
assert (E : c2 = c3).
unfold c2,c3; repeat simpl.
rewrite update_elim. trivial.
rewrite <- E.
apply ToSingle. apply HeadTo_Soundness.
Qed.
*)
(*
Theorem progress : forall C s, C <> End -> exists C' s', MCTo (C, s) (C', s').
Proof.
intros.
induction C.
elim H; trivial.
destruct e.
repeat eapply ex_intro.
apply C_Com.
repeat eapply ex_intro.
apply C_Sel.
case_eq (Nat.eqb (s p) (s p0)); intros.
repeat eapply ex_intro.
apply C_Then.
apply beq_nat_true; auto.
repeat eapply ex_intro.
apply C_Else.
apply beq_nat_false; auto.
Qed.
*)

Theorem progress : forall C s, ~(terminated C) -> exists c', (C,s) ---> c'.
Proof.
intros.
exists (HeadTo (C,s) H).
apply HeadTo_Soundness.
Qed.

Theorem termination : forall C s, exists c', (C,s) --->* c' /\ terminated (fst c').
Proof.
pose proof terminated_iff_End as T.
induction C; intro s.
(* End *)
* exists (End, s). split. 
  + apply ToRefl.
  + rewrite T. trivial.
(* Eta *)
* set (c0 := (e;C,s)).
  set (NTc0 := eta_not_terminated e C).
  set (c1 := HeadTo c0 NTc0).
  assert (c1 = (HeadTo c0 NTc0)); auto.
  induction c1 as (C1, s1).
  elim (IHC s1); intros c' Hc'.
  inversion_clear c'; exists c'; split; auto.
  inversion_clear Hc'.
  apply ToStep with (C,s1); auto.
  replace C with C1.
  rewrite H.
  apply HeadTo_Soundness.
  unfold c0 in H; induction e; simpl in H; inversion H; auto.
  inversion_clear Hc'. auto.
(* If *)
* rename C1 into CT, C2 into CE.
  set (c0 := (If p == p0 Then CT Else CE, s)).
  set (NTc0 := cond_not_terminated p p0 CT CE).
  set (c1 := HeadTo c0 NTc0).
  assert (c1 = (HeadTo c0 NTc0)); auto.
  induction c1 as (C1, s1).
  case_eq (Nat.eqb (s p) (s p0)); intro G.
  + elim (IHC1 s1); intros c' Hc'.
    inversion_clear c'; exists c'; split; auto.
    inversion_clear Hc'. 
    apply ToStep with (CT,s1); auto.
    replace CT with C1.
    rewrite H.
    apply HeadTo_Soundness.
    unfold c0 in H.
    simpl in H.
    rewrite G in H.
    inversion H. auto.
    inversion_clear Hc'. auto.
  + elim (IHC2 s1); intros c' Hc'.
    inversion_clear c'; exists c'; split; auto.
    inversion_clear Hc'. 
    apply ToStep with (CE,s1); auto.
    replace CE with C1.
    rewrite H.
    apply HeadTo_Soundness.
    unfold c0 in H.
    simpl in H.
    rewrite G in H.
    inversion H. auto.
    inversion_clear Hc'. auto.
Qed.

End Semantics_Props.

Notation "c $ H -H-> c'" := (HeadTo c H = c') (at level 50).

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
  - case_eq (s p =? s p0); intro; rewrite H2 in H3; inversion H3.
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
  - case_eq (s p0 =? s p1); intro; rewrite H3 in H4; inversion H4.
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
  - case_eq (s p0 =? s p1); intro; rewrite H3 in H4; inversion H4.
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
  - case_eq (s p0 =? s p1); intro; rewrite H2 in H3; inversion H3.
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
  - case_eq (s p =? s p0); intro; rewrite H2 in H3; inversion H3.
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
  - case_eq (s p0 =? s p1); intro; rewrite H2 in H3; inversion H3.
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
  - case_eq (s p0 =? s p1); intro; rewrite H2 in H3; inversion H3.
    * exists (If p0 == p1 Then If p == q Then C Else C'' Else C0_2); split; auto.
      apply CtxThen; apply CtxElse; auto.
      intro; simpl; rewrite <- H6; rewrite H2; auto.
    * exists (If p0 == p1 Then C0_1 Else (If p == q Then C Else C'')); split; auto.
      apply CtxElse; apply CtxElse; auto.
      intro; simpl; rewrite <- H6; rewrite H2; auto.
Qed.

Lemma HeadTo_precongr : forall {C C' C'' s s' H}, (C,s)$H -H-> (C',s') -> C' ~<= C'' ->
  exists C''', C ~<= C''' /\ forall H', (C''',s)$H' -H-> (C'',s').
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
    apply Trans with C'; auto.
Qed.

(** Currently this lemma could be stronger, but once unfolding is around things get different. *)
Lemma MCTo_square : forall C C' s s' H, (C,s)$H -H-> (C',s') ->
  forall C'', C ~< C'' -> exists C''', (C'',s) ---> (C''',s') /\ C' ~<= C'''.
Proof.
intros.
revert C' s' H0; induction H1; intros.
+ exists C'; split; try apply Refl; inversion H1; induction eta1.
  - eapply C_Struct.
    * apply Precongr_step_to; apply EtaEta; apply independent_sym; auto.
    * apply Refl.
    * apply C_Com.
  - eapply C_Struct.
    * apply Precongr_step_to; apply EtaEta; apply independent_sym; auto.
    * apply Refl.
    * apply C_Sel.
+ exists C'; inversion H2; induction eta; split; try apply Refl.
  - eapply C_Struct.
    * apply Precongr_step_to; apply CondEta; auto.
    * apply Refl.
    * apply C_Com.
  - eapply C_Struct.
    * apply Precongr_step_to; apply CondEta; auto.
    * apply Refl.
    * apply C_Sel.
+ exists C'; split; try apply Refl; inversion H2; revert H4; case_eq (s p =? s q); intros.
  - eapply C_Struct.
    * apply Precongr_step_to; apply EtaCond; auto.
    * apply Refl.
    * apply C_Then; apply Nat.eqb_eq; auto.
  - eapply C_Struct.
    * apply Precongr_step_to; apply EtaCond; auto.
    * apply Refl.
    * apply C_Else; rewrite <- Nat.eqb_eq; intro.
      rewrite H3 in H5; inversion H5.
+ exists C'; split; try apply Refl; inversion H1; revert H3; case_eq (s p =? s q); intros.
  - eapply C_Struct.
    * apply Precongr_step_to; apply CondCond; apply disjoint_sym; auto.
    * apply Refl.
    * apply C_Then; apply Nat.eqb_eq; auto.
  - eapply C_Struct.
    * apply Precongr_step_to; apply CondCond; apply disjoint_sym; auto.
    * apply Refl.
    * apply C_Else; rewrite <- Nat.eqb_eq; intro.
      rewrite H2 in H4; inversion H4.
+ exists C2; inversion H0; induction eta; inversion H3; split; auto.
  - apply C_Com.
  - rewrite <- H4; apply Precongr_step_to; auto.
  - apply C_Sel.
  - rewrite <- H4; apply Precongr_step_to; auto.
+ inversion H0; revert H3; case_eq (s p =? s q); intros; inversion H3.
  - exists C''; split.
    * apply C_Then; apply Nat.eqb_eq; rewrite <- H6; auto.
    * rewrite <- H5; apply Precongr_step_to; auto.
  - exists C; split.
    * rewrite <- H5; apply C_Else; rewrite <- Nat.eqb_eq; intro.
      rewrite H6 in H2; rewrite H4 in H2; inversion H2.
    * rewrite H5; apply Refl.
+ inversion H0; revert H3; case_eq (s p =? s q); intros; inversion H3.
  - exists C; split.
    * rewrite <- H5; apply C_Then; apply Nat.eqb_eq; rewrite <- H6; auto.
    * rewrite H5; apply Refl.
  - exists C''; split.
    * apply C_Else; rewrite <- Nat.eqb_eq; intro.
      rewrite H6 in H2; rewrite H4 in H2; inversion H2.
    * rewrite <- H5; apply Precongr_step_to; auto.
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

(** Canonical representation for reductions. *)
Lemma MCTo_canonical_weak : forall {C s C' s'}, (C,s) ---> (C',s') -> exists C'' C''', C ~<= C'' /\ C''' ~<= C' /\ forall H, (C'',s)$H -H-> (C''',s').
Proof.
intros.
dependent induction H.
+ exists (p#e-->q;C'); exists C'; repeat split; auto; apply Refl.
+ exists (Sel p q l; C'); exists C'; repeat split; auto; apply Refl.
+ exists (If p == q Then C' Else C2); exists C'; repeat split; try apply Refl.
  intros; simpl; rewrite <- Nat.eqb_eq in H; rewrite H; auto.
+ exists (If p == q Then C1 Else C'); exists C'; repeat split; try apply Refl.
  intros; simpl; rewrite <- Nat.eqb_eq in H.
  rewrite (not_true_is_false _ H); auto.
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