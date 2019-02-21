Require Export Basic.
Require Export Common.
Local Open Scope nat_scope.

Section Syntax.
Inductive Eta : Type :=
 | Com : Pid -> Expr -> Pid -> Eta
 | Sel : Pid -> Pid -> Label -> Eta
.

Lemma eq_eta_dec : forall (eta eta':Eta), { eta = eta' } + { eta <> eta' }.
Proof.
repeat decide equality.
Qed.

Definition disjoint (p q r s:Pid) :=  p <> r /\ p <> s /\ q <> r /\ q <> s.

Definition independent (eta1 eta2:Eta) : Prop :=
match eta1, eta2 with
 | Com p _ q, Com r _ s => disjoint p q r s
 | Com p _ q, Sel r s _ => disjoint p q r s
 | Sel p q _, Com r _ s => disjoint p q r s
 | Sel p q _, Sel r s _ => disjoint p q r s
end.

Definition unused (r:Pid) (eta:Eta) : Prop :=
match eta with
 | Com p _ q => p <> r /\ q <> r
 | Sel p q _ => p <> r /\ q <> r
end.

Inductive Choreography : Type :=
 | End : Choreography
 | Interaction : Eta -> Choreography -> Choreography
 | Cond : Pid -> Pid -> Choreography -> Choreography -> Choreography
.

Lemma eq_chor_dec : forall (C C':Choreography), { C = C' } + { C <> C' }.
Proof.
repeat decide equality.
Qed.

Fixpoint WellFormed (C:Choreography) : Prop :=
match C with
| End => True
| Interaction eta C' => match eta with Com p _ q => p <> q /\ WellFormed C'
                          | Sel p q _ => p <> q /\ WellFormed C' end
| Cond p q C1 C2 => p <> q /\ WellFormed C1 /\ WellFormed C2
end.

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

Section Semantics.

Inductive Precongr : Choreography -> Choreography -> Prop :=
 | Refl C : Precongr C C
 | Trans C1 C2 C3 (P1:Precongr C1 C2) (P2:Precongr C2 C3) : Precongr C1 C3
 | EtaEta eta1 eta2 C : independent eta1 eta2 -> Precongr (eta1; eta2; C) (eta2; eta1; C)
 | EtaCond eta p q C1 C2 : unused p eta -> unused q eta -> Precongr (eta; (If p == q Then C1 Else C2)) (If p == q Then (eta; C1) Else (eta; C2))
 | CondEta eta p q C1 C2 : unused p eta -> unused q eta -> Precongr (If p == q Then (eta; C1) Else (eta; C2)) (eta; (If p == q Then C1 Else C2))
 | CondCond p q r s C1 C2 C3 C4 : disjoint p q r s -> Precongr (If p == q Then (If r == s Then C1 Else C2) Else (If r == s Then C3 Else C4))
                                                               (If r == s Then (If p == q Then C1 Else C3) Else (If p == q Then C2 Else C4))
 | CtxEta eta C1 C2 : Precongr C1 C2 -> Precongr (eta; C1) (eta; C2)
 | CtxCond p q C1 C2 C3 C4 : Precongr C1 C2 -> Precongr C3 C4 -> Precongr (If p == q Then C1 Else C3) (If p == q Then C2 Else C4)
.

Notation "C1 \u227c C2" := (Precongr C1 C2) (at level 50, left associativity).
Notation "C1 \u22e0 C2" := (not (C1 \u227c C2)) (at level 50).

Example sanity_check : Precongr ( Com 0 this 1; If 2 == 3 Then (Com 4 succ_this 3; End) Else (Com 3 zero 2; End) )
                                ( If 2 == 3 Then (Com 0 this 1; Com 4 succ_this 3; End) Else (Com 3 zero 2; Com 0 this 1; End) ).
Proof.
 eapply Trans.
 apply EtaCond; split; auto.
 apply CtxCond.
 apply Refl.
 apply EtaEta.
 split; auto.
Qed.

Definition Configuration : Type := Choreography * Store.

Definition WellFormedConf (conf:Configuration) : Prop := WellFormed( fst conf ).

Inductive MCTo : Configuration -> Configuration -> Prop :=
 | C_Com p e q C s : MCTo ( Com p e q; C, s ) ( C, (update s q (evaluate e s p)) )
 | C_Sel p q l C s : MCTo ( Sel p q l; C, s ) ( C, s )
 | C_Then p q C1 C2 s : (s p = s q) -> MCTo ( If p == q Then C1 Else C2, s ) ( C1, s )
 | C_Else p q C1 C2 s : (s p <> s q) -> MCTo ( If p == q Then C1 Else C2, s ) ( C2, s )
 | C_Struct C1 C1' C2 C2' s1 s2 : Precongr C1 C1' -> Precongr C2' C2 -> MCTo (C1', s1) (C2', s2) -> MCTo (C1, s1) (C2, s2)
.


Inductive MCToStar : Configuration -> Configuration -> Prop :=
 | ToRefl c : MCToStar c c
 | ToSingle c1 c2 (P:MCTo c1 c2) : MCToStar c1 c2
 | ToTran c1 c2 c3 (P1:MCToStar c1 c2) (P2:MCToStar c2 c3) : MCToStar c1 c3
.

Notation "c --> c'" := (MCTo c c') (at level 50, left associativity).
Notation "c -->* c'" := (MCToStar c c') (at level 50, left associativity).


Definition terminated (c:Configuration) : Prop := Precongr (fst c) End.

Lemma not_end_precongr : forall (C C':Choreography), C <> End -> C' = End -> ~ Precongr C C'.
intros; intro.
induction H1; auto; try inversion H0.
Qed.

Lemma not_end_precongr' : forall C:Choreography, Precongr C End -> C = End.
intros.
elim (eq_chor_dec C End); auto.
intro.
elim not_end_precongr with C End; auto.
Qed.

Lemma terminated_iff_end : forall c:Configuration, terminated c <-> fst c = End.
Proof.
destruct c; unfold terminated; simpl; clear s.
split.
apply not_end_precongr'.
intro; rewrite H.
constructor.
Qed.

Definition HeadTo (c:Configuration) : ~ (terminated c) -> Configuration.
destruct c; destruct c; intros.
elim H; apply terminated_iff_end; auto.
destruct e.
apply (c, update s p0 (evaluate e s p)).
apply (c, s).
apply (if ((s p) =? (s p0)) then (c1, s) else (c2, s)).
Defined.

Example HeadTo_Com : forall p e q C s HC, 
HeadTo (Com p e q ; C, s) HC = (C, update s q (evaluate e s p)).
Proof.
intros.
simpl.
trivial.
Qed.

Example HeadTo_Sel : forall p q l C s HC, 
HeadTo (Sel p q l; C, s) HC = (C, s).
Proof.
intros.
simpl.
trivial.
Qed.

Lemma HeadTo_Soundness : forall c Hc, c --> (HeadTo c Hc).
Proof.
destruct c; intros.
induction c.
elim Hc; apply terminated_iff_end; trivial.
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

Example MCToStar_sanity_check : forall p e q s C, 
(Com p e q ; Com p zero q ; C, s) -->* (C, update s q 0).
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
rewrite update_update. trivial.
rewrite <- E.
apply ToSingle. apply HeadTo_Soundness.
Qed.

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

Theorem progress : forall c, ~(terminated c) -> exists c', c --> c'.
Proof.
intros.
exists (HeadTo c H).
apply HeadTo_Soundness.
Qed.

Theorem termination : forall C s, exists c', (C,s) -->* c' /\ terminated c'.
Proof.
pose proof terminated_iff_end as T.
induction C; intro s.
(* End *)
* exists (End, s). split. 
  + apply ToRefl.
  + rewrite T. trivial.
(* Eta *)
* set (c0 := (e;C,s)).
  assert (NTc0 : not (terminated c0)).
  rewrite T. discriminate.
  set (c1 := HeadTo c0 NTc0).
  assert (c1 = (HeadTo c0 NTc0)); auto.
  induction c1 as (C1, s1).
  elim (IHC s1); intros c' Hc'.
  inversion_clear c'; exists c'; split; auto.
  inversion_clear Hc'. 
  apply ToTran with (C,s1); auto.
  replace C with C1.
  apply ToSingle.
  rewrite H.
  apply HeadTo_Soundness.
  unfold c0 in H; induction e; simpl in H; inversion H; auto.
  inversion_clear Hc'. auto.
(* If *)
* rename C1 into CT, C2 into CE.
  set (c0 := (If p == p0 Then CT Else CE, s)).
  assert (NTc0 : not (terminated c0)).
  rewrite T. discriminate.
  set (c1 := HeadTo c0 NTc0).
  assert (c1 = (HeadTo c0 NTc0)); auto.
  induction c1 as (C1, s1).
  case_eq (Nat.eqb (s p) (s p0)); intro G.
  + elim (IHC1 s1); intros c' Hc'.
    inversion_clear c'; exists c'; split; auto.
    inversion_clear Hc'. 
    apply ToTran with (CT,s1); auto.
    replace CT with C1.
    apply ToSingle.
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
    apply ToTran with (CE,s1); auto.
    replace CE with C1.
    apply ToSingle.
    rewrite H.
    apply HeadTo_Soundness.
    unfold c0 in H.
    simpl in H.
    rewrite G in H.
    inversion H. auto.
    inversion_clear Hc'. auto.
Qed.

End Semantics.