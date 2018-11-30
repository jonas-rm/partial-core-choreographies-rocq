Require Import FunctionalExtensionality.
Require Import Nat.
Require Import EqNat.
Require Import PeanoNat.
Local Open Scope nat_scope.

Module CoreChoreographies.

Section Syntax.

Inductive Label : Type :=
 | left : Label
 | right : Label
.

Inductive Expr : Type :=
 | this : Expr
 | zero : Expr
 | succ_this : Expr
.

(* Not needed for now.
Definition eqexpr_dec : forall (e e' : Expr), { e = e' } + { e <> e' }.
Proof.
decide equality.
Defined.
*)

Definition eqexpr (e:Expr) (e':Expr) : bool :=
match (e, e') with
 | (this, this) => true
 | (zero, zero) => true
 | (succ_this, succ_this) => true
 | (_, _) => false
end.

(* Notation "e == e'" := (eqexpr e e') (at level 60). *)

Definition Pid := nat.

Definition eqpid := Nat.eqb.

Inductive Eta : Type :=
 | Com : Pid -> Expr -> Pid -> Eta
 | Sel : Pid -> Pid -> Label -> Eta
.

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

End Syntax.

Notation "p --> q [ l ]" := (Sel p q l) (at level 57, format "p '-->' q [ l ]").
Notation "p ( e ) --> q" := (Com p e q) (at level 57, format "p ( e ) '-->' q").
Notation "eta ';' C" := (Interaction eta C) (at level 60, right associativity).
Notation "'If' p '==' q 'Then' C1 'Else' C2" := (Cond p q C1 C2) (at level 60).

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

Definition Value := nat.

Definition Store := Pid -> Value.

(*
Definition eq_Store (s s':Store) := forall p, s p = s' p.
Notation "s0 ':=:' s1" := eq_Store s0 s1.
*)

Definition evaluate (e:Expr) (s:Store) (p:Pid) : Value :=
match e with
 | zero => 0
 | this => s p
 | succ_this => S (s p)
end.

Definition update (s:Store) (p:Pid) (v:Value) : Store :=
fun (q:Pid) => if (p =? q) then v else (s q)
.

Lemma update_read : forall (s:Store) (p:Pid) (v:Value),
  update s p v p = v.
Proof.
  intros.
  unfold update.
  rewrite <- beq_nat_refl; auto.
Qed.

Lemma update_monotonicity : forall (s:Store) (p q:Pid) (v:Value),
  p <> q -> update s p v q = s q.
Proof.
intros.
unfold update.
case_eq (p =? q); auto.
intro.
generalize (beq_nat_true _ _ H0); intros.
elim H; auto.
Qed.

Lemma update_update : forall (s:Store) (p:Pid) (v1 v2:Value),
  update (update s p v2) p v1 = update s p v1.
Proof.
intros.
unfold update.
apply FunctionalExtensionality.functional_extensionality.
unfold update; intro q.
case_eq (p =? q); trivial.
Qed.

Definition Configuration : Type := Choreography * Store.

Inductive MCTo : Configuration -> Configuration -> Prop :=
 | C_Com p e q C s : MCTo ( Com p e q; C, s ) ( C, (update s q (evaluate e s p)) )
 | C_Sel p q l C s : MCTo ( Sel p q l; C, s ) ( C, s )
 | C_Then p q C1 C2 s : (s p = s q) -> MCTo ( If p == q Then C1 Else C2, s ) ( C1, s )
 | C_Else p q C1 C2 s : (s p <> s q) -> MCTo ( If p == q Then C1 Else C2, s ) ( C2, s )
 | C_Struct C1 C1' C2 C2' s1 s2 : Precongr C1 C1' -> Precongr C2' C2 -> MCTo (C1', s1) (C2', s2) -> MCTo (C1, s1) (C2, s2)
.

Definition terminated (c:Configuration) : Prop :=
 Precongr (fst c) End
.

Example terminated_iff_end : forall c:Configuration, terminated c <-> fst c = End.
Proof.
intro c.
destruct c as (C,s).
split; unfold terminated; simpl;intro H.
* induction H.
+
+
+
+
+
+
+
+
*
Qed.


Inductive MCToStar : Configuration -> Configuration -> Prop :=
 | ToRefl c : MCToStar c c
 | ToSingle c1 c2 (P:MCTo c1 c2) : MCToStar c1 c2
 | ToTran c1 c2 c3 (P1:MCToStar c1 c2) (P2:MCToStar c2 c3) : MCToStar c1 c3
.

Definition terminated (c:Configuration) : Prop :=
 fst c = End.

Example terminated_iff_end : forall c:Configuration, terminated c <-> fst c = End.
Proof.
intros.
unfold iff; split; unfold terminated; unfold fst; trivial.
Qed.

Definition HeadTo (c:Configuration) : ~ (terminated c) -> Configuration.
destruct c; destruct c; intros.
elim H; apply terminated_iff_end; auto.
destruct e.
apply (c, update s p0 (evaluate e s p)).
apply (c, s).
apply (if ((s p) =? (s p0)) then (c1, s) else (c2, s)).
Defined.

(*Definition HeadTo' (C:Choreography) (s:Store) : C <> End -> Configuration :=
HeadTo (C,s).*)

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

Lemma HeadTo_Soundness : forall c Hc, MCTo c (HeadTo c Hc).
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
MCToStar (Com p e q ; Com p zero q ; C, s) (C, update s q 0).
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

Theorem progress : forall c, ~(terminated c) -> exists c', MCTo c c'.
Proof.
intros.
exists (HeadTo c H).
apply HeadTo_Soundness.
Qed.

Theorem termination : forall C s, exists c', MCToStar (C,s) c' /\ terminated c'.
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
