Require Import EqNat.
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

Notation "p '-->' q '[' l ']'" := (Sel p q l) (at level 57).
Notation "p '$' e '-->' q" := (Com p e q) (at level 57).
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

Definition State := Pid -> Value.

Definition evaluate (e:Expr) (s:State) (p:Pid) : Value :=
match e with
 | zero => 0
 | this => s p
 | succ_this => S (s p)
end.

Definition update (s:State) (p:Pid) (v:Value) : State :=
fun (q:Pid) => if (Nat.eqb p q) then v else (s q)
.

Lemma read_after_update : forall (s:State) (p:Pid) (v:Value),
  update s p v p = v.
Proof.
intros.
unfold update.
assert (G : (Nat.eqb p p) = true).
induction p; auto.
rewrite G; trivial.
Qed.

Lemma eqb_S : forall n m, Nat.eqb m n = Nat.eqb (S m) (S n).
Proof.
intros.
simpl.
trivial.
Qed.

Lemma eqb_eq : forall n m, Nat.eqb n m = true <-> n = m.
Proof.
induction n.
induction m.
split; trivial.
split; discriminate.
induction m.
split; discriminate.
simpl.
assert (Eq_S : forall p q, p = q <-> (S p) = (S q)).
intros; split; auto.
rewrite <- Eq_S.
apply IHn.
Qed.

(* Lemma neqb_neq : forall n m, Nat.eqb n m = false <-> n <> m. *)

(*Lemma local_update : forall (s:State) (p q:Pid) (v:Value),
  p <> q -> update s p v q = s q.
Proof.
intros.
unfold update.
pose proof eqb_eq p q as E.

Qed.

Lemma last_update : forall (s:State) (p:Pid) (v1 v2:Value),
  update (update s p v2) p v1 = update s p v1.*)

Definition Configuration : Type := Choreography * State.

Inductive MCTo : Configuration -> Configuration -> Prop :=
 | C_Com p e q C s : MCTo ( Com p e q; C, s ) ( C, (update s q (evaluate e s p)) )
 | C_Sel p q l C s : MCTo ( Sel p q l; C, s ) ( C, s )
 | C_Then p q C1 C2 s : (s p = s q) -> MCTo ( If p == q Then C1 Else C2, s ) ( C1, s )
 | C_Else p q C1 C2 s : (s p <> s q) -> MCTo ( If p == q Then C1 Else C2, s ) ( C2, s )
 | C_Struct C1 C1' C2 C2' s1 s2 : Precongr C1 C1' -> Precongr C2' C2 -> MCTo (C1', s1) (C2', s2) -> MCTo (C1, s1) (C2, s2)
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
elim (Nat.eqb (s p) (s p0)).
apply (c1, s).
apply (c2, s).
Defined.

Definition HeadTo' (C:Choreography) (s:State) : C <> End -> Configuration :=
HeadTo (C,s).

Example foo : forall p e q C s HC, 
HeadTo (Com p e q ; C, s) HC = (C, update s q (evaluate e s p)).
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
apply ( C_Sel p p0 l c s ).
unfold HeadTo.
unfold bool_rect.
case_eq (Nat.eqb (s p) (s p0)); intros.
apply C_Then.
apply beq_nat_true; auto.
apply C_Else.
apply beq_nat_false; auto.
Qed.

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

Theorem progress_cool : forall c, ~(terminated c) -> exists c', MCTo c c'.
Proof.
intros.
exists (HeadTo c H).
apply HeadTo_Soundness.
Qed.

Inductive MCToStar : Configuration -> Configuration -> Prop :=
 | ToRefl c : MCToStar c c
 | To c1 c2 (P:MCTo c1 c2) : MCToStar c1 c2
 | ToTran c1 c2 c3 (P1:MCToStar c1 c2) (P2:MCToStar c2 c3) : MCToStar c1 c3
.

(*Example MCToStar_sanity_check : forall p e q s C, 
MCToStar (Com p e q ; Com p zero q ; C, s) (C, update s q 0).
Proof.
intros.
set (c0 := (Com p e q ; Com p zero q ; C, s)).
assert (NTc0 : not (terminated c0)).
unfold terminated; unfold fst; discriminate.
set (c1 := HeadTo c0 NTc0).
apply ToTran with c1.
apply To; apply HeadTo_Soundness.
assert (NTc1 : not (terminated c1)).
unfold terminated; unfold fst; discriminate.
set (c2 := HeadTo c1 NTc1).
set (c3 := (C, update s q 0)).
assert (EqS : snd c2 = snd c3).
simpl.
unfold update.
assert (EqC2C3 : c2 = c3).
unfold c2; unfold c3; repeat simpl.
unfold update.

Qed.*)


(*Theorem termination : forall c1, exists c2, terminated c2 /\ MCToStar c1 c2.
Proof.
intro c1.
destruct c1 as (C1,s1).
induction C1.
exists (End,s1).
split.
apply terminated_iff_end; trivial.
apply ToRefl.



elim H; intros.
destruct H0.
exists x.
split.
inversion e.
apply ToTran with (HeadTo (e;c,b) ).

unfold terminated; trivial.
Qed.*)

End Semantics.
