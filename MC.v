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
fun n => if (Nat.eqb p n) then v else (s p)
.

Definition Configuration : Type := Choreography * State.

Inductive MCTo : Configuration -> Configuration -> Prop :=
 | C_Com p e q C s : MCTo ( Com p e q; C, s ) ( C, (update s q (evaluate e s p)) )
 | C_Sel p q l C s : MCTo ( Sel p q l; C, s ) ( C, s )
 | C_Then p q C1 C2 s : (s p = s q) -> MCTo ( If p == q Then C1 Else C2, s ) ( C1, s )
 | C_Else p q C1 C2 s : (s p <> s q) -> MCTo ( If p == q Then C1 Else C2, s ) ( C2, s )
 | C_Struct C1 C1' C2 C2' s1 s2 : Precongr C1 C1' -> Precongr C2' C2 -> MCTo (C1', s1) (C2', s2) -> MCTo (C1, s1) (C2, s2)
.

Definition HeadTo (C:Choreography) (s:State) : C <> End -> Configuration.
destruct C; intros.
elim H; auto.
destruct e.
apply (C, update s p0 (evaluate e s p)).
apply (C, s).
elim (Nat.eqb (s p) (s p0)).
apply (C1, s).
apply (C2, s).
Defined.

Lemma HeadTo_Soundness : forall C s HC, MCTo (C, s) (HeadTo C s HC).
Proof.
induction C; intros.
elim HC; trivial.
induction e.
apply C_Com.
apply ( C_Sel p p0 l C s ).
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

Theorem progress_cool : forall C s, C <> End -> exists conf, MCTo (C, s) conf.
Proof.
intros.
exists (HeadTo C s H).
apply HeadTo_Soundness.
Qed.

(* Inductive MCToStar : Configuration -> Configuration -> Prop :=
 | ToRefl conf : MCToStar conf conf
 | 
 *)

End Semantics.
