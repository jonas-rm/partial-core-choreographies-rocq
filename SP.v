Require Import Bool.
Require Import List.
Require Import Coq.Lists.ListSet.
Require Import Arith.
Require Import Sorting.Permutation.
Require Import Basics.
Require Import FunInd.

Local Open Scope nat_scope.

Section ToMove.

Definition is_defined (A:Type) (o:option A) : bool :=
match o with
 | Some a => true
 | None => false
end.

End ToMove.

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

Check (Empty | Empty)%SP.
Check (0 [1, bnil])%SP.
Check (Empty | 0 [1, bnil])%SP.
Check (If 0 Then bnil Else bnil)%SP.
Check (0!zero; 0?; 1+left; bnil)%SP.

Section Semantics.

Definition sp_evaluate (e:Expr) (v:Value) : Value :=
match e with
 | zero => 0
 | this => v
 | succ_this => S v
end.

Inductive Precongr : Network -> Network -> Prop :=
 | Refl N : Precongr N N
 | Trans N1 N2 N3 (P1:Precongr N1 N2) (P2:Precongr N2 N3) : Precongr N1 N3
 | PZero p v : Precongr (Process p v End) Empty
 | NZero N : Precongr (Par N Empty) N
.

Inductive SPTo : Network -> Network -> Prop :=
 | S_Com p v q u e B B' : SPTo ( p [v, q!e;B] | q [u, p?;B'] )%SP
                               ( p [v, B] | q [(sp_evaluate e v), B'] )%SP
 | S_Sel p v q u l B f {B':Behaviour}: (f l = inl B') -> SPTo ( Par (Process p v (Sel q l B)) (Process q u (Branching p f)) )
                               ( Par (Process p v B) (Process q u B') )
 | S_Then p v q u e B1 B2 B : ((sp_evaluate e v) = u) -> SPTo ( Par (Process p v (Send q e B)) (Process q u (Cond p B1 B2)) )
                               ( Par (Process p v B) (Process q u B1) )
 | S_Else p v q u e B1 B2 B : ((sp_evaluate e v) <> u) -> SPTo ( Par (Process p v (Send q e B)) (Process q u (Cond p B1 B2)) )
                               ( Par (Process p v B) (Process q u B2) )
 | S_Par N M N' : SPTo N N' -> SPTo (Par N M) (Par N' M)
 | S_Struct N1 N1' N2 N2' : Precongr N1 N1' -> Precongr N2' N2 -> SPTo N1' N2' -> SPTo N1 N2
.

Inductive SPToStar : Network -> Network -> Prop :=
 | ToRefl N : SPToStar N N
 | ToSingle N1 N2 (P:SPTo N1 N2) : SPToStar N1 N2
 | ToTran N1 N2 N3 (P1:SPToStar N1 N2) (P2:SPToStar N2 N3) : SPToStar N1 N3
.

Notation "N --> N'" := (SPTo N N') (at level 50, left associativity).
Notation "N -->* N'" := (SPToStar N N') (at level 50, left associativity).

End Semantics.