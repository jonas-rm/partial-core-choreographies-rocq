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

Notation "N | N'" := (Par N N') (at level 50, left associativity).
Notation "p , v |> B" := (Process p v B) (at level 50, left associativity).
Notation "'send' p e ; B" := (Send p e B) (at level 50, left associativity).
Notation "'recv' p ; B" := (Recv p B) (at level 50, left associativity).
Notation "'sel' p l ; B" := (Sel p l B) (at level 50, left associativity).
Notation "'branch' p f" := (Branching p f) (at level 50, left associativity).
Notation "'PIf' p 'PThen' B1 'PElse' B2" := (Cond p B1 B2) (at level 60).
Notation "'bnil'" := End (at level 50).

Check Empty | Empty.

Check 0, 1 |> bnil.

Check (proc p 0 sel r left; send r this; bnil).

Check (proc p 0 (PIf q PThen (sel r left; send r this; bnil) PElse (sel r right; recv r; bnil))).

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
 | S_Com p v q u e B B' : SPTo ( Par (Process p v (Send q e B)) (Process q u (Recv p B')) )
                               ( Par (Process p v B) (Process q (sp_evaluate e v) B') )
 | S_Sel p v q u l B f {B':Behaviour}: (f l = inl B') -> SPTo ( Par (Process p v (Sel q l B)) (Process q u (Branching p f)) )
                               ( Par (Process p v B) (Process q u B') )
 | S_Then p v q u e B1 B2 B : ((sp_evaluate e v) = u) -> SPTo ( Par (Process p v (Send q e B)) (Process q u (Cond p B1 B2)) )
                               ( Par (Process p v B) (Process q u B1) )
 | S_Else p v q u e B1 B2 B : ((sp_evaluate e v) <> u) -> SPTo ( Par (Process p v (Send q e B)) (Process q u (Cond p B1 B2)) )
                               ( Par (Process p v B) (Process q u B2) )
 | S_Par N M N' : SPTo N N' -> SPTo (Par N M) (Par N' M)
 | S_Struct N1 N1' N2 N2' : Precongr N1 N1' -> Precongr N2' N2 -> SPTo N1' N2' -> SPTo N1 N2
 (* misses S_Sel *)
.

Inductive SPToStar : Network -> Network -> Prop :=
 | ToRefl N : SPToStar N N
 | ToSingle N1 N2 (P:SPTo N1 N2) : SPToStar N1 N2
 | ToTran N1 N2 N3 (P1:SPToStar N1 N2) (P2:SPToStar N2 N3) : SPToStar N1 N3
.

Notation "N --> N'" := (SPTo N N') (at level 50, left associativity).
Notation "N -->* N'" := (SPToStar N N') (at level 50, left associativity).

End Semantics.