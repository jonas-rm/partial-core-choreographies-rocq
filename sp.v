Require Import Bool.
Load mc.
Local Open Scope nat_scope.

Module StatefulProcesses.

Section Syntax.

Inductive Behaviour : Type :=
 | End : Behaviour
 | Send : Pid -> Expr -> Behaviour -> Behaviour
 | Recv : Pid -> Behaviour -> Behaviour
 | Sel : Pid -> Label -> Behaviour -> Behaviour
 | Branching : Pid -> (Label -> option( Behaviour )) -> Behaviour
 | Cond : Pid -> Behaviour -> Behaviour -> Behaviour
.

Inductive Network : Type :=
 | Empty : Network
 | Process : Pid -> Value -> Behaviour -> Network
 | Par : Network -> Network -> Network.

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
 | S_Then p v q u e B1 B2 B : ((sp_evaluate e v) = u) -> SPTo ( Par (Process p v (Send q e B)) (Process q u (Cond p B1 B2)) )
                               ( Par (Process p v B) (Process q u B1) )
 | S_Else p v q u e B1 B2 B : ((sp_evaluate e v) <> u) -> SPTo ( Par (Process p v (Send q e B)) (Process q u (Cond p B1 B2)) )
                               ( Par (Process p v B) (Process q u B2) )
 | S_Par N M N' : SPTo N N' -> SPTo (Par N M) (Par N' M)
 | S_Struct N1 N1' N2 N2' : Precongr N1 N1' -> Precongr N2' N2 -> SPTo N1' N2' -> SPTo N1 N2
 (* misses S_Sel *)
.

Fixpoint merge (B1:Behaviour) (B2:Behaviour) : option Behaviour.
apply (
match (B1, B2) with
 | (Send p e B, Send p' e' B') =>
    if (Nat.eqb p p') && (eqexpr e e') && ((merge B B') <> None) then Some( Send p e (merge B B') )
    else None
 | (_, _) => None
end
).

Fixpoint bproj (C:Choreography) (p:Pid) : Behaviour.
destruct C.
apply End.
destruct e.
case_eq (Nat.eqb p p0).
intro.
apply (Send p1 e (bproj C p)).
intro.
case_eq (Nat.eqb p p1).
intro.
apply (Recv p0 (bproj C p)).
intro.
apply (bproj C p).
case_eq (Nat.eqb p p0).
intro.
apply (Sel p1 l (bproj C p)).
intro.
case_eq (Nat.eqb p p1).
intro.
apply End. (*(Branching p0 (bproj C p)).*)
intro.
apply (bproj C p).
case_eq (Nat.eqb p p0).
intro.
apply (Cond p1 (bproj C1 p) (bproj C2 p)).
intro.
case_eq (Nat.eqb p p1).
intro.
apply (Send p0 this (End)). (* merging here *)
intro.
apply End. (* merging here *)
Defined.

Print bproj.

End Syntax.