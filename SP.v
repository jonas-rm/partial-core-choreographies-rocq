Require Import Bool.
Require Import List.
Require Import Coq.Lists.ListSet.
Require Import Arith.
Require Import Sorting.Permutation.
Require Import Common.
Require Import MC.
Require Import Basics.

Local Open Scope nat_scope.

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
 | Par : Network -> Network -> Network
.

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

Definition is_defined (A:Type) (o:option A) : bool :=
match o with
 | Some a => true
 | None => false
end.

Fixpoint merge (B1:Behaviour) (B2:Behaviour) : option Behaviour :=
match (B1, B2) with
 | (Send p e B, Send p' e' B') =>
    if (eqb_pid p p') && (eqb_expr e e') then
      match (merge B B') with
       | Some Bm => Some( Send p e Bm )
       | _ => None
      end
    else None
 | (Recv p B, Recv p' B') =>
    if (eqb_pid p p') then
      match (merge B B') with
       | Some Bm => Some( Recv p Bm )
       | _ => None
      end
    else None
 | (Cond p B1 B2, Cond p' B1' B2') =>
    if (eqb_pid p p') then
      match (merge B1 B1') with
       | Some B1m => match (merge B2 B2') with | Some B2m => Some( Cond p B1m B2m ) | _ => None end
       | _ => None
      end
    else None
 | (End, End) => Some End
 | (_, _) => None
end.

Definition bproj_buildB (constructor:Behaviour -> Behaviour) (cont:option Behaviour) : option Behaviour :=
match cont with
| Some B => Some(constructor B)
| _ => None
end.

Definition bproj_buildbiB (biconstructor:Behaviour -> Behaviour -> Behaviour) (cont1:option Behaviour) (cont2:option Behaviour): option Behaviour :=
match cont1 with
| Some B1 => bproj_buildB (biconstructor B1) (cont2)
| _ => None
end.

Fixpoint bproj (C:Choreography) (p:Pid) : option Behaviour.
destruct C.
apply (Some End).
destruct e.
case_eq (Nat.eqb p p0).
intro.
apply (bproj_buildB (Send p1 e) (bproj C p)).
intro.
case_eq (Nat.eqb p p1).
intro.
apply (bproj_buildB (Recv p0) (bproj C p)).
intro.
apply (bproj C p).
case_eq (Nat.eqb p p0).
intro.
apply (bproj_buildB (Sel p1 l) (bproj C p)).
intro.
case_eq (Nat.eqb p p1).
intro.
apply (Some End). (*(Branching p0 (bproj C p)).*)
intro.
apply (bproj C p).
case_eq (Nat.eqb p p0).
intro.
apply (bproj_buildbiB (Cond p1) (bproj C1 p) (bproj C2 p)).
intro.
case_eq (Nat.eqb p p1).
intro.
apply (bproj_buildB (Send p0 this)
                    ( match ((bproj C1 p), (bproj C2 p)) with
                      | (Some B1, Some B2) => (merge B1 B2)
                      | (_, _) => None
                      end
                    )
      ).
intro.
apply ( match ((bproj C1 p), (bproj C2 p)) with
                      | (Some B1, Some B2) => (merge B1 B2)
                      | (_, _) => None
                      end
                    ).
Defined.

Fixpoint epp_list (conf:Configuration) (pids:list Pid) (WF:WellFormedConf conf) : option Network :=
match pids with
| nil => Some( Empty )
| cons p l => match ((bproj (fst conf) p), (epp_list conf l WF)) with | (Some B, Some N) => Some( Par ( Process p (snd conf p) B ) N )
                                                             | (_, _) => None end
end.

Fixpoint epp (conf:Configuration) (WF:WellFormedConf conf) : option Network := epp_list conf (pn (fst conf)) WF.

Fixpoint SPpn (N:Network) : list Pid :=
match N with
| Empty => nil
| Process p v B => (p :: nil)
| Par N N' => (SPpn N) ++ (SPpn N')
end
.

Definition WellFormedNetwork (N:Network) : Prop := NoDup(SPpn N).
(* Enrich with no self-communications *)

(* Lemma set_union_whatever : forall (p p':Pid) (P:set Pid),
  {In p P /\ In p' P /\ (set_union_pid (p::p'::nil) P) = P} + 
  {In p P /\ ~In p' P /\ (set_union_pid (p::p'::nil) P) = (p::P)} + 
  {~In p P /\ In p' P /\ (set_union_pid (p::p'::nil) P) = (p::P)} + 
  {~In p P /\ ~In p' P /\ (set_union_pid (p::p'::nil) P) = (p::p'::P)}.
Proof.
intros.
elim (In_dec eq_nat_dec p P); elim (In_dec eq_nat_dec p' P); intros.
(* 1/4 *)
repeat left; repeat split; auto; simpl.
induction P.
simpl.
symmetry.
destruct (p :: p' :: nil).
trivial.
contradiction.
destruct (p :: p' :: nil).
symmetry.
symmetry.
unfold set_union_pid. unfold set_union.
simpl.
rewrite -> ((set_union_pid nil P) = P).
induction P.
induction P.
induction P; simpl; auto.
inversion a.
 *)

(*
Lemma epp_preserves_pids (conf:Configuration) :
  forall (C:Choreography) (s:Store) (N:Network) (WF:WellFormedConf conf),
  conf = (C,s) -> (epp conf WF) = Some N -> (eq_pidset (pn C) (SPpn N)).
Proof.
Proof.
intros.
subst.
simpl in WF.
revert N H0.
induction C; intros.
(* End *)
simpl in H0.
simpl.
inversion_clear H0.
simpl.
apply perm_nil.
(* Interaction *)
induction e.
(* Com *)
inversion_clear WF.
set (NoDupPn := pn_is_set (Com p e p0; C) WF).
simpl. simpl in NoDupPn.
simpl in H0.


rewrite (set_union_pid_char).
rewrite (set_union_pid_char) in NoDupPn.
simpl in H0.


Qed.

Lemma epp_preserves_wellformedness (conf:Configuration) (WF:WellFormedConf conf) : forall N, (epp conf WF) = Some N -> WellFormedNetwork N.
Proof.
intros.
destruct conf.
Qed.
*)

End Syntax.