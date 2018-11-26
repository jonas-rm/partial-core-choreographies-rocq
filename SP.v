Require Import Bool.
Require Import List.
Require Import Coq.Lists.ListSet.
Require Import Arith.
Require Import Sorting.Permutation.
Load MC.
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

Definition is_defined (A:Type) (o:option A) : bool :=
match o with
 | Some a => true
 | None => false
end.

Fixpoint merge (B1:Behaviour) (B2:Behaviour) : option Behaviour :=
match (B1, B2) with
 | (Send p e B, Send p' e' B') =>
    if (eqpid p p') && (eqexpr e e') then
      match (merge B B') with
       | Some Bm => Some( Send p e Bm )
       | _ => None
      end
    else None
 | (Recv p B, Recv p' B') =>
    if (eqpid p p') then
      match (merge B B') with
       | Some Bm => Some( Recv p Bm )
       | _ => None
      end
    else None
 | (Cond p B1 B2, Cond p' B1' B2') =>
    if (eqpid p p') then
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

Fixpoint WellFormed (C:Choreography) : Prop :=
match C with
| CoreChoreographies.End => True
| eta; C' => match eta with Com p _ q => p <> q /\ WellFormed C'
                          | CoreChoreographies.Sel p q _ => p <> q /\ WellFormed C' end
| CoreChoreographies.Cond p q C1 C2 => p <> q /\ WellFormed C1 /\ WellFormed C2
end.

Fixpoint pn_eta (e:Eta) : list Pid :=
match e with
| Com p _ q => (cons p (cons q nil))
| CoreChoreographies.Sel p q _ => (cons p (cons q nil))
end
.

Definition set_union_pid := set_union eq_nat_dec.
Definition set_inter_pid := set_inter eq_nat_dec.

Fixpoint pn (C:Choreography) : list Pid :=
match C with
| CoreChoreographies.End => nil
| eta; C' => (set_union_pid (pn_eta eta) (pn C'))
| CoreChoreographies.Cond p q C1 C2 => (set_union_pid (set_union_pid (cons p (cons q nil)) (pn C1)) (pn C2))
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

Definition WellFormedConf (conf:Configuration) : Prop := match conf with (C,s) => WellFormed C end.

Fixpoint epp_list (conf:Configuration) (pids:list Pid) (WF:WellFormedConf conf) : option Network :=
match conf with (C,s) =>
  match pids with
  | nil => Some( Empty )
  | cons p l => match ((bproj C p), (epp_list conf l WF)) with | (Some B, Some N) => Some( Par ( Process p (s p) B ) N )
                                                               | (_, _) => None end
  end
end.

Fixpoint epp (conf:Configuration) (WF:WellFormedConf conf) : option Network := match conf with (C,s) => (epp_list conf (pn C) WF) end.

Fixpoint SPpn (N:Network) : list Pid :=
match N with
| Empty => nil
| Process p v B => (p :: nil)
| Par N N' => (SPpn N) ++ (SPpn N')
end
.

Definition WellFormedNetwork (N:Network) : Prop := NoDup(SPpn N).
(* Enrich with no self-communications *)

Definition pidseteq (s:set Pid) (s':set Pid) : Prop := Permutation s s'.

Lemma set_union_whatever : forall (p p':Pid) (P:set Pid),
  {In p P /\ In p' P /\ (set_union_pid (p::p'::nil) P) = P} + 
  {In p P /\ ~In p' P /\ (set_union_pid (p::p'::nil) P) = (p::P)} + 
  {~In p P /\ In p' P /\ (set_union_pid (p::p'::nil) P) = (p::P)} + 
  {~In p P /\ ~In p' P /\ (set_union_pid (p::p'::nil) P) = (p::p'::P)}.
intros.
elim (In_dec eq_nat_dec p P); elim (In_dec eq_nat_dec p' P); intros.
(* 1/4 *)
repeat left; repeat split; auto; simpl.
induction P; simpl; auto.
inversion a.


Lemma epp_preserves_pids (conf:Configuration) :
  forall (C:Choreography) (s:State) (N:Network) (WF:WellFormedConf conf),
  conf = (C,s) -> (epp conf WF) = Some N -> (pidseteq (pn C) (SPpn N)).
Proof.
intros.
subst.
simpl in WF.
revert N H0.
induction C; intros.

(* End *)
simpl in H0.
simpl.
inversion H0.
simpl.
apply perm_nil.

(* Interaction *)
induction e.
inversion_clear WF.
simpl in H0.



set (H3 := (IHC H1 N)).
revert H0.
simpl.
unfold set_union_pid.
intro.
red.
unfold set_inter_pid.
Print set_inter.


simpl.
simpl in H0.
unfold set_union_pid, set_union in H0.
simpl in H0.
unfold epp_list in H0.
simpl in H0.
unfold epp in H0.
unfold epp_list in H0.
simpl in H0.
simpl in H0.
(* Com *)
Qed.

Lemma epp_preserves_wellformedness (conf:Configuration) (WF:WellFormedConf conf) : forall N, (epp conf WF) = Some N -> WellFormedNetwork N.
Proof.
intros.
destruct conf.
Qed.

End Syntax.