Require Import Bool.
Require Import List.
Require Import Coq.Lists.ListSet.
Require Import Arith.
Require Import Sorting.Permutation.
Require Import Basic.
Require Import Common.
Require Import FunInd.
Require Import MC.
Require Import SP.

Local Open Scope nat_scope.

Section EPP.

Fixpoint merge (B1:Behaviour) (B2:Behaviour) : option Behaviour :=
match B1, B2 with
 | Send p e B, Send p' e' B' =>
    if (eqb_pid p p') && (eqb_expr e e') then
      match (merge B B') with
       | Some Bm => Some( Send p e Bm )
       | _ => None
      end
    else None
 | Recv p B, Recv p' B' =>
    if (eqb_pid p p') then
      match (merge B B') with
       | Some Bm => Some( Recv p Bm )
       | _ => None
      end
    else None
 | Sel p l B, Sel p' l' B' =>
    if (eqb_pid p p') && (eqb_label l l') then
      match (merge B B') with
       | Some Bm => Some( Sel p l Bm )
       | _ => None
      end
    else None
 | Branching p f, Branching p' f' =>
    if (eqb_pid p p') then
      match
        match (f left, f' left) with
        | (inl B, inl B') => match (merge B B') with Some B'' => Some (inl B'') | None => None end
        | (inl B, inr _) => Some (inl B)
        | (inr _, inl B') => Some (inl B')
        | (inr _, inr _) => Some (inr tt)
        end,
        match (f right, f' right) with
        | (inl B, inl B') => match (merge B B') with Some B'' => Some (inl B'') | None => None end
        | (inl B, inr _) => Some (inl B)
        | (inr _, inl B') => Some (inl B')
        | (inr _, inr _) => Some (inr tt)
        end
      with
        | Some bl, Some br => Some (Branching p (fun l => match l with left => bl | right => br end))
        | _, _ => None
      end
      (*
      match merge_branch (f left, f' left), merge_branch (f right, f' right) with
        | Some bl, Some br => Some (Branching p (fun l => match l with left => bl | right => br end))
        | _, _ => None
      end
      *)
      (* match merge_branches f f' with Some f'' => Some (Branching p f'') | None => None end *)
    else None
 | Cond p B1 B2, Cond p' B1' B2' =>
    if (eqb_pid p p') then
      match (merge B1 B1') with
       | Some B1m => match (merge B2 B2') with | Some B2m => Some( Cond p B1m B2m ) | _ => None end
       | _ => None
      end
    else None
 | End, End => Some End
 | _, _ => None
end.
(*
with merge_branch (bp : Branch * Branch) : option Branch :=
match bp with
| (inl B, inl B') => match (merge B B') with Some B'' => Some (inl B'') | None => None end
| (inl B, inr _) => Some (inl B)
| (inr _, inl B') => Some (inl B')
| (inr _, inr _) => Some (inr tt)
end
*)
(*
with merge_branches (f f' : Label -> Branch) : option (Label -> Branch) :=
  match merge_branch (f left) (f' left), merge_branch (f right) (f' right) with
  | Some bl, Some br => Some (fun l => match l with left => bl | right => br end)
  | _, _ => None
end
*)


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

Fixpoint bproj (C:Choreography) (r:Pid) : option Behaviour :=
match C with
| MC.End => (Some End)
| eta;C' => match eta with
            | p # e --> q => if (eqb_pid p r)
                               then bproj_buildB (Send q e) (bproj C' r)
                               else if (eqb_pid q r)
                                      then (bproj_buildB (Recv p) (bproj C' r))
                                      else (bproj C' r)
            | p --> q [ l ] => if (eqb_pid p r)
                               then bproj_buildB (Sel q l) (bproj C' r)
                               else if (eqb_pid q r)
                                      then match (bproj C' r) with
                                           | Some BC => Some (Branching p
                                                               (fun l' => match l, l' with
                                                                          | left,left => inl BC
                                                                          | right,right => inl BC
                                                                          | _,_ => inr tt end))
                                           | None => None
                                           end
                                      else (bproj C' r)
            end
| If p == q Then C1 Else C2 => if (eqb_pid p r)
                               then bproj_buildbiB (Cond q) (bproj C1 r) (bproj C2 r)
                               else if (eqb_pid q r)
                                      then bproj_buildB (Send p this)
                                             ( match ((bproj C1 r), (bproj C2 r)) with
                                               | (Some B1, Some B2) => (merge B1 B2)
                                               | (_, _) => None
                                               end
                                             )
                                      else match ((bproj C1 r), (bproj C2 r)) with
                                           | (Some B1, Some B2) => (merge B1 B2)
                                           | (_, _) => None
                                           end
end.

(*

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
*)

Fixpoint WellFormed (C:Choreography) : Prop :=
match C with
| MC.End => True
| eta; C' => match eta with Com p _ q => p <> q /\ WellFormed C'
                          | MC.Sel p q _ => p <> q /\ WellFormed C' end
| MC.Cond p q C1 C2 => p <> q /\ WellFormed C1 /\ WellFormed C2
end.

Fixpoint pn_eta (e:Eta) : list Pid :=
match e with
| Com p _ q => (cons p (cons q nil))
| MC.Sel p q _ => (cons p (cons q nil))
end
.

Fixpoint pn (C:Choreography) : list Pid :=
match C with
| MC.End => nil
| eta; C' => (set_union_pid (pn_eta eta) (pn C'))
| MC.Cond p q C1 C2 => (set_union_pid (set_union_pid (cons p (cons q nil)) (pn C1)) (pn C2))
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

Definition WellFormedConf (conf:Configuration) : Prop := WellFormed( fst conf ).

Fixpoint epp_list (conf:Configuration) (pids:list Pid) (WF:WellFormedConf conf) : option Network :=
match pids with
| nil => Some( Empty )
| cons p l => match (bproj (fst conf) p), (epp_list conf l WF) with
              | Some B, Some N => Some( Par ( Process p (snd conf p) B ) N )
              | _, _ => None end
end.

Fixpoint epp (conf:Configuration) (WF:WellFormedConf conf) : option Network := epp_list conf (pn (fst conf)) WF.

End EPP.

Section PaperExample1.

Local Definition p := 0.
Local Definition q := 1.
Local Definition r := 2.
Local Definition sigma : State := fun p => 0.

(* Definition TestChoreography := p # this --> q; p --> q [ left ]; MC.End. *)

(* Eval compute in (bproj TestChoreography p).
Eval compute in (bproj TestChoreography q).
Eval compute in (bproj TestChoreography r).
 *)

Definition PaperExample1_C := If p == q Then (p # this --> r; MC.End) Else (r # this --> p; MC.End).

Definition PaperExample1_C_Configuration := (PaperExample1_C, sigma).

Proposition PaperExample1_C_Configuration_WellFormed : WellFormedConf PaperExample1_C_Configuration.
unfold WellFormedConf.
simpl.
easy.
Qed.

Proposition PaperExample1_C_unprojectable : epp (PaperExample1_C, sigma) PaperExample1_C_Configuration_WellFormed = None.
easy.
Qed.

(* Eval compute in (bproj PaperExample1_1 p).
Eval compute in (bproj PaperExample1_1 q).
Eval compute in (bproj PaperExample1_1 r). *)

Definition PaperExample1_C'_Then := p --> r [left]; p # this --> r; MC.End.
Definition PaperExample1_C'_Else := p --> r [right]; r # this --> p; MC.End.

Eval compute in (bproj PaperExample1_C'_Then r).
Eval compute in (bproj PaperExample1_C'_Else r).

Definition r_BThen := bproj PaperExample1_C'_Then r.

Proposition r_BThen_defined : (exists B:Behaviour, r_BThen = Some B).
econstructor.
unfold r_BThen.
simpl.
reflexivity.
Qed.

Definition r_BElse := (bproj PaperExample1_C'_Else r).

Proposition r_BElse_defined : (exists B:Behaviour, r_BElse = Some B).
econstructor.
easy.
Qed.

Definition merge_option (oB1 oB2 : option Behaviour) : option Behaviour :=
match oB1, oB2 with
| Some B1, Some B2 => merge B1 B2
| _, _ => None
end.

Proposition r_merge_defined : (exists B:Behaviour, (merge_option r_BThen r_BElse) = Some B).
econstructor.
simpl.
auto.
Qed.

Proposition r_merge : (merge_option r_BThen r_BElse) = Some (Branching p (fun l : Label => match l with
                                    | left => inl (Recv p End)
                                    | right => inl (Send p this End)
                                    end)).
simpl.
reflexivity.
Qed.

Eval compute in (merge_option r_BThen r_BElse).

Definition PaperExample1_C' := If p == q Then PaperExample1_C'_Then Else PaperExample1_C'_Else.

(* Eval compute in (bproj PaperExample1_C' p).
Eval compute in (bproj PaperExample1_C' q).
Eval compute in (bproj PaperExample1_C' r).
 *)

Proposition r_merge_bproj_coherent : (merge_option r_BThen r_BElse) = (bproj PaperExample1_C' r).
simpl.
reflexivity.
Qed.

Definition PaperExample1_C'_Configuration := (PaperExample1_C', sigma).

Proposition PaperExample1_C'_Configuration_WellFormed : WellFormedConf PaperExample1_C'_Configuration.
unfold WellFormedConf.
simpl.
easy.
Qed.

(* Eval compute in epp PaperExample1_C'_Configuration PaperExample1_C'_Configuration_WellFormed. *)

Local Definition p_then_B := (r + left; (r ! this; bnil))%SP.
Local Definition p_else_B := (r + right; (r ? ; bnil))%SP.
Local Definition P := (p [0, If q Then p_then_B Else p_else_B])%SP.
Local Definition Q := (q [0, 0 ! this; bnil])%SP.
Local Definition R := (
  r [0, p & (fun l : Label => match l with
                              | left => inl (p ? ; bnil)%SP
                              | right => inl (p ! this; bnil)%SP
                              end)]
)%SP.

Proposition PaperExample1_C'_Configuration_epp :
(epp PaperExample1_C'_Configuration PaperExample1_C'_Configuration_WellFormed) =
Some (P | Q | R | nnil)%SP
.
reflexivity.
Qed.

(* Should be generalised *)
Local Theorem Some_eq : forall a b : Network, Some a = Some b -> a = b.
intros.
inversion H.
trivial.
Qed.

Local Lemma sp_evaluate_0_0 : (sp_evaluate this 0) = 0.
simpl.
trivial.
Qed.

Local Definition P' := (p [0, r + left; (r ! this; bnil)])%SP.
Local Definition Q' := (q [0, bnil])%SP.

Example PaperExample1_C'_Configuration_epp_FirstRed :
forall N, (epp PaperExample1_C'_Configuration PaperExample1_C'_Configuration_WellFormed) = Some N
          ->
          SPTo N (P' | Q' | R | nnil)%SP
.
intros.
simpl in H.
symmetry in H.
apply Some_eq in H.
rewrite H; clear.
unfold sigma.
(* set (ParH := (S_Par (pProc | qProc) (rProc | Empty) (pProc' | qProc'))).*)
set (ThenH := ((S_Then q 0 p 0 this bnil p_then_B p_else_B) sp_evaluate_0_0)).
set (PQred := (S_Struct (P | Q) (Q | P) (Q' | P') (P' | Q') (Sym P Q) ThenH (Sym Q' P'))).
apply (S_Struct (P|Q|R|nnil) ((P|Q)|R|nnil) ((P'|Q')|R|nnil) (P'|Q'|R|nnil)).
(* P | (Q | (R |nnil)) <= P | ( *)
apply (AssocL P Q (R | nnil)).
constructor.
apply PQred.
apply AssocR.
Qed.

End PaperExample1.


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

Lemma epp_preserves_pids (conf:Configuration) :
  forall (C:Choreography) (s:State) (N:Network) (WF:WellFormedConf conf),
  conf = (C,s) -> (epp conf WF) = Some N -> (eq_pidset (pn C) (SPpn N)).
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