Require Import CC.

Local Open Scope nat_scope.

Module Amendment (P X V E B R:DecType) (Ev:Eval E X V V) (BEv:Eval B X V Bool).

Module Import CCBase := CCBase P X V E B P Ev BEv.

(*
Module Import EPPBase := EPPBase P X V E B P Ev BEv.
Module Import CCBase := EPPBase.CCBase.
*)

(** multicast selection from p to all processes in ps except p *)
Fixpoint mcast_selection (l : Label) (p : Pid) (ps : list Pid) (C : Choreography) : Choreography :=
match ps with
| cons q qs => if Pid_dec p q 
               then (mcast_selection l p qs C) 
               else p --> q [ l ] ;; (mcast_selection l p qs C)
| nil       => C
end.

Definition branches_pn := fun Pids C1 C2 => (set_union_pid (CCC_pn C1 Pids) (CCC_pn C2 Pids)).

(** Simple amendment: multicast left/right selections to all processes in the then or else branch of a conditional *)
Fixpoint amend_C ( C : Choreography) (Pids:RecVar -> list Pid) : Choreography :=
match C with
| Interaction eta C' => Interaction eta (amend_C C' Pids)
| Cond p b C1 C2     => let all_pids := branches_pn Pids C1 C2
                        in Cond p b 
                            (mcast_selection left  p all_pids (amend_C C1 Pids)) 
                            (mcast_selection right p all_pids (amend_C C2 Pids))
| Call X             => Call X
| RT_Call X l C'     => RT_Call X l (amend_C C' Pids)
| End                => End
end.

Definition Pids := fun (Defs : DefSet) X => fst (Defs X).

Definition amend_D Defs :=
  fun X => (fst (Defs X), amend_C (snd (Defs X)) (Pids Defs)).

Definition amend_P (P : Program) : Program :=
Build_Program (amend_D (Procedures P)) (amend_C (Main P) (Vars P)).

(** amendment preserves wellformedness *)
Lemma mcast_no_self_comm : forall l p ps C, no_self_comm C -> no_self_comm (mcast_selection l p ps C).
Proof.
intros. induction ps; auto.
simpl. case_eq (Pid_dec p a). 
auto.
rewrite Pdec.eqb_neq. simpl. auto.
Qed.

Lemma mcast_no_empty_ann : forall l p ps C, no_empty_ann C -> no_empty_ann (mcast_selection l p ps C).
Proof.
intros. induction ps; auto.
simpl. case_eq (Pid_dec p a); auto.
Qed.

Lemma amend_C_no_empty_ann : forall C Pids, no_empty_ann C -> no_empty_ann (amend_C C Pids).
Proof.
intros. induction C; auto; destroy H; simpl; auto.
apply conj; apply mcast_no_empty_ann; auto.
Qed.

Lemma amend_C_no_self_comm : forall C Pids, no_self_comm C -> no_self_comm (amend_C C Pids).
Proof.
intros. induction C; auto; destroy H; simpl; auto.
apply conj; apply mcast_no_self_comm; auto.
Qed.

Lemma amend_C_WF : forall C Pids, Choreography_WF C -> Choreography_WF (amend_C C Pids).
Proof.
unfold Choreography_WF. intros. destroy H. apply conj.
apply amend_C_no_self_comm. assumption.
apply amend_C_no_empty_ann. assumption.
Qed.

Lemma mcast_within_Xs : forall Xs l p ps C, within_Xs Xs C -> within_Xs Xs (mcast_selection l p ps C).
Proof.
intros. induction ps; auto.
simpl. case_eq (Pid_dec p a); auto.
Qed.

Lemma amend_C_within_Xs : forall Xs C Pids, within_Xs Xs C -> within_Xs Xs (amend_C C Pids).
Proof.
intros. induction C; simpl; auto; destroy H.
apply conj; apply mcast_within_Xs; auto.
auto.
Qed.

Lemma mcast_consistent : forall Xs l p ps C, consistent Xs C -> consistent Xs (mcast_selection l p ps C).
Proof.
intros. induction ps; auto.
simpl. case_eq (Pid_dec p a); auto.
Qed.

Lemma amend_C_consistent : forall Xs C Pids, consistent Xs C -> consistent Xs (amend_C C Pids).
Proof.
intros. induction C; simpl; auto; destroy H.
apply conj; apply mcast_consistent; auto.
auto.
Qed.

Lemma mcast_initial : forall l p ps C, initial C -> initial (mcast_selection l p ps C).
Proof.
intros. induction ps; auto.
simpl. case_eq (Pid_dec p a); auto.
Qed.

Lemma amend_C_initial : forall C Pids, initial C -> initial (amend_C C Pids).
Proof.
intros. induction C; simpl; auto; destroy H.
apply conj; apply mcast_initial; auto.
Qed.

Lemma amend_P_WF : forall Xs P, Program_WF Xs P -> Program_WF Xs (amend_P P).
Proof.
intros. destroy H. 
apply conj. apply amend_C_WF. assumption.
apply conj. apply amend_C_within_Xs. assumption.
apply conj. apply amend_C_consistent. assumption.
clear H0 H1 H2.
intros.
apply conj. apply amend_C_WF. apply H. assumption.
apply conj. apply amend_C_initial. apply H. assumption.
apply conj. apply H. assumption.
apply amend_C_within_Xs. apply H. assumption.
Qed.

(** There is an operational correspondence between a choreography and its amendment up-to injectioned selections *)

Definition selection (tl:RichLabel) : Prop :=
  match tl with
  | R_Sel _ _ _ => True
  | _           => False
end.


Lemma CCC_To_Com_value : forall Defs C s s' p q e v x, 
  (CCC_To Defs (p # e --> q $ x;; C) s (R_Com p v q x) C s') ->
  v = (eval_on_state e s p).
Proof.
intros. inversion H; auto.
inversion H2.
inversion H8.
contradiction H10.
trivial.
Qed.

Lemma amend_complete_C_Com : forall Defs C s s' p q e v x, 
  (CCC_To Defs (p # e --> q $ x;; C) s (R_Com p v q x) C s') -> 
  (CCC_To Defs (amend_C (p # e --> q $ x;; C) (Pids Defs)) s (R_Com p v q x) (amend_C C (Pids Defs)) s'). 
Proof.
intros. simpl.
apply CCC_To_Com_value in H as H1.
apply CCC_To_Com_state in H as H2.
rewrite H1.
apply C_Com.
rewrite <- H1.
assumption.
Qed.

Lemma amend_complete_C_Sel : forall Defs C s s' p q l, 
  (CCC_To Defs (p --> q [l];; C) s (R_Sel p q l) C s') -> 
  (CCC_To Defs (amend_C (p --> q [l];; C) (Pids Defs)) s (R_Sel p q l) (amend_C C (Pids Defs)) s'). 
Proof.
intros. simpl. 
apply CCC_To_Sel_state in H.
apply C_Sel.
assumption.
Qed.

Lemma amend_complete_C_Cond : forall Defs C1 C2 C3 s s' p b, 
  (CCC_To Defs (If p ?? b Then C1 Else C2 ) s (R_Cond p) C3 s') -> 
  (CCC_To Defs (amend_C (If p ?? b Then C1 Else C2 ) (Pids Defs)) s 
    (R_Cond p) (mcast_selection (if (beval_on_state b s p) then left else right) p 
      (branches_pn (Pids Defs) C1 C2) (amend_C C3 (Pids Defs))) s'). 
Proof.
intros. simpl.
inversion_clear H.
rewrite H1.
apply C_Then; assumption.
rewrite H1.
apply C_Else; assumption.
simpl in H0.
contradiction H0.
trivial.
Qed.

Definition is_mcast_selection ts : Prop := 
match ts with
| cons tl ts => match tl with 
                | (R_Sel p _ l) => fold_left 
                  (fun b tl => match tl with | (R_Sel p _ l) => True /\ b | _ => False end)
                  ts True
                | _ => False end  
| nil        => True
end.

Fixpoint mcast_selection_ts (l : Label) (p : Pid) (ps : list Pid) : list RichLabel :=
match ps with
| cons q qs => if Pid_dec p q 
               then (mcast_selection_ts l p qs) 
               else (R_Sel p q l) :: (mcast_selection_ts l p qs)
| nil       => nil
end.

(*

```
C = p.e -> q.x; 
    if r.b then
      s.e' -> t.x; 0
    else
      s.e' -> t.x; 0
```
We can apply Delay_Eta and Delay_Cond to obtain a transition to
```
C' = p.e -> q.x; 
     if r.b then
      0
     else
       0
```
This is no longer possible with the amendment of C
```
amend(C) = p.e -> q.x; 
      if r.b then
        r.L -> s;
        r.L -> t;
        s.e' -> t.x; 0
      else
        r.R -> s;
        r.R -> t;
        s.e' -> t.x; 0
```
*)

Lemma amend_complete : forall P P' s s' tl, 
  (P,s) --[ tl ]--> (P',s') -> exists ts, 
    is_mcast_selection (fst ts ++ snd ts) /\
    (amend_P P,s) --[ map forget (fst ts) ++ (tl :: map forget (snd ts)) ]-->* (amend_P P',s').
Proof.
intros. induction P as (Defs,C), P' as (Defs',C').
generalize (CCP_To_Defs_stable Defs Defs' C C' tl s s' H); intro.
rewrite <- H0 in H; rewrite <- H0; clear Defs' H0.
induction C. 
* (* Interaction e c *)
  inversion_clear H.  
  inversion_clear H0.
  + (* C_Com *)
    exists (nil, nil). split. 
    simpl. trivial.
    apply CCT_Step with (amend_P {| Procedures := Defs; Main := C' |}, s').
    unfold amend_P, Vars.
    do 2 constructor.
    auto.
    constructor.
  + (* C_Sel *)
    exists (nil, nil). split. 
    simpl. trivial.
    apply CCT_Step with (amend_P {| Procedures := Defs; Main := C' |}, s').
    unfold amend_P, Vars.
    do 2 constructor.
    auto.
    constructor.
  + (* C_Delay_Eta *)
    elim IHC.
    intros ts HT.
    exists ts.
    inversion_clear HT.
    split.
    assumption.
    


    ({| Procedures := Defs; Main := C |}, s) --[ tl ]--> ({| Procedures := Defs; Main := C' |}, s')
    do 2 eexists; split. 
    
    

; apply C_Delay_Eta; eauto.
* (* Cond : Pid -> BExpr -> Choreography -> Choreography -> Choreography *)
* (* Call : RecVar -> Choreography *)
* (* RT_Call : RecVar -> (list Pid) -> Choreography -> Choreography *)
* (* End : Choreography *)
Qed.

induction H0. 
* (* C_Com *) 
  exists nil, nil. apply conj; simpl. 
  trivial.
  apply CCT_Step with (amend_P {| Procedures := Defs; Main := C |}, s').
  2: constructor.
  unfold amend_P.
  simpl.
  constructor.
* (* C_Sel *) 
  left. constructor. simpl. constructor. assumption.
* (* C_Then *)
  right. left.
  exists (map forget ( mcast_selection_ts left p (branches_pn (Pids Defs) C1 C2) )).
  unfold amend_P, Procedures, Vars.
  apply CCT_Step with ({| Procedures := amend_D Defs; 
    Main :=  mcast_selection left p (branches_pn (Pids Defs) C1 C2) (amend_C C1 (Pids Defs)) 
  |}, s').
  + repeat constructor; auto.
  + induction (branches_pn (Pids Defs) C1 C2); simpl.
    apply CCT_Refl.
    case_eq (Pid_dec p a); auto.
    intro. 
    apply CCT_Step with ({| Procedures := amend_D Defs; Main := mcast_selection left p s0 (amend_C C1 (Pids Defs)) |}, s').
    repeat constructor.
    auto.
* (* C_Else *)
* (* C_Delay_Eta *)
* (* C_Delay_Cond *)
* (* C_Delay_Call *)
* (* C_ *)
* (* C_ *)
* (* C_ *)
* (* C_ *)
Qed.


Lemma amend_complete : forall P P' s s' tl, 
   ((P,s) --[ tl ]--> (P',s')) -> 
   ((amend_P P,s) --[ tl ]--> (amend_P P',s')) \/
   (exists ts, (amend_P P,s) --[ tl :: ts ]-->* (amend_P P',s')) \/
   (exists ts, (amend_P P,s) --[ ts ++ (tl :: nil) ]-->* (amend_P P',s')).
Proof.
intros. inversion_clear H. 
induction H0. 
* (* C_Com *) 
  left. constructor. simpl. constructor. assumption.
* (* C_Sel *) 
  left. constructor. simpl. constructor. assumption.
* (* C_Then *)
  right. left.
  exists (map forget ( mcast_selection_ts left p (branches_pn (Pids Defs) C1 C2) )).
  unfold amend_P, Procedures, Vars.
  apply CCT_Step with ({| Procedures := amend_D Defs; 
    Main :=  mcast_selection left p (branches_pn (Pids Defs) C1 C2) (amend_C C1 (Pids Defs)) 
  |}, s').
  + repeat constructor; auto.
  + induction (branches_pn (Pids Defs) C1 C2); simpl.
    apply CCT_Refl.
    case_eq (Pid_dec p a); auto.
    intro. 
    apply CCT_Step with ({| Procedures := amend_D Defs; Main := mcast_selection left p s0 (amend_C C1 (Pids Defs)) |}, s').
    repeat constructor.
    auto.
* (* C_Else *)
  right. left.
  exists (map forget ( mcast_selection_ts right p (branches_pn (Pids Defs) C1 C2) )).
  unfold amend_P, Procedures, Vars.
  apply CCT_Step with ({| Procedures := amend_D Defs; 
    Main :=  mcast_selection right p (branches_pn (Pids Defs) C1 C2) (amend_C C2 (Pids Defs)) 
  |}, s').
  + repeat constructor; auto.
  + induction (branches_pn (Pids Defs) C1 C2); simpl.
    apply CCT_Refl.
    case_eq (Pid_dec p a); auto.
    intro. 
    apply CCT_Step with ({| Procedures := amend_D Defs; Main := mcast_selection right p s0 (amend_C C2 (Pids Defs)) |}, s').
    repeat constructor.
    auto.
* (* C_Delay_Eta *)
  
  left. constructor. simpl. constructor; auto.

* (* C_Delay_Cond *)
* (* C_Delay_Call *)
* (* C_ *)
* (* C_ *)
* (* C_ *)
* (* C_ *)
Qed.

(** Amended choreographgies are always projectable *)
(*
Lemma amend_C_projectable : forall C Defs ps, projectable_C Defs ps (amend_C C (Pids Defs))).
Proof.

Qed.
*)
