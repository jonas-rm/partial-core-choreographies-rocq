Require Import Kleene.
Require Export MC.

Local Open Scope nat_scope.

(** * Choreography language
  We start by defining the types for the concrete language
  we use for proving Turing completeness. *)
Inductive Expr : Type :=
 | this : Expr
 | zero : Expr
 | succ_this : Expr
.

Inductive BExpr : Type := compare.

Module MC_Expressions <: DecType.

Definition t := Expr.

Lemma eq_dec : forall (e e' : Expr), { e = e' } + { e <> e' }.
Proof.
decide equality.
Qed.

End MC_Expressions.

Module Bool_Expressions <: DecType.

Definition t := BExpr.

Lemma eq_dec : forall (e e' : BExpr), { e = e' } + { e <> e' }.
Proof.
decide equality.
Qed.

End Bool_Expressions.

(** The two variables in each process. *)

Definition xx := true.
Definition yy := false.

Module MC_Eval <: (Eval MC_Expressions Bool Nat Nat).

Definition eval (e:Expr) (f:bool -> nat) : nat :=
match e with
 | zero => 0
 | this => f xx
 | succ_this => S (f xx)
end.

Lemma eval_wd : forall f f', (forall x, f x = f' x) ->
  forall e, eval e f = eval e f'.
Proof. intros. case e; simpl; auto. Qed.

End MC_Eval.

Module MC_BEval <: (Eval Bool_Expressions Bool Nat Bool).

Definition eval (b:BExpr) (f:bool -> nat) : bool :=
  (f xx =? f yy).

Lemma eval_wd : forall f f', (forall x, f x = f' x) ->
  forall b, eval b f = eval b f'.
Proof. intros. case b; simpl. unfold eval; auto. Qed.

End MC_BEval.

Module Import MC_Nat :=
  MCBase Nat Bool Nat MC_Expressions Bool_Expressions Nat MC_Eval MC_BEval.

(** Restricted conditional. *)

Definition Send p e q : Eta := p#e --> q$xx.
Definition IfEq p q C1 C2 : Choreography :=
  q#this --> p$yy;; If p ? compare Then C1 Else C2.

(* Probably means something.
Import St.
*)

Example sanity_check : forall P s,
  (Build_Program P (3#this --> 2$yy;; Sel 0 1 left;; If 2 ? compare Then (4#succ_this --> 3$xx;; End) Else (3#zero --> 2$xx;; End)),s)
  --[ L_Sel 0 1 left ]-->
  (Build_Program P (3#this --> 2$yy;; If 2 ? compare Then (4#succ_this --> 3$xx;; End) Else (3#zero --> 2$xx;; End)), s).
Proof.
intros.
constructor.
apply C_Delay_Eta.
1: simpl. auto with arith.
apply C_Sel.
Qed.

Example MCToStar_sanity_check : forall p e q s1 C P, exists s2 v,
  (Build_Program P (Send p e q;; Send p zero q;; C), s1)
  --[ (List.cons (L_Com p v q) (List.cons (L_Com p 0 q) List.nil)) ]-->*
  (Build_Program P C, s2) /\ (CSt.eq_state_ext s2 (CSt.update s1 q xx 0)).
Proof.
intros.
unfold Send.
generalize (C_Com P p e q xx (p#zero --> q$xx;;C) s1).
set (C' := (p # e --> q $ xx;; p # zero --> q $ xx;; C)%MC).
simpl. set (s' := CSt.update s1 q xx (eval_on_state e s1 p)). intros.
generalize (C_Com P p zero q xx C s').
set (C'' := (p # zero --> q $ xx;; C)%MC).
fold C'' in H.
simpl. set (s'' := CSt.update s' q xx 0). intros.
exists s'', (eval_on_state e s1 p); split.
+ eapply MCT_Step.
  1: constructor. apply H. apply eq_state_ext_refl.
  eapply MCT_Step.
  1: constructor. apply H0. apply eq_state_ext_refl.
  constructor.
+ unfold s'', s'.
  apply CSt.update_update_ext.
Qed.

(*
Section Implementation.

(* The type of partial functions and the notion of a choreography implementing one.
    We can only represent computable functions, but this is not a problem. *)

Definition PFunction (n:nat) := t nat n -> option nat.

Definition implements (P:Program) {n} (f:PFunction n) (ps:t Pid n) (q:Pid) :=
  forall (xs:t nat n) (s:State), (forall Hi, s (ps[@Hi]) xx = xs[@Hi]) ->
  (forall y, f xs = Some y -> exists s' ts P', (P,s) --[ts]-->* (P',s') /\ s' q xx = y /\ Main P' = End) /\
  (f xs = None -> forall s' ts P', (P,s) --[ts]-->* (P',s') -> Main P' <> End).

(** For convenience. *)
Lemma implements_None : forall P {n} f ps q, implements P f ps q -> 
  forall (xs:t nat n) (s:State), (forall Hi, s (ps[@Hi]) xx = xs[@Hi]) ->
  f xs = None -> forall s' ts P', (P,s) --[ts]-->* (P',s') -> Main P' <> End.
Proof.
unfold implements; intros.
elim (H _ _ H0); eauto.
Qed.

Lemma implements_Some : forall P {n} f ps q, implements P f ps q -> 
  forall (xs:t nat n) (s:State), (forall Hi, s (ps[@Hi]) xx = xs[@Hi]) ->
  forall y, f xs = Some y -> exists s' ts P', (P,s) --[ts]-->* (P',s') /\ s' q xx = y /\ Main P' = End.
Proof.
unfold implements; intros.
elim (H _ _ H0); auto.
Qed.

(** Currying for simple cases. *)
Definition make_pf_1 (f:nat -> nat) : PFunction 1
  := fun xs => Some (f (hd xs)).

Definition make_pf_2 (f:nat -> nat -> nat) : PFunction 2
  := fun xs => Some (f (hd xs) (hd (tl xs))).

Definition make_pf_3 (f:nat -> nat -> nat -> nat) : PFunction 3
  := fun xs => Some (f (hd xs) (hd (tl xs)) (hd (tl (tl xs)))).

(* We recover the examples from the paper. *)
Definition C_Inc (p t:Pid) : Choreography :=
  Send p this t;; Send t succ_this p;; End.

Definition P_Inc ps p t := Pack0 ps (C_Inc p t).

Lemma P_Inc_char : forall ps p t s,
  let s1 := update s t xx (s p xx) in
  let tl := (List.cons (L_Com p (s p xx) t) (List.cons (L_Com t (S (s p xx)) p) List.nil)) in
  (P_Inc ps p t, s) --[ tl ]-->* (Pack0 ps End, (update s1 p xx (S (s p xx)))).
Proof.
intros; eapply MCT_Step.
1: { constructor. apply C_Com. }
assert (S (s p xx) = eval_on_state succ_this s1 t).
1: { unfold s1; simpl. rewrite update_read; auto. }
eapply MCT_Step.
- constructor. simpl. rewrite H. apply C_Com.
- rewrite H. apply MCT_Refl.
Qed.

Lemma P_Inc_correct : forall ps p t, implements (P_Inc ps p t) (make_pf_1 (fun n => S n)) [p] p.
Proof.
unfold make_pf_1; split; intros; inversion H0.
generalize (P_Inc_char ps p t s).
set (s1 := update s t xx (s p xx)).
set (s2 := update s1 p xx (S (s p xx))).
set (tl1 := L_Com p (s p xx) t).
set (tl2 := L_Com t (S (s p xx)) p).
set (tls := List.cons tl1 (List.cons tl2 List.nil)).
simpl; intros.
exists s2, tls, (Pack0 ps End).
repeat split; auto.
unfold s2, s1; simpl.
rewrite update_read.
replace xs with [s p xx]; auto.
apply eq_nth_iff; intros.
rewrite <- H.
repeat rewrite nth_hd'; auto.
Qed.

End Implementation.
*)

(** * Extensions of MC
    We require some additional operators on MC for our encoding. *)

Section MC_plus.

Fixpoint Implementation_Choreography (m n:nat) (C:Choreography) :=
  match C with
  | End => False
  | Call X => m <= X <= n
  | RT_Call X _ C' => m <= X <= n /\ Implementation_Choreography m n C'
  | (Eta;; C')%MC => Implementation_Choreography m n C'
  | If p ? b Then C1 Else C2 => Implementation_Choreography m n C1 /\ Implementation_Choreography m n C2
end.

Definition Implementation_Program (P:Program) (m n:nat) :=
    Main P = Call m /\
    (forall k, m<=k<n -> Implementation_Choreography m n (Procs P k)) /\
    (forall k, (k<m \/ n<=k) -> Procs P m = End).

(** ** Functions Pi and Gamma *)

Fixpoint Pi {m} (f:PRFunction m) : nat :=
  match f with
  | Zero => 0
  | Successor => 0
  | Projection _ => 0
  | @Composition k _ g fs => Pi g + vsum (map Pi fs) + k
  | Recursion f g => Pi f + Pi g + 3
  | Minimization f => Pi f + 3
  end.

Fixpoint Gamma {m} (f:PRFunction m) : nat :=
  match f with
  | Zero => 1
  | Successor => 1
  | Projection _ => 1
  | @Composition _ _ g fs => Gamma g + vsum (map Gamma fs)
  | Recursion f g => Gamma f + Gamma g + 3
  | Minimization f => Gamma f + 2
  end.

(*
Eval compute in (Pi PR_sub).
Eval compute in (Gamma PR_sub).
*)

(** Useful macros for writing choreographies. *)
Definition Pack0 (ps:list Pid) (C:Choreography) :=
  Build_Program (fun (X:RecVar) => (ps,End)) C.

Definition Pack1 X CX : RecVar -> Choreography :=
  (fun (R:RecVar) => if RecVar_dec R X then CX else End).

End MC_plus.

(** * Definitions
    We have the usual problems with defining implementation: we need information about the size
    of the vector of processes that we only get with an interactive definition. *sigh*
    Even worse, because of composition we need to do induction on the depth of the function... *)
Section Definitions.

Fixpoint all_pids (n:Pid) :=
  match n with
  | O => List.cons 0 List.nil
  | S k => List.cons (S k) (all_pids k)
  end.

Fixpoint seq_labels (n:nat) {k} {m} (fs:t (PRFunction m) k) : t Pid k :=
  match fs with
  | [] => []
  | (_ :: fs') => (n :: seq_labels (S n) fs')
  end.

Fixpoint skip_labels (n:nat) {k} {m} (fs:t (PRFunction m) k) : t Pid k :=
  match fs with
  | [] => []
  | (f :: fs') => (n :: skip_labels (n + Pi f) fs')
  end.

(** This function takes care of the first part of the definition of composition.
    Relationship to the arguments in the paper:
    - fs is the vector of functions
    - ps are the (fixed) argument processes
    - target is the output process for the first function to implement
    - init is the label l_i
    - k is the first free procedure definition
*)
Fixpoint seq_compose {m} {k} (fs:t (PRFunction m) k) d (Hd:forall i, depth fs[@i] < d) (ps:t Pid m) (target init:nat) (X:RecVar)
  (Implement : forall m' (f:PRFunction m') (Hd:depth f < d) (ps':t Pid m') (q' i':nat) (k':RecVar), RecVar -> Choreography) {struct fs} : RecVar -> Choreography.
(*
  match fs with
  | [] => End
  | f :: fs' => Implement m f d (Hd Fin.F1) ps target init ;; compose_args fs' ps (S target) (init + Pi f) Implement
  end.
*)
Proof.
destruct fs.
- apply (fun _ => End).
- assert (forall i, depth fs[@i] < d).
  intro; apply (Hd (Fin.FS i)).
  pose (Implement m h (Hd Fin.F1) ps target init X) as Ph.
  pose (seq_compose _ _ fs d H ps (S target) (init + Pi h) (X + Gamma h) Implement) as Pfs.
  apply (fun Y => if Y <? X + Gamma h then (Ph Y) else (Pfs Y)).
Defined.

(** Relationship to the arguments in the paper:
    - f is the function (f)
    - pids is the list of all processes used in the choreography
    - ps are the input processes p
    - q is the output process q
    - init is the label l
    - k is the first free recursion variable
*)
Fixpoint Implementation_aux {m} (f:PRFunction m) d (Hd:depth f<d)
  (ps:t Pid m) (q:Pid) (init:nat) (X:RecVar) {struct d}: RecVar -> Choreography.
Proof.
induction d.
+ elim (Nat.nlt_0_r _ Hd).
+ destruct f; intros; revert X0.

  (* Zero *)
  - apply (Pack1 X (Send ps[@Fin.F1] zero q;; Call (S X))).

  (* Successor *)
  - apply (Pack1 X (Send ps[@Fin.F1] succ_this q;; Call (S X))).

  (* Projection *)
  - apply (Pack1 X (Send ps[@Fin.of_nat_lt l] this q;; Call (S X))).

  (* Composition *)
  - simpl in Hd; generalize (lt_S_n _ _ Hd); clear Hd; intro Hd'.
    pose (max_lt_l _ _ _ Hd') as Hdf.
    pose (max_lt_r _ _ _ Hd') as Hdfs.
    assert (forall i, depth fs[@i] < d).
    intros; rewrite <- nth_map'; apply vmax_lt; auto.
    pose (seq_compose fs _ H ps init (init+k) X (fun m f => Implementation_aux m f d)) as Pfs.
    pose (Implementation_aux _ f _ Hdf (seq_labels init fs) q (init + (vsum (map Pi fs))) (X + (vsum (map Gamma fs)))) as Pf.
    apply (fun Y => if Y <? X + vsum (map Gamma fs) then Pfs Y else Pf Y).

  (* Recursion *)
  - rename f1 into f; rename f2 into g.
    simpl in Hd; generalize (lt_S_n _ _ Hd); clear Hd; intro Hd'.
    pose (max_lt_l _ _ _ Hd') as Hf.
    pose (max_lt_r _ _ _ Hd') as Hg.
    pose (Implementation_aux _ f _ Hf (tl ps) init (init+3) X) as Pf.
    pose (Implementation_aux _ g _ Hg (S init :: init :: tl ps) (init+2) (init+3 + Pi f) (X + Gamma f + 2)) as Pg.
    apply (fun Y =>
      if (Y <? X + Gamma f) then Pf Y
      else if (RecVar_dec Y (X + Gamma f)) then
         (Send (init+2) zero (S init);; Call (X + Gamma f + 1))%MC
      else if (RecVar_dec Y (X + Gamma f + 1)) then 
         (IfEq (S init) ps[@Fin.F1] (Send init this q;; Call (X + Gamma f + Gamma g + 3)) (Call (X + Gamma f + 2)))%MC
      else if (RecVar_dec Y (X + Gamma f + Gamma g + 2)) then
         (Send (init+2) this init;; Send (S init) this (init+2);; Send (init+2) succ_this (S init);; Call (X + Gamma f + 1))%MC
      else Pg Y).

  (* Minimization *)
  - simpl in Hd; apply lt_S_n in Hd; rename Hd into Hf.
    pose (Implementation_aux _ f _ Hf (shiftin (S init) ps) init (init+3) (X + 1)) as Pf.
    apply (fun Y =>
      if (RecVar_dec Y X) then
         (Send (init+2) zero (init+1);; Call (X + 1))%MC
      else if (RecVar_dec Y (X + Gamma f + 1)) then
         (Send (init+1) zero (init+2);; IfEq (init+2) init
            (Send (init+1) this q;; Call (X + Gamma f + 2))
            (Send (init+1) this (init+2);; Send (init+2) succ_this (init+1);; Call (X + 1)))%MC
        else Pf Y).
Defined.

(** The definition in the paper uses auxiliary process names distinct from the ps and q,
    numbered from 0. We model this by using auxiliary processes higher than the ps and q. *)
Definition Implementation {m} (f:PRFunction m) (ps:t Pid m) (q:Pid) : Program :=
  Build_Program
    (fun X => (all_pids ((max q (vmax ps)) + Pi f),
               Implementation_aux f _ (lt_n_Sn (depth f)) ps q (S (max q (vmax ps))) 0 X))
    (Call 0).

(** By default, we take process 0 for q and 1..m for the ps. *)
Definition Implementation' {m} (f:PRFunction m) : Program :=
  Implementation f (vec_1_to_n m) 0.

(* Sanity checks.
Eval compute in (Main (Implementation' (Composition Successor [Zero]))).
Eval compute in (map snd (map (Procedures (Implementation' (Composition Successor [Zero]))) [0;1;2])).

Eval compute in (Main (Implementation' (Composition Zero [Projection aux13]))).
Eval compute in (map snd (map (Procedures (Implementation' (Composition Zero [Projection aux13]))) [0;1;2])).

Eval compute in (Main (Implementation' (Composition (Projection aux22) (Zero :: [Successor])))).
Eval compute in (map snd (map (Procedures (Implementation' (Composition (Projection aux22) (Zero :: [Successor])))) [0;1;2;3])).

Eval compute in (Main (Implementation' PR_add)).
Eval compute in (map snd (map (Procedures (Implementation' PR_add)) [0;1;2;3;4;5;6])).
Eval compute in (map snd (map (Procedures (Implementation' (Composition Successor [Projection aux23]))) [0;1;2])).
*)

(** There is also a parallel variant for composition. This is defined in the same steps, but
    requires yet another auxiliary function. *)

Definition copy_input {m} (ps qs:t Pid m) (X:RecVar) : Choreography.
(*
  match m with
  | 0 => End
  | S _ => (hd ps # this --> hd qs; copy_input (tl ps) (tl qs))
  end.
*)
Proof.
induction m.
+ apply (Call X).
+ apply (Send (hd ps) this (hd qs);; IHm (tl ps) (tl qs))%MC.
Defined.

Fixpoint copy_input_iter {m} (ps:t Pid m) {n} (qs: t (t Pid m) n) (X:RecVar) :
  RecVar -> Choreography :=
  match qs with
  | nil _ => (fun _ => End)
  | (rs::qs') => (fun Y => if RecVar_dec X Y
        then copy_input ps rs (S X)
        else copy_input_iter ps qs' (S X) Y)
  end.

(*
Eval compute in (map (copy_input_iter [1;3;5] [[2;4;6];[7;8;9]] 2) [0;1;2;3;4;5]).
*)

Fixpoint Gamma' {m} (f:PRFunction m) : nat :=
  match f with
  | Zero => 1
  | Successor => 1
  | Projection _ => 1
  | @Composition k _ g fs => Gamma g + vsum (map Gamma fs) + k
  | Recursion f g => Gamma f + Gamma g + 3
  | Minimization f => Gamma f + 2
  end.

(** The extra argument ps_start is for the processes where the inputs in fs[@0] come from. *)
Fixpoint par_compose {m} {k} (fs:t (PRFunction m) k) d (Hd:forall i, depth fs[@i] < d) (target init ps_start:nat) (X:RecVar)
  (Implement : forall m' (f:PRFunction m') (Hd:depth f < d) (ps':t Pid m') (q' i':nat) (k':RecVar), RecVar -> Choreography) {struct fs} : RecVar -> Choreography.
Proof.
destruct fs.
- apply (fun _ => End).
- assert (forall i, depth fs[@i] < d).
  intro; apply (Hd (Fin.FS i)).
  pose (Implement m h (Hd Fin.F1) (vec_k_to_n m ps_start) target init X) as Ph.
  pose (par_compose _ _ fs d H (S target) (init + Pi h) (ps_start + m) (X + Gamma h) Implement) as Pfs.
  apply (fun Y => if Y <? X + Gamma h then (Ph Y) else (Pfs Y)).
Defined.

Fixpoint Par_Implementation_aux {m} (f:PRFunction m) d (Hd:depth f<d)
  (ps:t Pid m) (q:Pid) (init:nat) (X:RecVar) {struct d}: RecVar -> Choreography.
Proof.
induction d.
+ elim (Nat.nlt_0_r _ Hd).
+ destruct f; intros; revert X0.

  (* Zero *)
  - apply (Pack1 X (Send ps[@Fin.F1] zero q;; Call (S X))).

  (* Successor *)
  - apply (Pack1 X (Send ps[@Fin.F1] succ_this q;; Call (S X))).

  (* Projection *)
  - apply (Pack1 X (Send ps[@Fin.of_nat_lt l] this q;; Call (S X))).

  (* Composition *)
  - simpl in Hd; generalize (lt_S_n _ _ Hd); clear Hd; intro Hd'.
    pose (max_lt_l _ _ _ Hd') as Hdf.
    pose (max_lt_r _ _ _ Hd') as Hdfs.
    assert (forall i, depth fs[@i] < d).
    intros; rewrite <- nth_map'; apply vmax_lt; auto.
    set (init' := init + m*k).
    pose (copy_input_iter ps (vec_m_with_k init m k) X) as Hinit.
    pose (par_compose fs _ H init' (init'+k) init (X+k) (fun m f => Par_Implementation_aux m f d)) as Pfs.
    pose (Par_Implementation_aux _ f _ Hdf (seq_labels init' fs) q (init' + (vsum (map Pi fs))) (X + k + (vsum (map Gamma' fs)))) as Pf.
    apply (fun Y =>
      if Y <? X + k then Hinit Y
      else if Y <? X + k + vsum (map Gamma fs) then Pfs Y else Pf Y).

  (* Recursion *)
  - rename f1 into f; rename f2 into g.
    simpl in Hd; generalize (lt_S_n _ _ Hd); clear Hd; intro Hd'.
    pose (max_lt_l _ _ _ Hd') as Hf.
    pose (max_lt_r _ _ _ Hd') as Hg.
    pose (Par_Implementation_aux _ f _ Hf (tl ps) init (init+3) X) as Pf.
    pose (Par_Implementation_aux _ g _ Hg (S init :: init :: tl ps) (init+2) (init+3 + Pi f) (X + Gamma' f + 2)) as Pg.
    apply (fun Y =>
      if (Y <? X + Gamma' f) then Pf Y
      else if (RecVar_dec Y (X + Gamma' f)) then
         (Send (init+2) zero (S init);; Call (X + Gamma' f + 1))%MC
      else if (RecVar_dec Y (X + Gamma' f + 1)) then 
         (IfEq (S init) ps[@Fin.F1] (Send init this q;; Call (X + Gamma' f + Gamma' g + 3)) (Call (X + Gamma' f + 2)))%MC
      else if (RecVar_dec Y (X + Gamma' f + Gamma' g + 2)) then
         (Send (init+2) this init;; Send (S init) this (init+2);; Send (init+2) succ_this (S init);; Call (X + Gamma' f + 1))%MC
      else Pg Y).

  (* Minimization *)
  - simpl in Hd; apply lt_S_n in Hd; rename Hd into Hf.
    pose (Par_Implementation_aux _ f _ Hf (shiftin (S init) ps) init (init+3) (X + 1)) as Pf.
    apply (fun Y =>
      if (RecVar_dec Y X) then
         (Send (init+2) zero (init+1);; Call (X + 1))%MC
      else if (RecVar_dec Y (X + Gamma' f + 1)) then
         (Send (init+1) zero (init+2);; IfEq (init+2) init
            (Send (init+1) this q;; Call (X + Gamma' f + 2))
            (Send (init+1) this (init+2);; Send (init+2) succ_this (init+1);; Call (X + 1)))%MC
        else Pf Y).
Defined.

Definition Par_Implementation {m} (f:PRFunction m) (ps:t Pid m) (q:Pid) : Program :=
  Build_Program
    (fun X => (all_pids ((max q (vmax ps)) + Pi f),
               Par_Implementation_aux f _ (lt_n_Sn (depth f)) ps q (S (max q (vmax ps))) 0 X))
    (Call 0).

(** By default, we take process 0 for q and 1..m for the ps. *)
Definition Par_Implementation' {m} (f:PRFunction m) : Program :=
  Par_Implementation f (vec_1_to_n m) 0.

(* Sanity checks.
Eval compute in (Main (Par_Implementation' (Composition Successor [Zero]))).
Eval compute in (map snd (map (Procedures (Par_Implementation' (Composition Successor [Zero]))) [0;1;2;3])).

Eval compute in (Main (Par_Implementation' (Composition Zero [Projection aux13]))).
Eval compute in (map snd (map (Procedures (Par_Implementation' (Composition Zero [Projection aux13]))) [0;1;2;3])).

Eval compute in (Main (Par_Implementation' (Composition (Projection aux22) [Zero; Successor]))).
Eval compute in (map snd (map (Procedures (Par_Implementation' (Composition (Projection aux22) (Zero :: [Successor])))) [0;1;2;3;4;5])).

Eval compute in (Main (Par_Implementation' PR_add)).
Eval compute in (map snd (map (Procedures (Par_Implementation' PR_add)) [0;1;2;3;4;5;6;7;8;9])).
Eval compute in (map snd (map (Procedures (Par_Implementation' (Composition Successor [Projection aux23]))) [0;1;2;3])).
*)

End Definitions.

Section Soundness.

(* Without classical logic we can't make PRFunctions into PFunctions. *)

(* Missing: confluence, determinism. *)

Definition implements (P:Program) {n} (f:PRFunction n) (ps:t Pid n) (q:Pid) :=
  forall (xs:t nat n) (s:State), (forall Hi, s (ps[@Hi]) xx = xs[@Hi]) ->
  (forall y, converges f xs y <-> exists s' ts P', (P,s) --[ts]-->* (P',s') /\ s' q xx = y /\ Main P' = End) /\
  (diverges f xs <-> forall s' ts P', (P,s) --[ts]-->* (P',s') -> Main P' <> End).

(** For convenience - unfinished.
Lemma implements_None : forall P {n} f ps q, implements P f ps q -> 
  forall (xs:t nat n) (s:State), (forall Hi, s (ps[@Hi]) xx = xs[@Hi]) ->
  diverges f xs -> forall s' ts P', (P,s) --[ts]-->* (P',s') -> Main P' <> End.
Proof.
unfold implements; intros.
elim (H _ _ H0); eauto.
Qed.

Lemma implements_Some : forall P {n} f ps q, implements P f ps q -> 
  forall (xs:t nat n) (s:State), (forall Hi, s (ps[@Hi]) xx = xs[@Hi]) ->
  forall y, converges f xs y -> exists s' ts P', (P,s) --[ts]-->* (P',s') /\ s' q xx = y /\ Main P' = End.
Proof.
unfold implements; intros.
elim (H _ _ H0); auto.
Qed.

Theorem encoding_sound : forall n (f:PRFunction n),
  implements (Implementation' f) f (vec_1_to_n n) 0.
*)

End Soundness.
