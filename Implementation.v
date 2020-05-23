Require Import Kleene.
Require Import Common.
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

Module Export MC_Nat :=
  MCBase Nat Bool Nat MC_Expressions Bool_Expressions Nat MC_Eval MC_BEval.

Local Open Scope MC_scope.

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
rewrite <- forget_Sel.
constructor.
apply C_Delay_Eta.
1: simpl. auto with arith.
apply C_Sel'.
Qed.

Example MCToStar_sanity_check : forall p e q s1 C P, exists s2 v,
  (Build_Program P (Send p e q;; Send p zero q;; C), s1)
  --[ (List.cons (L_Com p v q) (List.cons (L_Com p 0 q) List.nil)) ]-->*
  (Build_Program P C, s2) /\ (CSt.eq_state_ext s2 (CSt.update s1 q xx 0)).
Proof.
intros.
unfold Send.
generalize (C_Com P p e q xx (p#zero --> q$xx;;C) s1).
set (C' := p # e --> q $ xx;; p # zero --> q $ xx;; C).
simpl. set (s' := CSt.update s1 q xx (eval_on_state e s1 p)). intros.
generalize (C_Com P p zero q xx C s').
set (C'' := p # zero --> q $ xx;; C).
fold C'' in H.
simpl. set (s'' := CSt.update s' q xx 0). intros.
exists s'', (eval_on_state e s1 p); split.
+ eapply MCT_Step.
  1: rewrite <- (forget_Com xx). constructor. apply H. ESEr.
  eapply MCT_Step.
  1: rewrite <- (forget_Com xx). constructor. apply H0. ESEr.
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
  | Eta;; C' => Implementation_Choreography m n C'
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

Lemma Gamma_neq_zero : forall m (f:PRFunction m), 0 < Gamma f.
Proof.
induction f; simpl; auto with arith.
Qed.

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

Lemma all_pids_not_nil : forall n, all_pids n <> List.nil.
Proof. intros; case n; discriminate. Qed.

Fixpoint seq_labels (n:nat) {k} {m} (fs:t (PRFunction m) k) : t Pid k :=
  match fs with
  | [] => []
  | (_ :: fs') => (n :: seq_labels (S n) fs')
  end.

Lemma seq_labels_lt : forall x {m k} (fs:t (PRFunction m) k) n,
  In x (seq_labels n fs) -> n <= x < n + k.
Proof.
induction k.
+ refine (@case0 _ _ _); simpl; intros. inversion H.
+ intro. revert k fs IHk. refine (@caseS _ _ _); simpl; intros.
  elim (In_elim H); clear H; intro.
  - rewrite H; split; auto with arith.
    rewrite <- plus_Snm_nSm. apply le_plus_l.
  - elim (IHk _ _ H); intros.
    split; auto with arith. rewrite <- plus_Snm_nSm; auto.
Qed.

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
    pose (vmax_lt_map _ _ Hdfs) as H.
    pose (seq_compose fs _ H ps init (init+m) X (fun m f => Implementation_aux m f d)) as Pfs.
    pose (Implementation_aux _ f _ Hdf (seq_labels init fs) q (init + m) (X + (vsum (map Gamma fs)))) as Pf.
    apply (fun Y => if Y <? X + vsum (map Gamma fs) then Pfs Y else Pf Y).

  (* Recursion *)
  - rename f1 into g; rename f2 into h.
    simpl in Hd; generalize (lt_S_n _ _ Hd); clear Hd; intro Hd'.
    pose (max_lt_l _ _ _ Hd') as Hg.
    pose (max_lt_r _ _ _ Hd') as Hh.
    pose (Implementation_aux _ g _ Hg (tl ps) init (init+3) X) as Pg.
    pose (Implementation_aux _ h _ Hh (S init :: init :: tl ps) (init+2) (init+3 + Pi g) (X + Gamma g + 2)) as Ph.
    apply (fun Y =>
      if (Y <? X + Gamma g) then Pg Y
      else if (RecVar_dec Y (X + Gamma g)) then
         Send (init+2) zero (S init);; Call (X + Gamma g + 1)
      else if (RecVar_dec Y (X + Gamma g + 1)) then 
         IfEq (S init) ps[@Fin.F1] (Send init this q;; Call (X + Gamma g + Gamma h + 3)) (Call (X + Gamma g + 2))
      else if (RecVar_dec Y (X + Gamma g + Gamma h + 2)) then
         Send (init+2) this init;; Send (S init) this (init+2);; Send (init+2) succ_this (S init);; Call (X + Gamma g + 1)
      else Ph Y).

  (* Minimization *)
  - simpl in Hd; apply lt_S_n in Hd; rename Hd into Hf.
    pose (Implementation_aux _ f _ Hf (shiftin (init+1) ps) init (init+3) (X + 1)) as Pf.
    apply (fun Y =>
      if (RecVar_dec Y X) then
         Send (init+2) zero (init+1);; Call (X + 1)
      else if (RecVar_dec Y (X + Gamma f + 1)) then
         Send (init+1) zero (init+2);; IfEq (init+2) init
            (Send (init+1) this q;; Call (X + Gamma f + 2))
            (Send (init+1) this (init+2);; Send (init+2) succ_this (init+1);; Call (X + 1))
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

(** Again - since the definitions are interactive, we prove that they behave as expected. *)
Lemma Zero_Procs : forall d Hd ps q n X,
  Implementation_aux Zero d Hd ps q n X X = Send ps[@Fin.F1] zero q;; Call (S X).
Proof.
intros; induction d. inversion Hd.
simpl. unfold Pack1; simpl.
assert (X = X); auto.
rewrite <- Rdec.eqb_eq in H. unfold RecVar_dec.
rewrite H; auto.
Qed.

Lemma Successor_Procs : forall d Hd ps q n X,
  Implementation_aux Successor d Hd ps q n X X = Send ps[@Fin.F1] succ_this q;; Call (S X).
Proof.
intros; induction d. inversion Hd.
simpl. unfold Pack1; simpl.
assert (X = X); auto.
rewrite <- Rdec.eqb_eq in H. unfold RecVar_dec.
rewrite H; auto.
Qed.

Lemma Projection_Procs : forall k m (Hp:k<m) d Hd ps q n X,
  Implementation_aux (Projection Hp) d Hd ps q n X X = Send ps[@Fin.of_nat_lt Hp] this q;; Call (S X).
Proof.
intros; induction d. inversion Hd.
simpl. unfold Pack1; simpl.
assert (X = X); auto.
rewrite <- Rdec.eqb_eq in H. unfold RecVar_dec.
rewrite H; auto.
Qed.

Lemma seq_compose_Procs_hd : forall m k f (fs:t (PRFunction m) k) d Hd ps q i X Implement Y,
  X <= Y < X + Gamma f ->
  seq_compose (f::fs) d Hd ps q i X Implement Y = 
    Implement m f (Hd Fin.F1) ps q i X Y.
Proof.
intros; simpl.
inversion_clear H.
apply Nat.ltb_lt in H1; rewrite H1; auto.
Qed.

Lemma seq_compose_Procs_tl : forall m k f (fs:t (PRFunction m) k) d Hd ps q i X Implement Y,
  X + Gamma f <= Y < X + (vsum (map Gamma (f::fs))) ->
  seq_compose (f::fs) d Hd ps q i X Implement Y = 
    seq_compose fs d (fun i => Hd (Fin.FS i)) ps (S q) (i + Pi f) (X + Gamma f) Implement Y.
Proof.
intros; simpl.
inversion_clear H.
apply le_not_lt, Nat.ltb_nlt in H0; rewrite H0; auto.
Qed.

Lemma Composition_Procs_fs : forall k m (fs:t (PRFunction k) m) g d (Hd:depth (Composition g fs) < S d) ps q n X Y,
  X <= Y < X + (vsum (map Gamma fs)) ->
  let Hd' := (lt_S_n (Nat.max (depth g) (vmax (map depth fs))) d Hd) in
  let Hf := (vmax_lt_map _ _ (max_lt_r _ _ _ Hd')) in
  Implementation_aux (Composition g fs) _ Hd ps q n X Y =
    seq_compose fs _ Hf ps n (n+m) X (fun m f => Implementation_aux f d) Y.
Proof.
intros; simpl.
inversion_clear H.
rewrite <- Nat.ltb_lt in H1. rewrite H1; auto.
Qed.

Lemma Composition_Procs_g : forall k m (fs:t (PRFunction k) m) g d (Hd:depth (Composition g fs) < S d) ps q n X Y,
  X + (vsum (map Gamma fs)) <= Y < X + Gamma (Composition g fs) ->
  let Hd' := (lt_S_n (Nat.max (depth g) (vmax (map depth fs))) d Hd) in
  let Hg := (max_lt_l _ _ _ Hd') in
  Implementation_aux (Composition g fs) _ Hd ps q n X Y =
    Implementation_aux g _ Hg (seq_labels n fs) q (n + m) (X + (vsum (map Gamma fs))) Y.
Proof.
intros; simpl.
inversion_clear H.
apply le_not_lt, Nat.ltb_nlt in H0. rewrite H0; auto.
Qed.

Lemma Recursion_Procs_g : forall k (g:PRFunction k) h d (Hd:depth (Recursion g h) < S d) ps q n X Y,
  X <= Y < X + Gamma g ->
  let Hd' := (lt_S_n (Nat.max (depth g) (depth h)) d Hd) in
  let Hg := (max_lt_l _ _ _ Hd') in
  Implementation_aux (Recursion g h) _ Hd ps q n X Y =
    Implementation_aux _ _ Hg (tl ps) n (n+3) X Y.
Proof.
intros; simpl.
inversion_clear H.
rewrite <- Nat.ltb_lt in H1. rewrite H1; auto.
Qed.

Lemma Recursion_Procs_0 : forall k (g:PRFunction k) h d (Hd:depth (Recursion g h) < S d) ps q n X,
  Implementation_aux (Recursion g h) _ Hd ps q n X (X + Gamma g) =
    Send (n + 2) zero (S n);; Call (X + Gamma g + 1).
Proof.
intros; simpl.
generalize (lt_irrefl (X+Gamma g)); intro.
rewrite <- Nat.ltb_nlt in H. rewrite H.
unfold RecVar_dec. generalize (eq_refl (X+Gamma g)); intro.
apply Rdec.eqb_eq in H0. rewrite H0; auto.
Qed.

Lemma Recursion_Procs_1 : forall k (g:PRFunction k) h d (Hd:depth (Recursion g h) < S d) ps q n X,
  Implementation_aux (Recursion g h) _ Hd ps q n X (X + Gamma g + 1) =
    IfEq (S n) ps[@Fin.F1] (Send n this q;; Call (X + Gamma g + Gamma h + 3)) (Call (X + Gamma g + 2)).
Proof.
intros; simpl.
assert (~ X + Gamma g + 1 < X+Gamma g); intros.
+ intro. apply lt_irrefl with (X + Gamma g).
  etransitivity; eauto. rewrite plus_comm in H; auto.
+ rewrite <- Nat.ltb_nlt in H. rewrite H.
  unfold RecVar_dec.
  assert (X + Gamma g + 1 <> X + Gamma g); intros.
  1: apply gt_neq; rewrite plus_comm; auto.
  apply Rdec.eqb_neq in H0. rewrite H0.
  generalize (eq_refl (X+Gamma g + 1)); intro.
  apply Rdec.eqb_eq in H1. rewrite H1; auto.
Qed.

Lemma Recursion_Procs_h : forall k (g:PRFunction k) h d (Hd:depth (Recursion g h) < S d) ps q n X Y,
  X + Gamma g + 2 <= Y < X + Gamma g + Gamma h + 2 ->
  let Hd' := (lt_S_n (Nat.max (depth g) (depth h)) d Hd) in
  let Hh := (max_lt_r _ _ _ Hd') in
  Implementation_aux (Recursion g h) _ Hd ps q n X Y =
    Implementation_aux _ _ Hh (S n :: n :: tl ps) (n+2) (n+3 + Pi g) (X + Gamma g + 2) Y.
Proof.
intros; simpl.
inversion_clear H.
assert (~ Y < X+Gamma g); intros.
+ intro. apply lt_irrefl with (X + Gamma g).
  apply le_lt_trans with (X + Gamma g + 2); auto with arith.
  apply le_lt_trans with Y; auto.
+ rewrite <- Nat.ltb_nlt in H. rewrite H.
  unfold RecVar_dec.
  assert (Y <> X + Gamma g); intros.
  1: {
    apply gt_neq.
    apply lt_le_trans with (X + Gamma g + 2); auto with arith.
    rewrite <- (plus_comm 2); auto with arith.
  }
  apply Rdec.eqb_neq in H2. rewrite H2.
  assert (Y <> X + Gamma g + 1); intros.
  1: {
    apply gt_neq.
    apply lt_le_trans with (X + Gamma g + 2); auto with arith.
  }
  apply Rdec.eqb_neq in H3. rewrite H3.
  apply lt_neq, Rdec.eqb_neq in H1. simpl in H1; rewrite H1; auto.
Qed.

Lemma Recursion_Procs_2 : forall k (g:PRFunction k) h d (Hd:depth (Recursion g h) < S d) ps q n X,
  Implementation_aux (Recursion g h) _ Hd ps q n X (X + Gamma g + Gamma h + 2) =
    Send (n+2) this n;; Send (S n) this (n+2);; Send (n+2) succ_this (S n);; Call (X + Gamma g + 1).
Proof.
intros; simpl.
assert (~ X + Gamma g + Gamma h + 2 < X+Gamma g); intros.
+ intro. apply lt_irrefl with (X + Gamma g).
  apply le_lt_trans with (X + Gamma g + Gamma h + 2); auto with arith.
+ rewrite <- Nat.ltb_nlt in H. simpl in H; rewrite H.
  unfold RecVar_dec.
  assert (X + Gamma g + Gamma h + 2 <> X + Gamma g); intros.
  1: {
    apply gt_neq.
    apply lt_le_trans with (X + Gamma g + 2); auto with arith.
    rewrite <- (plus_comm 2); auto with arith.
  }
  apply Rdec.eqb_neq in H0. simpl in H0; rewrite H0.
  assert (X + Gamma g + Gamma h + 2 <> X + Gamma g + 1); intros.
  1: {
    apply gt_neq.
    apply lt_le_trans with (X + Gamma g + 2); auto with arith.
  }
  apply Rdec.eqb_neq in H1. simpl in H1; rewrite H1.
  generalize (eq_refl (X + Gamma g + Gamma h + 2)); intro.
  apply Rdec.eqb_eq in H2. simpl in H2; rewrite H2; auto.
Qed.

Lemma Minimization_Procs_0 : forall k (h:PRFunction (S k)) d (Hd:depth (Minimization h) < S d) ps q n X,
  Implementation_aux (Minimization h) _ Hd ps q n X X =
    Send (n+2) zero (n+1);; Call (X + 1).
Proof.
intros; simpl.
unfold RecVar_dec.
generalize (eq_refl X); intro.
apply Rdec.eqb_eq in H. rewrite H; auto.
Qed.

Lemma Minimization_Procs_h : forall k (h:PRFunction (S k)) d (Hd:depth (Minimization h) < S d) ps q n X Y,
  (X + 1) <= Y < X + Gamma h + 1 ->
  let Hh := (lt_S_n (depth h) d Hd) in
  Implementation_aux (Minimization h) _ Hd ps q n X Y =
    Implementation_aux h _ Hh (shiftin (n+1) ps) n (n+3) (X + 1) Y.
Proof.
intros; simpl.
inversion_clear H.
assert (Y <> X). apply gt_neq; rewrite plus_comm in H0; auto.
unfold RecVar_dec.
apply Rdec.eqb_neq in H. rewrite H.
assert (Y <> X + Gamma h + 1). apply lt_neq; auto.
apply Rdec.eqb_neq in H2. rewrite H2; auto.
Qed.

Lemma Minimization_Procs_1 : forall k (h:PRFunction (S k)) d (Hd:depth (Minimization h) < S d) ps q n X,
  Implementation_aux (Minimization h) _ Hd ps q n X (X + Gamma h + 1) =
    Send (n+1) zero (n+2);; IfEq (n+2) n
            (Send (n+1) this q;; Call (X + Gamma h + 2))
            (Send (n+1) this (n+2);; Send (n+2) succ_this (n+1);; Call (X + 1)).
Proof.
intros; simpl.
assert (X + Gamma h + 1 <> X). apply gt_neq; rewrite <- (plus_comm 1); auto with arith.
unfold RecVar_dec.
apply Rdec.eqb_neq in H. rewrite H.
generalize (eq_refl (X + Gamma h + 1)); intro.
apply Rdec.eqb_eq in H0. rewrite H0; auto.
Qed.

(** ** Parallel implementation
  There is also a parallel variant for composition. This is defined in the same steps, but
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
+ apply (Send (hd ps) this (hd qs);; IHm (tl ps) (tl qs)).
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
    pose (par_compose fs _ H init' (init'+m) init (X+m) (fun m f => Par_Implementation_aux m f d)) as Pfs.
    pose (Par_Implementation_aux _ f _ Hdf (seq_labels init' fs) q (init' + m) (X + k + (vsum (map Gamma' fs)))) as Pf.
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
         Send (init+2) zero (S init);; Call (X + Gamma' f + 1)
      else if (RecVar_dec Y (X + Gamma' f + 1)) then 
         IfEq (S init) ps[@Fin.F1] (Send init this q;; Call (X + Gamma' f + Gamma' g + 3)) (Call (X + Gamma' f + 2))
      else if (RecVar_dec Y (X + Gamma' f + Gamma' g + 2)) then
         Send (init+2) this init;; Send (S init) this (init+2);; Send (init+2) succ_this (S init);; Call (X + Gamma' f + 1)
      else Pg Y).

  (* Minimization *)
  - simpl in Hd; apply lt_S_n in Hd; rename Hd into Hf.
    pose (Par_Implementation_aux _ f _ Hf (shiftin (S init) ps) init (init+3) (X + 1)) as Pf.
    apply (fun Y =>
      if (RecVar_dec Y X) then
         Send (init+2) zero (init+1);; Call (X + 1)
      else if (RecVar_dec Y (X + Gamma' f + 1)) then
         Send (init+1) zero (init+2);; IfEq (init+2) init
           (Send (init+1) this q;; Call (X + Gamma' f + 2))
           (Send (init+1) this (init+2);; Send (init+2) succ_this (init+1);; Call (X + 1))
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

Definition implements (P:Program) {n} (f:PRFunction n) (ps:t Pid n) (q:Pid) :=
  forall (xs:t nat n) (s:State), (forall Hi, s (ps[@Hi]) xx = xs[@Hi]) ->
  (forall y, converges f xs y <-> exists s' ts P', (P,s) --[ts]-->* (P',s') /\ s' q xx = y /\ Main P' = End) /\
  (diverges f xs <-> forall s' ts P', (P,s) --[ts]-->* (P',s') -> Main P' <> End).

(** For convenience. *)
Lemma implements_None : forall P {n} f ps q, implements P f ps q -> 
  forall (xs:t nat n) (s:State), (forall Hi, s (ps[@Hi]) xx = xs[@Hi]) ->
  diverges f xs -> forall s' ts P', (P,s) --[ts]-->* (P',s') -> Main P' <> End.
Proof.
unfold implements; intros.
elim (H _ _ H0); intros.
elim H4; eauto.
Qed.

Lemma implements_Some : forall P {n} f ps q, implements P f ps q -> 
  forall (xs:t nat n) (s:State), (forall Hi, s (ps[@Hi]) xx = xs[@Hi]) ->
  forall y, converges f xs y -> exists s' ts P', (P,s) --[ts]-->* (P',s') /\ s' q xx = y /\ Main P' = End.
Proof.
unfold implements; intros.
elim (H _ _ H0); intros.
elim (H2 y); eauto.
Qed.

(*
Lemma implements_WF : forall {n} (f:PRFunction n) ps q,
  MCP_WF (Implementation f ps q).
Proof.
*)

(* Prove this, and refactor the next result.
Lemma Implementation_aux_input : forall {n} (f:PRFunction n) d Hd ps q i X Defs,
  ~In q ps -> (forall p, In p ps -> p < i) -> q < i ->
  (forall Y, X <= Y < X + Gamma f -> fst (Defs Y) <> List.nil) ->
  (forall Y, X <= Y < X + Gamma f -> snd (Defs Y) = Implementation_aux f d Hd ps q i X Y) ->
  forall s s' tl C,
  (Build_Program Defs (Call X),s) --[tl]-->* (Build_Program Defs C,s')
  -> forall p, p < i -> p <> q -> s' p xx = s p xx.
Proof.
intros n f d; revert n f. induction d. inversion Hd.
intros n f; case f; intros; rename H into Hqps, H0 into Hps, H1 into Hqn, H2 into HDefs, H3 into HDefs'.
+ 
*)

Lemma Implementation_aux_converges : forall {n} (f:PRFunction n) d Hd ps q i X Defs ns y,
  ~In q ps -> (forall p, In p ps -> p < i) -> q < i ->
  (forall Y, X <= Y < X + Gamma f -> fst (Defs Y) <> List.nil) ->
  (forall Y, X <= Y < X + Gamma f -> snd (Defs Y) = Implementation_aux f d Hd ps q i X Y) ->
  converges f ns y -> 
  forall (s:State), (forall H, s ps[@H] xx = ns[@H]) ->
  exists s' tl, s' q xx = y /\ (forall p, p < i -> p <> q -> s' p xx = s p xx) /\
  (Build_Program Defs (Call X),s) --[tl]-->* (Build_Program Defs (Call (X + Gamma f)),s').
Proof.
intros n f d; revert n f. induction d. inversion Hd.
intros n f; case f; intros; rename H into Hqps, H0 into Hps, H1 into Hqn, H2 into HDefs, H3 into HDefs', H4 into Hf, H5 into Hinput.
+ (* Zero *)
  assert (X <= X < X + Gamma Zero). split; auto; rewrite plus_comm; auto with arith.
  generalize (HDefs _ H), (HDefs' _ H).
  simpl; unfold Pack1; simpl.
  rewrite Rdec.eqb_refl. intros HX HX'.
  elim (Call_reduce _ _ s HX); intros tl Htl.
  rewrite HX' in Htl.
  set (s' := update s q xx 0).
  exists s', (tl ++ (L_Com ps[@Fin.F1] 0 q :: List.nil))%list.
  rewrite (converges_Zero _ _ Hf).
  split. apply update_read.
  split. intros; apply update_read'. auto.
  eapply MCT_Trans; eauto.
  replace (L_Com ps[@Fin.F1] 0 q) with (forget (R_Com ps[@Fin.F1] 0 q xx)); auto.
  econstructor; constructor. rewrite plus_comm; simpl. apply C_Com'.
+ (* Successor *)
  set (x := s ps[@Fin.F1] xx).
  assert (X <= X < X + Gamma Zero). split; auto; rewrite plus_comm; auto with arith.
  generalize (HDefs _ H), (HDefs' _ H).
  simpl; unfold Pack1; simpl.
  rewrite Rdec.eqb_refl. intros HX HX'.
  elim (Call_reduce _ _ s HX); intros tl Htl.
  rewrite HX' in Htl.
  set (s' := update s q xx (S x)).
  exists s', (tl ++ (L_Com ps[@Fin.F1] (S x) q :: List.nil))%list.
  rewrite (converges_Successor _ _ Hf).
  split. rewrite <- nth_hd, <- Hinput. apply update_read.
  split. intros; apply update_read'. auto.
  eapply MCT_Trans; eauto.
  replace (L_Com ps[@Fin.F1] (S x) q) with (forget (R_Com ps[@Fin.F1] (S x) q xx)); auto.
  econstructor; constructor. rewrite plus_comm; simpl. apply C_Com'.
+ (* Projection *)
  set (x := s ps[@Fin.of_nat_lt l] xx).
  assert (X <= X < X + Gamma Zero). split; auto; rewrite plus_comm; auto with arith.
  generalize (HDefs _ H), (HDefs' _ H).
  simpl; unfold Pack1; simpl.
  rewrite Rdec.eqb_refl. intros HX HX'.
  elim (Call_reduce _ _ s HX); intros tl Htl.
  rewrite HX' in Htl.
  set (s' := update s q xx x).
  exists s', (tl ++ (L_Com ps[@Fin.of_nat_lt l] x q :: List.nil))%list.
  rewrite (converges_Projection _ _ _ _ _ Hf).
  split. rewrite <- Hinput. apply update_read.
  split. intros; apply update_read'. auto.
  eapply MCT_Trans; eauto.
  replace (L_Com ps[@Fin.of_nat_lt l] x q) with (forget (R_Com ps[@Fin.of_nat_lt l] x q xx)); auto.
  econstructor; constructor. rewrite plus_comm; simpl. apply C_Com'.
+ (* Composition *)
  set (Hd' := lt_S_n (Nat.max (depth g) (vmax (map depth fs))) d Hd).
  set (Hfs := vmax_lt_map _ _ (max_lt_r _ _ _ Hd')).
  set (Hg := max_lt_l _ _ _ Hd').
  elim (converges_Composition _ _ _ _ Hf); clear Hf; intros.
  inversion_clear H. rename x into ms, H0 into H'fs, H1 into H'g.
  (* Here we start directly with the loop *)
  assert (exists sF tlF, (Build_Program Defs (Call X),s) --[tlF]-->* (Build_Program Defs (Call (X + vsum (map Gamma fs))),sF)
    /\ (forall p, p<i -> sF p xx = s p xx)
    /\ forall z H, converges (fs[@H]) ns z -> sF (seq_labels i fs)[@H] xx = z).
  - assert (forall Y, X <= Y < X + vsum (map Gamma fs) -> X <= Y < X + Gamma (Composition g fs)).
    1: {
      intros. inversion_clear H; split; auto.
      simpl. rewrite (plus_comm (Gamma g)).
      etransitivity; eauto.
      rewrite <- plus_0_r at 1. rewrite plus_assoc.
      apply plus_lt_compat_l. apply Gamma_neq_zero.
    }
    generalize (fun Y HY => HDefs Y (H Y HY)).
    clear HDefs; intro HDefs.
    assert (exists k, forall Y, X <= Y < X + vsum (map Gamma fs) ->
      snd (Defs Y) = seq_compose fs _ Hfs ps i (i+m+k) X (fun m f => Implementation_aux f d) Y).
    1: { exists 0; intros. rewrite HDefs'; auto. rewrite Composition_Procs_fs, plus_0_r; auto. }
    clearbody Hd' Hfs.
    clear g H'g H Hd Hd' Hg HDefs'; rename H0 into HDefs'.
    revert dependent X. revert dependent i. revert dependent s.
    induction m.
    * intros. exists s, List.nil.
      rewrite <- (vector_0_inv fs). repeat split; auto.
      simpl. rewrite plus_comm; constructor.
      intros. inversion H.
    * intros.
      revert dependent ms. revert IHm.
      revert dependent fs. revert m. refine (@caseS _ _ _); intros.
      revert dependent t. revert IHm.
      revert dependent ms. revert n0. refine (@caseS _ _ _); intros.
      clear f. rename h into f, t0 into fs, h0 into x, t into xs, n0 into m.
      (* First f... *)
      assert (forall Y, X <= Y < X + Gamma f -> X <= Y < X + vsum (map Gamma (f::fs))).
      1: { intros. inversion_clear H; split; auto. simpl. rewrite plus_assoc; auto with arith. }
      elim HDefs'; clear HDefs'; intros k' HDefs'.
      assert (i < i + S m + k').
      1: { apply lt_le_trans with (i + S m); auto with arith. rewrite <- plus_n_Sm; auto with arith. }
      elim IHd with k f (Hfs Fin.F1) ps i (i + S m + k') X Defs ns x s; auto.
      2: { intro. apply (lt_irrefl i); auto. }
      2: { transitivity i; auto. }
      2: {
        intros.
        rewrite HDefs'; auto.
        simpl. inversion_clear H1.
        apply Nat.ltb_lt in H3; rewrite H3. auto.
      }
      2: { change (converges (hd (f::fs)) ns (hd (x::xs))). repeat rewrite <- nth_hd; auto. }
      intros. destroy H1. rename x0 into sf, x1 into tlf.
      (* ... then the rest. *)
      elim IHm with fs (fun H => Hfs (Fin.FS H)) xs sf (S i) (X + Gamma f); intros.
      2: { change (converges (tl (f::fs))[@H4] ns (tl (x::xs))[@H4]). rewrite <- nth_tl. apply H'fs. }
      2: { assert (ps[@H4] < i). apply Hps; eapply nth_In; eauto.
           rewrite H3; auto. transitivity i; auto. apply lt_neq; auto. }
      2: { apply lt_le_trans with i; auto. }
      2: { apply lt_le_trans with i; auto. }
      2: {
        apply HDefs. simpl. inversion_clear HY; split.
        transitivity (X + Gamma f); auto with arith.
        rewrite plus_assoc; auto.
      }
      2: {
        exists (k' + Pi f); intros.
        inversion_clear H4. rewrite <- plus_assoc in H6.
        rewrite (HDefs' Y). 2: split; auto; transitivity (X + Gamma f); auto with arith.
        simpl. generalize H5; intro.
        apply le_not_lt, Nat.ltb_nlt in H5. rewrite H5.
        replace (i + S m + k' + Pi f) with (S (i + m + (k' + Pi f))); auto.
        repeat rewrite plus_assoc. rewrite <- plus_n_Sm; auto.
      }
      simpl (vsum (map Gamma (f::fs))).
      destroy H4. rename x0 into s', x1 into tl'.
      (* Wheee. *)
      exists s', (tlf ++ tl')%list; repeat split; auto.
      ++ rewrite plus_assoc. eapply MCT_Trans; eauto.
      ++ intros; rewrite H6; auto.
         apply H3. transitivity i; auto.
         apply lt_neq; auto.
      ++ intros. revert H8.
         apply (hd_tl_induction' (fun x y => converges x ns z -> s' y xx = z)); auto.
         simpl; intros. rewrite H6; auto. rewrite (converges_inj _ _ _ _ H8 (H'fs Fin.F1)); auto.
  - destroy H. rename x into sF, x0 into tlF.
    assert (X + Gamma (Composition g fs) = X + vsum (map Gamma fs) + Gamma g) as HX.
    simpl. rewrite (plus_comm (Gamma g)), plus_assoc; auto.
    elim IHd with m g Hg (seq_labels i fs) q (i+m) (X + vsum (map Gamma fs)) Defs ms y sF; auto.
    * intros. destroy H2. rename x into s', x0 into tl'.
      exists s', (tlF++tl')%list; repeat split; auto.
      ++ intros. rewrite H4; auto. apply lt_le_trans with i; auto with arith.
      ++ eapply MCT_Trans; eauto.
         rewrite HX; auto.
    * intro. elim (seq_labels_lt _ _ _ H2); intros.
      elim (lt_irrefl q). apply lt_le_trans with i; auto.
    * intros. elim (seq_labels_lt _ _ _ H2); auto.
    * apply lt_le_trans with i; auto with arith.
    * intros. inversion_clear H2. apply HDefs; split; auto.
      transitivity (X + vsum (map Gamma fs)); auto with arith.
      rewrite HX; auto.
    * intros. inversion_clear H2. rewrite HDefs'.
      rewrite Composition_Procs_g; auto. rewrite HX; auto.
      split; auto. transitivity (X + vsum (map Gamma fs)); auto with arith.
      rewrite HX; auto.
+ (* Recursion *)
  set (Hd' := lt_S_n (Nat.max (depth g) (depth h)) d Hd).
  set (Hg := (max_lt_l _ _ _ Hd')).
  set (Hh := (max_lt_r _ _ _ Hd')).
  assert (forall H, ps[@H] < i) as Hpsi.
  1: { intros. apply Hps. eapply nth_In; auto. }
  (* Setting up for the base case, using the induction hypothesis on g *)
  (* Call X,s -> Call (X + Gamma g),sg sg(ps) = s(ps), sg(init) = f(s(tl ps)) *)
  assert (forall Y, X <= Y < X + Gamma g -> X <= Y < X + (Gamma g + Gamma h + 3)) as H'.
  1: {
    intros. inversion_clear H; split; simpl; auto.
    transitivity (X + Gamma g); auto.
    apply plus_lt_compat_l; auto with arith.
    apply le_lt_trans with (Gamma g + Gamma h); auto with arith.
    rewrite <- (plus_comm 3); simpl; auto.
  }
  assert (forall Y, X <= Y < X + Gamma g -> fst (Defs Y) <> List.nil) as HgDefs. eauto.
  assert (forall Y, X <= Y < X + Gamma g -> snd (Defs Y) = Implementation_aux g _ Hg (tl ps) i (i+3) X Y) as HgDefs'.
  1: {
    intros. elim H; intros. generalize (HDefs' _ (H' _ H)).
    rewrite Recursion_Procs_g; auto.
  }
  assert (~In i (tl ps)) as Hi.
  1: { intro. apply (lt_irrefl i). apply Hps. apply In_tail; auto. }
  assert (i < i+3) as Hi'. rewrite plus_comm; simpl; auto.
  assert (forall p, In p (tl ps) -> p < i+3) as Hpsg.
  1: { intros. transitivity i; auto. apply Hps, In_tail; auto. }
  elim (converges_Recursion_full _ _ _ _ Hf 0); auto with arith.
  intros g0 Hg0.
  assert (forall H, s (tl ps)[@H] xx = (tl ns)[@H]) as Hinput'.
  1: intro; repeat rewrite <- nth_tl; auto.
  elim (IHd _ _ Hg (tl ps) i (i+3) _ _ (tl ns) _ Hi Hpsg Hi' HgDefs HgDefs' Hg0 s Hinput'); intros.
  destroy H.
  rename x into sg, x0 into tlg, H0 into Hsg, H1 into Hsg', H into Htlg.
  clear Hi HgDefs HgDefs' H' Hpsg Hg.
  (* Call X + Gamma g,sg -> Call (X + Gamma g + 1),s' s'(ps) = s(ps), s'(S init) = 0, s'(init) = f(s(tl ps)) *)
  assert (X <= X + Gamma g < X + Gamma (Recursion g h)).
  1: {
    split; auto with arith.
    apply plus_lt_compat_l. simpl. rewrite <- (plus_comm 3).
    transitivity (2 + Gamma g); simpl; auto with arith.
  }
  elim (Call_reduce Defs (X + Gamma g) sg); auto. intros.
  rename x into tlg'.
  rewrite HDefs', Recursion_Procs_0 in H0; auto.
  generalize (C_Com' Defs (i+2) zero (S i) xx (Call (X + Gamma g + 1)) sg); intro.
  simpl in H1. generalize (MCP_To_intro _ _ _ _ _ _ H1).
  clear H1; simpl; intro.
  set (P := Build_Program Defs (Call (X + Gamma g + 1))).
  generalize (MCT_Trans _ _ _ _ _ Htlg (MCT_Trans _ _ _ _ _ H0 (MCT_Step _ _ _ _ _ H1 (MCT_Refl _)))).
  clear H0 H1; fold P; intro HP.
  set (t := (tlg ++ tlg' ++ L_Com (i+2) 0 (S i) :: List.nil)%list).
  set (s0 := update sg (S i) xx 0).
  fold t s0 in HP.
  assert (s0 i xx = g0) as Hs0i. rewrite <- Hsg. apply update_read'; auto.
  assert (s0 (S i) xx = 0) as Hs0Si. apply update_read.
  assert (forall H, s0 ps[@H] xx = ns[@H]) as Hs0.
  1: {
    intros. rewrite <- Hinput, <- Hsg'; auto.
    apply update_read'; auto.
    apply gt_neq; red; transitivity i; auto.
    transitivity i; auto.
    apply lt_neq; auto.
  }
  assert (forall p, p < i -> s0 p xx = s p xx) as Hs0'.
  1: {
    intros; unfold s0; rewrite update_read'.
    apply Hsg'; auto with arith. apply lt_neq; auto.
    apply gt_neq; red; transitivity i; auto.
  }
  clearbody t s0. clear sg Hsg Hsg' Htlg.
  (* Loop invariant *)
  assert (forall m, m <= hd ns -> exists t' s' y', (P,s0) --[ t' ]-->* (P,s')
    /\ converges (Recursion g h) (m::tl ns) y' /\ s' i xx = y' /\ s' (S i) xx = m /\ forall j, j < i -> s' j xx = s0 j xx).
  - induction m; intros.
    * exists List.nil, s0, g0; repeat split; auto. constructor.
    * elim IHm; auto with arith; clear IHm.
      intros tlI H'; destroy H'.
      rename x into sI, x0 into yI, H1 into HI.
      assert (X <= X + Gamma g + 1 < X + Gamma (Recursion g h)).
      1: { split; simpl; auto with arith.  repeat (rewrite <- plus_assoc; apply plus_lt_compat_l); auto with arith. }
      elim (Call_reduce Defs (X + Gamma g + 1) sI); intros; auto.
      rename x into tlU, H5 into HU.
      rewrite HDefs', Recursion_Procs_1 in HU; auto.
      unfold IfEq in HU.
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs ps[@Fin.F1] this (S i) yy (If (S i) ? compare Then Send i this q;; Call (X + Gamma g + Gamma h + 3) Else Call (X + Gamma g + 2)) sI)).
      simpl; intro.
      assert (beval_on_state compare (update sI (S i) yy (sI ps[@Fin.F1] xx)) (S i) = false).
      1: { 
        unfold beval_on_state, beval, MC_BEval.eval.
        rewrite update_read. rewrite update_read''. 2: discriminate.
        rewrite H4. rewrite H'; auto. rewrite Hs0.
        rewrite Nat.eqb_neq. apply lt_neq.
        rewrite nth_hd; auto.
      }
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Else' Defs (S i) compare (Send i this q;; Call (X + Gamma g + Gamma h + 3)) (Call (X + Gamma g + 2)) _ H6)).
      simpl; clear H6; intro.
      assert (X <= X + Gamma g + 2 < X + Gamma (Recursion g h)).
      1: { split; simpl; auto with arith.  repeat (rewrite <- plus_assoc; apply plus_lt_compat_l); auto with arith. }
      set (sU := update sI (S i) yy (sI ps[@Fin.F1] xx)).
      generalize (MCT_Trans _ _ _ _ _ HU (MCT_Step _ _ _ _ _ H5 (MCT_Step _ _ _ _ _ H6 (MCT_Refl _)))).
      clear HU H5 H6; intro.
      (* Setting up for the induction hypothesis on h *)
      assert (i+2 < i+3+Pi g) as Hi''; intros. auto with arith.
      assert (forall p, In p (S i::i::tl ps) -> p < i+3+Pi g) as Hpsh; intros.
      1: { elim (In_elim H6); intro.
        rewrite <- H8. rewrite <- plus_assoc. rewrite plus_comm; simpl.
        rewrite plus_comm; auto with arith.
        elim (In_elim H8); intro.
        rewrite H9; apply le_lt_trans with (p+0); auto with arith.
        transitivity i. apply Hps, In_tail; auto.
        apply le_lt_trans with (i+0); auto with arith.
      }
      assert (~In (i+2) (S i::i::tl ps)) as Hi; intros.
      1: { intro. elim (In_elim H6).
        apply lt_neq. rewrite plus_comm; auto.
        intro; elim (In_elim H8).
        apply lt_neq; rewrite plus_comm; simpl; auto.
        intro. apply (lt_irrefl i).
        transitivity (i+2). rewrite plus_comm; simpl; auto.
        apply Hps, In_tail; auto.
      }
      assert (forall Y, X + Gamma g + 2 <= Y < X + Gamma g + 2 + Gamma h -> X <= Y < X + (Gamma g + Gamma h + 3)) as H''.
      1: {
        intros. inversion_clear H6; split; simpl.
        transitivity (X + Gamma g + 2); auto with arith.
        repeat rewrite <- plus_assoc.
        repeat rewrite <- plus_assoc in H9.
        rewrite (plus_comm 2) in H9.
        etransitivity; eauto.
        repeat apply plus_lt_compat_l; auto with arith.
      }
      assert (forall Y, X + Gamma g + 2 <= Y < X + Gamma g + 2 + Gamma h -> fst (Defs Y) <> List.nil) as HhDefs; auto.
      assert (forall Y, X + Gamma g + 2 <= Y < X + Gamma g + 2 + Gamma h -> snd (Defs Y) = Implementation_aux h d Hh (S i :: i :: tl ps) (i + 2) (i + 3 + Pi g) (X + Gamma g + 2) Y) as HhDefs'; auto.
      1: {
        intros. unfold Hh, Hd'; rewrite <- Recursion_Procs_h with (q:=q); auto.
        replace (X + Gamma g + Gamma h + 2) with (X + Gamma g + 2 + Gamma h); auto.
        repeat rewrite <- plus_assoc. rewrite (plus_comm 2); auto.
      }
      assert (forall H, sU (S i::i::tl ps)[@H] xx = (m::yI::tl ns)[@H]) as Hinput''; intros.
      1: {
        replace (sU (S i::i::tl ps)[@H6] xx) with (map (fun y => sU y xx) (S i::i::tl ps))[@H6].
        2: rewrite (nth_map _ _ _ _ (eq_refl _)); auto.
        apply hd_tl_eq. 2: apply hd_tl_eq.
        * simpl. unfold sU; rewrite update_read''; auto. discriminate.
        * simpl. unfold sU; rewrite update_read'; auto.
        * simpl. intros. rewrite (nth_map _ _ _ _ (eq_refl _)).
          unfold sU; rewrite update_read'; auto.
          repeat rewrite <- nth_tl. rewrite <- Hs0; auto.
          apply gt_neq; red.
          transitivity i; auto. rewrite <- nth_tl; auto.
      }
      elim (converges_Recursion_full _ _ _ _ Hf (S m)); auto; intros.
      elim (converges_Recursion_step _ _ _ m _ H6); simpl; auto. intros.
      inversion_clear H8.
      rewrite (converges_inj _ _ _ _ H9 H2) in H10; clear x0 H9.
      elim (IHd _ _ Hh _ _ _ _ _ _ _ Hi Hpsh Hi'' HhDefs HhDefs' H10 _ Hinput''); intros.
      rename x0 into sF; destroy H8.
      rename x0 into tlF.
      (* After calling h *)
      repeat rewrite <- plus_assoc in H8; rewrite (plus_comm 2) in H8.
      repeat rewrite plus_assoc in H8.
      assert (X <= X + Gamma g + Gamma h + 2 < X + (Gamma g + Gamma h + 3)).
      1: { split; auto with arith.
        repeat rewrite <- plus_assoc; repeat apply plus_lt_compat_l; auto.
      }
      elim (Call_reduce Defs (X + Gamma g + Gamma h + 2) sF); auto; intros.
      rewrite HDefs', Recursion_Procs_2 in H13; auto.
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (i+2) this i xx (Send (S i) this (i+2);; Send (i+2) succ_this (S i);; Call (X + Gamma g + 1)) sF)).
      simpl. set (sF' := update sF i xx (sF (i+2) xx)); intros.
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (S i) this (i+2) xx (Send (i+2) succ_this (S i);; Call (X + Gamma g + 1)) sF')).
      simpl. set (sF'' := update sF' (i+2) xx (sF' (S i) xx)); intros.
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (i+2) succ_this (S i) xx (Call (X + Gamma g + 1)) sF'')).
      simpl. set (sF''' := update sF'' (S i) xx (S (sF'' (i+2) xx))); intros.
      exists (tlI ++ (tlU ++ L_Com ps[@Fin.F1] (sI ps[@Fin.F1] xx) (S i) :: L_Tau (S i) :: List.nil) ++ tlF ++ x0 ++ L_Com (i+2) (sF (i+2) xx) i :: L_Com (S i) (sF' (S i) xx) (i+2) :: L_Com (i+2) (S (sF'' (i+2) xx)) (S i) :: List.nil)%list.
      exists sF''', x. repeat split; auto.
      ++ do 4 (eapply MCT_Trans; eauto).
         do 3 (eapply MCT_Step; eauto).
         constructor.
      ++ unfold sF''', sF'', sF'.
         do 2 (rewrite update_read'; auto).
         rewrite update_read; auto.
         apply gt_neq; rewrite plus_comm; simpl; auto.
      ++ unfold sF''', sF'', sF'.
         rewrite update_read.
         rewrite update_read.
         rewrite update_read'; auto.
         rewrite H11; auto.
         2: {
           rewrite <- plus_assoc; rewrite (plus_comm 3).
           rewrite plus_assoc; rewrite plus_comm.
           simpl; auto with arith.
         }
         2: { apply lt_neq; rewrite plus_comm; auto. }
         unfold sU. rewrite update_read''; auto. discriminate.
      ++ unfold sF''', sF'', sF'; intros.
         rewrite update_read.
         repeat rewrite update_read'.
         rewrite H11; auto with arith.
         unfold sU. rewrite update_read'; auto.
         apply gt_neq; red; transitivity i; auto.
         apply lt_neq; red; transitivity i; auto with arith.
         apply gt_neq; auto.
         apply gt_neq; red; transitivity i; auto. rewrite plus_comm; simpl; auto.
         apply gt_neq; red; transitivity i; auto with arith.
  - elim (H0 _ (le_refl _)); clear H0; intros tl Htl.
    destroy Htl.
    rename x into sF.
    rewrite <- eta in H1.
    rewrite <- (converges_inj _ _ _ _ Hf H1) in H2; clear H1 x0.
    assert (X <= X + Gamma g + 1 < X + Gamma (Recursion g h)).
    1: {
      split; auto with arith.
      simpl. repeat rewrite <- plus_assoc; repeat apply plus_lt_compat_l.
      rewrite plus_comm; auto with arith.
    }
    elim (Call_reduce Defs (X + Gamma g + 1) sF); auto; intros.
    rewrite HDefs', Recursion_Procs_1 in H4; auto.
    rename x into tlU, H4 into HU.
    unfold IfEq in HU.
    generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs ps[@Fin.F1] this (S i) yy (If (S i) ? compare Then Send i this q;; Call (X + Gamma g + Gamma h + 3) Else Call (X + Gamma g + 2)) sF)).
    simpl; intro.
    assert (beval_on_state compare (update sF (S i) yy (sF ps[@Fin.F1] xx)) (S i) = true).
    1: { 
      unfold beval_on_state, beval, MC_BEval.eval.
      rewrite update_read. rewrite update_read''. 2: discriminate.
      rewrite H3. rewrite Htl; auto. rewrite Hs0.
        rewrite Nat.eqb_eq. rewrite nth_hd; auto.
    }
    generalize (MCP_To_intro _ _ _ _ _ _ (C_Then' Defs (S i) compare (Send i this q;; Call (X + Gamma g + Gamma h + 3)) (Call (X + Gamma g + 2)) _ H5)).
    set (sF' := update sF (S i) yy (sF ps[@Fin.F1] xx)).
    simpl; clear H5; intro.
    generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs i this q xx (Call (X + Gamma g + Gamma h + 3)) sF')).
    simpl; set (sF'' := update sF' q xx (sF' i xx)); intro.
    exists sF'', (t ++ tl ++ (tlU ++ L_Com ps[@Fin.F1] (sF ps[@Fin.F1] xx) (S i) :: L_Tau (S i) :: L_Com i (sF' i xx) q :: List.nil))%list.
    repeat split; auto.
    * unfold sF'', sF'. rewrite update_read.
      rewrite update_read'; auto.
    * unfold sF'', sF'. intros; repeat rewrite update_read'; auto.
      2: apply gt_neq; red; transitivity i; auto.
      rewrite Htl; auto.
    * do 3 (eapply MCT_Trans; eauto).
      do 3 (eapply MCT_Step; eauto).
      do 2 rewrite <- (plus_assoc X). constructor.
+ (* Minimization *)
  set (Hd' := lt_S_n (depth h) d Hd).
  assert (forall H, ps[@H] < i) as Hpsi.
  1: { intros. apply Hps. eapply nth_In; auto. }
  assert (S X = X + 1) as HXSX. rewrite plus_comm; auto.
  (* Initialization *)
  assert (X <= X < X + Gamma (Minimization h)).
  1: {
    split; auto with arith.
    apply le_lt_trans with (X + 0); auto with arith.
    apply plus_lt_compat_l; apply Gamma_neq_zero.
  }
  elim (Call_reduce Defs X s); auto. intros tl0 H00.
  rewrite HDefs' in H00; auto.
  rewrite Minimization_Procs_0 in H00.
  generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (i+2) zero (i+1) xx (Call (X+1)) s)).
  simpl. set (s0 := update s (i+1) xx 0); intro.
  (* Setting up for the induction hypothesis on h *)
  assert (forall Y, X + 1 <= Y < X + 1 + Gamma h -> X <= Y < X + (Gamma h + 2)) as H'.
  1: {
    intros. inversion_clear H1; split; simpl.
    transitivity (X + 1); auto with arith.
    transitivity (X + 1 + Gamma h); auto.
    rewrite <- (plus_comm 2), plus_assoc.
    auto with arith.
  }
  assert (forall Y, X + 1 <= Y < X + 1 + Gamma h -> fst (Defs Y) <> List.nil) as HhDefs. eauto.
  assert (forall Y, X + 1 <= Y < X + 1 + Gamma h -> snd (Defs Y) = Implementation_aux h _ Hd' (shiftin (i+1) ps) i (i+3) (X+1) Y) as HhDefs'.
  1: {
    intros. elim H1; intros. generalize (HDefs' _ (H' _ H1)).
    rewrite Minimization_Procs_h; auto.
    split; auto.
    rewrite <- plus_assoc, <- (plus_comm 1), plus_assoc; auto.
  }
  assert (~In i (shiftin (i+1) ps)) as Hi.
  1: {
    intro. apply (lt_irrefl i). elim (shiftin_elim _ _ H1); auto.
    intros; rewrite <- H2 at 2; auto. rewrite plus_comm; auto.
  }
  assert (i < i+3) as Hi'. rewrite plus_comm; simpl; auto.
  assert (forall p, In p (shiftin (i+1) ps) -> p < i+3) as Hpsh.
  1: {
    intros. elim (shiftin_elim _ _ H1); auto.
    intro. rewrite <- H2; simpl; auto with arith.
    transitivity i; auto.
  }
  assert (exists z, converges h (shiftin 0 ns) z).
  1: {
    elim (eq_nat_dec y 0); intros.
    + exists 0. apply converges_Minimization.
      rewrite <- a; auto.
    + elim (converges_Minimization_mon _ _ _ Hf) with 0; eauto.
      apply neq_0_lt; auto.
  }
  inversion_clear H1.
  assert (forall H, s0 (shiftin (i+1) ps)[@H] xx = (shiftin 0 ns)[@H]) as Hinput'.
  1: {
    intro.
    replace (s0 (shiftin (i+1) ps)[@H1] xx) with (map (fun y => s0 y xx) (shiftin (i+1) ps))[@H1]; auto.
    2: rewrite (nth_map _ _ _ _ (eq_refl _)); auto.
    rewrite map_shiftin.
    apply shiftin_eq.
    unfold s0. rewrite plus_comm; apply update_read.
    intro. rewrite nth_map'. unfold s0; rewrite update_read'; auto.
    apply gt_neq; red. transitivity i; auto. rewrite plus_comm; auto.
  }
  elim (IHd _ _ Hd' _ _ _ _ _ _ _ Hi Hpsh Hi' HhDefs HhDefs' H2 _ Hinput'); intros.
  rename x0 into sI; destroy H1.
  rename x0 into tlI, H1 into HI.
  replace (X + 1 + Gamma h) with (X + Gamma h + 1) in HI.
  2: repeat rewrite <- plus_assoc; rewrite <- (plus_comm 1); auto.
  generalize (MCT_Trans _ _ _ _ _ H00 (MCT_Step _ _ _ _ _ H0 HI)).
  set (P := Build_Program Defs (Call (X + Gamma h + 1))).
  clear H0 H00 HI; intro HI.
  assert (X <= X + Gamma h + 1 < X + Gamma (Minimization h)).
  1: { split; simpl; auto with arith. rewrite plus_assoc; auto with arith. }
  (* Loop *)
  assert (forall m, m <= y -> exists t' s' y', (P,sI) --[ t' ]-->* (P,s')
    /\ converges h (shiftin m ns) y' /\ s' i xx = y' /\ s' (i+1) xx = m /\ forall j, j < i -> s' j xx = s0 j xx).
  - induction m; intros.
    * exists List.nil, sI, x; repeat split; auto. constructor.
      rewrite H4; auto with arith. unfold s0. rewrite plus_comm, update_read; auto.
      apply gt_neq. red; rewrite plus_comm; auto.
      intros; apply H4. transitivity i; auto. apply lt_neq; auto.
    * elim IHm; auto with arith; clear IHm.
      intros tlI' H''; destroy H''.
      rename x1 into yI, x0 into sI', H5 into HI'.
      elim (Call_reduce Defs (X + Gamma h + 1) sI'); intros; auto.
      rename x0 into tlU, H5 into HU.
      rewrite HDefs', Minimization_Procs_1 in HU; auto.
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (i+1) zero (i+2) xx (IfEq (i+2) i (Send (i+1) this q;; Call (X + Gamma h + 2)) (Send (i+1) this (i+2);; Send (i+2) succ_this (i+1);; Call (X+1))) sI')).
      simpl. set (s1 := update sI' (i+2) xx 0); intro.
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs i this (i+2) yy (Cond (i+2) compare (Send (i+1) this q;; Call (X + Gamma h + 2)) (Send (i+1) this (i+2);; Send (i+2) succ_this (i+1);; Call (X+1))) s1)).
      simpl. set (s2 := update s1 (i+2) yy (s1 i xx)); intro.
      assert (beval_on_state compare s2 (i+2) = false).
      1: {
        unfold beval_on_state, beval, MC_BEval.eval.
        apply Nat.eqb_neq.
        unfold s2, s1.
        rewrite update_read, update_read''; auto. 2: discriminate.
        rewrite update_read, update_read'.
        rewrite H7.
        elim (converges_Minimization_mon _ _ _ Hf m); auto.
        intros. rewrite (converges_inj _ _ _ _ H6 H10); discriminate.
        apply gt_neq; rewrite plus_comm; simpl; auto.
      }
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Else' Defs _ _ (Send (i+1) this q;; Call (X+Gamma h+2)) (Send (i+1) this (i+2);; Send (i+2) succ_this (i+1);; Call (X+1)) _ H10)).
      simpl; clear H10; intro.
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (i+1) this (i+2) xx (Send (i+2) succ_this (i+1);; Call (X+1)) s2)).
      simpl. set (s3 := update s2 (i+2) xx (s2 (i+1) xx)); intro.
      generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (i+2) succ_this (i+1) xx (Call (X+1)) s3)).
      simpl. set (s4 := update s3 (i+1) xx (S (s3 (i+2) xx))); intro.
      (* IH on H again *)
      assert (exists z, converges h (shiftin (S m) ns) z).
      1: {
        inversion H1; intros.
        + rewrite H13. elim (converges_Minimization _ _ _ Hf); intros.
          exists 0, x0; eauto.
        + elim (converges_Minimization_mon _ _ _ Hf) with (S m); eauto.
          rewrite <- H14; auto with arith.
      }
      inversion_clear H13. rename x0 into x'.
      assert (forall H, s4 (shiftin (i+1) ps)[@H] xx = (shiftin (S m) ns)[@H]) as Hinput''.
      1: {
        intro.
        replace (s4 (shiftin (i+1) ps)[@H13] xx) with (map (fun y => s4 y xx) (shiftin (i+1) ps))[@H13]; auto.
        2: rewrite (nth_map _ _ _ _ (eq_refl _)); auto.
        rewrite map_shiftin.
        apply shiftin_eq.
        + unfold s4, s3, s2, s1.
          repeat rewrite update_read. repeat rewrite update_read'.
          2: apply gt_neq; red; auto with arith.
          2: apply gt_neq; red; auto with arith.
          rewrite <- H8; auto.
        + intro. rewrite nth_map'. unfold s4, s3, s2, s1.
          assert (i+2<>ps[@H15]). apply gt_neq; red; transitivity i; auto. rewrite plus_comm; simpl; auto.
          repeat rewrite update_read'; auto.
          2: apply gt_neq; red; auto with arith.
          rewrite H'', <- Hinput; auto.
          unfold s0. apply update_read'; auto.
          apply gt_neq; red; rewrite plus_comm. transitivity i; auto.
      }
      elim (IHd _ _ Hd' _ _ _ _ _ _ _ Hi Hpsh Hi' HhDefs HhDefs' H14 _ Hinput''); intros.
      rename x0 into sL; destroy H13.
      rename x0 into tlL, H13 into HL.
      replace (X + 1 + Gamma h) with (X + Gamma h + 1) in HL.
      2: repeat rewrite <- plus_assoc; rewrite <- (plus_comm 1); auto.
      fold P in HL, HU.
      eexists; exists sL, x'; repeat split; auto.
      -- do 2 (eapply MCT_Trans; eauto).
         do 5 (eapply MCT_Step; eauto).
      -- rewrite H16; auto with arith. 2: rewrite plus_comm; simpl; auto.
         unfold s4, s3, s2, s1.
         do 2 rewrite update_read. repeat rewrite update_read'.
         2: apply gt_neq; red; auto with arith.
         2: apply gt_neq; red; auto with arith.
         rewrite <- H8; auto.
      -- intros. rewrite H16. 2: transitivity i; auto with arith. 2: apply lt_neq; auto.
         assert (i+2 <> j). apply gt_neq; red; rewrite plus_comm. transitivity i; simpl; auto.
         unfold s4, s3, s2, s1. rewrite <- (plus_comm 1).
         rewrite update_read. repeat rewrite update_read'; auto.
         apply gt_neq; red; transitivity i; auto.
  - elim (H1 y); auto.
    intros tlL HL; destroy HL.
    rename x0 into sL.
    rewrite (converges_inj _ _ _ _ H6 (converges_Minimization _ _ _ Hf)) in H7; clear x1 H6.
    elim (Call_reduce Defs (X + Gamma h + 1) sL); intros; auto.
    rename x0 into tlU, H6 into HU.
    rewrite HDefs', Minimization_Procs_1 in HU; auto.
    generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (i+1) zero (i+2) xx (IfEq (i+2) i (Send (i+1) this q;; Call (X + Gamma h + 2)) (Send (i+1) this (i+2);; Send (i+2) succ_this (i+1);; Call (X+1))) sL)).
    simpl. set (s1 := update sL (i+2) xx 0); intro.
    generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs i this (i+2) yy (Cond (i+2) compare (Send (i+1) this q;; Call (X + Gamma h + 2)) (Send (i+1) this (i+2);; Send (i+2) succ_this (i+1);; Call (X+1))) s1)).
    simpl. set (s2 := update s1 (i+2) yy (s1 i xx)); intro.
    assert (beval_on_state compare s2 (i+2) = true).
    1: {
      unfold beval_on_state, beval, MC_BEval.eval.
      apply Nat.eqb_eq.
      unfold s2, s1.
      rewrite update_read, update_read''; auto. 2: discriminate.
      rewrite update_read, update_read'; auto.
      apply gt_neq; rewrite plus_comm; simpl; auto.
    }
    generalize (MCP_To_intro _ _ _ _ _ _ (C_Then' Defs _ _ (Send (i+1) this q;; Call (X+Gamma h+2)) (Send (i+1) this (i+2);; Send (i+2) succ_this (i+1);; Call (X+1)) _ H10)).
    simpl; clear H10; intro.
    generalize (MCP_To_intro _ _ _ _ _ _ (C_Com' Defs (i+1) this q xx (Call (X+Gamma h+2)) s2)).
    simpl. set (s3 := update s2 q xx (s2 (i+1) xx)); intro.
    exists s3; eexists. repeat split; auto.
    * unfold s3, s2, s1.
      rewrite update_read.
      rewrite update_read'. 2: apply gt_neq; auto with arith.
      rewrite update_read'; auto. apply gt_neq; auto with arith.
    * intros. unfold s3, s2, s1.
      rewrite update_read'; auto.
      rewrite update_read'. 2: apply gt_neq; auto with arith.
      rewrite update_read'. 2: apply gt_neq; auto with arith.
      rewrite HL; auto.
      unfold s0. apply update_read'. apply gt_neq; auto with arith.
    * do 3 (eapply MCT_Trans; eauto).
      do 4 (eapply MCT_Step; eauto).
      rewrite plus_assoc; constructor.
Qed.

(*
Theorem encoding_sound : forall n (f:PRFunction n),
  implements (Implementation' f) f (vec_1_to_n n) 0.
*)

End Soundness.
