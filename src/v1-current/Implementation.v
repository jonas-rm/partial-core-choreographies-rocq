Require Import Common.
Require Export CC.
Require Export Kleene.

Open Scope nat_scope.

(** * Choreography language
  We start by defining the types for the concrete language
  we use for proving Turing completeness. *)

Inductive Expr : Type :=
 | this : Expr
 | zero : Expr
 | succ_this : Expr
.

Lemma Expr_eq_dec : forall (e e' : Expr), { e = e' } + { e <> e' }.
Proof.
decide equality.
Qed.

Inductive BExpr : Type := compare.

Lemma BExpr_eq_dec : forall (e e' : BExpr), { e = e' } + { e <> e' }.
Proof.
decide equality.
Qed.

Definition CC_Expressions := Build_DecType Expr Expr_eq_dec.
Definition Bool_Expressions := Build_DecType BExpr BExpr_eq_dec.

(** The two variables in each process. *)

Definition CC_Nat := Build_DecType nat Nat.eq_dec.

Definition eval (e:Expr) (f:bool -> nat) : nat :=
match e with
 | zero => 0
 | this => f true
 | succ_this => S (f true)
end.

Lemma eval_wd : forall f f', (forall x, f x = f' x) ->
  forall e, eval e f = eval e f'.
Proof. intros. case e; simpl; auto. Qed.

Definition CC_Eval := Build_Eval CC_Expressions Bool CC_Nat CC_Nat eval eval_wd.

Definition beval (b:BExpr) (f:bool -> nat) : bool :=
  (f true =? f false).

Lemma beval_wd : forall f f', (forall x, f x = f' x) ->
  forall b, beval b f = beval b f'.
Proof. intros. case b; simpl. unfold beval; auto. Qed.

Definition CC_BEval := Build_Eval Bool_Expressions Bool CC_Nat Bool beval beval_wd.

Local Open Scope CC_scope.

(** Implementation signature *)

Definition IS := Build_Signature
  CC_Nat Bool CC_Nat CC_Expressions Bool_Expressions
  CC_Nat Unit CC_Eval CC_BEval.

Notation Pid := (pid IS).
Notation RecVar := (recvar IS).
Notation beval_on_state := (eval_on_state CC_BEval).
Notation Update := (@update CC_Nat Bool CC_Nat).

Definition xx : var IS := true.
Definition yy : var IS := false.

(** Restricted conditional. *)

Definition eps := (tt : ann IS).
Definition Send p e q := p # e --> q $ xx.
Definition IfEq (p q:pid IS) C1 C2 :=
  (q#this --> p$yy) @ eps;; If p ?? compare Then C1 Else C2.

Example sanity_check : forall P s,
  (P,Com IS 3 this 2 yy @ eps;; Sel IS 0 1 left @ eps;;
     Cond IS 2 compare (Send 4 succ_this 3 @ eps;; End)
                       (Send 3 zero 2 @ eps;; End),s)
  --[ @TL_Sel (pid IS) (value IS) 0 1 left ]-->
  (P,IfEq 2 3 (Send 4 succ_this 3 @ eps;; End) (Send 3 zero 2@ eps;; End), s).
Proof.
intros.
rewrite <- forget_Sel with (Var:=var IS) (RecVar := recvar IS).
constructor.
apply C_Delay_Eta.
1: simpl. auto with arith.
apply C_Sel'.
Qed.

Open Scope list_scope.

Example CC_ToStar_sanity_check : forall p e q s1 C P, exists s2 v,
  (P,Send p e q @ eps;; Send p zero q @ eps;; C,s1)
  --[ TL_Com p v q :: @TL_Com (pid IS) (value IS) p 0 q :: List.nil ]-->*
  (P,C,s2) /\ s2 [==] (s1[[q,xx => 0]]).
Proof.
intros.
unfold Send.
generalize (C_Com _ P p e q xx eps (p#zero --> q$xx @ eps;;C) s1).
set (C' := p # e --> q $ xx @ eps;; p # zero --> q $ xx @ eps;; C).
simpl. set (s' := s1[[q,xx => (eval_on_state (ev IS) e s1 p)]]). intros.
generalize (C_Com _ P p zero q xx eps C s').
set (C'' := p # zero --> q $ xx @ eps;; C).
fold C'' in H.
simpl. set (s'' := s'[[q,xx => 0]]). intros.
exists s'', (eval_on_state (ev IS) e s1 p); split.
+ eapply CCT_Step.
  1: rewrite <- forget_Com with (RecVar := recvar IS) (x := xx). constructor. apply H. ESEr.
  eapply CCT_Step.
  1: rewrite <- forget_Com with (RecVar := recvar IS) (x := xx). constructor. apply H0. ESEr.
  apply CCT_Refl.
+ unfold s'', s'.
  apply update_update_ext.
Qed.

(** * Extensions of CC
    We require some additional operators on CC for our encoding. *)

Section CC_plus.

Fixpoint Implementation_Choreography (m n:nat) (C:Choreography IS) :=
  match C with
  | End => False
  | Call X => m <= X <= n
  | RT_Call X _ C' => m <= X <= n /\ Implementation_Choreography m n C'
  | Eta @ eps;; C' => Implementation_Choreography m n C'
  | If p ?? b Then C1 Else C2 => Implementation_Choreography m n C1
                              /\ Implementation_Choreography m n C2
end.

Definition Implementation_Program (P:Program IS) (m n:nat) :=
    Main P = @Call IS m /\
    (forall k, m<=k<n -> Implementation_Choreography m n (Procs P k)) /\
    (forall k, (k<m \/ n<=k) -> Procs P m = End).

(** ** Functions Pi and Gamma *)

Fixpoint Pi {m} (f:PRFunction m) : nat :=
  match f with
  | Zero => 0
  | Successor => 0
  | Projection _ => 0
  | @Composition k m g fs => Pi g + vsum (map Pi fs) + m
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

Definition Pack0 (ps:list Pid) (C:Choreography IS) :=
  (fun (X:RecVar) => (ps,@End IS),C).

Definition Pack1 X CX : RecVar -> Choreography IS :=
  (fun (R:RecVar) => if eq_nat_dec R X then CX else End).

End CC_plus.

(** * Definitions
    We have the usual problems with defining implementation: we need information about the size
    of the vector of processes that we only get with an interactive definition. *sigh*
    Even worse, because of composition we need to do induction on the depth of the function... *)

Open Scope vector_scope.

Section Definitions.

Fixpoint all_pids (n:Pid) : set Pid :=
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

(** Some auxiliary results about these functions. *)

Lemma all_pids_In : forall m n, m <= n -> List.In m (all_pids n).
Proof.
induction n; simpl; auto with arith.
intro. inversion_clear H; auto.
Qed.

Lemma In_all_pids : forall m n, List.In m (all_pids n) -> m <= n.
Proof.
induction n; simpl; intros; inversion_clear H; auto; inversion H0; auto.
Qed.

Lemma all_pids_incl : forall (m n:Pid), m <= n -> all_pids m [C] all_pids n.
Proof.
red; red; intros.
apply all_pids_In. transitivity m; auto. apply In_all_pids; auto.
Qed.

(** This function takes care of the first part of the definition of composition.
    Relationship to the arguments in the paper:
    - fs is the vector of functions
    - ps are the (fixed) argument processes
    - target is the output process for the first function to implement
    - init is the label l_i
    - k is the first free procedure definition
*)

Fixpoint seq_compose {m} {k} (fs:t (PRFunction m) k)
  d (Hd:forall i, depth fs[@i] < d) (ps:t Pid m) (target init:nat) (X:RecVar)
  (Implement : forall m' (f:PRFunction m') (Hd:depth f < d) (ps':t Pid m')
               (q' i':nat) (k':RecVar), RecVar -> Choreography IS) {struct fs}
  : RecVar -> Choreography IS.
(*
  match fs with
  | [] => End
  | f :: fs' => Implement m f d (Hd Fin.F1) ps target init  @ eps;; compose_args fs' ps (S target) (init + Pi f) Implement
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

Fixpoint Encoding_rec {m} (f:PRFunction m) d (Hd:depth f<d)
  (ps:t Pid m) (q:Pid) (init:nat) (X:RecVar) {struct d}: RecVar -> Choreography IS.
Proof.
induction d.
+ elim (Nat.nlt_0_r _ Hd).
+ destruct f; intros; revert X0.

  (* Zero *)
  - apply (Pack1 X (Send (hd ps) zero q @ eps;; @Call IS (S X))).

  (* Successor *)
  - apply (Pack1 X (Send (hd ps) succ_this q @ eps;; @Call IS (S X))).

  (* Projection *)
  - apply (Pack1 X (Send ps[@Fin.of_nat_lt l] this q @ eps;; @Call IS (S X))).

  (* Composition *)
  - simpl in Hd; generalize (lt_S_n _ _ Hd); clear Hd; intro Hd'.
    pose (max_lt_l _ _ _ Hd') as Hdf.
    pose (max_lt_r _ _ _ Hd') as Hdfs.
    pose (vmax_lt_map _ _ Hdfs) as H.
    pose (seq_compose fs _ H ps init (init+m) X (fun m f => Encoding_rec m f d)) as Pfs.
    pose (Encoding_rec _ f _ Hdf (seq_labels init fs) q (init + m) (X + (vsum (map Gamma fs)))) as Pf.
    apply (fun Y => if Y <? X + vsum (map Gamma fs) then Pfs Y else Pf Y).

  (* Recursion *)
  - rename f1 into g; rename f2 into h.
    simpl in Hd; generalize (lt_S_n _ _ Hd); clear Hd; intro Hd'.
    pose (max_lt_l _ _ _ Hd') as Hg.
    pose (max_lt_r _ _ _ Hd') as Hh.
    pose (Encoding_rec _ g _ Hg (tl ps) init (init+3) X) as Pg.
    pose (Encoding_rec _ h _ Hh (S init :: init :: tl ps) (init+2) (init+3 + Pi g) (X + Gamma g + 2)) as Ph.
    apply (fun Y =>
      if (Y <? X + Gamma g) then Pg Y
      else if (eq_nat_dec Y (X + Gamma g)) then
         Send (init+2) zero (S init) @ eps;; @Call IS (X + Gamma g + 1)
      else if (eq_nat_dec Y (X + Gamma g + 1)) then 
         IfEq (S init) (hd ps) (Send init this q @ eps;; @Call IS (X + Gamma g + Gamma h + 3)) (@Call IS (X + Gamma g + 2))
      else if (eq_nat_dec Y (X + Gamma g + Gamma h + 2)) then
         Send (init+2) this init @ eps;; Send (S init) this (init+2) @ eps;; Send (init+2) succ_this (S init) @ eps;; @Call IS (X + Gamma g + 1)
      else Ph Y).

  (* Minimization *)
  - simpl in Hd; apply lt_S_n in Hd; rename Hd into Hf.
    pose (Encoding_rec _ f _ Hf (shiftin (init+1) ps) init (init+3) (X + 1)) as Pf.
    apply (fun Y =>
      if (eq_nat_dec Y X) then
         Send (init+2) zero (init+1) @ eps;; @Call IS (X + 1)
      else if (eq_nat_dec Y (X + Gamma f + 1)) then
         Send (init+1) zero (init+2) @ eps;; IfEq (init+2) init
            (Send (init+1) this q @ eps;; @Call IS (X + Gamma f + 2))
            (Send (init+1) this (init+2) @ eps;; Send (init+2) succ_this (init+1) @ eps;; @Call IS (X + 1))
        else Pf Y).
Defined.

(** The definition in the paper uses auxiliary process names distinct from the ps and q,
    numbered from 0. We model this by using auxiliary processes higher than the ps and q. *)

Definition Encoding {m} (f:PRFunction m) (ps:t Pid m) (q:Pid) : Program IS :=
    (fun X => (all_pids ((max q (vmax ps)) + Pi f),
               Encoding_rec f _ (lt_n_Sn (depth f)) ps q (S (max q (vmax ps))) 0 X),
    @Call IS 0).

(** By default, we take process 0 for q and 1..m for the ps. *)

Definition Encoding' {m} (f:PRFunction m) : Program IS :=
  Encoding f (vec_1_to_n m) 0.

(*
Eval compute in (Main (Encoding' (Composition Successor [Zero]))).
Eval compute in (map snd (map ((Procedures _) (Encoding' (Composition Successor [Zero]))) [0;1;2])).

Eval compute in (Main (Encoding' (Composition Zero [Projection aux13]))).
Eval compute in (map snd (map ((Procedures _) (Encoding' (Composition Zero [Projection aux13]))) [0;1;2])).

Eval compute in (Main (Encoding' (Composition (Projection aux22) (Zero :: [Successor])))).
Eval compute in (map snd (map ((Procedures _) (Encoding' (Composition (Projection aux22) (Zero :: [Successor])))) [0;1;2;3])).

Eval compute in (Main (Encoding' PR_add)).
Eval compute in (map snd (map ((Procedures _) (Encoding' PR_add)) [0;1;2;3;4;5;6])).
Eval compute in (map snd (map ((Procedures _) (Encoding' (Composition Successor [Projection aux23]))) [0;1;2])).
*)
End Definitions.

(** Again - since the definitions are interactive, we prove that they behave as expected. *)

Section Soundness.

Lemma Zero_Procs : forall d Hd ps q n X,
  Encoding_rec Zero d Hd ps q n X X = Send (hd ps) zero q @ eps;; @Call IS (S X).
Proof.
intros; induction d. inversion Hd.
simpl. unfold Pack1; simpl.
rewrite Nat_eq; auto.
Qed.

Lemma Successor_Procs : forall d Hd ps q n X,
  Encoding_rec Successor d Hd ps q n X X =
    Send (hd ps) succ_this q @ eps;; @Call IS (S X).
Proof.
intros; induction d. inversion Hd.
simpl. unfold Pack1; simpl.
rewrite Nat_eq; auto.
Qed.

Lemma Projection_Procs : forall k m (Hp:k<m) d Hd ps q n X,
  Encoding_rec (Projection Hp) d Hd ps q n X X =
    Send ps[@Fin.of_nat_lt Hp] this q @ eps;; @Call IS (S X).
Proof.
intros; induction d. inversion Hd.
simpl. unfold Pack1; simpl.
rewrite Nat_eq; auto.
Qed.

Lemma seq_compose_Procs_hd :
  forall m k f (fs:t (PRFunction m) k) d Hd ps q i X Implement Y,
  X <= Y < X + Gamma f ->
  seq_compose (f::fs) d Hd ps q i X Implement Y =
    Implement m f (Hd Fin.F1) ps q i X Y.
Proof.
intros; simpl.
inversion_clear H.
apply Nat.ltb_lt in H1; rewrite H1; auto.
Qed.

Lemma seq_compose_Procs_tl :
  forall m k f (fs:t (PRFunction m) k) d Hd ps q i X Implement Y,
  X + Gamma f <= Y < X + (vsum (map Gamma (f::fs))) ->
  seq_compose (f::fs) d Hd ps q i X Implement Y = 
    seq_compose fs d (fun i => Hd (Fin.FS i)) ps (S q) (i + Pi f) (X + Gamma f) Implement Y.
Proof.
intros; simpl.
inversion_clear H.
apply le_not_lt, Nat.ltb_nlt in H0; rewrite H0; auto.
Qed.

Lemma Composition_Procs_fs :
  forall k m (fs:t (PRFunction k) m) g d (Hd:depth (Composition g fs) < S d)
        ps q n X Y,
  X <= Y < X + (vsum (map Gamma fs)) ->
  let Hd' := (lt_S_n (Nat.max (depth g) (vmax (map depth fs))) d Hd) in
  let Hf := (vmax_lt_map _ _ (max_lt_r _ _ _ Hd')) in
  Encoding_rec (Composition g fs) _ Hd ps q n X Y =
    seq_compose fs _ Hf ps n (n+m) X (fun m f => Encoding_rec f d) Y.
Proof.
intros; simpl.
inversion_clear H.
rewrite <- Nat.ltb_lt in H1. rewrite H1; auto.
Qed.

Lemma Composition_Procs_g :
  forall k m (fs:t (PRFunction k) m) g d (Hd:depth (Composition g fs) < S d)
        ps q n X Y,
  X + (vsum (map Gamma fs)) <= Y < X + Gamma (Composition g fs) ->
  let Hd' := (lt_S_n (Nat.max (depth g) (vmax (map depth fs))) d Hd) in
  let Hg := (max_lt_l _ _ _ Hd') in
  Encoding_rec (Composition g fs) _ Hd ps q n X Y =
    Encoding_rec g _ Hg (seq_labels n fs) q (n + m) (X + (vsum (map Gamma fs))) Y.
Proof.
intros; simpl.
inversion_clear H.
apply le_not_lt, Nat.ltb_nlt in H0. rewrite H0; auto.
Qed.

Lemma Recursion_Procs_g :
  forall k (g:PRFunction k) h d (Hd:depth (Recursion g h) < S d) ps q n X Y,
  X <= Y < X + Gamma g ->
  let Hd' := (lt_S_n (Nat.max (depth g) (depth h)) d Hd) in
  let Hg := (max_lt_l _ _ _ Hd') in
  Encoding_rec (Recursion g h) _ Hd ps q n X Y =
    Encoding_rec _ _ Hg (tl ps) n (n+3) X Y.
Proof.
intros; simpl.
inversion_clear H.
rewrite <- Nat.ltb_lt in H1. rewrite H1; auto.
Qed.

Lemma Recursion_Procs_0 :
  forall k (g:PRFunction k) h d (Hd:depth (Recursion g h) < S d) ps q n X,
  Encoding_rec (Recursion g h) _ Hd ps q n X (X + Gamma g) =
    Send (n + 2) zero (S n) @ eps;; @Call IS (X + Gamma g + 1).
Proof.
intros; simpl.
generalize (lt_irrefl (X+Gamma g)); intro.
rewrite <- Nat.ltb_nlt in H. rewrite H.
rewrite Nat_eq; auto.
Qed.

Lemma Recursion_Procs_1 :
  forall k (g:PRFunction k) h d (Hd:depth (Recursion g h) < S d) ps q n X,
  Encoding_rec (Recursion g h) _ Hd ps q n X (X + Gamma g + 1) =
    IfEq (S n) (hd ps) (Send n this q @ eps;; @Call IS (X + Gamma g + Gamma h + 3))
                       (@Call IS (X + Gamma g + 2)).
Proof.
intros; simpl.
assert (~ X + Gamma g + 1 < X+Gamma g); intros.
+ intro. apply lt_irrefl with (X + Gamma g).
  etransitivity; eauto. rewrite plus_comm in H; auto.
+ rewrite <- Nat.ltb_nlt in H. rewrite H.
  rewrite Nat_neq, Nat_eq; auto.
  apply gt_neq; rewrite plus_comm; auto.
Qed.

Lemma Recursion_Procs_h :
  forall k (g:PRFunction k) h d (Hd:depth (Recursion g h) < S d) ps q n X Y,
  X + Gamma g + 2 <= Y < X + Gamma g + Gamma h + 2 ->
  let Hd' := (lt_S_n (Nat.max (depth g) (depth h)) d Hd) in
  let Hh := (max_lt_r _ _ _ Hd') in
  Encoding_rec (Recursion g h) _ Hd ps q n X Y =
    Encoding_rec _ _ Hh (S n :: n :: tl ps) (n+2) (n+3 + Pi g) (X + Gamma g + 2) Y.
Proof.
intros; simpl.
inversion_clear H.
assert (~ Y < X+Gamma g); intros.
+ intro. apply lt_irrefl with (X + Gamma g).
  apply le_lt_trans with (X + Gamma g + 2); auto with arith.
  apply le_lt_trans with Y; auto.
+ rewrite <- Nat.ltb_nlt in H. rewrite H.
  rewrite Nat_neq, Nat_neq, Nat_neq; auto.
  - apply lt_neq; auto.
  - apply gt_neq.
    apply lt_le_trans with (X + Gamma g + 2); auto with arith.
  - apply gt_neq.
    apply lt_le_trans with (X + Gamma g + 2); auto with arith.
    rewrite <- (plus_comm 2); auto with arith.
Qed.

Lemma Recursion_Procs_2 :
  forall k (g:PRFunction k) h d (Hd:depth (Recursion g h) < S d) ps q n X,
  Encoding_rec (Recursion g h) _ Hd ps q n X (X + Gamma g + Gamma h + 2) =
    Send (n+2) this n @ eps;; Send (S n) this (n+2) @ eps;;
      Send (n+2) succ_this (S n) @ eps;; @Call IS (X + Gamma g + 1).
Proof.
intros; simpl.
assert (~ X + Gamma g + Gamma h + 2 < X+Gamma g); intros.
+ intro. apply lt_irrefl with (X + Gamma g).
  apply le_lt_trans with (X + Gamma g + Gamma h + 2); auto with arith.
+ rewrite <- Nat.ltb_nlt in H. simpl in H; rewrite H.
  rewrite Nat_neq, Nat_neq, Nat_eq; auto.
  - apply gt_neq.
    apply lt_le_trans with (X + Gamma g + 2); auto with arith.
  - apply gt_neq.
    apply lt_le_trans with (X + Gamma g + 2); auto with arith.
    rewrite <- (plus_comm 2); auto with arith.
Qed.

Lemma Minimization_Procs_0 :
  forall k (h:PRFunction (S k)) d (Hd:depth (Minimization h) < S d) ps q n X,
  Encoding_rec (Minimization h) _ Hd ps q n X X =
    Send (n+2) zero (n+1) @ eps;; @Call IS (X + 1).
Proof.
intros; simpl.
rewrite Nat_eq; auto.
Qed.

Lemma Minimization_Procs_h :
  forall k (h:PRFunction (S k)) d (Hd:depth (Minimization h) < S d) ps q n X Y,
  (X + 1) <= Y < X + Gamma h + 1 ->
  let Hh := (lt_S_n (depth h) d Hd) in
  Encoding_rec (Minimization h) _ Hd ps q n X Y =
    Encoding_rec h _ Hh (shiftin (n+1) ps) n (n+3) (X + 1) Y.
Proof.
intros; simpl.
inversion_clear H.
rewrite Nat_neq, Nat_neq; auto.
- apply lt_neq; auto.
- apply gt_neq; rewrite plus_comm in H0; auto.
Qed.

Lemma Minimization_Procs_1 :
  forall k (h:PRFunction (S k)) d (Hd:depth (Minimization h) < S d) ps q n X,
  Encoding_rec (Minimization h) _ Hd ps q n X (X + Gamma h + 1) =
    Send (n+1) zero (n+2) @ eps;; IfEq (n+2) n
      (Send (n+1) this q @ eps;; @Call IS (X + Gamma h + 2))
      (Send (n+1) this (n+2) @ eps;; Send (n+2) succ_this (n+1) @ eps;; @Call IS (X+1)).
Proof.
intros; simpl.
rewrite Nat_neq, Nat_eq; auto.
apply gt_neq; rewrite <- (plus_comm 1); auto with arith.
Qed.

Lemma Encoding_rec_ge : forall {n} (f:PRFunction n) d Hd ps q i X Y,
  Y >= X + Gamma f -> Encoding_rec f d Hd ps q i X Y = End.
Proof.
intros n f d; revert n f. induction d. inversion Hd.
intros n f. case f; intros.
+ simpl in H; red in H. rewrite plus_comm in H.
  simpl. unfold Pack1; simpl.
  rewrite Nat_neq; auto.
  apply gt_neq; auto with arith.
+ simpl in H; red in H. rewrite plus_comm in H.
  simpl. unfold Pack1; simpl.
  rewrite Nat_neq; auto.
  apply gt_neq; auto with arith.
+ simpl in H; red in H. rewrite plus_comm in H.
  simpl. unfold Pack1; simpl.
  rewrite Nat_neq; auto.
  apply gt_neq; auto with arith.
+ red in H.
  simpl.
  assert (Y >= X + vsum (map Gamma fs)). red. transitivity (X + (Gamma (Composition g fs))); simpl; auto with arith.
  apply le_not_lt in H0. rewrite <- Nat.ltb_nlt in H0. rewrite H0.
  apply IHd; rewrite <- plus_assoc, <- (plus_comm (Gamma g)); auto.
+ red in H; simpl.
  assert (Y > X + Gamma g + 1).
  1: { red. apply lt_le_trans with (X + (Gamma (Recursion g h))); simpl; auto.
       repeat (rewrite <- plus_assoc; apply plus_lt_compat_l). rewrite plus_comm. simpl; auto with arith. }
  assert (Y >= X + Gamma g). red; red in H0. transitivity (X + Gamma g + 1); auto with arith.
  apply le_not_lt in H1. rewrite <- Nat.ltb_nlt in H1. rewrite H1.
  rewrite Nat_neq, Nat_neq, Nat_neq; auto.
  - apply IHd; red. transitivity (X + (Gamma (Recursion g h))); auto.
    simpl. repeat rewrite <- plus_assoc; repeat apply plus_le_compat_l.
    rewrite plus_comm; auto with arith.
  - apply gt_neq; simpl in H. red; apply lt_le_trans with (X + Gamma g + Gamma h + 3).
    apply plus_lt_compat_l; auto. rewrite (plus_assoc X) in H; rewrite <- (plus_assoc X); auto.
  - apply gt_neq; auto.
  - apply gt_neq; auto. red. transitivity (X + Gamma g + 1); auto. rewrite <- (plus_comm 1); auto.
+ red in H; simpl.
  rewrite Nat_neq, Nat_neq.
  - apply IHd; red. transitivity (X + (Gamma (Minimization h))); auto.
    simpl. repeat rewrite <- plus_assoc; repeat apply plus_le_compat_l.
    rewrite plus_comm; auto with arith.
  - apply gt_neq; red. apply lt_le_trans with (X + (Gamma (Minimization h))); simpl; auto.
    rewrite <- plus_assoc; apply plus_lt_compat_l. auto with arith.
  - apply gt_neq; red. apply lt_le_trans with (X + Gamma (Minimization h)); auto with arith. 
       rewrite <- plus_0_r at 1. apply plus_lt_compat_l, Gamma_neq_zero.
Qed.

End Soundness.

(** Some auxiliary results about how these functions reduce. *)

Section LargeStepSemantics.

Lemma Zero_reduce : forall Defs (ps: t Pid 1) q X s, exists t,
  (Defs,Send (hd ps) zero q @ eps;; @Call IS X,s) --[t]-->
    (Defs,@Call IS X,s[[q,xx => 0]]).
Proof. intros. eexists; constructor. apply C_Com'. Qed.

Lemma Successor_reduce : forall Defs (ps: t Pid 1) q X s, exists t,
  (Defs,Send (hd ps) succ_this q @ eps;; @Call IS X,s) --[t]-->
    (Defs,@Call IS X, s[[q,xx => S (s (hd ps) xx)]]).
Proof. intros. eexists; constructor. apply C_Com'. Qed.

Lemma Projection_reduce : forall k m (Hp:k<m) Defs ps q X s, exists t,
  (Defs,Send ps[@Fin.of_nat_lt Hp] this q @ eps;; @Call IS X,s) --[t]-->
    (Defs,@Call IS X,s[[q,xx => s ps[@Fin.of_nat_lt Hp] xx]]).
Proof. intros. eexists; constructor. apply C_Com'. Qed.

Lemma Recursion_reduce_0 : forall Defs X n s, exists t,
  (Defs,Send (n + 2) zero (S n) @ eps;; @Call IS X,s) --[t]-->
    (Defs,@Call IS X,s[[S n,xx => 0]]).
Proof. intros. eexists; constructor. apply C_Com'. Qed.

Lemma Recursion_reduce_1_true : forall m Defs X Y n (ps:t Pid (S m)) q s,
  s (S n) xx = s (hd ps) xx -> exists t s',
  (Defs,IfEq (S n) (hd ps) (Send n this q @ eps;; @Call IS X) (@Call IS Y),s)
    --[t]-->* (Defs,@Call IS X,s')
  /\ s' q xx = s n xx /\ forall p, p <> q -> s' p xx = s p xx.
Proof.
intros. unfold IfEq.
generalize (CCP_Base _ _ _ _ _ _ _ (C_Com' IS Defs (hd ps) this (S n) yy eps (Cond IS (S n) compare (Send n this q @ eps;; @Call IS X) (@Call IS Y)) s)).
simpl; intro.
assert (beval_on_state compare (Update s (S n) yy (s (hd ps) xx)) (S n) = true).
1: { unfold beval_on_state; simpl; unfold beval. rewrite update_read, update_read'', Nat.eqb_eq; auto. discriminate. }
unfold Update in H1.
generalize (CCP_Base _ _ _ _ _ _ _ (C_Then' IS Defs (S n) compare (Send n this q @ eps;; @Call IS X) (@Call IS Y) _ H1)).
simpl; intro.
generalize (CCP_Base _ _ _ _ _ _ _ (C_Com' IS Defs n this q xx eps (@Call IS X) (Update s (S n) yy (s (hd ps) xx)))).
simpl; intro.
do 2 eexists; split. 2: split.
+ do 3 (eapply (CCT_Step IS); eauto). apply CCT_Refl.
+ rewrite update_read, update_read'; auto.
+ intros. rewrite update_read', update_read''; auto. discriminate.
Qed.

Lemma Recursion_reduce_1_false : forall m Defs X Y n (ps:t Pid (S m)) q s,
  s (S n) xx <> s (hd ps) xx -> exists t,
  (Defs,IfEq (S n) (hd ps) (Send n this q @ eps;; @Call IS X) (@Call IS Y),s)
    --[t]-->* (Defs,@Call IS Y, Update s (S n) yy (s (hd ps) xx)).
Proof.
intros. unfold IfEq.
generalize (CCP_Base _ _ _ _ _ _ _ (C_Com' IS Defs (hd ps) this (S n) yy eps (Cond IS (S n) compare (Send n this q @ eps;; @Call IS X) (@Call IS Y)) s)).
simpl; intro.
assert (beval_on_state compare (Update s (S n) yy (s (hd ps) xx)) (S n) = false).
1: { unfold beval_on_state; simpl; unfold beval. rewrite update_read, update_read'', Nat.eqb_neq; auto. discriminate. }
generalize (CCP_Base _ _ _ _ _ _ _ (C_Else' IS Defs (S n) compare (Send n this q @ eps;; @Call IS X) (@Call IS Y) _ H1)).
simpl; intro.
eexists. do 2 (eapply (CCT_Step IS); eauto). apply CCT_Refl.
Qed.

Lemma Recursion_reduce_2 : forall Defs X n s, exists t s',
  (Defs,Send (n+2) this n @ eps;; Send (S n) this (n+2) @ eps;;
      Send (n+2) succ_this (S n) @ eps;; @Call IS X,s)
    --[t]-->* (Defs,@Call IS X,s')
    /\ (forall p, p < n -> s' p xx = s p xx) /\ s' n xx = s (n+2) xx
    /\ s' (S n) xx = S (s (S n) xx) /\ s' (n+2) xx = s (S n) xx.
Proof.
intros.
generalize (CCP_Base _ _ _ _ _ _ _ (C_Com' IS Defs (n+2) this n xx eps (Send (S n) this (n+2) @ eps;; Send (n+2) succ_this (S n) @ eps;; @Call IS X) s)).
simpl. set (s1 := Update s n xx (s (n+2) xx)).
fold xx s1; intro.
generalize (CCP_Base _ _ _ _ _ _ _ (C_Com' IS Defs (S n) this (n+2) xx eps (Send (n+2) succ_this (S n) @ eps;; @Call IS X) s1)).
simpl. set (s2 := s1[[n+2,xx => (s1 (S n) xx)]]).
fold xx s2; intro.
generalize (CCP_Base _ _ _ _ _ _ _ (C_Com' IS Defs (n+2) succ_this (S n) xx eps (@Call IS X) s2)).
simpl. set (s3 := s2[[S n,xx => (S (s2 (n+2) xx))]]).
fold xx s3; intro.
do 2 eexists. split. do 3 (eapply (CCT_Step IS); eauto); apply CCT_Refl.
assert (n+2<>n). apply gt_neq; red; rewrite plus_comm; simpl; auto.
unfold s3, s2, s1. repeat split.
+ intros. repeat rewrite update_read'; auto; apply gt_neq; red; auto. rewrite plus_comm; simpl; auto.
+ rewrite update_read, update_read', update_read', update_read; auto.
+ rewrite update_read, update_read, update_read'; auto.
+ rewrite update_read', update_read, update_read'; auto. rewrite plus_comm; simpl; auto.
Qed.

Lemma Minimization_reduce_0 : forall Defs X n s, exists t,
  (Defs,Send (n + 2) zero (n + 1) @ eps;; @Call IS X,s) --[t]-->
  (Defs,@Call IS X,s[[n+1,xx => 0]]).
Proof. intros. eexists; constructor. apply C_Com'. Qed.

Lemma Minimization_reduce_1_true : forall Defs X Y n s q, q < n -> s n xx = 0 ->
  exists t s', (Defs,Send (n+1) zero (n+2) @ eps;; IfEq (n+2) n
     (Send (n+1) this q @ eps;; @Call IS X)
     (Send (n+1) this (n+2) @ eps;; Send (n+2) succ_this (n+1) @ eps;; @Call IS Y),s)
    --[t]-->* (Defs,@Call IS X,s')
  /\ (forall p, p < n -> p <> q -> s' p xx = s p xx) /\ s' q xx = s (n+1) xx
  /\ s' n xx = s n xx /\ s' (n+1) xx = s (n+1) xx /\ s' (n+2) xx = 0.
Proof.
intros. unfold IfEq.
generalize (CCP_Base _ _ _ _ _ _ _ (C_Com' IS Defs (n+1) zero (n+2) xx eps (Com IS n this (n + 2) yy @ eps;; Cond IS (n + 2) compare (Send (n + 1) this q @ eps;; @Call IS X) ((Send (n + 1) this (n + 2) @ eps;; Send (n + 2) succ_this (n + 1) @ eps;; @Call IS Y))) s)).
simpl. set (s1 := Update s (n+2) xx 0).
fold s1; intro.
generalize (CCP_Base _ _ _ _ _ _ _ (C_Com' IS Defs n this (n+2) yy eps (Cond IS (n + 2) compare (Send (n + 1) this q @ eps;; @Call IS X) ((Send (n + 1) this (n + 2) @ eps;; Send (n + 2) succ_this (n + 1) @ eps;; @Call IS Y))) s1)).
simpl. set (s2 := Update s1 (n+2) yy (s1 n xx)).
fold xx s2; intro.
assert (beval_on_state compare s2 (n+2) = true).
1: {
  simpl. unfold beval, s2, s1.
  rewrite update_read, update_read'', update_read, update_read', Nat.eqb_eq; auto.
  rewrite plus_comm; simpl; apply gt_neq; auto. discriminate.
}
generalize (CCP_Base _ _ _ _ _ _ _ (C_Then' IS Defs (n+2) compare (Send (n + 1) this q @ eps;; @Call IS X) (Send (n + 1) this (n + 2) @ eps;; Send (n + 2) succ_this (n + 1) @ eps;; @Call IS Y) s2 H3)).
simpl; intro.
generalize (CCP_Base _ _ _ _ _ _ _ (C_Com' IS Defs (n + 1) this q xx eps (@Call IS X) s2)).
simpl; intro.
do 2 eexists; split. do 4 (eapply (CCT_Step IS); eauto). apply CCT_Refl.
assert (n+2 <> n+1). apply gt_neq; red; do 2 rewrite (plus_comm n); simpl; auto.
assert (n+2 <> n). apply gt_neq; red; rewrite (plus_comm n); simpl; auto.
unfold s2, s1; repeat split.
+ intros. repeat rewrite update_read'; auto. all: apply gt_neq; red; auto; rewrite plus_comm; simpl; auto.
+ rewrite update_read, update_read', update_read'; auto.
+ rewrite update_read', update_read', update_read'; auto. apply lt_neq; auto.
+ rewrite update_read', update_read', update_read'; auto. apply lt_neq; rewrite plus_comm; auto.
+ rewrite update_read', update_read'', update_read; auto. discriminate.
  apply lt_neq; rewrite plus_comm; simpl; auto.
Qed.

Lemma Minimization_reduce_1_false : forall Defs X Y n s q, q < n -> s n xx <> 0 ->
  exists t s', (Defs,Send (n+1) zero (n+2) @ eps;; IfEq (n+2) n
     (Send (n+1) this q @ eps;; @Call IS X)
     (Send (n+1) this (n+2) @ eps;; Send (n+2) succ_this (n+1) @ eps;; @Call IS Y),s)
    --[t]-->* (Defs,@Call IS Y,s')
  /\ (forall p, p < n -> s' p xx = s p xx) /\ s' n xx = s n xx
  /\ s' (n+1) xx = S (s (n+1) xx) /\ s' (n+2) xx = s (n+1) xx.
Proof.
intros. unfold IfEq.
generalize (CCP_Base _ _ _ _ _ _ _ (C_Com' IS Defs (n+1) zero (n+2) xx eps (Com IS n this (n + 2) yy @ eps;; Cond IS (n + 2) compare (Send (n + 1) this q @ eps;; @Call IS X) ((Send (n + 1) this (n + 2) @ eps;; Send (n + 2) succ_this (n + 1) @ eps;; @Call IS Y))) s)).
simpl. set (s1 := Update s (n+2) xx 0).
fold s1; intro.
generalize (CCP_Base _ _ _ _ _ _ _ (C_Com' IS Defs n this (n+2) yy eps (Cond IS (n + 2) compare (Send (n + 1) this q @ eps;; @Call IS X) ((Send (n + 1) this (n + 2) @ eps;; Send (n + 2) succ_this (n + 1) @ eps;; @Call IS Y))) s1)).
simpl. set (s2 := Update s1 (n+2) yy (s1 n xx)).
fold xx s2; intro.
assert (beval_on_state compare s2 (n+2) = false).
1: {
  simpl. unfold beval, s2, s1.
  rewrite update_read, update_read'', update_read, update_read', Nat.eqb_neq; auto.
  rewrite plus_comm; simpl; apply gt_neq; auto. discriminate.
}
generalize (CCP_Base _ _ _ _ _ _ _ (C_Else' IS Defs (n+2) compare (Send (n + 1) this q @ eps;; @Call IS X) (Send (n + 1) this (n + 2) @ eps;; Send (n + 2) succ_this (n + 1) @ eps;; @Call IS Y) s2 H3)).
simpl; intro.
generalize (CCP_Base _ _ _ _ _ _ _ (C_Com' IS Defs (n+1) this (n+2) xx eps (Send (n + 2) succ_this (n + 1) @ eps;; @Call IS Y) s2)).
simpl. set (s3 := s2[[n+2,xx => (s2 (n+1) xx)]]).
fold xx s3; intro.
generalize (CCP_Base _ _ _ _ _ _ _ (C_Com' IS Defs (n+2) succ_this (n+1) xx eps (@Call IS Y) s3)).
simpl; intro.
do 2 eexists; split. do 5 (eapply (CCT_Step IS); eauto). apply CCT_Refl.
assert (n+2 <> n+1). apply gt_neq; red; do 2 rewrite (plus_comm n); simpl; auto.
assert (n+2 <> n). apply gt_neq; red; rewrite (plus_comm n); simpl; auto.
assert (n+1 <> n). apply gt_neq; red; rewrite (plus_comm n); simpl; auto.
unfold s3, s2, s1. repeat split; auto.
+ intros. repeat rewrite update_read'; auto. all: apply gt_neq; red; auto; rewrite plus_comm; simpl; auto.
+ rewrite update_read, update_read', update_read', update_read', update_read'; auto.
+ rewrite update_read, update_read, update_read', update_read'; auto.
+ rewrite update_read, update_read', update_read, update_read'', update_read'; auto. discriminate.
Qed.

End LargeStepSemantics.

(** Without classical logic we can't make [PRFunction]s into functions, so we define
  implementation as a relation. *)

Definition implements (P:Program IS) {n} (f:PRFunction n) (ps:t Pid n) (q:Pid) :=
  forall (xs:t nat n) s, (forall Hi, s (ps[@Hi]) xx = xs[@Hi]) ->
  (forall y, converges f xs y <-> exists s' ts P',
      (P,s) --[ts]-->* (P',s') /\ s' q xx = y /\ Main P' = End) /\
  (diverges f xs <-> forall s' ts P', (P,s) --[ts]-->* (P',s') -> Main P' <> End).

(** For convenience. *)

Lemma implements_None : forall P {n} f ps q, implements P f ps q -> 
  forall (xs:t nat n) s, (forall Hi, s (ps[@Hi]) xx = xs[@Hi]) ->
  diverges f xs -> forall s' ts P', (P,s) --[ts]-->* (P',s') -> Main P' <> End.
Proof.
unfold implements; intros.
elim (H _ _ H0); intros.
elim H4; eauto.
Qed.

Lemma implements_Some : forall P {n} f ps q, implements P f ps q -> 
  forall (xs:t nat n) s, (forall Hi, s (ps[@Hi]) xx = xs[@Hi]) ->
  forall y, converges f xs y -> exists s' ts P',
    (P,s) --[ts]-->* (P',s') /\ s' q xx = y /\ Main P' = End.
Proof.
unfold implements; intros.
elim (H _ _ H0); intros.
elim (H2 y); eauto.
Qed.

Lemma implements_char (P:Program IS) {n} (f:PRFunction n) (ps:t Pid n) (q:Pid) :
  (forall (xs:t nat n) s, (forall Hi, s (ps[@Hi]) xx = xs[@Hi]) ->
  (forall y, converges f xs y <-> exists s' ts P',
      (P,s) --[ts]-->* (P',s') /\ s' q xx = y /\ Main P' = End))
  -> implements P f ps q.
Proof.
red; intros.
split; auto.
split; intros.
+ elim (H xs s H0 (s' q xx)); intros.
  intro. clear H3.
  elim H4. 2: exists s', ts, P'; auto.
  intro. rewrite H1. discriminate.
+ red; intro.
  case_eq (Kleene.eval f steps xs); auto.
  intros. exfalso.
  elim (H _ _ H0 n0); intros.
  clear H4. elim H3. 2: exists steps; auto.
  intros. destroy H4. apply (H1 x x0 x1); auto.
Qed.

Lemma Encoding_rec_converges :
  forall {n} (f:PRFunction n) d Hd ps q i X (Defs:DefSet IS) ns y,
  ~In q ps -> (forall p, In p ps -> p < i) -> q < i ->
  (forall Y, X <= Y < X + Gamma f -> fst (Defs Y) <> List.nil) ->
  (forall Y, X <= Y < X + Gamma f -> snd (Defs Y) = Encoding_rec f d Hd ps q i X Y) ->
  converges f ns y -> 
  forall s, (forall H, s ps[@H] xx = ns[@H]) ->
  exists tl s', (Defs,@Call IS X,s) --[tl]-->* (Defs,@Call IS (X + Gamma f),s')
  /\ s' q xx = y /\ (forall p, p < i -> p <> q -> s' p xx = s p xx).
Proof.
intros n f d; revert n f. induction d. inversion Hd.
intros n f; case f; intros; rename H into Hqps, H0 into Hps, H1 into Hqn, H2 into HDefs, H3 into HDefs', H4 into Hf, H5 into Hinput.
+ (* Zero *)
  assert (X <= X < X + Gamma Zero). split; auto; rewrite plus_comm; auto with arith.
  generalize (HDefs _ H), (HDefs' _ H).
  simpl; unfold Pack1; simpl.
  rewrite Nat_eq. intros HX HX'.
  elim (Call_reduce IS _ _ HX); intros tl Htl.
  simpl in Htl; rewrite HX' in Htl.
  elim (Zero_reduce Defs ps q (S X) s); intros tl' Htl'.
  do 2 eexists.
  split. eapply CCT_Trans; eauto. econstructor; eauto. rewrite plus_comm; apply CCT_Refl.
  split. rewrite (converges_Zero _ _ Hf).
  rewrite update_read; auto.
  intros; rewrite update_read'; auto.
+ (* Successor *)
  set (x := s (hd ps) xx).
  assert (X <= X < X + Gamma Successor). split; auto; rewrite plus_comm; auto with arith.
  generalize (HDefs _ H), (HDefs' _ H).
  simpl; unfold Pack1; simpl.
  rewrite Nat_eq. intros HX HX'.
  elim (Call_reduce IS _ _ HX); intros tl Htl.
  simpl in Htl; rewrite HX' in Htl.
  elim (Successor_reduce Defs ps q (S X) s); intros tl' Htl'.
  do 2 eexists.
  split. eapply CCT_Trans; eauto. econstructor; eauto. rewrite plus_comm; apply CCT_Refl.
  split. rewrite (converges_Successor _ _ Hf).
  rewrite <- nth_hd, Hinput, nth_hd, update_read; auto.
  intros; rewrite update_read'; auto.
+ (* Projection *)
  assert (X <= X < X + Gamma (Projection l)). split; auto; rewrite plus_comm; auto with arith.
  generalize (HDefs _ H), (HDefs' _ H).
  simpl; unfold Pack1; simpl.
  rewrite Nat_eq. intros HX HX'.
  elim (Call_reduce IS _ _ HX); intros tl Htl.
  simpl in Htl; rewrite HX' in Htl.
  elim (Projection_reduce _ _ l Defs ps q (S X) s); intro tl'.
  do 2 eexists.
  split. eapply CCT_Trans; eauto. econstructor; eauto. rewrite plus_comm; apply CCT_Refl.
  split. rewrite (converges_Projection _ _ _ _ _ Hf).
  rewrite <- Hinput, update_read; auto.
  intros; rewrite update_read'; auto.
+ (* Composition *)
  set (Hd' := lt_S_n (Nat.max (depth g) (vmax (map depth fs))) d Hd).
  set (Hfs := vmax_lt_map _ _ (max_lt_r _ _ _ Hd')).
  set (Hg := max_lt_l _ _ _ Hd').
  elim (converges_Composition _ _ _ _ Hf); clear Hf; intros.
  inversion_clear H. rename x into ms, H0 into H'fs, H1 into H'g.
  (* Here we start directly with the loop *)
  assert (exists tlF sF, (Defs,@Call IS X,s) --[tlF]-->* (Defs,@Call IS (X + vsum (map Gamma fs)),sF)
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
      snd (Defs Y) = seq_compose fs _ Hfs ps i (i+m+k) X (fun m f => Encoding_rec f d) Y).
    1: { exists 0; intros. rewrite HDefs'; auto. rewrite Composition_Procs_fs, plus_0_r; auto. }
    clearbody Hd' Hfs.
    clear g H'g H Hd Hd' Hg HDefs'; rename H0 into HDefs'.
    revert dependent X. revert dependent i. revert dependent s.
    induction m.
    * intros. exists List.nil, s.
      rewrite <- (vector_0_inv fs). repeat split; auto.
      simpl. rewrite plus_comm; apply CCT_Refl.
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
      intros. destroy H1. rename x1 into sf, x0 into tlf.
      (* ... then the rest. *)
      elim IHm with fs (fun H => Hfs (Fin.FS H)) xs sf (S i) (X + Gamma f); intros.
      2: { change (converges (tl (f::fs))[@H4] ns (tl (x::xs))[@H4]). rewrite <- nth_tl. apply H'fs. }
      2: { assert (ps[@H4] < i). apply Hps; eapply nth_In; eauto.
           rewrite H1; auto. transitivity i; auto. apply lt_neq; auto. }
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
      destroy H4. rename x1 into s', x0 into tl'.
      (* Wheee. *)
      exists (tlf ++ tl')%list, s'; repeat split; auto.
      ++ rewrite plus_assoc. eapply CCT_Trans; eauto.
      ++ intros; rewrite H6; auto.
         apply H1. transitivity i; auto.
         apply lt_neq; auto.
      ++ intros. revert H8.
         apply (hd_tl_induction' (fun x y => converges x ns z -> s' y xx = z)); auto.
         simpl; intros. rewrite H6; auto. rewrite (converges_inj _ _ _ _ H8 (H'fs Fin.F1)); auto.
  - destroy H. rename x0 into sF, x into tlF.
    assert (X + Gamma (Composition g fs) = X + vsum (map Gamma fs) + Gamma g) as HX.
    simpl. rewrite (plus_comm (Gamma g)), plus_assoc; auto.
    elim IHd with m g Hg (seq_labels i fs) q (i+m) (X + vsum (map Gamma fs)) Defs ms y sF; auto.
    * intros. destroy H2. rename x0 into s', x into tl'.
      exists (tlF++tl')%list, s'; repeat split; auto.
      ++ eapply CCT_Trans; eauto. rewrite HX; auto.
      ++ intros. rewrite H2; auto. apply lt_le_trans with i; auto with arith.
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
  (* @Call IS X,s -> @Call IS (X + Gamma g),sg sg(ps) = s(ps), sg(init) = f(s(tl ps)) *)
  assert (forall Y, X <= Y < X + Gamma g -> X <= Y < X + (Gamma g + Gamma h + 3)) as H'.
  1: {
    intros. inversion_clear H; split; simpl; auto.
    transitivity (X + Gamma g); auto.
    apply plus_lt_compat_l; auto with arith.
    apply le_lt_trans with (Gamma g + Gamma h); auto with arith.
    rewrite <- (plus_comm 3); simpl; auto.
  }
  assert (forall Y, X <= Y < X + Gamma g -> fst (Defs Y) <> List.nil) as HgDefs. eauto.
  assert (forall Y, X <= Y < X + Gamma g -> snd (Defs Y) = Encoding_rec g _ Hg (tl ps) i (i+3) X Y) as HgDefs'.
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
  rename x0 into sg, x into tlg, H into Hsg', H1 into Hsg, H0 into Htlg.
  clear Hi HgDefs HgDefs' H' Hpsg Hg.
  (* @Call IS X + Gamma g,sg -> @Call IS (X + Gamma g + 1),s' s'(ps) = s(ps), s'(S init) = 0, s'(init) = f(s(tl ps)) *)
  assert (X <= X + Gamma g < X + Gamma (Recursion g h)).
  1: {
    split; auto with arith.
    apply plus_lt_compat_l. simpl. rewrite <- (plus_comm 3).
    transitivity (2 + Gamma g); simpl; auto with arith.
  }
  elim (Call_reduce IS Defs (X + Gamma g)); auto. intros.
  rename x into tlg'.
  rewrite HDefs', Recursion_Procs_0 in H0; auto.
  elim (Recursion_reduce_0 Defs (X + Gamma g + 1) i sg); intros tl0 Htl0.
  set (P := (Defs,@Call IS (X + Gamma g + 1))).
  generalize (CCT_Trans _ _ _ _ _ _ Htlg (CCT_Trans _ _ _ _ _ _ (H0 sg) (CCT_Step _ _ _ _ _ _ Htl0 (CCT_Refl _ _)))).
  clear H0 Htl0; fold P; intro HP.
  set (t := (tlg ++ tlg' ++ tl0 :: List.nil)%list).
  set (s0 := sg[[S i,xx => 0]]).
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
    * exists List.nil, s0, g0; repeat split; auto. apply CCT_Refl.
    * elim IHm; auto with arith; clear IHm.
      intros tlI H'; destroy H'.
      rename x into sI, x0 into yI, H1 into HI.
      assert (X <= X + Gamma g + 1 < X + Gamma (Recursion g h)).
      1: { split; simpl; auto with arith.  repeat (rewrite <- plus_assoc; apply plus_lt_compat_l); auto with arith. }
      elim (Call_reduce IS Defs (X + Gamma g + 1)); intros; auto.
      rename x into tlU, H5 into HU.
      rewrite HDefs', Recursion_Procs_1 in HU; auto.
      assert (sI (S i) xx <> sI (hd ps) xx).
      1: { rewrite H4, <- nth_hd, H', Hs0, nth_hd; auto. apply lt_neq; auto. }
      elim (Recursion_reduce_1_false _ Defs (X + Gamma g + Gamma h + 3) (X + Gamma g + 2) i ps q sI H5).
      intros tl1 Htl1.
      generalize (CCT_Trans _ _ _ _ _ _ (HU sI) Htl1).
      set (sU := sI[[S i,yy => (sI (@hd Pid _ ps) xx)]]).
      clear HU H5 Htl1; intro.
      (* Setting up for the induction hypothesis on h *)
      assert (i+2 < i+3+Pi g) as Hi''; intros. auto with arith.
      assert (forall p, In p (S i::i::tl ps) -> p < i+3+Pi g) as Hpsh; intros.
      1: { elim (In_elim H6); intro.
        rewrite <- H7. rewrite <- plus_assoc. rewrite plus_comm; simpl.
        rewrite plus_comm; auto with arith.
        elim (In_elim H7); intro.
        rewrite H8; apply le_lt_trans with (p+0); auto with arith.
        transitivity i. apply Hps, In_tail; auto.
        apply le_lt_trans with (i+0); auto with arith.
      }
      assert (~In (i+2) (S i::i::tl ps)) as Hi; intros.
      1: { intro. elim (In_elim H6).
        apply lt_neq. rewrite plus_comm; auto.
        intro; elim (In_elim H7).
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
        repeat rewrite <- plus_assoc in H8.
        rewrite (plus_comm 2) in H8.
        etransitivity; eauto.
        repeat apply plus_lt_compat_l; auto with arith.
      }
      assert (forall Y, X + Gamma g + 2 <= Y < X + Gamma g + 2 + Gamma h -> fst (Defs Y) <> List.nil) as HhDefs; auto.
      assert (forall Y, X + Gamma g + 2 <= Y < X + Gamma g + 2 + Gamma h -> snd (Defs Y) = Encoding_rec h d Hh (S i :: i :: tl ps) (i + 2) (i + 3 + Pi g) (X + Gamma g + 2) Y) as HhDefs'; auto.
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
      inversion_clear H7.
      rewrite (converges_inj _ _ _ _ H8 H2) in H9; clear x0 H8.
      elim (IHd _ _ Hh _ _ _ _ _ _ _ Hi Hpsh Hi'' HhDefs HhDefs' H9 _ Hinput''); intros.
      rename x0 into tlF; destroy H7. rename x0 into sF.
      (* After calling h *)
      repeat rewrite <- plus_assoc in H8; rewrite (plus_comm 2) in H8.
      repeat rewrite plus_assoc in H8.
      assert (X <= X + Gamma g + Gamma h + 2 < X + (Gamma g + Gamma h + 3)).
      1: { split; auto with arith.
        repeat rewrite <- plus_assoc; repeat apply plus_lt_compat_l; auto.
      }
      elim (Call_reduce IS Defs (X + Gamma g + Gamma h + 2)); auto; intros.
      rewrite HDefs', Recursion_Procs_2 in H12; auto.
      elim (Recursion_reduce_2 Defs (X+Gamma g+1) i sF).
      intros tl2 Htl2; destroy Htl2. rename x1 into s2.
      exists (tlI ++ (tlU ++ tl1) ++ tlF ++ x0 ++ tl2)%list, s2, x. repeat split; auto.
      ++ do 4 (eapply CCT_Trans; eauto).
      ++ etransitivity; eauto.
      ++ rewrite H16, H7. generalize (Hinput'' (Fin.F1)); auto.
         rewrite <- plus_assoc; rewrite (plus_comm 3).
         rewrite plus_assoc; rewrite plus_comm.
         simpl; auto with arith.
         apply lt_neq; rewrite plus_comm; auto.
      ++ intros. rewrite H14, H7; auto.
         unfold sU. rewrite update_read''; auto. discriminate.
         transitivity i; auto.
         rewrite <- plus_assoc, plus_comm; simpl; rewrite plus_comm; auto with arith.
         apply lt_neq; red; transitivity i; auto with arith.
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
    elim (Call_reduce IS Defs (X + Gamma g + 1)); auto; intros.
    rewrite HDefs', Recursion_Procs_1 in H4; auto.
    rename x into tlU, H4 into HU.
    assert (sF (S i) xx = sF (hd ps) xx).
    1: { rewrite H3, <- nth_hd, <- Hs0, <- nth_hd, Htl; auto. }
    elim (Recursion_reduce_1_true _ Defs (X + Gamma g + Gamma h + 3) (X + Gamma g + 2) i ps q sF H4).
    intros. destroy H5. rename x into tl1, x0 into s1, H6 into Htl1.
    generalize (CCT_Trans _ _ _ _ _ _ (HU sF) Htl1).
    clear HU Htl1; intro.
    exists (t ++ tl ++ (tlU ++ tl1))%list, s1.
    repeat split; auto.
    * simpl; repeat rewrite plus_assoc.
      do 3 (eapply CCT_Trans; eauto).
    * transitivity (sF i xx); auto.
    * intros. rewrite H5, Htl; auto.
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
  elim (Call_reduce IS Defs X); auto. intros tl0 H00.
  rewrite HDefs' in H00; auto.
  rewrite Minimization_Procs_0 in H00.
  elim (Minimization_reduce_0 Defs (X+1) i s); intro tl0'.
  set (s0 := Update s (i+1) xx 0); intro.
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
  assert (forall Y, X + 1 <= Y < X + 1 + Gamma h -> snd (Defs Y) = Encoding_rec h _ Hd' (shiftin (i+1) ps) i (i+3) (X+1) Y) as HhDefs'.
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
  rename x0 into tlI; destroy H1. rename x0 into sI, H3 into HI, H4 into H3, H1 into H4.
  replace (X + 1 + Gamma h) with (X + Gamma h + 1) in HI.
  2: repeat rewrite <- plus_assoc; rewrite <- (plus_comm 1); auto.
  generalize (CCT_Trans _ _ _ _ _ _ (H00 s) (CCT_Step _ _ _ _ _ _ H0 HI)).
  set (P := (Defs,@Call IS (X + Gamma h + 1))).
  clear H0 H00 HI; intro HI.
  assert (X <= X + Gamma h + 1 < X + Gamma (Minimization h)).
  1: { split; simpl; auto with arith. rewrite plus_assoc; auto with arith. }
  (* Loop *)
  assert (forall m, m <= y -> exists t' s' y', (P,sI) --[ t' ]-->* (P,s')
    /\ converges h (shiftin m ns) y' /\ s' i xx = y' /\ s' (i+1) xx = m /\ forall j, j < i -> s' j xx = s0 j xx).
  - induction m; intros.
    * exists List.nil, sI, x; repeat split; auto. apply CCT_Refl.
      rewrite H4; auto with arith. unfold s0. rewrite plus_comm, update_read; auto.
      apply gt_neq. red; rewrite plus_comm; auto.
      intros; apply H4. transitivity i; auto. apply lt_neq; auto.
    * elim IHm; auto with arith; clear IHm.
      intros tlI' H''; destroy H''.
      rename x1 into yI, x0 into sI', H5 into HI'.
      elim (Call_reduce IS Defs (X + Gamma h + 1)); intros; auto.
      rename x0 into tlU, H5 into HU.
      rewrite HDefs', Minimization_Procs_1 in HU; auto.
      assert (sI' i xx <> 0). 
      1: {
        rewrite H7.
        elim (converges_Minimization_mon _ _ _ Hf m); auto.
        intros. rewrite <- (converges_inj _ _ _ _ H5 H6); discriminate.
      }
      elim (Minimization_reduce_1_false Defs (X + Gamma h + 2) (X + 1) i sI' q); auto.
      intros. destroy H9. rename x0 into tl4, x1 into s4. rename H13 into H12'.
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
        + rewrite H12', H8; auto.
        + intro. rewrite nth_map', H11, H'', <- Hinput; auto.
          unfold s0. apply update_read'; auto.
          apply gt_neq; red; rewrite plus_comm. transitivity i; auto.
      }
      elim (IHd _ _ Hd' _ _ _ _ _ _ _ Hi Hpsh Hi' HhDefs HhDefs' H14 _ Hinput''); intros.
      rename x0 into tlL; destroy H13.
      rename x0 into sL, H15 into HL.
      replace (X + 1 + Gamma h) with (X + Gamma h + 1) in HL.
      2: repeat rewrite <- plus_assoc; rewrite <- (plus_comm 1); auto.
      fold P in HL, HU.
      exists (tlI' ++ tlU ++ tl4 ++ tlL)%list, sL, x'; repeat split; auto.
      -- do 3 (eapply CCT_Trans; eauto).
      -- rewrite H13, H12', H8; auto with arith.
         apply gt_neq; red; rewrite plus_comm; auto.
      -- intros. rewrite H13, H11; auto.
         transitivity i; auto. apply lt_neq; auto.
  - elim (H1 y); auto.
    intros tlL HL; destroy HL.
    rename x0 into sL.
    rewrite (converges_inj _ _ _ _ H6 (converges_Minimization _ _ _ Hf)) in H7; clear x1 H6.
    elim (Call_reduce IS Defs (X + Gamma h + 1)); intros; auto.
    rename x0 into tlU, H6 into HU.
    rewrite HDefs', Minimization_Procs_1 in HU; auto.
    elim (Minimization_reduce_1_true Defs (X + Gamma h + 2) (X + 1) i sL q); auto.
    intros. destroy H6. rename x0 into tl3, x1 into s3.
    repeat rewrite <- plus_assoc in H9; simpl in H9.
    exists ((tl0 ++ tl0' :: tlI) ++ tlL ++ tlU ++ tl3)%list, s3.
    repeat split; auto.
    * do 3 (eapply CCT_Trans; eauto). repeat rewrite <- plus_assoc; auto.
    * transitivity (sL (i+1) xx); auto.
    * intros. rewrite H10, HL; auto.
      unfold s0. apply update_read'. apply gt_neq; auto with arith.
Qed.

Theorem Encoding_converges : forall {n} (f:PRFunction n) ps q ns y,
  ~In q ps -> converges f ns y -> forall s, (forall H, s ps[@H] xx = ns[@H]) ->
  exists c' tl, (Encoding f ps q, s) --[tl]-->* c' /\ Main (fst c') = End /\ snd c' q xx = y.
Proof.
intros.
set (Hd := Nat.lt_succ_diag_r (depth f)).
set (i := (S (max q (vmax ps)))).
elim (Encoding_rec_converges f _ Hd ps q i 0 (Procedures IS (Encoding f ps q)) ns y H) with s; intros; auto.
+ destroy H2. rename x0 into s', x into tl.
  simpl (0 + Gamma f) in H2.
  elim (Call_reduce _ (Procedures IS (Encoding f ps q)) (Gamma f)); intros.
  2: apply all_pids_not_nil.
  rename x into tl'.
  eexists. exists (tl++tl')%list; repeat split.
  * eapply CCT_Trans; eauto.
  * change (snd (Procedures IS (Encoding f ps q) (Gamma f)) = End).
    apply Encoding_rec_ge; auto with arith.
  * auto.
+ apply le_n_S. transitivity (vmax ps). apply vmax_In; auto. apply Nat.le_max_r.
+ apply le_n_S. apply Nat.le_max_l.
+ apply all_pids_not_nil.
Qed.

Lemma Encoding_rec_End : forall {n} (f:PRFunction n) d Hd ps q i X (Defs:DefSet IS),
  (forall Y, X <= Y < X + Gamma f -> fst (Defs Y) <> List.nil) ->
  (forall Y, X <= Y < X + Gamma f -> snd (Defs Y) = Encoding_rec f d Hd ps q i X Y) ->
  (forall p, In p ps -> p < i) -> q < i -> ~In q ps ->
  forall ns s, (forall H, s ps[@H] xx = ns[@H]) ->
  forall t s', (Defs,@Call IS X,s) --[t]-->* (Defs,End,s')
  -> exists t' s'', (Defs,@Call IS X,s) --[t']-->* (Defs,@Call IS (X + Gamma f),s'')
  /\ (forall p, p < i -> p <> q -> s p xx = s'' p xx) /\ converges f ns (s'' q xx).
Proof.
intros n f d; revert n f. induction d. inversion Hd.
intros n f; case f; intros; rename H into HDefs, H0 into HDefs', H1 into Hps, H2 into Hq, H3 into Hq', H4 into Hinput, H5 into Htl.
+ (* Zero *)
  assert (X <= X < X + Gamma Zero). split; auto; rewrite plus_comm; auto with arith.
  generalize (HDefs _ H), (HDefs' _ H).
  simpl; unfold Pack1; simpl.
  rewrite Nat_eq. intros HX HX'.
  elim (Call_reduce IS _ _ HX); intros tl' Htl'.
  simpl in Htl'; rewrite HX' in Htl'.
  elim (Zero_reduce Defs ps q (S X) s).
  set (s'' := s[[q,xx => 0]]); intros tl0 H0.
  generalize (CCT_Trans _ _ _ _ _ _ (Htl' s) (CCT_Step _ _ _ _ _ _ H0 (CCT_Refl _ _))); intros.
  exists (tl' ++ tl0 :: List.nil)%list, s''; repeat split.
  - eapply CCT_Trans; eauto. eapply CCT_Step; eauto. rewrite plus_comm; apply CCT_Refl.
  - intros. unfold s''. rewrite update_read'; auto.
  - exists 0. unfold s'', Kleene.eval; simpl. rewrite update_read, hd_map; auto.
+ (* Successor *)
  set (x := s (hd ps) xx).
  assert (X <= X < X + Gamma Successor). split; auto; rewrite plus_comm; auto with arith.
  generalize (HDefs _ H), (HDefs' _ H).
  simpl; unfold Pack1; simpl.
  rewrite Nat_eq. intros HX HX'.
  elim (Call_reduce IS _ _ HX); intros tl' Htl'.
  simpl in Htl'; rewrite HX' in Htl'.
  elim (Successor_reduce Defs ps q (S X) s).
  fold x; set (s'' := Update s q xx (S x)); intros tl0 H0.
  exists (tl' ++ tl0 :: List.nil)%list, s''; repeat split.
  - eapply CCT_Trans; eauto. eapply CCT_Step; eauto. rewrite plus_comm; apply CCT_Refl.
  - intros. unfold s''. rewrite update_read'; auto.
  - exists 0. unfold s'', Kleene.eval, x; simpl.
    rewrite update_read, hd_map, <- nth_hd, <- Hinput, nth_hd, plus_comm; auto.
+ (* Projection *)
  set (x := s ps[@Fin.of_nat_lt l] xx).
  assert (X <= X < X + Gamma (Projection l)). split; auto; rewrite plus_comm; auto with arith.
  generalize (HDefs _ H), (HDefs' _ H).
  simpl; unfold Pack1; simpl.
  rewrite Nat_eq. intros HX HX'.
  elim (Call_reduce IS _ _ HX); intros tl' Htl'.
  simpl in Htl'; rewrite HX' in Htl'.
  elim (Projection_reduce _ _ l Defs ps q (S X) s).
  fold x; set (s'' := s[[q,xx => x]]); intros tl0 H0.
  exists (tl' ++ tl0 :: List.nil)%list, s''; repeat split.
  - eapply CCT_Trans; eauto. eapply CCT_Step; eauto. rewrite plus_comm; apply CCT_Refl.
  - intros. unfold s''. rewrite update_read'; auto.
  - exists 0. unfold s'', Kleene.eval, x; simpl.
    rewrite all_defined_map_Some, update_read, nth_map'; auto.
+ (* Composition *)
  set (Hd' := lt_S_n (Nat.max (depth g) (vmax (map depth fs))) d Hd).
  set (Hfs := vmax_lt_map _ _ (max_lt_r _ _ _ Hd')).
  set (Hg := max_lt_l _ _ _ Hd').
  (* Here we start directly with the loop *)
  assert (exists sF tlF, (Defs,@Call IS X,s) --[tlF]-->* (Defs,@Call IS (X + vsum (map Gamma fs)),sF)
    /\ (forall p, p < i -> p <> q -> sF p xx = s p xx) /\ forall H, converges (fs[@H]) ns (sF (seq_labels i fs)[@H] xx)).
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
      snd (Defs Y) = seq_compose fs _ Hfs ps i (i+m+k) X (fun m f => Encoding_rec f d) Y).
    1: { exists 0; intros. rewrite HDefs'; auto. rewrite Composition_Procs_fs, plus_0_r; auto. }
    clearbody Hd' Hfs.
    clear g H Hd Hd' Hg HDefs'; rename H0 into HDefs'.
    revert dependent X. revert dependent i. revert dependent s.
    revert t s'; induction m.
    * intros. exists s, List.nil.
      rewrite <- (vector_0_inv fs).
      simpl. repeat split; auto. rewrite plus_comm; apply CCT_Refl. intros. inversion H.
    * intros.
      revert IHm.
      revert dependent fs. revert m. refine (@caseS _ _ _); intros.
      clear f. rename h into f, t0 into fs, n0 into m.
      (* First f... *)
      assert (forall Y, X <= Y < X + Gamma f -> X <= Y < X + vsum (map Gamma (f::fs))).
      1: { intros. inversion_clear H; split; auto. simpl. rewrite plus_assoc; auto with arith. }
      elim HDefs'; clear HDefs'; intros k' HDefs'.
      assert (i < i + S m + k').
      1: { apply lt_le_trans with (i + S m); auto with arith. rewrite <- plus_n_Sm; auto with arith. }
      elim IHd with k f (Hfs Fin.F1) ps i (i + S m + k') X Defs ns s t s'; auto.
      2: {
        intros.
        rewrite HDefs'; auto.
        simpl. inversion_clear H1.
        apply Nat.ltb_lt in H3; rewrite H3. auto.
      }
      2: { transitivity i; auto with arith. }
      2: { intro. apply (lt_irrefl i); auto. }
      intros. do 3 (elim H1; intro; clear H1; intro H1).
      rename x0 into sf, x into tlf, H1 into H1', H3 into H1.
      elim (diamond_5 _ _ _ _ _ _ _ _ _ H2 Htl (eq_refl _)).
      intros. destroy H3. clear H3.
      (* ... then the rest. *)
      elim IHm with fs (fun H => Hfs (Fin.FS H)) x x0 sf (S i) (X + Gamma f); intros; auto.
      destroy H3. rename x1 into sfs, x2 into tlfs, H3 into H3', H6 into H3. clear x x0 H4.
      2: { rewrite <- Hinput, H1; auto. transitivity i; auto. 2: apply lt_neq. all: eapply Hps, nth_In; eauto. }
      2: { transitivity i; auto. }
      2: {
        apply HDefs. simpl. inversion_clear HY; split.
        transitivity (X + Gamma f); auto with arith.
        rewrite plus_assoc; auto.
      }
      2: {
        exists (k' + Pi f); intros.
        inversion_clear H3. rewrite <- plus_assoc in H6.
        rewrite (HDefs' Y). 2: split; auto; transitivity (X + Gamma f); auto with arith.
        simpl. generalize H5; intro.
        apply le_not_lt, Nat.ltb_nlt in H5. rewrite H5.
        replace (i + S m + k' + Pi f) with (S (i + m + (k' + Pi f))); auto.
        repeat rewrite plus_assoc. rewrite <- plus_n_Sm; auto.
      }
      simpl (vsum (map Gamma (f::fs))).
      (* Wheee. *)
      exists sfs, (tlf ++ tlfs)%list; repeat split.
      ++ rewrite plus_assoc. eapply CCT_Trans; eauto.
      ++ intros; rewrite H3, H1; auto. transitivity i; auto. apply lt_neq; auto.
      ++ intro. apply (hd_tl_induction' (fun x y => converges x ns (sfs y xx))); auto.
         rewrite H3; auto. simpl. apply gt_neq; auto.
  - destroy H. rename x into sF, x0 into tlF, H into H', H1 into H.
    assert (X + Gamma (Composition g fs) = X + vsum (map Gamma fs) + Gamma g) as HX.
    simpl. rewrite (plus_comm (Gamma g)), plus_assoc; auto.
    elim (diamond_5 _ _ _ _ _ _ _ _ _ H0 Htl (eq_refl _)).
    intros. destroy H1.
    elim IHd with m g Hg (seq_labels i fs) q (i+m) (X + vsum (map Gamma fs)) Defs (map (fun y => sF y xx) (seq_labels i fs)) sF x x0; auto.
    * intros. do 3 (elim H3; intro; clear H3; intro H3). rename x2 into s'', x1 into tl'.
      exists (tlF++tl')%list, s''; repeat split.
      ++ eapply CCT_Trans; eauto. rewrite HX; auto.
      ++ intros; rewrite <- H5, H; auto. apply lt_le_trans with i; auto with arith.
      ++ apply Composition_converges with (map (fun y => sF y xx) (seq_labels i fs)); auto.
         intro. rewrite nth_map'; auto.
    * intros. inversion_clear H3. apply HDefs; split; auto.
      transitivity (X + vsum (map Gamma fs)); auto with arith.
      rewrite HX; auto.
    * intros. inversion_clear H3. rewrite HDefs'.
      rewrite Composition_Procs_g; auto. rewrite HX; auto.
      split; auto. transitivity (X + vsum (map Gamma fs)); auto with arith.
      rewrite HX; auto.
    * intros. elim (seq_labels_lt _ _ _ H3); auto.
    * apply lt_le_trans with i; auto with arith.
    * intro. elim (seq_labels_lt _ _ _ H3); intros.
      elim (lt_irrefl q). apply lt_le_trans with i; auto.
    * intro. rewrite nth_map'; auto.
+ (* Recursion *)
  set (Hd' := lt_S_n (Nat.max (depth g) (depth h)) d Hd).
  set (Hg := (max_lt_l _ _ _ Hd')).
  set (Hh := (max_lt_r _ _ _ Hd')).
  assert (forall H, ps[@H] < i) as Hpsi. intro; eapply Hps, nth_In; auto.
  (* @Call IS X,s -> @Call IS (X + Gamma g),sg sg(ps) = s(ps), sg(init) = f(s(tl ps)) *)
  assert (forall Y, X <= Y < X + Gamma g -> X <= Y < X + (Gamma g + Gamma h + 3)) as H'.
  1: {
    intros. inversion_clear H; split; simpl; auto.
    transitivity (X + Gamma g); auto.
    apply plus_lt_compat_l; auto with arith.
    apply le_lt_trans with (Gamma g + Gamma h); auto with arith.
    rewrite <- (plus_comm 3); simpl; auto.
  }
  assert (forall Y, X <= Y < X + Gamma g -> fst (Defs Y) <> List.nil) as HgDefs. eauto.
  assert (forall Y, X <= Y < X + Gamma g -> snd (Defs Y) = Encoding_rec g _ Hg (tl ps) i (i+3) X Y) as HgDefs'.
  1: {
    intros. elim H; intros. generalize (HDefs' _ (H' _ H)).
    rewrite Recursion_Procs_g; auto.
  }
  assert (i < i+3) as Hi'. rewrite plus_comm; simpl; auto.
  elim IHd with k g Hg (tl ps) i (i+3) X Defs (tl ns) s t s'; intros; auto.
  2: { transitivity i; auto. apply Hps, In_tail; auto. }
  2: { intro. apply (lt_irrefl i), Hps, In_tail; auto. }
  2: { repeat rewrite <- nth_tl; auto. }
  do 3 (elim H; intro; clear H; intro H).
  rename x0 into sg, x into tlg, H0 into Htlg, H1 into Hps', H into H1'.
  clear HgDefs HgDefs' H' Hg.
  (* @Call IS X + Gamma g,sg -> @Call IS (X + Gamma g + 1),s' s'(ps) = s(ps), s'(S init) = 0, s'(init) = f(s(tl ps)) *)
  assert (X <= X + Gamma g < X + Gamma (Recursion g h)).
  1: {
    split; auto with arith.
    apply plus_lt_compat_l. simpl. rewrite <- (plus_comm 3).
    transitivity (2 + Gamma g); simpl; auto with arith.
  }
  elim (Call_reduce IS Defs (X + Gamma g)); auto. intros.
  rename x into tlg'.
  rewrite HDefs', Recursion_Procs_0 in H0; auto.
  elim (Recursion_reduce_0 Defs (X + Gamma g + 1) i sg); intro tl1; intros.
  set (P := (Defs,@Call IS (X + Gamma g + 1))).
  generalize (CCT_Trans _ _ _ _ _ _ Htlg (CCT_Trans _ _ _ _ _ _ (H0 sg) (CCT_Step _ _ _ _ _ _ H1 (CCT_Refl _ _)))).
  clear H0 H1; fold P; intro HP.
  set (t' := (tlg ++ tlg' ++ tl1 :: List.nil)%list).
  set (s0 := sg[[S i,xx => 0]]).
  fold t' s0 in HP.
  clearbody t'. clear Htlg.
  (* Loop invariant *)
  assert (forall m, m <= s0 (hd ps) xx -> exists t' s', (P,s0) --[ t' ]-->* (P,s')
    /\ s' (S i) xx = m /\ (forall p, p < i -> s' p xx = s0 p xx) /\ converges (Recursion g h) (m::tl ns) (s' i xx)).
  - induction m; intros.
    * exists List.nil, s0; repeat split; auto. apply CCT_Refl. apply update_read.
      unfold s0. rewrite update_read'; auto.
    * elim IHm; auto with arith; clear IHm.
      intros tlI H'; do 4 (elim H'; intro; clear H'; intro H'). rename H' into H3', H3 into H'.
      rename x into sI, H1 into HI.
      assert (X <= X + Gamma g + 1 < X + Gamma (Recursion g h)).
      1: { split; simpl; auto with arith.  repeat (rewrite <- plus_assoc; apply plus_lt_compat_l); auto with arith. }
      elim (Call_reduce IS Defs (X + Gamma g + 1)); intros; auto.
      rename x into tlU, H3 into HU.
      rewrite HDefs', Recursion_Procs_1 in HU; auto.
      assert (sI (S i) xx <> sI (hd ps) xx).
      1: { rewrite H2, H'. apply lt_neq; auto. rewrite <- nth_hd; auto. }
      elim (Recursion_reduce_1_false _ Defs (X + Gamma g + Gamma h + 3) (X + Gamma g + 2) i ps q sI); auto.
      set (sU := sI[[S i,yy => (sI (hd ps) xx)]]).
      intros tlU' HU'.
      (* Setting up for the induction hypothesis on h *)
      assert (i+2 < i+3+Pi g) as Hi''; intros. auto with arith.
      assert (forall Y, X + Gamma g + 2 <= Y < X + Gamma g + 2 + Gamma h -> X <= Y < X + (Gamma g + Gamma h + 3)) as H''.
      1: {
        intros. inversion_clear H4; split; simpl.
        transitivity (X + Gamma g + 2); auto with arith.
        repeat rewrite <- plus_assoc.
        repeat rewrite <- plus_assoc in H6.
        rewrite (plus_comm 2) in H6.
        etransitivity; eauto.
        repeat apply plus_lt_compat_l; auto with arith.
      }
      assert (forall Y, X + Gamma g + 2 <= Y < X + Gamma g + 2 + Gamma h -> fst (Defs Y) <> List.nil) as HhDefs; auto.
      assert (forall Y, X + Gamma g + 2 <= Y < X + Gamma g + 2 + Gamma h -> snd (Defs Y) = Encoding_rec h d Hh (S i :: i :: tl ps) (i + 2) (i + 3 + Pi g) (X + Gamma g + 2) Y) as HhDefs'; auto.
      1: {
        intros. unfold Hh, Hd'; rewrite <- Recursion_Procs_h with (q:=q); auto.
        replace (X + Gamma g + Gamma h + 2) with (X + Gamma g + 2 + Gamma h); auto.
        repeat rewrite <- plus_assoc. rewrite (plus_comm 2); auto.
      }
      elim (diamond_5 _ _ _ _ _ _ _ _ _ (CCT_Trans _ _ _ _ _ _ HP (CCT_Trans _ _ _ _ _ _ HI (CCT_Trans _ _ _ _ _ _ (HU sI) HU'))) Htl (eq_refl _)).
      intros. destroy H4. clear H4.
      elim IHd with (2+k) h Hh (S i::i::tl ps) (i+2) (i+3+Pi g) (X + Gamma g + 2) Defs (m :: (sI i xx) :: tl ns) sU x x0; intros; auto.
      2: {
        elim (In_elim H4); intro.
        rewrite <- H6. rewrite <- plus_assoc. rewrite plus_comm; simpl.
        rewrite plus_comm; auto with arith.
        elim (In_elim H6); intro.
        rewrite H7; apply le_lt_trans with (p+0); auto with arith.
        transitivity i. apply Hps, In_tail; auto.
        apply le_lt_trans with (i+0); auto with arith.
      }
      2: {
        intro. elim (In_elim H4).
        apply lt_neq. rewrite plus_comm; auto.
        intro; elim (In_elim H6).
        apply lt_neq; rewrite plus_comm; simpl; auto.
        intro. apply (lt_irrefl i).
        transitivity (i+2). rewrite plus_comm; simpl; auto.
        apply Hps, In_tail; auto.
      }
      2: {
        apply (hd_tl_induction' (fun x y => sU x xx = y)).
        simpl. rewrite <- H2; unfold sU. rewrite update_read''; auto. discriminate.
        intro. apply (hd_tl_induction' (fun x y => sU x xx = y)); simpl; unfold sU.
        rewrite update_read''; auto. discriminate.
        assert (forall H, ps[@H] < i). intro; eapply Hps, nth_In; eauto.
        intro. repeat rewrite <- nth_tl. rewrite update_read'', H'; auto.
        2: discriminate.
        unfold s0. rewrite update_read', <- Hps'; auto.
        transitivity i; auto. apply lt_neq; auto. apply gt_neq; red; transitivity i; auto.
      }
      rename x1 into tlF; do 3 (elim H4; intro; clear H4; intro H4). rename x1 into sF, H4 into H4', H7 into H4.
      (* After calling h *)
      repeat rewrite <- plus_assoc in H6; rewrite (plus_comm 2) in H6.
      repeat rewrite plus_assoc in H6.
      assert (X <= X + Gamma g + Gamma h + 2 < X + (Gamma g + Gamma h + 3)).
      1: { split; auto with arith.
        repeat rewrite <- plus_assoc; repeat apply plus_lt_compat_l; auto.
      }
      elim (Call_reduce IS Defs (X + Gamma g + Gamma h + 2)); auto; intros.
      rewrite HDefs', Recursion_Procs_2 in H8; auto.
      elim (Recursion_reduce_2 Defs (X + Gamma g + 1) i sF); intros.
      destroy H9. rename x2 into tlF', x3 into sF'.
      exists (tlI ++ tlU ++ tlU' ++ tlF ++ x1 ++ tlF')%list, sF'.
      repeat split; auto.
      ++ do 5 (eapply CCT_Trans; eauto).
      ++ rewrite H13, <- H4, <- H2. unfold sU. rewrite update_read''; auto. discriminate.
         rewrite <- (plus_comm 3); simpl; auto with arith.
         apply lt_neq; rewrite plus_comm; simpl; auto.
      ++ intros. rewrite H11, <- H4; auto.
         unfold sU. rewrite update_read'; auto.
         apply gt_neq; auto. transitivity (i+2); auto with arith.
         apply lt_neq; auto with arith.
      ++ apply Recursion_converges_step with (sI i xx); auto.
         rewrite H12; auto.
  - elim (H0 _ (le_refl _)); clear H0; intros tl' Htl'.
    do 4 (elim Htl'; intro; clear Htl'; intro Htl'). rename Htl' into H2', H2 into Htl'.
    rename x into sF.
    assert (X <= X + Gamma g + 1 < X + Gamma (Recursion g h)).
    1: {
      split; auto with arith.
      simpl. repeat rewrite <- plus_assoc; repeat apply plus_lt_compat_l.
      rewrite plus_comm; auto with arith.
    }
    elim (Call_reduce IS Defs (X + Gamma g + 1)); auto; intros.
    rewrite HDefs', Recursion_Procs_1 in H3; auto.
    rename x into tlU, H3 into HU.
    assert (sF (S i) xx = sF (hd ps) xx).
    1: { rewrite H1, Htl'; auto. rewrite <- nth_hd; auto. }
    elim (Recursion_reduce_1_true _ Defs (X + Gamma g + Gamma h + 3) (X + Gamma g + 2) i ps q sF); auto.
    intros. destroy H4. rename x into tlF', x0 into sF'.
    exists (t' ++ tl' ++ tlU ++ tlF')%list, sF'; repeat split.
    * do 3 (eapply CCT_Trans; eauto). simpl. repeat rewrite plus_assoc; auto.
    * intros. rewrite H4, Htl'; auto.
      unfold s0. rewrite update_read'. 2: apply gt_neq; auto.
      apply Hps'; auto. transitivity i; auto. apply lt_neq; auto.
    * rewrite H6; auto. 
      replace ns with (s0 (hd ps) xx :: tl ns); auto.
      rewrite eta. replace (s0 (hd ps) xx) with (hd ns); auto.
      assert (hd ps < i). apply Hps. rewrite eta; constructor.
      unfold s0; rewrite update_read', <- Hps', <- nth_hd, <- nth_hd; auto.
      transitivity i; auto. apply lt_neq; auto. apply gt_neq; red; transitivity i; auto.
+ (* Minimization *)
  set (Hd' := lt_S_n (depth h) d Hd).
  assert (forall H, ps[@H] < i) as Hpsi. intro; eapply Hps, nth_In; auto.
  assert (i + 1 < i + 3) as Hi1. apply plus_lt_compat_l; auto.
  assert (i + 1 <> i) as Hi2. rewrite plus_comm; simpl; auto.
  assert (i + 2 < i + 3) as Hi3. apply plus_lt_compat_l; auto.
  assert (S X = X + 1) as HXSX. rewrite plus_comm; auto.
  (* Initialization *)
  assert (X <= X < X + Gamma (Minimization h)).
  1: {
    split; auto with arith.
    apply le_lt_trans with (X + 0); auto with arith.
    apply plus_lt_compat_l; apply Gamma_neq_zero.
  }
  elim (Call_reduce IS Defs X); auto. intros tl0 H00.
  rewrite HDefs', Minimization_Procs_0 in H00; auto.
  elim (Minimization_reduce_0 Defs (X+1) i s); intros tl0' H0.
  set (s0 := s[[i+1,xx => 0]]); fold s0 in H0.
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
  assert (forall Y, X + 1 <= Y < X + 1 + Gamma h -> snd (Defs Y) = Encoding_rec h _ Hd' (shiftin (i+1) ps) i (i+3) (X+1) Y) as HhDefs'.
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
  specialize (H00 s).
  elim (diamond_5 _ _ _ _ _ _ _ _ _ (CCT_Trans _ _ _ _ _ _ H00 (CCT_Step _ _ _ _ _ _ H0 (CCT_Refl _ _))) Htl (eq_refl _)); intros.
  destroy H1. clear H1.
  elim IHd with (1+k) h Hd' (shiftin (i+1) ps) i (i+3) (X+1) Defs (shiftin 0 ns) s0 x x0; auto; intros.
  2: {
    rewrite <- (nth_map' (fun y => s0 y xx)), map_shiftin. apply shiftin_eq.
    apply update_read.
    intro; unfold s0. rewrite nth_map', update_read'; auto.
    apply gt_neq; red; transitivity i. eapply Hps, nth_In; eauto. rewrite plus_comm; auto.
  }
  do 3 (elim H1; intro; clear H1; intro H1). rename x1 into tlI, x2 into sI, H3 into HI, H1 into H1', H4 into H1.
  clear x x0 H2.
  replace (X + 1 + Gamma h) with (X + Gamma h + 1) in HI.
  2: repeat rewrite <- plus_assoc; rewrite <- (plus_comm 1); auto.
  generalize (CCT_Trans _ _ _ _ _ _ H00 (CCT_Step _ _ _ _ _ _ H0 HI)).
  clear H0 H00 HI; intro HI.
  assert (X <= X + Gamma h + 1 < X + Gamma (Minimization h)).
  1: { split; simpl; auto with arith. rewrite plus_assoc; auto with arith. }
  set (P := (Defs,@Call IS (X + Gamma h + 1))).
  set (tP := (tl0 ++ tl0' :: tlI)%list). fold P tP in HI.
  clearbody tP; clear tl0 tl0' tlI.
  assert (forall sP, sP i xx <> 0 -> forall tlF sF, (P,sP) --[tlF]-->*(Defs,End,sF) ->
      (forall p, p < i -> sP p xx = s p xx) -> exists tlP s', (P,sP) --[tlP]-->* (P,s') /\ length tlP > 0 /\
        (forall p, p < i -> s' p xx = s p xx) /\ s' (i+1) xx = S (sP (i+1) xx) /\ s' (i+2) xx = sP (i+1) xx
          /\ converges h (shiftin (S (sP (i+1) xx)) ns) (s' i xx)).
  - intros.
    elim (Call_reduce IS Defs (X + Gamma h + 1)); intros; auto.
    rename x into tlh.
    rewrite HDefs', Minimization_Procs_1 in H5; auto.
    elim (Minimization_reduce_1_false Defs (X + Gamma h + 2) (X + 1) i sP q); auto.
    intros. destroy H6. rename x into tl1, x0 into s1.
    specialize (H5 sP).
    elim (diamond_5 _ _ _ _ _ _ _ _ _ (CCT_Trans _ _ _ _ _ _ H5 H7) H3); auto.
    intros. destroy H11. clear H11.
    elim IHd with (1+k) h Hd' (shiftin (i+1) ps) i (i+3) (X+1) Defs (shiftin (s1 (i+1) xx) ns) s1 x x0; auto; intros.
    2: {
      rewrite <- (nth_map' (fun y => s1 y xx)), map_shiftin. apply shiftin_eq; auto.
      intro. rewrite nth_map', H8, H4, Hinput; auto.
    }
    do 3 (elim H11; intro; clear H11; intro H11). rename x1 into tlH, x2 into sH.
    clear x x0 H12.
    replace (X + 1 + Gamma h) with (X + Gamma h + 1) in H13.
    2: repeat rewrite <- plus_assoc; rewrite <- (plus_comm 1); auto.
    fold P in H13.
    exists (tlh ++ tl1 ++ tlH)%list, sH; repeat split; auto.
    * do 2 (eapply CCT_Trans; eauto).
    * red. apply lt_le_trans with (length tlh). 2: rewrite app_length; auto with arith.
      case_eq (length tlh); intros; auto with arith.
      exfalso. apply length_zero_iff_nil in H12. rewrite H12 in H5; inversion H5.
    * intros. rewrite <- H14, H8, H4; auto. transitivity i; auto. apply lt_neq; auto.
    * rewrite <- H14; auto.
    * rewrite <- H14; auto.
      rewrite plus_comm; simpl; apply gt_neq; auto.
    * rewrite <- H10; auto.
  - elim (diamond_5 _ _ _ _ _ _ _ _ _ HI Htl); auto.
    intros. destroy H3. clear H3. rename x into tlP', x0 into sP'.
    assert (forall N, length tlP' <= N -> exists tl sF, (P,sI) --[ tl ]-->* (P,sF)
      /\ sF i xx = 0 /\ (forall p, p < i -> sF p xx = sI p xx)
      /\ (forall m, m < sF (i+1) xx -> exists z, converges h (shiftin m ns) (S z)) /\ converges h (shiftin (sF (i+1) xx) ns) 0).
    * assert (converges h (shiftin (sI (i+1) xx) ns) (sI i xx)).
      1: { rewrite <- H1; auto. unfold s0; rewrite update_read; auto. }
      clear H1'; rename H3 into H1'.
      assert (forall m, m < sI (i+1) xx -> exists z, converges h (shiftin m ns) (S z)).
      1: { intro. rewrite <- H1; auto. unfold s0; rewrite update_read. intro; inversion H3. }
      rename H3 into H1''.
      assert (forall p, p < i -> sI p xx = s p xx).
      1: {
        intros; rewrite <- H1. unfold s0; rewrite update_read'; auto.
        apply gt_neq; red; rewrite plus_comm; simpl; auto. transitivity i; auto. apply lt_neq; auto.
      }
      clear H1; rename H3 into H1.
      intro; revert dependent tlP'. revert dependent sI. revert dependent sP'. revert dependent tP.
      induction N; intros.
      1: { exfalso. inversion H3. rewrite length_zero_iff_nil in H6; rewrite H6 in H4; inversion H4. }
      case_eq (sI i xx); intros.
      1: { exists List.nil, sI. repeat split; auto. apply CCT_Refl. rewrite <- H5; auto. }
      elim H2 with sI tlP' sP'; intros; auto.
      2: rewrite H5; discriminate.
      do 6 (elim H6; intro; clear H6; intro H6). rename x into tlF, x0 into sF.
      elim (diamond_5a _ _ _ _ _ _ _ _ _ H7 H4); auto; intros.
      destroy H12. elim IHN with (tP ++ tlF)%list x0 sF x; auto.
      clear H14 IHN x H12 x0 H13; intros.
      destroy H12. rename x into tlN, x0 into sN.
      2: { eapply CCT_Trans; eauto. }
      2: { rewrite H10; auto. }
      2: { rewrite H10; intros. inversion H15; auto. exists n0. rewrite <- H5; auto. }
      2: { rewrite <- H12 in H3. apply le_S_n. transitivity (length tlF + length x); auto.
            change (0 + length x < length tlF + length x). apply plus_lt_compat_r; auto. }
      exists (tlF ++ tlN)%list, sN; repeat split; auto.
      eapply CCT_Trans; eauto. intros. rewrite H15, H9, H1; auto.
      exists x1; auto.
    * elim (H3 (length tlP')); auto. intros. clear H2 H3 H4. destroy H5.
      rename x0 into sL, x into tlL.
      elim (Call_reduce IS Defs (X + Gamma h + 1)); intros; auto.
      rename x into tlh.
      rewrite HDefs', Minimization_Procs_1 in H7; auto.
      elim (Minimization_reduce_1_true Defs (X + Gamma h + 2) (X + 1) i sL q); auto.
      intros. destroy H8. rename x into tl1, x0 into s1.
      simpl; simpl in H9; rewrite plus_assoc.
      exists (tP ++ tlL ++ tlh ++ tl1)%list, s1; repeat split; auto.
      ++ do 3 (eapply CCT_Trans; eauto).
      ++ intros. rewrite H10, H4, <- H1; auto. unfold s0; rewrite update_read'; auto.
         apply gt_neq; red; rewrite plus_comm; auto. transitivity i; auto. apply lt_neq; auto.
      ++ rewrite H11; apply Minimization_converges; auto.
         exists x1; auto.
Qed.

Theorem Encoding_converges' : forall {n} (f:PRFunction n) ps q ns y,
  ~In q ps -> forall s, (forall H, s ps[@H] xx = ns[@H]) ->
  (exists c' tl, (Encoding f ps q,s) --[tl]-->* c'
     /\ Main (fst c') = End /\ snd c' q xx = y)
  -> converges f ns y.
Proof.
intros. destroy H1. induction x; induction a as (Procs,Main).
simpl in H1, H3. rewrite H3 in H2; clear H3 Main. rename x0 into tl, b into s'.
set (Hd := Nat.lt_succ_diag_r (depth f)).
set (i := (S (max q (vmax ps)))).
elim (Encoding_rec_End f _ Hd ps q i 0 (Procedures IS (Encoding f ps q))) with ns s tl s'; intros; auto.
+ destroy H3. rewrite <- H1. exists x1; auto.
  elim (Call_reduce _ (Procedures IS (Encoding f ps q)) (0 + Gamma f)).
  2: apply all_pids_not_nil.
  intros.
  replace (snd (Procedures IS (Encoding f ps q) (0 + Gamma f))) with (Encoding_rec f _ Hd ps q i 0 (0 + Gamma f)) in H6.
  2: reflexivity. 
  rewrite (Encoding_rec_ge f _ Hd ps q i 0 (0 + Gamma f)) in H6; auto.
  elim (diamond_5 _ _ _ _ _ _ _ _ _ H2 (CCT_Trans _ _ _ _ _ _ H4 (H6 x0))); auto. intros.
  destroy H7. elim (CCP_ToStar_End _ _ _ _ _ _ H8); auto; intros.
  rewrite H3. rewrite H10, <- H7. auto.
+ apply all_pids_not_nil.
+ apply le_n_S. transitivity (vmax ps). apply vmax_In; auto. apply Nat.le_max_r.
+ apply le_n_S. apply Nat.le_max_l.
+ unfold Encoding in H2. rewrite <- (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ _ H2) in H2; auto.
Qed.

Theorem Encoding_diverges : forall {n} (f:PRFunction n) ps q ns,
  ~In q ps -> diverges f ns -> 
  forall s, (forall H, s ps[@H] xx = ns[@H]) ->
  forall c tl, (Encoding f ps q, s) --[tl]-->* c -> Main (fst c) <> End.
Proof.
intros.
red; intro.
set (Hd := Nat.lt_succ_diag_r (depth f)).
set (i := (S (max q (vmax ps)))).
induction c; induction a as (Procs,Main).
simpl in H3; rewrite H3 in H2; clear Main H3. rename b into s'.
elim (Encoding_rec_End f _ Hd ps q i 0 (Procedures IS (Encoding f ps q))) with ns s tl s'; intros; auto.
+ destroy H3. rewrite H0 in H3. inversion H3.
+ apply all_pids_not_nil.
+ apply le_n_S. transitivity (vmax ps). apply vmax_In; auto. apply Nat.le_max_r.
+ apply le_n_S. apply Nat.le_max_l.
+ unfold Encoding in H2. rewrite <- (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ _ H2) in H2; auto.
Qed.

Theorem encoding_sound : forall n (f:PRFunction n),
  implements (Encoding' f) f (vec_1_to_n n) 0.
Proof.
intros. apply implements_char.
split; intros.
+ elim (Encoding_converges f (vec_1_to_n n) 0 xs y) with s; intros; auto.
  2: { intro. elim (in_vec_k_to_n _ H1); intros. inversion H2. }
  destroy H1. induction x. simpl in H1, H3.
  rename a into P, b into s', x0 into tl. exists s', tl, P.
  repeat split; auto.
+ apply (Encoding_converges' f (vec_1_to_n n) 0 xs y) with s; auto.
  intro. elim (in_vec_k_to_n _ H1); intros. inversion H2.
  destroy H0. exists (x1,x), x0; repeat split; auto.
Qed.

(** ** Well formedness
  We now show that implementation choreographies are well-formed. This is strictly speaking not necessary,
  but it is relevant. *)

Section WellFormedness.

(** We need to use the list of recursion variables up to a given bound. *)

Fixpoint RecVarList n : list RecVar :=
match n with
| 0 => (0::List.nil)%list
| S m => (n::RecVarList m)
end.

Lemma RecVarList_In : forall m n, m <= n -> List.In m (RecVarList n).
Proof.
induction n; simpl; auto with arith.
intros.
inversion H; auto.
Qed.

Lemma In_RecVarList : forall m n, List.In m (RecVarList n) -> m <= n.
Proof.
induction n; simpl; intros.
+ inversion_clear H; inversion H0; auto.
+ inversion H; auto. rewrite H0; auto.
Qed.

Lemma RecVarList_incl : forall m n, m <= n ->
  (forall X, List.In X (RecVarList m) -> List.In X (RecVarList n)).
Proof.
intros.
apply RecVarList_In.
transitivity m; auto.
apply In_RecVarList; auto.
Qed.

(** Choreography implementations are well-formed. *)

Lemma Encoding_Main_WF : forall {n} (f:PRFunction n) ps q,
  Choreography_WF (Main (Encoding f ps q)).
Proof. intros. simpl. split; simpl; auto. Qed.

(* Lemma Encoding_Main_within_Xs : forall {n} (f:PRFunction n) ps q Xs,
  List.In 0 Xs -> @within_Xs IS Xs (Main (Encoding f ps q)).
Proof. auto. Qed.
 *)

Lemma seq_compose_WF :
  forall {k m} (fs:t (PRFunction m) k) d Hd ps n q X Implement Y,
  (forall p, In p ps -> p < n) -> n + k <= q ->
  (forall k f ps' m' n' H X Y, (forall p, In p ps' -> p < m') -> m' < n' ->
      Choreography_WF (Implement k f H ps' m' n' X Y)) ->
  Choreography_WF (seq_compose fs d Hd ps n q X Implement Y).
Proof.
induction k; intro.
+ refine (@case0 _ _ _ ); simpl; intros.
  split; simpl; auto.
+ intro; revert k fs IHk. refine (@caseS _ _ _); simpl; intros.
  elim Nat.ltb; auto.
  - assert (n0 < n0 + S n). rewrite <- plus_Snm_nSm; auto with arith.
    apply H1; auto.
    intros. apply lt_le_trans with (n0 + S n); auto.
  - apply IHk; auto. intros; transitivity n0; auto.
    rewrite plus_Snm_nSm. transitivity q; auto with arith.
Qed.

Lemma Encoding_rec_WF : forall m (f:PRFunction m) d Hd ps q n X Y,
  ~In q ps -> (forall p, In p ps -> p < n) -> q < n ->
  Choreography_WF (Encoding_rec f d Hd ps q n X Y).
Proof.
intros m f d; revert m f.
induction d. inversion Hd.
do 2 intro; case f; intros.
+ (* Zero *)
  simpl. unfold Pack1; simpl.
  elim eq_nat_dec; repeat split; simpl; auto.
  intro; apply H. eapply nth_In. rewrite nth_hd; auto.
+ (* Successor *)
  simpl. unfold Pack1; simpl.
  elim eq_nat_dec; repeat split; simpl; auto.
  intro; apply H. eapply nth_In. rewrite nth_hd; auto.
+ (* Projection *)
  simpl. unfold Pack1; simpl.
  elim eq_nat_dec; repeat split; simpl; auto.
  intro; apply H. eapply nth_In; eauto.
+ (* Composition *)
  simpl. elim Nat.ltb.
  - apply seq_compose_WF; intros; auto.
    apply IHd; auto.
    intro. apply (lt_irrefl m'); auto.
    intros; transitivity m'; auto.
  - apply IHd.
    * intro. elim (seq_labels_lt _ _ _ H2); intros. apply (lt_irrefl n).
      apply le_lt_trans with q; auto.
    * intros. elim (seq_labels_lt _ _ _ H2); auto.
    * apply lt_le_trans with n; auto with arith.
+ (* Recursion *)
  assert (n+2 <> n). apply gt_neq; rewrite plus_comm; simpl; auto.
  assert (n+3 <> n). apply gt_neq; rewrite plus_comm; simpl; auto.
  assert (n+2 <> S n). apply gt_neq; rewrite plus_comm; simpl; auto.
  simpl. elim Nat.ltb. 2: elim eq_nat_dec. 3: elim eq_nat_dec.  4: elim eq_nat_dec.
  - apply IHd; auto.
    * intro. elim (lt_irrefl n). apply H0, In_tail; auto.
    * transitivity n. apply H0, In_tail; auto. rewrite plus_comm; simpl; auto.
    * rewrite plus_comm; simpl; auto.
  - split; simpl; split; auto.
  - split; simpl; repeat split; auto.
    * apply lt_neq. transitivity n; auto. apply H0. apply nth_In with Fin.F1; apply nth_hd.
    * apply gt_neq; auto.
  - split; simpl; repeat split; auto.
  - intros; apply IHd; auto with arith.
    * intro. rewrite plus_comm in H5; simpl in H5.
      elim (In_elim H5); intros. elim (lt_irrefl (S n)). rewrite H6 at 2; auto.
      elim (In_elim H6); intros. elim (lt_irrefl n). rewrite H7 at 2; auto.
      apply (lt_irrefl n). transitivity (S (S n)); auto. apply H0, In_tail; auto.
    * intros. transitivity (n+2); auto with arith. rewrite plus_comm; simpl.
      elim (In_elim H5); intros. rewrite <- H6; auto.
      elim (In_elim H6); intros. rewrite <- H7; auto.
      transitivity n; auto. apply H0, In_tail; auto.
+ (* Minimization *)
  assert (n+1 <> n+2). apply lt_neq. rewrite plus_comm; rewrite (plus_comm n 2); auto.
  assert (n <> n+2). apply lt_neq. rewrite plus_comm; simpl; auto.
  simpl. elim eq_nat_dec. 2: elim eq_nat_dec.
  - split; simpl; split; auto.
  - split; simpl; repeat split; auto.
    apply gt_neq; red. rewrite plus_comm. transitivity n; auto.
  - assert (n < n+3). rewrite plus_comm; simpl; auto.
    intros; apply IHd; auto.
    * intro. elim (shiftin_elim _ _ H5); intro. apply (lt_irrefl n). rewrite <- H6 at 2; auto. rewrite plus_comm; auto.
      apply (lt_irrefl n); auto.
    * intros; transitivity (S (S n)). 2: rewrite plus_comm; simpl; auto.
      elim (shiftin_elim _ _ H5); auto with arith. intro. rewrite <- H6, plus_comm; auto.
Qed.

Lemma seq_compose_initial :
  forall {k m} (fs:t (PRFunction m) k) d Hd ps n q X Implement Y,
  (forall k f ps' m' n' H X Y, initial (Implement k f H ps' m' n' X Y)) ->
  initial (seq_compose fs d Hd ps n q X Implement Y).
Proof.
induction k; intro.
+ refine (@case0 _ _ _ ); simpl; intros.
  split; simpl; auto.
+ intro; revert k fs IHk. refine (@caseS _ _ _); simpl; intros.
  elim Nat.ltb; auto.
Qed.

Lemma Encoding_rec_initial : forall m (f:PRFunction m) d Hd ps q n X Y,
  initial (Encoding_rec f d Hd ps q n X Y).
Proof.
intros m f d; revert m f.
induction d. inversion Hd.
do 2 intro; case f; intros; simpl;
  unfold Pack1; try (elim eq_nat_dec; simpl; auto; fail);
  try elim Nat.ltb; try (apply seq_compose_initial); auto;
  repeat (elim eq_nat_dec; simpl; auto).
Qed.

Lemma Encoding_Procs_Vars_not_nil : forall {n} (f:PRFunction n) ps q X,
  Vars (Encoding f ps q) X <> List.nil.
Proof.
intros. unfold Vars; simpl.
apply all_pids_not_nil.
Qed.

(* Lemma seq_compose_within_Xs :
  forall {k m} (fs:t (PRFunction m) k) d Hd ps n q X Implement Y,
  (forall k f ps' m' n' H X Y,
    within_Xs (RecVarList (X+Gamma f)) (Implement k f H ps' m' n' X Y)) ->
    within_Xs (RecVarList (X+vsum (map Gamma fs)))
      (seq_compose fs d Hd ps n q X Implement Y).
Proof.
induction k; intro.
+ refine (@case0 _ _ _ ); simpl; intros.
  split; simpl; auto.
+ intro; revert k fs IHk. refine (@caseS _ _ _); simpl; intros.
  elim Nat.ltb; auto.
  - apply within_Xs_incl with (RecVarList (X + Gamma h)); auto.
    apply RecVarList_incl; auto with arith.
  - eapply within_Xs_incl.
    2: apply IHk; auto.
    apply RecVarList_incl.
    rewrite plus_assoc; auto with arith.
Qed.

Lemma Encoding_rec_within_Xs : forall m (f:PRFunction m) d Hd ps q n X,
  forall Y, within_Xs (RecVarList (X+Gamma f)) (Encoding_rec f d Hd ps q n X Y).
Proof.
intros m f d; revert m f.
induction d. inversion Hd.
do 2 intro; case f; intros; simpl.
+ (* Zero *)
  simpl. unfold Pack1; simpl; intros.
  elim eq_nat_dec; simpl; auto.
  intro; apply RecVarList_In; rewrite plus_comm; auto with arith.
+ (* Successor *)
  simpl. unfold Pack1; simpl; intros.
  elim eq_nat_dec; simpl; auto.
  intro; apply RecVarList_In; rewrite plus_comm; auto with arith.
+ (* Projection *)
  simpl. unfold Pack1; simpl; intros.
  elim eq_nat_dec; simpl; auto.
  intro; apply RecVarList_In; rewrite plus_comm; auto with arith.
+ (* Composition *)
  elim Nat.ltb.
  - eapply within_Xs_incl.
    2: apply seq_compose_within_Xs; auto.
    apply RecVarList_incl. auto with arith.
  - apply within_Xs_incl with (RecVarList (X + vsum (map Gamma fs) + Gamma g)); auto.
    apply RecVarList_incl. rewrite (plus_comm (Gamma g)), plus_assoc; auto with arith.
+ (* Recursion *)
  elim Nat.ltb; [idtac | elim eq_nat_dec; [idtac | elim eq_nat_dec; [idtac | elim eq_nat_dec] ] ]; simpl; intros.
  - apply within_Xs_incl with (RecVarList (X + Gamma g)); auto.
    apply RecVarList_incl. auto with arith.
  - apply RecVarList_In.
    rewrite <- plus_assoc. apply plus_le_compat_l.
    rewrite <- plus_assoc. apply plus_le_compat_l.
    rewrite plus_comm; auto with arith.
  - split; apply RecVarList_In.
    do 2 rewrite (plus_assoc X); auto with arith.
    rewrite <- plus_assoc. apply plus_le_compat_l.
    rewrite <- plus_assoc. apply plus_le_compat_l.
    rewrite plus_comm; auto with arith.
  - apply RecVarList_In.
    rewrite <- plus_assoc. apply plus_le_compat_l.
    rewrite <- plus_assoc. apply plus_le_compat_l.
    rewrite plus_comm; auto with arith.
  - apply within_Xs_incl with (RecVarList (X + Gamma g + 2 + Gamma h)); auto.
    apply RecVarList_incl.
    do 2 rewrite <- plus_assoc. apply plus_le_compat_l.
    rewrite <- plus_assoc. apply plus_le_compat_l.
    rewrite plus_comm; auto with arith.
+ (* Minimization *)
  elim eq_nat_dec; [idtac | elim eq_nat_dec]; simpl; intros.
  - apply RecVarList_In. apply plus_le_compat_l.
    rewrite plus_comm; auto with arith.
  - split; apply RecVarList_In.
    rewrite (plus_assoc X); auto with arith.
    apply plus_le_compat_l; auto with arith.
  - apply within_Xs_incl with (RecVarList (X + 1 + Gamma h)); auto.
    apply RecVarList_incl.
    rewrite <- plus_assoc. apply plus_le_compat_l.
    rewrite plus_comm; auto with arith.
Qed.
 *)

Lemma CCC_pn_all_pids_incl : forall (C:Choreography IS) m n, m <= n ->
  (CCC_pn C (fun _ => all_pids m) [C] all_pids m)
  -> (CCC_pn C (fun _ => all_pids n) [C] all_pids n).
Proof.
induction C; simpl; unfold set_incl; intros; auto.
- (* Eta *)
  unfold set_incl in IHC.
  elim (set_union_elim _ _ _ _ H1); intros.
  apply (all_pids_incl m); auto. apply H0. apply set_union_iff; auto.
  apply IHC with m; auto. intros; apply H0. apply set_union_iff; auto.
- (* Cond *)
  unfold set_incl in IHC1, IHC2.
  elim (set_union_elim _ _ _ _ H1); intros. elim (set_union_elim _ _ _ _ a); intros.
  apply (all_pids_incl m); auto. apply H0. apply set_union_iff; left. apply set_union_iff; auto.
  apply IHC1 with m; auto. intros; apply H0. apply set_union_iff; left. apply set_union_iff; auto.
  apply IHC2 with m; auto. intros; apply H0. apply set_union_iff; auto.
- (* RT_Call      *)
  unfold set_incl in IHC.
  elim (set_union_elim _ _ _ _ H1); intros.
  apply (all_pids_incl m); auto. apply H0. apply set_union_iff; auto.
  apply IHC with m; auto. intros; apply H0. apply set_union_iff; auto.
- (* End *)
  inversion H1.
Qed.

Lemma CCC_pn_eta : forall p f f' (C:Choreography IS),
  (forall X, f X = f' X) -> List.In p (CCC_pn C f) -> List.In p (CCC_pn C f').
Proof.
induction C; simpl; auto; intros.
+ (* Eta *)
  apply set_union_intro; elim (set_union_elim _ _ _ _ H0); auto.
  right; apply IHC; auto.
+ (* Cond *)
  apply set_union_intro; elim (set_union_elim _ _ _ _ H0); auto.
  2: right; apply IHC2; auto.
  left. apply set_union_intro; elim (set_union_elim _ _ _ _ a); auto.
  right; apply IHC1; auto.
+ (* Call IS *)
  rewrite <- H; auto.
+ (* RT_Call IS *)
  apply set_union_intro; elim (set_union_elim _ _ _ _ H0); auto.
  right; apply IHC; auto.
Qed.

Lemma seq_compose_well_ann :
  forall {k m} (fs:t (PRFunction k) m) d Hd ps target init X Impl Y,
  (forall p, In p ps -> p <= init) -> (forall p, In p ps -> p <= target) ->
  target + m <= init -> (forall H p Hd' q i' X' Y', q <= i' ->
  (forall p, In p ps -> p <= q) ->
  List.In p (@CCC_pn IS (Impl k fs[@H] Hd' ps q (S i') X' Y')
            (fun _ => all_pids (i' + Pi fs[@H]))) -> p <= i' + Pi fs[@H]) ->
  forall p, List.In p (CCC_pn (seq_compose fs d Hd ps (S target) (S init) X Impl Y)
            (fun _ => all_pids (init + vsum (map Pi fs)))) -> p <= init + vsum (map Pi fs).
Proof.
intros. revert init target H H0 H1 X Y p H2 H3. revert dependent m. induction m.
+ refine (@case0 _ _ _ ); simpl; intros. inversion H3.
+ intro. revert m fs IHm. refine (@caseS _ _ _); intros.
  revert H3; simpl. rewrite plus_assoc. elim Nat.ltb; intros.
  - apply In_all_pids. revert H3.
    apply CCC_pn_all_pids_incl with (init + Pi h). auto with arith.
    red; red; intros. apply all_pids_In.
    replace h with (hd (h::t)); auto. rewrite <- nth_hd.
    apply (H2 Fin.F1 z (Hd Fin.F1) (S target) init X Y); auto.
    transitivity (target + S n); auto. rewrite <- plus_n_Sm; auto with arith.
  - apply IHm with (fun H => Hd (Fin.FS H)) (S target) (X+Gamma h) Y; auto with arith.
    * transitivity init; auto with arith. rewrite plus_Sn_m, plus_n_Sm; auto.
    * intros. replace t with (tl (h::t)); auto. rewrite <- nth_tl.
      apply H2 with Hd' q X' Y'; auto.
Qed.

Lemma Encoding_rec_well_ann : forall {m} (f:PRFunction m) d Hd ps q i X Y,
  (forall p, In p ps -> p <= i) -> q <= i -> forall p,
  List.In p (CCC_pn (Encoding_rec f d Hd ps q (S i) X Y)
            (fun _ => all_pids (i + Pi f))) -> p <= i + Pi f.
Proof.
intros m f d; revert m f.
induction d. inversion Hd.
do 2 intro; case f; simpl; intros; revert H1.
- unfold Pack1. rewrite plus_0_r.
  elim eq_nat_dec; simpl; intros. 2: inversion H1.
  elim (set_union_elim _ _ _ _ H1); intros. inversion_clear a0.
  * apply H. eapply nth_In. rewrite nth_hd. eauto.
  * revert H0. inversion_clear H2; inversion H0; auto.
  * apply In_all_pids; auto.
- unfold Pack1. rewrite plus_0_r.
  elim eq_nat_dec; simpl; intros. 2: inversion H1.
  elim (set_union_elim _ _ _ _ H1); intros. inversion_clear a0.
  * apply H; eapply nth_In; rewrite nth_hd; eauto.
  * revert H0. inversion_clear H2; inversion H0; auto.
  * apply In_all_pids; auto.
- unfold Pack1. rewrite plus_0_r.
  elim eq_nat_dec; simpl; intros. 2: inversion H1.
  elim (set_union_elim _ _ _ _ H1); intros. inversion_clear a0.
  * apply H; eapply nth_In; eauto.
  * revert H0. inversion_clear H2; inversion H0; auto.
  * apply In_all_pids; auto.
- set (Hd' := lt_S_n (Nat.max (depth g) (vmax (map depth fs))) d Hd).
  set (Hfs := vmax_lt_map _ _ (max_lt_r _ _ _ Hd')).
  set (Hg := max_lt_l _ _ _ Hd').
  rename m into n; rename m0 into m.
  elim Nat.ltb; intro.
  * apply In_all_pids. revert H1. apply CCC_pn_all_pids_incl with (i + m + vsum (map Pi fs)).
    repeat rewrite <- plus_assoc. rewrite (plus_comm m); auto with arith.
    red; red; intros.
    apply all_pids_In. revert H1. apply seq_compose_well_ann; auto with arith.
    intros. apply IHd with Hd'0 ps q0 X' Y'; auto.
    intros; transitivity q0; auto.
  * apply In_all_pids.
    revert H1. apply CCC_pn_all_pids_incl with (i+m+Pi g).
    repeat rewrite <- plus_assoc. apply plus_le_compat_l.
    rewrite plus_comm. apply plus_le_compat_l; auto with arith.
    red; red; intros. apply all_pids_In.
    apply IHd with Hg (seq_labels (S i) fs) q (X + vsum (map Gamma fs)) Y; auto with arith.
    intros. elim (seq_labels_lt _ _ _ H2); auto with arith.
- set (Hd' := lt_S_n (Nat.max (depth g) (depth h)) d Hd).
  set (Hg := (max_lt_l _ _ _ Hd')).
  set (Hh := (max_lt_r _ _ _ Hd')).
  assert (forall p, In p (tl ps) -> p <= i+3).
  1:{ intros. transitivity i; auto with arith. apply H, In_tail; auto. }
  assert (S i <= i+3). rewrite plus_comm; simpl; auto.
  generalize (IHd _ _ Hg (tl ps) (S i) (i+3) X Y H1 H2 p).
  assert (forall p, In p (S (S i) :: S i :: tl ps) -> p <= i + 3 + Pi g).
  1: {
    intros. elim (In_elim H3); intros. rewrite <- H4, <- (plus_comm 3). auto with arith.
    elim (In_elim H4); intros. rewrite <- H5, <- (plus_comm 3). simpl; auto with arith.
    transitivity i; auto with arith. apply H, In_tail; auto.
  }
  assert (S (i + 2) <= i + 3 + Pi g). auto with arith.
  generalize (IHd _ _ Hh (S (S i) :: S i :: tl ps) (S (i + 2)) (i+3+Pi g) (X+Gamma g+2) Y H3 H4 p).
  do 2 intro.
  assert (S (S i) <= i + (Pi g + Pi h + 3)) as Hi. transitivity (i+3); auto with arith. rewrite plus_comm; simpl; auto.
  assert (S i <= i + (Pi g + Pi h + 3)) as Hi'. transitivity (i+3); auto with arith.
  assert (S (i+2) <= i + (Pi g + Pi h + 3)) as Hi''. transitivity (i+3); auto with arith.
  elim Nat.ltb. 2: elim eq_nat_dec. 3: elim eq_nat_dec. 4: elim eq_nat_dec.
  * intros.
    apply In_all_pids. revert H7. apply CCC_pn_all_pids_incl with (i+3+Pi g).
    rewrite <- plus_assoc, (plus_comm 3). auto with arith.
    red; red; intros. apply all_pids_In; eauto.
  * simpl; intros.
    elim (set_union_elim _ _ _ _ H7); intro. inversion_clear a0; inversion H8; auto.
    + rewrite <- H9; auto.
    + inversion H9.
    + apply In_all_pids; auto.
  * simpl; intros.
    elim (set_union_elim _ _ _ _ H7); intro. inversion_clear a0; inversion H8.
    + transitivity i; auto with arith. apply H. rewrite <- nth_hd. eapply nth_In; auto.
    + rewrite <- H9; auto.
    + inversion H9.
    + elim (set_union_elim _ _ _ _ b0); intro. elim (set_union_elim _ _ _ _ a0); intro.
      ++ inversion_clear a1; inversion H8; auto.
      ++ elim (set_union_elim _ _ _ _ b1); intro. inversion_clear a1.
         rewrite <- H8; auto.
         inversion_clear H8; inversion H9. rewrite <- H9. transitivity i; auto with arith.
         apply In_all_pids; auto.
      ++ apply In_all_pids; auto.
  * simpl; intros.
    elim (set_union_elim _ _ _ _ H7); intro. inversion_clear a0; inversion H8; auto.
    + rewrite <- H9; auto.
    + inversion H9.
    + elim (set_union_elim _ _ _ _ b1); intro. inversion_clear a0.
      ++ rewrite <- H8; auto.
      ++ inversion_clear H8; inversion H9; auto.
      ++ elim (set_union_elim _ _ _ _ b2); intro. inversion_clear a0.
         rewrite <- H8; auto.
         inversion_clear H8; inversion H9; auto.
         apply In_all_pids; auto.
  * rewrite (plus_comm (Pi g + Pi h)), plus_assoc, plus_assoc.
    auto.
- set (Hd' := lt_S_n (depth h) d Hd).
  assert (forall p, In p (shiftin (S (i+1)) ps) -> p <= i+3).
  1:{ intros. elim (shiftin_elim _ _ H1); auto with arith.
      intro; rewrite <- H2, plus_comm, <- (plus_comm 3); simpl; auto. }
  assert (S i <= i+3). rewrite plus_comm; simpl; auto.
  generalize (IHd _ _ Hd' _ _ _ (X+1) Y H1 H2 p); intro.
  assert (S (i+2) <= i + (Pi h + 3)) as Hi. rewrite <- (plus_comm 3); simpl; auto with arith.
  assert (S i <= i + (Pi h + 3)) as Hi'. transitivity (S (i+2)); auto with arith.
  assert (S (i+1) <= i + (Pi h + 3)) as Hi''. transitivity (S (i+2)); auto with arith.
  elim eq_nat_dec. 2: elim eq_nat_dec.
  * simpl; intros. elim (set_union_elim _ _ _ _ H4); intro. inversion_clear a0; inversion H5; auto.
    + rewrite <- H6; auto.
    + inversion H6.
    + apply In_all_pids; auto.
  * simpl; intros. elim (set_union_elim _ _ _ _ H4); intro.
    1: { inversion_clear a0; inversion H5; auto; inversion H6; auto. }
    elim (set_union_elim _ _ _ _ b0); intro.
    1: { inversion_clear a0; inversion H5; auto; inversion H6; auto. }
    elim (set_union_elim _ _ _ _ b1); intro.
    1: { elim (set_union_elim _ _ _ _ a0); intro.
        inversion_clear a1; inversion H5; auto.
        elim (set_union_elim _ _ _ _ b2); intro.
        inversion_clear a1; inversion H5; auto; inversion H6; auto.
        rewrite <- H6. transitivity i; auto with arith.
        apply In_all_pids; auto. }
    elim (set_union_elim _ _ _ _ b2); intro.
    1: { inversion_clear a0; inversion H5; auto; inversion H6; auto. }
    elim (set_union_elim _ _ _ _ b3); intro.
    1: { inversion_clear a0; inversion H5; auto; inversion H6; auto. }
    apply In_all_pids; auto.
  * rewrite (plus_comm (Pi h)), plus_assoc; auto.
Qed.

Lemma Encoding_WF : forall {n} (f:PRFunction n) ps q,
  ~In q ps -> Program_WF (Encoding f ps q).
Proof.
split. 2: repeat split.
+ apply Encoding_Main_WF.
+ apply Encoding_rec_WF; intros; auto; apply le_n_S.
  2: apply Nat.le_max_l.
  transitivity (vmax ps). 2: apply Nat.le_max_r. apply vmax_In; auto.
+ apply Encoding_rec_initial.
+ apply Encoding_Procs_Vars_not_nil.
+ red; intro. unfold Vars; simpl.
  do 2 red; intros.
  unfold Procs, Encoding, Procedures in H0.
  apply Encoding_rec_well_ann in H0.
  - apply all_pids_In; auto.
  - intros. apply Nat.max_le_iff. right; apply vmax_In; auto.
  - apply Nat.le_max_l.
Qed.

Lemma Encoding'_WF : forall {n} (f:PRFunction n),
  Program_WF (Encoding' f).
Proof.
intros; apply Encoding_WF.
intro. elim (in_vec_k_to_n _ H); intros.
inversion H0.
Qed.

End WellFormedness.
