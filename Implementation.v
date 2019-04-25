Require Export MC.
Require Export Kleene.
Require Import Coq.Program.Equality.

Local Open Scope nat_scope.

Section Implementation.

(** The type of partial functions and the notion of a choreography implementing one.
    We can only represent computable functions, but this is not a problem. *)

Definition PFunction (n:nat) := t nat n -> option nat.

Definition implements (C:Choreography) {n} (f:PFunction n) (ps:t Pid n) (q:Pid) :=
  forall (xs:t nat n) (s:State), (forall Hi, s (ps[@Hi]) = xs[@Hi]) ->
  (forall y, f xs = Some y -> exists s', (C,s) --->* (End,s') /\ s' q = y) /\
  (f xs = None -> ~exists s', (C,s) --->* (End,s')).

(** For convenience. *)
Lemma implements_None : forall C {n} f ps q, implements C f ps q -> 
  forall (xs:t nat n) (s:State), (forall Hi, s (ps[@Hi]) = xs[@Hi]) ->
  f xs = None -> ~exists s', (C,s) --->* (End,s').
unfold implements; intros.
elim (H _ _ H0); auto.
Qed.

Lemma implements_Some : forall C {n} f ps q, implements C f ps q -> 
  forall (xs:t nat n) (s:State), (forall Hi, s (ps[@Hi]) = xs[@Hi]) ->
  forall y, f xs = Some y -> exists s', (C,s) --->* (End,s') /\ s' q = y.
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

(** We recover the examples from the paper. *)
Definition C_Inc (p t:Pid) := p # this --> t; t # succ_this --> p; End.

Lemma C_Inc_char : forall p t s, let s1 := update s t (evaluate_on_state this s p) in
  (C_Inc p t, s) --->* (End, (update s1 p (evaluate_on_state succ_this s1 t))).
intros; eapply ToStep; [apply C_Com | eapply ToStep]; [apply C_Com | apply ToRefl].
Qed.

Lemma C_Inc_correct : forall p t, implements (C_Inc p t) (make_pf_1 (fun n => S n)) [p] p.
unfold make_pf_1; split; intros; inversion H0.
set (s1 := update s t (evaluate_on_state this s p)).
unfold C_Inc; exists (update s1 p (evaluate_on_state succ_this s1 t)).
split.
+ apply C_Inc_char.
+ assert (xs = [s p]).
  - apply eq_nth_iff; intros.
    rewrite <- H.
    repeat rewrite nth_hd'; auto.
  - unfold s1; clear s1; simpl.
    rewrite H1; clear H1 H2 H0 H.
    simpl; unfold update.
    repeat rewrite <- beq_nat_refl; auto.
Qed.

End Implementation.

(** * Extensions of MC
    We require some additional operators on MC for our encoding. *)

Section MC_plus.

(** ** Fat-semi. *)
Fixpoint fatsemi (C C':Choreography) : Choreography :=
  match C with
  | End => C'
  | eta; C0 => eta; fatsemi C0 C'
  | If p == q Then C1 Else C2 => If p == q Then (fatsemi C1 C') Else (fatsemi C2 C')
  end.

Notation "C ;; C'" := (fatsemi C C') (at level 90).

Fixpoint single_exit_point (C:Choreography) : Prop :=
  match C with
  | End => True
  | eta; C' => single_exit_point C'
  | If p == q Then C1 Else C2 => (single_exit_point C1) \/ (single_exit_point C2)
  end.

Lemma fatsemi_precongr : forall C C1 C2, C1 ~<= C2 -> (C1;;C) ~<= (C2;;C).
intros; induction H.
+ apply Refl.
+ apply Trans with (C2;;C); auto; clear C3 H0 IHPrecongr.
  induction H.
  - apply SRefl.
  - apply EtaEta; auto.
  - apply EtaCond; auto.
  - apply CondEta; auto.
  - apply CondCond; auto.
  - apply CtxEta; auto.
  - apply CtxThen; auto.
  - apply CtxElse; auto.
Qed.

Lemma fatsemi_End : forall C, (C;;End) = C.
induction C; simpl; auto.
+ rewrite IHC; auto.
+ rewrite IHC1; rewrite IHC2; auto.
Qed.

Lemma fatsemi_End_inv : forall C C', (C;;C') = End -> C = End /\ C' = End.
induction C; split; auto; try inversion H.
Qed.

Lemma fatsemi_To : forall C C' C'' s s', (C,s) ---> (C'',s') -> (C;;C',s) ---> (C'';;C',s').
intros.
dependent induction H.
- apply C_Com.
- apply C_Sel.
- apply C_Then; auto.
- apply C_Else; auto.
- apply C_Struct with (C1';;C') (C2';;C'); try (apply fatsemi_precongr; auto).
  apply IHMCTo; auto.
Qed.

Lemma fatsemi_ToStar : forall C C' C'' s s', (C,s) --->* (C', s') -> (C;;C'',s) --->* (C';;C'', s').
intros.
dependent induction H.
+ apply ToRefl.
+ induction c2.
  apply ToStep with (a;;C'', b); auto.
  - apply fatsemi_To; auto.
Qed.

(** Semantic characterization - Lemma 1. *)
Lemma Lemma_1_1 : forall C C' s s' s'',
  MCToStar (C,s) (End,s') -> MCToStar (C',s') (End,s'') -> MCToStar (C;;C',s) (End,s'').
intros.
apply MCToStar_trans with (C',s'); auto.
replace (C',s') with (End;;C',s'); auto; apply fatsemi_ToStar; auto.
Qed.

(** ** Function Pi *)

Fixpoint Pi {m} (f:PRFunction m) : nat :=
  match f with
  | Zero => 0
  | Successor => 0
  | Projection _ => 0
  | @Composition k _ g fs => Pi g + vsum (map Pi fs) + k
  | Recursion f g => Pi f + Pi g + 3
  | Minimization f => Pi f + 3
  end.

(*
Eval compute in (Pi PR_sub).
*)

End MC_plus.

Notation "C ;; C'" := (fatsemi C C') (at level 90).

(** * Definitions
    We have the usual problems with defining implementation: we need information about the size
    of the vector of processes that we only get with an interactive definition. *sigh*
    Even worse, because of composition we need to do induction on the depth of the function... *)
Section Definitions.

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
*)
Fixpoint seq_compose {m} {k} (fs:t (PRFunction m) k) d (Hd:forall i, depth fs[@i] < d) (ps:t Pid m) (target init:nat)
  (Implement : forall m' (f:PRFunction m') (Hd:depth f < d) (ps':t Pid m') (q' i':nat), Choreography) {struct fs} : Choreography.
(*
  match fs with
  | [] => End
  | f :: fs') => Implement m f d (Hd Fin.F1) ps target init ;; compose_args fs' ps (S target) (init + Pi f) Implement
  end.
*)
Proof.
destruct fs.
- apply End.
- apply (fatsemi (Implement m h (Hd Fin.F1) ps target init)).
  assert (forall i, depth fs[@i] < d).
  intro; apply (Hd (Fin.FS i)).
  apply (seq_compose _ _ fs d H ps (S target) (init + Pi h) Implement).
Defined.

(** Relationship to the arguments in the paper:
    - f is the function (f)
    - ps are the input processes p
    - q is the output process q
    - init is the label l
*)
Fixpoint Implementation_aux {m} (f:PRFunction m) d (Hd:depth f<d) (ps:t Pid m) (q:Pid) (init:nat) {struct d}: Choreography.
Proof.
induction d.
+ elim (Nat.nlt_0_r _ Hd).
+ destruct f; intros.

  (* Zero *)
  - apply (ps[@Fin.F1] # zero --> q; End).

  (* Successor *)
  - apply (ps[@Fin.F1] # succ_this --> q; End).

  (* Projection *)
  - apply (ps[@Fin.of_nat_lt l] # this --> q; End).

  (* Composition *)
  - simpl in Hd; generalize (lt_S_n _ _ Hd); clear Hd; intro Hd'.
    generalize (max_lt_l _ _ _ Hd').
    generalize (max_lt_r _ _ _ Hd').
    intros Hdfs Hdf.
    assert (forall i, depth fs[@i] < d).
    intros; rewrite <- nth_map'; apply vmax_lt; auto.
    apply
    ((seq_compose fs _ H ps init (init+k) (fun m f => Implementation_aux m f d));;
      Implementation_aux _ f _ Hdf (seq_labels init fs) q (init + (vsum (map Pi fs)))).

  (* Recursion *)
  - apply End.

  (* Minimization *)
  - apply End.
Defined.

(** The definition in the paper uses auxiliary process names distinct from the ps and q,
    numbered from 0. We model this by using auxiliary processes higher than the ps and q. *)
Definition Implementation {m} (f:PRFunction m) (ps:t Pid m) (q:Pid) : Choreography :=
  Implementation_aux f _ (lt_n_Sn (depth f)) ps q (S (max q (vmax ps))).

(** By default, we take process 0 for q and 1..m for the ps. *)
Definition Implementation' {m} (f:PRFunction m) : Choreography :=
  Implementation f (vec_1_to_n m) 0.

(* Sanity checks.
Eval compute in (Implementation' (Composition Successor [Zero])).
Eval compute in (Implementation' (Composition Zero [Projection aux13])).
Eval compute in (Implementation' (Composition (Projection aux22) (Zero :: [Successor]))).
*)

(** There is also a parallel variant for composition. This is defined in the same steps, but
    requires yet another auxiliary function. *)

Definition copy_input {m} (ps qs:t Pid m) : Choreography.
(*
  match m with
  | 0 => End
  | S _ => (hd ps # this --> hd qs; copy_input (tl ps) (tl qs))
  end.
*)
Proof.
induction m.
+ apply End.
+ apply (hd ps # this --> hd qs; IHm (tl ps) (tl qs)).
Defined.

Definition copy_input_iter {m} (ps:t Pid m) {n} (qs: t (t Pid m) n): Choreography.
Proof.
induction n.
+ apply End.
+ apply (copy_input ps (hd qs) ;; IHn (tl qs)).
Defined.

(** The extra argument ps_start is for the processes where the inputs in fs[@0] come from. *)
Fixpoint par_compose {m} {k} (fs:t (PRFunction m) k) d (Hd:forall i, depth fs[@i] < d) (target init ps_start:nat)
  (Implement : forall m' (f:PRFunction m') (Hd:depth f < d) (ps':t Pid m') (q' i':nat), Choreography) {struct fs} : Choreography.
Proof.
destruct fs.
- apply End.
- apply (fatsemi (Implement m h (Hd Fin.F1) (vec_k_to_n m ps_start) target init)).
  assert (forall i, depth fs[@i] < d).
  intro; apply (Hd (Fin.FS i)).
  apply (par_compose _ _ fs d H (S target) (init + Pi h) (ps_start + m) Implement).
Defined.

Fixpoint Par_Implementation_aux {m} (f:PRFunction m) d (Hd:depth f<d) (ps:t Pid m) (q:Pid) (init:nat) {struct d}: Choreography.
Proof.
induction d.
+ elim (Nat.nlt_0_r _ Hd).
+ destruct f; intros.

  (* Zero *)
  - apply (ps[@Fin.F1] # zero --> q; End).

  (* Successor *)
  - apply (ps[@Fin.F1] # succ_this --> q; End).

  (* Projection *)
  - apply (ps[@Fin.of_nat_lt l] # this --> q; End).

  (* Composition *)
  - simpl in Hd; generalize (lt_S_n _ _ Hd); clear Hd; intro Hd'.
    generalize (max_lt_l _ _ _ Hd').
    generalize (max_lt_r _ _ _ Hd').
    intros Hdfs Hdf.
    assert (forall i, depth fs[@i] < d).
    intros; rewrite <- nth_map'; apply vmax_lt; auto.
    set (init' := init + m*k).
    apply
    (copy_input_iter ps (vec_m_with_k init m k) ;;
      par_compose fs _ H init' (init'+k) init (fun m f => Par_Implementation_aux m f d);;
      Par_Implementation_aux _ f _ Hdf (seq_labels init' fs) q (init' + (vsum (map Pi fs)))).

  (* Recursion *)
  - apply End.

  (* Minimization *)
  - apply End.
Defined.

Definition Par_Implementation {m} (f:PRFunction m) (ps:t Pid m) (q:Pid) : Choreography :=
  Par_Implementation_aux f _ (lt_n_Sn (depth f)) ps q (S (max q (vmax ps))).

Definition Par_Implementation' {m} (f:PRFunction m) : Choreography :=
  Par_Implementation f (vec_1_to_n m) 0.

(* Sanity checks.
Eval compute in (Implementation' (Composition Successor [Zero])).
Eval compute in (Par_Implementation' (Composition Successor [Zero])).
Eval compute in (Implementation' (Composition Zero [Projection aux13])).
Eval compute in (Par_Implementation' (Composition Zero [Projection aux13])).
Eval compute in (Implementation' (Composition (Projection aux22) (Zero :: [Successor]))).
Eval compute in (Par_Implementation' (Composition (Projection aux22) (Zero :: [Successor]))).
*)

End Definitions.

(* We could also prove the converse: every choreography computes a computable function.
   At least without recursion... *)
