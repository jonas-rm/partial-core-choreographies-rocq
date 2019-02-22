Require Export MC.
Require Export Kleene.

Section to_be_moved.

Lemma max_lt_l : forall k m n, max m n < k -> m < k.
intro; case_eq k; intros.
inversion H0.
generalize (le_S_n _ _ H0); intros.
apply le_n_S.
eapply Nat.max_lub_l; exact H1.
Qed.

Lemma max_lt_r : forall k m n, max m n < k -> n < k.
intros; apply max_lt_l with m.
rewrite Nat.max_comm; auto.
Qed.

Lemma vmax_lt : forall n v x, vmax (n:=n) v < x -> forall p, v[@p] < x.
Proof.
induction p.
* revert n v H; refine (@caseS _ _ _); simpl; intros.
  eapply max_lt_l; exact H.
* revert n v H p IHp; refine (@caseS _ _ _); simpl; intros.
  apply IHp; eapply max_lt_r; exact H.
Qed.

(** Vector containing the numbers k to k+n. *)
Fixpoint vec_k_to_n n k : t nat n :=
  match n with
  | 0 => []
  | S m => k :: vec_k_to_n m (S k)
  end.

Definition vec_1_to_n n : t nat n := vec_k_to_n n 1.

(** Vector of vectors with values [[m; ...; m+n-1] [m+n; ...; m+2n-1] ... [m+(k-1)n; ...; m+kn-1]]. *)
Fixpoint vec_m_with_k m k n :=
  match k with
  | 0 => []
  | S k' => (vec_k_to_n n m :: vec_m_with_k (m+n) k' n)
  end.

(** Sum of a vector of natural numbers. *)
Fixpoint vsum {n} (v:t nat n) :=
  match v with
  | [] => 0
  | x :: xs => x + vsum xs
end.

End to_be_moved.

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

Fixpoint single_exit_point (C:Choreography) : bool :=
  match C with
  | End => true
  | eta; C' => single_exit_point C'
  | If p == q Then C1 Else C2 => xorb (single_exit_point C1) (single_exit_point C2)
  end.

(** Missing semantic characterization. *)

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
    (seq_compose fs _ H ps init (init+k) (fun m f => Implementation_aux m f d);;
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
