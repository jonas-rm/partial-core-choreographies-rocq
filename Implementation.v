Require Export MC.
Require Export Kleene.
Require Import Coq.Program.Equality.

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

Lemma terminated_does_not_reduce : forall C C' s s', Precongr C End -> ~MCTo (C,s) (C',s').
intros; intro.
rewrite (not_end_precongr' _ H) in H0; clear H.
dependent induction H0.
assert (C1' = End).
+ clear H1 IHMCTo C2' C' H0 s s'.
  dependent induction H; auto.
+ rewrite H2 in IHMCTo, H1; clear H C1' H2.
  apply IHMCTo with C2' s s'; auto.
Qed.

Lemma terminated_does_not_reduce_conf : forall c c', terminated c -> ~MCTo c c'.
intros.
induction c; induction c'.
rename a into C; rename a0 into C'; rename b into s; rename b0 into s'.
red in H; simpl in H.
apply terminated_does_not_reduce; auto.
Qed.

End to_be_moved.

Section Implementation.

(** The type of partial functions and the notion of a choreography implementing one.
    We can only represent computable functions, but this is not a problem. *)

Definition PFunction (n:nat) := t nat n -> option nat.

Definition implements (C:Choreography) {n} (f:PFunction n) (ps:t Pid n) (q:Pid) :=
  forall (xs:t nat n) (s:State), (forall Hi, s (ps[@Hi]) = xs[@Hi]) ->
  (forall y, f xs = Some y -> exists s', MCToStar (C,s) (End,s') /\ s' q = y) /\
  (f xs = None -> ~exists s', MCToStar (C,s) (End,s')).

(** For convenience. *)
Lemma implements_None : forall C {n} f ps q, implements C f ps q -> 
  forall (xs:t nat n) (s:State), (forall Hi, s (ps[@Hi]) = xs[@Hi]) ->
  f xs = None -> ~exists s', MCToStar (C,s) (End,s').
unfold implements; intros.
elim (H _ _ H0); auto.
Qed.

Lemma implements_Some : forall C {n} f ps q, implements C f ps q -> 
  forall (xs:t nat n) (s:State), (forall Hi, s (ps[@Hi]) = xs[@Hi]) ->
  forall y, f xs = Some y -> exists s', MCToStar (C,s) (End,s') /\ s' q = y.
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

Lemma C_Inc_char : forall p t s, let s1 := update s t (evaluate this s p) in
  MCToStar (C_Inc p t, s) (End, (update s1 p (evaluate succ_this s1 t))).
intros; eapply ToTran; apply ToSingle; apply C_Com.
Qed.

Lemma C_Inc_correct : forall p t, implements (C_Inc p t) (make_pf_1 (fun n => S n)) [p] p.
unfold make_pf_1; split; intros; inversion H0.
set (s1 := update s t (evaluate this s p)).
unfold C_Inc; exists (update s1 p (evaluate succ_this s1 t)).
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

Lemma fatsemi_precongr : forall C C1 C2, Precongr C1 C2 -> Precongr (C1;;C) (C2;;C).
intros; induction H.
+ apply Refl.
+ apply Trans with (C2;;C); auto.
+ apply EtaEta; auto.
+ apply EtaCond; auto.
+ apply CondEta; auto.
+ apply CondCond; auto.
+ apply CtxEta; auto.
+ apply CtxCond; auto.
Qed.

Lemma fatsemi_End : forall C, (C;;End) = C.
induction C; simpl; auto.
+ rewrite IHC; auto.
+ rewrite IHC1; rewrite IHC2; auto.
Qed.

Lemma fatsemi_End_inv : forall C C', (C;;C') = End -> C = End /\ C' = End.
induction C; split; auto; try inversion H.
Qed.

(** Semantic characterization - Lemma 1. *)
Lemma MCTo_inv : forall c c', MCTo c c' ->
    (exists p e q C s, c = (p#e-->q; C, s) /\ c' = (C,update s q (evaluate e s p)))
    \/ (exists p q l C s, c = (Sel p q l; C, s) /\ c' = (C,s))
    \/ (exists p q C1 C2 s, c = (If p == q Then C1 Else C2, s) /\ s p = s q /\ c' = (C1,s))
    \/ (exists p q C1 C2 s, c = (If p == q Then C1 Else C2, s) /\ s p <> s q /\ c' = (C2,s))
    \/ (exists C s C' s' C1 C2, c = (C,s) /\ c' = (C',s') /\ Precongr C C1 /\ Precongr C2 C' /\ MCTo (C1,s) (C2,s')).
intros; inversion H; auto.
+ left.
  exists p; exists e; exists q; exists C; exists s; split; auto.
+ right; left.
  exists p; exists q; exists l; exists C; exists s; split; auto.
+ right; right; left.
  exists p; exists q; exists C1; exists C2; exists s; split; auto.
+ right; right; right; left.
  exists p; exists q; exists C1; exists C2; exists s; split; auto.
+ repeat right.
  exists C1; exists s1; exists C2; exists s2; exists C1'; exists C2'; auto.
Qed.

Lemma MCToStar_inv : forall c c', MCToStar c c' ->
    c = c' \/ MCTo c c' \/ exists c'', MCToStar c c'' /\ MCToStar c'' c'.
intros; inversion H; auto.
repeat right; exists c2; auto.
Qed.

Lemma Lemma_1_To : forall C C' C'' s s', MCTo (C,s) (C'',s') -> MCTo (C;;C',s) (C'';;C',s').
intros.
dependent induction H.
- apply C_Com.
- apply C_Sel.
- apply C_Then; auto.
- apply C_Else; auto.
- apply C_Struct with (C1';;C') (C2';;C'); try (apply fatsemi_precongr; auto).
  apply IHMCTo; auto.
Qed.

Lemma Lemma_1_ToStar : forall C C' C'' s s', MCToStar (C,s) (C', s') -> MCToStar (C;;C'',s) (C';;C'', s').
intros.
dependent induction H.
+ apply ToRefl.
+ apply ToSingle; apply Lemma_1_To; auto.
+ induction c2.
  apply ToTran with (a;;C'', b); auto.
Qed.

Lemma Lemma_1_ToEnd : forall C C' s s', MCTo (C;;C',s) (End,s') ->
  {C = End /\ MCTo (C',s) (End,s')} + {C' = End /\ MCTo (C,s) (End,s')}.
double induction C C'; intros; auto;
  try (right; rewrite fatsemi_End in H0; auto);
  exfalso; clear H H0.
  - elim (MCTo_inv _ _ H1); intros; inversion_clear H.
    * inversion_clear H0; inversion_clear H; inversion_clear H0; inversion_clear H; inversion_clear H0.
      inversion H2.
      rewrite <- H3 in H; clear H4 H3 H2 H1 s' x2.

(* - Precongr preserves length
   - only length 1 reduces to End
*)

  - dependent induction H1.
    * elim (fatsemi_End_inv _ _ x); intros.
      inversion H0.
    * elim (fatsemi_End_inv _ _ x); intros.
      inversion H0.
    * apply IHMCTo with e c e0 c0 s s'.
      2: rewrite (not_end_precongr' _ H0); auto.
      simpl; rewrite H.



Lemma Lemma_1_1 : forall C C' s s' s'',
  MCToStar (C,s) (End,s') -> MCToStar (C',s') (End,s'') -> MCToStar (C;;C',s) (End,s'').
intros.
apply ToTran with (C',s'); auto.
replace (C',s') with (End;;C',s'); auto; apply Lemma_1_ToStar; auto.
Qed.

Lemma Lemma_1_2 : forall C C' s,
  (forall s', ~MCToStar (C,s) (End,s')) -> forall s', ~MCToStar (C;;C',s) (End,s').
intros; intro.
inversion H0.
+ rewrite <- H4 in H0; clear H4 s'.

(*  elim (fatsemi_End _ _ H3); intros.
  rewrite H2 in H; apply (H _ (ToRefl _)).
+ clear H1 H2 c1 c2.
  induction C; simpl in P; try clear IHC.
  - apply (H _ (ToRefl _)).
  - apply (H s'); apply ToSingle.
    inversion P.
    * elim (fatsemi_End _ _ H5); intros.
      rewrite H1; rewrite H7; apply C_Com.
    * elim (fatsemi_End _ _ H5); intros.
      rewrite H1; rewrite H7; apply C_Sel.
    * clear C1 C2 s1 s2 H1 H2 H3 H4.


  inversion P.
  - rewrite H4 in H2; clear H4 H3 s0 C0.

*)



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
