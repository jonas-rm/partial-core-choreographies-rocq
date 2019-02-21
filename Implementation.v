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

Eval compute in (Pi PR_sub).

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

Fixpoint compose_args {m} {k} (fs:t (PRFunction m) k) d (Hd:forall i, depth fs[@i] < d) (ps:t Pid m) (target:nat) (init:nat)
  (Implement : forall m' (f:PRFunction m') (Hd:depth f < d) (ps':t Pid m') (q' i':nat), Choreography) {struct fs} : Choreography.
Proof.
destruct fs.
- apply End.
- apply (fatsemi (Implement m h (Hd Fin.F1) ps target init)).
  assert (forall i, depth fs[@i] < d).
  intro; apply (Hd (Fin.FS i)).
  apply (compose_args _ _ fs d H ps (S target) (init + Pi h) Implement).
Defined.

(*
  match fs with
  | [] => End
  | f :: fs') => Implement m f d (Hd Fin.F1) ps target init ;; compose_args fs' ps (S target) (init + Pi f) Implement
  end.
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
    (compose_args fs _ H ps init (init+k) (fun m f => Implementation_aux m f d);;
      Implementation_aux _ f _ Hdf (skip_labels (init+k) fs) (init + (vsum (map Pi fs))) q).

  (* Recursion *)
  - apply End.

  (* Minimization *)
  - apply End.
Defined.

Definition Implementation {m} (f:PRFunction m) (ps:t Pid m) (q:Pid) : Choreography :=
  Implementation_aux f _ (lt_n_Sn (depth f)) ps q 0.

Eval compute in (Implementation (Composition Zero [Projection aux13]) (2 :: 1 :: [0]) 5).

End Definitions.
