Require Export Basic.
Require Export Vector.
Import VectorNotations.

(** * Definitions
    Our class of partial recursive functions, together with their semantics. *)
Section Definitions.

Inductive PRFunction : nat -> Set :=
  | Zero         : PRFunction 1
  | Successor    : PRFunction 1
  | Projection   : forall {m k:nat}, k < m -> PRFunction m
  | Composition  : forall {k m:nat} (g:PRFunction m) (fs:t (PRFunction k) m), PRFunction k
  | Recursion    : forall {k:nat} (g:PRFunction k) (h:PRFunction (2+k)), PRFunction (1+k)
  | Minimization : forall {k:nat} (h:PRFunction (1+k)), PRFunction k
.

(** Kleene is imprecise about how e.g. composition should behave on undefined arguments:
    does should (Composition g fs) be undefined if one of the fs is undefined, even if
    its value is never used? We believe the second approach to be the case (it is what 
    is assumed in typical proofs of Turing completeness). *)
Fixpoint all_defined {n} (v:t (option nat) n) : bool :=
  match v with
  | []             => true
  | (Some _) :: v' => all_defined v'
  | None :: _      => false
end.

(** Auxiliary function for minimization: we need to specify how many computation steps we
    want to allow, as all Coq functions must be total. We do a &dlquote;diagonal&urquote;
    search. *)
Fixpoint find_zero_from {k} (f:t (option nat) (1+k) -> option nat) (ns:t (option nat) k) (init:nat) (steps:nat) : option nat :=
  match steps with
  | O   => None
  | S m => match f (shiftin (Some init) ns) with
           | None       => None
           | Some O     => Some init
           | Some (S _) => find_zero_from f ns (S init) m
end end.

(** We'd love a readable definition of evaluation, but the dependent type of f makes it
    tricky to write. So... *)
(** First we define the fixpoint construction over the option type, to cater for undefinedness. *)
Fixpoint eval_opt {m} (f:PRFunction m) : forall (steps:nat) (ns:t (option nat) m), option nat.
destruct f; intros.

(* Zero *)
+ apply
  match (hd ns) with
    | Some x => Some 0
    | None => None
    end.

(* Successor *)
+ apply
    match (hd ns) with
    | Some x => Some (x + 1)
    | None => None
    end.

(* Projection *)
+ apply
  (if (all_defined ns) then (nth ns (Fin.of_nat_lt l)) else None).

(* Composition *)
+ set (ms := (map_inv (map_inv (map (eval_opt _) fs) steps) ns)).
  apply (if (all_defined ms) && (all_defined ns) then (eval_opt _ f steps ms) else None).

(* Recursion *)
+ elim (hd ns); [idtac 1 | apply None].              (* is there an argument? *)
  intro n; induction n.                              (* finally *)
  apply (eval_opt _ f1 steps (tl ns)).               (* f x1...xn *)
  destruct IHn; [rename n0 into x | apply None].
  apply (eval_opt _ f2 steps (Some n :: Some x :: tl ns)).

(* Minimization *)
+ destruct steps.
  - apply None.
  - apply (find_zero_from (eval_opt _ f steps) ns 0 steps).
Defined.

(** This is the evaluation function we actually want to use. *)
Definition eval {m} (f:PRFunction m) (steps:nat) (ns:t nat m) : option nat := eval_opt f steps (map Some ns).

End Definitions.

(** ª Sanity checks
    Our first goal is to prove that evaluation works as expected.
    This requires some preliminary properties about the auxiliary functions. *)
Section Auxiliary_Lemmas.

(** Predicate all_defined works as expected. *)
Lemma all_defined_map_Some : forall n v, all_defined (n:=n) (map Some v) = true.
Proof.
induction n; simpl; intros.
+ replace v with (nil nat); [auto | apply vector_0_inv].
+ rewrite (eta v); simpl; auto.
Qed.

Lemma all_defined_false : forall n v, all_defined (n:=n) v = false -> exists Hi, v[@Hi] = None.
Proof.
induction n; simpl; intros.
+ replace v with (nil (option nat)) in H; [inversion H | apply vector_0_inv].
+ rewrite (eta v) in H; simpl in H.
  revert H; case_eq (hd v); intros.
  - elim (IHn _ H0); intros.
    exists (Fin.FS x).
    rewrite nth_tl; auto.
  - exists (Fin.F1).
    rewrite nth_hd; auto.
Qed.

Lemma all_defined_true : forall n v, all_defined (n:=n) v = true -> forall Hi, v[@Hi] <> None.
Proof.
intros; intro.
induction n.
+ inversion Hi.
+ rewrite (eta v) in H.
  revert H; case_eq (hd v); intros.
  - generalize (IHn _ H1); clear IHn H1; intros.
    elim (eta_elim _ _ _ H0); intros.
    * rewrite H2 in H; inversion H.
    * elim H2; eapply H1; assumption.
  - inversion H1.
Qed.

Lemma all_defined_false' : forall n v Hi, v[@Hi] = None ->  all_defined (n:=n) v = false.
intros.
case_eq (all_defined v); intros; auto.
generalize (all_defined_true _ _ H0); intros.
elim (H1 Hi); auto.
Qed.

(** If find_zero_from returns a value (Some n), then we know that f(n)=0,
    but also that f is positive for all values between the initial one and n.
    Furthermore, the number of values we tested is bounded by the first parameter. *)
Lemma find_zero_from_Some : forall steps {k} f (ns:t (option nat) k) init m, find_zero_from f ns init steps = Some m ->
  m < init + steps /\ f (shiftin (Some m) ns) = Some O /\ forall n, init <= n < m -> exists val, f (shiftin (Some n) ns) = Some (S val).
induction steps; intros.
+ inversion H.
+ revert H; simpl.
  case_eq (f (shiftin (Some init) ns)).
  destruct n; intros.
  - inversion H0; repeat split.
    * rewrite plus_comm; simpl; auto with arith.
    * rewrite <- H2; auto.
    * intros; elim (lt_irrefl m).
      inversion_clear H1; apply le_lt_trans with n; auto.
  - elim (IHsteps _ _ _ _ _ H0); intros; split.
    * rewrite plus_comm; simpl; rewrite plus_comm; auto with arith.
    * inversion_clear H2; split; auto.
      intros; inversion_clear H2.
      elim (le_lt_eq_dec _ _ H5); intro.
      ++ apply H4; auto with arith.
      ++ exists n; rewrite <- b; auto.
  - intros; inversion H0.
Qed.

(** For convenience, we split these properties in separate lemmas. *)
Lemma find_zero_from_bound : forall steps {k} f (ns:t (option nat) k) init m,
  find_zero_from f ns init steps = Some m -> m < init + steps.
intros; elim (find_zero_from_Some steps f ns init m); auto.
Qed.

Lemma find_zero_from_value : forall steps {k} f (ns:t (option nat) k) init m,
  find_zero_from f ns init steps = Some m -> f (shiftin (Some m) ns) = Some O.
intros; elim (find_zero_from_Some steps f ns init m); intros; auto.
inversion H1; auto.
Qed.

Lemma find_zero_from_middle : forall steps {k} f (ns:t (option nat) k) init m,
  find_zero_from f ns init steps = Some m -> forall n, init <= n < m -> exists val, f (shiftin (Some n) ns) = Some (S val).
intros; elim (find_zero_from_Some steps f ns init m); intros; auto.
inversion_clear H2; auto.
Qed.

(** Furthermore, if f has other zeros, they must lie outside the range we tested. *)
Lemma find_zero_from_min : forall steps {k} f (ns:t (option nat) k) init m, find_zero_from f ns init steps = Some m ->
  forall n, f (shiftin (Some n) ns) = Some 0 -> n < init \/ m <= n.
intros.
elim (le_lt_dec m n); auto; intro.
elim (le_lt_dec init n); auto; intro.
generalize (find_zero_from_middle _ _ _ _ _ H); intros.
elim (H1 n); auto; intros.
rewrite H2 in H0; inversion H0.
Qed.

(** The negative counterpart: if find_zero returns None, then f is either undefined at least once
    in the range tested (for the given number of steps), or it is always positive. *)
Lemma find_zero_from_None : forall steps {k} f (ns:t (option nat) k) init,
  find_zero_from f ns init steps = None ->
  { exists n, init <= n < init + steps /\ f (shiftin (Some n) ns) = None /\
              forall k, init <= k < n -> exists val, f (shiftin (Some k) ns) = Some (S val)} +
  { forall n, init <= n < init + steps -> exists val, f (shiftin (Some n) ns) = Some (S val) }.
induction steps; intros.
+ right; simpl; intros.
  inversion_clear H0.
  elim (lt_irrefl n).
  apply lt_le_trans with init; auto.
  replace init with (init + 0); auto.
+ revert H; simpl.
  case_eq (f (shiftin (Some init) ns)); intros.
  revert H0; case_eq n; intros.
  inversion H1.
  rewrite H0 in H; clear H0 n; rename n0 into n.
  elim (IHsteps _ _ _ _ H1); clear IHsteps H1; intros.
  - left; inversion_clear a.
    inversion_clear H0; inversion_clear H1; inversion_clear H2.
    exists x; repeat split; auto with arith.
    * replace (init + S steps) with (S init + steps); auto with arith.
      rewrite (plus_comm init (S steps)); simpl; auto with arith.
    * intros; inversion_clear H2.
      inversion H5; [exists n; rewrite <- H2 | apply H4]; repeat split; auto with arith.
      rewrite H7; auto.
  - right; intros.
    inversion_clear H0.
    replace (init + S (steps)) with (S (steps + init)) in H2.
    2: rewrite (plus_comm init (S steps)); simpl; auto with arith.
    inversion H1.
    * exists n; rewrite <- H0; auto.
    * apply b; split; auto with arith.
      rewrite H3; rewrite plus_comm in H2; simpl; auto with arith.
  - left; exists init; repeat split; auto with arith.
    * rewrite (plus_comm init (S steps)); simpl; auto with arith.
    * intros; elim (lt_irrefl init); apply le_lt_trans with k0; inversion_clear H1; auto.
Qed.

End Auxiliary_Lemmas.

(** Since our definition of eval is very indirect, we now prove that it behaves as expected. *)
Section Sanity_Checks.

Lemma Zero_correct : forall n steps, eval Zero steps [n] = Some 0.
compute; auto.
Qed.

Lemma Successor_correct : forall n steps, eval Successor steps [n] = Some (S n).
intros; unfold eval; simpl.
replace (n+1) with (S n); auto.
rewrite plus_comm; auto.
Qed.

Lemma Projection_correct : forall m k (Hkm: k<m) n steps, eval (Projection Hkm) steps n = Some (nth n (Fin.of_nat_lt Hkm)).
intros; unfold eval; simpl.
rewrite all_defined_map_Some.
apply nth_map'.
Qed.

Lemma Composition_correct : forall k m (g:PRFunction m) (f:t (PRFunction k) m) (ns:t nat k) (ms:t nat m) steps,
  (forall Hi, eval (nth f Hi) steps ns = Some (nth ms Hi)) -> eval g steps ms = eval (Composition g f) steps ns.
intros; unfold eval; simpl.
case_eq (all_defined (map_inv (map_inv (map eval_opt f) steps) (map Some ns))); simpl; intro.
+ replace (all_defined (map Some ns)) with true.
  - replace (map Some ms) with (map_inv (map_inv (map eval_opt f) steps) (map Some ns)); auto.
    apply eq_nth_iff; intros.
    rewrite <- H1; clear H1 p2.
    rewrite nth_map'.
    rewrite <- H; clear H.
    repeat rewrite nth_map_inv'.
    rewrite nth_map'; auto.
  - symmetry; apply all_defined_map_Some.
+ exfalso.
  elim (all_defined_false _ _ H0); intros.
  repeat rewrite nth_map_inv' in H1; rewrite nth_map' in H1.
  generalize (H x); intro.
  unfold eval in H2; rewrite H2 in H1.
  inversion H1.
Qed.

Lemma Recursion_correct_base : forall k (g:PRFunction k) (h:PRFunction (2+k)) (ns:t nat (1+k)) steps,
  hd ns = 0 -> eval (Recursion g h) steps ns = eval g steps (tl ns).
intros; unfold eval.
revert k ns g h H; refine (@caseS _ _ _).
simpl; intros; rewrite H; auto.
Qed.

Lemma Recursion_correct_step : forall k (g:PRFunction k) (h:PRFunction (2+k)) (ns:t nat (1+k)) steps x y,
  hd ns = S x -> (eval (Recursion g h) steps (x :: tl ns)) = Some y ->
  eval (Recursion g h) steps ns = eval h steps (x :: y :: tl ns).
intros.
revert k ns g h x H y H0; refine (@caseS _ _ _).
simpl; intros.
unfold eval; rewrite H.
unfold eval in H0.
simpl (map Some (S x :: t)).
simpl (map Some (x :: y :: t)).
simpl (map Some (x :: t)) in H0.
simpl; simpl in H0; rewrite H0; auto.
Qed.

Lemma Minimization_correct : forall k (h:PRFunction (1+k)) (ns:t nat k) steps n,
  eval (Minimization h) steps ns = (Some n) ->
  exists s, eval h s (shiftin n ns) = (Some 0) /\ forall m, m < n -> exists n', eval h s (shiftin m ns) = (Some (S n')).
intros; revert H; unfold eval.
induction steps.
+ simpl; intros; inversion H.
+ simpl; intro.
  generalize (find_zero_from_value _ _ _ _ _ H); intros.
  generalize (find_zero_from_middle _ _ _ _ _ H); intros; exists steps.
  rewrite map_shiftin; split; auto.
  intros; rewrite map_shiftin; apply H1; split; auto with arith.
Qed.

End Sanity_Checks.

(** Tactics for dealing with proofs involving composition. *)

Ltac prove_composition_1 := intros;
                            do 2 rewrite <- nth_map';
                            do 2 rewrite <- nth_map_inv';
                            apply vector_1_equal;
                            auto.

Ltac prove_composition_2 := intros;
                            do 2 rewrite <- nth_map';
                            do 2 rewrite <- nth_map_inv';
                            apply vector_2_equal;
                            auto.

Ltac prove_composition_3 := intros;
                            do 2 rewrite <- nth_map';
                            do 2 rewrite <- nth_map_inv';
                            apply vector_3_equal;
                            auto.

(** * Examples
    We now recover the examples from the submitted journal paper. *)
Section Examples.

(** These lemmas are used to define projections. Their names seem inconsistent, but they refer to the usual convention for naming projections. *)
Lemma aux11 : 0 < 1.
auto with arith.
Qed.

Lemma aux12 : 0 < 2.
auto with arith.
Qed.

Lemma aux22 : 1 < 2.
auto with arith.
Qed.

Lemma aux13 : 0 < 3.
auto with arith.
Qed.

Lemma aux23 : 1 < 3.
auto with arith.
Qed.

Lemma aux33 : 2 < 3.
auto with arith.
Qed.

(** ** Addition. *)
Definition PR_add := Recursion (Projection aux11) (Composition Successor [Projection aux23]).

Eval compute in (eval PR_add 0 [2; 3]).
Eval compute in (eval PR_add 0 [5; 7]).

(* OMG *)
Lemma add_correct : forall m n steps, eval PR_add steps [m; n] = Some (m + n).
intros; induction m.
+ simpl; auto.
+ unfold PR_add.
  rewrite Recursion_correct_step with (x:=m) (y:=m+n); auto.
  unfold eval; simpl.
  replace (m+n+1) with (S (m+n)); auto.
  rewrite (plus_comm (m+n) 1); auto with arith.
Qed.

(** ** Multiplication. *)
Definition PR_mult := Recursion Zero (Composition PR_add [Projection aux33; Projection aux23]).

Eval compute in (eval PR_mult 0 [2; 3]).
Eval compute in (eval PR_mult 0 [5; 7]).

Lemma mult_correct : forall m n steps, eval PR_mult steps [m; n] = Some (m * n).
intros; induction m.
+ simpl; auto.
+ unfold PR_mult.
  rewrite Recursion_correct_step with (x:=m) (y:=m*n); simpl; auto.
  rewrite <- Composition_correct with (ms := [n; m*n]).
  - apply add_correct.
  - prove_composition_2.
Qed.

(** ** Sign function. *)
Definition PR_sign := Composition
  (Recursion Zero(Composition Successor [Composition Zero [Projection aux23]]))
  [Projection aux11; Projection aux11].

Eval compute in (eval PR_sign 0 [32]).
Eval compute in (eval PR_sign 0 [0]).

Lemma sign_correct_0 : forall steps, eval PR_sign steps [0] = Some (0).
intros; simpl; auto.
Qed.

Lemma sign_correct_S : forall n steps, eval PR_sign steps [S n] = Some (1).
intros; induction n.
simpl; auto.
unfold PR_sign.
revert IHn; unfold eval; simpl; intro.
rewrite IHn; auto.
Qed.

(** ** Predecessor. *)
Definition PR_pred := Composition (Recursion Zero (Projection aux13)) [Projection aux11; Zero].

Eval compute in (eval PR_pred 0 [32]).
Eval compute in (eval PR_pred 0 [0]).

Lemma pred_correct : forall n steps, eval PR_pred steps [n] = Some (pred n).
intros; unfold PR_pred.
rewrite <- Composition_correct with (ms := [n; 0]).
+ induction n.
  - rewrite Recursion_correct_base; auto.
  - rewrite Recursion_correct_step with (x := n) (y := pred n); auto.
+ prove_composition_2.
Qed.

(** ** Natural (total) subtraction. *)
Definition PR_minus := Composition (Recursion (Projection aux11) (Composition PR_pred [Projection aux23]))
  [Projection aux22; Projection aux12].

Eval compute in (eval PR_minus 0 [3; 2]).
Eval compute in (eval PR_minus 0 [7; 5]).
Eval compute in (eval PR_minus 0 [2; 3]).

Lemma minus_correct : forall m n steps, eval PR_minus steps [n; m] = Some (n - m).
intros; unfold PR_minus.
rewrite <- Composition_correct with (ms := [m; n]).
* induction m.
  + rewrite Recursion_correct_base; auto; rewrite <- minus_n_O; auto.
  + rewrite Recursion_correct_step with (x := m) (y := n - m); simpl; auto.
    replace (n - S m) with (pred (n - m)).
    - rewrite <- Composition_correct with (ms := [n-m]).
      ** apply pred_correct.
      ** prove_composition_1.
    - rewrite minus_S; auto.
* prove_composition_2.
Qed.

(** ** Greater than. *)
Definition PR_gt := Composition PR_sign [PR_minus].

Lemma gt_correct_true : forall m n steps, n > m -> eval PR_gt steps [n; m] = Some 1.
intros; unfold PR_gt.
rewrite <- Composition_correct with (ms := [n-m]).
+ red in H.
  elim (minus_is_S m n H); intros k Hk.
  rewrite Hk; apply sign_correct_S.
+ prove_composition_1.
  rewrite minus_correct; auto.
Qed.

Lemma gt_correct_false : forall m n steps, n <= m -> eval PR_gt steps [n; m] = Some 0.
intros; unfold PR_gt.
rewrite <- Composition_correct with (ms := [n-m]).
+ rewrite (not_lt_minus_0 n m); auto with arith.
+ prove_composition_1.
  rewrite minus_correct; auto.
Qed.

Lemma gt_correct_1 : forall m n steps, n > m <-> eval PR_gt steps [n; m] = Some 1.
split.
+ apply gt_correct_true.
+ intro; elim (le_lt_dec n m); auto.
  intro; rewrite gt_correct_false in H; auto.
  inversion H.
Qed.

Lemma gt_correct_0 : forall m n steps, n <= m <-> eval PR_gt steps [n; m] = Some 0.
split.
+ apply gt_correct_false.
+ intro; elim (le_lt_dec n m); auto.
  intro; rewrite gt_correct_true in H; auto.
  inversion H.
Qed.

(** ** Less or equal. *)
Definition PR_le := Composition PR_minus [Composition Successor [Composition Zero [Projection aux12]]; PR_gt].

Lemma le_correct_true : forall m n steps, m <= n -> eval PR_le steps [m; n] = Some 1.
intros; unfold PR_le.
rewrite <- Composition_correct with (ms := [1; 0]).
+ rewrite minus_correct; auto with arith.
+ prove_composition_2.
  apply gt_correct_false; auto.
Qed.

Lemma le_correct_false : forall m n steps, n < m -> eval PR_le steps [m; n] = Some 0.
intros; unfold PR_le.
rewrite <- Composition_correct with (ms := [1; 1]).
+ rewrite minus_correct; auto with arith.
+ prove_composition_2.
  apply gt_correct_true; auto.
Qed.

Lemma le_correct_1 : forall m n steps, m <= n <-> eval PR_le steps [m; n] = Some 1.
split.
+ apply le_correct_true.
+ intro; elim (le_lt_dec m n); auto.
  intro; rewrite le_correct_false in H; auto.
  inversion H.
Qed.

Lemma le_correct_0 : forall m n steps, n < m <-> eval PR_le steps [m; n] = Some 0.
split.
+ apply le_correct_false.
+ intro; elim (le_lt_dec m n); auto.
  intro; rewrite le_correct_true in H; auto.
  inversion H.
Qed.

(** ** Equality. *)
Definition PR_equal := Composition PR_mult [PR_le; Composition PR_le [Projection aux22; Projection aux12]].

Lemma equal_correct_true : forall m n steps, m = n -> eval PR_equal steps [m; n] = Some 1.
intros; unfold PR_equal.
rewrite <- Composition_correct with (ms := [1; 1]).
+ rewrite mult_correct; auto with arith.
+ prove_composition_2; apply le_correct_true; rewrite H; auto.
Qed.

Lemma equal_correct_false : forall m n steps, m <> n -> eval PR_equal steps [m; n] = Some 0.
intros; unfold PR_equal.
elim (not_eq _ _ H); intro.
- rewrite <- Composition_correct with (ms := [1; 0]).
  + rewrite mult_correct; auto with arith.
  + prove_composition_2.
    * apply le_correct_true; auto with arith.
    * apply le_correct_false; auto.
- rewrite <- Composition_correct with (ms := [0; 1]).
  + rewrite mult_correct; auto with arith.
  + prove_composition_2.
    * apply le_correct_false; auto.
    * apply le_correct_true; auto with arith.
Qed.

Lemma equal_correct_1 : forall m n steps, m = n <-> eval PR_equal steps [m; n] = Some 1.
split.
+ apply equal_correct_true.
+ intro; elim (Nat.eq_dec m n); auto.
  intro; rewrite equal_correct_false in H; auto.
  inversion H.
Qed.

Lemma equal_correct_0 : forall m n steps, m <> n <-> eval PR_equal steps [m; n] = Some 0.
split.
+ apply equal_correct_false.
+ intro; elim (Nat.eq_dec m n); auto.
  intro; rewrite equal_correct_true in H; auto.
  inversion H.
Qed.

(** ** Inequality. *)
Definition PR_diff := Composition PR_add [PR_gt; Composition PR_gt [Projection aux22; Projection aux12]].

Lemma diff_correct_true : forall m n steps, m <> n -> eval PR_diff steps [m; n] = Some 1.
intros; unfold PR_diff.
elim (not_eq _ _ H); intro.
- rewrite <- Composition_correct with (ms := [0; 1]).
  + rewrite add_correct; auto.
  + prove_composition_2.
    * apply gt_correct_false; auto with arith.
    * apply gt_correct_true; auto.
- rewrite <- Composition_correct with (ms := [1; 0]).
  + rewrite add_correct; auto.
  + prove_composition_2.
    * apply gt_correct_true; auto.
    * apply gt_correct_false; auto with arith.
Qed.

Lemma diff_correct_false : forall m n steps, m = n -> eval PR_diff steps [m; n] = Some 0.
intros; unfold PR_diff.
rewrite <- Composition_correct with (ms := [0; 0]).
+ rewrite add_correct; auto.
+ prove_composition_2; apply gt_correct_false; rewrite H; auto.
Qed.

Lemma diff_correct_1 : forall m n steps, m <> n <-> eval PR_diff steps [m; n] = Some 1.
split.
+ apply diff_correct_true.
+ intro; elim (Nat.eq_dec m n); auto.
  intro; rewrite diff_correct_false in H; auto.
  inversion H.
Qed.

Lemma diff_correct_0 : forall m n steps, m = n <-> eval PR_diff steps [m; n] = Some 0.
split.
+ apply diff_correct_false.
+ intro; elim (Nat.eq_dec m n); auto.
  intro; rewrite diff_correct_true in H; auto.
  inversion H.
Qed.

(** ** Subtraction.
    (Finally.) *)
Definition PR_sub_aux := Composition PR_diff [Composition PR_add [Projection aux23; Projection aux33]; Projection aux13].
Definition PR_sub := Minimization PR_sub_aux.

(** By the way, there is a typo in the definition of sub in the paper... *)

Lemma sub_aux_correct : forall m n k steps, eval PR_sub_aux steps [m; n; k] = Some 0 <-> m = n + k.
intros; unfold PR_sub_aux.
rewrite <- Composition_correct with (ms := [k+n; m]).
- rewrite <- diff_correct_0.
  rewrite plus_comm; split; auto.
- prove_composition_2.
  * rewrite <- Composition_correct with (ms := [n; k]).
    + rewrite plus_comm; apply add_correct.
    + prove_composition_2.
Qed.

Lemma sub_correct_1 : forall m n steps k, eval PR_sub steps [m; n] = Some k -> k = m - n.
intros.
unfold PR_sub in H.
generalize (Minimization_correct _ _ _ _ _ H); intro.
simpl shiftin in H0.
elim H0; clear H H0 steps; intros steps Hsteps; inversion_clear Hsteps.
clear H0.
rewrite sub_aux_correct in H.
apply plus_minus; auto.
Qed.

Lemma sub_correct_2 : forall m n steps k, eval PR_sub steps [m; n] = Some k -> n <= m.
intros.
generalize (sub_correct_1 _ _ _ _ H); intro; revert H.
destruct steps.
- intro; inversion H.
- change ((find_zero_from (eval_opt PR_sub_aux steps) [Some m; Some n] 0 steps) = Some k -> n <= m).
  intro.
  elim (le_lt_dec n m); intro; auto.
  generalize (find_zero_from_value _ _ _ _ _ H); intros.
  clear H; change (eval PR_sub_aux steps [m; n; k] = Some 0) in H1.
  rewrite sub_aux_correct in H1.
  rewrite not_le_minus_0 in H0; auto with arith.
  rewrite H0 in H1; rewrite plus_comm in H1.
  rewrite H1; auto with arith.
Qed.

End Examples.

(** * Evaluation
    Here we include several lemmas about evaluation. *)

Section Evaluation.

Lemma eval_opt_on_None : forall m (f:PRFunction m) steps ns Hi, ns[@Hi] = None -> eval_opt f steps ns = None.
induction f; intros.
+ simpl.
  replace (hd ns) with (None (A:=nat)); auto.
  rewrite <- H; rewrite <- (vector_1_inv ns) at 1.
  rewrite nth_hd'; auto.
+ simpl.
  replace (hd ns) with (None (A:=nat)); auto.
  rewrite <- H; rewrite <- (vector_1_inv ns) at 1.
  rewrite nth_hd'; auto.
+ simpl.
  case_eq (all_defined ns); intro; auto.
  rewrite (all_defined_false' _ _ _ H) in H0; inversion H0.
+ simpl.
  replace (all_defined ns) with false.
  rewrite andb_false_r; auto.
  symmetry; apply all_defined_false' with Hi; auto.
+ case_eq (hd ns); intros.
  2: simpl; rewrite H0; auto.
  elim (eta_elim _ _ _ H); intro.
  - rewrite H1 in H0; inversion H0.
  - inversion_clear H1.
    clear H Hi; revert ns H0 x H2.
    induction n; intros; simpl.
    * rewrite H0; simpl.
      apply IHf1 with x; auto.
    * rewrite H0; simpl.
      generalize (IHn (Some n :: tl ns) (eq_refl _) x H2); clear IHn; intros.
      simpl in H; rewrite H; auto.
+ case_eq steps; intros; auto.
  clear H0 steps; simpl.
  case_eq n; intros; simpl; auto.
  rewrite <- H0.
  rewrite <- (shiftin_nth _ (Some 0) _ ns _ _ (eq_refl Hi)) in H.
  set (ms := shiftin (Some 0) ns).
  case_eq (eval_opt f n ms); simpl; intros; rewrite H1; auto.
  exfalso.
  clear H0 n0; revert H1.
  rewrite IHf with (Hi := Fin.L_R 1 Hi); auto.
  intro; inversion H1.
Qed.

(** We need to do induction on the depth in order to get an induction hypothesis that works
    for composition. All lemmas are thereafter generalized so that this premise is removed. *)
Fixpoint depth {m} (f:PRFunction m) : nat :=
  match f with
  | Zero             => 0
  | Successor        => 0
  | Projection _     => 0
  | Composition g fs => 1 + Nat.max (depth g) (vmax (map depth fs))
  | Recursion g h    => 1 + Nat.max (depth g) (depth h)
  | Minimization h   => 1 + depth h
end.

(** Properties:
    - evaluation is injective (it cannot return two different values)
    - if evaluation returns a value, this is preserved when the maximum number of steps
      is increased
    - if evaluation does not return a value (yet), then neither does it for less steps. *)
Lemma eval_opt_inj_lemma : forall d n (f:PRFunction n) s s' ns m m', depth f <= d ->
  eval_opt f s ns = Some m -> eval_opt f s' ns = Some m' -> m = m'.
induction d; intros m f.
- induction f; intros; try (inversion H; fail); revert H0 H1;
    simpl; intros; rewrite H0 in H1; inversion H1; auto.
- induction f; intros; revert H0 H1.
  (* the first three cases are the same *)
  + simpl; intros; rewrite H0 in H1; inversion H1; auto.
  + simpl; intros; rewrite H0 in H1; inversion H1; auto.
  + simpl; intros; rewrite H0 in H1; inversion H1; auto.
  + simpl in H; apply le_S_n in H.
    generalize (Nat.max_lub_l _ _ _ H); generalize (Nat.max_lub_r _ _ _ H); clear H.
    simpl; do 2 intro.
    case_eq (all_defined (map_inv (map_inv (map eval_opt fs) s) ns)); intro; simpl.
    2: intros; inversion H2.
    case_eq (all_defined (map_inv (map_inv (map eval_opt fs) s') ns)); intro; simpl.
    2: intros; inversion H4.
    case_eq (all_defined ns); intro; simpl.
    2: intros; inversion H4.
    replace (map_inv (map_inv (map eval_opt fs) s) ns) with (map_inv (map_inv (map eval_opt fs) s') ns).
    apply IHf; auto.
    apply eq_nth_iff'; intros.
    repeat rewrite nth_map_inv'; rewrite nth_map'; auto.
    generalize (all_defined_true _ _ H1 p); clear H1; intro.
    repeat rewrite nth_map_inv' in H1.
    rewrite nth_map' in H1.
    generalize (all_defined_true _ _ H2 p); clear H2; intro.
    repeat rewrite nth_map_inv' in H2.
    rewrite nth_map' in H2.
    case_eq (eval_opt fs[@p] s ns); intro.
    2: elim H1; auto.
    case_eq (eval_opt fs[@p] s' ns); intro.
    2: elim H2; auto.
    intros; replace n with n0; auto.
    revert H4 H5; apply IHd; auto. (* HERE *)
    rewrite <- nth_map'; apply vmax_leq; auto.
  + simpl in H.
    assert (depth f1 <= d).
    etransitivity; [apply Nat.le_max_l | apply le_S_n; exact H].
    assert (depth f2 <= d).
    etransitivity; [apply Nat.le_max_r | apply le_S_n; exact H].
    clear H.
    rewrite (eta ns).
    case_eq (hd ns); do 2 intro.
    2: inversion H2.
    revert m m' ns H; induction n; do 4 intro.
    * simpl.
      apply IHf1; auto.
    * case_eq (eval_opt (Recursion f1 f2) s (Some n :: tl ns)); do 2 intro.
      rename n0 into f1x.
      case_eq (eval_opt (Recursion f1 f2) s' (Some n :: tl ns)); do 2 intro.
      rename n0 into f1x'.
      replace (eval_opt (Recursion f1 f2) s (Some (S n) :: tl ns)) with (eval_opt f2 s (Some n :: Some f1x :: tl ns)).
      replace (eval_opt (Recursion f1 f2) s' (Some (S n) :: tl ns)) with (eval_opt f2 s' (Some n :: Some f1x' :: tl ns)).
      ++ rewrite (IHn f1x f1x' (Some n::tl ns) (eq_refl _) H2 H3).
         apply IHf2; auto.
      ++ simpl; simpl in H3; rewrite H3; auto.
      ++ simpl; simpl in H2; rewrite H2; auto.
      ++ intros.
         simpl in H5; simpl in H3.
         rewrite H3 in H5; inversion H5.
      ++ intros.
         simpl in H2; simpl in H3.
         rewrite H2 in H3; inversion H3.
  + case_eq s; intros; inversion H1; clear H0 H1.
    revert H2; case_eq s'; intros; inversion H2; clear H0 H2.
    rename n0 into n'.
    simpl in H.
    generalize (le_S_n _ _ H); clear H; intro Hf.
    generalize (find_zero_from_middle _ _ _ _ _ H4);
    generalize (find_zero_from_value _ _ _ _ _ H4); clear H4; intros Hfn0 Hfn_lt.
    generalize (find_zero_from_middle _ _ _ _ _ H3);
    generalize (find_zero_from_value _ _ _ _ _ H3); clear H3; intros Hfn'0 Hfn'_lt.
    elim (lt_eq_lt_dec m m'); intro.
    * inversion_clear a; auto.
      elim (Hfn'_lt m); intros.
      generalize (IHf _ _ _ _ _ (le_S _ _ Hf) Hfn0 H0); intro exf; inversion exf.
      split; auto with arith.
    * elim (Hfn_lt m'); intros.
      generalize (IHf _ _ _ _ _ (le_S _ _ Hf) Hfn'0 H); intro exf; inversion exf.
      split; auto with arith.
Qed.

Lemma eval_opt_inj : forall n (f:PRFunction n) s s' ns m m',
  eval_opt f s ns = Some m -> eval_opt f s' ns = Some m' -> m = m'.
do 7 intro.
apply eval_opt_inj_lemma with (depth f); auto.
Qed.

Lemma eval_opt_mon_lemma : forall d m (f : PRFunction m), depth f <= d -> forall s ns k,
    eval_opt f s ns = Some k -> forall s', s' > s -> eval_opt f s' ns = Some k.
induction d; intros m f.
- induction f; intros; auto; inversion H.
- induction f; intros; auto; revert H0.
  + simpl in H; apply le_S_n in H.
    generalize (Nat.max_lub_l _ _ _ H); generalize (Nat.max_lub_r _ _ _ H); clear H.
    simpl; do 2 intro.
    case_eq (all_defined (map_inv (map_inv (map eval_opt fs) s) ns)); intro; simpl.
    2: intros; inversion H3.
    case_eq (all_defined ns); intro; simpl.
    2: intros; inversion H4.
    case_eq (all_defined (map_inv (map_inv (map eval_opt fs) s') ns)); intro; simpl.
    * replace (map_inv (map_inv (map eval_opt fs) s) ns) with (map_inv (map_inv (map eval_opt fs) s') ns).
      intro; apply IHf with s; auto.
      apply eq_nth_iff'; intros.
      repeat rewrite nth_map_inv'; rewrite nth_map'; auto.
      generalize (all_defined_true _ _ H4 p); clear H4; intro.
      repeat rewrite nth_map_inv' in H4.
      rewrite nth_map' in H4.
      generalize (all_defined_true _ _ H2 p); clear H2; intro.
      repeat rewrite nth_map_inv' in H2.
      rewrite nth_map' in H2.
      case_eq (eval_opt fs[@p] s ns); intro.
      2: elim H2; auto.
      case_eq (eval_opt fs[@p] s' ns); intro.
      2: elim H4; auto.
      intros; replace n with n0; auto.
      revert H5 H6; apply eval_opt_inj; auto.
    * elim (all_defined_false _ _ H4); intros.
      elim (all_defined_true _ _ H2 x); intros.
      revert H5; repeat rewrite nth_map_inv'; rewrite nth_map'; intro.
      case_eq (eval_opt fs[@x] s ns); auto; intros.
      assert (depth fs[@x] <= d).
      rewrite <- nth_map'; apply vmax_leq; auto.
      rewrite (IHd _ _ H8 _ _ _ H7) in H5; auto with arith; inversion H5.
  + simpl in H.
    assert (depth f1 <= d).
    etransitivity; [apply Nat.le_max_l | apply le_S_n; exact H].
    assert (depth f2 <= d).
    etransitivity; [apply Nat.le_max_r | apply le_S_n; exact H].
    clear H.
    rewrite (eta ns).
    case_eq (hd ns); do 2 intro.
    2: inversion H3.
    revert k0 ns H; induction n; do 3 intro.
    * simpl; intros.
      apply IHf1 with s; auto.
    * case_eq (eval_opt (Recursion f1 f2) s (Some n :: tl ns)); do 2 intro.
      rename n0 into f1x.
      generalize (IHn _ (Some n :: tl ns) (eq_refl _) H3); intro.
      replace (Some n :: tl (Some n :: tl ns)) with (Some n :: tl ns) in H4; auto.
      replace (eval_opt (Recursion f1 f2) s (Some (S n) :: tl ns)) with (eval_opt f2 s (Some n :: Some f1x :: tl ns)).
      replace (eval_opt (Recursion f1 f2) s' (Some (S n) :: tl ns)) with (eval_opt f2 s' (Some n :: Some f1x :: tl ns)).
      ++ intro; apply IHf2 with s; auto.
      ++ simpl; simpl in H4; rewrite H4; auto.
      ++ simpl; simpl in H3; rewrite H3; auto.
      ++ simpl in H3; simpl in H4.
         rewrite H3 in H4; inversion H4.
  + case_eq s; intros; [inversion H2 | simpl in H2].
    rewrite H0 in H1; clear H0 s.
    case_eq s'; simpl; intros.
    rewrite H0 in H1; inversion H1.
    rename n0 into n'; rename k0 into m.
    rewrite H0 in H1; clear H0 s'; red in H1.
    set (T := eval_opt).  (* WHAAAAAAAT ?! ?! ?! *)
    set (W := find_zero_from (T f n') ns 0 n').
    case_eq W; unfold W, T; clear W T; intros.
    * rename n0 into m'.
      generalize (find_zero_from_middle _ _ _ _ _ H2);
      generalize (find_zero_from_value _ _ _ _ _ H2); clear H2; intros fn_m fn_lt.
      generalize (find_zero_from_middle _ _ _ _ _ H0);
      generalize (find_zero_from_value _ _ _ _ _ H0); clear H0; intros fn'_m' fn'_lt.
      elim (lt_eq_lt_dec m m'); intro.
      ++ inversion_clear a; auto.
         elim (fn'_lt m); intros.
         2: split; auto with arith.
         generalize (eval_opt_inj _ _ _ _ _ _ _ fn_m H2); intro exf; inversion exf.
      ++ elim (fn_lt m'); intros.
         2: split; auto with arith.
         generalize (eval_opt_inj _ _ _ _ _ _ _ fn'_m' H0); intro exf; inversion exf.
    * generalize (find_zero_from_bound _ _ _ _ _ H2);
      generalize (find_zero_from_middle _ _ _ _ _ H2);
      generalize (find_zero_from_value _ _ _ _ _ H2); clear H2; intros fn_m fn_lt m_lt.
      simpl in H; generalize (le_S_n _ _ H); clear H; intro Hf.
      generalize (lt_S_n _ _ H1); clear H1; intro Hnn'.
      elim (find_zero_from_None _ _ _ _ H0); clear H0; simpl; intros.
      ** elim a; clear a; intros x a; elim a; clear a; intros Hx a.
         elim a; clear a; intros fn'_None fn'_lt.
         elim (lt_eq_lt_dec m x); intro.
         inversion_clear a.
         ++ elim (fn'_lt m); intros.
            2: split; auto with arith.
            assert (0 = S x0).
            2: inversion H1.
            apply (eval_opt_inj _ _ _ _ _ _ _ fn_m H0); auto.
         ++ rewrite <- H in fn'_None.
            generalize (IHd _ _ Hf _ _ _ fn_m _ Hnn'); intro.
            rewrite H0 in fn'_None; inversion fn'_None.
         ++ elim (fn_lt x); intros.
            2: split; auto with arith.
            assert (0 = S m).
            2: inversion H0.
            generalize (IHd _ _ Hf _ _ _ H _ Hnn'); intro.
            rewrite H0 in fn'_None; inversion fn'_None.
      ** elim (b m); intros.
         2: split; auto with arith; transitivity n; auto.
         generalize (eval_opt_inj _ _ _ _ _ _ _ fn_m H); intro exf; inversion exf.
Qed.

Lemma eval_opt_mon : forall m (f : PRFunction m) s ns k,
    eval_opt f s ns = Some k -> forall s', s' > s -> eval_opt f s' ns = Some k.
intros; apply eval_opt_mon_lemma with (depth f) s; auto.
Qed.

Lemma eval_opt_mon'_lemma : forall d m (f:PRFunction m) s ns, depth f <= d ->
  eval_opt f s ns = None -> forall s', s' <= s -> eval_opt f s' ns = None.
intros.
case_eq (eval_opt f s' ns); auto.
intros.
inversion H1.
+ rewrite H3 in H2; rewrite H2 in H0; auto.
+ rewrite (eval_opt_mon _ _ _ _ _ H2) in H0; auto.
  red; apply le_lt_trans with m0; auto; rewrite <- H4; auto with arith.
Qed.

Lemma eval_opt_mon' : forall m (f:PRFunction m) s ns,
  eval_opt f s ns = None -> forall s', s' <= s -> eval_opt f s' ns = None.
intros.
apply eval_opt_mon'_lemma with (depth f) s; auto.
Qed.

Lemma eval_mon : forall m (f:PRFunction m) steps ns k, eval f steps ns = (Some k) ->
  forall s', s' > steps -> eval f s' ns = (Some k).
intros.
apply eval_opt_mon with steps; auto.
Qed.

Lemma eval_inj_Some : forall m (f:PRFunction m) s s' ns m m', eval f s ns = Some m -> eval f s' ns = Some m' -> m = m'.
intros.
rewrite (eval_opt_inj _ _ _ _ _ _ _ H H0); auto.
Qed.

Lemma eval_inj_None : forall m (f:PRFunction m) s ns, eval f s ns = None -> forall s', s'<s -> eval f s' ns = None.
intros.
apply eval_opt_mon' with s; auto with arith.
Qed.

End Evaluation.

(** * Computation
    Finally we can define the computed value :-) *)
Section Convergence.

Definition converges {k} (f:PRFunction k) ns y := exists steps, eval f steps ns = Some y.

Definition diverges  {k} (f:PRFunction k) ns := forall steps, eval f steps ns = None.

Lemma converges_inj : forall {k} f ns y y', converges (k:=k) f ns y -> converges f ns y' -> y = y'.
intros.
inversion_clear H; inversion_clear H0.
revert H1 H; apply eval_inj_Some.
Qed.

Lemma converges_diverges : forall {k} f ns, (diverges (k:=k) f ns <-> forall y, ~converges f ns y).
split; intros; intro.
+ inversion_clear H0.
  rewrite H in H1; inversion H1.
+ case_eq (eval f steps ns); auto.
  intros.
  elim (H n); exists steps; auto.
Qed.

End Convergence.