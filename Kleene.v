Require Import Arith.
Require Import Vector.
Import VectorNotations.

Section to_be_moved.

(** Random stuff about natural numbers. *)
Lemma minus_S : forall m n, n - S m = pred (n - m).
double induction m n; simpl; auto.
intros; rewrite minus_n_O; auto.
Qed.

Lemma minus_is_S : forall m n, m < n -> exists k, n - m = S k.
induction n; intros.
+ inversion H.
+ exists (n-m); rewrite minus_Sn_m; auto with arith.
Qed.

Lemma not_lt_minus_0 n m : ~ m < n -> n - m = 0.
induction n; intros; auto.
assert (S n <= m).
+ apply not_gt; auto.
+ elim (le_lt_eq_dec _ _ H0); intro.
  - apply not_le_minus_0; auto with arith.
  - rewrite b; auto with arith.
Qed.

(** Random stuff about vectors to be placed elsewhere. *)
Lemma eq_nth_iff' {A} {n} (v1 v2:t A n) : (forall (p:Fin.t n), v1[@p] = v2[@p]) <-> v1 = v2.
split.
intro; apply eq_nth_iff; intros; rewrite H0; auto.
intros; apply eq_nth_iff; auto.
Qed.

Fixpoint map_inv {A} {B} {n} (f:t (A->B) n) (x:A) : t B n :=
  match f with
  | [] => []
  | (f0 :: fs) => (f0 x) :: (map_inv fs x)
  end.

Lemma nth_map' {A B} (f: A -> B) {n} v (p: Fin.t n) : (map f v) [@p] = f (v [@p]).
apply nth_map; auto.
Qed.

Lemma nth_map_inv {A} {B} {n} (f:t (A->B) n) v (p1 p2: Fin.t n) (eq: p1 = p2) :
  (map_inv f v) [@ p1] = f[@ p2] v.
subst p2; induction p1.
  revert n f; refine (@caseS _ _ _); now simpl.
  revert n f p1 IHp1; refine (@caseS _  _ _); now simpl.
Qed.

Lemma nth_map_inv' {A} {B} {n} (f:t (A->B) n) v (p: Fin.t n) : (map_inv f v) [@p] = f[@p] v.
apply nth_map_inv; auto.
Qed.

Lemma vector_one_equal : forall {A} (x y:A), x = y -> forall Hi, [x][@Hi] = [y][@Hi].
intros; rewrite H; auto.
Qed.

Lemma vector_two_equal : forall {A} (x x' y y':A), x = x' -> y = y' -> forall Hi, [x; y][@Hi] = [x'; y'][@Hi].
intros; rewrite H, H0; auto.
Qed.

Lemma vector_three_equal : forall {A} (x x' y y' z z':A), x = x' -> y = y' -> z = z' ->
  forall Hi, [x; y; z][@Hi] = [x'; y'; z'][@Hi].
intros; rewrite H, H0, H1; auto.
Qed.

(* Sanity check.
Definition f0 (n:nat) := 2*n.
Definition f1 (n:nat) := n+3.

Eval compute in (map_inv [f0; f1] 5).
*)

End to_be_moved.

Section Definitions.

Inductive PRFunction : nat -> Set :=
  | Zero         : PRFunction 1
  | Successor    : PRFunction 1
  | Projection   : forall {m k:nat}, k < m -> PRFunction m
  | Composition  : forall {k m:nat} (g:PRFunction m) (fs:t (PRFunction k) m), PRFunction k
  | Recursion    : forall {k:nat} (g:PRFunction k) (h:PRFunction (2+k)), PRFunction (1+k)
  | Minimization : forall {k:nat} (h:PRFunction (1+k)), PRFunction k
.

(*
Fixpoint eval_opt {m} (f:PRFunction m) (steps:nat) (ns:t (option nat) m) : option nat :=
  match f with
  | Zero      => Some 0
  | Successor => match (nth ns (Fin.of_nat_lt (Nat.lt_succ_diag_r 0))) with
                 | Some x => Some (x + 1)
                 | None   => None
                 end
  | _ => None
  end.

 -- does not work because it doesn't know Successor is PRFunction 1.
*)

(* Auxiliary function for minimization. *)
Fixpoint find_zero_from {k} (f:t (option nat) (1+k) -> option nat) (ns:t (option nat) k) (init:nat) (steps:nat) : option nat :=
  match steps with
  | O   => None
  | S m => match f ((Some init) :: ns) with
           | None       => None
           | Some O     => Some init
           | Some (S _) => find_zero_from f ns (S init) m
end end.

(* We'd love a readable definition, but the dependent type of f makes it tricky to write. So... *)
(* First we define the fixpoint construction over the option type, to cater for undefinedness. *)
Fixpoint eval_opt {m} (f:PRFunction m) : forall (steps:nat) (ns:t (option nat) m), option nat.
destruct f; intros.

(* Zero *)
+ apply
  match (nth ns (Fin.of_nat_lt (Nat.lt_succ_diag_r 0))) with
    | Some x => Some 0
    | None => None
    end.

(* Successor *)
+ apply
    match (nth ns (Fin.of_nat_lt (Nat.lt_succ_diag_r 0))) with
    | Some x => Some (x + 1)
    | None => None
    end.

(* Projection *)
+ apply (nth ns (Fin.of_nat_lt l)).

(* Composition *)
+ apply (eval_opt _ f).
  apply steps.
  apply (map_inv (map_inv (map (eval_opt _) fs) steps) ns).

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

(* This is the one we actually want to use. *)
Definition eval {m} (f:PRFunction m) (steps:nat) (ns:t nat m) : option nat := eval_opt f steps (map Some ns).

End Definitions.

Section Sanity_Checks.
(** Since our definition of eval is very indirect, we prove that it behaves as expected. *)

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
apply nth_map'.
Qed.

Lemma Composition_correct : forall k m (g:PRFunction m) (f:t (PRFunction k) m) (ns:t nat k) (ms:t nat m) steps,
  (forall Hi, eval (nth f Hi) steps ns = Some (nth ms Hi)) -> eval g steps ms = eval (Composition g f) steps ns.
intros; unfold eval; simpl.
replace (map Some ms) with (map_inv (map_inv (map eval_opt f) steps) (map Some ns)); auto.
apply eq_nth_iff; intros.
rewrite <- H0; clear H0 p2.
transitivity (Some ms[@p1]).
2: symmetry; apply nth_map'.
rewrite <- H; clear H.
transitivity ((map_inv (map eval_opt f) steps)[@p1] (map Some ns)).
apply nth_map_inv'.
replace (map_inv (map eval_opt f) steps)[@p1] with ((map eval_opt f)[@p1] steps).
2: symmetry; apply nth_map_inv'.
replace (map eval_opt f)[@p1] with (eval_opt f[@p1]).
2: symmetry; apply nth_map'.
auto.
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

Lemma find_zero_from_correct : forall steps {k} f (ns:t (option nat) k) init m, find_zero_from f ns init steps = Some m ->
  f ((Some m) :: ns) = Some O /\ forall n, init <= n < m -> exists val, f ((Some n) :: ns) = Some (S val).
induction steps; intros.
+ inversion H.
+ revert H; simpl.
  set (x := f (Some init :: ns)).
  assert (x = f (Some init :: ns)); auto; clearbody x.
  destruct x.
  destruct n; intros.
  - inversion H0; split.
    * rewrite <- H2; auto.
    * intros; elim (lt_irrefl m).
      inversion_clear H1; apply le_lt_trans with n; auto.
  - elim (IHsteps _ _ _ _ _ H0); intros; split; auto.
    intros; inversion_clear H3.
    elim (le_lt_eq_dec _ _ H4); intro.
    * apply H2; auto with arith.
    * exists n; rewrite <- b; auto.
  - intro; inversion H0.
Qed.

Lemma Minimization_correct : forall k (h:PRFunction (1+k)) (ns:t nat k) steps n,
  eval (Minimization h) steps ns = (Some n) ->
  exists s, eval h s (n::ns) = (Some 0) /\ forall m, m < n -> exists n', eval h s (m::ns) = (Some (S n')).
intros; revert H; unfold eval.
induction steps.
+ simpl; intros; inversion H.
+ simpl; intro.
  elim (find_zero_from_correct _ _ _ _ _ H); intros; exists steps; split; auto.
  intros; apply H1; split; auto with arith.
Qed.

End Sanity_Checks.

(* Tactics for dealing with proofs involving composition. *)

Ltac prove_composition_1 := intros;
                            do 2 rewrite <- nth_map';
                            do 2 rewrite <- nth_map_inv';
                            apply vector_one_equal;
                            auto.

Ltac prove_composition_2 := intros;
                            do 2 rewrite <- nth_map';
                            do 2 rewrite <- nth_map_inv';
                            apply vector_two_equal;
                            auto.

Ltac prove_composition_3 := intros;
                            do 2 rewrite <- nth_map';
                            do 2 rewrite <- nth_map_inv';
                            apply vector_three_equal;
                            auto.

Section Examples.
(** We recover the examples from the submitted journal paper. *)

(* These lemmas are used to define projections. Their names seem inconsistent, but they refer to the usual convention for naming projections. *)
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

(* Addition. *)
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

(* Multiplication. *)
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

(* Sign function. *)
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

(* Predecessor. *)
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

(* Natural (total) subtraction. *)
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

(* Less than. *)
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

(* Less or equal. *)
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

(* Equality. *)
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

(* Inequality. *)
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

(* Finally: subtraction. *)
Definition PR_sub := Minimization (Composition PR_diff [Composition PR_add [Projection aux23; Projection aux33]; Projection aux13]).

(* AGH: in the paper, we're minimizing on the last argument, not the first.
Also, typo in the definition of sub in the paper.
Lemma sub_correct : forall m n steps k, eval PR_sub steps [m; n] = Some k -> n <= m /\ k = n - m.
intros.
unfold PR_sub in H.
generalize (Minimization_correct _ _ _ _ _ H); intro.
elim H0; clear H H0 steps; intros steps Hsteps; inversion_clear Hsteps.
assert (k = n-m).
+ clear H0.
  rewrite <- Composition_correct with (ms := [m+n; k]) in H.
  - rewrite <- diff_correct_0 in H.
    apply plus_minus.
  - prove_composition_2.
    * rewrite <- Composition_correct with (ms := [
split.
+ clear H.

*)

End Examples.

(* Ongoing. *)

(* Define:
 - f ns converges_to x -> exists steps, eval f ns steps = x
 - diverges -> negation
 - sanity: f ns converges_to x and x' -> x = x'.
*)

Section Incomplete.

Lemma eval_mon_comp : forall {k m:nat} (g:PRFunction m) (fs:t (PRFunction k) m) steps ns,
  eval_opt (Composition g fs) steps ns = (Some k) ->
  exists Hi, exists k', eval_opt fs[@Hi] steps ns = (Some k').
intros.
simpl in H.
induction g; simpl in H.
+ repeat rewrite nth_map_inv' in H; rewrite nth_map' in H.
  exists (Fin.F1 (n:=0)).
  set (x := eval_opt fs[@Fin.F1] steps ns).
  fold x in H.
  induction x.
  exists a; auto.
  inversion H.
+ repeat rewrite nth_map_inv' in H; rewrite nth_map' in H.
  exists (Fin.F1 (n:=0)).
  set (x := eval_opt fs[@Fin.F1] steps ns).
  fold x in H.
  induction x.
  exists a; auto.
  inversion H.
+ repeat rewrite nth_map_inv' in H; rewrite nth_map' in H.
  exists (Fin.of_nat_lt l).
  set (x := eval_opt fs[@Fin.of_nat_lt l] steps ns).
  fold x in H.
  induction x.
  exists a; auto.
  inversion H.
+ Abort.

(* Hmmm. *)
Lemma eval_mon : forall m (f:PRFunction m) steps ns k, eval f steps ns = (Some k) ->
  forall s', s' > steps -> eval f s' ns = (Some k).
unfold eval.
assert
  (forall (m : nat) (f : PRFunction m) (steps : nat) (ns : t (option nat) m) (k : nat),
    eval_opt f steps ns = Some k -> forall s' : nat, s' > steps -> eval_opt f s' ns = Some k).
2: intros; apply H with steps; auto.
induction f; intros.
+ simpl; auto.
+ simpl; auto.
+ simpl; auto.
+ simpl; simpl in H.
  apply IHf with steps; auto.
  replace (map_inv (map_inv (map eval_opt fs) s') ns) with (map_inv (map_inv (map eval_opt fs) steps) ns); auto.
  apply eq_nth_iff'; intros.
  repeat rewrite nth_map_inv'.
  rewrite nth_map'.
  Abort.

End Incomplete.
