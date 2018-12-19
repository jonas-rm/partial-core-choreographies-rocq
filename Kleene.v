Require Import Arith.
Require Import Vector.
Import VectorNotations.

Section to_be_moved.

(** Random stuff about natural numbers. *)
Lemma minus_S : forall n m, n - S m = pred (n - m).
double induction n m; simpl; auto.
intros; rewrite minus_n_O; auto.
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

Section Examples.
(** We recover the examples from the submitted journal paper. *)

(* These lemmas are used to define projections. Their names seem inconsistent, but they refer to the usual convention for naming projections. *)
Lemma aux11 : 0 < 1.
auto with arith.
Qed.

Lemma aux13 : 0 < 3.
auto with arith.
Qed.

Lemma aux23 : 1 < 3.
auto with arith.
Qed.

Definition PR_add := Recursion (Projection aux11) (Composition Successor [Projection aux23]).

Eval compute in (eval PR_add 0 [2; 3]).
Eval compute in (eval PR_add 0 [5; 7]).

(* OMG *)
Lemma add_correct : forall m n steps, eval PR_add steps [m; n] = Some (m + n).
intros; induction m.
simpl; auto.
unfold PR_add.
rewrite Recursion_correct_step with (x:=m) (y:=m+n); auto.
unfold eval; simpl.
replace (m+n+1) with (S (m+n)); auto.
rewrite (plus_comm (m+n) 1); auto with arith.
Qed.

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

Definition PR_pred := Composition (Recursion Zero (Projection aux13)) [Projection aux11; Zero].

Eval compute in (eval PR_pred 0 [32]).
Eval compute in (eval PR_pred 0 [0]).

Lemma pred_correct : forall n steps, eval PR_pred steps [n] = Some (pred n).
intros; unfold PR_pred.
rewrite <- Composition_correct with (ms := [n; 0]).
+ induction n.
  - rewrite Recursion_correct_base; auto.
  - rewrite Recursion_correct_step with (x := n) (y := pred n); auto.
+ unfold eval; intro.
  do 2 rewrite <- nth_map'.
  repeat rewrite <- nth_map_inv'.
  replace (map_inv (map_inv (map eval_opt [Projection aux11; Zero]) steps) (map Some [n])) with (map Some [n; 0]); auto.
Qed.

Definition PR_sub := Recursion (Projection aux11) (Composition PR_pred [Projection aux23]).

Eval compute in (eval PR_sub 0 [2; 3]).
Eval compute in (eval PR_sub 0 [5; 7]).
Eval compute in (eval PR_sub 0 [3; 2]).

Lemma sub_correct : forall m n steps, eval PR_sub steps [m; n] = Some (n - m).
intros; unfold PR_sub.
induction m.
+ rewrite Recursion_correct_base; auto; rewrite <- minus_n_O; auto.
+ rewrite Recursion_correct_step with (x := m) (y := n - m); simpl; auto.
  replace (n - S m) with (pred (n - m)).
  - rewrite <- Composition_correct with (ms := [n-m]).
    * apply pred_correct.
    * unfold eval; intro.
      do 2 rewrite <- nth_map'.
      do 2 rewrite <- nth_map_inv'.
      replace (map_inv (map_inv (map eval_opt [Projection aux23]) steps) (map Some [m; n - m; n])) with (map Some [n-m]); auto.
  - rewrite minus_S; auto.
Qed.

End Examples.

(* Ongoing. *)

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
