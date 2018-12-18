Require Import Arith.
Require Import Vector.
Import VectorNotations.

Section to_be_moved.

Fixpoint map_inv {A} {B} {n} (f:t (A->B) n) (x:A) : t B n :=
  match f with
  | [] => []
  | (f0 :: fs) => (f0 x) :: (map_inv fs x)
  end.

Lemma nth_map' {A B} (f: A -> B) {n} v (p: Fin.t n): (map f v) [@p] = f (v [@p]).
apply nth_map; auto.
Qed.

Lemma nth_map_inv {A} {B} {n} (f:t (A->B) n) v (p1 p2: Fin.t n) (eq: p1 = p2):
  (map_inv f v) [@ p1] = f[@ p2] v.
subst p2; induction p1.
  revert n f; refine (@caseS _ _ _); now simpl.
  revert n f p1 IHp1; refine (@caseS _  _ _); now simpl.
Qed.

Lemma nth_map_inv' {A} {B} {n} (f:t (A->B) n) v (p: Fin.t n): (map_inv f v) [@p] = f[@p] v.
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
  | Zero : PRFunction 1
  | Successor : PRFunction 1
  | Projection : forall (m k:nat), k < m -> PRFunction m
  | Composition : forall {k m:nat} (g:PRFunction m) (f:t (PRFunction k) m), PRFunction k
  | Recursion : forall {k:nat} (g:PRFunction k) (h:PRFunction (2+k)), PRFunction (1+k)
  | Minimization : forall {k:nat} (h:PRFunction (1+k)), PRFunction k
.

Fixpoint eval_opt {m} (f:PRFunction m) : forall (steps:nat) (ns:t (option nat) m), option nat.
destruct f; intros.

(* Zero *)
+ apply (Some 0).

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
  apply (map_inv (map_inv (map (eval_opt _) f0) steps) ns).

(* Recursion *)
+ inversion ns; clear H n.                           (* getting the first element *)
  destruct h; [idtac 1 | apply None].                (* is there an argument? *)
  induction n.                                       (* finally *)
  apply (eval_opt _ f1 steps H0).                    (* f x1...xn *)
  destruct IHn; [rename n0 into x | apply None].
  apply (eval_opt _ f2 steps).
  apply (Some n :: Some x :: H0).

(* Minimization *)
+ destruct steps.
  - apply None.
  - 
apply None.
Defined.

Definition eval {m} (f:PRFunction m) (steps:nat) (ns:t nat m) : option nat := eval_opt f steps (map Some ns).

End Definitions.

Section Examples.

Lemma aux01 : 0 < 1.
auto with arith.
Qed.

Lemma aux13 : 1 < 3.
auto with arith.
Qed.

Definition PR_add := Recursion (Projection 1 0 aux01) (Composition Successor [Projection 3 1 aux13]).

Eval compute in (eval PR_add 0 [2; 3]).
Eval compute in (eval PR_add 0 [5; 7]).

Definition PR_sign := Composition (Recursion Zero
  (Composition Successor [Composition Zero [Projection 3 1 aux13]]))
  [Projection 1 0 aux01; Projection 1 0 aux01].

Eval compute in (eval PR_sign 0 [32]).
Eval compute in (eval PR_sign 0 [0]).

End Examples.

Section Sanity_Checks.

Lemma Zero_correct : forall n steps, eval Zero steps [n] = Some 0.
compute; auto.
Qed.

Lemma Successor_correct : forall n steps, eval Successor steps [n] = Some (S n).
intros; unfold eval; simpl.
replace (n+1) with (S n); auto.
rewrite plus_comm; auto.
Qed.

Lemma Projection_correct : forall m k Hkm n steps, eval (Projection m k Hkm) steps n = Some (nth n (Fin.of_nat_lt Hkm)).
intros; unfold eval; simpl.
apply nth_map'.
Qed.

Lemma Composition_correct: forall k m (g:PRFunction m) (f:t (PRFunction k) m) (ns:t nat k) (ms:t nat m) steps,
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

End Sanity_Checks.
