Require Import Arith.
Require Import Vector.
Import VectorNotations.

Section to_be_moved.

(** Random stuff about vectors to be placed elsewhere. *)
Lemma hd_tl : forall {A} {n} (v:t A (S n)), v = hd v :: tl v.
intros.
revert n v; refine (@caseS _ _ _).
simpl; auto.
Qed.

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
  | Zero : PRFunction 1
  | Successor : PRFunction 1
  | Projection : forall (m k:nat), k < m -> PRFunction m
  | Composition : forall {k m:nat} (g:PRFunction m) (f:t (PRFunction k) m), PRFunction k
  | Recursion : forall {k:nat} (g:PRFunction k) (h:PRFunction (2+k)), PRFunction (1+k)
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
  replace (map_inv (map_inv (map eval_opt f0) s') ns) with (map_inv (map_inv (map eval_opt f0) steps) ns); auto.
  apply eq_nth_iff'; intros.
  repeat rewrite nth_map_inv'.
  rewrite nth_map'.
  Abort.


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

Lemma Projection_correct : forall m k Hkm n steps, eval (Projection m k Hkm) steps n = Some (nth n (Fin.of_nat_lt Hkm)).
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

Lemma Minimization_correct : forall k (h:PRFunction (1+k)) (ns:t nat k) steps n,
  eval (Minimization h) steps ns = (Some n) ->
  eval h steps (n::ns) = (Some 0) /\ forall m, m < n -> exists n', eval h steps (n::ns) = (Some (S n')).
Abort.

End Sanity_Checks.

Section Examples.
(** We recover the examples from the submitted journal paper. *)

Lemma aux01 : 0 < 1.
auto with arith.
Qed.

Lemma aux13 : 1 < 3.
auto with arith.
Qed.

Definition PR_add := Recursion (Projection 1 0 aux01) (Composition Successor [Projection 3 1 aux13]).

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

Definition PR_sign := Composition (Recursion Zero
  (Composition Successor [Composition Zero [Projection 3 1 aux13]]))
  [Projection 1 0 aux01; Projection 1 0 aux01].

Eval compute in (eval PR_sign 0 [32]).
Eval compute in (eval PR_sign 0 [0]).

Lemma sign_correct_0 : forall steps, eval PR_sign steps [0] = Some (0).
intros; simpl; auto.
Qed.

Lemma sign_correct_S : forall m steps, eval PR_sign steps [S m] = Some (1).
intros; induction m.
simpl; auto.
unfold PR_sign.
revert IHm; unfold eval; simpl; intro.
rewrite IHm; auto.
Qed.

End Examples.

