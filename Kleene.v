Require Import Arith.
Require Import Vector.
Require Import Bool.

Import VectorNotations.

Section to_be_moved.

(** Random stuff about natural numbers. *)
Lemma minus_S : forall m n, n - S m = pred (n - m).
Proof.
double induction m n; simpl; auto.
intros; rewrite minus_n_O; auto.
Qed.

Lemma minus_is_S : forall m n, m < n -> exists k, n - m = S k.
Proof.
induction n; intros.
+ inversion H.
+ exists (n-m); rewrite minus_Sn_m; auto with arith.
Qed.

Lemma not_lt_minus_0 n m : ~ m < n -> n - m = 0.
Proof.
induction n; intros; auto.
assert (S n <= m).
+ apply not_gt; auto.
+ elim (le_lt_eq_dec _ _ H0); intro.
  - apply not_le_minus_0; auto with arith.
  - rewrite b; auto with arith.
Qed.

(** Random stuff about vectors to be placed elsewhere. *)

(* Equality. *)
Lemma eq_nth_iff' {A} {n} (v1 v2:t A n) : (forall (p:Fin.t n), v1[@p] = v2[@p]) <-> v1 = v2.
Proof.
split.
intro; apply eq_nth_iff; intros; rewrite H0; auto.
intros; apply eq_nth_iff; auto.
Qed.

(* Characterization results. *)

Lemma vector_1_equal : forall {A} (x y:A), x = y -> forall Hi, [x][@Hi] = [y][@Hi].
Proof.
intros; rewrite H; auto.
Qed.

Lemma vector_2_equal : forall {A} (x x' y y':A), x = x' -> y = y' -> forall Hi, [x; y][@Hi] = [x'; y'][@Hi].
Proof.
intros; rewrite H, H0; auto.
Qed.

Lemma vector_3_equal : forall {A} (x x' y y' z z':A), x = x' -> y = y' -> z = z' ->
  forall Hi, [x; y; z][@Hi] = [x'; y'; z'][@Hi].
Proof.
intros; rewrite H, H0, H1; auto.
Qed.

Lemma vector_0_inv : forall {A} (v:t A 0), [] = v.
Proof.
intro; apply (case0 (fun x => []=x)); auto.
Qed.

Lemma vector_1_inv : forall {A} (v:t A 1), [hd v] = v.
Proof.
intros; rewrite (eta v); simpl.
replace (tl v) with (nil A); auto.
apply vector_0_inv.
Qed.

Lemma vector_2_inv : forall {A} (v:t A 2), [hd v; hd (tl v)] = v.
Proof.
intros; rewrite (eta v); simpl.
replace (tl v) with [hd (tl v)]; auto.
apply vector_1_inv.
Qed.

Lemma vector_3_inv : forall {A} (v:t A 3), [hd v; hd (tl v); hd (tl (tl v))] = v.
Proof.
intros; rewrite (eta v); simpl.
replace (tl v) with [hd (tl v); hd (tl (tl v))]; auto.
apply vector_2_inv.
Qed.

(* On heads and tails. *)
Lemma nth_hd : forall {A} {n} (v:t A (S n)), v[@Fin.F1] = hd v.
Proof.
intros.
rewrite (eta v); simpl; auto.
Qed.

Lemma nth_hd' : forall {A} (v:t A 1) Hi, v[@Hi] = hd v.
Proof.
intros.
replace v with (const (hd v) 1) at 1.
+ rewrite const_nth; auto.
+ simpl; apply vector_1_inv.
Qed.

Lemma nth_tl : forall {A} {n} (v:t A (S n)) Hi, v[@Fin.FS Hi] = (tl v)[@Hi].
Proof.
induction n; simpl.
+ intros; inversion Hi.
+ intros; rewrite (eta v).
  simpl; auto.
Qed.

Require Import Coq.Program.Equality.
Lemma eta_elim : forall {A} {n} (v:t A (S n)) x Hi, v[@Hi] = x -> hd v = x \/ exists Hi', (tl v)[@Hi'] = x.
dependent induction Hi; intros.
- left; rewrite nth_hd in H; auto.
- right; rewrite nth_tl in H; eauto.
Qed.

Lemma map_shiftin : forall {A} {B} {n} (f:A->B) (v:t A n) x, map f (shiftin x v) = shiftin (f x) (map f v).
Proof.
induction v; simpl; auto.
intro.
rewrite IHv; auto.
Qed.

Fixpoint map_inv {A} {B} {n} (f:t (A->B) n) (x:A) : t B n :=
  match f with
  | [] => []
  | (f0 :: fs) => (f0 x) :: (map_inv fs x)
  end.

Lemma nth_map' {A B} (f: A -> B) {n} v (p: Fin.t n) : (map f v) [@p] = f (v [@p]).
Proof.
apply nth_map; auto.
Qed.

Lemma nth_map_inv {A} {B} {n} (f:t (A->B) n) v (p1 p2: Fin.t n) (eq: p1 = p2) :
  (map_inv f v) [@ p1] = f[@ p2] v.
Proof.
subst p2; induction p1.
+ revert n f; refine (@caseS _ _ _); now simpl.
+ revert n f p1 IHp1; refine (@caseS _  _ _); now simpl.
Qed.

Lemma nth_map_inv' {A} {B} {n} (f:t (A->B) n) v (p: Fin.t n) : (map_inv f v) [@p] = f[@p] v.
Proof.
apply nth_map_inv; auto.
Qed.

Fixpoint vmax {n} (v:t nat n) :=
  match v with
  | [] => 0
  | x :: xs => max x (vmax xs)
end.

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

(* Auxiliary functions for minimization. *)
Fixpoint all_defined {n} (v:t (option nat) n) : bool :=
  match v with
  | []             => true
  | (Some _) :: v' => all_defined v'
  | None :: _      => false
end.

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

Fixpoint find_zero_from {k} (f:t (option nat) (1+k) -> option nat) (ns:t (option nat) k) (init:nat) (steps:nat) : option nat :=
  match steps with
  | O   => None
  | S m => match f (shiftin (Some init) ns) with
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

(* This is the one we actually want to use. *)
Definition eval {m} (f:PRFunction m) (steps:nat) (ns:t nat m) : option nat := eval_opt f steps (map Some ns).

Lemma eval_opt_inv : forall m (f:PRFunction m) steps ns Hi, ns[@Hi] = None -> eval_opt f steps ns = None.
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
  generalize (IHf n ms _ H); clear IHf H H0 Hi; clearbody ms; intros.
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

Lemma Projection_correct : forall m k (Hkm: k<m) n steps, eval (Projection Hkm) steps n = Some (nth n (Fin.of_nat_lt Hkm)).
intros; unfold eval; simpl.
rewrite all_defined_map_Some.
apply nth_map'.
Qed.

Lemma Composition_correct : forall k m (g:PRFunction m) (f:t (PRFunction k) m) (ns:t nat k) (ms:t nat m) steps,
  (forall Hi, eval (nth f Hi) steps ns = Some (nth ms Hi)) -> eval g steps ms = eval (Composition g f) steps ns.
intros; unfold eval; simpl.
set (T := all_defined (map_inv (map_inv (map eval_opt f) steps) (map Some ns))).
assert (T = all_defined (map_inv (map_inv (map eval_opt f) steps) (map Some ns))); auto.
destruct T.
+ replace (all_defined (map Some ns)) with true.
  - simpl.
  replace (map Some ms) with (map_inv (map_inv (map eval_opt f) steps) (map Some ns)); auto.
  apply eq_nth_iff; intros.
  rewrite <- H1; clear H1 p2.
  rewrite nth_map'.
  rewrite <- H; clear H.
  repeat rewrite nth_map_inv'.
  rewrite nth_map'; auto.
  - symmetry; apply all_defined_map_Some.
+ exfalso.
  symmetry in H0.
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

Lemma find_zero_from_correct : forall steps {k} f (ns:t (option nat) k) init m, find_zero_from f ns init steps = Some m ->
  f (shiftin (Some m) ns) = Some O /\ forall n, init <= n < m -> exists val, f (shiftin (Some n) ns) = Some (S val).
induction steps; intros.
+ inversion H.
+ revert H; simpl.
  set (x := f (shiftin (Some init) ns)).
  assert (x = f (shiftin (Some init)ns)); auto; clearbody x.
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

Lemma find_zero_min : forall steps {k} f (ns:t (option nat) k) init m, find_zero_from f ns init steps = Some m ->
  forall n, f (shiftin (Some n) ns) = Some 0 -> n < init \/ m <= n.
intros.
elim (le_lt_dec m n); auto; intro.
elim (le_lt_dec init n); auto; intro.
elim (find_zero_from_correct _ _ _ _ _ H); intros.
exfalso.
elim (H2 n); auto; intros.
rewrite H3 in H0; inversion H0.
Qed.

Lemma Minimization_correct : forall k (h:PRFunction (1+k)) (ns:t nat k) steps n,
  eval (Minimization h) steps ns = (Some n) ->
  exists s, eval h s (shiftin n ns) = (Some 0) /\ forall m, m < n -> exists n', eval h s (shiftin m ns) = (Some (S n')).
intros; revert H; unfold eval.
induction steps.
+ simpl; intros; inversion H.
+ simpl; intro.
  elim (find_zero_from_correct _ _ _ _ _ H); intros; exists steps.
  rewrite map_shiftin; split; auto.
  intros; rewrite map_shiftin; apply H1; split; auto with arith.
Qed.

(*
Lemma Minimization_correct' : forall k (h:PRFunction (1+k)) (ns:t nat k) steps n,
  eval (Minimization h) steps ns = (Some n) -> forall m, eval h steps (shiftin m ns) = (Some 0) -> n <= m.
intros.
elim (Minimization_correct _ _ _ _ _ H); intros; clear H.
inversion_clear H1.
elim (le_lt_dec n m); auto; intro.
elim (H2 _ b); clear H2; intros.
rewrite 
*)

End Sanity_Checks.

(* Tactics for dealing with proofs involving composition. *)

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
Definition PR_sub_aux := Composition PR_diff [Composition PR_add [Projection aux23; Projection aux33]; Projection aux13].
Definition PR_sub := Minimization PR_sub_aux.

(* Typo in the definition of sub in the paper. *)

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
  elim (find_zero_from_correct _ _ _ _ _ H); intros.
  clear H H2; change (eval PR_sub_aux steps [m; n; k] = Some 0) in H1.
  rewrite sub_aux_correct in H1.
  rewrite not_le_minus_0 in H0; auto with arith.
  rewrite H0 in H1; rewrite plus_comm in H1.
  rewrite H1; auto with arith.
Qed.

End Examples.

Fixpoint depth {m} (f:PRFunction m) : nat :=
  match f with
  | Zero             => 0
  | Successor        => 0
  | Projection _     => 0
  | Composition g fs => 1 + max (depth g) (vmax (map depth fs))
  | Recursion g h    => 1 + max (depth g) (depth h)
  | Minimization h   => 1 + depth h
end.

(*
Lemma eval_opt_inj : forall d m (f:PRFunction m) s s' ns m m', depth f <= d ->
  eval_opt f s ns = Some m -> eval_opt f s' ns = Some m' -> m = m'.
induction d; intros m f.
- induction f; intros; try (inversion H; fail); revert H0 H1.
  + simpl; replace ns with [hd ns]; [intros | apply vector_1_inv].
    inversion H1; inversion H0; auto.
  + replace ns with [hd ns]; [idtac | apply vector_1_inv].
    set (x := hd ns); destruct x; simpl; intros; inversion H1; inversion H0; auto.
  + simpl.
    set (x := ns[@Fin.of_nat_lt l]); destruct x; simpl; intros; inversion H1; inversion H0; transitivity n; auto.
- induction f; intros; revert H0 H1.
  (* the first three cases are the same *)
  + simpl; replace ns with [hd ns]; [intros | apply vector_1_inv].
    inversion H1; inversion H0; auto.
  + replace ns with [hd ns]; [idtac | apply vector_1_inv].
    set (x := hd ns); destruct x; simpl; intros; inversion H1; inversion H0; auto.
  + simpl.
    set (x := ns[@Fin.of_nat_lt l]); destruct x; simpl; intros; inversion H1; inversion H0; transitivity n; auto.
  + simpl in H; apply le_S_n in H.
    generalize (Nat.max_lub_l _ _ _ H); generalize (Nat.max_lub_r _ _ _ H); clear H.
    simpl; intros.
    replace (map_inv (map_inv (map eval_opt fs) s) ns) with (map_inv (map_inv (map eval_opt fs) s') ns) in H1.
(* requires all calls to be defined *)



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

Lemma eval_opt_inj : forall m (f:PRFunction m) s s' ns m m', eval_opt f s ns = Some m -> eval_opt f s' ns = Some m' -> m = m'.
induction f; intros; revert H H0.
+ simpl; replace ns with [hd ns]; [intros | apply vector_1_inv].
  inversion H; inversion H0; auto.
+ replace ns with [hd ns]; [idtac | apply vector_1_inv].
  set (x := hd ns); destruct x; simpl; intros; inversion H; inversion H0; auto.
+ simpl.
  set (x := ns[@Fin.of_nat_lt l]); destruct x; simpl; intros; inversion H; inversion H0; transitivity n; auto.
+ simpl.
  apply IHf.

Lemma eval_inj : forall m (f:PRFunction m) s s' ns m m', eval f s ns = Some m -> eval f s' ns = Some m' -> m = m'.
induction f; simpl; intros; revert H H0.
+ replace ns with [hd ns]; [repeat rewrite Zero_correct | apply vector_1_inv].
  intros; inversion H; inversion H0; auto.
+ replace ns with [hd ns]; [repeat rewrite Successor_correct | apply vector_1_inv].
  intros; inversion H; inversion H0; auto.
+ repeat rewrite Projection_correct; intros.
  rewrite H in H0; inversion H0; auto.
+ rewrite Composition_correct with (ms := (map_inv (map_inv (map eval_opt fs) s) (map Some ns))).



End Incomplete.
*)