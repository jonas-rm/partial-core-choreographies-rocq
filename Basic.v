Require Export Bool.
Require Export List.
Require Export ListSet.
Require Export Sorting.Permutation.
Require Export Arith.

Ltac destroy H := repeat (elim H; intro; clear H; intro H).

(** * Natural numbers *)
Section Natural_Numbers.

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

Lemma max_lt_l : forall k m n, max m n < k -> m < k.
Proof.
intro; case_eq k; intros.
inversion H0.
generalize (le_S_n _ _ H0); intros.
apply le_n_S.
eapply Nat.max_lub_l; exact H1.
Qed.

Lemma max_lt_r : forall k m n, max m n < k -> n < k.
Proof.
intros; apply max_lt_l with m.
rewrite Nat.max_comm; auto.
Qed.

Theorem beq_sym: forall n m : nat, (n =? m) = (m =? n).
Proof.
  induction n as [|n' IH]; destruct m; auto.
  apply IH.
Qed.

Lemma O_plus_O : forall {n m}, n+m = 0 -> n = 0.
Proof.
double induction n m; auto; clear n m; intros.
- inversion H0.
- inversion H1.
Qed.

Lemma O_plus_O' : forall {n m}, n+m = 0 -> m = 0.
Proof.
intros n m; rewrite plus_comm; apply O_plus_O.
Qed.

End Natural_Numbers.

(** * Lists *)

Section Lists.

Variable T:Type.

(** ** A result about permutations *)

Lemma Permutation_NoDup : forall P Q: list T, Permutation P Q -> NoDup P -> NoDup Q.
Proof.
intros.
induction H; auto.
inversion_clear H0; apply NoDup_cons; auto.
intro; apply H1; apply Permutation_in with l'; auto.
apply Permutation_sym; auto.
inversion_clear H0; inversion_clear H1.
apply NoDup_cons.
intro; inversion_clear H1; auto.
apply H; left; auto.
apply NoDup_cons; auto.
intro; apply H; right; auto.
Qed.

(** ** Miscellaneous about NoDup *)

Lemma NoDup_app_char : forall l l':list T, NoDup l -> NoDup l' ->
                      (forall x, In x l -> ~In x l') -> NoDup (l++l').
Proof.
Proof.
induction l; simpl; auto.
intros.
inversion_clear H.
apply NoDup_cons.
intro; elim (in_app_or _ _ _ H); auto.
apply H1; auto.
apply IHl; auto.
Qed.

Lemma NoDup_app_elim_1 : forall l l':list T, NoDup (l++l') -> NoDup l.
Proof.
induction l; simpl; intros.
+ apply NoDup_nil.
+ inversion_clear H.
  apply NoDup_cons; eauto.
  intro; contradiction H0; apply in_or_app; auto.
Qed.

Lemma NoDup_app_elim_2 : forall l l':list T, NoDup (l++l') -> NoDup l'.
Proof.
induction l; simpl; intros; auto.
inversion H; auto.
Qed.

Lemma NoDup_app_both : forall l l':list T, NoDup (l++l') ->
  forall x, ~(In x l /\ In x l').
Proof.
induction l; simpl; intros; auto.
+ intro; inversion_clear H0; auto.
+ inversion_clear H; intro.
  inversion_clear H.
  generalize (IHl _ H1 x); intro.
  inversion_clear H2; auto.
  apply H0; apply in_or_app; rewrite H4; auto.
Qed.

Lemma NoDup_app_sym : forall l l':list T, NoDup (l++l') -> NoDup (l'++l).
Proof.
induction l; simpl; intros.
+ rewrite app_nil_r; auto.
+ inversion H; intros.
  clear x H0 l0 H1.
  apply NoDup_app_char; auto.
  - apply NoDup_app_elim_2 with l; auto.
  - apply NoDup_app_elim_1 with l'; auto.
  - intros; intro.
    inversion_clear H1.
    * contradiction H2; apply in_or_app; rewrite H4; auto.
    * apply (NoDup_app_both _ _ H3) with x; auto.
Qed.

Lemma NoDup_app :
  forall A (P Q:list A),
  (NoDup (P ++ Q)) -> (NoDup P) /\ (NoDup Q).
Proof.
intros.
induction P.
+ split; auto. apply NoDup_nil.
+ inversion H.
  elim IHP; auto; intros.
  split; auto.
  apply NoDup_cons; auto.
  intro; apply H2; apply in_or_app; auto.
Qed.

Lemma NoDup_app_not_in : forall l l':list T, NoDup (l ++ l') ->
  forall x, In x l -> ~In x l'.
Proof.
intros; intro.
apply (NoDup_app_both _ _ H) with x; auto.
Qed.

Lemma not_in_app : forall (xs ys : list T) (x : T),
  ~ In x (xs ++ ys) -> ~ In x xs /\ ~ In x ys.
Proof.
split; auto using in_or_app.
Qed.

Lemma not_in_app' : forall (xs ys : list T) (x : T),
  ~ In x xs /\ ~ In x ys -> ~ In x (xs ++ ys).
Proof.
intros.
inversion_clear H.
red.
rewrite in_app_iff.
intros.
inversion H; auto.
Qed.

Lemma not_in_app_iff : forall (xs ys : list T) (x : T),
  ~ In x (xs ++ ys) <-> ~ In x xs /\ ~ In x ys.
Proof.
split.
apply not_in_app.
apply not_in_app'.
Qed.

(** ** Disjoint lists *)

Definition disjoint {A:Type} (l l':list A) :=
  forall a, ~(In a l /\ In a l').

Lemma disjoint_dec : forall A (A_dec:forall x y:A,{x=y}+{x<>y}) l l',
  {disjoint (A:=A) l l'} + {~disjoint l l'}.
Proof.
induction l; auto.
+ left; repeat intro.
  inversion_clear H. inversion H0.
+ intro; elim IHl with l'.
  - intro. elim (In_dec A_dec a l'); intros.
    * right; intro. apply (H a); split; simpl; auto.
    * left; intro; intro; inversion_clear H.
      inversion_clear H0; auto.
      1: rewrite H in b; auto.
      apply a0 with a1; auto.
  - right; intro. apply b. repeat intro.
    inversion_clear H0; elim (H a0); split; simpl; auto.
Qed.

Lemma disjoint_not_in_fst : forall A (l l':list A),
  disjoint l l' -> forall a, In a l -> ~In a l'.
Proof.
intros; intro.
apply (H a); auto.
Qed.

Lemma disjoint_not_in_snd : forall A (l l':list A),
  disjoint l l' -> forall a, In a l' -> ~In a l.
Proof.
intros. intro.
apply (H a); auto.
Qed.

Lemma disjoint_char : forall A (l l':list A),
  (forall a, In a l -> ~In a l') -> disjoint l l'.
Proof. repeat intro. inversion_clear H0. apply (H a); auto. Qed.

Lemma disjoint_sym : forall A (l l':list A),
  disjoint l l' -> disjoint l' l.
Proof.
intros.
apply disjoint_char.
apply disjoint_not_in_snd; auto.
Qed.

(** ** On sets *)

Set Implicit Arguments.

Lemma set_union_elim : forall T T_dec (x:T) (X Y:set T),
  In x (set_union T_dec X Y) -> {In x X} + {In x Y}.
Proof.
induction Y.
+ left; simpl; auto.
+ elim (T_dec x a).
  - right. rewrite a0; simpl; auto.
  - intros; elim IHY; auto.
    right; simpl; auto.
    simpl in H.
    elim (set_add_elim _ _ _ _ H); auto.
    intros; elim b; auto.
Qed.

(** Equality and inclusion *)

Hypothesis T_dec : forall x y:T, {x=y}+{x<>y}.

Definition set_equals (T_dec : forall x y:T, {x=y}+{x<>y})
  (X Y:set T) := forall z, In z X <-> In z Y.

Definition set_incl (T_dec : forall x y:T, {x=y}+{x<>y})
  (X Y:set T) := forall z, In z X -> In z Y.

Lemma set_incl_dec  :
  forall X Y, {set_incl T_dec X Y}+{~set_incl T_dec X Y}.
Proof.
intros X Y; revert X; induction X.
+ left; red; simpl; intros.
  inversion H.
+ inversion_clear IHX; [elim (set_In_dec T_dec a Y) | idtac]; intros.
  - left; red; simpl; intros.
    inversion_clear H0; auto.
    rewrite <- H1; auto.
  - right; intro.
    apply b; apply H0; simpl; auto.
  - right; intro.
    red in H0.
    apply H; red; intros.
    apply H0; simpl; auto.
Qed.

Lemma set_equals_char : forall X Y, set_equals T_dec X Y <-> (set_incl T_dec X Y /\ set_incl T_dec Y X).
Proof.
split; intros.
+ split; red; intros; apply H; auto.
+ inversion_clear H.
  split; auto.
Qed.

Lemma set_equals_dec  :
  forall X Y, {set_equals T_dec X Y}+{~set_equals T_dec X Y}.
Proof.
intros.
elim (set_incl_dec X Y); [elim (set_incl_dec Y X) | idtac]; intros.
+ left; apply set_equals_char; auto.
+ right; intro; apply b.
  rewrite set_equals_char in H; inversion_clear H; auto.
+ right; intro; apply b.
  rewrite set_equals_char in H; inversion_clear H; auto.
Qed.

(** More robust remove *)

Fixpoint set_remove' x (X:set T) :=
  match X with
  | nil => nil
  | y::Y => if T_dec x y then (set_remove' x Y) else (y::set_remove' x Y)
  end.

Lemma set_remove'_not_In : forall x (X:set T), ~In x X -> set_remove' x X = X.
Proof.
induction X; auto.
simpl; intros.
elim T_dec; simpl; intros.
+ elim H; auto.
+ rewrite IHX; auto.
Qed.

Lemma set_remove'_1: forall x y (X : set T), In x (set_remove' y X) -> In x X.
Proof.
induction X; simpl; auto.
elim T_dec; intros; auto.
inversion_clear H; auto.
Qed.

Lemma set_remove'_2: forall x y (X:set T), In x (set_remove' y X) -> x <> y.
Proof.
induction X; auto.
simpl. elim T_dec; auto.
simpl; intros.
inversion_clear H; auto.
rewrite <- H0; auto.
Qed.

Lemma set_remove'_3: forall x y (X:set T), x<>y -> In x X -> In x (set_remove' y X).
Proof.
induction X; auto.
simpl; intros.
inversion_clear H0; intros.
+ rewrite H1; clear a H1.
  elim T_dec; intros; simpl; auto.
  elim H; auto.
+ elim T_dec; simpl; auto.
Qed.

Lemma set_remove'_cross : forall x y (X:set T),
  In x X -> set_remove' x X = set_remove' y X -> x = y.
Proof.
intros.
elim (T_dec x y); auto.
intro.
generalize (set_remove'_3 _ b H); intro.
rewrite <- H0 in H1.
elim (set_remove'_2 _ H1); auto.
Qed.

Lemma set_remove'_remove' : forall x y (X:set T),
  set_remove' x (set_remove' y X) = set_remove' y (set_remove' x X).
Proof.
induction X; simpl; auto.
intros; do 2 elim T_dec; simpl; intros.
+ rewrite a0, a1; auto.
+ elim T_dec; simpl; auto.
  intro; elim b0; auto.
+ elim T_dec; simpl; auto.
  intro; elim b0; auto.
+ elim T_dec; simpl; auto.
  1: intro; elim b; auto.
  elim T_dec; simpl; auto.
  1: intro; elim b0; auto.
  intros; rewrite IHX; auto.
Qed.

(** Size *)

Fixpoint set_size (X:set T) :=
  match X with
  | nil => 0
  | x::Y => if In_dec T_dec x Y then set_size Y else S (set_size Y)
  end.

Lemma set_size_0 : forall X, set_size X = 0 -> X = nil.
Proof.
induction X; auto.
simpl.
elim in_dec; simpl; intros.
+ rewrite IHX in a0; auto; inversion a0.
+ inversion H.
Qed.

Lemma set_size_remove' : forall X x, In x X ->
  set_size X = S (set_size (set_remove' x X)).
Proof.
induction X; intros; auto with arith.
inversion_clear H.
+ rewrite H0; clear a H0; simpl.
  elim T_dec; intro Hx. 2: elim Hx; auto.
  elim in_dec; intros; auto.
  rewrite set_remove'_not_In; auto.
+ simpl.
  elim T_dec; elim in_dec; intros; auto.
  * elim b; rewrite <- a0; auto.
  * rewrite (IHX a); simpl; auto; elim in_dec; auto; intros.
    2: { elim b0. apply set_remove'_3; auto. }
    rewrite <- IHX; auto.
  * simpl.
    elim in_dec; intros; auto.
    elim b. apply set_remove'_1 with x; auto.
Qed.

Lemma set_size_1 : forall X, set_size X = 1 ->
  forall x y, In x X -> In y X -> x = y.
Proof.
intros.
elim (T_dec y x); auto; intro.
exfalso.
rewrite (set_size_remove' _ _ H0) in H.
inversion H.
apply set_size_0 in H3.
apply (set_remove'_3 X b) in H1.
rewrite H3 in H1; inversion H1.
Qed.

Lemma set_size_remove'_lt : forall x (X:set T),
  set_size X <= S (set_size (set_remove' x X)).
Proof.
intros.
elim (In_dec T_dec x X); intro.
+ rewrite <- set_size_remove'; auto.
+ rewrite set_remove'_not_In; auto.
Qed.

Lemma set_size_neq_2 : forall x y (X:set T), x<>y ->
  In x X -> In y X -> set_size X <> 2 -> set_size (set_remove' x X) > 1.
Proof.
intros.
apply lt_S_n.
rewrite <- set_size_remove'; auto.
elim (nat_total_order _ _ H2); auto.
clear H2; intro.
exfalso.
rewrite (set_size_remove' X x) in H2; auto.
rewrite (set_size_remove' (set_remove' x X) y) in H2.
inversion H2. inversion H4. inversion H6.
apply set_remove'_3; auto.
Qed.

End Lists.

Require Import Vector.

Import VectorNotations.

(** * Vectors *)

Section Vectors.

(** ** Equality.
    This is a specialization of a lemma from the standard library. *)
Lemma eq_nth_iff' {A} {n} (v1 v2:t A n) :
  (forall (p:Fin.t n), v1[@p] = v2[@p]) <-> v1 = v2.
Proof.
split.
intro; apply eq_nth_iff; intros; rewrite H0; auto.
intros; apply eq_nth_iff; auto.
Qed.

(** Characterization results for vectors of length up to 3. *)

Lemma vector_1_equal : forall {A} (x y:A), x = y -> forall Hi, [x][@Hi] = [y][@Hi].
Proof.
intros; rewrite H; auto.
Qed.

Lemma vector_2_equal : forall {A} (x x' y y':A), x = x' -> y = y' ->
  forall Hi, [x; y][@Hi] = [x'; y'][@Hi].
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

(** On heads and tails. *)
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

Lemma In_nth : forall {A} {n} (v:t A n) H x, v[@H] = x -> In x v.
Proof.
induction H; simpl.
+ revert n v. refine (@caseS _  _ _); simpl; intros.
  rewrite H; constructor.
+ revert n v H IHt. refine (@caseS _  _ _); simpl; intros.
  constructor. auto.
Qed.

Fixpoint eta_elim_aux {A n} (v:t A (S n)) H :=
  match H with
  | Fin.F1 => hd v
  | Fin.FS H' => (tl v)[@H]
end.

(** Hopefully self-explanatory. *)
Lemma map_shiftin : forall {A} {B} {n} (f:A->B) (v:t A n) x,
  map f (shiftin x v) = shiftin (f x) (map f v).
Proof.
induction v; simpl; auto.
intro.
rewrite IHv; auto.
Qed.

(** ** Alternative map function
    It maps a list of functions onto an argument, rather than the usual. *)
Fixpoint map_inv {A} {B} {n} (f:t (A->B) n) (x:A) : t B n :=
  match f with
  | [] => []
  | (f0 :: fs) => (f0 x) :: (map_inv fs x)
  end.

(* Sanity check.
Definition f0 (n:nat) := 2*n.
Definition f1 (n:nat) := n+3.

Eval compute in (map_inv [f0; f1] 5).
*)

(** The results about map_inv are the same as those for map in the standard library, with analogous
    names. We add a specialization of nth_map. *)
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

Lemma nth_map_inv' {A} {B} {n} (f:t (A->B) n) v (p: Fin.t n) :
  (map_inv f v) [@p] = f[@p] v.
Proof.
apply nth_map_inv; auto.
Qed.

(** Maximum of a vector of natural numbers. *)
Fixpoint vmax {n} (v:t nat n) :=
  match v with
  | [] => 0
  | x :: xs => Nat.max x (vmax xs)
end.

Lemma vmax_leq : forall n v x, vmax (n:=n) v <= x -> forall p, v[@p] <= x.
Proof.
induction p.
* revert n v H; refine (@caseS _ _ _); simpl; intros.
  eapply Nat.max_lub_l; exact H.
* revert n v H p IHp; refine (@caseS _ _ _); simpl; intros.
  apply IHp; eapply Nat.max_lub_r; exact H.
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

End Vectors.
