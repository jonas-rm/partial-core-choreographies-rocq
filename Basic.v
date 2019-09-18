Require Export Bool.
Require Export List.
Require Export Sorting.Permutation.
Require Export Arith.

(* Kill me.
Require Import Coq.Program.Equality.
*)

Ltac destroy H := repeat (elim H; clear H; intro; intro H).
Ltac destroy_as H H' := rename H into H'; set (H:=True); destroy H'; clear H; rename H' into H.

(** * Logical stuff. *)
Section Logical.

(** De Morgan law *)
Lemma deMorganNotOr : forall P Q : Prop,
  ~(P \/ Q) -> ~P /\ ~Q.
Proof.
  unfold not.
  intros P Q PorQ_imp_false.
  split.
  - intros P_holds. apply PorQ_imp_false. left. assumption.
  - intros Q_holds. apply PorQ_imp_false. right. assumption.
Qed.

Lemma or_over_impl : forall (a b c:Prop), ((a \/ b) -> c) -> ((a -> c) /\ (b -> c)).
Proof.
intros a b c.
intros H.
split.
tauto.
tauto.
Qed.

Definition or_add_left : forall A B C, B \/ C -> (A \/ B) \/ C.
Proof.
intros.
inversion H; auto.
Defined.

Definition is_defined (A:Type) (o:option A) : bool :=
match o with
 | Some a => true
 | None => false
end.

End Logical.

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

(** ** A result about permutations. *)

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
split.
apply NoDup_nil.
trivial.
split.
simpl in H.
apply NoDup_cons_iff in H.
inversion_clear H.
apply NoDup_cons.
(* ~ In a (P ++ Q) -> ~ In a P *)
set (myH := (in_or_app P Q a)).
apply or_over_impl in myH; inversion_clear myH.
intro.
apply H0.
apply in_or_app.
auto.
elim IHP; auto.
simpl in H.
inversion H.
elim IHP; auto.
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

Fixpoint eta_elim_aux {A n} (v:t A (S n)) H :=
  match H with
  | Fin.F1 => hd v
  | Fin.FS H' => (tl v)[@H]
end.

(* A variant of the eta lemma from the standard library.
Lemma eta_elim : forall {A} {n} (v:t A (S n)) x Hi, v[@Hi] = x -> hd v = x \/ exists Hi', (tl v)[@Hi'] = x.
Proof.
dependent induction Hi; intros.
- left; rewrite nth_hd in H; auto.
- right; rewrite nth_tl in H; eauto.
Qed.
*)

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
