Require Import FunctionalExtensionality.
Require Import Nat.
Require Import EqNat.
Require Import PeanoNat.
Local Open Scope nat_scope.

Inductive Label : Type :=
 | left : Label
 | right : Label
.

Inductive Expr : Type :=
 | this : Expr
 | zero : Expr
 | succ_this : Expr
.

Lemma eq_expr_dec : forall (e e' : Expr), { e = e' } + { e <> e' }.
Proof.
decide equality.
Qed.

Definition eq_expr (e:Expr) (e':Expr) : bool :=
match (e, e') with
 | (this, this) => true
 | (zero, zero) => true
 | (succ_this, succ_this) => true
 | (_, _) => false
end.

Notation "e == e'" := (eq_expr e e') (at level 60).

Definition Pid := nat.

Definition eq_pid := Nat.eq.

Lemma eq_pid_dec : forall (p p':Pid), { p = p' } + { p <> p' }.
Proof.
decide equality.
Qed.


Definition Value := nat.

Definition Store := Pid -> Value.

Definition evaluate (e:Expr) (s:Store) (p:Pid) : Value :=
match e with
 | zero => 0
 | this => s p
 | succ_this => S (s p)
end.

Definition update (s:Store) (p:Pid) (v:Value) : Store :=
fun (q:Pid) => if (p =? q) then v else (s q)
.

Lemma update_read : forall (s:Store) (p:Pid) (v:Value),
  update s p v p = v.
Proof.
  intros.
  unfold update.
  rewrite <- beq_nat_refl; auto.
Qed.

Lemma update_monotonicity : forall (s:Store) (p q:Pid) (v:Value),
  p <> q -> update s p v q = s q.
Proof.
intros.
unfold update.
case_eq (p =? q); auto.
intro.
generalize (beq_nat_true _ _ H0); intros.
elim H; auto.
Qed.

Lemma update_update : forall (s:Store) (p:Pid) (v1 v2:Value),
  update (update s p v2) p v1 = update s p v1.
Proof.
intros.
unfold update.
apply FunctionalExtensionality.functional_extensionality. (* TODO avoid this *)
unfold update; intro q.
case_eq (p =? q); trivial.
Qed.