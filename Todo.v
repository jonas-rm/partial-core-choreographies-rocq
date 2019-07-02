(** Stupid file, just with lemmas we'd like to prove. *)

(* decidability of termination *)

(*
(** This theorem would be nicer with decidability of termination incorporated... *)
Theorem progress' : forall C s, ~(terminated C) -> WellFormed C ->
  forall c, (C,s) --->* c -> ~terminated (fst c) -> exists c', c ---> c'.
Proof.
intros.
induction c; apply progress; auto.
*)

(*
Lemma Precongr_Congruent_ctx : forall C C' l, WellFormed_ctx C l ->
  C ~<= C' -> C' ~<= C -> Congruent C C'.
Proof.
intros.
elim (Precongr_to_weighted H0); clear H0; intros n HC.
elim (Precongr_to_weighted H1); clear H1; intros n' HC'.
set (k := n+n').
assert (n+n' <= k) as Hk; auto; clearbody k.
revert n n' Hk C C' l H HC HC'; induction k.
+ intros; inversion Hk.
  rewrite (O_plus_O H1) in HC.
  inversion HC; auto.
+ intros.
  elim (O_or_S n); intro Hn.
  2: rewrite <- Hn in HC; inversion HC; auto.
  revert Hk HC.
  elim Hn; intros m Hm; rewrite <- Hm; clear n Hn Hm.
  rename n' into n; intros.
  inversion HC.
  clear C0 C'' n0 H0 H3 H4; rename C'0 into C1.
  apply CTrans with C1.
  - 

Maybe using:

Lemma Precongr_step_Precongr_eq : forall C C' l, WellFormed_ctx C l ->
  C ~<a C' -> C' ~<= C -> C ~<>~ C'.
Proof.
intros.
elim (Precongr_to_weighted H1); intros n Hn; clear H1.
revert C C' H H0 Hn; induction n; intros; inversion Hn.
+ apply Congruent_sym; auto.
+ clear n0 C0 C'' H1 H4 H5 Hn; rename C'0 into C1.
  clear IHn.
  revert dependent C1; induction n; intros; inversion H3; clear H3.
  - clear C0 C'0 H5 H6.

*)
