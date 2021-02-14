Require Export Common.
Require Import CC.

Local Open Scope nat_scope.

Module SPBase (P X V E B R:DecType) (Ev:Eval E X V V) (BEv:Eval B X V Bool).

(** Preamble: a lot of things just as in CC. *)

Module Export PSt := LState V X.
Module Export CSt := GState P V X.
Module Export TL := Transitions P V X R.

Module Bdec := DecidableType B.
Module Edec := DecidableType E.
Module Rdec := DecidableType R.

Definition Expr := E.t.
Definition Expr_dec := Edec.eqb.
Definition BExpr := B.t.
Definition BExpr_dec := Bdec.eqb.
Definition RecVar := R.t.
Definition RecVar_dec := Rdec.eqb.

Definition eval := Ev.eval.
Definition beval := BEv.eval.

Module EvSt := EvalState P E X V V Ev.
Module BEvSt := EvalState P B X V Bool BEv.

Definition eval_on_state := EvSt.eval_on_state.
Definition beval_on_state := BEvSt.eval_on_state.

Definition eval_eq := EvSt.eval_eq.
Definition eval_neq := EvSt.eval_neq.
Definition beval_eq := BEvSt.eval_eq.
Definition beval_neq := BEvSt.eval_neq.

(** * Syntax of processes *)

Section Syntax.

(** ** Behaviours *)

Inductive Behaviour : Type :=
| End : Behaviour
| Send : Pid -> Expr -> Behaviour -> Behaviour
| Recv : Pid -> Var -> Behaviour -> Behaviour
| Sel : Pid -> Label -> Behaviour -> Behaviour
| Branching : Pid -> option Behaviour -> option Behaviour -> Behaviour
| Cond : BExpr -> Behaviour -> Behaviour -> Behaviour
| Call : RecVar -> Behaviour
.

(** In order to do induction on behaviours. *)

Fixpoint depth (B:Behaviour) : nat :=
match B with
 | Send p e B' => 1 + depth B'
 | Recv p x B' => 1 + depth B'
 | Sel p l B' => 1 + depth B'
 | Branching p mB mB' => 1
                         + (match mB with None => 0 | Some B => depth B end)
                         + (match mB' with None => 0 | Some B => depth B end)
 | Cond b B1 B2 => 1 + Nat.max (depth B1) (depth B2)
 | Call X => 1
 | End => 1
end.

Theorem Behaviour_ind' :
  forall P:Behaviour -> Prop,
    P End ->
    (forall p e B, P B -> P (Send p e B)) ->
    (forall p v B, P B -> P (Recv p v B)) ->
    (forall p l B, P B -> P (Sel p l B)) ->
    (forall p mB mB', (forall B, mB = Some B -> P B) ->
                      (forall B, mB' = Some B -> P B) ->
                      P (Branching p mB mB')) ->
    (forall b B1 B2, P B1 -> P B2 -> P (Cond b B1 B2)) ->
    (forall X, P (Call X)) ->
    forall B, P B.
Proof.
intros; revert B.
assert (forall d B, depth B <= d -> P B).
2: eauto.
induction d; intros; case_eq B; intros; auto; rewrite H7 in H6; try (exfalso; inversion H6; fail); auto with arith.
+ clear H H0 H1 H2 H4 H5 H7 B.
  apply H3.
  - intros; apply IHd.
    rewrite H in H6; simpl in H6; apply le_S_n in H6.
    etransitivity. 2: apply H6. auto with arith.
  - intros; apply IHd.
    rewrite H in H6; simpl in H6; apply le_S_n in H6.
    etransitivity. 2: apply H6. auto with arith.
+ apply H4; apply IHd; apply le_S_n in H6.
  - etransitivity. eapply Nat.le_max_l. eauto.
  - etransitivity. eapply Nat.le_max_r. eauto.
Qed.

Theorem Behaviour_rec' :
  forall P:Behaviour -> Type,
    P End ->
    (forall p e B, P B -> P (Send p e B)) ->
    (forall p v B, P B -> P (Recv p v B)) ->
    (forall p l B, P B -> P (Sel p l B)) ->
    (forall p mB mB', (forall B, mB = Some B -> P B) ->
                      (forall B, mB' = Some B -> P B) ->
                      P (Branching p mB mB')) ->
    (forall b B1 B2, P B1 -> P B2 -> P (Cond b B1 B2)) ->
    (forall X, P (Call X)) ->
    forall B, P B.
Proof.
intros; revert B.
assert (forall d B, depth B <= d -> P B).
2: eauto.
induction d; intros; case_eq B; intros; auto; rewrite H0 in H; try (exfalso; inversion H; fail); auto with arith.
+ clear X X0 X1 X2 X4 X5 H0 B.
  apply X3.
  - intros; apply IHd.
    rewrite H0 in H; simpl in H; apply le_S_n in H.
    etransitivity. 2: apply H. auto with arith.
  - intros; apply IHd.
    rewrite H0 in H; simpl in H; apply le_S_n in H.
    etransitivity. 2: apply H. auto with arith.
+ apply X4; apply IHd; apply le_S_n in H.
  - etransitivity. eapply Nat.le_max_l. eauto.
  - etransitivity. eapply Nat.le_max_r. eauto.
Qed.

(** Equality of behaviours is decidable. We are using the fact that equality on labels is decidable. *)
Lemma Behaviour_eq_dec : forall (B B':Behaviour), {B=B'} + {B<>B'}.
Proof.
induction B using Behaviour_rec'; induction B' using Behaviour_rec';
  auto; try (right; discriminate).
+ case (P.eq_dec p p0); intros.
  2: right; intro; inversion H; auto.
  case (E.eq_dec e e0); intros.
  2: right; intro; inversion H; auto.
  elim (IHB B'); intros.
  2: right; intro; inversion H; auto.
  rewrite e1, e2, a; auto.
+ case (P.eq_dec p p0); intros.
  2: right; intro; inversion H; auto.
  case (X.eq_dec v v0); intros.
  2: right; intro; inversion H; auto.
  elim (IHB B'); intros.
  2: right; intro; inversion H; auto.
  rewrite e, e0, a; auto.
+ case (P.eq_dec p p0); intros.
  2: right; intro; inversion H; auto.
  case (eq_label_dec l l0); intros.
  2: right; intro; inversion H; auto.
  elim (IHB B'); intros.
  2: right; intro; inversion H; auto.
  rewrite e, e0, a; auto.
+ case (P.eq_dec p p0); intros.
  2: right; intro; inversion H; auto.
  rewrite <- e; clear e p0.
  case_eq mB; case_eq mB'; case_eq mB0; case_eq mB'0; intros; auto;
    try (right; discriminate).
  - elim (X b2) with b0; auto; intros.
    2: right; intro Hx; inversion Hx; auto.
    elim (X0 b1) with b; auto; intros.
    2: right; intro Hx; inversion Hx; auto.
    rewrite a, a0; auto.
  - elim (X b0) with b; auto; intros.
    rewrite a; auto.
    right; intro Hx; inversion Hx; auto.
  - elim (X0 b0) with b; auto; intros.
    rewrite a; auto.
    right; intro Hx; inversion Hx; auto.
+ case (B.eq_dec b b0); intros.
  2: right; intro; inversion H; auto.
  case (IHB1 B'1); intros.
  2: right; intro; inversion H; auto.
  elim (IHB2 B'2); intros.
  2: right; intro; inversion H; auto.
  rewrite e, e0, a; auto.
+ case (R.eq_dec X X0); intros.
  2: right; intro; inversion H; auto.
  rewrite e; auto.
Qed.

Lemma Behaviour_eq_End_dec : forall (b:Behaviour), {b=End} + {b<>End}.
Proof. intro; case b; auto; right; discriminate.  Qed.

(** ** Networks
  Networks are maps from process names to behaviours.
*)

Definition Network := Pid -> Behaviour.

(** A lot of definitions are parameterised on process lists, for decidability. *)

Definition within_ps (ps:list Pid) (N:Network) :=
  forall p, ~In p ps -> N p = End.

Lemma within_ps_cons : forall ps N, within_ps ps N ->
  forall p, within_ps (p::ps) N.
Proof.
red; intros.
red in H.
apply H; intro.
apply H0; simpl; auto.
Qed.

Lemma within_ps_rev : forall ps N, within_ps ps N ->
  forall p, N p <> End -> In p ps.
Proof.
intros.
elim (In_dec P.eq_dec p ps); auto.
intro. rewrite H in H0; auto.
elim H0; auto.
Qed.

Definition finite_support (N:Network) := exists ps, within_ps ps N.

(** ** Network equality *)

Definition Network_eq (N N':Network) : Prop := forall p, N p = N' p.

(** Network equality is an equivalence relation, as expected. *)

Lemma Network_eq_refl : reflexive _ Network_eq.
Proof. red. red. auto. Qed.

Lemma Network_eq_sym : symmetric _ Network_eq.
Proof. red. red. auto. Qed.

Lemma Network_eq_trans : transitive _ Network_eq.
Proof. red. red. intros. transitivity (y p); auto. Qed.

Lemma Network_eq_within_ps : forall ps N N',
  within_ps ps N -> within_ps ps N' ->
  (forall p, In p ps -> N p = N' p) -> Network_eq N N'.
Proof.
intros.
intro.
elim (In_dec P.eq_dec p ps); intros.
+ clear H0 H.
  induction ps; simpl; intros; inversion_clear a; apply H1; simpl; auto.
+ rewrite H0; auto.
Qed.

(** Programs in SP are pairs, like choreography programs in CC. *)

Definition DefSetB := RecVar -> Behaviour.

Record Program : Type :=
  { Procs : DefSetB;
    Net   : Network }.

Lemma SP_eta : forall P, P = Build_Program (Procs P) (Net P).
Proof. induction P; auto. Qed.

(** Syntactic constructors for building networks as lists *)

Definition EmptyNet : Network := fun _ => End.

Definition Process (p:Pid) (B:Behaviour) : Network :=
  fun p' => if (Pid_dec p' p) then B else End.

Definition Par (N N':Network) :=
  fun p => if (Behaviour_eq_End_dec (N p)) then N' p else N p.

Definition Network_rm (N:Network) (p:Pid) :=
  fun r => if (Pid_dec r p) then End else N r.

(* Generalisation to lists of processes. *)

Definition Network_rm_ps (N:Network) (ps:list Pid) :=
  fun r => if (in_dec P.eq_dec r ps) then End else N r.

Definition Network_res_ps (N:Network) (ps:list Pid) :=
  fun r => if (in_dec P.eq_dec r ps) then N r else End.

End Syntax.

Add Parametric Relation : Network Network_eq
  reflexivity proved by Network_eq_refl
  symmetry proved by Network_eq_sym
  transitivity proved by Network_eq_trans
  as Network_eq_rel.

Declare Scope SP_scope.
Delimit Scope SP_scope with SP.

Bind Scope SP_scope with Behaviour.
Bind Scope SP_scope with Network.

Notation "p ! e ; B" := (Send p e B) (at level 60, e at level 9, right associativity) : SP_scope.
Notation "p ? xx ; B" := (Recv p xx B) (at level 60, right associativity) : SP_scope.
Notation "p (+) l ; B" := (Sel p l B) (at level 49, l at level 9, right associativity) : SP_scope.
Notation "p '&' B1 '//' B2" := (Branching p B1 B2) (at level 60, no associativity) : SP_scope.
Notation "'If' e 'Then' B1 'Else' B2" := (Cond e B1 B2) (at level 60) : SP_scope.
Notation "'bnil'" := (End) : SP_scope.
Notation "'nnil'" := (EmptyNet) : SP_scope.

Notation "N | N'" := (Par N N') (at level 202, right associativity) : SP_scope.
Notation "p [ B ]" := (Process p B) (at level 201, no associativity) : SP_scope.
Notation "N ~~ p" := (Network_rm N p)  (at level 200, no associativity) : SP_scope.

Notation "N == N'" := (Network_eq N N') (at level 100) : SP_scope.

Ltac BInduction B m1 m2 := induction B using Behaviour_ind';
  try case_eq m1; try case_eq m2.

Ltac BDInduction B B' m1 m2 m3 m4:= induction B using Behaviour_ind'; induction B' using Behaviour_ind';
  try case_eq m1; try case_eq m2; try case_eq m3; try case_eq m4.

Open Scope SP_scope.

(*
These do not work - we now have parameters everywhere.
Check (EmptyNet | EmptyNet).
Check (0 [1, bnil]).
Check (Empty | 0 [1, bnil]).
Check (If 0 Then bnil Else bnil).
Check (0!zero; 0?; 1+left; bnil).
*)

(** ** Syntactic properties *)

Section SyntacticProperties.

(** A bunch of useful properties about networks. *)
Lemma EmptyNet_within_ps : forall ps, within_ps ps EmptyNet.
Proof. red; auto. Qed.

Lemma EmptyNet_finite_supp : finite_support EmptyNet.
Proof. exists nil. apply EmptyNet_within_ps. Qed.

Lemma Process_refl : forall p B, (p [B]) p = B.
Proof. intros. unfold Process. rewrite Pdec.eqb_refl; auto. Qed.

Lemma Process_out : forall p B p', p <> p' -> (p [B]) p' = End.
Proof.
intros; unfold Process.
rewrite <- Pdec.eqb_neq, Pdec.eqb_sym in H.
unfold Pid_dec; rewrite H; auto.
Qed.

Lemma Par_proj1 : forall N N' p, N p <> End -> (N | N') p = N p.
Proof.
intros.
unfold Par. elim Behaviour_eq_End_dec; auto.
intro. elim H; auto.
Qed.

Lemma Par_proj2 : forall N N' p, N p = End -> (N | N') p = N' p.
Proof.
intros.
unfold Par. elim Behaviour_eq_End_dec; auto.
intro. elim b; auto.
Qed.

Lemma Par_proj1' : forall N N' p, N' p = End -> (N | N') p = N p.
Proof.
intros.
unfold Par. elim Behaviour_eq_End_dec; auto.
transitivity bnil; auto.
Qed.

Lemma Par_assoc : forall N N' N'',
  Network_eq (N | (N' | N'')) ((N | N') | N'').
Proof.
red; intros.
unfold Par.
do 2 elim Behaviour_eq_End_dec; intros; auto.
elim b; auto.
Qed.

(** Useful results for networks with two processes. *)
Lemma Par_fst : forall p Bp q Bq, p <> q -> (p [Bp] | q [Bq]) p = Bp.
Proof.
intros. elim (Behaviour_eq_End_dec Bp); intro.
- rewrite a, Par_proj2.
  apply Process_out; auto.
  apply Process_refl; auto.
- rewrite Par_proj1; rewrite Process_refl; auto.
Qed.

Lemma Par_snd : forall p Bp q Bq, p <> q -> (p [Bp] | q [Bq]) q = Bq.
Proof.
intros. rewrite Par_proj2.
apply Process_refl; auto.
apply Process_out; auto.
Qed.

(** Lemmas about subterms. *)

Lemma Send_neq_cont : forall p e B, Send p e B <> B.
Proof.
intros; intro.
assert (depth (p!e;B) = depth B). rewrite H; auto.
simpl in H0. apply lt_irrefl with (depth B).
rewrite <- H0 at 2. auto.
Qed.

Lemma Recv_neq_cont : forall p x B, Recv p x B <> B.
Proof.
intros; intro.
apply lt_irrefl with (depth B). rewrite <- H at 2. auto.
Qed.

Lemma Sel_neq_cont : forall p l B, Sel p l B <> B.
Proof.
intros; intro.
apply lt_irrefl with (depth B). rewrite <- H at 2; auto.
Qed.

Lemma Branching_l_neq_cont : forall p Bl Br, Branching p (Some Bl) Br <> Bl.
Proof.
intros; intro.
apply lt_irrefl with (depth Bl). rewrite <- H at 2; simpl.
auto with arith.
Qed.

Lemma Branching_r_neq_cont : forall p Bl Br, Branching p Bl (Some Br) <> Br.
Proof.
intros; intro.
apply lt_irrefl with (depth Br). rewrite <- H at 2; simpl.
auto with arith.
Qed.

Lemma Then_neq_cont : forall b B1 B2, Cond b B1 B2 <> B1.
Proof.
intros; intro.
apply lt_irrefl with (depth B1). rewrite <- H at 2.
apply le_n_S, Nat.le_max_l.
Qed.

Lemma Else_neq_cont : forall b B1 B2, Cond b B1 B2 <> B2.
Proof.
intros; intro.
apply lt_irrefl with (depth B2). rewrite <- H at 2.
apply le_n_S, Nat.le_max_r.
Qed.

(** If two networks do not share any running processes, then their parallel composition is symmetric. *)

Definition Network_disjoint (N N':Network) :=
  forall p, N p = End \/ N' p = End.

Lemma Network_disjoint_sym : forall N N',
  Network_disjoint N N' -> Network_disjoint N' N.
Proof.
unfold Network_disjoint; intros.
elim (H p); auto.
Qed.

Lemma Par_comm : forall N N', Network_disjoint N N' -> (N | N') == (N' | N).
Proof.
red; intros.
unfold Par.
do 2 elim Behaviour_eq_End_dec; intros; auto.
+ transitivity End; auto.
+ exfalso.
  elim (H p); auto.
Qed.

Lemma Par_eq : forall N1 N2 N1' N2',
  (N1 == N1') -> (N2 == N2') -> (N1 | N2) == (N1' | N2').
Proof.
intros; intro.
unfold Par.
rewrite H, H0. auto.
Qed.

(** Properties of removal. *)

Lemma Network_rm_In : forall N p, (Network_rm N p) p = End.
Proof.
intros; unfold Network_rm.
rewrite Pdec.eqb_refl; auto.
Qed.

Lemma Network_rm_out : forall N p p', p <> p' ->
  Network_rm N p p' = N p'.
Proof.
intros; unfold Network_rm.
rewrite <- Pdec.eqb_neq in H.
unfold Pid_dec; rewrite Pdec.eqb_sym, H; auto.
Qed.

Lemma Network_rm_add :
  forall N p, N == (Network_rm N p | p [N p]).
Proof.
intros.
red. unfold Network_rm, Process, Par. intro.
case_eq (Pid_dec p0 p); intros.
+ rewrite Pdec.eqb_eq in H. rewrite H.
  elim Behaviour_eq_End_dec; auto.
  intro H'. contradiction.
+ elim Behaviour_eq_End_dec; auto.
Qed.

Lemma Network_rm_within_ps : forall N p ps,
  within_ps (p::ps) N -> within_ps ps (Network_rm N p).
Proof.
red; intros. unfold Network_rm.
case_eq (Pid_dec p0 p); auto.
intro; apply H; auto. intro; apply H0; auto.
inversion_clear H2; auto. rewrite H3 in H1; rewrite Pdec.eqb_neq in H1.
elim H1; auto.
Qed.

Lemma Network_rm_add_2_p : forall N p q Bp Bq, p <> q ->
  (Network_rm (Network_rm N p) q | p [Bp] | q [Bq]) p = Bp.
Proof.
intros. rewrite Par_proj2, Par_fst; auto.
rewrite Network_rm_out, Network_rm_In; auto.
Qed.

Lemma Network_rm_add_2_q : forall N p q Bp Bq, p <> q ->
  (Network_rm (Network_rm N p) q | p [Bp] | q [Bq]) q = Bq.
Proof.
intros. rewrite Par_proj2, Par_snd; auto.
apply Network_rm_In; auto.
Qed.

Lemma Network_rm_add_2_out : forall N p q r Bp Bq,
  p <> r -> q <> r ->
  (Network_rm (Network_rm N p) q | p [Bp] | q [Bq]) r = N r.
Proof.
intros. elim (Behaviour_eq_End_dec (N r)); intro.
repeat rewrite Par_proj2; try rewrite Process_out; auto.
repeat rewrite Network_rm_out; auto.
rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
Qed.

Lemma Network_rm_eq : forall N N', Network_eq N N' ->
  forall p, (Network_rm N p) == (Network_rm N' p).
Proof.
red; intros. unfold Network_rm.
case_eq (Pid_dec p0 p); auto.
Qed.

Lemma Network_rm_res_ps :
  forall N ps, N == (Network_rm_ps N ps | Network_res_ps N ps).
Proof.
intros.
red. unfold Network_rm_ps, Network_res_ps, Par. intro.
case_eq (in_dec P.eq_dec p ps); intros.
+ elim Behaviour_eq_End_dec; auto.
  intro. contradiction.
+ elim Behaviour_eq_End_dec; auto.
Qed.

(** Rewriting of networks. *)

Lemma Network_eq_cross'' : forall N N1 N2 p q Bp Bq,
  p <> q -> Network_eq N1 (Network_rm N p| p [Bp]) ->
  Network_eq N2 (Network_rm N q | q [Bq]) ->
  (Network_rm N2 p | p [Bp]) == (Network_rm N1 q | q [Bq]).
Proof.
intros; intro x.
case (P.eq_dec x p); intro Hxp. rewrite Hxp.
rewrite Par_proj2, Par_proj1', Process_refl, Network_rm_out, H0, Par_proj2, Process_refl; auto.
1, 3: apply Network_rm_In. apply Process_out; auto.
case (P.eq_dec x q); intro Hxq. rewrite Hxq.
rewrite Par_proj1', Par_proj2, Process_refl, Network_rm_out, H1, Par_proj2, Process_refl; auto.
1, 2: apply Network_rm_In. apply Process_out; auto.
(* final case *)
rewrite Par_proj1', Par_proj1'. repeat rewrite Network_rm_out; auto.
rewrite H0, H1, Par_proj1', Par_proj1'. repeat rewrite Network_rm_out; auto.
all: rewrite Process_out; auto.
Qed.

Lemma Network_eq_cross' : forall N N1 N2 p q r Bp Bq Br,
  p <> q -> p <> r -> q <> r ->
  Network_eq N1 (Network_rm (Network_rm N p) q | p [Bp] | q [Bq]) ->
  Network_eq N2 (Network_rm N r | r [Br]) ->
  (Network_rm (Network_rm N2 p) q | p [Bp] | q [Bq])
             == (Network_rm N1 r | r [Br]).
Proof.
intros; intro x.
case (P.eq_dec x p); intro Hxp. rewrite Hxp.
rewrite Network_rm_add_2_p, Par_proj1', Network_rm_out, H2, Network_rm_add_2_p; auto.
rewrite Process_out; auto.
case (P.eq_dec x q); intro Hxq. rewrite Hxq.
rewrite Network_rm_add_2_q, Par_proj1', Network_rm_out, H2, Network_rm_add_2_q; auto.
rewrite Process_out; auto.
case (P.eq_dec x r); intro Hxr. rewrite Hxr.
rewrite Network_rm_add_2_out, Par_proj2, Process_refl, H3, Par_proj2, Process_refl; auto; apply Network_rm_In.
(* final case *)
rewrite Par_proj1', Par_proj1'. repeat rewrite Network_rm_out; auto.
rewrite H2, H3, Par_proj1', Par_proj1'. repeat rewrite Network_rm_out; auto.
all: try rewrite Par_proj1'; rewrite Process_out; auto.
Qed.

Lemma Network_eq_cross : forall N N1 N2 p q r s Bp Bq Br Bs,
  p <> q -> p <> r -> p <> s -> q <> r -> q <> s -> r <> s ->
  Network_eq N1 (Network_rm (Network_rm N p) q | p [Bp] | q [Bq]) ->
  Network_eq N2 (Network_rm (Network_rm N r) s | r [Br] | s [Bs]) ->
  (Network_rm (Network_rm N2 p) q | p [Bp] | q [Bq])
             == (Network_rm (Network_rm N1 r) s | r [Br] | s [Bs]).
Proof.
intros; intro x.
case (P.eq_dec x p); intro Hxp. rewrite Hxp.
rewrite Network_rm_add_2_p, Par_proj1', Network_rm_out, Network_rm_out, H5, Network_rm_add_2_p; auto.
rewrite Par_proj1'; rewrite Process_out; auto.
case (P.eq_dec x q); intro Hxq. rewrite Hxq.
rewrite Network_rm_add_2_q, Par_proj1', Network_rm_out, Network_rm_out, H5, Network_rm_add_2_q; auto.
rewrite Par_proj1'; rewrite Process_out; auto.
case (P.eq_dec x r); intro Hxp0. rewrite Hxp0.
rewrite Network_rm_add_2_p, Par_proj1', Network_rm_out, Network_rm_out, H6, Network_rm_add_2_p; auto.
rewrite Par_proj1'; rewrite Process_out; auto.
case (P.eq_dec x s); intro Hxq0. rewrite Hxq0.
rewrite Network_rm_add_2_q, Par_proj1', Network_rm_out, Network_rm_out, H6, Network_rm_add_2_q; auto.
rewrite Par_proj1'; rewrite Process_out; auto.
(* final case *)
rewrite Par_proj1', Par_proj1'. repeat rewrite Network_rm_out; auto.
rewrite H5, H6, Par_proj1', Par_proj1'. repeat rewrite Network_rm_out; auto.
all: rewrite Par_proj1'; rewrite Process_out; auto.
Qed.

(* This construction makes the following lemma easier to prove. *)
Lemma Network_eq_within_ps_dec : forall ps N N', within_ps ps N -> within_ps ps N' ->
  { N == N' }+{~ (N == N') }.
Proof.
induction ps; intros.
+ left. intro. rewrite H, H0; auto.
+ elim (Behaviour_eq_dec (N a) (N' a)); intros.
  2: right; intro; auto.
  elim (IHps (Network_rm N a) (Network_rm N' a)); intros;
  try (apply Network_rm_within_ps; auto).
  - left; intro.
    case (P.eq_dec p a); intro. rewrite e; auto.
    generalize (a1 p).
    rewrite <- Pdec.eqb_neq in n. fold Pid_dec in n.
    unfold Network_rm; rewrite n; auto.
  - right; intro.
    apply b; intro.
    apply Network_rm_eq; auto.
Qed.

(* Equivalence of processes - where?
Fixpoint Behaviour_equiv (B1 B2:Behaviour) : Prop :=
match B1, B2 with
| bnil, bnil => True
| Call X, Call Y   => X = Y
| (p ! e; B), (p' ! e'; B') => p = p' /\ e = e' /\ Behaviour_equiv B B'
| (p ? x; B), (p' ? x'; B') => p = p' /\ x = x' /\ Behaviour_equiv B B'
| (p (+) l; B), (p' (+) l'; B') => p = p' /\ l = l' /\ Behaviour_equiv B B'
| (p & B1 // B2), (p' & B1' // B2') => p = p' /\ (OptionBehaviour_equiv B1 B1') /\ (OptionBehaviour_equiv B2 B2')
| (If e Then Bt Else Be), (If e' Then Bt' Else Be') => e = e' /\ Behaviour_equiv Bt Bt' /\ Behaviour_equiv Be Be'
| _, _ => False
end

with

OptionBehaviour_equiv (O O':option Behaviour) : Prop :=
match O, O' with
| None, None => True
| Some B, Some B'=> Behaviour_equiv B B'
| _, _ => False
end.
*)

(** ** Well-formedness
  We do not know whether we need well-formedness of processes yet.
  Well-formedness does not check that, in branchings, all labels are distinct.
*)

Fixpoint Behaviour_WF (p:Pid) (B:Behaviour) : Prop :=
match B with
| bnil => True
| Call _ => True
| (q ! _; B') => p <> q /\ Behaviour_WF p B'
| (q ? _; B') => p <> q /\ Behaviour_WF p B'
| (q (+) l; B') => p <> q /\ Behaviour_WF p B'
| (q & B1 // B2) => p <> q
                /\ (match B1 with None => True | Some B => Behaviour_WF p B end)
                /\ (match B2 with None => True | Some B => Behaviour_WF p B end)
| (If e Then B1 Else B2) => Behaviour_WF p B1 /\ Behaviour_WF p B2
end.

Lemma Behaviour_WF_dec : forall p B,
  {Behaviour_WF p B} + {~Behaviour_WF p B}.
Proof.
induction B using Behaviour_rec'; simpl; auto;
  try (elim (P.eq_dec p p0); intro; [idtac | inversion_clear IHB; auto];
  right; intro H'; inversion_clear H'; auto).
+ elim (P.eq_dec p p0); intro.
  1: right; rewrite a; tauto.
  case_eq mB; case_eq mB'; auto; intros.
  - elim (X b1); auto. 2: right; tauto.
    elim (X0 b0); tauto.
  - elim (X b0); tauto.
  - elim (X0 b0); tauto.
+ inversion_clear IHB1.
  2: right; intro H'; inversion_clear H'; auto.
  inversion_clear IHB2; auto.
  right; intro H'; inversion_clear H'; auto.
Qed.

Definition Network_WF (N:Network) : Prop :=
  forall p, Behaviour_WF p (N p).

Lemma Network_WF_dec : forall ps N, within_ps ps N ->
  {Network_WF N} + {~Network_WF N}.
Proof.
induction ps; simpl; intros.
+ left; intro; rewrite H; simpl; auto.
+ elim (Behaviour_WF_dec a (N a)); intro.
  2: right; intro; auto.
  elim (IHps (Network_rm N a)).
  3: apply Network_rm_within_ps; auto.
  - left; intro.
    case (P.eq_dec p a); intro.
    1: rewrite e; auto.
    generalize (a1 p).
    rewrite <- Pdec.eqb_neq in n.
    unfold Network_rm. unfold Pid_dec. rewrite n; auto.
  - right; intro.
    apply b; intro.
    unfold Network_rm.
    case Pid_dec; simpl; auto.
Qed.

Lemma Par_WF : forall N N', Network_WF N -> Network_WF N' ->
  Network_WF (N | N').
Proof.
intros; intro.
elim (Behaviour_eq_End_dec (N p)); intro.
1: rewrite Par_proj2; auto.
rewrite Par_proj1; auto.
Qed.

Lemma WF_Par1 : forall N N', Network_WF (N | N') -> Network_WF N.
Proof.
intros; intro.
elim (Behaviour_eq_End_dec (N p)); intro.
1: rewrite a; simpl; auto.
rewrite <- (Par_proj1 N N'); auto.
Qed.

Lemma WF_Par2 : forall N N', Network_disjoint N N' ->
  Network_WF (N | N') -> Network_WF N'.
Proof.
intros; intro.
elim (Behaviour_eq_End_dec (N' p)); intro.
1: rewrite a; simpl; auto.
rewrite <- (Par_proj2 N N'); auto.
elim (Behaviour_eq_End_dec (N p)); auto.
intro; exfalso.
elim (H p); auto.
Qed.

Lemma Network_WF_par : forall N N', Network_disjoint N N' ->
  Network_WF (N | N') -> Network_WF N /\ Network_WF N'.
Proof.
split.
apply WF_Par1 with N'; auto.
apply WF_Par2 with N; auto.
Qed.

Lemma Network_WF_comm : forall N N', Network_disjoint N N' ->
  Network_WF (N | N') -> Network_WF (N' | N).
Proof.
intros.
elim (Network_WF_par N N'); intros; auto.
apply Par_WF; auto.
Qed.

(* WF program doesn't make sense, because procedures don't know the processes
  that will execute them, so we do not know what to pass to Behaviour_WF.
   But: program with WF network reduces to program with WF network is
   an interesting property that is guaranteed by EPP. *)

End SyntacticProperties.

(** * Semantics of SP *)

Section Semantics.

(* Needed?
Definition Network_eq_upTo (N:Network) ps N' : Prop :=
  forall p, ~In p ps -> N' p = N p.
*)

(** Same strategy as for CC. *)

Inductive SP_To (Defs : DefSetB) :
  Network -> State -> RichLabel -> Network -> State -> Prop :=
 | S_Com N p e B q x B' N' s s' :
    N p = (q ! e ; B) -> N q = (p ? x ; B') ->
    let v := (eval_on_state e s p) in
    Network_eq N' ((Network_rm (Network_rm N p) q) | p[B] | q[B']) ->
    eq_state_ext s' (update s q x v) ->
    SP_To Defs N s (R_Com p v q x) N' s'
 | S_LSel N p B q Bl Br N' s s' :
    N p = (q (+) left ; B) -> N q = (p & Some Bl // Br) ->
    Network_eq N' ((Network_rm (Network_rm N p) q) | p[B] | q[Bl]) ->
    eq_state_ext s s' ->
    SP_To Defs N s (R_Sel p q left) N' s'
 | S_RSel N p B q Bl Br N' s s' :
    N p = (q (+) right ; B) -> N q = (p & Bl // Some Br) ->
    Network_eq N' ((Network_rm (Network_rm N p) q) | p[B] | q[Br]) ->
    eq_state_ext s s' ->
    SP_To Defs N s (R_Sel p q right) N' s'
 | S_Then N p b B1 B2 N' s s' :
    N p = (If b Then B1 Else B2) ->
    beval_on_state b s p = true ->
    Network_eq N' ((Network_rm N p) | p[B1]) ->
    eq_state_ext s s' ->
    SP_To Defs N s (R_Cond p) N' s'
 | S_Else N p b B1 B2 N' s s' :
    N p = (If b Then B1 Else B2) ->
    beval_on_state b s p = false ->
    Network_eq N' ((Network_rm N p) | p[B2]) ->
    eq_state_ext s s' ->
    SP_To Defs N s (R_Cond p) N' s'
 | S_Call N p X N' s s' :
    N p = Call X ->
    Network_eq N' ((Network_rm N p) | p[Defs X]) ->
    eq_state_ext s s' ->
    SP_To Defs N s (R_Call X p) N' s'.

(** Default reductions. *)

Lemma S_Com' : forall Defs N p e B q x B' s,
  N p = (q ! e ; B) -> N q = (p ? x ; B') ->
  let v := (eval_on_state e s p) in
  SP_To Defs N s (R_Com p v q x) ((Network_rm (Network_rm N p) q) | p[B] | q[B']) (update s q x v).
Proof. intros. apply S_Com with B B'; auto. reflexivity. ESEr. Qed.

Lemma S_LSel' : forall Defs N p B q Bl Br s,
  N p = (q (+) left ; B) -> N q = (p & Some Bl // Br) ->
  SP_To Defs N s (R_Sel p q left) ((Network_rm (Network_rm N p) q) | p[B] | q[Bl]) s.
Proof. intros. apply S_LSel with B Bl Br; auto. reflexivity. ESEr. Qed.

Lemma S_RSel' : forall Defs N p B q Bl Br s,
  N p = (q (+) right ; B) -> N q = (p & Bl // Some Br) ->
  SP_To Defs N s (R_Sel p q right) ((Network_rm (Network_rm N p) q) | p[B] | q[Br]) s.
Proof. intros. apply S_RSel with B Bl Br; auto. reflexivity. ESEr. Qed.

Lemma S_Then' : forall Defs N p b B1 B2 s,
  N p = (If b Then B1 Else B2) ->
  beval_on_state b s p = true ->
  SP_To Defs N s (R_Cond p) ((Network_rm N p) | p[B1]) s.
Proof. intros. apply S_Then with b B1 B2; auto. reflexivity. ESEr. Qed.

Lemma S_Else' : forall Defs N p b B1 B2 s,
  N p = (If b Then B1 Else B2) ->
  beval_on_state b s p = false ->
  SP_To Defs N s (R_Cond p) ((Network_rm N p) | p[B2]) s.
Proof. intros. apply S_Else with b B1 B2; auto. reflexivity. ESEr. Qed.

Lemma S_Call' : forall Defs N p X s,
  N p = Call X ->
  SP_To Defs N s (R_Call X p) ((Network_rm N p) | p[Defs X]) s.
Proof. intros. apply S_Call; auto. reflexivity. ESEr. Qed.

Definition Configuration : Type := Program * State.

Inductive SPP_To : Configuration -> TransitionLabel -> Configuration -> Prop :=
 | SPP_To_intro Defs N s t N' s' : SP_To Defs N s t N' s' ->
     SPP_To (Build_Program Defs N,s) (forget t) (Build_Program Defs N',s').

Inductive SPP_ToStar : Configuration -> list TransitionLabel -> Configuration -> Prop :=
 | SPT_Refl c : SPP_ToStar c nil c
 | SPT_Step c1 t c2 l c3 : SPP_To c1 t c2 -> SPP_ToStar c2 l c3 -> SPP_ToStar c1 (t::l) c3
.

End Semantics.

Bind Scope SP_scope with SP_To.
Notation "C --[ l ]--> C'" := (SPP_To C l C') (at level 50, left associativity) : SP_scope.
Notation "C --[ ls ]-->* C'" := (SPP_ToStar C ls C') (at level 50, left associativity) : SP_scope.

Section Determinism.

(** ** Results on determinism of the semantics.
  These results are named consistently with CC. *)

(** Reductions are preserved by state equivalence... *)

Lemma SP_To_eq : forall Defs N tl s1 N' s2 s1' s2',
  eq_state_ext s1 s1' -> eq_state_ext s2 s2' ->
  SP_To Defs N s1 tl N' s2 -> SP_To Defs N s1' tl N' s2'.
Proof.
intros.
induction H1.
+ unfold v.
  rewrite (eval_eq e s s1'); auto.
  apply S_Com with B B'; auto.
  ESEt s'. ESEs. eESEt.
  rewrite <- (eval_eq e s s1'); auto. fold v.
  ESEc; auto.
+ apply S_LSel with B Bl Br; auto. ESEt s. ESEs. ESEt s'.
+ apply S_RSel with B Bl Br; auto. ESEt s. ESEs. ESEt s'.
+ apply S_Then with b B1 B2; auto.
  rewrite <- (beval_eq b s); auto.
  ESEt s. ESEs. ESEt s'.
+ apply S_Else with b B1 B2; auto.
  rewrite <- (beval_eq b s); auto.
  ESEt s. ESEs. ESEt s'.
+ apply S_Call; auto. ESEt s. ESEs. ESEt s'.
Qed.

Lemma SPP_To_eq : forall P s1 tl P' s2 s1' s2',
  eq_state_ext s1 s1' -> eq_state_ext s2 s2' ->
  (P,s1) --[tl]--> (P',s2) -> (P,s1') --[tl]--> (P',s2').
Proof.
intros.
induction P.
inversion H1; constructor.
apply SP_To_eq with s1 s2; auto.
Qed.

Lemma SPP_ToStar_eq : forall P s1 tl P' s2 s1' s2',
  eq_state_ext s1 s1' -> eq_state_ext s2 s2' -> tl <> nil ->
  (P,s1) --[tl]-->* (P',s2) -> (P,s1') --[tl]-->* (P',s2').
Proof.
intros P s1 tl; revert P s1.
induction tl; intros. elim H1; auto.
case_eq tl; intros.
+ rewrite H3 in H2; inversion H2.
  inversion H9. rewrite H12 in H7.
  apply SPT_Step with (P',s2'). 2: constructor.
  apply SPP_To_eq with s1 s2; auto.
+ inversion H2.
  induction c2.
  apply SPT_Step with (a0,b).
  - apply SPP_To_eq with s1 b; auto. ESEr.
  - rewrite <- H3. eapply IHtl; eauto. ESEr.
    rewrite H3; discriminate.
Qed.

(** ...and by network equivalence. *)

Lemma SP_To_Network_eq : forall N1 N1' N2 SPDefs s s' t,
    (N1 == N2) -> SP_To SPDefs N1 s t N1' s' -> SP_To SPDefs N2 s t N1' s'.
Proof.
intros.
inversion H0.
+ apply S_Com with B B'; auto.
  1, 2: rewrite <- H; auto.
  etransitivity. eauto.
  apply Par_eq. 2: reflexivity.
  repeat apply Network_rm_eq; auto.
+ apply S_LSel with B Bl Br; auto.
  1, 2: rewrite <- H; auto.
  etransitivity. eauto.
  apply Par_eq. 2: reflexivity.
  repeat apply Network_rm_eq; auto.
+ apply S_RSel with B Bl Br; auto.
  1, 2: rewrite <- H; auto.
  etransitivity. eauto.
  apply Par_eq. 2: reflexivity.
  repeat apply Network_rm_eq; auto.
+ apply S_Then with b B1 B2; auto.
  rewrite <- H; auto.
  etransitivity. eauto.
  apply Par_eq. 2: reflexivity.
  apply Network_rm_eq; auto.
+ apply S_Else with b B1 B2; auto.
  rewrite <- H; auto.
  etransitivity. eauto.
  apply Par_eq. 2: reflexivity.
  apply Network_rm_eq; auto.
+ apply S_Call; auto.
  rewrite <- H; auto.
  etransitivity. eauto.
  apply Par_eq. 2: reflexivity.
  apply Network_rm_eq; auto.
Qed.

(** The set of procedure definitions never changes. *)

Hypothesis Defs : DefSetB.

Lemma SPP_To_Defs_stable : forall Defs' N N' tl s s',
  (Build_Program Defs N,s) --[tl]--> (Build_Program Defs' N',s') -> Defs = Defs'.
Proof. intros. inversion H. inversion H; auto. Qed.

Lemma SPP_ToStar_Defs_stable : forall Defs' N N' tl s s',
  (Build_Program Defs N,s) --[tl]-->* (Build_Program Defs' N',s') -> Defs = Defs'.
Proof.
intros Defs' N N' tl; revert N N'.
induction tl; intros; inversion H; clear H; auto.
clear c1 c3 H2 H4 t l H0 H1.
induction c2. induction a0.
apply SPP_To_Defs_stable in H3.
rewrite <- H3 in H5.
eauto.
Qed.

(** Reductions and state. *)

Lemma SP_To_disjoint_eval : forall N s tl s' p e N',
  disjoint_p_rl p tl -> SP_To Defs N s tl N' s' ->
  eval_on_state e s p = eval_on_state e s' p.
Proof.
intros.
induction H0; auto; try (apply eval_eq; auto; fail).
inversion_clear H.
transitivity (eval_on_state e (update s q x v) p).
apply eval_neq; auto.
apply eval_eq; ESEs.
Qed.

Lemma SP_To_disjoint_beval : forall N s tl s' p b N',
  disjoint_p_rl p tl -> SP_To Defs N s tl N' s' ->
  beval_on_state b s p = beval_on_state b s' p.
Proof.
intros.
induction H0; auto; try (apply beval_eq; auto; fail).
inversion_clear H.
transitivity (beval_on_state b (update s q x v) p).
apply beval_neq; auto.
apply beval_eq; ESEs.
Qed.

Lemma SP_To_disjoint_update : forall N s tl s' p x v N',
  disjoint_p_rl p tl -> SP_To Defs N s tl N' s' ->
  SP_To Defs N (update s p x v) tl N' (update s' p x v).
Proof.
intros.
induction H0; try (constructor; auto; try ESEc; auto; fail).
+ inversion_clear H.
  unfold v0. unfold eval_on_state. rewrite (eval_neq e s p0 p x v); auto.
  apply S_Com with B B'; auto.
  unfold eval_on_state. rewrite <- (eval_neq e s p0 p x v); auto.
  fold v0.
  ESEt (update (update s q x0 v0) p x v). ESEc; auto.
  apply update_independent; auto.
+ apply S_LSel with B Bl Br; auto. ESEc; auto.
+ apply S_RSel with B Bl Br; auto. ESEc; auto.
+ apply S_Then with b B1 B2; auto.
  rewrite <- beval_neq; auto.
  ESEc; auto.
+ apply S_Else with b B1 B2; auto.
  rewrite <- beval_neq; auto.
  ESEc; auto.
Qed.

(** Determinism of reductions given the label. *)
Lemma SP_To_deterministic_1 : forall N N1 N2 tl s s1 s2,
  SP_To Defs N s tl N1 s1 -> SP_To Defs N s tl N2 s2 -> N1 == N2.
Proof.
induction tl; intros; inversion H; inversion H0.
- rewrite H19 in H7; rewrite H22 in H10.
  inversion H7; inversion H10.
  rewrite H27, H28 in H23.
  etransitivity; eauto. symmetry; auto.
- rewrite H15 in H4; rewrite H18 in H7.
  inversion H4; inversion H7.
  rewrite H24, H25 in H21.
  etransitivity; eauto. symmetry; auto.
- rewrite H15 in H4; inversion H4.
- rewrite H15 in H4; inversion H4.
- rewrite H15 in H4; rewrite H18 in H7.
  inversion H4; inversion H7.
  rewrite H24, H26 in H21.
  etransitivity; eauto. symmetry; auto.
- rewrite H11 in H2; inversion H2.
  rewrite H21 in H13.
  etransitivity; eauto. symmetry; auto.
- rewrite H11 in H2; inversion H2.
  rewrite H20 in H12; rewrite H3 in H12; inversion H12.
- rewrite H11 in H2; inversion H2.
  rewrite H20 in H12; rewrite H3 in H12; inversion H12.
- rewrite H11 in H2; inversion H2.
  rewrite H22 in H13.
  etransitivity; eauto. symmetry; auto.
- etransitivity; eauto. symmetry; auto.
Qed.

Lemma SP_To_deterministic_2 : forall N N1 N2 tl s s1 s2,
  SP_To Defs N s tl N1 s1 -> SP_To Defs N s tl N2 s2 ->
  eq_state_ext s1 s2.
Proof.
induction tl; intros; inversion H; inversion H0;
  try (ESEt s; auto; ESEs; fail).
- rewrite H2 in H12; rewrite H14 in H24.
  eESEt. ESEs.
Qed.

Lemma SP_To_deterministic : forall N N1 N2 tl1 tl2 s s1 s2,
  SP_To Defs N s tl1 N1 s1 -> SP_To Defs N s tl2 N2 s2 ->
  tl1 = tl2 -> (N1 == N2) /\ eq_state_ext s1 s2.
Proof.
intros.
rewrite H1 in H; split.
eapply SP_To_deterministic_1; eauto.
eapply SP_To_deterministic_2; eauto.
Qed.

(* This one does not hold...
Lemma SP_To_deterministic_3 : forall N N' tl1 tl2 s s1 s2,
  SP_To Defs N s tl1 N' s1 -> SP_To Defs N s tl2 N' s2 ->
  tl1 = tl2.
*)

Ltac diff_assert p q H1 H2 H3 := assert (p <> q) as H1;
  [intro H1; rewrite H1, H2 in H3; inversion H3 | idtac].

Lemma SP_To_deterministic_4 : forall N N' tl1 tl2 s s1 s2,
  SP_To Defs N s tl1 N' s1 -> SP_To Defs N s tl2 N' s2 ->
  eq_state_ext s1 s2.
Proof.
induction tl1; induction tl2; intros; inversion H; inversion H0;
  try (ESEt s; ESEs; fail).
+ (* Com/Com *)
  case (P.eq_dec p p0); intro.
  - eESEt; eauto. ESEs; eESEt; eauto.
    unfold v2, v3.
    rewrite e1, H19 in H7; inversion H7.
    rewrite e1.
    rewrite <- H26, H22 in H10; inversion H10.
    ESEr.
  - exfalso.
    diff_assert p q0 Hpq0 H22 H7.
    diff_assert p q Hpq H10 H7.
    generalize (H11 p); generalize (H23 p); intros.
    rewrite Network_rm_add_2_out in H25; auto.
    rewrite Network_rm_add_2_p in H26; auto.
    rewrite H25, H7 in H26. apply (Send_neq_cont _ _ _ H26).
+ (* Com/Left *)
  exfalso.
  diff_assert p p0 Hpq0 H16 H7.
  diff_assert p q0 Hpp0 H19 H7.
  diff_assert p q Hpq H10 H7.
  generalize (H11 p); generalize (H22 p); intros.
  rewrite Network_rm_add_2_p in H25; auto.
  rewrite Network_rm_add_2_out in H24; auto.
  rewrite H24, H7 in H25. apply (Send_neq_cont _ _ _ H25).
+ (* Com/Right *)
  exfalso.
  diff_assert p p0 Hpq0 H16 H7.
  diff_assert p q0 Hpp0 H19 H7.
  diff_assert p q Hpq H10 H7.
  generalize (H11 p); generalize (H22 p); intros.
  rewrite Network_rm_add_2_p in H25; auto.
  rewrite Network_rm_add_2_out in H24; auto.
  rewrite H24, H7 in H25. apply (Send_neq_cont _ _ _ H25).
+ (* Com/Then *)
  exfalso.
  diff_assert p p0 Hpp0 H14 H7.
  diff_assert p q Hpq H10 H7.
  generalize (H11 p); generalize (H16 p); intros.
  rewrite Par_proj1, Network_rm_out in H22; auto.
  2: rewrite Network_rm_out, H7; auto; discriminate.
  rewrite Network_rm_add_2_p in H23; auto.
  rewrite H22, H7 in H23. apply (Send_neq_cont _ _ _ H23).
+ (* Com/Else *)
  exfalso.
  diff_assert p p0 Hpp0 H14 H7.
  diff_assert p q Hpq H10 H7.
  generalize (H11 p); generalize (H16 p); intros.
  rewrite Par_proj1, Network_rm_out in H22; auto.
  2: rewrite Network_rm_out, H7; auto; discriminate.
  rewrite Network_rm_add_2_p in H23; auto.
  rewrite H22, H7 in H23. apply (Send_neq_cont _ _ _ H23).
+ (* Com/Call *)
  exfalso.
  diff_assert p p0 Hpp0 H15 H7.
  diff_assert p q Hpq H10 H7.
  generalize (H11 p); generalize (H18 p); intros.
  rewrite Par_proj1, Network_rm_out in H22; auto.
  2: rewrite Network_rm_out, H7; auto; discriminate.
  rewrite Network_rm_add_2_p in H23; auto.
  rewrite H22, H7 in H23. apply (Send_neq_cont _ _ _ H23).
+ (* Left/Com *)
  exfalso.
  diff_assert p p0 Hpp0 H18 H4.
  diff_assert p q0 Hpq0 H21 H4.
  diff_assert p q Hpq H7 H4.
  generalize (H10 p); generalize (H22 p); intros.
  rewrite Network_rm_add_2_out in H24; auto.
  rewrite Network_rm_add_2_p in H25; auto.
  rewrite H24, H4 in H25. apply (Sel_neq_cont _ _ _ H25).
+ (* Right/Com *)
  exfalso.
  diff_assert p p0 Hpp0 H18 H4.
  diff_assert p q0 Hpq0 H21 H4.
  diff_assert p q Hpq H7 H4.
  generalize (H10 p); generalize (H22 p); intros.
  rewrite Network_rm_add_2_out in H24; auto.
  rewrite Network_rm_add_2_p in H25; auto.
  rewrite H24, H4 in H25. apply (Sel_neq_cont _ _ _ H25).
+ (* Then/Com *)
  exfalso.
  diff_assert p p0 Hpp0 H16 H2.
  diff_assert p q Hpq H19 H2.
  generalize (H4 p); generalize (H20 p); intros.
  rewrite Network_rm_add_2_out in H22; auto.
  rewrite Par_proj2, Process_refl in H23.
  2: rewrite Network_rm_In; auto.
  rewrite H22, H2 in H23. apply (Then_neq_cont _ _ _ H23).
+ (* Else/Com *)
  exfalso.
  diff_assert p p0 Hpp0 H16 H2.
  diff_assert p q Hpq H19 H2.
  generalize (H4 p); generalize (H20 p); intros.
  rewrite Network_rm_add_2_out in H22; auto.
  rewrite Par_proj2, Process_refl in H23.
  2: rewrite Network_rm_In; auto.
  rewrite H22, H2 in H23. apply (Else_neq_cont _ _ _ H23).
+ (* Call/Com *)
  exfalso.
  diff_assert p p0 Hpp0 H16 H3.
  diff_assert p q Hpq H19 H3.
  diff_assert p0 q Hp0q H19 H16.
  generalize (H6 q); generalize (H20 q); intros.
  rewrite Network_rm_add_2_q in H22; auto.
  rewrite Par_proj1, Network_rm_out in H23; auto.
  2: rewrite Network_rm_out, H19; auto; discriminate.
  rewrite H23, H19 in H22. apply (Recv_neq_cont _ _ _ H22).
Qed.

(** The label alone determines the resulting state. *)

Lemma SP_To_rl_implies_state : forall N1 s tl N1' s1 N2 N2' s2,
  SP_To Defs N1 s tl N1' s1 -> SP_To Defs N2 s tl N2' s2 ->
  eq_state_ext s1 s2.
Proof.
induction tl; intros; inversion H; inversion H0;
  try (ESEt s; ESEs; fail).
ESEt (update s q x v1). ESEs. ESEt (update s q x v2).
rewrite H14, H2; ESEr.
Qed.

(** ** Confluence *)

Lemma diamond_SP : forall N s tl1 tl2 N1 N2 s1 s2,
  SP_To Defs N s tl1 N1 s1 -> SP_To Defs N s tl2 N2 s2 ->
  tl1 <> tl2 -> exists N' s', SP_To Defs N1 s1 tl2 N' s' /\ SP_To Defs N2 s2 tl1 N' s'.
Proof.
induction tl1, tl2; intros; inversion H; inversion H0.
+ (* Com / Com *)
  revert H3 H15 H13 H25; unfold v2, v3; intros.
  clear s'0 H22 N'0 H21 x2 H17 q2 H16 v3 p2 H14 s3 H19 N3 H18.
  clear s' H10 N' H9 x1 H5 q1 H4 v2 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H20 H8.
  1: {
    rewrite <- H4, H23 in H11; inversion H11.
    apply H1. rewrite <- H3, <- H15, Hpp0, H4, H5, H9; auto.
  }
  diff_assert q q0 Hqq0 H23 H11.
  1: {
    rewrite <- H4, H20 in H8; inversion H8.
    apply H1. rewrite <- H3, <- H15, Hqq0, H4, H5, H9; auto.
  }
  diff_assert p q0 Hpq0 H23 H8.
  diff_assert p0 q Hp0q H11 H20.
  diff_assert p q Hpq H11 H8.
  diff_assert p0 q0 Hp0q0 H23 H20.
  assert (eval_on_state e s p = eval_on_state e s2 p); intros.
  1: {
    unfold eval_on_state, EvSt.eval_on_state. apply Ev.eval_wd.
    intro; rewrite H25, update_read'; auto.
  }
  assert (eval_on_state e0 s p0 = eval_on_state e0 s1 p0).
  1: {
    unfold eval_on_state, EvSt.eval_on_state. apply Ev.eval_wd.
    intro; rewrite H13, update_read'; auto.
  }
  exists (Network_rm (Network_rm N1 p0) q0 | p0[B0] | q0[B'0]),
         (update s1 q0 x0 (eval_on_state e0 s1 p0)); split.
  - rewrite H4; apply S_Com'.
    * rewrite (H12 p0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H20; discriminate.
    * rewrite (H12 q0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H23; discriminate.
  - rewrite H2; apply S_Com with B B'.
    * rewrite (H24 p), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H8; discriminate.
    * rewrite (H24 q), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H11; discriminate.
    * apply Network_eq_cross with N; auto.
    * eESEt. ESEc; eauto. eESEt. apply update_independent; auto.
      rewrite H2. ESEs; ESEc. rewrite <- H4; auto.
+ (* Left / Com *)
  revert H3 H13; unfold v1; intros.
  clear s'0 H22 N'0 H21 q2 H15 p2 H14 s3 H19 N3 H18.
  clear s' H10 N' H9 x0 H5 q1 H4 v1 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H17 H8.
  diff_assert q q0 Hqq0 H20 H11.
  diff_assert p q0 Hpq0 H20 H8.
  diff_assert p0 q Hp0q H11 H17.
  diff_assert p q Hpq H11 H8.
  diff_assert p0 q0 Hp0q0 H20 H17.
  exists (Network_rm (Network_rm N1 p0) q0 | p0[B0] | q0[Bl]), s1; split.
  - apply S_LSel' with Br; auto.
    * rewrite (H12 p0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H17; discriminate.
    * rewrite (H12 q0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H20; discriminate.
  - rewrite (eval_eq e s s2); auto; apply S_Com with B B'.
    * rewrite (H23 p), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H8; discriminate.
    * rewrite (H23 q), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H11; discriminate.
    * apply Network_eq_cross with N; auto.
    * eESEt. rewrite (eval_eq e s s2); auto. ESEc; auto.
+ (* Right / Com *)
  revert H3 H13; unfold v1; intros.
  clear s'0 H22 N'0 H21 q2 H15 p2 H14 s3 H19 N3 H18.
  clear s' H10 N' H9 x0 H5 q1 H4 v1 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H17 H8.
  diff_assert q q0 Hqq0 H20 H11.
  diff_assert p q0 Hpq0 H20 H8.
  diff_assert p0 q Hp0q H11 H17.
  diff_assert p q Hpq H11 H8.
  diff_assert p0 q0 Hp0q0 H20 H17.
  exists (Network_rm (Network_rm N1 p0) q0 | p0[B0] | q0[Br]), s1; split.
  - apply S_RSel' with Bl; auto.
    * rewrite (H12 p0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H17; discriminate.
    * rewrite (H12 q0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H20; discriminate.
  - rewrite (eval_eq e s s2); auto; apply S_Com with B B'.
    * rewrite (H23 p), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H8; discriminate.
    * rewrite (H23 q), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H11; discriminate.
    * apply Network_eq_cross with N; auto.
    * eESEt. rewrite (eval_eq e s s2); auto. ESEc; auto.
+ (* Then / Com *)
  revert H3 H13; unfold v1; intros.
  clear s'0 H22 N'0 H21 p2 H14 s3 H19 N3 H18.
  clear s' H10 N' H9 x0 H5 q0 H4 v1 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H15 H8.
  diff_assert p0 q Hp0q H11 H15.
  diff_assert p q Hpq H11 H8.
  exists (Network_rm N1 p0 | p0[B1]), s1; split.
  - apply S_Then' with b B2.
    * rewrite (H12 p0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H15; discriminate.
    * rewrite (beval_eq b s1 (update s q x (eval_on_state e s p))); auto.
      rewrite <- beval_neq; auto.
  - rewrite (eval_eq e s s2); auto; apply S_Com with B B'.
    * rewrite (H17 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H8; discriminate.
    * rewrite (H17 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H11; discriminate.
    * symmetry. apply Network_eq_cross' with N; auto.
    * rewrite <- (eval_eq e s s2); auto. eESEt; ESEc; auto.
+ (* Else / Com *)
  revert H3 H13; unfold v1; intros.
  clear s'0 H22 N'0 H21 p2 H14 s3 H19 N3 H18.
  clear s' H10 N' H9 x0 H5 q0 H4 v1 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H15 H8.
  diff_assert p0 q Hp0q H11 H15.
  diff_assert p q Hpq H11 H8.
  exists (Network_rm N1 p0 | p0[B2]), s1; split.
  - apply S_Else' with b B1.
    * rewrite (H12 p0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H15; discriminate.
    * rewrite (beval_eq b s1 (update s q x (eval_on_state e s p))); auto.
      rewrite <- beval_neq; auto.
  - rewrite (eval_eq e s s2); auto; apply S_Com with B B'.
    * rewrite (H17 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H8; discriminate.
    * rewrite (H17 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H11; discriminate.
    * symmetry. apply Network_eq_cross' with N; auto.
    * rewrite <- (eval_eq e s s2); auto. eESEt; ESEc; auto.
+ (* Call / Com *)
  revert H3 H13; unfold v1; intros.
  clear s'0 H21 N'0 H20 p2 H15 X0 H14 s3 H18 N3 H17.
  clear s' H10 N' H9 x0 H5 q0 H4 v1 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H16 H8.
  diff_assert p0 q Hp0q H11 H16.
  diff_assert p q Hpq H11 H8.
  exists (Network_rm N1 p0 | p0[Defs X]), s1; split.
  - apply S_Call'.
    rewrite (H12 p0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
    rewrite H16; discriminate.
  - rewrite (eval_eq e s s2); auto; apply S_Com with B B'.
    * rewrite (H19 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H8; discriminate.
    * rewrite (H19 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H11; discriminate.
    * symmetry. apply Network_eq_cross' with N; auto.
    * rewrite <- (eval_eq e s s2); auto. eESEt; ESEc; auto.
+ (* Com / Left *)
  revert H15 H24; unfold v1; intros.
  clear s' H10 N' H9 q1 H3 p1 H2 s0 H7 N0 H6.
  clear s'0 H21 N'0 H20 x0 H16 q2 H15 v1 H14 p2 H13 s3 H18 N3 H17.
  diff_assert p p0 Hpp0 H19 H5.
  diff_assert q q0 Hqq0 H22 H8.
  diff_assert p q0 Hpq0 H22 H5.
  diff_assert p0 q Hp0q H8 H19.
  diff_assert p q Hpq H8 H5.
  diff_assert p0 q0 Hp0q0 H22 H19.
  exists (Network_rm (Network_rm N2 p) q | p[B] | q[Bl]), s2; split.
  - rewrite (eval_eq e s s1); auto; apply S_Com with B0 B'.
    * rewrite (H11 p0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H19; discriminate.
    * rewrite (H11 q0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H22; discriminate.
    * apply Network_eq_cross with N; auto.
    * eESEt. rewrite (eval_eq e s s1); auto. ESEc; auto.
  - apply S_LSel' with Br; auto.
    * rewrite (H23 p), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H5; discriminate.
    * rewrite (H23 q), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H8; discriminate.
+ (* Com / Right *)
  revert H15 H24; unfold v1; intros.
  clear s' H10 N' H9 q1 H3 p1 H2 s0 H7 N0 H6.
  clear s'0 H21 N'0 H20 x0 H16 q2 H15 v1 H14 p2 H13 s3 H18 N3 H17.
  diff_assert p p0 Hpp0 H19 H5.
  diff_assert q q0 Hqq0 H22 H8.
  diff_assert p q0 Hpq0 H22 H5.
  diff_assert p0 q Hp0q H8 H19.
  diff_assert p q Hpq H8 H5.
  diff_assert p0 q0 Hp0q0 H22 H19.
  exists (Network_rm (Network_rm N2 p) q | p[B] | q[Br]), s2; split.
  - rewrite (eval_eq e s s1); auto; apply S_Com with B0 B'.
    * rewrite (H11 p0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H19; discriminate.
    * rewrite (H11 q0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H22; discriminate.
    * apply Network_eq_cross with N; auto.
    * eESEt. rewrite (eval_eq e s s1); auto. ESEc; auto.
  - apply S_RSel' with Bl; auto.
    * rewrite (H23 p), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H5; discriminate.
    * rewrite (H23 q), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H8; discriminate.
+ (* Left / Left *)
  clear s'0 H21 N'0 H20 q2 H14 p2 H13 s3 H18 N3 H17.
  clear s' H10 N' H9 q1 H3 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H16 H5.
  1: { apply H1. rewrite Hpp0, <- H15, H4, H3; auto. }
  diff_assert q q0 Hqq0 H19 H8. eauto.
  diff_assert p q0 Hpq0 H19 H5.
  diff_assert p0 q Hp0q H8 H16.
  diff_assert p q Hpq H8 H5.
  diff_assert p0 q0 Hp0q0 H19 H16.
  exists (Network_rm (Network_rm N1 p0) q0 | p0[B0] | q0[Bl0]), s1; split.
  - apply S_LSel' with Br0; auto.
    * rewrite (H11 p0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H16; discriminate.
    * rewrite (H11 q0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H19; discriminate.
  - apply S_LSel with B Bl Br; auto.
    * rewrite (H22 p), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H5; discriminate.
    * rewrite (H22 q), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H8; discriminate.
    * apply Network_eq_cross with N; auto.
    * ESEt s; ESEs.
+ (* Right / Left *)
  clear s'0 H21 N'0 H20 q2 H14 p2 H13 s3 H18 N3 H17.
  clear s' H10 N' H9 q1 H3 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H16 H5.
  diff_assert q q0 Hqq0 H19 H8. eauto.
  diff_assert p q0 Hpq0 H19 H5.
  diff_assert p0 q Hp0q H8 H16.
  diff_assert p q Hpq H8 H5.
  diff_assert p0 q0 Hp0q0 H19 H16.
  exists (Network_rm (Network_rm N1 p0) q0 | p0[B0] | q0[Br0]), s1; split.
  - apply S_RSel' with Bl0; auto.
    * rewrite (H11 p0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H16; discriminate.
    * rewrite (H11 q0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H19; discriminate.
  - apply S_LSel with B Bl Br; auto.
    * rewrite (H22 p), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H5; discriminate.
    * rewrite (H22 q), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H8; discriminate.
    * apply Network_eq_cross with N; auto.
    * ESEt s; ESEs.
+ (* Left / Right *)
  clear s'0 H21 N'0 H20 q2 H14 p2 H13 s3 H18 N3 H17.
  clear s' H10 N' H9 q1 H3 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H16 H5.
  diff_assert q q0 Hqq0 H19 H8. eauto.
  diff_assert p q0 Hpq0 H19 H5.
  diff_assert p0 q Hp0q H8 H16.
  diff_assert p q Hpq H8 H5.
  diff_assert p0 q0 Hp0q0 H19 H16.
  exists (Network_rm (Network_rm N1 p0) q0 | p0[B0] | q0[Bl0]), s1; split.
  - apply S_LSel' with Br0; auto.
    * rewrite (H11 p0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H16; discriminate.
    * rewrite (H11 q0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H19; discriminate.
  - apply S_RSel with B Bl Br; auto.
    * rewrite (H22 p), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H5; discriminate.
    * rewrite (H22 q), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H8; discriminate.
    * apply Network_eq_cross with N; auto.
    * ESEt s; ESEs.
+ (* Right / Right *)
  clear s'0 H21 N'0 H20 q2 H14 p2 H13 s3 H18 N3 H17.
  clear s' H10 N' H9 q1 H3 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H16 H5.
  1: { apply H1. rewrite Hpp0, <- H15, H4, H3; auto. }
  diff_assert q q0 Hqq0 H19 H8. eauto.
  diff_assert p q0 Hpq0 H19 H5.
  diff_assert p0 q Hp0q H8 H16.
  diff_assert p q Hpq H8 H5.
  diff_assert p0 q0 Hp0q0 H19 H16.
  exists (Network_rm (Network_rm N1 p0) q0 | p0[B0] | q0[Br0]), s1; split.
  - apply S_RSel' with Bl0; auto.
    * rewrite (H11 p0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H16; discriminate.
    * rewrite (H11 q0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H19; discriminate.
  - apply S_RSel with B Bl Br; auto.
    * rewrite (H22 p), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H5; discriminate.
    * rewrite (H22 q), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H8; discriminate.
    * apply Network_eq_cross with N; auto.
    * ESEt s; ESEs.
+ (* Then / Left *)
  clear s'0 H21 N'0 H20 p2 H13 s3 H18 N3 H17.
  clear s' H10 N' H9 H4 q0 H3 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H14 H5.
  diff_assert p0 q Hp0q H8 H14.
  diff_assert p q Hpq H8 H5.
  exists (Network_rm N1 p0 | p0[B1]), s1; split.
  - apply S_Then' with b B2.
    * rewrite (H11 p0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H14; discriminate.
    * rewrite (beval_eq b s1 s); auto. ESEs.
  - apply S_LSel with B Bl Br; auto.
    * rewrite (H16 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H5; discriminate.
    * rewrite (H16 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H8; discriminate.
    * symmetry. apply Network_eq_cross' with N; auto.
    * eESEt; ESEs.
+ (* Else / Left *)
  clear s'0 H21 N'0 H20 p2 H13 s3 H18 N3 H17.
  clear s' H10 N' H9 H4 q0 H3 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H14 H5.
  diff_assert p0 q Hp0q H8 H14.
  diff_assert p q Hpq H8 H5.
  exists (Network_rm N1 p0 | p0[B2]), s1; split.
  - apply S_Else' with b B1.
    * rewrite (H11 p0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H14; discriminate.
    * rewrite (beval_eq b s1 s); auto. ESEs.
  - apply S_LSel with B Bl Br; auto.
    * rewrite (H16 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H5; discriminate.
    * rewrite (H16 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H8; discriminate.
    * symmetry. apply Network_eq_cross' with N; auto.
    * eESEt; ESEs.
+ (* Then / Right *)
  clear s'0 H21 N'0 H20 p2 H13 s3 H18 N3 H17.
  clear s' H10 N' H9 H4 q0 H3 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H14 H5.
  diff_assert p0 q Hp0q H8 H14.
  diff_assert p q Hpq H8 H5.
  exists (Network_rm N1 p0 | p0[B1]), s1; split.
  - apply S_Then' with b B2.
    * rewrite (H11 p0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H14; discriminate.
    * rewrite (beval_eq b s1 s); auto. ESEs.
  - apply S_RSel with B Bl Br; auto.
    * rewrite (H16 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H5; discriminate.
    * rewrite (H16 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H8; discriminate.
    * symmetry. apply Network_eq_cross' with N; auto.
    * eESEt; ESEs.
+ (* Else / Right *)
  clear s'0 H21 N'0 H20 p2 H13 s3 H18 N3 H17.
  clear s' H10 N' H9 H4 q0 H3 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H14 H5.
  diff_assert p0 q Hp0q H8 H14.
  diff_assert p q Hpq H8 H5.
  exists (Network_rm N1 p0 | p0[B2]), s1; split.
  - apply S_Else' with b B1.
    * rewrite (H11 p0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H14; discriminate.
    * rewrite (beval_eq b s1 s); auto. ESEs.
  - apply S_RSel with B Bl Br; auto.
    * rewrite (H16 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H5; discriminate.
    * rewrite (H16 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H8; discriminate.
    * symmetry. apply Network_eq_cross' with N; auto.
    * eESEt; ESEs.
+ (* Call / Left *)
  clear s'0 H20 N'0 H19 p2 H14 X0 H13 s3 H17 N3 H16.
  clear s' H10 N' H9 H4 q0 H3 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H15 H5.
  diff_assert p0 q Hp0q H8 H15.
  diff_assert p q Hpq H8 H5.
  exists (Network_rm N1 p0 | p0[Defs X]), s1; split.
  - apply S_Call'.
    rewrite (H11 p0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
    rewrite H15; discriminate.
  - apply S_LSel with B Bl Br; auto.
    * rewrite (H18 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H5; discriminate.
    * rewrite (H18 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H8; discriminate.
    * symmetry. apply Network_eq_cross' with N; auto.
    * eESEt; ESEs.
+ (* Call / Right *)
  clear s'0 H20 N'0 H19 p2 H14 X0 H13 s3 H17 N3 H16.
  clear s' H10 N' H9 H4 q0 H3 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H15 H5.
  diff_assert p0 q Hp0q H8 H15.
  diff_assert p q Hpq H8 H5.
  exists (Network_rm N1 p0 | p0[Defs X]), s1; split.
  - apply S_Call'.
    rewrite (H11 p0), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
    rewrite H15; discriminate.
  - apply S_RSel with B Bl Br; auto.
    * rewrite (H18 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H5; discriminate.
    * rewrite (H18 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H8; discriminate.
    * symmetry. apply Network_eq_cross' with N; auto.
    * eESEt; ESEs.
+ (* Com / Then *)
  revert H12 H22; unfold v1; intros.
  diff_assert p p0 Hpp0 H17 H3.
  diff_assert p0 q Hp0q H20 H17.
  diff_assert p q Hpq H20 H3.
  exists (Network_rm N2 p | p[B1]), s2; split.
  - rewrite (eval_eq e s s1); auto; apply S_Com with B B'.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H17; discriminate.
    * rewrite (H5 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H20; discriminate.
    * symmetry; apply Network_eq_cross' with N; auto.
    * rewrite <- (eval_eq e s s1); auto. eESEt; ESEc; auto.
  - apply S_Then' with b B2.
    * rewrite (H21 p), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H3; discriminate.
    * rewrite (beval_eq b s2 (update s q x (eval_on_state e s p0))); auto.
      rewrite <- beval_neq; auto.
+ (* Com / Else *)
  revert H12 H22; unfold v1; intros.
  diff_assert p p0 Hpp0 H17 H3.
  diff_assert p0 q Hp0q H20 H17.
  diff_assert p q Hpq H20 H3.
  exists (Network_rm N2 p | p[B2]), s2; split.
  - rewrite (eval_eq e s s1); auto; apply S_Com with B B'.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H17; discriminate.
    * rewrite (H5 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H20; discriminate.
    * symmetry; apply Network_eq_cross' with N; auto.
    * rewrite <- (eval_eq e s s1); auto. eESEt; ESEc; auto.
  - apply S_Else' with b B1.
    * rewrite (H21 p), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H3; discriminate.
    * rewrite (beval_eq b s2 (update s q x (eval_on_state e s p0))); auto.
      rewrite <- beval_neq; auto.
+ (* Left / Then *)
  diff_assert p p0 Hpp0 H14 H3.
  diff_assert p0 q Hp0q H17 H14.
  diff_assert p q Hpq H17 H3.
  exists (Network_rm N2 p | p[B1]), s2; split.
  - apply S_LSel with B Bl Br; auto.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H14; discriminate.
    * rewrite (H5 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H17; discriminate.
    * symmetry. apply Network_eq_cross' with N; auto.
    * eESEt; ESEs.
  - apply S_Then' with b B2.
    * rewrite (H20 p), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H3; discriminate.
    * rewrite (beval_eq b s2 s); auto. ESEs.
+ (* Right / Then *)
  diff_assert p p0 Hpp0 H14 H3.
  diff_assert p0 q Hp0q H17 H14.
  diff_assert p q Hpq H17 H3.
  exists (Network_rm N2 p | p[B1]), s2; split.
  - apply S_RSel with B Bl Br; auto.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H14; discriminate.
    * rewrite (H5 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H17; discriminate.
    * symmetry. apply Network_eq_cross' with N; auto.
    * eESEt; ESEs.
  - apply S_Then' with b B2.
    * rewrite (H20 p), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H3; discriminate.
    * rewrite (beval_eq b s2 s); auto. ESEs.
+ (* Left / Else *)
  diff_assert p p0 Hpp0 H14 H3.
  diff_assert p0 q Hp0q H17 H14.
  diff_assert p q Hpq H17 H3.
  exists (Network_rm N2 p | p[B2]), s2; split.
  - apply S_LSel with B Bl Br; auto.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H14; discriminate.
    * rewrite (H5 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H17; discriminate.
    * symmetry. apply Network_eq_cross' with N; auto.
    * eESEt; ESEs.
  - apply S_Else' with b B1.
    * rewrite (H20 p), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H3; discriminate.
    * rewrite (beval_eq b s2 s); auto. ESEs.
+ (* Right / Else *)
  diff_assert p p0 Hpp0 H14 H3.
  diff_assert p0 q Hp0q H17 H14.
  diff_assert p q Hpq H17 H3.
  exists (Network_rm N2 p | p[B2]), s2; split.
  - apply S_RSel with B Bl Br; auto.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H14; discriminate.
    * rewrite (H5 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H17; discriminate.
    * symmetry. apply Network_eq_cross' with N; auto.
    * eESEt; ESEs.
  - apply S_Else' with b B1.
    * rewrite (H20 p), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H3; discriminate.
    * rewrite (beval_eq b s2 s); auto. ESEs.
+ (* Then / Then *)
  assert (p <> p0) as Hpp0. intro Hpp0; elim H1; rewrite Hpp0; auto.
  exists (Network_rm N1 p0 | p0[B0]), s1; split.
  - apply S_Then' with b0 B3; auto.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H12; discriminate.
    * rewrite (beval_eq b0 s1 s); auto. ESEs.
  - apply S_Then with b B1 B2; auto.
    * rewrite (H14 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H3; discriminate.
    * rewrite (beval_eq b s2 s); auto. ESEs.
    * apply Network_eq_cross'' with N; auto.
    * eESEt; ESEs.
+ (* Else / Then *)
  assert (p <> p0) as Hpp0. intro Hpp0; elim H1; rewrite Hpp0; auto.
  exists (Network_rm N1 p0 | p0[B3]), s1; split.
  - apply S_Else' with b0 B0; auto.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H12; discriminate.
    * rewrite (beval_eq b0 s1 s); auto. ESEs.
  - apply S_Then with b B1 B2; auto.
    * rewrite (H14 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H3; discriminate.
    * rewrite (beval_eq b s2 s); auto. ESEs.
    * apply Network_eq_cross'' with N; auto.
    * eESEt; ESEs.
+ (* Then / Else *)
  assert (p <> p0) as Hpp0. intro Hpp0; elim H1; rewrite Hpp0; auto.
  exists (Network_rm N1 p0 | p0[B0]), s1; split.
  - apply S_Then' with b0 B3; auto.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H12; discriminate.
    * rewrite (beval_eq b0 s1 s); auto. ESEs.
  - apply S_Else with b B1 B2; auto.
    * rewrite (H14 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H3; discriminate.
    * rewrite (beval_eq b s2 s); auto. ESEs.
    * apply Network_eq_cross'' with N; auto.
    * eESEt; ESEs.
+ (* Else / Else *)
  assert (p <> p0) as Hpp0. intro Hpp0; elim H1; rewrite Hpp0; auto.
  exists (Network_rm N1 p0 | p0[B3]), s1; split.
  - apply S_Else' with b0 B0; auto.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H12; discriminate.
    * rewrite (beval_eq b0 s1 s); auto. ESEs.
  - apply S_Else with b B1 B2; auto.
    * rewrite (H14 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H3; discriminate.
    * rewrite (beval_eq b s2 s); auto. ESEs.
    * apply Network_eq_cross'' with N; auto.
    * eESEt; ESEs.
+ (* Call / Then *)
  diff_assert p p0 Hpp0 H13 H3.
  exists (Network_rm N1 p0 | p0[Defs X]), s1; split.
  - apply S_Call'; auto.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H13; discriminate.
  - apply S_Then with b B1 B2; auto.
    * rewrite (H16 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H3; discriminate.
    * rewrite (beval_eq b s2 s); auto. ESEs.
    * apply Network_eq_cross'' with N; auto.
    * eESEt; ESEs.
+ (* Call / Else *)
  diff_assert p p0 Hpp0 H13 H3.
  exists (Network_rm N1 p0 | p0[Defs X]), s1; split.
  - apply S_Call'; auto.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H13; discriminate.
  - apply S_Else with b B1 B2; auto.
    * rewrite (H16 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H3; discriminate.
    * rewrite (beval_eq b s2 s); auto. ESEs.
    * apply Network_eq_cross'' with N; auto.
    * eESEt; ESEs.
+ (* Com / Call *)
  revert H12 H22; unfold v1; intros.
  diff_assert p p0 Hpp0 H17 H4.
  diff_assert p q Hpq H20 H4.
  diff_assert p0 q Hp0q H20 H17.
  exists (Network_rm N2 p | p[Defs X]), s2; split.
  - rewrite (eval_eq e s s1); auto; apply S_Com with B B'.
    * rewrite (H7 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H17; discriminate.
    * rewrite (H7 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H20; discriminate.
    * symmetry; apply Network_eq_cross' with N; auto.
    * rewrite <- (eval_eq e s s1); auto. eESEt; ESEc; auto.
  - apply S_Call'.
    * rewrite (H21 p), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H4; discriminate.
+ (* Left / Call *)
  diff_assert p p0 Hpp0 H14 H4.
  diff_assert p q Hpq H17 H4.
  diff_assert p0 q Hp0q H17 H14.
  exists (Network_rm N2 p | p[Defs X]), s2; split.
  - apply S_LSel with B Bl Br; auto.
    * rewrite (H7 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H14; discriminate.
    * rewrite (H7 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H17; discriminate.
    * symmetry; apply Network_eq_cross' with N; auto.
    * eESEt; ESEs; auto.
  - apply S_Call'.
    * rewrite (H20 p), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H4; discriminate.
+ (* Right / Call *)
  diff_assert p p0 Hpp0 H14 H4.
  diff_assert p q Hpq H17 H4.
  diff_assert p0 q Hp0q H17 H14.
  exists (Network_rm N2 p | p[Defs X]), s2; split.
  - apply S_RSel with B Bl Br; auto.
    * rewrite (H7 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H14; discriminate.
    * rewrite (H7 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H17; discriminate.
    * symmetry; apply Network_eq_cross' with N; auto.
    * eESEt; ESEs; auto.
  - apply S_Call'.
    * rewrite (H20 p), Par_proj1; rewrite Network_rm_out, Network_rm_out; auto.
      rewrite H4; discriminate.
+ (* Then / Call *)
  diff_assert p p0 Hpp0 H12 H4.
  exists (Network_rm N2 p | p[Defs X]), s2; split.
  - apply S_Then with b B1 B2; auto.
    * rewrite (H7 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H12; discriminate.
    * rewrite (beval_eq b s1 s); auto. ESEs.
    * apply Network_eq_cross'' with N; auto.
    * eESEt; ESEs.
  - apply S_Call'; auto.
    * rewrite (H14 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H4; discriminate.
+ (* Else / Call *)
  diff_assert p p0 Hpp0 H12 H4.
  exists (Network_rm N2 p | p[Defs X]), s2; split.
  - apply S_Else with b B1 B2; auto.
    * rewrite (H7 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H12; discriminate.
    * rewrite (beval_eq b s1 s); auto. ESEs.
    * apply Network_eq_cross'' with N; auto.
    * eESEt; ESEs.
  - apply S_Call'; auto.
    * rewrite (H14 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H4; discriminate.
+ (* Call / Call *)
  assert (p <> p0) as Hpp0. intro Hpp0.
  elim (R.eq_dec X X0); intro.
  1: apply H1; rewrite Hpp0, a; auto.
  apply b. rewrite <- Hpp0, H4 in H13; inversion H13; auto.
  exists (Network_rm N1 p0 | p0[Defs X0]), s1; split.
  - apply S_Call'; auto.
    rewrite (H7 p0), Par_proj1; rewrite Network_rm_out; auto.
    rewrite H13; discriminate.
  - apply S_Call; auto.
    * rewrite (H16 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H4; discriminate.
    * apply Network_eq_cross'' with N; auto.
    * eESEt; ESEs.
Qed.

End Determinism.

End SPBase.

(* The remaining is stuff from CC that it would be interesting to adapt.

Lemma MCC_To_Program_WF : forall P s l P' s' Xs,
  Program_WF Xs P -> (P,s) --[l]--> (P',s') -> Program_WF Xs P'.
Proof.
intros.
generalize (MCC_To_within_Xs _ _ _ _ _ Xs H H0); intro HXs.
inversion H0; auto.
rewrite <- H1 in H; rewrite <- H5 in HXs.
clear s'0 H6 s0 H3 H5 H0 P' H1 P H2 l.
apply Program_WF_Main_change with C; auto.
clear HXs.
generalize (Program_WF_Main _ _ H); simpl; intro HC.
induction H4.
+ eapply Choreography_WF_eta; eauto.
+ eapply Choreography_WF_eta; eauto.
+ eapply Choreography_WF_Then; eauto.
+ eapply Choreography_WF_Else; eauto.
+ inversion_clear HC.
  inversion_clear H1; simpl in H2.
  destroy H.
  elim IHMCC_To; repeat (split; auto).
+ inversion_clear HC.
  inversion_clear H1; inversion_clear H2.
  assert (Choreography_WF C1). split; auto.
  assert (Choreography_WF C2). split; auto.
  generalize (Program_WF_Then _ _ _ _ _ _ H); intro.
  generalize (Program_WF_Else _ _ _ _ _ _ H); intro.
  elim IHMCC_To1; auto; elim IHMCC_To2; auto; intros.
  split; split; auto.
+ assert (Choreography_WF C).
  1: { inversion_clear HC. simpl in H1; inversion_clear H2; split; auto. }
  assert (within_Xs Xs C).
  1: { elim (Program_WF_Main_within_Xs _ _ H); auto. }
  generalize (Program_WF_Main_change _ _ _ _ H1 H2 H); intro.
  assert (Choreography_WF C'); auto; clear IHMCC_To.
  inversion_clear H5. repeat split; simpl; auto.
  inversion_clear HC. inversion_clear H8; auto.
+ change (Choreography_WF (Procs (Build_Program Defs (Call X)) X)).
  apply Program_WF_Proc with Xs; auto.
  apply (Program_WF_Vars_In _ _ H). red; simpl; auto.
+ elim (Program_WF_Proc _ _ H X); intros.
  2: apply (Program_WF_Vars_In _ _ H); red; simpl; auto.
  split; simpl; auto.
  split; auto.
  revert H1; case (fst (Defs X)); intros.
  1: exfalso; inversion H1.
  intro.
  unfold set_size_pid in H1.
  rewrite (set_size_remove' P.eq_dec) with (p0::l) p in H1; auto.
  - unfold set_remove_pid in H5; rewrite H5 in H1.
    elim (lt_irrefl _ H1).
  - revert H5; simpl. elim P.eq_dec; auto.
    intros. inversion H5.
+ elim (Program_WF_Proc _ _ H X); intros.
  2: {
    apply (Program_WF_Vars_In _ _ H); red; simpl.
    apply set_union_intro1; simpl; auto.
  }
  inversion_clear HC.
  simpl in H4, H5.
  split; simpl; auto.
  inversion_clear H6; split; auto.
  unfold set_size_pid in H1.
  rewrite (set_size_remove' P.eq_dec) with ps p in H1; auto.
  unfold set_remove_pid; intro. rewrite H6 in H1.
  elim (lt_irrefl _ H1).
+ elim HC; intros.
  inversion_clear H4; red; auto.
Qed.

Lemma MCT_Trans : forall c tl c' tl' c'',
  c --[tl]-->* c' -> c' --[tl']-->* c'' -> c --[tl++tl']-->* c''.
Proof.
intros c tl; revert c.
induction tl; simpl; intros; inversion H; auto.
simpl. apply MCT_Step with c2; auto.
apply IHtl with c'; auto.
Qed.

End BigStepSemantics.

Section Confluence.

Lemma diamond_Chor : forall Defs C s tl1 tl2 C1 C2 s1 s2,
  MCC_To Defs C s tl1 C1 s1 -> MCC_To Defs C s tl2 C2 s2 ->
  tl1 <> tl2 -> exists C' s', MCC_To Defs C1 s1 tl2 C' s' /\ MCC_To Defs C2 s2 tl1 C' s'.
Proof.
induction C; intros s tl' tl'' C' C'' s' s'' HC' HC'' Htl; intros.
+ (* End *)
  inversion HC'.
+ (* Call *)
  inversion HC'; inversion HC''; auto.
  - exfalso.
    rewrite <- H4, <- H12 in Htl.
    rewrite (set_size_1 _ _ H9 p p0) in Htl; auto.
  - exfalso. rewrite H1 in H9; apply (lt_irrefl _ H9).
  - exfalso. rewrite H9 in H1; apply (lt_irrefl _ H1).
  - case (P.eq_dec p p0); intro Hpp0.
    1: { exfalso. rewrite <- H12, <- H4, Hpp0 in Htl; auto. }
    clear HC' HC'' Htl s'1 H14 C'' H13 tl'' H12 s1 H11 X0 H7.
    clear s'0 H6 C' H5 tl' H4 s0 H3 X H.
    rename r into X.
    elim (Nat.eq_dec (set_size_pid (fst (Defs X))) 2); intro HX.
    * exists (snd (Defs X)), s.
      split; apply C_Call_Finish; try ESEs.
      ++ revert HX.
         unfold set_size_pid, set_remove_pid.
         intro; rewrite (set_size_remove' P.eq_dec) with (fst (Defs X)) p in HX; auto.
      ++ apply set_remove'_3; auto.
      ++ revert HX.
         unfold set_size_pid, set_remove_pid.
         intro; rewrite (set_size_remove' P.eq_dec) with (fst (Defs X)) p0 in HX; auto.
      ++ apply set_remove'_3; auto.
    * exists (RT_Call X (set_remove_pid p (set_remove_pid p0 (fst (Defs X)))) (snd (Defs X))), s.
      unfold set_remove_pid.
      rewrite set_remove'_remove' at 1.
      split; (apply C_Call_Enter; try ESEs;
        [eapply set_size_neq_2; eauto | apply set_remove'_3; auto]).
+ (* RT_Call *)
  inversion HC'; inversion HC''; auto.
  6: { exfalso. rewrite H17 in H7. apply (lt_irrefl _ H7). }
  7: { exfalso. rewrite H7 in H17. apply (lt_irrefl _ H17). }
  7: { exfalso. rewrite <- H14, <- H4, (set_size_1 _ _ H17 p p0) in Htl; auto. }
  - elim (IHC _ _ _ _  _ _ _ H7 H16); auto; intros.
    inversion_clear H17; inversion_clear H18.
    do 2 eexists; split; apply C_Delay_Call; eauto.
  - exists (RT_Call r (set_remove_pid p l) C'0), s'; split.
    * apply C_Call_Enter'; auto.
    * apply C_Delay_Call; auto.
      apply disjoint_ps_remove; auto. 
      apply MCC_To_eq with s s'; auto. ESEr.
  - exists C'0, s'; split.
    * apply C_Call_Finish'; auto.
    * apply MCC_To_eq with s s'; auto. ESEr. rewrite <- H14; auto.
  - exists (RT_Call r (set_remove_pid p l) C'0), s''; split.
    * apply C_Delay_Call; auto.
      apply disjoint_ps_remove; auto. 
      apply MCC_To_eq with s s''; auto. ESEr.
    * apply C_Call_Enter'; auto.
  - case (P.eq_dec p p0); intro Hpp0.
    1: { exfalso. rewrite <- H14, <- H4, Hpp0 in Htl; auto. }
    clear HC' HC'' Htl s'1 H16 C'' H15 tl'' H14 s1 H13 C1 H11 ps0 H10.
    clear X0 H9 s'0 H6 C' H5 tl' H4 C0 H1 ps H0 X H IHC.
    rename l into ps, r into X.
    elim (Nat.eq_dec (set_size_pid ps) 2); intro HX.
    * exists C, s.
      split; apply C_Call_Finish; try ESEs.
      -- revert HX.
         unfold set_size_pid, set_remove_pid.
         intro; rewrite (set_size_remove' P.eq_dec) with ps p in HX; auto.
      -- apply set_remove'_3; auto.
      -- revert HX.
         unfold set_size_pid, set_remove_pid.
         intro; rewrite (set_size_remove' P.eq_dec) with ps p0 in HX; auto.
      -- apply set_remove'_3; auto.
    * exists (RT_Call X (set_remove_pid p (set_remove_pid p0 ps)) C), s.
      unfold set_remove_pid.
      rewrite set_remove'_remove' at 1.
      split; (apply C_Call_Enter; try ESEs;
       [eapply set_size_neq_2; eauto | apply set_remove'_3; auto]).
  - exists C'0, s''; split.
    * apply MCC_To_eq with s s''; auto. ESEr. rewrite <- H5; auto.
    * apply C_Call_Finish'; auto.
+ (* Eta *)
  inversion HC'; inversion HC''; try (rewrite <- H in H6; inversion H6).
  - elim Htl. unfold v, v0 in H9, H2. rewrite <- H9, <- H2, H14, H15, H16, H17; auto.
  - clear HC' HC'' Htl s'1 H12 C'' H11 t H10 s1 H9 C1 H7 eta H6 H14.
    rewrite <- H3.
    clear s'0 H4 C' H3 C0 H1 s0 H0 tl' H2.
    rename C'0 into C'.
    generalize (C_Com' Defs p e0 q x C' s''); rewrite H; intro.
    rewrite <- H in H8; inversion_clear H8.
    exists C', (update s'' q x v); split.
    * apply MCC_To_eq with (update s q x v) (update s'' q x v). ESEs. ESEr.
      apply MCC_To_disjoint_update; auto.
    * unfold v.
      rewrite (MCC_To_disjoint_eval _ _ _ _ _ _ _ _ H1 H13); auto.
  - elim Htl. rewrite <- H9, <- H2, H14, H15, H16; auto.
  - rewrite <- H3.
    generalize (C_Sel' Defs p q l C'0 s''); rewrite H; intro.
    rewrite <- H in H8; inversion_clear H8.
    exists C'0, s''; split; auto.
    apply MCC_To_eq with s s''; auto. ESEr.
  - rewrite <- H11.
    generalize (C_Com' Defs p e0 q x C'0 s'); rewrite H7; intro.
    rewrite <- H7 in H1; inversion_clear H1.
    exists C'0, (update s' q x v); split.
    * unfold v.
      rewrite (MCC_To_disjoint_eval _ _ _ _ _ _ _ _ H15 H6); auto.
    * apply MCC_To_eq with (update s q x v) (update s' q x v). ESEs. ESEr.
      apply MCC_To_disjoint_update; auto.
  - rewrite <- H11.
    generalize (C_Sel' Defs p q l C'0 s'); rewrite H7; intro.
    rewrite <- H7 in H1; inversion_clear H1.
    exists C'0, s'; split; auto.
    apply MCC_To_eq with s s'; auto. ESEr.
  - elim (IHC _ _ _ _ _ _ _ H6 H14); intros; auto.
    inversion_clear H15. inversion_clear H16.
    do 2 eexists; split; apply C_Delay_Eta; eauto.
+ (* Cond *)
  inversion HC'; inversion HC''; try (rewrite H8 in H18; inversion H18).
  - elim Htl. rewrite <- H14, <- H4; auto.
  - rewrite <- H5.
    exists C1', s''; split; auto.
    * apply MCC_To_eq with s s''; auto. ESEr.
    * apply C_Then'.
      rewrite <- (MCC_To_disjoint_beval Defs C1 s tl'' s'' p b C1'); auto.
  - elim Htl. rewrite <- H14, <- H4; auto.
  - rewrite <- H5.
    exists C2', s''; split; auto.
    * apply MCC_To_eq with s s''; auto. ESEr.
    * apply C_Else'.
      rewrite <- (MCC_To_disjoint_beval Defs C1 s tl'' s'' p b C1'); auto.
  - rewrite <- H16.
    exists C1', s'; split; auto.
    * apply C_Then'.
      rewrite <- (MCC_To_disjoint_beval Defs C1 s tl' s' p b C1'); auto.
    * apply MCC_To_eq with s s'; auto. ESEr.
  - rewrite <- H16.
    exists C2', s'; split; auto.
    * apply C_Else'.
      rewrite <- (MCC_To_disjoint_beval Defs C1 s tl' s' p b C1'); auto.
    * apply MCC_To_eq with s s'; auto. ESEr.
  - clear HC' HC'' s'1 H17 C'' H16 t0 H15 s1 H13 C5 H14 b1 H11 p1 H10.
    clear s'0 H6 C' H5 t H4 s0 H2 C3 H3 C0 H1 b0 H0 p0 H C4 H12.
    elim (IHC1 _ _ _ _ _ _ _ H8 H19); elim (IHC2 _ _ _ _ _ _ _ H9 H20); auto.
    intros; clear IHC1 IHC2.
    rename C1' into C1a, C1'0 into C1b, x0 into C1'.
    rename C2' into C2a, C2'0 into C2b, x into C2'.
    elim H; clear H; intros s1 Hs1; inversion_clear Hs1.
    elim H0; clear H0; intros s2 Hs2; inversion_clear Hs2.
    pose (MCC_To_rl_implies_state _ _ _ _ _ _ _ _ _ H H0) as Hrl.
    clearbody Hrl.
    exists (If p ? b Then C1' Else C2'), s1; split; apply C_Delay_Cond; auto.
    * apply MCC_To_eq with s' s2; auto. ESEr. ESEs.
    * apply MCC_To_eq with s'' s2; auto. ESEr. ESEs.
Qed.

Lemma diamond_1 : forall c tl1 tl2 c1 c2,
  c --[ tl1 ]--> c1 -> c --[ tl2 ]--> c2 ->
  tl1 <> tl2 -> exists c', c1 --[ tl2 ]--> c' /\ c2 --[ tl1 ]--> c'.
Proof.
induction c. induction a.
rename Procedures0 into Defs, Main0 into C, b into s.
intros.
inversion H; inversion H0.
elim (diamond_Chor _ _ _ _ _ _ _ _ _ H7 H13); intros.
2: { intro; apply H1. rewrite <- H9, <- H3, H14. auto. }
inversion_clear H14. inversion_clear H15.
exists (Build_Program Defs x,x0); split; constructor; auto.
Qed.

Lemma diamond_2 : forall c tl1 tl2 c1 c2,
  c --[ tl1 ]--> c1 -> c --[ tl2 ]--> c2 ->
  {fst c1 = fst c2 /\ eq_state_ext (snd c1) (snd c2)}
  + {exists c', c1 --[ tl2 ]--> c' /\ c2 --[ tl1 ]--> c'}.
Proof.
induction c, c1, c2. induction a, p, p0.
rename Procedures1 into Defs', Main1 into C', s into s'.
rename Procedures2 into Defs'', Main2 into C'', s0 into s''.
rename Procedures0 into Defs, Main0 into C, b into s.
intros.
elim (chor_eq_dec C' C''); intro HC'C''; [left | right].
+ inversion H; inversion H0.
  clear H H0 s'1 H16 C'1 H15 tl2 H10 s1 H12 C1 H11 Defs1 H9 s'0 H8.
  clear C'0 H7 tl1 H2 s0 H4 C0 H3 Defs0 H1.
  revert H5 H13; rewrite <- H6, <- H14, <- HC'C''; clear H6 H14 HC'C'' Defs' Defs'' C''.
  intros HC HC'.
  split; auto.
  eapply MCC_To_deterministic_4; eauto.
+ inversion H; inversion H0.
  elim (RichLabel_eq_dec t t0); intro.
  1: {
    elim HC'C''.
    rewrite <- a, <- H14 in H13. rewrite <- H6 in H5.
    eapply MCC_To_deterministic_1; eauto.
  }
  rewrite <- H6 in H5; rewrite <- H14 in H13.
  elim (diamond_Chor _ _ _ _ _ _ _ _ _ H5 H13); intros; auto.
  inversion_clear H17. inversion_clear H18.
  rewrite <- H6, <- H14.
  exists (Build_Program Defs x,x0); split; constructor; auto.
Qed.

(** In this one we unfold the configuration because of the equivalence.
  Furthermore, we use logical disjunction - the labels are too weak... *)
Lemma diamond_3a : forall P s tl1 tl2 P1 s1 P2 s2,
  (P,s) --[ tl1 ]-->* (P1,s1) -> (P,s) --[ tl2 ]--> (P2,s2) ->
  (exists tl' s1', (P2,s2) --[ tl' ]-->* (P1,s1') /\ eq_state_ext s1 s1' /\ length tl1 = S (length tl'))
  \/ (exists P' s', (P1,s1) --[ tl2 ]--> (P',s') /\ (P2,s2) --[ tl1 ]-->* (P',s')).
Proof.
induction P, P1, P2.
rename Procedures1 into Defs', Main1 into C1.
rename Procedures2 into Defs'', Main2 into C2.
rename Procedures0 into Defs, Main0 into C.
intros.
rewrite <- (MCP_To_Defs_stable _ _ _ _ _ _ _ H0);
rewrite <- (MCP_To_Defs_stable _ _ _ _ _ _ _ H0) in H0.
rewrite <- (MCP_ToStar_Defs_stable _ _ _ _ _ _ _ H);
rewrite <- (MCP_ToStar_Defs_stable _ _ _ _ _ _ _ H) in H.
clear Defs' Defs''.
revert C s tl2 C1 s1 C2 s2 H H0; induction tl1.
+ right.
  inversion H.
  rewrite <- H2, <- H4. do 2 eexists; split; eauto. constructor.
+ intros.
  inversion H; clear H.
  clear t l H1 H2 c1 c3 H3 H5.
  induction c2, a0.
  rewrite <- (MCP_To_Defs_stable _ _ _ _ _ _ _ H4) in H6, H4; clear Procedures0.
  elim (diamond_2 _ _ _ _ _ H0 H4); simpl; intros.
  - inversion_clear a0. inversion H.
    rewrite <- H3 in H, H4, H6; rewrite <- H3; clear H3 Main0.
    left; exists tl1. case_eq tl1; intros.
    * rewrite H2 in H6. inversion H6. exists s2; split. constructor.
      split. rewrite <- H8; ESEs. auto.
    * rewrite <- H2. exists s1; split. 2: split; auto; ESEr.
      apply MCP_ToStar_eq with b s1; auto. ESEs. ESEr. rewrite H2; discriminate.
  - inversion_clear b0.
    induction x, a0; inversion_clear H.
    rewrite <- (MCP_To_Defs_stable _ _ _ _ _ _ _ H2) in H1, H2; clear Procedures0.
    rename Main1 into C', Main0 into C0.
    elim (IHtl1 _ _ _ _ _ _ _ H6 H2); intro.
    * destroy H.
      rename x into tl', x0 into s'.
      left; exists (a::tl'), s'; split; auto.
      apply MCT_Step with (Build_Program Defs C',b0); auto.
    * destroy H.
      right; exists x, x0; split; auto.
      apply MCT_Step with (Build_Program Defs C',b0); auto.
Qed.

Lemma diamond_3 : forall P s tl1 tl2 P1 s1 P2 s2,
  (P,s) --[ tl1 ]-->* (P1,s1) -> (P,s) --[ tl2 ]--> (P2,s2) ->
  (exists tl' s1', (P2,s2) --[ tl' ]-->* (P1,s1') /\ eq_state_ext s1 s1')
  \/ (exists P' s', (P1,s1) --[ tl2 ]--> (P',s') /\ (P2,s2) --[ tl1 ]-->* (P',s')).
Proof.
intros.
elim (diamond_3a _ _ _ _ _ _ _ _ H H0); intros; auto.
destroy H1; eauto.
Qed.

Lemma diamond_4a : forall P s tl1 tl2 P1 s1 P2 s2,
  (P,s) --[ tl1 ]-->* (P1,s1) -> (P,s) --[ tl2 ]-->* (P2,s2) ->
  (exists P' tl1' tl2' s1' s2',
    (P1,s1) --[ tl1' ]-->* (P',s1') /\ (P2,s2) --[ tl2' ]-->* (P',s2')
    /\ eq_state_ext s1' s2' /\ length tl1 + length tl1' = length tl2 + length tl2').
Proof.
induction P, P1, P2.
rename Procedures1 into Defs', Main1 into C1.
rename Procedures2 into Defs'', Main2 into C2.
rename Procedures0 into Defs, Main0 into C.
intros.
rewrite <- (MCP_ToStar_Defs_stable _ _ _ _ _ _ _ H0);
rewrite <- (MCP_ToStar_Defs_stable _ _ _ _ _ _ _ H0) in H0.
rewrite <- (MCP_ToStar_Defs_stable _ _ _ _ _ _ _ H);
rewrite <- (MCP_ToStar_Defs_stable _ _ _ _ _ _ _ H) in H.
clear Defs' Defs''.
revert C s tl1 C1 s1 C2 s2 H H0; induction tl2.
+ intros.
  inversion H0.
  rewrite <- H2, <- H4.
  exists (Build_Program Defs C1), nil, tl1, s1, s1; repeat split; auto.
  constructor.
+ intros.
  inversion H0; clear H0.
  clear t l H1 H2 c1 c3 H3 H5.
  induction c2, a0.
  rewrite <- (MCP_To_Defs_stable _ _ _ _ _ _ _ H4) in H6, H4; clear Procedures0.
  elim (diamond_3a _ _ _ _ _ _ _ _ H H4); intros.
  - destroy H0.
    rename x into tl', x0 into s', Main0 into C0.
    elim (IHtl2 _ _ _ _ _ _ _ H1 H6); intros.
    destroy H3.
    induction x.
    rewrite <- (MCP_ToStar_Defs_stable _ _ _ _ _ _ _ H5) in H7, H5; clear Procedures0.
    rename Main0 into C', x0 into tl1', x1 into tl2', x2 into s1', x3 into s2'.
    case_eq tl1'; intros.
    * rewrite H9 in H5. inversion H5.
      rewrite <- H11; rewrite <- H11 in H5, H7; rewrite H9 in H3; clear C' tl1' H11 H9.
      rewrite <- H13 in H5, H8. clear s1' H13 c H10.
      exists (Build_Program Defs C1), nil, tl2', s1, s2'; repeat split; auto.
      constructor. ESEt s'. simpl. rewrite <- H3, H0. auto.
    * exists (Build_Program Defs C'), tl1', tl2', s1', s2'; repeat split; auto.
      apply MCP_ToStar_eq with s' s1'; auto. ESEs. ESEr. rewrite H9; discriminate.
      simpl. rewrite <- H3, H0; auto.
  - destroy H0.
    induction x.
    rewrite <- (MCP_ToStar_Defs_stable _ _ _ _ _ _ _ H0) in H1, H0; clear Procedures0.
    rename Main1 into C', x0 into s', Main0 into C0.
    elim (IHtl2 _ _ _ _ _ _ _ H0 H6); intros.
    destroy H2.
    induction x.
    rewrite <- (MCP_ToStar_Defs_stable _ _ _ _ _ _ _ H3) in H5, H3; clear Procedures0.
    rename Main0 into C'', x0 into tl1'', x1 into tl2'', x2 into s1'', x3 into s2''.
    exists (Build_Program Defs C''), (a::tl1''), tl2'', s1'', s2''; repeat split; auto.
    apply MCT_Step with (Build_Program Defs C',s'); auto.
    simpl. rewrite <- H2. auto.
Qed.

Lemma diamond_4 : forall P s tl1 tl2 P1 s1 P2 s2,
  (P,s) --[ tl1 ]-->* (P1,s1) -> (P,s) --[ tl2 ]-->* (P2,s2) ->
  (exists P' tl1' tl2' s1' s2',
    (P1,s1) --[ tl1' ]-->* (P',s1') /\ (P2,s2) --[ tl2' ]-->* (P',s2') /\ eq_state_ext s1' s2').
Proof.
intros.
elim (diamond_4a _ _ _ _ _ _ _ _ H H0); auto.
intros. destroy H1. exists x, x0, x1, x2, x3; auto.
Qed.

(** Useful particular cases. *)

Lemma MCP_ToStar_End : forall c c' tl, c --[ tl ]-->* c' ->
  Main (fst c) = End -> tl = nil /\ c = c'.
Proof.
intros.
inversion H; auto.
exfalso.
induction c, a. simpl in H0; rewrite H0 in H1.
inversion H1. inversion H11.
Qed.

Lemma diamond_5a : forall P s tl1 tl2 P1 s1 P2 s2,
  (P,s) --[ tl1 ]-->* (P1,s1) -> (P,s) --[ tl2 ]-->* (P2,s2) ->
  Main P2 = End -> 
  (exists tl1' s1',
    (P1,s1) --[ tl1' ]-->* (P2,s1') /\ eq_state_ext s1' s2 /\ length tl1 + length tl1' = length tl2).
Proof.
intros.
elim (diamond_4a _ _ _ _ _ _ _ _ H H0); intros.
destroy H2.
rename x into P', x0 into tl', x1 into tl'', x2 into s', x3 into s''.
elim (MCP_ToStar_End _ _ _ H4 H1); intros.
inversion H7.
exists tl', s'; repeat split; auto.
rewrite H6, plus_0_r in H2; auto.
Qed.

Lemma diamond_5 : forall P s tl1 tl2 P1 s1 P2 s2,
  (P,s) --[ tl1 ]-->* (P1,s1) -> (P,s) --[ tl2 ]-->* (P2,s2) ->
  Main P2 = End -> 
  (exists tl1' s1',
    (P1,s1) --[ tl1' ]-->* (P2,s1') /\ eq_state_ext s1' s2).
Proof.
intros.
elim (diamond_5a _ _ _ _ _ _ _ _ H H0 H1).
intros. destroy H2; eauto.
Qed.

Lemma termination_unique : forall c tl1 c1 tl2 c2,
  c --[tl1]-->* c1 -> c --[tl2]-->* c2 ->
  Main (fst c1) = End -> Main (fst c2) = End -> eq_state_ext (snd c1) (snd c2).
Proof.
intros.
induction c, c1, c2. induction a, p, p0. simpl.
elim (diamond_4 _ _ _ _ _ _ _ _ H H0); intros.
destroy H3.
elim (MCP_ToStar_End _ _ _ H4 H1); intros.
elim (MCP_ToStar_End _ _ _ H5 H2); intros.
rewrite H6 in H4; rewrite H8 in H5. inversion H4; inversion H5; auto.
Qed.

End Confluence.

End MCBase.
*)
