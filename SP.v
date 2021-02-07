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

Lemma Par_comm : forall N N', Network_disjoint N N' ->
  Network_eq (N | N') (N' | N).
Proof.
red; intros.
unfold Par.
do 2 elim Behaviour_eq_End_dec; intros; auto.
+ transitivity End; auto.
+ exfalso.
  elim (H p); auto.
Qed.

Lemma Par_eq : forall N1 N2 N1' N2',
  Network_eq N1 N1' -> Network_eq N2 N2' -> Network_eq (N1 | N2) (N1' | N2').
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
  forall N p, Network_eq N (Network_rm N p | p [N p]).
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
  forall p, Network_eq (Network_rm N p) (Network_rm N' p).
Proof.
red; intros. unfold Network_rm.
case_eq (Pid_dec p0 p); auto.
Qed.

Lemma Network_rm_res_ps :
  forall N ps, Network_eq N (Network_rm_ps N ps | Network_res_ps N ps).
Proof.
intros.
red. unfold Network_rm_ps, Network_res_ps, Par. intro.
case_eq (in_dec P.eq_dec p ps); intros.
+ elim Behaviour_eq_End_dec; auto.
  intro. contradiction.
+ elim Behaviour_eq_End_dec; auto.
Qed.

(* This construction makes the following lemma easier to prove. *)
Lemma Network_eq_within_ps_dec : forall ps N N', within_ps ps N -> within_ps ps N' ->
  {Network_eq N N'}+{~Network_eq N N'}.
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
    Network_eq N1 N2 ->
    SP_To SPDefs N1 s t N1' s' -> SP_To SPDefs N2 s t N1' s'.
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
  SP_To Defs N s tl N1 s1 -> SP_To Defs N s tl N2 s2 ->
  Network_eq N1 N2.
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
  tl1 = tl2 -> Network_eq N1 N2 /\ eq_state_ext s1 s2.
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

(** Rewriting of networks. *)

Lemma Network_eq_cross'' : forall N N1 N2 p q Bp Bq,
  p <> q -> Network_eq N1 (Network_rm N p| p [Bp]) ->
  Network_eq N2 (Network_rm N q | q [Bq]) ->
  Network_eq (Network_rm N2 p | p [Bp]) (Network_rm N1 q | q [Bq]).
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
  Network_eq (Network_rm (Network_rm N2 p) q | p [Bp] | q [Bq])
             (Network_rm N1 r | r [Br]).
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
  Network_eq (Network_rm (Network_rm N2 p) q | p [Bp] | q [Bq])
             (Network_rm (Network_rm N1 r) s | r [Br] | s [Bs]).
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

Section Merge.

Inductive XBehaviour : Type :=
| XEnd : XBehaviour
| XSend : Pid -> Expr -> XBehaviour -> XBehaviour
| XRecv : Pid -> Var -> XBehaviour -> XBehaviour
| XSel : Pid -> Label -> XBehaviour -> XBehaviour
| XBranching : Pid -> option XBehaviour -> option XBehaviour -> XBehaviour
| XCond : BExpr -> XBehaviour -> XBehaviour -> XBehaviour
| XCall : RecVar -> XBehaviour
| XUndefined : XBehaviour
.

Lemma XUndefined_dec : forall B, {B = XUndefined} + {B <> XUndefined}.
Proof. induction B; auto; right; discriminate. Qed.

Lemma Xmatch_elim : forall B T (X1 X2:T), B <> XUndefined ->
  match B with XUndefined => X1 | _ => X2 end = X2.
Proof. induction B; try case o, o0; auto. intros; elim H; auto. Qed.

(* Sigh. *)

Fixpoint Xdepth (B:XBehaviour) : nat :=
match B with
 | XSend p e B' => 1 + Xdepth B'
 | XRecv p x B' => 1 + Xdepth B'
 | XSel p l B' => 1 + Xdepth B'
 | XBranching p mB mB' => 1
                          + (match mB with None => 0 | Some B => Xdepth B end)
                          + (match mB' with None => 0 | Some B => Xdepth B end)
 | XCond b B1 B2 => 1 + Nat.max (Xdepth B1) (Xdepth B2)
 | XCall X => 1
 | XEnd => 1
 | XUndefined => 0
end.

Theorem XBehaviour_ind' :
  forall P:XBehaviour -> Prop,
    P XEnd ->
    (forall p e B, P B -> P (XSend p e B)) ->
    (forall p v B, P B -> P (XRecv p v B)) ->
    (forall p l B, P B -> P (XSel p l B)) ->
    (forall p mB mB', (forall B, mB = Some B -> P B) ->
                      (forall B, mB' = Some B -> P B) ->
                      P (XBranching p mB mB')) ->
    (forall b B1 B2, P B1 -> P B2 -> P (XCond b B1 B2)) ->
    (forall X, P (XCall X)) ->
    P XUndefined ->
    forall B, P B.
Proof.
intros; revert B.
assert (forall d B, Xdepth B <= d -> P B).
2: eauto.
induction d; intros; case_eq B; intros; auto; rewrite H8 in H7; try (exfalso; inversion H7; fail); auto with arith.
+ clear H H0 H1 H2 H4 H5 H6 H8 B.
  apply H3.
  1,2: intros; apply IHd;
    rewrite H in H7; simpl in H7; apply le_S_n in H7;
    etransitivity; [idtac | apply H7]; auto with arith.
+ apply H4; apply IHd; apply le_S_n in H7.
  - etransitivity. eapply Nat.le_max_l. eauto.
  - etransitivity. eapply Nat.le_max_r. eauto.
Qed.

Theorem XBehaviour_rec' :
  forall P:XBehaviour -> Type,
    P XEnd ->
    (forall p e B, P B -> P (XSend p e B)) ->
    (forall p v B, P B -> P (XRecv p v B)) ->
    (forall p l B, P B -> P (XSel p l B)) ->
    (forall p mB mB', (forall B, mB = Some B -> P B) ->
                      (forall B, mB' = Some B -> P B) ->
                      P (XBranching p mB mB')) ->
    (forall b B1 B2, P B1 -> P B2 -> P (XCond b B1 B2)) ->
    (forall X, P (XCall X)) ->
    P XUndefined ->
    forall B, P B.
Proof.
intros; revert B.
assert (forall d B, Xdepth B <= d -> P B).
2: eauto.
induction d; intros; case_eq B; intros; auto; rewrite H0 in H; try (exfalso; inversion H; fail); auto with arith.
+ apply X3.
  1,2: intros; apply IHd;
    rewrite H1 in H; simpl in H; apply le_S_n in H;
    etransitivity; [idtac | apply H]; auto with arith.
+ apply X4; apply IHd; apply le_S_n in H.
  - etransitivity. eapply Nat.le_max_l. eauto.
  - etransitivity. eapply Nat.le_max_r. eauto.
Qed.

Fixpoint inject (B:Behaviour) : XBehaviour :=
match B with
| End                    => XEnd
| p ! e; B               => XSend p e (inject B)
| p ? v; B               => XRecv p v (inject B)
| p (+) l; B             => XSel p l (inject B)
| p & None // None       => XBranching p None None
| p & Some Bl // None    => XBranching p (Some (inject Bl)) None
| p & None // Some Br    => XBranching p None (Some (inject Br))
| p & Some Bl // Some Br => XBranching p (Some (inject Bl)) (Some (inject Br))
| If e Then B1 Else B2   => XCond e (inject B1) (inject B2)
| Call X                 => XCall X
end.

Lemma inject_not_undefined : forall B, inject B <> XUndefined.
Proof. induction B; try case o, o0; discriminate. Qed.

Lemma inject_elim : forall B, exists B', inject B = B' /\ B' <> XUndefined.
Proof.
intro; exists (inject B); split; auto.
apply inject_not_undefined.
Qed.

Lemma inject_match : forall B T (X1 X2:T),
  match inject B with XUndefined => X1 | _ => X2 end = X2.
Proof. induction B; try case o, o0; auto. Qed.

Lemma inject_inj : forall B B', inject B = inject B' -> B = B'.
Proof.
induction B using Behaviour_ind'; induction B' using Behaviour_ind';
  intros; auto; try inversion H;
  try (induction mB, mB'; inversion H1; fail);
  try (rewrite (IHB _ H3); auto).
+ induction mB, mB', mB0, mB'0; inversion H3; auto.
  rewrite H with a b0; auto. rewrite H0 with b b1; auto.
  rewrite H with a b; auto.
  rewrite H0 with b b0; auto.
+ rewrite (IHB1 _ H2), (IHB2 _ H3); auto.
+ inversion H1; auto.
Qed.

Fixpoint Xmerge (B1 B2:XBehaviour) : XBehaviour :=
match B1, B2 with
| XEnd,                   XEnd           => XEnd
| XSend p e B,            XSend p' e' B' =>
    if Pid_dec p p' && Expr_dec e e'
    then match Xmerge B B' with XUndefined => XUndefined
                              | _          => XSend p e (Xmerge B B') end
    else XUndefined
| XRecv p v B,            XRecv p' v' B' =>
    if Pid_dec p p' && Var_dec v v'
    then match Xmerge B B' with XUndefined => XUndefined
                              | _          => XRecv p v (Xmerge B B') end
    else XUndefined
| XSel p l B,             XSel p' l' B' =>
    if Pid_dec p p' && eqb_label l l'
    then match Xmerge B B' with XUndefined => XUndefined
                              | _          => XSel p l (Xmerge B B') end
    else XUndefined
| XBranching p Bl Br,     XBranching p' Bl' Br' =>
    if Pid_dec p p'
    then let BL := match Bl with None   => Bl'
                               | Some B => match Bl' with None    => Bl
                                                        | Some B' => Some (Xmerge B B')
                                           end
                   end
      in let BR := match Br with None   => Br'
                               | Some B => match Br' with None    => Br
                                                        | Some B' => Some (Xmerge B B')
                                           end
                   end
      in match BL, BR with Some XUndefined, _ => XUndefined
                         | _, Some XUndefined => XUndefined
                         | _, _               => XBranching p BL BR
         end
    else XUndefined
| XCond e B1 B2,          XCond e' B1' B2'      =>
    if BExpr_dec e e'
    then match Xmerge B1 B1', Xmerge B2 B2' with XUndefined, _ => XUndefined
                                               | _, XUndefined => XUndefined
                                               | Bt, Be        => XCond e Bt Be end
    else XUndefined
| XCall X,                XCall X'              =>
    if RecVar_dec X X' then XCall X else XUndefined
| _,                         _                  => XUndefined
end.

Definition merge B1 B2 := Xmerge (inject B1) (inject B2).

Lemma merge_undefined_or_behaviour : forall B1 B2,
  { merge B1 B2 = XUndefined } + { exists B, merge B1 B2 = inject B }.
Proof.
unfold merge.
induction B1 using Behaviour_rec'; induction B2 using Behaviour_rec'; auto;
  try (case mB; case mB'; auto; fail); simpl.
+ right. exists End; auto.
+ elim Pid_dec; auto. elim Expr_dec; auto. simpl.
  elim (IHB1 B2); intro. rewrite a; auto. 
  right. inversion_clear b. rewrite H, inject_match.
  exists (p ! e; x); auto.
+ elim Pid_dec; auto. elim Var_dec; auto. simpl.
  elim (IHB1 B2); intro. rewrite a; auto.
  right. inversion_clear b. rewrite H, inject_match.
  exists (p ? v; x); auto.
+ elim Pid_dec; auto. elim eqb_label; auto. simpl.
  elim (IHB1 B2); intro. rewrite a; auto.
  right. inversion_clear b. rewrite H, inject_match.
  exists (p (+) l; x); auto.
+ case_eq mB; case_eq mB0; case_eq mB'; case_eq mB'0; simpl; intros;
  elim Pid_dec; auto; do 2 try rewrite inject_match;
  try (right; exists (p & Some b0 // Some b); auto; fail);
  try (right; exists (p & Some b // None); auto; fail);
  try (right; exists (p & None // Some b); auto; fail).
  - elim (X _ H2 b1); intros. rewrite a; auto.
    elim (X0 _ H0 b); intros.
    * left. inversion_clear b3. rewrite H3, inject_match, a; auto.
    * right. inversion_clear b3; inversion_clear b4.
      rewrite H3, inject_match, H4, inject_match.
      exists (p & Some x // Some x0); auto.
  - elim (X _ H2 b0); intros. rewrite a; auto.
    right. inversion_clear b2. rewrite H3, inject_match.
    exists (p & Some x // Some b); auto.
  - elim (X _ H2 b0); intros. rewrite a; auto.
    right. inversion_clear b2. rewrite H3, inject_match.
    exists (p & Some x // Some b); auto.
  - elim (X _ H2 b); intros. rewrite a; auto.
    right. inversion_clear b1. rewrite H3, inject_match.
    exists (p & Some x // None); auto.
  - elim (X0 _ H0 b); intros. rewrite a; auto.
    right. inversion_clear b2. rewrite H3, inject_match.
    exists (p & Some b1 // Some x); auto.
  - elim (X0 _ H0 b); intros. rewrite a; auto.
    right. inversion_clear b2. rewrite H3, inject_match.
    exists (p & Some b1 // Some x); auto.
  - elim (X0 _ H0 b); intros. rewrite a; auto.
    right. inversion_clear b1. rewrite H3, inject_match.
    exists (p & None // Some x); auto.
  - right; exists (p & None // None); auto.
+ elim BExpr_dec; auto.
  elim (IHB1_1 B2_1); intro. rewrite a; auto.
  elim (IHB1_2 B2_2); intro.
  - left. inversion_clear b1. rewrite H, a; case x; intros; try case o, o0; auto.
  - right. inversion_clear b1. inversion_clear b2.
    rewrite H, H0.
    exists (If b Then x Else x0); case x, x0; intros; try case o, o0; try case o1, o2; simpl; auto.
+ elim RecVar_dec; auto.
  right. exists (Call X); auto.
Qed.

Lemma merge_not_undefined : forall B B', merge B B' <> XUndefined ->
  exists B'', merge B B' = inject B''.
Proof.
intros.
elim (merge_undefined_or_behaviour B B'); auto.
tauto.
Qed.

Lemma merge_idempotent : forall B, merge B B = inject B.
Proof.
unfold merge.
BInduction B mB mB'; simpl; intros;
  try rewrite Pdec.eqb_refl;
  try rewrite Edec.eqb_refl;
  try rewrite Vdec.eqb_refl;
  try rewrite Xdec.eqb_refl;
  try rewrite label_eqb_refl;
  try rewrite Bdec.eqb_refl;
  try rewrite Rdec.eqb_refl;
  try rewrite IHB, inject_match;
  simpl; auto.
+ rewrite H, H0, inject_match, inject_match; auto.
+ rewrite H, inject_match; auto.
+ rewrite H0, inject_match; auto.
+ rewrite IHB1, IHB2.
  case B1, B2; intros; try case o, o0; try case o1, o2; auto.
Qed.

Lemma Xmerge_comm : forall B B', Xmerge B B' = Xmerge B' B.
Proof.
induction B using XBehaviour_ind'; induction B' using XBehaviour_ind'; simpl; auto;
  try (case_eq mB; case_eq mB'; intros; auto);
  try (case_eq mB0; case_eq mB'0; intros; auto); simpl;
  unfold Pid_dec, Expr_dec, Var_dec, BExpr_dec, RecVar_dec; simpl;
  try rewrite Pdec.eqb_sym;
  try rewrite Edec.eqb_sym;
  try rewrite Vdec.eqb_sym;
  try rewrite Xdec.eqb_sym;
  try rewrite label_eqb_sym;
  try rewrite Bdec.eqb_sym;
  try rewrite Rdec.eqb_sym; auto;
  try (case_eq (Pdec.eqb p0 p); intro Hp0p; simpl; auto; rewrite Pdec.eqb_eq in Hp0p; rewrite Hp0p);
  try (case_eq (Edec.eqb e0 e); intro He0e; simpl; auto; rewrite Edec.eqb_eq in He0e; rewrite He0e);
  try (case_eq (Xdec.eqb v0 v); intro Hv0v; simpl; auto; rewrite Xdec.eqb_eq in Hv0v; rewrite Hv0v);
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; auto; rewrite label_eqb_eq in Hl0l; rewrite Hl0l);
  try (case_eq (Bdec.eqb b0 b); intro Hb0b; simpl; auto; rewrite Bdec.eqb_eq in Hb0b; rewrite Hb0b);
  try (case_eq (Rdec.eqb X0 X); intro HX0X; simpl; auto; rewrite Rdec.eqb_eq in HX0X; rewrite HX0X);
  try rewrite IHB; try rewrite (H _ H4); try rewrite (H0 _ H3); auto.
rewrite IHB1, IHB2; auto.
Qed.

Lemma merge_comm : forall B B', merge B B' = merge B' B.
Proof. intros. apply Xmerge_comm. Qed.

(** Inversion lemmas about merge. *)
Lemma merge_inv_End : forall B B', merge B B' = XEnd -> B = End /\ B' = End.
Proof.
unfold merge.
intros B B' HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (case o; case o0); try (case o1; case o2);
  simpl; auto; try (intros; inversion HBB'; fail);
  unfold Pid_dec, Expr_dec, Var_dec, BExpr_dec, RecVar_dec; simpl;
  try (case_eq (Pdec.eqb p0 p); intro Hp0p; simpl; try (rewrite Pdec.eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (Edec.eqb e0 e); intro He0e; simpl; try (rewrite Edec.eqb_eq in He0e; rewrite He0e));
  try (case_eq (Xdec.eqb v0 v); intro Hv0v; simpl; try (rewrite Xdec.eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (Bdec.eqb b2 b); intro Hb0b; simpl; try (rewrite Bdec.eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (Rdec.eqb r0 r); intro HX0X; simpl; try (rewrite Rdec.eqb_eq in HX0X; rewrite HX0X));
  intros; try inversion HBB';
  try (elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0).
4,7,13:
  elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
5,9: elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
5,8,9,10: elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b2))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b1)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b3) (inject b0))); intro HM.
  rewrite HM in H0; inversion H0.
  elim (XUndefined_dec (Xmerge (inject b4) (inject b1))); intro HM'.
  rewrite HM', Xmatch_elim in H0; auto; inversion H0.
  revert HM HM' H0.
  case (Xmerge (inject b3) (inject b0)); case (Xmerge (inject b4) (inject b1));
  intros; inversion H0.
Qed.

Lemma merge_inv_Send : forall B B' p e X, merge B B' = XSend p e X ->
  exists B1 B1', B = p ! e; B1 /\ B' = p ! e; B1' /\ merge B1 B1' = X.
Proof.
unfold merge.
intros B B' P E X HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (case o; case o0); try (case o1; case o2);
  simpl; auto; try (intros; inversion HBB'; fail);
  unfold Pid_dec, Expr_dec, Var_dec, BExpr_dec, RecVar_dec; simpl;
  try (case_eq (Pdec.eqb p0 p); intro Hp0p; simpl; try (rewrite Pdec.eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (Edec.eqb e0 e); intro He0e; simpl; try (rewrite Edec.eqb_eq in He0e; rewrite He0e));
  try (case_eq (Xdec.eqb v0 v); intro Hv0v; simpl; try (rewrite Xdec.eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (Bdec.eqb b2 b); intro Hb0b; simpl; try (rewrite Bdec.eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (Rdec.eqb r0 r); intro HX0X; simpl; try (rewrite Rdec.eqb_eq in HX0X; rewrite HX0X));
  intros; try inversion HBB';
  try (elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0).
1: exists b0, b; auto.
4,7,13:
  elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
5,9: elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
5,8,9,10: elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b2))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b1)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b3) (inject b0))); intro HM.
  rewrite HM in H0; inversion H0.
  elim (XUndefined_dec (Xmerge (inject b4) (inject b1))); intro HM'.
  rewrite HM', Xmatch_elim in H0; auto; inversion H0.
  revert HM HM' H0.
  case (Xmerge (inject b3) (inject b0)); case (Xmerge (inject b4) (inject b1));
  intros; inversion H0.
Qed.

Lemma merge_inv_Recv : forall B B' p v X, merge B B' = XRecv p v X ->
  exists B1 B1', B = p ? v; B1 /\ B' = p ? v; B1' /\ merge B1 B1' = X.
Proof.
unfold merge.
intros B B' P V X HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (case o; case o0); try (case o1; case o2);
  simpl; auto; try (intros; inversion HBB'; fail);
  unfold Pid_dec, Expr_dec, Var_dec, BExpr_dec, RecVar_dec; simpl;
  try (case_eq (Pdec.eqb p0 p); intro Hp0p; simpl; try (rewrite Pdec.eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (Edec.eqb e0 e); intro He0e; simpl; try (rewrite Edec.eqb_eq in He0e; rewrite He0e));
  try (case_eq (Xdec.eqb v0 v); intro Hv0v; simpl; try (rewrite Xdec.eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (Bdec.eqb b2 b); intro Hb0b; simpl; try (rewrite Bdec.eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (Rdec.eqb r0 r); intro HX0X; simpl; try (rewrite Rdec.eqb_eq in HX0X; rewrite HX0X));
  intros; try inversion HBB';
  try (elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0).
1: exists b0, b; auto.
4,7,13:
  elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
5,9: elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
5,8,9,10: elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b2))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b1)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b3) (inject b0))); intro HM.
  rewrite HM in H0; inversion H0.
  elim (XUndefined_dec (Xmerge (inject b4) (inject b1))); intro HM'.
  rewrite HM', Xmatch_elim in H0; auto; inversion H0.
  revert HM HM' H0.
  case (Xmerge (inject b3) (inject b0)); case (Xmerge (inject b4) (inject b1));
  intros; inversion H0.
Qed.

Lemma merge_inv_Sel : forall B B' p l X, merge B B' = XSel p l X ->
  exists B1 B1', B = p (+) l; B1 /\ B' = p (+) l; B1' /\ merge B1 B1' = X.
Proof.
unfold merge.
intros B B' P L X HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (case o; case o0); try (case o1; case o2);
  simpl; auto; try (intros; inversion HBB'; fail);
  unfold Pid_dec, Expr_dec, Var_dec, BExpr_dec, RecVar_dec; simpl;
  try (case_eq (Pdec.eqb p0 p); intro Hp0p; simpl; try (rewrite Pdec.eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (Edec.eqb e0 e); intro He0e; simpl; try (rewrite Edec.eqb_eq in He0e; rewrite He0e));
  try (case_eq (Xdec.eqb v0 v); intro Hv0v; simpl; try (rewrite Xdec.eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (Bdec.eqb b2 b); intro Hb0b; simpl; try (rewrite Bdec.eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (Rdec.eqb r0 r); intro HX0X; simpl; try (rewrite Rdec.eqb_eq in HX0X; rewrite HX0X));
  intros; try inversion HBB';
  try (elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0).
1: exists b0, b; auto.
4,7,13:
  elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
5,9: elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
5,8,9,10: elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b2))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b1)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b3) (inject b0))); intro HM.
  rewrite HM in H0; inversion H0.
  elim (XUndefined_dec (Xmerge (inject b4) (inject b1))); intro HM'.
  rewrite HM', Xmatch_elim in H0; auto; inversion H0.
  revert HM HM' H0.
  case (Xmerge (inject b3) (inject b0)); case (Xmerge (inject b4) (inject b1));
  intros; inversion H0.
Qed.

Lemma merge_inv_Branching : forall B B' p Bl Br, merge B B' = XBranching p Bl Br ->
  exists Bl' Bl'' Br' Br'', B = p & Bl' // Br' /\ B' = p & Bl'' // Br''
  /\ (Bl = None -> Bl' = None /\ Bl'' = None)
  /\ (Br = None -> Br' = None /\ Br'' = None)
  /\ (forall BL, Bl = Some BL ->
         (Bl' = None -> exists BL'', Bl'' = Some BL'' /\ BL = inject BL'')
      /\ (Bl'' = None -> exists BL', Bl' = Some BL' /\ BL = inject BL')
      /\ (forall BL' BL'', Bl' = Some BL' /\ Bl'' = Some BL'' -> merge BL' BL'' = BL))
  /\ (forall BR, Br = Some BR ->
         (Br' = None -> exists BR'', Br'' = Some BR'' /\ BR = inject BR'')
      /\ (Br'' = None -> exists BR', Br' = Some BR' /\ BR = inject BR')
      /\ (forall BR' BR'', Br' = Some BR' /\ Br'' = Some BR'' -> merge BR' BR'' = BR)).
Proof.
unfold merge.
intros B B' P Be Bt HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (case o; case o0); try (case o1; case o2);
  simpl; auto; try (intros; inversion HBB'; fail);
  unfold Pid_dec, Expr_dec, Var_dec, BExpr_dec, RecVar_dec; simpl;
  try (case_eq (Pdec.eqb p0 p); intro Hp0p; simpl; try (rewrite Pdec.eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (Edec.eqb e0 e); intro He0e; simpl; try (rewrite Edec.eqb_eq in He0e; rewrite He0e));
  try (case_eq (Xdec.eqb v0 v); intro Hv0v; simpl; try (rewrite Xdec.eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (Bdec.eqb b2 b); intro Hb0b; simpl; try (rewrite Bdec.eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (Rdec.eqb r0 r); intro HX0X; simpl; try (rewrite Rdec.eqb_eq in HX0X; rewrite HX0X));
  intros; try inversion HBB';
  try (elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0).
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b2))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some b0), (Some b2), (Some b), (Some b1);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    inversion H6; inversion H7; auto.
+ elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some b), (Some b1), None, (Some b0);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
  exists b0; auto.
+ elim (XUndefined_dec (inject b1)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, (Some b1), (Some b), (Some b0);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
  exists b1; auto.
+ elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0;
  exists None, (Some b0), None, (Some b);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto);
  [ exists b0 | exists b]; auto.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some b0), (Some b1), (Some b), None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
  exists b; auto.
+ elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some b), (Some b0), None, None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, (Some b0), (Some b), None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto);
  [ exists b0 | exists b]; auto.
+ elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, (Some b), None, None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
  exists b; auto.
+ elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some b0), None, (Some b), (Some b1);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
  exists b0; auto.
+ elim (XUndefined_dec (inject b)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some b), None, None, (Some b0);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto);
  [ exists b | exists b0]; auto.
+ elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, None, (Some b), (Some b0);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, None, None, (Some b);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
  exists b; auto.
+ elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some b0), None, (Some b), None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto);
  [ exists b0 | exists b]; auto.
+ elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some b), None, None, None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
  exists b; auto.
+ elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, None, (Some b), None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
  exists b; auto.
+ exists None, None, None, None;
  repeat (split; auto); try inversion H; intros; try inversion H4.
+ clear HBB'.
  elim (XUndefined_dec (Xmerge (inject b3) (inject b0))); intro HM.
  rewrite HM in H0; inversion H0.
  elim (XUndefined_dec (Xmerge (inject b4) (inject b1))); intro HM'.
  rewrite HM', Xmatch_elim in H0; auto; inversion H0.
  revert HM HM' H0.
  case (Xmerge (inject b3) (inject b0)); case (Xmerge (inject b4) (inject b1));
  intros; inversion H0.
Qed.

Lemma merge_inv_Branching_None_None : forall B B' p,
  merge B B' = XBranching p None None ->
  B = p & None // None /\ B' = p & None // None.
Proof.
intros.
elim (merge_inv_Branching _ _ _ _ _ H); intros.
destroy H0.
elim H3; auto; elim H4; auto.
intros. rewrite H1, H2, H6, H7, H8, H9; auto.
Qed.

Lemma merge_inv_Branching_Some_None : forall B B' p Bl,
  merge B B' = XBranching p (Some Bl) None ->
  (B = p & None // None /\ exists BL, B' = p & Some BL // None  /\ Bl = inject BL)
  \/ ((exists BL, B = p & Some BL // None /\ Bl = inject BL) /\ B' = p & None // None)
  \/ exists BL' BL'', B = p & Some BL' // None /\ B' = p & Some BL'' // None
    /\ merge BL' BL'' = Bl.
Proof.
intros.
elim (merge_inv_Branching _ _ _ _ _ H); intros.
destroy H0.
clear H3; elim H4; auto.
clear H0; elim (H5 Bl); auto.
intros. inversion_clear H3.
rewrite H1, H2, H6, H7; rewrite H1, H2, H6, H7 in H.
clear B B' x1 x2 H1 H2 H6 H7 H4 H5.
induction x. rename a into B. all: induction x0. 1,3: rename a into B'.
+ right. right. clear H0 H8. exists B, B'; auto.
+ left. split; auto. exists B'; split; auto.
  elim H0; intros; auto. inversion_clear H1. inversion H2; auto.
+ right. left. split; auto. exists B; split; auto.
  elim H8; intros; auto. inversion_clear H1. inversion H2; auto.
+ exfalso.
  unfold merge in H; simpl in H.
  unfold Pid_dec in H; rewrite Pdec.eqb_refl in H. inversion H.
Qed.

Lemma merge_inv_Branching_None_Some : forall B B' p Br,
  merge B B' = XBranching p None (Some Br) ->
  (B = p & None // None /\ exists BR, B' = p & None // Some BR  /\ Br = inject BR)
  \/ ((exists BR, B = p & None // Some BR /\ Br = inject BR) /\ B' = p & None // None)
  \/ exists BR' BR'', B = p & None // Some BR' /\ B' = p & None // Some BR''
    /\ merge BR' BR'' = Br.
Proof.
intros.
elim (merge_inv_Branching _ _ _ _ _ H); intros.
destroy H0.
clear H4; elim H3; auto.
clear H5; elim (H0 Br); auto.
intros. inversion_clear H5.
rewrite H1, H2, H6, H7; rewrite H1, H2, H6, H7 in H.
clear B B' x x0 H1 H2 H6 H7 H3.
induction x1. rename a into B. all: induction x2. 1,3: rename a into B'.
+ right. right. clear H0 H8. exists B, B'; auto.
+ left. split; auto. exists B'; split; auto.
  elim H4; intros; auto. inversion_clear H1. inversion H2; auto.
+ right. left. split; auto. exists B; split; auto.
  elim H8; intros; auto. inversion_clear H1. inversion H2; auto.
+ exfalso.
  unfold merge in H; simpl in H.
  unfold Pid_dec in H; rewrite Pdec.eqb_refl in H. inversion H.
Qed.

Lemma merge_inv_Cond : forall B B' b Be Bt, merge B B' = XCond b Be Bt ->
  exists Be' Be'' Bt' Bt'', B = Cond b Be' Bt' /\ B' = Cond b Be'' Bt''
    /\ merge Be' Be'' = Be /\ merge Bt' Bt'' = Bt.
Proof.
unfold merge.
intros B B' BB Be Bt HBB'; revert B B' BB Be Bt HBB'.
BDInduction B B' mB mB' mB0 mB'0;
  simpl; auto; try (intros; inversion HBB'; fail);
  unfold Pid_dec, Expr_dec, Var_dec, BExpr_dec, RecVar_dec; simpl;
  try (case_eq (Pdec.eqb p p0); intro Hp0p; simpl; try (rewrite Pdec.eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (Edec.eqb e e0); intro He0e; simpl; try (rewrite Edec.eqb_eq in He0e; rewrite He0e));
  try (case_eq (Xdec.eqb v v0); intro Hv0v; simpl; try (rewrite Xdec.eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l l0); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (Bdec.eqb b b0); intro Hb0b; simpl; try (rewrite Bdec.eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (Rdec.eqb X X0); intro HX0X; simpl; try (rewrite Rdec.eqb_eq in HX0X; rewrite HX0X));
  intros; try inversion HBB'.
1,2,3: elim (XUndefined_dec (Xmerge (inject B) (inject B'))); intro HM;
  [ rewrite HM in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
1: elim (XUndefined_dec (Xmerge (inject b2) (inject b0))); intro HT1;
  [ rewrite HT1 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
1,2: elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HT2;
  [ rewrite HT2 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
2,4,7,9,13: elim (XUndefined_dec (inject b0)); intro HT3;
  [ rewrite HT3 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
3,4,6,10,11,13,14,15: elim (XUndefined_dec (inject b)); intro HT4;
  [ rewrite HT4 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
7: elim (XUndefined_dec (inject b0)); intro HT5;
  [ rewrite HT5 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
11: elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro HT6;
  [ rewrite HT6 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
12: elim (XUndefined_dec (inject b1)); intro HT7;
  [ rewrite HT7 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
12,14,15: elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HT8;
  [ rewrite HT8 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
15: elim (XUndefined_dec (Xmerge (inject b1) (inject b0))); intro HT8;
  [ rewrite HT8 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
15: elim (XUndefined_dec (inject b)); intro HT7;
  [ rewrite HT7 in H8; inversion H8 | rewrite Xmatch_elim in H8; auto ].
all: try inversion H8.
clear IHB'1 IHB'2 HBB' Hb0b b. rename b0 into b.
elim (XUndefined_dec (Xmerge (inject B1) (inject B'1))); intro HM.
rewrite HM in H0; inversion H0.
elim (XUndefined_dec (Xmerge (inject B2) (inject B'2))); intro HM'.
rewrite HM', Xmatch_elim in H0; auto; inversion H0.
exists B1, B'1, B2, B'2.
revert HM HM' H0.
case (Xmerge (inject B1) (inject B'1));
case (Xmerge (inject B2) (inject B'2)); intros;
inversion H0; auto.
Qed.

Lemma merge_inv_Call : forall B B' X, merge B B' = XCall X ->
  B = Call X /\ B' = Call X.
Proof.
unfold merge.
intros B B' X HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (case o; case o0); try (case o1; case o2);
  simpl; auto; try (intros; inversion HBB'; fail);
  unfold Pid_dec, Expr_dec, Var_dec, BExpr_dec, RecVar_dec; simpl;
  try (case_eq (Pdec.eqb p0 p); intro Hp0p; simpl; try (rewrite Pdec.eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (Edec.eqb e0 e); intro He0e; simpl; try (rewrite Edec.eqb_eq in He0e; rewrite He0e));
  try (case_eq (Xdec.eqb v0 v); intro Hv0v; simpl; try (rewrite Xdec.eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (Bdec.eqb b2 b); intro Hb0b; simpl; try (rewrite Bdec.eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (Rdec.eqb r0 r); intro HX0X; simpl; try (rewrite Rdec.eqb_eq in HX0X; rewrite HX0X));
  intros; try inversion HBB';
  try (elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro HM;
  [ rewrite HM in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0).
4,7,13:
  elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
5,9: elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
5,8,9,10: elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b2))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b1)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b0))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b0) (inject b1))); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (inject b)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b0)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge (inject b) (inject b1))); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (inject b)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec (inject b0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
+ elim (XUndefined_dec (Xmerge (inject b3) (inject b0))); intro HM.
  rewrite HM in H0; inversion H0.
  elim (XUndefined_dec (Xmerge (inject b4) (inject b1))); intro HM'.
  rewrite HM', Xmatch_elim in H0; auto; inversion H0.
  revert HM HM' H0.
  case (Xmerge (inject b3) (inject b0)); case (Xmerge (inject b4) (inject b1));
  intros; inversion H0.
+ auto.
Qed.

(** Collapse an Undefined behaviour. *)
Fixpoint collapse (B:XBehaviour) : XBehaviour :=
let rec := fun B' => match collapse B' with XUndefined => XUndefined | _ => B end in
match B with
| XSend p e B' => rec B'
| XRecv p x B' => rec B'
| XSel p l B'  => rec B'
| XBranching p mB mB' => match mB, mB' with
                         | None,    None    => B
                         | Some Bl, None    => rec Bl
                         | None,    Some Br => rec Br
                         | Some Bl, Some Br => match collapse Bl, collapse Br with
                                               | XUndefined, _ => XUndefined
                                               | _, XUndefined => XUndefined
                                               | _, _          => B
                                               end
                         end
| XCond b B1 B2 => match collapse B1, collapse B2 with
                   | XUndefined, _ => XUndefined
                   | _, XUndefined => XUndefined
                   | _, _          => B
                   end
| _ => B
end.

(** Relationship with inject. *)
Lemma collapse_inject : forall B, collapse (inject B) = inject B.
Proof.
induction B using Behaviour_ind'; simpl; auto.
1,2,3: rewrite IHB, inject_match; auto.
2: rewrite IHB1, IHB2, inject_match, inject_match; auto.
case_eq mB; case_eq mB'; intros; simpl; auto.
+ rewrite (H _ H2), (H0 _ H1), inject_match, inject_match; auto.
+ rewrite (H _ H2), inject_match; auto.
+ rewrite (H0 _ H1), inject_match; auto.
Qed.

Lemma inject_exists : forall B,
  {B' | B = inject B'} -> collapse B <> XUndefined.
Proof.
intros. inversion_clear X.
rewrite H, collapse_inject; apply inject_not_undefined.
Qed.

Ltac XBeh_case B HB := elim (XUndefined_dec B); intro HB; try rewrite HB; auto;
  rewrite Xmatch_elim; auto.

(** Elimination lemmas. *)
Lemma collapse_char : forall B,
  {collapse B = XUndefined} + {collapse B = B}.
Proof.
induction B using XBehaviour_rec'; simpl; auto.
1,2,3: elim IHB; intro H; rewrite H; auto; XBeh_case B HB.
+ case_eq mB; case_eq mB'; intros; auto.
  - elim (X _ H0); intro HB; rewrite HB; auto; XBeh_case x0 Hx0.
    elim (X0 _ H); intro HB'; rewrite HB'; auto; XBeh_case x Hx.
  - elim (X _ H0); intro HB; rewrite HB; auto; XBeh_case x Hx.
  - elim (X0 _ H); intro HB'; rewrite HB'; auto; XBeh_case x Hx.
+ elim IHB1; intro H1; rewrite H1; auto; XBeh_case B1 HB1.
  elim IHB2; intro H2; rewrite H2; auto; XBeh_case B2 HB2.
Qed.

Lemma collapse_char' : forall B,
  ({B' | B = inject B'}) + {collapse B = XUndefined}.
Proof.
induction B using XBehaviour_rec'; simpl; auto.
+ left; exists End; auto.
+ elim IHB; intro H; try rewrite H; auto.
  left; elim H; clear H; intros B' HB'; rewrite HB'.
  exists (p ! e; B'); simpl; auto.
+ elim IHB; intro H; try rewrite H; auto.
  left; elim H; clear H; intros B' HB'; rewrite HB'.
  exists (p ? v; B'); simpl; auto.
+ elim IHB; intro H; try rewrite H; auto.
  left; elim H; clear H; intros B' HB'; rewrite HB'.
  exists (p (+) l; B'); simpl; auto.
+ case_eq mB; case_eq mB'; intros; auto.
  - elim (X _ H0); intro HB; try rewrite HB; auto.
    rewrite Xmatch_elim. 2: apply inject_exists; auto.
    elim (X0 _ H); intro HB'; try rewrite HB'; auto.
    rewrite Xmatch_elim. 2: apply inject_exists; auto.
    left; inversion_clear HB; inversion_clear HB'.
    exists (p & Some x1 // Some x2); rewrite H1, H2; auto.
  - elim (X _ H0); intro HB; try rewrite HB; auto.
    rewrite Xmatch_elim. 2: apply inject_exists; auto.
    left; inversion_clear HB.
    exists (p & Some x0 // None); rewrite H1; auto.
  - elim (X0 _ H); intro HB'; try rewrite HB'; auto.
    rewrite Xmatch_elim. 2: apply inject_exists; auto.
    left; inversion_clear HB'.
    exists (p & None // Some x0); rewrite H1; auto.
  - left. exists (p & None // None); auto.
+ elim IHB1; intro H1; try rewrite H1; auto.
  rewrite Xmatch_elim. 2: apply inject_exists; auto.
  elim IHB2; intro H2; try rewrite H2; auto.
  rewrite Xmatch_elim. 2: apply inject_exists; auto.
  left; inversion_clear H1; inversion_clear H2.
  exists (If b Then x Else x0); rewrite H, H0; auto.
+ left; exists (Call X); auto.
Qed.

Lemma collapse_char'' : forall B, collapse B = XUndefined ->
  forall B', B <> inject B'.
Proof.
induction B using XBehaviour_ind'; induction B' using Behaviour_ind'.
all: try inversion H.
all: try discriminate.
all: try (case mB, mB'; discriminate).
+ elim (XUndefined_dec (collapse B)); intro.
  intro; inversion H0; apply IHB with B'; auto.
  rewrite Xmatch_elim in H1; auto. inversion H1.
+ elim (XUndefined_dec (collapse B)); intro.
  intro; inversion H0; apply IHB with B'; auto.
  rewrite Xmatch_elim in H1; auto. inversion H1.
+ elim (XUndefined_dec (collapse B)); intro.
  intro; inversion H0; apply IHB with B'; auto.
  rewrite Xmatch_elim in H1; auto. inversion H1.
+ induction mB, mB', mB0, mB'0; try discriminate.
  all: simpl in H1.
  - elim (XUndefined_dec (collapse a)); intro.
    intro. inversion H4. apply H with a b; auto.
    rewrite Xmatch_elim in H1; auto.
    elim (XUndefined_dec (collapse x)); intro.
    intro. inversion H4. apply H0 with x b0; auto.
    rewrite Xmatch_elim in H1; auto. rewrite H1; discriminate.
  - elim (XUndefined_dec (collapse a)); intro.
    intro. inversion H4. apply H with a b; auto.
    rewrite Xmatch_elim in H1; auto. rewrite H1; discriminate.
  - elim (XUndefined_dec (collapse x)); intro.
    intro. inversion H4. apply H0 with x b; auto.
    rewrite Xmatch_elim in H1; auto. rewrite H1; discriminate.
+ elim (XUndefined_dec (collapse B1)); intro.
  intro; inversion H0; apply IHB1 with B'1; auto.
  rewrite Xmatch_elim in H1; auto.
  elim (XUndefined_dec (collapse B2)); intro.
  intro; inversion H0; apply IHB2 with B'2; auto.
  rewrite Xmatch_elim in H1; auto. inversion H1.
Qed.

Lemma collapse_exists : forall B, collapse B <> XUndefined ->
  exists B', B = inject B'.
Proof.
intros; elim (collapse_char' B); intros.
inversion_clear a; eauto.
elim H; auto.
Qed.

Lemma collapse_inv : forall B B', collapse B = inject B' -> B = inject B'.
Proof.
induction B using XBehaviour_ind'; auto; simpl; intros.
+ elim (collapse_char' B); intro.
  2: rewrite b in H; elim (inject_not_undefined B'); auto.
  inversion_clear a. rewrite H0 in H.
  rewrite Xmatch_elim, <- H0 in H; auto.
  rewrite collapse_inject; apply inject_not_undefined.
+ elim (collapse_char' B); intro.
  2: rewrite b in H; elim (inject_not_undefined B'); auto.
  inversion_clear a. rewrite H0 in H.
  rewrite Xmatch_elim, <- H0 in H; auto.
  rewrite collapse_inject; apply inject_not_undefined.
+ elim (collapse_char' B); intro.
  2: rewrite b in H; elim (inject_not_undefined B'); auto.
  inversion_clear a. rewrite H0 in H.
  rewrite Xmatch_elim, <- H0 in H; auto.
  rewrite collapse_inject; apply inject_not_undefined.
+ induction mB, mB'; auto.
  - elim (collapse_char' a); intro.
    2: rewrite b in H1; elim (inject_not_undefined B'); auto.
    inversion_clear a0. rewrite H2 in H1.
    rewrite Xmatch_elim, <- H2 in H1.
    elim (collapse_char' x); intro.
    2: rewrite b in H1; elim (inject_not_undefined B'); auto.
    inversion_clear a0. rewrite H3 in H1.
    rewrite Xmatch_elim, <- H3 in H1; auto.
    all: rewrite collapse_inject; apply inject_not_undefined.
  - elim (collapse_char' a); intro.
    2: rewrite b in H1; elim (inject_not_undefined B'); auto.
    inversion_clear a0. rewrite H2 in H1.
    rewrite Xmatch_elim, <- H2 in H1; auto.
    rewrite collapse_inject; apply inject_not_undefined.
  - elim (collapse_char' x); intro.
    2: rewrite b in H1; elim (inject_not_undefined B'); auto.
    inversion_clear a. rewrite H2 in H1.
    rewrite Xmatch_elim, <- H2 in H1; auto.
    rewrite collapse_inject; apply inject_not_undefined.
+ elim (collapse_char' B1); intro.
  2: rewrite b0 in H; elim (inject_not_undefined B'); auto.
  inversion_clear a. rewrite H0 in H.
  rewrite Xmatch_elim, <- H0 in H.
  elim (collapse_char' B2); intro.
  2: rewrite b0 in H; elim (inject_not_undefined B'); auto.
  inversion_clear a. rewrite H1 in H.
  rewrite Xmatch_elim, <- H1 in H; auto.
  all: rewrite collapse_inject; apply inject_not_undefined.
Qed.
(** Relationship with merge. *)
Local Ltac prove_this B HB := 
    elim (XUndefined_dec B); intro HB;
    [ rewrite HB; auto | rewrite Xmatch_elim; auto ].

Local Ltac assert_this B B' H :=
  assert ({ collapse B = XUndefined } + { collapse B' = XUndefined });
  [ elim (XUndefined_dec (collapse B)); auto; intros;
    elim (XUndefined_dec (collapse B')); auto; intros;
    do 2 rewrite Xmatch_elim in H; auto; inversion H | idtac].

Lemma collapse_merge : forall B B',
  collapse B = XUndefined -> collapse (Xmerge B B') = XUndefined.
Proof.
induction B using XBehaviour_ind'; induction B' using XBehaviour_ind';
  auto.
+ elim (XUndefined_dec (collapse B)); intros.
  2: { simpl in H. rewrite Xmatch_elim in H; auto. inversion H. }
  simpl. case Pid_dec; auto. case Expr_dec; auto.
  simpl. elim (XUndefined_dec (Xmerge B B')); intros.
  rewrite a0; auto. rewrite Xmatch_elim; auto.
  simpl. rewrite IHB; auto.
+ elim (XUndefined_dec (collapse B)); intros.
  2: { simpl in H. rewrite Xmatch_elim in H; auto. inversion H. }
  simpl. case Pid_dec; auto. case Var_dec; auto.
  simpl. elim (XUndefined_dec (Xmerge B B')); intros.
  rewrite a0; auto. rewrite Xmatch_elim; auto.
  simpl. rewrite IHB; auto.
+ elim (XUndefined_dec (collapse B)); intros.
  2: { simpl in H. rewrite Xmatch_elim in H; auto. inversion H. }
  simpl. case Pid_dec; auto. case eqb_label; auto.
  simpl. elim (XUndefined_dec (Xmerge B B')); intros.
  rewrite a0; auto. rewrite Xmatch_elim; auto.
  simpl. rewrite IHB; auto.
+ simpl. case Pid_dec; auto.
  case_eq mB; case_eq mB'; case_eq mB0; case_eq mB'0; intros;
  try (inversion H7; fail).
  - prove_this (Xmerge x2 x0) a. prove_this (Xmerge x1 x) a'.
    assert_this x1 x2 H7. inversion_clear H8; simpl.
    rewrite (H0 x1); auto. case (collapse (Xmerge x2 x0)); auto.
    rewrite H; auto.
  - prove_this (Xmerge x1 x) a. prove_this x0 a'.
    assert_this x1 x0 H7. inversion_clear H8; simpl.
    rewrite (H x1); auto.
    rewrite H9. case (collapse (Xmerge x1 x)); auto.
  - prove_this x1 a. prove_this (Xmerge x0 x) a'.
    assert_this x1 x0 H7. inversion_clear H8; simpl.
    rewrite H9; auto.
    rewrite (H0 x0); auto. case (collapse x1); auto.
  - prove_this x0 a. prove_this x a'.
  - prove_this (Xmerge x1 x0) a. prove_this x a'.
    elim (XUndefined_dec (collapse x1)); intro a''; simpl.
    rewrite (H x1); auto.
    rewrite Xmatch_elim in H7; auto. inversion H7.
  - prove_this (Xmerge x0 x) a. simpl.
    elim (XUndefined_dec (collapse x0)); intro a'; simpl.
    rewrite (H x0); auto.
    rewrite Xmatch_elim in H7; auto. inversion H7.
  - prove_this x0 a. prove_this x a'. simpl.
    elim (XUndefined_dec (collapse x0)); intro a''; simpl.
    rewrite a''; auto.
    rewrite Xmatch_elim; auto.
    rewrite Xmatch_elim in H7; auto; inversion H7.
  - prove_this x a.
  - prove_this x0 a. prove_this (Xmerge x1 x) a'.
    elim (XUndefined_dec (collapse x0)); intro a''; simpl.
    rewrite a''; auto.
    elim (XUndefined_dec (collapse x1)); intro; simpl.
    rewrite Xmatch_elim; auto. rewrite (H0 x1); auto.
    rewrite Xmatch_elim in H7; auto; inversion H7.
  - prove_this x a. prove_this x0 a'.
    simpl.
    elim (XUndefined_dec (collapse x0)); intro a''; simpl.
    rewrite a''; auto. case (collapse x); auto.
    elim (XUndefined_dec (collapse x)); intro; simpl.
    rewrite a0; auto.
    rewrite Xmatch_elim; auto.
    rewrite Xmatch_elim in H7; auto; inversion H7.
  - prove_this (Xmerge x0 x) a.
    simpl.
    elim (XUndefined_dec (collapse (Xmerge x0 x))); intro.
    rewrite a0; auto.
    elim (XUndefined_dec (collapse x0)); intro.
    elim b. apply H0; auto.
    rewrite Xmatch_elim in H7; auto. inversion H7.
  - prove_this x a.
+ simpl; intros.
  case BExpr_dec; auto.
  assert_this B1 B2 H. clear H IHB'1 IHB'2.
  inversion_clear H0.
  - generalize (IHB1 B'1 H); clear IHB1 IHB2.
    case (Xmerge B1 B'1); simpl; intros; auto.
    1,7: inversion H0.
    1,2,3: elim (XUndefined_dec (collapse x)); intros;
      [ case (Xmerge B2 B'2); simpl; try rewrite a; auto
      | rewrite Xmatch_elim in H0; auto; inversion H0 ].
    * revert H0. case o, o0; intros.
      4: inversion H0.
      2,3: elim (XUndefined_dec (collapse x)); intros;
        [ case (Xmerge B2 B'2); simpl; try rewrite a; auto
        | rewrite Xmatch_elim in H0; auto; inversion H0 ].
      assert_this x x0 H0.
      inversion_clear H1.
      case (Xmerge B2 B'2); simpl; try rewrite H2; auto.
      case (Xmerge B2 B'2); simpl; case (collapse x); try rewrite H2; auto.
    * assert_this x x0 H0. clear H0.
      inversion_clear H1.
      case (Xmerge B2 B'2); simpl; try rewrite H0; auto.
      case (Xmerge B2 B'2); simpl; case (collapse x); try rewrite H0; auto.
  - generalize (IHB2 B'2 H); clear IHB1 IHB2.
    case (Xmerge B2 B'2); simpl; intros; auto.
    1,7: inversion H0.
    6: case (Xmerge B1 B'1); auto.
    1,2,3: elim (XUndefined_dec (collapse x)); intros;
      [case (Xmerge B1 B'1); simpl; try rewrite a; auto;
        intros; try case o, o0; try case (collapse x0); try case (collapse x1); auto
      | rewrite Xmatch_elim in H0; auto; inversion H0].
    * revert H0. case o, o0; intros.
      4: inversion H0.
      2,3: elim (XUndefined_dec (collapse x)); intros;
        [ case (Xmerge B1 B'1); simpl; try rewrite a; auto;
          intros; try case o, o0; try case (collapse x0); try case (collapse x1); auto
        | rewrite Xmatch_elim in H0; auto; inversion H0].
      assert_this x x0 H0. clear H0.
      inversion_clear H1.
      case (Xmerge B1 B'1); simpl; try rewrite H0; auto;
        intros; try case o, o0; try case (collapse x1); try case (collapse x2); auto.
      case (Xmerge B1 B'1); simpl; try rewrite H0; auto;
        intros; try case o, o0; try case (collapse x); try case (collapse x1); try case (collapse x2); auto.
    * assert_this x x0 H0. clear H0.
      inversion_clear H1.
      case (Xmerge B1 B'1); simpl; try rewrite H0; auto;
        intros; try case o, o0; try case (collapse x1); try case (collapse x2); auto.
      case (Xmerge B1 B'1); simpl; try rewrite H0; auto;
        intros; try case o, o0; try case (collapse x); try case (collapse x1); try case (collapse x2); auto.
+ simpl; intros. inversion H.
Qed.

Lemma collapse_merge' : forall B B',
  collapse B' = XUndefined -> collapse (Xmerge B B') = XUndefined.
Proof. intros. rewrite Xmerge_comm. apply collapse_merge; auto. Qed.

Lemma Xmerge_idempotent : forall B, collapse B <> XUndefined ->
  Xmerge B B = B.
Proof.
intros. elim (collapse_char' B). 2: tauto.
intro. inversion_clear a. rewrite H0.
fold (merge x x). apply merge_idempotent.
Qed.

(** Inversion lemmas for Xmerge. *)
Lemma Xmerge_inv_Branching : forall B B' p Bl Br, Xmerge B B' = XBranching p Bl Br ->
  exists Bl' Bl'' Br' Br'', B = XBranching p Bl' Br' /\ B' = XBranching p Bl'' Br''
  /\ (Bl = None -> Bl' = None /\ Bl'' = None)
  /\ (Br = None -> Br' = None /\ Br'' = None)
  /\ (forall BL, Bl = Some BL ->
         (Bl' = None -> Bl'' = Some BL) /\ (Bl'' = None -> Bl' = Some BL)
      /\ (forall BL' BL'', Bl' = Some BL' /\ Bl'' = Some BL'' -> Xmerge BL' BL'' = BL))
  /\ (forall BR, Br = Some BR ->
         (Br' = None -> Br'' = Some BR) /\ (Br'' = None -> Br' = Some BR)
      /\ (forall BR' BR'', Br' = Some BR' /\ Br'' = Some BR'' -> Xmerge BR' BR'' = BR)).
Proof.
intros B B' P Be Bt HBB'; revert HBB'.
case B; case B'; intros; revert HBB';
  try (case o; case o0); try (case o1; case o2);
  simpl; auto; try (intros; inversion HBB'; fail);
  unfold Pid_dec, Expr_dec, Var_dec, BExpr_dec, RecVar_dec; simpl;
  try (case_eq (Pdec.eqb p0 p); intro Hp0p; simpl; try (rewrite Pdec.eqb_eq in Hp0p; rewrite Hp0p));
  try (case_eq (Edec.eqb e0 e); intro He0e; simpl; try (rewrite Edec.eqb_eq in He0e; rewrite He0e));
  try (case_eq (Xdec.eqb v0 v); intro Hv0v; simpl; try (rewrite Xdec.eqb_eq in Hv0v; rewrite Hv0v));
  try (case_eq (eqb_label l0 l); intro Hl0l; simpl; try (rewrite label_eqb_eq in Hl0l; rewrite Hl0l));
  try (case_eq (Bdec.eqb b2 b); intro Hb0b; simpl; try (rewrite Bdec.eqb_eq in Hb0b; rewrite Hb0b));
  try (case_eq (Rdec.eqb r0 r); intro HX0X; simpl; try (rewrite Rdec.eqb_eq in HX0X; rewrite HX0X));
  intros; try inversion HBB';
  try (elim (XUndefined_dec (Xmerge x0 x)); intro HM;
  [ rewrite HM in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0).
+ elim (XUndefined_dec (Xmerge x0 x2)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge x x1)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some x0), (Some x2), (Some x), (Some x1);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    inversion H6; inversion H7; auto.
+ elim (XUndefined_dec (Xmerge x x1)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec x0); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some x), (Some x1), None, (Some x0);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec x1); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge x x0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, (Some x1), (Some x), (Some x0);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec x0); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0;
  exists None, (Some x0), None, (Some x);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec (Xmerge x0 x1)); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some x0), (Some x1), (Some x), None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec (Xmerge x x0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some x), (Some x0), None, None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec x0); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, (Some x0), (Some x), None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, (Some x), None, None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec x0); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ].
  elim (XUndefined_dec (Xmerge x x1)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some x0), None, (Some x), (Some x1);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec x); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec x0); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some x), None, None, (Some x0);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec (Xmerge x x0)); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, None, (Some x), (Some x0);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, None, None, (Some x);
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec x0); intro HM;
  [ rewrite HM in H0; inversion H0
  | rewrite Xmatch_elim in H0; auto ];
  elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some x0), None, (Some x), None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists (Some x), None, None, None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ elim (XUndefined_dec x); intro HM';
  [ rewrite HM' in H0
  | rewrite Xmatch_elim in H0; auto ]; inversion H0.
  exists None, None, (Some x), None;
  repeat (split; auto); try inversion H; intros; try inversion H4;
    try (inversion H6; inversion H7; auto).
+ exists None, None, None, None;
  repeat (split; auto); try inversion H; intros; try inversion H4.
+ clear HBB'.
  revert H0. case Bdec.eqb; intro. 2: inversion H0.
  elim (XUndefined_dec (Xmerge x1 x)); intro HM.
  rewrite HM in H0; inversion H0.
  elim (XUndefined_dec (Xmerge x2 x0)); intro HM'.
  rewrite HM', Xmatch_elim in H0; auto; inversion H0.
  revert HM HM' H0.
  case (Xmerge x1 x); case (Xmerge x2 x0);
  intros; inversion H0.
Qed.

Lemma Xmerge_Cond_inv : forall b Bt Bt' Be Be',
  Xmerge Bt Bt' <> XUndefined -> Xmerge Be Be' <> XUndefined ->
  Xmerge (XCond b Bt Be) (XCond b Bt' Be') = XCond b (Xmerge Bt Bt') (Xmerge Be Be').
Proof.
intros. revert H H0.
simpl. unfold BExpr_dec; rewrite Bdec.eqb_refl.
case_eq (Xmerge Bt Bt'); case_eq (Xmerge Be Be'); simpl; auto.
all: intros; try (elim H1; auto; fail); try (elim H2; auto; fail).
Qed.

Lemma Xmerge_inv_inject : forall B1 B2 B, Xmerge B1 B2 = inject B ->
  exists B', B1 = inject B'.
Proof.
intros. symmetry in H.
revert B1 B2 B H.
induction B1 using XBehaviour_ind'; induction B2 using XBehaviour_ind';
  simpl; intros;
  try (elim (inject_not_undefined _ H); fail);
  try (elim (inject_not_undefined _ H1); fail).
+ exists End; auto.
+ revert H. case_eq (Pid_dec p p0). case_eq (Expr_dec e e0).
  all: simpl; intros.
  2: elim (inject_not_undefined _ H1).
  2: elim (inject_not_undefined _ H0).
  elim (XUndefined_dec (Xmerge B1 B2)); intro H'.
  1: rewrite H' in H1; elim (inject_not_undefined _ H1).
  rewrite Xmatch_elim in H1; auto.
  clear H H0 e0 p0.
  revert H1. case B; intros; inversion H1.
  2: induction o, o0; inversion H1.
  elim IHB1 with B2 b; auto. intros. destroy H.
  exists (p!e;x); repeat split; simpl.
  rewrite H; auto.
+ revert H. case_eq (Pid_dec p p0). case_eq (Var_dec v v0).
  all: simpl; intros.
  2: elim (inject_not_undefined _ H1).
  2: elim (inject_not_undefined _ H0).
  elim (XUndefined_dec (Xmerge B1 B2)); intro H'.
  1: rewrite H' in H1; elim (inject_not_undefined _ H1).
  rewrite Xmatch_elim in H1; auto.
  clear H H0 v0 p0.
  revert H1. case B; intros; inversion H1.
  2: induction o, o0; inversion H1.
  elim IHB1 with B2 b; auto. intros. destroy H.
  exists (p ? v;x); repeat split; simpl.
  rewrite H; auto.
+ revert H. case_eq (Pid_dec p p0). case_eq (eqb_label l l0).
  all: simpl; intros.
  2: elim (inject_not_undefined _ H1).
  2: elim (inject_not_undefined _ H0).
  elim (XUndefined_dec (Xmerge B1 B2)); intro H'.
  1: rewrite H' in H1; elim (inject_not_undefined _ H1).
  rewrite Xmatch_elim in H1; auto.
  clear H H0 l0 p0.
  revert H1. case B; intros; inversion H1.
  2: induction o, o0; inversion H1.
  elim IHB1 with B2 b; auto. intros. destroy H.
  exists (p(+)l;x); repeat split; simpl.
  rewrite H; auto.
+ revert H3. case_eq (Pid_dec p p0); simpl; intros.
  2: elim (inject_not_undefined _ H4).
  induction mB, mB', mB0, mB'0.
  - elim (XUndefined_dec (Xmerge a x0)); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    elim (XUndefined_dec (Xmerge x x1)); intro H''.
    1: rewrite H'' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    elim H with a x0 a0; auto. intros.
    elim H0 with x x1 b; auto. intros.
    exists (p & Some x2 // Some x3); simpl.
    rewrite H5, H9; auto.
  - elim (XUndefined_dec (Xmerge a x0)); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    elim (XUndefined_dec x); intro H''.
    1: rewrite H'' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    elim H with a x0 a0; auto. intros.
    exists (p & Some x1 // Some b); simpl.
    rewrite H5; auto.
  - elim (XUndefined_dec a); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    elim (XUndefined_dec (Xmerge x x0)); intro H''.
    1: rewrite H'' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    elim H0 with x x0 b; auto. intros.
    exists (p & Some a0 // Some x1); simpl.
    rewrite H5; auto.
  - elim (XUndefined_dec a); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    elim (XUndefined_dec x); intro H''.
    1: rewrite H'' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    exists (p & Some a0 // Some b); auto.
  - elim (XUndefined_dec (Xmerge a x)); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    elim (XUndefined_dec x0); intro H''.
    1: rewrite H'' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    elim H with a x a0; auto. intros.
    exists (p & Some x1 // None); simpl.
    rewrite H5; auto.
  - elim (XUndefined_dec (Xmerge a x)); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    elim H with a x a0; auto. intros.
    exists (p & Some x0 // None); simpl.
    rewrite H5; auto.
  - elim (XUndefined_dec a); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    elim (XUndefined_dec x); intro H''.
    1: rewrite H'' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    exists (p & Some a0 // None); auto.
  - elim (XUndefined_dec a); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    exists (p & Some a0 // None); auto.
  - elim (XUndefined_dec x0); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    elim (XUndefined_dec (Xmerge x x1)); intro H''.
    1: rewrite H'' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    elim H0 with x x1 b; auto. intros.
    exists (p & None // Some x2); simpl.
    rewrite H5; auto.
  - elim (XUndefined_dec x0); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    elim (XUndefined_dec x); intro H''.
    1: rewrite H'' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    exists (p & None // Some b); auto.
  - elim (XUndefined_dec (Xmerge x x0)); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    elim H0 with x x0 b; auto. intros.
    exists (p & None // Some x1); simpl.
    rewrite H5; auto.
  - elim (XUndefined_dec x); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    exists (p & None // Some b); auto.
  - elim (XUndefined_dec x); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    elim (XUndefined_dec x0); intro H''.
    1: rewrite H'' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    exists (p & None // None); auto.
  - elim (XUndefined_dec x); intro H'.
    1: rewrite H' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    exists (p & None // None); auto.
  - elim (XUndefined_dec x); intro H''.
    1: rewrite H'' in H4; elim (inject_not_undefined _ H4).
    rewrite Xmatch_elim in H4; auto.
    revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    exists (p & None // None); auto.
  - revert H4. case B; intros; inversion H4.
    clear H6. induction o, o0; inversion H4.
    exists (p & None // None); auto.
+ revert H. case_eq (BExpr_dec b b0); simpl; intros.
  2: elim (inject_not_undefined _ H0).
  clear IHB2_1 IHB2_2.
  elim (collapse_char' (Xmerge B1_1 B2_1)); intros.
  elim (collapse_char' (Xmerge B1_2 B2_2)); intros.
  destroy a; destroy a0. rename x into B1, x0 into B2, a into HB1, a0 into HB2.
  elim IHB1_1 with B2_1 B1; auto. intros.
  elim IHB1_2 with B2_2 B2; auto. intros.
  clear IHB1_1 IHB1_2.
  1: exists (If b Then x Else x0); rewrite H1, H2; auto.
  all: assert (collapse (XCond b (Xmerge B1_1 B2_1) (Xmerge B1_2 B2_2)) = XUndefined).
  1,3: simpl; rewrite b1; auto.
  1: case collapse; auto.
  clear a. all: clear b1.
  - assert (inject B = collapse (XCond b (Xmerge B1_1 B2_1) (Xmerge B1_2 B2_2))).
    rewrite <- collapse_inject, H0. case Xmerge; case Xmerge; simpl; auto.
    all: intros.
    4: case o, o0; auto. 1,2,3,4,5,6,7: case (collapse x); auto; case (collapse x0); auto.
    elim (inject_not_undefined B). etransitivity; eauto.
  - assert (inject B = collapse (XCond b (Xmerge B1_1 B2_1) (Xmerge B1_2 B2_2))).
    rewrite <- collapse_inject, H0. case Xmerge; case Xmerge; simpl; auto.
    all: intros.
    4: case o, o0; auto. 1,2,3,4,5,6,7: case (collapse x); auto; case (collapse x0); auto.
    elim (inject_not_undefined B). etransitivity; eauto.
+ exists (Call X); auto.
Qed.

Lemma Xmerge_inv_inject' : forall B1 B2 B, Xmerge B1 B2 = inject B ->
  exists B', B2 = inject B'.
Proof.
intros.
apply Xmerge_inv_inject with B1 B.
rewrite Xmerge_comm; auto.
Qed.

Lemma Xmerge_inv : forall B1 B2 B, Xmerge B1 B2 = inject B ->
  exists B'1 B'2, B1 = inject B'1 /\ B2 = inject B'2 /\ merge B'1 B'2 = inject B.
Proof.
intros.
elim (Xmerge_inv_inject _ _ _ H). intros B1' HB1.
elim (Xmerge_inv_inject' _ _ _ H). intros B2' HB2.
exists B1', B2'; repeat split; auto.
unfold merge. rewrite <- HB1, <- HB2; auto.
Qed.

Lemma Xmerge_inv_XCall : forall B B' X,
  Xmerge B B' = XCall X -> B = XCall X.
Proof.
intros.
elim (Xmerge_inv B B' (Call X)); auto.
intros. destroy H0.
elim (merge_inv_Call _ _ _ H0); intros.
rewrite H1, H3; auto.
Qed.

End Merge.

End SPBase.

(* The remaining is stuff from CC that it would be interesting to adapt.


(** Currently not used, but might prove useful. *)

Lemma R_Com_reduce_eq : forall Defs p C v v' q q' x x' s C' s' C'' s'',
  MCC_To Defs C s (R_Com p v q x) C' s' ->
  MCC_To Defs C s (R_Com p v' q' x') C'' s'' ->
  v = v' /\ q = q' /\ x = x'.
Proof.
induction C; intros; try (inversion H; inversion H0); eauto.
+ rewrite <- H1 in H11; inversion H11.
  repeat split.
  * unfold v1, v2. rewrite H23; auto.
  * transitivity q1; auto; transitivity q0; auto.
  * transitivity x1; auto; transitivity x0; auto.
+ rewrite <- H1 in H13; inversion H13.
  destroy H19; exfalso; auto.
+ rewrite <- H9 in H3; inversion H3.
  destroy H19; exfalso; auto.
Qed.

Lemma L_Com_reduce_eq : forall Defs p C v v' q q' s C' s' C'' s'',
  (Build_Program Defs C,s) --[L_Com p v q]--> (Build_Program Defs C', s') ->
  (Build_Program Defs C,s) --[L_Com p v' q']--> (Build_Program Defs C'', s'') ->
  v = v' /\ q = q'.
Proof.
intros.
inversion H; inversion H0.
induction t; try (inversion H5; fail).
induction t0; try (inversion H12; fail).
simpl in H5, H12.
inversion H5; inversion H12.
rewrite H16 in H2; rewrite H19 in H9.
elim (R_Com_reduce_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2 H9); intros.
destroy H22.
split.
+ transitivity v0; auto; transitivity v1; auto.
+ transitivity q0; auto; transitivity q1; auto.
Qed.

Lemma R_Com_reduce_neq : forall Defs p p' C v v' q q' x x' s C' s' C'' s'',
  MCC_To Defs C s (R_Com p v q x) C' s' ->
  MCC_To Defs C s (R_Com p' v' q' x') C'' s'' ->
  p <> p' -> q <> q'.
Proof.
induction C; intros; try (inversion H; inversion H0); eauto.
+ rewrite <- H2 in H12; inversion H12.
  exfalso; apply H1.
  transitivity p0; auto; transitivity p1; auto.
+ rewrite <- H2 in H14; inversion H14.
  destroy H20; destroy H21. rewrite <- H8; auto.
+ rewrite <- H10 in H4; inversion H4.
  destroy H20; destroy H21. rewrite <- H16; auto.
Qed.

Lemma L_Com_reduce_neq : forall Defs p p' C v v' q q' s C' s' C'' s'',
  (Build_Program Defs C,s) --[L_Com p v q]--> (Build_Program Defs C', s') ->
  (Build_Program Defs C,s) --[L_Com p' v' q']--> (Build_Program Defs C'', s'') ->
  p <> p' -> q <> q'.
Proof.
intros.
rename H1 into Hp.
inversion H; inversion H0.
induction t; inversion H5.
induction t0; inversion H12.
rewrite H21, H20, H19 in H9; rewrite H18, H17, H16 in H2.
apply (R_Com_reduce_neq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2 H9); auto.
Qed.

Lemma R_Sel_reduce_eq : forall Defs p C q q' l l' s C' s' C'' s'',
  MCC_To Defs C s (R_Sel p q l) C' s' ->
  MCC_To Defs C s (R_Sel p q' l') C'' s'' ->
  q = q' /\ l = l'.
Proof.
induction C; intros; try (inversion H; inversion H0); eauto.
+ rewrite <- H1 in H10; inversion H10.
  repeat split.
  * transitivity q1; auto; transitivity q0; auto.
  * transitivity l1; auto; transitivity l0; auto.
+ rewrite <- H1 in H12; inversion H12.
  destroy H18; exfalso; auto.
+ rewrite <- H9 in H3; inversion H3.
  destroy H18; exfalso; auto.
Qed.

Lemma L_Sel_reduce_eq : forall Defs p C q q' l l' s C' s' C'' s'',
  (Build_Program Defs C,s) --[L_Sel p q l]--> (Build_Program Defs C', s') ->
  (Build_Program Defs C,s) --[L_Sel p q' l']--> (Build_Program Defs C'', s'') ->
  q = q' /\ l = l'.
Proof.
intros.
inversion H; inversion H0.
induction t; try (inversion H5; fail).
induction t0; try (inversion H12; fail).
simpl in H5, H12.
inversion H5; inversion H12.
rewrite H16 in H2; rewrite H19 in H9.
elim (R_Sel_reduce_eq _ _ _ _ _ _ _ _ _ _ _ _ H2 H9); split.
+ transitivity q0; auto; transitivity q1; auto.
+ transitivity l0; auto; transitivity l1; auto.
Qed.

Lemma R_Sel_reduce_neq : forall Defs p p' C q q' l l' s C' s' C'' s'',
  MCC_To Defs C s (R_Sel p q l) C' s' ->
  MCC_To Defs C s (R_Sel p' q' l') C'' s'' ->
  p <> p' -> q <> q'.
Proof.
induction C; intros; try (inversion H; inversion H0); eauto.
+ rewrite <- H2 in H11; inversion H11.
  exfalso; apply H1.
  transitivity p0; auto; transitivity p1; auto.
+ rewrite <- H2 in H13; inversion H13.
  destroy H20; destroy H19. rewrite <- H7; auto.
+ rewrite <- H10 in H4; inversion H4.
  destroy H20; destroy H19. rewrite <- H15; auto.
Qed.

Lemma L_Sel_reduce_neq : forall Defs p p' C q q' l l' s C' s' C'' s'',
  (Build_Program Defs C,s) --[L_Sel p q l]--> (Build_Program Defs C', s') ->
  (Build_Program Defs C,s) --[L_Sel p' q' l']--> (Build_Program Defs C'', s'') ->
  p <> p' -> q <> q'.
Proof.
intros.
rename H1 into Hp.
inversion H; inversion H0.
induction t; inversion H5.
induction t0; inversion H12.
rewrite H21, H20, H19 in H9; rewrite H18, H17, H16 in H2.
apply (R_Sel_reduce_neq _ _ _ _ _ _ _ _ _ _ _ _ _ H2 H9); auto.
Qed.

End Uniqueness.

(** * Deadlock-freedom by design *)

Theorem progress : forall P, Main P <> End -> MCP_WF P ->
  forall s, exists tl c', (P,s) --[tl]--> c'.
Proof.
induction P.
rename Procedures0 into Ps, Main0 into C.
induction C; intros.
+ simpl in H. elim H; auto.
+ rename r into X; set (ps := fst (Ps X)).
  simpl in H.
  case_eq (set_size_pid ps); [idtac | intros; case_eq n].
  - intro. exfalso.
    unfold ps in H1.
    generalize (MCP_WF_Vars _ H0 X); intros.
    simpl in H2.
    unfold Vars in H2; simpl in H2.
    rewrite (set_size_0 _ _ H1) in H2.
    apply H2; auto.
    red. simpl. auto.
  - intros.
    rewrite H2 in H1; clear H2 n.
    case_eq ps; intros.
    1: { rewrite H2 in H1; inversion H1. }
    unfold ps in H1, H2; clear ps.
    assert (In p (fst (Ps X))). rewrite H2; left; auto.
    do 2 eexists.
    constructor; apply (C_Call_Local' Ps p X); auto.
  - intros.
    rewrite H2 in H1; clear n H2.
    case_eq ps; intros.
    1: { rewrite H2 in H1; inversion H1. }
    unfold ps in H1, H2; clear ps.
    assert (set_size_pid (fst (Ps X)) > 1).
    1: { rewrite H1; auto with arith. }
    assert (In p (fst (Ps X))).
    1: { rewrite H2; left; auto. }
    do 2 eexists.
    constructor; apply (C_Call_Start' Ps p); auto.
+ case_eq (set_size_pid l); intros; [idtac | case_eq n].
  - clear H IHC; exfalso.
    generalize (MCP_WF_Main _ H0).
    simpl; intros.
    inversion_clear H.
    inversion_clear H3.
    elim H; eapply set_size_0; apply H1.
  - intros.
    rewrite H2 in H1; clear n H2.
    case_eq l; intro.
    1: { rewrite H2 in H1; inversion H1. }
    do 2 eexists; constructor.
    apply C_Call_Finish'.
    1: { rewrite <- H2; auto. }
    left; eauto.
  - intros.
    rewrite H2 in H1; clear n H2.
    case_eq l; intro.
    1: { rewrite H2 in H1; inversion H1. }
    do 2 eexists; constructor. apply C_Call_Enter'.
    1: { rewrite <- H2; rewrite H1; auto with arith. }
    left; eauto.
+ case_eq e; do 2 eexists; do 2 constructor; ESEr.
+ case_eq (beval_on_state b s p).
  - do 2 eexists; constructor; apply C_Then'; auto.
  - do 2 eexists; constructor; apply C_Else'; auto.
Qed.

Lemma MCC_To_within_Xs : forall P s l P' s' Xs,
  Program_WF Xs P -> (P,s) --[l]--> (P',s') -> within_Xs Xs (Main P').
Proof.
intros.
revert H.
inversion_clear H0.
simpl; intros.
generalize (Program_WF_within_Xs _ _ H0); intros.
unfold Procs in H1; simpl in H1.
generalize (Program_WF_Main_within_Xs _ _ H0); simpl; intros.
clear H0.
induction H; auto.
+ inversion_clear H2; auto.
+ inversion_clear H2; auto.
+ inversion_clear H2; split; auto.
+ inversion_clear H2. simpl; auto.
+ simpl; auto.
+ inversion_clear H2; auto.
Qed.

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

Lemma MCC_To_MCP_WF : forall P s l P' s',
  MCP_WF P -> (P,s) --[l]--> (P',s') -> MCP_WF P'.
Proof.
intros.
inversion H0.
inversion_clear H.
rename x into Xs; exists Xs; inversion_clear H7.
simpl; split.
rewrite H5.
apply (MCC_To_Program_WF _ _ _ _ _ _ H H0).
rewrite <- H1 in H8.
apply well_ann_Main_change with C; auto.
Qed.

Section BigStepSemantics.

Lemma RT_Call_reduce : forall Defs X ps C s, (ps <> List.nil) ->
  exists tl, (Build_Program Defs (RT_Call X ps C),s) --[tl]-->* (Build_Program Defs C,s).
Proof.
intros.
set (n := set_size_pid ps).
assert (n = set_size_pid ps); auto.
clearbody n; revert ps H H0.
induction n; intros.
+ symmetry in H0; apply set_size_0 in H0. exfalso; auto.
+ case_eq n; intros.
  - rewrite H1 in H0; clear IHn H1 n.
    case_eq ps; intros. rewrite H1 in H; elim H; auto.
    exists (L_Tau p::List.nil)%list.
    econstructor. 2: constructor.
    replace (L_Tau p) with (forget (R_Call X p)); auto.
    constructor. apply C_Call_Finish'; [rewrite <- H1 | simpl]; auto.
  - case_eq ps; intros. rewrite H2 in H; elim H; auto.
    rewrite H1 in H0, IHn; clear n H1; rename n0 into n.
    assert (S n = set_size_pid (set_remove_pid p ps)).
    1: {
      unfold set_size_pid in H0.
      rewrite (set_size_remove' P.eq_dec ps p) in H0; auto.
      rewrite H2; simpl; auto.
    }
    elim (IHn (set_remove_pid p ps)); intros; auto.
    2: { intro. rewrite H3 in H1. simpl in H1; inversion H1. }
    rename x into tls.
    exists (L_Tau p :: tls)%list.
    eapply MCT_Step with (Build_Program Defs (RT_Call X (set_remove_pid p ps) C),s); auto.
    replace (L_Tau p) with (forget (R_Call X p)); auto.
    constructor. rewrite H2; apply C_Call_Enter'.
    rewrite <- H2, <- H0; auto with arith.
    simpl; auto.
Qed.

Lemma Call_reduce : forall (Defs:DefSet) X s, (fst (Defs X) <> List.nil) ->
  exists tl, (Build_Program Defs (Call X),s) --[tl]-->* (Build_Program Defs (snd (Defs X)),s).
Proof.
intros.
case_eq (set_size_pid (fst (Defs X))); intros; [idtac | case_eq n]; intros.
+ exfalso; apply set_size_0 in H0; auto.
+ rewrite H1 in H0; clear n H1.
  case_eq (fst (Defs X)); intros. exfalso; auto.
  exists (L_Tau p::List.nil)%list.
  econstructor. 2: constructor.
  replace (L_Tau p) with (forget (R_Call X p)); auto.
  change (fst (A:=set P.t) (Defs X) = p::l)%list in H1.
  constructor. apply C_Call_Local'; auto. rewrite H1; simpl; auto.
+ rewrite H1 in H0; clear n H1. rename n0 into n.
  case_eq (fst (Defs X)); intros. exfalso; auto.
  assert (set_remove_pid p (fst (Defs X)) <> List.nil).
  1: {
    intro. unfold set_size_pid, set_remove_pid in H0, H2.
    rewrite (set_size_remove' P.eq_dec (fst (Defs X)) p) in H0.
    2: rewrite H1; simpl; auto.
    rewrite H2 in H0. inversion H0.
  }
  elim (RT_Call_reduce Defs X (set_remove_pid p (fst (Defs X))) (snd (Defs X)) s); auto.
  intros.
  exists (L_Tau p :: x)%list.
  eapply MCT_Step; eauto.
  replace (L_Tau p) with (forget (R_Call X p)); auto.
  constructor. apply C_Call_Start'.
  - change (set_size_pid (fst (A:=set P.t) (Defs X)) = S (S n)) in H0.
    rewrite H0; auto with arith.
  - change (fst (A:=set P.t) (Defs X) = p::l)%list in H1.
    rewrite H1; simpl; auto.
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
