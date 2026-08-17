Require Export Common.
Require Export CC.

Local Open Scope nat_scope.

(** Preamble: a lot of things just as in CC. *)

Section SPBase.

Variable Sig : Signature.

Abbreviation Pid := (pid Sig).
Abbreviation Var := (var Sig).
Abbreviation Value := (value Sig).
Abbreviation Expr := (expr Sig).
Abbreviation BExpr := (bexpr Sig).
Abbreviation RecVar := (recvar Sig).
Abbreviation Ann := (ann Sig).
Abbreviation Ev := (ev Sig).
Abbreviation BEv := (bev Sig).

Abbreviation Store := (State Pid Var Value).

(** * Syntax of processes *)

Section Syntax.

(** ** Behaviours *)

Inductive Behaviour : Type :=
| End : Behaviour
| Send : Pid -> Expr -> Ann -> Behaviour -> Behaviour
| Recv : Pid -> Var -> Ann -> Behaviour -> Behaviour
| Sel : Pid -> Label -> Ann -> Behaviour -> Behaviour
| Branching : Pid -> option (Ann*Behaviour) -> option (Ann*Behaviour) -> Behaviour
| Cond : BExpr -> Behaviour -> Behaviour -> Behaviour
| Call : RecVar -> Behaviour
.

(** Induction principles on behaviours. *)

Fixpoint depth (B:Behaviour) : nat :=
match B with
 | Send p e _ B' => 1 + depth B'
 | Recv p x _ B' => 1 + depth B'
 | Sel p l _ B' => 1 + depth B'
 | Branching p mB mB' =>
             1 + (match mB with None => 0 | Some (_,B) => depth B end)
               + (match mB' with None => 0 | Some (_,B) => depth B end)
 | Cond b B1 B2 => 1 + Nat.max (depth B1) (depth B2)
 | Call X => 1
 | End => 1
end.

Theorem Behaviour_ind' :
  forall P:Behaviour -> Prop,
    P End ->
    (forall p e a B, P B -> P (Send p e a B)) ->
    (forall p v a B, P B -> P (Recv p v a B)) ->
    (forall p l a B, P B -> P (Sel p l a B)) ->
    (forall p, P (Branching p None None)) ->
    (forall p a Bl, P Bl -> P (Branching p (Some (a,Bl)) None)) ->
    (forall p a Br, P Br -> P (Branching p None (Some (a,Br)))) ->
    (forall p a Bl a' Br, P Bl -> P Br ->
            P (Branching p (Some (a,Bl)) (Some (a',Br)))) ->
    (forall b B1 B2, P B1 -> P B2 -> P (Cond b B1 B2)) ->
    (forall X, P (Call X)) ->
    forall B, P B.
Proof.
intros; revert B.
assert (forall d B, depth B <= d -> P B).
2: eauto.
induction d; intros; case_eq B; intros; auto; rewrite H10 in H9; try (exfalso; inversion H9; fail); auto with arith.
+ induction o; induction o0; try induction a; try induction a0; auto.
  1: apply H6. 3: apply H4. 4: apply H5.
  all: apply IHd.
  all: simpl in H9; apply le_S_n in H9.
  all: etransitivity; [idtac | apply H9]; auto with arith.
+ apply H7; apply IHd; apply le_S_n in H9.
  - etransitivity. eapply Nat.le_max_l. eauto.
  - etransitivity. eapply Nat.le_max_r. eauto.
Qed.

Theorem Behaviour_rec' :
  forall P:Behaviour -> Type,
    P End ->
    (forall p e a B, P B -> P (Send p e a B)) ->
    (forall p v a B, P B -> P (Recv p v a B)) ->
    (forall p l a B, P B -> P (Sel p l a B)) ->
    (forall p, P (Branching p None None)) ->
    (forall p a Bl, P Bl -> P (Branching p (Some (a,Bl)) None)) ->
    (forall p a Br, P Br -> P (Branching p None (Some (a,Br)))) ->
    (forall p a Bl a' Br, P Bl -> P Br ->
            P (Branching p (Some (a,Bl)) (Some (a',Br)))) ->
    (forall b B1 B2, P B1 -> P B2 -> P (Cond b B1 B2)) ->
    (forall X, P (Call X)) ->
    forall B, P B.
Proof.
intros; revert B.
assert (forall d B, depth B <= d -> P B).
2: eauto.
induction d; intros; case_eq B; intros; auto; rewrite H0 in H; try (exfalso; inversion H; fail); auto with arith.
+ induction o; induction o0; try induction a; try induction a0; auto.
  1: apply X6. 3: apply X4. 4: apply X5.
  all: apply IHd.
  all: simpl in H; apply le_S_n in H.
  all: etransitivity; [idtac | apply H]; auto with arith.
+ apply X7; apply IHd; apply le_S_n in H.
  - etransitivity. eapply Nat.le_max_l. eauto.
  - etransitivity. eapply Nat.le_max_r. eauto.
Qed.

Local Ltac dec_eq t t' H H' :=
  case (eq_dec t t'); [intro H; rewrite <- H | right; intro; inversion H'; auto].

(** Equality of behaviours is decidable. *)

Lemma Behaviour_eq_dec : forall (B B':Behaviour), {B=B'} + {B<>B'}.
Proof.
induction B using Behaviour_rec'; induction B' using Behaviour_rec';
  auto; try (right; discriminate).
1,2,3,4,5,6,7: dec_eq p p0 Hpp0 H.
1: dec_eq e e0 Hee0 H.
2: dec_eq v v0 Hvv0 H.
3: dec_eq l l0 Hll0 H.
9: dec_eq X X0 HXX0 H; auto.
4: auto.
1,2,3,4,5,6: dec_eq a a0 Haa0 H.
6: dec_eq a' a'0 Ha'a'0 H.
1,2,3: elim (IHB B'); intro H'; [left; rewrite H'; auto | right; intro; inversion H; auto].
1,2: elim (IHB B'); intro H'; [left; rewrite H'; auto | right; intro; inversion H; auto].
+ elim (IHB1 B'1); intro H'. 2: right; intro; inversion H; auto.
  elim (IHB2 B'2); intro H''. 2: right; intro; inversion H; auto.
  rewrite H', H''; auto.
+ dec_eq b b0 Hbb0 H.
  elim (IHB1 B'1); intro H'. 2: right; intro; inversion H; auto.
  elim (IHB2 B'2); intro H''. 2: right; intro; inversion H; auto.
  rewrite H', H''; auto.
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
elim (In_dec (@eq_dec Pid) p ps); auto.
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
elim (In_dec (@eq_dec _) p ps); intros.
+ clear H0 H.
  induction ps; simpl; intros; inversion_clear a; apply H1; simpl; auto.
+ rewrite H0; auto.
Qed.

(** Programs in SP are pairs, like choreography programs in CC. *)

Definition DefSetB := RecVar -> Behaviour.

Definition Program : Type := DefSetB * Network.

Definition Procs : Program -> DefSetB := fst.
Definition Net : Program -> Network := snd.

Lemma SP_eta : forall P, P = (Procs P,Net P).
Proof. induction P; auto. Qed.

(** Syntactic constructors for building networks as lists *)

Definition EmptyNet : Network := fun _ => End.

Definition Process (p:Pid) (B:Behaviour) : Network :=
  fun p' => if (eq_dec p' p) then B else End.

Definition Par (N N':Network) :=
  fun p => if (Behaviour_eq_End_dec (N p)) then N' p else N p.

Definition Network_rm (N:Network) (p:Pid) :=
  fun r => if (eq_dec r p) then End else N r.

(* Generalisation to lists of processes. *)

Definition Network_rm_ps (N:Network) (ps:list Pid) :=
  fun r => if (in_dec (@eq_dec Pid) r ps) then End else N r.

Definition Network_res_ps (N:Network) (ps:list Pid) :=
  fun r => if (in_dec (@eq_dec Pid) r ps) then N r else End.

End Syntax.

Add Parametric Relation : Network Network_eq
  reflexivity proved by Network_eq_refl
  symmetry proved by Network_eq_sym
  transitivity proved by Network_eq_trans
  as Network_eq_rel.

(** Pretty-printing rules. For some reason | only works if it is given an invalid level. *)

Declare Scope SP_scope.
Delimit Scope SP_scope with SP.

Bind Scope SP_scope with Behaviour.
Bind Scope SP_scope with Network.

Notation "p ! e @! a ; B" := (Send p e a B)
  (at level 60, e at level 9, right associativity) : SP_scope.
Notation "p ? xx @? a ; B" := (Recv p xx a B)
  (at level 60) : SP_scope.
Notation "p (+) l @+ a ; B" := (Sel p l a B)
  (at level 60, l at level 9) : SP_scope.
Notation "p '&' B1 '//' B2" := (Branching p B1 B2)
  (at level 60, no associativity) : SP_scope.
Notation "'If' e 'Then' B1 'Else' B2" := (Cond e B1 B2)
  (at level 60) : SP_scope.
Notation "'bnil'" := (End) : SP_scope.
Notation "'nnil'" := (EmptyNet) : SP_scope.

Notation "N | N'" := (Par N N') (at level 201, right associativity) : SP_scope.
Notation "p [ B ]" := (Process p B) (at level 40, no associativity) : SP_scope.
Notation "N '\' p" := (Network_rm N p)  (at level 40, no associativity) : SP_scope.
Notation "N (==) N'" := (Network_eq N N') (at level 80) : SP_scope.

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

Lemma Process_refl : forall p B, (p[B]) p = B.
Proof. intros. unfold Process. case eq_dec; tauto. Qed.

Lemma Process_out : forall p B p', p <> p' -> (p[B]) p' = End.
Proof. intros; unfold Process. case eq_dec; auto. intro; elim H; auto. Qed.

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

Lemma Par_assoc : forall N N' N'', (N | (N' | N'')) (==) ((N | N') | N'').
Proof.
red; intros.
unfold Par.
do 2 elim Behaviour_eq_End_dec; intros; auto.
elim b; auto.
Qed.

(** Useful results for networks with two processes. *)

Lemma Par_fst : forall p Bp q Bq, p <> q -> (p[Bp] | q[Bq]) p = Bp.
Proof.
intros. elim (Behaviour_eq_End_dec Bp); intro.
- rewrite a, Par_proj2.
  apply Process_out; auto.
  apply Process_refl; auto.
- rewrite Par_proj1; rewrite Process_refl; auto.
Qed.

Lemma Par_snd : forall p Bp q Bq, p <> q -> (p[Bp] | q[Bq]) q = Bq.
Proof.
intros. rewrite Par_proj2.
apply Process_refl; auto.
apply Process_out; auto.
Qed.

(** Lemmas about subterms. *)

Lemma Send_neq_cont : forall p e a B, p ! e @! a; B <> B.
Proof.
intros; intro.
assert (depth (p!e@!a;B) = depth B). rewrite H; auto.
simpl in H0. apply Nat.nle_succ_diag_l with (depth B).
rewrite <- H0 at 2. auto.
Qed.

Lemma Recv_neq_cont : forall p x a B, p ? x @? a; B <> B.
Proof.
intros; intro.
apply Nat.nle_succ_diag_l with (depth B). rewrite <- H at 2. auto.
Qed.

Lemma Sel_neq_cont : forall p l a B, p (+) l @+ a; B <> B.
Proof.
intros; intro.
apply Nat.nle_succ_diag_l with (depth B). rewrite <- H at 2; auto.
Qed.

Lemma Branching_l_neq_cont : forall p a Bl Br, Branching p (Some (a,Bl)) Br <> Bl.
Proof.
intros; intro.
apply Nat.nle_succ_diag_l with (depth Bl). rewrite <- H at 2; simpl.
auto with arith.
Qed.

Lemma Branching_r_neq_cont : forall p a Bl Br, Branching p Bl (Some (a,Br)) <> Br.
Proof.
intros; intro.
apply Nat.nle_succ_diag_l with (depth Br). rewrite <- H at 2; simpl.
auto with arith.
Qed.

Lemma Then_neq_cont : forall b B1 B2, If b Then B1 Else B2 <> B1.
Proof.
intros; intro.
apply Nat.nle_succ_diag_l with (depth B1). rewrite <- H at 2.
apply le_n_S, Nat.le_max_l.
Qed.

Lemma Else_neq_cont : forall b B1 B2, If b Then B1 Else B2 <> B2.
Proof.
intros; intro.
apply Nat.nle_succ_diag_l with (depth B2). rewrite <- H at 2.
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

Lemma Par_comm : forall N N', Network_disjoint N N' -> (N | N') (==) (N' | N).
Proof.
red; intros.
unfold Par.
do 2 elim Behaviour_eq_End_dec; intros; auto.
+ transitivity End; auto.
+ exfalso.
  elim (H p); auto.
Qed.

Lemma Par_eq : forall N1 N2 N1' N2',
  N1 (==) N1' -> N2 (==) N2' -> (N1 | N2) (==) (N1' | N2').
Proof.
intros; intro.
unfold Par.
rewrite H, H0. auto.
Qed.

(** Properties of removal. *)

Lemma Network_rm_In : forall N p, (N \ p) p = End.
Proof.
intros; unfold Network_rm.
rewrite DecType_eq; auto.
Qed.

Lemma Network_rm_out : forall N p p', p <> p' -> (N \ p) p' = N p'.
Proof.
intros; unfold Network_rm.
rewrite DecType_neq; auto.
Qed.

Lemma Network_rm_add : forall N p, N (==) (N \ p | p[N p]).
Proof.
intros.
red. unfold Network_rm, Process, Par. intro.
case_eq (eq_dec p0 p); intros.
+ rewrite e. elim Behaviour_eq_End_dec; tauto.
+ elim Behaviour_eq_End_dec; auto.
Qed.

Lemma Network_rm_within_ps : forall N p ps,
  within_ps (p::ps) N -> within_ps ps (N \ p).
Proof.
red; intros. unfold Network_rm.
case_eq (eq_dec p0 p); auto.
intros. apply H; auto. intro; apply H0; auto.
inversion_clear H2; auto. elim n; auto.
Qed.

Lemma Network_rm_add_2_p : forall N p q Bp Bq, p <> q ->
  (N \ p \ q | p[Bp] | q[Bq]) p = Bp.
Proof.
intros.
rewrite Par_proj2, Par_fst; auto.
rewrite Network_rm_out, Network_rm_In; auto.
Qed.

Lemma Network_rm_add_2_q : forall N p q Bp Bq, p <> q ->
  (N  \ p \ q | p[Bp] | q[Bq]) q = Bq.
Proof.
intros. rewrite Par_proj2, Par_snd; auto.
apply Network_rm_In; auto.
Qed.

Lemma Network_rm_add_2_out : forall N p q r Bp Bq,
  p <> r -> q <> r -> (N \ p \ q | p[Bp] | q[Bq]) r = N r.
Proof.
intros. elim (Behaviour_eq_End_dec (N r)); intro.
repeat rewrite Par_proj2; try rewrite Process_out; auto.
repeat rewrite Network_rm_out; auto.
rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
Qed.

Lemma Network_rm_eq : forall N N', N (==) N' -> forall p, N \ p (==) N' \ p.
Proof.
red; intros. unfold Network_rm.
case_eq (eq_dec p0 p); auto.
Qed.

Lemma Network_rm_res_ps :
  forall N ps, N (==) (Network_rm_ps N ps | Network_res_ps N ps).
Proof.
intros.
red. unfold Network_rm_ps, Network_res_ps, Par. intro.
case_eq (in_dec (@eq_dec Pid) p ps); intros.
+ elim Behaviour_eq_End_dec; auto.
  intro. contradiction.
+ elim Behaviour_eq_End_dec; auto.
Qed.

(** Rewriting of networks. *)

Lemma Network_eq_cross'' : forall N N1 N2 p q Bp Bq,
  p <> q -> N1 (==) (N \ p | p[Bp]) -> N2 (==) (N \ q | q[Bq]) ->
  (N2 \ p | p[Bp]) (==) (N1 \ q | q[Bq]).
Proof.
intros; intro x.
case (eq_dec x p); intro Hxp. rewrite Hxp.
rewrite Par_proj2, Par_proj1', Process_refl, Network_rm_out, H0, Par_proj2, Process_refl; auto.
1, 3: apply Network_rm_In. apply Process_out; auto.
case (eq_dec x q); intro Hxq. rewrite Hxq.
rewrite Par_proj1', Par_proj2, Process_refl, Network_rm_out, H1, Par_proj2, Process_refl; auto.
1, 2: apply Network_rm_In. apply Process_out; auto.
(* final case *)
rewrite Par_proj1', Par_proj1'. repeat rewrite Network_rm_out; auto.
rewrite H0, H1, Par_proj1', Par_proj1'. repeat rewrite Network_rm_out; auto.
all: rewrite Process_out; auto.
Qed.

(** For a simpler formulation of the next lemmas. *)

Definition disj_3 (p q r:Pid) := p <> q /\ p <> r /\ q <> r.
Definition disj_4 (p q r s:Pid) :=
  p <> q /\ p <> r /\ p <> s /\ q <> r /\ q <> s /\ r <> s.

Local Ltac elim_3 H Hpq Hpr Hqr := destruct H as [Hpq [Hpr Hqr] ].
Local Ltac elim_4 H Hpq Hpr Hps Hqr Hqs Hrs :=
  destruct H as [Hpq [Hpr [Hps [Hqr [Hqs Hrs] ] ] ] ].

Lemma Network_eq_cross' : forall N N1 N2 p q r Bp Bq Br, disj_3 p q r ->
  N1 (==) (N \ p \ q | p[Bp] | q[Bq]) -> N2 (==) (N \ r | r[Br]) ->
  (N2 \ p \ q | p[Bp] | q[Bq]) (==) (N1 \ r | r[Br]).
Proof.
intros; intro x. destroy H.
case (eq_dec x p); intro Hxp. rewrite Hxp.
rewrite Network_rm_add_2_p, Par_proj1', Network_rm_out, H0, Network_rm_add_2_p; auto.
rewrite Process_out; auto.
case (eq_dec x q); intro Hxq. rewrite Hxq.
rewrite Network_rm_add_2_q, Par_proj1', Network_rm_out, H0, Network_rm_add_2_q; auto.
rewrite Process_out; auto.
case (eq_dec x r); intro Hxr. rewrite Hxr.
rewrite Network_rm_add_2_out, Par_proj2, Process_refl, H1, Par_proj2, Process_refl; auto; apply Network_rm_In.
(* final case *)
repeat rewrite Par_proj1'. repeat rewrite Network_rm_out; auto.
rewrite H0, H1. repeat rewrite Par_proj1'. repeat rewrite Network_rm_out; auto.
all: rewrite Process_out; auto.
Qed.

Lemma Network_eq_cross : forall N N1 N2 p q r s Bp Bq Br Bs, disj_4 p q r s ->
  N1 (==) (N \ p \ q | p[Bp] | q[Bq]) -> N2 (==) (N \ r \ s | r[Br] | s[Bs]) ->
  (N2 \ p \ q | p[Bp] | q[Bq]) (==) (N1 \ r \ s | r[Br] | s[Bs]).
Proof.
intros; intro x. destroy H.
case (eq_dec x p); intro Hxp. rewrite Hxp.
rewrite Network_rm_add_2_p, Par_proj1', Network_rm_out, Network_rm_out, H0, Network_rm_add_2_p; auto.
1: rewrite Par_proj1'; rewrite Process_out; auto.
case (eq_dec x q); intro Hxq. rewrite Hxq.
rewrite Network_rm_add_2_q, Par_proj1', Network_rm_out, Network_rm_out, H0, Network_rm_add_2_q; auto.
1: rewrite Par_proj1'; rewrite Process_out; auto.
case (eq_dec x r); intro Hxp0. rewrite Hxp0.
rewrite Network_rm_add_2_p, Par_proj1', Network_rm_out, Network_rm_out, H1, Network_rm_add_2_p; auto.
1: rewrite Par_proj1'; rewrite Process_out; auto.
case (eq_dec x s); intro Hxq0. rewrite Hxq0.
rewrite Network_rm_add_2_q, Par_proj1', Network_rm_out, Network_rm_out, H1, Network_rm_add_2_q; auto.
1: rewrite Par_proj1'; rewrite Process_out; auto.
(* final case *)
repeat rewrite Par_proj1'. repeat rewrite Network_rm_out; auto.
rewrite H0, H1. repeat rewrite Par_proj1'. repeat rewrite Network_rm_out; auto.
all: rewrite Process_out; auto.
Qed.

Lemma Network_eq_within_ps_dec : forall ps N N',
  within_ps ps N -> within_ps ps N' -> { N (==) N' }+{~ (N (==) N') }.
Proof.
induction ps; intros.
+ left. intro. rewrite H, H0; auto.
+ elim (Behaviour_eq_dec (N a) (N' a)); intros.
  2: right; intro; auto.
  elim (IHps (N \ a) (N' \ a)); intros;
  try (apply Network_rm_within_ps; auto).
  - left; intro.
    case (eq_dec p a); intro. rewrite e; auto.
    generalize (a1 p).
    unfold Network_rm; repeat rewrite DecType_neq; auto.
  - right; intro.
    apply b; intro.
    apply Network_rm_eq; auto.
Qed.

(** ** Well-formedness
  Not used too much, since this is guaranteed by EPP.
*)

Fixpoint Behaviour_WF (p:Pid) (B:Behaviour) : Prop :=
match B with
| q ! _ @! _ ; B'        => p <> q /\ Behaviour_WF p B'
| q ? _ @? _ ; B'        => p <> q /\ Behaviour_WF p B'
| q (+) l @+ _; B'       => p <> q /\ Behaviour_WF p B'
| q & B1 // B2           => p <> q
      /\ (match B1 with None => True | Some (_,B) => Behaviour_WF p B end)
      /\ (match B2 with None => True | Some (_,B) => Behaviour_WF p B end)
| (If e Then B1 Else B2) => Behaviour_WF p B1 /\ Behaviour_WF p B2
| Call _                 => True
| End                    => True
end.

Lemma Behaviour_WF_dec : forall p B, {Behaviour_WF p B} + {~Behaviour_WF p B}.
Proof.
induction B using Behaviour_rec'; simpl; auto;
  try elim (eq_dec p p0); tauto.
Qed.

Definition Network_WF (N:Network) : Prop := forall p, Behaviour_WF p (N p).

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
    case (eq_dec p a); intro.
    1: rewrite e; auto.
    generalize (a1 p).
    unfold Network_rm. rewrite DecType_neq; auto.
  - right; intro.
    apply b; intro.
    unfold Network_rm.
    case eq_dec; simpl; auto.
Qed.

Lemma Par_WF : forall N N', Network_WF N -> Network_WF N' -> Network_WF (N | N').
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

(** Program_WF doesn't make sense, because procedures don't know the processes
   that will execute them, so we do not know what to pass to Behaviour_WF.
   But: program with WF network reduces to program with WF network is
   an interesting property that is guaranteed by EPP. *)

End SyntacticProperties.

(** * Semantics of SP *)

Section Semantics.

(** Same strategy as for CC. *)

Inductive SP_To (D : DefSetB) :
  Network -> Store -> (RichLabel Pid Value Var RecVar) -> Network -> Store -> Prop :=
 | S_Com N p e a B q x a' B' N' s s' :
    N p = (q ! e @!a ; B) -> N q = (p ? x @? a'; B') ->
    let v := (eval_on_state Ev e s p) in
    N' (==) (N \ p \ q | p[B] | q[B']) -> s' [==] (s[[q,x => v]]) ->
    SP_To D N s (RL_Com p v q x) N' s'
 | S_LSel N p a B q a' Bl Br N' s s' :
    N p = (q (+) left @+ a ; B) -> N q = (p & Some (a',Bl) // Br) ->
    N' (==) (N \ p \ q | p[B] | q[Bl]) -> s [==] s' ->
    SP_To D N s (RL_Sel p q left) N' s'
 | S_RSel N p a B q a' Bl Br N' s s' :
    N p = (q (+) right @+ a ; B) -> N q = (p & Bl // Some (a',Br)) ->
    N' (==) (N \ p \ q | p[B] | q[Br]) -> s [==] s' ->
    SP_To D N s (RL_Sel p q right) N' s'
 | S_Then N p b B1 B2 N' s s' :
    N p = (If b Then B1 Else B2) ->
    eval_on_state BEv b s p = true ->
    N' (==) (N \ p | p[B1]) -> s [==] s' ->
    SP_To D N s (RL_Cond p) N' s'
 | S_Else N p b B1 B2 N' s s' :
    N p = (If b Then B1 Else B2) ->
    eval_on_state BEv b s p = false ->
    N' (==) (N \ p | p[B2]) -> s [==] s' ->
    SP_To D N s (RL_Cond p) N' s'
 | S_Call N p X N' s s' :
    N p = Call X ->
    N' (==) (N \ p | p[D X]) -> s [==] s' ->
    SP_To D N s (RL_Call X p) N' s'.

Notation "<< N , s >> --[ tl , D ]--> << N' , s' >>" :=
  (SP_To D N s tl N' s') (at level 100) : SP_scope.

(** Default reductions. *)

Lemma S_Com' : forall D N p e a B q x a' B' s,
  N p = (q ! e @! a ; B) -> N q = (p ? x @? a' ; B') ->
  let v := (eval_on_state Ev e s p) in
  <<N,s>> --[RL_Com p v q x,D]--> <<N \ p \ q | p[B] | q[B'],s[[q,x => v]]>>.
Proof. intros. apply S_Com with a B a' B'; auto. reflexivity. ESEr. Qed.

Lemma S_LSel' : forall D N p a B q a' Bl Br s,
  N p = (q (+) left @+ a ; B) -> N q = (p & Some (a',Bl) // Br) ->
  <<N,s>> --[RL_Sel p q left,D]--> <<N \ p \ q | p[B] | q[Bl],s>>.
Proof. intros. apply S_LSel with a B a' Bl Br; auto. reflexivity. ESEr. Qed.

Lemma S_RSel' : forall D N p a B q a' Bl Br s,
  N p = (q (+) right @+ a ; B) -> N q = (p & Bl // Some (a',Br)) ->
  <<N,s>> --[RL_Sel p q right,D]--> <<N \ p \ q | p[B] | q[Br], s>>.
Proof. intros. apply S_RSel with a B a' Bl Br; auto. reflexivity. ESEr. Qed.

Lemma S_Then' : forall D N p b B1 B2 s,
  N p = (If b Then B1 Else B2) -> eval_on_state BEv b s p = true ->
  <<N,s>> --[RL_Cond p,D]--> <<N \ p | p[B1],s>>.
Proof. intros. apply S_Then with b B1 B2; auto. reflexivity. ESEr. Qed.

Lemma S_Else' : forall D N p b B1 B2 s,
  N p = (If b Then B1 Else B2) -> eval_on_state BEv b s p = false ->
  <<N,s>> --[RL_Cond p,D]--> <<N \ p | p[B2],s>>.
Proof. intros. apply S_Else with b B1 B2; auto. reflexivity. ESEr. Qed.

Lemma S_Call' : forall D N p X s, N p = Call X ->
  <<N,s>> --[RL_Call X p,D]--> <<N \ p | p[D X],s>>.
Proof. intros. apply S_Call; auto. reflexivity. ESEr. Qed.

Definition Configuration : Type := Program * Store.

Inductive SPP_To :
  Configuration -> (TransitionLabel Pid Value) -> Configuration -> Prop :=
 | SPP_Base D N s t N' s' : SP_To D N s t N' s' ->
     SPP_To (D,N,s) (forget t) (D,N',s').

Inductive SPP_ToStar :
  Configuration -> list (TransitionLabel Pid Value) -> Configuration -> Prop :=
 | SPT_Base P s s' : s [==] s' -> SPP_ToStar (P,s) nil (P,s')
 | SPT_Step c1 t c2 l c3 : SPP_To c1 t c2 ->
                           SPP_ToStar c2 l c3 -> SPP_ToStar c1 (t::l) c3
.

Lemma SPT_Refl : forall c, SPP_ToStar c nil c.
Proof. induction c. constructor. ESEr. Qed.

End Semantics.

Bind Scope SP_scope with SP_To.

Notation "<< N , s >> --[ tl , D ]--> << N' , s' >>" :=
  (SP_To D N s tl N' s') (at level 100) : SP_scope.
Notation "C --[ l ]--> C'" := (SPP_To C l C')
  (at level 50, left associativity) : SP_scope.
Notation "C --[ ls ]-->* C'" := (SPP_ToStar C ls C')
  (at level 50, left associativity) : SP_scope.

(** ** Results on determinism of the semantics.
  These results are named consistently with CC. *)

Section Determinism.

(** Reductions are preserved by state equivalence... *)

Lemma SP_To_eq : forall D N tl s1 N' s2 s1' s2', s1 [==] s1' -> s2 [==] s2' ->
  <<N,s1>> --[tl,D]--> <<N',s2>> -> <<N,s1'>> --[tl,D]--> <<N',s2'>>.
Proof.
intros.
induction H1.
+ unfold v.
  rewrite (eval_eq _ e s s1'); auto.
  apply S_Com with a B a' B'; auto.
  ESEt s'. ESEs. eESEt.
  rewrite <- (eval_eq _ e s s1'); auto. fold v.
  ESEc; auto.
+ apply S_LSel with a B a' Bl Br; auto. ESEt s. ESEs. ESEt s'.
+ apply S_RSel with a B a' Bl Br; auto. ESEt s. ESEs. ESEt s'.
+ apply S_Then with b B1 B2; auto.
  rewrite <- (eval_eq _ b s); auto.
  ESEt s. ESEs. ESEt s'.
+ apply S_Else with b B1 B2; auto.
  rewrite <- (eval_eq _ b s); auto.
  ESEt s. ESEs. ESEt s'.
+ apply S_Call; auto. ESEt s. ESEs. ESEt s'.
Qed.

Lemma SPP_To_eq : forall P s1 tl P' s2 s1' s2', s1 [==] s1' -> s2 [==] s2' ->
  (P,s1) --[tl]--> (P',s2) -> (P,s1') --[tl]--> (P',s2').
Proof.
intros.
induction P.
inversion H1; constructor.
apply SP_To_eq with s1 s2; auto.
Qed.

Lemma SPP_ToStar_eq : forall P s1 tl P' s2 s1' s2',
  s1 [==] s1' -> s2 [==] s2' ->
  (P,s1) --[tl]-->* (P',s2) -> (P,s1') --[tl]-->* (P',s2').
Proof.
intros P s1 tl; revert P s1.
induction tl; intros.
+ inversion H1. constructor.
  ESEt s2. ESEt s1. ESEs.
+ inversion H1.
  induction c2.
  apply SPT_Step with (a0,b).
  - apply SPP_To_eq with s1 b; auto. ESEr.
  - eapply IHtl; eauto. ESEr.
Qed.

(** ...by network equivalence... *)

Lemma SP_To_Network_eq : forall N1 N' N2 D s s' tl, (N1 (==) N2) ->
  <<N1,s>> --[tl,D]--> <<N',s'>> -> <<N2,s>> --[tl,D]--> <<N',s'>>.
Proof.
intros.
inversion H0.
+ apply S_Com with a B a' B'; auto.
  1, 2: rewrite <- H; auto.
  etransitivity. eauto.
  repeat apply Par_eq. 2,3: reflexivity.
  repeat apply Network_rm_eq; auto.
+ apply S_LSel with a B a' Bl Br; auto.
  1, 2: rewrite <- H; auto.
  etransitivity. eauto.
  repeat apply Par_eq. 2,3: reflexivity.
  repeat apply Network_rm_eq; auto.
+ apply S_RSel with a B a' Bl Br; auto.
  1, 2: rewrite <- H; auto.
  etransitivity. eauto.
  repeat apply Par_eq. 2,3: reflexivity.
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

Lemma SPP_To_Network_eq : forall P1 P1' P2 s s' tl,
  (Net P1 (==) Net P1') -> (Procs P1 = Procs P1') ->
  (P1,s) --[tl]--> (P2,s') -> (P1',s) --[tl]--> (P2,s').
Proof.
intros.
inversion H1.
induction P1' as (D',N1'). simpl in H, H0.
rewrite <- H0, <- H2; simpl. constructor.
apply SP_To_Network_eq with N; auto.
rewrite <- H, <- H2; simpl. reflexivity.
Qed.

Lemma SPP_ToStar_Network_eq : forall P1 P1' P2 s s' tl,
  (Net P1 (==) Net P1') -> (Procs P1 = Procs P1') -> tl <> nil ->
  (P1,s) --[tl]-->* (P2,s') -> (P1',s) --[tl]-->* (P2,s').
Proof.
intros.
inversion H2. rewrite <- H4 in H1. elim H1; auto.
clear tl H6 c3 H7 H2 H1.
induction c2 as (P'',s'').
apply SPT_Step with (P'',s''); auto.
eapply SPP_To_Network_eq; eauto.
Qed.

(** ... and by extensionally equal sets of procedure definitions. *)

Lemma SP_To_Defs_wd : forall D D', (forall X, D X = D' X) ->
  forall N s tl N' s',
  <<N,s>> --[tl,D]--> <<N',s'>> -> <<N,s>> --[tl,D']--> <<N',s'>>.
Proof.
intros. inversion H0.
+ econstructor; eauto.
+ econstructor; eauto.
+ econstructor; eauto.
+ econstructor; eauto.
+ eapply S_Else; eauto.
+ apply S_Call; auto. rewrite <- H; auto.
Qed.

(** The set of procedure definitions never changes. *)

Hypothesis D : DefSetB.

Lemma SPP_To_Defs_stable : forall D' N N' tl s s',
  (D,N,s) --[tl]--> (D',N',s') -> D = D'.
Proof. intros. inversion H. inversion H; auto. Qed.

Lemma SPP_ToStar_Defs_stable : forall D' N N' tl s s',
  (D,N,s) --[tl]-->* (D',N',s') -> D = D'.
Proof.
intros D' N N' tl; revert N N'.
induction tl; intros; inversion H; clear H; auto.
clear c1 c3 H2 H4 t l H0 H1.
induction c2. induction a0.
apply SPP_To_Defs_stable in H3.
rewrite <- H3 in H5.
eauto.
Qed.

(** Reductions and state. *)

Lemma SP_To_disjoint_eval : forall N s tl s' p e N',
  disjoint_p_rl p tl -> <<N,s>> --[tl,D]--> <<N',s'>>  ->
  eval_on_state Ev e s p = eval_on_state Ev e s' p.
Proof.
intros.
induction H0; auto; try (apply eval_eq; auto; fail).
inversion_clear H.
transitivity (eval_on_state Ev e (s[[q,x => v]]) p).
apply eval_neq; auto.
apply eval_eq; ESEs.
Qed.

Lemma SP_To_disjoint_beval : forall N s tl s' p b N',
  disjoint_p_rl p tl -> <<N,s>> --[tl,D]--> <<N',s'>> ->
  eval_on_state BEv b s p = eval_on_state BEv b s' p.
Proof.
intros.
induction H0; auto; try (apply eval_eq; auto; fail).
inversion_clear H.
transitivity (eval_on_state BEv b (s[[q,x => v]]) p).
apply eval_neq; auto.
apply eval_eq; ESEs.
Qed.

Lemma SP_To_disjoint_update : forall N s tl s' p x v N',
  disjoint_p_rl p tl -> <<N,s>> --[tl,D]--> <<N',s'>> ->
  <<N,s[[p,x => v]]>> --[tl,D]--> <<N',s'[[p,x => v]]>>.
Proof.
intros.
induction H0; try (constructor; auto; try ESEc; auto; fail).
+ inversion_clear H.
  unfold v0. rewrite (eval_neq _ e s p0 p x v); auto.
  apply S_Com with a B a' B'; auto.
  rewrite <- (eval_neq _ e s p0 p x v); auto.
  fold v0.
  ESEt (s[[q,x0 => v0]][[p,x => v]]). ESEc; auto.
  apply update_independent; auto.
+ apply S_LSel with a B a' Bl Br; auto. ESEc; auto.
+ apply S_RSel with a B a' Bl Br; auto. ESEc; auto.
+ apply S_Then with b B1 B2; auto.
  rewrite <- eval_neq; auto.
  ESEc; auto.
+ apply S_Else with b B1 B2; auto.
  rewrite <- eval_neq; auto.
  ESEc; auto.
Qed.

(** Determinism of reductions given the label. *)

Lemma SP_To_deterministic_1 : forall N N1 N2 tl s s1 s2,
  <<N,s>> --[tl,D]--> <<N1,s1>> -> <<N,s>> --[tl,D]--> <<N2,s2>> -> N1 (==) N2.
Proof.
induction tl; intros; inversion H; inversion H0.
- rewrite H19 in H7; rewrite H22 in H10.
  inversion H7; inversion H10.
  rewrite H28, H30 in H23.
  etransitivity; eauto. symmetry; auto.
- rewrite H15 in H4; rewrite H18 in H7.
  inversion H4; inversion H7.
  rewrite H25, H27 in H21.
  etransitivity; eauto. symmetry; auto.
- rewrite H15 in H4; inversion H4.
- rewrite H15 in H4; inversion H4.
- rewrite H15 in H4; rewrite H18 in H7.
  inversion H4; inversion H7.
  rewrite H25, H28 in H21.
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
  <<N,s>> --[tl,D]--> <<N1,s1>> -> <<N,s>> --[tl,D]--> <<N2,s2>> -> s1 [==] s2.
Proof.
induction tl; intros; inversion H; inversion H0;
  try (ESEt s; auto; ESEs; fail).
- rewrite H2 in H12; rewrite H14 in H24.
  eESEt. ESEs.
Qed.

Lemma SP_To_deterministic : forall N N1 N2 tl1 tl2 s s1 s2,
  <<N,s>> --[tl1,D]--> <<N1,s1>> -> <<N,s>> --[tl2,D]--> <<N2,s2>> ->
  tl1 = tl2 -> (N1 (==) N2) /\ s1 [==] s2.
Proof.
intros.
rewrite H1 in H; split.
eapply SP_To_deterministic_1; eauto.
eapply SP_To_deterministic_2; eauto.
Qed.

(* This one does not hold...
Lemma SP_To_deterministic_3 : forall N N' tl1 tl2 s s1 s2,
  SP_To D N s tl1 N' s1 -> SP_To D N s tl2 N' s2 ->
  tl1 = tl2.
*)

Ltac diff_assert p q H1 H2 H3 := assert (p <> q) as H1;
  [intro H1; rewrite H1, H2 in H3; inversion H3 | idtac].

Lemma SP_To_deterministic_4 : forall N N' tl1 tl2 s s1 s2,
  <<N,s>> --[tl1,D]--> <<N',s1>> -> <<N,s>> --[tl2,D]--> <<N',s2>> ->
  s1 [==] s2.
Proof.
induction tl1; induction tl2; intros; inversion H; inversion H0;
  try (ESEt s; ESEs; fail).
+ (* Com/Com *)
  case (eq_dec p p0); intro.
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
    rewrite H25, H7 in H26. apply (Send_neq_cont _ _ _ _ H26).
+ (* Com/Left *)
  exfalso.
  diff_assert p p0 Hpq0 H16 H7.
  diff_assert p q0 Hpp0 H19 H7.
  diff_assert p q Hpq H10 H7.
  generalize (H11 p); generalize (H22 p); intros.
  rewrite Network_rm_add_2_p in H25; auto.
  rewrite Network_rm_add_2_out in H24; auto.
  rewrite H24, H7 in H25. apply (Send_neq_cont _ _ _ _ H25).
+ (* Com/Right *)
  exfalso.
  diff_assert p p0 Hpq0 H16 H7.
  diff_assert p q0 Hpp0 H19 H7.
  diff_assert p q Hpq H10 H7.
  generalize (H11 p); generalize (H22 p); intros.
  rewrite Network_rm_add_2_p in H25; auto.
  rewrite Network_rm_add_2_out in H24; auto.
  rewrite H24, H7 in H25. apply (Send_neq_cont _ _ _ _ H25).
+ (* Com/Then *)
  exfalso.
  diff_assert p p0 Hpp0 H14 H7.
  diff_assert p q Hpq H10 H7.
  generalize (H11 p); generalize (H16 p); intros.
  rewrite Par_proj1, Network_rm_out in H22; auto.
  2: rewrite Network_rm_out, H7; auto; discriminate.
  rewrite Network_rm_add_2_p in H23; auto.
  rewrite H22, H7 in H23. apply (Send_neq_cont _ _ _ _ H23).
+ (* Com/Else *)
  exfalso.
  diff_assert p p0 Hpp0 H14 H7.
  diff_assert p q Hpq H10 H7.
  generalize (H11 p); generalize (H16 p); intros.
  rewrite Par_proj1, Network_rm_out in H22; auto.
  2: rewrite Network_rm_out, H7; auto; discriminate.
  rewrite Network_rm_add_2_p in H23; auto.
  rewrite H22, H7 in H23. apply (Send_neq_cont _ _ _ _ H23).
+ (* Com/Call *)
  exfalso.
  diff_assert p p0 Hpp0 H15 H7.
  diff_assert p q Hpq H10 H7.
  generalize (H11 p); generalize (H18 p); intros.
  rewrite Par_proj1, Network_rm_out in H22; auto.
  2: rewrite Network_rm_out, H7; auto; discriminate.
  rewrite Network_rm_add_2_p in H23; auto.
  rewrite H22, H7 in H23. apply (Send_neq_cont _ _ _ _ H23).
+ (* Left/Com *)
  exfalso.
  diff_assert p p0 Hpp0 H18 H4.
  diff_assert p q0 Hpq0 H21 H4.
  diff_assert p q Hpq H7 H4.
  generalize (H10 p); generalize (H22 p); intros.
  rewrite Network_rm_add_2_out in H24; auto.
  rewrite Network_rm_add_2_p in H25; auto.
  rewrite H24, H4 in H25. apply (Sel_neq_cont _ _ _ _ H25).
+ (* Right/Com *)
  exfalso.
  diff_assert p p0 Hpp0 H18 H4.
  diff_assert p q0 Hpq0 H21 H4.
  diff_assert p q Hpq H7 H4.
  generalize (H10 p); generalize (H22 p); intros.
  rewrite Network_rm_add_2_out in H24; auto.
  rewrite Network_rm_add_2_p in H25; auto.
  rewrite H24, H4 in H25. apply (Sel_neq_cont _ _ _ _ H25).
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
  rewrite H23, H19 in H22. apply (Recv_neq_cont _ _ _ _ H22).
Qed.

(** The label alone determines the resulting state. *)

Lemma SP_To_rl_implies_state : forall N1 s tl N1' s1 N2 N2' s2,
  <<N1,s>> --[tl,D]--> <<N1',s1>> -> <<N2,s>> --[tl,D]--> <<N2',s2>> ->
  s1 [==] s2.
Proof.
induction tl; intros; inversion H; inversion H0;
  try (ESEt s; ESEs; fail).
ESEt (s[[q,x => v1]]). ESEs. ESEt (s[[q,x => v2]]).
rewrite H14, H2; ESEr.
Qed.

(** ** Confluence *)

Lemma diamond_SP : forall N s tl1 tl2 N1 N2 s1 s2,
  <<N,s>> --[tl1,D]--> <<N1,s1>> -> <<N,s>> --[tl2,D]--> <<N2,s2>> ->
  tl1 <> tl2 -> exists N' s',
  <<N1,s1>> --[tl2,D]--> <<N',s'>> /\ <<N2,s2>> --[tl1,D]--> <<N',s'>>.
Proof.
induction tl1, tl2; intros; inversion H; inversion H0.
+ (* Com / Com *)
  revert H3 H15 H13 H25; unfold v2, v3; intros.
  clear s'0 H22 N'0 H21 x2 H17 q2 H16 v3 p2 H14 s3 H19 N3 H18.
  clear s' H10 N' H9 x1 H5 q1 H4 v2 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H20 H8.
  1: {
    rewrite <- H4, H23 in H11; inversion H11.
    apply H1. rewrite <- H3, <- H15, Hpp0, H4, H5, H9, H10; auto.
  }
  diff_assert q q0 Hqq0 H23 H11.
  1: {
    rewrite <- H4, H20 in H8; inversion H8.
    apply H1. rewrite <- H3, <- H15, Hqq0, H4, H5, H9, H10; auto.
  }
  diff_assert p q0 Hpq0 H23 H8.
  diff_assert p0 q Hp0q H11 H20.
  diff_assert p q Hpq H11 H8.
  diff_assert p0 q0 Hp0q0 H23 H20.
  assert (eval_on_state Ev e s p = eval_on_state Ev e s2 p); intros.
  1: {
    unfold eval_on_state. apply eval_wd.
    intro; rewrite H25, update_read'; auto.
  }
  assert (eval_on_state Ev e0 s p0 = eval_on_state Ev e0 s1 p0).
  1: {
    unfold eval_on_state. apply eval_wd.
    intro; rewrite H13, update_read'; auto.
  }
  exists (N1 \ p0 \ q0 | p0[B0] | q0[B'0]),
         (s1[[q0,x0 => eval_on_state Ev e0 s1 p0]]); split.
  - rewrite H4; apply S_Com' with a0 a'0.
    * rewrite (H12 p0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H20; discriminate.
    * rewrite (H12 q0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H23; discriminate.
  - rewrite H2; apply S_Com with a B a' B'.
    * rewrite (H24 p). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H8; discriminate.
    * rewrite (H24 q). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H11; discriminate.
    * apply Network_eq_cross with N; repeat split; auto.
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
  exists (N1 \ p0 \ q0 | p0[B0] | q0[Bl]), s1; split.
  - apply S_LSel' with a0 a'0 Br; auto.
    * rewrite (H12 p0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H17; discriminate.
    * rewrite (H12 q0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H20; discriminate.
  - rewrite (eval_eq _ e s s2); auto; apply S_Com with a B a' B'.
    * rewrite (H23 p). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H8; discriminate.
    * rewrite (H23 q). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H11; discriminate.
    * apply Network_eq_cross with N; repeat split; auto.
    * eESEt. rewrite (eval_eq _ e s s2); auto. ESEc; auto.
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
  exists (N1 \ p0 \ q0 | p0[B0] | q0[Br]), s1; split.
  - apply S_RSel' with a0 a'0 Bl; auto.
    * rewrite (H12 p0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H17; discriminate.
    * rewrite (H12 q0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H20; discriminate.
  - rewrite (eval_eq _ e s s2); auto; apply S_Com with a B a' B'.
    * rewrite (H23 p). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H8; discriminate.
    * rewrite (H23 q). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H11; discriminate.
    * apply Network_eq_cross with N; repeat split; auto.
    * eESEt. rewrite (eval_eq _ e s s2); auto. ESEc; auto.
+ (* Then / Com *)
  revert H3 H13; unfold v1; intros.
  clear s'0 H22 N'0 H21 p2 H14 s3 H19 N3 H18.
  clear s' H10 N' H9 x0 H5 q0 H4 v1 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H15 H8.
  diff_assert p0 q Hp0q H11 H15.
  diff_assert p q Hpq H11 H8.
  exists (N1 \ p0 | p0[B1]), s1; split.
  - apply S_Then' with b B2.
    * rewrite (H12 p0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H15; discriminate.
    * rewrite (eval_eq _ b s1 (s[[q,x => eval_on_state Ev e s p]])); auto.
      rewrite <- eval_neq; auto.
  - rewrite (eval_eq _ e s s2); auto; apply S_Com with a B a' B'.
    * rewrite (H17 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H8; discriminate.
    * rewrite (H17 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H11; discriminate.
    * symmetry. apply Network_eq_cross' with N; repeat split; auto.
    * rewrite <- (eval_eq _ e s s2); auto. eESEt; ESEc; auto.
+ (* Else / Com *)
  revert H3 H13; unfold v1; intros.
  clear s'0 H22 N'0 H21 p2 H14 s3 H19 N3 H18.
  clear s' H10 N' H9 x0 H5 q0 H4 v1 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H15 H8.
  diff_assert p0 q Hp0q H11 H15.
  diff_assert p q Hpq H11 H8.
  exists (N1 \ p0 | p0[B2]), s1; split.
  - apply S_Else' with b B1.
    * rewrite (H12 p0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H15; discriminate.
    * rewrite (eval_eq _ b s1 (s[[q,x => eval_on_state Ev e s p]])); auto.
      rewrite <- eval_neq; auto.
  - rewrite (eval_eq _ e s s2); auto; apply S_Com with a B a' B'.
    * rewrite (H17 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H8; discriminate.
    * rewrite (H17 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H11; discriminate.
    * symmetry. apply Network_eq_cross' with N; repeat split; auto.
    * rewrite <- (eval_eq _ e s s2); auto. eESEt; ESEc; auto.
+ (* Call / Com *)
  revert H3 H13; unfold v1; intros.
  clear s'0 H21 N'0 H20 p2 H15 X0 H14 s3 H18 N3 H17.
  clear s' H10 N' H9 x0 H5 q0 H4 v1 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H16 H8.
  diff_assert p0 q Hp0q H11 H16.
  diff_assert p q Hpq H11 H8.
  exists (N1 \ p0 | p0[D X]), s1; split.
  - apply S_Call'.
    rewrite (H12 p0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all:rewrite H16; discriminate.
  - rewrite (eval_eq _ e s s2); auto; apply S_Com with a B a' B'.
    * rewrite (H19 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H8; discriminate.
    * rewrite (H19 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H11; discriminate.
    * symmetry. apply Network_eq_cross' with N; repeat split; auto.
    * rewrite <- (eval_eq _ e s s2); auto. eESEt; ESEc; auto.
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
  - rewrite (eval_eq _ e s s1); auto; apply S_Com with a0 B0 a'0 B'.
    * rewrite (H11 p0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H19; discriminate.
    * rewrite (H11 q0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H22; discriminate.
    * apply Network_eq_cross with N; repeat split; auto.
    * eESEt. rewrite (eval_eq _ e s s1); auto. ESEc; auto.
  - apply S_LSel' with a a' Br; auto.
    * rewrite (H23 p). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H5; discriminate.
    * rewrite (H23 q). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H8; discriminate.
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
  - rewrite (eval_eq _ e s s1); auto; apply S_Com with a0 B0 a'0 B'.
    * rewrite (H11 p0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H19; discriminate.
    * rewrite (H11 q0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H22; discriminate.
    * apply Network_eq_cross with N; repeat split; auto.
    * eESEt. rewrite (eval_eq _ e s s1); auto. ESEc; auto.
  - apply S_RSel' with a a' Bl; auto.
    * rewrite (H23 p). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H5; discriminate.
    * rewrite (H23 q). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H8; discriminate.
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
  exists (N1 \ p0 \ q0 | p0[B0] | q0[Bl0]), s1; split.
  - apply S_LSel' with a0 a'0 Br0; auto.
    * rewrite (H11 p0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H16; discriminate.
    * rewrite (H11 q0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H19; discriminate.
  - apply S_LSel with a B a' Bl Br; auto.
    * rewrite (H22 p). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H5; discriminate.
    * rewrite (H22 q). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H8; discriminate.
    * apply Network_eq_cross with N; repeat split; auto.
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
  exists (N1 \ p0 \ q0 | p0[B0] | q0[Br0]), s1; split.
  - apply S_RSel' with a0 a'0 Bl0; auto.
    * rewrite (H11 p0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H16; discriminate.
    * rewrite (H11 q0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H19; discriminate.
  - apply S_LSel with a B a' Bl Br; auto.
    * rewrite (H22 p). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H5; discriminate.
    * rewrite (H22 q). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H8; discriminate.
    * apply Network_eq_cross with N; repeat split; auto.
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
  exists (N1 \ p0 \ q0 | p0[B0] | q0[Bl0]), s1; split.
  - apply S_LSel' with a0 a'0 Br0; auto.
    * rewrite (H11 p0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H16; discriminate.
    * rewrite (H11 q0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H19; discriminate.
  - apply S_RSel with a B a' Bl Br; auto.
    * rewrite (H22 p). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H5; discriminate.
    * rewrite (H22 q). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H8; discriminate.
    * apply Network_eq_cross with N; repeat split; auto.
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
  exists (N1 \ p0 \ q0 | p0[B0] | q0[Br0]), s1; split.
  - apply S_RSel' with a0 a'0 Bl0; auto.
    * rewrite (H11 p0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H16; discriminate.
    * rewrite (H11 q0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H19; discriminate.
  - apply S_RSel with a B a' Bl Br; auto.
    * rewrite (H22 p). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H5; discriminate.
    * rewrite (H22 q). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H8; discriminate.
    * apply Network_eq_cross with N; repeat split; auto.
    * ESEt s; ESEs.
+ (* Then / Left *)
  clear s'0 H21 N'0 H20 p2 H13 s3 H18 N3 H17.
  clear s' H10 N' H9 H4 q0 H3 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H14 H5.
  diff_assert p0 q Hp0q H8 H14.
  diff_assert p q Hpq H8 H5.
  exists (N1 \ p0 | p0[B1]), s1; split.
  - apply S_Then' with b B2.
    * rewrite (H11 p0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H14; discriminate.
    * rewrite (eval_eq _ b s1 s); auto. ESEs.
  - apply S_LSel with a B a' Bl Br; auto.
    * rewrite (H16 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H5; discriminate.
    * rewrite (H16 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H8; discriminate.
    * symmetry. apply Network_eq_cross' with N; repeat split; auto.
    * eESEt; ESEs.
+ (* Else / Left *)
  clear s'0 H21 N'0 H20 p2 H13 s3 H18 N3 H17.
  clear s' H10 N' H9 H4 q0 H3 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H14 H5.
  diff_assert p0 q Hp0q H8 H14.
  diff_assert p q Hpq H8 H5.
  exists (N1 \ p0 | p0[B2]), s1; split.
  - apply S_Else' with b B1.
    * rewrite (H11 p0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H14; discriminate.
    * rewrite (eval_eq _ b s1 s); auto. ESEs.
  - apply S_LSel with a B a' Bl Br; auto.
    * rewrite (H16 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H5; discriminate.
    * rewrite (H16 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H8; discriminate.
    * symmetry. apply Network_eq_cross' with N; repeat split; auto.
    * eESEt; ESEs.
+ (* Then / Right *)
  clear s'0 H21 N'0 H20 p2 H13 s3 H18 N3 H17.
  clear s' H10 N' H9 H4 q0 H3 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H14 H5.
  diff_assert p0 q Hp0q H8 H14.
  diff_assert p q Hpq H8 H5.
  exists (N1 \ p0 | p0[B1]), s1; split.
  - apply S_Then' with b B2.
    * rewrite (H11 p0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H14; discriminate.
    * rewrite (eval_eq _ b s1 s); auto. ESEs.
  - apply S_RSel with a B a' Bl Br; auto.
    * rewrite (H16 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H5; discriminate.
    * rewrite (H16 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H8; discriminate.
    * symmetry. apply Network_eq_cross' with N; repeat split; auto.
    * eESEt; ESEs.
+ (* Else / Right *)
  clear s'0 H21 N'0 H20 p2 H13 s3 H18 N3 H17.
  clear s' H10 N' H9 H4 q0 H3 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H14 H5.
  diff_assert p0 q Hp0q H8 H14.
  diff_assert p q Hpq H8 H5.
  exists (N1 \ p0 | p0[B2]), s1; split.
  - apply S_Else' with b B1.
    * rewrite (H11 p0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H14; discriminate.
    * rewrite (eval_eq _ b s1 s); auto. ESEs.
  - apply S_RSel with a B a' Bl Br; auto.
    * rewrite (H16 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H5; discriminate.
    * rewrite (H16 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H8; discriminate.
    * symmetry. apply Network_eq_cross' with N; repeat split; auto.
    * eESEt; ESEs.
+ (* Call / Left *)
  clear s'0 H20 N'0 H19 p2 H14 X0 H13 s3 H17 N3 H16.
  clear s' H10 N' H9 H4 q0 H3 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H15 H5.
  diff_assert p0 q Hp0q H8 H15.
  diff_assert p q Hpq H8 H5.
  exists (N1 \ p0 | p0[D X]), s1; split.
  - apply S_Call'.
    rewrite (H11 p0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
    all:rewrite H15; discriminate.
  - apply S_LSel with a B a' Bl Br; auto.
    * rewrite (H18 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H5; discriminate.
    * rewrite (H18 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H8; discriminate.
    * symmetry. apply Network_eq_cross' with N; repeat split; auto.
    * eESEt; ESEs.
+ (* Call / Right *)
  clear s'0 H20 N'0 H19 p2 H14 X0 H13 s3 H17 N3 H16.
  clear s' H10 N' H9 H4 q0 H3 p1 H2 s0 H7 N0 H6.
  diff_assert p p0 Hpp0 H15 H5.
  diff_assert p0 q Hp0q H8 H15.
  diff_assert p q Hpq H8 H5.
  exists (N1 \ p0 | p0[D X]), s1; split.
  - apply S_Call'.
    rewrite (H11 p0). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
    all: rewrite H15; discriminate.
  - apply S_RSel with a B a' Bl Br; auto.
    * rewrite (H18 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H5; discriminate.
    * rewrite (H18 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H8; discriminate.
    * symmetry. apply Network_eq_cross' with N; repeat split; auto.
    * eESEt; ESEs.
+ (* Com / Then *)
  revert H12 H22; unfold v1; intros.
  diff_assert p p0 Hpp0 H17 H3.
  diff_assert p0 q Hp0q H20 H17.
  diff_assert p q Hpq H20 H3.
  exists (Network_rm N2 p | p[B1]), s2; split.
  - rewrite (eval_eq _ e s s1); auto; apply S_Com with a B a' B'.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H17; discriminate.
    * rewrite (H5 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H20; discriminate.
    * symmetry; apply Network_eq_cross' with N; repeat split; auto.
    * rewrite <- (eval_eq _ e s s1); auto. eESEt; ESEc; auto.
  - apply S_Then' with b B2.
    * rewrite (H21 p). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H3; discriminate.
    * rewrite (eval_eq _ b s2 (s[[q,x => eval_on_state Ev e s p0]])); auto.
      rewrite <- eval_neq; auto.
+ (* Com / Else *)
  revert H12 H22; unfold v1; intros.
  diff_assert p p0 Hpp0 H17 H3.
  diff_assert p0 q Hp0q H20 H17.
  diff_assert p q Hpq H20 H3.
  exists (Network_rm N2 p | p[B2]), s2; split.
  - rewrite (eval_eq _ e s s1); auto; apply S_Com with a B a' B'.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H17; discriminate.
    * rewrite (H5 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H20; discriminate.
    * symmetry; apply Network_eq_cross' with N; repeat split; auto.
    * rewrite <- (eval_eq _ e s s1); auto. eESEt; ESEc; auto.
  - apply S_Else' with b B1.
    * rewrite (H21 p). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H3; discriminate.
    * rewrite (eval_eq _ b s2 (s[[q,x => eval_on_state Ev e s p0]])); auto.
      rewrite <- eval_neq; auto.
+ (* Left / Then *)
  diff_assert p p0 Hpp0 H14 H3.
  diff_assert p0 q Hp0q H17 H14.
  diff_assert p q Hpq H17 H3.
  exists (Network_rm N2 p | p[B1]), s2; split.
  - apply S_LSel with a B a' Bl Br; auto.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H14; discriminate.
    * rewrite (H5 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H17; discriminate.
    * symmetry. apply Network_eq_cross' with N; repeat split; auto.
    * eESEt; ESEs.
  - apply S_Then' with b B2.
    * rewrite (H20 p). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H3; discriminate.
    * rewrite (eval_eq _ b s2 s); auto. ESEs.
+ (* Right / Then *)
  diff_assert p p0 Hpp0 H14 H3.
  diff_assert p0 q Hp0q H17 H14.
  diff_assert p q Hpq H17 H3.
  exists (Network_rm N2 p | p[B1]), s2; split.
  - apply S_RSel with a B a' Bl Br; auto.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H14; discriminate.
    * rewrite (H5 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H17; discriminate.
    * symmetry. apply Network_eq_cross' with N; repeat split; auto.
    * eESEt; ESEs.
  - apply S_Then' with b B2.
    * rewrite (H20 p). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H3; discriminate.
    * rewrite (eval_eq _ b s2 s); auto. ESEs.
+ (* Left / Else *)
  diff_assert p p0 Hpp0 H14 H3.
  diff_assert p0 q Hp0q H17 H14.
  diff_assert p q Hpq H17 H3.
  exists (Network_rm N2 p | p[B2]), s2; split.
  - apply S_LSel with a B a' Bl Br; auto.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H14; discriminate.
    * rewrite (H5 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H17; discriminate.
    * symmetry. apply Network_eq_cross' with N; repeat split; auto.
    * eESEt; ESEs.
  - apply S_Else' with b B1.
    * rewrite (H20 p). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H3; discriminate.
    * rewrite (eval_eq _ b s2 s); auto. ESEs.
+ (* Right / Else *)
  diff_assert p p0 Hpp0 H14 H3.
  diff_assert p0 q Hp0q H17 H14.
  diff_assert p q Hpq H17 H3.
  exists (Network_rm N2 p | p[B2]), s2; split.
  - apply S_RSel with a B a' Bl Br; auto.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H14; discriminate.
    * rewrite (H5 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H17; discriminate.
    * symmetry. apply Network_eq_cross' with N; repeat split; auto.
    * eESEt; ESEs.
  - apply S_Else' with b B1.
    * rewrite (H20 p). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H3; discriminate.
    * rewrite (eval_eq _ b s2 s); auto. ESEs.
+ (* Then / Then *)
  assert (p <> p0) as Hpp0. intro Hpp0; elim H1; rewrite Hpp0; auto.
  exists (N1 \ p0 | p0[B0]), s1; split.
  - apply S_Then' with b0 B3; auto.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H12; discriminate.
    * rewrite (eval_eq _ b0 s1 s); auto. ESEs.
  - apply S_Then with b B1 B2; auto.
    * rewrite (H14 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H3; discriminate.
    * rewrite (eval_eq _ b s2 s); auto. ESEs.
    * apply Network_eq_cross'' with N; auto.
    * eESEt; ESEs.
+ (* Else / Then *)
  assert (p <> p0) as Hpp0. intro Hpp0; elim H1; rewrite Hpp0; auto.
  exists (N1 \ p0 | p0[B3]), s1; split.
  - apply S_Else' with b0 B0; auto.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H12; discriminate.
    * rewrite (eval_eq _ b0 s1 s); auto. ESEs.
  - apply S_Then with b B1 B2; auto.
    * rewrite (H14 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H3; discriminate.
    * rewrite (eval_eq _ b s2 s); auto. ESEs.
    * apply Network_eq_cross'' with N; auto.
    * eESEt; ESEs.
+ (* Then / Else *)
  assert (p <> p0) as Hpp0. intro Hpp0; elim H1; rewrite Hpp0; auto.
  exists (N1 \ p0 | p0[B0]), s1; split.
  - apply S_Then' with b0 B3; auto.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H12; discriminate.
    * rewrite (eval_eq _ b0 s1 s); auto. ESEs.
  - apply S_Else with b B1 B2; auto.
    * rewrite (H14 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H3; discriminate.
    * rewrite (eval_eq _ b s2 s); auto. ESEs.
    * apply Network_eq_cross'' with N; auto.
    * eESEt; ESEs.
+ (* Else / Else *)
  assert (p <> p0) as Hpp0. intro Hpp0; elim H1; rewrite Hpp0; auto.
  exists (N1 \ p0 | p0[B3]), s1; split.
  - apply S_Else' with b0 B0; auto.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H12; discriminate.
    * rewrite (eval_eq _ b0 s1 s); auto. ESEs.
  - apply S_Else with b B1 B2; auto.
    * rewrite (H14 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H3; discriminate.
    * rewrite (eval_eq _ b s2 s); auto. ESEs.
    * apply Network_eq_cross'' with N; auto.
    * eESEt; ESEs.
+ (* Call / Then *)
  diff_assert p p0 Hpp0 H13 H3.
  exists (N1 \ p0 | p0[D X]), s1; split.
  - apply S_Call'; auto.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H13; discriminate.
  - apply S_Then with b B1 B2; auto.
    * rewrite (H16 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H3; discriminate.
    * rewrite (eval_eq _ b s2 s); auto. ESEs.
    * apply Network_eq_cross'' with N; auto.
    * eESEt; ESEs.
+ (* Call / Else *)
  diff_assert p p0 Hpp0 H13 H3.
  exists (N1 \ p0 | p0[D X]), s1; split.
  - apply S_Call'; auto.
    * rewrite (H5 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H13; discriminate.
  - apply S_Else with b B1 B2; auto.
    * rewrite (H16 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H3; discriminate.
    * rewrite (eval_eq _ b s2 s); auto. ESEs.
    * apply Network_eq_cross'' with N; auto.
    * eESEt; ESEs.
+ (* Com / Call *)
  revert H12 H22; unfold v1; intros.
  diff_assert p p0 Hpp0 H17 H4.
  diff_assert p q Hpq H20 H4.
  diff_assert p0 q Hp0q H20 H17.
  exists (Network_rm N2 p | p[D X]), s2; split.
  - rewrite (eval_eq _ e s s1); auto; apply S_Com with a B a' B'.
    * rewrite (H7 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H17; discriminate.
    * rewrite (H7 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H20; discriminate.
    * symmetry; apply Network_eq_cross' with N; repeat split; auto.
    * rewrite <- (eval_eq _ e s s1); auto. eESEt; ESEc; auto.
  - apply S_Call'.
    * rewrite (H21 p). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H4; discriminate.
+ (* Left / Call *)
  diff_assert p p0 Hpp0 H14 H4.
  diff_assert p q Hpq H17 H4.
  diff_assert p0 q Hp0q H17 H14.
  exists (Network_rm N2 p | p[D X]), s2; split.
  - apply S_LSel with a B a' Bl Br; auto.
    * rewrite (H7 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H14; discriminate.
    * rewrite (H7 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H17; discriminate.
    * symmetry; apply Network_eq_cross' with N; repeat split; auto.
    * eESEt; ESEs; auto.
  - apply S_Call'.
    * rewrite (H20 p). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H4; discriminate.
+ (* Right / Call *)
  diff_assert p p0 Hpp0 H14 H4.
  diff_assert p q Hpq H17 H4.
  diff_assert p0 q Hp0q H17 H14.
  exists (Network_rm N2 p | p[D X]), s2; split.
  - apply S_RSel with a B a' Bl Br; auto.
    * rewrite (H7 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H14; discriminate.
    * rewrite (H7 q), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H17; discriminate.
    * symmetry; apply Network_eq_cross' with N; repeat split; auto.
    * eESEt; ESEs; auto.
  - apply S_Call'.
    * rewrite (H20 p). repeat rewrite Par_proj1; repeat rewrite Network_rm_out; auto.
      all: rewrite H4; discriminate.
+ (* Then / Call *)
  diff_assert p p0 Hpp0 H12 H4.
  exists (Network_rm N2 p | p[D X]), s2; split.
  - apply S_Then with b B1 B2; auto.
    * rewrite (H7 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H12; discriminate.
    * rewrite (eval_eq _ b s1 s); auto. ESEs.
    * apply Network_eq_cross'' with N; auto.
    * eESEt; ESEs.
  - apply S_Call'; auto.
    * rewrite (H14 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H4; discriminate.
+ (* Else / Call *)
  diff_assert p p0 Hpp0 H12 H4.
  exists (Network_rm N2 p | p[D X]), s2; split.
  - apply S_Else with b B1 B2; auto.
    * rewrite (H7 p0), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H12; discriminate.
    * rewrite (eval_eq _ b s1 s); auto. ESEs.
    * apply Network_eq_cross'' with N; auto.
    * eESEt; ESEs.
  - apply S_Call'; auto.
    * rewrite (H14 p), Par_proj1; rewrite Network_rm_out; auto.
      rewrite H4; discriminate.
+ (* Call / Call *)
  assert (p <> p0) as Hpp0. intro Hpp0.
  elim (eq_dec X X0); intro.
  1: apply H1; rewrite Hpp0, a; auto.
  apply b. rewrite <- Hpp0, H4 in H13; inversion H13; auto.
  exists (Network_rm N1 p0 | p0[D X0]), s1; split.
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

(** Useful generalizations *)

Lemma SPP_To_deterministic_1 : forall P s tl P' s' P'' s'',
  (P,s) --[tl]--> (P',s') -> (P,s) --[tl]--> (P'',s'') ->
  Net P' (==) Net P''.
Proof.
intros.
induction P as (D,N), P' as (D',N'), P'' as (D'',N'').
inversion H; inversion H0. simpl.
assert (t = t0).
+ clear s'1 H16 N'1 H15 s1 H12 N1 H11 D1 H9 s'0 H8 N'0 H7 s0 H4 N0 H3 D0 H1 H H0.
  rewrite <- H14 in H13; rewrite <- H6 in H5. clear D' D'' H6 H14.
  rewrite <- H10 in H2; clear tl H10. rename t0 into t'.
  induction H5; induction H13; try discriminate; inversion H2; auto.
  - rewrite <- H11, H0 in H5; inversion H5. auto.
  - rewrite <- H8, H in H4. discriminate.
  - rewrite <- H8, H in H4. discriminate.
  - rewrite <- H8, H in H3. discriminate.
  - rewrite <- H8, H in H3. discriminate.
  - rewrite <- H7, H in H3; inversion H3. auto.
+ rewrite <- H17 in H13.
  eapply SP_To_deterministic_1; eauto.
  rewrite <- H6, H14; eauto.
Qed.

Lemma SPP_To_deterministic_2 : forall P s tl P' s' P'' s'',
  (P,s) --[tl]--> (P',s') -> (P,s) --[tl]--> (P'',s'') -> s' [==] s''.
Proof.
intros.
induction P as (D,N), P' as (D',N'), P'' as (D'',N'').
inversion H; inversion H0. simpl.
assert (t = t0).
+ clear s'1 H16 N'1 H15 s1 H12 N1 H11 D1 H9 s'0 H8 N'0 H7 s0 H4 N0 H3 D0 H1 H H0.
  rewrite <- H14 in H13; rewrite <- H6 in H5. clear D' D'' H6 H14.
  rewrite <- H10 in H2; clear tl H10. rename t0 into t'.
  induction H5; induction H13; try discriminate; inversion H2; auto.
  - rewrite <- H11, H0 in H5; inversion H5. auto.
  - rewrite <- H8, H in H4. discriminate.
  - rewrite <- H8, H in H4. discriminate.
  - rewrite <- H8, H in H3. discriminate.
  - rewrite <- H8, H in H3. discriminate.
  - rewrite <- H7, H in H3; inversion H3. auto.
+ rewrite <- H17 in H13.
  eapply SP_To_deterministic_2; eauto.
  rewrite <- H6, H14; eauto.
Qed.

Lemma SPP_To_deterministic : forall P s tl P' s' P'' s'',
  (P,s) --[tl]--> (P',s') -> (P,s) --[tl]--> (P'',s'') ->
  (Net P' (==) Net P'') /\ Procs P' = Procs P'' /\ s' [==] s''.
Proof.
repeat split.
+ eapply SPP_To_deterministic_1; eauto.
+ transitivity (Procs P). symmetry.
  induction P, P'. eapply SPP_To_Defs_stable; eauto.
  induction P, P''. eapply SPP_To_Defs_stable; eauto.
+ eapply SPP_To_deterministic_2; eauto.
Qed.

Lemma SPP_ToStar_deterministic_1 : forall P s tl P' s' P'' s'',
  (P,s) --[tl]-->* (P',s') -> (P,s) --[tl]-->* (P'',s'')
  -> Net P' (==) Net P''.
Proof.
intros P s tl; revert P s.
induction tl; intros; inversion H; inversion H0.
+ rewrite <- H2, H7; reflexivity.
+ induction c2; induction c4.
  generalize (SPP_To_deterministic_1 _ _ _ _ _ _ _ H4 H10); intro.
  generalize (SPP_To_deterministic_2 _ _ _ _ _ _ _ H4 H10); intro.
  apply SPP_To_eq with (s1':=s) (s2':=b) in H10. 2: ESEr. 2: ESEs.
  case_eq tl.
  - intro. rewrite H15 in H12, H6; inversion H6; inversion H12.
    rewrite <- H22, <- H17; auto.
  - intros. apply IHtl with a1 b s' s''; auto.
    apply SPP_ToStar_Network_eq with a0; auto.
    rewrite (SP_eta P), (SP_eta a0) in H4.
    rewrite (SP_eta P), (SP_eta a1) in H10.
    rewrite <- (SPP_To_Defs_stable _ _ _ _ _ _ _ H4).
    rewrite <- (SPP_To_Defs_stable _ _ _ _ _ _ _ H10); auto.
    rewrite H15; discriminate.
    apply SPP_ToStar_eq with b0 s''; auto.
    ESEs. ESEr.
Qed.

End SPBase.

Declare Scope SP_scope.
Delimit Scope SP_scope with SP.

Bind Scope SP_scope with Behaviour.
Bind Scope SP_scope with Network.

Notation "p ! e @! a ; B" := (Send _ p e a B)
  (at level 60, e at level 9, right associativity) : SP_scope.
Notation "p ? xx @? a ; B" := (Recv _ p xx a B)
  (at level 60, right associativity) : SP_scope.
Notation "p (+) l @+ a ; B" := (Sel _ p l a B)
  (at level 49, l at level 9, right associativity) : SP_scope.
Notation "p '&' B1 '//' B2" := (Branching _ p B1 B2)
  (at level 60, no associativity) : SP_scope.
Notation "'If' e 'Then' B1 'Else' B2" := (Cond _ e B1 B2)
  (at level 60) : SP_scope.
Notation "'bnil'" := (End _) : SP_scope.
Notation "'nnil'" := (EmptyNet _) : SP_scope.

Notation "<< N , s >> --[ tl , D ]--> << N' , s' >>" :=
  (SP_To _ D N s tl N' s') (at level 100) : SP_scope.
Notation "C --[ l ]--> C'" := (SPP_To _ C l C')
  (at level 50, left associativity) : SP_scope.
Notation "C --[ ls ]-->* C'" := (SPP_ToStar _ C ls C')
  (at level 50, left associativity) : SP_scope.

Notation "N | N'" := (Par _ N N') (at level 202, right associativity) : SP_scope.
Notation "p [ B ]" := (Process _ p B) (at level 201, no associativity) : SP_scope.
Notation "N \ p" := (Network_rm _ N p)  (at level 50, no associativity) : SP_scope.
Notation "N (==) N'" := (Network_eq _ N N') (at level 80) : SP_scope.

Arguments Net [Sig].
Arguments Procs [Sig].

(** Tactics for proofs by induction. *)

Ltac BInduction B := induction B using Behaviour_ind'.
Ltac BDInduction B B' := induction B using Behaviour_ind'; induction B' using Behaviour_ind'.

Ltac elim_as mB p := case mB; try induction p.
Ltac opt_elim b p := case_eq b; repeat induction p.

(** Tactics for network equality. *)

Ltac NEQr := apply Network_eq_refl.
Ltac NEQs := apply Network_eq_sym; auto.
Ltac NEQt N := apply Network_eq_trans with N; auto.
