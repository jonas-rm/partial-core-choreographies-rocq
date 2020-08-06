Require Export Common.
Require Import MC.

Local Open Scope nat_scope.

Module SPBase (P X V E B R:DecType) (Ev:Eval E X V V) (BEv:Eval B X V Bool).

Module Export PSt := LState V X.
Module Export CSt := GState P V X.
Module Export TL := TransitionLabels P V X R.

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

(** ** These things should be somehow shared with MC. *)

(** Expression evaluation on the state of a process *)

Definition eval_on_state (e:Expr) (s:State) (p:Pid) : Value := eval e (s p).
Definition beval_on_state (b:BExpr) (s:State) (p:Pid) : bool := beval b (s p).

(** Consistency with state equivalence. *)
Lemma eval_eq : forall e s s' p, eq_state_ext s s' ->
  eval_on_state e s p = eval_on_state e s' p.
Proof.
intros; unfold eval_on_state; simpl.
apply Ev.eval_wd.
apply H.
Qed.

Lemma eval_neq : forall e s p q x v, p <> q ->
  eval_on_state e s p = eval_on_state e (update s q x v) p.
Proof.
intros; unfold eval_on_state; simpl.
replace (s p) with (update s q x v p); auto.
unfold update.
case_eq (Pid_dec q p); auto.
intro; elim H.
apply Pdec.eqb_eq in H0; auto.
Qed.

Lemma beval_eq : forall b s s' p, eq_state_ext s s' ->
  beval_on_state b s p = beval_on_state b s' p.
Proof.
intros; unfold beval_on_state; simpl.
apply BEv.eval_wd.
apply H.
Qed.

Lemma beval_neq : forall b s p q x v, p <> q ->
  beval_on_state b s p = beval_on_state b (update s q x v) p.
Proof.
intros; unfold beval_on_state; simpl.
replace (s p) with (update s q x v p); auto.
unfold update.
case_eq (Pid_dec q p); auto.
intro; elim H.
apply Pdec.eqb_eq in H0; auto.
Qed.

(** * Syntax of processes *)

Section Syntax.

(** ** Behaviours *)

Inductive Behaviour : Type :=
| End : Behaviour
| Send : Pid -> Expr -> Behaviour -> Behaviour
| Recv : Pid -> Var -> Behaviour -> Behaviour
| Sel : Pid -> Label -> Behaviour -> Behaviour
| Branching : Pid -> list (Label * Behaviour) -> Behaviour
| Cond : BExpr -> Behaviour -> Behaviour -> Behaviour
| Call : RecVar -> Behaviour
.

Definition Cases := list (Label*Behaviour).

(** Informally, we think of [Branching] as a partial function from labels to 
  behaviours. There are several possible ways of formalizing this; the choice we
  make corresponds closely to the notation in choreography papers - there is a
  well-formedness assumption that no label occurs twice in the list. *)

(** In order to do induction on behaviours, WTF?????? *)

Fixpoint depth (B:Behaviour) : nat :=
match B with
 | Send p e B' => 1 + depth B'
 | Recv p x B' => 1 + depth B'
 | Sel p l B' => 1 + depth B'
 | Branching p c => 1 + list_max (map (fun p => match p with (_,B') => depth B' end) c)
 | Cond b B1 B2 => 1 + Nat.max (depth B1) (depth B2)
 | Call X => 1
 | End => 1
end.

Theorem Behaviour_ind' :
  forall P:Behaviour -> Prop,
    P End ->
    (forall (p:Pid) (e:Expr) (B:Behaviour), P B -> P (Send p e B)) ->
    (forall (p:Pid) (v:Var) (B:Behaviour), P B -> P (Recv p v B)) ->
    (forall (p:Pid) (l:Label) (B:Behaviour), P B -> P (Sel p l B)) ->
    (forall (p:Pid) (c:Cases), (forall (l:Label) (B:Behaviour), In (l,B) c -> P B) -> P (Branching p c)) ->
    (forall (b:BExpr) (B1 B2:Behaviour), P B1 -> P B2 -> P (Cond b B1 B2)) ->
    (forall (X:RecVar), P (Call X)) ->
    forall B:Behaviour, P B.
Proof.
intros.
revert B.
assert (forall d B, depth B <= d -> P B).
2: eauto.
induction d; intros; case_eq B; intros; auto; rewrite H7 in H6; try (exfalso; inversion H6; fail); auto with arith.
+ clear H H0 H1 H2 H4 H5 H7 B.
  apply H3.
  intros; apply IHd.
  simpl in H6. apply le_S_n in H6.
  rewrite list_max_le, Forall_forall in H6.
  apply in_map with (f:=fun p:Label*Behaviour => let (_,B):=p in depth B) in H.
  auto.
+ apply H4; apply IHd; simpl in H; apply le_S_n in H6.
  - etransitivity. eapply Nat.le_max_l. eauto.
  - etransitivity. eapply Nat.le_max_r. eauto.
Qed.

Theorem Behaviour_rec' :
  forall P:Behaviour -> Type,
    P End ->
    (forall (p:Pid) (e:Expr) (B:Behaviour), P B -> P (Send p e B)) ->
    (forall (p:Pid) (v:Var) (B:Behaviour), P B -> P (Recv p v B)) ->
    (forall (p:Pid) (l:Label) (B:Behaviour), P B -> P (Sel p l B)) ->
    (forall (p:Pid) (c:Cases), (forall (l:Label) (B:Behaviour), In (l,B) c -> P B) -> P (Branching p c)) ->
    (forall (b:BExpr) (B1 B2:Behaviour), P B1 -> P B2 -> P (Cond b B1 B2)) ->
    (forall (X:RecVar), P (Call X)) ->
    forall B:Behaviour, P B.
Proof.
intros.
revert B.
assert (forall d B, depth B <= d -> P B).
2: eauto.
induction d; intros; case_eq B; intros; auto; rewrite H0 in H; try (exfalso; inversion H; fail); auto with arith.
+ apply X3.
  intros; apply IHd.
  simpl in H. apply le_S_n in H.
  rewrite list_max_le, Forall_forall in H.
  apply in_map with (f:=fun p:Label*Behaviour => let (_,B):=p in depth B) in H1.
  auto.
+ apply X4; apply IHd; simpl in H; apply le_S_n in H.
  - etransitivity. eapply Nat.le_max_l. eauto.
  - etransitivity. eapply Nat.le_max_r. eauto.
Defined.

(** Equality of behaviours is decidable. We are using the fact that equality on labels is decidable. *)
Lemma Behaviour_eq_dec : forall (B B':Behaviour), {B=B'} + {B<>B'}.
Proof.
induction B using Behaviour_rec'; induction B' using Behaviour_rec'; auto;
  try (right; discriminate).
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
  assert ({c=c0}+{c<>c0}).
  - clear e X0 p0. revert c X; induction c0; intros.
    case c; auto. right; discriminate.
    case_eq c. right; discriminate.
    intros. induction p0. rename a0 into l1, b into B1.
    induction a. rename a into l2, b into B2.
    case (eq_label_dec l1 l2); intros.
    2: right; intro; inversion H0; auto.
    elim (X l1 B1) with B2; intros.
    2: right; intro; inversion H0; auto.
    2: rewrite H; simpl; auto.
    elim (IHc0 l); intros.
    2: right; intro; inversion H0; auto.
    rewrite e, a, a0; auto.
    apply X with l0. rewrite H; right; auto.
  - inversion_clear H.
    2: right; intro; inversion H; auto.
    rewrite e, H0; auto.
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
Proof. intros; apply Behaviour_eq_dec. Qed.

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

(** Syntactic constructors for building networks as lists *)

Definition EmptyNet : Network := fun _ => End.

Lemma EmptyNet_within_ps : forall ps, within_ps ps EmptyNet.
Proof. red; auto. Qed.

Lemma EmptyNet_finite_supp : finite_support EmptyNet.
Proof. exists nil. apply EmptyNet_within_ps. Qed.

Definition Process (p:Pid) (B:Behaviour) : Network :=
  fun p' => if (Pid_dec p' p) then B else End.

Definition Par (N N':Network) :=
  fun p => if (Behaviour_eq_End_dec (N p)) then N' p else N p.

Lemma Par_proj1 : forall N N' p, N p <> End -> Par N N' p = N p.
Proof.
intros.
unfold Par. elim Behaviour_eq_End_dec; auto.
intro. elim H; auto.
Qed.

Lemma Par_proj2 : forall N N' p, N p = End -> Par N N' p = N' p.
Proof.
intros.
unfold Par. elim Behaviour_eq_End_dec; auto.
intro. elim b; auto.
Qed.

Lemma Par_assoc : forall N N' N'',
  Network_eq (Par N (Par N' N'')) (Par (Par N N') N'').
Proof.
red; intros.
unfold Par.
do 2 elim Behaviour_eq_End_dec; intros; auto.
elim b; auto.
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
  Network_eq (Par N N') (Par N' N).
Proof.
red; intros.
unfold Par.
do 2 elim Behaviour_eq_End_dec; intros; auto.
+ transitivity End; auto.
+ exfalso.
  elim (H p); auto.
Qed.

(** We can also remove a process from a network. *)

Definition Network_rm (N:Network) (p:Pid) :=
  fun r => if (Pid_dec r p) then End else N r.

Lemma Network_rm_add :
  forall N p, Network_eq N (Par (Network_rm N p) (Process p (N p))).
Proof.
intros.
red. unfold Network_rm, Process, Par. intro.
case_eq (Pid_dec p0 p); intros.
+ rewrite Pdec.eqb_eq in H. rewrite H.
  elim Behaviour_eq_End_dec; auto.
  intro H'. contradiction.
+ elim Behaviour_eq_End_dec; auto.
Qed.

Lemma Network_rm_eq : forall N N', Network_eq N N' ->
  forall p, Network_eq (Network_rm N p) (Network_rm N' p).
Proof.
red; intros. unfold Network_rm.
case_eq (Pid_dec p0 p); auto.
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

(* Generalisation of the above to lists of processes. *)

Definition Network_rm_ps (N:Network) (ps:list Pid) :=
  fun r => if (in_dec P.eq_dec r ps) then End else N r.

Definition Network_res_ps (N:Network) (ps:list Pid) :=
  fun r => if (in_dec P.eq_dec r ps) then N r else End.

Lemma Network_rm_res_ps :
  forall N ps, Network_eq N (Par (Network_rm_ps N ps) (Network_res_ps N ps)).
Proof.
intros.
red. unfold Network_rm_ps, Network_res_ps, Par. intro.
case_eq (in_dec P.eq_dec p ps); intros.
+ elim Behaviour_eq_End_dec; auto.
  intro. contradiction.
+ elim Behaviour_eq_End_dec; auto.
Qed.

(** This construction makes the following lemma easier to prove. *)
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

(** Programs in SP are pairs, like choreography programs in MC. *)

Definition DefSetB := RecVar -> Behaviour.

Record Program : Type :=
  { Procedures : DefSetB;
    Net        : Network }.

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

Notation "N | N'" := (Par N N') (at level 202, right associativity) : SP_scope.
Notation "p [ B ]" := (Process p B) (at level 201, no associativity) : SP_scope.
Notation "p ! e ; B" := (Send p e B) (at level 60, e at level 9, right associativity) : SP_scope.
Notation "p ? xx ; B" := (Recv p xx B) (at level 60, right associativity) : SP_scope.
Notation "p (+) l ; B" := (Sel p l B) (at level 49, l at level 9, right associativity) : SP_scope.
Notation "p '&' c" := (Branching p c) (at level 60, no associativity) : SP_scope.
Notation "'If' e 'Then' B1 'Else' B2" := (Cond e B1 B2) (at level 60) : SP_scope.
Notation "'bnil'" := (End) : SP_scope.
Notation "'nnil'" := (EmptyNet) : SP_scope.

(*
These do not work - we now have parameters everywhere.
Check (EmptyNet | EmptyNet)%SP.
Check (0 [1, bnil])%SP.
Check (Empty | 0 [1, bnil])%SP.
Check (If 0 Then bnil Else bnil)%SP.
Check (0!zero; 0?; 1+left; bnil)%SP.
*)

(** ** Syntactic properties *)

Section SyntacticProperties.

(* Equivalence of processes - where?
Fixpoint Behaviour_equiv (B1 B2:Behaviour) : Prop :=
match B1, B2 with
| bnil%SP, bnil%SP => True
| Call X, Call Y   => X = Y
| (p ! e; B)%SP, (p' ! e'; B')%SP => p = p' /\ e = e' /\ Behaviour_equiv B B'
| (p ? x; B)%SP, (p' ? x'; B')%SP => p = p' /\ x = x' /\ Behaviour_equiv B B'
| (p (+) l; B)%SP, (p' (+) l'; B')%SP => p = p' /\ l = l' /\ Behaviour_equiv B B'
| (p & f)%SP, (p' & f')%SP => p = p' /\ (forall l, OptionBehaviour_equiv (f l) (f' l))
| (If e Then Bt Else Be)%SP, (If e' Then Bt' Else Be')%SP => e = e' /\ Behaviour_equiv Bt Bt' /\ Behaviour_equiv Be Be'
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

(**
  We do not know whether we need well-formedness of processes yet.
  Well-formedness does not check that, in branchings, all labels are distinct.
*)

Fixpoint Behaviour_WF (p:Pid) (B:Behaviour) : Prop :=
match B with
| bnil%SP => True
| Call _ => True
| (q ! _; B')%SP => p <> q /\ Behaviour_WF p B'
| (q ? _; B')%SP => p <> q /\ Behaviour_WF p B'
| (q (+) l; B')%SP => p <> q /\ Behaviour_WF p B'
| (q & c)%SP => p <> q /\ fold_right and True (map (fun case => match case with (_, B') => Behaviour_WF p B' end) c)
| (If e Then B1 Else B2)%SP => Behaviour_WF p B1 /\ Behaviour_WF p B2
end.

Lemma Behaviour_WF_dec : forall p B,
  {Behaviour_WF p B} + {~Behaviour_WF p B}.
Proof.
induction B using Behaviour_rec'; simpl; auto;
  try (elim (P.eq_dec p p0); intro; [idtac | inversion_clear IHB; auto];
  right; intro H'; inversion_clear H'; auto).
+ assert ({fold_right and True (map (fun case : Label * Behaviour => let (_, B) := case in Behaviour_WF p B) c)} +
  {~ (fold_right and True (map (fun case : Label * Behaviour => let (_, B) := case in Behaviour_WF p B) c))}).
  - induction c; simpl; auto.
    induction a.
    elim (X a b); simpl; auto.
    2: right; intro H'; inversion_clear H'; auto.
    intro.
    elim IHc; auto.
    1: right; intro H'; inversion_clear H'; auto.
    intros. apply X with l; simpl; auto.
  - elim H.
    2: right; intro H'; inversion_clear H'; auto.
    elim (P.eq_dec p p0); auto.
    right; intro H'; inversion_clear H'; auto.
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

(** Same strategy as for MC. *)

Inductive SP_To (Defs : DefSetB) :
  Network -> State -> RichLabel -> Network -> State -> Prop :=
 | S_Com N p e B q x B' N' s s' :
    N p = (q ! e ; B)%SP -> N q = (p ? x ; B')%SP ->
    let v := (eval_on_state e s p) in
    Network_eq N' ((Network_rm (Network_rm N p) q) | p[B] | q[B']) ->
    eq_state_ext s' (update s q x v) ->
    SP_To Defs N s (R_Com p v q x) N' s'
 | S_Sel N p l B q c B' N' s s' :
    N p = (q (+) l ; B)%SP -> N q = (p & c)%SP -> In (l, B') c ->
    Network_eq N' ((Network_rm (Network_rm N p) q) | p[B] | q[B']) ->
    eq_state_ext s s' ->
    SP_To Defs N s (R_Sel p q l) N' s'
 | S_Then N p b B1 B2 N' s s' :
    N p = (If b Then B1 Else B2)%SP ->
    beval_on_state b s p = true ->
    Network_eq N' ((Network_rm N p) | p[B1]) ->
    eq_state_ext s s' ->
    SP_To Defs N s (R_Cond p) N' s'
 | S_Else N p b B1 B2 N' s s' :
    N p = (If b Then B1 Else B2)%SP ->
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
  N p = (q ! e ; B)%SP -> N q = (p ? x ; B')%SP ->
  let v := (eval_on_state e s p) in
  SP_To Defs N s (R_Com p v q x) ((Network_rm (Network_rm N p) q) | p[B] | q[B']) (update s q x v).
Proof. intros. apply S_Com with B B'; auto. reflexivity. ESEr. Qed.

Lemma S_Sel' : forall Defs N p l B q c B' s,
  N p = (q (+) l ; B)%SP -> N q = (p & c)%SP -> In (l, B') c ->
  SP_To Defs N s (R_Sel p q l) ((Network_rm (Network_rm N p) q) | p[B] | q[B']) s.
Proof. intros. apply S_Sel with B c B'; auto. reflexivity. ESEr. Qed.

Lemma S_Then' : forall Defs N p b B1 B2 s,
  N p = (If b Then B1 Else B2)%SP ->
  beval_on_state b s p = true ->
  SP_To Defs N s (R_Cond p) ((Network_rm N p) | p[B1]) s.
Proof. intros. apply S_Then with b B1 B2; auto. reflexivity. ESEr. Qed.

Lemma S_Else' : forall Defs N p b B1 B2 s,
  N p = (If b Then B1 Else B2)%SP ->
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

(** ** Determinism
  A process is deterministic if every branching term contains at most
  one behaviour for each label. A network is deterministic if every
  process in it is deterministic.
*)

Fixpoint deterministic_B (B:Behaviour) : Prop :=
match B with
| bnil%SP => True
| Call _ => True
| (_ ! _; B')%SP => deterministic_B B'
| (_ ? _; B')%SP => deterministic_B B'
| (_ (+) _; B')%SP => deterministic_B B'
| (_ & c)%SP => NoDup (map fst c) /\
    fold_right and True (map (fun case => match case with (_, B') => deterministic_B B' end) c)
| (If e Then B1 Else B2)%SP => deterministic_B B1 /\ deterministic_B B2
end.

Lemma deterministic_B_dec : forall B, {deterministic_B B} + {~deterministic_B B}.
Proof.
induction B using Behaviour_rec'; simpl; auto.
+ elim (ListDec.NoDup_dec eq_label_dec (map fst c)); intro Hc.
  2: right; intro H'; apply Hc; inversion_clear H'; auto.
  assert ({fold_right and True (map (fun case : Label * Behaviour => let (_, B) := case in deterministic_B B) c)} +
  {~ (fold_right and True (map (fun case : Label * Behaviour => let (_, B) := case in deterministic_B B) c))}).
  - induction c; simpl; auto.
    induction a.
    elim (X a b); simpl; auto.
    2: right; intro H'; inversion_clear H'; auto.
    intro.
    elim IHc; auto.
    1: right; intro H'; inversion_clear H'; auto.
    intros. apply X with l; simpl; auto.
    inversion Hc; auto.
  - elim H; auto.
    right; intro H'; inversion_clear H'; auto.
+ inversion_clear IHB1.
  2: right; intro H'; inversion_clear H'; auto.
  inversion_clear IHB2; auto.
  right; intro H'; inversion_clear H'; auto.
Qed.

Definition deterministic_N (N:Network) : Prop :=
  forall p, deterministic_B (N p).

Lemma deterministic_N_dec : forall ps N, within_ps ps N ->
  {deterministic_N N} + {~deterministic_N N}.
Proof.
induction ps; simpl; intros.
+ left; intro; rewrite H; simpl; auto.
+ elim (deterministic_B_dec (N a)); intro.
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

Definition deterministic_D (D:DefSetB) : Prop :=
  forall X, deterministic_B (D X).

Definition deterministic_P (P:Program) : Prop :=
  (deterministic_D (Procedures P)) /\ deterministic_N (Net P).

(** Many aspects of the semantics are deterministic anyway. *)

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
+ apply S_Sel with B c B'; auto. ESEt s. ESEs. ESEt s'.
+ apply S_Then with b B1 B2; auto.
  rewrite <- (beval_eq b s); auto.
  ESEt s. ESEs. ESEt s'.
+ apply S_Else with b B1 B2; auto.
  rewrite <- (beval_eq b s); auto.
  ESEt s. ESEs. ESEt s'.
+ apply S_Call; auto. ESEt s. ESEs. ESEt s'.
Qed.

Open Scope SP_scope.

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

(** Others explicitly depend on the program being deterministic. *)

End Determinism.

End SPBase.
