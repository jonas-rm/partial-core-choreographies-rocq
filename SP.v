Require Import MC.

Local Open Scope nat_scope.

Module SPBase (P X V E B R:DecType) (Ev:Eval E X V V) (BEv:Eval B X V Bool).

Module Export MCBase := MCBase P X V E B R Ev BEv.

Module Export PSt := LState V X.
Module Export CSt := GState P V X.

Section Syntax.

Inductive Behaviour : Type :=
| End : Behaviour
| Send : Pid -> Expr -> Behaviour -> Behaviour
| Recv : Pid -> Var -> Behaviour -> Behaviour
| Sel : Pid -> Label -> Behaviour -> Behaviour
| Branching : Pid -> (Label -> option Behaviour) -> Behaviour
| Cond : BExpr -> Behaviour -> Behaviour -> Behaviour
| Call : RecVar -> Behaviour
.

Definition Branch : Type := option Behaviour.

(** Equality of behaviours is not decidable because of branching... *)
Lemma Behaviour_eq_End_dec : forall (b:Behaviour), {b=End} + {b<>End}.
Proof.
induction b; auto; right; discriminate.
Qed.

Definition Network := Pid -> Behaviour.

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

Definition Network_eq (N N':Network) : Prop := forall p, N p = N' p.

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

(*
Lemma Network_eq_within_ps_dec : forall ps N N', within_ps ps N -> within_ps ps N' ->
  {Network_eq N N'}+{~Network_eq N N'}.
Proof.
intros.
*)

Definition EmptyNet : Network := fun _ => End.

Lemma EmptyNet_within_ps : forall ps, within_ps ps EmptyNet.
Proof. red; auto. Qed.

Lemma EmptyNet_finite_supp : finite_support EmptyNet.
Proof. exists nil. apply EmptyNet_within_ps. Qed.

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

Lemma Par_assoc : forall N N' N'',
  Network_eq (Par N (Par N' N'')) (Par (Par N N') N'').
Proof.
red; intros.
unfold Par.
do 2 elim Behaviour_eq_End_dec; intros; auto.
elim b; auto.
Qed.

Definition Process (p:Pid) (b:Behaviour) : Network :=
  fun p' => if (P.eq_dec p p') then b else End.

Record Program : Type :=
  { Procedures : RecVar -> Behaviour;
    Net        : Network }.

End Syntax.

Delimit Scope SP_scope with SP.

Bind Scope SP_scope with Behaviour.
Bind Scope SP_scope with Network.

Notation "N | N'" := (Par N N') (at level 202, right associativity) : SP_scope.
Notation "p [ B ]" := (Process p B) (at level 201, no associativity) : SP_scope.
Notation "p ! e ; B" := (Send p e B) (at level 60, e at level 9, right associativity) : SP_scope.
Notation "p ? xx ; B" := (Recv p xx B) (at level 60, right associativity) : SP_scope.
Notation "p (+) l ; B" := (Sel p l B) (at level 49, l at level 9, right associativity) : SP_scope.
Notation "p & f" := (Branching p f) (at level 60, no associativity) : SP_scope.
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

Section SyntacticProperties.

Fixpoint Behaviour_WF (p:Pid) (B:Behaviour) : Prop :=
match B with
| bnil%SP => True
| Call _ => True
| (q ! _; B)%SP => p <> q /\ Behaviour_WF p B
| (q ? _; B)%SP => p <> q /\ Behaviour_WF p B
| (q (+) l; B)%SP => p <> q /\ Behaviour_WF p B
| (q & f)%SP => p <> q /\ (forall l,
    match (f l) with | Some B' => Behaviour_WF p B' | _ => True end)
| (If e Then B1 Else B2)%SP => Behaviour_WF p B1 /\ Behaviour_WF p B2
end.

Fixpoint B_size (B:Behaviour) :=
match B with
| bnil%SP => 0
| Call _ => 0
| (_ ! _; B')%SP => 1 + B_size B'
| (_ ? _; B')%SP => 1 + B_size B'
| (_ (+) _; B')%SP => 1 + B_size B'
| (_ & f)%SP =>
  (match (f left) with | Some B' => B_size B' | _ => 0 end)
  + (match (f right) with | Some B' => B_size B' | _ => 0 end)
  + 1
| (If e Then B1 Else B2)%SP => B_size B1 + B_size B2 + 1
end.

Lemma Behaviour_WF_dec : forall p B,
  {Behaviour_WF p B} + {~Behaviour_WF p B}.
Proof.
assert (forall p p0 B, {Behaviour_WF p B}+{~Behaviour_WF p B} -> {p<>p0 /\ Behaviour_WF p B}+{~(p<>p0 /\ Behaviour_WF p B)}).
+ intros.
  elim (P.eq_dec p p0); intro.
  - right; rewrite a; intro. inversion H0; auto.
  - inversion_clear H; auto.
    right; intro. inversion H; auto.
+ intros.
  set (n := B_size B).
  assert (B_size B <= n); auto.
  clearbody n.
  revert dependent B.
  induction n; intros; induction B; simpl in H; simpl; auto with arith;
    try (exfalso; inversion H; fail).
  - exfalso.
    assert (1<=0).
    2: inversion H0.
    etransitivity; eauto with arith.
  - exfalso.
    inversion H.
    apply (lt_irrefl 0).
    eapply lt_le_trans. 2: apply H. auto with arith.
  - elim (P.eq_dec p p0); intro.
    1: { right; rewrite a; intro. inversion H0; auto. }
    revert H; case_eq (o left); case_eq (o right); simpl; intros.
    * assert (B_size b0 <= n).
      1: { apply le_S_n. etransitivity.
           2: apply H1.
           rewrite plus_comm. auto with arith. }
      assert (B_size b1 <= n).
      1: { apply le_S_n. etransitivity.
           2: apply H1.
           rewrite plus_comm. auto with arith. }
      elim (IHn _ H2); elim (IHn _ H3); intros.
      ++ left; split; auto.
         induction l; try rewrite H; try rewrite H0; auto.
      ++ right; intro; inversion_clear H4.
         generalize (H6 left); rewrite H0; auto.
      ++ right; intro; inversion_clear H4.
         generalize (H6 right); rewrite H; auto.
      ++ right; intro; inversion_clear H4.
         generalize (H6 left); rewrite H0; auto.
    * assert (B_size b0 <= n).
      1: { apply le_S_n. etransitivity.
           2: apply H1.
           rewrite plus_comm. auto with arith. }
      elim (IHn _ H2); intros.
      ++ left; split; auto.
         induction l; try rewrite H; try rewrite H0; auto.
      ++ right; intro; inversion_clear H3.
         generalize (H5 left); rewrite H0; auto.
    * assert (B_size b0 <= n).
      1: { apply le_S_n. etransitivity.
           2: apply H1.
           rewrite plus_comm. auto with arith. }
      elim (IHn _ H2); intros.
      ++ left; split; auto.
         induction l; try rewrite H; try rewrite H0; auto.
      ++ right; intro; inversion_clear H3.
         generalize (H5 right); rewrite H; auto.
    * left; split; auto.
      induction l; try rewrite H; try rewrite H0; auto.
  - assert (B_size B1 <= S n).
      1: { etransitivity.
           2: apply H.
           auto with arith. }
    assert (B_size B2 <= S n).
      1: { etransitivity.
           2: apply H.
           auto with arith. }
    elim IHB1; elim IHB2; intros; auto;
      right; intro; inversion_clear H2; auto.
Qed.

Definition Network_WF (N:Network) : Prop :=
  forall p, Behaviour_WF p (N p).

Lemma Network_WF_dec : forall ps N, within_ps ps N ->
  {Network_WF N} + {~Network_WF N}.
Proof.
intros ps N.
assert (ps<>nil -> {forall p, In p ps -> Behaviour_WF p (N p)} + {~forall p, In p ps -> Behaviour_WF p (N p)}).
+ induction ps; simpl.
  1: right; auto.
  elim (Behaviour_WF_dec a (N a)); intro.
  2: right; auto.
  revert IHps; case ps; intro.
  * left; intros.
    inversion_clear H0; [rewrite <- H1; auto | inversion H1].
  * intros.
    elim IHps; intros; auto.
    3: discriminate.
    1: { left; intros. inversion_clear H0; try rewrite <- H1; auto. }
    right; intro; auto.
+ intros.
  red in H0.
  case_eq ps; intros.
  1: { left; intros. red; intros. rewrite H0; try rewrite H1; simpl; auto. }
  elim H; auto.
  2: rewrite H1; discriminate.
  left; red; intros.
  elim (In_dec P.eq_dec p0 ps); auto.
  intro; rewrite H0; simpl; auto.
Qed.

Lemma Par_WF : forall N N', Network_WF N -> Network_WF N' ->
  Network_WF (N | N').
Proof.
intros; intro.
elim (Behaviour_eq_End_dec (N p)); intro.
1: rewrite Par_proj2; auto.
rewrite Par_proj1; auto.
Qed.

(*
Definition Program_WF (P:Program) := 
  (forall X p, Behaviour_WF p (Procedures P X)) /\
  (forall p, Network_WF (Net p)).

 add within_Xs and decidability *)

(* WF program doesn't make sense.
   But: program with WF network reduces to program with WF network is
   an interesting property that is guaranteed by EPP. *)

End SyntacticProperties.

Section Semantics.

Lemma Network_WF_par : forall N N', Network_disjoint N N' ->
  Network_WF (N | N') -> Network_WF N /\ Network_WF N'.
Proof.
intros.
split; intro.
+ elim (Behaviour_eq_End_dec (N p)); intro.
  1: rewrite a; simpl; auto.
  rewrite <- (Par_proj1 N N'); auto.
+ elim (Behaviour_eq_End_dec (N' p)); intro.
  1: rewrite a; simpl; auto.
  rewrite <- (Par_proj2 N N'); auto.
  elim (Behaviour_eq_End_dec (N p)); auto.
  intro.
  exfalso.
  elim (H p); auto.
Qed.

Lemma Network_WF_comm : forall N N', Network_disjoint N N' ->
  Network_WF (N | N') -> Network_WF (N' | N).
Proof.
intros.
elim (Network_WF_par N N'); intros; auto.
apply Par_WF; auto.
Qed.

Definition Network_eq_upTo (N:Network) ps N' : Prop :=
  forall p, ~In p ps -> N' p = N p.

Inductive SP_To (Procs : RecVar -> Behaviour) :
  Network -> State -> TransitionLabel -> Network -> State -> Prop :=
 | S_Com N N' s p e q x B B':
    N p = (q ! e ; B)%SP -> N q = (p ? x ; B')%SP ->
    N' p = B -> N' q = B' ->
    Network_eq_upTo N (p::q::List.nil) N' ->
    let v := (eval_on_state e s p) in
    SP_To Procs N s (L_Com p v q) N' (update s q x v)
 | S_Sel N N' s p q l B f B':
    N p = (q (+) l ; B)%SP -> N q = (p & f)%SP ->
    f l = Some B' ->
    N' p = B -> N' q = B' ->
    Network_eq_upTo N (p::q::nil) N' ->
    SP_To Procs N s (L_Sel p q l) N' s
 | S_Then N N' s p b B1 B2 :
    N p = (If b Then B1 Else B2)%SP ->
    N' p = B1 -> (beval_on_state b s p = true) ->
    Network_eq_upTo N (p::nil) N' ->
    SP_To Procs N s (L_Tau p) N' s
 | S_Else N N' s p b B1 B2 :
    N p = (If b Then B1 Else B2)%SP ->
    N' p = B2 -> (beval_on_state b s p = false) ->
    Network_eq_upTo N (p::nil) N' ->
    SP_To Procs N s (L_Tau p) N' s
 | S_Call N N' s p X :
    N p = Call X -> N' p = Procs X ->
    Network_eq_upTo N (p::nil) N' ->
    SP_To Procs N s (L_Tau p) N' s.

Definition Configuration : Type := Program * State.

Inductive SPP_To : Configuration -> TransitionLabel -> Configuration -> Prop :=
 | SPP_To_intro Procs N s t N' s' : SP_To Procs N s t N' s' ->
     SPP_To (Build_Program Procs N,s) t (Build_Program Procs N',s').

Inductive SPP_ToStar : Configuration -> list TransitionLabel -> Configuration -> Prop :=
 | SPT_Refl c : SPP_ToStar c nil c
 | SPT_Step c1 t c2 l c3 : SPP_To c1 t c2 -> SPP_ToStar c2 l c3 -> SPP_ToStar c1 (t::l) c3
.

Bind Scope SP_scope with SP_To.
Notation "N --[ l ]--> N'" := (SPP_To N l N') (at level 50, left associativity) : SP_scope.
Notation "N --[ ls ]-->* N'" := (SPP_ToStar N ls N') (at level 50, left associativity) : SP_scope.

End Semantics.

End SPBase.
