Require Export Basic.
Require Export Common.

Local Open Scope nat_scope.

(** * The general type of MC choreographies
  This type is parameterized over sets of process identifiers,
  values, expressions and recursion variables. *)

Module MCBase (P X V E B R: DecType) (Ev:Eval E X V V) (BEv:Eval B X V Bool).

Module Export PSt := LState V X.
Module Export CSt := GState P V X.

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

Definition Store := CSt.State.

(** ** Syntax of MC choreographies. *)

Section Syntax.

(** Communication actions. *)

Inductive Eta : Type :=
 | Com : Pid -> Expr -> Pid -> Var -> Eta
 | Sel : Pid -> Pid -> Label -> Eta
.

Lemma eta_eq_dec : forall (eta eta':Eta), { eta = eta' } + { eta <> eta' }.
Proof.
decide equality; try apply P.eq_dec.
+ apply X.eq_dec.
+ apply E.eq_dec.
+ decide equality.
Qed.

(** Choreographies. *)

Inductive Choreography : Type :=
 | End         : Choreography
 | Call        : RecVar -> Choreography
 | RT_Call     : RecVar -> (list Pid) -> Choreography -> Choreography
 | Interaction : Eta -> Choreography -> Choreography
 | Cond        : Pid -> BExpr -> Choreography -> Choreography -> Choreography
.

(** A program is a pair containing all procedure definitions and the main
    choreography. *)

Record Program : Type :=
  { Procedures : RecVar -> (list Pid)*Choreography;
    Main       : Choreography }.

Definition Vars := fun P X => fst (Procedures P X).
Definition Procs := fun P X => snd (Procedures P X).

End Syntax.

(** Pretty-printing rules for choreographies. *)

Delimit Scope MC_scope with MC.

Bind Scope MC_scope with Choreography.
Bind Scope MC_scope with Eta.

Notation "p # e --> q $ x" := (Com p e q x) (at level 50, e at level 9) : MC_scope.
Notation "p --> q [ l ]" := (Sel p q l) (at level 50) : MC_scope.
Notation "eta ';;' C" := (Interaction eta C) (at level 60, right associativity) : MC_scope.
Notation "'If' p '?' b 'Then' C1 'Else' C2" := (Cond p b C1 C2) (at level 60).

Section Syntactic_Properties.

(** Syntactic properties of choreographies and programs. *)

Lemma chor_eq_dec : forall (C C':Choreography), { C = C' } + { C <> C' }.
Proof.
decide equality.
+ apply R.eq_dec.
+ apply list_eq_dec.
  apply P.eq_dec.
+ apply R.eq_dec.
+ apply eta_eq_dec.
+ apply B.eq_dec.
+ apply P.eq_dec.
Qed.

(** An initial choreography is what a programmer should write. *)
Fixpoint initial (C:Choreography) : Prop :=
match C with
| End              => True
| Call _           => True
| RT_Call _ _ _    => False
| Interaction _ C' => initial C'
| Cond _ _ C1 C2   => initial C1 /\ initial C2
end.

Lemma initial_dec : forall C, {initial C}+{~initial C}.
Proof.
induction C; simpl; auto.
inversion_clear IHC1; inversion_clear IHC2; auto;
  right; intro; inversion_clear H1; auto.
Qed.

(** Free procedure names in a choreography. *)
Definition set_union_rv := set_union R.eq_dec.

Fixpoint Free_RecVar (C:Choreography) : list RecVar :=
match C with
| End              => nil
| Call Y           => (Y::nil)
| RT_Call Y _ C'   => set_union_rv (Y::nil) (Free_RecVar C')
| Interaction _ C' => Free_RecVar C'
| Cond _ _ C1 C2   => set_union_rv (Free_RecVar C1) (Free_RecVar C2)
end.

Definition X_Free (X:RecVar) (C:Choreography) : Prop :=
  In X (Free_RecVar C).

Lemma X_Free_dec : forall X C, {X_Free X C}+{~X_Free X C}.
Proof.
induction C; unfold X_Free; simpl; auto.
+ elim (R.eq_dec X r); simpl; auto.
  right; intro. inversion_clear H; auto.
+ unfold set_union_rv. simpl.
  inversion_clear IHC.
  - left. apply set_union_intro2; auto.
  - elim (R.eq_dec X r); simpl; intro.
    * left. rewrite a. apply set_union_intro1; simpl; auto.
    * right; intro.
      elim (set_union_elim _ _ _ _ H0); auto.
      simpl. intro. inversion_clear H1; auto.
+ inversion_clear IHC1; [idtac | inversion_clear IHC2].
  - left. apply set_union_intro1; auto.
  - left. apply set_union_intro2; auto.
  - right; intro.
    elim (set_union_elim _ _ _ _ H1); auto.
Qed.

(** Inversion results for bound variables. *)

Lemma X_Free_Eta : forall X eta C,
  X_Free X (eta;;C) -> X_Free X C.
Proof.
intros. apply H.
Qed.

Lemma set_union_elim : forall A A_dec (a:A) (x y:set A),
  In a (set_union A_dec x y) -> {In a x} + {In a y}.
Proof.
induction y.
+ left; simpl; auto.
+ elim (A_dec a a0).
  - right. rewrite a1; simpl; auto.
  - intros; elim IHy; auto.
    right; simpl; auto.
    simpl in H.
    elim (set_add_elim _ _ _ _ H); auto.
    intros; elim b; auto.
Qed.

Lemma X_Free_Cond : forall X p b C1 C2,
  X_Free X (If p ? b Then C1 Else C2) -> {X_Free X C1} + {X_Free X C2}.
Proof.
intros. red in H. simpl in H.
elim (set_union_elim _ _ _ _ _ H); auto.
Qed.

Lemma Not_X_Free_Eta : forall X eta C,
  ~X_Free X (eta;;C) -> ~X_Free X C.
Proof.
intros. intro. apply H. red. simpl. auto.
Qed.

Lemma Not_X_Free_Then : forall X p b C1 C2,
  ~X_Free X (If p ? b Then C1 Else C2) -> ~X_Free X C1.
Proof.
intros. intro. apply H. red. simpl. apply set_union_intro1. auto.
Qed.

Lemma Not_X_Free_Else : forall X p b C1 C2,
  ~X_Free X (If p ? b Then C1 Else C2) -> ~X_Free X C2.
Proof.
intros. intro. apply H. red. simpl. apply set_union_intro2. auto.
Qed.

(** A choreography is well-formed if:
    - it does not contain self-communications;
    - annotations are correct;
    - annotations of runtime terms are not empty.
*)

(** We start with the set of process names in a choreography. *)

Definition set_union_pid := set_union P.eq_dec.

Definition eta_pn (e:Eta) : list Pid :=
match e with
| Com p _ q _ => (p::q::nil)
| Sel p q _   => (p::q::nil)
end.

Fixpoint MCC_pn (C:Choreography) (Pids:RecVar -> list Pid) : list Pid :=
match C with
| End                => nil
| Call X             => Pids X
| RT_Call _ l C'     => set_union_pid l (MCC_pn C' Pids)
| Interaction eta C' => (set_union_pid (eta_pn eta) (MCC_pn C' Pids))
| Cond p _ C1 C2     => (set_union_pid (set_union_pid (p::nil) (MCC_pn C1 Pids)) (MCC_pn C2 Pids))
end.

Definition set_equals_Pid := set_equals P.eq_dec.

(** A program is well-annotated if every procedure is annotated with the correct set of variables. *)

Definition well_ann (P:Program) : Prop :=
  forall X, set_equals_Pid (MCC_pn (Procs P X) (Vars P)) (Vars P X).

Lemma well_ann_Main_change : forall Defs C C',
  well_ann (Build_Program Defs C) -> well_ann (Build_Program Defs C').
Proof.
intros.
intro.
unfold Procs, Vars; simpl.
apply H.
Qed.

(** No process attempts to communicate with itself. *)

Fixpoint no_self_comm (C:Choreography) : Prop :=
match C with
| End                => True
| Call _             => True
| RT_Call _ _ C'     => no_self_comm C'
| Interaction eta C' => match eta with
                        | Com p _ q _ => p <> q
                        | Sel p q _   => p <> q
                        end /\ no_self_comm C'
| Cond _ _ C1 C2     => no_self_comm C1 /\ no_self_comm C2
end.

Lemma no_self_comm_dec : forall C, {no_self_comm C} + {~no_self_comm C}.
Proof.
induction C; simpl; auto.
+ inversion_clear IHC.
  - induction e; simpl; auto.
    * case_eq (Pid_dec p p0); simpl; intros.
      ++ right; intro.
         inversion_clear H1.
         apply H2; apply Pdec.eqb_eq; auto.
      ++ left; split; auto.
         apply Pdec.eqb_neq; auto.
    * case_eq (Pid_dec p p0); simpl; intros.
      ++ right; intro.
         inversion_clear H1.
         apply H2; apply Pdec.eqb_eq; auto.
      ++ left; split; auto.
         apply Pdec.eqb_neq; auto.
  - right; intro.
    inversion_clear H0; auto.
+ inversion_clear IHC1; inversion_clear IHC2; auto;
  right; intro; inversion_clear H1; auto.
Qed.

(** There are no procedure calls with empty annotations. *)

Fixpoint no_empty_ann (C:Choreography) : Prop :=
match C with
| End                => True
| Call _             => True
| RT_Call _ l C'     => l <> nil /\ no_empty_ann C'
| Interaction eta C' => no_empty_ann C'
| Cond _ _ C1 C2     => no_empty_ann C1 /\ no_empty_ann C2
end.

Lemma no_empty_ann_dec : forall C, {no_empty_ann C} + {~no_empty_ann C}.
Proof.
induction C; simpl; auto.
+ inversion_clear IHC.
  - elim (destruct_list l).
    * left; split; auto.
      inversion_clear a.
      inversion_clear X.
      rewrite H0; discriminate.
    * right; intro.
      inversion_clear H0; auto.
  - right; intro.
    inversion_clear H0; auto.
+ inversion_clear IHC1; inversion_clear IHC2; auto;
  right; intro; inversion_clear H1; auto.
Qed.

(** Choreography well-formedness. *)

Definition Choreography_WF (C:Choreography) : Prop :=
  no_self_comm C /\ no_empty_ann C.

Lemma Choreography_WF_dec : forall C, {Choreography_WF C} + {~Choreography_WF C}.
Proof.
intros.
unfold Choreography_WF.
elim (no_self_comm_dec C); intro.
2: right; intro; inversion_clear H; auto.
elim (no_empty_ann_dec C); intro.
2: right; intro; inversion_clear H; auto.
auto.
Qed.

Lemma Choreography_WF_no_self_comm : forall C,
  Choreography_WF C -> no_self_comm C.
Proof. intros. inversion_clear H. auto. Qed.

Lemma Choreography_WF_no_empty_ann : forall C,
  Choreography_WF C -> no_empty_ann C.
Proof. intros. inversion_clear H. auto. Qed.

(** Inversion results. *)
Lemma Choreography_WF_eta : forall eta C,
  Choreography_WF (eta;;C) -> Choreography_WF C.
Proof.
intros.
inversion_clear H; simpl in H0, H1.
split; auto.
inversion_clear H0; auto.
Qed.

Lemma Choreography_WF_Then : forall p b C1 C2,
  Choreography_WF (If p ? b Then C1 Else C2) -> Choreography_WF C1.
Proof.
intros.
inversion_clear H; inversion_clear H0; inversion_clear H1; split; auto.
Qed.

Lemma Choreography_WF_Else : forall p b C1 C2,
  Choreography_WF (If p ? b Then C1 Else C2) -> Choreography_WF C2.
Proof.
intros.
inversion_clear H; inversion_clear H0; inversion_clear H1; split; auto.
Qed.

(** A program is well-formed if there is a finite set of procedures Xs such that:
    - main and all procedures in Xs are well-formed
    - main and all procedures in Xs only call procedures in Xs
    - annotations are consistent
*)

Fixpoint within_Xs (Xs:list RecVar) (C:Choreography) : Prop :=
match C with
| End              => True
| Call X           => In X Xs
| RT_Call X _ C'   => In X Xs /\ within_Xs Xs C'
| Interaction _ C' => within_Xs Xs C'
| Cond _ _ C1 C2   => within_Xs Xs C1 /\ within_Xs Xs C2
end.

Lemma within_Xs_dec : forall Xs C, {within_Xs Xs C} + {~within_Xs Xs C}.
Proof.
induction C; simpl; auto.
+ apply In_dec; apply R.eq_dec.
+ inversion_clear IHC; [elim (In_dec R.eq_dec r Xs) | idtac]; intros.
  - left; split; auto.
  - right; intro; apply b.
    inversion_clear H0; auto.
  - right; intro; apply H.
    inversion_clear H0; auto.
+ inversion_clear IHC1; inversion_clear IHC2; auto;
  right; intro; inversion_clear H1; auto.
Qed.

(** We need a recursive definition on the list of used process variables. *)

Fixpoint Program_WF_rec (Xs Ys:list RecVar) (P:Program) : Prop :=
match Xs with
| nil     => Choreography_WF (Main P) /\ within_Xs Ys (Main P)
| (X::Zs) => Choreography_WF (Procs P X) /\ (Vars P X) <> nil /\
               within_Xs Ys (Procs P X) /\ Program_WF_rec Zs Ys P
end.

Lemma Program_WF_rec_dec : forall Xs Ys P,
  {Program_WF_rec Xs Ys P} + {~Program_WF_rec Xs Ys P}.
Proof.
induction Xs; simpl; intros.
+ elim (Choreography_WF_dec (Main P)); intros.
  2: right; intro; inversion_clear H; auto.
  elim (within_Xs_dec Ys (Main P)); intros.
  2: right; intro; inversion_clear H; auto.
  auto.
+ elim (IHXs Ys P); intros.
  2: right; intro; inversion_clear H; inversion_clear H1; inversion_clear H2; auto.
  clear IHXs.
  elim (Choreography_WF_dec (Procs P a)); intros.
  2: right; intro; inversion_clear H; inversion_clear H1; auto.
  elim (within_Xs_dec Ys (Procs P a)); intros.
  2: right; intro; inversion_clear H; inversion_clear H1; inversion_clear H2; auto.
  case_eq (Vars P a); intros.
  right; intro; inversion_clear H0; inversion_clear H2; inversion_clear H3; auto.
  left; repeat (split; auto).
  discriminate.
Qed.

Definition Program_WF (Xs:list RecVar) (P:Program) : Prop :=
  Program_WF_rec Xs Xs P.

Lemma Program_WF_dec : forall Xs P, {Program_WF Xs P} + {~Program_WF Xs P}.
Proof.
intros.
exact (Program_WF_rec_dec Xs Xs P).
Qed.

Lemma Program_WF_Proc : forall P Xs, Program_WF Xs P ->
  forall X, In X Xs -> Choreography_WF (Procs P X).
Proof.
induction P.
rename Procedures0 into Ps, Main0 into C.
simpl; intros.
red in H.
assert (forall y, Program_WF_rec y Xs (Build_Program Ps C) -> In X y -> Choreography_WF (Procs (Build_Program Ps C) X)).
2: apply H1 with Xs; auto.
clear H; induction y; simpl; intros.
+ inversion H1.
+ inversion_clear H1; inversion_clear H; inversion_clear H3; inversion_clear H4; auto.
  rewrite <- H2; auto.
Qed.

Lemma Program_WF_Main : forall P Xs, Program_WF Xs P -> Choreography_WF (Main P).
Proof.
induction P.
rename Procedures0 into Ps, Main0 into C.
simpl; intros.
red in H.
assert (forall y, Program_WF_rec y Xs (Build_Program Ps C) -> Choreography_WF C).
2: apply H0 with Xs; auto.
clear H; induction y; simpl; intros.
+ inversion H; auto.
+ inversion_clear H; inversion_clear H1; inversion_clear H2; auto.
Qed.

Lemma Program_WF_Main_within_Xs : forall P Xs, Program_WF Xs P ->
  within_Xs Xs (Main P).
Proof.
induction P.
rename Procedures0 into Ps, Main0 into C.
simpl; intros.
red in H.
assert (forall y, Program_WF_rec y Xs (Build_Program Ps C) -> within_Xs Xs C).
2: apply H0 with Xs; auto.
clear H; induction y; simpl; intros.
+ inversion H; auto.
+ inversion_clear H; inversion_clear H1; inversion_clear H2; auto.
Qed.

Lemma Program_WF_Vars_In : forall P Xs, Program_WF Xs P ->
  forall X, X_Free X (Main P) -> In X Xs.
Proof.
intros.
induction P.
rename Procedures0 into Defs, Main0 into C.
assert (forall Ys, Program_WF_rec Xs Ys (Build_Program Defs C) -> In X Ys).
2: eauto.
clear H; induction Xs; simpl; intros.
+ inversion_clear H.
  clear H1.
  induction C; simpl in H0, H2; auto.
  - inversion H0.
  - inversion H0.
    * rewrite <- H; auto.
    * inversion H.
  - red in H0. simpl in H0.
    inversion_clear H2.
    elim (set_union_elim _ _ _ _ _ H0); intros; auto.
    inversion a.
    2: inversion H2.
    rewrite <- H2; auto.
  - inversion H2.
    elim (X_Free_Cond _ _ _ _ _ H0); intros; auto.
+ inversion_clear H; inversion_clear H2; inversion_clear H3.
  auto.
Qed.

Lemma Program_WF_Vars : forall P Xs, Program_WF Xs P ->
  forall X, In X Xs -> Vars P X <> nil.
Proof.
intros.
assert (forall Ys, Program_WF_rec Xs Ys P -> Vars P X <> nil).
2: eauto.
clear H.
induction Xs.
+ inversion H0.
+ intros.
  inversion_clear H0.
  - rewrite H1 in H; clear a H1.
    inversion_clear H; inversion_clear H1; auto.
  - apply IHXs with Ys; auto.
    inversion_clear H; inversion_clear H2; inversion_clear H3; auto.
Qed.

Lemma Program_WF_within_Xs : forall P Xs, Program_WF Xs P ->
  forall X, In X Xs -> within_Xs Xs (Procs P X).
Proof.
assert (forall P Xs Ys, Program_WF_rec Xs Ys P ->
  forall X, In X Xs -> within_Xs Ys (Procs P X)).
2: eauto.
induction Xs; intros.
+ inversion H0.
+ inversion_clear H0.
  - rewrite H1 in H; clear a H1.
    inversion_clear H; inversion_clear H1; inversion_clear H2; auto.
  - apply IHXs; auto.
    inversion_clear H; inversion_clear H2; inversion_clear H3; auto.
Qed.

(** Inversion results. *)
Lemma Program_WF_Main_change : forall Xs Defs C C',
  Choreography_WF C' -> within_Xs Xs C' ->
  Program_WF Xs (Build_Program Defs C) -> Program_WF Xs (Build_Program Defs C').
Proof.
intros.
revert H1.
unfold Program_WF.
assert (forall Ys, Program_WF_rec Ys Xs (Build_Program Defs C) -> Program_WF_rec Ys Xs (Build_Program Defs C')); eauto.
induction Ys; simpl; auto.
intros.
inversion_clear H1; inversion_clear H3; inversion_clear H4.
repeat (split; auto).
Qed.

Lemma Program_WF_eta : forall Xs Defs C eta,
  Program_WF Xs (Build_Program Defs (eta;;C)) -> Program_WF Xs (Build_Program Defs C).
Proof.
intros.
elim (Program_WF_Main _ _ H); simpl; intros.
inversion_clear H0.
eapply Program_WF_Main_change; eauto.
eapply Choreography_WF_eta; repeat split; eauto.
apply (Program_WF_Main_within_Xs _ _ H).
Qed.

Lemma Program_WF_Then : forall Xs Defs p b C1 C2,
  Program_WF Xs (Build_Program Defs (If p ? b Then C1 Else C2)) -> Program_WF Xs (Build_Program Defs C1).
Proof.
intros.
elim (Program_WF_Main _ _ H); simpl; intros.
inversion_clear H0; inversion_clear H1.
eapply Program_WF_Main_change; eauto.
apply Choreography_WF_Then with p b C2; repeat split; auto.
apply (Program_WF_Main_within_Xs _ _ H).
Qed.

Lemma Program_WF_Else : forall Xs Defs p b C1 C2,
  Program_WF Xs (Build_Program Defs (If p ? b Then C1 Else C2)) -> Program_WF Xs (Build_Program Defs C2).
Proof.
intros.
elim (Program_WF_Main _ _ H); simpl; intros.
inversion_clear H0; inversion_clear H1.
eapply Program_WF_Main_change; eauto.
apply Choreography_WF_Else with p b C1; repeat split; auto.
apply (Program_WF_Main_within_Xs _ _ H).
Qed.

(** This one is not decidable. *)

Definition MCP_WF (P:Program) := exists Xs, Program_WF Xs P /\ well_ann P.

Lemma MCP_WF_Main : forall P, MCP_WF P -> Choreography_WF (Main P).
Proof.
intros.
inversion_clear H.
inversion_clear H0.
apply Program_WF_Main with x; auto.
Qed.

Lemma MCP_WF_Vars : forall P, MCP_WF P ->
  forall X, X_Free X (Main P) -> Vars P X <> nil.
Proof.
intros.
inversion_clear H.
rename x into Xs; inversion_clear H1.
clear H2.
apply Program_WF_Vars with Xs; auto.
apply Program_WF_Vars_In with P; auto.
Qed.

End Syntactic_Properties.

(** ** Semantics of MC. *)

Section Semantics_Definitions.

(** Expression evaluation on the state of a process *)

Definition eval_on_state (e:Expr) (s:State) (p:Pid) : Value := eval e (s p).
Definition beval_on_state (b:BExpr) (s:State) (p:Pid) : bool := beval b (s p).

(** The semantics uses a labeled transition system. We first define the type of labels. *)

Inductive TransitionLabel : Type :=
| L_Com (p:Pid) (v:Value) (q:Pid) : TransitionLabel
| L_Sel (p:Pid) (q:Pid) (l:Label) : TransitionLabel
| L_Tau (p:Pid) : TransitionLabel
.

Definition disjoint_p_tl (p:Pid) (t:TransitionLabel) : Prop :=
match t with
| L_Com r _ s => p <> r /\ p <> s
| L_Sel r s _ => p <> r /\ p <> s
| L_Tau r     => p <> r
end.

Definition disjoint_eta_tl (eta:Eta) (t:TransitionLabel) : Prop :=
match eta with
| (p # _ --> q $ _)%MC => disjoint_p_tl p t /\ disjoint_p_tl q t
| (p --> q [_])%MC     => disjoint_p_tl p t /\ disjoint_p_tl q t
end.

Definition set_remove_pid := set_remove P.eq_dec.

(** One-step and multi-step reduction. Multi-step reduction is simply a reflexive and transitive closure. *)

Inductive MCC_To (Procs : RecVar -> (list Pid)*Choreography) :
  Choreography -> State -> TransitionLabel -> Choreography -> State -> Prop :=
 | C_Com p e q x C s : let v := (eval_on_state e s p) in
        MCC_To Procs (p # e --> q $ x;; C) s
               (L_Com p v q)
               C (update s q x v)
 | C_Sel p q l C s : MCC_To Procs (p --> q [l];; C) s (L_Sel p q l) C s
 | C_Then p b C1 C2 s : (beval_on_state b s p = true) ->
        MCC_To Procs (If p ? b Then C1 Else C2) s (L_Tau p) C1 s
 | C_Else p b C1 C2 s : (beval_on_state b s p = false) ->
        MCC_To Procs (If p ? b Then C1 Else C2) s (L_Tau p) C2 s
 | C_Delay_Eta eta C C' s s' t: disjoint_eta_tl eta t -> 
        MCC_To Procs C s t C' s' ->
        MCC_To Procs (eta;; C) s t (eta;; C') s'
 | C_Delay_Cond p b C1 C2 C1' C2' s s' t: disjoint_p_tl p t -> 
        MCC_To Procs C1 s t C1' s' ->
        MCC_To Procs C2 s t C2' s' ->
        MCC_To Procs (If p ? b Then C1 Else C2) s t (If p ? b Then C1' Else C2') s'
 | C_Call_Local p X s : (fst (Procs X) = (p::nil)) ->
        MCC_To Procs (Call X) s (L_Tau p) (snd (Procs X)) s
 | C_Call_Start p X s: (length (fst (Procs X)) > 1) -> In p (fst (Procs X)) ->
        MCC_To Procs
               (Call X) s
               (L_Tau p)
               (RT_Call X (set_remove_pid p (fst (Procs X))) (snd (Procs X))) s
 | C_Call_Enter p ps X C s : length ps > 1 -> In p ps ->
        MCC_To Procs
               (RT_Call X ps C) s
               (L_Tau p)
               (RT_Call X (set_remove_pid p ps) C) s
 | C_Call_Finish p X C s: 
        MCC_To Procs
               (RT_Call X (p::nil) C) s (L_Tau p) C s
.

Definition Configuration : Type := Program * State.

Inductive MCP_To : Configuration -> TransitionLabel -> Configuration -> Prop :=
 | MCP_To_intro Procs C s t C' s' : MCC_To Procs C s t C' s' ->
     MCP_To (Build_Program Procs C,s) t (Build_Program Procs C',s').

Inductive MCP_ToStar : Configuration -> list TransitionLabel -> Configuration -> Prop :=
 | MCT_Refl c : MCP_ToStar c nil c
 | MCT_Step c1 t c2 l c3 : MCP_To c1 t c2 -> MCP_ToStar c2 l c3 -> MCP_ToStar c1 (t::l) c3
.

(*
(** A well-formed program is terminated if its main choreography is either 0 or a call to a terminated procedure. *)

Definition terminated (P:Program) : Prop :=
match Main P with
| End    => True
| Call X => (Vars P X) = nil
| _      => False
end.
*)

End Semantics_Definitions.

(** Notations for precongruence and reductions. *)

Notation "c --[ tl ]--> c'" := (MCP_To c tl c') (at level 50, left associativity).
Notation "c --[ ts ]-->* c'" := (MCP_ToStar c ts c') (at level 50, left associativity).

Section Sanity_Checks.

Example Com_reduction : forall P p e q x C s,
  (Build_Program P (p # e --> q $ x;; C), s) --[ L_Com p (eval_on_state e s p) q ]--> (Build_Program P C, update s q x (eval_on_state e s p)).
Proof. constructor. constructor. Qed.

Example Sel_reduction : forall P p q l C s, 
  (Build_Program P (p --> q [l];; C), s) --[ L_Sel p q l ]--> (Build_Program P C, s).
Proof. constructor. constructor. Qed.

End Sanity_Checks.

Theorem progress : forall P, Main P <> End -> MCP_WF P ->
  forall s, exists tl c', (P,s) --[tl]--> c'.
Proof.
induction P.
rename Procedures0 into Ps, Main0 into C.
induction C; intros.
+ simpl in H. elim H; auto.
+ rename r into X; set (ps := fst (Ps X)).
  simpl in H.
  case_eq ps; [idtac | intros; case_eq l].
  - intro. exfalso.
    unfold ps in H1.
    generalize (MCP_WF_Vars _ H0 X); intros.
    simpl in H2.
    unfold Vars in H2; simpl in H2.
    rewrite H1 in H2.
    apply H2; auto.
    red. simpl. auto.
  - intros.
    rewrite H2 in H1; clear H2 l.
    do 2 eexists.
    constructor; apply C_Call_Local.
    unfold ps in H1; rewrite H1.
    reflexivity.
  - intros.
    do 2 eexists.
    constructor; apply C_Call_Start;
    fold ps; rewrite H1, H2.
    * simpl; auto with arith.
    * left; auto.
+ case_eq l.
  - clear H IHC.
    intro; exfalso.
    generalize (MCP_WF_Main _ H0).
    simpl; intros.
    inversion_clear H1.
    inversion_clear H3.
    simpl in H1.
    rewrite H in H1; auto.
  - intros.
    case l0; do 2 eexists; constructor.
    * apply C_Call_Finish.
    * constructor; simpl; auto with arith.
+ case_eq e; do 2 eexists; do 2 constructor.
+ case_eq (beval_on_state b s p).
  - do 2 eexists; constructor; apply C_Then; auto.
  - do 2 eexists; constructor; apply C_Else; auto.
Qed.

Lemma MCC_To_within_Xs : forall P s l P' s' Xs,
  Program_WF Xs P -> (P,s) --[l]--> (P',s') -> within_Xs Xs (Main P').
Proof.
intros.
revert H.
inversion_clear H0.
rename Procs0 into Defs.
simpl; intros.
generalize (Program_WF_within_Xs _ _ H0); intros.
unfold Procs in H1; simpl in H1.
generalize (Program_WF_Main_within_Xs _ _ H0); simpl; intros.
clear H0.
induction H; auto.
+ inversion_clear H2; auto.
+ inversion_clear H2; auto.
+ inversion_clear H2; split; auto.
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
clear s'0 H6 s0 H3 H5 H0 P' H1 P H2 t.
rename Procs0 into Defs.
apply Program_WF_Main_change with C; auto.
clear HXs.
generalize (Program_WF_Main _ _ H); simpl; intro HC.
(* generalize (Program_WF_within_Xs _ _ H); simpl; intro HXs.
generalize (Program_WF_Vars_In _ _ H); simpl; intro HX. *)
induction H4.
+ eapply Choreography_WF_eta; eauto.
+ eapply Choreography_WF_eta; eauto.
+ eapply Choreography_WF_Then; eauto.
+ eapply Choreography_WF_Else; eauto.
+ inversion_clear HC.
  inversion_clear H1; simpl in H2.
  elim IHMCC_To; repeat split; auto.
  eapply Program_WF_eta; eauto.
+ inversion_clear HC.
  inversion_clear H1; inversion_clear H2.
  assert (Choreography_WF C1). split; auto.
  assert (Choreography_WF C2). split; auto.
  generalize (Program_WF_Then _ _ _ _ _ _ H); intro.
  generalize (Program_WF_Else _ _ _ _ _ _ H); intro.
  elim IHMCC_To1; auto; elim IHMCC_To2; auto; intros.
  split; split; auto.
+ change (Choreography_WF (Procs (Build_Program Defs (Call X)) X)).
  apply Program_WF_Proc with Xs; auto.
  apply (Program_WF_Vars_In _ _ H). red; simpl; auto.
+ elim (Program_WF_Proc _ _ H X); intros.
  2: apply (Program_WF_Vars_In _ _ H); red; simpl; auto.
  split; simpl; auto.
  split; auto.
  revert H0; case (fst (Defs X)); intros.
  1: exfalso; inversion H0.
  revert H0; case l; intros.
  1: exfalso; inversion H0; inversion H5.
  simpl.
  elim P.eq_dec; try discriminate.
+ elim (Program_WF_Proc _ _ H X); intros.
  2: {
    apply (Program_WF_Vars_In _ _ H); red; simpl.
    apply set_union_intro1; simpl; auto.
  }
  inversion_clear HC.
  simpl in H4, H5.
  split; simpl; auto.
  inversion_clear H5; split; auto.
  revert H0; case ps; intros.
  1: exfalso; inversion H0.
  revert H0; case l; intros.
  1: exfalso; inversion H0; inversion H8.
  simpl.
  elim P.eq_dec; try discriminate.
+ elim HC; intros.
  inversion_clear H1; red; auto.
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

End MCBase.
