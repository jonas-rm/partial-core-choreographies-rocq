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

Definition set_remove_pid := set_remove' P.eq_dec.
Definition set_size_pid := set_size P.eq_dec.

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

Definition DefSet := RecVar -> (list Pid)*Choreography.

Record Program : Type :=
  { Procedures : DefSet;
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

Lemma X_Free_dec : forall X C, {X_Free X C} + {~X_Free X C}.
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
      simpl. intro. inversion_clear a; auto.
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

Lemma X_Free_Cond : forall X p b C1 C2,
  X_Free X (If p ? b Then C1 Else C2) -> {X_Free X C1} + {X_Free X C2}.
Proof.
intros. red in H. simpl in H.
elim (set_union_elim _ _ _ _ H); auto.
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

Definition set_incl_Pid := set_incl P.eq_dec.

(** A program is well-annotated if every process used by a procedure is in its annotation. *)

Definition well_ann (P:Program) : Prop :=
  forall X, set_incl_Pid (MCC_pn (Procs P X) (Vars P)) (Vars P X).

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
2: right; intro; destroy H; auto.
elim (no_empty_ann_dec C); intro.
2: right; intro; destroy H; auto.
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
destroy H; destroy H0; split; auto.
Qed.

Lemma Choreography_WF_Else : forall p b C1 C2,
  Choreography_WF (If p ? b Then C1 Else C2) -> Choreography_WF C2.
Proof.
intros.
destroy H; destroy H0; split; auto.
Qed.

Lemma Choreography_WF_Call_1 : forall X ps C,
  Choreography_WF (RT_Call X ps C) -> Choreography_WF C.
Proof.
intros.
destroy H; split; auto.
Qed.

Lemma Choreography_WF_Call_2 : forall X p ps C,
  Choreography_WF (RT_Call X ps C) -> set_size_pid ps > 1 ->
  Choreography_WF (RT_Call X (set_remove_pid p ps) C).
Proof.
intros.
destroy H; repeat split; auto.
unfold set_size_pid in H0. unfold set_remove_pid.
elim (In_dec P.eq_dec p ps); intro.
+ rewrite (set_size_remove' P.eq_dec ps p) in H0; auto.
  apply lt_S_n in H0.
  intro; rewrite H3 in H0; inversion H0.
+ rewrite set_remove'_not_In; auto.
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
    destroy H0; auto.
  - right; intro; apply H.
    destroy H0; auto.
+ inversion_clear IHC1; inversion_clear IHC2; auto;
  right; intro; destroy H1; auto.
Qed.

Lemma within_Xs_incl : forall C Xs Ys, (forall X, In X Xs -> In X Ys) ->
  within_Xs Xs C -> within_Xs Ys C.
Proof.
induction C; simpl; auto.
+ intros. inversion_clear H0. split; eauto.
+ intros. inversion_clear H0. split; eauto.
Qed.

(** We need to consider the list of used process variables. *)

Definition Program_WF (Xs:list RecVar) (P:Program) : Prop :=
  Choreography_WF (Main P) /\ within_Xs Xs (Main P) /\
  forall X, In X Xs -> Choreography_WF (Procs P X) /\ initial (Procs P X) /\
            (Vars P X) <> nil /\ within_Xs Xs (Procs P X).

Lemma Program_WF_dec : forall Xs P, {Program_WF Xs P} + {~Program_WF Xs P}.
Proof.
intros.
elim (Choreography_WF_dec (Main P)); intros.
2: right; intro; destroy H; auto.
elim (within_Xs_dec Xs (Main P)); intros.
2: right; intro; destroy H; auto.
assert (forall (Ys:list RecVar), {forall X, In X Ys -> Choreography_WF (Procs P X) /\ initial (Procs P X) /\
            (Vars P X) <> nil /\ within_Xs Xs (Procs P X)} +
        {~forall X, In X Ys -> Choreography_WF (Procs P X) /\ initial (Procs P X) /\
            (Vars P X) <> nil /\ within_Xs Xs (Procs P X)}); intros.
2: { elim (X Xs); clear X; intros.
  left; repeat (split; auto).
  right; intro. destroy H; auto.
}
clear a a0.
induction Ys; simpl; intros.
+ left. intros; inversion H.
+ elim IHYs; intros.
  2: right; intro; destroy H; auto.
  clear IHYs.
  elim (Choreography_WF_dec (Procs P a)); intros.
  2: right; intro; elim (H a); auto.
  elim (initial_dec (Procs P a)); intros.
  2: right; intro; elim (H a); intros; destroy H1; auto.
  elim (within_Xs_dec Xs (Procs P a)); intros.
  2: right; intro; elim (H a); intros; destroy H1; auto.
  case_eq (Vars P a); intros.
  right; intro; elim (H0 a); intros; destroy H2; auto.
  left; intros.
  inversion_clear H0; auto.
  rewrite <- H1; repeat (split; auto).
  rewrite H; discriminate.
Qed.

Lemma Program_WF_Proc : forall P Xs, Program_WF Xs P ->
  forall X, In X Xs -> Choreography_WF (Procs P X).
Proof. intros. destroy H. elim (H X); auto. Qed.

Lemma Program_WF_Main : forall P Xs, Program_WF Xs P -> Choreography_WF (Main P).
Proof. intros. destroy H; auto. Qed.

Lemma Program_WF_initial_Proc : forall P Xs, Program_WF Xs P ->
  forall X, In X Xs -> initial (Procs P X).
Proof. intros. destroy H. elim (H X); auto. intros. destroy H4; auto. Qed.

Lemma Program_WF_Main_within_Xs : forall P Xs, Program_WF Xs P ->
  within_Xs Xs (Main P).
Proof. intros. destroy H; auto. Qed.

Lemma Program_WF_Vars_In : forall P Xs, Program_WF Xs P ->
  forall X, X_Free X (Main P) -> In X Xs.
Proof.
intros.
destroy H. clear H.
induction P.
rename Procedures0 into Defs, Main0 into C.
simpl in H0, H2. clear H1.
induction C; auto.
+ inversion H0.
+ inversion H0. rewrite H in H2; simpl in H2; auto. inversion H.
+ inversion_clear H2. red in H0. simpl in H0.
  elim (set_union_elim _ _ _ _ H0); intros; auto.
  inversion_clear a. rewrite H2 in H; auto. inversion H2.
+ inversion_clear H2.
  elim (set_union_elim _ _ _ _ H0); auto.
Qed.

Lemma Program_WF_Vars : forall P Xs, Program_WF Xs P ->
  forall X, In X Xs -> Vars P X <> nil.
Proof. intros. destroy H. elim (H X); auto. intros. destroy H4; auto. Qed.

Lemma Program_WF_within_Xs : forall P Xs, Program_WF Xs P ->
  forall X, In X Xs -> within_Xs Xs (Procs P X).
Proof. intros. destroy H. elim (H X); auto. intros. destroy H4; auto. Qed.

(** Inversion results. *)
Lemma Program_WF_Main_change : forall Xs Defs C C',
  Choreography_WF C' -> within_Xs Xs C' ->
  Program_WF Xs (Build_Program Defs C) -> Program_WF Xs (Build_Program Defs C').
Proof.
intros.
destroy H1; repeat (split; auto).
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

Lemma Program_WF_Call : forall Xs Defs X ps C,
  Program_WF Xs (Build_Program Defs (RT_Call X ps C)) -> Program_WF Xs (Build_Program Defs C).
Proof.
intros.
elim (Program_WF_Main _ _ H); simpl; intros.
inversion_clear H1.
eapply Program_WF_Main_change; eauto.
split; auto.
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

Lemma MCP_WF_eta : forall Defs C eta,
  MCP_WF (Build_Program Defs (eta;;C)) -> MCP_WF (Build_Program Defs C).
Proof.
intros.
inversion_clear H; inversion_clear H0.
exists x; split; auto. eapply Program_WF_eta; eauto.
Qed.

Lemma MCP_WF_Then : forall Defs p b C1 C2,
  MCP_WF (Build_Program Defs (If p ? b Then C1 Else C2)) -> MCP_WF (Build_Program Defs C1).
Proof.
intros.
inversion_clear H; inversion_clear H0.
exists x; split; auto. eapply Program_WF_Then; eauto.
Qed.

Lemma MCP_WF_Else : forall Defs p b C1 C2,
  MCP_WF (Build_Program Defs (If p ? b Then C1 Else C2)) -> MCP_WF (Build_Program Defs C2).
Proof.
intros.
inversion_clear H; inversion_clear H0.
exists x; split; auto. eapply Program_WF_Else; eauto.
Qed.

Lemma MCP_WF_Call : forall Defs X ps C,
  MCP_WF (Build_Program Defs (RT_Call X ps C)) -> MCP_WF (Build_Program Defs C).
Proof.
intros.
inversion_clear H; inversion_clear H0.
exists x; split; auto. eapply Program_WF_Call; eauto.
Qed.

End Syntactic_Properties.

(** ** Semantics of MC. *)

Section Semantics_Definitions.

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

(** The semantics uses a labeled transition system. We first define the type of labels. *)

Inductive RichLabel : Type :=
| R_Com (p:Pid) (v:Value) (q:Pid) (x:Var) : RichLabel
| R_Sel (p:Pid) (q:Pid) (l:Label) : RichLabel
| R_Cond (p:Pid) : RichLabel
| R_Call (X:RecVar) (p:Pid) : RichLabel
.

Lemma RichLabel_eq_dec : forall (x y:RichLabel), {x=y}+{x<>y}.
Proof.
decide equality; try (apply P.eq_dec).
+ apply X.eq_dec.
+ apply V.eq_dec.
+ decide equality.
+ apply R.eq_dec.
Qed.

Inductive TransitionLabel : Type :=
| L_Com (p:Pid) (v:Value) (q:Pid) : TransitionLabel
| L_Sel (p:Pid) (q:Pid) (l:Label) : TransitionLabel
| L_Tau (p:Pid) : TransitionLabel
.

Lemma TransitionLabel_eq_dec : forall (x y:TransitionLabel), {x=y}+{x<>y}.
Proof.
decide equality; try (apply P.eq_dec).
+ apply V.eq_dec.
+ decide equality.
Qed.

Definition forget (t:RichLabel) : TransitionLabel :=
  match t with
  | R_Com p v q _ => L_Com p v q
  | R_Sel p q l   => L_Sel p q l
  | R_Cond p      => L_Tau p
  | R_Call _ p    => L_Tau p
end.

(** Useful for rewriting in proofs. *)
Lemma forget_Com : forall x p v q, forget (R_Com p v q x) = L_Com p v q.
Proof. auto. Qed.

Lemma forget_Sel : forall p q l, forget (R_Sel p q l) = L_Sel p q l.
Proof. auto. Qed.

Lemma forget_Cond : forall p, forget (R_Cond p) = L_Tau p.
Proof. auto. Qed.

Lemma forget_Call : forall X p, forget (R_Call X p) = L_Tau p.
Proof. auto. Qed.

Definition disjoint_p_rl (p:Pid) (t:RichLabel) : Prop :=
match t with
| R_Com r _ s _ => p <> r /\ p <> s
| R_Sel r s _   => p <> r /\ p <> s
| R_Cond r      => p <> r
| R_Call _ r    => p <> r
end.

Fixpoint disjoint_ps_rl (ps:list Pid) (t:RichLabel) : Prop :=
match ps with
| nil    => True
| p::ps' => disjoint_p_rl p t /\ disjoint_ps_rl ps' t
end.

Lemma disjoint_ps_rl_In p ps t :
  In p ps -> disjoint_ps_rl ps t -> disjoint_p_rl p t.
Proof.
induction ps; intros; inversion H; inversion_clear H0; auto.
rewrite <- H1; auto.
Qed.

Lemma disjoint_ps_Sel : forall p q l ps,
  disjoint_ps_rl ps (R_Sel p q l) -> disjoint (p::q::nil) ps.
Proof.
intros. intro; intro. inversion_clear H0.
induction ps; auto.
inversion_clear H.
inversion_clear H2; auto.
rewrite H in H0. inversion_clear H0.
inversion_clear H1; auto. inversion_clear H0; auto.
Qed.

Lemma disjoint_ps_Com : forall p v q x ps,
  disjoint_ps_rl ps (R_Com p v q x) -> disjoint (p::q::nil) ps.
Proof.
intros. intro; intro. inversion_clear H0.
induction ps; auto.
inversion_clear H.
inversion_clear H2; auto.
rewrite H in H0. inversion_clear H0.
inversion_clear H1; auto. inversion_clear H0; auto.
Qed.

Lemma disjoint_ps_Cond : forall p ps,
  disjoint_ps_rl ps (R_Cond p) -> ~In p ps.
Proof.
induction ps; intros; simpl; auto.
intro. inversion_clear H. simpl in H1.
inversion_clear H0; auto.
apply IHps; auto.
Qed.

Lemma disjoint_ps_Call : forall p ps X,
  disjoint_ps_rl ps (R_Call X p) -> ~In p ps.
Proof.
induction ps; intros; simpl; auto.
intro. inversion_clear H. simpl in H1.
inversion_clear H0; auto.
eapply IHps; eauto.
Qed.

Lemma disjoint_ps_char : forall ps tl,
  (forall p, In p ps -> disjoint_p_rl p tl) -> disjoint_ps_rl ps tl.
Proof.
induction ps; simpl; auto.
Qed.

Lemma disjoint_ps_remove : forall p ps tl,
  disjoint_ps_rl ps tl -> disjoint_ps_rl (set_remove_pid p ps) tl.
Proof.
intros.
apply disjoint_ps_char; intros.
apply disjoint_ps_rl_In with ps; auto.
eapply set_remove'_1; apply H0.
Qed.

Definition disjoint_eta_rl (eta:Eta) (t:RichLabel) : Prop :=
match eta with
| (p # _ --> q $ _)%MC => disjoint_p_rl p t /\ disjoint_p_rl q t
| (p --> q [_])%MC     => disjoint_p_rl p t /\ disjoint_p_rl q t
end.

Lemma disjoint_Sel_Sel : forall p q l p' q' l',
  disjoint_eta_rl (Sel p q l) (R_Sel p' q' l') -> disjoint (p::q::nil) (p'::q'::nil).
Proof.
intros. intro; intro. inversion_clear H.
inversion_clear H1; inversion_clear H2.
inversion_clear H0. inversion_clear H2; inversion_clear H5.
+ apply H. transitivity a; auto.
+ inversion_clear H2. 2: inversion H5.
  apply H3. transitivity a; auto.
+ inversion_clear H0. 2: inversion H5.
  apply H1. transitivity a; auto.
+ inversion_clear H0. 2: inversion H5.
  inversion_clear H2. 2: inversion H0.
  apply H4. transitivity a; auto.
Qed.

Lemma disjoint_Com_Com : forall p q e x p' q' v x',
  disjoint_eta_rl (Com p e q x) (R_Com p' v q' x') -> disjoint (p::q::nil) (p'::q'::nil).
Proof. intros. apply disjoint_Sel_Sel with left right; auto. Qed.

Lemma disjoint_Com_Sel : forall p q e x p' q' l,
  disjoint_eta_rl (Com p e q x) (R_Sel p' q' l) -> disjoint (p::q::nil) (p'::q'::nil).
Proof. intros. apply disjoint_Sel_Sel with l left; auto. Qed.

Lemma disjoint_Sel_Com : forall p q l p' v q' x,
  disjoint_eta_rl (Sel p q l) (R_Com p' x q' v) -> disjoint (p::q::nil) (p'::q'::nil).
Proof. intros. apply disjoint_Sel_Sel with l left; auto. Qed.

(** One-step and multi-step reduction. Multi-step reduction is simply a reflexive and transitive closure. *)

Inductive MCC_To (Defs : DefSet) :
  Choreography -> State -> RichLabel -> Choreography -> State -> Prop :=
 | C_Com p e q x C s s' : let v := (eval_on_state e s p) in
        eq_state_ext s' (update s q x v) ->
        MCC_To Defs (p # e --> q $ x;; C) s (R_Com p v q x) C s'
 | C_Sel p q l C s s':
        eq_state_ext s s' ->
        MCC_To Defs (p --> q [l];; C) s (R_Sel p q l) C s'
 | C_Then p b C1 C2 s s':
        eq_state_ext s s' -> (beval_on_state b s p = true) ->
        MCC_To Defs (If p ? b Then C1 Else C2) s (R_Cond p) C1 s'
 | C_Else p b C1 C2 s s':
        eq_state_ext s s' -> (beval_on_state b s p = false) ->
        MCC_To Defs (If p ? b Then C1 Else C2) s (R_Cond p) C2 s'
 | C_Delay_Eta eta C C' s s' t: disjoint_eta_rl eta t -> 
        MCC_To Defs C s t C' s' ->
        MCC_To Defs (eta;; C) s t (eta;; C') s'
 | C_Delay_Cond p b C1 C2 C1' C2' s s' t: disjoint_p_rl p t -> 
        MCC_To Defs C1 s t C1' s' ->
        MCC_To Defs C2 s t C2' s' ->
        MCC_To Defs (If p ? b Then C1 Else C2) s t (If p ? b Then C1' Else C2') s'
 | C_Delay_Call ps X C C' s s' t:
        disjoint_ps_rl ps t -> MCC_To Defs C s t C' s' ->
        MCC_To Defs (RT_Call X ps C) s t (RT_Call X ps C') s'
 | C_Call_Local p X s s': eq_state_ext s s' ->
        set_size_pid (fst (Defs X)) = 1 -> In p (fst (Defs X)) ->
        MCC_To Defs (Call X) s (R_Call X p) (snd (Defs X)) s'
 | C_Call_Start p X s s':
        eq_state_ext s s' ->
        set_size_pid (fst (Defs X)) > 1 -> In p (fst (Defs X)) ->
        MCC_To Defs
               (Call X) s
               (R_Call X p)
               (RT_Call X (set_remove_pid p (fst (Defs X))) (snd (Defs X))) s'
 | C_Call_Enter p ps X C s s':
        eq_state_ext s s' -> set_size_pid ps > 1 -> In p ps ->
        MCC_To Defs
               (RT_Call X ps C) s
               (R_Call X p)
               (RT_Call X (set_remove_pid p ps) C) s'
 | C_Call_Finish p ps X C s s':
        eq_state_ext s s' -> set_size_pid ps = 1 -> In p ps ->
        MCC_To Defs
               (RT_Call X ps C) s (R_Call X p) C s'
.

(* Grrrr *)

Lemma C_Com' : forall Defs p e q x C s, let v := (eval_on_state e s p) in
        MCC_To Defs (p # e --> q $ x;; C) s (R_Com p v q x) C (update s q x v).
Proof. intros. apply C_Com. ESEr. Qed.

Lemma C_Sel' : forall Defs p q l C s,
  MCC_To Defs (p --> q [l];; C) s (R_Sel p q l) C s.
Proof. intros. apply C_Sel. ESEr. Qed.

Lemma C_Then' : forall Defs p b C1 C2 s,
        beval_on_state b s p = true ->
        MCC_To Defs (If p ? b Then C1 Else C2) s (R_Cond p) C1 s.
Proof. intros. apply C_Then. ESEr. auto. Qed.

Lemma C_Else' : forall Defs p b C1 C2 s,
        beval_on_state b s p = false ->
        MCC_To Defs (If p ? b Then C1 Else C2) s (R_Cond p) C2 s.
Proof. intros. apply C_Else. ESEr. auto. Qed.

Lemma C_Call_Local' : forall Defs p X s,
        set_size_pid (fst (Defs X)) = 1 -> In p (fst (Defs X)) ->
        MCC_To Defs (Call X) s (R_Call X p) (snd (Defs X)) s.
Proof. intros. apply C_Call_Local; auto. ESEr. Qed.

Lemma C_Call_Start' : forall Defs p X s,
        set_size_pid (fst (Defs X)) > 1 -> In p (fst (Defs X)) ->
        MCC_To Defs
               (Call X) s
               (R_Call X p)
               (RT_Call X (set_remove_pid p (fst (Defs X))) (snd (Defs X))) s.
Proof. intros. apply C_Call_Start; auto. ESEr. Qed.

Lemma C_Call_Enter' : forall Defs p ps X C s,
        set_size_pid ps > 1 -> In p ps ->
        MCC_To Defs
               (RT_Call X ps C) s
               (R_Call X p)
               (RT_Call X (set_remove_pid p ps) C) s.
Proof. intros. apply C_Call_Enter; auto. ESEr. Qed.

Lemma C_Call_Finish' : forall Defs p ps X C s,
        set_size_pid ps = 1 -> In p ps ->
        MCC_To Defs (RT_Call X ps C) s (R_Call X p) C s.
Proof. intros. apply C_Call_Finish; auto. ESEr. Qed.

Definition Configuration : Type := Program * State.

Inductive MCP_To : Configuration -> TransitionLabel -> Configuration -> Prop :=
 | MCP_To_intro Defs C s t C' s' : MCC_To Defs C s t C' s' ->
     MCP_To (Build_Program Defs C,s) (forget t) (Build_Program Defs C',s').

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
Proof. intros. rewrite <- (forget_Com x). constructor. apply C_Com'. Qed.

Example Sel_reduction : forall P p q l C s, 
  (Build_Program P (p --> q [l];; C), s) --[ L_Sel p q l ]--> (Build_Program P C, s).
Proof. intros. rewrite <- forget_Sel. constructor. apply C_Sel'. Qed.

End Sanity_Checks.

Section Uniqueness.

(** ** Results on determinism of the semantics. *)

(** Reductions are preserved by state equivalence. *)

Lemma MCC_To_eq : forall Defs C s1 tl C' s2 s1' s2',
  eq_state_ext s1 s1' -> eq_state_ext s2 s2' ->
  MCC_To Defs C s1 tl C' s2 -> MCC_To Defs C s1' tl C' s2'.
Proof.
intros.
induction H1.
+ unfold v.
  rewrite (eval_eq e s s1'); auto.
  apply C_Com.
  ESEt s'. ESEs. eESEt.
  rewrite <- (eval_eq e s s1'); auto. fold v.
  ESEc; auto.
+ apply C_Sel. ESEt s. ESEs. ESEt s'.
+ apply C_Then. ESEt s. ESEs. ESEt s'.
  rewrite <- (beval_eq b s); auto.
+ apply C_Else. ESEt s. ESEs. ESEt s'.
  rewrite <- (beval_eq b s); auto.
+ apply C_Delay_Eta; auto.
+ apply C_Delay_Cond; auto.
+ apply C_Delay_Call; auto.
+ apply C_Call_Local; auto. ESEt s. ESEs. ESEt s'.
+ apply C_Call_Start; auto. ESEt s. ESEs. ESEt s'.
+ apply C_Call_Enter; auto. ESEt s. ESEs. ESEt s'.
+ apply C_Call_Finish; auto. ESEt s. ESEs. ESEt s'.
Qed.

Lemma MCP_To_eq : forall P s1 tl P' s2 s1' s2',
  eq_state_ext s1 s1' -> eq_state_ext s2 s2' ->
  (P,s1) --[tl]--> (P',s2) -> (P,s1') --[tl]--> (P',s2').
Proof.
intros.
induction P.
inversion H1; constructor.
apply MCC_To_eq with s1 s2; auto.
Qed.

Lemma MCP_ToStar_eq : forall P s1 tl P' s2 s1' s2',
  eq_state_ext s1 s1' -> eq_state_ext s2 s2' -> tl <> nil ->
  (P,s1) --[tl]-->* (P',s2) -> (P,s1') --[tl]-->* (P',s2').
Proof.
intros P s1 tl; revert P s1.
induction tl; intros. elim H1; auto.
case_eq tl; intros.
+ rewrite H3 in H2; inversion H2.
  inversion H9. rewrite H12 in H7.
  apply MCT_Step with (P',s2'). 2: constructor.
  apply MCP_To_eq with s1 s2; auto.
+ inversion H2.
  induction c2.
  apply MCT_Step with (a0,b).
  - apply MCP_To_eq with s1 b; auto. ESEr.
  - rewrite <- H3. eapply IHtl; eauto. ESEr.
    rewrite H3; discriminate.
Qed.

(** The set of procedure definitions never changes. *)

Hypothesis Defs : DefSet.

Lemma MCP_To_Defs_stable : forall Defs' C C' tl s s',
  (Build_Program Defs C,s) --[tl]--> (Build_Program Defs' C',s') -> Defs = Defs'.
Proof.
intros.
inversion H.
inversion H; auto.
Qed.

Lemma MCP_ToStar_Defs_stable : forall Defs' C C' tl s s',
  (Build_Program Defs C,s) --[tl]-->* (Build_Program Defs' C',s') -> Defs = Defs'.
Proof.
intros Defs' C C' tl; revert C C'.
induction tl; intros; inversion H; clear H; auto.
clear c1 c3 H2 H4 t l H0 H1.
induction c2. induction a0.
apply MCP_To_Defs_stable in H3.
rewrite <- H3 in H5.
eauto.
Qed.

(** Reductions and state. *)

Lemma MCC_To_disjoint_eval : forall C s tl s' p e C',
  disjoint_p_rl p tl -> MCC_To Defs C s tl C' s' ->
  eval_on_state e s p = eval_on_state e s' p.
Proof.
intros.
induction H0; auto; try (apply eval_eq; auto; fail).
inversion_clear H.
transitivity (eval_on_state e (update s q x v) p).
apply eval_neq; auto.
apply eval_eq; ESEs.
Qed.

Lemma MCC_To_disjoint_beval : forall C s tl s' p b C',
  disjoint_p_rl p tl -> MCC_To Defs C s tl C' s' ->
  beval_on_state b s p = beval_on_state b s' p.
Proof.
intros.
induction H0; auto; try (apply beval_eq; auto; fail).
inversion_clear H.
transitivity (beval_on_state b (update s q x v) p).
apply beval_neq; auto.
apply beval_eq; ESEs.
Qed.

Lemma MCC_To_disjoint_update : forall C s tl s' p x v C',
  disjoint_p_rl p tl -> MCC_To Defs C s tl C' s' ->
  MCC_To Defs C (update s p x v) tl C' (update s' p x v).
Proof.
intros.
induction H0; try (constructor; auto; try ESEc; auto; fail).
+ inversion_clear H.
  unfold v0. rewrite (eval_neq e s p0 p x v); auto.
  apply C_Com.
  rewrite <- (eval_neq e s p0 p x v); auto.
  fold v0.
  ESEt (update (update s q x0 v0) p x v). ESEc; auto.
  apply update_independent; auto.
+ apply C_Then. ESEc; auto.
  rewrite <- beval_neq; auto.
+ apply C_Else. ESEc; auto.
  rewrite <- beval_neq; auto.
Qed.

(** Determinism of reductions given the label. *)
Lemma MCC_To_deterministic_1 : forall C C1 C2 tl s s1 s2,
  MCC_To Defs C s tl C1 s1 -> MCC_To Defs C s tl C2 s2 -> C1 = C2.
Proof.
(* Might be simpler: induction tl *)
induction C; intros; inversion H; inversion H0; 
  try (transitivity C; auto; fail).
- auto.
- rewrite H3 in H11; elim (lt_irrefl _ H11).
- rewrite H11 in H3; elim (lt_irrefl _ H3).
- rewrite <- H6 in H14; inversion H14; auto.
- rewrite (IHC _ _ _ _ _ _ H9 H18); auto.
- rewrite <- H15 in H8. apply (disjoint_ps_rl_In _ _ _ H19) in H8.
  elim H8; auto.
- rewrite <- H15 in H8. apply (disjoint_ps_rl_In _ _ _ H19) in H8.
  elim H8; auto.
- rewrite <- H6 in H18. apply (disjoint_ps_rl_In _ _ _ H10) in H18.
  elim H18; auto.
- rewrite <- H6 in H16; inversion H16; auto.
- rewrite H19 in H9; elim (lt_irrefl _ H9).
- rewrite <- H6 in H18. apply (disjoint_ps_rl_In _ _ _ H10) in H18.
  elim H18; auto.
- rewrite H9 in H19; elim (lt_irrefl _ H19).
- exfalso. rewrite <- H1, <- H4 in H10.
  inversion_clear H10. inversion_clear H16. auto.
- exfalso. rewrite <- H1, <- H4 in H10.
  inversion_clear H10. inversion_clear H16. auto.
- exfalso. rewrite <- H12, <- H9 in H3.
  inversion_clear H3. inversion_clear H16. auto.
- exfalso. rewrite <- H12, <- H9 in H3.
  inversion_clear H3. inversion_clear H16. auto.
- elim (IHC _ _ _ _ _ _ H8 H16); auto.
- transitivity C1; auto.
- rewrite H10 in H20; inversion H20.
- rewrite <- H6 in H19; elim H19; auto.
- rewrite H10 in H20; inversion H20.
- transitivity C2; auto.
- rewrite <- H6 in H19; elim H19; auto.
- rewrite <- H17 in H9; elim H9; auto.
- rewrite <- H17 in H9; elim H9; auto.
- rewrite (IHC1 _ _ _ _ _ _ H10 H21); rewrite (IHC2 _ _ _ _ _ _ H11 H22); auto.
Qed.

Lemma MCC_To_deterministic_2 : forall C C1 C2 tl s s1 s2,
  MCC_To Defs C s tl C1 s1 -> MCC_To Defs C s tl C2 s2 ->
  eq_state_ext s1 s2.
Proof.
induction C; intros; inversion H; inversion H0;
  try (ESEt s; ESEs; fail); eauto.
- rewrite <- H15 in H8. apply (disjoint_ps_rl_In _ _ _ H19) in H8.
  elim H8; auto.
- rewrite <- H15 in H8. apply (disjoint_ps_rl_In _ _ _ H19) in H8.
  elim H8; auto.
- rewrite <- H6 in H18. apply (disjoint_ps_rl_In _ _ _ H10) in H18.
  elim H18; auto.
- rewrite <- H6 in H18. apply (disjoint_ps_rl_In _ _ _ H10) in H18.
  elim H18; auto.
- ESEt (update s q x v).
  revert H14; unfold v, v0.
  rewrite <- H1 in H8; inversion H8.
  ESEs.
- rewrite <- H4 in H11; inversion H11.
- rewrite <- H1, <- H4 in H10.
  inversion_clear H10. inversion H16. elim H10; auto.
- rewrite <- H4 in H11; inversion H11.
- rewrite <- H1, <- H4 in H10.
  inversion_clear H10. inversion H16. elim H10; auto.
- rewrite <- H9, <- H12 in H3.
  inversion_clear H3. inversion H16. elim H3; auto.
- rewrite <- H9, <- H12 in H3.
  inversion_clear H3. inversion H16. elim H3; auto.
- rewrite <- H6 in H19; elim H19; auto.
- rewrite <- H6 in H19; elim H19; auto.
- rewrite <- H17 in H9; elim H9; auto.
- rewrite <- H17 in H9; elim H9; auto.
Qed.

Lemma MCC_To_deterministic : forall C C1 C2 tl1 tl2 s s1 s2,
  MCC_To Defs C s tl1 C1 s1 -> MCC_To Defs C s tl2 C2 s2 ->
  tl1 = tl2 -> C1 = C2 /\ eq_state_ext s1 s2.
Proof.
intros.
rewrite H1 in H; split.
eapply MCC_To_deterministic_1; eauto.
eapply MCC_To_deterministic_2; eauto.
Qed.

(** Conversely: the result choreography determines the transition label
  and resulting state. *)

Lemma MCC_To_eta_reduction : forall eta C s1 s2 tl,
  MCC_To Defs (eta;;C) s1 tl C s2 ->
  (forall p e q x, eta = (p # e --> q $ x)%MC -> tl = R_Com p (eval_on_state e s1 p) q x)
  /\
  (forall p q l, eta = (p --> q[l])%MC -> tl = R_Sel p q l).
Proof.
induction C; intros; inversion H; split; intros;
  try (unfold v); try (inversion H6; auto; fail).
+ clear s' H5 C' H6 t H4 s H3 eta0 H0 C0 H1.
  rewrite H2, H9 in IHC; rewrite H9 in H7, H8.
  clear e H9 H2 H.
  elim (IHC _ _ _ H8); auto.
+ clear s' H5 C' H6 t H4 s H3 eta0 H0 C0 H1.
  rewrite H2, H9 in IHC; rewrite H9 in H7, H8.
  clear e H9 H2 H.
  elim (IHC _ _ _ H8); auto.
Qed.

Lemma MCC_To_Then_reduction : forall p b C1 C2 s1 s2 tl,
  MCC_To Defs (If p ? b Then C1 Else C2) s1 tl C1 s2 ->
  tl = R_Cond p.
Proof.
induction C1; intros; inversion H; auto.
rewrite <- H7, <- H8 in H12; rewrite <- H7.
apply (IHC1_1 _ _ _ _ H12).
Qed.

Lemma MCC_To_Else_reduction : forall p b C1 C2 s1 s2 tl,
  MCC_To Defs (If p ? b Then C1 Else C2) s1 tl C2 s2 ->
  tl = R_Cond p.
Proof.
intros p b C1 C2; revert C1.
induction C2; intros; inversion H; auto.
rewrite <- H7, <- H8 in H13; rewrite <- H7.
apply (IHC2_2 _ _ _ _ H13).
Qed.

Lemma MCC_To_Call_reduction_1 : forall p X s1 s2 tl,
  initial (snd (Defs X)) -> In p (fst (Defs X))
  -> MCC_To Defs (Call X) s1 tl (snd (Defs X)) s2
  -> tl = R_Call X p.
Proof.
intros.
set (C:=snd (Defs X)). assert (C = snd (Defs X)); auto.
clearbody C. revert p X s1 s2 tl H H0 H1 H2.
induction C; intros; inversion H1;
  try (rewrite (set_size_1 _ _ H5 _ _ H0 H6); auto; fail);
  try (rewrite <- H4 in H; simpl in H; inversion H).
Qed.

Lemma MCC_To_Call_reduction_2 : forall p X s1 s2 tl,
  initial (snd (Defs X)) -> In p (fst (Defs X))
  -> MCC_To Defs (Call X) s1 tl (RT_Call X (set_remove_pid p (fst (Defs X))) (snd (Defs X))) s2
  -> tl = R_Call X p.
Proof.
intros.
set (C:=snd (Defs X)). assert (C = snd (Defs X)); auto.
clearbody C. revert p X s1 s2 tl H H0 H1 H2.
induction C; intros; inversion H1;
  try (rewrite H4 in H; simpl in H; inversion H);
  try rewrite (set_remove'_cross _ _ _ _ H9 H4); auto.
Qed.

Lemma MCC_To_Call_reduction_3 : forall C p ps X s1 s2 tl,
  In p ps ->
  MCC_To Defs (RT_Call X ps C) s1 tl (RT_Call X (set_remove_pid p ps) C) s2 ->
  tl = R_Call X p.
Proof.
induction C; intros; inversion H0;
  try (rewrite (set_remove'_cross _ _ _ _ H10 H4); auto; fail);
  try (rewrite H7 in H; apply set_remove'_2 in H; elim H; auto; fail).
rewrite (set_size_1 _ _ H11 _ _ H H12); auto.
Qed.

Fixpoint C_size (C:Choreography) :=
match C with
| RT_Call _ _ C' => S (C_size C')
| (Eta;; C')%MC  => S (C_size C')
| Cond _ _ C1 C2 => S (C_size C1 + C_size C2)
| _              => 0
end.

Fixpoint subterm (C1 C2:Choreography) : Prop :=
match C2 with
| (Eta;;C')%MC     => C1 = C' \/ subterm C1 C'
| Cond _ _ C1' C2' => C1 = C1' \/ C1 = C2' \/ subterm C1 C1' \/ subterm C1 C2'
| RT_Call _ _ C'   => C1 = C' \/ subterm C1 C'
| _                => False
end.

Lemma subterm_size : forall C C', subterm C C' -> C_size C < C_size C'.
Proof.
intros C C'; revert C; induction C'; simpl; intros; inversion H; try rewrite H0; auto with arith.
inversion_clear H0. rewrite H1; auto with arith.
inversion_clear H1.
+ transitivity (C_size C'1); auto with arith.
+ transitivity (C_size C'2); auto with arith.
Qed.

Lemma subterm_not_equal : forall C C', subterm C C' -> C <> C'.
Proof.
intros; intro.
generalize (subterm_size _ _ H); intro.
rewrite H0 in H1.
apply (lt_irrefl _ H1).
Qed.

Lemma MCC_To_Call_reduction_4 : forall C p ps X s1 s2 tl,
  In p ps -> MCC_To Defs (RT_Call X ps C) s1 tl C s2
  -> tl = R_Call X p.
Proof.
induction C; intros; inversion H0; auto;
  try (rewrite (set_size_1 _ _ H7 _ _ H H9); auto; fail);
  try (rewrite (set_size_1 _ _ H3 _ _ H H4); auto; fail).
+ clear H0 s' H6 C' H9 t H5 s H3 C0 H4 ps0 H2 X0 H1.
  rewrite <- H7; rewrite <- H7 in H11; clear r H7.
  rewrite <- H8 in H10, H11; clear l H8.
  eauto.
+ elim (subterm_not_equal C (RT_Call r (set_remove_pid p0 ps) C)); simpl; auto.
Qed.

Lemma MCC_To_deterministic_3 : forall C C' tl1 tl2 s s1 s2,
  MCC_To Defs C s tl1 C' s1 -> MCC_To Defs C s tl2 C' s2 ->
  tl1 = tl2.
Proof.
induction C; intros; inversion H; inversion H0; auto.
+ rewrite (set_size_1 _ _ H11 _ _ H12 H4); auto.
+ rewrite H3 in H11; elim (lt_irrefl _ H11).
+ rewrite H11 in H3; elim (lt_irrefl _ H3).
+ rewrite <- H7 in H15; inversion H15.
  rewrite (set_remove'_cross _ _ _ _ H12 H18); auto.
+ rewrite <- H6 in H15; inversion H15.
  rewrite <- H20 in H9; eauto.
+ rewrite <- H6 in H16; inversion H16.
  rewrite <- H21 in H19. apply set_remove'_2 in H19. elim H19; auto.
+ rewrite H16, <- H6 in H9.
  apply (MCC_To_Call_reduction_4 _ _ _ _ _ _ _ H19 H9).
+ rewrite <- H7 in H0.
  symmetry; apply (MCC_To_Call_reduction_3 _ _ _ _ _ _ _ H10 H0).
+ rewrite <- H7 in H17; inversion H17.
  rewrite (set_remove'_cross _ _ _ _ H20 H22); auto.
+ rewrite <- H19 in H9; elim (lt_irrefl _ H9).
+ rewrite H7, <- H16 in H19.
  symmetry; apply (MCC_To_Call_reduction_4 _ _ _ _ _ _ _ H10 H19).
+ rewrite <- H9 in H19; elim (lt_irrefl _ H19).
+ rewrite (set_size_1 _ _ H19 _ _ H10 H20); auto.
+ unfold v, v0; rewrite <- H1 in H8; inversion H8; auto.
+ rewrite <- H1 in H8; inversion H8; auto.
+ rewrite H5, <- H13 in H15.
  clear H H0 C0 H3 s0 H2 H5 s' H6 C1 H9 eta H8 s3 H11 t H12 s'0 H14 C' H13.
  elim (MCC_To_eta_reduction _ _ _ _ _ H15); intros.
  symmetry; apply H; auto.
+ rewrite <- H1 in H8; inversion H8; auto.
+ rewrite <- H1 in H8; inversion H8; auto.
+ rewrite H5, <- H13 in H15.
  clear H H0 C0 H3 s0 H2 H5 s' H6 C1 H9 eta H8 s3 H11 t H12 s'0 H14 C' H13.
  elim (MCC_To_eta_reduction _ _ _ _ _ H15); intros.
  symmetry; apply H0; auto.
+ rewrite H13, <- H6 in H8.
  elim (MCC_To_eta_reduction _ _ _ _ _ H8); intros.
  apply H16; auto.
+ rewrite H13, <- H6 in H8.
  elim (MCC_To_eta_reduction _ _ _ _ _ H8); intros.
  apply H17; auto.
+ revert H8 H16. rewrite <- H6 in H14; inversion H14.
  eauto.
+ rewrite H7, <- H17 in H20.
  rewrite (MCC_To_Then_reduction _ _ _ _ _ _ _ H20); auto.
+ rewrite H7, <- H17 in H21.
  rewrite (MCC_To_Else_reduction _ _ _ _ _ _ _ H21); auto.
+ rewrite H18, <- H7 in H10.
  apply (MCC_To_Then_reduction _ _ _ _ _ _ _ H10); auto.
+ rewrite H18, <- H7 in H11.
  apply (MCC_To_Else_reduction _ _ _ _ _ _ _ H11); auto.
+ revert H21 H22. rewrite <- H7 in H18; inversion H18.
  eauto.
Qed.

Lemma MCC_To_deterministic_4 : forall C C' tl1 tl2 s s1 s2,
  MCC_To Defs C s tl1 C' s1 -> MCC_To Defs C s tl2 C' s2 ->
  eq_state_ext s1 s2.
Proof.
intros.
rewrite (MCC_To_deterministic_3 _ _ _ _ _ _ _ H0 H) in H0.
eapply MCC_To_deterministic_2; eauto.
Qed.

(** The label alone determines the resulting state. *)

Lemma MCC_To_rl_implies_state : forall C1 s tl C1' s1 C2 C2' s2,
  MCC_To Defs C1 s tl C1' s1 -> MCC_To Defs C2 s tl C2' s2 ->
  eq_state_ext s1 s2.
Proof.
induction C1; induction C2; intros; inversion H; inversion H0;
  try (ESEt s; ESEs; fail); eauto;
  try (rewrite <- H4 in H13; inversion H13; fail);
  try (rewrite <- H6 in H14; inversion H14; fail).
+ rewrite <- H6 in H12; inversion H12.
+ rewrite <- H6 in H12; inversion H12.
+ ESEt (update s q x v). ESEs. ESEt (update s q0 x0 v0).
  rewrite <- H4 in H11; inversion H11. ESEr.
+ rewrite <- H4 in H11; inversion H11.
+ rewrite <- H4 in H11; inversion H11.
Qed.

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
Lemma diamond_3 : forall P s tl1 tl2 P1 s1 P2 s2,
  (P,s) --[ tl1 ]-->* (P1,s1) -> (P,s) --[ tl2 ]--> (P2,s2) ->
  (exists tl' s1', (P2,s2) --[ tl' ]-->* (P1,s1') /\ eq_state_ext s1 s1')
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
      rewrite <- H8; ESEs.
    * rewrite <- H2. exists s1; split. 2: ESEr.
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

Lemma diamond_4 : forall P s tl1 tl2 P1 s1 P2 s2,
  (P,s) --[ tl1 ]-->* (P1,s1) -> (P,s) --[ tl2 ]-->* (P2,s2) ->
  (exists P' tl1' tl2' s1' s2',
    (P1,s1) --[ tl1' ]-->* (P',s1') /\ (P2,s2) --[ tl2' ]-->* (P',s2') /\ eq_state_ext s1' s2').
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
  elim (diamond_3 _ _ _ _ _ _ _ _ H H4); intros.
  - destroy H0.
    rename x into tl', x0 into s', Main0 into C0.
    elim (IHtl2 _ _ _ _ _ _ _ H1 H6); intros.
    destroy H2.
    induction x.
    rewrite <- (MCP_ToStar_Defs_stable _ _ _ _ _ _ _ H3) in H5, H3; clear Procedures0.
    rename Main0 into C', x0 into tl1', x1 into tl2', x2 into s1', x3 into s2'.
    case_eq tl1'; intros.
    * rewrite H7 in H3. inversion H3.
      rewrite <- H9; rewrite <- H9 in H3, H5; clear C' tl1' H7 H9.
      rewrite <- H11 in H3, H2. clear s1' H11 c H8.
      exists (Build_Program Defs C1), nil, tl2', s1, s2'; repeat split; auto.
      constructor. ESEt s'.
    * exists (Build_Program Defs C'), tl1', tl2', s1', s2'; repeat split; auto.
      apply MCP_ToStar_eq with s' s1'; auto. ESEs. ESEr. rewrite H7; discriminate.
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
