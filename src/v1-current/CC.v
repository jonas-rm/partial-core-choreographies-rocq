Require Export Basic.
Require Export Common.

(** * The general type of Core Choreographies
  This type is parameterized over sets of process identifiers,
  values, expressions and recursion variables. A lot of stuff
  is common with SP, and was defined already in [Common].*)

Record Signature :=
  { pid    : DecType;
    var    : DecType;
    value  : DecType;
    expr   : DecType;
    bexpr  : DecType;
    recvar : DecType;
    ann    : DecType;
    ev     : @Eval expr var value value;
    bev    : @Eval bexpr var value Bool}.

Notation "X [\] x" := (set_remove' (@eq_dec (pid _)) x X) (at level 50).
Notation "[#] X" := (set_size (@eq_dec (pid _)) X) (at level 40).
Notation "X [U] Y" := (set_union (@eq_dec (pid _)) X Y) (at level 50).
Notation "X [C] Y" := (@set_incl (pid _) X Y) (at level 40).

Section CCBase.

Variable Sig : Signature.

Notation Pid := (pid Sig).
Notation Var := (var Sig).
Notation Value := (value Sig).
Notation Expr := (expr Sig).
Notation BExpr := (bexpr Sig).
Notation RecVar := (recvar Sig).
Notation Ann := (ann Sig).
Notation Ev := (ev Sig).
Notation BEv := (bev Sig).

Notation PSt := (LState Value Var).
Notation Store := (State Pid Var Value).

(** ** Syntax of Core Choreographies. *)

Section Syntax.

(** Communication actions. *)

Inductive Eta : Type :=
 | Com : Pid -> Expr -> Pid -> Var -> Eta
 | Sel : Pid -> Pid -> Label -> Eta
.

Lemma eta_eq_dec : forall (eta eta':Eta), { eta = eta' } + { eta <> eta' }.
Proof. decide equality; apply eq_dec. Qed.

(** Choreographies. *)

Inductive Choreography : Type :=
 | Interaction : Eta -> Ann -> Choreography -> Choreography
 | Cond        : Pid -> BExpr -> Choreography -> Choreography -> Choreography
 | Call        : RecVar -> Choreography
 | RT_Call     : RecVar -> (list Pid) -> Choreography -> Choreography
 | End         : Choreography
.

(** A program is a pair containing all procedure definitions and the main
    choreography.

  Procedure definitions are functions from a variable number of processes to
  choreographies, without free process names. We model this as a function
  returning a pair (list Pid)*Choreography, with the proviso that all processes
  occurring in the choreography must be included in the list of processes.
 *)

Definition DefSet := RecVar -> (list Pid)*Choreography.

Definition Program : Type := DefSet * Choreography.

Definition Procedures : Program -> DefSet := (@fst _ _).
Definition Main : Program -> Choreography := (@snd _ _ ).

Definition Vars := fun P X => fst (Procedures P X).
Definition Procs := fun P X => snd (Procedures P X).

Definition Names (D:DefSet) := fun X => fst (D X).

End Syntax.

(** Pretty-printing rules for choreographies. *)

Declare Scope CC_scope.
Delimit Scope CC_scope with CC.

Bind Scope CC_scope with Choreography.
Bind Scope CC_scope with Eta.

Notation "p # e --> q $ x" := (Com p e q x)
          (at level 50, e at level 9) : CC_scope.
Notation "p --> q [ l ]" := (Sel p q l)
          (at level 50) : CC_scope.
Notation "eta '@' ann ';;' C" := (Interaction eta ann C)
          (at level 60, right associativity) : CC_scope.
Notation "'If' p '??' b 'Then' C1 'Else' C2" := (Cond p b C1 C2)
          (at level 60) : CC_scope.

Open Scope CC_scope.

Section Syntactic_Properties.

(** Syntactic properties of choreographies and programs. *)

Lemma chor_eq_dec : forall (C C':Choreography), { C = C' } + { C <> C' }.
Proof.
decide equality; try apply eq_dec.
apply eta_eq_dec.
apply list_eq_dec, eq_dec.
Qed.

(** An initial choreography is what a programmer should write. *)
Fixpoint initial (C:Choreography) : Prop :=
match C with
| Interaction _ _ C' => initial C'
| Cond _ _ C1 C2     => initial C1 /\ initial C2
| Call _             => True
| RT_Call _ _ _      => False
| End                => True
end.

Lemma initial_dec : forall C, {initial C} + {~initial C}.
Proof.
induction C; simpl; auto.
inversion_clear IHC1; inversion_clear IHC2; auto;
  right; intro; inversion_clear H1; auto.
Qed.

(** Free procedure names in a choreography. *)
Definition set_union_rv := set_union (@eq_dec RecVar).

Fixpoint Free_RecVar (C:Choreography) : list RecVar :=
match C with  
| Interaction _ _ C' => Free_RecVar C'
| Cond _ _ C1 C2     => set_union_rv (Free_RecVar C1) (Free_RecVar C2)
| Call Y             => (Y::nil)
| RT_Call Y _ C'     => set_union_rv (Y::nil) (Free_RecVar C')
| End                => nil
end.

Definition X_Free (X:RecVar) (C:Choreography) : Prop := In X (Free_RecVar C).

Lemma X_Free_dec : forall X C, {X_Free X C} + {~X_Free X C}.
Proof.
induction C; unfold X_Free; simpl; auto.
+ (* Cond *)
  inversion_clear IHC1; [idtac | inversion_clear IHC2].
  - left. apply set_union_intro1; auto.
  - left. apply set_union_intro2; auto.
  - right; intro.
    elim (set_union_elim _ _ _ _ H1); auto.
+ (* Call *)
  elim (eq_dec X t); simpl; auto.
  right; intro. inversion_clear H; auto.
+ (* RT_Call *)
  unfold set_union_rv. simpl.
  inversion_clear IHC.
  - left. apply set_union_intro2; auto.
  - elim (eq_dec X t); simpl; intro.
    * left. rewrite a. apply set_union_intro1; simpl; auto.
    * right; intro.
      elim (set_union_elim _ _ _ _ H0); auto.
      simpl. intro. inversion_clear a; auto.
Qed.

(** Inversion results for bound variables. *)

Lemma X_Free_Eta : forall X ann eta C, X_Free X (eta @ ann;;C) -> X_Free X C.
Proof. intros. apply H. Qed.

Lemma X_Free_Cond : forall X p b C1 C2,
  X_Free X (If p ?? b Then C1 Else C2) -> {X_Free X C1} + {X_Free X C2}.
Proof.
intros. red in H. simpl in H.
elim (set_union_elim _ _ _ _ H); auto.
Qed.

Lemma Not_X_Free_Eta : forall X ann eta C, ~X_Free X (eta @ ann;;C) -> ~X_Free X C.
Proof.
intros. intro. apply H. red. simpl. auto.
Qed.

Lemma Not_X_Free_Then : forall X p b C1 C2,
  ~X_Free X (If p ?? b Then C1 Else C2) -> ~X_Free X C1.
Proof.
intros. intro. apply H. red. simpl. apply set_union_intro1. auto.
Qed.

Lemma Not_X_Free_Else : forall X p b C1 C2,
  ~X_Free X (If p ?? b Then C1 Else C2) -> ~X_Free X C2.
Proof.
intros. intro. apply H. red. simpl. apply set_union_intro2. auto.
Qed.

(** The set of process names in a choreography. *)

Definition eta_pn (e:Eta) : list Pid :=
match e with
| Com p _ q _ => (p::q::nil)
| Sel p q _   => (p::q::nil)
end.

Fixpoint CCC_pn (C:Choreography) (Pids:RecVar -> list Pid) : list Pid :=
match C with
| Interaction eta _ C' => (eta_pn eta [U] CCC_pn C' Pids)
| Cond p _ C1 C2       => ((p::nil) [U] CCC_pn C1 Pids [U] CCC_pn C2 Pids)
| Call X               => Pids X
| RT_Call _ l C'       => l [U] CCC_pn C' Pids
| End                  => nil
end.

Ltac sup := rewrite set_union_iff; auto.

Lemma CCC_pn_mon : forall X Y, (forall Z p, In p (X Z) -> In p (Y Z)) ->
  forall C p, In p (CCC_pn C X) -> In p (CCC_pn C Y).
Proof.
induction C; simpl; auto.
+ intro. sup; sup. intro. elim H0; auto.
+ intro. sup; sup; sup; sup. intro. elim H0; auto.
  intro. elim H1; auto.
+ intro. sup; sup. intro. elim H0; auto.
Qed.

(** A choreography is well-formed if:
    - it does not contain self-communications;
    - annotations of runtime terms are not empty.
*)

(** No process attempts to communicate with itself. *)

Fixpoint no_self_comm (C:Choreography) : Prop :=
match C with
| Interaction eta _ C' => match eta with
                          | Com p _ q _ => p <> q
                          | Sel p q _   => p <> q
                          end /\ no_self_comm C'
| Cond _ _ C1 C2       => no_self_comm C1 /\ no_self_comm C2
| Call _               => True
| RT_Call _ _ C'       => no_self_comm C'
| End                  => True
end.

Lemma no_self_comm_dec : forall C, {no_self_comm C} + {~no_self_comm C}.
Proof.
induction C; simpl; auto.
+ (* Eta *)
  inversion_clear IHC.
  - induction e; simpl; auto.
    * case_eq (t0 =? t2); simpl; intros.
      ++ right; intro.
         inversion_clear H1.
         apply H2; apply eqb_eq; auto.
      ++ left; split; auto.
         apply eqb_neq; auto.
    * case_eq (t0 =? t1); simpl; intros.
      ++ right; intro.
         inversion_clear H1.
         apply H2; apply eqb_eq; auto.
      ++ left; split; auto.
         apply eqb_neq; auto.
  - right; intro.
    inversion_clear H0; auto.
+ (* Cond *)
  inversion_clear IHC1; inversion_clear IHC2; auto;
  right; intro; inversion_clear H1; auto.
Qed.

(** There are no procedure calls with empty annotations. *)

Fixpoint no_empty_ann (C:Choreography) : Prop :=
match C with
| Interaction eta _ C' => no_empty_ann C'
| Cond _ _ C1 C2       => no_empty_ann C1 /\ no_empty_ann C2
| Call _               => True
| RT_Call _ l C'       => l <> nil /\ no_empty_ann C'
| End                  => True
end.

Lemma no_empty_ann_dec : forall C, {no_empty_ann C} + {~no_empty_ann C}.
Proof.
induction C; simpl; auto.
+ (* Cond *)
  inversion_clear IHC1; inversion_clear IHC2; auto;
  right; intro; inversion_clear H1; auto.
+ (* RT_Call *)
  inversion_clear IHC.
  - elim (destruct_list l).
    * left; split; auto.
      inversion_clear a.
      inversion_clear X.
      rewrite H0; discriminate.
    * right; intro.
      inversion_clear H0; auto.
  - right; intro.
    inversion_clear H0; auto.
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

Lemma Choreography_WF_no_self_comm : forall C, Choreography_WF C -> no_self_comm C.
Proof. intros. inversion_clear H. auto. Qed.

Lemma Choreography_WF_no_empty_ann : forall C, Choreography_WF C -> no_empty_ann C.
Proof. intros. inversion_clear H. auto. Qed.

(** Inversion results. *)
Lemma Choreography_WF_eta : forall ann eta C,
  Choreography_WF (eta @ ann;;C) -> Choreography_WF C.
Proof.
intros.
inversion_clear H; simpl in H0, H1.
split; auto.
inversion_clear H0; auto.
Qed.

Lemma Choreography_WF_Then : forall p b C1 C2,
  Choreography_WF (If p ?? b Then C1 Else C2) -> Choreography_WF C1.
Proof.
intros.
destroy H; destroy H0; split; auto.
Qed.

Lemma Choreography_WF_Else : forall p b C1 C2,
  Choreography_WF (If p ?? b Then C1 Else C2) -> Choreography_WF C2.
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
  Choreography_WF (RT_Call X ps C) -> [#] ps > 1 ->
  Choreography_WF (RT_Call X (ps [\] p) C).
Proof.
intros.
destroy H; repeat split; auto.
elim (In_dec (@eq_dec Pid) p ps); intro.
+ rewrite (set_size_remove' (@eq_dec Pid) ps p) in H0; auto.
  apply lt_S_n in H0.
  intro; rewrite H3 in H0; inversion H0.
+ rewrite set_remove'_not_In; auto.
Qed.

(** A program is well-formed if there is a finite set of procedures Xs such that:
    - main and all procedures in Xs are well-formed
    - all procedures in Xs are initial
    - main and all procedures in Xs only call procedures in Xs
    - annotations in main are consistent
*)

Fixpoint within_Xs (Xs:list RecVar) (C:Choreography) : Prop :=
match C with
| Interaction _ _ C' => within_Xs Xs C'
| Cond _ _ C1 C2     => within_Xs Xs C1 /\ within_Xs Xs C2
| Call X             => In X Xs
| RT_Call X _ C'     => In X Xs /\ within_Xs Xs C'
| End                => True
end.

Lemma within_Xs_dec : forall Xs C, {within_Xs Xs C} + {~within_Xs Xs C}.
Proof.
induction C; simpl; auto.
+ (* Cond *)
  inversion_clear IHC1; inversion_clear IHC2; auto;
  right; intro; destroy H1; auto.
+ (* Call *)
  apply In_dec, eq_dec.
+ (* RT_Call *)
  inversion_clear IHC; [elim (In_dec (@eq_dec _) t Xs) | idtac]; intros.
  - left; split; auto.
  - right; intro; apply b.
    destroy H0; auto.
  - right; intro; apply H.
    destroy H0; auto.
Qed.

Lemma within_Xs_incl : forall C Xs Ys,
  (forall X, In X Xs -> In X Ys) -> within_Xs Xs C -> within_Xs Ys C.
Proof.
induction C; simpl; auto;
  intros; inversion_clear H0; split; eauto.
Qed.

Lemma within_Xs_char : forall Xs C, within_Xs Xs C ->
  forall X, X_Free X C -> In X Xs.
Proof.
unfold X_Free.
induction C; auto; simpl; unfold set_union_rv; intros; destroy H.
- rewrite set_union_iff in H0. inversion H0; auto.
- inversion_clear H0; inversion H1. rewrite <- H1; auto.
- rewrite set_union_iff in H0. inversion H0; auto.
  inversion H2; inversion H3; auto. rewrite <- H3; auto.
- inversion H0.
Qed.

Fixpoint consistent (Xs:RecVar -> list Pid) (C:Choreography) : Prop :=
match C with
| Interaction _ _ C' => consistent Xs C'
| Cond _ _ C1 C2     => consistent Xs C1 /\ consistent Xs C2
| Call X             => True
| RT_Call X l C'     => l [C] Xs X /\ consistent Xs C'
| End                => True
end.

Lemma consistent_dec : forall Xs C, {consistent Xs C} + {~consistent Xs C}.
Proof.
induction C; simpl; auto.
+ (* Cond *)
  elim IHC1. 2: right; tauto.
  elim IHC2; tauto.
+ (* RT_Call *)
  elim IHC. 2: right; tauto.
  elim (set_incl_dec (@eq_dec _) l (Xs t)); tauto.
Qed.

Lemma initial_consistent : forall C, initial C -> forall Xs, consistent Xs C.
Proof.
induction C; auto; simpl; intros; inversion H.
split; auto.
Qed.

(** We need to consider the list of used process variables. *)

Definition Program_WF (Xs:list RecVar) (P:Program) : Prop :=
  Choreography_WF (Main P) /\ within_Xs Xs (Main P) /\
  consistent (Vars P) (Main P) /\
  forall X, In X Xs -> Choreography_WF (Procs P X) /\ initial (Procs P X) /\
            (Vars P X) <> nil /\ within_Xs Xs (Procs P X).

Lemma Program_WF_dec : forall Xs P, {Program_WF Xs P} + {~Program_WF Xs P}.
Proof.
intros.
elim (Choreography_WF_dec (Main P)); intros.
2: right; intro; destroy H; auto.
elim (within_Xs_dec Xs (Main P)); intros.
2: right; intro; destroy H; auto.
elim (consistent_dec (Vars P) (Main P)); intros.
2: right; intro; destroy H; auto.
assert (forall (Ys:list RecVar), {forall X, In X Ys -> Choreography_WF (Procs P X) /\ initial (Procs P X) /\
            (Vars P X) <> nil /\ within_Xs Xs (Procs P X)} +
        {~forall X, In X Ys -> Choreography_WF (Procs P X) /\ initial (Procs P X) /\
            (Vars P X) <> nil /\ within_Xs Xs (Procs P X)}); intros.
2: { elim (X Xs); clear X; intros.
  left; repeat (split; auto).
  right; intro. destroy H; auto.
}
clear a a0 a1.
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

Lemma Program_WF_consistent : forall P Xs, Program_WF Xs P ->
  consistent (Vars P) (Main P).
Proof. intros. destroy H; auto. Qed.

Lemma Program_WF_initial_Proc : forall P Xs, Program_WF Xs P ->
  forall X, In X Xs -> initial (Procs P X).
Proof. intros. destroy H. elim (H X); auto. intros. destroy H5; auto. Qed.

Lemma Program_WF_Main_within_Xs : forall P Xs, Program_WF Xs P ->
  within_Xs Xs (Main P).
Proof. intros. destroy H; auto. Qed.

Lemma Program_WF_Vars_In : forall P Xs, Program_WF Xs P ->
  forall X, X_Free X (Main P) -> In X Xs.
Proof.
intros.
destroy H. clear H.
induction P as (D,C).
simpl in H0, H2. clear H1.
induction C; auto.
+ (* Cond *)
  inversion_clear H2. inversion_clear H3.
  elim (set_union_elim _ _ _ _ H0); auto.
+ (* Call *)
  inversion H0. rewrite H in H2; simpl in H2; auto. inversion H.
+ (* RT_Call *)
  inversion_clear H3. inversion_clear H2. red in H0. simpl in H0.
  elim (set_union_elim _ _ _ _ H0); intros; auto.
  inversion_clear a. rewrite H2 in H3; auto. inversion H2.
+ (* End *)
  inversion H0.
Qed.

Lemma Program_WF_Vars : forall P Xs, Program_WF Xs P ->
  forall X, In X Xs -> Vars P X <> nil.
Proof. intros. destroy H. elim (H X); auto. intros. destroy H5; auto. Qed.

Lemma Program_WF_within_Xs : forall P Xs, Program_WF Xs P ->
  forall X, In X Xs -> within_Xs Xs (Procs P X).
Proof. intros. destroy H. elim (H X); auto. intros. destroy H5; auto. Qed.

(** Inversion results. *)

Lemma Program_WF_Main_change : forall Xs D C C',
  Choreography_WF C' -> within_Xs Xs C' -> consistent (Names D) C' ->
  Program_WF Xs (D,C) -> Program_WF Xs (D,C').
Proof.
intros.
destroy H2; repeat (split; auto).
Qed.

Lemma Program_WF_eta : forall Xs D C ann eta,
  Program_WF Xs (D,eta @ ann;;C) -> Program_WF Xs (D,C).
Proof.
intros.
elim (Program_WF_Main _ _ H); simpl; intros.
inversion_clear H0.
eapply Program_WF_Main_change; eauto.
eapply Choreography_WF_eta with (ann:=ann0); repeat split; eauto.
apply (Program_WF_Main_within_Xs _ _ H).
destroy H; auto.
Qed.

Lemma Program_WF_Then : forall Xs D p b C1 C2,
  Program_WF Xs (D,If p ?? b Then C1 Else C2) -> Program_WF Xs (D,C1).
Proof.
intros.
elim (Program_WF_Main _ _ H); simpl; intros.
inversion_clear H0; inversion_clear H1.
eapply Program_WF_Main_change; eauto.
apply Choreography_WF_Then with p b C2; repeat split; auto.
apply (Program_WF_Main_within_Xs _ _ H).
destroy H. inversion_clear H6; auto.
Qed.

Lemma Program_WF_Else : forall Xs D p b C1 C2,
  Program_WF Xs (D,If p ?? b Then C1 Else C2) -> Program_WF Xs (D,C2).
Proof.
intros.
elim (Program_WF_Main _ _ H); simpl; intros.
inversion_clear H0; inversion_clear H1.
eapply Program_WF_Main_change; eauto.
apply Choreography_WF_Else with p b C1; repeat split; auto.
apply (Program_WF_Main_within_Xs _ _ H).
destroy H. inversion_clear H6; auto.
Qed.

Lemma Program_WF_Call : forall Xs D X ps C,
  Program_WF Xs (D,RT_Call X ps C) -> Program_WF Xs (D,C).
Proof.
intros.
elim (Program_WF_Main _ _ H); simpl; intros.
inversion_clear H1.
eapply Program_WF_Main_change; eauto.
split; auto.
apply (Program_WF_Main_within_Xs _ _ H).
destroy H. inversion_clear H5; auto.
Qed.

(** A program is well-annotated if every process used by a procedure is in its annotation. *)

Definition well_ann (P:Program) : Prop :=
  forall X, CCC_pn (Procs P X) (Vars P) [C] Vars P X.

Lemma well_ann_Main_change : forall D C C', well_ann (D,C) -> well_ann (D,C').
Proof.
intros.
intro.
unfold Procs, Vars; simpl.
apply H.
Qed.

(** This one is not decidable. *)

Definition CCP_WF (P:Program) := well_ann P /\ exists Xs, Program_WF Xs P.

Lemma CCP_WF_Main : forall P, CCP_WF P -> Choreography_WF (Main P).
Proof.
intros.
inversion_clear H; inversion_clear H1.
apply Program_WF_Main with x; auto.
Qed.

Lemma CCP_WF_Vars : forall P, CCP_WF P ->
  forall X, X_Free X (Main P) -> Vars P X <> nil.
Proof.
intros.
inversion_clear H; inversion_clear H2.
rename x into Xs.
apply Program_WF_Vars with Xs; auto.
apply Program_WF_Vars_In with P; auto.
Qed.

Lemma CCP_WF_eta : forall D C ann eta, CCP_WF (D,eta @ ann;;C) -> CCP_WF (D,C).
Proof.
intros.
inversion_clear H; inversion_clear H1.
split; auto. exists x; auto. eapply Program_WF_eta; eauto.
Qed.

Lemma CCP_WF_Then : forall D p b C1 C2,
  CCP_WF (D,If p ?? b Then C1 Else C2) -> CCP_WF (D,C1).
Proof.
intros.
inversion_clear H; inversion_clear H1.
split; auto. exists x; auto. eapply Program_WF_Then; eauto.
Qed.

Lemma CCP_WF_Else : forall D p b C1 C2,
  CCP_WF (D,If p ?? b Then C1 Else C2) -> CCP_WF (D,C2).
Proof.
intros.
inversion_clear H; inversion_clear H1.
split; auto. exists x; auto. eapply Program_WF_Else; eauto.
Qed.

Lemma CCP_WF_Call : forall D X ps C, CCP_WF (D,RT_Call X ps C) -> CCP_WF (D,C).
Proof.
intros.
inversion_clear H; inversion_clear H1.
split; auto. exists x; auto. eapply Program_WF_Call; eauto.
Qed.

End Syntactic_Properties.

Ltac sup := rewrite set_union_iff; auto.

(** ** Semantics of CC. *)

Section Semantics_Definitions.

(** The next definition and lemmas extend some lemmas in module
  [Transitions] to communication actions, which are specific to
  CC. *)

Definition disjoint_eta_rl (eta:Eta) (t:RichLabel Pid Value Var RecVar) : Prop :=
match eta with
| p # _ --> q $ _ => disjoint_p_rl p t /\ disjoint_p_rl q t
| p --> q [_]     => disjoint_p_rl p t /\ disjoint_p_rl q t
end.

Lemma disjoint_Sel_Sel : forall p q l p' q' l',
  disjoint_eta_rl (p --> q[l]) (RL_Sel p' q' l') ->
  disjoint (p::q::nil) (p'::q'::nil).
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
  disjoint_eta_rl (p#e --> q$x) (RL_Com p' v q' x') ->
  disjoint (p::q::nil) (p'::q'::nil).
Proof. intros. apply disjoint_Sel_Sel with left right; auto. Qed.

Lemma disjoint_Com_Sel : forall p q e x p' q' l,
  disjoint_eta_rl (p#e --> q$x) (RL_Sel p' q' l) ->
  disjoint (p::q::nil) (p'::q'::nil).
Proof. intros. apply disjoint_Sel_Sel with l left; auto. Qed.

Lemma disjoint_Sel_Com : forall p q l p' v q' x,
  disjoint_eta_rl (p --> q[l]) (RL_Com p' x q' v) ->
  disjoint (p::q::nil) (p'::q'::nil).
Proof. intros. apply disjoint_Sel_Sel with l left; auto. Qed.

(** One-step and multi-step reduction. Multi-step reduction is simply a reflexive and transitive closure. *)

Inductive CCC_To (D : DefSet) :
  Choreography -> Store -> (RichLabel Pid Value Var RecVar)
               -> Choreography -> Store -> Prop :=
 | C_Com p e q x a C s s' : let v := eval_on_state Ev e s p in
        s' [==] (s[[q,x => v]]) ->
        CCC_To D (p#e --> q$x @ a ;; C) s (RL_Com p v q x) C s'
 | C_Sel p q l a C s s': s [==] s' ->
        CCC_To D (p --> q [l] @ a ;; C) s (RL_Sel p q l) C s'
 | C_Then p b C1 C2 s s': s [==] s' ->
        eval_on_state BEv b s p = true ->
        CCC_To D (If p ?? b Then C1 Else C2) s (RL_Cond p) C1 s'
 | C_Else p b C1 C2 s s': s [==] s' ->
        eval_on_state BEv b s p = false ->
        CCC_To D (If p ?? b Then C1 Else C2) s (RL_Cond p) C2 s'
 | C_Delay_Eta eta ann C C' s s' t: disjoint_eta_rl eta t -> 
        CCC_To D C s t C' s' ->
        CCC_To D (eta @ ann;; C) s t (eta @ ann;; C') s'
 | C_Delay_Cond p b C1 C2 C1' C2' s s' t: disjoint_p_rl p t -> 
        CCC_To D C1 s t C1' s' ->
        CCC_To D C2 s t C2' s' ->
        CCC_To D (If p ?? b Then C1 Else C2) s t
                    (If p ?? b Then C1' Else C2') s'
 | C_Delay_Call ps X C C' s s' t:
        disjoint_ps_rl ps t -> CCC_To D C s t C' s' ->
        CCC_To D (RT_Call X ps C) s t (RT_Call X ps C') s'
 | C_Call_Local p X s s': s [==] s' ->
        [#] (fst (D X)) = 1 -> In p (fst (D X)) ->
        CCC_To D (Call X) s (RL_Call X p) (snd (D X)) s'
 | C_Call_Start p X s s': s [==] s' ->
        [#] (fst (D X)) > 1 -> In p (fst (D X)) ->
        CCC_To D (Call X) s (RL_Call X p)
                 (RT_Call X (fst (D X) [\] p) (snd (D X))) s'
 | C_Call_Enter p ps X C s s': s [==] s' ->
        [#] ps > 1 -> In p ps ->
        CCC_To D (RT_Call X ps C) s (RL_Call X p)
                 (RT_Call X (ps [\] p) C) s'
 | C_Call_Finish p ps X C s s': s [==] s' ->
        [#] ps = 1 -> In p ps ->
        CCC_To D (RT_Call X ps C) s (RL_Call X p) C s'
.

Notation "<< C , s >> --[ rl , D ]--> << C' , s' >>" :=
  (CCC_To D C s rl C' s') (at level 100).

(** Useful for inferring a transition automatically. *)

Lemma C_Com' : forall D p e q x a C s, let v := (eval_on_state Ev e s p) in
        <<p#e --> q$x @ a;; C,s>> --[RL_Com p v q x,D]--> <<C,s[[q,x => v]]>>.
Proof. intros. apply C_Com. ESEr. Qed.

Lemma C_Sel' : forall D p q l a C s,
        <<p --> q[l] @ a;; C,s>> --[RL_Sel p q l,D]--> <<C,s>>.
Proof. intros. apply C_Sel. ESEr. Qed.

Lemma C_Then' : forall D p b C1 C2 s, eval_on_state BEv b s p = true ->
        <<If p ?? b Then C1 Else C2,s>> --[RL_Cond p,D]--> <<C1,s>>.
Proof. intros. apply C_Then. ESEr. auto. Qed.

Lemma C_Else' : forall D p b C1 C2 s, eval_on_state BEv b s p = false ->
        <<If p ?? b Then C1 Else C2,s>> --[RL_Cond p,D]--> <<C2,s>>.
Proof. intros. apply C_Else. ESEr. auto. Qed.

Lemma C_Call_Local' : forall D p X s, [#] (fst (D X)) = 1 -> In p (fst (D X)) ->
        <<Call X,s>> --[RL_Call X p,D]--> <<snd (D X),s>>.
Proof. intros. apply C_Call_Local; auto. ESEr. Qed.

Lemma C_Call_Start' : forall D p X s, [#] (fst (D X)) > 1 -> In p (fst (D X)) ->
        <<Call X,s>> --[RL_Call X p,D]-->
               <<RT_Call X (fst (D X) [\] p) (snd (D X)),s>>.
Proof. intros. apply C_Call_Start; auto. ESEr. Qed.

Lemma C_Call_Enter' : forall D p ps X C s, [#] ps > 1 -> In p ps ->
        <<RT_Call X ps C,s>> --[RL_Call X p,D]--> <<RT_Call X (ps [\] p) C,s>>.
Proof. intros. apply C_Call_Enter; auto. ESEr. Qed.

Lemma C_Call_Finish' : forall D p ps X C s, [#] ps = 1 -> In p ps ->
        <<RT_Call X ps C,s>> --[RL_Call X p,D]--> <<C,s>>.
Proof. intros. apply C_Call_Finish; auto. ESEr. Qed.

Definition Configuration : Type := Program * Store.

Inductive CCP_To : Configuration -> TransitionLabel _ _ -> Configuration -> Prop :=
 | CCP_To_intro D C s t C' s' : <<C,s>> --[t,D]--> <<C',s'>> ->
     CCP_To (D,C,s) (forget t) (D,C',s').

Inductive CCP_ToStar :
  Configuration -> list (TransitionLabel _ _) -> Configuration -> Prop :=
 | CCT_Refl c : CCP_ToStar c nil c
 | CCT_Step c1 t c2 l c3 : CCP_To c1 t c2 ->
                           CCP_ToStar c2 l c3 -> CCP_ToStar c1 (t::l) c3
.

End Semantics_Definitions.

(** Notations for reductions. *)

Notation "<< C , s >> --[ rl , D ]--> << C' , s' >>" :=
        (CCC_To D C s rl C' s') (at level 100) : CC_scope.
Notation "c --[ tl ]--> c'" := (CCP_To c tl c') (at level 50) : CC_scope.
Notation "c --[ ts ]-->* c'" := (CCP_ToStar c ts c') (at level 50) : CC_scope.

Definition Forget := @forget Pid Value Var RecVar.

Section Sanity_Checks.

Example Com_reduction : forall P p e q x a C s,
  (P,p#e --> q$x @ a;; C,s) --[TL_Com p (eval_on_state Ev e s p) q]-->
        (P,C,s[[q,x => eval_on_state Ev e s p]]).
Proof.
intros. rewrite <- (forget_Com _ Value _ RecVar x).
constructor. apply C_Com'.
Qed.

Example Sel_reduction : forall P p q l a C s,
  (P,p --> q[l] @ a;; C,s) --[TL_Sel p q l]--> (P,C,s).
Proof.
intros. rewrite <- (forget_Sel _ Value Var RecVar). constructor. apply C_Sel'.
Qed.

End Sanity_Checks.

Section BigStepSemantics.

Lemma RT_Call_reduce : forall D X ps C s, (ps <> List.nil) ->
  exists tl, (D,RT_Call X ps C,s) --[tl]-->* (D,C,s).
Proof.
intros.
set (n := [#] ps).
assert (n = [#] ps); auto.
clearbody n; revert ps H H0.
induction n; intros.
+ symmetry in H0; apply set_size_0 in H0. exfalso; auto.
+ case_eq n; intros.
  - rewrite H1 in H0; clear IHn H1 n.
    case_eq ps; intros. rewrite H1 in H; elim H; auto.
    exists (TL_Tau t::List.nil)%list.
    econstructor. 2: constructor.
    change (TL_Tau t) with (Forget (RL_Call X t)).
    constructor. apply C_Call_Finish'; [rewrite <- H1 | simpl]; auto.
  - case_eq ps; intros. rewrite H2 in H; elim H; auto.
    rewrite H1 in H0, IHn; clear n H1; rename n0 into n.
    assert (S n = [#] (ps [\] t)).
    1: {
      rewrite (set_size_remove' (@eq_dec _) ps t) in H0; auto.
      rewrite H2; simpl; auto.
    }
    elim (IHn (ps [\] t)); intros; auto.
    2: { intro. rewrite H3 in H1. simpl in H1; inversion H1. }
    rename x into tls, t into p.
    exists (TL_Tau p :: tls)%list.
    eapply CCT_Step with (D,RT_Call X (ps [\] p) C,s); auto.
    replace (TL_Tau p) with (Forget (RL_Call X p)); auto.
    constructor. rewrite H2; apply C_Call_Enter'.
    rewrite <- H2, <- H0; auto with arith.
    simpl; auto.
Qed.

Lemma Call_reduce : forall (D:DefSet) X s, (fst (D X) <> List.nil) ->
  exists tl, (D,Call X,s) --[tl]-->* (D,snd (D X),s).
Proof.
intros.
case_eq ([#] (fst (D X))); intros; [idtac | case_eq n]; intros.
+ exfalso; apply set_size_0 in H0; auto.
+ rewrite H1 in H0; clear n H1.
  case_eq (fst (D X)); intros. exfalso; auto.
  rename t into p. exists (TL_Tau p::List.nil)%list.
  econstructor. 2: constructor.
  replace (TL_Tau p) with (Forget (RL_Call X p)); auto.
  change (fst (A:=set Pid) (D X) = p::l)%list in H1.
  constructor. apply C_Call_Local'; auto. rewrite H1; simpl; auto.
+ rewrite H1 in H0; clear n H1. rename n0 into n.
  case_eq (fst (D X)); intros. exfalso; auto.
  rename t into p. assert (fst (D X) [\] p <> List.nil).
  1: {
    intro.
    rewrite (set_size_remove' (@eq_dec _) (fst (D X)) p) in H0.
    2: rewrite H1; simpl; auto.
    rewrite H2 in H0. inversion H0.
  }
  elim (RT_Call_reduce D X (fst (D X) [\] p) (snd (D X)) s); auto.
  intros.
  exists (TL_Tau p :: x)%list.
  eapply CCT_Step; eauto.
  replace (TL_Tau p) with (Forget (RL_Call X p)); auto.
  constructor. apply C_Call_Start'.
  - change ([#] (fst (A:=set Pid) (D X)) = S (S n)) in H0.
    rewrite H0; auto with arith.
  - change (fst (A:=set Pid) (D X) = p::l)%list in H1.
    rewrite H1; simpl; auto.
Qed.

Lemma CCT_Trans : forall c tl c' tl' c'',
  c --[tl]-->* c' -> c' --[tl']-->* c'' -> c --[tl++tl']-->* c''.
Proof.
intros c tl; revert c.
induction tl; simpl; intros; inversion H; auto.
simpl. apply CCT_Step with c2; auto.
apply IHtl with c'; auto.
Qed.

End BigStepSemantics.

Section Properties.

(** ** Main properties of the semantics *)

(** Determining the state from the label. *)
Lemma CCC_To_Com_state : forall D C s p v q x C' s',
  <<C,s>> --[RL_Com p v q x,D]--> <<C',s'>> -> s' [==] (s[[q,x => v]]).
Proof. induction C; intros; inversion H; eauto. Qed.

Lemma CCC_To_Sel_state : forall D C s p v l C' s',
  <<C,s>> --[RL_Sel p v l,D]--> <<C',s'>> -> s [==] s'.
Proof. induction C, l; intros; inversion H; eauto. Qed.

Lemma CCC_To_Cond_state : forall D C s p C' s',
  <<C,s>> --[RL_Cond p,D]--> <<C',s'>> -> s [==] s'.
Proof. induction C; intros; inversion H; eauto. Qed.

Lemma CCC_To_Call_state : forall D C s p X C' s',
  <<C,s>> --[RL_Call X p,D]--> <<C',s'>> -> s [==] s'.
Proof. induction C; intros; inversion H; eauto. Qed.

(** Reductions preserve well-formedness. *)

Lemma CCC_To_within_Xs : forall P s l P' s' Xs,
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
induction H; simpl; try (inversion_clear H2); auto.
Qed.

Lemma CCC_To_consistent : forall P s l P' s' Xs,
  Program_WF Xs P -> (P,s) --[l]--> (P',s') -> consistent (Vars P') (Main P').
Proof.
intros.
revert H.
inversion_clear H0.
simpl; intros.
generalize (Program_WF_consistent _ _ H0); intros.
unfold Vars in H1; simpl in H1.
unfold Vars; simpl.
generalize (Program_WF_initial_Proc _ _ H0); intros.
generalize (Program_WF_Main_within_Xs _ _ H0); simpl; intros.
unfold Procs in H2; simpl in H2.
clear H0.
induction H; auto; inversion_clear H1; auto.
1,2: inversion_clear H3; split; auto.
+ apply initial_consistent; auto.
+ split. intro; apply set_remove'_1.
  apply initial_consistent; auto.
+ split; auto.
  red; intros.
  apply set_remove'_1 in H1; auto.
Qed.

Lemma CCC_To_Program_WF : forall P s l P' s' Xs,
  Program_WF Xs P -> (P,s) --[l]--> (P',s') -> Program_WF Xs P'.
Proof.
intros.
generalize (CCC_To_within_Xs _ _ _ _ _ Xs H H0); intro HXs.
inversion H0; auto.
generalize (CCC_To_consistent _ _ _ _ _ Xs H H0); intro HXs'.
rewrite <- H1 in H; rewrite <- H5 in HXs, HXs'.
clear s'0 H6 s0 H3 H5 H0 P' H1 P H2 l.
apply Program_WF_Main_change with C; auto.
clear HXs HXs'.
generalize (Program_WF_Main _ _ H); simpl; intro HC.
induction H4.
+ eapply Choreography_WF_eta; eauto.
+ eapply Choreography_WF_eta; eauto.
+ eapply Choreography_WF_Then; eauto.
+ eapply Choreography_WF_Else; eauto.
+ inversion_clear HC.
  inversion_clear H1; simpl in H2.
  destroy H.
  elim IHCCC_To; repeat (split; auto).
+ inversion_clear HC.
  inversion_clear H1; inversion_clear H2.
  assert (Choreography_WF C1). split; auto.
  assert (Choreography_WF C2). split; auto.
  generalize (Program_WF_Then _ _ _ _ _ _ H); intro.
  generalize (Program_WF_Else _ _ _ _ _ _ H); intro.
  elim IHCCC_To1; auto; elim IHCCC_To2; auto; intros.
  split; split; auto.
+ assert (Choreography_WF C).
  1: { inversion_clear HC. simpl in H1; inversion_clear H2; split; auto. }
  assert (within_Xs Xs C).
  1: { elim (Program_WF_Main_within_Xs _ _ H); auto. }
  assert (consistent (Names D) C).
  1: { elim (Program_WF_consistent _ _ H); auto. }
  generalize (Program_WF_Main_change _ _ _ _ H1 H2 H3 H); intro.
  assert (Choreography_WF C'); auto; clear IHCCC_To.
  inversion_clear H6. repeat split; simpl; auto.
  inversion_clear HC. inversion_clear H9; auto.
+ change (Choreography_WF (Procs (D,Call X) X)).
  apply Program_WF_Proc with Xs; auto.
  apply (Program_WF_Vars_In _ _ H). red; simpl; auto.
+ elim (Program_WF_Proc _ _ H X); intros.
  2: apply (Program_WF_Vars_In _ _ H); red; simpl; auto.
  split; simpl; auto.
  split; auto.
  revert H1; case (fst (D X)); intros.
  1: exfalso; inversion H1.
  intro.
  rewrite (set_size_remove' (@eq_dec _)) with (t::l) p in H1; auto.
  - rewrite H5 in H1.
    elim (lt_irrefl _ H1).
  - revert H5; simpl. elim eq_dec; auto.
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
  rewrite (set_size_remove' (@eq_dec _)) with ps p in H1; auto.
  intro. rewrite H6 in H1.
  elim (lt_irrefl _ H1).
+ destroy HC. repeat split; auto.
Qed.

Lemma CCC_To_CCP_WF : forall P s l P' s',
  CCP_WF P -> (P,s) --[l]--> (P',s') -> CCP_WF P'.
Proof.
intros.
inversion H0. inversion_clear H.
inversion_clear H8. rename x into Xs.
split.
+ rewrite <- H1 in H7.
  apply well_ann_Main_change with C; auto.
+ exists Xs. rewrite H5.
  apply (CCC_To_Program_WF _ _ _ _ _ _ H H0).
Qed.

Lemma CCC_ToStar_CCP_WF : forall P s l P' s',
  CCP_WF P -> (P,s) --[l]-->* (P',s') -> CCP_WF P'.
Proof.
intros P s l; revert P s.
induction l; intros; inversion H0.
+ rewrite <- H2; auto.
+ induction c2. rename a0 into P'', b into s''.
  apply (IHl P'' s'' P' s'); auto.
  eapply CCC_To_CCP_WF; eauto.
Qed.

Lemma CCC_To_pn : forall D C s tl C' s', CCC_To D C s tl C' s' ->
  forall p, In p (RL_pn _ _ _ _ tl) -> In p (CCC_pn C (Names D)).
Proof.
induction C; simpl; intros; inversion H; simpl.
+ rewrite <- H5 in H0; simpl in H0. sup.
+ rewrite <- H5 in H0; simpl in H0. sup.
+ sup. right. eapply IHC; eauto.
+ rewrite <- H6 in H0; simpl in H0. sup. sup.
+ rewrite <- H6 in H0; simpl in H0. sup. sup.
+ sup. right. eapply IHC2; eauto.
+ rewrite <- H6 in H0; simpl in H0.
  inversion_clear H0. rewrite <- H9; auto. inversion H9.
+ rewrite <- H6 in H0; simpl in H0.
  inversion_clear H0. rewrite <- H9; auto. inversion H9.
+ sup. right. eapply IHC; eauto.
+ rewrite <- H6 in H0; simpl in H0. sup.
  inversion_clear H0. rewrite <- H11; auto. inversion H11.
+ rewrite <- H6 in H0; simpl in H0. sup.
  inversion_clear H0. rewrite <- H11; auto. inversion H11.
Qed.

Lemma CCC_To_pn' : forall D C s tl C' s', CCC_To D C s tl C' s' ->
  forall p, In p (CCC_pn C' (Names D)) ->
    In p (CCC_pn C (Names D))
     \/ exists X, (In p (CCC_pn (snd (D X)) (Names D)) /\ X_Free X C).
Proof.
induction C; intros; inversion H.
+ left. simpl. sup.
+ left. simpl. sup.
+ simpl. sup. rewrite <- H6 in H0; simpl in H0.
  revert H0; sup; intro. inversion_clear H0; auto.
  elim (IHC _ _ _ _ H9 p); auto.
+ left. simpl. sup; sup.
+ left. simpl. sup; sup.
+ simpl. sup; sup. rewrite <- H7 in H0; simpl in H0.
  revert H0. sup; sup; intro. inversion_clear H0. inversion_clear H12; auto.
  elim (IHC1 _ _ _ _ H10 p); auto.
    right. destroy H12; exists x; split; auto.
    red; simpl; unfold set_union_rv. rewrite set_union_iff; auto.
  elim (IHC2 _ _ _ _ H11 p); auto.
    right. destroy H0; exists x; split; auto.
    red; simpl; unfold set_union_rv. rewrite set_union_iff; auto.
+ simpl. right; exists t; rewrite H7; split; auto.
  red. simpl. auto.
+ simpl. rewrite <- H7 in H0; simpl in H0.
  revert H0; sup; intro. inversion_clear H0; auto.
  - left. eapply set_remove'_1; eauto.
  - right. exists t; split; auto. red; simpl; auto.
+ simpl. sup. rewrite <- H6 in H0; simpl in H0.
  revert H0; sup; intro. inversion_clear H0; auto.
  elim (IHC _ _ _ _ H9 p); auto. intros. destroy H0.
  right; exists x; split; auto. red; simpl. 
  unfold set_union_rv; rewrite set_union_iff; auto.
+ simpl. sup. rewrite <- H7 in H0; simpl in H0.
  revert H0; sup; intro. inversion_clear H0; auto.
  left; left. eapply set_remove'_1; eauto.
+ simpl; sup.
Qed.

Lemma CCC_To_pn'' : forall P s tl P' s',  well_ann P -> (P,s) --[tl]--> (P',s') ->
  forall p, In p (CCC_pn (Main P') (Vars P')) -> In p (CCC_pn (Main P) (Vars P)).
Proof.
intros.
revert H1. inversion H0. unfold Vars; simpl.
rewrite <- H1 in H. clear P H0 H1 P' H5.
revert dependent C'.
clear s'0 H6 tl H2 s0 H3.
induction C; intros; revert H1; inversion H4.
all: simpl; repeat sup.
+ intro. inversion_clear H10; auto.
  right. eauto.
+ intro. inversion_clear H12.
  left. inversion_clear H13; auto.
  right. eauto.
  right. eauto.
+ apply H.
+ intro. inversion_clear H9.
  eapply set_remove'_1; eauto.
  apply H; auto.
+ intro. inversion_clear H10; auto.
  right. eauto.
+ intro. inversion_clear H11; auto.
  left. eapply set_remove'_1; eauto.
Qed.

(** Some more specific properties. *)

Lemma CCC_To_Com_neq : forall D C s p v q x C' s', Choreography_WF C ->
  <<C,s>> --[RL_Com p v q x,D]--> <<C',s'>> -> p <> q.
Proof.
induction C; intros; inversion H0.
+ rewrite <- H1 in H; destroy H.
  simpl in H12. rewrite <- H6, <- H8; tauto.
+ eapply IHC; eauto. apply Choreography_WF_eta with t e; auto.
+ eapply IHC1; eauto. apply Choreography_WF_Then with p b C2; auto.
+ eapply IHC; eauto. eapply Choreography_WF_Call_1; eauto.
Qed.

Lemma CCC_To_Sel_neq : forall D C s p q l C' s', Choreography_WF C ->
  <<C,s>> --[RL_Sel p q l,D]--> <<C',s'>> -> p <> q.
Proof.
induction C; intros; inversion H0.
+ rewrite <- H1 in H; destroy H.
  simpl in H11. rewrite <- H6, <- H7; tauto.
+ eapply IHC; eauto. apply Choreography_WF_eta with t e; auto.
+ eapply IHC1; eauto. apply Choreography_WF_Then with p b C2; auto.
+ eapply IHC; eauto. eapply Choreography_WF_Call_1; eauto.
Qed.

Lemma CCC_To_Xs : forall D C s p X C' s' Xs, within_Xs Xs C ->
  <<C,s>> --[RL_Call X p,D]--> <<C',s'>> -> In X Xs.
Proof.
induction C; intros; inversion H0.
+ eapply IHC; eauto.
+ eapply IHC1; eauto. inversion H; auto.
+ rewrite <- H2. auto.
+ rewrite <- H2; auto.
+ eapply IHC; eauto. inversion H; auto.
+ rewrite <- H4; inversion H; auto.
+ rewrite <- H4; inversion H; auto.
Qed.

(** Deadlock-freedom by design. *)

Theorem progress : forall P, Main P <> End -> CCP_WF P ->
  forall s, exists tl c', (P,s) --[tl]--> c'.
Proof.
induction P as (Ps,C).
induction C; intros.
+ (* Eta *)
  case_eq e; do 2 eexists; do 2 constructor; ESEr.
+ (* Cond *)
  case_eq (eval_on_state BEv t0 s t).
  - do 2 eexists; constructor; apply C_Then'; auto.
  - do 2 eexists; constructor; apply C_Else'; auto.
+ (* Call *)
  rename t into X; set (ps := fst (Ps X)).
  simpl in H.
  case_eq ([#] ps); [idtac | intros; case_eq n].
  - intro. exfalso.
    unfold ps in H1.
    generalize (CCP_WF_Vars _ H0 X); intros.
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
    assert (In t (fst (Ps X))). rewrite H2; left; auto.
    do 2 eexists.
    constructor; apply (C_Call_Local' Ps t X); auto.
  - intros.
    rewrite H2 in H1; clear n H2.
    case_eq ps; intros.
    1: { rewrite H2 in H1; inversion H1. }
    unfold ps in H1, H2; clear ps.
    assert ([#] (fst (Ps X)) > 1).
    1: { rewrite H1; auto with arith. }
    assert (In t (fst (Ps X))).
    1: { rewrite H2; left; auto. }
    do 2 eexists.
    constructor; apply (C_Call_Start' Ps t); auto.
+ (* RT_Call *)
  case_eq ([#] l); intros; [idtac | case_eq n].
  - clear H IHC; exfalso.
    generalize (CCP_WF_Main _ H0).
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
+ (* End *)
  simpl in H. elim H; auto.
Qed.

Theorem deadlock_freedom : forall P, CCP_WF P ->
  forall s ts c', (P,s) --[ts]-->* c' ->
  {Main (fst c') = End} + {exists tl c'', c' --[tl]--> c''}.
Proof.
intros. induction c'. rename a into P', b into s'.
simpl; intros.
elim (chor_eq_dec (Main P') End); intros; auto.
right. apply progress; auto.
eapply CCC_ToStar_CCP_WF; eauto.
Qed.

End Properties.

Section Uniqueness.

(** ** Results on determinism of the semantics. *)

(** Reductions are preserved by state equivalence. *)

Lemma CCC_To_eq : forall D C s1 tl C' s2 s1' s2', s1 [==] s1' -> s2 [==] s2' ->
  <<C,s1>> --[tl,D]--> <<C',s2>> -> <<C,s1'>> --[tl,D]--> <<C',s2'>>.
Proof.
intros.
induction H1.
+ unfold v.
  rewrite (eval_eq _ e s s1'); auto.
       apply C_Com.
  ESEt s'. ESEs. eESEt.
  rewrite <- (eval_eq _ e s s1'); auto. fold v.
  ESEc; auto.
+ apply C_Sel. ESEt s. ESEs. ESEt s'.
+ apply C_Then. ESEt s. ESEs. ESEt s'.
  rewrite <- (eval_eq _ b s); auto.
+ apply C_Else. ESEt s. ESEs. ESEt s'.
  rewrite <- (eval_eq _ b s); auto.
+ apply C_Delay_Eta; auto.
+ apply C_Delay_Cond; auto.
+ apply C_Delay_Call; auto.
+ apply C_Call_Local; auto. ESEt s. ESEs. ESEt s'.
+ apply C_Call_Start; auto. ESEt s. ESEs. ESEt s'.
+ apply C_Call_Enter; auto. ESEt s. ESEs. ESEt s'.
+ apply C_Call_Finish; auto. ESEt s. ESEs. ESEt s'.
Qed.

Lemma CCP_To_eq : forall P s1 tl P' s2 s1' s2', s1 [==] s1' -> s2 [==] s2' ->
  (P,s1) --[tl]--> (P',s2) -> (P,s1') --[tl]--> (P',s2').
Proof.
intros.
induction P.
inversion H1; constructor.
apply CCC_To_eq with s1 s2; auto.
Qed.

Lemma CCP_ToStar_eq : forall P s1 tl P' s2 s1' s2', s1 [==] s1' -> s2 [==] s2' ->
  tl <> nil -> (P,s1) --[tl]-->* (P',s2) -> (P,s1') --[tl]-->* (P',s2').
Proof.
intros P s1 tl; revert P s1.
induction tl; intros. elim H1; auto.
case_eq tl; intros.
+ rewrite H3 in H2; inversion H2.
  inversion H9. rewrite H12 in H7.
  apply CCT_Step with (P',s2'). 2: constructor.
  apply CCP_To_eq with s1 s2; auto.
+ inversion H2.
  induction c2.
  apply CCT_Step with (a0,b).
  - apply CCP_To_eq with s1 b; auto. ESEr.
  - rewrite <- H3. eapply IHtl; eauto. ESEr.
    rewrite H3; discriminate.
Qed.

(** The set of procedure definitions never changes. *)

Hypothesis D : DefSet.

Lemma CCP_To_Defs_stable : forall D' C C' tl s s',
  (D,C,s) --[tl]--> (D',C',s') -> D = D'.
Proof.
intros.
inversion H.
inversion H; auto.
Qed.

Lemma CCP_ToStar_Defs_stable : forall D' C C' tl s s',
  (D,C,s) --[tl]-->* (D',C',s') -> D = D'.
Proof.
intros D' C C' tl; revert C C'.
induction tl; intros; inversion H; clear H; auto.
clear c1 c3 H2 H4 t l H0 H1.
induction c2. induction a0.
apply CCP_To_Defs_stable in H3.
rewrite <- H3 in H5.
eauto.
Qed.

(** Reductions and state. *)

Lemma CCC_To_disjoint_eval : forall C s tl s' p e C', disjoint_p_rl p tl ->
  <<C,s>> --[tl,D]--> <<C',s'>> -> eval_on_state Ev e s p = eval_on_state Ev e s' p.
Proof.
intros.
induction H0; auto; try (apply eval_eq; auto; fail).
inversion_clear H.
transitivity (eval_on_state Ev e (s[[q,x => v]]) p).
apply eval_neq; auto.
apply eval_eq; ESEs.
Qed.

Lemma CCC_To_disjoint_beval : forall C s tl s' p b C', disjoint_p_rl p tl ->
  <<C,s>> --[tl,D]--> <<C',s'>> -> eval_on_state BEv b s p = eval_on_state BEv b s' p.
Proof.
intros.
induction H0; auto; try (apply eval_eq; auto; fail).
inversion_clear H.
transitivity (eval_on_state BEv b (s[[q,x => v]]) p).
apply eval_neq; auto.
apply eval_eq; ESEs.
Qed.

Lemma CCC_To_disjoint_update : forall C s tl s' p x v C', disjoint_p_rl p tl ->
  <<C,s>> --[tl,D]--> <<C',s'>> ->
  <<C,s[[p,x => v]]>> --[tl,D]--> <<C',s'[[p,x => v]]>>.
Proof.
intros.
induction H0; try (constructor; auto; try ESEc; auto; fail).
+ inversion_clear H.
  unfold v0. rewrite (eval_neq _ e s p0 p x v); auto.
  apply C_Com.
  rewrite <- (eval_neq _ e s p0 p x v); auto.
  fold v0.
  ESEt (s[[q,x0 => v0]][[p,x => v]]). ESEc; auto.
  apply update_independent; auto.
+ apply C_Then. ESEc; auto.
  rewrite <- eval_neq; auto.
+ apply C_Else. ESEc; auto.
  rewrite <- eval_neq; auto.
Qed.

(** Determinism of reductions given the label. *)
Lemma CCC_To_deterministic_1 : forall C C1 C2 tl s s1 s2,
  <<C,s>> --[tl,D]--> <<C1,s1>> -> <<C,s>> --[tl,D]--> <<C2,s2>> -> C1 = C2.
Proof.
(* Might be simpler: induction tl *)
induction C; intros; inversion H; inversion H0; 
  try (transitivity C; auto; fail).
(* Eta *)
- exfalso. rewrite <- H1, <- H5 in H16.
  inversion_clear H16. inversion_clear H18. auto.
- exfalso. rewrite <- H1, <- H5 in H16.
  inversion_clear H16. inversion_clear H18. auto.
- exfalso. rewrite <- H10, <- H14 in H8.
  inversion_clear H8. inversion_clear H18. auto.
- exfalso. rewrite <- H10, <- H14 in H8.
  inversion_clear H8. inversion_clear H18. auto.
- elim (IHC _ _ _ _ _ _ H9 H18); auto.
(* Cond *)
- transitivity C1; auto.
- rewrite H10 in H20; inversion H20.
- rewrite <- H6 in H19; elim H19; auto.
- rewrite H10 in H20; inversion H20.
- transitivity C2; auto.
- rewrite <- H6 in H19; elim H19; auto.
- rewrite <- H17 in H9; elim H9; auto.
- rewrite <- H17 in H9; elim H9; auto.
- rewrite (IHC1 _ _ _ _ _ _ H10 H21); rewrite (IHC2 _ _ _ _ _ _ H11 H22); auto.
(* Call *)
- auto.
- rewrite H3 in H11; elim (lt_irrefl _ H11).
- rewrite H11 in H3; elim (lt_irrefl _ H3).
- rewrite <- H6 in H14; inversion H14; auto.
- rewrite (IHC _ _ _ _ _ _ H9 H18); auto.
(* RT_Call *)
- rewrite <- H15 in H8. apply (disjoint_ps_rl_In _ _ _ _ _ _ _ H19) in H8.
  elim H8; auto.
- rewrite <- H15 in H8. apply (disjoint_ps_rl_In _ _ _ _ _ _ _ H19) in H8.
  elim H8; auto.
- rewrite <- H6 in H18. apply (disjoint_ps_rl_In _ _ _ _ _ _ _ H10) in H18.
  elim H18; auto.
- rewrite <- H6 in H16; inversion H16; auto.
- rewrite H19 in H9; elim (lt_irrefl _ H9).
- rewrite <- H6 in H18. apply (disjoint_ps_rl_In _ _ _ _ _ _ _ H10) in H18.
  elim H18; auto.
- rewrite H9 in H19; elim (lt_irrefl _ H19).
Qed.

Lemma CCC_To_deterministic_2 : forall C C1 C2 tl s s1 s2,
  <<C,s>> --[tl,D]--> <<C1,s1>> -> <<C,s>> --[tl,D]--> <<C2,s2>> -> s1 [==] s2.
Proof.
induction C; intros; inversion H; inversion H0;
  try (ESEt s; ESEs; fail); eauto.
(* Eta *)
- ESEt (s[[q,x => v]]).
  revert H16; unfold v, v0.
  rewrite <- H1 in H9; inversion H9.
  ESEs.
- rewrite <- H1 in H9; inversion H9.
- rewrite <- H1, <- H5 in H16.
  inversion_clear H16. inversion H18. elim H16; auto.
- rewrite <- H1 in H9; inversion H9.
- rewrite <- H1, <- H5 in H16.
  inversion_clear H16. inversion H18. elim H16; auto.
- rewrite <- H10, <- H14 in H8.
  inversion_clear H8. inversion H18. elim H8; auto.
- rewrite <- H10, <- H14 in H8.
  inversion_clear H8. inversion H18. elim H8; auto.
(* Cond *)
- rewrite <- H6 in H19; elim H19; auto.
- rewrite <- H6 in H19; elim H19; auto.
- rewrite <- H17 in H9; elim H9; auto.
- rewrite <- H17 in H9; elim H9; auto.
(* RT_Call *)
- rewrite <- H15 in H8. apply (disjoint_ps_rl_In _ _ _ _ _ _ _ H19) in H8.
  elim H8; auto.
- rewrite <- H15 in H8. apply (disjoint_ps_rl_In _ _ _ _ _ _ _ H19) in H8.
  elim H8; auto.
- rewrite <- H6 in H18. apply (disjoint_ps_rl_In _ _ _ _ _ _ _ H10) in H18.
  elim H18; auto.
- rewrite <- H6 in H18. apply (disjoint_ps_rl_In _ _ _ _ _ _ _ H10) in H18.
  elim H18; auto.
Qed.

Lemma CCC_To_deterministic : forall C C1 C2 tl1 tl2 s s1 s2,
  <<C,s>> --[tl1,D]--> <<C1,s1>> -> <<C,s>> --[tl2,D]--> <<C2,s2>> ->
  tl1 = tl2 -> C1 = C2 /\ s1 [==] s2.
Proof.
intros.
rewrite H1 in H; split.
eapply CCC_To_deterministic_1; eauto.
eapply CCC_To_deterministic_2; eauto.
Qed.

(** Conversely: the result choreography determines the transition label
  and resulting state. *)

Lemma CCC_To_eta_reduction : forall ann eta C s1 s2 tl,
  <<eta @ ann;;C,s1>> --[tl,D]--> <<C,s2>> ->
  (forall p e q x, eta = (p#e --> q$x) -> tl = RL_Com p (eval_on_state Ev e s1 p) q x)
  /\ (forall p q l, eta = (p --> q[l]) -> tl = RL_Sel p q l).
Proof.
induction C; intros; inversion H; split; intros;
  try (unfold v); try (inversion H7; auto; fail).
+ clear s' H5 C' H8 t0 H4 s H2 eta0 H1 ann1 H0 C0 H3.
  rewrite H6, H7, H11 in *.
  clear e H9 H11 H.
  elim (IHC _ _ _ H10); auto.
+ clear s' H5 C' H8 t0 H4 s H2 eta0 H0 C0 H3.
  rewrite H6, H7, H11 in *.
  clear e H9 H11 H.
  elim (IHC _ _ _ H10); auto.
Qed.

Lemma CCC_To_Then_reduction : forall p b C1 C2 s1 s2 tl,
  <<If p ?? b Then C1 Else C2,s1>> --[tl,D]--> <<C1,s2>> -> tl = RL_Cond p.
Proof.
induction C1; intros; inversion H; auto.
rewrite <- H7, <- H8 in H12; rewrite <- H7.
apply (IHC1_1 _ _ _ _ H12).
Qed.

Lemma CCC_To_Else_reduction : forall p b C1 C2 s1 s2 tl,
  <<If p ?? b Then C1 Else C2,s1>> --[tl,D]--> <<C2,s2>> -> tl = RL_Cond p.
Proof.
intros p b C1 C2; revert C1.
induction C2; intros; inversion H; auto.
rewrite <- H7, <- H8 in H13; rewrite <- H7.
apply (IHC2_2 _ _ _ _ H13).
Qed.

Lemma CCC_To_Call_reduction_1 : forall p X s1 s2 tl,
  initial (snd (D X)) -> In p (fst (D X)) ->
  <<Call X,s1>> --[tl,D]--> <<snd (D X),s2>> -> tl = RL_Call X p.
Proof.
intros.
set (C:=snd (D X)). assert (C = snd (D X)); auto.
clearbody C. revert p X s1 s2 tl H H0 H1 H2.
induction C; intros; inversion H1;
  try (rewrite (set_size_1 _ _ H5 _ _ H0 H6); auto; fail);
  try (rewrite <- H4 in H; simpl in H; inversion H).
Qed.

Lemma CCC_To_Call_reduction_2 : forall p X s1 s2 tl,
  initial (snd (D X)) -> In p (fst (D X)) ->
  <<Call X,s1>> --[tl,D]--> <<RT_Call X (fst (D X)[\]p) (snd (D X)),s2>> ->
  tl = RL_Call X p.
Proof.
intros.
set (C:=snd (D X)). assert (C = snd (D X)); auto.
clearbody C. revert p X s1 s2 tl H H0 H1 H2.
induction C; intros; inversion H1;
  try (rewrite H4 in H; simpl in H; inversion H);
  try rewrite (set_remove'_cross _ _ _ _ H9 H4); auto.
Qed.

Lemma CCC_To_Call_reduction_3 : forall C p ps X s1 s2 tl, In p ps ->
  <<RT_Call X ps C,s1>> --[tl,D]--> <<RT_Call X (ps[\]p) C,s2>> ->
  tl = RL_Call X p.
Proof.
induction C; intros; inversion H0;
  try (rewrite (set_remove'_cross _ _ _ _ H10 H4); auto; fail);
  try (rewrite H7 in H; apply set_remove'_2 in H; elim H; auto; fail).
rewrite (set_size_1 _ _ H11 _ _ H H12); auto.
Qed.

Fixpoint C_size (C:Choreography) :=
match C with
| Eta@_;; C'     => S (C_size C')
| Cond _ _ C1 C2 => S (C_size C1 + C_size C2)
| RT_Call _ _ C' => S (C_size C')
| _              => 0
end.

Fixpoint subterm (C1 C2:Choreography) : Prop :=
match C2 with
| Eta@_;;C'        => C1 = C' \/ subterm C1 C'
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

Lemma CCC_To_Call_reduction_4 : forall C p ps X s1 s2 tl,
  In p ps -> <<RT_Call X ps C,s1>> --[tl,D]--> <<C,s2>> -> tl = RL_Call X p.
Proof.
induction C; intros; inversion H0; auto;
  try (rewrite (set_size_1 _ _ H7 _ _ H H9); auto; fail);
  try (rewrite (set_size_1 _ _ H3 _ _ H H4); auto; fail).
+ rewrite <- H7; rewrite <- H7 in H11.
  rewrite <- H8 in H10, H11.
  eauto.
+ elim (subterm_not_equal C (RT_Call t (ps [\] p0) C)); simpl; auto.
Qed.

Lemma CCC_To_deterministic_3 : forall C C' tl1 tl2 s s1 s2,
  <<C,s>> --[tl1,D]--> <<C',s1>> -> <<C,s>> --[tl2,D]-->
  <<C',s2>> -> tl1 = tl2.
Proof.
induction C; intros; inversion H; inversion H0; auto.
(* Eta *)
+ unfold v, v0; rewrite <- H1 in H9; inversion H9; auto.
+ rewrite <- H1 in H9; inversion H9; auto.
+ rewrite H6, <- H14 in H17.
(*   clear H H0 C0 H3 s0 H2 H5 s' H6 C1 H9 eta H8 s3 H11 t H12 s'0 H14 C' H13. *)
  elim (CCC_To_eta_reduction _ _ _ _ _ _ H17); intros.
  symmetry; apply H18; auto.
+ rewrite <- H1 in H9; inversion H9; auto.
+ rewrite <- H1 in H9; inversion H9; auto.
+ rewrite H6, <- H14 in H17.
  elim (CCC_To_eta_reduction _ _ _ _ _ _ H17); intros.
  symmetry; apply H19; auto.
+ rewrite H15, <- H6 in H9.
  elim (CCC_To_eta_reduction _ _ _ _ _ _ H9); intros.
  apply H18; auto.
+ rewrite H15, <- H6 in H9.
  elim (CCC_To_eta_reduction _ _ _ _ _ _ H9); intros.
  apply H19; auto.
+ revert H9 H18. rewrite <- H6 in H15; inversion H15.
  eauto.
(* Cond *)
+ rewrite H7, <- H17 in H20.
  rewrite (CCC_To_Then_reduction _ _ _ _ _ _ _ H20); auto.
+ rewrite H7, <- H17 in H21.
  rewrite (CCC_To_Else_reduction _ _ _ _ _ _ _ H21); auto.
+ rewrite H18, <- H7 in H10.
  apply (CCC_To_Then_reduction _ _ _ _ _ _ _ H10); auto.
+ rewrite H18, <- H7 in H11.
  apply (CCC_To_Else_reduction _ _ _ _ _ _ _ H11); auto.
+ revert H21 H22. rewrite <- H7 in H18; inversion H18.
  eauto.
(* Call *)
+ rewrite (set_size_1 _ _ H11 _ _ H12 H4); auto.
+ rewrite H3 in H11; elim (lt_irrefl _ H11).
+ rewrite H11 in H3; elim (lt_irrefl _ H3).
+ rewrite <- H7 in H15; inversion H15.
  rewrite (set_remove'_cross _ _ _ _ H12 H18); auto.
+ rewrite <- H6 in H15; inversion H15.
  rewrite <- H20 in H9; eauto.
(* RT_Call *)
+ rewrite <- H6 in H16; inversion H16.
  rewrite <- H21 in H19. apply set_remove'_2 in H19. elim H19; auto.
+ rewrite H16, <- H6 in H9.
  apply (CCC_To_Call_reduction_4 _ _ _ _ _ _ _ H19 H9).
+ rewrite <- H7 in H0.
  symmetry; apply (CCC_To_Call_reduction_3 _ _ _ _ _ _ _ H10 H0).
+ rewrite <- H7 in H17; inversion H17.
  rewrite (set_remove'_cross _ _ _ _ H20 H22); auto.
+ rewrite <- H19 in H9; elim (lt_irrefl _ H9).
+ rewrite H7, <- H16 in H19.
  symmetry; apply (CCC_To_Call_reduction_4 _ _ _ _ _ _ _ H10 H19).
+ rewrite <- H9 in H19; elim (lt_irrefl _ H19).
+ rewrite (set_size_1 _ _ H19 _ _ H10 H20); auto.
Qed.

Lemma CCC_To_deterministic_4 : forall C C' tl1 tl2 s s1 s2,
  <<C,s>> --[tl1,D]--> <<C',s1>> -> <<C,s>> --[tl2,D]--> <<C',s2>> -> s1 [==] s2.
Proof.
intros.
rewrite (CCC_To_deterministic_3 _ _ _ _ _ _ _ H0 H) in H0.
eapply CCC_To_deterministic_2; eauto.
Qed.

(** The label alone determines the resulting state. *)

Lemma CCC_To_rl_implies_state : forall C1 s tl C1' s1 C2 C2' s2,
  <<C1,s>> --[tl,D]--> <<C1',s1>> -> <<C2,s>> --[tl,D]--> <<C2',s2>> -> s1 [==] s2.
Proof.
induction C1; induction C2; intros; inversion H; inversion H0;
  try (ESEt s; ESEs; fail); eauto;
  try (rewrite <- H5 in H14; inversion H14; fail);
  try (rewrite <- H6 in H15; inversion H15; fail);
  try (rewrite <- H5 in H13; inversion H13; fail).
(* Eta *)
+ ESEt (s[[q,x => v]]). ESEs. ESEt (s[[q0,x0 => v0]]).
  rewrite <- H5 in H13; inversion H13. ESEr.
(* Call *)
+ rewrite <- H6 in H13; inversion H13.
(* RT_Call *)
+ rewrite <- H6 in H13; inversion H13.
Qed.

(** Currently not used, but might prove useful. *)

Lemma RL_Com_reduce_eq : forall D p C v v' q q' x x' s C' s' C'' s'',
  <<C,s>> --[RL_Com p v q x,D]--> <<C',s'>> ->
  <<C,s>> --[RL_Com p v' q' x',D]--> <<C'',s''>> -> v = v' /\ q = q' /\ x = x'.
Proof.
induction C; intros; try (inversion H; inversion H0); eauto.
+ rewrite <- H1 in H12; inversion H12.
  repeat split.
  * unfold v1, v2. rewrite H25; auto.
  * transitivity q1; auto; transitivity q0; auto.
  * transitivity x1; auto; transitivity x0; auto.
+ rewrite <- H1 in H19; inversion H19.
  destroy H21; exfalso; auto.
+ rewrite <- H10 in H8; inversion H8.
  destroy H21; exfalso; auto.
Qed.

Lemma L_Com_reduce_eq : forall D p C v v' q q' s C' s' C'' s'',
  (D,C,s) --[TL_Com p v q]--> (D,C',s') ->
  (D,C,s) --[TL_Com p v' q']--> (D,C'',s'') -> v = v' /\ q = q'.
Proof.
intros.
inversion H; inversion H0.
induction t; try (inversion H5; fail).
induction t0; try (inversion H12; fail).
simpl in H5, H12.
inversion H5; inversion H12.
rewrite H16 in H2; rewrite H19 in H9.
elim (RL_Com_reduce_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2 H9); intros.
destroy H22.
split.
+ transitivity v0; auto; transitivity v1; auto.
+ transitivity q0; auto; transitivity q1; auto.
Qed.

Lemma RL_Com_reduce_neq : forall D p p' C v v' q q' x x' s C' s' C'' s'',
  <<C,s>> --[RL_Com p v q x,D]--> <<C',s'>> ->
  <<C,s>> --[RL_Com p' v' q' x',D]--> <<C'',s''>> -> p <> p' -> q <> q'.
Proof.
induction C; intros; try (inversion H; inversion H0); eauto.
+ rewrite <- H2 in H13; inversion H13.
  exfalso. apply H1.
  transitivity p0; auto; transitivity p1; auto.
+ rewrite <- H2 in H20; inversion H20.
  destroy H22; destroy H23. rewrite <- H9; auto.
+ rewrite <- H11 in H9; inversion H9.
  destroy H22; destroy H23. rewrite <- H18; auto.
Qed.

Lemma L_Com_reduce_neq : forall D p p' C v v' q q' s C' s' C'' s'',
  (D,C,s) --[TL_Com p v q]--> (D,C',s') ->
  (D,C,s) --[TL_Com p' v' q']--> (D,C'',s'') -> p <> p' -> q <> q'.
Proof.
intros.
rename H1 into Hp.
inversion H; inversion H0.
induction t; inversion H5.
induction t0; inversion H12.
rewrite H21, H20, H19 in H9; rewrite H18, H17, H16 in H2.
apply (RL_Com_reduce_neq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H2 H9); auto.
Qed.

Lemma RL_Sel_reduce_eq : forall D p C q q' l l' s C' s' C'' s'',
  <<C,s>> --[RL_Sel p q l,D]--> <<C',s'>> ->
  <<C,s>> --[RL_Sel p q' l',D]--> <<C'',s''>> -> q = q' /\ l = l'.
Proof.
induction C; intros; try (inversion H; inversion H0); eauto.
+ rewrite <- H1 in H11; inversion H11.
  repeat split.
  * transitivity q1; auto; transitivity q0; auto.
  * transitivity l1; auto; transitivity l0; auto.
+ rewrite <- H1 in H18; inversion H18.
  destroy H20; exfalso; auto.
+ rewrite <- H10 in H8; inversion H8.
  destroy H20; exfalso; auto.
Qed.

Lemma L_Sel_reduce_eq : forall D p C q q' l l' s C' s' C'' s'',
  (D,C,s) --[TL_Sel p q l]--> (D,C',s') ->
  (D,C,s) --[TL_Sel p q' l']--> (D,C'',s'') -> q = q' /\ l = l'.
Proof.
intros.
inversion H; inversion H0.
induction t; try (inversion H5; fail).
induction t0; try (inversion H12; fail).
simpl in H5, H12.
inversion H5; inversion H12.
rewrite H16 in H2; rewrite H19 in H9.
elim (RL_Sel_reduce_eq _ _ _ _ _ _ _ _ _ _ _ _ H2 H9); split.
+ transitivity q0; auto; transitivity q1; auto.
+ transitivity l0; auto; transitivity l1; auto.
Qed.

Lemma RL_Sel_reduce_neq : forall D p p' C q q' l l' s C' s' C'' s'',
  <<C,s>> --[RL_Sel p q l,D]--> <<C',s'>> ->
  <<C,s>> --[RL_Sel p' q' l',D]--> <<C'',s''>> -> p <> p' -> q <> q'.
Proof.
induction C; intros; try (inversion H; inversion H0); eauto.
+ rewrite <- H2 in H12; inversion H12.
  exfalso; apply H1.
  transitivity p0; auto; transitivity p1; auto.
+ rewrite <- H2 in H19; inversion H19.
  destroy H21; destroy H22. rewrite <- H8; auto.
+ rewrite <- H11 in H9; inversion H9.
  destroy H21; destroy H22. rewrite <- H17; auto.
Qed.

Lemma L_Sel_reduce_neq : forall D p p' C q q' l l' s C' s' C'' s'',
  (D,C,s) --[TL_Sel p q l]--> (D,C', s') ->
  (D,C,s) --[TL_Sel p' q' l']--> (D,C'', s'') -> p <> p' -> q <> q'.
Proof.
intros.
rename H1 into Hp.
inversion H; inversion H0.
induction t; inversion H5.
induction t0; inversion H12.
rewrite H21, H20, H19 in H9; rewrite H18, H17, H16 in H2.
apply (RL_Sel_reduce_neq _ _ _ _ _ _ _ _ _ _ _ _ _ H2 H9); auto.
Qed.

End Uniqueness.

(** ** Confluence of CC *)

Section Confluence.

Lemma diamond_Chor : forall D C s tl1 tl2 C1 C2 s1 s2,
  <<C,s>> --[tl1,D]--> <<C1,s1>> -> <<C,s>> --[tl2,D]--> <<C2,s2>> -> tl1 <> tl2 ->
  exists C' s', <<C1,s1>> --[tl2,D]--> <<C',s'>> /\ <<C2,s2>> --[tl1,D]--> <<C',s'>>.
Proof.
induction C; intros s tl' tl'' C' C'' s' s'' HC' HC'' Htl; intros.
+ (* Eta *)
  inversion HC'; inversion HC''; try (rewrite <- H in H7; inversion H7).
  - elim Htl. unfold v, v0 in H11, H3. rewrite <- H11, <- H3, H16, H17, H18, H19; auto.
  - clear HC' HC'' Htl s'1 H13 C'' H12 t0 H11 s1 H9 C1 H10 eta H7 ann0 H8 H16.
    rewrite <- H4.
    clear s'0 H5 C' H4 C0 H2 s0 H0 tl' H3.
    rename C'0 into C'.
    generalize (C_Com' D p e0 q x t C' s''); rewrite H; intro.
    rewrite <- H in H14; inversion_clear H14.
    exists C', (s''[[q,x => v]]); split.
    * apply CCC_To_eq with (s[[q,x => v]]) (s''[[q,x => v]]). ESEs. ESEr.
      apply CCC_To_disjoint_update; auto.
    * unfold v.
      rewrite (CCC_To_disjoint_eval _ _ _ _ _ _ _ _ H2 H15); auto.
  - elim Htl. rewrite <- H11, <- H3, H16, H17, H18; auto.
  - rewrite <- H4.
    generalize (C_Sel' D p q l t C'0 s''); rewrite H; intro.
    rewrite <- H in H14; inversion_clear H14.
    exists C'0, s''; split; auto.
    apply CCC_To_eq with s s''; auto. ESEr.
  - rewrite <- H13.
    generalize (C_Com' D p e0 q x t C'0 s'); rewrite H8; intro.
    rewrite <- H8 in H6; inversion_clear H6.
    exists C'0, (s'[[q,x => v]]); split.
    * unfold v.
      rewrite (CCC_To_disjoint_eval _ _ _ _ _ _ _ _ H17 H7); auto.
    * apply CCC_To_eq with (s[[q,x => v]]) (s'[[q,x => v]]). ESEs. ESEr.
      apply CCC_To_disjoint_update; auto.
  - rewrite <- H13.
    generalize (C_Sel' D p q l t C'0 s'); rewrite H8; intro.
    rewrite <- H8 in H6; inversion_clear H6.
    exists C'0, s'; split; auto.
    apply CCC_To_eq with s s'; auto. ESEr.
  - elim (IHC _ _ _ _ _ _ _ H7 H16); intros; auto.
    inversion_clear H17. inversion_clear H18.
    do 2 eexists; split; apply C_Delay_Eta; eauto.
+ (* Cond *)
  inversion HC'; inversion HC''; try (rewrite H8 in H18; inversion H18).
  - elim Htl. rewrite <- H14, <- H4; auto.
  - rewrite <- H5.
    exists C1', s''; split; auto.
    * apply CCC_To_eq with s s''; auto. ESEr.
    * apply C_Then'.
      rewrite <- (CCC_To_disjoint_beval D C1 s tl'' s'' t t0 C1'); auto.
  - elim Htl. rewrite <- H14, <- H4; auto.
  - rewrite <- H5.
    exists C2', s''; split; auto.
    * apply CCC_To_eq with s s''; auto. ESEr.
    * apply C_Else'.
      rewrite <- (CCC_To_disjoint_beval D C1 s tl'' s'' t t0 C1'); auto.
  - rewrite <- H16.
    exists C1', s'; split; auto.
    * apply C_Then'.
      rewrite <- (CCC_To_disjoint_beval D C1 s tl' s' t t0 C1'); auto.
    * apply CCC_To_eq with s s'; auto. ESEr.
  - rewrite <- H16.
    exists C2', s'; split; auto.
    * apply C_Else'.
      rewrite <- (CCC_To_disjoint_beval D C1 s tl' s' t t0 C1'); auto.
    * apply CCC_To_eq with s s'; auto. ESEr.
  - clear HC' HC'' s'1 H17 C'' H16 t2 H15 s1 H13 C5 H14 b0 H11 p0 H10.
    clear s'0 H6 C' H5 t1 H4 s0 H2 C3 H3 C0 H1 b H0 p H C4 H12.
    rename t into p, t0 into b.
    elim (IHC1 _ _ _ _ _ _ _ H8 H19); elim (IHC2 _ _ _ _ _ _ _ H9 H20); auto.
    intros; clear IHC1 IHC2.
    rename C1' into C1a, C1'0 into C1b, x0 into C1'.
    rename C2' into C2a, C2'0 into C2b, x into C2'.
    elim H; clear H; intros s1 Hs1; inversion_clear Hs1.
    elim H0; clear H0; intros s2 Hs2; inversion_clear Hs2.
    pose (CCC_To_rl_implies_state _ _ _ _ _ _ _ _ _ H H0) as Hrl.
    clearbody Hrl.
    exists (If p ?? b Then C1' Else C2'), s1; split; apply C_Delay_Cond; auto.
    * apply CCC_To_eq with s' s2; auto. ESEr. ESEs.
    * apply CCC_To_eq with s'' s2; auto. ESEr. ESEs.
+ (* Call *)
  inversion HC'; inversion HC''; auto.
  - exfalso.
    rewrite <- H4, <- H12 in Htl.
    rewrite (set_size_1 _ _ H9 p p0) in Htl; auto.
  - exfalso. rewrite H1 in H9; apply (lt_irrefl _ H9).
  - exfalso. rewrite H9 in H1; apply (lt_irrefl _ H1).
  - case (eq_dec p p0); intro Hpp0.
    1: { exfalso. rewrite <- H12, <- H4, Hpp0 in Htl; auto. }
    clear HC' HC'' Htl s'1 H14 C'' H13 tl'' H12 s1 H11 X0 H7.
    clear s'0 H6 C' H5 tl' H4 s0 H3 X H.
    rename t into X.
    elim (Nat.eq_dec ([#] (fst (D X))) 2); intro HX.
    * exists (snd (D X)), s.
      split; apply C_Call_Finish; try ESEs.
      ++ revert HX.
         intro; rewrite (set_size_remove' (@eq_dec _)) with (fst (D X)) p in HX; auto.
      ++ apply set_remove'_3; auto.
      ++ revert HX.
         intro; rewrite (set_size_remove' (@eq_dec _)) with (fst (D X)) p0 in HX; auto.
      ++ apply set_remove'_3; auto.
    * exists (RT_Call X (fst (D X) [\] p0 [\] p) (snd (D X))), s.
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
  - exists (RT_Call t (l [\] p) C'0), s'; split.
    * apply C_Call_Enter'; auto.
    * apply C_Delay_Call; auto.
      apply disjoint_ps_remove; auto. 
      apply CCC_To_eq with s s'; auto. ESEr.
  - exists C'0, s'; split.
    * apply C_Call_Finish'; auto.
    * apply CCC_To_eq with s s'; auto. ESEr. rewrite <- H14; auto.
  - exists (RT_Call t (l [\] p) C'0), s''; split.
    * apply C_Delay_Call; auto.
      apply disjoint_ps_remove; auto. 
      apply CCC_To_eq with s s''; auto. ESEr.
    * apply C_Call_Enter'; auto.
  - case (eq_dec p p0); intro Hpp0.
    1: { exfalso. rewrite <- H14, <- H4, Hpp0 in Htl; auto. }
    clear HC' HC'' Htl s'1 H16 C'' H15 tl'' H14 s1 H13 C1 H11 ps0 H10.
    clear X0 H9 s'0 H6 C' H5 tl' H4 C0 H1 ps H0 X H IHC.
    rename l into ps, t into X.
    elim (Nat.eq_dec ([#] ps) 2); intro HX.
    * exists C, s.
      split; apply C_Call_Finish; try ESEs.
      -- revert HX.
         intro; rewrite (set_size_remove' (@eq_dec _)) with ps p in HX; auto.
      -- apply set_remove'_3; auto.
      -- revert HX.
         intro; rewrite (set_size_remove' (@eq_dec _)) with ps p0 in HX; auto.
      -- apply set_remove'_3; auto.
    * exists (RT_Call X (ps [\] p0 [\] p) C), s.
      rewrite set_remove'_remove' at 1.
      split; (apply C_Call_Enter; try ESEs;
       [eapply set_size_neq_2; eauto | apply set_remove'_3; auto]).
  - exists C'0, s''; split.
    * apply CCC_To_eq with s s''; auto. ESEr. rewrite <- H5; auto.
    * apply C_Call_Finish'; auto.
+ (* End *)
  inversion HC'.
Qed.

Lemma diamond_1 : forall c tl1 tl2 c1 c2, c --[ tl1 ]--> c1 -> c --[ tl2 ]--> c2 ->
  tl1 <> tl2 -> exists c', c1 --[ tl2 ]--> c' /\ c2 --[ tl1 ]--> c'.
Proof.
induction c as [a s]. induction a as [D C].
intros.
inversion H; inversion H0.
elim (diamond_Chor _ _ _ _ _ _ _ _ _ H7 H13); intros.
2: { intro; apply H1. rewrite <- H9, <- H3, H14. auto. }
inversion_clear H14. inversion_clear H15.
exists (D,x,x0); split; constructor; auto.
Qed.

Lemma diamond_2 : forall c tl1 tl2 c1 c2, c --[ tl1 ]--> c1 -> c --[ tl2 ]--> c2 ->
  {fst c1 = fst c2 /\ snd c1 [==] snd c2}
  + {exists c', c1 --[ tl2 ]--> c' /\ c2 --[ tl1 ]--> c'}.
Proof.
induction c as [a s]. induction a as [D C].
induction c1 as [a s']. induction a as [D' C'].
induction c2 as [a s'']. induction a as [D'' C''].
intros.
elim (chor_eq_dec C' C''); intro HC'C''; [left | right].
+ inversion H; inversion H0.
  clear H H0 s'1 H16 C'1 H15 tl2 H10 s1 H12 C1 H11 D1 H9 s'0 H8.
  clear C'0 H7 tl1 H2 s0 H4 C0 H3 D0 H1.
  revert H5 H13; rewrite <- H6, <- H14, <- HC'C''; clear H6 H14 HC'C'' D' D'' C''.
  intros HC HC'.
  split; auto.
  eapply CCC_To_deterministic_4; eauto.
+ inversion H; inversion H0.
  elim (RichLabel_eq_dec _ _ _ _ t t0); intro.
  1: {
    elim HC'C''.
    rewrite <- a, <- H14 in H13. rewrite <- H6 in H5.
    eapply CCC_To_deterministic_1; eauto.
  }
  rewrite <- H6 in H5; rewrite <- H14 in H13.
  elim (diamond_Chor _ _ _ _ _ _ _ _ _ H5 H13); intros; auto.
  inversion_clear H17. inversion_clear H18.
  rewrite <- H6, <- H14.
  exists (D,x,x0); split; constructor; auto.
Qed.

(** In this one we unfold the configuration because of the equivalence.
  Furthermore, we use logical disjunction - the labels are too weak... *)

Lemma diamond_3a : forall P s tl1 tl2 P1 s1 P2 s2,
  (P,s) --[ tl1 ]-->* (P1,s1) -> (P,s) --[ tl2 ]--> (P2,s2) ->
  (exists tl' s1', (P2,s2) --[ tl' ]-->* (P1,s1')
                 /\ s1 [==] s1' /\ length tl1 = S (length tl'))
  \/ (exists P' s', (P1,s1) --[ tl2 ]--> (P',s') /\ (P2,s2) --[ tl1 ]-->* (P',s')).
Proof.
induction P as [D C].
induction P1 as [D1 C1].
induction P2 as [D2 C2].
intros.
rewrite <- (CCP_To_Defs_stable _ _ _ _ _ _ _ H0);
rewrite <- (CCP_To_Defs_stable _ _ _ _ _ _ _ H0) in H0.
rewrite <- (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ H);
rewrite <- (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ H) in H.
revert C s tl2 C1 s1 C2 s2 H H0; induction tl1.
+ right.
  inversion H.
  rewrite <- H2, <- H4. do 2 eexists; split; eauto. constructor.
+ intros.
  inversion H; clear H.
  clear t l H1 H2 c1 c3 H3 H5.
  induction c2, a0 as [D' C'].
  rewrite <- (CCP_To_Defs_stable _ _ _ _ _ _ _ H4) in H6, H4.
  elim (diamond_2 _ _ _ _ _ H0 H4); simpl; intros.
  - inversion_clear a0. inversion H.
    rewrite <- H3 in H, H4, H6; rewrite <- H3; clear H3.
    left; exists tl1. case_eq tl1; intros.
    * rewrite H2 in H6. inversion H6. exists s2; split. constructor.
      split. rewrite <- H8; ESEs. auto.
    * rewrite <- H2. exists s1; split. 2: split; auto; ESEr.
      apply CCP_ToStar_eq with b s1; auto. ESEs. ESEr. rewrite H2; discriminate.
  - inversion_clear b0.
    induction x, a0 as [D'' C'']; inversion_clear H.
    rewrite <- (CCP_To_Defs_stable _ _ _ _ _ _ _ H2) in H1, H2.
    elim (IHtl1 _ _ _ _ _ _ _ H6 H2); intro.
    * destroy H.
      rename x into tl', x0 into s'.
      left; exists (a::tl'), s'; split; auto.
      apply CCT_Step with (D,C'',b0); auto.
    * destroy H.
      right; exists x, x0; split; auto.
      apply CCT_Step with (D,C'',b0); auto.
Qed.

Lemma diamond_3 : forall P s tl1 tl2 P1 s1 P2 s2,
  (P,s) --[ tl1 ]-->* (P1,s1) -> (P,s) --[ tl2 ]--> (P2,s2) ->
  (exists tl' s1', (P2,s2) --[ tl' ]-->* (P1,s1') /\ s1 [==] s1')
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
    /\ s1' [==] s2' /\ length tl1 + length tl1' = length tl2 + length tl2').
Proof.
induction P as [D C], P1 as [D' C1], P2 as [D'' C2].
intros.
rewrite <- (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ H0);
rewrite <- (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ H0) in H0.
rewrite <- (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ H);
rewrite <- (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ H) in H.
clear D' D''.
revert C s tl1 C1 s1 C2 s2 H H0; induction tl2.
+ intros.
  inversion H0.
  rewrite <- H2, <- H4.
  exists (D,C1), nil, tl1, s1, s1; repeat split; auto.
  constructor.
+ intros.
  inversion H0; clear H0.
  clear t l H1 H2 c1 c3 H3 H5.
  induction c2, a0 as [D0 C0].
  rewrite <- (CCP_To_Defs_stable _ _ _ _ _ _ _ H4) in H6, H4.
  elim (diamond_3a _ _ _ _ _ _ _ _ H H4); intros.
  - destroy H0.
    rename x into tl', x0 into s'.
    elim (IHtl2 _ _ _ _ _ _ _ H1 H6); intros.
    destroy H3.
    induction x.
    rewrite <- (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ H5) in H7, H5.
    rename b0 into C', x0 into tl1', x1 into tl2', x2 into s1', x3 into s2'.
    case_eq tl1'; intros.
    * rewrite H9 in H5. inversion H5.
      rewrite <- H11; rewrite <- H11 in H5, H7; rewrite H9 in H3; clear C' tl1' H11 H9.
      rewrite <- H13 in H5, H8. clear s1' H13 c H10.
      exists (D,C1), nil, tl2', s1, s2'; repeat split; auto.
      constructor. ESEt s'. simpl. rewrite <- H3, H0. auto.
    * exists (D,C'), tl1', tl2', s1', s2'; repeat split; auto.
      apply CCP_ToStar_eq with s' s1'; auto. ESEs. ESEr. rewrite H9; discriminate.
      simpl. rewrite <- H3, H0; auto.
  - destroy H0.
    induction x as [D' C'].
    rewrite <- (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ H0) in H1, H0.
    rename x0 into s'.
    elim (IHtl2 _ _ _ _ _ _ _ H0 H6); intros.
    destroy H2.
    induction x as [D'' C''].
    rewrite <- (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ H3) in H5, H3.
    rename x0 into tl1'', x1 into tl2'', x2 into s1'', x3 into s2''.
    exists (D,C''), (a::tl1''), tl2'', s1'', s2''; repeat split; auto.
    apply CCT_Step with (D,C',s'); auto.
    simpl. rewrite <- H2. auto.
Qed.

Lemma diamond_4 : forall P s tl1 tl2 P1 s1 P2 s2,
  (P,s) --[ tl1 ]-->* (P1,s1) -> (P,s) --[ tl2 ]-->* (P2,s2) ->
  (exists P' tl1' tl2' s1' s2', (P1,s1) --[ tl1' ]-->* (P',s1')
                             /\ (P2,s2) --[ tl2' ]-->* (P',s2') /\ s1' [==] s2').
Proof.
intros.
elim (diamond_4a _ _ _ _ _ _ _ _ H H0); auto.
intros. destroy H1. exists x, x0, x1, x2, x3; auto.
Qed.

(** Useful particular cases. *)

Lemma CCP_ToStar_End : forall c c' tl, c --[ tl ]-->* c' ->
  Main (fst c) = End -> tl = nil /\ c = c'.
Proof.
intros.
inversion H; auto.
exfalso.
induction c, a. simpl in H0; rewrite H0 in H1.
inversion H1. inversion H11.
Qed.

Lemma diamond_5a : forall P s tl1 tl2 P1 s1 P2 s2,
  (P,s) --[ tl1 ]-->* (P1,s1) -> (P,s) --[ tl2 ]-->* (P2,s2) -> Main P2 = End -> 
  (exists tl1' s1', (P1,s1) --[ tl1' ]-->* (P2,s1')
                  /\ s1' [==] s2 /\ length tl1 + length tl1' = length tl2).
Proof.
intros.
elim (diamond_4a _ _ _ _ _ _ _ _ H H0); intros.
destroy H2.
rename x into P', x0 into tl', x1 into tl'', x2 into s', x3 into s''.
elim (CCP_ToStar_End _ _ _ H4 H1); intros.
inversion H7.
exists tl', s'; repeat split; auto.
rewrite H6, plus_0_r in H2; auto.
Qed.

Lemma diamond_5 : forall P s tl1 tl2 P1 s1 P2 s2,
  (P,s) --[ tl1 ]-->* (P1,s1) -> (P,s) --[ tl2 ]-->* (P2,s2) -> Main P2 = End -> 
  (exists tl1' s1', (P1,s1) --[ tl1' ]-->* (P2,s1') /\ s1' [==] s2).
Proof.
intros.
elim (diamond_5a _ _ _ _ _ _ _ _ H H0 H1).
intros. destroy H2; eauto.
Qed.

Lemma termination_unique : forall c tl1 c1 tl2 c2,
  c --[tl1]-->* c1 -> c --[tl2]-->* c2 ->
  Main (fst c1) = End -> Main (fst c2) = End -> snd c1 [==] snd c2.
Proof.
intros.
induction c, c1, c2. induction a, p, p0. simpl.
elim (diamond_4 _ _ _ _ _ _ _ _ H H0); intros.
destroy H3.
elim (CCP_ToStar_End _ _ _ H4 H1); intros.
elim (CCP_ToStar_End _ _ _ H5 H2); intros.
rewrite H6 in H4; rewrite H8 in H5. inversion H4; inversion H5; auto.
Qed.

End Confluence.

End CCBase.

Declare Scope CC_scope.
Delimit Scope CC_scope with CC.

Bind Scope CC_scope with Choreography.
Bind Scope CC_scope with Eta.

Notation "p # e --> q $ x" := (Com _ p e q x) (at level 50, e at level 9) : CC_scope.
Notation "p --> q [ l ]" := (Sel _ p q l) (at level 50) : CC_scope.
Notation "eta '@' ann ';;' C" := (Interaction _ eta ann C) (at level 60, right associativity) : CC_scope.
Notation "'If' p '??' b 'Then' C1 'Else' C2" := (Cond _ p b C1 C2) (at level 60) : CC_scope.
Notation "<< C , s >> --[ rl , D ]--> << C' , s' >>" := (CCC_To _ D C s rl C' s') (at level 100) : CC_scope.
Notation "c --[ tl ]--> c'" := (CCP_To _ c tl c') (at level 50, left associativity) : CC_scope.
Notation "c --[ ts ]-->* c'" := (CCP_ToStar _ c ts c') (at level 50, left associativity) : CC_scope.

Arguments End {Sig}.
Arguments Call {Sig}.
Arguments RT_Call {Sig}.
Arguments Main {Sig}.
Arguments Procs {Sig}.
Arguments Vars {Sig}.
Arguments initial {Sig}.
Arguments within_Xs {Sig}.
Arguments Choreography_WF {Sig}.
Arguments CCC_pn {Sig}.
Arguments CCP_WF {Sig}.