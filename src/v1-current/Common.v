Require Export List.
Require Export ListSet.
Require Export Permutation.
Require Export Setoid.
Require Export Basic.

(** * Decidable types
    Several structures need to be decidable.
    For some annoying reason, the standard library version does not work. *)

Record DecType : Type :=
  { t :> Type;
    eq_dec : forall x y:t, {x = y} + {x <> y} }.

Arguments eq_dec [d].

Section DecidableType.

Variable M : DecType.
Definition eqb (x y:M) := if (eq_dec x y) then true else false.

Notation "x '=?' y" := (eqb x y).

Lemma eqb_eq : forall x y, (x =? y) = true <-> x = y.
Proof.
intros; unfold eqb; elim (eq_dec x y); intros; split; auto.
intro; discriminate H.
Qed.

Lemma eqb_neq : forall x y, (x =? y) = false <-> x <> y.
Proof.
intros; split; intro.
+ contradict H. rewrite <- eqb_eq in H. rewrite H. discriminate.
+ case_eq (x =? y); auto. intro. rewrite eqb_eq in H0. elim H; auto.
Qed.

Lemma eqb_refl : forall x, (x =? x) = true.
Proof.
intro. rewrite eqb_eq. auto.
Qed.

Lemma eqb_sym : forall x y, (x =? y) = (y =? x).
Proof.
intros. case_eq (x =? y); intro; symmetry.
+ rewrite eqb_eq. symmetry. rewrite <- eqb_eq. auto.
+ rewrite eqb_neq. rewrite eqb_neq in H. auto.
Qed.

Lemma eqb_trans : forall x y z,
  (x =? y) = true -> (y =? z) = true -> (x =? z) = true.
Proof.
intros.
rewrite eqb_eq in H, H0; rewrite eqb_eq.
transitivity y; auto.
Qed.

Lemma eqb_ntrans : forall x y z,
  (x =? y) = true -> (y =? z) = false -> (x =? z) = false.
Proof.
intros.
rewrite eqb_eq in H.
rewrite eqb_neq in H0.
rewrite eqb_neq.
intro; apply H0.
transitivity x; auto.
Qed.

Lemma eqb_ntrans' : forall x y z,
  (x =? y) = false -> (y =? z) = true -> (x =? z) = false.
Proof.
intros.
rewrite eqb_eq in H0.
rewrite eqb_neq in H.
rewrite eqb_neq.
intro; apply H.
transitivity z; auto.
Qed.

Lemma DecType_eq : forall T (t:M) (A B:T),
  (if eq_dec t t then A else B) = A.
Proof.
intros. elim eq_dec; auto.
intros. elim b; auto.
Qed.

Lemma DecType_neq : forall T (t t':M) (A B:T), t <> t' ->
  (if eq_dec t t' then A else B) = B.
Proof.
intros. elim eq_dec; auto.
intros. elim H; auto.
Qed.

End DecidableType.

Notation "x '=?' y" := (eqb _ x y).

(** ** Cartesian product of two decidable types. *)

Section UnitType.

Lemma unit_dec : forall (x y:unit), {x = y} + {x <> y}.
Proof. induction x, y; auto. Qed.

Definition Unit := Build_DecType unit unit_dec.

End UnitType.

Section DecProd.

Variable A B:DecType.

Lemma DP_eq_dec : forall (p1 p2:(A*B)), {p1 = p2} + {p1 <> p2}.
Proof.
intros. case p1 as [X p]. case p2 as [Y q].
case (eq_dec p q); case (eq_dec X Y); intros;
  try (right; intro; inversion H; auto; fail).
rewrite e, e0; auto.
Qed.

Definition DecProd := {| t := A*B; eq_dec := DP_eq_dec |}.

End DecProd.

(** ** Booleans as a decidable type *)
Definition Bool := {| t := bool; eq_dec := bool_dec |}.

(** * Labels
    We require that there be exactly two labels (left and right), as this
    is the default practice in many choreography languages. *)

Section Labels.

Inductive label : Type :=
 | left : label
 | right : label
.

Lemma eq_label_dec : forall (l l' : label), { l = l' } + { l <> l' }.
Proof.
decide equality.
Qed.

Definition Label := {| t := label; eq_dec := eq_label_dec |}.

(*
Definition eqb_label (l l':Label) : bool :=
match l, l' with
 | left, left => true
 | right, right => true
 | _, _ => false
end.

Lemma label_eqb_eq : forall (l l':Label), (eqb_label l l') = true <-> l = l'.
Proof.
intros; unfold eqb; elim (eq_label_dec l l'); intros; split; auto.
+ intro. rewrite <- H. case l; auto.
+ generalize b. case l; case l'; try easy.
Qed.

Lemma label_eqb_neq : forall (l l':Label), (eqb_label l l') = false <-> l <> l'.
Proof.
split; intros.
- red. rewrite <- label_eqb_eq, H. intro; inversion H0.
- red in H; rewrite <- label_eqb_eq in H.
  case_eq (eqb_label l l'); auto. tauto.
Qed.

Lemma label_eqb_refl : forall l, eqb_label l l = true.
Proof. intro. rewrite label_eqb_eq. auto. Qed.

Lemma label_eqb_sym : forall l l0, eqb_label l l0 = eqb_label l0 l.
Proof. intros. case l; case l0; auto. Qed.

Lemma label_eqb_trans : forall l l0 l1,
  eqb_label l l0 = true -> eqb_label l0 l1 = true -> eqb_label l l1 = true.
Proof.
intros.
apply label_eqb_eq.
transitivity l0; apply label_eqb_eq; auto.
Qed.

Lemma label_eqb_ntrans : forall l l0 l1,
  eqb_label l l0 = true -> eqb_label l0 l1 = false -> eqb_label l l1 = false.
Proof.
intros.
apply label_eqb_neq.
apply label_eqb_eq in H.
apply label_eqb_neq in H0.
intro; apply H0. transitivity l; auto.
Qed.
*)


End Labels.

(** * Local states
    This is the state of a particular process. It maps the values in the
    process's local set of variables to values.
    The set of variables needs to be decidable. *)


Section LState.

Variable Value Var : DecType.

Definition LState := Var -> Value.

(** ** Equivalence of states *)

Definition Leq_state (s s': LState) : Prop := forall x, s x = s' x.

Notation "s [=] s'" := (Leq_state s s') (at level 50).

Lemma Leq_state_neq : forall x s s', s x <> s' x -> ~ s [=] s'.
Proof.
intros. red. intros.
apply H; auto.
Qed.

Lemma Leq_state_refl : reflexive _ Leq_state.
Proof.
repeat (red; intros). auto.
Qed.

Lemma Leq_state_sym : symmetric _ Leq_state.
Proof.
repeat (red; intros).
apply symmetry, H.
Qed.

Lemma Leq_state_trans : transitive _ Leq_state.
Proof.
red.
intros.
red.
red in H, H0.
intros.
specialize (H x0).
specialize (H0 x0).
rewrite H. apply H0.
Qed.

Add Parametric Relation : LState Leq_state
  reflexivity proved by Leq_state_refl
  symmetry proved by Leq_state_sym
  transitivity proved by Leq_state_trans
  as Leq_state_rel.

(* TODO: Perhaps Add Parametric Morphism *)

(** ** Updating states *)

Definition Lupdate (s:LState) (x:Var) (v:Value) : LState :=
  fun (y:Var) => if (x =? y) then v else (s y).

Lemma Lupdate_read : forall s x v, Lupdate s x v x = v.
Proof.
  intros.
  unfold Lupdate.
  rewrite eqb_refl.
  auto.
Qed.

Lemma Lupdate_read'' : forall s x y v, x <> y ->
  Lupdate s x v y = s y.
Proof.
  intros.
  unfold Lupdate.
  rewrite <- eqb_neq in H; rewrite H; auto.
Qed.

Lemma Lupdate_update : forall s x v w,
  Lupdate (Lupdate s x w) x v [=] Lupdate s x v.
Proof.
intros.
red.
unfold Lupdate.
intro y.
case_eq (x =? y); trivial.
Qed.

Lemma Lupdate_independent' : forall s x y v v', x <> y ->
  Lupdate (Lupdate s y v') x v [=] Lupdate (Lupdate s x v) y v'.
Proof.
red; intros.
unfold Lupdate.
case_eq (x =? x0); case_eq (y =? x0); auto; intros.
elim H; rewrite eqb_eq in H0; rewrite eqb_eq in H1.
transitivity x0; auto.
Qed.

End LState.

Notation "s [=] s'" := (Leq_state _ _ s s') (at level 50).

Arguments Lupdate [Value Var].

(** * Global states
    These are states for a choreography, or for a network as a whole:
    they map each process name to its state.
    Note that all processes are required to use the same sets of variables
    and values. *)

Section GState.

Variable Pid Var Value : DecType.

Definition State := Pid -> (LState Value Var).

(** ** Equivalence of states
    We now define equivalence up to a set of processes: we are often only
    interested in some of those. *)

Definition eq_state (P : list Pid) (s: State) (s': State) : Prop := 
  forall p, In p P -> (s p) [=] (s' p).

Notation "s [= P =] s'" := (eq_state P s s') (at level 50).

Lemma eq_state_neq : forall p P (s s':State),
  ~ s p [=] s' p -> In p P -> ~ s [= P =] s'.
Proof.
intros. red. intros.
apply H; auto.
Qed.

Lemma eq_state_nil : forall s s', s [= nil =] s'.
Proof.
intros. red. intros. contradiction.
Qed.

Lemma eq_state_cons : forall p P s s',
  s p [=] s' p -> s [= P =] s' -> s [= p::P =] s'.
Proof.
intros. red. intros.
inversion H1.
(* head *)
+ rewrite <- H2. auto.
(* tail *)
+ apply H0, H2.
Qed.

Lemma eq_state_hd : forall p P s s', s [= p::P =] s' -> s p [=] s' p.
Proof.
intros. apply H, in_eq.
Qed.

Lemma eq_state_tl : forall p P s s', s [= p::P =] s' -> s [= P =] s'.
Proof.
intros. red. intros. apply H, in_cons, H0.
Qed.

Lemma eq_state_cons_iff : forall p P s s',
  s [= p::P =] s' <-> (s p [=] s' p) /\ s [= P =] s'.
Proof.
split.
+ split; [apply eq_state_hd with P|apply eq_state_tl with p]; apply H.
+ intros. destruct H. apply eq_state_cons; auto.
Qed.

Lemma eq_state_app : forall P P' s s',
  s [= P =] s' -> s [= P' =] s' -> s [= P ++ P' =] s'.
Proof.
intros. red. intros.
apply in_app_or in H1.
destruct H1.
(* p in P *)
+ apply H, H1.
(* p in P' *)
+ apply H0, H1.
Qed.

Lemma eq_state_split : forall P P' s s',
  s [= P ++ P' =] s' -> s [= P =] s' /\ s [= P =] s'.
Proof.
intros. split; red; intros; apply H, in_or_app; auto.
Qed.

Lemma eq_state_refl : forall P, reflexive _ (eq_state P).
Proof. repeat (red; intros). auto. Qed.

Lemma eq_state_sym : forall P, symmetric _ (eq_state P).
Proof. repeat (red; intros). apply symmetry, H, H0. Qed.

Lemma eq_state_trans : forall P, transitive _ (eq_state P).
Proof.
red.
intros.
red.
red in H, H0.
intros.
specialize (H p H1).
specialize (H0 p H1).
apply Leq_state_trans with (y p); auto.
Qed.

Add Parametric Relation P : State (eq_state P)
  reflexivity proved by (eq_state_refl P)
  symmetry proved by (eq_state_sym P)
  transitivity proved by (eq_state_trans P)
  as eq_state_rel.

(* TODO: Perhaps Add Parametric Morphism *)

(** ** Updating the state
    This function updates the local state of the given process. *)

Definition update (s:State) (p:Pid) (x:Var) (v:Value) : State :=
  fun (q:Pid) => if (p =? q) then (Lupdate (s p) x v) else (s q).

Lemma update_read : forall s p x v, update s p x v p x = v.
Proof.
  intros.
  unfold update.
  rewrite eqb_refl.
  apply Lupdate_read; auto.
Qed.

Lemma update_read' : forall s p q x y v, p <> q ->
  update s p x v q y = s q y.
Proof.
  intros.
  unfold update.
  rewrite <- eqb_neq in H; rewrite H; auto.
Qed.

Lemma update_read'' : forall s p q x y v, x <> y ->
  update s p x v q y = s q y.
Proof.
  intros.
  unfold update.
  case_eq (p =? q); auto.
  intros; rewrite Lupdate_read''; auto.
  rewrite eqb_eq in H0; rewrite H0. auto.
Qed.

Lemma update_update : forall s p x v w P,
  update (update s p x w) p x v [= P =] update s p x v.
Proof.
intros.
red.
unfold update.
intro q.
case_eq (p =? q).
+ rewrite eqb_refl; intros.
  apply Lupdate_update.
+ intros; apply Leq_state_refl.
Qed.

Lemma update_not_in : forall s p x v P,
  ~In p P -> s [= P =] update s p x v.
Proof.
intros.
induction P.
+ apply eq_state_nil.
+ apply eq_state_cons_iff.
  apply not_in_cons in H.
  destruct H.
  split.
  - unfold update.
    case_eq (p =? a).
    2: intros; apply Leq_state_refl.
    intro H1. rewrite eqb_eq in H1.
    elim H. contradiction.
  - apply IHP, H0.
Qed.

(** ** Extensional equivalence
    Equivalence of states not up to. *)

Definition eq_state_ext (s s': State) : Prop :=
  forall p, s p [=] s' p.

Notation "s [==] s'" := (eq_state_ext s s') (at level 50).

Lemma eq_state_ext_refl : forall s, s [==] s.
Proof. red; intros. apply Leq_state_refl. Qed.

Lemma eq_state_ext_sym : forall s s', s [==] s' -> s' [==] s.
Proof. red; intros. apply Leq_state_sym. auto. Qed.

Lemma eq_state_ext_trans : forall s s' s'',
  s [==] s' -> s' [==] s'' -> s [==] s''.
Proof. red; intros. apply Leq_state_trans with (s' p); auto. Qed.

Lemma eq_state_ext_congr : forall s s' p x v,
  s [==] s' -> update s p x v [==] update s' p x v.
Proof.
repeat intro.
unfold update.
elim eqb; auto.
2: apply H.
unfold Lupdate.
elim eqb; auto.
apply H.
Qed.

(*
Add Parametric Relation : State eq_state_ext
  reflexivity proved by eq_state_ext_refl
  symmetry proved by eq_state_ext_sym
  transitivity proved by eq_state_ext_trans
  as eq_state_ext_rel.
*)

Lemma update_update_ext : forall s p x v1 v2,
  update (update s p x v2) p x v1 [==] update s p x v1.
Proof.
intros.
red.
unfold update.
rewrite eqb_refl.
intro q; elim eqb; auto.
+ apply Lupdate_update.
+ apply Leq_state_refl.
Qed.

Lemma update_independent : forall s p q x y v v', p <> q ->
  update (update s q y v') p x v [==] update (update s p x v) q y v'.
Proof.
red; intros.
unfold update.
rewrite <- eqb_neq in H; rewrite H.
rewrite eqb_sym in H; rewrite H.
case_eq (p =? p0); case_eq (q =? p0); intros; try apply Leq_state_refl.
rewrite eqb_eq in H0, H1.
rewrite eqb_neq in H.
elim H; transitivity p0; auto.
Qed.

Lemma update_independent' : forall s p x y v v', x <> y ->
  update (update s p y v') p x v [==] update (update s p x v) p y v'.
Proof.
red; intros.
unfold update.
rewrite eqb_refl.
elim eqb.
+ apply Lupdate_independent'; auto.
+ apply Leq_state_refl.
Qed.

End GState.

Ltac ESEr := apply eq_state_ext_refl.
Ltac ESEs := apply eq_state_ext_sym; auto.
Ltac ESEt x := apply eq_state_ext_trans with x; auto.
Ltac eESEt := eapply eq_state_ext_trans; eauto.
Ltac ESEc := apply eq_state_ext_congr.

(** * Evaluation
    Evaluation is parameterized on the types of expressions and values.
    Decidability of expressions makes choreography equality decidable. *)

Record Eval {Expression Vars Input Output : DecType} :=
  { eval : Expression -> (Vars -> Input) -> Output;
    eval_wd : forall f f', (forall x, f x = f' x) ->
      forall e, eval e f = eval e f'}.

Arguments eq_state_ext [Pid Var Value].
Arguments update [Pid Var Value].

Notation "s [==] s'" := (eq_state_ext s s') (at level 50).

(** Both CC and SP use two types of expressions - one
  for values, one for Boolean expressions. Their shared properties
  that depend on the state are proven here. *)

Section EvalState.

Variable Pid Expression Vars Input Output : DecType.
Variable Ev:@Eval Expression Vars Input Output.

Local Definition CSt := State Pid Vars Input.

(** Expression evaluation on the state of a process *)

Definition eval_on_state (e:Expression) (s:CSt) (p:Pid) : Output := eval Ev e (s p).

(** Consistency with state equivalence. *)
Lemma eval_eq : forall e s s' p, s [==] s' ->
  eval_on_state e s p = eval_on_state e s' p.
Proof.
intros; unfold eval_on_state; simpl.
apply eval_wd, H.
Qed.

Lemma eval_neq : forall e s p q x v, p <> q ->
  eval_on_state e s p = eval_on_state e (update s q x v) p.
Proof.
intros; unfold eval_on_state; simpl.
replace (s p) with (update s q x v p); auto.
unfold update.
case_eq (q =? p); auto.
intro; elim H.
apply eqb_eq in H0; auto.
Qed.

End EvalState.

Arguments eval_on_state [Pid Expression Vars Input Output].
Arguments eval_eq [Pid Expression Vars Input Output].
Arguments eval_neq [Pid Expression Vars Input Output].

Section Transitions.

Variable Pid Value Var RecVar : DecType.

(** * Transition labels *)

Inductive TransitionLabel : Type :=
| L_Com (p:Pid) (v:Value) (q:Pid) : TransitionLabel
| L_Sel (p:Pid) (q:Pid) (l:Label) : TransitionLabel
| L_Tau (p:Pid) : TransitionLabel
.

Lemma TransitionLabel_eq_dec : forall (x y:TransitionLabel), {x=y} + {x<>y}.
Proof. decide equality; apply eq_dec. Qed.

(** The semantics uses a labeled transition system with more expressive labels. *)

Inductive RichLabel : Type :=
| R_Com (p:Pid) (v:Value) (q:Pid) (x:Var) : RichLabel
| R_Sel (p:Pid) (q:Pid) (l:Label) : RichLabel
| R_Cond (p:Pid) : RichLabel
| R_Call (X:RecVar) (p:Pid) : RichLabel
.

Lemma RichLabel_eq_dec : forall (x y:RichLabel), {x=y} + {x<>y}.
Proof. decide equality; apply eq_dec. Qed.

Definition tpn (t:RichLabel) : list Pid :=
  match t with
  | R_Com p v q _ => p::q::nil
  | R_Sel p q l   => p::q::nil
  | R_Cond p      => p::nil
  | R_Call _ p    => p::nil
end.

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

(** Disjointness between a process/list of processes and a label
  - used for a lot of properties of the semantics, these lemmas
  are useful for reasoning about it. *)

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

Lemma disjoint_ps_remove : forall p ps tl, disjoint_ps_rl ps tl ->
  disjoint_ps_rl (set_remove' (@eq_dec _) p ps) tl.
Proof.
intros.
apply disjoint_ps_char; intros.
apply disjoint_ps_rl_In with ps; auto.
eapply set_remove'_1; apply H0.
Qed.

End Transitions.

Arguments R_Com [Pid Value Var RecVar].
Arguments R_Sel [Pid Value Var RecVar].
Arguments R_Cond [Pid Value Var RecVar].
Arguments R_Call [Pid Value Var RecVar].

Arguments L_Com [Pid Value].
Arguments L_Sel [Pid Value].
Arguments L_Tau [Pid Value].

Arguments forget [Pid Value Var RecVar].
Arguments disjoint_ps_rl [Pid Value Var RecVar].
Arguments disjoint_p_rl [Pid Value Var RecVar].
