Require Export List.
Require Export ListSet.
Require Export Permutation.
Require Export Setoid.
Require Export Basic.

(** * Labels
    We require that there be exactly two labels (left and right), as this
    is the default practice in many choreography languages. *)

Section Labels.

Inductive Label : Type :=
 | left : Label
 | right : Label
.

Lemma eq_label_dec : forall (l l' : Label), { l = l' } + { l <> l' }.
Proof.
decide equality.
Qed.

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

Lemma label_eqb_refl : forall l, eqb_label l l = true.
Proof. intro. rewrite label_eqb_eq. auto. Qed.

Lemma label_eqb_sym : forall l l0, eqb_label l l0 = eqb_label l0 l.
Proof. intros. case l; case l0; auto. Qed.

End Labels.

(** * Decidable types
    Several structures need to be decidable.
    For some annoying reason, the standard library version does not work. *)

Module Type DecType.

Parameter t : Type.
Parameter eq_dec : forall x y:t, {x = y} + {x <> y}.

End DecType.

Module DecidableType (Import M:DecType).

Definition eqb (x y:t) := if (eq_dec x y) then true else false.

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

End DecidableType.

(** ** Cartesian product of two decidable types. *)

Module DecProd (A B:DecType) <: DecType.

Definition t : Type := A.t * B.t.

Lemma eq_dec : forall (p1 p2:t), {p1 = p2} + {p1 <> p2}.
Proof.
intros. case p1 as [X p]. case p2 as [Y q].
case (B.eq_dec p q); case (A.eq_dec X Y); intros;
  try (right; intro; inversion H; auto; fail).
rewrite e, e0; auto.
Qed.

End DecProd.

(** ** Booleans as a decidable type *)
Module Bool <: DecType.

Definition t := bool.
Definition eq_dec := bool_dec.

End Bool.

(** * Local states
    This is the state of a particular process. It maps the values in the
    process's local set of variables to values.
    The set of variables needs to be decidable. *)

Module LState (V X : DecType).

Module Vdec := DecidableType V.
Module Xdec := DecidableType X.

Definition Value := V.t. 
Definition Value_dec := Vdec.eqb.
Definition Var := X.t.
Definition Var_dec := Xdec.eqb.

Definition State := Var -> Value.

(** ** Equivalence of states *)

Definition eq_state (s s': State) : Prop := forall x, s x = s' x.

Lemma eq_state_neq : forall x s s', s x <> s' x -> ~ eq_state s s'.
Proof.
intros. red. intros.
apply H; auto.
Qed.

(* Not true: requires a finite set of variables.
Lemma eq_state_dec : forall s1 s2,
  { eq_state s1 s2 } + { ~eq_state s1 s2}.
Proof.
intros.
induction P.
(* P is empty *)
+ left. red. intros. contradiction.
(* a :: P *)
+ case IHP; clear IHP; intro.
  - case_eq (Value_dec (s1 a) (s2 a)).
    * left. apply eq_state_cons; auto. apply (Vdec.eqb_eq); auto.
    * right. contradict H. rewrite not_false_iff_true. rewrite Vdec.eqb_eq. apply eq_state_hd with P, H.
  - right. contradict n. apply eq_state_tl with a, n.
Qed.
*)

Lemma eq_state_refl : reflexive _ eq_state.
Proof.
repeat (red; intros). auto.
Qed.

Lemma eq_state_sym : symmetric _ eq_state.
Proof.
repeat (red; intros).
apply symmetry, H.
Qed.

Lemma eq_state_trans : transitive _ eq_state.
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

Add Parametric Relation : State eq_state
  reflexivity proved by eq_state_refl
  symmetry proved by eq_state_sym
  transitivity proved by eq_state_trans
  as eq_state_rel.

(* TODO: Perhaps Add Parametric Morphism *)

(** ** Updating states *)

Definition update (s:State) (x:Var) (v:Value) : State :=
  fun (y:Var) => if (Var_dec x y) then v else (s y).

Lemma update_read : forall s x v, update s x v x = v.
Proof.
  intros.
  unfold update.
  rewrite Xdec.eqb_refl.
  auto.
Qed.

Lemma update_read'' : forall s x y v, x <> y ->
  update s x v y = s y.
Proof.
  intros.
  unfold update, Var_dec.
  rewrite <- Xdec.eqb_neq in H; rewrite H; auto.
Qed.

Lemma update_update : forall s x v w,
  eq_state (update (update s x w) x v) (update s x v).
Proof.
intros.
red.
unfold update.
intro y.
case_eq (Var_dec x y); trivial.
Qed.

Lemma update_independent' : forall s x y v v', x <> y ->
  eq_state (update (update s y v') x v) (update (update s x v) y v').
Proof.
red; intros.
unfold update.
case_eq (Var_dec x x0); case_eq (Var_dec y x0); auto; intros.
elim H; rewrite Xdec.eqb_eq in H0; rewrite Xdec.eqb_eq in H1.
transitivity x0; auto.
Qed.

End LState.

(** * Global states
    These are states for a choreography, or for a network as a whole:
    they map each process name to its state.
    Note that all processes are required to use the same sets of variables
    and values. *)

Module GState (P V X : DecType).

Module Import LSt := LState V X.

Module Pdec := DecidableType P.

Definition Pid := P.t.
Definition Pid_dec := Pdec.eqb.

Definition State := Pid -> LSt.State.

(** ** Equivalence of states
    We now define equivalence up to a set of processes: we are often only
    interested in some of those. *)

Definition eq_state (P : list Pid) (s: State) (s': State) : Prop := 
  forall p, In p P -> LSt.eq_state (s p) (s' p).

(*
Definition eq_state (P : set Pid) (s1: State) (s2: State) : Prop :=
set_fold_right (fun p => fun b => b /\ (s1 p = s2 p)) P True.
*)

Lemma eq_state_neq : forall p P (s s':State),
  ~LSt.eq_state (s p) (s' p) -> In p P -> ~ eq_state P s s'.
Proof.
intros. red. intros.
apply H; auto.
Qed.

Lemma eq_state_nil : forall s s', eq_state nil s s'.
Proof.
intros. red. intros. contradiction.
Qed.

Lemma eq_state_cons : forall p P s s',
  (LSt.eq_state (s p) (s' p)) -> eq_state P s s' -> eq_state (p::P) s s'.
Proof.
intros. red. intros.
inversion H1.
(* head *)
+ rewrite <- H2. auto.
(* tail *)
+ apply H0, H2.
Qed.

Lemma eq_state_hd : forall p P s s',
  eq_state (p::P) s s' -> LSt.eq_state (s p) (s' p).
Proof.
intros. apply H, in_eq.
Qed.

Lemma eq_state_tl : forall p P s s',
  eq_state (p::P) s s' -> eq_state P s s'.
Proof.
intros. red. intros. apply H, in_cons, H0.
Qed.

Lemma eq_state_cons_iff : forall p P s s',
  eq_state (p::P) s s' <-> (LSt.eq_state (s p) (s' p)) /\ eq_state P s s'.
Proof.
split.
+ split; [apply eq_state_hd with P|apply eq_state_tl with p]; apply H.
+ intros. destruct H. apply eq_state_cons; auto.
Qed.

Lemma eq_state_app : forall P P' s s',
  eq_state P s s' -> eq_state P' s s' -> eq_state (P ++ P') s s'.
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
  eq_state (P ++ P') s s' -> eq_state P s s' /\ eq_state P' s s'.
Proof.
intros. split; red; intros; apply H, in_or_app; auto.
Qed.

(* Not true: requires a finite set of variables.
Lemma eq_state_dec : forall P s1 s2,
  { eq_state P s1 s2 } + { ~eq_state P s1 s2}.
Proof.
intros.
induction P.
(* P is empty *)
+ left. red. intros. contradiction.
(* a :: P *)
+ case IHP; clear IHP; intro.
  - case_eq (Value_dec (s1 a) (s2 a)).
    * left. apply eq_state_cons; auto. apply (Vdec.eqb_eq); auto.
    * right. contradict H. rewrite not_false_iff_true. rewrite Vdec.eqb_eq. apply eq_state_hd with P, H.
  - right. contradict n. apply eq_state_tl with a, n.
Qed.
*)

Lemma eq_state_refl : forall P, reflexive _ (eq_state P).
Proof.
repeat (red; intros). auto.
Qed.

Lemma eq_state_sym : forall P, symmetric _ (eq_state P).
Proof.
repeat (red; intros).
apply symmetry, H, H0.
Qed.

Lemma eq_state_trans : forall P, transitive _ (eq_state P).
Proof.
red.
intros.
red.
red in H, H0.
intros.
specialize (H p H1).
specialize (H0 p H1).
rewrite H. apply H0.
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
  fun (q:Pid) => if (Pid_dec p q) then (LSt.update (s p) x v)
                                  else (s q).

Lemma update_read : forall s p x v, update s p x v p x = v.
Proof.
  intros.
  unfold update.
  rewrite Pdec.eqb_refl.
  apply LSt.update_read; auto.
Qed.

Lemma update_read' : forall s p q x y v, p <> q ->
  update s p x v q y = s q y.
Proof.
  intros.
  unfold update, Pid_dec.
  rewrite <- Pdec.eqb_neq in H; rewrite H; auto.
Qed.

Lemma update_read'' : forall s p q x y v, x <> y ->
  update s p x v q y = s q y.
Proof.
  intros.
  unfold update, Pid_dec.
  elim (P.eq_dec p q); intro.
  generalize a; intro. rewrite <- Pdec.eqb_eq in a; rewrite a, a0. apply update_read''; auto.
  rewrite <- Pdec.eqb_neq in b; rewrite b. auto.
Qed.

Lemma update_update : forall s p x v w P,
  eq_state P (update (update s p x w) p x v) (update s p x v).
Proof.
intros.
red.
unfold update.
intro q.
case_eq (Pid_dec p q).
+ rewrite Pdec.eqb_refl; intros.
  apply LSt.update_update.
+ reflexivity.
Qed.

Lemma update_not_in : forall s p x v P,
  ~In p P -> eq_state P s (update s p x v).
Proof.
intros.
induction P.
+ apply eq_state_nil.
+ apply eq_state_cons_iff.
  apply not_in_cons in H.
  destruct H.
  split.
  - unfold update.
    case_eq (Pid_dec p a).
    2: reflexivity.
    intro H1. rewrite Pdec.eqb_eq in H1.
    elim H. contradiction.
  - apply IHP, H0.
Qed.

(** ** Extensional equivalence
    Equivalence of states not up to. *)

Definition eq_state_ext (s s': State) : Prop :=
  forall p, LSt.eq_state (s p) (s' p).

Lemma eq_state_ext_refl : forall s, eq_state_ext s s.
Proof. red; intros. apply LSt.eq_state_refl. Qed.

Lemma eq_state_ext_sym : forall s s', eq_state_ext s s' -> eq_state_ext s' s.
Proof. red; intros. apply LSt.eq_state_sym. auto. Qed.

Lemma eq_state_ext_trans : forall s s' s'',
  eq_state_ext s s' -> eq_state_ext s' s'' -> eq_state_ext s s''.
Proof. red; intros. transitivity (s' p); auto. Qed.

Lemma eq_state_ext_congr : forall s s' p x v,
  eq_state_ext s s' -> eq_state_ext (update s p x v) (update s' p x v).
Proof.
repeat intro.
unfold update.
elim Pid_dec; auto.
2: apply H.
unfold LSt.update.
elim Var_dec; auto.
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
  eq_state_ext (update (update s p x v2) p x v1) (update s p x v1).
Proof.
intros.
red.
unfold update.
rewrite Pdec.eqb_refl.
intro q; elim Pid_dec; auto.
+ apply LSt.update_update.
+ reflexivity.
Qed.

Lemma update_independent : forall s p q x y v v', p <> q ->
  eq_state_ext (update (update s q y v') p x v) (update (update s p x v) q y v').
Proof.
red; intros.
unfold update.
unfold Pid_dec.
rewrite <- Pdec.eqb_neq in H; rewrite H.
rewrite Pdec.eqb_sym in H; rewrite H.
case_eq (Pdec.eqb p p0); case_eq (Pdec.eqb q p0); try reflexivity; intros.
rewrite Pdec.eqb_eq in H0, H1.
rewrite Pdec.eqb_neq in H.
elim H; transitivity p0; auto.
Qed.

Lemma update_independent' : forall s p x y v v', x <> y ->
  eq_state_ext (update (update s p y v') p x v) (update (update s p x v) p y v').
Proof.
red; intros.
unfold update.
rewrite Pdec.eqb_refl.
elim Pid_dec.
+ apply LSt.update_independent'; auto.
+ reflexivity.
Qed.

Ltac ESEr := apply eq_state_ext_refl.
Ltac ESEs := apply eq_state_ext_sym; auto.
Ltac ESEt x := apply eq_state_ext_trans with x; auto.
Ltac eESEt := eapply eq_state_ext_trans; eauto.
Ltac ESEc := apply eq_state_ext_congr.

End GState.

(** * Evaluation
    Evaluation is parameterized on the types of expressions and values.
    Decidability of expressions makes choreography equality decidable. *)

Module Type Eval (Expression Vars Input Output : DecType).

Parameter eval : Expression.t -> (Vars.t -> Input.t) -> Output.t.
Parameter eval_wd : forall f f', (forall x, f x = f' x) -> 
  forall e, eval e f = eval e f'.

End Eval.

(** In both MC and SP, there are two modules of expressions - one
  for values, one for Boolean expressions. Their shared properties
  that depend on the state are proven in this module. *)

Module EvalState (Pid Expression Vars Input Output : DecType)
  (Ev:Eval Expression Vars Input Output).

Module Export CSt := GState Pid Input Vars.

(** Expression evaluation on the state of a process *)

Definition eval_on_state (e:Expression.t) (s:State) (p:Pid.t) : Output.t := Ev.eval e (s p).

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

End EvalState.

Module Transitions (P V X R:DecType).

Module Export PSt := LState V X.
Module Export CSt := GState P V X.

Definition RecVar := R.t.

(** * Transition labels *)

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

(** The semantics uses a labeled transition system with more expressive labels. *)

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
  disjoint_ps_rl (set_remove' P.eq_dec p ps) tl.
Proof.
intros.
apply disjoint_ps_char; intros.
apply disjoint_ps_rl_In with ps; auto.
eapply set_remove'_1; apply H0.
Qed.

End Transitions.
