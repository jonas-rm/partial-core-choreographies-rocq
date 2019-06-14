Require Export Basic.
Require Export Common.

Local Open Scope nat_scope.

(** * The general type of MC choreographies
  This type is parameterized over sets of process identifiers,
  values, expressions and recursion variables. *)

Module MCBase (P E V R: DecType) (Import Ev : Eval E V).

Module Import St := State P V.
Module Pdec := DecidableType P.
Module Edec := DecidableType E.
Module Vdec := DecidableType V.
Module Rdec := DecidableType R.

Definition Pid := P.t.
Definition Pid_dec := Pdec.eqb.
Definition Expr := E.t.
Definition Expr_dec := Edec.eqb.
Definition Value := V.t.
Definition Value_dec := Vdec.eqb.
Definition RecVar := R.t.
Definition RecVar_dec := Rdec.eqb.
Definition State := St.State.

(** ** Syntax of MC choreographies. *)

Section Syntax.

(** Communication actions. *)

Inductive Eta : Type :=
 | Com : Pid -> Expr -> Pid -> Eta
 | Sel : Pid -> Pid -> Label -> Eta
.

Lemma eta_eq_dec : forall (eta eta':Eta), { eta = eta' } + { eta <> eta' }.
Proof.
decide equality; try apply P.eq_dec.
+ apply E.eq_dec.
+ decide equality.
Qed.

Definition disjoint (p q r s:Pid) :=  p <> r /\ p <> s /\ q <> r /\ q <> s.

Lemma disjoint_sym : forall p q r s, disjoint p q r s -> disjoint r s p q.
Proof.
intros; inversion H; inversion_clear H1; inversion_clear H3; repeat split; auto.
Qed.

Definition independent (eta1 eta2:Eta) : Prop :=
match eta1, eta2 with
 | Com p _ q, Com r _ s => disjoint p q r s
 | Com p _ q, Sel r s _ => disjoint p q r s
 | Sel p q _, Com r _ s => disjoint p q r s
 | Sel p q _, Sel r s _ => disjoint p q r s
end.

Lemma independent_sym : forall eta eta', independent eta eta' -> independent eta' eta.
Proof.
intros; induction eta; induction eta'; inversion H; inversion_clear H1; inversion_clear H3; repeat split; auto.
Qed.

Definition unused (r:Pid) (eta:Eta) : Prop :=
match eta with
 | Com p _ q => p <> r /\ q <> r
 | Sel p q _ => p <> r /\ q <> r
end.

(** Choreographies. *)

Inductive Choreography : Type :=
 | End : Choreography
 | Call : RecVar -> Choreography
 | Interaction : Eta -> Choreography -> Choreography
 | Cond : Pid -> Pid -> Choreography -> Choreography -> Choreography
 | Rec : RecVar -> Choreography -> Choreography -> Choreography
.

Lemma chor_eq_dec : forall (C C':Choreography), { C = C' } + { C <> C' }.
Proof.
decide equality; try apply P.eq_dec; try apply R.eq_dec.
apply eta_eq_dec.
Qed.

(** Free and bound procedure names in a choreography. *)
Fixpoint Free (X:RecVar) (C:Choreography) : Prop :=
match C with
| End                => False
| Call Y             => X = Y
| Interaction eta C' => Free X C'
| Cond p q C1 C2     => Free X C1 \/ Free X C2
| Rec Y CY C'        => X <> Y /\ (Free X CY \/ Free X C')
end.

Fixpoint Bound (X:RecVar) (C:Choreography) : Prop :=
match C with
| End                => False
| Call Y             => False
| Interaction eta C' => Bound X C'
| Cond p q C1 C2     => Bound X C1 \/ Bound X C2
| Rec Y CY C'        => X = Y \/ Bound X CY \/ Bound X C'
end.

(** A choreography is well-formed if it does not contain self-communications or free recursion variables,
    and all recursive calls are guarded. *)

Fixpoint guarded (C:Choreography) : Prop :=
match C with
| End => True
| Call X => False
| Interaction eta C' => True
| Cond p q C1 C2 => True
| Rec X CX C' => guarded CX /\ guarded C'
end.

Fixpoint WellFormed_ctx (C:Choreography) (l:list RecVar) : Prop :=
match C with
| End => True
| Call X => In X l
| Interaction eta C' => match eta with
                        | Com p _ q => p <> q /\ WellFormed_ctx C' l
                        | Sel p q _ => p <> q /\ WellFormed_ctx C' l
                        end
| Cond p q C1 C2 => p <> q /\ WellFormed_ctx C1 l /\ WellFormed_ctx C2 l
| Rec X C1 C2 => WellFormed_ctx C1 (X::l) /\ (guarded C1) /\ WellFormed_ctx C2 (X::l)
end.

Definition WellFormed (C:Choreography) : Prop := WellFormed_ctx C nil.

(** Set of process names in a choreography. *)

Definition pn_eta (e:Eta) : list Pid :=
match e with
| Com p _ q => (cons p (cons q nil))
| Sel p q _ => (cons p (cons q nil))
end.

Definition set_union_pid := set_union P.eq_dec.

Fixpoint pn (C:Choreography) : list Pid :=
match C with
| End => nil
| Call X => nil
| Interaction eta C' => (set_union_pid (pn_eta eta) (pn C'))
| Cond p q C1 C2 => (set_union_pid (set_union_pid (cons p (cons q nil)) (pn C1)) (pn C2))
| Rec X C1 C2 => (set_union_pid (pn C1) (pn C2))
end.

Lemma pn_is_set (C:Choreography) : WellFormed C -> NoDup(pn C).
Proof.
intro.
red in H.
assert (forall l, WellFormed_ctx C l -> NoDup (pn C)); eauto.
clear H; induction C; intros.
+ (* End *)
  apply NoDup_nil.
+ (* X *)
  apply NoDup_nil.
+ (* e; C *)
  simpl.
  apply set_union_nodup.
  simpl in H.
  induction e; inversion_clear H.
  - (* Com *)
    simpl; repeat apply NoDup_cons; simpl; auto.
    intro.
    inversion_clear H; auto.
    apply NoDup_nil.
  - (* Sel *)
    simpl; repeat apply NoDup_cons; simpl; auto.
    intro.
    inversion_clear H; auto.
    apply NoDup_nil.
   - induction e; inversion H; eauto.
+ (* Cond *)
  inversion H.
  inversion_clear H1.
  simpl.
  repeat apply set_union_nodup; eauto.
  simpl; repeat apply NoDup_cons; simpl; auto.
  intro.
  inversion_clear H1; auto.
  apply NoDup_nil.
+ (* Def *)
  inversion H.
  inversion_clear H1.
  simpl.
  repeat apply set_union_nodup; auto.
  simpl; repeat apply NoDup_cons; simpl; eauto.
  simpl; repeat apply NoDup_cons; simpl; eauto.
Qed.

End Syntax.

(** Pretty-printing rules for choreographies. *)

Notation "p # e --> q" := (Com p e q) (at level 50, e at level 9, format "p # e --> q").
Notation "p --> q [ l ]" := (Sel p q l) (at level 50, format "p --> q [ l ]").
Notation "eta ';' C" := (Interaction eta C) (at level 60, right associativity).
Notation "'If' p '==' q 'Then' C1 'Else' C2" := (Cond p q C1 C2) (at level 60).
Notation "'Def' X '==' C1 'In' C2" := (Rec X C1 C2) (at level 60).

(* Check (1-->2[left]). *)
(* Check (1#this--> 2). *)

(** ** Syntactic properties *)

Section Syntactic_Properties.

(** Inversion results for free and bound variables. *)

Lemma NotFreeThen : forall X p q C1 C2, ~Free X (If p == q Then C1 Else C2) -> ~Free X C1.
Proof. intros. intro. apply H. constructor. auto. Qed.

Lemma NotFreeElse : forall X p q C1 C2, ~Free X (If p == q Then C1 Else C2) -> ~Free X C2.
Proof. intros. intro. apply H. try (constructor; auto; fail). Qed.

Lemma NotFreeDef : forall X Y CY C, X <> Y -> ~Free X (Def Y == CY In C) -> ~Free X CY.
Proof. intros. intro. apply H0. constructor; auto. Qed.

Lemma NotFreeRec : forall X Y CY C, X <> Y -> ~Free X (Def Y == CY In C) -> ~Free X C.
Proof. intros. intro. apply H0. try (constructor; auto; fail). Qed.

Lemma NotBoundThen : forall X p q C1 C2, ~Bound X (If p == q Then C1 Else C2) -> ~Bound X C1.
Proof. intros. intro. apply H. constructor. auto. Qed.

Lemma NotBoundElse : forall X p q C1 C2, ~Bound X (If p == q Then C1 Else C2) -> ~Bound X C2.
Proof. intros. intro. apply H. try (constructor; auto; fail). Qed.

Lemma NotBound_neq : forall X Y CY C, ~Bound X (Def Y == CY In C) -> X <> Y.
Proof. intros. intro. apply H. constructor; auto. Qed.

Lemma NotBoundDef : forall X Y CY C, ~Bound X (Def Y == CY In C) -> ~Bound X CY.
Proof. intros. intro. apply H. try (constructor; auto; fail). Qed.

Lemma NotBoundRec : forall X Y CY C, ~Bound X (Def Y == CY In C) -> ~Bound X C.
Proof. intros. intro. apply H. try (constructor; auto; fail). Qed.

(** Properties of well-formedness. *)

Lemma WellFormed_ctx_mon : forall C l, WellFormed_ctx C l ->
  forall l', (forall X, List.In X l -> List.In X l') -> WellFormed_ctx C l'.
Proof.
induction C; simpl; intros; auto.
+ induction e; destroy_as H H'; split; eauto.
+ destroy_as H H'; repeat split; eauto.
+ destroy_as H H'; repeat split; auto.
  - apply IHC1 with (r::l); auto.
    intros X HX; inversion_clear HX; simpl; auto.
  - apply IHC2 with (r::l); auto.
    intros X HX; inversion_clear HX; simpl; auto.
Qed.

Lemma WellFormed_ctx_simpl : forall C l X, WellFormed_ctx C (X::l) ->
  ~Free X C -> WellFormed_ctx C l.
Proof.
induction C; simpl; intros; auto.
+ inversion_clear H; auto.
  elim H0; auto.
+ induction e; inversion_clear H; split; eauto.
+ destroy_as H H'; split; auto.
  split; [eapply IHC1 | eapply IHC2]; eauto.
+ destroy_as H H'.
  case_eq (RecVar_dec X r); intro.
  - rewrite Rdec.eqb_eq in H3.
    assert (forall Y, List.In Y (r::X::l) -> List.In Y (r::l)).
    intros. inversion_clear H4; try rewrite H5; [left | rewrite <- H3]; auto.
    repeat split; auto; apply WellFormed_ctx_mon with (r::X::l); auto.
  - rewrite Rdec.eqb_neq in H3. 
    generalize (NotFreeDef _ _ _ _ H3 H0).
    generalize (NotFreeRec _ _ _ _ H3 H0).
    assert (forall Y, List.In Y (r::X::l) -> List.In Y (X::r::l)).
    1: { intros. inversion_clear H4; try rewrite H5; [right; left | idtac]; auto.
         inversion_clear H5; try rewrite H6; [left | right; right]; auto.
    }
    repeat split; auto; [apply IHC1 with X | apply IHC2 with X]; auto;
      eapply WellFormed_ctx_mon; eauto.
Qed.

Lemma DefEta_wf_ctx : forall X CX eta C l,
  WellFormed_ctx (Def X == CX In (eta;C)) l <-> WellFormed_ctx (eta; Def X == CX In C) l.
Proof.
intros.
induction eta; simpl; split; intro H'; destroy H'; repeat split; auto.
Qed.

Lemma DefEta_wf : forall X CX eta C,
  WellFormed (Def X == CX In (eta;C)) <-> WellFormed (eta; Def X == CX In C).
Proof.
intros; apply DefEta_wf_ctx.
Qed.

Lemma CondEta_wf_ctx : forall X CX p q C1 C2 l,
  WellFormed_ctx (Def X == CX In (If p == q Then C1 Else C2)) l <-> WellFormed_ctx (If p == q Then Def X == CX In C1 Else Def X == CX In C2) l.
Proof.
intros.
simpl; split; intro H'; destroy H'; repeat split; auto.
destroy_as H0 H''; auto.
Qed.

Lemma CondEta_wf : forall X CX p q C1 C2,
  WellFormed (Def X == CX In (If p == q Then C1 Else C2)) <-> WellFormed (If p == q Then Def X == CX In C1 Else Def X == CX In C2).
Proof.
intros; apply CondEta_wf_ctx.
Qed.

End Syntactic_Properties.

(** ** Semantics of MC. *)

Section Semantics_Definitions.

(* Structural precongruence is defined in two steps.
   One-step congruence contains exactly one swap or unfolding; then we close
   under reflexivity and transitivity. For unfolding, we need some previous work. *)

Inductive Unfolded X CX : Choreography -> Choreography -> Prop :=
  | UVar : Unfolded X CX (Call X) CX
  | UEta eta C1 C2 : Unfolded X CX C1 C2 -> Unfolded X CX (eta;C1) (eta;C2)
  | UThen p q C1 C2 C' : Unfolded X CX C1 C2 -> Unfolded X CX (If p == q Then C1 Else C') (If p == q Then C2 Else C')
  | UElse p q C' C1 C2 : Unfolded X CX C1 C2 -> Unfolded X CX (If p == q Then C' Else C1) (If p == q Then C' Else C2)
  | URec Y CY C1 C2: X <> Y -> Unfolded X CX C1 C2 -> Unfolded X CX (Def Y == CY In C1) (Def Y == CY In C2)
.

Inductive MC_Precongr_step : Choreography -> Choreography -> Prop :=
 | PB_Refl C : MC_Precongr_step C C
 | EtaEta eta1 eta2 C : independent eta1 eta2 -> MC_Precongr_step (eta1; eta2; C) (eta2; eta1; C)
 | EtaCond eta p q C1 C2 : unused p eta -> unused q eta -> MC_Precongr_step (eta; (If p == q Then C1 Else C2)) (If p == q Then (eta; C1) Else (eta; C2))
 | CondEta eta p q C1 C2 : unused p eta -> unused q eta -> MC_Precongr_step (If p == q Then (eta; C1) Else (eta; C2)) (eta; (If p == q Then C1 Else C2))
 | CondCond p q r s C1 C2 C3 C4 : disjoint p q r s -> MC_Precongr_step (If p == q Then (If r == s Then C1 Else C2) Else (If r == s Then C3 Else C4))
                                                               (If r == s Then (If p == q Then C1 Else C3) Else (If p == q Then C2 Else C4))
 | EtaRec eta X CX C : MC_Precongr_step (eta; Def X == CX In C) (Def X == CX In (eta;C))
 | RecEta eta X CX C : MC_Precongr_step (Def X == CX In (eta;C)) (eta; Def X == CX In C)
 | CondRec p q X CX C1 C2 : MC_Precongr_step (If p == q Then Def X == CX In C1 Else Def X == CX In C2) (Def X == CX In If p == q Then C1 Else C2)
 | RecCond p q X CX C1 C2 : MC_Precongr_step (Def X == CX In If p == q Then C1 Else C2) (If p == q Then Def X == CX In C1 Else Def X == CX In C2)
 | RecRec X CX Y CY C : X <> Y -> ~Free X CY -> ~Free Y CX -> MC_Precongr_step (Def X == CX In (Def Y == CY In C)) (Def Y == CY In (Def X == CX In C))
 | Unfold X CX C1 C2 : Unfolded X CX C1 C2 -> MC_Precongr_step (Def X == CX In C1) (Def X == CX In C2)
 | Garbage X C : MC_Precongr_step (Def X == C In End) End
 | CtxEta eta C1 C2 : MC_Precongr_step C1 C2 -> MC_Precongr_step (eta; C1) (eta; C2)
 | CtxThen p q C' C'' C : MC_Precongr_step C' C'' -> MC_Precongr_step (If p == q Then C' Else C) (If p == q Then C'' Else C)
 | CtxElse p q C C' C'' : MC_Precongr_step C' C'' -> MC_Precongr_step (If p == q Then C Else C') (If p == q Then C Else C'')
 | CtxRec X C1 C2 C2' : MC_Precongr_step C2 C2' -> MC_Precongr_step (Def X == C1 In C2) (Def X == C1 In C2')
.

Inductive MC_Precongr : Choreography -> Choreography -> Prop :=
 | MCP_Refl C : MC_Precongr C C
 | MCP_Step C1 C2 C3: MC_Precongr_step C1 C2 -> MC_Precongr C2 C3 -> MC_Precongr C1 C3
.

Definition Configuration : Type := Choreography * State.

Definition WellFormedConf (conf:Configuration) : Prop := WellFormed (fst conf).

(** Expression evaluation on the state of a process *)

Definition evaluate_on_state (e:Expr) (s:State) (p:Pid) : Value := eval e (s p).

(** One-step and multi-step reduction. Multi-step reduction is simply a reflexive and transitive closure. *)

Inductive MCTo : Configuration -> Configuration -> Prop :=
 | C_Com p e q C s : MCTo ( Com p e q; C, s ) ( C, (update s q (evaluate_on_state e s p)) )
 | C_Sel p q l C s : MCTo ( Sel p q l; C, s ) ( C, s )
 | C_Then p q C1 C2 s : (s p = s q) -> MCTo ( If p == q Then C1 Else C2, s ) ( C1, s )
 | C_Else p q C1 C2 s : (s p <> s q) -> MCTo ( If p == q Then C1 Else C2, s ) ( C2, s )
 | C_Ctx X C1 C2 C2' s s' : MCTo (C2,s) (C2',s') -> MCTo ( Def X == C1 In C2,s ) ( Def X == C1 In C2',s')
 | C_Struct C1 C1' C2 C2' s1 s2 : MC_Precongr C1 C1' -> MC_Precongr C2' C2 -> MCTo (C1', s1) (C2', s2) -> MCTo (C1, s1) (C2, s2)
.

(* We'd love to use the library definitions, but they just don't work -- and give horrible names. *)

Inductive MCToStar : Configuration -> Configuration -> Prop :=
 | MCT_Refl c : MCToStar c c
 | MCT_Step c1 c2 c3 : MCTo c1 c2 -> MCToStar c2 c3 -> MCToStar c1 c3
.

Definition terminated (C:Choreography) : Prop := MC_Precongr C End.

(** ** Head reductions

    Head reductions do not use structural precongruence.
*)

Fixpoint pure_call (C:Choreography) : Prop :=
match C with
| Call _ => True
| Def _ == _ In C2 => pure_call C2
| _ => False
end.

Lemma pure_call_dec : forall C, {pure_call C} + {~pure_call C}.
Proof.
induction C; simpl; auto.
Qed.

Fixpoint has_head_action (C:Choreography) : Prop :=
match C with
| End => False
| Call X => False
| eta; C' => True
| If p == q Then C1 Else C2 => True
| Def X == C1 In C2 => has_head_action C2
end.

Lemma has_head_action_dec : forall C, {has_head_action C} + {~has_head_action C}.
Proof.
induction C; simpl; auto.
Qed.

Definition HeadTo (c:Configuration) : has_head_action (fst c) -> Configuration.
Proof.
destruct c; induction c; intros.
+ inversion H.
+ inversion H.
+ destruct e.
  - apply (c, update s p0 (evaluate_on_state e s p)).
  - apply (c, s).
+ apply (if (Value_dec (s p) (s p0)) then (c1, s) else (c2, s)).
+ elim IHc2; intros.
  - apply (Def r == c1 In a,b).
  - auto.
Defined.

(*
Example HeadTo_Com : forall p e q C s HC, 
HeadTo (p # e --> q ; C, s) HC = (C, update s q (evaluate_on_state e s p)).
Proof.
intros.
simpl.
trivial.
Qed.

Example HeadTo_Sel : forall p q l C s HC, 
HeadTo (p --> q [l]; C, s) HC = (C, s).
Proof.
intros.
simpl.
trivial.
Qed.
*)

End Semantics_Definitions.

(** Notations for precongruence and reductions. *)

Notation "C1 ~<= C2" := (MC_Precongr C1 C2) (at level 50, left associativity).
Notation "C1 ~< C2" := (MC_Precongr_step C1 C2) (at level 50, left associativity).
Notation "c ---> c'" := (MCTo c c') (at level 50, left associativity).
Notation "c --->* c'" := (MCToStar c c') (at level 50, left associativity).
Notation "c $ H -H-> c'" := (HeadTo c H = c') (at level 50).

(** ** Semantic properties *)

Section Semantics_Props.

(** Head reductions are unique and correct. *)

Lemma HeadTo_wd : forall c H H', HeadTo c H = HeadTo c H'.
Proof.
destruct c; induction c; auto; intros.
+ inversion H.
+ inversion H.
+ induction e; simpl; auto.
+ generalize (IHc2 H H'); clear IHc1 IHc2.
  set (c := HeadTo (c2,s) H).
  set (c' := HeadTo (c2,s) H').
  intros.
  simpl in c, c'; simpl; fold c c'.
  assert (c = HeadTo (c2,s) H); auto; clearbody c.
  assert (c' = HeadTo (c2,s) H'); auto; clearbody c'.
  induction c; induction c'; inversion H0; auto.
Qed.

Lemma HeadTo_Soundness : forall c Hc, c ---> (HeadTo c Hc).
Proof.
destruct c; induction c; intros.
+ inversion Hc.
+ inversion Hc.
+ induction e.
  - apply C_Com.
  - apply C_Sel.
+ simpl; case_eq (Value_dec (s p) (s p0)); intros.
  - apply C_Then; apply Vdec.eqb_eq; auto.
  - apply C_Else; apply Vdec.eqb_neq; auto.
+ generalize (IHc2 Hc).
  set (c := HeadTo (c2,s) Hc); intros.
  assert (c = HeadTo (c2,s) Hc); auto.
  simpl in H0; simpl; rewrite <- H0.
  change (c = HeadTo (c2,s) Hc) in H0; auto.
  clearbody c; induction c.
  apply C_Ctx; auto.
Qed.

(** Head reductions under recursive definitions. *)

Lemma HeadTo_Def_forward : forall C C' s s' H, (C,s)$H -H-> (C',s') ->
  forall X CX, (Def X == CX In C,s)$H -H-> (Def X == CX In C',s').
Proof.
intros.
simpl; simpl in H0; rewrite H0; simpl; auto.
Qed.

Lemma HeadTo_Def : forall C C' s s' H, (C,s)$H -H-> (C',s')
  -> forall X CX H', (Def X == CX In C,s)$H' -H-> (Def X == CX In C',s').
Proof.
intros; apply HeadTo_Def_forward.
rewrite <- H0; apply HeadTo_wd.
Qed.

Lemma HeadTo_Def_inv : forall X CX C C' s s' H, (Def X == CX In C,s)$H -H-> (C',s') ->
  exists C'', C' = Def X == CX In C'' /\ (C,s)$H -H-> (C'',s').
Proof.
intros X CX C; revert X CX.
induction C; intros; try inversion H.
+ exists C; split; induction e; inversion H0; auto.
+ revert H0; simpl; case_eq (Value_dec (s p) (s p0)); intros;
  eexists; inversion H1; auto.
+ set (c := HeadTo (Def X == CX In C2,s) H).
  assert (c = HeadTo (Def X == CX In C2,s) H) as Hc; auto.
  clearbody c; induction c.
  rename a into C2'; rename b into s2'.
  generalize (eq_refl (HeadTo (Def X == CX In C2,s) H)); intros.
  rewrite <- Hc in H1 at 2; clear Hc.
  elim (IHC2 _ _ _ _ _ _ H1); intros.
  rename x into C''; inversion_clear H2.
  clear IHC1 IHC2.
  simpl in H0, H4; rewrite H4 in H0.
  inversion H0; clear H0.
  simpl in H1; rewrite H4 in H1.
  inversion H1; clear H1.
  exists (Def r == C1 In C''); split; auto.
  simpl; rewrite H4, H6; auto.
Qed.

Lemma eta_has_head_action : forall eta C, has_head_action (eta; C).
Proof.
red; auto.
Qed.

Lemma cond_has_head_action : forall p q C1 C2, has_head_action (If p == q Then C1 Else C2).
Proof.
red; auto.
Qed.

(** Properties of unfolding. *)

Lemma Unfolded_antisym : forall X CX CX' C1 C2,
  Unfolded X CX C1 C2 -> Unfolded X CX' C2 C1 -> C1 = C2.
Proof.
intros.
induction H; inversion H0; auto; try rewrite IHUnfolded; auto.
Qed.

Lemma Unfolded_pn_iff : forall X CX C C', Unfolded X CX C C' ->
  forall p, set_In p (pn C') <-> (set_In p (pn C) \/ set_In p (pn CX)).
Proof.
intros.
induction H; simpl; split; auto; intros; try inversion_clear IHUnfolded.
(* AGH *)
+ inversion_clear H; auto. elim H0.
+ elim (set_union_elim _ _ _ _ H0); intro.
  - left; apply set_union_intro1; auto.
  - elim H1; auto.
    left; apply set_union_intro2; auto.
+ inversion_clear H0.
  elim (set_union_elim _ _ _ _ H3); intro.
  - apply set_union_intro1; auto.
  - apply set_union_intro2; apply H2; auto.
  - apply set_union_intro2; apply H2; auto.
+ elim (set_union_elim _ _ _ _ H0); intro.
  elim (set_union_elim _ _ _ _ H3); intro.
  - left; do 2 apply set_union_intro1; auto.
  - elim H1; auto.
    left; apply set_union_intro1; apply set_union_intro2; auto.
  - left; apply set_union_intro2; auto.
+ inversion_clear H0.
  elim (set_union_elim _ _ _ _ H3); intro.
  elim (set_union_elim _ _ _ _ H0); intro.
  - do 2 apply set_union_intro1; auto.
  - apply set_union_intro1; apply set_union_intro2; apply H2; auto.
  - apply set_union_intro2; auto.
  - apply set_union_intro1; apply set_union_intro2; apply H2; auto.
+ elim (set_union_elim _ _ _ _ H0); intro.
  - left; apply set_union_intro1; auto.
  - elim H1; auto.
    left; apply set_union_intro2; auto.
+ inversion_clear H0.
  elim (set_union_elim _ _ _ _ H3); intro.
  - apply set_union_intro1; auto.
  - apply set_union_intro2; apply H2; auto.
  - apply set_union_intro2; apply H2; auto.
+ elim (set_union_elim _ _ _ _ H1); intro.
  - left; apply set_union_intro1; auto.
  - elim H2; auto.
    left; apply set_union_intro2; auto.
+ inversion_clear H1.
  elim (set_union_elim _ _ _ _ H4); intro.
  - apply set_union_intro1; auto.
  - apply set_union_intro2; apply H3; auto.
  - apply set_union_intro2; apply H3; auto.
Qed.

Lemma Unfolded_pn : forall X CX C1 C2, Unfolded X CX C1 C2 -> 
  forall p, set_In p (pn C2) -> set_In p (pn CX) \/ set_In p (pn C1).
Proof.
intros.
elim (Unfolded_pn_iff _ _ _ _ H p); intros.
elim H1; auto.
Qed.

Lemma Unfolded_wf_ctx : forall X CX C C' l lX l',
  (forall Y, List.In Y l -> List.In Y l') -> (forall Y, List.In Y lX -> List.In Y l') ->
  WellFormed_ctx CX lX -> WellFormed_ctx C l -> Unfolded X CX C C' -> WellFormed_ctx C' l'.
Proof.
intros.
revert dependent l'; revert dependent l.
induction H3; simpl; intros.
+ apply WellFormed_ctx_mon with lX; auto.
+ induction eta; inversion_clear H2; eauto.
+ destroy_as H2 H'; repeat split; eauto.
  apply WellFormed_ctx_mon with l; auto.
+ destroy_as H2 H'; repeat split; eauto.
  apply WellFormed_ctx_mon with l; auto.
+ destroy_as H2 H'; repeat split; auto.
  - apply WellFormed_ctx_mon with (Y::l); auto.
    intros Z HZ; inversion_clear HZ; simpl; auto.
  - apply IHUnfolded with (Y::l); simpl; auto.
    intros Z HZ; inversion_clear HZ; simpl; auto.
Qed.

Lemma Unfolded_guarded : forall X CX C C', Unfolded X CX C C' ->
  guarded C -> guarded CX -> guarded C'.
Proof.
intros.
induction H; simpl; auto.
inversion_clear H0.
split; auto.
Qed.

(** Additional properties of precongruence. *)

Lemma MCP_step_to : forall C C', C ~< C' -> C ~<= C'.
Proof.
intros; apply MCP_Step with C'; auto; constructor.
Qed.

Lemma MCP_Trans : forall C1 C2 C3, C1 ~<= C2 -> C2 ~<= C3 -> C1 ~<= C3.
Proof.
intros; induction H; auto.
apply MCP_Step with C2; auto.
Qed.

Lemma CtxEta': forall eta C1 C2, C1 ~<= C2 -> (eta; C1) ~<= (eta; C2).
Proof.
intros.
induction H; try constructor.
apply MCP_Step with (eta; C2); auto.
apply CtxEta; auto.
Qed.

Lemma CtxThen': forall p q C' C'' C, C' ~<= C'' -> (If p == q Then C' Else C) ~<= (If p == q Then C'' Else C).
Proof.
intros.
induction H; try constructor.
apply MCP_Step with (If p == q Then C2 Else C); auto.
apply CtxThen; auto.
Qed.

Lemma CtxElse': forall p q C C' C'', C' ~<= C'' -> (If p == q Then C Else C') ~<= (If p == q Then C Else C'').
Proof.
intros.
induction H; try constructor.
apply MCP_Step with (If p == q Then C Else C2); auto.
apply CtxElse; auto.
Qed.

Lemma CtxCond': forall p q C1 C2 C3 C4, C1 ~<= C2 -> C3 ~<= C4 -> (If p == q Then C1 Else C3) ~<= (If p == q Then C2 Else C4).
Proof.
intros.
apply MCP_Trans with (If p == q Then C1 Else C4); [apply CtxElse' | apply CtxThen']; auto.
Qed.

Lemma CtxRec': forall X C1 C2 C2', C2 ~<= C2' -> (Def X == C1 In C2) ~<= (Def X == C1 In C2').
Proof.
intros.
induction H; try constructor.
apply MCP_Step with (Def X == C1 In C2); auto; apply CtxRec; auto.
Qed.

Lemma MCToStar_trans : forall c1 c2 c3, c1 --->* c2 -> c2 --->* c3 -> c1 --->* c3.
Proof.
intros; induction H; auto.
apply MCT_Step with c2; auto.
Qed.

Lemma End_MCP' : forall C C', C' ~<= C -> C' = End -> C = End.
Proof.
intros.
induction H; auto.
apply IHMC_Precongr; clear C3 H1 IHMC_Precongr.
induction H; auto; try inversion H0.
Qed.

Lemma End_MCP : forall C, End ~<= C -> C = End.
Proof.
intros; apply End_MCP' with End; auto.
Qed.

Lemma Call_MCP' : forall C C' X, C' ~<= C -> C' = Call X -> C = Call X.
Proof.
intros.
induction H; auto.
apply IHMC_Precongr; clear C3 H1 IHMC_Precongr.
induction H; auto; try inversion H0.
Qed.

Lemma Call_MCP : forall X C, Call X ~<= C -> C = Call X.
Proof.
intros; apply Call_MCP' with (Call X); auto.
Qed.

Lemma MCP_Call' : forall C C' X, C' ~<= C -> C = Call X -> C' = Call X.
Proof.
intros.
induction H; auto.
apply IHMC_Precongr in H0; clear C3 H1 IHMC_Precongr.
induction H; auto; try inversion H0.
Qed.

Lemma MCP_Call : forall X C, C ~<= Call X -> C = Call X.
Proof.
intros; apply MCP_Call' with (Call X); auto.
Qed.

Lemma MCP_eta' : forall eta C C', C' = (eta; End) -> C' ~<= C -> C = eta; End.
Proof.
intros.
induction H0; auto.
apply IHMC_Precongr; clear IHMC_Precongr H1 C3.
induction H0; auto; try inversion H.
rewrite H3 in H0; rewrite (End_MCP _ (MCP_step_to _ _ H0)); auto.
Qed.

Lemma MCP_eta : forall eta C, (eta; End) ~<= C -> C = eta; End.
Proof.
intros.
apply MCP_eta' with (eta;End); auto.
Qed.

Lemma eta_MCP_step_inv : forall eta C1 C2, (eta;C1) ~< (eta;C2) -> C1 ~< C2.
Proof.
intros; inversion H; auto; apply PB_Refl.
Qed.

Lemma Then_MCP_step_inv : forall p q C1 C2 C,
  (If p == q Then C1 Else C) ~< (If p == q Then C2 Else C) -> C1 ~< C2.
Proof.
intros; inversion H; auto; apply PB_Refl.
Qed.

Lemma Else_MCP_step_inv : forall p q C1 C2 C,
  (If p == q Then C Else C1) ~< (If p == q Then C Else C2) -> C1 ~< C2.
Proof.
intros; inversion H; auto; apply PB_Refl.
Qed.

Lemma Def_MCP_step_inv : forall X Y CX CY C1 C2,
  Unfolded X CX C1 C2 -> Unfolded Y CY C2 C1 ->
  forall Z CZ, X <> Z -> Y <> Z -> (Def Z == CZ In C1) ~< (Def Z == CZ In C2) -> C1 ~< C2.
Proof.
intros.
induction H; inversion H0.
+ rewrite <- H in H3; inversion H3; auto; try apply PB_Refl.
  inversion H6; elim H1; auto.
+ clear eta0 C0 C3 H4 H6 H7; inversion H3; auto; try apply PB_Refl.
  apply CtxEta; apply IHUnfolded; auto.
  inversion H6; apply Unfold; auto.
+ inversion H3; auto; try apply PB_Refl.
  apply CtxThen; apply IHUnfolded; auto.
  inversion H11; try apply PB_Refl; apply Unfold; auto.
+ inversion H3; auto; try apply PB_Refl.
+ inversion H3; auto; try apply PB_Refl.
+ inversion H3; auto; try apply PB_Refl.
  apply CtxElse; apply IHUnfolded; auto.
  inversion H11; try apply PB_Refl; apply Unfold; auto.
+ rename Y0 into W; rename CY0 into CW.
  clear Y1 CY1 C0 C3 H9 H8 H6 H5.
  inversion H3; auto; try apply PB_Refl.
  apply CtxRec; apply IHUnfolded; auto.
  inversion H6; apply Unfold; auto.
Qed.

Ltac l := apply set_union_intro1; auto; fail.
Ltac r := apply set_union_intro2; auto; fail.
Ltac ll := apply set_union_intro1, set_union_intro1; auto; fail.
Ltac lr := apply set_union_intro1, set_union_intro2; auto; fail.
Ltac rl := apply set_union_intro2, set_union_intro1; auto; fail.
Ltac rr := apply set_union_intro2, set_union_intro2; auto; fail.
Ltac lll := apply set_union_intro1, set_union_intro1, set_union_intro1; auto; fail.
Ltac llr := apply set_union_intro1, set_union_intro1, set_union_intro2; auto; fail.
Ltac lrl := apply set_union_intro1, set_union_intro2, set_union_intro1; auto; fail.
Ltac lrr := apply set_union_intro1, set_union_intro2, set_union_intro2; auto; fail.
Ltac rll := apply set_union_intro2, set_union_intro1, set_union_intro1; auto; fail.
Ltac rlr := apply set_union_intro2, set_union_intro1, set_union_intro2; auto; fail.
Ltac rrl := apply set_union_intro2, set_union_intro2, set_union_intro1; auto; fail.
Ltac rrr := apply set_union_intro2, set_union_intro2, set_union_intro2; auto; fail.

Ltac kill_it H := repeat (elim (set_union_elim _ _ _ _ H); clear H; intros);
     try l; try r; try ll; try lr; try rl; try rr;
     try lll; try llr; try lrl; try lrr; try rll; try rlr; try rrl; try rrr.

(** Precongruence preserves process names. *)
Lemma MCP_step_pn : forall C C', C ~< C' ->
  forall p, set_In p (pn C') -> set_In p (pn C).
Proof.
intros; induction H; simpl in H0; simpl; auto; (kill_it H0; try kill_it H).
+ apply set_union_intro1, set_union_intro2, set_union_intro1, set_union_intro2; auto.
+ elim (Unfolded_pn _ _ _ _ H p H0); intro; [l | r].
+ inversion H0.
Qed.

Lemma MCP_pn : forall C C', C ~<= C' ->
  forall p, set_In p (pn C') -> set_In p (pn C).
Proof.
intros; induction H; auto.
apply MCP_step_pn with C2; auto.
Qed.

(** Precongruence vs well-formedness. *)

Lemma MCP_step_guarded : forall C C', C ~< C' ->
  guarded C -> forall l, WellFormed_ctx C l -> guarded C'.
Proof.
intros C C' H; induction H; simpl; intros; auto.
- split. 2: apply H. induction eta; apply H0.
- inversion_clear H0; split; eauto; apply H2.
- destroy_as H2 H'; auto.
- inversion_clear H0; split; eauto; eapply Unfolded_guarded; eauto.
- inversion_clear H0; split; eauto; eapply IHMC_Precongr_step; eauto; apply H1.
Qed.

Lemma MCP_step_wf_ctx : forall C C' l, WellFormed_ctx C l -> C ~< C' -> WellFormed_ctx C' l.
Proof.
intros.
revert l H; induction H0; intros; auto.
+ induction eta1; induction eta2; destroy_as H0 H'; repeat split; auto.
+ induction eta; destroy_as H1 H'; repeat split; auto.
+ induction eta; destroy_as H1 H'; destroy_as H3 H''; repeat split; auto.
+ destroy_as H0 H'; destroy_as H2 H''; repeat split; auto.
+ simpl. simpl in H. induction eta; repeat split; apply H.
+ simpl. simpl in H. induction eta; repeat split; apply H.
+ simpl. simpl in H. repeat split; apply H.
+ simpl. simpl in H. repeat split; apply H.
+ destroy_as H2 H'; repeat split; auto.
  - apply WellFormed_ctx_simpl with X; auto.
    eapply WellFormed_ctx_mon; eauto.
    intros.
    inversion_clear H7; try rewrite H8; [right; left | idtac]; auto.
    inversion_clear H8; try rewrite H9; [left | right; right]; auto.
  - eapply WellFormed_ctx_mon; eauto.
    intros.
    inversion_clear H7; try rewrite H8; [left | right; right]; auto.
  - eapply WellFormed_ctx_mon; eauto.
    intros.
    inversion_clear H7; try rewrite H8; [right; left | idtac]; auto.
    inversion_clear H8; try rewrite H7; [left | right; right]; auto.
+ destroy_as H0 H'; repeat split; auto.
  apply (Unfolded_wf_ctx X CX C1 C2 (X::l) (X::l) (X::l)); auto.
+ simpl; auto.
+ induction eta; destroy_as H H'; split; auto.
+ destroy_as H H'; split; auto.
+ destroy_as H H'; split; auto.
+ destroy_as H H'; repeat split; eauto.
Qed.

Lemma MCP_wf_ctx : forall C C' l, WellFormed_ctx C l -> C ~<= C' -> WellFormed_ctx C' l.
Proof.
intros.
induction H0; auto.
apply IHMC_Precongr; clear IHMC_Precongr C3 H1.
apply MCP_step_wf_ctx with C1; auto.
Qed.

Lemma MCP_wf : forall C C', WellFormed C -> C ~<= C' -> WellFormed C'.
Proof.
intros.
apply MCP_wf_ctx with C; auto.
Qed.

(** Auxiliary result about unfolding - requires previous results on precongruence. *)

Lemma Unfolded_mixed : forall X Y CX CY C1 C2,
  Unfolded X CX C1 C2 -> Unfolded Y CY C2 C1 ->
  C1 = C2 \/ (CX = Call Y /\ CY = Call X /\ ~C1 ~< C2 /\ ~C2 ~< C1).
Proof.
intros; case_eq (RecVar_dec X Y); intro.
+ left; rewrite Rdec.eqb_eq in H1; rewrite <- H1 in H0.
  apply Unfolded_antisym with X CX CY; auto.
+ induction H; inversion H0; auto.
  - right; repeat split; auto;
    intro H'; pose (Call_MCP _ _ (MCP_step_to _ _ H')) as H'';
    inversion H''; rewrite Rdec.eqb_neq in H1; elim H1; auto.
  - elim IHUnfolded; auto; intro H'; [left; rewrite H' | right; destroy H']; repeat split; auto.
    * intro H''; contradiction H8; apply eta_MCP_step_inv with eta; auto.
    * intro H''; contradiction H'; apply eta_MCP_step_inv with eta; auto.
  - elim IHUnfolded; auto; intro H'; [left; rewrite H' | right; destroy H']; repeat split; auto.
    * intro H''; contradiction H10; apply Then_MCP_step_inv with p q C'; auto.
    * intro H''; contradiction H'; apply Then_MCP_step_inv with p q C'; auto.
  - elim IHUnfolded; auto; intro H'; [left; rewrite H' | right; destroy H']; repeat split; auto.
    * intro H''; contradiction H10; apply Else_MCP_step_inv with p q C'; auto.
    * intro H''; contradiction H'; apply Else_MCP_step_inv with p q C'; auto.
  - elim IHUnfolded; auto; intro H'; [left; rewrite H' | right; destroy H']; repeat split;
    rename Y0 into Z; rename CY0 into CZ; auto.
    * intro H''; contradiction H11; apply Def_MCP_step_inv with X Y CX CY Z CZ; auto.
    * intro H''; contradiction H'; apply Def_MCP_step_inv with Y X CY CX Z CZ; auto.
Qed.

Lemma MCP_step_Unfold_ctx : forall X CX C1 C2, Unfolded X CX C1 C2 -> C2 ~< C1 ->
  forall l, WellFormed_ctx C1 l -> C1 = C2.
Proof.
intros.
revert l H1; induction H0; inversion H; auto; intros.
- rename X0 into Z; rename CX0 into CZ; clear Y H1 CY H2 C0 H4 C3 H5.
  elim (Unfolded_mixed _ _ _ _ _ _ H0 H6); intros.
  + rewrite H1; auto.
  + destroy_as H1 H'; destroy_as H7 H'.
    rewrite H2 in H9; inversion H9.
- rewrite IHMC_Precongr_step with l; induction eta; inversion H5; auto.
- rewrite IHMC_Precongr_step with l; destroy_as H7 H'; auto.
- rewrite IHMC_Precongr_step with l; destroy_as H7 H'; auto.
- rewrite IHMC_Precongr_step with (X0::l); destroy_as H7 H'; auto.
Qed.

Lemma MCP_step_Unfold : forall X CX C1 C2, Unfolded X CX C1 C2 -> C2 ~< C1 ->
  WellFormed C1 -> C1 = C2.
Proof.
intros; apply MCP_step_Unfold_ctx with X CX nil; auto.
Qed.

End Semantics_Props.

Section Applications.

(** We now can prove some more results by induction on canonical proofs
    of precongruence or reduction. *)

(** Properties of termination. *)

Lemma MCP_step_not_terminated : forall C C', ~terminated C -> C ~< C' -> ~terminated C'.
Proof.
intros; intro.
apply H.
apply MCP_Step with C'; auto.
Qed.

Lemma MCP_not_terminated : forall C C', ~terminated C -> C ~<= C' -> ~terminated C'.
Proof.
intros; intro.
apply H.
apply MCP_Trans with C'; auto.
Qed.

Lemma Unfolded_head_action : forall C, has_head_action C ->
  forall X CX C', Unfolded X CX C C' -> has_head_action C'.
Proof.
intros; induction H0; auto.
inversion H.
Qed.

Lemma MCP_step_head_action : forall C, has_head_action C ->
  forall C', C ~< C' -> has_head_action C'.
Proof.
intros; induction H0; auto.
simpl; simpl in H.
eapply Unfolded_head_action; eauto.
Qed.

Lemma MCP_head_action : forall C, has_head_action C ->
  forall C', C ~<= C' -> has_head_action C'.
Proof.
intros.
induction H0; auto.
apply IHMC_Precongr; eapply MCP_step_head_action; eauto.
Qed.

Lemma eta_not_terminated : forall eta C, ~terminated (eta; C).
Proof.
intros; intro.
apply MCP_head_action in H; simpl; auto.
Qed.

Lemma cond_not_terminated : forall p q C1 C2, ~terminated (If p == q Then C1 Else C2).
Proof.
intros; intro.
apply MCP_head_action in H; simpl; auto.
Qed.

Lemma terminated_Def : forall X C1 C2, terminated C2 -> terminated (Def X == C1 In C2).
Proof.
intros.
eapply MCP_Trans.
2: apply MCP_step_to; apply Garbage.
apply CtxRec'; auto.
Qed.

End Applications.

(** * Deadlock-freedom-by-design

  We now prove Theorem 1: every non-terminated choreography can reduce. *)

Section Progress.

(** We start with useful characterizations of being guarded and being a pure call. *)

Lemma guarded_char : forall C, guarded C -> C ~<= End \/ has_head_action C.
Proof.
induction C; intros; auto.
+ left; constructor.
+ inversion_clear H.
  elim IHC2; intros; auto.
  left; apply terminated_Def; auto.
Qed.

Lemma pure_call_char : forall C, ~terminated C -> ~has_head_action C -> pure_call C.
Proof.
induction C; simpl; auto; intros.
+ contradiction H; constructor.
+ apply IHC2; auto.
  intro; contradiction H.
  apply terminated_Def; auto.
Qed.

(** The idea of the proof is: if C is not terminated, then we can always apply
    a reduction rule, eventually by unfolding some procedure definition.
    To take care of this case, we need to be able to unfold a procedure call within the
    context of the choreography (relation Ctx_Unfolded below). *)

(** A specialization of the remove function from the standard library. *)

Fixpoint remove_Def (X:RecVar) (l:list (RecVar*Choreography)) : list (RecVar*Choreography) :=
match l with
| nil => nil
| (Y,CY) :: l' => if RecVar_dec X Y then remove_Def Y l' else (Y,CY) :: remove_Def X l'
end.

Definition add_or_replace (X:RecVar) (CX:Choreography) l := (X,CX) :: remove_Def X l.

Inductive Ctx_Unfolded : list (RecVar*Choreography) -> Choreography -> Choreography -> Prop :=
| Ctx_Unfold X CX l : List.In (X,CX) l -> Ctx_Unfolded l (Call X) CX
| Ctx_Eta eta C C' l : Ctx_Unfolded l C C' -> Ctx_Unfolded l (eta;C) (eta;C')
| Ctx_Then p q C C' CE l : Ctx_Unfolded l C C' -> Ctx_Unfolded l (If p == q Then C Else CE) (If p == q Then C' Else CE)
| Ctx_Else p q CT C C' l : Ctx_Unfolded l C C' -> Ctx_Unfolded l (If p == q Then CT Else C) (If p == q Then CT Else C')
| Ctx_Rec X CX C C' l : Ctx_Unfolded (add_or_replace X CX l) C C' -> Ctx_Unfolded l (Def X == CX In C) (Def X == CX In C')
.

(** Membership characterizations for these list functions. *)

Lemma remove_Def_not_in : forall X CX l, ~List.In (X,CX) (remove_Def X l).
Proof.
induction l; simpl; auto.
induction a.
case_eq (RecVar_dec X a); intros; intro; contradiction IHl.
- rewrite Rdec.eqb_eq in H; rewrite <- H in H0; auto.
- inversion_clear H0; auto.
  revert H; inversion H1; rewrite Rdec.eqb_refl.
  intro; inversion H.
Qed.

Lemma remove_Def_in : forall X Y CY l, X <> Y -> List.In (Y,CY) l -> List.In (Y,CY) (remove_Def X l).
Proof.
induction l; simpl; auto; intros.
induction a.
case_eq (RecVar_dec X a); intros.
- rewrite Rdec.eqb_eq in H1.
  rewrite <- H1; apply IHl; auto.
  inversion_clear H0; auto.
  contradiction H; inversion H2.
  transitivity a; auto.
- simpl; inversion_clear H0; auto.
Qed.

Lemma in_remove_Def : forall X Y CY l, List.In (Y,CY) (remove_Def X l) -> List.In (Y,CY) l.
Proof.
induction l; simpl; auto.
induction a.
case_eq (RecVar_dec X a); intros.
- right; apply IHl.
  rewrite Rdec.eqb_eq in H; rewrite <- H in H0; auto.
- inversion_clear H0; auto.
Qed.

Lemma remove_Def_neq : forall X Y CY l, List.In (Y,CY) (remove_Def X l) -> X <> Y.
Proof.
induction l; simpl; auto.
induction a.
case_eq (RecVar_dec X a); intros.
- apply IHl.
  rewrite Rdec.eqb_eq in H; rewrite <- H in H0; auto.
- inversion_clear H0; auto.
  rewrite Rdec.eqb_neq in H; revert H; inversion H1; auto.
Qed.

Lemma in_add_or_replace : forall l X CX Y CY,
  List.In (X,CX) (add_or_replace Y CY l) <-> (X = Y /\ CX = CY) \/ (X <> Y /\ List.In (X,CX) l).
Proof.
simpl; split; intros; inversion_clear H.
- inversion H0; auto.
- right; split.
  + intro; symmetry in H; revert H.
    eapply remove_Def_neq; eauto.
  + eapply in_remove_Def; eauto.
- inversion H0.
  rewrite H; rewrite H1; auto.
- inversion_clear H0; right; apply remove_Def_in; auto.
Qed.

(** Unlike regular unfolding, contextual unfolding is guaranteed to return something
    precongruent to the original choreography. *)

Lemma MCP_step_Ctx_Unfolded : forall C C', Ctx_Unfolded nil C C' -> C ~< C'.
Proof.
assert (forall C C' l, Ctx_Unfolded l C C' ->
  C ~< C' \/ exists X CX, List.In (X,CX) l /\ Unfolded X CX C C').
2: { intros.
     elim (H C C' nil); intros; auto.
     destroy_as H1 H'; inversion H2.
   }
induction C; intros; inversion H.
+ right.
  exists r, C'; split; auto; constructor.
+ clear l0 eta C0 H1 H0 H3; rename C'0 into C0.
  elim (IHC _ _ H4); intros.
  - left; constructor; auto.
  - right; destroy_as H0 H'.
    exists x, x0; split; try constructor; auto.
+ clear l0 p1 q C CE H1 H0 H3 H4 H5.
  elim (IHC1 _ _ H6); intros.
  - left; constructor; auto.
  - right; destroy_as H0 H'.
    exists x, x0; split; try constructor; auto.
+ clear l0 p1 q C CT H1 H0 H3 H4 H5.
  elim (IHC2 _ _ H6); intros.
  - left; constructor; auto.
  - right; destroy_as H0 H'.
    exists x, x0; split; try constructor; auto.
+ clear l0 X CX C H1 H0 H3 H4.
  elim (IHC2 _ _ H5); intros.
  - left; apply CtxRec; auto.
  - destroy_as H0 H'.
    elim (in_add_or_replace l x x0 r C1); intros.
    clear H4; elim H3; auto; clear H3 H1; intros.
    * left; constructor.
      inversion_clear H1.
      rewrite <- H3, <- H4; auto.
    * right; inversion_clear H1; exists x, x0; split; try constructor; auto.
Qed.

Lemma MCP_Ctx_Unfolded : forall C C', Ctx_Unfolded nil C C' -> C ~<= C'.
Proof.
intros.
apply MCP_step_to.
apply MCP_step_Ctx_Unfolded; auto.
Qed.

(** Furthermore, it is not a pure function call. *)

Lemma Ctx_Unfolded_guarded : forall C C' l,
  (forall X CX, List.In (X,CX) l -> guarded CX) ->
  Ctx_Unfolded l C C' -> WellFormed_ctx C (map fst l) -> guarded C'.
Proof.
induction C; intros; inversion H0; simpl; eauto.
clear C H6 CX H5 X H2 l0 H3.
rename C'0 into C0.
destroy_as H1 H'; split; auto.
apply IHC2 with (add_or_replace r C1 l); auto.
+ intros.
  inversion_clear H5.
  - inversion H6.
    rewrite <- H9; auto.
  - apply H with X.
    apply in_remove_Def with r; auto.
+ apply WellFormed_ctx_mon with (r:: map fst l); auto.
  simpl; intros.
  inversion_clear H5; auto.
  rewrite in_map_iff in H6.
  destroy H6; induction x.
  elim (R.eq_dec r X); auto.
  right; replace X with (fst (a,b)).
  apply in_map; apply remove_Def_in; auto.
  simpl in H5; rewrite H5; auto.
Qed.

Lemma Ctx_Unfolded_has_head : forall C C',
  Ctx_Unfolded nil C C' -> WellFormed C -> ~terminated C -> has_head_action C'.
Proof.
intros.
generalize (MCP_Ctx_Unfolded _ _ H); intro.
assert (forall (X:RecVar) CX, List.In (X,CX) nil -> guarded CX).
1: intros; inversion H3.
generalize (Ctx_Unfolded_guarded _ _ _ H3 H H0); intro.
assert (~terminated C').
1: intro; apply H1; apply MCP_Trans with C'; auto.
induction C'; auto.
1: inversion H; inversion H6.
inversion H.
1: inversion H6.
clear H11 C'; rename C'2 into C'.
rewrite H10 in H8; clear H10 CX; rename C'1 into CX.
rewrite H6 in H8; clear H6 X; rename r into X.
clear H7 l.
unfold add_or_replace in H9; simpl in H9.
inversion_clear H4.
elim (guarded_char _ H7); intros; auto.
contradiction H5.
apply terminated_Def; auto.
Qed.

Lemma pure_call_Ctx_Unfolded : forall C, pure_call C -> WellFormed C ->
  exists C', Ctx_Unfolded nil C C'.
Proof.
assert (forall C l, pure_call C -> WellFormed_ctx C (map fst l) -> exists C', Ctx_Unfolded l C C'); auto.
induction C; simpl; intros; try inversion H.
+ rewrite in_map_iff in H0; destroy_as H0 H'.
  induction x.
  exists b; constructor.
  simpl in H1; rewrite <- H1; auto.
+ destroy_as H0 H'.
  elim IHC2 with (add_or_replace r C1 l); auto.
  - intros; exists (Def r == C1 In x); constructor; auto.
  - apply WellFormed_ctx_mon with (r :: map fst l); auto.
    clear H0 H2 H1 H IHC1 IHC2 C2.
    simpl; intros.
    inversion_clear H; auto.
    elim (R.eq_dec r X); auto.
    rewrite in_map_iff in H0; destroy H0.
    induction x.
    rewrite <- H; right.
    apply in_map; apply remove_Def_in; auto.
Qed.

(** Now we can prove that any non-terminated choreography is precongruent
    to a choreography with head action, which has a head reduction. *)

Lemma not_terminated_has_head_action : forall C, ~terminated C ->
  WellFormed C -> exists C', has_head_action C' /\ C ~<= C'.
Proof.
intros.
elim (has_head_action_dec C); intro.
+ exists C; split; auto; constructor.
+ elim (pure_call_Ctx_Unfolded C); auto.
  2: apply pure_call_char; auto.
  intro C'; intros.
  exists C'; split; auto.
  - apply Ctx_Unfolded_has_head with C; auto.
  - apply MCP_Ctx_Unfolded; auto.
Qed.

Theorem progress : forall C s, ~(terminated C) -> WellFormed C -> exists c', (C,s) ---> c'.
Proof.
intros.
elim (not_terminated_has_head_action C); auto.
intros C' HC'; destroy HC'.
set (c := HeadTo (C',s) H1).
assert (c = HeadTo (C',s) H1); auto; clearbody c.
exists c; induction c.
rename a into C''; rename b into s'.
apply C_Struct with C' C''; auto.
+ constructor.
+ rewrite H2; apply HeadTo_Soundness.
Qed.

End Progress.

(** *  Weighted Relations *)

Section Weighted_Relations.

(** Many proofs in MC are by induction on the proof of precongruence/reduction.
    However, since these are dependent types, formalizing them directly requires using
    Coq.Program.Equality, which imports axioms.
    In order to do these proofs faithfully, we clone these types with a weight - the
    size of the derivation.

    For precongruence, we also get a canonical representation: any precongruence proof can be split into a sequence of unfoldings followed by reversible rewritings and a sequence of garbage collection steps. *)

Definition Precongruence := Choreography -> Choreography -> Prop.
Definition WeightedRelation (T:Type) := nat -> T -> T -> Prop.
Definition WeightedPrecongruence := WeightedRelation (Choreography).

Inductive Precongr_unfold : Precongruence :=
| MCP_Unfold X CX C1 C2 : Unfolded X CX C1 C2 -> Precongr_unfold (Def X == CX In C1) (Def X == CX In C2)
.

Inductive Precongr_sym : Precongruence :=
| MCP_EtaEta eta1 eta2 C : independent eta1 eta2 -> Precongr_sym (eta1; eta2; C) (eta2; eta1; C)
| MCP_EtaCond eta p q C1 C2 : unused p eta -> unused q eta -> Precongr_sym (eta; (If p == q Then C1 Else C2)) (If p == q Then (eta; C1) Else (eta; C2))
| MCP_CondEta eta p q C1 C2 : unused p eta -> unused q eta -> Precongr_sym (If p == q Then (eta; C1) Else (eta; C2)) (eta; (If p == q Then C1 Else C2))
| MCP_CondCond p q r s C1 C2 C3 C4 : disjoint p q r s -> Precongr_sym (If p == q Then (If r == s Then C1 Else C2) Else (If r == s Then C3 Else C4))
                                                              (If r == s Then (If p == q Then C1 Else C3) Else (If p == q Then C2 Else C4))
| MCP_EtaRec eta X CX C : Precongr_sym (eta; Def X == CX In C) (Def X == CX In (eta;C))
| MCP_RecEta eta X CX C : Precongr_sym (Def X == CX In (eta;C)) (eta; Def X == CX In C)
| MCP_CondRec p q X CX C1 C2 : Precongr_sym (If p == q Then Def X == CX In C1 Else Def X == CX In C2) (Def X == CX In If p == q Then C1 Else C2)
| MCP_RecCond p q X CX C1 C2 : Precongr_sym (Def X == CX In If p == q Then C1 Else C2) (If p == q Then Def X == CX In C1 Else Def X == CX In C2)
| MCP_RecRec X CX Y CY C : X <> Y -> ~Free X CY -> ~Free Y CX -> Precongr_sym (Def X == CX In (Def Y == CY In C)) (Def Y == CY In (Def X == CX In C))
.

Inductive Precongr_garbage : Precongruence :=
| MCP_Garbage X C : Precongr_garbage (Def X == C In End) End
.

Inductive CtxClose (R:Precongruence) : WeightedPrecongruence :=
| WCtxBase C C' : R C C' -> CtxClose R 0 C C'
| WCtxEta n eta C1 C2 : CtxClose R n C1 C2 -> CtxClose R (S n) (eta; C1) (eta; C2)
| WCtxThen n p q C' C'' C : CtxClose R n C' C'' -> CtxClose R (S n) (If p == q Then C' Else C) (If p == q Then C'' Else C)
| WCtxElse n p q C C' C'' : CtxClose R n C' C'' -> CtxClose R (S n) (If p == q Then C Else C') (If p == q Then C Else C'')
| WCtxRec n X C1 C2 C2' : CtxClose R n C2 C2' -> CtxClose R (S n) (Def X == C1 In C2) (Def X == C1 In C2')
.

Inductive TransClose {T} (R:WeightedRelation T) : WeightedRelation T :=
| TBase C : TransClose R 0 C C
| TStep {n k C} C' {C''} : R n C C' -> TransClose R k C' C'' -> TransClose R (S (n+k)) C C''
.

(** The transitive closure of R is actually transitive. *)

Lemma TTrans : forall {T} (R:WeightedRelation T) n1 n2 C C' C'',
  TransClose R n1 C C' -> TransClose R n2 C' C'' -> TransClose R (n1+n2) C C''.
Proof.
do 2 intro.
assert (forall n1 k n2 C C' C'', k<n1 -> TransClose R k C C' -> TransClose R n2 C' C'' -> TransClose R (k+n2) C C''); eauto.
induction n1; intros; simpl; [inversion H | inversion H0]; auto.
+ clear C''0 H6 C0 H5 H0.
  rewrite <- H4 in H; clear k H4; apply lt_S_n in H.
  assert (k0 < n1). apply le_lt_trans with (n+k0); auto with arith.
  replace (S (n+k0)+n2) with ((S n) + (k0+n2)). 2: ring.
  apply TStep with C'0; eauto.
Qed.

Lemma MCP_step_CtxClose : forall (R:Precongruence), (forall C C', R C C' -> C ~< C') ->
  forall n C C', CtxClose R n C C' -> C ~< C'.
Proof.
induction n; intros.
+ inversion H0; auto.
+ inversion H0; try (constructor; auto; fail).
Qed.

Lemma MCP_CtxClose : forall (R:Precongruence), (forall C C', R C C' -> C ~<= C') ->
  forall n C C', CtxClose R n C C' -> C ~<= C'.
Proof.
induction n; intros; inversion H0; auto.
+ apply CtxEta'; auto.
+ apply CtxThen'; auto.
+ apply CtxElse'; auto.
+ apply CtxRec'; auto.
Qed.

Lemma MCP_step_TransClose : forall (R:WeightedPrecongruence), (forall n C C', R n C C' -> C ~< C') ->
  forall n C C', TransClose R n C C' -> C ~<= C'.
Proof.
intros R HR.
assert (forall n k C C', k<n -> TransClose R k C C' -> C ~<= C'); eauto.
induction n; intros; try (inversion H; fail); inversion H0.
+ constructor.
+ rewrite <- H3 in H; apply lt_S_n in H.
  apply MCP_Trans with C'0.
  - apply MCP_step_to; eauto.
  - apply IHn with k0; auto.
    apply le_lt_trans with (n0+k0); auto with arith.
Qed.

Lemma MCP_TransClose : forall (R:WeightedPrecongruence), (forall n C C', R n C C' -> C ~<= C') ->
  forall n C C', TransClose R n C C' -> C ~<= C'.
Proof.
intros R HR.
assert (forall n k C C', k<n -> TransClose R k C C' -> C ~<= C'); eauto.
induction n; intros; try (inversion H; fail); inversion H0.
+ constructor.
+ rewrite <- H3 in H; apply lt_S_n in H.
  apply MCP_Trans with C'0; eauto.
  apply IHn with k0; auto.
  apply le_lt_trans with (n0+k0); auto with arith.
Qed.

Definition UPrecongr_step := CtxClose Precongr_unfold.
Definition SPrecongr_step := CtxClose Precongr_sym.
Definition GPrecongr_step := CtxClose Precongr_garbage.

Definition UPrecongr := TransClose UPrecongr_step.
Definition SPrecongr := TransClose SPrecongr_step.
Definition GPrecongr := TransClose GPrecongr_step.

Inductive MC_Precongr_weighted : Choreography -> Choreography -> Prop :=
| PWIntro n1 n2 n3 C1 C2 C3 C4 : UPrecongr n1 C1 C2 -> SPrecongr n2 C2 C3 -> GPrecongr n3 C3 C4 -> MC_Precongr_weighted C1 C4.

End Weighted_Relations.

(** Pretty-printing. *)

Notation "C $ n ~<u C'" := (UPrecongr_step n C C') (at level 50).
Notation "C $ n ~<>~ C'" := (SPrecongr_step n C C') (at level 50).
Notation "C $ n g>~ C'" := (GPrecongr_step n C C') (at level 50).
Notation "C $ n ~<=u C'" := (UPrecongr n C C') (at level 50).
Notation "C $ n ~<=>~ C'" := (SPrecongr n C C') (at level 50).
Notation "C $ n g>=~ C'" := (GPrecongr n C C') (at level 50).
Notation "C ~<=n C'" := (MC_Precongr_weighted C C') (at level 50).

(** We first show that these relations precisely correspond to the unweighted ones. *)

Section Weighted_Reductions.

(** ** Soundness
       Weighted relations imply non-weighted ones. *)

Lemma Precongr_unfold_to_step : forall C1 C2, Precongr_unfold C1 C2 -> C1 ~< C2.
Proof.
intros. inversion H; constructor; auto.
Qed.

Lemma Precongr_sym_to_step : forall C1 C2, Precongr_sym C1 C2 -> C1 ~< C2.
Proof.
intros. inversion H; constructor; auto.
Qed.

Lemma Precongr_garbage_to_step : forall C1 C2, Precongr_garbage C1 C2 -> C1 ~< C2.
Proof.
intros. inversion H; constructor; auto.
Qed.

Lemma MCP_to_weighted : forall C C', C ~<=n C' -> C ~<= C'.
Proof.
intros.
inversion H.
apply MCP_Trans with C2; [idtac | apply MCP_Trans with C3];
  eapply MCP_step_TransClose; eauto;
  eapply MCP_step_CtxClose; eauto.
+ exact Precongr_unfold_to_step.
+ exact Precongr_sym_to_step.
+ exact Precongr_garbage_to_step.
Qed.

(** ** Compatibility
       The transitive closure of a contextual closure is also contextually closed. *)

Lemma TCtxEta : forall {R n} eta {C C'}, CtxClose R n C C' -> TransClose (CtxClose R) (S (S n)) (eta;C) (eta;C').
Proof.
intros.
replace (S n) with ((S n)+0); auto.
eapply TStep; eauto; constructor; auto.
Qed.

Lemma TCtxThen : forall {R n} p q CT {C C'}, CtxClose R n C C' ->
  TransClose (CtxClose R) (S (S n)) (If p == q Then CT Else C) (If p == q Then CT Else C').
Proof.
intros.
replace (S n) with ((S n)+0); auto.
eapply TStep; eauto; constructor; auto.
Qed.

Lemma TCtxElse : forall {R n} p q {C C'} CE, CtxClose R n C C' ->
  TransClose (CtxClose R) (S (S n)) (If p == q Then C Else CE) (If p == q Then C' Else CE).
Proof.
intros.
replace (S n) with ((S n)+0); auto.
eapply TStep; eauto; constructor; auto.
Qed.

Lemma TCtxRec : forall {R n} X CX {C C'}, CtxClose R n C C' ->
  TransClose (CtxClose R) (S (S n)) (Def X == CX In C) (Def X == CX In C').
Proof.
intros.
replace (S n) with ((S n)+0); auto.
eapply TStep; eauto; constructor; auto.
Qed.

Lemma TCtxEta' : forall {R n} eta {C C'}, TransClose (CtxClose R) n C C' -> 
  exists n', TransClose (CtxClose R) n' (eta;C) (eta;C').
Proof.
intros.
assert (forall n k C C', k<n -> TransClose (CtxClose R) k C C' -> exists n', TransClose (CtxClose R) n' (eta;C) (eta;C')); eauto.
clear n C C' H. induction n; intros; [inversion H | inversion H0].
+ exists 0; constructor.
+ rewrite <- H3 in H; apply lt_S_n in H; clear k H3 H0.
  assert (k0 < n). apply le_lt_trans with (n0+k0); auto with arith.
  elim (IHn _ _ _ H0 H2); intros n' Hn'.
  exists (S (S n0) + n'); econstructor; eauto.
  constructor; auto.
Qed.

Lemma TCtxThen' : forall {R n} p q CT {C C'}, TransClose (CtxClose R) n C C' ->
  exists n', TransClose (CtxClose R) n' (If p == q Then CT Else C) (If p == q Then CT Else C').
Proof.
intros.
assert (forall n k C C', k<n -> TransClose (CtxClose R) k C C' -> exists n', TransClose (CtxClose R) n' (If p == q Then CT Else C) (If p == q Then CT Else C')); eauto.
clear n C C' H. induction n; intros; [inversion H | inversion H0].
+ exists 0; constructor.
+ rewrite <- H3 in H; apply lt_S_n in H; clear k H3 H0.
  assert (k0 < n). apply le_lt_trans with (n0+k0); auto with arith.
  elim (IHn _ _ _ H0 H2); intros n' Hn'.
  exists (S (S n0) + n'); econstructor; eauto.
  constructor; auto.
Qed.

Lemma TCtxElse' : forall {R n} p q {C C'} CE, TransClose (CtxClose R) n C C' ->
  exists n', TransClose (CtxClose R) n' (If p == q Then C Else CE) (If p == q Then C' Else CE).
Proof.
intros.
assert (forall n k C C', k<n -> TransClose (CtxClose R) k C C' -> exists n', TransClose (CtxClose R) n' (If p == q Then C Else CE) (If p == q Then C' Else CE)); eauto.
clear n C C' H. induction n; intros; [inversion H | inversion H0].
+ exists 0; constructor.
+ rewrite <- H3 in H; apply lt_S_n in H; clear k H3 H0.
  assert (k0 < n). apply le_lt_trans with (n0+k0); auto with arith.
  elim (IHn _ _ _ H0 H2); intros n' Hn'.
  exists (S (S n0) + n'); econstructor; eauto.
  constructor; auto.
Qed.

Lemma TCtxRec' : forall {R n} X CX {C C'}, TransClose (CtxClose R) n C C' ->
  exists n', TransClose (CtxClose R) n' (Def X == CX In C) (Def X == CX In C').
Proof.
intros.
assert (forall n k C C', k<n -> TransClose (CtxClose R) k C C' -> exists n', TransClose (CtxClose R) n' (Def X == CX In C) (Def X == CX In C')); eauto.
clear n C C' H. induction n; intros; [inversion H | inversion H0].
+ exists 0; constructor.
+ rewrite <- H3 in H; apply lt_S_n in H; clear k H3 H0.
  assert (k0 < n). apply le_lt_trans with (n0+k0); auto with arith.
  elim (IHn _ _ _ H0 H2); intros n' Hn'.
  exists (S (S n0) + n'); econstructor; eauto.
  constructor; auto.
Qed.

(** ** Completeness
       Non-weighted relations can be made weighted. *)

(** Base case *)

Lemma MCP_step_to_weighted_str : forall C C', C ~< C' ->
  C=C' \/ (exists n, C$n ~<u C') \/ (exists n, C$n ~<>~ C') \/ (exists n, C$n g>~ C').
Proof.
intros; induction H;
  auto;
  try (right; left; exists 0; constructor; constructor; auto; fail);
  try (right; right; left; exists 0; constructor; constructor; auto; fail);
  try (right; right; right; exists 0; constructor; constructor; auto; fail);
  (elim IHMC_Precongr_step; intro H';
    [ rewrite H'; auto|
      elim H'; clear H'; intro H'; [right; left |
      elim H'; clear H'; intro H'; [right; right; left | right; right; right]]]);
  elim H'; clear H'; intros n Hn;
  exists (S n); constructor; auto.
Qed.

Section Transitivity.

Variable R R':WeightedPrecongruence.
Hypothesis RR'_comm : (forall n1 n2 C C' C'', R n1 C C' -> R' n2 C' C'' -> exists C0, R' n2 C C0 /\ R n1 C0 C'').

Lemma TransClose_comm' : forall n1 n2 C C' C'', TransClose R n1 C C' -> R' n2 C' C'' ->
  exists C0, R' n2 C C0 /\ TransClose R n1 C0 C''.
Proof.
set (RT := TransClose R).
assert (forall n1 k n2 C C' C'', k<n1 -> RT k C C' -> R' n2 C' C'' -> exists C0, R' n2 C C0 /\ RT k C0 C''); eauto.
induction n1; intros; [inversion H | inversion H0].
+ exists C''; split; auto; constructor.
+ clear C''0 H6 H5 H0.
  rewrite <- H4 in H; clear k H4; apply lt_S_n in H.
  assert (k0 < n1). apply le_lt_trans with (n + k0); auto with arith.
  elim (IHn1 _ _ _ _ _ H0 H3 H1); intros.
  destroy_as H4 H'.
  clear H H3 C' H1 H0.
  elim (RR'_comm _ _ _ _ _ H2 H5); intros.
  destroy_as H H'.
  rename x into C1; rename x0 into C3.
  exists C3; split; auto.
  change (RT (S n + k0) C3 C''). apply TTrans with C1; auto.
  replace (S n) with (S n + 0); auto with arith.
  apply TStep with C1; auto. constructor.
Qed.

Lemma TransClose_comm : forall n1 n2 C C' C'', TransClose R n1 C C' -> TransClose R' n2 C' C'' ->
  exists C0, TransClose R' n2 C C0 /\ TransClose R n1 C0 C''.
Proof.
set (RT := TransClose R); set (RT' := TransClose R').
assert (forall n2 k n1 C C' C'', k<n2 -> RT n1 C C' -> RT' k C' C'' -> exists C0, RT' k C C0 /\ RT n1 C0 C''); eauto.
induction n2; intros; [inversion H | inversion H1]; intros.
+ rewrite <- H4; exists C; split; auto; constructor.
+ clear C''0 H6 C0 H5 H1.
  rewrite <- H4 in H; clear k H4; apply lt_S_n in H.
  assert (k0 < n2). apply le_lt_trans with (n+k0); auto with arith.
  fold UPrecongr in H3.
  elim (TransClose_comm' _ _ _ _ _ H0 H2); intros.
  destroy_as H4 H'.
  clear H0 H2. rename x into C0.
  elim (IHn2 _ _ _ _ _ H1 H4 H3); intros.
  destroy_as H0 H'.
  clear H1 H4 H3. rename x into C1.
  exists C1; split; auto.
  apply TStep with C0; auto.
Qed.

End Transitivity.

(** Unfolding can be pushed before garbage collection. *)

Lemma Precongr_garbage_Unfolded_comm : forall n X CX C C' C'', C$n g>~ C' -> Unfolded X CX C' C'' ->
  exists C0, Unfolded X CX C C0 /\ C0$n g>~ C''.
Proof.
induction n; intros.
+ revert H0. inversion H. inversion H0.
  intro. inversion H5.
+ revert H0. inversion H; intro; inversion H4.
  - elim (IHn _ _ _ _ _ H1 H8); intros.
    inversion_clear H9. rename x into C4.
    exists (eta;C4); split; constructor; auto.
  - elim (IHn _ _ _ _ _ H1 H10); intros.
    inversion_clear H11. rename x into C4.
    exists (If p == q Then C4 Else C0); split; constructor; auto.
  - exists (If p == q Then C'0 Else C2); split; constructor; auto.
  - exists (If p == q Then C2 Else C'0); split; constructor; auto.
  - elim (IHn _ _ _ _ _ H1 H10); intros.
    inversion_clear H11. rename x into C4.
    exists (If p == q Then C0 Else C4); split; constructor; auto.
  - elim (IHn _ _ _ _ _ H1 H10); intros.
    inversion_clear H11. rename x into C4.
    exists (Def X0 == C1 In C4); split; constructor; auto.
Qed.

(* OBSOLETE - BUT TRUE :-)
Lemma Precongr_garbage_Unfolded_comm' : forall n X CX CX' C C', CX$n g>~ CX' -> Unfolded X CX' C C' ->
  exists n' C0, Unfolded X CX C C0 /\ C0$n' g>~ C'.
Proof.
intros. revert n X CX CX' C' H H0.
induction C; intros; inversion H0.
+ rewrite H2 in H0; rewrite <- H1; clear H2 X H0 H1 C'; rename r into X.
  exists n, CX; split; try constructor; auto.
+ elim (IHC _ _ _ _ _ H H4); intros.
  inversion_clear H5.
  rename x into n'; rename x0 into C0; inversion_clear H6.
  exists (S n'), (e; C0); split; try constructor; auto.
+ elim (IHC1 _ _ _ _ _ H H6); intros.
  inversion_clear H7.
  rename x into n'; rename x0 into C4; inversion_clear H8.
  exists (S n'), (If p == p0 Then C4 Else C2); split; try constructor; auto.
+ elim (IHC2 _ _ _ _ _ H H6); intros.
  inversion_clear H7.
  rename x into n'; rename x0 into C4; inversion_clear H8.
  exists (S n'), (If p == p0 Then C1 Else C4); split; try constructor; auto.
+ elim (IHC2 _ _ _ _ _ H H6); intros.
  inversion_clear H7.
  rename x into n'; rename x0 into C4; inversion_clear H8.
  exists (S n'), (Def r == C1 In C4); split; try constructor; auto.
Qed.
*)

Lemma Precongr_garbage_unfold_comm : forall n1 n2 C C' C'', C$n1 g>~ C' -> C'$n2 ~<u C'' ->
  exists C0, C$n2 ~<u C0 /\ C0$n1 g>~ C''.
Proof.
induction n1; [intros | induction n2]; intros.
+ inversion H. inversion H1.
  rewrite <- H5 in H0.
  clear C0 H3 C'0 H4 C' H5 C H2 H1 H.
  inversion H0. inversion H.
+ inversion H0. inversion H1.
  rewrite <- H5 in H, H0. rewrite <- H6 in H0.
  clear C'' H6 C' H5 C'0 H4 C0 H3 H1.
  inversion H.
  clear H7 C2' H6 C0 X0 H3 C H4 H n H1.
  elim (Precongr_garbage_Unfolded_comm _ _ _ _ _ _ H5 H2); intros.
  inversion_clear H. rename x into C0.
  exists (Def X == CX In C0); split; repeat constructor; auto.
+ revert H; inversion H0; intros; inversion H4.
  - clear C'' H3 C' H2 n H H0 C3 H9 eta0 H6 n0 H5 C H7 H4.
    elim (IHn1 _ _ _ _ H8 H1); intros.
    inversion_clear H. rename x into C3.
    exists (eta;C3); split; constructor; auto.
  - clear C1 H11 C''1 H10 q0 H9 p0 H6 C H7 H4 n0 H5 C' C'' H0 H2 H3 n H.
    elim (IHn1 _ _ _ _ H8 H1); intros.
    inversion_clear H. rename x into C3.
    exists (If p == q Then C3 Else C0); split; constructor; auto.
  - exists (If p == q Then C''0 Else C'1); split; try constructor; auto.
  - exists (If p == q Then C'1 Else C''0); split; try constructor; auto.
  - clear C1 H11 C''1 H10 q0 H9 p0 H6 C H7 H4 n0 H5 C' C'' H0 H2 H3 n H.
    elim (IHn1 _ _ _ _ H8 H1); intros.
    inversion_clear H. rename x into C3.
    exists (If p == q Then C0 Else C3); split; constructor; auto.
  - clear C2'0 H10 C0 H9 X0 H6 C H7 n0 H5 C'' C' H2 H3 H0 H4 n H.
    elim (IHn1 _ _ _ _ H8 H1); intros.
    inversion_clear H. rename x into C0.
    exists (Def X == C1 In C0); split; constructor; auto.
Qed.

Lemma Precongr_garbage_unfold_comm_trans : forall n1 n2 C C' C'', C$n1 g>=~ C' -> C'$n2 ~<=u C'' ->
  exists C0, C$n2 ~<=u C0 /\ C0$n1 g>=~ C''.
Proof.
intros.
eapply TransClose_comm; eauto.
apply Precongr_garbage_unfold_comm.
Qed.

End Weighted_Reductions.

End MCBase.
