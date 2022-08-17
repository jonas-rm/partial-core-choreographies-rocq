Require Import EPP.

(** * Amendment *)

Section Amendment.

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

Notation Sig' := (Sig' Sig).

Notation Forget := (@forget Pid Value Var RecVar).

Local Ltac eq_elim t t' H := case (eq_dec t t'); intro H;
  [ rewrite <- H in *; clear t' H | idtac].

Local Ltac sup := rewrite set_union_iff; auto.

(** ** Definitions *)

Section Amend.

Variable Defs:DefSet Sig.
Variable a:Ann.

(** The unprojectable processes at a conditional. *)

Fixpoint up_list p b ps C1 C2 : list Pid :=
  match ps with
  | nil => nil
  | r :: ps' => let ps'' := up_list p b ps' C1 C2 in
                if (r =? p) then ps''
                else if projectable_B_dec _ Defs (If p ?? b Then C1 Else C2) r
                then ps'' else (r :: ps'')
  end.

(** Add selections from p to all processes in ps. *)

Fixpoint add_sels p l ps C : Choreography Sig :=
  match ps with
  | nil => C
  | r :: ps' => p --> r[l]@a;; add_sels p l ps' C
  end.

Open Scope CC_scope.

(** Amending a choreography. *)

Fixpoint amend (ps:list Pid) (C:Choreography Sig) :=
match C with
| eta@a';; C' => eta@a';; (amend ps C')
| If p ?? b Then C1 Else C2 =>
    let l := up_list p b ps (amend ps C1) (amend ps C2) in
    If p ?? b Then (add_sels p left l (amend ps C1))
              Else (add_sels p right l (amend ps C2))
| RT_Call X l C' => RT_Call X l (amend ps C')
| _ => C
end.

(** Generalization to a set of procedure definitions. *)

Definition amend_D ps : DefSet Sig :=
  fun X => (fst (Defs X), amend ps (snd (Defs X))).

(** Sanity checks - examples from the paper. *)

Example BuyerSeller : forall buyer seller offer x acceptable product y,
  buyer<>seller ->
  amend (buyer::seller::nil)
  (buyer#offer --> seller$x@a;;
    If seller??acceptable
      Then (seller#product --> buyer$y@a;; CC.End)
    Else CC.End)
  = (buyer#offer --> seller$x@a;;
    If seller??acceptable
      Then (seller-->buyer[left]@a;; seller#product --> buyer$y@a;; CC.End)
    Else (seller-->buyer[right]@a;; CC.End)).
Proof.
intros; simpl.
rewrite <- eqb_neq in H. rewrite H.
elim projectable_B_dec; simpl; auto.
- intro; exfalso. rewrite eqb_neq in H.
  induction a0 as [B HB].
  inversion HB; auto.
  inversion H5; auto. inversion H8; auto.
  rewrite <- H19, <- H25 in H10; inversion H10.
- intro.
  rewrite eqb_refl. auto.
Qed.

Example counter_example_1 : forall p q r e e' x y b, p <> q -> p <> r -> q <> r ->
  amend (p::q::r::nil)
    (p#e-->q$x@a;; If r??b Then (r#e'-->p$y@a;;CC.End) Else CC.End)
  = (p#e-->q$x@a;; If r??b
                   Then (r-->p[left]@a;; r#e'-->p$y@a;; CC.End)
                   Else (r-->p[right]@a;; CC.End)).
Proof.
intros; simpl.
rewrite <- eqb_neq in H0, H1; rewrite H0, H1.
elim projectable_B_dec; auto.
2: elim projectable_B_dec; auto.
- intro; exfalso. rewrite eqb_neq in H0; clear H1.
  induction a0 as [B HB].
  inversion HB; auto.
  inversion H6; auto. inversion H9; auto.
  rewrite <- H20, <- H26 in H11; inversion H11.
- intro. rewrite eqb_refl. auto.
- intro; exfalso. apply b0.
  rewrite eqb_neq in H0, H1.
  exists (End _).
  apply bproj_Cond' with (End _) (End _); repeat constructor; auto.
Qed.

Example smart : forall p q r e e' e'' x b, p <> q -> p <> r -> q <> r ->
  amend (p::q::r::nil)
    (If p??b Then (p#e-->q$x@a;; q#e'-->r$x@a;; CC.End)
            Else (q#e''-->r$x@a;; CC.End))
  = (If p??b Then (p-->q[left]@a;; p#e-->q$x@a;; q#e'-->r$x@a;; CC.End)
            Else (p-->q[right]@a;; q#e''-->r$x@a;; CC.End)).
Proof.
intros; simpl.
rewrite eqb_refl.
assert (q <> p) as Hq; auto.
assert (r <> p) as Hr; auto.
rewrite <- eqb_neq in Hq, Hr; rewrite Hq, Hr.
elim projectable_B_dec; auto.
2: elim projectable_B_dec; auto.
- intro; exfalso.
  induction a0 as [B HB].
  inversion HB; auto.
  inversion H7; auto. inversion H10; auto.
  rewrite <- H21, <- H32 in H12; inversion H12.
- intros; exfalso. apply b0.
  exists (Recv Sig' q x a (End _)).
  apply bproj_Cond' with (Recv Sig' q x a (End _)) (Recv Sig' q x a (End _));
    repeat constructor; auto.
Qed.

Example counter_example_2 : forall p q r e x b, p <> q -> p <> r -> q <> r ->
  amend (p::q::r::nil)
    (If p??b Then (q#e-->r$x@a;; q#e-->p$x@a;; CC.End)
             Else (q#e-->r$x@a;; CC.End))
  = (If p??b Then (p-->q[left]@a;; q#e-->r$x@a;; q#e-->p$x@a;; CC.End)
             Else (p-->q[right]@a;; q#e-->r$x@a;; CC.End)).
Proof.
intros; simpl.
rewrite eqb_refl.
assert (q <> p) as Hq; auto.
assert (r <> p) as Hr; auto.
rewrite <- eqb_neq in Hq, Hr; rewrite Hq, Hr.
elim projectable_B_dec; auto.
2: elim projectable_B_dec; auto.
- intro; exfalso.
  induction a0 as [B HB].
  inversion HB; auto.
  revert H12.
  inversion_clear H7; auto. inversion_clear H10; auto.
  intro. inversion_clear H10. revert H13.
  inversion_clear H12; auto. inversion_clear H7; auto.
  intro. inversion_clear H13.
- intros; exfalso. apply b0.
  rewrite eqb_neq in Hr.
  exists (Recv Sig' q x a (End _)).
  apply bproj_Cond' with (Recv Sig' q x a (End _)) (Recv Sig' q x a (End _)); repeat constructor; auto.
Qed.

(** To avoid duplication of cases - I'd love an or... *)

Lemma up_list_If : forall p b r ps C1 C2,
  { up_list p b (r::ps) C1 C2 = up_list p b ps C1 C2 }
  + { up_list p b (r::ps) C1 C2 = r :: up_list p b ps C1 C2 }.
Proof. intros; simpl. elim (r =? p); auto. elim projectable_B_dec; auto. Qed.

Lemma not_In_up_list : forall p b ps C1 C2,
  ~In p (up_list p b ps C1 C2).
Proof.
induction ps; intros; simpl; auto.
case_eq (a0 =? p); auto.
elim projectable_B_dec; auto.
intros; intro.
inversion_clear H0; auto.
rewrite eqb_neq in H; auto.
apply (IHps _ _ H1).
Qed.

(** General properties of [up_list] *)

Lemma not_In_up_list' : forall p b ps C1 C2 r, p <> r -> In r ps ->
  ~In r (up_list p b ps C1 C2) ->
  projectable_B Defs (If p ?? b Then C1 Else C2) r.
Proof.
induction ps; intros. inversion H0.
inversion_clear H0.
+ rewrite H2 in *; clear a0 H2.
  revert H1; simpl.
  replace (r =? p) with false. 2: symmetry; rewrite eqb_neq; auto.
  elim projectable_B_dec; auto.
  intros. elim H1; simpl; auto.
+ revert H1.
  elim (up_list_If p b a0 ps C1 C2); intro HA; rewrite HA; auto.
  intro. apply IHps; auto.
  intro; apply H1; simpl; auto.
Qed.

(** Amendment does not add new process names to a choreography. *)

Lemma up_list_incl : forall p b ps C1 C2, up_list p b ps C1 C2 [C] ps.
Proof.
red; intros. induction ps; simpl; auto.
revert H; simpl. elim eqb; auto.
elim projectable_B_dec; auto.
simpl; intros. inversion_clear H; auto.
Qed.

Lemma up_list_incl_C : forall p b ps C1 C2,
  up_list p b ps C1 C2 [C] (CCC_pn C1 (Names Defs) [U] CCC_pn C2 (Names Defs)).
Proof.
red; intros. induction ps; simpl; auto. inversion H.
generalize H; simpl.
case_eq (a0 =? p); intro; auto.
elim projectable_B_dec; intros; auto.
elim (In_dec (@eq_dec Pid) z (up_list p b ps C1 C2)); auto.
intro. inversion_clear H1; auto.
rewrite H2 in *; clear a H2.
elim (In_dec (@eq_dec Pid) z (CCC_pn C1 (Names Defs) [U] CCC_pn C2 (Names Defs))); auto.
intro. elim b0.
exists (End _). apply bproj_not_In; auto.
simpl. repeat sup.
intro; apply b2. repeat sup. 
induction H1 as [ [H1 | H1] | H1]; auto.
rewrite eqb_neq in H0. simpl in H1.
inversion_clear H1; exfalso; auto.
Qed.

Lemma add_sels_CCC_pn_C : forall ps p l C f,
  CCC_pn C f [C] CCC_pn (add_sels p l ps C) f.
Proof. red; intros. induction ps; simpl; auto. sup. Qed.

Lemma add_sels_CCC_pn_ps : forall ps p l C f,
  ps [C] CCC_pn (add_sels p l ps C) f.
Proof.
red; intros.
induction ps, H.
all: simpl; sup. rewrite H; simpl; auto.
Qed.

Lemma add_sels_CCC_pn : forall ps p l C f,
  CCC_pn (add_sels p l ps C) f [C] (p :: CCC_pn C f [U] ps).
Proof.
intros; induction ps; simpl; auto.
red; simpl; auto.
red; red in IHps; intros.
simpl; rewrite set_add_iff.
rewrite set_union_iff in H.
induction H as [ [H | [H | H] ] | H]; auto.
inversion H. elim (IHps z); auto.
Qed.

Lemma amend_CCC_pn_C : forall ps f C, CCC_pn C f [C] CCC_pn (amend ps C) f.
Proof.
red; intros. induction C; simpl; auto.
all: sup.
+ induction e; simpl in H; rewrite set_union_iff in H; tauto.
+ simpl in H. repeat rewrite set_union_iff in H.
  induction H as [ [H | H] | H]; sup.
  1: left; right. 2: right.
  all: apply add_sels_CCC_pn_C; auto.
+ simpl in H. rewrite set_union_iff in H; tauto.
Qed.

Lemma amend_CCC_pn_incl : forall ps C,
  CCC_pn (amend ps C) (Names Defs) [C] CCC_pn C (Names Defs).
Proof.
red; intros. induction C. induction e.
all: simpl; auto.
all: simpl in H; repeat rewrite set_union_iff in H.
all: inversion_clear H; repeat sup.
inversion_clear H0; auto.
2: rename H0 into H.
all: apply add_sels_CCC_pn in H.
all: inversion_clear H. 1,3: rewrite H0; simpl; auto.
all: rewrite set_union_iff in H0; inversion_clear H0; auto.
all: apply up_list_incl_C in H; rewrite set_union_iff in H; tauto.
Qed.

(** Amendment preserves well-formedness. *)

Lemma add_sels_no_self_comm : forall p l ps C, ~In p ps ->
  no_self_comm _ C -> no_self_comm _ (add_sels p l ps C).
Proof.
induction ps; intros; simpl; auto.
simpl in H. apply Decidable.not_or in H.
inversion_clear H.
split; eauto.
Qed.

Lemma amend_no_self_comm : forall ps C,
  no_self_comm _ C -> no_self_comm _ (amend ps C).
Proof.
induction C; auto; intros.
+ induction e. all: destroy H; split; auto.
+ simpl. induction H as [H1 H2].
  specialize (IHC1 H1). specialize (IHC2 H2). clear H1 H2.
  split; apply add_sels_no_self_comm; auto.
  all: apply not_In_up_list; auto.
Qed.

Lemma add_sels_initial : forall p l ps C, initial C -> initial (add_sels p l ps C).
Proof. induction ps; auto. Qed.

Lemma amend_initial : forall ps C, initial C -> initial (amend ps C).
Proof.
induction C; auto; intros.
inversion_clear H.
split; apply add_sels_initial; auto.
Qed.

Lemma add_sels_no_empty_ann : forall p l ps C,
  no_empty_ann _ C -> no_empty_ann _ (add_sels p l ps C).
Proof. induction ps; auto. Qed.

Lemma amend_no_empty_ann : forall ps C,
  no_empty_ann _ C -> no_empty_ann _ (amend ps C).
Proof.
induction C; auto; intros.
+ inversion_clear H.
  split; apply add_sels_no_empty_ann; auto.
+ destroy H; split; auto.
Qed.

Lemma amend_Choreography_WF : forall ps C,
  Choreography_WF C -> Choreography_WF (amend ps C).
Proof.
intros.
destroy H; split.
apply amend_no_self_comm; auto.
apply amend_no_empty_ann; auto.
Qed.

Lemma add_sels_within_Xs : forall p l ps C Xs,
  within_Xs Xs C -> within_Xs Xs (add_sels p l ps C).
Proof. induction ps; auto. Qed.

Lemma amend_within_Xs : forall ps C Xs,
  within_Xs Xs C -> within_Xs Xs (amend ps C).
Proof.
induction C; auto; intros.
+ inversion_clear H.
  split; apply add_sels_within_Xs; auto.
+ destroy H. split; auto.
Qed.

Lemma add_sels_consistent : forall p l ps C, consistent _ (Vars (Defs,C)) C ->
  consistent _ (Vars (amend_D ps,add_sels p l ps C)) (add_sels p l ps C).
Proof. induction ps; auto. Qed.

Lemma amend_consistent : forall ps C, consistent _ (Vars (Defs,C)) C ->
  consistent _ (Vars (amend_D ps,amend ps C)) (amend ps C).
Proof.
induction C; auto; intros.
+ inversion_clear H.
  split; apply add_sels_consistent; auto.
+ destroy H. split; auto.
Qed.

Lemma amend_Program_WF : forall ps C Xs,
  Program_WF _ Xs (Defs,C) -> Program_WF _ Xs (amend_D ps,amend ps C).
Proof.
intros.
destroy H. split. 2: split. 3: split.
+ apply amend_Choreography_WF; auto.
+ apply amend_within_Xs; auto.
+ apply amend_consistent; auto.
+ intros X HX. induction (H X HX) as (H3,(H4,(H5,H6))).
  repeat split.
  - apply amend_no_self_comm; auto.
  - apply amend_initial; auto.
  - unfold Vars, amend_D; simpl. auto.
  - apply amend_within_Xs; auto.
Qed.

(** ** Selection expansion up to permutation
  This relation is used for characterising traces created by amendment. *)

Inductive sel_exp :
  list (TransitionLabel Pid Value) -> list (TransitionLabel Pid Value) -> Prop :=
| se_base l l' : Permutation l l' -> sel_exp l l'
| se_extra p q la l l' l'' : sel_exp l l' ->
                             Permutation (TL_Sel p q la::l') l'' -> sel_exp l l''.

Lemma sel_exp_refl : forall ts, sel_exp ts ts.
Proof. constructor. auto. Qed.

Lemma sel_exp_cons : forall t ts ts',
  sel_exp ts ts' -> sel_exp (t::ts) (t::ts').
Proof.
intros. induction H.
- apply se_base; auto.
- apply se_extra with p q la (t::l'); auto.
  eapply Permutation_trans. apply perm_swap. auto.
Qed.

Lemma sel_exp_extra : forall p q l ts ts',
  sel_exp ts ts' -> sel_exp ts (TL_Sel p q l::ts').
Proof.
intros.
apply se_extra with p q l ts'; auto.
Qed.

Lemma sel_exp_app : forall ts ts' ts'',
  sel_exp ts' ts'' -> sel_exp (ts++ts') (ts++ts'').
Proof.
induction ts; intros; auto.
apply sel_exp_cons; auto.
Qed.

Lemma sel_exp_perm' : forall ts ts' ts'',
  sel_exp ts ts' -> Permutation ts' ts'' -> sel_exp ts ts''.
Proof.
intros. induction H.
- apply se_base. eapply perm_trans; eauto.
- apply se_extra with p q la l'; auto.
  eapply Permutation_trans; eauto.
Qed.

Lemma sel_exp_perm : forall ts ts' ts'',
  sel_exp ts ts' -> Permutation ts'' ts -> sel_exp ts'' ts'.
Proof.
intros. induction H.
- apply se_base. eapply perm_trans; eauto.
- apply se_extra with p q la l'; auto.
Qed.

Lemma sel_exp_trans : forall ts ts' ts'',
  sel_exp ts ts' -> sel_exp ts' ts'' -> sel_exp ts ts''.
Proof.
intros. induction H0.
- apply sel_exp_perm' with l; auto.
- apply se_extra with p q la l'; auto.
Qed.

Lemma sel_exp_swap : forall t t' ts ts',
  sel_exp ts (t :: ts') -> sel_exp (t' :: ts) (t :: t' :: ts').
Proof.
intros.
eapply sel_exp_perm'.
2: apply perm_swap.
apply sel_exp_cons; auto.
Qed.

Lemma sel_exp_perm_extra : forall t t' ts ts' p q l,
  sel_exp ts (t :: ts') -> sel_exp (t' :: ts) (t :: t' :: (TL_Sel p q l) :: ts').
Proof.
intros.
eapply sel_exp_trans. 2: apply sel_exp_swap.
apply sel_exp_cons; eauto.
apply sel_exp_cons, sel_exp_extra.
apply sel_exp_refl.
Qed.

Lemma sel_exp_app' : forall t ts ts' ts'',
  sel_exp ts (t::ts') -> sel_exp (ts''++ts) (t::ts''++ts').
Proof.
intros.
apply sel_exp_perm' with (ts''++t::ts').
apply sel_exp_app; auto.
apply Permutation_sym, Permutation_middle.
Qed.

Lemma sel_exp_app'' : forall t ts ts' ts'',
  sel_exp ts (ts' ++ ts'') -> sel_exp (t :: ts) (ts' ++ t :: ts'').
Proof.
intros.
eapply sel_exp_trans.
apply sel_exp_cons; eauto.
constructor. apply Permutation_middle.
Qed.

Lemma sel_exp_app_both : forall ts1 ts1' ts2 ts2',
  sel_exp ts1 ts1' -> sel_exp ts2 ts2' -> sel_exp (ts1++ts2) (ts1'++ts2').
Proof.
intros.
eapply sel_exp_trans.
apply sel_exp_app; eauto.
eapply sel_exp_perm.
2: apply Permutation_app_comm.
eapply sel_exp_perm'.
2: apply Permutation_app_comm.
apply sel_exp_app; auto.
Qed.

(** Selections added by [add_sels] can be removed by a trace containing only selections. *)

Lemma add_sels_reduce : forall D p l ps C s,
  exists tl, sel_exp nil tl /\
    (D,add_sels p l ps C,s) --[tl]-->* (D,C,s).
Proof.
induction ps; simpl; intros.
+ exists nil. split. apply sel_exp_refl. apply CCT_Refl.
+ induction (IHps C s) as [tl [Hsub Htl] ].
  exists (@forget Pid Value Var RecVar (RL_Sel p a0 l)::tl).
  split. apply sel_exp_extra; auto.
  econstructor; eauto. repeat constructor; auto.
Qed.

(** If we added different selections to two choreographies, then
  any moves they both can perform must have been possible already. *)

Lemma add_sels_reduce_both : forall p ps C1 C2 s tl D C1' C2' s',
  <<add_sels p left ps C1,s>> --[tl,D]--> <<C1',s'>> ->
  <<add_sels p right ps C2,s>> --[tl,D]--> <<C2',s'>> ->
  exists C1'' C2'', <<C1,s>> --[tl,D]--> <<C1'',s'>>
    /\ <<C2,s>> --[tl,D]--> <<C2'',s'>>
    /\ C1' = add_sels p left ps C1'' /\ C2' = add_sels p right ps C2''.
Proof.
induction ps; simpl; intros.
+ exists C1', C2'; auto.
+ inversion H; inversion H0.
  1: rewrite <- H17 in H7; inversion H7.
  1: rewrite <- H7 in H18. simpl in H18. tauto.
  1: rewrite <- H16 in H8. simpl in H8. tauto.
  elim (IHps _ _ _ _ _ _ _ _ H9 H18).
  intros C1'' (C2'',(HC1,(HC2,(HC1',HC2')))).
  repeat eexists; repeat split; eauto.
  rewrite HC1'; auto.
  rewrite HC2'; auto.
Qed.

(** Miscellaneous. *)

Lemma amend_eq_End : forall ps C, amend ps C = CC.End -> C = CC.End.
Proof. induction C; simpl; auto; discriminate. Qed.

(** ** Completeness *)

Lemma amend_complete_1 : forall ps C s tl C' s', Choreography_WF C ->
  (Defs,C,s) --[tl]--> (Defs,C',s') ->
  exists tl' tlI tlF C'' s'',
       sel_exp tl' (tlI++tlF)
    /\ (Defs,C',s') --[tl']-->* (Defs,C'',s'')
    /\ (amend_D ps,amend ps C,s) --[tlI ++ tl::tlF]-->* (amend_D ps,amend ps C'',s'').
Proof.
Local Ltac IHElim IHC HC H tl' tlI CI sI tl0 C0 s0 tlF CF sF H1 H2 H3 H4 H5 H6 := 
    induction (IHC _ _ _ _ HC H) as
    [tl' [tlI [CI [sI [tl0 [C0 [s0 [tlF [CF [sF [H1 [H2 [H3 [H4 [H5 H6] ] ] ] ] ] ] ] ] ] ] ] ] ] ]; clear IHC.
intros. rename H into HC, H0 into H.
assert (exists tl' tlI CI sI tl0 C0 s0 tlF CF sF,
       sel_exp tl' (tlI++tlF)
    /\ tl = forget tl0
    /\ (Defs,C',s') --[tl']-->* (Defs,CF,sF)
    /\ (amend_D ps,amend ps C,s) --[tlI]-->* (amend_D ps,CI,sI)
    /\ <<CI,sI>> --[tl0,amend_D ps]--> <<C0,s0>>
    /\ (amend_D ps,C0,s0) --[tlF]-->* (amend_D ps,amend ps CF,sF)).
2: { induction H0 as [tl' [tlI [CI [sI [tl0 [C0 [s0 [tlF [CF [sF H0] ] ] ] ] ] ] ] ] ].
     induction H0 as (H0,(H1,(H2,(H3,(H4,H5))))).
     do 5 eexists. repeat split; eauto.
     eapply CCT_Trans; eauto. econstructor; eauto.
     rewrite H1; constructor; eauto. }
inversion_clear H. clear tl; rename H0 into H, t into tl.
revert C s tl C' s' HC H.
induction C; intros. induction e.
+ rename t0 into p, t1 into e, t2 into q, t3 into x, t into a'.
  inversion H.
  - (* Com *)
    rewrite <- H8 in *.
    clear s'0 H9 C' H8 tl H7 s0 H1 C0 H6 a0 H5 x0 H4 q0 H3 e0 H2 p0 H0 H.
    simpl. exists nil, nil; do 2 eexists.
    exists (RL_Com p v q x), (amend ps C), s'.
    exists nil, C, s'.
    repeat split; eauto. apply sel_exp_refl.
    all: constructor; auto; ESEr.
  - (* Delay *)
    rewrite <- H5 in *.
    clear s'0 H6 t H4 s0 H2 C0 H3 ann H1 eta H0 H H5.
    rename C' into Cc, C'0 into C'. simpl. induction H7 as [Hp Hq].
    set (v := eval_on_state Ev e s p). set (tlS := RL_Com (RecVar:=RecVar) p v q x).
    assert (v = eval_on_state Ev e s' p) as Hv.
    1: unfold v. eapply CCC_To_disjoint_eval; eauto.
    apply CCC_To_disjoint_update with (p:=q) (v:=v) (x:=x) in H8; auto.
    IHElim IHC (Choreography_WF_eta _ _ _ _ HC) H8 tl' tlI CI sI tl0 C0 s0 tlF CF sF Htrace Hforget H' HI H0 HF.
    exists (forget tlS::tl'). exists (forget tlS::tlI), CI, sI.
    exists tl0, C0, s0. exists tlF, CF, sF.
    repeat split; auto.
    * apply sel_exp_cons; auto.
    * econstructor; eauto. unfold tlS; rewrite Hv.
      repeat constructor; auto.
    * econstructor; eauto. repeat constructor; auto.
+ rename t0 into p, t1 into q, t2 into l, t into a'.
  inversion H.
  - (* Sel *)
    rewrite <- H7 in *.
    clear s'0 H8 C' H7 tl H6 s0 H0 C0 H5 a0 H3 l0 H2 q0 H1 p0 H H4.
    simpl. exists nil, nil; do 2 eexists.
    exists (RL_Sel p q l), (amend ps C), s'.
    exists nil, C, s'.
    repeat split; eauto. apply sel_exp_refl.
    all: constructor; eauto; try ESEr.
  - (* Delay *)
    rewrite <- H5 in *.
    clear s'0 H6 t H3 s0 H1 C0 H2 ann H0 eta H H4 H5.
    rename C' into Cc, C'0 into C'.
    IHElim IHC (Choreography_WF_eta _ _ _ _ HC) H8 tl' tlI CI sI tl0 C0 s0 tlF CF sF Htrace Hforget H' HI H0 HF.
    simpl. set (tlS := @RL_Sel _ Value Var RecVar p q l).
    exists (forget tlS::tl'). exists (forget tlS::tlI), CI, sI.
    exists tl0, C0, s0. exists tlF, CF, sF.
    repeat split; auto.
    * apply sel_exp_cons; auto.
    * econstructor; eauto. repeat constructor; auto.
    * econstructor; eauto. repeat constructor; auto.
+ rename t into p, t0 into b.
  inversion H.
  - (* Then *)
    rewrite <- H6 in *.
    clear s'0 H7 C' H6 tl H5 s0 H1 C3 H3 C0 H2 b0 H0 p0 H H4.
    elim (add_sels_reduce (amend_D ps) p left (up_list p b ps (amend ps C1) (amend ps C2)) (amend ps C1) s').
    intros t1 (Ht1,Ht1').
    exists nil, nil; do 2 eexists.
    exists (@RL_Cond Pid Value Var RecVar p); do 2 eexists.
    exists t1, C1, s'.
    repeat split; auto. 1,2: apply CCT_Refl.
    simpl. apply C_Then; eauto.
    apply CCP_ToStar_Defs_eq with (D:=amend_D ps) in Ht1'; auto.
  - (* Else *)
    rewrite <- H6 in *.
    clear s'0 H7 C' H6 tl H5 s0 H1 C3 H3 C0 H2 b0 H0 p0 H H4.
    elim (add_sels_reduce (amend_D ps) p right (up_list p b ps (amend ps C1) (amend ps C2)) (amend ps C2) s').
    intros t1 (Ht1,Ht1').
    exists nil, nil; do 2 eexists.
    exists (@RL_Cond Pid Value Var RecVar p); do 2 eexists.
    exists t1, C2, s'.
    repeat split; auto. 1,2: apply CCT_Refl.
    simpl. apply C_Else; eauto.
    apply CCP_ToStar_Defs_eq with (D:=amend_D ps) in Ht1'; auto.
  - (* Delay *)
    rewrite <- H6 in *.
    clear s'0 H7 t H5 s0 H2 C3 H3 C0 H1 b0 H0 p0 H H6 H4.
    IHElim IHC1 (Choreography_WF_Then _ _ _ _ _ HC) H9 tl'1 tl1I C1I s1I tl01 C01 s01 tl1F C1F s1F Htrace1 Hforget1 H1' H1I H01 H1F.
    IHElim IHC2 (Choreography_WF_Else _ _ _ _ _ HC) H10 tl'2 tl2I C2I s2I tl02 C02 s02 tl2F C2F s2F Htrace2 Hforget2 H2' H2I H02 H2F.
    generalize (CCC_To_disjoint_beval _ _ _ _ _ _ _ b _ H8 H9); intro Hb.
    case_eq (eval_on_state BEv b s p); intro Hb'.
    * (* Then, amend *)
      simpl.
      set (tl0 := @RL_Cond Pid Value Var RecVar p).
      elim (add_sels_reduce (amend_D ps) p left (up_list p b ps (amend ps C1) (amend ps C2)) (amend ps C1) s).
      intros t1 (Ht1,Ht1').
      exists (Forget tl0::tl'1).
      exists (Forget tl0::t1++tl1I), C1I, s1I.
      exists tl01, C01, s01.
      exists tl1F, C1F, s1F.
      repeat split; auto.
      ++ simpl. apply sel_exp_cons.
         rewrite <- (app_nil_l tl'1), <- app_assoc.
         apply sel_exp_app_both; auto.
      ++ econstructor; eauto. repeat constructor. rewrite <- Hb; auto.
      ++ econstructor; eauto. 2: eapply CCT_Trans; eauto.
         repeat constructor; auto.
    * (* Else, no amend *)
      set (tl0 := @RL_Cond Pid Value Var RecVar p).
      elim (add_sels_reduce (amend_D ps) p right (up_list p b ps (amend ps C1) (amend ps C2)) (amend ps C2) s).
      intros t1 (Ht1,Ht1').
      exists (Forget tl0::tl'2).
      exists (Forget tl0::t1++tl2I), C2I, s2I.
      exists tl02, C02, s02.
      exists tl2F, C2F, s2F.
      repeat split; auto.
      ++ simpl. apply sel_exp_cons.
         rewrite <- (app_nil_l tl'2), <- app_assoc.
         apply sel_exp_app_both; auto.
      ++ econstructor; eauto. repeat constructor. rewrite <- Hb; auto.
      ++ econstructor; eauto. 2: eapply CCT_Trans; eauto.
         repeat constructor; auto.
+ rename t into X. inversion H.
  - (* Local *)
    rewrite <- H6 in *.
    clear s'0 H7 C' H6 tl H5 s0 H4 X0 H0 H.
    simpl. exists nil, nil; do 2 eexists.
    exists (RL_Call X p), (amend ps (snd (Defs X))), s'.
    exists nil, (snd (Defs X)), s'.
    repeat split; eauto. apply sel_exp_refl.
    all: constructor; simpl; eauto; ESEr.
  - (* Call *)
    rewrite <- H5 in *.
    clear s'0 H7 C' H6 tl H5 s0 H4 X0 H0 H.
    simpl. exists nil, nil; do 2 eexists.
    exists (RL_Call X p); eexists; exists s'.
    exists nil; eexists; exists s'.
    repeat split; eauto. apply sel_exp_refl.
    all: constructor; simpl; eauto; ESEr.
+ rename t into X. inversion H.
  - (* Delay *)
    rewrite <- H5, <- H1 in *.
    clear s'0 H6 C' H5 t H4 s0 H2 C0 H3 H X0 H0 l H1. rename C'0 into C'.
    IHElim IHC (Choreography_WF_Call_1 _ _ _ _ HC) H8 tl' tlI CI sI tl0 C0 s0 tlF CF sF Htrace Hforget H' HI H0 HF.
    induction HC as [HC [Hps HA] ]. clear HC HA.
    induction (RT_Call_reduce _ _ Hps) as [tlR HR].
    exists (tlR++tl'). exists (tlR++tlI), CI, sI.
    exists tl0, C0, s0. exists tlF, CF, sF.
    repeat split; auto.
    * rewrite <- app_assoc. apply sel_exp_app; auto.
    * eapply CCT_Trans; eauto.
    * eapply CCT_Trans; eauto.
  - (* Enter *)
    rewrite <- H6, <- H1 in *.
    clear s'0 H7 C' H6 tl H5 s0 H4 C0 H2 H X0 H0 l H1.
    simpl. exists nil, nil; do 2 eexists.
    exists (RL_Call X p), (RT_Call X (ps0[\]p) (amend ps C)), s'.
    exists nil; eexists; exists s'.
    repeat split; eauto. apply sel_exp_refl.
    all: constructor; eauto; ESEr.
  - (* Finish *)
    rewrite <- H6, <- H1 in *.
    clear s'0 H7 C' H6 tl H5 s0 H4 C0 H2 H X0 H0 l H1.
    simpl. exists nil, nil; do 2 eexists.
    exists (RL_Call X p), (amend ps C), s'.
    exists nil, C, s'.
    repeat split; eauto. apply sel_exp_refl.
    all: constructor; eauto; ESEr.
+ inversion H.
Qed.

Lemma amend_complete_1' : forall ps C s tl C' s', Choreography_WF C ->
  (Defs,C,s) --[tl]--> (Defs,C',s') ->
  exists tl' tl'' C'' s'',
       sel_exp (tl::tl') tl''
    /\ (Defs,C',s') --[tl']-->* (Defs,C'',s'')
    /\ (amend_D ps,amend ps C,s) --[tl'']-->* (amend_D ps,amend ps C'',s'').
Proof.
intros.
elim (amend_complete_1 ps C s tl C' s'); auto.
intros. induction H1 as (tlI,(tlF,(C'',(s'',(H1,(H2,H3)))))).
do 4 eexists. repeat split; eauto.
apply sel_exp_app''; auto.
Qed.

Lemma amend_complete_many : forall ps C s tl C' s' Xs, Program_WF _ Xs (Defs,C) ->
  (Defs,C,s) --[tl]-->* (Defs,C',s') ->
  exists tl' tl'' C'' s'',
       sel_exp (tl++tl') tl''
    /\ (Defs,C',s') --[tl']-->* (Defs,C'',s'')
    /\ (amend_D ps,amend ps C,s) --[tl'']-->* (amend_D ps,amend ps C'',s'').
Proof.
intros.
set (n := length tl). assert (length tl <= n) as Hn; auto.
clearbody n. revert C s tl C' s' Hn H H0.
induction n; intros.
+ case_eq tl; intros.
  2: rewrite H1 in Hn; inversion Hn.
  rewrite H1 in *; clear tl H1.
  inversion_clear H0.
  exists nil, nil, C', s'.
  repeat split; simpl; constructor; auto; ESEr.
+ case_eq tl; intros.
  1: { (* repeat... *)
    rewrite H1 in *; clear tl H1.
    inversion_clear H0.
    exists nil, nil, C', s'.
    repeat split; simpl; constructor; auto; ESEr.
  }
  rewrite H1 in *; clear tl H1.
  simpl in Hn. apply le_S_n in Hn. rename l into tl.
  inversion_clear H0. induction c2 as [ [D C''] s''].
  generalize (CCP_To_Defs_stable _ _ _ _ _ _ _ _ H1). intro H'; rewrite <- H' in *; clear D H'.
  elim (amend_complete_1' ps C s t C'' s''); auto.
  2: elim H; auto.
  intros tl0 [t0 [C0 [s0 [Hsub0 [Htl0 Htl0IF] ] ] ] ].
  induction (diamond_4b _ _ _ _ _ _ _ _ _ H2 Htl0) as [ [D C2] [tl' [tl0' [s2a [s2b [HC' [HC0 [Hs [Hperm [Hlen1 Hlen2] ] ] ] ] ] ] ] ] ].
  generalize (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ _ HC'). intro H'; rewrite <- H' in *; clear D H'.
  generalize (CCP_To_Program_WF _ _ _ _ _ _ _ H H1). intro HP''.
  generalize (CCP_ToStar_Program_WF _ _ _ _ _ _ _ HP'' H2). intro HP'.
  generalize (CCP_ToStar_Program_WF _ _ _ _ _ _ _ HP' HC'). intro HP2.
  generalize (CCP_ToStar_Program_WF _ _ _ _ _ _ _ HP'' Htl0). intro HP0.
  elim (IHn C0 s0 tl0' C2 s2b); auto.
  intros tl1 [t1 [C1 [s1 [Hsub1 [Htl1 Htl1IF] ] ] ] ].
  2: etransitivity; eauto.
  exists (tl' ++ tl1), (t0 ++ t1), C1, s1.
  repeat split.
  - simpl. eapply sel_exp_trans.
    2: apply sel_exp_app_both; eauto.
    simpl. apply sel_exp_cons.
    repeat rewrite app_assoc.
    constructor. apply Permutation_app; auto.
  - eapply CCT_Trans; eauto.
    apply CCP_ToStar_eq with s2b s1. ESEs. ESEr. auto.
  - eapply CCT_Trans; eauto.
Qed.

(** ** Soundness *)

Lemma amend_sound_1 : forall ps C s tl C' s', Choreography_WF C ->
  (amend_D ps, amend ps C,s) --[tl]--> (amend_D ps,C',s') ->
  exists tl' tl'' C'' s'',
  (amend_D ps,C',s') --[tl']-->* (amend_D ps, amend ps C'',s'')
  /\ (Defs,C,s) --[tl'']-->* (Defs,C'',s'') /\ sel_exp tl'' (tl::tl').
Proof.
Local Ltac IHElim' IHC HC H tl' tl'' C'' s'' Htl' Htl'' Hsub :=
   induction (IHC HC _ _ _ H) as [tl' [tl'' [C'' [s'' [Htl' [Htl'' Hsub] ] ] ] ] ]; clear IHC.
intros. rename H into HC. inversion_clear H0.
clear tl. revert C HC s C' s' H.
induction C; intros. induction e.
+ rename t1 into p, t2 into e, t3 into q, t4 into x, t0 into a'.
  inversion H.
  - (* Com *)
    rewrite <- H7 in *.
    clear s'0 H9 C' H8 t H7 s0 H1 C0 H6 a0 H5 x0 H4 q0 H3 e0 H2 p0 H H0.
    exists nil, (Forget (RL_Com p v q x) :: nil), C, s'. repeat split.
    * repeat constructor.
    * econstructor; eauto. 2: apply CCT_Refl. repeat constructor; auto.
    * apply sel_exp_refl.
  - (* Delay *)
    clear s'0 H6 C' H5 t0 H4 s0 H2 C0 H3 ann H1 eta H H0.
    induction H7 as [Hp Hq].
    set (v := eval_on_state Ev e s' p). set (tlS := RL_Com (RecVar:=RecVar) p v q x).
    assert (v = eval_on_state Ev e s p) as Hv.
    1: unfold v. symmetry; eapply CCC_To_disjoint_eval; eauto.
    apply CCC_To_disjoint_update with (p:=q) (v:=v) (x:=x) in H8; auto.
    IHElim' IHC (Choreography_WF_eta _ _ _ _ HC) H8 tl' tl'' C'' s'' Htl' Htl'' Hsub.
    exists (Forget tlS::tl'), (Forget tlS::tl''), C'', s''.
    repeat split; auto.
    * econstructor; eauto. unfold v; repeat constructor.
    * econstructor; eauto. unfold tlS; rewrite Hv; repeat constructor.
    * apply sel_exp_swap; auto.
+ rename t1 into p, t2 into q, t3 into l, t0 into a'.
  inversion H.
  - (* Sel *)
    rewrite <- H6 in *.
    clear s'0 H8 C' H7 t H6 s0 H1 C0 H5 a0 H4 l0 H3 q0 H2 p0 H H0.
    exists nil, (Forget (RL_Sel p q l) :: nil), C, s'. repeat split.
    * repeat constructor.
    * econstructor; eauto. 2: apply CCT_Refl. repeat constructor; auto.
    * apply sel_exp_refl.
  - (* Delay *)
    clear s'0 H6 C' H5 t0 H4 s0 H2 C0 H3 ann H1 eta H H0.
    induction H7 as [Hp Hq].
    IHElim' IHC (Choreography_WF_eta _ _ _ _ HC) H8 tl' tl'' C'' s'' Htl' Htl'' Hsub.
    set (tlS := @RL_Sel Pid Value Var RecVar p q l).
    exists (Forget tlS::tl'), (Forget tlS::tl''), C'', s''.
    repeat split; auto.
    * econstructor; eauto. repeat constructor.
    * econstructor; eauto. repeat constructor.
    * apply sel_exp_swap; auto.
+ rename t0 into p, t1 into b.
  inversion H.
  - (* Then *)
    rewrite <- H5, <- H6 in *.
    clear s'0 H7 C' H6 t H5 s0 H2 C3 H4 C0 H3 b0 H1 p0 H0.
    elim (add_sels_reduce (amend_D ps) p left (up_list p b ps (amend ps C1) (amend ps C2)) (amend ps C1) s').
    intros t1 (Ht1,Ht1').
    exists t1, (Forget (RL_Cond p)::nil), C1, s'. repeat split; auto.
    * econstructor. 2: apply CCT_Refl. repeat constructor; eauto.
    * apply sel_exp_cons; auto.
  - (* Else *)
    rewrite <- H5, <- H6 in *.
    clear s'0 H7 C' H6 t H5 s0 H2 C3 H4 C0 H3 b0 H1 p0 H0.
    elim (add_sels_reduce (amend_D ps) p right (up_list p b ps (amend ps C1) (amend ps C2)) (amend ps C2) s').
    intros t1 (Ht1,Ht1').
    exists t1, (Forget (RL_Cond p)::nil), C2, s'. repeat split; auto.
    * econstructor. 2: apply CCT_Refl. repeat constructor; eauto.
    * apply sel_exp_cons; auto.
  - (* Delay *)
    rewrite <- H6 in *.
    clear s'0 H7 C' H6 t0 H5 s0 H3 C3 H4 C0 H2 b0 H1 p0 H0.
    generalize (CCC_To_disjoint_beval _ _ _ _ _ _ _ b _ H8 H9); intro Hb.
    elim (add_sels_reduce_both _ _ _ _ _ _ _ _ _ _ H9 H10).
    intros C'1 (C'2,(HC1,(HC2,(HC'1,HC'2)))).
    rewrite HC'1, HC'2 in *; clear C1' C2' HC'1 HC'2.
    case_eq (eval_on_state BEv b s p); intro Hb'.
    * IHElim' IHC1 (Choreography_WF_Then _ _ _ _ _ HC) HC1 tl' tl'' C'' s'' Htl' Htl'' Hsub.
      elim (add_sels_reduce (amend_D ps) p left (up_list p b ps (amend ps C1) (amend ps C2)) C'1 s').
      intros t1 (Ht1,Ht1').
      exists (Forget (RL_Cond p)::t1++tl'), (Forget (RL_Cond p)::tl''), C'', s''.
      repeat split.
      econstructor; eauto. repeat constructor; auto. rewrite <- Hb; auto.
      eapply CCT_Trans; eauto.
      econstructor; eauto. repeat constructor; auto.
      apply sel_exp_swap; auto.
      rewrite <- (app_nil_r tl'').
      apply sel_exp_perm' with ((Forget t :: tl') ++ t1).
      apply sel_exp_app_both; auto.
      simpl. apply Permutation_cons; auto. apply Permutation_app_comm.
    * IHElim' IHC2 (Choreography_WF_Else _ _ _ _ _ HC) HC2 tl' tl'' C'' s'' Htl' Htl'' Hsub.
      elim (add_sels_reduce (amend_D ps) p right (up_list p b ps (amend ps C1) (amend ps C2)) C'2 s').
      intros t1 (Ht1,Ht1').
      exists (Forget (RL_Cond p)::t1++tl'), (Forget (RL_Cond p)::tl''), C'', s''.
      repeat split.
      econstructor; eauto. constructor. apply C_Else'; eauto.
      eapply CCT_Trans; eauto.
      econstructor; eauto. repeat constructor; auto.
      apply sel_exp_swap; auto.
      rewrite <- (app_nil_r tl'').
      apply sel_exp_perm' with ((Forget t :: tl') ++ t1).
      apply sel_exp_app_both; auto.
      simpl. apply Permutation_cons; auto. apply Permutation_app_comm.
+ rename t0 into X. inversion H.
  - (* Local *)
    rewrite <- H6 in *.
    clear s'0 H7 C' H6 t H5 s0 H4 X0 H0 H.
    simpl. exists nil, (Forget (RL_Call X p)::nil), (snd (Defs X)), s'.
    repeat split; repeat constructor.
    econstructor. 2: apply CCT_Refl. repeat constructor; auto.
  - (* Call *)
    rewrite <- H5 in *.
    clear s'0 H7 C' H6 t H5 s0 H4 X0 H0 H.
    simpl. exists nil, (Forget (RL_Call X p)::nil), (RT_Call X (fst (Defs X) [\] p) (snd (Defs X))), s'.
    repeat split; eauto. 3: apply sel_exp_refl.
    apply CCT_Refl.
    econstructor. 2: apply CCT_Refl. repeat constructor; auto.
+ rename t0 into X. inversion H.
  - (* Delay *)
    rewrite <- H5, <- H1 in *.
    clear s'0 H6 C' H5 t0 H4 s0 H2 C0 H3 H X0 H0 l H1. rename C'0 into C'.
    IHElim' IHC (Choreography_WF_Call_1 _ _ _ _ HC) H8 tl' tl'' C'' s'' Htl' Htl'' Hsub.
    induction HC as [HC [Hps HA] ]; clear HC HA.
    induction (RT_Call_reduce _ _ Hps) as [tlR HR].
    exists (tlR++tl'), (tlR++tl''), C'', s''.
    repeat split; auto.
    * eapply CCT_Trans; eauto.
    * eapply CCT_Trans; eauto.
    * apply sel_exp_app'; auto.
  - (* Enter *)
    rewrite <- H5, <- H1 in *.
    clear s'0 H7 C' H6 t H5 s0 H4 C0 H2 H X0 H0 l H1.
    exists nil, (Forget (RL_Call X p)::nil), (RT_Call X (ps0[\]p) C), s'.
    repeat split; eauto. 3: apply sel_exp_refl.
    apply CCT_Refl.
    econstructor. 2: apply CCT_Refl. repeat constructor; auto.
  - (* Finish *)
    rewrite <- H5, <- H1 in *.
    clear s'0 H7 C' H6 t H5 s0 H4 C0 H2 H X0 H0 l H1.
    exists nil, (Forget (RL_Call X p)::nil), C, s'.
    repeat split; eauto. 3: apply sel_exp_refl.
    apply CCT_Refl.
    econstructor. 2: apply CCT_Refl. repeat constructor; auto.
+ inversion H.
Qed.

Lemma amend_sound_many : forall ps C s tl C' s' Xs, Program_WF _ Xs (Defs,C) ->
  (amend_D ps, amend ps C,s) --[tl]-->* (amend_D ps,C',s') ->
  exists tl' tl'' C'' s'',
  (amend_D ps,C',s') --[tl']-->* (amend_D ps, amend ps C'',s'')
  /\ (Defs,C,s) --[tl'']-->* (Defs,C'',s'') /\ sel_exp tl'' (tl++tl').
Proof.
intros.
set (n := length tl). assert (length tl <= n) as Hn; auto.
clearbody n. revert C s tl C' s' Hn H H0.
induction n; intros.
+ case_eq tl; intros.
  2: rewrite H1 in Hn; inversion Hn.
  rewrite H1 in *; clear tl H1.
  inversion H0. rewrite <- H2 in *.
  exists nil, nil, C, s'.
  repeat split; simpl; auto. apply CCT_Refl.
  constructor; auto; ESEr. apply sel_exp_refl.
+ case_eq tl; intros.
  1: { (* repeat... *)
    rewrite H1 in *; clear tl H1.
    inversion H0. rewrite <- H2 in *.
    exists nil, nil, C, s'.
    repeat split; simpl; auto. apply CCT_Refl.
    constructor; auto; ESEr. apply sel_exp_refl.
  }
  rewrite H1 in *; clear tl H1.
  simpl in Hn. apply le_S_n in Hn. rename l into tl.
  inversion_clear H0. induction c2 as [ [D C''] s''].
  generalize (CCP_To_Defs_stable _ _ _ _ _ _ _ _ H1). intro H'; rewrite <- H' in *; clear D H'.
  elim (amend_sound_1 ps C s t C'' s''); auto.
  2: elim H; auto.
  intros tl0 [t0 [C0 [s0 [Htl0 [Hsub0 Htl0IF] ] ] ] ].
  induction (diamond_4b _ _ _ _ _ _ _ _ _ H2 Htl0) as [ [D C2] [tl' [tl0' [s2a [s2b [HC' [HC0 [Hs [Hperm [Hlen1 Hlen2] ] ] ] ] ] ] ] ] ].
  generalize (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ _ HC'). intro H'; rewrite <- H' in *; clear D H'.
  generalize (CCP_To_Program_WF _ _ _ _ _ _ _ (amend_Program_WF _ _ _ H) H1). intro HP''.
  generalize (CCP_ToStar_Program_WF _ _ _ _ _ _ _ HP'' H2). intro HP'.
  generalize (CCP_ToStar_Program_WF _ _ _ _ _ _ _ HP' HC'). intro HP2.
  generalize (CCP_ToStar_Program_WF _ _ _ _ _ _ _ HP'' Htl0). intro HP0.
  elim (IHn C0 s0 tl0' C2 s2b); auto.
  intros tl1 [t1 [C1 [s1 [Hsub1 [Htl1 Htl1IF] ] ] ] ].
  2: etransitivity; eauto.
  exists (tl' ++ tl1), (t0 ++ t1), C1, s1.
  repeat split.
  - eapply CCT_Trans; eauto.
    apply CCP_ToStar_eq with s2b s1. ESEs. ESEr. auto.
  - eapply CCT_Trans; eauto.
  - simpl. eapply sel_exp_trans.
    apply sel_exp_app_both; eauto.
    simpl. apply sel_exp_cons.
    repeat rewrite app_assoc.
    constructor. apply Permutation_sym, Permutation_app; auto.
  - eapply CCP_ToStar_Program_WF. 2: eauto. auto.
Qed.

End Amend.

(** ** Additional lemmas
These lemmas cannot be proved earlier because we made Defs a section parameter. *)

Section Miscellaneous.

Lemma up_list_stable : forall Defs Defs' p b ps C1 C2,
  (forall X, fst (Defs X) = fst (Defs' X)) ->
  up_list Defs p b ps C1 C2 = up_list Defs' p b ps C1 C2.
Proof.
intros. induction ps; simpl; auto.
elim (a =? p); auto.
do 2 elim projectable_B_dec; auto.
3: rewrite IHps; auto.
1,2: intros; exfalso.
all: generalize projectable_B_stable; eauto.
Qed.

(** Now we can also define amendment of a program. *)

Variable ps : list Pid.
Variable a : Ann.
Variable P : CC.Program Sig.

Definition amend_P :=
  (amend_D (Procedures _ P) a ps, amend (Procedures _ P) a ps (Main P)).

Lemma amend_P_Vars : Vars P = Vars amend_P.
Proof. auto. Qed.

End Miscellaneous.

(** ** Projectability of amendment. *)

Section Projectability.

Lemma add_sels_proj' : forall Defs a p l ps C r, ~In r ps ->
  projectable_B Defs C r -> projectable_B Defs (add_sels a p l ps C) r.
Proof.
induction ps; auto.
intros. simpl in *.
apply Decidable.not_or in H; inversion_clear H.
induction (IHps C r) as [B HB]; auto.
elim (eq_dec p r); intro Hpr. rewrite Hpr in *.
all: eexists; constructor; eauto.
Qed.

Lemma add_sels_proj : forall Defs a p b ps C1 C2 r, p <> r -> In r ps ->
  projectable_B Defs C1 r -> projectable_B Defs C2 r ->
  projectable_B Defs (If p ?? b Then (add_sels a p left ps C1) Else (add_sels a p right ps C2)) r.
Proof.
induction ps; intros. inversion H0.
induction H0 as [H0 | H0]; simpl.
elim (In_dec (@eq_dec Pid) r ps); intro Hr.
3: elim (eq_dec a0 r); intro Hr.
+ rewrite H0.
  induction (IHps _ _ _ H Hr H1 H2) as [B HB]; clear IHps.
  revert H; inversion_clear HB; intros. tauto.
  exists (Branching Sig' p (Some (a,B1)) (Some (a,B2))).
  apply bproj_Cond' with (Branching Sig' p (Some (a,B1)) None)
        (Branching Sig' p None (Some (a,B2))); auto.
  all: try constructor; auto.
  apply (merge_Branching_SNNS Sig').
+ rewrite H0.
  apply (add_sels_proj' Defs a p left ps) in H1; auto.
  apply (add_sels_proj' Defs a p right ps) in H2; auto.
  induction H1 as [B1 HB1]. induction H2 as [B2 HB2].
  exists (Branching Sig' p (Some (a,B1)) (Some (a,B2))).
  apply bproj_Cond' with (Branching Sig' p (Some (a,B1)) None)
        (Branching Sig' p None (Some (a,B2))); auto.
  all: try constructor; auto.
  apply (merge_Branching_SNNS Sig').
+ rewrite Hr.
  induction (IHps _ _ _ H H0 H1 H2) as [B HB]; clear IHps.
  revert H; inversion_clear HB; intros. tauto.
  exists (Branching Sig' p (Some (a,B1)) (Some (a,B2))).
  apply bproj_Cond' with (Branching Sig' p (Some (a,B1)) None)
        (Branching Sig' p None (Some (a,B2))); auto.
  all: try constructor; auto.
  apply (merge_Branching_SNNS Sig').
+ induction (IHps _ _ _ H H0 H1 H2) as [B HB]; clear IHps.
  revert H; inversion_clear HB; intros. tauto.
  exists B. apply bproj_Cond' with B1 B2; auto.
  all: constructor; auto.
Qed.

Lemma add_sels_proj'' : forall Defs a p b ps C1 C2 r,
  projectable_B Defs (If p ?? b Then C1 Else C2) r  ->
  projectable_B Defs (If p ?? b Then (add_sels a p left ps C1) Else (add_sels a p right ps C2)) r.
Proof.
induction ps; auto.
simpl; intros.
einduction IHps as [B HB]; eauto.
inversion HB.
2: elim (eq_dec a0 r); intro Hr.
+ rewrite H3 in *. eexists. constructor; constructor; eauto.
+ rewrite Hr.
  eexists. econstructor; auto.
  apply (bproj_Left Sig); eauto. apply (bproj_Right Sig); eauto.
  constructor.
+ eexists. econstructor; eauto. all: constructor; eauto.
Qed.

Lemma amend_projectable_B : forall Defs a r ps C,
  In r ps -> projectable_B (amend_D Defs a ps) (amend Defs a ps C) r.
Proof.
induction C; intros.
+ simpl.
  induction IHC as [B HB]; auto.
  induction e. all: eq_elim r t0 Hr.
  2: eq_elim r t2 Hr'. 5: eq_elim r t1 Hr'. 5: induction t2.
  all: try (eexists; econstructor; eauto; fail).
  exists (@Branching Sig' t0 (Some (t,B)) None). constructor; auto.
  exists (@Branching Sig' t0 None (Some (t,B))). constructor; auto.
+ simpl. specialize (IHC1 H). specialize (IHC2 H).
  elim (eq_dec t r); intro Htr.
  2: elim (In_dec (@eq_dec Pid) r (up_list Defs t t0 ps (amend Defs a ps C1) (amend Defs a ps C2))); intro Hr.
  - rewrite Htr.
    apply (add_sels_proj' (amend_D Defs a ps) a r left (up_list Defs r t0 ps (amend Defs a ps C1) (amend Defs a ps C2))) in IHC1.
    apply (add_sels_proj' (amend_D Defs a ps) a r right (up_list Defs r t0 ps (amend Defs a ps C1) (amend Defs a ps C2))) in IHC2.
    2,3: apply not_In_up_list.
    induction IHC1 as [B1 HB1]. induction IHC2 as [B2 HB2].
    eexists. constructor; eauto.
  - apply add_sels_proj; auto.
  - apply add_sels_proj''. apply not_In_up_list' with ps; auto.
    intro; apply Hr. erewrite up_list_stable; eauto.
+ elim (in_dec (@eq_dec Pid) r (fst (Defs t))).
  all: eexists. constructor; auto. apply bproj_Call_out; auto.
+ elim (in_dec (@eq_dec Pid) r l).
  eexists. constructor; auto.
  induction IHC as [B HB]; auto.
  eexists. apply bproj_RT_Call_out; eauto.
+ simpl. eexists; constructor.
Qed.

Lemma amend_projectable_C : forall Defs a ps C, projectable_C (amend_D Defs a ps) (amend Defs a ps C) ps.
Proof.
intros. red. rewrite Forall_forall.
intros. apply amend_projectable_B; auto.
Qed.

End Projectability.

End Amendment.

Arguments amend [Sig].
Arguments amend_D [Sig].
Arguments amend_P [Sig].
