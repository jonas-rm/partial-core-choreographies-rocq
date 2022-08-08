Require Import EPP.

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

Local Ltac eq_elim t t' H := case (eq_dec t t'); intro H;
  [ rewrite <- H in *; clear t' H | idtac].

Open Scope CC_scope.

(** Move me. *)
Lemma update_idempotent : forall (s:(State Pid Var Value)) p x,
  s[[p,x=>s p x]] [==] s.
Proof.
red; red; intros.
unfold update, Lupdate. case_eq (p =? p0).
2: intros; ESEr.
intro. rewrite eqb_eq in H; rewrite <- H; clear p0 H.
case_eq (x =? x0).
2: intros; ESEr.
intro. rewrite eqb_eq in H; rewrite <- H; auto.
Qed.

Notation Forget := (@forget Pid Value Var RecVar).

Lemma disjoint_p_rl_eq : forall p t t', Forget t = Forget t' ->
  disjoint_p_rl p t -> disjoint_p_rl p t'.
Proof.
intros. induction t, t'; inversion H; auto.
all: rewrite H2 in *; auto.
all: rewrite H3, H4 in *; auto.
Qed.

Lemma disjoint_eta_rl_eq : forall eta t t', Forget t = Forget t' ->
  disjoint_eta_rl _ eta t -> disjoint_eta_rl _ eta t'.
Proof.
intros. induction eta, t, t'; inversion H; auto.
all: rewrite H2 in *; auto.
all: rewrite H3, H4 in *; auto.
Qed.

(** For characterising traces created by amendment. *)

Inductive sel_subtrace : list (TransitionLabel Pid Value) -> list (TransitionLabel Pid Value) -> Prop :=
| ss_base l l' : Permutation l l' -> sel_subtrace l l'
| ss_cons t l l' l'' : sel_subtrace l l' -> Permutation (t::l') l'' -> sel_subtrace l l''
| ss_extra p q la l l' l'' : sel_subtrace l l' -> Permutation (TL_Sel p q la::l') l'' -> sel_subtrace l l''.

Lemma sel_subtrace_refl : forall ts, sel_subtrace ts ts.
Proof. constructor. auto. Qed.

Lemma sel_subtrace_cons : forall t ts ts',
  sel_subtrace ts ts' -> sel_subtrace (t::ts) (t::ts').
Proof.
intros. induction H.
- apply ss_base; auto.
- apply ss_cons with t0 (t::l'); auto.
  eapply Permutation_trans. apply perm_swap. auto.
- apply ss_extra with p q la (t::l'); auto.
  eapply Permutation_trans. apply perm_swap. auto.
Qed.

Lemma sel_subtrace_extra : forall p q l ts ts',
  sel_subtrace ts ts' -> sel_subtrace ts (TL_Sel p q l::ts').
Proof.
intros.
apply ss_extra with p q l ts'; auto.
Qed.

Lemma sel_subtrace_app : forall ts ts' ts'',
  sel_subtrace ts' ts'' -> sel_subtrace (ts++ts') (ts++ts'').
Proof.
induction ts; intros; auto.
apply sel_subtrace_cons; auto.
Qed.

Lemma sel_subtrace_perm' : forall ts ts' ts'',
  sel_subtrace ts ts' -> Permutation ts' ts'' -> sel_subtrace ts ts''.
Proof.
intros. induction H.
- apply ss_base. eapply perm_trans; eauto.
- apply ss_cons with t l'; auto.
  eapply Permutation_trans; eauto.
- apply ss_extra with p q la l'; auto.
  eapply Permutation_trans; eauto.
Qed.

Lemma sel_subtrace_perm : forall ts ts' ts'',
  sel_subtrace ts ts' -> Permutation ts'' ts -> sel_subtrace ts'' ts'.
Proof.
intros. induction H.
- apply ss_base. eapply perm_trans; eauto.
- apply ss_cons with t l'; auto.
- apply ss_extra with p q la l'; auto.
Qed.

Lemma sel_subtrace_trans : forall ts ts' ts'',
  sel_subtrace ts ts' -> sel_subtrace ts' ts'' -> sel_subtrace ts ts''.
Proof.
intros. induction H0.
- apply sel_subtrace_perm' with l; auto.
- apply ss_cons with t l'; auto.
- apply ss_extra with p q la l'; auto.
Qed.

Lemma sel_subtrace_swap : forall t t' ts ts',
  sel_subtrace ts (t :: ts') -> sel_subtrace (t' :: ts) (t :: t' :: ts').
Proof.
intros.
eapply sel_subtrace_perm'.
2: apply perm_swap.
apply sel_subtrace_cons; auto.
Qed.

Lemma sel_subtrace_perm_extra : forall t t' ts ts' p q l,
  sel_subtrace ts (t :: ts') -> sel_subtrace (t' :: ts) (t :: t' :: (TL_Sel p q l) :: ts').
Proof.
intros.
eapply sel_subtrace_trans. 2: apply sel_subtrace_swap.
apply sel_subtrace_cons; eauto.
apply sel_subtrace_cons, sel_subtrace_extra.
apply sel_subtrace_refl.
Qed.

Lemma sel_subtrace_app' : forall t ts ts' ts'',
  sel_subtrace ts (t::ts') -> sel_subtrace (ts''++ts) (t::ts''++ts').
Proof.
intros.
apply sel_subtrace_perm' with (ts''++t::ts').
apply sel_subtrace_app; auto.
apply Permutation_sym, Permutation_middle.
Qed.

Lemma sel_subtrace_app'' : forall t ts ts' ts'',
  sel_subtrace ts (ts' ++ ts'') -> sel_subtrace (t :: ts) (ts' ++ t :: ts'').
Proof.
intros.
eapply sel_subtrace_trans.
apply sel_subtrace_cons; eauto.
constructor. apply Permutation_middle.
Qed.

Lemma sel_subtrace_app_both : forall ts1 ts1' ts2 ts2',
  sel_subtrace ts1 ts1' -> sel_subtrace ts2 ts2' -> sel_subtrace (ts1++ts2) (ts1'++ts2').
Proof.
intros.
eapply sel_subtrace_trans.
apply sel_subtrace_app; eauto.
eapply sel_subtrace_perm.
2: apply Permutation_app_comm.
eapply sel_subtrace_perm'.
2: apply Permutation_app_comm.
apply sel_subtrace_app; auto.
Qed.

Variable Defs:DefSet Sig.

Section AmendOne.

Variable r:Pid.
Variable a:Ann.

(* Clean me *)
Fixpoint amend_1 (C:Choreography Sig) :=
match C with
| eta@a';; C' => eta@a';; (amend_1 C')
| If q ?? b Then C1 Else C2 =>
    let C1' := amend_1 C1 in let C2' := amend_1 C2 in
    let C' := If q ?? b Then C1' Else C2' in
    if (r =? q) then C'
    else if projectable_B_dec _ Defs (If q ?? b Then C1' Else C2') r then C'
         else If q ?? b Then (q --> r[left]@a;; C1') Else (q --> r[right]@a;; C2')
| RT_Call X ps C' => RT_Call X ps (amend_1 C')
| _ => C
end.

Definition amend_1_D : DefSet Sig :=
  fun X => (fst (Defs X),amend_1 (snd (Defs X))).

(** To avoid duplication of cases - I'd love an or... *)

Lemma amend_1_If : forall q b C1 C2,
  let C1' := amend_1 C1 in let C2' := amend_1 C2 in
  { amend_1 (If q ?? b Then C1 Else C2) = If q ?? b Then C1' Else C2' }
  + { amend_1 (If q ?? b Then C1 Else C2) = If q ?? b Then (q --> r[left]@a;; C1') Else (q --> r[right]@a;; C2') }.
Proof. intros; simpl. elim (r =? q); auto. elim projectable_B_dec; auto. Qed.

(** Amendment preserves well-formedness. *)

Lemma amend_1_no_self_comm : forall C,
  no_self_comm _ C -> no_self_comm _ (amend_1 C).
Proof.
induction C; auto; intros.
+ induction e. all: destroy H; split; auto.
+ simpl. case_eq (r =? t); intro.
  2: elim projectable_B_dec; intro.
  all: destroy H; repeat split; eauto.
  all: rewrite eqb_neq in H0; auto.
Qed.

Lemma amend_1_initial : forall C, initial C -> initial (amend_1 C).
Proof.
induction C; auto; intros.
elim (amend_1_If t t0 C1 C2); intro HA; rewrite HA.
all: destroy H; split; auto.
Qed.

Lemma amend_1_no_empty_ann : forall C,
  no_empty_ann _ C -> no_empty_ann _ (amend_1 C).
Proof.
induction C; auto; intros.
+ elim (amend_1_If t t0 C1 C2); intro HA; rewrite HA.
  all: destroy H; split; auto.
+ destroy H; split; auto.
Qed.

Lemma amend_1_Choreography_WF : forall C, Choreography_WF C -> Choreography_WF (amend_1 C).
Proof.
intros.
destroy H; split.
apply amend_1_no_self_comm; auto.
apply amend_1_no_empty_ann; auto.
Qed.

Lemma amend_1_within_Xs : forall C Xs,
  within_Xs Xs C -> within_Xs Xs (amend_1 C).
Proof.
induction C; auto; intros.
+ elim (amend_1_If t t0 C1 C2); intro HA; rewrite HA; clear HA.
  all: destroy H; split; eauto.
+ destroy H. split; auto.
Qed.

Lemma amend_1_consistent : forall C,
  consistent _ (Vars (Defs,C)) C -> consistent _ (Vars (amend_1_D,amend_1 C)) (amend_1 C).
Proof.
induction C; auto; intros.
+ elim (amend_1_If t t0 C1 C2); intro HA; rewrite HA; clear HA.
  all: destroy H; split; eauto.
+ destroy H. split; auto.
Qed.

Lemma amend_1_Program_WF : forall C Xs,
  Program_WF _ Xs (Defs,C) -> Program_WF _ Xs (amend_1_D,amend_1 C).
Proof.
intros.
destroy H. split. 2: split. 3: split.
+ apply amend_1_Choreography_WF; auto.
+ apply amend_1_within_Xs; auto.
+ apply amend_1_consistent; auto.
+ intros X HX. induction (H X HX) as (H3,(H4,(H5,H6))).
  repeat split.
  - apply amend_1_no_self_comm; auto.
  - apply amend_1_initial; auto.
  - unfold Vars, amend_1_D; simpl. auto.
  - apply amend_1_within_Xs; auto.
Qed.

(** Projectability of amendment. *)

Lemma amend_1_proj : forall C, projectable_B Sig Defs (amend_1 C) r.
Proof.
induction C; intros.
+ simpl.
  induction IHC as [B HB].
  induction e. all: eq_elim r t0 Hr.
  2: eq_elim r t2 Hr'. 5: eq_elim r t1 Hr'. 5: induction t2.
  all: try (eexists; econstructor; eauto; fail).
  exists (@Branching Sig' t0 (Some (t,B)) None). constructor; auto.
  exists (@Branching Sig' t0 None (Some (t,B))). constructor; auto.
+ induction IHC1 as [B1 HB1]. induction IHC2 as [B2 HB2].
  simpl. case_eq (r =? t); intro.
  2: elim projectable_B_dec; intros.
  - rewrite eqb_eq in H. rewrite <- H.
    eexists; econstructor; eauto.
  - rewrite eqb_neq in H.
    induction a0 as [B HB]. inversion HB. symmetry in H3; tauto.
    exists B. apply bproj_Cond' with B0 B3; auto.
  - rewrite eqb_neq in H.
    exists (@Branching Sig' t (Some (a,B1)) (Some (a,B2))).
    apply bproj_Cond' with (@Branching Sig' t (Some (a,B1)) None) (@Branching Sig' t None (Some (a,B2)));
      try constructor; auto.
    apply (merge_Branching_SNNS Sig').
+ elim (in_dec (@eq_dec Pid) r (fst (Defs t))).
  all: eexists. constructor; auto. apply bproj_Call_out; auto.
+ elim (in_dec (@eq_dec Pid) r l).
  eexists. constructor; auto.
  induction IHC as [B HB].
  eexists. apply bproj_RT_Call_out; eauto.
+ simpl. eexists; constructor.
Qed.

(** Completeness *)

Lemma amend_1_complete_1 : forall C s tl C' s', Choreography_WF C ->
  (Defs,C,s) --[tl]--> (Defs,C',s') ->
  exists tl' tlI tlF C'' s'',
       sel_subtrace tl' (tlI++tlF)
    /\ (Defs,C',s') --[tl']-->* (Defs,C'',s'')
    /\ (amend_1_D,amend_1 C,s) --[tlI ++ tl::tlF]-->* (amend_1_D,amend_1 C'',s'').
Proof.
Local Ltac IHElim IHC HC H tl' tlI CI sI tl0 C0 s0 tlF CF sF H1 H2 H3 H4 H5 H6 := 
    induction (IHC _ _ _ _ HC H) as
    [tl' [tlI [CI [sI [tl0 [C0 [s0 [tlF [CF [sF [H1 [H2 [H3 [H4 [H5 H6] ] ] ] ] ] ] ] ] ] ] ] ] ] ]; clear IHC.
intros. rename H into HC, H0 into H.
assert (exists tl' tlI CI sI tl0 C0 s0 tlF CF sF,
       sel_subtrace tl' (tlI++tlF)
    /\ tl = forget tl0
    /\ (Defs,C',s') --[tl']-->* (Defs,CF,sF)
    /\ (amend_1_D,amend_1 C,s) --[tlI]-->* (amend_1_D,CI,sI)
    /\ <<CI,sI>> --[tl0,amend_1_D]--> <<C0,s0>>
    /\ (amend_1_D,C0,s0) --[tlF]-->* (amend_1_D,amend_1 CF,sF)).
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
    exists (RL_Com p v q x), (amend_1 C), s'.
    exists nil, C, s'.
    repeat split; eauto. apply sel_subtrace_refl.
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
    * apply sel_subtrace_cons; auto.
    * econstructor; eauto. unfold tlS; rewrite Hv.
      repeat constructor; auto.
    * econstructor; eauto. repeat constructor; auto.
+ rename t0 into p, t1 into q, t2 into l, t into a'.
  inversion H.
  - (* Sel *)
    rewrite <- H7 in *.
    clear s'0 H8 C' H7 tl H6 s0 H0 C0 H5 a0 H3 l0 H2 q0 H1 p0 H H4.
    simpl. exists nil, nil; do 2 eexists.
    exists (RL_Sel p q l), (amend_1 C), s'.
    exists nil, C, s'.
    repeat split; eauto. apply sel_subtrace_refl.
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
    * apply sel_subtrace_cons; auto.
    * econstructor; eauto. repeat constructor; auto.
    * econstructor; eauto. repeat constructor; auto.
+ rename t into p, t0 into b.
  inversion H.
  - (* Then *)
    rewrite <- H6 in *.
    clear s'0 H7 C' H6 tl H5 s0 H1 C3 H3 C0 H2 b0 H0 p0 H H4.
    (* did we amend? *)
    elim (amend_1_If p b C1 C2); intro HA; rewrite HA.
    * exists nil, nil; do 2 eexists.
      exists (@RL_Cond Pid Value Var RecVar p), (amend_1 C1), s'.
      exists nil, C1, s'.
      repeat split; try constructor; eauto.
      all: try ESEr. erewrite eval_eq; eauto. ESEs.
    * exists nil, nil; do 2 eexists.
      exists (@RL_Cond Pid Value Var RecVar p), (p-->r[left]@a;; amend_1 C1), s'.
      exists (@Forget (RL_Sel p r left)::nil), C1, s'.
      repeat split. apply sel_subtrace_extra, sel_subtrace_refl.
      all: repeat constructor; auto.
      repeat econstructor.
  - (* Else *)
    rewrite <- H6 in *.
    clear s'0 H7 C' H6 tl H5 s0 H1 C3 H3 C0 H2 b0 H0 p0 H H4.
    (* did we amend? *)
    elim (amend_1_If p b C1 C2); intro HA; rewrite HA.
    * exists nil, nil; do 2 eexists.
      exists (@RL_Cond Pid Value Var RecVar p), (amend_1 C2), s'.
      exists nil, C2, s'.
      repeat split; try constructor; eauto.
      all: try ESEr. erewrite eval_eq; eauto. ESEs.
    * exists nil, nil; do 2 eexists.
      exists (@RL_Cond Pid Value Var RecVar p), (p-->r[right]@a;; amend_1 C2), s'.
      exists (@Forget (RL_Sel p r right)::nil), C2, s'.
      repeat split. apply sel_subtrace_extra, sel_subtrace_refl.
      all: repeat constructor; auto.
      repeat econstructor.
  - (* Delay *)
    rewrite <- H6 in *.
    clear s'0 H7 t H5 s0 H2 C3 H3 C0 H1 b0 H0 p0 H H6 H4.
    IHElim IHC1 (Choreography_WF_Then _ _ _ _ _ HC) H9 tl'1 tl1I C1I s1I tl01 C01 s01 tl1F C1F s1F Htrace1 Hforget1 H1' H1I H01 H1F.
    IHElim IHC2 (Choreography_WF_Else _ _ _ _ _ HC) H10 tl'2 tl2I C2I s2I tl02 C02 s02 tl2F C2F s2F Htrace2 Hforget2 H2' H2I H02 H2F.
    generalize (CCC_To_disjoint_beval _ _ _ _ _ _ _ b _ H8 H9); intro Hb.
    case_eq (eval_on_state BEv b s p); intro Hb'.
    all: elim (amend_1_If p b C1 C2); intro HA.
    all: rewrite HA in *; clear HA.
    * (* Then, no amend *)
      set (tl0 := @RL_Cond Pid Value Var RecVar p).
      exists (Forget tl0::tl'1).
      exists (Forget tl0::tl1I), C1I, s1I.
      exists tl01, C01, s01.
      exists tl1F, C1F, s1F.
      repeat split; auto.
      simpl. apply sel_subtrace_cons; auto.
      econstructor; eauto. repeat constructor. rewrite <- Hb; auto.
      econstructor; eauto. repeat constructor; auto.
    * (* Then, amend *)
      set (tl0 := @RL_Cond Pid Value Var RecVar p).
      set (tl0' := @RL_Sel Pid Value Var RecVar p r left).
      exists (Forget tl0::tl'1).
      exists (Forget tl0::Forget tl0'::tl1I), C1I, s1I.
      exists tl01, C01, s01.
      exists tl1F, C1F, s1F.
      repeat split; auto.
      simpl. apply sel_subtrace_cons, sel_subtrace_extra; auto.
      econstructor; eauto. repeat constructor. rewrite <- Hb; auto.
      econstructor; eauto. repeat constructor; auto.
      econstructor; eauto. repeat constructor; auto.
    * (* Else, no amend *)
      set (tl0 := @RL_Cond Pid Value Var RecVar p).
      exists (Forget tl0::tl'2).
      exists (Forget tl0::tl2I), C2I, s2I.
      exists tl02, C02, s02.
      exists tl2F, C2F, s2F.
      repeat split; auto.
      simpl. apply sel_subtrace_cons; auto.
      econstructor; eauto. repeat constructor. rewrite <- Hb; auto.
      econstructor; eauto. repeat constructor; auto.
    * (* Else, no amend *)
      set (tl0 := @RL_Cond Pid Value Var RecVar p).
      set (tl0' := @RL_Sel Pid Value Var RecVar p r right).
      exists (Forget tl0::tl'2).
      exists (Forget tl0::Forget tl0'::tl2I), C2I, s2I.
      exists tl02, C02, s02.
      exists tl2F, C2F, s2F.
      repeat split; auto.
      simpl. apply sel_subtrace_cons, sel_subtrace_extra; auto.
      econstructor; eauto. repeat constructor. rewrite <- Hb; auto.
      econstructor; eauto. 2: econstructor; eauto.
      2: repeat constructor; auto. repeat constructor; auto.
+ rename t into X. inversion H.
  - (* Local *)
    rewrite <- H6 in *.
    clear s'0 H7 C' H6 tl H5 s0 H4 X0 H0 H.
    simpl. exists nil, nil; do 2 eexists.
    exists (RL_Call X p), (amend_1 (snd (Defs X))), s'.
    exists nil, (snd (Defs X)), s'.
    repeat split; eauto. apply sel_subtrace_refl.
    all: constructor; simpl; eauto; ESEr.
  - (* Call *)
    rewrite <- H5 in *.
    clear s'0 H7 C' H6 tl H5 s0 H4 X0 H0 H.
    simpl. exists nil, nil; do 2 eexists.
    exists (RL_Call X p); eexists; exists s'.
    exists nil; eexists; exists s'.
    repeat split; eauto. apply sel_subtrace_refl.
    all: constructor; simpl; eauto; ESEr.
+ rename t into X. inversion H.
  - (* Delay *)
    rewrite <- H5, <- H1 in *.
    clear s'0 H6 C' H5 t H4 s0 H2 C0 H3 H X0 H0 l H1. rename C'0 into C'.
    IHElim IHC (Choreography_WF_Call_1 _ _ _ _ HC) H8 tl' tlI CI sI tl0 C0 s0 tlF CF sF Htrace Hforget H' HI H0 HF.
    induction HC as [HC [Hps HA] ]. clear HC HA.
    induction (RT_Call_reduce _ ps Hps) as [tlR HR].
    exists (tlR++tl'). exists (tlR++tlI), CI, sI.
    exists tl0, C0, s0. exists tlF, CF, sF.
    repeat split; auto.
    * rewrite <- app_assoc. apply sel_subtrace_app; auto.
    * eapply CCT_Trans; eauto.
    * eapply CCT_Trans; eauto.
  - (* Enter *)
    rewrite <- H6, <- H1 in *.
    clear s'0 H7 C' H6 tl H5 s0 H4 C0 H2 H X0 H0 l H1.
    simpl. exists nil, nil; do 2 eexists.
    exists (RL_Call X p), (RT_Call X (ps[\]p) (amend_1 C)), s'.
    exists nil; eexists; exists s'.
    repeat split; eauto. apply sel_subtrace_refl.
    all: constructor; eauto; ESEr.
  - (* Finish *)
    rewrite <- H6, <- H1 in *.
    clear s'0 H7 C' H6 tl H5 s0 H4 C0 H2 H X0 H0 l H1.
    simpl. exists nil, nil; do 2 eexists.
    exists (RL_Call X p), (amend_1 C), s'.
    exists nil, C, s'.
    repeat split; eauto. apply sel_subtrace_refl.
    all: constructor; eauto; ESEr.
+ inversion H.
Qed.

Lemma amend_1_complete_1' : forall C s tl C' s', Choreography_WF C ->
  (Defs,C,s) --[tl]--> (Defs,C',s') ->
  exists tl' tl'' C'' s'',
       sel_subtrace (tl::tl') tl''
    /\ (Defs,C',s') --[tl']-->* (Defs,C'',s'')
    /\ (amend_1_D,amend_1 C,s) --[tl'']-->* (amend_1_D,amend_1 C'',s'').
Proof.
intros.
elim (amend_1_complete_1 C s tl C' s'); auto.
intros. induction H1 as (tlI,(tlF,(C'',(s'',(H1,(H2,H3)))))).
do 4 eexists. repeat split; eauto.
apply sel_subtrace_app''; auto.
Qed.

Lemma amend_1_complete_many : forall C s tl C' s' Xs, Program_WF _ Xs (Defs,C) ->
  (Defs,C,s) --[tl]-->* (Defs,C',s') ->
  exists tl' tl'' C'' s'',
       sel_subtrace (tl ++ tl') tl''
    /\ (Defs,C',s') --[tl']-->* (Defs,C'',s'')
    /\ (amend_1_D,amend_1 C,s) --[tl'']-->* (amend_1_D,amend_1 C'',s'').
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
  elim (amend_1_complete_1' C s t C'' s''); auto.
  2: elim H; auto.
  intros tl0 [t0 [C0 [s0 [Hsub0 [Htl0 Htl0IF] ] ] ] ].
  induction (diamond_4b _ _ _ _ _ _ _ _ _ H2 Htl0) as [ [D C2] [tl' [tl0' [s2a [s2b [HC' [HC0 [Hs [Hperm [Hlen1 Hlen2] ] ] ] ] ] ] ] ] ].
  generalize (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ _ HC'). intro H'; rewrite <- H' in *; clear D H'.
  generalize (CCC_To_Program_WF _ _ _ _ _ _ _ H H1). intro HP''.
  generalize (CCC_ToStar_Program_WF _ _ _ _ _ _ _ HP'' H2). intro HP'.
  generalize (CCC_ToStar_Program_WF _ _ _ _ _ _ _ HP' HC'). intro HP2.
  generalize (CCC_ToStar_Program_WF _ _ _ _ _ _ _ HP'' Htl0). intro HP0.
  elim (IHn C0 s0 tl0' C2 s2b); auto.
  intros tl1 [t1 [C1 [s1 [Hsub1 [Htl1 Htl1IF] ] ] ] ].
  2: etransitivity; eauto.
  exists (tl' ++ tl1), (t0 ++ t1), C1, s1.
  repeat split.
  - simpl. eapply sel_subtrace_trans.
    2: apply sel_subtrace_app_both; eauto.
    simpl. apply sel_subtrace_cons.
    repeat rewrite app_assoc.
    constructor. apply Permutation_app; auto.
  - eapply CCT_Trans; eauto.
    apply CCP_ToStar_eq with s2b s1. ESEs. ESEr. auto.
  - eapply CCT_Trans; eauto.
Qed.

(** Soundness *)

Lemma amend_1_sound_1 : forall C s tl C' s', Choreography_WF C ->
  (amend_1_D, amend_1 C,s) --[tl]--> (amend_1_D,C',s') ->
  exists tl' tl'' C'' s'',
  (amend_1_D,C',s') --[tl']-->* (amend_1_D, amend_1 C'',s'')
  /\ (Defs,C,s) --[tl'']-->* (Defs,C'',s'') /\ sel_subtrace tl'' (tl::tl').
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
    * apply sel_subtrace_refl.
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
    * apply sel_subtrace_swap; auto.
+ rename t1 into p, t2 into q, t3 into l, t0 into a'.
  inversion H.
  - (* Sel *)
    rewrite <- H6 in *.
    clear s'0 H8 C' H7 t H6 s0 H1 C0 H5 a0 H4 l0 H3 q0 H2 p0 H H0.
    exists nil, (Forget (RL_Sel p q l) :: nil), C, s'. repeat split.
    * repeat constructor.
    * econstructor; eauto. 2: apply CCT_Refl. repeat constructor; auto.
    * apply sel_subtrace_refl.
  - (* Delay *)
    clear s'0 H6 C' H5 t0 H4 s0 H2 C0 H3 ann H1 eta H H0.
    induction H7 as [Hp Hq].
    IHElim' IHC (Choreography_WF_eta _ _ _ _ HC) H8 tl' tl'' C'' s'' Htl' Htl'' Hsub.
    set (tlS := @RL_Sel Pid Value Var RecVar p q l).
    exists (Forget tlS::tl'), (Forget tlS::tl''), C'', s''.
    repeat split; auto.
    * econstructor; eauto. repeat constructor.
    * econstructor; eauto. repeat constructor.
    * apply sel_subtrace_swap; auto.
+ rename t0 into p, t1 into b.
  elim (amend_1_If p b C1 C2); intro HA; rewrite HA in *; clear HA.
  all: inversion H.
  - (* Then *)
    rewrite <- H5, <- H6 in *.
    clear s'0 H7 C' H6 t H5 s0 H2 C3 H4 C0 H3 b0 H1 p0 H0.
    exists nil, (Forget (RL_Cond p)::nil), C1, s'. repeat split; auto.
    * apply CCT_Refl.
    * econstructor. 2: apply CCT_Refl. repeat constructor; eauto.
    * apply sel_subtrace_refl.
  - (* Else *)
    rewrite <- H5, <- H6 in *.
    clear s'0 H7 C' H6 t H5 s0 H2 C3 H4 C0 H3 b0 H1 p0 H0.
    exists nil, (Forget (RL_Cond p)::nil), C2, s'. repeat split; auto.
    * apply CCT_Refl.
    * econstructor. 2: apply CCT_Refl. repeat constructor; eauto.
    * apply sel_subtrace_refl.
  - (* Delay *)
    rewrite <- H6 in *.
    clear s'0 H7 C' H6 t0 H5 s0 H3 C3 H4 C0 H2 b0 H1 p0 H0.
    generalize (CCC_To_disjoint_beval _ _ _ _ _ _ _ b _ H8 H9); intro Hb.
    case_eq (eval_on_state BEv b s p); intro Hb'.
    * IHElim' IHC1 (Choreography_WF_Then _ _ _ _ _ HC) H9 tl' tl'' C'' s'' Htl' Htl'' Hsub.
      exists (Forget (RL_Cond p)::tl'), (Forget (RL_Cond p)::tl''), C'', s''.
      repeat split.
      econstructor; eauto. repeat constructor; auto. rewrite <- Hb; auto.
      econstructor; eauto. repeat constructor; auto.
      apply sel_subtrace_swap; auto.
    * IHElim' IHC2 (Choreography_WF_Else _ _ _ _ _ HC) H10 tl' tl'' C'' s'' Htl' Htl'' Hsub.
      exists (Forget (RL_Cond p)::tl'), (Forget (RL_Cond p)::tl''), C'', s''.
      repeat split.
      econstructor; eauto. repeat constructor; auto. rewrite <- Hb; auto.
      econstructor; eauto. repeat constructor; auto.
      apply sel_subtrace_swap; auto.
  - (* Then + Amend *)
    rewrite <- H5, <- H6 in *.
    clear s'0 H7 C' H6 t H5 s0 H2 C3 H4 C0 H3 b0 H1 p0 H0.
    exists (Forget (RL_Sel p r left)::nil), (Forget (RL_Cond p)::nil), C1, s'. repeat split; auto.
    * econstructor; repeat constructor.
    * econstructor. 2: apply CCT_Refl. repeat constructor; auto.
    * apply sel_subtrace_cons, sel_subtrace_extra, sel_subtrace_refl.
  - (* Else + Amend *)
    rewrite <- H5, <- H6 in *.
    clear s'0 H7 C' H6 t H5 s0 H2 C3 H4 C0 H3 b0 H1 p0 H0.
    exists (Forget (RL_Sel p r right)::nil), (Forget (RL_Cond p)::nil), C2, s'. repeat split; auto.
    * econstructor; repeat constructor.
    * econstructor. 2: apply CCT_Refl. repeat constructor; auto.
    * apply sel_subtrace_cons, sel_subtrace_extra, sel_subtrace_refl.
  - (* Delay + Amend *)
    rewrite <- H6 in *.
    clear s'0 H7 C' H6 t0 H5 s0 H3 C3 H4 C0 H2 b0 H1 p0 H0.
    generalize (CCC_To_disjoint_beval _ _ _ _ _ _ _ b _ H8 H9); intro Hb.
    inversion H9; inversion H10.
    1: rewrite <- H6 in H19; inversion H19.
    1: rewrite <- H6 in H20; simpl in H20; tauto.
    1: rewrite <- H18 in H7; simpl in H7; tauto.
    rewrite <- H17, <- H5 in *; rename C' into C'1, C'0 into C'2.
    clear s'1 H18 C2' H17 t1 H16 s1 H14 C0 H15 ann0 H13 eta0 H12.
    clear s'0 H6 C1' H5 t0 H4 s0 H2 C H3 ann H1 eta H0.
    case_eq (eval_on_state BEv b s p); intro Hb'.
    * IHElim' IHC1 (Choreography_WF_Then _ _ _ _ _ HC) H11 tl' tl'' C'' s'' Htl' Htl'' Hsub.
      exists (Forget (RL_Cond p)::Forget (RL_Sel p r left)::tl'), (Forget (RL_Cond p)::tl''), C'', s''.
      repeat split.
      econstructor; eauto. repeat constructor; auto. rewrite <- Hb; auto.
      econstructor; eauto. repeat constructor; auto.
      econstructor; eauto. repeat constructor; auto.
      apply sel_subtrace_perm_extra; auto.
    * IHElim' IHC2 (Choreography_WF_Else _ _ _ _ _ HC) H20 tl' tl'' C'' s'' Htl' Htl'' Hsub.
      exists (Forget (RL_Cond p)::Forget (RL_Sel p r right)::tl'), (Forget (RL_Cond p)::tl''), C'', s''.
      repeat split.
      econstructor; eauto. constructor. apply C_Else'. rewrite <- Hb; auto.
      econstructor; eauto. repeat constructor; auto.
      econstructor; eauto. repeat constructor; auto.
      apply sel_subtrace_perm_extra; auto.
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
    repeat split; eauto. 3: apply sel_subtrace_refl.
    apply CCT_Refl.
    econstructor. 2: apply CCT_Refl. repeat constructor; auto.
+ rename t0 into X. inversion H.
  - (* Delay *)
    rewrite <- H5, <- H1 in *.
    clear s'0 H6 C' H5 t0 H4 s0 H2 C0 H3 H X0 H0 l H1. rename C'0 into C'.
    IHElim' IHC (Choreography_WF_Call_1 _ _ _ _ HC) H8 tl' tl'' C'' s'' Htl' Htl'' Hsub.
    induction HC as [HC [Hps HA] ]; clear HC HA.
    induction (RT_Call_reduce _ ps Hps) as [tlR HR].
    exists (tlR++tl'), (tlR++tl''), C'', s''.
    repeat split; auto.
    * eapply CCT_Trans; eauto.
    * eapply CCT_Trans; eauto.
    * apply sel_subtrace_app'; auto.
  - (* Enter *)
    rewrite <- H5, <- H1 in *.
    clear s'0 H7 C' H6 t H5 s0 H4 C0 H2 H X0 H0 l H1.
    exists nil, (Forget (RL_Call X p)::nil), (RT_Call X (ps[\]p) C), s'.
    repeat split; eauto. 3: apply sel_subtrace_refl.
    apply CCT_Refl.
    econstructor. 2: apply CCT_Refl. repeat constructor; auto.
  - (* Finish *)
    rewrite <- H5, <- H1 in *.
    clear s'0 H7 C' H6 t H5 s0 H4 C0 H2 H X0 H0 l H1.
    exists nil, (Forget (RL_Call X p)::nil), C, s'.
    repeat split; eauto. 3: apply sel_subtrace_refl.
    apply CCT_Refl.
    econstructor. 2: apply CCT_Refl. repeat constructor; auto.
+ inversion H.
Qed.

Lemma amend_1_sound_many : forall C s tl C' s' Xs, Program_WF _ Xs (Defs,C) ->
  (amend_1_D, amend_1 C,s) --[tl]-->* (amend_1_D, C',s') ->
  exists tl' tl'' C'' s'',
  (amend_1_D,C',s') --[tl']-->* (amend_1_D, amend_1 C'',s'')
  /\ (Defs,C,s) --[tl'']-->* (Defs,C'',s'') /\ sel_subtrace tl'' (tl++tl').
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
  constructor; auto; ESEr. apply sel_subtrace_refl.
+ case_eq tl; intros.
  1: { (* repeat... *)
    rewrite H1 in *; clear tl H1.
    inversion H0. rewrite <- H2 in *.
    exists nil, nil, C, s'.
    repeat split; simpl; auto. apply CCT_Refl.
    constructor; auto; ESEr. apply sel_subtrace_refl.
  }
  rewrite H1 in *; clear tl H1.
  simpl in Hn. apply le_S_n in Hn. rename l into tl.
  inversion_clear H0. induction c2 as [ [D C''] s''].
  generalize (CCP_To_Defs_stable _ _ _ _ _ _ _ _ H1). intro H'; rewrite <- H' in *; clear D H'.
  elim (amend_1_sound_1 C s t C'' s''); auto.
  2: elim H; auto.
  intros tl0 [t0 [C0 [s0 [Htl0 [Hsub0 Htl0IF] ] ] ] ].
  induction (diamond_4b _ _ _ _ _ _ _ _ _ H2 Htl0) as [ [D C2] [tl' [tl0' [s2a [s2b [HC' [HC0 [Hs [Hperm [Hlen1 Hlen2] ] ] ] ] ] ] ] ] ].
  generalize (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ _ HC'). intro H'; rewrite <- H' in *; clear D H'.
  generalize (CCC_To_Program_WF _ _ _ _ _ _ _ (amend_1_Program_WF _ _ H) H1). intro HP''.
  generalize (CCC_ToStar_Program_WF _ _ _ _ _ _ _ HP'' H2). intro HP'.
  generalize (CCC_ToStar_Program_WF _ _ _ _ _ _ _ HP' HC'). intro HP2.
  generalize (CCC_ToStar_Program_WF _ _ _ _ _ _ _ HP'' Htl0). intro HP0.
  elim (IHn C0 s0 tl0' C2 s2b); auto.
  intros tl1 [t1 [C1 [s1 [Hsub1 [Htl1 Htl1IF] ] ] ] ].
  2: etransitivity; eauto.
  exists (tl' ++ tl1), (t0 ++ t1), C1, s1.
  repeat split.
  - eapply CCT_Trans; eauto.
    apply CCP_ToStar_eq with s2b s1. ESEs. ESEr. auto.
  - eapply CCT_Trans; eauto.
  - simpl. eapply sel_subtrace_trans.
    apply sel_subtrace_app_both; eauto.
    simpl. apply sel_subtrace_cons.
    repeat rewrite app_assoc.
    constructor. apply Permutation_sym, Permutation_app; auto.
  - eapply CCC_ToStar_Program_WF. 2: eauto. auto.
Qed.

End AmendOne.

Section AmendMany.

Variable a:Ann.

Fixpoint amend_ps (ps:list Pid) (C:Choreography Sig) :=
  match ps with
  | nil => C
  | p::ps' => amend_ps ps' (amend_1 p a C)
  end.

Variable ps : list Pid.

Notation Amend := (amend_ps ps).

Definition amend_ps_D : DefSet Sig :=
  fun X => (fst (Defs X),Amend (snd (Defs X))).

Lemma amend_ps_complete : forall C s tl C' s' Xs, Program_WF _ Xs (Defs,C) ->
  (Defs,C,s) --[tl]-->* (Defs,C',s') ->
  exists tl' tl'' C'' s'',
       sel_subtrace (tl ++ tl') tl''
    /\ (Defs,C',s') --[tl']-->* (Defs,C'',s'')
    /\ (amend_ps_D,Amend C,s) --[tl'']-->* (amend_ps_D,Amend C'',s'').
Proof.
unfold amend_ps_D. induction ps; simpl; intros.
+ exists nil, tl, C', s'.
  repeat split; auto.
  rewrite app_nil_r; apply sel_subtrace_refl.
  apply CCT_Refl.
  change C with (Main (Defs,C)). change C' with (Main (Defs,C')).
  apply CCP_ToStar_Defs_eq; simpl; auto.
  intro. induction (Defs X); auto.
+ rename a0 into p.
  elim (amend_1_complete_many p a C s tl C' s' Xs); auto.
  intros tl0 [t0 [C0 [s0 [Hsub0 [Htl0 Htl0IF] ] ] ] ].
  elim (IHl


  induction (diamond_4b _ _ _ _ _ _ _ _ _ H2 Htl0) as [ [D C2] [tl' [tl0' [s2a [s2b [HC' [HC0 [Hs [Hperm [Hlen1 Hlen2] ] ] ] ] ] ] ] ] ].
  generalize (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ _ HC'). intro H'; rewrite <- H' in *; clear D H'.
  generalize (CCC_To_Program_WF _ _ _ _ _ _ _ H H1). intro HP''.
  generalize (CCC_ToStar_Program_WF _ _ _ _ _ _ _ HP'' H2). intro HP'.
  generalize (CCC_ToStar_Program_WF _ _ _ _ _ _ _ HP' HC'). intro HP2.
  generalize (CCC_ToStar_Program_WF _ _ _ _ _ _ _ HP'' Htl0). intro HP0.
  elim (IHn C0 s0 tl0' C2 s2b); auto.
  intros tl1 [t1 [C1 [s1 [Hsub1 [Htl1 Htl1IF] ] ] ] ].
  2: etransitivity; eauto.
  exists (tl' ++ tl1), (t0 ++ t1), C1, s1.
  repeat split.
  - simpl. eapply sel_subtrace_trans.
    2: apply sel_subtrace_app_both; eauto.
    simpl. apply sel_subtrace_cons.
    repeat rewrite app_assoc.
    constructor. apply Permutation_app; auto.
  - eapply CCT_Trans; eauto.
    apply CCP_ToStar_eq with s2b s1. ESEs. ESEr. auto.
  - eapply CCT_Trans; eauto.
Qed.





End AmendMany.

End Amendment.
