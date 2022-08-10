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

Open Scope SP_scope.

Lemma epp_EmptyNet' : forall Xs ps P HP N, Program_WF Sig Xs P ->
  N (==) nnil -> N (>>) Net (epp Xs ps P HP) -> Main P = CC.End.
Proof.
intros. rename H into HWF, H1 into HN, H0 into HN'.
induction P as (D,C).
assert (projectable_C D C ps) as HC.
1: inversion HP; auto.
generalize (epp_C_char _ _ _ _ _ HP HC); intro.
destruct C; auto. induction e.
1,2: rename t0 into p. 3: rename t into p.
1,2,3: specialize (HN p); rewrite HN', H in HN; simpl in HN.
- rewrite epp_C_Com_p with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ _ HC) in HN.
  inversion HN; auto.
  inversion HP. inversion_clear H1. inversion_clear H3.
  apply H1; simpl. rewrite set_union_iff; simpl; auto.
- rewrite epp_C_Sel_p with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ _ HC) in HN.
  inversion HN; auto.
  inversion HP. inversion_clear H1. inversion_clear H3.
  apply H1; simpl. rewrite set_union_iff; simpl; auto.
- rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ _ HC)
        (HC2:=projectable_C_inv_Else _ _ _ _ _ _ _ HC) in HN.
  inversion HN; auto.
  inversion HP. inversion_clear H1. inversion_clear H3.
  apply H1; simpl. repeat rewrite set_union_iff; simpl; auto.
- generalize (Program_WF_Main_within_Xs _ _ _ HWF); intro.
  simpl in H0.
  generalize (Program_WF_Vars _ _ _ HWF t H0); intros.
  case_eq (Vars (D,CC.Call t) t); intro. tauto.
  rename t0 into p. intros. clear H1.
  specialize (HN p). rewrite HN', H, epp_C_Call in HN.
  3: { unfold Vars in H2. simpl in H2.
       rewrite H2; simpl; auto. }
  2: { inversion_clear HP. destroy H3.
       apply H6 with t; simpl; auto.
       unfold Vars in H2. simpl in H2.
       rewrite H2; simpl; auto. }
  inversion HN; auto.
- apply Program_WF_Main, Choreography_WF_no_empty_ann in HWF.
  induction HWF as [H2 H2'].
  case_eq l; intro. tauto.
  rename t0 into p. intros.
  specialize (HN p). rewrite HN', H, epp_C_RT_Call in HN.
  3: rewrite H0; simpl; auto.
  inversion HN; auto.
  apply HP; simpl. rewrite set_union_iff, H0; simpl; auto.
Qed.

Lemma epp_EmptyNet : forall Xs ps P HP, Program_WF Sig Xs P ->
  nnil (>>) Net (epp Xs ps P HP) -> Main P = CC.End.
Proof.
intros.
apply epp_EmptyNet' with (N:=nnil) (HP:=HP); auto.
apply Network_eq_refl.
Qed.

Close Scope SP_scope.

(** For characterising traces created by amendment. *)

Inductive sel_subtrace : list (TransitionLabel Pid Value) -> list (TransitionLabel Pid Value) -> Prop :=
| ss_base l l' : Permutation l l' -> sel_subtrace l l'
(* | ss_cons t l l' l'' : sel_subtrace l l' -> Permutation (t::l') l'' -> sel_subtrace l l'' *)
| ss_extra p q la l l' l'' : sel_subtrace l l' -> Permutation (TL_Sel p q la::l') l'' -> sel_subtrace l l''.

Lemma sel_subtrace_refl : forall ts, sel_subtrace ts ts.
Proof. constructor. auto. Qed.

Lemma sel_subtrace_cons : forall t ts ts',
  sel_subtrace ts ts' -> sel_subtrace (t::ts) (t::ts').
Proof.
intros. induction H.
- apply ss_base; auto.
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
- apply ss_extra with p q la l'; auto.
  eapply Permutation_trans; eauto.
Qed.

Lemma sel_subtrace_perm : forall ts ts' ts'',
  sel_subtrace ts ts' -> Permutation ts'' ts -> sel_subtrace ts'' ts'.
Proof.
intros. induction H.
- apply ss_base. eapply perm_trans; eauto.
- apply ss_extra with p q la l'; auto.
Qed.

Lemma sel_subtrace_trans : forall ts ts' ts'',
  sel_subtrace ts ts' -> sel_subtrace ts' ts'' -> sel_subtrace ts ts''.
Proof.
intros. induction H0.
- apply sel_subtrace_perm' with l; auto.
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

Section Amend.

Variable Defs:DefSet Sig.
Variable a:Ann.

Fixpoint up_list p b ps C1 C2 : list Pid :=
  match ps with
  | nil => nil
  | r :: ps' => let ps'' := up_list p b ps' C1 C2 in
                if (r =? p) then ps''
                else if projectable_B_dec _ Defs (If p ?? b Then C1 Else C2) r
                then ps'' else (r :: ps'')
  end.

Fixpoint add_sels p l ps C : Choreography Sig :=
  match ps with
  | nil => C
  | r :: ps' => p --> r[l]@a;; add_sels p l ps' C
  end.

Fixpoint amend (ps:list Pid) (C:Choreography Sig) :=
match C with
| eta@a';; C' => eta@a';; (amend ps C')
| If p ?? b Then C1 Else C2 =>
    let l := up_list p b ps (amend ps C1) (amend ps C2) in
    If p ?? b Then (add_sels p left l (amend ps C1)) Else (add_sels p right l (amend ps C2))
| RT_Call X l C' => RT_Call X l (amend ps C')
| _ => C
end.

Definition amend_D ps : DefSet Sig :=
  fun X => (fst (Defs X), amend ps (snd (Defs X))).

(** To avoid duplication of cases - I'd love an or... *)

Lemma up_list_If : forall p b r ps C1 C2,
  { up_list p b (r::ps) C1 C2 = up_list p b ps C1 C2 }
  + { up_list p b (r::ps) C1 C2 = r :: up_list p b ps C1 C2 }.
Proof. intros; simpl. elim (r =? p); auto. elim projectable_B_dec; auto. Qed.

(** Amendment preserves well-formedness. *)

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

Lemma amend_Choreography_WF : forall ps C, Choreography_WF C -> Choreography_WF (amend ps C).
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

Lemma add_sels_consistent : forall p l ps C,
  consistent _ (Vars (Defs,C)) C -> consistent _ (Vars (amend_D ps,add_sels p l ps C)) (add_sels p l ps C).
Proof. induction ps; auto. Qed.

Lemma amend_consistent : forall ps C,
  consistent _ (Vars (Defs,C)) C -> consistent _ (Vars (amend_D ps,amend ps C)) (amend ps C).
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

(** Completeness *)

Lemma add_sels_reduce : forall D p l ps C s,
  exists tl, sel_subtrace nil tl /\
    (D,add_sels p l ps C,s) --[tl]-->* (D,C,s).
Proof.
induction ps; simpl; intros.
+ exists nil. split. apply sel_subtrace_refl. apply CCT_Refl.
+ induction (IHps C s) as [tl [Hsub Htl] ].
  exists (@forget Pid Value Var RecVar (RL_Sel p a0 l)::tl).
  split. apply sel_subtrace_extra; auto.
  econstructor; eauto. repeat constructor; auto.
Qed.

Lemma amend_complete_1 : forall ps C s tl C' s', Choreography_WF C ->
  (Defs,C,s) --[tl]--> (Defs,C',s') ->
  exists tl' tlI tlF C'' s'',
       sel_subtrace tl' (tlI++tlF)
    /\ (Defs,C',s') --[tl']-->* (Defs,C'',s'')
    /\ (amend_D ps,amend ps C,s) --[tlI ++ tl::tlF]-->* (amend_D ps,amend ps C'',s'').
Proof.
Local Ltac IHElim IHC HC H tl' tlI CI sI tl0 C0 s0 tlF CF sF H1 H2 H3 H4 H5 H6 := 
    induction (IHC _ _ _ _ HC H) as
    [tl' [tlI [CI [sI [tl0 [C0 [s0 [tlF [CF [sF [H1 [H2 [H3 [H4 [H5 H6] ] ] ] ] ] ] ] ] ] ] ] ] ] ]; clear IHC.
intros. rename H into HC, H0 into H.
assert (exists tl' tlI CI sI tl0 C0 s0 tlF CF sF,
       sel_subtrace tl' (tlI++tlF)
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
    exists (RL_Sel p q l), (amend ps C), s'.
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
      ++ simpl. apply sel_subtrace_cons.
         rewrite <- (app_nil_l tl'1), <- app_assoc.
         apply sel_subtrace_app_both; auto.
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
      ++ simpl. apply sel_subtrace_cons.
         rewrite <- (app_nil_l tl'2), <- app_assoc.
         apply sel_subtrace_app_both; auto.
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
    induction (RT_Call_reduce _ _ Hps) as [tlR HR].
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
    exists (RL_Call X p), (RT_Call X (ps0[\]p) (amend ps C)), s'.
    exists nil; eexists; exists s'.
    repeat split; eauto. apply sel_subtrace_refl.
    all: constructor; eauto; ESEr.
  - (* Finish *)
    rewrite <- H6, <- H1 in *.
    clear s'0 H7 C' H6 tl H5 s0 H4 C0 H2 H X0 H0 l H1.
    simpl. exists nil, nil; do 2 eexists.
    exists (RL_Call X p), (amend ps C), s'.
    exists nil, C, s'.
    repeat split; eauto. apply sel_subtrace_refl.
    all: constructor; eauto; ESEr.
+ inversion H.
Qed.

Lemma amend_complete_1' : forall ps C s tl C' s', Choreography_WF C ->
  (Defs,C,s) --[tl]--> (Defs,C',s') ->
  exists tl' tl'' C'' s'',
       sel_subtrace (tl::tl') tl''
    /\ (Defs,C',s') --[tl']-->* (Defs,C'',s'')
    /\ (amend_D ps,amend ps C,s) --[tl'']-->* (amend_D ps,amend ps C'',s'').
Proof.
intros.
elim (amend_complete_1 ps C s tl C' s'); auto.
intros. induction H1 as (tlI,(tlF,(C'',(s'',(H1,(H2,H3)))))).
do 4 eexists. repeat split; eauto.
apply sel_subtrace_app''; auto.
Qed.

Lemma amend_complete_many : forall ps C s tl C' s' Xs, Program_WF _ Xs (Defs,C) ->
  (Defs,C,s) --[tl]-->* (Defs,C',s') ->
  exists tl' tl'' C'' s'',
       sel_subtrace (tl++tl') tl''
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

Lemma amend_sound_1 : forall ps C s tl C' s', Choreography_WF C ->
  (amend_D ps, amend ps C,s) --[tl]--> (amend_D ps,C',s') ->
  exists tl' tl'' C'' s'',
  (amend_D ps,C',s') --[tl']-->* (amend_D ps, amend ps C'',s'')
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
  inversion H.
  - (* Then *)
    rewrite <- H5, <- H6 in *.
    clear s'0 H7 C' H6 t H5 s0 H2 C3 H4 C0 H3 b0 H1 p0 H0.
    elim (add_sels_reduce (amend_D ps) p left (up_list p b ps (amend ps C1) (amend ps C2)) (amend ps C1) s').
    intros t1 (Ht1,Ht1').
    exists t1, (Forget (RL_Cond p)::nil), C1, s'. repeat split; auto.
    * econstructor. 2: apply CCT_Refl. repeat constructor; eauto.
    * apply sel_subtrace_cons; auto.
  - (* Else *)
    rewrite <- H5, <- H6 in *.
    clear s'0 H7 C' H6 t H5 s0 H2 C3 H4 C0 H3 b0 H1 p0 H0.
    elim (add_sels_reduce (amend_D ps) p right (up_list p b ps (amend ps C1) (amend ps C2)) (amend ps C2) s').
    intros t1 (Ht1,Ht1').
    exists t1, (Forget (RL_Cond p)::nil), C2, s'. repeat split; auto.
    * econstructor. 2: apply CCT_Refl. repeat constructor; eauto.
    * apply sel_subtrace_cons; auto.
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
      apply sel_subtrace_swap; auto.
      rewrite <- (app_nil_r tl'').
      apply sel_subtrace_perm' with ((Forget t :: tl') ++ t1).
      apply sel_subtrace_app_both; auto.
      simpl. apply Permutation_cons; auto. apply Permutation_app_comm.
    * IHElim' IHC2 (Choreography_WF_Else _ _ _ _ _ HC) HC2 tl' tl'' C'' s'' Htl' Htl'' Hsub.
      elim (add_sels_reduce (amend_D ps) p right (up_list p b ps (amend ps C1) (amend ps C2)) C'2 s').
      intros t1 (Ht1,Ht1').
      exists (Forget (RL_Cond p)::t1++tl'), (Forget (RL_Cond p)::tl''), C'', s''.
      repeat split.
      econstructor; eauto. constructor. apply C_Else'; eauto.
      eapply CCT_Trans; eauto.
      econstructor; eauto. repeat constructor; auto.
      apply sel_subtrace_swap; auto.
      rewrite <- (app_nil_r tl'').
      apply sel_subtrace_perm' with ((Forget t :: tl') ++ t1).
      apply sel_subtrace_app_both; auto.
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
    repeat split; eauto. 3: apply sel_subtrace_refl.
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
    * apply sel_subtrace_app'; auto.
  - (* Enter *)
    rewrite <- H5, <- H1 in *.
    clear s'0 H7 C' H6 t H5 s0 H4 C0 H2 H X0 H0 l H1.
    exists nil, (Forget (RL_Call X p)::nil), (RT_Call X (ps0[\]p) C), s'.
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

Lemma amend_sound_many : forall ps C s tl C' s' Xs, Program_WF _ Xs (Defs,C) ->
  (amend_D ps, amend ps C,s) --[tl]-->* (amend_D ps,C',s') ->
  exists tl' tl'' C'' s'',
  (amend_D ps,C',s') --[tl']-->* (amend_D ps, amend ps C'',s'')
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
  elim (amend_sound_1 ps C s t C'' s''); auto.
  2: elim H; auto.
  intros tl0 [t0 [C0 [s0 [Htl0 [Hsub0 Htl0IF] ] ] ] ].
  induction (diamond_4b _ _ _ _ _ _ _ _ _ H2 Htl0) as [ [D C2] [tl' [tl0' [s2a [s2b [HC' [HC0 [Hs [Hperm [Hlen1 Hlen2] ] ] ] ] ] ] ] ] ].
  generalize (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ _ HC'). intro H'; rewrite <- H' in *; clear D H'.
  generalize (CCC_To_Program_WF _ _ _ _ _ _ _ (amend_Program_WF _ _ _ H) H1). intro HP''.
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

(** Miscellaneous. *)
Lemma amend_eq_End : forall ps C, amend ps C = CC.End -> C = CC.End.
Proof. induction C; simpl; auto; discriminate. Qed.

End Amend.

Section Projectability.

(** Projectability of amendment. *)

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

Lemma bproj_stable : forall (D D':DefSet Sig) p C B,
  (forall X, fst (D X) = fst (D' X)) ->
  [[D,C | p]] == B -> [[D',C | p]] == B.
Proof.
intros. induction H0; auto.
all: try constructor; auto.
2,3: rewrite <- H; auto.
apply bproj_Cond' with B1 B2; auto.
Qed.

Lemma projectable_B_stable : forall (D D':DefSet Sig) p C,
  (forall X, fst (D X) = fst (D' X)) ->
  projectable_B D p C -> projectable_B D' p C.
Proof.
intros. induction H0 as [B HB].
exists B. apply bproj_stable with D; auto.
Qed.

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

Local Ltac sup := rewrite set_union_iff; auto.

Lemma add_sels_CCC_pn_C : forall ps a p l C f,
  CCC_pn C f [C] CCC_pn (add_sels a p l ps C) f.
Proof. red; intros. induction ps; simpl; auto. sup. Qed.

Lemma add_sels_CCC_pn_ps : forall ps a p l C f,
  ps [C] CCC_pn (add_sels a p l ps C) f.
Proof.
red; intros.
induction ps, H.
all: simpl; sup. rewrite H; simpl; auto.
Qed.

Lemma add_sels_CCC_pn : forall ps a p l C f,
  CCC_pn (add_sels a p l ps C) f [C] (p :: CCC_pn C f [U] ps).
Proof.
intros; induction ps; simpl; auto.
red; simpl; auto.
red; red in IHps; intros.
simpl; rewrite set_add_iff.
rewrite set_union_iff in H.
induction H as [ [H | [H | H] ] | H]; auto.
inversion H. elim (IHps z); auto.
Qed.

Lemma amend_CCC_pn_C : forall ps a f Defs C,
  CCC_pn C f [C] CCC_pn (amend Defs a ps C) f.
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

Lemma up_list_incl : forall Defs p b ps C1 C2, up_list Defs p b ps C1 C2 [C] ps.
Proof.
red; intros. induction ps; simpl; auto.
revert H; simpl. elim eqb; auto.
elim projectable_B_dec; auto.
simpl; intros. inversion_clear H; auto.
Qed.

Lemma up_list_incl_C : forall Defs p b ps C1 C2,
  up_list Defs p b ps C1 C2 [C] (CCC_pn C1 (Names Defs) [U] CCC_pn C2 (Names Defs)).
Proof.
red; intros. induction ps; simpl; auto. inversion H.
generalize H; simpl.
case_eq (a =? p); intro; auto.
elim projectable_B_dec; intros; auto.
elim (In_dec (@eq_dec Pid) z (up_list Defs p b ps C1 C2)); auto.
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

Lemma amend_CCC_pn_incl : forall ps a Defs C,
  CCC_pn (amend Defs a ps C) (Names Defs) [C] CCC_pn C (Names Defs).
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

Variable ps : list Pid.
Variable a : Ann.
Variable P : CC.Program Sig.

Definition amend_P :=
  (amend_D (Procedures _ P) a ps, amend (Procedures _ P) a ps (Main P)).

Lemma amend_P_Vars : Vars P = Vars amend_P.
Proof. auto. Qed.

End Amendment.

Arguments amend [Sig].
Arguments amend_D [Sig].
Arguments amend_P [Sig].

Require Export EPPTheorem.
Require Export Implementation.

Section TuringRevisited.

Theorem amended_encoding_WF : forall n (f:PRFunction n),
  CCP_WF (amend_P (all_pids (n+Pi f)) eps (Encoding' f)).
Proof.
intros.
induction (Encoding'_WF f) as [Hann [Xs HWF] ].
split.
+ red; simpl; intros. rewrite <- amend_P_Vars.
  clear Xs HWF.
  red; intros. apply Hann.
  induction (Encoding' f) as (D,C).
  unfold Procs, Procedures, amend_P in H. simpl in H.
  generalize amend_CCC_pn_incl; intro.
  red in H0. eauto.
+ exists Xs. apply amend_Program_WF; auto.
Qed.

Lemma amend_implements : forall n (f:PRFunction n) ps q P ps' a Xs,
  Program_WF _ Xs P -> implements P f ps q -> implements (amend_P ps' a P) f ps q.
Proof.
red; intros. rename H into HP, H1 into Hps.
induction (H0 xs s) as [Hconv Hdiv]; auto.
induction P as (Defs,C).
split; intros.
1: induction (Hconv y) as [Hto Hfrom]; clear Hconv Hdiv.
2: induction Hdiv as [Hto Hfrom]; clear Hconv.
all: split; intros.
+ (* function converges *)
  specialize (Hto H); clear Hfrom.
  induction Hto as [s' [ts [P' [Hred [Hs' HP'] ] ] ] ].
  induction P' as (Defs',C').
  generalize (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ _ Hred) as HDefs; intros.
  rewrite <- HDefs in *; clear Defs' HDefs. simpl in *.
  rewrite HP' in *; clear C' HP'.
  apply amend_complete_many with (a:=a) (ps:=ps') (Xs:=Xs) in Hred; auto.
  induction Hred as (tl',(tl'',(C'',(s'',(Hsub,(Htl',Htl'')))))).
  generalize (CCP_ToStar_End _ _ _ _ _ _ Htl'); intro H'.
  induction H' as [H1 H2]; auto. rewrite H1 in *; clear H1 tl'.
  inversion Htl'. rewrite <- H3 in *; clear s'0 H6 C'' H3 s0 H4 P H1 H5.
  exists s'', tl''; eexists. repeat split; eauto.
  rewrite <- H2; auto.
+ (* choreography terminates *)
  apply Hfrom; clear Hto Hfrom.
  induction H as (s',(ts,(P',(Hts,(Hs',HP'))))).
  induction P' as (Defs',C'). simpl in *; rewrite HP' in *; clear C' HP'.
  rewrite <- (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ _ Hts) in Hts; clear Defs'.
  apply amend_sound_many with (Xs:=Xs) in Hts; auto.
  induction Hts as (tl',(tl'',(C'',(s'',(Htl',(Htl'',Hsub)))))).
  generalize (CCP_ToStar_End _ _ _ _ _ _ Htl'); intro H'.
  induction H' as [H1 H2]; auto. rewrite H1 in *; clear H1 tl'.
  inversion Htl'. symmetry in H1. rewrite (amend_eq_End _ _ _ _ _ H1) in *.
  clear s'0 H5 C'' H1 s0 H3 P H H4.
  exists s'', tl'', (Defs,End). repeat split; auto.
  rewrite <- H2; auto.
+ (* function diverges *)
  specialize (Hto H); clear H Hfrom.
  induction P' as (Defs',C').
  generalize (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ _ H1) as HDefs; intros.
  rewrite <- HDefs in *; clear Defs' HDefs. simpl in *.
  apply amend_sound_many with (Xs:=Xs) in H1; auto.
  induction H1 as (tl',(tl'',(C'',(s'',(Htl',(Htl'',Hsub)))))).
  simpl in Htl''. specialize (Hto _ _ _ Htl'').
  intro. apply Hto; simpl.
  rewrite H in *; clear C' H. simpl in *.
  generalize (CCP_ToStar_End _ _ _ _ _ _ Htl'); intro H'.
  induction H' as [H1 H2]; auto. rewrite H1 in *; clear H1 tl'.
  inversion Htl'. symmetry in H1. apply (amend_eq_End _ _ _ _ _ H1).
+ (* choreography diverges *)
  apply Hfrom; clear Hto Hfrom; intros.
  induction P' as (Defs',C').
  generalize (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ _ H1) as HDefs; intros.
  rewrite <- HDefs in *; clear Defs' HDefs. simpl in *.
  apply amend_complete_many with (a:=a) (ps:=ps') (Xs:=Xs) in H1; auto.
  induction H1 as (tl',(tl'',(C'',(s'',(Hsub,(Htl',Htl'')))))).
  intro HC'. rewrite HC' in *; clear C' HC'.
  generalize (CCP_ToStar_End _ _ _ _ _ _ Htl'); intro H'.
  induction H' as [H1 H2]; auto. rewrite H1 in *; clear H1 tl'.
  inversion Htl'. rewrite <- H3 in *; clear s'0 H6 C'' H3 s0 H4 P H1 H5.
  apply (H _ _ _ Htl''); auto.
Qed.

Theorem amended_encoding_sound : forall n (f:PRFunction n),
  implements (amend_P (all_pids (n+Pi f)) eps (Encoding' f)) f (vec_1_to_n n) 0.
Proof.
intros.
induction (Encoding'_WF f) as [Hann [Xs HP] ].
apply amend_implements with Xs; auto.
apply encoding_sound.
Qed.

Lemma vmax_vec_1_to_n : forall n, vmax (vec_1_to_n n) = n.
Proof.
intro. unfold vec_1_to_n.
destruct n; auto.
rewrite vec_k_to_n_vmax.
apply Nat.add_sub.
auto with arith.
Qed.

Theorem amended_encoding_projectable : forall n (f:PRFunction n),
  projectable _ (RecVarList (Gamma f)) (all_pids (n+Pi f)) (amend_P (all_pids (n+Pi f)) eps (Encoding' f)).
Proof.
intros.
induction (Encoding'_WF f) as [Hann [Xs HWF] ].
repeat split.
+ apply amend_projectable_C.
+ red. rewrite List.Forall_forall; intros.
  unfold Procedures, amend_P.
  set (P := Encoding' f). assert (P = Encoding' f); auto.
  clearbody P. induction P as (D,C). simpl.
  red; rewrite List.Forall_forall; intros.
  apply amend_projectable_B.
  unfold Encoding', Encoding in H0.
  change D with (fst (D,C)) in H1. rewrite H0 in H1. simpl in H1.
  rewrite vmax_vec_1_to_n in H1; auto.
+ unfold amend_P; simpl. tauto.
+ set (P := Encoding' f). assert (P = Encoding' f); auto.
  clearbody P. induction P as (D,C). simpl.
  unfold Encoding', Encoding in H.
  intros. change D with (fst (D,C)) in H1.
  rewrite H in H1. simpl in H1.
  rewrite vmax_vec_1_to_n in H1; auto.
+ set (P := Encoding' f). assert (P = Encoding' f); auto.
  clearbody P. induction P as (D,C). simpl; intros.
  specialize (Hann X p). rewrite <- H in Hann.
  unfold Encoding', Encoding in H.
  intros. apply CCC_pn_mon with (Y:=Names D) in H1.
  2: simpl; tauto.
  apply amend_CCC_pn_incl in H1.
  apply Hann in H1.
  change D with (fst (D,C)) in H1.
  rewrite H in H1. simpl in H1.
  rewrite vmax_vec_1_to_n in H1; auto.
Qed.

Theorem amended_encoding_Projectable : forall n (f:PRFunction n),
  Projectable _ (amend_P (all_pids (n+Pi f)) eps (Encoding' f)).
Proof.
intros.
induction (Encoding'_WF f) as [Hann [Xs HWF] ].
(* this should be simplifiable *)
exists Xs, (all_pids (n+Pi f)); split. repeat split.
+ apply amend_projectable_C.
+ red. rewrite List.Forall_forall; intros.
  unfold Procedures, amend_P.
  set (P := Encoding' f). assert (P = Encoding' f); auto.
  clearbody P. induction P as (D,C). simpl.
  red; rewrite List.Forall_forall; intros.
  apply amend_projectable_B.
  unfold Encoding', Encoding in H0.
  change D with (fst (D,C)) in H1. rewrite H0 in H1. simpl in H1.
  rewrite vmax_vec_1_to_n in H1; auto.
+ unfold amend_P; simpl. tauto.
+ set (P := Encoding' f). assert (P = Encoding' f); auto.
  clearbody P. induction P as (D,C). simpl.
  unfold Encoding', Encoding in H.
  intros. change D with (fst (D,C)) in H1.
  rewrite H in H1. simpl in H1.
  rewrite vmax_vec_1_to_n in H1; auto.
+ set (P := Encoding' f). assert (P = Encoding' f); auto.
  clearbody P. induction P as (D,C). simpl; intros.
  specialize (Hann X p). rewrite <- H in Hann.
  unfold Encoding', Encoding in H.
  intros. apply CCC_pn_mon with (Y:=Names D) in H1.
  2: simpl; tauto.
  apply amend_CCC_pn_incl in H1.
  apply Hann in H1.
  change D with (fst (D,C)) in H1.
  rewrite H in H1. simpl in H1.
  rewrite vmax_vec_1_to_n in H1; auto.
+ apply amend_Program_WF; auto.
Qed.

End TuringRevisited.

Section SP_Turing.

Open Scope SP_scope.

Definition SP_implements (P:SP.Program (Sig' IS)) {n} (f:PRFunction n) (ps:t Pid n) (q:Pid) :=
  forall (xs:t nat n) s, (forall Hi, s (ps[@Hi]) xx = xs[@Hi]) ->
  (forall y, converges f xs y <-> exists s' ts P',
      (P,s) --[ts]-->* (P',s') /\ s' q xx = y /\ Net P' (==) EmptyNet _) /\
  (diverges f xs <-> forall s' ts P', (P,s) --[ts]-->* (P',s') -> ~(Net P' (==) EmptyNet _)).

Definition Encode_Net {n} f := epp _ _ _ (amended_encoding_projectable n f).

Lemma epp_implements : forall n (f:PRFunction n) P Xs ps q ps',
  Program_WF _ Xs P -> well_ann _ P -> forall (HP:projectable _ Xs ps' P),
  (forall p, List.In p ps' -> str_proj (Procedures _ P) (Main P) p) ->
  (forall p, List.In p (CCC_pn (Main P) (Vars P)) -> List.In p ps') ->
  (forall p X, List.In X Xs -> List.In p (Vars P X) -> List.In p ps') ->
  implements P f ps q -> SP_implements (epp Xs ps' P HP) f ps q.
Proof.
intros.
rename H0 into Hann, H1 into Hsp, H2 into Hpn, H3 into Hin, H4 into Himpl.
red; intros.
induction (Himpl _ _ H0) as [Hconv Hdiv]; clear H0.
repeat split.
+ (* f converges *)
  intros. elim (Hconv y); intros. specialize (H1 H0).
  clear Hconv Hdiv H0 H2.
  induction H1 as [s' [ts [P' [Hts [Hs' HP'] ] ] ] ].
  induction P as (D,C), P' as (D',C').
  generalize (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ _ Hts); intro HD.
  simpl in HP'. rewrite <- HD, HP' in *; clear C' D' HD HP'.
  apply EPP_Complete' with (HP:=HP) in Hts; auto.
  induction Hts as [N [tl' [Htl' HN] ] ].
  exists s', tl', N. repeat split; auto.
  assert (projectable_C D End ps').
  1:{ red; rewrite List.Forall_forall; intros.
      exists (SP.End _); constructor.
  }
  assert (projectable IS Xs ps' (D,End)).
  1: { elim HP. intros HC (HD,(H1,(H2,H3))).
       repeat split; auto. simpl; tauto.
  }
  specialize (HN H1).
  generalize (epp_C_char _ _ _ _ _ H1 H0); intros.
  intro. specialize (HN p). rewrite H2 in HN.
  rewrite epp_C_End in HN. inversion HN; auto.
+ (* N terminates *)
  intros. apply (Hconv y); intros. clear Hconv Hdiv.
  induction H0 as [s' [ts [P' [Hts [Hs' HP'] ] ] ] ].
  apply EPP_Sound' in Hts; auto.
  induction Hts as [P'' [ts' [Htl' HN] ] ].
  exists s', ts', P''; repeat split; auto.
  apply CCC_ToStar_projectable with (s:=s) (tl:=ts') (P':=P'') (s':=s') in HP; auto.
  specialize (HN HP).
  apply epp_EmptyNet' with (HP:=HP) (N:=Net P'); auto.
  apply (CCC_ToStar_Program_WF _ _ _ _ _ _ _ H Htl').
+ (* f diverges *)
  induction Hdiv; intros. specialize (H0 H2). clear Hconv H1 H2.
  apply EPP_Sound' in H3.
  induction H3 as [P'' [ts' [Htl' HN] ] ].
  intro. eapply H0; eauto. all: auto.
  apply CCC_ToStar_projectable with (s:=s) (tl:=ts') (P':=P'') (s':=s') in HP; auto.
  apply epp_EmptyNet' with (HP:=HP) (N:=Net P'); auto.
  apply (CCC_ToStar_Program_WF _ _ _ _ _ _ _ H Htl').
+ (* N loops *)
  intros. apply Hdiv; intros. clear Hconv Hdiv.
  induction P as (D,C), P' as (D',C').
  generalize (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ _ H1); intros HD HC'.
  simpl in HC'. rewrite HC', <- HD in *; clear D' C' HD HC'.
  apply EPP_Complete' with (HP:=HP) in H1; auto.
  induction H1 as [N [tl' [Htl' HN] ] ].
  eapply H0; eauto.
  assert (projectable_C D End ps').
  1:{ red; rewrite List.Forall_forall; intros.
      exists (SP.End _); constructor.
  }
  assert (projectable IS Xs ps' (D,End)).
  1: { elim HP. intros HC (HD,(H2,(H3,H4))).
       repeat split; auto. simpl; tauto.
  }
  specialize (HN H2).
  generalize (epp_C_char _ _ _ _ _ H2 H1); intros.
  intro. specialize (HN p). rewrite H3 in HN.
  rewrite epp_C_End in HN. inversion HN; auto.
Qed.

Theorem encode_Net_sound : forall n (f:PRFunction n),
  SP_implements (Encode_Net f) f (vec_1_to_n n) 0.
Proof.
intros.
induction (amended_encoding_WF n f) as [Hann [Xs HXs] ].
apply epp_implements; auto.
+ apply amend_Program_WF; auto.
  split. apply Encoding_Main_WF.
  split. apply Encoding_Main_within_Xs; apply RecVarList_In; auto with arith.
  split. simpl; auto.
  split.
  1: { apply Encoding_rec_WF; intros; auto.
       intro. elim (in_vec_k_to_n _ H0); intros.
       inversion H1.
    2: auto with arith.
    elim (in_vec_k_to_n _ H0); intros.
    rewrite vmax_vec_1_to_n; auto.
  }
  split. apply Encoding_rec_initial.
  split. apply Encoding_Procs_Vars_not_nil.
  change (Gamma f) with (0 + Gamma f).
  apply Encoding_rec_within_Xs; simpl; auto.
+ intros. apply HXs.
+ intros. simpl in H.
  rewrite <- amend_P_Vars in H.
  unfold Vars, Encoding', Procedures in H.
  simpl in H.
  rewrite vmax_vec_1_to_n in H; auto.
+ intros. unfold Vars, Encoding', Procedures in H0.
  simpl in H0.
  rewrite vmax_vec_1_to_n in H0; auto.
+ apply amended_encoding_sound.
Qed.

End SP_Turing.
