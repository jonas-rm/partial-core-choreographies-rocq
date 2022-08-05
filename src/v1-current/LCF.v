Require Import EPP.

Section Amendmend.

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

Variable Defs:DefSet Sig.

(* Clean me *)
Fixpoint amend (C:Choreography Sig) (p:Pid) (a:Ann) :=
match C with
| eta@a';; C' => eta@a';; (amend C' p a)
| If q ?? b Then C1 Else C2 =>
    let C1' := amend C1 p a in let C2' := amend C2 p a in
    let C' := If q ?? b Then C1' Else C2' in
    if (p =? q) then C'
    else if projectable_B_dec _ Defs (If q ?? b Then C1' Else C2') p then C'
         else If q ?? b Then (q --> p[left]@a;; C1') Else (q --> p[right]@a;; C2')
| RT_Call X ps C' => RT_Call X ps (amend C' p a)
| _ => C
end.

(** To avoid duplication of cases - I'd love an or... *)
Lemma amend_If : forall q b C1 C2 p a,
  let C1' := amend C1 p a in let C2' := amend C2 p a in
  { amend (If q ?? b Then C1 Else C2) p a = If q ?? b Then C1' Else C2' }
  + { amend (If q ?? b Then C1 Else C2) p a = If q ?? b Then (q --> p[left]@a;; C1') Else (q --> p[right]@a;; C2') }.
Proof. intros; simpl. elim (p =? q); auto. elim projectable_B_dec; auto. Qed.

Lemma amend_proj : forall C p a,
  projectable_B Sig Defs (amend C p a) p.
Proof.
induction C; intros.
+ simpl.
  induction (IHC p a) as [B HB].
  induction e. all: eq_elim p t0 Hp.
  2: eq_elim p t2 Hp'. 5: eq_elim p t1 Hp'. 5: induction t2.
  all: try (eexists; econstructor; eauto; fail).
  exists (@Branching Sig' t0 (Some (t,B)) None). constructor; auto.
  exists (@Branching Sig' t0 None (Some (t,B))). constructor; auto.
+ induction (IHC1 p a) as [B1 HB1]. induction (IHC2 p a) as [B2 HB2].
  simpl. case_eq (p =? t); intro.
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
+ elim (in_dec (@eq_dec Pid) p (fst (Defs t))).
  all: eexists. constructor; auto. apply bproj_Call_out; auto.
+ elim (in_dec (@eq_dec Pid) p l).
  eexists. constructor; auto.
  induction (IHC p a) as [B HB].
  eexists. apply bproj_RT_Call_out; eauto.
+ simpl. eexists; constructor.
Qed.

Definition amend_D (p:Pid) (a:Ann) : DefSet Sig :=
  fun X => (fst (Defs X),amend (snd (Defs X)) p a).

(*
Inductive sel_subtrace : list (TransitionLabel Pid Value) -> list (TransitionLabel Pid Value) -> Prop :=
| ss_refl ts : sel_subtrace ts ts
| ss_cons t ts ts' : sel_subtrace ts ts' -> sel_subtrace (t::ts) (t::ts')
| ss_extra p q l ts ts' : sel_subtrace ts ts' -> sel_subtrace ts (TL_Sel p q l::ts')
.

Lemma sel_subtrace_app : forall ts ts' ts'',
  sel_subtrace ts ts' -> sel_subtrace (ts''++ts) (ts''++ts').
Proof. induction ts''; simpl; auto. constructor; auto. Qed.

Lemma sel_subtrace_trans : forall ts ts' ts'',
  sel_subtrace ts ts' -> sel_subtrace ts' ts'' -> sel_subtrace ts ts''.
Proof.
intros. revert ts H. induction H0; auto.
+ intros. inversion H; constructor; auto.
+ intros. inversion H.
  - constructor; auto.
  - constructor. rewrite H2; auto.
  - constructor; auto.
Qed.

Definition sel_subtrace' ts ts' :=
  exists ts'', sel_subtrace ts ts'' /\ Permutation ts' ts''.

Lemma sel_subtrace'_refl : forall ts, sel_subtrace' ts ts.
Proof. intros. exists ts; split; auto. constructor. Qed.

Lemma sel_subtrace'_base : forall ts ts',
  sel_subtrace ts ts' -> sel_subtrace' ts ts'.
Proof. intros. exists ts'; split; auto. Qed.

Lemma sel_subtrace'_cons : forall t ts ts',
  sel_subtrace' ts ts' -> sel_subtrace' (t::ts) (t::ts').
Proof.
intros. induction H as [ts'' [H' H''] ].
exists (t::ts''). split; econstructor; eauto.
Qed.

Lemma sel_subtrace'_extra : forall p q l ts ts',
  sel_subtrace' ts ts' -> sel_subtrace' ts (TL_Sel p q l::ts').
Proof.
intros. induction H as [ts'' [H' H''] ].
exists (TL_Sel p q l::ts'').
split; constructor; auto.
Qed.

Lemma sel_subtrace'_app : forall ts ts' ts'',
  sel_subtrace' ts' ts'' -> sel_subtrace' (ts++ts') (ts++ts'').
Proof.
intros. induction H as [ts_ [H' H''] ].
exists (ts ++ ts_); split.
+ apply sel_subtrace_app; auto.
+ apply Permutation_app_head; auto.
Qed.

Lemma sel_subtrace'_perm : forall t t' ts ts',
  sel_subtrace' ts (t :: ts') -> sel_subtrace' (t' :: ts) (t :: t' :: ts').
Proof.
intros.
induction H as [ts0 [H1 H2] ].
exists (t' :: ts0); split.
repeat constructor; auto.
eapply Permutation_trans. apply perm_swap.
constructor; auto.
Qed.

Lemma sel_subtrace'_perm_extra : forall t t' ts ts' p q l,
  sel_subtrace' ts (t :: ts') -> sel_subtrace' (t' :: ts) (t :: t' :: (TL_Sel p q l) :: ts').
Proof.
intros.
induction H as [ts0 [H1 H2] ].
exists (t' :: TL_Sel p q l :: ts0); split.
repeat constructor; auto.
eapply Permutation_trans. apply perm_swap. constructor.
eapply Permutation_trans. apply perm_swap.
constructor; auto.
Qed.

Lemma sel_subtrace'_app' : forall t ts ts' ts'',
  sel_subtrace' ts (t::ts') -> sel_subtrace' (ts''++ts) (t::ts''++ts').
Proof.
intros. induction H as [ts0 [H' H''] ].
exists (ts''++ts0).
split.
+ apply sel_subtrace_app; auto.
+ eapply Permutation_trans.
  apply Permutation_middle.
  apply Permutation_app_head; auto.
Qed.

Lemma sel_subtrace'_app'' : forall t ts ts' ts'',
  sel_subtrace' ts (ts' ++ ts'') -> sel_subtrace' (t :: ts) (ts' ++ t :: ts'').
Proof.
intros. induction H as [ts0 [H' H''] ].
exists (t :: ts0); split.
+ constructor; auto.
+ eapply Permutation_trans.
  2: apply Permutation_cons; eauto.
  apply Permutation_sym, Permutation_middle.
Qed.

Lemma sel_subtrace'_Perm : forall ts ts' ts'',
  sel_subtrace' ts ts' -> Permutation ts' ts'' -> sel_subtrace' ts ts''.
Proof.
intros. induction H as [ts0 [H' H''] ].
exists ts0; split; auto.
eapply Permutation_trans.
apply Permutation_sym. all: eauto.
Qed.

(* Missing induction principle. *)
Lemma sel_subtrace_app_inv : forall ts ts' ts'',
  sel_subtrace (ts ++ ts') ts'' ->
  exists ts1 ts2, ts'' = ts1 ++ ts2 /\ sel_subtrace ts ts1 /\ sel_subtrace ts' ts2.
Proof.
intros. induction H.
+ exists ts, ts'. repeat split; auto.


intros ts ts' ts''. revert ts ts'.
induction ts''; intros.
+ exists nil, nil.
  inversion H. apply app_eq_nil in H2; inversion_clear H2.
  rewrite H1, H3; repeat split; auto; constructor.
+ inversion H.
  - 



+ exists nil, ts''; repeat split; auto. constructor.
+ inversion H.
  - rewrite <- H1 in *. clear ts'' H1 ts0 H0.
    exists (a::ts), ts'; repeat split; auto; constructor.
  - rewrite <- H1 in *; clear ts'' H1 ts0 H2 t H0.
    induction (IHts _ _ H3) as [ts1 [ts2 [H1 [H2 H0] ] ] ].
    exists (a::ts1), ts2; repeat split; auto.
    rewrite H1; auto. constructor; auto.
  - simpl in *. 





Lemma sel_subtrace'_Perm' : forall ts ts' ts'',
  sel_subtrace' ts ts' -> Permutation ts'' ts -> sel_subtrace' ts'' ts'.
Proof.
intros.
revert H0 ts' H.
apply (Permutation_ind_transp
  (fun l1 l2 => forall l, sel_subtrace' l2 l -> sel_subtrace' l1 l)).
+ auto.
+ intros.
  induction H as [l0 [H' H''] ].

  induction l1; simpl in *.
  - induction H as [l1 [H' H''] ].
    inversion H'.
    * rewrite <- H0 in *; clear ts0 l1 H H0.
      inversion H''. clear l' H2 x0 H l H0 H''.
      inversion H1.

+ eauto.


revert ts' H. induction H0; auto; intros.
- induction H as [ts0 [H' H''] ].
  inversion H'.
  + rewrite <- H1 in *; clear H H1 ts ts0.
    exists (x::l); split. constructor.
    eapply Permutation_trans; eauto. constructor; auto.
    apply Permutation_sym; auto.
  + rewrite <- H1 in *; clear t H ts H2 ts0 H1.
Search Permutation.
    exists (x :: ts'0); split. constructor; auto. auto.

Admitted.
(* intros. induction H as [ts0 [H' H''] ].
exists ts; split; auto.
eapply Permutation_trans.
apply Permutation_sym. all: eauto.
Qed.
 *)


Lemma sel_subtrace'_trans : forall ts ts' ts'',
  sel_subtrace' ts ts' -> sel_subtrace' ts' ts'' -> sel_subtrace' ts ts''.
Proof.
intros.
induction H as [t [H1 H2] ].
generalize (sel_subtrace'_Perm' _ _ _ H0 (Permutation_sym H2)); intros.
induction H as [t' [H3 H4] ].
exists t'; split; auto.
eapply sel_subtrace_trans; eauto.
Qed.
*)

Lemma amend_1_complete_1 : forall C s tl C' s', Choreography_WF C ->
  (Defs,C,s) --[tl]--> (Defs,C',s') ->
  forall r a, exists tl' tlI tlF C'' s'',
       sel_subtrace tl' (tlI++tlF)
    /\ (Defs,C',s') --[tl']-->* (Defs,C'',s'')
    /\ (amend_D r a,amend C r a,s) --[tlI ++ tl::tlF]-->* (amend_D r a,amend C'' r a,s'').
Proof.
Local Ltac IHElim IHC HC H tl' tlI CI sI tl0 C0 s0 tlF CF sF H1 H2 H3 H4 H5 H6 := 
    induction (IHC _ _ _ _ HC H) as
    [tl' [tlI [CI [sI [tl0 [C0 [s0 [tlF [CF [sF [H1 [H2 [H3 [H4 [H5 H6] ] ] ] ] ] ] ] ] ] ] ] ] ] ]; clear IHC.
intros. rename H into HC, H0 into H.
assert (exists tl' tlI CI sI tl0 C0 s0 tlF CF sF,
       sel_subtrace tl' (tlI++tlF)
    /\ tl = forget tl0
    /\ (Defs,C',s') --[tl']-->* (Defs,CF,sF)
    /\ (amend_D r a,amend C r a,s) --[tlI]-->* (amend_D r a,CI,sI)
    /\ <<CI,sI>> --[tl0,amend_D r a]--> <<C0,s0>>
    /\ (amend_D r a,C0,s0) --[tlF]-->* (amend_D r a,amend CF r a,sF)).
2: { destroy H0. do 5 eexists. repeat split; eauto.
     eapply CCT_Trans; eauto. econstructor; eauto.
     rewrite H2; constructor; eauto. }
inversion_clear H. clear tl; rename H0 into H, t into tl.
revert C s tl C' s' HC H.
induction C; intros. induction e.
+ rename t0 into p, t1 into e, t2 into q, t3 into x, t into a'.
  inversion H.
  - (* Com *)
    rewrite <- H8 in *.
    clear s'0 H9 C' H8 tl H7 s0 H1 C0 H6 a0 H5 x0 H4 q0 H3 e0 H2 p0 H0 H.
    simpl. exists nil, nil; do 2 eexists.
    exists (RL_Com p v q x), (amend C r a), s'.
    exists nil, C, s'.
    repeat split; eauto. apply sel_subtrace_refl.
    all: constructor. auto.
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
    exists (RL_Sel p q l), (amend C r a), s'.
    exists nil, C, s'.
    repeat split; eauto. apply sel_subtrace_refl.
    all: constructor. auto.
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
    elim (amend_If p b C1 C2 r a); intro HA; rewrite HA.
    * exists nil, nil; do 2 eexists.
      exists (@RL_Cond Pid Value Var RecVar p), (amend C1 r a), s'.
      exists nil, C1, s'.
      repeat split; try constructor; auto.
    * exists nil, nil; do 2 eexists.
      exists (@RL_Cond Pid Value Var RecVar p), (p-->r[left]@a;; amend C1 r a), s'.
      exists (@Forget (RL_Sel p r left)::nil), C1, s'.
      repeat split. apply sel_subtrace_extra, sel_subtrace_refl.
      all: repeat constructor; auto.
      repeat econstructor.
  - (* Else *)
    rewrite <- H6 in *.
    clear s'0 H7 C' H6 tl H5 s0 H1 C3 H3 C0 H2 b0 H0 p0 H H4.
    (* did we amend? *)
    elim (amend_If p b C1 C2 r a); intro HA; rewrite HA.
    * exists nil, nil; do 2 eexists.
      exists (@RL_Cond Pid Value Var RecVar p), (amend C2 r a), s'.
      exists nil, C2, s'.
      repeat split; try constructor; auto.
    * exists nil, nil; do 2 eexists.
      exists (@RL_Cond Pid Value Var RecVar p), (p-->r[right]@a;; amend C2 r a), s'.
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
    all: elim (amend_If p b C1 C2 r a); intro HA.
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
    exists (RL_Call X p), (amend (snd (Defs X)) r a), s'.
    exists nil, (snd (Defs X)), s'.
    repeat split; eauto. apply sel_subtrace_refl.
    all: constructor; simpl; auto.
  - (* Call *)
    rewrite <- H5 in *.
    clear s'0 H7 C' H6 tl H5 s0 H4 X0 H0 H.
    simpl. exists nil, nil; do 2 eexists.
    exists (RL_Call X p); eexists; exists s'.
    exists nil; eexists; exists s'.
    repeat split; eauto. apply sel_subtrace_refl.
    all: constructor; simpl; auto.
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
    exists (RL_Call X p), (RT_Call X (ps[\]p) (amend C r a)), s'.
    exists nil; eexists; exists s'.
    repeat split; eauto. apply sel_subtrace_refl.
    all: constructor; auto.
  - (* Finish *)
    rewrite <- H6, <- H1 in *.
    clear s'0 H7 C' H6 tl H5 s0 H4 C0 H2 H X0 H0 l H1.
    simpl. exists nil, nil; do 2 eexists.
    exists (RL_Call X p), (amend C r a), s'.
    exists nil, C, s'.
    repeat split; eauto. apply sel_subtrace_refl.
    all: constructor; auto.
+ inversion H.
Qed.

Lemma amend_1_complete_1' : forall C s tl C' s', Choreography_WF C ->
  (Defs,C,s) --[tl]--> (Defs,C',s') ->
  forall r a, exists tl' tl'' C'' s'',
       sel_subtrace (tl::tl') tl''
    /\ (Defs,C',s') --[tl']-->* (Defs,C'',s'')
    /\ (amend_D r a,amend C r a,s) --[tl'']-->* (amend_D r a,amend C'' r a,s'').
Proof.
intros.
elim (amend_1_complete_1 C s tl C' s') with r a; auto.
intros. destroy H1.
do 4 eexists. repeat split; eauto.
apply sel_subtrace_app''; auto.
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

Lemma amend_1_complete_many : forall C s tl C' s' Xs, Program_WF _ Xs (Defs,C) ->
  (Defs,C,s) --[tl]-->* (Defs,C',s') ->
  forall r a, exists tl' tl'' C'' s'',
       sel_subtrace (tl ++ tl') tl''
    /\ (Defs,C',s') --[tl']-->* (Defs,C'',s'')
    /\ (amend_D r a,amend C r a,s) --[tl'']-->* (amend_D r a,amend C'' r a,s'').
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
  repeat split; simpl; constructor; auto.
+ case_eq tl; intros.
  1: { (* repeat... *)
    rewrite H1 in *; clear tl H1.
    inversion_clear H0.
    exists nil, nil, C', s'.
    repeat split; simpl; constructor; auto.
  }
  rewrite H1 in *; clear tl H1.
  simpl in Hn. apply le_S_n in Hn. rename l into tl.
  inversion_clear H0. induction c2 as [ [D C''] s''].
  generalize (CCP_To_Defs_stable _ _ _ _ _ _ _ _ H1). intro H'; rewrite <- H' in *; clear D H'.
  elim (amend_1_complete_1' C s t C'' s'') with r a; auto.
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
  - eapply CCT_Trans; eauto. apply CCP_ToStar_eq with s2b; auto.
  - eapply CCT_Trans; eauto.




Lemma amend_1_sound_1 : forall C r a s tl C' s', Choreography_WF C ->
  (amend_D r a, amend C r a,s) --[tl]--> (amend_D r a, C',s') ->
  exists tl' tl'' C'' s'',
  (amend_D r a,C',s') --[tl']-->* (amend_D r a, amend C'' r a,s'')
  /\ (Defs,C,s) --[tl'']-->* (Defs,C'',s'') /\ sel_subtrace' tl'' (tl::tl').
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
    * econstructor; eauto. 2: constructor. repeat constructor; auto.
    * apply sel_subtrace'_refl.
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
    * apply sel_subtrace'_perm; auto.
+ rename t1 into p, t2 into q, t3 into l, t0 into a'.
  inversion H.
  - (* Sel *)
    rewrite <- H6 in *.
    clear s'0 H8 C' H7 t H6 s0 H1 C0 H5 a0 H4 l0 H3 q0 H2 p0 H H0.
    exists nil, (Forget (RL_Sel p q l) :: nil), C, s'. repeat split.
    * repeat constructor.
    * econstructor; eauto. 2: constructor. repeat constructor; auto.
    * apply sel_subtrace'_refl.
  - (* Delay *)
    clear s'0 H6 C' H5 t0 H4 s0 H2 C0 H3 ann H1 eta H H0.
    induction H7 as [Hp Hq].
    IHElim' IHC (Choreography_WF_eta _ _ _ _ HC) H8 tl' tl'' C'' s'' Htl' Htl'' Hsub.
    set (tlS := @RL_Sel Pid Value Var RecVar p q l).
    exists (Forget tlS::tl'), (Forget tlS::tl''), C'', s''.
    repeat split; auto.
    * econstructor; eauto. repeat constructor.
    * econstructor; eauto. repeat constructor.
    * apply sel_subtrace'_perm; auto.
+ rename t0 into p, t1 into b.
  elim (amend_If p b C1 C2 r a); intro HA; rewrite HA in *; clear HA.
  all: inversion H.
  - (* Then *)
    rewrite <- H5, <- H6 in *.
    clear s'0 H7 C' H6 t H5 s0 H2 C3 H4 C0 H3 b0 H1 p0 H0.
    exists nil, (Forget (RL_Cond p)::nil), C1, s'. repeat split; auto.
    * constructor.
    * econstructor. 2: constructor. repeat constructor; eauto.
    * apply sel_subtrace'_refl.
  - (* Else *)
    rewrite <- H5, <- H6 in *.
    clear s'0 H7 C' H6 t H5 s0 H2 C3 H4 C0 H3 b0 H1 p0 H0.
    exists nil, (Forget (RL_Cond p)::nil), C2, s'. repeat split; auto.
    * constructor.
    * econstructor. 2: constructor. repeat constructor; eauto.
    * apply sel_subtrace'_refl.
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
      apply sel_subtrace'_perm; auto.
    * IHElim' IHC2 (Choreography_WF_Else _ _ _ _ _ HC) H10 tl' tl'' C'' s'' Htl' Htl'' Hsub.
      exists (Forget (RL_Cond p)::tl'), (Forget (RL_Cond p)::tl''), C'', s''.
      repeat split.
      econstructor; eauto. repeat constructor; auto. rewrite <- Hb; auto.
      econstructor; eauto. repeat constructor; auto.
      apply sel_subtrace'_perm; auto.
  - (* Then + Amend *)
    rewrite <- H5, <- H6 in *.
    clear s'0 H7 C' H6 t H5 s0 H2 C3 H4 C0 H3 b0 H1 p0 H0.
    exists (Forget (RL_Sel p r left)::nil), (Forget (RL_Cond p)::nil), C1, s'. repeat split; auto.
    * econstructor; repeat constructor.
    * econstructor. 2: constructor. repeat constructor; auto.
    * eexists; split. 2: apply Permutation_refl. repeat constructor.
  - (* Else + Amend *)
    rewrite <- H5, <- H6 in *.
    clear s'0 H7 C' H6 t H5 s0 H2 C3 H4 C0 H3 b0 H1 p0 H0.
    exists (Forget (RL_Sel p r right)::nil), (Forget (RL_Cond p)::nil), C2, s'. repeat split; auto.
    * econstructor; repeat constructor.
    * econstructor. 2: constructor. repeat constructor; auto.
    * eexists; split. 2: apply Permutation_refl. repeat constructor.
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
      apply sel_subtrace'_perm_extra; auto.
    * IHElim' IHC2 (Choreography_WF_Else _ _ _ _ _ HC) H20 tl' tl'' C'' s'' Htl' Htl'' Hsub.
      exists (Forget (RL_Cond p)::Forget (RL_Sel p r right)::tl'), (Forget (RL_Cond p)::tl''), C'', s''.
      repeat split.
      econstructor; eauto. constructor. apply C_Else'. rewrite <- Hb; auto.
      econstructor; eauto. repeat constructor; auto.
      econstructor; eauto. repeat constructor; auto.
      apply sel_subtrace'_perm_extra; auto.
+ rename t0 into X. inversion H.
  - (* Local *)
    rewrite <- H6 in *.
    clear s'0 H7 C' H6 t H5 s0 H4 X0 H0 H.
    simpl. exists nil, (Forget (RL_Call X p)::nil), (snd (Defs X)), s'.
    repeat split; repeat constructor.
    econstructor; constructor. constructor; auto.
    apply sel_subtrace'_refl.
  - (* Call *)
    rewrite <- H5 in *.
    clear s'0 H7 C' H6 t H5 s0 H4 X0 H0 H.
    simpl. exists nil, (Forget (RL_Call X p)::nil), (RT_Call X (fst (Defs X) [\] p) (snd (Defs X))), s'.
    repeat split; eauto. 3: apply sel_subtrace'_refl.
    constructor.
    econstructor; constructor. constructor; auto.
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
    * apply sel_subtrace'_app'; auto.
  - (* Enter *)
    rewrite <- H5, <- H1 in *.
    clear s'0 H7 C' H6 t H5 s0 H4 C0 H2 H X0 H0 l H1.
    exists nil, (Forget (RL_Call X p)::nil), (RT_Call X (ps[\]p) C), s'.
    repeat split; eauto. 3: apply sel_subtrace'_refl.
    constructor.
    econstructor; constructor. constructor; auto.
  - (* Finish *)
    rewrite <- H5, <- H1 in *.
    clear s'0 H7 C' H6 t H5 s0 H4 C0 H2 H X0 H0 l H1.
    exists nil, (Forget (RL_Call X p)::nil), C, s'.
    repeat split; eauto. 3: apply sel_subtrace'_refl.
    constructor.
    econstructor; constructor. constructor; auto.
+ inversion H.
Qed.


(* Lemma : P --[tl]-->* P' iff amend(P) --[tl']-->* amend(P')

p.e -> q.x;; If r ?? b Then r.e' -> p.y Else 0

-->

p.e -> q.x ;; r.e' -> p.y


(* amended *)
p.e -> q.x;; If r ?? b Then r --> p[l];; r.e' -> p.y Else r --> p[r]

-->

p.e -> q.x;; r --> p[l];; r.e' -> p.y


*)

(*
if P -->* P' and amend(P) -->* P''
then there exists P''' such that
  P' -->* P''' and P'' -->* amend(P''')
*)

(*
Lemma amend_reduce_1 : forall Defs C p sigma t C' sigma',
  CCC_To Defs (amend Defs C p) sigma t C' sigma' ->
  
*)

Inductive more_sels : Choreography -> Choreography -> Prop :=
| MS_refl C : more_sels C C
| MS_Eta eta C C' : more_sels C C' -> more_sels (eta;;C) (eta;;C')
| MS_If p b C1 C1' C2 C2' : more_sels C1 C1' -> more_sels C2 C2' ->
      more_sels (If p ?? b Then C1 Else C2) (If p ?? b Then C1' Else C2')
| MS_RT_Call X ps C C' : more_sels C C' -> more_sels (RT_Call X ps C) (RT_Call X ps C')
| MS_sel p q l C C' : more_sels C C' -> more_sels (p --> q[l];; C) C'
.

Lemma amend_more_sels : forall Defs C p, more_sels (amend Defs C p) C.
Proof.
induction C.
all: try (constructor; auto).
rename p into q; intro p.
change (amend Defs (If q ?? b Then C1 Else C2) p) with
    match (collapse (bproj Defs (If q ?? b Then (amend Defs C1 p) Else (amend Defs C2 p)) p)) with
    | XUndefined => If q ?? b Then (q --> p[left];; amend Defs C1 p) Else (q --> p[right];; amend Defs C2 p)
    | _ => If q ?? b Then (amend Defs C1 p) Else (amend Defs C2 p)
    end.
  elim (XUndefined_dec (collapse (bproj Defs (If q ?? b Then (amend Defs C1 p) Else (amend Defs C2 p)) p))); intros.
- rewrite a. constructor; constructor; auto.
- rewrite Xmatch_elim; auto. constructor; auto.
Qed.

(*
C1 R C2
C1 --> C1'

* C1' R than C2
* C2 --> C2' and C1' R C2'

C1 : If r.e Then p --> q[l] Else p --> q[l]
C2 : If r.e Then p --> q[l] Else 0
*)

Lemma more_sels_reduce_1 : forall C1 C2, more_sels C1 C2 ->
  forall Defs sigma t C1' sigma', CCC_To Defs C1 sigma t C1' sigma' ->
  more_sels C1' C2 \/ exists C2', CCC_To Defs C2 sigma t C2' sigma' /\ more_sels C1' C2'.
Proof.
intros C1 C2 H. induction H; intros.
- right. exists C1'. split; auto. constructor.
- inversion H0.
  + right. exists C'; split; auto. constructor; auto. rewrite <- H5; auto.
  + right. exists C'; split; auto. constructor; auto. rewrite <- H5; auto.
  + rewrite <- H6 in H0.
    clear s' H7 C1' H6 t0 H5 s H4 C0 H2 eta0 H1.
    elim (IHmore_sels _ _ _ _ _ H8); intros.
    left; constructor; auto.
    right. inversion_clear H1. inversion_clear H2. rename x into C2'.
    exists (eta;; C2'). split; constructor; auto.
- inversion H1.
  + right. exists C1'; split; auto. constructor; auto. rewrite <- H8; auto.
  + right. exists C2'; split; auto. constructor; auto. rewrite <- H8; auto.
  + elim (IHmore_sels1 _ _ _ _ _ H11); elim (IHmore_sels2 _ _ _ _ _ H12); intros.
    * left. constructor; auto.
    * 

Abort.

(** MOVE ME *)


Section ComputableReduction.

Require Import Sumbool.

Notation "A '&&&' B" := (sumbool_and _ _ _ _ A B).

Fixpoint compatible (Defs:DefSet) (s:State) (tl:RichLabel) (C:Choreography) : Prop :=
  (match C, tl with
  | Call X,           R_Call Y p       => X = Y /\ In p (fst (Defs X))
  | RT_Call X ps C',  R_Call Y p       => (X = Y /\ In p ps)
                                          \/ (~In p ps /\ compatible Defs s tl C')
  | RT_Call X ps C',  R_Com p _ q _    => disjoint (p::q::nil) ps /\ compatible Defs s tl C'
  | RT_Call X ps C',  R_Sel p q _      => disjoint (p::q::nil) ps /\ compatible Defs s tl C'
  | RT_Call X ps C',  R_Cond p         => ~In p ps /\ compatible Defs s tl C'
  | Com p e q x;; C', R_Com p' v q' x' => (p=p' /\ q=q' /\ x=x' /\ v=eval_on_state e s p)
                                          \/ (disjoint (p::q::nil) (p'::q'::nil) /\ compatible Defs s tl C')
  | Com p _ q _;; C', R_Sel p' q' _    => (disjoint (p::q::nil) (p'::q'::nil) /\ compatible Defs s tl C')
  | Com p _ q _;; C', R_Cond p'        => (~In p' (p::q::nil) /\ compatible Defs s tl C')
  | Com p _ q _;; C', R_Call Y p'      => (~In p' (p::q::nil) /\ compatible Defs s tl C')
  | Sel p q l;; C',   R_Sel p' q' l'   => (p=p' /\ q=q' /\ l=l')
                                          \/ (disjoint (p::q::nil) (p'::q'::nil) /\ compatible Defs s tl C')
  | Sel p q _;; C',   R_Com p' _ q' _  => (disjoint (p::q::nil) (p'::q'::nil) /\ compatible Defs s tl C')
  | Sel p q _;; C',   R_Cond p'        => (~In p' (p::q::nil) /\ compatible Defs s tl C')
  | Sel p q _;; C',   R_Call Y p'      => (~In p' (p::q::nil) /\ compatible Defs s tl C')
  | Cond p e C1 C2,   R_Cond p'        => (p=p')
                                          \/ (p<>p' /\ compatible Defs s tl C1 /\ compatible Defs s tl C2)
  | Cond p _ C1 C2,   R_Com p' _ q' _  => (~In p (p'::q'::nil) /\ compatible Defs s tl C1 /\ compatible Defs s tl C2)
  | Cond p _ C1 C2,   R_Sel p' q' _    => (~In p (p'::q'::nil) /\ compatible Defs s tl C1 /\ compatible Defs s tl C2)
  | Cond p _ C1 C2,   R_Call Y p'      => (p<>p' /\ compatible Defs s tl C1 /\ compatible Defs s tl C2)
  | _,                _                => False
end)%MC.

(*
Fixpoint reduce_C (Defs:DefSet) (C:Choreography) (s:State) (tl:RichLabel) :=
  (match C, tl with
  | Call X,           R_Call Y p       => if (R.eq_dec X Y &&& In_dec P.eq_dec p (fst (Defs X)))
                                            then (if (Nat.eq_dec (length (fst (Defs X))) 1)
                                                  then snd (Defs X)
                                                  else (RT_Call X (set_remove_pid p (fst (Defs X))) (snd (Defs X))))
                                            else End
  | RT_Call X ps C',  R_Call Y p       => if (R.eq_dec X Y &&& In_dec P.eq_dec p ps)
                                          then (if (Nat.eq_dec (length ps) 1)
                                                then C'
                                                else (RT_Call X (set_remove_pid p ps) C'))
                                          else End
  | Com p e q x;; C', R_Com p' v q' x' => if (P.eq_dec p p' &&& P.eq_dec q q' &&& V.eq_dec (eval_on_state e s p) v)
                                          then C'
                                          else if disjoint_dec _ P.eq_dec (p::q::nil) (p'::q'::nil)
                                               then reduce_C Defs C' s tl
                                               else End
  | Com p _ q _;; C', R_Sel p' q' _    => if (disjoint_dec _ P.eq_dec (p::q::nil) (p'::q'::nil))
                                          then reduce_C Defs C' s tl
                                          else End
  | Com p _ q _;; C', R_Cond p'        => if (In_dec P.eq_dec p' (p::q::nil))
                                          then End
                                          else reduce_C Defs C' s tl
  | Com p _ q _;; C', R_Call _ p'      => if (In_dec P.eq_dec p' (p::q::nil))
                                          then End
                                          else reduce_C Defs C' s tl
  | Sel p q l;; C',   R_Sel p' q' l'   => if (P.eq_dec p p' &&& P.eq_dec q q' &&& eq_label_dec l l')
                                          then C'
                                          else if disjoint_dec _ P.eq_dec (p::q::nil) (p'::q'::nil)
                                               then reduce_C Defs C' s tl
                                               else End
  | Sel p q _;; C',   R_Com p' _ q' _  => if (disjoint_dec _ P.eq_dec (p::q::nil) (p'::q'::nil))
                                          then reduce_C Defs C' s tl
                                          else End
  | Sel p q _;; C',   R_Cond p'        => if (In_dec P.eq_dec p' (p::q::nil))
                                          then End
                                          else reduce_C Defs C' s tl
  | Sel p q _;; C',   R_Call _ p'      => if (In_dec P.eq_dec p' (p::q::nil))
                                          then End
                                          else reduce_C Defs C' s tl
  | Cond p b C1 C2,   R_Cond p'        => if P.eq_dec p p'
                                          then if beval_on_state b s p
                                               then C1 else C2
                                          else If p ? b Then (reduce_C Defs C1 s tl) Else (reduce_C Defs C2 s tl)
  | Cond p b C1 C2,   R_Com p' _ q' _  => if In_dec P.eq_dec p (p'::q'::nil)
                                          then End
                                          else If p ? b Then (reduce_C Defs C1 s tl) Else (reduce_C Defs C2 s tl)
  | Cond p b C1 C2,   R_Sel p' q' _    => if In_dec P.eq_dec p (p'::q'::nil)
                                          then End
                                          else If p ? b Then (reduce_C Defs C1 s tl) Else (reduce_C Defs C2 s tl)
  | Cond p b C1 C2,   R_Call _ p'      => if P.eq_dec p p'
                                          then End
                                          else If p ? b Then (reduce_C Defs C1 s tl) Else (reduce_C Defs C2 s tl)
  | _, _ => End
end)%MC.
*)

Fixpoint reduce_C (Defs:DefSet) (C:Choreography) (s:State) (tl:RichLabel) :=
  (match C, tl with
  | Call X,           R_Call _ p       => if Nat.eq_dec (set_size_pid (fst (Defs X))) 1
                                          then snd (Defs X)
                                          else RT_Call X (set_remove_pid p (fst (Defs X))) (snd (Defs X))
  | RT_Call X ps C',  R_Call Y p       => if In_dec P.eq_dec p ps
                                          then if Nat.eq_dec (set_size_pid ps) 1
                                               then C'
                                               else RT_Call X (set_remove_pid p ps) C'
                                          else RT_Call X ps (reduce_C Defs C' s tl)
  | RT_Call X ps C',  _                => RT_Call X ps (reduce_C Defs C' s tl)
  | Com p e q x;; C', R_Com p' v q' x' => if (P.eq_dec p p' &&& P.eq_dec q q' &&& V.eq_dec (eval_on_state e s p) v)
                                          then C'
                                          else Com p e q x;; reduce_C Defs C' s tl
  | Com p e q x;; C', _                => Com p e q x;; reduce_C Defs C' s tl
  | Sel p q l;; C',   R_Sel p' q' l'   => if (P.eq_dec p p' &&& P.eq_dec q q' &&& eq_label_dec l l')
                                          then C'
                                          else Sel p q l;; reduce_C Defs C' s tl
  | Sel p q l;; C',   _                => Sel p q l;; reduce_C Defs C' s tl
  | Cond p b C1 C2,   R_Cond p'        => if P.eq_dec p p'
                                          then if beval_on_state b s p
                                               then C1 else C2
                                          else If p ? b Then (reduce_C Defs C1 s tl) Else (reduce_C Defs C2 s tl)
  | Cond p b C1 C2,   _                => If p ? b Then (reduce_C Defs C1 s tl) Else (reduce_C Defs C2 s tl)
  | _, _ => End
  end)%MC.

Definition reduce_S (s:State) (tl:RichLabel) :=
  match tl with
  | R_Com _ v q x => update s q x v
  | _             => s
  end.

Lemma reduce_sound : forall Defs C s tl, MCP_WF (Build_Program Defs C) ->
  compatible Defs s tl C -> MCC_To Defs C s tl (reduce_C Defs C s tl) (reduce_S s tl).
Proof.
induction C; intros; induction tl; try inversion H0; simpl.
- rewrite <- H1. elim Nat.eq_dec; intros.
  + apply C_Call_Local'; auto.
  + apply C_Call_Start'; auto.
    elim (not_eq _ _ b); intros; auto.
    inversion H3. 2: inversion H5.
    elim (MCP_WF_Vars _ H r); auto.
    red; simpl; auto. unfold Vars; simpl. eapply set_size_0; eauto.
- apply C_Delay_Call; auto.
    2: { apply IHC; auto. eapply MCP_WF_Call; eauto. }
    clear H2 H0 H s IHC C r Defs.
    induction l; simpl; auto.
    split. split; intro; eapply H1; simpl; eauto.
    apply IHl; repeat intro. inversion_clear H.
    apply (H1 a0); split; simpl; auto.
- apply C_Delay_Call; auto.
    2: { apply IHC; auto. eapply MCP_WF_Call; eauto. }
    clear H2 H0 H s IHC C r Defs.
    induction l; simpl; auto.
    split. split; intro; eapply H1; simpl; eauto.
    apply IHl; repeat intro. inversion_clear H.
    apply (H1 a0); split; simpl; auto.
- apply C_Delay_Call; auto.
    2: { apply IHC; auto. eapply MCP_WF_Call; eauto. }
    clear H2 H0 H s IHC C r Defs.
    induction l; simpl; auto.
    split. intro; eapply H1; simpl; eauto.
    apply IHl; repeat intro. apply H1; simpl; auto.
- inversion_clear H1. rewrite H2. elim in_dec; [elim Nat.eq_dec | idtac]; intros.
  + apply C_Call_Finish'; auto.
  + apply C_Call_Enter'; auto.
    elim (not_eq _ _ b); intros; auto.
    inversion H1. 2: inversion H5.
    generalize (MCP_WF_Main _ H); simpl; intros.
    inversion H4. inversion H7.
    apply set_size_0 in H5. elim H8; auto.
  + elim b; auto.
- inversion_clear H1. elim in_dec; intros.
  + exfalso; auto.
  + apply C_Delay_Call; auto.
    2: { apply IHC; auto. eapply MCP_WF_Call; eauto. }
    clear b H3 H0 H IHC.
    induction l; simpl; auto.
    simpl in H2. split; auto.
- induction e.
  + inversion H0. inversion_clear H1. inversion_clear H3. inversion_clear H4.
    * rewrite H5, H2, H1, H3. clear H2 H1 H3 H5 H0.
      elim P.eq_dec; intro Hp. 2: elim Hp; auto.
      elim P.eq_dec; intro Hq. 2: elim Hq; auto.
      elim V.eq_dec; intro Hv. 2: elim Hv; auto.
      apply C_Com'.
    * inversion_clear H1. red in H2.
      elim P.eq_dec; intro Hp. elim (H2 p); rewrite Hp; simpl; auto.
      elim P.eq_dec; intro Hq. elim (H2 q); rewrite Hq; simpl; auto.
      elim V.eq_dec; intro Hv; simpl; apply C_Delay_Eta; auto.
      ++ simpl. split; split; intro; auto; eapply H2; simpl; eauto.
      ++ eapply IHC; auto. eapply MCP_WF_eta; eauto.
      ++ simpl. split; split; intro; auto; eapply H2; simpl; eauto.
      ++ eapply IHC; auto. eapply MCP_WF_eta; eauto.
  + inversion_clear H0. apply C_Delay_Eta; auto.
      ++ simpl. split; split; intro; auto; eapply H1; simpl; eauto.
         split; right; left; eauto.
      ++ eapply IHC; auto. eapply MCP_WF_eta; eauto.
- induction e.
  + inversion_clear H0. apply C_Delay_Eta; auto.
      ++ simpl. split; split; intro; auto; eapply H1; simpl; eauto.
         split; right; left; eauto.
      ++ eapply IHC; auto. eapply MCP_WF_eta; eauto.
  + inversion H0. inversion_clear H1. inversion_clear H3. inversion_clear H4.
    * rewrite H2, H1. clear H2 H1.
      elim P.eq_dec; intro Hp. 2: elim Hp; auto.
      elim P.eq_dec; intro Hq. 2: elim Hq; auto.
      elim eq_label_dec; intro Hl. 2: elim Hl; auto.
      apply C_Sel'.
    * inversion_clear H1. red in H2.
      elim P.eq_dec; intro Hp. elim (H2 p); rewrite Hp; simpl; auto.
      elim P.eq_dec; intro Hq. elim (H2 q); rewrite Hq; simpl; auto.
      elim eq_label_dec; intro Hl; simpl; apply C_Delay_Eta; auto.
      ++ simpl. split; split; intro; auto; eapply H2; simpl; eauto.
      ++ eapply IHC; auto. eapply MCP_WF_eta; eauto.
      ++ simpl. split; split; intro; auto; eapply H2; simpl; eauto.
      ++ eapply IHC; auto. eapply MCP_WF_eta; eauto.
- induction e.
  + inversion H0. apply C_Delay_Eta.
    * simpl. split; intro; auto; eapply H1; simpl; eauto.
    * eapply IHC; auto. eapply MCP_WF_eta; eauto.
  + inversion H0. apply C_Delay_Eta.
    * simpl. split; intro; auto; eapply H1; simpl; eauto.
    * eapply IHC; auto. eapply MCP_WF_eta; eauto.
- induction e.
  + inversion H0. apply C_Delay_Eta.
    * simpl. split; intro; auto; eapply H1; simpl; eauto.
    * eapply IHC; auto. eapply MCP_WF_eta; eauto.
  + inversion H0. apply C_Delay_Eta.
    * simpl. split; intro; auto; eapply H1; simpl; eauto.
    * eapply IHC; auto. eapply MCP_WF_eta; eauto.
- inversion_clear H2.
  apply C_Delay_Cond.
  + split; intro; eapply H1; simpl; eauto.
  + eapply IHC1; auto. eapply MCP_WF_Then; eauto.
  + eapply IHC2; auto. eapply MCP_WF_Else; eauto.
- inversion_clear H2.
  apply C_Delay_Cond.
  + split; intro; eapply H1; simpl; eauto.
  + eapply IHC1; auto. eapply MCP_WF_Then; eauto.
  + eapply IHC2; auto. eapply MCP_WF_Else; eauto.
- elim P.eq_dec; intro Hp. 2: elim Hp; auto.
  case_eq (beval_on_state b s p); intro Hb; rewrite <- Hp.
  + apply C_Then'; auto.
  + apply C_Else'; auto.
- inversion_clear H1. inversion_clear H3.
  elim P.eq_dec; intro Hp. elim H2; auto.
  apply C_Delay_Cond; auto.
  + eapply IHC1; auto. eapply MCP_WF_Then; eauto.
  + eapply IHC2; auto. eapply MCP_WF_Else; eauto.
- inversion_clear H2.
  apply C_Delay_Cond; auto.
  + eapply IHC1; auto. eapply MCP_WF_Then; eauto.
  + eapply IHC2; auto. eapply MCP_WF_Else; eauto.
Qed.

Lemma reduce_compatible : forall Defs C s tl C' s',
  MCC_To Defs C s tl C' s' -> compatible Defs s tl C.
Proof.
intros.
induction H; simpl; auto.
+ induction eta; induction t; simpl; auto.
  * right; split; auto.
    apply disjoint_Com_Com in H; auto.
  * split; auto. apply disjoint_Com_Sel in H; auto.
  * split; auto. intro.
    inversion_clear H. inversion_clear H1; auto.
    inversion_clear H; auto.
  * split; auto. intro.
    inversion_clear H. inversion_clear H1; auto.
    inversion_clear H; auto.
  * split; auto. apply disjoint_Sel_Sel in H; auto.
  * right; split; auto.
    apply disjoint_Sel_Sel in H; auto.
  * split; auto. intro.
    inversion_clear H. inversion_clear H1; auto.
    inversion_clear H; auto.
  * split; auto. intro.
    inversion_clear H. inversion_clear H1; auto.
    inversion_clear H; auto.
+ induction t; simpl; auto.
  * repeat split; auto. intro.
    inversion_clear H. inversion_clear H2; auto.
    inversion_clear H; auto.
  * repeat split; auto. intro.
    inversion_clear H. inversion_clear H2; auto.
    inversion_clear H; auto.
+ induction t; simpl; auto.
  * split; auto. apply disjoint_ps_Com in H; auto.
  * split; auto. apply disjoint_ps_Sel in H; auto.
  * split; auto. apply disjoint_ps_Cond; auto.
  * apply disjoint_ps_Call in H; auto.
Qed.

Lemma reduce_unique_1 : forall Defs C s tl C' s',
  MCP_WF (Build_Program Defs C) ->
  MCC_To Defs C s tl C' s' -> C' = reduce_C Defs C s tl.
Proof.
intros.
eapply MCC_To_deterministic_1; eauto.
apply reduce_sound; auto.
eapply reduce_compatible; eauto.
Qed.
*)

End ComputableReduction.
