Require Export EPP.

Local Open Scope nat_scope.

(** * The EPP Theorem *)

Section EPP_Theorem.

Local Ltac sup := rewrite set_union_iff; auto.

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
Notation PR := (DecProd RecVar Pid).
Notation Sig' := (Sig' Sig).

Open Scope CC.

Section Completeness.

(** ** Completeness
  The completeness part of the EPP theorem. *)

Lemma EPP_Complete : forall P ps,
  Program_WF _ P -> well_ann _ P -> forall (HP:projectable Sig ps P),
  (forall p, In p ps -> str_proj (Procedures _ P) (Main P) p) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In p (Vars P X) -> In p ps) ->
  forall s tl P' s', (P,s) --[tl]--> (P',s') ->
  exists N tl', ((epp ps P HP,s) --[tl']--> (N,s'))%SP
    /\ Procs N = Procs (epp ps P HP)
    /\ forall H, Net N (>>) Net (epp ps P' H).
Proof.
intros P ps HWF Hann HP Hsp HMain HXs s tl P' s' HTo.
induction P as (D,C), P' as (D',C').
generalize (CCP_To_Defs_stable _ D D' C C' tl s s' HTo); intro.
rewrite <- H in HTo; rewrite <- H; clear D' H.
simpl in Hsp, HMain.
set (N' := epp _ _ HP). assert (N' = epp _ _ HP) as HN; auto.
clearbody N'; induction N' as (D',N).
assert (projectable_C D C ps) as HC.
1: apply str_proj_C'; auto.
induction tl; intros; inversion HTo; induction t; inversion H3.
+ rewrite H9, H8, H7 in H0.
  clear q0 v0 p0 s'0 C'0 s0 C0 D0 H9 H8 H7 H5 H4 H3 H2 H1 H.
  generalize (CCC_To_pn _ _ _ _ _ _ _ H0); intro.
  assert (In p ps) as Hp.
  1: { apply HMain, H. simpl; auto. }
  assert (In q ps) as Hq.
  1: { apply HMain, H. simpl; auto. }
  assert (p <> q) as Hpq.
  1: { eapply CCC_To_Com_neq; eauto. apply HWF. }
  clear H.
  elim (CCC_To_bproj_Com_p _ D C s C' s' p q v x); auto.
  intros e [a [Bp [HBp [HBp' Hv] ] ] ].
  elim (CCC_To_bproj_Com_q _ D C s C' s' p q v x); auto.
  intros a' [Bq [HBq HBq'] ].
  exists (D',fun r => if (eq_dec r p) then Bp else if (eq_dec r q) then Bq else N r),
  (@forget Pid Value Var PR (RL_Com p v q x)).
  repeat split; auto.
  - apply (@SPP_Base Sig'). rewrite Hv. apply S_Com with (a:ann Sig') Bp a' Bq.
    * replace N with (Net (D',N)); auto.
      rewrite HN. eapply bproj_unique; eauto.
      apply epp_C_char'; auto.
    * replace N with (Net (D',N)); auto.
      rewrite HN. eapply bproj_unique; eauto.
      apply epp_C_char'; auto.
    * intro r. elim eq_dec; intro H5.
      rewrite H5. symmetry; apply Network_rm_add_2_p; auto.
      elim eq_dec; intro H6. rewrite H6.
      symmetry; apply Network_rm_add_2_q; auto.
      rewrite Network_rm_add_2_out; auto.
    * apply CCC_To_Com_state with D C p C'.
      rewrite Hv in H0; auto.
  - simpl; intros H5 r.
    replace N with (Net (D',N)); auto.
    elim eq_dec; intro H6.
    2: elim eq_dec; intro H7.
    3: elim (In_dec (@eq_dec Pid) r ps); intro.
    * rewrite H6.
      apply MB_refl'.
      eapply bproj_unique; eauto.
      apply epp_C_char'; auto.
    * rewrite H7.
      apply MB_refl'.
      eapply bproj_unique; eauto.
      apply epp_C_char'; auto.
    * replace (Net (epp _ _ H5) r) with (N r).
      apply MB_refl.
      replace N with (Net (D',N)); auto.
      rewrite HN.
      elim (CCC_To_bproj_Com_r _ D C s C' s' p q v x r); auto.
      intros B [HB HB'].
      etransitivity; eapply bproj_unique.
      1,4: apply epp_C_char'; auto. all: eauto.
    * replace (Net (epp _ _ H5) r) with (End Sig').
      simpl. replace (N r) with (End Sig'). constructor.
      replace N with (Net (D',N)); auto.
      rewrite HN, epp_C_char with (HC:=HC), epp_C_out; auto.
      elim (CCP_To_projectable _ (D,C) ps)
        with s (TL_Com p v q) (D,C') s'; intros; auto.
      rewrite epp_C_char with (HC:=H), epp_C_out; auto.
      eauto.
+ rewrite H9, H8, H7 in H0.
  clear q0 l0 p0 s'0 C'0 s0 C0 D0 H9 H8 H7 H5 H4 H3 H2 H1 H.
  generalize (CCC_To_pn _ _ _ _ _ _ _ H0); intro.
  assert (In p ps) as Hp.
  1: { apply HMain, H. simpl; auto. }
  assert (In q ps) as Hq.
  1: { apply HMain, H. simpl; auto. }
  assert (p <> q) as Hpq.
  1: { eapply CCC_To_Sel_neq; eauto. apply HWF. }
  clear H.
  elim (CCC_To_bproj_Sel_p _ D C s C' s' p q l); auto.
  intros a [Bp [HBp HBp'] ].
  induction l.
  1: elim (CCC_To_bproj_Sel_ql _ D C s C' s' p q); auto.
  2: elim (CCC_To_bproj_Sel_qr _ D C s C' s' p q); auto.
  all: intros a' [Bq [HBq1 HBq2] ].
  exists (D',fun r => if (eq_dec r p) then Bp else if (eq_dec r q) then Bq else N r),
  (@forget Pid Value Var PR (RL_Sel p q left)).
  2: exists (D',fun r => if (eq_dec r p) then Bp else if (eq_dec r q) then Bq else N r),
  (@forget Pid Value Var PR (RL_Sel p q right)).
  all: repeat split; auto.
  1,3: apply (@SPP_Base Sig').
  2: apply S_RSel with (a:ann Sig') Bp a' None Bq.
  1: apply S_LSel with (a:ann Sig') Bp a' Bq None.
  1,2,5,6: replace N with (Net (D',N)); auto.
  1,2,3,4: eapply bproj_unique; eauto.
  1,2,3,4: rewrite HN; apply epp_C_char'; auto.
  1,3: intro r; case eq_dec; intro H4;
    [rewrite H4; symmetry; apply Network_rm_add_2_p; auto
    | case eq_dec; intro H5;
      [ rewrite H5; auto; symmetry; apply Network_rm_add_2_q; auto
        | rewrite Network_rm_add_2_out; auto] ].
  1: apply CCC_To_Sel_state with D C p q left C'; auto.
  1: apply CCC_To_Sel_state with D C p q right C'; auto.
  1,2: simpl; intros H5 r;
    replace N with (Net (D',N)); auto;
    case eq_dec; intro H4;
    [idtac | case eq_dec; intro H6;
      [idtac | elim (In_dec (@eq_dec Pid) r ps); intro] ].
    all: try rewrite H4.
    all: try rewrite H6.
    1,2,5,6: apply MB_refl'; eapply bproj_unique; eauto.
    1,2,3,4: apply epp_C_char'; auto.
    1: induction (CCC_To_bproj_Sel_r _ D C s C' s' p q left r) as [B [HB HB'] ]; auto.
    3: induction (CCC_To_bproj_Sel_r _ D C s C' s' p q right r) as [B [HB HB'] ]; auto.
    1,3: apply MB_refl'; transitivity (N r); auto;
        replace N with (Net (D',N)); auto; rewrite HN;
        etransitivity; eapply bproj_unique.
    1,4,5,8: apply epp_C_char'; auto. 1,2,3,4: eauto.
    1,2: replace (Net (epp _ _ H5) r) with (End Sig').
    1,3: simpl; replace (N r) with (End Sig').
    1,3: constructor.
    1,2: replace N with (Net (D',N)); auto;
      rewrite HN, epp_C_char with (HC:=HC), epp_C_out; auto.
    1: elim (CCP_To_projectable _ (D,C) ps)
        with s (TL_Sel p q left) (D,C') s'; intros;
       eauto; rewrite epp_C_char with (HC:=H), epp_C_out; auto.
    1: elim (CCP_To_projectable _ (D,C) ps)
        with s (TL_Sel p q right) (D,C') s'; intros;
       eauto; rewrite epp_C_char with (HC:=H), epp_C_out; auto.
+ rewrite H7 in H0.
  clear p0 s'0 C'0 s0 C0 H7 H5 H4 H3 H2 H1 D0 H.
  generalize (CCC_To_pn _ _ _ _ _ _ _ H0); intro.
  assert (In p ps) as Hp.
  1: { apply HMain, H. simpl; auto. }
  clear H.
  elim (CCC_To_bproj_Cond_p _ D C s C' s' p); auto.
  intros b [Bt [Be [HB [HBt HBe] ] ] ].
  case_eq (eval_on_state BEv b s p); intro Hb.
  1: exists (D',fun r => if (eq_dec r p) then Bt else N r),
    (@forget Pid Value Var PR (RL_Cond p)).
  2: exists (D',fun r => if (eq_dec r p) then Be else N r),
    (@forget Pid Value Var PR (RL_Cond p)).
  1,2: repeat split; auto.
  1,3: apply (@SPP_Base Sig').
  1: apply (@S_Then Sig') with b Bt Be; auto.
  4: apply (@S_Else Sig') with b Bt Be; auto.
  1,4: replace N with (Net (D',N)); auto;
       eapply bproj_unique; eauto;
       rewrite HN; apply epp_C_char'; auto.
  1,3: intro r; case eq_dec; intro H3;
      [ rewrite H3, Par_proj2;
        [ symmetry; apply Process_refl | apply Network_rm_In]
      | symmetry; rewrite Par_proj1'; auto;
        [apply Network_rm_out; auto
        | apply Process_out; auto] ].
  1,2: apply CCC_To_Cond_state with D C p C'; auto.
  all: simpl; intros H5 r; replace N with (Net (D',N)); auto.
  all: case eq_dec; intro H3; [idtac | elim (In_dec (@eq_dec Pid) r ps); intro].
  all: try rewrite H3.
  * apply MB_refl'.
    eapply bproj_unique; eauto.
    apply epp_C_char'; auto.
  * rewrite HN. assert (p <> r) as Hpr; auto.
    elim (CCC_To_bproj_Cond_r Sig _ _ _ _ _ _ r (Hsp _ a) H0 Hpr).
    intros B [B' [HB'' [HB' H'] ] ].
    replace (Net (epp _ _ HP) r) with B.
    replace (Net (epp _ _ H5) r) with B'; auto.
    eapply bproj_unique; eauto. apply epp_C_char'; auto.
    eapply bproj_unique; eauto. apply epp_C_char'; auto.
  * replace (Net (epp _ _ H5) r) with (End Sig').
    simpl. replace (N r) with (End Sig'). constructor.
    replace N with (Net (D',N)); auto.
    rewrite HN, epp_C_char with (HC:=HC), epp_C_out; auto.
    elim (CCP_To_projectable _ (D,C) ps)
      with s (TL_Tau p) (D,C') s'; intros; auto.
    rewrite epp_C_char with (HC:=H), epp_C_out; auto.
    eauto.
  * apply MB_refl'.
    eapply bproj_unique; eauto.
    apply epp_C_char'; auto.
  * rewrite HN. assert (p <> r) as Hpr; auto.
    elim (CCC_To_bproj_Cond_r Sig _ _ _ _ _ _ r (Hsp _ a) H0 Hpr).
    intros B [B' [HB'' [HB' H'] ] ].
    replace (Net (epp _ _ HP) r) with B.
    replace (Net (epp _ _ H5) r) with B'; auto.
    eapply bproj_unique; eauto. apply epp_C_char'; auto.
    eapply bproj_unique; eauto. apply epp_C_char'; auto.
  * replace (Net (epp _ _ H5) r) with (End Sig').
    simpl. replace (N r) with (End Sig'). constructor.
    replace N with (Net (D',N)); auto.
    rewrite HN, epp_C_char with (HC:=HC), epp_C_out; auto.
    elim (CCP_To_projectable _ (D,C) ps)
      with s (TL_Tau p) (D,C') s'; intros; auto.
    rewrite epp_C_char with (HC:=H), epp_C_out; auto.
    eauto.
+ rewrite H7 in H0.
  clear p0 s'0 C'0 s0 C0 D0 H7 H5 H4 H3 H2 H1 H.
  generalize (CCC_To_pn _ _ _ _ _ _ _ H0); intro.
  assert (In p ps) as Hp.
  1: { apply HMain, H. simpl; auto. }
  clear H.
  elim (CCC_To_bproj_Call_p _ D C s C' s' p X); auto.
  2: { intros; eapply Program_WF_D_str_proj with (P:=(D,C)); eauto. }
  intros HX' [B [B' [HB [HB' H'] ] ] ].
  inversion_clear HP. destroy H1.
  specialize (H2 X); clear H3 H4 H1.
  exists (D',fun r => if (eq_dec r p) then B else N r),
    (forget (@RL_Call Pid Value Var PR (X,p) p)).
  repeat split.
  - apply (@SPP_Base Sig'), (@S_Call Sig').
    * replace N with (Net (D',N)); auto.
      eapply bproj_unique; eauto.
      rewrite HN. apply epp_C_char'; auto.
    * intro r. case eq_dec; intro Hr.
      rewrite Hr, Par_proj2, Process_refl.
      replace D' with (Procs (D',N)); auto.
      rewrite HN. eapply bproj_unique; eauto.
      apply epp_D_char'; auto. apply Hann.
      apply Network_rm_In.
      symmetry; rewrite Par_proj1'; auto.
      apply Network_rm_out; auto.
      apply Process_out; auto.
    * apply CCC_To_Call_state with D C p X C'; auto.
  - simpl; intros H5 r.
    replace N with (Net (D',N)); auto.
    case eq_dec; intro Hr.
    * rewrite Hr.
      elim (CCC_To_bproj_Call_p _ D C s C' s' p X); auto.
      intros HX'' [B1 [B2 [HB1 [HB2 HB12] ] ] ].
      rewrite (bproj_unique _ _ _ _ _ _ HB1 HB) in *; clear B1 HB1.
      rewrite (bproj_unique _ _ _ _ _ _ HB2 HB') in *; clear B2 HB2.
      erewrite bproj_unique; eauto.
      apply epp_C_char'; auto.
      intros. eapply Program_WF_D_str_proj with (P:=(D,C)); eauto.
    * elim (In_dec (@eq_dec Pid) r ps); intro Hr'.
      apply MB_refl'. transitivity (N r); auto.
      replace N with (Net (D',N)); auto.
      elim (CCC_To_bproj_Call_r _ D C s C' s' p X r); auto.
      intros B0 [HB0 HB0'].
      rewrite HN. etransitivity; eapply bproj_unique.
      1,4: apply epp_C_char'; auto. 1,2: eauto.
      rewrite HN.
      repeat rewrite epp_out; auto. constructor.
Qed.

Lemma EPP_Complete' : forall P ps,
  Program_WF _ P -> well_ann _ P -> forall (HP:projectable Sig ps P),
  (forall p, In p ps -> str_proj (Procedures _ P) (Main P) p) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In p (Vars P X) -> In p ps) ->
  forall s tl P' s', (P,s) --[tl]-->* (P',s') ->
  exists N tl', ((epp ps P HP,s) --[tl']-->* (N,s'))%SP
  /\ forall H, Net N (>>) Net (epp ps P' H).
Proof.
intros P ps HWF Hann HP Hinit HMain HXs s tl P' s' HTo.
assert (forall p, In p ps -> str_proj (Procedures _ P) (Main P) p) as Hsp.
1: { auto. }
induction P as (D,C), P' as (D',C').
generalize (CCP_ToStar_Defs_stable _ D D' C C' tl s s' HTo); intro.
rewrite <- H in HTo; rewrite <- H; clear D' H.
simpl in Hsp, HMain. clear Hinit.
revert dependent C'. revert dependent C. revert s s'. induction tl.
+ intros. inversion HTo.
  exists (epp _ _ HP), nil; repeat split.
  apply (SPT_Base Sig'). auto.
  rewrite <- H0. intros; apply MBN_refl'.
  intro. inversion HP.
  rewrite epp_C_char with (HC:=H5). rewrite epp_C_char with (HC:=H5).
  auto.
+ intros. inversion HTo. clear HTo.
  rewrite <- H in H2; clear a H l H0 c1 H1 c3 H3.
  induction c2 as ((D',C''),s'').
  generalize (CCP_To_Defs_stable _ D D' _ _ _ _ _ H2); intro.
  rewrite <- H in H2, H4; clear D' H.
  elim EPP_Complete with (HP:=HP) (s:=s) (s':=s'') (tl:=t)
    (P':=(D,C'')); auto.
  intros. destroy H. rename x into pP, x0 into t'.
  assert (projectable Sig ps (D,C'')) as HP''.
  1: {
    inversion HP. simpl in H5; destroy H5.
    repeat split; auto.
    apply str_proj_C'.
    eapply CCP_To_str_proj; eauto.
    intros. apply HMain. change C with (Main (D,C)).
    eapply CCP_To_pn; eauto.
    eapply CCC_pn_mon. 2: apply H9. simpl; tauto.
  }
  elim IHtl with (s:=s'') (s':=s') (C:=C'') (C':=C') (HP:=HP''); auto.
  - intros. destroy H3. rename x into pP', x0 into tl'.
    apply SPP_ToStar_MBN with (P1':=pP) in H5.
    destroy H5.
    exists x, (t'::tl'). repeat split; auto.
    apply SPT_Step with (pP,s''); auto.
    intro. apply MBN_trans with (Net pP'); auto.
    auto.
    intro. rewrite H1.
    inversion HP''. simpl in H7; clear H6; destroy H7.
    induction X. repeat rewrite epp_D_char with (HD:=H6); auto.
  - eapply CCP_To_Program_WF; eauto.
  - intros. apply HMain. change C with (Main (D,C)).
    eapply CCP_To_pn; eauto.
  - change C'' with (Main (D,C'')).
    change D with (Procedures _ (D,C'')).
    intros. eapply CCP_To_str_proj; eauto.
Qed.

Lemma EPP_Complete'' : forall P ps,
  Program_WF _ P -> well_ann _ P -> forall (HP:projectable Sig ps P),
  initial (Main P) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X,In p (Vars P X) -> In p ps) ->
  forall s tl P' s', (P,s) --[tl]-->* (P',s') ->
  exists N tl', ((epp ps P HP,s) --[tl']-->* (N,s'))%SP
  /\ forall H, Net N (>>) Net (epp ps P' H).
Proof.
intros; apply EPP_Complete' with tl; auto.
apply initial_str_proj, HP; auto.
Qed.

End Completeness.

Section Soundness.

(** * Soundness of EPP
  Soundness is proven by case analysis on the label of the reduction, and
  then by induction on the choreography. We split the proofs for each label
  in separate results, as we get some stronger statements. *)

Open Scope SP_scope.

Definition SP_eq (P P':Program Sig') : Prop :=
  forall X, Procs P X = Procs P' X /\ (Net P (==) Net P')%SP.

Lemma SP_To_bproj_Com : forall D D' ps C HC s N' s' p x q v,
  (forall p, In p ps -> @str_proj Sig D C p) ->
  (forall p, In p (CCC_pn C (Names D)) -> In p ps) ->
  <<epp_C D ps C HC,s>> --[RL_Com p v q x,D']--> <<N',s'>> ->
  exists C', (<<C,s>> --[RL_Com p v q x,D]--> <<C',s'>>)%CC
  /\ forall HC', (N' (==) (epp_C D ps C' HC')).
Proof.
intros.
rename H into Hsp, H0 into Hin, H1 into H.
revert v N' H.
induction C; intros. induction e.
+ inversion H. rewrite <- H1 in H. unfold v1; unfold v1 in H, H11.
  clear s'0 H8 N'0 H7 x0 H3 q0 H2 v v1 H1 p0 H0 s0 H5.
  rename t into a'', t0 into p', t2 into q', t1 into e0, t3 into v'.
  elim ((@eq_dec Pid) p p'); intro Hpp'.
  - clear IHC Hsp Hin.
    revert HC H H6 H9 H10 H4. rewrite <- Hpp'. clear p' Hpp'. intros.
    (* get the remaining equalities *)
    assert (In p ps /\ q = q' /\ e = e0).
    1: {
      revert H6.
      unfold epp_C. elim In_dec; simpl; intro.
      2: discriminate.
      elim bproj_dec. induction a1; simpl; intro.
      rewrite H6 in p0; inversion p0; tauto.
      (* absurd case *)
      clear H H9 H10 H4. intro; exfalso; contr_aux HC.
    }
    destroy H0. rename H1 into Hpps.
    revert HC H4 H10 H9 H6 H H11. rewrite <- H2, <- H0.
    clear q' H2 e0 H0; intros.
    assert (p <> q) as Hpq.
    1: {
      pattern p at 2 in H6.
      intro H'; rewrite H', H9 in H6; inversion H6.
    }
    assert (In q ps /\ x = v').
    1: {
      revert H9.
      unfold epp_C. elim In_dec; simpl; intro.
      2: discriminate.
      elim bproj_dec. induction a1; simpl; intro.
      rewrite H9 in p0; inversion p0; tauto.
      (* absurd case *)
      clear H H6 H10 H4. intro. exfalso. contr_aux HC.
    }
    destroy H0.
    revert dependent HC. rewrite <- H0. clear v' H0; intros.
    rename H1 into Hqps.
    exists C; repeat split.
    1: apply (@C_Com Sig); auto.
    intros. eapply Network_eq_trans. apply H10.
    intro r.
    case ((@eq_dec Pid) p r); intro Hpr.
    2: case ((@eq_dec Pid) q r); intro Hqr.
    * rewrite <- Hpr, Network_rm_add_2_p; auto.
      rewrite epp_C_Com_p with (HC':=HC') in H6; auto.
      inversion H6; auto.
    * rewrite <- Hqr, Network_rm_add_2_q; auto.
      rewrite epp_C_Com_q with (HC':=HC') in H9; auto.
      inversion H9; auto.
    * rewrite Network_rm_add_2_out; auto.
      apply epp_C_Com_r; auto.
  - generalize (projectable_C_inv_Com Sig D ps p' e0 q' v' a'' C HC); intro HC'.
    (* get the remaining equalities *)
    assert (In p ps) as Hpps.
    1: { revert H6. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
    assert (In q ps) as Hqps.
    1: { revert H9. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
    assert (p' <> q) as Hp'q.
    1: intro. rewrite <- H0, epp_C_Com_p with (HC':=HC') in H9; auto.
      inversion H9. rewrite H0; auto.
    assert (q' <> p) as Hq'p.
    1: intro. rewrite <- H0, epp_C_Com_q with (HC':=HC') in H6.
      inversion H6. rewrite H0; auto. rewrite H0; auto.
    assert (q' <> q) as Hq'q.
    1: intro. rewrite <- H0, epp_C_Com_q with (HC':=HC') in H9.
      inversion H9. apply Hpp'; auto. 1,2: rewrite H0; auto.
    assert (p <> q) as Hpq.
    1: { intro H'; rewrite H', H9 in H6; inversion H6. }
    assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
    1: intros. apply Hin. simpl; sup.
    elim (IHC HC' Hsp Hin' (eval_on_state Ev e s p) ((epp_C D ps C HC' \ p \ q | p[B] | q[B'])%SP)); intros.
    rename x0 into C'. destroy H0.
    exists (p' # e0 --> q' $ v' @ a'';; C'); repeat split.
    * apply (@C_Delay_Eta Sig); repeat split; auto.
    * intros. eapply Network_eq_trans. apply H10. rewrite <- H4.
      set (H':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC'0).
      set (H'':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC).
      intro r. elim ((@eq_dec Pid) p r); intro Hpr.
      2: elim ((@eq_dec Pid) q r); intro Hqr.
      3: rewrite Network_rm_add_2_out, H4; auto.
      3: elim (In_dec (@eq_dec Pid) r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
      3: elim ((@eq_dec Pid) p' r); intro Hp'r.
      4: elim ((@eq_dec Pid) q' r); intro Hq'r.
      ++ rewrite <- Hpr, Network_rm_add_2_p; auto.
         rewrite epp_C_Com_r with (HC':=H'); auto.
         rewrite <- H0, Network_rm_add_2_p; auto.
      ++ rewrite <- Hqr, Network_rm_add_2_q; auto.
         rewrite epp_C_Com_r with (HC':=H'); auto.
         rewrite <- H0, Network_rm_add_2_q; auto.
      ++ rewrite <- Hp'r; intro.
         rewrite epp_C_Com_p with (HC':=H'), epp_C_Com_p with (HC':=H''); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
      ++ rewrite <- Hq'r; intro. rewrite <- Hq'r in Hp'r.
         rewrite epp_C_Com_q with (HC':=H'), epp_C_Com_q with (HC':=H''); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
      ++ rewrite epp_C_Com_r with (HC':=H'), epp_C_Com_r with (HC':=H''); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
    * apply S_Com with (a:ann Sig') B a' B'; auto.
      rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC) in H6; inversion H6; auto.
      apply epp_C_wd.
      rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC) in H9; inversion H9; auto.
      apply epp_C_wd.
      apply Network_eq_refl.
+ inversion H. rewrite <- H1 in H. unfold v1; unfold v1 in H, H11.
  clear s'0 H8 N'0 H7 x0 H3 q0 H2 v v1 H1 p0 H0 s0 H5.
  rename t into a'', t0 into p', t1 into q', t2 into l.
  generalize (projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC); intro HC'.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H6. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (In q ps) as Hqps.
  1: { revert H9. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H0, epp_C_Sel_p with (HC':=HC') in H6; auto.
    inversion H6. rewrite H0; auto.
  assert (p' <> q) as Hp'q.
  1: intro. rewrite <- H0, epp_C_Sel_p with (HC':=HC') in H9; auto.
    inversion H9. rewrite H0; auto.
  assert (q' <> p) as Hq'p.
  1: intro. induction l.
    1: rewrite <- H0, epp_C_Sel_ql with (HC':=HC') in H6.
    4: rewrite <- H0, epp_C_Sel_qr with (HC':=HC') in H6.
    1,4: inversion H6. 1,2,3,4: rewrite H0; auto.
  assert (q' <> q) as Hq'q.
  1: intro. induction l.
    1: rewrite <- H0, epp_C_Sel_ql with (HC':=HC') in H9.
    4: rewrite <- H0, epp_C_Sel_qr with (HC':=HC') in H9.
    1,4: inversion H9. 1,2,3,4: rewrite H0; auto.
  assert (p <> q) as Hpq.
  1: { intro H'; rewrite H', H9 in H6; inversion H6. }
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (eval_on_state Ev e s p) (epp_C D ps C HC' \ p \ q | p[B] | q[B']))%SP; intros.
  rename x0 into C'. destroy H0.
  exists (p' --> q'[l] @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros. eapply Network_eq_trans. apply H10. rewrite <- H4.
    set (H' := projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC'0).
    set (H'' := projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC).
    intro r. elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim ((@eq_dec Pid) q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec (@eq_dec Pid) r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
    3: elim ((@eq_dec Pid) p' r); intro Hp'r.
    4: elim ((@eq_dec Pid) q' r); intro Hq'r.
    - rewrite <- Hpr, Network_rm_add_2_p; auto.
      rewrite epp_C_Sel_r with (HC':=H'); auto.
      rewrite <- H0, Network_rm_add_2_p; auto.
    - rewrite <- Hqr, Network_rm_add_2_q; auto.
      rewrite epp_C_Sel_r with (HC':=H'); auto.
      rewrite <- H0, Network_rm_add_2_q; auto.
    - rewrite <- Hp'r; intro.
      rewrite epp_C_Sel_p with (HC':=H'), epp_C_Sel_p with (HC':=H''); auto.
      rewrite <- H0; auto.
      rewrite Network_rm_add_2_out; auto.
      rewrite epp_C_wd with (H':=HC'); auto.
    - rewrite <- Hq'r; intro. rewrite <- Hq'r in Hp'r.
      induction l.
      1: rewrite epp_C_Sel_ql with (HC':=H'), epp_C_Sel_ql with (HC':=H''); auto.
      2: rewrite epp_C_Sel_qr with (HC':=H'), epp_C_Sel_qr with (HC':=H''); auto.
      all: rewrite <- H0, Network_rm_add_2_out; auto.
      all: rewrite epp_C_wd with (H':=HC'); auto.
    - rewrite epp_C_Sel_r with (HC':=H'), epp_C_Sel_r with (HC':=H''); auto.
      rewrite <- H0; auto.
      rewrite Network_rm_add_2_out; auto.
      rewrite epp_C_wd with (H':=HC'); auto.
  * apply S_Com with (a:ann Sig') B a' B'; auto.
    rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC) in H6; inversion H6; auto.
    apply epp_C_wd.
    rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC) in H9; inversion H9; auto.
    apply epp_C_wd.
    apply Network_eq_refl.
+ inversion H. rewrite <- H1 in H. unfold v1; unfold v1 in H, H11.
  clear s'0 H8 N'0 H7 x0 H3 q0 H2 v v1 H1 p0 H0 s0 H5.
  rename t into p', t0 into b.
  generalize (projectable_C_inv_Then Sig _ _ _ _ _ _ HC); intro HC1.
  generalize (projectable_C_inv_Else Sig _ _ _ _ _ _ HC); intro HC2.
  assert (forall p, In p ps -> str_proj D C1 p) as Hsp1.
  1: apply Hsp.
  assert (forall p, In p ps -> str_proj D C2 p) as Hsp2.
  1: apply Hsp.
  clear Hsp.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H6. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (In q ps) as Hqps.
  1: { revert H9. unfold epp_C. elim In_dec; simpl; auto.
    discriminate.
  }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H0, epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H6; auto.
    inversion H6. rewrite H0; auto.
  assert (p' <> q) as Hp'q.
  1: intro. rewrite <- H0, epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H9; auto.
    inversion H9. rewrite H0; auto.
  assert (p <> q) as Hpq.
  1: { intro H'; rewrite H', H9 in H6; inversion H6. }
  elim (epp_C_Cond_Send_inv Sig _ _ _ _ _ _ HC HC1 HC2 _ _ _ _ _ H6).
  intros. destroy H0. rename x0 into Bp1, x1 into Bp2, H1 into Hp1, H2 into Hp2, H0 into Hp'.
  elim (epp_C_Cond_Recv_inv Sig _ _ _ _ _ _ HC HC1 HC2 _ _ _ _ _ H9).
  intros. destroy H0. rename x0 into Bq1, x1 into Bq2, H1 into Hq1, H2 into Hq2, H0 into Hq'.
  assert (forall p, In p (CCC_pn C1 (Names D)) -> In p ps) as Hin1.
  1: intros. apply Hin. simpl; sup; sup.
  assert (forall p, In p (CCC_pn C2 (Names D)) -> In p ps) as Hin2.
  1: intros. apply Hin. simpl; sup; sup.
  elim (IHC1 HC1 Hsp1 Hin1 (eval_on_state Ev e s p) (epp_C D ps C1 HC1 \ p \ q | p[Bp1] | q[Bq1]))%SP; intros.
  rename x0 into C1'. destroy H0.
  elim (IHC2 HC2 Hsp2 Hin2 (eval_on_state Ev e s p) (Network_rm _ (Network_rm _ (epp_C D ps C2 HC2) p) q | p[Bp2] | q[Bq2]))%SP; intros.
  rename x0 into C2'. destroy H2. clear IHC1 IHC2.
  exists (If p' ?? b Then C1' Else C2'); repeat split.
  * apply C_Delay_Cond; repeat split; auto.
  * intros. eapply Network_eq_trans. apply H10. rewrite <- H4.
    intro r. elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim ((@eq_dec Pid) q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec (@eq_dec Pid) r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
    3: elim ((@eq_dec Pid) p' r); intro Hp'r.
    - rewrite <- Hpr in *; clear r Hpr.
      rewrite Network_rm_add_2_p; auto.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then Sig _ _ _ _ _ _ HC')
                                   (HC2:=projectable_C_inv_Else Sig _ _ _ _ _ _ HC'); auto.
      intros. specialize (H5 _ _ HC' _ Hp'p).
      rewrite <- H0, <- H2, Network_rm_add_2_p, Network_rm_add_2_p in H5; auto.
      eapply merge_unique; eauto.
    - rewrite <- Hqr in *; clear r Hqr.
      rewrite Network_rm_add_2_q; auto.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then Sig _ _ _ _ _ _ HC')
                                   (HC2:=projectable_C_inv_Else Sig _ _ _ _ _ _ HC'); auto.
      intros. specialize (H5 _ _ HC' _ Hp'q).
      rewrite <- H0, <- H2, Network_rm_add_2_q, Network_rm_add_2_q in H5; auto.
      eapply merge_unique; eauto.
    - rewrite <- Hp'r in *; clear r Hp'r; intros.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then Sig _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else Sig _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H2, Network_rm_add_2_out, Network_rm_add_2_out; auto.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then Sig _ _ _ _ _ _ HC)
                                (HC2:=projectable_C_inv_Else Sig _ _ _ _ _ _ HC); auto.
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2); auto.
    - intro.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then Sig _ _ _ _ _ _ HC')
                                   (HC2:=projectable_C_inv_Else Sig _ _ _ _ _ _ HC'); auto.
      intros. specialize (H5 _ _ HC' _ Hp'r).
      rewrite <- H0, <- H2, Network_rm_add_2_out, Network_rm_add_2_out in H5; auto.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then Sig _ _ _ _ _ _ HC)
                                   (HC2:=projectable_C_inv_Else Sig _ _ _ _ _ _ HC); auto.
      intros. specialize (H7 _ _ HC _ Hp'r).
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2) in H7; auto.
      eapply merge_unique; eauto.
  * apply S_Com with (a:ann Sig') Bp2 a' Bq2; auto.
    apply Network_eq_refl.
  * apply S_Com with (a:ann Sig') Bp1 a' Bq1; auto.
    apply Network_eq_refl.
+ exfalso.
  inversion H.
  elim (In_dec (@eq_dec Pid) p ps); intros.
  elim (In_dec (@eq_dec Pid) p (fst (D t))); intros.
  rewrite epp_C_Call in H6; auto. inversion H6.
  rewrite epp_C_Call_out in H6; auto. inversion H6.
  rewrite epp_C_out in H6; auto. inversion H6.
+ inversion H. rewrite <- H1 in H. unfold v1; unfold v1 in H, H11.
  clear s'0 H8 N'0 H7 x0 H3 q0 H2 v v1 H1 p0 H0 s0 H5.
  rename l into ps', t into X.
  assert (projectable_C D C ps) as HC'.
  1: { red. rewrite Forall_forall. intros.
    elim (Hsp x0); auto; intros.
    apply str_proj_C; auto.
  }
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H6. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (In q ps) as Hqps.
  1: { revert H9. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (~In p ps') as Hp.
  1: intro. rewrite epp_C_RT_Call in H6; auto. inversion H6.
  assert (~In q ps') as Hq.
  1: intro. rewrite epp_C_RT_Call in H9; auto. inversion H9.
  assert (p <> q) as Hpq.
  1: { intro H'; rewrite H', H9 in H6; inversion H6. }
  assert (forall p, In p ps -> str_proj D C p) as Hsp'.
  1: apply Hsp.
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp' Hin' (eval_on_state Ev e s p) (Network_rm _ (Network_rm _ (epp_C D ps C HC') p) q | p[B] | q[B']))%SP; intros.
  rename x0 into C'. destroy H0.
  exists (RT_Call X ps' C'); repeat split.
  * apply C_Delay_Call; repeat split; auto.
    apply disjoint_ps_char. simpl.
    intros r Hr. split; intro H'; rewrite H' in Hr; auto.
  * intros. eapply Network_eq_trans. apply H10. rewrite <- H4.
    assert (projectable_C D C' ps).
    1: apply str_proj_C'; intros. eapply CCC_To_str_proj_Com; eauto.
    intro r. elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim ((@eq_dec Pid) q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec (@eq_dec Pid) r ps); intro Hr1.
    3: elim (In_dec (@eq_dec Pid) r ps'); intro Hr2.
    - rewrite <- Hpr, Network_rm_add_2_p; auto.
      rewrite epp_C_RT_Call_out with (HC':=H2); auto.
      rewrite <- H0, Network_rm_add_2_p; auto.
    - rewrite <- Hqr, Network_rm_add_2_q; auto.
      rewrite epp_C_RT_Call_out with (HC':=H2); auto.
      rewrite <- H0, Network_rm_add_2_q; auto.
    - repeat rewrite epp_C_RT_Call; auto.
    - rewrite epp_C_RT_Call_out with (HC':=H2); auto.
      rewrite epp_C_RT_Call_out with (HC':=HC'); auto.
      rewrite <- H0; auto.
      rewrite Network_rm_add_2_out; auto.
    - repeat rewrite epp_C_out; auto.
  * apply S_Com with (a:ann Sig') B a' B'; auto.
    rewrite epp_C_RT_Call_out with (HC':=HC') in H6; inversion H6; auto.
    rewrite epp_C_RT_Call_out with (HC':=HC') in H9; inversion H9; auto.
    apply Network_eq_refl.
+ exfalso.
  inversion H.
  rewrite epp_C_End in H6. inversion H6.
Qed.

Lemma SP_To_bproj_Sel_l : forall D D' ps C HC s N' s' p q,
  (forall p, In p ps -> @str_proj Sig D C p) ->
  (forall p, In p (CCC_pn C (Names D)) -> In p ps) ->
  <<epp_C D ps C HC,s>> --[RL_Sel p q left,D']--> <<N',s'>> ->
  exists C', (<<C,s>> --[RL_Sel p q left,D]--> <<C',s'>>)%CC
  /\ forall HC', (N' (==) (epp_C D ps C' HC')).
Proof.
intros.
rename H into Hsp, H0 into Hin, H1 into H.
revert N' H.
induction C; intros. induction e.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  rename t into a'', t0 into p', t2 into q', t1 into e, t3 into v'.
  generalize (projectable_C_inv_Com Sig D ps p' e q' v' a'' C HC); intro HC'.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H2. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (In q ps) as Hqps.
  1: { revert H3. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H0, epp_C_Com_p with (HC':=HC') in H2; auto.
    inversion H2. rewrite H0; auto.
  assert (p' <> q) as Hp'q.
  1: intro. rewrite <- H0, epp_C_Com_p with (HC':=HC') in H3; auto.
    inversion H3. rewrite H0; auto.
  assert (q' <> q) as Hq'q.
  1: intro. rewrite <- H0, epp_C_Com_q with (HC':=HC') in H3.
    inversion H3. 1,2: rewrite H0; auto.
  assert (q' <> p) as Hq'p.
  1: intro. rewrite <- H0, epp_C_Com_q with (HC':=HC') in H2.
    inversion H2. 1,2: rewrite H0; auto.
  assert (p <> q) as Hpq.
  1: { intro H'; rewrite H', H3 in H2; inversion H2. }
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (Network_rm _ (Network_rm _ (epp_C D ps C HC') p) q | p[B] | q[Bl])); intros.
  rename x into C'. destroy H0.
  exists (p' # e --> q' $ v' @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros. eapply Network_eq_trans. apply H6. rewrite <- H4.
    intro r. elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim ((@eq_dec Pid) q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec (@eq_dec Pid) r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
    3: elim ((@eq_dec Pid) p' r); intro Hp'r.
    4: elim ((@eq_dec Pid) q' r); intro Hq'r.
    ++ rewrite <- Hpr, Network_rm_add_2_p; auto.
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite <- H0, Network_rm_add_2_p; auto.
    ++ rewrite <- Hqr, Network_rm_add_2_q; auto.
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite <- H0, Network_rm_add_2_q; auto.
    ++ rewrite <- Hp'r; intro.
       rewrite epp_C_Com_p with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_p with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
    ++ rewrite <- Hq'r; intro. rewrite <- Hq'r in Hp'r.
       rewrite epp_C_Com_q with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_q with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
    ++ rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
  * apply S_LSel with (a:ann Sig') B a' Bl Br; auto.
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC) in H2; inversion H2; auto.
    apply epp_C_wd.
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC) in H3; auto.
    etransitivity. 2: apply H3.
    apply epp_C_wd.
    apply Network_eq_refl.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  rename t into a'', t0 into p', t1 into q', t2 into l.
  elim ((@eq_dec Pid) p p'); intro Hpp'.
  - clear IHC Hsp Hin.
    revert HC H H2 H3 H6 H4. rewrite <- Hpp'. clear p' Hpp'. intros.
    (* get the remaining equalities *)
    assert (In p ps /\ q = q' /\ l = left).
    1: {
      revert H2.
      unfold epp_C. elim In_dec; simpl; intro.
      2: discriminate.
      elim bproj_dec. induction a1; simpl; intro.
      rewrite H2 in p0; inversion p0; tauto.
      (* absurd case *)
      clear H H3 H6 H4. intro; exfalso; contr_aux HC.
    }
    destroy H0. rename H1 into Hpps.
    revert HC H4 H6 H2 H3 H. rewrite H0, <- H5.
    clear q' H0 l H5; intros.
    assert (p <> q) as Hpq.
    1: {
      pattern p at 2 in H2.
      intro H'; rewrite H', H3 in H2; inversion H2.
    }
    assert (In q ps) as Hqps.
    1: { revert H3. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
    exists C; repeat split.
    1: apply (@C_Sel Sig); auto.
    intros. eapply Network_eq_trans; eauto.
    intro r.
    case ((@eq_dec Pid) p r); intro Hpr.
    2: case ((@eq_dec Pid) q r); intro Hqr.
    * rewrite <- Hpr, Network_rm_add_2_p; auto.
      rewrite epp_C_Sel_p with (HC':=HC') in H2; auto.
      inversion H2; auto.
    * rewrite <- Hqr, Network_rm_add_2_q; auto.
      rewrite epp_C_Sel_ql with (HC':=HC') in H3; auto.
      inversion H3; auto.
    * rewrite Network_rm_add_2_out; auto.
      apply epp_C_Sel_r; auto.
  - generalize (projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC); intro HC'.
    (* get the remaining equalities *)
    assert (In p ps) as Hpps.
    1: { revert H2. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
    assert (In q ps) as Hqps.
    1: { revert H3. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
    assert (p' <> p) as Hp'p.
    1: intro. rewrite <- H0, epp_C_Sel_p with (HC':=HC') in H2; auto.
      inversion H2. rewrite H0; auto.
    assert (p' <> q) as Hp'q.
    1: intro. rewrite <- H0, epp_C_Sel_p with (HC':=HC') in H3; auto.
      inversion H3. rewrite H0; auto.
    assert (q' <> p) as Hq'p.
    1: intro. induction l.
      1: rewrite <- H0, epp_C_Sel_ql with (HC':=HC') in H2.
      4: rewrite <- H0, epp_C_Sel_qr with (HC':=HC') in H2.
      1,4: inversion H2. 1,2,3,4: rewrite H0; auto.
    assert (q' <> q) as Hq'q.
    1: intro. induction l.
      1: rewrite <- H0, epp_C_Sel_ql with (HC':=HC') in H3.
      4: rewrite <- H0, epp_C_Sel_qr with (HC':=HC') in H3.
      1,4: inversion H3; auto. 1,2,3,4: rewrite H0; auto.
    assert (p <> q) as Hpq.
    1: { intro H'; rewrite H', H3 in H2; inversion H2. }
    assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
    1: intros. apply Hin. simpl; sup.
    elim (IHC HC' Hsp Hin' (Network_rm _ (Network_rm _ (epp_C D ps C HC') p) q | p[B] | q[Bl])); intros.
    rename x into C'. destroy H0.
    exists (p' --> q'[l] @ a'';; C'); repeat split.
    * apply C_Delay_Eta; repeat split; auto.
    * intros. eapply Network_eq_trans. apply H6. rewrite <- H4.
      intro r. elim ((@eq_dec Pid) p r); intro Hpr.
      2: elim ((@eq_dec Pid) q r); intro Hqr.
      3: rewrite Network_rm_add_2_out, H4; auto.
      3: elim (In_dec (@eq_dec Pid) r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
      3: elim ((@eq_dec Pid) p' r); intro Hp'r.
      4: elim ((@eq_dec Pid) q' r); intro Hq'r.
      ++ rewrite <- Hpr, Network_rm_add_2_p; auto.
         rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC'0); auto.
         rewrite <- H0, Network_rm_add_2_p; auto.
      ++ rewrite <- Hqr, Network_rm_add_2_q; auto.
        rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC'0); auto.
        rewrite <- H0, Network_rm_add_2_q; auto.
      ++ rewrite <- Hp'r; intro.
         rewrite epp_C_Sel_p with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC'0); auto.
         rewrite epp_C_Sel_p with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
      ++ rewrite <- Hq'r; intro. rewrite <- Hq'r in Hp'r.
          induction l.
         1: rewrite epp_C_Sel_ql with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC'0); auto.
         1: rewrite epp_C_Sel_ql with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC); auto.
         2: rewrite epp_C_Sel_qr with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC'0); auto.
         2: rewrite epp_C_Sel_qr with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC); auto.
         all: rewrite <- H0, Network_rm_add_2_out; auto.
         all: rewrite epp_C_wd with (H':=HC'); auto.
      ++ rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC'0); auto.
         rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
    * apply S_LSel with (a:ann Sig') B a' Bl Br; auto.
      rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC) in H2; inversion H2; auto.
      apply epp_C_wd.
      rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC) in H3; auto.
      etransitivity. 2: apply H3.
      apply epp_C_wd.
      apply Network_eq_refl.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  elim (epp_C_Sel_Branching_l Sig _ _ _ _ _ _ _ _ _ _ H2 H3); intros.
  rewrite H1 in H3; clear Br H1 H0.
  rename t into p', t0 into b.
  generalize (projectable_C_inv_Then Sig _ _ _ _ _ _ HC); intro HC1.
  generalize (projectable_C_inv_Else Sig _ _ _ _ _ _ HC); intro HC2.
  assert (forall p, In p ps -> str_proj D C1 p) as Hsp1.
  1: apply Hsp.
  assert (forall p, In p ps -> str_proj D C2 p) as Hsp2.
  1: apply Hsp.
  clear Hsp.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H2. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (In q ps) as Hqps.
  1: { revert H3. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H0, epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H2; auto.
    inversion H2. rewrite H0; auto.
  assert (p' <> q) as Hp'q.
  1: intro. rewrite <- H0, epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H3; auto.
    inversion H3. rewrite H0; auto.
  assert (p <> q) as Hpq.
  1: { intro H'; rewrite H', H3 in H2; inversion H2. }
  elim (epp_C_Cond_Sel_inv Sig _ _ _ _ _ _ HC HC1 HC2 _ _ _ _ _ H2).
  intros. destroy H0. rename x into Bp1, x0 into Bp2, H1 into Hp1, H5 into Hp2, H0 into Hp'.
  elim (epp_C_Cond_Branching_l_inv Sig _ _ _ _ _ _ HC HC1 HC2 _ _ _ _ H3).
  intros. destroy H0. rename x into Bq1, x0 into Bq2, H1 into Hq1, H5 into Hq2, H0 into Hq'.
  assert (forall p, In p (CCC_pn C1 (Names D)) -> In p ps) as Hin1.
  1: intros. apply Hin. simpl; sup; sup.
  assert (forall p, In p (CCC_pn C2 (Names D)) -> In p ps) as Hin2.
  1: intros. apply Hin. simpl; sup; sup.
  elim (IHC1 HC1 Hsp1 Hin1 (epp_C D ps C1 HC1 \ p \ q | p[Bp1] | q[Bq1])); intros.
  rename x into C1'. destroy H0.
  elim (IHC2 HC2 Hsp2 Hin2 (Network_rm _ (Network_rm _ (epp_C D ps C2 HC2) p) q | p[Bp2] | q[Bq2])); intros.
  rename x into C2'. destroy H5. clear IHC1 IHC2.
  exists (If p' ?? b Then C1' Else C2'); repeat split.
  * apply C_Delay_Cond; repeat split; auto.
  * intros. eapply Network_eq_trans. apply H6. rewrite <- H4.
    intro r. elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim ((@eq_dec Pid) q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec (@eq_dec Pid) r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
    3: elim ((@eq_dec Pid) p' r); intro Hp'r.
    - rewrite <- Hpr in *; clear r Hpr.
      rewrite Network_rm_add_2_p; auto.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then Sig _ _ _ _ _ _ HC')
                                   (HC2:=projectable_C_inv_Else Sig _ _ _ _ _ _ HC'); auto.
      intros. specialize (H8 _ _ HC' _ Hp'p).
      rewrite <- H0, <- H5, Network_rm_add_2_p, Network_rm_add_2_p in H8; auto.
      eapply merge_unique; eauto.
    - rewrite <- Hqr in *; clear r Hqr.
      rewrite Network_rm_add_2_q; auto.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then Sig _ _ _ _ _ _ HC')
                                   (HC2:=projectable_C_inv_Else Sig _ _ _ _ _ _ HC'); auto.
      intros. specialize (H8 _ _ HC' _ Hp'q).
      rewrite <- H0, <- H5, Network_rm_add_2_q, Network_rm_add_2_q in H8; auto.
      eapply merge_unique; eauto.
    - rewrite <- Hp'r in *; clear r Hp'r; intros.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then Sig _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else Sig _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H5, Network_rm_add_2_out, Network_rm_add_2_out; auto.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then Sig _ _ _ _ _ _ HC)
                                (HC2:=projectable_C_inv_Else Sig _ _ _ _ _ _ HC); auto.
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2); auto.
    - intro.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then Sig _ _ _ _ _ _ HC')
                                   (HC2:=projectable_C_inv_Else Sig _ _ _ _ _ _ HC'); auto.
      intros. specialize (H8 _ _ HC' _ Hp'r).
      rewrite <- H0, <- H5, Network_rm_add_2_out, Network_rm_add_2_out in H8; auto.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then Sig _ _ _ _ _ _ HC)
                                   (HC2:=projectable_C_inv_Else Sig _ _ _ _ _ _ HC); auto.
      intros. specialize (H10 _ _ HC _ Hp'r).
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2) in H10; auto.
      eapply merge_unique; eauto.
  * apply S_LSel with (a:ann Sig') Bp2 a' Bq2 None; auto.
    apply Network_eq_refl.
  * apply S_LSel with (a:ann Sig') Bp1 a' Bq1 None; auto.
    apply Network_eq_refl.
+ exfalso.
  inversion H.
  elim (In_dec (@eq_dec Pid) p ps); intros.
  elim (In_dec (@eq_dec Pid) p (fst (D t))); intros.
  rewrite epp_C_Call in H2; auto. inversion H2.
  rewrite epp_C_Call_out in H2; auto. inversion H2.
  rewrite epp_C_out in H2; auto. inversion H2.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  rename l into ps', t into X.
  assert (projectable_C D C ps) as HC'.
  1: { red. rewrite Forall_forall. intros.
    elim (Hsp x); auto; intros.
    apply str_proj_C; auto.
  }
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H2. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (In q ps) as Hqps.
  1: { revert H3. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (~In p ps') as Hp.
  1: intro. rewrite epp_C_RT_Call in H2; auto. inversion H2.
  assert (~In q ps') as Hq.
  1: intro. rewrite epp_C_RT_Call in H3; auto. inversion H3.
  assert (p <> q) as Hpq.
  1: { intro H'; rewrite H', H3 in H2; inversion H2. }
  assert (forall p, In p ps -> str_proj D C p) as Hsp'.
  1: apply Hsp.
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp' Hin' (Network_rm _ (Network_rm _ (epp_C D ps C HC') p) q | p[B] | q[Bl])); intros.
  rename x into C'. destroy H0.
  exists (RT_Call X ps' C'); repeat split.
  * apply C_Delay_Call; repeat split; auto.
    apply disjoint_ps_char. simpl.
    intros r Hr. split; intro H'; rewrite H' in Hr; auto.
  * intros. eapply Network_eq_trans. apply H6. rewrite <- H4.
    assert (projectable_C D C' ps).
    1: apply str_proj_C'; intros. eapply CCC_To_str_proj_Sel; eauto.
    intro r. elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim ((@eq_dec Pid) q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec (@eq_dec Pid) r ps); intro Hr1.
    3: elim (In_dec (@eq_dec Pid) r ps'); intro Hr2.
    - rewrite <- Hpr, Network_rm_add_2_p; auto.
      rewrite epp_C_RT_Call_out with (HC':=H5); auto.
      rewrite <- H0, Network_rm_add_2_p; auto.
    - rewrite <- Hqr, Network_rm_add_2_q; auto.
      rewrite epp_C_RT_Call_out with (HC':=H5); auto.
      rewrite <- H0, Network_rm_add_2_q; auto.
    - repeat rewrite epp_C_RT_Call; auto.
    - rewrite epp_C_RT_Call_out with (HC':=H5); auto.
      rewrite epp_C_RT_Call_out with (HC':=HC'); auto.
      rewrite <- H0; auto.
      rewrite Network_rm_add_2_out; auto.
    - repeat rewrite epp_C_out; auto.
  * apply S_LSel with (a:ann Sig') B a' Bl Br; auto.
    rewrite epp_C_RT_Call_out with (HC':=HC') in H2; inversion H2; auto.
    rewrite epp_C_RT_Call_out with (HC':=HC') in H3; inversion H3; auto.
    apply Network_eq_refl.
+ exfalso.
  inversion H.
  rewrite epp_C_End in H2. inversion H2.
Qed.

Lemma SP_To_bproj_Sel_r : forall D D' ps C HC s N' s' p q,
  (forall p, In p ps -> @str_proj Sig D C p) ->
  (forall p, In p (CCC_pn C (Names D)) -> In p ps) ->
  <<epp_C D ps C HC,s>> --[RL_Sel p q right,D']--> <<N',s'>> ->
  exists C', (<<C,s>> --[RL_Sel p q right,D]--> <<C',s'>>)%CC
  /\ forall HC', (N' (==) (epp_C D ps C' HC')).
Proof.
intros.
rename H into Hsp, H0 into Hin, H1 into H.
revert N' H.
induction C; intros. induction e.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  rename t into a'', t0 into p', t2 into q', t1 into e, t3 into v'.
  generalize (projectable_C_inv_Com Sig D ps p' e q' v' a'' C HC); intro HC'.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H2. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (In q ps) as Hqps.
  1: { revert H3. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H0, epp_C_Com_p with (HC':=HC') in H2; auto.
    inversion H2. rewrite H0; auto.
  assert (p' <> q) as Hp'q.
  1: intro. rewrite <- H0, epp_C_Com_p with (HC':=HC') in H3; auto.
    inversion H3. rewrite H0; auto.
  assert (q' <> q) as Hq'q.
  1: intro. rewrite <- H0, epp_C_Com_q with (HC':=HC') in H3.
    inversion H3. 1,2: rewrite H0; auto.
  assert (q' <> p) as Hq'p.
  1: intro. rewrite <- H0, epp_C_Com_q with (HC':=HC') in H2.
    inversion H2. 1,2: rewrite H0; auto.
  assert (p <> q) as Hpq.
  1: { intro H'; rewrite H', H3 in H2; inversion H2. }
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (Network_rm _ (Network_rm _ (epp_C D ps C HC') p) q | p[B] | q[Br])); intros.
  rename x into C'. destroy H0.
  exists (p' # e --> q' $ v' @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros. eapply Network_eq_trans. apply H6. rewrite <- H4.
    intro r. elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim ((@eq_dec Pid) q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec (@eq_dec Pid) r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
    3: elim ((@eq_dec Pid) p' r); intro Hp'r.
    4: elim ((@eq_dec Pid) q' r); intro Hq'r.
    ++ rewrite <- Hpr, Network_rm_add_2_p; auto.
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite <- H0, Network_rm_add_2_p; auto.
    ++ rewrite <- Hqr, Network_rm_add_2_q; auto.
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite <- H0, Network_rm_add_2_q; auto.
    ++ rewrite <- Hp'r; intro.
       rewrite epp_C_Com_p with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_p with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
    ++ rewrite <- Hq'r; intro. rewrite <- Hq'r in Hp'r.
       rewrite epp_C_Com_q with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_q with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
    ++ rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
  * apply S_RSel with (a:ann Sig') B a' Bl Br; auto.
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC) in H2; inversion H2; auto.
    apply epp_C_wd.
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC) in H3; auto.
    etransitivity. 2: apply H3.
    apply epp_C_wd.
    apply Network_eq_refl.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  rename t into a'', t0 into p', t1 into q', t2 into l.
  elim ((@eq_dec Pid) p p'); intro Hpp'.
  - clear IHC Hsp Hin.
    revert HC H H2 H3 H6 H4. rewrite <- Hpp'. clear p' Hpp'. intros.
    (* get the remaining equalities *)
    assert (In p ps /\ q = q' /\ l = right).
    1: {
      revert H2.
      unfold epp_C. elim In_dec; simpl; intro.
      2: discriminate.
      elim bproj_dec. induction a1; simpl; intro.
      rewrite H2 in p0; inversion p0; tauto.
      (* absurd case *)
      clear H H3 H6 H4. intro; exfalso; contr_aux HC.
    }
    destroy H0. rename H1 into Hpps.
    revert HC H4 H6 H2 H3 H. rewrite H0, <- H5.
    clear q' H0 l H5; intros.
    assert (p <> q) as Hpq.
    1: {
      pattern p at 2 in H2.
      intro H'; rewrite H', H3 in H2; inversion H2.
    }
    assert (In q ps) as Hqps.
    1: { revert H3. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
    exists C; repeat split.
    1: apply (@C_Sel Sig); auto.
    intros. eapply Network_eq_trans; eauto.
    intro r.
    case ((@eq_dec Pid) p r); intro Hpr.
    2: case ((@eq_dec Pid) q r); intro Hqr.
    * rewrite <- Hpr, Network_rm_add_2_p; auto.
      rewrite epp_C_Sel_p with (HC':=HC') in H2; auto.
      inversion H2; auto.
    * rewrite <- Hqr, Network_rm_add_2_q; auto.
      rewrite epp_C_Sel_qr with (HC':=HC') in H3; auto.
      inversion H3; auto.
    * rewrite Network_rm_add_2_out; auto.
      apply epp_C_Sel_r; auto.
  - generalize (projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC); intro HC'.
    (* get the remaining equalities *)
    assert (In p ps) as Hpps.
    1: { revert H2. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
    assert (In q ps) as Hqps.
    1: { revert H3. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
    assert (p' <> p) as Hp'p.
    1: intro. rewrite <- H0, epp_C_Sel_p with (HC':=HC') in H2; auto.
      inversion H2. rewrite H0; auto.
    assert (p' <> q) as Hp'q.
    1: intro. rewrite <- H0, epp_C_Sel_p with (HC':=HC') in H3; auto.
      inversion H3. rewrite H0; auto.
    assert (q' <> p) as Hq'p.
    1: intro. induction l.
      1: rewrite <- H0, epp_C_Sel_ql with (HC':=HC') in H2.
      4: rewrite <- H0, epp_C_Sel_qr with (HC':=HC') in H2.
      1,4: inversion H2. 1,2,3,4: rewrite H0; auto.
    assert (q' <> q) as Hq'q.
    1: intro. induction l.
      1: rewrite <- H0, epp_C_Sel_ql with (HC':=HC') in H3.
      4: rewrite <- H0, epp_C_Sel_qr with (HC':=HC') in H3.
      1,4: inversion H3; auto. 1,2,3,4: rewrite H0; auto.
    assert (p <> q) as Hpq.
    1: { intro H'; rewrite H', H3 in H2; inversion H2. }
    assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
    1: intros. apply Hin. simpl; sup.
    elim (IHC HC' Hsp Hin' (Network_rm _ (Network_rm _ (epp_C D ps C HC') p) q | p[B] | q[Br])); intros.
    rename x into C'. destroy H0.
    exists (p' --> q'[l] @ a'';; C'); repeat split.
    * apply C_Delay_Eta; repeat split; auto.
    * intros. eapply Network_eq_trans. apply H6. rewrite <- H4.
      intro r. elim ((@eq_dec Pid) p r); intro Hpr.
      2: elim ((@eq_dec Pid) q r); intro Hqr.
      3: rewrite Network_rm_add_2_out, H4; auto.
      3: elim (In_dec (@eq_dec Pid) r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
      3: elim ((@eq_dec Pid) p' r); intro Hp'r.
      4: elim ((@eq_dec Pid) q' r); intro Hq'r.
      ++ rewrite <- Hpr, Network_rm_add_2_p; auto.
         rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC'0); auto.
         rewrite <- H0, Network_rm_add_2_p; auto.
      ++ rewrite <- Hqr, Network_rm_add_2_q; auto.
        rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC'0); auto.
        rewrite <- H0, Network_rm_add_2_q; auto.
      ++ rewrite <- Hp'r; intro.
         rewrite epp_C_Sel_p with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC'0); auto.
         rewrite epp_C_Sel_p with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
      ++ rewrite <- Hq'r; intro. rewrite <- Hq'r in Hp'r.
          induction l.
         1: rewrite epp_C_Sel_ql with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC'0); auto.
         1: rewrite epp_C_Sel_ql with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC); auto.
         2: rewrite epp_C_Sel_qr with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC'0); auto.
         2: rewrite epp_C_Sel_qr with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC); auto.
         all: rewrite <- H0, Network_rm_add_2_out; auto.
         all: rewrite epp_C_wd with (H':=HC'); auto.
      ++ rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC'0); auto.
         rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
    * apply S_RSel with (a:ann Sig') B a' Bl Br; auto.
      rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC) in H2; inversion H2; auto.
      apply epp_C_wd.
      rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC) in H3; auto.
      etransitivity. 2: apply H3.
      apply epp_C_wd.
      apply Network_eq_refl.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  elim (epp_C_Sel_Branching_r Sig _ _ _ _ _ _ _ _ _ _ H2 H3); intros.
  rewrite H0 in H3; clear Bl H1 H0.
  rename t into p', t0 into b.
  generalize (projectable_C_inv_Then Sig _ _ _ _ _ _ HC); intro HC1.
  generalize (projectable_C_inv_Else Sig _ _ _ _ _ _ HC); intro HC2.
  assert (forall p, In p ps -> str_proj D C1 p) as Hsp1.
  1: apply Hsp.
  assert (forall p, In p ps -> str_proj D C2 p) as Hsp2.
  1: apply Hsp.
  clear Hsp.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H2. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (In q ps) as Hqps.
  1: { revert H3. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H0, epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H2; auto.
    inversion H2. rewrite H0; auto.
  assert (p' <> q) as Hp'q.
  1: intro. rewrite <- H0, epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H3; auto.
    inversion H3. rewrite H0; auto.
  assert (p <> q) as Hpq.
  1: { intro H'; rewrite H', H3 in H2; inversion H2. }
  elim (epp_C_Cond_Sel_inv Sig _ _ _ _ _ _ HC HC1 HC2 _ _ _ _ _ H2).
  intros. destroy H0. rename x into Bp1, x0 into Bp2, H1 into Hp1, H5 into Hp2, H0 into Hp'.
  elim (epp_C_Cond_Branching_r_inv Sig _ _ _ _ _ _ HC HC1 HC2 _ _ _ _ H3).
  intros. destroy H0. rename x into Bq1, x0 into Bq2, H1 into Hq1, H5 into Hq2, H0 into Hq'.
  assert (forall p, In p (CCC_pn C1 (Names D)) -> In p ps) as Hin1.
  1: intros. apply Hin. simpl; sup; sup.
  assert (forall p, In p (CCC_pn C2 (Names D)) -> In p ps) as Hin2.
  1: intros. apply Hin. simpl; sup; sup.
  elim (IHC1 HC1 Hsp1 Hin1 (epp_C D ps C1 HC1 \ p \ q | p[Bp1] | q[Bq1])); intros.
  rename x into C1'. destroy H0.
  elim (IHC2 HC2 Hsp2 Hin2 (Network_rm _ (Network_rm _ (epp_C D ps C2 HC2) p) q | p[Bp2] | q[Bq2])); intros.
  rename x into C2'. destroy H5. clear IHC1 IHC2.
  exists (If p' ?? b Then C1' Else C2'); repeat split.
  * apply C_Delay_Cond; repeat split; auto.
  * intros. eapply Network_eq_trans. apply H6. rewrite <- H4.
    intro r. elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim ((@eq_dec Pid) q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec (@eq_dec Pid) r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
    3: elim ((@eq_dec Pid) p' r); intro Hp'r.
    - rewrite <- Hpr in *; clear r Hpr.
      rewrite Network_rm_add_2_p; auto.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then Sig _ _ _ _ _ _ HC')
                                   (HC2:=projectable_C_inv_Else Sig _ _ _ _ _ _ HC'); auto.
      intros. specialize (H8 _ _ HC' _ Hp'p).
      rewrite <- H0, <- H5, Network_rm_add_2_p, Network_rm_add_2_p in H8; auto.
      eapply merge_unique; eauto.
    - rewrite <- Hqr in *; clear r Hqr.
      rewrite Network_rm_add_2_q; auto.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then Sig _ _ _ _ _ _ HC')
                                   (HC2:=projectable_C_inv_Else Sig _ _ _ _ _ _ HC'); auto.
      intros. specialize (H8 _ _ HC' _ Hp'q).
      rewrite <- H0, <- H5, Network_rm_add_2_q, Network_rm_add_2_q in H8; auto.
      eapply merge_unique; eauto.
    - rewrite <- Hp'r in *; clear r Hp'r; intros.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then Sig _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else Sig _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H5, Network_rm_add_2_out, Network_rm_add_2_out; auto.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then Sig _ _ _ _ _ _ HC)
                                (HC2:=projectable_C_inv_Else Sig _ _ _ _ _ _ HC); auto.
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2); auto.
    - intro.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then Sig _ _ _ _ _ _ HC')
                                   (HC2:=projectable_C_inv_Else Sig _ _ _ _ _ _ HC'); auto.
      intros. specialize (H8 _ _ HC' _ Hp'r).
      rewrite <- H0, <- H5, Network_rm_add_2_out, Network_rm_add_2_out in H8; auto.
      specialize epp_C_Cond_r with (HC1:=projectable_C_inv_Then Sig _ _ _ _ _ _ HC)
                                   (HC2:=projectable_C_inv_Else Sig _ _ _ _ _ _ HC); auto.
      intros. specialize (H10 _ _ HC _ Hp'r).
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2) in H10; auto.
      eapply merge_unique; eauto.
  * apply S_RSel with (a:ann Sig') Bp2 a' None Bq2; auto.
    apply Network_eq_refl.
  * apply S_RSel with (a:ann Sig') Bp1 a' None Bq1; auto.
    apply Network_eq_refl.
+ exfalso.
  inversion H.
  elim (In_dec (@eq_dec Pid) p ps); intros.
  elim (In_dec (@eq_dec Pid) p (fst (D t))); intros.
  rewrite epp_C_Call in H2; auto. inversion H2.
  rewrite epp_C_Call_out in H2; auto. inversion H2.
  rewrite epp_C_out in H2; auto. inversion H2.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  rename l into ps', t into X.
  assert (projectable_C D C ps) as HC'.
  1: { red. rewrite Forall_forall. intros.
    elim (Hsp x); auto; intros.
    apply str_proj_C; auto.
  }
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H2. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (In q ps) as Hqps.
  1: { revert H3. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (~In p ps') as Hp.
  1: intro. rewrite epp_C_RT_Call in H2; auto. inversion H2.
  assert (~In q ps') as Hq.
  1: intro. rewrite epp_C_RT_Call in H3; auto. inversion H3.
  assert (p <> q) as Hpq.
  1: { intro H'; rewrite H', H3 in H2; inversion H2. }
  assert (forall p, In p ps -> str_proj D C p) as Hsp'.
  1: apply Hsp.
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp' Hin' (Network_rm _ (Network_rm _ (epp_C D ps C HC') p) q | p[B] | q[Br])); intros.
  rename x into C'. destroy H0.
  exists (RT_Call X ps' C'); repeat split.
  * apply C_Delay_Call; repeat split; auto.
    apply disjoint_ps_char. simpl.
    intros r Hr. split; intro H'; rewrite H' in Hr; auto.
  * intros. eapply Network_eq_trans. apply H6. rewrite <- H4.
    assert (projectable_C D C' ps).
    1: apply str_proj_C'; intros. eapply CCC_To_str_proj_Sel; eauto.
    intro r. elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim ((@eq_dec Pid) q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec (@eq_dec Pid) r ps); intro Hr1.
    3: elim (In_dec (@eq_dec Pid) r ps'); intro Hr2.
    - rewrite <- Hpr, Network_rm_add_2_p; auto.
      rewrite epp_C_RT_Call_out with (HC':=H5); auto.
      rewrite <- H0, Network_rm_add_2_p; auto.
    - rewrite <- Hqr, Network_rm_add_2_q; auto.
      rewrite epp_C_RT_Call_out with (HC':=H5); auto.
      rewrite <- H0, Network_rm_add_2_q; auto.
    - repeat rewrite epp_C_RT_Call; auto.
    - rewrite epp_C_RT_Call_out with (HC':=H5); auto.
      rewrite epp_C_RT_Call_out with (HC':=HC'); auto.
      rewrite <- H0; auto.
      rewrite Network_rm_add_2_out; auto.
    - repeat rewrite epp_C_out; auto.
  * apply S_RSel with (a:ann Sig') B a' Bl Br; auto.
    rewrite epp_C_RT_Call_out with (HC':=HC') in H2; inversion H2; auto.
    rewrite epp_C_RT_Call_out with (HC':=HC') in H3; inversion H3; auto.
    apply Network_eq_refl.
+ exfalso.
  inversion H.
  rewrite epp_C_End in H2. inversion H2.
Qed.

Lemma SP_To_bproj_Cond : forall D D' ps C HC s N' s' p,
  (forall p, In p ps -> @str_proj Sig D C p) ->
  (forall p, In p (CCC_pn C (Names D)) -> In p ps) ->
  <<epp_C D ps C HC,s>> --[RL_Cond p,D']--> <<N',s'>> ->
  exists C', (<<C,s>> --[RL_Cond p,D]--> <<C',s'>>)%CC
  /\ forall HC', (N' (>>) (epp_C D ps C' HC')).
Proof.
intros.
rename H into Hsp, H0 into Hin, H1 into H.
revert N' H.
induction C; intros. induction e. 1,2,3,5: inversion H. (* double cases *)
+ clear s'0 H8 N'0 H7 p0 H0 s0 H5 H.
  rename t into a'', t0 into p', t2 into q', t3 into v', t1 into e.
  generalize (projectable_C_inv_Com Sig D ps p' e q' v' a'' C HC); intro HC'.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H1. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H, epp_C_Com_p with (HC':=HC') in H1; auto.
    inversion H1. rewrite H; auto.
  assert (q' <> p) as Hq'p.
  1: intro. rewrite <- H, epp_C_Com_q with (HC':=HC') in H1.
    inversion H1. 1,2: rewrite H; auto.
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (Network_rm _ (epp_C D ps C HC') p | p[B1])) ; intros.
  rename x into C'. destroy H.
  exists (p' # e --> q' $ v' @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros; intro r. rewrite H3.
    set (H':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC'0). clearbody H'.
    generalize (H H' r); clear H; intro.
    elim ((@eq_dec Pid) r p); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
    2: elim ((@eq_dec Pid) p' r); intro Hp'r.
    3: elim ((@eq_dec Pid) q' r); intro Hq'r.
    - rewrite Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite Hpr, Par_proj2 in H. 2: apply Network_rm_In.
      rewrite epp_C_Com_r with (HC':=H'); auto.
    - rewrite <- Hp'r, Par_proj1', Network_rm_out; auto.
      rewrite <- Hp'r, Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_Com_p with (HC':=H'), epp_C_Com_p with (HC':=HC'); auto.
      constructor; auto. all: rewrite Hp'r; auto.
      all: apply Process_out; auto.
    - rewrite <- Hq'r, Par_proj1', Network_rm_out; auto.
      rewrite <- Hq'r, Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_Com_q with (HC':=H'), epp_C_Com_q with (HC':=HC'); auto.
      constructor; auto. all: rewrite Hq'r; auto.
      all: apply Process_out; auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_Com_r with (HC':=H'), epp_C_Com_r with (HC':=HC'); auto.
      all: apply Process_out; auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_out, epp_C_out; auto. constructor.
      all: apply Process_out; auto.
  * apply (@S_Then Sig') with b B1 B2; auto.
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC) in H1; inversion H1; auto.
    apply epp_C_wd.
    apply Network_eq_refl.
+ clear s'0 H8 N'0 H7 p0 H0 s0 H5 H.
  rename t into a'', t0 into p', t2 into q', t3 into v', t1 into e.
  generalize (projectable_C_inv_Com Sig D ps p' e q' v' a'' C HC); intro HC'.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H1. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H, epp_C_Com_p with (HC':=HC') in H1; auto.
    inversion H1. rewrite H; auto.
  assert (q' <> p) as Hq'p.
  1: intro. rewrite <- H, epp_C_Com_q with (HC':=HC') in H1.
    inversion H1. 1,2: rewrite H; auto.
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (Network_rm _ (epp_C D ps C HC') p | p[B2])); intros.
  rename x into C'. destroy H.
  exists (p' # e --> q' $ v' @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros; intro r. rewrite H3.
    set (H':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC'0). clearbody H'.
    generalize (H H' r); clear H; intro.
    elim ((@eq_dec Pid) r p); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
    2: elim ((@eq_dec Pid) p' r); intro Hp'r.
    3: elim ((@eq_dec Pid) q' r); intro Hq'r.
    - rewrite Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite Hpr, Par_proj2 in H. 2: apply Network_rm_In.
      rewrite epp_C_Com_r with (HC':=H'); auto.
    - rewrite <- Hp'r, Par_proj1', Network_rm_out; auto.
      rewrite <- Hp'r, Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_Com_p with (HC':=H'), epp_C_Com_p with (HC':=HC'); auto.
      constructor; auto. all: rewrite Hp'r; auto.
      all: apply Process_out; auto.
    - rewrite <- Hq'r, Par_proj1', Network_rm_out; auto.
      rewrite <- Hq'r, Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_Com_q with (HC':=H'), epp_C_Com_q with (HC':=HC'); auto.
      constructor; auto. all: rewrite Hq'r; auto.
      all: apply Process_out; auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_Com_r with (HC':=H'), epp_C_Com_r with (HC':=HC'); auto.
      all: apply Process_out; auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_out, epp_C_out; auto. constructor.
      all: apply Process_out; auto.
  * apply (@S_Else Sig') with b B1 B2; auto.
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC) in H1; inversion H1; auto.
    apply epp_C_wd.
    apply Network_eq_refl.
+ clear s'0 H8 N'0 H7 p0 H0 s0 H5 H.
  rename t into a'', t0 into p', t1 into q', t2 into l.
  generalize (projectable_C_inv_Sel Sig D ps p' q' l a'' C HC); intro HC'.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H1. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H, epp_C_Sel_p with (HC':=HC') in H1; auto.
    inversion H1. rewrite H; auto.
  assert (q' <> p) as Hq'p.
  1: intro. induction l.
    rewrite <- H, epp_C_Sel_ql with (HC':=HC') in H1. inversion H1.
    3: rewrite <- H, epp_C_Sel_qr with (HC':=HC') in H1. 3: inversion H1.
    1,2,3,4: rewrite H; auto.
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (Network_rm _ (epp_C D ps C HC') p | p[B1])); intros.
  rename x into C'. destroy H.
  exists (p' --> q' [l] @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros; intro r. rewrite H3.
    set (H':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC'0). clearbody H'.
    generalize (H H' r); clear H; intro.
    elim ((@eq_dec Pid) r p); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
    2: elim ((@eq_dec Pid) p' r); intro Hp'r.
    3: elim ((@eq_dec Pid) q' r); intro Hq'r.
    - rewrite Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite Hpr, Par_proj2 in H. 2: apply Network_rm_In.
      rewrite epp_C_Sel_r with (HC':=H'); auto.
    - rewrite <- Hp'r, Par_proj1', Network_rm_out; auto.
      rewrite <- Hp'r, Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_Sel_p with (HC':=H'), epp_C_Sel_p with (HC':=HC'); auto.
      constructor; auto. all: rewrite Hp'r; auto.
      all: apply Process_out; auto.
    - rewrite <- Hq'r, Par_proj1', Network_rm_out; auto.
      rewrite <- Hq'r, Par_proj1', Network_rm_out in H; auto.
      induction l.
      rewrite epp_C_Sel_ql with (HC':=H'), epp_C_Sel_ql with (HC':=HC'); auto.
      6: rewrite epp_C_Sel_qr with (HC':=H'), epp_C_Sel_qr with (HC':=HC'); auto.
      1: apply MB_Branching_SN with (Sig:=Sig'); auto.
      5: apply MB_Branching_NS with (Sig:=Sig'); auto.
      all: rewrite Hq'r; auto.
      all: apply Process_out; auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_Sel_r with (HC':=H'), epp_C_Sel_r with (HC':=HC'); auto.
      all: apply Process_out; auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_out, epp_C_out; auto. constructor.
      all: apply Process_out; auto.
  * apply (@S_Then Sig') with b B1 B2; auto.
    rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC) in H1; inversion H1; auto.
    apply epp_C_wd.
    apply Network_eq_refl.
+ clear s'0 H8 N'0 H7 p0 H0 s0 H5 H.
  rename t into a'', t0 into p', t1 into q', t2 into l.
  generalize (projectable_C_inv_Sel Sig D ps p' q' l a'' C HC); intro HC'.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H1. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H, epp_C_Sel_p with (HC':=HC') in H1; auto.
    inversion H1. rewrite H; auto.
  assert (q' <> p) as Hq'p.
  1: intro. induction l.
    rewrite <- H, epp_C_Sel_ql with (HC':=HC') in H1. inversion H1.
    3: rewrite <- H, epp_C_Sel_qr with (HC':=HC') in H1. 3: inversion H1.
    1,2,3,4: rewrite H; auto.
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (Network_rm _ (epp_C D ps C HC') p | p[B2])); intros.
  rename x into C'. destroy H.
  exists (p' --> q' [l] @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros; intro r. rewrite H3.
    set (H':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC'0). clearbody H'.
    generalize (H H' r); clear H; intro.
    elim ((@eq_dec Pid) r p); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
    2: elim ((@eq_dec Pid) p' r); intro Hp'r.
    3: elim ((@eq_dec Pid) q' r); intro Hq'r.
    - rewrite Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite Hpr, Par_proj2 in H. 2: apply Network_rm_In.
      rewrite epp_C_Sel_r with (HC':=H'); auto.
    - rewrite <- Hp'r, Par_proj1', Network_rm_out; auto.
      rewrite <- Hp'r, Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_Sel_p with (HC':=H'), epp_C_Sel_p with (HC':=HC'); auto.
      constructor; auto. all: rewrite Hp'r; auto.
      all: apply Process_out; auto.
    - rewrite <- Hq'r, Par_proj1', Network_rm_out; auto.
      rewrite <- Hq'r, Par_proj1', Network_rm_out in H; auto.
      induction l.
      rewrite epp_C_Sel_ql with (HC':=H'), epp_C_Sel_ql with (HC':=HC'); auto.
      6: rewrite epp_C_Sel_qr with (HC':=H'), epp_C_Sel_qr with (HC':=HC'); auto.
      1: apply MB_Branching_SN with (Sig:=Sig'); auto.
      5: apply MB_Branching_NS with (Sig:=Sig'); auto.
      all: rewrite Hq'r; auto.
      all: apply Process_out; auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_Sel_r with (HC':=H'), epp_C_Sel_r with (HC':=HC'); auto.
      all: apply Process_out; auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H; auto.
      rewrite epp_C_out, epp_C_out; auto. constructor.
      all: apply Process_out; auto.
  * apply (@S_Else Sig') with b B1 B2; auto.
    rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC) in H1; inversion H1; auto.
    apply epp_C_wd.
    apply Network_eq_refl.
+ clear s'0 H8 N'0 H7 p0 H0 s0 H5 H.
  rename t into p', t0 into b0.
  assert (projectable_C D C1 ps) as HC1.
  1: eapply projectable_C_inv_Then; eauto.
  assert (projectable_C D C2 ps) as HC2.
  1: eapply projectable_C_inv_Else; eauto.
  assert (In p ps) as Hpps.
  1: { revert H1. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  elim ((@eq_dec Pid) p p'); intro Hpp'.
  - revert dependent HC. revert Hsp Hin.
    rewrite <- Hpp'; clear p' Hpp'; intros.
    assert (b = b0).
    1: rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H1; inversion H1; auto.
    revert H2 H1. rewrite H. clear b H. rename b0 into b; intros.
    exists C1. repeat split.
    apply (@C_Then Sig); auto.
    intros; intro r. rewrite H3.
    elim ((@eq_dec Pid) r p); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
    * rewrite Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H1; auto.
      inversion H1. apply MB_refl'.
      rewrite Process_refl. apply epp_C_wd.
    * rewrite Par_proj1', Network_rm_out; auto.
      eapply merge_is_upper_bound, epp_C_Cond_r; eauto.
      apply Process_out; auto.
    * rewrite Par_proj1', Network_rm_out; auto.
      apply MB_refl'. repeat rewrite epp_C_out; auto.
      apply Process_out; auto.
  - assert (forall p, In p ps -> str_proj D C1 p) as Hsp1.
    1: apply Hsp.
    assert (forall p, In p ps -> str_proj D C2 p) as Hsp2.
    1: apply Hsp.
    clear Hsp.
    assert (p' <> p) as Hp'p. auto.
    (* get the remaining equalities *)
    elim (epp_C_Cond_Cond_inv Sig _ _ _ _ _ _ _ HC HC1 HC2 _ _ _ Hp'p H1); auto.
    intros. destroy H. rename x into B1t, x0 into B1e, x1 into B2t, x2 into B2e, H0 into Hp1, H5 into Hp2, H7 into Ht, H into He.
    assert (forall p, In p (CCC_pn C1 (Names D)) -> In p ps) as Hin1.
    1: intros. apply Hin. simpl; sup; sup.
    assert (forall p, In p (CCC_pn C2 (Names D)) -> In p ps) as Hin2.
    1: intros. apply Hin. simpl; sup; sup.
    elim (IHC1 HC1 Hsp1 Hin1 (epp_C D ps C1 HC1 \ p | p[B1t])); intros.
    rename x into C1'. destroy H.
    elim (IHC2 HC2 Hsp2 Hin2 (Network_rm _ (epp_C D ps C2 HC2) p | p[B2t])); intros.
    rename x into C2'. destroy H5. clear IHC1 IHC2.
    exists (If p' ?? b0 Then C1' Else C2'); repeat split.
    * apply (@C_Delay_Cond Sig); repeat split; simpl; auto.
    * intros. intro r. rewrite H3.
      assert (projectable_C D C1' ps) as HC1'.
      1: eapply projectable_C_inv_Then; eauto.
      assert (projectable_C D C2' ps) as HC2'.
      1: eapply projectable_C_inv_Else; eauto.
      elim ((@eq_dec Pid) r p); intro Hpr.
      2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
      2: elim ((@eq_dec Pid) p' r); intro Hp'r.
      ++ generalize (H HC1' r) (H5 HC2' r).
         rewrite Hpr, Par_proj2, Par_proj2, Par_proj2; auto.
         2,3,4: apply Network_rm_In.
         repeat rewrite Process_refl. intros.
         elim (MB_yields_merge _ _ _ _ _ _ H8 H9 Ht); auto.
         intros B' [HB'1 HB1].
         apply MB_trans with B'; auto.
         apply MB_refl'. eapply merge_unique; eauto.
         apply epp_C_Cond_r; auto.
      ++ generalize (H HC1' r) (H5 HC2' r).
         rewrite <- Hp'r. rewrite <- Hp'r in Hr, Hpr. clear r Hp'r.
         rewrite Par_proj1', Par_proj1', Par_proj1', Network_rm_out, Network_rm_out, Network_rm_out; auto.
         rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2); auto.
         rewrite epp_C_Cond_p with (HC1:=HC1') (HC2:=HC2'); auto.
         constructor; auto.
         all: apply Process_out; auto.
      ++ generalize (epp_C_Cond_r Sig _ _ _ _ _ _ HC HC1 HC2 _ Hp'r); intro.
         generalize (epp_C_Cond_r Sig _ _ _ _ _ _ HC' HC1' HC2' _ Hp'r); intro.
         rewrite Par_proj1', Network_rm_out; auto.
         specialize (H5 HC2' r). specialize (H HC1' r).
         rewrite Par_proj1', Network_rm_out in H, H5; auto.
         eapply merge_is_lub; eauto.
         1,2: eapply MB_trans; eauto.
         eapply merge_is_upper_bound; eauto.
         eapply merge_is_upper_bound'; eauto.
         all: apply Process_out; auto.
      ++ rewrite Par_proj1', Network_rm_out; auto.
         repeat rewrite epp_C_out; auto. constructor.
         apply Process_out; auto.
    * apply (@S_Then Sig') with b B2t B2e; auto.
      apply Network_eq_refl.
    * apply (@S_Then Sig') with b B1t B1e; auto.
      apply Network_eq_refl.
+ clear s'0 H8 N'0 H7 p0 H0 s0 H5 H.
  rename t into p', t0 into b0.
  assert (projectable_C D C1 ps) as HC1.
  1: eapply projectable_C_inv_Then; eauto.
  assert (projectable_C D C2 ps) as HC2.
  1: eapply projectable_C_inv_Else; eauto.
  assert (In p ps) as Hpps.
  1: { revert H1. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  elim ((@eq_dec Pid) p p'); intro Hpp'.
  - revert dependent HC. revert Hsp Hin.
    rewrite <- Hpp'; clear p' Hpp'; intros.
    assert (b = b0).
    1: rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H1; inversion H1; auto.
    revert H2 H1. rewrite H. clear b H. rename b0 into b; intros.
    exists C2. repeat split.
    apply (@C_Else Sig); auto.
    intros; intro r. rewrite H3.
    elim ((@eq_dec Pid) r p); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
    * rewrite Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H1; auto.
      inversion H1. apply MB_refl'.
      rewrite Process_refl. apply epp_C_wd.
    * rewrite Par_proj1', Network_rm_out; auto.
      eapply merge_is_upper_bound', epp_C_Cond_r; auto.
      apply Process_out; auto.
    * rewrite Par_proj1', Network_rm_out; auto.
      apply MB_refl'. repeat rewrite epp_C_out; auto.
      apply Process_out; auto.
  - assert (forall p, In p ps -> str_proj D C1 p) as Hsp1.
    1: apply Hsp.
    assert (forall p, In p ps -> str_proj D C2 p) as Hsp2.
    1: apply Hsp.
    clear Hsp.
    assert (p' <> p) as Hp'p. auto.
    (* get the remaining equalities *)
    elim (epp_C_Cond_Cond_inv Sig _ _ _ _ _ _ _ HC HC1 HC2 _ _ _ Hp'p H1); auto.
    intros. destroy H. rename x into B1t, x0 into B1e, x1 into B2t, x2 into B2e, H0 into Hp1, H5 into Hp2, H7 into Ht, H into He.
    assert (forall p, In p (CCC_pn C1 (Names D)) -> In p ps) as Hin1.
    1: intros. apply Hin. simpl; sup; sup.
    assert (forall p, In p (CCC_pn C2 (Names D)) -> In p ps) as Hin2.
    1: intros. apply Hin. simpl; sup; sup.
    elim (IHC1 HC1 Hsp1 Hin1 (epp_C D ps C1 HC1 \ p | p[B1e])); intros.
    rename x into C1'. destroy H.
    elim (IHC2 HC2 Hsp2 Hin2 (Network_rm _ (epp_C D ps C2 HC2) p | p[B2e])); intros.
    rename x into C2'. destroy H5. clear IHC1 IHC2.
    exists (If p' ?? b0 Then C1' Else C2'); repeat split.
    * apply (@C_Delay_Cond Sig); repeat split; simpl; auto.
    * intros. intro r. rewrite H3.
      assert (projectable_C D C1' ps) as HC1'.
      1: eapply projectable_C_inv_Then; eauto.
      assert (projectable_C D C2' ps) as HC2'.
      1: eapply projectable_C_inv_Else; eauto.
      elim ((@eq_dec Pid) r p); intro Hpr.
      2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
      2: elim ((@eq_dec Pid) p' r); intro Hp'r.
      ++ generalize (H HC1' r) (H5 HC2' r).
         rewrite Hpr, Par_proj2, Par_proj2, Par_proj2; auto.
         2,3,4: apply Network_rm_In.
         repeat rewrite Process_refl. intros.
         elim (MB_yields_merge _ _ _ _ _ _ H8 H9 He); auto.
         intros B' [HB'1 HB1].
         apply MB_trans with B'; auto.
         apply MB_refl'. eapply merge_unique; eauto.
         apply epp_C_Cond_r; auto.
      ++ generalize (H HC1' r) (H5 HC2' r).
         rewrite <- Hp'r. rewrite <- Hp'r in Hr, Hpr. clear r Hp'r.
         rewrite Par_proj1', Par_proj1', Par_proj1', Network_rm_out, Network_rm_out, Network_rm_out; auto.
         rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2); auto.
         rewrite epp_C_Cond_p with (HC1:=HC1') (HC2:=HC2'); auto.
         constructor; auto.
         all: apply Process_out; auto.
      ++ generalize (epp_C_Cond_r Sig _ _ _ _ _ _ HC HC1 HC2 _ Hp'r); intro.
         generalize (epp_C_Cond_r Sig _ _ _ _ _ _ HC' HC1' HC2' _ Hp'r); intro.
         rewrite Par_proj1', Network_rm_out; auto.
         specialize (H5 HC2' r). specialize (H HC1' r).
         rewrite Par_proj1', Network_rm_out in H, H5; auto.
         eapply merge_is_lub; eauto.
         1,2: eapply MB_trans; eauto.
         eapply merge_is_upper_bound; eauto.
         eapply merge_is_upper_bound'; eauto.
         all: apply Process_out; auto.
      ++ rewrite Par_proj1', Network_rm_out; auto.
         repeat rewrite epp_C_out; auto. constructor.
         apply Process_out; auto.
    * apply (@S_Else Sig') with b B2t B2e; auto.
      apply Network_eq_refl.
    * apply (@S_Else Sig') with b B1t B1e; auto.
      apply Network_eq_refl.
(* RT_Call - order switched because of inversion *)
+ clear s'0 H8 N'0 H7 p0 H0 s0 H5 H.
  rename t into X, l into ps'.
  assert (projectable_C D C ps) as HC'.
  1: apply str_proj_C'. apply Hsp.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H1. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (~In p ps').
  1: intro. rewrite epp_C_RT_Call in H1; auto; inversion H1.
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  assert (forall p, In p ps -> str_proj D C p) as Hsp'. apply Hsp.
  elim (IHC HC' Hsp' Hin' (Network_rm _ (epp_C D ps C HC') p | p[B1])); intros.
  rename x into C'. destroy H0.
  exists (RT_Call X ps' C'); repeat split.
  * apply C_Delay_Call; repeat split; auto.
    apply disjoint_ps_char.
    intros; intro. rewrite H8 in H7; auto.
  * intros; intro r. rewrite H3.
    assert (projectable_C D C' ps) as H'.
    1: apply str_proj_C'; intros. eapply CCC_To_str_proj_Cond; eauto.
    specialize (H0 H' r).
    elim ((@eq_dec Pid) r p); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps'); intro Hr.
    - rewrite Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite Hpr, Par_proj2 in H0. 2: apply Network_rm_In.
      rewrite epp_C_RT_Call_out with (HC':=H'); auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H0; auto.
      apply MB_refl'.
      repeat rewrite epp_C_RT_Call; auto.
      1,2: apply Hin; simpl; sup.
      all: apply Process_out; auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H0; auto.
      rewrite epp_C_RT_Call_out with (HC':=H'); auto.
      rewrite epp_C_RT_Call_out with (HC':=HC'); auto.
      all: apply Process_out; auto.
  * apply (@S_Then Sig') with b B1 B2; auto.
    rewrite epp_C_RT_Call_out with (HC':=HC') in H1; inversion H1; auto.
    apply Network_eq_refl.
+ clear s'0 H8 N'0 H7 p0 H0 s0 H5 H.
  rename t into X, l into ps'.
  assert (projectable_C D C ps) as HC'.
  1: apply str_proj_C'. apply Hsp.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H1. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (~In p ps').
  1: intro. rewrite epp_C_RT_Call in H1; auto; inversion H1.
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  assert (forall p, In p ps -> str_proj D C p) as Hsp'. apply Hsp.
  elim (IHC HC' Hsp' Hin' (Network_rm _ (epp_C D ps C HC') p | p[B2])); intros.
  rename x into C'. destroy H0.
  exists (RT_Call X ps' C'); repeat split.
  * apply C_Delay_Call; repeat split; auto.
    apply disjoint_ps_char.
    intros; intro. rewrite H8 in H7; auto.
  * intros; intro r. rewrite H3.
    assert (projectable_C D C' ps) as H'.
    1: apply str_proj_C'; intros. eapply CCC_To_str_proj_Cond; eauto.
    specialize (H0 H' r).
    elim ((@eq_dec Pid) r p); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps'); intro Hr.
    - rewrite Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite Hpr, Par_proj2 in H0. 2: apply Network_rm_In.
      rewrite epp_C_RT_Call_out with (HC':=H'); auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H0; auto.
      apply MB_refl'.
      repeat rewrite epp_C_RT_Call; auto.
      1,2: apply Hin; simpl; sup.
      all: apply Process_out; auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H0; auto.
      rewrite epp_C_RT_Call_out with (HC':=H'); auto.
      rewrite epp_C_RT_Call_out with (HC':=HC'); auto.
      all: apply Process_out; auto.
  * apply (@S_Else Sig') with b B1 B2; auto.
    rewrite epp_C_RT_Call_out with (HC':=HC') in H1; inversion H1; auto.
    apply Network_eq_refl.
+ exfalso.
  inversion H.
  1,2: elim (In_dec (@eq_dec Pid) p ps); intros.
  1,3: elim (In_dec (@eq_dec Pid) p (fst (D t))); intros.
  1,3: rewrite epp_C_Call in H1; auto.
  3,4: rewrite epp_C_Call_out in H1; auto.
  5,6: rewrite epp_C_out in H1; auto.
  all: inversion H1.
+ exfalso.
  inversion H.
  all: rewrite epp_C_End in H1; inversion H1.
Unshelve. auto. auto.
Qed.

Lemma SP_To_bproj_Call : forall D (D':DefSetB Sig') ps C HC s N' s' p X,
  Choreography_WF C ->
  (forall p, In p ps -> str_proj D C p) ->
  (forall p, In p (CCC_pn C (Names D)) -> In p ps) ->
  (forall p HX, D' (X,p) = epp_C D ps (snd (D X)) HX p) ->
  (forall p X, In p (CCC_pn (snd (D X)) (Names D))
            -> In p (fst (D X))) ->
  (forall X, projectable_C D (snd (D X)) ps) ->
  (forall X, initial (snd (D X))
    /\ forall p, In p (fst (D X)) -> In p ps) ->
  <<epp_C D ps C HC,s>> --[RL_Call ((X,p):recvar Sig') p,D']--> <<N',s'>> ->
  exists C', (<<C,s>> --[RL_Call X p,D]--> <<C',s'>>)%CC
  /\ forall HC', (N' (>>) epp_C D ps C' HC').
Proof.
intros.
rename H into HWF, H0 into Hsp, H1 into Hin,
  H2 into HD, H3 into Hnames, H4 into HD', H5 into Hinit, H6 into H.
revert N' H.
induction C; intros. induction e.
+ inversion H.
  clear s'0 H7 N'0 H6 X0 H0 s0 H4 p0 H1.
  rename t into a'', t0 into p', t2 into q', t1 into e, t3 into v.
  generalize (projectable_C_inv_Com Sig D ps p' e q' v a'' C HC); intro HC'.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H2. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H0, epp_C_Com_p with (HC':=HC') in H2; auto.
    inversion H2. rewrite H0; auto.
  assert (q' <> p) as Hq'p.
  1: intro. rewrite <- H0, epp_C_Com_q with (HC':=HC') in H2.
    inversion H2. rewrite H0; auto. rewrite H0; auto.
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  apply Choreography_WF_eta in HWF.
  elim (IHC HC' HWF Hsp Hin' (Network_rm _ (epp_C D ps C HC') p | Process Sig' p (D' (X,p)))); intros.
  rename x into C'. destroy H0.
  exists (p' # e --> q' $ v @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros. intro r. rewrite H5. 
    set (H':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC'0).
    generalize (H0 H' r); clear H0.
    elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
    2: elim ((@eq_dec Pid) p' r); intro Hp'r.
    3: elim ((@eq_dec Pid) q' r); intro Hq'r.
    - rewrite <- Hpr, Par_proj2, Par_proj2. 2,3: apply Network_rm_In.
      rewrite epp_C_Com_r with (HC':=H'); auto.
    - rewrite <- Hp'r, Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto.
      2,3: apply Process_out; auto.
      rewrite epp_C_Com_p with (HC':=H'), epp_C_Com_p with (HC':=HC'); auto.
      constructor; auto. all: rewrite Hp'r; auto.
    - rewrite <- Hq'r, Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto.
      2,3: apply Process_out; auto.
      rewrite epp_C_Com_q with (HC':=H'), epp_C_Com_q with (HC':=HC'); auto.
      constructor; auto. all: rewrite Hq'r; auto.
    - rewrite Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto.
      2,3: apply Process_out; auto.
      rewrite epp_C_Com_r with (HC':=H'), epp_C_Com_r with (HC':=HC'); auto.
    - intro. apply MB_refl'.
      rewrite Par_proj1', Network_rm_out; auto.
      2: apply Process_out; auto.
      rewrite epp_C_out, epp_C_out; auto.
  * apply (@S_Call Sig'); auto.
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com Sig _ _ _ _ _ _ _ _ HC) in H2; inversion H2; auto.
    apply epp_C_wd.
    apply Network_eq_refl.
+ inversion H.
  clear s'0 H7 N'0 H6 X0 H0 s0 H4 p0 H1.
  rename t into a'', t0 into p', t1 into q', t2 into l.
  generalize (projectable_C_inv_Sel Sig D ps p' q' l a'' C HC); intro HC'.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H2. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H0, epp_C_Sel_p with (HC':=HC') in H2; auto.
    inversion H2. rewrite H0; auto.
  assert (q' <> p) as Hq'p.
  1: intro. induction l.
    rewrite <- H0, epp_C_Sel_ql with (HC':=HC') in H2.
    inversion H2. rewrite H0; auto. rewrite H0; auto.
    rewrite <- H0, epp_C_Sel_qr with (HC':=HC') in H2.
    inversion H2. rewrite H0; auto. rewrite H0; auto.
  assert (forall p, In p (CCC_pn C (Names D)) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  apply Choreography_WF_eta in HWF.
  elim (IHC HC' HWF Hsp Hin' (Network_rm _ (epp_C D ps C HC') p | (Process Sig' p (D' (X,p))))); intros.
  rename x into C'. destroy H0.
  exists (p' --> q'[l] @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros. intro r. rewrite H5.
    set (H':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC'0).
    generalize (H0 H' r); clear H0.
    elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
    2: elim ((@eq_dec Pid) p' r); intro Hp'r.
    3: elim ((@eq_dec Pid) q' r); intro Hq'r.
    - rewrite <- Hpr, Par_proj2, Par_proj2. 2,3: apply Network_rm_In.
      rewrite epp_C_Sel_r with (HC':=H'); auto.
    - rewrite <- Hp'r, Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto.
      2,3: apply Process_out; auto.
      rewrite epp_C_Sel_p with (HC':=H'), epp_C_Sel_p with (HC':=HC'); auto.
      constructor; auto. all: rewrite Hp'r; auto.
    - rewrite <- Hq'r, Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto.
      2,3: apply Process_out; auto.
      induction l.
      rewrite epp_C_Sel_ql with (HC':=H'), epp_C_Sel_ql with (HC':=HC'); auto.
      apply MB_Branching_SN with (Sig := Sig'); auto.
      1,2,3,4: rewrite Hq'r; auto.
      rewrite epp_C_Sel_qr with (HC':=H'), epp_C_Sel_qr with (HC':=HC'); auto.
      apply MB_Branching_NS with (Sig := Sig'); auto.
      1,2,3,4: rewrite Hq'r; auto.
    - rewrite Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto.
      2,3: apply Process_out; auto.
      rewrite epp_C_Sel_r with (HC':=H'), epp_C_Sel_r with (HC':=HC'); auto.
    - intro. apply MB_refl'.
      rewrite Par_proj1', Network_rm_out; auto.
      2: apply Process_out; auto.
      rewrite epp_C_out, epp_C_out; auto.
  * apply (S_Call Sig'); auto.
    rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel Sig _ _ _ _ _ _ _ HC) in H2; inversion H2; auto.
    apply epp_C_wd.
    apply Network_eq_refl.
+ inversion H.
  clear s'0 H7 N'0 H6 p0 H1 X0 H0 s0 H4.
  rename t into p', t0 into b.
  generalize (projectable_C_inv_Then Sig _ _ _ _ _ _ HC); intro HC1.
  generalize (projectable_C_inv_Else Sig _ _ _ _ _ _ HC); intro HC2.
  assert (forall p, In p ps -> str_proj D C1 p) as Hsp1.
  1: apply Hsp.
  assert (forall p, In p ps -> str_proj D C2 p) as Hsp2.
  1: apply Hsp.
  clear Hsp.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H2. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H0, epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H2; auto.
    inversion H2. rewrite H0; auto.
  generalize (Choreography_WF_Then _ _ _ _ _ HWF) as HWF1.
  generalize (Choreography_WF_Else _ _ _ _ _ HWF) as HWF2.
  intros; clear HWF.
  assert (forall p, In p (CCC_pn C1 (Names D)) -> In p ps) as Hin1.
  1: intros. apply Hin. simpl; sup; sup.
  assert (forall p, In p (CCC_pn C2 (Names D)) -> In p ps) as Hin2.
  1: intros. apply Hin. simpl; sup; sup.
  elim (IHC1 HC1 HWF1 Hsp1 Hin1 (epp_C D ps C1 HC1 \ p | Process Sig' p (D' (X,p)))); intros.
  rename x into C1'. destroy H0.
  elim (IHC2 HC2 HWF2 Hsp2 Hin2 (Network_rm _ (epp_C D ps C2 HC2) p | Process Sig' p (D' (X,p)))); intros.
  rename x into C2'. destroy H4. clear IHC1 IHC2.
  exists (If p' ?? b Then C1' Else C2'); repeat split.
  * apply C_Delay_Cond; repeat split; auto.
  * intros. intro r. rewrite H5.
    set (H1':=projectable_C_inv_Then Sig _ _ _ _ _ _ HC').
    generalize (H0 H1' r); clear H0.
    set (H2':=projectable_C_inv_Else Sig _ _ _ _ _ _ HC').
    generalize (H4 H2' r); clear H4.
    elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
    2: elim ((@eq_dec Pid) p' r); intro Hp'r.
    - rewrite <- Hpr, Par_proj2, Par_proj2, Par_proj2. 2,3,4: apply Network_rm_In.
      intros. eapply merge_is_lub. apply H4. apply H0.
      apply epp_C_Cond_r; auto.
    - rewrite <- Hp'r, Par_proj1', Par_proj1', Par_proj1', Network_rm_out, Network_rm_out, Network_rm_out; auto.
      2,3,4: apply Process_out; auto.
      rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2). 2: rewrite Hp'r; auto.
      rewrite epp_C_Cond_p with (HC1:=H1') (HC2:=H2'). 2: rewrite Hp'r; auto.
      constructor; auto.
    - rewrite Par_proj1', Par_proj1', Par_proj1', Network_rm_out, Network_rm_out, Network_rm_out; auto.
      2,3,4: apply Process_out; auto.
      intros. eapply merge_is_lub.
      3: apply epp_C_Cond_r; auto.
      1,2: eapply MB_trans; eauto.
      eapply merge_is_upper_bound, epp_C_Cond_r; auto.
      eapply merge_is_upper_bound', epp_C_Cond_r; auto.
    - intros. apply MB_refl'.
      rewrite Par_proj1', Network_rm_out; auto.
      2: apply Process_out; auto.
      rewrite epp_C_out, epp_C_out; auto.
  * apply (S_Call Sig'); auto.
    eapply bproj_unique. apply epp_C_bproj; auto.
    generalize (epp_C_bproj Sig _ _ _ HC _ Hpps); intro.
    rewrite H2 in H4.
    inversion H4. inversion H17. rewrite <- H21, H19; auto.
    apply Network_eq_refl.
  * apply (S_Call Sig'); auto.
    eapply bproj_unique. apply epp_C_bproj; auto.
    generalize (epp_C_bproj Sig _ _ _ HC _ Hpps); intro.
    rewrite H2 in H0.
    inversion H0. inversion H15. rewrite <- H19, H16; auto.
    apply Network_eq_refl.
+ inversion H.
  clear s'0 H7 N'0 H6 p0 H1 X0 H0 s0 H4. rename t into r.
  assert (In p ps /\ In p (fst (D r)) /\ r = X).
  1: { clear H3 H8 H5 N H N' Hin Hsp s s'.
    revert H2. unfold epp_C. elim In_dec. 2: discriminate.
    elim bproj_dec. induction a; simpl; intros.
    rewrite H2 in p0; inversion_clear p0; auto.
    intros H H'. exfalso. contr_aux HC.
  }
  destroy H0. rename H1 into Hpps, H4 into HX.
  revert dependent HC. rewrite H0.
  rewrite H0 in HX, Hsp, Hin, HWF; clear r H0; intros.
  assert (0 < [#] (fst (D X))).
  1: {
    elim (Nat.lt_ge_cases 0 ([#] (fst (D X)))); auto.
    intro. inversion H0. apply set_size_0 in H4. rewrite H4 in HX; inversion HX.
  }
  inversion H0.
  - exists (snd (D X)); split.
    apply C_Call_Local; auto.
    intro. intro r. rewrite H5.
    apply MB_refl'.
    elim ((@eq_dec Pid) p r); intro Hpr.
    * rewrite <- Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite Process_refl; auto.
    * rewrite Par_proj1', Network_rm_out; auto.
      rewrite epp_C_Call_out, epp_C_out'; auto.
      ++ intro. apply Hpr.
         apply Hnames in H1.
         eapply set_size_1; eauto.
      ++ intro. apply Hpr. eapply set_size_1; eauto.
      ++ apply Process_out; auto.
  - exists (RT_Call X (fst (D X) [\] p) (snd (D X))).
    split.
    apply C_Call_Start; auto. rewrite <- H1; auto with arith.
    intro. intro r. rewrite H5.
    elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r (fst (D X))); intro Hr.
    * rewrite <- Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite Process_refl.
      apply MB_refl'.
      rewrite epp_C_RT_Call_out with (HC':=HD' X); auto.
      intro Hp; apply set_remove'_2 in Hp; auto.
    * rewrite Par_proj1', Network_rm_out; auto.
      apply MB_refl'.
      rewrite epp_C_RT_Call, epp_C_Call; auto.
      apply set_remove'_3; auto.
      apply Process_out; auto.
    * rewrite Par_proj1', Network_rm_out; auto.
      apply MB_refl'.
      rewrite epp_C_out', epp_C_out'; auto.
      simpl. sup. intro; apply Hr.
      inversion_clear H6. eapply set_remove'_1; eauto.
      apply Hnames; auto.
      apply Process_out; auto.
+ inversion H.
  clear s'0 H7 N'0 H6 p0 H1 X0 H0 s0 H4. rename t into r.
  assert (In p ps) as Hpps.
  1: { revert H2. unfold epp_C. elim In_dec; auto. discriminate. }
  generalize (Choreography_WF_no_empty_ann _ _ HWF) as Hann.
  apply Choreography_WF_Call_1 in HWF.
  intro. destroy Hann. clear Hann.
  assert (projectable_C D C ps) as HCp.
  1: apply str_proj_C'; apply Hsp.
  elim (eq_dec r X); intro Hr. (* case 2 pending *)
  revert dependent HC. rewrite Hr.
  rewrite Hr in Hsp, Hin; clear r Hr; intros.
  assert (0 < [#] l).
  1: {
    elim (Nat.lt_ge_cases 0 ([#] l)); auto.
    intro. exfalso. inversion H1. apply set_size_0 in H6; auto.
  }
  elim (In_dec (@eq_dec Pid) p l); intro Hpl. (* weird edge case *)
  1: elim (Nat.eq_dec ([#] l) 1); clear H0; intro H0.
  - exists C; split.
    apply C_Call_Finish; auto.
    intro. intro r. rewrite H5.
    elim ((@eq_dec Pid) p r); intro Hpr.
    * rewrite <- Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite Process_refl.
      elim (Hsp p); auto; intros. elim (H6 p); auto; intros; clear H6.
      rewrite (HD _ (HD' X)); auto.
      apply H9; apply epp_C_bproj; auto.
    * rewrite Par_proj1', Network_rm_out; auto.
      rewrite epp_C_RT_Call_out with (HC':=HC'). apply MB_refl.
      intro. apply Hpr. eapply set_size_1; eauto.
      apply Process_out; auto.
  - exists (RT_Call X (l [\] p) C).
    split.
    apply C_Call_Enter; auto.
    1: inversion H1; auto. elim H0; auto. apply le_n_S in H6; auto.
    intro. intro r. rewrite H5.
    elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r l); intro Hr.
    * rewrite <- Hpr, Par_proj2, Process_refl. 2: apply Network_rm_In.
      elim (Hsp p); auto; intros.
      rewrite epp_C_RT_Call_out with (HC':=HCp); auto.
      elim (H6 p); auto; clear H6; intros.
      rewrite (HD _ (HD' X)).
      apply H7; apply epp_C_bproj; auto.
      intro Hp; apply set_remove'_2 in Hp; auto.
    * rewrite Par_proj1', Network_rm_out; auto.
      apply MB_refl'.
      rewrite epp_C_RT_Call, epp_C_RT_Call; auto.
      1,3: apply Hin; simpl; sup.
      apply set_remove'_3; auto.
      apply Process_out; auto.
    * rewrite Par_proj1', Network_rm_out; auto.
      apply MB_refl'.
      rewrite epp_C_RT_Call_out with (HC':=HCp); auto.
      rewrite epp_C_RT_Call_out with (HC':=HCp); auto.
      intro. apply Hr. eapply set_remove'_1; eauto.
      apply Process_out; auto.
  - elim (IHC HCp) with (N':=(Network_rm _ (epp_C _ _ _ HCp) p | Process Sig' p (D'(X,p)))); auto.
    2: intros; elim (Hsp p0); auto.
    2: intros; apply Hin; simpl; sup.
    intros. destroy H4. rename x into C'.
    exists (RT_Call X l C'); split.
    * apply C_Delay_Call; auto.
      apply disjoint_ps_char.
      simpl; intros. intro. rewrite H9 in H7; auto.
    * intros.
      assert (projectable_C D C' ps).
      1: {
        eapply (CCC_To_projectable_C _ D ps C s C' s' (RL_Call X p)); eauto.
        apply Hsp. intros; eapply initial_str_proj; eauto.
        apply Hinit; auto.
        intros. intro. apply Hnames.
        intros r Z. intros. elim (Hinit Z); auto.
      }
      intro r. rewrite H5. clear N N' H H3 H5. rename l into ps'.
      generalize (H4 H7 r); clear H4; intro.
      elim ((@eq_dec Pid) p r); intro Hpr.
      2: rewrite Par_proj1', Network_rm_out; auto.
      2: elim (In_dec (@eq_dec Pid) r ps'); intro Hr.
      ++ rewrite <- Hpr, Par_proj2. 2: apply Network_rm_In.
         rewrite epp_C_RT_Call_out with (HC':=H7); auto.
         rewrite <- Hpr, Par_proj2 in H; auto.
         apply Network_rm_In.
      ++ repeat rewrite epp_C_RT_Call; auto.
         apply MB_refl.
         all: apply Hin; simpl; sup.
      ++ rewrite epp_C_RT_Call_out with (HC':=H7); auto.
         rewrite epp_C_RT_Call_out with (HC':=HCp); auto.
         rewrite Par_proj1', Network_rm_out in H; auto.
         apply Process_out; auto.
      ++ apply Process_out; auto.
    * apply (S_Call Sig'); auto.
      rewrite epp_C_RT_Call_out with (HC':=HCp) in H2; auto.
      apply Network_eq_refl.
  - assert (~In p l) as Hp.
    1: { intro. rewrite epp_C_RT_Call in H2; auto. inversion H2; auto. }
    elim (IHC HCp) with (N':=(Network_rm _ (epp_C _ _ _ HCp) p | Process Sig' p (D'(X,p)))); auto.
    2: intros; elim (Hsp p0); auto.
    2: intros; apply Hin; simpl; sup.
    intros. destroy H1. rename x into C', r into Y.
    exists (RT_Call Y l C'); split.
    * apply C_Delay_Call; auto.
      apply disjoint_ps_char.
      simpl; intros. intro. rewrite H7 in H6; auto.
    * intros.
      assert (projectable_C D C' ps).
      1: {
        eapply (CCC_To_projectable_C Sig D ps C s C' s' (RL_Call X p)); eauto.
        apply Hsp. intros; eapply initial_str_proj; eauto.
        apply Hinit; auto.
        intros. intro. apply Hnames.
        intros r Z. intros. elim (Hinit Z); auto.
      }
      intro r. rewrite H5. clear N N' H H3 H5. rename l into ps'.
      generalize (H1 H6 r); clear H1; intro.
      elim ((@eq_dec Pid) p r); intro Hpr.
      2: rewrite Par_proj1', Network_rm_out; auto.
      2: elim (In_dec (@eq_dec Pid) r ps'); intro Hr'.
      ++ rewrite <- Hpr, Par_proj2. 2: apply Network_rm_In.
         rewrite epp_C_RT_Call_out with (HC':=H6); auto.
         rewrite <- Hpr, Par_proj2 in H; auto.
         apply Network_rm_In.
      ++ repeat rewrite epp_C_RT_Call; auto.
         apply MB_refl.
         all: apply Hin; simpl; sup.
      ++ rewrite epp_C_RT_Call_out with (HC':=H6); auto.
         rewrite epp_C_RT_Call_out with (HC':=HCp); auto.
         rewrite Par_proj1', Network_rm_out in H; auto.
         apply Process_out; auto.
      ++ apply Process_out; auto.
    * apply (S_Call Sig'); auto.
      rewrite epp_C_RT_Call_out with (HC':=HCp) in H2; auto.
      apply Network_eq_refl.
+ exfalso.
  inversion H.
  rewrite epp_C_End in H2. inversion H2.
Unshelve. auto. auto.
Qed.

Lemma SP_To_bproj_Call_name : forall D D' ps C HC s N' s' p X,
  <<epp_C D ps C HC,s>> --[RL_Call X p,D']--> <<N',s'>> ->
  exists (Y:RecVar), X = (Y,p) /\ X_Free _ Y C.
Proof.
intros.
inversion H.
clear s'0 H7 N'0 H6 p0 H1 X0 H0 s0 H4 N H3 H s s' H8 N' H5 D'.
revert H2. unfold epp_C.
elim In_dec. 2: discriminate.
elim bproj_dec. induction a; simpl; intros.
rewrite H2 in p0. clear a x H2.
clear HC. rename p0 into HC. revert HC; simpl.
induction C; simpl; try discriminate.
induction e. 2: induction t2. all: intros.
all: inversion HC; try tauto.
all: unfold X_Free; simpl; unfold set_union_rv.
- inversion H9.
  elim IHC1; auto; intros. destroy H12.
  exists x; repeat split; auto. sup.
  rewrite <- H13, H10; auto.
- exists t; auto.
- exists t; repeat split. sup; simpl; auto.
- elim IHC; auto; intros. destroy H7.
  exists x. split; auto. sup; simpl; auto.
- clear H2. rewrite <- H in a; inversion a.
- clear H2. contr HC.
Qed.

Lemma EPP_Sound : forall P ps,
  Program_WF _ P -> well_ann _ P -> forall (HP:projectable Sig ps P),
  (forall p, In p ps -> str_proj (Procedures _ P) (Main P) p) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In p (Vars P X) -> In p ps) ->
  forall s tl N' s', (epp ps P HP,s) --[tl]--> (N',s') ->
  exists P' tl', ((P,s) --[tl']--> (P',s'))%CC /\
    forall H, Net N' (>>) Net (epp ps P' H).
Proof.
intros.
inversion H4.
clear tl H4 s'0 H10 H6 s0 H7 s'0 N' H9. rename N'0 into N'.
rename D into D'.
induction P as (D,C).
assert (projectable_C D C ps) as HC.
1: inversion HP; auto.
assert (SP_To _ D' (epp_C _ _ _ HC) s t N' s').
1: {
  eapply SP_To_Network_eq; eauto. eapply Network_eq_trans.
  2: apply epp_C_char. rewrite <- H5. apply Network_eq_refl.
}
destroy H. simpl in *.
  unfold CC.Procs in H; simpl in H.
inversion HP. simpl in *. destroy H10.
simpl in H1, H2, H3.
assert (forall X p, In p ps -> str_proj D (snd (D X)) p).
1: {
  intros. elim (In_dec (@eq_dec Pid) p (fst (D X))); intro.
  eapply initial_str_proj; eauto. apply (H X); auto.
  eapply initial_str_proj'; eauto. apply (H X); auto.
  intro; apply b, H0; auto.
}
induction t. 2: induction l.
+ apply SP_To_bproj_Com in H4.
  destroy H4. rename x0 into C'.
  assert (projectable_C D C' ps).
  1: { eapply CCC_To_projectable_C; eauto. }
  exists (D,C'),
     (@forget Pid Value Var RecVar (RL_Com p v q x)); repeat split; auto.
  - simpl. intros. apply MBN_refl'.
    eapply Network_eq_trans. apply (H4 H16); auto.
    apply Network_eq_sym; apply epp_C_char.
  - apply H1.
  - apply H2.
+ apply SP_To_bproj_Sel_l in H4.
  destroy H4. rename x into C'.
  assert (projectable_C D C' ps).
  1: { eapply CCC_To_projectable_C; eauto. }
  exists (D,C'),
     (@forget Pid Value Var RecVar (RL_Sel p q left)); repeat split; auto.
  - simpl. intros. apply MBN_refl'.
    eapply Network_eq_trans. apply (H4 H16); auto.
    apply Network_eq_sym; apply epp_C_char.
  - apply H1.
  - apply H2.
+ apply SP_To_bproj_Sel_r in H4.
  destroy H4. rename x into C'.
  assert (projectable_C D C' ps).
  1: { eapply CCC_To_projectable_C; eauto. }
  exists (D,C'),
     (@forget Pid Value Var RecVar (RL_Sel p q right)); repeat split; auto.
  - simpl. intros. apply MBN_refl'.
    eapply Network_eq_trans. apply (H4 H16); auto.
    apply Network_eq_sym; apply epp_C_char.
  - apply H1.
  - apply H2.
+ apply SP_To_bproj_Cond in H4.
  destroy H4. rename x into C'.
  assert (projectable_C D C' ps).
  1: { eapply CCC_To_projectable_C; eauto. }
  exists (D,C'),
     (@forget Pid Value Var RecVar (RL_Cond p)); repeat split; auto.
  - simpl. intros. eapply MBN_trans. apply (H4 H16).
    apply MBN_refl'.
    apply Network_eq_sym. apply epp_C_char.
  - apply H1.
  - apply H2.
+ elim (SP_To_bproj_Call_name _ _ _ _ _ _ _ _ _ _ H4); intros.
  destroy H15. rename x into Y. rewrite H16 in *; clear X H16.
  apply SP_To_bproj_Call in H4; auto.
  destroy H4. rename x into C'.
  assert (projectable_C D C' ps).
  1: { eapply CCC_To_projectable_C; eauto. }
  exists (D,C'),
     (@forget Pid Value Var RecVar (RL_Call Y p)); repeat split; auto.
  - simpl. intros. eapply MBN_trans. apply (H4 H17).
    apply MBN_refl'.
    apply Network_eq_sym. apply epp_C_char.
  - replace D' with (Procs (epp _ _ HP)).
    2: rewrite <- H5; auto.
    intro r; intros. rewrite epp_D_char'' with (HX:=H11 Y); auto.
    elim (In_dec (@eq_dec Pid) r (fst (D Y))); intro Hr.
    eapply bproj_unique; apply epp_C_bproj; eauto.
    rewrite epp_C_out; auto. rewrite epp_C_out'; auto.
    intro. apply Hr, H0; auto.
  - intros; apply H0; auto.
  - intros. apply Forall_forall; intros.
    apply str_proj_C; auto.
  - split; eauto. apply H; auto.
Qed.

Lemma SP_To_MBN_epp : forall D N1 s N2 s' tl D' ps C HC,
  N1 (>>) @epp_C Sig D' ps C HC -> <<N1,s>> --[tl,D]--> <<N2,s'>> ->
  exists N2', <<epp_C D' ps C HC,s>> --[tl,D]--> <<N2',s'>> /\ N2 (>>) N2'.
Proof.
intros.
rename H into Hmb, H0 into HTo.
inversion HTo.
+ clear s'0 H7 N' H6 tl H5 N H3 s0 H4 HTo.
  generalize (Hmb p); intro.
  rewrite H in H3; inversion H3.
  rename B'0 into Bp; clear B0 H8 a0 H7 e0 H6 p0 H4.
  rename H9 into H8. symmetry in H8.
  generalize (Hmb q); intro.
  rewrite H0 in H4; inversion H4.
  rename B'0 into Bq; clear B0 H11 x0 H10 a0 H9 p0 H6.
  rename H12 into H11. symmetry in H11.
  assert (p <> q) as Hpq.
  1: intro. rewrite H6, H0 in H; inversion H.
  exists (Network_rm _ (Network_rm _ (epp_C D' ps C HC) p) q | p[Bp] | q[Bq]).
  repeat split.
  1: apply S_Com with (a:ann Sig') Bp a' Bq; auto. apply Network_eq_refl.
  eapply MBN_trans. apply MBN_refl'; eauto.
  intro r. elim ((@eq_dec Pid) r p); intro Hp.
  2: elim ((@eq_dec Pid) r q); intro Hq.
  - rewrite Hp, Network_rm_add_2_p, Network_rm_add_2_p; auto.
  - rewrite Hq, Network_rm_add_2_q, Network_rm_add_2_q; auto.
  - rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
+ clear s'0 H7 N' H6 tl H5 N H3 s0 H4 HTo.
  assert (p <> q) as Hpq.
  1: intro. rewrite H3, H0 in H; inversion H.
  generalize (Hmb p); intro.
  rewrite H in H3; inversion H3.
  rename B' into Bp; clear B0 H8 a0 H7 l H6 p0 H4.
  rename H9 into H8; symmetry in H8.
  generalize (Hmb q); intro.
  rewrite H0 in H4; inversion H4.
  - symmetry in H11. apply epp_C_not_Branching_None_None in H11. inversion H11.
  - symmetry in H11. eapply epp_C_Sel_Branching_l in H11; eauto. tauto.
  - symmetry in H11. clear mBr H11 Bl0 H10 a0 H9 p0 H6.
    exists (epp_C D' ps C HC \ p \ q | p[Bp] | q[Bl']).
    repeat split.
    1: apply S_LSel with (a:ann Sig') Bp a' Bl' None; auto. apply Network_eq_refl.
    eapply MBN_trans. apply MBN_refl'; eauto.
    intro r. elim ((@eq_dec Pid) r p); intro Hp.
    2: elim ((@eq_dec Pid) r q); intro Hq.
    * rewrite Hp, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    * rewrite Hq, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    * rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
  - symmetry in H12. rewrite <- H11 in H0. clear Br H11 Bl0 H10 a0 H7 p0 H6 H4. rename Br0 into Br.
    exists (epp_C D' ps C HC \ p \ q | p[Bp] | q[Bl']).
    repeat split.
    1: apply S_LSel with (a:ann Sig') Bp a' Bl' (Some (a'0,Br')); auto. apply Network_eq_refl.
    eapply MBN_trans. apply MBN_refl'; eauto.
    intro r. elim ((@eq_dec Pid) r p); intro Hp.
    2: elim ((@eq_dec Pid) r q); intro Hq.
    * rewrite Hp, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    * rewrite Hq, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    * rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
+ clear s'0 H7 N' H6 tl H5 N H3 s0 H4 HTo.
  assert (p <> q) as Hpq.
  1: intro. rewrite H3, H0 in H; inversion H.
  generalize (Hmb p); intro.
  rewrite H in H3; inversion H3.
  rename B' into Bp; clear B0 H8 a0 H7 l H6 p0 H4.
  rename H9 into H8. symmetry in H8.
  generalize (Hmb q); intro.
  rewrite H0 in H4; inversion H4.
  - symmetry in H11. apply epp_C_not_Branching_None_None in H11. inversion H11.
  - symmetry in H12. clear mBl H9 Br0 H11 a0 H10 p0 H6.
    exists (epp_C D' ps C HC \ p \ q | p[Bp] | q[Br']).
    repeat split.
    1: apply S_RSel with (a:ann Sig') Bp a' None Br'; auto. apply Network_eq_refl.
    eapply MBN_trans. apply MBN_refl'; eauto.
    intro r. elim ((@eq_dec Pid) r p); intro Hp.
    2: elim ((@eq_dec Pid) r q); intro Hq.
    * rewrite Hp, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    * rewrite Hq, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    * rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
  - symmetry in H11. eapply epp_C_Sel_Branching_r in H11; eauto. tauto.
  - symmetry in H12. rewrite <- H7 in H0. clear Bl H7 Br0 H11 a'0 H10 p0 H6 H4. rename Bl0 into Bl.
    exists (epp_C D' ps C HC \ p \ q | p[Bp] | q[Br']).
    repeat split.
    1: apply S_RSel with (a:ann Sig') Bp a' (Some (a0,Bl')) Br'; auto. apply Network_eq_refl.
    eapply MBN_trans. apply MBN_refl'; eauto.
    intro r. elim ((@eq_dec Pid) r p); intro Hp.
    2: elim ((@eq_dec Pid) r q); intro Hq.
    * rewrite Hp, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    * rewrite Hq, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    * rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
+ clear s'0 H7 N' H6 tl H5 N H3 s0 H4 HTo.
  generalize (Hmb p); intro.
  rewrite H in H3; inversion H3.
  clear B3 H7 B0 H5 b0 H4. symmetry in H8.
  exists (Network_rm _ (epp_C D' ps C HC) p | p[B1']).
  repeat split.
  1: apply (@S_Then Sig') with b B1' B2'; auto. apply Network_eq_refl.
  eapply MBN_trans. apply MBN_refl'; eauto.
  intro r. elim ((@eq_dec Pid) r p); intro Hp.
  - rewrite Hp, Par_proj2, Par_proj2, Process_refl, Process_refl; auto;
      apply Network_rm_In.
  - rewrite Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto;
      apply Process_out; auto.
+ clear s'0 H7 N' H6 tl H5 N H3 s0 H4 HTo.
  generalize (Hmb p); intro.
  rewrite H in H3; inversion H3.
  clear B3 H7 B0 H5 b0 H4. symmetry in H8.
  exists (epp_C D' ps C HC \ p | p[B2']).
  repeat split. 
  1: apply (@S_Else Sig') with b B1' B2'; auto. apply Network_eq_refl.
  eapply MBN_trans. apply MBN_refl'; eauto.
  intro r. elim ((@eq_dec Pid) r p); intro Hp.
  - rewrite Hp, Par_proj2, Par_proj2, Process_refl, Process_refl; auto;
      apply Network_rm_In.
  - rewrite Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto;
      apply Process_out; auto.
+ clear s'0 H6 N' H5 tl H4 s0 H3 N H2 HTo.
  generalize (Hmb p); intro.
  rewrite H in H2; inversion H2.
  clear X0 H4. symmetry in H5.
  exists (epp_C D' ps C HC \ p | p [D X]).
  repeat split.
  1: apply S_Call; auto. apply Network_eq_refl.
  eapply MBN_trans. apply MBN_refl'; eauto.
  intro r. elim ((@eq_dec Pid) r p); intro Hp.
  - rewrite Hp, Par_proj2, Par_proj2. 2,3: apply Network_rm_In.
    apply MB_refl.
  - rewrite Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto;
      apply Process_out; auto.
Qed.

Lemma SPP_To_MBN_epp : forall P1 s P2 s' tl ps P HP,
  (forall X, Procs P1 X = Procs (epp ps P HP) X) ->
  Net P1 (>>) Net (epp ps P HP) -> SPP_To Sig' (P1,s) tl (P2,s') ->
  exists P2', ((epp ps P HP,s) --[tl]--> (P2',s')) /\ Net P2 (>>) Net P2'
  /\ forall X, Procs P2 X = Procs P2' X.
Proof.
intros.
induction P1 as (D,N1), P2 as (D2,N2).
rewrite <- (SPP_To_Defs_stable _ _ _ _ _ _ _ _ H1);
rewrite <- (SPP_To_Defs_stable _ _ _ _ _ _ _ _ H1) in H1; clear D2.
induction P as (D',C).
inversion HP. inversion_clear H3. clear H5. simpl in H2, H4.
inversion H1. clear s'0 H10 N' H9 tl H5 s0 H7 N H6 D0 H3 H1.
eapply SP_To_MBN_epp with (HC:=H2) in H8; eauto.
2: intro r; rewrite <- epp_C_char with (HP:=HP); auto.
destroy H8. rename x into N2'.
exists (Procs (epp _ _ HP),N2'); repeat split; auto.
rewrite (SP_eta _ (epp _ _ HP)); constructor.
simpl. apply SP_To_Defs_wd with D; auto.
eapply SP_To_Network_eq; eauto.
apply Network_eq_sym; apply epp_C_char.
Qed.

(** Generalizing the last result to -->* already requires the EPP Theorem. *)

Lemma SPP_ToStar_MBN_epp : forall P1 s P2 s' tl ps P,
  Program_WF _ P -> well_ann _ P -> forall (HP:projectable Sig ps P),
  (forall p, In p ps -> str_proj (Procedures _ P) (Main P) p) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In p (Vars P X) -> In p ps) ->
  (forall X, Procs P1 X = Procs (epp ps P HP) X) ->
  Net P1 (>>) Net (epp ps P HP) -> (P1,s) --[tl]-->* (P2,s') ->
  exists P2', (epp ps P HP,s) --[tl]-->* (P2',s') /\ Net P2 (>>) Net P2'
  /\ forall X, Procs P2 X = Procs P2' X.
Proof.
intros.
induction P1 as (D,N1), P2 as (D2,N2).
rewrite <- (SPP_ToStar_Defs_stable _ _ _ _ _ _ _ _ H6);
rewrite <- (SPP_ToStar_Defs_stable _ _ _ _ _ _ _ _ H6) in H6; clear D2.
induction P as (D',C).
revert dependent C. revert s s' N1 N2 H6. induction tl; intros.
+ inversion H6. rewrite <- H8.
  exists (epp _ _ HP); repeat split; auto. apply (SPT_Base Sig'); auto.
+ inversion H6. clear c3 H11 l H8 t H7 c1 H9 H6. rename a into t.
  induction c2 as ((D2,N3),s'').
  rewrite <- (SPP_To_Defs_stable _ _ _ _ _ _ _ _ H10) in H12, H10. clear D2.
  apply SPP_To_MBN_epp with (HP:=HP) in H10; auto.
  destroy H10. induction x as (D3,N3'). simpl in H7, H10.
  generalize H6 as H6'; intro.
  rewrite (SP_eta _ (epp _ _ HP)) in H6'.
  rewrite <- (SPP_To_Defs_stable _ _ _ _ _ _ _ _ H6') in H6, H10, H6'. clear D3.
  rewrite <- SP_eta in H6'.
  apply EPP_Sound in H6; auto. destroy H6. rename x0 into t'.
  induction x as (D'3,C'').
  rewrite <- (CCP_To_Defs_stable _ _ _ _ _ _ _ _ H8) in H6, H8. clear D'3.
  assert (projectable Sig ps (D',C'')).
  1: eapply CCP_To_projectable; eauto.
  generalize (H6 H9); clear H6; intro. simpl in H6.
  generalize H12 as H12'; intro.
  inversion HP. clear H11; inversion_clear H13. simpl in H11; clear H14.
  rename H11 into HD.
  apply IHtl with (HP:=H9) in H12; auto. clear IHtl.
  destroy H12. rename x into P2'. induction P2' as (D2',N2').
  rewrite (SP_eta _ (epp _ _ H9)) in H11.
  rewrite <- (SPP_ToStar_Defs_stable _ _ _ _ _ _ _ _ H11) in H13, H12, H11.
  clear D2'. rewrite <- SP_eta in H11. simpl in H11, H12, H13.
  apply SPP_ToStar_MBN with (P1':=(Procs (epp _ _ HP),N3')) in H11; auto.
  destroy H11. rename x into P2'. simpl in H11, H15.
  exists P2'; repeat split; auto.
  - econstructor; eauto.
  - simpl.
    apply SPP_ToStar_MBN with (P1':=(D,N3)) in H14; auto.
    destroy H14. apply MBN_trans with (Net x); auto.
    apply MBN_refl'.
    change N2 with (Net (D,N2)).
    eapply SPP_ToStar_deterministic_1; eauto.
    simpl; intro.
    rewrite H12. induction X. repeat rewrite epp_D_char with (HD:=HD); auto.
  - simpl; intro. rewrite H12, <- H11.
    induction X. repeat rewrite epp_D_char with (HD:=HD); auto.
  - simpl; intro. induction X; repeat rewrite epp_D_char with (HD:=HD); auto.
  - eapply CCP_To_Program_WF; eauto.
  - eapply CCP_To_str_proj; eauto.
  - intros. apply H2. eapply CCP_To_pn; eauto.
  - intro; rewrite H10. induction X; repeat rewrite epp_D_char with (HD:=HD); auto.
  - apply MBN_trans with N3'; auto.
Qed.

Lemma EPP_Sound' : forall P ps,
  Program_WF _ P -> well_ann _ P -> forall (HP:projectable Sig ps P),
  (forall p, In p ps -> str_proj (Procedures _ P) (Main P) p) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In p (Vars P X) -> In p ps) ->
  forall s tl P' s', (epp ps P HP,s) --[tl]-->* (P',s') ->
  exists P'' tl', ((P,s) --[tl']-->* (P'',s'))%CC /\
    forall H, Net P' (>>) Net (epp ps P'' H).
Proof.
intros.
induction P as (D,C), P' as (D',N).
revert dependent N. revert dependent C. revert D' s s'.
induction tl; intros; inversion H4.
+ eexists; exists nil. repeat split. apply (CCT_Base Sig); auto.
  intro. apply MBN_refl'.
  inversion HP. simpl in H9.
  apply Network_eq_trans with (epp_C D ps C H11).
  2: apply Network_eq_sym. all: apply epp_C_char.
+ clear c3 H9 l H6 t H5 c1 H7 H4. rename a into t.
  induction c2 as (P'', s'').
  eapply SPP_To_MBN_epp in H8; eauto. destroy H8.
  rename x into P'. 2: apply MBN_refl.
  rewrite (SP_eta _ (epp _ _ HP)), (SP_eta _ P') in H4.
  generalize (SPP_To_Defs_stable _ _ _ _ _ _ _ _ H4); intro H4'.
  rewrite <- SP_eta, <- SP_eta in H4.
  apply EPP_Sound in H4; auto. destroy H4.
  rename x into P1, x0 into t'.
  assert (projectable Sig ps P1).
  1: eapply CCP_To_projectable; eauto.
  induction P1 as (D1, C1).
  rewrite <- (CCP_To_Defs_stable _ _ _ _ _ _ _ _ H6) in H4, H7, H6. clear D1.
  generalize (H4 H7); clear H4; intro.
  assert (Program_WF _ (D,C1)).
  1: eapply CCP_To_Program_WF; eauto.
  assert (forall p, In p ps -> str_proj D C1 p).
  1: {
    change D with (Procedures _ (D,C1)).
    change C1 with (Main (D,C1)) at 2.
    intros. inversion HP. destroy H13.
    eapply CCP_To_str_proj with (P:=(D,C)); eauto.
  }
  assert (forall p, In p (CCC_pn C1 (Vars (D,C1))) -> In p ps).
  1:{
    change C1 with (Main (D,C1)) at 1.
    intros. apply H2. eapply CCP_To_pn; eauto.
  }
  apply SPP_ToStar_MBN_epp with (HP:=H7) in H10; auto.
  - destroy H10.
    rename x into P1. induction P1 as (D1,N1).
    eapply IHtl in H9; auto. 2: apply H13.
    destroy H9. rename x into P2, x0 into tl'.
    clear IHtl. exists P2, (t'::tl').
    repeat split.
    eapply CCT_Step; eauto.
    intro. apply MBN_trans with N1; auto.
  - intro. rewrite H8, <- H4'.
    inversion HP. destroy H14. induction X.
    simpl in H15; repeat rewrite epp_D_char with (HD:=H15); auto.
  - apply MBN_trans with (Net P'); auto.
Qed.

End Soundness.

End EPP_Theorem.
