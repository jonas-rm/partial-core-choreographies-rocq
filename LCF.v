Require Export Basic.
Require Export Common.
Require Export MC.

Module Temp (P X V E B R:DecType) (Ev:Eval E X V V) (BEv:Eval B X V Bool).

Module Import MCBase := MCBase P X V E B R Ev BEv.




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
  2: { exfalso. rewrite H17 in H7. apply (lt_irrefl _ H7). }
  2: { exfalso. rewrite H7 in H17. apply (lt_irrefl _ H17). }
  2: { exfalso. rewrite <- H14, <- H4, (set_size_1 _ _ H17 p p0) in Htl; auto. }
  case (P.eq_dec p p0); intro Hpp0.
  1: { exfalso. rewrite <- H14, <- H4, Hpp0 in Htl; auto. }
  clear HC' HC'' Htl s'1 H16 C'' H15 tl'' H14 s1 H13 C1 H11 ps0 H10.
  clear X0 H9 s'0 H6 C' H5 tl' H4 C0 H1 ps H0 X H IHC.
  rename l into ps, r into X.
  elim (Nat.eq_dec (set_size_pid ps) 2); intro HX.
  * exists C, s.
    split; apply C_Call_Finish; try ESEs.
    - revert HX.
      unfold set_size_pid, set_remove_pid.
      intro; rewrite (set_size_remove' P.eq_dec) with ps p in HX; auto.
    - apply set_remove'_3; auto.
    - revert HX.
      unfold set_size_pid, set_remove_pid.
      intro; rewrite (set_size_remove' P.eq_dec) with ps p0 in HX; auto.
    - apply set_remove'_3; auto.
  * exists (RT_Call X (set_remove_pid p (set_remove_pid p0 ps)) C), s.
    unfold set_remove_pid.
    rewrite set_remove'_remove' at 1.
    split; (apply C_Call_Enter; try ESEs;
      [eapply set_size_neq_2; eauto | apply set_remove'_3; auto]).
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
  clear H H0 s'1 H16 C'1 H15 tl2 H10 s1 H12 C1 H11 Procs1 H9 s'0 H8.
  clear C'0 H7 tl1 H2 s0 H4 C0 H3 Procs0 H1.
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

Lemma diamond_3 : forall c tl1 tl2 c1 c2,
  c --[ tl1 ]-->* c1 -> c --[ tl2 ]--> c2 ->
  {exists tl', c2 --[ tl' ]-->* c1}
  + {exists c', c1 --[ tl2 ]--> c' /\ c2 --[ tl1 ]-->* c'}.
Proof.
induction c, c1, c2. induction a, p, p0.
rename Procedures1 into Defs', Main1 into C', s into s'.
rename Procedures2 into Defs'', Main2 into C'', s0 into s''.
rename Procedures0 into Defs, Main0 into C, b into s.
intros.
rewrite <- (MCP_To_Procs_stable _ _ _ _ _ _ _ H0);
rewrite <- (MCP_To_Procs_stable _ _ _ _ _ _ _ H0) in H0.
rewrite <- (MCP_ToStar_Procs_stable _ _ _ _ _ _ _ H);
rewrite <- (MCP_ToStar_Procs_stable _ _ _ _ _ _ _ H) in H.
clear Defs' Defs''.
revert C s tl2 C' s' C'' s'' H H0; induction tl1.
+ right.
  inversion H.
  rewrite <- H2, <- H4. eexists; split; eauto. constructor.
+ intros.






Lemma termination_unique : forall c tl1 c1 tl2 c2,
  c --[tl1]-->* c1 -> c --[tl2]-->* c2 ->
  Main (fst c1) = End -> Main (fst c2) = End -> eq_state_ext (snd c1) (snd c2).
induction c. induction a.
rename Procedures0 into Defs, Main0 into C, b into s.
intro tl; revert C s.
induction tl; simpl; intros.
+ inversion H.
  rewrite <- H5 in H1. simpl in H1. rewrite H1 in H0.
  inversion H0; simpl. ESEr.
  exfalso. inversion H4. inversion H15.
+ case_eq tl2; intros.
  - exfalso. rewrite H3 in H0; inversion H0.
    rewrite <- H6 in H2. simpl in H2; rewrite H2 in H.
    inversion H. inversion H9. inversion H17.
  - rewrite H3 in H0; clear H3 tl2. rename l into tl2.
    inversion_clear H; inversion_clear H0.
    elim (diamond_2 _ _ _ _ _ H3 H).
    * intro. inversion_clear a0.
      induction c3, c4. induction a0, p.
      simpl in H0, H6; inversion H0; clear H0.
      rewrite <- H9 in H5, H; clear Main1 H9.
      rewrite <- H8 in H5, H; clear Procedures1 H8.
      rewrite <- (MCP_To_Procs_stable _ _ _ _ _ _ _ H3) in H, H4, H5, H3.
      clear Procedures0.
      rename Main0 into C', b into s', s0 into s''.
      induction c2.
      case_eq tl2; intros.
      2: {
        apply MCP_ToStar_eq with (s1':=s') (s2':=b) in H5.
        apply (IHtl _ _ _ _ _ H4 H5); auto. ESEs. ESEr.
        rewrite H0; discriminate.
      }
      rewrite H0 in H5; inversion H5; clear tl2 H0.
      simpl.
      rewrite <- H8 in H2, H5; clear a0 H8.
      rewrite <- H10 in H2, H5; rewrite <- H10; clear b H10.
      simpl in H2. rewrite H2 in H3, H4, H, H5; clear H2 C' c H7.
      inversion H4; simpl; auto.
      inversion H0. inversion H15.
    * inversion H3; inversion H.
      clear H H3 t H12 s1 H14 C1 H13 Procs1 H11 a H6 s0 H8 C0 H7 Procs0 H0.
      induction c3, c4. induction a, p.
      inversion H9; inversion H15. clear H9 H15.
      revert H4 H5 H10 H16.
      rewrite <- H0, <- H3, <- H6, <- H7, <- H8, H11.
      clear s'0 H11 Main1 H8 Procedures0 H0 Procedures1 H7 b H6 Main0 H3; intros.
      elim b; clear b; intros c' Hc'; inversion_clear Hc'.

Lemma convergence : forall c tls1 tls2 c1 c2,
  c --[ tls1 ]-->* c1 -> c --[ tls2 ]-->* c2 ->
  tls1 <> tls2 -> exists c', c1 --[ tl2 ]--> c' /\ c2 --[ tl1 ]--> c'.
