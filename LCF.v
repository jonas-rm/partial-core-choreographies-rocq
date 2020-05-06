Require Export Basic.
Require Export Common.
Require Export MC.

Module Temp (P X V E B R:DecType) (Ev:Eval E X V V) (BEv:Eval B X V Bool).

Module Import MCBase := MCBase P X V E B R Ev BEv.

Lemma set_remove'_remove' : forall A A_dec (S:set A) x y,
  set_remove' A_dec x (set_remove' A_dec y S) = set_remove' A_dec y (set_remove' A_dec x S).
Proof.
induction S; simpl; auto.
intros; do 2 elim A_dec; simpl; intros.
+ rewrite a0, a1; auto.
+ elim A_dec; simpl; auto.
  intro; elim b0; auto.
+ elim A_dec; simpl; auto.
  intro; elim b0; auto.
+ elim A_dec; simpl; auto.
  1: intro; elim b; auto.
  elim A_dec; simpl; auto.
  1: intro; elim b0; auto.
  intros; rewrite IHS; auto.
Qed.

Lemma set_remove'_2_weird : forall T T_dec (X:set T) x y, x<>y -> 
  In x X -> In y X -> set_size T_dec X <> 2 -> set_size T_dec (set_remove' T_dec x X) > 1.
Proof.
intros.
apply lt_S_n.
rewrite <- set_size_remove'; auto.
elim (nat_total_order _ _ H2); auto.
clear H2; intro.
exfalso.
rewrite (set_size_remove' T_dec X x) in H2; auto.
rewrite (set_size_remove' T_dec (set_remove' T_dec x X) y) in H2.
inversion H2. inversion H4. inversion H6.
apply set_remove'_In; auto.
Qed.

(*
Lemma set_remove_2_weird : forall A A_dec (S:set A) x y, x<>y ->
  In x S -> In y S -> length S = 2 -> set_remove A_dec x S = (y::nil).
Proof.
intros.
destruct S; auto; try (inversion H2; fail).
destruct S; auto; try (inversion H2; fail).
destruct S; auto; try (inversion H2; fail).
clear H2.
simpl in H0, H1.
inversion_clear H0.
+ revert H1; rewrite H2; intros.
  simpl; elim A_dec; simpl; intro Hx.
  2: elim Hx; auto.
  inversion_clear H1; intros.
  1: elim H; auto.
  inversion_clear H0; inversion H1; auto.
+ inversion_clear H2; inversion H0; simpl.
  elim A_dec; simpl; intro Hx.
  - exfalso. rewrite <- Hx, H0 in H1.
    elim H; inversion_clear H1; auto.
    inversion_clear H3; auto. inversion H1.
  - elim A_dec; intro H'x.
    2: elim H'x; auto.
    inversion_clear H1; inversion H3; inversion H1; auto.
    elim H; transitivity a0; auto.
Qed.
*)

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

Lemma beval_eq : forall b s s' p, eq_state_ext s s' ->
  beval_on_state b s p = beval_on_state b s' p.
Proof.
intros; unfold beval_on_state; simpl.
apply BEv.eval_wd.
apply H.
Qed.

Lemma beval_neq : forall b s p q x v, p <> q ->
  beval_on_state b s p = beval_on_state b (update s q x v) p.
Proof.
intros; unfold beval_on_state; simpl.
replace (s p) with (update s q x v p); auto.
unfold update.
case_eq (Pid_dec q p); auto.
intro; elim H.
apply Pdec.eqb_eq in H0; auto.
Qed.

Lemma MCC_To_eq : forall Defs C s1 tl C' s2 s1' s2',
  eq_state_ext s1 s1' -> eq_state_ext s2 s2' ->
  MCC_To Defs C s1 tl C' s2 -> MCC_To Defs C s1' tl C' s2'.
Proof.
intros.
induction H1.
+ unfold v.
  rewrite (eval_eq e s s1'); auto.
  apply C_Com.
  ESEt s'. ESEs. eESEt.
  rewrite <- (eval_eq e s s1'); auto. fold v.
  ESEc; auto.
+ apply C_Sel. ESEt s. ESEs. ESEt s'.
+ apply C_Then. ESEt s. ESEs. ESEt s'.
  rewrite <- (beval_eq b s); auto.
+ apply C_Else. ESEt s. ESEs. ESEt s'.
  rewrite <- (beval_eq b s); auto.
+ apply C_Delay_Eta; auto.
+ apply C_Delay_Cond; auto.
+ apply C_Call_Local; auto. ESEt s. ESEs. ESEt s'.
+ apply C_Call_Start; auto. ESEt s. ESEs. ESEt s'.
+ apply C_Call_Enter; auto. ESEt s. ESEs. ESEt s'.
+ apply C_Call_Finish; auto. ESEt s. ESEs. ESEt s'.
Qed.

Lemma MCC_To_disjoint_eval : forall Defs C s tl s' p e C',
  disjoint_p_rl p tl -> MCC_To Defs C s tl C' s' ->
  eval_on_state e s p = eval_on_state e s' p.
Proof.
intros.
induction H0; auto; try (apply eval_eq; auto; fail).
inversion_clear H.
transitivity (eval_on_state e (update s q x v) p).
apply eval_neq; auto.
apply eval_eq; ESEs.
Qed.

Lemma MCC_To_disjoint_beval : forall Defs C s tl s' p b C',
  disjoint_p_rl p tl -> MCC_To Defs C s tl C' s' ->
  beval_on_state b s p = beval_on_state b s' p.
Proof.
intros.
induction H0; auto; try (apply beval_eq; auto; fail).
inversion_clear H.
transitivity (beval_on_state b (update s q x v) p).
apply beval_neq; auto.
apply beval_eq; ESEs.
Qed.

Lemma MCC_To_disjoint_update : forall Defs C s tl s' p x v C',
  disjoint_p_rl p tl -> MCC_To Defs C s tl C' s' ->
  MCC_To Defs C (update s p x v) tl C' (update s' p x v).
Proof.
intros.
induction H0; try (constructor; auto; try ESEc; auto; fail).
+ inversion_clear H.
  unfold v0. rewrite (eval_neq e s p0 p x v); auto.
  apply C_Com.
  rewrite <- (eval_neq e s p0 p x v); auto.
  fold v0.
  ESEt (update (update s q x0 v0) p x v). ESEc; auto.
  apply update_independent; auto.
+ apply C_Then. ESEc; auto.
  rewrite <- beval_neq; auto.
+ apply C_Else. ESEc; auto.
  rewrite <- beval_neq; auto.
Qed.

Lemma MCC_To_deterministic' : forall Defs C s tl C1 s1 C2 s2,
  MCC_To Defs C s tl C1 s1 -> MCC_To Defs C s tl C2 s2 -> C1 = C2.
Proof.
(* Might be simpler: induction tl *)
induction C; intros; inversion H; inversion H0; 
  try (transitivity C; auto; fail).
- auto.
- rewrite H3 in H11; elim (lt_irrefl _ H11).
- rewrite H11 in H3; elim (lt_irrefl _ H3).
- rewrite <- H6 in H14; inversion H14; auto.
- rewrite <- H6 in H16; inversion H16; auto.
- rewrite H19 in H9; elim (lt_irrefl _ H9).
- rewrite H9 in H19; elim (lt_irrefl _ H19).
- exfalso. rewrite <- H1, <- H4 in H10.
  inversion_clear H10. inversion_clear H16. auto.
- exfalso. rewrite <- H1, <- H4 in H10.
  inversion_clear H10. inversion_clear H16. auto.
- exfalso. rewrite <- H12, <- H9 in H3.
  inversion_clear H3. inversion_clear H16. auto.
- exfalso. rewrite <- H12, <- H9 in H3.
  inversion_clear H3. inversion_clear H16. auto.
- elim (IHC _ _ _ _ _ _ H8 H16); auto.
- transitivity C1; auto.
- rewrite H10 in H20; inversion H20.
- rewrite <- H6 in H19; elim H19; auto.
- rewrite H10 in H20; inversion H20.
- transitivity C2; auto.
- rewrite <- H6 in H19; elim H19; auto.
- rewrite <- H17 in H9; elim H9; auto.
- rewrite <- H17 in H9; elim H9; auto.
- rewrite (IHC1 _ _ _ _ _ _ H10 H21); rewrite (IHC2 _ _ _ _ _ _ H11 H22); auto.
Qed.

Lemma MCC_To_deterministic'' : forall Defs C s tl C1 s1 C2 s2,
  MCC_To Defs C s tl C1 s1 -> MCC_To Defs C s tl C2 s2 ->
  eq_state_ext s1 s2.
Proof.
induction C; intros; inversion H; inversion H0;
  try (ESEt s; ESEs; fail); auto.
- ESEt (update s q x v).
  revert H14; unfold v, v0.
  rewrite <- H1 in H8; inversion H8.
  ESEs.
- rewrite <- H4 in H11; inversion H11.
- rewrite <- H1, <- H4 in H10.
  inversion_clear H10. inversion H16. elim H10; auto.
- rewrite <- H4 in H11; inversion H11.
- rewrite <- H1, <- H4 in H10.
  inversion_clear H10. inversion H16. elim H10; auto.
- rewrite <- H9, <- H12 in H3.
  inversion_clear H3. inversion H16. elim H3; auto.
- rewrite <- H9, <- H12 in H3.
  inversion_clear H3. inversion H16. elim H3; auto.
- eauto.
- rewrite <- H6 in H19; elim H19; auto.
- rewrite <- H6 in H19; elim H19; auto.
- rewrite <- H17 in H9; elim H9; auto.
- rewrite <- H17 in H9; elim H9; auto.
- eauto.
Qed.

Lemma MCC_To_deterministic : forall Defs C s tl1 C1 s1 tl2 C2 s2,
  MCC_To Defs C s tl1 C1 s1 -> MCC_To Defs C s tl2 C2 s2 ->
  tl1 = tl2 -> C1 = C2 /\ eq_state_ext s1 s2.
Proof.
intros.
rewrite H1 in H; split.
eapply MCC_To_deterministic'; eauto.
eapply MCC_To_deterministic''; eauto.
Qed.

Lemma MCC_To_rl_implies_state : forall Defs C1 s tl C1' s1 C2 C2' s2,
  MCC_To Defs C1 s tl C1' s1 -> MCC_To Defs C2 s tl C2' s2 ->
  eq_state_ext s1 s2.
Proof.
induction C1; induction C2; intros; inversion H; inversion H0;
  try (ESEt s; ESEs; fail); eauto;
  try (rewrite <- H4 in H13; inversion H13; fail);
  try (rewrite <- H6 in H14; inversion H14; fail).
+ rewrite <- H6 in H12; inversion H12.
+ rewrite <- H6 in H12; inversion H12.
+ ESEt (update s q x v). ESEs. ESEt (update s q0 x0 v0).
  rewrite <- H4 in H11; inversion H11. ESEr.
+ rewrite <- H4 in H11; inversion H11.
+ rewrite <- H4 in H11; inversion H11.
Qed.

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
      ++ apply set_remove'_In; auto.
      ++ revert HX.
         unfold set_size_pid, set_remove_pid.
         intro; rewrite (set_size_remove' P.eq_dec) with (fst (Defs X)) p0 in HX; auto.
      ++ apply set_remove'_In; auto.
    * exists (RT_Call X (set_remove_pid p (set_remove_pid p0 (fst (Defs X)))) (snd (Defs X))), s.
      unfold set_remove_pid.
      rewrite set_remove'_remove' at 1.
      split; (apply C_Call_Enter; try ESEs;
        [eapply set_remove'_2_weird; eauto | apply set_remove'_In; auto]).
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
    - apply set_remove'_In; auto.
    - revert HX.
      unfold set_size_pid, set_remove_pid.
      intro; rewrite (set_size_remove' P.eq_dec) with ps p0 in HX; auto.
    - apply set_remove'_In; auto.
  * exists (RT_Call X (set_remove_pid p (set_remove_pid p0 ps)) C), s.
    unfold set_remove_pid.
    rewrite set_remove'_remove' at 1.
    split; (apply C_Call_Enter; try ESEs;
      [eapply set_remove'_2_weird; eauto | apply set_remove'_In; auto]).
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

Lemma diamond : forall c tl1 tl2 c1 c2,
  c --[ tl1 ]--> c1 -> c --[ tl2 ]--> c2 ->
  tl1 <> tl2 -> exists c', c1 --[ tl2 ]--> c' /\ c2 --[ tl1 ]--> c'.
Proof.
induction c.
induction a.
rename Procedures0 into Defs, Main0 into C, b into s.
intros.
inversion H; inversion H0.
elim (diamond_Chor _ _ _ _ _ _ _ _ _ H7 H13); intros.
2: { intro; apply H1. rewrite <- H9, <- H3, H14. auto. }
inversion_clear H14. inversion_clear H15.
exists (Build_Program Defs x,x0); split; constructor; auto.
Qed.
