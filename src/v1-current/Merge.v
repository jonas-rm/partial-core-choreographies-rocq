Require Export BranchingOrder.

Section SP_Merge.

Open Scope SP.

(** * Merging of two behaviours
  Merging is defined inductively as a ternary relation. *)

Variable Sig : Signature.

Inductive merge : Behaviour Sig -> Behaviour Sig -> Behaviour Sig -> Prop :=
| merge_End : merge (End _) (End _) (End _)
| merge_Send : forall p e a B1 B2 B, merge B1 B2 B -> merge (p ! e @! a; B1) (p ! e @! a;B2) (p ! e @! a;B)
| merge_Recv : forall p x a B1 B2 B, merge B1 B2 B -> merge (p ? x @? a;B1) (p ? x @? a;B2) (p ? x @? a;B)
| merge_Sel : forall p l a B1 B2 B, merge B1 B2 B -> merge (p (+) l @+ a;B1) (p (+) l @+ a;B2) (p (+) l @+ a;B)
| merge_Branching_NNNN : forall p,
                          merge (p & None // None) (p & None // None) (p & None // None)
| merge_Branching_NNNS : forall p aR bR,
                          merge (p & None // None) (p & None // Some (aR,bR)) (p & None // Some (aR,bR))
| merge_Branching_NNSN : forall p aL bL,
                          merge (p & None // None) (p & Some (aL,bL) // None) (p & Some (aL,bL) // None)
| merge_Branching_NNSS : forall p aL bL aR bR,
                          merge (p & None // None) (p & Some (aL,bL) // Some (aR,bR)) (p & Some (aL,bL) // Some (aR,bR))
| merge_Branching_NSNN : forall p aR bR,
                          merge (p & None // Some (aR,bR)) (p & None // None) (p & None // Some (aR,bR))
| merge_Branching_NSNS : forall p aR bR1 bR2 bR, merge bR1 bR2 bR ->
                          merge (p & None // Some (aR,bR1)) (p & None // Some (aR,bR2)) (p & None // Some (aR,bR))
| merge_Branching_NSSN : forall p aL bL aR bR,
                          merge (p & None // Some (aR,bR)) (p & Some (aL,bL) // None) (p & Some (aL,bL) // Some (aR,bR))
| merge_Branching_NSSS : forall p aL bL aR bR1 bR2 bR, merge bR1 bR2 bR ->
                          merge (p & None // Some (aR,bR1)) (p & Some (aL,bL) // Some (aR,bR2)) (p & Some (aL,bL) // Some (aR,bR))
| merge_Branching_SNNN : forall p aL bL,
                          merge (p & Some (aL,bL) // None) (p & None // None) (p & Some (aL,bL) // None)
| merge_Branching_SNNS : forall p aL bL aR bR,
                          merge (p & Some (aL,bL) // None) (p & None // Some (aR,bR)) (p & Some (aL,bL) // Some (aR,bR))
| merge_Branching_SNSN : forall p aL bL1 bL2 bL, merge bL1 bL2 bL ->
                          merge (p & Some (aL,bL1) // None) (p & Some (aL,bL2) // None) (p & Some (aL,bL) // None)
| merge_Branching_SNSS : forall p aL bL1 bL2 bL aR bR, merge bL1 bL2 bL ->
                          merge (p & Some (aL,bL1) // None) (p & Some (aL,bL2) // Some (aR,bR)) (p & Some (aL,bL) // Some (aR,bR))
| merge_Branching_SSNN : forall p aL bL aR bR,
                          merge (p & Some (aL,bL) // Some (aR,bR)) (p & None // None) (p & Some (aL,bL) // Some (aR,bR))
| merge_Branching_SSNS : forall p aL bL aR bR1 bR2 bR, merge bR1 bR2 bR ->
                          merge (p & Some (aL,bL) // Some (aR,bR1)) (p & None // Some (aR,bR2)) (p & Some (aL,bL) // Some (aR,bR))
| merge_Branching_SSSN : forall p aL bL1 bL2 bL aR bR, merge bL1 bL2 bL ->
                          merge (p & Some (aL,bL1) // Some (aR,bR)) (p & Some (aL,bL2) // None) (p & Some (aL,bL) // Some (aR,bR))
| merge_Branching_SSSS : forall p aL bL1 bL2 bL aR bR1 bR2 bR, merge bL1 bL2 bL -> merge bR1 bR2 bR ->
                          merge (p & Some (aL,bL1) // Some (aR,bR1)) (p & Some (aL,bL2) // Some (aR,bR2)) (p & Some (aL,bL) // Some (aR,bR))
| merge_Cond           : forall b Bt1 Be1 Bt2 Be2 Bt Be, merge Bt1 Bt2 Bt -> merge Be1 Be2 Be ->
                         merge (If b Then Bt1 Else Be1) (If b Then Bt2 Else Be2) (If b Then Bt Else Be)
| merge_Call           : forall X, merge (Call _ X) (Call _ X) (Call _ X)
.

(** We start by proving that this relation is functional. *)

Lemma merge_unique : forall B1 B2 B B',
  merge B1 B2 B -> merge B1 B2 B' -> B = B'.
Proof.
intros. revert dependent B'.
induction H; intros.
all: try (inversion H0; auto; fail).
1,2,3: inversion H0; rewrite (IHmerge B4); auto.
8: inversion H1; rewrite (IHmerge1 Bt4), (IHmerge2 Be4); auto.
1,2,5: inversion H0; rewrite (IHmerge bR4); auto.
1,2,3: inversion H0; rewrite (IHmerge bL4); auto.
inversion H1; rewrite (IHmerge1 bL4), (IHmerge2 bR4); auto.
Qed.

(** Furthermore, we can decide whether two behaviours are mergeable,
  and compute their merge in the affirmative case. *)

Ltac fail_with H := right; intro H; induction H as [B HB]; inversion HB; auto.

Lemma merge_computable : forall B1 B2,
  { B | merge B1 B2 B } + { ~exists B, merge B1 B2 B }.
Proof.
induction B1 using Behaviour_rec'; induction B2 using Behaviour_rec'; simpl; auto.
all: try (fail_with H; fail).
all: try clear IHB2; try clear IHB2_1 IHB2_2.
1: left; exists (End _); constructor.
21: {
  case (eq_dec X X0); intro HX.
  left; exists (Call _ X); rewrite HX; constructor.
  fail_with H.
}
20: {
  case (eq_dec b b0); intro Hb. rewrite <- Hb in *; clear b0 Hb.
  induction (IHB1_1 B2_1) as [ [BT HBT] | HBT ].
  induction (IHB1_2 B2_2) as [ [BE HBE] | HBE ].
  left; exists (If b Then BT Else BE). constructor; auto.
  all: fail_with H; eauto.
}
all: case (eq_dec p p0); intro Hp;
  [ rewrite <- Hp in *; clear p0 Hp | fail_with H].
all: try (left; eexists; constructor; fail). (* a lot of merges *)
+ case (eq_dec e e0); intro He.
  case (eq_dec a a0); intro Ha.
  induction (IHB1 B2) as [ [B HB] | HB].
  left. exists (p ! e @! a; B). rewrite He, Ha. constructor; auto.
  all: right; intro.
  apply HB. induction H as [B H']. inversion_clear H'. exists B4; auto.
  all: induction H as [B HB]; inversion HB; auto.
+ case (eq_dec v v0); intro Hv.
  case (eq_dec a a0); intro Ha.
  induction (IHB1 B2) as [ [B HB] | HB].
  left. exists (p ? v @? a; B). rewrite Hv, Ha. constructor; auto.
  all: right; intro.
  apply HB. induction H as [B H']. inversion_clear H'. exists B4; auto.
  all: induction H as [B HB]; inversion HB; auto.
+ case (eq_dec l l0); intro Hl.
  case (eq_dec a a0); intro Ha.
  induction (IHB1 B2) as [ [B HB] | HB].
  left. exists (p (+) l @+ a; B). rewrite Hl, Ha. constructor; auto.
  all: right; intro.
  apply HB. induction H as [B H']. inversion_clear H'. exists B4; auto.
  all: induction H as [B HB]; inversion HB; auto.
+ case (eq_dec a a0); intro Ha. 2: fail_with H.
  rewrite <- Ha in *; clear a0 Ha.
  induction (IHB1 B2) as [ [BL HBL] | H].
  left. exists (p & Some (a,BL) // None); constructor; auto.
  fail_with HB. apply H. exists bL; auto.
+ case (eq_dec a a0); intro Ha. 2: fail_with H.
  rewrite <- Ha in *; clear a0 Ha.
  induction (IHB1 B2_1) as [ [BL HBL] | H].
  left. exists (p & Some (a,BL) // Some (a',B2_2)); constructor; auto.
  fail_with HB. apply H. exists bL; auto.
+ case (eq_dec a a0); intro Ha. 2: fail_with H.
  rewrite <- Ha in *; clear a0 Ha.
  induction (IHB1 B2) as [ [BR HBR] | H].
  left. exists (p & None // Some (a,BR)); constructor; auto.
  fail_with HB. apply H. exists bR; auto.
+ case (eq_dec a a'); intro Ha. 2: fail_with H.
  rewrite <- Ha in *; clear a' Ha.
  induction (IHB1 B2_2) as [ [BR HBR] | H].
  left. exists (p & Some (a0,B2_1) // Some (a,BR)); constructor; auto.
  fail_with HB. apply H. exists bR; auto.
+ case (eq_dec a a0); intro Ha. 2: fail_with H.
  rewrite <- Ha in *; clear a0 Ha.
  induction (IHB1_1 B2) as [ [BL HBL] | H].
  left. exists (p & Some (a,BL) // Some (a',B1_2)); constructor; auto.
  fail_with HB. apply H. exists bL; auto.
+ case (eq_dec a' a0); intro Ha. 2: fail_with H.
  rewrite <- Ha in *; clear a0 Ha.
  induction (IHB1_2 B2) as [ [BR HBR] | H].
  left. exists (p & Some (a,B1_1) // Some (a',BR)); constructor; auto.
  fail_with HB. apply H. exists bR; auto.
+ case (eq_dec a a0); intro Ha. 2: fail_with H.
  rewrite <- Ha in *; clear a0 Ha.
  case (eq_dec a' a'0); intro Ha. 2: fail_with H.
  rewrite <- Ha in *; clear a'0 Ha.
  induction (IHB1_1 B2_1) as [ [BL HBL] | H].
  induction (IHB1_2 B2_2) as [ [BR HBR] | H].
  left. exists (p & Some (a,BL) // Some (a',BR)); constructor; auto.
  fail_with HB. apply H. exists bR; auto.
  fail_with HB. apply H. exists bL; auto.
Qed.

(** ** Relationship with pruning
  We now look into the relationship between [merge] and [more_branches]. *)

Lemma larger_is_merge : forall B1 B2, B1 [>>] B2 -> merge B1 B2 B1.
Proof.
intros.
induction H; try constructor; auto.
all: try opt_elim mBl p0; try opt_elim mBr p0; try constructor; auto.
Qed.

Lemma merge_is_larger : forall B1 B2, merge B1 B2 B1 -> B1 [>>] B2.
Proof.
intros.
induction H; try constructor; auto.
all: apply more_branches_refl.
Qed.

(** Summary of the previous two lemmas. *)

Lemma more_branches_merge : forall B1 B2, B1 [>>] B2 <-> merge B1 B2 B1.
Proof.
split.
+ apply larger_is_merge.
+ apply merge_is_larger.
Qed.

(** Idempotence follows from this characterization. Commutativity is immediate from the definition. *)
Lemma merge_idempotent : forall B, merge B B B.
Proof. intro. apply more_branches_merge, more_branches_refl. Qed.

Lemma merge_comm : forall B1 B2 B, merge B1 B2 B -> merge B2 B1 B.
Proof. intros. induction H; constructor; auto. Qed.

(** We can now prove that [merge] is a partial lub. *)

Lemma merge_is_upper_bound : forall B1 B2 B,
  merge B1 B2 B -> B [>>] B1.
Proof.
intros. induction H; try constructor; auto.
all: apply more_branches_refl.
Qed.

Lemma merge_is_upper_bound' : forall B1 B2 B,
  merge B1 B2 B -> B [>>] B2.
Proof. intros. apply merge_is_upper_bound with B1, merge_comm; auto. Qed.

Local Ltac mb_trans B B' := apply more_branches_trans with B;
  [idtac | apply merge_is_upper_bound with B']; auto.

Local Ltac mb_trans' B B' := apply more_branches_trans with B;
  [idtac | apply merge_is_upper_bound' with B']; auto.

Local Ltac mb_trans'' B B' := apply more_branches_trans with B;
  [apply merge_is_upper_bound with B' | idtac]; auto.

Local Ltac mb_trans''' B B' := apply more_branches_trans with B;
  [apply merge_is_upper_bound' with B' | idtac]; auto.

(** Some kind of colimit. *)

Lemma more_branches_merge_extend : forall B1 B2 B1' B2' B,
  B1 [>>] B1' -> B2 [>>] B2' -> merge B1 B2 B ->
  exists B', merge B1' B2' B' /\ B [>>] B'.
Proof.
intros.
revert dependent B2'. revert dependent B1'.
induction H1; intros; inversion_clear H; inversion_clear H0.
(* simple cases *)
1: exists (End _); split; constructor.
1,2,3: induction (IHmerge _ H2 _ H) as [BB [H' H''] ].
1: exists (p ! e @! a ; BB); split; constructor; auto.
1: exists (p ? x @? a ; BB); split; constructor; auto.
1: exists (p (+) l @+ a ; BB); split; constructor; auto.
83: exists (Call _ X); split; constructor.
82: {
  induction (IHmerge1 _ H1 _ H) as  [BT [HBT' HBT''] ].
  induction (IHmerge2 _ H2 _ H3) as  [BE [HBE' HBE''] ].
  exists (If b Then BT Else BE); repeat split; constructor; auto.
}
(* Trivial mergings *)
all: try (exists (p & None // None);
          split; constructor; fail).
all: try (exists (p & Some (aL,Bl') // None);
          split; constructor; auto; fail).
all: try (exists (p & None // Some (aR,Br'));
          split; constructor; auto; fail).
all: try (exists (p & Some (aL,Bl') // Some (aR,Br'));
          split; constructor; auto; fail).
all: try (induction (IHmerge _ (more_branches_refl _ _) _ H) as [BR [H' H''] ];
   exists (p & None // Some (aR,Br'));
   split; constructor; auto; mb_trans' BR bR1; fail).
all: try (induction (IHmerge _ H2 _ (more_branches_refl _ _)) as [BR [H' H''] ];
   exists (p & None // Some (aR,Br'));
   split; constructor; auto; mb_trans BR bR2; fail).
all: try (induction (IHmerge _ H2 _ H) as [BR [H' H''] ];
   exists (p & None // Some (aR,BR));
   split; constructor; auto; fail).
all: try (induction (IHmerge _ (more_branches_refl _ _) _ H) as [BL [H' H''] ];
   exists (p & Some (aL,Bl') // None);
   split; constructor; auto; mb_trans' BL bL1; fail).
all: try (induction (IHmerge _ H2 _ (more_branches_refl _ _)) as [BL [H' H''] ];
   exists (p & Some (aL,Bl') // None);
   split; constructor; auto; mb_trans BL bL2; fail).
all: try (induction (IHmerge _ H2 _ H) as [BL [H' H''] ];
   exists (p & Some (aL,BL) // None);
   split; constructor; auto; fail).
all: try (induction (IHmerge _ (more_branches_refl _ _) _ H) as [BL [H' H''] ];
   exists (p & Some (aL,Bl') // Some (aR,Br'));
   split; constructor; auto; mb_trans' BL bL1; fail).
all: try (induction (IHmerge _ H2 _ (more_branches_refl _ _)) as [BL [H' H''] ];
   exists (p & Some (aL,Bl') // Some (aR,Br'));
   split; constructor; auto; mb_trans BL bL2; fail).
all: try (induction (IHmerge _ H2 _ H) as [BL [H' H''] ];
  exists (p & Some (aL,BL) // Some (aR,Br'));
  split; constructor; auto; fail).
+ induction (IHmerge _ (more_branches_refl _ _) _ H2) as [BR [H' H''] ];
  exists (p & Some (aL,Bl') // Some (aR,Br'));
  split; constructor; auto; mb_trans' BR bR1.
+ induction (IHmerge _ H2 _ (more_branches_refl _ _)) as [BR [H' H''] ];
  exists (p & Some (aL,Bl') // Some (aR,Br'));
  split; constructor; auto; mb_trans BR bR2.
+ induction (IHmerge _ H2 _ H3) as [BR [H' H''] ];
  exists (p & Some (aL,Bl') // Some (aR,BR));
  split; constructor; auto.
+ induction (IHmerge _ (more_branches_refl _ _) _ H) as [BR [H' H''] ];
  exists (p & Some (aL,Bl') // Some (aR,Br'));
  split; constructor; auto; mb_trans' BR bR1.
+ induction (IHmerge _ H3 _ (more_branches_refl _ _)) as [BR [H' H''] ];
  exists (p & Some (aL,Bl') // Some (aR,Br'));
  split; constructor; auto; mb_trans BR bR2.
+ induction (IHmerge _ H3 _ H) as [BR [H' H''] ];
  exists (p & Some (aL,Bl') // Some (aR,BR));
  split; constructor; auto.
+ induction (IHmerge2 _ (more_branches_refl _ _) _ H) as [BR [H' H''] ];
  exists (p & None // Some (aR,Br'));
  split; constructor; auto; mb_trans' BR bR1.
+ induction (IHmerge1 _ (more_branches_refl _ _) _ H) as [BL [H' H''] ];
  exists (p & Some (aL,Bl') // None);
  split; constructor; auto; mb_trans' BL bL1; auto.
+ induction (IHmerge1 _ (more_branches_refl _ _) _ H) as [BL [Hl' Hl''] ];
  induction (IHmerge2 _ (more_branches_refl _ _) _ H1) as [BR [Hr' Hr''] ];
  exists (p & Some (aL,Bl') // Some (aR,Br'));
  split; constructor; auto.
  mb_trans' BL bL1. mb_trans' BR bR1.
+ induction (IHmerge2 _ H1 _ (more_branches_refl _ _)) as [BR [H' H''] ];
  exists (p & None // Some (aR,Br'));
  split; constructor; auto; mb_trans BR bR2.
+ induction (IHmerge2 _ H1 _ H) as [BR [H' H''] ];
  exists (p & None // Some (aR,BR));
  split; constructor; auto.
+ induction (IHmerge1 _ (more_branches_refl _ _) _ H) as [BL [Hl' Hl''] ];
  induction (IHmerge2 _ H1 _ (more_branches_refl _ _)) as [BR [Hr' Hr''] ];
  exists (p & Some (aL,Bl') // Some (aR,Br'));
  split; constructor; auto. mb_trans' BL bL1. mb_trans BR bR2.
+ induction (IHmerge1 _ (more_branches_refl _ _) _ H) as [BL [Hl' Hl''] ];
  induction (IHmerge2 _ H1 _ H2) as [BR [Hr' Hr''] ];
  exists (p & Some (aL,Bl') // Some (aR,BR));
  split; constructor; auto. mb_trans' BL bL1.
+ induction (IHmerge1 _ H1 _ (more_branches_refl _ _)) as [BL [H' H''] ];
  exists (p & Some (aL,Bl') // None);
  split; constructor; auto; mb_trans BL bL2; auto.
+ induction (IHmerge1 _ H1 _ (more_branches_refl _ _)) as [BL [H' H''] ];
  induction (IHmerge2 _ (more_branches_refl _ _) _ H) as [BR [Hr' Hr''] ];
  exists (p & Some (aL,Bl') // Some (aR,Br'));
  split; constructor; auto. mb_trans BL bL2. mb_trans' BR bR1.
+ induction (IHmerge1 _ H1 _ H) as [BL [H' H''] ];
  exists (p & Some (aL,BL) // None);
  split; constructor; auto.
+ induction (IHmerge1 _ H1 _ H) as [BL [H' H''] ];
  induction (IHmerge2 _ (more_branches_refl _ _) _ H2) as [BR [Hr' Hr''] ];
  exists (p & Some (aL,BL) // Some (aR,Br'));
  split; constructor; auto. mb_trans' BR bR1.
+ induction (IHmerge1 _ H1 _ (more_branches_refl _ _)) as [BL [H' H''] ];
  induction (IHmerge2 _ H2 _ (more_branches_refl _ _)) as [BR [Hr' Hr''] ];
  exists (p & Some (aL,Bl') // Some (aR,Br'));
  split; constructor; auto. mb_trans BL bL2. mb_trans BR bR2.
+ induction (IHmerge1 _ H1 _ (more_branches_refl _ _)) as [BL [H' H''] ];
  induction (IHmerge2 _ H2 _ H) as [BR [Hr' Hr''] ];
  exists (p & Some (aL,Bl') // Some (aR,BR));
  split; constructor; auto. mb_trans BL bL2.
+ induction (IHmerge1 _ H1 _ H) as [BL [H' H''] ];
  induction (IHmerge2 _ H2 _ (more_branches_refl _ _)) as [BR [Hr' Hr''] ];
  exists (p & Some (aL,BL) // Some (aR,Br'));
  split; constructor; auto. mb_trans BR bR2.
+ induction (IHmerge1 _ H1 _ H) as [BL [H' H''] ];
  induction (IHmerge2 _ H2 _ H3) as [BR [Hr' Hr''] ];
  exists (p & Some (aL,BL) // Some (aR,BR));
  split; constructor; auto.
Qed.

(** Merge is an lub *)

Lemma more_branches_has_lub : forall B B1 B2, B [>>] B1 -> B [>>] B2 ->
  exists B', merge B1 B2 B' /\ B [>>] B'.
Proof.
intros.
elim (more_branches_merge_extend B B B1 B2 B); eauto.
apply merge_idempotent.
Qed.

Lemma merge_is_lub : forall B B1 B2, B [>>] B1 -> B [>>] B2 ->
  forall B', merge B1 B2 B' -> B [>>] B'.
Proof.
intros.
elim (more_branches_has_lub B B1 B2); auto.
intros b Hb; destroy Hb.
rewrite (merge_unique _ _ _ _ H1 H2); auto.
Qed.

(** Using these results we can prove associativity of merge. *)

Lemma merge_assoc : forall B1 B2 B3 B12 B23 B,
  merge B1 B2 B12 -> merge B12 B3 B -> merge B2 B3 B23 -> merge B1 B23 B.
Proof.
intros.
induction (more_branches_has_lub B B1 B23) as [B' [HB' HB''] ].
replace B with B'; auto.
apply more_branches_antisym; auto.
- apply merge_is_lub with B12 B3; auto.
  apply merge_is_lub with B1 B2; auto.
  apply merge_is_upper_bound with B23; auto.
  1,2: mb_trans''' B23 B1.
  apply merge_is_upper_bound with B3; auto.
  apply merge_is_upper_bound' with B2; auto.
- mb_trans B12 B2.
  apply merge_is_upper_bound with B3; auto.
- apply merge_is_lub with B2 B3; auto.
  mb_trans'' B12 B3.
  apply merge_is_upper_bound' with B1; auto.
  apply merge_is_upper_bound' with B12; auto.
Qed.

End SP_Merge.

Arguments merge [Sig].
