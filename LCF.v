Require Export Implementation.
Require Export Coq.Program.Equality.

Section test.

Inductive MCTo_T : Configuration -> Configuration -> Set :=
 | TC_Com p e q C s : MCTo_T ( Com p e q; C, s ) ( C, (update s q (evaluate_on_state e s p)) )
 | TC_Sel p q l C s : MCTo_T ( Sel p q l; C, s ) ( C, s )
 | TC_Then p q C1 C2 s : (s p = s q) -> MCTo_T ( If p == q Then C1 Else C2, s ) ( C1, s )
 | TC_Else p q C1 C2 s : (s p <> s q) -> MCTo_T ( If p == q Then C1 Else C2, s ) ( C2, s )
 | TC_Struct C1 C1' C2 C2' s1 s2 : Precongr C1 C1' -> Precongr C2' C2 -> MCTo_T (C1', s1) (C2', s2) -> MCTo_T (C1, s1) (C2, s2)
.

Inductive MCToStar_T : Configuration -> Configuration -> Type :=
 | TToRefl c : MCToStar_T c c
 | TToSingle c1 c2 (P:MCTo_T c1 c2) : MCToStar_T c1 c2
 | TToTran c1 c2 c3 (P1:MCToStar_T c1 c2) (P2:MCToStar_T c2 c3) : MCToStar_T c1 c3
.

Lemma MCTo_strongify : forall c c', MCTo_T c c' -> c ---> c'.
intros.
induction H; auto.
+ apply C_Com.
+ apply C_Sel.
+ apply C_Then; auto.
+ apply C_Else; auto.
+ apply C_Struct with C1' C2'; auto.
Qed.

Lemma MCToStar_strongify : forall c c', MCToStar_T c c' -> c --->* c'.
intros.
induction X; auto.
+ apply ToRefl.
+ apply ToSingle; apply MCTo_strongify; auto.
+ apply ToTran with c2; auto.
Qed.

Fixpoint ToDepth {c c'} (H:MCTo_T c c') : nat :=
  match H with
  | TC_Com _ _ _ _ _ => 0
  | TC_Sel _ _ _ _ _ => 0
  | TC_Then _ _ _ _ _ _ => 0
  | TC_Else _ _ _ _ _ _ => 0
  | TC_Struct _ _ _ _ _ _ _ _ H' => 1 + ToDepth H'
end.

Fixpoint ToStarDepth {c c'} (H:MCToStar_T c c') : nat :=
  match H with
  | TToRefl _ => 0
  | TToSingle _ _ _ => 0
  | TToTran _ _ _ H' H'' => 1 + max (ToStarDepth H') (ToStarDepth H'')
  end.

(** * Induction principles for one-step reduction in MC. *)
Lemma MCTo_ind : forall (P:Choreography -> State -> Choreography -> State -> Prop),
  (forall p e q C s, P (p#e --> q; C) s C (update s q (evaluate_on_state e s p))) ->
  (forall p q l C s, P (Sel p q l; C) s C s) ->
  (forall p q C1 C2 s, s p = s q -> P (If p == q Then C1 Else C2) s C1 s) ->
  (forall p q C1 C2 s, s p <> s q -> P (If p == q Then C1 Else C2) s C2 s) ->
  (forall C1 C1' C2 C2' s1 s2, Precongr C1 C1' -> Precongr C2' C2 -> P C1' s1 C2' s2 -> P C1 s1 C2 s2) ->
  forall C s C' s', (C,s) ---> (C',s') -> P C s C' s'.
intros.
dependent induction H4; auto.
apply H3 with C1' C2'; auto.
Qed.

Lemma MCTo_inv : forall c c', c ---> c' ->
    (exists p e q C s, c = (p#e-->q; C, s) /\ c' = (C,update s q (evaluate_on_state e s p)))
    \/ (exists p q l C s, c = (Sel p q l; C, s) /\ c' = (C,s))
    \/ (exists p q C1 C2 s, c = (If p == q Then C1 Else C2, s) /\ s p = s q /\ c' = (C1,s))
    \/ (exists p q C1 C2 s, c = (If p == q Then C1 Else C2, s) /\ s p <> s q /\ c' = (C2,s))
    \/ (exists C s C' s' C1 C2, c = (C,s) /\ c' = (C',s') /\ Precongr C C1 /\ Precongr C2 C' /\ (C1,s) ---> (C2,s')).
intros; inversion H; auto.
+ left.
  exists p; exists e; exists q; exists C; exists s; split; auto.
+ right; left.
  exists p; exists q; exists l; exists C; exists s; split; auto.
+ right; right; left.
  exists p; exists q; exists C1; exists C2; exists s; split; auto.
+ right; right; right; left.
  exists p; exists q; exists C1; exists C2; exists s; split; auto.
+ repeat right.
  exists C1; exists s1; exists C2; exists s2; exists C1'; exists C2'; auto.
Qed.

Lemma MCToStar_inv : forall c c', c --->* c' -> c = c' \/ c ---> c' \/ exists c'', c --->* c'' /\ c'' --->* c'.
intros; inversion H; auto.
repeat right; exists c2; auto.
Qed.


End test.

Notation "c ===> c'" := (MCTo_T c c') (at level 50, left associativity).
Notation "c ===>* c'" := (MCToStar_T c c') (at level 50, left associativity).

Ltac strongify := first [apply MCTo_strongify | apply MCToStar_strongify].

Section to_be_moved.

Lemma terminated_does_not_reduce : forall C C' s s', Precongr C End -> ~(C,s) ---> (C',s').
intros; intro.
rewrite (not_end_precongr' _ H) in H0; clear H.
dependent induction H0.
assert (C1' = End).
+ clear H1 IHMCTo C2' C' H0 s s'.
  dependent induction H; auto.
+ rewrite H2 in IHMCTo, H1; clear H C1' H2.
  apply IHMCTo with C2' s s'; auto.
Qed.

Lemma terminated_does_not_reduce_conf : forall c c', terminated c -> ~ c ---> c'.
intros.
induction c; induction c'.
rename a into C; rename a0 into C'; rename b into s; rename b0 into s'.
red in H; simpl in H.
apply terminated_does_not_reduce; auto.
Qed.

Fixpoint size (C:Choreography) : nat :=
  match C with
  | End => 0
  | eta; C' => 1 + size C'
  | If p == q Then C1 Else C2 => 1 + min (size C1) (size C2)
  end.

Lemma size_0_End : forall C, size C = 0 -> C = End.
induction C; simpl; auto; intros; inversion H.
Qed.

Lemma precongr_size_ge : forall C C', Precongr C C' -> size C <= size C'.
intros.
induction H; simpl; auto with arith.
+ transitivity (size C2); auto.
+ set (s1 := size C1); set (s2 := size C2); set (s3 := size C3); set (s4 := size C4).
  rewrite Nat.min_assoc.
  rewrite <- (Nat.min_assoc s1 s2 s3).
  rewrite (Nat.min_comm s2 s3).
  repeat rewrite Nat.min_assoc; auto.
+ apply le_n_S.
  apply Nat.min_glb.
  * transitivity (size C1); auto; apply Nat.le_min_l.
  * transitivity (size C3); auto; apply Nat.le_min_r.
Qed.

Lemma MCTo_End_size : forall C s s', (C,s) ---> (End, s') -> size C = 1.
intros.
assert (size C <> 0).
* intro.
  rewrite (size_0_End _ H0) in H.
  apply (terminated_does_not_reduce _ _ _ _ (Refl _) H).
* generalize (eq_refl End).
  generalize H0.
  apply MCTo_ind with (P:=fun C _ C' _ => size C <> 0 -> C' = End -> size C = 1) (s:=s) (C':=End) (s':=s'); simpl; auto; intros.
  + rewrite H2; auto.
  + rewrite H2; auto.
  + rewrite H3; auto.
  + rewrite H3; rewrite Nat.min_comm; auto.
  + rewrite H5 in H2; clear H5.
    generalize (not_end_precongr' _ H2); clear H2; intro.
    generalize (precongr_size_ge _ _ H1); intro.
    rewrite H3 in H5; auto.
    - inversion H5; auto.
      elim H4; auto with arith.
    - intro; apply H4.
      rewrite H6 in H5; auto with arith.
Qed.

Lemma fatsemi_size : forall C C', size C + size C' <= size (C;;C').
induction C; simpl; auto with arith.
intros.
apply le_n_S.
rewrite <- Nat.add_min_distr_r.
apply Nat.min_glb.
+ etransitivity; [apply Nat.le_min_l | apply IHC1].
+ etransitivity; [apply Nat.le_min_r | apply IHC2].
Qed.

End to_be_moved.

Lemma fatsemi_ToEnd : forall C C' s s', (C;;C',s) ---> (End,s') ->
  {C = End /\ (C',s) ---> (End,s')} + {C' = End /\ (C,s) ---> (End,s')}.
double induction C C'; intros; auto;
  try (right; rewrite fatsemi_End in H0; auto).
- exfalso; clear H H0.
  generalize (MCTo_End_size _ _ _ H1); simpl; intros.
  inversion H.
  apply lt_irrefl with 0.
  apply lt_le_trans with 1; auto.
  rewrite <- H2 at 2.
  etransitivity.
  2: apply fatsemi_size.
  replace 1 with (0+1); auto.
  apply plus_le_compat; simpl; auto with arith.
- exfalso; clear H H0.
  generalize (MCTo_End_size _ _ _ H2); simpl; clear H1 H2; intros.
  inversion H.
  apply lt_irrefl with 0.
  apply lt_le_trans with 1; auto.
  rewrite <- H1 at 2.
  etransitivity.
  2: apply fatsemi_size.
  replace 1 with (0+1); auto.
  apply plus_le_compat; simpl; auto with arith.
- right; split; auto.
  rewrite fatsemi_End in H1; auto.
- exfalso; clear H H0.
  generalize (MCTo_End_size _ _ _ H2); simpl; clear H1 H2; intros.
  inversion H.
  apply lt_irrefl with 0.
  apply lt_le_trans with 1; auto.
  rewrite <- H1 at 2.
  apply Nat.min_glb.
  + etransitivity.
    2: apply fatsemi_size.
    replace 1 with (0+1); auto.
    apply plus_le_compat; simpl; auto with arith.
  + etransitivity.
    2: apply fatsemi_size.
    replace 1 with (0+1); auto.
    apply plus_le_compat; simpl; auto with arith.
- exfalso; clear H H0.
  generalize (MCTo_End_size _ _ _ H3); simpl; clear H1 H2 H3; intros.
  inversion H.
  apply lt_irrefl with 0.
  apply lt_le_trans with 1; auto.
  rewrite <- H1 at 2.
  apply Nat.min_glb.
  + etransitivity.
    2: apply fatsemi_size.
    replace 1 with (0+1); auto.
    apply plus_le_compat; simpl; auto with arith.
  + etransitivity.
    2: apply fatsemi_size.
    replace 1 with (0+1); auto.
    apply plus_le_compat; simpl; auto with arith.
Qed.

Lemma Lemma_1_2 : forall C C' s,
  (forall s', ~MCToStar (C,s) (End,s')) -> forall s', ~MCToStar (C;;C',s) (End,s').
intros; intro.
dependent induction H0.
+ apply (H s').
  elim (fatsemi_End_inv _ _ x); intros.
  rewrite H0; apply ToRefl.
+ elim (fatsemi_ToEnd _ _ _ _ P); intros.
  - inversion_clear a; apply (H s).
    rewrite H0; apply ToRefl; auto.
  - inversion_clear b; apply (H s'); apply ToSingle; auto.
+ 
