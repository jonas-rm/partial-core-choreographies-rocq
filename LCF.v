Require Export Implementation.

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

End to_be_moved.

Lemma fatsemi_ToEnd : forall C C' s s', (C;;C',s) ---> (End,s') ->
  {C = End /\ (C',s) ---> (End,s')} + {C' = End /\ (C,s) ---> (End,s')}.
double induction C C'; intros; auto;
  try (right; rewrite fatsemi_End in H0; auto);
  exfalso; clear H H0.
  - elim (MCTo_inv _ _ H1); intros; inversion_clear H.
    * inversion_clear H0; inversion_clear H; inversion_clear H0; inversion_clear H; inversion_clear H0.
      inversion H2.
      rewrite <- H3 in H; clear H4 H3 H2 H1 s' x2.

(* - Precongr preserves length
   - only length 1 reduces to End
*)

  - dependent induction H1.
    * elim (fatsemi_End_inv _ _ x); intros.
      inversion H0.
    * elim (fatsemi_End_inv _ _ x); intros.
      inversion H0.
    * apply IHMCTo with e c e0 c0 s s'.
      2: rewrite (not_end_precongr' _ H0); auto.
      simpl; rewrite H.

Lemma Lemma_1_2 : forall C C' s,
  (forall s', ~MCToStar (C,s) (End,s')) -> forall s', ~MCToStar (C;;C',s) (End,s').
intros; intro.
inversion H0.
+ rewrite <- H4 in H0; clear H4 s'.

(*  elim (fatsemi_End _ _ H3); intros.
  rewrite H2 in H; apply (H _ (ToRefl _)).
+ clear H1 H2 c1 c2.
  induction C; simpl in P; try clear IHC.
  - apply (H _ (ToRefl _)).
  - apply (H s'); apply ToSingle.
    inversion P.
    * elim (fatsemi_End _ _ H5); intros.
      rewrite H1; rewrite H7; apply C_Com.
    * elim (fatsemi_End _ _ H5); intros.
      rewrite H1; rewrite H7; apply C_Sel.
    * clear C1 C2 s1 s2 H1 H2 H3 H4.


  inversion P.
  - rewrite H4 in H2; clear H4 H3 s0 C0.

*)


