Require Export SP.

Section XBehaviour.

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

(** ** Extended behaviours
  To work with partial functions, we first define an extended type of
  behaviours, including undefined subterms.
*)

Inductive XBehaviour : Type :=
| XEnd : XBehaviour
| XSend : Pid -> Expr -> Ann -> XBehaviour -> XBehaviour
| XRecv : Pid -> Var -> Ann -> XBehaviour -> XBehaviour
| XSel : Pid -> Label -> Ann -> XBehaviour -> XBehaviour
| XBranching : Pid -> option (Ann*XBehaviour) -> option (Ann*XBehaviour) -> XBehaviour
| XCond : BExpr -> XBehaviour -> XBehaviour -> XBehaviour
| XCall : RecVar -> XBehaviour
| XUndefined : XBehaviour
.

(** Special lemmas for dealing with undefinedness. *)

Lemma XUndefined_dec : forall B, {B = XUndefined} + {B <> XUndefined}.
Proof. induction B; auto; right; discriminate. Qed.

Lemma Xmatch_elim : forall B T (X1 X2:T), B <> XUndefined ->
  match B with XUndefined => X1 | _ => X2 end = X2.
Proof. induction B; try case o, o0; auto. intros; elim H; auto. Qed.

(** Useful tactics using these two lemmas. *)
Ltac not_XUndef B HB := 
    elim (XUndefined_dec B); intro HB;
    [ rewrite HB; auto | rewrite Xmatch_elim; auto ].

Ltac not_XUndef_with B HB H := 
    elim (XUndefined_dec B); intro HB;
    [ rewrite HB in H | rewrite Xmatch_elim in H; auto ]; inversion H.

(** As before, it helps to have specialized induction principles. *)

Fixpoint Xdepth (B:XBehaviour) : nat :=
match B with
 | XSend p e a B' => 1 + Xdepth B'
 | XRecv p x a B' => 1 + Xdepth B'
 | XSel p l a B' => 1 + Xdepth B'
 | XBranching p mB mB' =>
              1 + (match mB with None => 0 | Some (_,B) => Xdepth B end)
                + (match mB' with None => 0 | Some (_,B) => Xdepth B end)
 | XCond b B1 B2 => 1 + Nat.max (Xdepth B1) (Xdepth B2)
 | XCall X => 1
 | XEnd => 1
 | XUndefined => 0
end.

Theorem XBehaviour_ind' :
  forall P:XBehaviour -> Prop,
    P XEnd ->
    (forall p e a B, P B -> P (XSend p e a B)) ->
    (forall p v a B, P B -> P (XRecv p v a B)) ->
    (forall p l a B, P B -> P (XSel p l a B)) ->
    (forall p, P (XBranching p None None)) ->
    (forall p a Bl, P Bl -> P (XBranching p (Some (a,Bl)) None)) ->
    (forall p a Br, P Br -> P (XBranching p None (Some (a,Br)))) ->
    (forall p a Bl a' Br, P Bl -> P Br -> P (XBranching p (Some (a,Bl)) (Some (a',Br)))) ->
    (forall b B1 B2, P B1 -> P B2 -> P (XCond b B1 B2)) ->
    (forall X, P (XCall X)) ->
    P XUndefined ->
    forall B, P B.
Proof.
intros; revert B.
assert (forall d B, Xdepth B <= d -> P B).
2: eauto.
induction d; intros; case_eq B; intros; auto; rewrite H11 in H10; try (exfalso; inversion H10; fail); auto with arith.
+ induction o; induction o0; try induction a; try induction a0; auto.
  1: apply H6. 3: apply H4. 4: apply H5.
  all: apply IHd.
  all: simpl in H10; apply le_S_n in H10.
  all: etransitivity; [idtac | apply H10]; auto with arith.
+ apply H7; apply IHd; apply le_S_n in H10.
  - etransitivity. eapply Nat.le_max_l. eauto.
  - etransitivity. eapply Nat.le_max_r. eauto.
Qed.

Theorem XBehaviour_rec' :
  forall P:XBehaviour -> Type,
    P XEnd ->
    (forall p e a B, P B -> P (XSend p e a B)) ->
    (forall p v a B, P B -> P (XRecv p v a B)) ->
    (forall p l a B, P B -> P (XSel p l a B)) ->
    (forall p, P (XBranching p None None)) ->
    (forall p a Bl, P Bl -> P (XBranching p (Some (a,Bl)) None)) ->
    (forall p a Br, P Br -> P (XBranching p None (Some (a,Br)))) ->
    (forall p a Bl a' Br, P Bl -> P Br -> P (XBranching p (Some (a,Bl)) (Some (a',Br)))) ->
    (forall b B1 B2, P B1 -> P B2 -> P (XCond b B1 B2)) ->
    (forall X, P (XCall X)) ->
    P XUndefined ->
    forall B, P B.
Proof.
intros; revert B.
assert (forall d B, Xdepth B <= d -> P B).
2: eauto.
induction d; intros; case_eq B; intros; auto; rewrite H0 in H; try (exfalso; inversion H; fail); auto with arith.
+ induction o; induction o0; try induction a; try induction a0; auto.
  1: apply X6. 3: apply X4. 4: apply X5.
  all: apply IHd.
  all: simpl in H; apply le_S_n in H.
  all: etransitivity; [idtac | apply H]; auto with arith.
+ apply X7; apply IHd; apply le_S_n in H.
  - etransitivity. eapply Nat.le_max_l. eauto.
  - etransitivity. eapply Nat.le_max_r. eauto.
Qed.

(** Weird lemma for case analysis. *)
Lemma XB_match : forall (T:Type) B (t:T),
  match B with XUndefined => t | _ => t end = t.
Proof. intros. case B; auto. Qed.

Open Scope SP_scope.

(** ** Injection
  Every behaviour can be injected in the extended type in the obvious way.
*)

Fixpoint inject (B:Behaviour Sig) : XBehaviour :=
match B with
| End _                           => XEnd
| p ! e @! a; B                   => XSend p e a (inject B)
| p ? v @? a; B                   => XRecv p v a (inject B)
| p (+) l @+ a; B                 => XSel p l a (inject B)
| p & None // None                => XBranching p None None
| p & Some (a,Bl) // None         => XBranching p (Some (a,inject Bl)) None
| p & None // Some (a,Br)         => XBranching p None (Some (a,inject Br))
| p & Some (a,Bl) // Some (a',Br) => XBranching p (Some (a,inject Bl)) (Some (a',inject Br))
| If e Then B1 Else B2            => XCond e (inject B1) (inject B2)
| Call _ X                        => XCall X
end.

(** This injection is an injection (!) mapping into not-undefined extended behaviours. *)

Lemma inject_not_undefined : forall B, inject B <> XUndefined.
Proof. induction B; try case o, o0; try case p; try case p0; discriminate. Qed.

Lemma inject_elim : forall B, exists B', inject B = B' /\ B' <> XUndefined.
Proof.
intro; exists (inject B); split; auto.
apply inject_not_undefined.
Qed.

Lemma inject_match : forall B T (X1 X2:T),
  match inject B with XUndefined => X1 | _ => X2 end = X2.
Proof. induction B; try case o, o0; try case p; try case p0; auto. Qed.

Lemma inject_inj : forall B B', inject B = inject B' -> B = B'.
Proof.
BDInduction B B'; intros; auto; try inversion H;
  try rewrite (IHB _ H4); auto.
+ rewrite (IHB _ H3); auto.
+ rewrite (IHB _ H3); auto.
+ rewrite (IHB1 _ H3), (IHB2 _ H5); auto.
+ rewrite (IHB1 _ H2), (IHB2 _ H3); auto.
Qed.

(** ** Collapse
  This function collapses every extended behaviour containing [XUndefined]
  to [XUndefined], effectively mapping [XBehaviour] into [option Behaviour]. *)

Fixpoint collapse (B:XBehaviour) : XBehaviour :=
let rec := fun B' => match collapse B' with XUndefined => XUndefined | _ => B end in
match B with
| XSend p e a B' => rec B'
| XRecv p x a B' => rec B'
| XSel p l a B'  => rec B'
| XBranching p mB mB' => match mB, mB' with
                         | None,    None            => B
                         | Some (a,Bl), None        => rec Bl
                         | None,    Some (a,Br)     => rec Br
                         | Some (_,Bl), Some (_,Br) => match collapse Bl, collapse Br with
                                               | XUndefined, _ => XUndefined
                                               | _, XUndefined => XUndefined
                                               | _, _          => B
                                               end
                         end
| XCond b B1 B2 => match collapse B1, collapse B2 with
                   | XUndefined, _ => XUndefined
                   | _, XUndefined => XUndefined
                   | _, _          => B
                   end
| _ => B
end.

(** Relationship with inject. *)
Lemma collapse_inject : forall B, collapse (inject B) = inject B.
Proof.
BInduction B; simpl; auto.
1,2,3,4,5: rewrite IHB, inject_match; auto.
1,2: rewrite IHB1, IHB2, inject_match, inject_match; auto.
Qed.

Lemma inject_exists : forall B,
  {B' | B = inject B'} -> collapse B <> XUndefined.
Proof.
intros. inversion_clear X.
rewrite H, collapse_inject; apply inject_not_undefined.
Qed.

(** Elimination lemmas. *)
Lemma collapse_char : forall B,
  {collapse B = XUndefined} + {collapse B = B}.
Proof.
induction B using XBehaviour_rec'; simpl; auto.
1,2,3,4,5: elim IHB; intro H; rewrite H; auto; not_XUndef B HB.
1,2: elim IHB1; intro H1; rewrite H1; auto; not_XUndef B1 HB1.
1,2: elim IHB2; intro H2; rewrite H2; auto; not_XUndef B2 HB2.
Qed.

Lemma collapse_char' : forall B,
  ({B' | B = inject B'}) + {collapse B = XUndefined}.
Proof.
induction B using XBehaviour_rec'; simpl; auto.
+ left; exists (End _); auto.
+ elim IHB; intro H; try rewrite H; auto.
  left; elim H; clear H; intros B' HB'; rewrite HB'.
  exists (p ! e @! a ; B'); simpl; auto.
+ elim IHB; intro H; try rewrite H; auto.
  left; elim H; clear H; intros B' HB'; rewrite HB'.
  exists (p ? v @? a; B'); simpl; auto.
+ elim IHB; intro H; try rewrite H; auto.
  left; elim H; clear H; intros B' HB'; rewrite HB'.
  exists (p (+) l @+a ; B'); simpl; auto.
+ left. exists (p & None // None); auto.
+ elim IHB; intro H; try rewrite H; auto.
  left; elim H; clear H; intros B' HB'; rewrite HB'.
  exists (p & Some (a,B') // None); auto.
+ elim IHB; intro H; try rewrite H; auto.
  left; elim H; clear H; intros B' HB'; rewrite HB'.
  exists (p & None // Some (a,B')); auto.
+ elim IHB1; intro H1; try rewrite H1; auto.
  rewrite Xmatch_elim. 2: apply inject_exists; auto.
  elim IHB2; intro H2; try rewrite H2; auto.
  rewrite Xmatch_elim. 2: apply inject_exists; auto.
  left; inversion H1 as (B'1,H'1); inversion H2 as (B'2,H'2).
  exists (p & Some (a,B'1) // Some (a',B'2)). rewrite H'1, H'2; auto.
+ elim IHB1; intro H1; try rewrite H1; auto.
  rewrite Xmatch_elim. 2: apply inject_exists; auto.
  elim IHB2; intro H2; try rewrite H2; auto.
  rewrite Xmatch_elim. 2: apply inject_exists; auto.
  left; inversion H1 as (B'1,H'1); inversion H2 as (B'2,H'2).
  exists (If b Then B'1 Else B'2); rewrite H'1, H'2; auto.
+ left; exists (Call _ X); auto.
Qed.

Lemma collapse_char'' : forall B, collapse B = XUndefined ->
  forall B', B <> inject B'.
Proof.
induction B using XBehaviour_ind'; induction B' using Behaviour_ind'.
all: try inversion H.
all: try discriminate.
1,2,3,4,5: not_XUndef_with (collapse B) HB H1.
1,2,3,4,5: intro; inversion H0; apply IHB with B'; auto.
1,2: not_XUndef_with (collapse B1) HB1 H1.
1,3: intro; inversion H0; apply IHB1 with B'1; auto.
1,2: not_XUndef_with (collapse B2) HB2 H2.
1,2: intro; inversion H0; apply IHB2 with B'2; auto.
Qed.

Lemma collapse_exists : forall B, collapse B <> XUndefined ->
  exists B', B = inject B'.
Proof.
intros; elim (collapse_char' B); intros.
inversion_clear a; eauto.
elim H; auto.
Qed.

Lemma collapse_inv : forall B B', collapse B = inject B' -> B = inject B'.
Proof.
induction B using XBehaviour_ind'; auto; simpl; intros.
1,2,3,4,5: not_XUndef_with (collapse B) HB H;
           elim (inject_not_undefined _ (eq_sym H)).
1,2: not_XUndef_with (collapse B1) HB1 H.
1,3: elim (inject_not_undefined _ (eq_sym H)).
1,2: not_XUndef_with (collapse B2) HB2 H.
1,3: elim (inject_not_undefined _ (eq_sym H2)).
1,2: rewrite Xmatch_elim; auto.
Qed.

End XBehaviour.

(** Tactics for induction proofs. *)
Ltac XBInduction B := induction B using XBehaviour_ind'.
Ltac XBDInduction B B' := induction B using XBehaviour_ind'; induction B' using XBehaviour_ind'.

Ltac not_XUndef B HB := 
    elim (XUndefined_dec _ B); intro HB;
    [ rewrite HB; auto | rewrite Xmatch_elim; auto ].

Ltac not_XUndef_with B HB H := 
    elim (XUndefined_dec _ B); intro HB;
    [ rewrite HB in H | rewrite Xmatch_elim in H; auto ]; inversion H.

Ltac opt_elim b p := case_eq b; repeat induction p.

Arguments XEnd {Sig}.
Arguments XSend [Sig].
Arguments XRecv [Sig].
Arguments XSel [Sig].
Arguments XBranching [Sig].
Arguments XCond [Sig].
Arguments XCall [Sig].
Arguments XUndefined {Sig}.

Arguments inject [Sig].
Arguments collapse [Sig].
