Require Export MC.
Require Export SP.

Local Open Scope nat_scope.

Module EPPBase (P X V E B R:DecType) (Ev:Eval E X V V) (BEv:Eval B X V Bool).

Module PR := DecProd R P.

Module Import MCBase := MCBase P X V E B R Ev BEv.
Module Import SP_EPP := SPBase P X V E B PR Ev BEv.

(*
Section Tactics.

Ltac Pid_dec_rewrite p q Hpq :=
  try rewrite Pdec.eqb_refl;
  case_eq (Pid_dec p q); [
    auto; rewrite (Pdec.eqb_eq p q); intro Hpq; try rewrite Hpq; auto
    |
    auto; rewrite (Pdec.eqb_neq p q); intro Hpq; try rewrite Hpq; auto
  ].

Ltac NotIn_from_neq_1 H :=
  simpl; intro H; inversion H; auto.

Ltac assert_NotIn_from_neq_1 x y H :=
  assert (~ In x (y :: nil)); [NotIn_from_neq_1 H | ].

Ltac NotIn_from_neq_2 x y z H H' :=
  simpl; intro H; inversion H as [H' | H']; inversion H'; auto.

Ltac assert_NotIn_from_neq_2 x y z H H' :=
  assert (~ In x (y :: z :: nil)); [NotIn_from_neq_2 x y z H H' | ].

End Tactics.
*)

Section EPP.

(** First step: returns an XBehaviour, possibly with XUndefined subcomponents. *)
Fixpoint bproj (Defs:DefSet) (C:Choreography) (r:Pid) : XBehaviour :=
match C with
| MCBase.End                => XEnd
| p#e --> q$x;; C'          => if Pid_dec p r
                               then XSend q e (bproj Defs C' r)
                               else if Pid_dec q r
                                    then XRecv p x (bproj Defs C' r)
                                    else bproj Defs C' r
| p --> q[left];; C'        => if Pid_dec p r
                               then XSel q left (bproj Defs C' r)
                               else if Pid_dec q r
                                    then XBranching p (Some (bproj Defs C' r)) None
                                    else bproj Defs C' r
| p --> q[right];; C'       => if Pid_dec p r
                               then XSel q right (bproj Defs C' r)
                               else if Pid_dec q r
                                    then XBranching p None (Some (bproj Defs C' r))
                                    else bproj Defs C' r
| If p ?? b Then C1 Else C2 => if Pid_dec p r
                               then XCond b (bproj Defs C1 r) (bproj Defs C2 r)
                               else Xmerge (bproj Defs C1 r) (bproj Defs C2 r)
| MCBase.Call X             => if In_dec P.eq_dec r (fst (Defs X))
                               then XCall (X,r)
                               else XEnd
| RT_Call X ps C'           => if In_dec P.eq_dec r ps
                               then XCall (X,r)
                               else bproj Defs C' r
end.

(** Second step: collapse all undefined behaviours. *)
Definition epp_list (Defs:DefSet) (C:Choreography) (ps:list Pid) : list (Pid * XBehaviour) :=
  map (fun p => (p, collapse (bproj Defs C p))) ps.

(** Definitions of projectability at all different levels. *)
Definition projectable_C Defs ps C :=
  Forall (fun X => snd X <> XUndefined) (epp_list Defs C ps).

Definition projectable_D Xs Defs :=
  Forall (fun X => projectable_C Defs (fst (Defs X)) (snd (Defs X)) ) Xs.

Definition projectable Xs ps P :=
  projectable_C (Procedures P) ps (Main P) /\
  projectable_D Xs (Procedures P) /\
  (forall p, In p (MCC_pn (Main P) (fun _ => nil)) -> In p ps) /\
  (forall p X, In X Xs -> In p (fst (Procedures P X)) -> In p ps) /\
  (forall p X, In X Xs -> In p (MCC_pn (snd (Procedures P X)) (fun _ => nil)) -> In p ps).

(** Not decidable, but in practice easy to compute. *)
Definition Projectable P := exists Xs ps,
  projectable Xs ps P /\ Program_WF Xs P.

(** Now we can define EPP, again in a layered manner.
  Definitions are interactive because of the absurd cases. *)
Definition epp_C Defs ps C : projectable_C Defs ps C -> Network.
Proof.
intros; intro p.
elim (In_dec P.eq_dec p ps); intro Hp.
2: apply End.
elim (collapse_char' (bproj Defs C p)); intro.
1: inversion_clear a. apply x.
exfalso.
red in H. rewrite Forall_forall in H.
apply (H (p,collapse (bproj Defs C p))); auto.
unfold epp_list.
apply in_map_iff. exists p; auto.
Defined.

Definition epp_D Xs Defs : projectable_D Xs Defs -> DefSetB.
Proof.
intros; intro.
case_eq X; intros R p HX.
elim (In_dec R.eq_dec R Xs).
2: intros; apply End.
elim (In_dec P.eq_dec p (fst (Defs R))).
2: intros; apply End.
elim (collapse_char' (bproj Defs (snd (Defs R)) p)); intros.
induction a. apply x.
exfalso.
red in H. rewrite Forall_forall in H.
generalize (H _ a0); clear H; intro.
red in H. rewrite Forall_forall in H.
apply (H (p, collapse (bproj Defs (snd (Defs R)) p))); auto.
apply in_map_iff. exists p; auto.
Defined.

Definition epp Xs ps P : projectable Xs ps P -> Program.
Proof.
intro H; inversion_clear H. inversion_clear H1.
constructor.
apply (epp_D _ _ H).
apply (epp_C _ _ _ H0).
Defined.

(** Proof irrelevance for EPP. *)
Lemma epp_C_wd : forall Defs C ps H H',
  Network_eq (epp_C Defs ps C H) (epp_C Defs ps C H').
Proof.
intros; intro. unfold epp_C.
elim In_dec; auto.
intros. elim collapse_char'; auto.
intros. exfalso.
red in H. rewrite Forall_forall in H.
apply (H (p, collapse (bproj Defs C p))); auto.
apply in_map_iff. exists p; auto.
Qed.

Lemma epp_D_wd : forall Xs Defs H H' X, epp_D Xs Defs H X = epp_D Xs Defs H' X.
Proof.
intros; unfold epp_D.
induction X as (R,p).
elim In_dec; auto.
intros. elim In_dec; auto.
intros. elim collapse_char'; auto.
intros. exfalso.
red in H. rewrite Forall_forall in H.
generalize (H _ a0); clear H; intro.
red in H. rewrite Forall_forall in H.
apply (H (p, collapse (bproj Defs (snd (Defs R)) p))); auto.
apply in_map_iff. exists p; auto.
Qed.

Lemma epp_C_char : forall Xs ps Defs C HP HC,
  Network_eq (Net (epp Xs ps {| Procedures := Defs; Main := C |} HP))
  (epp_C Defs ps C HC).
Proof.
intros.
unfold epp.
case HP; intros. case a; intros.
apply epp_C_wd.
Qed.

Lemma epp_D_char : forall Xs ps Defs C HP HD X p,
  Procs (epp Xs ps {| Procedures := Defs; Main := C |} HP) (X,p)
  = epp_D Xs Defs HD (X,p).
Proof.
intros.
unfold epp.
case HP; intros. case a; intros.
apply epp_D_wd.
Qed.

End EPP.

Section Projectability.

(** ** Properties of projectability
  All variants of parameterized projectability are decidable. *)

Lemma projectable_C_dec : forall Defs ps C,
  { projectable_C Defs ps C } + { ~projectable_C Defs ps C }.
Proof.
intros. apply Forall_dec; intro.
induction x as (p,B).
simpl. elim (XUndefined_dec B); auto.
Qed.

Lemma projectable_D_dec : forall Xs Defs,
  { projectable_D Xs Defs } + { ~projectable_D Xs Defs }.
Proof.
intros. apply Forall_dec; intro.
apply projectable_C_dec.
Qed.

Lemma projectable_dec : forall Xs ps P,
  { projectable Xs ps P } + { ~projectable Xs ps P }.
Proof.
intros.
elim (projectable_C_dec (Procedures P) ps (Main P)); intro HC.
2: right; intro; inversion_clear H; auto.
elim (projectable_D_dec Xs (Procedures P)); intro HD.
2: right; intro; destroy H; auto.
generalize (fun p => In_dec P.eq_dec p ps); intro.
elim (Forall_dec (fun p => In p ps)) with (MCC_pn (Main P) (fun _ => nil)); auto; intro Hps.
1: elim (Forall_dec (fun X => forall p, In p (MCC_pn (snd (Procedures P X)) (fun _ => nil)) -> In p ps)) with Xs; intro HXs1.
1: elim (Forall_dec (fun X => forall p, In p (fst (Procedures P X)) -> In p ps)) with Xs; intro HXs2.
+ left. rewrite Forall_forall in Hps, HXs1, HXs2.
  repeat split; eauto.
+ right; intro; apply HXs2.
  destroy H. rewrite Forall_forall; eauto.
+ elim (Forall_dec (fun p => In p ps)) with (fst (Procedures P HXs2)); auto.
  - left; rewrite Forall_forall in a; auto.
  - right; intro. apply b; rewrite Forall_forall; auto.
+ right; intro; apply HXs1.
  destroy H. rewrite Forall_forall; eauto.
+ elim (Forall_dec (fun p => In p ps)) with (MCC_pn (snd (Procedures P HXs1)) (fun _ => nil)); auto.
  - left. rewrite Forall_forall in a; eauto.
  - right; intro. apply b; rewrite Forall_forall; eauto.
+ right; intro; apply Hps.
  destroy H. rewrite Forall_forall; eauto.
Qed.

(** Inversion lemmas for projectability. *)
Lemma projectable_inv_Com : forall Defs ps p e q x C,
  projectable_C Defs ps (p#e --> q$x;; C) -> projectable_C Defs ps C.
Proof.
intros. red; red in H.
rewrite Forall_forall; rewrite Forall_forall in H.
intros. induction x0 as (r,B). intro.
apply (H (r,XUndefined)); auto.
unfold epp_list in H0; rewrite in_map_iff in H0.
unfold epp_list; rewrite in_map_iff.
destroy H0. inversion H2.
rewrite H4 in H0. simpl in H1. clear x0 H4 H2.
exists r; simpl. split; auto.
case Pid_dec; [idtac | case Pid_dec]; simpl; rewrite H5, H1; auto.
Qed.

Lemma projectable_inv_Sel : forall Defs ps p q l C,
  projectable_C Defs ps (p --> q[l];; C) -> projectable_C Defs ps C.
Proof.
intros. red; red in H.
rewrite Forall_forall; rewrite Forall_forall in H.
intros. induction x as (r,B). intro.
apply (H (r,XUndefined)); auto.
unfold epp_list in H0; rewrite in_map_iff in H0.
unfold epp_list; rewrite in_map_iff.
destroy H0. inversion H2.
rewrite H4 in H0. simpl in H1. clear x H4 H2.
exists r; simpl. split; auto.
case l; (case Pid_dec; [idtac | case Pid_dec]); simpl; rewrite H5, H1; auto.
Qed.

Lemma projectable_inv_Cond : forall Defs ps p b C1 C2,
  projectable_C Defs ps (If p ?? b Then C1 Else C2) -> projectable_C Defs ps C1.
Proof.
intros. red; red in H.
rewrite Forall_forall; rewrite Forall_forall in H.
intros. induction x as (r,B). intro.
apply (H (r,XUndefined)); auto.
unfold epp_list in H0; rewrite in_map_iff in H0.
unfold epp_list; rewrite in_map_iff.
destroy H0. inversion H2.
rewrite H4 in H0. simpl in H1. clear x H4 H2.
exists r; simpl. split; auto.
case Pid_dec; simpl.
+ rewrite H5, H1; auto.
+ rewrite collapse_merge; auto. rewrite H5; auto.
Qed.

Lemma projectable_inv_Cond' : forall Defs ps p b C1 C2,
  projectable_C Defs ps (If p ?? b Then C1 Else C2) -> projectable_C Defs ps C2.
Proof.
intros. red; red in H.
rewrite Forall_forall; rewrite Forall_forall in H.
intros. induction x as (r,B). intro.
apply (H (r,XUndefined)); auto.
unfold epp_list in H0; rewrite in_map_iff in H0.
unfold epp_list; rewrite in_map_iff.
destroy H0. inversion H2.
rewrite H4 in H0. simpl in H1. clear x H4 H2.
exists r; simpl. split; auto.
case Pid_dec; simpl.
+ rewrite H5, H1. case (collapse (bproj Defs C1 r)); auto.
+ rewrite collapse_merge'; auto. rewrite H5; auto.
Qed.

(** The corresponding lemmas for RT_Call do not hold.
  Therefore, projectability is not preserved by reductions,
  so we need an auxiliary notion. *)
Fixpoint strongly_projectable Defs (C:Choreography) (r:Pid) : Prop :=
match C with
| eta;; C'                  => strongly_projectable Defs C' r
| If p ?? b Then C1 Else C2 => strongly_projectable Defs C1 r
                               /\ strongly_projectable Defs C2 r
                               /\ collapse (bproj Defs C r) <> XUndefined
| RT_Call X ps C            => strongly_projectable Defs C r
| _                         => True
end.

Lemma strongly_projectable_C : forall Defs C r,
  strongly_projectable Defs C r -> collapse (bproj Defs C r) <> XUndefined.
Proof.
induction C; simpl.
+ discriminate.
+ intro; elim in_dec; discriminate.
+ intro; elim in_dec; auto. discriminate.
+ intro; induction e; elim Pid_dec;
  [idtac | elim Pid_dec | elim l | elim l; elim Pid_dec];
    auto; simpl; intros; try (rewrite Xmatch_elim; auto; discriminate).
+ intro; elim Pid_dec; tauto.
Qed.

Lemma strongly_projectable_C' : forall Defs C ps,
  (forall r, In r ps -> strongly_projectable Defs C r) -> projectable_C Defs ps C.
Proof.
intros; red; rewrite Forall_forall.
induction x as (p,B); simpl; intros.
apply in_map_iff in H0; destroy H0. inversion H1.
rewrite H3 in H0; clear H3 H1 x.
apply strongly_projectable_C, H. auto.
Qed.

Lemma initial_strongly_projectable : forall C, initial C ->
  forall Defs ps, projectable_C Defs ps C ->
  forall r, In r ps -> strongly_projectable Defs C r.
Proof.
induction C; auto; simpl; intros.
+ inversion H.
+ induction e.
  - apply projectable_inv_Com in H0; eauto.
  - apply projectable_inv_Sel in H0; eauto.
+ inversion_clear H. repeat split.
  - apply projectable_inv_Cond in H0; eauto.
  - apply projectable_inv_Cond' in H0; eauto.
  - red in H0. rewrite Forall_forall in H0.
    generalize (H0 (r,collapse (bproj Defs (If p ?? b Then C1 Else C2) r))); intros.
    simpl in H; apply H.
    apply in_map_iff. exists r; auto.
Qed.

(** Strong projectability of well-formed programs is preserved by reductions. *)
Lemma strongly_projectable_reduces : forall P Xs ps,
  Program_WF Xs P -> projectable Xs ps P ->
  forall s tl P' s', ((P,s) --[tl]--> (P',s'))%MC -> projectable Xs ps P'.
Proof.
intros.
induction P as (Defs,C). induction P' as (Defs', C').
generalize (MCP_To_Defs_stable Defs Defs' C C' tl s s' H1); intro.
rewrite <- H2 in H1; rewrite <- H2; clear Defs' H2.
inversion H1. rewrite <- H3 in H1. clear s'0 H8 C'0 H7 tl H3 s0 H5 C0 H4 Defs0 H2.
rename H6 into Ht.
destroy H0; intros. repeat split; auto.
2: {
  (* generalize (MCC_To_within_Xs _ _ _ _ _ _ H' H1); intros. *)
  clear H1.
  (* set (H':=H). clearbody H'. *)
  red in H; unfold MCBase.Procs, Vars in H; simpl in H.
  destroy H. clear H1 H6. set (H1 := True). set (H6 := True).
  intros. induction Ht.
  1,2,3,4: apply H4; simpl;
    unfold set_union_pid; repeat rewrite set_union_iff; auto.
  - elim (set_union_elim _ _ _ _ H7); intro.
    1: apply H4, set_union_iff; auto.
    apply IHHt; auto.
    * induction eta.
      eapply projectable_inv_Com; eauto.
      eapply projectable_inv_Sel; eauto.
    * intros. apply H4; simpl.
      unfold set_union_pid; repeat rewrite set_union_iff; auto.
    (* * apply Choreography_WF_eta with eta; auto. *)
  - elim (set_union_elim _ _ _ _ H7); intro.
    1: elim (set_union_elim _ _ _ _ a); intro.
    1: apply H4, set_union_iff; left. apply set_union_iff; auto.
    2: apply IHHt2; auto. 1: apply IHHt1; auto.
    * eapply projectable_inv_Cond; eauto.
    * intros. apply H4; simpl.
      unfold set_union_pid; repeat rewrite set_union_iff; auto.
    * eapply projectable_inv_Cond'; eauto.
    * intros. apply H4; simpl.
      unfold set_union_pid; repeat rewrite set_union_iff; auto.
  - elim (set_union_elim _ _ _ _ H7); intro.
    1: apply H4, set_union_iff; auto.
    apply IHHt; auto.
    simpl in H2.



    auto.
 Search In set_union. apply set_union.

  - rewrite <- H16 in H9; simpl in H9.
    apply H0 with r; auto.
  - rewrite <- H16 in H9; simpl in H9.
    elim (set_union_elim _ _ _ _ H9); eauto.
    intro; apply H5 with r; auto; simpl.
    apply set_remove'_1 with P.eq_dec p0; auto.
  - apply IHC; auto. 

inversion H1; clear H1.
rename H into HP, H2 into HC, H0 into HD, H7 into Ht.
destroy HP. unfold MCBase.Procs, Vars in HP.
simpl in H0, HC, HD, HP. rename H0 into HC'.
revert C HC HC' C' s s' t Ht.
induction C; intros; inversion Ht;
  clear dependent s0; clear dependent s'0.
+ red in HD. rewrite Forall_forall in HD.
  simpl. 

simpl in HC'.
projectable_C Defs (fst (Defs X)) (snd (Defs X)) -> projectable_C Defs ps (snd (Defs X))

(* Start of proof for old version.
induction H0.
+ intro; apply (H (p,XUndefined)); auto.
  unfold epp_list in H1; rewrite in_map_iff in H1.
  unfold epp_list; rewrite in_map_iff.
  destroy H1. inversion H3.
  rewrite H5 in H1. simpl in H2. clear x0 H5 H3.
  exists p; simpl. split; auto.
  case Pid_dec; [idtac | case Pid_dec]; simpl; rewrite H6, H2; auto.
+ intro; apply (H (p,XUndefined)); auto.
  unfold epp_list in H1; rewrite in_map_iff in H1.
  unfold epp_list; rewrite in_map_iff.
  destroy H1. inversion H3.
  rewrite H5 in H1. simpl in H2.
  exists p; simpl. split; auto.
  case l; (case Pid_dec; [idtac | case Pid_dec]); simpl; rewrite H6, H2; auto.
+ intro; apply (H (p,XUndefined)); auto.
  unfold epp_list in H1; rewrite in_map_iff in H1.
  unfold epp_list; rewrite in_map_iff.
  destroy H1. inversion H4.
  rewrite H6 in H1. simpl in H3.
  exists p; simpl. split; auto.
  case Pid_dec; simpl. rewrite H7, H3; auto.
  rewrite H3 in H7. rewrite (collapse_merge _ _ H7); auto.
+ intro; apply (H (p,XUndefined)); auto.
  unfold epp_list in H1; rewrite in_map_iff in H1.
  unfold epp_list; rewrite in_map_iff.
  destroy H1. inversion H4.
  rewrite H6 in H1. simpl in H3.
  exists p; simpl. split; auto.
  case Pid_dec; simpl. rewrite H7, H3; auto.
  case (collapse (bproj Defs C1 p)); auto.
  rewrite H3 in H7. rewrite (collapse_merge' _ _ H7); auto.
+ rename p into p'; rename B into B'.
  unfold epp_list in H1; rewrite in_map_iff in H1.  
  destroy H1.
  assert (x = p' /\ collapse (bproj Defs (eta;;C') x) = B').
  1: inversion H3; auto.
  inversion_clear H4. rewrite H5 in H6, H1. clear H5 x H3.
  simpl. rewrite <- H6; clear H6.
  assert (collapse (bproj Defs C' p') <> XUndefined).
  - change (snd (p',collapse (bproj Defs C' p')) <> XUndefined).
    apply IHMCC_To; auto.

  - case eta; intros; simpl;
    case Pid_dec; [idtac | case Pid_dec | case l | case l; case Pid_dec ];
    simpl; try rewrite Xmatch_elim; auto; discriminate.
  - apply IHMCC_To.
    intros; induction x as (p, B).
    simpl; intro.
  - apply (H (p',collapse (bproj Defs (eta;;C) p'))); auto.
    unfold epp_list in H3; rewrite in_map_iff in H3.
    unfold epp_list; rewrite in_map_iff.
    destroy H3. inversion H5.
    rewrite H7 in H3.
    exists p'; split; auto.
    assert (collapse (bproj Defs C p') = XUndefined).
    2: simpl; case eta; (intros; case Pid_dec; [idtac | case Pid_dec]; try case l; simpl); rewrite H5; auto.
    rewrite H7, H2; auto

*)

(* *)
[idtac | case Pid_dec]; simpl; rewrite H7, H3; auto.
+ 

  clear p0 e0 x0 H3 H5 H v H0; simpl in H2.
  exists p; simpl. split; auto.
  unfold Pid_dec; rewrite Pdec.eqb_refl.
  simpl. rewrite H6, H2; auto.
  - unfold epp_list in H1; rewrite in_map_iff in H1.
    unfold epp_list; rewrite in_map_iff.
    destroy H1. inversion H3.
    rewrite H5 in H1; rewrite <- e0.
    clear p0 e0 x0 H3 H5 H v H0; simpl in H2.
    exists p; simpl. split; auto.
    unfold Pid_dec; rewrite Pdec.eqb_refl.
    simpl. rewrite H6, H2; auto.
*)
Abort.


End Projectability.

Section MoreBranches.

Inductive more_branches : Behaviour -> Behaviour -> Prop :=
| MB_End : more_branches End End
| MB_Send p e B B': more_branches B B' -> more_branches (p ! e; B) (p ! e; B')
| MB_Recv p x B B': more_branches B B' -> more_branches (p ? x; B) (p ? x; B')
| MB_Sel p l B B': more_branches B B' -> more_branches (p (+) l; B) (p (+) l; B')
| MB_Branching_None_None p mBl mBr : more_branches (p & mBl // mBr) (p & None // None)
| MB_Branching_None_Some p mBl Br Br' : more_branches Br Br' ->
    more_branches (p & mBl // Some Br) (p & None // Some Br')
| MB_Branching_Some_None p Bl Bl' mBr : more_branches Bl Bl' ->
    more_branches (p & Some Bl // mBr) (p & Some Bl' // None)
| MB_Branching_Some_Some p Bl Bl' Br Br' : more_branches Bl Bl' -> more_branches Br Br' ->
    more_branches (p & Some Bl // Some Br) (p & Some Bl' // Some Br')
| MB_Cond b B1 B1' B2 B2' : more_branches B1 B1' -> more_branches B2 B2' ->
    more_branches (If b Then B1 Else B2) (If b Then B1' Else B2')
| MB_Call X : more_branches (Call X) (Call X)
.

Lemma more_branches_char_1 : forall B1 B2,
  more_branches B1 B2 -> merge B1 B2 = inject B1.
Proof.
unfold merge; intros.
induction H; simpl; auto;
  try case mBl; try case mBr; simpl; intros;
  try rewrite Pdec.eqb_refl;
  try rewrite Edec.eqb_refl;
  try rewrite Vdec.eqb_refl;
  try rewrite Xdec.eqb_refl;
  try rewrite label_eqb_refl;
  try rewrite Bdec.eqb_refl;
  try rewrite Rdec.eqb_refl;
  try rewrite IHmore_branches;
  repeat rewrite inject_match;
  simpl; auto.
+ rewrite IHmore_branches1, IHmore_branches2, inject_match, inject_match. auto.
+ rewrite IHmore_branches1, IHmore_branches2.
  case_eq (inject B1); case_eq (inject B2); simpl; auto; intros;
    try elim (inject_not_undefined _ H1);
    elim (inject_not_undefined _ H2).
Qed.

Lemma more_branches_char_2 : forall B1 B2,
  merge B1 B2 = inject B1 -> more_branches B1 B2.
Proof.
unfold merge.
induction B1 using Behaviour_ind'; induction B2 using Behaviour_ind'; simpl;
  try case_eq mB; try case_eq mB'; try case mB0; try case mB'0; simpl;
  intros; try constructor;
  try (inversion H; fail); try (inversion H3; fail).
10,13,16,17,18: exfalso; revert H5;
  case_eq (Pid_dec p p0); intro Hp; simpl; [idtac | intro H'; inversion H'];
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp;
  repeat rewrite inject_match; intro; inversion H5.
7,10,13,14:  revert H5;
  case_eq (Pid_dec p p0); intro Hp; simpl; [idtac | intro H'; inversion H'];
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp;
  intros; constructor.
+ revert H.
  case_eq (Pid_dec p p0); intro Hp; simpl. 2: intro H'; inversion H'.
  case_eq (Expr_dec e e0); intro He; simpl. 2: intro H'; inversion H'.
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp.
  unfold Expr_dec in He; rewrite Edec.eqb_eq in He; rewrite He.
  intros; constructor.
  apply IHB1.
  elim (XUndefined_dec (Xmerge (inject B1) (inject B2))); intro.
  1: rewrite a in H; inversion H.
  rewrite Xmatch_elim in H; auto.
  inversion H. rewrite H1; auto.
+ revert H.
  case_eq (Pid_dec p p0); intro Hp; simpl. 2: intro H'; inversion H'.
  case_eq (Var_dec v v0); intro Hv; simpl. 2: intro H'; inversion H'.
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp.
  unfold Var_dec in Hv; rewrite Xdec.eqb_eq in Hv. rewrite Hv.
  intros; constructor.
  apply IHB1.
  elim (XUndefined_dec (Xmerge (inject B1) (inject B2))); intro.
  1: rewrite a in H; inversion H.
  rewrite Xmatch_elim in H; auto.
  inversion H. rewrite H1; auto.
+ revert H.
  case_eq (Pid_dec p p0); intro Hp; simpl. 2: intro H'; inversion H'.
  case_eq (eqb_label l l0); intro Hl; simpl. 2: intro H'; inversion H'.
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp.
  rewrite label_eqb_eq in Hl; rewrite Hl.
  intros; constructor.
  apply IHB1.
  elim (XUndefined_dec (Xmerge (inject B1) (inject B2))); intro.
  1: rewrite a in H; inversion H.
  rewrite Xmatch_elim in H; auto.
  inversion H. rewrite H1; auto.
+ revert H5.
  case_eq (Pid_dec p p0); intro Hp; simpl. 2: intro H'; inversion H'.
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp.
  intros.
  assert (Xmerge (inject b1) (inject b) = inject b1 /\ Xmerge (inject b2) (inject b0) = inject b2).
  1: {
    elim (XUndefined_dec (Xmerge (inject b2) (inject b0))); intro.
    1: rewrite a in H5; inversion H5. 
    rewrite Xmatch_elim in H5; auto.
    elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro.
    1: rewrite a in H5; inversion H5.
    rewrite Xmatch_elim in H5; auto.
    inversion H5. rewrite H7, H8; auto.
  }
  inversion_clear H6.
  constructor; auto.
+ revert H5.
  case_eq (Pid_dec p p0); intro Hp; simpl. 2: intro H'; inversion H'.
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp.
  intros; constructor.
  apply H; auto.
  elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro.
  rewrite a in H5; inversion H5.
  rewrite Xmatch_elim, inject_match in H5; auto.
  inversion H5. rewrite H7; auto.
+ revert H5.
  case_eq (Pid_dec p p0); intro Hp; simpl. 2: intro H'; inversion H'.
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp.
  intros; constructor.
  apply H0; auto. rewrite inject_match in H5.
  elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro.
  rewrite a in H5; inversion H5.
  rewrite Xmatch_elim in H5; auto.
  inversion H5. rewrite H7; auto.
+ exfalso. revert H5.
  case_eq (Pid_dec p p0); intro Hp; simpl. 2: intro H'; inversion H'.
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp.
  rewrite inject_match.
  elim (XUndefined_dec (Xmerge (inject b1) (inject b0))); intro.
  rewrite a; intro; inversion H5.
  rewrite Xmatch_elim; auto. intro; inversion H5.
+ revert H5.
  case_eq (Pid_dec p p0); intro Hp; simpl. 2: intro H'; inversion H'.
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp.
  intros; constructor.
  apply H; auto.
  elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro.
  rewrite a in H5; inversion H5.
  rewrite Xmatch_elim in H5; auto.
  inversion H5. rewrite H7; auto.
+ exfalso. revert H5.
  case_eq (Pid_dec p p0); intro Hp; simpl. 2: intro H'; inversion H'.
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp.
  rewrite inject_match.
  elim (XUndefined_dec (Xmerge (inject b1) (inject b))); intro.
  rewrite a; intro; inversion H5.
  rewrite Xmatch_elim; auto. intro; inversion H5.
+ revert H5.
  case_eq (Pid_dec p p0); intro Hp; simpl. 2: intro H'; inversion H'.
  unfold Pid_dec in Hp; rewrite Pdec.eqb_eq in Hp; rewrite Hp.
  intros; constructor.
  apply H0; auto.
  elim (XUndefined_dec (Xmerge (inject b0) (inject b))); intro.
  rewrite a in H5; inversion H5.
  rewrite Xmatch_elim in H5; auto.
  inversion H5. rewrite H7; auto.
+ revert H.
  case_eq (BExpr_dec b b0); intro Hb; simpl. 2: intro H'; inversion H'.
  unfold BExpr_dec in Hb; rewrite Bdec.eqb_eq in Hb; rewrite Hb.
  rename B1_1 into Bt, B1_2 into Be, B2_1 into Bt', B2_2 into Be'.
  intro.
  assert (Xmerge (inject Bt) (inject Bt') = inject Bt /\ Xmerge (inject Be) (inject Be') = inject Be).
  1: {
    elim (XUndefined_dec (Xmerge (inject Bt) (inject Bt'))); intro.
    1: rewrite a in H; inversion H. 
    elim (XUndefined_dec (Xmerge (inject Be) (inject Be'))); intro.
    1: rewrite a, Xmatch_elim in H; auto; inversion H.
    revert H.
    case (Xmerge (inject Bt) (inject Bt')); case (Xmerge (inject Be) (inject Be'));
      intros; try inversion H; auto.
  }
  inversion_clear H0. constructor; auto.
+ revert H.
  case_eq (RecVar_dec X X0); intro HX; simpl. 2: intro H'; inversion H'.
  unfold RecVar_dec in HX; rewrite Rdec.eqb_eq in HX; rewrite HX.
  constructor.
Qed.

Lemma more_branches_char : forall B1 B2,
  more_branches B1 B2 <-> merge B1 B2 = inject B1.
Proof.
split.
+ apply more_branches_char_1.
+ apply more_branches_char_2.
Qed.

Lemma merge_more_branches : forall B1 B2 B,
  merge B1 B2 = inject B -> more_branches B B1.
Proof.
unfold merge; intros.
rename H into Hinj; revert B1 B2 Hinj.
induction B using Behaviour_ind'; simpl; intros.
+ elim (merge_inv_End _ _ Hinj); intros.
  rewrite H; constructor.
+ elim (merge_inv_Send _ _ _ _ _ Hinj); intros.
  rename x into B1'; inversion_clear H.
  rename x into B2'; inversion_clear H0.
  inversion_clear H1.
  rewrite H; constructor; eauto.
+ elim (merge_inv_Recv _ _ _ _ _ Hinj); intros.
  rename x into B1'; inversion_clear H.
  rename x into B2'; inversion_clear H0.
  inversion_clear H1.
  rewrite H; constructor; eauto.
+ elim (merge_inv_Sel _ _ _ _ _ Hinj); intros.
  rename x into B1'; inversion_clear H.
  rename x into B2'; inversion_clear H0.
  inversion_clear H1.
  rewrite H; constructor; eauto.
+ revert Hinj. case_eq mB; case_eq mB'; intros;
  elim (merge_inv_Branching _ _ _ _ _ Hinj); intros;
  rename x into Bl'; inversion_clear H3;
  rename x into Bl''; inversion_clear H4;
  rename x into Br'; inversion_clear H3;
  rename x into Br''; inversion_clear H4;
  destroy H5; rewrite H3.
  - elim (H8 (inject b0)); auto; intros; inversion_clear H10.
    elim (H5 (inject b)); auto; intros; inversion_clear H13.
    case_eq Bl'; case_eq Bl''; case_eq Br'; case_eq Br''; constructor.
    3,5: apply (H _ H2 b3 b2); apply H12; auto.
    2,6,11,13: apply (H0 _ H1 b2 b1); apply H15; auto.
    2,6,9,10: apply (H0 _ H1 b1 b);
      elim H14; auto; intros; destroy H19;
      rewrite H16 in H20; inversion H20;
      rewrite <- H19; apply merge_idempotent.
    4,5: apply (H _ H2 b2 b0);
      elim H11; auto; intros; destroy H19;
      rewrite H18 in H20; inversion H20;
      rewrite <- H19; apply merge_idempotent.
    * apply (H _ H2 b4 b3). apply H12; auto.
    * apply (H _ H2 b2 b1). apply H12; auto.
    * apply (H _ H2 b3 b0).
      elim H11; auto. intros. destroy H19.
      rewrite H18 in H20; inversion H20.
      rewrite <- H19. apply merge_idempotent.
    * apply (H _ H2 b1 b0).
      elim H11; auto. intros. destroy H19.
      rewrite H18 in H20; inversion H20.
      rewrite <- H19. apply merge_idempotent.
  - elim (H8 (inject b)); auto; intros; inversion_clear H10.
    elim H7; auto; intros. rewrite H10.
    case_eq Bl'; case_eq Bl''; constructor.
    * apply (H _ H2 b1 b0). apply H12; auto.
    * apply (H _ H2 b0 b).
      elim H11; auto; intros. destroy H16.
      rewrite H15 in H17; inversion H17.
      rewrite <- H16; apply merge_idempotent.
  - elim (H5 (inject b)); auto; intros; inversion_clear H10.
    elim H6; auto; intros. rewrite H10.
    case_eq Br'; case_eq Br''; constructor.
    * apply (H0 _ H1 b1 b0). apply H12; auto.
    * apply (H0 _ H1 b0 b).
      elim H11; auto; intros. destroy H16.
      rewrite H15 in H17; inversion H17.
      rewrite <- H16; apply merge_idempotent.
  - elim H6; auto; intros. rewrite H9.
    elim H7; auto; intros. rewrite H11.
    constructor.
+ elim (merge_inv_Cond _ _ _ _ _ Hinj); intros.
  rename x into Be'; inversion_clear H.
  rename x into Be''; inversion_clear H0.
  rename x into Bt; inversion_clear H.
  rename x into Bt''; destroy H0.
  rewrite H; constructor; eauto.
+ elim (merge_inv_Call _ _ _ Hinj); intros.
  rewrite H; constructor; eauto.
Qed.

Lemma merge_more_branches' : forall B1 B2 B,
  merge B1 B2 = inject B -> more_branches B B2.
Proof.
intros.
apply merge_more_branches with B1.
rewrite merge_comm; auto.
Qed.

End MoreBranches.

(** Needs: projectability preserved by reduction; characterization of EPP. *)

Lemma EPP_reduces : forall Xs ps P s tl P' s' HP,
  ((P,s) --[tl]--> (P',s'))%MC ->
  exists tl' N', (epp Xs ps P HP,s) --[tl']--> (N',s').
Proof.
intros.
induction P as (D,C), P' as (D',C').
generalize (MCP_To_Defs_stable _ _ _ _ _ _ _ H); intro.
rewrite <- H0 in H; clear D' H0.
inversion H.
clear s'0 H6 C'0 H5 s0 H3 C0 H2 Defs H0 tl H1 H.
inversion HP. simpl in H, H0. destroy H0.
induction H4.
+ exists (forget (R_Com p v q x)).
  exists (Build_Program (epp_D _ _ H1) EmptyNet).



(*
Theorem EPP_Complete : forall P s P' s' tl, projectable P ->
  ((P,s) --[tl]--> (P',s'))%MC ->
  exists N', ...
Proof.
induction P.
*)

(*

More branches is behavioural equivalence.

*)


Definition more_branches_beh (B1 B2:Behaviour) := (merge_beh B1 B2) = Some B1.


Definition more_branches_net (N N':Network) (ps:list Pid) :=
  forall p, In p ps -> more_branches_beh (N p) (N' p).

Definition more_branches_defs (SPDefs SPDefs' : RecVar -> Behaviour) :=
  forall X, more_branches_beh (SPDefs X) (SPDefs' X).

Inductive MoreBranches_net : Network -> Network -> list Pid -> Prop :=
| MBN_nil N N' : MoreBranches_net N N' nil
| MBN_cons N N' p ps :
  MoreBranches (N p) (N' p) -> MoreBranches_net N N' ps ->
  MoreBranches_net N N' (p::ps).

Lemma more_branches_beh_MoreBranches_1 :
  forall B B',
  more_branches_beh B B' -> MoreBranches B B'.
Proof.
intro.
induction B using Behaviour_ind_b; intro; induction B' using Behaviour_ind_b; try easy.
+ intro. constructor.
+ specialize (IHB B').
  intro.
  red in H. inversion H. clear H.
  generalize H1. clear H1.
  case_eq (Pid_dec p p0); case_eq (Expr_dec e e0); try easy.
  intro. intro.
  rewrite Pdec.eqb_eq in H0. rewrite <- H0.
  rewrite Edec.eqb_eq in H. rewrite <- H.
  simpl.
  case_eq (merge_beh B B'); try easy.
  intros.
  constructor.
  inversion H2. clear H2.
  rewrite H4 in H1.
  apply (IHB H1).
+ specialize (IHB B').
  intro.
  red in H. inversion H. clear H.
  generalize H1. clear H1.
  case_eq (Pid_dec p p0); case_eq (Var_dec v v0); try easy.
  intro. intro.
  rewrite Pdec.eqb_eq in H0. rewrite <- H0.
  rewrite Xdec.eqb_eq in H. rewrite <- H.
  simpl.
  case_eq (merge_beh B B'); try easy.
  intros.
  constructor.
  inversion H2. clear H2.
  rewrite H4 in H1.
  apply (IHB H1).
+ specialize (IHB B').
  intro.
  red in H. inversion H. clear H.
  generalize H1. clear H1.
  case_eq (Pid_dec p p0); case_eq (eqb_label l l0); try easy.
  intro. intro.
  rewrite Pdec.eqb_eq in H0. rewrite <- H0.
  rewrite label_eqb_eq in H. rewrite <- H.
  simpl.
  case_eq (merge_beh B B'); try easy.
  intros.
  constructor.
  inversion H2. clear H2.
  rewrite H4 in H1.
  apply (IHB H1).
+ clear H1 H2.
  rewrite more_branches_beh_char.
  intro. red in H1.
  generalize H1. clear H1.
  case_eq (Pid_dec p p0); try easy.
  intro.
  rewrite Pdec.eqb_eq in H1. rewrite <- H1.
  case_eq (o left); case_eq (o right); case_eq (o0 left); case_eq (o0 right); constructor; try easy.
  - intros. exists b2. split. apply H5.
    apply H; auto.
    rewrite more_branches_beh_char.
    rewrite H3 in H7. inversion H7. clear H7.
    rewrite <- H9.
    apply H6.
  - intros. exists b1. split. apply H4.
    apply H0; auto.
    rewrite more_branches_beh_char.
    rewrite H2 in H7. inversion H7. clear H7.
    rewrite <- H9.
    apply H6.
  - intros. exists b1. split. apply H5.
    apply H; auto.
    rewrite more_branches_beh_char.
    rewrite H3 in H7. inversion H7. clear H7.
    rewrite <- H9.
    apply H6.
  - intros. rewrite H2 in H7. inversion H7.
  - intros. rewrite H3 in H7. inversion H7.
  - intros. exists b0. split. apply H4.
    apply H0; auto.
    rewrite more_branches_beh_char.
    rewrite H2 in H7. inversion H7. clear H7.
    rewrite <- H9.
    apply H6.
  - intros. rewrite H3 in H7. inversion H7.
  - intros. rewrite H2 in H7. inversion H7.
  - intros. exists b0. split. apply H5.
    apply H; auto.
    rewrite more_branches_beh_char.
    rewrite H3 in H7. inversion H7. clear H7.
    rewrite <- H9.
    apply H6.
  - intros. rewrite H2 in H7. inversion H7.
  - intros. rewrite H3 in H7. inversion H7.
  - intros. rewrite H2 in H7. inversion H7.
  - intros. rewrite H3 in H7. inversion H7.
  - intros. exists b0. split. apply H4.
    apply H0; auto.
    rewrite more_branches_beh_char.
    rewrite H2 in H7. inversion H7. clear H7.
    rewrite <- H9.
    apply H6.
  - intros. rewrite H3 in H7. inversion H7.
  - intros. rewrite H2 in H7. inversion H7.
  - intros. rewrite H3 in H7. inversion H7.
  - intros. rewrite H2 in H7. inversion H7.
+ clear IHB'1 IHB'2.
  intro. rewrite more_branches_beh_char in H. red in H. generalize H. clear H.
  case_eq (BExpr_dec b b0).
  2: easy.
  intros.
  specialize (IHB1 B'1). specialize (IHB2 B'2).
  rewrite more_branches_beh_char in IHB1, IHB2.
  inversion H0. clear H0.
  pose (Hthen := IHB1 H1). pose (Helse := IHB2 H2).
  rewrite Bdec.eqb_eq in H.
  rewrite <- H.
  constructor; auto.
+ rewrite more_branches_beh_char.
  intro. red in H. generalize H. clear H.
  case_eq (RecVar_dec r r0).
  2: easy.
  intros.
  rewrite Rdec.eqb_eq in H.
  rewrite H.
  constructor.
Qed.

Lemma more_branches_beh_MoreBranches_2 :
  forall B B',
  MoreBranches B B' -> more_branches_beh B B'.
Proof.
intros. apply more_branches_beh_char. revert H. revert B'.
induction B using Behaviour_ind_b; intro; induction B' using Behaviour_ind_b; try (easy; fail).
all: intro HMB; inversion HMB; clear HMB.
+ (*rewrite <- H3. rewrite <- H4.*) clear H H1 H2 H3 H4 H5.
  simpl. rewrite Pdec.eqb_refl. rewrite Edec.eqb_refl. simpl.
  apply (IHB _ H0).
+ simpl. rewrite Pdec.eqb_refl. rewrite Xdec.eqb_refl. simpl.
  apply (IHB _ H0).
+ simpl. rewrite Pdec.eqb_refl. rewrite label_eqb_refl. simpl.
  apply (IHB _ H0).
+ simpl. rewrite Pdec.eqb_refl. split.
  - case_eq (o left); case_eq (o0 left); auto.
    * intros.
      apply (H _ H10).
      specialize (H6 _ H9). destruct H6. inversion H6.
      rewrite H10 in H11. inversion H11. apply H6.
    * intros. specialize (H6 _ H9). destruct H6. inversion H6. rewrite H11 in H10. inversion H10.
  - case_eq (o right); case_eq (o0 right); auto.
    * intros.
      apply (H0 _ H10).
      specialize (H8 _ H9). destruct H8. inversion H8.
      rewrite H10 in H11. inversion H11. apply H12.
    * intros. specialize (H8 _ H9). destruct H8. inversion H8. rewrite H11 in H10. inversion H10.
+ simpl. rewrite Bdec.eqb_refl. split.
  - apply (IHB1 _ H1).
  - apply (IHB2 _ H6).
+ simpl. rewrite Rdec.eqb_refl. trivial.
Qed.

Lemma more_branches_beh_MoreBranches :
  forall B B',
  more_branches_beh B B' <-> MoreBranches B B'.
Proof.
split. apply more_branches_beh_MoreBranches_1. apply more_branches_beh_MoreBranches_2.
Qed.

Lemma more_branches_net_MoreBranches_2 :
  forall N N' ps,
  MoreBranches_net N N' ps -> more_branches_net N N' ps.
Proof.
intro. intro.
induction ps.
1: { red. intros. inversion H0. }
intro.
inversion H.
red.
rewrite <- H0 in H4. rewrite <- H0.
intros.
inversion H6.
- rewrite <- H7. apply more_branches_beh_MoreBranches. apply H4.
- pose (H' := IHps H5).
  apply (H' _ H7).
Qed.

Lemma more_branches_net_mono :
  forall N N' p ps,
  more_branches_net N N' (p::ps) -> more_branches_net N N' ps.
Proof.
red. intros.
case (P.eq_dec p0 p); intros.
+ rewrite e.
  red in H. apply (H p). constructor. reflexivity.
+ red in H. apply (H p0). apply in_cons. assumption.
Qed.

Lemma more_branches_net_MoreBranches_1 :
  forall N N' ps,
  more_branches_net N N' ps -> MoreBranches_net N N' ps.
Proof.
intro. intro.
induction ps; intros.
1: constructor.
constructor.
- red in H. specialize (H a).
  assert (In a (a::ps)).
  1: constructor; trivial.
  pose (Ha := H H0).
  apply more_branches_beh_MoreBranches; auto.
- apply more_branches_net_mono in H.
  apply (IHps H).
Qed.

Lemma more_branches_net_MoreBranches :
  forall N N' ps,
  more_branches_net N N' ps <-> MoreBranches_net N N' ps.
Proof.
split. apply more_branches_net_MoreBranches_1. apply more_branches_net_MoreBranches_2.
Qed.

Lemma more_branches_completeness :
  forall N1 N2 N2' ps SPDefs1 SPDefs2 s s' t,
    within_ps ps N1 -> within_ps ps N2 ->
    more_branches_net N1 N2 ps ->
    more_branches_defs SPDefs1 SPDefs2 ->
    SP_To SPDefs1 N2 s t N2' s' ->
    exists N1', SP_To SPDefs2 N1 s t N1' s' /\ more_branches_net N1' N2' ps.
Proof.
intros.
red in H, H0, H1, H2.
inversion H3.
+ assert (In p ps) as Hp. elim (In_dec P.eq_dec p ps); auto. intro; rewrite H0 in H4; auto; inversion H4.
  assert (In q ps) as Hq. elim (In_dec P.eq_dec q ps); auto. intro; rewrite H0 in H5; auto; inversion H5.
  generalize (H1 _ Hp); generalize (H1 _ Hq); intros.
  apply more_branches_beh_MoreBranches_1 in H14.
  apply more_branches_beh_MoreBranches_1 in H15.
  rewrite H4 in H15; rewrite H5 in H14.
  inversion H14; inversion H15.
  rewrite H17, H19 in H16; clear p0 H17 x0 H19 B'0 H20.
  rewrite H22, H24 in H21; clear B'1 H25 e0 H24 p1 H22.
  exists (fun r => if (Pid_dec r p) then B1 else if (Pid_dec r q) then B0 else N1 r); split.
  - apply S_Com with B1 B0; auto.
    case_eq (Pid_dec p p); auto. intro. apply Pdec.eqb_neq in H17. elim H17; auto.
    assert (q <> p). intro. rewrite H17 in H16; rewrite <- H16 in H21; inversion H21.
    rewrite <- Pdec.eqb_neq in H17; unfold Pid_dec at 1; rewrite H17; auto.
    case_eq (Pid_dec q q); auto. intro. apply Pdec.eqb_neq in H19. elim H19; auto.
    red; intros.
    case_eq (Pid_dec p0 p); intros.
    1: { rewrite Pdec.eqb_eq in H19. rewrite H19 in H17. elim H17; simpl; auto. }
    case_eq (Pid_dec p0 q); intros.
    1: { rewrite Pdec.eqb_eq in H20. rewrite H20 in H17. elim H17; simpl; auto. }
    auto.
  - red. intros.
    case_eq (Pid_dec p0 p); intros.
    * rewrite Pdec.eqb_eq in H19. rewrite H19.
      rewrite H6. apply (more_branches_beh_MoreBranches). auto.
    * case_eq (Pid_dec p0 q); intros.
      ** rewrite Pdec.eqb_eq in H20. rewrite H20.
         rewrite H7. apply (more_branches_beh_MoreBranches). auto.
      ** rewrite Pdec.eqb_neq in H19, H20.
         red in H8. specialize (H8 p0).
         assert (~ In p0 (p::q::nil)).
         *** simpl. red. intros.
             inversion H22; auto.
             inversion H24; auto.
         *** pose (H' := H8 H22).
             rewrite H'. auto.
Admitted.

End EPP_Properties.

End EPPBase.
