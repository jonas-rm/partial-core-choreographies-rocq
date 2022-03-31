Require Export CC.
Require Export XMerge.

Local Open Scope nat_scope.

Ltac sup := unfold set_union_pid; rewrite set_union_iff; auto.

Section EndPointProjection.

Variable Sig : Signature.

Local Definition Pid := pid Sig.
Local Definition Var := var Sig.
Local Definition Value := value Sig.
Local Definition Expr := expr Sig.
Local Definition BExpr := bexpr Sig.
Local Definition RecVar := recvar Sig.
Local Definition Ann := ann Sig.
Local Definition Ev := ev Sig.
Local Definition BEv := bev Sig.

Local Definition PR := DecProd RecVar Pid.

Definition Sig' := Build_Signature Pid Var Value Expr BExpr PR Ann Ev BEv.

Open Scope CC.

Section EPP.

(** ** EndPoint projection
  First step: returns an XBehaviour, possibly with XUndefined subcomponents. *)
Fixpoint bproj (Defs:DefSet Sig) (C:Choreography Sig) (r:Pid) : XBehaviour Sig' :=
match C with
| CC.End                    => XEnd
| p#e --> q$x @ a ;; C'     => if eq_dec p r
                               then @XSend Sig' q e a (bproj Defs C' r)
                               else if eq_dec q r
                                    then @XRecv Sig' p x a (bproj Defs C' r)
                                    else bproj Defs C' r
| p --> q[left] @ a;; C'    => if eq_dec p r
                               then @XSel Sig' q left a (bproj Defs C' r)
                               else if eq_dec q r
                                    then @XBranching Sig' p (Some (a,bproj Defs C' r)) None
                                    else bproj Defs C' r
| p --> q[right] @ a;; C'       => if eq_dec p r
                               then @XSel Sig' q right a (bproj Defs C' r)
                               else if eq_dec q r
                                    then @XBranching Sig' p None (Some (a,bproj Defs C' r))
                                    else bproj Defs C' r
| If p ?? b Then C1 Else C2 => if eq_dec p r
                               then @XCond Sig' b (bproj Defs C1 r) (bproj Defs C2 r)
                               else bproj Defs C1 r [[\/]] bproj Defs C2 r
| CC.Call X                 => if In_dec (@eq_dec Pid) r (fst (Defs X))
                               then @XCall Sig' (X,r)
                               else XEnd
| RT_Call X ps C'           => if In_dec (@eq_dec Pid) r ps
                               then @XCall Sig' (X,r)
                               else bproj Defs C' r
end.

(** Second step: collapse all undefined behaviours. *)
Definition epp_list (Defs:DefSet Sig) (C:Choreography Sig) (ps:list Pid) : list (Pid * XBehaviour _) :=
  map (fun p => (p, collapse (bproj Defs C p))) ps.

(** Definitions of projectability at all different levels. *)
Definition projectable_C Defs ps C :=
  Forall (fun X => snd X <> XUndefined) (epp_list Defs C ps).

Definition projectable_D Xs Defs :=
  Forall (fun X => projectable_C Defs (fst (Defs X)) (snd (Defs X)) ) Xs.

Definition projectable Xs ps P :=
  projectable_C (Procedures Sig P) ps (Main P) /\
  projectable_D Xs (Procedures _ P) /\
  (forall p, In p (CCC_pn (Main P) (fun _ => nil)) -> In p ps) /\
  (forall p X, In X Xs -> In p (fst (Procedures _ P X)) -> In p ps) /\
  (forall p X, In X Xs -> In p (CCC_pn (snd (Procedures _ P X)) (fun _ => nil)) -> In p ps).

(** Not decidable, but in practice easy to compute. 
  Maybe we want to compute ps from Xs? *)
Definition Projectable P := exists Xs ps,
  projectable Xs ps P /\ Program_WF _ Xs P.

(** For simplifying future definitions. *)
Lemma projectable_C_use : forall Defs ps C, projectable_C Defs ps C ->
  forall p, In p ps -> exists B, collapse (bproj Defs C p) = inject B.
Proof.
intros.
red in H. rewrite Forall_forall in H.
elim (collapse_char' _ (bproj Defs C p)); intros.
inversion_clear a.
+ rewrite H1. rewrite collapse_inject. exists x; auto.
+ elim (H (p,collapse (bproj Defs C p))); auto.
  unfold epp_list; rewrite in_map_iff.
  exists p; auto.
Qed.

Lemma projectable_C_use' : forall Defs ps C, projectable_C Defs ps C ->
  forall p, In p ps -> collapse (bproj Defs C p) <> XUndefined.
Proof.
intros. apply projectable_C_use with (p:=p) in H; auto.
inversion_clear H. rewrite H1.
apply inject_not_undefined.
Qed.

(** Now we can define EPP, again in a layered manner.
  Definitions are interactive because of the absurd cases. *)
Definition epp_C Defs ps C : projectable_C Defs ps C -> Network Sig'.
Proof.
intros; intro p.
elim (In_dec (@eq_dec Pid) p ps); intro Hp.
2: apply End.
elim (collapse_char' _ (bproj Defs C p)); intro.
1: inversion_clear a. apply x.
exfalso.
apply projectable_C_use' with (p:=p) in H; auto.
Defined.

Definition epp_D Xs Defs : projectable_D Xs Defs -> DefSetB Sig'.
Proof.
intros; intro.
case_eq X; intros R p HX.
elim (In_dec (@eq_dec RecVar) R Xs).
2: intros; apply End.
elim (In_dec (@eq_dec Pid) p (fst (Defs R))).
2: intros; apply End.
elim (collapse_char' _ (bproj Defs (snd (Defs R)) p)); intros.
induction a. apply x.
exfalso.
red in H. rewrite Forall_forall in H.
generalize (H _ a0); clear H; intro.
apply projectable_C_use' with (p:=p) in H; auto.
Defined.

Definition epp Xs ps P : projectable Xs ps P -> Program Sig'.
Proof.
intro H; inversion_clear H. inversion_clear H1.
constructor.
apply (epp_D _ _ H).
apply (epp_C _ _ _ H0).
Defined.

(** Auxiliary results about behaviour projection. *)
Lemma bproj_not_In : forall Defs r C,
  ~In r (CCC_pn C (fun X => fst (Defs X))) -> bproj Defs C r = XEnd.
Proof.
induction C; simpl; auto; intros.
+ assert (bproj Defs C r = XEnd).
  1: apply IHC; intro; apply H; sup.
  induction e.
  - intros. case_eq (eq_dec t0 r); [idtac | case_eq (eq_dec t2 r)]; auto.
    all: intros; elim H; rewrite e; simpl; sup; left. left; auto.
    right; left; auto.
  - case t2; (case_eq (eq_dec t0 r); [idtac | case_eq (eq_dec t1 r)]); auto.
    all: intros; elim H; rewrite e; simpl; sup; left.
    1,3: left; auto. all: right; left; auto.
+ assert (bproj Defs C1 r = XEnd).
  1: apply IHC1; intro; apply H; sup. left; sup.
  assert (bproj Defs C2 r = XEnd).
  1: apply IHC2; intro; apply H; sup.
  case_eq (eq_dec t r).
  2: rewrite H0, H1; auto.
  intros; elim H; rewrite e; simpl; sup. left; sup. left; left; auto.
+ elim in_dec; auto. intro; elim H; auto.
+ elim in_dec; intros.
  - elim H; sup.
  - apply IHC. intro; apply H; sup.
Qed.

Lemma bproj_Call_In : forall Defs C p X, bproj Defs C p = @XCall Sig' (X, p) ->
  consistent _ (fun X => fst (Defs X)) C -> In p (fst (Defs X)).
Proof.
induction C; try induction e; simpl.
+ intros r X. elim eq_dec. intros. inversion H.
  elim eq_dec. intros; inversion H. auto.
+ intros p1 X. case t2.
  - elim eq_dec. intros; inversion H.
    elim eq_dec. intros; inversion H. auto.
  - elim eq_dec. intros; inversion H.
    elim eq_dec. intros; inversion H. auto.
+ intros p0 X. elim eq_dec. intros; inversion H.
  intros. apply Xmerge_inv_Call in H. destroy H. destroy H0. auto.
+ do 2 intro. elim in_dec; intros; inversion H.
  rewrite <- H2; auto.
+ do 2 intro. elim in_dec; intros; destroy H0; auto.
  inversion H. rewrite <- H3. apply (H1 p); auto.
+ intros. inversion H.
Qed.

Lemma bproj_disjoint : forall Defs e a C p, ~In p (eta_pn _ e) ->
  bproj Defs (e@a;; C) p = bproj Defs C p.
Proof.
induction e; intros.
+ simpl in H. assert (t <> p /\ t1 <> p). tauto.
  inversion_clear H0.
  simpl. repeat rewrite DecType_neq; auto.
+ simpl in H. assert (t <> p /\ t0 <> p). tauto.
  inversion_clear H0.
  simpl. repeat rewrite DecType_neq; case t1; auto.
Qed.

Open Scope SP_scope.

(** Proof irrelevance for EPP. *)
Lemma epp_C_wd : forall Defs C ps H H',
  epp_C Defs ps C H == epp_C Defs ps C H'.
Proof.
intros; intro. unfold epp_C.
elim In_dec; auto.
intros. elim collapse_char'; auto.
intros. exfalso.
red in H. rewrite Forall_forall in H.
apply (H (p, collapse (bproj Defs C p))); auto.
apply in_map_iff. exists p; auto.
Qed.

Lemma epp_C_out : forall Defs C ps H p, ~In p ps ->
  epp_C Defs ps C H p = End _.
Proof. intros; unfold epp_C. elim In_dec; tauto. Qed.

Lemma epp_C_out' : forall Defs ps C HC p,
  ~In p (CCC_pn C (fun X => fst (Defs X))) -> epp_C Defs ps C HC p = End _.
Proof.
intros.
unfold epp_C; simpl.
elim In_dec; auto.
elim collapse_char'; intros.
induction a; simpl.
apply inject_inj. rewrite <- p0.
clear a0 p0 x.
2: { exfalso. apply projectable_C_use' with (p:=p) in HC; auto. }
clear HC.
induction C; intros; auto.
rename t into a; induction e. 2: induction t1.
all: simpl.
1,2,3,4: case_eq (eq_dec t p); intros.
2: case_eq (eq_dec t1 p); auto.
5,7: case_eq (eq_dec t0 p); auto.
12: elim (In_dec (@eq_dec Pid) p (fst (Defs t))); auto.
13: elim (In_dec (@eq_dec Pid) p l).
all: intros.
1,2,4,5,7,9,10: elim H; rewrite e; simpl; sup; simpl; auto.
1: sup; repeat left; auto.
1,2,3: apply IHC; auto; intro; apply H; simpl; sup.
+ destroy Hsp. rewrite IHC1, IHC2; auto.
  intro; apply H. simpl; sup; sup.
  intro; apply H. simpl; sup; sup.
+ elim H; auto.
+ elim H. simpl; sup.
+ destroy Hsp. apply IHC; auto.
  intro; apply H. simpl; sup.
Qed.

Lemma epp_C_char : forall Xs ps Defs C HP HC,
  Net (epp Xs ps {| Procedures := Defs; Main := C |} HP) == (epp_C Defs ps C HC).
Proof.
intros.
unfold epp.
case HP; intros. case a; intros.
apply epp_C_wd.
Qed.

Lemma epp_C_char' : forall Xs ps Defs C HP p, In p ps ->
  bproj Defs C p = inject (Net (epp Xs ps {| Procedures := Defs; Main := C |} HP) p).
Proof.
intros; unfold epp.
case HP; intros. case a; intros.
simpl.
unfold epp_C. elim in_dec; simpl.
elim collapse_char'; simpl.
+ induction a1; auto.
+ intros. exfalso.
  red in p0. rewrite Forall_forall in p0.
  apply (p0 (p, collapse (bproj Defs C p))); auto.
  apply in_map_iff. exists p; auto.
+ tauto.
Qed. 

Lemma epp_C_bproj : forall Defs ps C HC p, In p ps ->
  bproj Defs C p = inject (epp_C Defs ps C HC p).
Proof.
intros. unfold epp_C; simpl.
elim In_dec; simpl. 2: tauto.
elim collapse_char'. induction a; auto.
intro; exfalso. apply projectable_C_use' with (p:=p) in HC; auto.
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
apply (H (p, collapse  (bproj Defs (snd (Defs R)) p))); auto.
apply in_map_iff. exists p; auto.
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

Lemma epp_D_char' : forall Xs ps Defs C HP X p,
  In X Xs -> set_incl_pid (CCC_pn (snd (Defs X)) (fun Y => fst (Defs Y))) (fst (Defs X)) ->
  bproj Defs (snd (Defs X)) p = inject (Procs (epp Xs ps {| Procedures := Defs; Main := C |} HP) (X,p)).
Proof.
intros.
unfold epp.
case HP; intros.
case a; simpl; intro HD. clear a; intros.
elim In_dec; simpl; intro Hp; elim In_dec; simpl; intro HX.
elim collapse_char'; simpl; intro Hb.
elim Hb; simpl; intros; auto.
+ exfalso. red in HD. rewrite Forall_forall in HD.
  generalize (HD X HX); intro HD'.
  red in HD'. rewrite Forall_forall in HD'.
  apply (HD' (p, collapse (bproj Defs (snd (Defs X)) p))); auto.
  apply in_map_iff. exists p; auto.
+ tauto.
+ apply bproj_not_In.
  intro; apply Hp, H0. auto.
+ tauto.
Qed.

Lemma epp_D_char'' : forall Xs ps Defs C HP X p HX, In X Xs ->
   Procs (epp Xs ps {| Procedures := Defs; Main := C |} HP) (X, p) =
   epp_C Defs (fst (Defs X)) (snd (Defs X)) HX p.
Proof.
intros Xs ps Defs C HP X p HX HX'.
inversion HP. clear H. destroy H0. clear H1 H2 H0.
rewrite epp_D_char with (HD:=H).
simpl. elim In_dec; intro.
2: simpl; rewrite epp_C_out; auto.
all: elim In_dec; simpl; auto. 2: intro H'; elim H'; auto.
elim collapse_char'. induction a0; simpl; intros.
apply inject_inj. rewrite <- p0. apply epp_C_bproj; auto.
intro; exfalso. apply projectable_C_use' with (p:=p) in HX; auto.
Qed.

Lemma epp_out : forall Xs ps Defs C HP p, ~In p ps ->
  Net (epp Xs ps {| Procedures := Defs; Main := C |} HP) p = End _.
Proof.
intros; unfold epp.
unfold epp.
case HP; intros.
case a; simpl; intro HD. clear a; intros.
apply epp_C_out; auto.
Qed.

(** Sanity checks: EPP works as defined informally in the paper. *)
Lemma epp_C_Com_p : forall Defs ps C p e q x a HC HC', In p ps ->
  epp_C Defs ps (p#e-->q$x@a;;C) HC p = Send Sig' q e a (epp_C Defs ps C HC' p).
Proof.
intros. rename a into A. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
rewrite DecType_eq in p0.
rewrite p1 in p0. induction x0; inversion p0.
2: case o, o0; try induction p2; try induction p3; inversion p0.
apply inject_inj in H4; rewrite H4; auto.
intro. exfalso. clear p0.
apply projectable_C_use' with (p:=p) in HC'; auto.
simpl. intro; exfalso.
revert b; rewrite DecType_eq.
simpl. rewrite Xmatch_elim. discriminate.
apply projectable_C_use' with ps; auto.
Qed.

Lemma epp_C_Com_q : forall Defs ps C p e q x a HC HC', p <> q -> In q ps ->
  epp_C Defs ps (p#e-->q$x@a;;C) HC q = Recv Sig' p x a (epp_C Defs ps C HC' q).
Proof.
intros. rename a into A. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
rewrite DecType_eq, DecType_neq in p0; auto.
rewrite p1 in p0. induction x0; inversion p0.
2: case o, o0; try induction p2; try induction p3; inversion p0.
apply inject_inj in H5; rewrite H5; auto.
intro. exfalso. clear p0.
apply projectable_C_use' with (p:=q) in HC'; auto.
simpl. intro; exfalso.
revert b; rewrite DecType_eq, DecType_neq; auto. simpl.
rewrite Xmatch_elim. discriminate.
apply projectable_C_use' with ps; auto.
Qed.

Lemma epp_C_Com_r : forall Defs ps C p e q x a HC HC' r, p <> r -> q <> r ->
  epp_C Defs ps (p#e-->q$x@a;;C) HC r = epp_C Defs ps C HC' r.
Proof.
intros. rename a into A. unfold epp_C.
elim In_dec; intro; simpl; auto.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
do 2 rewrite DecType_neq in p0; auto.
rewrite p1 in p0. apply inject_inj; auto.
intro. exfalso. clear p0.
apply projectable_C_use' with (p:=r) in HC'; auto.
simpl. intro; exfalso.
revert b. rewrite DecType_neq; auto. rewrite DecType_neq; auto.
apply projectable_C_use' with ps; auto.
Qed.

Lemma epp_C_Sel_p : forall Defs ps C p q l a HC HC', In p ps ->
  epp_C Defs ps (p-->q[l]@a;;C) HC p = Sel Sig' q l a (epp_C Defs ps C HC' p).
Proof.
intros. rename a into A. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
repeat rewrite DecType_eq in p0.
rewrite p1 in p0; induction x, l; inversion p0.
1,2: apply inject_inj in H4; rewrite H4; auto.
1,2: case o, o0; try induction p2; try induction p3; inversion H1.
intro; exfalso; clear p0.
apply projectable_C_use' with (p:=p) in HC'; auto.
simpl. intro; exfalso.
revert b; repeat rewrite DecType_eq.
induction l; simpl; rewrite Xmatch_elim.
1,3: discriminate.
all: apply projectable_C_use' with ps; auto.
Qed.

Lemma epp_C_Sel_ql : forall Defs ps C p q a HC HC', p <> q -> In q ps ->
  epp_C Defs ps (p-->q[left]@a;;C) HC q = Branching Sig' p (Some (a,epp_C Defs ps C HC' q)) None.
Proof.
intros. rename a into A. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
rewrite DecType_eq, DecType_neq in p0; auto.
rewrite p1 in p0. induction x; inversion p0.
case o, o0; try induction p2; try induction p3; inversion p0.
apply inject_inj in H5; rewrite H5; auto.
intro. exfalso. clear p0.
apply projectable_C_use' with (p:=q) in HC'; auto.
simpl. intro; exfalso.
revert b; rewrite DecType_eq, DecType_neq; auto. simpl.
rewrite Xmatch_elim. discriminate.
apply projectable_C_use' with ps; auto.
Qed.

Lemma epp_C_Sel_qr : forall Defs ps C p q a HC HC', p <> q -> In q ps ->
  epp_C Defs ps (p-->q[right]@a;;C) HC q = Branching Sig' p None (Some (a,epp_C Defs ps C HC' q)).
Proof.
intros. rename a into A. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
rewrite DecType_eq, DecType_neq in p0; auto.
rewrite p1 in p0. induction x; inversion p0.
case o, o0; try induction p2; try induction p3; inversion p0.
apply inject_inj in H5; rewrite H5; auto.
intro. exfalso. clear p0.
apply projectable_C_use' with (p:=q) in HC'; auto.
simpl. intro; exfalso.
revert b; rewrite DecType_eq, DecType_neq; auto. simpl.
rewrite Xmatch_elim. discriminate.
apply projectable_C_use' with ps; auto.
Qed.

Lemma epp_C_Sel_r : forall Defs ps C p q l a HC HC' r, p <> r -> q <> r ->
  epp_C Defs ps (p-->q[l]@a;;C) HC r = epp_C Defs ps C HC' r.
Proof.
intros. rename a into A. unfold epp_C.
elim In_dec; intro; simpl; auto.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
do 4 rewrite DecType_neq in p0; auto.
rewrite p1 in p0. apply inject_inj; induction l; auto.
intro. exfalso. clear p0.
apply projectable_C_use' with (p:=r) in HC'; auto.
simpl. intro; exfalso.
do 4 rewrite DecType_neq in b; auto.
revert b; simpl.
induction l; apply projectable_C_use' with ps; auto.
Qed.

Lemma epp_C_Cond_p : forall Defs ps p b C1 C2 HC HC1 HC2, In p ps ->
  epp_C Defs ps (If p ?? b Then C1 Else C2) HC p
  = Cond Sig' b (epp_C Defs ps C1 HC1 p) (epp_C Defs ps C2 HC2 p).
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
+ rewrite DecType_eq in p0.
  apply inject_inj. simpl. rewrite <- p1, <- p2; auto.
+ intro; exfalso. rewrite DecType_eq in p0. revert p0.
  apply projectable_C_use' with (p:=p) in HC2; auto.
+ intro; exfalso. rewrite DecType_eq in p0. revert p0.
  apply projectable_C_use' with (p:=p) in HC1; auto.
+ intro; exfalso. rewrite DecType_eq in b0. revert b0.
  simpl; repeat rewrite Xmatch_elim.
  discriminate.
  apply projectable_C_use' with (p:=p) in HC2; auto.
  apply projectable_C_use' with (p:=p) in HC1; auto.
Qed.

Lemma epp_C_Cond_r : forall Defs ps p b C1 C2 HC HC1 HC2 r, p <> r ->
  inject (epp_C Defs ps (If p ?? b Then C1 Else C2) HC r)
  = epp_C Defs ps C1 HC1 r [\/] epp_C Defs ps C2 HC2 r.
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
+ revert p0. rewrite DecType_neq; auto; intros.
  rewrite p1, p2 in p0; auto.
+ intro; exfalso. rewrite DecType_neq in p0; auto. revert p0.
  apply projectable_C_use' with (p:=r) in HC2; auto.
+ intro; exfalso. rewrite DecType_neq in p0; auto. revert p0.
  apply projectable_C_use' with (p:=r) in HC1; auto.
+ intro; exfalso. apply projectable_C_use' with (p:=r) in HC; auto.
Qed.

(*
Lemma epp_C_Then_r : forall Defs ps p b C1 C2 HC HC1 HC2 r, p <> r ->
  epp_C Defs ps C1 HC1 r = epp_C Defs ps C2 HC2 r ->
  epp_C Defs ps (If p ?? b Then C1 Else C2) HC r = epp_C Defs ps C1 HC1 r.
Proof.
intros.
apply inject_inj. rewrite epp_C_Cond_r with (HC1:=HC1) (HC2:=HC2); auto.
rewrite H0. apply merge_idempotent.
Qed.

Lemma epp_C_Else_r : forall Defs ps p b C1 C2 HC HC1 HC2 r, p <> r ->
  epp_C Defs ps C1 HC1 r = epp_C Defs ps C2 HC2 r ->
  epp_C Defs ps (If p ?? b Then C1 Else C2) HC r = epp_C Defs ps C2 HC2 r.
Proof.
intros.
rewrite epp_C_Then_r with (HC1:=HC1) (HC2:=HC2); auto.
Qed.
*)

Lemma epp_C_Call : forall Defs ps X p HC, In p ps -> In p (fst (Defs X)) ->
  epp_C Defs ps (CC.Call X) HC p = Call Sig' (X,p).
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim collapse_char'. induction a0; simpl.
revert p0. elim In_dec; intros.
induction x; auto; inversion p0.
case o, o0; try induction p1; try induction p2; inversion p0.
auto. tauto.
intro. exfalso.
revert b. elim in_dec; discriminate.
Qed.

Lemma epp_C_Call_out : forall Defs ps X p HC, ~In p (fst (Defs X)) ->
  epp_C Defs ps (CC.Call X) HC p = End _.
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim collapse_char'. induction a0; simpl.
revert p0. elim In_dec; intros. tauto.
induction x; auto; inversion p0.
case o, o0; try induction p1; try induction p2; inversion p0.
intro. exfalso.
revert b. elim in_dec; discriminate.
Qed.

Lemma epp_C_RT_Call : forall Defs ps X p ps' C HC, In p ps -> In p ps' ->
  epp_C Defs ps (RT_Call X ps' C) HC p = Call Sig' (X,p).
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim collapse_char'. induction a0; simpl.
revert p0. elim In_dec; intros.
induction x; auto; inversion p0.
case o, o0; try induction p1; try induction p2; inversion p0.
auto. tauto.
intro. exfalso.
revert b. elim in_dec; auto. discriminate.
Qed.

Lemma epp_C_RT_Call_out : forall Defs ps X p ps' C HC HC', ~In p ps' ->
  epp_C Defs ps (RT_Call X ps' C) HC p = epp_C Defs ps C HC' p.
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim collapse_char'. induction a0; simpl.
elim collapse_char'. induction a0; simpl.
revert p0. elim In_dec; intros. tauto.
apply inject_inj; transitivity (bproj Defs C p); auto.
intro. exfalso.
revert p0. elim in_dec; auto.
intros. rewrite p0, collapse_inject in b.
eapply inject_not_undefined; eauto.
intro; exfalso. revert b.
elim In_dec; auto.
intros. apply projectable_C_use' with (p:=p) in HC'; auto.
Qed.

Lemma epp_C_End : forall Defs ps p HC,
  epp_C Defs ps CC.End HC p = End _.
Proof.
intros. unfold epp_C.
elim In_dec; intro; simpl. 2: tauto.
elim collapse_char'. induction a0; simpl.
induction x; auto; inversion p0.
case o, o0; try induction p1; try induction p2; inversion p0.
discriminate.
Qed.

(** Strange characterizations lemmas for branching. *)
Lemma bproj_not_Branching_None_None : forall Defs C r q,
  bproj Defs C r <> inject (q & None // None).
Proof.
intros. induction C; simpl. induction e. 2: induction t2.
1,2,3,4: elim eq_dec.
2,4,6: elim eq_dec.
12,13: elim In_dec.
all: auto.
all: try discriminate.
repeat intro.
apply Xmerge_inv_Branching in H; destroy H.
clear H4 H.
elim H2; auto. clear H2; intros.
elim H3; auto. clear H3; intros.
apply IHC1. rewrite H, H3 in H0; auto.
Qed.

Lemma epp_C_not_Branching_None_None : forall Defs ps C HC p q,
  epp_C Defs ps C HC p <> Branching Sig' q None None.
Proof.
intros.
unfold epp_C.
elim In_dec; intro; simpl. 2: discriminate.
elim collapse_char'; intro; simpl.
induction a0. intro. rewrite H in p0.
clear H x a HC ps.
revert p0. apply bproj_not_Branching_None_None.
exfalso. apply projectable_C_use' with (p:=p) in HC; auto.
Qed.

Lemma bproj_Sel_Branching_l : forall Defs C p q a Bp Bl Br,
  bproj Defs C p = @XSel Sig' q left a Bp ->
  bproj Defs C q = @XBranching Sig' p Bl Br -> Bl <> None /\ Br = None.
Proof.
induction C; simpl; intros; revert H H0; try discriminate.
rename t into a'. induction e. 2: induction t1.
1,2,3,4: case (eq_dec t p); intro; try discriminate.
1,2,3,4,5: case (eq_dec t q); intro; try discriminate.
1: case (eq_dec t1 p); intro; try discriminate.
1: case (eq_dec t1 q); intro; try discriminate.
3,4: case (eq_dec t0 p); intro; try discriminate.
2,3,4: case (eq_dec t0 q); intro; try discriminate.
9,10: elim in_dec; intro; try discriminate.
9: elim in_dec; intro; try discriminate.
all: eauto; intros.
+ inversion H0; split; auto. discriminate.
+ inversion H. exfalso; auto.
+ inversion H0; split; auto.
+ inversion H0. exfalso; auto.
+ apply Xmerge_inv_Sel in H. destroy H.
  rename x into B1, x0 into B2.
  apply Xmerge_inv_Branching in H0. destroy H0.
  rename x into B1l, x1 into B1r, x0 into B2l, x2 into B2r.
  elim (IHC1 _ _ _ _ _ _ H1 H3); intros.
  elim (IHC2 _ _ _ _ _ _ H2 H4); intros.
  split. intro. tauto.
  induction Br; auto.
  induction a0. eelim H0; eauto. intro. exfalso.
  apply H12 in H9. rewrite H9 in H11; inversion H11.
Qed.

Lemma epp_C_Sel_Branching_l : forall Defs ps C HC p q a Bp Bl Br,
  epp_C Defs ps C HC p = Sel Sig' q left a Bp ->
  epp_C Defs ps C HC q = Branching Sig' p Bl Br ->
  Bl <> None /\ Br = None.
Proof.
intros.
revert H H0. unfold epp_C.
elim In_dec. 2: discriminate.
elim In_dec. 2: discriminate.
elim (collapse_char'); intro Hc. induction Hc.
elim (collapse_char'); intro Hc. induction Hc.
simpl; intros.
rewrite H in p0; rewrite H0 in p1. simpl in p0.
induction Bl, Br; simpl in p1; try induction a2; try induction p2.
2: split; auto; discriminate.
1,2,3: elim (bproj_Sel_Branching_l _ _ _ _ _ _ _ _ p0 p1);
  simpl; intros. inversion H2. inversion H2. auto.
simpl. intro. exfalso. apply projectable_C_use' with (p:=q) in HC; auto.
simpl. intro. intro. exfalso. apply projectable_C_use' with (p:=p) in HC; auto.
Qed.

Lemma bproj_Sel_Branching_r : forall Defs C p q a Bp Bl Br,
  bproj Defs C p = @XSel Sig' q right a Bp ->
  bproj Defs C q = @XBranching Sig' p Bl Br -> Bl = None /\ Br <> None.
Proof.
induction C; simpl; intros; revert H H0; try discriminate.
rename t into a'. induction e. 2: induction t1.
1,2,3,4: case (eq_dec t p); intro; try discriminate.
1,2,3,4,5: case (eq_dec t q); intro; try discriminate.
1: case (eq_dec t1 p); intro; try discriminate.
1: case (eq_dec t1 q); intro; try discriminate.
2,4: case (eq_dec t0 p); intro; try discriminate.
2,3,4: case (eq_dec t0 q); intro; try discriminate.
9,10: elim in_dec; intro; try discriminate.
9: elim in_dec; intro; try discriminate.
all: eauto; intros.
+ inversion H0. exfalso; auto.
+ inversion H0; split; auto.
+ inversion H0; split; auto. discriminate.
+ inversion H. exfalso; auto.
+ apply Xmerge_inv_Sel in H. destroy H.
  rename x into B1, x0 into B2.
  apply Xmerge_inv_Branching in H0. destroy H0.
  rename x into B1l, x1 into B1r, x0 into B2l, x2 into B2r.
  elim (IHC1 _ _ _ _ _ _ H1 H3); intros.
  elim (IHC2 _ _ _ _ _ _ H2 H4); intros.
  split. 2: intro; tauto.
  induction Bl; auto.
  induction a0. eelim H7; eauto. intro. exfalso.
  apply H12 in H8. rewrite H8 in H10; inversion H10.
Qed.

Lemma epp_C_Sel_Branching_r : forall Defs ps C HC p q a Bp Bl Br,
  epp_C Defs ps C HC p = Sel Sig' q right a Bp ->
  epp_C Defs ps C HC q = Branching Sig' p Bl Br ->
  Bl = None /\ Br <> None.
Proof.
intros.
revert H H0. unfold epp_C.
elim In_dec. 2: discriminate.
elim In_dec. 2: discriminate.
elim (collapse_char'); intro Hc. induction Hc.
elim (collapse_char'); intro Hc. induction Hc.
simpl; intros.
rewrite H in p0; rewrite H0 in p1. simpl in p0.
induction Bl, Br; try induction a2; try induction p2; simpl in p1.
3: split; auto; discriminate.
1,2,3: elim (bproj_Sel_Branching_r _ _ _ _ _ _ _ _ p0 p1);
  simpl; intros. inversion H1. inversion H1. auto.
simpl. intro. exfalso. apply projectable_C_use' with (p:=q) in HC; auto.
simpl. intro. intro. exfalso. apply projectable_C_use' with (p:=p) in HC; auto.
Qed.

(** Strange inversion lemmas for conditionals. *)
Lemma epp_C_Cond_Send_inv : forall Defs ps p b C1 C2 HC HC1 HC2 r q e a B,
  epp_C Defs ps (If p ?? b Then C1 Else C2) HC r = Send Sig' q e a B ->
  exists B1 B2, epp_C Defs ps C1 HC1 r = Send Sig' q e a B1
  /\ epp_C Defs ps C2 HC2 r = Send Sig' q e a B2 /\ B1 [\/] B2 = inject B.
Proof.
intros.
assert (p <> r).
1: {
  intro. revert HC H; rewrite H0. intro.
  elim (In_dec (@eq_dec Pid) r ps); intro.
  rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2); auto. discriminate.
  rewrite epp_C_out; auto. discriminate.
}
generalize (epp_C_Cond_r _ _ _ _ _ _ HC HC1 HC2 _ H0); intros.
rewrite H in H1.
apply merge_inv_Send; auto.
Qed.

Lemma epp_C_Cond_Recv_inv : forall Defs ps p b C1 C2 HC HC1 HC2 r q x a B,
  epp_C Defs ps (If p ?? b Then C1 Else C2) HC r = Recv Sig' q x a B ->
  exists B1 B2, epp_C Defs ps C1 HC1 r = Recv Sig' q x a B1
  /\ epp_C Defs ps C2 HC2 r = Recv Sig' q x a B2 /\ B1 [\/] B2 = inject B.
Proof.
intros.
assert (p <> r).
1: {
  intro. revert HC H; rewrite H0. intro.
  elim (In_dec (@eq_dec Pid) r ps); intro.
  rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2); auto. discriminate.
  rewrite epp_C_out; auto. discriminate.
}
generalize (epp_C_Cond_r _ _ _ _ _ _ HC HC1 HC2 _ H0); intros.
rewrite H in H1.
apply merge_inv_Recv; auto.
Qed.

Lemma epp_C_Cond_Sel_inv : forall Defs ps p b C1 C2 HC HC1 HC2 r q l a B,
  epp_C Defs ps (If p ?? b Then C1 Else C2) HC r = Sel Sig' q l a B ->
  exists B1 B2, epp_C Defs ps C1 HC1 r = Sel Sig' q l a B1
  /\ epp_C Defs ps C2 HC2 r = Sel Sig' q l a B2 /\ B1 [\/] B2 = inject B.
Proof.
intros.
assert (p <> r).
1: {
  intro. revert HC H; rewrite H0. intro.
  elim (In_dec (@eq_dec Pid) r ps); intro.
  rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2); auto. discriminate.
  rewrite epp_C_out; auto. discriminate.
}
generalize (epp_C_Cond_r _ _ _ _ _ _ HC HC1 HC2 _ H0); intros.
rewrite H in H1.
apply merge_inv_Sel; auto.
Qed.

Lemma epp_C_Cond_Branching_l_inv : forall Defs ps p b C1 C2 HC HC1 HC2 r q a B,
  epp_C Defs ps (If p ?? b Then C1 Else C2) HC r = Branching Sig' q (Some (a,B)) None ->
  exists B1 B2, epp_C Defs ps C1 HC1 r = Branching Sig' q (Some (a,B1)) None
  /\ epp_C Defs ps C2 HC2 r = Branching Sig' q (Some (a,B2)) None /\ B1 [\/] B2 = inject B.
Proof.
intros.
assert (p <> r).
1: {
  intro. revert HC H; rewrite H0. intro.
  elim (In_dec (@eq_dec Pid) r ps); intro.
  rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2); auto. discriminate.
  rewrite epp_C_out; auto. discriminate.
}
generalize (epp_C_Cond_r _ _ _ _ _ _ HC HC1 HC2 _ H0); intros.
rewrite H in H1.
symmetry in H1. apply merge_inv_Branching_Some_None in H1.
inversion_clear H1; inversion_clear H2.
1: elim (epp_C_not_Branching_None_None _ _ _ _ _ _ H1).
1: inversion_clear H1. elim (epp_C_not_Branching_None_None _ _ _ _ _ _ H3).
destroy H1. eauto.
Qed.

Lemma epp_C_Cond_Branching_r_inv : forall Defs ps p b C1 C2 HC HC1 HC2 r q a B,
  epp_C Defs ps (If p ?? b Then C1 Else C2) HC r = Branching Sig' q None (Some (a,B)) ->
  exists B1 B2, epp_C Defs ps C1 HC1 r = Branching Sig' q None (Some (a,B1))
  /\ epp_C Defs ps C2 HC2 r = Branching Sig' q None (Some (a,B2)) /\ B1 [\/] B2 = inject B.
Proof.
intros.
assert (p <> r).
1: {
  intro. revert HC H; rewrite H0. intro.
  elim (In_dec (@eq_dec Pid) r ps); intro.
  rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2); auto. discriminate.
  rewrite epp_C_out; auto. discriminate.
}
generalize (epp_C_Cond_r _ _ _ _ _ _ HC HC1 HC2 _ H0); intros.
rewrite H in H1.
symmetry in H1. apply merge_inv_Branching_None_Some in H1.
inversion_clear H1; inversion_clear H2.
1: elim (epp_C_not_Branching_None_None _ _ _ _ _ _ H1).
1: inversion_clear H1. elim (epp_C_not_Branching_None_None _ _ _ _ _ _ H3).
destroy H1. eauto.
Qed.

Lemma epp_C_Cond_Cond_inv : forall Defs ps p b b' C1 C2 HC HC1 HC2 r Bt Be,
  epp_C Defs ps (If p ?? b Then C1 Else C2) HC r = Cond Sig' b' Bt Be ->
  p <> r -> exists B1t B1e B2t B2e,
    epp_C Defs ps C1 HC1 r = Cond Sig' b' B1t B1e
    /\ epp_C Defs ps C2 HC2 r = Cond Sig' b' B2t B2e
    /\ B1t [\/] B2t = inject Bt /\ B1e [\/] B2e = inject Be.
Proof.
intros.
generalize (epp_C_Cond_r _ _ _ _ _ _ HC HC1 HC2 _ H0); intros.
rewrite H in H1.
symmetry in H1. apply merge_inv_Cond in H1.
destroy H1.
change (x [\/] x0 = inject Bt) in H4.
change (x1 [\/] x2 = inject Be) in H1.
exists x, x1, x0, x2. repeat split; auto.
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
simpl. elim (XUndefined_dec _ B); auto.
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
elim (projectable_C_dec (Procedures _ P) ps (Main P)); intro HC.
2: right; intro; inversion_clear H; auto.
elim (projectable_D_dec Xs (Procedures _ P)); intro HD.
2: right; intro; destroy H; auto.
generalize (fun p => In_dec (@eq_dec Pid) p ps); intro.
elim (Forall_dec (fun p => In p ps)) with (CCC_pn (Main P) (fun _ => nil)); auto; intro Hps.
1: elim (Forall_dec (fun X => forall p, In p (CCC_pn (snd (Procedures _ P X)) (fun _ => nil)) -> In p ps)) with Xs; intro HXs1.
1: elim (Forall_dec (fun X => forall p, In p (fst (Procedures _ P X)) -> In p ps)) with Xs; intro HXs2.
+ left. rewrite Forall_forall in Hps, HXs1, HXs2.
  repeat split; eauto.
+ right; intro; apply HXs2.
  destroy H. rewrite Forall_forall; eauto.
+ elim (Forall_dec (fun p => In p ps)) with (fst (Procedures _ P HXs2)); auto.
  - left; rewrite Forall_forall in a; auto.
  - right; intro. apply b; rewrite Forall_forall; auto.
+ right; intro; apply HXs1.
  destroy H. rewrite Forall_forall; eauto.
+ elim (Forall_dec (fun p => In p ps)) with (CCC_pn (snd (Procedures _ P HXs1)) (fun _ => nil)); auto.
  - left. rewrite Forall_forall in a; eauto.
  - right; intro. apply b; rewrite Forall_forall; eauto.
+ right; intro; apply Hps.
  destroy H. rewrite Forall_forall; eauto.
Qed.

(** Inversion lemmas for projectability. *)
Lemma projectable_C_inv_Com : forall Defs ps p e q x a C,
  projectable_C Defs ps (p#e --> q$x@a;; C) -> projectable_C Defs ps C.
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
case eq_dec; [idtac | case eq_dec]; simpl; rewrite H5, H1; auto.
Qed.

Lemma projectable_C_inv_Sel : forall Defs ps p q l a C,
  projectable_C Defs ps (p --> q[l]@a;; C) -> projectable_C Defs ps C.
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
case l; (case eq_dec; [idtac | case eq_dec]); simpl; rewrite H5, H1; auto.
Qed.

Lemma projectable_C_inv_Eta : forall Defs ps eta a C,
  projectable_C Defs ps (eta@a;; C) -> projectable_C Defs ps C.
Proof.
intros; induction eta.
eapply projectable_C_inv_Com; eauto.
eapply projectable_C_inv_Sel; eauto.
Qed.

Lemma projectable_C_inv_Then : forall Defs ps p b C1 C2,
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
case eq_dec; simpl.
+ rewrite H5, H1; auto.
+ rewrite collapse_merge; auto. rewrite H5; auto.
Qed.

Lemma projectable_C_inv_Else : forall Defs ps p b C1 C2,
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
case eq_dec; simpl.
+ rewrite H5, H1. case (collapse (bproj Defs C1 r)); auto.
+ rewrite collapse_merge'; auto. rewrite H5; auto.
Qed.

(** The corresponding lemmas for RT_Call do not hold.
  Therefore, projectability is not preserved by reductions,
  so we need an auxiliary notion. *)
Fixpoint strongly_projectable Defs (C:Choreography Sig) (r:Pid) : Prop :=
match C with
| eta@a;; C'                => strongly_projectable Defs C' r
| If p ?? b Then C1 Else C2 => strongly_projectable Defs C1 r
     /\ strongly_projectable Defs C2 r
     /\ collapse (bproj Defs C r) <> XUndefined
| RT_Call X ps C            => strongly_projectable Defs C r /\
     (forall p, In p ps -> In p (fst (Defs X))
          /\ bproj Defs (snd (Defs X)) p [[>]] bproj Defs C p)
| _                         => True
end.

Lemma strongly_projectable_C : forall Defs C r,
  strongly_projectable Defs C r -> collapse (bproj Defs C r) <> XUndefined.
Proof.
induction C; simpl.
+ intro; induction e; elim eq_dec;
  [idtac | elim eq_dec | elim t2 | elim t2; elim eq_dec];
    auto; simpl; intros; try (rewrite Xmatch_elim; auto; discriminate).
+ intro; elim eq_dec; tauto.
+ intro; elim in_dec; discriminate.
+ intro; elim in_dec; auto. discriminate.
  intros. inversion_clear H; auto.
+ discriminate.
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
+ induction e.
  - apply projectable_C_inv_Com in H0; eauto.
  - apply projectable_C_inv_Sel in H0; eauto.
+ inversion_clear H. repeat split.
  - apply projectable_C_inv_Then in H0; eauto.
  - apply projectable_C_inv_Else in H0; eauto.
  - red in H0. rewrite Forall_forall in H0.
    generalize (H0 (r,collapse (bproj Defs (If t ?? t0 Then C1 Else C2) r))); intros.
    simpl in H; apply H.
    apply in_map_iff. exists r; auto.
+ inversion H.
Qed.

Lemma initial_strongly_projectable' : forall Defs C r, initial C ->
  ~In r (CCC_pn C (fun X => fst (Defs X))) -> strongly_projectable Defs C r.
Proof.
induction C; simpl; intros; auto.
+ apply IHC; auto. intro; apply H0. sup.
+ destroy H; repeat split.
  - apply IHC1; auto. intro; apply H0. sup; sup.
  - apply IHC2; auto. intro; apply H0. sup; sup.
  - revert H0. sup; sup; intros.
    repeat rewrite bproj_not_In; auto. elim eq_dec; discriminate.
+ destroy H.
Qed.

(** Inversion lemmas for strong projectability. *)
Lemma strongly_projectable_inv_Eta : forall Defs eta C a p,
  strongly_projectable Defs (eta@a;;C) p -> strongly_projectable Defs C p.
Proof. auto. Qed.

Lemma strongly_projectable_inv_Then : forall Defs p b C1 C2 r,
  strongly_projectable Defs (If p ?? b Then C1 Else C2) r ->
  strongly_projectable Defs C1 r.
Proof. intros. destroy H. auto. Qed.

Lemma strongly_projectable_inv_Else : forall Defs p b C1 C2 r,
  strongly_projectable Defs (If p ?? b Then C1 Else C2) r ->
  strongly_projectable Defs C2 r.
Proof. intros. destroy H. auto. Qed.

Lemma strongly_projectable_inv_RT_Call : forall Defs ps X C p,
  strongly_projectable Defs (RT_Call ps X C) p ->
  strongly_projectable Defs C p.
Proof. intros. destroy H. auto. Qed.

(** Inversion lemmas about program projectability. *)
Lemma projectable_inv_Eta : forall Xs ps Defs eta a C,
  projectable Xs ps (CC.Build_Program _ Defs (eta@a;;C)) ->
  projectable Xs ps (CC.Build_Program _ Defs C).
Proof.
intros.
destroy H; repeat split; auto.
apply projectable_C_inv_Eta with eta a; auto.
intros. apply H2; simpl. sup.
Qed.

Lemma projectable_inv_Com : forall Xs ps Defs p e q x a C,
  projectable Xs ps (CC.Build_Program _ Defs (p#e-->q$x@a;;C)) ->
  projectable Xs ps (CC.Build_Program _ Defs C).
Proof. intros; eapply projectable_inv_Eta; eauto. Qed.

Lemma projectable_inv_Sel : forall Xs ps Defs p q l a C,
  projectable Xs ps (CC.Build_Program _ Defs (p-->q[l]@a;;C)) ->
  projectable Xs ps (CC.Build_Program _ Defs C).
Proof. intros; eapply projectable_inv_Eta; eauto. Qed.

Lemma projectable_inv_Then : forall Xs ps Defs p b C1 C2,
  projectable Xs ps (CC.Build_Program _ Defs (If p ?? b Then C1 Else C2)) ->
  projectable Xs ps (CC.Build_Program _ Defs C1).
Proof.
intros.
destroy H; repeat split; auto.
apply projectable_C_inv_Then with p b C2; auto.
intros. apply H2; simpl. sup; sup.
Qed.

Lemma projectable_inv_Else : forall Xs ps Defs p b C1 C2,
  projectable Xs ps (CC.Build_Program _ Defs (If p ?? b Then C1 Else C2)) ->
  projectable Xs ps (CC.Build_Program _ Defs C2).
Proof.
intros.
destroy H; repeat split; auto.
apply projectable_C_inv_Else with p b C1; auto.
intros. apply H2; simpl. sup; sup.
Qed.

Lemma projectable_inv_RT_Call : forall Xs ps Defs X p ps' C,
  projectable Xs ps (CC.Build_Program _ Defs (RT_Call X ps' C)) ->
  collapse (bproj Defs C p) <> XUndefined ->
  projectable Xs ps (CC.Build_Program _ Defs (RT_Call X (set_remove_pid _ p ps') C)).
Proof.
intros.
destroy H; repeat split; auto.
+ clear H H4 H3 H2.
  intros. red; red in H1.
  rewrite Forall_forall; rewrite Forall_forall in H1.
  intros. induction x as (r,B). intro.
  apply (H1 (r,XUndefined)); auto.
  unfold epp_list in H; rewrite in_map_iff in H.
  unfold epp_list; rewrite in_map_iff.
  destroy H. inversion H3.
  rewrite H5 in H. simpl in H2. clear x H5 H3.
  exists r; simpl. split; auto.
  revert H6. case In_dec; case In_dec; simpl; intros.
  - rewrite H6, H2; auto.
  - elim n; eapply set_remove'_1; eauto.
  - rewrite H2 in H6. elim H0.
    rewrite <- (set_remove'_out (@eq_dec Pid) r p ps'); auto.
  - rewrite H6, H2; auto.
+ intro r. simpl; sup.
  intros. apply H3; simpl. sup.
  elim H5; auto.
  left. eapply set_remove'_1; eauto.
Qed.

(** Miscellaneous. *)
Lemma CCC_To_Call_ann : forall Defs C s X p C' s',
  CCC_To _ Defs C s (R_Call X p) C' s' ->
  strongly_projectable Defs C p -> In p (fst (Defs X)).
Proof.
induction C; intros; inversion H; eauto;
  try (destroy H0; eauto).
all: rewrite <- H4; elim (H0 p); auto.
Qed.

Lemma Program_WF_Defs_strongly_projectable : forall Xs ps P,
  CC.Program_WF _ Xs P -> projectable Xs ps P -> well_ann _ P ->
  forall X p, In X Xs -> In p ps -> strongly_projectable (Procedures _ P) (CC.Procs P X) p.
Proof.
intros. destroy H.
elim (H X); auto.
intros. clear H; destroy H8.
destroy H0.
elim (In_dec (@eq_dec Pid) p (Vars P X)); intros.
+ apply initial_strongly_projectable with (Vars P X); auto.
  red in H11. rewrite Forall_forall in H11. apply H11; auto.
+ apply initial_strongly_projectable'; auto.
  intro; apply b, H1. auto.
Qed.

End Projectability.

Section EPP_Theorem.

(** ** The EPP Theorem
  Lemmas about reduction and projection. *)

 Lemma CCC_To_bproj_Com_p : forall Defs C s C' s' p q v x,
  strongly_projectable Defs C p ->
  CCC_To _ Defs C s (R_Com p v q x) C' s' ->
  exists e a Bp, bproj Defs C p = @XSend Sig' q e a Bp /\ bproj Defs C' p = Bp
    /\ v = eval_on_state Ev e s p.
Proof.
intros.
rename H into HC, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ unfold v1. rewrite <- H5. rewrite H5, H7, H8 in H2. rename e0 into e', t into a'.
  simpl; rewrite DecType_eq.
  exists e', a', (bproj Defs C' p0); auto.
+ elim IHC with C'0; auto.
  clear C' H5 s'0 H6 ann H0 t0 H4 s0 H2 C0 H3 eta H1 H8 H.
  rename C'0 into C'; intros.
  destroy H. rewrite <- H1 in H0.
  induction e; try (case t2); destroy H7; destroy H2; simpl; repeat split.
  all: do 4 (rewrite DecType_neq; auto); repeat eexists; eauto.
+ clear H s'0 H7 C' H6 s0 H3 C3 H4 C0 H2 b H1 p0 H0 t1 H5.
  rename t into p', t0 into b. inversion_clear H8.
  elim IHC1 with C1'; auto. 2: apply HC.
  elim IHC2 with C2'; auto. 2: apply HC.
  clear IHC1 IHC2 H9 H10; intros.
  destroy H1; destroy H2.
  rename x0 into e, x1 into e', x2 into a, x3 into B2, x4 into a', x5 into B1.
  apply strongly_projectable_C with (r:=p) in HC; auto.
  revert HC; simpl. rewrite DecType_neq; auto.
  rewrite H2, H3, H4, H5, H6; simpl. rewrite eqb_refl.
  case eqb; simpl. 2: intros; elim HC; auto.
  case eqb; simpl. 2: intros; elim HC; auto.
  exists e', a', (B1 [[\/]] B2); repeat split; auto.
  rewrite Xmatch_elim; auto.
  intro. rewrite H7 in HC; auto.
  rewrite DecType_neq; auto.
+ elim IHC with C'0; auto; intros.
  2: apply HC; auto.
  apply disjoint_ps_Com in H7.
  destroy H9. rewrite <- H11 in H10.
  simpl. elim in_dec; intros.
  elim (disjoint_not_in_fst _ _ _ H7 p); simpl; auto.
  repeat eexists; eauto.
Qed.

Lemma CCC_To_bproj_Com_q : forall Defs C s C' s' p q v x,
  strongly_projectable Defs C q ->
  CCC_To _ Defs C s (R_Com p v q x) C' s' -> p <> q ->
  exists a Bq, bproj Defs C q = @XRecv Sig' p x a Bq /\ bproj Defs C' q = Bq.
Proof.
intros.
rename H into HC, H1 into Hpq, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ rewrite <- H4. rewrite H5, H7, H8 in H2. rename e0 into e'.
  simpl; repeat split. rewrite DecType_neq, DecType_eq; auto.
  exists t, (bproj Defs C q); auto.
+ elim IHC with C'0; auto.
  intros; destroy H0.
  induction e; try (case t3); destroy H7; destroy H10; simpl; repeat split.
  all: do 4 (rewrite DecType_neq; auto); eauto.
+ clear H s'0 H7 C' H6 s0 H3 C3 H4 C0 H2 b H1 p0 H0 t1 H5.
  rename p into p', t into p, t0 into b. inversion_clear H8.
  elim IHC1 with C1'; auto. 2: apply HC.
  elim IHC2 with C2'; auto. 2: apply HC.
  clear IHC1 IHC2 H9 H10; intros.
  destroy H1; destroy H2.
  rename x0 into a, x1 into a', x2 into B2, x3 into B1.
  simpl.
  apply strongly_projectable_C with (r:=q) in HC; auto.
  revert HC. simpl; rewrite DecType_neq; auto.
  rewrite H1, H2, H3, H4. simpl. repeat rewrite eqb_refl.
  elim eqb; simpl. 2: intro H'; elim H'; auto.
  exists a', (B1 [[\/]] B2); split; auto.
  rewrite Xmatch_elim; auto.
  intro. rewrite H5 in HC; auto.
  rewrite DecType_neq; auto.
+ elim IHC with C'0; auto; intros.
  2: apply HC; auto.
  apply disjoint_ps_Com in H7.
  destroy H9. simpl.
  elim in_dec; intros; eauto.
  elim (disjoint_not_in_snd _ _ _ H7 q); simpl; auto.
Qed.

Lemma CCC_To_bproj_Com_r : forall Defs C s C' s' p q v x r,
  strongly_projectable Defs C r ->
  CCC_To _ Defs C s (R_Com p v q x) C' s' ->
  p <> r -> q <> r -> bproj Defs C' r = bproj Defs C r.
Proof.
intros.
rename H into HC, H1 into Hpr, H2 into Hqr, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ rewrite <- H4. rewrite H5, H7, H8 in H2. rename e0 into e'.
  simpl; repeat split. repeat (rewrite DecType_neq; auto).
+ simpl; rewrite IHC; auto.
+ simpl. destroy HC.
  rewrite (IHC1 H11 C1'), (IHC2 H12 C2'); auto.
+ simpl. rewrite IHC; auto.
  apply HC.
Qed.

Lemma CCC_To_bproj_Sel_p : forall Defs C s C' s' p q l,
  strongly_projectable Defs C p ->
  CCC_To _ Defs C s (R_Sel p q l) C' s' ->
  exists a Bp, bproj Defs C p = @XSel Sig' q l a Bp /\ bproj Defs C' p = Bp.
Proof.
intros.
rename H into HC, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ rewrite <- H4. rewrite H5, H6, H7 in H2.
  simpl; repeat split. repeat rewrite DecType_eq.
  exists t, (bproj Defs C p); case l; auto.
+ elim IHC with C'0; auto; intros.
  induction e; try (case t3); destroy H7; destroy H10; simpl.
  all: repeat (rewrite DecType_neq; auto); eauto.
+ clear H s'0 H7 C' H6 s0 H3 C3 H4 C0 H2 b H1 p0 H0 t1 H5.
  rename p into p', t into p, t0 into b. inversion_clear H8.
  elim IHC1 with C1'; auto. 2: apply HC.
  elim IHC2 with C2'; auto. 2: apply HC.
  clear IHC1 IHC2 H9 H10; intros.
  destroy H1; destroy H2.
  rename x into a, x0 into a', x1 into B2, x2 into B1.
  simpl. apply strongly_projectable_C with (r:=p') in HC; auto.
  revert HC. simpl. repeat (rewrite DecType_neq; auto).
  rewrite H1, H2, H3, H4; simpl. repeat rewrite eqb_refl.
  elim eqb. 2: intro H'; elim H'; auto.
  exists a', (B1 [[\/]] B2); auto.
  rewrite Xmatch_elim; auto.
  intro. rewrite H5 in HC; auto.
+ elim IHC with C'0; auto; intros.
  2: apply HC; auto.
  apply disjoint_ps_Sel in H7.
  destroy H9. simpl.
  elim in_dec; intros; eauto.
  elim (disjoint_not_in_fst _ _ _ H7 p); simpl; auto.
Qed.

Lemma CCC_To_bproj_Sel_ql : forall Defs C s C' s' p q,
  strongly_projectable Defs C q ->
  CCC_To _ Defs C s (R_Sel p q left) C' s' -> p <> q ->
  exists a Bq, bproj Defs C q = @XBranching Sig' p (Some (a,Bq)) None /\ bproj Defs C' q = Bq.
Proof.
intros.
rename H into HC, H1 into Hpq, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ rewrite <- H4. rewrite H5, H6, H7 in H2.
  simpl; repeat split. rewrite DecType_eq, DecType_neq; auto.
  exists t, (bproj Defs C q); auto.
+ elim IHC with C'0; auto; intros.
  induction e; try (case t3); destroy H7; destroy H10; simpl.
  all: repeat (rewrite DecType_neq; auto); eauto.
+ clear H s'0 H7 C' H6 s0 H3 C3 H4 C0 H2 b H1 p0 H0 t1 H5.
  rename p into p', t into p, t0 into b. inversion_clear H8.
  elim IHC1 with C1'; auto. 2: apply HC.
  elim IHC2 with C2'; auto. 2: apply HC.
  clear IHC1 IHC2 H9 H10; intros.
  destroy H2; destroy H1.
  rename x into a, x0 into a', x1 into B1, x2 into B2.
  simpl. apply strongly_projectable_C with (r:=q) in HC; auto.
  revert HC. simpl. repeat (rewrite DecType_neq; auto).
  rewrite H1, H2, H3, H4. simpl. rewrite eqb_refl.
  elim eqb. 2: intro H'; elim H'; auto.
  exists a', (B1 [[\/]] B2).
  rewrite Xmatch_elim; auto.
  intro. rewrite H5 in HC; auto.
+ elim IHC with C'0; auto; intros.
  2: apply HC; auto.
  apply disjoint_ps_Sel in H7.
  destroy H9; simpl.
  elim in_dec; intros; eauto.
  elim (disjoint_not_in_snd _ _ _ H7 q); simpl; auto.
Qed.

Lemma CCC_To_bproj_Sel_qr : forall Defs C s C' s' p q,
  strongly_projectable Defs C q ->
  CCC_To _ Defs C s (R_Sel p q right) C' s' -> p <> q ->
  exists a Bq, bproj Defs C q = @XBranching Sig' p None (Some (a,Bq)) /\ bproj Defs C' q = Bq.
Proof.
intros.
rename H into HC, H1 into Hpq, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ rewrite <- H4. rewrite H5, H6, H7 in H2.
  simpl; repeat split. rewrite DecType_eq, DecType_neq; auto.
  exists t, (bproj Defs C q); auto.
+ elim IHC with C'0; auto; intros.
  induction e; try (case t3); destroy H7; destroy H10; simpl.
  all: repeat (rewrite DecType_neq; auto); eauto.
+ clear H s'0 H7 C' H6 s0 H3 C3 H4 C0 H2 b H1 p0 H0 t1 H5.
  rename p into p', t into p, t0 into b. inversion_clear H8.
  elim IHC1 with C1'; auto. 2: apply HC.
  elim IHC2 with C2'; auto. 2: apply HC.
  clear IHC1 IHC2 H9 H10; intros.
  destroy H2; destroy H1.
  rename x into a, x0 into a0, x1 into B1, x2 into B2.
  simpl. apply strongly_projectable_C with (r:=q) in HC; auto.
  revert HC. simpl. repeat (rewrite DecType_neq; auto).
  rewrite H1, H2, H3, H4. simpl. rewrite eqb_refl.
  elim eqb. 2: intro H'; elim H'; auto.
  exists a0, (B1 [[\/]] B2).
  rewrite Xmatch_elim; auto.
  intro. rewrite H5 in HC; auto.
+ elim IHC with C'0; auto; intros.
  2: apply HC; auto.
  apply disjoint_ps_Sel in H7.
  destroy H9; simpl.
  elim in_dec; intros; eauto.
  elim (disjoint_not_in_snd _ _ _ H7 q); simpl; auto.
Qed.

Lemma CCC_To_bproj_Sel_r : forall Defs C s C' s' p q l r,
  strongly_projectable Defs C r ->
  CCC_To _ Defs C s (R_Sel p q l) C' s' ->
  p <> r -> q <> r -> bproj Defs C' r = bproj Defs C r.
Proof.
intros.
rename H into HC, H1 into Hpr, H2 into Hqr, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ rewrite <- H4. rewrite H5, H6, H7 in H2.
  simpl; repeat split; repeat (rewrite DecType_neq; auto).
  case l; auto.
+ induction e; try (case t3); simpl.
  all: case (eq_dec t1 r); intros.
  1,3,5: rewrite IHC; auto.
  1: case (eq_dec t3 r); auto.
  2,3: case (eq_dec t2 r); auto.
  all: rewrite IHC; auto.
+ simpl. destroy HC. rewrite (IHC1 H11 C1'), (IHC2 H12 C2'); auto.
+ simpl. rewrite IHC; auto. apply HC.
Qed.

Lemma CCC_To_bproj_Cond_p : forall Defs C s C' s' p,
  strongly_projectable Defs C p ->
  CCC_To _ Defs C s (R_Cond p) C' s' ->
  exists b Bt Be, bproj Defs C p = @XCond Sig' b Bt Be
    /\ (eval_on_state BEv b s p = true -> bproj Defs C' p = Bt)
    /\ (eval_on_state BEv b s p = false -> bproj Defs C' p = Be).
Proof.
intros.
rename H into HC, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ elim IHC with C'0; intros; auto.
  destroy H9. rename x into b, x0 into Bt, x1 into Be.
  induction e; destroy H7; simpl in H12, H7.
  all: exists b, Bt, Be; repeat split.
  all: simpl.
  4,5,6: case t3.
  all: repeat (rewrite DecType_neq; auto).
+ rewrite H6 in HC. rewrite <- H5.
  clear s'0 H7 C' H5 p0 H6 s0 H2 C3 H4 C0 H3 b H1 p0 H0 H IHC1 IHC2.
  apply strongly_projectable_C in HC; revert HC.
  simpl. rewrite DecType_eq; simpl.
  elim (collapse_char' _ (bproj Defs C1 p)); intro HC1.
  2: rewrite HC1; intro; elim HC; auto.
  inversion_clear HC1. rename x into B1.
  rewrite Xmatch_elim. 2: rewrite H, collapse_inject; apply inject_not_undefined.
  elim (collapse_char' _ (bproj Defs C2 p)); intro HC2.
  2: rewrite HC2; intro HC; elim HC; auto.
  inversion_clear HC2. rename x into B2.
  rewrite Xmatch_elim. 2: rewrite H0, collapse_inject; apply inject_not_undefined.
  intros.
  exists t0, (bproj Defs C1 p), (bproj Defs C2 p); repeat split; auto.
  intro. unfold CC.BEv in H9; unfold BEv in H1.
  rewrite H9 in H1; inversion H1.
+ rewrite H6 in HC. rewrite <- H5.
  clear s'0 H7 C' H5 p0 H6 s0 H2 C3 H4 C0 H3 b H1 p0 H0 H IHC1 IHC2.
  apply strongly_projectable_C in HC; revert HC.
  simpl. rewrite DecType_eq; simpl.
  elim (collapse_char' _ (bproj Defs C1 p)); intro HC1.
  2: rewrite HC1; intro HC; elim HC; auto.
  inversion_clear HC1. rename x into B1.
  rewrite Xmatch_elim. 2: rewrite H, collapse_inject; apply inject_not_undefined.
  elim (collapse_char' _ (bproj Defs C2 p)); intro HC2.
  2: rewrite HC2; intro HC; elim HC; auto.
  inversion_clear HC2. rename x into B2.
  rewrite Xmatch_elim. 2: rewrite H0, collapse_inject; apply inject_not_undefined.
  intros.
  exists t0, (bproj Defs C1 p), (bproj Defs C2 p); repeat split; auto.
  intro. unfold CC.BEv in H9; unfold BEv in H1.
  rewrite H9 in H1; inversion H1.
+ clear s'0 H7 C' H6 t1 H5 s0 H3 C3 H4 C0 H2 b H1 p0 H0 H.
  elim IHC1 with C1'; auto. 2: apply HC.
  elim IHC2 with C2'; auto. 2: apply HC.
  clear IHC1 IHC2 H9 H10. intros.
  destroy H; destroy H0. simpl in H8.
  rename x into b2, x1 into Bt2, x2 into Be2.
  rename x0 into b1, x3 into Bt1, x4 into Be1.
  apply strongly_projectable_C in HC; revert HC.
  simpl. do 2 (rewrite DecType_neq; auto).
  rewrite H3, H1.
  intros.
  elim (XUndefined_dec _ (XCond b1 Bt1 Be1 [[\/]] XCond b2 Bt2 Be2)); intros.
  1: rewrite a in HC; elim HC; auto.
  revert HC; simpl. case_eq (eqb BExpr b1 b2).
  2: intros; elim HC; auto.
  intro.
  rename b1 into b'; rewrite eqb_eq in H5; rewrite <- H5 in *; clear b2 H5.
  intro; clear HC.
  exists b', (Bt1 [[\/]] Bt2), (Be1 [[\/]] Be2); repeat split.
  rewrite <- Xmerge_Cond_inv; simpl. rewrite eqb_refl; auto.
  1,2: intro; apply b; simpl; rewrite H5, eqb_refl; auto.
  case (Bt1 [[\/]] Bt2); auto.
  intros. rewrite H4, H2; auto.
  intros. rewrite H, H0; auto.
+ elim IHC with C'0; auto.
  2: apply HC.
  intros. destroy H9. rename x into b, x0 into Bt, x1 into Be.
  apply disjoint_ps_Cond in H7.
  simpl. elim in_dec. intro; elim H7; auto.
  exists b, Bt, Be; repeat split; auto.
Qed.

Lemma CCC_To_bproj_Cond_r : forall Defs C s C' s' p r,
  strongly_projectable Defs C r ->
  CCC_To _ Defs C s (R_Cond p) C' s' ->
  p <> r -> bproj Defs C r [[>]] bproj Defs C' r.
Proof.
intros.
rename H into HC, H1 into Hpr, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ clear s'0 H6 C' H5 t0 H4 s0 H2 C0 H3 eta H1 ann H0 H.
  elim IHC with C'0; intros; auto.
  rename C'0 into C'; clear IHC H8.
  destroy H.
  induction e; try (case t2); destroy H7; simpl in H2, H7.
  all: simpl.
  all: elim eq_dec; auto.
  2,4,6: elim eq_dec; auto.
  all: rewrite H0, H1; rename x into B, x0 into B'; intros.
  3,5,7: exists B, B'; auto.
  - exists (Send Sig' t2 t1 t B), (Send Sig' t2 t1 t B'); repeat split; auto.
    constructor; auto.
  - exists (Recv Sig' t0 t3 t B), (Recv Sig' t0 t3 t B'); repeat split; auto.
    constructor; auto.
  - exists (Branching Sig' t0 (Some (t,B)) None), (Branching Sig' t0 (Some (t,B')) None); repeat split; auto.
    apply MB_Branching_Some_None with (Sig:=Sig'); auto.
  - exists (Branching Sig' t0 None (Some (t,B))), (Branching Sig' t0 None (Some (t,B'))); repeat split; auto.
    apply MB_Branching_None_Some with (Sig:=Sig'); auto.
  - exists (Sel Sig' t1 left t B), (Sel Sig' t1 left t B'); repeat split; auto.
    constructor; auto.
  - exists (Sel Sig' t1 right t B), (Sel Sig' t1 right t B'); repeat split; auto.
    constructor; auto.
+ rewrite H6 in HC. rewrite <- H5.
  clear s'0 H7 C' H5 p0 H6 s0 H2 C3 H4 C0 H3 b H1 p0 H0 H IHC1 IHC2.
  apply strongly_projectable_C in HC; revert HC.
  simpl. rewrite DecType_neq; auto.
  intro. apply collapse_exists in HC. destroy HC.
  rename x into B.
  elim (Xmerge_inv _ _ _ _ HC); intros. destroy H.
  rename x into B1, x0 into B2.
  exists B, B1.
  repeat split; auto.
  apply merge_is_upper_bound with B2; auto.
+ rewrite H6 in HC. rewrite <- H5.
  clear s'0 H7 C' H5 p0 H6 s0 H2 C3 H4 C0 H3 b H1 p0 H0 H IHC1 IHC2.
  apply strongly_projectable_C in HC; revert HC.
  simpl. rewrite DecType_neq; auto.
  intro. apply collapse_exists in HC. destroy HC.
  rename x into B.
  elim (Xmerge_inv _ _ _ _ HC); intros. destroy H.
  rename x into B1, x0 into B2.
  exists B, B2.
  repeat split; auto.
  apply merge_is_upper_bound' with B1; auto.
+ clear s'0 H7 C' H6 t1 H5 s0 H3 C3 H4 C0 H2 b H1 p0 H0 H.
  elim IHC1 with C1'; auto. 2: apply HC.
  elim IHC2 with C2'; auto. 2: apply HC.
  clear IHC1 IHC2 H9 H10. intros.
  destroy H; destroy H0. simpl in H8.
  intros. simpl. case (eq_dec t r).
  * rewrite H1, H2, H3, H4.
    exists (Cond Sig' t0 x0 x), (Cond Sig' t0 x2 x1); simpl.
    repeat split; auto.
    constructor; auto.
  * intros.
    apply strongly_projectable_C in HC; revert HC.
    simpl; rewrite DecType_neq; auto. intro.
    elim (collapse_exists _ _ HC); intros; clear HC.
    rewrite H3, H1 in H5. fold (x0 [\/] x) in H5.
    elim (more_branches_merge_extend _ _ _ _ _ _ H0 H H5).
    intros. destroy H6.
    exists x3, x4; repeat split; auto.
    rewrite H3, H1; auto. rewrite H2, H4; auto.
+ elim IHC with C'0; auto.
  2: apply HC.
  intros. destroy H9.
  apply disjoint_ps_Cond in H7.
  simpl. elim in_dec; intros; auto.
  apply Xmore_branches_refl with (Call Sig' (t,r)); auto.
  rewrite H10, H11. exists x, x0; auto.
Qed.

Lemma CCC_To_bproj_Call_p : forall Defs C s C' s' p X Xs,
  strongly_projectable Defs C p ->
  (forall Y, In Y Xs -> strongly_projectable Defs (snd (Defs Y)) p) ->
  (forall Y, set_incl_pid (CCC_pn (snd (Defs Y)) (fun X => fst (Defs X))) (fst (Defs Y))) ->
  In X Xs ->
  CCC_To _ Defs C s (R_Call X p) C' s' ->
  bproj Defs C p = @XCall Sig' (X,p) /\ bproj Defs (snd (Defs X)) p [[>]] bproj Defs C' p.
Proof.
intros.
rename H into HC, H0 into HDefs, H2 into HX, H1 into Hnames, H3 into H.
revert C' H.
induction C; intros; inversion H.
+ elim IHC with C'0; auto.
  induction e; try (case t3); destroy H7; simpl in H9, H7; simpl.
  1,2,3: repeat (rewrite DecType_neq; auto).
+ clear H s'0 H7 C' H6 s0 H3 C3 H4 C0 H2 b H1 p0 H0 t1 H5.
  destroy HC. rename H into HC', H0 into HC''.
  rename p into p', t into p, t0 into b. simpl in H8.
  elim IHC1 with C1'; auto.
  elim IHC2 with C2'; auto.
  clear IHC1 IHC2 H9 H10; intros.
  simpl; rewrite H, H1, DecType_neq, DecType_neq; auto; repeat split.
  apply Xmerge_idempotent; discriminate.
  destroy H0; destroy H2.
  rewrite H3 in H5. apply inject_inj in H5. rewrite <- H5 in H2.
  elim (more_branches_has_lub _ _ _ _ H2 H0); intros. destroy H7.
  exists x, x3; repeat split; auto.
  rewrite H4, H6; unfold merge in H9; auto.
+ split; auto.
  simpl; elim in_dec; auto. tauto.
  generalize (strongly_projectable_C _ _ _ (HDefs X HX)); intros.
  elim (collapse_exists _ _ H9); intros.
  apply Xmore_branches_refl with x; auto.
+ simpl; split.
  - elim in_dec; auto. tauto.
  - elim in_dec; auto.
    intros. apply set_remove'_2 in a. elim a; auto.
    generalize (strongly_projectable_C _ _ _ (HDefs X HX)); intros.
    elim (collapse_exists _ _ H9); intros.
    apply Xmore_branches_refl with x; auto.
+ simpl. elim in_dec; auto.
  - apply disjoint_ps_Call in H7. tauto.
  - intros. apply IHC; auto. apply HC.
+ simpl; split.
  - elim in_dec; auto. tauto.
  - elim in_dec; auto.
    intro. apply set_remove'_2 in a. elim a; auto.
    intros. rewrite <- H3. apply HC; auto.
+ simpl; split.
  - elim in_dec; auto. tauto.
  - rewrite <- H5, <- H3. apply HC; auto.
Qed.

Lemma CCC_To_bproj_Call_r : forall Defs C s C' s' p X r,
  (forall X, set_incl_pid (CCC_pn (snd (Defs X)) (fun Y => fst (Defs Y))) (fst (Defs X))) ->
  CCC_To _ Defs C s (R_Call X p) C' s' ->
  p <> r -> bproj Defs C' r = bproj Defs C r.
Proof.
intros.
rename H into HDefs, H1 into Hpr, H0 into H.
revert C' H.
induction C; intros; inversion H.
+ simpl. rewrite IHC; auto.
+ simpl. rewrite (IHC1 C1'), (IHC2 C2'); auto.
+ simpl. elim in_dec; auto.
  intros; elim Hpr. apply set_size_1 with (@eq_dec Pid) (fst (Defs X)); auto.
  intro. apply bproj_not_In.
  intro; apply b, HDefs; auto.
+ simpl. elim in_dec; elim in_dec; auto; intros.
  elim b. eapply set_remove'_1; eauto.
  elim b. apply set_remove'_3; auto.
  apply bproj_not_In. intro; apply b, HDefs; auto.
+ simpl. rewrite IHC with C'0; auto.
+ simpl. elim in_dec; elim in_dec; auto; intros.
  elim b. eapply set_remove'_1; eauto.
  elim b. apply set_remove'_3; auto.
+ simpl. elim in_dec; auto.
  intros. elim Hpr. apply set_size_1 with (@eq_dec Pid) l; auto.
Qed.

Lemma CCC_To_bproj_disjoint : forall Defs C s tl C' s' ps p,
  (forall X, set_incl_pid (CCC_pn (snd (Defs X)) (fun Y => fst (Defs Y))) (fst (Defs X))) ->
  (forall r, In r ps -> strongly_projectable Defs C r) -> In p ps ->
  disjoint_p_rl p tl -> CCC_To _ Defs C s tl C' s' ->
  bproj Defs C p [[>]] bproj Defs C' p.
Proof.
do 7 intro. intros r HDefs.
intros. induction tl.
- destroy H1.
  rewrite (CCC_To_bproj_Com_r Defs C s C' s' p q v x); auto.
  apply strongly_projectable_C' in H.
  apply projectable_C_use with (p:=r) in H; auto.
  destroy H. apply Xmore_branches_refl with x0, collapse_inv; auto.
- destroy H1.
  rewrite (CCC_To_bproj_Sel_r Defs C s C' s' p q l); auto.
  apply strongly_projectable_C' in H.
  apply projectable_C_use with (p:=r) in H; auto.
  destroy H. apply Xmore_branches_refl with x, collapse_inv; auto.
- apply (CCC_To_bproj_Cond_r Defs C s C' s' p r); auto.
- rewrite (CCC_To_bproj_Call_r Defs C s C' s' p X); auto.
  apply strongly_projectable_C' in H.
  apply projectable_C_use with (p:=r) in H; auto.
  destroy H. apply Xmore_branches_refl with x, collapse_inv; auto.
Qed.

(** Projectability of well-formed programs is preserved by reductions. *)
Lemma CCC_To_projectable_C_Com : forall Defs ps C s C' s' p v q x,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  CCC_To _ Defs C s (R_Com p v q x) C' s' ->
  projectable_C Defs ps C'.
Proof.
intros.
red. rewrite Forall_forall; intro.
induction x0 as (r,B). unfold epp_list; rewrite in_map_iff.
simpl; intros. destroy H1. inversion H2.
rewrite H4 in H1; clear x0 H4 H2 B H5.
generalize (strongly_projectable_C _ _ _ (H _ H1)); intro.
elim ((@eq_dec Pid) p r); intro Hpr. 2: elim ((@eq_dec Pid) q r); intro Hqr.
+ rewrite Hpr in H0; clear p Hpr.
  elim (CCC_To_bproj_Com_p _ _ _ _ _ _ _ _ _ (H _ H1) H0).
  intros. destroy H3. intro.
  rewrite H4 in H2. simpl in H2.
  rewrite <- H5, H6 in H2. auto.
+ rewrite Hqr in H0; clear q Hqr.
  elim (CCC_To_bproj_Com_q _ _ _ _ _ _ _ _ _ (H _ H1) H0); auto.
  intros. destroy H3. intro.
  rewrite H4 in H2. simpl in H2.
  rewrite <- H3, H5 in H2. auto.
+ rewrite (CCC_To_bproj_Com_r _ _ _ _ _ _ _ _ _ _ (H _ H1) H0); auto.
Qed.

Lemma CCC_To_projectable_C_Sel : forall Defs ps C s C' s' p q l,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  CCC_To _ Defs C s (R_Sel p q l) C' s' ->
  projectable_C Defs ps C'.
Proof.
intros.
red. rewrite Forall_forall; intro.
induction x as (r,B). unfold epp_list; rewrite in_map_iff.
simpl; intros. destroy H1. inversion H2.
rewrite H4 in H1; clear x H4 H2 B H5.
generalize (strongly_projectable_C _ _ _ (H _ H1)); intro.
elim ((@eq_dec Pid) p r); intro Hpr. 2: elim ((@eq_dec Pid) q r); intro Hqr.
+ rewrite Hpr in H0; clear p Hpr.
  elim (CCC_To_bproj_Sel_p _ _ _ _ _ _ _ _ (H _ H1) H0).
  intros. destroy H3. intro.
  rewrite H4 in H2. simpl in H2.
  rewrite <- H3, H5 in H2. auto.
+ rewrite Hqr in H0; clear q Hqr.
  induction l.
  - elim (CCC_To_bproj_Sel_ql _ _ _ _ _ _ _ (H _ H1) H0); auto.
    intros. destroy H3. intro.
    rewrite H4 in H2. simpl in H2.
    rewrite <- H3, H5 in H2. auto.
  - elim (CCC_To_bproj_Sel_qr _ _ _ _ _ _ _ (H _ H1) H0); auto.
    intros. destroy H3. intro.
    rewrite H4 in H2. simpl in H2.
    rewrite <- H3, H5 in H2. auto.
+ rewrite (CCC_To_bproj_Sel_r _ _ _ _ _ _ _ _ _ (H _ H1) H0); auto.
Qed.

Lemma CCC_To_projectable_C_Cond : forall Defs ps C s C' s' p,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  CCC_To _ Defs C s (R_Cond p) C' s' ->
  projectable_C Defs ps C'.
Proof.
intros.
red. rewrite Forall_forall; intro.
induction x as (r,B). unfold epp_list; rewrite in_map_iff.
simpl; intros. destroy H1. inversion H2.
rewrite H4 in H1; clear x H4 H2 B H5.
generalize (strongly_projectable_C _ _ _ (H _ H1)); intro.
elim ((@eq_dec Pid) p r); intro Hpr.
+ rewrite Hpr in H0; clear p Hpr.
  elim (CCC_To_bproj_Cond_p _ _ _ _ _ _ (H _ H1) H0).
  intros. destroy H3. intro.
  rewrite H4 in H2. simpl in H2.
  case_eq (eval_on_state BEv x s r); intro.
  rewrite <- H5, H6 in H2; auto.
  rewrite <- H3, H6 in H2; auto.
  induction (collapse x0); auto.
+ generalize (CCC_To_bproj_Cond_r _ _ _ _ _ _ _ (H _ H1) H0 Hpr); intros.
  destroy H3. rewrite H5, collapse_inject. apply inject_not_undefined.
Qed.

Lemma CCC_To_projectable_C_Call : forall Defs ps C s C' s' X p Xs,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  (forall p Y, In p ps -> In Y Xs -> strongly_projectable Defs (snd (Defs Y)) p) ->
  (forall Y, set_incl_pid (CCC_pn (snd (Defs Y)) (fun Z => fst (Defs Z))) (fst (Defs Y))) ->
  In X Xs -> CCC_To _ Defs C s (R_Call X p) C' s' ->
  projectable_C Defs ps C'.
Proof.
intros Defs ps C s C' s' X p Xs H H' H'' HX H0.
red. rewrite Forall_forall; intro.
induction x as (r,B). unfold epp_list; rewrite in_map_iff.
simpl; intros. destroy H1. inversion H2.
rewrite H4 in H1; clear x H4 H2 B H5.
generalize (strongly_projectable_C _ _ _ (H _ H1)); intro.
elim ((@eq_dec Pid) p r); intro Hpr.
+ rewrite Hpr in H0; clear p Hpr.
  elim (CCC_To_bproj_Call_p Defs C s C' s' r X Xs); auto.
  intros; intro. destroy H4.
  rewrite H7, collapse_inject in H5. apply (inject_not_undefined _ x0); auto.
+ rewrite (CCC_To_bproj_Call_r Defs C s C' s' p X); auto.
Qed.

Lemma CCC_To_projectable_C : forall Defs ps C s C' s' t Xs,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  (forall p Y, In p ps -> In Y Xs -> strongly_projectable Defs (snd (Defs Y)) p) ->
  (forall Y, set_incl_pid (CCC_pn (snd (Defs Y)) (fun Z => fst (Defs Z))) (fst (Defs Y))) ->
  (forall p X, In X Xs -> In p (fst (Defs X)) -> In p ps) ->
  within_Xs Xs C -> CCC_To _ Defs C s t C' s' -> projectable_C Defs ps C'.
Proof.
induction t; intros.
eapply CCC_To_projectable_C_Com; eauto.
eapply CCC_To_projectable_C_Sel; eauto.
eapply CCC_To_projectable_C_Cond; eauto.
eapply CCC_To_projectable_C_Call; eauto.
eapply CCC_To_Xs; eauto.
Qed.

Lemma CCC_To_projectable : forall P Xs ps,
  Program_WF _ Xs P -> well_ann _ P -> projectable Xs ps P ->
  (forall p, In p ps -> strongly_projectable (Procedures _ P) (Main P) p) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In X Xs -> In p (Vars P X) -> In p ps) ->
  forall s tl P' s', (P,s) --[tl]--> (P',s') -> projectable Xs ps P'.
Proof.
intros. rename H2 into HSP, H3 into Hnames, H4 into HDefs, H5 into H2.
induction P as (Defs,C). induction P' as (Defs', C').
generalize (CCP_To_Defs_stable _ Defs Defs' C C' tl s s' H2); intro.
rewrite <- H3 in H2; rewrite <- H3; clear Defs' H3.
inversion H2. rewrite <- H4 in H2. clear s'0 H9 C'0 H8 tl H4 s0 H6 C0 H5 Defs0 H3.
rename H7 into Ht.
destroy H0; intros. repeat split; auto.
+ destroy H1.
  apply CCC_To_projectable_C with C s s' t Xs; auto.
  - simpl. intro r; intros.
    elim (In_dec (@eq_dec Pid) r (CCC_pn (snd (Defs Y)) (fun X : RecVar => fst (Defs X)))); intro.
    * apply initial_strongly_projectable with (fst (Defs Y)); auto.
      destroy H. elim (H Y); tauto.
      red in H4; rewrite Forall_forall in H4; auto.
      apply H0; auto.
    * apply initial_strongly_projectable'; auto.
      destroy H. elim (H Y); tauto.
  - destroy H; auto.
+ apply H1.
+ simpl. intros. elim (CCC_To_pn' _ _ _ _ _ _ _ Ht p); intros; auto.
  - destroy H4. apply HDefs with x.
    destroy H. apply within_Xs_char with C; auto.
    apply H0; auto.
  - eapply CCC_pn_mon; eauto.
    simpl. intros. inversion H4.
+ apply H1.
Qed.

(** Strong projectability of well-formed programs is preserved by reductions:
  this is needed for chaining applications of the EPP theorem. *)
Lemma CCC_To_strongly_projectable_Com : forall Defs C s C' s' ps p v q x r,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) ->
  In r ps ->
  CCC_To _ Defs C s (R_Com p v q x) C' s' ->
  strongly_projectable Defs C' r.
Proof.
intros.
rename H into H0, H1 into Hr, H0 into Hnames, H2 into H.
revert C H0 Hnames r Hr C' H.
induction C; intros; inversion H.
+ rewrite <- H5; eauto.
+ simpl; apply IHC; auto.
  intros. apply Hnames. simpl; sup.
+ elim (H0 r); auto; intros. inversion_clear H13.
  assert (strongly_projectable Defs C1' r).
    apply IHC1; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  assert (strongly_projectable Defs C2' r).
    apply IHC2; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  repeat split; auto.
  destroy H9.
  simpl. case (eq_dec t r); intro.
  2: elim ((@eq_dec Pid) p r); intro Hpr.
  3: elim ((@eq_dec Pid) q r); intro Hqr.
  - apply strongly_projectable_C in H13.
    apply strongly_projectable_C in H16.
    simpl. repeat rewrite Xmatch_elim; auto. discriminate.
  - rewrite Hpr in H10, H11.
    elim (CCC_To_bproj_Com_p _ _ _ _ _ _ _ _ _ H12 H10); intros.
    destroy H18. rename x0 into e, x1 into a, x2 into B1. clear H18.
    elim (CCC_To_bproj_Com_p _ _ _ _ _ _ _ _ _ H14 H11); intros.
    destroy H18. rename x0 into e', x1 into a', x2 into B2. clear H18.
    rewrite H20, H22.
    generalize (H0 r Hr); clear H0; intro.
    apply strongly_projectable_C in H0; revert H0.
    simpl. rewrite H19, H21; simpl; auto.
    repeat (rewrite DecType_neq; auto); repeat rewrite eqb_refl.
    simpl. elim (XUndefined_dec _ (B1 [[\/]] B2)); intro.
    rewrite a0. auto. case eqb; case eqb; simpl; tauto.
    rewrite Xmatch_elim; auto.
    case eqb; case eqb; simpl; auto.
    case (collapse (B1 [[\/]] B2)); auto; discriminate.
  - rewrite Hqr in H10, H11.
    elim (CCC_To_bproj_Com_q _ _ _ _ _ _ _ _ _ H12 H10); auto; intros.
    destroy H18. rename x0 into a1, x1 into B1.
    elim (CCC_To_bproj_Com_q _ _ _ _ _ _ _ _ _ H14 H11); auto; intros.
    destroy H20. rename x0 into a2, x1 into B2.
    rewrite H20, H18.
    generalize (H0 r Hr); clear H0; intro.
    apply strongly_projectable_C in H0; revert H0.
    simpl. rewrite H19, H21.
    rewrite DecType_neq; auto.
    simpl. repeat rewrite eqb_refl.
    case eqb; simpl. 2: tauto.
    intros; intro.
    elim (XUndefined_dec _ (B1 [[\/]] B2)); intro.
    rewrite a in H0. auto.
    rewrite Xmatch_elim in H0; auto.
    simpl in H0; rewrite H22 in H0. auto.
  - rewrite (CCC_To_bproj_Com_r _ _ _ _ _ _ _ _ _ _ H12 H10); auto.
    rewrite (CCC_To_bproj_Com_r _ _ _ _ _ _ _ _ _ _ H14 H11); auto.
    intro; apply H15.
    simpl. rewrite DecType_neq; auto.
+ destroy H0.
  rewrite <- H1 in H0, Hnames, H, H6. rewrite <- H1.
  clear t H1.
  repeat split; auto.
  apply IHC; auto. apply H0.
  intros; apply Hnames. simpl. sup.
  elim (H0 r); auto. intros. elim (H11 p0); auto.
  apply disjoint_ps_rl_In with (p:=p0) in H8; auto.
  destroy H8.
  rewrite (CCC_To_bproj_Com_r Defs C s C'0 s' p q v x); auto.
  elim (H0 r); auto. intros. elim (H12 p0); auto.
  apply H0. apply Hnames. simpl. sup.
Qed.

Lemma CCC_To_strongly_projectable_Sel : forall Defs C s C' s' ps p q l r,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) ->
  In r ps ->
  CCC_To _ Defs C s (R_Sel p q l) C' s' ->
  strongly_projectable Defs C' r.
Proof.
intros.
rename H into H0, H1 into Hr, H0 into Hnames, H2 into H.
revert C H0 Hnames r Hr C' H.
induction C; intros; inversion H.
+ rewrite <- H5; eauto.
+ simpl; apply IHC; auto.
  intros. apply Hnames. simpl; sup.
+ elim (H0 r); auto; intros. inversion_clear H13.
  assert (strongly_projectable Defs C1' r).
    apply IHC1; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  assert (strongly_projectable Defs C2' r).
    apply IHC2; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  repeat split; auto.
  destroy H9.
  simpl. case (eq_dec t r); intro H18.
  2: elim ((@eq_dec Pid) p r); intro Hpr.
  3: elim ((@eq_dec Pid) q r); intro Hqr.
  3: induction l.
  - apply strongly_projectable_C in H13.
    apply strongly_projectable_C in H16.
    simpl. repeat rewrite Xmatch_elim; auto. discriminate.
  - rewrite Hpr in H10, H11.
    elim (CCC_To_bproj_Sel_p _ _ _ _ _ _ _ _ H12 H10); intros.
    destroy H19. rename x into a1, x0 into B1.
    elim (CCC_To_bproj_Sel_p _ _ _ _ _ _ _ _ H14 H11); intros.
    destroy H21. rename x into a2, x0 into B2.
    rewrite H21, H19.
    generalize (H0 r Hr); clear H0; intro.
    apply strongly_projectable_C in H0; revert H0.
    simpl. rewrite H20, H22.
    rewrite DecType_neq; auto.
    simpl. repeat rewrite eqb_refl.
    case eqb. 2: tauto.
    intros; intro.
    elim (XUndefined_dec _ (B1 [[\/]] B2)); intro.
    rewrite a in H0. auto.
    rewrite Xmatch_elim in H0; auto.
    simpl in H0; rewrite H23 in H0. auto.
  - rewrite Hqr in H10, H11.
    elim (CCC_To_bproj_Sel_ql _ _ _ _ _ _ _ H12 H10); auto; intros.
    destroy H19. rename x into a1, x0 into B1.
    elim (CCC_To_bproj_Sel_ql _ _ _ _ _ _ _ H14 H11); auto; intros.
    destroy H21. rename x into a2, x0 into B2.
    rewrite H21, H19.
    generalize (H0 r Hr); clear H0; intro.
    apply strongly_projectable_C in H0; revert H0.
    simpl. rewrite H20, H22.
    rewrite DecType_neq; auto.
    simpl. rewrite eqb_refl.
    elim eqb. 2: tauto.
    intros; intro.
    elim (XUndefined_dec _ (B1 [[\/]] B2)); intro.
    rewrite a in H0. auto.
    rewrite Xmatch_elim in H0; auto.
    simpl in H0; rewrite H23 in H0. auto.
  - rewrite Hqr in H10, H11.
    elim (CCC_To_bproj_Sel_qr _ _ _ _ _ _ _ H12 H10); auto; intros.
    destroy H19. rename x into a1, x0 into B1.
    elim (CCC_To_bproj_Sel_qr _ _ _ _ _ _ _ H14 H11); auto; intros.
    destroy H21. rename x into a2, x0 into B2.
    rewrite H21, H19.
    generalize (H0 r Hr); clear H0; intro.
    apply strongly_projectable_C in H0; revert H0.
    simpl. rewrite H20, H22.
    rewrite DecType_neq; auto.
    simpl. rewrite eqb_refl.
    elim eqb. 2: tauto.
    intros; intro.
    elim (XUndefined_dec _ (B1 [[\/]] B2)); intro.
    rewrite a in H0. auto.
    rewrite Xmatch_elim in H0; auto.
    simpl in H0; rewrite H23 in H0. auto.
  - rewrite (CCC_To_bproj_Sel_r _ _ _ _ _ _ _ _ _ H12 H10); auto.
    rewrite (CCC_To_bproj_Sel_r _ _ _ _ _ _ _ _ _ H14 H11); auto.
    intro; apply H15.
    simpl. rewrite DecType_neq; auto.
+ destroy H0.
  rewrite <- H1 in H0, Hnames, H, H6. rewrite <- H1.
  clear t H1.
  repeat split; auto.
  apply IHC; auto. apply H0.
  intros; apply Hnames. simpl. sup.
  elim (H0 r); auto. intros. elim (H11 p0); auto.
  apply disjoint_ps_rl_In with (p:=p0) in H8; auto.
  destroy H8.
  rewrite (CCC_To_bproj_Sel_r Defs C s C'0 s' p q l); auto.
  elim (H0 r); auto. intros. elim (H12 p0); auto.
  apply H0. apply Hnames. simpl. sup.
Qed.

Lemma CCC_To_strongly_projectable_Cond : forall Defs C s C' s' ps p r,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) ->
  In r ps ->
  CCC_To _ Defs C s (R_Cond p) C' s' ->
  strongly_projectable Defs C' r.
Proof.
intros.
rename H into H0, H1 into Hr, H0 into Hnames, H2 into H.
revert C H0 Hnames r Hr C' H.
induction C; intros; inversion H.
+ simpl; apply IHC; auto.
  intros. apply Hnames. simpl; sup.
+ rewrite <- H6; eapply strongly_projectable_inv_Then; eauto.
+ rewrite <- H6; eapply strongly_projectable_inv_Else; eauto.
+ rename p0 into q.
  elim (H0 r); auto; intros. inversion_clear H13.
  assert (strongly_projectable Defs C1' r).
    apply IHC1; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  assert (strongly_projectable Defs C2' r).
    apply IHC2; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  repeat split; auto.
  destroy H9.
  simpl. case (eq_dec t r); intro Hqr.
  2: elim ((@eq_dec Pid) p r); intro Hpr.
  - apply strongly_projectable_C in H13.
    apply strongly_projectable_C in H16.
    simpl. repeat rewrite Xmatch_elim; auto. discriminate.
  - rewrite Hpr in H10, H11.
    elim (CCC_To_bproj_Cond_p _ _ _ _ _ _ H12 H10); intros.
    destroy H17. rename x into b1, x0 into B1t, x1 into B1e.
    elim (CCC_To_bproj_Cond_p _ _ _ _ _ _ H14 H11); intros.
    destroy H20. rename x into b2, x0 into B2t, x1 into B2e.
    revert H15; simpl.
    rewrite DecType_neq, H18, H21; auto.
    elim (eq_dec b1 b2); intro Hb.
    2: {
      simpl. rewrite <- eqb_neq in Hb; unfold Sig' in Hb; simpl in Hb.
      rewrite Hb. simpl; auto.
    }
    rewrite <- Hb. rewrite <- Hb in H20, H22. intro.
    assert (B1t [[\/]] B2t <> XUndefined).
    1: { intro. revert H15. simpl; rewrite H23, eqb_refl. auto. }
    assert (B1e [[\/]] B2e <> XUndefined).
    1: { intro. revert H15. simpl; rewrite H24, Xmatch_elim; auto. rewrite eqb_refl; auto. }
    rewrite Xmerge_Cond_inv in H15; auto.
    case_eq (eval_on_state BEv b1 s r); intro Hb'.
    rewrite H19, H22; auto. intro.
    simpl in H15. rewrite H25 in H15. auto.
    rewrite H20, H17; auto. intro.
    revert H15. simpl. rewrite H25. case (collapse (B1t [[\/]] B2t)); auto.
  - generalize (CCC_To_bproj_Cond_r _ _ _ _ _ _ _ H12 H10 Hpr); intro.
    generalize (CCC_To_bproj_Cond_r _ _ _ _ _ _ _ H14 H11 Hpr); intro.
    simpl in H15. rewrite DecType_neq in H15; auto.
    apply collapse_exists in H15. destroy H15.
    generalize (Xmore_branches_merge_extend _ _ _ _ _ _ H17 H18 H15); intro.
    destroy H19. rewrite H21, collapse_inject; apply inject_not_undefined.
+ destroy H0.
  rewrite <- H1 in H0, Hnames, H, H6. rewrite <- H1.
  clear t H1.
  repeat split; auto.
  apply IHC; auto. apply H0.
  intros; apply Hnames. simpl. sup.
  elim (H0 r); auto. intros. elim (H11 p0); auto.
  apply disjoint_ps_rl_In with (p:=p0) in H8; auto.
  destroy H8.
  apply Xmore_branches_trans with (bproj Defs C p0).
  elim (H0 r); auto. intros. elim (H11 p0); auto.
  apply (CCC_To_bproj_Cond_r Defs C s C'0 s' p); auto.
  apply H0. apply Hnames. simpl. sup.
Qed.

Lemma CCC_To_strongly_projectable_Call : forall Defs C s C' s' ps p X r Xs,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  (forall p Y, In p ps -> In Y Xs -> strongly_projectable Defs (snd (Defs Y)) p) ->
  (forall Y, set_incl_pid (CCC_pn (snd (Defs Y)) (fun Z => fst (Defs Z))) (fst (Defs Y))) ->
  (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) ->
  In r ps -> In X Xs -> 
  CCC_To _ Defs C s (R_Call X p) C' s' ->
  strongly_projectable Defs C' r.
Proof.
intros.
rename H into H0, H3 into Hr, H2 into Hnames, H1 into HDefs, H4 into HX, H5 into H, H0 into Hsp.
revert C H0 Hnames r Hr C' H.
induction C; intros; inversion H.
+ simpl; apply IHC; auto.
  intros. apply Hnames. simpl; sup.
+ rename p0 into q.
  elim (H0 r); auto; intros. inversion_clear H13.
  assert (strongly_projectable Defs C1' r).
    apply IHC1; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  assert (strongly_projectable Defs C2' r).
    apply IHC2; auto. intros; apply H0; auto.
    intros. apply Hnames. simpl; sup; sup.
  repeat split; auto.
  simpl in H9.
  simpl. case (eq_dec t r); intro H18.
  2: elim ((@eq_dec Pid) p r); intro Hpr.
  - apply strongly_projectable_C in H13.
    apply strongly_projectable_C in H16.
    simpl. repeat rewrite Xmatch_elim; auto. discriminate.
  - rewrite Hpr in H10, H11.
    elim (CCC_To_bproj_Call_p _ _ _ _ _ _ _ _ H12 (fun Y => Hsp r Y Hr) HDefs HX H10); intros.
    elim (CCC_To_bproj_Call_p _ _ _ _ _ _ _ _ H14 (fun Y => Hsp r Y Hr) HDefs HX H11); intros.
    elim (Xmerge_is_lub _ _ _ _ H19 H21); intros.
    destroy H22. rewrite H24, collapse_inject.
    apply inject_not_undefined.
  - rewrite (CCC_To_bproj_Call_r _ _ _ _ _ _ _ _ HDefs H10); auto.
    rewrite (CCC_To_bproj_Call_r _ _ _ _ _ _ _ _ HDefs H11); auto.
    intro; apply H15.
    simpl. rewrite DecType_neq, H17; auto.
+ auto.
+ repeat split; auto.
  eapply set_remove'_1; eauto.
  generalize (Hsp p1 X); intros.
  apply strongly_projectable_C, collapse_exists in H11; auto.
  destroy H11. apply Xmore_branches_refl with x; auto.
  apply Hnames; simpl. rewrite H2. eapply set_remove'_1; eauto.
+ repeat split.
  eapply IHC; eauto. apply H0.
  intros; apply Hnames. simpl; sup.
  elim (H0 r); auto. intros. elim (H12 p0); auto.
  elim (H0 r); auto. intros. elim (H12 p0); auto. intros.
  apply disjoint_ps_rl_In with (p:=p0) in H8; auto.
  destroy H8.
  rewrite (CCC_To_bproj_Call_r Defs C s C'0 s' p X p0); auto.
+ rewrite H4 in H0, Hnames, H, H1; clear t H4.
  elim (H0 r); auto; intros.
  split; auto; intros.
  assert (In p1 l). eapply set_remove'_1; eauto.
  elim (H12 p1); auto.
+ rewrite <- H6. apply H0; auto.
Qed.

Lemma CCC_To_strongly_projectable : forall Defs ps C s C' s' t Xs,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) ->
  (forall p Y, In p ps -> In Y Xs -> strongly_projectable Defs (snd (Defs Y)) p) ->
  (forall Y, set_incl_pid (CCC_pn (snd (Defs Y)) (fun Z => fst (Defs Z))) (fst (Defs Y))) ->
  (forall p X, In X Xs -> In p (fst (Defs X)) -> In p ps) ->
  within_Xs Xs C -> CCC_To _ Defs C s t C' s' ->
  forall p, In p ps -> strongly_projectable Defs C' p.
Proof.
induction t; intros.
+ eapply CCC_To_strongly_projectable_Com; eauto.
+ eapply CCC_To_strongly_projectable_Sel; eauto.
+ eapply CCC_To_strongly_projectable_Cond; eauto.
+ eapply CCC_To_strongly_projectable_Call; eauto.
  eapply CCC_To_Xs; eauto.
Qed.

Lemma CCP_To_strongly_projectable : forall P Xs ps,
  Program_WF _ Xs P -> well_ann _ P -> projectable Xs ps P ->
  (forall p, In p ps -> strongly_projectable (Procedures _ P) (Main P) p) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In X Xs -> In p (Vars P X) -> In p ps) ->
  forall s tl P' s', (P,s) --[tl]--> (P',s') ->
  forall p, In p ps -> strongly_projectable (Procedures _ P') (Main P') p.
Proof.
intros. rename H2 into HSP, H3 into Hnames, H4 into HDefs, H5 into H2.
induction P as (Defs,C). induction P' as (Defs', C').
generalize (CCP_To_Defs_stable _ Defs Defs' C C' tl s s' H2); intro.
rewrite <- H3 in H2; rewrite <- H3; clear Defs' H3.
inversion H2. rewrite <- H4 in H2. clear s'0 H10 C'0 H9 tl H4 s0 H7 C0 H5 Defs0 H3.
rename H8 into Ht.
destroy H0; intros.
rename p into r.
destroy H1.
simpl. eapply CCC_To_strongly_projectable; eauto.
+ intros. red in H4; rewrite Forall_forall in H4.
  destroy H. elim (H Y); auto. clear H. simpl; intros; destroy H13.
  elim (In_dec (@eq_dec Pid) p (fst (Defs Y))); intro.
  apply initial_strongly_projectable with (fst (Defs Y)); auto.
  apply initial_strongly_projectable'; auto.
  intro. apply b, H0; auto.
+ apply Program_WF_Main_within_Xs; auto.
Qed.

(** ** Completeness
  The completeness part of the EPP theorem. *)
Lemma EPP_Complete : forall P Xs ps,
  Program_WF _ Xs P -> well_ann _ P -> forall (HP:projectable Xs ps P),
  (forall p, In p ps -> strongly_projectable (Procedures _ P) (Main P) p) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In X Xs -> In p (Vars P X) -> In p ps) ->
  forall s tl P' s', ((P,s) --[tl]--> (P',s'))%CC ->
  exists N tl', ((epp Xs ps P HP,s) --[tl']--> (N,s'))%SP
    /\ Procs N = Procs (epp Xs ps P HP)
    /\ forall H, Net N >> Net (epp Xs ps P' H).
Proof.
intros P Xs ps HWF Hann HP Hsp HMain HXs s tl P' s' HTo.
induction P as (Defs,C), P' as (Defs',C').
generalize (CCP_To_Defs_stable _ Defs Defs' C C' tl s s' HTo); intro.
rewrite <- H in HTo; rewrite <- H; clear Defs' H.
simpl in Hsp, HMain.
set (N' := epp _ _ _ HP). assert (N' = epp _ _ _ HP) as HN; auto.
clearbody N'; induction N' as (Defs',N).
assert (forall r, {Br | bproj Defs C r = inject Br}) as Hout.
1: { intro.
  elim (In_dec (@eq_dec Pid) r ps); intro Hr.
  elim (collapse_char' _ (bproj Defs C r)); auto.
  intro. elim (strongly_projectable_C _ _ _ (Hsp r Hr)); auto.
  exists (End _); apply bproj_not_In.
  intro; apply Hr, HMain. auto.
}
assert (projectable_C Defs ps C) as HC.
1: apply strongly_projectable_C'; auto.
induction tl; intros; inversion HTo; induction t; inversion H3.
+ rewrite H9, H8, H7 in H0.
  clear q0 v0 p0 s'0 C'0 s0 C0 Defs0 H9 H8 H7 H5 H4 H3 H2 H1 H.
  generalize (CCC_To_pn _ _ _ _ _ _ _ H0); intro.
  assert (In p ps) as Hp.
  1: { apply HMain, H. simpl; auto. }
  assert (In q ps) as Hq.
  1: { apply HMain, H. simpl; auto. }
  assert (p <> q) as Hpq.
  1: { eapply CCC_To_Com_neq; eauto. apply HWF. }
  clear H.
  elim (CCC_To_bproj_Com_p Defs C s C' s' p q v x); intros; auto.
  destroy H. rename x0 into e.
  elim (Hout p); intro.
  rewrite H1; case x0; intros; try (inversion p0); try (inversion p1).
  2: case o, o0; try induction p1; try induction p2; inversion p0.
  rewrite H7 in H1, H2. rename b into Bp.
  clear t1 H6 x2 H7 t0 H5 t H4 p0 x0.
  elim (CCC_To_bproj_Com_q Defs C s C' s' p q v x); intros; auto.
  destroy H3.
  elim (Hout q); intro.
  rewrite H4; case x3; intros; try (inversion p1); try (inversion p0).
  2: case o, o0; try induction p1; try induction p2; inversion p0.
  rewrite H9 in H4, H3. rename b into Bq.
  clear x2 H9 t1 H8 t0 H7 t H6 p0 x3.
  exists (Build_Program Sig' Defs' (fun r =>
    if (eq_dec r p) then Bp
    else if (eq_dec r q) then Bq
    else N r)),
  (@forget Pid Value Var PR (R_Com p v q x)).
  repeat split; auto.
  - rewrite H. apply (@SPP_To_intro Sig'). apply S_Com with (x1:ann Sig') Bp x0 Bq.
    * replace N with (Net (Build_Program _ Defs' N)); auto.
      change (bproj Defs C p = inject (Send Sig' q e x1 Bp)) in H1.
      rewrite epp_C_char' with (HP:=HP) in H1; auto.
      apply inject_inj in H1. rewrite <- H1, HN; auto.
    * replace N with (Net (Build_Program _ Defs' N)); auto.
      change (bproj Defs C q = inject (Recv Sig' p x x0 Bq)) in H4.
      rewrite epp_C_char' with (HP:=HP) in H4; auto.
      apply inject_inj in H4. rewrite <- H4, HN; auto.
    * intro r. case (eq_dec r p); intro H5.
      rewrite H5. symmetry; apply Network_rm_add_2_p; auto.
      case (eq_dec r q); intro H6. rewrite H6.
      symmetry; apply Network_rm_add_2_q; auto.
      elim (Hout r); intros.
      rewrite Network_rm_add_2_out; auto.
    * apply CCC_To_Com_state with Defs C p C'.
      rewrite H in H0; auto.
  - simpl; intros H5 r.
    replace N with (Net (Build_Program _ Defs' N)); auto.
    case (eq_dec r p); intro H6.
    2: case (eq_dec r q); intro H7.
    3: elim (In_dec (@eq_dec Pid) r ps); intro.
    * rewrite H6, DecType_eq.
      apply more_branches_refl'.
      rewrite epp_C_char' with (HP:=H5) in H2; auto.
      apply inject_inj in H2; auto.
    * rewrite H7, DecType_eq.
      apply more_branches_refl'.
      rewrite epp_C_char' with (HP:=H5) in H3; auto.
      rewrite <- H7, DecType_neq, H7; auto.
      apply inject_inj in H3; auto.
    * replace (Net (epp _ _ _ H5) r) with (N r).
      do 2 (rewrite DecType_neq; auto).
      apply more_branches_refl.
      replace N with (Net (Build_Program _ Defs' N)); auto.
      rewrite HN.
      apply inject_inj.
      repeat rewrite <- epp_C_char'; auto.
      symmetry; apply CCC_To_bproj_Com_r with s s' p q v x; auto.
    * replace (Net (epp _ _ _ H5) r) with (End Sig').
      simpl. replace (N r) with (End Sig').
      do 2 (rewrite DecType_neq; auto). constructor.
      replace N with (Net (Build_Program _ Defs' N)); auto.
      rewrite HN, epp_C_char with (HC:=HC), epp_C_out; auto.
      elim (CCC_To_projectable (CC.Build_Program _ Defs C) Xs ps)
        with s (L_Com p v q) (CC.Build_Program _ Defs C') s'; intros; auto.
      rewrite epp_C_char with (HC:=H8), epp_C_out; auto.
      eauto.
+ rewrite H9, H8, H7 in H0.
  clear q0 l0 p0 s'0 C'0 s0 C0 Defs0 H9 H8 H7 H5 H4 H3 H2 H1 H.
  generalize (CCC_To_pn _ _ _ _ _ _ _ H0); intro.
  assert (In p ps) as Hp.
  1: { apply HMain, H. simpl; auto. }
  assert (In q ps) as Hq.
  1: { apply HMain, H. simpl; auto. }
  assert (p <> q) as Hpq.
  1: { eapply CCC_To_Sel_neq; eauto. apply HWF. }
  clear H.
  elim (CCC_To_bproj_Sel_p Defs C s C' s' p q l); intros; auto.
  destroy H. rename x into a.
  elim (Hout p); intro.
  rewrite H1; case x; intros; try (inversion p0); try (inversion p1).
  2: case o, o0; try induction p1; try induction p2; inversion p0.
  rewrite H6 in H1, H. rename b into Bp.
  clear t1 H5 t0 H4 t H3 p0 x.
  induction l.
  1: elim (CCC_To_bproj_Sel_ql Defs C s C' s' p q); intros; auto.
  2: elim (CCC_To_bproj_Sel_qr Defs C s C' s' p q); intros; auto.
  all: destroy H2; elim (Hout q); intro.
  all: rewrite H3; case x2; intros; try (inversion p1); try (inversion p0).
  all: case o, o0; try induction p1; try induction p2; inversion p0.
  all: rewrite H9 in H3, H2; rename b into Bq.
  all: clear x1 H9 p0 H6 H5 p0 x0.
  exists (Build_Program _ Defs' (fun r =>
    if (eq_dec r p) then Bp
    else if (eq_dec r q) then Bq
    else N r)),
  (@forget Pid Value Var PR (R_Sel p q left)).
  2: exists (Build_Program _ Defs' (fun r =>
    if (eq_dec r p) then Bp
    else if (eq_dec r q) then Bq
    else N r)),
  (@forget Pid Value Var PR (R_Sel p q right)).
  all: repeat split; auto.
  1,3: apply (@SPP_To_intro Sig').
  2: apply S_RSel with (a:ann Sig') Bp x None Bq.
  1: apply S_LSel with (a:ann Sig') Bp x Bq None.
  1,5: replace N with (Net (Build_Program _ Defs' N)); auto.
  1: change (bproj Defs C p = inject (Sel Sig' q left a Bp)) in H1.
  2: change (bproj Defs C p = inject (Sel Sig' q right a Bp)) in H1.
  1,2: rewrite epp_C_char' with (HP:=HP) in H1; auto;
    apply inject_inj in H1; rewrite <- H1, HN; auto.
  1,4: replace N with (Net (Build_Program _ Defs' N)); auto.
  1: change (bproj Defs C q = inject (Branching Sig' p (Some (x,Bq)) None)) in H3.
  2: change (bproj Defs C q = inject (Branching Sig' p None (Some (x,Bq)))) in H3.
  1,2: rewrite epp_C_char' with (HP:=HP) in H3; auto;
    apply inject_inj in H3; etransitivity; eauto; rewrite HN; auto.
  1,3: intro r; case (eq_dec r p); intro H4;
    [rewrite H4; symmetry; apply Network_rm_add_2_p; auto
    | case (eq_dec r q); intro H5;
      [ rewrite H5; symmetry; apply Network_rm_add_2_q; auto
        | elim (Hout r); intros;
          rewrite Network_rm_add_2_out; auto]].
  1: apply CCC_To_Sel_state with Defs C p q left C'; auto.
  1: apply CCC_To_Sel_state with Defs C p q right C'; auto.
  1,2: simpl; intros H5 r;
    replace N with (Net (Build_Program _ Defs' N)); auto;
    case (eq_dec r p); intro H4;
    [idtac | case (eq_dec r q); intro H6;
      [idtac | elim (In_dec (@eq_dec Pid) r ps); intro]].
    all: try (rewrite H4; rewrite DecType_eq).
    all: try (rewrite H6; rewrite DecType_eq).
    all: repeat (rewrite DecType_neq; auto).
    1,5: apply more_branches_refl';
      rewrite epp_C_char' with (HP:=H5) in H; auto;
      apply inject_inj in H; auto.
    1,4: apply more_branches_refl';
      rewrite epp_C_char' with (HP:=H5) in H2; auto;
      apply inject_inj in H2; auto.
    1,3: apply more_branches_refl'; transitivity (N r); auto;
        replace N with (Net (Build_Program _ Defs' N)); auto;
        rewrite HN; apply inject_inj;
        repeat rewrite <- epp_C_char'; auto.
    1: symmetry; apply CCC_To_bproj_Sel_r with s s' p q left; auto.
    1: symmetry; apply CCC_To_bproj_Sel_r with s s' p q right; auto.
    1,2: replace (Net (epp _ _ _ H5) r) with (End Sig').
    1,3: simpl; replace (N r) with (End Sig').
    1,3: constructor.
    1,2: replace N with (Net (Build_Program _ Defs' N)); auto;
      rewrite HN, epp_C_char with (HC:=HC), epp_C_out; auto.
    1: elim (CCC_To_projectable (CC.Build_Program _ Defs C) Xs ps)
        with s (L_Sel p q left) (CC.Build_Program _ Defs C') s'; intros;
       eauto; rewrite epp_C_char with (HC:=H9), epp_C_out; auto.
    1: elim (CCC_To_projectable (CC.Build_Program _ Defs C) Xs ps)
        with s (L_Sel p q right) (CC.Build_Program _ Defs C') s'; intros;
       eauto; rewrite epp_C_char with (HC:=H9), epp_C_out; auto.
+ rewrite H7 in H0.
  clear p0 s'0 C'0 s0 C0 H7 H5 H4 H3 H2 H1 Defs0 H.
  generalize (CCC_To_pn _ _ _ _ _ _ _ H0); intro.
  assert (In p ps) as Hp.
  1: { apply HMain, H. simpl; auto. }
  clear H.
  elim (CCC_To_bproj_Cond_p Defs C s C' s' p); intros; auto.
  destroy H. rename x into b.
  elim (Hout p); intro.
  rewrite H1; case x; intros; try (inversion p0); try (inversion p1).
  1: case o, o0; try induction p1; try induction p2; inversion p0.
  rewrite H5 in H1, H2; rewrite H6 in H1, H. rename b0 into Bt, b1 into Be.
  clear x1 H6 x0 H5 t H4 p0.
  case_eq (eval_on_state BEv b s p); intro Hb.
  1: exists (Build_Program _ Defs' (fun r =>
    if (eq_dec r p) then Bt else N r)),
    (@forget Pid Value Var PR (R_Cond p)).
  2: exists (Build_Program _ Defs' (fun r =>
    if (eq_dec r p) then Be else N r)),
    (@forget Pid Value Var PR (R_Cond p)).
  1,2: repeat split; auto.
  1,3: apply (@SPP_To_intro Sig').
  1: apply (@S_Then Sig') with b Bt Be; auto.
  4: apply (@S_Else Sig') with b Bt Be; auto.
  1,4: replace N with (Net (Build_Program _ Defs' N)); auto;
      change (bproj Defs C p = inject (Cond Sig' b Bt Be)) in H1;
      rewrite epp_C_char' with (HP:=HP) in H1; auto;
      apply inject_inj in H1; rewrite <- H1, HN; auto.
  1,3: intro r; case (eq_dec r p); intro H3;
      [ rewrite H3, Par_proj2;
        [ symmetry; apply Process_refl | apply Network_rm_In]
      | symmetry; rewrite Par_proj1';
        [apply Network_rm_out; auto
        | apply Process_out; auto]].
  1,2: apply CCC_To_Cond_state with Defs C p C'; auto.
  all: simpl; intros H5 r; replace N with (Net (Build_Program _ Defs' N)); auto.
  all: case (eq_dec r p); intro H3; [idtac | elim (In_dec (@eq_dec Pid) r ps); intro].
    all: try (rewrite H3; rewrite DecType_eq).
    all: repeat (rewrite DecType_neq; auto).
  * apply more_branches_refl'.
    rewrite epp_C_char' with (HP:=H5) in H2; auto.
    apply inject_inj in H2; auto.
  * rewrite HN. assert (p <> r) as Hpr; auto.
    elim (CCC_To_bproj_Cond_r _ _ _ _ _ _ r (Hsp _ a) H0 Hpr).
    intros. destroy H4.
    replace (Net (epp _ _ _ HP) r) with x0.
    replace (Net (epp _ _ _ H5) r) with x1; auto.
    all: apply inject_inj.
    rewrite <- H7. apply epp_C_char'; auto.
    rewrite <- H6. apply epp_C_char'; auto.
  * replace (Net (epp _ _ _ H5) r) with (End Sig').
    simpl. replace (N r) with (End Sig'). constructor.
    replace N with (Net (Build_Program _ Defs' N)); auto.
    rewrite HN, epp_C_char with (HC:=HC), epp_C_out; auto.
    elim (CCC_To_projectable (CC.Build_Program _ Defs C) Xs ps)
      with s (L_Tau p) (CC.Build_Program _ Defs C') s'; intros; auto.
    rewrite epp_C_char with (HC:=H4), epp_C_out; auto.
    eauto.
  * apply more_branches_refl'.
    rewrite epp_C_char' with (HP:=H5) in H; auto.
    apply inject_inj in H; auto.
  * rewrite HN. assert (p <> r) as Hpr; auto.
    elim (CCC_To_bproj_Cond_r _ _ _ _ _ _ r (Hsp _ a) H0 Hpr).
    intros. destroy H4.
    replace (Net (epp _ _ _ HP) r) with x0.
    replace (Net (epp _ _ _ H5) r) with x1; auto.
    all: apply inject_inj.
    rewrite <- H7. apply epp_C_char'; auto.
    rewrite <- H6. apply epp_C_char'; auto.
  * replace (Net (epp _ _ _ H5) r) with (End Sig').
    simpl. replace (N r) with (End Sig'). constructor.
    replace N with (Net (Build_Program _ Defs' N)); auto.
    rewrite HN, epp_C_char with (HC:=HC), epp_C_out; auto.
    elim (CCC_To_projectable (CC.Build_Program _ Defs C) Xs ps)
      with s (L_Tau p) (CC.Build_Program _ Defs C') s'; intros; auto.
    rewrite epp_C_char with (HC:=H4), epp_C_out; auto.
    eauto.
+ rewrite H7 in H0.
  clear p0 s'0 C'0 s0 C0 Defs0 H7 H5 H4 H3 H2 H1 H.
  generalize (CCC_To_pn _ _ _ _ _ _ _ H0); intro.
  assert (In p ps) as Hp.
  1: { apply HMain, H. simpl; auto. }
  clear H.
  assert (In X Xs) as HX.
  1: { eapply CCC_To_Xs; eauto. destroy HWF; auto. }
  elim (CCC_To_bproj_Call_p Defs C s C' s' p X Xs); intros; auto.
  2: { eapply Program_WF_Defs_strongly_projectable with (P:=CC.Build_Program _ Defs C); eauto. }
  2: apply Hann.
  elim (Hout p); intro.
  rewrite H; case x; intros; try (inversion p0); try (inversion p1).
  1: case o, o0; try induction p1; try induction p2; inversion p0.
  rewrite H3 in H. rename t into Y, H3 into HY. clear p0 x.
  inversion_clear HP. destroy H3.
  red in H4; rewrite Forall_forall in H4.
  generalize (H4 _ HX); clear H3 H6 H5 H4 H2; intro H4.
  apply projectable_C_use with (p:=p) in H4.
  simpl in H4; destroy H4. rename x into Bp.
  2: { simpl. eapply CCC_To_Call_ann; eauto. }
  exists (Build_Program _ Defs' (fun r =>
    if (eq_dec r p) then Bp else N r)),
  (@forget Pid Value Var PR (R_Call Y p)).
  repeat split.
  - apply (@SPP_To_intro Sig'), (@S_Call Sig').
    * replace N with (Net (Build_Program _ Defs' N)); auto.
      change (bproj Defs C p = inject (Call _ Y)) in H.
      rewrite epp_C_char' with (HP:=HP) in H; auto.
      apply inject_inj in H. rewrite <- H, HN; auto.
    * intro r. case (eq_dec r p); intro H2.
      rewrite H2, Par_proj2, Process_refl.
      replace Defs' with (Procs (Build_Program _ Defs' N)); auto.
      rewrite HN, <- HY. rewrite epp_D_char' with (HP:=HP) in H4; auto.
      2: apply Hann.
      rewrite collapse_inject in H4. apply inject_inj; auto.
      apply Network_rm_In.
      symmetry; rewrite Par_proj1'.
      apply Network_rm_out; auto.
      apply Process_out; auto.
    * apply CCC_To_Call_state with Defs C p X C'; auto.
  - simpl; intros H5 r.
    replace N with (Net (Build_Program _ Defs' N)); auto.
    case (eq_dec r p); intro H2.
    * rewrite H2, DecType_eq.
      elim (CCC_To_bproj_Call_p Defs C s C' s' p X Xs); auto.
      intros.
      destroy H6.
      replace Bp with x. replace (Net (epp _ _ _ H5) p) with x0; auto.
      apply inject_inj. rewrite <- H8, epp_C_char' with (HP:=H5); auto.
      apply inject_inj. apply collapse_inv in H4.
      rewrite <- H7; auto.
      intros. eapply Program_WF_Defs_strongly_projectable with (P:=CC.Build_Program _ Defs C); eauto.
    * rewrite DecType_neq; auto.
      elim (In_dec (@eq_dec Pid) r ps); intro Hr.
      apply more_branches_refl'. transitivity (N r); auto.
      replace N with (Net (Build_Program _ Defs' N)); auto.
      rewrite HN.
      apply inject_inj.
      repeat rewrite <- epp_C_char'; auto.
      symmetry; apply CCC_To_bproj_Call_r with s s' p X; auto.
      rewrite HN.
      repeat rewrite epp_out; auto. constructor.
Qed.

Lemma EPP_Complete' : forall P Xs ps,
  Program_WF _ Xs P -> well_ann _ P -> forall (HP:projectable Xs ps P),
  initial (Main P) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In X Xs -> In p (Vars P X) -> In p ps) ->
  forall s tl P' s', (P,s) --[tl]-->* (P',s') ->
  exists N tl', ((epp Xs ps P HP,s) --[tl']-->* (N,s'))%SP
  /\ forall H, Net N >> Net (epp Xs ps P' H).
Proof.
intros P Xs ps HWF Hann HP Hinit HMain HXs s tl P' s' HTo.
assert (forall p, In p ps -> strongly_projectable (Procedures _ P) (Main P) p) as Hsp.
1: { intros. apply initial_strongly_projectable with ps; auto. apply HP. }
induction P as (Defs,C), P' as (Defs',C').
generalize (CCP_ToStar_Defs_stable _ Defs Defs' C C' tl s s' HTo); intro.
rewrite <- H in HTo; rewrite <- H; clear Defs' H.
simpl in Hsp, HMain. clear Hinit.
revert dependent C'. revert dependent C. revert s s'. induction tl.
+ intros. inversion HTo.
  exists (epp _ _ _ HP), nil; repeat split.
  constructor; auto.
  rewrite <- H0. intros; apply more_branches_N_refl'.
  intro. inversion HP.
  rewrite epp_C_char with (HC:=H3). rewrite epp_C_char with (HC:=H3).
  auto.
+ intros. inversion HTo. clear HTo.
  rewrite <- H in H2; clear a H l H0 c1 H1 c3 H3.
  induction c2 as ((Defs',C''),s'').
  generalize (CCP_To_Defs_stable _ Defs Defs' _ _ _ _ _ H2); intro.
  rewrite <- H in H2, H4; clear Defs' H.
  elim EPP_Complete with (HP:=HP) (s:=s) (s':=s'') (tl:=t)
    (P':=CC.Build_Program _ Defs C''); auto.
  intros. destroy H. rename x into pP, x0 into t'.
  assert (projectable Xs ps (CC.Build_Program _ Defs C'')) as HP''.
  1: {
    inversion HP. simpl in H5; destroy H5.
    repeat split; auto.
    apply strongly_projectable_C'.
    eapply CCP_To_strongly_projectable; eauto.
    intros. apply HMain. change C with (Main (CC.Build_Program _ Defs C)).
    eapply CCC_To_pn''; eauto.
    eapply CCC_pn_mon. 2: apply H9. simpl; tauto.
  }
  elim IHtl with (s:=s'') (s':=s') (C:=C'') (C':=C') (HP:=HP''); auto.
  - intros. destroy H3. rename x into pP', x0 into tl'.
    apply SPP_ToStar_more_branches_N with (P1':=pP) in H5.
    destroy H5.
    exists x, (t'::tl'). repeat split; auto.
    apply SPT_Step with (pP,s''); auto.
    intro. apply more_branches_N_trans with (Net pP'); auto.
    auto.
    intro. rewrite H1.
    inversion HP''. simpl in H7; clear H6; destroy H7.
    induction X. repeat rewrite epp_D_char with (HD:=H6); auto.
  - eapply CCC_To_Program_WF; eauto.
  - intros. apply HMain. change C with (Main (CC.Build_Program _ Defs C)).
    eapply CCC_To_pn''; eauto.
  - change C'' with (Main (CC.Build_Program _ Defs C'')).
    change Defs with (Procedures _ (CC.Build_Program _ Defs C'')).
    intros. eapply CCP_To_strongly_projectable; eauto.
Qed.

(** ** Soundness of EPP
  Soundness is proven by case analysis on the label of the reduction, and
  then by induction on the choreography. We split the proofs for each label
  in separate results, as we get some stronger statements. *)

Definition SP_eq (P P':Program Sig') : Prop :=
  forall X, Procs P X = Procs P' X /\ (Net P == Net P')%SP.

Lemma SP_To_bproj_Com : forall Defs Defs' ps C HC s N' s' p x q v,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) ->
  SP_To _ Defs' (epp_C Defs ps C HC) s (R_Com p v q x) N' s' ->
  exists C', CCC_To _ Defs C s (R_Com p v q x) C' s'
  /\ forall HC', (N' == (epp_C Defs ps C' HC'))%SP.
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
      elim (collapse_char'); simpl; intro.
      induction a1. revert p0. rewrite DecType_eq.
      intros. induction x0; inversion p0.
      2: case o, o0; try induction p1; try induction p2; inversion p0.
      inversion H6. auto.
      (* absurd case *)
      exfalso. clear H H9 H10 H4.
      apply projectable_C_use' with (p:=p) in HC; auto.
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
      elim (collapse_char'); simpl; intro.
      induction a1. revert p0. rewrite DecType_eq, DecType_neq; auto.
      intros. induction x0; inversion p0.
      2: case o, o0; try induction p1; try induction p2; inversion p0.
      inversion H9. auto.
      (* absurd case *)
      exfalso. clear H H6 H10 H4.
      apply projectable_C_use' with (p:=q) in HC; auto.
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
  - generalize (projectable_C_inv_Com Defs ps p' e0 q' v' a'' C HC); intro HC'.
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
    assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
    1: intros. apply Hin. simpl; sup.
    elim (IHC HC' Hsp Hin' (eval_on_state Ev e s p) ((epp_C Defs ps C HC' ~~ p ~~ q | p[B] | q[B'])%SP)); intros.
    rename x0 into C'. destroy H0.
    exists (p' # e0 --> q' $ v' @ a'';; C'); repeat split.
    * apply (@C_Delay_Eta Sig); repeat split; auto.
    * intros. eapply Network_eq_trans. apply H10. rewrite <- H4.
      set (H':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0).
      set (H'':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC).
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
      rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC) in H6; inversion H6; auto.
      apply epp_C_wd.
      rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC) in H9; inversion H9; auto.
      apply epp_C_wd.
      apply Network_eq_refl.
+ inversion H. rewrite <- H1 in H. unfold v1; unfold v1 in H, H11.
  clear s'0 H8 N'0 H7 x0 H3 q0 H2 v v1 H1 p0 H0 s0 H5.
  rename t into a'', t0 into p', t1 into q', t2 into l.
  generalize (projectable_C_inv_Sel _ _ _ _ _ _ _ HC); intro HC'.
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
  assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (eval_on_state Ev e s p) (epp_C Defs ps C HC' ~~ p ~~ q | p[B] | q[B']))%SP; intros.
  rename x0 into C'. destroy H0.
  exists (p' --> q'[l] @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros. eapply Network_eq_trans. apply H10. rewrite <- H4.
    set (H' := projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0).
    set (H'' := projectable_C_inv_Sel _ _ _ _ _ _ _ HC).
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
    rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC) in H6; inversion H6; auto.
    apply epp_C_wd.
    rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC) in H9; inversion H9; auto.
    apply epp_C_wd.
    apply Network_eq_refl.
+ inversion H. rewrite <- H1 in H. unfold v1; unfold v1 in H, H11.
  clear s'0 H8 N'0 H7 x0 H3 q0 H2 v v1 H1 p0 H0 s0 H5.
  rename t into p', t0 into b.
  generalize (projectable_C_inv_Then _ _ _ _ _ _ HC); intro HC1.
  generalize (projectable_C_inv_Else _ _ _ _ _ _ HC); intro HC2.
  assert (forall p, In p ps -> strongly_projectable Defs C1 p) as Hsp1.
  1: apply Hsp.
  assert (forall p, In p ps -> strongly_projectable Defs C2 p) as Hsp2.
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
  elim (epp_C_Cond_Send_inv _ _ _ _ _ _ HC HC1 HC2 _ _ _ _ _ H6).
  intros. destroy H0. rename x0 into Bp1, x1 into Bp2, H1 into Hp1, H2 into Hp2, H0 into Hp'.
  elim (epp_C_Cond_Recv_inv _ _ _ _ _ _ HC HC1 HC2 _ _ _ _ _ H9).
  intros. destroy H0. rename x0 into Bq1, x1 into Bq2, H1 into Hq1, H2 into Hq2, H0 into Hq'.
  assert (forall p, In p (CCC_pn C1 (fun X => fst (Defs X))) -> In p ps) as Hin1.
  1: intros. apply Hin. simpl; sup; sup.
  assert (forall p, In p (CCC_pn C2 (fun X => fst (Defs X))) -> In p ps) as Hin2.
  1: intros. apply Hin. simpl; sup; sup.
  elim (IHC1 HC1 Hsp1 Hin1 (eval_on_state Ev e s p) (epp_C Defs ps C1 HC1 ~~ p ~~ q | p[Bp1] | q[Bq1]))%SP; intros.
  rename x0 into C1'. destroy H0.
  elim (IHC2 HC2 Hsp2 Hin2 (eval_on_state Ev e s p) (Network_rm _ (Network_rm _ (epp_C Defs ps C2 HC2) p) q | p[Bp2] | q[Bq2]))%SP; intros.
  rename x0 into C2'. destroy H2. clear IHC1 IHC2.
  exists (If p' ?? b Then C1' Else C2'); repeat split.
  * apply C_Delay_Cond; repeat split; auto.
  * intros. eapply Network_eq_trans. apply H10. rewrite <- H4.
    intro r. elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim ((@eq_dec Pid) q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec (@eq_dec Pid) r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
    3: elim ((@eq_dec Pid) p' r); intro Hp'r.
    - rewrite <- Hpr, Network_rm_add_2_p; auto.
      apply inject_inj.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H2, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    - rewrite <- Hqr, Network_rm_add_2_q; auto.
      apply inject_inj.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H2, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    - rewrite <- Hp'r; intro.
      apply inject_inj.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H2; auto.
      rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC)
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC); auto.
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2); auto.
    - intro. apply inject_inj.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC)
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC); auto.
      rewrite <- H0, <- H2; auto.
      rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2); auto.
  * apply S_Com with (a:ann Sig') Bp2 a' Bq2; auto.
    apply Network_eq_refl.
  * apply S_Com with (a:ann Sig') Bp1 a' Bq1; auto.
    apply Network_eq_refl.
+ exfalso.
  inversion H.
  elim (In_dec (@eq_dec Pid) p ps); intros.
  elim (In_dec (@eq_dec Pid) p (fst (Defs t))); intros.
  rewrite epp_C_Call in H6; auto. inversion H6.
  rewrite epp_C_Call_out in H6; auto. inversion H6.
  rewrite epp_C_out in H6; auto. inversion H6.
+ inversion H. rewrite <- H1 in H. unfold v1; unfold v1 in H, H11.
  clear s'0 H8 N'0 H7 x0 H3 q0 H2 v v1 H1 p0 H0 s0 H5.
  rename l into ps', t into X.
  assert (projectable_C Defs ps C) as HC'.
  1: { red. rewrite Forall_forall. intro.
    induction x0 as (r,Br). unfold epp_list; rewrite in_map_iff.
    intro. destroy H0. inversion H1. simpl.
    elim (Hsp r); auto; intros.
    apply strongly_projectable_C; auto.
    rewrite <- H3; auto.
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
  assert (forall p, In p ps -> strongly_projectable Defs C p) as Hsp'.
  1: apply Hsp.
  assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp' Hin' (eval_on_state Ev e s p) (Network_rm _ (Network_rm _ (epp_C Defs ps C HC') p) q | p[B] | q[B']))%SP; intros.
  rename x0 into C'. destroy H0.
  exists (RT_Call X ps' C'); repeat split.
  * apply C_Delay_Call; repeat split; auto.
    apply disjoint_ps_char. simpl.
    intros r Hr. split; intro H'; rewrite H' in Hr; auto.
  * intros. eapply Network_eq_trans. apply H10. rewrite <- H4.
    assert (projectable_C Defs ps C').
    1: apply strongly_projectable_C'; intros. eapply CCC_To_strongly_projectable_Com; eauto.
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

Lemma SP_To_bproj_Sel_l : forall Defs Defs' ps C HC s N' s' p q,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) ->
  SP_To _ Defs' (epp_C Defs ps C HC) s (R_Sel p q left) N' s' ->
  exists C', CCC_To _ Defs C s (R_Sel p q left) C' s'
  /\ forall HC', (N' == (epp_C Defs ps C' HC'))%SP.
Proof.
intros.
rename H into Hsp, H0 into Hin, H1 into H.
revert N' H.
induction C; intros. induction e.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  rename t into a'', t0 into p', t2 into q', t1 into e, t3 into v'.
  generalize (projectable_C_inv_Com Defs ps p' e q' v' a'' C HC); intro HC'.
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
  assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (Network_rm _ (Network_rm _ (epp_C Defs ps C HC') p) q | p[B] | q[Bl]))%SP; intros.
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
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite <- H0, Network_rm_add_2_p; auto.
    ++ rewrite <- Hqr, Network_rm_add_2_q; auto.
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite <- H0, Network_rm_add_2_q; auto.
    ++ rewrite <- Hp'r; intro.
       rewrite epp_C_Com_p with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_p with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
    ++ rewrite <- Hq'r; intro. rewrite <- Hq'r in Hp'r.
       rewrite epp_C_Com_q with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_q with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
    ++ rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
  * apply S_LSel with (a:ann Sig') B a' Bl Br; auto.
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC) in H2; inversion H2; auto.
    apply epp_C_wd.
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC) in H3; auto.
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
      elim (collapse_char'); simpl; intro.
      induction a1. revert p0. repeat rewrite DecType_eq.
      intros. induction x, l; inversion H2.
      1,2: inversion p0; auto.
      rewrite <- H11 in H5; inversion H5.
      (* absurd case *)
      exfalso. clear H H3 H6 H4.
      apply projectable_C_use' with (p:=p) in HC; auto.
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
  - generalize (projectable_C_inv_Sel _ _ _ _ _ _ _ HC); intro HC'.
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
    assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
    1: intros. apply Hin. simpl; sup.
    elim (IHC HC' Hsp Hin' (Network_rm _ (Network_rm _ (epp_C Defs ps C HC') p) q | p[B] | q[Bl]))%SP; intros.
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
         rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
         rewrite <- H0, Network_rm_add_2_p; auto.
      ++ rewrite <- Hqr, Network_rm_add_2_q; auto.
        rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
        rewrite <- H0, Network_rm_add_2_q; auto.
      ++ rewrite <- Hp'r; intro.
         rewrite epp_C_Sel_p with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
         rewrite epp_C_Sel_p with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
      ++ rewrite <- Hq'r; intro. rewrite <- Hq'r in Hp'r.
          induction l.
         1: rewrite epp_C_Sel_ql with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
         1: rewrite epp_C_Sel_ql with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC); auto.
         2: rewrite epp_C_Sel_qr with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
         2: rewrite epp_C_Sel_qr with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC); auto.
         all: rewrite <- H0, Network_rm_add_2_out; auto.
         all: rewrite epp_C_wd with (H':=HC'); auto.
      ++ rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
         rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
    * apply S_LSel with (a:ann Sig') B a' Bl Br; auto.
      rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC) in H2; inversion H2; auto.
      apply epp_C_wd.
      rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC) in H3; auto.
      etransitivity. 2: apply H3.
      apply epp_C_wd.
      apply Network_eq_refl.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  elim (epp_C_Sel_Branching_l _ _ _ _ _ _ _ _ _ _ H2 H3); intros.
  rewrite H1 in H3; clear Br H1 H0.
  rename t into p', t0 into b.
  generalize (projectable_C_inv_Then _ _ _ _ _ _ HC); intro HC1.
  generalize (projectable_C_inv_Else _ _ _ _ _ _ HC); intro HC2.
  assert (forall p, In p ps -> strongly_projectable Defs C1 p) as Hsp1.
  1: apply Hsp.
  assert (forall p, In p ps -> strongly_projectable Defs C2 p) as Hsp2.
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
  elim (epp_C_Cond_Sel_inv _ _ _ _ _ _ HC HC1 HC2 _ _ _ _ _ H2).
  intros. destroy H0. rename x into Bp1, x0 into Bp2, H1 into Hp1, H5 into Hp2, H0 into Hp'.
  elim (epp_C_Cond_Branching_l_inv _ _ _ _ _ _ HC HC1 HC2 _ _ _ _ H3).
  intros. destroy H0. rename x into Bq1, x0 into Bq2, H1 into Hq1, H5 into Hq2, H0 into Hq'.
  assert (forall p, In p (CCC_pn C1 (fun X => fst (Defs X))) -> In p ps) as Hin1.
  1: intros. apply Hin. simpl; sup; sup.
  assert (forall p, In p (CCC_pn C2 (fun X => fst (Defs X))) -> In p ps) as Hin2.
  1: intros. apply Hin. simpl; sup; sup.
  elim (IHC1 HC1 Hsp1 Hin1 (epp_C Defs ps C1 HC1 ~~ p ~~ q | p[Bp1] | q[Bq1]))%SP; intros.
  rename x into C1'. destroy H0.
  elim (IHC2 HC2 Hsp2 Hin2 (Network_rm _ (Network_rm _ (epp_C Defs ps C2 HC2) p) q | p[Bp2] | q[Bq2]))%SP; intros.
  rename x into C2'. destroy H5. clear IHC1 IHC2.
  exists (If p' ?? b Then C1' Else C2'); repeat split.
  * apply C_Delay_Cond; repeat split; auto.
  * intros. eapply Network_eq_trans. apply H6. rewrite <- H4.
    intro r. elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim ((@eq_dec Pid) q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec (@eq_dec Pid) r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
    3: elim ((@eq_dec Pid) p' r); intro Hp'r.
    - rewrite <- Hpr, Network_rm_add_2_p; auto.
      apply inject_inj.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H5, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    - rewrite <- Hqr, Network_rm_add_2_q; auto.
      apply inject_inj.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H5, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    - rewrite <- Hp'r; intro.
      apply inject_inj.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H5; auto.
      rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC)
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC); auto.
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2); auto.
    - intro. apply inject_inj.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC)
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC); auto.
      rewrite <- H0, <- H5; auto.
      rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2); auto.
  * apply S_LSel with (a:ann Sig') Bp2 a' Bq2 None; auto.
    apply Network_eq_refl.
  * apply S_LSel with (a:ann Sig') Bp1 a' Bq1 None; auto.
    apply Network_eq_refl.
+ exfalso.
  inversion H.
  elim (In_dec (@eq_dec Pid) p ps); intros.
  elim (In_dec (@eq_dec Pid) p (fst (Defs t))); intros.
  rewrite epp_C_Call in H2; auto. inversion H2.
  rewrite epp_C_Call_out in H2; auto. inversion H2.
  rewrite epp_C_out in H2; auto. inversion H2.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  rename l into ps', t into X.
  assert (projectable_C Defs ps C) as HC'.
  1: { red. rewrite Forall_forall. intro.
    induction x as (r,B'). unfold epp_list; rewrite in_map_iff.
    intro. destroy H0. inversion H1. simpl.
    elim (Hsp r); auto; intros.
    apply strongly_projectable_C; auto.
    rewrite <- H7; auto.
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
  assert (forall p, In p ps -> strongly_projectable Defs C p) as Hsp'.
  1: apply Hsp.
  assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp' Hin' (Network_rm _ (Network_rm _ (epp_C Defs ps C HC') p) q | p[B] | q[Bl]))%SP; intros.
  rename x into C'. destroy H0.
  exists (RT_Call X ps' C'); repeat split.
  * apply C_Delay_Call; repeat split; auto.
    apply disjoint_ps_char. simpl.
    intros r Hr. split; intro H'; rewrite H' in Hr; auto.
  * intros. eapply Network_eq_trans. apply H6. rewrite <- H4.
    assert (projectable_C Defs ps C').
    1: apply strongly_projectable_C'; intros. eapply CCC_To_strongly_projectable_Sel; eauto.
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

Lemma SP_To_bproj_Sel_r : forall Defs Defs' ps C HC s N' s' p q,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) ->
  SP_To _ Defs' (epp_C Defs ps C HC) s (R_Sel p q right) N' s' ->
  exists C', CCC_To _ Defs C s (R_Sel p q right) C' s'
  /\ forall HC', (N' == (epp_C Defs ps C' HC'))%SP.
Proof.
intros.
rename H into Hsp, H0 into Hin, H1 into H.
revert N' H.
induction C; intros. induction e.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  rename t into a'', t0 into p', t2 into q', t1 into e, t3 into v'.
  generalize (projectable_C_inv_Com Defs ps p' e q' v' a'' C HC); intro HC'.
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
  assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (Network_rm _ (Network_rm _ (epp_C Defs ps C HC') p) q | p[B] | q[Br]))%SP; intros.
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
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite <- H0, Network_rm_add_2_p; auto.
    ++ rewrite <- Hqr, Network_rm_add_2_q; auto.
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite <- H0, Network_rm_add_2_q; auto.
    ++ rewrite <- Hp'r; intro.
       rewrite epp_C_Com_p with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_p with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
    ++ rewrite <- Hq'r; intro. rewrite <- Hq'r in Hp'r.
       rewrite epp_C_Com_q with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_q with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
    ++ rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0); auto.
       rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC); auto.
       rewrite <- H0; auto.
       rewrite Network_rm_add_2_out; auto.
       rewrite epp_C_wd with (H':=HC'); auto.
  * apply S_RSel with (a:ann Sig') B a' Bl Br; auto.
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC) in H2; inversion H2; auto.
    apply epp_C_wd.
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC) in H3; auto.
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
      elim (collapse_char'); simpl; intro.
      induction a1. revert p0. repeat rewrite DecType_eq.
      intros. induction x, l; inversion H2.
      1,2: inversion p0; auto.
      rewrite <- H11 in H5; inversion H5.
      (* absurd case *)
      exfalso. clear H H3 H6 H4.
      apply projectable_C_use' with (p:=p) in HC; auto.
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
  - generalize (projectable_C_inv_Sel _ _ _ _ _ _ _ HC); intro HC'.
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
    assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
    1: intros. apply Hin. simpl; sup.
    elim (IHC HC' Hsp Hin' (Network_rm _ (Network_rm _ (epp_C Defs ps C HC') p) q | p[B] | q[Br]))%SP; intros.
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
         rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
         rewrite <- H0, Network_rm_add_2_p; auto.
      ++ rewrite <- Hqr, Network_rm_add_2_q; auto.
        rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
        rewrite <- H0, Network_rm_add_2_q; auto.
      ++ rewrite <- Hp'r; intro.
         rewrite epp_C_Sel_p with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
         rewrite epp_C_Sel_p with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
      ++ rewrite <- Hq'r; intro. rewrite <- Hq'r in Hp'r.
          induction l.
         1: rewrite epp_C_Sel_ql with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
         1: rewrite epp_C_Sel_ql with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC); auto.
         2: rewrite epp_C_Sel_qr with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
         2: rewrite epp_C_Sel_qr with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC); auto.
         all: rewrite <- H0, Network_rm_add_2_out; auto.
         all: rewrite epp_C_wd with (H':=HC'); auto.
      ++ rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0); auto.
         rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC); auto.
         rewrite <- H0; auto.
         rewrite Network_rm_add_2_out; auto.
         rewrite epp_C_wd with (H':=HC'); auto.
    * apply S_RSel with (a:ann Sig') B a' Bl Br; auto.
      rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC) in H2; inversion H2; auto.
      apply epp_C_wd.
      rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC) in H3; auto.
      etransitivity. 2: apply H3.
      apply epp_C_wd.
      apply Network_eq_refl.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  elim (epp_C_Sel_Branching_r _ _ _ _ _ _ _ _ _ _ H2 H3); intros.
  rewrite H0 in H3; clear Bl H1 H0.
  rename t into p', t0 into b.
  generalize (projectable_C_inv_Then _ _ _ _ _ _ HC); intro HC1.
  generalize (projectable_C_inv_Else _ _ _ _ _ _ HC); intro HC2.
  assert (forall p, In p ps -> strongly_projectable Defs C1 p) as Hsp1.
  1: apply Hsp.
  assert (forall p, In p ps -> strongly_projectable Defs C2 p) as Hsp2.
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
  elim (epp_C_Cond_Sel_inv _ _ _ _ _ _ HC HC1 HC2 _ _ _ _ _ H2).
  intros. destroy H0. rename x into Bp1, x0 into Bp2, H1 into Hp1, H5 into Hp2, H0 into Hp'.
  elim (epp_C_Cond_Branching_r_inv _ _ _ _ _ _ HC HC1 HC2 _ _ _ _ H3).
  intros. destroy H0. rename x into Bq1, x0 into Bq2, H1 into Hq1, H5 into Hq2, H0 into Hq'.
  assert (forall p, In p (CCC_pn C1 (fun X => fst (Defs X))) -> In p ps) as Hin1.
  1: intros. apply Hin. simpl; sup; sup.
  assert (forall p, In p (CCC_pn C2 (fun X => fst (Defs X))) -> In p ps) as Hin2.
  1: intros. apply Hin. simpl; sup; sup.
  elim (IHC1 HC1 Hsp1 Hin1 (epp_C Defs ps C1 HC1 ~~ p ~~ q | p[Bp1] | q[Bq1]))%SP; intros.
  rename x into C1'. destroy H0.
  elim (IHC2 HC2 Hsp2 Hin2 (Network_rm _ (Network_rm _ (epp_C Defs ps C2 HC2) p) q | p[Bp2] | q[Bq2]))%SP; intros.
  rename x into C2'. destroy H5. clear IHC1 IHC2.
  exists (If p' ?? b Then C1' Else C2'); repeat split.
  * apply C_Delay_Cond; repeat split; auto.
  * intros. eapply Network_eq_trans. apply H6. rewrite <- H4.
    intro r. elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim ((@eq_dec Pid) q r); intro Hqr.
    3: rewrite Network_rm_add_2_out, H4; auto.
    3: elim (In_dec (@eq_dec Pid) r ps); [idtac | intro; repeat rewrite epp_C_out; auto].
    3: elim ((@eq_dec Pid) p' r); intro Hp'r.
    - rewrite <- Hpr, Network_rm_add_2_p; auto.
      apply inject_inj.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H5, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    - rewrite <- Hqr, Network_rm_add_2_q; auto.
      apply inject_inj.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H5, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    - rewrite <- Hp'r; intro.
      apply inject_inj.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite <- H0, <- H5; auto.
      rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
      rewrite epp_C_Cond_p with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC)
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC); auto.
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2); auto.
    - intro. apply inject_inj.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC')
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC'); auto.
      rewrite epp_C_Cond_r with (HC1:=projectable_C_inv_Then _ _ _ _ _ _ HC)
                                (HC2:=projectable_C_inv_Else _ _ _ _ _ _ HC); auto.
      rewrite <- H0, <- H5; auto.
      rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
      rewrite epp_C_wd with (H':=HC1), epp_C_wd with (H':=HC2); auto.
  * apply S_RSel with (a:ann Sig') Bp2 a' None Bq2; auto.
    apply Network_eq_refl.
  * apply S_RSel with (a:ann Sig') Bp1 a' None Bq1; auto.
    apply Network_eq_refl.
+ exfalso.
  inversion H.
  elim (In_dec (@eq_dec Pid) p ps); intros.
  elim (In_dec (@eq_dec Pid) p (fst (Defs t))); intros.
  rewrite epp_C_Call in H2; auto. inversion H2.
  rewrite epp_C_Call_out in H2; auto. inversion H2.
  rewrite epp_C_out in H2; auto. inversion H2.
+ inversion H.
  clear s'0 H8 N'0 H7 q0 H1 p0 H0 s0 H5.
  rename l into ps', t into X.
  assert (projectable_C Defs ps C) as HC'.
  1: { red. rewrite Forall_forall. intro.
    induction x as (r,B'). unfold epp_list; rewrite in_map_iff.
    intro. destroy H0. inversion H1. simpl.
    elim (Hsp r); auto; intros.
    apply strongly_projectable_C; auto.
    rewrite <- H7; auto.
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
  assert (forall p, In p ps -> strongly_projectable Defs C p) as Hsp'.
  1: apply Hsp.
  assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp' Hin' (Network_rm _ (Network_rm _ (epp_C Defs ps C HC') p) q | p[B] | q[Br]))%SP; intros.
  rename x into C'. destroy H0.
  exists (RT_Call X ps' C'); repeat split.
  * apply C_Delay_Call; repeat split; auto.
    apply disjoint_ps_char. simpl.
    intros r Hr. split; intro H'; rewrite H' in Hr; auto.
  * intros. eapply Network_eq_trans. apply H6. rewrite <- H4.
    assert (projectable_C Defs ps C').
    1: apply strongly_projectable_C'; intros. eapply CCC_To_strongly_projectable_Sel; eauto.
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

Lemma SP_To_bproj_Cond : forall Defs Defs' ps C HC s N' s' p,
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) ->
  SP_To _ Defs' (epp_C Defs ps C HC) s (R_Cond p) N' s' ->
  exists C', CCC_To _ Defs C s (R_Cond p) C' s'
  /\ forall HC', (N' >> (epp_C Defs ps C' HC'))%SP.
Proof.
intros.
rename H into Hsp, H0 into Hin, H1 into H.
revert N' H.
induction C; intros. induction e. 1,2,3,5: inversion H. (* double cases *)
+ clear s'0 H8 N'0 H7 p0 H0 s0 H5 H.
  rename t into a'', t0 into p', t2 into q', t3 into v', t1 into e.
  generalize (projectable_C_inv_Com Defs ps p' e q' v' a'' C HC); intro HC'.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H1. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H, epp_C_Com_p with (HC':=HC') in H1; auto.
    inversion H1. rewrite H; auto.
  assert (q' <> p) as Hq'p.
  1: intro. rewrite <- H, epp_C_Com_q with (HC':=HC') in H1.
    inversion H1. 1,2: rewrite H; auto.
  assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (Network_rm _ (epp_C Defs ps C HC') p | p[B1]))%SP ; intros.
  rename x into C'. destroy H.
  exists (p' # e --> q' $ v' @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros; intro r. rewrite H3.
    set (H':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0). clearbody H'.
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
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC) in H1; inversion H1; auto.
    apply epp_C_wd.
    apply Network_eq_refl.
+ clear s'0 H8 N'0 H7 p0 H0 s0 H5 H.
  rename t into a'', t0 into p', t2 into q', t3 into v', t1 into e.
  generalize (projectable_C_inv_Com Defs ps p' e q' v' a'' C HC); intro HC'.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H1. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H, epp_C_Com_p with (HC':=HC') in H1; auto.
    inversion H1. rewrite H; auto.
  assert (q' <> p) as Hq'p.
  1: intro. rewrite <- H, epp_C_Com_q with (HC':=HC') in H1.
    inversion H1. 1,2: rewrite H; auto.
  assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (Network_rm _ (epp_C Defs ps C HC') p | p[B2]))%SP; intros.
  rename x into C'. destroy H.
  exists (p' # e --> q' $ v' @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros; intro r. rewrite H3.
    set (H':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0). clearbody H'.
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
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC) in H1; inversion H1; auto.
    apply epp_C_wd.
    apply Network_eq_refl.
+ clear s'0 H8 N'0 H7 p0 H0 s0 H5 H.
  rename t into a'', t0 into p', t1 into q', t2 into l.
  generalize (projectable_C_inv_Sel Defs ps p' q' l a'' C HC); intro HC'.
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
  assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (Network_rm _ (epp_C Defs ps C HC') p | p[B1]))%SP; intros.
  rename x into C'. destroy H.
  exists (p' --> q' [l] @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros; intro r. rewrite H3.
    set (H':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0). clearbody H'.
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
      1: apply MB_Branching_Some_None with (Sig:=Sig'); auto.
      5: apply MB_Branching_None_Some with (Sig:=Sig'); auto.
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
    rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC) in H1; inversion H1; auto.
    apply epp_C_wd.
    apply Network_eq_refl.
+ clear s'0 H8 N'0 H7 p0 H0 s0 H5 H.
  rename t into a'', t0 into p', t1 into q', t2 into l.
  generalize (projectable_C_inv_Sel Defs ps p' q' l a'' C HC); intro HC'.
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
  assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  elim (IHC HC' Hsp Hin' (Network_rm _ (epp_C Defs ps C HC') p | p[B2]))%SP; intros.
  rename x into C'. destroy H.
  exists (p' --> q' [l] @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros; intro r. rewrite H3.
    set (H':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0). clearbody H'.
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
      1: apply MB_Branching_Some_None with (Sig:=Sig'); auto.
      5: apply MB_Branching_None_Some with (Sig:=Sig'); auto.
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
    rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC) in H1; inversion H1; auto.
    apply epp_C_wd.
    apply Network_eq_refl.
+ clear s'0 H8 N'0 H7 p0 H0 s0 H5 H.
  rename t into p', t0 into b0.
  assert (projectable_C Defs ps C1) as HC1.
  1: eapply projectable_C_inv_Then; eauto.
  assert (projectable_C Defs ps C2) as HC2.
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
      inversion H1. apply more_branches_refl'.
      rewrite Process_refl. apply epp_C_wd.
    * rewrite Par_proj1', Network_rm_out; auto.
      apply X_more_branches.
      rewrite epp_C_Cond_r with (HC1:=HC') (HC2:=HC2); auto.
      apply Xmerge_is_larger.
      fold (epp_C _ _ _ HC' r [\/] epp_C _ _ _ HC2 r).
      rewrite <- epp_C_Cond_r with (HC:=HC); auto.
      elim (projectable_C_use _ _ _ HC r); auto.
      intros. rewrite <- epp_C_bproj, H; auto.
      apply inject_not_undefined.
      apply Process_out; auto.
    * rewrite Par_proj1', Network_rm_out; auto.
      apply more_branches_refl'. repeat rewrite epp_C_out; auto.
      apply Process_out; auto.
  - assert (forall p, In p ps -> strongly_projectable Defs C1 p) as Hsp1.
    1: apply Hsp.
    assert (forall p, In p ps -> strongly_projectable Defs C2 p) as Hsp2.
    1: apply Hsp.
    clear Hsp.
    assert (p' <> p) as Hp'p. auto.
    (* get the remaining equalities *)
    elim (epp_C_Cond_Cond_inv _ _ _ _ _ _ _ HC HC1 HC2 _ _ _ H1); auto.
    intros. destroy H. rename x into B1t, x0 into B1e, x1 into B2t, x2 into B2e, H0 into Hp1, H5 into Hp2, H7 into Ht, H into He.
    assert (forall p, In p (CCC_pn C1 (fun X => fst (Defs X))) -> In p ps) as Hin1.
    1: intros. apply Hin. simpl; sup; sup.
    assert (forall p, In p (CCC_pn C2 (fun X => fst (Defs X))) -> In p ps) as Hin2.
    1: intros. apply Hin. simpl; sup; sup.
    elim (IHC1 HC1 Hsp1 Hin1 (epp_C Defs ps C1 HC1 ~~ p | p[B1t]))%SP; intros.
    rename x into C1'. destroy H.
    elim (IHC2 HC2 Hsp2 Hin2 (Network_rm _ (epp_C Defs ps C2 HC2) p | p[B2t]))%SP; intros.
    rename x into C2'. destroy H5. clear IHC1 IHC2.
    exists (If p' ?? b0 Then C1' Else C2'); repeat split.
    * apply (@C_Delay_Cond Sig); repeat split; simpl; auto.
    * intros. intro r. rewrite H3.
      assert (projectable_C Defs ps C1') as HC1'.
      1: eapply projectable_C_inv_Then; eauto.
      assert (projectable_C Defs ps C2') as HC2'.
      1: eapply projectable_C_inv_Else; eauto.
      elim ((@eq_dec Pid) r p); intro Hpr.
      2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
      2: elim ((@eq_dec Pid) p' r); intro Hp'r.
      ++ apply X_more_branches.
         generalize (H HC1' r) (H5 HC2' r).
         rewrite Hpr, Par_proj2, Par_proj2, Par_proj2; auto.
         2,3,4: apply Network_rm_In.
         repeat rewrite Process_refl. intros.
         rewrite epp_C_Cond_r with (HC1:=HC1') (HC2:=HC2'); auto.
         elim (more_branches_merge_extend _ _ _ _ _ _ H8 H9 Ht); auto.
         intros. destroy H10.
         rewrite H11. apply more_branches_X; auto.
      ++ generalize (H HC1' r) (H5 HC2' r).
         rewrite <- Hp'r. rewrite <- Hp'r in Hr, Hpr. clear r Hp'r.
         rewrite Par_proj1', Par_proj1', Par_proj1', Network_rm_out, Network_rm_out, Network_rm_out; auto.
         rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2); auto.
         rewrite epp_C_Cond_p with (HC1:=HC1') (HC2:=HC2'); auto.
         constructor; auto.
         all: apply Process_out; auto.
      ++ apply X_more_branches.
         generalize (more_branches_X _ _ _ (H HC1' r)) (more_branches_X _ _ _ (H5 HC2' r)).
         rewrite Par_proj1', Par_proj1', Par_proj1', Network_rm_out, Network_rm_out, Network_rm_out; auto.
         rewrite epp_C_Cond_r with (HC1:=HC1) (HC2:=HC2); auto.
         rewrite epp_C_Cond_r with (HC1:=HC1') (HC2:=HC2'); auto.
         intros. eapply Xmore_branches_merge_extend; eauto.
         fold (epp_C _ _ _ HC1 r [\/] epp_C _ _ _ HC2 r).
         rewrite <- epp_C_Cond_r with (HC:=HC); eauto.
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
  assert (projectable_C Defs ps C1) as HC1.
  1: eapply projectable_C_inv_Then; eauto.
  assert (projectable_C Defs ps C2) as HC2.
  1: eapply projectable_C_inv_Else; eauto.
  assert (In p ps) as Hpps.
  1: { revert H1. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  elim ((@eq_dec Pid) p p'); intro Hpp'.
  - revert dependent HC. revert Hsp Hin.
    rewrite <- Hpp'; clear p' Hpp'; intros.
    assert (b = b0).
    1: rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H1; inversion H1; auto.
    revert H2 H1. rewrite H. clear b H; intros. rename b0 into b.
    exists C2. repeat split.
    apply (@C_Else Sig); auto.
    intros; intro r. rewrite H3.
    elim ((@eq_dec Pid) r p); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
    * rewrite Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2) in H1; auto.
      inversion H1. apply more_branches_refl'.
      rewrite Process_refl; apply epp_C_wd.
    * rewrite Par_proj1', Network_rm_out; auto.
      apply X_more_branches.
      rewrite epp_C_Cond_r with (HC1:=HC1) (HC2:=HC'); auto.
      apply Xmerge_is_larger'.
      fold (epp_C _ _ _ HC1 r [\/] epp_C _ _ _ HC' r).
      rewrite <- epp_C_Cond_r with (HC:=HC); auto.
      elim (projectable_C_use _ _ _ HC r); auto.
      intros. rewrite <- epp_C_bproj, H; auto.
      apply inject_not_undefined.
      apply Process_out; auto.
    * rewrite Par_proj1', Network_rm_out; auto.
      apply more_branches_refl'. repeat rewrite epp_C_out; auto.
      apply Process_out; auto.
  - assert (forall p, In p ps -> strongly_projectable Defs C1 p) as Hsp1.
    1: apply Hsp.
    assert (forall p, In p ps -> strongly_projectable Defs C2 p) as Hsp2.
    1: apply Hsp.
    clear Hsp.
    assert (p' <> p) as Hp'p. auto.
    (* get the remaining equalities *)
    elim (epp_C_Cond_Cond_inv _ _ _ _ _ _ _ HC HC1 HC2 _ _ _ H1); auto.
    intros. destroy H. rename x into B1t, x0 into B1e, x1 into B2t, x2 into B2e, H0 into Hp1, H5 into Hp2, H7 into Ht, H into He.
    assert (forall p, In p (CCC_pn C1 (fun X => fst (Defs X))) -> In p ps) as Hin1.
    1: intros. apply Hin. simpl; sup; sup.
    assert (forall p, In p (CCC_pn C2 (fun X => fst (Defs X))) -> In p ps) as Hin2.
    1: intros. apply Hin. simpl; sup; sup.
    elim (IHC1 HC1 Hsp1 Hin1 (epp_C Defs ps C1 HC1 ~~ p | p[B1e]))%SP; intros.
    rename x into C1'. destroy H.
    elim (IHC2 HC2 Hsp2 Hin2 (Network_rm _ (epp_C Defs ps C2 HC2) p | p[B2e]))%SP; intros.
    rename x into C2'. destroy H5. clear IHC1 IHC2.
    exists (If p' ?? b0 Then C1' Else C2'); repeat split.
    * apply C_Delay_Cond; repeat split; simpl; auto.
    * intros. intro r. rewrite H3.
      assert (projectable_C Defs ps C1') as HC1'.
      1: eapply projectable_C_inv_Then; eauto.
      assert (projectable_C Defs ps C2') as HC2'.
      1: eapply projectable_C_inv_Else; eauto.
      elim ((@eq_dec Pid) r p); intro Hpr.
      2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
      2: elim ((@eq_dec Pid) p' r); intro Hp'r.
      ++ apply X_more_branches.
         generalize (H HC1' r) (H5 HC2' r).
         rewrite Hpr, Par_proj2, Par_proj2, Par_proj2; auto.
         2,3,4: apply Network_rm_In.
         repeat rewrite Process_refl. intros.
         rewrite epp_C_Cond_r with (HC1:=HC1') (HC2:=HC2'); auto.
         elim (more_branches_merge_extend _ _ _ _ _ _ H8 H9 He); auto.
         intros. destroy H10.
         rewrite H11. apply more_branches_X; auto.
      ++ generalize (H HC1' r) (H5 HC2' r).
         rewrite <- Hp'r. rewrite <- Hp'r in Hr, Hpr. clear r Hp'r.
         rewrite Par_proj1', Par_proj1', Par_proj1', Network_rm_out, Network_rm_out, Network_rm_out; auto.
         rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2); auto.
         rewrite epp_C_Cond_p with (HC1:=HC1') (HC2:=HC2'); auto.
         constructor; auto.
         all: apply Process_out; auto.
      ++ apply X_more_branches.
         generalize (more_branches_X _ _ _ (H HC1' r)) (more_branches_X _ _ _ (H5 HC2' r)).
         rewrite Par_proj1', Par_proj1', Par_proj1', Network_rm_out, Network_rm_out, Network_rm_out; auto.
         rewrite epp_C_Cond_r with (HC1:=HC1) (HC2:=HC2); auto.
         rewrite epp_C_Cond_r with (HC1:=HC1') (HC2:=HC2'); auto.
         intros. eapply Xmore_branches_merge_extend; eauto.
         fold (epp_C _ _ _ HC1 r [\/] epp_C _ _ _ HC2 r).
         rewrite <- epp_C_Cond_r with (HC:=HC); eauto.
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
  assert (projectable_C Defs ps C) as HC'.
  1: apply strongly_projectable_C'. apply Hsp.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H1. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (~In p ps').
  1: intro. rewrite epp_C_RT_Call in H1; auto; inversion H1.
  assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  assert (forall p, In p ps -> strongly_projectable Defs C p) as Hsp'. apply Hsp.
  elim (IHC HC' Hsp' Hin' (Network_rm _ (epp_C Defs ps C HC') p | p[B1]))%SP; intros.
  rename x into C'. destroy H0.
  exists (RT_Call X ps' C'); repeat split.
  * apply C_Delay_Call; repeat split; auto.
    apply disjoint_ps_char.
    intros; intro. rewrite H8 in H7; auto.
  * intros; intro r. rewrite H3.
    assert (projectable_C Defs ps C') as H'.
    1: apply strongly_projectable_C'; intros. eapply CCC_To_strongly_projectable_Cond; eauto.
    generalize (H0 H' r); clear H0; intro.
    elim ((@eq_dec Pid) r p); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps'); intro Hr.
    - rewrite Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite Hpr, Par_proj2 in H0. 2: apply Network_rm_In.
      rewrite epp_C_RT_Call_out with (HC':=H'); auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H0; auto.
      apply more_branches_refl'.
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
  assert (projectable_C Defs ps C) as HC'.
  1: apply strongly_projectable_C'. apply Hsp.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H1. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (~In p ps').
  1: intro. rewrite epp_C_RT_Call in H1; auto; inversion H1.
  assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  assert (forall p, In p ps -> strongly_projectable Defs C p) as Hsp'. apply Hsp.
  elim (IHC HC' Hsp' Hin' (Network_rm _ (epp_C Defs ps C HC') p | p[B2]))%SP; intros.
  rename x into C'. destroy H0.
  exists (RT_Call X ps' C'); repeat split.
  * apply C_Delay_Call; repeat split; auto.
    apply disjoint_ps_char.
    intros; intro. rewrite H8 in H7; auto.
  * intros; intro r. rewrite H3.
    assert (projectable_C Defs ps C') as H'.
    1: apply strongly_projectable_C'; intros. eapply CCC_To_strongly_projectable_Cond; eauto.
    generalize (H0 H' r); clear H0; intro.
    elim ((@eq_dec Pid) r p); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps'); intro Hr.
    - rewrite Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite Hpr, Par_proj2 in H0. 2: apply Network_rm_In.
      rewrite epp_C_RT_Call_out with (HC':=H'); auto.
    - rewrite Par_proj1', Network_rm_out; auto.
      rewrite Par_proj1', Network_rm_out in H0; auto.
      apply more_branches_refl'.
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
  1,3: elim (In_dec (@eq_dec Pid) p (fst (Defs t))); intros.
  1,3: rewrite epp_C_Call in H1; auto.
  3,4: rewrite epp_C_Call_out in H1; auto.
  5,6: rewrite epp_C_out in H1; auto.
  all: inversion H1.
+ exfalso.
  inversion H.
  all: rewrite epp_C_End in H1; inversion H1.
Qed.

Lemma SP_To_bproj_Call : forall Defs (Defs':DefSetB Sig') ps C HC s N' s' p X Xs,
  Choreography_WF C -> within_Xs Xs C -> In X Xs ->
  (forall p, In p ps -> strongly_projectable Defs C p) ->
  (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) ->
  (forall p HX, Defs' (X,p) = epp_C Defs ps (snd (Defs X)) HX p) ->
  (forall p X, In p (CCC_pn (snd (Defs X)) (fun Y => fst (Defs Y))) -> In p (fst (Defs X))) ->
  (forall X, In X Xs -> projectable_C Defs ps (snd (Defs X))) ->
  (forall X, In X Xs -> initial (snd (Defs X))
    /\ forall p, In p (fst (Defs X)) -> In p ps) ->
  SP_To _ Defs' (epp_C Defs ps C HC) s (R_Call ((X,p):recvar Sig') p) N' s' ->
  exists C', CCC_To _ Defs C s (R_Call X p) C' s'
  /\ forall HC', (N' >> epp_C Defs ps C' HC')%SP.
Proof.
intros.
rename H into HWF, H0 into HCXs, H1 into HXs, H2 into Hsp, H3 into Hin,
  H4 into HDefs, H5 into Hnames, H6 into HDefs', H7 into Hinit, H8 into H.
revert N' H.
induction C; intros. induction e.
+ inversion H.
  clear s'0 H7 N'0 H6 X0 H0 s0 H4 p0 H1.
  rename t into a'', t0 into p', t2 into q', t1 into e, t3 into v.
  generalize (projectable_C_inv_Com Defs ps p' e q' v a'' C HC); intro HC'.
  (* get the remaining equalities *)
  assert (In p ps) as Hpps.
  1: { revert H2. unfold epp_C. elim In_dec; simpl; auto. discriminate. }
  assert (p' <> p) as Hp'p.
  1: intro. rewrite <- H0, epp_C_Com_p with (HC':=HC') in H2; auto.
    inversion H2. rewrite H0; auto.
  assert (q' <> p) as Hq'p.
  1: intro. rewrite <- H0, epp_C_Com_q with (HC':=HC') in H2.
    inversion H2. rewrite H0; auto. rewrite H0; auto.
  assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  apply Choreography_WF_eta in HWF.
  elim (IHC HC' HWF HCXs Hsp Hin' (Network_rm _ (epp_C Defs ps C HC') p | Process Sig' p (Defs' (X,p))))%SP; intros.
  rename x into C'. destroy H0.
  exists (p' # e --> q' $ v @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros. intro r. rewrite H5. 
    set (H':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC'0).
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
    - intro. apply more_branches_refl'.
      rewrite Par_proj1', Network_rm_out; auto.
      2: apply Process_out; auto.
      rewrite epp_C_out, epp_C_out; auto.
  * apply (@S_Call Sig'); auto.
    rewrite epp_C_Com_r with (HC':=projectable_C_inv_Com _ _ _ _ _ _ _ _ HC) in H2; inversion H2; auto.
    apply epp_C_wd.
    apply Network_eq_refl.
+ inversion H.
  clear s'0 H7 N'0 H6 X0 H0 s0 H4 p0 H1.
  rename t into a'', t0 into p', t1 into q', t2 into l.
  generalize (projectable_C_inv_Sel Defs ps p' q' l a'' C HC); intro HC'.
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
  assert (forall p, In p (CCC_pn C (fun X => fst (Defs X))) -> In p ps) as Hin'.
  1: intros. apply Hin. simpl; sup.
  apply Choreography_WF_eta in HWF.
  elim (IHC HC' HWF HCXs Hsp Hin' (Network_rm _ (epp_C Defs ps C HC') p | (Process Sig' p (Defs' (X,p)))))%SP; intros.
  rename x into C'. destroy H0.
  exists (p' --> q'[l] @ a'';; C'); repeat split.
  * apply C_Delay_Eta; repeat split; auto.
  * intros. intro r. rewrite H5.
    set (H':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC'0).
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
      apply MB_Branching_Some_None with (Sig := Sig'); auto.
      1,2,3,4: rewrite Hq'r; auto.
      rewrite epp_C_Sel_qr with (HC':=H'), epp_C_Sel_qr with (HC':=HC'); auto.
      apply MB_Branching_None_Some with (Sig := Sig'); auto.
      1,2,3,4: rewrite Hq'r; auto.
    - rewrite Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto.
      2,3: apply Process_out; auto.
      rewrite epp_C_Sel_r with (HC':=H'), epp_C_Sel_r with (HC':=HC'); auto.
    - intro. apply more_branches_refl'.
      rewrite Par_proj1', Network_rm_out; auto.
      2: apply Process_out; auto.
      rewrite epp_C_out, epp_C_out; auto.
  * apply S_Call; auto.
    rewrite epp_C_Sel_r with (HC':=projectable_C_inv_Sel _ _ _ _ _ _ _ HC) in H2; inversion H2; auto.
    apply epp_C_wd.
    apply Network_eq_refl.
+ inversion H.
  clear s'0 H7 N'0 H6 p0 H1 X0 H0 s0 H4.
  rename t into p', t0 into b.
  generalize (projectable_C_inv_Then _ _ _ _ _ _ HC); intro HC1.
  generalize (projectable_C_inv_Else _ _ _ _ _ _ HC); intro HC2.
  assert (forall p, In p ps -> strongly_projectable Defs C1 p) as Hsp1.
  1: apply Hsp.
  assert (forall p, In p ps -> strongly_projectable Defs C2 p) as Hsp2.
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
  assert (forall p, In p (CCC_pn C1 (fun X => fst (Defs X))) -> In p ps) as Hin1.
  1: intros. apply Hin. simpl; sup; sup.
  assert (forall p, In p (CCC_pn C2 (fun X => fst (Defs X))) -> In p ps) as Hin2.
  1: intros. apply Hin. simpl; sup; sup.
  inversion HCXs. rename H0 into HCXs1, H1 into HCXs2.
  elim (IHC1 HC1 HWF1 HCXs1 Hsp1 Hin1 (epp_C Defs ps C1 HC1 ~~ p | Process Sig' p (Defs' (X,p))))%SP; intros.
  rename x into C1'. destroy H0.
  elim (IHC2 HC2 HWF2 HCXs2 Hsp2 Hin2 (Network_rm _ (epp_C Defs ps C2 HC2) p | Process Sig' p (Defs' (X,p))))%SP; intros.
  rename x into C2'. destroy H4. clear IHC1 IHC2.
  exists (If p' ?? b Then C1' Else C2'); repeat split.
  * apply C_Delay_Cond; repeat split; auto.
  * intros. intro r. rewrite H5.
    set (H1':=projectable_C_inv_Then _ _ _ _ _ _ HC').
    generalize (H0 H1' r); clear H0.
    set (H2':=projectable_C_inv_Else _ _ _ _ _ _ HC').
    generalize (H4 H2' r); clear H4.
    elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r ps); intro Hr.
    2: elim ((@eq_dec Pid) p' r); intro Hp'r.
    - rewrite <- Hpr, Par_proj2, Par_proj2, Par_proj2. 2,3,4: apply Network_rm_In.
      intros. elim (more_branches_has_lub _ _ _ _ H0 H4); intros.
      destroy H7.
      rewrite merge_comm, <- epp_C_Cond_r with (HC:=HC') in H9; auto.
      apply inject_inj in H9. rewrite H9; auto.
    - rewrite <- Hp'r, Par_proj1', Par_proj1', Par_proj1', Network_rm_out, Network_rm_out, Network_rm_out; auto.
      2,3,4: apply Process_out; auto.
      rewrite epp_C_Cond_p with (HC1:=HC1) (HC2:=HC2). 2: rewrite Hp'r; auto.
      rewrite epp_C_Cond_p with (HC1:=H1') (HC2:=H2'). 2: rewrite Hp'r; auto.
      constructor; auto.
    - rewrite Par_proj1', Par_proj1', Par_proj1', Network_rm_out, Network_rm_out, Network_rm_out; auto.
      2,3,4: apply Process_out; auto.
      intros. apply X_more_branches.
      rewrite epp_C_Cond_r with (HC1:=HC1) (HC2:=HC2); auto.
      rewrite epp_C_Cond_r with (HC1:=H1') (HC2:=H2'); auto.
      apply more_branches_X in H0.
      apply more_branches_X in H4.
      generalize (epp_C_Cond_r _ _ _ _ _ _ HC HC1 HC2 r Hp'r); intro.
      symmetry in H7.
      apply (Xmore_branches_merge_extend _ _ _ _ _ _ H4 H0 H7).
    - intros. apply more_branches_refl'.
      rewrite Par_proj1', Network_rm_out; auto.
      2: apply Process_out; auto.
      rewrite epp_C_out, epp_C_out; auto.
  * apply S_Call; auto.
    assert (inject (epp_C _ _ _ HC p) = inject (Call Sig' (X,p))). rewrite H2; auto.
    rewrite epp_C_Cond_r with (HC1:=HC1) (HC2:=HC2) in H4; auto.
    apply merge_inv_Call in H4; tauto.
    apply Network_eq_refl.
  * apply S_Call; auto.
    assert (inject (epp_C _ _ _ HC p) = inject (Call Sig' (X,p))). rewrite H2; auto.
    rewrite epp_C_Cond_r with (HC1:=HC1) (HC2:=HC2) in H0; auto.
    apply merge_inv_Call in H0; tauto.
    apply Network_eq_refl.
+ inversion H.
  clear s'0 H7 N'0 H6 p0 H1 X0 H0 s0 H4. rename t into r.
  assert (In p ps /\ In p (fst (Defs r)) /\ r = X).
  1: { clear H3 H8 H5 N H N' Hin Hsp s s'.
    revert H2. unfold epp_C. elim In_dec. 2: discriminate.
    elim collapse_char'. induction a. simpl.
    intros. revert p0; simpl. elim In_dec.
    repeat split; auto. rewrite H2 in p0; inversion p0; auto.
    rewrite H2; discriminate.
    intros H H'. exfalso.
    apply projectable_C_use' with (p:=p) in HC; auto.
  }
  destroy H0. rename H1 into Hpps, H4 into HX.
  revert dependent HC. rewrite H0.
  rewrite H0 in HX, Hsp, Hin, HWF, HCXs; clear r H0; intros.
  assert (0 < set_size_pid _ (fst (Defs X))).
  1: {
    elim (Nat.lt_ge_cases 0 (set_size_pid _ (fst (Defs X)))); auto.
    intro. inversion H0. apply set_size_0 in H4. rewrite H4 in HX; inversion HX.
  }
  inversion H0.
  - exists (snd (Defs X)); split.
    apply C_Call_Local; auto.
    intro. intro r. rewrite H5.
    apply more_branches_refl'.
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
  - exists (RT_Call X (set_remove_pid _ p (fst (Defs X))) (snd (Defs X))).
    split.
    apply C_Call_Start; auto. rewrite <- H1; auto with arith.
    intro. intro r. rewrite H5.
    elim ((@eq_dec Pid) p r); intro Hpr.
    2: elim (In_dec (@eq_dec Pid) r (fst (Defs X))); intro Hr.
    * rewrite <- Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite Process_refl.
      apply more_branches_refl'.
      rewrite epp_C_RT_Call_out with (HC':=HDefs' X HXs); auto.
      intro Hp; apply set_remove'_2 in Hp; auto.
    * rewrite Par_proj1', Network_rm_out; auto.
      apply more_branches_refl'.
      rewrite epp_C_RT_Call, epp_C_Call; auto.
      apply set_remove'_3; auto.
      apply Process_out; auto.
    * rewrite Par_proj1', Network_rm_out; auto.
      apply more_branches_refl'.
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
  assert (projectable_C Defs ps C) as HCp.
  1: apply strongly_projectable_C'; apply Hsp.
  elim (eq_dec r X); intro Hr. (* case 2 pending *)
  revert dependent HC. rewrite Hr.
  rewrite Hr in Hsp, Hin, HCXs; clear r Hr; intros.
  assert (0 < set_size_pid _ l).
  1: {
    elim (Nat.lt_ge_cases 0 (set_size_pid _ l)); auto.
    intro. exfalso. inversion H1. apply set_size_0 in H6; auto.
  }
  elim (In_dec (@eq_dec Pid) p l); intro Hpl. (* weird edge case *)
  1: elim (Nat.eq_dec (set_size_pid _ l) 1); clear H0; intro H0.
  - exists C; split.
    apply C_Call_Finish; auto.
    intro. intro r. rewrite H5.
    elim ((@eq_dec Pid) p r); intro Hpr.
    * rewrite <- Hpr, Par_proj2. 2: apply Network_rm_In.
      rewrite Process_refl.
      elim (Hsp p); auto; intros. elim (H6 p); auto; intros; clear H6.
      rewrite (HDefs _ (HDefs' _ HXs)); auto.
      apply X_more_branches. rewrite <- epp_C_bproj, <- epp_C_bproj; auto.
    * rewrite Par_proj1', Network_rm_out; auto.
      rewrite epp_C_RT_Call_out with (HC':=HC'). apply more_branches_refl.
      intro. apply Hpr. eapply set_size_1; eauto.
      apply Process_out; auto.
  - exists (RT_Call X (set_remove_pid _ p l) C).
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
      rewrite (HDefs _ (HDefs' _ HXs)).
      apply X_more_branches. rewrite <- epp_C_bproj, <- epp_C_bproj; auto.
      intro Hp; apply set_remove'_2 in Hp; auto.
    * rewrite Par_proj1', Network_rm_out; auto.
      apply more_branches_refl'.
      rewrite epp_C_RT_Call, epp_C_RT_Call; auto.
      1,3: apply Hin; simpl; sup.
      apply set_remove'_3; auto.
      apply Process_out; auto.
    * rewrite Par_proj1', Network_rm_out; auto.
      apply more_branches_refl'.
      rewrite epp_C_RT_Call_out with (HC':=HCp); auto.
      rewrite epp_C_RT_Call_out with (HC':=HCp); auto.
      intro. apply Hr. eapply set_remove'_1; eauto.
      apply Process_out; auto.
  - elim (IHC HCp) with (N':=(Network_rm _ (epp_C _ _ _ HCp) p | Process Sig' p (Defs'(X,p)))%SP); auto.
    2: elim HCXs; auto.
    2: intros; elim (Hsp p0); auto.
    2: intros; apply Hin; simpl; sup.
    intros. destroy H4. rename x into C'.
    exists (RT_Call X l C'); split.
    * apply C_Delay_Call; auto.
      apply disjoint_ps_char.
      simpl; intros. intro. rewrite H9 in H7; auto.
    * intros.
      assert (projectable_C Defs ps C').
      1: {
        eapply (CCC_To_projectable_C Defs ps C s C' s' (R_Call X p) Xs); eauto.
        apply Hsp. intros; eapply initial_strongly_projectable; eauto.
        apply Hinit; auto.
        intros. intro. apply Hnames.
        intros r Z. intros. elim (Hinit Z); auto.
        elim HCXs; auto.
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
         apply more_branches_refl.
         all: apply Hin; simpl; sup.
      ++ rewrite epp_C_RT_Call_out with (HC':=H7); auto.
         rewrite epp_C_RT_Call_out with (HC':=HCp); auto.
         rewrite Par_proj1', Network_rm_out in H; auto.
         apply Process_out; auto.
      ++ apply Process_out; auto.
    * apply S_Call; auto.
      rewrite epp_C_RT_Call_out with (HC':=HCp) in H2; auto.
      apply Network_eq_refl.
  - assert (~In p l) as Hp.
    1: { intro. rewrite epp_C_RT_Call in H2; auto. inversion H2; auto. }
    elim (IHC HCp) with (N':=(Network_rm _ (epp_C _ _ _ HCp) p | Process Sig' p (Defs'(X,p)))%SP); auto.
    2: elim HCXs; auto.
    2: intros; elim (Hsp p0); auto.
    2: intros; apply Hin; simpl; sup.
    intros. destroy H1. rename x into C', r into Y.
    exists (RT_Call Y l C'); split.
    * apply C_Delay_Call; auto.
      apply disjoint_ps_char.
      simpl; intros. intro. rewrite H7 in H6; auto.
    * intros.
      assert (projectable_C Defs ps C').
      1: {
        eapply (CCC_To_projectable_C Defs ps C s C' s' (R_Call X p) Xs); eauto.
        apply Hsp. intros; eapply initial_strongly_projectable; eauto.
        apply Hinit; auto.
        intros. intro. apply Hnames.
        intros r Z. intros. elim (Hinit Z); auto.
        elim HCXs; auto.
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
         apply more_branches_refl.
         all: apply Hin; simpl; sup.
      ++ rewrite epp_C_RT_Call_out with (HC':=H6); auto.
         rewrite epp_C_RT_Call_out with (HC':=HCp); auto.
         rewrite Par_proj1', Network_rm_out in H; auto.
         apply Process_out; auto.
      ++ apply Process_out; auto.
    * apply S_Call; auto.
      rewrite epp_C_RT_Call_out with (HC':=HCp) in H2; auto.
      apply Network_eq_refl.
+ exfalso.
  inversion H.
  rewrite epp_C_End in H2. inversion H2.
Qed.

Lemma SP_To_bproj_Call_name : forall Defs Defs' ps C HC s N' s' p X,
  SP_To _ Defs' (epp_C Defs ps C HC) s (R_Call X p) N' s' ->
  exists Y, X = (Y,p) /\ X_Free _ Y C.
Proof.
intros.
inversion H.
clear s'0 H7 N'0 H6 p0 H1 X0 H0 s0 H4 N H3 H s s' H8 N' H5 Defs'.
revert H2. unfold epp_C.
elim In_dec. 2: discriminate.
elim collapse_char'; simpl.
induction a. intros.
rewrite H2 in p0. clear a x H2.
clear HC. rename p0 into HC. revert HC; simpl.
induction C; simpl; try discriminate.
induction e. 2: induction t2.
1,2,3,4: elim eq_dec; try discriminate.
1,2,3: elim eq_dec; try discriminate; auto.
2,3: elim In_dec; try discriminate; auto.
all: intros.
all: unfold X_Free; simpl; unfold set_union_rv.
- apply Xmerge_inv_Call in HC. destroy HC.
  elim IHC1; auto; intros. destroy H0.
  exists x; repeat split; auto. sup.
- inversion HC; eauto.
- inversion HC. exists t. split; auto. sup; simpl; auto.
- elim IHC; auto; intros. destroy H.
  exists x. split; auto. sup; simpl; auto.
- clear H2. exfalso. apply projectable_C_use' with (p:=p) in HC; auto.
Qed.

Lemma EPP_Sound : forall P Xs ps,
  Program_WF _ Xs P -> well_ann _ P -> forall (HP:projectable Xs ps P),
  (forall p, In p ps -> strongly_projectable (Procedures _ P) (Main P) p) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In X Xs -> In p (Vars P X) -> In p ps) ->
  forall s tl N' s', ((epp Xs ps P HP,s) --[tl]--> (N',s'))%SP ->
  exists P' tl', (P,s) --[tl']--> (P',s') /\
    forall H, Net N' >> Net (epp Xs ps P' H).
Proof.
intros.
inversion H4.
clear tl H4 s'0 H10 H6 s0 H7 s'0 N' H9. rename N'0 into N'.
rename Defs into Defs'.
induction P as (Defs,C).
assert (projectable_C Defs ps C) as HC.
1: inversion HP; auto.
assert (SP_To _ Defs' (epp_C _ _ _ HC) s t N' s').
1: {
  eapply SP_To_Network_eq; eauto. eapply Network_eq_trans.
  2: apply epp_C_char. rewrite <- H5. apply Network_eq_refl.
}
destroy H. simpl in H6, H7, H9.
  unfold CC.Procs in H; simpl in H.
inversion HP. simpl in H10, H11. destroy H11.
simpl in H1, H2, H3.
red in H12; rewrite Forall_forall in H12.
assert (forall X p, In X Xs -> In p ps -> strongly_projectable Defs (snd (Defs X)) p).
1: {
  intros. elim (In_dec (@eq_dec Pid) p (fst (Defs X))); intro.
  eapply initial_strongly_projectable; eauto. apply (H X); auto.
  eapply initial_strongly_projectable'; eauto. apply (H X); auto.
  intro; apply b, H0; auto.
}
induction t. 2: induction l.
+ apply SP_To_bproj_Com in H4.
  destroy H4. rename x0 into C'.
  assert (projectable_C Defs ps C').
  1: { eapply CCC_To_projectable_C; eauto. }
  exists (CC.Build_Program _ Defs C'),
     (@forget Pid Value Var RecVar (R_Com p v q x)); repeat split; auto.
  - apply (@CCP_To_intro Sig); auto.
  - simpl. intros. apply more_branches_N_refl'.
    eapply Network_eq_trans. apply (H4 H17); auto.
    apply Network_eq_sym; apply epp_C_char.
  - apply H1.
  - apply H2.
+ apply SP_To_bproj_Sel_l in H4.
  destroy H4. rename x into C'.
  assert (projectable_C Defs ps C').
  1: { eapply CCC_To_projectable_C; eauto. }
  exists (CC.Build_Program _ Defs C'),
     (@forget Pid Value Var RecVar (R_Sel p q left)); repeat split; auto.
  - apply (@CCP_To_intro Sig); auto.
  - simpl. intros. apply more_branches_N_refl'.
    eapply Network_eq_trans. apply (H4 H17); auto.
    apply Network_eq_sym; apply epp_C_char.
  - apply H1.
  - apply H2.
+ apply SP_To_bproj_Sel_r in H4.
  destroy H4. rename x into C'.
  assert (projectable_C Defs ps C').
  1: { eapply CCC_To_projectable_C; eauto. }
  exists (CC.Build_Program _ Defs C'),
     (@forget Pid Value Var RecVar (R_Sel p q right)); repeat split; auto.
  - apply (@CCP_To_intro Sig); auto.
  - simpl. intros. apply more_branches_N_refl'.
    eapply Network_eq_trans. apply (H4 H17); auto.
    apply Network_eq_sym; apply epp_C_char.
  - apply H1.
  - apply H2.
+ apply SP_To_bproj_Cond in H4.
  destroy H4. rename x into C'.
  assert (projectable_C Defs ps C').
  1: { eapply CCC_To_projectable_C; eauto. }
  exists (CC.Build_Program _ Defs C'),
     (@forget Pid Value Var RecVar (R_Cond p)); repeat split; auto.
  - apply (@CCP_To_intro Sig); auto.
  - simpl. intros. eapply more_branches_N_trans. apply (H4 H17).
    apply more_branches_N_refl'.
    apply Network_eq_sym. apply epp_C_char.
  - apply H1.
  - apply H2.
+ elim (SP_To_bproj_Call_name _ _ _ _ _ _ _ _ _ _ H4); intros.
  destroy H16. rename x into Y. rewrite H17 in H4, H8; clear X H17.
  assert (In Y Xs).
  1: apply within_Xs_char with (X:=Y) in H7; auto.
  apply SP_To_bproj_Call with (Xs:=Xs) in H4; auto.
  destroy H4. rename x into C'.
  assert (projectable_C Defs ps C').
  1: { eapply CCC_To_projectable_C; eauto. }
  exists (CC.Build_Program _ Defs C'),
     (@forget Pid Value Var RecVar (R_Call Y p)); repeat split; auto.
  - apply (@CCP_To_intro Sig); auto.
  - simpl. intros. eapply more_branches_N_trans. apply (H4 H19).
    apply more_branches_N_refl'.
    apply Network_eq_sym. apply epp_C_char.
  - replace Defs' with (Procs (epp _ _ _ HP)).
    2: rewrite <- H5; auto.
    intro r; intros. rewrite epp_D_char'' with (HX:=H12 _ H17); auto.
    elim (In_dec (@eq_dec Pid) r (fst (Defs Y))); intro Hr.
    apply inject_inj. rewrite <- epp_C_bproj, <- epp_C_bproj; eauto.
    rewrite epp_C_out; auto. rewrite epp_C_out'; auto.
    intro. apply Hr, H0; auto.
  - intros; apply H0; auto.
  - intros. apply Forall_forall; intro.
    induction x as (r,B). unfold epp_list; rewrite in_map_iff.
    intros. destroy H19. inversion H20. rewrite H22 in H19; clear x H22 H23 H20.
    elim (In_dec (@eq_dec Pid) r (fst (Defs X))); intro Hr.
    simpl. apply H12, projectable_C_use with (p:=r) in H18; auto.
    destroy H18. rewrite H18; apply inject_not_undefined.
    simpl. rewrite bproj_not_In; auto. discriminate.
    intro; apply Hr, H0; auto.
  - split; eauto. apply H; auto.
Qed.

Lemma SP_To_more_branches_N_epp : forall Defs N1 s N2 s' tl Defs' ps C HC,
  N1 >> epp_C Defs' ps C HC -> SP_To _ Defs N1 s tl N2 s' ->
  exists N2', SP_To _ Defs (epp_C Defs' ps C HC) s tl N2' s' /\ N2 >> N2'.
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
  exists (Network_rm _ (Network_rm _ (epp_C Defs' ps C HC) p) q | p[Bp] | q[Bq])%SP.
  repeat split.
  1: apply S_Com with (a:ann Sig') Bp a' Bq; auto. apply Network_eq_refl.
  eapply more_branches_N_trans. apply more_branches_N_refl'; eauto.
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
    exists (epp_C Defs' ps C HC ~~ p ~~ q | p[Bp] | q[Bl'])%SP.
    repeat split.
    1: apply S_LSel with (a:ann Sig') Bp a' Bl' None; auto. apply Network_eq_refl.
    eapply more_branches_N_trans. apply more_branches_N_refl'; eauto.
    intro r. elim ((@eq_dec Pid) r p); intro Hp.
    2: elim ((@eq_dec Pid) r q); intro Hq.
    * rewrite Hp, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    * rewrite Hq, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    * rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
  - symmetry in H12. rewrite <- H11 in H0. clear Br H11 Bl0 H10 a0 H7 p0 H6 H4. rename Br0 into Br.
    exists (epp_C Defs' ps C HC ~~ p ~~ q | p[Bp] | q[Bl'])%SP.
    repeat split.
    1: apply S_LSel with (a:ann Sig') Bp a' Bl' (Some (a'0,Br')); auto. apply Network_eq_refl.
    eapply more_branches_N_trans. apply more_branches_N_refl'; eauto.
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
    exists (epp_C Defs' ps C HC ~~ p ~~ q | p[Bp] | q[Br'])%SP.
    repeat split.
    1: apply S_RSel with (a:ann Sig') Bp a' None Br'; auto. apply Network_eq_refl.
    eapply more_branches_N_trans. apply more_branches_N_refl'; eauto.
    intro r. elim ((@eq_dec Pid) r p); intro Hp.
    2: elim ((@eq_dec Pid) r q); intro Hq.
    * rewrite Hp, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    * rewrite Hq, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    * rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
  - symmetry in H11. eapply epp_C_Sel_Branching_r in H11; eauto. tauto.
  - symmetry in H12. rewrite <- H7 in H0. clear Bl H7 Br0 H11 a'0 H10 p0 H6 H4. rename Bl0 into Bl.
    exists (epp_C Defs' ps C HC ~~ p ~~ q | p[Bp] | q[Br'])%SP.
    repeat split.
    1: apply S_RSel with (a:ann Sig') Bp a' (Some (a0,Bl')) Br'; auto. apply Network_eq_refl.
    eapply more_branches_N_trans. apply more_branches_N_refl'; eauto.
    intro r. elim ((@eq_dec Pid) r p); intro Hp.
    2: elim ((@eq_dec Pid) r q); intro Hq.
    * rewrite Hp, Network_rm_add_2_p, Network_rm_add_2_p; auto.
    * rewrite Hq, Network_rm_add_2_q, Network_rm_add_2_q; auto.
    * rewrite Network_rm_add_2_out, Network_rm_add_2_out; auto.
+ clear s'0 H7 N' H6 tl H5 N H3 s0 H4 HTo.
  generalize (Hmb p); intro.
  rewrite H in H3; inversion H3.
  clear B3 H7 B0 H5 b0 H4. symmetry in H8.
  exists (Network_rm _ (epp_C Defs' ps C HC) p | p[B1'])%SP.
  repeat split.
  1: apply (@S_Then Sig') with b B1' B2'; auto. apply Network_eq_refl.
  eapply more_branches_N_trans. apply more_branches_N_refl'; eauto.
  intro r. elim ((@eq_dec Pid) r p); intro Hp.
  - rewrite Hp, Par_proj2, Par_proj2, Process_refl, Process_refl; auto;
      apply Network_rm_In.
  - rewrite Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto;
      apply Process_out; auto.
+ clear s'0 H7 N' H6 tl H5 N H3 s0 H4 HTo.
  generalize (Hmb p); intro.
  rewrite H in H3; inversion H3.
  clear B3 H7 B0 H5 b0 H4. symmetry in H8.
  exists (epp_C Defs' ps C HC ~~ p | p[B2'])%SP.
  repeat split. 
  1: apply (@S_Else Sig') with b B1' B2'; auto. apply Network_eq_refl.
  eapply more_branches_N_trans. apply more_branches_N_refl'; eauto.
  intro r. elim ((@eq_dec Pid) r p); intro Hp.
  - rewrite Hp, Par_proj2, Par_proj2, Process_refl, Process_refl; auto;
      apply Network_rm_In.
  - rewrite Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto;
      apply Process_out; auto.
+ clear s'0 H6 N' H5 tl H4 s0 H3 N H2 HTo.
  generalize (Hmb p); intro.
  rewrite H in H2; inversion H2.
  clear X0 H4. symmetry in H5.
  exists (epp_C Defs' ps C HC ~~ p | p [Defs X])%SP.
  repeat split.
  1: apply S_Call; auto. apply Network_eq_refl.
  eapply more_branches_N_trans. apply more_branches_N_refl'; eauto.
  intro r. elim ((@eq_dec Pid) r p); intro Hp.
  - rewrite Hp, Par_proj2, Par_proj2. 2,3: apply Network_rm_In.
    apply more_branches_refl.
  - rewrite Par_proj1', Par_proj1', Network_rm_out, Network_rm_out; auto;
      apply Process_out; auto.
Qed.

Lemma SPP_To_more_branches_N_epp : forall P1 s P2 s' tl Xs ps P HP,
  (forall X, Procs P1 X = Procs (epp Xs ps P HP) X) ->
  Net P1 >> Net (epp Xs ps P HP) -> SPP_To _ (P1,s) tl (P2,s') ->
  exists P2', ((epp Xs ps P HP,s) --[tl]--> (P2',s'))%SP /\ Net P2 >> Net P2'
  /\ forall X, Procs P2 X = Procs P2' X.
Proof.
intros.
induction P1 as (Defs,N1), P2 as (Defs2,N2).
rewrite <- (SPP_To_Defs_stable _ _ _ _ _ _ _ _ H1);
rewrite <- (SPP_To_Defs_stable _ _ _ _ _ _ _ _ H1) in H1; clear Defs2.
induction P as (Defs',C).
inversion HP. inversion_clear H3. clear H5. simpl in H2, H4.
inversion H1. clear s'0 H10 N' H9 tl H5 s0 H7 N H6 Defs0 H3 H1.
eapply SP_To_more_branches_N_epp with (HC:=H2) in H8; eauto.
2: intro r; rewrite <- epp_C_char with (HP:=HP); auto.
destroy H8. rename x into N2'.
exists (Build_Program _ (Procs (epp _ _ _ HP)) N2'); repeat split; auto.
rewrite (SP_eta _ (epp _ _ _ HP)); constructor.
simpl. apply SP_To_Defs_wd with Defs; auto.
eapply SP_To_Network_eq; eauto.
apply Network_eq_sym; apply epp_C_char.
Qed.

(** Generalizing the last result to -->* already requires the EPP Theorem. *)

Lemma SPP_ToStar_more_branches_N : forall P1 s P2 s' tl Xs ps P,
  Program_WF _ Xs P -> well_ann _ P -> forall (HP:projectable Xs ps P),
  (forall p, In p ps -> strongly_projectable (Procedures _ P) (Main P) p) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In X Xs -> In p (Vars P X) -> In p ps) ->
  (forall X, Procs P1 X = Procs (epp Xs ps P HP) X) ->
  Net P1 >> Net (epp Xs ps P HP) -> ((P1,s) --[tl]-->* (P2,s'))%SP ->
  exists P2', SPP_ToStar _ (epp Xs ps P HP,s) tl (P2',s') /\ Net P2 >> Net P2'
  /\ forall X, Procs P2 X = Procs P2' X.
Proof.
intros.
induction P1 as (Defs,N1), P2 as (Defs2,N2).
rewrite <- (SPP_ToStar_Defs_stable _ _ _ _ _ _ _ _ H6);
rewrite <- (SPP_ToStar_Defs_stable _ _ _ _ _ _ _ _ H6) in H6; clear Defs2.
induction P as (Defs',C).
revert dependent C. revert s s' N1 N2 H6. induction tl; intros.
+ inversion H6. rewrite <- H8.
  exists (epp _ _ _ HP); repeat split; auto. constructor.
+ inversion H6. clear c3 H11 l H8 t H7 c1 H9 H6. rename a into t.
  induction c2 as ((Defs2,N3),s'').
  rewrite <- (SPP_To_Defs_stable _ _ _ _ _ _ _ _ H10) in H12, H10. clear Defs2.
  apply SPP_To_more_branches_N_epp with (HP:=HP) in H10; auto.
  destroy H10. induction x as (Defs3,N3'). simpl in H7, H10.
  generalize H6 as H6'; intro.
  rewrite (SP_eta _ (epp _ _ _ HP)) in H6'.
  rewrite <- (SPP_To_Defs_stable _ _ _ _ _ _ _ _ H6') in H6, H10, H6'. clear Defs3.
  rewrite <- SP_eta in H6'.
  apply EPP_Sound in H6; auto. destroy H6. rename x0 into t'.
  induction x as (Defs'3,C'').
  rewrite <- (CCP_To_Defs_stable _ _ _ _ _ _ _ _ H8) in H6, H8. clear Defs'3.
  assert (projectable Xs ps (CC.Build_Program _ Defs' C'')).
  1: eapply CCC_To_projectable; eauto.
  generalize (H6 H9); clear H6; intro. simpl in H6.
  generalize H12 as H12'; intro.
  inversion HP. clear H11; inversion_clear H13. simpl in H11; clear H14.
  rename H11 into HD.
  apply IHtl with (HP:=H9) in H12; auto. clear IHtl.
  destroy H12. rename x into P2'. induction P2' as (Defs2',N2').
  rewrite (SP_eta _ (epp _ _ _ H9)) in H11.
  rewrite <- (SPP_ToStar_Defs_stable _ _ _ _ _ _ _ _ H11) in H13, H12, H11.
  clear Defs2'. rewrite <- SP_eta in H11. simpl in H11, H12, H13.
  apply SPP_ToStar_more_branches_N with (P1':=Build_Program _ (Procs (epp _ _ _ HP)) N3') in H11; auto.
  destroy H11. rename x into P2'. simpl in H11, H15.
  exists P2'; repeat split; auto.
  - econstructor; eauto.
  - simpl.
    apply SPP_ToStar_more_branches_N with (P1':=Build_Program _ Defs N3) in H14; auto.
    destroy H14. apply more_branches_N_trans with (Net x); auto.
    apply more_branches_N_refl'.
    change N2 with (Net (Build_Program _ Defs N2)).
    eapply SPP_ToStar_deterministic_1; eauto.
    simpl; intro.
    rewrite H12. induction X. repeat rewrite epp_D_char with (HD:=HD); auto.
  - simpl; intro. rewrite H12, <- H11.
    induction X. repeat rewrite epp_D_char with (HD:=HD); auto.
  - simpl; intro. induction X; repeat rewrite epp_D_char with (HD:=HD); auto.
  - eapply CCC_To_Program_WF; eauto.
  - eapply CCP_To_strongly_projectable; eauto.
  - intros. apply H2. eapply CCC_To_pn''; eauto.
  - intro; rewrite H10. induction X; repeat rewrite epp_D_char with (HD:=HD); auto.
  - apply more_branches_N_trans with N3'; auto.
Qed.

Lemma EPP_Sound' : forall P Xs ps,
  Program_WF _ Xs P -> well_ann _ P -> forall (HP:projectable Xs ps P),
  (forall p, In p ps -> strongly_projectable (Procedures _ P) (Main P) p) ->
  (forall p, In p (CCC_pn (Main P) (Vars P)) -> In p ps) ->
  (forall p X, In X Xs -> In p (Vars P X) -> In p ps) ->
  forall s tl P' s', ((epp Xs ps P HP,s) --[tl]-->* (P',s'))%SP ->
  exists P'' tl', ((P,s) --[tl']-->* (P'',s')) /\
    forall H, Net P' >> Net (epp Xs ps P'' H).
Proof.
intros.
induction P as (Defs,C), P' as (Defs',N).
revert dependent N. revert dependent C. revert Defs' s s'.
induction tl; intros; inversion H4.
+ eexists; exists nil. repeat split. constructor.
  intro. apply more_branches_N_refl'.
  inversion HP. simpl in H9.
  apply Network_eq_trans with (epp_C Defs ps C H9).
  2: apply Network_eq_sym. all: apply epp_C_char.
+ clear c3 H9 l H6 t H5 c1 H7 H4. rename a into t.
  induction c2 as (P'', s'').
  eapply SPP_To_more_branches_N_epp in H8; eauto. destroy H8.
  rename x into P'. 2: apply more_branches_N_refl.
  rewrite (SP_eta _ (epp _ _ _ HP)), (SP_eta _ P') in H4.
  generalize (SPP_To_Defs_stable _ _ _ _ _ _ _ _ H4); intro H4'.
  rewrite <- SP_eta, <- SP_eta in H4.
  apply EPP_Sound in H4; auto. destroy H4.
  rename x into P1, x0 into t'.
  assert (projectable Xs ps P1).
  1: eapply CCC_To_projectable; eauto.
  induction P1 as (Defs1, C1).
  rewrite <- (CCP_To_Defs_stable _ _ _ _ _ _ _ _ H6) in H4, H7, H6. clear Defs1.
  generalize (H4 H7); clear H4; intro.
  assert (Program_WF _ Xs (CC.Build_Program _ Defs C1)).
  1: eapply CCC_To_Program_WF; eauto.
  assert (forall p, In p ps -> strongly_projectable Defs C1 p).
  1: {
    change Defs with (Procedures _ (CC.Build_Program _ Defs C1)).
    change C1 with (Main (CC.Build_Program _ Defs C1)) at 2.
    intros. inversion HP. destroy H13.
    eapply CCP_To_strongly_projectable with (P:=CC.Build_Program _ Defs C); eauto.
  }
  assert (forall p, In p (CCC_pn C1 (Vars {| Procedures := Defs; Main := C1 |})) -> In p ps).
  1:{
    change C1 with (Main (CC.Build_Program _ Defs C1)) at 1.
    intros. apply H2. eapply CCC_To_pn''; eauto.
  }
  apply SPP_ToStar_more_branches_N with (HP:=H7) in H10; auto.
  - destroy H10.
    rename x into P1. induction P1 as (Defs1,N1).
    eapply IHtl in H9; auto. 2: apply H13.
    destroy H9. rename x into P2, x0 into tl'.
    clear IHtl. exists P2, (t'::tl').
    repeat split.
    eapply CCT_Step; eauto.
    intro. apply more_branches_N_trans with N1; auto.
  - intro. rewrite H8, <- H4'.
    inversion HP. destroy H14. induction X.
    simpl in H15; repeat rewrite epp_D_char with (HD:=H15); auto.
  - apply more_branches_N_trans with (Net P'); auto.
Qed.

End EPP_Theorem.

End EndPointProjection.
