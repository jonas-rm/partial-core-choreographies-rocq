Require Export Amendment.
Require Export EPPTheorem.
Require Export Implementation.

(** * Turing completeness *)

(** ** Turing completeness of CC *)

Theorem CC_Turing_Complete : forall n (f:PRFunction n),
  exists P, Program_WF P /\ implements P f (vec_1_to_n n) 0.
Proof.
eexists; split.
2: apply encoding_sound.
apply Encoding'_WF.
Qed.

(** ** Turing completeness of projectable CC. *)

Section Amend.

Variable n:nat.
Variable f:PRFunction n.

Theorem amended_encoding_WF : Program_WF (amend_P (all_pids (n+Pi f)) eps (Encoding' f)).
Proof.
intros.
apply amend_Program_WF, Encoding'_WF.
Qed.

Lemma amend_implements : forall ps q P ps' a,
  Program_WF P -> implements P f ps q -> implements (amend_P ps' a P) f ps q.
Proof.
red; intros. rename H into HP, H1 into Hps.
induction (H0 xs s) as [Hconv Hdiv]; auto.
induction P as (Defs,C).
split; intros.
1: induction (Hconv y) as [Hto Hfrom]; clear Hconv Hdiv.
2: induction Hdiv as [Hto Hfrom]; clear Hconv.
all: split; intros.
+ (* function converges *)
  specialize (Hto H); clear Hfrom.
  induction Hto as [s' [ts [P' [Hred [Hs' HP'] ] ] ] ].
  induction P' as (Defs',C').
  generalize (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ _ Hred) as HDefs; intros.
  rewrite <- HDefs in *; clear Defs' HDefs. simpl in *.
  rewrite HP' in *; clear C' HP'.
  apply amend_complete_many with (a:=a) (ps:=ps') in Hred; auto.
  induction Hred as (tl',(tl'',(C'',(s'',(Hsub,(Htl',Htl'')))))).
  generalize (CCP_ToStar_End _ _ _ _ _ _ Htl'); intro H'.
  induction H' as [H1 H2]; auto. rewrite H1 in *; clear H1 tl'.
  inversion Htl'. rewrite <- H3 in *; clear s'0 H6 C'' H3 s0 H4 P H1 H5.
  exists s'', tl''; eexists. repeat split; eauto.
  rewrite <- H2; auto.
+ (* choreography terminates *)
  apply Hfrom; clear Hto Hfrom.
  induction H as (s',(ts,(P',(Hts,(Hs',HP'))))).
  induction P' as (Defs',C'). simpl in *; rewrite HP' in *; clear C' HP'.
  rewrite <- (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ _ Hts) in Hts; clear Defs'.
  apply amend_sound_many in Hts; auto.
  induction Hts as (tl',(tl'',(C'',(s'',(Htl',(Htl'',Hsub)))))).
  generalize (CCP_ToStar_End _ _ _ _ _ _ Htl'); intro H'.
  induction H' as [H1 H2]; auto. rewrite H1 in *; clear H1 tl'.
  inversion Htl'. symmetry in H1. rewrite (amend_eq_End _ _ _ _ _ H1) in *.
  clear s'0 H5 C'' H1 s0 H3 P H H4.
  exists s'', tl'', (Defs,End). repeat split; auto.
  rewrite <- H2; auto.
+ (* function diverges *)
  specialize (Hto H); clear H Hfrom.
  induction P' as (Defs',C').
  generalize (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ _ H1) as HDefs; intros.
  rewrite <- HDefs in *; clear Defs' HDefs. simpl in *.
  apply amend_sound_many in H1; auto.
  induction H1 as (tl',(tl'',(C'',(s'',(Htl',(Htl'',Hsub)))))).
  simpl in Htl''. specialize (Hto _ _ _ Htl'').
  intro. apply Hto; simpl.
  rewrite H in *; clear C' H. simpl in *.
  generalize (CCP_ToStar_End _ _ _ _ _ _ Htl'); intro H'.
  induction H' as [H1 H2]; auto. rewrite H1 in *; clear H1 tl'.
  inversion Htl'. symmetry in H1. apply (amend_eq_End _ _ _ _ _ H1).
+ (* choreography diverges *)
  apply Hfrom; clear Hto Hfrom; intros.
  induction P' as (Defs',C').
  generalize (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ _ H1) as HDefs; intros.
  rewrite <- HDefs in *; clear Defs' HDefs. simpl in *.
  apply amend_complete_many with (a:=a) (ps:=ps') in H1; auto.
  induction H1 as (tl',(tl'',(C'',(s'',(Hsub,(Htl',Htl'')))))).
  intro HC'. rewrite HC' in *; clear C' HC'.
  generalize (CCP_ToStar_End _ _ _ _ _ _ Htl'); intro H'.
  induction H' as [H1 H2]; auto. rewrite H1 in *; clear H1 tl'.
  inversion Htl'. rewrite <- H3 in *; clear s'0 H6 C'' H3 s0 H4 P H1 H5.
  apply (H _ _ _ Htl''); auto.
Qed.

Theorem amended_encoding_sound :
  implements (amend_P (all_pids (n+Pi f)) eps (Encoding' f))
             f (vec_1_to_n n) 0.
Proof.
intros.
apply amend_implements. apply Encoding'_WF.
apply encoding_sound.
Qed.

Theorem amended_encoding_projectable :
  projectable _ (all_pids (n+Pi f))
                (amend_P (all_pids (n+Pi f)) eps (Encoding' f)).
Proof.
intros.
induction (Encoding'_WF f) as [HWF [Hcons HProcs] ].
repeat split.
+ apply amend_projectable_C.
+ intro X.
  unfold Procedures, amend_P.
  set (P := Encoding' f). assert (P = Encoding' f); auto.
  clearbody P. induction P as (D,C). simpl.
  red; rewrite List.Forall_forall; intros.
  apply amend_projectable_B.
  unfold Encoding', Encoding in H.
  change D with (fst (D,C)) in H0. rewrite H in H0. simpl in H0.
  rewrite vmax_vec_1_to_n in H0; auto.
+ unfold amend_P; simpl. tauto.
+ set (P := Encoding' f). assert (P = Encoding' f); auto.
  clearbody P. induction P as (D,C). simpl.
  unfold Encoding', Encoding in H.
  intros. change D with (fst (D,C)) in H0.
  rewrite H in H0. simpl in H0.
  rewrite vmax_vec_1_to_n in H0; auto.
+ set (P := Encoding' f). assert (P = Encoding' f); auto.
  clearbody P. induction P as (D,C). simpl; intros.
  specialize (HProcs X). rewrite <- H in HProcs.
  unfold Encoding', Encoding in H.
  intros. apply CCC_pn_mon with (Y:=Names D) in H0.
  2: simpl; tauto.
  apply amend_CCC_pn_incl, HProcs in H0.
  change D with (fst (D,C)) in H0.
  rewrite H in H0. simpl in H0.
  rewrite vmax_vec_1_to_n in H0; auto.
Qed.

Theorem amended_encoding_Projectable :
  Projectable _ (amend_P (all_pids (n+Pi f)) eps (Encoding' f)).
Proof.
intros.
induction (Encoding'_WF f) as [HWF [Hcons HProcs] ].
(* this should be simplifiable *)
exists (all_pids (n+Pi f)); split. repeat split.
+ apply amend_projectable_C.
+ intro.
  unfold Procedures, amend_P.
  set (P := Encoding' f). assert (P = Encoding' f); auto.
  clearbody P. induction P as (D,C). simpl.
  red; rewrite List.Forall_forall; intros.
  apply amend_projectable_B.
  unfold Encoding', Encoding in H.
  change D with (fst (D,C)) in H0. rewrite H in H0. simpl in H0.
  rewrite vmax_vec_1_to_n in H0; auto.
+ unfold amend_P; simpl. tauto.
+ set (P := Encoding' f). assert (P = Encoding' f); auto.
  clearbody P. induction P as (D,C). simpl.
  unfold Encoding', Encoding in H.
  intros. change D with (fst (D,C)) in H0.
  rewrite H in H0. simpl in H0.
  rewrite vmax_vec_1_to_n in H0; auto.
+ set (P := Encoding' f). assert (P = Encoding' f); auto.
  clearbody P. induction P as (D,C). simpl; intros.
  specialize (HProcs X). rewrite <- H in HProcs.
  unfold Encoding', Encoding in H.
  intros. apply CCC_pn_mon with (Y:=Names D) in H0.
  2: simpl; tauto.
  apply amend_CCC_pn_incl in H0.
  apply HProcs in H0.
  change D with (fst (D,C)) in H0.
  rewrite H in H0. simpl in H0.
  rewrite vmax_vec_1_to_n in H0; auto.
+ apply amend_Program_WF; red; auto.
Qed.

Lemma projCC_Turing_Complete : exists P,
  Program_WF P /\ Projectable _ P /\ implements P f (vec_1_to_n n) 0.
Proof.
eexists; split. 2: split.
2: apply amended_encoding_Projectable.
apply amended_encoding_WF.
apply amended_encoding_sound.
Qed.

End Amend.

(** ** Turing completeness of SP. *)

Section SP_Turing.

Open Scope SP_scope.

Definition SP_implements (P:SP.Program (Sig' IS))
  {n} (f:PRFunction n) (ps:t Pid n) (q:Pid) :=
    forall (xs:t nat n) s, (forall Hi, s (ps[@Hi]) xx = xs[@Hi]) ->
    (forall y, converges f xs y <-> exists s' ts P',
        (P,s) --[ts]-->* (P',s') /\ s' q xx = y /\ Net P' (==) EmptyNet _) /\
    (diverges f xs <->
        forall s' ts P', (P,s) --[ts]-->* (P',s') -> ~(Net P' (==) EmptyNet _)).

Definition Encode_Net {n} f := epp _ _ (amended_encoding_projectable n f).

Variable n:nat.
Variable f:PRFunction n.

Lemma epp_implements : forall P ps q ps',
  Program_WF P -> forall (HP:projectable _ ps' P),
  (forall p, List.In p ps' -> str_proj (Procedures _ P) (Main P) p) ->
  (forall p, List.In p (CCC_pn (Main P) (Vars P)) -> List.In p ps') ->
  (forall p X, List.In p (Vars P X) -> List.In p ps') ->
  implements P f ps q -> SP_implements (epp ps' P HP) f ps q.
Proof.
intros.
rename H0 into Hsp, H1 into Hpn, H2 into Hin, H3 into Himpl.
red; intros.
induction (Himpl _ _ H0) as [Hconv Hdiv]; clear H0.
repeat split.
+ (* f converges *)
  intros. elim (Hconv y); intros. specialize (H1 H0).
  clear Hconv Hdiv H0 H2.
  induction H1 as [s' [ts [P' [Hts [Hs' HP'] ] ] ] ].
  induction P as (D,C), P' as (D',C').
  generalize (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ _ Hts); intro HD.
  simpl in HP'. rewrite <- HD, HP' in *; clear C' D' HD HP'.
  apply EPP_Complete' with (HP:=HP) in Hts; auto.
  induction Hts as [N [tl' [Htl' HN] ] ].
  exists s', tl', N. repeat split; auto.
  assert (projectable_C D End ps').
  1:{ red; rewrite List.Forall_forall; intros.
      exists (SP.End _); constructor.
  }
  assert (projectable IS ps' (D,End)).
  1: { elim HP. intros HC (HD,(H1,(H2,H3))).
       repeat split; auto. simpl; tauto.
  }
  specialize (HN H1).
  generalize (epp_C_char _ _ _ _ H1 H0); intros.
  intro. specialize (HN p). rewrite H2 in HN.
  rewrite epp_C_End in HN. inversion HN; auto.
+ (* N terminates *)
  intros. apply (Hconv y); intros. clear Hconv Hdiv.
  induction H0 as [s' [ts [P' [Hts [Hs' HP'] ] ] ] ].
  apply EPP_Sound' in Hts; auto.
  induction Hts as [P'' [ts' [Htl' HN] ] ].
  exists s', ts', P''; repeat split; auto.
  apply CCP_ToStar_projectable with (s:=s) (tl:=ts') (P':=P'') (s':=s') in HP; auto.
  specialize (HN HP).
  apply epp_EmptyNet' with (HP:=HP) (N:=Net P'); auto.
  apply (CCP_ToStar_Program_WF _ _ _ _ _ _ H Htl').
+ (* f diverges *)
  induction Hdiv; intros. specialize (H0 H2). clear Hconv H1 H2.
  apply EPP_Sound' in H3.
  induction H3 as [P'' [ts' [Htl' HN] ] ].
  intro. eapply H0; eauto. all: auto.
  apply CCP_ToStar_projectable with (s:=s) (tl:=ts') (P':=P'') (s':=s') in HP; auto.
  apply epp_EmptyNet' with (HP:=HP) (N:=Net P'); auto.
  apply (CCP_ToStar_Program_WF _ _ _ _ _ _ H Htl').
+ (* N loops *)
  intros. apply Hdiv; intros. clear Hconv Hdiv.
  induction P as (D,C), P' as (D',C').
  generalize (CCP_ToStar_Defs_stable _ _ _ _ _ _ _ _ H1); intros HD HC'.
  simpl in HC'. rewrite HC', <- HD in *; clear D' C' HD HC'.
  apply EPP_Complete' with (HP:=HP) in H1; auto.
  induction H1 as [N [tl' [Htl' HN] ] ].
  eapply H0; eauto.
  assert (projectable_C D End ps').
  1:{ red; rewrite List.Forall_forall; intros.
      exists (SP.End _); constructor.
  }
  assert (projectable IS ps' (D,End)).
  1: { elim HP. intros HC (HD,(H2,(H3,H4))).
       repeat split; auto. simpl; tauto.
  }
  specialize (HN H2).
  generalize (epp_C_char _ _ _ _ H2 H1); intros.
  intro. specialize (HN p). rewrite H3 in HN.
  rewrite epp_C_End in HN. inversion HN; auto.
Qed.

Theorem encode_Net_sound : SP_implements (Encode_Net f) f (vec_1_to_n n) 0.
Proof.
intros.
induction (amended_encoding_WF n f) as [HWF [Hcons HProcs] ].
apply epp_implements; auto.
+ apply amend_Program_WF; auto.
  apply Encoding'_WF.
+ intros. simpl in H.
  rewrite <- amend_P_Vars in H.
  unfold Vars, Encoding', Procedures in H.
  simpl in H.
  rewrite vmax_vec_1_to_n in H; auto.
+ intros. unfold Vars, Encoding', Procedures in H.
  simpl in H.
  rewrite vmax_vec_1_to_n in H; auto.
+ apply amended_encoding_sound.
Qed.

Lemma encode_Net_WF : Network_WF _ (Net (Encode_Net f)).
Proof.
unfold Encode_Net.
set (ps := all_pids (n+Pi f)).
unfold amend_P.
assert (projectable_C (amend_D (Procedures _ (Encoding' f)) eps ps) (Main (Encoding' f)) ps).
1: apply amended_encoding_projectable.
intro.
rewrite epp_C_char with (HP:=amended_encoding_projectable n f) (HC:=H).
apply epp_C_WF.
apply amend_no_self_comm.
unfold Encoding', Encoding. simpl; auto.
Qed.

Theorem SP_Turing_Complete :
  exists P, Network_WF _ (Net P) /\ SP_implements P f (vec_1_to_n n) 0.
Proof.
eexists; split.
apply encode_Net_WF.
apply encode_Net_sound.
Qed.

End SP_Turing.
