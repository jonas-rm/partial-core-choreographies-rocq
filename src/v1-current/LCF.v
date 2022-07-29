Require Import EPP.

Section Amendmend.

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

Notation Sig' := (Sig' Sig).

Local Ltac eq_elim t t' H := case (eq_dec t t'); intro H;
  [ rewrite <- H in *; clear t' H | idtac].

Open Scope CC_scope.

(* Clean me *)
Fixpoint amend Defs (C:Choreography Sig) (p:Pid) (a:Ann) :=
match C with
| eta@a';; C' => eta@a';; (amend Defs C' p a)
| If q ?? b Then C1 Else C2 =>
    let C1' := amend Defs C1 p a in let C2' := amend Defs C2 p a in
    if (p =? q)
    then If q ?? b Then C1' Else C2'
    else if projectable_B_dec _ Defs (If q ?? b Then C1' Else C2') p
         then If q ?? b Then C1' Else C2'
         else If q ?? b Then (q --> p[left]@a;; C1') Else (q --> p[right]@a;; C2')
| RT_Call X ps C' => RT_Call X ps (amend Defs C' p a)
| _ => C
end.

Lemma amend_proj : forall Defs C p a,
  projectable_B Sig Defs (amend Defs C p a) p.
Proof.
induction C; intros.
+ simpl.
  induction (IHC p a) as [B HB].
  induction e. all: eq_elim p t0 Hp.
  2: eq_elim p t2 Hp'. 5: eq_elim p t1 Hp'. 5: induction t2.
  all: try (eexists; econstructor; eauto; fail).
  exists (@Branching Sig' t0 (Some (t,B)) None). constructor; auto.
  exists (@Branching Sig' t0 None (Some (t,B))). constructor; auto.
+ induction (IHC1 p a) as [B1 HB1]. induction (IHC2 p a) as [B2 HB2].
  simpl. case_eq (p =? t); intro.
  2: elim projectable_B_dec; intros.
  - rewrite eqb_eq in H. rewrite <- H.
    eexists; econstructor; eauto.
  - rewrite eqb_neq in H.
    induction a0 as [B HB]. inversion HB. symmetry in H3; tauto.
    exists B. apply bproj_Cond' with B0 B3; auto.
  - rewrite eqb_neq in H.
    exists (@Branching Sig' t (Some (a,B1)) (Some (a,B2))).
    apply bproj_Cond' with (@Branching Sig' t (Some (a,B1)) None) (@Branching Sig' t None (Some (a,B2)));
      try constructor; auto.
    apply (merge_Branching_SNNS Sig').
+ elim (in_dec (@eq_dec Pid) p (fst (Defs t))).
  all: eexists. constructor; auto. apply bproj_Call_out; auto.
+ elim (in_dec (@eq_dec Pid) p l).
  eexists. constructor; auto.
  induction (IHC p a) as [B HB].
  eexists. apply bproj_RT_Call_out; eauto.
+ simpl. eexists; constructor.
Qed.

Inductive sel_subtrace : list (TransitionLabel Pid Value) -> list (TransitionLabel Pid Value) -> Prop :=
| ss_refl ts : sel_subtrace ts ts
| ss_cons t ts ts' : sel_subtrace ts ts' -> sel_subtrace (t::ts) (t::ts')
| ss_extra p q l ts ts' : sel_subtrace ts ts' -> sel_subtrace ts (TL_Sel p q l::ts')
.

Lemma amend_sound : forall Defs C s tl C' s',
  (Defs,C,s) --[tl]--> (Defs,C',s') ->
  forall r a, exists tl' tl'' C'' s'',
       sel_subtrace tl' tl''
    /\ (Defs,C',s') --[tl']-->* (Defs,C'',s'')
    /\ (Defs,amend Defs C r a,s) --[tl::tl'']-->* (Defs,amend Defs C'' r a,s'').
Proof.
intros. revert C s tl C' s' H.
induction C; intros. induction e.
+ inversion H. clear s'0 H6 C'0 H5 tl H1 H s0 H3 C0 H2 D H0.
  rename t0 into p, t1 into e, t2 into q, t3 into x, t into a', t4 into tl.
  inversion H4.
  - (* Com *)
    rewrite <- H8 in *.
    clear s'0 H9 C' H8 tl H7 s0 H0 C0 H6 a0 H5 x0 H3 q0 H2 e0 H1 p0 H H4.
    simpl. exists nil, nil, C, s'.
    repeat split; auto; econstructor. 2: constructor.
    rewrite <- forget_Com with (RecVar := RecVar) (x:=x).
    constructor. apply C_Com; auto.
  - (* Delay *)
    rewrite <- H5 in *.
    clear s'0 H6 t H3 s0 H1 C0 H2 ann H0 eta H H4 H5.

(* needs some non-trivial rewritings on H8

    induction (IHC _ _ _ _ (CCP_To_intro _ _ _ _ _ _ _ H8)) as [tlF [tlF' [CF [sF [HF1 [HF2 HF3] ] ] ] ] ].
    simpl. set (v := eval_on_state Ev e s p); set (tl' := @RL_Com _ _ _ RecVar p v q x).
    exists (forget tl'::tlF), (forget tl'::tlF'), CF, sF.
    repeat split; auto. econstructor; eauto.
    econstructor; eauto. unfold tl'; apply
    * inversion HF1.
 repeat constructor; auto.
*)
  admit.

+ inversion H. clear s'0 H6 C'0 H5 tl H1 H s0 H3 C0 H2 D H0.
  rename t0 into p, t1 into q, t2 into l, t into a', t3 into tl.
  inversion H4.
  - (* Sel *)
    rewrite <- H7 in *.
    clear s'0 H8 C' H7 tl H6 s0 H0 C0 H5 a0 H3 l0 H2 q0 H1 p0 H H4.
    simpl. exists nil, nil, C, s'.
    repeat split; auto; econstructor. 2: constructor.
    rewrite <- forget_Sel with (RecVar := RecVar) (Var := Var).
    constructor. apply C_Sel; auto.
  - (* Delay *)
    rewrite <- H5 in *.
    clear s'0 H6 t H3 s0 H1 C0 H2 ann H0 eta H H4 H5. rename C'0 into C0.
    induction (IHC _ _ _ _ (CCP_To_intro _ _ _ _ _ _ _ H8)) as [tlF [tlF' [CF [sF [HF1 [HF2 HF3] ] ] ] ] ].
    simpl. set (tl' := @RL_Sel _ Value Var RecVar p q l).
    exists (forget tl'::tlF), (forget tl'::tlF'), CF, sF.
    repeat split; auto. econstructor; eauto.
    econstructor; eauto.
    unfold tl'; constructor; constructor; ESEr.
    inversion_clear HF3.
    induction c2 as [ [Defs' C'' ] s''].
    generalize (CCP_To_Defs_stable _ _ _ _ _ _ _ _ H) as HDefs; intro.
    rewrite <- HDefs in *; clear Defs' HDefs.
    econstructor; eauto.
    * inversion H. constructor. apply C_Delay_Eta; eauto.
      induction t; induction tl; inversion H5; auto.
    * econstructor; eauto.
      constructor. unfold tl'; constructor; ESEr.
+ inversion H. clear s'0 H6 C'0 H5 tl H1 s0 H3 C H2 D H0 H.
  rename t into p, t0 into b, t1 into tl.
  inversion H4.
  - (* Then *)
    rewrite <- H6 in *.
    clear s'0 H7 C' H6 tl H5 s0 H1 C3 H3 C0 H2 b0 H0 p0 H H4.
    simpl.
    (* did we amend? *)
    case_eq (r =? p); intro Hr.
    2: case projectable_B_dec; intro HC.
    1,2: exists nil, nil, C1, s'.
    1,2: repeat split; auto; econstructor. 2,4: constructor.
    1,2: rewrite <- forget_Cond with (RecVar := RecVar) (Var := Var).
    1,2: constructor; apply C_Then; auto.
    exists nil, (@forget Pid Value Var RecVar (RL_Sel p r left)::nil), C1, s'.
    repeat split; auto; repeat constructor.
    econstructor. 2: econstructor. 3: constructor.
    * rewrite <- (@forget_Cond Pid Value Var RecVar).
      constructor. constructor; eauto.
    * constructor. constructor; ESEr.
  - (* Else *)
    rewrite <- H6 in *.
    clear s'0 H7 C' H6 tl H5 s0 H1 C3 H3 C0 H2 b0 H0 p0 H H4.
    simpl.
    (* did we amend? *)
    case_eq (r =? p); intro Hr.
    2: case projectable_B_dec; intro HC.
    1,2: exists nil, nil, C2, s'.
    1,2: repeat split; auto; econstructor. 2,4: constructor.
    1,2: rewrite <- forget_Cond with (RecVar := RecVar) (Var := Var).
    1,2: constructor; apply C_Else; auto.
    exists nil, (@forget Pid Value Var RecVar (RL_Sel p r right)::nil), C2, s'.
    repeat split; auto; repeat constructor.
    econstructor. 2: econstructor. 3: constructor.
    * rewrite <- (@forget_Cond Pid Value Var RecVar).
      constructor. apply C_Else; eauto.
    * constructor. constructor; ESEr.
  - (* Delay *)
    rewrite <- H6 in *.
    clear s'0 H7 t H5 s0 H2 C3 H3 C0 H1 b0 H0 p0 H H6 H4.
    induction (IHC1 _ _ _ _ (CCP_To_intro _ _ _ _ _ _ _ H9)) as [tl1F [tl1F' [C1F [s1F [HF1 [HF2 HF3] ] ] ] ] ].
    induction (IHC2 _ _ _ _ (CCP_To_intro _ _ _ _ _ _ _ H10)) as [tl2F [tl2F' [C2F [s2F [HF4 [HF5 HF6] ] ] ] ] ].
    simpl. 

    (* problems here also *)
    set (tl' := @RL_Sel _ Value Var RecVar p q l).
    exists (forget tl'::tlF), (forget tl'::tlF'), CF, sF.
    repeat split; auto. econstructor; eauto.
    econstructor; eauto.
    unfold tl'; constructor; constructor; ESEr.
    inversion_clear HF3.
    induction c2 as [ [Defs' C'' ] s''].
    generalize (CCP_To_Defs_stable _ _ _ _ _ _ _ _ H) as HDefs; intro.
    rewrite <- HDefs in *; clear Defs' HDefs.
    econstructor; eauto.
    * inversion H. constructor. apply C_Delay_Eta; eauto.
      induction t; induction tl; inversion H5; auto.
    * econstructor; eauto.
      constructor. unfold tl'; constructor; ESEr.




(* Lemma : P --[tl]-->* P' iff amend(P) --[tl']-->* amend(P')

p.e -> q.x;; If r ?? b Then r.e' -> p.y Else 0

-->

p.e -> q.x ;; r.e' -> p.y


(* amended *)
p.e -> q.x;; If r ?? b Then r --> p[l];; r.e' -> p.y Else r --> p[r]

-->

p.e -> q.x;; r --> p[l];; r.e' -> p.y


*)

(*
if P -->* P' and amend(P) -->* P''
then there exists P''' such that
  P' -->* P''' and P'' -->* amend(P''')
*)

(*
Lemma amend_reduce_1 : forall Defs C p sigma t C' sigma',
  CCC_To Defs (amend Defs C p) sigma t C' sigma' ->
  
*)

Inductive more_sels : Choreography -> Choreography -> Prop :=
| MS_refl C : more_sels C C
| MS_Eta eta C C' : more_sels C C' -> more_sels (eta;;C) (eta;;C')
| MS_If p b C1 C1' C2 C2' : more_sels C1 C1' -> more_sels C2 C2' ->
      more_sels (If p ?? b Then C1 Else C2) (If p ?? b Then C1' Else C2')
| MS_RT_Call X ps C C' : more_sels C C' -> more_sels (RT_Call X ps C) (RT_Call X ps C')
| MS_sel p q l C C' : more_sels C C' -> more_sels (p --> q[l];; C) C'
.

Lemma amend_more_sels : forall Defs C p, more_sels (amend Defs C p) C.
Proof.
induction C.
all: try (constructor; auto).
rename p into q; intro p.
change (amend Defs (If q ?? b Then C1 Else C2) p) with
    match (collapse (bproj Defs (If q ?? b Then (amend Defs C1 p) Else (amend Defs C2 p)) p)) with
    | XUndefined => If q ?? b Then (q --> p[left];; amend Defs C1 p) Else (q --> p[right];; amend Defs C2 p)
    | _ => If q ?? b Then (amend Defs C1 p) Else (amend Defs C2 p)
    end.
  elim (XUndefined_dec (collapse (bproj Defs (If q ?? b Then (amend Defs C1 p) Else (amend Defs C2 p)) p))); intros.
- rewrite a. constructor; constructor; auto.
- rewrite Xmatch_elim; auto. constructor; auto.
Qed.

(*
C1 R C2
C1 --> C1'

* C1' R than C2
* C2 --> C2' and C1' R C2'

C1 : If r.e Then p --> q[l] Else p --> q[l]
C2 : If r.e Then p --> q[l] Else 0
*)

Lemma more_sels_reduce_1 : forall C1 C2, more_sels C1 C2 ->
  forall Defs sigma t C1' sigma', CCC_To Defs C1 sigma t C1' sigma' ->
  more_sels C1' C2 \/ exists C2', CCC_To Defs C2 sigma t C2' sigma' /\ more_sels C1' C2'.
Proof.
intros C1 C2 H. induction H; intros.
- right. exists C1'. split; auto. constructor.
- inversion H0.
  + right. exists C'; split; auto. constructor; auto. rewrite <- H5; auto.
  + right. exists C'; split; auto. constructor; auto. rewrite <- H5; auto.
  + rewrite <- H6 in H0.
    clear s' H7 C1' H6 t0 H5 s H4 C0 H2 eta0 H1.
    elim (IHmore_sels _ _ _ _ _ H8); intros.
    left; constructor; auto.
    right. inversion_clear H1. inversion_clear H2. rename x into C2'.
    exists (eta;; C2'). split; constructor; auto.
- inversion H1.
  + right. exists C1'; split; auto. constructor; auto. rewrite <- H8; auto.
  + right. exists C2'; split; auto. constructor; auto. rewrite <- H8; auto.
  + elim (IHmore_sels1 _ _ _ _ _ H11); elim (IHmore_sels2 _ _ _ _ _ H12); intros.
    * left. constructor; auto.
    * 

Abort.

(** MOVE ME *)


Section ComputableReduction.

Require Import Sumbool.

Notation "A '&&&' B" := (sumbool_and _ _ _ _ A B).

Fixpoint compatible (Defs:DefSet) (s:State) (tl:RichLabel) (C:Choreography) : Prop :=
  (match C, tl with
  | Call X,           R_Call Y p       => X = Y /\ In p (fst (Defs X))
  | RT_Call X ps C',  R_Call Y p       => (X = Y /\ In p ps)
                                          \/ (~In p ps /\ compatible Defs s tl C')
  | RT_Call X ps C',  R_Com p _ q _    => disjoint (p::q::nil) ps /\ compatible Defs s tl C'
  | RT_Call X ps C',  R_Sel p q _      => disjoint (p::q::nil) ps /\ compatible Defs s tl C'
  | RT_Call X ps C',  R_Cond p         => ~In p ps /\ compatible Defs s tl C'
  | Com p e q x;; C', R_Com p' v q' x' => (p=p' /\ q=q' /\ x=x' /\ v=eval_on_state e s p)
                                          \/ (disjoint (p::q::nil) (p'::q'::nil) /\ compatible Defs s tl C')
  | Com p _ q _;; C', R_Sel p' q' _    => (disjoint (p::q::nil) (p'::q'::nil) /\ compatible Defs s tl C')
  | Com p _ q _;; C', R_Cond p'        => (~In p' (p::q::nil) /\ compatible Defs s tl C')
  | Com p _ q _;; C', R_Call Y p'      => (~In p' (p::q::nil) /\ compatible Defs s tl C')
  | Sel p q l;; C',   R_Sel p' q' l'   => (p=p' /\ q=q' /\ l=l')
                                          \/ (disjoint (p::q::nil) (p'::q'::nil) /\ compatible Defs s tl C')
  | Sel p q _;; C',   R_Com p' _ q' _  => (disjoint (p::q::nil) (p'::q'::nil) /\ compatible Defs s tl C')
  | Sel p q _;; C',   R_Cond p'        => (~In p' (p::q::nil) /\ compatible Defs s tl C')
  | Sel p q _;; C',   R_Call Y p'      => (~In p' (p::q::nil) /\ compatible Defs s tl C')
  | Cond p e C1 C2,   R_Cond p'        => (p=p')
                                          \/ (p<>p' /\ compatible Defs s tl C1 /\ compatible Defs s tl C2)
  | Cond p _ C1 C2,   R_Com p' _ q' _  => (~In p (p'::q'::nil) /\ compatible Defs s tl C1 /\ compatible Defs s tl C2)
  | Cond p _ C1 C2,   R_Sel p' q' _    => (~In p (p'::q'::nil) /\ compatible Defs s tl C1 /\ compatible Defs s tl C2)
  | Cond p _ C1 C2,   R_Call Y p'      => (p<>p' /\ compatible Defs s tl C1 /\ compatible Defs s tl C2)
  | _,                _                => False
end)%MC.

(*
Fixpoint reduce_C (Defs:DefSet) (C:Choreography) (s:State) (tl:RichLabel) :=
  (match C, tl with
  | Call X,           R_Call Y p       => if (R.eq_dec X Y &&& In_dec P.eq_dec p (fst (Defs X)))
                                            then (if (Nat.eq_dec (length (fst (Defs X))) 1)
                                                  then snd (Defs X)
                                                  else (RT_Call X (set_remove_pid p (fst (Defs X))) (snd (Defs X))))
                                            else End
  | RT_Call X ps C',  R_Call Y p       => if (R.eq_dec X Y &&& In_dec P.eq_dec p ps)
                                          then (if (Nat.eq_dec (length ps) 1)
                                                then C'
                                                else (RT_Call X (set_remove_pid p ps) C'))
                                          else End
  | Com p e q x;; C', R_Com p' v q' x' => if (P.eq_dec p p' &&& P.eq_dec q q' &&& V.eq_dec (eval_on_state e s p) v)
                                          then C'
                                          else if disjoint_dec _ P.eq_dec (p::q::nil) (p'::q'::nil)
                                               then reduce_C Defs C' s tl
                                               else End
  | Com p _ q _;; C', R_Sel p' q' _    => if (disjoint_dec _ P.eq_dec (p::q::nil) (p'::q'::nil))
                                          then reduce_C Defs C' s tl
                                          else End
  | Com p _ q _;; C', R_Cond p'        => if (In_dec P.eq_dec p' (p::q::nil))
                                          then End
                                          else reduce_C Defs C' s tl
  | Com p _ q _;; C', R_Call _ p'      => if (In_dec P.eq_dec p' (p::q::nil))
                                          then End
                                          else reduce_C Defs C' s tl
  | Sel p q l;; C',   R_Sel p' q' l'   => if (P.eq_dec p p' &&& P.eq_dec q q' &&& eq_label_dec l l')
                                          then C'
                                          else if disjoint_dec _ P.eq_dec (p::q::nil) (p'::q'::nil)
                                               then reduce_C Defs C' s tl
                                               else End
  | Sel p q _;; C',   R_Com p' _ q' _  => if (disjoint_dec _ P.eq_dec (p::q::nil) (p'::q'::nil))
                                          then reduce_C Defs C' s tl
                                          else End
  | Sel p q _;; C',   R_Cond p'        => if (In_dec P.eq_dec p' (p::q::nil))
                                          then End
                                          else reduce_C Defs C' s tl
  | Sel p q _;; C',   R_Call _ p'      => if (In_dec P.eq_dec p' (p::q::nil))
                                          then End
                                          else reduce_C Defs C' s tl
  | Cond p b C1 C2,   R_Cond p'        => if P.eq_dec p p'
                                          then if beval_on_state b s p
                                               then C1 else C2
                                          else If p ? b Then (reduce_C Defs C1 s tl) Else (reduce_C Defs C2 s tl)
  | Cond p b C1 C2,   R_Com p' _ q' _  => if In_dec P.eq_dec p (p'::q'::nil)
                                          then End
                                          else If p ? b Then (reduce_C Defs C1 s tl) Else (reduce_C Defs C2 s tl)
  | Cond p b C1 C2,   R_Sel p' q' _    => if In_dec P.eq_dec p (p'::q'::nil)
                                          then End
                                          else If p ? b Then (reduce_C Defs C1 s tl) Else (reduce_C Defs C2 s tl)
  | Cond p b C1 C2,   R_Call _ p'      => if P.eq_dec p p'
                                          then End
                                          else If p ? b Then (reduce_C Defs C1 s tl) Else (reduce_C Defs C2 s tl)
  | _, _ => End
end)%MC.
*)

Fixpoint reduce_C (Defs:DefSet) (C:Choreography) (s:State) (tl:RichLabel) :=
  (match C, tl with
  | Call X,           R_Call _ p       => if Nat.eq_dec (set_size_pid (fst (Defs X))) 1
                                          then snd (Defs X)
                                          else RT_Call X (set_remove_pid p (fst (Defs X))) (snd (Defs X))
  | RT_Call X ps C',  R_Call Y p       => if In_dec P.eq_dec p ps
                                          then if Nat.eq_dec (set_size_pid ps) 1
                                               then C'
                                               else RT_Call X (set_remove_pid p ps) C'
                                          else RT_Call X ps (reduce_C Defs C' s tl)
  | RT_Call X ps C',  _                => RT_Call X ps (reduce_C Defs C' s tl)
  | Com p e q x;; C', R_Com p' v q' x' => if (P.eq_dec p p' &&& P.eq_dec q q' &&& V.eq_dec (eval_on_state e s p) v)
                                          then C'
                                          else Com p e q x;; reduce_C Defs C' s tl
  | Com p e q x;; C', _                => Com p e q x;; reduce_C Defs C' s tl
  | Sel p q l;; C',   R_Sel p' q' l'   => if (P.eq_dec p p' &&& P.eq_dec q q' &&& eq_label_dec l l')
                                          then C'
                                          else Sel p q l;; reduce_C Defs C' s tl
  | Sel p q l;; C',   _                => Sel p q l;; reduce_C Defs C' s tl
  | Cond p b C1 C2,   R_Cond p'        => if P.eq_dec p p'
                                          then if beval_on_state b s p
                                               then C1 else C2
                                          else If p ? b Then (reduce_C Defs C1 s tl) Else (reduce_C Defs C2 s tl)
  | Cond p b C1 C2,   _                => If p ? b Then (reduce_C Defs C1 s tl) Else (reduce_C Defs C2 s tl)
  | _, _ => End
  end)%MC.

Definition reduce_S (s:State) (tl:RichLabel) :=
  match tl with
  | R_Com _ v q x => update s q x v
  | _             => s
  end.

Lemma reduce_sound : forall Defs C s tl, MCP_WF (Build_Program Defs C) ->
  compatible Defs s tl C -> MCC_To Defs C s tl (reduce_C Defs C s tl) (reduce_S s tl).
Proof.
induction C; intros; induction tl; try inversion H0; simpl.
- rewrite <- H1. elim Nat.eq_dec; intros.
  + apply C_Call_Local'; auto.
  + apply C_Call_Start'; auto.
    elim (not_eq _ _ b); intros; auto.
    inversion H3. 2: inversion H5.
    elim (MCP_WF_Vars _ H r); auto.
    red; simpl; auto. unfold Vars; simpl. eapply set_size_0; eauto.
- apply C_Delay_Call; auto.
    2: { apply IHC; auto. eapply MCP_WF_Call; eauto. }
    clear H2 H0 H s IHC C r Defs.
    induction l; simpl; auto.
    split. split; intro; eapply H1; simpl; eauto.
    apply IHl; repeat intro. inversion_clear H.
    apply (H1 a0); split; simpl; auto.
- apply C_Delay_Call; auto.
    2: { apply IHC; auto. eapply MCP_WF_Call; eauto. }
    clear H2 H0 H s IHC C r Defs.
    induction l; simpl; auto.
    split. split; intro; eapply H1; simpl; eauto.
    apply IHl; repeat intro. inversion_clear H.
    apply (H1 a0); split; simpl; auto.
- apply C_Delay_Call; auto.
    2: { apply IHC; auto. eapply MCP_WF_Call; eauto. }
    clear H2 H0 H s IHC C r Defs.
    induction l; simpl; auto.
    split. intro; eapply H1; simpl; eauto.
    apply IHl; repeat intro. apply H1; simpl; auto.
- inversion_clear H1. rewrite H2. elim in_dec; [elim Nat.eq_dec | idtac]; intros.
  + apply C_Call_Finish'; auto.
  + apply C_Call_Enter'; auto.
    elim (not_eq _ _ b); intros; auto.
    inversion H1. 2: inversion H5.
    generalize (MCP_WF_Main _ H); simpl; intros.
    inversion H4. inversion H7.
    apply set_size_0 in H5. elim H8; auto.
  + elim b; auto.
- inversion_clear H1. elim in_dec; intros.
  + exfalso; auto.
  + apply C_Delay_Call; auto.
    2: { apply IHC; auto. eapply MCP_WF_Call; eauto. }
    clear b H3 H0 H IHC.
    induction l; simpl; auto.
    simpl in H2. split; auto.
- induction e.
  + inversion H0. inversion_clear H1. inversion_clear H3. inversion_clear H4.
    * rewrite H5, H2, H1, H3. clear H2 H1 H3 H5 H0.
      elim P.eq_dec; intro Hp. 2: elim Hp; auto.
      elim P.eq_dec; intro Hq. 2: elim Hq; auto.
      elim V.eq_dec; intro Hv. 2: elim Hv; auto.
      apply C_Com'.
    * inversion_clear H1. red in H2.
      elim P.eq_dec; intro Hp. elim (H2 p); rewrite Hp; simpl; auto.
      elim P.eq_dec; intro Hq. elim (H2 q); rewrite Hq; simpl; auto.
      elim V.eq_dec; intro Hv; simpl; apply C_Delay_Eta; auto.
      ++ simpl. split; split; intro; auto; eapply H2; simpl; eauto.
      ++ eapply IHC; auto. eapply MCP_WF_eta; eauto.
      ++ simpl. split; split; intro; auto; eapply H2; simpl; eauto.
      ++ eapply IHC; auto. eapply MCP_WF_eta; eauto.
  + inversion_clear H0. apply C_Delay_Eta; auto.
      ++ simpl. split; split; intro; auto; eapply H1; simpl; eauto.
         split; right; left; eauto.
      ++ eapply IHC; auto. eapply MCP_WF_eta; eauto.
- induction e.
  + inversion_clear H0. apply C_Delay_Eta; auto.
      ++ simpl. split; split; intro; auto; eapply H1; simpl; eauto.
         split; right; left; eauto.
      ++ eapply IHC; auto. eapply MCP_WF_eta; eauto.
  + inversion H0. inversion_clear H1. inversion_clear H3. inversion_clear H4.
    * rewrite H2, H1. clear H2 H1.
      elim P.eq_dec; intro Hp. 2: elim Hp; auto.
      elim P.eq_dec; intro Hq. 2: elim Hq; auto.
      elim eq_label_dec; intro Hl. 2: elim Hl; auto.
      apply C_Sel'.
    * inversion_clear H1. red in H2.
      elim P.eq_dec; intro Hp. elim (H2 p); rewrite Hp; simpl; auto.
      elim P.eq_dec; intro Hq. elim (H2 q); rewrite Hq; simpl; auto.
      elim eq_label_dec; intro Hl; simpl; apply C_Delay_Eta; auto.
      ++ simpl. split; split; intro; auto; eapply H2; simpl; eauto.
      ++ eapply IHC; auto. eapply MCP_WF_eta; eauto.
      ++ simpl. split; split; intro; auto; eapply H2; simpl; eauto.
      ++ eapply IHC; auto. eapply MCP_WF_eta; eauto.
- induction e.
  + inversion H0. apply C_Delay_Eta.
    * simpl. split; intro; auto; eapply H1; simpl; eauto.
    * eapply IHC; auto. eapply MCP_WF_eta; eauto.
  + inversion H0. apply C_Delay_Eta.
    * simpl. split; intro; auto; eapply H1; simpl; eauto.
    * eapply IHC; auto. eapply MCP_WF_eta; eauto.
- induction e.
  + inversion H0. apply C_Delay_Eta.
    * simpl. split; intro; auto; eapply H1; simpl; eauto.
    * eapply IHC; auto. eapply MCP_WF_eta; eauto.
  + inversion H0. apply C_Delay_Eta.
    * simpl. split; intro; auto; eapply H1; simpl; eauto.
    * eapply IHC; auto. eapply MCP_WF_eta; eauto.
- inversion_clear H2.
  apply C_Delay_Cond.
  + split; intro; eapply H1; simpl; eauto.
  + eapply IHC1; auto. eapply MCP_WF_Then; eauto.
  + eapply IHC2; auto. eapply MCP_WF_Else; eauto.
- inversion_clear H2.
  apply C_Delay_Cond.
  + split; intro; eapply H1; simpl; eauto.
  + eapply IHC1; auto. eapply MCP_WF_Then; eauto.
  + eapply IHC2; auto. eapply MCP_WF_Else; eauto.
- elim P.eq_dec; intro Hp. 2: elim Hp; auto.
  case_eq (beval_on_state b s p); intro Hb; rewrite <- Hp.
  + apply C_Then'; auto.
  + apply C_Else'; auto.
- inversion_clear H1. inversion_clear H3.
  elim P.eq_dec; intro Hp. elim H2; auto.
  apply C_Delay_Cond; auto.
  + eapply IHC1; auto. eapply MCP_WF_Then; eauto.
  + eapply IHC2; auto. eapply MCP_WF_Else; eauto.
- inversion_clear H2.
  apply C_Delay_Cond; auto.
  + eapply IHC1; auto. eapply MCP_WF_Then; eauto.
  + eapply IHC2; auto. eapply MCP_WF_Else; eauto.
Qed.

Lemma reduce_compatible : forall Defs C s tl C' s',
  MCC_To Defs C s tl C' s' -> compatible Defs s tl C.
Proof.
intros.
induction H; simpl; auto.
+ induction eta; induction t; simpl; auto.
  * right; split; auto.
    apply disjoint_Com_Com in H; auto.
  * split; auto. apply disjoint_Com_Sel in H; auto.
  * split; auto. intro.
    inversion_clear H. inversion_clear H1; auto.
    inversion_clear H; auto.
  * split; auto. intro.
    inversion_clear H. inversion_clear H1; auto.
    inversion_clear H; auto.
  * split; auto. apply disjoint_Sel_Sel in H; auto.
  * right; split; auto.
    apply disjoint_Sel_Sel in H; auto.
  * split; auto. intro.
    inversion_clear H. inversion_clear H1; auto.
    inversion_clear H; auto.
  * split; auto. intro.
    inversion_clear H. inversion_clear H1; auto.
    inversion_clear H; auto.
+ induction t; simpl; auto.
  * repeat split; auto. intro.
    inversion_clear H. inversion_clear H2; auto.
    inversion_clear H; auto.
  * repeat split; auto. intro.
    inversion_clear H. inversion_clear H2; auto.
    inversion_clear H; auto.
+ induction t; simpl; auto.
  * split; auto. apply disjoint_ps_Com in H; auto.
  * split; auto. apply disjoint_ps_Sel in H; auto.
  * split; auto. apply disjoint_ps_Cond; auto.
  * apply disjoint_ps_Call in H; auto.
Qed.

Lemma reduce_unique_1 : forall Defs C s tl C' s',
  MCP_WF (Build_Program Defs C) ->
  MCC_To Defs C s tl C' s' -> C' = reduce_C Defs C s tl.
Proof.
intros.
eapply MCC_To_deterministic_1; eauto.
apply reduce_sound; auto.
eapply reduce_compatible; eauto.
Qed.
*)

End ComputableReduction.
