Require Export Basic.
Require Export Common.

Local Open Scope nat_scope.

(** * The general type of MC choreographies
  This type is parameterized over sets of process identifiers,
  values, expressions and recursion variables. *)

Module MCBase (P X V E B R: DecType).

Module Import PSt := LState V X.
Module Import CSt := GState P V X.
Module Import Ev := Eval E X V V.
Module Import BEv := Eval B X V Bool.

Module Bdec := DecidableType B.
Module Edec := DecidableType E.
Module Rdec := DecidableType R.

Definition Expr := E.t.
Definition Expr_dec := Edec.eqb.
Definition BExpr := B.t.
Definition BExpr_dec := Bdec.eqb.
Definition RecVar := R.t.
Definition RecVar_dec := Rdec.eqb.

Definition Store := CSt.State.

Definition eval := Ev.eval.
Definition beval := BEv.eval.

(** ** Syntax of MC choreographies. *)

Section Syntax.

(** Communication actions. *)

Inductive Eta : Type :=
 | Com : Pid -> Expr -> Pid -> Var -> Eta
 | Sel : Pid -> Pid -> Label -> Eta
.

Lemma eta_eq_dec : forall (eta eta':Eta), { eta = eta' } + { eta <> eta' }.
Proof.
decide equality; try apply P.eq_dec.
+ apply X.eq_dec.
+ apply E.eq_dec.
+ decide equality.
Qed.

(*
Definition disjoint (p q r s:Pid) :=  p <> r /\ p <> s /\ q <> r /\ q <> s.

Lemma disjoint_sym : forall p q r s, disjoint p q r s -> disjoint r s p q.
Proof.
intros; inversion H; inversion_clear H1; inversion_clear H3; repeat split; auto.
Qed.

Definition independent (eta1 eta2:Eta) : Prop :=
match eta1, eta2 with
 | Com p _ q _, Com r _ s _ => disjoint p q r s
 | Com p _ q _, Sel r s _   => disjoint p q r s
 | Sel p q _, Com r _ s _   => disjoint p q r s
 | Sel p q _, Sel r s _     => disjoint p q r s
end.

Lemma independent_sym : forall eta eta', independent eta eta' ->
  independent eta' eta.
Proof.
intros; induction eta; induction eta'; inversion H; inversion_clear H1; inversion_clear H3; repeat split; auto.
Qed.

Definition unused (r:Pid) (eta:Eta) : Prop :=
match eta with
 | Com p _ q _ => p <> r /\ q <> r
 | Sel p q _   => p <> r /\ q <> r
end.
*)

(** Choreographies. *)

Inductive Choreography : Type :=
 | End         : Choreography
 | Call        : RecVar -> Choreography
 | RT_Call     : RecVar -> (list Pid) -> Choreography -> Choreography
 | Interaction : Eta -> Choreography -> Choreography
 | Cond        : Pid -> BExpr -> Choreography -> Choreography -> Choreography
.

(** A program is a pair containing all procedure definitions and the main
    choreography. *)
Record Program : Type :=
  { Procedures : RecVar -> (list Pid)*Choreography;
    Main       : Choreography }.

Definition Vars := fun P X => fst (Procedures P X).
Definition Procs := fun P X => snd (Procedures P X).

Lemma chor_eq_dec : forall (C C':Choreography), { C = C' } + { C <> C' }.
Proof.
decide equality.
+ apply R.eq_dec.
+ apply list_eq_dec.
  apply P.eq_dec.
+ apply R.eq_dec.
+ apply eta_eq_dec.
+ apply B.eq_dec.
+ apply P.eq_dec.
Qed.

(** An initial choreography is what a programmer should write. *)
Fixpoint initial (C:Choreography) : Prop :=
match C with
| End              => True
| Call _           => True
| RT_Call _ _ _    => False
| Interaction _ C' => initial C'
| Cond _ _ C1 C2   => initial C1 /\ initial C2
end.

(** Free procedure names in a choreography. *)
Definition set_union_rv := set_union R.eq_dec.

Fixpoint Free_RecVar (C:Choreography) : list RecVar :=
match C with
| End              => nil
| Call Y           => (Y::nil)
| RT_Call Y _ C'   => set_union_rv (Y::nil) (Free_RecVar C')
| Interaction _ C' => Free_RecVar C'
| Cond _ _ C1 C2   => set_union_rv (Free_RecVar C1) (Free_RecVar C2)
end.

Definition X_Free (X:RecVar) (C:Choreography) : Prop :=
  In X (Free_RecVar C).


(** A choreography is well-formed if:
    - it does not contain self-communications;
    - all recursive calls are guarded;
    - annotations are correct;
    - annotations of runtime terms are not empty.
*)

(** We start with the set of process names in a choreography. *)

Definition set_union_pid := set_union P.eq_dec.

Definition pn_eta (e:Eta) : list Pid :=
match e with
| Com p _ q _ => (set_union_pid (p::nil) (q::nil))
| Sel p q _   => (set_union_pid (p::nil) (q::nil))
end.

Fixpoint MCC_pn (C:Choreography) (Pids:RecVar -> list Pid) : list Pid :=
match C with
| End                => nil
| Call X             => Pids X
| RT_Call _ l C'     => set_union_pid l (MCC_pn C' Pids)
| Interaction eta C' => (set_union_pid (pn_eta eta) (MCC_pn C' Pids))
| Cond p _ C1 C2     => (set_union_pid (set_union_pid (p::nil) (MCC_pn C1 Pids)) (MCC_pn C2 Pids))
end.

(*
Fixpoint MCP_pn (Xs:list RecVar) (P:Program) : list Pid :=
match Xs with
| nil   => MCC_pn (Main P)
| Y::Ys => set_union_pid (MCC_pn (Procedures P Y)) (MCP_pn Ys P)
end.
*)

Definition set_equals_Pid := set_equals P.eq_dec.

Definition well_ann (P:Program) : Prop :=
  forall X, set_equals_Pid (MCC_pn (Procs P X) (Vars P)) (Vars P X).

Fixpoint guarded (C:Choreography) : Prop :=
match C with
| End             => True
| Call _          => False
| RT_Call _ _ _   => False
| Interaction _ _ => True
| Cond _ _ _ _    => True
end.

Fixpoint no_self_comm (C:Choreography) : Prop :=
match C with
| End                => True
| Call _             => True
| RT_Call _ _ C'     => no_self_comm C'
| Interaction eta C' => match eta with
                        | Com p _ q _ => p <> q
                        | Sel p q _   => p <> q
                        end /\ no_self_comm C'
| Cond _ _ C1 C2     => no_self_comm C1 /\ no_self_comm C2
end.

Fixpoint no_empty_ann (C:Choreography) : Prop :=
match C with
| End                => True
| Call _             => True
| RT_Call _ l C'     => l <> nil /\ no_empty_ann C'
| Interaction eta C' => no_empty_ann C'
| Cond _ _ C1 C2     => no_empty_ann C1 /\ no_empty_ann C2
end.

Definition Choreography_WF (C:Choreography) : Prop :=
  no_self_comm C /\ no_empty_ann C /\ guarded C.

Lemma guarded_dec : forall C, {guarded C} + {~guarded C}.
Proof.
induction C; simpl; auto.
Qed.

Lemma no_self_comm_dec : forall C, {no_self_comm C} + {~no_self_comm C}.
Proof.
induction C; simpl; auto.
+ inversion_clear IHC.
  - induction e; simpl; auto.
    * case_eq (Pid_dec p p0); simpl; intros.
      ++ right; intro.
         inversion_clear H1.
         apply H2; apply Pdec.eqb_eq; auto.
      ++ left; split; auto.
         apply Pdec.eqb_neq; auto.
    * case_eq (Pid_dec p p0); simpl; intros.
      ++ right; intro.
         inversion_clear H1.
         apply H2; apply Pdec.eqb_eq; auto.
      ++ left; split; auto.
         apply Pdec.eqb_neq; auto.
  - right; intro.
    inversion_clear H0; auto.
+ inversion_clear IHC1; inversion_clear IHC2; auto;
  right; intro; inversion_clear H1; auto.
Qed.

Lemma no_empty_ann_dec : forall C, {no_empty_ann C} + {~no_empty_ann C}.
Proof.
induction C; simpl; auto.
+ inversion_clear IHC.
  - elim (destruct_list l).
    * left; split; auto.
      inversion_clear a.
      inversion_clear X.
      rewrite H0; discriminate.
    * right; intro.
      inversion_clear H0; auto.
  - right; intro.
    inversion_clear H0; auto.
+ inversion_clear IHC1; inversion_clear IHC2; auto;
  right; intro; inversion_clear H1; auto.
Qed.

Lemma Choreography_WF_dec : forall C, {Choreography_WF C} + {~Choreography_WF C}.
Proof.
intros.
unfold Choreography_WF.
elim (guarded_dec C); intro.
2: right; intro; inversion_clear H; inversion_clear H1; auto.
elim (no_self_comm_dec C); intro.
2: right; intro; inversion_clear H; inversion_clear H1; auto.
elim (no_empty_ann_dec C); intro.
2: right; intro; inversion_clear H; inversion_clear H1; auto.
auto.
Qed.

(** A program is well-formed if there is a finite set of procedures Xs such that:
    - main and all procedures in Xs are well-formed
    - main and all procedures in Xs only call procedures in Xs
    - annotations are consistent
*)

Fixpoint within_Xs (Xs:list RecVar) (C:Choreography) : Prop :=
match C with
| End              => True
| Call X           => In X Xs
| RT_Call X _ C'   => In X Xs /\ within_Xs Xs C'
| Interaction _ C' => within_Xs Xs C'
| Cond _ _ C1 C2   => within_Xs Xs C1 /\ within_Xs Xs C2
end.

Fixpoint Program_WF_rec (Xs Ys:list RecVar) (P:Program) : Prop :=
match Xs with
| nil     => Choreography_WF (Main P) /\ within_Xs Ys (Main P)
| (X::Zs) => Choreography_WF (Procs P X) /\
               within_Xs Ys (Procs P X) /\ Program_WF_rec Zs Ys P
end.

Definition Program_WF (Xs:list RecVar) (P:Program) : Prop :=
  Program_WF_rec Xs Xs P.

Lemma within_Xs_dec : forall Xs C, {within_Xs Xs C} + {~within_Xs Xs C}.
Proof.
induction C; simpl; auto.
+ apply In_dec; apply R.eq_dec.
+ inversion_clear IHC; [elim (In_dec R.eq_dec r Xs) | idtac]; intros.
  - left; split; auto.
  - right; intro; apply b.
    inversion_clear H0; auto.
  - right; intro; apply H.
    inversion_clear H0; auto.
+ inversion_clear IHC1; inversion_clear IHC2; auto;
  right; intro; inversion_clear H1; auto.
Qed.

Lemma Program_WF_rec_dec : forall Xs Ys P,
  {Program_WF_rec Xs Ys P} + {~Program_WF_rec Xs Ys P}.
Proof.
induction Xs; simpl; intros.
+ elim (Choreography_WF_dec (Main P)); intros.
  2: right; intro; inversion_clear H; auto.
  elim (within_Xs_dec Ys (Main P)); intros.
  2: right; intro; inversion_clear H; inversion_clear H0; auto.
  auto.
+ elim (IHXs Ys P); intros.
  2: right; intro; inversion_clear H; inversion_clear H1; auto.
  clear IHXs.
  elim (Choreography_WF_dec (Procs P a)); intros.
  2: right; intro; inversion_clear H; auto.
  elim (within_Xs_dec Ys (Procs P a)); intros.
  2: right; intro; inversion_clear H; inversion_clear H1; auto.
  auto.
Qed.

Lemma Program_WF_dec : forall Xs P, {Program_WF Xs P} + {~Program_WF Xs P}.
Proof.
intros.
exact (Program_WF_rec_dec Xs Xs P).
Qed.

(** This one is not decidable. *)

Definition MCP_WF (P:Program) := exists Xs, Program_WF Xs P /\ well_ann P.

Lemma MCP_WF_Main : forall P, MCP_WF P -> Choreography_WF (Main P).
Proof.
induction P.
rename Procedures0 into Ps, Main0 into C.
simpl; intros.
inversion_clear H.
inversion_clear H0.
clear H1.
red in H.
assert (forall y, Program_WF_rec y x {|Procedures := Ps; Main := C|} -> Choreography_WF C).
2: apply H0 with x; auto.
clear H; induction y; simpl; intros.
+ inversion_clear H; auto.
+ inversion_clear H; inversion_clear H1; auto.
Qed.

End Syntax.

(** Pretty-printing rules for choreographies. *)

Notation "p # e --> q $ x" := (Com p e q x) (at level 50, e at level 9).
Notation "p --> q [ l ]" := (Sel p q l) (at level 50).
Notation "eta ';' C" := (Interaction eta C) (at level 60, right associativity).
Notation "'If' p '?' b 'Then' C1 'Else' C2" := (Cond p b C1 C2) (at level 60).

(** ** Syntactic properties *)

Section Syntactic_Properties.

(** Inversion results for free and bound variables. *)

Lemma NotFreeThen : forall X p b C1 C2,
  ~X_Free X (If p ? b Then C1 Else C2) -> ~X_Free X C1.
Proof.
intros. intro. apply H. red. simpl. apply set_union_intro1. auto.
Qed.

Lemma NotFreeElse : forall X p b C1 C2,
  ~X_Free X (If p ? b Then C1 Else C2) -> ~X_Free X C2.
Proof.
intros. intro. apply H. red. simpl. apply set_union_intro2. auto.
Qed.

(** Process names form a set.

Lemma NoDup_MCC_pn: forall C, NoDup (MCC_pn C).
Proof.
induction C.
+ (* End *)
  apply NoDup_nil.
+ (* X *)
  apply NoDup_nil.
+ (* e; C *)
  simpl; apply set_union_nodup; auto.
  induction e;
    apply set_union_nodup; apply NoDup_cons; auto; apply NoDup_nil.
+ (* Cond *)
  repeat apply set_union_nodup; eauto.
  apply NoDup_cons; auto; apply NoDup_nil.
Qed.

Lemma NoDup_MCP_pn: forall Xs P, NoDup (MCP_pn Xs P).
Proof.
induction Xs; intros; simpl.
+ apply NoDup_MCC_pn.
+ apply set_union_nodup; auto.
  apply NoDup_MCC_pn.
Qed.
*)

(* Properties of well-formedness.
   Nothing here at the moment. *)

End Syntactic_Properties.

(** ** Semantics of MC. *)

Section Semantics_Definitions.

(** NONE OF THIS ANYMORE.
(* Structural precongruence is defined in two steps.
   One-step congruence contains exactly one swap or unfolding; then we close
   under reflexivity and transitivity. For unfolding, we need some previous work. *)

Inductive Unfolded X CX : Choreography -> Choreography -> Prop :=
  | UVar : Unfolded X CX (Call X) CX
  | UEta eta C1 C2 : Unfolded X CX C1 C2 -> Unfolded X CX (eta;C1) (eta;C2)
  | UThen p b C1 C2 C' : Unfolded X CX C1 C2 ->
        Unfolded X CX (If p ? b Then C1 Else C') (If p ? b Then C2 Else C')
  | UElse p b C' C1 C2 : Unfolded X CX C1 C2 ->
        Unfolded X CX (If p ? b Then C' Else C1) (If p ? b Then C' Else C2)
.

Inductive MC_Precongr_step (Procs : RecVar -> Choreography)
 : Choreography -> Choreography -> Prop :=
 | Refl C : MC_Precongr_step Procs C C
 | EtaEta eta1 eta2 C : independent eta1 eta2 ->
        MC_Precongr_step Procs (eta1; eta2; C) (eta2; eta1; C)
 | EtaCond eta p b C1 C2 : unused p eta ->
        MC_Precongr_step Procs (eta; (If p ? b Then C1 Else C2))
                        (If p ? b Then (eta; C1) Else (eta; C2))
 | CondEta p b C1 C2 eta : unused p eta ->
        MC_Precongr_step Procs (If p ? b Then (eta; C1) Else (eta; C2))
                                      (eta; (If p ? b Then C1 Else C2))
 | CondCond p q b b' C1 C2 C3 C4 : p <> q -> MC_Precongr_step Procs
        (If p ? b Then (If q ? b' Then C1 Else C2) Else (If q ? b' Then C3 Else C4))
        (If q ? b' Then (If p ? b Then C1 Else C3) Else (If p ? b Then C2 Else C4))
 | Unfold X C1 C2 : Unfolded X (Procs X) C1 C2 -> MC_Precongr_step Procs C1 C2
 | CtxEta eta C1 C2 : MC_Precongr_step Procs C1 C2 ->
        MC_Precongr_step Procs (eta; C1) (eta; C2)
 | CtxThen p b C' C'' C : MC_Precongr_step Procs C' C'' ->
        MC_Precongr_step Procs (If p ? b Then C' Else C) (If p ? b Then C'' Else C)
 | CtxElse p b C C' C'' : MC_Precongr_step Procs C' C'' ->
        MC_Precongr_step Procs (If p ? b Then C Else C') (If p ? b Then C Else C'')
.

Inductive MC_Precongr (Procs : RecVar -> Choreography) :
  Choreography -> Choreography -> Prop :=
 | MCP_Refl C : MC_Precongr Procs C C
 | MCP_Step C1 C2 C3: MC_Precongr_step Procs C1 C2 ->
         MC_Precongr Procs C2 C3 -> MC_Precongr Procs C1 C3
.

(*
Definition Configuration : Type := Choreography * State.

Definition WellFormedConf (conf:Configuration) : Prop := WellFormed (fst conf).
*)
*)

(** Expression evaluation on the state of a process *)

Definition eval_on_state (e:Expr) (s:State) (p:Pid) : Value := eval e (s p).
Definition beval_on_state (b:BExpr) (s:State) (p:Pid) : bool := beval b (s p).

(** One-step and multi-step reduction. Multi-step reduction is simply a reflexive and transitive closure. *)

Inductive TransitionLabel : Type :=
| L_Com (p:Pid) (v:Value) (q:Pid) : TransitionLabel
| L_Sel (p:Pid) (q:Pid) (l:Label) : TransitionLabel
| L_Tau (p:Pid) : TransitionLabel
.

Definition disjoint_p_tl (p:Pid) (t:TransitionLabel) : Prop :=
match t with
| L_Com r _ s => p <> r /\ p <> s
| L_Sel r s _ => p <> r /\ p <> s
| L_Tau r     => p <> r
end.

Definition disjoint_eta_tl (eta:Eta) (t:TransitionLabel) : Prop :=
match eta with
| (p # _ --> q $ _) => disjoint_p_tl p t /\ disjoint_p_tl q t
| (p --> q [_])     => disjoint_p_tl p t /\ disjoint_p_tl q t
end.

Definition set_remove_pid := set_remove P.eq_dec.

Inductive MCC_To (Procs : RecVar -> (list Pid)*Choreography) :
  Choreography -> State -> TransitionLabel -> Choreography -> State -> Prop :=
 | C_Com p e q x C s : let v := (eval_on_state e s p) in
        MCC_To Procs (p # e --> q $ x; C) s
               (L_Com p v q)
               C (update s q x v)
 | C_Sel p q l C s : MCC_To Procs (p --> q [l]; C) s (L_Sel p q l) C s
 | C_Then p b C1 C2 s : (beval_on_state b s p = true) ->
        MCC_To Procs (If p ? b Then C1 Else C2) s (L_Tau p) C1 s
 | C_Else p b C1 C2 s : (beval_on_state b s p = false) ->
        MCC_To Procs (If p ? b Then C1 Else C2) s (L_Tau p) C2 s
 | C_Delay_Eta eta C C' s s' t: disjoint_eta_tl eta t -> 
        MCC_To Procs C s t C' s' ->
        MCC_To Procs (eta; C) s t (eta; C') s'
 | C_Delay_Cond p b C1 C2 C1' C2' s s' t: disjoint_p_tl p t -> 
        MCC_To Procs C1 s t C1' s' ->
        MCC_To Procs C2 s t C2' s' ->
        MCC_To Procs (If p ? b Then C1 Else C2) s t (If p ? b Then C1' Else C2') s'
 | C_Call_Start p X s: In p (fst (Procs X)) ->
        MCC_To Procs
               (Call X) s
               (L_Tau p)
               (RT_Call X (set_remove_pid p (fst (Procs X))) (snd (Procs X))) s
 | C_Call_Enter p ps X C s : In p ps ->
        MCC_To Procs
               (RT_Call X ps C) s
               (L_Tau p)
               (RT_Call X (set_remove_pid p ps) C) s
 | C_Call_Finish p X C s: 
        MCC_To Procs
               (RT_Call X (p::nil) C) s (L_Tau p) C s
.

Definition Configuration : Type := Program * State.

Inductive MCP_To : Configuration -> TransitionLabel -> Configuration -> Prop :=
 | MCP_To_intro Procs C s t C' s' : MCC_To Procs C s t C' s' ->
     MCP_To (Build_Program Procs C,s) t (Build_Program Procs C',s').

Inductive MCP_ToStar : Configuration -> Configuration -> Prop :=
 | MCT_Refl c : MCP_ToStar c c
 | MCT_Step c1 t c2 c3 : MCP_To c1 t c2 -> MCP_ToStar c2 c3 -> MCP_ToStar c1 c3
.

Definition terminated (P:Program) : Prop :=
match Main P with
| End    => True
| Call X => (Vars P X) = nil
| _      => False
end.

(*** PROBABLY NOT NEEDED

(** ** Head reductions

    Head reductions do not use structural precongruence.
*)

Fixpoint choreography_has_head_action
  (Procs: RecVar -> Choreography) (C:Choreography) : Prop :=
match C with
| End => False
| Call X => Procs X <> End
| eta; C' => True
| If p ? b Then C1 Else C2 => True
end.

Definition has_head_action (P : Program) : Prop :=
  choreography_has_head_action (Procedures P) (Main P).

Lemma has_head_action_dec : forall P, {has_head_action P} + {~has_head_action P}.
Proof.
induction P; unfold has_head_action; simpl.
induction Main0; simpl; auto.
case_eq (Procedures0 r); auto; left; discriminate.
Qed.

Definition HeadTo_unfolded (c:Configuration) : Configuration :=
  let P := fst c in let s := snd c in
    match (Main P) with
    | End => (P, s)
    | eta; C => match eta with
                | Com p e q x => (Build_Program (Procedures P) C,
                                  update s q x (eval_on_state e s p))
                | Sel p q l   => (Build_Program (Procedures P) C, s)
                end
    | If p ? b Then C1 Else C2 => match (beval_on_state b s p) with
                                  | true => (Build_Program (Procedures P) C1, s)
                                  | false => (Build_Program (Procedures P) C2, s)
                                  end
    | Call X => (P, s)
    end.

Definition HeadTo (c:Configuration) : Configuration :=
  let P := fst c in let s := snd c in
    match (Main P) with
    | Call X => HeadTo_unfolded (Build_Program (Procedures P) (Procedures P X),s)
    | _      => HeadTo_unfolded c
    end.

(*
Example HeadTo_Com : forall P p e q x C s,
  HeadTo (Build_Program P (p # e --> q $ x; C), s) = (Build_Program P C, update s q x (eval_on_state e s p)).
Proof. auto. Qed.

Example HeadTo_Sel : forall P p q l C s, 
  HeadTo (Build_Program P (p --> q [l]; C), s) = (Build_Program P C, s).
Proof. auto. Qed.
*)
*)

End Semantics_Definitions.

(** Notations for precongruence and reductions. *)

Notation "c --[ tl ]--> c'" := (MCP_To c tl c') (at level 50, left associativity).
Notation "c --->* c'" := (MCP_ToStar c c') (at level 50, left associativity).

Lemma not_terminated_reduces : forall P, ~terminated P ->
  MCP_WF P -> forall s, exists tl c', (P,s) --[tl]--> c'.
Proof.
induction P.
rename Procedures0 into Ps, Main0 into C.
induction C; intros.
+ elim H.
  red; simpl; auto.
+ rename r into X; set (ps := fst (Ps X)).
  unfold terminated in H; simpl in H.
  unfold Vars in H; simpl in H.
  case_eq ps.
  - intro; elim H; auto.
  - intros.
    do 2 eexists.
    do 2 constructor.
    fold ps; rewrite H1.
    left; auto.
+ case_eq l.
  - clear H IHC.
    intro; exfalso.
    generalize (MCP_WF_Main _ H0).
    simpl; intros.
    inversion_clear H1.
    inversion_clear H3.
    simpl in H1.
    rewrite H in H1; auto.
  - do 2 eexists.
    do 2 constructor.
    left; auto.
+ case_eq e; do 2 eexists; do 2 constructor.
+ case_eq (beval_on_state b s p).
  - do 2 eexists; constructor; apply C_Then; auto.
  - do 2 eexists; constructor; apply C_Else; auto.
Qed.

(*** WE ARE HERE ***)


(** ** Semantic properties *)

Section Semantics_Props.

Lemma MCP_WF_In : forall P Xs, Program_WF Xs P ->
  forall X, Main P = Call X -> In X Xs.
Proof.
intros.
red in H.
assert (forall Ys, Program_WF_rec Ys Xs P -> In X Xs); eauto.
clear H; induction Ys; simpl; intros.
+ inversion_clear H.
  rewrite H0 in H2; simpl in H2; auto.
+ destroy_as H H'; auto.
Qed.

Lemma MCP_WF_Main_no_self_comm : forall P, MCP_WF P -> no_self_comm (Main P).
Proof.
intros.
inversion_clear H.
rename x into Xs; red in H0.
assert (forall Ys, Program_WF_rec Ys Xs P -> no_self_comm (Main P)); eauto.
induction Ys; simpl; intros.
+ inversion_clear H; auto.
+ destroy_as H H'; auto.
Qed.

Lemma MCP_WF_chor : forall P Xs, Program_WF Xs P -> forall X, In X Xs ->
  Choreography_WF (Procedures P X).
Proof.
intros.
red in H.
assert (forall Ys, Program_WF_rec Ys Xs P -> In X Ys -> Choreography_WF (Procedures P X)); eauto.
clear H; induction Ys; simpl; intros.
+ inversion H1.
+ inversion_clear H1.
  - rewrite <- H2; inversion_clear H; auto.
  - destroy_as H H'; auto.
Qed.

Lemma MCP_WF_guarded : forall P Xs, Program_WF Xs P -> forall X, In X Xs ->
  guarded (Procedures P X).
Proof.
intros.
elim (MCP_WF_chor P Xs) with X; auto.
Qed.

Lemma MCP_WF_no_self_comm : forall P Xs, Program_WF Xs P -> forall X, In X Xs ->
  no_self_comm (Procedures P X).
Proof.
intros.
elim (MCP_WF_chor P Xs) with X; auto.
Qed.

Lemma MCP_WF_within : forall P Xs, Program_WF Xs P -> forall X, In X Xs ->
  within_Xs Xs (Procedures P X).
Proof.
intros.
red in H.
assert (forall Ys, Program_WF_rec Ys Xs P -> In X Ys -> within_Xs Xs (Procedures P X)); eauto.
clear H; induction Ys; simpl; intros.
+ inversion H1.
+ inversion_clear H1.
  - rewrite <- H2; destroy_as H H'; auto.
  - destroy_as H H'; auto.
Qed.

(** Head reductions are correct. *)

Lemma HeadTo_Soundness : forall P s, has_head_action P -> MCP_WF P ->
  (P,s) ---> (HeadTo (P,s)).
Proof.
intros.
unfold HeadTo; simpl.
case_eq (Main P); intros; simpl.
+ (* End *)
  red in H; rewrite H1 in H.
  inversion H.
+ (* Call *)
  rename r into X.
  case_eq (Procedures P X); intros.
  - (* End *)
    red in H; rewrite H1 in H; simpl in H.
    elim H; auto.
  - (* Call Y *)
    exfalso.
    rename r into Y.
    inversion_clear H0.
    rename x into Xs.
    generalize (MCP_WF_In _ _ H3 _ H1); intro.
    generalize (MCP_WF_guarded _ _ H3 _ H0); intro.
    rewrite H2 in H4; auto.
  - (* Eta *)
    induction P; simpl.
    rename Procedures0 into Procs, Main0 into C, c into C'.
    simpl in H1.
    induction e; constructor; simpl.
    * apply C_Struct with (p#e --> p0 $ v;C') C'; try constructor.
      (*** MCP_step_to ***)
      apply MCP_Step with (p#e --> p0 $ v;C'); try constructor.
      rewrite H1; apply Unfold with X.
      rewrite <- H2; constructor.
    * apply C_Struct with (p --> p0 [l] ;C') C'; try constructor.
      (*** MCP_step_to ***)
      apply MCP_Step with (p --> p0 [l];C'); try constructor.
      rewrite H1; apply Unfold with X.
      rewrite <- H2; constructor.
  - (* Cond *)
    induction P; simpl.
    rename Procedures0 into Procs, Main0 into C, c into C'.
    simpl in H1.
    unfold HeadTo_unfolded; simpl.
    case_eq (beval_on_state b s p); intros; simpl; constructor.
    * apply C_Struct with (If p ? b Then C' Else c0) C'; try constructor; auto.
      (*** MCP_step_to ***)
      apply MCP_Step with (If p ? b Then C' Else c0); try constructor.
      rewrite H1; apply Unfold with X.
      rewrite <- H2; constructor.
    * apply C_Struct with (If p ? b Then C' Else c0) c0; try constructor; auto.
      (*** MCP_step_to ***)
      apply MCP_Step with (If p ? b Then C' Else c0); try constructor.
      rewrite H1; apply Unfold with X.
      rewrite <- H2; constructor.
+ (* Eta *)
  unfold HeadTo_unfolded; simpl; rewrite H1.
  induction P; simpl.
  rename Procedures0 into Procs, Main0 into C, c into C'.
  simpl in H1; rewrite H1.
  induction e; simpl; try constructor; auto; constructor.
+ (* Cond *)
  unfold HeadTo_unfolded; simpl; rewrite H1.
  induction P; simpl.
  rename Procedures0 into Procs, Main0 into C, c into C'.
  simpl in H1; rewrite H1.
  case_eq (beval_on_state b s p); simpl; try constructor; auto; constructor; auto.
Qed.

Lemma eta_has_head_action : forall eta C Xs,
  choreography_has_head_action Xs (eta; C).
Proof.
red; auto.
Qed.

Lemma cond_has_head_action : forall p b C1 C2 Xs,
  choreography_has_head_action Xs (If p ? b Then C1 Else C2).
Proof.
red; auto.
Qed.

(** Properties of unfolding. *)

Lemma Unfolded_antisym : forall X CX CX' C1 C2,
  Unfolded X CX C1 C2 -> Unfolded X CX' C2 C1 -> C1 = C2.
Proof.
intros.
induction H; inversion H0; auto; try rewrite IHUnfolded; auto.
Qed.

Lemma Unfolded_pn_iff : forall X CX C C', Unfolded X CX C C' ->
  forall p, set_In p (MCC_pn C') <-> (set_In p (MCC_pn C) \/ set_In p (MCC_pn CX)).
Proof.
intros.
induction H; simpl; split; auto; intros; try inversion_clear IHUnfolded.
(* AGH *)
+ inversion_clear H; auto. elim H0.
+ elim (set_union_elim _ _ _ _ H0); intro.
  - left; apply set_union_intro1; auto.
  - elim H1; auto.
    left; apply set_union_intro2; auto.
+ inversion_clear H0.
  elim (set_union_elim _ _ _ _ H3); intro.
  - apply set_union_intro1; auto.
  - apply set_union_intro2; apply H2; auto.
  - apply set_union_intro2; apply H2; auto.
+ elim (set_union_elim _ _ _ _ H0); intro.
  elim (set_union_elim _ _ _ _ H3); intro.
  - left; do 2 apply set_union_intro1; auto.
  - elim H1; auto.
    left; apply set_union_intro1; apply set_union_intro2; auto.
  - left; apply set_union_intro2; auto.
+ inversion_clear H0.
  elim (set_union_elim _ _ _ _ H3); intro.
  elim (set_union_elim _ _ _ _ H0); intro.
  - do 2 apply set_union_intro1; auto.
  - apply set_union_intro1; apply set_union_intro2; apply H2; auto.
  - apply set_union_intro2; auto.
  - apply set_union_intro1; apply set_union_intro2; apply H2; auto.
+ elim (set_union_elim _ _ _ _ H0); intro.
  - left; apply set_union_intro1; auto.
  - elim H1; auto.
    left; apply set_union_intro2; auto.
+ inversion_clear H0.
  elim (set_union_elim _ _ _ _ H3); intro.
  - apply set_union_intro1; auto.
  - apply set_union_intro2; apply H2; auto.
  - apply set_union_intro2; apply H2; auto.
Qed.

Lemma Unfolded_pn : forall X CX C1 C2, Unfolded X CX C1 C2 -> 
  forall p, set_In p (MCC_pn C2) -> set_In p (MCC_pn CX) \/ set_In p (MCC_pn C1).
Proof.
intros.
elim (Unfolded_pn_iff _ _ _ _ H p); intros.
elim H1; auto.
Qed.

Lemma Unfolded_Free : forall X CX C C', Unfolded X CX C C' ->
  forall Y, X_Free Y C' -> X_Free Y CX \/ X_Free Y C.
Proof.
induction C; intros; simpl; inversion H; auto.
- rewrite <- H2 in H0. eapply IHC; eauto.
- rewrite <- H2 in H0. inversion_clear H0; auto.
  elim IHC1 with C3 Y; auto.
- rewrite <- H2 in H0. inversion_clear H0; auto.
  elim IHC2 with C3 Y; auto.
Qed.

Lemma Unfolded_guarded : forall X CX C C', Unfolded X CX C C' ->
  guarded C -> guarded C'.
Proof.
intros.
induction H; simpl; auto.
inversion H0.
Qed.

(** Additional properties of precongruence. *)

Lemma MCP_step_to : forall P C C', C ~< (P) C' -> C ~<= (P) C'.
Proof.
intros; apply MCP_Step with C'; auto; constructor.
Qed.

Lemma MCP_Trans : forall P C1 C2 C3,
  C1 ~<= (P) C2 -> C2 ~<= (P) C3 -> C1 ~<= (P) C3.
Proof.
intros; induction H; auto.
apply MCP_Step with C2; auto.
Qed.

Lemma CtxEta': forall P eta C1 C2,
  C1 ~<= (P) C2 -> (eta; C1) ~<= (P) (eta; C2).
Proof.
intros.
induction H; try constructor.
apply MCP_Step with (eta; C2); auto.
apply CtxEta; auto.
Qed.

Lemma CtxThen': forall P p b C' C'' C, C' ~<= (P) C'' ->
  (If p ? b Then C' Else C) ~<= (P) (If p ? b Then C'' Else C).
Proof.
intros.
induction H; try constructor.
apply MCP_Step with (If p ? b Then C2 Else C); auto.
apply CtxThen; auto.
Qed.

Lemma CtxElse': forall P p b C C' C'', C' ~<= (P) C'' ->
  (If p ? b Then C Else C') ~<= (P) (If p ? b Then C Else C'').
Proof.
intros.
induction H; try constructor.
apply MCP_Step with (If p ? b Then C Else C2); auto.
apply CtxElse; auto.
Qed.

Lemma CtxCond': forall P p b C1 C2 C3 C4, C1 ~<= (P) C2 -> C3 ~<= (P) C4 ->
  (If p ? b Then C1 Else C3) ~<= (P) (If p ? b Then C2 Else C4).
Proof.
intros.
apply MCP_Trans with (If p ? b Then C1 Else C4); [apply CtxElse' | apply CtxThen']; auto.
Qed.

Lemma MCToStar_trans : forall c1 c2 c3, c1 --->* c2 -> c2 --->* c3 -> c1 --->* c3.
Proof.
intros; induction H; auto.
apply MCT_Step with c2; auto.
Qed.

Lemma End_MCP' : forall P C C', C' ~<= (P) C -> C' = End -> C = End.
Proof.
intros.
induction H; auto.
apply IHMC_Precongr; clear C3 H1 IHMC_Precongr.
induction H; auto; try inversion H0.
rewrite H0 in H; inversion H.
Qed.

Lemma End_MCP : forall P C, End ~<= (P) C -> C = End.
Proof.
intros; apply End_MCP' with P End; auto.
Qed.

Lemma eta_MCP_step_inv : forall P eta C1 C2,
  (eta;C1) ~< (P) (eta;C2) -> C1 ~< (P) C2.
Proof.
intros; inversion H; auto; try constructor.
inversion H0; econstructor; eauto.
Qed.

Lemma Then_MCP_step_inv : forall P p b C1 C2 C,
  (If p ? b Then C1 Else C) ~< (P) (If p ? b Then C2 Else C) -> C1 ~< (P) C2.
Proof.
intros; inversion H; auto; try constructor.
inversion H0; econstructor; eauto.
Qed.

Lemma Else_MCP_step_inv : forall P p b C1 C2 C,
  (If p ? b Then C Else C1) ~< (P) (If p ? b Then C Else C2) -> C1 ~< (P) C2.
Proof.
intros; inversion H; auto; try constructor.
inversion H0; econstructor; eauto.
Qed.


Ltac l := apply set_union_intro1; auto; fail.
Ltac r := apply set_union_intro2; auto; fail.
Ltac ll := apply set_union_intro1, set_union_intro1; auto; fail.
Ltac lr := apply set_union_intro1, set_union_intro2; auto; fail.
Ltac rl := apply set_union_intro2, set_union_intro1; auto; fail.
Ltac rr := apply set_union_intro2, set_union_intro2; auto; fail.
Ltac lll := apply set_union_intro1, set_union_intro1, set_union_intro1; auto; fail.
Ltac llr := apply set_union_intro1, set_union_intro1, set_union_intro2; auto; fail.
Ltac lrl := apply set_union_intro1, set_union_intro2, set_union_intro1; auto; fail.
Ltac lrr := apply set_union_intro1, set_union_intro2, set_union_intro2; auto; fail.
Ltac rll := apply set_union_intro2, set_union_intro1, set_union_intro1; auto; fail.
Ltac rlr := apply set_union_intro2, set_union_intro1, set_union_intro2; auto; fail.
Ltac rrl := apply set_union_intro2, set_union_intro2, set_union_intro1; auto; fail.
Ltac rrr := apply set_union_intro2, set_union_intro2, set_union_intro2; auto; fail.

Ltac kill_it H := repeat (elim (set_union_elim _ _ _ _ H); clear H; intros);
     try l; try r; try ll; try lr; try rl; try rr;
     try lll; try llr; try lrl; try lrr; try rll; try rlr; try rrl; try rrr.

(** Precongruence vs well-formedness. *)

Lemma MCP_step_guarded : forall P C C', C ~< (P) C' ->
  MCP_WF (Build_Program P C) -> guarded C -> guarded C'.
Proof.
intros.
inversion_clear H0.
rename x into Xs.
induction H; simpl; auto.
induction C1; simpl; inversion H; auto.
change P with (Procedures (Build_Program P (Call r))).
apply MCP_WF_guarded with Xs; auto.
apply MCP_WF_In with (Build_Program P (Call r)); auto.
Qed.

Lemma MCP_step_wf : forall P C C', MCP_WF (Build_Program P C) -> C ~< (P) C' ->
  MCP_WF (Build_Program P C').
Proof.
intros.
rename P into Procs.
set (P := Build_Program Procs C); fold P in H.
set (P' := Build_Program Procs C').
inversion_clear H; rename x into Xs.
exists Xs.
red in H1; red.
generalize (MCP_WF_no_self_comm _ _ H1); intros.
generalize (MCP_WF_guarded _ _ H1); intros.
generalize (MCP_WF_within _ _ H1); intro H''.
revert H1.
assert (forall Ys, Program_WF_rec Ys Xs P -> (forall Y, In Y Ys -> In Y Xs) -> Program_WF_rec Ys Xs P'); auto.
induction Ys; simpl.
+ intros. clear H3; revert H1.
  induction H0; intro H'; inversion_clear H'; auto.
  * inversion H1; inversion H5; repeat (split; auto).
  * inversion H1; inversion H5; repeat (split; auto).
  * inversion H1; inversion H5; inversion H4; repeat (split; auto).
  * inversion H1; inversion H5; inversion H4.
    inversion H3; inversion H10; inversion H11; repeat (split; auto).
  * induction H0; auto.
    - inversion H1; elim IHUnfolded; repeat split; auto.
    - inversion H1; inversion H3; elim IHUnfolded; repeat split; auto.
    - inversion H1; inversion H3; elim IHUnfolded; repeat split; auto.
  * inversion H1; elim IHMC_Precongr_step; repeat split; auto.
  * inversion H1; inversion H3; elim IHMC_Precongr_step; repeat split; auto.
  * inversion H1; inversion H3; elim IHMC_Precongr_step; repeat split; auto.
+ intro.
  destroy_as H1 H'.
  repeat split; auto.
Qed.

Lemma MCP_wf : forall P C C', MCP_WF (Build_Program P C) -> C ~<= (P) C' ->
  MCP_WF (Build_Program P C').
Proof.
intros.
induction H0; auto.
apply IHMC_Precongr.
apply MCP_step_wf with C1; auto.
Qed.


(**** YAY!!!! *****)

(** Auxiliary result about unfolding - requires previous results on precongruence. *)

Lemma Unfolded_mixed : forall X Y CX CY C1 C2,
  Unfolded X CX C1 C2 -> Unfolded Y CY C2 C1 ->
  C1 = C2 \/ (CX = Call Y /\ CY = Call X /\ ~C1 ~< C2 /\ ~C2 ~< C1).
Proof.
intros; case_eq (RecVar_dec X Y); intro.
+ left; rewrite Rdec.eqb_eq in H1; rewrite <- H1 in H0.
  apply Unfolded_antisym with X CX CY; auto.
+ induction H; inversion H0; auto.
  - right; repeat split; auto;
    intro H'; pose (Call_MCP _ _ (MCP_step_to _ _ H')) as H'';
    inversion H''; rewrite Rdec.eqb_neq in H1; elim H1; auto.
  - elim IHUnfolded; auto; intro H'; [left; rewrite H' | right; destroy H']; repeat split; auto.
    * intro H''; contradiction H8; apply eta_MCP_step_inv with eta; auto.
    * intro H''; contradiction H'; apply eta_MCP_step_inv with eta; auto.
  - elim IHUnfolded; auto; intro H'; [left; rewrite H' | right; destroy H']; repeat split; auto.
    * intro H''; contradiction H10; apply Then_MCP_step_inv with p q C'; auto.
    * intro H''; contradiction H'; apply Then_MCP_step_inv with p q C'; auto.
  - elim IHUnfolded; auto; intro H'; [left; rewrite H' | right; destroy H']; repeat split; auto.
    * intro H''; contradiction H10; apply Else_MCP_step_inv with p q C'; auto.
    * intro H''; contradiction H'; apply Else_MCP_step_inv with p q C'; auto.
  - elim IHUnfolded; auto; intro H'; [left; rewrite H' | right; destroy H']; repeat split;
    rename Y0 into Z; rename CY0 into CZ; auto.
    * intro H''; contradiction H11; apply Def_MCP_step_inv with X Y CX CY Z CZ; auto.
    * intro H''; contradiction H'; apply Def_MCP_step_inv with Y X CY CX Z CZ; auto.
Qed.

Lemma MCP_step_Unfold_ctx : forall X CX C1 C2, Unfolded X CX C1 C2 -> C2 ~< C1 ->
  forall l, WellFormed_ctx C1 l -> C1 = C2.
Proof.
intros.
revert l H1; induction H0; inversion H; auto; intros.
- rename X0 into Z; rename CX0 into CZ; clear Y H1 CY H2 C0 H4 C3 H5.
  elim (Unfolded_mixed _ _ _ _ _ _ H0 H6); intros.
  + rewrite H1; auto.
  + destroy_as H1 H'; destroy_as H7 H'.
    rewrite H2 in H9; inversion H9.
- rewrite IHMC_Precongr_step with l; induction eta; inversion H5; auto.
- rewrite IHMC_Precongr_step with l; destroy_as H7 H'; auto.
- rewrite IHMC_Precongr_step with l; destroy_as H7 H'; auto.
- rewrite IHMC_Precongr_step with (X0::l); destroy_as H7 H'; auto.
Qed.

Lemma MCP_step_Unfold : forall X CX C1 C2, Unfolded X CX C1 C2 -> C2 ~< C1 ->
  WellFormed C1 -> C1 = C2.
Proof.
intros; apply MCP_step_Unfold_ctx with X CX nil; auto.
Qed.

End Semantics_Props.

Section Applications.

(** We now can prove some more results by induction on canonical proofs
    of precongruence or reduction. *)

(** Properties of termination. *)

Lemma MCP_step_not_terminated : forall C C', ~terminated C -> C ~< C' -> ~terminated C'.
Proof.
intros; intro.
apply H.
apply MCP_Step with C'; auto.
Qed.

Lemma MCP_not_terminated : forall C C', ~terminated C -> C ~<= C' -> ~terminated C'.
Proof.
intros; intro.
apply H.
apply MCP_Trans with C'; auto.
Qed.

Lemma Unfolded_head_action : forall C, has_head_action C ->
  forall X CX C', Unfolded X CX C C' -> has_head_action C'.
Proof.
intros; induction H0; auto.
inversion H.
Qed.

Lemma MCP_step_head_action : forall C, has_head_action C ->
  forall C', C ~< C' -> has_head_action C'.
Proof.
intros; induction H0; auto.
simpl; simpl in H.
eapply Unfolded_head_action; eauto.
Qed.

Lemma MCP_head_action : forall C, has_head_action C ->
  forall C', C ~<= C' -> has_head_action C'.
Proof.
intros.
induction H0; auto.
apply IHMC_Precongr; eapply MCP_step_head_action; eauto.
Qed.

Lemma eta_not_terminated : forall eta C, ~terminated (eta; C).
Proof.
intros; intro.
apply MCP_head_action in H; simpl; auto.
Qed.

Lemma cond_not_terminated : forall p q C1 C2, ~terminated (If p ? b Then C1 Else C2).
Proof.
intros; intro.
apply MCP_head_action in H; simpl; auto.
Qed.

Lemma terminated_Def : forall X C1 C2, terminated C2 -> terminated (Def X == C1 In C2).
Proof.
intros.
eapply MCP_Trans.
2: apply MCP_step_to; apply Garbage.
apply CtxRec'; auto.
Qed.

End Applications.

(** * Deadlock-freedom-by-design

  We now prove Theorem 1: every non-terminated choreography can reduce. *)

Section Progress.

(** We start with useful characterizations of being guarded and being a pure call. *)

Lemma guarded_char : forall C, guarded C -> C ~<= End \/ has_head_action C.
Proof.
induction C; intros; auto.
+ left; constructor.
+ inversion_clear H.
  elim IHC2; intros; auto.
  left; apply terminated_Def; auto.
Qed.

Lemma pure_call_char : forall C, ~terminated C -> ~has_head_action C -> pure_call C.
Proof.
induction C; simpl; auto; intros.
+ contradiction H; constructor.
+ apply IHC2; auto.
  intro; contradiction H.
  apply terminated_Def; auto.
Qed.

(** The idea of the proof is: if C is not terminated, then we can always apply
    a reduction rule, eventually by unfolding some procedure definition.
    To take care of this case, we need to be able to unfold a procedure call within the
    context of the choreography (relation Ctx_Unfolded below). *)

(** A specialization of the remove function from the standard library. *)

Fixpoint remove_Def (X:RecVar) (l:list (RecVar*Choreography)) : list (RecVar*Choreography) :=
match l with
| nil => nil
| (Y,CY) :: l' => if RecVar_dec X Y then remove_Def Y l' else (Y,CY) :: remove_Def X l'
end.

Definition add_or_replace (X:RecVar) (CX:Choreography) l := (X,CX) :: remove_Def X l.

Inductive Ctx_Unfolded : list (RecVar*Choreography) -> Choreography -> Choreography -> Prop :=
| Ctx_Unfold X CX l : List.In (X,CX) l -> Ctx_Unfolded l (Call X) CX
| Ctx_Eta eta C C' l : Ctx_Unfolded l C C' -> Ctx_Unfolded l (eta;C) (eta;C')
| Ctx_Then p q C C' CE l : Ctx_Unfolded l C C' -> Ctx_Unfolded l (If p ? b Then C Else CE) (If p ? b Then C' Else CE)
| Ctx_Else p q CT C C' l : Ctx_Unfolded l C C' -> Ctx_Unfolded l (If p ? b Then CT Else C) (If p ? b Then CT Else C')
| Ctx_Rec X CX C C' l : Ctx_Unfolded (add_or_replace X CX l) C C' -> Ctx_Unfolded l (Def X == CX In C) (Def X == CX In C')
.

(** Membership characterizations for these list functions. *)

Lemma remove_Def_not_in : forall X CX l, ~List.In (X,CX) (remove_Def X l).
Proof.
induction l; simpl; auto.
induction a.
case_eq (RecVar_dec X a); intros; intro; contradiction IHl.
- rewrite Rdec.eqb_eq in H; rewrite <- H in H0; auto.
- inversion_clear H0; auto.
  revert H; inversion H1; rewrite Rdec.eqb_refl.
  intro; inversion H.
Qed.

Lemma remove_Def_in : forall X Y CY l, X <> Y -> List.In (Y,CY) l -> List.In (Y,CY) (remove_Def X l).
Proof.
induction l; simpl; auto; intros.
induction a.
case_eq (RecVar_dec X a); intros.
- rewrite Rdec.eqb_eq in H1.
  rewrite <- H1; apply IHl; auto.
  inversion_clear H0; auto.
  contradiction H; inversion H2.
  transitivity a; auto.
- simpl; inversion_clear H0; auto.
Qed.

Lemma in_remove_Def : forall X Y CY l, List.In (Y,CY) (remove_Def X l) -> List.In (Y,CY) l.
Proof.
induction l; simpl; auto.
induction a.
case_eq (RecVar_dec X a); intros.
- right; apply IHl.
  rewrite Rdec.eqb_eq in H; rewrite <- H in H0; auto.
- inversion_clear H0; auto.
Qed.

Lemma remove_Def_neq : forall X Y CY l, List.In (Y,CY) (remove_Def X l) -> X <> Y.
Proof.
induction l; simpl; auto.
induction a.
case_eq (RecVar_dec X a); intros.
- apply IHl.
  rewrite Rdec.eqb_eq in H; rewrite <- H in H0; auto.
- inversion_clear H0; auto.
  rewrite Rdec.eqb_neq in H; revert H; inversion H1; auto.
Qed.

Lemma in_add_or_replace : forall l X CX Y CY,
  List.In (X,CX) (add_or_replace Y CY l) <-> (X = Y /\ CX = CY) \/ (X <> Y /\ List.In (X,CX) l).
Proof.
simpl; split; intros; inversion_clear H.
- inversion H0; auto.
- right; split.
  + intro; symmetry in H; revert H.
    eapply remove_Def_neq; eauto.
  + eapply in_remove_Def; eauto.
- inversion H0.
  rewrite H; rewrite H1; auto.
- inversion_clear H0; right; apply remove_Def_in; auto.
Qed.

(** Unlike regular unfolding, contextual unfolding is guaranteed to return something
    precongruent to the original choreography. *)

Lemma MCP_step_Ctx_Unfolded : forall C C', Ctx_Unfolded nil C C' -> C ~< C'.
Proof.
assert (forall C C' l, Ctx_Unfolded l C C' ->
  C ~< C' \/ exists X CX, List.In (X,CX) l /\ Unfolded X CX C C').
2: { intros.
     elim (H C C' nil); intros; auto.
     destroy_as H1 H'; inversion H2.
   }
induction C; intros; inversion H.
+ right.
  exists r, C'; split; auto; constructor.
+ clear l0 eta C0 H1 H0 H3; rename C'0 into C0.
  elim (IHC _ _ H4); intros.
  - left; constructor; auto.
  - right; destroy_as H0 H'.
    exists x, x0; split; try constructor; auto.
+ clear l0 p1 q C CE H1 H0 H3 H4 H5.
  elim (IHC1 _ _ H6); intros.
  - left; constructor; auto.
  - right; destroy_as H0 H'.
    exists x, x0; split; try constructor; auto.
+ clear l0 p1 q C CT H1 H0 H3 H4 H5.
  elim (IHC2 _ _ H6); intros.
  - left; constructor; auto.
  - right; destroy_as H0 H'.
    exists x, x0; split; try constructor; auto.
+ clear l0 X CX C H1 H0 H3 H4.
  elim (IHC2 _ _ H5); intros.
  - left; apply CtxRec; auto.
  - destroy_as H0 H'.
    elim (in_add_or_replace l x x0 r C1); intros.
    clear H4; elim H3; auto; clear H3 H1; intros.
    * left; constructor.
      inversion_clear H1.
      rewrite <- H3, <- H4; auto.
    * right; inversion_clear H1; exists x, x0; split; try constructor; auto.
Qed.

Lemma MCP_Ctx_Unfolded : forall C C', Ctx_Unfolded nil C C' -> C ~<= C'.
Proof.
intros.
apply MCP_step_to.
apply MCP_step_Ctx_Unfolded; auto.
Qed.

(** Furthermore, it is not a pure function call. *)

Lemma Ctx_Unfolded_guarded : forall C C' l,
  (forall X CX, List.In (X,CX) l -> guarded CX) ->
  Ctx_Unfolded l C C' -> WellFormed_ctx C (map fst l) -> guarded C'.
Proof.
induction C; intros; inversion H0; simpl; eauto.
clear C H6 CX H5 X H2 l0 H3.
rename C'0 into C0.
destroy_as H1 H'; split; auto.
apply IHC2 with (add_or_replace r C1 l); auto.
+ intros.
  inversion_clear H5.
  - inversion H6.
    rewrite <- H9; auto.
  - apply H with X.
    apply in_remove_Def with r; auto.
+ apply WellFormed_ctx_mon with (r:: map fst l); auto.
  simpl; intros.
  inversion_clear H5; auto.
  rewrite in_map_iff in H6.
  destroy H6; induction x.
  elim (R.eq_dec r X); auto.
  right; replace X with (fst (a,b)).
  apply in_map; apply remove_Def_in; auto.
  simpl in H5; rewrite H5; auto.
Qed.

Lemma Ctx_Unfolded_has_head : forall C C',
  Ctx_Unfolded nil C C' -> WellFormed C -> ~terminated C -> has_head_action C'.
Proof.
intros.
generalize (MCP_Ctx_Unfolded _ _ H); intro.
assert (forall (X:RecVar) CX, List.In (X,CX) nil -> guarded CX).
1: intros; inversion H3.
generalize (Ctx_Unfolded_guarded _ _ _ H3 H H0); intro.
assert (~terminated C').
1: intro; apply H1; apply MCP_Trans with C'; auto.
induction C'; auto.
1: inversion H; inversion H6.
inversion H.
1: inversion H6.
clear H11 C'; rename C'2 into C'.
rewrite H10 in H8; clear H10 CX; rename C'1 into CX.
rewrite H6 in H8; clear H6 X; rename r into X.
clear H7 l.
unfold add_or_replace in H9; simpl in H9.
inversion_clear H4.
elim (guarded_char _ H7); intros; auto.
contradiction H5.
apply terminated_Def; auto.
Qed.

Lemma pure_call_Ctx_Unfolded : forall C, pure_call C -> WellFormed C ->
  exists C', Ctx_Unfolded nil C C'.
Proof.
assert (forall C l, pure_call C -> WellFormed_ctx C (map fst l) -> exists C', Ctx_Unfolded l C C'); auto.
induction C; simpl; intros; try inversion H.
+ rewrite in_map_iff in H0; destroy_as H0 H'.
  induction x.
  exists b; constructor.
  simpl in H1; rewrite <- H1; auto.
+ destroy_as H0 H'.
  elim IHC2 with (add_or_replace r C1 l); auto.
  - intros; exists (Def r == C1 In x); constructor; auto.
  - apply WellFormed_ctx_mon with (r :: map fst l); auto.
    clear H0 H2 H1 H IHC1 IHC2 C2.
    simpl; intros.
    inversion_clear H; auto.
    elim (R.eq_dec r X); auto.
    rewrite in_map_iff in H0; destroy H0.
    induction x.
    rewrite <- H; right.
    apply in_map; apply remove_Def_in; auto.
Qed.

(** Now we can prove that any non-terminated choreography is precongruent
    to a choreography with head action, which has a head reduction. *)

Lemma not_terminated_has_head_action : forall C, ~terminated C ->
  WellFormed C -> exists C', has_head_action C' /\ C ~<= C'.
Proof.
intros.
elim (has_head_action_dec C); intro.
+ exists C; split; auto; constructor.
+ elim (pure_call_Ctx_Unfolded C); auto.
  2: apply pure_call_char; auto.
  intro C'; intros.
  exists C'; split; auto.
  - apply Ctx_Unfolded_has_head with C; auto.
  - apply MCP_Ctx_Unfolded; auto.
Qed.

Theorem progress : forall C s, ~(terminated C) -> WellFormed C -> exists c', (C,s) ---> c'.
Proof.
intros.
elim (not_terminated_has_head_action C); auto.
intros C' HC'; destroy HC'.
set (c := HeadTo (C',s) H1).
assert (c = HeadTo (C',s) H1); auto; clearbody c.
exists c; induction c.
rename a into C''; rename b into s'.
apply C_Struct with C' C''; auto.
+ constructor.
+ rewrite H2; apply HeadTo_Soundness.
Qed.

End Progress.

(** *  Weighted Relations *)

Section Weighted_Relations.

(** Many proofs in MC are by induction on the proof of precongruence/reduction.
    However, since these are dependent types, formalizing them directly requires using
    Coq.Program.Equality, which imports axioms.
    In order to do these proofs faithfully, we clone these types with a weight - the
    size of the derivation.

    For precongruence, we also get a canonical representation: any precongruence proof can be split into a sequence of unfoldings followed by reversible rewritings and a sequence of garbage collection steps. *)

Definition Precongruence := Choreography -> Choreography -> Prop.
Definition WeightedRelation (T:Type) := nat -> T -> T -> Prop.
Definition WeightedPrecongruence := WeightedRelation (Choreography).

Inductive Precongr_unfold : Precongruence :=
| MCP_Unfold X CX C1 C2 : Unfolded X CX C1 C2 -> Precongr_unfold (Def X == CX In C1) (Def X == CX In C2)
.

Inductive Precongr_sym : Precongruence :=
| MCP_EtaEta eta1 eta2 C : independent eta1 eta2 -> Precongr_sym (eta1; eta2; C) (eta2; eta1; C)
| MCP_EtaCond eta p q C1 C2 : unused p eta -> unused q eta -> Precongr_sym (eta; (If p ? b Then C1 Else C2)) (If p ? b Then (eta; C1) Else (eta; C2))
| MCP_CondEta eta p q C1 C2 : unused p eta -> unused q eta -> Precongr_sym (If p ? b Then (eta; C1) Else (eta; C2)) (eta; (If p ? b Then C1 Else C2))
| MCP_CondCond p q r s C1 C2 C3 C4 : disjoint p q r s -> Precongr_sym (If p ? b Then (If r == s Then C1 Else C2) Else (If r == s Then C3 Else C4))
                                                              (If r == s Then (If p ? b Then C1 Else C3) Else (If p ? b Then C2 Else C4))
| MCP_EtaRec eta X CX C : Precongr_sym (eta; Def X == CX In C) (Def X == CX In (eta;C))
| MCP_RecEta eta X CX C : Precongr_sym (Def X == CX In (eta;C)) (eta; Def X == CX In C)
| MCP_CondRec p q X CX C1 C2 : Precongr_sym (If p ? b Then Def X == CX In C1 Else Def X == CX In C2) (Def X == CX In If p ? b Then C1 Else C2)
| MCP_RecCond p q X CX C1 C2 : Precongr_sym (Def X == CX In If p ? b Then C1 Else C2) (If p ? b Then Def X == CX In C1 Else Def X == CX In C2)
| MCP_RecRec X CX Y CY C : X <> Y -> ~Free X CY -> ~Free Y CX -> Precongr_sym (Def X == CX In (Def Y == CY In C)) (Def Y == CY In (Def X == CX In C))
.

Inductive Precongr_garbage : Precongruence :=
| MCP_Garbage X C : Precongr_garbage (Def X == C In End) End
.

Inductive CtxClose (R:Precongruence) : WeightedPrecongruence :=
| WCtxBase C C' : R C C' -> CtxClose R 0 C C'
| WCtxEta n eta C1 C2 : CtxClose R n C1 C2 -> CtxClose R (S n) (eta; C1) (eta; C2)
| WCtxThen n p q C' C'' C : CtxClose R n C' C'' -> CtxClose R (S n) (If p ? b Then C' Else C) (If p ? b Then C'' Else C)
| WCtxElse n p q C C' C'' : CtxClose R n C' C'' -> CtxClose R (S n) (If p ? b Then C Else C') (If p ? b Then C Else C'')
| WCtxRec n X C1 C2 C2' : CtxClose R n C2 C2' -> CtxClose R (S n) (Def X == C1 In C2) (Def X == C1 In C2')
.

Inductive TransClose {T} (R:WeightedRelation T) : WeightedRelation T :=
| TBase C : TransClose R 0 C C
| TStep {n k C} C' {C''} : R n C C' -> TransClose R k C' C'' -> TransClose R (S (n+k)) C C''
.

(** The transitive closure of R is actually transitive. *)

Lemma TTrans : forall {T} (R:WeightedRelation T) n1 n2 C C' C'',
  TransClose R n1 C C' -> TransClose R n2 C' C'' -> TransClose R (n1+n2) C C''.
Proof.
do 2 intro.
assert (forall n1 k n2 C C' C'', k<n1 -> TransClose R k C C' -> TransClose R n2 C' C'' -> TransClose R (k+n2) C C''); eauto.
induction n1; intros; simpl; [inversion H | inversion H0]; auto.
+ clear C''0 H6 C0 H5 H0.
  rewrite <- H4 in H; clear k H4; apply lt_S_n in H.
  assert (k0 < n1). apply le_lt_trans with (n+k0); auto with arith.
  replace (S (n+k0)+n2) with ((S n) + (k0+n2)). 2: ring.
  apply TStep with C'0; eauto.
Qed.

Lemma MCP_step_CtxClose : forall (R:Precongruence), (forall C C', R C C' -> C ~< C') ->
  forall n C C', CtxClose R n C C' -> C ~< C'.
Proof.
induction n; intros.
+ inversion H0; auto.
+ inversion H0; try (constructor; auto; fail).
Qed.

Lemma MCP_CtxClose : forall (R:Precongruence), (forall C C', R C C' -> C ~<= C') ->
  forall n C C', CtxClose R n C C' -> C ~<= C'.
Proof.
induction n; intros; inversion H0; auto.
+ apply CtxEta'; auto.
+ apply CtxThen'; auto.
+ apply CtxElse'; auto.
+ apply CtxRec'; auto.
Qed.

Lemma MCP_step_TransClose : forall (R:WeightedPrecongruence), (forall n C C', R n C C' -> C ~< C') ->
  forall n C C', TransClose R n C C' -> C ~<= C'.
Proof.
intros R HR.
assert (forall n k C C', k<n -> TransClose R k C C' -> C ~<= C'); eauto.
induction n; intros; try (inversion H; fail); inversion H0.
+ constructor.
+ rewrite <- H3 in H; apply lt_S_n in H.
  apply MCP_Trans with C'0.
  - apply MCP_step_to; eauto.
  - apply IHn with k0; auto.
    apply le_lt_trans with (n0+k0); auto with arith.
Qed.

Lemma MCP_TransClose : forall (R:WeightedPrecongruence), (forall n C C', R n C C' -> C ~<= C') ->
  forall n C C', TransClose R n C C' -> C ~<= C'.
Proof.
intros R HR.
assert (forall n k C C', k<n -> TransClose R k C C' -> C ~<= C'); eauto.
induction n; intros; try (inversion H; fail); inversion H0.
+ constructor.
+ rewrite <- H3 in H; apply lt_S_n in H.
  apply MCP_Trans with C'0; eauto.
  apply IHn with k0; auto.
  apply le_lt_trans with (n0+k0); auto with arith.
Qed.

Definition UPrecongr_step := CtxClose Precongr_unfold.
Definition SPrecongr_step := CtxClose Precongr_sym.
Definition GPrecongr_step := CtxClose Precongr_garbage.

Definition UPrecongr := TransClose UPrecongr_step.
Definition SPrecongr := TransClose SPrecongr_step.
Definition GPrecongr := TransClose GPrecongr_step.

Inductive MC_Precongr_weighted : Choreography -> Choreography -> Prop :=
| PWIntro n1 n2 n3 C1 C2 C3 C4 : UPrecongr n1 C1 C2 -> SPrecongr n2 C2 C3 -> GPrecongr n3 C3 C4 -> MC_Precongr_weighted C1 C4.

End Weighted_Relations.

(** Pretty-printing. *)

Notation "C $ n ~<u C'" := (UPrecongr_step n C C') (at level 50).
Notation "C $ n ~<>~ C'" := (SPrecongr_step n C C') (at level 50).
Notation "C $ n g>~ C'" := (GPrecongr_step n C C') (at level 50).
Notation "C $ n ~<=u C'" := (UPrecongr n C C') (at level 50).
Notation "C $ n ~<=>~ C'" := (SPrecongr n C C') (at level 50).
Notation "C $ n g>=~ C'" := (GPrecongr n C C') (at level 50).
Notation "C ~<=n C'" := (MC_Precongr_weighted C C') (at level 50).

(** We first show that these relations precisely correspond to the unweighted ones. *)

Section Weighted_Reductions.

(** ** Soundness
       Weighted relations imply non-weighted ones. *)

Lemma Precongr_unfold_to_step : forall C1 C2, Precongr_unfold C1 C2 -> C1 ~< C2.
Proof.
intros. inversion H; constructor; auto.
Qed.

Lemma Precongr_sym_to_step : forall C1 C2, Precongr_sym C1 C2 -> C1 ~< C2.
Proof.
intros. inversion H; constructor; auto.
Qed.

Lemma Precongr_garbage_to_step : forall C1 C2, Precongr_garbage C1 C2 -> C1 ~< C2.
Proof.
intros. inversion H; constructor; auto.
Qed.

Lemma MCP_to_weighted : forall C C', C ~<=n C' -> C ~<= C'.
Proof.
intros.
inversion H.
apply MCP_Trans with C2; [idtac | apply MCP_Trans with C3];
  eapply MCP_step_TransClose; eauto;
  eapply MCP_step_CtxClose; eauto.
+ exact Precongr_unfold_to_step.
+ exact Precongr_sym_to_step.
+ exact Precongr_garbage_to_step.
Qed.

(** ** Compatibility
       The transitive closure of a contextual closure is also contextually closed. *)

Lemma TCtxEta : forall {R n} eta {C C'}, CtxClose R n C C' -> TransClose (CtxClose R) (S (S n)) (eta;C) (eta;C').
Proof.
intros.
replace (S n) with ((S n)+0); auto.
eapply TStep; eauto; constructor; auto.
Qed.

Lemma TCtxThen : forall {R n} p q CT {C C'}, CtxClose R n C C' ->
  TransClose (CtxClose R) (S (S n)) (If p ? b Then CT Else C) (If p ? b Then CT Else C').
Proof.
intros.
replace (S n) with ((S n)+0); auto.
eapply TStep; eauto; constructor; auto.
Qed.

Lemma TCtxElse : forall {R n} p q {C C'} CE, CtxClose R n C C' ->
  TransClose (CtxClose R) (S (S n)) (If p ? b Then C Else CE) (If p ? b Then C' Else CE).
Proof.
intros.
replace (S n) with ((S n)+0); auto.
eapply TStep; eauto; constructor; auto.
Qed.

Lemma TCtxRec : forall {R n} X CX {C C'}, CtxClose R n C C' ->
  TransClose (CtxClose R) (S (S n)) (Def X == CX In C) (Def X == CX In C').
Proof.
intros.
replace (S n) with ((S n)+0); auto.
eapply TStep; eauto; constructor; auto.
Qed.

Lemma TCtxEta' : forall {R n} eta {C C'}, TransClose (CtxClose R) n C C' -> 
  exists n', TransClose (CtxClose R) n' (eta;C) (eta;C').
Proof.
intros.
assert (forall n k C C', k<n -> TransClose (CtxClose R) k C C' -> exists n', TransClose (CtxClose R) n' (eta;C) (eta;C')); eauto.
clear n C C' H. induction n; intros; [inversion H | inversion H0].
+ exists 0; constructor.
+ rewrite <- H3 in H; apply lt_S_n in H; clear k H3 H0.
  assert (k0 < n). apply le_lt_trans with (n0+k0); auto with arith.
  elim (IHn _ _ _ H0 H2); intros n' Hn'.
  exists (S (S n0) + n'); econstructor; eauto.
  constructor; auto.
Qed.

Lemma TCtxThen' : forall {R n} p q CT {C C'}, TransClose (CtxClose R) n C C' ->
  exists n', TransClose (CtxClose R) n' (If p ? b Then CT Else C) (If p ? b Then CT Else C').
Proof.
intros.
assert (forall n k C C', k<n -> TransClose (CtxClose R) k C C' -> exists n', TransClose (CtxClose R) n' (If p ? b Then CT Else C) (If p ? b Then CT Else C')); eauto.
clear n C C' H. induction n; intros; [inversion H | inversion H0].
+ exists 0; constructor.
+ rewrite <- H3 in H; apply lt_S_n in H; clear k H3 H0.
  assert (k0 < n). apply le_lt_trans with (n0+k0); auto with arith.
  elim (IHn _ _ _ H0 H2); intros n' Hn'.
  exists (S (S n0) + n'); econstructor; eauto.
  constructor; auto.
Qed.

Lemma TCtxElse' : forall {R n} p q {C C'} CE, TransClose (CtxClose R) n C C' ->
  exists n', TransClose (CtxClose R) n' (If p ? b Then C Else CE) (If p ? b Then C' Else CE).
Proof.
intros.
assert (forall n k C C', k<n -> TransClose (CtxClose R) k C C' -> exists n', TransClose (CtxClose R) n' (If p ? b Then C Else CE) (If p ? b Then C' Else CE)); eauto.
clear n C C' H. induction n; intros; [inversion H | inversion H0].
+ exists 0; constructor.
+ rewrite <- H3 in H; apply lt_S_n in H; clear k H3 H0.
  assert (k0 < n). apply le_lt_trans with (n0+k0); auto with arith.
  elim (IHn _ _ _ H0 H2); intros n' Hn'.
  exists (S (S n0) + n'); econstructor; eauto.
  constructor; auto.
Qed.

Lemma TCtxRec' : forall {R n} X CX {C C'}, TransClose (CtxClose R) n C C' ->
  exists n', TransClose (CtxClose R) n' (Def X == CX In C) (Def X == CX In C').
Proof.
intros.
assert (forall n k C C', k<n -> TransClose (CtxClose R) k C C' -> exists n', TransClose (CtxClose R) n' (Def X == CX In C) (Def X == CX In C')); eauto.
clear n C C' H. induction n; intros; [inversion H | inversion H0].
+ exists 0; constructor.
+ rewrite <- H3 in H; apply lt_S_n in H; clear k H3 H0.
  assert (k0 < n). apply le_lt_trans with (n0+k0); auto with arith.
  elim (IHn _ _ _ H0 H2); intros n' Hn'.
  exists (S (S n0) + n'); econstructor; eauto.
  constructor; auto.
Qed.

(** ** Completeness
       Non-weighted relations can be made weighted. *)

(** Base case *)

Lemma MCP_step_to_weighted_str : forall C C', C ~< C' ->
  C=C' \/ (exists n, C$n ~<u C') \/ (exists n, C$n ~<>~ C') \/ (exists n, C$n g>~ C').
Proof.
intros; induction H;
  auto;
  try (right; left; exists 0; constructor; constructor; auto; fail);
  try (right; right; left; exists 0; constructor; constructor; auto; fail);
  try (right; right; right; exists 0; constructor; constructor; auto; fail);
  (elim IHMC_Precongr_step; intro H';
    [ rewrite H'; auto|
      elim H'; clear H'; intro H'; [right; left |
      elim H'; clear H'; intro H'; [right; right; left | right; right; right]]]);
  elim H'; clear H'; intros n Hn;
  exists (S n); constructor; auto.
Qed.

Section Transitivity.

Variable R R':WeightedPrecongruence.
Hypothesis RR'_comm : (forall n1 n2 C C' C'', R n1 C C' -> R' n2 C' C'' -> exists C0, R' n2 C C0 /\ R n1 C0 C'').

Lemma TransClose_comm' : forall n1 n2 C C' C'', TransClose R n1 C C' -> R' n2 C' C'' ->
  exists C0, R' n2 C C0 /\ TransClose R n1 C0 C''.
Proof.
set (RT := TransClose R).
assert (forall n1 k n2 C C' C'', k<n1 -> RT k C C' -> R' n2 C' C'' -> exists C0, R' n2 C C0 /\ RT k C0 C''); eauto.
induction n1; intros; [inversion H | inversion H0].
+ exists C''; split; auto; constructor.
+ clear C''0 H6 H5 H0.
  rewrite <- H4 in H; clear k H4; apply lt_S_n in H.
  assert (k0 < n1). apply le_lt_trans with (n + k0); auto with arith.
  elim (IHn1 _ _ _ _ _ H0 H3 H1); intros.
  destroy_as H4 H'.
  clear H H3 C' H1 H0.
  elim (RR'_comm _ _ _ _ _ H2 H5); intros.
  destroy_as H H'.
  rename x into C1; rename x0 into C3.
  exists C3; split; auto.
  change (RT (S n + k0) C3 C''). apply TTrans with C1; auto.
  replace (S n) with (S n + 0); auto with arith.
  apply TStep with C1; auto. constructor.
Qed.

Lemma TransClose_comm : forall n1 n2 C C' C'', TransClose R n1 C C' -> TransClose R' n2 C' C'' ->
  exists C0, TransClose R' n2 C C0 /\ TransClose R n1 C0 C''.
Proof.
set (RT := TransClose R); set (RT' := TransClose R').
assert (forall n2 k n1 C C' C'', k<n2 -> RT n1 C C' -> RT' k C' C'' -> exists C0, RT' k C C0 /\ RT n1 C0 C''); eauto.
induction n2; intros; [inversion H | inversion H1]; intros.
+ rewrite <- H4; exists C; split; auto; constructor.
+ clear C''0 H6 C0 H5 H1.
  rewrite <- H4 in H; clear k H4; apply lt_S_n in H.
  assert (k0 < n2). apply le_lt_trans with (n+k0); auto with arith.
  fold UPrecongr in H3.
  elim (TransClose_comm' _ _ _ _ _ H0 H2); intros.
  destroy_as H4 H'.
  clear H0 H2. rename x into C0.
  elim (IHn2 _ _ _ _ _ H1 H4 H3); intros.
  destroy_as H0 H'.
  clear H1 H4 H3. rename x into C1.
  exists C1; split; auto.
  apply TStep with C0; auto.
Qed.

End Transitivity.

(** Unfolding can be pushed before reversible rewriting. *)

Lemma Precongr_sym_Unfolded_comm : forall n X CX C C' C'', C$n ~<>~ C' -> Unfolded X CX C' C'' ->
  exists C0, Unfolded X CX C C0 /\ C0$n ~<>~ C''.
Proof.
induction n; intros.
+ revert H0. inversion H. inversion H0; intros.
  - inversion H6. inversion H10.
    eexists; split; [repeat constructor | constructor; apply MCP_EtaEta]; auto.
  - inversion H7; inversion H13;
      (eexists; split; [repeat constructor | constructor; apply MCP_EtaCond]; auto).
  - inversion H7. inversion H11;
      (eexists; split; [repeat constructor | constructor; apply MCP_CondEta]; auto).
  - inversion H6; inversion H12;
      (eexists; split; [repeat constructor | constructor; apply MCP_CondCond]; auto).
  - inversion H5. inversion H11.
    eexists; split; [repeat constructor | constructor; apply MCP_EtaRec]; auto.
  - inversion H5. inversion H9.
    eexists; split; [repeat constructor | constructor; apply MCP_RecEta]; auto.
  - inversion H5. inversion H11;
      (eexists; split; [repeat constructor | constructor; apply MCP_CondRec]; auto).
  - inversion H5; inversion H11;
      (eexists; split; [repeat constructor | constructor; apply MCP_RecCond]; auto).
  - rename X0 into Z; rename CX0 into CZ.
    inversion H8. inversion H14.
    eexists; split; [repeat constructor | constructor; apply MCP_RecRec]; auto.
+ revert H0. inversion H; intro; inversion H4.
  - elim (IHn _ _ _ _ _ H1 H8); intros.
    inversion_clear H9. rename x into C4.
    exists (eta;C4); split; constructor; auto.
  - elim (IHn _ _ _ _ _ H1 H10); intros.
    inversion_clear H11. rename x into C4.
    exists (If p ? b Then C4 Else C0); split; constructor; auto.
  - exists (If p ? b Then C'0 Else C2); split; constructor; auto.
  - exists (If p ? b Then C2 Else C'0); split; constructor; auto.
  - elim (IHn _ _ _ _ _ H1 H10); intros.
    inversion_clear H11. rename x into C4.
    exists (If p ? b Then C0 Else C4); split; constructor; auto.
  - elim (IHn _ _ _ _ _ H1 H10); intros.
    inversion_clear H11. rename x into C4.
    exists (Def X0 == C1 In C4); split; constructor; auto.
Qed.

Lemma Precongr_sym_Unfolded_comm' : forall n X CX CX' C C', CX$n ~<>~ CX' -> Unfolded X CX' C C' ->
  exists n' C0, Unfolded X CX C C0 /\ C0$n' ~<>~ C'.
Proof.
intros. revert n X CX CX' C' H H0.
induction C; intros; inversion H0.
+ rewrite H2 in H0; rewrite <- H1; clear H2 X H0 H1 C'; rename r into X.
  exists n, CX; split; try constructor; auto.
+ elim (IHC _ _ _ _ _ H H4); intros.
  inversion_clear H5.
  rename x into n'; rename x0 into C0; inversion_clear H6.
  exists (S n'), (e; C0); split; try constructor; auto.
+ elim (IHC1 _ _ _ _ _ H H6); intros.
  inversion_clear H7.
  rename x into n'; rename x0 into C4; inversion_clear H8.
  exists (S n'), (If p == p0 Then C4 Else C2); split; try constructor; auto.
+ elim (IHC2 _ _ _ _ _ H H6); intros.
  inversion_clear H7.
  rename x into n'; rename x0 into C4; inversion_clear H8.
  exists (S n'), (If p == p0 Then C1 Else C4); split; try constructor; auto.
+ elim (IHC2 _ _ _ _ _ H H6); intros.
  inversion_clear H7.
  rename x into n'; rename x0 into C4; inversion_clear H8.
  exists (S n'), (Def r == C1 In C4); split; try constructor; auto.
Qed.

Lemma Precongr_sym_unfold_comm : forall n1 n2 C C' C'', C$n1 ~<>~ C' -> C'$n2 ~<u C'' ->
  exists n2' C0, C$n2' ~<u C0 /\ C0$n1 ~<>~ C''.
Proof.
intros.
revert n1 C C' C'' H0 H. induction n2; do 5 intro.
+ inversion H0. clear C0 C'0 H2 H3 H0.
  inversion H. clear C' C'' H1 H2 H.
  intro. inversion H; clear H.
  - clear C' H4 C0 H3 n1 H2.
    revert H0; inversion H1; intro; inversion H0.
    * exists 1; eexists; split;
       [repeat constructor; eauto | constructor; apply MCP_EtaRec].
    * exists 1; eexists; split;
       [repeat constructor; eauto | constructor; apply MCP_CondRec].
    * exists 1; eexists; split;
       [repeat constructor; eauto | constructor; apply MCP_CondRec].
    * inversion H7.
      exists 1; eexists; split;
       [repeat constructor; eauto | constructor; apply MCP_RecRec]; auto.
  - clear C2' H6 C0 H5 X0 H1 C H3 n1 H2.
    fold SPrecongr_step in H4.
    elim (Precongr_sym_Unfolded_comm _ _ _ _ _ _ H4 H0); intros.
    inversion_clear H.
    exists 0; eexists; split. repeat constructor; eauto.
    constructor; eauto.
+ inversion H0; fold UPrecongr_step in H1; clear C' C'' H2 H3 H0 n H; intros.
  - inversion H; clear H; [inversion H0; clear H0 | idtac].
    * clear eta2 H C0 H3 n1 H2 C H5.
      rewrite <- H7 in H1; clear H7 H4 C' C1.
      inversion H1.
      ++ inversion H.
      ++ fold UPrecongr_step in H4.
         eexists; eexists; split;
         [do 2 apply WCtxEta; eauto | constructor; apply MCP_EtaEta; auto].
    * rewrite <- H5 in H1. clear H5 C' H4 C1.
      rewrite H in H6; clear eta0 H C0 H3 n1 H2 H6 C.
      inversion H1.
      ++ inversion H.
      ++ fold UPrecongr_step in H6.
         eexists; eexists; split;
         [apply WCtxThen, WCtxEta; eauto | constructor; apply MCP_CondEta; auto].
      ++ fold UPrecongr_step in H6.
         eexists; eexists; split;
         [apply WCtxElse, WCtxEta; eauto | constructor; apply MCP_CondEta; auto].
    * rewrite <- H7 in H1. clear H7 C' H4 C1.
      rewrite H6 in H; clear eta0 H6 H C C0 H3 n1 H2.
      inversion H1; clear H1.
      ++ inversion H.
         eexists; eexists; split;
         [do 3 constructor; eauto | constructor; apply MCP_RecEta; auto].
      ++ fold UPrecongr_step in H5.
         eexists; eexists; split;
         [apply WCtxRec, WCtxEta; eauto | constructor; apply MCP_RecEta; auto].
    * fold SPrecongr_step in H4.
      clear C3 H5 eta0 H0 C H3 n1 H2.
      elim (IHn2 _ _ _ _ H1 H4); intros.
      inversion_clear H. inversion_clear H0.
      eexists; eexists; split; [apply WCtxEta; eauto | constructor; eauto].
  - inversion H; clear H; [inversion H0; clear H0 | idtac | idtac].
    * rewrite <- H8 in H1.
      clear C0 C'0 H8 H9 C H6 C' H4 C1 H3 q0 H5 p0 H n1 H2.
      inversion H1.
      ++ inversion H.
      ++ fold UPrecongr_step in H4.
         eexists; eexists; split;
         [apply WCtxEta, WCtxThen; eauto | constructor; apply MCP_EtaCond; auto].
    * clear C' C0 H4 H9 s H7 r H C H5 C1 H3 n1 H2.
      rewrite <- H8 in H1; clear H8 C'0.
      inversion H1.
      ++ inversion H.
      ++ fold UPrecongr_step in H7.
         eexists; eexists; split;
         [do 2 apply WCtxThen; eauto | constructor; apply MCP_CondCond; auto].
      ++ fold UPrecongr_step in H7.
         eexists; eexists; split;
         [apply WCtxElse, WCtxThen; eauto | constructor; apply MCP_CondCond; auto].
    * rewrite <- H8 in H1.
      clear C0 H9 C'0 H8 q0 H7 p0 H6 C H C' H4 C1 H3 n1 H2.
      inversion H1.
      ++ inversion H.
         eexists; eexists; split;
         [do 3 constructor; eauto | constructor; apply MCP_RecCond; auto ].
      ++ fold UPrecongr_step in H5.
         eexists; eexists; split;
         [apply WCtxRec, WCtxThen; eauto | constructor; apply MCP_RecCond; auto].
    * clear C'' H6 C1 H7 q0 H5 p0 H0 C H3 n1 H2.
      fold SPrecongr_step in H4.
      elim (IHn2 _ _ _ _ H1 H4); intros.
      inversion_clear H. inversion_clear H0.
      rename x into n'. rename x0 into C1.
      eexists; eexists; split;
        [apply WCtxThen; eauto | constructor; auto].
    * clear C'' H6 C1 H7 q0 H5 p0 H0 C H3 n1 H2.
      fold SPrecongr_step in H4.
      eexists; eexists; split;
        [apply WCtxThen; eauto | constructor; auto].
  - inversion H; clear H; [inversion H0; clear H0 | idtac | idtac].
    * rewrite <- H9 in H1.
      clear C0 C'0 H8 H9 C H6 C' H4 C1 H3 q0 H5 p0 H n1 H2.
      inversion H1.
      ++ inversion H.
      ++ fold UPrecongr_step in H4.
         eexists; eexists; split;
         [apply WCtxEta, WCtxElse; eauto | constructor; apply MCP_EtaCond; auto].
    * rewrite <- H9 in H1.
      clear C' C0 H4 H9 s H7 r H C H5 C1 H3 n1 H2 C'0 H8.
      inversion H1.
      ++ inversion H.
      ++ fold UPrecongr_step in H7.
         eexists; eexists; split;
         [apply WCtxThen, WCtxElse; eauto | constructor; apply MCP_CondCond; auto].
      ++ fold UPrecongr_step in H7.
         eexists; eexists; split;
         [do 2 apply WCtxElse; eauto | constructor; apply MCP_CondCond; auto].
    * rewrite <- H9 in H1.
      clear C0 H9 C'0 H8 q0 H7 p0 H6 C H C' H4 C1 H3 n1 H2.
      inversion H1.
      ++ inversion H.
         eexists; eexists; split;
         [do 3 constructor; eauto | constructor; apply MCP_RecCond; auto ].
      ++ fold UPrecongr_step in H5.
         eexists; eexists; split;
         [apply WCtxRec, WCtxElse; eauto | constructor; apply MCP_RecCond; auto].
    * clear C'' H6 C1 H7 q0 H5 p0 H0 C H3 n1 H2.
      fold SPrecongr_step in H4.
      eexists; eexists; split;
        [apply WCtxElse; eauto | constructor; auto].
    * clear C'' H6 C1 H7 q0 H5 p0 H0 C H3 n1 H2.
      fold SPrecongr_step in H4.
      elim (IHn2 _ _ _ _ H1 H4); intros.
      inversion_clear H. inversion_clear H0.
      rename x into n'. rename x0 into C1.
      eexists; eexists; split;
        [apply WCtxElse; eauto | constructor; auto].
  - inversion H; clear H; [inversion H0; clear H0 | idtac ].
    * rewrite <- H8 in H1.
      clear C2 H8 CX H7 X0 H6 C H C' H4 C0 H3 n1 H2.
      inversion H1. inversion H.
      eexists; eexists; split;
        [apply WCtxEta, WCtxRec; eauto | constructor; apply MCP_EtaRec; auto].
    * rewrite <- H8 in H1.
      clear C2 H8 CX H7 X0 H6 C H C' H4 C0 H3 n1 H2.
      inversion H1. inversion H.
      ++ eexists; eexists; split;
           [apply WCtxThen, WCtxRec; eauto | constructor; apply MCP_CondRec; auto].
      ++ eexists; eexists; split;
           [apply WCtxElse, WCtxRec; eauto | constructor; apply MCP_CondRec; auto].
    * rewrite <- H6 in H1.
      clear C2 H6 CY H5 Y H C H7 C2 H4 C0 H3 n1 H2.
      rename X0 into Y, CX into CY, C1 into CX.
      inversion H1.
      ++ inversion H.
         eexists; eexists; split;
          [do 3 constructor; eauto | constructor; apply MCP_RecRec; auto].
      ++ inversion H.
         eexists; eexists; split;
          [do 2 apply WCtxRec; eauto | constructor; apply MCP_RecRec; auto].
    * elim (IHn2 _ _ _ _ H1 H4); intros.
      inversion_clear H. inversion_clear H7.
      eexists; eexists; split; try (constructor; eauto; fail).
Qed.

Lemma Precongr_sym_unfold_comm' : forall n1 n2 C C' C'', C$n1 ~<=>~ C' -> C'$n2 ~<u C'' ->
  exists n1' n2' C0, C$n2' ~<u C0 /\ C0$n1' ~<=>~ C''.
Proof.
assert (forall n1 k n2 C C' C'', k<n1 -> C$k ~<=>~ C' -> C'$n2 ~<u C'' ->
  exists n1' n2' C0, C$n2' ~<u C0 /\ C0$n1' ~<=>~ C''); eauto.
induction n1; intros; [inversion H | inversion H0].
+ eexists; eexists; exists C''; split; eauto; constructor.
+ clear C''0 H6 H5 H0.
  rewrite <- H4 in H; clear k H4; apply lt_S_n in H.
  assert (k0 < n1). apply le_lt_trans with (n + k0); auto with arith.
  elim (IHn1 _ _ _ _ _ H0 H3 H1); intros.
  destroy_as H4 H'.
  elim (Precongr_sym_unfold_comm _ _ _ _ _ H2 H5); intros.
  inversion_clear H6. inversion_clear H7.
  rename x1 into C1, x2 into m, x3 into C3.
  exists (S (n + x)), m, C3; split; auto.
  apply TStep with C1; auto.
Qed.

Lemma Precongr_sym_unfold_comm_trans : forall n1 n2 C C' C'', C$n1 ~<=>~ C' -> C'$n2 ~<=u C'' ->
  exists n1' n2' C0, C$n2' ~<=u C0 /\ C0$n1' ~<=>~ C''.
Proof.
assert (forall n2 k n1 C C' C'', k<n2 -> C$n1 ~<=>~ C' -> C'$k ~<=u C'' -> exists n1' n2' C0, C$n2' ~<=u C0 /\ C0$n1' ~<=>~ C''); eauto.
induction n2; intros; [inversion H | inversion H1]; intros.
+ rewrite <- H4; exists n1, 0, C; split; auto; constructor.
+ clear C''0 H6 C0 H5 H1.
  rewrite <- H4 in H; clear k H4; apply lt_S_n in H.
  assert (k0 < n2). apply le_lt_trans with (n+k0); auto with arith.
  fold UPrecongr in H3.
  elim (Precongr_sym_unfold_comm' _ _ _ _ _ H0 H2); intros.
  destroy_as H4 H'.
  clear H0 H2. rename x into n0; rename x1 into C0.
  elim (IHn2 _ _ _ _ _ H1 H4 H3); intros.
  destroy_as H0 H'.
  clear H1 H4 H3. rename x into n'; rename x2 into C1.
  exists n', (S (x0+x1)), C1; split; auto.
  apply TStep with C0; auto.
Qed.

(** Unfolding can be pushed before garbage collection. *)

Lemma Precongr_garbage_Unfolded_comm : forall n X CX C C' C'', C$n g>~ C' -> Unfolded X CX C' C'' ->
  exists C0, Unfolded X CX C C0 /\ C0$n g>~ C''.
Proof.
induction n; intros.
+ revert H0. inversion H. inversion H0.
  intro. inversion H5.
+ revert H0. inversion H; intro; inversion H4.
  - elim (IHn _ _ _ _ _ H1 H8); intros.
    inversion_clear H9. rename x into C4.
    exists (eta;C4); split; constructor; auto.
  - elim (IHn _ _ _ _ _ H1 H10); intros.
    inversion_clear H11. rename x into C4.
    exists (If p ? b Then C4 Else C0); split; constructor; auto.
  - exists (If p ? b Then C'0 Else C2); split; constructor; auto.
  - exists (If p ? b Then C2 Else C'0); split; constructor; auto.
  - elim (IHn _ _ _ _ _ H1 H10); intros.
    inversion_clear H11. rename x into C4.
    exists (If p ? b Then C0 Else C4); split; constructor; auto.
  - elim (IHn _ _ _ _ _ H1 H10); intros.
    inversion_clear H11. rename x into C4.
    exists (Def X0 == C1 In C4); split; constructor; auto.
Qed.

(* OBSOLETE - BUT TRUE :-)
Lemma Precongr_garbage_Unfolded_comm' : forall n X CX CX' C C', CX$n g>~ CX' -> Unfolded X CX' C C' ->
  exists n' C0, Unfolded X CX C C0 /\ C0$n' g>~ C'.
Proof.
intros. revert n X CX CX' C' H H0.
induction C; intros; inversion H0.
+ rewrite H2 in H0; rewrite <- H1; clear H2 X H0 H1 C'; rename r into X.
  exists n, CX; split; try constructor; auto.
+ elim (IHC _ _ _ _ _ H H4); intros.
  inversion_clear H5.
  rename x into n'; rename x0 into C0; inversion_clear H6.
  exists (S n'), (e; C0); split; try constructor; auto.
+ elim (IHC1 _ _ _ _ _ H H6); intros.
  inversion_clear H7.
  rename x into n'; rename x0 into C4; inversion_clear H8.
  exists (S n'), (If p == p0 Then C4 Else C2); split; try constructor; auto.
+ elim (IHC2 _ _ _ _ _ H H6); intros.
  inversion_clear H7.
  rename x into n'; rename x0 into C4; inversion_clear H8.
  exists (S n'), (If p == p0 Then C1 Else C4); split; try constructor; auto.
+ elim (IHC2 _ _ _ _ _ H H6); intros.
  inversion_clear H7.
  rename x into n'; rename x0 into C4; inversion_clear H8.
  exists (S n'), (Def r == C1 In C4); split; try constructor; auto.
Qed.
*)

Lemma Precongr_garbage_unfold_comm : forall n1 n2 C C' C'', C$n1 g>~ C' -> C'$n2 ~<u C'' ->
  exists C0, C$n2 ~<u C0 /\ C0$n1 g>~ C''.
Proof.
induction n1; [intros | induction n2]; intros.
+ inversion H. inversion H1.
  rewrite <- H5 in H0.
  clear C0 H3 C'0 H4 C' H5 C H2 H1 H.
  inversion H0. inversion H.
+ inversion H0. inversion H1.
  rewrite <- H5 in H, H0. rewrite <- H6 in H0.
  clear C'' H6 C' H5 C'0 H4 C0 H3 H1.
  inversion H.
  clear H7 C2' H6 C0 X0 H3 C H4 H n H1.
  elim (Precongr_garbage_Unfolded_comm _ _ _ _ _ _ H5 H2); intros.
  inversion_clear H. rename x into C0.
  exists (Def X == CX In C0); split; repeat constructor; auto.
+ revert H; inversion H0; intros; inversion H4.
  - clear C'' H3 C' H2 n H H0 C3 H9 eta0 H6 n0 H5 C H7 H4.
    elim (IHn1 _ _ _ _ H8 H1); intros.
    inversion_clear H. rename x into C3.
    exists (eta;C3); split; constructor; auto.
  - clear C1 H11 C''1 H10 q0 H9 p0 H6 C H7 H4 n0 H5 C' C'' H0 H2 H3 n H.
    elim (IHn1 _ _ _ _ H8 H1); intros.
    inversion_clear H. rename x into C3.
    exists (If p ? b Then C3 Else C0); split; constructor; auto.
  - exists (If p ? b Then C''0 Else C'1); split; try constructor; auto.
  - exists (If p ? b Then C'1 Else C''0); split; try constructor; auto.
  - clear C1 H11 C''1 H10 q0 H9 p0 H6 C H7 H4 n0 H5 C' C'' H0 H2 H3 n H.
    elim (IHn1 _ _ _ _ H8 H1); intros.
    inversion_clear H. rename x into C3.
    exists (If p ? b Then C0 Else C3); split; constructor; auto.
  - clear C2'0 H10 C0 H9 X0 H6 C H7 n0 H5 C'' C' H2 H3 H0 H4 n H.
    elim (IHn1 _ _ _ _ H8 H1); intros.
    inversion_clear H. rename x into C0.
    exists (Def X == C1 In C0); split; constructor; auto.
Qed.

Lemma Precongr_garbage_unfold_comm_trans : forall n1 n2 C C' C'', C$n1 g>=~ C' -> C'$n2 ~<=u C'' ->
  exists C0, C$n2 ~<=u C0 /\ C0$n1 g>=~ C''.
Proof.
intros.
eapply TransClose_comm; eauto.
apply Precongr_garbage_unfold_comm.
Qed.

End Weighted_Reductions.

End MCBase.
