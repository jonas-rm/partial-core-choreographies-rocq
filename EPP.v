Require Import MC.
Require Import SP.

From Coq Require Import FunctionalExtensionality.

Local Open Scope nat_scope.

Module EPPBase (P X V E B R:DecType) (Ev:Eval E X V V) (BEv:Eval B X V Bool).

Module Import SPBase := SPBase P X V E B R Ev BEv.

(*
Module Export PSt := LState V X.
Module Export CSt := GState P V X.
*)

Section MaybeMove.

Definition Network_rm (N:Network) (p:Pid) :=
  fun r => if (Pid_dec r p) then End else N r.

Lemma Network_rm_add :
  forall N p, Network_eq (Network_rm N p | p [N p])%SP N.
Proof.
intros.
red. unfold Network_rm. unfold Process. unfold Par. intro.
case_eq (Pid_dec p0 p); intros.
+ rewrite Pdec.eqb_eq in H. rewrite H.
  elim (Behaviour_eq_End_dec bnil); auto.
  intro H'. contradiction.
+ elim (Behaviour_eq_End_dec (N p0)); auto.
Qed.

(* Generalisation of the above to lists of processes. *)

Definition Network_rm_ps (N:Network) (ps:list Pid) :=
  fun r => if (in_dec P.eq_dec r ps) then End else N r.

Definition Network_res_ps (N:Network) (ps:list Pid) :=
  fun r => if (in_dec P.eq_dec r ps) then N r else End.

Lemma Network_rm_res_ps :
  forall N ps, Network_eq (Network_rm_ps N ps | Network_res_ps N ps)%SP N.
Proof.
intros.
red. unfold Network_rm_ps. unfold Network_res_ps. unfold Par. intro.
case_eq (in_dec P.eq_dec p ps); intros.
+ elim (Behaviour_eq_End_dec bnil); auto.
  intro. contradiction.
+ elim (Behaviour_eq_End_dec (N p)); auto.
Qed.

Definition SPDefs_eq (Defs Defs':RecVar -> Behaviour) : Prop := forall X, Defs X = Defs' X.

Lemma Network_eq_corr :
  forall N1 N1' N2 SPDefs1 SPDefs2 s s' t,
    Network_eq N1 N2 ->
    SPDefs_eq SPDefs1 SPDefs2 ->
    SP_To SPDefs1 N1 s t N1' s' ->
    exists N2', SP_To SPDefs2 N2 s t N2' s' /\ Network_eq N1' N2'.
Proof.
intros.
inversion H1.
+ set (N2' := fun r => if Pid_dec p r then B else (if Pid_dec q r then B' else N2 r)).
  exists N2'.
  split.
  - apply (S_Com _ _ _ _ _ _ _ _ B B').
    * pose (H p) as H'. rewrite <- H'. assumption.
    * pose (H q) as H'. rewrite <- H'. assumption.
    * unfold N2'. rewrite Pdec.eqb_refl. reflexivity.
    * unfold N2'. rewrite Pdec.eqb_refl.
      case_eq (Pid_dec p q); auto.
      intro. rewrite Pdec.eqb_eq in H12.
      rewrite H12 in H4.
      rewrite <- H4. rewrite <- H5. reflexivity.
    * unfold N2'.
      red. intros.
      case_eq (Pid_dec p p0); case_eq (Pid_dec q p0); auto.
      ** intros.
         rewrite Pdec.eqb_eq in H14.
         rewrite H14 in H12.
         elim H12. constructor. reflexivity.
      ** intros.
         rewrite Pdec.eqb_eq in H14.
         rewrite H14 in H12.
         elim H12. constructor. reflexivity.
      ** intros.
         rewrite Pdec.eqb_eq in H13.
         rewrite H13 in H12.
         elim H12.
         apply in_cons. constructor. reflexivity.
  - red. intro.
    case_eq (Pid_dec p p0).
         
Admitted.

End MaybeMove.

Section EPP.

Fixpoint merge_beh (B1:Behaviour) (B2:Behaviour) : option Behaviour :=
match B1, B2 with
 | Send p e B, Send p' e' B' =>
    if Pid_dec p p' && Expr_dec e e' then
      match merge_beh B B' with
       | Some Bm => Some( Send p e Bm )
       | _ => None
      end
    else None
 | Recv p x B, Recv p' x' B' =>
    if Pid_dec p p' && Var_dec x x' then
      match merge_beh B B' with
       | Some Bm => Some( Recv p x Bm )
       | _ => None
      end
    else None
 | Sel p l B, Sel p' l' B' =>
    if Pid_dec p p' && eqb_label l l' then
      match (merge_beh B B') with
       | Some Bm => Some( Sel p l Bm )
       | _ => None
      end
    else None
 | Branching p f, Branching p' f' =>
    if Pid_dec p p' then
      match
        (* inl Some B = merging of a branching failed
           inl None = there were no branches to merge for that label in the first place, so all OK
           inr tt = merging error
        *)
        match f left, f' left with
        | Some B, Some B' => match merge_beh B B' with Some B'' => inl (Some B'') | None => inr tt end
        | Some B, None => inl (Some B)
        | None, Some B' => inl (Some B')
        | None, None => inl None
        end,
        match f right, f' right with
        | Some B, Some B' => match (merge_beh B B') with Some B'' => inl (Some B'') | None => inr tt end
        | Some B, None => inl (Some B)
        | None, Some B' => inl (Some B')
        | None, None => inl None
        end
      with
        | inl bl, inl br => Some (Branching p (fun l => match l with left => bl | right => br end))
        | _, _ => None
      end
    else None
 | Cond e B1 B2, Cond e' B1' B2' =>
    if BExpr_dec e e' then
      match (merge_beh B1 B1') with
       | Some B1m => match (merge_beh B2 B2') with | Some B2m => Some( Cond e B1m B2m ) | _ => None end
       | _ => None
      end
    else None
 | Call X, Call Y => if RecVar_dec X Y then Some (Call X) else None
 | End, End => Some End
 | _, _ => None
end.

Definition bproj_buildB (constructor:Behaviour -> Behaviour) (cont:option Behaviour) : option Behaviour :=
match cont with
| Some B => Some(constructor B)
| _ => None
end.

Definition bproj_buildbiB (biconstructor:Behaviour -> Behaviour -> Behaviour) (cont1:option Behaviour) (cont2:option Behaviour): option Behaviour :=
match cont1 with
| Some B1 => bproj_buildB (biconstructor B1) (cont2)
| _ => None
end.


(* DefSet is overkill, we might wanna just get RecVar -> list Pid *)
Fixpoint bproj (Defs:DefSet) (C:Choreography) (r:Pid) : option Behaviour :=
match C with
| MCBase.End => Some End
| (eta;;C')%MC => match eta with
            | (p # e --> q $ x)%MC => if (Pid_dec p r)
                                      then bproj_buildB (Send q e) (bproj Defs C' r)
                                      else (bproj_buildB (Recv p x) (bproj Defs C' r))
            | (p --> q [ l ])%MC => if (Pid_dec p r)
                                    then bproj_buildB (Sel q l) (bproj Defs C' r)
                                    else if (Pid_dec q r)
                                         then match (bproj Defs C' r) with
                                           | Some BC => Some (Branching p
                                                               (fun l' => match l, l' with
                                                                          | left,left => Some BC
                                                                          | right,right => Some BC
                                                                          | _,_ => None end))
                                           | None => None
                                           end
                                         else (bproj Defs C' r)
            end
| MCBase.Cond p b C1 C2 => if (Pid_dec p r)
                              then bproj_buildbiB (Cond b) (bproj Defs C1 r) (bproj Defs C2 r)
                              else match (bproj Defs C1 r), (bproj Defs C2 r) with
                                    | Some B1, Some B2 => (merge_beh B1 B2)
                                    | _, _ => None
                                   end
| MCBase.Call X => if In_dec P.eq_dec r (fst (Defs X)) then Some (Call X) else Some End
| MCBase.RT_Call X ps C' => if In_dec P.eq_dec r ps then Some (Call X) else bproj Defs C' r
end.

Definition epp_list (Defs:DefSet) (C:Choreography) (ps:list Pid) : list (Pid * option Behaviour) :=
  map (fun p => (p, bproj Defs C p)) ps.

Definition projectable Defs C ps := all_defined (map snd (epp_list Defs C ps)).

Fixpoint epp_net (Defs:DefSet) (C:Choreography) (ps:list Pid) :
  projectable Defs C ps -> Network.
Proof.
unfold projectable.
induction ps.
+ intro. apply EmptyNet.
+ simpl. case_eq (bproj Defs C a); intros.
  - intro p. apply (if (P.eq_dec a p) then b else (epp_net _ _ _ H0 p)).
  - inversion H0.
Defined.

(*
Fixpoint epp (Defs:DefSet) (Xs: list RecVar) (C:Choreography) (ps:list Pid) :
  (forall X, In X Xs -> projectable Defs (snd (Defs X)) (fst (Defs X))) ->
  projectable Defs C ps ->
  (RecVar -> Behaviour) * Network :=
fun projXs => fun projMain =>
(
  fun X => if false then projXs else ,
  epp_net Defs C ps projMain
).

Fixpoint epp_Program (P:MCBase.Program) (ps:list Pid) :
  projectable (MCBase.Procedures P) (Main P) ps -> SPBase.Program :=
fun x =>
  Build_Program
    (fun X => End)
    (EmptyNet)
.
*)

End EPP.

Section EPP_Properties.

Fixpoint more_branches_beh_direct (B1 B2:Behaviour) : Prop :=
match B1, B2 with
 | Send p e B, Send p' e' B' =>
    if (Pid_dec p p') && (Expr_dec e e') then more_branches_beh_direct B B' else False
 | Recv p x B, Recv p' x' B' =>
    if (Pid_dec p p') && (Var_dec x x') then more_branches_beh_direct B B' else False
 | Sel p l B, Sel p' l' B' =>
    if (Pid_dec p p') && (eqb_label l l') then more_branches_beh_direct B B' else False
 | Branching p f, Branching p' f' =>
    if (Pid_dec p p') then
      match f left, f' left with
       | Some B, Some B' => more_branches_beh_direct B B'
       | Some B, None => True
       | None, Some B' => False
       | None, None => True
      end
      /\
      match f right, f' right with
       | Some B, Some B' => more_branches_beh_direct B B'
       | Some B, None => True
       | None, Some B' => False
       | None, None => True
      end
    else False
 | Cond e B1 B2, Cond e' B1' B2' =>
    if (BExpr_dec e e') then more_branches_beh_direct B1 B1' /\ more_branches_beh_direct B2 B2' else False
 | Call X, Call Y => if (RecVar_dec X Y) then True else False
 | End, End => True
 | _, _ => False
end.

Definition more_branches_beh (B1 B2:Behaviour) := (merge_beh B1 B2) = Some B1.

Lemma more_branches_beh_char_1 : forall (B1 B2:Behaviour), more_branches_beh B1 B2 -> more_branches_beh_direct B1 B2.
induction B1 using Behaviour_ind_b; induction B2 using Behaviour_ind_b; try easy.
+ intro. inversion H. simpl.
  case_eq (Pid_dec p p0); case_eq (Expr_dec e e0); intros; rewrite H0 in H1; rewrite H2 in H1; simpl in H1; simpl; inversion H1.
  specialize (IHB1 B2).
  unfold more_branches_beh in IHB1.
  destruct (merge_beh B1 B2).
  - inversion H4.
    rewrite H5 in IHB1.
    auto.
  - inversion H4.
+ intro. inversion H. simpl.
  case_eq (Pid_dec p p0); case_eq (Var_dec v v0); intros; rewrite H0 in H1; rewrite H2 in H1; simpl in H1; simpl; inversion H1.
  specialize (IHB1 B2).
  unfold more_branches_beh in IHB1.
  destruct (merge_beh B1 B2).
  - inversion H4.
    rewrite H5 in IHB1.
    auto.
  - inversion H4.
+ intro. inversion H. simpl.
  case_eq (Pid_dec p p0); case_eq (eqb_label l l0); intros; rewrite H0 in H1; rewrite H2 in H1; simpl in H1; simpl; inversion H1.
  specialize (IHB1 B2).
  unfold more_branches_beh in IHB1.
  destruct (merge_beh B1 B2).
  - inversion H4.
    rewrite H5 in IHB1.
    auto.
  - inversion H4.
+ intro.
  red in H3. simpl in H3.
  case_eq (Pid_dec p p0).
  - intro.
    rewrite H4 in H3.
    case_eq (o left); case_eq (o0 left); case_eq (o right); case_eq (o0 right); intros; try easy.
    all: rewrite H5, H6, H7, H8 in H3.
    all: simpl; rewrite H4.
    all: try rewrite H5; try rewrite H6; try rewrite H7; try rewrite H8; split; auto.
    * assert (more_branches_beh b2 b1).
      2: apply (H _ H8 _ H9).
      red.
      case_eq (merge_beh b2 b1); case_eq (merge_beh b0 b); intros.
      all: try rewrite H9 in H3.
      all: try rewrite H10 in H3.
      all: try easy.
      inversion H3.
      assert (o left = Some b4). 2: { rewrite <- H11. apply H8. }
      rewrite <- H12; auto.
    * assert (more_branches_beh b0 b).
      2: apply (H0 _ H6 _ H9).
      red.
      case_eq (merge_beh b2 b1); case_eq (merge_beh b0 b); intros.
      all: try rewrite H9 in H3.
      all: try rewrite H10 in H3.
      all: try easy.
      inversion H3.
      assert (o right = Some b3). 2: { rewrite <- H11. apply H6. }
      rewrite <- H12; auto.
    * assert (more_branches_beh b1 b0).
      2: apply (H _ H8 _ H9).
      red.
      case_eq (merge_beh b1 b0); intros.
      all: try rewrite H9 in H3.
      all: try easy.
      inversion H3.
      assert (o left = Some b2). 2: { rewrite <- H10. apply H8. }
      rewrite <- H11; auto.
    * assert (more_branches_beh b1 b0).
      2: apply (H _ H8 _ H9).
      red.
      case_eq (merge_beh b1 b0); intros.
      all: try rewrite H9 in H3.
      all: try easy.
      inversion H3.
      assert (o left = Some b2). 2: { rewrite <- H10. apply H8. }
      rewrite <- H11; auto.
    * case_eq (merge_beh b1 b0); intros.
      ** rewrite H9 in H3.
         assert (o = (fun l : Label => match l with
                            | left => Some b1
                            | right => None
                            end)).
         2: {
           rewrite H10 in H3.
           inversion H3.
           assert (Some b = None).
           2: inversion H11.
           set (f := (fun l : Label => match l with
                        | left => Some b2
                        | right => Some b
                        end)) in H12.
           set (g := (fun l : Label => match l with
                        | left => Some b2
                        | right => None
                        end)) in H12.
           change ((f right) = (g right)).
           rewrite H12; auto.
         }
         apply functional_extensionality.
         intro.
         case x; auto.
      ** rewrite H9 in H3.
         inversion H3.
    * case_eq (merge_beh b0 b); intros.
      ** rewrite H9 in H3.
         assert (o = (fun l : Label => match l with
                            | left => Some b0
                            | right => None
                            end)).
         1: apply functional_extensionality; intro; case x; auto.
         rewrite H10 in H3.
         inversion H3. clear H3.
         set (f := (fun l : Label => match l with
                      | left => Some b1
                      | right => None
                      end)) in H12.
         set (g := (fun l : Label => match l with
                      | left => Some b0
                      | right => None
                      end)) in H12.
         assert (Some b0 = Some b1).
         1: { change ((g left) = (f left)). rewrite H12; auto. }
         inversion H3.
         rewrite <- H13.
         rewrite <- H13 in H9.
         assert (more_branches_beh b0 b).
         1: apply H9.
         apply (H _ H8 _ H11).
      ** rewrite H9 in H3.
         inversion H3.
    * case_eq (merge_beh b0 b); intros; rewrite H9 in H3.
      ** assert (o = (fun l : Label => match l with
                            | left => Some b1
                            | right => Some b0
                            end)).
         1: apply functional_extensionality; intro; case x; auto.
         rewrite H10 in H3.
         inversion H3. clear H3.
         set (f := (fun l : Label => match l with
                      | left => Some b1
                      | right => Some b2
                      end)) in H12.
         set (g := (fun l : Label => match l with
                      | left => Some b1
                      | right => Some b0
                      end)) in H12.
         assert (Some b2 = Some b0).
         1: { change ((f right) = (g right)). rewrite H12; auto. }
         inversion H3.
         rewrite <- H13 in H9.
         assert (more_branches_beh b2 b).
         1: apply H9.
         pose (Hright := H0 b2).
         rewrite <- H13.
         rewrite <- H13 in H6.
         apply (H0 _ H6 _ H11).
      ** inversion H3.
    * assert (o = (fun l : Label => match l with
                            | left => Some b0
                            | right => None
                            end)).
      1: apply functional_extensionality; intro; case x; auto.
      rewrite H9 in H3.
      set (f := (fun l : Label => match l with
                   | left => Some b0
                   | right => Some b
                   end)) in H3.
      set (g := (fun l : Label => match l with
                   | left => Some b0
                   | right => None
                   end)) in H3.
      assert (Some b = None).
      2: inversion H10.
      change ((f right) = (g right)).
      inversion H3; auto.
    * case_eq (merge_beh b0 b); intros; rewrite H9 in H3.
      2: inversion H3.
      assert (o = (fun l : Label => match l with
                          | left => None
                          | right => Some b0
                          end)).
      1: apply functional_extensionality; intro; case x; auto.
      rewrite H10 in H3.
      set (f := (fun l : Label => match l with
                   | left => Some b1
                   | right => Some b2
                   end)) in H3.
      set (g := (fun l : Label => match l with
                   | left => None
                   | right => Some b0
                   end)) in H3.
      inversion H3.
      assert (Some b1 = None).
      2: inversion H11.
      change ((f left) = (g left)).
      inversion H3; auto.
    * case_eq (merge_beh b0 b); intros; rewrite H9 in H3.
      2: inversion H3.
      assert (o = (fun l : Label => match l with
                          | left => None
                          | right => Some b0
                          end)).
      1: apply functional_extensionality; intro; case x; auto.
      rewrite H10 in H3.
      set (f := (fun l : Label => match l with
                   | left => Some b1
                   | right => Some b2
                   end)) in H3.
      set (g := (fun l : Label => match l with
                   | left => None
                   | right => Some b0
                   end)) in H3.
      inversion H3.
      assert (Some b1 = None).
      2: inversion H11.
      change ((f left) = (g left)).
      inversion H3; auto.
    * assert (o = (fun l : Label => match l with
                          | left => None
                          | right => Some b
                          end)).
      1: apply functional_extensionality; intro; case x; auto.
      rewrite H9 in H3.
      set (f := (fun l : Label => match l with
                   | left => Some b0
                   | right => Some b
                   end)) in H3.
      set (g := (fun l : Label => match l with
                   | left => None
                   | right => Some b
                   end)) in H3.
      inversion H3.
      assert (Some b0 = None).
      2: inversion H10.
      change ((f left) = (g left)).
      inversion H3; auto.
    * assert (o = (fun l : Label => match l with
                        | left => None
                        | right => None
                        end)).
      1: apply functional_extensionality; intro; case x; auto.
      rewrite H9 in H3.
      set (f := (fun l : Label => match l with
                   | left => Some b0
                   | right => Some b
                   end)) in H3.
      set (g := (fun l : Label => match l with
                   | left => None
                   | right => None
                   end)) in H3.
      inversion H3.
      assert (Some b0 = None).
      2: inversion H10.
      change ((f left) = (g left)).
      inversion H3; auto.
    * assert (o = (fun l : Label => match l with
                        | left => None
                        | right => None
                        end)).
      1: apply functional_extensionality; intro; case x; auto.
      rewrite H9 in H3.
      set (f := (fun l : Label => match l with
                   | left => Some b0
                   | right => Some b
                   end)) in H3.
      set (g := (fun l : Label => match l with
                   | left => None
                   | right => None
                   end)) in H3.
      inversion H3.
      assert (Some b0 = None).
      2: inversion H10.
      change ((f left) = (g left)).
      inversion H3; auto.
    * assert (o = (fun l : Label => match l with
                        | left => None
                        | right => None
                        end)).
      1: apply functional_extensionality; intro; case x; auto.
      rewrite H9 in H3.
      set (f := (fun l : Label => match l with
                   | left => Some b
                   | right => None
                   end)) in H3.
      set (g := (fun l : Label => match l with
                   | left => None
                   | right => None
                   end)) in H3.
      inversion H3.
      assert (Some b = None).
      2: inversion H10.
      change ((f left) = (g left)).
      inversion H3; auto.
    * case_eq (merge_beh b0 b); intros; rewrite H9 in H3.
      2: inversion H3.
      assert (o = (fun l : Label => match l with
                          | left => None
                          | right => Some b0
                          end)).
      1: apply functional_extensionality; intro; case x; auto.
      rewrite H10 in H3.
      set (f := (fun l : Label => match l with
                   | left => None
                   | right => Some b1
                   end)) in H3.
      set (g := (fun l : Label => match l with
                   | left => None
                   | right => Some b0
                   end)) in H3.
      inversion H3.
      assert (Some b1 = Some b0).
      1: { change ((f right) = (g right)). rewrite H12; auto. }
      inversion H11.
      rewrite H14 in H9.
      assert (more_branches_beh b0 b).
      1: apply H9.
      rewrite <- H14.
      rewrite <- H14 in H6.
      apply (H0 _ H6).
      rewrite H14; trivial.
    * assert (o = (fun l : Label => match l with
                        | left => None
                        | right => None
                        end)).
      1: apply functional_extensionality; intro; case x; auto.
      rewrite H9 in H3.
      set (f := (fun l : Label => match l with
                   | left => None
                   | right => Some b
                   end)) in H3.
      set (g := (fun l : Label => match l with
                   | left => None
                   | right => None
                   end)) in H3.
      inversion H3.
      assert (Some b = None).
      2: inversion H10.
      change ((f right) = (g right)).
      inversion H3; auto.
  - intro.
    rewrite H4 in H3.
    inversion H3.
+ intros.
  simpl.
  red in H.
  simpl in H.
  case_eq (BExpr_dec b b0); intros.
  1: split.
  - rewrite H0 in H.
    apply IHB1_1.
    red.
    case_eq (merge_beh B1_1 B2_1); intros; rewrite H1 in H.
    2: inversion H.
    case_eq (merge_beh B1_2 B2_2); intros; rewrite H2 in H.
    2: inversion H.
    inversion H; auto.
  - rewrite H0 in H.
    apply IHB1_2.
    red.
    case_eq (merge_beh B1_1 B2_1); intros; rewrite H1 in H.
    2: inversion H.
    case_eq (merge_beh B1_2 B2_2); intros; rewrite H2 in H.
    2: inversion H.
    inversion H; auto.
  - rewrite H0 in H.
    inversion H.
+ intros.
  inversion H.
  simpl.
  case_eq (RecVar_dec r r0); intros; auto.
  rewrite H0 in H1.
  inversion H1.
Qed.

Lemma more_branches_beh_char_2 : forall (B1 B2:Behaviour), more_branches_beh_direct B1 B2 -> more_branches_beh B1 B2.
induction B1 using Behaviour_ind_b; induction B2 using Behaviour_ind_b; try easy.
+ intro. red. simpl. simpl in H.
  case_eq (Pid_dec p p0); case_eq (Expr_dec e e0);
  simpl;
  intros; rewrite H0, H1 in H; simpl in H; try easy.
  pose (Hm := IHB1 B2 H).
  inversion Hm.
  rewrite H3; auto.
+ intro. red. simpl. simpl in H.
  case_eq (Pid_dec p p0); case_eq (Var_dec v v0);
  simpl;
  intros; rewrite H0, H1 in H; simpl in H; try easy.
  pose (Hm := IHB1 B2 H).
  inversion Hm.
  rewrite H3; auto.
+ intro. red. simpl. simpl in H.
  case_eq (Pid_dec p p0); case_eq (eqb_label l l0);
  simpl;
  intros; rewrite H0, H1 in H; simpl in H; try easy.
  pose (Hm := IHB1 B2 H).
  inversion Hm.
  rewrite H3; auto.
+ intro. red. simpl. simpl in H3.
  case_eq (Pid_dec p p0).
  - intro.
    rewrite H4 in H3.
    inversion_clear H3.
    case_eq (o left); case_eq (o0 left); case_eq (o right); case_eq (o0 right); intros.
    all: rewrite H9, H8 in H5.
    all: rewrite H7, H3 in H6.
    all: try easy.
    * pose (Hleft := H _ H9 _ H5).
      inversion Hleft.
      rewrite H11.
      pose (Hright := H0 _ H7 b H6).
      inversion Hright.
      rewrite H12.
      assert (o = (fun l : Label => match l with
                            | left => Some b2
                            | right => Some b0
                            end)).
      2: rewrite H10; auto. apply functional_extensionality. intro. case x; auto.
    * pose (Hleft := H _ H9 _ H5).
      inversion Hleft.
      rewrite H11.
      assert (o = (fun l : Label => match l with
                            | left => Some b1
                            | right => Some b
                            end)).
      2: rewrite H10; auto. apply functional_extensionality. intro. case x; auto.
    * pose (Hleft := H _ H9 _ H5).
      inversion Hleft.
      rewrite H11.
      assert (o = (fun l : Label => match l with
                            | left => Some b0
                            | right => None
                            end)).
      2: rewrite H10; auto. apply functional_extensionality. intro. case x; auto.
    * pose (Hright := H0 _ H7 b H6).
      inversion Hright.
      rewrite H11.
      assert (o = (fun l : Label => match l with
                            | left => Some b1
                            | right => Some b0
                            end)).
      2: rewrite H10; auto. apply functional_extensionality. intro. case x; auto.
    * assert (o = (fun l : Label => match l with
                            | left => Some b0
                            | right => Some b
                            end)).
      2: rewrite H10; auto. apply functional_extensionality. intro. case x; auto.
    * assert (o = (fun l : Label => match l with
                            | left => Some b
                            | right => None
                            end)).
      2: rewrite H10; auto. apply functional_extensionality. intro. case x; auto.
    * pose (Hright := H0 _ H7 b H6).
      inversion Hright.
      rewrite H11.
      assert (o = (fun l : Label => match l with
                            | left => None
                            | right => Some b0
                            end)).
      2: rewrite H10; auto. apply functional_extensionality. intro. case x; auto.
    * assert (o = (fun l : Label => match l with
                            | left => None
                            | right => Some b
                            end)).
      2: rewrite H10; auto. apply functional_extensionality. intro. case x; auto.
    * assert (o = (fun l : Label => match l with
                            | left => None
                            | right => None
                            end)).
      2: rewrite H10; auto. apply functional_extensionality. intro. case x; auto.
  - intro.
    rewrite H4 in H3.
    exfalso; auto.
+ intro. red. simpl. simpl in H.
  case_eq (BExpr_dec b b0).
  - intro.
    rewrite H0 in H. inversion_clear H.
    pose (Hm := IHB1_1 B2_1 H1).
    inversion Hm.
    rewrite H3.
    pose (Hm2 := IHB1_2 B2_2 H2).
    inversion Hm2.
    rewrite H4; auto.
  - intro.
    rewrite H0 in H.
    exfalso; auto.
+ intro. red. simpl. simpl in H.
  case_eq (RecVar_dec r r0);
  simpl;
  intros; rewrite H0 in H; simpl in H; easy.
Qed.

Lemma more_branches_beh_char : forall (B1 B2:Behaviour), more_branches_beh B1 B2 <-> more_branches_beh_direct B1 B2.
Proof.
intros; split.
+ apply more_branches_beh_char_1.
+ apply more_branches_beh_char_2.
Qed.

Definition more_branches_net (N N':Network) (ps:list Pid) :=
  forall p, In p ps -> more_branches_beh (N p) (N' p).

Definition more_branches_defs (SPDefs SPDefs' : RecVar -> Behaviour) :=
  forall X, more_branches_beh (SPDefs X) (SPDefs' X).

Inductive MoreBranches : Behaviour -> Behaviour -> Prop :=
| MB_Send p e B B' :
  MoreBranches B B' ->
  MoreBranches (p ! e ; B)%SP (p ! e ; B')%SP
| MB_Recv p x B B' :
  MoreBranches B B' ->
  MoreBranches (p ? x ; B)%SP (p ? x ; B')%SP
| MB_Sel p l B B' :
  MoreBranches B B' ->
  MoreBranches (p (+) l; B)%SP (p (+) l; B')%SP
| MB_Branching p o o' :
  (forall Bleft', o' left = Some Bleft' -> exists Bleft, o left = Some Bleft /\
    MoreBranches Bleft Bleft') ->
  (forall Bright', o' right = Some Bright' -> exists Bright, o right = Some Bright /\
    MoreBranches Bright Bright') ->
  MoreBranches (p & o) (p & o')
| MB_Cond b B1 B2 B1' B2' :
  MoreBranches B1 B1' -> MoreBranches B2 B2' ->
  MoreBranches
    (If b Then B1 Else B2)%SP (If b Then B1' Else B2')%SP
| MB_Call X : MoreBranches (Call X)%SP (Call X)%SP
| MB_End : MoreBranches bnil%SP bnil%SP.

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
