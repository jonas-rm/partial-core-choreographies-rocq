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
Definition Pid_In_dec := in_dec P.eq_dec.

(*
Definition option_apply_or_True (f:Behaviour -> Type) (o:option Behaviour) : Type :=
match o with
| Some B => f B
| _ => True
end.
*)

Fixpoint depth (B:Behaviour) : nat :=
match B with
 | Send p e B' => 1 + depth B'
 | Recv p x B' => 1 + depth B'
 | Sel p l B' => 1 + depth B'
 | Branching p f => 1 +
    match f left, f right with
     | Some B1, Some B2 => Nat.max (depth B1) (depth B2)
     | Some B1, None => depth B1
     | None, Some B2 => depth B2
     | None, None => 0
    end
 | Cond e B1 B2 => 1 + Nat.max (depth B1) (depth B2)
 | Call X => 1
 | End => 1
end.

(*
Definition option_apply_or_True (f:Behaviour -> Prop) (o:option Behaviour) : Prop :=
  forall B, o = Some B -> f B
  /\
  o = None -> True.
*)

Theorem Behaviour_ind_b :
  forall P : Behaviour -> Prop,
    P bnil%SP ->
    (forall (p : Pid) (e : Expr) (b : Behaviour), P b -> P (p ! e; b)%SP) ->
    (forall (p : Pid) (v : Var) (b : Behaviour), P b -> P (p ? v; b)%SP) ->
    (forall (p : Pid) (l : Label) (b : Behaviour), P b -> P (p (+) l; b)%SP) ->
    (forall (p : Pid) (o : Label -> option Behaviour),
      (forall (b0 : Behaviour), (o left) = Some b0 -> P b0) ->
      (forall (b1 : Behaviour), (o right) = Some b1 -> P b1) ->
      P (p & o)%SP
    ) ->
    (forall (b : BExpr) (b0 : Behaviour),
    P b0 -> forall b1 : Behaviour, P b1 -> P (If b Then b0 Else b1)%SP) ->
    (forall r : RecVar, P (Call r)) -> forall b : Behaviour, P b.
Proof.
intros.
revert b.
assert (forall d b, depth b <= d -> P b).
2: eauto.
induction d; intros; case_eq b; intros; auto; rewrite H7 in H6; try (exfalso; inversion H6; fail).
+ apply H0. apply IHd. simpl in H. auto with arith.
+ apply H1. apply IHd. simpl in H. auto with arith.
+ apply H2. apply IHd. simpl in H. auto with arith.
+ apply H3.
  (* left branch *)
  - inversion H6.
    * intros.
      rewrite H8 in H9.
      case_eq (o right); intros; rewrite H10 in H9; apply IHd; rewrite <- H9.
      ** apply Nat.le_max_l.
      ** auto with arith.
    * intros.
      apply IHd.
      simpl in H9.
      rewrite H10 in H9.
      case_eq (o right); intros.
      ** rewrite H11 in H9. etransitivity. eapply Nat.le_max_l. eauto with arith.
      ** rewrite H11 in H9. inversion H9; auto with arith.
  - inversion H6.
    * intros.
      rewrite H8 in H9.
      case_eq (o left); intros; rewrite H10 in H9; apply IHd; rewrite <- H9; auto with arith.
      apply Nat.le_max_r.
    * intros.
      apply IHd.
      simpl in H9.
      rewrite H10 in H9.
      case_eq (o left); intros.
      ** rewrite H11 in H9. etransitivity. eapply Nat.le_max_r. eauto with arith.
      ** rewrite H11 in H9. inversion H9; auto with arith.
+ apply H4; apply IHd; simpl in H; apply le_S_n in H6.
  - etransitivity. eapply Nat.le_max_l. eauto.
  - etransitivity. eapply Nat.le_max_r. eauto.
Qed.

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
| MCBase.Call X => if Pid_In_dec r (fst (Defs X)) then Some (Call X) else Some End
| MCBase.RT_Call X ps C' => if Pid_In_dec r ps then Some (Call X) else bproj Defs C' r
end.

Fixpoint epp_list (Defs:DefSet) (C:Choreography) (ps:list Pid) : option Network :=
match ps with
| nil => Some nnil%SP
| p::qs => match epp_list Defs C qs with
            | Some N => match bproj Defs C p with
                         | Some B => Some (p[B] | N)%SP
                         | None => None
                        end
            | None => None
           end
end.

(* Definition epp (Defs:DefSet) (C:Choreography) (ps:list Pid) *)

(* Definition epp (Defs:DefSet) (C:Choreography) : option Network := epp_list Defs C (??). *)

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

Lemma more_branches_completeness :
  forall N1 N1' N2 N2' ps SPDefs1 SPDefs2 s s' t,
    within_ps ps N1 -> within_ps ps N2 ->
    more_branches_net N1 N2 ps ->
    more_branches_defs SPDefs1 SPDefs2 ->
    SP_To SPDefs1 N1 s t N1' s' ->
    SP_To SPDefs2 N2 s t N2' s' /\ more_branches_net N1' N2' ps.
Proof.
intros.
red in H, H0, H1, H2.
inversion H3.
+ red in H8.
  split.
  - elim (In_dec P.eq_dec p ps); intro.
    2: { pose (Hp := H p b). rewrite Hp in H4. inversion H4. }
    pose (Hp := H1 p a).
    inversion Hp. clear Hp.
    rewrite H4 in H15.
    inversion H15. clear H15.
    case_eq (N2 p); intros; try rewrite H14 in H16; inversion H16.
    clear H17.
    case_eq (Pid_dec q p0); case_eq (Expr_dec e e0); intros; rewrite H15, H17 in H16; simpl in H16; try inversion H16.
    clear H19.
    case_eq (merge_beh B b); intros.
    * rewrite H18 in H16.
      inversion H16.
Admitted.

(*
Theorem EPP_Theorem : forall c l c', MCP_To c l c' -> SP_To
*)
End EPP_Properties.

End EPPBase.