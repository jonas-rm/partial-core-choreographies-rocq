Require Import MC.
Require Import SP.

Local Open Scope nat_scope.

Module EPPBase (P X V E B R:DecType) (Ev:Eval E X V V) (BEv:Eval B X V Bool).

Module Import SPBase := SPBase P X V E B R Ev BEv.

(*
Module Export PSt := LState V X.
Module Export CSt := GState P V X.
*)

Section MaybeMove.
Definition Pid_In_dec := in_dec P.eq_dec.
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

(* Mmh we gotta discuss how to import SPBase with RecVars = RecVars * Pid *)

(* Definition epp (Defs:DefSet) (C:Choreography) (ps:list Pid) *)

(* Definition epp (Defs:DefSet) (C:Choreography) : option Network := epp_list Defs C (??). *)

End EPP.

Print within_ps.

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
      match f left, f' left with
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
induction B1, B2; intros; inversion H; auto.
+ simpl; trivial.
+ simpl.
  case_eq (Pid_dec p p0); case_eq (Expr_dec e e0); intros; rewrite H0 in H1; rewrite H2 in H1; simpl in H1; simpl; inversion H1.
Admitted.

Lemma more_branches_beh_char_2 : forall (B1 B2:Behaviour), more_branches_beh_direct B1 B2 -> more_branches_beh B1 B2.
Admitted.

Lemma more_branches_beh_char : forall (B1 B2:Behaviour), more_branches_beh B1 B2 <-> more_branches_beh_direct B1 B2.
Proof.
intros; split.
+ apply more_branches_beh_char_1.
+ apply more_branches_beh_char_2.
Qed.

(* Theorem EPP_Theorem : forall Defs C s, *)

End EPP_Properties.
