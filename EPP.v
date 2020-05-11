Require Import MC.
Require Import SP.

Module EPPBase (P X V E B R:DecType) (Ev:Eval E X V V) (BEv:Eval B X V Bool).

Module Import MCBase := MCBase P X V E B R Ev BEv.
Module Import SPBase := SPBase P X V E B R Ev BEv.

(*
Module Export PSt := LState V X.
Module Export CSt := GState P V X.
*)

Section EPP.

Print Pid_dec.

Print Expr_dec.

Fixpoint merge (B1:Behaviour) (B2:Behaviour) : option Behaviour :=
match B1, B2 with
 | Send p e B, Send p' e' B' =>
    if (Pid_dec p p') && (Expr_dec e e') then
      match (merge B B') with
       | Some Bm => Some( Send p e Bm )
       | _ => None
      end
    else None
 | Recv p x B, Recv p' x' B' =>
    if (Pid_dec p p') then
      if (Var_dec x x') then
        match (merge B B') with
         | Some Bm => Some( Recv p x Bm )
         | _ => None
        end
      else None
    else None
 | Sel p l B, Sel p' l' B' =>
    if (Pid_dec p p') && (eqb_label l l') then
      match (merge B B') with
       | Some Bm => Some( Sel p l Bm )
       | _ => None
      end
    else None
 | Branching p f, Branching p' f' =>
    if (Pid_dec p p') then
      match
        match (f left, f' left) with
        | (inl B, inl B') => match (merge B B') with Some B'' => Some (inl B'') | None => None end
        | (inl B, inr _) => Some (inl B)
        | (inr _, inl B') => Some (inl B')
        | (inr _, inr _) => Some (inr tt)
        end,
        match (f right, f' right) with
        | (inl B, inl B') => match (merge B B') with Some B'' => Some (inl B'') | None => None end
        | (inl B, inr _) => Some (inl B)
        | (inr _, inl B') => Some (inl B')
        | (inr _, inr _) => Some (inr tt)
        end
      with
        | Some bl, Some br => Some (Branching p (fun l => match l with left => bl | right => br end))
        | _, _ => None
      end
      (*
      match merge_branch (f left, f' left), merge_branch (f right, f' right) with
        | Some bl, Some br => Some (Branching p (fun l => match l with left => bl | right => br end))
        | _, _ => None
      end
      *)
      (* match merge_branches f f' with Some f'' => Some (Branching p f'') | None => None end *)
    else None
 | Cond p B1 B2, Cond p' B1' B2' =>
    if (Pid_dec p p') then
      match (merge B1 B1') with
       | Some B1m => match (merge B2 B2') with | Some B2m => Some( Cond p B1m B2m ) | _ => None end
       | _ => None
      end
    else None
 | End, End => Some End
 | _, _ => None
end.


Fixpoint pproj (C:MCBase.Choreography) (r:Pid) : option Behaviour :=
match C with
| MCBase.End => (Some End)
| _ => (Some End)
end.

End EPP.

Section EPP_Properties.
End EPP_Properties.