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

Fixpoint pproj (C:MCBase.Choreography) (r:Pid) : option Behaviour :=
match C with
| MCBase.End => (Some End)
| _ => (Some End)
end.

End EPP.

Section EPP_Properties.
End EPP_Properties.