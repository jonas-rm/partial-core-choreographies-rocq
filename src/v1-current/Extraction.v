Require Export Implementation.
Require Export EPP.
Require Extraction.

Definition sig := Build_Signature CC_Nat Bool CC_Nat CC_Expressions Bool_Expressions CC_Nat Unit CC_Eval CC_BEval.
Definition epp' := @EPP.epp sig.

(* Extraction Inline Signature. *)
(* Extraction Inline Network. *)
(* Extraction Inline pid. *)
(* Extraction Inline var. *)
(* Extraction Inline value. *)
(* Extraction Inline expr. *)
(* Extraction Inline bexpr. *)
(* Extraction Inline recvar. *)
(* Extraction Inline ann. *)
(* Extraction Inline ev. *)
(* Extraction Inline bev. *)
(* Extraction Inline bproj_dec. *)
(* Extraction Inline epp_C. *)
(* Extraction Inline epp_D. *)
(* Extraction Inline epp. *)
(* Extraction Inline sig. *)
(* Extraction Inline merge_dec. *)

Extraction Language Haskell.
Extraction "EPP" epp'.

Extraction Language Scheme.
Extraction "EPP" epp'.

Extraction Language OCaml.
Extraction "EPP" epp'.
