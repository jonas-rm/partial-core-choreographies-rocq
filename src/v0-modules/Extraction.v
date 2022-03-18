Require Export Implementation.
Require Export EPP.

Require Extraction.

Module EPP_Extract := EPPBase  Nat Bool Nat CC_Expressions Bool_Expressions Nat CC_Eval CC_BEval.

Extraction Language Haskell.

Extraction "test2" EPPBase.

Extraction "test" EPP_Extract.epp.

Extraction Language OCaml.

Extraction "test" EPPBase.

Extraction "test2" EPP_Extract.epp.
