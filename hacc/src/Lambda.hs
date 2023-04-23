{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module Lambda where

import Control.DeepSeq (NFData)
import GHC.Generics (Generic)

import qualified Data.List as L

import EPPUser

newtype Env = Env [(Var, Val)] deriving (Show, Generic, NFData)

empty :: Env
empty = Env []

bind :: Env -> Var -> Val -> Env
bind (Env e) v x = Env $ (v, x):e

ref :: Env -> Var -> Val
ref (Env e) v = case L.lookup v e of
  Just x -> x
  Nothing -> error $ "Variable doesn't exist: " ++ show v

data Val
  = BoolVal Bool
  | IntVal Int
  | StringVal String
  | FunVal Env Var Expr
  | ForeignFunVal (Val -> Val)
  deriving (Generic, NFData)

instance Show Val where
  show (BoolVal x) = show x
  show (IntVal x) = show x
  show (StringVal x) = show x
  show (FunVal _ _ _) = "#<FunVal>"
  show (ForeignFunVal _) = "#<ForeignFunVal>"

instance Eq Val where
  (==) (BoolVal x1) (BoolVal x2) = x1 == x2
  (==) (IntVal x1) (IntVal x2) = x1 == x2
  (==) (StringVal x1) (StringVal x2) = x1 == x2
  (==) _ _ = False

data Expr
  = Lit Val
  | Ref Var
  | Lambda Var Expr
  | ForeignLambda (Val -> Val)
  | Apply Expr Expr
  deriving (Generic, NFData)

instance Show Expr where
  show (Lit x) = "Lit (" ++ show x ++ ")"
  show (Ref v) = "Ref (" ++ show v ++ ")"
  show (Lambda v b) = "Lambda (" ++ show v ++ ") (" ++ show b ++ ")"
  show (ForeignLambda _) = "ForeignLambda"
  show (Apply f x) = "Apply (" ++ show f ++ ") (" ++ show x ++ ")"

instance Eq Expr where
  (==) (Lit x1) (Lit x2) = x1 == x2
  (==) (Ref x1) (Ref x2) = x1 == x2
  (==) (Lambda v1 b1) (Lambda v2 b2) = v1 == v2 && b1 == b2
  (==) (Apply f1 x1) (Apply f2 x2) = f1 == f2 && x1 == x2
  (==) _ _ = False

eval :: Env -> Expr -> Val
eval _ (Lit x) = x
eval e (Ref v) = ref e v
eval e (Lambda v b) = FunVal e v b
eval _ (ForeignLambda f) = ForeignFunVal f
eval e (Apply f x) = let r = eval e f in case r of
  FunVal e' v b -> eval (bind e' v $ eval e x) b
  ForeignFunVal f' -> f' (eval e x)
  _ -> error $ "Cannot apply a non-function: " ++ show r

newtype BExpr = BExpr Expr deriving (Show, Eq, Generic, NFData)

beval :: Env -> BExpr -> Bool
beval e (BExpr ex) = let r = eval e ex in case r of
  BoolVal b -> b
  _ -> error $ "Expression did not evaluate to a boolean: " ++ show r

-- Pretty-printing

instance PPrint Expr where
  format (Lit x) = show x
  format (Ref (Var v)) = v
  format (Lambda (Var v) b) = "\\" ++ v ++ " -> " ++ format b
  format (ForeignLambda _) = "ForeignLambda"
  format (Apply f x) = "(" ++ format f ++ ") (" ++ format x ++ ")"

instance PPrint BExpr where
  format (BExpr ex) = format ex
