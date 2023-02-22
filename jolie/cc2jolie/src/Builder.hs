module Builder where

import EPPUser (Var(..), Pid(..), RecVar(..), Label(..), Ann(..), Eta(..))
import Prelude hiding (seq)

import qualified EPPUser as EU

data Instruction e b
  = Interaction (Eta e) Ann
  | CCond Pid b [Instruction e b] [Instruction e b]
  | CCall RecVar

com :: Pid -> e -> Pid -> Var -> Instruction e b
com src ex dst v = Interaction (Com src ex dst v) (Ann "")

left :: Pid -> Pid -> Instruction e b
left src dst = Interaction (Sel src dst CLeft) (Ann "")

right :: Pid -> Pid -> Instruction e b
right src dst = Interaction (Sel src dst CRight) (Ann "")

ann :: String -> Instruction e b -> Instruction e b
ann str (Interaction e _) = Interaction e (Ann str)
ann _ _ = error "Cannot annotate anything other than an interaction"

cond :: Pid -> b -> ([Instruction e b], [Instruction e b]) -> Instruction e b
cond pid ex (c1, c2) = CCond pid ex c1 c2

call :: RecVar -> Instruction e b
call = CCall

chor :: [Instruction e b] -> EU.Choreography e b
chor [] = EU.CEnd
chor ((Interaction e a):is) = EU.Interaction e a $ chor is
chor ((CCond pid ex is1 is2):is)
  | null is = EU.CCond pid ex (chor is1) (chor is2)
  | otherwise = error "CCond must be in tail position"
chor ((CCall v):is)
  | null is = EU.CCall v
  | otherwise = error "CCall must be in tail position"

proc :: RecVar -> [Instruction e b] -> (RecVar, EU.Choreography e b)
proc v is = (v, chor is)

prog :: ([(RecVar, [Instruction e b])], [Instruction e b]) -> EU.CProgram e b
prog (defs, main) =
  EU.CProgram (EU.CDefSet [(v, chor is) | (v, is) <- defs], chor main)

pids :: [String] -> [Pid]
pids = map Pid

vars :: [String] -> [Var]
vars = map Var

recvars :: [String] -> [RecVar]
recvars = map RecVar
