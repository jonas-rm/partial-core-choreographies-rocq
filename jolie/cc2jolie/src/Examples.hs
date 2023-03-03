{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module Examples where

import Data.Maybe (fromJust)

import Builder ( com, left, right, cond
               , call, prog, pids, vars, recvars, ann )
import EPPUser
import Jolie
import Lambda

-- Util

exprs :: [String] -> [JolieExpr]
exprs = map JolieExpr

bexprs :: [String] -> [JolieBExpr]
bexprs = map $ JolieBExpr . JolieExpr

-- Lambda Calculus Example

plus :: Val -> Val -> Val
plus (IntVal x) (IntVal y) = IntVal $ x + y
plus _ _ = error "Cannot add non-integer values"

lambda :: Expr
lambda = (Apply
          (Apply
           (Lambda (Var "x")
            (Lambda (Var "y")
             (Foreign plus (Ref (Var "x")) (Ref (Var "y")))))
           (Lit (IntVal 5)))
          (Lit (IntVal 10)))

-- DistAuth Example

auth :: CProgram Expr BExpr
auth = prog
  ( []
  , [ com c credentials' ip credentials
    , cond ip check
      ( [ ann "ann1" $ left ip s
        , left ip c
        , com s token' c token ]
      , [ ann "ann2" $ right ip s
        , right ip c ] ) ] )
  where
    [ip, s, c] = pids ["Ip", "Server", "Client"]
    [credentials, token] = vars ["credentials", "token"]
    [credentials', token'] = [Ref credentials, Ref token]
    [check] = [BExpr $ credentials']

authc :: Choreography Expr BExpr
authc = let CProgram (_, c) = auth in c

authb :: BProgram Expr BExpr
authb = fromJust $ epp auth

authn :: Network Expr BExpr
authn = let BProgram (_, n) = authb in n

-- Jolie DistAuth Example

jolie :: CProgram JolieExpr JolieBExpr
jolie = prog
  ( []
  , [ com c "credentials" ip credentials
    , cond ip "check@Util( credentials )"
      ( [ ann "ann1" $ left ip s
        , ann "ann2" $ left ip c
        , com s "makeToken@Util()" c token ]
      , [ right ip s
        , right ip c ] ) ] )
  where
    [ip, s, c] = pids ["Ip", "Server", "Client"]
    [credentials, token] = vars ["credentials", "token"]

joliec :: Choreography JolieExpr JolieBExpr
joliec = let CProgram (_, c) = jolie in c

jolieb :: BProgram JolieExpr JolieBExpr
jolieb = fromJust $ epp jolie

jolien :: Network JolieExpr JolieBExpr
jolien = let BProgram (_, n) = jolieb in n

-- Jolie DistAuth RecVar Example

jolierec :: CProgram JolieExpr JolieBExpr
jolierec = prog
  ( [ (x, [ com c "credentials" ip credentials
          , cond ip "check@Util( credentials )"
            ( [ ann "ann1" $ left ip s
              , ann "ann2" $ left ip c
              , com s "makeToken@Util()" c token
              , call x ]
            , [ right ip s
              , right ip c
              , call x ] ) ] ) ]
  , [ call x ] )
  where
    [ip, s, c] = pids ["Ip", "Server", "Client"]
    [credentials, token] = vars ["credentials", "token"]
    [x] = recvars ["X"]

jolierecc :: Choreography JolieExpr JolieBExpr
jolierecc = let CProgram (_, c) = jolierec in c

jolierecb :: BProgram JolieExpr JolieBExpr
jolierecb = fromJust $ epp jolierec

jolierecn :: Network JolieExpr JolieBExpr
jolierecn = let BProgram (_, n) = jolierecb in n
