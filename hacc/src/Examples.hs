{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module Examples where

import Data.Maybe (fromJust)

import Builder ( com, left, right, cond
               , call, prog, pids, vars, recvars, ann )
import EPPUser
import Jolie
import Lambda

-- Lambda Calculus Example

plus :: Val -> Val
plus x = ForeignFunVal $ \y -> case (x, y) of
                                 (IntVal x', IntVal y') -> IntVal $ x' + y'
                                 _ -> error "Cannot add non-integer values"

lambda :: Expr
lambda = (Apply (Apply (ForeignLambda plus) (Lit (IntVal 5))) (Lit (IntVal 10)))

-- DistAuth Example

auth :: CProgram String String
auth = prog
  ( []
  , [ ann "authenticate" $ com c "credentials" ip credentials
    , cond ip "check(credentials)"
      ( [ ann "authOk" $ left ip s
        , ann "authOk" $ left ip c
        , ann "acceptToken" $ com s "makeToken" c token ]
      , [ ann "authFail" $ right ip s
        , ann "authFail" $ right ip c ] ) ] )
  where
    [ip, s, c] = pids ["Ip", "Server", "Client"]
    [credentials, token] = vars ["credentials", "token"]

authc :: Choreography String String
authc = let CProgram (_, c) = auth in c

authb :: BProgram String String
authb = fromJust $ epp auth

authn :: Network String String
authn = let BProgram (_, n) = authb in n

-- Lambda DistAuth Example

auth' :: CProgram Expr BExpr
auth' = prog
  ( []
  , [ ann "authenticate" $ com c credentials' ip credentials
    , cond ip check
      ( [ ann "autOk" $ left ip s
        , ann "authOk" $ left ip c
        , ann "acceptToken" $ com s token' c token ]
      , [ ann "authFail" $ right ip s
        , ann "authFail" $ right ip c ] ) ] )
  where
    [ip, s, c] = pids ["Ip", "Server", "Client"]
    [credentials, token] = vars ["credentials", "token"]
    [credentials', token'] = [Ref credentials, Ref token]
    [check] = [BExpr $ credentials']

authc' :: Choreography Expr BExpr
authc' = let CProgram (_, c) = auth' in c

authb' :: BProgram Expr BExpr
authb' = fromJust $ epp auth'

authn' :: Network Expr BExpr
authn' = let BProgram (_, n) = authb' in n

-- Jolie DistAuth Example

jolie :: CProgram JolieExpr JolieBExpr
jolie = prog
  ( []
  , [ ann "authenticate" $ com c "credentials" ip credentials
    , cond ip "check@Util( credentials )"
      ( [ ann "authOk" $ left ip s
        , ann "authOk" $ left ip c
        , ann "acceptToken" $ com s "makeToken@Util()" c token ]
      , [ ann "authFail" $ right ip s
        , ann "authFail" $ right ip c ] ) ] )
  where
    [ip, s, c] = pids ["Ip", "Server", "Client"]
    [credentials, token] = vars ["credentials", "token"]

joliec :: Choreography JolieExpr JolieBExpr
joliec = let CProgram (_, c) = jolie in c

jolieb :: BProgram JolieExpr JolieBExpr
jolieb = fromJust $ epp jolie

jolien :: Network JolieExpr JolieBExpr
jolien = let BProgram (_, n) = jolieb in n

joliej :: String
joliej = compileJolie "" jolieb

-- Jolie DistAuth RecVar Example

jolierec :: CProgram JolieExpr JolieBExpr
jolierec = prog
  ( [ (x, [ ann "authenticate" $ com c "credentials" ip credentials
          , cond ip "check@Util( credentials )"
            ( [ ann "authOk" $ left ip s
              , ann "authOk" $ left ip c
              , ann "acceptToken" $ com s "makeToken@Util()" c token
              , call x ]
            , [ ann "authFail" $ right ip s
              , ann "authFail" $ right ip c
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

jolierecj :: String
jolierecj = compileJolie "" jolierecb
