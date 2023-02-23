{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}

module Jolie where

import Control.DeepSeq (NFData)
import Control.Spoon (spoon)
import Data.Maybe (catMaybes, listToMaybe)
import GHC.Generics (Generic)

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S

import Builder (Exprify, exprify)
import EPPUser

import qualified EPP as E

data JolieExpr = JolieExpr String deriving (Show, Generic, NFData)
data JolieBExpr = JolieBExpr JolieExpr deriving (Show, Generic, NFData)

type JolieBehaviour = Behaviour JolieExpr JolieBExpr
type JolieDefSet = BDefSet JolieExpr JolieBExpr
type JolieProgram = BProgram JolieExpr JolieBExpr

-- Pretty-printing

instance PPrint JolieExpr where
  format (JolieExpr e) = e

instance PPrint JolieBExpr where
  format (JolieBExpr e) = format e

-- Builder

instance Exprify [Char] JolieExpr where
  exprify = JolieExpr

instance Exprify [Char] JolieBExpr where
  exprify = JolieBExpr . exprify

-- Compilation

data JolieOp
  = JolieCom String
  | JolieSel String
  deriving (Show, Eq, Ord)

data Service = Service
  { sPid :: Pid
  , sPort :: Int
  , sBehaviour :: JolieBehaviour
  , sOutputs :: S.Set Pid
  , sOps :: S.Set JolieOp
  } deriving Show

serviceDefault :: Service
serviceDefault = Service
  { sPid = undefined
  , sBehaviour = undefined
  , sPort = undefined
  , sOutputs = S.empty
  , sOps = S.empty
  }

makeOp :: String -> Pid -> Ann -> String
makeOp prefix (Pid pid) (Ann "") = prefix ++ pid
makeOp _ _ (Ann ann) = ann

makeCom :: Pid -> Ann -> String
makeCom pid ann = makeOp "com" pid ann

makeSel :: Label -> Pid -> Ann -> String
makeSel l pid ann = makeOp (format l) pid ann

addOp :: Service -> (String -> JolieOp) -> String -> Service
addOp s ctor op = s { sOps = S.insert (ctor op) $ sOps s }

serviceUnion :: Service -> Service -> Service
serviceUnion s1 s2 = s1
  { sOutputs = S.union (sOutputs s1) (sOutputs s2)
  , sOps = S.union (sOps s1) (sOps s2)
  }

mkService :: JolieDefSet -> Int -> (Pid, JolieBehaviour) -> Service
mkService (BDefSet defs) port (pid, b) = mk S.empty (serviceDefault { sPid = pid, sPort = port, sBehaviour = b }) b
  where
    mk _ s BEnd = s
    mk seen s (Send dst _ _ b') = mk seen (s { sOutputs = S.insert dst $ sOutputs s }) b'
    mk seen s (Recv src _ ann b') = mk seen (addOp s JolieCom $ makeCom src ann) b'
    mk seen s (Choose dst _ _ b') = mk seen (s { sOutputs = S.insert dst $ sOutputs s }) b'
    mk seen s (Offer src left right) = serviceUnion (branch seen s src CLeft left) (branch seen s src CRight right)
    mk seen s (BCond _ b1 b2) = serviceUnion (mk seen s b1) (mk seen s b2)
    mk seen s (BCall v)
      | S.member v seen = s
      | otherwise = mk (S.insert v seen) s b'
      where
        b' = case L.lookup v defs of
          Just b'' -> b''
          Nothing -> error $ "Definition doesn't exist: " ++ show v

    branch _ s _ _ Nothing = s
    branch seen s src l (Just (ann, b')) = mk seen (addOp s JolieSel $ makeSel l src ann) b'

collectServices :: JolieProgram -> M.Map Pid Service
collectServices (BProgram (defs, Network n)) = foldr f M.empty $ zip [8080..] n
  where
    f (port, proc@(pid, _)) m = M.insert pid (mkService defs port proc) m

compileInterface :: Service -> String
compileInterface s =
  ("interface " ++ pid ++ "Api {\n" ++ "OneWay:\n" ++
    (indent 4 $ join ",\n" (map compileOp $ S.toList $ sOps s)) ++
    "\n}")
  where
    Pid pid = sPid s
    compileOp o = case o of
      JolieCom name -> name ++ "( Msg )"
      JolieSel name -> name

compileLocation :: Service -> String
compileLocation s = let Pid pid = sPid s in
  ("location: \"socket://localhost:" ++ (show $ sPort s) ++ "\"\n" ++
   "protocol: http { format = \"json\" }\n" ++
   "interfaces: " ++ pid ++ "Api")

compileInputPort :: Service -> String
compileInputPort s = "inputPort Input {\n" ++ (indent 4 $ compileLocation s) ++ "\n}"

compileOutputPort :: Service -> String
compileOutputPort s = let Pid pid = sPid s in
  "outputPort " ++ pid ++ " {\n" ++ (indent 4 $ compileLocation s) ++ "\n}"

compileOutputPorts :: M.Map Pid Service -> Service -> String
compileOutputPorts smap s = join "\n\n" $ map compileOutputPort outputs
  where
    -- NOTE: A service might not be found in case it was specified as external.
    outputs = catMaybes [M.lookup pid smap | pid <- S.toList $ sOutputs s]

compilePorts :: M.Map Pid Service -> Service -> String
compilePorts smap s = compileInputPort s ++ "\n\n" ++ compileOutputPorts smap s

branchAnn :: Maybe (Ann, Behaviour e b) -> Maybe (Ann, Behaviour e b) -> Maybe String
branchAnn left right = listToMaybe $ catMaybes $ map f $ [left, right]
  where
    f (Just (Ann "", _)) = Nothing
    f (Just (Ann a, _)) = Just a
    f Nothing = Nothing

compileBehaviour :: (PPrint e, PPrint b) => Pid -> Behaviour e b -> String
compileBehaviour pid b = compile b
  where
    compile BEnd = ""
    compile (Send (Pid dst) ex ann b') =
      (makeCom pid ann) ++ "@" ++ dst ++
      "( " ++ format ex ++ " )\n" ++ compile b'
    compile (Recv src (Var v) ann b') =
      (makeCom src ann) ++ "( " ++ v ++ " )\n" ++ compile b'
    compile (Choose (Pid dst) l ann b') =
      (makeSel l pid ann) ++ "@" ++ dst ++ "()\n" ++ compile b'
    compile (Offer src left right) =
      (slap $ catMaybes [branch src CLeft left, branch src CRight right]) ++
      "\n"
    compile (BCond ex b1 b2) =
      "if ( " ++ format ex ++ " ) {\n" ++ (indent 4 $ compile b1) ++
      "} else {\n" ++ (indent 4 $ compile b2) ++ "}\n"
    compile (BCall (RecVar v, Pid pid')) = v ++ "_" ++ pid' ++ "\n"

    branch _ _ Nothing = Nothing
    branch src l (Just (ann, b'))
      | null c = Nothing
      | otherwise = Just $ ("[ " ++ (makeSel l src ann) ++ "() ] {\n" ++
                            (indent 4 c) ++ "}")
      where
        c = compileBehaviour pid b'

compileDefinition :: (PPrint e, PPrint b) => RecVar -> Pid -> Behaviour e b -> String
compileDefinition (RecVar v) pid'@(Pid pid) b =
  ("define " ++ v ++ "_" ++ pid ++ " {\n" ++
   (indent 4 $ compileBehaviour pid' b) ++ "}")

compileDefinitions :: (PPrint e, PPrint b) => BDefSet b e -> Service -> String
compileDefinitions (BDefSet defs) s = slap [compileDefinition v pid b | ((v, pid), b) <- defs, pid == sPid s]

compileMain :: (PPrint e, PPrint b) => Pid -> Behaviour e b -> String
compileMain pid b = "main {\n" ++ (indent 4 $ compileBehaviour pid b) ++ "}"

compileService :: (PPrint e, PPrint b) => M.Map Pid Service -> BDefSet b e -> Service -> String
compileService smap defs s = let Pid pid = sPid s in
  ("service " ++ pid ++ " {\n" ++
   slop "\n\n" [indent 4 $ "embed Util as Util",
                indent 4 $ compileInputPort s,
                indent 4 $ compileOutputPorts smap s,
                indent 4 $ compileDefinitions defs s,
                indent 4 $ compileMain (sPid s) (sBehaviour s)] ++
   "\n}")

jolieHeader :: String
jolieHeader =
  "from .util import Util\n\n" ++
  "type Msg: any { ? }\n" ++
  "type Label: string {}"

compileJolie :: String -> JolieProgram -> String
compileJolie preface p@(BProgram (defs, _)) =
  slop "\n\n" $ [jolieHeader, preface] ++ interfaces ++ services'
  where
    smap = collectServices p
    services = M.elems smap
    interfaces = map compileInterface services
    services' = map (compileService smap defs) services

compileJolie' :: String -> [Pid] -> CProgram JolieExpr JolieBExpr -> Maybe String
compileJolie' preface external p = spoon $ compileJolie preface p''
  where
    (p', vs, pids) = encodeProgram p
    (BProgram (BDefSet defs, Network n)) = decodeProgram vs pids $ E.epp sig $ p'
    -- NOTE: External processes are effectively bystanders that don't
    -- participate in the choreography other than by being sent messages. This
    -- means we don't send them any labels, which will in the general case make
    -- the choreography unprojectable. Since the code of an external process is
    -- provided elsewhere anyway, we remove them from the projected program.
    --
    -- The extracted EPP code is such that is raises an exception in the case of
    -- an unprojectable choreography. However, laziness allows us to identify
    -- fragments related to external processes (via Pids provided by the user)
    -- and remove them from the program, before they've had a chance to be
    -- computed and potentially throw an error.
    p'' = BProgram (BDefSet $ [d | d@((_, pid), _) <- defs, not $ elem pid external],
                    Network $ [d | d@(pid, _) <- n, not $ elem pid external])
