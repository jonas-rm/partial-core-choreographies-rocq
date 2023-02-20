module EPPUser where

import Data.Maybe (fromJust, fromMaybe, catMaybes, listToMaybe)
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified GHC.Base

import qualified EPP as E

-- Expressions

newtype Var = Var String deriving (Show, Eq)

newtype Env = Env [(Var, Val)] deriving Show

empty :: Env
empty = Env []

bind :: Env -> Var -> Val -> Env
bind (Env e) v x = Env $ (v, x):e

ref :: Env -> Var -> Val
ref (Env e) v = case L.lookup v e of
  Just x -> x
  Nothing -> error "Variable doesn't exist"

data Val
  = BoolVal Bool
  | IntVal Int
  | StringVal String
  | FunVal Env Var Expr

instance Show Val where
  show (BoolVal x) = show x
  show (IntVal x) = show x
  show (StringVal x) = show x
  show _ = "#<FunVal>"

instance Eq Val where
  (==) (BoolVal x1) (BoolVal x2) = x1 == x2
  (==) (IntVal x1) (IntVal x2) = x1 == x2
  (==) (StringVal x1) (StringVal x2) = x1 == x2
  (==) _ _ = False

data Expr
  = Lit Val
  | Ref Var
  | Lambda Var Expr
  | Apply Expr Expr
  | Foreign (Val -> Val -> Val) Expr Expr

instance Show Expr where
  show (Lit x) = "Lit (" ++ show x ++ ")"
  show (Ref v) = "Ref (" ++ show v ++ ")"
  show (Lambda v b) = "Lambda (" ++ show v ++ ") (" ++ show b ++ ")"
  show (Apply f x) = "Apply (" ++ show f ++ ") (" ++ show x ++ ")"
  show (Foreign _ x y) = "Foreign #<F> (" ++ show x ++ ") (" ++ show y ++ ")"

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
eval e (Apply f x) = case eval e f of
  FunVal e' v b -> eval (bind e' v $ eval e x) b
  _ -> error "Cannot apply a non-function"
eval e (Foreign f x y) = f (eval e x) (eval e y)

newtype BExpr = BExpr Expr deriving Show

beval :: Env -> BExpr -> Bool
beval e (BExpr ex) = case eval e ex of
  BoolVal b -> b
  _ -> error "Expression did not evaluate to a boolean"

-- Choreographies

newtype Pid = Pid String deriving (Show, Eq, Ord)
newtype RecVar = RecVar String deriving (Show, Eq, Ord)
data Label = CLeft | CRight deriving (Show, Eq)
newtype Ann = Ann String deriving (Show, Eq)

data Eta e
  = Com Pid e Pid Var
  | Sel Pid Pid Label
  deriving Show

data Choreography e b
  = CEnd
  | Interaction (Eta e) Ann (Choreography e b)
  | CCond Pid b (Choreography e b) (Choreography e b)
  | CCall RecVar
  | RtCall RecVar [Pid] (Choreography e b)
  deriving Show

newtype CDefSet e b = CDefSet [(RecVar, ([Pid], Choreography e b))] deriving Show
newtype CProgram e b = CProgram (CDefSet e b, Choreography e b) deriving Show

-- Processes

data Behaviour e b
  = BEnd
  | Send Pid e Ann (Behaviour e b)
  | Recv Pid Var Ann (Behaviour e b)
  | Choose Pid Label Ann (Behaviour e b)
  | Offer Pid (Maybe (Ann, (Behaviour e b))) (Maybe (Ann, (Behaviour e b)))
  | BCond b (Behaviour e b) (Behaviour e b)
  | BCall RecVar
  deriving Show

newtype BDefSet e b = BDefSet [(RecVar, Behaviour e b)] deriving Show
newtype Network e b = Network [(Pid, Behaviour e b)] deriving Show
newtype BProgram e b = BProgram (BDefSet e b, Network e b) deriving Show

-- Encode

cast = E.unsafeCoerce

encodeList :: [a] -> E.List a
encodeList [] = E.Nil
encodeList (x:xs) = E.Cons x (encodeList xs)

encodeChoreography :: Choreography e b -> E.Choreography
encodeChoreography CEnd = E.End
encodeChoreography (Interaction (Com src ex dst v) ann c) =
  E.Interaction (E.Com (cast src) (cast ex) (cast dst) (cast v)) (cast ann) (encodeChoreography c)
encodeChoreography (Interaction (Sel src dst l) ann c) =
  E.Interaction (E.Sel (cast src) (cast dst) (cast l)) (cast ann) (encodeChoreography c)
encodeChoreography (CCond pid ex c1 c2) =
  E.Cond (cast pid) (cast ex) (encodeChoreography c1) (encodeChoreography c2)
encodeChoreography (CCall v) = E.Call (cast v)
encodeChoreography (RtCall v pids c) =
  E.RT_Call (cast v) (encodeList $ map cast pids) (encodeChoreography c)

collectPids :: CProgram e b -> S.Set Pid
collectPids (CProgram (CDefSet defs, c)) = S.unions $ map rec $ [c] ++ (map (snd . snd) defs)
  where
    rec CEnd = S.empty
    rec (Interaction (Com src _ dst _) _ c) = S.fromList [src, dst] `S.union` rec c
    rec (Interaction (Sel src dst _) _ c) = S.fromList [src, dst] `S.union` rec c
    rec (CCond pid _ c1 c2) = S.singleton pid `S.union` rec c1 `S.union` rec c2
    rec (CCall _) = S.empty
    rec (RtCall _ pids c) = S.fromList pids `S.union` rec c

encodeDefs :: CDefSet e b -> E.DefSet
encodeDefs (CDefSet s) = \v -> case L.lookup (cast v) s of
  Just (pids, c) -> E.Pair (encodeList $ map cast pids) (encodeChoreography c)
  Nothing -> error "Definition doesn't exist"

encodeProgram :: CProgram e b -> (E.Program, [RecVar], [Pid])
encodeProgram p@(CProgram (s, c)) =
  (E.Pair (encodeDefs s) (encodeChoreography c),
   let CDefSet s' = s in L.nub $ map fst s',
   S.toList $ collectPids p)

-- Decode

decodeOption :: E.Option a -> Maybe a
decodeOption (E.Some x) = Just x
decodeOption E.None = Nothing

decodeProd :: E.Prod a b -> (a, b)
decodeProd (E.Pair x1 x2) = (x1, x2)

decodeBehaviour :: E.Behaviour -> Behaviour e b
decodeBehaviour (E.End0) = BEnd
decodeBehaviour (E.Send dst ex ann b) =
  Send (cast dst) (cast ex) (cast ann) (decodeBehaviour b)
decodeBehaviour (E.Recv src v ann b) =
  Recv (cast src) (cast v) (cast ann) (decodeBehaviour b)
decodeBehaviour (E.Sel0 dst l ann b) =
  Choose (cast dst) (cast l) (cast ann) (decodeBehaviour b)
decodeBehaviour (E.Branching pid left right) =
  let decode (ann, b) = (cast ann, decodeBehaviour b)
      left' = decode . decodeProd <$> decodeOption left
      right' = decode . decodeProd <$> decodeOption right in
    Offer (cast pid) left' right'
decodeBehaviour (E.Cond0 ex b1 b2) =
  BCond (cast ex) (decodeBehaviour b1) (decodeBehaviour b2)
decodeBehaviour (E.Call0 v) = BCall (cast v)

decodeNetwork :: [Pid] -> E.Network -> Network e b
decodeNetwork pids n = Network $
  map (\pid -> (pid, decodeBehaviour $ n $ cast pid)) pids

decodeDefs :: [RecVar] -> E.DefSetB -> BDefSet e b
decodeDefs vs s = BDefSet $ map (\v -> (v, decodeBehaviour $ s $ cast v)) vs

decodeProgram :: [RecVar] -> [Pid] -> E.Program0 -> BProgram e b
decodeProgram vs pids (E.Pair s n) =
  BProgram (decodeDefs vs s, decodeNetwork pids n)

-- Projection

epp :: E.Signature -> CProgram e b -> BProgram e b
epp sig p = decodeProgram vs pids $ E.epp sig $ p'
  where (p', vs, pids) = encodeProgram p

-- Signature

toSumbool :: Bool -> E.Sumbool
toSumbool True = E.Left
toSumbool False = E.Right

sig :: E.Signature
sig = E.Build_Signature (cast val) (cast bool) (cast val) (cast expr) (cast bexpr) (cast val) (cast ann) (cast eval') (cast beval')
  where
    val :: Val -> Val -> E.Sumbool
    val (IntVal x1) (IntVal x2) = toSumbool $ x1 == x2
    -- val = undefined

    bool :: Val -> Val -> E.Sumbool
    -- bool (BoolVal x1) (BoolVal x2) = toSumbool $ x1 == x2
    bool = undefined

    expr :: Expr -> Expr -> E.Sumbool
    -- expr ex1 ex2 = toSumbool $ ex1 == ex2
    expr = undefined

    bexpr :: BExpr -> BExpr -> E.Sumbool
    -- bexpr (BExpr ex1) (BExpr ex2) = toSumbool $ ex1 == ex2
    bexpr = undefined

    ann :: Ann -> Ann -> E.Sumbool
    -- ann a1 a2 = toSumbool $ a1 == a2
    ann = undefined

    eval' :: Expr -> (Var -> Val) -> Val
    -- eval' ex e = eval (Env e) ex
    eval' = undefined

    beval' :: BExpr -> (Var -> Val) -> Bool
    -- beval' ex e = beval (Env e) ex
    beval' = undefined

-- Pretty-printing

class Format a where
  format :: a -> String

instance Format Expr where
  format (Lit x) = show x
  format (Ref (Var v)) = v
  format (Lambda (Var v) b) = "\\" ++ v ++ " -> " ++ format b
  format (Apply f x) = "(" ++ format f ++ ") (" ++ format x ++ ")"
  format (Foreign _ x y) = "#<F> (" ++ format x ++ ") (" ++ format y ++ ")"

instance Format BExpr where
  format (BExpr ex) = format ex

formatLabel :: Label -> String
formatLabel CLeft = "left"
formatLabel CRight = "right"

formatAnn :: Ann -> String
formatAnn (Ann "") = ""
formatAnn (Ann ann) = " {" ++ ann ++ "}"

formatChoreography :: (Format e, Format b) => Int -> Choreography e b -> String
formatChoreography d CEnd = ""
formatChoreography d (Interaction (Com (Pid src) ex (Pid dst) (Var v)) ann c) =
  (replicate d ' ' ++ src ++ ".(" ++ format ex ++ ") -> " ++ dst ++ "." ++ v ++
   formatAnn ann ++ ";\n" ++ formatChoreography d c)
formatChoreography d (Interaction (Sel (Pid src) (Pid dst) l) ann c) =
  (replicate d ' ' ++ src ++ " -> " ++ dst ++
   "[" ++ formatLabel l ++ "]" ++ formatAnn ann ++ ";\n" ++
   formatChoreography d c)
formatChoreography d (CCond (Pid p) ex c1 c2) =
  (replicate d ' ' ++ "if " ++ p ++ ".(" ++ format ex ++ ") then\n" ++
   formatChoreography (d + 2) c1 ++
   replicate d ' ' ++ "else\n" ++
   formatChoreography (d + 2) c2)
formatChoreography d (CCall (RecVar v)) = v ++ ";\n"
formatChoreography d (RtCall (RecVar v) pids c) =
  let ps = map (\(Pid p) -> p) pids in
    (replicate d ' ' ++ v ++ "(" ++ L.intercalate ", " ps ++ ");\n" ++
     formatChoreography d c)

instance (Format e, Format b) => Format (Choreography e b) where
  format = formatChoreography 0

formatBehaviour :: (Format e, Format b) => Int -> (Behaviour e b) -> String
formatBehaviour _ BEnd = ""
formatBehaviour d (Send (Pid dst) ex ann b) =
  (replicate d ' ' ++ dst ++ "!(" ++ format ex ++ ")" ++
   formatAnn ann ++ ";\n" ++ formatBehaviour d b)
formatBehaviour d (Recv (Pid src) (Var v) ann b) =
  (replicate d ' ' ++ src ++ "?" ++ v ++
   formatAnn ann ++ ";\n" ++ formatBehaviour d b)
formatBehaviour d (Choose (Pid dst) l ann b) =
  (replicate d ' ' ++ dst ++ "⊕" ++ formatLabel l ++
   formatAnn ann ++ ";\n" ++ formatBehaviour d b)
formatBehaviour d (Offer (Pid src) left right) =
  (replicate d ' ' ++ src ++ "&{\n" ++
   replicate (d + 2) ' ' ++
   "left" ++ (case left of
                 Just (ann, b) -> case b of
                   BEnd -> ": ∅;\n"
                   b -> formatAnn ann ++ ":\n" ++ formatBehaviour (d + 4) b
                 Nothing -> ": ∅;\n") ++
   replicate (d + 2) ' ' ++ "\n" ++ replicate (d + 2) ' ' ++
   "right" ++ (case right of
                  Just (ann, b) -> case b of
                    BEnd -> ": ∅;\n"
                    b -> formatAnn ann ++ ":\n" ++ formatBehaviour (d + 4) b
                  Nothing -> ": ∅;\n") ++
   replicate d ' ' ++ "}\n")
formatBehaviour d (BCond ex b1 b2) =
  (replicate d ' ' ++ "if (" ++ format ex ++ ") then\n" ++
   formatBehaviour (d + 2) b1 ++
   replicate d ' ' ++ "else\n" ++
   formatBehaviour (d + 2) b2)
formatBehaviour d (BCall (RecVar v)) =
  replicate d ' ' ++ v ++ ";\n"

instance (Format e, Format b) => Format (Behaviour e b) where
  format = formatBehaviour 0

instance (Format e, Format b) => Format (Network e b) where
  format (Network n) = L.intercalate "\n" $ map (\(Pid pid, b) -> pid ++ ":\n" ++ formatBehaviour 2 b) n

-- Lambda Example

plus :: Val -> Val -> Val
plus (IntVal x) (IntVal y) = IntVal $ x + y
plus _ _ = error "Cannot add non-integer values"

lambda = (Apply
          (Apply
           (Lambda (Var "x")
            (Lambda (Var "y")
             (Foreign plus (Ref (Var "x")) (Ref (Var "y")))))
           (Lit (IntVal 5)))
          (Lit (IntVal 10)))

-- EPP Example

{-
  client.getCredentials() -> ip.credentials;

  if checkCredentials ip.credentials then
    ip -> client[left];
    ip -> server[left];
    server.token -> client.token;
    client.write("authenticated: " + token);
  else
    ip -> client[right];
    ip -> server[right];
    client.write("unauthenticated");
-}

auth = let ip = Pid "Ip"
           s = Pid "Server"
           c = Pid "Client"
           a = Ann ""
           credentials = Var "credentials"
           token = Ref (Var "token")
           t = Var "t"
           c1 = Interaction (Sel ip s CLeft) a (Interaction (Sel ip c CLeft) a (Interaction (Com s token c t) a CEnd))
           c2 = Interaction (Sel ip s CRight) a (Interaction (Sel ip c CRight) a CEnd)
           c3 = Interaction (Com c (Ref credentials) ip credentials) a (CCond ip (BExpr $ Lit $ BoolVal True) c1 c2)
     in CProgram (CDefSet [], c3)
authc = let CProgram (_, c) = auth in c
authb = epp sig auth
authn = let BProgram (_, n) = authb in n

-- Jolie

data JolieExpr = JolieExpr String deriving Show
data JolieBExpr = JolieBExpr JolieExpr deriving Show

type JolieBehaviour = Behaviour JolieExpr JolieBExpr
type JolieDefSet = BDefSet JolieExpr JolieBExpr
type JolieProgram = BProgram JolieExpr JolieBExpr

instance Format JolieExpr where
  format (JolieExpr e) = e

instance Format JolieBExpr where
  format (JolieBExpr e) = format e

header :: String
header = "type Msg: any { ? }\n" ++ "type Label: string {}"

indent :: Int -> String -> String
indent d = L.intercalate "\n" . map (\l -> replicate d ' ' ++ l) . lines

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
serviceDefault = Service { sPid = undefined, sBehaviour = undefined,
                           sPort = undefined, sOutputs = S.empty,
                           sOps = S.empty }

makeOp :: String -> Pid -> Ann -> String
makeOp prefix (Pid pid) (Ann "") = prefix ++ pid
makeOp _ _ (Ann ann) = ann

addOp :: Service -> (String -> JolieOp) -> String -> Service
addOp s ctor op = s { sOps = S.insert (ctor op) $ sOps s }

serviceUnion :: Service -> Service -> Service
serviceUnion s1 s2 = s1 { sOutputs = S.union (sOutputs s1) (sOutputs s2),
                          sOps = S.union (sOps s1) (sOps s2) }

mkService :: JolieDefSet -> Int -> (Pid, JolieBehaviour) -> Service
mkService (BDefSet defs) port (pid, b) = rec S.empty (serviceDefault { sPid = pid, sPort = port, sBehaviour = b }) b
  where
    rec _ s BEnd = s
    rec seen s (Send dst _ ann b) = rec seen (s { sOutputs = S.insert dst $ sOutputs s }) b
    rec seen s (Recv src _ ann b) = rec seen (addOp s JolieCom $ makeOp "com" src ann) b
    rec seen s (Choose dst _ ann b) = rec seen (s { sOutputs = S.insert dst $ sOutputs s }) b
    rec seen s (Offer src left right) = serviceUnion (branch seen s src left) (branch seen s src right)
    rec seen s (BCond _ b1 b2) = serviceUnion (rec seen s b1) (rec seen s b2)
    rec seen s (BCall v) = if S.member v seen then s else rec (S.insert v seen) s b
      where Just b = L.lookup v defs

    branch _ s _ Nothing = s
    branch seen s src (Just (ann, b)) = rec seen (addOp s JolieSel $ makeOp "sel" src ann) b

collectServices :: JolieProgram -> M.Map Pid Service
collectServices p@(BProgram (defs, Network n)) = foldr f M.empty $ zip [8080..] n
  where
    f (port, proc@(pid, _)) m = M.insert pid (mkService defs port proc) m

compileInterface :: Service -> String
compileInterface s = ("interface " ++ pid ++ "Api {\n" ++
                      replicate 4 ' ' ++ "OneWay:\n" ++
                      L.intercalate ",\n" (map compileOp $ S.toList $ sOps s) ++
                      "\n}")
  where
    Pid pid = sPid s
    compileOp o = replicate 8 ' ' ++ (case o of
      JolieCom name -> name ++ "( Msg )"
      JolieSel name -> name ++ "( Label )")

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
compileOutputPorts smap s = L.intercalate "\n\n" $ map compileOutputPort outputs
  where
    outputs = map (\pid -> fromJust $ M.lookup pid smap) $ S.toList $ sOutputs s

compilePorts :: M.Map Pid Service -> Service -> String
compilePorts smap s = compileInputPort s ++ "\n\n" ++ compileOutputPorts smap s

branchAnn :: Maybe (Ann, Behaviour e b) -> Maybe (Ann, Behaviour e b) -> Maybe String
branchAnn left right = listToMaybe $ catMaybes $ map f $ [left, right]
  where
    f (Just (Ann "", _)) = Nothing
    f (Just (Ann a, _)) = Just a
    f Nothing = Nothing

compileBehaviour :: Service -> String
compileBehaviour s = "main {\n" ++ (indent 4 $ rec 0 $ sBehaviour s) ++ "\n}"
  where
    rec _ BEnd = ""
    rec d (Send (Pid dst) ex ann b) =
      (replicate d ' ' ++ (makeOp "com" (sPid s) ann) ++ "@" ++ dst ++
       "( " ++ format ex ++ " );\n" ++ rec d b)
    rec d (Recv src (Var v) ann b) =
      (replicate d ' ' ++ (makeOp "com" src ann) ++ "( " ++ v ++ " );\n" ++
       rec d b)
    rec d (Choose (Pid dst) l ann b) =
      (replicate d ' ' ++ (makeOp "sel" (sPid s) ann) ++ "@" ++ dst ++
       "( \"" ++ formatLabel l ++ "\" );\n" ++ rec d b)
    rec d (Offer src left right) = let op = fromMaybe (makeOp "sel" src (Ann "")) (branchAnn left right) in
      (replicate d ' ' ++ op ++ "( label );\n" ++
       replicate d ' ' ++ "if ( label == \"left\" ) {\n" ++
       (case left of
         Just (ann, b) -> case b of
           BEnd -> replicate (d + 4) ' ' ++ "// empty\n"
           b -> rec (d + 4) b
         Nothing -> replicate (d + 4) ' ' ++ "// empty\n") ++
       replicate d ' ' ++ "} else {\n" ++
       (case right of
         Just (ann, b) -> case b of
           BEnd -> replicate (d + 4) ' ' ++ "// empty\n"
           b -> rec (d + 4) b
         Nothing -> replicate (d + 4) ' ' ++ "// empty\n") ++
       replicate d ' ' ++ "}\n")
    rec d (BCond ex b1 b2) =
      (replicate d ' ' ++ "if ( " ++ format ex ++ " ) {\n" ++
       rec (d + 4) b1 ++
       replicate d ' ' ++ "} else {\n" ++
       rec (d + 4) b2
       ++ "}")
    rec d (BCall (RecVar v)) =
      replicate d ' ' ++ v ++ ";\n"

compileBody :: M.Map Pid Service -> Service -> String
compileBody smap s = let Pid pid = sPid s in
  ("service " ++ pid ++ " {\n" ++
   L.intercalate "\n\n" [indent 4 $ compileInputPort s,
                         indent 4 $ compileOutputPorts smap s,
                         indent 4 $ compileBehaviour s] ++
   "\n}")

compileJolie :: JolieProgram -> String
compileJolie p@(BProgram (_, Network n)) =
  L.intercalate "\n\n" $ [header] ++ interfaces ++ bodies
  where
    smap = collectServices p
    services = M.elems smap
    interfaces = map compileInterface services
    bodies = map (compileBody smap) services

-- Jolie Test

auth' = let ip = Pid "Ip"
            s = Pid "Server"
            c = Pid "Client"
            a = Ann ""
            credentials = JolieExpr "credentials"
            token = JolieExpr "makeToken()"
            x = Var "credentials"
            t = Var "t"
            cond = JolieBExpr $ JolieExpr "check( credentials )"
            c1 = Interaction (Sel ip s CLeft) (Ann "ann1") (Interaction (Sel ip c CLeft) a (Interaction (Com s token c t) a CEnd))
            c2 = Interaction (Sel ip s CRight) (Ann "ann2") (Interaction (Sel ip c CRight) a CEnd)
            c3 = Interaction (Com c credentials ip x) a (CCond ip cond c1 c2)
        in CProgram (CDefSet [], c3)
authc' = let CProgram (_, c) = auth' in c
authb' = epp sig auth'
authn' = let BProgram (_, n) = authb' in n
