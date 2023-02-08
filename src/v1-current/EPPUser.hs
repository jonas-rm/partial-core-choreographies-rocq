module EPPUser where

-- TODO: Parsing.

-- TODO: Simulation. How exactly does evaluation work? How exactly can we use
-- the "state function" and who even provides it?

-- TODO: Make our representation use lists instead of functions. We can recover
-- them because we can collect all of the Pids and then extract them later.

import qualified Data.List as L
import qualified GHC.Base

import qualified EPP as E

-- Expressions

newtype Var = Var String deriving (Show, Eq)

-- newtype Env = Env [(Var, Val)] deriving Show

-- empty :: Env
-- empty = Env []

-- bind :: Env -> Var -> Val -> Env
-- bind (Env e) v x = Env $ (v, x):e

-- ref :: Env -> Var -> Val
-- ref (Env e) v = case L.lookup v e of
--   Just x -> x
--   Nothing -> error "Variable doesn't exist"

newtype Env = Env (Var -> Val)

instance Show Env where
  show _ = "#<Env>"

emptyEnv :: Env
emptyEnv = Env $ \_ -> error "Variable doesn't exist"

bind :: Env -> Var -> Val -> Env
bind (Env e) v x = Env $ \v' -> if v' == v then x else e v'

ref :: Env -> Var -> Val
ref (Env e) v = e v

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

newtype Pid = Pid String deriving (Show, Eq)
newtype RecVar = RecVar String deriving (Show, Eq)
data Label = CLeft | CRight deriving (Show, Eq)
newtype Ann = Ann String deriving (Show, Eq)

data Eta
  = Com Pid Expr Pid Var
  | Sel Pid Pid Label
  deriving Show

data Choreography
  = CEnd
  | Interaction Eta Ann Choreography
  | CCond Pid BExpr Choreography Choreography
  | CCall RecVar
  | RtCall RecVar [Pid] Choreography
  deriving Show

-- newtype CDefSet = CDefSet [(RecVar, ([Pid], Choreography))] deriving Show
newtype CDefSet = CDefSet (RecVar -> ([Pid], Choreography))

emptyCDefSet :: CDefSet
emptyCDefSet = CDefSet $ \_ -> error "Definition doesn't exist"

instance Show CDefSet where
  show _ = "#<CDefSet>"

newtype CProgram = CProgram (CDefSet, Choreography) deriving Show

-- Processes

data Behaviour
  = BEnd
  | Send Pid Expr Ann Behaviour
  | Recv Pid Var Ann Behaviour
  | Choose Pid Label Ann Behaviour
  | Offer Pid (Maybe (Ann, Behaviour)) (Maybe (Ann, Behaviour))
  | BCond BExpr Behaviour Behaviour
  | BCall RecVar
  deriving Show

-- newtype BDefSet = BDefSet [(RecVar, Behaviour)]
newtype BDefSet = BDefSet (RecVar -> Behaviour)

instance Show BDefSet where
  show _ = "#<BDefSet>"

-- newtype Network = Network [(Pid, Behaviour)]
newtype Network = Network (Pid -> Behaviour)

instance Show Network where
  show _ = "#<Network>"

newtype BProgram = BProgram (BDefSet, Network) deriving Show

-- Encode

cast = E.unsafeCoerce

encodeList :: [a] -> E.List a
encodeList [] = E.Nil
encodeList (x:xs) = E.Cons x (encodeList xs)

encodeChoreography :: Choreography -> E.Choreography
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

encodeDefs :: CDefSet -> E.DefSet
encodeDefs (CDefSet s) = \v -> let (pids, c) = s (cast v) in
  E.Pair (encodeList $ map cast pids) (encodeChoreography c)

encodeProgram :: CProgram -> E.Program
encodeProgram (CProgram (s, c)) = E.Pair (encodeDefs s) (encodeChoreography c)

-- Decode

decodeOption :: E.Option a -> Maybe a
decodeOption (E.Some x) = Just x
decodeOption E.None = Nothing

decodeProd :: E.Prod a b -> (a, b)
decodeProd (E.Pair x1 x2) = (x1, x2)

decodeBehaviour :: E.Behaviour -> Behaviour
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

decodeNetwork :: E.Network -> Network
decodeNetwork n = Network $ \pid -> decodeBehaviour $ n (cast pid)

decodeDefs :: E.DefSetB -> BDefSet
decodeDefs s = BDefSet $ \v -> decodeBehaviour $ s (cast v)

decodeProgram :: E.Program0 -> BProgram
decodeProgram (E.Pair s n) = BProgram (decodeDefs s, decodeNetwork n)

-- Projection

epp :: E.Signature -> CProgram -> BProgram
epp sig = decodeProgram . E.epp sig . encodeProgram

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

formatLabel :: Label -> String
formatLabel CLeft = "left"
formatLabel CRight = "right"

formatAnn :: Ann -> String
formatAnn (Ann "") = ""
formatAnn (Ann ann) = " {" ++ ann ++ "}"

formatChoreography :: Int -> Choreography -> String
formatChoreography d CEnd = ""
formatChoreography d (Interaction (Com (Pid src) ex (Pid dst) (Var v)) ann c) =
  (replicate d ' ' ++ src ++ "." ++ format ex ++ " -> " ++ dst ++ "." ++ v ++
   formatAnn ann ++ ";\n" ++ formatChoreography d c)
formatChoreography d (Interaction (Sel (Pid src) (Pid dst) l) ann c) =
  (replicate d ' ' ++ src ++ " -> " ++ dst ++
   "[" ++ formatLabel l ++ "]" ++ formatAnn ann ++ ";\n" ++
   formatChoreography d c)
formatChoreography d (CCond (Pid p) (BExpr ex) c1 c2) =
  (replicate d ' ' ++ "if " ++ p ++ "." ++ format ex ++ " then\n" ++
   formatChoreography (d + 2) c1 ++
   replicate d ' ' ++ "else\n" ++
   formatChoreography (d + 2) c2)
formatChoreography d (CCall (RecVar v)) = v ++ ";\n"
formatChoreography d (RtCall (RecVar v) pids c) =
  let ps = map (\(Pid p) -> p) pids in
    (replicate d ' ' ++ v ++ "(" ++ L.intercalate ", " ps ++ ");\n" ++
     formatChoreography d c)

instance Format Choreography where
  format = formatChoreography 0

formatBehaviour :: Int -> Behaviour -> String
formatBehaviour _ BEnd = ""
formatBehaviour d (Send (Pid dst) ex ann b) =
  (replicate d ' ' ++ dst ++ "!" ++ format ex ++
   formatAnn ann ++ ";\n" ++ formatBehaviour d b)
formatBehaviour d (Recv (Pid src) (Var v) ann b) =
  (replicate d ' ' ++ src ++ "?" ++ v ++
   formatAnn ann ++ ";\n" ++ formatBehaviour d b)
formatBehaviour d (Choose (Pid dst) l ann b) =
  (replicate d ' ' ++ dst ++ "⊕" ++ formatLabel l ++
   formatAnn ann ++ ";\n" ++ formatBehaviour d b)
formatBehaviour d (Offer (Pid src) left right) =
  (replicate d ' ' ++ src ++ "&{\n" ++
   "  left" ++ (case left of
                 Just (ann, b) -> case b of
                   BEnd -> ": ∅;\n"
                   b -> formatAnn ann ++ ": " ++ formatBehaviour d b
                 Nothing -> ": ∅;\n") ++
   "  right" ++ (case right of
                  Just (ann, b) -> case b of
                    BEnd -> ": ∅;\n"
                    b -> formatAnn ann ++ ": " ++ formatBehaviour d b
                  Nothing -> ": ∅;\n") ++
   "}\n")
formatBehaviour d (BCond (BExpr ex) b1 b2) =
  (replicate d ' ' ++ "if " ++ format ex ++ " then\n" ++
   formatBehaviour (d + 2) b1 ++
   replicate d ' ' ++ "else\n" ++
   formatBehaviour (d + 2) b2)
formatBehaviour d (BCall (RecVar v)) =
  replicate d ' ' ++ v ++ ";\n"

instance Format Behaviour where
  format = formatBehaviour 0

-- Test

plus :: Val -> Val -> Val
plus (IntVal x) (IntVal y) = IntVal $ x + y
plus _ _ = error "Cannot add non-integer values"

test = (Apply
        (Apply
        (Lambda (Var "x")
         (Lambda (Var "y")
          (Foreign plus (Ref (Var "x")) (Ref (Var "y")))))
        (Lit (IntVal 5)))
       (Lit (IntVal 10)))

test2 = let ip = Pid "ip"
            s = Pid "s"
            c = Pid "c"
            a = Ann "ann"
            credentials = Ref (Var "credentials")
            token = Ref (Var "token")
            x = Var "x"
            t = Var "t"
            c1 = Interaction (Sel ip s CLeft) a (Interaction (Sel ip c CLeft) a (Interaction (Com s token c t) a CEnd))
            c2 = Interaction (Sel ip s CRight) a (Interaction (Sel ip c CRight) a CEnd)
            c3 = Interaction (Com c credentials ip x) a (CCond ip (BExpr $ Lit $ BoolVal True) c1 c2)
     in CProgram (emptyCDefSet, c3)

test3 = let BProgram (_, Network n) = epp sig test2 in
  [n (Pid "c"), n (Pid "s"), n (Pid "ip")]

test4 = let CProgram (_, c) = test2 in c

-- TODO Jolie

newtype Service = Service String

compile :: Network -> [Service]
compile = undefined
