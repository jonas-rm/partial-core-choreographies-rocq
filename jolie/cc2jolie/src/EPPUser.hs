{-# LANGUAGE DeriveGeneric, DeriveAnyClass #-}

module EPPUser where

import Control.DeepSeq (NFData)
import Control.Spoon (spoon)
import GHC.Generics (Generic)

import qualified Data.List as L
import qualified Data.Set as S

import qualified EPP as E

-- Util

indent :: Int -> String -> String
indent d str =
  (L.intercalate "\n" [replicate d ' ' ++ l | l <- lines str] ++
   if length str /= 0 && last str == '\n' then "\n" else "")

join :: String -> [String] -> String
join = L.intercalate

slap :: [String] -> String
slap = join "\n"

slop :: String -> [String] -> String
slop sep = join sep . L.delete ""

-- Choreographies

newtype Var = Var String deriving (Show, Eq, Generic, NFData)
newtype Pid = Pid String deriving (Show, Eq, Ord, Generic, NFData)
newtype RecVar = RecVar String deriving (Show, Eq, Ord, Generic, NFData)
data Label = CLeft | CRight deriving (Show, Eq, Generic, NFData)
newtype Ann = Ann String deriving (Show, Eq, Generic, NFData)

data Eta e
  = Com Pid e Pid Var
  | Sel Pid Pid Label
  deriving (Show, Generic, NFData)

data Choreography e b
  = CEnd
  | Interaction (Eta e) Ann (Choreography e b)
  | CCond Pid b (Choreography e b) (Choreography e b)
  | CCall RecVar
  | RtCall RecVar [Pid] (Choreography e b)
  deriving (Show, Generic, NFData)

newtype CDefSet e b = CDefSet [(RecVar, Choreography e b)] deriving (Show, Generic, NFData)
newtype CProgram e b = CProgram (CDefSet e b, Choreography e b) deriving (Show, Generic, NFData)

-- Processes

data Behaviour e b
  = BEnd
  | Send Pid e Ann (Behaviour e b)
  | Recv Pid Var Ann (Behaviour e b)
  | Choose Pid Label Ann (Behaviour e b)
  | Offer Pid (Maybe (Ann, (Behaviour e b))) (Maybe (Ann, (Behaviour e b)))
  | BCond b (Behaviour e b) (Behaviour e b)
  | BCall (RecVar, Pid)
  deriving (Show, Generic, NFData)

newtype BDefSet e b = BDefSet [((RecVar, Pid), Behaviour e b)] deriving (Show, Generic, NFData)
newtype Network e b = Network [(Pid, Behaviour e b)] deriving (Show, Generic, NFData)
newtype BProgram e b = BProgram (BDefSet e b, Network e b) deriving (Show, Generic, NFData)

-- Encode

cast :: a -> b
cast = E.unsafeCoerce

encodeProd :: (a, b) -> E.Prod a b
encodeProd (x1, x2) = E.Pair x1 x2

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

collectPids :: CDefSet e b -> Choreography e b -> [Pid]
collectPids (CDefSet defs) c' = S.toList $ collect S.empty c'
  where
    collect _ CEnd = S.empty
    collect seen (Interaction (Com src _ dst _) _ c) =
      S.fromList [src, dst] `S.union` collect seen c
    collect seen (Interaction (Sel src dst _) _ c) =
      S.fromList [src, dst] `S.union` collect seen c
    collect seen (CCond pid _ c1 c2) =
      S.singleton pid `S.union` collect seen c1 `S.union` collect seen c2
    collect seen (CCall v)
      | S.member v seen = S.empty
      | otherwise = case L.lookup v defs of
        Just c -> collect (S.insert v seen) c
        Nothing -> error $ "Definition doesn't exist: " ++ show v
    collect _ (RtCall _ _ _) = error "Runtime term encountered"

encodeDefs :: CDefSet e b -> E.DefSet
encodeDefs s@(CDefSet defs) = \v -> let d = cast v :: RecVar in
  case L.lookup d defs of
    Just c -> E.Pair (encodeList $ map cast $ collectPids s c) (encodeChoreography c)
    Nothing -> error $ "Definition doesn't exist: " ++ show d

encodeProgram :: CProgram e b -> (E.Program, [(RecVar, Pid)], [Pid])
encodeProgram (CProgram (s@(CDefSet defs), c)) =
  (E.Pair (encodeDefs s) (encodeChoreography c),
   [(v, pid) | (v, c') <- defs, pid <- collectPids s c'],
   collectPids s c)

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
decodeBehaviour (E.Call0 v) = BCall $ decodeProd $ cast v

decodeNetwork :: [Pid] -> E.Network -> Network e b
decodeNetwork pids n =
  Network $ [(pid, decodeBehaviour $ n $ cast pid) | pid <- pids]

decodeDefs :: [(RecVar, Pid)] -> E.DefSetB -> BDefSet e b
decodeDefs vs s =
  BDefSet $ [(v, decodeBehaviour $ s $ cast $ encodeProd v) | v <- vs]

decodeProgram :: [(RecVar, Pid)] -> [Pid] -> E.Program0 -> BProgram e b
decodeProgram vs pids (E.Pair s n) =
  BProgram (decodeDefs vs s, decodeNetwork pids n)

-- Signature

sig :: E.Signature
sig = E.Build_Signature (cast pid) (cast var) undefined undefined undefined (cast recvar) (cast ann) undefined undefined
  where
    eq :: Eq a => a -> a -> E.Sumbool
    eq x y = if x == y then E.Left else E.Right

    pid :: Pid -> Pid -> E.Sumbool
    pid = eq

    var :: Var -> Var -> E.Sumbool
    var = eq

    -- val :: Eq v => v -> v -> E.Sumbool
    -- val = eq

    -- expr :: Eq e => e -> e -> E.Sumbool
    -- expr = eq

    -- bexpr :: Eq b => b -> b -> E.Sumbool
    -- bexpr = eq

    ann :: Ann -> Ann -> E.Sumbool
    ann = eq

    recvar :: RecVar -> RecVar -> E.Sumbool
    recvar = eq

    -- ev :: e -> (Var -> v) -> v
    -- ev ex e = eval (Env e) ex
    -- ev = undefined

    -- bev :: b -> (Var -> v) -> Bool
    -- bev ex e = beval (Env e) ex
    -- bev = undefined

-- Projection

epp :: (NFData e, NFData b) => CProgram e b -> Maybe (BProgram e b)
epp p = spoon $ decodeProgram vs pids $ E.epp sig $ p'
  where (p', vs, pids) = encodeProgram p

-- Pretty-printing

class PPrint a where
  format :: a -> String

  pprint :: a -> IO ()
  pprint = putStrLn . format

instance PPrint Label where
  format CLeft = "left"
  format CRight = "right"

instance PPrint Ann where
  format (Ann "") = ""
  format (Ann ann) = " {" ++ ann ++ "}"

instance (PPrint e, PPrint b) => PPrint (Choreography e b) where
  format CEnd = ""
  format (Interaction (Com (Pid src) ex (Pid dst) (Var v)) ann c) =
    (src ++ ".(" ++ format ex ++ ") -> " ++ dst ++ "." ++ v ++
     format ann ++ ";\n" ++ format c)
  format (Interaction (Sel (Pid src) (Pid dst) l) ann c) =
    (src ++ " -> " ++ dst ++ " [" ++ format l ++ "]" ++
     format ann ++ ";\n" ++ format c)
  format (CCond (Pid p) ex c1 c2) =
    ("if " ++ p ++ ".(" ++ format ex ++ ") then\n" ++ (indent 2 $ format c1) ++
     "else\n" ++ (indent 2 $ format c2))
  format (CCall (RecVar v)) = v ++ ";\n"
  format (RtCall (RecVar v) pids c) =
    let ps = [p | Pid p <- pids] in
      v ++ "(" ++ join ", " ps ++ ");\n" ++ format c

section :: PPrint a => String -> a -> String
section header x = header ++ ":\n" ++ (indent 2 $ format x)

instance (PPrint e, PPrint b) => PPrint (CDefSet e b) where
  format (CDefSet defs) = slap [section v c | (RecVar v, c) <- defs]

instance (PPrint e, PPrint b) => PPrint (CProgram e b) where
  format (CProgram (CDefSet defs, c)) =
    format $ CDefSet $ defs ++ [(RecVar "main", c)]

instance (PPrint e, PPrint b) => PPrint (Behaviour e b) where
  format BEnd = ""
  format (Send (Pid dst) ex ann b) =
    (dst ++ "!(" ++ format ex ++ ")" ++
     format ann ++ ";\n" ++ format b)
  format (Recv (Pid src) (Var v) ann b) =
    (src ++ "?" ++ v ++
     format ann ++ ";\n" ++ format b)
  format (Choose (Pid dst) l ann b) =
    (dst ++ "⊕" ++ format l ++
     format ann ++ ";\n" ++ format b)
  format (Offer (Pid src) left right) =
    (src ++ "&{\n" ++
     (indent 2 $
       ("left" ++ (case left of
                    Just (ann, b') -> case b' of
                      BEnd -> ": ∅;\n"
                      b'' -> format ann ++ ":\n" ++ (indent 2 $ format b'')
                    Nothing -> ": ∅;\n") ++
        "right" ++ (case right of
                     Just (ann, b') -> case b' of
                       BEnd -> ": ∅;\n"
                       b'' -> format ann ++ ":\n" ++ (indent 2 $ format b'')
                     Nothing -> ": ∅;\n"))) ++
      "}\n")
  format (BCond ex b1 b2) =
    ("if (" ++ format ex ++ ") then\n" ++ (indent 2 $ format b1) ++
     "else\n" ++ (indent 2 $ format b2))
  format (BCall (RecVar v, Pid pid)) = v ++ "_" ++ pid ++ ";\n"

instance (PPrint e, PPrint b) => PPrint (BDefSet e b) where
  format (BDefSet defs) =
    slap [section (v ++ "_" ++ pid) c | ((RecVar v, Pid pid), c) <- defs]

instance (PPrint e, PPrint b) => PPrint (Network e b) where
  format (Network n) = slap [section pid b | (Pid pid, b) <- n]

instance (PPrint e, PPrint b) => PPrint (BProgram e b) where
  format (BProgram (defs, n)) = slop "\n" [format defs, format n]
