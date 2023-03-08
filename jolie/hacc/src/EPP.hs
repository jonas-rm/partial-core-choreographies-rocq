{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module EPP where

import qualified Prelude

#ifdef __GLASGOW_HASKELL__
import qualified GHC.Base
#else
-- HUGS
import qualified IOExts
#endif

#ifdef __GLASGOW_HASKELL__
unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#
#else
-- HUGS
unsafeCoerce :: a -> b
unsafeCoerce = IOExts.unsafeCoerce
#endif

#ifdef __GLASGOW_HASKELL__
type Any = GHC.Base.Any
#else
-- HUGS
type Any = ()
#endif

__ :: any
__ = Prelude.error "Logical or arity value used"

false_rect :: a1
false_rect =
  Prelude.error "absurd case"

and_rect :: (() -> () -> a1) -> a1
and_rect f =
  f __ __

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec =
  eq_rect

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r =
  eq_rec

data Nat =
   O
 | S Nat

nat_rect :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rect f f0 n =
  case n of {
   O -> f;
   S n0 -> f0 n0 (nat_rect f f0 n0)}

data Option a =
   Some a
 | None

option_rect :: (a1 -> a2) -> a2 -> (Option a1) -> a2
option_rect f f0 o =
  case o of {
   Some x -> f x;
   None -> f0}

data Prod a b =
   Pair a b

prod_rect :: (a1 -> a2 -> a3) -> (Prod a1 a2) -> a3
prod_rect f p =
  case p of {
   Pair x x0 -> f x x0}

fst :: (Prod a1 a2) -> a1
fst p =
  case p of {
   Pair x _ -> x}

snd :: (Prod a1 a2) -> a2
snd p =
  case p of {
   Pair _ y -> y}

data List a =
   Nil
 | Cons a (List a)

list_rect :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rect f f0 l =
  case l of {
   Nil -> f;
   Cons y l0 -> f0 y l0 (list_rect f f0 l0)}

list_rec :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rec =
  list_rect

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
data Sumbool =
   Left
 | Right

sumbool_rect :: (() -> a1) -> (() -> a1) -> Sumbool -> a1
sumbool_rect f f0 s =
  case s of {
   Left -> f __;
   Right -> f0 __}

data Sumor a =
   Inleft a
 | Inright

sumor_rect :: (a1 -> a2) -> (() -> a2) -> (Sumor a1) -> a2
sumor_rect f f0 s =
  case s of {
   Inleft x -> f x;
   Inright -> f0 __}

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

max :: Nat -> Nat -> Nat
max n m =
  case n of {
   O -> m;
   S n' -> case m of {
            O -> n;
            S m' -> S (max n' m')}}

in_dec :: (a1 -> a1 -> Sumbool) -> a1 -> (List a1) -> Sumbool
in_dec h a l =
  list_rec Right (\a0 _ iHl ->
    let {s = h a0 a} in case s of {
                         Left -> Left;
                         Right -> iHl}) l

type Set a = List a

set_add :: (a1 -> a1 -> Sumbool) -> a1 -> (Set a1) -> Set a1
set_add aeq_dec a x =
  case x of {
   Nil -> Cons a Nil;
   Cons a1 x1 ->
    case aeq_dec a a1 of {
     Left -> Cons a1 x1;
     Right -> Cons a1 (set_add aeq_dec a x1)}}

set_union :: (a1 -> a1 -> Sumbool) -> (Set a1) -> (Set a1) -> Set a1
set_union aeq_dec x y =
  case y of {
   Nil -> x;
   Cons a1 y1 -> set_add aeq_dec a1 (set_union aeq_dec x y1)}

type DecType =
  Any -> Any -> Sumbool
  -- singleton inductive, whose constructor was Build_DecType
  
type T = Any

eq_dec :: DecType -> T -> T -> Sumbool
eq_dec d =
  d

dP_eq_dec :: DecType -> DecType -> (Prod T T) -> (Prod T T) -> Sumbool
dP_eq_dec a b p1 p2 =
  case p1 of {
   Pair x p ->
    case p2 of {
     Pair y q ->
      case eq_dec b p q of {
       Left ->
        case eq_dec a x y of {
         Left -> eq_rec_r y (eq_rec_r q Left p) x;
         Right -> Right};
       Right -> Right}}}

decProd :: DecType -> DecType -> DecType
decProd a b =
  unsafeCoerce dP_eq_dec a b

data Label =
   Left0
 | Right0

label_rect :: a1 -> a1 -> Label -> a1
label_rect f f0 l =
  case l of {
   Left0 -> f;
   Right0 -> f0}

label_rec :: a1 -> a1 -> Label -> a1
label_rec =
  label_rect

eq_label_dec :: Label -> Label -> Sumbool
eq_label_dec l l' =
  label_rec (\x -> case x of {
                    Left0 -> Left;
                    Right0 -> Right}) (\x ->
    case x of {
     Left0 -> Right;
     Right0 -> Left}) l l'

label :: DecType
label =
  unsafeCoerce eq_label_dec

type Eval =
  T -> (T -> T) -> T
  -- singleton inductive, whose constructor was Build_Eval
  
data Signature =
   Build_Signature DecType DecType DecType DecType DecType DecType DecType 
 Eval Eval

pid :: Signature -> DecType
pid s =
  case s of {
   Build_Signature pid0 _ _ _ _ _ _ _ _ -> pid0}

var :: Signature -> DecType
var s =
  case s of {
   Build_Signature _ var0 _ _ _ _ _ _ _ -> var0}

value :: Signature -> DecType
value s =
  case s of {
   Build_Signature _ _ value0 _ _ _ _ _ _ -> value0}

expr :: Signature -> DecType
expr s =
  case s of {
   Build_Signature _ _ _ expr0 _ _ _ _ _ -> expr0}

bexpr :: Signature -> DecType
bexpr s =
  case s of {
   Build_Signature _ _ _ _ bexpr0 _ _ _ _ -> bexpr0}

recvar :: Signature -> DecType
recvar s =
  case s of {
   Build_Signature _ _ _ _ _ recvar0 _ _ _ -> recvar0}

ann :: Signature -> DecType
ann s =
  case s of {
   Build_Signature _ _ _ _ _ _ ann0 _ _ -> ann0}

ev :: Signature -> Eval
ev s =
  case s of {
   Build_Signature _ _ _ _ _ _ _ ev0 _ -> ev0}

bev :: Signature -> Eval
bev s =
  case s of {
   Build_Signature _ _ _ _ _ _ _ _ bev0 -> bev0}

data Eta =
   Com T T T T
 | Sel T T T

eta_rect :: Signature -> (T -> T -> T -> T -> a1) -> (T -> T -> T -> a1) ->
            Eta -> a1
eta_rect _ f f0 e =
  case e of {
   Com x x0 x1 x2 -> f x x0 x1 x2;
   Sel x x0 x1 -> f0 x x0 x1}

data Choreography =
   Interaction Eta T Choreography
 | Cond T T Choreography Choreography
 | Call T
 | RT_Call T (List T) Choreography
 | End

choreography_rect :: Signature -> (Eta -> T -> Choreography -> a1 -> a1) ->
                     (T -> T -> Choreography -> a1 -> Choreography -> a1 ->
                     a1) -> (T -> a1) -> (T -> (List T) -> Choreography -> a1
                     -> a1) -> a1 -> Choreography -> a1
choreography_rect sig f f0 f1 f2 f3 c =
  case c of {
   Interaction e t c0 -> f e t c0 (choreography_rect sig f f0 f1 f2 f3 c0);
   Cond t t0 c0 c1 ->
    f0 t t0 c0 (choreography_rect sig f f0 f1 f2 f3 c0) c1
      (choreography_rect sig f f0 f1 f2 f3 c1);
   Call t -> f1 t;
   RT_Call t l c0 -> f2 t l c0 (choreography_rect sig f f0 f1 f2 f3 c0);
   End -> f3}

type DefSet = T -> Prod (List T) Choreography

type Program = Prod DefSet Choreography

procedures :: Signature -> Program -> DefSet
procedures _ =
  fst

main :: Signature -> Program -> Choreography
main _ =
  snd

vars :: Signature -> Program -> T -> List T
vars sig p x =
  fst (procedures sig p x)

eta_pn :: Signature -> Eta -> List T
eta_pn _ e =
  case e of {
   Com p _ q _ -> Cons p (Cons q Nil);
   Sel p q _ -> Cons p (Cons q Nil)}

cCC_pn :: Signature -> Choreography -> (T -> List T) -> List T
cCC_pn sig c pids =
  case c of {
   Interaction eta _ c' ->
    set_union (eq_dec (pid sig)) (eta_pn sig eta) (cCC_pn sig c' pids);
   Cond p _ c1 c2 ->
    set_union (eq_dec (pid sig))
      (set_union (eq_dec (pid sig)) (Cons p Nil) (cCC_pn sig c1 pids))
      (cCC_pn sig c2 pids);
   Call x -> pids x;
   RT_Call _ l c' -> set_union (eq_dec (pid sig)) l (cCC_pn sig c' pids);
   End -> Nil}

cCP_pn :: Signature -> Program -> List T
cCP_pn sig p =
  cCC_pn sig (main sig p) (vars sig p)

data Behaviour =
   End0
 | Send T T T Behaviour
 | Recv T T T Behaviour
 | Sel0 T T T Behaviour
 | Branching T (Option (Prod T Behaviour)) (Option (Prod T Behaviour))
 | Cond0 T Behaviour Behaviour
 | Call0 T

depth :: Signature -> Behaviour -> Nat
depth sig b =
  case b of {
   Send _ _ _ b' -> add (S O) (depth sig b');
   Recv _ _ _ b' -> add (S O) (depth sig b');
   Sel0 _ _ _ b' -> add (S O) (depth sig b');
   Branching _ mB mB' ->
    add
      (add (S O)
        (case mB of {
          Some p0 -> case p0 of {
                      Pair _ b0 -> depth sig b0};
          None -> O}))
      (case mB' of {
        Some p0 -> case p0 of {
                    Pair _ b0 -> depth sig b0};
        None -> O});
   Cond0 _ b1 b2 -> add (S O) (max (depth sig b1) (depth sig b2));
   _ -> S O}

behaviour_rec' :: Signature -> a1 -> (T -> T -> T -> Behaviour -> a1 -> a1)
                  -> (T -> T -> T -> Behaviour -> a1 -> a1) -> (T -> T -> T
                  -> Behaviour -> a1 -> a1) -> (T -> a1) -> (T -> T ->
                  Behaviour -> a1 -> a1) -> (T -> T -> Behaviour -> a1 -> a1)
                  -> (T -> T -> Behaviour -> T -> Behaviour -> a1 -> a1 ->
                  a1) -> (T -> Behaviour -> Behaviour -> a1 -> a1 -> a1) ->
                  (T -> a1) -> Behaviour -> a1
behaviour_rec' sig x x0 x1 x2 x3 x4 x5 x6 x7 x8 b =
  let {d = depth sig b} in
  nat_rect (\b0 _ ->
    case b0 of {
     End0 -> x;
     Call0 t -> x8 t;
     _ -> false_rect}) (\_ iHd b0 _ ->
    case b0 of {
     End0 -> x;
     Send t t0 t1 b1 -> x0 t t0 t1 b1 (iHd b1 __);
     Recv t t0 t1 b1 -> x1 t t0 t1 b1 (iHd b1 __);
     Sel0 t t0 t1 b1 -> x2 t t0 t1 b1 (iHd b1 __);
     Branching t o o0 ->
      option_rect (\a _ _ ->
        option_rect (\a0 _ _ ->
          prod_rect (\a1 b1 _ _ ->
            prod_rect (\a2 b2 _ _ ->
              x6 t a1 b1 a2 b2 (iHd b1 __) (iHd b2 __)) a0 __ __) a __ __)
          (\_ _ -> prod_rect (\a0 b1 _ _ -> x4 t a0 b1 (iHd b1 __)) a __ __)
          o0 __ __) (\_ _ ->
        option_rect (\a _ _ ->
          prod_rect (\a0 b1 _ _ -> x5 t a0 b1 (iHd b1 __)) a __ __) (\_ _ ->
          x3 t) o0 __ __) o __ __;
     Cond0 t b1 b2 -> x7 t b1 b2 (iHd b1 __) (iHd b2 __);
     Call0 t -> x8 t}) d b __

type Network = T -> Behaviour

type DefSetB = T -> Behaviour

type Program0 = Prod DefSetB Network

merge_dec :: Signature -> Behaviour -> Behaviour -> Sumor Behaviour
merge_dec sig b1 =
  behaviour_rec' sig (\b2 ->
    behaviour_rec' sig (Inleft End0) (\_ _ _ _ _ -> Inright) (\_ _ _ _ _ ->
      Inright) (\_ _ _ _ _ -> Inright) (\_ -> Inright) (\_ _ _ _ -> Inright)
      (\_ _ _ _ -> Inright) (\_ _ _ _ _ _ _ -> Inright) (\_ _ _ _ _ ->
      Inright) (\_ -> Inright) b2) (\p e a _ iHB1 b2 ->
    behaviour_rec' sig Inright (\p0 e0 a0 b3 _ ->
      case eq_dec (pid sig) p p0 of {
       Left ->
        eq_rect p
          (case eq_dec (expr sig) e e0 of {
            Left ->
             case eq_dec (ann sig) a a0 of {
              Left ->
               let {s = iHB1 b3} in
               sumor_rect (\a1 -> Inleft (Send p e a a1)) (\_ -> Inright) s;
              Right -> Inright};
            Right -> Inright}) p0;
       Right -> Inright}) (\_ _ _ _ _ -> Inright) (\_ _ _ _ _ -> Inright)
      (\_ -> Inright) (\_ _ _ _ -> Inright) (\_ _ _ _ -> Inright)
      (\_ _ _ _ _ _ _ -> Inright) (\_ _ _ _ _ -> Inright) (\_ -> Inright) b2)
    (\p v a _ iHB1 b2 ->
    behaviour_rec' sig Inright (\_ _ _ _ _ -> Inright) (\p0 v0 a0 b3 _ ->
      case eq_dec (pid sig) p p0 of {
       Left ->
        eq_rect p
          (case eq_dec (var sig) v v0 of {
            Left ->
             case eq_dec (ann sig) a a0 of {
              Left ->
               let {s = iHB1 b3} in
               sumor_rect (\a1 -> Inleft (Recv p v a a1)) (\_ -> Inright) s;
              Right -> Inright};
            Right -> Inright}) p0;
       Right -> Inright}) (\_ _ _ _ _ -> Inright) (\_ -> Inright)
      (\_ _ _ _ -> Inright) (\_ _ _ _ -> Inright) (\_ _ _ _ _ _ _ -> Inright)
      (\_ _ _ _ _ -> Inright) (\_ -> Inright) b2) (\p l a _ iHB1 b2 ->
    behaviour_rec' sig Inright (\_ _ _ _ _ -> Inright) (\_ _ _ _ _ ->
      Inright) (\p0 l0 a0 b3 _ ->
      case eq_dec (pid sig) p p0 of {
       Left ->
        eq_rect p
          (case eq_dec label l l0 of {
            Left ->
             case eq_dec (ann sig) a a0 of {
              Left ->
               let {s = iHB1 b3} in
               sumor_rect (\a1 -> Inleft (Sel0 p l a a1)) (\_ -> Inright) s;
              Right -> Inright};
            Right -> Inright}) p0;
       Right -> Inright}) (\_ -> Inright) (\_ _ _ _ -> Inright) (\_ _ _ _ ->
      Inright) (\_ _ _ _ _ _ _ -> Inright) (\_ _ _ _ _ -> Inright) (\_ ->
      Inright) b2) (\p b2 ->
    behaviour_rec' sig Inright (\_ _ _ _ _ -> Inright) (\_ _ _ _ _ ->
      Inright) (\_ _ _ _ _ -> Inright) (\p0 ->
      case eq_dec (pid sig) p p0 of {
       Left -> eq_rect p (Inleft (Branching p None None)) p0;
       Right -> Inright}) (\p0 a b3 _ ->
      case eq_dec (pid sig) p p0 of {
       Left -> eq_rect p (Inleft (Branching p (Some (Pair a b3)) None)) p0;
       Right -> Inright}) (\p0 a b3 _ ->
      case eq_dec (pid sig) p p0 of {
       Left -> eq_rect p (Inleft (Branching p None (Some (Pair a b3)))) p0;
       Right -> Inright}) (\p0 a b2_1 a' b2_2 _ _ ->
      case eq_dec (pid sig) p p0 of {
       Left ->
        eq_rect p (Inleft (Branching p (Some (Pair a b2_1)) (Some (Pair a'
          b2_2)))) p0;
       Right -> Inright}) (\_ _ _ _ _ -> Inright) (\_ -> Inright) b2)
    (\p a b2 iHB1 b3 ->
    behaviour_rec' sig Inright (\_ _ _ _ _ -> Inright) (\_ _ _ _ _ ->
      Inright) (\_ _ _ _ _ -> Inright) (\p0 ->
      case eq_dec (pid sig) p p0 of {
       Left -> eq_rect p (Inleft (Branching p (Some (Pair a b2)) None)) p0;
       Right -> Inright}) (\p0 a0 b4 _ ->
      case eq_dec (pid sig) p p0 of {
       Left ->
        eq_rect p
          (case eq_dec (ann sig) a a0 of {
            Left ->
             eq_rect a
               (let {s = iHB1 b4} in
                sumor_rect (\a1 -> Inleft (Branching p (Some (Pair a a1))
                  None)) (\_ -> Inright) s) a0;
            Right -> Inright}) p0;
       Right -> Inright}) (\p0 a0 b4 _ ->
      case eq_dec (pid sig) p p0 of {
       Left ->
        eq_rect p (Inleft (Branching p (Some (Pair a b2)) (Some (Pair a0
          b4)))) p0;
       Right -> Inright}) (\p0 a0 b2_1 a' b2_2 _ _ ->
      case eq_dec (pid sig) p p0 of {
       Left ->
        eq_rect p
          (case eq_dec (ann sig) a a0 of {
            Left ->
             eq_rect a
               (let {s = iHB1 b2_1} in
                sumor_rect (\a1 -> Inleft (Branching p (Some (Pair a a1))
                  (Some (Pair a' b2_2)))) (\_ -> Inright) s) a0;
            Right -> Inright}) p0;
       Right -> Inright}) (\_ _ _ _ _ -> Inright) (\_ -> Inright) b3)
    (\p a b2 iHB1 b3 ->
    behaviour_rec' sig Inright (\_ _ _ _ _ -> Inright) (\_ _ _ _ _ ->
      Inright) (\_ _ _ _ _ -> Inright) (\p0 ->
      case eq_dec (pid sig) p p0 of {
       Left -> eq_rect p (Inleft (Branching p None (Some (Pair a b2)))) p0;
       Right -> Inright}) (\p0 a0 b4 _ ->
      case eq_dec (pid sig) p p0 of {
       Left ->
        eq_rect p (Inleft (Branching p (Some (Pair a0 b4)) (Some (Pair a
          b2)))) p0;
       Right -> Inright}) (\p0 a0 b4 _ ->
      case eq_dec (pid sig) p p0 of {
       Left ->
        eq_rect p
          (case eq_dec (ann sig) a a0 of {
            Left ->
             eq_rect a
               (let {s = iHB1 b4} in
                sumor_rect (\a1 -> Inleft (Branching p None (Some (Pair a
                  a1)))) (\_ -> Inright) s) a0;
            Right -> Inright}) p0;
       Right -> Inright}) (\p0 a0 b2_1 a' b2_2 _ _ ->
      case eq_dec (pid sig) p p0 of {
       Left ->
        eq_rect p
          (case eq_dec (ann sig) a a' of {
            Left ->
             eq_rect a
               (let {s = iHB1 b2_2} in
                sumor_rect (\a1 -> Inleft (Branching p (Some (Pair a0 b2_1))
                  (Some (Pair a a1)))) (\_ -> Inright) s) a';
            Right -> Inright}) p0;
       Right -> Inright}) (\_ _ _ _ _ -> Inright) (\_ -> Inright) b3)
    (\p a b1_1 a' b1_2 iHB1_1 iHB1_2 b2 ->
    behaviour_rec' sig Inright (\_ _ _ _ _ -> Inright) (\_ _ _ _ _ ->
      Inright) (\_ _ _ _ _ -> Inright) (\p0 ->
      case eq_dec (pid sig) p p0 of {
       Left ->
        eq_rect p (Inleft (Branching p (Some (Pair a b1_1)) (Some (Pair a'
          b1_2)))) p0;
       Right -> Inright}) (\p0 a0 b3 _ ->
      case eq_dec (pid sig) p p0 of {
       Left ->
        eq_rect p
          (case eq_dec (ann sig) a a0 of {
            Left ->
             eq_rect a
               (let {s = iHB1_1 b3} in
                sumor_rect (\a1 -> Inleft (Branching p (Some (Pair a a1))
                  (Some (Pair a' b1_2)))) (\_ -> Inright) s) a0;
            Right -> Inright}) p0;
       Right -> Inright}) (\p0 a0 b3 _ ->
      case eq_dec (pid sig) p p0 of {
       Left ->
        eq_rect p
          (case eq_dec (ann sig) a' a0 of {
            Left ->
             eq_rect a'
               (let {s = iHB1_2 b3} in
                sumor_rect (\a1 -> Inleft (Branching p (Some (Pair a b1_1))
                  (Some (Pair a' a1)))) (\_ -> Inright) s) a0;
            Right -> Inright}) p0;
       Right -> Inright}) (\p0 a0 b2_1 a'0 b2_2 _ _ ->
      case eq_dec (pid sig) p p0 of {
       Left ->
        eq_rect p
          (case eq_dec (ann sig) a a0 of {
            Left ->
             eq_rect a
               (case eq_dec (ann sig) a' a'0 of {
                 Left ->
                  eq_rect a'
                    (let {s = iHB1_1 b2_1} in
                     sumor_rect (\a1 ->
                       let {s0 = iHB1_2 b2_2} in
                       sumor_rect (\a2 -> Inleft (Branching p (Some (Pair a
                         a1)) (Some (Pair a' a2)))) (\_ -> Inright) s0)
                       (\_ -> Inright) s) a'0;
                 Right -> Inright}) a0;
            Right -> Inright}) p0;
       Right -> Inright}) (\_ _ _ _ _ -> Inright) (\_ -> Inright) b2)
    (\b _ _ iHB1_1 iHB1_2 b2 ->
    behaviour_rec' sig Inright (\_ _ _ _ _ -> Inright) (\_ _ _ _ _ ->
      Inright) (\_ _ _ _ _ -> Inright) (\_ -> Inright) (\_ _ _ _ -> Inright)
      (\_ _ _ _ -> Inright) (\_ _ _ _ _ _ _ -> Inright) (\b0 b2_1 b2_2 _ _ ->
      case eq_dec (bexpr sig) b b0 of {
       Left ->
        eq_rect b
          (let {s = iHB1_1 b2_1} in
           sumor_rect (\a ->
             let {s0 = iHB1_2 b2_2} in
             sumor_rect (\a0 -> Inleft (Cond0 b a a0)) (\_ -> Inright) s0)
             (\_ -> Inright) s) b0;
       Right -> Inright}) (\_ -> Inright) b2) (\x b2 ->
    behaviour_rec' sig Inright (\_ _ _ _ _ -> Inright) (\_ _ _ _ _ ->
      Inright) (\_ _ _ _ _ -> Inright) (\_ -> Inright) (\_ _ _ _ -> Inright)
      (\_ _ _ _ -> Inright) (\_ _ _ _ _ _ _ -> Inright) (\_ _ _ _ _ ->
      Inright) (\x0 ->
      case eq_dec (recvar sig) x x0 of {
       Left -> Inleft (Call0 x);
       Right -> Inright}) b2) b1

sig' :: Signature -> Signature
sig' sig =
  Build_Signature (pid sig) (var sig) (value sig) (expr sig) (bexpr sig)
    (decProd (recvar sig) (pid sig)) (ann sig) (ev sig) (bev sig)

bproj_dec :: Signature -> DefSet -> Choreography -> T -> Sumor Behaviour
bproj_dec sig d c =
  choreography_rect sig (\e t _ iHC ->
    eta_rect sig (\t0 t1 t2 t3 p ->
      let {s = iHC p} in
      sumor_rect (\a ->
        case eq_dec (pid sig) p t0 of {
         Left -> eq_rect p (Inleft (Send t2 t1 t a)) t0;
         Right ->
          case eq_dec (pid sig) p t2 of {
           Left -> eq_rect p (Inleft (Recv t0 t3 t a)) t2;
           Right -> Inleft a}}) (\_ -> Inright) s) (\t0 t1 t2 p ->
      let {s = iHC p} in
      sumor_rect (\a ->
        case eq_dec (pid sig) p t0 of {
         Left -> eq_rect p (Inleft (Sel0 t1 t2 t a)) t0;
         Right ->
          case eq_dec (pid sig) p t1 of {
           Left ->
            eq_rect p
              (label_rect (Inleft (Branching t0 (Some (Pair t a)) None))
                (Inleft (Branching t0 None (Some (Pair t a))))
                (unsafeCoerce t2)) t1;
           Right -> Inleft a}}) (\_ -> Inright) s) e)
    (\t t0 _ iHC1 _ iHC2 p ->
    let {s = iHC1 p} in
    sumor_rect (\a ->
      let {s0 = iHC2 p} in
      sumor_rect (\a0 ->
        case eq_dec (pid sig) p t of {
         Left -> eq_rect p (Inleft (Cond0 t0 a a0)) t;
         Right ->
          let {s1 = merge_dec (sig' sig) a a0} in
          sumor_rect (\a1 -> Inleft a1) (\_ -> Inright) s1}) (\_ -> Inright)
        s0) (\_ -> Inright) s) (\t p ->
    sumbool_rect (\_ -> Inleft (Call0 (unsafeCoerce (Pair t p)))) (\_ ->
      Inleft End0) (in_dec (eq_dec (pid sig)) p (fst (d t))))
    (\t l _ iHC p ->
    sumbool_rect (\_ -> Inleft (Call0 (unsafeCoerce (Pair t p))))
      (let {s = iHC p} in sumor_rect (\a _ -> Inleft a) (\_ _ -> Inright) s)
      (in_dec (eq_dec (pid sig)) p l)) (\_ -> Inleft End0) c

epp_C :: Signature -> DefSet -> (List T) -> Choreography -> Network
epp_C sig d ps c p =
  sumbool_rect (\_ ->
    let {s = bproj_dec sig d c p} in
    sumor_rect (\a -> a) (\_ -> false_rect) s) (\_ -> End0)
    (in_dec (eq_dec (pid sig)) p ps)

epp_D :: Signature -> DefSet -> DefSetB
epp_D sig d x =
  case unsafeCoerce x of {
   Pair r p ->
    sumbool_rect
      (let {s = bproj_dec sig d (snd (d r)) p} in
       sumor_rect (\a _ -> a) (\_ _ -> false_rect) s) (\_ -> End0)
      (in_dec (eq_dec (pid sig)) p (fst (d r)))}

epp :: Signature -> Program -> Program0
epp sig p =
  and_rect (\_ _ -> Pair (epp_D sig (procedures sig p))
    (epp_C sig (procedures sig p) (cCP_pn sig p) (main sig p)))

