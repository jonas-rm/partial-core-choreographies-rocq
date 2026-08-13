
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type unit0 =
| Tt

type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

type 'a sumor =
| Inleft of 'a
| Inright

(** val add : nat -> nat -> nat **)

let rec add n m =
  match n with
  | O -> m
  | S p -> S (add p m)

(** val bool_dec : bool -> bool -> sumbool **)

let bool_dec b1 b2 =
  match b1 with
  | True -> (match b2 with
             | True -> Left
             | False -> Right)
  | False -> (match b2 with
              | True -> Right
              | False -> Left)

module Nat =
 struct
  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')

  (** val max : nat -> nat -> nat **)

  let rec max n m =
    match n with
    | O -> m
    | S n' -> (match m with
               | O -> n
               | S m' -> S (max n' m'))

  (** val eq_dec : nat -> nat -> sumbool **)

  let rec eq_dec n m =
    match n with
    | O -> (match m with
            | O -> Left
            | S _ -> Right)
    | S n0 -> (match m with
               | O -> Right
               | S m0 -> eq_dec n0 m0)
 end

(** val in_dec : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 list -> sumbool **)

let rec in_dec h a = function
| Nil -> Right
| Cons (y, l0) ->
  let s = h y a in (match s with
                    | Left -> Left
                    | Right -> in_dec h a l0)

type 'a set = 'a list

(** val set_add : ('a1 -> 'a1 -> sumbool) -> 'a1 -> 'a1 set -> 'a1 set **)

let rec set_add aeq_dec a = function
| Nil -> Cons (a, Nil)
| Cons (a1, x1) ->
  (match aeq_dec a a1 with
   | Left -> Cons (a1, x1)
   | Right -> Cons (a1, (set_add aeq_dec a x1)))

(** val set_union :
    ('a1 -> 'a1 -> sumbool) -> 'a1 set -> 'a1 set -> 'a1 set **)

let rec set_union aeq_dec x = function
| Nil -> x
| Cons (a1, y1) -> set_add aeq_dec a1 (set_union aeq_dec x y1)

type decType =
  __ -> __ -> sumbool
  (* singleton inductive, whose constructor was Build_DecType *)

type t = __

(** val eq_dec0 : decType -> t -> t -> sumbool **)

let eq_dec0 d =
  d

(** val unit_dec : unit0 -> unit0 -> sumbool **)

let unit_dec _ _ =
  Left

(** val unit1 : decType **)

let unit1 =
  Obj.magic unit_dec

(** val dP_eq_dec :
    decType -> decType -> (t, t) prod -> (t, t) prod -> sumbool **)

let dP_eq_dec a b p1 p2 =
  let Pair (x, p) = p1 in
  let Pair (y, q) = p2 in
  (match eq_dec0 b p q with
   | Left -> eq_dec0 a x y
   | Right -> Right)

(** val decProd : decType -> decType -> decType **)

let decProd a b =
  Obj.magic dP_eq_dec a b

(** val bool0 : decType **)

let bool0 =
  Obj.magic bool_dec

type label =
| Left0
| Right0

(** val eq_label_dec : label -> label -> sumbool **)

let eq_label_dec l l' =
  match l with
  | Left0 -> (match l' with
              | Left0 -> Left
              | Right0 -> Right)
  | Right0 -> (match l' with
               | Left0 -> Right
               | Right0 -> Left)

(** val label0 : decType **)

let label0 =
  Obj.magic eq_label_dec

type eval =
  t -> (t -> t) -> t
  (* singleton inductive, whose constructor was Build_Eval *)

type signature = { pid : decType; var : decType; value : decType;
                   expr : decType; bexpr : decType; recvar : decType;
                   ann : decType; ev : eval; bev : eval }

type eta =
| Com of t * t * t * t
| Sel of t * t * t

type choreography =
| Interaction of eta * t * choreography
| Cond of t * t * choreography * choreography
| Call of t
| RT_Call of t * t list * choreography
| End

type defSet = t -> (t list, choreography) prod

type program = (defSet, choreography) prod

(** val procedures : signature -> program -> defSet **)

let procedures _ =
  fst

(** val main : signature -> program -> choreography **)

let main _ =
  snd

(** val vars : signature -> program -> t -> t list **)

let vars sig2 p x =
  fst (procedures sig2 p x)

(** val eta_pn : signature -> eta -> t list **)

let eta_pn _ = function
| Com (p, _, q, _) -> Cons (p, (Cons (q, Nil)))
| Sel (p, q, _) -> Cons (p, (Cons (q, Nil)))

(** val cCC_pn : signature -> choreography -> (t -> t list) -> t list **)

let rec cCC_pn sig2 c pids =
  match c with
  | Interaction (eta0, _, c') ->
    set_union (eq_dec0 sig2.pid) (eta_pn sig2 eta0) (cCC_pn sig2 c' pids)
  | Cond (p, _, c1, c2) ->
    set_union (eq_dec0 sig2.pid)
      (set_union (eq_dec0 sig2.pid) (Cons (p, Nil)) (cCC_pn sig2 c1 pids))
      (cCC_pn sig2 c2 pids)
  | Call x -> pids x
  | RT_Call (_, l, c') -> set_union (eq_dec0 sig2.pid) l (cCC_pn sig2 c' pids)
  | End -> Nil

(** val cCP_pn : signature -> program -> t list **)

let cCP_pn sig2 p =
  cCC_pn sig2 (main sig2 p) (vars sig2 p)

type expr0 =
| This
| Zero
| Succ_this

(** val expr_eq_dec : expr0 -> expr0 -> sumbool **)

let expr_eq_dec e e' =
  match e with
  | This -> (match e' with
             | This -> Left
             | _ -> Right)
  | Zero -> (match e' with
             | Zero -> Left
             | _ -> Right)
  | Succ_this -> (match e' with
                  | Succ_this -> Left
                  | _ -> Right)

(** val bExpr_eq_dec : __ -> sumbool **)

let bExpr_eq_dec _ =
  Left

(** val cC_Expressions : decType **)

let cC_Expressions =
  Obj.magic expr_eq_dec

(** val bool_Expressions : decType **)

let bool_Expressions =
  Obj.magic (fun _ -> bExpr_eq_dec)

(** val cC_Nat : decType **)

let cC_Nat =
  Obj.magic Nat.eq_dec

(** val eval0 : expr0 -> (bool -> nat) -> nat **)

let eval0 e f =
  match e with
  | This -> f True
  | Zero -> O
  | Succ_this -> S (f True)

(** val cC_Eval : eval **)

let cC_Eval =
  Obj.magic eval0

(** val beval : (bool -> nat) -> bool **)

let beval f =
  Nat.eqb (f True) (f False)

(** val cC_BEval : eval **)

let cC_BEval =
  Obj.magic (fun _ -> beval)

type behaviour =
| End0
| Send of t * t * t * behaviour
| Recv of t * t * t * behaviour
| Sel0 of t * t * t * behaviour
| Branching of t * (t, behaviour) prod option * (t, behaviour) prod option
| Cond0 of t * behaviour * behaviour
| Call0 of t

(** val depth : signature -> behaviour -> nat **)

let rec depth sig2 = function
| Send (_, _, _, b') -> add (S O) (depth sig2 b')
| Recv (_, _, _, b') -> add (S O) (depth sig2 b')
| Sel0 (_, _, _, b') -> add (S O) (depth sig2 b')
| Branching (_, mB, mB') ->
  add
    (add (S O)
      (match mB with
       | Some p0 -> let Pair (_, b0) = p0 in depth sig2 b0
       | None -> O))
    (match mB' with
     | Some p0 -> let Pair (_, b0) = p0 in depth sig2 b0
     | None -> O)
| Cond0 (_, b1, b2) -> add (S O) (Nat.max (depth sig2 b1) (depth sig2 b2))
| _ -> S O

(** val behaviour_rec' :
    signature -> 'a1 -> (t -> t -> t -> behaviour -> 'a1 -> 'a1) -> (t -> t
    -> t -> behaviour -> 'a1 -> 'a1) -> (t -> t -> t -> behaviour -> 'a1 ->
    'a1) -> (t -> 'a1) -> (t -> t -> behaviour -> 'a1 -> 'a1) -> (t -> t ->
    behaviour -> 'a1 -> 'a1) -> (t -> t -> behaviour -> t -> behaviour -> 'a1
    -> 'a1 -> 'a1) -> (t -> behaviour -> behaviour -> 'a1 -> 'a1 -> 'a1) ->
    (t -> 'a1) -> behaviour -> 'a1 **)

let behaviour_rec' sig2 x x0 x1 x2 x3 x4 x5 x6 x7 x8 b =
  let d = depth sig2 b in
  let rec f = function
  | O ->
    (fun b0 _ ->
      match b0 with
      | End0 -> x
      | Call0 t0 -> x8 t0
      | _ -> assert false (* absurd case *))
  | S n0 ->
    let iHd = f n0 in
    (fun b0 _ ->
    match b0 with
    | End0 -> x
    | Send (t0, t1, t2, b1) -> x0 t0 t1 t2 b1 (iHd b1 __)
    | Recv (t0, t1, t2, b1) -> x1 t0 t1 t2 b1 (iHd b1 __)
    | Sel0 (t0, t1, t2, b1) -> x2 t0 t1 t2 b1 (iHd b1 __)
    | Branching (t0, o, o0) ->
      (match o with
       | Some x9 ->
         (match o0 with
          | Some x10 ->
            let Pair (x11, x12) = x9 in
            let Pair (x13, x14) = x10 in
            x6 t0 x11 x12 x13 x14 (iHd x12 __) (iHd x14 __)
          | None -> let Pair (x10, x11) = x9 in x4 t0 x10 x11 (iHd x11 __))
       | None ->
         (match o0 with
          | Some x9 -> let Pair (x10, x11) = x9 in x5 t0 x10 x11 (iHd x11 __)
          | None -> x3 t0))
    | Cond0 (t0, b1, b2) -> x7 t0 b1 b2 (iHd b1 __) (iHd b2 __)
    | Call0 t0 -> x8 t0)
  in f d b __

type network = t -> behaviour

type defSetB = t -> behaviour

type program0 = (defSetB, network) prod

(** val merge_dec : signature -> behaviour -> behaviour -> behaviour sumor **)

let merge_dec sig2 b1 =
  behaviour_rec' sig2 (fun b2 ->
    behaviour_rec' sig2 (Inleft End0) (fun _ _ _ _ _ -> Inright)
      (fun _ _ _ _ _ -> Inright) (fun _ _ _ _ _ -> Inright) (fun _ ->
      Inright) (fun _ _ _ _ -> Inright) (fun _ _ _ _ -> Inright)
      (fun _ _ _ _ _ _ _ -> Inright) (fun _ _ _ _ _ -> Inright) (fun _ ->
      Inright) b2) (fun p e a _ iHB1 b2 ->
    behaviour_rec' sig2 Inright (fun p0 e0 a0 b3 _ ->
      match eq_dec0 sig2.pid p p0 with
      | Left ->
        (match eq_dec0 sig2.expr e e0 with
         | Left ->
           (match eq_dec0 sig2.ann a a0 with
            | Left ->
              let s = iHB1 b3 in
              (match s with
               | Inleft x -> Inleft (Send (p, e, a, x))
               | Inright -> Inright)
            | Right -> Inright)
         | Right -> Inright)
      | Right -> Inright) (fun _ _ _ _ _ -> Inright) (fun _ _ _ _ _ ->
      Inright) (fun _ -> Inright) (fun _ _ _ _ -> Inright) (fun _ _ _ _ ->
      Inright) (fun _ _ _ _ _ _ _ -> Inright) (fun _ _ _ _ _ -> Inright)
      (fun _ -> Inright) b2) (fun p v a _ iHB1 b2 ->
    behaviour_rec' sig2 Inright (fun _ _ _ _ _ -> Inright)
      (fun p0 v0 a0 b3 _ ->
      match eq_dec0 sig2.pid p p0 with
      | Left ->
        (match eq_dec0 sig2.var v v0 with
         | Left ->
           (match eq_dec0 sig2.ann a a0 with
            | Left ->
              let s = iHB1 b3 in
              (match s with
               | Inleft x -> Inleft (Recv (p, v, a, x))
               | Inright -> Inright)
            | Right -> Inright)
         | Right -> Inright)
      | Right -> Inright) (fun _ _ _ _ _ -> Inright) (fun _ -> Inright)
      (fun _ _ _ _ -> Inright) (fun _ _ _ _ -> Inright) (fun _ _ _ _ _ _ _ ->
      Inright) (fun _ _ _ _ _ -> Inright) (fun _ -> Inright) b2)
    (fun p l a _ iHB1 b2 ->
    behaviour_rec' sig2 Inright (fun _ _ _ _ _ -> Inright) (fun _ _ _ _ _ ->
      Inright) (fun p0 l0 a0 b3 _ ->
      match eq_dec0 sig2.pid p p0 with
      | Left ->
        (match eq_dec0 label0 l l0 with
         | Left ->
           (match eq_dec0 sig2.ann a a0 with
            | Left ->
              let s = iHB1 b3 in
              (match s with
               | Inleft x -> Inleft (Sel0 (p, l, a, x))
               | Inright -> Inright)
            | Right -> Inright)
         | Right -> Inright)
      | Right -> Inright) (fun _ -> Inright) (fun _ _ _ _ -> Inright)
      (fun _ _ _ _ -> Inright) (fun _ _ _ _ _ _ _ -> Inright)
      (fun _ _ _ _ _ -> Inright) (fun _ -> Inright) b2) (fun p b2 ->
    behaviour_rec' sig2 Inright (fun _ _ _ _ _ -> Inright) (fun _ _ _ _ _ ->
      Inright) (fun _ _ _ _ _ -> Inright) (fun p0 ->
      match eq_dec0 sig2.pid p p0 with
      | Left -> Inleft (Branching (p, None, None))
      | Right -> Inright) (fun p0 a b3 _ ->
      match eq_dec0 sig2.pid p p0 with
      | Left -> Inleft (Branching (p, (Some (Pair (a, b3))), None))
      | Right -> Inright) (fun p0 a b3 _ ->
      match eq_dec0 sig2.pid p p0 with
      | Left -> Inleft (Branching (p, None, (Some (Pair (a, b3)))))
      | Right -> Inright) (fun p0 a b2_1 a' b2_2 _ _ ->
      match eq_dec0 sig2.pid p p0 with
      | Left ->
        Inleft (Branching (p, (Some (Pair (a, b2_1))), (Some (Pair (a',
          b2_2)))))
      | Right -> Inright) (fun _ _ _ _ _ -> Inright) (fun _ -> Inright) b2)
    (fun p a b2 iHB1 b3 ->
    behaviour_rec' sig2 Inright (fun _ _ _ _ _ -> Inright) (fun _ _ _ _ _ ->
      Inright) (fun _ _ _ _ _ -> Inright) (fun p0 ->
      match eq_dec0 sig2.pid p p0 with
      | Left -> Inleft (Branching (p, (Some (Pair (a, b2))), None))
      | Right -> Inright) (fun p0 a0 b4 _ ->
      match eq_dec0 sig2.pid p p0 with
      | Left ->
        (match eq_dec0 sig2.ann a a0 with
         | Left ->
           let s = iHB1 b4 in
           (match s with
            | Inleft x -> Inleft (Branching (p, (Some (Pair (a, x))), None))
            | Inright -> Inright)
         | Right -> Inright)
      | Right -> Inright) (fun p0 a0 b4 _ ->
      match eq_dec0 sig2.pid p p0 with
      | Left ->
        Inleft (Branching (p, (Some (Pair (a, b2))), (Some (Pair (a0, b4)))))
      | Right -> Inright) (fun p0 a0 b2_1 a' b2_2 _ _ ->
      match eq_dec0 sig2.pid p p0 with
      | Left ->
        (match eq_dec0 sig2.ann a a0 with
         | Left ->
           let s = iHB1 b2_1 in
           (match s with
            | Inleft x ->
              Inleft (Branching (p, (Some (Pair (a, x))), (Some (Pair (a',
                b2_2)))))
            | Inright -> Inright)
         | Right -> Inright)
      | Right -> Inright) (fun _ _ _ _ _ -> Inright) (fun _ -> Inright) b3)
    (fun p a b2 iHB1 b3 ->
    behaviour_rec' sig2 Inright (fun _ _ _ _ _ -> Inright) (fun _ _ _ _ _ ->
      Inright) (fun _ _ _ _ _ -> Inright) (fun p0 ->
      match eq_dec0 sig2.pid p p0 with
      | Left -> Inleft (Branching (p, None, (Some (Pair (a, b2)))))
      | Right -> Inright) (fun p0 a0 b4 _ ->
      match eq_dec0 sig2.pid p p0 with
      | Left ->
        Inleft (Branching (p, (Some (Pair (a0, b4))), (Some (Pair (a, b2)))))
      | Right -> Inright) (fun p0 a0 b4 _ ->
      match eq_dec0 sig2.pid p p0 with
      | Left ->
        (match eq_dec0 sig2.ann a a0 with
         | Left ->
           let s = iHB1 b4 in
           (match s with
            | Inleft x -> Inleft (Branching (p, None, (Some (Pair (a, x)))))
            | Inright -> Inright)
         | Right -> Inright)
      | Right -> Inright) (fun p0 a0 b2_1 a' b2_2 _ _ ->
      match eq_dec0 sig2.pid p p0 with
      | Left ->
        (match eq_dec0 sig2.ann a a' with
         | Left ->
           let s = iHB1 b2_2 in
           (match s with
            | Inleft x ->
              Inleft (Branching (p, (Some (Pair (a0, b2_1))), (Some (Pair (a,
                x)))))
            | Inright -> Inright)
         | Right -> Inright)
      | Right -> Inright) (fun _ _ _ _ _ -> Inright) (fun _ -> Inright) b3)
    (fun p a b1_1 a' b1_2 iHB1_1 iHB1_2 b2 ->
    behaviour_rec' sig2 Inright (fun _ _ _ _ _ -> Inright) (fun _ _ _ _ _ ->
      Inright) (fun _ _ _ _ _ -> Inright) (fun p0 ->
      match eq_dec0 sig2.pid p p0 with
      | Left ->
        Inleft (Branching (p, (Some (Pair (a, b1_1))), (Some (Pair (a',
          b1_2)))))
      | Right -> Inright) (fun p0 a0 b3 _ ->
      match eq_dec0 sig2.pid p p0 with
      | Left ->
        (match eq_dec0 sig2.ann a a0 with
         | Left ->
           let s = iHB1_1 b3 in
           (match s with
            | Inleft x ->
              Inleft (Branching (p, (Some (Pair (a, x))), (Some (Pair (a',
                b1_2)))))
            | Inright -> Inright)
         | Right -> Inright)
      | Right -> Inright) (fun p0 a0 b3 _ ->
      match eq_dec0 sig2.pid p p0 with
      | Left ->
        (match eq_dec0 sig2.ann a' a0 with
         | Left ->
           let s = iHB1_2 b3 in
           (match s with
            | Inleft x ->
              Inleft (Branching (p, (Some (Pair (a, b1_1))), (Some (Pair (a',
                x)))))
            | Inright -> Inright)
         | Right -> Inright)
      | Right -> Inright) (fun p0 a0 b2_1 a'0 b2_2 _ _ ->
      match eq_dec0 sig2.pid p p0 with
      | Left ->
        (match eq_dec0 sig2.ann a a0 with
         | Left ->
           (match eq_dec0 sig2.ann a' a'0 with
            | Left ->
              let s = iHB1_1 b2_1 in
              (match s with
               | Inleft x ->
                 let s0 = iHB1_2 b2_2 in
                 (match s0 with
                  | Inleft x0 ->
                    Inleft (Branching (p, (Some (Pair (a, x))), (Some (Pair
                      (a', x0)))))
                  | Inright -> Inright)
               | Inright -> Inright)
            | Right -> Inright)
         | Right -> Inright)
      | Right -> Inright) (fun _ _ _ _ _ -> Inright) (fun _ -> Inright) b2)
    (fun b _ _ iHB1_1 iHB1_2 b2 ->
    behaviour_rec' sig2 Inright (fun _ _ _ _ _ -> Inright) (fun _ _ _ _ _ ->
      Inright) (fun _ _ _ _ _ -> Inright) (fun _ -> Inright) (fun _ _ _ _ ->
      Inright) (fun _ _ _ _ -> Inright) (fun _ _ _ _ _ _ _ -> Inright)
      (fun b0 b2_1 b2_2 _ _ ->
      match eq_dec0 sig2.bexpr b b0 with
      | Left ->
        let s = iHB1_1 b2_1 in
        (match s with
         | Inleft x ->
           let s0 = iHB1_2 b2_2 in
           (match s0 with
            | Inleft x0 -> Inleft (Cond0 (b, x, x0))
            | Inright -> Inright)
         | Inright -> Inright)
      | Right -> Inright) (fun _ -> Inright) b2) (fun x b2 ->
    behaviour_rec' sig2 Inright (fun _ _ _ _ _ -> Inright) (fun _ _ _ _ _ ->
      Inright) (fun _ _ _ _ _ -> Inright) (fun _ -> Inright) (fun _ _ _ _ ->
      Inright) (fun _ _ _ _ -> Inright) (fun _ _ _ _ _ _ _ -> Inright)
      (fun _ _ _ _ _ -> Inright) (fun x0 ->
      match eq_dec0 sig2.recvar x x0 with
      | Left -> Inleft (Call0 x)
      | Right -> Inright) b2) b1

(** val sig' : signature -> signature **)

let sig' sig2 =
  { pid = sig2.pid; var = sig2.var; value = sig2.value; expr = sig2.expr;
    bexpr = sig2.bexpr; recvar = (decProd sig2.recvar sig2.pid); ann =
    sig2.ann; ev = sig2.ev; bev = sig2.bev }

(** val bproj_dec :
    signature -> defSet -> choreography -> t -> behaviour sumor **)

let rec bproj_dec sig2 d c p =
  match c with
  | Interaction (e, t0, c0) ->
    (match e with
     | Com (x, x0, x1, x2) ->
       let s = bproj_dec sig2 d c0 p in
       (match s with
        | Inleft x3 ->
          (match eq_dec0 sig2.pid p x with
           | Left -> Inleft (Send (x1, x0, t0, x3))
           | Right ->
             (match eq_dec0 sig2.pid p x1 with
              | Left -> Inleft (Recv (x, x2, t0, x3))
              | Right -> Inleft x3))
        | Inright -> Inright)
     | Sel (x, x0, x1) ->
       let s = bproj_dec sig2 d c0 p in
       (match s with
        | Inleft x2 ->
          (match eq_dec0 sig2.pid p x with
           | Left -> Inleft (Sel0 (x0, x1, t0, x2))
           | Right ->
             (match eq_dec0 sig2.pid p x0 with
              | Left ->
                (match Obj.magic x1 with
                 | Left0 ->
                   Inleft (Branching (x, (Some (Pair (t0, x2))), None))
                 | Right0 ->
                   Inleft (Branching (x, None, (Some (Pair (t0, x2))))))
              | Right -> Inleft x2))
        | Inright -> Inright))
  | Cond (t0, t1, c0, c1) ->
    let s = bproj_dec sig2 d c0 p in
    (match s with
     | Inleft x ->
       let s0 = bproj_dec sig2 d c1 p in
       (match s0 with
        | Inleft x0 ->
          (match eq_dec0 sig2.pid p t0 with
           | Left -> Inleft (Cond0 (t1, x, x0))
           | Right ->
             let s1 = merge_dec (sig' sig2) x x0 in
             (match s1 with
              | Inleft x1 -> Inleft x1
              | Inright -> Inright))
        | Inright -> Inright)
     | Inright -> Inright)
  | Call t0 ->
    (match in_dec (eq_dec0 sig2.pid) p (fst (d t0)) with
     | Left -> Inleft (Call0 (Obj.magic (Pair (t0, p))))
     | Right -> Inleft End0)
  | RT_Call (t0, l, c0) ->
    (match in_dec (eq_dec0 sig2.pid) p l with
     | Left -> Inleft (Call0 (Obj.magic (Pair (t0, p))))
     | Right ->
       let s = bproj_dec sig2 d c0 p in
       (match s with
        | Inleft x -> Inleft x
        | Inright -> Inright))
  | End -> Inleft End0

(** val epp_C : signature -> defSet -> t list -> choreography -> network **)

let epp_C sig2 d ps c p =
  match in_dec (eq_dec0 sig2.pid) p ps with
  | Left ->
    let s = bproj_dec sig2 d c p in
    (match s with
     | Inleft x -> x
     | Inright -> assert false (* absurd case *))
  | Right -> End0

(** val epp_D : signature -> defSet -> defSetB **)

let epp_D sig2 d x =
  let Pair (r, p) = Obj.magic x in
  (match in_dec (eq_dec0 sig2.pid) p (fst (d r)) with
   | Left ->
     let s = bproj_dec sig2 d (snd (d r)) p in
     (match s with
      | Inleft x0 -> x0
      | Inright -> assert false (* absurd case *))
   | Right -> End0)

(** val epp : signature -> program -> program0 **)

let epp sig2 p =
  Pair ((epp_D sig2 (procedures sig2 p)),
    (epp_C sig2 (procedures sig2 p) (cCP_pn sig2 p) (main sig2 p)))

(** val sig1 : signature **)

let sig1 =
  { pid = cC_Nat; var = bool0; value = cC_Nat; expr = cC_Expressions; bexpr =
    bool_Expressions; recvar = cC_Nat; ann = unit1; ev = cC_Eval; bev =
    cC_BEval }

(** val epp' : program -> program0 **)

let epp' p =
  epp sig1 p
