From PCC Require Export Implementation.

From Stdlib Require Import Vector.
Import VectorNotations.

Section ParallelImplementation.

(** ** Parallel implementation
  There is also a parallel variant for composition. This is defined in the same steps, but
  requires yet another auxiliary function. *)

Open Scope CC_scope.

Definition copy_input {m} (ps qs:t Pid m) (X:RecVar) : Choreography IS.
(*
  match m with
  | 0 => End
  | S _ => (hd ps # this --> hd qs; copy_input (tl ps) (tl qs))
  end.
*)
Proof.
induction m.
+ apply (Call X).
+ apply (Interaction _ (Send (hd ps) this (hd qs)) eps (IHm (tl ps) (tl qs))).
Defined.

Fixpoint copy_input_iter {m} (ps:t Pid m) {n} (qs: t (t Pid m) n) (X:RecVar) :
  RecVar -> Choreography IS :=
  match qs with
  | nil _ => (fun _ => End)
  | (rs::qs') => (fun Y => if (X =? Y)
        then copy_input ps rs (S X)
        else copy_input_iter ps qs' (S X) Y)
  end.

(*
Eval compute in (map (copy_input_iter [1;3;5] [[2;4;6];[7;8;9]] 2) [0;1;2;3;4;5]).
*)

Fixpoint Gamma' {m} (f:PRFunction m) : nat :=
  match f with
  | Zero => 1
  | Successor => 1
  | Projection _ => 1
  | @Composition k _ g fs => Gamma' g + vsum (map Gamma' fs) + k
  | Recursion f g => Gamma' f + Gamma' g + 3
  | Minimization f => Gamma' f + 2
  end.

(** The extra argument ps_start is for the processes where the inputs in [fs[@0]] come from. *)

Fixpoint par_compose {m} {k} (fs:t (PRFunction m) k)
  d (Hd:forall i, depth fs[@i] < d) (target init ps_start:nat) (X:RecVar)
  (Implement : forall m' (f:PRFunction m') (Hd:depth f < d)
  (ps':t Pid m') (q' i':nat) (k':RecVar), RecVar -> Choreography IS) {struct fs}
  : RecVar -> Choreography IS.
Proof.
destruct fs.
- apply (fun _ => End).
- assert (forall i, depth fs[@i] < d).
  intro; apply (Hd (Fin.FS i)).
  pose (Implement m h (Hd Fin.F1) (vec_k_to_n m ps_start) target init X) as Ph.
  pose (par_compose _ _ fs d H (S target) (init + Pi h) (ps_start + m) (X + Gamma h) Implement) as Pfs.
  apply (fun Y => if Y <? X + Gamma h then (Ph Y) else (Pfs Y)).
Defined.

Fixpoint Par_Implementation_aux {m} (f:PRFunction m) d (Hd:depth f<d)
  (ps:t Pid m) (q:Pid) (init:nat) (X:RecVar) {struct d}: RecVar -> Choreography IS.
Proof.
induction d.
+ elim (Nat.nlt_0_r _ Hd).
+ destruct f; intros; revert X0.

  (* Zero *)
  - apply (Pack1 X (Send (hd ps) zero q @ eps;; @Call IS (S X))).

  (* Successor *)
  - apply (Pack1 X (Send (hd ps) succ_this q @ eps;; @Call IS (S X))).

  (* Projection *)
  - apply (Pack1 X (Send ps[@Fin.of_nat_lt l] this q @ eps;; @Call IS (S X))).

  (* Composition *)
  - simpl in Hd; generalize (proj2 (Nat.succ_lt_mono _ _) Hd); clear Hd; intro Hd'.
    pose (max_lt_l _ _ _ Hd') as Hdf.
    pose (max_lt_r _ _ _ Hd') as Hdfs.
    assert (forall i, depth fs[@i] < d).
    intros; rewrite <- nth_map'; apply vmax_lt; auto.
    set (init' := init + m*k).
    pose (copy_input_iter ps (vec_m_with_k init m k) X) as Hinit.
    pose (par_compose fs _ H init' (init'+m) init (X+m) (fun m f => Par_Implementation_aux m f d)) as Pfs.
    pose (Par_Implementation_aux _ f _ Hdf (seq_labels init' fs) q (init' + m) (X + k + (vsum (map Gamma' fs)))) as Pf.
    apply (fun Y =>
      if Y <? X + k then Hinit Y
      else if Y <? X + k + vsum (map Gamma fs) then Pfs Y else Pf Y).

  (* Recursion *)
  - rename f1 into f; rename f2 into g.
    simpl in Hd; generalize (proj2 (Nat.succ_lt_mono _ _) Hd); clear Hd; intro Hd'.
    pose (max_lt_l _ _ _ Hd') as Hf.
    pose (max_lt_r _ _ _ Hd') as Hg.
    pose (Par_Implementation_aux _ f _ Hf (tl ps) init (init+3) X) as Pf.
    pose (Par_Implementation_aux _ g _ Hg (S init :: init :: tl ps) (init+2) (init+3 + Pi f) (X + Gamma' f + 2)) as Pg.
    apply (fun Y =>
      if (Y <? X + Gamma' f) then Pf Y
      else if (Y =? (X + Gamma' f)) then
         Send (init+2) zero (S init) @ eps;; @Call IS (X + Gamma' f + 1)
      else if (Y =? (X + Gamma' f + 1)) then 
         IfEq (S init) (hd ps) (Send init this q @eps;; @Call IS (X + Gamma' f + Gamma' g + 3)) (@Call IS (X + Gamma' f + 2))
      else if (Y =? (X + Gamma' f + Gamma' g + 2)) then
         Send (init+2) this init @ eps;; Send (S init) this (init+2) @ eps;; Send (init+2) succ_this (S init) @ eps;; @Call IS (X + Gamma' f + 1)
      else Pg Y).

  (* Minimization *)
  - simpl in Hd; apply (proj2 (Nat.succ_lt_mono _ _)) in Hd; rename Hd into Hf.
    pose (Par_Implementation_aux _ f _ Hf (shiftin (S init) ps) init (init+3) (X + 1)) as Pf.
    apply (fun Y =>
      if (Y =? X) then
         Send (init+2) zero (init+1) @ eps;; @Call IS (X + 1)
      else if (Y =? (X + Gamma' f + 1)) then
         Send (init+1) zero (init+2) @ eps;; IfEq (init+2) init
           (Send (init+1) this q @ eps;; @Call IS (X + Gamma' f + 2))
           (Send (init+1) this (init+2) @ eps;; Send (init+2) succ_this (init+1) @ eps;; @Call IS (X + 1))
        else Pf Y).
Defined.

Definition Par_Implementation {m} (f:PRFunction m) (ps:t Pid m) (q:Pid)
  : Program IS :=
  (fun X => (all_pids ((max q (vmax ps)) + Pi f),
             Par_Implementation_aux f _ (Nat.lt_succ_diag_r (depth f))
                                    ps q (S (max q (vmax ps))) 0 X),
  @Call IS 0).

(** By default, we take process 0 for q and 1..m for the ps. *)

Definition Par_Implementation' {m} (f:PRFunction m) : Program IS :=
  Par_Implementation f (vec_1_to_n m) 0.

(* Sanity checks.
Eval compute in (Main (Par_Implementation' (Composition Successor [Zero]))).
Eval compute in (map snd (map (Procedures _ (Par_Implementation' (Composition Successor [Zero]))) [0;1;2;3])).

Eval compute in (Main (Par_Implementation' (Composition Zero [Projection aux13]))).
Eval compute in (map snd (map (Procedures _ (Par_Implementation' (Composition Zero [Projection aux13]))) [0;1;2;3])).

Eval compute in (Main (Par_Implementation' (Composition (Projection aux22) [Zero; Successor]))).
Eval compute in (map snd (map (Procedures _ (Par_Implementation' (Composition (Projection aux22) (Zero :: [Successor])))) [0;1;2;3;4;5])).

Eval compute in (Main (Par_Implementation' PR_add)).
Eval compute in (map snd (map (Procedures _ (Par_Implementation' PR_add)) [0;1;2;3;4;5;6;7;8;9])).
Eval compute in (map snd (map (Procedures _ (Par_Implementation' (Composition Successor [Projection aux23]))) [0;1;2;3])).
*)

End ParallelImplementation.
