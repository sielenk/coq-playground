Require Import List Arith.
Require MSets FMapAVL.

Module S := Coq.MSets.MSetAVL.Make Coq.Structures.OrdersEx.Nat_as_OT.
Module M := Coq.FSets.FMapAVL.Make Coq.Structures.OrderedTypeEx.Nat_as_OT.

Inductive type: S.t -> Type :=
| Bool           :                         type S.empty
| Nat            :                         type S.empty
| Var n          :                         type (S.singleton n)
| Prod  {vs1 vs2}: type vs1 -> type vs2 -> type (S.union vs1 vs2)
| List  {vs}     : type vs              -> type vs
| Lambda{vs1 vs2}: type vs1 -> type vs2 -> type (S.union vs1 vs2)
| Forall v {vs}  : type vs              -> type (S.remove v vs)
.

Fixpoint foo{vs}(t: type vs)(x: M.t Type): Type :=
  match t with 
  | Bool => bool
  | Nat => nat
  | Var n => match M.find n x with Some T => T | None => Empty_set end
  | Prod t1 t2 => prod (foo t1 x) (foo t2 x)
  | List t => list (foo t x)
  | Lambda t1 t2 => (foo t1 x) -> (foo t2 x)
  | Forall v t => forall (tt: Type), (foo t (M.add v tt x))
  end.

Fixpoint bar{vs}(t: type vs)(x1 x2: M.t Type): foo t x1 -> foo t x2 -> Prop :=
  match t with 
  | Bool => eq
  | Nat => eq
  | Var n => fun t1 t2 =>
    True (* (M.find n x1) (M.find n x2) *)
  | Prod t1 t2 => fun v1 v2 =>
    match v1, v2 with
     (v1a, v1b), (v2a, v2b) => bar _ x1 x2 v1a v2a /\ bar _ x1 x2 v1b v2b
    end
  | List t => fun v1 v2 => False
  | Lambda t1 t2 => fun f1 f2 =>
    forall v1 v2, bar _ x1 x2 v1 v2 -> bar _ x1 x2 (f1 v1) (f2 v2)
  | Forall X F => fun g g' =>
    forall A A' (R: A -> A' -> Prop) a a', R a a' -> bar _ (M.add X A x1) (M.add X A' x2) (g A) (g' A')
  end.


Definition x := foo (Prod Bool Nat) (M.empty _).

Definition y: x := pair true 4.