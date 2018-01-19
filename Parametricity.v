Require Import List Arith.
Require MSets FMapAVL.

Module S := Coq.MSets.MSetAVL.Make Coq.Structures.OrdersEx.Nat_as_OT.
Module M := Coq.FSets.FMapAVL.Make Coq.Structures.OrderedTypeEx.Nat_as_OT.

Inductive type: Type :=
| Bool    :                 type
| Nat     :                 type
| Var     : nat  ->         type
| Prod    : type -> type -> type
| List    : type         -> type
| Lambda  : type -> type -> type
| Forall  : nat  -> type -> type
.

Fixpoint type2Type(t: type)(x: M.t Type): Type :=
  match t with 
  | Bool => bool
  | Nat => nat
  | Var n => match M.find n x with Some T => T | None => Empty_set end
  | Prod t1 t2 => prod (type2Type t1 x) (type2Type t2 x)
  | List t => list (type2Type t x)
  | Lambda t1 t2 => (type2Type t1 x) -> (type2Type t2 x)
  | Forall v t => forall (tt: Type), (type2Type t (M.add v tt x))
  end.


Definition x := type2Type (Prod Bool Nat) (M.empty _).
Definition y: x := pair true 4.


Inductive Rel := Rel_ A A' (R: A -> A' -> Prop).

Definition p1(R: Rel): Type := match R with Rel_ T _ _ => T end.
Definition p2(R: Rel): Type := match R with Rel_ _ T _ => T end.


Fixpoint type2Rel(t: type)(Rs: M.t Rel): type2Type t (M.map p1 Rs) -> type2Type t (M.map p2 Rs) -> Prop :=
  match t with 
  | Bool => eq
  | Nat => eq
  | Var n => match M.find n Rs with Some (Rel_ A A' R) => _ | None => fun _ _ => False end
  | Prod t1 t2 => fun v1 v2 =>
    match v1, v2 with
     (v1a, v1b), (v2a, v2b) => type2Rel _ Rs v1a v2a /\ type2Rel _ Rs v1b v2b
    end
  | List t => fun v1 v2 => False
  | Lambda t1 t2 => fun f1 f2 =>
    forall v1 v2, type2Rel _ Rs v1 v2 -> type2Rel _ Rs (f1 v1) (f2 v2)
  | Forall X F => fun g g' =>
    forall A A' (R: A -> A' -> Prop) a a', R a a' -> type2Rel _ (M.add X (Rel_ _ _ R) Rs) (g A) (g' A')
  end.

