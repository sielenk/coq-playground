Require Import
  Coq.FSets.FMapAVL
  Coq.FSets.FMapFacts
  Coq.Structures.OrderedTypeEx
  Coq.Logic.FunctionalExtensionality.



Module M := FMapAVL.Make Nat_as_OT.

Module P := WProperties_fun Nat_as_OT M.
Module F := P.F.

Inductive type: Set :=
  | Bool    :                 type
  | Nat     :                 type
  | Var     : nat  ->         type
  | Prod    : type -> type -> type
(*| List    : type         -> type*)
  | Lambda  : type -> type -> type
  | Forall  : nat  -> type -> type
  .


Definition update{V} k v (env: nat -> V) k': V :=
  if Nat.eqb k k' then v else env k'.


Fixpoint type2Type(t: type)(env: nat -> Type): Type :=
  match t with 
  | Bool => bool
  | Nat => nat
  | Var v => env v
  | Prod t1 t2 => prod (type2Type t1 env) (type2Type t2 env)
(*| List t => list (type2Type t env) *)
  | Lambda t1 t2 => (type2Type t1 env) -> (type2Type t2 env)
  | Forall v t => forall (tt: Type), (type2Type t (update v tt env))
  end.


Definition x := type2Type (Prod Bool Nat) (fun _ => Empty_set).
Definition y: x := pair true 4.


Inductive Rel := Rel_ A A' (R: A -> A' -> Prop).

Definition p1 (env: nat -> Rel) n: Type := match env n with Rel_ T _ _ => T end.
Definition p2 (env: nat -> Rel) n: Type := match env n with Rel_ _ T _ => T end.
Definition rel(env: nat -> Rel) n: p1 env n -> p2 env n -> Prop :=
  match env n as R
    return match R with Rel_ A _ _ => A end -> match R with Rel_ _ A _ => A end -> Prop 
    with Rel_ _ _ R => R end.

Lemma p1_update{A A'} k R env: update k A (p1 env) = p1 (update k (Rel_ A A' R) env).
Proof.
  unfold update, p1.
  extensionality k'.
  destruct (Nat.eqb k k'); reflexivity.
Qed.

Lemma p2_update{A A'} k R env: update k A' (p2 env) = p2 (update k (Rel_ A A' R) env).
Proof.
  unfold update, p2.
  extensionality k'.
  destruct (Nat.eqb k k'); reflexivity.
Qed.

Definition lift1{k t' A A' R env}(x: type2Type t' (update k A (p1 env))):
                                     type2Type t' (p1 (update k (Rel_ A A' R) env)).
  rewrite <- p1_update.
  assumption.
Defined.

Definition lift2{k t' A A' R env}(x: type2Type t' (update k A' (p2 env))):
                                     type2Type t' (p2 (update k (Rel_ A A' R) env)).
  rewrite <- p2_update.
  assumption.
Defined.

Fixpoint type2Rel(t: type)(env: nat -> Rel): type2Type t (p1 env) -> type2Type t (p2 env) -> Prop :=
  match t with 
  | Bool => eq
  | Nat => eq
  | Var v => rel env v
  | Prod t1 t2 => fun v1 v2 =>
    match v1, v2 with
     (v1a, v1b), (v2a, v2b) => type2Rel _ env v1a v2a /\ type2Rel _ env v1b v2b
    end
(*| List t => fun v1 v2 => False*)
  | Lambda t1 t2 => fun f1 f2 =>
    forall v1 v2, type2Rel _ env v1 v2 -> type2Rel _ env (f1 v1) (f2 v2)
  | Forall X t' => fun g g' =>
      forall A A' (R: A -> A' -> Prop),
        type2Rel t' (update X (Rel_ _ _ R) env) (lift1 (g A)) (lift2 (g' A'))
  end.


Definition type2Type'(T: type): Type :=
  type2Type T (fun _ => Empty_set).

Definition type2Rel' (T: type): type2Type' T -> type2Type' T -> Prop :=
  type2Rel T (fun _ => Rel_ Empty_set Empty_set (fun _ _ => False)).



Theorem Parametricity: forall T (t: type2Type' T), type2Rel' T t t.
Proof.
  unfold type2Type', type2Rel'.
  induction T; simpl; try auto.
  intros [].
  intros [t1 t2]. auto.
  set (R1 := type2Rel T1 (fun _ : nat => Rel_ Empty_set Empty_set (fun _ _ : Empty_set => False))) in * |- *.
  set (R2 := type2Rel T2 (fun _ : nat => Rel_ Empty_set Empty_set (fun _ _ : Empty_set => False))) in * |- *.
  unfold p1, p2 in * |- *.
  set (TT1 := type2Type T1 (fun _ : nat => Empty_set)) in * |- *.
  set (TT2 := type2Type T2 (fun _ : nat => Empty_set)) in * |- *.
  intros f a1 a2 H.

Qed.



Definition I : type := Forall 0 (Lambda (Var 0) (Var 0)).
Definition It: Type := type2Type I (fun _ => Empty_set).
Definition Ir: It -> It -> Prop := type2Rel I (fun _ => Rel_ Empty_set Empty_set (fun _ _ => False)).

Definition i: It := fun X (x: X) => x.

Theorem foo: Ir i i.
Proof.
  unfold Ir.
  compute.
  intros A A' R a a' H.
  apply H.
  set (H3 := p1_update 0 R (fun _ : nat => Rel_ Empty_set Empty_set (fun _ _ : Empty_set => False))).
  set (H4 := p2_update 0 R (fun _ : nat => Rel_ Empty_set Empty_set (fun _ _ : Empty_set => False))).
  generalize H3.


 simpl.

