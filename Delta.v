Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Eqdep.


Require Import Category.
Require Import Functor.
Require Import NaturalTransformation.
Require Import FunctorCategory.
Require Import MetaCategory.
Require Import Diagrams.


Polymorphic Definition deltaOb A {B: Cat}(X: B): Ob (FUN A B).
  refine {|
    funSig := {|
      fmap_o _   := X;
      fmap _ _ _ := id X
    |}
  |}.
  split.
  intros Y Z f f' Hf.
  reflexivity.
  intros Y.
  reflexivity.
  simpl. intros _ _ _ _ _.
  symmetry.
  apply (ident_r B).
Defined.

Polymorphic Definition deltaHom A {B: Cat}{X Y: B}(f: Hom X Y):
    Hom (deltaOb A X) (deltaOb A Y).
  refine {| preNatTrans a := f: Hom (deltaOb A X a) (deltaOb A Y a) |}.
  simpl.
  intros _ _ _.
  transitivity f.
  apply (ident_l B).
  symmetry.
  apply (ident_r B).
Defined.

Polymorphic Definition deltaSig(A B: Cat): FunSig B (FUN A B) := {|
  fmap_o   := deltaOb A;
  fmap X Y := deltaHom A
|}.

Polymorphic Lemma deltaAx(A B: Cat): FunAx (deltaSig A B).
Proof.
  split.
  intros X Y f f' Hf u.
  apply Hf.
  intros X u.
  reflexivity.
  intros X Y Z g h u.
  reflexivity.
Defined.

Polymorphic Definition delta(A B: Cat): Fun B (FUN A B) := {|
  funAx := deltaAx A B
|}.
