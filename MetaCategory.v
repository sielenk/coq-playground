Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.


Require Import Category.
Require Import Functor.
Require Import NaturalTransformation.
Require Import FunctorCategory.



Polymorphic Definition funId(A: Cat): Fun A A.
  refine {| funSig := {| fmap_o X := X; fmap X Y f := f |} |}.
  split.
  intros X Y f f' H1.
  assumption.
  intros X.
  reflexivity.
  intros X Y Z g h.
  reflexivity.
Defined.

Polymorphic Definition funComp{A B C: Cat}(G: Fun B C)(F: Fun A B): Fun A C.
  refine {| funSig := {| fmap_o X := G (F X); fmap X Y f := fmap G (fmap F f) |} |}.
  split.
  intros X Y f f' H1.
  apply (fmap_eq G).
  apply (fmap_eq F).
  assumption.
  intros X.
  simpl. transitivity (fmap G (id (F X))).
  f_equiv.
  apply (fmap_id F).
  apply (fmap_id G).
  intros X Y Z g f.
  simpl. transitivity (fmap G (comp (fmap F g) (fmap F f))).
  f_equiv.
  apply (fmap_comp F).
  apply (fmap_comp G).
Defined.

Polymorphic Definition CAT: CatSig := {|
  Ob         := Cat;
  Hom        := Fun;
  id         := funId;
  comp _ _ _ := funComp;
  eq_h A B   := @isomorphic (FUN A B)
|}.
