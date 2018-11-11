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
Require Import Delta.



Polymorphic Record AdjointSig{A B: Cat}{F: Fun B A}{G: Fun A B} := {
  epsilon: NatTrans (funComp F G) (funId A);
  eta    : NatTrans (funId B) (funComp G F)
}.

Arguments AdjointSig {_ _} _ _.

Polymorphic Record AdjointAx{A B F G}(S: @AdjointSig A B F G): Prop := {
  foo: forall Y, eq_h (id (F Y)) (comp (epsilon S (F Y)) (fmap F (eta S Y)));
  bar: forall X, eq_h (comp (fmap G (epsilon S X)) (eta S (G X))) (id (G X))
}.

Polymorphic Record Adjoint{A B: Cat}{F: Fun B A}{G: Fun A B} := {
  adjointSig :> AdjointSig F G;
  adjointAx  :> AdjointAx adjointSig
}.
