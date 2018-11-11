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

Polymorphic Definition CATSig: CatSig := {|
  Ob         := Cat;
  Hom        := Fun;
  id         := funId;
  comp _ _ _ := funComp;
  eq_h A B   := @isomorphic (FUN A B)
|}.

(*
Polymorphic Lemma CATAx: CatAx CATSig.
Proof.
  split.
  intros. simpl.
  apply (@isomorphic_Equivalence (FUN X Y)).
  intros X Y Z f1 f2 [fa [fb Hf]] g1 g2 [ga [gb Hg]].
  apply iso_isomorphic.
  eapply fun_iso.
  intros X' Y' f'. simpl.
  refine {|
    iso_hom := _;
    iso_inv := _
  |}.
  split; intro X'; simpl.
  eapply fun_iso.
  eexists. simpl in fa. (comp f2 g2).
  eexists.
  
Qed.
*)

Polymorphic Definition CAT := CATSig.
