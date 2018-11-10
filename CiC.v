Require Import Category.


Polymorphic Definition CiCSig: CatSig := {|
  Ob               := Type;
  Hom X Y          := X -> Y;
  id X x           := x;
  comp X Y Z g f x := g (f x);
  eq_h X Y f g     := forall x, f x = g x
|}.

Polymorphic Lemma CiCAx: CatAx CiCSig.
Proof.
  split; simpl; try reflexivity.
  intros X Y.
  split.
  intros f x. reflexivity.
  intros f g H x. symmetry. apply H.
  intros f g h H1 H2 x.
  transitivity (g x).
  apply H1. apply H2.
  intros X Y Z g g' Hg f f' Hf x.
  transitivity (g (f' x)).
  f_equal. apply Hf.
  apply Hg.
Defined.

Polymorphic Definition CiC: Cat := {|
  catAx := CiCAx
|}.
