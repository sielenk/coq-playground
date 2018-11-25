Require Import Category.


Polymorphic Definition RelSig: CatSig := {|
  Ob             := Type;
  Hom X Y        := X -> Y -> Prop;
  id X           := eq;
  comp X Y Z g f := fun x z => exists y, g y z /\ f x y;
  eq_h X Y f1 f2 := forall x y, f1 x y <-> f2 x y;
|}.

Polymorphic Lemma RelAx : CatAx RelSig.
Proof.
  split.
  intros. split.
  intros f x y. reflexivity.
  intros f1 f2 Hf x y. symmetry. apply Hf.
  intros f1 f2 f3 H1f H2f x y.
  transitivity (f2 x y). apply H1f. apply H2f.
  intros X Y Z g1 g2 Hg f1 f2 Hf x z.
  simpl. split; intros [y [Hg' Hf']]; exists y; split;
  [apply Hg | apply Hf | apply Hg | apply Hf];
  assumption.
  intros X Y f x y. simpl. split.
  intros [x' [H1 H2]]. destruct H2. assumption.
  intros H. exists x. auto.
  intros X Y f x y. simpl. split.
  intros [y' [H1 H2]]. destruct H1. assumption.
  intros H. exists y. auto.
  intros W X Y Z h g f x z.
  simpl. split.
  intros [y [H1 [x' [H2 H3]]]].
  exists x'. split. exists y. split; assumption. assumption.
  intros [x' [[y [H1 H2]] H3]].
  exists y. split. assumption. exists x'. split; assumption.
Qed.

Polymorphic Definition Rel: Cat := {|
  catAx := RelAx
|}.
