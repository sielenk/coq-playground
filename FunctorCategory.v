Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Require Export NaturalTransformation.

Section functor_category.
  Polymorphic Variables A B: Cat.

  Polymorphic Definition natTransId(F: Fun A B): NatTrans F F.
    refine {| preNatTrans X := id (F X) |}.
    intros.
    transitivity (fmap F f).
    apply (ident_r B).
    symmetry.
    apply (ident_l B).
  Defined.

  Polymorphic Definition natTransComp{F G H: Fun A B}:
      NatTrans G H-> NatTrans F G -> NatTrans F H.
    intros eta1 eta2.
    refine {| preNatTrans X := comp (eta1 X) (eta2 X) |}.
    intros.
    transitivity (comp (comp (fmap H f) (eta1 X)) (eta2 X)).
    apply (assoc B).
    transitivity (comp (comp (eta1 Y) (fmap G f)) (eta2 X)).
    f_equiv.
    apply natural.
    transitivity (comp (eta1 Y) (comp (eta2 Y) (fmap F f))).
    transitivity (comp (eta1 Y) (comp (fmap G f) (eta2 X))).
    symmetry.
    apply (assoc B).
    f_equiv.
    apply natural.
    apply (assoc B).
  Defined.


  Polymorphic Definition FUNSig: CatSig := {|
    Ob                 := Fun A B;
    Hom                := NatTrans;
    id                 := natTransId;
    comp F G H         := natTransComp;
    eq_h F G eta1 eta2 := forall X, eq_h (eta1 X) (eta2 X)
  |}.

  Polymorphic Lemma FUNAx: CatAx FUNSig.
  Proof.
    split.
    intros F G.
    split.
    intros f X.
    reflexivity.
    intros f g H X.
    symmetry.
    apply H.
    intros f g h H1 H2 X.
    transitivity (g X).
    apply H1.
    apply H2.
    intros F G H f f' H1 g g' H2 X.
    apply (comp_eq B).
    apply H1.
    apply H2.
    intros F G f X.
    apply (ident_r B).
    intros F G f X.
    apply (ident_l B).
    intros F G H I h g f X.
    apply (assoc B).
  Qed.

  Polymorphic Definition FUN: Cat := {|
    catAx  := FUNAx
  |}.
End functor_category.

Arguments natTransId   {_ _}.
Arguments natTransComp {_ _ _ _ _}.
