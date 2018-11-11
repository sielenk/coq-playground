Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.

Require Export NaturalTransformation.

Section functor_category.
  Polymorphic Variables(A: CatSig)(B: Cat).

  Polymorphic Definition natTransId(F: FunSig A B): NatTrans F F.
    refine {| natTrans X := id (F X) |}.
    intros X Y f.
    transitivity (fmap F f).
    apply (ident_r B).
    symmetry.
    apply (ident_l B).
  Defined.

  Polymorphic Definition natTransComp{F G H: FunSig A B}:
      NatTrans G H-> NatTrans F G -> NatTrans F H.
    intros eta1 eta2.
    refine {| natTrans X := comp (eta1 X) (eta2 X) |}.
    intros X Y f.
    transitivity (comp (comp (fmap H f) (eta1 X)) (eta2 X)).
    apply (assoc B).
    transitivity (comp (comp (eta1 Y) (fmap G f)) (eta2 X)).
    f_equiv.
    apply natTrans_natural.
    transitivity (comp (eta1 Y) (comp (eta2 Y) (fmap F f))).
    transitivity (comp (eta1 Y) (comp (fmap G f) (eta2 X))).
    symmetry.
    apply (assoc B).
    f_equiv.
    apply natTrans_natural.
    apply (assoc B).
  Defined.


  Polymorphic Definition FUNSig: CatSig := {|
    Ob                 := FunSig A B;
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

  Polymorphic Definition fun_iso(F G: FUNSig)
      (iso: forall X, Iso (F X) (G X))
      (Hnat: natural iso):
      Iso F G.
    refine {|
      iso_hom := {|
        natTrans X := iso_hom (iso X);
        natTrans_natural := Hnat
      |}: @Hom FUN _ _;
      iso_inv := {|
        natTrans X := iso_inv (iso X);
        natTrans_natural := iso_natural _ Hnat
      |}
    |}.
    simpl.
    split; intro X; apply (iso_prop _).
  Defined.
End functor_category.

Arguments natTransId   {_ _}.
Arguments natTransComp {_ _ _ _ _}.
Arguments fun_iso      {_ _}.
