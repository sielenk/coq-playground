Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.


Require Import Category.
Require Import Functor.
Require Import NaturalTransformation.
Require Import FunctorCategory.
Require Import MetaCategory.
Require Import Diagrams.


Section isomorphic_A1_A.
  Polymorphic Variable A: Cat.

  Polymorphic Let A1 := FUN one A.

  Polymorphic Definition fun_A1_A_Sig: FunSig A1 A := {|
    fmap_o(X: A1) := X one_X;
    fmap X Y f    := f one_X
  |}.

  Polymorphic Lemma fun_A1_A_Ax: FunAx fun_A1_A_Sig.
  Proof.
    split.
    intros X Y f f' Hf.
    apply Hf.
    intros X.
    reflexivity.
    intros X Y Z g h.
    reflexivity.
  Defined.

  Polymorphic Definition fun_A1_A: Fun A1 A := {|
    funAx := fun_A1_A_Ax
  |}.

  Polymorphic Let id1 := comp (A := CATSig) (oneFun A) fun_A1_A: FUN A1 A1.
  Polymorphic Let id2 := id   (A := CATSig) A1:                  FUN A1 A1.

  Polymorphic Definition iso_A1_1(F: A1)(X: one): Iso (id1 F X) (id2 F X).
    refine {|
      iso_hom := match X as u return (Hom (F one_X) (F u)) with
                 | oneOb_ => id (F one_X)
                 end;
      iso_inv := match X as u return (Hom (F u) (F one_X)) with
                 | oneOb_  => id (F one_X)
                 end
    |}.
    destruct X; split; apply (ident_r A).
  Defined.

  Polymorphic Definition iso_A1_2(F: A1): Iso (id1 F) (id2 F).
    apply (fun_iso _ _ (iso_A1_1 F)).

    intros [] [] [].
    simpl.
    transitivity (id (F one_X)).
    transitivity (fmap F one_idX).
    apply (ident_r A).
    unfold A1 in F. simpl in F.
    apply (fmap_id (F: Fun _ _)).
    symmetry. apply (ident_r A).
  Defined.

  Polymorphic Definition iso_A1_3: Iso id1 id2.
    apply (fun_iso _ _ iso_A1_2).

    intros X Y f [].
    simpl.
    transitivity (f one_X).
    apply (ident_r A).
    symmetry. apply (ident_l A).
  Defined.

  Polymorphic Definition iso_A1_A: @Iso CATSig A1 A.
    refine {|
      iso_hom := fun_A1_A: @Hom CATSig _ _;
      iso_inv := oneFun _
    |}.

    split.
    set (A' := A: CATSig).
    set (Y := id A': FUN A' A').
    exists (id Y).
    exists (id Y).
    split; intro Z; apply (ident_r A).

    apply (iso_isomorphic iso_A1_3).
  Defined.
End isomorphic_A1_A.
