Require Import Functor.
Require Import CommaCategory.
Require Import FunctorCategory.
Require Import Delta.
Require Import Diagrams.
Require Import MetaCategory.


Polymorphic Definition Cone{D A: Cat}(F: Fun D A): CAT :=
  CommaCat (delta D A) (oneFun (FUN D A) F).

Polymorphic Definition cone{D A: Cat}{F: Fun D A}(N: A)(psi: forall X, Hom N (F X)):
    (forall{X Y: D}(f: Hom X Y), eq_h (comp (fmap F f) (psi X)) (psi Y)) ->
    Cone F.

  intro H. simpl.
  refine (Build_CommaOb _ _ _
    (delta D A) (oneFun (FUN D A) F)
    N oneX
    (Build_NatTrans _ _ (delta D A N) (oneFun (FUN D A) F oneX) psi _)).
  intros X Y f. simpl.
  transitivity (psi Y). apply H.
  symmetry. apply (ident_r A).
Defined.

Polymorphic Definition cone_Ob{D A: Cat}{F: Fun D A}: Fun (Cone F) A :=
  CommaDomFun _ _.

Polymorphic Definition cone_Hom{D A: Cat}{F: Fun D A}(L: Cone F)(X: D): Hom (cone_Ob L) (F X) :=
  fmap (CommaHomFun _ _ L) twoF X.

Polymorphic Lemma cone_prop{D A: Cat}{F: Fun D A}(L: Cone F):
    forall{X Y: D}(f: Hom X Y), eq_h (comp (fmap F f) (cone_Hom L X)) (cone_Hom L Y).
Proof.
  intros X Y f.
  transitivity (comp (cone_Hom L Y) (id _)).
  apply (natTrans_natural (fmap (CommaHomFun _ _ L) twoF) X Y f).
  apply (ident_r A).
Qed.

Polymorphic Definition coneHom{D A: Cat}{F: Fun D A}
    (X Y: Cone F)
    (f: Hom (cone_Ob X) (cone_Ob Y)):
    (forall d: D, eq_h (cone_Hom X d) (comp (cone_Hom Y d) f)) ->
    Hom X Y.
  intro H.
  refine {|
    commaHom_fst := f;
    commaHom_snd := oneHom;
  |}.
  intro d.
  symmetry.
  transitivity (commaOb_f X d).
  destruct oneHom.
  apply (ident_l (FUN D A)).
  apply (H d).
Defined.



Polymorphic Record Lim{D A: Cat}(F: Fun D A) := {
  limit_cone    :> Cone F;
  limit_terminal:  terminal limit_cone
}.
