Require Import Functor.
Require Import CommaCategory.
Require Import FunctorCategory.
Require Import Delta.
Require Import Diagrams.
Require Import MetaCategory.


Definition Cone{D A: Cat}(F: Fun D A): CAT :=
  CommaCat (delta D A) (oneFun (FUN D A) F).

Definition cone{D A: Cat}{F: Fun D A}(N: A)(psi: forall X, Hom N (F X)):
    (forall{X Y: D}(f: Hom X Y), eq_h (comp (fmap F f) (psi X)) (psi Y)) ->
    Cone F.

  intro H. simpl.
  refine (Build_CommaOb _ _ _
    (delta D A) (oneFun (FUN D A) F)
    N oneOb
    (Build_NatTrans _ _ (delta D A N) (oneFun (FUN D A) F oneOb) psi _)).
  intros X Y f. simpl.
  transitivity (psi Y). apply H.
  symmetry. apply (ident_r A).
Defined.

Definition cone_Ob{D A: Cat}{F: Fun D A}: Fun (Cone F) A :=
  CommaDomFun _ _.

Definition cone_Hom{D A: Cat}{F: Fun D A}(L: Cone F)(X: D): Hom (cone_Ob L) (F X) :=
  fmap (CommaHomFun _ _ L) twoF X.

Lemma cone_prop{D A: Cat}{F: Fun D A}(L: Cone F):
    forall{X Y: D}(f: Hom X Y),  eq_h (comp (fmap F f) (cone_Hom L X)) (cone_Hom L Y).
Proof.
  intros X Y f.
  transitivity (comp (cone_Hom L Y) (id _)).
  apply (natTrans_natural (fmap (CommaHomFun _ _ L) twoF) X Y f).
  apply (ident_r A).
Qed.

Record lim{D A: Cat}(F: Fun D A) := {
  limit_cone   :> Cone F;
  limit_initial:  initial limit_cone
}.
