Require Import Functor.
Require Import CommaCategory.
Require Import FunctorCategory.
Require Import Delta.
Require Import Diagrams.
Require Import MetaCategory.
Require Import Isomorphisms.




Definition Cone{D A: Cat}(F: Fun D A): CAT :=
  CommaCat (delta D A) (iso_inv (iso_A1_A (FUN D A)) F).

Definition vertex{D A: Cat}{F: Fun D A}: Fun (Cone F) A :=
  CommaDomFun _ _.

Definition foo{D A: Cat}{F: Fun D A}(L: Cone F): NatTrans (deltaOb D (vertex L)) F :=
  fmap (CommaHomFun _ _ L) (tt: @Hom two false true).

Lemma bar{D A: Cat}{F: Fun D A}(L: Cone F):
    forall{X Y: D}(f: Hom X Y),  eq_h (comp (fmap F f) (foo L X)) (foo L Y).
Proof.
  intros X Y f.
  transitivity (comp (foo L Y) (id _)).
  apply (natTrans_natural (foo L) X Y f).
  apply (ident_r A).
Qed.

Record lim{D A: Cat}(F: Fun D A) := {
  limit_cone   :> Cone F;
  limit_initial:  initial limit_cone
}.
