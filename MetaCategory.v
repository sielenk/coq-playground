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


Polymorphic Definition natTransCompH{A B C: Cat}{H I: Fun B C}{F G: Fun A B}:
  NatTrans H I -> NatTrans F G -> NatTrans (funComp H F) (funComp I G).
  intros eta epsilon.
  refine {|
    natTrans X := @comp C
      ((funComp H F) X)
      ((funComp H G) X)
      ((funComp I G) X)
      (eta (G X))
      (fmap H (epsilon X))
  |}.
  intros X Y f. simpl.
  assert (HetaF    := natTrans_natural eta _ _ (fmap F f)).
  assert (HetaG    := natTrans_natural eta _ _ (fmap G f)).
  assert (Hepsilon := natTrans_natural epsilon X Y f).
  transitivity (comp (comp (fmap I (fmap G f)) (eta (G X))) (fmap H (epsilon X))).
  apply (assoc C).
  transitivity (comp (comp (eta (G Y)) (fmap H (fmap G f))) (fmap H (epsilon X))).
  f_equiv.
  assumption.
  transitivity (comp (eta (G Y)) (comp (fmap H (fmap G f)) (fmap H (epsilon X)))).
  symmetry. apply (assoc C).
  transitivity (comp (eta (G Y)) (comp (fmap H (epsilon Y)) (fmap H (fmap F f)))).
  f_equiv.
  transitivity (fmap H (comp (epsilon Y) (fmap F f))).
  transitivity (fmap H (comp (fmap G f) (epsilon X))).
  symmetry. apply (fmap_comp H).
  f_equiv.
  assumption.
  apply (fmap_comp H).
  apply (assoc C).
Defined.

Polymorphic Definition natTransIsoCompH{A B C: Cat}{H I: Fun B C}{F G: Fun A B}:
  @Iso (FUN B C) H I -> @Iso (FUN A B) F G -> @Iso (FUN A C) (funComp H F) (funComp I G).
  intros [g g' [Hg1 Hg2]] [f f' [Hf1 Hf2]].
  refine {|
      iso_hom := natTransCompH g  f: @Hom (FUN A C) _ _;
      iso_inv := natTransCompH g' f'
    |}.

  split; intro X; simpl.

  transitivity (comp (g (G X)) (g' (G X))); try apply Hg1.
  transitivity (comp (g (G X)) (comp (fmap H (f X)) (comp (g' (F X)) (fmap I (f' X))))).
  symmetry. apply (assoc C).
  f_equiv.
  transitivity (comp (comp (fmap H (f X)) (g' (F X))) (fmap I (f' X))).
  apply (assoc C).
  transitivity (comp (comp (g' (G X)) (fmap I (f X))) (fmap I (f' X))).
  f_equiv.
  apply (natTrans_natural g' (F X) (G X) (f X)).
  transitivity (comp (g' (G X)) (comp (fmap I (f X)) (fmap I (f' X)))).
  symmetry. apply (assoc C).
  transitivity (comp (g' (G X)) (fmap I (comp (f X) (f' X)))).
  f_equiv.
  symmetry. apply (fmap_comp I).
  transitivity (comp (g' (G X)) (fmap I (id _))).
  f_equiv.
  f_equiv.
  apply Hf1.
  transitivity (comp (g' (G X)) (id _)).
  f_equiv.
  apply (fmap_id I).
  apply (ident_r C).

  transitivity (comp (g' (F X)) (g (F X))); try apply Hg2.
  transitivity (comp (g' (F X)) (comp (fmap I (f' X)) (comp (g (G X)) (fmap H (f X))))).
  symmetry. apply (assoc C).
  f_equiv.
  transitivity (comp (comp (fmap I (f' X)) (g (G X))) (fmap H (f X))).
  apply (assoc C).
  transitivity (comp (comp (g (F X)) (fmap H (f' X))) (fmap H (f X))).
  f_equiv.
  apply (natTrans_natural g (G X) (F X) (f' X)).
  transitivity (comp (g (F X)) (comp (fmap H (f' X)) (fmap H (f X)))).
  symmetry. apply (assoc C).
  transitivity (comp (g (F X)) (fmap H (comp (f' X) (f X)))).
  f_equiv.
  symmetry. apply (fmap_comp H).
  transitivity (comp (g (F X)) (fmap H (id _))).
  f_equiv.
  f_equiv.
  apply Hf2.
  transitivity (comp (g (F X)) (id _)).
  f_equiv.
  apply (fmap_id H).
  apply (ident_r C).
Defined.


Polymorphic Lemma CATAx: CatAx CATSig.
Proof.
  split.
  intros.

  destruct (@isomorphic_Equivalence (FUN X Y)) as [Hr Hs Ht].
  split.
  intros f. simpl. apply Hr.
  intros g f. simpl. apply Hs.
  intros h g f. simpl. apply Ht.

  intros X Y Z f1 f2 [fa [fb Hf]] g1 g2 [ga [gb Hg]].
  apply iso_isomorphic.
  apply natTransIsoCompH.
  refine {|
    iso_hom := fa;
    iso_inv := fb;
    iso_prop := Hf
  |}.
  refine {|
    iso_hom := ga;
    iso_inv := gb;
    iso_prop := Hg
  |}.

  intros X Y f.
  apply iso_isomorphic.
  apply (fun_iso (comp f (id X)) f (fun Z => id_iso _)).
  intros X' Y' f'. simpl.
  transitivity (fmap f f').
  refine (ident_r Y _ _ (fmap f f')).
  symmetry. refine (ident_l Y _ _ (fmap f f')).

  intros X Y f.
  apply iso_isomorphic.
  apply (fun_iso (comp (id Y) f) f (fun Z => id_iso _)).
  intros X' Y' f'. simpl.
  transitivity (fmap f f').
  refine (ident_r Y _ _ (fmap f f')).
  symmetry. refine (ident_l Y _ _ (fmap f f')).

  intros W X Y Z h g f.
  apply iso_isomorphic.
  apply (fun_iso (comp h (comp g f)) (comp (comp h g) f) (fun Z => id_iso _)).
  intros X' Y' f'. simpl.
  set (HH := fmap h (fmap g (fmap f f'))).
  transitivity HH.
  refine (ident_r Z _ _ HH).
  symmetry. refine (ident_l Z _ _ HH).
Qed.

Polymorphic Definition CAT: Cat := {|
  catAx := CATAx
|}.
