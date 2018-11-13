Require Export Coq.Classes.Morphisms.

Require Export Category.


Polymorphic Record FunSig(A B: CatSig) := {
  fmap_o  :> A -> B;
  fmap X Y:  Hom X Y -> Hom (fmap_o X) (fmap_o Y)
}.

Global Arguments fmap_o {_ _}.
Global Arguments fmap   {_ _} _ {_ _}.

Polymorphic Record FunAx{A B: CatSig}(F: FunSig A B): Prop := {
  fmap_eq  : forall X Y, Proper (eq_h ==> eq_h) (@fmap A B F X Y);
  fmap_id  : forall X, eq_h (fmap F (id X)) (id (F X));
  fmap_comp: forall X Y Z (g: Hom Y Z)(f: Hom X Y),
                 eq_h (fmap F (comp g f))
                      (comp (fmap F g) (fmap F f))
}.

Global Arguments fmap_eq   {_ _ _} _ {_ _}.
Global Arguments fmap_id   {_ _ _} _ {_}.
Global Arguments fmap_comp {_ _ _} _ {_ _ _}.

Polymorphic Record Fun(A B: CatSig): Type := {
  funSig :> FunSig A B;
  funAx  :> FunAx funSig
}.

Polymorphic Instance fmap_eq_Proper{A B}{F: Fun A B}{X Y}: Proper (eq_h ==> eq_h) (@fmap A B F X Y) :=
  fmap_eq F.


Polymorphic Definition faithful{A B}(F: FunSig A B): Prop :=
  forall X Y (f f': Hom X Y), eq_h (fmap F f) (fmap F f') -> eq_h f f'.

Polymorphic Definition full{A B}(F: FunSig A B): Prop :=
  forall X Y (f: Hom (F X) (F Y)), exists f', f = fmap F f'.


Lemma reflect_CatAx{A}{B: Cat}(F: Fun A B): faithful F -> CatAx A.
Proof.
  intro H.
  split.
  intros X Y; split; simpl.
  intro f. apply H. reflexivity.
  intros f g H'. apply H.
  symmetry.
  apply (fmap_eq F). assumption.
  intros f g h H1 H2. apply H.
  transitivity (fmap F g);
  apply (fmap_eq F); assumption.
  intros X Y Z g1 g2 Hg f1 f2 Hf. apply H.
  transitivity (comp (fmap F g1) (fmap F f1)).
  apply (fmap_comp F).
  transitivity (comp (fmap F g2) (fmap F f2)).
  f_equiv; apply (fmap_eq F); assumption.
  symmetry. apply (fmap_comp F).
  intros X Y f. apply H.
  transitivity (comp (fmap F f) (fmap F (id X))).
  apply (fmap_comp F).
  transitivity (comp (fmap F f) (id _)).
  f_equiv.
  apply (fmap_id F).
  apply (ident_r B).
  intros X Y f. apply H.
  transitivity (comp (fmap F (id Y)) (fmap F f)).
  apply (fmap_comp F).
  transitivity (comp (id _) (fmap F f)).
  f_equiv.
  apply (fmap_id F).
  apply (ident_l B).
  intros. apply H.
  transitivity (comp (fmap F h) (comp (fmap F g) (fmap F f))).
  transitivity (comp (fmap F h) (fmap F (comp g f))).
  apply (fmap_comp F).
  f_equiv.
  apply (fmap_comp F).
  transitivity (comp (comp (fmap F h) (fmap F g)) (fmap F f)).
  apply (assoc B).
  transitivity (comp (fmap F (comp h g)) (fmap F f)).
  f_equiv.
  symmetry. apply (fmap_comp F).
  symmetry. apply (fmap_comp F).
Qed.
