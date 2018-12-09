Require Import Category.
Require Import Functor.
Require Import Diagrams.
Require Import Limits.
Require Import CommaCategory.

Require Import Coq.Logic.Eqdep.


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


Polymorphic Inductive CiC_equalizer{X Y: CiC}(f g: Hom X Y): CiC :=
  cic_equalizer x: f x = g x -> CiC_equalizer f g.

Polymorphic Lemma CiC_equalizer_eq{X Y: CiC}{f g: Hom X Y}
  x1 x2 (H: x1 = x2) H1 H2:
  cic_equalizer f g x1 H1 = cic_equalizer f g x2 H2.
Proof.
  destruct H.
  f_equal.
  apply UIP.
Qed.

Definition cic_equalizer_cone{X Y: CiC}(f g: Hom X Y): Cone (equalizerFun f g).
  apply (@cone equalizer CiC (equalizerFun f g)
    (CiC_equalizer f g)
    (fun X' N =>
      match N with
      | cic_equalizer _ _ x _ => equalizer_ob_rect (equalizerFun f g) x (g x) X'
      end)).
  intros [] [] [] [x H]; simpl; try reflexivity.
  assumption.
Defined.

Definition cic_equalizer_hom{X Y: CiC}(f g: Hom X Y) N:
    Hom N (cic_equalizer_cone f g).
  refine (
    (fun H => coneHom N
                      (cic_equalizer_cone f g)
                      (fun xn => cic_equalizer f g (cone_Hom N equalizer_f xn) (H xn)) _) _).
  intros [|] x; simpl.
  symmetry. apply (cone_prop N equalizer_g).
  reflexivity.
  intro xn.
  transitivity (cone_Hom N equalizer_Y xn).
  apply (cone_prop N equalizer_f xn).
  symmetry.
  apply (cone_prop N equalizer_g xn).
Defined.

Definition cic_equalizer_lim{X Y: CiC}(f g: Hom X Y): Lim (equalizerFun f g).
  apply (lim _ (cic_equalizer_hom f g)).
  intros [Xn Yn fn] [f1 f2 Hf].
  simpl in * |- *. subst.
  split; try reflexivity. simpl.
  intros xn.
  generalize (Hf equalizer_f xn). simpl.
  destruct (f1 xn).
  intros H'.
  unfold cone_Hom. simpl.
  apply CiC_equalizer_eq.
  symmetry. assumption.
Defined.
