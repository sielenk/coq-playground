Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Eqdep.


Require Import Category.
Require Import Functor.
Require Import FunctorCategory.
Require Import Diagrams.


Section comma_category.
  Polymorphic Variables A B C: Cat.
  Polymorphic Variable  S: Fun A C.
  Polymorphic Variable  T: Fun B C.

  Polymorphic Record CommaOb := {
    commaOb_X;
    commaOb_Y;
    commaOb_f: Hom (S commaOb_X) (T commaOb_Y)
  }.

  Polymorphic Record CommaHom X Y := {
    commaHom_fst: Hom (commaOb_X X) (commaOb_X Y);
    commaHom_snd: Hom (commaOb_Y X) (commaOb_Y Y);
    commaHom_prop: eq_h (comp (commaOb_f Y) (fmap S commaHom_fst))
                        (comp (fmap T commaHom_snd) (commaOb_f X))
  }.

  Global Arguments commaHom_fst {_ _}.
  Global Arguments commaHom_snd {_ _}.
  Global Arguments commaHom_prop{_ _}.

  Polymorphic Definition comma_id X: CommaHom X X.
    refine {|
      commaHom_fst := id _;
      commaHom_snd := id _
    |}.
    transitivity (comp (commaOb_f X) (id (S (commaOb_X X)))).
    f_equiv.
    apply (fmap_id S).
    transitivity (commaOb_f X).
    apply (ident_r C).
    symmetry.
    transitivity (comp (id (T (commaOb_Y X))) (commaOb_f X)).
    f_equiv.
    apply (fmap_id T).
    apply (ident_l C).
  Defined.

  Polymorphic Definition comma_comp{X Y Z}(g: CommaHom Y Z)(f: CommaHom X Y): CommaHom X Z.
    refine {|
      commaHom_fst := comp (commaHom_fst g) (commaHom_fst f);
      commaHom_snd := comp (commaHom_snd g) (commaHom_snd f)
    |}.
    transitivity (comp (commaOb_f Z) (comp (fmap S (commaHom_fst g)) (fmap S (commaHom_fst f)))).
    f_equiv.
    apply (fmap_comp S).
    transitivity (comp (comp (commaOb_f Z) (fmap S (commaHom_fst g))) (fmap S (commaHom_fst f))).
    apply (assoc C).
    transitivity (comp (comp (fmap T (commaHom_snd g)) (commaOb_f Y)) (fmap S (commaHom_fst f))).
    f_equiv.
    apply commaHom_prop.
    transitivity (comp (fmap T (commaHom_snd g)) (comp (commaOb_f Y) (fmap S (commaHom_fst f)))).
    symmetry.
    apply (assoc C).
    transitivity (comp (comp (fmap T (commaHom_snd g)) (fmap T (commaHom_snd f))) (commaOb_f X)).
    transitivity (comp (fmap T (commaHom_snd g)) (comp (fmap T (commaHom_snd f)) (commaOb_f X))).
    f_equiv.
    apply commaHom_prop.
    apply (assoc C).
    f_equiv.
    symmetry.
    apply (fmap_comp T).
  Defined.

  Polymorphic Definition comma_eq_h X Y: relation (CommaHom X Y) :=
    fun f g => eq_h (commaHom_fst f) (commaHom_fst g) /\
               eq_h (commaHom_snd f) (commaHom_snd g).

  Polymorphic Definition CommaCatSig: CatSig := {|
    id         := comma_id;
    comp _ _ _ := comma_comp;
    eq_h       := comma_eq_h
  |}.

  Polymorphic Lemma CommaCatAx: CatAx CommaCatSig.
  Proof.
    split.
    intros X Y. split.
    intros [f g].
    split; simpl; reflexivity.
    intros [f g] [f' g'] [Hf Hg]. simpl in Hf, Hg.
    split; simpl; symmetry; assumption.
    intros [f g] [f' g'] [f'' g''] [Hf Hg] [Hf' Hg'].
    simpl in Hf, Hg, Hf', Hg'.
    split; simpl; [transitivity f' | transitivity g']; assumption.
    intros X Y Z g g' [Hg Hg'] f f' [Hf Hf'].
    split; simpl; [
      transitivity (comp (commaHom_fst g) (commaHom_fst f')) |
      transitivity (comp (commaHom_snd g) (commaHom_snd f'))]; f_equiv; assumption.
    intros X Y [f f']. split; simpl.
    apply (ident_r A).
    apply (ident_r B).
    intros X Y [f f']. split; simpl.
    apply (ident_l A).
    apply (ident_l B).
    intros X Y Z [h h'] [g g'] [f f']. split; simpl.
    apply (assoc A).
    apply (assoc B).
  Qed.

  Polymorphic Definition CommaCat: Cat := {|
    catAx := CommaCatAx
  |}.

  Polymorphic Definition CommaDomFunSig: FunSig CommaCat A := {|
    fmap_o   := commaOb_X: CommaCat -> A;
    fmap _ _ := commaHom_fst
  |}.

  Polymorphic Lemma CommaDomFunAx: FunAx CommaDomFunSig.
  Proof.
    split.
    intros X Y f f' [Hf _].
    apply Hf.
    intros. reflexivity.
    intros. reflexivity.
  Qed.

  Polymorphic Definition CommaDomFun: Fun CommaCat A := {|
    funAx := CommaDomFunAx
  |}.


  Polymorphic Definition CommaCodFunSig: FunSig CommaCat B := {|
    fmap_o   := commaOb_Y: CommaCat -> B;
    fmap _ _ := commaHom_snd
  |}.

  Polymorphic Lemma CommaCodFunAx: FunAx CommaCodFunSig.
  Proof.
    split.
    intros X Y f f' [_ Hf'].
    apply Hf'.
    intros. reflexivity.
    intros. reflexivity.
  Qed.

  Polymorphic Definition CommaCodFun: Fun CommaCat B := {|
    funAx := CommaCodFunAx
  |}.


  Polymorphic Definition CommaHomFunSig: FunSig CommaCat (FUN two C).
    refine {|
      fmap_o(X: Ob CommaCat) := twoFun (commaOb_f X): Ob (FUN two C)
    |}.
    intros X Y [f1 f2 Hf].
    set (g1 := commaOb_f X)in Hf |- *.
    set (g2 := commaOb_f Y)in Hf |- *.
    refine {| natTrans := two_ob_rect
                            (fun X' => Hom (twoFun g1 X') (twoFun g2 X'))
                            (fmap S f1)
                            (fmap T f2)
    |}.
    unfold natural.
    apply two_hom_rect.
    apply Hf.
    apply two_ob_rect.
    transitivity (fmap S f1).
    apply (ident_l C).
    symmetry. apply (ident_r C).
    transitivity (fmap T f2).
    apply (ident_l C).
    symmetry; apply (ident_r C).
  Defined.

  Polymorphic Lemma CommaHomFunAx: FunAx CommaHomFunSig.
  Proof.
    split.
    intros X Y [f1a f1b Hf1] [f2a f2b Hf2] [Hfa Hfb] [|]; simpl in Hfa, Hfb |- *.
    apply (fmap_eq T). assumption.
    apply (fmap_eq S). assumption.
    intros X [|].
    apply (fmap_id T).
    apply (fmap_id S).
    intros X Y Z [g1 g2 Hg] [f1 f2 Hf] [|]; simpl.
    apply (fmap_comp T).
    apply (fmap_comp S).
  Qed.

  Polymorphic Definition CommaHomFun: Fun CommaCat (FUN two C) := {|
    funAx := CommaHomFunAx
  |}.
End comma_category.

Arguments CommaCat{_ _ _}.
Arguments CommaOb{_ _ _}.
Arguments commaOb_X{_ _ _ _ _}.
Arguments commaOb_Y{_ _ _ _ _}.
Arguments commaOb_f{_ _ _ _ _}.
Arguments commaHom_fst{_ _ _ _ _ _ _}.
Arguments commaHom_snd{_ _ _ _ _ _ _}.
Arguments CommaCodFun{_ _ _}.
Arguments CommaDomFun{_ _ _}.
Arguments CommaHomFun{_ _ _}.
