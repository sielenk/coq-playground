Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Eqdep.

Require Import Category.
Require Import Functor.
Require Import MetaCategory.
Require Import FunctorCategory.
Require Import NaturalTransformation.


Inductive twoOb : Type := twoX_ | twoY_.
Inductive twoHom: twoOb -> twoOb -> Type :=
  | twoIdX_: twoHom twoX_ twoX_
  | twoIdY_: twoHom twoY_ twoY_
  | twoF_  : twoHom twoX_ twoY_
  .

Definition no_twoYX(f: twoHom twoY_ twoX_): False :=
  match f in twoHom X' Y'
  return match X', Y' with twoY_, twoX_ => False | _, _ => True end
  with twoIdX_ => I | twoIdY_ => I | twoF_ => I end.

Lemma two_thin{X Y}(f1 f2: twoHom X Y): f1 = f2.
Proof.
  set (H X' Y' := match X', Y' return twoHom X' Y' -> twoHom X' Y' with
     | twoX_, twoX_ => fun _ => twoIdX_
     | twoX_, twoY_ => fun _ => twoF_
     | twoY_, twoY_ => fun _ => twoIdY_
     | twoY_, twoX_ => fun f => match no_twoYX f with end
     end).
  transitivity (H _ _ f1).
  destruct f1; reflexivity.
  destruct f2; reflexivity.
Qed.

Definition twoSig: CatSig := {|
  Ob             := twoOb;
  Hom            := twoHom;
  id X           := match X with
                    | twoX_ => twoIdX_
                    | twoY_ => twoIdY_
                    end;
  comp X Y Z g   := match g in twoHom Y' Z' return twoHom X Y' -> twoHom X Z' with
                    | twoIdX_ => fun f => f
                    | twoIdY_ => fun f => f
                    | twoF_   => match X with
                                 | twoX_ => fun f => twoF_
                                 | twoY_ => fun f => match no_twoYX f with end
                                 end
                    end;
  eq_h _ _       := eq
|}.

Lemma twoAx: CatAx twoSig.
Proof.
  split; try auto.
  intros X Y. apply eq_equivalence.
  intros X Y Z g1 g2 [] f1 f2 []. reflexivity.
  intros X Y []; reflexivity.
  intros X Y []; reflexivity.
  intros W X Y Z [] g f; try reflexivity.
  destruct f; try destruct (no_twoYX g).
  reflexivity.
Qed.

Definition two: Cat := {|
  catAx := twoAx
|}.

Polymorphic Definition twoFunSig{A: CatSig}{X Y: A}(f: Hom X Y): FunSig two A := {|
  fmap_o(X': two) := match X' with
                     | twoX_ => X
                     | twoY_ => Y
                     end;
  fmap X' Y'      := match X', Y' with
                     | twoX_, twoX_ => fun _ => id X
                     | twoX_, twoY_ => fun _ => f
                     | twoY_, twoY_ => fun _ => id Y
                     | twoY_, twoX_ => fun f => match no_twoYX f with end
                     end
|}.

Polymorphic Lemma twoFunAx{A: Cat}{X Y: A}(f: Hom X Y): FunAx (twoFunSig f).
Proof.
  split.
  intros X' Y' g1 g2 []. reflexivity.
  intros []; reflexivity.
  intros [] Y' Z' [] f'.
  symmetry. apply (ident_r A).
  symmetry. apply (ident_l A).
  symmetry. apply (ident_r A).
  destruct (no_twoYX f').
  symmetry. apply (ident_r A).
  destruct (no_twoYX f').
Qed.

Polymorphic Definition twoFun{A: Cat}{X Y: A}(f: Hom X Y): Fun two A := {|
  funAx := twoFunAx f
|}.

Definition twoX:   two           := twoX_.
Definition twoY:   two           := twoY_.
Definition twoIdX: Hom twoX twoX := twoIdX_.
Definition twoIdY: Hom twoY twoY := twoIdY_.
Definition twoF:   Hom twoX twoY := twoF_.


Definition equalizerSig: CatSig := {|
  Ob             := bool: Type;
  Hom X Y        := match X, Y with
                    | true, false => Empty_set
                    | false, true => bool
                    | _, _        => unit
                    end: Type;
  id X           := match X with
                    | false => tt
                    | true  => tt
                    end;
  comp X Y Z     := match X, Z with
                    | true, false => match Y with
                                     | true  => fun g _ => match g with end
                                     | false => fun _ f => match f with end
                                     end
                    | false, true => match Y with
                                     | true  => fun _ f => f
                                     | false => fun g _ => g
                                     end
                    | _, _        => fun _ _ => tt
                    end;
  eq_h _ _       := eq
|}.

Lemma equalizerAx: CatAx equalizerSig.
Proof.
  split.
  split; simpl; try auto.
  intros u v w H1 H2.
  transitivity v; assumption.
  intros X Y Z f f' Hf g g' Hg.
  f_equiv.
  apply Hf.
  apply Hg.
  intros [|] [|] []; reflexivity.
  intros [|] [|] []; reflexivity.
  intros [|] [|] [|] [|]; try reflexivity; simpl.
  intros [].
  intros [].
  intros _ _ [].
  intros _ [].
Qed.

Definition equalizer: Cat := {|
  catAx := equalizerAx
|}.

Definition equalizer_X:   equalizer                   := false.
Definition equalizer_Y:   equalizer                   := true.
Definition equalizer_idX: Hom equalizer_X equalizer_X := tt.
Definition equalizer_idY: Hom equalizer_Y equalizer_Y := tt.
Definition equalizer_f:   Hom equalizer_X equalizer_Y := false.
Definition equalizer_g:   Hom equalizer_X equalizer_Y := true.

Polymorphic Definition equalizerFunSig{A: CatSig}{X Y: A}(f g: Hom X Y):
    FunSig equalizerSig A := {|
  fmap_o     := fun(X': equalizer) => if X' then Y else X;
  fmap X' Y' := match X', Y' with
                | false, false => fun _ => id X
                | true, true   => fun _ => id Y
                | false, true  => fun f' => if f' then g else f
                | true, false  => fun f' => match f' with end
                end
|}.

Polymorphic Lemma equalizerFunAx{A: Cat}{X Y: A}(f g: Hom X Y):
    FunAx (equalizerFunSig f g).
Proof.
  split.
  intros X' Y' h h' []. reflexivity.
  intros [|]; reflexivity.
  intros [|] [|] [|] g' f'; simpl.
  symmetry. apply (ident_r A).
  destruct g'.
  destruct f'.
  destruct f'.
  symmetry. apply (ident_l A).
  destruct g'.
  symmetry. apply (ident_r A).
  symmetry. apply (ident_r A).
Qed.

Polymorphic Definition equalizerFun{A: Cat}{X Y: A}(f g: Hom X Y):
    Fun equalizer A := {|
  funAx := equalizerFunAx f g
|}.



Definition pullbackSig: CatSig := {|
  Ob             := option bool: Type;
  Hom X Y        := match X, Y with
                    | None, Some _          => Empty_set
                    | Some true, Some false => Empty_set
                    | Some false, Some true => Empty_set
                    | _, _                  => unit
                    end: Type;
  id X           := match X with
                    | None       => tt
                    | Some false => tt
                    | Some true  => tt
                    end;
  comp X Y Z     := match X, Y, Z with
                    | None, Some _, _          => fun _ f => match f with end
                    | Some true, Some false, _ => fun _ f => match f with end
                    | Some false, Some true, _ => fun _ f => match f with end
                    | _, None, Some _          => fun g _ => match g with end
                    | _, Some true, Some false => fun g _ => match g with end
                    | _, Some false, Some true => fun g _ => match g with end
                    | _, _, _                  => fun _ _ => tt
                    end;
  eq_h _ _       := eq
|}.

Lemma pullbackAx: CatAx pullbackSig.
Proof.
  split. 
  intros X Y. apply eq_equivalence.
  intros X Y Z g1 g2 [] f1 f2 []. reflexivity.
  intros [[]|] [[]|] []; reflexivity.
  intros [[]|] [[]|] []; reflexivity.
  intros [[]|] [[]|] [[]|] [[]|] [] [] []; reflexivity.
Qed.

Definition pullback: Cat := {|
  catAx := pullbackAx
|}.

Definition pullback_Xf:   pullback                    := Some false.
Definition pullback_Xg:   pullback                    := Some true.
Definition pullback_Y:    pullback                    := None.
Definition pullback_idXf: Hom pullback_Xf pullback_Xf := tt.
Definition pullback_idXg: Hom pullback_Xg pullback_Xg := tt.
Definition pullback_idY:  Hom pullback_Y  pullback_Y  := tt.
Definition pullback_f:    Hom pullback_Xf pullback_Y  := tt.
Definition pullback_g:    Hom pullback_Xg pullback_Y  := tt.

Polymorphic Definition pullbackFunSig{A: CatSig}{Xf Xg Y: A}(f: Hom Xf Y)(g: Hom Xg Y):
    FunSig pullbackSig A := {|
  fmap_o     := fun(X': pullback)=> match X' with
                | Some false => Xf
                | Some true  => Xg
                | None       => Y
                end;
  fmap X' Y' := match X', Y' with
                | Some false, Some false => fun _ => id Xf
                | Some true, Some true   => fun _ => id Xg
                | None, None             => fun _ => id Y
                | Some false, None       => fun _ => f
                | Some true, None        => fun _ => g
                | _, _                   => fun f => match f with end
                end
|}.

Polymorphic Lemma pullbackFunAx{A: Cat}{Xf Xg Y: A}(f: Hom Xf Y)(g: Hom Xg Y):
    FunAx (pullbackFunSig f g).
Proof.
  split.
  intros [[|]|] [[|]|]; simpl; intros [] u' H; reflexivity.
  intros [[|]|]; simpl; reflexivity.
  intros [[|]|] [[|]|] [[|]|]; simpl; intros [] []; symmetry;
    try apply (ident_r A); apply (ident_l A).
Qed.

Polymorphic Definition pullbackFun{A: Cat}{Xf Xg Y: A}(f: Hom Xf Y)(g: Hom Xg Y):
    Fun pullbackSig A := {|
  funAx := pullbackFunAx f g
|}.



Polymorphic Definition productSig(I: Type): CatSig := {|
  Ob             := I;
  Hom X Y        := X = Y: Type;
  id X           := eq_refl X;
  comp X Y Z g f := eq_trans f g;
  eq_h _ _       := eq
|}.

Polymorphic Lemma productAx(I: Type): CatAx (productSig I).
Proof.
  split; simpl; try auto.
  intros X Y. apply eq_equivalence.
  intros X Y Z g1 g2 [] f1 f2 []. reflexivity.
  intros X Y []. reflexivity.
  intros W X Y Z [] [] []. reflexivity.
Qed.

Polymorphic Definition product(I: Type): Cat := {|
  catAx := productAx I
|}.

Polymorphic Definition productFunSig{I: Type}{A: CatSig}(Xi: I -> A):
    FunSig (productSig I) A := {|
  fmap_o       := Xi: product I -> A;
  fmap I1 I2 H := match H in _ = I2' with eq_refl => id _ end
|}.

Polymorphic Lemma productFunAx{I: Type}{A: Cat}(Xi: I -> A):
    FunAx (productFunSig Xi).
Proof.
  split; simpl; try reflexivity.
  intros Y Z [] H [].
  reflexivity.
  intros W Y Z [] []. simpl.
  symmetry. apply (ident_r A).
Qed.

Polymorphic Definition productFun{I: Type}{A: Cat}(Xi: I -> A):
    Fun (productSig I) A := {|
  funAx := productFunAx Xi
|}.


Inductive ZeroOb: Type := .
Definition zero: Cat := product ZeroOb.
Polymorphic Definition zeroFun(A: Cat): Fun zero A :=
  productFun (fun I: zero => match I with end).


Inductive OneOb: Type := oneOb_.
Definition one: Cat := product OneOb.

Definition oneX:   one           := oneOb_.
Definition oneIdX: Hom oneX oneX := eq_refl.

Definition oneHom{X Y: one}: Hom X Y.
  destruct X, Y. reflexivity.
Defined.

Polymorphic Definition oneFunSig(A: Cat): FunSig A (FUN one A).
  set (fmap_o X := productFun (fun I: one => X): FUN one A).
  refine {|
    fmap_o     := fmap_o;
    fmap X Y f := {|
      natTrans Z := f: Hom (fmap_o X Z) (fmap_o Y Z);
    |}
  |}.

  intros X' Y' []. simpl.
  transitivity f.
  apply (ident_l A).
  symmetry. apply (ident_r A).
Defined.

Polymorphic Lemma oneFunAx(A: Cat): FunAx (oneFunSig A).
Proof.
  split.
  intros X Y f1 f2 Hf X'. assumption.
  intros X X'. reflexivity.
  intros X Y Z g f X'. reflexivity.
Qed.

Polymorphic Definition oneFun(A: Cat): Fun A (FUN one A) := {|
  funAx := oneFunAx A
|}.

Lemma one_thin: thin one.
Proof.
  intros X Y.
  apply UIP.
Qed.

Definition oneOb_isomorphic(X Y: one): Iso X Y.
  destruct X, Y.
  refine {|
    iso_hom := oneHom;
    iso_inv := oneHom
  |}.
  split; reflexivity.
Defined.


Definition zero_initial: initial (zero: CAT).
  refine {|
    initial_hom(Y: CAT) := zeroFun Y: @Hom CAT zero Y
  |}.
  intros A F.
  eexists.
  eexists.
  split; intros [].

  Unshelve.

  refine {| natTrans(X: zero) := match X with end |}.
  intros [].

  refine {| natTrans(X: zero) := match X with end |}.
  intros [].
Defined.


Polymorphic Definition oneTerminalFunSig(A: CatSig): FunSig A one := {|
  fmap_o(_: A) := oneX;
  fmap _ _ _   := oneIdX
|}.

Polymorphic Lemma oneTerminalFunAx(A: CatSig): FunAx (oneTerminalFunSig A).
Proof.
  split.
  intros X Y f1 f2 Hf. reflexivity.
  intros X. reflexivity.
  intros X Y Z g f. reflexivity.
Qed.

Polymorphic Definition oneTerminalFun(A: CatSig): Fun A one := {|
  funAx := oneTerminalFunAx A
|}.

Definition one_terminal: terminal (one: CAT).
  refine {|
    terminal_hom(A: CAT) := oneTerminalFun A: @Hom CAT A one
  |}.
  intros A F.

  apply iso_isomorphic.
  apply (fun_iso (oneTerminalFun A) F (fun X: A => oneOb_isomorphic _ _)).

  intros X Y f.
  generalize (fmap F f). intros [].
  generalize (fmap (oneTerminalFun A) f). intros [].
  generalize (oneOb_isomorphic ((oneTerminalFun A) X) (F X)). intros [[]].
  reflexivity.
Defined.
