Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Eqdep.

Require Import Category.
Require Import Functor.




Definition zeroSig: CatSig := {|
  Ob             := Empty_set: Type;
  Hom _ _        := Empty_set: Type;
  id X           := match X with end;
  comp _ Y _ _ _ := match Y with end;
  eq_h _ _ _ _   := True
|}.

Lemma zeroAx: CatAx zeroSig.
Proof.
  split; simpl; intros [].
Qed.

Definition zero: Cat := {| catAx := zeroAx |}.

Polymorphic Definition zeroFunSig A: FunSig zeroSig A := {|
  fmap_o(X: Ob zero) := match X with end;
  fmap X Y f         := match f with end
|}.

Polymorphic Lemma zeroFunAx A: FunAx (zeroFunSig A).
Proof.
  split; simpl; intros [].
Qed.

Polymorphic Definition zeroFun A: Fun zeroSig A :=
  {| funAx := zeroFunAx A |}.



Definition oneSig: CatSig := {|
  Ob             := unit: Type;
  Hom _ _        := unit: Type;
  id _           := tt;
  comp _ _ _ _ _ := tt;
  eq_h _ _ _ _   := True
|}.

Lemma oneAx: CatAx oneSig.
Proof.
  split; simpl; split; repeat intros []; try apply I.
Qed.

Definition one: Cat := {| catAx := oneAx |}.

Polymorphic Definition oneFunSig{A: CatSig}(X: Ob A): FunSig one A := {|
  fmap_o _   := X;
  fmap _ _ _ := id X
|}.

Polymorphic Lemma oneFunAx{A: Cat}(W: Ob A): FunAx (oneFunSig W).
Proof.
  split; simpl; intros.
  intros f f' Hf.
  reflexivity.
  reflexivity.
  symmetry. apply (ident_r A).
Qed.

Polymorphic Definition oneFun{A: Cat}(X: Ob A): Fun one A := {|
  funAx := oneFunAx X
|}.



Definition twoSig: CatSig := {|
  Ob             := bool: Type;
  Hom X Y        := match X, Y with
                    | true, false => Empty_set
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
                    | _, _        => fun _ _ => tt
                    end;
  eq_h _ _ _ _   := True
|}.

Lemma twoAx: CatAx twoSig.
Proof.
  split; simpl; try auto.
  intros X Y; split; auto.
  intros X Y Z _ _ _ _ _ _. auto.
Qed.

Definition two: Cat := {|
  catAx := twoAx
|}.

Polymorphic Definition twoFunSig{A: CatSig}{X Y: A}(f: Hom X Y): FunSig two A := {|
  fmap_o     := fun(X': two) => if X' then Y else X;
  fmap X' Y' := match X', Y' with
                | false, false => fun _ => id X
                | true, true   => fun _ => id Y
                | false, true  => fun _ => f
                | true, false  => fun f' => match f' with end
                end
|}.

Polymorphic Lemma twoFunAx{A: Cat}{X Y: A}(f: Hom X Y): FunAx (twoFunSig f).
Proof.
  split.
  intros [|] [|] f1 f2 Hf; simpl; try reflexivity.
  destruct f1.
  intros [|]; reflexivity.
  intros [|] [|] [|] g' f'; simpl.
  symmetry.
  apply (ident_r A).
  destruct g'.
  destruct f'.
  destruct f'.
  symmetry.
  apply (ident_l A).
  destruct g'.
  symmetry.
  apply (ident_r A).
  symmetry.
  apply (ident_r A).
Qed.

Polymorphic Definition twoFun{A: Cat}{X Y: A}(f: Hom X Y): Fun two A :=
  {| funAx := twoFunAx f |}.



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

Polymorphic Definition equalizerFunSig{A: CatSig}{X Y: A}(f g: Hom X Y):
    FunSig equalizerSig A := {|
  fmap_o     := fun(X': equalizer) => if X' then Y else X;
  fmap X' Y' := match X', Y' with
                | false, false => fun _ => id X
                | true, true   => fun _ => id Y
                | false, true  => fun f' => if f' then f else g
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
  eq_h _ _ _ _   := True
|}.

Lemma pullbackAx: CatAx pullbackSig.
Proof.
  split; simpl; try auto.
  intros X Y; split; auto.
  intros X Y Z _ _ _ _ _ _. auto.
Qed.

Definition pullback: Cat := {|
  catAx := pullbackAx
|}.

Polymorphic Definition pullbackFunSig{A: CatSig}{X1 X2 Y: A}(f: Hom X1 Y)(g: Hom X2 Y):
    FunSig pullbackSig A := {|
  fmap_o     := fun(X': pullback)=> match X' with
                | Some false => X1
                | Some true  => X2
                | None       => Y
                end;
  fmap X' Y' := match X', Y' with
                | Some false, Some false => fun _ => id X1
                | Some true, Some true   => fun _ => id X2
                | None, None             => fun _ => id Y
                | Some false, None       => fun _ => f
                | Some true, None        => fun _ => g
                | _, _                   => fun f => match f with end
                end
|}.

Polymorphic Lemma pullbackFunAx{A: Cat}{X1 X2 Y: A}(f: Hom X1 Y)(g: Hom X2 Y):
    FunAx (pullbackFunSig f g).
Proof.
  split.
  intros [[|]|] [[|]|]; simpl; intros [] u' H; reflexivity.
  intros [[|]|]; simpl; reflexivity.
  intros [[|]|] [[|]|] [[|]|]; simpl; intros [] []; symmetry;
    try apply (ident_r A); apply (ident_l A).
Qed.

Polymorphic Definition pullbackFun{A: Cat}{X1 X2 Y: A}(f: Hom X1 Y)(g: Hom X2 Y):
    Fun pullbackSig A := {|
  funAx := pullbackFunAx f g
|}.



Polymorphic Definition productSig(I: Type): CatSig := {|
  Ob             := I;
  Hom X Y        := X = Y: Type;
  id X           := eq_refl X;
  comp X Y Z g f := eq_trans f g;
  eq_h _ _ _ _   := True
|}.

Polymorphic Lemma productAx(I: Type): CatAx (productSig I).
Proof.
  split; simpl; try auto.
  intros X Y; split; auto.
  intros X Y Z _ _ _ _ _ _. auto.
Qed.

Polymorphic Definition product(I: Type): Cat := {|
  catAx := productAx I
|}.

Polymorphic Definition productFunSig{I: Type}{A: CatSig}(X: I -> A):
    FunSig (productSig I) A := {|
  fmap_o       := X: product I -> A;
  fmap I1 I2 H := match H in _ = I2' with eq_refl => id _ end
|}.

Polymorphic Lemma productFunAx{I: Type}{A: Cat}(X: I -> A):
    FunAx (productFunSig X).
Proof.
  split; simpl; try reflexivity.
  intros Y Z [] H _.
  rewrite (UIP_refl I Y H). reflexivity.
  intros W Y Z [] []. simpl.
  symmetry. apply (ident_r A).
Qed.

Polymorphic Definition productFun{I: Type}{A: Cat}(X: I -> A):
    FunSig (productSig I) A := {|
  funAx := productFunAx X
|}.
