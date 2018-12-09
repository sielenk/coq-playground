Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Eqdep.

Require Import Category.
Require Import Functor.
Require Import MetaCategory.
Require Import FunctorCategory.
Require Import NaturalTransformation.


Definition twoSig: CatSig := {|
  Ob         := bool;
  Hom X Y    := match X, Y with
                | true, false => Empty_set
                | _, _        => unit
                end;
  id X       := match X with false => tt | true => tt end;
  comp X Y Z := match X, Z with
                | true, false => match Y with
                                 | false => fun _ f => match f with end
                                 | true  => fun g _ => match g with end
                                 end
                | _, _        => fun _ _ => tt
                end;
  eq_h _ _   := eq
|}.

Lemma twoAx: CatAx twoSig.
Proof.
  split; try auto.
  intros X Y. apply eq_equivalence.
  intros X Y Z g1 g2 [] f1 f2 []. reflexivity.
  intros [] [] []; reflexivity.
  intros [] [] []; reflexivity.
  intros [] [] [] [] [] g f; try reflexivity.
  destruct f.
Qed.

Definition two: Cat := {|
  catAx := twoAx
|}.

Definition two_X: two             := false.
Definition two_Y: two             := true.
Definition two_f: Hom two_X two_Y := tt.

Polymorphic Definition two_ob_rect
    (P: two -> Type)
    (Px: P two_X)
    (Py: P two_Y)
    X:
    P X :=
  match X return P X with false => Px | true => Py end.

Polymorphic Definition two_hom_rect
    (P: forall X Y: two, Hom X Y -> Type)
    (Pf: P _ _ two_f)
    (Pid: forall X, P _ _ (id X)):
    forall X Y f, P X Y f.
  intros [] [] []; try apply Pid.
  apply Pf.
Defined.

Polymorphic Definition twoFunSig{A: CatSig}{X Y: A}(f: Hom X Y): FunSig two A :=
  let map := two_ob_rect (fun _ => A) X Y in {|
    fmap_o := map;
    fmap   := two_hom_rect (fun X Y f => Hom (map X) (map Y))
                           f (fun X => id (map X))
  |}.

Polymorphic Lemma twoFunAx{A: Cat}{X Y: A}(f: Hom X Y): FunAx (twoFunSig f).
Proof.
  split.
  intros X' Y' g1 g2 []. reflexivity.
  intros []; reflexivity.
  intros [] [] [] [] []; symmetry; try apply (ident_l A).
  apply (ident_r A).
Qed.

Polymorphic Definition twoFun{A: Cat}{X Y: A}(f: Hom X Y): Fun two A := {|
  funAx := twoFunAx f
|}.

Polymorphic Lemma twoFun_X{A: Cat}{X Y: A}(f: Hom X Y): twoFun f two_X = X.
Proof.
  reflexivity.
Qed.

Polymorphic Lemma twoFun_Y{A: Cat}{X Y: A}(f: Hom X Y): twoFun f two_Y = Y.
Proof.
  reflexivity.
Qed.

Polymorphic Lemma twoFun_f{A: Cat}{X Y: A}(f: Hom X Y): fmap (twoFun f) two_f = f.
Proof.
  reflexivity.
Qed.


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
Definition equalizer_f:   Hom equalizer_X equalizer_Y := false.
Definition equalizer_g:   Hom equalizer_X equalizer_Y := true.

Polymorphic Definition equalizer_ob_rect
    (P: equalizer -> Type)
    (Px: P equalizer_X)
    (Py: P equalizer_Y)
    X:
    P X :=
  if X return P X then Py else Px.

Polymorphic Definition equalizer_hom_rect
    (P: forall X Y: equalizer, Hom X Y -> Type)
    (Pf: P _ _ equalizer_f)
    (Pg: P _ _ equalizer_g)
    (Pid: forall X, P _ _ (id X)):
    forall X Y f, P X Y f.
  intros [|] [|] []; try apply Pid.
  apply Pg.
  apply Pf.
Defined.

Polymorphic Definition equalizerFunSig{A: CatSig}{X Y: A}(f g: Hom X Y):
    FunSig equalizerSig A :=
  let map := equalizer_ob_rect (fun _ => A) X Y in {|
    fmap_o := map;
    fmap   := equalizer_hom_rect
                (fun X Y _ => Hom (map X) (map Y))
                f g (fun X => id (map X))
|}.

Polymorphic Lemma equalizerFunAx{A: Cat}{X Y: A}(f g: Hom X Y):
    FunAx (equalizerFunSig f g).
Proof.
  split.
  intros X' Y' h h' []. reflexivity.
  intros [|]; reflexivity.
  intros [|] [|] [|] g' f'; simpl.
  destruct g', f'.
  symmetry. apply (ident_r A).
  destruct g'.
  destruct f'.
  destruct f'.
  destruct g'.
  symmetry. apply (ident_l A).
  destruct g'.
  destruct f'.
  symmetry. apply (ident_r A).
  destruct g', f'.
  symmetry. apply (ident_r A).
Qed.

Polymorphic Definition equalizerFun{A: Cat}{X Y: A}(f g: Hom X Y):
    Fun equalizer A := {|
  funAx := equalizerFunAx f g
|}.

Polymorphic Lemma equalizerFun_X{A: Cat}{X Y: A}(f g: Hom X Y):
  equalizerFun f g equalizer_X = X.
Proof.
  reflexivity.
Qed.

Polymorphic Lemma equalizerFun_Y{A: Cat}{X Y: A}(f g: Hom X Y):
  equalizerFun f g equalizer_Y = Y.
Proof.
  reflexivity.
Qed.

Polymorphic Lemma equalizerFun_f{A: Cat}{X Y: A}(f g: Hom X Y):
  fmap (equalizerFun f g) equalizer_f = f.
Proof.
  reflexivity.
Qed.

Polymorphic Lemma equalizerFun_g{A: Cat}{X Y: A}(f g: Hom X Y):
  fmap (equalizerFun f g) equalizer_g = g.
Proof.
  reflexivity.
Qed.


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
Definition pullback_f:    Hom pullback_Xf pullback_Y  := tt.
Definition pullback_g:    Hom pullback_Xg pullback_Y  := tt.

Polymorphic Definition pullback_ob_rect
    (P: pullback -> Type)
    (Pxf: P pullback_Xf)
    (Pxg: P pullback_Xg)
    (Py: P pullback_Y)
    (X: pullback):
    P X :=
  match X with
  | None    => Py
  | Some X' => match X' with
               | false => Pxf
               | true  => Pxg
               end
  end.

Polymorphic Definition pullback_hom_rect
    (P: forall X Y: pullback, Hom X Y -> Type)
    (Pf: P _ _ pullback_f)
    (Pg: P _ _ pullback_g)
    (Pid: forall X, P _ _ (id X)):
    forall X Y f, P X Y f.
  intros [[]|] [[]|] []; try apply Pid; assumption.
Defined.


Polymorphic Definition pullbackFunSig{A: CatSig}{Xf Xg Y: A}(f: Hom Xf Y)(g: Hom Xg Y):
    FunSig pullbackSig A :=
  let map := pullback_ob_rect (fun _ => A) Xf Xg Y in {|
  fmap_o := map;
  fmap   := pullback_hom_rect (fun X Y f => Hom (map X) (map Y))
                              f g (fun X => id (map X))
|}.

Polymorphic Lemma pullbackFunAx{A: Cat}{Xf Xg Y: A}(f: Hom Xf Y)(g: Hom Xg Y):
    FunAx (pullbackFunSig f g).
Proof.
  split.
  intros [[|]|] [[|]|]; simpl; intros [] [] H; reflexivity.
  intros [[|]|]; simpl; reflexivity.
  intros [[|]|] [[|]|] [[|]|]; simpl; intros [] []; symmetry;
    try apply (ident_r A); apply (ident_l A).
Qed.

Polymorphic Definition pullbackFun{A: Cat}{Xf Xg Y: A}(f: Hom Xf Y)(g: Hom Xg Y):
    Fun pullback A := {|
  funAx := pullbackFunAx f g
|}.

Polymorphic Lemma pullbackFun_Xf{A: Cat}{Xf Xg Y: A}(f: Hom Xf Y)(g: Hom Xg Y):
  pullbackFun f g pullback_Xf = Xf.
Proof.
  reflexivity.
Qed.

Polymorphic Lemma pullbackFun_Xg{A: Cat}{Xf Xg Y: A}(f: Hom Xf Y)(g: Hom Xg Y):
  pullbackFun f g pullback_Xg = Xg.
Proof.
  reflexivity.
Qed.

Polymorphic Lemma pullbackFun_Y{A: Cat}{Xf Xg Y: A}(f: Hom Xf Y)(g: Hom Xg Y):
  pullbackFun f g pullback_Y = Y.
Proof.
  reflexivity.
Qed.

Polymorphic Lemma pullbackFun_f{A: Cat}{Xf Xg Y: A}(f: Hom Xf Y)(g: Hom Xg Y):
  fmap (pullbackFun f g) pullback_f = f.
Proof.
  reflexivity.
Qed.

Polymorphic Lemma pullbackFun_g{A: Cat}{Xf Xg Y: A}(f: Hom Xf Y)(g: Hom Xg Y):
  fmap (pullbackFun f g) pullback_g = g.
Proof.
  reflexivity.
Qed.


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

Polymorphic Lemma productFun_I{I: Type}{A: Cat}(Xi: I -> A)(i: product I):
  productFun Xi i = Xi i.
Proof.
  reflexivity.
Qed.


Inductive ZeroOb: Type := .
Definition zero: Cat := product ZeroOb.
Polymorphic Definition zeroFun(A: Cat): Fun zero A :=
  productFun (fun I: zero => match I with end).


Inductive OneOb: Type := oneOb_.
Definition one: Cat := product OneOb.

Definition one_X:   one             := oneOb_.
Definition one_idX: Hom one_X one_X := eq_refl.

Definition one_f{X Y: one}: Hom X Y.
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

Polymorphic Lemma oneFun_X{A: Cat}(X: A):
  oneFun A X one_X = X.
Proof.
  reflexivity.
Qed.


Lemma one_thin: thin one.
Proof.
  intros X Y.
  apply UIP.
Qed.

Definition oneOb_isomorphic(X Y: one): Iso X Y.
  destruct X, Y.
  refine {|
    iso_hom := one_idX;
    iso_inv := one_idX
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
  fmap_o(_: A) := one_X;
  fmap _ _ _   := one_idX
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
