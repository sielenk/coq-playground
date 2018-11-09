Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Eqdep.


Polymorphic Record CatSig: Type := {
  Ob        :> Type;
  Hom       :  Ob -> Ob -> Type;
  id X      :  Hom X X;
  comp X Y Z:  Hom Y Z -> Hom X Y -> Hom X Z;
  eq_h X Y  :  relation (Hom X Y)
}.

Global Arguments Hom  {A} : rename.
Global Arguments id   {A} : rename.
Global Arguments comp {A X Y Z} : rename.
Global Arguments eq_h {A X Y} : rename.

Polymorphic Record CatAx(A: CatSig): Prop := {
  eq_h_equiv:  forall X Y, Equivalence (@eq_h A X Y);
  comp_eq   :  forall X Y Z, Proper (eq_h ==> eq_h ==> eq_h) (@comp A X Y Z);
  ident_r   :  forall (X Y: A)(f: Hom X Y), eq_h (comp f (id _)) f;
  ident_l   :  forall (X Y: A)(f: Hom X Y), eq_h (comp (id _) f) f;
  assoc     :  forall (W X Y Z: A)(h: Hom Y Z)(g: Hom X Y)(f: Hom W X),
                 eq_h (comp h (comp g f)) (comp (comp h g) f)
}.

Global Arguments eq_h_equiv {A}.
Global Arguments comp_eq    {A}.
Global Arguments ident_r    {A}.
Global Arguments ident_l    {A}.
Global Arguments assoc      {A}.

Polymorphic Record Cat: Type := {
  catSig :> CatSig;
  catAx  :> CatAx catSig
}.

Instance eq_h_Equivalence{A: Cat}{X Y}: Equivalence (@eq_h A X Y) :=
  eq_h_equiv A X Y.

Instance comp_eq_Proper{A: Cat}{X Y Z}: Proper (eq_h ==> eq_h ==> eq_h) (@comp A X Y Z) :=
  comp_eq A X Y Z.


Polymorphic Definition isomorphic{A: CatSig}: relation A :=
  fun X Y => exists f g, eq_h (comp f g) (id Y) /\ eq_h (comp g f) (id X).

Instance isomorphic_Equivalence{A: Cat}: Equivalence (@isomorphic A).
Proof.
  split.
  intro X.
  exists (id X).
  exists (id X).
  assert (eq_h (comp (id X) (id X)) (id X)).
  apply (ident_r A).
  split; assumption.
  intros X Y [f [g [H1 H2]]].
  exists g.
  exists f.
  split; assumption.
  intros X Y Z [f [g [H1 H2]]] [f' [g' [H1' H2']]].
  exists (comp f' f).
  exists (comp g g').
  split.
  transitivity (comp f' g').
  transitivity (comp f' (comp f (comp g g'))).
  symmetry. apply (assoc A).
  f_equiv.
  transitivity (comp (comp f g) g').
  apply (assoc A).
  transitivity (comp (id _) g').
  f_equiv.
  assumption.
  apply (ident_l A).
  assumption.
  transitivity (comp g f).
  transitivity (comp g (comp g' (comp f' f))).
  symmetry. apply (assoc A).
  f_equiv.
  transitivity (comp (comp g' f') f).
  apply (assoc A).
  transitivity (comp (id _) f).
  f_equiv.
  assumption.
  apply (ident_l A).
  assumption.
Qed.


Polymorphic Record FunSig(A B: CatSig) := {
  fmap_o  :> A -> B;
  fmap X Y:  Hom X Y -> Hom (fmap_o X) (fmap_o Y)
}.

Global Arguments fmap_o {A B}.
Global Arguments fmap   {A B} _ {X Y}.

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

Instance fmap_eq_Proper{A B}{F: Fun A B}{X Y}: Proper (eq_h ==> eq_h) (@fmap A B F X Y) :=
  fmap_eq F.


Polymorphic Record NatTrans{A B}(F G: FunSig A B) := {
  preNatTrans :> forall X, Hom (F X) (G X);
  natural     :  forall X Y (f: Hom X Y), 
                   eq_h (comp (fmap G f) (preNatTrans X))
                        (comp (preNatTrans Y) (fmap F f))
}.


Polymorphic Definition natTransId{A B: Cat}(F: Fun A B): NatTrans F F.
  refine {| preNatTrans X := id (F X) |}.
  intros.
  transitivity (fmap F f).
  apply (ident_r B).
  symmetry.
  apply (ident_l B).
Defined.

Polymorphic Definition natTransComp{A B: Cat}{F G H: Fun A B}:
    NatTrans G H-> NatTrans F G -> NatTrans F H.
  intros eta1 eta2.
  refine {| preNatTrans X := comp (eta1 X) (eta2 X) |}.
  intros.
  transitivity (comp (comp (fmap H f) (eta1 X)) (eta2 X)).
  apply (assoc B).
  transitivity (comp (comp (eta1 Y) (fmap G f)) (eta2 X)).
  f_equiv.
  apply natural.
  transitivity (comp (eta1 Y) (comp (eta2 Y) (fmap F f))).
  transitivity (comp (eta1 Y) (comp (fmap G f) (eta2 X))).
  symmetry.
  apply (assoc B).
  f_equiv.
  apply natural.
  apply (assoc B).
Defined.


Section functor_category.
  Polymorphic Variables A B: Cat.

  Polymorphic Definition FUNSig: CatSig := {|
    Ob                 := Fun A B;
    Hom                := NatTrans;
    id                 := natTransId;
    comp F G H         := natTransComp;
    eq_h F G eta1 eta2 := forall X, eq_h (eta1 X) (eta2 X)
  |}.

  Polymorphic Lemma FUNAx: CatAx FUNSig.
  Proof.
    split.
    intros F G.
    split.
    intros f X.
    reflexivity.
    intros f g H X.
    symmetry.
    apply H.
    intros f g h H1 H2 X.
    transitivity (g X).
    apply H1.
    apply H2.
    intros F G H f f' H1 g g' H2 X.
    apply (comp_eq B).
    apply H1.
    apply H2.
    intros F G f X.
    apply (ident_r B).
    intros F G f X.
    apply (ident_l B).
    intros F G H I h g f X.
    apply (assoc B).
  Qed.

  Polymorphic Definition FUN: Cat := {|
    catAx  := FUNAx
  |}.
End functor_category.



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

Polymorphic Definition CAT: CatSig := {|
  Ob         := Cat;
  Hom        := Fun;
  id         := funId;
  comp _ _ _ := funComp;
  eq_h A B   := @isomorphic (FUN A B)
|}.



Polymorphic Record AdjointSig{A B: Cat}(F: Fun B A)(G: Fun A B) := {
  epsilon: NatTrans (funComp F G) (funId A);
  eta    : NatTrans (funId B) (funComp G F)
}.

Polymorphic Record AdjointAx{A B F G}(S: @AdjointSig A B F G): Prop := {
  foo: forall Y, eq_h (id (F Y)) (comp (epsilon _ _ S (F Y)) (fmap F (eta _ _ S Y)))
}.






Definition zeroSig: CatSig := {|
  Ob             := Empty_set;
  Hom _ _        := Empty_set;
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
  Ob             := unit;
  Hom _ _        := unit;
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
  Ob             := bool;
  Hom X Y        := match X, Y with
                    | true, false => Empty_set
                    | _, _        => unit
                    end;
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
  Ob             := bool;
  Hom X Y        := match X, Y with
                    | true, false => Empty_set
                    | false, true => bool
                    | _, _        => unit
                    end;
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
  Ob             := option bool;
  Hom X Y        := match X, Y with
                    | None, Some _          => Empty_set
                    | Some true, Some false => Empty_set
                    | Some false, Some true => Empty_set
                    | _, _                  => unit
                    end;
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
  Hom X Y        := X = Y;
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



Polymorphic Definition deltaOb A {B: Cat}(X: B): Ob (FUN A B).
  refine {|
    funSig := {|
      fmap_o _   := X;
      fmap _ _ _ := id X
    |}
  |}.
  split.
  intros Y Z f f' Hf.
  reflexivity.
  intros Y.
  reflexivity.
  simpl. intros _ _ _ _ _.
  symmetry.
  apply (ident_r B).
Defined.

Polymorphic Definition deltaHom A {B: Cat}{X Y: B}(f: Hom X Y):
    Hom (deltaOb A X) (deltaOb A Y).
  refine {| preNatTrans a := f: Hom (deltaOb A X a) (deltaOb A Y a) |}.
  simpl.
  intros _ _ _.
  transitivity f.
  apply (ident_l B).
  symmetry.
  apply (ident_r B).
Defined.

Polymorphic Definition delta(A B: Cat): Fun B (FUN A B).
  refine {|
    funSig := {|
      fmap_o   := deltaOb A;
      fmap X Y := deltaHom A
    |}
  |}.
  split.
  intros X Y f f' Hf u.
  apply Hf.
  intros X u.
  reflexivity.
  intros X Y Z g h u.
  reflexivity.
Defined.


Polymorphic Definition deltaInv(A: Cat): Fun (FUN one A) A.
  refine {|
    funSig := {|
      fmap_o     := fun(X: Ob (FUN one A)) => X tt;
      fmap X Y f := f tt
    |}
  |}.
  split.
  intros X Y f f' Hf.
  apply Hf.
  intros X.
  reflexivity.
  intros X Y Z g h.
  reflexivity.
Defined.


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
    refine {|
      preNatTrans(X': Ob two) :=
        if X' return Hom (twoFun g1 X') (twoFun g2 X')
          then fmap T f2
          else fmap S f1
    |}.
    intros [|] [|] []; simpl; try assumption;
    [transitivity (fmap T f2) | transitivity (fmap S f1)];
    try apply (ident_l C);
    symmetry;
    apply (ident_r C).
  Defined.
End comma_category.

Arguments CommaCat{_ _ _}.
Arguments CommaCodFun{_ _ _}.
Arguments CommaDomFun{_ _ _}.


  .






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

Definition CiC: Cat := {|
  catAx := CiCAx
|}.



Definition xxOb(F: FUN equalizer CiC): CiC :=
  { X: F false | @fmap _ _ F false true false X = @fmap _ _ F false true true X }.

Definition xxHom{F G: FUN equalizer CiC}: Hom F G -> Hom (xxOb F) (xxOb G).
  simpl.
  intros [f Hf] [X HX]. simpl in *.
  exists (f false X).
  repeat rewrite Hf.
  f_equal.
  assumption.
Defined.

Definition xx: Fun (FUN equalizer CiC) CiC.
  refine {| funSig := {| fmap_o := xxOb; fmap X Y := xxHom |} |}.
  split.
  intros F G [X HX] [Y HY] HH.
  simpl in * |- *.
  intros [Z HZ]. simpl in HX.
  refine

  refine {| preNatTrans(X: equalizer) := equalizerFun f g X|}.
  simpl.

Definition xx : @Hom (FUN equalizer CiC) (delta equalizer _) (equalizerFun CiC). : FUN equalizer CiC

Definition xx(F: Fun equalizer CiC): 
    Hom (delta equalizer CiC { X: F false | fmap F false X = fmap F true X }) F.
  simpl.

Polymorphic Definition equalizerFun{A: Cat}{X Y: A}(f g: Hom X Y): Fun equalizer A.



Polymorphic Definition preOp(A: PreCat): PreCat := {|
  Ob             := A;
  Hom X Y        := Hom Y X;
  id             := id;
  comp X Y Z g f := comp f g;
  eq_h X Y f g   := eq_h g f;
|}.

Polymorphic Definition op(A: Cat): Cat.
  refine {| preCat := preOp A |}; intros; try split.
  intro f. simpl. reflexivity.
  intros f g H. simpl. symmetry. apply H.
  intros f g h H1 H2. simpl. transitivity g; assumption.
  intros f f' Hf g g' Hg. simpl. apply comp_eq; assumption.
  simpl. symmetry. apply ident_l.
  simpl. symmetry. apply ident_r.
  simpl. apply assoc.
Defined.



Polymorphic Definition foo A: Functor A (FUN (op A) CiC) :=
  let F := fun X => Build_Functor (op A) CiC
      (fun W => @Hom A W X)
      (fun X' Y' f (g: @Hom A X' X) => comp g f)
  in
    Build_Functor A (FUN (op A) CiC)
      F
      (fun X Y f W => comp f).

Definition faithful{A B}(F: Functor A B): Prop :=
  forall X Y (f f': Hom X Y), fmap F f = fmap F f' -> f = f'.

Definition full{A B}(F: Functor A B): Prop :=
  forall X Y (f: Hom (F X) (F Y)), exists f', f = fmap F f'.

Lemma foo' A: faithful (foo A).
Proof.
  intros X Y f f' H.
  simpl in H.
