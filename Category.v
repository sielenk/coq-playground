Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Logic.Eqdep.


Polymorphic Record PreCat := {
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

Polymorphic Record Cat := {
  preCat    :> PreCat;
  eq_h_equiv:  forall X Y, Equivalence (@eq_h preCat X Y);
  comp_eq   :  forall X Y Z, Proper (eq_h ==> eq_h ==> eq_h) (@comp preCat X Y Z);
  ident_r   :  forall (X Y: preCat)(f: Hom X Y), eq_h (comp f (id _)) f;
  ident_l   :  forall (X Y: preCat)(f: Hom X Y), eq_h (comp (id _) f) f;
  assoc     :  forall (W X Y Z: preCat)(h: Hom Y Z)(g: Hom X Y)(f: Hom W X),
                 eq_h (comp h (comp g f)) (comp (comp h g) f)
}.

Instance eq_h_Equivalence{A: Cat}{X Y}: Equivalence (@eq_h A X Y) :=
  eq_h_equiv A X Y.

Instance comp_eq_Proper{A: Cat}{X Y Z}: Proper (eq_h ==> eq_h ==> eq_h) (@comp A X Y Z) :=
  comp_eq A X Y Z.


Polymorphic Definition isomorphic{A: PreCat}: relation A :=
  fun X Y => exists f g, eq_h (comp f g) (id Y) /\ eq_h (comp g f) (id X).

Instance isomorphic_Equivalence{A: Cat}: Equivalence (@isomorphic A).
Proof.
  split.
  intro X.
  exists (id X).
  exists (id X).
  assert (eq_h (comp (id X) (id X)) (id X)).
  apply ident_r.
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
  symmetry. apply assoc.
  f_equiv.
  transitivity (comp (comp f g) g').
  apply assoc.
  transitivity (comp (id _) g').
  f_equiv.
  assumption.
  apply ident_l.
  assumption.
  transitivity (comp g f).
  transitivity (comp g (comp g' (comp f' f))).
  symmetry. apply assoc.
  f_equiv.
  transitivity (comp (comp g' f') f).
  apply assoc.
  transitivity (comp (id _) f).
  f_equiv.
  assumption.
  apply ident_l.
  assumption.
Qed.


Polymorphic Record PreFun(A B: PreCat) := {
  fmap_o  :> A -> B;
  fmap X Y:  Hom X Y -> Hom (fmap_o X) (fmap_o Y)
}.

Global Arguments fmap_o {A B}.
Global Arguments fmap   {A B} _ {X Y}.

Polymorphic Record Fun(A B: PreCat) := {
  preFun    :> PreFun A B;
  fmap_eq   :  forall X Y, Proper (eq_h ==> eq_h) (@fmap _ _ preFun X Y);
  fmap_id   :  forall X, eq_h (fmap preFun (id X)) (id (preFun X));
  fmap_comp :  forall X Y Z (g: Hom Y Z)(f: Hom X Y),
                 eq_h (fmap preFun (comp g f))
                      (comp (fmap preFun g) (fmap preFun f))
}.

Instance fmap_eq_Proper{A B}{F: Fun A B}{X Y}: Proper (eq_h ==> eq_h) (@fmap A B F X Y) :=
  fmap_eq A B F X Y.


Polymorphic Record NatTrans{A B}(F G: PreFun A B) := {
  preNatTrans :> forall X, Hom (F X) (G X);
  natural     :  forall X Y (f: Hom X Y), 
                   eq_h (comp (fmap G f) (preNatTrans X))
                        (comp (preNatTrans Y) (fmap F f)) 
}.


Polymorphic Definition natTransId{A B: Cat}(F: Fun A B): NatTrans F F.
  refine {| preNatTrans X := id (F X) |}.
  intros.
  transitivity (fmap F f).
  apply ident_r.
  symmetry.
  apply ident_l.
Defined.

Polymorphic Definition natTransComp{A B: Cat}{F G H: Fun A B}:
    NatTrans G H-> NatTrans F G -> NatTrans F H.
  intros eta1 eta2.
  refine {| preNatTrans X := comp (eta1 X) (eta2 X) |}.
  intros.
  transitivity (comp (comp (fmap H f) (eta1 X)) (eta2 X)).
  apply assoc.
  transitivity (comp (comp (eta1 Y) (fmap G f)) (eta2 X)).
  f_equiv.
  apply natural.
  transitivity (comp (eta1 Y) (comp (eta2 Y) (fmap F f))).
  transitivity (comp (eta1 Y) (comp (fmap G f) (eta2 X))).
  symmetry.
  apply assoc.
  f_equiv.
  apply natural.
  apply assoc.
Defined.

Polymorphic Definition preFUN(A B: Cat): PreCat := {|
  Ob                 := Fun A B;
  Hom                := NatTrans;
  id                 := natTransId;
  comp F G H         := natTransComp;
  eq_h F G eta1 eta2 := forall X, eq_h (eta1 X) (eta2 X)
|}.

Polymorphic Definition FUN(A B: Cat): Cat.
  refine {| preCat := preFUN A B |}.
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
  apply comp_eq.
  apply H1.
  apply H2.
  intros F G f X.
  apply ident_r.
  intros F G f X.
  apply ident_l.
  intros F G H I h g f X.
  apply assoc.
Defined.


Definition zero: Cat.
  refine {|
    preCat := {|
      Ob             := Empty_set;
      Hom _ _        := Empty_set;
      id X           := match X with end;
      comp _ Y _ _ _ := match Y with end;
      eq_h _ _ _ _   := True
    |}
  |}; simpl; intros [].
Defined.

Polymorphic Definition zeroFun A: Fun zero A.
  refine {|
    preFun := {|
      fmap_o(X: Ob zero) := match X with end;
      fmap X Y f         := match f with end
    |}
  |}; intros [].
Defined.


Definition one: Cat.
  refine {|
    preCat := {|
      Ob             := unit;
      Hom _ _        := unit;
      id _           := tt;
      comp _ _ _ _ _ := tt;
      eq_h _ _ _ _   := True
    |}
  |}; simpl; split; repeat intros []; try apply I.
Defined.

Polymorphic Definition oneFun{A: Cat}(X: Ob A): Fun one A.
  refine {|
    preFun := {|
      fmap_o _   := X;
      fmap _ _ _ := id X
    |}
  |}; simpl; intros.
  intros f f' Hf. reflexivity.
  reflexivity.
  symmetry. apply ident_r.
Defined.


Definition two: Cat.
  refine {|
    preCat := {|
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
    |}
  |}; simpl; try auto.
  intros X Y; split; auto.
  intros X Y Z _ _ _ _ _ _. auto.
Defined.

Polymorphic Definition twoFun{A: Cat}{X Y: A}(f: Hom X Y): Fun two A.
  refine {|
    preFun := {|
      fmap_o     := fun(X': two) => if X' then Y else X;
      fmap X' Y' := match X', Y' with
                    | false, false => fun _ => id X
                    | true, true   => fun _ => id Y
                    | false, true  => fun _ => f
                    | true, false  => fun f' => match f' with end
                    end
    |}
  |}.
  intros [|] [|] f1 f2 Hf; simpl; try reflexivity.
  destruct f1.
  intros [|]; reflexivity.
  intros [|] [|] [|] g' f'; simpl.
  symmetry.
  apply ident_r.
  destruct g'.
  destruct f'.
  destruct f'.
  symmetry.
  apply ident_l.
  destruct g'.
  symmetry.
  apply ident_r.
  symmetry.
  apply ident_r.
Defined.


Definition equalizer: Cat.
  refine {|
    preCat := {|
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
    |}
  |}; simpl; try auto.
  intros [|] [|] []; reflexivity.
  intros [|] [|] []; reflexivity.
  intros [|] [|] [|] [|]; try reflexivity; simpl.
  intros [].
  intros [].
  intros _ _ [].
  intros _ [].
Defined.

Polymorphic Definition equalizerFun{A: Cat}{X Y: A}(f g: Hom X Y): Fun equalizer A.
  refine {|
    preFun := {|
      fmap_o     := fun(X': equalizer) => if X' then Y else X;
      fmap X' Y' := match X', Y' with
                    | false, false => fun _ => id X
                    | true, true   => fun _ => id Y
                    | false, true  => fun f' => if f' then f else g
                    | true, false  => fun f' => match f' with end
                    end
    |}
  |}.
  intros [|]; reflexivity.
  intros [|] [|] [|] g' f'; simpl.
  symmetry. apply ident_r.
  destruct g'.
  destruct f'.
  destruct f'.
  symmetry. apply ident_l.
  destruct g'.
  symmetry. apply ident_r.
  symmetry. apply ident_r.
Defined.


Definition pullback: Cat.
  refine {|
    preCat := {|
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
    |}
  |}; simpl; try auto.
  intros X Y; split; auto.
  intros X Y Z _ _ _ _ _ _. auto.
Defined.

Polymorphic Definition pullbackFun{A: Cat}{X Y Z: A}(f: Hom X Z)(g: Hom Y Z): Fun pullback A.
  refine {|
    preFun := {|
      fmap_o     := fun(X': pullback)=> match X' with
                    | Some false => X
                    | Some true  => Y
                    | None       => Z
                    end;
      fmap X' Y' := match X', Y' with
                    | Some false, Some false => fun _ => id X
                    | Some true, Some true   => fun _ => id Y
                    | None, None             => fun _ => id Z
                    | Some false, None       => fun _ => f
                    | Some true, None        => fun _ => g
                    | _, _                   => fun f => match f with end
                    end
    |}
  |}.
  intros [[|]|] [[|]|]; simpl; intros [] u' H; reflexivity.
  intros [[|]|]; simpl; reflexivity.
  intros [[|]|] [[|]|] [[|]|]; simpl; intros [] []; symmetry;
    try apply ident_r; apply ident_l.
Defined.


Polymorphic Definition product(I: Type): Cat.
  refine {|
    preCat := {|
      Ob             := I;
      Hom X Y        := X = Y;
      id X           := eq_refl X;
      comp X Y Z g f := eq_trans f g;
      eq_h _ _ _ _   := True
    |}
  |}; simpl; try auto.
  intros X Y; split; auto.
  intros X Y Z _ _ _ _ _ _. auto.
Defined.

Polymorphic Definition productFun{I: Type}{A: Cat}(X: I -> A): Fun (product I) A.
  refine {|
    preFun := {|
      fmap_o       := X: product I -> A;
      fmap I1 I2 H := match H in _ = I2' with eq_refl => id _ end
    |}
  |}; simpl; try reflexivity.
  intros Y Z [] H _.
  rewrite (UIP_refl I Y H). reflexivity.
  intros W Y Z [] []. simpl.
  symmetry. apply ident_r.
Defined.


Polymorphic Definition deltaOb A {B: Cat}(X: B): Ob (FUN A B).
  refine {|
    preFun := {|
      fmap_o _   := X;
      fmap _ _ _ := id X
    |}
  |}.
  intros Y Z f f' Hf.
  reflexivity.
  intros Y.
  reflexivity.
  simpl. intros _ _ _ _ _.
  symmetry.
  apply ident_r.
Defined.

Polymorphic Definition deltaHom A {B: Cat}{X Y: B}(f: Hom X Y):
    Hom (deltaOb A X) (deltaOb A Y).
  refine {| preNatTrans a := f: Hom (deltaOb A X a) (deltaOb A Y a) |}.
  simpl.
  intros _ _ _.
  transitivity f.
  apply ident_l.
  symmetry.
  apply ident_r.
Defined.

Polymorphic Definition delta(A B: Cat): Fun B (FUN A B).
  refine {|
    preFun := {|
      fmap_o   := deltaOb A;
      fmap X Y := deltaHom A
    |}
  |}.
  intros X Y f f' Hf u.
  apply Hf.
  intros X u.
  reflexivity.
  intros X Y Z g h u.
  reflexivity.
Defined.


Polymorphic Definition deltaInv(A: Cat): Fun (FUN one A) A.
  refine {|
    preFun := {|
      fmap_o     := fun(X: Ob (FUN one A)) => X tt;
      fmap X Y f := f tt
    |}
  |}.
  intros X Y f f' Hf.
  apply Hf.
  intros X.
  reflexivity.
  intros X Y Z g h.
  reflexivity.
Defined.




Polymorphic Definition funId(A: Cat): Fun A A.
  refine {| preFun := {| fmap_o X := X; fmap X Y f := f |} |}.
  intros X Y f f' H1.
  assumption.
  intros X.
  reflexivity.
  intros X Y Z g h.
  reflexivity.
Defined.

Polymorphic Definition funComp(A B C: Cat)(G: Fun B C)(F: Fun A B): Fun A C.
  refine {| preFun := {| fmap_o X := G (F X); fmap X Y f := fmap G (fmap F f) |} |}.
  intros X Y f f' H1.
  apply fmap_eq.
  apply fmap_eq.
  assumption.
  intros X.
  simpl. transitivity (fmap G (id (F X))).
  f_equiv.
  apply fmap_id.
  apply fmap_id.
  intros X Y Z g f.
  simpl. transitivity (fmap G (comp (fmap F g) (fmap F f))).
  f_equiv.
  apply fmap_comp.
  apply fmap_comp.
Defined.

Polymorphic Definition CAT: PreCat := {|
  Ob       := Cat;
  Hom      := Fun;
  id       := funId;
  comp     := funComp;
  eq_h A B := @isomorphic (FUN A B)
|}.


Polymorphic Definition CiC: Cat.
  refine {|
    preCat := {|
      Ob               := Type;
      Hom X Y          := X -> Y;
      id X x           := x;
      comp X Y Z g f x := g (f x);
      eq_h X Y f g     := forall x, f x = g x
    |}
  |}; simpl; try reflexivity.
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
  refine {| preFun := {| fmap_o := xxOb; fmap X Y := xxHom |} |}.
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
