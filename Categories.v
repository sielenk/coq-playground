Require Import Coq.Logic.EqdepFacts.
Require Import Coq.Classes.RelationClasses.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

Set Universe Polymorphism On.


Definition eqF{X Y}(H: X = Y): X -> Y :=
  match H in _ = Y' return X -> Y' with
  | eq_refl _ => fun x => x
  end.


Polymorphic Cumulative Record CatSig@{i j}: Type@{max(i+1,j+1)} := {
  Ob         : Type@{i};
  Hom        : Ob -> Ob -> Type@{j};
  id X       : Hom X X;
  comp{X Y Z}: Hom Y Z -> Hom X Y -> Hom X Z
}.

Arguments Hom {c}.
Arguments id  {c}.
Arguments comp{c X Y Z}.

Polymorphic Record CatAx@{i j}(A: CatSig@{i j}): Prop := {
  ident_r{X Y: Ob A}(f: Hom X Y): comp f (id _) = f;
  ident_l{X Y: Ob A}(f: Hom X Y): comp (id _) f = f;
  assoc{W X Y Z: Ob A}(f: Hom Y Z)(g: Hom X Y)(h: Hom W X):
    comp (comp f g) h = comp f (comp g h)
}.

Arguments ident_r {A} _ {X Y}.
Arguments ident_l {A} _ {X Y}.
Arguments assoc   {A} _ {W X Y Z}.

Polymorphic Cumulative Record Cat@{i j}: Type@{max(i+1,j+1)} := {
  catSig :> CatSig@{i j};
  catAx  :> CatAx@{i j} catSig
}.



Polymorphic Definition eqHom@{i j}{A: Cat@{i j}}{X Y: Ob A}(f: Hom X Y){X' Y': Ob A}(f': Hom X' Y'): Prop :=
  eq_dep (Ob A * Ob A) (fun AB => Hom (fst AB) (snd AB)) (X, Y) f (X', Y') f'.

Definition eqHom_refl{A: Cat}{X Y: Ob A}(f: Hom X Y): eqHom f f :=
  eq_dep_intro _ _ _ _.

Definition eq_eqHom{A: Cat}{X Y: Ob A}(f f': Hom X Y): f = f' -> eqHom f f'.
  intros [].
  constructor.
Defined.

Lemma eqHom_eq{A: Cat}{X Y: Ob A}(f f': Hom X Y): eqHom f f' -> f = f'.
Proof.
  apply eq_dep_eq.
Qed.

Polymorphic Definition eqHom_trans@{i j}{A: Cat@{i j}}{X Y: Ob@{i j} A}(f f': Hom X Y):
  (forall X' Y' (f'': Hom X' Y'), X = X' -> Y = Y' -> eqHom f f'' -> eqHom f'' f') -> f = f'.
  intro H1.
  apply eqHom_eq.
  apply (H1 X Y f (eq_refl X) (eq_refl Y) (eqHom_refl f)).
Defined.




Lemma catEq(A B: Cat):
    forall
      (eqOb: Ob A = Ob B)
      (eqHom: forall X Y, Hom X Y = Hom (eqF eqOb X) (eqF eqOb Y)),
      (forall X, eqF (eqHom X X) (id X) = id (eqF eqOb X)) ->
      (forall X Y Z f g,
        eqF (eqHom X Z) (comp f g) = comp (eqF (eqHom Y Z) f) (eqF (eqHom X Y) g)) ->
      A = B.
Proof.
  destruct A as [[ObA HomA idA compA] Ha], B as [[ObB HomB idB compB] Hb].
  simpl.
  intro H. destruct H. simpl.
  intro H1.
  assert (H: HomA = HomB). extensionality X. extensionality Y.
  apply H1. destruct H.
  intro H2.
  assert (H: idA = idB). extensionality X.
  rewrite <- H2.
  rewrite (UIP_refl _ _ (H1 X X)).
  reflexivity. destruct H.
  intro H3.
  assert (H: compA = compB).
  extensionality X. extensionality Y. extensionality Z. extensionality f. extensionality g.
  set (H := H3 X Y Z f g).
  rewrite (UIP_refl _ _ (H1 X Z)) in H.
  rewrite (UIP_refl _ _ (H1 X Y)) in H.
  rewrite (UIP_refl _ _ (H1 Y Z)) in H.
  apply H.
  destruct H.
  f_equal.
  apply proof_irrelevance.
Qed.


Section Fun.
  Polymorphic Variables A B: CatSig.

  Polymorphic Cumulative Record FunSig: Type := {
    fmap1: Ob A -> Ob B;
    fmap2{X Y}: Hom X Y -> Hom (fmap1 X) (fmap1 Y)
  }.

  Polymorphic Record FunAx(F: FunSig): Prop := {
    fmap_id: forall X, fmap2 F (id X) = id _;
    fmap_comp{X Y Z}(f: Hom Y Z)(g: Hom X Y):
      fmap2 F (comp f g) = comp (fmap2 F f) (fmap2 F g)
  }.

  Polymorphic Cumulative Record Fun: Type := {
    funSig :> FunSig;
    funAx  :> FunAx funSig
  }.
End Fun.

Arguments FunAx {A B}.
Arguments fmap1 {A B}.
Arguments fmap2 {A B} _ {X Y}.
Arguments fmap_id   {A B F}.
Arguments fmap_comp {A B F}.



Lemma funHomEq{A B: Cat}{F G: Fun A B}(eq1: forall X, fmap1 F X = fmap1 G X):
    forall X Y, Hom (fmap1 F X) (fmap1 F Y) = Hom (fmap1 G X) (fmap1 G Y).
Proof.
  intros X Y.
  repeat rewrite eq1.
  reflexivity.
Qed.

Lemma funEq{A B: Cat}(F G: Fun A B):
    forall
      (eq1: forall X, fmap1 F X = fmap1 G X)
      (eq2: forall X Y f, eqF (funHomEq eq1 X Y) (fmap2 F f) = fmap2 G f),
      F = G.
Proof.
  destruct F as [[Fo Fh] Hf], G as [[Go Gh] Hg]; simpl.
  intros H1 H2.
  assert (H: Fo = Go). extensionality X.
  apply H1. destruct H.
  assert (H: Fh = Gh). extensionality X. extensionality Y. extensionality f.
  rewrite <- H2.
  rewrite (UIP_refl _ _ _). reflexivity.
  destruct H.
  f_equal.
  apply proof_irrelevance.
Qed.


Definition faithful{A B}(F: FunSig A B): Prop :=
  forall X Y (f f': Hom X Y), fmap2 F f = fmap2 F f' -> f = f'.

Definition full{A B}(F: FunSig A B): Prop :=
  forall X Y f, exists f': Hom X Y, fmap2 F f' = f.



Polymorphic Cumulative Record Nat{A B}(F G: Fun A B) := {
  eta:> forall X, Hom (fmap1 F X) (fmap1 G X);
  eta_ax{X Y}(f: Hom X Y):
    comp (fmap2 G f) (eta X) = comp (eta Y) (fmap2 F f)
}.

Arguments eta {A B F G}.

Polymorphic Lemma natEq@{i j k l}{A B}{F G: Fun@{i j k l} A B}(M N: Nat F G): (forall X, eta N X = eta M X) -> M = N.
Proof.
  destruct M, N. simpl.
  intro H.
  assert (H': eta1 = eta0). extensionality X.
  apply H.
  destruct H'.
  f_equal; apply proof_irrelevance.
Qed.


Polymorphic Definition opSig@{i j}(A: CatSig@{i j}): CatSig@{i j} := {|
  Ob             := Ob A;
  Hom X Y        := Hom Y X;
  id X           := id X;
  comp _ _ _ g f := comp f g
|}.

Polymorphic Definition op@{i j}(A: Cat@{i j}): Cat@{i j}.
  refine {| catSig := opSig A; catAx := _ |}.
  constructor; simpl; intros.
  apply (ident_l A).
  apply (ident_r A).
  symmetry. apply (assoc A).
Defined.


Section prodSig.
  Polymorphic Universe i j k l.

  Polymorphic Variables A: CatSig@{i j}.
  Polymorphic Variables B: CatSig@{k l}.

  Polymorphic Definition prodSig: CatSig := {|
    Ob             := Ob A * Ob B;
    Hom X Y        := (Hom (fst X) (fst Y) * Hom (snd X) (snd Y))%type;
    id X           := (id (fst X), id (snd X));
    comp _ _ _ g f := (comp (fst g) (fst f), comp (snd g) (snd f))
  |}.

  Polymorphic Definition firstSig: FunSig prodSig A :=
    Build_FunSig prodSig A fst (fun _ _ => fst).

  Polymorphic Definition secondSig: FunSig prodSig B :=
    Build_FunSig prodSig B snd (fun _ _ => snd).
End prodSig.

Arguments firstSig  {A B}.
Arguments secondSig {A B}.

Section prod.
  Polymorphic Variables A B: Cat.

  Polymorphic Definition prod: Cat.
    refine {| catSig := prodSig A B; catAx := _ |}.
    constructor; simpl; intros.
    rewrite (ident_r A).
    rewrite (ident_r B).
    destruct f. reflexivity.
    rewrite (ident_l A).
    rewrite (ident_l B).
    destruct f. reflexivity.
    rewrite (assoc A).
    rewrite (assoc B).
    reflexivity.
  Defined.

  Polymorphic Definition first: Fun prod A.
    refine {| funSig := firstSig; funAx := _ |}.
    constructor; reflexivity.
  Defined.

  Polymorphic Definition second: Fun prod B.
    refine {| funSig := secondSig; funAx := _ |}.
    constructor; reflexivity.
  Defined.
End prod.

Arguments first  {A B}.
Arguments second {A B}.


Definition deltaSig A {B}(X: Ob B): FunSig A B :=
  {| fmap1 _ := X; fmap2 _ _ _ := id X |}.

Definition delta A {B: Cat}(X: Ob B): Fun A B.
  refine {| funSig := deltaSig A X; funAx := _ |}.
  constructor; intros; simpl.
  reflexivity.
  rewrite (ident_r B).
  reflexivity.
Defined.


Definition funIdSig A: FunSig A A := {|
  fmap1 X     := X;
  fmap2 _ _ f := f
|}.

Definition funId A: Fun A A.
  refine {| funSig := funIdSig A; funAx := _ |}.
  constructor; reflexivity.
Defined.

Definition funCompSig{A B C}(F: FunSig B C)(G: FunSig A B): FunSig A C := {|
  fmap1 X     := fmap1 F (fmap1 G X);
  fmap2 _ _ f := fmap2 F (fmap2 G f)
|}.

Definition funComp{A B C}(F: Fun B C)(G: Fun A B): Fun A C.
  refine {| funSig := funCompSig F G; funAx := _ |}.
  constructor; intros; simpl.

  rewrite (fmap_id G).
  rewrite (fmap_id F).
  reflexivity.

  rewrite (fmap_comp G).
  rewrite (fmap_comp F).
  reflexivity.
Defined.

Definition CATSig: CatSig := {|
  Ob         := Cat;
  Hom        := Fun;
  id         := funId;
  comp _ _ _ := funComp
|}.

Definition CAT: Cat.
  refine {| catSig := CATSig; catAx := _ |}.
  constructor; simpl.

  intros A B F. refine (funEq _ _ (fun X => _) _).
  intros X Y f.
  rewrite (UIP_refl _ _ _).
  reflexivity.

  intros A B F. refine (funEq _ _ (fun X => _) _).
  intros X Y f.
  rewrite (UIP_refl _ _ _).
  reflexivity.

  intros A B C D F G H. refine (funEq _ _ (fun X => _) _).
  intros X Y f.
  rewrite (UIP_refl _ _ _).
  reflexivity.

  Unshelve.
  reflexivity.
  reflexivity.
  reflexivity.
Defined.


Section FUN.
  Polymorphic Universe i j k l.

  Polymorphic Variable A: CatSig@{i j}.
  Polymorphic Variable B: Cat@{k l}.

  Polymorphic Definition natId(F: Fun A B): Nat F F.
    refine ({| eta X := id (fmap1 F X) |}).

    intros.
    rewrite (ident_r B).
    rewrite (ident_l B).
    reflexivity.
  Defined.

  Polymorphic Definition natComp{F G H: Fun A B}(N: Nat G H)(M: Nat F G): Nat F H.
    refine ({| eta X := comp (eta N X) (eta M X) |}).

    intros.
    rewrite (assoc B).
    rewrite <- eta_ax.
    rewrite <- (assoc B).
    rewrite eta_ax.
    apply (assoc B).
  Defined.

  Polymorphic Definition FUNSig: CatSig := {|
    Ob         := Fun A B;
    Hom        := Nat;
    id         := natId;
    comp _ _ _ := natComp
  |}.

  Polymorphic Definition FUN: Cat.
    refine {| catSig := FUNSig; catAx := _ |}.
    constructor; simpl.

    intros F G N. refine (natEq _ _ _).
    intro X. simpl.
    rewrite (ident_r B). reflexivity.

    intros F G N. refine (natEq _ _ _).
    intro X. simpl.
    rewrite (ident_l B). reflexivity.

    intros F G H I N M O. refine (natEq _ _ _).
    intro X. simpl.
    symmetry. apply (assoc B).
  Defined.
End FUN.



Polymorphic Definition SETSig: CatSig := {|
  Ob               := Type;
  Hom X Y          := X -> Y;
  id _ x           := x;
  comp _ _ _ g f x := g (f x)
|}.

Polymorphic Definition SET@{i j}: Cat@{i j}.
  refine {| catSig := SETSig@{i j}; catAx := _ |}.
  constructor; simpl; intros; extensionality x; reflexivity.
Defined.


Polymorphic Definition HomFunSig@{i j k l}{A: Cat@{i j}}(X: Ob A): FunSig@{i j k l} A SET@{k l} :=
  Build_FunSig@{i j k l} A SET@{k l} (Hom X) (fun Y Z => comp).

Polymorphic Definition HomFun@{i j k l}{A: Cat@{i j}}(X: Ob A): Fun@{i j k l} A SET@{k l}.
  refine (Build_Fun@{i j k l} A SET@{k l} (HomFunSig@{i j k l} X) _).
  constructor; intros; extensionality h; simpl.
  rewrite (ident_l A). reflexivity.
  apply (assoc A).
Defined.


Section yoneda.
  Polymorphic Universe i j k l n m.
  Polymorphic Variable A: Cat@{i j}.

  Polymorphic Definition U: Cat@{n m} := FUN@{i j k l n m} A SET@{k l}.

  Polymorphic Definition bangSig: FunSig@{i j k l} (op A) U.
    refine {|
      fmap1       := HomFun (A := A): Ob (op A) -> Ob U;
      fmap2 X Y f := {|
        eta Z := (fun g => comp g f): Hom (fmap1 (HomFun (A := A) X) Z) (fmap1 (HomFun (A := A) Y) Z)
      |}
    |}.
    intros W Z g.
    extensionality h.
    simpl.
    rewrite (assoc A).
    reflexivity.
  Defined.

  Polymorphic Definition bang: Fun@{i j k l} (op A) U.
    refine {| funSig := bangSig; funAx := _ |}.
    constructor; intros; apply natEq; simpl.
    intro Y. extensionality f.
    rewrite (ident_r A). reflexivity.
    intro W. extensionality h.
    apply (assoc A).
  Defined.

(*
  Polymorphic Definition applySig: FunSig (prod U A) SET@{k l} := {|
    fmap1 (X: Ob (prod U A)) := fmap1 (fmap1 first X) (fmap1 second X);
    fmap2 X Y f := fmap2 (fmap2 first f) (fmap2 second f)
  |}.
*)

  Polymorphic Variable F: Ob U.

  Polymorphic Definition yoneda1(X: Ob A): fmap1 F X -> Hom (fmap1 bang X) F.
    refine (fun u => Build_Nat A SET (HomFun X) F (fun Y f => fmap2 F f u) _).
    simpl.
    intros Y Z f.
    extensionality g.
    rewrite (fmap_comp F).
    reflexivity.
  Defined.

  Polymorphic Definition yoneda2(X: Ob A): Hom (fmap1 bang X) F -> fmap1 F X :=
    fun N => eta N X (id X).

(*
  Lemma foo: faithful bang.
  Proof.
    intros X Y f f'.   simpl. H.
*)

End yoneda.




Definition unique{T}(t: T) := forall t', t = t'.

Polymorphic Definition initial@{i j}{A: Cat@{i j}}(X: Ob A) := forall Y, { f: Hom X Y | unique f }.

Polymorphic Definition skeletal@{i j}(A: CatSig@{i j}) := forall (X Y: Ob A)(f: Hom X Y), unique f.


Definition cone{I A: Cat}(N: Ob A)(F: Fun I A) := Nat (delta I N) F.





Definition oneOb := unit.

Inductive oneHom: oneOb -> oneOb -> Set :=
  UnitHom: oneHom tt tt.

Definition oneId(X: oneOb): oneHom X X :=
  match X as X' return oneHom X' X' with tt => UnitHom end.

Definition oneComp X Y Z (f: oneHom Y Z)(g: oneHom X Y): oneHom X Z :=
  match X as X', Z as Z' return oneHom X' Z' with tt, tt => UnitHom end.

Definition CatOneSig: CatSig := {|
  Ob   := oneOb;
  Hom  := oneHom;
  id   := oneId;
  comp := oneComp
|}.

Definition CatOne: Cat@{Set Set}.
  refine {| catSig := CatOneSig; catAx := _ |}.
  constructor.
  intros X Y []. reflexivity.
  intros X Y []. reflexivity.
  intros [] X Y [] f g h. reflexivity.
Defined.


Inductive twoOb: Set := Zero | One.

Inductive twoHom: twoOb -> twoOb -> Set :=
| IdZero:  twoHom Zero Zero
| IdOne:   twoHom One One
| ZeroOne: twoHom Zero One
.

Definition twoId(X: twoOb): twoHom X X :=
  match X as X' return (twoHom X' X') with
  | Zero => IdZero
  | One  => IdOne
  end.

Definition twoComp X Y Z (f: twoHom Y Z)(g: twoHom X Y): twoHom X Z.
  assert (Zero <> One).
  intro H.
  inversion H.
  refine (
    sumor_rec (fun _ => twoHom X Z) (fun gf => gf) (fun H => False_rec _ (H (eq_refl _)))
      match f in twoHom Yf Z', g in twoHom X' Yg return twoHom X' Z' + {Yf <> Yg} with
      | IdZero,  IdZero  => inleft IdZero
      | IdOne,   IdOne   => inleft IdOne
      | ZeroOne, IdZero  => inleft ZeroOne
      | IdOne,   ZeroOne => inleft ZeroOne
      | IdOne,   IdZero  => inright _
      | _,       _       => inright H
      end
  ).
  intro H'. apply H. symmetry. assumption.
Defined.

Definition CatTwoSig: CatSig@{Set Set} := {|
  Ob   := twoOb;
  Hom  := twoHom;
  id   := twoId;
  comp := twoComp
|}.

Definition CatTwo: Cat@{Set Set}.
  refine {| catSig := CatTwoSig; catAx := _ |}.

  assert (H1: forall (X Y : twoOb) (f : twoHom X Y),
    twoComp X X Y f (twoId X) = f).
  intros X Y []; reflexivity.

  assert (H2: forall (X Y : twoOb) (f : twoHom X Y),
    twoComp X Y Y (twoId Y) f = f).
  intros X Y []; reflexivity.

  constructor; try assumption.
  intros W X Y Z f g h.
  destruct f; try (repeat rewrite H2; reflexivity).
  destruct h; try (repeat rewrite H1; reflexivity).
  inversion g.
Defined.


Lemma two_skeletal: skeletal CatTwo.
Proof.
  intros X Y f f'.
  apply eqHom_trans@{Set Set}.
  intros X' Y' ff H1 H2 H3.
  destruct ff, f'; try reflexivity;
  inversion H1;
  inversion H2.
Qed.

Lemma zero_initial: @initial CatTwo Zero.
Proof.
  intros [ | ]; [exists IdZero | exists ZeroOne];
  apply two_skeletal.
Qed.


Definition FunA: Fun CatOne CatTwo.
  apply (Build_Fun CatOne CatTwo
    (fun _ => Zero)
    (fun _ _ _ => IdZero)).
  reflexivity.
  reflexivity.
Defined.

Definition FunB: Fun CatOne CatTwo.
  apply (Build_Fun CatOne CatTwo
    (fun _ => One)
    (fun _ _ _ => IdOne)).
  reflexivity.
  reflexivity.
Defined.

Definition NatAB: Nat FunA FunB.
  apply (Build_Nat CatOne CatTwo FunA FunB (fun _ => ZeroOne)).
  reflexivity.
Defined.



Definition xxFmap1(X: Ob CatTwo): Ob (FUN CatOne CatTwo) :=
  match X with Zero => FunA | One => FunB end.

Definition xxFmap2(X Y: Ob CatTwo)(f: Hom X Y): Hom (xxFmap1 X) (xxFmap1 Y) :=
  match f in (twoHom X' Y') return (Hom (xxFmap1 X') (xxFmap1 Y')) with
  | IdZero  => funId CatOne CatTwo FunA
  | IdOne   => funId CatOne CatTwo FunB
  | ZeroOne => NatAB
  end.

Definition xxx: Fun CatTwo (FUN CatOne CatTwo).
  refine (Build_Fun _ _ xxFmap1 xxFmap2 _ _).
  simpl. intros []; reflexivity.
  intros.
  apply eqHom_trans.
  intros.
  simpl in * |- *.
  destruct (xxFmap2 X Z (twoComp X Y Z f g)).
  simpl in * |- *.

  set (fg := comp f g). simpl.
  assert (fg = comp f g) by reflexivity.
  destruct fg, Y; simpl.
  
