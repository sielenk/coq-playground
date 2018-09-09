Require Import Relations.
Require Import RelationClasses.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.


Definition eqF{X Y}(H: X = Y): X -> Y :=
  match H in _ = Y' return X -> Y' with
  | eq_refl _ => fun x => x
  end.

Lemma eqFunc{X Y}{f1 f2: X -> Y}: f1 = f2 -> forall x, f1 x = f2 x.
Proof.
  intros [] x.
  reflexivity.
Qed.

Definition injective{X Y}(f: X -> Y): Prop :=
  forall x1 x2, f x1 = f x2 -> x1 = x2.

Definition surjective{X Y}(f: X -> Y): Prop :=
  forall y, exists x, f y = x.



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


Polymorphic Definition initial@{i j}{A: CatSig@{i j}}(X: Ob A): Prop :=
  forall Y, exists f: Hom X Y, forall f', f = f'.

Polymorphic Definition terminal@{i j}{A: CatSig@{i j}}(Y: Ob A): Prop :=
  forall X, exists f: Hom X Y, forall f', f = f'.

Polymorphic Definition separator@{i j}{A: CatSig@{i j}}(S: Ob A): Prop :=
  forall(X Y: Ob A)(f g: Hom X Y), f <> g -> exists(h: Hom S X), comp f h <> comp g h.

Polymorphic Definition section@{i j}{A: CatSig@{i j}}{X Y: Ob A}(f: Hom X Y): Prop :=
  exists g, comp g f = id X.

Polymorphic Definition retraction@{i j}{A: CatSig@{i j}}{X Y: Ob A}(f: Hom X Y): Prop :=
  exists g, comp f g = id Y.

Polymorphic Definition iso@{i j}{A: CatSig@{i j}}{X Y: Ob A}(f: Hom X Y): Prop :=
  exists g, comp f g = id Y /\ comp g f = id X.

Polymorphic Definition mono@{i j}{A: CatSig@{i j}}{X Y: Ob A}(f: Hom X Y): Prop :=
  forall W (h k: Hom W X), comp f h = comp f k -> h = k.

Polymorphic Definition epi@{i j}{A: CatSig@{i j}}{X Y: Ob A}(f: Hom X Y): Prop :=
  forall Z (h k: Hom Y Z), comp h f = comp k f -> h = k.

Polymorphic Definition bi@{i j}{A: CatSig@{i j}}{X Y: Ob A}(f: Hom X Y): Prop :=
  mono f /\ epi f.

Polymorphic Definition balanced@{i j}(A: CatSig@{i j}): Prop :=
  forall (X Y: Ob A)(f: Hom X Y), bi f -> iso f.

Polymorphic Definition thin@{i j}(A: CatSig@{i j}): Prop :=
  forall (X Y: Ob A)(f f': Hom X Y), f = f'.

Polymorphic Definition isomorphic@{i j}{A: CatSig@{i j}}: relation (Ob A) :=
  fun X Y => exists(f: Hom X Y), iso f.

Polymorphic Definition skeletal@{i j}(A: CatSig@{i j}): Prop :=
  forall (X Y: Ob A), isomorphic X Y -> X = Y.



Polymorphic Instance Equivalence_isomorphic@{i j}{A: Cat@{i j}}: Equivalence (isomorphic (A:=A)).
Proof.
  split.

  intro X.
  exists (id X).
  exists (id X).
  split; apply (ident_r A).

  intros X Y [f [f' H]].
  exists f'.
  exists f.
  split; tauto.

  intros X Y Z [f [f' [Hf1 Hf2]]] [g [g' [Hg1 Hg2]]].
  exists (comp g f).
  exists (comp f' g').
  split.
  rewrite (assoc A).
  rewrite <- (assoc A f f' g').
  rewrite Hf1.
  rewrite (ident_l A).
  assumption.
  rewrite (assoc A).
  rewrite <- (assoc A g' g f).
  rewrite Hg2.
  rewrite (ident_l A).
  assumption.
Qed.


Polymorphic Definition EmbedTypeSig@{i}(T: Type@{i}): CatSig@{i Set} := {|
  Ob             := T;
  Hom            := eq;
  id X           := eq_refl;
  comp X Y Z f g := eq_trans g f
|}.

Polymorphic Definition EmbedType@{i}(T: Type@{i}): Cat@{i Set}.
  refine {| catSig := EmbedTypeSig T |}.
  split; simpl; intros; apply proof_irrelevance.
Defined.



Polymorphic Definition FullSubcatSig(A: CatSig)(P: Ob A -> Prop): CatSig := {|
  Ob             := sig P;
  Hom X Y        := Hom (proj1_sig X) (proj1_sig Y);
  id X           := id (proj1_sig X);
  comp X Y Z f g := comp (c := A) f g
|}.

Polymorphic Definition FullSubcat(A: Cat)(P: Ob A -> Prop): Cat.
  refine {| catSig := FullSubcatSig A P |}.
  constructor; simpl; intros.
  apply (ident_r A).
  apply (ident_l A).
  apply (assoc A).
Defined.


Polymorphic Definition HomSubcatSig
    (A: CatSig)
    (P: forall (X Y: Ob A), Hom X Y -> Prop)
    (H1: forall X, P X X (id X))
    (H2: forall X Y Z f g, P Y Z f -> P X Y g -> P X Z (comp f g)): CatSig := {|
  Ob             := Ob A;
  Hom X Y        := sig (P X Y);
  id X           := exist (P X X) (id X) (H1 X);
  comp X Y Z f g := exist (P X Z) _ (H2 X Y Z _ _ (proj2_sig f) (proj2_sig g))
|}.

Polymorphic Definition HomSubcat(A: Cat)(P: forall (X Y: Ob A), Hom X Y -> Prop)
  (H1: forall X, P X X (id X))
  (H2: forall X Y Z f g, P Y Z f -> P X Y g -> P X Z (comp f g)): Cat.
  refine {| catSig := HomSubcatSig A P H1 H2 |}.
  constructor; simpl; intros.
  destruct f as [f H3].
  refine (eq_sig_uncurried _ _ _). simpl.
  exists (ident_r A _).
  apply proof_irrelevance.
  destruct f as [f H3].
  refine (eq_sig_uncurried _ _ _). simpl.
  exists (ident_l A _).
  apply proof_irrelevance.
  refine (eq_sig_uncurried _ _ _). simpl.
  exists (assoc A _ _ _).
  apply proof_irrelevance.
Defined.


Definition comp'{A: CatSig}{X Y Y' Z: Ob A}(H: Y = Y'): Hom Y' Z -> Hom X Y -> Hom X Z :=
  match H with eq_refl => comp end.

Lemma eq_comp_comp'{A: CatSig}{X Y Z: Ob A}(f: Hom Y Z)(g: Hom X Y): comp f g = comp' (eq_refl Y) f g.
Proof.
  simpl.
  reflexivity.
Qed.


Polymorphic Cumulative Inductive eqHom@{i j}{A: CatSig@{i j}}{X Y: Ob A}(f: Hom X Y): forall{X' Y': Ob A}, Hom X' Y' -> Prop :=
  eqHom_refl: eqHom f f.

Polymorphic Definition eqHom_sym@{i j}{A: CatSig@{i j}}{X Y: Ob A}(f: Hom X Y){X' Y': Ob A}(f': Hom X' Y'):
  eqHom f f' -> eqHom f' f.
  intros [].
  constructor.
Defined.

Polymorphic Definition eqHom_trans@{i j}{A: CatSig@{i j}}
  {X1 Y1: Ob A}(f1: Hom X1 Y1)
  {X2 Y2: Ob A}(f2: Hom X2 Y2)
  {X3 Y3: Ob A}(f3: Hom X3 Y3):
  eqHom f2 f3 -> eqHom f1 f2 -> eqHom f1 f3.
  intros [] H. exact H.
Defined.


Polymorphic Definition eq_eqHom@{i j}{A: CatSig@{i j}}{X Y: Ob A}(f f': Hom X Y): f = f' -> eqHom f f'.
  intros [].
  constructor.
Defined.

Polymorphic Lemma eqHom_eq@{i j}{A: CatSig@{i j}}{X Y: Ob A}(f f': Hom X Y): eqHom f f' -> f = f'.
Proof.
  intro H1.
  set (X' := X).
  set (Y' := Y).
  change (Hom X' Y') in f'.
  change (@eqHom@{i j} A X Y f X' Y' f') in H1.
  set (H2 := eq_refl _ : Hom X Y = Hom X' Y').
  transitivity (eqF H2 f).
  reflexivity.
  generalize dependent H2.
  generalize dependent Y'.
  generalize dependent X'.
  intros X' Y' f' [] H.
  rewrite (UIP_refl _ _ _).
  reflexivity.
Qed.

Polymorphic Definition eqHom_trans'@{i j}{A: CatSig@{i j}}{X Y: Ob A}(f f': Hom X Y):
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
  Polymorphic Universe i j k l.

  Polymorphic Variables A: CatSig@{i j}.
  Polymorphic Variables B: CatSig@{k l}.

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


Polymorphic Definition embedding@{i j k l}{A B}(F: FunSig@{i j k l} A B): Prop :=
  forall (X Y: Ob A)(f: Hom X Y)(X' Y': Ob A)(f': Hom X' Y'),
    eqHom (fmap2 F f) (fmap2 F f') -> eqHom f f'.

Polymorphic Definition faithful@{i j k l}{A B}(F: FunSig@{i j k l} A B): Prop :=
  forall X Y, injective (fmap2 F (X:=X)(Y:=Y)).

Polymorphic Definition full@{i j k l}{A B}(F: FunSig@{i j k l} A B): Prop :=
  forall X Y, surjective (fmap2 F (X:=X)(Y:=Y)).

Polymorphic Definition amnestic@{i j k l}{A B}(F: FunSig@{i j k l} A B): Prop :=
  forall(X Y: Ob@{i j} A)(f: Hom X Y),
    iso f ->
    (exists Z, eqHom (fmap2 F f) (id Z)) ->
    (exists Z, eqHom f (id Z)).



Lemma faithful_catax{A}{B: Cat}(F: Fun A B): faithful F -> CatAx A.
Proof.
  intro H.
  constructor; intros; apply H; repeat rewrite (fmap_comp F); try rewrite (fmap_id F).
  apply (ident_r B).
  apply (ident_l B).
  apply (assoc B).
Qed.





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
  refine {| catSig := opSig@{i j} A |}.
  constructor; simpl; intros.
  apply (ident_l A).
  apply (ident_r A).
  symmetry. apply (assoc A).
Defined.


Section prodSig.
  Polymorphic Universe i j k l n m.

  Polymorphic Variables A: CatSig@{i j}.
  Polymorphic Variables B: CatSig@{k l}.

  Polymorphic Definition prodSig: CatSig@{n m} := {|
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
  Polymorphic Universe i j k l n m.

  Polymorphic Variable A: Cat@{i j}.
  Polymorphic Variable B: Cat@{k l}.

  Polymorphic Definition prod: Cat@{n m}.
    refine {| catSig := prodSig A B |}.
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
  refine {| funSig := deltaSig A X |}.
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
  refine {| funSig := funIdSig A |}.
  constructor; reflexivity.
Defined.

Definition funCompSig{A B C}(F: FunSig B C)(G: FunSig A B): FunSig A C := {|
  fmap1 X     := fmap1 F (fmap1 G X);
  fmap2 _ _ f := fmap2 F (fmap2 G f)
|}.

Definition funComp{A B C}(F: Fun B C)(G: Fun A B): Fun A C.
  refine {| funSig := funCompSig F G |}.
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
  refine {| catSig := CATSig |}.
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
    refine {| catSig := FUNSig |}.
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
  refine {| catSig := SETSig@{i j} |}.
  constructor; simpl; intros; extensionality x; reflexivity.
Defined.



Polymorphic Definition h_sup_Sig@{i j k l}{A: Cat@{i j}}(X: Ob A): FunSig@{i j k l} A SET@{k l} :=
  Build_FunSig@{i j k l} A SET@{k l} (Hom X) (fun Y Z => comp).

Polymorphic Definition h_sup@{i j k l}{A: Cat@{i j}}(X: Ob A): Fun@{i j k l} A SET@{k l}.
  apply (Build_Fun@{i j k l} A SET@{k l} (h_sup_Sig@{i j k l} X)).
  constructor; intros; extensionality h; simpl.
  rewrite (ident_l A). reflexivity.
  apply (assoc A).
Defined.


Polymorphic Definition h_sub_Sig@{i j k l}{A: Cat@{i j}}(Y: Ob A): FunSig@{i j k l} (op A) SET@{k l} :=
  Build_FunSig@{i j k l} (op A) SET@{k l} (fun X => Hom (X: Ob A) Y) (fun X Y f g => comp g f).

Polymorphic Definition h_sub@{i j k l}{A: Cat@{i j}}(Y: Ob A): Fun@{i j k l} (op A) SET@{k l}.
  apply (Build_Fun@{i j k l} (op A) SET@{k l} (h_sub_Sig@{i j k l} Y)).
  constructor; intros; extensionality h; simpl.
  rewrite (ident_r A). reflexivity.
  symmetry. apply (assoc A).
Defined.


Section yoneda.
  Polymorphic Universe i j k l n m.
  Polymorphic Variable A: Cat@{i j}.

  Polymorphic Variable F: Fun A SET@{k l}.
  Polymorphic Variable X: Ob A.

  Polymorphic Definition yoneda1: Hom (c:=SET) (fmap1 F X) (Nat (h_sup X) F).
    refine (fun u => {| eta Y := (fun f => fmap2 F f u): Hom (fmap1 (h_sup X) Y) (fmap1 F Y) |}).
    intros Y Z f.
    extensionality g.
    simpl. rewrite (fmap_comp F).
    reflexivity.
  Defined.

  Polymorphic Definition yoneda2: Hom (c:=SET) (Nat (h_sup X) F) (fmap1 F X) :=
    fun eta => eta X (id X).

  Polymorphic Lemma yoneda12: comp yoneda1 yoneda2 = id _.
  Proof.
    extensionality eta.
    apply natEq.
    intro Y.
    extensionality f.
    set (H := eqFunc (eta_ax _ _ eta f) (id _)).
    simpl in H.
    rewrite (ident_r A f) in H.
    symmetry.
    assumption.
  Qed.

  Polymorphic Lemma yoneda21: comp yoneda2 yoneda1 = id _.
  Proof.
    extensionality u.
    simpl.
    rewrite (fmap_id F).
    reflexivity.
  Qed.

  Polymorphic Lemma yoneda: isomorphic (A:=SET) (fmap1 F X) (Nat (h_sup X) F).
  Proof.
    exists yoneda1.
    exists yoneda2.
    split; simpl.
    apply yoneda12.
    apply yoneda21.
  Qed.
End yoneda.

Arguments yoneda1  {A}.
Arguments yoneda2  {A}.
Arguments yoneda12 {A}.
Arguments yoneda21 {A}.
Arguments yoneda   {A}.



Definition eval{A B: Cat}: Fun (prod (FUN A B) A) B.
  refine {|
    funSig := {|
      fmap1 (FX: Ob (prod (FUN A B) A)) := fmap1 (fmap1 first FX) (fmap1 second FX);
      fmap2 FX GY etaf := comp (fmap2 first etaf (fmap1 second GY)) (fmap2 (fmap1 first FX) (fmap2 second etaf))
    |}
  |}.
  split; simpl.

  intros [F X]; simpl.
  rewrite (ident_l B).
  apply (fmap_id F).

  intros [F X] [G Y] [H Z] [eta1 f] [eta2 g]; simpl in * |- *.
  rewrite (fmap_comp F).
  repeat rewrite (assoc B (eta1 Z)).
  f_equal.
  rewrite <- (assoc B (eta2 Z)).
  rewrite <- (eta_ax F G eta2 f).
  apply (assoc B).
Defined.


Section yoneda_embedding.
  Polymorphic Universe i j k l n m.
  Polymorphic Variable A: Cat@{i j}.

  Polymorphic Lemma yoneda_embedding(X Y: Ob A): isomorphic (A:=SET) (Hom X Y) (Nat (h_sup Y) (h_sup X)).
  Proof.
    exists (yoneda1 (h_sup X) Y).
    exists (yoneda2 (h_sup X) Y).
    simpl.
    split.
    apply yoneda12.
    extensionality f.
    apply (ident_l A).
  Qed.
End yoneda_embedding.







Definition oneOb := unit.

Inductive oneHom: oneOb -> oneOb -> Set :=
  UnitHom: oneHom tt tt.

Definition oneId(X: oneOb): oneHom X X :=
  match X as X' return oneHom X' X' with tt => UnitHom end.

Definition oneComp X Y Z (f: oneHom Y Z)(g: oneHom X Y): oneHom X Z :=
  match X as X', Z as Z' return oneHom X' Z' with tt, tt => UnitHom end.

Definition CatOneSig@{i j}: CatSig@{i j} := {|
  Ob   := oneOb: Type@{i};
  Hom  := oneHom: oneOb -> oneOb -> Type@{j};
  id   := oneId;
  comp := oneComp
|}.

Definition CatOne@{i j}: Cat@{i j}.
  refine {| catSig := CatOneSig |}.
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
  assert (H1: Zero <> One).
  intro H. inversion H.
  assert (H2: One <> Zero).
  intro H. apply H1. symmetry. assumption.
  exact (
    sumor_rec (fun _ => twoHom X Z) (fun gf => gf) (fun H => False_rec _ (H (eq_refl _)))
      match f in twoHom Yf Z', g in twoHom X' Yg return twoHom X' Z' + {Yf <> Yg} with
      | IdZero,  IdZero  => inleft IdZero
      | IdOne,   IdOne   => inleft IdOne
      | ZeroOne, IdZero  => inleft ZeroOne
      | IdOne,   ZeroOne => inleft ZeroOne
      | IdOne,   IdZero  => inright H2
      | _,       _       => inright H1
      end
  ).
Defined.

Definition CatTwoSig@{i j}: CatSig@{i j} := {|
  Ob   := twoOb: Type@{i};
  Hom  := twoHom: twoOb -> twoOb -> Type@{j};
  id   := twoId;
  comp := twoComp
|}.

Definition CatTwo@{i j}: Cat@{i j}.
  refine {| catSig := CatTwoSig |}.

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


Lemma one_thin: thin CatOne.
Proof.
  intros X Y f f'.
  apply eqHom_trans'.
  intros X' Y' ff H1 H2 H3.
  destruct ff, f'; try reflexivity;
  inversion H1;
  inversion H2.
Qed.

Lemma two_thin: thin CatTwo.
Proof.
  intros X Y f f'.
  apply eqHom_trans'.
  intros X' Y' ff H1 H2 H3.
  destruct ff, f'; try reflexivity;
  inversion H1;
  inversion H2.
Qed.

Lemma zero_initial: @initial CatTwo Zero.
Proof.
  intros [ | ]; [exists IdZero | exists ZeroOne];
  apply two_thin.
Qed.


Definition FunASig: FunSig CatOne CatTwo := {|
  fmap1 _     := Zero: Ob CatTwo;
  fmap2 _ _ _ := IdZero
|}.

Definition FunA: Fun CatOne CatTwo.
  refine {| funSig := FunASig |}.
  constructor; simpl; intros; reflexivity.
Defined.

Definition FunBSig: FunSig CatOne CatTwo := {|
  fmap1 _     := One: Ob CatTwo;
  fmap2 _ _ _ := IdOne
|}.

Definition FunB: Fun CatOne CatTwo.
  refine {| funSig := FunBSig |}.
  constructor; simpl; intros; reflexivity.
Defined.

Definition NatAB: Nat FunA FunB.
  apply (Build_Nat CatOne CatTwo FunA FunB (fun _ => ZeroOne)).
  reflexivity.
Defined.



Definition xxFmap1(X: Ob CatTwo): Ob (FUN CatOne CatTwo) :=
  match X with Zero => FunA | One => FunB end.

Definition xxFmap2(X Y: Ob CatTwo)(f: Hom X Y): Hom (xxFmap1 X) (xxFmap1 Y) :=
  match f in (twoHom X' Y') return (Hom (xxFmap1 X') (xxFmap1 Y')) with
  | IdZero  => natId CatOne CatTwo FunA
  | IdOne   => natId CatOne CatTwo FunB
  | ZeroOne => NatAB
  end.

Definition xxx: Fun CatTwo (FUN CatOne CatTwo).
  refine {| funSig := {| fmap1 := xxFmap1; fmap2 := xxFmap2 |}|}.
  constructor.
  simpl.
  intros []; reflexivity.

  intros.
  repeat rewrite eq_comp_comp'.

  set (H1 := eq_refl Y).
  set (H2 := eq_refl _).
  set (Y' := Y).
  change (Hom X Y') in g.
  change (Y = Y') in H1.

  destruct g; simpl.
  intros.
  apply eqHom_trans.
  intros.
  simpl in * |- *.
  destruct (xxFmap2 X Z (twoComp X Y Z f g)).
  simpl in * |- *.

  set (fg := comp f g). simpl.
  assert (fg = comp f g) by reflexivity.
  destruct fg, Y; simpl.
  
