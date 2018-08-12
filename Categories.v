Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.


Definition eqF{X Y}(H: X = Y): X -> Y :=
  match H in _ = Y' return X -> Y' with
  | eq_refl _ => fun x => x
  end.


Polymorphic Cumulative Record Cat := {
  Ob: Type;
  Hom: Ob -> Ob -> Type;
  id X: Hom X X;
  comp{X Y Z}: Hom Y Z -> Hom X Y -> Hom X Z;
  ident_r{X Y}(f: Hom X Y): comp f (id _) = f;
  ident_l{X Y}(f: Hom X Y): comp (id _) f = f;
  assoc{W X Y Z}(f: Hom Y Z)(g: Hom X Y)(h: Hom W X):
    comp (comp f g) h = comp f (comp g h)
}.

Arguments Hom {c}.
Arguments id  {c}.
Arguments comp{c X Y Z}.

Lemma catEq(A B: Cat):
    forall
      (eqOb: Ob A = Ob B)
      (eqHom: forall X Y, Hom X Y = Hom (eqF eqOb X) (eqF eqOb Y)),
      (forall X, eqF (eqHom X X) (id X) = id (eqF eqOb X)) ->
      (forall X Y Z f g,
      eqF (eqHom X Z) (comp f g) = comp (eqF (eqHom Y Z) f) (eqF (eqHom X Y) g)) ->
      A = B.
Proof.
  destruct A, B. simpl.
  intro H. destruct H. simpl.
  intro H1.
  assert (H': Hom0 = Hom1). extensionality X. extensionality Y.
  apply H1. destruct H'.
  intro H2.
  assert (H': id0 = id1). extensionality X.
  rewrite <- H2.
  rewrite (proof_irrelevance _ (H1 X X) (eq_refl _)).
  reflexivity. destruct H'.
  intro H3.
  assert (H': comp0 = comp1).
  extensionality X. extensionality Y. extensionality Z. extensionality f. extensionality g.
  set (H' := H3 X Y Z f g).
  rewrite (proof_irrelevance _ (H1 X Z) (eq_refl _)) in H'.
  rewrite (proof_irrelevance _ (H1 X Y) (eq_refl _)) in H'.
  rewrite (proof_irrelevance _ (H1 Y Z) (eq_refl _)) in H'.
  apply H'.
  destruct H'.
  f_equal; apply proof_irrelevance.
Qed.


Polymorphic Cumulative Record Fun(A B: Cat) := {
  fmap1: Ob A -> Ob B;
  fmap2{X Y}: Hom X Y -> Hom (fmap1 X) (fmap1 Y);
  fmap_id: forall X, fmap2 (id X) = id _;
  fmap_comp{X Y Z}(f: Hom Y Z)(g: Hom X Y):
    fmap2 (comp f g) = comp (fmap2 f) (fmap2 g)
}.

Arguments fmap1 {A B}.
Arguments fmap2 {A B} f {X Y}.

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
  destruct F, G. simpl.
  intros H1 H2.
  assert (H': fmap3 = fmap5). extensionality X.
  apply H1. destruct H'.
  assert (H': fmap4 = fmap6). extensionality X. extensionality Y. extensionality f.
  rewrite <- H2.
  rewrite (proof_irrelevance _ _ (eq_refl _)). reflexivity.
  destruct H'.
  f_equal; apply proof_irrelevance.
Qed.


Polymorphic Cumulative Record Nat{A B}(F G: Fun A B) := {
  eta: forall X, Hom (fmap1 F X) (fmap1 G X);
  eta_ax{X Y}(f: Hom X Y):
    comp (fmap2 G f) (eta X) = comp (eta Y) (fmap2 F f)
}.

Arguments eta {A B F G}.

Lemma natEq{A B}{F G: Fun A B}(M N: Nat F G): (forall X, eta N X = eta M X) -> M = N.
Proof.
  destruct M, N. simpl.
  intro H.
  assert (H': eta1 = eta0). extensionality X.
  apply H.
  destruct H'.
  f_equal; apply proof_irrelevance.
Qed.



Definition catId A: Fun A A.
  apply (Build_Fun _ _ (fun X => X) (fun _ _ f => f)); reflexivity.
Defined.

Definition catComp A B C (F: Fun B C)(G: Fun A B): Fun A C.
  apply (Build_Fun _ _
    (fun X => fmap1 F (fmap1 G X))
    (fun _ _ f => fmap2 F (fmap2 G f))).
  intros. repeat rewrite fmap_id. reflexivity.
  intros. repeat rewrite fmap_comp. reflexivity.
Defined.

Definition CAT: Cat.
  apply (Build_Cat Cat Fun catId catComp).
  intros A B F. refine (funEq _ _ _ _).
  intros X Y f.
  rewrite (proof_irrelevance _ _ (eq_refl _)).
  reflexivity.
  intros A B F. refine (funEq _ _ _ _).
  intros X Y f.
  rewrite (proof_irrelevance _ _ (eq_refl _)).
  reflexivity.
  intros A B C D F G H. refine (funEq _ _ _ _).
  intros X Y f.
  rewrite (proof_irrelevance _ _ (eq_refl _)).
  reflexivity.
  Unshelve.
  intros; reflexivity.
  intros; reflexivity.
  intros; reflexivity.
Defined.

Section Foo.
  Variable A B: Cat.

  Definition funId(F: Fun A B): Nat F F.
    apply (Build_Nat A B F F (fun X => id _)).
    intros.
    rewrite ident_r.
    rewrite ident_l.
    reflexivity.
  Defined.

  Definition funComp(F G H: Fun A B)(N: Nat G H)(M: Nat F G): Nat F H.
    apply (Build_Nat A B F H (fun X => comp (eta N X) (eta M X))).
    intros.
    rewrite assoc.
    rewrite <- eta_ax.
    rewrite <- assoc.
    rewrite eta_ax.
    apply assoc.
  Defined.

  Definition FUN: Cat.
    apply (Build_Cat (Fun A B) Nat funId funComp).
    intros F G N. refine (natEq _ _ _).
    intro X. simpl.
    rewrite ident_r. reflexivity.
    intros F G N. refine (natEq _ _ _).
    intro X. simpl.
    rewrite ident_l. reflexivity.
    intros F G H I N M O. refine (natEq _ _ _).
    intro X. simpl.
    symmetry. apply assoc.
  Defined.
End Foo.






Inductive oneOb := UnitOb.

Inductive oneHom: oneOb -> oneOb -> Type :=
  UnitHom: oneHom UnitOb UnitOb.

Definition oneId(X: oneOb): oneHom X X :=
  match X as X' return (oneHom X' X') with
  | UnitOb => UnitHom
  end.

Definition oneComp X Y Z (f: oneHom Y Z)(g: oneHom X Y): oneHom X Z :=
  match X as X', Z as Z' return (oneHom X' Z') with
  | UnitOb, UnitOb => UnitHom
  end.

Definition CatOne: Cat.
  apply (Build_Cat oneOb oneHom oneId oneComp).
  intros X Y []. reflexivity.
  intros X Y []. reflexivity.
  intros [] X Y [] f g h. reflexivity.
Defined.


Inductive twoOb := Zero | One.

Inductive twoHom: twoOb -> twoOb -> Type :=
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
  set (Y' := Y) in g.
  assert (Y = Y') by reflexivity.
  generalize dependent Y'.
  intros Y' g H.
  destruct f, g; try constructor.
  inversion H.
Defined.

Definition CatTwo: Cat.
  assert (H1: forall (X Y : twoOb) (f : twoHom X Y),
    twoComp X X Y f (twoId X) = f).
  intros X Y []; reflexivity.

  assert (H2: forall (X Y : twoOb) (f : twoHom X Y),
    twoComp X Y Y (twoId Y) f = f).
  intros X Y []; reflexivity.

  apply (Build_Cat twoOb twoHom twoId twoComp H1 H2).
  intros W X Y Z f g h.
  destruct f; try (repeat rewrite H2; reflexivity).
  destruct h; try (repeat rewrite H1; reflexivity).
  inversion g.
Defined.


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
  | IdZero => funId CatOne CatTwo FunA
  | IdOne => funId CatOne CatTwo FunB
  | ZeroOne => NatAB
  end.

Definition xxx: Fun CatTwo (FUN CatOne CatTwo).
  refine (Build_Fun _ _ xxFmap1 xxFmap2 _ _).
  simpl. intros []; reflexivity.
  intros.
  set (fg := comp f g).
  assert (fg = comp f g) by reflexivity.
  destruct fg, Y; simpl.
  
