Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Classes.Morphisms.


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

Polymorphic Instance eq_h_Equivalence{A: Cat}{X Y}: Equivalence (@eq_h A X Y) :=
  eq_h_equiv A X Y.

Polymorphic Instance comp_eq_Proper{A: Cat}{X Y Z}: Proper (eq_h ==> eq_h ==> eq_h) (@comp A X Y Z) :=
  comp_eq A X Y Z.


Polymorphic Definition thin(A: CatSig) :=
  forall (X Y: A)(f1 f2: Hom X Y), f1 = f2.


Polymorphic Record Ret{A: CatSig}{X Y: Ob A} := {
  ret_hom :> Hom X Y;
  ret_sec :  Hom Y X;
  ret_prop:  eq_h (comp ret_hom ret_sec) (id Y)
}.

Arguments Ret {_} _ _.


Polymorphic Record Sec{A: CatSig}{X Y: Ob A} := {
  sec_hom :> Hom X Y;
  sec_ret :  Hom Y X;
  sec_prop:  eq_h (comp sec_ret sec_hom) (id X)
}.

Arguments Sec {_} _ _.


Polymorphic Record Iso{A: CatSig}{X Y: Ob A} := {
  iso_hom :> Hom X Y;
  iso_inv :  Hom Y X;
  iso_prop:  eq_h (comp iso_hom iso_inv) (id Y) /\
             eq_h (comp iso_inv iso_hom) (id X)
}.

Arguments Iso {_} _ _.


Polymorphic Record Mon{A: CatSig}{X Y: Ob A} := {
  mon_hom :> Hom X Y;
  mon_prop:  forall{W}(g1 g2: Hom W X), eq_h (comp mon_hom g1) (comp mon_hom g2) -> eq_h g1 g2
}.

Arguments Mon {_} _ _.


Polymorphic Record Epi{A: CatSig}{X Y: Ob A} := {
  epi_hom :> Hom X Y;
  epi_prop:  forall{Z}(g1 g2: Hom Y Z), eq_h (comp g1 epi_hom) (comp g2 epi_hom) -> eq_h g1 g2
}.

Arguments Epi {_} _ _.


Polymorphic Definition sec_mon{A: Cat}{X Y: Ob A}(f: Sec X Y): Mon X Y.
  refine {| mon_hom := f |}.
  intros.
  transitivity (comp (id _) g2).
  transitivity (comp (comp (sec_ret f) f) g2).
  transitivity (comp (sec_ret f) (comp f g2)).
  transitivity (comp (sec_ret f) (comp f g1)).
  transitivity (comp (comp (sec_ret f) f) g1).
  transitivity (comp (id _) g1).
  symmetry. apply (ident_l A).
  f_equiv.
  symmetry. apply (sec_prop f).
  symmetry. apply (assoc A).
  f_equiv.
  assumption.
  apply (assoc A).
  f_equiv.
  apply (sec_prop f).
  apply (ident_l A).
Defined.


Polymorphic Definition ret_epi{A: Cat}{X Y: Ob A}(f: Ret X Y): Epi X Y.
  refine {| epi_hom := f |}.
  intros.
  transitivity (comp g1 (id _)).
  symmetry. apply (ident_r A).
  transitivity (comp g1 (comp f (ret_sec f))).
  f_equiv.
  symmetry. apply (ret_prop f).
  transitivity (comp (comp g1 f) (ret_sec f)).
  apply (assoc A).
  transitivity (comp (comp g2 f) (ret_sec f)).
  f_equiv.
  assumption.
  transitivity (comp g2 (comp f (ret_sec f))).
  symmetry. apply (assoc A).
  transitivity (comp g2 (id _)).
  f_equiv.
  apply (ret_prop f).
  apply (ident_r A).
Defined.


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

Polymorphic Definition iso_isomorphic{A}{X Y: Ob A}: Iso X Y -> isomorphic X Y.
  intro f.
  exists (iso_hom f).
  exists (iso_inv f).
  apply iso_prop.
Defined.


Polymorphic Record initial{A: CatSig}{X: A} := {
  initial_hom :> forall Y, Hom X Y;
  initial_uniq:  forall {Y} f, eq_h (initial_hom Y) f
}.

Arguments initial{_} _.

Polymorphic Record terminal{A: CatSig}{Y: A} := {
  terminal_hom :> forall X, Hom X Y;
  terminal_uniq:  forall {X} f, eq_h (terminal_hom X) f
}.

Arguments terminal{_} _.


Polymorphic Definition opSig(A: CatSig): CatSig := {|
  Ob             := A;
  Hom X Y        := Hom Y X;
  id             := id;
  comp X Y Z g f := comp f g;
  eq_h X Y f g   := eq_h g f;
|}.

Polymorphic Lemma opAx(A: Cat): CatAx (opSig A).
Proof.
  split; intros.
  split. intro f. simpl. reflexivity.
  intros f g H. simpl. symmetry. apply H.
  intros f g h H1 H2. simpl. transitivity g; assumption.
  intros f f' Hf g g' Hg. simpl. apply (comp_eq A); assumption.
  simpl. symmetry. apply (ident_l A).
  simpl. symmetry. apply (ident_r A).
  simpl. apply (assoc A).
Qed.

Polymorphic Definition op(A: Cat): Cat := {|
  catAx := opAx A
|}.


Polymorphic Definition id_iso{A: Cat}(X: A): Iso X X.
  refine {|
    iso_hom := id X;
    iso_inv := id X
  |}.
  split; apply (ident_r A).
Defined.


Polymorphic Definition comp_iso{A: Cat}{X Y Z: A}(g: Iso Y Z)(f: Iso X Y): Iso X Z.
  refine {|
    iso_hom := comp g f;
    iso_inv := comp (iso_inv f) (iso_inv g)
  |}.
  split.
  transitivity (comp g (comp (comp f (iso_inv f)) (iso_inv g))).
  transitivity (comp g (comp f (comp (iso_inv f) (iso_inv g)))).
  symmetry. apply (assoc A).
  f_equiv.
  apply (assoc A).
  transitivity (comp g (comp (id _) (iso_inv g))).
  f_equiv.
  f_equiv.
  apply (iso_prop f).
  transitivity (comp g (iso_inv g)).
  f_equiv.
  apply (ident_l A).
  apply (iso_prop g).
  transitivity (comp (iso_inv f) (comp (iso_inv g) (comp g f))).
  symmetry. apply (assoc A).
  transitivity (comp (iso_inv f) (comp (comp (iso_inv g) g) f)).
  f_equiv.
  apply (assoc A).
  transitivity (comp (iso_inv f) (comp (id _) f)).
  f_equiv.
  f_equiv.
  apply (iso_prop g).
  transitivity (comp (iso_inv f) f).
  f_equiv.
  apply (ident_l A).
  apply (iso_prop f).
Defined.

Polymorphic Definition isoCatSig(A: Cat): CatSig := {|
  Ob         := A;
  Hom        := Iso;
  id         := id_iso;
  comp X Y Z := comp_iso;
  eq_h X Y   := eq_h;
|}.

Polymorphic Lemma isoCatAx(A: Cat): CatAx (isoCatSig A).
Proof.
  split.
  intros X Y.
  split.
  intros f. simpl. reflexivity.
  intros f g H. simpl. symmetry. assumption.
  intros f g h H1 H2. simpl. transitivity (g: @Hom A _ _); assumption.
  intros X Y Z f1 f2 Hf g1 g2 Hg.
  simpl. f_equiv; assumption.
  intros X Y f. apply (ident_r A).
  intros X Y f. apply (ident_l A).
  intros W X Y Z h g f. apply (assoc A).
Qed.

Polymorphic Definition isoCat(A: Cat): Cat := {|
  catAx := isoCatAx A
|}.
