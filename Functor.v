Require Export Coq.Classes.Morphisms.

Require Export Category.


Polymorphic Record FunSig(A B: CatSig) := {
  fmap_o  :> A -> B;
  fmap X Y:  Hom X Y -> Hom (fmap_o X) (fmap_o Y)
}.

Global Arguments fmap_o {_ _}.
Global Arguments fmap   {_ _} _ {_ _}.

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

Polymorphic Instance fmap_eq_Proper{A B}{F: Fun A B}{X Y}: Proper (eq_h ==> eq_h) (@fmap A B F X Y) :=
  fmap_eq F.


Polymorphic Definition faithful{A B}(F: FunSig A B): Prop :=
  forall X Y (f f': Hom X Y), fmap F f = fmap F f' -> f = f'.

Polymorphic Definition full{A B}(F: FunSig A B): Prop :=
  forall X Y (f: Hom (F X) (F Y)), exists f', f = fmap F f'.
