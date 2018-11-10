Require Export Category.
Require Export Functor.


Polymorphic Record NatTrans{A B}(F G: FunSig A B) := {
  preNatTrans :> forall X, Hom (F X) (G X);
  natural     :  forall X Y (f: Hom X Y), 
                   eq_h (comp (fmap G f) (preNatTrans X))
                        (comp (preNatTrans Y) (fmap F f))
}.
