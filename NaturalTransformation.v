Require Export Category.
Require Export Functor.


Polymorphic Definition natural{A B}{F G: FunSig A B}
    (phi: forall X, Hom (F X) (G X)): Prop :=
  forall X Y (f: Hom X Y), 
    eq_h (comp (fmap G f) (phi X))
         (comp (phi Y) (fmap F f)).


Polymorphic Record NatTrans{A B}{F G: FunSig A B} := {
  natTrans        :> forall X, Hom (F X) (G X);
  natTrans_natural:  natural natTrans
}.

Arguments NatTrans {_ _} _ _.


Polymorphic Lemma iso_natural{A}{B: Cat}{F G: FunSig A B}
    (iso: forall X, Iso (F X) (G X)):
    natural (fun X => iso_hom (iso X)) -> 
    natural (fun X => iso_inv (iso X)).
Proof.
  intros H X Y f.
  set (gX := iso_hom (iso X)).
  set (hX := iso_inv (iso X)).
  set (gY := iso_hom (iso Y)).
  set (hY := iso_inv (iso Y)).
  set (H' := H X Y f: eq_h (comp (fmap G f) gX) (comp gY (fmap F f))).
  transitivity (comp (comp hY (fmap G f)) (id _)).
  transitivity (comp (comp hY (fmap G f)) (comp gX hX)).
  transitivity (comp hY (comp (comp (fmap G f) gX) hX)).
  transitivity (comp hY (comp (comp gY (fmap F f)) hX)).
  transitivity (comp (comp hY (comp gY (fmap F f))) hX).
  f_equiv.
  transitivity (comp (comp hY gY) (fmap F f)).
  transitivity (comp (id _) (fmap F f)).
  symmetry. apply (ident_l B).
  f_equiv.
  symmetry. apply iso_prop.
  symmetry. apply (assoc B).
  symmetry. apply (assoc B).
  f_equiv.
  f_equiv.
  symmetry. assumption.
  transitivity (comp hY (comp (fmap G f) (comp gX hX))).
  f_equiv.
  symmetry. apply (assoc B).
  apply (assoc B).
  f_equiv.
  apply iso_prop.
  apply (ident_r B).
Qed.
