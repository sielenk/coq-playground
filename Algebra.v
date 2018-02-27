Record SemiGroupSig := {
  carrier: Set;
  op: carrier -> carrier -> carrier
}.

Arguments op {s}.

Coercion carrier: SemiGroupSig >-> Sortclass.

Record SemiGroupAx(sig: SemiGroupSig) := {
  associative: forall x y z: sig, op (op x y) z = op x (op y z);
}.

Arguments associative {sig}.

Definition SemiGroup := sig SemiGroupAx.

Definition semiGroupSig(h: SemiGroup) := let (sig, _) := h in sig.
Definition semiGroupAx (h: SemiGroup) :=
  match h as h' return SemiGroupAx (semiGroupSig h') with exist _ _ ax => ax end.

Coercion semiGroupSig: SemiGroup >-> SemiGroupSig.
Coercion semiGroupAx : SemiGroup >-> SemiGroupAx.

Definition lTrans(h: SemiGroupSig)(a: h): h -> h := op a.
Definition rTrans(h: SemiGroupSig)(a: h): h -> h := fun x => op x a.


(***************************************************************)


Record MonoidSig := {
  monoidSigIsSemiGroup: SemiGroupSig;
  unit: monoidSigIsSemiGroup;
}.

Arguments unit {m}.

Coercion monoidSigIsSemiGroup: MonoidSig >-> SemiGroupSig.

Record MonoidAx(sig: MonoidSig) := {
  monoidIsSemiGroupAx: SemiGroupAx sig;
  leftUnit:     forall x: sig, op unit x = x;
  rightUnit:    forall x: sig, op x unit = x
}.

Arguments leftUnit {sig}.
Arguments rightUnit {sig}.

Coercion monoidIsSemiGroupAx: MonoidAx >-> SemiGroupAx.

Definition Monoid := sig MonoidAx.

Definition monoidSig(m: Monoid) := let (sig, _) := m in sig.
Definition monoidAx (m: Monoid) :=
  match m as m' return MonoidAx (monoidSig m') with exist _ _ ax => ax end.

Coercion monoidSig: Monoid >-> MonoidSig.
Coercion monoidAx : Monoid >-> MonoidAx.


Lemma unitUnique(m: Monoid): forall e: m, (forall x, op x e = x) -> e = unit.
Proof.
  intros e H.
  rewrite <- (leftUnit m e).
  apply H.
Qed.


(***************************************************************)


Record GroupSig := {
  groupSigIsMonoidSig: MonoidSig;
  invert: groupSigIsMonoidSig -> groupSigIsMonoidSig
}.

Arguments invert {g}.

Coercion groupSigIsMonoidSig: GroupSig >-> MonoidSig.

Record GroupAx(sig: GroupSig) := {
  groupIsMonoidAx: MonoidAx sig;
  leftInverse:  forall x: sig, op (invert x) x = unit;
  rightInverse: forall x: sig, op x (invert x) = unit
}.

Arguments leftInverse {sig}.
Arguments rightInverse {sig}.

Coercion groupIsMonoidAx: GroupAx >-> MonoidAx.

Definition Group := sig GroupAx.

Definition groupSig(g: Group) := let (sig, _) := g in sig.
Definition groupAx (g: Group) :=
  match g as g' return GroupAx (groupSig g') with exist _ _ ax => ax end.

Coercion groupSig: Group >-> GroupSig.
Coercion groupAx : Group >-> GroupAx.


Lemma makeGroupAx(sig: GroupSig):
  (forall x y z: sig, op (op x y) z = op x (op y z)) ->
  (forall x: sig, op unit x = x) ->
  (forall x: sig, op (invert x) x = unit) ->
  GroupAx sig.
Proof.
  intros assoc leftUnit leftInverse.
  assert (rightInverse: forall x : sig, op x (invert x) = unit).
  intros x.
  rewrite <- (leftUnit (op x (invert x))).
  transitivity (op (op (invert (invert x)) (invert x)) (op x (invert x))).
  f_equal. symmetry. apply leftInverse.
  transitivity (op (invert (invert x)) (op (op (invert x) x) (invert x))).
  rewrite assoc. f_equal. symmetry. apply assoc.
  rewrite leftInverse.
  rewrite leftUnit.
  apply leftInverse.
  repeat (split; try assumption).
  intros x.
  rewrite <- (leftInverse x).
  rewrite <- assoc.
  rewrite rightInverse.
  apply leftUnit.
Qed.


Lemma inverseUnique(g: Group): forall x y: g, op x y = unit -> y = invert x.
Proof.
  intros x y H.
  rewrite <- (rightUnit g (invert x)).
  rewrite <- H.
  rewrite <- (associative g).
  rewrite (leftInverse g).
  symmetry. apply (leftUnit g).
Qed.

Lemma leftInjection(g: Group): forall a x y: g, op a x = op a y-> x = y.
Proof.
  intros a x y H.
  rewrite <- (leftUnit g x).
  rewrite <- (leftInverse g a).
  rewrite (associative g).
  rewrite H.
  rewrite <- (associative g).
  rewrite (leftInverse g a).
  apply (leftUnit g y).
Qed.

Lemma rightInjection(g: Group): forall a x y: g, op x a = op y a -> x = y.
Proof.
  intros a x y H.
  rewrite <- (rightUnit g x).
  rewrite <- (rightInverse g a).
  rewrite <- (associative g).
  rewrite H.
  rewrite (associative g).
  rewrite (rightInverse g a).
  apply (rightUnit g y).
Qed.


Definition groupFromSemigroup(h: SemiGroup): h -> (forall a y: h, { x | op a x = y } * { x | op x a = y }) -> Group.
  intros b H.
  destruct (snd (H b b)) as [e He].
  set (inv y := proj1_sig (snd (H y e))).
  exists (Build_GroupSig (Build_MonoidSig _ e) inv).
  apply makeGroupAx; simpl.
  apply (associative h).
  intro a.
  destruct (fst (H b a)) as [a' Ha'].
  transitivity (op e (op b a')).
  f_equal. symmetry. assumption.
  rewrite <- (associative h).
  rewrite He. assumption.
  intro a.
  unfold inv.
  destruct (snd (H a e)) as [a' Ha'].
  simpl. assumption.
Defined.
