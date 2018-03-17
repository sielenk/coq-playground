Require Import ProofIrrelevance.
Require Import EqdepFacts.



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

Definition semiGroupSig: SemiGroup -> SemiGroupSig := @proj1_sig _ _.
Coercion   semiGroupSig: SemiGroup >-> SemiGroupSig.

Definition semiGroupAx: forall G: SemiGroup, SemiGroupAx G := @proj2_sig _ _.
Coercion   semiGroupAx : SemiGroup >-> SemiGroupAx.

Definition isSemiGroupHom{h1 h2: SemiGroupSig}(f: h1 -> h2): Prop :=
  forall x1 x2, f (op x1 x2) = op (f x1) (f x2).

Definition SemiGroupHom(h1 h2: SemiGroupSig) := sig (@isSemiGroupHom h1 h2).

Definition semiGroupHomFun{h1 h2} : SemiGroupHom h1 h2 -> h1 -> h2 := @proj1_sig _ _.
Coercion   semiGroupHomFun: SemiGroupHom >-> Funclass.

Definition semiGroupHomAx{h1 h2} : forall f: SemiGroupHom h1 h2, isSemiGroupHom f := @proj2_sig _ _.
Coercion   semiGroupHomAx: SemiGroupHom >-> isSemiGroupHom.


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

Definition monoidSig: Monoid -> MonoidSig := @proj1_sig _ _.
Coercion   monoidSig: Monoid >-> MonoidSig.

Definition monoidAx: forall M: Monoid, MonoidAx M := @proj2_sig _ _.
Coercion   monoidAx : Monoid >-> MonoidAx.

Definition isMonoidHom{m1 m2: MonoidSig}(f: m1 -> m2): Prop :=
  isSemiGroupHom f /\ f unit = unit.

Definition MonoidHom(m1 m2: MonoidSig) := sig (@isMonoidHom m1 m2).

Definition monoidHomFun{m1 m2} : MonoidHom m1 m2 -> m1 -> m2 := @proj1_sig _ _.
Coercion   monoidHomFun: MonoidHom >-> Funclass.

Definition monoidHomAx{m1 m2} : forall f: MonoidHom m1 m2, isMonoidHom f := @proj2_sig _ _.
Coercion   monoidHomAx: MonoidHom >-> isMonoidHom.


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

Definition groupSig: Group -> GroupSig := @proj1_sig _ _.
Coercion   groupSig: Group >-> GroupSig.

Definition groupAx: forall g: Group, GroupAx g := @proj2_sig _ _.
Coercion   groupAx : Group >-> GroupAx.

Definition isGroupHom{g1 g2: GroupSig}(f: g1 -> g2): Prop :=
  isMonoidHom f /\ forall x, invert (f x) = f (invert x).

Definition GroupHom(g1 g2: GroupSig) := sig (@isGroupHom g1 g2).

Definition groupHomFun{g1 g2}: GroupHom g1 g2 -> g1 -> g2 := @proj1_sig _ _.
Coercion   groupHomFun: GroupHom >-> Funclass.

Definition groupHomAx{g1 g2} : forall f: GroupHom g1 g2, isGroupHom f := @proj2_sig _ _.
Coercion   groupHomAx: GroupHom >-> isGroupHom.


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

Lemma unitUnique2(g: Group): forall x y: g, op x y = x -> y = unit.
Proof.
  intros x y H.
  apply (leftInjection g x).
  rewrite (rightUnit g).
  assumption.
Qed.


Definition groupFromSemigroup(h: SemiGroup):
  h ->
  (forall a y: h, { x | op a x = y }) ->
  (forall a y: h, { x | op x a = y }) ->
  Group.

  intros b H1 H2.
  destruct (H2 b b) as [e He].
  set (inv y := proj1_sig (H2 y e)).
  exists (Build_GroupSig (Build_MonoidSig _ e) inv).
  apply makeGroupAx; simpl.
  apply (associative h).
  intro a.
  destruct (H1 b a) as [a' Ha'].
  transitivity (op e (op b a')).
  f_equal. symmetry. assumption.
  rewrite <- (associative h).
  rewrite He. assumption.
  intro a.
  unfold inv.
  destruct (H2 a e) as [a' Ha'].
  simpl. assumption.
Defined.


Lemma semiGroupHomIsGroupHom{g1 g2: Group}: SemiGroupHom g1 g2 -> GroupHom g1 g2.
Proof.
  intro f.
  set (H1 := semiGroupHomAx f).
  assert (H2: f unit = unit).
  apply (unitUnique2 _ (f unit)).
  rewrite <- H1. f_equal. apply (rightUnit g1).
  exists f.
  repeat split; try assumption.
  intro x.
  symmetry. apply inverseUnique.
  rewrite <- H1.
  rewrite (rightInverse g1).
  assumption.
Qed.

Lemma groupAxFromHom{g1: GroupSig}{g2: Group}(f: GroupHom g1 g2): (forall x y, f x = f y -> x = y) -> GroupAx g1.
Proof.
  destruct f as [f [[H1 H2] H3]]. simpl. intro H4.
  unfold isSemiGroupHom in H1.
  apply makeGroupAx; intros; apply H4; repeat rewrite H1.
  apply (associative g2).
  rewrite H2. apply (leftUnit g2).
  rewrite H2. rewrite <- H3. apply (leftInverse g2).
Qed.


Definition kernSig{g1 g2: Group}(f: GroupHom g1 g2): GroupSig.
  destruct (groupHomAx f) as [[H1 H2] H3].
  unfold isSemiGroupHom in H1.
  refine (
      Build_GroupSig (
        Build_MonoidSig (
          Build_SemiGroupSig
            { x | f x = unit }
            (fun x y =>
              let (x', Hx) := x in
              let (y', Hy) := y in
                exist _ (op x' y') _))
          (exist _ unit _))
        (fun x =>
          let (x', Hx) := x in
            exist _ (invert x') _)).
  clear x. simpl in Hx.
  rewrite <- H3.
  rewrite Hx.
  apply (unitUnique2 g2 unit).
  apply (rightInverse g2).
  Unshelve.
  simpl in Hx, Hy.
  rewrite H1, Hx, Hy.
  apply (rightUnit g2).
  assumption.
Defined.

Definition kernHom{g1 g2: Group}(f: GroupHom g1 g2): GroupHom (kernSig f) g1.
  destruct f as [f [[H1 H2] H3]].
  exists (@proj1_sig _ _). simpl.
  repeat split.
  unfold isSemiGroupHom; simpl.
  intros [x Hx] [y Hy]; simpl.
  reflexivity.
  intros [x Hx]; simpl.
  reflexivity.
Defined.

Lemma kernHomInjective{g1 g2: Group}(f: GroupHom g1 g2): forall x y, kernHom f x = kernHom f y -> x = y.
Proof.
  destruct f as [f [[H1 H2] H3]]. simpl.
  intros [x Hx] [y Hy]. simpl.
  apply subset_eq_compat.
Qed.

Lemma kernAx{g1 g2: Group}(f: GroupHom g1 g2): GroupAx (kernSig f).
Proof.
  apply (groupAxFromHom _ (kernHomInjective f)).
Qed.

Definition kern{g1 g2} f: Group := exist _ _ (@kernAx g1 g2 f).

