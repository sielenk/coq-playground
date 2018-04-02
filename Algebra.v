Require Import ProofIrrelevance.
Require Import EqdepFacts.

Delimit Scope group_scope with group.
Local Open Scope group_scope.


Record SemiGroupSig := {
  carrier: Set;
  op: carrier -> carrier -> carrier
}.

Definition makeSemiGroupSig{X: Set}(op: X -> X -> X): SemiGroupSig :=
  Build_SemiGroupSig X op.

Arguments op {s}.

Notation "x * y" := (op x y) : group_scope.



Coercion carrier: SemiGroupSig >-> Sortclass.

Record SemiGroupAx(sig: SemiGroupSig) := {
  associative: forall x y z: sig, (x * y) * z = x * (y * z);
}.

Arguments associative {sig}.

Definition SemiGroup := sig SemiGroupAx.

Definition semiGroupSig: SemiGroup -> SemiGroupSig := @proj1_sig _ _.
Coercion   semiGroupSig: SemiGroup >-> SemiGroupSig.

Definition semiGroupAx: forall G: SemiGroup, SemiGroupAx G := @proj2_sig _ _.
Coercion   semiGroupAx : SemiGroup >-> SemiGroupAx.

Definition isSemiGroupHom{h1 h2: SemiGroupSig}(f: h1 -> h2): Prop :=
  forall x1 x2, f (x1 * x2) = f x1 * f x2.

Definition SemiGroupHom(h1 h2: SemiGroupSig) := sig (@isSemiGroupHom h1 h2).

Definition semiGroupHomFun{h1 h2} : SemiGroupHom h1 h2 -> h1 -> h2 := @proj1_sig _ _.
Coercion   semiGroupHomFun: SemiGroupHom >-> Funclass.

Definition semiGroupHomAx{h1 h2} : forall f: SemiGroupHom h1 h2, isSemiGroupHom f := @proj2_sig _ _.
Coercion   semiGroupHomAx: SemiGroupHom >-> isSemiGroupHom.


Definition abelian(h: SemiGroupSig) := forall a b: h, a * b = b * a.


(***************************************************************)


Record MonoidSig := {
  monoidSigIsSemiGroup: SemiGroupSig;
  unit: monoidSigIsSemiGroup;
}.

Definition makeMonoidSig{X: Set}(op: X -> X -> X)(unit: X): MonoidSig :=
  Build_MonoidSig (makeSemiGroupSig op) unit.

Arguments unit {m}.

Coercion monoidSigIsSemiGroup: MonoidSig >-> SemiGroupSig.

Record MonoidAx(sig: MonoidSig) := {
  monoidIsSemiGroupAx: SemiGroupAx sig;
  leftUnit:     forall x: sig, unit * x = x;
  rightUnit:    forall x: sig, x * unit = x
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


Lemma unitUnique(m: Monoid): forall e: m, (forall x, x * e = x) -> e = unit.
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

Definition makeGroupSig{X: Set}(op: X -> X -> X)(unit: X)(invert: X -> X): GroupSig :=
  Build_GroupSig (makeMonoidSig op unit) invert.


Arguments invert {g}.

Coercion groupSigIsMonoidSig: GroupSig >-> MonoidSig.

Record GroupAx(sig: GroupSig) := {
  groupIsMonoidAx: MonoidAx sig;
  leftInverse:  forall x: sig, invert x * x = unit;
  rightInverse: forall x: sig, x * invert x = unit
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

Definition groupHomAx{g1 g2}: forall f: GroupHom g1 g2, isGroupHom f := @proj2_sig _ _.
Coercion   groupHomAx: GroupHom >-> isGroupHom.


Lemma makeGroupAx(sig: GroupSig):
  (forall x y z: sig, (x * y) * z = x * (y * z)) ->
  (forall x: sig, unit * x = x) ->
  (forall x: sig, invert x * x = unit) ->
  GroupAx sig.
Proof.
  intros assoc leftUnit leftInverse.
  assert (rightInverse: forall x : sig, x * invert x = unit).
  intros x.
  rewrite <- (leftUnit (x * invert x)).
  transitivity ((invert (invert x) * invert x) * (x * invert x)).
  f_equal. symmetry. apply leftInverse.
  transitivity (invert (invert x) * ((invert x * x) * invert x)).
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


Lemma inverseUnique(g: Group): forall x y: g, x * y = unit -> y = invert x.
Proof.
  intros x y H.
  rewrite <- (rightUnit g (invert x)).
  rewrite <- H.
  rewrite <- (associative g).
  rewrite (leftInverse g).
  symmetry. apply (leftUnit g).
Qed.

Lemma inverseId(g: Group): forall x: g, invert (invert x) = x.
Proof.
  intros x.
  symmetry.
  apply (inverseUnique g).
  apply (leftInverse g).
Qed.

Lemma inverseUnit(g: Group): @invert g unit = unit.
Proof.
  symmetry.
  apply (inverseUnique g).
  apply (leftUnit g).
Qed.

Lemma inverseOp(g: Group): forall a b: g, invert (a * b) = invert b * invert a.
Proof.
  intros a b.
  symmetry.
  apply (inverseUnique g).
  rewrite (associative g).
  rewrite <- (associative g b (invert b)).
  rewrite (rightInverse g).
  rewrite (leftUnit g).
  apply (rightInverse g).
Qed.

Lemma leftInjection(g: Group): forall a x y: g, a * x = a * y-> x = y.
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

Lemma rightInjection(g: Group): forall a x y: g, x * a = y * a -> x = y.
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

Lemma unitUnique2(g: Group): forall x y: g, x * y = x -> y = unit.
Proof.
  intros x y H.
  apply (leftInjection g x).
  rewrite (rightUnit g).
  assumption.
Qed.


Definition groupFromSemigroup(h: SemiGroup):
  h ->
  (forall a y: h, { x | a * x = y }) ->
  (forall a y: h, { x | x * a = y }) ->
  Group.

  intros b H1 H2.
  destruct (H2 b b) as [e He].
  set (inv y := proj1_sig (H2 y e)).
  exists (Build_GroupSig (Build_MonoidSig _ e) inv).
  apply makeGroupAx; simpl.
  apply (associative h).
  intro a.
  destruct (H1 b a) as [a' Ha'].
  transitivity (e * (b * a')).
  f_equal. auto.
  rewrite <- (associative h).
  rewrite He. assumption.
  intro a.
  unfold inv.
  destruct (H2 a e) as [a' Ha'].
  simpl. assumption.
Defined.


Lemma semiGroupHomIsGroupHom{g1 g2: Group}(f: g1 -> g2): isSemiGroupHom f -> isGroupHom f.
Proof.
  intro H1.
  assert (H2: f unit = unit).
  apply (unitUnique2 _ (f unit)).
  rewrite <- H1. f_equal. apply (rightUnit g1).
  repeat split; try assumption.
  intro x.
  symmetry. apply inverseUnique.
  rewrite <- H1.
  rewrite (rightInverse g1).
  assumption.
Qed.

Lemma semiGroupHomToGroupHom{g1 g2: Group}: SemiGroupHom g1 g2 -> GroupHom g1 g2.
Proof.
  intros [f H1].
  exists f.
  apply (semiGroupHomIsGroupHom _ H1).
Qed.

Lemma groupAxFromHom{g1: GroupSig}{g2: Group}(f: GroupHom g1 g2): (forall x y, f x = f y -> x = y) -> GroupAx g1.
Proof.
  destruct f as [f [[H1 H2] H3]].
  unfold isSemiGroupHom in H1.
  simpl. intro H4.
  apply makeGroupAx; intros; apply H4; repeat rewrite H1.
  apply (associative g2).
  rewrite H2. apply (leftUnit g2).
  rewrite H2. rewrite <- H3. apply (leftInverse g2).
Qed.


Inductive SubGroup(g: Group) :=
  makeSubGroup(P: g -> Prop): (exists a, P a) -> (forall a b, P a -> P b -> P (a * invert b)) -> SubGroup g.

Definition isIn{g: Group}(h: SubGroup g): g -> Prop := let (P, _, _) := h in P.

Lemma unitIsIn{g: Group}(h: SubGroup g): isIn h unit.
Proof.
  destruct h as [P H1 H2]. simpl.
  destruct H1 as [a Ha].
  rewrite <- (rightInverse g a).
  apply H2; assumption.
Qed.

Lemma invertIsIn{g: Group}(h: SubGroup g)(a: g): isIn h a -> isIn h (invert a).
Proof.
  set (H1 := unitIsIn h).
  destruct h as [P H2 H3]. simpl in H1 |- *.
  intro Ha.
  rewrite <- (leftUnit g (invert a)).
  apply H3; try assumption.
Qed.

Lemma opIsIn{g: Group}(h: SubGroup g)(a b: g): isIn h a -> isIn h b -> isIn h (a * b).
Proof.
  set (H1 := invertIsIn h).
  destruct h as [P H2 H3]. simpl in H1 |- *.
  intros Ha Hb.
  rewrite <- (inverseId g b).
  apply H3; try assumption.
  apply H1; try assumption.
Qed.


Definition subGroupSig{g: Group}(h: SubGroup g): GroupSig :=
    makeGroupSig (X := sig (isIn h))
      (fun x y =>
        let (x', Hx) := x in
        let (y', Hy) := y in
          exist _ (x' * y') (opIsIn h x' y' Hx Hy))
      (exist _ unit (unitIsIn h))
      (fun x =>
        let (x', Hx) := x in
          exist _ (invert x') (invertIsIn h x' Hx)).



Definition subGroupInsert{g: Group}(h: SubGroup g): forall x, isIn h x -> subGroupSig h :=
  match h as h' return (forall x, isIn h' x -> subGroupSig h') with
  | makeSubGroup _ P _ _ => exist P
  end.

Definition subGroupExtract{g: Group}(h: SubGroup g): GroupHom (subGroupSig h) g.
  destruct h as [P H1 H2].
  exists (@proj1_sig _ _).
  repeat split.
  unfold isSemiGroupHom; simpl.
  intros [x Hx] [y Hy]; simpl.
  reflexivity.
  intros [x Hx]; simpl.
  reflexivity.
Defined.



Lemma subGroupInsertUnit{g: Group}(h: SubGroup g) H: subGroupInsert h unit H = unit.
Proof.
  destruct h as [P H1 H2].
  simpl.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma subGroupInsertInvert{g: Group}(h: SubGroup g) x H1 H2: subGroupInsert h (invert x) H1 = invert (subGroupInsert h x H2).
Proof.
  destruct h as [P H3 H4].
  simpl.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma subGroupInsertOp{g: Group}(h: SubGroup g) x y H1 H2 H3:
  subGroupInsert h (op x y) H1 = op (subGroupInsert h x H2) (subGroupInsert h y H3).
Proof.
  destruct h as [P H4 H5].
  simpl.
  f_equal.
  apply proof_irrelevance.
Qed.

Lemma subGroupEmbedding{g: Group}(h: SubGroup g): forall x y, subGroupExtract h x = subGroupExtract h y -> x = y.
Proof.
  destruct h as [P H1 H2].
  intros [x Hx] [y Hy]. simpl.
  apply subset_eq_compat.
Qed.

Lemma subGroupInOut{g: Group}(h: SubGroup g) x H: subGroupExtract h (subGroupInsert h x H) = x.
Proof.
  destruct h as [P H1 H2].
  reflexivity.
Qed.


Lemma subGroupAx{g: Group}(h: SubGroup g): GroupAx (subGroupSig h).
Proof.
  apply (groupAxFromHom _ (subGroupEmbedding _)).
Qed.

Definition subGroup{g: Group}(h: SubGroup g): Group := exist _ _ (subGroupAx h).

Coercion subGroup: SubGroup >-> Group.



Definition subSubGroup{g: Group}(h: SubGroup g)(k: SubGroup h): SubGroup g.
  refine (makeSubGroup g (fun x => ex (fun H => isIn k (subGroupInsert h x H))) _ _).
  exists unit.
  exists (unitIsIn h).
  rewrite subGroupInsertUnit.
  apply (unitIsIn k).
  intros a b [Ha1 Ha2] [Hb1 Hb2].
  exists (opIsIn _ _ _ Ha1 (invertIsIn _ _ Hb1)).
  rewrite (subGroupInsertOp _ _ _ _ Ha1 (invertIsIn _ _ Hb1)).
  rewrite (subGroupInsertInvert _ _ (invertIsIn _ _ Hb1) Hb1).
  apply (opIsIn k); try assumption.
  apply (invertIsIn k); assumption.
Defined.

Definition subGroupCut{g: Group}(I: Type)(hi: I -> SubGroup g): SubGroup g.
  refine (makeSubGroup g (fun x => forall i, isIn (hi i) x) _ _).
  exists unit.
  intro i; apply (unitIsIn _).
  intros a b Ha Hb i.
  apply opIsIn; try apply Ha; apply invertIsIn; apply Hb.
Defined.


Definition minimalSubGroup(g: Group): SubGroup g.
  refine (makeSubGroup g (eq unit) (ex_intro _ _ eq_refl) (fun a b => _)).
  intros [] [].
  rewrite inverseUnit.
  rewrite (rightUnit g).
  reflexivity.
Defined.

Definition maximalSubGroup(g: Group): SubGroup g :=
  makeSubGroup g (fun x => True) (ex_intro _ unit I) (fun _ _ _ _ => I).

Definition kern{g1 g2: Group}(f: GroupHom g1 g2): SubGroup g1.
  destruct (groupHomAx f) as [[H1 H2] H3].
  unfold isSemiGroupHom in H1.
  refine (makeSubGroup g1 (fun x => f x = unit) (ex_intro _ unit H2) (fun a b H4 H5 => _)).
  simpl in H4, H5.
  rewrite H1, H4.
  rewrite <- H3.
  rewrite H5.
  rewrite inverseUnit.
  apply (rightUnit g2).
Defined.

Definition image{g1 g2: Group}(f: GroupHom g1 g2): SubGroup g2.
  destruct (groupHomAx f) as [[H1 H2] H3].
  unfold isSemiGroupHom in H1.
  refine (makeSubGroup g2 (fun x => ex (fun y => f y = x)) (ex_intro _ _ (ex_intro _ _ H2)) (fun a b => _)).
  intros [a' Ha] [b' Hb].
  exists (a' * invert b').
  rewrite H1. rewrite <- H3, Ha, Hb.
  reflexivity.
Defined.


Definition centralizer(g: Group)(P: g -> Prop): SubGroup g.
  refine (makeSubGroup g (fun a => forall x, P x -> a * x = x * a) (ex_intro _ unit _) (fun a b => _)).
  intros x H.
  rewrite (rightUnit g).
  apply (leftUnit g).
  intros H1 H2 x Hx.
  rewrite <- (associative g).
  rewrite <- (H1 x Hx).
  repeat rewrite (associative g).
  f_equal.
  apply (rightInjection g b).
  repeat rewrite (associative g).
  rewrite <- (H2 x Hx).
  rewrite <- (associative g).
  rewrite (leftInverse g).
  rewrite (rightUnit g).
  apply (leftUnit g).
Defined.

Definition center(g: Group) := centralizer g (fun _ => True).

Lemma centerInCentralizer(g: Group)(P: g -> Prop): forall a, isIn (center g) a -> isIn (centralizer g P) a.
Proof.
  intros a Ha.
  simpl in Ha.
  intros b Hb.
  apply Ha.
  auto.
Qed.

Lemma centerAbelian(g: Group): abelian (center g).
Proof.
  intros [a Ha] [b Hb].
  apply subGroupEmbedding.
  simpl.
  rewrite Ha; auto.
Qed.


Definition konjugated{g: Group}(x y: g): Prop :=
  ex (fun a => x = a * y * invert a).

Lemma konjugatedReflexive{g: Group}(x: g): konjugated x x.
Proof.
  exists unit.
  rewrite (leftUnit g).
  rewrite (inverseUnit g).
  rewrite (rightUnit g).
  auto.
Qed.

Lemma konjugatedSymmetric{g: Group}(x y: g): konjugated x y -> konjugated y x.
Proof.
  intros [a H].
  exists (invert a).
  rewrite H.
  transitivity ((invert a * a) * y * (invert a * invert (invert a))).
  rewrite (rightInverse g).
  rewrite (leftInverse g).
  rewrite (rightUnit g).
  rewrite (leftUnit g).
  auto.
  repeat rewrite (associative g).
  auto.
Qed.

Lemma konjugatedTransitive{g: Group}(x y z: g): konjugated x y -> konjugated y z -> konjugated x z.
Proof.
  intros [a Ha] [b Hb].
  exists (a * b).
  rewrite Ha, Hb.
  repeat rewrite (associative g).
  repeat f_equal.
  rewrite inverseOp.
  auto.
Qed.


Definition automorphism{g: Group}(a: g): GroupHom g g.
  exists (fun x => a * x * invert a).
  apply semiGroupHomIsGroupHom.
  intros x y.
  repeat rewrite (associative g).
  f_equal. f_equal.
  rewrite <- (associative g).
  rewrite (leftInverse g).
  rewrite (leftUnit g).
  reflexivity.
Defined.


Definition isNormal{g: Group}(h: SubGroup g): Prop :=
  let (P, _, _) := h in forall x a, P (a * x * invert a) -> P x.

Lemma minimalIsNormal(g: Group): isNormal (minimalSubGroup g).
Proof.
  intros x a H.
  apply (leftInjection g a).
  apply (rightInjection g (invert a)).
  rewrite <- H.
  rewrite (rightUnit g).
  apply (rightInverse g).
Qed.

Lemma maximalIsNormal(g: Group): isNormal (maximalSubGroup g).
Proof.
  intros x a H.
  auto.
Qed.

Lemma kernIsNormal{g1 g2: Group}(f: GroupHom g1 g2): isNormal (kern f).
Proof.
  destruct f as [f [[H1 H2] H3]]; simpl.
  unfold isSemiGroupHom in H1.
  intros x a H4.
  repeat rewrite H1 in H4.
  apply (leftInjection g2 (f a)).
  apply (rightInjection g2 (f (invert a))).
  rewrite H4.
  rewrite (rightUnit g2).
  rewrite <- H3.
  rewrite (rightInverse g2).
  reflexivity.
Qed.

Lemma centerIsNormal(g: Group): isNormal (center g).
Proof.
  intros x a Hx y _.
  set (H := Hx (a * y * invert a) I).
  repeat rewrite (associative g) in H.
  apply (leftInjection g) in H.
  repeat rewrite <- (associative g) in H.
  apply (rightInjection g) in H.
  transitivity (x * invert a * a * y).
  f_equal.
  rewrite (associative g).
  rewrite (leftInverse g).
  rewrite (rightUnit g).
  auto.
  rewrite H.
  f_equal.
  rewrite (associative g).
  rewrite (leftInverse g).
  rewrite (rightUnit g).
  auto.
Qed.
