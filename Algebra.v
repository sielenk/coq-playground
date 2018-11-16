(*
 * Abstract Algebra
 *
 * (c) 2018, Marvin H. Sielenkemper
 *)

Require Import ProofIrrelevance.
Require Import EqdepFacts.
Require Import PeanoNat.
Require Import RelationClasses.
Require Import Morphisms.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require List.

Delimit Scope group_scope with group.
Local Open Scope group_scope.


Record SemiGroupSig := makeSemiGroupSig {
  carrier:> Set;
  op: carrier -> carrier -> carrier
}.

Arguments makeSemiGroupSig {carrier}.
Arguments op {s}.

Notation "x * y" := (op x y) : group_scope.

Record SemiGroupAx(sig: SemiGroupSig) := {
  associative: forall x y z: sig, (x * y) * z = x * (y * z);
}.

Arguments associative {sig}.

Record SemiGroup := {
  semiGroupSig:> SemiGroupSig;
  semiGroupAx :> SemiGroupAx semiGroupSig
}.



Record SemiGroupHom(h1 h2: SemiGroupSig) := makeSemiGroupHom {
  semiGroupHomFun:> h1 -> h2;
  isSemiGroupHom: forall x1 x2, semiGroupHomFun (x1 * x2) = semiGroupHomFun x1 * semiGroupHomFun x2
}.

Arguments isSemiGroupHom {h1 h2}.


Definition abelian(h: SemiGroupSig) := forall a b: h, a * b = b * a.


(***************************************************************)


Record MonoidSig := {
  monoidSigIsSemiGroup:> SemiGroupSig;
  unit: monoidSigIsSemiGroup;
}.

Arguments unit {m}.

Definition makeMonoidSig{X: Set}(op: X -> X -> X)(unit: X): MonoidSig :=
  Build_MonoidSig (makeSemiGroupSig op) unit.

Record MonoidAx(sig: MonoidSig) := {
  monoidIsSemiGroupAx:> SemiGroupAx sig;
  leftUnit:  forall x: sig, unit * x = x;
  rightUnit: forall x: sig, x * unit = x
}.

Arguments leftUnit {sig}.
Arguments rightUnit {sig}.

Record Monoid := {
  monoidSig:> MonoidSig;
  monoidAx :> MonoidAx monoidSig
}.


Record MonoidHom(m1 m2: MonoidSig) := {
  monoidHomIsSemiGroupHom:> SemiGroupHom m1 m2;
  isMonoidHom: monoidHomIsSemiGroupHom unit = unit
}.

Arguments isMonoidHom {m1 m2}.

Definition makeMonoidHom{m1 m2: MonoidSig}(f: m1 -> m2):
    (forall x1 x2, f (x1 * x2) = f x1 * f x2) ->
    f unit = unit ->
    MonoidHom m1 m2 :=
  fun H1 => Build_MonoidHom m1 m2 (makeSemiGroupHom m1 m2 f H1).


Lemma unitUnique(m: Monoid): forall e: m, (forall x, x * e = x) -> e = unit.
Proof.
  intros e H.
  rewrite <- (leftUnit m e).
  apply H.
Qed.


(***************************************************************)


Record GroupSig := {
  groupSigIsMonoidSig:> MonoidSig;
  invert: groupSigIsMonoidSig -> groupSigIsMonoidSig
}.

Arguments invert {g}.

Definition makeGroupSig{X: Set}(op: X -> X -> X)(unit: X)(invert: X -> X): GroupSig :=
  Build_GroupSig (makeMonoidSig op unit) invert.

Record GroupAx(sig: GroupSig) := {
  groupIsMonoidAx:> MonoidAx sig;
  leftInverse:  forall x: sig, invert x * x = unit;
  rightInverse: forall x: sig, x * invert x = unit
}.

Arguments leftInverse {sig}.
Arguments rightInverse {sig}.

Record Group := {
  groupSig:> GroupSig;
  groupAx :> GroupAx groupSig
}.


Record GroupHom(g1 g2: GroupSig) := {
  groupHomIsMonoidHom:> MonoidHom g1 g2;
  isGroupHom: forall x, invert (groupHomIsMonoidHom x) = groupHomIsMonoidHom (invert x)
}.

Arguments isGroupHom {g1 g2}.

Definition makeGroupHom{g1 g2: GroupSig}(f: g1 -> g2):
    (forall x1 x2, f (x1 * x2) = f x1 * f x2) ->
    f unit = unit ->
    (forall x, invert (f x) = f (invert x)) ->
    GroupHom g1 g2 :=
  fun H1 H2 => Build_GroupHom g1 g2 (makeMonoidHom f H1 H2).


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
  exists (makeGroupSig op e inv).
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


Definition makeGroupHom2(g1 g2: Group)(f: g1 -> g2): (forall x1 x2, f (x1 * x2) = f x1 * f x2) -> GroupHom g1 g2.
  intro H1.
  assert (H2: f unit = unit).
  apply (unitUnique2 _ (f unit)).
  rewrite <- H1. f_equal. apply (rightUnit g1).
  refine (makeGroupHom f H1 H2 _).
  intro x.
  symmetry. apply inverseUnique.
  rewrite <- H1.
  rewrite (rightInverse g1).
  assumption.
Defined.

Definition groupHomId{g: Group}: GroupHom g g := makeGroupHom2 g g (fun a => a) (fun x y => eq_refl).

Definition groupHomComp{g1 g2 g3: Group}: GroupHom g2 g3 -> GroupHom g1 g2 -> GroupHom g1 g3.
  intros g f.
  apply (makeGroupHom2 _ _ (fun a => g (f a))).
  intros x y.
  rewrite (isSemiGroupHom f).
  rewrite (isSemiGroupHom g).
  reflexivity.
Defined.


Lemma groupAxFromHom{g1: GroupSig}{g2: Group}(f: GroupHom g1 g2): (forall x y, f x = f y -> x = y) -> GroupAx g1.
Proof.
  intro H1.
  set (H2 := isMonoidHom f).
  apply makeGroupAx; intros; apply H1; repeat rewrite (isSemiGroupHom f); try rewrite H2.
  apply (associative g2).
  apply (leftUnit g2).
  rewrite <- (isGroupHom f). apply (leftInverse g2).
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
  set (k := subGroupSig h).
  apply (makeGroupHom (g1:=k) (g2:=g) (@proj1_sig _ _)); simpl.
  intros [x Hx] [y Hy]; simpl.
  reflexivity.
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

Definition subGroup{g: Group}(h: SubGroup g): Group := Build_Group _ (subGroupAx h).
Coercion   subGroup: SubGroup >-> Group.


Definition subSubGroup_1{g: Group}(h: SubGroup g)(k: SubGroup h): SubGroup g.
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

Definition subSubGroup_2{g: Group}(h k: SubGroup g): (forall a, isIn h a -> isIn k a) -> SubGroup k.
  destruct h as [P H1 H2]. simpl.
  intro H3.
  refine (makeSubGroup k (fun x => P (subGroupExtract k x)) _ _).
  destruct H1 as [a Pa]. exists (subGroupInsert k _ (H3 _ Pa)).
  rewrite subGroupInOut. assumption.
  intros [a Pa] [b Pb]. apply H2.
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
  set (H1 := isSemiGroupHom f).
  set (H2 := isMonoidHom f).
  set (H3 := isGroupHom f).
  refine (makeSubGroup g1 (fun x => f x = unit) (ex_intro _ unit H2) (fun a b H4 H5 => _)).
  simpl in H4, H5.
  rewrite H1, H4.
  rewrite <- H3.
  rewrite H5.
  rewrite inverseUnit.
  apply (rightUnit g2).
Defined.

Definition image{g1 g2: Group}(f: GroupHom g1 g2): SubGroup g2.
  refine (makeSubGroup g2 (fun x => ex (fun y => f y = x)) (ex_intro _ _ (ex_intro _ _ (isMonoidHom f))) (fun a b => _)).
  intros [a' Ha] [b' Hb].
  exists (a' * invert b').
  rewrite (isSemiGroupHom f). rewrite <- (isGroupHom f), Ha, Hb.
  reflexivity.
Defined.


Definition konjugate{g: Group}(a x: g): g := a * x * invert a.

Lemma konjugate_1{g: Group}(a x: g): konjugate a x = x <-> a * x = x * a.
Proof.
  unfold konjugate.
  split; intro H; [
    apply (rightInjection g (invert a)); rewrite H |
    apply (rightInjection g a); rewrite H; f_equal
  ];
  rewrite (associative g); rewrite (rightInverse g); rewrite (rightUnit g); reflexivity.
Qed.

Lemma konjugateUnit1{g: Group}(a: g): konjugate unit a = a.
Proof.
  unfold konjugate.
  rewrite (inverseUnit g).
  rewrite (rightUnit g).
  apply (leftUnit g).
Qed.

Lemma konjugateUnit2{g: Group}(a: g): konjugate a unit = unit.
Proof.
  unfold konjugate.
  rewrite (rightUnit g).
  rewrite (rightInverse g).
  reflexivity.
Qed.

Lemma konjugateOp1{g: Group}(a b x: g): konjugate a (konjugate b x) = konjugate (a * b) x.
Proof.
  unfold konjugate.
  rewrite (inverseOp g).
  repeat rewrite <- (associative g).
  reflexivity.
Qed.

Lemma konjugateOp2{g: Group}(a x y: g): konjugate a x * konjugate a y = konjugate a (x * y).
Proof.
  unfold konjugate.
  transitivity (a * x * (invert a * a) * y * invert a).
  repeat rewrite <- (associative g).
  reflexivity.
  rewrite (leftInverse g).
  rewrite (rightUnit g).
  repeat rewrite <- (associative g).
  reflexivity.
Qed.

Lemma konjugateInvert{g: Group}(a x: g): konjugate a (invert x) = invert (konjugate a x).
Proof.
  unfold konjugate.
  repeat rewrite (inverseOp g).
  rewrite (inverseId g).
  apply (associative g).
Qed.

Lemma konjugateInjective{g: Group}(a x y: g): konjugate a x = konjugate a y -> x = y.
Proof.
  unfold konjugate.
  intro H.
  apply (leftInjection g a).
  apply (rightInjection g (invert a)).
  apply H.
Qed.


Definition centralizer(g: Group)(P: g -> Prop): SubGroup g.
  refine (makeSubGroup g (fun a => forall x, P x -> konjugate a x = x) (ex_intro _ unit _) (fun a b => _)).
  intros x H.
  apply konjugateUnit1.
  intros H1 H2 x Hx.
  rewrite <- konjugateOp1.
  rewrite <- H1; try assumption.
  f_equal. clear H1 a.
  rewrite <- (H2 x Hx) at 1.
  rewrite konjugateOp1.
  rewrite (leftInverse g).
  apply konjugateUnit1.
Defined.

Lemma centralizer_1{g: Group}(P: g -> Prop):
  forall(a: centralizer g P) x, P x -> konjugate (subGroupExtract _ a) x = x.
Proof.
  intros [a Pa]. apply Pa.
Qed.

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
  apply subGroupEmbedding; simpl.
  rewrite <- konjugate_1.
  rewrite Ha; auto.
Qed.


Definition normalizer{g: Group}(h: SubGroup g): SubGroup g.
  refine (makeSubGroup g (fun a => forall x, isIn h x <-> isIn h (konjugate a x)) (ex_intro _ unit _) (fun a b => _)).
  intro x.
  rewrite konjugateUnit1.
  reflexivity.
  intros H1 H2 x.
  rewrite <- konjugateOp1.
  rewrite <- H1.
  clear H1 a.
  rewrite (H2 (konjugate (invert b) x)).
  rewrite konjugateOp1.
  rewrite (rightInverse g).
  rewrite konjugateUnit1.
  reflexivity.
Defined.

Lemma normalizer_1{g: Group}(h: SubGroup g): forall a x, isIn (normalizer h) a -> isIn h x <-> isIn h (konjugate a x).
Proof.
  simpl.
  intros a x H. apply H.
Qed.

Lemma normalizer_2{g: Group}(h: SubGroup g): forall a, isIn h a -> isIn (normalizer h) a.
Proof.
  simpl.
  intros a Ha x.
  split; intro Hx.
  repeat apply (opIsIn h); try apply (invertIsIn h); assumption.
  rewrite <- konjugateUnit1.
  rewrite <- (rightInverse g (invert a)).
  rewrite inverseId.
  rewrite <- konjugateOp1.
  apply opIsIn.
  apply opIsIn; try assumption.
  apply invertIsIn; assumption.
  repeat apply invertIsIn; assumption.
Qed.


Definition generatedSubGroup{g: Group}(P: g -> Prop): SubGroup g.
  refine (subGroupCut { h: SubGroup g | forall a: g, P a -> isIn h a } (@proj1_sig _ _)).
Defined.

Definition generatedSubGroup_2{g: Group}(P: g -> Prop): SubGroup g.
  set (reduce_1 (tx: bool * sig P) := match tx with (t, (exist _ x _)) => if t then invert x else x end).
  set (reduce_2 := List.fold_right (fun tx y => reduce_1 tx * y) unit).

  assert (H1: forall xs ys, reduce_2 (app xs ys) = reduce_2 xs * reduce_2 ys).
  intro xs.
  induction xs as [ | [t [x Hx]]]; intro ys.
  rewrite (leftUnit g). reflexivity.
  simpl. rewrite IHxs.
  symmetry; apply (associative g).

  set (invert_1 (tx: bool * sig P) := let (t, x) := tx in (negb t, x)).
  set (invert_2 txs := List.rev (List.map invert_1 txs)).

  assert (H2: forall xs, reduce_2 (invert_2 xs) = invert (reduce_2 xs)).
  intro xs.
  unfold reduce_2 at 1, invert_2.
  rewrite List.fold_left_rev_right.
  induction xs as [ | [t [x Hx]]].
  symmetry. apply (inverseUnit g).
  simpl. rewrite (inverseOp g).
  set (x' := invert (if t then invert x else x)).
  assert (x' = if negb t then invert x else x).
  destruct t; auto; apply inverseId. destruct H.
  generalize dependent x'. clear Hx x t. intro y.
  rewrite <- IHxs. clear IHxs.
  rewrite (rightUnit g).
  generalize (List.map invert_1 xs). clear xs.
  intros [ | x xs]; simpl.
  symmetry; apply (leftUnit g).
  rewrite (rightUnit g).
  generalize (reduce_1 x) as x'. clear x. intro x.
  generalize dependent y.
  generalize dependent x.
  induction xs as [ | x' xs]; auto.
  simpl. generalize (reduce_1 x') as w. clear x'.
  intros x y z.
  rewrite <- IHxs.
  rewrite <- (associative g).
  reflexivity.

  set (P' a := exists xs, reduce_2 xs = a).

  apply (makeSubGroup g P').

  exists unit.
  exists nil.
  reflexivity.

  intros a b [xas Hxa] [xbs Hxb].
  exists (xas ++ (invert_2 xbs))%list.
  rewrite H1, H2, Hxa, Hxb.
  reflexivity.
Defined.

Lemma generatedSubGroupEquiv{g: Group}(P: g -> Prop): forall a: g, isIn (generatedSubGroup P) a <-> isIn (generatedSubGroup_2 P) a.
Proof.
  intro a.
  split.

  intro H.
  simpl in H.
  refine (H (exist _ (generatedSubGroup_2 P) _)).
  intros x Hx.
  exists (cons (false, exist _ x Hx) nil).
  apply (rightUnit g).

  intros [txs H] [h Hh].
  simpl. destruct H.
  induction txs as [ | tx].
  apply (unitIsIn h).
  simpl.
  apply (opIsIn h); try assumption.
  destruct tx as [[ | ] [x Hx]]; try apply (invertIsIn h); auto.
Qed.


Definition konjugated{g: Group}(x y: g): Prop :=
  ex (fun a => x = konjugate a y).

Lemma konjugatedReflexive{g: Group}: Reflexive (konjugated (g:=g)).
Proof.
  exists unit.
  rewrite konjugateUnit1.
  reflexivity.
Qed.

Lemma konjugatedSymmetric{g: Group}: Symmetric (konjugated (g:=g)).
Proof.
  intros x y [a H].
  exists (invert a).
  rewrite H.
  rewrite konjugateOp1.
  rewrite (leftInverse g).
  rewrite konjugateUnit1.
  reflexivity.
Qed.

Lemma konjugatedTransitive{g: Group}: Transitive (konjugated (g:=g)).
Proof.
  intros x y z [a Ha] [b Hb].
  exists (a * b).
  rewrite Ha, Hb.
  apply konjugateOp1.
Qed.

Instance konjugatedEquiv{g: Group}: Equivalence (konjugated (g:=g)).
Proof.
  split; [apply konjugatedReflexive | apply konjugatedSymmetric | apply konjugatedTransitive].
Qed.


Definition innerAutomorphism{g: Group}(a: g): GroupHom g g.
  apply (makeGroupHom2 _ _ (konjugate a)).
  intros x y.
  rewrite konjugateOp2.
  reflexivity.
Defined.


Definition isNormal{g: Group}(h: SubGroup g): Prop :=
  let (P, _, _) := h in forall x a, P (konjugate a x) -> P x.

Lemma normal_1{g: Group}(h: SubGroup g): isNormal h -> forall x a, isIn h (konjugate a x) <-> isIn h x.
Proof.
  intro H1.
  assert (H2: forall x a, isIn h (konjugate a x) -> isIn h x).
  destruct h as [P H3 H4].
  apply H1.
  split; try apply H2.
  intro H3.
  apply (H2 _ (invert a)).
  rewrite konjugateOp1.
  rewrite (leftInverse g).
  rewrite konjugateUnit1.
  assumption.
Qed.


Lemma minimalIsNormal(g: Group): isNormal (minimalSubGroup g).
Proof.
  intros x a H.
  rewrite <- (konjugateUnit2 a) in H.
  apply (konjugateInjective _ _ _ H).
Qed.

Lemma maximalIsNormal(g: Group): isNormal (maximalSubGroup g).
Proof.
  intros x a H.
  auto.
Qed.

Lemma kernIsNormal{g1 g2: Group}(f: GroupHom g1 g2): isNormal (kern f).
Proof.
  set (H1 := isSemiGroupHom f).
  set (H3 := isGroupHom f).
  intros x a H4.
  unfold konjugate in H4.
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
  set (H := Hx (konjugate a y) I).
  unfold konjugate in H.
  repeat rewrite (associative g) in H.  clear Hx.
  apply (leftInjection g) in H.
  repeat rewrite inverseOp in H.
  repeat rewrite <- (associative g) in H.
  apply (rightInjection g) in H.
  rewrite <- H at 2. clear H.
  unfold konjugate.
  f_equal.
  repeat rewrite (associative g).
  f_equal.
  rewrite (rightInverse g).
  rewrite (rightUnit g).
  rewrite <- (associative g).
  rewrite (leftInverse g).
  rewrite (leftUnit g).
  reflexivity.
Qed.

Lemma isNormalInNormalizer(g: Group)(h: SubGroup g): isNormal (subSubGroup_2 h (normalizer h) (normalizer_2 h)).
Proof.
  destruct h as [P H1 H2]. simpl.
  intros [x Hx] [a Ha]. simpl.
  apply Ha.
Qed.


Definition injective {A B}(f: A -> B) := forall a1 a2, f a1 = f a2 -> a1 = a2.
Definition surjective{A B}(f: A -> B) := forall a, exists x, f x = a.
Definition bijective {A B}(f: A -> B) := injective f /\ surjective f.

Inductive bij(A B: Type) := makeBij (u: A -> B)(v: B -> A): injective u -> (forall a, u (v a) = a) -> bij A B.

Definition bij2Fun{A B}(f: bij A B): A -> B := let (f', _, _, _) := f in f'.
Coercion   bij2Fun: bij >-> Funclass.

Definition bijComp{A B C}(g: bij B C)(f: bij A B): bij A C.
  refine (match g, f with
          | makeBij _ _ g g' H1 H2, makeBij _ _ f f' H3 H4 =>
              makeBij _ _ (fun a => g (f a)) (fun b => f' (g' b)) _ _
          end).
  intros a1 a2 H5.
  apply H3.
  apply H1.
  apply H5.
  intro c.
  rewrite H4.
  apply H2.
Defined.

Definition bijInvert{A B}(f: bij A B): bij B A.
  refine (match f with makeBij _ _ u v H1 H2 => makeBij _ _ v u _ _ end).
  intros b1 b2 H3.
  rewrite <- (H2 b1).
  rewrite <- (H2 b2).
  rewrite H3.
  reflexivity.
  intros a.
  apply H1.
  apply H2.
Defined.


Inductive aut(g: Group) := makeAut (u: GroupHom g g)(v: GroupHom g g): injective u -> (forall a, u (v a) = a) -> aut g.

Definition aut2hom{g}(f: aut g): GroupHom g g := let (f', _, _, _) := f in f'.
Coercion   aut2hom: aut >-> GroupHom.

Definition autId{g}: aut g.
  refine (makeAut _ groupHomId groupHomId _ _).
  intros b1 b2 H3. apply H3.
  intros a. reflexivity.
Defined.

Definition autComp{g}(f1 f2: aut g): aut g.
  refine (match f1, f2 with
          | makeAut _ f1 f1' H1 H2, makeAut _ f2 f2' H3 H4 =>
              makeAut _ (groupHomComp f1 f2) (groupHomComp f2' f1') _ _
          end).
  intros a1 a2 H5.
  apply H3.
  apply H1.
  apply H5. simpl.
  intro c.
  rewrite H4.
  apply H2.
Defined.

Definition autInvert{g}(f: aut g): aut g.
  refine (match f with makeAut _ f f' H1 H2 => makeAut _ f' f _ _ end).
  intros b1 b2 H3.
  rewrite <- (H2 b1).
  rewrite <- (H2 b2).
  rewrite H3.
  reflexivity.
  intros a.
  apply H1.
  apply H2.
Defined.

Definition autEq{g}(f1 f2: aut g): (forall x, f1 x = f2 x) -> f1 = f2.
  destruct f1 as [[[[f1 H1] H2] H3] [[[f1' H4] H5] H6] H7 H8].
  destruct f2 as [[[[f2 H9] Ha] Hb] [[[f2' Hc] Hd] He] Hf Hg].
  simpl in * |- *.
  intro Hh.
  assert (Hi: f1 = f2).
  apply (functional_extensionality f1 f2 Hh).
  assert (Hj: f1' = f2').
  apply (functional_extensionality f1' f2').
  intro x.
  apply Hf.
  rewrite Hg.
  rewrite <- Hi.
  apply H8.
  subst.
  rewrite (proof_irrelevance _ H1 H9).
  rewrite (proof_irrelevance _ H2 Ha).
  rewrite (proof_irrelevance _ H3 Hb).
  rewrite (proof_irrelevance _ H4 Hc).
  rewrite (proof_irrelevance _ H5 Hd).
  rewrite (proof_irrelevance _ H6 He).
  rewrite (proof_irrelevance _ H7 Hf).
  rewrite (proof_irrelevance _ H8 Hg).
  reflexivity.
Defined.


Definition AutSig(g: Group): GroupSig := makeGroupSig (X := aut g) autComp autId autInvert.

Definition Aut(g: Group): Group.
  exists (AutSig g).
  apply makeGroupAx; intros; apply autEq; simpl.
  destruct x, y, z; reflexivity.
  destruct x; reflexivity.
  destruct x.
  intro a. simpl.
  apply i.
  rewrite e.
  reflexivity.
Defined.


Definition foo(g: Group): GroupHom g (Aut g).
  refine (makeGroupHom2 g (Aut g)
    (fun a => makeAut g (innerAutomorphism a)
                        (innerAutomorphism (invert a))
                        (fun b1 b2 => _)
                        (fun b => _))
    (fun a1 a2 => _)).
  apply autEq.
  simpl.
  intro a3. symmetry. apply konjugateOp1.
  Unshelve.
  simpl.
  apply konjugateInjective.
  simpl.
  rewrite konjugateOp1.
  rewrite (rightInverse g).
  apply konjugateUnit1.
Defined.


Definition natMonoid: Monoid.
  exists (Build_MonoidSig (makeSemiGroupSig plus) 0).
  repeat split; simpl.
  symmetry. apply Nat.add_assoc.
  apply Nat.add_0_r.
Defined.
