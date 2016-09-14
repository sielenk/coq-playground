Require Import Setoids.Setoid.


Axiom preNum: Set.

Definition set := preNum -> Prop.

Axiom L: preNum -> set.
Axiom R: preNum -> set.

Definition liftL(R: preNum -> preNum -> Prop)(l: set)(r: preNum): Prop :=
  forall ul, l ul -> R ul r.

Definition liftR(R: preNum -> preNum -> Prop)(l: preNum)(r: set): Prop :=
  forall ur, r ur -> R l ur.

Definition lift(R: preNum -> preNum -> Prop)(l: set)(r: set): Prop :=
  forall ul ur, l ul -> r ur -> R ul ur.

Axiom mkNum: set -> set -> preNum.

Axiom mkNumLR: forall n,   n = mkNum (L n) (R n).
Axiom mkNumL:  forall l r, l = L (mkNum l r).
Axiom mkNumR:  forall l r, r = R (mkNum l r).

Definition empty: set := fun _ => False.
Definition zero_      := mkNum empty empty.
Definition n_one_     := mkNum empty (eq zero_).
Definition p_one_     := mkNum (eq zero_) empty.

Axiom      le: preNum -> preNum -> Prop.
Definition ge m n :=  le n m.
Definition lt m n := ~le n m.
Definition gt m n := ~le m n.

Axiom leRec: forall m n, le m n <-> liftL lt (L m) n /\ liftR lt m (R n).

Definition isNumber n := lift lt (L n) (R n).

Definition num := sig isNumber.

Lemma zeroIsNumber: isNumber zero_.
Proof.
  intros m n H1.
  unfold zero_ in H1.
  rewrite <- mkNumL in H1.
  destruct H1.
Qed.

Lemma nOneIsNumber: isNumber n_one_.
Proof.
  intros m n H1 H2.
  unfold n_one_ in H1.
  rewrite <- mkNumL in H1.
  destruct H1.
Qed.

Lemma pOneIsNumber: isNumber p_one_.
Proof.
  intros m n H1 H2.
  unfold p_one_ in H2.
  rewrite <- mkNumR in H2.
  destruct H2.
Qed.

Lemma zeroLeZero: le zero_ zero_.
Proof.
  rewrite leRec.
  split.
  unfold liftL, lt, zero_.
  intros ul H1 H2.
  rewrite <- mkNumL in H1.
  destruct H1.
  unfold liftR, lt, zero_.
  intros ul H1 H2.
  rewrite <- mkNumR in H1.
  destruct H1.
Qed.

Lemma nOneLessThanZero: lt n_one_ zero_.
Proof.
  intros H1.
  rewrite leRec in H1.
  destruct H1 as [H1 H2].
  unfold liftR, zero_, lt, not in H2.
  apply (H2 zero_); try apply zeroLeZero.
  unfold n_one_.
  rewrite <- mkNumR.
  reflexivity.
Qed.

Definition zero: num := exist _ zero_ zeroIsNumber.

f
