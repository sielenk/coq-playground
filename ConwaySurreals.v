Require Import Setoids.Setoid.

Axiom U: Set.

Definition set := U -> Prop.

Record preNum := mkPreNum {
  L : set;
  R : set
}.

Axiom embed: preNum -> U.
Axiom embedInjective: forall n1 n2, embed n1 = embed n2 -> n1 = n2.


Definition liftL(R: preNum -> preNum -> Prop)(l: set)(r: preNum): Prop :=
  forall ul, l (embed ul) -> R ul r.

Definition liftR(R: preNum -> preNum -> Prop)(l: preNum)(r: set): Prop :=
  forall ur, r (embed ur) -> R l ur.

Definition lift(R: preNum -> preNum -> Prop)(l: set)(r: set): Prop :=
  forall ul ur, l (embed ul) -> r (embed ur) -> R ul ur.

Definition empty: set := fun _ => False.
Definition zero_      := mkPreNum empty empty.
Definition n_one_     := mkPreNum empty (eq (embed zero_)).
Definition p_one_     := mkPreNum (eq (embed zero_)) empty.

Axiom      le: preNum -> preNum -> Prop.
Definition ge m n :=  le n m.
Definition lt m n := ~le n m.
Definition gt m n := ~le m n.

Definition like m n := le m n /\ le n m.

Axiom leRec: forall m n, le m n <-> liftL lt (L m) n /\ liftR lt m (R n).

Definition isNumber n := lift lt (L n) (R n).

Definition num := sig isNumber.

Lemma zeroIsNumber: isNumber zero_.
Proof.
  intros m n [].
Qed.

Lemma nOneIsNumber: isNumber n_one_.
Proof.
  intros m n [].
Qed.

Lemma pOneIsNumber: isNumber p_one_.
Proof.
  intros m n H1 [].
Qed.

Lemma zeroLeZero: le zero_ zero_.
Proof.
  rewrite leRec.
  split; intros _ [].
Qed.

Lemma nOneLtZero: lt n_one_ zero_.
Proof.
  intros H1.
  rewrite leRec in H1.
  destruct H1 as [H1 H2].
  apply (H2 zero_); try apply zeroLeZero.
  reflexivity.
Qed.

Lemma pOneGtZero: gt p_one_ zero_.
Proof.
  intros H1.
  rewrite leRec in H1.
  destruct H1 as [H1 H2].
  apply (H1 zero_); try apply zeroLeZero.
  reflexivity.
Qed.

Lemma nOneLenOne: le n_one_ n_one_.
Proof.
  rewrite leRec.
  split.
  intros _ [].
  intros x H1 H2. simpl in H1.
  apply embedInjective in H1.
  destruct H1.
  apply nOneLtZero.
  assumption.
Qed.

Definition zero: num := exist _ zero_  zeroIsNumber.
Definition nOne: num := exist _ n_one_ nOneIsNumber.
Definition pOne: num := exist _ p_one_ pOneIsNumber.
