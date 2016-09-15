Require Import Setoids.Setoid.

Axiom U: Set.

Definition set := U -> Prop.

Record preNum := mkPreNum {
  L : set;
  R : set
}.

Axiom embed: preNum -> U.
Axiom embedInjective: forall n1 n2, embed n1 = embed n2 -> n1 = n2.


Definition liftLa(R: preNum -> preNum -> Prop)(l: set)(r: preNum): Prop :=
  forall ul, l (embed ul) -> R ul r.

Definition liftLe(R: preNum -> preNum -> Prop)(l: set)(r: preNum): Prop :=
  exists ul, l (embed ul) -> R ul r.

Definition liftRa(R: preNum -> preNum -> Prop)(l: preNum)(r: set): Prop :=
  forall ur, r (embed ur) -> R l ur.

Definition liftRe(R: preNum -> preNum -> Prop)(l: preNum)(r: set): Prop :=
  exists ur, r (embed ur) -> R l ur.

Definition lift(R: preNum -> preNum -> Prop)(l: set)(r: set): Prop :=
  forall ul ur, l (embed ul) -> r (embed ur) -> R ul ur.

Definition empty: set := fun _ => False.
Definition zero_      := mkPreNum empty empty.
Definition n_one_     := mkPreNum empty (eq (embed zero_)).
Definition p_one_     := mkPreNum (eq (embed zero_)) empty.

Inductive le m n : Prop := Le: liftLa lt (L m) n /\ liftRa lt m (R n) -> le m n
with      lt m n : Prop := Lt: liftLe le (L m) n \/ liftRe le m (R n) -> lt m n.

Definition ge m n := le n m.
Definition gt m n := lt n m.

Definition like m n := le m n /\ le n m.

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
  apply Le; split; intros _ [].
Qed.

Lemma nOneLeZero: le n_one_ zero_.
Proof.
  apply Le; split; intros n [].
Qed.

Lemma nOneLtZero: lt n_one_ zero_.
Proof.
  apply Lt.
  left.
  exists zero_.
  intros _.
  apply zeroLeZero.
Qed.

Lemma pOneGeZero: ge p_one_ zero_.
Proof.
  apply Le; split; intros n [].
Qed.

Lemma pOneGtZero: gt p_one_ zero_.
Proof.
  apply Lt.
  left.
  exists zero_.
  intros _.
  apply pOneGeZero.
Qed.

Lemma nOneLenOne: le n_one_ n_one_.
Proof.
  apply Le; split; intros n H.
  destruct H.
  apply embedInjective in H.
  destruct H.
  apply nOneLtZero.
Qed.

Definition zero: num := exist _ zero_  zeroIsNumber.
Definition nOne: num := exist _ n_one_ nOneIsNumber.
Definition pOne: num := exist _ p_one_ pOneIsNumber.
