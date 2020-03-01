Require Export predicate.
Require Export refl.

Inductive pnat :=
| P : nat -> pnat
.

Inductive integer :=
| PosZ : pnat -> integer
| Zero : integer
| NegZ : pnat -> integer
.

Definition int_plus (n : integer) (m : integer) :=
  match n, m with
  | Zero, _ => m
  | _, Zero => n
  | PosZ (P n'), PosZ (P m') => PosZ (P (S (n' + m')))
  | NegZ (P n'), NegZ (P m') => NegZ (P (S (n' + m')))
  | PosZ (P n'), NegZ (P m') =>
    if Nat.leb m' n' then
      match n' - m' with
      | 0 => Zero
      | S x => PosZ (P x)
      end
    else
      match m' - n' with
      | 0 => Zero
      | S x => NegZ (P x)
      end
  | NegZ (P n'), PosZ (P m') =>
    if Nat.leb m' n' then
      match n' - m' with
      | 0 => Zero
      | S x => NegZ (P x)
      end
    else
      match m' - n' with
      | 0 => Zero
      | S x => PosZ (P x)
      end
  end
.

Notation "x +- y" := (int_plus x y) (at level 50, left associativity).

Lemma int_plus_comm : forall x y, x +- y = y +- x.
Proof.
  intros. destruct x; destruct y; try destruct p; try destruct p0;
  simpl; refl; repeat match goal with
  | |- PosZ ?x = PosZ ?y => replace x with y; refl
  | |- NegZ ?x = NegZ ?y => replace x with y; refl
  | |- P ?x = P ?y => replace x with y; refl
  | |- S ?x = S ?y => replace x with y; refl
  end; try nia; repeat match goal with
  | [ |- context [ if ?x then _ else _ ] ] =>
    destruct x eqn: ?; reflection
  end; repeat match goal with
  | [ |- context [ match ?x with 0 => _ | S _ => _ end ] ] =>
    destruct x eqn: ?
  end; refl; nia.
Qed.

Lemma int_plus_assoc : forall x y z, x +- (y +- z) = x +- y +- z.
Proof.
  intros.
  destruct x as [[a] | | [a]]; destruct y as [[b] | | [b]];
  destruct z as [[c] | | [c]]; simpl; refl; try nia;
  repeat match goal with
  | [ |- context [ if ?x then _ else _ ] ] =>
    destruct x eqn: ?
  | [ |- context [ match ?x with 0 => _ | S _ => _ end ] ] =>
    destruct x eqn: ?
  | [ H : context [ if ?x then _ else _ ] |- _ ] =>
    destruct x eqn: ?
  | [ H : context [ match ?x with 0 => _ | S _ => _ end ] |- _ ] =>
    destruct x eqn: ?
  end; reflection; refl; simpl; repeat match goal with
  | |- PosZ ?x = PosZ ?y => replace x with y; refl
  | |- NegZ ?x = NegZ ?y => replace x with y; refl
  | |- P ?x = P ?y => replace x with y; refl
  | |- S ?x = S ?y => replace x with y; refl
  end; try nia; repeat match goal with
  | [ |- context [ if ?x then _ else _ ] ] =>
    destruct x eqn: ?
  | [ |- context [ match ?x with 0 => _ | S _ => _ end ] ] =>
    destruct x eqn: ?
  | [ H : context [ if ?x then _ else _ ] |- _ ] =>
    destruct x eqn: ?
  | [ H : context [ match ?x with 0 => _ | S _ => _ end ] |- _ ] =>
    destruct x eqn: ?
  end; refl; repeat match goal with
  | |- PosZ ?x = PosZ ?y => replace x with y; refl
  | |- NegZ ?x = NegZ ?y => replace x with y; refl
  | |- P ?x = P ?y => replace x with y; refl
  | |- S ?x = S ?y => replace x with y; refl
  end; repeat match goal with
  | H : ?x <= ?y, H0 : ?y <= ?x |- _ =>
    eassert (x = y) by nia; subst y; clear H H0
  end; reflection; try nia; match goal with
  | H : false = true |- _ => inv H
  end.
Qed.

Definition int_mul (n : integer) (m : integer) :=
  match n, m with
  | Zero, _ => Zero
  | _, Zero => Zero
  | PosZ (P n'), PosZ (P m')
  | NegZ (P n'), NegZ (P m') => match (S n' * S m') with
    | 0 => Zero
    | S x => PosZ (P x)
    end
  | PosZ (P n'), NegZ (P m')
  | NegZ (P n'), PosZ (P m') => match (S n' * S m') with
    | 0 => Zero
    | S x => NegZ (P x)
    end
  end
.

Notation "x *- y" := (int_mul x y) (at level 40, left associativity).

Lemma int_mul_comm : forall x y, x *- y = y *- x.
Proof.
  intros. destruct x as [[a] | | [a]]; destruct y as [[b] | | [b]];
  try (simpl; refl; fail); unfold int_mul; repeat match goal with
  | [ |- context [ match ?x with 0 => _ | S _ => _ end ] ] =>
    destruct x eqn: ?
  end; try (
    simpl in *; match goal with
    | H : S _ = 0 |- _ => inv H
    | H : 0 = S _ |- _ => inv H
    end; fail
  ); repeat match goal with
  | |- PosZ ?x = PosZ ?y => replace x with y; refl
  | |- NegZ ?x = NegZ ?y => replace x with y; refl
  | |- P ?x = P ?y => replace x with y; refl
  | |- S ?x = S ?y => replace x with y; refl
  end; nia.
Qed.

Lemma int_mul_assoc : forall x y z, x *- (y *- z) = x *- y *- z.
Proof.
  intros.
  destruct x as [[a] | | [a]]; destruct y as [[b] | | [b]];
  destruct z as [[c] | | [c]]; try (simpl; refl; fail); unfold int_mul;
  repeat match goal with
  | [ |- context [ match ?x with 0 => _ | S _ => _ end ] ] =>
    destruct x eqn: ?
  end; try (
    simpl in *; match goal with
    | H : S _ = 0 |- _ => inv H
    | H : 0 = S _ |- _ => inv H
    end; fail
  ); repeat match goal with
  | |- PosZ ?x = PosZ ?y => replace x with y; refl
  | |- NegZ ?x = NegZ ?y => replace x with y; refl
  | |- P ?x = P ?y => replace x with y; refl
  | |- S ?x = S ?y => replace x with y; refl
  end; eassert (D : forall x y, S x = S y -> x = y) by (clear; intros; nia);
  apply D; clear D; repeat match goal with
  | [ |- context [S ?x] ] => remember (S x); match goal with
    | H : _ = S x |- _ => clear H
    end
  | [ H : context [S ?x] |- _ ] => remember (S x); match goal with
    | H : _ = S x |- _ => clear H
    end
  end; subst; clear; nia.
Qed.

Lemma int_dist_front : forall x y z, x *- (y +- z) = x *- y +- x *- z.
Proof.
  intros.
  destruct x as [[a] | | [a]]; destruct y as [[b] | | [b]];
  destruct z as [[c] | | [c]]; try (simpl; refl; fail); unfold int_mul;
  unfold int_plus; repeat match goal with
  | [ |- context [ match ?x with 0 => _ | S _ => _ end ] ] =>
    destruct x eqn: ?
  | [ |- context [ if ?x then _ else _ ] ] =>
    destruct x eqn: ?
  | [ H : context [ if ?x then _ else _ ] |- _ ] =>
    destruct x eqn: ?
  end; try (
    simpl in *; match goal with
    | H : S _ = 0 |- _ => inv H
    | H : 0 = S _ |- _ => inv H
    end; fail
  ); refl; reflection; repeat match goal with
  | |- PosZ ?x = PosZ ?y => replace x with y; refl
  | |- NegZ ?x = NegZ ?y => replace x with y; refl
  | |- P ?x = P ?y => replace x with y; refl
  | |- S ?x = S ?y => replace x with y; refl
  end; try nia.
Qed.

Lemma int_dist_back : forall x y z, (x +- y) *- z = x *- z +- y *- z.
Proof.
  intros. repeat rewrite (int_mul_comm _ z). apply int_dist_front.
Qed.

Definition int_plus_inv (n : integer) :=
  match n with
  | PosZ x => NegZ x
  | Zero => Zero
  | NegZ x => PosZ x
  end
.

Notation "-- x" := (int_plus_inv x) (at level 30, right associativity).

Lemma int_mul_div : forall n m k, k <> Zero -> n *- k = m *- k -> n = m.
Proof.
  intros; try (subst; eauto; fail).
  destruct k; try (destruct (H (@eq_refl integer Zero)); fail); clear H;
  destruct n as [[n] | | [n]]; destruct m as [[m] | | [m]];
  unfold int_mul in *; repeat match goal with
  | [ H : context [ match ?x with P _ => _ end ] |- _ ] => destruct x eqn: ?
  | [ H : context [ match ?x with 0 => _ | S _ => _ end ] |- _ ] =>
    destruct x eqn: ?
  end;
  try (
    simpl in *;
    match goal with
    | H : S _ = 0 |- _ => inv H
    | H : PosZ _ = Zero |- _ => inv H
    | H : PosZ _ = NegZ _ |- _ => inv H
    | H : Zero = PosZ _ |- _ => inv H
    | H : Zero = NegZ _ |- _ => inv H
    | H : NegZ _ = PosZ _ |- _ => inv H
    | H : NegZ _ = Zero |- _ => inv H
    end; fail
  ); trivial; repeat match goal with
  | |- PosZ ?x = PosZ ?y => replace x with y; refl
  | |- NegZ ?x = NegZ ?y => replace x with y; refl
  | |- P ?x = P ?y => replace x with y; refl
  | |- S ?x = S ?y => replace x with y; refl
  end; inv H0; nia.
Qed.
