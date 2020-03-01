Require Export integer.

Inductive rational :=
| Rational : integer -> pnat -> rational
.

Definition rational_eq (p : rational) (q : rational) : Prop :=
  match p, q with
  | Rational a b, Rational c d => a *- PosZ d = c *- PosZ b
  end
.

Notation "x =/ y" := (rational_eq x y) (at level 70, no associativity).

Lemma rational_eq_refl : forall x, x =/ x.
Proof.
  intros. destruct x as [a b]. unfold rational_eq. refl.
Qed.

Lemma rational_eq_symm : forall x y, x =/ y -> y =/ x.
Proof.
  intros. destruct x as [a b]; destruct y as [c d]. unfold rational_eq in *.
  congruence.
Qed.

Lemma rational_eq_trans : forall x y z, x =/ y -> y =/ z -> x =/ z.
Proof.
  intros. destruct x as [a b]; destruct y as [c d]; destruct z as [e f].
  unfold rational_eq in *. eassert (
    a *- PosZ d *- PosZ f = c *- PosZ b *- PosZ f
  ) by (rewrite H; eauto).
  repeat rewrite <- int_mul_assoc in H1.
  rewrite (int_mul_comm (PosZ b)) in H1. repeat rewrite int_mul_assoc in H1.
  rewrite H0 in H1. repeat rewrite <- int_mul_assoc in H1.
  repeat rewrite (int_mul_comm (PosZ d)) in H1.
  repeat rewrite int_mul_assoc in H1.
  remember (a *- PosZ f) as x. remember (e *- PosZ b) as y. rename d into z.
  revert H1; clear; intros.
  eapply int_mul_div; try eassumption. intro Hc; inv Hc.
Qed.

Definition rational_plus (p : rational) (q : rational) :=
  match p, q with
  | Rational a b, Rational c d => match PosZ b *- PosZ d with
    | PosZ x => Rational (a *- PosZ d +- c *- PosZ b) x
    | _ => Rational Zero (P 0)
    end
  end
.

Notation "x +/ y" := (rational_plus x y) (at level 50, left associativity).

Lemma rational_plus_wd : forall p q r,
  p =/ q <-> p +/ r =/ q +/ r.
Proof.
  intros; split; intros;
  destruct p as [a b]; destruct q as [c d]; destruct r as [e f];
  unfold rational_eq in *; unfold rational_plus in *;
  repeat match goal with
  | [ |- context [ match ?x with PosZ _ => _ | _ => _ end ] ] =>
    destruct x eqn: ?
  | [ H : context [ match ?x with PosZ _ => _ | _ => _ end ] |- _ ] =>
    destruct x eqn: ?
  end; try (
    simpl in *;
    repeat match goal with
    | [ H : context [ match ?x with P _ => _ end ] |- _ ] =>
      destruct x eqn: ?
    | H : PosZ _ = Zero |- _ => inv H
    | H : PosZ _ = NegZ _ |- _ => inv H
    end; fail
  ).
  + rewrite <- Heqi0; rewrite <- Heqi.
    repeat rewrite int_dist_back; repeat rewrite int_mul_assoc.
    (* first term *)
    repeat rewrite <- (int_mul_assoc _ (PosZ f)).
    repeat rewrite (int_mul_comm (PosZ f)).
    repeat rewrite int_mul_assoc; rewrite H.
    (* second term *)
    rewrite <- (int_mul_assoc e).
    rewrite (int_mul_comm (PosZ b)).
    rewrite int_mul_assoc; refl.
  + rewrite <- Heqi0 in H; rewrite <- Heqi in H.
    repeat rewrite int_mul_assoc in H.
    repeat rewrite int_dist_back in H.
    (* first term *)
    repeat rewrite <- (int_mul_assoc _ (PosZ f)) in H.
    repeat rewrite (int_mul_comm (PosZ f)) in H.
    repeat rewrite int_mul_assoc in H.
    repeat rewrite <- int_mul_assoc in H. remember (PosZ f *- PosZ f) as x.
    repeat rewrite int_mul_assoc in H.
    (* second term *)
    rewrite <- (int_mul_assoc _ (PosZ b)) in H.
    rewrite (int_mul_comm (PosZ b)) in H. rewrite int_mul_assoc in H.
    remember (e *- PosZ d *- PosZ b *- PosZ f) as y.
    assert (forall y, y +- -- y = Zero). {
      clear; intros. destruct y; refl; simpl in *; destruct p.
      + destruct (Nat.leb n n) eqn: ?; reflection; try nia.
        destruct (n - n) eqn: ?; try nia. refl.
      + destruct (Nat.leb n n) eqn: ?; reflection; try nia.
        destruct (n - n) eqn: ?; try nia. refl.
    } eassert (
      a *- PosZ d *- x +- y +- -- y = c *- PosZ b *- x +- y +- -- y
    ) by (rewrite H; refl). clear H.
    repeat rewrite <- int_plus_assoc in H1. repeat rewrite H0 in H1.
    unfold int_plus in H1.
    assert (a *- PosZ d *- x = c *- PosZ b *- x). {
      destruct (a *- PosZ d *- x) as [[n] | | [n]] eqn: ?;
      destruct (c *- PosZ b *- x) as [[m] | | [m]] eqn: ?;
      try assumption.
    } clear H0 H1.
    eapply int_mul_div; try eassumption. subst x; clear.
    unfold int_mul. destruct f. simpl in *. intro Hc; inv Hc.
Qed.

Lemma rational_plus_comm : forall p q, p +/ q =/ q +/ p.
Proof.
  intros. destruct p as [a b]; destruct q as [c d].
  unfold rational_plus. rewrite (int_mul_comm (PosZ d) (PosZ b)).
  destruct (PosZ b *- PosZ d) eqn: EQ; try (
    simpl in EQ; destruct b; destruct d; inv EQ; fail
  ). rewrite int_plus_comm. refl.
Qed.

Lemma rational_plus_assoc : forall p q r, p +/ (q +/ r) =/ p +/ q +/ r.
Proof.
  intros. destruct p as [a b]; destruct q as [c d]; destruct r as [e f].
  unfold rational_plus. repeat match goal with
  | [ |- context [ match ?x with PosZ _ => _ | _ => _ end ] ] =>
    destruct x eqn: ?
  end; try (
    simpl in *; repeat match goal with
    | H : PosZ _ = Zero |- _ => inv H
    | H : PosZ _ = NegZ _ |- _ => inv H
    | [ H : context [ match ?x with P _ => _ end ] |- _ ] => destruct x
    end; fail
  ). repeat rewrite int_dist_back. rewrite int_plus_assoc.
  (* replace (a *- PosZ d *- PosZ f) with (a *- PosZ p) *)
  rewrite <- Heqi; rewrite int_mul_assoc.
  (* replace (c *- PosZ b *- PosZ f) with (c *- PosZ f *- PosZ b) *)
  rewrite <- (int_mul_assoc c _ _); rewrite (int_mul_comm _ (PosZ b));
  rewrite int_mul_assoc.
  (* replace (e *- PosZ p1) with (e *- PosZ d *- PosZ b) *)
  rewrite <- Heqi1; rewrite (int_mul_comm (PosZ b) _);
  rewrite int_mul_assoc.
  replace p2 with p0; refl.
  eassert (D : PosZ p0 = PosZ p2 -> p0 = p2) by (
    clear; intro H; inv H; eauto
  ); apply D; clear D. rewrite <- Heqi2; rewrite <- Heqi0.
  rewrite <- Heqi1; rewrite <- Heqi. apply int_mul_assoc.
Qed.

Definition rational_mul (p : rational) (q : rational) :=
  match p, q with
  | Rational a b, Rational c d => match PosZ b *- PosZ d with
    | PosZ x => Rational (a *- c) x
    | _ => Rational Zero (P 0)
    end
  end
.

Notation "x */ y" := (rational_mul x y) (at level 40, left associativity).

Lemma rational_mul_wd : forall p q r,
  p =/ q -> p */ r =/ q */ r.
Proof.
  intros;
  destruct p as [a b]; destruct q as [c d]; destruct r as [e f];
  unfold rational_eq in *; unfold rational_mul in *;
  repeat match goal with
  | [ |- context [ match ?x with PosZ _ => _ | _ => _ end ] ] =>
    destruct x eqn: ?
  | [ H : context [ match ?x with PosZ _ => _ | _ => _ end ] |- _ ] =>
    destruct x eqn: ?
  end; try (
    simpl in *;
    repeat match goal with
    | [ H : context [ match ?x with P _ => _ end ] |- _ ] =>
      destruct x eqn: ?
    | H : PosZ _ = Zero |- _ => inv H
    | H : PosZ _ = NegZ _ |- _ => inv H
    end; fail
  ).
  rewrite <- Heqi; rewrite <- Heqi0. repeat rewrite int_mul_assoc.
  replace (c *- e *- PosZ b) with (a *- e *- PosZ d); refl.
  repeat rewrite <- int_mul_assoc; repeat rewrite (int_mul_comm e).
  repeat rewrite int_mul_assoc; rewrite H; refl.
Qed.

Lemma rational_mul_comm : forall x y, x */ y =/ y */ x.
Proof.
  intros. destruct x as [a b]; destruct y as [c d]. unfold rational_mul.
  repeat match goal with
  | [ |- context [ match ?x with PosZ _ => _ | _ => _ end ] ] =>
    destruct x eqn: ?
  end; try (
    simpl in *; repeat match goal with
    | H : PosZ _ = Zero |- _ => inv H
    | H : PosZ _ = NegZ _ |- _ => inv H
    | [ H : context [ match ?x with P _ => _ end ] |- _ ] => destruct x
    end; fail
  ). rewrite int_mul_comm. replace p0 with p; refl.
  eassert (D : PosZ p = PosZ p0 -> p = p0) by (
    clear; intro H; inv H; eauto
  ); apply D; clear D. rewrite <- Heqi0; rewrite <- Heqi.
  apply int_mul_comm.
Qed.

Lemma rational_mul_assoc : forall x y z, x */ (y */ z) =/ x */ y */ z.
Proof.
  intros. destruct x as [a b]; destruct y as [c d]; destruct z as [e f].
  unfold rational_mul. repeat match goal with
  | [ |- context [ match ?x with PosZ _ => _ | _ => _ end ] ] =>
    destruct x eqn: ?
  end; try (
    simpl in *; repeat match goal with
    | H : PosZ _ = Zero |- _ => inv H
    | H : PosZ _ = NegZ _ |- _ => inv H
    | [ H : context [ match ?x with P _ => _ end ] |- _ ] => destruct x
    end; fail
  ). rewrite int_mul_assoc. replace p2 with p0; refl.
  eassert (D : PosZ p0 = PosZ p2 -> p0 = p2) by (
    clear; intro H; inv H; eauto
  ); apply D; clear D. rewrite <- Heqi2; rewrite <- Heqi0.
  rewrite <- Heqi1; rewrite <- Heqi. apply int_mul_assoc.
Qed.

Lemma rational_dist_front : forall x y z,
  x */ (y +/ z) =/ x */ y +/ x */ z.
Proof.
  intros. destruct x as [a b]; destruct y as [c d]; destruct z as [e f].
  unfold rational_mul; unfold rational_plus; repeat match goal with
  | [ |- context [ match ?x with PosZ _ => _ | _ => _ end ] ] =>
    destruct x eqn: ?
  end; try (
    simpl in *; repeat match goal with
    | H : PosZ _ = Zero |- _ => inv H
    | H : PosZ _ = NegZ _ |- _ => inv H
    | [ H : context [ match ?x with P _ => _ end ] |- _ ] => destruct x
    end; fail
  ). rewrite int_dist_front. repeat rewrite int_mul_assoc.
  unfold rational_eq. rewrite <- Heqi3; rewrite <- Heqi0.
  rewrite <- Heqi; rewrite <- Heqi1; rewrite <- Heqi2.
  repeat rewrite int_plus_assoc; repeat rewrite int_mul_assoc.
  rewrite int_dist_back; repeat rewrite int_mul_assoc.
  (* first term *)
  rewrite <- (int_mul_assoc (a *- c)). rewrite (int_mul_comm (PosZ f)).
  rewrite int_mul_assoc.
  (* second term *)
  rewrite <- (int_mul_assoc (a *- e)). rewrite (int_mul_comm (PosZ d)).
  rewrite int_mul_assoc.
  (* parenthesis term ok *)
  remember (a *- c *- PosZ b *- PosZ f +- a *- e *- PosZ b *- PosZ d).
  (* last step *)
  rewrite <- (int_mul_assoc i). rewrite (int_mul_comm (PosZ d)).
  rewrite int_mul_assoc; refl.
Qed.

Lemma rational_dist_back : forall x y z,
  (x +/ y) */ z =/ x */ z +/ y */ z.
Proof.
  intros. assert (FACT1 := rational_dist_front z x y).
  assert (FACT2 := rational_mul_comm (x +/ y) z).
  assert (FACT3 := rational_eq_trans _ _ _ FACT2 FACT1).
  clear FACT1 FACT2.
  assert (FACT4 := rational_mul_comm z x).
  assert (FACT5 := rational_plus_wd (z */ x) (x */ z) (z */ y)).
  destruct FACT5 as [FACT5 _]. specialize (FACT5 FACT4).
  assert (FACT6 := rational_eq_trans _ _ _ FACT3 FACT5).
  clear FACT3 FACT4 FACT5.
  assert (FACT7 := rational_mul_comm z y).
  assert (FACT8 := rational_plus_wd (z */ y) (y */ z) (x */ z)).
  destruct FACT8 as [FACT8 _]. specialize (FACT8 FACT7).
  assert (FACT9 := rational_plus_comm (x */ z) (z */ y)).
  assert (FACT10 := rational_eq_trans _ _ _ FACT6 FACT9).
  assert (FACT11 := rational_eq_trans _ _ _ FACT10 FACT8).
  revert FACT11; clear; intros.
  assert (FACT12 := rational_plus_comm (y */ z) (x */ z)).
  assert (FACT13 := rational_eq_trans _ _ _ FACT11 FACT12).
  assumption.
Qed.

Definition rational_plus_inv (r : rational) :=
  match r with
  | Rational a b => Rational (-- a) b
  end
.

Notation "--/ x" := (rational_plus_inv x)
  (at level 30, right associativity).

Definition rational_abs (r : rational) :=
  match r with
  | Rational (NegZ x) b => Rational (PosZ x) b
  | _ => r
  end
.

Definition rational_positive (r : rational) :=
  match r with
  | Rational (PosZ _) _ => True
  | _ => False
  end
.

Definition rational_nonnegative (r : rational) :=
  match r with
  | Rational (NegZ _) _ => False
  | _ => True
  end
.

Definition rational_le (p : rational) (q : rational) :=
  rational_nonnegative (q +/ --/ p).

Definition rational_lt (p : rational) (q : rational) :=
  rational_positive (q +/ --/ p).

Definition rational_ge (p : rational) (q : rational) :=
  rational_le q p.

Definition rational_gt (p : rational) (q : rational) :=
  rational_lt q p.

Notation "x <=/ y" := (rational_le x y) (at level 70, no associativity).
Notation "x </ y" := (rational_lt x y) (at level 70, no associativity).
Notation "x >=/ y" := (rational_ge x y) (at level 70, no associativity).
Notation "x >/ y" := (rational_gt x y) (at level 70, no associativity).
