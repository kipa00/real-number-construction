Require Export rational.

Ltac int_contra :=
  match goal with
  | H : PosZ _ = Zero |- _ => inv H
  | H : PosZ _ = NegZ _ |- _ => inv H
  | H : Zero = PosZ _ |- _ => inv H
  | H : Zero = NegZ _ |- _ => inv H
  | H : NegZ _ = PosZ _ |- _ => inv H
  | H : NegZ _ = Zero |- _ => inv H
  | H : S _ = 0 |- _ => inv H
  | H : 0 = S _ |- _ => inv H
  end
.

Ltac simpl_int :=
  unfold int_mul in *; unfold int_plus in *;
  unfold int_plus_inv in *; repeat match goal with
  | [ H : context [ match ?x with P _ => _ end ] |- _ ] =>
    destruct x eqn: ?
  | [ |- context [ match ?x with P _ => _ end ] ] => destruct x eqn: ?
  | [ H : context [ match ?x with 0 => _ | S _ => _ end ] |- _ ] =>
    destruct x eqn: ?
  | [ |- context [ match ?x with 0 => _ | S _ => _ end ] ] =>
    destruct x eqn: ?
  end; try int_contra
.

Ltac destruct_posz :=
  repeat match goal with
  | [ |- context [ match ?x with PosZ _ => _ | _ => _ end ] ] =>
    destruct x eqn: ?
  | [ H : context [ match ?x with PosZ _ => _ | _ => _ end ] |- _ ] =>
    destruct x eqn: ?
  end; try (simpl_int; fail)
.

Ltac simpl_eq :=
  repeat match goal with
  | H : True |- _ => clear H
  | H : S _ = S _ |- _ => inv H
  | H : P _ = P _ |- _ => inv H
  | H : PosZ _ = PosZ _ |- _ => inv H
  | H : NegZ _ = NegZ _ |- _ => inv H
  | |- S ?x = S ?y => replace y with x; refl
  | |- P ?x = P ?y => replace y with x; refl
  | |- PosZ ?x = PosZ ?y => replace y with x; refl
  | |- NegZ ?x = NegZ ?y => replace y with x; refl
  end; refl
.

Ltac reverse :=
  match goal with
  | |- ?x = ?y => replace x with y; refl
  end
.

Lemma rational_le_refl : forall x, x <=/ x.
Proof.
  intros x.
  assert (Hzero : forall x, x +- --x = Zero). {
    clear; intros. destruct x; simpl; refl; destruct p;
    destruct (Nat.leb n n) eqn: EQ; reflection; try nia;
    replace (n - n) with 0 by nia; refl.
  }
  unfold rational_le.
  unfold rational_plus; unfold rational_plus_inv;
  destruct x as [[[a] | | [a]] b]; destruct_posz; try (
    simpl in *; trivial; fail
  ); rewrite <- int_dist_back; rewrite Hzero; simpl in *; trivial.
Qed.

Lemma rational_le_antisymm : forall x y, x <=/ y -> y <=/ x -> x =/ y.
Proof.
  intros.
  destruct x as [[[a] | | [a]] [b]]; destruct y as [[[c] | | [c]] [d]];
  unfold rational_le in *; unfold rational_plus in *;
  unfold rational_plus_inv in *; destruct_posz; simpl_int; simpl in *;
  repeat match goal with
  | [ H : context [ if ?x then _ else _ ] |- _ ] => destruct x eqn: ?
  end; simpl_eq; reflection; try nia.
Qed.

Lemma rational_le_trans : forall x y z, x <=/ y -> y <=/ z -> x <=/ z.
Proof.
  intros. unfold rational_le in *.
  assert (z +/ --/ x =/ z +/ --/ y +/ (y +/ --/ x)). {
    clear. apply rational_eq_symm.
    eapply rational_eq_trans; try eapply rational_plus_assoc.
    apply rational_eq_symm.
    assert (z =/ z +/ --/ y +/ y). {
      eapply rational_eq_trans; try eapply rational_plus_assoc.
      assert (--/y +/ y =/ Rational Zero (P 0)). {
        unfold rational_plus; unfold rational_plus_inv.
        clear. destruct y. destruct_posz; try (simpl in *; trivial; fail).
        rewrite <- int_dist_back. replace (-- i +- i) with Zero by (
          clear; destruct i; simpl_int; try destruct (Nat.leb n n);
          eauto; nia
        ). simpl in *; eauto.
      } eapply (rational_plus_wd _ _ z) in H.
      eapply rational_eq_trans in H; try eapply rational_plus_comm.
      apply rational_eq_symm in H. eapply rational_eq_trans;
      try eapply H. clear. destruct z. unfold rational_plus.
      destruct_posz; try (
        simpl in *; destruct_posz; simpl in *; int_contra
      ). simpl. destruct p; destruct p0. simpl in *.
      simpl_eq. rewrite <- int_mul_assoc. simpl in *; refl.
    } eapply (rational_plus_wd _ _ (--/ x)) in H. assumption.
  }
  assert (
    forall x y, x =/ y ->
    rational_nonnegative x <-> rational_nonnegative y
  ). {
    clear; intros; split; intros;
    destruct x as [[[a] | | [a]] b]; destruct y as [[[c] | | [c]] d];
    simpl in *; eauto; destruct_posz.
  } eapply H2; try eassumption. clear H1 H2.
  remember (y +/ --/ x) as b; remember (z +/ --/ y) as a;
  revert H0 H; clear; intros H H0.
  destruct a as [[[a] | | [a]] n]; destruct b as [[[b] | | [b]] m];
  try (simpl in *; inv H; inv H0; fail); simpl in *; destruct_posz;
  simpl_int; eauto.
Qed.

Lemma rational_le_tri : forall x y,
  rational_abs (x +/ y) <=/ rational_abs x +/ rational_abs y.
Proof.
  intros. destruct x as [[[a] | | [a]] b]; destruct y as [[[c] | | [c]] d];
  unfold rational_abs; unfold rational_le;
  unfold rational_plus; unfold rational_plus_inv; destruct_posz; simpl_int;
  try (simpl in *; int_contra);
  repeat match goal with
  | [ |- context [ if ?x then _ else _ ] ] => destruct x eqn: ?
  | [ H : context [ if ?x then _ else _ ] |- _ ] => destruct x eqn: ?
  end; trivial; reflection; try int_contra; simpl_eq; simpl;
  remember (fun x y => x - y) as minus;
  repeat match goal with
  | [ H : context [ minus ?x ?y ] |- _ ] =>
    replace (minus x y) with (S x - S y) in H by (subst; clear; eauto)
  | [ H : context [ S (S (?x + ?y)) ] |- _ ] =>
    replace (S (S (x + y))) with (S x + S y) in H by (clear; nia)
  | [ H : context [ ?x <= ?y ] |- _ ] => apply leb_refl in H;
    replace (Nat.leb x y) with (Nat.leb (S x) (S y)) in H by (clear; eauto)
  | [ H : context [ ?x > ?y ] |- _ ] => apply leb_frefl in H;
    replace (Nat.leb x y) with (Nat.leb (S x) (S y)) in H by (clear; eauto)
  end; reflection; repeat match goal with
  | [ H : context [ S ?x ] |- _ ] => remember (S x); match goal with
    | H : _ = S x |- _ => clear H
    end
  end; subst; try nia.
Qed.

Lemma rational_lt_asymm : forall x y, ~(x </ y /\ y </ x).
Proof.
  intros x y H; destruct H.
  destruct x as [[[a] | | [a]] b]; destruct y as [[[c] | | [c]] d];
  unfold rational_lt in *; unfold rational_plus in *;
  unfold rational_plus_inv in *; destruct_posz; simpl_int;
  repeat match goal with
  | [ H : context [ if ?x then _ else _ ] |- _ ] => destruct x eqn: ?
  end; try (
    unfold rational_positive; simpl in *; match goal with
    | H : False |- _ => inv H
    end; fail
  ); reflection; nia.
Qed.

Lemma rational_lt_trans : forall x y z, x </ y -> y </ z -> x </ z.
Proof.
  intros. unfold rational_lt in *.
  assert (z +/ --/ x =/ z +/ --/ y +/ (y +/ --/ x)). {
    clear. apply rational_eq_symm.
    eapply rational_eq_trans; try eapply rational_plus_assoc.
    apply rational_eq_symm.
    assert (z =/ z +/ --/ y +/ y). {
      eapply rational_eq_trans; try eapply rational_plus_assoc.
      assert (--/y +/ y =/ Rational Zero (P 0)). {
        unfold rational_plus; unfold rational_plus_inv.
        clear. destruct y. destruct_posz; try (simpl in *; trivial; fail).
        rewrite <- int_dist_back. replace (-- i +- i) with Zero by (
          clear; destruct i; simpl_int; try destruct (Nat.leb n n);
          eauto; nia
        ). simpl in *; eauto.
      } eapply (rational_plus_wd _ _ z) in H.
      eapply rational_eq_trans in H; try eapply rational_plus_comm.
      apply rational_eq_symm in H. eapply rational_eq_trans;
      try eapply H. clear. destruct z. unfold rational_plus.
      destruct_posz; try (
        simpl in *; destruct_posz; simpl in *; int_contra
      ). simpl. destruct p; destruct p0. simpl in *.
      simpl_eq. rewrite <- int_mul_assoc. simpl in *; refl.
    } eapply (rational_plus_wd _ _ (--/ x)) in H. assumption.
  } assert (
    forall x y, x =/ y ->
    rational_positive x <-> rational_positive y
  ). {
    clear; intros; split; intros;
    destruct x as [[[a] | | [a]] b]; destruct y as [[[c] | | [c]] d];
    simpl in *; eauto; destruct_posz.
  } eapply H2; try eassumption. clear H1 H2.
  remember (y +/ --/ x) as b; remember (z +/ --/ y) as a.
  revert H0 H; clear; intros H H0.
  destruct a as [[[a] | | [a]] n]; destruct b as [[[b] | | [b]] m]; try (
    simpl in *; repeat match goal with
    | H : False |- _ => inv H
    end; fail
  ). clear. simpl; destruct_posz; simpl_int; simpl; trivial.
Qed.

Lemma rational_abs_wd : forall x y,
  x =/ y -> rational_abs x =/ rational_abs y.
Proof.
  intros. destruct x as [[[a] | | [a]] b]; destruct y as [[[c] | | [c]] d];
  unfold rational_eq in *; unfold rational_abs; simpl_int; refl; simpl_eq.
Qed.

Ltac rational_rw H := eapply rational_eq_trans; try eapply H.

Lemma rational_plus_inv_wd : forall x y,
  x =/ y <-> --/ x =/ --/ y.
Proof.
  intros; split; intros;
  destruct x as [[[a] | | [a]] b]; destruct y as [[[c] | | [c]] d];
  unfold rational_eq in *; unfold rational_plus_inv in *; simpl_int;
  trivial; simpl_eq.
Qed.

Lemma rational_le_wd : forall x y x' y',
  x =/ x' -> y =/ y' -> x <=/ y <-> x' <=/ y'.
Proof.
  assert (
    forall x y, x =/ y ->
    rational_nonnegative x <-> rational_nonnegative y
  ). {
    clear; intros; split; intros;
    destruct x as [[[a] | | [a]] b]; destruct y as [[[c] | | [c]] d];
    simpl in *; eauto; destruct_posz.
  }
  intros; split; intros.
  + unfold rational_le in *. eapply H; try eassumption.
    revert H0 H1; clear; intros.
    eapply (rational_plus_wd _ _ (--/ x)) in H1. eapply rational_eq_symm.
    rational_rw H1. rational_rw rational_plus_comm.
    eapply rational_eq_symm. rational_rw rational_plus_comm.
    apply -> rational_plus_wd. apply -> rational_plus_inv_wd.
    eapply rational_eq_symm; eassumption.
  + unfold rational_le in *. eapply H; try eassumption.
    clear H H2. eapply (rational_plus_wd _ _ (--/ x)) in H1.
    rational_rw H1. rational_rw rational_plus_comm.
    eapply rational_eq_symm. rational_rw rational_plus_comm.
    apply -> rational_plus_wd. apply -> rational_plus_inv_wd.
    eapply rational_eq_symm; assumption.
Qed.

Lemma rational_lt_wd : forall x y x' y',
  x =/ x' -> y =/ y' -> x </ y <-> x' </ y'.
Proof.
  assert (
    forall x y, x =/ y ->
    rational_positive x <-> rational_positive y
  ). {
    clear; intros; split; intros;
    destruct x as [[[a] | | [a]] b]; destruct y as [[[c] | | [c]] d];
    simpl in *; eauto; destruct_posz.
  } intros; split; intros.
  + unfold rational_lt in *. eapply H; try eassumption.
    revert H0 H1; clear; intros.
    eapply (rational_plus_wd _ _ (--/ x)) in H1. eapply rational_eq_symm.
    rational_rw H1. rational_rw rational_plus_comm.
    eapply rational_eq_symm. rational_rw rational_plus_comm.
    apply -> rational_plus_wd. apply -> rational_plus_inv_wd.
    eapply rational_eq_symm; eassumption.
  + unfold rational_lt in *. eapply H; try eassumption.
    clear H H2. eapply (rational_plus_wd _ _ (--/ x)) in H1.
    rational_rw H1. rational_rw rational_plus_comm.
    eapply rational_eq_symm. rational_rw rational_plus_comm.
    apply -> rational_plus_wd. apply -> rational_plus_inv_wd.
    eapply rational_eq_symm; assumption.
Qed.

Lemma rational_eq_minus : forall x y,
  x =/ y <-> x +/ --/ y =/ Rational Zero (P 0).
Proof.
  intros; split; intros;
  destruct x as [[[a] | | [a]] b]; destruct y as [[[c] | | [c]] d];
  unfold rational_eq in *; simpl; simpl_int; try int_contra;
  repeat match goal with
  | [ |- context [ if ?x then _ else _ ] ] => destruct x eqn: ?
  end; trivial; reflection; try (simpl in *; int_contra); simpl_eq;
  try lia; unfold rational_plus in *; unfold rational_plus_inv in *;
  simpl_int; try (simpl in *; int_contra);
  repeat match goal with
  | [ H : context [ if ?x then _ else _ ] |- _ ] => destruct x eqn: ?
  end; reflection; try lia; simpl in *; int_contra.
Qed.

Lemma rational_le_lt : forall x y, x <=/ y <-> x </ y \/ x =/ y.
Proof.
  intros; split; intros.
  + unfold rational_lt; unfold rational_le in H. remember (y +/ --/ x).
    destruct r as [[[a] | | [a]] b] eqn: ?.
    - left; simpl; trivial.
    - right. apply rational_eq_symm. eapply rational_eq_minus.
      symmetry in Heqr. eassert (Heq : y +/ --/ x =/ Rational Zero b) by (
        rewrite Heqr; apply rational_eq_refl
      ). rational_rw Heq; clear.
      unfold rational_eq; simpl_int. trivial.
    - inv H.
  + destruct H.
    - unfold rational_lt in H; unfold rational_le. remember (y +/ --/ x).
      destruct r; simpl in *; try (inv H; fail).
      destruct i; try (inv H; fail). trivial.
    - apply rational_eq_symm in H. apply rational_eq_minus in H.
      unfold rational_le. remember (y +/ --/ x).
      destruct r as [[[a] | | [a]] b]; simpl in *; trivial. inv H.
Qed.

Lemma rational_plus_inv_mul : forall x,
  --/ x =/ Rational (NegZ (P 0)) (P 0) */ x.
Proof.
  intros; destruct x as [[[a] | | [a]] b] eqn: ?;
  unfold rational_plus_inv; unfold rational_eq; unfold rational_mul;
  simpl_int; trivial; try (
    simpl in *; int_contra
  ); simpl in *; simpl_eq; nia.
Qed.

Lemma rational_lt_plus : forall a b c d,
  a </ b -> c </ d -> a +/ c </ b +/ d.
Proof.
  intros. unfold rational_lt in *.
  assert (
    forall x y, x =/ y ->
    rational_positive x <-> rational_positive y
  ). {
    clear; intros; split; intros;
    destruct x as [[[a] | | [a]] b]; destruct y as [[[c] | | [c]] d];
    simpl in *; eauto; destruct_posz.
  } assert (
    b +/ --/ a +/ (d +/ --/ c) =/ b +/ d +/ --/ (a +/ c)
  ). {
    clear.
    assert (H : forall p q r : rational, p +/ q +/ r =/ p +/ (q +/ r)). {
      clear; intros. apply rational_eq_symm. apply rational_plus_assoc.
    } rational_rw H. apply rational_eq_symm. rational_rw H.
    rational_rw rational_plus_comm. apply rational_eq_symm.
    rational_rw rational_plus_comm. apply -> rational_plus_wd.
    assert (H0 := rational_plus_comm d (--/ c)).
    eapply (rational_plus_wd _ _ (--/ a)) in H0.
    assert (H1 := rational_plus_comm (d +/ --/ c) (--/ a)).
    apply rational_eq_symm in H1.
    assert (H2 := rational_eq_trans _ _ _ H1 H0).
    rational_rw H2. rational_rw rational_plus_comm. clear H0 H1 H2.
    rational_rw rational_plus_assoc. apply rational_eq_symm.
    rational_rw rational_plus_comm. apply -> rational_plus_wd.
    rational_rw rational_plus_inv_mul.
    rational_rw rational_dist_front.
    assert (H0 := rational_plus_inv_mul a).
    eapply (rational_plus_wd _ _ (--/ c)) in H0.
    apply rational_eq_symm in H0. rational_rw H0.
    rational_rw rational_plus_comm. apply rational_eq_symm.
    rational_rw rational_plus_comm. apply -> rational_plus_wd.
    apply rational_plus_inv_mul.
  } specialize (H1 _ _ H2). apply -> H1. clear H1 H2.
  remember (b +/ --/ a) as x. remember (d +/ --/ c) as y.
  revert H H0; clear; intros.
  destruct x as [[[a] | | [a]] b]; destruct y as [[[c] | | [c]] d];
  try (inv H; inv H0; fail). unfold rational_plus. simpl_int; try (
    simpl in *; int_contra
  ). simpl. trivial.
Qed.

Lemma rational_abs_mul : forall x y,
  rational_abs (x */ y) =/ rational_abs x */ rational_abs y.
Proof.
  intros; destruct x as [[[a] | | [a]] b]; destruct y as [[[c] | | [c]] d];
  unfold rational_abs; unfold rational_mul; unfold rational_eq;
  destruct_posz; simpl_int; trivial; try (simpl in *; int_contra);
  simpl_eq; nia.
Qed.

Lemma rational_lt_split : forall x y, x </ y \/ x =/ y \/ x >/ y.
Proof.
  intros; unfold rational_gt; unfold rational_lt.
  destruct (y +/ --/ x) as [[[a] | | [a]] b] eqn: EQ.
  + left. simpl; trivial.
  + right; left. apply rational_eq_symm. apply rational_eq_minus.
    rewrite EQ. simpl; trivial.
  + right; right. assert (x +/ --/ y =/ --/ (y +/ --/ x)). {
      clear. apply rational_eq_symm. rational_rw rational_plus_inv_mul.
      rational_rw rational_dist_front. apply rational_eq_symm.
      rational_rw rational_plus_comm. assert (H := rational_plus_inv_mul y).
      eapply rational_plus_wd in H; rational_rw H; clear H.
      rational_rw rational_plus_comm. apply rational_eq_symm.
      rational_rw rational_plus_comm. apply -> rational_plus_wd. clear.
      destruct x as [[[a] | | [a]] b]; unfold rational_plus_inv;
      unfold rational_mul; unfold rational_eq; simpl_int; trivial; try (
        simpl in *; int_contra
      ); simpl_eq; nia.
    } rewrite EQ in H; clear EQ. simpl in H.
    assert (
      forall x y, x =/ y ->
      rational_positive x <-> rational_positive y
    ). {
      clear; intros; split; intros;
      destruct x as [[[a] | | [a]] b]; destruct y as [[[c] | | [c]] d];
      simpl in *; eauto; destruct_posz.
    } apply rational_eq_symm in H. apply -> H0; try eassumption.
    simpl; trivial.
Qed.

Lemma rational_archimedean : forall p, exists M,
  p </ Rational (PosZ (P M)) (P 0).
Proof.
  intros. destruct p as [[[a] | | [a]] b]; try (
    exists 0; unfold rational_lt; simpl; destruct_posz; simpl_int;
    try match goal with
    | [ |- context [ if ?x then _ else _ ] ] => destruct x eqn: ?
    end; reflection; simpl; trivial; nia
  ). exists (S a). unfold rational_lt; simpl; destruct_posz; simpl_int;
  try match goal with
  | [ |- context [ if ?x then _ else _ ] ] => destruct x eqn: ?
  end; reflection; simpl; trivial; try nia.
Qed.

Lemma rational_finite_maximum : forall f N,
  exists M, forall n, n <= N -> f n </ Rational (PosZ (P M)) (P 0).
Proof.
  intros. induction N.
  + destruct (rational_archimedean (f 0)) as [N H]. exists N; intros.
    eassert (n = 0) by nia; subst; eassumption.
  + destruct IHN as [M1 HM1].
    destruct (rational_archimedean (f (S N))) as [M2 HM2].
    destruct (Nat.leb M1 M2) eqn: EQ; reflection.
    - exists M2. intros. inv H; try assumption.
      specialize (HM1 _ H1). inv EQ; try assumption.
      eapply rational_lt_trans; try eassumption.
      unfold rational_lt; simpl.
      replace (Nat.leb (M1 * 1) (S (m * 1))) with true by (
        symmetry; apply leb_refl; nia
      ). simpl_int; trivial. nia.
    - exists M1. intros. inv H.
      * eapply rational_lt_trans; try eassumption. unfold rational_lt.
        simpl. replace (Nat.leb (M2 * 1) (M1 * 1)) with true by (
          symmetry; apply leb_refl; nia
        ). simpl_int; trivial. nia.
      * exact (HM1 _ H1).
Qed.

Lemma rational_abs_elim : forall x y,
  rational_abs x </ y <-> --/ y </ x /\ x </ y.
Proof.
  intros; split; intros; try split;
  try match goal with
  | H : _ /\ _ |- _ => destruct H
  end; destruct x as [[[a] | | [a]] [b]]; destruct y as [[[c] | | [c]] [d]];
  unfold rational_lt in *; unfold rational_plus in *;
  unfold rational_plus_inv in *; unfold rational_abs in *;
  simpl_int; try (simpl in *; trivial; int_contra); try match goal with
  | [ H : context [ if ?x then _ else _ ] |- _ ] => destruct x eqn: ?
  | [ |- context [ if ?x then _ else _ ] ] => destruct x eqn: ?
  end; reflection; try (
    simpl in *; trivial; try match goal with
    | H : False |- _ => inv H
    end; int_contra
  ); try lia; try match goal with
  | [ H : context [ if ?x then _ else _ ] |- _ ] => destruct x eqn: ?
  | [ |- context [ if ?x then _ else _ ] ] => destruct x eqn: ?
  end; reflection; try (simpl in *; trivial; int_contra); nia.
Qed.

Ltac rsymm := apply rational_eq_symm.

Lemma rational_diff_sum : forall x y z w,
  x +/ y +/ --/ (z +/ w) =/ x +/ --/ z +/ (y +/ --/ w).
Proof.
  intros. assert (H : forall x y z, x +/ y +/ z =/ x +/ (y +/ z)). {
    clear; intros. rsymm. apply rational_plus_assoc.
  } rational_rw H. rsymm. rational_rw H.
  rational_rw rational_plus_comm. rsymm. rational_rw rational_plus_comm.
  apply -> rational_plus_wd. rsymm. rational_rw rational_plus_assoc.
  assert (H0 := rational_plus_comm (--/ z) y).
  eapply (rational_plus_wd _ _ (--/ w)) in H0. rational_rw H0.
  clear H0. rational_rw H. rational_rw rational_plus_comm.
  rsymm. rational_rw rational_plus_comm. apply -> rational_plus_wd.
  rational_rw rational_plus_inv_mul. rational_rw rational_dist_front.
  clear H. assert (H := rational_plus_inv_mul z).
  eapply (rational_plus_wd _ _ (--/ w)) in H. rsymm. rational_rw H.
  rational_rw rational_plus_comm. rsymm. rational_rw rational_plus_comm.
  apply -> rational_plus_wd. rsymm. apply rational_plus_inv_mul.
Qed.

Lemma rational_pm_zero : forall x, x +/ --/ x =/ Rational Zero (P 0).
Proof.
  intros. destruct x as [[[a] | | [a]] [b]];
  unfold rational_plus; unfold rational_plus_inv; unfold rational_eq;
  simpl_int; try (simpl in *; trivial; int_contra); match goal with
  | [ |- context [ if ?x then _ else _ ] ] => destruct x eqn: ?
  end; reflection; try (simpl in *; trivial; int_contra);
  simpl_int; trivial; nia.
Qed.

Lemma rational_plus_zero : forall x, x +/ Rational Zero (P 0) =/ x.
Proof.
  intros. destruct x as [[[a] | | [a]] [b]];
  unfold rational_plus; unfold rational_plus_inv; unfold rational_eq;
  simpl_int; try (simpl in *; trivial; int_contra); simpl_eq; nia.
Qed.

Lemma rational_lt_plus_eq : forall x y z,
  x </ y -> x +/ z </ y +/ z.
Proof.
  intros; unfold rational_lt in *.
  assert (
    forall x y, x =/ y ->
    rational_positive x <-> rational_positive y
  ). {
    clear; intros; split; intros;
    destruct x as [[[a] | | [a]] b]; destruct y as [[[c] | | [c]] d];
    simpl in *; eauto; destruct_posz.
  } apply -> H0; try (rsymm; eapply rational_diff_sum).
  apply -> H0; try eassumption. rsymm; rational_rw rational_plus_zero.
  rational_rw rational_plus_comm; rsymm; rational_rw rational_plus_comm.
  apply -> rational_plus_wd; rsymm. apply rational_pm_zero.
Qed.

Lemma rational_lt_mul : forall x y z w,
  Rational Zero (P 0) </ x -> x </ y -> Rational Zero (P 0) </ z -> z </ w
  -> x */ z </ y */ w.
Proof.
  intros.
  assert (
    forall x, Rational Zero (P 0) </ x
    -> exists a b, x = Rational (PosZ a) b
  ). {
    clear; intros. destruct x as [[[a] | | [a]] [b]]; try (eexists; eauto).
    + inv H.
    + inv H.
  } destruct (H3 x H) as [[a] [[b] Heqx]];
  destruct (H3 z H1) as [[e] [[f] Heqz]].
  destruct (H3 y (rational_lt_trans _ _ _ H H0)) as [[c] [[d] Heqy]];
  destruct (H3 w (rational_lt_trans _ _ _ H1 H2)) as [[g] [[h] Heqw]].
  subst; revert H0 H2; clear; intros.
  unfold rational_mul; unfold rational_lt in *; unfold rational_plus in *;
  unfold rational_plus_inv in *; simpl_int;
  try (simpl in *; trivial; int_contra); repeat match goal with
  | [ H : context [ if ?x then _ else _ ] |- _ ] =>
    destruct x eqn: ?
  | [ |- context [if ?x then _ else _ ] ] => destruct x eqn: ?
  end; reflection; try (simpl in *; trivial; int_contra);
  remember (fun x y => x - y) as minus;
  repeat match goal with
  | H : minus ?x ?y = S _ |- _ =>
    eassert (x > y) by (revert H; subst minus; clear; intros; nia);
    replace (minus x y) with (S x - S y) in H by (subst; clear; eauto)
  end; repeat match goal with
  | [ H : context [ minus ?x ?y ] |- _ ] =>
    replace (minus x y) with (S x - S y) in H by (subst; clear; eauto)
  | [ H : context [ S (S (?x + ?y)) ] |- _ ] =>
    replace (S (S (x + y))) with (S x + S y) in H by (clear; nia)
  | [ H : context [ ?x <= ?y ] |- _ ] => eapply leb_refl in H;
    replace (Nat.leb x y) with (Nat.leb (S x) (S y)) in H by (clear; eauto)
  | [ H : context [ ?x > ?y ] |- _ ] => eapply leb_frefl in H;
    replace (Nat.leb x y) with (Nat.leb (S x) (S y)) in H by (clear; eauto)
  end; reflection; repeat match goal with
  | [ H : context [ S ?x ] |- _ ] => remember (S x); match goal with
    | H : _ = S x |- _ => clear H
    end
  end; subst; nia.
  (* why doesn't it work? *)
  Unshelve. all: exact (P 0).
Qed.

Lemma rational_lt_pos : forall x,
  Rational Zero (P 0) </ x <-> rational_positive x.
Proof.
  intros; split; intros.
  + destruct x as [[[a] | | [a]] [b]]; eauto.
  + destruct x as [[[a] | | [a]] [b]]; eauto.
Qed.

Lemma rational_lt_mul_nonneg : forall x y z w,
  Rational Zero (P 0) <=/ x -> x </ y -> Rational Zero (P 0) <=/ z -> z </ w
  -> x */ z </ y */ w.
Proof.
  intros. apply rational_le_lt in H; apply rational_le_lt in H1.
  destruct H; destruct H1; try (apply rational_lt_mul; assumption).
  + apply -> rational_lt_wd in H2; try (rsymm; eexact H1);
    try (eapply rational_eq_refl). assert (Hy := rational_lt_trans _ _ _ H H0).
    apply -> rational_lt_pos in H2; apply -> rational_lt_pos in Hy.
    assert (rational_positive (y */ w)). {
      destruct y as [[[a] | | [a]] [b]]; destruct w as [[[c] | | [c]] [d]];
      try (inv H2; inv Hy; fail). unfold rational_mul; simpl_int; eauto;
      simpl in *; int_contra.
    } apply rational_lt_pos in H3. eapply rational_lt_wd; try eexact H3;
    try eapply rational_eq_refl. eapply rational_mul_wd in H1.
    rational_rw rational_mul_comm; rsymm. rational_rw H1. clear.
    destruct x as [[[a] | | [a]] [b]]; unfold rational_mul;
    unfold rational_eq; simpl_int; trivial.
  + apply -> rational_lt_wd in H0; try (rsymm; eexact H);
    try (eapply rational_eq_refl).
    assert (Hw := rational_lt_trans _ _ _ H1 H2).
    apply -> rational_lt_pos in H0; apply -> rational_lt_pos in Hw.
    assert (rational_positive (y */ w)). {
      destruct y as [[[a] | | [a]] [b]]; destruct w as [[[c] | | [c]] [d]];
      try (inv H0; inv Hw; fail). unfold rational_mul; simpl_int; eauto;
      simpl in *; int_contra.
    } apply rational_lt_pos in H3. eapply rational_lt_wd; try eexact H3;
    try eapply rational_eq_refl. eapply rational_mul_wd in H; rsymm.
    rational_rw H. clear. destruct z as [[[a] | | [a]] [b]];
    unfold rational_mul; unfold rational_eq; simpl_int; trivial.
  + apply -> rational_lt_wd in H0; try (rsymm; eexact H);
    try (eapply rational_eq_refl). apply -> rational_lt_wd in H2;
    try (rsymm; eexact H1); try (eapply rational_eq_refl).
    apply -> rational_lt_pos in H0; apply -> rational_lt_pos in H2.
    assert (rational_positive (y */ w)). {
      destruct y as [[[a] | | [a]] [b]]; destruct w as [[[c] | | [c]] [d]];
      try (inv H0; inv H2; fail). unfold rational_mul; simpl_int; eauto;
      simpl in *; int_contra.
    } apply rational_lt_pos in H3. eapply rational_lt_wd; try eexact H3;
    try eapply rational_eq_refl. eapply rational_mul_wd in H; rsymm.
    rational_rw H. clear. destruct z as [[[a] | | [a]] [b]];
    unfold rational_mul; unfold rational_eq; simpl_int; trivial.
Qed.
