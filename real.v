Require Export rational.
Require Export rational_prop.

Definition Rational0 := Rational Zero (P 0).
Definition RationalHalf := Rational (PosZ (P 0)) (P 1).

Definition cauchy (f : nat -> rational) : Prop :=
  forall eps : rational, eps >/ Rational0 ->
    exists N : nat, forall n m, n > N -> m > N ->
      rational_abs ((f n) +/ --/ (f m)) </ eps.

Inductive real :=
| Real : forall f : nat -> rational, cauchy f -> real
.

Definition seq_zero (f : nat -> rational) : Prop :=
  forall eps : rational, eps >/ Rational0 ->
    exists N : nat, forall n, n > N ->
      rational_abs (f n) </ eps.

Lemma cauchy_plus : forall f g,
  cauchy f -> cauchy g -> cauchy (fun n => f n +/ g n).
Proof.
  intros f g Hfc Hgc. unfold cauchy; intros.
  specialize (Hfc (RationalHalf */ eps)).
  specialize (Hgc (RationalHalf */ eps)).
  assert (RationalHalf */ eps >/ Rational0). {
    revert H; clear; intros.
    destruct eps as [[[a] | | [a]] b]; try (
      unfold rational_gt in H; unfold rational_lt in H; simpl in H;
      destruct_posz; simpl_int; simpl in H; inv H
    ). unfold rational_gt; unfold rational_lt. simpl. trivial.
  } specialize (Hfc H0); specialize (Hgc H0). clear H0.
  destruct Hfc as [N1 Hf]. destruct Hgc as [N2 Hg].
  exists (if Nat.leb N1 N2 then N2 else N1); intros.
  destruct (Nat.leb N1 N2) eqn: EQ; reflection.
  + eassert (n > N1) by nia; eassert (m > N1) by nia.
    specialize (Hf n m H2 H3); specialize (Hg n m H0 H1).
    clear EQ H0 H1 H2 H3 H N1 N2.
    assert (
      rational_abs (f n +/ g n +/ --/ (f m +/ g m))
      =/ rational_abs (f n +/ --/ f m +/ (g n +/ --/ g m))
    ). { clear. apply rational_abs_wd. apply rational_diff_sum. }
    assert (H0 := rational_eq_refl eps).
    eapply rational_lt_wd; try eassumption. clear H H0.
    assert (H := rational_lt_plus _ _ _ _ Hf Hg).
    assert (RationalHalf */ eps +/ RationalHalf */ eps =/ eps). {
      clear; assert (H := rational_dist_back RationalHalf RationalHalf eps).
      apply rational_eq_symm in H. rational_rw H. clear H.
      destruct eps as [[[a] | | [a]] b]; unfold rational_eq; simpl;
      destruct_posz; simpl_int; try (simpl in *; int_contra); trivial;
      simpl_eq; nia.
    } assert (H1 := rational_lt_wd _ _ _ _ (rational_eq_refl (
      rational_abs (f n +/ --/ f m) +/ rational_abs (g n +/ --/ g m)
    )) H0). destruct H1 as [H1 _].
    specialize (H1 (rational_lt_plus _ _ _ _ Hf Hg)). revert H1; clear.
    intros. remember (f n +/ --/ f m) as x. remember (g n +/ --/ g m) as y.
    revert H1; clear; intros. assert (H := rational_le_tri x y).
    apply rational_le_lt in H. destruct H.
    - eapply rational_lt_trans; eassumption.
    - eapply rational_lt_wd; try eassumption. apply rational_eq_refl.
  + eassert (n > N2) by nia; eassert (m > N2) by nia.
    specialize (Hf n m H0 H1); specialize (Hg n m H2 H3).
    clear EQ H0 H1 H2 H3 H N1 N2.
    assert (
      rational_abs (f n +/ g n +/ --/ (f m +/ g m))
      =/ rational_abs (f n +/ --/ f m +/ (g n +/ --/ g m))
    ). { clear. apply rational_abs_wd. apply rational_diff_sum. }
    assert (H0 := rational_eq_refl eps).
    eapply rational_lt_wd; try eassumption. clear H H0.
    assert (H := rational_lt_plus _ _ _ _ Hf Hg).
    assert (RationalHalf */ eps +/ RationalHalf */ eps =/ eps). {
      clear; assert (H := rational_dist_back RationalHalf RationalHalf eps).
      apply rational_eq_symm in H. rational_rw H. clear H.
      destruct eps as [[[a] | | [a]] b]; unfold rational_eq; simpl;
      destruct_posz; simpl_int; try (simpl in *; int_contra); trivial;
      simpl_eq; nia.
    } assert (H1 := rational_lt_wd _ _ _ _ (rational_eq_refl (
      rational_abs (f n +/ --/ f m) +/ rational_abs (g n +/ --/ g m)
    )) H0). destruct H1 as [H1 _].
    specialize (H1 (rational_lt_plus _ _ _ _ Hf Hg)). revert H1; clear.
    intros. remember (f n +/ --/ f m) as x. remember (g n +/ --/ g m) as y.
    revert H1; clear; intros. assert (H := rational_le_tri x y).
    apply rational_le_lt in H. destruct H.
    - eapply rational_lt_trans; eassumption.
    - eapply rational_lt_wd; try eassumption. apply rational_eq_refl.
Qed.

Definition real_plus (x : real) (y : real) :=
  match x, y with
  | Real f Hf, Real g Hg =>
    Real (fun n => f n +/ g n) (cauchy_plus f g Hf Hg)
  end
.

Lemma cauchy_plus_inv : forall f, cauchy f -> cauchy (fun n => --/ f n).
Proof.
  intros; unfold cauchy; intros.
  specialize (H eps H0). destruct H as [N H]. exists N. intros.
  specialize (H n m H1 H2).
  eapply rational_lt_wd; try eapply (rational_eq_refl eps); try exact H.
  remember (f n) as x; remember (f m) as y; clear.
  destruct x as [[[a] | | [a]] b]; destruct y as [[[c] | | [c]] d];
  unfold rational_eq; unfold rational_plus; unfold rational_plus_inv;
  unfold rational_abs; destruct_posz; simpl_int; trivial; try (
    simpl in *; int_contra
  ); simpl_eq; repeat match goal with
  | [ H : context [ if ?x then _ else _ ] |- _ ] => destruct x eqn: ?
  end; try int_contra; reflection; simpl_eq; remember (
    fun x y => x - y
  ) as minus; eassert (D : forall a b, S a = S b -> a = b) by (
    clear; intros a b H; inv H; refl
  ); apply D; clear D; repeat match goal with
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
  end; subst; refl.
Qed.

Definition real_plus_inv (x : real) :=
  match x with
  | Real f Hf => Real (fun n => --/ f n) (cauchy_plus_inv f Hf)
  end
.

Notation "x +| y" := (real_plus x y) (at level 50, left associativity).
Notation "--| x" := (real_plus_inv x) (at level 30, right associativity).

Definition real_eq (x : real) (y : real) :=
  match (x +| --| y) with
  | Real f Hf => seq_zero f
  end
.

Notation "x =| y" := (real_eq x y) (at level 70, no associativity).

Lemma real_eq_refl : forall x, x =| x.
Proof.
  intros. destruct x as [f Hf]. unfold real_eq.
  unfold real_plus; unfold real_plus_inv. clear Hf. unfold seq_zero.
  intros. exists 0. intros n _. remember (f n) as x.
  eapply rational_lt_wd; try eapply (rational_eq_refl eps); try eapply H.
  clear. destruct x as [[[a] | | [a]] b]; unfold rational_eq;
  unfold rational_abs; unfold rational_plus; unfold rational_plus_inv;
  unfold Rational0; destruct_posz; simpl_int; trivial;
  repeat match goal with
  | [ H : context [ if ?x then _ else _ ] |- _ ] => destruct x eqn: ?
  end; try int_contra; nia.
Qed.

Lemma real_eq_symm : forall x y, x =| y -> y =| x.
Proof.
  intros. destruct x as [f Hf]. destruct y as [g Hg].
  unfold real_eq in *. unfold real_plus in *. unfold real_plus_inv in *.
  unfold seq_zero in *. intros.
  specialize (H eps H0). destruct H as [N H]. exists N; intros.
  specialize (H n H1). remember (f n) as x; remember (g n) as y.
  revert H; clear; intros.
  eapply rational_lt_wd; try eapply (rational_eq_refl eps); try eapply H.
  assert (x +/ --/ y =/ --/ (y +/ --/ x)). {
    clear. rsymm. rational_rw rational_plus_inv_mul.
    rational_rw rational_dist_front. rsymm.
    rational_rw rational_plus_comm. assert (H := rational_plus_inv_mul y).
    eapply (rational_plus_wd _ _ x) in H. rational_rw H. clear H.
    rational_rw rational_plus_comm; rsymm. rational_rw rational_plus_comm.
    apply -> rational_plus_wd. eapply rational_eq_trans; try (
      rsymm; eapply rational_plus_inv_mul
    ). destruct x as [[[a] | | [a]] b]; unfold rational_plus_inv;
    apply rational_eq_refl.
  } apply rational_abs_wd in H0. rsymm. rational_rw H0.
  remember (y +/ --/ x). clear. destruct r as [[[a] | | [a]] b];
  unfold rational_plus_inv; unfold rational_abs; simpl_int;
  apply rational_eq_refl.
Qed.

Lemma rational_missing_link : forall a b c,
  a +/ --/ c =/ a +/ --/ b +/ (b +/ --/ c).
Proof.
  intros. rsymm. rational_rw rational_plus_assoc.
  apply -> rational_plus_wd. eapply rational_eq_trans; try (
    rsymm; eapply rational_plus_assoc
  ). assert (--/ b +/ b =/ Rational0). {
    clear; unfold Rational0. destruct b as [[[a] | | [a]] b];
    unfold rational_plus in *; unfold rational_plus_inv in *;
    unfold rational_eq; simpl_int; try apply rational_eq_refl; try (
      simpl in *; int_contra
    ); repeat match goal with
    | [ |- context [ if ?x then _ else _ ] ] => destruct x eqn: ?
    end; reflection; simpl_int; trivial; nia.
  } eapply (rational_plus_wd _ _ a) in H; rational_rw rational_plus_comm.
  rational_rw H; clear. destruct a as [[[a] | | [a]] b]; unfold Rational0;
  unfold rational_plus; simpl_int; try (simpl in *; int_contra);
  unfold rational_eq; simpl_int; trivial; try (simpl in *; int_contra);
  simpl_eq; nia.
Qed.

Lemma real_eq_trans : forall x y z, x =| y -> y =| z -> x =| z.
Proof.
  intros. destruct x as [f Hf]; destruct y as [g Hg]; destruct z as [h Hh].
  unfold real_eq in *; unfold real_plus in *; unfold real_plus_inv in *.
  clear Hf Hg Hh; rename H into Hf; rename H0 into Hg.
  unfold seq_zero in *; intros.
  specialize (Hf (RationalHalf */ eps)).
  specialize (Hg (RationalHalf */ eps)).
  assert (RationalHalf */ eps >/ Rational0). {
    revert H; clear; intros.
    destruct eps as [[[a] | | [a]] b]; try (
      unfold rational_gt in H; unfold rational_lt in H; simpl in H;
      destruct_posz; simpl_int; simpl in H; inv H
    ). unfold rational_gt; unfold rational_lt. simpl. trivial.
  } specialize (Hf H0); specialize (Hg H0); clear H0.
  destruct Hf as [N1 Hf]; destruct Hg as [N2 Hg].
  exists (if Nat.leb N1 N2 then N2 else N1); intros.
  assert (Hhalf : RationalHalf */ eps +/ RationalHalf */ eps =/ eps). {
    clear; assert (H := rational_dist_back RationalHalf RationalHalf eps).
    apply rational_eq_symm in H. rational_rw H. clear H.
    destruct eps as [[[a] | | [a]] b]; unfold rational_eq; simpl;
    destruct_posz; simpl_int; try (simpl in *; int_contra); trivial;
    simpl_eq; nia.
  } destruct (Nat.leb N1 N2) eqn: EQ; reflection.
  + eassert (n > N1) by nia. specialize (Hf _ H1); specialize (Hg _ H0).
    clear H0 H1 EQ H.
    assert (FACT := rational_lt_plus _ _ _ _ Hf Hg).
    eapply rational_lt_wd in FACT; try (rsymm; eexact Hhalf);
    try eapply rational_eq_refl.
    assert (FACT2 := rational_le_tri (f n +/ --/ g n) (g n +/ --/ h n)).
    assert (FACT3 := rational_missing_link (f n) (g n) (h n)).
    apply rational_abs_wd in FACT3.
    eapply rational_le_wd in FACT2; try eexact FACT3;
    try eapply rational_eq_refl. apply rational_le_lt in FACT2.
    destruct FACT2.
    - eapply rational_lt_trans; try eassumption.
    - eapply rational_lt_wd; try eassumption. apply rational_eq_refl.
  + eassert (n > N2) by nia. specialize (Hf _ H0); specialize (Hg _ H1).
    clear H0 H1 EQ H.
    assert (FACT := rational_lt_plus _ _ _ _ Hf Hg).
    eapply rational_lt_wd in FACT; try (rsymm; eexact Hhalf);
    try eapply rational_eq_refl.
    assert (FACT2 := rational_le_tri (f n +/ --/ g n) (g n +/ --/ h n)).
    assert (FACT3 := rational_missing_link (f n) (g n) (h n)).
    apply rational_abs_wd in FACT3.
    eapply rational_le_wd in FACT2; try eexact FACT3;
    try eapply rational_eq_refl. apply rational_le_lt in FACT2.
    destruct FACT2.
    - eapply rational_lt_trans; try eassumption.
    - eapply rational_lt_wd; try eassumption. apply rational_eq_refl.
Qed.

Lemma real_plus_wd : forall x y z, x =| y -> x +| z =| y +| z.
Proof.
  intros. destruct x; destruct y; destruct z.
  unfold real_plus; unfold real_eq in *. simpl in *.
  unfold seq_zero in *; intros. specialize (H _ H0). destruct H as [N H].
  exists N. intros. specialize (H _ H1). clear H0 H1.
  eapply rational_lt_wd; try eassumption; try eapply rational_eq_refl.
  clear. apply rational_abs_wd. rational_rw rational_diff_sum.
  remember (f n +/ --/ f0 n) as x; remember (f1 n) as y; clear.
  assert (y +/ --/ y =/ Rational0). {
    clear; destruct y as [[[a] | | [a]] b];
    unfold Rational0; unfold rational_plus; unfold rational_plus_inv;
    unfold rational_eq; destruct_posz; simpl_int; try (
      simpl in *; int_contra
    ); try match goal with
    | [ |- context [ if ?x then _ else _ ] ] => destruct x
    end; trivial; nia.
  } rational_rw rational_plus_comm. eapply rational_plus_wd in H.
  rational_rw H. clear. destruct x as [[[a] | | [a]] b];
  unfold Rational0; unfold rational_plus; unfold rational_plus_inv;
  unfold rational_eq; destruct_posz; simpl_int; try (
    simpl in *; int_contra
  ); try match goal with
  | [ |- context [ if ?x then _ else _ ] ] => destruct x
  end; trivial; simpl_eq; nia.
Qed.

Lemma real_plus_comm : forall x y, x +| y =| y +| x.
Proof.
  intros. destruct x; destruct y.
  unfold real_plus; unfold real_eq. simpl.
  unfold seq_zero; intros. exists 0. intros n _.
  assert (
    rational_abs (f n +/ f0 n +/ --/ (f0 n +/ f n)) =/ Rational0
  ). {
    replace Rational0 with (rational_abs Rational0) by (simpl; eauto).
    apply rational_abs_wd; clear. remember (f n); remember (f0 n); clear.
    assert (F := rational_plus_comm r r0). eapply rational_plus_wd in F.
    rational_rw F. clear. rational_rw rational_diff_sum.
    assert (forall x, x +/ --/ x =/ Rational0). {
      clear; intros. destruct x as [[[a] | | [a]] b];
      unfold rational_plus; unfold rational_plus_inv;
      unfold rational_eq; unfold Rational0; destruct_posz; simpl_int;
      trivial; try match goal with
      | [ |- context [ if ?x then _ else _ ] ] => destruct x eqn: ?
      end; reflection; trivial; nia.
    } assert (Hr0 := H r0). eapply rational_plus_wd in Hr0.
    rational_rw Hr0; clear Hr0. specialize (H r).
    rational_rw rational_plus_comm. eapply rational_plus_wd in H.
    rational_rw H; clear. unfold Rational0; simpl; eauto.
  } eapply rational_lt_wd; try eassumption; try eapply rational_eq_refl.
Qed.

Lemma real_plus_assoc : forall x y z, x +| (y +| z) =| x +| y +| z.
Proof.
  intros. destruct x; destruct y; destruct z.
  unfold real_eq; unfold real_plus; unfold real_plus_inv; simpl.
  clear. unfold seq_zero. intros. exists 0. intros n _.
  eapply rational_lt_wd; try eassumption; try apply rational_eq_refl.
  replace Rational0 with (rational_abs Rational0) by (simpl; eauto).
  apply rational_abs_wd. remember (f n) as x; remember (f0 n) as y;
  remember (f1 n) as z; clear.
  assert (FACT := rational_plus_assoc x y z).
  eapply rational_plus_inv_wd in FACT. eapply rational_plus_wd in FACT.
  rational_rw rational_plus_comm. rsymm. rational_rw FACT. rsymm.
  remember (x +/ (y +/ z)) as w; clear. destruct w as [[[a] | | [a]] b];
  unfold rational_plus; unfold rational_plus_inv; unfold rational_eq;
  unfold Rational0; simpl_int; trivial; try match goal with
  | [ |- context [ if ?x then _ else _ ] ] => destruct x eqn: ?
  end; trivial; nia.
Qed.

Lemma bound_relief : forall x y z,
  rational_abs (x +/ --/ y) </ z -> rational_abs x </ rational_abs y +/ z.
Proof.
  intros. apply rational_abs_elim in H. destruct H.
  eapply (rational_lt_plus_eq _ _ y) in H.
  eapply (rational_lt_plus_eq _ _ y) in H0.
  assert (forall a b c, a <=/ b -> b </ c -> a </ c). {
    clear; intros. apply rational_le_lt in H. destruct H.
    + eapply rational_lt_trans; eauto.
    + eapply rational_lt_wd; try eexact H; try eassumption.
      apply rational_eq_refl.
  } assert (Hltle : forall a b c, a </ b -> b <=/ c -> a </ c). {
    clear; intros. apply rational_le_lt in H0. destruct H0.
    + eapply rational_lt_trans; eauto.
    + eapply rational_lt_wd; try eexact H0; try eassumption;
      try (rsymm; eassumption). apply rational_eq_refl.
  } apply rational_abs_elim; split.
  + assert (--/ z +/ y </ x). {
      apply -> rational_lt_wd; try eexact H; try apply rational_eq_refl.
      rsymm; rational_rw rational_plus_assoc.
      assert (--/y +/ y =/ Rational Zero (P 0)). {
        clear. rational_rw rational_plus_comm. apply rational_pm_zero.
      } eapply rational_plus_wd in H2.
      eapply rational_eq_trans in H2; try eapply rational_plus_comm.
      apply rational_eq_symm in H2; rational_rw H2; clear.
      rsymm; rational_rw rational_plus_comm. apply rational_plus_zero.
    } eapply H1; try eexact H2.
    clear. eapply rational_le_wd; try (
      rational_rw rational_plus_inv_mul; rational_rw rational_dist_front;
      eapply rational_eq_refl; fail
    ); try eapply rational_eq_refl.
    assert (H := rational_plus_inv_mul z). eapply rational_plus_wd in H.
    apply rational_eq_symm in H.
    eapply rational_eq_trans in H; try eapply rational_plus_comm.
    eapply rational_le_wd; try eexact H; try eapply rational_eq_refl.
    clear H. unfold rational_le.
    assert (forall x y,
      x =/ y -> rational_nonnegative x -> rational_nonnegative y
    ). {
      clear; intros. destruct x as [[[a] | | [a]] [b]];
      destruct y as [[[c] | | [c]] [d]]; try (simpl in *; trivial; fail).
      - simpl in H. inv H.
      - simpl in H. inv H.
    } eapply H; try (rsymm; eapply rational_diff_sum).
    assert (forall a b, --/ a +/ --/ b =/ --/ (a +/ b)). {
      clear; intros. rsymm; rational_rw rational_plus_inv_mul.
      rational_rw rational_dist_front.
      assert (--/ a +/ Rational (NegZ (P 0)) (P 0) */ b =/ --/ a +/ --/ b).
      {
        rational_rw rational_plus_comm; rsymm;
        rational_rw rational_plus_comm; apply -> rational_plus_wd.
        apply rational_plus_inv_mul.
      } rational_rw H. apply -> rational_plus_wd. rsymm.
      apply rational_plus_inv_mul.
    } assert (--/ z +/ --/ --/ z =/ Rational Zero (P 0)). {
      rational_rw (H0 z (--/ z)).
      assert (--/ (z +/ --/ z) =/ --/ Rational Zero (P 0)). {
        apply -> rational_plus_inv_wd. apply rational_pm_zero.
      } rational_rw H1; clear. simpl; trivial.
    } eapply rational_plus_wd in H1. eapply H; try (rsymm; eexact H1).
    clear. destruct y as [[[a] | | [a]] [b]];
    unfold rational_plus; unfold rational_plus_inv; unfold rational_mul;
    unfold rational_abs; simpl_int; try (simpl in *; trivial; int_contra);
    destruct (Nat.leb n4 n2) eqn: ?; simpl_int; simpl; trivial;
    reflection; nia.
  + assert (x </ z +/ y). {
      apply -> rational_lt_wd; try eexact H0; try apply rational_eq_refl.
      rsymm; rational_rw rational_plus_assoc.
      assert (--/y +/ y =/ Rational Zero (P 0)). {
        clear. rational_rw rational_plus_comm. apply rational_pm_zero.
      } eapply rational_plus_wd in H2.
      eapply rational_eq_trans in H2; try eapply rational_plus_comm.
      apply rational_eq_symm in H2; rational_rw H2; clear.
      rsymm; rational_rw rational_plus_comm. apply rational_plus_zero.
    } eapply Hltle; try eexact H2. clear.
    assert (forall x y,
      x =/ y -> rational_nonnegative x -> rational_nonnegative y
    ). {
      clear; intros. destruct x as [[[a] | | [a]] [b]];
      destruct y as [[[c] | | [c]] [d]]; try (simpl in *; trivial; fail).
      - simpl in H. inv H.
      - simpl in H. inv H.
    } assert (H0 := rational_plus_comm z (rational_abs y)).
    eapply rational_plus_wd in H0; eapply H; try eexact H0.
    eapply H; try (rsymm; eapply rational_diff_sum). clear H0.
    assert (H0 := rational_pm_zero z). eapply rational_plus_wd in H0;
    eapply H; try (rsymm; eapply H0). clear.
    destruct y as [[[a] | | [a]] [b]];
    unfold rational_plus; unfold rational_plus_inv; unfold rational_mul;
    unfold rational_abs; simpl_int; try (simpl in *; trivial; int_contra);
    destruct (Nat.leb n1 n1) eqn: ?; simpl_int; simpl; trivial;
    reflection; nia.
Qed.

Lemma cauchy_bounded : forall f, cauchy f ->
  exists M, forall n, rational_abs (f n) </ Rational (PosZ (P M)) (P 0).
Proof.
  intros. destruct (H RationalHalf) as [N HN]; try (
    unfold RationalHalf; unfold Rational0; unfold rational_gt;
    unfold rational_lt; simpl; trivial; fail
  ). destruct (
    rational_finite_maximum (fun n => rational_abs (f n)) N
  ) as [M1 HM1]. destruct (rational_archimedean (
    rational_abs (f (S N)) +/ RationalHalf
  )) as [M2 HM2].
  destruct (Nat.leb M1 M2) eqn: EQ; eexists; intros;
  destruct (Nat.leb n N) eqn: EQ2; reflection.
  + inversion EQ; try (subst M1; apply HM1; eassumption).
    eassert (M1 < M2) by nia. rewrite H1. clear EQ H1 H0 m.
    eapply rational_lt_trans; try (eapply HM1; eassumption).
    unfold rational_lt; simpl.
    replace (Nat.leb (M1 * 1) (M2 * 1)) with true by (
      symmetry; apply leb_refl; nia
    ). simpl_int; trivial. nia.
  + specialize (HN n (S N) EQ2 (le_n (S N))). apply bound_relief in HN.
    eapply rational_lt_trans; try eexact HM2.
    assert (forall a b c, a <=/ b -> b </ c -> a </ c). {
      clear; intros. apply rational_le_lt in H. destruct H.
      - eapply rational_lt_trans; eauto.
      - eapply rational_lt_wd; try eexact H; try eassumption.
        apply rational_eq_refl.
    } eapply H0; try eexact HN; clear H0.
    remember (f n) as x; clear. destruct x as [[[a] | | [a]] [b]];
    unfold rational_le; unfold rational_plus; unfold rational_plus_inv;
    destruct_posz; simpl_int; simpl; trivial; remember (b + a * S b);
    destruct (Nat.leb n n) eqn: EQ; reflection; try nia;
    replace (n - n) with 0 by nia; trivial.
  + apply HM1; assumption.
  + specialize (HN n (S N) EQ2 (le_n (S N))). apply bound_relief in HN.
    assert (forall x, x <=/ rational_abs x). {
      clear; intros. destruct x as [[[a] | | [a]] [b]];
      unfold rational_le; unfold rational_plus; unfold rational_plus_inv;
      destruct_posz; simpl_int; simpl; trivial. remember (b + a * S b).
      destruct (Nat.leb n n) eqn: EQ; reflection; try nia.
      replace (n - n) with 0 by nia; trivial.
    } specialize (H0 (f n)).
    eapply rational_lt_trans; try eexact HN.
    eapply rational_lt_trans; try eexact HM2.
    unfold rational_lt; simpl.
    eassert (HH : forall x, x * 1 = x) by (intros; nia);
    repeat rewrite HH; clear HH.
    destruct (Nat.leb M2 M1) eqn: ?; reflection; try nia.
    destruct (M1 - M2) eqn: ?; try nia.
Qed.

Lemma cauchy_mul : forall f g,
  cauchy f -> cauchy g -> cauchy (fun n => f n */ g n).
Proof.
  intros f g Hf Hg. destruct (cauchy_bounded _ Hf) as [M1 HM1].
  destruct (cauchy_bounded _ Hg) as [M2 HM2]. unfold cauchy; intros.
  assert (forall M,
    eps */ RationalHalf */ Rational (PosZ (P 0)) (P M) >/ Rational0
  ). {
    revert H; clear; intros. unfold RationalHalf; unfold Rational0 in *;
    unfold rational_gt in *; unfold rational_lt in *;
    unfold rational_mul in *; unfold rational_plus in *;
    unfold rational_plus_inv in *; destruct eps as [[[a] | | [a]] [b]];
    simpl_int; try (simpl in *; trivial; int_contra).
  } specialize (Hf _ (H0 M2)). specialize (Hg _ (H0 M1)).
  destruct Hf as [N1 HN1]; destruct Hg as [N2 HN2].
  exists (if Nat.leb N1 N2 then N2 else N1).
  assert (forall M,
    eps */ RationalHalf */ Rational (PosZ (P 0)) (P M)
    */ Rational (PosZ (P M)) (P 0) =/ eps */ RationalHalf
  ). {
    clear; intros. unfold RationalHalf; unfold Rational0 in *;
    unfold rational_gt in *; unfold rational_lt in *;
    unfold rational_mul in *; unfold rational_plus in *;
    unfold rational_plus_inv in *; destruct eps as [[[a] | | [a]] [b]];
    destruct_posz; simpl_int; try (simpl in *; trivial; int_contra);
    unfold rational_eq; simpl_int; try (simpl in *; trivial; int_contra);
    simpl_eq; eassert (S n8 = S n9 -> n8 = n9) by (
      clear; intros H; inv H; eauto
    ); apply H; clear H; repeat match goal with
    | [ H : context [ S ?x ] |- _ ] => remember (S x); match goal with
      | H : _ = S x |- _ => clear H
      end
    end; subst; nia.
  } assert (Hlelt : forall a b c, a <=/ b -> b </ c -> a </ c). {
    clear; intros. apply rational_le_lt in H. destruct H.
    + eapply rational_lt_trans; eauto.
    + eapply rational_lt_wd; try eexact H; try eassumption.
      apply rational_eq_refl.
  } assert (Habsle : forall x, Rational Zero (P 0) <=/ rational_abs x). {
    clear; intros. destruct x as [[[a] | | [a]] [b]]; unfold rational_abs;
    apply rational_le_lt; try (
      left; apply rational_lt_pos; simpl; eauto; fail
    ); right. unfold rational_eq; simpl. eauto.
  } destruct (Nat.leb N1 N2) eqn: EQ; reflection.
  + intros. eassert (n > N1) by nia; eassert (m > N1) by nia.
    specialize (HN1 _ _ H4 H5); specialize (HN2 _ _ H2 H3).
    clear H2 H3 H4 H5 EQ.
    assert (H2 :=
      rational_missing_link (f n */ g n) (f n */ g m) (f m */ g m)
    ). assert (eps =/ eps */ RationalHalf +/ eps */ RationalHalf). {
      clear. rational_rw rational_dist_front.
      destruct eps as [[[a] | | [a]] [b]]; unfold rational_eq;
      unfold RationalHalf; unfold rational_mul; unfold rational_plus;
      simpl_int; try (simpl in *; trivial; int_contra); simpl_eq; nia.
    } eapply rational_lt_wd; try eexact H3;
    try eexact (rational_abs_wd _ _ H2). clear H2 H3.
    eapply Hlelt; try eapply rational_le_tri. apply rational_lt_plus.
    - assert (f n */ g n +/ --/ (f n */ g m) =/ (g n +/ --/ g m) */ f n). {
        remember (f n) as a; remember (g n) as b; remember (g m) as c; clear.
        rsymm; rational_rw rational_mul_comm.
        rational_rw rational_dist_front.
        rational_rw rational_plus_comm; rsymm.
        rational_rw rational_plus_comm; apply -> rational_plus_wd.
        rational_rw rational_plus_inv_mul; rational_rw rational_mul_comm.
        assert (H := rational_plus_inv_mul c). eapply rational_mul_wd in H.
        eapply rational_eq_trans in H; try eapply rational_mul_comm.
        rsymm; rational_rw H. rsymm; eapply rational_eq_trans;
        try (rsymm; eapply rational_mul_assoc).
        rational_rw rational_mul_comm. apply rational_mul_wd.
        apply rational_mul_comm.
      } apply rational_abs_wd in H2.
      eapply rational_lt_wd; try eexact H2; try (rsymm; eapply H1).
      eapply rational_lt_wd; try eapply rational_abs_mul;
      try eapply rational_eq_refl. specialize (HM1 n).
      apply rational_lt_mul_nonneg; try eassumption;
      try apply Habsle.
    - assert (f n */ g m +/ --/ (f m */ g m) =/ (f n +/ --/ f m) */ g m). {
        remember (f n) as a; remember (f m) as b; remember (g m) as c; clear.
        rsymm; rational_rw rational_dist_back.
        rational_rw rational_plus_comm; rsymm.
        rational_rw rational_plus_comm; apply -> rational_plus_wd.
        rational_rw rational_plus_inv_mul; rational_rw rational_mul_comm.
        assert (H := rational_plus_inv_mul b). eapply rational_mul_wd in H.
        rsymm; rational_rw H. eapply rational_eq_trans;
        try (rsymm; eapply rational_mul_assoc).
        rational_rw rational_mul_comm. apply rational_eq_refl.
      } apply rational_abs_wd in H2.
      eapply rational_lt_wd; try eexact H2; try (rsymm; eapply H1).
      eapply rational_lt_wd; try eapply rational_abs_mul;
      try eapply rational_eq_refl. specialize (HM2 m).
      apply rational_lt_mul_nonneg; try eassumption;
      try apply Habsle.
  + intros. eassert (n > N2) by nia; eassert (m > N2) by nia.
    specialize (HN2 _ _ H4 H5); specialize (HN1 _ _ H2 H3).
    clear H2 H3 H4 H5 EQ.
    assert (H2 :=
      rational_missing_link (f n */ g n) (f n */ g m) (f m */ g m)
    ). assert (eps =/ eps */ RationalHalf +/ eps */ RationalHalf). {
      clear. rational_rw rational_dist_front.
      destruct eps as [[[a] | | [a]] [b]]; unfold rational_eq;
      unfold RationalHalf; unfold rational_mul; unfold rational_plus;
      simpl_int; try (simpl in *; trivial; int_contra); simpl_eq; nia.
    } eapply rational_lt_wd; try eexact H3;
    try eexact (rational_abs_wd _ _ H2). clear H2 H3.
    eapply Hlelt; try eapply rational_le_tri. apply rational_lt_plus.
    - assert (f n */ g n +/ --/ (f n */ g m) =/ (g n +/ --/ g m) */ f n). {
        remember (f n) as a; remember (g n) as b; remember (g m) as c; clear.
        rsymm; rational_rw rational_mul_comm.
        rational_rw rational_dist_front.
        rational_rw rational_plus_comm; rsymm.
        rational_rw rational_plus_comm; apply -> rational_plus_wd.
        rational_rw rational_plus_inv_mul; rational_rw rational_mul_comm.
        assert (H := rational_plus_inv_mul c). eapply rational_mul_wd in H.
        eapply rational_eq_trans in H; try eapply rational_mul_comm.
        rsymm; rational_rw H. rsymm; eapply rational_eq_trans;
        try (rsymm; eapply rational_mul_assoc).
        rational_rw rational_mul_comm. apply rational_mul_wd.
        apply rational_mul_comm.
      } apply rational_abs_wd in H2.
      eapply rational_lt_wd; try eexact H2; try (rsymm; eapply H1).
      eapply rational_lt_wd; try eapply rational_abs_mul;
      try eapply rational_eq_refl. specialize (HM1 n).
      apply rational_lt_mul_nonneg; try eassumption;
      try apply Habsle.
    - assert (f n */ g m +/ --/ (f m */ g m) =/ (f n +/ --/ f m) */ g m). {
        remember (f n) as a; remember (f m) as b; remember (g m) as c; clear.
        rsymm; rational_rw rational_dist_back.
        rational_rw rational_plus_comm; rsymm.
        rational_rw rational_plus_comm; apply -> rational_plus_wd.
        rational_rw rational_plus_inv_mul; rational_rw rational_mul_comm.
        assert (H := rational_plus_inv_mul b). eapply rational_mul_wd in H.
        rsymm; rational_rw H. eapply rational_eq_trans;
        try (rsymm; eapply rational_mul_assoc).
        rational_rw rational_mul_comm. apply rational_eq_refl.
      } apply rational_abs_wd in H2.
      eapply rational_lt_wd; try eexact H2; try (rsymm; eapply H1).
      eapply rational_lt_wd; try eapply rational_abs_mul;
      try eapply rational_eq_refl. specialize (HM2 m).
      apply rational_lt_mul_nonneg; try eassumption;
      try apply Habsle.
Qed.

Definition real_mul (x : real) (y : real) :=
  match x, y with
  | Real f Hf, Real g Hg =>
    Real (fun n => f n */ g n) (cauchy_mul f g Hf Hg)
  end
.

Notation "x *| y" := (real_mul x y) (at level 40, left associativity).

Lemma real_mul_comm : forall x y, x *| y =| y *| x.
Proof.
  intros [f Hf] [g Hg]; unfold real_mul; unfold real_eq;
  unfold real_plus; unfold real_plus_inv. unfold seq_zero; intros.
  exists 0; intros n _. eapply rational_lt_wd; try eexact H;
  try eapply rational_eq_refl. clear.
  assert (H := rational_mul_comm (f n) (g n)).
  eapply rational_plus_wd in H. eapply rational_abs_wd in H.
  rational_rw H. remember (g n */ f n) as x; clear.
  destruct x as [[[a] | | [a]] [b]]; unfold rational_plus;
  unfold rational_plus_inv; unfold Rational0; unfold rational_eq;
  unfold rational_abs; simpl_int; trivial; destruct (Nat.leb n0 n0) eqn: ?;
  reflection; trivial; simpl; nia.
Qed.

Lemma real_mul_assoc : forall x y z, x *| (y *| z) =| x *| y *| z.
Proof.
  intros [f Hf] [g Hg] [h Hh]; unfold real_mul; unfold real_eq;
  unfold real_plus; unfold real_plus_inv. unfold seq_zero; intros.
  exists 0; intros n _. eapply rational_lt_wd; try eexact H;
  try eapply rational_eq_refl. clear.
  assert (H := rational_mul_assoc (f n) (g n) (h n)).
  eapply rational_plus_wd in H. eapply rational_abs_wd in H.
  rational_rw H. remember (f n */ g n */ h n) as x; clear.
  destruct x as [[[a] | | [a]] [b]]; unfold rational_plus;
  unfold rational_plus_inv; unfold Rational0; unfold rational_eq;
  unfold rational_abs; simpl_int; trivial; destruct (Nat.leb n0 n0) eqn: ?;
  reflection; trivial; simpl; nia.
Qed.

Lemma real_dist_front : forall x y z, x *| (y +| z) =| x *| y +| x *| z.
Proof.
  intros [f Hf] [g Hg] [h Hh]; unfold real_mul; unfold real_eq;
  unfold real_plus; unfold real_plus_inv. unfold seq_zero; intros.
  exists 0; intros n _. eapply rational_lt_wd; try eexact H;
  try eapply rational_eq_refl. clear.
  assert (H := rational_dist_front (f n) (g n) (h n)).
  eapply rational_plus_wd in H. eapply rational_abs_wd in H.
  rational_rw H. remember (f n */ g n +/ f n */ h n) as x; clear.
  destruct x as [[[a] | | [a]] [b]]; unfold rational_plus;
  unfold rational_plus_inv; unfold Rational0; unfold rational_eq;
  unfold rational_abs; simpl_int; trivial; destruct (Nat.leb n0 n0) eqn: ?;
  reflection; trivial; simpl; nia.
Qed.

Lemma real_dist_back : forall x y z, (x +| y) *| z =| (x *| z) +| (y *| z).
Proof.
  intros [f Hf] [g Hg] [h Hh]; unfold real_mul; unfold real_eq;
  unfold real_plus; unfold real_plus_inv. unfold seq_zero; intros.
  exists 0; intros n _. eapply rational_lt_wd; try eexact H;
  try eapply rational_eq_refl. clear.
  assert (H := rational_dist_back (f n) (g n) (h n)).
  eapply rational_plus_wd in H. eapply rational_abs_wd in H.
  rational_rw H. remember (f n */ h n +/ g n */ h n) as x; clear.
  destruct x as [[[a] | | [a]] [b]]; unfold rational_plus;
  unfold rational_plus_inv; unfold Rational0; unfold rational_eq;
  unfold rational_abs; simpl_int; trivial; destruct (Nat.leb n0 n0) eqn: ?;
  reflection; trivial; simpl; nia.
Qed.
