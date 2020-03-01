Require Export predicate.

Lemma eqb_refl : forall n m, n = m <-> Nat.eqb n m = true.
Proof.
  intros; split; revert m; induction n; induction m; intros; eauto.
  + inversion H.
  + inversion H.
Qed.

Lemma eqb_frefl : forall n m, ~n = m <-> Nat.eqb n m = false.
Proof.
  intros; split; intros.
  + destruct (Nat.eqb n m) eqn: EQ; refl.
    apply eqb_refl in EQ. destruct (H EQ).
  + intro Hc. subst. eassert (T : m = m) by refl; apply eqb_refl in T.
    rewrite T in H; inv H.
Qed.

Lemma leb_refl : forall n m, n <= m <-> Nat.leb n m = true.
Proof.
  intros; split; revert m; induction n; induction m; intros; eauto.
  + inversion H.
  + simpl. apply IHn. nia.
  + inversion H.
  + specialize (IHn _ H). nia.
Qed.

Lemma leb_frefl : forall n m, n > m <-> Nat.leb n m = false.
Proof.
  intros; split; intros.
  + destruct (Nat.leb n m) eqn: EQ; try reflexivity.
    apply leb_refl in EQ; nia.
  + eassert (~(n <= m) -> n > m) by nia. apply H0; clear H0.
    intro Hc; apply leb_refl in Hc; rewrite H in Hc; inversion Hc.
Qed.

Lemma ltb_refl : forall n m, n < m <-> Nat.ltb n m = true.
Proof.
  intros; split; revert m; induction n; induction m; intros; simpl; try lia.
  + eauto.
  + unfold Nat.ltb in *. remember (S n) as Sn; simpl; subst Sn. apply IHn.
    nia.
  + inv H.
  + inv H.
  + unfold Nat.ltb in *.
    eassert (D : n < m -> S n < S m) by nia; apply D; clear D.
    apply IHn; assumption.
Qed.

Lemma ltb_frefl : forall n m, n >= m <-> Nat.ltb n m = false.
Proof.
  intros; split; intros.
  + destruct (Nat.ltb n m) eqn: EQ; refl. apply ltb_refl in EQ. nia.
  + eassert (D : ~n < m -> n >= m) by nia; apply D; clear D.
    intro Hc. apply ltb_refl in Hc. rewrite Hc in H; inv H.
Qed.

Lemma minus_le : forall n m, n - m = 0 <-> n <= m.
Proof.
  induction n; induction m; split; intros; eauto; try nia.
Qed.

Ltac reflection :=
  repeat match goal with
  | H : Nat.eqb _ _ = true |- _ => apply eqb_refl in H
  | H : Nat.eqb _ _ = false |- _ => apply eqb_frefl in H
  | H : Nat.leb _ _ = true |- _ => apply leb_refl in H
  | H : Nat.leb _ _ = false |- _ => apply leb_frefl in H
  | H : Nat.ltb _ _ = true |- _ => apply ltb_refl in H
  | H : Nat.ltb _ _ = false |- _ => apply ltb_frefl in H
  | H : _ - _ = 0 |- _ => apply minus_le in H
  end
.