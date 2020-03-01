Require Export Lia.

Lemma nat_plus_comm : forall x y, x + y = y + x.
Proof.
  intros; nia.
Qed.

Lemma nat_plus_assoc : forall x y z, x + (y + z) = x + y + z.
Proof.
  intros; nia.
Qed.

Lemma nat_mul_comm : forall x y, x * y = y * x.
Proof.
  intros; nia.
Qed.

Lemma nat_mul_assoc : forall x y z, x * (y * z) = x * y * z.
Proof.
  intros; nia.
Qed.

Lemma nat_dist_front : forall x y z, x * (y + z) = x * y + x * z.
Proof.
  intros; nia.
Qed.

Lemma nat_dist_back : forall x y z, (x + y) * z = x * z + y * z.
Proof.
  intros; nia.
Qed.

Ltac inv H := inversion H; subst; clear H.
Ltac refl := try reflexivity.