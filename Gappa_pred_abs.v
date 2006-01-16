Require Import AllFloat.
Require Import Gappa_common.

Section Gappa_pred_abs.

Definition mul_aa_helper (xi yi zi : FF) :=
 Fpos0 (lower zi) &&
 Fle_b (lower zi) (Fmult (lower xi) (lower yi)) &&
 Fle_b (Fmult (upper xi) (upper yi)) (upper zi).

Theorem mul_aa :
 forall x y : R, forall xi yi zi : FF,
 ABS x xi -> ABS y yi ->
 mul_aa_helper xi yi zi = true ->
 ABS (x * y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (H1,H2).
generalize (Fpos0_correct _ H1). clear H1. intro H1.
generalize (Fle_b_correct _ _ H2). rewrite Fmult_correct with (1 := radixNotZero). clear H2. intro H2.
generalize (Fle_b_correct _ _ H3). rewrite Fmult_correct with (1 := radixNotZero). clear H3. intro H3.
unfold ABS, bndR in *.
split.
exact H1.
rewrite Rabs_mult.
apply ImultR_pp with (lower xi) (upper xi) (lower yi) (upper yi)
 ; intuition.
Qed.

Definition div_aa_helper (xi yi zi : FF) :=
 Fpos (lower yi) &&
 Fpos0 (lower zi) &&
 Fle_b (Fmult (upper yi) (lower zi)) (lower xi) &&
 Fle_b (upper xi) (Fmult (lower yi) (upper zi)).

Theorem div_aa :
 forall x y : R, forall xi yi zi : FF,
 ABS x xi -> ABS y yi ->
 div_aa_helper xi yi zi = true ->
 ABS (x / y) zi.
intros x y xi yi zi Hx Hy Hb.
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H4).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H3).
generalize (andb_prop _ _ Hb). clear Hb. intros (Hb,H2).
generalize (Fpos_correct _ Hb). intro H1.
generalize (Fpos0_correct _ H2). clear H2. intro H2.
generalize (Fle_b_correct _ _ H3). rewrite Fmult_correct with (1 := radixNotZero). clear H3. intro H3.
generalize (Fle_b_correct _ _ H4). rewrite Fmult_correct with (1 := radixNotZero). clear H4. intro H4.
split.
exact H2.
replace (Rabs (x / y)) with (Rabs x / Rabs y)%R.
unfold ABS, bndR in *.
apply IdivR_pp with (lower xi) (upper xi) (lower yi) (upper yi)
 ; intuition.
unfold Rdiv.
rewrite Rabs_mult.
rewrite Rabs_Rinv.
apply refl_equal.
apply abs_not_zero_correct with (1 := Hy) (2 := Hb).
Qed.

End Gappa_pred_abs.