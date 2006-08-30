Require Import Gappa_common.
Require Import Gappa_round.

Section Gappa_proxy.

Theorem fix_of_flt_bnd :
 forall x : R, forall xi : FF, forall n : Z, forall p : positive,
 FLT x p -> ABS x xi ->
 Zle_bool (n + Zpos p) (Zpos (digits (pos_of_Z (Fnum (lower xi)))) + Fexp (lower xi))
 && Fpos (lower xi) = true ->
 FIX x n.
Admitted.

Theorem flt_of_fix_bnd :
 forall x : R, forall xi : FF, forall n : Z, forall p : positive,
 FIX x n -> ABS x xi ->
 Zle_bool (Zpos (digits (pos_of_Z (Fnum (upper xi)))) + Fexp (upper xi)) (n + Zpos p) = true ->
 FLT x p.
Admitted.

End Gappa_proxy.
