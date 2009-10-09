Require Import Gappa_common.
Require Import List.

Section Array.

Definition index := positive.

Variable A : Type.

Inductive binary_tree : Type :=
  | Empty : binary_tree
  | Missing (left right : binary_tree) : binary_tree
  | Full (val : A) (left right : binary_tree) : binary_tree.

Definition empty := Empty.

Fixpoint get t (n : index) { struct n } :=
  match t, n with
  | Empty, _ => None
  | Missing _ _, xH => None
  | Full v _ _, xH => Some v
  | Missing l _, xO p => get l p
  | Missing _ r, xI p => get r p
  | Full _ l _, xO p => get l p
  | Full _ _ r, xI p => get r p
  end.

Definition set t (n : index) v :=
  let fix aux t n { struct n } :=
    match t, n with
    | Empty, xH => Full v Empty Empty
    | Empty, xO p => Missing (aux Empty p) Empty
    | Empty, xI p => Missing Empty (aux Empty p)
    | Missing l r, xH => Full v l r
    | Missing l r, xO p => Missing (aux l p) r
    | Missing l r, xI p => Missing l (aux r p)
    | Full _ l r, xH => Full v l r
    | Full w l r, xO p => Full w (aux l p) r
    | Full w l r, xI p => Full w l (aux r p)
    end in
  aux t n.

Fixpoint mix0 l :=
  match l with
  | nil => l
  | h :: t => h :: @None A :: mix0 t
  end.

Theorem mix0_even :
  forall n l,
  nth (2 * n) (mix0 l) None = nth n l None.
Proof.
induction n ; intros l.
simpl.
now case l.
rewrite <- mult_n_Sm, plus_comm.
now case l.
Qed.

Theorem mix0_odd :
  forall n l,
  nth (1 + 2 * n) (mix0 l) None = None.
Proof.
induction n ; intros l.
now case l.
rewrite <- mult_n_Sm, <- (plus_comm 2), plus_assoc.
now case l.
Qed.

Fixpoint mix l r :=
  match l, r with
  | nil, nil => l
  | nil, _ => None :: mix0 r
  | _, nil => mix0 l
  | hl :: tl, hr :: tr => hl :: hr :: mix tl tr
  end.

Theorem mix_even :
  forall n l r,
  nth (2 * n) (mix l r) None = nth n l None.
Proof.
induction n ; intros l r.
now case l ; case r.
rewrite <- mult_n_Sm, plus_comm.
destruct l as [|hl ql] ; destruct r as [|hr qr].
apply refl_equal.
exact (mix0_odd n (hr :: qr)).
exact (mix0_even n ql).
exact (IHn ql qr).
Qed.

Theorem mix_odd :
  forall n l r,
  nth (1 + 2 * n) (mix l r) None = nth n r None.
Proof.
induction n ; intros l r.
now case l ; case r.
rewrite <- mult_n_Sm, <- (plus_comm 2), plus_assoc.
destruct l as [|hl ql] ; destruct r as [|hr qr].
apply refl_equal.
exact (mix0_even n qr).
exact (mix0_odd n ql).
exact (IHn ql qr).
Qed.

Fixpoint flatten t :=
  match t with
  | Empty => nil
  | Missing l r => None :: mix (flatten l) (flatten r)
  | Full v l r => Some v :: mix (flatten l) (flatten r)
  end.

Theorem flatten_get_aux :
  forall n t,
  nth (pred (nat_of_P n)) (flatten t) None = get t n.
Proof.
assert (H : forall n, 2 * nat_of_P n = S (S (2 * pred (nat_of_P n)))).
(* . *)
induction n.
rewrite nat_of_P_xI.
simpl. ring.
rewrite nat_of_P_xO.
rewrite IHn.
simpl. ring.
apply refl_equal.
(* . *)
induction n.
rewrite nat_of_P_xI, H.
intros [|l r|v l r].
apply refl_equal.
simpl get.
rewrite <- IHn.
exact (mix_odd (pred (nat_of_P n)) (flatten l) (flatten r)).
simpl get.
rewrite <- IHn.
exact (mix_odd (pred (nat_of_P n)) (flatten l) (flatten r)).
rewrite nat_of_P_xO, H.
intros [|l r|v l r].
apply refl_equal.
simpl get.
rewrite <- IHn.
exact (mix_even (pred (nat_of_P n)) (flatten l) (flatten r)).
simpl get.
rewrite <- IHn.
exact (mix_even (pred (nat_of_P n)) (flatten l) (flatten r)).
now intros [|l r|v l r].
Qed.

Theorem flatten_get :
  forall n t,
  nth n (flatten t) None = get t (P_of_succ_nat n).
Proof.
intros n t.
rewrite <- flatten_get_aux.
apply (f_equal (fun x => nth x (flatten t) None)).
now rewrite nat_of_P_o_P_of_succ_nat_eq_succ.
Qed.

Theorem get_set_same :
  forall v n t,
  get (set t n v) n = Some v.
Proof.
induction n ; intros.
destruct t ; simpl ; apply IHn.
destruct t ; simpl ; apply IHn.
destruct t ; apply refl_equal.
Qed.

Theorem get_set_other :
  forall v n t m, n <> m ->
  get (set t m v) n = get t n.
Proof.
induction n ; intros.
(* . *)
destruct m.
(* .. *)
assert (forall t, get (set t m v) n = get t n).
intros.
apply IHn.
intros H0.
apply H.
exact (f_equal xI H0).
destruct t ; simpl ; try apply H0.
rewrite H0.
now case n.
(* .. *)
destruct t ; trivial.
now case n.
(* .. *)
destruct t ; trivial.
now case n.
(* . *)
destruct m.
(* .. *)
destruct t ; trivial.
now case n.
(* .. *)
assert (forall t, get (set t m v) n = get t n).
intros.
apply IHn.
intros H0.
apply H.
exact (f_equal xO H0).
destruct t ; simpl ; try apply H0.
rewrite H0.
now case n.
(* .. *)
destruct t ; trivial.
now case n.
(* . *)
destruct m.
now destruct t.
now destruct t.
now elim H.
Qed.

(*
Theorem flatten_set_aux :
  forall n t v,
  nth (pred (nat_of_P n)) (flatten (set t n v)) None = Some v.
Proof.
*)

Definition to_list t :=
  fold_left (fun acc h => match h with None => acc | Some v => v :: acc end) (flatten t) nil.

Theorem to_list_get :
  forall t i,
  match get t i with
  | Some v => In v (to_list t)
  | None => True
  end.
Proof.
intros t i.
rewrite <- flatten_get_aux.
unfold to_list.
rewrite <- fold_left_rev_right.
pattern (flatten t) at 1 ; rewrite <- (rev_involutive (flatten t)).
set (n := pred (nat_of_P i)).
induction (rev (flatten t)).
now case n.
destruct (le_or_lt (length (rev l)) n) as [H|H] ; simpl.
(* . *)
rewrite (app_nth2 _ _ _ H).
case (n - length (rev l)).
simpl. destruct a.
now left.
easy.
now intros [|n0].
(* . *)
rewrite (app_nth1 _ _ _ H).
destruct (nth n (rev l) None).
destruct a.
now right.
exact IHl.
exact I.
Qed.

Definition array := binary_tree.

End Array.

Implicit Arguments get.
Implicit Arguments set.
Implicit Arguments flatten.
Implicit Arguments to_list.
Implicit Arguments to_list_get.

Section PropList.

Variable A : Type.
Variable f : A -> Prop.

Inductive prop_list : list A -> Prop :=
  | pNil : prop_list nil
  | pCons e l : f e -> prop_list l -> prop_list (cons e l).

End PropList.

Implicit Arguments prop_list.

Section Gappa_reflection.

Inductive uop := uNeg | uAbs | uSqrt.
Inductive bop := bAdd | bSub | bMul | bDiv.

Inductive expression :=
  | eVar : index -> expression
  | eUnary : uop -> index -> expression
  | eBinary : bop -> index -> index -> expression.

Inductive property :=
  | pFalse : property
  | pBND : index -> index -> index -> property.

Variable depth : nat.
Variable variables : array R.
Variable expressions : array expression.
Variable floats : array float2.
Variable properties : array property.

Definition interp_float f :=
  match get floats f with
  | Some f => f
  | None => Float2 0 0
  end.

Fixpoint interp_expr_ n e { struct n } :=
  match get expressions e, n with
  | Some e, S n =>
    match e with
    | eVar i => match get variables i with None => R0 | Some x => x end
    | eUnary o i =>
      match o with uNeg => Ropp | uAbs => Rabs | uSqrt => sqrt end
      (interp_expr_ n i)
    | eBinary o i1 i2 =>
      match o with bAdd => Rplus | bSub => Rminus | bMul => Rmult | bDiv => Rdiv end
      (interp_expr_ n i1) (interp_expr_ n i2)
    end
  | _, _ => R0
  end.

Definition interp_expr := interp_expr_ depth.

Definition interp_prop_ p :=
  match p with
  | pFalse => False
  | pBND l e u => BND (interp_expr e) (makepairF (interp_float l) (interp_float u))
  end.

Definition interp_prop p :=
  match get properties p with
  | Some p => interp_prop_ p
  | None => True
  end.

Definition good_env env :=
  prop_list interp_prop (to_list env).

Theorem get_env_spec :
  forall env,
  good_env env ->
  forall i,
  match get env i with
  | Some p => interp_prop p
  | None => True
  end.
Proof.
intros env Henv i.
unfold good_env in Henv.
generalize (to_list_get env i).
destruct (get env i) ; trivial.
induction (to_list env).
easy.
inversion_clear Henv.
simpl.
intros [H1|H1].
now rewrite <- H1.
now apply IHl.
Qed.

Theorem set_env_spec :
  forall env,
  good_env env ->
  forall i p,
  interp_prop p ->
  good_env (set env i p).
Proof.
intros env Henv i p Hp.
unfold good_env.
assert (forall env,
  (forall n, match nth n (flatten env) None with None => True | Some i => interp_prop i end) <->
  prop_list interp_prop (to_list env)).
(* . *)
clear.
intros env.
admit.
(* . *)
apply -> H.
intros n.
rewrite flatten_get.
destruct (positive_eq_dec i (P_of_succ_nat n)) as [Heq|Heq].
rewrite <- Heq.
now rewrite get_set_same.
rewrite get_set_other.
rewrite <- flatten_get.
apply <- H.
apply Henv.
now apply sym_not_eq.
Qed.

Inductive theorem :=
  | Th (f : list property -> property -> bool) :
    (forall l p, prop_list interp_prop_ l -> f l p = true -> interp_prop_ p) -> theorem.

Variable theorems : array theorem.

Inductive step :=
  | sTheorem : index -> list index -> step
  | sUnion : index -> list (index * steps * index) -> step
with steps :=
  | sNil : steps
  | sCons : step -> index -> index -> steps -> steps.

Definition get_hyps env l :=
  fold_left (fun acc h =>
    match get env h with
    | Some h =>
      match get properties h with
      | Some h => h :: acc
      | None => acc
      end
    | _ => acc
    end) l nil.

Theorem get_hyps_spec :
  forall env l,
  good_env env ->
  prop_list interp_prop_ (get_hyps env l).
Proof.
intros env l Henv.
generalize (get_env_spec _ Henv).
unfold interp_prop.
clear Henv. intros Henv.
unfold get_hyps.
rewrite <- fold_left_rev_right.
induction (rev l) as [|h t IH] ; clear l.
apply pNil.
simpl.
generalize (Henv h).
destruct (get env h) as [h1|]. 2: easy.
destruct (get properties h1) as [h2|]. 2: easy.
intros.
now apply pCons.
Qed.

Fixpoint perform env proof { struct proof } :=
  match proof with
  | sNil => env
  | sCons s p res proof =>
    perform
      match s with
      | sTheorem t h =>
        match get theorems t, get properties p with
        | Some (Th f _), Some p' =>
          if f (get_hyps env h) p' then set env res p else env
        | _, _ => env
        end
      | sUnion bnd proofs => 
        match get env bnd with
        | Some bnd =>
          match get properties bnd with
          | Some (pBND l e u) => env
          | _ => env
          end
        | None => env
        end
      end proof
  end.

Theorem perform_spec :
  forall proof env,
  good_env env ->
  good_env (perform env proof).
Proof.
induction proof ; intros env Henv.
exact Henv.
apply IHproof.
destruct s ; simpl.
(* . *)
destruct (get theorems i1) as [(f, Hf)|]. 2: easy.
case_eq (get properties i). 2: easy.
intros p Hp.
generalize (Hf _ p (get_hyps_spec _ l Henv)).
case (f (get_hyps env l) p). 2: easy.
intros H.
specialize (H (refl_equal _)).
apply set_env_spec.
apply Henv.
unfold interp_prop.
now rewrite Hp.
(* . *)
admit.
Qed.

End Gappa_reflection.