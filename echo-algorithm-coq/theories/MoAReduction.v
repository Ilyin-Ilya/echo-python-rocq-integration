(** * Corrected splitting law for MoA reduction

    Proposition 4 in the source says [k < delta(v)], although [delta] is the
    dimensionality and is one for every vector.  This module proves the useful
    statement for [k <= length v], corresponding to total size [tau(v)]. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

Module MoAReduction.

Section Reduction.
  Context {A : Type}.
  Variable op : A -> A -> A.
  Variable unit : A.

  Hypothesis op_assoc : forall x y z,
      op x (op y z) = op (op x y) z.
  Hypothesis op_left_unit : forall x, op unit x = x.
  Hypothesis op_right_unit : forall x, op x unit = x.

  Fixpoint reduce (xs : list A) : A :=
    match xs with
    | [] => unit
    | x :: xs' => op x (reduce xs')
    end.

  Lemma reduce_app : forall left right,
      reduce (left ++ right) = op (reduce left) (reduce right).
  Proof.
    induction left as [|x left IH]; intros right; simpl.
    - symmetry. apply op_left_unit.
    - rewrite IH, op_assoc. reflexivity.
  Qed.

  Theorem reduction_split : forall k vector,
      k <= length vector ->
      reduce vector =
        op (reduce (firstn k vector)) (reduce (skipn k vector)).
  Proof.
    intros k vector _.
    rewrite <- reduce_app, firstn_skipn. reflexivity.
  Qed.

  Corollary reduction_split_strict : forall k vector,
      k < length vector ->
      reduce vector =
        op (reduce (firstn k vector)) (reduce (skipn k vector)).
  Proof.
    intros k vector H. apply reduction_split. lia.
  Qed.

End Reduction.

End MoAReduction.
