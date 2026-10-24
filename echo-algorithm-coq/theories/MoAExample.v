(** * Executable examples for the MoA formalization *)

From Stdlib Require Import List Arith.
Import ListNotations.
Require Import MoAArray MoAReduction MoACost.

Import MoAArray.MoAArray.
Import MoAReduction.MoAReduction.
Import MoACost.MoACost.

Definition matrix_2x3 : array nat.
Proof.
  refine (mkArray nat [2; 3] [1; 2; 3; 4; 5; 6] _).
  reflexivity.
Defined.

Example matrix_2x3_shape : arr_shape matrix_2x3 = [2; 3].
Proof. reflexivity. Qed.

Example matrix_2x3_last_offset : gamma [1; 2] [2; 3] = 5.
Proof. reflexivity. Qed.

Example matrix_2x3_last_lookup :
    flat_get matrix_2x3 [1; 2] = Some 6.
Proof. reflexivity. Qed.

Example matrix_2x3_ravel_lookup :
    flat_get (ravel matrix_2x3) [5] = Some 6.
Proof. reflexivity. Qed.

Example split_four_term_sum :
    reduce Nat.add 0 [1; 2; 3; 4] =
      Nat.add (reduce Nat.add 0 (firstn 2 [1; 2; 3; 4]))
              (reduce Nat.add 0 (skipn 2 [1; 2; 3; 4])).
Proof. reflexivity. Qed.

Definition independent_example (_ _ : execution nat) : Prop := True.
Definition two_sequential : execution nat :=
  Sequential (Work 8) (Work 8).
Definition two_parallel : execution nat :=
  Parallel (Work 8) (Work 8).

Lemma two_work_items_lift :
    dimension_lifting independent_example two_sequential two_parallel.
Proof.
  apply lift_independent.
  - exact I.
  - apply lift_refl.
  - apply lift_refl.
Qed.

Example two_sequential_cost : nat_cost two_sequential = 16.
Proof. reflexivity. Qed.

Example two_parallel_cost : nat_cost two_parallel = 8.
Proof. reflexivity. Qed.

Example lifted_example_nonincreasing :
    nat_cost two_parallel <= nat_cost two_sequential.
Proof.
  apply nat_dimension_lifting_nonincreasing with
      (independent := independent_example).
  exact two_work_items_lift.
Qed.
