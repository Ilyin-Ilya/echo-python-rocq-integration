(** * A checked operational core for Mathematics of Arrays

    This module formalizes the shape/content representation from Definitions
    1--2 and the row-major index conversion used in Proposition 2 of Hains and
    Mullin (2026).  Partial source operations are represented by [option] or by
    explicit validity hypotheses. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

Module MoAArray.

Fixpoint shape_size (s : list nat) : nat :=
  match s with
  | [] => 1
  | n :: s' => n * shape_size s'
  end.

Lemma shape_size_app : forall a b,
    shape_size (a ++ b) = shape_size a * shape_size b.
Proof.
  induction a as [|x xs IH]; intros b; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

(** An array is a shape and a row-major content list with the invariant from
    Definition 1.  In particular, an empty shape has size one and represents a
    scalar. *)
Record array (A : Type) : Type := mkArray {
  arr_shape : list nat;
  arr_data : list A;
  arr_wf : length arr_data = shape_size arr_shape
}.

Arguments arr_shape {A} _.
Arguments arr_data {A} _.

Definition dimensionality {A} (x : array A) : nat :=
  length (arr_shape x).

Definition total_size {A} (x : array A) : nat :=
  shape_size (arr_shape x).

Definition scalar {A} (a : A) : array A.
Proof.
  refine (mkArray A [] [a] _); reflexivity.
Defined.

Definition ravel {A} (x : array A) : array A.
Proof.
  refine (mkArray A [shape_size (arr_shape x)] (arr_data x) _).
  simpl. rewrite Nat.mul_1_r. apply arr_wf.
Defined.

(** [gamma i s] is the usual row-major offset
    [sum_a i[a] * product_{b>a} s[b]].  Mismatched tails are assigned zero;
    all theorems that use it require matching index and shape lengths. *)
Fixpoint gamma (index shape : list nat) : nat :=
  match index, shape with
  | i :: index', _ :: shape' =>
      i * shape_size shape' + gamma index' shape'
  | _, _ => 0
  end.

Fixpoint valid_index (index shape : list nat) : Prop :=
  match index, shape with
  | [], [] => True
  | i :: index', n :: shape' => i < n /\ valid_index index' shape'
  | _, _ => False
  end.

Definition flat_get {A} (x : array A) (index : list nat) : option A :=
  if Nat.eqb (length index) (dimensionality x)
  then nth_error (arr_data x) (gamma index (arr_shape x))
  else None.

(** Positive take/drop, the fragment used by the indexing and reduction laws.
    The source additionally overloads these operations with signed suffix
    conventions; those can be layered on top without changing these proofs. *)
Definition take {A} (k : nat) (xs : list A) : list A := firstn k xs.
Definition drop {A} (k : nat) (xs : list A) : list A := skipn k xs.

Lemma take_drop_partition : forall A k (xs : list A),
    take k xs ++ drop k xs = xs.
Proof.
  intros A k xs. apply firstn_skipn.
Qed.

Lemma valid_index_lengths : forall index shape,
    valid_index index shape -> length index = length shape.
Proof.
  induction index as [|i index IH]; destruct shape as [|n shape];
    simpl; intros H; try contradiction; auto.
  destruct H as [_ H]. simpl. now rewrite (IH shape H).
Qed.

Lemma valid_index_tail_size_positive : forall index shape,
    valid_index index shape -> 0 < shape_size shape.
Proof.
  induction index as [|i index IH]; destruct shape as [|n shape];
    simpl; intros H; try contradiction.
  - lia.
  - destruct H as [Hin Htail].
    specialize (IH shape Htail). nia.
Qed.

Theorem gamma_in_bounds : forall index shape,
    valid_index index shape -> gamma index shape < shape_size shape.
Proof.
  induction index as [|i index IH]; destruct shape as [|n shape];
    simpl; intros H; try contradiction.
  - lia.
  - destruct H as [Hin Htail].
    specialize (IH shape Htail).
    pose proof (valid_index_tail_size_positive index shape Htail).
    nia.
Qed.

Theorem flat_get_valid : forall A (x : array A) index,
    valid_index index (arr_shape x) ->
    exists value, flat_get x index = Some value.
Proof.
  intros A x index Hvalid.
  unfold flat_get.
  rewrite (valid_index_lengths _ _ Hvalid), Nat.eqb_refl.
  assert (Hbound : gamma index (arr_shape x) < length (arr_data x)).
  { rewrite arr_wf. now apply gamma_in_bounds. }
  destruct (nth_error (arr_data x) (gamma index (arr_shape x)))
    as [value|] eqn:Hget.
  - now exists value.
  - apply nth_error_None in Hget. lia.
Qed.

(** Ravel preserves every full row-major lookup.  This is the executable core
    of Proposition 2; both sides use the same gamma offset. *)
Theorem ravel_gamma : forall A (x : array A) index,
    length index = dimensionality x ->
    flat_get (ravel x) [gamma index (arr_shape x)] = flat_get x index.
Proof.
  intros A x index Hlen.
  unfold flat_get, dimensionality in *.
  simpl. rewrite Nat.mul_1_r, Nat.add_0_r.
  rewrite Hlen, Nat.eqb_refl. reflexivity.
Qed.

(** Concatenating an index prefix and suffix decomposes the flat offset into
    a block offset and an offset inside that block.  This is the arithmetic
    fact needed by compositional/Psi indexing. *)
Theorem gamma_app : forall i1 s1 i2 s2,
    length i1 = length s1 ->
    length i2 = length s2 ->
    gamma (i1 ++ i2) (s1 ++ s2) =
      gamma i1 s1 * shape_size s2 + gamma i2 s2.
Proof.
  induction i1 as [|i i1 IH]; intros s1 i2 s2 H1 H2.
  - destruct s1; [|discriminate]. simpl. lia.
  - destruct s1 as [|n s1]; [discriminate|].
    simpl in H1. injection H1 as Htail.
    simpl. rewrite shape_size_app, (IH s1 i2 s2 Htail H2).
    nia.
Qed.

End MoAArray.
