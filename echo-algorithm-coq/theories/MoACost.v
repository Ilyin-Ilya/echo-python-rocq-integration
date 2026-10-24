(** * Structured execution costs and dimension lifting

    Definitions 24--26 of the source do not specify enough graph structure for
    their induction: edge costs disappear from Definition 25 and "shortening a
    sequential chain" does not relate transformed subgraphs.  Here execution
    structure is explicit and dimension lifting is a structural relation.
    [Work c] may represent either an instruction or a transfer, so both kinds
    of cost participate in evaluation. *)

From Stdlib Require Import List Arith Lia PeanoNat.
Import ListNotations.

Module MoACost.

Inductive execution (C : Type) : Type :=
| Done : execution C
| Work : C -> execution C
| Sequential : execution C -> execution C -> execution C
| Parallel : execution C -> execution C -> execution C.

Arguments Done {C}.
Arguments Work {C} _.
Arguments Sequential {C} _ _.
Arguments Parallel {C} _ _.

Section Costs.
  Context {C : Type}.
  Variable zero : C.
  Variable seq_cost par_cost : C -> C -> C.

  Fixpoint cost (e : execution C) : C :=
    match e with
    | Done => zero
    | Work c => c
    | Sequential x y => seq_cost (cost x) (cost y)
    | Parallel x y => par_cost (cost x) (cost y)
    end.

  Variable leC : C -> C -> Prop.

  Hypothesis leC_refl : forall x, leC x x.
  Hypothesis leC_trans : forall x y z, leC x y -> leC y z -> leC x z.
  Hypothesis seq_cost_mono : forall x x' y y',
      leC x x' -> leC y y' ->
      leC (seq_cost x y) (seq_cost x' y').
  Hypothesis par_cost_mono : forall x x' y y',
      leC x x' -> leC y y' ->
      leC (par_cost x y) (par_cost x' y').
  Hypothesis parallel_no_slower : forall x y,
      leC (par_cost x y) (seq_cost x y).

  Variable independent : execution C -> execution C -> Prop.

  (** [dimension_lifting source target] records exactly which sequential
      composition becomes parallel.  The independence premise is the semantic
      side condition omitted by a cost-only account. *)
  Inductive dimension_lifting : execution C -> execution C -> Prop :=
  | lift_refl : forall e,
      dimension_lifting e e
  | lift_sequential : forall x x' y y',
      dimension_lifting x x' ->
      dimension_lifting y y' ->
      dimension_lifting (Sequential x y) (Sequential x' y')
  | lift_parallel : forall x x' y y',
      dimension_lifting x x' ->
      dimension_lifting y y' ->
      dimension_lifting (Parallel x y) (Parallel x' y')
  | lift_independent : forall x x' y y',
      independent x y ->
      dimension_lifting x x' ->
      dimension_lifting y y' ->
      dimension_lifting (Sequential x y) (Parallel x' y').

  Theorem dimension_lifting_nonincreasing : forall source target,
      dimension_lifting source target ->
      leC (cost target) (cost source).
  Proof.
    intros source target Hlift.
    induction Hlift; simpl.
    - apply leC_refl.
    - now apply seq_cost_mono.
    - now apply par_cost_mono.
    - eapply leC_trans.
      + apply par_cost_mono; eassumption.
      + apply parallel_no_slower.
  Qed.

End Costs.

(** The source's principal instance: sequential costs add and parallel costs
    take the longest branch. *)
Definition nat_cost (e : execution nat) : nat :=
  cost 0 Nat.add Nat.max e.

Lemma nat_add_mono : forall x x' y y',
    x <= x' -> y <= y' -> x + y <= x' + y'.
Proof. lia. Qed.

Lemma nat_max_mono : forall x x' y y',
    x <= x' -> y <= y' -> Nat.max x y <= Nat.max x' y'.
Proof.
  intros. apply Nat.max_le_compat; assumption.
Qed.

Lemma nat_parallel_no_slower : forall x y,
    Nat.max x y <= x + y.
Proof.
  intros x y. apply Nat.max_lub; lia.
Qed.

Section NatLifting.
  Variable independent : execution nat -> execution nat -> Prop.

  Corollary nat_dimension_lifting_nonincreasing : forall source target,
      dimension_lifting independent source target ->
      nat_cost target <= nat_cost source.
  Proof.
    intros source target H.
    unfold nat_cost.
    exact (@dimension_lifting_nonincreasing
             nat 0 Nat.add Nat.max le
             Nat.le_refl Nat.le_trans nat_add_mono nat_max_mono
             nat_parallel_no_slower independent source target H).
  Qed.
End NatLifting.

(** Table 1, kept symbolic in the transfer cost [t]. *)
Definition seq4_cost (t : nat) : nat := 9 * t + 32.
Definition par4_cost (t : nat) : nat := 6 * t + 16.
Definition parseq22_cost (t : nat) : nat := 5 * t + 16.

Theorem table1_parseq_le_par : forall t,
    parseq22_cost t <= par4_cost t.
Proof. unfold parseq22_cost, par4_cost; lia. Qed.

Theorem table1_par_lt_seq : forall t,
    1 <= t -> par4_cost t < seq4_cost t.
Proof. unfold par4_cost, seq4_cost; lia. Qed.

Theorem table1_parseq_lt_seq : forall t,
    1 <= t -> parseq22_cost t < seq4_cost t.
Proof. unfold parseq22_cost, seq4_cost; lia. Qed.

End MoACost.
