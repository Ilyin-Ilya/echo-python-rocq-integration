(** * A complete bounded runner for canonical executable Echo

    A schedule is only a list of [echo_event] values.  It cannot contain or
    install a successor state: every successful state change is computed by
    the canonical [echo_exec] interpreter.  Invalid events are reported at
    the state where they were rejected.

    Completion is observable from canonical state alone.  The initiator must
    have started, have no pending neighbors, and the message store must be
    empty.  In addition, it must either carry the normal finished flag or have
    no configured neighbors.  The latter classifies a singleton immediately
    after successful startup without accepting malformed unfinished states. *)

From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.
Require Import EchoAlgorithm EchoExecutableTypes EchoTransitionIR
  EchoExecutableReachability.

Section EchoRunner.

Variable node : Type.
Variable node_eq : forall (n m : node), {n = m} + {n <> m}.
Variable config : @echo_config node.

Local Notation initiator := (config_initiator config).
Local Notation all_nodes := (config_nodes config).
Local Notation adj := (config_adjacent config).
Local Notation echo_exec := (@echo_exec node node_eq config).
Local Notation EchoStep := (@EchoStep node node_eq config).
Local Notation echo_reachable := (@echo_reachable node node_eq config).

Definition echo_list_emptyb {A : Type} (items : list A) : bool :=
  match items with
  | [] => true
  | _ :: _ => false
  end.

Lemma echo_list_emptyb_true_iff {A : Type} (items : list A) :
  echo_list_emptyb items = true <-> items = [].
Proof. destruct items; simpl; split; congruence. Qed.

Lemma echo_list_emptyb_false_iff {A : Type} (items : list A) :
  echo_list_emptyb items = false <-> items <> [].
Proof. destruct items; simpl; split; congruence. Qed.

(** Protocol completion, including the singleton case. *)
Definition echo_complete (state : @executable_echo_state node) : Prop :=
  started state = true /\
  process_pending (processes state initiator) = [] /\
  message_store state = [] /\
  (process_finished (processes state initiator) = true \/
   nbrs all_nodes adj initiator = []).

Definition echo_completeb (state : @executable_echo_state node) : bool :=
  started state &&
  echo_list_emptyb (process_pending (processes state initiator)) &&
  echo_list_emptyb (message_store state) &&
  (process_finished (processes state initiator) ||
   echo_list_emptyb (nbrs all_nodes adj initiator)).

Theorem echo_completeb_true_iff (state : @executable_echo_state node) :
  echo_completeb state = true <-> echo_complete state.
Proof.
  unfold echo_completeb, echo_complete.
  rewrite !andb_true_iff.
  rewrite orb_true_iff.
  rewrite !echo_list_emptyb_true_iff.
  tauto.
Qed.

(** A started empty-store state that is not complete is a protocol dead end.
    The complete check always takes precedence in [run_schedule]. *)
Definition echo_stuckb (state : @executable_echo_state node) : bool :=
  started state && echo_list_emptyb (message_store state).

Inductive run_outcome : Type :=
  | EchoRunComplete
      (final_state : @executable_echo_state node) (steps : nat)
  | EchoRunStuck
      (final_state : @executable_echo_state node) (steps : nat)
  | EchoRunBounded
      (final_state : @executable_echo_state node) (steps : nat)
  | EchoRunInvalidChoice
      (final_state : @executable_echo_state node) (steps : nat)
      (rejected_event : @echo_event node).

Definition run_outcome_state (outcome : run_outcome) :
    @executable_echo_state node :=
  match outcome with
  | EchoRunComplete state _
  | EchoRunStuck state _
  | EchoRunBounded state _
  | EchoRunInvalidChoice state _ _ => state
  end.

Definition run_outcome_steps (outcome : run_outcome) : nat :=
  match outcome with
  | EchoRunComplete _ steps
  | EchoRunStuck _ steps
  | EchoRunBounded _ steps
  | EchoRunInvalidChoice _ steps _ => steps
  end.

Definition run_outcome_rejected_event
    (outcome : run_outcome) : option (@echo_event node) :=
  match outcome with
  | EchoRunInvalidChoice _ _ event => Some event
  | _ => None
  end.

Definition bump_run_outcome (outcome : run_outcome) : run_outcome :=
  match outcome with
  | EchoRunComplete state steps => EchoRunComplete state (S steps)
  | EchoRunStuck state steps => EchoRunStuck state (S steps)
  | EchoRunBounded state steps => EchoRunBounded state (S steps)
  | EchoRunInvalidChoice state steps event =>
      EchoRunInvalidChoice state (S steps) event
  end.

Lemma bump_run_outcome_state (outcome : run_outcome) :
  run_outcome_state (bump_run_outcome outcome) =
  run_outcome_state outcome.
Proof. now destruct outcome. Qed.

Lemma bump_run_outcome_steps (outcome : run_outcome) :
  run_outcome_steps (bump_run_outcome outcome) =
  S (run_outcome_steps outcome).
Proof. now destruct outcome. Qed.

(** Execute at most [fuel] scheduled events.  A missing schedule entry is a
    finite schedule bound, while an event rejected by [echo_exec] is reported
    separately as an invalid scheduler choice. *)
Fixpoint run_schedule
    (fuel : nat)
    (state : @executable_echo_state node)
    (schedule : list (@echo_event node)) : run_outcome :=
  if echo_completeb state then
    EchoRunComplete state 0
  else if echo_stuckb state then
    EchoRunStuck state 0
  else
    match fuel, schedule with
    | 0, _ => EchoRunBounded state 0
    | S _, [] => EchoRunBounded state 0
    | S remaining, event :: rest =>
        match echo_exec state event with
        | Some successor =>
            bump_run_outcome (run_schedule remaining successor rest)
        | None => EchoRunInvalidChoice state 0 event
        end
    end.

(** Precise terminal meaning of each constructor. *)
Definition run_outcome_classified (outcome : run_outcome) : Prop :=
  match outcome with
  | EchoRunComplete state _ => echo_completeb state = true
  | EchoRunStuck state _ =>
      echo_completeb state = false /\ echo_stuckb state = true
  | EchoRunBounded state _ =>
      echo_completeb state = false /\ echo_stuckb state = false
  | EchoRunInvalidChoice state _ event =>
      echo_completeb state = false /\
      echo_stuckb state = false /\
      echo_exec state event = None
  end.

Lemma bump_run_outcome_classified (outcome : run_outcome) :
  run_outcome_classified outcome ->
  run_outcome_classified (bump_run_outcome outcome).
Proof. now destruct outcome. Qed.

Theorem run_schedule_outcome_classified
    (fuel : nat)
    (state : @executable_echo_state node)
    (schedule : list (@echo_event node)) :
  run_outcome_classified (run_schedule fuel state schedule).
Proof.
  revert state schedule.
  induction fuel as [| fuel IH]; intros state schedule;
    cbn [run_schedule].
  - destruct (echo_completeb state) eqn:Hcomplete; simpl.
    + exact Hcomplete.
    + destruct (echo_stuckb state) eqn:Hstuck; simpl; auto.
  - destruct (echo_completeb state) eqn:Hcomplete; simpl.
    + exact Hcomplete.
    + destruct (echo_stuckb state) eqn:Hstuck; simpl.
      * auto.
      * destruct schedule as [| event rest]; simpl; auto.
        destruct (echo_exec state event) as [successor |] eqn:Hexec;
          simpl; auto.
        now apply bump_run_outcome_classified, IH.
Qed.

(** A runner can only finish in a canonically reachable state.  In the
    recursive case the proof extends reachability with the exact successful
    [echo_exec] equality, viewed definitionally as [EchoStep]. *)
Theorem run_schedule_reachable
    (fuel : nat)
    (state : @executable_echo_state node)
    (schedule : list (@echo_event node)) :
  echo_reachable state ->
  echo_reachable (run_outcome_state (run_schedule fuel state schedule)).
Proof.
  revert state schedule.
  induction fuel as [| fuel IH]; intros state schedule Hreachable;
    cbn [run_schedule].
  - destruct (echo_completeb state); simpl; [exact Hreachable |].
    destruct (echo_stuckb state); simpl; exact Hreachable.
  - destruct (echo_completeb state); simpl; [exact Hreachable |].
    destruct (echo_stuckb state); simpl; [exact Hreachable |].
    destruct schedule as [| event rest]; simpl; [exact Hreachable |].
    destruct (echo_exec state event) as [successor |] eqn:Hexec; simpl.
    + rewrite bump_run_outcome_state.
      apply IH. eapply EchoReachStep; eauto.
    + exact Hreachable.
Qed.

Corollary run_schedule_complete_sound
    (fuel : nat)
    (state final_state : @executable_echo_state node)
    (schedule : list (@echo_event node))
    (steps : nat) :
  run_schedule fuel state schedule = EchoRunComplete final_state steps ->
  echo_complete final_state.
Proof.
  intro Hrun.
  pose proof (run_schedule_outcome_classified fuel state schedule)
    as Hclassified.
  rewrite Hrun in Hclassified. cbn in Hclassified.
  now apply echo_completeb_true_iff.
Qed.

Corollary run_schedule_stuck_sound
    (fuel : nat)
    (state final_state : @executable_echo_state node)
    (schedule : list (@echo_event node))
    (steps : nat) :
  run_schedule fuel state schedule = EchoRunStuck final_state steps ->
  echo_completeb final_state = false /\
  echo_stuckb final_state = true.
Proof.
  intro Hrun.
  pose proof (run_schedule_outcome_classified fuel state schedule)
    as Hclassified.
  now rewrite Hrun in Hclassified.
Qed.

Corollary run_schedule_invalid_choice_sound
    (fuel : nat)
    (state rejected_state : @executable_echo_state node)
    (schedule : list (@echo_event node))
    (steps : nat) (event : @echo_event node) :
  run_schedule fuel state schedule =
    EchoRunInvalidChoice rejected_state steps event ->
  echo_completeb rejected_state = false /\
  echo_stuckb rejected_state = false /\
  echo_exec rejected_state event = None.
Proof.
  intro Hrun.
  pose proof (run_schedule_outcome_classified fuel state schedule)
    as Hclassified.
  now rewrite Hrun in Hclassified.
Qed.

Corollary run_schedule_complete_reachable
    (fuel : nat)
    (state final_state : @executable_echo_state node)
    (schedule : list (@echo_event node))
    (steps : nat) :
  echo_reachable state ->
  run_schedule fuel state schedule = EchoRunComplete final_state steps ->
  echo_reachable final_state /\ echo_complete final_state.
Proof.
  intros Hreachable Hrun. split.
  - pose proof (run_schedule_reachable fuel state schedule Hreachable)
      as Hfinal.
    now rewrite Hrun in Hfinal.
  - eapply run_schedule_complete_sound. exact Hrun.
Qed.

(** The number recorded in any result counts successful interpreter calls;
    it can never exceed either the fuel or the available schedule prefix. *)
Theorem run_schedule_steps_le_fuel
    (fuel : nat)
    (state : @executable_echo_state node)
    (schedule : list (@echo_event node)) :
  run_outcome_steps (run_schedule fuel state schedule) <= fuel.
Proof.
  revert state schedule.
  induction fuel as [| fuel IH]; intros state schedule;
    cbn [run_schedule].
  - destruct (echo_completeb state); simpl; [lia |].
    destruct (echo_stuckb state); simpl; lia.
  - destruct (echo_completeb state); simpl; [lia |].
    destruct (echo_stuckb state); simpl; [lia |].
    destruct schedule as [| event rest]; simpl; [lia |].
    destruct (echo_exec state event) as [successor |] eqn:Hexec; simpl.
    + rewrite bump_run_outcome_steps. specialize (IH successor rest). lia.
    + lia.
Qed.

Theorem run_schedule_steps_le_schedule
    (fuel : nat)
    (state : @executable_echo_state node)
    (schedule : list (@echo_event node)) :
  run_outcome_steps (run_schedule fuel state schedule) <=
  List.length schedule.
Proof.
  revert state schedule.
  induction fuel as [| fuel IH]; intros state schedule;
    cbn [run_schedule].
  - destruct (echo_completeb state); simpl; [lia |].
    destruct (echo_stuckb state); simpl; lia.
  - destruct (echo_completeb state); simpl; [lia |].
    destruct (echo_stuckb state); simpl; [lia |].
    destruct schedule as [| event rest]; simpl; [lia |].
    destruct (echo_exec state event) as [successor |] eqn:Hexec; simpl.
    + rewrite bump_run_outcome_steps. specialize (IH successor rest). lia.
    + lia.
Qed.

Corollary run_schedule_from_initial_reachable
    (fuel : nat) (schedule : list (@echo_event node)) :
  echo_reachable
    (run_outcome_state
      (run_schedule fuel initial_executable_echo_state schedule)).
Proof.
  apply run_schedule_reachable. constructor.
Qed.

End EchoRunner.

Arguments echo_list_emptyb {A} _.
Arguments echo_complete {node} config _.
Arguments echo_completeb {node} config _.
Arguments echo_stuckb {node} _.
Arguments EchoRunComplete {node} _ _.
Arguments EchoRunStuck {node} _ _.
Arguments EchoRunBounded {node} _ _.
Arguments EchoRunInvalidChoice {node} _ _ _.
Arguments run_outcome_state {node} _.
Arguments run_outcome_steps {node} _.
Arguments run_outcome_rejected_event {node} _.
Arguments bump_run_outcome {node} _.
Arguments run_schedule {node} node_eq config _ _ _.
Arguments run_outcome_classified {node} node_eq config _.
