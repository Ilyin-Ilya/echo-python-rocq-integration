(** * Public executable surface for Echo's generic IR program

    This module deliberately imports no legacy Echo transition language or
    compatibility proof.  It gives the generated generic program a compact
    public API for initialization, stepping, completion, reachability, and
    bounded execution.  Future direct safety proofs should depend on this
    surface rather than on [EchoTransitionIR]. *)

From Stdlib Require Import List Bool Arith.
Import ListNotations.
Require Import ProtocolIRTypes ProtocolIRExpressions ProtocolIRActions
  ProtocolIRInterpreter ProtocolIRRunner EchoIRSignature EchoIRProgram.

Section EchoIRExecutable.

Variable node : Type.
Variable node_eq : forall left right : node,
  {left = right} + {left <> right}.

(** The one maintained generic Echo behavior value. *)
Definition echo_program :
    ir_protocol_program node echo_ir_signature :=
  @echo_ir_program node.

Definition echo_initial_state :
    ir_protocol_state node echo_ir_signature :=
  initialize_ir_protocol echo_program.

Definition echo_exec
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (event : ir_external_event node echo_ir_signature) :
    ir_step_result node echo_ir_signature :=
  interpret_protocol_rules node_eq config
    (ir_program_rules echo_program) state event.

Definition EchoStep
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (event : ir_external_event node echo_ir_signature)
    (successor : ir_protocol_state node echo_ir_signature) : Prop :=
  exists rule, echo_exec config state event = IRStepSuccess rule successor.

Definition echo_complete
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  eval_ir_state_predicate node_eq config state
    (ir_program_complete echo_program) = Some true.

Definition echo_stuck
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  eval_ir_state_predicate node_eq config state
    (ir_program_stuck echo_program) = Some true.

Definition echo_reachable
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  ir_protocol_reachable node_eq config (ir_program_rules echo_program)
    echo_initial_state state.

Definition echo_run
    (config : ir_protocol_config node echo_ir_signature)
    (fuel : nat)
    (schedule : list (ir_external_event node echo_ir_signature)) :
    ir_run_outcome node echo_ir_signature :=
  run_ir_protocol node_eq config echo_program fuel schedule.

(** These equalities make the source-of-truth boundary mechanically visible. *)
Theorem echo_program_is_generic_ir :
  echo_program = @echo_ir_program node.
Proof. reflexivity. Qed.

Theorem echo_exec_is_generic_interpretation
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (event : ir_external_event node echo_ir_signature) :
  echo_exec config state event =
  interpret_protocol_rules node_eq config (@echo_ir_rules node) state event.
Proof. reflexivity. Qed.

(** Initialization is computed from the generic program record, with no
    compatibility encoding or old executable state involved. *)
Theorem echo_initial_state_shape :
  (forall owner,
    ir_processes echo_initial_state owner EchoIRParent =
      IROptionNodeValue None /\
    ir_processes echo_initial_state owner EchoIRPending =
      IRListNodeValue [] /\
    ir_processes echo_initial_state owner EchoIRFinished =
      IRBoolValue false) /\
  ir_message_store echo_initial_state = [] /\
  ir_global_fields echo_initial_state EchoIRStarted = IRBoolValue false /\
  ir_next_message_id echo_initial_state = 1.
Proof.
  repeat split; reflexivity.
Qed.

(** Functional interpretation makes the generic Echo step deterministic. *)
Theorem EchoStep_deterministic
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (event : ir_external_event node echo_ir_signature)
    (first second : ir_protocol_state node echo_ir_signature) :
  EchoStep config state event first ->
  EchoStep config state event second ->
  first = second.
Proof.
  intros [first_rule first_step] [second_rule second_step].
  rewrite first_step in second_step.
  now inversion second_step.
Qed.

(** A successful Echo step exposes only facts from the generic interpreter:
    the external event was resolved, one rule from [echo_program] was selected
    and enabled, and that rule's action computed the successor.  Direct Echo
    invariants should use this lemma instead of unfolding the interpreter or
    passing through the retired Echo-specific transition language. *)
Theorem echo_ir_step_success_components
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (external_event : ir_external_event node echo_ir_signature) :
  EchoStep config state external_event successor ->
  exists rule_id runtime_event selected_rule,
    ir_resolve_event state external_event = Some runtime_event /\
    select_ir_rule node_eq config state runtime_event
      (ir_program_rules echo_program) =
        IRUniqueRuleSelected selected_rule /\
    In selected_rule (ir_program_rules echo_program) /\
    eval_ir_rule node_eq config state runtime_event selected_rule =
      IRRuleEnabled /\
    ir_rule_id selected_rule = rule_id /\
    eval_ir_action node_eq config state runtime_event
      (ir_rule_action selected_rule) = Some successor.
Proof.
  intros [rule_id interpreted].
  destruct (interpret_protocol_rules_success_components
    node_eq config (ir_program_rules echo_program) state external_event
    rule_id successor interpreted) as
    [runtime_event [selected_rule
      [resolved [selected [identifier action]]]]].
  exists rule_id, runtime_event, selected_rule.
  repeat split.
  - exact resolved.
  - exact selected.
  - exact (select_ir_rule_unique_in
      node_eq config state runtime_event
      (ir_program_rules echo_program) selected_rule selected).
  - exact (select_ir_rule_unique_is_enabled
      node_eq config state runtime_event
      (ir_program_rules echo_program) selected_rule selected).
  - exact identifier.
  - exact action.
Qed.

(** Every guard attached to the rule selected by a successful generic Echo
    step evaluated to true in the pre-state. *)
Theorem echo_ir_step_selected_guard_holds
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (external_event : ir_external_event node echo_ir_signature)
    (runtime_event : ir_runtime_event node echo_ir_signature)
    (selected_rule : ir_rule node echo_ir_signature)
    (guard : ir_expr node echo_ir_signature IRBool) :
  EchoStep config state external_event successor ->
  ir_resolve_event state external_event = Some runtime_event ->
  select_ir_rule node_eq config state runtime_event
    (ir_program_rules echo_program) =
      IRUniqueRuleSelected selected_rule ->
  In guard (ir_rule_guards selected_rule) ->
  eval_ir_expr node_eq config state runtime_event guard =
    Some (IRBoolValue true).
Proof.
  intros step resolved selected member.
  destruct (echo_ir_step_success_components
    config state successor external_event step) as
    [rule_id [actual_event [actual_rule
      [actual_resolved [actual_selected
        [actual_in [actual_enabled [identifier action]]]]]]]].
  rewrite resolved in actual_resolved.
  inversion actual_resolved. subst actual_event.
  rewrite selected in actual_selected.
  inversion actual_selected. subst actual_rule.
  exact (eval_ir_rule_enabled_guard
    node_eq config state runtime_event selected_rule guard
    actual_enabled member).
Qed.

(** The scheduler can request delivery only by identifier.  If that request
    produces an Echo step, the identifier resolved to an authoritative
    message already present in the pre-state's queue. *)
Theorem echo_ir_step_delivery_message_queued
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (selected_id : nat)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  EchoStep config state (IRProtocolDeliver selected_id certificates)
    successor ->
  exists message,
    In message (ir_message_store state) /\
    selected_id = ir_message_id message.
Proof.
  intro step.
  destruct (echo_ir_step_success_components
    config state successor (IRProtocolDeliver selected_id certificates)
    step) as
    [rule_id [runtime_event [selected_rule
      [resolved [selected
        [selected_in [enabled [identifier action]]]]]]]].
  destruct (resolved_delivery_was_queued
    state selected_id certificates runtime_event resolved) as
    [message [queued [same_id event_shape]]].
  exists message. now split.
Qed.

(** The first directly maintained state invariant on the generic Echo API:
    successful steps never decrease the fresh-message allocator. *)
Theorem EchoStep_next_message_id_monotone
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (external_event : ir_external_event node echo_ir_signature) :
  EchoStep config state external_event successor ->
  ir_next_message_id state <= ir_next_message_id successor.
Proof.
  intros [rule_id interpreted].
  exact (interpret_protocol_rules_next_message_id_monotone
    node_eq config (ir_program_rules echo_program) state successor
    external_event rule_id interpreted).
Qed.

(** Echo initializes its allocator at one, so every state reachable through
    the generic interpreter retains a positive next message identifier. *)
Theorem echo_reachable_next_message_id_positive
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) :
  echo_reachable config state ->
  1 <= ir_next_message_id state.
Proof.
  intro reachable.
  pose proof (ir_protocol_reachable_next_message_id_monotone
    node_eq config (ir_program_rules echo_program)
    echo_initial_state state reachable) as monotone.
  exact monotone.
Qed.

Lemma echo_single_step_reachable
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (event : ir_external_event node echo_ir_signature) :
  EchoStep config state event successor ->
  ir_protocol_reachable node_eq config (ir_program_rules echo_program)
    state successor.
Proof.
  intros [rule step].
  eapply IRReachableStep.
  - exact step.
  - constructor.
Qed.

Theorem EchoStep_preserves_reachability
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (event : ir_external_event node echo_ir_signature) :
  echo_reachable config state ->
  EchoStep config state event successor ->
  echo_reachable config successor.
Proof.
  intros reachable step.
  unfold echo_reachable in *.
  eapply ir_protocol_reachable_trans.
  - exact reachable.
  - now apply echo_single_step_reachable with (event := event).
Qed.

(** Every terminal runner state is reachable from the generic initializer. *)
Theorem echo_run_reachable
    (config : ir_protocol_config node echo_ir_signature)
    (fuel : nat)
    (schedule : list (ir_external_event node echo_ir_signature)) :
  echo_reachable config (ir_run_outcome_state
    (echo_run config fuel schedule)).
Proof.
  unfold echo_reachable, echo_run, echo_initial_state, echo_program.
  apply run_ir_protocol_reachable.
Qed.

Theorem echo_run_step_bound
    (config : ir_protocol_config node echo_ir_signature)
    (fuel : nat)
    (schedule : list (ir_external_event node echo_ir_signature)) :
  ir_run_outcome_steps (echo_run config fuel schedule) <= fuel.
Proof.
  unfold echo_run, echo_program.
  apply run_ir_protocol_step_bound.
Qed.

Theorem echo_run_complete_sound
    (config : ir_protocol_config node echo_ir_signature)
    (fuel : nat)
    (schedule : list (ir_external_event node echo_ir_signature))
    (final : ir_protocol_state node echo_ir_signature)
    (steps : nat) :
  echo_run config fuel schedule = IRRunComplete final steps ->
  echo_complete config final.
Proof.
  unfold echo_run, echo_complete, run_ir_protocol.
  now apply run_ir_protocol_schedule_complete_sound.
Qed.

Theorem echo_run_stuck_sound
    (config : ir_protocol_config node echo_ir_signature)
    (fuel : nat)
    (schedule : list (ir_external_event node echo_ir_signature))
    (final : ir_protocol_state node echo_ir_signature)
    (steps : nat) :
  echo_run config fuel schedule = IRRunStuck final steps ->
  echo_stuck config final.
Proof.
  unfold echo_run, echo_stuck, run_ir_protocol.
  now apply run_ir_protocol_schedule_stuck_sound.
Qed.

End EchoIRExecutable.

Arguments echo_program {node}.
Arguments echo_initial_state {node}.
