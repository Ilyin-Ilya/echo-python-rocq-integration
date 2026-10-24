(** * Generic initialization and bounded schedule execution *)

From Stdlib Require Import List Bool Arith Lia String.
Import ListNotations.
Open Scope string_scope.
Require Import ProtocolIRTypes ProtocolIRExpressions ProtocolIRActions
  ProtocolIRInterpreter.

Record ir_protocol_program
    (node : Type) (signature : protocol_signature) : Type :=
  mkIRProtocolProgram {
    ir_program_schema_version : nat;
    ir_program_ir_version : nat;
    ir_program_id : string;
    ir_program_initial_local : ir_local_store node signature;
    ir_program_initial_global : ir_global_store node signature;
    ir_program_initial_next_message_id : nat;
    ir_program_rules : list (ir_rule node signature);
    ir_program_complete : ir_expr node signature IRBool;
    ir_program_stuck : ir_expr node signature IRBool
  }.

Arguments mkIRProtocolProgram {node signature} _ _ _ _ _ _ _ _ _.
Arguments ir_program_schema_version {node signature} _.
Arguments ir_program_ir_version {node signature} _.
Arguments ir_program_id {node signature} _.
Arguments ir_program_initial_local {node signature} _ _.
Arguments ir_program_initial_global {node signature} _ _.
Arguments ir_program_initial_next_message_id {node signature} _.
Arguments ir_program_rules {node signature} _.
Arguments ir_program_complete {node signature} _.
Arguments ir_program_stuck {node signature} _.

Definition initialize_ir_protocol
    {node : Type} {signature : protocol_signature}
    (program : ir_protocol_program node signature) :
    ir_protocol_state node signature :=
  mkIRProtocolState
    (fun _ => ir_program_initial_local program)
    []
    (ir_program_initial_global program)
    (ir_program_initial_next_message_id program).

Definition eval_ir_state_predicate
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (state : ir_protocol_state node signature)
    (predicate : ir_expr node signature IRBool) : option bool :=
  match eval_ir_expr
    node_eq_dec config state IRRuntimeQuery predicate with
  | Some (IRBoolValue value) => Some value
  | Some _ => None
  | None => None
  end.

Inductive ir_run_error : Type :=
  | IRCompletionPredicateMalformed
  | IRStuckPredicateMalformed
  | IRTransitionRejected (error : ir_step_error).

Inductive ir_run_outcome
    (node : Type) (signature : protocol_signature) : Type :=
  | IRRunComplete
      (state : ir_protocol_state node signature)
      (steps : nat)
  | IRRunStuck
      (state : ir_protocol_state node signature)
      (steps : nat)
  | IRRunScheduleExhausted
      (state : ir_protocol_state node signature)
      (steps : nat)
  | IRRunBounded
      (state : ir_protocol_state node signature)
      (steps : nat)
  | IRRunInvalid
      (state : ir_protocol_state node signature)
      (event : option (ir_external_event node signature))
      (error : ir_run_error)
      (steps : nat).

Arguments IRRunComplete {node signature} _ _.
Arguments IRRunStuck {node signature} _ _.
Arguments IRRunScheduleExhausted {node signature} _ _.
Arguments IRRunBounded {node signature} _ _.
Arguments IRRunInvalid {node signature} _ _ _ _.

Definition ir_run_outcome_steps
    {node : Type} {signature : protocol_signature}
    (outcome : ir_run_outcome node signature) : nat :=
  match outcome with
  | IRRunComplete _ steps
  | IRRunStuck _ steps
  | IRRunScheduleExhausted _ steps
  | IRRunBounded _ steps
  | IRRunInvalid _ _ _ steps => steps
  end.

Definition ir_run_outcome_state
    {node : Type} {signature : protocol_signature}
    (outcome : ir_run_outcome node signature) :
    ir_protocol_state node signature :=
  match outcome with
  | IRRunComplete state _
  | IRRunStuck state _
  | IRRunScheduleExhausted state _
  | IRRunBounded state _
  | IRRunInvalid state _ _ _ => state
  end.

Definition increment_ir_run_outcome
    {node : Type} {signature : protocol_signature}
    (outcome : ir_run_outcome node signature) :
    ir_run_outcome node signature :=
  match outcome with
  | IRRunComplete state steps => IRRunComplete state (S steps)
  | IRRunStuck state steps => IRRunStuck state (S steps)
  | IRRunScheduleExhausted state steps =>
      IRRunScheduleExhausted state (S steps)
  | IRRunBounded state steps => IRRunBounded state (S steps)
  | IRRunInvalid state event error steps =>
      IRRunInvalid state event error (S steps)
  end.

Lemma increment_ir_run_outcome_steps
    {node : Type} {signature : protocol_signature}
    (outcome : ir_run_outcome node signature) :
  ir_run_outcome_steps (increment_ir_run_outcome outcome) =
    S (ir_run_outcome_steps outcome).
Proof. destruct outcome; reflexivity. Qed.

Lemma increment_ir_run_outcome_state
    {node : Type} {signature : protocol_signature}
    (outcome : ir_run_outcome node signature) :
  ir_run_outcome_state (increment_ir_run_outcome outcome) =
    ir_run_outcome_state outcome.
Proof. destruct outcome; reflexivity. Qed.

Lemma increment_ir_run_complete_inv
    {node : Type} {signature : protocol_signature}
    (outcome : ir_run_outcome node signature)
    (final : ir_protocol_state node signature)
    (steps : nat) :
  increment_ir_run_outcome outcome = IRRunComplete final steps ->
  exists previous_steps, outcome = IRRunComplete final previous_steps.
Proof.
  destruct outcome; cbn; intro result; try discriminate.
  inversion result. subst. eauto.
Qed.

Lemma increment_ir_run_stuck_inv
    {node : Type} {signature : protocol_signature}
    (outcome : ir_run_outcome node signature)
    (final : ir_protocol_state node signature)
    (steps : nat) :
  increment_ir_run_outcome outcome = IRRunStuck final steps ->
  exists previous_steps, outcome = IRRunStuck final previous_steps.
Proof.
  destruct outcome; cbn; intro result; try discriminate.
  inversion result. subst. eauto.
Qed.

Inductive ir_protocol_reachable
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (rules : list (ir_rule node signature)) :
    ir_protocol_state node signature ->
    ir_protocol_state node signature -> Prop :=
  | IRReachableRefl : forall state,
      ir_protocol_reachable node_eq_dec config rules state state
  | IRReachableStep :
      forall state event rule successor final,
      interpret_protocol_rules node_eq_dec config rules state event =
        IRStepSuccess rule successor ->
      ir_protocol_reachable node_eq_dec config rules successor final ->
      ir_protocol_reachable node_eq_dec config rules state final.

Lemma ir_protocol_reachable_trans
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (rules : list (ir_rule node signature))
    (first second third : ir_protocol_state node signature) :
  ir_protocol_reachable node_eq_dec config rules first second ->
  ir_protocol_reachable node_eq_dec config rules second third ->
  ir_protocol_reachable node_eq_dec config rules first third.
Proof.
  intros first_path second_path.
  induction first_path.
  - exact second_path.
  - eapply IRReachableStep.
    + exact H.
    + now apply IHfirst_path.
Qed.

(** Message identifiers remain monotone along every finite path interpreted
    by the generic kernel. *)
Theorem ir_protocol_reachable_next_message_id_monotone
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (rules : list (ir_rule node signature))
    (initial final : ir_protocol_state node signature) :
  ir_protocol_reachable node_eq_dec config rules initial final ->
  ir_next_message_id initial <= ir_next_message_id final.
Proof.
  intro reachable.
  induction reachable.
  - apply Nat.le_refl.
  - eapply Nat.le_trans.
    + exact (interpret_protocol_rules_next_message_id_monotone
        node_eq_dec config rules state successor event rule H).
    + exact IHreachable.
Qed.

Fixpoint run_ir_protocol_schedule
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (program : ir_protocol_program node signature)
    (fuel : nat)
    (state : ir_protocol_state node signature)
    (schedule : list (ir_external_event node signature)) :
    ir_run_outcome node signature :=
  match eval_ir_state_predicate
    node_eq_dec config state (ir_program_complete program) with
  | None => IRRunInvalid state None IRCompletionPredicateMalformed 0
  | Some true => IRRunComplete state 0
  | Some false =>
      match eval_ir_state_predicate
        node_eq_dec config state (ir_program_stuck program) with
      | None => IRRunInvalid state None IRStuckPredicateMalformed 0
      | Some true => IRRunStuck state 0
      | Some false =>
          match fuel with
          | 0 => IRRunBounded state 0
          | S remaining_fuel =>
              match schedule with
              | [] => IRRunScheduleExhausted state 0
              | event :: remaining_schedule =>
                  match interpret_protocol_rules
                    node_eq_dec config (ir_program_rules program)
                    state event with
                  | IRStepFailure error =>
                      IRRunInvalid state (Some event)
                        (IRTransitionRejected error) 0
                  | IRStepSuccess _ successor =>
                      increment_ir_run_outcome
                        (run_ir_protocol_schedule
                          node_eq_dec config program remaining_fuel
                          successor remaining_schedule)
                  end
              end
          end
      end
  end.

Definition run_ir_protocol
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (program : ir_protocol_program node signature)
    (fuel : nat)
    (schedule : list (ir_external_event node signature)) :
    ir_run_outcome node signature :=
  run_ir_protocol_schedule node_eq_dec config program fuel
    (initialize_ir_protocol program) schedule.

Theorem run_ir_protocol_schedule_complete_sound
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (program : ir_protocol_program node signature) :
  forall fuel state schedule final steps,
    run_ir_protocol_schedule node_eq_dec config program fuel state schedule =
      IRRunComplete final steps ->
    eval_ir_state_predicate
      node_eq_dec config final (ir_program_complete program) = Some true.
Proof.
  induction fuel as [|fuel IH];
    intros state schedule final steps run_result;
    cbn [run_ir_protocol_schedule] in run_result.
  - destruct (eval_ir_state_predicate
      node_eq_dec config state (ir_program_complete program))
      as [complete |] eqn:complete_result; try discriminate.
    destruct complete.
    + inversion run_result. subst. exact complete_result.
    + destruct (eval_ir_state_predicate
        node_eq_dec config state (ir_program_stuck program))
        as [stuck |] eqn:stuck_result; try discriminate.
      destruct stuck; discriminate.
  - destruct (eval_ir_state_predicate
      node_eq_dec config state (ir_program_complete program))
      as [complete |] eqn:complete_result; try discriminate.
    destruct complete.
    + inversion run_result. subst. exact complete_result.
    + destruct (eval_ir_state_predicate
        node_eq_dec config state (ir_program_stuck program))
        as [stuck |] eqn:stuck_result; try discriminate.
      destruct stuck; try discriminate.
      destruct schedule as [|event remaining_schedule]; try discriminate.
      destruct (interpret_protocol_rules
        node_eq_dec config (ir_program_rules program) state event)
        as [rule successor | error] eqn:step_result; try discriminate.
      apply increment_ir_run_complete_inv in run_result
        as [previous_steps recursive_result].
      eapply IH. exact recursive_result.
Qed.

Theorem run_ir_protocol_schedule_stuck_sound
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (program : ir_protocol_program node signature) :
  forall fuel state schedule final steps,
    run_ir_protocol_schedule node_eq_dec config program fuel state schedule =
      IRRunStuck final steps ->
    eval_ir_state_predicate
      node_eq_dec config final (ir_program_stuck program) = Some true.
Proof.
  induction fuel as [|fuel IH];
    intros state schedule final steps run_result;
    cbn [run_ir_protocol_schedule] in run_result.
  - destruct (eval_ir_state_predicate
      node_eq_dec config state (ir_program_complete program))
      as [complete |] eqn:complete_result; try discriminate.
    destruct complete; try discriminate.
    destruct (eval_ir_state_predicate
      node_eq_dec config state (ir_program_stuck program))
      as [stuck |] eqn:stuck_result; try discriminate.
    destruct stuck.
    + inversion run_result. subst. exact stuck_result.
    + discriminate.
  - destruct (eval_ir_state_predicate
      node_eq_dec config state (ir_program_complete program))
      as [complete |] eqn:complete_result; try discriminate.
    destruct complete; try discriminate.
    destruct (eval_ir_state_predicate
      node_eq_dec config state (ir_program_stuck program))
      as [stuck |] eqn:stuck_result; try discriminate.
    destruct stuck.
    + inversion run_result. subst. exact stuck_result.
    + destruct schedule as [|event remaining_schedule]; try discriminate.
      destruct (interpret_protocol_rules
        node_eq_dec config (ir_program_rules program) state event)
        as [rule successor | error] eqn:step_result; try discriminate.
      apply increment_ir_run_stuck_inv in run_result
        as [previous_steps recursive_result].
      eapply IH. exact recursive_result.
Qed.

Theorem run_ir_protocol_schedule_step_bound
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (program : ir_protocol_program node signature) :
  forall fuel state schedule,
    ir_run_outcome_steps
      (run_ir_protocol_schedule
        node_eq_dec config program fuel state schedule) <= fuel.
Proof.
  induction fuel as [|fuel IH]; intros state schedule.
  - cbn [run_ir_protocol_schedule].
    destruct (eval_ir_state_predicate
      node_eq_dec config state (ir_program_complete program))
      as [complete |] eqn:complete_result.
    + destruct complete.
      * reflexivity.
      * destruct (eval_ir_state_predicate
          node_eq_dec config state (ir_program_stuck program))
          as [stuck |] eqn:stuck_result.
        -- destruct stuck; reflexivity.
        -- reflexivity.
    + reflexivity.
  - cbn [run_ir_protocol_schedule].
    destruct (eval_ir_state_predicate
      node_eq_dec config state (ir_program_complete program))
      as [complete |] eqn:complete_result.
    + destruct complete.
      * cbn. lia.
      * destruct (eval_ir_state_predicate
          node_eq_dec config state (ir_program_stuck program))
          as [stuck |] eqn:stuck_result.
        -- destruct stuck.
           ++ cbn. lia.
           ++ destruct schedule as [|event remaining_schedule].
              ** cbn. lia.
              ** destruct (interpret_protocol_rules
                   node_eq_dec config (ir_program_rules program) state event)
                   as [rule successor | error].
                 --- rewrite increment_ir_run_outcome_steps.
                     specialize (IH successor remaining_schedule).
                     lia.
                 --- cbn. lia.
        -- cbn. lia.
    + cbn. lia.
Qed.

Theorem run_ir_protocol_step_bound
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (program : ir_protocol_program node signature)
    (fuel : nat)
    (schedule : list (ir_external_event node signature)) :
  ir_run_outcome_steps
    (run_ir_protocol node_eq_dec config program fuel schedule) <= fuel.
Proof.
  apply run_ir_protocol_schedule_step_bound.
Qed.

Theorem run_ir_protocol_schedule_reachable
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (program : ir_protocol_program node signature) :
  forall fuel state schedule,
    ir_protocol_reachable node_eq_dec config (ir_program_rules program)
      state
      (ir_run_outcome_state
        (run_ir_protocol_schedule
          node_eq_dec config program fuel state schedule)).
Proof.
  induction fuel as [|fuel IH]; intros state schedule.
  - cbn [run_ir_protocol_schedule].
    destruct (eval_ir_state_predicate
      node_eq_dec config state (ir_program_complete program))
      as [complete |] eqn:complete_result.
    + destruct complete.
      * constructor.
      * destruct (eval_ir_state_predicate
          node_eq_dec config state (ir_program_stuck program))
          as [stuck |] eqn:stuck_result.
        -- destruct stuck; constructor.
        -- constructor.
    + constructor.
  - cbn [run_ir_protocol_schedule].
    destruct (eval_ir_state_predicate
      node_eq_dec config state (ir_program_complete program))
      as [complete |] eqn:complete_result.
    + destruct complete.
      * constructor.
      * destruct (eval_ir_state_predicate
          node_eq_dec config state (ir_program_stuck program))
          as [stuck |] eqn:stuck_result.
        -- destruct stuck.
           ++ constructor.
           ++ destruct schedule as [|event remaining_schedule].
              ** constructor.
              ** destruct (interpret_protocol_rules
                   node_eq_dec config (ir_program_rules program) state event)
                   as [rule successor | error] eqn:step_result.
                 --- rewrite increment_ir_run_outcome_state.
                     exact
                       (@IRReachableStep
                         node signature node_eq_dec config
                         (ir_program_rules program)
                         state event rule successor
                         (ir_run_outcome_state
                           (run_ir_protocol_schedule
                             node_eq_dec config program fuel successor
                             remaining_schedule))
                         step_result
                         (IH successor remaining_schedule)).
                 --- constructor.
        -- constructor.
    + constructor.
Qed.

Theorem run_ir_protocol_reachable
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (program : ir_protocol_program node signature)
    (fuel : nat)
    (schedule : list (ir_external_event node signature)) :
  ir_protocol_reachable node_eq_dec config (ir_program_rules program)
    (initialize_ir_protocol program)
    (ir_run_outcome_state
      (run_ir_protocol node_eq_dec config program fuel schedule)).
Proof.
  apply run_ir_protocol_schedule_reachable.
Qed.
