(** * Direct lifecycle invariants for the public Echo IR executable

    This module reasons only about the generic Echo program and interpreter.
    In particular, it does not import a legacy Echo transition, compatibility
    relation, or forward/backward simulation proof. *)

From Stdlib Require Import List Bool Arith.
Import ListNotations.
Require Import ProtocolIRTypes ProtocolIRExpressions ProtocolIRActions
  ProtocolIRInterpreter ProtocolIRRunner EchoIRSignature EchoIRProgram
  EchoIRExecutable EchoIRExecutableInvariants.

Section EchoIRExecutableLifecycle.

Variable node : Type.
Variable node_eq : forall left right : node,
  {left = right} + {left <> right}.

Definition echo_ir_finished_participants_parented
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall owner,
    owner <> echo_ir_config_initiator node config ->
    ir_processes state owner EchoIRFinished = IRBoolValue true ->
    exists parent,
      ir_processes state owner EchoIRParent =
        IROptionNodeValue (Some parent).

(** Echo rules that update a process always write these three local fields in
    this order.  Naming the common state transformation keeps later invariant
    proofs independent of action-sequence syntax. *)
Definition echo_ir_update_process
    (state : ir_protocol_state node echo_ir_signature)
    (owner : node)
    (parent : ir_value node IROptionNode)
    (pending : ir_value node IRListNode)
    (finished : bool) : ir_protocol_state node echo_ir_signature :=
  ir_set_local_field node_eq
    (ir_set_local_field node_eq
      (ir_set_local_field node_eq state owner EchoIRParent parent)
      owner EchoIRPending pending)
    owner EchoIRFinished (IRBoolValue finished).

Lemma echo_ir_update_process_unfinished_preserves_parented
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (owner : node)
    (parent : ir_value node IROptionNode)
    (pending : ir_value node IRListNode) :
  echo_ir_finished_participants_parented config state ->
  echo_ir_finished_participants_parented config
    (echo_ir_update_process state owner parent pending false).
Proof.
  intros invariant observed observed_not_root observed_finished.
  unfold echo_ir_update_process in *.
  destruct (node_eq owner observed) as [same | different].
  - subst observed.
    rewrite ir_set_local_field_same in observed_finished.
    discriminate.
  - repeat rewrite ir_set_local_field_read_other_process
      in observed_finished by exact different.
    repeat rewrite ir_set_local_field_read_other_process
      by exact different.
    now apply invariant.
Qed.

Lemma echo_ir_update_process_finished_some_preserves_parented
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (owner parent : node)
    (pending : ir_value node IRListNode) :
  echo_ir_finished_participants_parented config state ->
  echo_ir_finished_participants_parented config
    (echo_ir_update_process state owner
      (IROptionNodeValue (Some parent)) pending true).
Proof.
  intros invariant observed observed_not_root observed_finished.
  unfold echo_ir_update_process in *.
  destruct (node_eq owner observed) as [same | different].
  - subst observed. exists parent.
    rewrite ir_set_local_field_read_different by discriminate.
    rewrite ir_set_local_field_read_different by discriminate.
    apply ir_set_local_field_same.
  - repeat rewrite ir_set_local_field_read_other_process
      in observed_finished by exact different.
    repeat rewrite ir_set_local_field_read_other_process
      by exact different.
    now apply invariant.
Qed.

Lemma echo_ir_update_initiator_preserves_parented
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (parent : ir_value node IROptionNode)
    (pending : ir_value node IRListNode)
    (finished : bool) :
  echo_ir_finished_participants_parented config state ->
  echo_ir_finished_participants_parented config
    (echo_ir_update_process state
      (echo_ir_config_initiator node config) parent pending finished).
Proof.
  intros invariant observed observed_not_root observed_finished.
  unfold echo_ir_update_process in *.
  repeat rewrite ir_set_local_field_read_other_process
    in observed_finished by
      (intro same; apply observed_not_root; now symmetry).
  repeat rewrite ir_set_local_field_read_other_process
    by (intro same; apply observed_not_root; now symmetry).
  now apply invariant.
Qed.

Lemma echo_ir_start_action_preserves_finished_parented
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (certificates : ir_start_certificates node echo_ir_signature) :
  echo_ir_finished_participants_parented config state ->
  eval_ir_action node_eq config state (IRRuntimeStart certificates)
    (ir_rule_action (@echo_ir_start_rule node)) = Some successor ->
  echo_ir_finished_participants_parented config successor.
Proof.
  intros invariant action.
  unfold echo_ir_start_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_bool, echo_ir_initiator, echo_ir_start_order, echo_ir_neighbors,
    echo_ir_emit_many, echo_ir_empty_payload, echo_ir_option_none in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs] in action.
  unfold echo_ir_initiator in action.
  set (initiator := ir_node_value_contents
    (ir_config_fields config EchoIRInitiator)).
  assert (initiator_value :
    ir_config_fields config EchoIRInitiator = IRNodeValue initiator).
  { apply ir_node_value_eta. }
  replace (ir_config_fields config EchoIRInitiator)
    with (IRNodeValue initiator) in action
    by (symmetry; exact initiator_value).
  repeat rewrite initiator_value in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs] in action.
  repeat rewrite initiator_value in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs] in action.
  injection action as <-.
  unfold ir_emit_messages, ir_set_global_field.
  change (echo_ir_finished_participants_parented config
    (echo_ir_update_process state
      (echo_ir_config_initiator node config)
      (IROptionNodeValue None)
      (IRListNodeValue (ir_config_neighbors config initiator))
      false)).
  now apply echo_ir_update_initiator_preserves_parented.
Qed.

Lemma echo_ir_first_request_nonleaf_action_preserves_finished_parented
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_finished_participants_parented config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_nonleaf_rule node)) =
      Some successor ->
  echo_ir_finished_participants_parented config successor.
Proof.
  intros invariant action.
  unfold echo_ir_first_request_nonleaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_forward_order,
    echo_ir_remove, echo_ir_neighbors, echo_ir_emit_many,
    echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
    ir_event_message] in action.
  injection action as <-.
  unfold ir_emit_messages, ir_remove_selected_message.
  change (echo_ir_finished_participants_parented config
    (echo_ir_update_process state (ir_message_receiver message)
      (IROptionNodeValue (Some (ir_message_sender message)))
      (IRListNodeValue
        (ir_remove_node node_eq (ir_message_sender message)
          (ir_config_neighbors config (ir_message_receiver message))))
      false)).
  now apply echo_ir_update_process_unfinished_preserves_parented.
Qed.

Lemma echo_ir_first_request_leaf_action_preserves_finished_parented
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_finished_participants_parented config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_leaf_rule node)) =
      Some successor ->
  echo_ir_finished_participants_parented config successor.
Proof.
  intros invariant action.
  unfold echo_ir_first_request_leaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_empty_nodes,
    echo_ir_emit_one, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  unfold ir_emit_messages, ir_remove_selected_message.
  change (echo_ir_finished_participants_parented config
    (echo_ir_update_process state (ir_message_receiver message)
      (IROptionNodeValue (Some (ir_message_sender message)))
      (IRListNodeValue []) true)).
  now apply echo_ir_update_process_finished_some_preserves_parented.
Qed.

Lemma echo_ir_message_only_action_preserves_finished_parented
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature) :
  echo_ir_finished_participants_parented config state ->
  ir_processes successor = ir_processes state ->
  echo_ir_finished_participants_parented config successor.
Proof.
  intros invariant processes owner owner_not_root finished.
  unfold echo_ir_finished_participants_parented in invariant.
  rewrite processes in finished |- *.
  now apply invariant.
Qed.

Lemma echo_ir_repeated_request_action_preserves_finished_parented
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_finished_participants_parented config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_repeated_request_rule node)) =
      Some successor ->
  echo_ir_finished_participants_parented config successor.
Proof.
  intros invariant action.
  unfold echo_ir_repeated_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_receiver, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  eapply echo_ir_message_only_action_preserves_finished_parented.
  - exact invariant.
  - unfold ir_emit_messages, ir_remove_selected_message. reflexivity.
Qed.

Lemma echo_ir_initiator_request_action_preserves_finished_parented
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_finished_participants_parented config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_request_rule node)) =
      Some successor ->
  echo_ir_finished_participants_parented config successor.
Proof.
  intros invariant action.
  unfold echo_ir_initiator_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_initiator, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  rewrite (ir_node_value_eta
    (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
    ir_event_message] in action.
  injection action as <-.
  eapply echo_ir_message_only_action_preserves_finished_parented.
  - exact invariant.
  - unfold ir_emit_messages, ir_remove_selected_message. reflexivity.
Qed.

Lemma echo_ir_participant_reply_more_action_preserves_finished_parented
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_finished_participants_parented config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_more_rule node)) =
      Some successor ->
  echo_ir_finished_participants_parented config successor.
Proof.
  intros invariant action.
  unfold echo_ir_participant_reply_more_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_receiver, echo_ir_expected_parent, echo_ir_some,
    echo_ir_removed_pending, echo_ir_remove, echo_ir_sender,
    echo_ir_pending, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  unfold echo_ir_receiver, echo_ir_parent in action.
  set (parent := ir_option_node_value_contents
    (ir_processes state (ir_message_receiver message) EchoIRParent)).
  assert (parent_value :
    ir_processes state (ir_message_receiver message) EchoIRParent =
      IROptionNodeValue parent).
  { apply ir_option_node_value_eta. }
  destruct parent as [parent_node |].
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite (ir_list_node_value_eta
      (ir_processes state (ir_message_receiver message) EchoIRPending))
      in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    injection action as <-.
    unfold ir_remove_selected_message.
    change (echo_ir_finished_participants_parented config
      (echo_ir_update_process state (ir_message_receiver message)
        (IROptionNodeValue (Some parent_node))
        (IRListNodeValue
          (ir_remove_node node_eq (ir_message_sender message)
            (ir_list_node_value_contents
              (ir_processes state
                (ir_message_receiver message) EchoIRPending))))
        false)).
    now apply echo_ir_update_process_unfinished_preserves_parented.
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_participant_reply_final_action_preserves_finished_parented
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_finished_participants_parented config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_final_rule node)) =
      Some successor ->
  echo_ir_finished_participants_parented config successor.
Proof.
  intros invariant action.
  unfold echo_ir_participant_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_receiver, echo_ir_expected_parent, echo_ir_some,
    echo_ir_empty_nodes, echo_ir_emit_one, echo_ir_empty_payload,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  unfold echo_ir_receiver, echo_ir_parent in action.
  set (parent := ir_option_node_value_contents
    (ir_processes state (ir_message_receiver message) EchoIRParent)).
  assert (parent_value :
    ir_processes state (ir_message_receiver message) EchoIRParent =
      IROptionNodeValue parent).
  { apply ir_option_node_value_eta. }
  destruct parent as [parent_node |].
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    unfold ir_remove_selected_message in action.
    cbn [ir_processes] in action.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite ir_set_local_field_read_different in action by discriminate.
    rewrite ir_set_local_field_same in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    injection action as <-.
    unfold ir_emit_messages, ir_remove_selected_message.
    change (echo_ir_finished_participants_parented config
      (echo_ir_update_process state (ir_message_receiver message)
        (IROptionNodeValue (Some parent_node))
        (IRListNodeValue []) true)).
    now apply echo_ir_update_process_finished_some_preserves_parented.
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_initiator_reply_more_action_preserves_finished_parented
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_finished_participants_parented config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_more_rule node)) =
      Some successor ->
  echo_ir_finished_participants_parented config successor.
Proof.
  intros invariant action.
  unfold echo_ir_initiator_reply_more_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_removed_pending,
    echo_ir_remove, echo_ir_sender, echo_ir_pending, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta
    (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  rewrite ir_set_local_field_read_different in action by discriminate.
  rewrite (ir_list_node_value_eta
    (ir_processes state
      (ir_node_value_contents (ir_config_fields config EchoIRInitiator))
      EchoIRPending)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  unfold ir_remove_selected_message.
  change (echo_ir_finished_participants_parented config
    (echo_ir_update_process state
      (echo_ir_config_initiator node config)
      (IROptionNodeValue None)
      (IRListNodeValue
        (ir_remove_node node_eq (ir_message_sender message)
          (ir_list_node_value_contents
            (ir_processes state
              (echo_ir_config_initiator node config) EchoIRPending))))
      false)).
  now apply echo_ir_update_initiator_preserves_parented.
Qed.

Lemma echo_ir_initiator_reply_final_action_preserves_finished_parented
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_finished_participants_parented config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_final_rule node)) =
      Some successor ->
  echo_ir_finished_participants_parented config successor.
Proof.
  intros invariant action.
  unfold echo_ir_initiator_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_empty_nodes,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta
    (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  unfold ir_remove_selected_message.
  change (echo_ir_finished_participants_parented config
    (echo_ir_update_process state
      (echo_ir_config_initiator node config)
      (IROptionNodeValue None) (IRListNodeValue []) true)).
  now apply echo_ir_update_initiator_preserves_parented.
Qed.

(** The selected generic rule preserves the lifecycle invariant.  Rule
    identity and runtime-event shape come from the generic interpreter; each
    branch delegates to the reusable action-effect lemma above. *)
Theorem EchoStep_preserves_finished_participants_parented
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (external_event : ir_external_event node echo_ir_signature) :
  echo_ir_finished_participants_parented config state ->
  EchoStep node node_eq config state external_event successor ->
  echo_ir_finished_participants_parented config successor.
Proof.
  intros invariant step.
  destruct (echo_ir_step_success_components node node_eq
    config state successor external_event step) as
    [rule_id [runtime_event [selected_rule
      [resolved [selected
        [selected_in [enabled [identifier action]]]]]]]].
  change (In selected_rule (@echo_ir_rules node)) in selected_in.
  unfold echo_ir_rules in selected_in.
  cbn in selected_in.
  destruct selected_in as [same | selected_in].
  - subst selected_rule.
    pose proof (eval_ir_rule_enabled_pattern node_eq config state
      runtime_event (@echo_ir_start_rule node) enabled) as pattern.
    destruct runtime_event as [|certificates|message certificates];
      cbn [echo_ir_start_rule ir_event_pattern_matches] in pattern;
      try discriminate.
    exact (echo_ir_start_action_preserves_finished_parented config
      state successor certificates invariant action).
  - destruct selected_in as [same | selected_in].
    + subst selected_rule.
      pose proof (eval_ir_rule_enabled_pattern node_eq config state
        runtime_event (@echo_ir_first_request_nonleaf_rule node) enabled)
        as pattern.
      destruct runtime_event as [|start_certificates|message certificates];
        cbn [echo_ir_first_request_nonleaf_rule ir_event_pattern_matches]
          in pattern; try discriminate.
      exact
        (echo_ir_first_request_nonleaf_action_preserves_finished_parented
          config state successor message certificates invariant action).
    + destruct selected_in as [same | selected_in].
      * subst selected_rule.
        pose proof (eval_ir_rule_enabled_pattern node_eq config state
          runtime_event (@echo_ir_first_request_leaf_rule node) enabled)
          as pattern.
        destruct runtime_event as [|start_certificates|message certificates];
          cbn [echo_ir_first_request_leaf_rule ir_event_pattern_matches]
            in pattern; try discriminate.
        exact
          (echo_ir_first_request_leaf_action_preserves_finished_parented
            config state successor message certificates invariant action).
      * destruct selected_in as [same | selected_in].
        -- subst selected_rule.
           pose proof (eval_ir_rule_enabled_pattern node_eq config state
             runtime_event (@echo_ir_repeated_request_rule node) enabled)
             as pattern.
           destruct runtime_event as
             [|start_certificates|message certificates];
             cbn [echo_ir_repeated_request_rule ir_event_pattern_matches]
               in pattern; try discriminate.
           exact (echo_ir_repeated_request_action_preserves_finished_parented
             config state successor message certificates invariant action).
        -- destruct selected_in as [same | selected_in].
           ++ subst selected_rule.
              pose proof (eval_ir_rule_enabled_pattern node_eq config state
                runtime_event (@echo_ir_initiator_request_rule node) enabled)
                as pattern.
              destruct runtime_event as
                [|start_certificates|message certificates];
                cbn [echo_ir_initiator_request_rule ir_event_pattern_matches]
                  in pattern; try discriminate.
              exact
                (echo_ir_initiator_request_action_preserves_finished_parented
                  config state successor message certificates
                  invariant action).
           ++ destruct selected_in as [same | selected_in].
              ** subst selected_rule.
                 pose proof (eval_ir_rule_enabled_pattern node_eq config state
                   runtime_event
                   (@echo_ir_participant_reply_more_rule node) enabled)
                   as pattern.
                 destruct runtime_event as
                   [|start_certificates|message certificates];
                   cbn [echo_ir_participant_reply_more_rule
                     ir_event_pattern_matches] in pattern; try discriminate.
                 exact
                   (echo_ir_participant_reply_more_action_preserves_finished_parented
                     config state successor message certificates
                     invariant action).
              ** destruct selected_in as [same | selected_in].
                 --- subst selected_rule.
                     pose proof (eval_ir_rule_enabled_pattern
                       node_eq config state runtime_event
                       (@echo_ir_participant_reply_final_rule node) enabled)
                       as pattern.
                     destruct runtime_event as
                       [|start_certificates|message certificates];
                       cbn [echo_ir_participant_reply_final_rule
                         ir_event_pattern_matches] in pattern;
                       try discriminate.
                     exact
                       (echo_ir_participant_reply_final_action_preserves_finished_parented
                         config state successor message certificates
                         invariant action).
                 --- destruct selected_in as [same | selected_in].
                     +++ subst selected_rule.
                         pose proof (eval_ir_rule_enabled_pattern
                           node_eq config state runtime_event
                           (@echo_ir_initiator_reply_more_rule node) enabled)
                           as pattern.
                         destruct runtime_event as
                           [|start_certificates|message certificates];
                           cbn [echo_ir_initiator_reply_more_rule
                             ir_event_pattern_matches] in pattern;
                           try discriminate.
                         exact
                           (echo_ir_initiator_reply_more_action_preserves_finished_parented
                             config state successor message certificates
                             invariant action).
                     +++ destruct selected_in as [same | selected_in].
                         *** subst selected_rule.
                             pose proof (eval_ir_rule_enabled_pattern
                               node_eq config state runtime_event
                               (@echo_ir_initiator_reply_final_rule node)
                               enabled) as pattern.
                             destruct runtime_event as
                               [|start_certificates|message certificates];
                               cbn [echo_ir_initiator_reply_final_rule
                                 ir_event_pattern_matches] in pattern;
                               try discriminate.
                             exact
                               (echo_ir_initiator_reply_final_action_preserves_finished_parented
                                 config state successor message certificates
                                 invariant action).
                         *** contradiction.
Qed.

Lemma echo_ir_initial_finished_participants_parented
    (config : ir_protocol_config node echo_ir_signature) :
  echo_ir_finished_participants_parented config (@echo_initial_state node).
Proof.
  intros owner owner_not_root finished.
  discriminate.
Qed.

Theorem echo_ir_path_preserves_finished_participants_parented
    (config : ir_protocol_config node echo_ir_signature)
    (initial final : ir_protocol_state node echo_ir_signature) :
  ir_protocol_reachable node_eq config
    (ir_program_rules (@echo_program node)) initial final ->
  echo_ir_finished_participants_parented config initial ->
  echo_ir_finished_participants_parented config final.
Proof.
  intros reachable.
  induction reachable; intro invariant.
  - exact invariant.
  - apply IHreachable.
    eapply EchoStep_preserves_finished_participants_parented.
    + exact invariant.
    + exists rule. exact H.
Qed.

Theorem echo_reachable_finished_participants_parented
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) :
  echo_reachable node node_eq config state ->
  echo_ir_finished_participants_parented config state.
Proof.
  intro reachable.
  eapply echo_ir_path_preserves_finished_participants_parented.
  - exact reachable.
  - apply echo_ir_initial_finished_participants_parented.
Qed.

End EchoIRExecutableLifecycle.
