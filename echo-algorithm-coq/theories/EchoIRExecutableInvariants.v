(** * Direct reachable-state invariants for the public Echo IR executable

    This module proves properties from the generic Echo program, interpreter,
    and action semantics only.  It deliberately imports no legacy Echo state,
    transition language, compatibility relation, or simulation theorem. *)

From Stdlib Require Import List Bool Arith.
Import ListNotations.
Require Import ProtocolIRTypes ProtocolIRExpressions ProtocolIRActions
  ProtocolIRInterpreter ProtocolIRRunner EchoIRSignature EchoIRProgram
  EchoIRExecutable.

Section EchoIRExecutableInvariants.

Variable node : Type.
Variable node_eq : forall left right : node,
  {left = right} + {left <> right}.

(** The initiator is read from the intrinsically typed generic configuration;
    no compatibility encoding or second Echo configuration is involved. *)
Definition echo_ir_config_initiator
    (config : ir_protocol_config node echo_ir_signature) : node :=
  ir_node_value_contents (ir_config_fields config EchoIRInitiator).

Definition echo_ir_initiator_parent_none
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  ir_processes state (echo_ir_config_initiator config) EchoIRParent =
    IROptionNodeValue None.

Lemma echo_ir_enabled_noninitiator_guard
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature)
    (rule : ir_rule node echo_ir_signature) :
  eval_ir_rule node_eq config state
    (IRRuntimeDeliver message certificates) rule = IRRuleEnabled ->
  In (echo_ir_not_equal node (echo_ir_receiver node)
    (echo_ir_initiator node)) (ir_rule_guards rule) ->
  ir_message_receiver message <> echo_ir_config_initiator config.
Proof.
  intros enabled member.
  pose proof (eval_ir_rule_enabled_guard node_eq config state
    (IRRuntimeDeliver message certificates) rule
    (echo_ir_not_equal node (echo_ir_receiver node)
      (echo_ir_initiator node)) enabled member) as guard.
  unfold echo_ir_not_equal, echo_ir_equal, echo_ir_receiver,
    echo_ir_initiator in guard.
  cbn [eval_ir_expr] in guard.
  rewrite (ir_node_value_eta
    (ir_config_fields config EchoIRInitiator)) in guard.
  unfold echo_ir_config_initiator.
  cbn [ir_event_message ir_value_eqb] in guard.
  unfold ir_node_eqb in guard.
  destruct (node_eq (ir_message_receiver message)
    (ir_node_value_contents (ir_config_fields config EchoIRInitiator)))
    as [same | different].
  - discriminate guard.
  - exact different.
Qed.

Lemma echo_ir_start_action_parent_none
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (certificates : ir_start_certificates node echo_ir_signature) :
  eval_ir_action node_eq config state (IRRuntimeStart certificates)
    (ir_rule_action (@echo_ir_start_rule node)) = Some successor ->
  echo_ir_initiator_parent_none config successor.
Proof.
  intro action.
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
    with (IRNodeValue initiator) in action by (symmetry; exact initiator_value).
  repeat rewrite initiator_value in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs] in action.
  repeat rewrite initiator_value in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs] in action.
  injection action as <-.
  unfold echo_ir_initiator_parent_none, echo_ir_config_initiator.
  rewrite initiator_value.
  unfold ir_emit_messages, ir_set_global_field.
  cbn [ir_processes].
  rewrite ir_set_local_field_read_different by discriminate.
  rewrite ir_set_local_field_read_different by discriminate.
  apply ir_set_local_field_same.
Qed.

Lemma echo_ir_first_request_nonleaf_action_parent_none
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  ir_message_receiver message <> echo_ir_config_initiator config ->
  echo_ir_initiator_parent_none config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_nonleaf_rule node)) =
      Some successor ->
  echo_ir_initiator_parent_none config successor.
Proof.
  intros receiver_not_root parent_none action.
  unfold echo_ir_first_request_nonleaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_forward_order,
    echo_ir_remove, echo_ir_neighbors,
    echo_ir_emit_many, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs] in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs] in action.
  injection action as <-.
  unfold echo_ir_initiator_parent_none in *.
  unfold ir_emit_messages, ir_remove_selected_message.
  cbn [ir_processes].
  repeat rewrite ir_set_local_field_read_other_process
    by exact receiver_not_root.
  exact parent_none.
Qed.

Lemma echo_ir_first_request_leaf_action_parent_none
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  ir_message_receiver message <> echo_ir_config_initiator config ->
  echo_ir_initiator_parent_none config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_leaf_rule node)) =
      Some successor ->
  echo_ir_initiator_parent_none config successor.
Proof.
  intros receiver_not_root parent_none action.
  unfold echo_ir_first_request_leaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_empty_nodes,
    echo_ir_emit_one, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs] in action.
  injection action as <-.
  unfold echo_ir_initiator_parent_none in *.
  unfold ir_emit_messages, ir_remove_selected_message.
  cbn [ir_processes].
  repeat rewrite ir_set_local_field_read_other_process
    by exact receiver_not_root.
  exact parent_none.
Qed.

Lemma echo_ir_repeated_request_action_parent_none
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_initiator_parent_none config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_repeated_request_rule node)) =
      Some successor ->
  echo_ir_initiator_parent_none config successor.
Proof.
  intros parent_none action.
  unfold echo_ir_repeated_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_receiver, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs] in action.
  injection action as <-.
  unfold echo_ir_initiator_parent_none in *.
  unfold ir_emit_messages, ir_remove_selected_message.
  exact parent_none.
Qed.

Lemma echo_ir_initiator_request_action_parent_none
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_initiator_parent_none config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_request_rule node)) =
      Some successor ->
  echo_ir_initiator_parent_none config successor.
Proof.
  intros parent_none action.
  unfold echo_ir_initiator_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_initiator, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs] in action.
  rewrite (ir_node_value_eta
    (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs] in action.
  injection action as <-.
  unfold echo_ir_initiator_parent_none in *.
  unfold ir_emit_messages, ir_remove_selected_message.
  exact parent_none.
Qed.

Lemma echo_ir_participant_reply_more_action_parent_none
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  ir_message_receiver message <> echo_ir_config_initiator config ->
  echo_ir_initiator_parent_none config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_more_rule node)) =
      Some successor ->
  echo_ir_initiator_parent_none config successor.
Proof.
  intros receiver_not_root parent_none action.
  unfold echo_ir_participant_reply_more_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_receiver, echo_ir_expected_parent, echo_ir_some,
    echo_ir_removed_pending, echo_ir_remove, echo_ir_sender,
    echo_ir_pending, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  unfold echo_ir_receiver in action.
  unfold echo_ir_parent in action.
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
    unfold echo_ir_initiator_parent_none in *.
    unfold ir_remove_selected_message.
    cbn [ir_processes].
    repeat rewrite ir_set_local_field_read_other_process
      by exact receiver_not_root.
    exact parent_none.
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_participant_reply_final_action_parent_none
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  ir_message_receiver message <> echo_ir_config_initiator config ->
  echo_ir_initiator_parent_none config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_final_rule node)) =
      Some successor ->
  echo_ir_initiator_parent_none config successor.
Proof.
  intros receiver_not_root parent_none action.
  unfold echo_ir_participant_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_receiver, echo_ir_expected_parent, echo_ir_some,
    echo_ir_empty_nodes, echo_ir_emit_one, echo_ir_empty_payload,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs] in action.
  unfold echo_ir_receiver in action.
  unfold echo_ir_parent in action.
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
    unfold echo_ir_initiator_parent_none in *.
    unfold ir_emit_messages, ir_remove_selected_message.
    cbn [ir_processes].
    repeat rewrite ir_update_processes_different
      by exact receiver_not_root.
    exact parent_none.
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_initiator_reply_more_action_parent_none
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_more_rule node)) =
      Some successor ->
  echo_ir_initiator_parent_none config successor.
Proof.
  intro action.
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
      EchoIRPending))
    in action.
  cbn [echo_ir_config_initiator eval_ir_expr eval_ir_action
    ir_event_message] in action.
  injection action as <-.
  unfold echo_ir_initiator_parent_none, echo_ir_config_initiator.
  unfold ir_remove_selected_message.
  cbn [ir_processes].
  rewrite ir_set_local_field_read_different by discriminate.
  rewrite ir_set_local_field_read_different by discriminate.
  apply ir_set_local_field_same.
Qed.

Lemma echo_ir_initiator_reply_final_action_parent_none
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_final_rule node)) =
      Some successor ->
  echo_ir_initiator_parent_none config successor.
Proof.
  intro action.
  unfold echo_ir_initiator_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_empty_nodes,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr] in action.
  rewrite (ir_node_value_eta
    (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action] in action.
  injection action as <-.
  unfold echo_ir_initiator_parent_none, echo_ir_config_initiator.
  unfold ir_remove_selected_message.
  cbn [ir_processes].
  rewrite ir_set_local_field_read_different by discriminate.
  rewrite ir_set_local_field_read_different by discriminate.
  apply ir_set_local_field_same.
Qed.

(** Every one of the nine generated Echo rules preserves the initiator-parent
    invariant.  The proof obtains the actual selected rule, enabled guards,
    and evaluated action from the generic interpreter; it does not replay or
    translate the step through another Echo semantics. *)
Theorem EchoStep_preserves_initiator_parent_none
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (external_event : ir_external_event node echo_ir_signature) :
  echo_ir_initiator_parent_none config state ->
  EchoStep node node_eq config state external_event successor ->
  echo_ir_initiator_parent_none config successor.
Proof.
  intros parent_none step.
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
    exact (echo_ir_start_action_parent_none config
      state successor certificates action).
  - destruct selected_in as [same | selected_in].
    + subst selected_rule.
      pose proof (eval_ir_rule_enabled_pattern node_eq config state
        runtime_event (@echo_ir_first_request_nonleaf_rule node) enabled)
        as pattern.
      destruct runtime_event as [|start_certificates|message certificates];
        cbn [echo_ir_first_request_nonleaf_rule ir_event_pattern_matches]
          in pattern; try discriminate.
      pose proof (echo_ir_enabled_noninitiator_guard config state
        message certificates (@echo_ir_first_request_nonleaf_rule node)
        enabled ltac:(left; reflexivity)) as receiver_not_root.
      exact (echo_ir_first_request_nonleaf_action_parent_none
        config state successor message certificates
        receiver_not_root parent_none action).
    + destruct selected_in as [same | selected_in].
      * subst selected_rule.
        pose proof (eval_ir_rule_enabled_pattern node_eq config state
          runtime_event (@echo_ir_first_request_leaf_rule node) enabled)
          as pattern.
        destruct runtime_event as [|start_certificates|message certificates];
          cbn [echo_ir_first_request_leaf_rule ir_event_pattern_matches]
            in pattern; try discriminate.
        pose proof (echo_ir_enabled_noninitiator_guard config state
          message certificates (@echo_ir_first_request_leaf_rule node)
          enabled ltac:(left; reflexivity)) as receiver_not_root.
        exact (echo_ir_first_request_leaf_action_parent_none
          config state successor message certificates
          receiver_not_root parent_none action).
      * destruct selected_in as [same | selected_in].
        -- subst selected_rule.
           pose proof (eval_ir_rule_enabled_pattern node_eq config state
             runtime_event (@echo_ir_repeated_request_rule node) enabled)
             as pattern.
           destruct runtime_event as
             [|start_certificates|message certificates];
             cbn [echo_ir_repeated_request_rule ir_event_pattern_matches]
               in pattern; try discriminate.
           exact (echo_ir_repeated_request_action_parent_none
             config state successor message certificates
             parent_none action).
        -- destruct selected_in as [same | selected_in].
           ++ subst selected_rule.
              pose proof (eval_ir_rule_enabled_pattern node_eq config state
                runtime_event (@echo_ir_initiator_request_rule node) enabled)
                as pattern.
              destruct runtime_event as
                [|start_certificates|message certificates];
                cbn [echo_ir_initiator_request_rule ir_event_pattern_matches]
                  in pattern; try discriminate.
              exact (echo_ir_initiator_request_action_parent_none
                config state successor message certificates
                parent_none action).
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
                 pose proof (echo_ir_enabled_noninitiator_guard config state
                   message certificates
                   (@echo_ir_participant_reply_more_rule node)
                   enabled ltac:(left; reflexivity)) as receiver_not_root.
                 exact (echo_ir_participant_reply_more_action_parent_none
                   config state successor message certificates
                   receiver_not_root parent_none action).
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
                     pose proof (echo_ir_enabled_noninitiator_guard
                       config state message certificates
                       (@echo_ir_participant_reply_final_rule node)
                       enabled ltac:(left; reflexivity))
                       as receiver_not_root.
                     exact
                       (echo_ir_participant_reply_final_action_parent_none
                         config state successor message
                         certificates receiver_not_root parent_none action).
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
                           (echo_ir_initiator_reply_more_action_parent_none
                             config state successor message
                             certificates action).
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
                               (echo_ir_initiator_reply_final_action_parent_none
                                 config state successor message
                                 certificates action).
                         *** contradiction.
Qed.

(** Initialization sets every process parent to [None], including the
    initiator read from the generic configuration. *)
Lemma echo_ir_initial_initiator_parent_none
    (config : ir_protocol_config node echo_ir_signature) :
  echo_ir_initiator_parent_none config (@echo_initial_state node).
Proof. reflexivity. Qed.

Theorem echo_ir_path_preserves_initiator_parent_none
    (config : ir_protocol_config node echo_ir_signature)
    (initial final : ir_protocol_state node echo_ir_signature) :
  ir_protocol_reachable node_eq config
    (ir_program_rules (@echo_program node)) initial final ->
  echo_ir_initiator_parent_none config initial ->
  echo_ir_initiator_parent_none config final.
Proof.
  intros reachable.
  induction reachable; intro parent_none.
  - exact parent_none.
  - apply IHreachable.
    eapply EchoStep_preserves_initiator_parent_none.
    + exact parent_none.
    + exists rule. exact H.
Qed.

(** The initiator remains parentless in every state reachable through the
    public generic Echo step relation. *)
Theorem echo_reachable_initiator_parent_none
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) :
  echo_reachable node node_eq config state ->
  echo_ir_initiator_parent_none config state.
Proof.
  intro reachable.
  eapply echo_ir_path_preserves_initiator_parent_none.
  - exact reachable.
  - apply echo_ir_initial_initiator_parent_none.
Qed.

End EchoIRExecutableInvariants.
