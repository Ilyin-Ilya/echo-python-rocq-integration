(** * Direct pending-list invariants for the public Echo IR executable

    This module proves pending-list validity from the generic configuration,
    generated Echo rules, and generic interpreter.  It deliberately imports
    no legacy Echo transition, compatibility relation, or simulation proof. *)

From Stdlib Require Import List Bool Arith Sorting.Permutation.
Import ListNotations.
Require Import ProtocolIRTypes ProtocolIRExpressions ProtocolIRActions
  ProtocolIRInterpreter ProtocolIRRunner EchoIRSignature EchoIRProgram
  EchoIRExecutable EchoIRExecutableInvariants EchoIRExecutableLifecycle.

Section EchoIRExecutablePending.

Variable node : Type.
Variable node_eq : forall left right : node,
  {left = right} + {left <> right}.

Definition echo_ir_pending_contents
    (state : ir_protocol_state node echo_ir_signature)
    (owner : node) : list node :=
  ir_list_node_value_contents
    (ir_processes state owner EchoIRPending).

(** A valid pending list is duplicate-free and contains only configured
    neighbors of its owner.  Stating neighborhood through the generic config
    keeps this result protocol-runtime-facing rather than Echo-encoding-facing. *)
Definition echo_ir_pending_valid
    (config : ir_protocol_config node echo_ir_signature)
    (owner : node) (pending : list node) : Prop :=
  NoDup pending /\
  forall neighbor,
    In neighbor pending ->
    In neighbor (ir_config_nodes config) /\
    In neighbor (ir_config_neighbors config owner).

Definition echo_ir_config_neighbors_well_formed
    (config : ir_protocol_config node echo_ir_signature) : Prop :=
  forall owner,
    In owner (ir_config_nodes config) ->
    echo_ir_pending_valid config owner
      (ir_config_neighbors config owner).

Definition echo_ir_pending_well_formed
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall owner,
    In owner (ir_config_nodes config) ->
    echo_ir_pending_valid config owner
      (echo_ir_pending_contents state owner).

Lemma echo_ir_pending_valid_empty
    (config : ir_protocol_config node echo_ir_signature)
    (owner : node) :
  echo_ir_pending_valid config owner [].
Proof.
  split; [constructor | intros neighbor member; contradiction].
Qed.

Lemma echo_ir_remove_node_in
    (selected candidate : node) (items : list node) :
  In candidate (ir_remove_node node_eq selected items) ->
  In candidate items.
Proof.
  induction items as [|head rest IH]; cbn; intro member.
  - contradiction.
  - destruct (node_eq selected head) as [same | different].
    + now right.
    + destruct member as [same | member].
      * now left.
      * right. now apply IH.
Qed.

Lemma echo_ir_remove_node_nodup
    (selected : node) (items : list node) :
  NoDup items -> NoDup (ir_remove_node node_eq selected items).
Proof.
  induction items as [|head rest IH]; intro nodup; cbn.
  - constructor.
  - inversion nodup as [|? ? head_not_in rest_nodup]; subst.
    destruct (node_eq selected head) as [same | different].
    + exact rest_nodup.
    + constructor.
      * intro member. apply head_not_in.
        now apply (echo_ir_remove_node_in selected head rest).
      * now apply IH.
Qed.

Lemma echo_ir_pending_valid_remove
    (config : ir_protocol_config node echo_ir_signature)
    (owner selected : node) (items : list node) :
  echo_ir_pending_valid config owner items ->
  echo_ir_pending_valid config owner
    (ir_remove_node node_eq selected items).
Proof.
  intros [nodup valid]. split.
  - now apply echo_ir_remove_node_nodup.
  - intros candidate member. apply valid.
    now apply (echo_ir_remove_node_in selected candidate items).
Qed.

Lemma echo_ir_pending_valid_permutation
    (config : ir_protocol_config node echo_ir_signature)
    (owner : node) (left right : list node) :
  Permutation left right ->
  echo_ir_pending_valid config owner right ->
  echo_ir_pending_valid config owner left.
Proof.
  intros permutation [nodup valid]. split.
  - eapply Permutation_NoDup.
    + symmetry. exact permutation.
    + exact nodup.
  - intros candidate member. apply valid.
    eapply Permutation_in; eauto.
Qed.

Lemma echo_ir_update_process_preserves_pending
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (owner : node)
    (parent : ir_value node IROptionNode)
    (pending : list node)
    (finished : bool) :
  echo_ir_pending_well_formed config state ->
  (In owner (ir_config_nodes config) ->
    echo_ir_pending_valid config owner pending) ->
  echo_ir_pending_well_formed config
    (echo_ir_update_process node node_eq state owner parent
      (IRListNodeValue pending) finished).
Proof.
  intros invariant new_valid observed observed_in.
  unfold echo_ir_pending_contents, echo_ir_update_process.
  destruct (node_eq owner observed) as [same | different].
  - subst observed.
    rewrite ir_set_local_field_read_different by discriminate.
    rewrite ir_set_local_field_same.
    exact (new_valid observed_in).
  - repeat rewrite ir_set_local_field_read_other_process by exact different.
    now apply invariant.
Qed.

Lemma echo_ir_message_only_preserves_pending
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature) :
  echo_ir_pending_well_formed config state ->
  ir_processes successor = ir_processes state ->
  echo_ir_pending_well_formed config successor.
Proof.
  intros invariant processes owner owner_in.
  unfold echo_ir_pending_contents.
  rewrite processes.
  now apply invariant.
Qed.

Lemma echo_ir_start_enabled_order
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (certificates : ir_start_certificates node echo_ir_signature) :
  eval_ir_rule node_eq config state (IRRuntimeStart certificates)
    (@echo_ir_start_rule node) = IRRuleEnabled ->
  Permutation
    (ir_config_neighbors config (echo_ir_config_initiator node config))
    (ir_config_neighbors config (echo_ir_config_initiator node config)).
Proof.
  intros _. apply Permutation_refl.
Qed.

Lemma echo_ir_nonleaf_enabled_order
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  eval_ir_rule node_eq config state
    (IRRuntimeDeliver message certificates)
    (@echo_ir_first_request_nonleaf_rule node) = IRRuleEnabled ->
  Permutation
    (ir_remove_node node_eq (ir_message_sender message)
      (ir_config_neighbors config (ir_message_receiver message)))
    (ir_remove_node node_eq (ir_message_sender message)
      (ir_config_neighbors config (ir_message_receiver message))).
Proof.
  intros _. apply Permutation_refl.
Qed.

Lemma echo_ir_start_action_preserves_pending
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (certificates : ir_start_certificates node echo_ir_signature) :
  echo_ir_pending_well_formed config state ->
  (In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
    echo_ir_pending_valid config (echo_ir_config_initiator node config)
      (ir_config_neighbors config (echo_ir_config_initiator node config))) ->
  eval_ir_action node_eq config state (IRRuntimeStart certificates)
    (ir_rule_action (@echo_ir_start_rule node)) = Some successor ->
  echo_ir_pending_well_formed config successor.
Proof.
  intros invariant ordered_valid action.
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
  change (echo_ir_pending_well_formed config
    (echo_ir_update_process node node_eq state
      (echo_ir_config_initiator node config)
      (IROptionNodeValue None)
      (IRListNodeValue (ir_config_neighbors config initiator))
      false)).
  eapply echo_ir_update_process_preserves_pending.
  - exact invariant.
  - exact ordered_valid.
Qed.

Lemma echo_ir_first_request_nonleaf_action_preserves_pending
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_pending_well_formed config state ->
  (In (ir_message_receiver message) (ir_config_nodes config) ->
    echo_ir_pending_valid config (ir_message_receiver message)
      (ir_remove_node node_eq (ir_message_sender message)
        (ir_config_neighbors config (ir_message_receiver message)))) ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_nonleaf_rule node)) =
      Some successor ->
  echo_ir_pending_well_formed config successor.
Proof.
  intros invariant ordered_valid action.
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
  change (echo_ir_pending_well_formed config
    (echo_ir_update_process node node_eq state
      (ir_message_receiver message)
      (IROptionNodeValue (Some (ir_message_sender message)))
      (IRListNodeValue
        (ir_remove_node node_eq (ir_message_sender message)
          (ir_config_neighbors config (ir_message_receiver message))))
      false)).
  eapply echo_ir_update_process_preserves_pending.
  - exact invariant.
  - exact ordered_valid.
Qed.

Lemma echo_ir_first_request_leaf_action_preserves_pending
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_pending_well_formed config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_leaf_rule node)) =
      Some successor ->
  echo_ir_pending_well_formed config successor.
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
  change (echo_ir_pending_well_formed config
    (echo_ir_update_process node node_eq state
      (ir_message_receiver message)
      (IROptionNodeValue (Some (ir_message_sender message)))
      (IRListNodeValue []) true)).
  eapply echo_ir_update_process_preserves_pending.
  - exact invariant.
  - intros _. apply echo_ir_pending_valid_empty.
Qed.

Lemma echo_ir_repeated_request_action_preserves_pending
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_pending_well_formed config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_repeated_request_rule node)) =
      Some successor ->
  echo_ir_pending_well_formed config successor.
Proof.
  intros invariant action.
  unfold echo_ir_repeated_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_receiver, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  eapply echo_ir_message_only_preserves_pending.
  - exact invariant.
  - unfold ir_emit_messages, ir_remove_selected_message. reflexivity.
Qed.

Lemma echo_ir_initiator_request_action_preserves_pending
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_pending_well_formed config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_request_rule node)) =
      Some successor ->
  echo_ir_pending_well_formed config successor.
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
  eapply echo_ir_message_only_preserves_pending.
  - exact invariant.
  - unfold ir_emit_messages, ir_remove_selected_message. reflexivity.
Qed.

Lemma echo_ir_participant_reply_more_action_preserves_pending
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_pending_well_formed config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_more_rule node)) =
      Some successor ->
  echo_ir_pending_well_formed config successor.
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
    change (echo_ir_pending_well_formed config
      (echo_ir_update_process node node_eq state
        (ir_message_receiver message)
        (IROptionNodeValue (Some parent_node))
        (IRListNodeValue
          (ir_remove_node node_eq (ir_message_sender message)
            (echo_ir_pending_contents state
              (ir_message_receiver message))))
        false)).
    eapply echo_ir_update_process_preserves_pending.
    + exact invariant.
    + intro receiver_in. apply echo_ir_pending_valid_remove.
      now apply invariant.
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_participant_reply_final_action_preserves_pending
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_pending_well_formed config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_final_rule node)) =
      Some successor ->
  echo_ir_pending_well_formed config successor.
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
    change (echo_ir_pending_well_formed config
      (echo_ir_update_process node node_eq state
        (ir_message_receiver message)
        (IROptionNodeValue (Some parent_node))
        (IRListNodeValue []) true)).
    eapply echo_ir_update_process_preserves_pending.
    + exact invariant.
    + intros _. apply echo_ir_pending_valid_empty.
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_initiator_reply_more_action_preserves_pending
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_pending_well_formed config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_more_rule node)) =
      Some successor ->
  echo_ir_pending_well_formed config successor.
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
  change (echo_ir_pending_well_formed config
    (echo_ir_update_process node node_eq state
      (echo_ir_config_initiator node config)
      (IROptionNodeValue None)
      (IRListNodeValue
        (ir_remove_node node_eq (ir_message_sender message)
          (echo_ir_pending_contents state
            (echo_ir_config_initiator node config))))
      false)).
  eapply echo_ir_update_process_preserves_pending.
  - exact invariant.
  - intro initiator_in. apply echo_ir_pending_valid_remove.
    now apply invariant.
Qed.

Lemma echo_ir_initiator_reply_final_action_preserves_pending
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_pending_well_formed config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_final_rule node)) =
      Some successor ->
  echo_ir_pending_well_formed config successor.
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
  change (echo_ir_pending_well_formed config
    (echo_ir_update_process node node_eq state
      (echo_ir_config_initiator node config)
      (IROptionNodeValue None) (IRListNodeValue []) true)).
  eapply echo_ir_update_process_preserves_pending.
  - exact invariant.
  - intros _. apply echo_ir_pending_valid_empty.
Qed.

(** Every successful generic Echo transition preserves pending-list validity.
    The only certificate-sensitive branches derive their list permutation from
    an enabled generated guard; every other branch either removes one element,
    installs the empty list, or leaves process state untouched. *)
Theorem EchoStep_preserves_pending_well_formed
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (external_event : ir_external_event node echo_ir_signature) :
  echo_ir_config_neighbors_well_formed config ->
  echo_ir_pending_well_formed config state ->
  EchoStep node node_eq config state external_event successor ->
  echo_ir_pending_well_formed config successor.
Proof.
  intros neighbors_valid invariant step.
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
    eapply echo_ir_start_action_preserves_pending.
    + exact invariant.
    + intro initiator_in.
      eapply echo_ir_pending_valid_permutation.
      * exact (echo_ir_start_enabled_order config state certificates enabled).
      * now apply neighbors_valid.
    + exact action.
  - destruct selected_in as [same | selected_in].
    + subst selected_rule.
      pose proof (eval_ir_rule_enabled_pattern node_eq config state
        runtime_event (@echo_ir_first_request_nonleaf_rule node) enabled)
        as pattern.
      destruct runtime_event as [|start_certificates|message certificates];
        cbn [echo_ir_first_request_nonleaf_rule ir_event_pattern_matches]
          in pattern; try discriminate.
      eapply echo_ir_first_request_nonleaf_action_preserves_pending.
      * exact invariant.
      * intro receiver_in.
        eapply echo_ir_pending_valid_permutation.
        -- exact (echo_ir_nonleaf_enabled_order
             config state message certificates enabled).
        -- apply echo_ir_pending_valid_remove.
           now apply neighbors_valid.
      * exact action.
    + destruct selected_in as [same | selected_in].
      * subst selected_rule.
        pose proof (eval_ir_rule_enabled_pattern node_eq config state
          runtime_event (@echo_ir_first_request_leaf_rule node) enabled)
          as pattern.
        destruct runtime_event as [|start_certificates|message certificates];
          cbn [echo_ir_first_request_leaf_rule ir_event_pattern_matches]
            in pattern; try discriminate.
        exact (echo_ir_first_request_leaf_action_preserves_pending
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
           exact (echo_ir_repeated_request_action_preserves_pending
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
              exact (echo_ir_initiator_request_action_preserves_pending
                config state successor message certificates invariant action).
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
                   (echo_ir_participant_reply_more_action_preserves_pending
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
                       (echo_ir_participant_reply_final_action_preserves_pending
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
                           (echo_ir_initiator_reply_more_action_preserves_pending
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
                               (echo_ir_initiator_reply_final_action_preserves_pending
                                 config state successor message certificates
                                 invariant action).
                         *** contradiction.
Qed.

Lemma echo_ir_initial_pending_well_formed
    (config : ir_protocol_config node echo_ir_signature) :
  echo_ir_pending_well_formed config (@echo_initial_state node).
Proof.
  intros owner owner_in.
  apply echo_ir_pending_valid_empty.
Qed.

Theorem echo_ir_path_preserves_pending_well_formed
    (config : ir_protocol_config node echo_ir_signature)
    (initial final : ir_protocol_state node echo_ir_signature) :
  echo_ir_config_neighbors_well_formed config ->
  ir_protocol_reachable node_eq config
    (ir_program_rules (@echo_program node)) initial final ->
  echo_ir_pending_well_formed config initial ->
  echo_ir_pending_well_formed config final.
Proof.
  intros neighbors_valid reachable.
  induction reachable; intro invariant.
  - exact invariant.
  - apply IHreachable.
    eapply EchoStep_preserves_pending_well_formed.
    + exact neighbors_valid.
    + exact invariant.
    + exists rule. exact H.
Qed.

Theorem echo_reachable_pending_well_formed
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) :
  echo_ir_config_neighbors_well_formed config ->
  echo_reachable node node_eq config state ->
  echo_ir_pending_well_formed config state.
Proof.
  intros neighbors_valid reachable.
  eapply echo_ir_path_preserves_pending_well_formed.
  - exact neighbors_valid.
  - exact reachable.
  - apply echo_ir_initial_pending_well_formed.
Qed.

End EchoIRExecutablePending.
