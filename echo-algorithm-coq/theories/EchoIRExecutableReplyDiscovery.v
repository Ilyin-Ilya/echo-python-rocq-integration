(** * Direct reply-receiver discovery for generic Echo IR

    Replies are sent only to processes that have left their generated initial
    local state.  The inductive support invariant also records that installed
    parent targets and queued-request senders are discovered; those are the
    two causal facts used when a rule creates a new reply. *)

From Stdlib Require Import List Bool Arith Sorting.Permutation.
Import ListNotations.
Require Import ProtocolIRTypes ProtocolIRExpressions ProtocolIRActions
  ProtocolIRInterpreter ProtocolIRRunner EchoIRSignature EchoIRProgram
  EchoIRExecutable EchoIRExecutableInvariants EchoIRExecutableLifecycle
  EchoIRExecutablePending EchoIRExecutableDiscovery EchoIRExecutableTopology
  EchoIRExecutableRequestAccounting EchoIRExecutableRequestParent.

Section EchoIRExecutableReplyDiscovery.

Variable node : Type.
Variable node_eq : forall left right : node,
  {left = right} + {left <> right}.

Definition echo_ir_parent_targets_discovered
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall child parent,
    In child (ir_config_nodes config) ->
    echo_ir_parent_value node state child = Some parent ->
    echo_ir_local_discovered node state parent.

Definition echo_ir_request_senders_discovered
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall message,
    In message (ir_message_store state) ->
    ir_message_kind message = EchoIRRequest ->
    echo_ir_local_discovered node state (ir_message_sender message).

Definition echo_ir_reply_receivers_discovered
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall message,
    In message (ir_message_store state) ->
    ir_message_kind message = EchoIRReply ->
    echo_ir_local_discovered node state (ir_message_receiver message).

Definition echo_ir_reply_discovery_support
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  echo_ir_parent_targets_discovered config state /\
  echo_ir_request_senders_discovered state /\
  echo_ir_reply_receivers_discovered state.

Lemma echo_ir_update_process_other_discovery
    (state : ir_protocol_state node echo_ir_signature)
    (owner observed : node) (parent : ir_value node IROptionNode)
    (pending : ir_value node IRListNode) (finished : bool) :
  owner <> observed ->
  echo_ir_local_discovered node state observed ->
  echo_ir_local_discovered node
    (echo_ir_update_process node node_eq state owner
      parent pending finished) observed.
Proof.
  intros different discovered.
  unfold echo_ir_local_discovered, echo_ir_parent_value,
    echo_ir_pending_value, echo_ir_finished_value,
    echo_ir_update_process in discovered |- *.
  repeat rewrite ir_set_local_field_read_other_process
    by exact different.
  exact discovered.
Qed.

Lemma echo_ir_update_process_some_owner_discovered
    (state : ir_protocol_state node echo_ir_signature)
    (owner parent : node) (pending : ir_value node IRListNode)
    (finished : bool) :
  echo_ir_local_discovered node
    (echo_ir_update_process node node_eq state owner
      (IROptionNodeValue (Some parent)) pending finished) owner.
Proof.
  left. unfold echo_ir_parent_value, echo_ir_update_process.
  rewrite ir_set_local_field_read_different by discriminate.
  rewrite ir_set_local_field_read_different by discriminate.
  rewrite ir_set_local_field_same. discriminate.
Qed.

Lemma echo_ir_update_process_nonempty_owner_discovered
    (state : ir_protocol_state node echo_ir_signature)
    (owner : node) (parent : ir_value node IROptionNode)
    (pending : list node) (finished : bool) :
  pending <> [] ->
  echo_ir_local_discovered node
    (echo_ir_update_process node node_eq state owner parent
      (IRListNodeValue pending) finished) owner.
Proof.
  intro nonempty. right. left.
  unfold echo_ir_pending_value, echo_ir_update_process.
  rewrite ir_set_local_field_read_different by discriminate.
  rewrite ir_set_local_field_same. exact nonempty.
Qed.

Lemma echo_ir_update_process_finished_owner_discovered
    (state : ir_protocol_state node echo_ir_signature)
    (owner : node) (parent : ir_value node IROptionNode)
    (pending : ir_value node IRListNode) :
  echo_ir_local_discovered node
    (echo_ir_update_process node node_eq state owner parent pending true) owner.
Proof.
  right. right.
  unfold echo_ir_finished_value, echo_ir_update_process.
  rewrite ir_set_local_field_same. discriminate.
Qed.

Lemma echo_ir_update_process_discovery_monotone
    (state : ir_protocol_state node echo_ir_signature)
    (owner : node) (parent : ir_value node IROptionNode)
    (pending : ir_value node IRListNode) (finished : bool) :
  echo_ir_local_discovered node
    (echo_ir_update_process node node_eq state owner
      parent pending finished) owner ->
  forall observed,
    echo_ir_local_discovered node state observed ->
    echo_ir_local_discovered node
      (echo_ir_update_process node node_eq state owner
        parent pending finished) observed.
Proof.
  intros owner_discovered observed discovered.
  destruct (node_eq owner observed) as [same | different].
  - now subst observed.
  - now apply echo_ir_update_process_other_discovery.
Qed.

Lemma echo_ir_update_process_some_preserves_reply_discovery_support
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (owner parent : node) (pending : ir_value node IRListNode)
    (finished : bool) :
  In owner (ir_config_nodes config) ->
  echo_ir_reply_discovery_support config state ->
  echo_ir_local_discovered node state parent ->
  echo_ir_reply_discovery_support config
    (echo_ir_update_process node node_eq state owner
      (IROptionNodeValue (Some parent)) pending finished).
Proof.
  intros owner_in [parents [requests replies]] parent_discovered.
  pose proof (echo_ir_update_process_some_owner_discovered
    state owner parent pending finished) as owner_discovered.
  pose proof (echo_ir_update_process_discovery_monotone
    state owner (IROptionNodeValue (Some parent)) pending finished
    owner_discovered) as monotone.
  split.
  - intros child target child_in installed.
    unfold echo_ir_parent_value, echo_ir_update_process in installed.
    destruct (node_eq owner child) as [same | different].
    + subst child.
      rewrite ir_set_local_field_read_different in installed by discriminate.
      rewrite ir_set_local_field_read_different in installed by discriminate.
      rewrite ir_set_local_field_same in installed.
      injection installed as <-. now apply monotone.
    + repeat rewrite ir_set_local_field_read_other_process in installed
        by exact different.
      now apply monotone, (parents child target child_in).
  - split; intros message queued kind.
    + apply monotone. apply requests with (message := message); assumption.
    + apply monotone. apply replies with (message := message); assumption.
Qed.

Lemma echo_ir_update_process_none_preserves_reply_discovery_support
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (owner : node) (pending : ir_value node IRListNode)
    (finished : bool) :
  echo_ir_reply_discovery_support config state ->
  echo_ir_local_discovered node
    (echo_ir_update_process node node_eq state owner
      (IROptionNodeValue None) pending finished) owner ->
  echo_ir_reply_discovery_support config
    (echo_ir_update_process node node_eq state owner
      (IROptionNodeValue None) pending finished).
Proof.
  intros [parents [requests replies]] owner_discovered.
  pose proof (echo_ir_update_process_discovery_monotone
    state owner (IROptionNodeValue None) pending finished owner_discovered)
    as monotone.
  split.
  - intros child target child_in installed.
    unfold echo_ir_parent_value, echo_ir_update_process in installed.
    destruct (node_eq owner child) as [same | different].
    + subst child.
      rewrite ir_set_local_field_read_different in installed by discriminate.
      rewrite ir_set_local_field_read_different in installed by discriminate.
      rewrite ir_set_local_field_same in installed. discriminate.
    + repeat rewrite ir_set_local_field_read_other_process in installed
        by exact different.
      now apply monotone, (parents child target child_in).
  - split; intros message queued kind.
    + apply monotone. apply requests with (message := message); assumption.
    + apply monotone. apply replies with (message := message); assumption.
Qed.

Lemma echo_ir_remove_preserves_reply_discovery_support
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (selected_id : nat) :
  echo_ir_reply_discovery_support config state ->
  echo_ir_reply_discovery_support config
    (ir_remove_selected_message state selected_id).
Proof.
  intros [parents [requests replies]]. split.
  - exact parents.
  - split; intros message queued kind.
    + apply requests with (message := message); [|exact kind].
      cbn [ir_remove_selected_message ir_message_store] in queued.
      now apply (echo_ir_remove_message_in node selected_id _ message).
    + apply replies with (message := message); [|exact kind].
      cbn [ir_remove_selected_message ir_message_store] in queued.
      now apply (echo_ir_remove_message_in node selected_id _ message).
Qed.

Lemma echo_ir_emit_preserves_reply_discovery_support
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (kind : echo_ir_message_kind) (sender : node)
    (receivers : list node)
    (payload : ir_payload_store node echo_ir_signature) :
  echo_ir_reply_discovery_support config state ->
  (kind = EchoIRRequest -> echo_ir_local_discovered node state sender) ->
  (kind = EchoIRReply -> forall receiver, In receiver receivers ->
    echo_ir_local_discovered node state receiver) ->
  echo_ir_reply_discovery_support config
    (ir_emit_messages state kind sender receivers payload).
Proof.
  intros [parents [requests replies]] request_sender reply_receivers.
  split.
  - exact parents.
  - split; intros message queued message_kind;
      cbn [ir_emit_messages ir_message_store] in queued;
      apply in_app_or in queued as [old | emitted].
    + now apply requests with (message := message).
    + destruct (echo_ir_materialized_message_fields node
        (ir_next_message_id state) kind sender receivers payload
        message emitted) as [same_sender receiver_in].
      rewrite same_sender. apply request_sender.
      rewrite <- message_kind. symmetry.
      now apply (echo_ir_materialized_message_kind node
        (ir_next_message_id state) kind sender receivers payload message).
    + now apply replies with (message := message).
    + destruct (echo_ir_materialized_message_fields node
        (ir_next_message_id state) kind sender receivers payload
        message emitted) as [same_sender receiver_in].
      apply reply_receivers; [|exact receiver_in].
      rewrite <- message_kind. symmetry.
      now apply (echo_ir_materialized_message_kind node
        (ir_next_message_id state) kind sender receivers payload message).
Qed.

Lemma echo_ir_updated_some_parent_value
    (state : ir_protocol_state node echo_ir_signature)
    (owner parent : node) (pending : ir_value node IRListNode)
    (finished : bool) :
  echo_ir_parent_value node
    (echo_ir_update_process node node_eq state owner
      (IROptionNodeValue (Some parent)) pending finished) owner =
    Some parent.
Proof.
  unfold echo_ir_parent_value, echo_ir_update_process.
  rewrite ir_set_local_field_read_different by discriminate.
  rewrite ir_set_local_field_read_different by discriminate.
  now rewrite ir_set_local_field_same.
Qed.

Lemma echo_ir_start_action_establishes_reply_discovery
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (certificates : ir_start_certificates node echo_ir_signature) :
  (forall owner,
    In owner (ir_config_nodes config) ->
    echo_ir_parent_value node state owner = None) ->
  ir_message_store state = [] ->
  eval_ir_action node_eq config state (IRRuntimeStart certificates)
    (ir_rule_action (@echo_ir_start_rule node)) = Some successor ->
  echo_ir_reply_discovery_support config successor.
Proof.
  intros parents_none store_empty action.
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
  set (updated := echo_ir_update_process node node_eq state
    (echo_ir_config_initiator node config) (IROptionNodeValue None)
    (IRListNodeValue (ir_config_neighbors config
      (echo_ir_config_initiator node config))) false).
  set (started := ir_set_global_field updated EchoIRStarted
    (IRBoolValue true)).
  split.
  - intros child parent child_in installed.
    pose proof (parents_none child child_in) as child_none.
    unfold echo_ir_parent_value in child_none.
    unfold echo_ir_parent_value, ir_emit_messages, started,
      ir_set_global_field, updated, echo_ir_update_process in installed.
    cbn [ir_processes] in installed.
    destruct (node_eq (echo_ir_config_initiator node config) child)
      as [same | different].
    + subst child.
      rewrite ir_set_local_field_read_different in installed by discriminate.
      rewrite ir_set_local_field_read_different in installed by discriminate.
      rewrite ir_set_local_field_same in installed. discriminate.
    + repeat rewrite ir_set_local_field_read_other_process in installed
        by exact different.
      rewrite child_none in installed. discriminate.
  - split.
    + intros message queued request_kind.
      cbn [ir_emit_messages ir_message_store] in queued.
      apply in_app_or in queued as [old | emitted].
      * change (In message (ir_message_store state)) in old.
        rewrite store_empty in old. contradiction.
      * destruct (echo_ir_materialized_message_fields node
          (ir_next_message_id started) EchoIRRequest
          (echo_ir_config_initiator node config)
          (ir_config_neighbors config
            (echo_ir_config_initiator node config)) []
          message emitted) as [same_sender receiver_in].
        rewrite same_sender.
        unfold ir_emit_messages, started, ir_set_global_field.
        change (echo_ir_local_discovered node updated
          (echo_ir_config_initiator node config)).
        unfold updated.
        apply echo_ir_update_process_nonempty_owner_discovered.
        intro empty. rewrite empty in receiver_in. contradiction.
    + intros message queued reply_kind.
      cbn [ir_emit_messages ir_message_store] in queued.
      apply in_app_or in queued as [old | emitted].
      * change (In message (ir_message_store state)) in old.
        rewrite store_empty in old. contradiction.
      * pose proof (echo_ir_materialized_message_kind node
          (ir_next_message_id started) EchoIRRequest
          (echo_ir_config_initiator node config)
          (ir_config_neighbors config
            (echo_ir_config_initiator node config)) []
          message emitted) as emitted_kind.
        rewrite reply_kind in emitted_kind. discriminate.
Qed.

Lemma echo_ir_first_request_nonleaf_action_preserves_reply_discovery
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_reply_discovery_support config state ->
  In (ir_message_receiver message) (ir_config_nodes config) ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRRequest ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_nonleaf_rule node)) =
      Some successor ->
  echo_ir_reply_discovery_support config successor.
Proof.
  intros support receiver_in queued request_kind action.
  unfold echo_ir_first_request_nonleaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_forward_order,
    echo_ir_remove, echo_ir_neighbors,
    echo_ir_emit_many, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
    ir_event_message] in action.
  injection action as <-.
  set (updated := echo_ir_update_process node node_eq state
    (ir_message_receiver message)
    (IROptionNodeValue (Some (ir_message_sender message)))
    (IRListNodeValue
      (ir_remove_node node_eq (ir_message_sender message)
        (ir_config_neighbors config (ir_message_receiver message)))) false).
  set (removed := ir_remove_selected_message updated
    (ir_message_id message)).
  assert (sender_discovered :
    echo_ir_local_discovered node state (ir_message_sender message)).
  { exact (proj1 (proj2 support) message queued request_kind). }
  assert (updated_support : echo_ir_reply_discovery_support config updated).
  { unfold updated. now apply
      echo_ir_update_process_some_preserves_reply_discovery_support. }
  assert (removed_support : echo_ir_reply_discovery_support config removed).
  { unfold removed. now apply echo_ir_remove_preserves_reply_discovery_support. }
  apply echo_ir_emit_preserves_reply_discovery_support.
  - exact removed_support.
  - intros _. unfold removed, updated, ir_remove_selected_message.
    apply echo_ir_update_process_some_owner_discovered.
  - discriminate.
Qed.

Lemma echo_ir_first_request_leaf_action_preserves_reply_discovery
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_reply_discovery_support config state ->
  In (ir_message_receiver message) (ir_config_nodes config) ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRRequest ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_leaf_rule node)) =
      Some successor ->
  echo_ir_reply_discovery_support config successor.
Proof.
  intros support receiver_in queued request_kind action.
  unfold echo_ir_first_request_leaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_empty_nodes,
    echo_ir_emit_one, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  set (updated := echo_ir_update_process node node_eq state
    (ir_message_receiver message)
    (IROptionNodeValue (Some (ir_message_sender message)))
    (IRListNodeValue []) true).
  set (removed := ir_remove_selected_message updated
    (ir_message_id message)).
  assert (sender_discovered :
    echo_ir_local_discovered node state (ir_message_sender message)).
  { exact (proj1 (proj2 support) message queued request_kind). }
  assert (updated_support : echo_ir_reply_discovery_support config updated).
  { unfold updated. now apply
      echo_ir_update_process_some_preserves_reply_discovery_support. }
  assert (removed_support : echo_ir_reply_discovery_support config removed).
  { unfold removed. now apply echo_ir_remove_preserves_reply_discovery_support. }
  apply echo_ir_emit_preserves_reply_discovery_support.
  - exact removed_support.
  - discriminate.
  - intros _ receiver [same | impossible]; [subst receiver | contradiction].
    unfold removed, ir_remove_selected_message.
    apply (proj1 updated_support (ir_message_receiver message)
      (ir_message_sender message)).
    + exact receiver_in.
    + unfold updated. apply echo_ir_updated_some_parent_value.
Qed.

Lemma echo_ir_request_reply_action_preserves_reply_discovery
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature)
    (rule : ir_rule node echo_ir_signature)
    (reply_sender : node) :
  ir_rule_action rule =
    echo_ir_sequence node
      [IRRemoveSelectedMessageAction;
       echo_ir_emit_one node EchoIRReply
         (IRLiteral (IRNodeValue reply_sender)) (echo_ir_sender node)] ->
  echo_ir_reply_discovery_support config state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRRequest ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates) (ir_rule_action rule) =
      Some successor ->
  echo_ir_reply_discovery_support config successor.
Proof.
  intros rule_action support queued request_kind action.
  rewrite rule_action in action.
  unfold echo_ir_emit_one, echo_ir_sender, echo_ir_empty_payload in action.
  cbn [echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  assert (sender_discovered :
    echo_ir_local_discovered node state (ir_message_sender message)).
  { exact (proj1 (proj2 support) message queued request_kind). }
  apply echo_ir_emit_preserves_reply_discovery_support.
  - now apply echo_ir_remove_preserves_reply_discovery_support.
  - discriminate.
  - intros _ receiver [same | impossible]; [subst receiver | contradiction].
    exact sender_discovered.
Qed.

Lemma echo_ir_repeated_request_action_preserves_reply_discovery
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_reply_discovery_support config state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRRequest ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_repeated_request_rule node)) =
      Some successor ->
  echo_ir_reply_discovery_support config successor.
Proof.
  intros support queued request_kind action.
  unfold echo_ir_repeated_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_receiver, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  assert (sender_discovered :
    echo_ir_local_discovered node state (ir_message_sender message)).
  { exact (proj1 (proj2 support) message queued request_kind). }
  apply echo_ir_emit_preserves_reply_discovery_support.
  - now apply echo_ir_remove_preserves_reply_discovery_support.
  - discriminate.
  - intros _ receiver [same | impossible]; [subst receiver | contradiction].
    exact sender_discovered.
Qed.

Lemma echo_ir_initiator_request_action_preserves_reply_discovery
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_reply_discovery_support config state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRRequest ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_request_rule node)) =
      Some successor ->
  echo_ir_reply_discovery_support config successor.
Proof.
  intros support queued request_kind action.
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
  assert (sender_discovered :
    echo_ir_local_discovered node state (ir_message_sender message)).
  { exact (proj1 (proj2 support) message queued request_kind). }
  apply echo_ir_emit_preserves_reply_discovery_support.
  - now apply echo_ir_remove_preserves_reply_discovery_support.
  - discriminate.
  - intros _ receiver [same | impossible]; [subst receiver | contradiction].
    exact sender_discovered.
Qed.

Lemma echo_ir_participant_reply_more_action_preserves_reply_discovery
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_reply_discovery_support config state ->
  In (ir_message_receiver message) (ir_config_nodes config) ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_more_rule node)) =
      Some successor ->
  echo_ir_reply_discovery_support config successor.
Proof.
  intros support receiver_in action.
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
    apply echo_ir_remove_preserves_reply_discovery_support.
    apply echo_ir_update_process_some_preserves_reply_discovery_support.
    + exact receiver_in.
    + exact support.
    + apply (proj1 support (ir_message_receiver message) parent_node
        receiver_in).
      unfold echo_ir_parent_value. rewrite parent_value. reflexivity.
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_participant_reply_final_action_preserves_reply_discovery
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_reply_discovery_support config state ->
  In (ir_message_receiver message) (ir_config_nodes config) ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_final_rule node)) =
      Some successor ->
  echo_ir_reply_discovery_support config successor.
Proof.
  intros support receiver_in action.
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
    set (updated := echo_ir_update_process node node_eq state
      (ir_message_receiver message) (IROptionNodeValue (Some parent_node))
      (IRListNodeValue []) true).
    set (removed := ir_remove_selected_message updated
      (ir_message_id message)).
    assert (parent_discovered : echo_ir_local_discovered node state parent_node).
    { apply (proj1 support (ir_message_receiver message) parent_node receiver_in).
      unfold echo_ir_parent_value. rewrite parent_value. reflexivity. }
    assert (updated_support : echo_ir_reply_discovery_support config updated).
    { unfold updated. now apply
        echo_ir_update_process_some_preserves_reply_discovery_support. }
    assert (removed_support : echo_ir_reply_discovery_support config removed).
    { unfold removed. now apply echo_ir_remove_preserves_reply_discovery_support. }
    apply echo_ir_emit_preserves_reply_discovery_support.
    + exact removed_support.
    + discriminate.
    + intros _ receiver [same | impossible]; [subst receiver | contradiction].
      unfold removed, ir_remove_selected_message.
      exact (proj1 updated_support (ir_message_receiver message) parent_node
        receiver_in
        (ltac:(unfold updated; apply echo_ir_updated_some_parent_value))).
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_initiator_reply_more_action_preserves_reply_discovery
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_reply_discovery_support config state ->
  ir_remove_node node_eq (ir_message_sender message)
    (ir_list_node_value_contents
      (ir_processes state
        (echo_ir_config_initiator node config) EchoIRPending)) <> [] ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_more_rule node)) =
      Some successor ->
  echo_ir_reply_discovery_support config successor.
Proof.
  intros support remaining_nonempty action.
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
  apply echo_ir_remove_preserves_reply_discovery_support.
  apply echo_ir_update_process_none_preserves_reply_discovery_support.
  - exact support.
  - now apply echo_ir_update_process_nonempty_owner_discovered.
Qed.

Lemma echo_ir_initiator_reply_final_action_preserves_reply_discovery
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_reply_discovery_support config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_final_rule node)) =
      Some successor ->
  echo_ir_reply_discovery_support config successor.
Proof.
  intros support action. unfold echo_ir_initiator_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_empty_nodes,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta
    (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  apply echo_ir_remove_preserves_reply_discovery_support.
  apply echo_ir_update_process_none_preserves_reply_discovery_support.
  - exact support.
  - apply echo_ir_update_process_finished_owner_discovered.
Qed.

Lemma echo_ir_enabled_removed_pending_nonempty
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature)
    (rule : ir_rule node echo_ir_signature) :
  eval_ir_rule node_eq config state
    (IRRuntimeDeliver message certificates) rule = IRRuleEnabled ->
  In (echo_ir_nonempty node
      (echo_ir_removed_pending node (echo_ir_initiator node)))
    (ir_rule_guards rule) ->
  ir_remove_node node_eq (ir_message_sender message)
    (ir_list_node_value_contents
      (ir_processes state
        (echo_ir_config_initiator node config) EchoIRPending)) <> [].
Proof.
  intros enabled member.
  pose proof (eval_ir_rule_enabled_guard node_eq config state
    (IRRuntimeDeliver message certificates) rule
    (echo_ir_nonempty node
      (echo_ir_removed_pending node (echo_ir_initiator node)))
    enabled member) as guard.
  unfold echo_ir_nonempty, echo_ir_is_empty, echo_ir_removed_pending,
    echo_ir_remove, echo_ir_sender, echo_ir_pending,
    echo_ir_initiator in guard.
  cbn [eval_ir_expr ir_event_message] in guard.
  rewrite (ir_node_value_eta
    (ir_config_fields config EchoIRInitiator)) in guard.
  cbn [eval_ir_expr ir_event_message] in guard.
  rewrite (ir_list_node_value_eta
    (ir_processes state
      (ir_node_value_contents (ir_config_fields config EchoIRInitiator))
      EchoIRPending)) in guard.
  cbn [eval_ir_expr ir_event_message] in guard.
  injection guard as nonempty.
  destruct (ir_remove_node node_eq (ir_message_sender message)
    (ir_list_node_value_contents
      (ir_processes state
        (ir_node_value_contents (ir_config_fields config EchoIRInitiator))
        EchoIRPending)))
    as [|first rest] eqn:remaining.
  - cbn in nonempty. discriminate.
  - intro impossible.
    unfold echo_ir_config_initiator in impossible.
    rewrite remaining in impossible. discriminate.
Qed.

Theorem EchoStep_preserves_reply_discovery_support
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (external_event : ir_external_event node echo_ir_signature) :
  echo_ir_topology_well_formed node config state ->
  echo_ir_reply_discovery_support config state ->
  EchoStep node node_eq config state external_event successor ->
  echo_ir_reply_discovery_support config successor.
Proof.
  intros topology support step.
  destruct (echo_ir_step_success_components node node_eq
    config state successor external_event step) as
    [rule_id [runtime_event [selected_rule
      [resolved [selected
        [selected_in [enabled [identifier action]]]]]]]].
  change (In selected_rule (@echo_ir_rules node)) in selected_in.
  unfold echo_ir_rules in selected_in. cbn in selected_in.
  destruct selected_in as [same | selected_in].
  - subst selected_rule.
    pose proof (eval_ir_rule_enabled_pattern node_eq config state
      runtime_event (@echo_ir_start_rule node) enabled) as pattern.
    destruct runtime_event as [|certificates|message certificates];
      cbn [echo_ir_start_rule ir_event_pattern_matches] in pattern;
      try discriminate.
    eapply echo_ir_start_action_establishes_reply_discovery.
    + exact (echo_ir_start_enabled_configured_parent_none node node_eq
        config state certificates enabled).
    + exact (echo_ir_start_enabled_store_empty node node_eq
        config state certificates enabled).
    + exact action.
  - destruct selected_in as [same | selected_in].
    + subst selected_rule.
      pose proof (eval_ir_rule_enabled_pattern node_eq config state
        runtime_event (@echo_ir_first_request_nonleaf_rule node) enabled)
        as pattern.
      destruct runtime_event as [|start_certificates|message certificates];
        cbn [echo_ir_first_request_nonleaf_rule ir_event_pattern_matches]
          in pattern; try discriminate.
      pose proof (echo_ir_resolved_delivery_queued node
        state external_event message certificates resolved) as queued.
      pose proof ((proj2 topology) message queued) as message_edge.
      destruct message_edge as [sender_in [receiver_in forward_edge]].
      assert (request_kind : ir_message_kind message = EchoIRRequest).
      { exact (echo_ir_enabled_request_pattern_kind node node_eq config state
          message certificates (@echo_ir_first_request_nonleaf_rule node)
          eq_refl enabled). }
      eapply echo_ir_first_request_nonleaf_action_preserves_reply_discovery;
        eauto.
    + destruct selected_in as [same | selected_in].
      * subst selected_rule.
        pose proof (eval_ir_rule_enabled_pattern node_eq config state
          runtime_event (@echo_ir_first_request_leaf_rule node) enabled)
          as pattern.
        destruct runtime_event as [|start_certificates|message certificates];
          cbn [echo_ir_first_request_leaf_rule ir_event_pattern_matches]
            in pattern; try discriminate.
        pose proof (echo_ir_resolved_delivery_queued node
          state external_event message certificates resolved) as queued.
        pose proof ((proj2 topology) message queued) as message_edge.
        destruct message_edge as [sender_in [receiver_in forward_edge]].
        assert (request_kind : ir_message_kind message = EchoIRRequest).
        { exact (echo_ir_enabled_request_pattern_kind node node_eq config state
            message certificates (@echo_ir_first_request_leaf_rule node)
            eq_refl enabled). }
        eapply echo_ir_first_request_leaf_action_preserves_reply_discovery;
          eauto.
      * destruct selected_in as [same | selected_in].
        -- subst selected_rule.
           pose proof (eval_ir_rule_enabled_pattern node_eq config state
             runtime_event (@echo_ir_repeated_request_rule node) enabled)
             as pattern.
           destruct runtime_event as [|start_certificates|message certificates];
             cbn [echo_ir_repeated_request_rule ir_event_pattern_matches]
               in pattern; try discriminate.
           pose proof (echo_ir_resolved_delivery_queued node
             state external_event message certificates resolved) as queued.
           assert (request_kind : ir_message_kind message = EchoIRRequest).
           { exact (echo_ir_enabled_request_pattern_kind node node_eq
               config state message certificates
               (@echo_ir_repeated_request_rule node) eq_refl enabled). }
           eapply echo_ir_repeated_request_action_preserves_reply_discovery;
             eauto.
        -- destruct selected_in as [same | selected_in].
           ++ subst selected_rule.
              pose proof (eval_ir_rule_enabled_pattern node_eq config state
                runtime_event (@echo_ir_initiator_request_rule node) enabled)
                as pattern.
              destruct runtime_event as
                [|start_certificates|message certificates];
                cbn [echo_ir_initiator_request_rule ir_event_pattern_matches]
                  in pattern; try discriminate.
              pose proof (echo_ir_resolved_delivery_queued node
                state external_event message certificates resolved) as queued.
              assert (request_kind : ir_message_kind message = EchoIRRequest).
              { exact (echo_ir_enabled_request_pattern_kind node node_eq
                  config state message certificates
                  (@echo_ir_initiator_request_rule node) eq_refl enabled). }
              eapply
                echo_ir_initiator_request_action_preserves_reply_discovery;
                eauto.
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
                 pose proof (echo_ir_resolved_delivery_queued node
                   state external_event message certificates resolved)
                   as queued.
                 pose proof ((proj2 topology) message queued) as message_edge.
                 destruct message_edge as
                   [sender_in [receiver_in forward_edge]].
                 pose proof (echo_ir_enabled_expected_parent node node_eq
                   config state message certificates
                   (@echo_ir_participant_reply_more_rule node) enabled
                   ltac:(cbn [echo_ir_participant_reply_more_rule];
                     now right; left)) as same_parent.
                 eapply
                   echo_ir_participant_reply_more_action_preserves_reply_discovery;
                   eauto.
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
                     pose proof (echo_ir_resolved_delivery_queued node
                       state external_event message certificates resolved)
                       as queued.
                     pose proof ((proj2 topology) message queued)
                       as message_edge.
                     destruct message_edge as
                       [sender_in [receiver_in forward_edge]].
                     pose proof (echo_ir_enabled_expected_parent node node_eq
                       config state message certificates
                       (@echo_ir_participant_reply_final_rule node) enabled
                       ltac:(cbn [echo_ir_participant_reply_final_rule];
                         now right; left)) as same_parent.
                     eapply
                       echo_ir_participant_reply_final_action_preserves_reply_discovery;
                       eauto.
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
                         pose proof
                           (echo_ir_enabled_removed_pending_nonempty
                             config state message certificates
                             (@echo_ir_initiator_reply_more_rule node)
                             enabled
                             ltac:(cbn [echo_ir_initiator_reply_more_rule];
                               repeat (first
                                 [left; reflexivity | right])))
                           as remaining_nonempty.
                         eapply
                           echo_ir_initiator_reply_more_action_preserves_reply_discovery;
                           eauto.
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
                             eapply
                               echo_ir_initiator_reply_final_action_preserves_reply_discovery;
                               eauto.
                         *** contradiction.
Qed.

Lemma echo_ir_initial_reply_discovery_support
    (config : ir_protocol_config node echo_ir_signature) :
  echo_ir_reply_discovery_support config (@echo_initial_state node).
Proof.
  split.
  - intros child parent child_in installed. discriminate.
  - split.
    + intros message queued request_kind. contradiction.
    + intros message queued reply_kind. contradiction.
Qed.

Theorem echo_ir_path_preserves_reply_discovery_support
    (config : ir_protocol_config node echo_ir_signature)
    (initial final : ir_protocol_state node echo_ir_signature) :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  ir_protocol_reachable node_eq config
    (ir_program_rules (@echo_program node)) initial final ->
  echo_ir_topology_well_formed node config initial ->
  echo_ir_reply_discovery_support config initial ->
  echo_ir_reply_discovery_support config final.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  induction reachable; intros topology support.
  - exact support.
  - apply IHreachable.
    + eapply EchoStep_preserves_topology_well_formed.
      * exact initiator_in.
      * exact neighbors_valid.
      * exact symmetric.
      * exact topology.
      * exists rule. exact H.
    + eapply EchoStep_preserves_reply_discovery_support.
      * exact topology.
      * exact support.
      * exists rule. exact H.
Qed.

Theorem echo_reachable_reply_discovery_support
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_reachable node node_eq config state ->
  echo_ir_reply_discovery_support config state.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  eapply echo_ir_path_preserves_reply_discovery_support.
  - exact initiator_in.
  - exact neighbors_valid.
  - exact symmetric.
  - exact reachable.
  - apply echo_ir_initial_topology_well_formed.
  - apply echo_ir_initial_reply_discovery_support.
Qed.

Corollary echo_reachable_reply_receivers_discovered
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_reachable node node_eq config state ->
  echo_ir_reply_receivers_discovered state.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  exact (proj2 (proj2
    (echo_reachable_reply_discovery_support config state
      initiator_in neighbors_valid symmetric reachable))).
Qed.

End EchoIRExecutableReplyDiscovery.
