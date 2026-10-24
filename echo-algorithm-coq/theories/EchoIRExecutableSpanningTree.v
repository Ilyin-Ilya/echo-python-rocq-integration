(** * Direct parent paths for the executable generic Echo IR

    This module turns the proof-only rooted parent-chain certificate into the
    finite path representation exposed by the public spanning-tree API.  It
    depends only on the generated generic IR program and its direct invariants;
    no old Echo transition relation or simulation proof is imported. *)

From Stdlib Require Import List Arith Sorting.Permutation
  Arith.Wf_nat Init.Wf
  Wellfounded.Inverse_Image.
Import ListNotations.
Require Import ProtocolIRTypes ProtocolIRExpressions ProtocolIRActions
  ProtocolIRInterpreter ProtocolIRRunner EchoIRSignature EchoIRProgram
  EchoIRExecutable EchoIRExecutableInvariants EchoIRExecutableDiscovery
  EchoIRExecutableLifecycle EchoIRExecutablePending EchoIRExecutableTopology
  EchoIRExecutableRequestParent EchoIRExecutableReplyDiscovery
  EchoIRExecutableObligations.

Section EchoIRExecutableSpanningTree.

Variable node : Type.
Variable node_eq : forall left right : node,
  {left = right} + {left <> right}.

Definition echo_ir_parent
    (state : ir_protocol_state node echo_ir_signature)
    (owner : node) : option node :=
  echo_ir_parent_value node state owner.

Fixpoint echo_ir_parent_path
    (state : ir_protocol_state node echo_ir_signature)
    (owner : node) (steps : nat) : option node :=
  match steps with
  | 0 => Some owner
  | S rest =>
      match echo_ir_parent state owner with
      | None => None
      | Some parent => echo_ir_parent_path state parent rest
      end
  end.

Definition echo_ir_reaches_initiator
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (owner : node) : Prop :=
  exists steps,
    echo_ir_parent_path state owner steps =
      Some (echo_ir_config_initiator node config).

Definition echo_ir_started_value
    (state : ir_protocol_state node echo_ir_signature) : bool :=
  match ir_global_fields state EchoIRStarted with
  | IRBoolValue started => started
  end.

Definition echo_ir_reached
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (owner : node) : Prop :=
  owner = echo_ir_config_initiator node config \/
  echo_ir_local_discovered node state owner.

(** While the protocol is started, every edge leaving the reached region is
    represented by an outstanding pending item at its reached endpoint. *)
Definition echo_ir_discovery_frontier
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  echo_ir_started_value state = true ->
  forall owner neighbor,
    In owner (ir_config_nodes config) ->
    echo_ir_reached config state owner ->
    In neighbor (ir_config_neighbors config owner) ->
    echo_ir_reached config state neighbor \/
    In neighbor (echo_ir_pending_value node state owner).

Lemma echo_ir_reached_dec config state owner :
  {echo_ir_reached config state owner} +
  {~ echo_ir_reached config state owner}.
Proof.
  destruct (node_eq owner (echo_ir_config_initiator node config))
    as [root | nonroot].
  - left. now left.
  - destruct (echo_ir_parent_value node state owner) as
      [installed_parent |] eqn:parent_value.
    + left. right. left. now rewrite parent_value.
    + destruct (echo_ir_pending_value node state owner) as
        [|item rest] eqn:pending.
      * destruct (echo_ir_finished_value node state owner) eqn:finished.
        -- left. right. right. right. now rewrite finished.
        -- right. intros [root | [has_parent | [has_pending | is_finished]]].
           ++ contradiction.
           ++ now rewrite parent_value in has_parent.
           ++ now rewrite pending in has_pending.
           ++ now rewrite finished in is_finished.
      * left. right. right. left. now rewrite pending.
Qed.

Lemma echo_ir_initial_discovery_frontier config :
  echo_ir_discovery_frontier config (@echo_initial_state node).
Proof. intros started. discriminate. Qed.

(** Generic transport used by message-only actions: the frontier observes only
    the started flag, reachedness, and pending projections. *)
Lemma echo_ir_discovery_frontier_ext config left right :
  echo_ir_started_value right = echo_ir_started_value left ->
  (forall owner,
    echo_ir_reached config right owner <->
    echo_ir_reached config left owner) ->
  (forall owner,
    echo_ir_pending_value node right owner =
    echo_ir_pending_value node left owner) ->
  echo_ir_discovery_frontier config left ->
  echo_ir_discovery_frontier config right.
Proof.
  intros same_started same_reached same_pending frontier started
    owner neighbor owner_in owner_reached adjacent.
  apply same_reached in owner_reached.
  rewrite same_started in started.
  destruct (frontier started owner neighbor owner_in owner_reached adjacent)
    as [neighbor_reached | neighbor_pending].
  - left. now apply same_reached.
  - right. now rewrite same_pending.
Qed.

Lemma echo_ir_remove_preserves_discovery_frontier
    config state selected_id :
  echo_ir_discovery_frontier config state ->
  echo_ir_discovery_frontier config
    (ir_remove_selected_message state selected_id).
Proof.
  intro frontier.
  eapply echo_ir_discovery_frontier_ext; try exact frontier;
    intros; reflexivity.
Qed.

Lemma echo_ir_emit_preserves_discovery_frontier
    config state kind sender receivers payload :
  echo_ir_discovery_frontier config state ->
  echo_ir_discovery_frontier config
    (ir_emit_messages state kind sender receivers payload).
Proof.
  intro frontier.
  eapply echo_ir_discovery_frontier_ext; try exact frontier;
    intros; reflexivity.
Qed.

Lemma echo_ir_update_process_other_reached_iff
    config state owner observed parent pending finished :
  owner <> observed ->
  echo_ir_reached config
    (echo_ir_update_process node node_eq state owner parent pending finished)
    observed <->
  echo_ir_reached config state observed.
Proof.
  intro different.
  unfold echo_ir_reached, echo_ir_local_discovered,
    echo_ir_parent_value, echo_ir_pending_value, echo_ir_finished_value,
    echo_ir_update_process.
  repeat rewrite ir_set_local_field_read_other_process by exact different.
  tauto.
Qed.

Lemma echo_ir_update_process_other_pending
    state owner observed parent pending finished :
  owner <> observed ->
  echo_ir_pending_value node
    (echo_ir_update_process node node_eq state owner parent pending finished)
    observed =
  echo_ir_pending_value node state observed.
Proof.
  intro different.
  unfold echo_ir_pending_value, echo_ir_update_process.
  repeat rewrite ir_set_local_field_read_other_process by exact different.
  reflexivity.
Qed.

Lemma echo_ir_update_process_reached_monotone
    config state owner parent pending finished :
  echo_ir_reached config
    (echo_ir_update_process node node_eq state owner parent pending finished)
    owner ->
  forall observed,
    echo_ir_reached config state observed ->
    echo_ir_reached config
      (echo_ir_update_process node node_eq state owner parent pending finished)
      observed.
Proof.
  intros owner_after observed observed_before.
  destruct (node_eq owner observed) as [same | different].
  - now subst observed.
  - apply (proj2 (echo_ir_update_process_other_reached_iff
      config state owner observed parent pending finished different)).
    exact observed_before.
Qed.

(** Startup establishes the frontier by placing every initiator neighbor in
    its pending list before any other process is reached. *)
Lemma echo_ir_started_root_pending_establishes_discovery_frontier
    config state order :
  echo_ir_started_value state = true ->
  (forall owner,
    In owner (ir_config_nodes config) ->
    echo_ir_reached config state owner ->
    owner = echo_ir_config_initiator node config) ->
  echo_ir_pending_value node state
    (echo_ir_config_initiator node config) = order ->
  Permutation order
    (ir_config_neighbors config
      (echo_ir_config_initiator node config)) ->
  echo_ir_discovery_frontier config state.
Proof.
  intros started only_root root_pending ordered _ owner neighbor
    owner_in owner_reached adjacent.
  right. specialize (only_root owner owner_in owner_reached). subst owner.
  rewrite root_pending.
  exact (Permutation_in neighbor (Permutation_sym ordered) adjacent).
Qed.

(** Generic process-update kernel.  A caller only has to show that reachedness
    is monotone and that every still-unreached neighbor of the updated owner is
    present in its new pending list. *)
Lemma echo_ir_update_process_preserves_discovery_frontier
    config state owner parent pending finished :
  echo_ir_discovery_frontier config state ->
  (forall observed,
    echo_ir_reached config state observed ->
    echo_ir_reached config
      (echo_ir_update_process node node_eq state owner parent
        (IRListNodeValue pending) finished) observed) ->
  (echo_ir_started_value state = true -> forall neighbor,
    In neighbor (ir_config_neighbors config owner) ->
    ~ echo_ir_reached config
      (echo_ir_update_process node node_eq state owner parent
        (IRListNodeValue pending) finished) neighbor ->
    In neighbor pending) ->
  echo_ir_discovery_frontier config
    (echo_ir_update_process node node_eq state owner parent
      (IRListNodeValue pending) finished).
Proof.
  intros frontier monotone owner_pending started observed neighbor
    observed_in observed_reached adjacent.
  destruct (echo_ir_reached_dec config
    (echo_ir_update_process node node_eq state owner parent
      (IRListNodeValue pending) finished) neighbor)
    as [neighbor_reached | neighbor_unreached]; [now left |].
  right.
  destruct (node_eq owner observed) as [same | different].
  - subst observed.
    unfold echo_ir_pending_value, echo_ir_update_process.
    rewrite ir_set_local_field_read_different by discriminate.
    rewrite ir_set_local_field_same.
    now apply (owner_pending started).
  - pose proof (proj1 (echo_ir_update_process_other_reached_iff
      config state owner observed parent (IRListNodeValue pending) finished
      different) observed_reached) as observed_before.
    assert (started_before : echo_ir_started_value state = true).
    { exact started. }
    destruct (frontier started_before observed neighbor observed_in
      observed_before adjacent) as [neighbor_before | neighbor_pending].
    + exfalso. apply neighbor_unreached. now apply monotone.
    + rewrite (echo_ir_update_process_other_pending state owner observed
        parent (IRListNodeValue pending) finished different).
      exact neighbor_pending.
Qed.

Lemma echo_ir_queued_request_sender_reached
    config state message :
  echo_ir_request_senders_discovered node state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRRequest ->
  echo_ir_reached config state (ir_message_sender message).
Proof.
  intros senders queued request_kind.
  right. now apply (senders message queued request_kind).
Qed.

Lemma echo_ir_queued_reply_sender_reached
    config state message :
  echo_ir_reply_noninitiator_senders_discovered node config state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRReply ->
  echo_ir_reached config state (ir_message_sender message).
Proof.
  intros senders queued reply_kind.
  destruct (node_eq (ir_message_sender message)
    (echo_ir_config_initiator node config)) as [root | nonroot].
  - now left.
  - right. now apply (senders message queued reply_kind nonroot).
Qed.

(** Reply rules delete the replying child from the receiver's pending list.
    If that child is already reached, deleting it cannot remove an edge that
    still crosses the discovery frontier. *)
Lemma echo_ir_remove_pending_update_preserves_discovery_frontier
    config state owner sender parent finished :
  echo_ir_discovery_frontier config state ->
  In owner (ir_config_nodes config) ->
  echo_ir_reached config state owner ->
  echo_ir_reached config state sender ->
  echo_ir_reached config
    (echo_ir_update_process node node_eq state owner parent
      (IRListNodeValue
        (ir_remove_node node_eq sender
          (echo_ir_pending_value node state owner))) finished) owner ->
  echo_ir_discovery_frontier config
    (echo_ir_update_process node node_eq state owner parent
      (IRListNodeValue
        (ir_remove_node node_eq sender
          (echo_ir_pending_value node state owner))) finished).
Proof.
  intros frontier owner_in owner_before sender_before owner_after.
  eapply echo_ir_update_process_preserves_discovery_frontier.
  - exact frontier.
  - now apply echo_ir_update_process_reached_monotone.
  - intros started neighbor adjacent neighbor_unreached.
    assert (sender_after : echo_ir_reached config
      (echo_ir_update_process node node_eq state owner parent
        (IRListNodeValue
          (ir_remove_node node_eq sender
            (echo_ir_pending_value node state owner))) finished) sender).
    { eapply echo_ir_update_process_reached_monotone; eauto. }
    assert (different : neighbor <> sender).
    { intro same. subst neighbor. contradiction. }
    destruct (frontier started owner neighbor owner_in owner_before adjacent)
      as [neighbor_before | neighbor_pending].
    + exfalso. apply neighbor_unreached.
      eapply echo_ir_update_process_reached_monotone; eauto.
    + now apply echo_ir_remove_node_preserves_other.
Qed.

Lemma echo_ir_start_action_discovery_frontier
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (certificates : ir_start_certificates node echo_ir_signature) :
  (forall owner,
    In owner (ir_config_nodes config) ->
    ~ echo_ir_local_discovered node state owner) ->
  Permutation
    (ir_config_neighbors config (echo_ir_config_initiator node config))
    (ir_config_neighbors config (echo_ir_config_initiator node config)) ->
  eval_ir_action node_eq config state (IRRuntimeStart certificates)
    (ir_rule_action (@echo_ir_start_rule node)) = Some successor ->
  echo_ir_discovery_frontier config successor.
Proof.
  intros initially_unreached ordered action.
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
  apply echo_ir_emit_preserves_discovery_frontier.
  apply echo_ir_started_root_pending_establishes_discovery_frontier
    with (order := ir_config_neighbors config
      (echo_ir_config_initiator node config)).
  - reflexivity.
  - intros owner owner_in [root | discovered]; [exact root |].
    destruct (node_eq (echo_ir_config_initiator node config) owner)
      as [same | different].
    + now symmetry.
    + exfalso. apply (initially_unreached owner owner_in).
      unfold echo_ir_local_discovered, echo_ir_parent_value,
        echo_ir_pending_value, echo_ir_finished_value,
        ir_set_global_field in discovered.
      cbn [ir_processes] in discovered.
      repeat rewrite ir_set_local_field_read_other_process in discovered
        by exact different.
      exact discovered.
  - unfold echo_ir_pending_value, ir_set_global_field.
    cbn [ir_processes].
    apply echo_ir_update_process_pending_same.
  - exact ordered.
Qed.

Lemma echo_ir_start_enabled_configured_unreached
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (certificates : ir_start_certificates node echo_ir_signature) :
  eval_ir_rule node_eq config state (IRRuntimeStart certificates)
    (@echo_ir_start_rule node) = IRRuleEnabled ->
  forall owner,
    In owner (ir_config_nodes config) ->
    ~ echo_ir_local_discovered node state owner.
Proof.
  intros enabled owner owner_in.
  assert (parent_none : echo_ir_parent_value node state owner = None).
  { now apply (echo_ir_start_enabled_configured_parent_none node node_eq
      config state certificates enabled). }
  pose proof (eval_ir_rule_enabled_guard node_eq config state
    (IRRuntimeStart certificates) (@echo_ir_start_rule node)
    (@IRAllNodesLocalEqualExpr node echo_ir_signature EchoIRPending
      (echo_ir_empty_nodes node)) enabled) as pending_guard.
  assert (pending_member :
    In (@IRAllNodesLocalEqualExpr node echo_ir_signature EchoIRPending
      (echo_ir_empty_nodes node))
      (ir_rule_guards (@echo_ir_start_rule node))).
  { cbn [echo_ir_start_rule]. now right; right; left. }
  specialize (pending_guard pending_member).
  unfold echo_ir_empty_nodes in pending_guard.
  cbn [eval_ir_expr] in pending_guard.
  injection pending_guard as all_pending_empty.
  apply forallb_forall with (x := owner) in all_pending_empty;
    [|exact owner_in].
  assert (pending_empty : echo_ir_pending_value node state owner = []).
  { unfold echo_ir_pending_value.
    rewrite (ir_list_node_value_eta
      (ir_processes state owner EchoIRPending)) in all_pending_empty |- *.
    cbn [ir_value_eqb] in all_pending_empty |- *.
    destruct (ir_list_node_value_contents
      (ir_processes state owner EchoIRPending)) as [|head rest];
      [reflexivity | discriminate]. }
  pose proof (eval_ir_rule_enabled_guard node_eq config state
    (IRRuntimeStart certificates) (@echo_ir_start_rule node)
    (@IRAllNodesLocalEqualExpr node echo_ir_signature EchoIRFinished
      (echo_ir_bool node false)) enabled) as finished_guard.
  assert (finished_member :
    In (@IRAllNodesLocalEqualExpr node echo_ir_signature EchoIRFinished
      (echo_ir_bool node false))
      (ir_rule_guards (@echo_ir_start_rule node))).
  { cbn [echo_ir_start_rule]. now right; right; right; left. }
  specialize (finished_guard finished_member).
  unfold echo_ir_bool in finished_guard.
  cbn [eval_ir_expr] in finished_guard.
  injection finished_guard as all_finished_false.
  apply forallb_forall with (x := owner) in all_finished_false;
    [|exact owner_in].
  assert (finished_false : echo_ir_finished_value node state owner = false).
  { unfold echo_ir_finished_value.
    rewrite (echo_ir_bool_value_eta node
      (ir_processes state owner EchoIRFinished)) in all_finished_false |- *.
    cbn [ir_value_eqb] in all_finished_false |- *.
    destruct (echo_ir_bool_value_contents node
      (ir_processes state owner EchoIRFinished));
      [discriminate | reflexivity]. }
  unfold echo_ir_local_discovered.
  rewrite parent_none, pending_empty, finished_false.
  tauto.
Qed.

Lemma echo_ir_first_request_leaf_enabled_no_forward
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  eval_ir_rule node_eq config state (IRRuntimeDeliver message certificates)
    (@echo_ir_first_request_leaf_rule node) = IRRuleEnabled ->
  ir_remove_node node_eq (ir_message_sender message)
    (ir_config_neighbors config (ir_message_receiver message)) = [].
Proof.
  intro enabled.
  pose proof (eval_ir_rule_enabled_guard node_eq config state
    (IRRuntimeDeliver message certificates)
    (@echo_ir_first_request_leaf_rule node)
    (echo_ir_is_empty node (echo_ir_forward_targets node)) enabled) as guard.
  assert (member :
    In (echo_ir_is_empty node (echo_ir_forward_targets node))
      (ir_rule_guards (@echo_ir_first_request_leaf_rule node))).
  { cbn [echo_ir_first_request_leaf_rule echo_ir_process_initial].
    repeat (first [left; reflexivity | right]). }
  specialize (guard member).
  unfold echo_ir_is_empty, echo_ir_forward_targets, echo_ir_remove,
    echo_ir_sender, echo_ir_neighbors, echo_ir_receiver in guard.
  cbn [eval_ir_expr ir_event_message] in guard.
  destruct (ir_remove_node node_eq (ir_message_sender message)
    (ir_config_neighbors config (ir_message_receiver message)))
    as [|head rest] eqn:removed; [reflexivity | discriminate].
Qed.

Lemma echo_ir_first_request_nonleaf_action_discovery_frontier
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_discovery_frontier config state ->
  echo_ir_request_senders_discovered node state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRRequest ->
  Permutation
    (ir_remove_node node_eq (ir_message_sender message)
      (ir_config_neighbors config (ir_message_receiver message)))
    (ir_remove_node node_eq (ir_message_sender message)
      (ir_config_neighbors config (ir_message_receiver message))) ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_nonleaf_rule node)) = Some successor ->
  echo_ir_discovery_frontier config successor.
Proof.
  intros frontier senders queued request_kind ordered action.
  unfold echo_ir_first_request_nonleaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_forward_order,
    echo_ir_remove, echo_ir_neighbors,
    echo_ir_emit_many, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs ir_event_message]
    in action.
  injection action as <-.
  apply echo_ir_emit_preserves_discovery_frontier.
  apply echo_ir_remove_preserves_discovery_frontier.
  eapply echo_ir_update_process_preserves_discovery_frontier.
  - exact frontier.
  - apply echo_ir_update_process_reached_monotone.
    right. apply echo_ir_update_process_some_owner_discovered.
  - intros started neighbor adjacent neighbor_unreached.
    assert (sender_before : echo_ir_reached config state
      (ir_message_sender message)).
    { eapply echo_ir_queued_request_sender_reached; eauto. }
    assert (sender_after : echo_ir_reached config
      (echo_ir_update_process node node_eq state
        (ir_message_receiver message)
        (IROptionNodeValue (Some (ir_message_sender message)))
        (IRListNodeValue
          (ir_remove_node node_eq (ir_message_sender message)
            (ir_config_neighbors config (ir_message_receiver message))))
        false) (ir_message_sender message)).
    { eapply echo_ir_update_process_reached_monotone; eauto.
      right. apply echo_ir_update_process_some_owner_discovered. }
    assert (different : neighbor <> ir_message_sender message).
    { intro same. subst neighbor. contradiction. }
    apply (Permutation_in neighbor (Permutation_sym ordered)).
    now apply echo_ir_remove_node_preserves_other.
Qed.

Lemma echo_ir_first_request_leaf_action_discovery_frontier
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_discovery_frontier config state ->
  echo_ir_request_senders_discovered node state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRRequest ->
  ir_remove_node node_eq (ir_message_sender message)
    (ir_config_neighbors config (ir_message_receiver message)) = [] ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_leaf_rule node)) = Some successor ->
  echo_ir_discovery_frontier config successor.
Proof.
  intros frontier senders queued request_kind no_forward action.
  unfold echo_ir_first_request_leaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_empty_nodes,
    echo_ir_emit_one, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  apply echo_ir_emit_preserves_discovery_frontier.
  apply echo_ir_remove_preserves_discovery_frontier.
  eapply echo_ir_update_process_preserves_discovery_frontier.
  - exact frontier.
  - apply echo_ir_update_process_reached_monotone.
    right. apply echo_ir_update_process_some_owner_discovered.
  - intros started neighbor adjacent neighbor_unreached.
    assert (sender_before : echo_ir_reached config state
      (ir_message_sender message)).
    { eapply echo_ir_queued_request_sender_reached; eauto. }
    assert (sender_after : echo_ir_reached config
      (echo_ir_update_process node node_eq state
        (ir_message_receiver message)
        (IROptionNodeValue (Some (ir_message_sender message)))
        (IRListNodeValue []) true) (ir_message_sender message)).
    { eapply echo_ir_update_process_reached_monotone; eauto.
      right. apply echo_ir_update_process_some_owner_discovered. }
    assert (different : neighbor <> ir_message_sender message).
    { intro same. subst neighbor. contradiction. }
    pose proof (echo_ir_remove_node_preserves_other node node_eq
      (ir_message_sender message) neighbor
      (ir_config_neighbors config (ir_message_receiver message))
      different adjacent) as remains.
    rewrite no_forward in remains. contradiction.
Qed.

Lemma echo_ir_repeated_request_action_discovery_frontier
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_discovery_frontier config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_repeated_request_rule node)) = Some successor ->
  echo_ir_discovery_frontier config successor.
Proof.
  intros frontier action.
  unfold echo_ir_repeated_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_receiver, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  apply echo_ir_emit_preserves_discovery_frontier.
  now apply echo_ir_remove_preserves_discovery_frontier.
Qed.

Lemma echo_ir_initiator_request_action_discovery_frontier
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_discovery_frontier config state ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_request_rule node)) = Some successor ->
  echo_ir_discovery_frontier config successor.
Proof.
  intros frontier action.
  unfold echo_ir_initiator_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_initiator, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator))
    in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs ir_event_message]
    in action.
  injection action as <-.
  apply echo_ir_emit_preserves_discovery_frontier.
  now apply echo_ir_remove_preserves_discovery_frontier.
Qed.

Lemma echo_ir_participant_reply_more_action_discovery_frontier
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_discovery_frontier config state ->
  echo_ir_reply_noninitiator_senders_discovered node config state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRReply ->
  In (ir_message_receiver message) (ir_config_nodes config) ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_more_rule node)) = Some successor ->
  echo_ir_discovery_frontier config successor.
Proof.
  intros frontier senders queued reply_kind receiver_in action.
  unfold echo_ir_participant_reply_more_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_receiver, echo_ir_expected_parent, echo_ir_some,
    echo_ir_removed_pending, echo_ir_remove, echo_ir_sender,
    echo_ir_pending, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  unfold EchoIRProgram.echo_ir_receiver, EchoIRProgram.echo_ir_parent in action.
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
    change (echo_ir_discovery_frontier config
      (ir_remove_selected_message
        (echo_ir_update_process node node_eq state
          (ir_message_receiver message)
          (IROptionNodeValue (Some parent_node))
          (IRListNodeValue
            (ir_remove_node node_eq (ir_message_sender message)
              (ir_list_node_value_contents
                (ir_processes state
                  (ir_message_receiver message) EchoIRPending)))) false)
        (ir_message_id message))).
    apply echo_ir_remove_preserves_discovery_frontier.
    eapply echo_ir_remove_pending_update_preserves_discovery_frontier.
    + exact frontier.
    + exact receiver_in.
    + right. left. unfold echo_ir_parent_value.
      rewrite parent_value. discriminate.
    + eapply echo_ir_queued_reply_sender_reached; eauto.
    + right. apply echo_ir_update_process_some_owner_discovered.
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_participant_reply_final_action_discovery_frontier
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_discovery_frontier config state ->
  echo_ir_reply_noninitiator_senders_discovered node config state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRReply ->
  In (ir_message_receiver message) (ir_config_nodes config) ->
  ir_remove_node node_eq (ir_message_sender message)
    (echo_ir_pending_value node state (ir_message_receiver message)) = [] ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_final_rule node)) = Some successor ->
  echo_ir_discovery_frontier config successor.
Proof.
  intros frontier senders queued reply_kind receiver_in no_pending action.
  unfold echo_ir_participant_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_receiver, echo_ir_expected_parent, echo_ir_some,
    echo_ir_empty_nodes, echo_ir_emit_one, echo_ir_empty_payload,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  unfold EchoIRProgram.echo_ir_receiver, EchoIRProgram.echo_ir_parent in action.
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
    change (echo_ir_discovery_frontier config
      (ir_emit_messages
        (ir_remove_selected_message
          (echo_ir_update_process node node_eq state
            (ir_message_receiver message)
            (IROptionNodeValue (Some parent_node))
            (IRListNodeValue []) true)
          (ir_message_id message))
        EchoIRReply (ir_message_receiver message) [parent_node] [])).
    apply echo_ir_emit_preserves_discovery_frontier.
    apply echo_ir_remove_preserves_discovery_frontier.
    rewrite <- no_pending.
    eapply echo_ir_remove_pending_update_preserves_discovery_frontier.
    + exact frontier.
    + exact receiver_in.
    + right. left. unfold echo_ir_parent_value.
      rewrite parent_value. discriminate.
    + eapply echo_ir_queued_reply_sender_reached; eauto.
    + right. apply echo_ir_update_process_some_owner_discovered.
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_initiator_reply_more_action_discovery_frontier
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_discovery_frontier config state ->
  echo_ir_reply_noninitiator_senders_discovered node config state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRReply ->
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_more_rule node)) = Some successor ->
  echo_ir_discovery_frontier config successor.
Proof.
  intros frontier senders queued reply_kind initiator_in action.
  unfold echo_ir_initiator_reply_more_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_removed_pending,
    echo_ir_remove, echo_ir_sender, echo_ir_pending, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  rewrite ir_set_local_field_read_different in action by discriminate.
  rewrite (ir_list_node_value_eta
    (ir_processes state
      (ir_node_value_contents (ir_config_fields config EchoIRInitiator))
      EchoIRPending)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  apply echo_ir_remove_preserves_discovery_frontier.
  eapply echo_ir_remove_pending_update_preserves_discovery_frontier.
  - exact frontier.
  - exact initiator_in.
  - now left.
  - eapply echo_ir_queued_reply_sender_reached; eauto.
  - now left.
Qed.

Lemma echo_ir_initiator_reply_final_action_discovery_frontier
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_discovery_frontier config state ->
  echo_ir_reply_noninitiator_senders_discovered node config state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRReply ->
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  ir_remove_node node_eq (ir_message_sender message)
    (echo_ir_pending_value node state
      (echo_ir_config_initiator node config)) = [] ->
  eval_ir_action node_eq config state (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_final_rule node)) = Some successor ->
  echo_ir_discovery_frontier config successor.
Proof.
  intros frontier senders queued reply_kind initiator_in no_pending action.
  unfold echo_ir_initiator_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_empty_nodes,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  apply echo_ir_remove_preserves_discovery_frontier.
  rewrite <- no_pending.
  eapply echo_ir_remove_pending_update_preserves_discovery_frontier.
  - exact frontier.
  - exact initiator_in.
  - now left.
  - eapply echo_ir_queued_reply_sender_reached; eauto.
  - now left.
Qed.

Theorem EchoStep_preserves_discovery_frontier
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (external_event : ir_external_event node echo_ir_signature) :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_queued_edges_valid node config state ->
  echo_ir_request_senders_discovered node state ->
  echo_ir_reply_noninitiator_senders_discovered node config state ->
  echo_ir_discovery_frontier config state ->
  EchoStep node node_eq config state external_event successor ->
  echo_ir_discovery_frontier config successor.
Proof.
  intros initiator_in queued_edges request_senders reply_senders frontier step.
  destruct (echo_ir_step_success_components node node_eq
    config state successor external_event step) as
    [rule_id [runtime_event [selected_rule
      [resolved [selected [selected_in [enabled [identifier action]]]]]]]].
  change (In selected_rule (@echo_ir_rules node)) in selected_in.
  unfold echo_ir_rules in selected_in. cbn in selected_in.
  destruct selected_in as [same | selected_in]; [subst selected_rule |].
  - pose proof (eval_ir_rule_enabled_pattern node_eq config state runtime_event
      (@echo_ir_start_rule node) enabled) as pattern.
    destruct runtime_event as [|certificates|message certificates];
      cbn [echo_ir_start_rule ir_event_pattern_matches] in pattern;
      try discriminate.
    eapply echo_ir_start_action_discovery_frontier.
    + exact (echo_ir_start_enabled_configured_unreached
        config state certificates enabled).
    + exact (echo_ir_start_enabled_order node node_eq
        config state certificates enabled).
    + exact action.
  - destruct selected_in as [same | selected_in]; [subst selected_rule |].
    + pose proof (eval_ir_rule_enabled_pattern node_eq config state runtime_event
        (@echo_ir_first_request_nonleaf_rule node) enabled) as pattern.
      destruct runtime_event as [|start_certificates|message certificates];
        cbn [echo_ir_first_request_nonleaf_rule ir_event_pattern_matches]
          in pattern; try discriminate.
      pose proof (echo_ir_resolved_delivery_queued node state
        external_event message certificates resolved) as queued.
      pose proof (echo_ir_enabled_request_pattern_kind node node_eq
        config state message certificates
        (@echo_ir_first_request_nonleaf_rule node) eq_refl enabled)
        as request_kind.
      eapply echo_ir_first_request_nonleaf_action_discovery_frontier; eauto.
    + destruct selected_in as [same | selected_in]; [subst selected_rule |].
      * pose proof (eval_ir_rule_enabled_pattern node_eq config state
          runtime_event (@echo_ir_first_request_leaf_rule node) enabled)
          as pattern.
        destruct runtime_event as [|start_certificates|message certificates];
          cbn [echo_ir_first_request_leaf_rule ir_event_pattern_matches]
            in pattern; try discriminate.
        pose proof (echo_ir_resolved_delivery_queued node state
          external_event message certificates resolved) as queued.
        pose proof (echo_ir_enabled_request_pattern_kind node node_eq
          config state message certificates
          (@echo_ir_first_request_leaf_rule node) eq_refl enabled)
          as request_kind.
        eapply echo_ir_first_request_leaf_action_discovery_frontier; eauto.
        exact (echo_ir_first_request_leaf_enabled_no_forward
          config state message certificates enabled).
      * destruct selected_in as [same | selected_in]; [subst selected_rule |].
        -- pose proof (eval_ir_rule_enabled_pattern node_eq config state
             runtime_event (@echo_ir_repeated_request_rule node) enabled)
             as pattern.
           destruct runtime_event as
             [|start_certificates|message certificates];
             cbn [echo_ir_repeated_request_rule ir_event_pattern_matches]
               in pattern; try discriminate.
           eapply echo_ir_repeated_request_action_discovery_frontier; eauto.
        -- destruct selected_in as [same | selected_in];
             [subst selected_rule |].
           ++ pose proof (eval_ir_rule_enabled_pattern node_eq config state
                runtime_event (@echo_ir_initiator_request_rule node) enabled)
                as pattern.
              destruct runtime_event as
                [|start_certificates|message certificates];
                cbn [echo_ir_initiator_request_rule ir_event_pattern_matches]
                  in pattern; try discriminate.
              eapply echo_ir_initiator_request_action_discovery_frontier;
                eauto.
           ++ destruct selected_in as [same | selected_in];
                [subst selected_rule |].
              ** pose proof (eval_ir_rule_enabled_pattern node_eq config state
                   runtime_event (@echo_ir_participant_reply_more_rule node)
                   enabled) as pattern.
                 destruct runtime_event as
                   [|start_certificates|message certificates];
                   cbn [echo_ir_participant_reply_more_rule
                     ir_event_pattern_matches] in pattern; try discriminate.
                 pose proof (echo_ir_resolved_delivery_queued node state
                   external_event message certificates resolved) as queued.
                 pose proof (echo_ir_enabled_reply_pattern_kind node node_eq
                   config state message certificates
                   (@echo_ir_participant_reply_more_rule node) eq_refl enabled)
                   as reply_kind.
                 pose proof (echo_ir_enabled_expected_parent node node_eq
                   config state message certificates
                   (@echo_ir_participant_reply_more_rule node) enabled
                   ltac:(cbn [echo_ir_participant_reply_more_rule];
                     now right; left)) as old_parent.
                 destruct (queued_edges message queued) as
                   [sender_in [receiver_in edge]].
                 eapply
                   echo_ir_participant_reply_more_action_discovery_frontier;
                   eauto.
              ** destruct selected_in as [same | selected_in];
                   [subst selected_rule |].
                 --- pose proof (eval_ir_rule_enabled_pattern node_eq config
                       state runtime_event
                       (@echo_ir_participant_reply_final_rule node) enabled)
                       as pattern.
                     destruct runtime_event as
                       [|start_certificates|message certificates];
                       cbn [echo_ir_participant_reply_final_rule
                         ir_event_pattern_matches] in pattern;
                       try discriminate.
                     pose proof (echo_ir_resolved_delivery_queued node state
                       external_event message certificates resolved) as queued.
                     pose proof (echo_ir_enabled_reply_pattern_kind node node_eq
                       config state message certificates
                       (@echo_ir_participant_reply_final_rule node)
                       eq_refl enabled) as reply_kind.
                     pose proof (echo_ir_enabled_expected_parent node node_eq
                       config state message certificates
                       (@echo_ir_participant_reply_final_rule node) enabled
                       ltac:(cbn [echo_ir_participant_reply_final_rule];
                         now right; left)) as old_parent.
                     pose proof
                       (echo_ir_enabled_receiver_removed_pending_empty node
                         node_eq config state message certificates
                         (@echo_ir_participant_reply_final_rule node) enabled
                         ltac:(cbn [echo_ir_participant_reply_final_rule];
                           repeat (first [left; reflexivity | right])))
                       as empty.
                     destruct (queued_edges message queued) as
                       [sender_in [receiver_in edge]].
                     eapply
                       echo_ir_participant_reply_final_action_discovery_frontier;
                       eauto.
                 --- destruct selected_in as [same | selected_in];
                       [subst selected_rule |].
                     +++ pose proof (eval_ir_rule_enabled_pattern node_eq
                           config state runtime_event
                           (@echo_ir_initiator_reply_more_rule node) enabled)
                           as pattern.
                         destruct runtime_event as
                           [|start_certificates|message certificates];
                           cbn [echo_ir_initiator_reply_more_rule
                             ir_event_pattern_matches] in pattern;
                           try discriminate.
                         pose proof (echo_ir_resolved_delivery_queued node state
                           external_event message certificates resolved)
                           as queued.
                         pose proof (echo_ir_enabled_reply_pattern_kind node
                           node_eq config state message certificates
                           (@echo_ir_initiator_reply_more_rule node)
                           eq_refl enabled) as reply_kind.
                         eapply
                           echo_ir_initiator_reply_more_action_discovery_frontier;
                           eauto.
                     +++ destruct selected_in as [same | selected_in];
                           [subst selected_rule |].
                         *** pose proof (eval_ir_rule_enabled_pattern node_eq
                               config state runtime_event
                               (@echo_ir_initiator_reply_final_rule node)
                               enabled) as pattern.
                             destruct runtime_event as
                               [|start_certificates|message certificates];
                               cbn [echo_ir_initiator_reply_final_rule
                                 ir_event_pattern_matches] in pattern;
                               try discriminate.
                             pose proof (echo_ir_resolved_delivery_queued node
                               state external_event message certificates
                               resolved) as queued.
                             pose proof
                               (echo_ir_enabled_reply_pattern_kind node node_eq
                                 config state message certificates
                                 (@echo_ir_initiator_reply_final_rule node)
                                 eq_refl enabled) as reply_kind.
                             pose proof
                               (echo_ir_enabled_initiator_removed_pending_empty
                                 node node_eq config state message certificates
                                 (@echo_ir_initiator_reply_final_rule node)
                                 enabled
                                 ltac:(cbn
                                   [echo_ir_initiator_reply_final_rule];
                                   repeat
                                     (first [left; reflexivity | right])))
                               as empty.
                             eapply
                               echo_ir_initiator_reply_final_action_discovery_frontier;
                               eauto.
                         *** contradiction.
Qed.

Definition echo_ir_rooted_frontier_bundle config state : Prop :=
  echo_ir_rooted_pending_bundle node config state /\
  echo_ir_discovery_frontier config state.

Lemma echo_ir_initial_rooted_frontier_bundle config :
  echo_ir_rooted_frontier_bundle config (@echo_initial_state node).
Proof.
  split.
  - apply echo_ir_initial_rooted_pending_bundle.
  - apply echo_ir_initial_discovery_frontier.
Qed.

Lemma EchoStep_preserves_rooted_frontier_bundle
    config state successor event :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_ir_rooted_frontier_bundle config state ->
  EchoStep node node_eq config state event successor ->
  echo_ir_rooted_frontier_bundle config successor.
Proof.
  intros initiator_in neighbors_valid symmetric
    [rooted_pending frontier] step.
  assert (rooted_pending_after :
    echo_ir_rooted_pending_bundle node config successor).
  { eapply EchoStep_preserves_rooted_pending_bundle; eauto. }
  split; [exact rooted_pending_after |].
  destruct rooted_pending as [reply_pending rooted].
  destruct reply_pending as [child_bundle replies].
  destruct child_bundle as [request_pending children].
  destruct request_pending as [edge_bundle requests].
  destruct edge_bundle as [parent_bundle reply_unique].
  destruct parent_bundle as
    [request_bundle [root_parent [reply_senders parent_replies]]].
  destruct request_bundle as
    [[parent_edges queued_edges]
      [discovered [accounting [reply_support reverse]]]].
  destruct reply_support as
    [parent_targets [request_senders reply_receivers]].
  eapply EchoStep_preserves_discovery_frontier; eauto.
Qed.

Theorem echo_ir_path_preserves_rooted_frontier_bundle
    config initial final :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  ir_protocol_reachable node_eq config
    (ir_program_rules (@echo_program node)) initial final ->
  echo_ir_rooted_frontier_bundle config initial ->
  echo_ir_rooted_frontier_bundle config final.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  induction reachable; intro bundle.
  - exact bundle.
  - apply IHreachable.
    eapply EchoStep_preserves_rooted_frontier_bundle; eauto.
    exists rule. exact H.
Qed.

Theorem echo_reachable_discovery_frontier config state :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_reachable node node_eq config state ->
  echo_ir_discovery_frontier config state.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  pose proof (echo_ir_path_preserves_rooted_frontier_bundle config
    (@echo_initial_state node) state initiator_in neighbors_valid symmetric
    reachable (echo_ir_initial_rooted_frontier_bundle config)) as bundle.
  exact (proj2 bundle).
Qed.

Lemma echo_ir_parent_chain_has_path config state owner :
  echo_ir_parent_chain node config state owner ->
  echo_ir_reaches_initiator config state owner.
Proof.
  intro chain. induction chain.
  - exists 0. reflexivity.
  - destruct IHchain as [steps path].
    exists (S steps). cbn [echo_ir_parent_path].
    change
      (match echo_ir_parent_value node state child with
       | None => None
       | Some observed => echo_ir_parent_path state observed steps
       end = Some (echo_ir_config_initiator node config)).
    now rewrite H0.
Qed.

Lemma echo_ir_parent_chain_owner_configured
    config state owner :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_parent_chain node config state owner ->
  In owner (ir_config_nodes config).
Proof.
  intros initiator_in chain. induction chain.
  - exact initiator_in.
  - exact H.
Qed.

(** Once the initiator is finished, unfinished-child pendingness propagates
    finishedness down every certified parent chain. *)
Lemma echo_ir_parent_chain_finished
    config state owner :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_completion_well_formed node config state ->
  echo_ir_unfinished_children_pending node config state ->
  echo_ir_finished_value node state
    (echo_ir_config_initiator node config) = true ->
  echo_ir_parent_chain node config state owner ->
  echo_ir_finished_value node state owner = true.
Proof.
  intros initiator_in completion children root_finished chain.
  induction chain.
  - exact root_finished.
  - destruct (echo_ir_finished_value node state child) eqn:finished;
      [reflexivity |].
    assert (parent_in : In parent (ir_config_nodes config)).
    { eapply echo_ir_parent_chain_owner_configured; eauto. }
    pose proof (completion parent parent_in IHchain) as parent_empty.
    pose proof (children child parent H H0 finished) as child_pending.
    rewrite parent_empty in child_pending. contradiction.
Qed.

(** A finished reached process has no pending items.  The frontier invariant
    therefore forces each of its configured neighbors into the reached set. *)
Lemma echo_ir_finished_reached_neighbor_reached
    config state owner neighbor :
  echo_ir_discovery_frontier config state ->
  echo_ir_completion_well_formed node config state ->
  echo_ir_started_value state = true ->
  In owner (ir_config_nodes config) ->
  echo_ir_reached config state owner ->
  echo_ir_finished_value node state owner = true ->
  In neighbor (ir_config_neighbors config owner) ->
  echo_ir_reached config state neighbor.
Proof.
  intros frontier completion started owner_in reached finished adjacent.
  destruct (frontier started owner neighbor owner_in reached adjacent)
    as [neighbor_reached | neighbor_pending]; [exact neighbor_reached |].
  pose proof (completion owner owner_in finished) as pending_empty.
  rewrite pending_empty in neighbor_pending. contradiction.
Qed.

(** Connectivity is expressed directly through the generic configuration:
    each non-initiator has a neighbor of smaller wave depth.  Once the root is
    finished, the rooted-chain and frontier invariants make reachedness closed
    over those edges, so well-founded induction covers every configured node. *)
Theorem echo_ir_finished_root_frontier_all_reached
    config state
    (wave_depth : node -> nat) :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  (forall owner,
    In owner (ir_config_nodes config) ->
    owner <> echo_ir_config_initiator node config ->
    exists parent,
      In parent (ir_config_nodes config) /\
      In owner (ir_config_neighbors config parent) /\
      wave_depth parent < wave_depth owner) ->
  echo_ir_discovered_participants_parented node config state ->
  echo_ir_parent_chains_rooted node config state ->
  echo_ir_completion_well_formed node config state ->
  echo_ir_unfinished_children_pending node config state ->
  echo_ir_discovery_frontier config state ->
  echo_ir_started_value state = true ->
  echo_ir_finished_value node state
    (echo_ir_config_initiator node config) = true ->
  forall owner,
    In owner (ir_config_nodes config) ->
    echo_ir_reached config state owner.
Proof.
  intros initiator_in connected parented rooted completion children frontier
    started root_finished.
  apply (well_founded_ind
    (wf_inverse_image node nat lt wave_depth lt_wf)
    (fun owner =>
      In owner (ir_config_nodes config) ->
      echo_ir_reached config state owner)).
  intros owner IH owner_in.
  destruct (node_eq owner (echo_ir_config_initiator node config))
    as [root | nonroot].
  - now left.
  - destruct (connected owner owner_in nonroot) as
      [parent [parent_in [adjacent lower]]].
    pose proof (IH parent lower parent_in) as parent_reached.
    assert (parent_chain : echo_ir_parent_chain node config state parent).
    { destruct (node_eq parent (echo_ir_config_initiator node config))
        as [parent_root | parent_nonroot].
      - subst parent. constructor.
      - destruct parent_reached as [impossible | parent_discovered];
          [contradiction |].
        destruct (parented parent parent_nonroot parent_discovered)
          as [grandparent installed].
        now apply rooted with (parent := grandparent). }
    assert (parent_finished :
      echo_ir_finished_value node state parent = true).
    { eapply echo_ir_parent_chain_finished; eauto. }
    eapply echo_ir_finished_reached_neighbor_reached; eauto.
Qed.

(** End-to-end direct executable theorem: reachability supplies every
    maintained invariant above, so a finished initiator closes the discovery
    frontier over the whole connected configuration. *)
Theorem echo_reachable_finished_root_all_reached
    config state (wave_depth : node -> nat) :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  (forall owner,
    In owner (ir_config_nodes config) ->
    owner <> echo_ir_config_initiator node config ->
    exists parent,
      In parent (ir_config_nodes config) /\
      In owner (ir_config_neighbors config parent) /\
      wave_depth parent < wave_depth owner) ->
  echo_reachable node node_eq config state ->
  echo_ir_started_value state = true ->
  echo_ir_finished_value node state
    (echo_ir_config_initiator node config) = true ->
  forall owner,
    In owner (ir_config_nodes config) ->
    echo_ir_reached config state owner.
Proof.
  intros initiator_in neighbors_valid symmetric connected reachable
    started root_finished.
  eapply echo_ir_finished_root_frontier_all_reached; eauto.
  - exact (echo_reachable_discovered_participants_parented
      node node_eq config state reachable).
  - eapply echo_reachable_parent_chains_rooted; eauto.
  - exact (echo_reachable_completion node node_eq config state reachable).
  - eapply echo_reachable_unfinished_children_pending; eauto.
  - eapply echo_reachable_discovery_frontier; eauto.
Qed.

(** A configured process which is the initiator or has left its generated
    initial local state has a finite parent path to the initiator. *)
Theorem echo_reachable_discovered_reaches_initiator
    config state owner :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_reachable node node_eq config state ->
  In owner (ir_config_nodes config) ->
  (owner = echo_ir_config_initiator node config \/
    echo_ir_local_discovered node state owner) ->
  echo_ir_reaches_initiator config state owner.
Proof.
  intros initiator_in neighbors_valid symmetric reachable owner_in observed.
  destruct (node_eq owner (echo_ir_config_initiator node config))
    as [root | nonroot].
  - subst owner. apply echo_ir_parent_chain_has_path. constructor.
  - destruct observed as [root | discovered]; [contradiction |].
    pose proof
      (echo_reachable_discovered_participants_parented
        node node_eq config state reachable owner nonroot discovered)
      as [parent installed].
    pose proof (echo_reachable_parent_chains_rooted
      node node_eq config state initiator_in neighbors_valid symmetric
      reachable) as rooted.
    apply echo_ir_parent_chain_has_path.
    now apply rooted with (parent := parent).
Qed.

(** Finished configured processes are discovered, so the same direct path
    theorem applies to them. *)
Theorem echo_reachable_finished_reaches_initiator
    config state owner :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_reachable node node_eq config state ->
  In owner (ir_config_nodes config) ->
  echo_ir_finished_value node state owner = true ->
  echo_ir_reaches_initiator config state owner.
Proof.
  intros initiator_in neighbors_valid symmetric reachable owner_in finished.
  eapply echo_reachable_discovered_reaches_initiator; eauto.
  right. right. right. now rewrite finished.
Qed.

Lemma echo_complete_started_and_finished_or_isolated config state :
  echo_complete node node_eq config state ->
  echo_ir_started_value state = true /\
  (echo_ir_finished_value node state
      (echo_ir_config_initiator node config) = true \/
   ir_config_neighbors config
      (echo_ir_config_initiator node config) = []).
Proof.
  intro complete.
  unfold echo_complete, echo_program, eval_ir_state_predicate in complete.
  unfold echo_ir_program, echo_ir_complete_expr, echo_ir_started,
    echo_ir_is_empty, echo_ir_pending, echo_ir_initiator,
    echo_ir_finished, echo_ir_neighbors in complete.
  cbn [ir_program_complete] in complete.
  cbn [eval_ir_expr] in complete.
  rewrite (ir_node_value_eta (ir_config_fields config EchoIRInitiator))
    in complete.
  cbn in complete.
  rewrite (echo_ir_bool_value_eta node
    (ir_global_fields state EchoIRStarted)) in complete.
  cbn in complete.
  rewrite (ir_list_node_value_eta
    (ir_processes state
      (ir_node_value_contents (ir_config_fields config EchoIRInitiator))
      EchoIRPending)) in complete.
  cbn in complete.
  rewrite (echo_ir_bool_value_eta node
    (ir_processes state
      (ir_node_value_contents (ir_config_fields config EchoIRInitiator))
      EchoIRFinished)) in complete.
  cbn in complete.
  destruct (echo_ir_bool_value_contents node
    (ir_global_fields state EchoIRStarted)) eqn:started;
    [|discriminate].
  destruct (ir_list_node_value_contents
    (ir_processes state
      (ir_node_value_contents (ir_config_fields config EchoIRInitiator))
      EchoIRPending)); [|discriminate].
  destruct (ir_message_store state); [|discriminate].
  destruct (echo_ir_bool_value_contents node
    (ir_processes state
      (ir_node_value_contents (ir_config_fields config EchoIRInitiator))
      EchoIRFinished)) eqn:finished.
  - split.
    + unfold echo_ir_started_value.
      rewrite (echo_ir_bool_value_eta node
        (ir_global_fields state EchoIRStarted)).
      exact started.
    + left. unfold echo_ir_finished_value.
      rewrite (echo_ir_bool_value_eta node
        (ir_processes state (echo_ir_config_initiator node config)
          EchoIRFinished)).
      unfold echo_ir_config_initiator. exact finished.
  - destruct (ir_config_neighbors config
      (ir_node_value_contents (ir_config_fields config EchoIRInitiator)))
      eqn:neighbors;
      [|discriminate].
    split.
    + unfold echo_ir_started_value.
      rewrite (echo_ir_bool_value_eta node
        (ir_global_fields state EchoIRStarted)).
      exact started.
    + now right.
Qed.

(** Public direct spanning-tree theorem for the generated executable.  No
    legacy Echo transition relation, compatibility state, or simulation
    theorem appears in its statement or proof. *)
Theorem echo_reachable_finished_root_spanning_tree
    config state (wave_depth : node -> nat) :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  (forall owner,
    In owner (ir_config_nodes config) ->
    owner <> echo_ir_config_initiator node config ->
    exists parent,
      In parent (ir_config_nodes config) /\
      In owner (ir_config_neighbors config parent) /\
      wave_depth parent < wave_depth owner) ->
  echo_reachable node node_eq config state ->
  echo_ir_started_value state = true ->
  echo_ir_finished_value node state
    (echo_ir_config_initiator node config) = true ->
  forall owner,
    In owner (ir_config_nodes config) ->
    echo_ir_reaches_initiator config state owner.
Proof.
  intros initiator_in neighbors_valid symmetric connected reachable
    started root_finished owner owner_in.
  assert (reached : echo_ir_reached config state owner).
  { eapply echo_reachable_finished_root_all_reached; eauto. }
  eapply echo_reachable_discovered_reaches_initiator; eauto.
Qed.

Lemma echo_ir_empty_initiator_neighbors_only_node
    config (wave_depth : node -> nat) :
  (forall owner,
    In owner (ir_config_nodes config) ->
    owner <> echo_ir_config_initiator node config ->
    exists parent,
      In parent (ir_config_nodes config) /\
      In owner (ir_config_neighbors config parent) /\
      wave_depth parent < wave_depth owner) ->
  ir_config_neighbors config
    (echo_ir_config_initiator node config) = [] ->
  forall owner,
    In owner (ir_config_nodes config) ->
    owner = echo_ir_config_initiator node config.
Proof.
  intros connected root_isolated.
  apply (well_founded_ind
    (wf_inverse_image node nat lt wave_depth lt_wf)
    (fun owner =>
      In owner (ir_config_nodes config) ->
      owner = echo_ir_config_initiator node config)).
  intros owner IH owner_in.
  destruct (node_eq owner (echo_ir_config_initiator node config))
    as [root | nonroot]; [exact root |].
  destruct (connected owner owner_in nonroot) as
    [parent [parent_in [adjacent lower]]].
  specialize (IH parent lower parent_in). subst parent.
  rewrite root_isolated in adjacent. contradiction.
Qed.

(** Completion uses either the normal finished-root case or the isolated-root
    case admitted by the generated completion predicate. *)
Theorem echo_reachable_complete_spanning_tree
    config state (wave_depth : node -> nat) :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  (forall owner,
    In owner (ir_config_nodes config) ->
    owner <> echo_ir_config_initiator node config ->
    exists parent,
      In parent (ir_config_nodes config) /\
      In owner (ir_config_neighbors config parent) /\
      wave_depth parent < wave_depth owner) ->
  echo_reachable node node_eq config state ->
  echo_complete node node_eq config state ->
  forall owner,
    In owner (ir_config_nodes config) ->
    echo_ir_reaches_initiator config state owner.
Proof.
  intros initiator_in neighbors_valid symmetric connected reachable complete
    owner owner_in.
  destruct (echo_complete_started_and_finished_or_isolated
    config state complete) as [started [root_finished | root_isolated]].
  - eapply echo_reachable_finished_root_spanning_tree; eauto.
  - pose proof (echo_ir_empty_initiator_neighbors_only_node
      config wave_depth connected root_isolated owner owner_in) as root.
    subst owner. exists 0. reflexivity.
Qed.

End EchoIRExecutableSpanningTree.
