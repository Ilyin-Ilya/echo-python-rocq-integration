(** * Reverse-simulation infrastructure for the generic Echo IR

    These theorems reconstruct temporary old executable events from successful
    generic interpreter results.  Delivery reconstruction always starts from
    the authoritative queued message selected by numeric ID; no duplicated
    scheduler-supplied message record is trusted. *)

From Stdlib Require Import List Bool Arith Sorting.Permutation.
Import ListNotations.
Require Import EchoAlgorithm EchoExecutableTypes EchoTransitionIR
  EchoExecutableReachability ProtocolIRTypes ProtocolIRExpressions ProtocolIRActions
  ProtocolIRInterpreter ProtocolIRRunner EchoIRSignature EchoIRProgram EchoIRCompatibility
  EchoIRRuleUniqueness EchoIRForwardSimulation.

Section EchoIRBackwardSimulation.

Variable node : Type.
Variable node_eq : forall left right : node,
  {left = right} + {left <> right}.
Variable config : @echo_config node.

(** Common reverse-delivery decomposition.  A reported Echo rule identifier
    determines the concrete selected rule, while numeric-ID resolution yields
    the originating old queued message. *)
Lemma echo_ir_delivery_success_components_for_rule
    (state : @executable_echo_state node)
    (selected_id : nat)
    (certificates : ir_delivery_certificates node echo_ir_signature)
    (reported_id : echo_ir_rule_id)
    (expected_rule : ir_rule node echo_ir_signature)
    (ir_successor : ir_protocol_state node echo_ir_signature) :
  In expected_rule (@echo_ir_rules node) ->
  ir_rule_id expected_rule = reported_id ->
  interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state)
      (IRProtocolDeliver selected_id certificates) =
    @IRStepSuccess node echo_ir_signature reported_id ir_successor ->
  exists message,
    In message (message_store state) /\
    selected_id = message_id message /\
    eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
      expected_rule = IRRuleEnabled /\
    eval_ir_action node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
      (ir_rule_action expected_rule) = Some ir_successor.
Proof.
  intros expected_in expected_identifier interpreted.
  destruct (interpret_protocol_rules_success_components
    node_eq (echo_ir_encode_config config) (@echo_ir_rules node)
    (echo_ir_encode_state state) (IRProtocolDeliver selected_id certificates)
    reported_id ir_successor interpreted) as
    [runtime_event [selected_rule
      [resolved [selected [selected_identifier action]]]]].
  destruct (@echo_ir_resolved_delivery_source node
    state selected_id certificates runtime_event resolved) as
    [message [queued [message_identifier runtime_is_delivery]]].
  subst runtime_event.
  pose proof (select_ir_rule_unique_in node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_rules node) selected_rule selected) as selected_in.
  assert (selected_rule = expected_rule) as selected_is_expected.
  {
    eapply echo_ir_rule_identifier_injective.
    - exact selected_in.
    - exact expected_in.
    - now rewrite selected_identifier, expected_identifier.
  }
  subst selected_rule.
  exists message. split; [exact queued |].
  split; [exact message_identifier |].
  split.
  - exact (select_ir_rule_unique_is_enabled node_eq
      (echo_ir_encode_config config) (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
      (@echo_ir_rules node) expected_rule selected).
  - exact action.
Qed.

(** Reverse direction of the generic list-membership test.  The forward
    bridge already proves [In -> ir_node_in = true]; reverse simulation needs
    the converse when an enabled generic guard is turned back into an old
    executable guard. *)
Lemma echo_ir_node_in_true_implies_in
    (selected : node)
    (items : list node) :
  ir_node_in node_eq selected items = true -> In selected items.
Proof.
  induction items as [|candidate rest IH]; intro contained.
  - discriminate.
  - cbn [ir_node_in] in contained.
    destruct (node_eq selected candidate) as [same | different].
    + now left.
    + right. now apply IH.
Qed.

(** A successful generic non-leaf request reconstructs an actual queued old
    message, the forwarding-order certificate, a valid old [EchoStep], and an
    old successor corresponding to the generic successor. *)
Theorem echo_ir_first_request_nonleaf_backward_simulates
    (state : @executable_echo_state node)
    (selected_id : nat)
    (certificates : ir_delivery_certificates node echo_ir_signature)
    (ir_successor : ir_protocol_state node echo_ir_signature) :
  interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state)
      (IRProtocolDeliver selected_id certificates) =
    @IRStepSuccess node echo_ir_signature
      EchoIRFirstRequestNonLeafRule ir_successor ->
  exists message successor,
    In message (message_store state) /\
    selected_id = message_id message /\
    @EchoStep node node_eq config state
      (EchoFirstRequestNonLeaf message
        (@echo_ir_delivery_forward_order_value node certificates)) successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intro interpreted.
  destruct (interpret_protocol_rules_success_components
    node_eq (echo_ir_encode_config config) (@echo_ir_rules node)
    (echo_ir_encode_state state) (IRProtocolDeliver selected_id certificates)
    EchoIRFirstRequestNonLeafRule ir_successor interpreted) as
    [runtime_event [selected_rule
      [resolved [selected [selected_rule_id action]]]]].
  destruct (@echo_ir_resolved_delivery_source node
    state selected_id certificates runtime_event resolved) as
    [message [queued [message_identifier runtime_is_delivery]]].
  subst runtime_event.
  pose proof (select_ir_rule_unique_in node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_rules node) selected_rule selected) as selected_in.
  assert (expected_in :
    In (@echo_ir_first_request_nonleaf_rule node) (@echo_ir_rules node)).
  {
    cbn [echo_ir_rules]. now right; left.
  }
  assert (selected_rule = @echo_ir_first_request_nonleaf_rule node)
    as selected_is_expected.
  {
    eapply echo_ir_rule_identifier_injective.
    - exact selected_in.
    - exact expected_in.
    - cbn [echo_ir_first_request_nonleaf_rule ir_rule_id].
      exact selected_rule_id.
  }
  subst selected_rule.
  pose proof (select_ir_rule_unique_is_enabled node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_rules node) (@echo_ir_first_request_nonleaf_rule node)
    selected) as enabled.
  pose proof (eval_ir_rule_enabled_pattern node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_first_request_nonleaf_rule node) enabled) as request_pattern.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_first_request_nonleaf_rule node)
    (@echo_ir_not_equal node IRNode (@echo_ir_receiver node)
      (@echo_ir_initiator node)) enabled ltac:(
        cbn [echo_ir_first_request_nonleaf_rule echo_ir_process_initial];
        repeat (first [left; reflexivity | right]))) as receiver_not_initiator.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_first_request_nonleaf_rule node)
    (@echo_ir_equal node IROptionNode
      (@echo_ir_parent node (@echo_ir_receiver node))
      (@echo_ir_option_none node)) enabled ltac:(
        cbn [echo_ir_first_request_nonleaf_rule echo_ir_process_initial];
        repeat (first [left; reflexivity | right]))) as receiver_parent_none.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_first_request_nonleaf_rule node)
    (@echo_ir_equal node IRListNode
      (@echo_ir_pending node (@echo_ir_receiver node))
      (@echo_ir_empty_nodes node)) enabled ltac:(
        cbn [echo_ir_first_request_nonleaf_rule echo_ir_process_initial];
        repeat (first [left; reflexivity | right]))) as receiver_pending_empty.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_first_request_nonleaf_rule node)
    (@echo_ir_equal node IRBool
      (@echo_ir_finished node (@echo_ir_receiver node))
      (@echo_ir_bool node false)) enabled ltac:(
        cbn [echo_ir_first_request_nonleaf_rule echo_ir_process_initial];
        repeat (first [left; reflexivity | right]))) as receiver_not_finished.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_first_request_nonleaf_rule node)
    (IRListPermutationExpr (@echo_ir_forward_order node)
      (@echo_ir_forward_targets node)) enabled ltac:(
        cbn [echo_ir_first_request_nonleaf_rule echo_ir_process_initial];
        repeat (first [left; reflexivity | right]))) as forwarding_permutation.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_first_request_nonleaf_rule node)
    (@echo_ir_nonempty node (@echo_ir_forward_order node)) enabled ltac:(
        cbn [echo_ir_first_request_nonleaf_rule echo_ir_process_initial];
        repeat (first [left; reflexivity | right]))) as forwarding_nonempty.
  cbn [echo_ir_first_request_nonleaf_rule ir_rule_pattern
    ir_event_pattern_matches echo_ir_encode_message echo_ir_encode_kind
    ir_message_kind] in request_pattern.
  cbn [eval_ir_expr echo_ir_not_equal echo_ir_equal echo_ir_receiver
    echo_ir_initiator echo_ir_parent echo_ir_pending echo_ir_finished
    echo_ir_option_none echo_ir_empty_nodes echo_ir_bool
    echo_ir_forward_order echo_ir_forward_targets echo_ir_remove
    echo_ir_sender echo_ir_neighbors echo_ir_nonempty echo_ir_is_empty
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_message ir_processes
    ir_config_fields ir_config_neighbors ir_message_sender ir_message_receiver
    ir_event_message ir_value_eqb echo_ir_signature echo_ir_local_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type]
    in receiver_not_initiator, receiver_parent_none,
      receiver_pending_empty, receiver_not_finished,
      forwarding_permutation, forwarding_nonempty.
  assert (request_kind : message_kind message = EchoRequest).
  {
    destruct (message_kind message) eqn:kind; [reflexivity |].
    cbn [echo_ir_encode_kind] in request_pattern.
    destruct (signature_message_kind_eq_dec echo_ir_signature
      EchoIRRequest EchoIRReply); discriminate.
  }
  inversion receiver_not_initiator as [receiver_not_initiator_bool].
  apply Bool.negb_true_iff in receiver_not_initiator_bool.
  assert (receiver_different :
    message_receiver message <> config_initiator config).
  {
    unfold ir_node_eqb in receiver_not_initiator_bool.
    destruct (node_eq (message_receiver message) (config_initiator config))
      as [same | different].
    - discriminate.
    - exact different.
  }
  inversion receiver_parent_none as [receiver_parent_none_bool].
  inversion receiver_pending_empty as [receiver_pending_empty_bool].
  inversion receiver_not_finished as [receiver_not_finished_bool].
  assert (receiver_initial :
    processes state (message_receiver message) = initial_echo_process).
  {
    destruct (processes state (message_receiver message))
      as [parent pending finished] eqn:receiver_process.
    cbn [process_parent] in receiver_parent_none_bool.
    unfold ir_option_node_eqb in receiver_parent_none_bool.
    destruct parent; try discriminate.
    cbn [process_pending] in receiver_pending_empty_bool.
    destruct pending; try discriminate.
    cbn [process_finished] in receiver_not_finished_bool.
    cbn [initial_echo_process].
    destruct finished; try discriminate. reflexivity.
  }
  set (ordered_forwards :=
    @echo_ir_delivery_forward_order_value node certificates).
  assert (certificate_order :
    certificates EchoIRForwardOrder = IRListNodeValue ordered_forwards).
  {
    subst ordered_forwards.
    apply ir_list_node_value_eta.
  }
  rewrite certificate_order in forwarding_permutation, forwarding_nonempty.
  cbn in forwarding_permutation, forwarding_nonempty.
  inversion forwarding_permutation as [forwarding_permutation_bool].
  apply (proj1 (ir_node_list_permutationb_true_iff node_eq
    ordered_forwards
    (ir_remove_node node_eq (message_sender message)
      (nbrs (config_nodes config) (config_adjacent config)
        (message_receiver message))))) in forwarding_permutation_bool.
  inversion forwarding_nonempty as [forwarding_nonempty_bool].
  apply Bool.negb_true_iff in forwarding_nonempty_bool.
  assert (forwarding_nonempty_prop : ordered_forwards <> []).
  {
    destruct ordered_forwards; [discriminate | congruence].
  }
  rewrite echo_ir_remove_node_agrees in forwarding_permutation_bool.
  assert (old_guards :
    @EchoTransitionIR.eval_guards node node_eq config state
      (EchoFirstRequestNonLeaf message ordered_forwards)
      (EchoTransitionIR.ir_rule_guards first_echo_nonleaf_rule) = true).
  {
    apply (proj2 (@eval_guards_true_iff node node_eq config state
      (EchoFirstRequestNonLeaf message ordered_forwards)
      (EchoTransitionIR.ir_rule_guards first_echo_nonleaf_rule))).
    unfold first_echo_nonleaf_rule. repeat constructor.
    - cbn [guard_holds event_message]. exact request_kind.
    - cbn [guard_holds eval_node_expr event_message].
      exact receiver_different.
    - cbn [guard_holds event_message]. exact queued.
    - cbn [guard_holds eval_node_expr event_message].
      exact receiver_initial.
    - cbn [guard_holds eval_nodes_expr eval_node_expr event_message
        event_ordered_nodes].
      exact forwarding_permutation_bool.
    - cbn [guard_holds eval_nodes_expr event_ordered_nodes].
      exact forwarding_nonempty_prop.
  }
  assert (old_step :
    @EchoStep node node_eq config state
      (EchoFirstRequestNonLeaf message ordered_forwards)
      (@EchoTransitionIR.eval_action node node_eq config state
        (EchoFirstRequestNonLeaf message ordered_forwards)
        (EchoTransitionIR.ir_rule_action first_echo_nonleaf_rule))).
  {
    unfold EchoStep, echo_exec, EchoTransitionIR.echo_exec,
      interpret_echo_program.
    change
      ((if @EchoTransitionIR.eval_guards node node_eq config state
          (EchoFirstRequestNonLeaf message ordered_forwards)
          (EchoTransitionIR.ir_rule_guards first_echo_nonleaf_rule)
        then Some (@EchoTransitionIR.eval_action node node_eq config state
          (EchoFirstRequestNonLeaf message ordered_forwards)
          (EchoTransitionIR.ir_rule_action first_echo_nonleaf_rule))
        else None) =
       Some (@EchoTransitionIR.eval_action node node_eq config state
         (EchoFirstRequestNonLeaf message ordered_forwards)
         (EchoTransitionIR.ir_rule_action first_echo_nonleaf_rule))).
    now rewrite old_guards.
  }
  exists message.
  exists (@EchoTransitionIR.eval_action node node_eq config state
    (EchoFirstRequestNonLeaf message ordered_forwards)
    (EchoTransitionIR.ir_rule_action first_echo_nonleaf_rule)).
  split; [exact queued |].
  split; [exact message_identifier |].
  split; [exact old_step |].
  destruct (@echo_ir_first_request_nonleaf_action_forward
    node node_eq config state
    (@EchoTransitionIR.eval_action node node_eq config state
      (EchoFirstRequestNonLeaf message ordered_forwards)
      (EchoTransitionIR.ir_rule_action first_echo_nonleaf_rule))
    message ordered_forwards old_step) as
    [simulated_successor [simulated_action correspondence]].
  unfold echo_ir_first_request_nonleaf_rule in action, simulated_action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action
    echo_ir_set_parent echo_ir_set_pending echo_ir_set_finished
    echo_ir_emit_many echo_ir_receiver echo_ir_sender echo_ir_some
    echo_ir_forward_order echo_ir_bool echo_ir_empty_payload
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_globals echo_ir_encode_message
    echo_ir_delivery_certificates echo_ir_event_forward_order
    echo_ir_event_expected_parent eval_ir_expr ir_set_local_field
    ir_remove_selected_message ir_emit_messages eval_ir_payload_exprs
    ir_event_message ir_message_id ir_message_sender ir_message_receiver
    echo_ir_signature echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type]
    in action, simulated_action.
  rewrite certificate_order in action.
  rewrite action in simulated_action. inversion simulated_action. subst.
  exact correspondence.
Qed.

(** The leaf request case needs no delivery certificate in its action.  The
    selected generic rule nevertheless proves the request kind, participant
    receiver, initial local process, and empty forwarding target list needed
    by the old executable rule. *)
Theorem echo_ir_first_request_leaf_backward_simulates
    (state : @executable_echo_state node)
    (selected_id : nat)
    (certificates : ir_delivery_certificates node echo_ir_signature)
    (ir_successor : ir_protocol_state node echo_ir_signature) :
  interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state)
      (IRProtocolDeliver selected_id certificates) =
    @IRStepSuccess node echo_ir_signature
      EchoIRFirstRequestLeafRule ir_successor ->
  exists message successor,
    In message (message_store state) /\
    selected_id = message_id message /\
    @EchoStep node node_eq config state
      (EchoFirstRequestLeaf message) successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intro interpreted.
  destruct (echo_ir_delivery_success_components_for_rule
    state selected_id certificates
    EchoIRFirstRequestLeafRule (@echo_ir_first_request_leaf_rule node)
    ir_successor ltac:(cbn [echo_ir_rules]; now right; right; left)
    eq_refl interpreted) as
    [message [queued [message_identifier [enabled action]]]].
  pose proof (eval_ir_rule_enabled_pattern node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_first_request_leaf_rule node) enabled) as request_pattern.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_first_request_leaf_rule node)
    (@echo_ir_not_equal node IRNode (@echo_ir_receiver node)
      (@echo_ir_initiator node)) enabled ltac:(
        cbn [echo_ir_first_request_leaf_rule echo_ir_process_initial];
        repeat (first [left; reflexivity | right]))) as receiver_not_initiator.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_first_request_leaf_rule node)
    (@echo_ir_equal node IROptionNode
      (@echo_ir_parent node (@echo_ir_receiver node))
      (@echo_ir_option_none node)) enabled ltac:(
        cbn [echo_ir_first_request_leaf_rule echo_ir_process_initial];
        repeat (first [left; reflexivity | right]))) as receiver_parent_none.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_first_request_leaf_rule node)
    (@echo_ir_equal node IRListNode
      (@echo_ir_pending node (@echo_ir_receiver node))
      (@echo_ir_empty_nodes node)) enabled ltac:(
        cbn [echo_ir_first_request_leaf_rule echo_ir_process_initial];
        repeat (first [left; reflexivity | right]))) as receiver_pending_empty.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_first_request_leaf_rule node)
    (@echo_ir_equal node IRBool
      (@echo_ir_finished node (@echo_ir_receiver node))
      (@echo_ir_bool node false)) enabled ltac:(
        cbn [echo_ir_first_request_leaf_rule echo_ir_process_initial];
        repeat (first [left; reflexivity | right]))) as receiver_not_finished.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_first_request_leaf_rule node)
    (@echo_ir_is_empty node (@echo_ir_forward_targets node)) enabled ltac:(
        cbn [echo_ir_first_request_leaf_rule echo_ir_process_initial];
        repeat (first [left; reflexivity | right]))) as no_forward_targets.
  cbn [echo_ir_first_request_leaf_rule ir_rule_pattern
    ir_event_pattern_matches echo_ir_encode_message echo_ir_encode_kind
    ir_message_kind] in request_pattern.
  cbn [eval_ir_expr echo_ir_not_equal echo_ir_equal echo_ir_receiver
    echo_ir_initiator echo_ir_parent echo_ir_pending echo_ir_finished
    echo_ir_option_none echo_ir_empty_nodes echo_ir_bool
    echo_ir_forward_targets echo_ir_remove echo_ir_sender echo_ir_neighbors
    echo_ir_is_empty echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_message
    ir_processes ir_config_fields ir_config_neighbors ir_message_sender
    ir_message_receiver ir_event_message ir_value_eqb echo_ir_signature
    echo_ir_local_field_type echo_ir_config_field_type]
    in receiver_not_initiator, receiver_parent_none,
      receiver_pending_empty, receiver_not_finished, no_forward_targets.
  assert (request_kind : message_kind message = EchoRequest).
  {
    destruct (message_kind message) eqn:kind; [reflexivity |].
    cbn [echo_ir_encode_kind] in request_pattern.
    destruct (signature_message_kind_eq_dec echo_ir_signature
      EchoIRRequest EchoIRReply); discriminate.
  }
  inversion receiver_not_initiator as [receiver_not_initiator_bool].
  apply Bool.negb_true_iff in receiver_not_initiator_bool.
  assert (receiver_different :
    message_receiver message <> config_initiator config).
  {
    unfold ir_node_eqb in receiver_not_initiator_bool.
    destruct (node_eq (message_receiver message) (config_initiator config))
      as [same | different].
    - discriminate.
    - exact different.
  }
  inversion receiver_parent_none as [receiver_parent_none_bool].
  inversion receiver_pending_empty as [receiver_pending_empty_bool].
  inversion receiver_not_finished as [receiver_not_finished_bool].
  assert (receiver_initial :
    processes state (message_receiver message) = initial_echo_process).
  {
    destruct (processes state (message_receiver message))
      as [parent pending finished] eqn:receiver_process.
    cbn [process_parent] in receiver_parent_none_bool.
    unfold ir_option_node_eqb in receiver_parent_none_bool.
    destruct parent; try discriminate.
    cbn [process_pending] in receiver_pending_empty_bool.
    destruct pending; try discriminate.
    cbn [process_finished] in receiver_not_finished_bool.
    cbn [initial_echo_process].
    destruct finished; try discriminate. reflexivity.
  }
  inversion no_forward_targets as [no_forward_targets_bool].
  assert (targets_empty :
    ir_remove_node node_eq (message_sender message)
      (nbrs (config_nodes config) (config_adjacent config)
        (message_receiver message)) = []).
  {
    destruct (ir_remove_node node_eq (message_sender message)
      (nbrs (config_nodes config) (config_adjacent config)
        (message_receiver message))); [reflexivity | discriminate].
  }
  rewrite echo_ir_remove_node_agrees in targets_empty.
  assert (old_guards :
    @EchoTransitionIR.eval_guards node node_eq config state
      (EchoFirstRequestLeaf message)
      (EchoTransitionIR.ir_rule_guards first_echo_leaf_rule) = true).
  {
    apply (proj2 (@eval_guards_true_iff node node_eq config state
      (EchoFirstRequestLeaf message)
      (EchoTransitionIR.ir_rule_guards first_echo_leaf_rule))).
    unfold first_echo_leaf_rule. repeat constructor.
    - cbn [guard_holds event_message]. exact request_kind.
    - cbn [guard_holds eval_node_expr event_message].
      exact receiver_different.
    - cbn [guard_holds event_message]. exact queued.
    - cbn [guard_holds eval_node_expr event_message].
      exact receiver_initial.
    - cbn [guard_holds eval_nodes_expr eval_node_expr event_message].
      exact targets_empty.
  }
  assert (old_step :
    @EchoStep node node_eq config state (EchoFirstRequestLeaf message)
      (@EchoTransitionIR.eval_action node node_eq config state
        (EchoFirstRequestLeaf message)
        (EchoTransitionIR.ir_rule_action first_echo_leaf_rule))).
  {
    unfold EchoStep, echo_exec, EchoTransitionIR.echo_exec,
      interpret_echo_program.
    change
      ((if @EchoTransitionIR.eval_guards node node_eq config state
          (EchoFirstRequestLeaf message)
          (EchoTransitionIR.ir_rule_guards first_echo_leaf_rule)
        then Some (@EchoTransitionIR.eval_action node node_eq config state
          (EchoFirstRequestLeaf message)
          (EchoTransitionIR.ir_rule_action first_echo_leaf_rule))
        else None) =
       Some (@EchoTransitionIR.eval_action node node_eq config state
         (EchoFirstRequestLeaf message)
         (EchoTransitionIR.ir_rule_action first_echo_leaf_rule))).
    now rewrite old_guards.
  }
  exists message.
  exists (@EchoTransitionIR.eval_action node node_eq config state
    (EchoFirstRequestLeaf message)
    (EchoTransitionIR.ir_rule_action first_echo_leaf_rule)).
  split; [exact queued |].
  split; [exact message_identifier |].
  split; [exact old_step |].
  destruct (@echo_ir_first_request_leaf_action_forward
    node node_eq config state
    (@EchoTransitionIR.eval_action node node_eq config state
      (EchoFirstRequestLeaf message)
      (EchoTransitionIR.ir_rule_action first_echo_leaf_rule))
    message old_step) as
    [simulated_successor [simulated_action correspondence]].
  unfold echo_ir_first_request_leaf_rule in action, simulated_action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action
    echo_ir_set_parent echo_ir_set_pending echo_ir_set_finished
    echo_ir_emit_one echo_ir_receiver echo_ir_sender echo_ir_some
    echo_ir_empty_nodes echo_ir_bool echo_ir_empty_payload
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_globals echo_ir_encode_message
    echo_ir_delivery_certificates echo_ir_event_forward_order
    echo_ir_event_expected_parent eval_ir_expr ir_set_local_field
    ir_remove_selected_message ir_emit_messages eval_ir_payload_exprs
    ir_event_message ir_message_id ir_message_sender ir_message_receiver
    echo_ir_signature echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type]
    in action, simulated_action.
  rewrite action in simulated_action. inversion simulated_action. subst.
  exact correspondence.
Qed.

(** Repeated requests are reconstructed from the generic "process seen"
    predicate.  Its boolean disjunction yields exactly the old guard saying
    that the receiver has a parent or has already finished. *)
Theorem echo_ir_repeated_request_backward_simulates
    (state : @executable_echo_state node)
    (selected_id : nat)
    (certificates : ir_delivery_certificates node echo_ir_signature)
    (ir_successor : ir_protocol_state node echo_ir_signature) :
  interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state)
      (IRProtocolDeliver selected_id certificates) =
    @IRStepSuccess node echo_ir_signature EchoIRRepeatedRequestRule ir_successor ->
  exists message successor,
    In message (message_store state) /\
    selected_id = message_id message /\
    @EchoStep node node_eq config state
      (EchoRepeatedRequest message) successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intro interpreted.
  destruct (echo_ir_delivery_success_components_for_rule
    state selected_id certificates
    EchoIRRepeatedRequestRule (@echo_ir_repeated_request_rule node)
    ir_successor ltac:(cbn [echo_ir_rules]; now right; right; right; left)
    eq_refl interpreted) as
    [message [queued [message_identifier [enabled action]]]].
  pose proof (eval_ir_rule_enabled_pattern node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_repeated_request_rule node) enabled) as request_pattern.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_repeated_request_rule node)
    (@echo_ir_not_equal node IRNode (@echo_ir_receiver node)
      (@echo_ir_initiator node)) enabled ltac:(
        cbn [echo_ir_repeated_request_rule]; now left))
    as receiver_not_initiator.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_repeated_request_rule node)
    (@echo_ir_process_seen node (@echo_ir_receiver node)) enabled ltac:(
        cbn [echo_ir_repeated_request_rule]; now right; left))
    as receiver_seen.
  cbn [echo_ir_repeated_request_rule ir_rule_pattern
    ir_event_pattern_matches echo_ir_encode_message echo_ir_encode_kind
    ir_message_kind] in request_pattern.
  cbn [eval_ir_expr echo_ir_not_equal echo_ir_equal echo_ir_receiver
    echo_ir_initiator echo_ir_process_seen echo_ir_parent echo_ir_finished
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_message ir_processes
    ir_config_fields ir_message_receiver ir_event_message ir_value_eqb
    echo_ir_signature echo_ir_local_field_type echo_ir_config_field_type]
    in receiver_not_initiator, receiver_seen.
  assert (request_kind : message_kind message = EchoRequest).
  {
    destruct (message_kind message) eqn:kind; [reflexivity |].
    cbn [echo_ir_encode_kind] in request_pattern.
    destruct (signature_message_kind_eq_dec echo_ir_signature
      EchoIRRequest EchoIRReply); discriminate.
  }
  inversion receiver_not_initiator as [receiver_not_initiator_bool].
  apply Bool.negb_true_iff in receiver_not_initiator_bool.
  assert (receiver_different :
    message_receiver message <> config_initiator config).
  {
    unfold ir_node_eqb in receiver_not_initiator_bool.
    destruct (node_eq (message_receiver message) (config_initiator config))
      as [same | different].
    - discriminate.
    - exact different.
  }
  inversion receiver_seen as [receiver_seen_bool].
  assert (receiver_has_parent_or_finished :
    (exists parent,
      process_parent (processes state (message_receiver message)) =
        Some parent) \/
    process_finished (processes state (message_receiver message)) = true).
  {
    destruct (process_parent (processes state (message_receiver message)))
      as [parent |] eqn:parent_state.
    - left. now exists parent.
    - cbn in receiver_seen_bool.
      right. exact receiver_seen_bool.
  }
  assert (old_guards :
    @EchoTransitionIR.eval_guards node node_eq config state
      (EchoRepeatedRequest message)
      (EchoTransitionIR.ir_rule_guards repeated_echo_rule) = true).
  {
    apply (proj2 (@eval_guards_true_iff node node_eq config state
      (EchoRepeatedRequest message)
      (EchoTransitionIR.ir_rule_guards repeated_echo_rule))).
    unfold repeated_echo_rule. constructor.
    - cbn [guard_holds event_message]. exact request_kind.
    - constructor.
      + cbn [guard_holds eval_node_expr event_message].
        exact receiver_different.
      + constructor.
        * cbn [guard_holds event_message]. exact queued.
        * constructor.
          -- cbn [guard_holds eval_node_expr event_message].
             exact receiver_has_parent_or_finished.
          -- constructor.
  }
  assert (old_step :
    @EchoStep node node_eq config state (EchoRepeatedRequest message)
      (@EchoTransitionIR.eval_action node node_eq config state
        (EchoRepeatedRequest message)
        (EchoTransitionIR.ir_rule_action repeated_echo_rule))).
  {
    unfold EchoStep, echo_exec, EchoTransitionIR.echo_exec,
      interpret_echo_program.
    change
      ((if @EchoTransitionIR.eval_guards node node_eq config state
          (EchoRepeatedRequest message)
          (EchoTransitionIR.ir_rule_guards repeated_echo_rule)
        then Some (@EchoTransitionIR.eval_action node node_eq config state
          (EchoRepeatedRequest message)
          (EchoTransitionIR.ir_rule_action repeated_echo_rule))
        else None) =
       Some (@EchoTransitionIR.eval_action node node_eq config state
         (EchoRepeatedRequest message)
         (EchoTransitionIR.ir_rule_action repeated_echo_rule))).
    now rewrite old_guards.
  }
  exists message.
  exists (@EchoTransitionIR.eval_action node node_eq config state
    (EchoRepeatedRequest message)
    (EchoTransitionIR.ir_rule_action repeated_echo_rule)).
  split; [exact queued |].
  split; [exact message_identifier |].
  split; [exact old_step |].
  destruct (@echo_ir_repeated_request_action_forward
    node node_eq config state
    (@EchoTransitionIR.eval_action node node_eq config state
      (EchoRepeatedRequest message)
      (EchoTransitionIR.ir_rule_action repeated_echo_rule))
    message old_step) as
    [simulated_successor [simulated_action correspondence]].
  unfold echo_ir_repeated_request_rule in action, simulated_action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action echo_ir_emit_one
    echo_ir_receiver echo_ir_sender echo_ir_empty_payload
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_globals echo_ir_encode_message
    echo_ir_delivery_certificates echo_ir_event_forward_order
    echo_ir_event_expected_parent eval_ir_expr ir_remove_selected_message
    ir_emit_messages eval_ir_payload_exprs ir_event_message ir_message_id
    ir_message_sender ir_message_receiver echo_ir_signature
    echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type]
    in action, simulated_action.
  rewrite action in simulated_action. inversion simulated_action. subst.
  exact correspondence.
Qed.

(** An initiator-directed request is reconstructed from the generic equality,
    started, and unfinished guards; its action is independent of delivery
    certificates. *)
Theorem echo_ir_initiator_request_backward_simulates
    (state : @executable_echo_state node)
    (selected_id : nat)
    (certificates : ir_delivery_certificates node echo_ir_signature)
    (ir_successor : ir_protocol_state node echo_ir_signature) :
  interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state)
      (IRProtocolDeliver selected_id certificates) =
    @IRStepSuccess node echo_ir_signature EchoIRInitiatorRequestRule ir_successor ->
  exists message successor,
    In message (message_store state) /\
    selected_id = message_id message /\
    @EchoStep node node_eq config state
      (EchoInitiatorRequest message) successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intro interpreted.
  destruct (echo_ir_delivery_success_components_for_rule
    state selected_id certificates
    EchoIRInitiatorRequestRule (@echo_ir_initiator_request_rule node)
    ir_successor ltac:(cbn [echo_ir_rules]; now right; right; right; right; left)
    eq_refl interpreted) as
    [message [queued [message_identifier [enabled action]]]].
  pose proof (eval_ir_rule_enabled_pattern node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_initiator_request_rule node) enabled) as request_pattern.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_initiator_request_rule node)
    (@echo_ir_equal node IRNode (@echo_ir_receiver node)
      (@echo_ir_initiator node)) enabled ltac:(
        cbn [echo_ir_initiator_request_rule]; now left)) as receiver_is_initiator.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_initiator_request_rule node) (@echo_ir_started node)
    enabled ltac:(cbn [echo_ir_initiator_request_rule]; now right; left))
    as protocol_started.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_initiator_request_rule node)
    (@echo_ir_equal node IRBool
      (@echo_ir_finished node (@echo_ir_initiator node))
      (@echo_ir_bool node false)) enabled ltac:(
        cbn [echo_ir_initiator_request_rule]; now right; right; left))
    as initiator_not_finished.
  cbn [echo_ir_initiator_request_rule ir_rule_pattern
    ir_event_pattern_matches echo_ir_encode_message echo_ir_encode_kind
    ir_message_kind] in request_pattern.
  cbn [eval_ir_expr echo_ir_equal echo_ir_receiver echo_ir_initiator
    echo_ir_started echo_ir_finished echo_ir_bool echo_ir_encode_config
    echo_ir_encode_config_fields echo_ir_encode_state echo_ir_encode_process
    echo_ir_encode_globals echo_ir_encode_message ir_processes
    ir_global_fields ir_config_fields ir_message_receiver ir_event_message
    ir_value_eqb echo_ir_signature echo_ir_local_field_type
    echo_ir_global_field_type echo_ir_config_field_type]
    in receiver_is_initiator, protocol_started, initiator_not_finished.
  assert (request_kind : message_kind message = EchoRequest).
  {
    destruct (message_kind message) eqn:kind; [reflexivity |].
    cbn [echo_ir_encode_kind] in request_pattern.
    destruct (signature_message_kind_eq_dec echo_ir_signature
      EchoIRRequest EchoIRReply); discriminate.
  }
  inversion receiver_is_initiator as [receiver_is_initiator_bool].
  assert (receiver_equal :
    message_receiver message = config_initiator config).
  {
    unfold ir_node_eqb in receiver_is_initiator_bool.
    destruct (node_eq (message_receiver message) (config_initiator config))
      as [same | different].
    - exact same.
    - discriminate.
  }
  inversion protocol_started as [protocol_started_bool].
  inversion initiator_not_finished as [initiator_not_finished_bool].
  assert (initiator_not_finished_prop :
    process_finished (processes state (config_initiator config)) = false).
  {
    destruct (process_finished (processes state (config_initiator config)))
      eqn:finished; [discriminate | reflexivity].
  }
  assert (old_guards :
    @EchoTransitionIR.eval_guards node node_eq config state
      (EchoInitiatorRequest message)
      (EchoTransitionIR.ir_rule_guards initiator_echo_rule) = true).
  {
    apply (proj2 (@eval_guards_true_iff node node_eq config state
      (EchoInitiatorRequest message)
      (EchoTransitionIR.ir_rule_guards initiator_echo_rule))).
    unfold initiator_echo_rule. constructor.
    - cbn [guard_holds event_message]. exact request_kind.
    - constructor.
      + cbn [guard_holds eval_node_expr event_message]. exact receiver_equal.
      + constructor.
        * cbn [guard_holds]. exact protocol_started_bool.
        * constructor.
          -- cbn [guard_holds eval_node_expr].
             exact initiator_not_finished_prop.
          -- constructor.
             ++ cbn [guard_holds event_message]. exact queued.
             ++ constructor.
  }
  assert (old_step :
    @EchoStep node node_eq config state (EchoInitiatorRequest message)
      (@EchoTransitionIR.eval_action node node_eq config state
        (EchoInitiatorRequest message)
        (EchoTransitionIR.ir_rule_action initiator_echo_rule))).
  {
    unfold EchoStep, echo_exec, EchoTransitionIR.echo_exec,
      interpret_echo_program.
    change
      ((if @EchoTransitionIR.eval_guards node node_eq config state
          (EchoInitiatorRequest message)
          (EchoTransitionIR.ir_rule_guards initiator_echo_rule)
        then Some (@EchoTransitionIR.eval_action node node_eq config state
          (EchoInitiatorRequest message)
          (EchoTransitionIR.ir_rule_action initiator_echo_rule))
        else None) =
       Some (@EchoTransitionIR.eval_action node node_eq config state
         (EchoInitiatorRequest message)
         (EchoTransitionIR.ir_rule_action initiator_echo_rule))).
    now rewrite old_guards.
  }
  exists message.
  exists (@EchoTransitionIR.eval_action node node_eq config state
    (EchoInitiatorRequest message)
    (EchoTransitionIR.ir_rule_action initiator_echo_rule)).
  split; [exact queued |].
  split; [exact message_identifier |].
  split; [exact old_step |].
  destruct (@echo_ir_initiator_request_action_forward
    node node_eq config state
    (@EchoTransitionIR.eval_action node node_eq config state
      (EchoInitiatorRequest message)
      (EchoTransitionIR.ir_rule_action initiator_echo_rule))
    message old_step) as
    [simulated_successor [simulated_action correspondence]].
  unfold echo_ir_initiator_request_rule in action, simulated_action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action echo_ir_emit_one
    echo_ir_initiator echo_ir_sender echo_ir_empty_payload
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_globals echo_ir_encode_message
    echo_ir_delivery_certificates echo_ir_event_forward_order
    echo_ir_event_expected_parent eval_ir_expr ir_remove_selected_message
    ir_emit_messages eval_ir_payload_exprs ir_event_message ir_message_id
    ir_message_sender ir_message_receiver echo_ir_signature
    echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type]
    in action, simulated_action.
  rewrite action in simulated_action. inversion simulated_action. subst.
  exact correspondence.
Qed.

(** A successful participant reply with work still pending reconstructs the
    expected-parent certificate as the old event witness. *)
Theorem echo_ir_participant_reply_more_backward_simulates
    (state : @executable_echo_state node)
    (selected_id : nat)
    (certificates : ir_delivery_certificates node echo_ir_signature)
    (ir_successor : ir_protocol_state node echo_ir_signature) :
  interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state)
      (IRProtocolDeliver selected_id certificates) =
    @IRStepSuccess node echo_ir_signature
      EchoIRParticipantReplyMoreRule ir_successor ->
  exists message successor,
    In message (message_store state) /\
    selected_id = message_id message /\
    @EchoStep node node_eq config state
      (EchoParticipantReplyMore message
        (@echo_ir_delivery_expected_parent_value node certificates)) successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intro interpreted.
  destruct (echo_ir_delivery_success_components_for_rule
    state selected_id certificates
    EchoIRParticipantReplyMoreRule
    (@echo_ir_participant_reply_more_rule node)
    ir_successor ltac:(
      cbn [echo_ir_rules];
      now right; right; right; right; right; left)
    eq_refl interpreted) as
    [message [queued [message_identifier [enabled action]]]].
  pose proof (eval_ir_rule_enabled_pattern node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_participant_reply_more_rule node) enabled) as reply_pattern.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_participant_reply_more_rule node)
    (@echo_ir_not_equal node IRNode (@echo_ir_receiver node)
      (@echo_ir_initiator node)) enabled ltac:(
        cbn [echo_ir_participant_reply_more_rule]; now left))
    as receiver_not_initiator.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_participant_reply_more_rule node)
    (@echo_ir_equal node IROptionNode
      (@echo_ir_parent node (@echo_ir_receiver node))
      (@echo_ir_some node (@echo_ir_expected_parent node))) enabled ltac:(
        cbn [echo_ir_participant_reply_more_rule]; now right; left))
    as parent_matches.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_participant_reply_more_rule node)
    (IRListContainsExpr (@echo_ir_sender node)
      (@echo_ir_pending node (@echo_ir_receiver node))) enabled ltac:(
        cbn [echo_ir_participant_reply_more_rule];
        now right; right; left)) as sender_pending.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_participant_reply_more_rule node)
    (@echo_ir_nonempty node
      (@echo_ir_removed_pending node (@echo_ir_receiver node))) enabled ltac:(
        cbn [echo_ir_participant_reply_more_rule];
        now right; right; right; left)) as pending_remains.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_participant_reply_more_rule node)
    (@echo_ir_equal node IRBool
      (@echo_ir_finished node (@echo_ir_receiver node))
      (@echo_ir_bool node false)) enabled ltac:(
        cbn [echo_ir_participant_reply_more_rule];
        now right; right; right; right; left)) as receiver_not_finished.
  cbn [echo_ir_participant_reply_more_rule ir_rule_pattern
    ir_event_pattern_matches echo_ir_encode_message echo_ir_encode_kind
    ir_message_kind] in reply_pattern.
  set (parent :=
    @echo_ir_delivery_expected_parent_value node certificates).
  assert (certificate_parent :
    certificates EchoIRExpectedParent = IRNodeValue parent).
  {
    subst parent. apply ir_node_value_eta.
  }
  cbn [eval_ir_expr echo_ir_not_equal echo_ir_equal echo_ir_receiver
    echo_ir_initiator echo_ir_parent echo_ir_some echo_ir_expected_parent
    echo_ir_sender echo_ir_pending echo_ir_nonempty echo_ir_is_empty
    echo_ir_removed_pending echo_ir_remove echo_ir_finished echo_ir_bool
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_message ir_processes
    ir_config_fields ir_message_sender ir_message_receiver ir_event_message
    ir_value_eqb echo_ir_signature echo_ir_local_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type]
    in receiver_not_initiator, parent_matches, sender_pending,
      pending_remains, receiver_not_finished.
  rewrite certificate_parent in parent_matches.
  cbn in parent_matches.
  assert (reply_kind : message_kind message = EchoReply).
  {
    destruct (message_kind message) eqn:kind; [| reflexivity].
    cbn [echo_ir_encode_kind] in reply_pattern.
    destruct (signature_message_kind_eq_dec echo_ir_signature
      EchoIRReply EchoIRRequest); discriminate.
  }
  inversion receiver_not_initiator as [receiver_not_initiator_bool].
  apply Bool.negb_true_iff in receiver_not_initiator_bool.
  assert (receiver_different :
    message_receiver message <> config_initiator config).
  {
    unfold ir_node_eqb in receiver_not_initiator_bool.
    destruct (node_eq (message_receiver message) (config_initiator config))
      as [same | different].
    - discriminate.
    - exact different.
  }
  inversion parent_matches as [parent_matches_bool].
  assert (parent_equal :
    process_parent (processes state (message_receiver message)) =
      Some parent).
  {
    unfold ir_option_node_eqb in parent_matches_bool.
    destruct (process_parent (processes state (message_receiver message)))
      as [actual_parent |] eqn:parent_state; [| discriminate].
    unfold ir_node_eqb in parent_matches_bool.
    destruct (node_eq actual_parent parent) as [same | different].
    - now subst actual_parent.
    - discriminate.
  }
  inversion sender_pending as [sender_pending_bool].
  pose proof (echo_ir_node_in_true_implies_in
    (message_sender message)
    (process_pending (processes state (message_receiver message)))
    sender_pending_bool) as sender_pending_prop.
  inversion pending_remains as [pending_remains_bool].
  apply Bool.negb_true_iff in pending_remains_bool.
  assert (pending_remains_prop :
    remove_echo_node node_eq (message_sender message)
      (process_pending (processes state (message_receiver message))) <> []).
  {
    rewrite <- echo_ir_remove_node_agrees.
    destruct (ir_remove_node node_eq (message_sender message)
      (process_pending (processes state (message_receiver message))));
      [discriminate | congruence].
  }
  inversion receiver_not_finished as [receiver_not_finished_bool].
  assert (receiver_not_finished_prop :
    process_finished (processes state (message_receiver message)) = false).
  {
    destruct (process_finished (processes state (message_receiver message)))
      eqn:finished; [discriminate | reflexivity].
  }
  assert (old_guards :
    @EchoTransitionIR.eval_guards node node_eq config state
      (EchoParticipantReplyMore message parent)
      (EchoTransitionIR.ir_rule_guards participant_ack_more_rule) = true).
  {
    apply (proj2 (@eval_guards_true_iff node node_eq config state
      (EchoParticipantReplyMore message parent)
      (EchoTransitionIR.ir_rule_guards participant_ack_more_rule))).
    unfold participant_ack_more_rule. repeat constructor.
    - cbn [guard_holds event_message]. exact reply_kind.
    - cbn [guard_holds eval_node_expr event_message].
      exact receiver_different.
    - cbn [guard_holds event_message]. exact queued.
    - cbn [guard_holds eval_node_expr eval_parent_expr event_message
        event_parent]. exact parent_equal.
    - cbn [guard_holds eval_node_expr eval_nodes_expr event_message].
      exact sender_pending_prop.
    - cbn [guard_holds eval_node_expr eval_nodes_expr event_message].
      exact pending_remains_prop.
    - cbn [guard_holds eval_node_expr event_message].
      exact receiver_not_finished_prop.
  }
  assert (old_step :
    @EchoStep node node_eq config state
      (EchoParticipantReplyMore message parent)
      (@EchoTransitionIR.eval_action node node_eq config state
        (EchoParticipantReplyMore message parent)
        (EchoTransitionIR.ir_rule_action participant_ack_more_rule))).
  {
    unfold EchoStep, echo_exec, EchoTransitionIR.echo_exec,
      interpret_echo_program.
    change
      ((if @EchoTransitionIR.eval_guards node node_eq config state
          (EchoParticipantReplyMore message parent)
          (EchoTransitionIR.ir_rule_guards participant_ack_more_rule)
        then Some (@EchoTransitionIR.eval_action node node_eq config state
          (EchoParticipantReplyMore message parent)
          (EchoTransitionIR.ir_rule_action participant_ack_more_rule))
        else None) =
       Some (@EchoTransitionIR.eval_action node node_eq config state
         (EchoParticipantReplyMore message parent)
         (EchoTransitionIR.ir_rule_action participant_ack_more_rule))).
    now rewrite old_guards.
  }
  exists message.
  exists (@EchoTransitionIR.eval_action node node_eq config state
    (EchoParticipantReplyMore message parent)
    (EchoTransitionIR.ir_rule_action participant_ack_more_rule)).
  split; [exact queued |].
  split; [exact message_identifier |].
  split; [exact old_step |].
  destruct (@echo_ir_participant_reply_more_action_forward
    node node_eq config state
    (@EchoTransitionIR.eval_action node node_eq config state
      (EchoParticipantReplyMore message parent)
      (EchoTransitionIR.ir_rule_action participant_ack_more_rule))
    message parent old_step) as
    [simulated_successor [simulated_action correspondence]].
  unfold echo_ir_participant_reply_more_rule in action, simulated_action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action
    echo_ir_set_parent echo_ir_set_pending echo_ir_set_finished
    echo_ir_receiver echo_ir_sender echo_ir_some echo_ir_expected_parent
    echo_ir_pending echo_ir_removed_pending echo_ir_remove echo_ir_bool
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_globals echo_ir_encode_message
    echo_ir_delivery_certificates echo_ir_event_forward_order
    echo_ir_event_expected_parent eval_ir_expr ir_set_local_field
    ir_remove_selected_message ir_event_message ir_message_id
    ir_message_sender ir_message_receiver echo_ir_signature
    echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type]
    in action, simulated_action.
  rewrite certificate_parent in action.
  rewrite action in simulated_action. inversion simulated_action. subst.
  exact correspondence.
Qed.

(** The final participant reply uses the same reconstructed parent witness,
    but the removed pending list must be empty and the old action emits the
    participant's reply to that parent. *)
Theorem echo_ir_participant_reply_final_backward_simulates
    (state : @executable_echo_state node)
    (selected_id : nat)
    (certificates : ir_delivery_certificates node echo_ir_signature)
    (ir_successor : ir_protocol_state node echo_ir_signature) :
  interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state)
      (IRProtocolDeliver selected_id certificates) =
    @IRStepSuccess node echo_ir_signature
      EchoIRParticipantReplyFinalRule ir_successor ->
  exists message successor,
    In message (message_store state) /\
    selected_id = message_id message /\
    @EchoStep node node_eq config state
      (EchoParticipantReplyFinal message
        (@echo_ir_delivery_expected_parent_value node certificates)) successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intro interpreted.
  destruct (echo_ir_delivery_success_components_for_rule
    state selected_id certificates
    EchoIRParticipantReplyFinalRule
    (@echo_ir_participant_reply_final_rule node)
    ir_successor ltac:(
      cbn [echo_ir_rules];
      now right; right; right; right; right; right; left)
    eq_refl interpreted) as
    [message [queued [message_identifier [enabled action]]]].
  pose proof (eval_ir_rule_enabled_pattern node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_participant_reply_final_rule node) enabled) as reply_pattern.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_participant_reply_final_rule node)
    (@echo_ir_not_equal node IRNode (@echo_ir_receiver node)
      (@echo_ir_initiator node)) enabled ltac:(
        cbn [echo_ir_participant_reply_final_rule]; now left))
    as receiver_not_initiator.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_participant_reply_final_rule node)
    (@echo_ir_equal node IROptionNode
      (@echo_ir_parent node (@echo_ir_receiver node))
      (@echo_ir_some node (@echo_ir_expected_parent node))) enabled ltac:(
        cbn [echo_ir_participant_reply_final_rule]; now right; left))
    as parent_matches.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_participant_reply_final_rule node)
    (IRListContainsExpr (@echo_ir_sender node)
      (@echo_ir_pending node (@echo_ir_receiver node))) enabled ltac:(
        cbn [echo_ir_participant_reply_final_rule];
        now right; right; left)) as sender_pending.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_participant_reply_final_rule node)
    (@echo_ir_is_empty node
      (@echo_ir_removed_pending node (@echo_ir_receiver node))) enabled ltac:(
        cbn [echo_ir_participant_reply_final_rule];
        now right; right; right; left)) as pending_empty.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_participant_reply_final_rule node)
    (@echo_ir_equal node IRBool
      (@echo_ir_finished node (@echo_ir_receiver node))
      (@echo_ir_bool node false)) enabled ltac:(
        cbn [echo_ir_participant_reply_final_rule];
        now right; right; right; right; left)) as receiver_not_finished.
  cbn [echo_ir_participant_reply_final_rule ir_rule_pattern
    ir_event_pattern_matches echo_ir_encode_message echo_ir_encode_kind
    ir_message_kind] in reply_pattern.
  set (parent :=
    @echo_ir_delivery_expected_parent_value node certificates).
  assert (certificate_parent :
    certificates EchoIRExpectedParent = IRNodeValue parent).
  {
    subst parent. apply ir_node_value_eta.
  }
  cbn [eval_ir_expr echo_ir_not_equal echo_ir_equal echo_ir_receiver
    echo_ir_initiator echo_ir_parent echo_ir_some echo_ir_expected_parent
    echo_ir_sender echo_ir_pending echo_ir_is_empty
    echo_ir_removed_pending echo_ir_remove echo_ir_finished echo_ir_bool
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_message ir_processes
    ir_config_fields ir_message_sender ir_message_receiver ir_event_message
    ir_value_eqb echo_ir_signature echo_ir_local_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type]
    in receiver_not_initiator, parent_matches, sender_pending,
      pending_empty, receiver_not_finished.
  rewrite certificate_parent in parent_matches.
  cbn in parent_matches.
  assert (reply_kind : message_kind message = EchoReply).
  {
    destruct (message_kind message) eqn:kind; [| reflexivity].
    cbn [echo_ir_encode_kind] in reply_pattern.
    destruct (signature_message_kind_eq_dec echo_ir_signature
      EchoIRReply EchoIRRequest); discriminate.
  }
  inversion receiver_not_initiator as [receiver_not_initiator_bool].
  apply Bool.negb_true_iff in receiver_not_initiator_bool.
  assert (receiver_different :
    message_receiver message <> config_initiator config).
  {
    unfold ir_node_eqb in receiver_not_initiator_bool.
    destruct (node_eq (message_receiver message) (config_initiator config))
      as [same | different].
    - discriminate.
    - exact different.
  }
  inversion parent_matches as [parent_matches_bool].
  assert (parent_equal :
    process_parent (processes state (message_receiver message)) =
      Some parent).
  {
    unfold ir_option_node_eqb in parent_matches_bool.
    destruct (process_parent (processes state (message_receiver message)))
      as [actual_parent |] eqn:parent_state; [| discriminate].
    unfold ir_node_eqb in parent_matches_bool.
    destruct (node_eq actual_parent parent) as [same | different].
    - now subst actual_parent.
    - discriminate.
  }
  inversion sender_pending as [sender_pending_bool].
  pose proof (echo_ir_node_in_true_implies_in
    (message_sender message)
    (process_pending (processes state (message_receiver message)))
    sender_pending_bool) as sender_pending_prop.
  inversion pending_empty as [pending_empty_bool].
  assert (pending_empty_prop :
    remove_echo_node node_eq (message_sender message)
      (process_pending (processes state (message_receiver message))) = []).
  {
    rewrite <- echo_ir_remove_node_agrees.
    destruct (ir_remove_node node_eq (message_sender message)
      (process_pending (processes state (message_receiver message))));
      [reflexivity | discriminate].
  }
  inversion receiver_not_finished as [receiver_not_finished_bool].
  assert (receiver_not_finished_prop :
    process_finished (processes state (message_receiver message)) = false).
  {
    destruct (process_finished (processes state (message_receiver message)))
      eqn:finished; [discriminate | reflexivity].
  }
  assert (old_guards :
    @EchoTransitionIR.eval_guards node node_eq config state
      (EchoParticipantReplyFinal message parent)
      (EchoTransitionIR.ir_rule_guards participant_ack_final_rule) = true).
  {
    apply (proj2 (@eval_guards_true_iff node node_eq config state
      (EchoParticipantReplyFinal message parent)
      (EchoTransitionIR.ir_rule_guards participant_ack_final_rule))).
    unfold participant_ack_final_rule. repeat constructor.
    - cbn [guard_holds event_message]. exact reply_kind.
    - cbn [guard_holds eval_node_expr event_message].
      exact receiver_different.
    - cbn [guard_holds event_message]. exact queued.
    - cbn [guard_holds eval_node_expr eval_parent_expr event_message
        event_parent]. exact parent_equal.
    - cbn [guard_holds eval_node_expr eval_nodes_expr event_message].
      exact sender_pending_prop.
    - cbn [guard_holds eval_node_expr eval_nodes_expr event_message].
      exact pending_empty_prop.
    - cbn [guard_holds eval_node_expr event_message].
      exact receiver_not_finished_prop.
  }
  assert (old_step :
    @EchoStep node node_eq config state
      (EchoParticipantReplyFinal message parent)
      (@EchoTransitionIR.eval_action node node_eq config state
        (EchoParticipantReplyFinal message parent)
        (EchoTransitionIR.ir_rule_action participant_ack_final_rule))).
  {
    unfold EchoStep, echo_exec, EchoTransitionIR.echo_exec,
      interpret_echo_program.
    change
      ((if @EchoTransitionIR.eval_guards node node_eq config state
          (EchoParticipantReplyFinal message parent)
          (EchoTransitionIR.ir_rule_guards participant_ack_final_rule)
        then Some (@EchoTransitionIR.eval_action node node_eq config state
          (EchoParticipantReplyFinal message parent)
          (EchoTransitionIR.ir_rule_action participant_ack_final_rule))
        else None) =
       Some (@EchoTransitionIR.eval_action node node_eq config state
         (EchoParticipantReplyFinal message parent)
         (EchoTransitionIR.ir_rule_action participant_ack_final_rule))).
    now rewrite old_guards.
  }
  exists message.
  exists (@EchoTransitionIR.eval_action node node_eq config state
    (EchoParticipantReplyFinal message parent)
    (EchoTransitionIR.ir_rule_action participant_ack_final_rule)).
  split; [exact queued |].
  split; [exact message_identifier |].
  split; [exact old_step |].
  destruct (@echo_ir_participant_reply_final_action_forward
    node node_eq config state
    (@EchoTransitionIR.eval_action node node_eq config state
      (EchoParticipantReplyFinal message parent)
      (EchoTransitionIR.ir_rule_action participant_ack_final_rule))
    message parent old_step) as
    [simulated_successor [simulated_action correspondence]].
  unfold echo_ir_participant_reply_final_rule in action, simulated_action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action
    echo_ir_set_parent echo_ir_set_pending echo_ir_set_finished
    echo_ir_emit_one echo_ir_receiver echo_ir_some echo_ir_expected_parent
    echo_ir_empty_nodes echo_ir_bool echo_ir_empty_payload
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_globals echo_ir_encode_message
    echo_ir_delivery_certificates echo_ir_event_forward_order
    echo_ir_event_expected_parent eval_ir_expr ir_set_local_field
    ir_remove_selected_message ir_emit_messages eval_ir_payload_exprs
    ir_event_message ir_message_id ir_message_sender ir_message_receiver
    echo_ir_signature echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type]
    in action, simulated_action.
  rewrite certificate_parent in action.
  rewrite action in simulated_action. inversion simulated_action. subst.
  exact correspondence.
Qed.

(** A successful initiator reply with remaining work reconstructs the old
    event entirely from the selected queued message and encoded state; no
    Echo-specific delivery certificate is consumed by this branch. *)
Theorem echo_ir_initiator_reply_more_backward_simulates
    (state : @executable_echo_state node)
    (selected_id : nat)
    (certificates : ir_delivery_certificates node echo_ir_signature)
    (ir_successor : ir_protocol_state node echo_ir_signature) :
  interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state)
      (IRProtocolDeliver selected_id certificates) =
    @IRStepSuccess node echo_ir_signature
      EchoIRInitiatorReplyMoreRule ir_successor ->
  exists message successor,
    In message (message_store state) /\
    selected_id = message_id message /\
    @EchoStep node node_eq config state
      (EchoInitiatorReplyMore message) successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intro interpreted.
  destruct (echo_ir_delivery_success_components_for_rule
    state selected_id certificates
    EchoIRInitiatorReplyMoreRule
    (@echo_ir_initiator_reply_more_rule node)
    ir_successor ltac:(
      cbn [echo_ir_rules];
      now right; right; right; right; right; right; right; left)
    eq_refl interpreted) as
    [message [queued [message_identifier [enabled action]]]].
  pose proof (eval_ir_rule_enabled_pattern node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_initiator_reply_more_rule node) enabled) as reply_pattern.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_initiator_reply_more_rule node)
    (@echo_ir_equal node IRNode (@echo_ir_receiver node)
      (@echo_ir_initiator node)) enabled ltac:(
        cbn [echo_ir_initiator_reply_more_rule]; now left))
    as receiver_is_initiator.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_initiator_reply_more_rule node) (@echo_ir_started node)
    enabled ltac:(
      cbn [echo_ir_initiator_reply_more_rule]; now right; left))
    as protocol_started.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_initiator_reply_more_rule node)
    (@echo_ir_equal node IROptionNode
      (@echo_ir_parent node (@echo_ir_initiator node))
      (@echo_ir_option_none node)) enabled ltac:(
        cbn [echo_ir_initiator_reply_more_rule];
        now right; right; left)) as initiator_parent_none.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_initiator_reply_more_rule node)
    (IRListContainsExpr (@echo_ir_sender node)
      (@echo_ir_pending node (@echo_ir_initiator node))) enabled ltac:(
        cbn [echo_ir_initiator_reply_more_rule];
        now right; right; right; left)) as sender_pending.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_initiator_reply_more_rule node)
    (@echo_ir_nonempty node
      (@echo_ir_removed_pending node (@echo_ir_initiator node))) enabled ltac:(
        cbn [echo_ir_initiator_reply_more_rule];
        now right; right; right; right; left)) as pending_remains.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_initiator_reply_more_rule node)
    (@echo_ir_equal node IRBool
      (@echo_ir_finished node (@echo_ir_initiator node))
      (@echo_ir_bool node false)) enabled ltac:(
        cbn [echo_ir_initiator_reply_more_rule];
        now right; right; right; right; right; left))
    as initiator_not_finished.
  cbn [echo_ir_initiator_reply_more_rule ir_rule_pattern
    ir_event_pattern_matches echo_ir_encode_message echo_ir_encode_kind
    ir_message_kind] in reply_pattern.
  cbn [eval_ir_expr echo_ir_equal echo_ir_receiver echo_ir_initiator
    echo_ir_started echo_ir_parent echo_ir_option_none echo_ir_sender
    echo_ir_pending echo_ir_nonempty echo_ir_is_empty
    echo_ir_removed_pending echo_ir_remove echo_ir_finished echo_ir_bool
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_globals echo_ir_encode_message
    ir_processes ir_global_fields ir_config_fields ir_message_sender
    ir_message_receiver ir_event_message ir_value_eqb echo_ir_signature
    echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type]
    in receiver_is_initiator, protocol_started, initiator_parent_none,
      sender_pending, pending_remains, initiator_not_finished.
  assert (reply_kind : message_kind message = EchoReply).
  {
    destruct (message_kind message) eqn:kind; [| reflexivity].
    cbn [echo_ir_encode_kind] in reply_pattern.
    destruct (signature_message_kind_eq_dec echo_ir_signature
      EchoIRReply EchoIRRequest); discriminate.
  }
  inversion receiver_is_initiator as [receiver_is_initiator_bool].
  assert (receiver_equal :
    message_receiver message = config_initiator config).
  {
    unfold ir_node_eqb in receiver_is_initiator_bool.
    destruct (node_eq (message_receiver message) (config_initiator config))
      as [same | different].
    - exact same.
    - discriminate.
  }
  inversion protocol_started as [protocol_started_bool].
  inversion initiator_parent_none as [initiator_parent_none_bool].
  assert (initiator_parent_none_prop :
    process_parent (processes state (config_initiator config)) = None).
  {
    unfold ir_option_node_eqb in initiator_parent_none_bool.
    destruct (process_parent (processes state (config_initiator config)))
      as [parent |] eqn:parent_state; [discriminate | reflexivity].
  }
  inversion sender_pending as [sender_pending_bool].
  pose proof (echo_ir_node_in_true_implies_in
    (message_sender message)
    (process_pending (processes state (config_initiator config)))
    sender_pending_bool) as sender_pending_prop.
  inversion pending_remains as [pending_remains_bool].
  apply Bool.negb_true_iff in pending_remains_bool.
  assert (pending_remains_prop :
    remove_echo_node node_eq (message_sender message)
      (process_pending (processes state (config_initiator config))) <> []).
  {
    rewrite <- echo_ir_remove_node_agrees.
    destruct (ir_remove_node node_eq (message_sender message)
      (process_pending (processes state (config_initiator config))));
      [discriminate | congruence].
  }
  inversion initiator_not_finished as [initiator_not_finished_bool].
  assert (initiator_not_finished_prop :
    process_finished (processes state (config_initiator config)) = false).
  {
    destruct (process_finished (processes state (config_initiator config)))
      eqn:finished; [discriminate | reflexivity].
  }
  assert (old_guards :
    @EchoTransitionIR.eval_guards node node_eq config state
      (EchoInitiatorReplyMore message)
      (EchoTransitionIR.ir_rule_guards initiator_ack_more_rule) = true).
  {
    apply (proj2 (@eval_guards_true_iff node node_eq config state
      (EchoInitiatorReplyMore message)
      (EchoTransitionIR.ir_rule_guards initiator_ack_more_rule))).
    unfold initiator_ack_more_rule. repeat constructor.
    - cbn [guard_holds event_message]. exact reply_kind.
    - cbn [guard_holds eval_node_expr event_message]. exact receiver_equal.
    - cbn [guard_holds]. exact protocol_started_bool.
    - cbn [guard_holds eval_node_expr eval_parent_expr].
      exact initiator_parent_none_prop.
    - cbn [guard_holds event_message]. exact queued.
    - cbn [guard_holds eval_node_expr eval_nodes_expr event_message].
      exact sender_pending_prop.
    - cbn [guard_holds eval_node_expr eval_nodes_expr event_message].
      exact pending_remains_prop.
    - cbn [guard_holds eval_node_expr]. exact initiator_not_finished_prop.
  }
  assert (old_step :
    @EchoStep node node_eq config state
      (EchoInitiatorReplyMore message)
      (@EchoTransitionIR.eval_action node node_eq config state
        (EchoInitiatorReplyMore message)
        (EchoTransitionIR.ir_rule_action initiator_ack_more_rule))).
  {
    unfold EchoStep, echo_exec, EchoTransitionIR.echo_exec,
      interpret_echo_program.
    change
      ((if @EchoTransitionIR.eval_guards node node_eq config state
          (EchoInitiatorReplyMore message)
          (EchoTransitionIR.ir_rule_guards initiator_ack_more_rule)
        then Some (@EchoTransitionIR.eval_action node node_eq config state
          (EchoInitiatorReplyMore message)
          (EchoTransitionIR.ir_rule_action initiator_ack_more_rule))
        else None) =
       Some (@EchoTransitionIR.eval_action node node_eq config state
         (EchoInitiatorReplyMore message)
         (EchoTransitionIR.ir_rule_action initiator_ack_more_rule))).
    now rewrite old_guards.
  }
  exists message.
  exists (@EchoTransitionIR.eval_action node node_eq config state
    (EchoInitiatorReplyMore message)
    (EchoTransitionIR.ir_rule_action initiator_ack_more_rule)).
  split; [exact queued |].
  split; [exact message_identifier |].
  split; [exact old_step |].
  destruct (@echo_ir_initiator_reply_more_action_forward
    node node_eq config state
    (@EchoTransitionIR.eval_action node node_eq config state
      (EchoInitiatorReplyMore message)
      (EchoTransitionIR.ir_rule_action initiator_ack_more_rule))
    message old_step) as
    [simulated_successor [simulated_action correspondence]].
  unfold echo_ir_initiator_reply_more_rule in action, simulated_action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action
    echo_ir_set_parent echo_ir_set_pending echo_ir_set_finished
    echo_ir_initiator echo_ir_sender echo_ir_option_none echo_ir_pending
    echo_ir_removed_pending echo_ir_remove echo_ir_bool
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_globals echo_ir_encode_message
    echo_ir_delivery_certificates echo_ir_event_forward_order
    echo_ir_event_expected_parent eval_ir_expr ir_set_local_field
    ir_remove_selected_message ir_event_message ir_message_id
    ir_message_sender ir_message_receiver echo_ir_signature
    echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type]
    in action, simulated_action.
  rewrite action in simulated_action. inversion simulated_action. subst.
  exact correspondence.
Qed.

(** The last reply to the initiator reconstructs the old completion event:
    removing its sender empties the pending list and marks the initiator
    finished. *)
Theorem echo_ir_initiator_reply_final_backward_simulates
    (state : @executable_echo_state node)
    (selected_id : nat)
    (certificates : ir_delivery_certificates node echo_ir_signature)
    (ir_successor : ir_protocol_state node echo_ir_signature) :
  interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state)
      (IRProtocolDeliver selected_id certificates) =
    @IRStepSuccess node echo_ir_signature
      EchoIRInitiatorReplyFinalRule ir_successor ->
  exists message successor,
    In message (message_store state) /\
    selected_id = message_id message /\
    @EchoStep node node_eq config state
      (EchoInitiatorReplyFinal message) successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intro interpreted.
  destruct (echo_ir_delivery_success_components_for_rule
    state selected_id certificates
    EchoIRInitiatorReplyFinalRule
    (@echo_ir_initiator_reply_final_rule node)
    ir_successor ltac:(
      cbn [echo_ir_rules];
      now right; right; right; right; right; right; right; right; left)
    eq_refl interpreted) as
    [message [queued [message_identifier [enabled action]]]].
  pose proof (eval_ir_rule_enabled_pattern node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_initiator_reply_final_rule node) enabled) as reply_pattern.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_initiator_reply_final_rule node)
    (@echo_ir_equal node IRNode (@echo_ir_receiver node)
      (@echo_ir_initiator node)) enabled ltac:(
        cbn [echo_ir_initiator_reply_final_rule]; now left))
    as receiver_is_initiator.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_initiator_reply_final_rule node) (@echo_ir_started node)
    enabled ltac:(
      cbn [echo_ir_initiator_reply_final_rule]; now right; left))
    as protocol_started.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_initiator_reply_final_rule node)
    (@echo_ir_equal node IROptionNode
      (@echo_ir_parent node (@echo_ir_initiator node))
      (@echo_ir_option_none node)) enabled ltac:(
        cbn [echo_ir_initiator_reply_final_rule];
        now right; right; left)) as initiator_parent_none.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_initiator_reply_final_rule node)
    (IRListContainsExpr (@echo_ir_sender node)
      (@echo_ir_pending node (@echo_ir_initiator node))) enabled ltac:(
        cbn [echo_ir_initiator_reply_final_rule];
        now right; right; right; left)) as sender_pending.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_initiator_reply_final_rule node)
    (@echo_ir_is_empty node
      (@echo_ir_removed_pending node (@echo_ir_initiator node))) enabled ltac:(
        cbn [echo_ir_initiator_reply_final_rule];
        now right; right; right; right; left)) as pending_empty.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    (@echo_ir_initiator_reply_final_rule node)
    (@echo_ir_equal node IRBool
      (@echo_ir_finished node (@echo_ir_initiator node))
      (@echo_ir_bool node false)) enabled ltac:(
        cbn [echo_ir_initiator_reply_final_rule];
        now right; right; right; right; right; left))
    as initiator_not_finished.
  cbn [echo_ir_initiator_reply_final_rule ir_rule_pattern
    ir_event_pattern_matches echo_ir_encode_message echo_ir_encode_kind
    ir_message_kind] in reply_pattern.
  cbn [eval_ir_expr echo_ir_equal echo_ir_receiver echo_ir_initiator
    echo_ir_started echo_ir_parent echo_ir_option_none echo_ir_sender
    echo_ir_pending echo_ir_is_empty echo_ir_removed_pending echo_ir_remove
    echo_ir_finished echo_ir_bool echo_ir_encode_config
    echo_ir_encode_config_fields echo_ir_encode_state echo_ir_encode_process
    echo_ir_encode_globals echo_ir_encode_message ir_processes
    ir_global_fields ir_config_fields ir_message_sender ir_message_receiver
    ir_event_message ir_value_eqb echo_ir_signature echo_ir_local_field_type
    echo_ir_global_field_type echo_ir_config_field_type]
    in receiver_is_initiator, protocol_started, initiator_parent_none,
      sender_pending, pending_empty, initiator_not_finished.
  assert (reply_kind : message_kind message = EchoReply).
  {
    destruct (message_kind message) eqn:kind; [| reflexivity].
    cbn [echo_ir_encode_kind] in reply_pattern.
    destruct (signature_message_kind_eq_dec echo_ir_signature
      EchoIRReply EchoIRRequest); discriminate.
  }
  inversion receiver_is_initiator as [receiver_is_initiator_bool].
  assert (receiver_equal :
    message_receiver message = config_initiator config).
  {
    unfold ir_node_eqb in receiver_is_initiator_bool.
    destruct (node_eq (message_receiver message) (config_initiator config))
      as [same | different].
    - exact same.
    - discriminate.
  }
  inversion protocol_started as [protocol_started_bool].
  inversion initiator_parent_none as [initiator_parent_none_bool].
  assert (initiator_parent_none_prop :
    process_parent (processes state (config_initiator config)) = None).
  {
    unfold ir_option_node_eqb in initiator_parent_none_bool.
    destruct (process_parent (processes state (config_initiator config)))
      as [parent |] eqn:parent_state; [discriminate | reflexivity].
  }
  inversion sender_pending as [sender_pending_bool].
  pose proof (echo_ir_node_in_true_implies_in
    (message_sender message)
    (process_pending (processes state (config_initiator config)))
    sender_pending_bool) as sender_pending_prop.
  inversion pending_empty as [pending_empty_bool].
  assert (pending_empty_prop :
    remove_echo_node node_eq (message_sender message)
      (process_pending (processes state (config_initiator config))) = []).
  {
    rewrite <- echo_ir_remove_node_agrees.
    destruct (ir_remove_node node_eq (message_sender message)
      (process_pending (processes state (config_initiator config))));
      [reflexivity | discriminate].
  }
  inversion initiator_not_finished as [initiator_not_finished_bool].
  assert (initiator_not_finished_prop :
    process_finished (processes state (config_initiator config)) = false).
  {
    destruct (process_finished (processes state (config_initiator config)))
      eqn:finished; [discriminate | reflexivity].
  }
  assert (old_guards :
    @EchoTransitionIR.eval_guards node node_eq config state
      (EchoInitiatorReplyFinal message)
      (EchoTransitionIR.ir_rule_guards initiator_ack_final_rule) = true).
  {
    apply (proj2 (@eval_guards_true_iff node node_eq config state
      (EchoInitiatorReplyFinal message)
      (EchoTransitionIR.ir_rule_guards initiator_ack_final_rule))).
    unfold initiator_ack_final_rule. repeat constructor.
    - cbn [guard_holds event_message]. exact reply_kind.
    - cbn [guard_holds eval_node_expr event_message]. exact receiver_equal.
    - cbn [guard_holds]. exact protocol_started_bool.
    - cbn [guard_holds eval_node_expr eval_parent_expr].
      exact initiator_parent_none_prop.
    - cbn [guard_holds event_message]. exact queued.
    - cbn [guard_holds eval_node_expr eval_nodes_expr event_message].
      exact sender_pending_prop.
    - cbn [guard_holds eval_node_expr eval_nodes_expr event_message].
      exact pending_empty_prop.
    - cbn [guard_holds eval_node_expr]. exact initiator_not_finished_prop.
  }
  assert (old_step :
    @EchoStep node node_eq config state
      (EchoInitiatorReplyFinal message)
      (@EchoTransitionIR.eval_action node node_eq config state
        (EchoInitiatorReplyFinal message)
        (EchoTransitionIR.ir_rule_action initiator_ack_final_rule))).
  {
    unfold EchoStep, echo_exec, EchoTransitionIR.echo_exec,
      interpret_echo_program.
    change
      ((if @EchoTransitionIR.eval_guards node node_eq config state
          (EchoInitiatorReplyFinal message)
          (EchoTransitionIR.ir_rule_guards initiator_ack_final_rule)
        then Some (@EchoTransitionIR.eval_action node node_eq config state
          (EchoInitiatorReplyFinal message)
          (EchoTransitionIR.ir_rule_action initiator_ack_final_rule))
        else None) =
       Some (@EchoTransitionIR.eval_action node node_eq config state
         (EchoInitiatorReplyFinal message)
         (EchoTransitionIR.ir_rule_action initiator_ack_final_rule))).
    now rewrite old_guards.
  }
  exists message.
  exists (@EchoTransitionIR.eval_action node node_eq config state
    (EchoInitiatorReplyFinal message)
    (EchoTransitionIR.ir_rule_action initiator_ack_final_rule)).
  split; [exact queued |].
  split; [exact message_identifier |].
  split; [exact old_step |].
  destruct (@echo_ir_initiator_reply_final_action_forward
    node node_eq config state
    (@EchoTransitionIR.eval_action node node_eq config state
      (EchoInitiatorReplyFinal message)
      (EchoTransitionIR.ir_rule_action initiator_ack_final_rule))
    message old_step) as
    [simulated_successor [simulated_action correspondence]].
  unfold echo_ir_initiator_reply_final_rule in action, simulated_action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action
    echo_ir_set_parent echo_ir_set_pending echo_ir_set_finished
    echo_ir_initiator echo_ir_option_none echo_ir_empty_nodes echo_ir_bool
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_globals echo_ir_encode_message
    echo_ir_delivery_certificates echo_ir_event_forward_order
    echo_ir_event_expected_parent eval_ir_expr ir_set_local_field
    ir_remove_selected_message ir_event_message ir_message_id
    ir_message_sender ir_message_receiver echo_ir_signature
    echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type]
    in action, simulated_action.
  rewrite action in simulated_action. inversion simulated_action. subst.
  exact correspondence.
Qed.

(** Typed startup-certificate projection used to reconstruct the old startup
    witness without assuming equality of dependent certificate functions. *)
Definition echo_ir_start_order_value
    (certificates : ir_start_certificates node echo_ir_signature) :
    list node :=
  ir_list_node_value_contents (certificates EchoIRStartOrder).

(** General startup reverse simulation.  Unlike the earlier compatibility
    theorem, this accepts the scheduler's arbitrary typed certificate map and
    reconstructs the checked order from its sole startup field. *)
Theorem echo_ir_start_certificates_backward_simulate
    (state : @executable_echo_state node)
    (certificates : ir_start_certificates node echo_ir_signature)
    (ir_successor : ir_protocol_state node echo_ir_signature) :
  interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state)
      (IRProtocolStart certificates) =
    @IRStepSuccess node echo_ir_signature EchoIRStartRule ir_successor ->
  exists successor,
    @EchoStep node node_eq config state
      (EchoStart (echo_ir_start_order_value certificates)) successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intro interpreted.
  set (ordered_neighbors := echo_ir_start_order_value certificates).
  assert (certificate_order :
    certificates EchoIRStartOrder = IRListNodeValue ordered_neighbors).
  {
    subst ordered_neighbors. apply ir_list_node_value_eta.
  }
  destruct (interpret_protocol_rules_success_components
    node_eq (echo_ir_encode_config config) (@echo_ir_rules node)
    (echo_ir_encode_state state) (IRProtocolStart certificates)
    EchoIRStartRule ir_successor interpreted) as
    [runtime_event [selected_rule
      [resolved [selected [selected_rule_id action]]]]].
  cbn [ir_resolve_event] in resolved.
  inversion resolved. subst runtime_event.
  pose proof (select_ir_rule_unique_in node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeStart certificates) (@echo_ir_rules node)
    selected_rule selected) as selected_in.
  assert (expected_in :
    In (@echo_ir_start_rule node) (@echo_ir_rules node)).
  {
    cbn [echo_ir_rules]. now left.
  }
  assert (selected_rule = @echo_ir_start_rule node) as selected_is_start.
  {
    eapply echo_ir_rule_identifier_injective.
    - exact selected_in.
    - exact expected_in.
    - cbn [echo_ir_start_rule ir_rule_id]. exact selected_rule_id.
  }
  subst selected_rule.
  pose proof (select_ir_rule_unique_is_enabled node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeStart certificates) (@echo_ir_rules node)
    (@echo_ir_start_rule node) selected) as enabled.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeStart certificates) (@echo_ir_start_rule node)
    (IRNotExpr (@echo_ir_started node)) enabled ltac:(
      cbn [echo_ir_start_rule]; now left)) as not_started.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeStart certificates) (@echo_ir_start_rule node)
    (@IRAllNodesLocalEqualExpr node echo_ir_signature
      EchoIRParent (@echo_ir_option_none node)) enabled ltac:(
        cbn [echo_ir_start_rule]; now right; left)) as parents_initial.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeStart certificates) (@echo_ir_start_rule node)
    (@IRAllNodesLocalEqualExpr node echo_ir_signature
      EchoIRPending (@echo_ir_empty_nodes node)) enabled ltac:(
        cbn [echo_ir_start_rule]; now right; right; left))
    as pending_initial.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeStart certificates) (@echo_ir_start_rule node)
    (@IRAllNodesLocalEqualExpr node echo_ir_signature
      EchoIRFinished (@echo_ir_bool node false)) enabled ltac:(
        cbn [echo_ir_start_rule]; now right; right; right; left))
    as finished_initial.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeStart certificates) (@echo_ir_start_rule node)
    (@IRMessageStoreEmptyExpr node echo_ir_signature) enabled ltac:(
      cbn [echo_ir_start_rule];
      now right; right; right; right; left)) as messages_empty.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeStart certificates) (@echo_ir_start_rule node)
    (@IREqualExpr node echo_ir_signature IRNat
      (@IRNextMessageIdExpr node echo_ir_signature) (@echo_ir_nat node 1))
    enabled ltac:(
      cbn [echo_ir_start_rule];
      now right; right; right; right; right; left)) as next_id_one.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeStart certificates) (@echo_ir_start_rule node)
    (IRListPermutationExpr (@echo_ir_start_order node)
      (@echo_ir_neighbors node (@echo_ir_initiator node))) enabled ltac:(
        cbn [echo_ir_start_rule];
        repeat (first [left; reflexivity | right]))) as order_valid.
  cbn [eval_ir_expr echo_ir_started echo_ir_encode_config
    echo_ir_encode_config_fields echo_ir_encode_state echo_ir_encode_process
    echo_ir_encode_globals ir_global_fields ir_processes ir_message_store
    ir_next_message_id ir_config_nodes echo_ir_option_none echo_ir_empty_nodes
    echo_ir_bool echo_ir_nat echo_ir_start_order echo_ir_neighbors
    echo_ir_initiator ir_config_fields ir_config_neighbors ir_value_eqb
    echo_ir_signature echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_start_certificate_field_type]
    in not_started, parents_initial, pending_initial, finished_initial,
      messages_empty, next_id_one, order_valid.
  rewrite certificate_order in order_valid.
  cbn in order_valid.
  inversion not_started as [not_started_bool].
  apply Bool.negb_true_iff in not_started_bool.
  inversion parents_initial as [parents_initial_bool].
  inversion pending_initial as [pending_initial_bool].
  inversion finished_initial as [finished_initial_bool].
  inversion messages_empty as [messages_empty_bool].
  inversion next_id_one as [next_id_one_bool].
  inversion order_valid as [order_valid_bool].
  rewrite forallb_forall in parents_initial_bool.
  rewrite forallb_forall in pending_initial_bool.
  rewrite forallb_forall in finished_initial_bool.
  assert (configured_initial :
    configured_processes_initial config state).
  {
    intros process configured.
    specialize (parents_initial_bool process configured).
    specialize (pending_initial_bool process configured).
    specialize (finished_initial_bool process configured).
    destruct (processes state process) as [parent pending finished]
      eqn:process_state.
    cbn [process_parent] in parents_initial_bool.
    unfold ir_option_node_eqb in parents_initial_bool.
    destruct parent; try discriminate.
    cbn [process_pending] in pending_initial_bool.
    destruct pending; try discriminate.
    cbn [process_finished] in finished_initial_bool.
    cbn [initial_echo_process].
    destruct finished; try discriminate. reflexivity.
  }
  assert (store_empty : message_store state = []).
  {
    destruct (message_store state); [reflexivity | discriminate].
  }
  apply Nat.eqb_eq in next_id_one_bool.
  apply (proj1 (ir_node_list_permutationb_true_iff
    node_eq ordered_neighbors
    (nbrs (config_nodes config) (config_adjacent config)
      (config_initiator config)))) in order_valid_bool.
  assert (old_guards :
    @EchoTransitionIR.eval_guards node node_eq config state
      (EchoStart ordered_neighbors)
      (EchoTransitionIR.ir_rule_guards start_rule) = true).
  {
    apply (proj2 (@eval_guards_true_iff node node_eq config state
      (EchoStart ordered_neighbors)
      (EchoTransitionIR.ir_rule_guards start_rule))).
    unfold start_rule. constructor.
    - cbn [guard_holds]. repeat split; assumption.
    - constructor.
      + cbn [guard_holds eval_nodes_expr event_ordered_nodes
          eval_node_expr]. exact order_valid_bool.
      + constructor.
  }
  assert (old_step :
    @EchoStep node node_eq config state (EchoStart ordered_neighbors)
      (@EchoTransitionIR.eval_action node node_eq config state
        (EchoStart ordered_neighbors)
        (EchoTransitionIR.ir_rule_action start_rule))).
  {
    unfold EchoStep, echo_exec, EchoTransitionIR.echo_exec,
      interpret_echo_program.
    change
      ((if @EchoTransitionIR.eval_guards node node_eq config state
          (EchoStart ordered_neighbors)
          (EchoTransitionIR.ir_rule_guards start_rule)
        then Some (@EchoTransitionIR.eval_action node node_eq config state
          (EchoStart ordered_neighbors)
          (EchoTransitionIR.ir_rule_action start_rule))
        else None) =
       Some (@EchoTransitionIR.eval_action node node_eq config state
         (EchoStart ordered_neighbors)
         (EchoTransitionIR.ir_rule_action start_rule))).
    now rewrite old_guards.
  }
  exists (@EchoTransitionIR.eval_action node node_eq config state
    (EchoStart ordered_neighbors)
    (EchoTransitionIR.ir_rule_action start_rule)).
  split; [exact old_step |].
  destruct (@echo_ir_start_action_forward node node_eq config state
    (@EchoTransitionIR.eval_action node node_eq config state
      (EchoStart ordered_neighbors)
      (EchoTransitionIR.ir_rule_action start_rule))
    ordered_neighbors old_step) as
    [simulated_successor [simulated_action correspondence]].
  unfold echo_ir_start_rule in action, simulated_action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action
    echo_ir_set_parent echo_ir_set_pending echo_ir_set_finished
    echo_ir_emit_many echo_ir_initiator echo_ir_option_none
    echo_ir_start_order echo_ir_bool echo_ir_empty_payload
    echo_ir_encode_config
    echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_globals
    echo_ir_start_certificates eval_ir_expr ir_set_local_field
    ir_set_global_field ir_emit_messages eval_ir_payload_exprs
    echo_ir_signature echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_start_certificate_field_type]
    in action, simulated_action.
  rewrite certificate_order in action.
  rewrite action in simulated_action. inversion simulated_action. subst.
  exact correspondence.
Qed.

(** Observable agreement between a scheduler delivery and the reconstructed
    old Echo event.  Only certificates actually consumed by that branch are
    constrained; unused certificate fields are deliberately irrelevant. *)
Definition echo_ir_delivery_event_corresponds
    (selected_id : nat)
    (certificates : ir_delivery_certificates node echo_ir_signature)
    (event : @echo_event node) : Prop :=
  match event with
  | EchoStart _ => False
  | EchoFirstRequestNonLeaf message ordered_forwards =>
      selected_id = message_id message /\
      certificates EchoIRForwardOrder =
        IRListNodeValue ordered_forwards
  | EchoFirstRequestLeaf message
  | EchoRepeatedRequest message
  | EchoInitiatorRequest message
  | EchoInitiatorReplyMore message
  | EchoInitiatorReplyFinal message =>
      selected_id = message_id message
  | EchoParticipantReplyMore message parent
  | EchoParticipantReplyFinal message parent =>
      selected_id = message_id message /\
      certificates EchoIRExpectedParent = IRNodeValue parent
  end.

(** Every successful generic delivery is explained by one genuine old Echo
    event.  This is the branch-independent reverse theorem: the reported rule
    ID determines which of the eight constructive branch proofs supplies the
    event and old successor. *)
Theorem echo_ir_delivery_backward_simulates
    (state : @executable_echo_state node)
    (selected_id : nat)
    (certificates : ir_delivery_certificates node echo_ir_signature)
    (reported_id : echo_ir_rule_id)
    (ir_successor : ir_protocol_state node echo_ir_signature) :
  interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state)
      (IRProtocolDeliver selected_id certificates) =
    @IRStepSuccess node echo_ir_signature reported_id ir_successor ->
  exists event successor,
    echo_ir_rule_id_for_event event = reported_id /\
    echo_ir_delivery_event_corresponds selected_id certificates event /\
    @EchoStep node node_eq config state event successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intro interpreted.
  destruct reported_id.
  - destruct (echo_ir_delivery_success_components_for_rule
      state selected_id certificates EchoIRStartRule
      (@echo_ir_start_rule node) ir_successor
      ltac:(cbn [echo_ir_rules]; now left) eq_refl interpreted) as
      [message [queued [message_identifier [enabled action]]]].
    unfold eval_ir_rule, echo_ir_start_rule in enabled.
    discriminate.
  - destruct (echo_ir_first_request_nonleaf_backward_simulates
      state selected_id certificates ir_successor interpreted) as
      [message [successor
        [queued [message_identifier [step correspondence]]]]].
    exists (EchoFirstRequestNonLeaf message
      (@echo_ir_delivery_forward_order_value node certificates)), successor.
    split; [reflexivity |].
    split.
    + split; [exact message_identifier |].
      apply ir_list_node_value_eta.
    + split; assumption.
  - destruct (echo_ir_first_request_leaf_backward_simulates
      state selected_id certificates ir_successor interpreted) as
      [message [successor
        [queued [message_identifier [step correspondence]]]]].
    exists (EchoFirstRequestLeaf message), successor.
    split; [reflexivity |].
    split; [exact message_identifier |].
    split; assumption.
  - destruct (echo_ir_repeated_request_backward_simulates
      state selected_id certificates ir_successor interpreted) as
      [message [successor
        [queued [message_identifier [step correspondence]]]]].
    exists (EchoRepeatedRequest message), successor.
    split; [reflexivity |].
    split; [exact message_identifier |].
    split; assumption.
  - destruct (echo_ir_initiator_request_backward_simulates
      state selected_id certificates ir_successor interpreted) as
      [message [successor
        [queued [message_identifier [step correspondence]]]]].
    exists (EchoInitiatorRequest message), successor.
    split; [reflexivity |].
    split; [exact message_identifier |].
    split; assumption.
  - destruct (echo_ir_participant_reply_more_backward_simulates
      state selected_id certificates ir_successor interpreted) as
      [message [successor
        [queued [message_identifier [step correspondence]]]]].
    exists (EchoParticipantReplyMore message
      (@echo_ir_delivery_expected_parent_value node certificates)), successor.
    split; [reflexivity |].
    split.
    + split; [exact message_identifier |].
      apply ir_node_value_eta.
    + split; assumption.
  - destruct (echo_ir_participant_reply_final_backward_simulates
      state selected_id certificates ir_successor interpreted) as
      [message [successor
        [queued [message_identifier [step correspondence]]]]].
    exists (EchoParticipantReplyFinal message
      (@echo_ir_delivery_expected_parent_value node certificates)), successor.
    split; [reflexivity |].
    split.
    + split; [exact message_identifier |].
      apply ir_node_value_eta.
    + split; assumption.
  - destruct (echo_ir_initiator_reply_more_backward_simulates
      state selected_id certificates ir_successor interpreted) as
      [message [successor
        [queued [message_identifier [step correspondence]]]]].
    exists (EchoInitiatorReplyMore message), successor.
    split; [reflexivity |].
    split; [exact message_identifier |].
    split; assumption.
  - destruct (echo_ir_initiator_reply_final_backward_simulates
      state selected_id certificates ir_successor interpreted) as
      [message [successor
        [queued [message_identifier [step correspondence]]]]].
    exists (EchoInitiatorReplyFinal message), successor.
    split; [reflexivity |].
    split; [exact message_identifier |].
    split; assumption.
Qed.

(** A successful startup cannot report a delivery-rule identifier because
    all delivery patterns mismatch [IRRuntimeStart]. *)
Lemma echo_ir_start_success_rule_is_start
    (state : @executable_echo_state node)
    (certificates : ir_start_certificates node echo_ir_signature)
    (reported_id : echo_ir_rule_id)
    (ir_successor : ir_protocol_state node echo_ir_signature) :
  interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state)
      (IRProtocolStart certificates) =
    @IRStepSuccess node echo_ir_signature reported_id ir_successor ->
  reported_id = EchoIRStartRule.
Proof.
  intro interpreted.
  destruct (interpret_protocol_rules_success_components
    node_eq (echo_ir_encode_config config) (@echo_ir_rules node)
    (echo_ir_encode_state state) (IRProtocolStart certificates)
    reported_id ir_successor interpreted) as
    [runtime_event [selected_rule
      [resolved [selected [selected_identifier action]]]]].
  cbn [ir_resolve_event] in resolved.
  inversion resolved. subst runtime_event.
  pose proof (select_ir_rule_unique_in node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeStart certificates) (@echo_ir_rules node)
    selected_rule selected) as selected_in.
  pose proof (select_ir_rule_unique_is_enabled node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeStart certificates) (@echo_ir_rules node)
    selected_rule selected) as enabled.
  cbn [echo_ir_rules] in selected_in.
  repeat destruct selected_in as [same | selected_in];
    try contradiction; subst selected_rule.
  - cbn [echo_ir_start_rule ir_rule_id] in selected_identifier.
    symmetry. exact selected_identifier.
  - unfold eval_ir_rule, echo_ir_first_request_nonleaf_rule in enabled.
    discriminate.
  - unfold eval_ir_rule, echo_ir_first_request_leaf_rule in enabled.
    discriminate.
  - unfold eval_ir_rule, echo_ir_repeated_request_rule in enabled.
    discriminate.
  - unfold eval_ir_rule, echo_ir_initiator_request_rule in enabled.
    discriminate.
  - unfold eval_ir_rule, echo_ir_participant_reply_more_rule in enabled.
    discriminate.
  - unfold eval_ir_rule, echo_ir_participant_reply_final_rule in enabled.
    discriminate.
  - unfold eval_ir_rule, echo_ir_initiator_reply_more_rule in enabled.
    discriminate.
  - unfold eval_ir_rule, echo_ir_initiator_reply_final_rule in enabled.
    discriminate.
Qed.

(** Event-level bridge used by the unified reverse theorem.  It records only
    the externally observable selection and the typed witnesses consumed by
    the selected branch. *)
Definition echo_ir_external_event_corresponds
    (ir_event : ir_external_event node echo_ir_signature)
    (event : @echo_event node) : Prop :=
  match ir_event, event with
  | IRProtocolStart certificates, EchoStart ordered_neighbors =>
      certificates EchoIRStartOrder =
        IRListNodeValue ordered_neighbors
  | IRProtocolDeliver selected_id certificates, _ =>
      echo_ir_delivery_event_corresponds
        selected_id certificates event
  | _, _ => False
  end.

(** Unified one-step reverse simulation from the protocol-neutral scheduler
    API to the old Echo executable transition. *)
Theorem echo_ir_success_backward_simulates
    (state : @executable_echo_state node)
    (ir_event : ir_external_event node echo_ir_signature)
    (reported_id : echo_ir_rule_id)
    (ir_successor : ir_protocol_state node echo_ir_signature) :
  interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state) ir_event =
    @IRStepSuccess node echo_ir_signature reported_id ir_successor ->
  exists event successor,
    echo_ir_rule_id_for_event event = reported_id /\
    echo_ir_external_event_corresponds ir_event event /\
    @EchoStep node node_eq config state event successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  destruct ir_event as [certificates | selected_id certificates];
    intro interpreted.
  - pose proof (echo_ir_start_success_rule_is_start
      state certificates reported_id ir_successor interpreted)
      as reported_is_start.
    subst reported_id.
    destruct (echo_ir_start_certificates_backward_simulate
      state certificates ir_successor interpreted) as
      [successor [step correspondence]].
    exists (EchoStart (echo_ir_start_order_value certificates)), successor.
    split; [reflexivity |].
    split.
    + apply ir_list_node_value_eta.
    + split; assumption.
  - destruct (echo_ir_delivery_backward_simulates
      state selected_id certificates reported_id ir_successor interpreted) as
      [event [successor
        [identifier [event_correspondence [step correspondence]]]]].
    exists event, successor.
    split; [exact identifier |].
    split; [exact event_correspondence |].
    split; assumption.
Qed.

(** Reverse simulation is stable under the same pointwise state relation used
    by the forward proof.  The generic interpreter step is transported to the
    exact encoding of the old state, reversed there, and its successor is
    transported back by transitivity. *)
Theorem echo_ir_success_backward_simulates_from_corresponding_state
    (state : @executable_echo_state node)
    (ir_state : ir_protocol_state node echo_ir_signature)
    (ir_event : ir_external_event node echo_ir_signature)
    (reported_id : echo_ir_rule_id)
    (ir_successor : ir_protocol_state node echo_ir_signature) :
  echo_ir_states_correspond state ir_state ->
  interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) ir_state ir_event =
    @IRStepSuccess node echo_ir_signature reported_id ir_successor ->
  exists event successor,
    echo_ir_rule_id_for_event event = reported_id /\
    echo_ir_external_event_corresponds ir_event event /\
    @EchoStep node node_eq config state event successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intros state_correspondence interpreted.
  assert (inputs_equivalent :
    ir_states_equivalent ir_state (echo_ir_encode_state state)).
  {
    now apply (proj1
      (@echo_ir_states_correspond_iff_equivalent
        node state ir_state)).
  }
  destruct (interpret_protocol_rules_respects_state_equivalence
    node_eq (echo_ir_encode_config config) (@echo_ir_rules node)
    ir_state (echo_ir_encode_state state) ir_successor ir_event
    reported_id inputs_equivalent interpreted) as
    [encoded_successor [encoded_step successors_equivalent]].
  destruct (echo_ir_success_backward_simulates
    state ir_event reported_id encoded_successor encoded_step) as
    [event [successor
      [identifier [event_correspondence [step encoded_correspondence]]]]].
  exists event, successor.
  split; [exact identifier |].
  split; [exact event_correspondence |].
  split; [exact step |].
  apply (proj2
    (@echo_ir_states_correspond_iff_equivalent
      node successor ir_successor)).
  eapply ir_states_equivalent_trans.
  - exact successors_equivalent.
  - exact ((proj1
      (@echo_ir_states_correspond_iff_equivalent
        node successor encoded_successor))
      encoded_correspondence).
Qed.

(** A generic path starting from any state corresponding to an old reachable
    state reconstructs a chained old reachable execution. *)
Theorem echo_ir_path_backward_simulates
    (ir_initial ir_final : ir_protocol_state node echo_ir_signature) :
  forall state : @executable_echo_state node,
    @echo_reachable node node_eq config state ->
    echo_ir_states_correspond state ir_initial ->
    ir_protocol_reachable node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) ir_initial ir_final ->
    exists final_state,
      @echo_reachable node node_eq config final_state /\
      echo_ir_states_correspond final_state ir_final.
Proof.
  intros state old_reachable state_correspondence path.
  revert state old_reachable state_correspondence.
  induction path as
    [ir_state
    |ir_state ir_event reported_id ir_successor ir_final
      interpreted tail IH].
  - intros state old_reachable state_correspondence.
    exists state. split; assumption.
  - intros state old_reachable state_correspondence.
    destruct (echo_ir_success_backward_simulates_from_corresponding_state
      state ir_state ir_event reported_id ir_successor
      state_correspondence interpreted) as
      [event [successor
        [identifier [event_correspondence
          [old_step successor_correspondence]]]]].
    apply (IH successor).
    + exact (@EchoReachStep node node_eq config state event successor
        old_reachable old_step).
    + exact successor_correspondence.
Qed.

(** Reachability equivalence, reverse direction: every state reachable by the
    generic Echo IR from its initializer corresponds to an old executable
    Echo state reachable by genuine [EchoStep] transitions. *)
Theorem echo_ir_reachable_backward_simulates
    (ir_state : ir_protocol_state node echo_ir_signature) :
  ir_protocol_reachable node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node)
      (initialize_ir_protocol (@echo_ir_program node)) ir_state ->
  exists state,
    @echo_reachable node node_eq config state /\
    echo_ir_states_correspond state ir_state.
Proof.
  intro reachable.
  eapply (echo_ir_path_backward_simulates
    (initialize_ir_protocol (@echo_ir_program node)) ir_state
    initial_executable_echo_state).
  - apply EchoReachInitial.
  - rewrite <- (@echo_ir_encode_initial_state node).
    apply echo_ir_encoded_state_corresponds.
  - exact reachable.
Qed.

End EchoIRBackwardSimulation.
