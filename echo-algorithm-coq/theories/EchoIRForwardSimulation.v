(** * Forward-simulation infrastructure for the generic Echo IR

    Executable Echo states and generic IR states both store processes as
    functions.  The migration theorem therefore uses a pointwise relation
    instead of assuming function extensionality merely to package the same
    observations as record equality. *)

From Stdlib Require Import List Bool Arith Sorting.Permutation.
Import ListNotations.
Require Import EchoAlgorithm EchoExecutableTypes EchoTransitionIR
  EchoExecutableReachability ProtocolIRTypes ProtocolIRExpressions ProtocolIRActions
  ProtocolIRInterpreter ProtocolIRRunner EchoIRSignature EchoIRProgram EchoIRCompatibility
  EchoIRRuleUniqueness.

Section EchoIRForwardSimulation.

Variable node : Type.
Variable node_eq : forall left right : node,
  {left = right} + {left <> right}.
Variable config : @echo_config node.

(** Every observable component of the generic state is the encoding of the
    corresponding executable Echo component. *)
Definition echo_ir_states_correspond
    (echo_state : @executable_echo_state node)
    (ir_state : ir_protocol_state node echo_ir_signature) : Prop :=
  (forall process field,
    ir_processes ir_state process field =
      @echo_ir_encode_process node (processes echo_state process) field) /\
  ir_message_store ir_state =
    List.map (@echo_ir_encode_message node) (message_store echo_state) /\
  (forall field,
    ir_global_fields ir_state field =
      @echo_ir_encode_globals node echo_state field) /\
  ir_next_message_id ir_state = next_message_id echo_state.

Lemma echo_ir_encoded_state_corresponds
    (state : @executable_echo_state node) :
  echo_ir_states_correspond state (echo_ir_encode_state state).
Proof.
  repeat split; reflexivity.
Qed.

(** One-step views of [select_ir_rule] keep proofs about a rule head from
    unfolding the entire remaining rule list. *)
Lemma select_ir_rule_cons_mismatch
    (signature : protocol_signature)
    (ir_config : ir_protocol_config node signature)
    (ir_state : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (rule : ir_rule node signature)
    (rest : list (ir_rule node signature)) :
  eval_ir_rule node_eq ir_config ir_state event rule = IRRuleMismatch ->
  select_ir_rule node_eq ir_config ir_state event (rule :: rest) =
    select_ir_rule node_eq ir_config ir_state event rest.
Proof.
  intro mismatch.
  change
    (match eval_ir_rule node_eq ir_config ir_state event rule with
     | IRRuleMismatch | IRRuleDisabled =>
         select_ir_rule node_eq ir_config ir_state event rest
     | IRRuleMalformed => IRMalformedRuleObserved
     | IRRuleEnabled =>
         match select_ir_rule node_eq ir_config ir_state event rest with
         | IRNoRuleSelected => IRUniqueRuleSelected rule
         | IRUniqueRuleSelected _ => IRAmbiguousRulesSelected
         | IRAmbiguousRulesSelected => IRAmbiguousRulesSelected
         | IRMalformedRuleObserved => IRMalformedRuleObserved
         end
     end = select_ir_rule node_eq ir_config ir_state event rest).
  now rewrite mismatch.
Qed.

Lemma select_ir_rule_cons_disabled
    (signature : protocol_signature)
    (ir_config : ir_protocol_config node signature)
    (ir_state : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (rule : ir_rule node signature)
    (rest : list (ir_rule node signature)) :
  eval_ir_rule node_eq ir_config ir_state event rule = IRRuleDisabled ->
  select_ir_rule node_eq ir_config ir_state event (rule :: rest) =
    select_ir_rule node_eq ir_config ir_state event rest.
Proof.
  intro disabled.
  change
    (match eval_ir_rule node_eq ir_config ir_state event rule with
     | IRRuleMismatch | IRRuleDisabled =>
         select_ir_rule node_eq ir_config ir_state event rest
     | IRRuleMalformed => IRMalformedRuleObserved
     | IRRuleEnabled =>
         match select_ir_rule node_eq ir_config ir_state event rest with
         | IRNoRuleSelected => IRUniqueRuleSelected rule
         | IRUniqueRuleSelected _ => IRAmbiguousRulesSelected
         | IRAmbiguousRulesSelected => IRAmbiguousRulesSelected
         | IRMalformedRuleObserved => IRMalformedRuleObserved
         end
     end = select_ir_rule node_eq ir_config ir_state event rest).
  now rewrite disabled.
Qed.

Lemma select_ir_rule_cons_unique
    (signature : protocol_signature)
    (ir_config : ir_protocol_config node signature)
    (ir_state : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (rule : ir_rule node signature)
    (rest : list (ir_rule node signature)) :
  eval_ir_rule node_eq ir_config ir_state event rule = IRRuleEnabled ->
  select_ir_rule node_eq ir_config ir_state event rest = IRNoRuleSelected ->
  select_ir_rule node_eq ir_config ir_state event (rule :: rest) =
    IRUniqueRuleSelected rule.
Proof.
  intros enabled rest_none.
  change
    (match eval_ir_rule node_eq ir_config ir_state event rule with
     | IRRuleMismatch | IRRuleDisabled =>
         select_ir_rule node_eq ir_config ir_state event rest
     | IRRuleMalformed => IRMalformedRuleObserved
     | IRRuleEnabled =>
         match select_ir_rule node_eq ir_config ir_state event rest with
         | IRNoRuleSelected => IRUniqueRuleSelected rule
         | IRUniqueRuleSelected _ => IRAmbiguousRulesSelected
         | IRAmbiguousRulesSelected => IRAmbiguousRulesSelected
         | IRMalformedRuleObserved => IRMalformedRuleObserved
         end
     end = IRUniqueRuleSelected rule).
  now rewrite enabled, rest_none.
Qed.

Lemma select_ir_rule_app_none
    (signature : protocol_signature)
    (ir_config : ir_protocol_config node signature)
    (ir_state : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (prefix suffix : list (ir_rule node signature)) :
  select_ir_rule node_eq ir_config ir_state event prefix = IRNoRuleSelected ->
  select_ir_rule node_eq ir_config ir_state event (prefix ++ suffix) =
    select_ir_rule node_eq ir_config ir_state event suffix.
Proof.
  revert suffix.
  induction prefix as [|rule rest IH]; intros suffix prefix_none.
  - reflexivity.
  - cbn [List.app select_ir_rule] in prefix_none |- *.
    destruct (eval_ir_rule node_eq ir_config ir_state event rule)
      eqn:status.
    + now apply IH.
    + now apply IH.
    + destruct (select_ir_rule node_eq ir_config ir_state event rest);
        discriminate.
    + discriminate.
Qed.

Lemma echo_update_process_same
    (roles : node -> @echo_process node)
    (target : node)
    (replacement : @echo_process node) :
  update_process node_eq roles target replacement target = replacement.
Proof.
  unfold update_process.
  destruct (node_eq target target) as [same | different].
  - reflexivity.
  - contradiction.
Qed.

Lemma echo_update_process_different
    (roles : node -> @echo_process node)
    (target candidate : node)
    (replacement : @echo_process node) :
  target <> candidate ->
  update_process node_eq roles target replacement candidate =
    roles candidate.
Proof.
  intro different. unfold update_process.
  destruct (node_eq target candidate) as [same | not_same].
  - contradiction.
  - reflexivity.
Qed.

(** The old event constructor records the branch that its old interpreter
    checks.  This function names the corresponding generic rule ID; it is not
    an input to generic rule selection. *)
Definition echo_ir_rule_id_for_event
    (event : @echo_event node) : echo_ir_rule_id :=
  match event with
  | EchoStart _ => EchoIRStartRule
  | EchoFirstRequestNonLeaf _ _ => EchoIRFirstRequestNonLeafRule
  | EchoFirstRequestLeaf _ => EchoIRFirstRequestLeafRule
  | EchoRepeatedRequest _ => EchoIRRepeatedRequestRule
  | EchoInitiatorRequest _ => EchoIRInitiatorRequestRule
  | EchoParticipantReplyMore _ _ => EchoIRParticipantReplyMoreRule
  | EchoParticipantReplyFinal _ _ => EchoIRParticipantReplyFinalRule
  | EchoInitiatorReplyMore _ => EchoIRInitiatorReplyMoreRule
  | EchoInitiatorReplyFinal _ => EchoIRInitiatorReplyFinalRule
  end.

(** Removing the first message with a selected ID commutes with encoding. *)
Lemma echo_ir_remove_message_encoding
    (selected_id : nat)
    (messages : list (@echo_message node)) :
  ir_remove_message selected_id
      (List.map (@echo_ir_encode_message node) messages) =
    List.map (@echo_ir_encode_message node)
      (remove_echo_message selected_id messages).
Proof.
  induction messages as [|message rest IH].
  - reflexivity.
  - cbn [List.map ir_remove_message remove_echo_message
      echo_ir_encode_message].
    assert (encoded_id :
      ir_message_id (@echo_ir_encode_message node message) =
        message_id message) by reflexivity.
    rewrite encoded_id.
    destruct (Nat.eqb selected_id (message_id message)).
    + reflexivity.
    + cbn [List.map]. f_equal. exact IH.
Qed.

(** Materializing same-kind outbound messages also commutes with encoding. *)
Lemma echo_ir_materialize_messages_encoding
    (next_id : nat)
    (kind : echo_kind)
    (sender : node)
    (receivers : list node) :
  @ir_materialize_messages node echo_ir_signature next_id
      (echo_ir_encode_kind kind) sender receivers [] =
    List.map (@echo_ir_encode_message node)
      (materialize_echo_outbound next_id sender
        (List.map (mkEchoOutbound kind) receivers)).
Proof.
  revert next_id.
  induction receivers as [|receiver rest IH]; intros next_id.
  - reflexivity.
  - cbn [List.map ir_materialize_messages materialize_echo_outbound
      echo_ir_encode_message].
    f_equal. apply IH.
Qed.

Lemma echo_ir_remove_node_agrees
    (selected : node)
    (items : list node) :
  ir_remove_node node_eq selected items =
    remove_echo_node node_eq selected items.
Proof.
  induction items as [|candidate rest IH].
  - reflexivity.
  - cbn [ir_remove_node remove_echo_node].
    destruct (node_eq selected candidate).
    + reflexivity.
    + f_equal. exact IH.
Qed.

Lemma echo_ir_node_in_true_of_in
    (selected : node)
    (items : list node) :
  In selected items -> ir_node_in node_eq selected items = true.
Proof.
  induction items as [|candidate rest IH]; intro member.
  - contradiction.
  - cbn [ir_node_in].
    destruct member as [same | in_rest].
    + subst candidate.
      destruct (node_eq selected selected); [reflexivity | contradiction].
    + destruct (node_eq selected candidate).
      * reflexivity.
      * now apply IH.
Qed.

(** A successful old startup establishes every guard of the generic startup
    rule.  This is the first quantified branch of the forward simulation. *)
Lemma echo_ir_start_rule_enabled
    (state successor : @executable_echo_state node)
    (ordered_neighbors : list node) :
  @EchoStep node node_eq config state
      (EchoStart ordered_neighbors) successor ->
  eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeStart (@echo_ir_start_certificates node ordered_neighbors))
      (@echo_ir_start_rule node) =
    IRRuleEnabled.
Proof.
  intro step.
  pose proof (@EchoStep_start_guards node node_eq config
    state successor ordered_neighbors step) as
    [initial permutation].
  destruct initial as
    [not_started [configured_initial [messages_empty next_id_one]]].
  assert (parents_initial :
    forallb
      (fun process =>
        ir_option_node_eqb node_eq
          (process_parent (processes state process)) None)
      (config_nodes config) = true).
  {
    apply forallb_forall. intros process configured.
    rewrite (configured_initial process configured). reflexivity.
  }
  assert (pending_initial :
    forallb
      (fun process =>
        ir_node_list_eqb node_eq
          (process_pending (processes state process)) [])
      (config_nodes config) = true).
  {
    apply forallb_forall. intros process configured.
    rewrite (configured_initial process configured). reflexivity.
  }
  assert (finished_initial :
    forallb
      (fun process =>
        Bool.eqb (process_finished (processes state process)) false)
      (config_nodes config) = true).
  {
    apply forallb_forall. intros process configured.
    rewrite (configured_initial process configured). reflexivity.
  }
  assert (order_valid :
    ir_node_list_permutationb node_eq ordered_neighbors
      (nbrs (config_nodes config) (config_adjacent config)
        (config_initiator config)) = true).
  {
    apply (proj2 (ir_node_list_permutationb_true_iff
      node_eq ordered_neighbors
      (nbrs (config_nodes config) (config_adjacent config)
        (config_initiator config)))).
    exact permutation.
  }
  unfold eval_ir_rule, echo_ir_start_rule.
  cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches eval_ir_guards
    echo_ir_started echo_ir_process_initial echo_ir_parent echo_ir_pending
    echo_ir_finished echo_ir_option_none echo_ir_empty_nodes echo_ir_bool
    echo_ir_start_order echo_ir_neighbors echo_ir_initiator echo_ir_equal
    echo_ir_nat echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    echo_ir_start_certificates eval_ir_expr ir_value_eqb
    ir_global_fields ir_config_fields ir_processes ir_message_store
    ir_next_message_id ir_config_nodes ir_config_neighbors echo_ir_signature
    echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_start_certificate_field_type].
  rewrite not_started, messages_empty, next_id_one.
  rewrite parents_initial, pending_initial, finished_initial, order_valid.
  reflexivity.
Qed.

Lemma echo_ir_start_rule_selected
    (state successor : @executable_echo_state node)
    (ordered_neighbors : list node) :
  @EchoStep node node_eq config state
      (EchoStart ordered_neighbors) successor ->
  select_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeStart (@echo_ir_start_certificates node ordered_neighbors))
      (@echo_ir_rules node) =
    IRUniqueRuleSelected (@echo_ir_start_rule node).
Proof.
  intro step.
  pose proof (echo_ir_start_rule_enabled
    state successor ordered_neighbors step) as enabled.
  unfold echo_ir_rules.
  cbn [select_ir_rule].
  rewrite enabled.
  cbn [select_ir_rule eval_ir_rule ir_rule_pattern
    ir_event_pattern_matches echo_ir_first_request_nonleaf_rule
    echo_ir_first_request_leaf_rule echo_ir_repeated_request_rule
    echo_ir_initiator_request_rule echo_ir_participant_reply_more_rule
    echo_ir_participant_reply_final_rule echo_ir_initiator_reply_more_rule
    echo_ir_initiator_reply_final_rule].
  reflexivity.
Qed.

(** The startup action itself produces a state related to the old startup
    successor.  Rule selection and action correspondence are kept separate so
    the remaining delivery cases can reuse the same proof shape. *)
Lemma echo_ir_start_action_forward
    (state successor : @executable_echo_state node)
    (ordered_neighbors : list node) :
  @EchoStep node node_eq config state
      (EchoStart ordered_neighbors) successor ->
  exists ir_successor,
    eval_ir_action node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeStart (@echo_ir_start_certificates node ordered_neighbors))
      (ir_rule_action (@echo_ir_start_rule node)) =
        Some ir_successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intro step.
  assert (selected_old :
    lookup_rule (@event_tag node (EchoStart ordered_neighbors)) echo_program =
      Some start_rule).
  {
    reflexivity.
  }
  pose proof (@EchoStep_selected_action node node_eq config
    state successor (EchoStart ordered_neighbors) start_rule
    step selected_old) as old_action.
  unfold start_rule in old_action.
  cbn [EchoTransitionIR.eval_action EchoTransitionIR.ir_rule_action
    EchoTransitionIR.eval_nodes_expr
    EchoTransitionIR.event_ordered_nodes] in old_action.
  unfold apply_echo_start in old_action.
  cbn in old_action.
  subst successor.
  unfold echo_ir_start_rule.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action
    echo_ir_set_parent echo_ir_set_pending echo_ir_set_finished
    echo_ir_emit_many echo_ir_initiator echo_ir_option_none
    echo_ir_start_order echo_ir_bool echo_ir_encode_config
    echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_globals
    echo_ir_start_certificates eval_ir_expr ir_set_local_field
    ir_set_global_field ir_emit_messages eval_ir_payload_exprs
    echo_ir_signature echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_start_certificate_field_type].
  eexists. split.
  - reflexivity.
  - unfold echo_ir_states_correspond.
    repeat split.
    + intros process field.
      cbn [ir_emit_messages ir_set_global_field ir_processes processes].
      destruct (node_eq (config_initiator config) process)
        as [same | different].
      * subst process.
        rewrite echo_update_process_same.
        destruct field.
        -- cbn [ir_set_local_field ir_processes processes
             echo_ir_encode_process].
           repeat rewrite ir_update_processes_same.
           rewrite ir_update_field_different by discriminate.
           rewrite ir_update_field_different by discriminate.
           rewrite ir_update_field_same. reflexivity.
        -- cbn [ir_set_local_field ir_processes processes
             echo_ir_encode_process].
           repeat rewrite ir_update_processes_same.
           rewrite ir_update_field_different by discriminate.
           rewrite ir_update_field_same. reflexivity.
        -- cbn [ir_set_local_field ir_processes processes
             echo_ir_encode_process].
           rewrite ir_update_processes_same.
           rewrite ir_update_field_same. reflexivity.
      * rewrite echo_update_process_different by exact different.
        cbn [ir_set_local_field ir_processes processes
          echo_ir_encode_process].
        repeat rewrite ir_update_processes_different by exact different.
        reflexivity.
    + cbn [ir_emit_messages ir_set_global_field ir_set_local_field
        ir_message_store message_store echo_ir_encode_state].
      rewrite List.map_app.
      cbn [ir_set_global_field ir_set_local_field ir_next_message_id
        echo_ir_encode_state].
      pose proof (echo_ir_materialize_messages_encoding
        (next_message_id state) EchoRequest (config_initiator config)
        ordered_neighbors) as materialized.
      cbn [echo_ir_encode_kind] in materialized.
      rewrite materialized. reflexivity.
    + intros field. destruct field.
      cbn [ir_emit_messages ir_set_global_field ir_global_fields started
        echo_ir_encode_globals].
      rewrite ir_update_field_same. reflexivity.
    + cbn [ir_emit_messages ir_set_global_field ir_set_local_field
        ir_next_message_id next_message_id next_echo_message_id_after
        echo_ir_encode_state].
      unfold next_echo_message_id_after.
      now rewrite List.length_map.
Qed.

(** First end-to-end forward-simulation case: the old successful startup is
    accepted by the generic interpreter, reports the generic startup rule,
    and produces a pointwise-corresponding successor. *)
Theorem echo_ir_start_forward_simulates
    (state successor : @executable_echo_state node)
    (ordered_neighbors : list node) :
  @EchoStep node node_eq config state
      (EchoStart ordered_neighbors) successor ->
  exists ir_successor,
    interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state)
      (echo_ir_encode_event config (EchoStart ordered_neighbors)) =
        @IRStepSuccess node echo_ir_signature
          EchoIRStartRule ir_successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intro step.
  pose proof (echo_ir_start_rule_selected
    state successor ordered_neighbors step) as selected.
  destruct (echo_ir_start_action_forward
    state successor ordered_neighbors step) as
    [ir_successor [action correspondence]].
  exists ir_successor. split.
  - unfold interpret_protocol_rules.
    cbn [echo_ir_encode_event ir_resolve_event].
    rewrite selected, action. reflexivity.
  - exact correspondence.
Qed.

(** Reverse simulation for startup.  A generic success with the startup rule
    contains enough checked evidence to reconstruct a genuine old executable
    [EchoStep].  Reusing the forward theorem then identifies the generic
    successor without duplicating the action-correspondence proof. *)
Theorem echo_ir_start_backward_simulates
    (state : @executable_echo_state node)
    (ordered_neighbors : list node)
    (ir_successor : ir_protocol_state node echo_ir_signature) :
  interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state)
      (echo_ir_encode_event config (EchoStart ordered_neighbors)) =
    @IRStepSuccess node echo_ir_signature EchoIRStartRule ir_successor ->
  exists successor,
    @EchoStep node node_eq config state
      (EchoStart ordered_neighbors) successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intro interpreted.
  destruct (interpret_protocol_rules_success_components
    node_eq (echo_ir_encode_config config) (@echo_ir_rules node)
    (echo_ir_encode_state state)
    (echo_ir_encode_event config (EchoStart ordered_neighbors))
    EchoIRStartRule ir_successor interpreted) as
    [runtime_event [selected_rule
      [resolved [selected [selected_id action]]]]].
  cbn [echo_ir_encode_event ir_resolve_event] in resolved.
  inversion resolved. subst runtime_event.
  pose proof (select_ir_rule_unique_in node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeStart (@echo_ir_start_certificates node ordered_neighbors))
    (@echo_ir_rules node) selected_rule selected) as selected_in.
  assert (selected_rule = @echo_ir_start_rule node) as selected_is_start.
  {
    cbn [echo_ir_rules] in selected_in.
    repeat destruct selected_in as [same | selected_in];
      try contradiction; subst selected_rule;
      cbn [echo_ir_start_rule echo_ir_first_request_nonleaf_rule
        echo_ir_first_request_leaf_rule echo_ir_repeated_request_rule
        echo_ir_initiator_request_rule echo_ir_participant_reply_more_rule
        echo_ir_participant_reply_final_rule echo_ir_initiator_reply_more_rule
        echo_ir_initiator_reply_final_rule ir_rule_id] in selected_id;
      try discriminate; reflexivity.
  }
  subst selected_rule.
  pose proof (select_ir_rule_unique_is_enabled node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeStart (@echo_ir_start_certificates node ordered_neighbors))
    (@echo_ir_rules node) (@echo_ir_start_rule node) selected) as enabled.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeStart (@echo_ir_start_certificates node ordered_neighbors))
    (@echo_ir_start_rule node) (IRNotExpr (@echo_ir_started node))
    enabled ltac:(cbn [echo_ir_start_rule]; now left)) as not_started.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeStart (@echo_ir_start_certificates node ordered_neighbors))
    (@echo_ir_start_rule node)
    (@IRAllNodesLocalEqualExpr node echo_ir_signature
      EchoIRParent (@echo_ir_option_none node))
    enabled ltac:(cbn [echo_ir_start_rule]; now right; left)) as parents_initial.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeStart (@echo_ir_start_certificates node ordered_neighbors))
    (@echo_ir_start_rule node)
    (@IRAllNodesLocalEqualExpr node echo_ir_signature
      EchoIRPending (@echo_ir_empty_nodes node))
    enabled ltac:(cbn [echo_ir_start_rule]; now right; right; left)) as pending_initial.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeStart (@echo_ir_start_certificates node ordered_neighbors))
    (@echo_ir_start_rule node)
    (@IRAllNodesLocalEqualExpr node echo_ir_signature
      EchoIRFinished (@echo_ir_bool node false))
    enabled ltac:(cbn [echo_ir_start_rule]; now right; right; right; left)) as finished_initial.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeStart (@echo_ir_start_certificates node ordered_neighbors))
    (@echo_ir_start_rule node) (@IRMessageStoreEmptyExpr node echo_ir_signature)
    enabled ltac:(cbn [echo_ir_start_rule]; now right; right; right; right; left))
    as messages_empty.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeStart (@echo_ir_start_certificates node ordered_neighbors))
    (@echo_ir_start_rule node)
    (@IREqualExpr node echo_ir_signature IRNat
      (@IRNextMessageIdExpr node echo_ir_signature) (@echo_ir_nat node 1))
    enabled ltac:(cbn [echo_ir_start_rule]; now right; right; right; right; right; left))
    as next_id_one.
  pose proof (eval_ir_rule_enabled_guard node_eq
    (echo_ir_encode_config config) (echo_ir_encode_state state)
    (IRRuntimeStart (@echo_ir_start_certificates node ordered_neighbors))
    (@echo_ir_start_rule node)
    (IRListPermutationExpr (@echo_ir_start_order node)
      (@echo_ir_neighbors node (@echo_ir_initiator node)))
    enabled ltac:(cbn [echo_ir_start_rule];
      repeat (first [left; reflexivity | right]))) as order_valid.
  cbn [eval_ir_expr echo_ir_started echo_ir_encode_config
    echo_ir_encode_config_fields echo_ir_encode_state echo_ir_encode_process
    echo_ir_encode_globals ir_global_fields ir_processes ir_message_store
    ir_next_message_id ir_config_nodes echo_ir_option_none echo_ir_empty_nodes
    echo_ir_bool echo_ir_nat echo_ir_start_order echo_ir_neighbors
    echo_ir_initiator echo_ir_start_certificates ir_config_fields
    ir_config_neighbors ir_value_eqb echo_ir_signature
    echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_start_certificate_field_type]
    in not_started, parents_initial, pending_initial, finished_initial,
      messages_empty, next_id_one, order_valid.
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
    - cbn [guard_holds].
      repeat split; assumption.
    - constructor.
      + cbn [guard_holds eval_nodes_expr event_ordered_nodes
          eval_node_expr].
        exact order_valid_bool.
      + constructor.
  }
  exists (@EchoTransitionIR.eval_action node node_eq config state
    (EchoStart ordered_neighbors)
    (EchoTransitionIR.ir_rule_action start_rule)).
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
  split; [exact old_step |].
  destruct (echo_ir_start_forward_simulates state
      (@EchoTransitionIR.eval_action node node_eq config state
        (EchoStart ordered_neighbors)
        (EchoTransitionIR.ir_rule_action start_rule))
      ordered_neighbors old_step) as
    [simulated_successor [simulated correspondence]].
  rewrite interpreted in simulated. inversion simulated. subst.
  exact correspondence.
Qed.

(** Transfer the checked old non-leaf delivery guards into the corresponding
    generic rule. *)
Lemma echo_ir_first_request_nonleaf_rule_enabled
    (state successor : @executable_echo_state node)
    (message : @echo_message node)
    (ordered_forwards : list node) :
  @EchoStep node node_eq config state
      (EchoFirstRequestNonLeaf message ordered_forwards) successor ->
  eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoFirstRequestNonLeaf message ordered_forwards)))
      (@echo_ir_first_request_nonleaf_rule node) =
    IRRuleEnabled.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule (IRGuardKind EchoRequest)
    step eq_refl ltac:(
      cbn [first_echo_nonleaf_rule];
      repeat (first [left; reflexivity | right]))) as request_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule
    (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [first_echo_nonleaf_rule];
      repeat (first [left; reflexivity | right]))) as receiver_not_initiator.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule (IRGuardProcessInitial IRMessageReceiver)
    step eq_refl ltac:(
      cbn [first_echo_nonleaf_rule];
      repeat (first [left; reflexivity | right]))) as receiver_initial.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule
    (IRGuardPermutation IRNodesOrdered
      (IRNodesRemove IRMessageSender (IRNodesNeighbors IRMessageReceiver)))
    step eq_refl ltac:(
      cbn [first_echo_nonleaf_rule];
      repeat (first [left; reflexivity | right]))) as forwarding_permutation.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule (IRGuardNodesNonempty IRNodesOrdered)
    step eq_refl ltac:(
      cbn [first_echo_nonleaf_rule];
      repeat (first [left; reflexivity | right]))) as forwarding_nonempty.
  cbn [guard_holds eval_node_expr event_message eval_nodes_expr
    event_ordered_nodes] in request_kind, receiver_not_initiator,
    receiver_initial, forwarding_permutation, forwarding_nonempty.
  rewrite <- echo_ir_remove_node_agrees in forwarding_permutation.
  assert (targets_nonempty :
    ir_remove_node node_eq (message_sender message)
      (nbrs (config_nodes config) (config_adjacent config)
        (message_receiver message)) <> []).
  {
    intro targets_empty. rewrite targets_empty in forwarding_permutation.
    apply forwarding_nonempty.
    apply Permutation_nil.
    now apply Permutation_sym.
  }
  assert (order_valid :
    ir_node_list_permutationb node_eq ordered_forwards
      (ir_remove_node node_eq (message_sender message)
        (nbrs (config_nodes config) (config_adjacent config)
          (message_receiver message))) = true).
  {
    apply (proj2 (ir_node_list_permutationb_true_iff
      node_eq ordered_forwards
      (ir_remove_node node_eq (message_sender message)
        (nbrs (config_nodes config) (config_adjacent config)
          (message_receiver message))))).
    exact forwarding_permutation.
  }
  unfold eval_ir_rule, echo_ir_first_request_nonleaf_rule.
  unfold echo_ir_not_equal, echo_ir_equal, echo_ir_receiver,
    echo_ir_initiator, echo_ir_process_initial, echo_ir_parent,
    echo_ir_pending, echo_ir_finished, echo_ir_option_none,
    echo_ir_empty_nodes, echo_ir_bool, echo_ir_process_seen,
    echo_ir_forward_targets, echo_ir_nonempty, echo_ir_is_empty,
    echo_ir_neighbors, echo_ir_sender, echo_ir_forward_order.
  unfold echo_ir_equal, echo_ir_parent, echo_ir_finished,
    echo_ir_remove, echo_ir_receiver.
  cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches eval_ir_guards
    echo_ir_not_equal echo_ir_equal echo_ir_receiver echo_ir_initiator
    echo_ir_process_initial echo_ir_parent echo_ir_pending echo_ir_finished
    echo_ir_option_none echo_ir_empty_nodes echo_ir_bool
    echo_ir_process_seen echo_ir_forward_targets echo_ir_nonempty
    echo_ir_is_empty echo_ir_neighbors echo_ir_sender echo_ir_forward_order
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_globals echo_ir_encode_message
    echo_ir_encode_kind echo_ir_delivery_certificates
    echo_ir_event_forward_order echo_ir_event_expected_parent eval_ir_expr
    ir_value_eqb ir_processes ir_config_fields ir_config_neighbors
    ir_message_kind ir_message_sender ir_message_receiver
    echo_ir_signature echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  rewrite request_kind.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRRequest EchoIRRequest) as [same_kind | impossible_kind].
  2: contradiction.
  cbn [List.app eval_ir_guards eval_ir_expr echo_ir_encode_kind
    echo_ir_signature echo_ir_message_kind_eq_dec ir_rule_guards
    ir_processes ir_config_fields ir_config_neighbors ir_message_kind
    ir_message_sender ir_message_receiver ir_event_message
    echo_ir_encode_config
    echo_ir_encode_config_fields echo_ir_encode_state echo_ir_encode_process
    echo_ir_encode_message echo_ir_delivery_certificates
    echo_ir_event_forward_order echo_ir_local_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type
    ir_value_eqb].
  rewrite receiver_initial, order_valid.
  destruct (node_eq (message_receiver message) (config_initiator config))
    as [same_receiver | different_receiver].
  - contradiction.
  - destruct (ir_remove_node node_eq (message_sender message)
      (nbrs (config_nodes config) (config_adjacent config)
        (message_receiver message))) as [|target targets]
      eqn:targets_shape.
    + contradiction.
    + destruct ordered_forwards as [|first_forward remaining_forwards].
      * contradiction.
      * unfold initial_echo_process, ir_option_node_eqb,
          ir_node_list_eqb, ir_node_eqb.
        cbn.
        destruct (signature_message_kind_eq_dec echo_ir_signature
          EchoIRRequest EchoIRRequest) as [_ | impossible].
        2: contradiction.
        destruct (node_eq (message_receiver message)
          (config_initiator config)) as [same | different].
        -- contradiction.
        -- reflexivity.
Qed.

Lemma echo_ir_first_request_nonleaf_action_forward
    (state successor : @executable_echo_state node)
    (message : @echo_message node)
    (ordered_forwards : list node) :
  @EchoStep node node_eq config state
      (EchoFirstRequestNonLeaf message ordered_forwards) successor ->
  exists ir_successor,
    eval_ir_action node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoFirstRequestNonLeaf message ordered_forwards)))
      (ir_rule_action (@echo_ir_first_request_nonleaf_rule node)) =
        Some ir_successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intro step.
  pose proof (@EchoStep_selected_action node node_eq config
    state successor (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule step eq_refl) as old_action.
  unfold first_echo_nonleaf_rule in old_action.
  cbn [EchoTransitionIR.eval_action EchoTransitionIR.ir_rule_action
    EchoTransitionIR.eval_process_expr EchoTransitionIR.eval_parent_expr
    EchoTransitionIR.eval_nodes_expr EchoTransitionIR.eval_node_expr
    EchoTransitionIR.eval_outbound_expr EchoTransitionIR.event_message
    EchoTransitionIR.event_ordered_nodes] in old_action.
  unfold apply_echo_delivery in old_action.
  cbn in old_action. subst successor.
  unfold echo_ir_first_request_nonleaf_rule.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action
    echo_ir_set_parent echo_ir_set_pending echo_ir_set_finished
    echo_ir_emit_many echo_ir_receiver echo_ir_sender echo_ir_some
    echo_ir_forward_order echo_ir_bool echo_ir_empty_payload
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_globals echo_ir_encode_message
    echo_ir_delivery_certificates echo_ir_event_forward_order
    echo_ir_event_expected_parent eval_ir_expr ir_set_local_field
    ir_remove_selected_message ir_emit_messages eval_ir_payload_exprs
    echo_ir_signature echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  eexists. split.
  - reflexivity.
  - unfold echo_ir_states_correspond.
    repeat split.
    + intros process field.
      cbn [ir_emit_messages ir_remove_selected_message ir_processes
        processes].
      destruct (node_eq (message_receiver message) process)
        as [same | different].
      * subst process.
        rewrite echo_update_process_same.
        destruct field.
        -- cbn [ir_set_local_field ir_processes processes
             echo_ir_encode_process].
           repeat rewrite ir_update_processes_same.
           rewrite ir_update_field_different by discriminate.
           rewrite ir_update_field_different by discriminate.
           rewrite ir_update_field_same. reflexivity.
        -- cbn [ir_set_local_field ir_processes processes
             echo_ir_encode_process].
           repeat rewrite ir_update_processes_same.
           rewrite ir_update_field_different by discriminate.
           rewrite ir_update_field_same. reflexivity.
        -- cbn [ir_set_local_field ir_processes processes
             echo_ir_encode_process].
           rewrite ir_update_processes_same.
           rewrite ir_update_field_same. reflexivity.
      * rewrite echo_update_process_different by exact different.
        cbn [ir_set_local_field ir_processes processes
          echo_ir_encode_process].
        repeat rewrite ir_update_processes_different by exact different.
        reflexivity.
    + cbn [ir_emit_messages ir_remove_selected_message ir_set_local_field
        ir_message_store message_store echo_ir_encode_state].
      assert (encoded_id :
        ir_message_id (@echo_ir_encode_message node message) =
          message_id message) by reflexivity.
      assert (encoded_receiver :
        ir_message_receiver (@echo_ir_encode_message node message) =
          message_receiver message) by reflexivity.
      assert (encoded_sender :
        ir_message_sender (@echo_ir_encode_message node message) =
          message_sender message) by reflexivity.
      rewrite encoded_id, encoded_receiver, encoded_sender.
      rewrite List.map_app.
      rewrite echo_ir_remove_message_encoding.
      unfold ir_remove_selected_message.
      cbn [ir_set_local_field ir_next_message_id echo_ir_encode_state].
      pose proof (echo_ir_materialize_messages_encoding
        (next_message_id state) EchoRequest (message_receiver message)
        ordered_forwards) as materialized.
      cbn [echo_ir_encode_kind] in materialized.
      rewrite materialized. reflexivity.
    + cbn [ir_emit_messages ir_remove_selected_message ir_set_local_field
        ir_next_message_id next_message_id next_echo_message_id_after
        echo_ir_encode_state].
      unfold next_echo_message_id_after.
      now rewrite List.length_map.
Qed.

Lemma echo_ir_first_request_nonleaf_tail_selects_none
    (state successor : @executable_echo_state node)
    (message : @echo_message node)
    (ordered_forwards : list node) :
  @EchoStep node node_eq config state
      (EchoFirstRequestNonLeaf message ordered_forwards) successor ->
  select_ir_rule node_eq (echo_ir_encode_config config)
    (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message)
      (@echo_ir_delivery_certificates node config
        (EchoFirstRequestNonLeaf message ordered_forwards)))
    [@echo_ir_first_request_leaf_rule node;
     @echo_ir_repeated_request_rule node;
     @echo_ir_initiator_request_rule node;
     @echo_ir_participant_reply_more_rule node;
     @echo_ir_participant_reply_final_rule node;
     @echo_ir_initiator_reply_more_rule node;
     @echo_ir_initiator_reply_final_rule node] =
  IRNoRuleSelected.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule (IRGuardKind EchoRequest)
    step eq_refl ltac:(
      cbn [first_echo_nonleaf_rule];
      repeat (first [left; reflexivity | right]))) as request_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule
    (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [first_echo_nonleaf_rule];
      repeat (first [left; reflexivity | right]))) as receiver_not_initiator.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule (IRGuardProcessInitial IRMessageReceiver)
    step eq_refl ltac:(
      cbn [first_echo_nonleaf_rule];
      repeat (first [left; reflexivity | right]))) as receiver_initial.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule
    (IRGuardPermutation IRNodesOrdered
      (IRNodesRemove IRMessageSender (IRNodesNeighbors IRMessageReceiver)))
    step eq_refl ltac:(
      cbn [first_echo_nonleaf_rule];
      repeat (first [left; reflexivity | right]))) as forwarding_permutation.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule (IRGuardNodesNonempty IRNodesOrdered)
    step eq_refl ltac:(
      cbn [first_echo_nonleaf_rule];
      repeat (first [left; reflexivity | right]))) as forwarding_nonempty.
  cbn [guard_holds eval_node_expr event_message eval_nodes_expr
    event_ordered_nodes] in request_kind, receiver_not_initiator,
    receiver_initial, forwarding_permutation, forwarding_nonempty.
  rewrite <- echo_ir_remove_node_agrees in forwarding_permutation.
  assert (targets_nonempty :
    ir_remove_node node_eq (message_sender message)
      (nbrs (config_nodes config) (config_adjacent config)
        (message_receiver message)) <> []).
  {
    intro targets_empty. rewrite targets_empty in forwarding_permutation.
    apply forwarding_nonempty.
    apply Permutation_nil. now apply Permutation_sym.
  }
  assert (receiver_parent_none :
    process_parent (processes state (message_receiver message)) = None).
  { rewrite receiver_initial. reflexivity. }
  assert (receiver_pending_empty :
    process_pending (processes state (message_receiver message)) = []).
  { rewrite receiver_initial. reflexivity. }
  assert (receiver_not_finished :
    process_finished (processes state (message_receiver message)) = false).
  { rewrite receiver_initial. reflexivity. }
  unfold echo_ir_encode_message.
  rewrite request_kind.
  unfold echo_ir_first_request_leaf_rule, echo_ir_repeated_request_rule,
    echo_ir_initiator_request_rule, echo_ir_participant_reply_more_rule,
    echo_ir_participant_reply_final_rule, echo_ir_initiator_reply_more_rule,
    echo_ir_initiator_reply_final_rule.
  unfold echo_ir_not_equal, echo_ir_equal, echo_ir_receiver,
    echo_ir_initiator, echo_ir_process_initial, echo_ir_parent,
    echo_ir_pending, echo_ir_finished, echo_ir_option_none,
    echo_ir_empty_nodes, echo_ir_bool, echo_ir_process_seen,
    echo_ir_forward_targets, echo_ir_nonempty, echo_ir_is_empty,
    echo_ir_neighbors, echo_ir_sender, echo_ir_forward_order,
    echo_ir_removed_pending.
  unfold echo_ir_equal, echo_ir_parent, echo_ir_pending, echo_ir_finished,
    echo_ir_remove, echo_ir_receiver.
  cbn [List.app select_ir_rule eval_ir_rule ir_rule_pattern ir_rule_guards
    ir_event_pattern_matches eval_ir_guards eval_ir_expr
    echo_ir_encode_kind echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_message
    echo_ir_delivery_certificates echo_ir_event_forward_order
    echo_ir_event_expected_parent ir_value_eqb ir_processes ir_config_fields
    ir_config_neighbors ir_message_kind ir_message_sender
    ir_message_receiver ir_event_message echo_ir_signature
    echo_ir_message_kind_eq_dec echo_ir_local_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRRequest EchoIRRequest) as [_ | impossible_kind].
  2: { contradiction. }
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRReply EchoIRRequest) as [impossible_kind | _].
  1: { discriminate. }
  cbn [select_ir_rule eval_ir_rule ir_event_pattern_matches eval_ir_guards
    eval_ir_expr echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process ir_value_eqb ir_processes
    ir_config_fields ir_config_neighbors ir_message_sender
    ir_message_receiver ir_event_message echo_ir_signature
    echo_ir_local_field_type echo_ir_config_field_type].
  destruct (ir_remove_node node_eq (message_sender message)
    (nbrs (config_nodes config) (config_adjacent config)
      (message_receiver message))) as [|target targets]
    eqn:targets_shape.
  - contradiction.
  - unfold initial_echo_process, ir_option_node_eqb,
      ir_node_list_eqb, ir_node_eqb.
    cbn.
    rewrite receiver_parent_none, receiver_pending_empty,
      receiver_not_finished.
    rewrite targets_shape.
    unfold ir_node_eqb.
    destruct (node_eq (message_receiver message)
      (config_initiator config)) as [same_node | different_nodes].
    + contradiction.
    + cbn.
    reflexivity.
Qed.

Lemma echo_ir_first_request_nonleaf_rule_selected
    (state successor : @executable_echo_state node)
    (message : @echo_message node)
    (ordered_forwards : list node) :
  @EchoStep node node_eq config state
      (EchoFirstRequestNonLeaf message ordered_forwards) successor ->
  select_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoFirstRequestNonLeaf message ordered_forwards)))
      (@echo_ir_rules node) =
    IRUniqueRuleSelected (@echo_ir_first_request_nonleaf_rule node).
Proof.
  intro step.
  pose proof (echo_ir_first_request_nonleaf_rule_enabled
    state successor message ordered_forwards step) as enabled.
  pose proof (echo_ir_first_request_nonleaf_tail_selects_none
    state successor message ordered_forwards step) as tail_none.
  assert (start_mismatch :
    eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoFirstRequestNonLeaf message ordered_forwards)))
      (@echo_ir_start_rule node) = IRRuleMismatch).
  {
    unfold eval_ir_rule, echo_ir_start_rule.
    reflexivity.
  }
  unfold echo_ir_rules.
  erewrite select_ir_rule_cons_mismatch; [| exact start_mismatch].
  now apply select_ir_rule_cons_unique.
Qed.

(** A reachable old non-leaf request delivery resolves the same queued
    message by ID, selects the corresponding generic rule, and executes to a
    pointwise-corresponding successor. *)
Theorem echo_ir_first_request_nonleaf_forward_simulates
    (state successor : @executable_echo_state node)
    (message : @echo_message node)
    (ordered_forwards : list node) :
  @echo_reachable node node_eq config state ->
  @EchoStep node node_eq config state
      (EchoFirstRequestNonLeaf message ordered_forwards) successor ->
  exists ir_successor,
    interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state)
      (echo_ir_encode_event config
        (EchoFirstRequestNonLeaf message ordered_forwards)) =
      @IRStepSuccess node echo_ir_signature
        EchoIRFirstRequestNonLeafRule ir_successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intros reachable step.
  pose proof (@echo_ir_resolve_successful_delivery
    node node_eq config state successor
    (EchoFirstRequestNonLeaf message ordered_forwards)
    reachable step I) as resolved.
  pose proof (echo_ir_first_request_nonleaf_rule_selected
    state successor message ordered_forwards step) as selected.
  destruct (echo_ir_first_request_nonleaf_action_forward
    state successor message ordered_forwards step) as
    [ir_successor [action correspondence]].
  exists ir_successor. split.
  - unfold interpret_protocol_rules.
    rewrite resolved.
    cbn [event_message].
    rewrite selected, action. reflexivity.
  - exact correspondence.
Qed.

(** The first-request leaf branch differs from the non-leaf branch only at
    the forwarding boundary: removing the sender leaves no target. *)
Lemma echo_ir_first_request_leaf_rule_enabled
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoFirstRequestLeaf message) successor ->
  eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoFirstRequestLeaf message)))
      (@echo_ir_first_request_leaf_rule node) = IRRuleEnabled.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestLeaf message)
    first_echo_leaf_rule (IRGuardKind EchoRequest)
    step eq_refl ltac:(
      cbn [first_echo_leaf_rule];
      repeat (first [left; reflexivity | right]))) as request_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestLeaf message)
    first_echo_leaf_rule
    (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [first_echo_leaf_rule];
      repeat (first [left; reflexivity | right]))) as receiver_not_initiator.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestLeaf message)
    first_echo_leaf_rule (IRGuardProcessInitial IRMessageReceiver)
    step eq_refl ltac:(
      cbn [first_echo_leaf_rule];
      repeat (first [left; reflexivity | right]))) as receiver_initial.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestLeaf message)
    first_echo_leaf_rule
    (IRGuardNodesEmpty
      (IRNodesRemove IRMessageSender (IRNodesNeighbors IRMessageReceiver)))
    step eq_refl ltac:(
      cbn [first_echo_leaf_rule];
      repeat (first [left; reflexivity | right]))) as targets_empty.
  cbn [guard_holds eval_node_expr event_message eval_nodes_expr]
    in request_kind, receiver_not_initiator, receiver_initial, targets_empty.
  rewrite <- echo_ir_remove_node_agrees in targets_empty.
  unfold eval_ir_rule, echo_ir_first_request_leaf_rule.
  unfold echo_ir_not_equal, echo_ir_equal, echo_ir_receiver,
    echo_ir_initiator, echo_ir_process_initial, echo_ir_parent,
    echo_ir_pending, echo_ir_finished, echo_ir_option_none,
    echo_ir_empty_nodes, echo_ir_bool, echo_ir_process_seen,
    echo_ir_forward_targets, echo_ir_is_empty, echo_ir_neighbors,
    echo_ir_sender.
  unfold echo_ir_equal, echo_ir_parent, echo_ir_finished,
    echo_ir_remove, echo_ir_receiver.
  cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches eval_ir_guards
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_globals echo_ir_encode_message
    echo_ir_encode_kind echo_ir_delivery_certificates
    echo_ir_event_forward_order echo_ir_event_expected_parent eval_ir_expr
    ir_value_eqb ir_processes ir_config_fields ir_config_neighbors
    ir_message_kind ir_message_sender ir_message_receiver
    echo_ir_signature echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  rewrite request_kind.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRRequest EchoIRRequest) as [_ | impossible_kind].
  2: contradiction.
  cbn [List.app eval_ir_guards eval_ir_expr echo_ir_encode_kind
    echo_ir_signature echo_ir_message_kind_eq_dec ir_rule_guards
    ir_processes ir_config_fields ir_config_neighbors ir_message_kind
    ir_message_sender ir_message_receiver ir_event_message
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_message
    echo_ir_delivery_certificates echo_ir_event_forward_order
    echo_ir_local_field_type echo_ir_config_field_type
    echo_ir_delivery_certificate_field_type ir_value_eqb].
  rewrite receiver_initial, targets_empty.
  destruct (node_eq (message_receiver message) (config_initiator config))
    as [same_receiver | different_receiver].
  - contradiction.
  - unfold initial_echo_process, ir_option_node_eqb,
      ir_node_list_eqb, ir_node_eqb.
    cbn.
    destruct (signature_message_kind_eq_dec echo_ir_signature
      EchoIRRequest EchoIRRequest) as [_ | impossible].
    2: contradiction.
    destruct (node_eq (message_receiver message)
      (config_initiator config)) as [same | different].
    + contradiction.
    + reflexivity.
Qed.

(** The same empty-target fact makes the preceding non-leaf rule disabled,
    so rule order cannot steal a valid leaf delivery. *)
Lemma echo_ir_first_request_nonleaf_disabled_on_leaf
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoFirstRequestLeaf message) successor ->
  eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoFirstRequestLeaf message)))
      (@echo_ir_first_request_nonleaf_rule node) = IRRuleDisabled.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestLeaf message)
    first_echo_leaf_rule (IRGuardKind EchoRequest)
    step eq_refl ltac:(
      cbn [first_echo_leaf_rule];
      repeat (first [left; reflexivity | right]))) as request_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestLeaf message)
    first_echo_leaf_rule
    (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [first_echo_leaf_rule];
      repeat (first [left; reflexivity | right]))) as receiver_not_initiator.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestLeaf message)
    first_echo_leaf_rule (IRGuardProcessInitial IRMessageReceiver)
    step eq_refl ltac:(
      cbn [first_echo_leaf_rule];
      repeat (first [left; reflexivity | right]))) as receiver_initial.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestLeaf message)
    first_echo_leaf_rule
    (IRGuardNodesEmpty
      (IRNodesRemove IRMessageSender (IRNodesNeighbors IRMessageReceiver)))
    step eq_refl ltac:(
      cbn [first_echo_leaf_rule];
      repeat (first [left; reflexivity | right]))) as targets_empty.
  cbn [guard_holds eval_node_expr event_message eval_nodes_expr]
    in request_kind, receiver_not_initiator, receiver_initial, targets_empty.
  rewrite <- echo_ir_remove_node_agrees in targets_empty.
  unfold eval_ir_rule, echo_ir_first_request_nonleaf_rule.
  unfold echo_ir_not_equal, echo_ir_equal, echo_ir_receiver,
    echo_ir_initiator, echo_ir_process_initial, echo_ir_parent,
    echo_ir_pending, echo_ir_finished, echo_ir_option_none,
    echo_ir_empty_nodes, echo_ir_bool, echo_ir_process_seen,
    echo_ir_forward_targets, echo_ir_nonempty, echo_ir_is_empty,
    echo_ir_neighbors, echo_ir_sender, echo_ir_forward_order.
  unfold echo_ir_equal, echo_ir_parent, echo_ir_finished,
    echo_ir_remove, echo_ir_receiver.
  cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches eval_ir_guards
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_globals echo_ir_encode_message
    echo_ir_encode_kind echo_ir_delivery_certificates
    echo_ir_event_forward_order echo_ir_event_expected_parent eval_ir_expr
    ir_value_eqb ir_processes ir_config_fields ir_config_neighbors
    ir_message_kind ir_message_sender ir_message_receiver
    echo_ir_signature echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  rewrite request_kind.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRRequest EchoIRRequest) as [_ | impossible_kind].
  2: contradiction.
  cbn [List.app eval_ir_guards eval_ir_expr echo_ir_encode_kind
    echo_ir_signature echo_ir_message_kind_eq_dec ir_rule_guards
    ir_processes ir_config_fields ir_config_neighbors ir_message_kind
    ir_message_sender ir_message_receiver ir_event_message
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_message
    echo_ir_delivery_certificates echo_ir_event_forward_order
    echo_ir_local_field_type echo_ir_config_field_type
    echo_ir_delivery_certificate_field_type ir_value_eqb].
  rewrite receiver_initial, targets_empty.
  destruct (node_eq (message_receiver message) (config_initiator config))
    as [same_receiver | different_receiver].
  - contradiction.
  - unfold initial_echo_process, ir_option_node_eqb,
      ir_node_list_eqb, ir_node_eqb.
    cbn.
    destruct (signature_message_kind_eq_dec echo_ir_signature
      EchoIRRequest EchoIRRequest) as [_ | impossible].
    2: contradiction.
    destruct (node_eq (message_receiver message)
      (config_initiator config)) as [same | different].
    + contradiction.
    + reflexivity.
Qed.

Lemma echo_ir_first_request_leaf_action_forward
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoFirstRequestLeaf message) successor ->
  exists ir_successor,
    eval_ir_action node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoFirstRequestLeaf message)))
      (ir_rule_action (@echo_ir_first_request_leaf_rule node)) =
        Some ir_successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intro step.
  pose proof (@EchoStep_selected_action node node_eq config
    state successor (EchoFirstRequestLeaf message)
    first_echo_leaf_rule step eq_refl) as old_action.
  unfold first_echo_leaf_rule in old_action.
  cbn [EchoTransitionIR.eval_action EchoTransitionIR.ir_rule_action
    EchoTransitionIR.eval_process_expr EchoTransitionIR.eval_parent_expr
    EchoTransitionIR.eval_nodes_expr EchoTransitionIR.eval_node_expr
    EchoTransitionIR.eval_outbound_expr EchoTransitionIR.event_message
    EchoTransitionIR.event_ordered_nodes] in old_action.
  unfold apply_echo_delivery in old_action.
  cbn in old_action. subst successor.
  unfold echo_ir_first_request_leaf_rule.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action
    echo_ir_set_parent echo_ir_set_pending echo_ir_set_finished
    echo_ir_emit_one echo_ir_receiver echo_ir_sender echo_ir_some
    echo_ir_bool echo_ir_empty_nodes echo_ir_empty_payload
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_globals echo_ir_encode_message
    echo_ir_delivery_certificates echo_ir_event_forward_order
    echo_ir_event_expected_parent eval_ir_expr ir_set_local_field
    ir_remove_selected_message ir_emit_messages eval_ir_payload_exprs
    echo_ir_signature echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  eexists. split.
  - reflexivity.
  - unfold echo_ir_states_correspond.
    repeat split.
    + intros process field.
      cbn [ir_emit_messages ir_remove_selected_message ir_processes
        processes].
      destruct (node_eq (message_receiver message) process)
        as [same | different].
      * subst process.
        rewrite echo_update_process_same.
        destruct field.
        -- cbn [ir_set_local_field ir_processes processes
             echo_ir_encode_process].
           repeat rewrite ir_update_processes_same.
           rewrite ir_update_field_different by discriminate.
           rewrite ir_update_field_different by discriminate.
           rewrite ir_update_field_same. reflexivity.
        -- cbn [ir_set_local_field ir_processes processes
             echo_ir_encode_process].
           repeat rewrite ir_update_processes_same.
           rewrite ir_update_field_different by discriminate.
           rewrite ir_update_field_same. reflexivity.
        -- cbn [ir_set_local_field ir_processes processes
             echo_ir_encode_process].
           rewrite ir_update_processes_same.
           rewrite ir_update_field_same. reflexivity.
      * rewrite echo_update_process_different by exact different.
        cbn [ir_set_local_field ir_processes processes
          echo_ir_encode_process].
        repeat rewrite ir_update_processes_different by exact different.
        reflexivity.
    + cbn [ir_emit_messages ir_remove_selected_message ir_set_local_field
        ir_message_store message_store echo_ir_encode_state].
      assert (encoded_id :
        ir_message_id (@echo_ir_encode_message node message) =
          message_id message) by reflexivity.
      assert (encoded_receiver :
        ir_message_receiver (@echo_ir_encode_message node message) =
          message_receiver message) by reflexivity.
      assert (encoded_sender :
        ir_message_sender (@echo_ir_encode_message node message) =
          message_sender message) by reflexivity.
      rewrite encoded_id, encoded_receiver, encoded_sender.
      rewrite List.map_app.
      rewrite echo_ir_remove_message_encoding.
      unfold ir_remove_selected_message.
      cbn [ir_set_local_field ir_next_message_id echo_ir_encode_state].
      pose proof (echo_ir_materialize_messages_encoding
        (next_message_id state) EchoReply (message_receiver message)
        [message_sender message]) as materialized.
      cbn [echo_ir_encode_kind] in materialized.
      rewrite materialized. reflexivity.
Qed.

Lemma echo_ir_first_request_leaf_tail_selects_none
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoFirstRequestLeaf message) successor ->
  select_ir_rule node_eq (echo_ir_encode_config config)
    (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message)
      (@echo_ir_delivery_certificates node config
        (EchoFirstRequestLeaf message)))
    [@echo_ir_repeated_request_rule node;
     @echo_ir_initiator_request_rule node;
     @echo_ir_participant_reply_more_rule node;
     @echo_ir_participant_reply_final_rule node;
     @echo_ir_initiator_reply_more_rule node;
     @echo_ir_initiator_reply_final_rule node] =
  IRNoRuleSelected.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestLeaf message)
    first_echo_leaf_rule (IRGuardKind EchoRequest)
    step eq_refl ltac:(
      cbn [first_echo_leaf_rule];
      repeat (first [left; reflexivity | right]))) as request_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestLeaf message)
    first_echo_leaf_rule
    (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [first_echo_leaf_rule];
      repeat (first [left; reflexivity | right]))) as receiver_not_initiator.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestLeaf message)
    first_echo_leaf_rule (IRGuardProcessInitial IRMessageReceiver)
    step eq_refl ltac:(
      cbn [first_echo_leaf_rule];
      repeat (first [left; reflexivity | right]))) as receiver_initial.
  cbn [guard_holds eval_node_expr event_message]
    in request_kind, receiver_not_initiator, receiver_initial.
  assert (receiver_parent_none :
    process_parent (processes state (message_receiver message)) = None).
  { rewrite receiver_initial. reflexivity. }
  assert (receiver_not_finished :
    process_finished (processes state (message_receiver message)) = false).
  { rewrite receiver_initial. reflexivity. }
  unfold echo_ir_encode_message.
  rewrite request_kind.
  unfold echo_ir_repeated_request_rule, echo_ir_initiator_request_rule,
    echo_ir_participant_reply_more_rule,
    echo_ir_participant_reply_final_rule,
    echo_ir_initiator_reply_more_rule, echo_ir_initiator_reply_final_rule.
  unfold echo_ir_not_equal, echo_ir_equal, echo_ir_receiver,
    echo_ir_initiator, echo_ir_parent, echo_ir_finished,
    echo_ir_process_seen, echo_ir_started, echo_ir_bool,
    echo_ir_option_none, echo_ir_some, echo_ir_expected_parent,
    echo_ir_pending, echo_ir_removed_pending, echo_ir_sender,
    echo_ir_is_empty, echo_ir_empty_nodes.
  unfold echo_ir_equal, echo_ir_parent, echo_ir_pending, echo_ir_finished,
    echo_ir_remove, echo_ir_receiver.
  cbn [List.app select_ir_rule eval_ir_rule ir_rule_pattern ir_rule_guards
    ir_event_pattern_matches eval_ir_guards eval_ir_expr
    echo_ir_encode_kind echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_message
    echo_ir_delivery_certificates echo_ir_event_forward_order
    echo_ir_event_expected_parent ir_value_eqb ir_processes ir_config_fields
    ir_config_neighbors ir_message_kind ir_message_sender
    ir_message_receiver ir_event_message echo_ir_signature
    echo_ir_message_kind_eq_dec echo_ir_local_field_type
    echo_ir_global_field_type echo_ir_config_field_type
    echo_ir_delivery_certificate_field_type].
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRRequest EchoIRRequest) as [_ | impossible_kind].
  2: contradiction.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRReply EchoIRRequest) as [impossible_kind | _].
  1: discriminate.
  cbn [select_ir_rule eval_ir_rule ir_event_pattern_matches eval_ir_guards
    eval_ir_expr echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process ir_value_eqb ir_processes
    ir_global_fields ir_config_fields ir_config_neighbors ir_message_sender
    ir_message_receiver ir_event_message echo_ir_signature
    echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type].
  unfold ir_node_eqb.
  destruct (node_eq (message_receiver message)
    (config_initiator config)) as [same_node | different_nodes].
  - contradiction.
  - cbn.
    rewrite receiver_parent_none, receiver_not_finished.
    unfold ir_node_eqb.
    destruct (node_eq (message_receiver message)
      (config_initiator config)) as [same_again | different_again].
    + contradiction.
    + reflexivity.
Qed.

Lemma echo_ir_first_request_leaf_rule_selected
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoFirstRequestLeaf message) successor ->
  select_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoFirstRequestLeaf message)))
      (@echo_ir_rules node) =
    IRUniqueRuleSelected (@echo_ir_first_request_leaf_rule node).
Proof.
  intro step.
  pose proof (echo_ir_first_request_leaf_rule_enabled
    state successor message step) as enabled.
  pose proof (echo_ir_first_request_nonleaf_disabled_on_leaf
    state successor message step) as nonleaf_disabled.
  pose proof (echo_ir_first_request_leaf_tail_selects_none
    state successor message step) as tail_none.
  assert (start_mismatch :
    eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoFirstRequestLeaf message)))
      (@echo_ir_start_rule node) = IRRuleMismatch).
  {
    unfold eval_ir_rule, echo_ir_start_rule.
    reflexivity.
  }
  unfold echo_ir_rules.
  erewrite select_ir_rule_cons_mismatch; [| exact start_mismatch].
  erewrite select_ir_rule_cons_disabled; [| exact nonleaf_disabled].
  now apply select_ir_rule_cons_unique.
Qed.

Theorem echo_ir_first_request_leaf_forward_simulates
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @echo_reachable node node_eq config state ->
  @EchoStep node node_eq config state
      (EchoFirstRequestLeaf message) successor ->
  exists ir_successor,
    interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state)
      (echo_ir_encode_event config (EchoFirstRequestLeaf message)) =
      @IRStepSuccess node echo_ir_signature
        EchoIRFirstRequestLeafRule ir_successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intros reachable step.
  pose proof (@echo_ir_resolve_successful_delivery
    node node_eq config state successor (EchoFirstRequestLeaf message)
    reachable step I) as resolved.
  pose proof (echo_ir_first_request_leaf_rule_selected
    state successor message step) as selected.
  destruct (echo_ir_first_request_leaf_action_forward
    state successor message step) as
    [ir_successor [action correspondence]].
  exists ir_successor. split.
  - unfold interpret_protocol_rules.
    rewrite resolved.
    cbn [event_message].
    rewrite selected, action. reflexivity.
  - exact correspondence.
Qed.

(** A repeated request is recognized by the receiver already having a parent
    or already being finished. *)
Lemma echo_ir_repeated_request_rule_enabled
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoRepeatedRequest message) successor ->
  eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoRepeatedRequest message)))
      (@echo_ir_repeated_request_rule node) = IRRuleEnabled.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoRepeatedRequest message)
    repeated_echo_rule (IRGuardKind EchoRequest)
    step eq_refl ltac:(
      cbn [repeated_echo_rule];
      repeat (first [left; reflexivity | right]))) as request_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoRepeatedRequest message)
    repeated_echo_rule
    (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [repeated_echo_rule];
      repeat (first [left; reflexivity | right]))) as receiver_not_initiator.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoRepeatedRequest message)
    repeated_echo_rule
    (IRGuardHasParentOrFinished IRMessageReceiver)
    step eq_refl ltac:(
      cbn [repeated_echo_rule];
      repeat (first [left; reflexivity | right]))) as receiver_seen.
  cbn [guard_holds eval_node_expr event_message]
    in request_kind, receiver_not_initiator, receiver_seen.
  unfold eval_ir_rule, echo_ir_repeated_request_rule.
  unfold echo_ir_not_equal, echo_ir_equal, echo_ir_receiver,
    echo_ir_initiator, echo_ir_process_seen, echo_ir_parent,
    echo_ir_finished.
  cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches eval_ir_guards
    eval_ir_expr echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    echo_ir_encode_message echo_ir_encode_kind echo_ir_delivery_certificates
    echo_ir_event_forward_order echo_ir_event_expected_parent ir_value_eqb
    ir_processes ir_config_fields ir_message_kind ir_message_receiver
    echo_ir_signature echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  rewrite request_kind.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRRequest EchoIRRequest) as [_ | impossible_kind].
  2: contradiction.
  cbn [eval_ir_guards eval_ir_expr echo_ir_encode_kind echo_ir_signature
    echo_ir_message_kind_eq_dec ir_processes ir_config_fields
    ir_message_kind ir_message_receiver echo_ir_encode_config
    echo_ir_encode_config_fields echo_ir_encode_state echo_ir_encode_process
    echo_ir_encode_message ir_value_eqb].
  unfold ir_node_eqb.
  destruct (node_eq (message_receiver message) (config_initiator config))
    as [same_receiver | different_receiver].
  - contradiction.
  - cbn.
    unfold ir_node_eqb.
    destruct (node_eq (message_receiver message)
      (config_initiator config)) as [same_again | different_again].
    + contradiction.
    + cbn.
    destruct receiver_seen as [[parent parent_some] | receiver_finished].
    * rewrite parent_some. reflexivity.
    * rewrite receiver_finished.
      destruct (process_parent
        (processes state (message_receiver message))); reflexivity.
Qed.

Lemma echo_ir_repeated_request_action_forward
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoRepeatedRequest message) successor ->
  exists ir_successor,
    eval_ir_action node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoRepeatedRequest message)))
      (ir_rule_action (@echo_ir_repeated_request_rule node)) =
        Some ir_successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intro step.
  pose proof (@EchoStep_selected_action node node_eq config
    state successor (EchoRepeatedRequest message)
    repeated_echo_rule step eq_refl) as old_action.
  unfold repeated_echo_rule in old_action.
  cbn [EchoTransitionIR.eval_action EchoTransitionIR.ir_rule_action
    EchoTransitionIR.eval_process_expr EchoTransitionIR.eval_node_expr
    EchoTransitionIR.eval_outbound_expr EchoTransitionIR.event_message]
    in old_action.
  unfold apply_echo_delivery in old_action.
  cbn in old_action. subst successor.
  unfold echo_ir_repeated_request_rule.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action echo_ir_emit_one
    echo_ir_receiver echo_ir_sender echo_ir_empty_payload
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_globals echo_ir_encode_message
    echo_ir_delivery_certificates echo_ir_event_forward_order
    echo_ir_event_expected_parent eval_ir_expr ir_remove_selected_message
    ir_emit_messages eval_ir_payload_exprs echo_ir_signature
    echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  eexists. split.
  - reflexivity.
  - unfold echo_ir_states_correspond.
    repeat split.
    + intros process field.
      cbn [ir_emit_messages ir_remove_selected_message ir_processes
        processes echo_ir_encode_process].
      destruct (node_eq (message_receiver message) process)
        as [same | different].
      * subst process. rewrite echo_update_process_same. reflexivity.
      * rewrite echo_update_process_different by exact different.
        reflexivity.
    + cbn [ir_emit_messages ir_remove_selected_message ir_message_store
        message_store echo_ir_encode_state].
      assert (encoded_id :
        ir_message_id (@echo_ir_encode_message node message) =
          message_id message) by reflexivity.
      assert (encoded_receiver :
        ir_message_receiver (@echo_ir_encode_message node message) =
          message_receiver message) by reflexivity.
      assert (encoded_sender :
        ir_message_sender (@echo_ir_encode_message node message) =
          message_sender message) by reflexivity.
      rewrite encoded_id, encoded_receiver, encoded_sender.
      rewrite List.map_app.
      rewrite echo_ir_remove_message_encoding.
      unfold ir_remove_selected_message.
      cbn [ir_next_message_id echo_ir_encode_state].
      pose proof (echo_ir_materialize_messages_encoding
        (next_message_id state) EchoReply (message_receiver message)
        [message_sender message]) as materialized.
      cbn [echo_ir_encode_kind] in materialized.
      rewrite materialized. reflexivity.
Qed.

Lemma echo_ir_first_request_nonleaf_disabled_on_repeated
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoRepeatedRequest message) successor ->
  eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoRepeatedRequest message)))
      (@echo_ir_first_request_nonleaf_rule node) = IRRuleDisabled.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoRepeatedRequest message)
    repeated_echo_rule (IRGuardKind EchoRequest)
    step eq_refl ltac:(
      cbn [repeated_echo_rule];
      repeat (first [left; reflexivity | right]))) as request_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoRepeatedRequest message)
    repeated_echo_rule
    (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [repeated_echo_rule];
      repeat (first [left; reflexivity | right]))) as receiver_not_initiator.
  cbn [guard_holds eval_node_expr event_message]
    in request_kind, receiver_not_initiator.
  unfold eval_ir_rule, echo_ir_first_request_nonleaf_rule.
  unfold echo_ir_not_equal, echo_ir_equal, echo_ir_receiver,
    echo_ir_initiator, echo_ir_process_initial, echo_ir_parent,
    echo_ir_pending, echo_ir_finished, echo_ir_option_none,
    echo_ir_empty_nodes, echo_ir_bool, echo_ir_process_seen,
    echo_ir_forward_targets, echo_ir_nonempty, echo_ir_is_empty,
    echo_ir_neighbors, echo_ir_sender, echo_ir_forward_order.
  unfold echo_ir_equal, echo_ir_parent, echo_ir_finished,
    echo_ir_remove, echo_ir_receiver.
  cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches eval_ir_guards
    eval_ir_expr echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    echo_ir_encode_message echo_ir_encode_kind echo_ir_delivery_certificates
    echo_ir_event_forward_order echo_ir_event_expected_parent ir_value_eqb
    ir_processes ir_config_fields ir_config_neighbors ir_message_kind
    ir_message_sender ir_message_receiver ir_event_message echo_ir_signature
    echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  rewrite request_kind.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRRequest EchoIRRequest) as [_ | impossible_kind].
  2: contradiction.
  cbn [List.app eval_ir_guards eval_ir_expr echo_ir_encode_kind
    echo_ir_signature echo_ir_message_kind_eq_dec ir_rule_guards
    ir_processes ir_config_fields ir_config_neighbors ir_message_kind
    ir_message_sender ir_message_receiver ir_event_message
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_message
    echo_ir_delivery_certificates echo_ir_event_forward_order
    echo_ir_local_field_type echo_ir_config_field_type
    echo_ir_delivery_certificate_field_type ir_value_eqb].
  unfold ir_node_eqb.
  destruct (node_eq (message_receiver message) (config_initiator config))
    as [same_receiver | different_receiver].
  - contradiction.
  - cbn.
    unfold ir_node_eqb, ir_option_node_eqb, ir_node_list_eqb.
    destruct (node_eq (message_receiver message)
      (config_initiator config)) as [same_again | different_again].
    + contradiction.
    + destruct (process_parent
        (processes state (message_receiver message)));
      destruct (process_pending
        (processes state (message_receiver message)));
      destruct (process_finished
        (processes state (message_receiver message)));
      destruct (ir_remove_node node_eq (message_sender message)
        (nbrs (config_nodes config) (config_adjacent config)
          (message_receiver message)));
      reflexivity.
Qed.

Lemma echo_ir_first_request_leaf_disabled_on_repeated
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoRepeatedRequest message) successor ->
  eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoRepeatedRequest message)))
      (@echo_ir_first_request_leaf_rule node) = IRRuleDisabled.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoRepeatedRequest message)
    repeated_echo_rule (IRGuardKind EchoRequest)
    step eq_refl ltac:(
      cbn [repeated_echo_rule];
      repeat (first [left; reflexivity | right]))) as request_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoRepeatedRequest message)
    repeated_echo_rule
    (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [repeated_echo_rule];
      repeat (first [left; reflexivity | right]))) as receiver_not_initiator.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoRepeatedRequest message)
    repeated_echo_rule
    (IRGuardHasParentOrFinished IRMessageReceiver)
    step eq_refl ltac:(
      cbn [repeated_echo_rule];
      repeat (first [left; reflexivity | right]))) as receiver_seen.
  cbn [guard_holds eval_node_expr event_message]
    in request_kind, receiver_not_initiator, receiver_seen.
  unfold eval_ir_rule, echo_ir_first_request_leaf_rule.
  unfold echo_ir_not_equal, echo_ir_equal, echo_ir_receiver,
    echo_ir_initiator, echo_ir_process_initial, echo_ir_parent,
    echo_ir_pending, echo_ir_finished, echo_ir_option_none,
    echo_ir_empty_nodes, echo_ir_bool, echo_ir_process_seen,
    echo_ir_forward_targets, echo_ir_is_empty, echo_ir_neighbors,
    echo_ir_sender.
  unfold echo_ir_equal, echo_ir_parent, echo_ir_finished,
    echo_ir_remove, echo_ir_receiver.
  cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches eval_ir_guards
    eval_ir_expr echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    echo_ir_encode_message echo_ir_encode_kind echo_ir_delivery_certificates
    echo_ir_event_forward_order echo_ir_event_expected_parent ir_value_eqb
    ir_processes ir_config_fields ir_config_neighbors ir_message_kind
    ir_message_sender ir_message_receiver ir_event_message echo_ir_signature
    echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  rewrite request_kind.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRRequest EchoIRRequest) as [_ | impossible_kind].
  2: contradiction.
  cbn [List.app eval_ir_guards eval_ir_expr echo_ir_encode_kind
    echo_ir_signature echo_ir_message_kind_eq_dec ir_rule_guards
    ir_processes ir_config_fields ir_config_neighbors ir_message_kind
    ir_message_sender ir_message_receiver ir_event_message
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_message
    echo_ir_delivery_certificates echo_ir_event_forward_order
    echo_ir_local_field_type echo_ir_config_field_type
    echo_ir_delivery_certificate_field_type ir_value_eqb].
  unfold ir_node_eqb.
  destruct (node_eq (message_receiver message) (config_initiator config))
    as [same_receiver | different_receiver].
  - contradiction.
  - cbn.
    unfold ir_node_eqb, ir_option_node_eqb, ir_node_list_eqb.
    destruct (node_eq (message_receiver message)
      (config_initiator config)) as [same_again | different_again].
    + contradiction.
    + destruct receiver_seen as [[parent parent_some] | receiver_finished].
      * rewrite parent_some. reflexivity.
      * rewrite receiver_finished.
        destruct (process_parent
          (processes state (message_receiver message))) as [parent |].
        -- reflexivity.
        -- destruct (process_pending
            (processes state (message_receiver message)));
             reflexivity.
Qed.

Lemma echo_ir_repeated_request_tail_selects_none
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoRepeatedRequest message) successor ->
  select_ir_rule node_eq (echo_ir_encode_config config)
    (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message)
      (@echo_ir_delivery_certificates node config
        (EchoRepeatedRequest message)))
    [@echo_ir_initiator_request_rule node;
     @echo_ir_participant_reply_more_rule node;
     @echo_ir_participant_reply_final_rule node;
     @echo_ir_initiator_reply_more_rule node;
     @echo_ir_initiator_reply_final_rule node] =
  IRNoRuleSelected.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoRepeatedRequest message)
    repeated_echo_rule (IRGuardKind EchoRequest)
    step eq_refl ltac:(
      cbn [repeated_echo_rule];
      repeat (first [left; reflexivity | right]))) as request_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoRepeatedRequest message)
    repeated_echo_rule
    (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [repeated_echo_rule];
      repeat (first [left; reflexivity | right]))) as receiver_not_initiator.
  cbn [guard_holds eval_node_expr event_message]
    in request_kind, receiver_not_initiator.
  unfold echo_ir_encode_message.
  rewrite request_kind.
  unfold echo_ir_initiator_request_rule,
    echo_ir_participant_reply_more_rule,
    echo_ir_participant_reply_final_rule,
    echo_ir_initiator_reply_more_rule, echo_ir_initiator_reply_final_rule.
  unfold echo_ir_equal, echo_ir_receiver, echo_ir_initiator,
    echo_ir_started, echo_ir_finished, echo_ir_bool,
    echo_ir_parent, echo_ir_option_none, echo_ir_some,
    echo_ir_expected_parent, echo_ir_pending, echo_ir_removed_pending,
    echo_ir_sender, echo_ir_is_empty, echo_ir_empty_nodes.
  unfold echo_ir_equal, echo_ir_parent, echo_ir_pending, echo_ir_finished,
    echo_ir_remove, echo_ir_receiver.
  cbn [List.app select_ir_rule eval_ir_rule ir_rule_pattern ir_rule_guards
    ir_event_pattern_matches eval_ir_guards eval_ir_expr
    echo_ir_encode_kind echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_message
    echo_ir_delivery_certificates echo_ir_event_forward_order
    echo_ir_event_expected_parent ir_value_eqb ir_processes ir_global_fields
    ir_config_fields ir_config_neighbors ir_message_kind ir_message_sender
    ir_message_receiver ir_event_message echo_ir_signature
    echo_ir_message_kind_eq_dec echo_ir_local_field_type
    echo_ir_global_field_type echo_ir_config_field_type
    echo_ir_delivery_certificate_field_type].
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRRequest EchoIRRequest) as [_ | impossible_kind].
  2: contradiction.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRReply EchoIRRequest) as [impossible_kind | _].
  1: discriminate.
  cbn [select_ir_rule eval_ir_rule ir_event_pattern_matches eval_ir_guards
    eval_ir_expr echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process ir_value_eqb ir_processes
    ir_global_fields ir_config_fields ir_config_neighbors ir_message_sender
    ir_message_receiver ir_event_message echo_ir_signature
    echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type].
  unfold ir_node_eqb.
  destruct (node_eq (message_receiver message)
    (config_initiator config)) as [same_node | different_nodes].
  - contradiction.
  - cbn.
    unfold ir_node_eqb.
    destruct (node_eq (message_receiver message)
      (config_initiator config)) as [same_again | different_again].
    + contradiction.
    + reflexivity.
Qed.

Lemma echo_ir_repeated_request_rule_selected
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoRepeatedRequest message) successor ->
  select_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoRepeatedRequest message)))
      (@echo_ir_rules node) =
    IRUniqueRuleSelected (@echo_ir_repeated_request_rule node).
Proof.
  intro step.
  pose proof (echo_ir_repeated_request_rule_enabled
    state successor message step) as enabled.
  pose proof (echo_ir_first_request_nonleaf_disabled_on_repeated
    state successor message step) as nonleaf_disabled.
  pose proof (echo_ir_first_request_leaf_disabled_on_repeated
    state successor message step) as leaf_disabled.
  pose proof (echo_ir_repeated_request_tail_selects_none
    state successor message step) as tail_none.
  assert (start_mismatch :
    eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoRepeatedRequest message)))
      (@echo_ir_start_rule node) = IRRuleMismatch).
  {
    unfold eval_ir_rule, echo_ir_start_rule.
    reflexivity.
  }
  unfold echo_ir_rules.
  erewrite select_ir_rule_cons_mismatch; [| exact start_mismatch].
  erewrite select_ir_rule_cons_disabled; [| exact nonleaf_disabled].
  erewrite select_ir_rule_cons_disabled; [| exact leaf_disabled].
  now apply select_ir_rule_cons_unique.
Qed.

Theorem echo_ir_repeated_request_forward_simulates
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @echo_reachable node node_eq config state ->
  @EchoStep node node_eq config state
      (EchoRepeatedRequest message) successor ->
  exists ir_successor,
    interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state)
      (echo_ir_encode_event config (EchoRepeatedRequest message)) =
      @IRStepSuccess node echo_ir_signature
        EchoIRRepeatedRequestRule ir_successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intros reachable step.
  pose proof (@echo_ir_resolve_successful_delivery
    node node_eq config state successor (EchoRepeatedRequest message)
    reachable step I) as resolved.
  pose proof (echo_ir_repeated_request_rule_selected
    state successor message step) as selected.
  destruct (echo_ir_repeated_request_action_forward
    state successor message step) as
    [ir_successor [action correspondence]].
  exists ir_successor. split.
  - unfold interpret_protocol_rules.
    rewrite resolved.
    cbn [event_message].
    rewrite selected, action. reflexivity.
  - exact correspondence.
Qed.

Lemma echo_ir_initiator_request_rule_enabled
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoInitiatorRequest message) successor ->
  eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoInitiatorRequest message)))
      (@echo_ir_initiator_request_rule node) = IRRuleEnabled.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorRequest message)
    initiator_echo_rule (IRGuardKind EchoRequest)
    step eq_refl ltac:(
      cbn [initiator_echo_rule];
      repeat (first [left; reflexivity | right]))) as request_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorRequest message)
    initiator_echo_rule
    (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [initiator_echo_rule];
      repeat (first [left; reflexivity | right]))) as receiver_is_initiator.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorRequest message)
    initiator_echo_rule (IRGuardStarted true)
    step eq_refl ltac:(
      cbn [initiator_echo_rule];
      repeat (first [left; reflexivity | right]))) as protocol_started.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorRequest message)
    initiator_echo_rule (IRGuardFinished IRInitiatorNode false)
    step eq_refl ltac:(
      cbn [initiator_echo_rule];
      repeat (first [left; reflexivity | right]))) as initiator_unfinished.
  cbn [guard_holds eval_node_expr event_message]
    in request_kind, receiver_is_initiator, protocol_started,
      initiator_unfinished.
  unfold eval_ir_rule, echo_ir_initiator_request_rule.
  unfold echo_ir_equal, echo_ir_receiver, echo_ir_initiator,
    echo_ir_started, echo_ir_finished, echo_ir_bool.
  cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches eval_ir_guards
    eval_ir_expr echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    echo_ir_encode_message echo_ir_encode_kind echo_ir_delivery_certificates
    echo_ir_event_forward_order echo_ir_event_expected_parent ir_value_eqb
    ir_processes ir_global_fields ir_config_fields ir_message_kind
    ir_message_receiver echo_ir_signature echo_ir_local_field_type
    echo_ir_global_field_type echo_ir_config_field_type
    echo_ir_delivery_certificate_field_type].
  rewrite request_kind.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRRequest EchoIRRequest) as [_ | impossible_kind].
  2: contradiction.
  cbn [eval_ir_guards eval_ir_expr echo_ir_encode_kind echo_ir_signature
    echo_ir_message_kind_eq_dec ir_processes ir_global_fields
    ir_config_fields ir_message_kind ir_message_receiver
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_globals echo_ir_encode_message
    ir_value_eqb].
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRRequest EchoIRRequest) as [_ | impossible_again].
  2: contradiction.
  cbn [ir_event_message echo_ir_encode_message ir_message_receiver
    ir_value_eqb echo_ir_encode_config echo_ir_encode_config_fields
    ir_config_fields echo_ir_encode_state echo_ir_encode_process
    ir_processes echo_ir_encode_globals ir_global_fields].
  rewrite receiver_is_initiator, protocol_started, initiator_unfinished.
  unfold ir_node_eqb.
  destruct (node_eq (config_initiator config) (config_initiator config))
    as [_ | impossible_same].
  - reflexivity.
  - contradiction.
Qed.

Lemma echo_ir_initiator_request_action_forward
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoInitiatorRequest message) successor ->
  exists ir_successor,
    eval_ir_action node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoInitiatorRequest message)))
      (ir_rule_action (@echo_ir_initiator_request_rule node)) =
        Some ir_successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorRequest message)
    initiator_echo_rule
    (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [initiator_echo_rule];
      repeat (first [left; reflexivity | right]))) as receiver_is_initiator.
  cbn [guard_holds eval_node_expr event_message] in receiver_is_initiator.
  pose proof (@EchoStep_selected_action node node_eq config
    state successor (EchoInitiatorRequest message)
    initiator_echo_rule step eq_refl) as old_action.
  unfold initiator_echo_rule in old_action.
  cbn [EchoTransitionIR.eval_action EchoTransitionIR.ir_rule_action
    EchoTransitionIR.eval_process_expr EchoTransitionIR.eval_node_expr
    EchoTransitionIR.eval_outbound_expr EchoTransitionIR.event_message]
    in old_action.
  unfold apply_echo_delivery in old_action.
  cbn in old_action.
  rewrite receiver_is_initiator in old_action.
  subst successor.
  unfold echo_ir_initiator_request_rule.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action echo_ir_emit_one
    echo_ir_initiator echo_ir_sender echo_ir_empty_payload
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_globals echo_ir_encode_message
    echo_ir_delivery_certificates echo_ir_event_forward_order
    echo_ir_event_expected_parent eval_ir_expr ir_remove_selected_message
    ir_emit_messages eval_ir_payload_exprs echo_ir_signature
    echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  eexists. split.
  - reflexivity.
  - unfold echo_ir_states_correspond.
    repeat split.
    + intros process field.
      cbn [ir_emit_messages ir_remove_selected_message ir_processes
        processes echo_ir_encode_process].
      destruct (node_eq (config_initiator config) process)
        as [same | different].
      * subst process. rewrite echo_update_process_same. reflexivity.
      * rewrite echo_update_process_different by exact different.
        reflexivity.
    + cbn [ir_emit_messages ir_remove_selected_message ir_message_store
        message_store echo_ir_encode_state].
      assert (encoded_id :
        ir_message_id (@echo_ir_encode_message node message) =
          message_id message) by reflexivity.
      assert (encoded_sender :
        ir_message_sender (@echo_ir_encode_message node message) =
          message_sender message) by reflexivity.
      rewrite encoded_id, encoded_sender.
      rewrite List.map_app.
      rewrite echo_ir_remove_message_encoding.
      unfold ir_remove_selected_message.
      cbn [ir_next_message_id echo_ir_encode_state].
      pose proof (echo_ir_materialize_messages_encoding
        (next_message_id state) EchoReply (config_initiator config)
        [message_sender message]) as materialized.
      cbn [echo_ir_encode_kind] in materialized.
      rewrite materialized. reflexivity.
Qed.

Lemma echo_ir_participant_request_prefix_selects_none_on_initiator
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoInitiatorRequest message) successor ->
  select_ir_rule node_eq (echo_ir_encode_config config)
    (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message)
      (@echo_ir_delivery_certificates node config
        (EchoInitiatorRequest message)))
    [@echo_ir_first_request_nonleaf_rule node;
     @echo_ir_first_request_leaf_rule node;
     @echo_ir_repeated_request_rule node] =
  IRNoRuleSelected.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorRequest message)
    initiator_echo_rule (IRGuardKind EchoRequest)
    step eq_refl ltac:(
      cbn [initiator_echo_rule];
      repeat (first [left; reflexivity | right]))) as request_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorRequest message)
    initiator_echo_rule
    (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [initiator_echo_rule];
      repeat (first [left; reflexivity | right]))) as receiver_is_initiator.
  cbn [guard_holds eval_node_expr event_message]
    in request_kind, receiver_is_initiator.
  assert (nonleaf_disabled :
    eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoInitiatorRequest message)))
      (@echo_ir_first_request_nonleaf_rule node) = IRRuleDisabled).
  {
    unfold eval_ir_rule, echo_ir_first_request_nonleaf_rule.
    unfold echo_ir_not_equal, echo_ir_equal, echo_ir_receiver,
      echo_ir_initiator.
    cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches
      eval_ir_guards eval_ir_expr echo_ir_encode_config
      echo_ir_encode_config_fields echo_ir_encode_state
      echo_ir_encode_process echo_ir_encode_message echo_ir_encode_kind
      ir_value_eqb ir_config_fields ir_message_kind ir_message_receiver
      ir_event_message echo_ir_signature echo_ir_local_field_type
      echo_ir_config_field_type].
    rewrite request_kind.
    destruct (signature_message_kind_eq_dec echo_ir_signature
      EchoIRRequest EchoIRRequest) as [_ | impossible_kind].
    2: contradiction.
    cbn [eval_ir_guards eval_ir_expr echo_ir_encode_message
      ir_event_message ir_message_receiver echo_ir_encode_config
      echo_ir_encode_config_fields ir_config_fields ir_value_eqb].
    destruct (signature_message_kind_eq_dec echo_ir_signature
      EchoIRRequest EchoIRRequest) as [_ | impossible_again].
    2: contradiction.
    cbn [eval_ir_guards eval_ir_expr echo_ir_encode_message
      ir_event_message ir_message_receiver echo_ir_encode_config
      echo_ir_encode_config_fields ir_config_fields ir_value_eqb].
    cbn [echo_ir_encode_kind].
    destruct (signature_message_kind_eq_dec echo_ir_signature
      EchoIRRequest EchoIRRequest) as [_ | impossible_final].
    2: contradiction.
    cbn [List.app eval_ir_guards eval_ir_expr echo_ir_encode_message
      ir_event_message ir_message_receiver echo_ir_encode_config
      echo_ir_encode_config_fields ir_config_fields ir_value_eqb].
    rewrite receiver_is_initiator.
    unfold ir_node_eqb.
    destruct (node_eq (config_initiator config) (config_initiator config));
      [reflexivity | contradiction].
  }
  assert (leaf_disabled :
    eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoInitiatorRequest message)))
      (@echo_ir_first_request_leaf_rule node) = IRRuleDisabled).
  {
    unfold eval_ir_rule, echo_ir_first_request_leaf_rule.
    unfold echo_ir_not_equal, echo_ir_equal, echo_ir_receiver,
      echo_ir_initiator.
    cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches
      eval_ir_guards eval_ir_expr echo_ir_encode_config
      echo_ir_encode_config_fields echo_ir_encode_state
      echo_ir_encode_process echo_ir_encode_message echo_ir_encode_kind
      ir_value_eqb ir_config_fields ir_message_kind ir_message_receiver
      ir_event_message echo_ir_signature echo_ir_local_field_type
      echo_ir_config_field_type].
    rewrite request_kind.
    destruct (signature_message_kind_eq_dec echo_ir_signature
      EchoIRRequest EchoIRRequest) as [_ | impossible_kind].
    2: contradiction.
    cbn [eval_ir_guards eval_ir_expr echo_ir_encode_message
      ir_event_message ir_message_receiver echo_ir_encode_config
      echo_ir_encode_config_fields ir_config_fields ir_value_eqb].
    destruct (signature_message_kind_eq_dec echo_ir_signature
      EchoIRRequest EchoIRRequest) as [_ | impossible_again].
    2: contradiction.
    cbn [eval_ir_guards eval_ir_expr echo_ir_encode_message
      ir_event_message ir_message_receiver echo_ir_encode_config
      echo_ir_encode_config_fields ir_config_fields ir_value_eqb].
    cbn [echo_ir_encode_kind].
    destruct (signature_message_kind_eq_dec echo_ir_signature
      EchoIRRequest EchoIRRequest) as [_ | impossible_final].
    2: contradiction.
    cbn [List.app eval_ir_guards eval_ir_expr echo_ir_encode_message
      ir_event_message ir_message_receiver echo_ir_encode_config
      echo_ir_encode_config_fields ir_config_fields ir_value_eqb].
    rewrite receiver_is_initiator.
    unfold ir_node_eqb.
    destruct (node_eq (config_initiator config) (config_initiator config));
      [reflexivity | contradiction].
  }
  assert (repeated_disabled :
    eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoInitiatorRequest message)))
      (@echo_ir_repeated_request_rule node) = IRRuleDisabled).
  {
    unfold eval_ir_rule, echo_ir_repeated_request_rule.
    unfold echo_ir_not_equal, echo_ir_equal, echo_ir_receiver,
      echo_ir_initiator.
    cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches
      eval_ir_guards eval_ir_expr echo_ir_encode_config
      echo_ir_encode_config_fields echo_ir_encode_state
      echo_ir_encode_process echo_ir_encode_message echo_ir_encode_kind
      ir_value_eqb ir_config_fields ir_message_kind ir_message_receiver
      ir_event_message echo_ir_signature echo_ir_local_field_type
      echo_ir_config_field_type].
    rewrite request_kind.
    destruct (signature_message_kind_eq_dec echo_ir_signature
      EchoIRRequest EchoIRRequest) as [_ | impossible_kind].
    2: contradiction.
    cbn [eval_ir_guards eval_ir_expr echo_ir_encode_message
      ir_event_message ir_message_receiver echo_ir_encode_config
      echo_ir_encode_config_fields ir_config_fields ir_value_eqb].
    destruct (signature_message_kind_eq_dec echo_ir_signature
      EchoIRRequest EchoIRRequest) as [_ | impossible_again].
    2: contradiction.
    cbn [eval_ir_guards eval_ir_expr echo_ir_encode_message
      ir_event_message ir_message_receiver echo_ir_encode_config
      echo_ir_encode_config_fields ir_config_fields ir_value_eqb].
    cbn [echo_ir_encode_kind].
    destruct (signature_message_kind_eq_dec echo_ir_signature
      EchoIRRequest EchoIRRequest) as [_ | impossible_final].
    2: contradiction.
    cbn [List.app eval_ir_guards eval_ir_expr echo_ir_encode_message
      ir_event_message ir_message_receiver echo_ir_encode_config
      echo_ir_encode_config_fields ir_config_fields ir_value_eqb].
    rewrite receiver_is_initiator.
    unfold ir_node_eqb.
    destruct (node_eq (config_initiator config) (config_initiator config));
      [reflexivity | contradiction].
  }
  cbn [select_ir_rule].
  rewrite nonleaf_disabled, leaf_disabled, repeated_disabled.
  reflexivity.
Qed.

Lemma echo_ir_initiator_request_tail_selects_none
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoInitiatorRequest message) successor ->
  select_ir_rule node_eq (echo_ir_encode_config config)
    (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message)
      (@echo_ir_delivery_certificates node config
        (EchoInitiatorRequest message)))
    [@echo_ir_participant_reply_more_rule node;
     @echo_ir_participant_reply_final_rule node;
     @echo_ir_initiator_reply_more_rule node;
     @echo_ir_initiator_reply_final_rule node] =
  IRNoRuleSelected.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorRequest message)
    initiator_echo_rule (IRGuardKind EchoRequest)
    step eq_refl ltac:(
      cbn [initiator_echo_rule];
      repeat (first [left; reflexivity | right]))) as request_kind.
  cbn [guard_holds event_message] in request_kind.
  unfold echo_ir_encode_message.
  rewrite request_kind.
  cbn [select_ir_rule eval_ir_rule ir_rule_pattern ir_event_pattern_matches
    echo_ir_participant_reply_more_rule
    echo_ir_participant_reply_final_rule
    echo_ir_initiator_reply_more_rule echo_ir_initiator_reply_final_rule
    echo_ir_encode_kind echo_ir_signature].
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRReply EchoIRRequest) as [impossible_kind | _].
  - discriminate.
  - reflexivity.
Qed.

Lemma echo_ir_initiator_request_rule_selected
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoInitiatorRequest message) successor ->
  select_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoInitiatorRequest message)))
      (@echo_ir_rules node) =
    IRUniqueRuleSelected (@echo_ir_initiator_request_rule node).
Proof.
  intro step.
  pose proof (echo_ir_initiator_request_rule_enabled
    state successor message step) as enabled.
  pose proof (echo_ir_participant_request_prefix_selects_none_on_initiator
    state successor message step) as prefix_none.
  pose proof (echo_ir_initiator_request_tail_selects_none
    state successor message step) as tail_none.
  assert (start_mismatch :
    eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoInitiatorRequest message)))
      (@echo_ir_start_rule node) = IRRuleMismatch).
  {
    unfold eval_ir_rule, echo_ir_start_rule.
    reflexivity.
  }
  unfold echo_ir_rules.
  erewrite select_ir_rule_cons_mismatch; [| exact start_mismatch].
  change
    (select_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoInitiatorRequest message)))
      ([@echo_ir_first_request_nonleaf_rule node;
        @echo_ir_first_request_leaf_rule node;
        @echo_ir_repeated_request_rule node] ++
       (@echo_ir_initiator_request_rule node ::
        [@echo_ir_participant_reply_more_rule node;
         @echo_ir_participant_reply_final_rule node;
         @echo_ir_initiator_reply_more_rule node;
         @echo_ir_initiator_reply_final_rule node])) =
     IRUniqueRuleSelected (@echo_ir_initiator_request_rule node)).
  erewrite select_ir_rule_app_none; [| exact prefix_none].
  now apply select_ir_rule_cons_unique.
Qed.

Theorem echo_ir_initiator_request_forward_simulates
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @echo_reachable node node_eq config state ->
  @EchoStep node node_eq config state
      (EchoInitiatorRequest message) successor ->
  exists ir_successor,
    interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state)
      (echo_ir_encode_event config (EchoInitiatorRequest message)) =
      @IRStepSuccess node echo_ir_signature
        EchoIRInitiatorRequestRule ir_successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intros reachable step.
  pose proof (@echo_ir_resolve_successful_delivery
    node node_eq config state successor (EchoInitiatorRequest message)
    reachable step I) as resolved.
  pose proof (echo_ir_initiator_request_rule_selected
    state successor message step) as selected.
  destruct (echo_ir_initiator_request_action_forward
    state successor message step) as
    [ir_successor [action correspondence]].
  exists ir_successor. split.
  - unfold interpret_protocol_rules.
    rewrite resolved.
    cbn [event_message].
    rewrite selected, action. reflexivity.
  - exact correspondence.
Qed.

(** Request-pattern rules uniformly mismatch a delivered reply, independently
    of the reply certificates.  All four reply branches reuse this prefix. *)
Lemma echo_ir_request_rules_select_none_on_reply
    (state : @executable_echo_state node)
    (message : @echo_message node)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  message_kind message = EchoReply ->
  select_ir_rule node_eq (echo_ir_encode_config config)
    (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    [@echo_ir_first_request_nonleaf_rule node;
     @echo_ir_first_request_leaf_rule node;
     @echo_ir_repeated_request_rule node;
     @echo_ir_initiator_request_rule node] =
  IRNoRuleSelected.
Proof.
  intro reply_kind.
  unfold echo_ir_encode_message.
  rewrite reply_kind.
  cbn [select_ir_rule eval_ir_rule ir_rule_pattern ir_event_pattern_matches
    echo_ir_first_request_nonleaf_rule echo_ir_first_request_leaf_rule
    echo_ir_repeated_request_rule echo_ir_initiator_request_rule
    echo_ir_encode_kind echo_ir_signature].
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRRequest EchoIRReply) as [impossible_kind | _].
  - discriminate.
  - reflexivity.
Qed.

Lemma echo_ir_participant_reply_more_rule_enabled
    (state successor : @executable_echo_state node)
    (message : @echo_message node)
    (parent : node) :
  @EchoStep node node_eq config state
      (EchoParticipantReplyMore message parent) successor ->
  eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoParticipantReplyMore message parent)))
      (@echo_ir_participant_reply_more_rule node) = IRRuleEnabled.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyMore message parent)
    participant_ack_more_rule (IRGuardKind EchoReply)
    step eq_refl ltac:(
      cbn [participant_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as reply_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyMore message parent)
    participant_ack_more_rule
    (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [participant_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as receiver_not_initiator.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyMore message parent)
    participant_ack_more_rule
    (IRGuardParentEqual IRMessageReceiver (IRSomeParent IREventParent))
    step eq_refl ltac:(
      cbn [participant_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as parent_matches.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyMore message parent)
    participant_ack_more_rule
    (IRGuardNodeIn IRMessageSender (IRNodesPending IRMessageReceiver))
    step eq_refl ltac:(
      cbn [participant_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as sender_pending.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyMore message parent)
    participant_ack_more_rule
    (IRGuardNodesNonempty
      (IRNodesRemove IRMessageSender (IRNodesPending IRMessageReceiver)))
    step eq_refl ltac:(
      cbn [participant_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as pending_remains.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyMore message parent)
    participant_ack_more_rule
    (IRGuardFinished IRMessageReceiver false)
    step eq_refl ltac:(
      cbn [participant_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as receiver_unfinished.
  cbn [guard_holds eval_node_expr eval_parent_expr eval_nodes_expr
    event_message event_parent] in reply_kind, receiver_not_initiator,
    parent_matches, sender_pending, pending_remains, receiver_unfinished.
  rewrite <- echo_ir_remove_node_agrees in pending_remains.
  pose proof (echo_ir_node_in_true_of_in
    (message_sender message)
    (process_pending (processes state (message_receiver message)))
    sender_pending) as sender_pending_true.
  unfold eval_ir_rule, echo_ir_participant_reply_more_rule.
  unfold echo_ir_not_equal, echo_ir_equal, echo_ir_receiver,
    echo_ir_initiator, echo_ir_parent, echo_ir_some,
    echo_ir_expected_parent, echo_ir_sender, echo_ir_pending,
    echo_ir_nonempty, echo_ir_is_empty, echo_ir_removed_pending,
    echo_ir_finished, echo_ir_bool, echo_ir_remove.
  cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches eval_ir_guards
    eval_ir_expr echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    echo_ir_encode_message echo_ir_encode_kind echo_ir_delivery_certificates
    echo_ir_event_forward_order echo_ir_event_expected_parent ir_value_eqb
    ir_processes ir_config_fields ir_config_neighbors ir_message_kind
    ir_message_sender ir_message_receiver ir_event_message echo_ir_signature
    echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  rewrite reply_kind.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRReply EchoIRReply) as [_ | impossible_kind].
  2: contradiction.
  cbn [eval_ir_guards eval_ir_expr echo_ir_encode_kind echo_ir_signature
    echo_ir_message_kind_eq_dec ir_processes ir_config_fields
    ir_message_kind ir_message_sender ir_message_receiver ir_event_message
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_message
    echo_ir_delivery_certificates echo_ir_event_expected_parent ir_value_eqb].
  unfold ir_node_eqb.
  destruct (node_eq (message_receiver message) (config_initiator config))
    as [same_receiver | different_receiver].
  - contradiction.
  - cbn.
    unfold ir_node_eqb, ir_option_node_eqb.
    rewrite parent_matches, sender_pending_true, receiver_unfinished.
    destruct (node_eq parent parent) as [_ | impossible_parent].
    + destruct (ir_remove_node node_eq (message_sender message)
        (process_pending (processes state (message_receiver message))))
        as [|remaining rest] eqn:pending_shape.
      * contradiction.
      * unfold ir_node_eqb.
        destruct (node_eq parent parent) as [_ | impossible_again].
        -- reflexivity.
        -- contradiction.
    + contradiction.
Qed.

Lemma echo_ir_participant_reply_more_action_forward
    (state successor : @executable_echo_state node)
    (message : @echo_message node)
    (parent : node) :
  @EchoStep node node_eq config state
      (EchoParticipantReplyMore message parent) successor ->
  exists ir_successor,
    eval_ir_action node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoParticipantReplyMore message parent)))
      (ir_rule_action (@echo_ir_participant_reply_more_rule node)) =
        Some ir_successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intro step.
  pose proof (@EchoStep_selected_action node node_eq config
    state successor (EchoParticipantReplyMore message parent)
    participant_ack_more_rule step eq_refl) as old_action.
  unfold participant_ack_more_rule in old_action.
  cbn [EchoTransitionIR.eval_action EchoTransitionIR.ir_rule_action
    EchoTransitionIR.eval_process_expr EchoTransitionIR.eval_parent_expr
    EchoTransitionIR.eval_nodes_expr EchoTransitionIR.eval_node_expr
    EchoTransitionIR.eval_outbound_expr EchoTransitionIR.event_message
    EchoTransitionIR.event_parent] in old_action.
  unfold apply_echo_delivery in old_action.
  cbn in old_action. subst successor.
  unfold echo_ir_participant_reply_more_rule.
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
    echo_ir_local_field_type
    echo_ir_global_field_type echo_ir_config_field_type
    echo_ir_delivery_certificate_field_type].
  rewrite ir_set_local_field_read_different by discriminate.
  cbn [eval_ir_action ir_set_local_field ir_remove_selected_message].
  eexists. split.
  - reflexivity.
  - unfold echo_ir_states_correspond.
    repeat split.
    + intros process field.
      cbn [ir_remove_selected_message ir_processes processes].
      destruct (node_eq (message_receiver message) process)
        as [same | different].
      * subst process.
        rewrite echo_update_process_same.
        destruct field.
        -- cbn [ir_set_local_field ir_processes processes
             echo_ir_encode_process].
           repeat rewrite ir_update_processes_same.
           rewrite ir_update_field_different by discriminate.
           rewrite ir_update_field_different by discriminate.
           rewrite ir_update_field_same. reflexivity.
        -- cbn [ir_set_local_field ir_processes processes
             echo_ir_encode_process].
           repeat rewrite ir_update_processes_same.
           rewrite ir_update_field_different by discriminate.
           rewrite ir_update_field_same.
           rewrite echo_ir_remove_node_agrees. reflexivity.
        -- cbn [ir_set_local_field ir_processes processes
             echo_ir_encode_process].
           rewrite ir_update_processes_same.
           rewrite ir_update_field_same. reflexivity.
      * rewrite echo_update_process_different by exact different.
        cbn [ir_set_local_field ir_processes processes
          echo_ir_encode_process].
        repeat rewrite ir_update_processes_different by exact different.
        reflexivity.
    + cbn [ir_remove_selected_message ir_message_store message_store
        echo_ir_encode_state ir_set_local_field].
      rewrite echo_ir_remove_message_encoding.
      now rewrite app_nil_r.
    + cbn [ir_remove_selected_message ir_set_local_field
        ir_next_message_id next_message_id next_echo_message_id_after
        echo_ir_encode_state].
      unfold next_echo_message_id_after.
      now rewrite Nat.add_0_r.
Qed.

Lemma echo_ir_participant_reply_final_disabled_on_more
    (state successor : @executable_echo_state node)
    (message : @echo_message node)
    (parent : node) :
  @EchoStep node node_eq config state
      (EchoParticipantReplyMore message parent) successor ->
  eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoParticipantReplyMore message parent)))
      (@echo_ir_participant_reply_final_rule node) = IRRuleDisabled.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyMore message parent)
    participant_ack_more_rule (IRGuardKind EchoReply)
    step eq_refl ltac:(
      cbn [participant_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as reply_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyMore message parent)
    participant_ack_more_rule
    (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [participant_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as receiver_not_initiator.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyMore message parent)
    participant_ack_more_rule
    (IRGuardParentEqual IRMessageReceiver (IRSomeParent IREventParent))
    step eq_refl ltac:(
      cbn [participant_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as parent_matches.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyMore message parent)
    participant_ack_more_rule
    (IRGuardNodeIn IRMessageSender (IRNodesPending IRMessageReceiver))
    step eq_refl ltac:(
      cbn [participant_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as sender_pending.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyMore message parent)
    participant_ack_more_rule
    (IRGuardNodesNonempty
      (IRNodesRemove IRMessageSender (IRNodesPending IRMessageReceiver)))
    step eq_refl ltac:(
      cbn [participant_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as pending_remains.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyMore message parent)
    participant_ack_more_rule
    (IRGuardFinished IRMessageReceiver false)
    step eq_refl ltac:(
      cbn [participant_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as receiver_unfinished.
  cbn [guard_holds eval_node_expr eval_parent_expr eval_nodes_expr
    event_message event_parent] in reply_kind, receiver_not_initiator,
    parent_matches, sender_pending, pending_remains, receiver_unfinished.
  rewrite <- echo_ir_remove_node_agrees in pending_remains.
  pose proof (echo_ir_node_in_true_of_in
    (message_sender message)
    (process_pending (processes state (message_receiver message)))
    sender_pending) as sender_pending_true.
  unfold eval_ir_rule, echo_ir_participant_reply_final_rule.
  unfold echo_ir_not_equal, echo_ir_equal, echo_ir_receiver,
    echo_ir_initiator, echo_ir_parent, echo_ir_some,
    echo_ir_expected_parent, echo_ir_sender, echo_ir_pending,
    echo_ir_is_empty, echo_ir_removed_pending, echo_ir_finished,
    echo_ir_bool, echo_ir_remove.
  cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches eval_ir_guards
    eval_ir_expr echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    echo_ir_encode_message echo_ir_encode_kind echo_ir_delivery_certificates
    echo_ir_event_forward_order echo_ir_event_expected_parent ir_value_eqb
    ir_processes ir_config_fields ir_config_neighbors ir_message_kind
    ir_message_sender ir_message_receiver ir_event_message echo_ir_signature
    echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  rewrite reply_kind.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRReply EchoIRReply) as [_ | impossible_kind].
  2: contradiction.
  cbn [eval_ir_guards eval_ir_expr echo_ir_encode_kind echo_ir_signature
    echo_ir_message_kind_eq_dec ir_processes ir_config_fields
    ir_message_kind ir_message_sender ir_message_receiver ir_event_message
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_message
    echo_ir_delivery_certificates echo_ir_event_expected_parent ir_value_eqb].
  unfold ir_node_eqb.
  destruct (node_eq (message_receiver message) (config_initiator config))
    as [same_receiver | different_receiver].
  - contradiction.
  - cbn.
    unfold ir_node_eqb, ir_option_node_eqb.
    rewrite parent_matches, sender_pending_true, receiver_unfinished.
    destruct (node_eq parent parent) as [_ | impossible_parent].
    + destruct (ir_remove_node node_eq (message_sender message)
        (process_pending (processes state (message_receiver message))))
        as [|remaining rest] eqn:pending_shape.
      * contradiction.
      * unfold ir_node_eqb.
        destruct (node_eq parent parent) as [_ | impossible_again].
        -- reflexivity.
        -- contradiction.
    + contradiction.
Qed.

Lemma echo_ir_initiator_reply_more_disabled_on_participant_more
    (state successor : @executable_echo_state node)
    (message : @echo_message node)
    (parent : node) :
  @EchoStep node node_eq config state
      (EchoParticipantReplyMore message parent) successor ->
  eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoParticipantReplyMore message parent)))
      (@echo_ir_initiator_reply_more_rule node) = IRRuleDisabled.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyMore message parent)
    participant_ack_more_rule (IRGuardKind EchoReply)
    step eq_refl ltac:(
      cbn [participant_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as reply_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyMore message parent)
    participant_ack_more_rule
    (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [participant_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as receiver_not_initiator.
  cbn [guard_holds eval_node_expr event_message]
    in reply_kind, receiver_not_initiator.
  unfold eval_ir_rule, echo_ir_initiator_reply_more_rule.
  unfold echo_ir_equal, echo_ir_receiver, echo_ir_initiator.
  cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches eval_ir_guards
    eval_ir_expr echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    echo_ir_encode_message echo_ir_encode_kind echo_ir_delivery_certificates
    echo_ir_event_forward_order echo_ir_event_expected_parent ir_value_eqb
    ir_processes ir_config_fields ir_message_kind ir_message_receiver
    ir_event_message echo_ir_signature echo_ir_local_field_type
    echo_ir_global_field_type echo_ir_config_field_type
    echo_ir_delivery_certificate_field_type].
  rewrite reply_kind.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRReply EchoIRReply) as [_ | impossible_kind].
  2: contradiction.
  cbn [eval_ir_guards eval_ir_expr echo_ir_encode_kind echo_ir_signature
    echo_ir_message_kind_eq_dec ir_config_fields ir_message_kind
    ir_message_receiver ir_event_message echo_ir_encode_config
    echo_ir_encode_config_fields echo_ir_encode_message ir_value_eqb].
  unfold ir_node_eqb.
  destruct (node_eq (message_receiver message) (config_initiator config))
    as [same_receiver | different_receiver].
  - contradiction.
  - reflexivity.
Qed.

Lemma echo_ir_initiator_reply_final_disabled_on_participant_more
    (state successor : @executable_echo_state node)
    (message : @echo_message node)
    (parent : node) :
  @EchoStep node node_eq config state
      (EchoParticipantReplyMore message parent) successor ->
  eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoParticipantReplyMore message parent)))
      (@echo_ir_initiator_reply_final_rule node) = IRRuleDisabled.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyMore message parent)
    participant_ack_more_rule (IRGuardKind EchoReply)
    step eq_refl ltac:(
      cbn [participant_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as reply_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyMore message parent)
    participant_ack_more_rule
    (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [participant_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as receiver_not_initiator.
  cbn [guard_holds eval_node_expr event_message]
    in reply_kind, receiver_not_initiator.
  unfold eval_ir_rule, echo_ir_initiator_reply_final_rule.
  unfold echo_ir_equal, echo_ir_receiver, echo_ir_initiator.
  cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches eval_ir_guards
    eval_ir_expr echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    echo_ir_encode_message echo_ir_encode_kind echo_ir_delivery_certificates
    echo_ir_event_forward_order echo_ir_event_expected_parent ir_value_eqb
    ir_processes ir_config_fields ir_message_kind ir_message_receiver
    ir_event_message echo_ir_signature echo_ir_local_field_type
    echo_ir_global_field_type echo_ir_config_field_type
    echo_ir_delivery_certificate_field_type].
  rewrite reply_kind.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRReply EchoIRReply) as [_ | impossible_kind].
  2: contradiction.
  cbn [eval_ir_guards eval_ir_expr echo_ir_encode_kind echo_ir_signature
    echo_ir_message_kind_eq_dec ir_config_fields ir_message_kind
    ir_message_receiver ir_event_message echo_ir_encode_config
    echo_ir_encode_config_fields echo_ir_encode_message ir_value_eqb].
  unfold ir_node_eqb.
  destruct (node_eq (message_receiver message) (config_initiator config))
    as [same_receiver | different_receiver].
  - contradiction.
  - reflexivity.
Qed.

Lemma echo_ir_participant_reply_more_tail_selects_none
    (state successor : @executable_echo_state node)
    (message : @echo_message node)
    (parent : node) :
  @EchoStep node node_eq config state
      (EchoParticipantReplyMore message parent) successor ->
  select_ir_rule node_eq (echo_ir_encode_config config)
    (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message)
      (@echo_ir_delivery_certificates node config
        (EchoParticipantReplyMore message parent)))
    [@echo_ir_participant_reply_final_rule node;
     @echo_ir_initiator_reply_more_rule node;
     @echo_ir_initiator_reply_final_rule node] =
  IRNoRuleSelected.
Proof.
  intro step.
  pose proof (echo_ir_participant_reply_final_disabled_on_more
    state successor message parent step) as participant_final_disabled.
  pose proof (echo_ir_initiator_reply_more_disabled_on_participant_more
    state successor message parent step) as initiator_more_disabled.
  pose proof (echo_ir_initiator_reply_final_disabled_on_participant_more
    state successor message parent step) as initiator_final_disabled.
  cbn [select_ir_rule].
  now rewrite participant_final_disabled, initiator_more_disabled,
    initiator_final_disabled.
Qed.

Lemma echo_ir_participant_reply_more_rule_selected
    (state successor : @executable_echo_state node)
    (message : @echo_message node)
    (parent : node) :
  @EchoStep node node_eq config state
      (EchoParticipantReplyMore message parent) successor ->
  select_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoParticipantReplyMore message parent)))
      (@echo_ir_rules node) =
    IRUniqueRuleSelected (@echo_ir_participant_reply_more_rule node).
Proof.
  intro step.
  pose proof (echo_ir_participant_reply_more_rule_enabled
    state successor message parent step) as enabled.
  pose proof (echo_ir_participant_reply_more_tail_selects_none
    state successor message parent step) as tail_none.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyMore message parent)
    participant_ack_more_rule (IRGuardKind EchoReply)
    step eq_refl ltac:(
      cbn [participant_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as reply_kind.
  cbn [guard_holds event_message] in reply_kind.
  pose proof (echo_ir_request_rules_select_none_on_reply
    state message
    (@echo_ir_delivery_certificates node config
      (EchoParticipantReplyMore message parent))
    reply_kind) as prefix_none.
  assert (start_mismatch :
    eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoParticipantReplyMore message parent)))
      (@echo_ir_start_rule node) = IRRuleMismatch).
  {
    unfold eval_ir_rule, echo_ir_start_rule.
    reflexivity.
  }
  unfold echo_ir_rules.
  erewrite select_ir_rule_cons_mismatch; [| exact start_mismatch].
  change
    (select_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoParticipantReplyMore message parent)))
      ([@echo_ir_first_request_nonleaf_rule node;
        @echo_ir_first_request_leaf_rule node;
        @echo_ir_repeated_request_rule node;
        @echo_ir_initiator_request_rule node] ++
       (@echo_ir_participant_reply_more_rule node ::
        [@echo_ir_participant_reply_final_rule node;
         @echo_ir_initiator_reply_more_rule node;
         @echo_ir_initiator_reply_final_rule node])) =
     IRUniqueRuleSelected (@echo_ir_participant_reply_more_rule node)).
  erewrite select_ir_rule_app_none; [| exact prefix_none].
  now apply select_ir_rule_cons_unique.
Qed.

Theorem echo_ir_participant_reply_more_forward_simulates
    (state successor : @executable_echo_state node)
    (message : @echo_message node)
    (parent : node) :
  @echo_reachable node node_eq config state ->
  @EchoStep node node_eq config state
      (EchoParticipantReplyMore message parent) successor ->
  exists ir_successor,
    interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state)
      (echo_ir_encode_event config
        (EchoParticipantReplyMore message parent)) =
      @IRStepSuccess node echo_ir_signature
        EchoIRParticipantReplyMoreRule ir_successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intros reachable step.
  pose proof (@echo_ir_resolve_successful_delivery
    node node_eq config state successor
    (EchoParticipantReplyMore message parent)
    reachable step I) as resolved.
  pose proof (echo_ir_participant_reply_more_rule_selected
    state successor message parent step) as selected.
  destruct (echo_ir_participant_reply_more_action_forward
    state successor message parent step) as
    [ir_successor [action correspondence]].
  exists ir_successor. split.
  - unfold interpret_protocol_rules.
    rewrite resolved.
    cbn [event_message].
    rewrite selected, action. reflexivity.
  - exact correspondence.
Qed.

Lemma echo_ir_participant_reply_final_rule_enabled
    (state successor : @executable_echo_state node)
    (message : @echo_message node)
    (parent : node) :
  @EchoStep node node_eq config state
      (EchoParticipantReplyFinal message parent) successor ->
  eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoParticipantReplyFinal message parent)))
      (@echo_ir_participant_reply_final_rule node) = IRRuleEnabled.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyFinal message parent)
    participant_ack_final_rule (IRGuardKind EchoReply)
    step eq_refl ltac:(
      cbn [participant_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as reply_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyFinal message parent)
    participant_ack_final_rule
    (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [participant_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as receiver_not_initiator.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyFinal message parent)
    participant_ack_final_rule
    (IRGuardParentEqual IRMessageReceiver (IRSomeParent IREventParent))
    step eq_refl ltac:(
      cbn [participant_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as parent_matches.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyFinal message parent)
    participant_ack_final_rule
    (IRGuardNodeIn IRMessageSender (IRNodesPending IRMessageReceiver))
    step eq_refl ltac:(
      cbn [participant_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as sender_pending.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyFinal message parent)
    participant_ack_final_rule
    (IRGuardNodesEmpty
      (IRNodesRemove IRMessageSender (IRNodesPending IRMessageReceiver)))
    step eq_refl ltac:(
      cbn [participant_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as pending_empty.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyFinal message parent)
    participant_ack_final_rule
    (IRGuardFinished IRMessageReceiver false)
    step eq_refl ltac:(
      cbn [participant_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as receiver_unfinished.
  cbn [guard_holds eval_node_expr eval_parent_expr eval_nodes_expr
    event_message event_parent] in reply_kind, receiver_not_initiator,
    parent_matches, sender_pending, pending_empty, receiver_unfinished.
  rewrite <- echo_ir_remove_node_agrees in pending_empty.
  pose proof (echo_ir_node_in_true_of_in
    (message_sender message)
    (process_pending (processes state (message_receiver message)))
    sender_pending) as sender_pending_true.
  unfold eval_ir_rule, echo_ir_participant_reply_final_rule.
  unfold echo_ir_not_equal, echo_ir_equal, echo_ir_receiver,
    echo_ir_initiator, echo_ir_parent, echo_ir_some,
    echo_ir_expected_parent, echo_ir_sender, echo_ir_pending,
    echo_ir_is_empty, echo_ir_removed_pending, echo_ir_finished,
    echo_ir_bool, echo_ir_remove.
  cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches eval_ir_guards
    eval_ir_expr echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    echo_ir_encode_message echo_ir_encode_kind echo_ir_delivery_certificates
    echo_ir_event_forward_order echo_ir_event_expected_parent ir_value_eqb
    ir_processes ir_config_fields ir_config_neighbors ir_message_kind
    ir_message_sender ir_message_receiver ir_event_message echo_ir_signature
    echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  rewrite reply_kind.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRReply EchoIRReply) as [_ | impossible_kind].
  2: contradiction.
  cbn [eval_ir_guards eval_ir_expr echo_ir_encode_kind echo_ir_signature
    echo_ir_message_kind_eq_dec ir_processes ir_config_fields
    ir_message_kind ir_message_sender ir_message_receiver ir_event_message
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_message
    echo_ir_delivery_certificates echo_ir_event_expected_parent ir_value_eqb].
  unfold ir_node_eqb.
  destruct (node_eq (message_receiver message) (config_initiator config))
    as [same_receiver | different_receiver].
  - contradiction.
  - cbn.
    unfold ir_node_eqb, ir_option_node_eqb.
    rewrite parent_matches, sender_pending_true, pending_empty,
      receiver_unfinished.
    destruct (node_eq parent parent) as [_ | impossible_parent].
    + unfold ir_node_eqb.
      destruct (node_eq parent parent) as [_ | impossible_again].
      * reflexivity.
      * contradiction.
    + contradiction.
Qed.

Lemma echo_ir_participant_reply_final_action_forward
    (state successor : @executable_echo_state node)
    (message : @echo_message node)
    (parent : node) :
  @EchoStep node node_eq config state
      (EchoParticipantReplyFinal message parent) successor ->
  exists ir_successor,
    eval_ir_action node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoParticipantReplyFinal message parent)))
      (ir_rule_action (@echo_ir_participant_reply_final_rule node)) =
        Some ir_successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intro step.
  pose proof (@EchoStep_selected_action node node_eq config
    state successor (EchoParticipantReplyFinal message parent)
    participant_ack_final_rule step eq_refl) as old_action.
  unfold participant_ack_final_rule in old_action.
  cbn [EchoTransitionIR.eval_action EchoTransitionIR.ir_rule_action
    EchoTransitionIR.eval_process_expr EchoTransitionIR.eval_parent_expr
    EchoTransitionIR.eval_nodes_expr EchoTransitionIR.eval_node_expr
    EchoTransitionIR.eval_outbound_expr EchoTransitionIR.event_message
    EchoTransitionIR.event_parent] in old_action.
  unfold apply_echo_delivery in old_action.
  cbn in old_action. subst successor.
  unfold echo_ir_participant_reply_final_rule.
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
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  eexists. split.
  - reflexivity.
  - unfold echo_ir_states_correspond.
    repeat split.
    + intros process field.
      cbn [ir_emit_messages ir_remove_selected_message ir_processes
        processes].
      destruct (node_eq (message_receiver message) process)
        as [same | different].
      * subst process.
        rewrite echo_update_process_same.
        destruct field.
        -- cbn [ir_set_local_field ir_processes processes
             echo_ir_encode_process].
           repeat rewrite ir_update_processes_same.
           rewrite ir_update_field_different by discriminate.
           rewrite ir_update_field_different by discriminate.
           rewrite ir_update_field_same. reflexivity.
        -- cbn [ir_set_local_field ir_processes processes
             echo_ir_encode_process].
           repeat rewrite ir_update_processes_same.
           rewrite ir_update_field_different by discriminate.
           rewrite ir_update_field_same. reflexivity.
        -- cbn [ir_set_local_field ir_processes processes
             echo_ir_encode_process].
           rewrite ir_update_processes_same.
           rewrite ir_update_field_same. reflexivity.
      * rewrite echo_update_process_different by exact different.
        cbn [ir_set_local_field ir_processes processes
          echo_ir_encode_process].
        repeat rewrite ir_update_processes_different by exact different.
        reflexivity.
    + cbn [ir_emit_messages ir_remove_selected_message ir_set_local_field
        ir_message_store message_store echo_ir_encode_state].
      rewrite List.map_app.
      rewrite echo_ir_remove_message_encoding.
      unfold ir_remove_selected_message.
      cbn [ir_set_local_field ir_next_message_id echo_ir_encode_state].
      pose proof (echo_ir_materialize_messages_encoding
        (next_message_id state) EchoReply (message_receiver message)
        [parent]) as materialized.
      cbn [echo_ir_encode_kind] in materialized.
      rewrite materialized. reflexivity.
Qed.

Lemma echo_ir_participant_reply_more_disabled_on_final
    (state successor : @executable_echo_state node)
    (message : @echo_message node)
    (parent : node) :
  @EchoStep node node_eq config state
      (EchoParticipantReplyFinal message parent) successor ->
  eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoParticipantReplyFinal message parent)))
      (@echo_ir_participant_reply_more_rule node) = IRRuleDisabled.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyFinal message parent)
    participant_ack_final_rule (IRGuardKind EchoReply)
    step eq_refl ltac:(
      cbn [participant_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as reply_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyFinal message parent)
    participant_ack_final_rule
    (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [participant_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as receiver_not_initiator.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyFinal message parent)
    participant_ack_final_rule
    (IRGuardParentEqual IRMessageReceiver (IRSomeParent IREventParent))
    step eq_refl ltac:(
      cbn [participant_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as parent_matches.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyFinal message parent)
    participant_ack_final_rule
    (IRGuardNodeIn IRMessageSender (IRNodesPending IRMessageReceiver))
    step eq_refl ltac:(
      cbn [participant_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as sender_pending.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyFinal message parent)
    participant_ack_final_rule
    (IRGuardNodesEmpty
      (IRNodesRemove IRMessageSender (IRNodesPending IRMessageReceiver)))
    step eq_refl ltac:(
      cbn [participant_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as pending_empty.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyFinal message parent)
    participant_ack_final_rule
    (IRGuardFinished IRMessageReceiver false)
    step eq_refl ltac:(
      cbn [participant_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as receiver_unfinished.
  cbn [guard_holds eval_node_expr eval_parent_expr eval_nodes_expr
    event_message event_parent] in reply_kind, receiver_not_initiator,
    parent_matches, sender_pending, pending_empty, receiver_unfinished.
  rewrite <- echo_ir_remove_node_agrees in pending_empty.
  pose proof (echo_ir_node_in_true_of_in
    (message_sender message)
    (process_pending (processes state (message_receiver message)))
    sender_pending) as sender_pending_true.
  unfold eval_ir_rule, echo_ir_participant_reply_more_rule.
  unfold echo_ir_not_equal, echo_ir_equal, echo_ir_receiver,
    echo_ir_initiator, echo_ir_parent, echo_ir_some,
    echo_ir_expected_parent, echo_ir_sender, echo_ir_pending,
    echo_ir_nonempty, echo_ir_is_empty, echo_ir_removed_pending,
    echo_ir_finished, echo_ir_bool, echo_ir_remove.
  cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches eval_ir_guards
    eval_ir_expr echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    echo_ir_encode_message echo_ir_encode_kind echo_ir_delivery_certificates
    echo_ir_event_forward_order echo_ir_event_expected_parent ir_value_eqb
    ir_processes ir_config_fields ir_config_neighbors ir_message_kind
    ir_message_sender ir_message_receiver ir_event_message echo_ir_signature
    echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  rewrite reply_kind.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRReply EchoIRReply) as [_ | impossible_kind].
  2: contradiction.
  cbn [eval_ir_guards eval_ir_expr echo_ir_encode_kind echo_ir_signature
    echo_ir_message_kind_eq_dec ir_processes ir_config_fields
    ir_message_kind ir_message_sender ir_message_receiver ir_event_message
    echo_ir_encode_config echo_ir_encode_config_fields echo_ir_encode_state
    echo_ir_encode_process echo_ir_encode_message
    echo_ir_delivery_certificates echo_ir_event_expected_parent ir_value_eqb].
  unfold ir_node_eqb.
  destruct (node_eq (message_receiver message) (config_initiator config))
    as [same_receiver | different_receiver].
  - contradiction.
  - cbn.
    unfold ir_node_eqb, ir_option_node_eqb.
    rewrite parent_matches, sender_pending_true, pending_empty,
      receiver_unfinished.
    destruct (node_eq parent parent) as [_ | impossible_parent].
    + unfold ir_node_eqb.
      destruct (node_eq parent parent) as [_ | impossible_again].
      * reflexivity.
      * contradiction.
    + contradiction.
Qed.

(** Initiator-only reply rules are disabled as soon as a delivered reply is
    addressed to a participant.  This certificate-independent fact is shared
    by both participant reply branches. *)
Lemma echo_ir_initiator_reply_more_disabled_for_participant
    (state : @executable_echo_state node)
    (message : @echo_message node)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  message_kind message = EchoReply ->
  message_receiver message <> config_initiator config ->
  eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
      (@echo_ir_initiator_reply_more_rule node) = IRRuleDisabled.
Proof.
  intros reply_kind receiver_not_initiator.
  unfold eval_ir_rule, echo_ir_initiator_reply_more_rule.
  unfold echo_ir_equal, echo_ir_receiver, echo_ir_initiator.
  cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches eval_ir_guards
    eval_ir_expr echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    echo_ir_encode_message echo_ir_encode_kind ir_value_eqb ir_processes
    ir_config_fields ir_message_kind ir_message_receiver ir_event_message
    echo_ir_signature echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  rewrite reply_kind.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRReply EchoIRReply) as [_ | impossible_kind].
  2: contradiction.
  cbn [eval_ir_guards eval_ir_expr echo_ir_encode_kind echo_ir_signature
    echo_ir_message_kind_eq_dec ir_config_fields ir_message_kind
    ir_message_receiver ir_event_message echo_ir_encode_config
    echo_ir_encode_config_fields echo_ir_encode_message ir_value_eqb].
  unfold ir_node_eqb.
  destruct (node_eq (message_receiver message) (config_initiator config))
    as [same_receiver | different_receiver].
  - contradiction.
  - reflexivity.
Qed.

Lemma echo_ir_initiator_reply_final_disabled_for_participant
    (state : @executable_echo_state node)
    (message : @echo_message node)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  message_kind message = EchoReply ->
  message_receiver message <> config_initiator config ->
  eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
      (@echo_ir_initiator_reply_final_rule node) = IRRuleDisabled.
Proof.
  intros reply_kind receiver_not_initiator.
  unfold eval_ir_rule, echo_ir_initiator_reply_final_rule.
  unfold echo_ir_equal, echo_ir_receiver, echo_ir_initiator.
  cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches eval_ir_guards
    eval_ir_expr echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    echo_ir_encode_message echo_ir_encode_kind ir_value_eqb ir_processes
    ir_config_fields ir_message_kind ir_message_receiver ir_event_message
    echo_ir_signature echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  rewrite reply_kind.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRReply EchoIRReply) as [_ | impossible_kind].
  2: contradiction.
  cbn [eval_ir_guards eval_ir_expr echo_ir_encode_kind echo_ir_signature
    echo_ir_message_kind_eq_dec ir_config_fields ir_message_kind
    ir_message_receiver ir_event_message echo_ir_encode_config
    echo_ir_encode_config_fields echo_ir_encode_message ir_value_eqb].
  unfold ir_node_eqb.
  destruct (node_eq (message_receiver message) (config_initiator config))
    as [same_receiver | different_receiver].
  - contradiction.
  - reflexivity.
Qed.

Lemma echo_ir_participant_reply_final_tail_selects_none
    (state successor : @executable_echo_state node)
    (message : @echo_message node)
    (parent : node) :
  @EchoStep node node_eq config state
      (EchoParticipantReplyFinal message parent) successor ->
  select_ir_rule node_eq (echo_ir_encode_config config)
    (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message)
      (@echo_ir_delivery_certificates node config
        (EchoParticipantReplyFinal message parent)))
    [@echo_ir_initiator_reply_more_rule node;
     @echo_ir_initiator_reply_final_rule node] =
  IRNoRuleSelected.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyFinal message parent)
    participant_ack_final_rule (IRGuardKind EchoReply)
    step eq_refl ltac:(
      cbn [participant_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as reply_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyFinal message parent)
    participant_ack_final_rule
    (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [participant_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as receiver_not_initiator.
  cbn [guard_holds eval_node_expr event_message]
    in reply_kind, receiver_not_initiator.
  pose proof (echo_ir_initiator_reply_more_disabled_for_participant
    state message
    (@echo_ir_delivery_certificates node config
      (EchoParticipantReplyFinal message parent))
    reply_kind receiver_not_initiator) as more_disabled.
  pose proof (echo_ir_initiator_reply_final_disabled_for_participant
    state message
    (@echo_ir_delivery_certificates node config
      (EchoParticipantReplyFinal message parent))
    reply_kind receiver_not_initiator) as final_disabled.
  cbn [select_ir_rule].
  now rewrite more_disabled, final_disabled.
Qed.

Lemma echo_ir_participant_reply_final_rule_selected
    (state successor : @executable_echo_state node)
    (message : @echo_message node)
    (parent : node) :
  @EchoStep node node_eq config state
      (EchoParticipantReplyFinal message parent) successor ->
  select_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoParticipantReplyFinal message parent)))
      (@echo_ir_rules node) =
    IRUniqueRuleSelected (@echo_ir_participant_reply_final_rule node).
Proof.
  intro step.
  pose proof (echo_ir_participant_reply_final_rule_enabled
    state successor message parent step) as enabled.
  pose proof (echo_ir_participant_reply_more_disabled_on_final
    state successor message parent step) as participant_more_disabled.
  pose proof (echo_ir_participant_reply_final_tail_selects_none
    state successor message parent step) as tail_none.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyFinal message parent)
    participant_ack_final_rule (IRGuardKind EchoReply)
    step eq_refl ltac:(
      cbn [participant_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as reply_kind.
  cbn [guard_holds event_message] in reply_kind.
  pose proof (echo_ir_request_rules_select_none_on_reply
    state message
    (@echo_ir_delivery_certificates node config
      (EchoParticipantReplyFinal message parent))
    reply_kind) as prefix_none.
  assert (start_mismatch :
    eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoParticipantReplyFinal message parent)))
      (@echo_ir_start_rule node) = IRRuleMismatch).
  {
    unfold eval_ir_rule, echo_ir_start_rule.
    reflexivity.
  }
  unfold echo_ir_rules.
  erewrite select_ir_rule_cons_mismatch; [| exact start_mismatch].
  change
    (select_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoParticipantReplyFinal message parent)))
      ([@echo_ir_first_request_nonleaf_rule node;
        @echo_ir_first_request_leaf_rule node;
        @echo_ir_repeated_request_rule node;
        @echo_ir_initiator_request_rule node] ++
       (@echo_ir_participant_reply_more_rule node ::
        @echo_ir_participant_reply_final_rule node ::
        [@echo_ir_initiator_reply_more_rule node;
         @echo_ir_initiator_reply_final_rule node])) =
     IRUniqueRuleSelected (@echo_ir_participant_reply_final_rule node)).
  erewrite select_ir_rule_app_none; [| exact prefix_none].
  erewrite select_ir_rule_cons_disabled;
    [| exact participant_more_disabled].
  now apply select_ir_rule_cons_unique.
Qed.

Theorem echo_ir_participant_reply_final_forward_simulates
    (state successor : @executable_echo_state node)
    (message : @echo_message node)
    (parent : node) :
  @echo_reachable node node_eq config state ->
  @EchoStep node node_eq config state
      (EchoParticipantReplyFinal message parent) successor ->
  exists ir_successor,
    interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state)
      (echo_ir_encode_event config
        (EchoParticipantReplyFinal message parent)) =
      @IRStepSuccess node echo_ir_signature
        EchoIRParticipantReplyFinalRule ir_successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intros reachable step.
  pose proof (@echo_ir_resolve_successful_delivery
    node node_eq config state successor
    (EchoParticipantReplyFinal message parent)
    reachable step I) as resolved.
  pose proof (echo_ir_participant_reply_final_rule_selected
    state successor message parent step) as selected.
  destruct (echo_ir_participant_reply_final_action_forward
    state successor message parent step) as
    [ir_successor [action correspondence]].
  exists ir_successor. split.
  - unfold interpret_protocol_rules.
    rewrite resolved.
    cbn [event_message].
    rewrite selected, action. reflexivity.
  - exact correspondence.
Qed.

Lemma echo_ir_initiator_reply_more_rule_enabled
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoInitiatorReplyMore message) successor ->
  eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoInitiatorReplyMore message)))
      (@echo_ir_initiator_reply_more_rule node) = IRRuleEnabled.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyMore message)
    initiator_ack_more_rule (IRGuardKind EchoReply)
    step eq_refl ltac:(
      cbn [initiator_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as reply_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyMore message)
    initiator_ack_more_rule
    (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [initiator_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as receiver_is_initiator.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyMore message)
    initiator_ack_more_rule (IRGuardStarted true)
    step eq_refl ltac:(
      cbn [initiator_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as protocol_started.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyMore message)
    initiator_ack_more_rule
    (IRGuardParentEqual IRInitiatorNode IRNoParent)
    step eq_refl ltac:(
      cbn [initiator_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as initiator_parent_none.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyMore message)
    initiator_ack_more_rule
    (IRGuardNodeIn IRMessageSender (IRNodesPending IRInitiatorNode))
    step eq_refl ltac:(
      cbn [initiator_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as sender_pending.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyMore message)
    initiator_ack_more_rule
    (IRGuardNodesNonempty
      (IRNodesRemove IRMessageSender (IRNodesPending IRInitiatorNode)))
    step eq_refl ltac:(
      cbn [initiator_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as pending_remains.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyMore message)
    initiator_ack_more_rule
    (IRGuardFinished IRInitiatorNode false)
    step eq_refl ltac:(
      cbn [initiator_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as initiator_unfinished.
  cbn [guard_holds eval_node_expr eval_parent_expr eval_nodes_expr
    event_message] in reply_kind, receiver_is_initiator, protocol_started,
    initiator_parent_none, sender_pending, pending_remains,
    initiator_unfinished.
  rewrite <- echo_ir_remove_node_agrees in pending_remains.
  pose proof (echo_ir_node_in_true_of_in
    (message_sender message)
    (process_pending (processes state (config_initiator config)))
    sender_pending) as sender_pending_true.
  unfold eval_ir_rule, echo_ir_initiator_reply_more_rule.
  unfold echo_ir_equal, echo_ir_receiver, echo_ir_initiator,
    echo_ir_started, echo_ir_parent, echo_ir_option_none,
    echo_ir_sender, echo_ir_pending, echo_ir_nonempty, echo_ir_is_empty,
    echo_ir_removed_pending, echo_ir_finished, echo_ir_bool,
    echo_ir_remove.
  cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches eval_ir_guards
    eval_ir_expr echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    echo_ir_encode_message echo_ir_encode_kind echo_ir_delivery_certificates
    echo_ir_event_forward_order echo_ir_event_expected_parent ir_value_eqb
    ir_processes ir_global_fields ir_config_fields ir_config_neighbors
    ir_message_kind ir_message_sender ir_message_receiver ir_event_message
    echo_ir_signature echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  rewrite reply_kind.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRReply EchoIRReply) as [_ | impossible_kind].
  2: contradiction.
  cbn [eval_ir_guards eval_ir_expr echo_ir_encode_kind echo_ir_signature
    echo_ir_message_kind_eq_dec ir_processes ir_global_fields
    ir_config_fields ir_message_kind ir_message_sender ir_message_receiver
    ir_event_message echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    echo_ir_encode_message echo_ir_delivery_certificates ir_value_eqb].
  rewrite receiver_is_initiator, protocol_started, initiator_parent_none,
    sender_pending_true, initiator_unfinished.
  unfold ir_node_eqb, ir_option_node_eqb.
  destruct (node_eq (config_initiator config) (config_initiator config))
    as [_ | impossible_receiver].
  2: contradiction.
  cbn.
  destruct (ir_remove_node node_eq (message_sender message)
      (process_pending (processes state (config_initiator config))))
      as [|remaining rest] eqn:pending_shape.
  - contradiction.
  - reflexivity.
Qed.

Lemma echo_ir_initiator_reply_more_action_forward
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoInitiatorReplyMore message) successor ->
  exists ir_successor,
    eval_ir_action node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoInitiatorReplyMore message)))
      (ir_rule_action (@echo_ir_initiator_reply_more_rule node)) =
        Some ir_successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyMore message)
    initiator_ack_more_rule
    (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [initiator_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as receiver_is_initiator.
  cbn [guard_holds eval_node_expr event_message] in receiver_is_initiator.
  pose proof (@EchoStep_selected_action node node_eq config
    state successor (EchoInitiatorReplyMore message)
    initiator_ack_more_rule step eq_refl) as old_action.
  unfold initiator_ack_more_rule in old_action.
  cbn [EchoTransitionIR.eval_action EchoTransitionIR.ir_rule_action
    EchoTransitionIR.eval_process_expr EchoTransitionIR.eval_parent_expr
    EchoTransitionIR.eval_nodes_expr EchoTransitionIR.eval_node_expr
    EchoTransitionIR.eval_outbound_expr EchoTransitionIR.event_message]
    in old_action.
  unfold apply_echo_delivery in old_action.
  cbn in old_action.
  rewrite receiver_is_initiator in old_action.
  subst successor.
  unfold echo_ir_initiator_reply_more_rule.
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
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  cbn [ir_config_fields echo_ir_encode_config echo_ir_encode_config_fields
    eval_ir_expr].
  rewrite ir_set_local_field_read_different by discriminate.
  cbn [eval_ir_action ir_set_local_field ir_remove_selected_message].
  eexists. split.
  - reflexivity.
  - unfold echo_ir_states_correspond.
    repeat split.
    + intros process field.
      cbn [ir_remove_selected_message ir_processes processes].
      destruct (node_eq (config_initiator config) process)
        as [same | different].
      * subst process.
        rewrite echo_update_process_same.
        destruct field.
        -- cbn [ir_set_local_field ir_processes processes
             echo_ir_encode_process].
           repeat rewrite ir_update_processes_same.
           rewrite ir_update_field_different by discriminate.
           rewrite ir_update_field_different by discriminate.
           rewrite ir_update_field_same. reflexivity.
        -- cbn [ir_set_local_field ir_processes processes
             echo_ir_encode_process].
           repeat rewrite ir_update_processes_same.
           rewrite ir_update_field_different by discriminate.
           rewrite ir_update_field_same.
           rewrite echo_ir_remove_node_agrees. reflexivity.
        -- cbn [ir_set_local_field ir_processes processes
             echo_ir_encode_process].
           rewrite ir_update_processes_same.
           rewrite ir_update_field_same. reflexivity.
      * rewrite echo_update_process_different by exact different.
        cbn [ir_set_local_field ir_processes processes
          echo_ir_encode_process].
        repeat rewrite ir_update_processes_different by exact different.
        reflexivity.
    + cbn [ir_remove_selected_message ir_message_store message_store
        echo_ir_encode_state ir_set_local_field].
      rewrite echo_ir_remove_message_encoding.
      now rewrite app_nil_r.
    + cbn [ir_remove_selected_message ir_set_local_field
        ir_next_message_id next_message_id echo_ir_encode_state].
      unfold next_echo_message_id_after.
      now rewrite Nat.add_0_r.
Qed.

Lemma echo_ir_participant_reply_more_disabled_for_initiator
    (state : @executable_echo_state node)
    (message : @echo_message node)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  message_kind message = EchoReply ->
  message_receiver message = config_initiator config ->
  eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
      (@echo_ir_participant_reply_more_rule node) = IRRuleDisabled.
Proof.
  intros reply_kind receiver_is_initiator.
  unfold eval_ir_rule, echo_ir_participant_reply_more_rule.
  unfold echo_ir_not_equal, echo_ir_equal, echo_ir_receiver,
    echo_ir_initiator.
  cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches eval_ir_guards
    eval_ir_expr echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    echo_ir_encode_message echo_ir_encode_kind ir_value_eqb ir_processes
    ir_config_fields ir_message_kind ir_message_receiver ir_event_message
    echo_ir_signature echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  rewrite reply_kind.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRReply EchoIRReply) as [_ | impossible_kind].
  2: contradiction.
  cbn [eval_ir_guards eval_ir_expr echo_ir_encode_kind echo_ir_signature
    echo_ir_message_kind_eq_dec ir_config_fields ir_message_kind
    ir_message_receiver ir_event_message echo_ir_encode_config
    echo_ir_encode_config_fields echo_ir_encode_message ir_value_eqb].
  rewrite receiver_is_initiator.
  unfold ir_node_eqb.
  destruct (node_eq (config_initiator config) (config_initiator config))
    as [_ | impossible_receiver].
  - reflexivity.
  - contradiction.
Qed.

Lemma echo_ir_participant_reply_final_disabled_for_initiator
    (state : @executable_echo_state node)
    (message : @echo_message node)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  message_kind message = EchoReply ->
  message_receiver message = config_initiator config ->
  eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
      (@echo_ir_participant_reply_final_rule node) = IRRuleDisabled.
Proof.
  intros reply_kind receiver_is_initiator.
  unfold eval_ir_rule, echo_ir_participant_reply_final_rule.
  unfold echo_ir_not_equal, echo_ir_equal, echo_ir_receiver,
    echo_ir_initiator.
  cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches eval_ir_guards
    eval_ir_expr echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    echo_ir_encode_message echo_ir_encode_kind ir_value_eqb ir_processes
    ir_config_fields ir_message_kind ir_message_receiver ir_event_message
    echo_ir_signature echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  rewrite reply_kind.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRReply EchoIRReply) as [_ | impossible_kind].
  2: contradiction.
  cbn [eval_ir_guards eval_ir_expr echo_ir_encode_kind echo_ir_signature
    echo_ir_message_kind_eq_dec ir_config_fields ir_message_kind
    ir_message_receiver ir_event_message echo_ir_encode_config
    echo_ir_encode_config_fields echo_ir_encode_message ir_value_eqb].
  rewrite receiver_is_initiator.
  unfold ir_node_eqb.
  destruct (node_eq (config_initiator config) (config_initiator config))
    as [_ | impossible_receiver].
  - reflexivity.
  - contradiction.
Qed.

Lemma echo_ir_participant_reply_rules_select_none_for_initiator
    (state : @executable_echo_state node)
    (message : @echo_message node)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  message_kind message = EchoReply ->
  message_receiver message = config_initiator config ->
  select_ir_rule node_eq (echo_ir_encode_config config)
    (echo_ir_encode_state state)
    (IRRuntimeDeliver (@echo_ir_encode_message node message) certificates)
    [@echo_ir_participant_reply_more_rule node;
     @echo_ir_participant_reply_final_rule node] =
  IRNoRuleSelected.
Proof.
  intros reply_kind receiver_is_initiator.
  pose proof (echo_ir_participant_reply_more_disabled_for_initiator
    state message certificates reply_kind receiver_is_initiator)
    as more_disabled.
  pose proof (echo_ir_participant_reply_final_disabled_for_initiator
    state message certificates reply_kind receiver_is_initiator)
    as final_disabled.
  cbn [select_ir_rule].
  now rewrite more_disabled, final_disabled.
Qed.

Lemma echo_ir_initiator_reply_final_disabled_on_more
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoInitiatorReplyMore message) successor ->
  eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoInitiatorReplyMore message)))
      (@echo_ir_initiator_reply_final_rule node) = IRRuleDisabled.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyMore message)
    initiator_ack_more_rule (IRGuardKind EchoReply)
    step eq_refl ltac:(
      cbn [initiator_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as reply_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyMore message)
    initiator_ack_more_rule
    (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [initiator_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as receiver_is_initiator.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyMore message)
    initiator_ack_more_rule (IRGuardStarted true)
    step eq_refl ltac:(
      cbn [initiator_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as protocol_started.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyMore message)
    initiator_ack_more_rule
    (IRGuardParentEqual IRInitiatorNode IRNoParent)
    step eq_refl ltac:(
      cbn [initiator_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as initiator_parent_none.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyMore message)
    initiator_ack_more_rule
    (IRGuardNodeIn IRMessageSender (IRNodesPending IRInitiatorNode))
    step eq_refl ltac:(
      cbn [initiator_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as sender_pending.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyMore message)
    initiator_ack_more_rule
    (IRGuardNodesNonempty
      (IRNodesRemove IRMessageSender (IRNodesPending IRInitiatorNode)))
    step eq_refl ltac:(
      cbn [initiator_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as pending_remains.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyMore message)
    initiator_ack_more_rule
    (IRGuardFinished IRInitiatorNode false)
    step eq_refl ltac:(
      cbn [initiator_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as initiator_unfinished.
  cbn [guard_holds eval_node_expr eval_parent_expr eval_nodes_expr
    event_message] in reply_kind, receiver_is_initiator, protocol_started,
    initiator_parent_none, sender_pending, pending_remains,
    initiator_unfinished.
  rewrite <- echo_ir_remove_node_agrees in pending_remains.
  pose proof (echo_ir_node_in_true_of_in
    (message_sender message)
    (process_pending (processes state (config_initiator config)))
    sender_pending) as sender_pending_true.
  unfold eval_ir_rule, echo_ir_initiator_reply_final_rule.
  unfold echo_ir_equal, echo_ir_receiver, echo_ir_initiator,
    echo_ir_started, echo_ir_parent, echo_ir_option_none,
    echo_ir_sender, echo_ir_pending, echo_ir_is_empty,
    echo_ir_removed_pending, echo_ir_finished, echo_ir_bool,
    echo_ir_remove.
  cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches eval_ir_guards
    eval_ir_expr echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    echo_ir_encode_message echo_ir_encode_kind echo_ir_delivery_certificates
    echo_ir_event_forward_order echo_ir_event_expected_parent ir_value_eqb
    ir_processes ir_global_fields ir_config_fields ir_config_neighbors
    ir_message_kind ir_message_sender ir_message_receiver ir_event_message
    echo_ir_signature echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  rewrite reply_kind.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRReply EchoIRReply) as [_ | impossible_kind].
  2: contradiction.
  cbn [eval_ir_guards eval_ir_expr echo_ir_encode_kind echo_ir_signature
    echo_ir_message_kind_eq_dec ir_processes ir_global_fields
    ir_config_fields ir_message_kind ir_message_sender ir_message_receiver
    ir_event_message echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    echo_ir_encode_message echo_ir_delivery_certificates ir_value_eqb].
  rewrite receiver_is_initiator, protocol_started, initiator_parent_none,
    sender_pending_true, initiator_unfinished.
  unfold ir_node_eqb, ir_option_node_eqb.
  destruct (node_eq (config_initiator config) (config_initiator config))
    as [_ | impossible_receiver].
  2: contradiction.
  cbn.
  destruct (ir_remove_node node_eq (message_sender message)
      (process_pending (processes state (config_initiator config))))
      as [|remaining rest] eqn:pending_shape.
  - contradiction.
  - reflexivity.
Qed.

Lemma echo_ir_initiator_reply_more_rule_selected
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoInitiatorReplyMore message) successor ->
  select_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoInitiatorReplyMore message)))
      (@echo_ir_rules node) =
    IRUniqueRuleSelected (@echo_ir_initiator_reply_more_rule node).
Proof.
  intro step.
  pose proof (echo_ir_initiator_reply_more_rule_enabled
    state successor message step) as enabled.
  pose proof (echo_ir_initiator_reply_final_disabled_on_more
    state successor message step) as final_disabled.
  assert (tail_none :
    select_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoInitiatorReplyMore message)))
      [@echo_ir_initiator_reply_final_rule node] = IRNoRuleSelected).
  {
    cbn [select_ir_rule].
    now rewrite final_disabled.
  }
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyMore message)
    initiator_ack_more_rule (IRGuardKind EchoReply)
    step eq_refl ltac:(
      cbn [initiator_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as reply_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyMore message)
    initiator_ack_more_rule
    (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [initiator_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as receiver_is_initiator.
  cbn [guard_holds eval_node_expr event_message]
    in reply_kind, receiver_is_initiator.
  pose proof (echo_ir_request_rules_select_none_on_reply
    state message
    (@echo_ir_delivery_certificates node config
      (EchoInitiatorReplyMore message))
    reply_kind) as request_prefix_none.
  pose proof (echo_ir_participant_reply_rules_select_none_for_initiator
    state message
    (@echo_ir_delivery_certificates node config
      (EchoInitiatorReplyMore message))
    reply_kind receiver_is_initiator) as participant_prefix_none.
  assert (start_mismatch :
    eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoInitiatorReplyMore message)))
      (@echo_ir_start_rule node) = IRRuleMismatch).
  {
    unfold eval_ir_rule, echo_ir_start_rule.
    reflexivity.
  }
  unfold echo_ir_rules.
  erewrite select_ir_rule_cons_mismatch; [| exact start_mismatch].
  change
    (select_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoInitiatorReplyMore message)))
      ([@echo_ir_first_request_nonleaf_rule node;
        @echo_ir_first_request_leaf_rule node;
        @echo_ir_repeated_request_rule node;
        @echo_ir_initiator_request_rule node] ++
       [@echo_ir_participant_reply_more_rule node;
        @echo_ir_participant_reply_final_rule node;
        @echo_ir_initiator_reply_more_rule node;
        @echo_ir_initiator_reply_final_rule node]) =
     IRUniqueRuleSelected (@echo_ir_initiator_reply_more_rule node)).
  erewrite select_ir_rule_app_none; [| exact request_prefix_none].
  change
    (select_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoInitiatorReplyMore message)))
      ([@echo_ir_participant_reply_more_rule node;
        @echo_ir_participant_reply_final_rule node] ++
       [@echo_ir_initiator_reply_more_rule node;
        @echo_ir_initiator_reply_final_rule node]) =
     IRUniqueRuleSelected (@echo_ir_initiator_reply_more_rule node)).
  erewrite select_ir_rule_app_none; [| exact participant_prefix_none].
  now apply select_ir_rule_cons_unique.
Qed.

Theorem echo_ir_initiator_reply_more_forward_simulates
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @echo_reachable node node_eq config state ->
  @EchoStep node node_eq config state
      (EchoInitiatorReplyMore message) successor ->
  exists ir_successor,
    interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state)
      (echo_ir_encode_event config (EchoInitiatorReplyMore message)) =
      @IRStepSuccess node echo_ir_signature
        EchoIRInitiatorReplyMoreRule ir_successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intros reachable step.
  pose proof (@echo_ir_resolve_successful_delivery
    node node_eq config state successor (EchoInitiatorReplyMore message)
    reachable step I) as resolved.
  pose proof (echo_ir_initiator_reply_more_rule_selected
    state successor message step) as selected.
  destruct (echo_ir_initiator_reply_more_action_forward
    state successor message step) as
    [ir_successor [action correspondence]].
  exists ir_successor. split.
  - unfold interpret_protocol_rules.
    rewrite resolved.
    cbn [event_message].
    rewrite selected, action. reflexivity.
  - exact correspondence.
Qed.

Lemma echo_ir_initiator_reply_final_rule_enabled
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoInitiatorReplyFinal message) successor ->
  eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoInitiatorReplyFinal message)))
      (@echo_ir_initiator_reply_final_rule node) = IRRuleEnabled.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyFinal message)
    initiator_ack_final_rule (IRGuardKind EchoReply)
    step eq_refl ltac:(
      cbn [initiator_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as reply_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyFinal message)
    initiator_ack_final_rule
    (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [initiator_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as receiver_is_initiator.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyFinal message)
    initiator_ack_final_rule (IRGuardStarted true)
    step eq_refl ltac:(
      cbn [initiator_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as protocol_started.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyFinal message)
    initiator_ack_final_rule
    (IRGuardParentEqual IRInitiatorNode IRNoParent)
    step eq_refl ltac:(
      cbn [initiator_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as initiator_parent_none.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyFinal message)
    initiator_ack_final_rule
    (IRGuardNodeIn IRMessageSender (IRNodesPending IRInitiatorNode))
    step eq_refl ltac:(
      cbn [initiator_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as sender_pending.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyFinal message)
    initiator_ack_final_rule
    (IRGuardNodesEmpty
      (IRNodesRemove IRMessageSender (IRNodesPending IRInitiatorNode)))
    step eq_refl ltac:(
      cbn [initiator_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as pending_empty.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyFinal message)
    initiator_ack_final_rule
    (IRGuardFinished IRInitiatorNode false)
    step eq_refl ltac:(
      cbn [initiator_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as initiator_unfinished.
  cbn [guard_holds eval_node_expr eval_parent_expr eval_nodes_expr
    event_message] in reply_kind, receiver_is_initiator, protocol_started,
    initiator_parent_none, sender_pending, pending_empty,
    initiator_unfinished.
  rewrite <- echo_ir_remove_node_agrees in pending_empty.
  pose proof (echo_ir_node_in_true_of_in
    (message_sender message)
    (process_pending (processes state (config_initiator config)))
    sender_pending) as sender_pending_true.
  unfold eval_ir_rule, echo_ir_initiator_reply_final_rule.
  unfold echo_ir_equal, echo_ir_receiver, echo_ir_initiator,
    echo_ir_started, echo_ir_parent, echo_ir_option_none,
    echo_ir_sender, echo_ir_pending, echo_ir_is_empty,
    echo_ir_removed_pending, echo_ir_finished, echo_ir_bool,
    echo_ir_remove.
  cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches eval_ir_guards
    eval_ir_expr echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    echo_ir_encode_message echo_ir_encode_kind echo_ir_delivery_certificates
    echo_ir_event_forward_order echo_ir_event_expected_parent ir_value_eqb
    ir_processes ir_global_fields ir_config_fields ir_config_neighbors
    ir_message_kind ir_message_sender ir_message_receiver ir_event_message
    echo_ir_signature echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  rewrite reply_kind.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRReply EchoIRReply) as [_ | impossible_kind].
  2: contradiction.
  cbn [eval_ir_guards eval_ir_expr echo_ir_encode_kind echo_ir_signature
    echo_ir_message_kind_eq_dec ir_processes ir_global_fields
    ir_config_fields ir_message_kind ir_message_sender ir_message_receiver
    ir_event_message echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    echo_ir_encode_message echo_ir_delivery_certificates ir_value_eqb].
  rewrite receiver_is_initiator, protocol_started, initiator_parent_none,
    sender_pending_true, initiator_unfinished.
  unfold ir_node_eqb, ir_option_node_eqb.
  destruct (node_eq (config_initiator config) (config_initiator config))
    as [_ | impossible_receiver].
  - cbn. now rewrite pending_empty.
  - contradiction.
Qed.

Lemma echo_ir_initiator_reply_final_action_forward
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoInitiatorReplyFinal message) successor ->
  exists ir_successor,
    eval_ir_action node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoInitiatorReplyFinal message)))
      (ir_rule_action (@echo_ir_initiator_reply_final_rule node)) =
        Some ir_successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyFinal message)
    initiator_ack_final_rule
    (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [initiator_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as receiver_is_initiator.
  cbn [guard_holds eval_node_expr event_message] in receiver_is_initiator.
  pose proof (@EchoStep_selected_action node node_eq config
    state successor (EchoInitiatorReplyFinal message)
    initiator_ack_final_rule step eq_refl) as old_action.
  unfold initiator_ack_final_rule in old_action.
  cbn [EchoTransitionIR.eval_action EchoTransitionIR.ir_rule_action
    EchoTransitionIR.eval_process_expr EchoTransitionIR.eval_parent_expr
    EchoTransitionIR.eval_nodes_expr EchoTransitionIR.eval_node_expr
    EchoTransitionIR.eval_outbound_expr EchoTransitionIR.event_message]
    in old_action.
  unfold apply_echo_delivery in old_action.
  cbn in old_action.
  rewrite receiver_is_initiator in old_action.
  subst successor.
  unfold echo_ir_initiator_reply_final_rule.
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
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  cbn [ir_config_fields echo_ir_encode_config echo_ir_encode_config_fields
    eval_ir_expr eval_ir_action ir_set_local_field
    ir_remove_selected_message].
  eexists. split.
  - reflexivity.
  - unfold echo_ir_states_correspond.
    repeat split.
    + intros process field.
      cbn [ir_remove_selected_message ir_processes processes].
      destruct (node_eq (config_initiator config) process)
        as [same | different].
      * subst process.
        rewrite echo_update_process_same.
        destruct field.
        -- cbn [ir_set_local_field ir_processes processes
             echo_ir_encode_process].
           repeat rewrite ir_update_processes_same.
           rewrite ir_update_field_different by discriminate.
           rewrite ir_update_field_different by discriminate.
           rewrite ir_update_field_same. reflexivity.
        -- cbn [ir_set_local_field ir_processes processes
             echo_ir_encode_process].
           repeat rewrite ir_update_processes_same.
           rewrite ir_update_field_different by discriminate.
           rewrite ir_update_field_same. reflexivity.
        -- cbn [ir_set_local_field ir_processes processes
             echo_ir_encode_process].
           rewrite ir_update_processes_same.
           rewrite ir_update_field_same. reflexivity.
      * rewrite echo_update_process_different by exact different.
        cbn [ir_set_local_field ir_processes processes
          echo_ir_encode_process].
        repeat rewrite ir_update_processes_different by exact different.
        reflexivity.
    + cbn [ir_remove_selected_message ir_message_store message_store
        echo_ir_encode_state ir_set_local_field].
      rewrite echo_ir_remove_message_encoding.
      now rewrite app_nil_r.
    + cbn [ir_remove_selected_message ir_set_local_field
        ir_next_message_id next_message_id echo_ir_encode_state].
      unfold next_echo_message_id_after.
      now rewrite Nat.add_0_r.
Qed.

Lemma echo_ir_initiator_reply_more_disabled_on_final
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoInitiatorReplyFinal message) successor ->
  eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoInitiatorReplyFinal message)))
      (@echo_ir_initiator_reply_more_rule node) = IRRuleDisabled.
Proof.
  intro step.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyFinal message)
    initiator_ack_final_rule (IRGuardKind EchoReply)
    step eq_refl ltac:(
      cbn [initiator_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as reply_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyFinal message)
    initiator_ack_final_rule
    (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [initiator_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as receiver_is_initiator.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyFinal message)
    initiator_ack_final_rule (IRGuardStarted true)
    step eq_refl ltac:(
      cbn [initiator_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as protocol_started.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyFinal message)
    initiator_ack_final_rule
    (IRGuardParentEqual IRInitiatorNode IRNoParent)
    step eq_refl ltac:(
      cbn [initiator_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as initiator_parent_none.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyFinal message)
    initiator_ack_final_rule
    (IRGuardNodeIn IRMessageSender (IRNodesPending IRInitiatorNode))
    step eq_refl ltac:(
      cbn [initiator_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as sender_pending.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyFinal message)
    initiator_ack_final_rule
    (IRGuardNodesEmpty
      (IRNodesRemove IRMessageSender (IRNodesPending IRInitiatorNode)))
    step eq_refl ltac:(
      cbn [initiator_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as pending_empty.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyFinal message)
    initiator_ack_final_rule
    (IRGuardFinished IRInitiatorNode false)
    step eq_refl ltac:(
      cbn [initiator_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as initiator_unfinished.
  cbn [guard_holds eval_node_expr eval_parent_expr eval_nodes_expr
    event_message] in reply_kind, receiver_is_initiator, protocol_started,
    initiator_parent_none, sender_pending, pending_empty,
    initiator_unfinished.
  rewrite <- echo_ir_remove_node_agrees in pending_empty.
  pose proof (echo_ir_node_in_true_of_in
    (message_sender message)
    (process_pending (processes state (config_initiator config)))
    sender_pending) as sender_pending_true.
  unfold eval_ir_rule, echo_ir_initiator_reply_more_rule.
  unfold echo_ir_equal, echo_ir_receiver, echo_ir_initiator,
    echo_ir_started, echo_ir_parent, echo_ir_option_none,
    echo_ir_sender, echo_ir_pending, echo_ir_nonempty, echo_ir_is_empty,
    echo_ir_removed_pending, echo_ir_finished, echo_ir_bool,
    echo_ir_remove.
  cbn [ir_rule_pattern ir_rule_guards ir_event_pattern_matches eval_ir_guards
    eval_ir_expr echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    echo_ir_encode_message echo_ir_encode_kind echo_ir_delivery_certificates
    echo_ir_event_forward_order echo_ir_event_expected_parent ir_value_eqb
    ir_processes ir_global_fields ir_config_fields ir_config_neighbors
    ir_message_kind ir_message_sender ir_message_receiver ir_event_message
    echo_ir_signature echo_ir_local_field_type echo_ir_global_field_type
    echo_ir_config_field_type echo_ir_delivery_certificate_field_type].
  rewrite reply_kind.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRReply EchoIRReply) as [_ | impossible_kind].
  2: contradiction.
  cbn [eval_ir_guards eval_ir_expr echo_ir_encode_kind echo_ir_signature
    echo_ir_message_kind_eq_dec ir_processes ir_global_fields
    ir_config_fields ir_message_kind ir_message_sender ir_message_receiver
    ir_event_message echo_ir_encode_config echo_ir_encode_config_fields
    echo_ir_encode_state echo_ir_encode_process echo_ir_encode_globals
    echo_ir_encode_message echo_ir_delivery_certificates ir_value_eqb].
  rewrite receiver_is_initiator, protocol_started, initiator_parent_none,
    sender_pending_true, initiator_unfinished.
  unfold ir_node_eqb, ir_option_node_eqb.
  destruct (node_eq (config_initiator config) (config_initiator config))
    as [_ | impossible_receiver].
  2: contradiction.
  cbn. now rewrite pending_empty.
Qed.

Lemma echo_ir_initiator_reply_final_rule_selected
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @EchoStep node node_eq config state
      (EchoInitiatorReplyFinal message) successor ->
  select_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoInitiatorReplyFinal message)))
      (@echo_ir_rules node) =
    IRUniqueRuleSelected (@echo_ir_initiator_reply_final_rule node).
Proof.
  intro step.
  pose proof (echo_ir_initiator_reply_final_rule_enabled
    state successor message step) as enabled.
  pose proof (echo_ir_initiator_reply_more_disabled_on_final
    state successor message step) as more_disabled.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyFinal message)
    initiator_ack_final_rule (IRGuardKind EchoReply)
    step eq_refl ltac:(
      cbn [initiator_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as reply_kind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyFinal message)
    initiator_ack_final_rule
    (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
    step eq_refl ltac:(
      cbn [initiator_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as receiver_is_initiator.
  cbn [guard_holds eval_node_expr event_message]
    in reply_kind, receiver_is_initiator.
  pose proof (echo_ir_request_rules_select_none_on_reply
    state message
    (@echo_ir_delivery_certificates node config
      (EchoInitiatorReplyFinal message))
    reply_kind) as request_prefix_none.
  pose proof (echo_ir_participant_reply_rules_select_none_for_initiator
    state message
    (@echo_ir_delivery_certificates node config
      (EchoInitiatorReplyFinal message))
    reply_kind receiver_is_initiator) as participant_prefix_none.
  assert (start_mismatch :
    eval_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoInitiatorReplyFinal message)))
      (@echo_ir_start_rule node) = IRRuleMismatch).
  {
    unfold eval_ir_rule, echo_ir_start_rule.
    reflexivity.
  }
  unfold echo_ir_rules.
  erewrite select_ir_rule_cons_mismatch; [| exact start_mismatch].
  change
    (select_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoInitiatorReplyFinal message)))
      ([@echo_ir_first_request_nonleaf_rule node;
        @echo_ir_first_request_leaf_rule node;
        @echo_ir_repeated_request_rule node;
        @echo_ir_initiator_request_rule node] ++
       [@echo_ir_participant_reply_more_rule node;
        @echo_ir_participant_reply_final_rule node;
        @echo_ir_initiator_reply_more_rule node;
        @echo_ir_initiator_reply_final_rule node]) =
     IRUniqueRuleSelected (@echo_ir_initiator_reply_final_rule node)).
  erewrite select_ir_rule_app_none; [| exact request_prefix_none].
  change
    (select_ir_rule node_eq (echo_ir_encode_config config)
      (echo_ir_encode_state state)
      (IRRuntimeDeliver (@echo_ir_encode_message node message)
        (@echo_ir_delivery_certificates node config
          (EchoInitiatorReplyFinal message)))
      ([@echo_ir_participant_reply_more_rule node;
        @echo_ir_participant_reply_final_rule node] ++
       [@echo_ir_initiator_reply_more_rule node;
        @echo_ir_initiator_reply_final_rule node]) =
     IRUniqueRuleSelected (@echo_ir_initiator_reply_final_rule node)).
  erewrite select_ir_rule_app_none; [| exact participant_prefix_none].
  erewrite select_ir_rule_cons_disabled; [| exact more_disabled].
  now apply select_ir_rule_cons_unique.
Qed.

Theorem echo_ir_initiator_reply_final_forward_simulates
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  @echo_reachable node node_eq config state ->
  @EchoStep node node_eq config state
      (EchoInitiatorReplyFinal message) successor ->
  exists ir_successor,
    interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state)
      (echo_ir_encode_event config (EchoInitiatorReplyFinal message)) =
      @IRStepSuccess node echo_ir_signature
        EchoIRInitiatorReplyFinalRule ir_successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intros reachable step.
  pose proof (@echo_ir_resolve_successful_delivery
    node node_eq config state successor (EchoInitiatorReplyFinal message)
    reachable step I) as resolved.
  pose proof (echo_ir_initiator_reply_final_rule_selected
    state successor message step) as selected.
  destruct (echo_ir_initiator_reply_final_action_forward
    state successor message step) as
    [ir_successor [action correspondence]].
  exists ir_successor. split.
  - unfold interpret_protocol_rules.
    rewrite resolved.
    cbn [event_message].
    rewrite selected, action. reflexivity.
  - exact correspondence.
Qed.

(** Every reachable successful step of the retired Echo-specific executable
    model is reproduced by interpreting the generic Echo IR program.  The old
    event constructor is used only to state which generic rule ID must be
    reported; generic rule selection itself receives no branch tag. *)
Theorem echo_ir_forward_simulates
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  @echo_reachable node node_eq config state ->
  @EchoStep node node_eq config state event successor ->
  exists ir_successor,
    interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) (echo_ir_encode_state state)
      (echo_ir_encode_event config event) =
      @IRStepSuccess node echo_ir_signature
        (echo_ir_rule_id_for_event event) ir_successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intros reachable step.
  destruct event as
    [ordered_neighbors
    |message ordered_forwards
    |message
    |message
    |message
    |message parent
    |message parent
    |message
    |message].
  - cbn [echo_ir_rule_id_for_event].
    now apply echo_ir_start_forward_simulates.
  - cbn [echo_ir_rule_id_for_event].
    now apply echo_ir_first_request_nonleaf_forward_simulates.
  - cbn [echo_ir_rule_id_for_event].
    now apply echo_ir_first_request_leaf_forward_simulates.
  - cbn [echo_ir_rule_id_for_event].
    now apply echo_ir_repeated_request_forward_simulates.
  - cbn [echo_ir_rule_id_for_event].
    now apply echo_ir_initiator_request_forward_simulates.
  - cbn [echo_ir_rule_id_for_event].
    now apply echo_ir_participant_reply_more_forward_simulates.
  - cbn [echo_ir_rule_id_for_event].
    now apply echo_ir_participant_reply_final_forward_simulates.
  - cbn [echo_ir_rule_id_for_event].
    now apply echo_ir_initiator_reply_more_forward_simulates.
  - cbn [echo_ir_rule_id_for_event].
    now apply echo_ir_initiator_reply_final_forward_simulates.
Qed.

Lemma echo_ir_states_correspond_iff_equivalent
    (echo_state : @executable_echo_state node)
    (ir_state : ir_protocol_state node echo_ir_signature) :
  echo_ir_states_correspond echo_state ir_state <->
  ir_states_equivalent ir_state (echo_ir_encode_state echo_state).
Proof.
  unfold echo_ir_states_correspond, ir_states_equivalent.
  cbn [echo_ir_encode_state ir_processes ir_message_store
    ir_global_fields ir_next_message_id].
  tauto.
Qed.

(** The branch theorem is stable under the observational state relation, so a
    simulated execution can continue from the generic successor produced by
    its previous step rather than restarting from a freshly encoded state. *)
Theorem echo_ir_forward_simulates_from_corresponding_state
    (state successor : @executable_echo_state node)
    (ir_state : ir_protocol_state node echo_ir_signature)
    (event : @echo_event node) :
  @echo_reachable node node_eq config state ->
  echo_ir_states_correspond state ir_state ->
  @EchoStep node node_eq config state event successor ->
  exists ir_successor,
    interpret_protocol_rules node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node) ir_state (echo_ir_encode_event config event) =
      @IRStepSuccess node echo_ir_signature
        (echo_ir_rule_id_for_event event) ir_successor /\
    echo_ir_states_correspond successor ir_successor.
Proof.
  intros reachable correspondence step.
  destruct (echo_ir_forward_simulates state successor event reachable step)
    as [encoded_successor [encoded_step encoded_correspondence]].
  assert (inputs_equivalent :
    ir_states_equivalent (echo_ir_encode_state state) ir_state).
  {
    apply ir_states_equivalent_sym.
    now apply (proj1
      (echo_ir_states_correspond_iff_equivalent state ir_state)).
  }
  destruct (interpret_protocol_rules_respects_state_equivalence
    node_eq (echo_ir_encode_config config) (@echo_ir_rules node)
    (echo_ir_encode_state state) ir_state encoded_successor
    (echo_ir_encode_event config event)
    (echo_ir_rule_id_for_event event)
    inputs_equivalent encoded_step) as
    [ir_successor [ir_step successors_equivalent]].
  exists ir_successor. split.
  - exact ir_step.
  - apply (proj2
      (echo_ir_states_correspond_iff_equivalent successor ir_successor)).
    eapply ir_states_equivalent_trans.
    + exact (ir_states_equivalent_sym
        encoded_successor ir_successor successors_equivalent).
    + exact ((proj1
        (echo_ir_states_correspond_iff_equivalent
          successor encoded_successor)) encoded_correspondence).
Qed.

(** Every old reachable state has a genuinely chained generic execution from
    the generic program's initial state to an observationally corresponding
    state. *)
Theorem echo_ir_reachable_forward_simulates
    (state : @executable_echo_state node) :
  @echo_reachable node node_eq config state ->
  exists ir_state,
    ir_protocol_reachable node_eq (echo_ir_encode_config config)
      (@echo_ir_rules node)
      (initialize_ir_protocol (@echo_ir_program node)) ir_state /\
    echo_ir_states_correspond state ir_state.
Proof.
  intro reachable.
  induction reachable as
    [|before event after before_reachable
      [ir_before [ir_before_reachable before_correspondence]] step].
  - exists (initialize_ir_protocol (@echo_ir_program node)). split.
    + constructor.
    + rewrite <- echo_ir_encode_initial_state.
      apply echo_ir_encoded_state_corresponds.
  - destruct (echo_ir_forward_simulates_from_corresponding_state
      before after ir_before event before_reachable
      before_correspondence step) as
      [ir_after [ir_step after_correspondence]].
    exists ir_after. split.
    + eapply ir_protocol_reachable_trans.
      * exact ir_before_reachable.
      * eapply IRReachableStep.
        -- exact ir_step.
        -- constructor.
    + exact after_correspondence.
Qed.

End EchoIRForwardSimulation.

Arguments echo_ir_states_correspond {node} _ _.
Arguments echo_ir_rule_id_for_event {node} _.
