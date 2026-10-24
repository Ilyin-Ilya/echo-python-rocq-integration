(** * Rule selection and deterministic execution for the generic protocol IR *)

From Stdlib Require Import List Bool Arith.
Import ListNotations.
Require Import ProtocolIRTypes ProtocolIRExpressions ProtocolIRActions.

Inductive ir_event_pattern (signature : protocol_signature) : Type :=
  | IRStartPattern
  | IRDeliveryPattern (kind : signature_message_kind signature).

Arguments IRStartPattern {signature}.
Arguments IRDeliveryPattern {signature} _.

Record ir_rule
    (node : Type) (signature : protocol_signature) : Type :=
  mkIRRule {
    ir_rule_id : signature_rule_id signature;
    ir_rule_pattern : ir_event_pattern signature;
    ir_rule_guards : list (ir_expr node signature IRBool);
    ir_rule_action : ir_action node signature
  }.

Arguments mkIRRule {node signature} _ _ _ _.
Arguments ir_rule_id {node signature} _.
Arguments ir_rule_pattern {node signature} _.
Arguments ir_rule_guards {node signature} _.
Arguments ir_rule_action {node signature} _.

Definition ir_event_pattern_matches
    {node : Type} {signature : protocol_signature}
    (pattern : ir_event_pattern signature)
    (event : ir_runtime_event node signature) : bool :=
  match pattern, event with
  | IRStartPattern, IRRuntimeStart _ => true
  | IRDeliveryPattern expected, IRRuntimeDeliver message _ =>
      if signature_message_kind_eq_dec signature
          expected (ir_message_kind message)
      then true
      else false
  | _, _ => false
  end.

(** A value whose intrinsic type is [IRBool] has exactly the Boolean
    constructor.  Keeping this view lemma separate avoids importing
    proof-irrelevance-based dependent-destruction tactics into the kernel. *)
Definition ir_bool_value_view
    {node : Type}
    (value : ir_value node IRBool) :
  exists boolean, value = IRBoolValue boolean :=
  match value as current in ir_value _ kind
    return
      ((match kind as selected return ir_value node selected -> Prop with
        | IRBool =>
            fun typed => exists boolean, typed = IRBoolValue boolean
        | _ => fun _ => True
        end) current)
  with
  | IRBoolValue boolean => ex_intro _ boolean eq_refl
  | IRNatValue _
  | IRNodeValue _
  | IROptionNodeValue _
  | IRListNodeValue _
  | IRMessageRefValue _ => I
  end.

Fixpoint eval_ir_guards
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (state : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (guards : list (ir_expr node signature IRBool)) : option bool :=
  match guards with
  | [] => Some true
  | guard :: rest =>
      match eval_ir_expr node_eq_dec config state event guard with
      | Some (IRBoolValue true) =>
          eval_ir_guards node_eq_dec config state event rest
      | Some (IRBoolValue false) => Some false
      | Some _ => None
      | None => None
      end
  end.

Lemma eval_ir_guards_true_member
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (state : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (guards : list (ir_expr node signature IRBool)) :
  eval_ir_guards node_eq_dec config state event guards = Some true ->
  forall guard,
    In guard guards ->
    eval_ir_expr node_eq_dec config state event guard =
      Some (IRBoolValue true).
Proof.
  induction guards as [|first rest IH];
    intros evaluated guard member; cbn in evaluated, member.
  - contradiction.
  - destruct (eval_ir_expr node_eq_dec config state event first)
      as [value |] eqn:first_result; try discriminate.
    destruct (ir_bool_value_view value) as [boolean value_shape].
    subst value. destruct boolean; try discriminate.
    destruct member as [same | in_rest].
    + now subst guard.
    + now apply (IH evaluated guard in_rest).
Qed.

Inductive ir_rule_status : Type :=
  | IRRuleMismatch
  | IRRuleDisabled
  | IRRuleEnabled
  | IRRuleMalformed.

Definition eval_ir_rule
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (state : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (rule : ir_rule node signature) : ir_rule_status :=
  if ir_event_pattern_matches (ir_rule_pattern rule) event
  then
    match eval_ir_guards
      node_eq_dec config state event (ir_rule_guards rule) with
    | Some true => IRRuleEnabled
    | Some false => IRRuleDisabled
    | None => IRRuleMalformed
    end
  else IRRuleMismatch.

Theorem eval_ir_rule_enabled_guard
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (state : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (rule : ir_rule node signature)
    (guard : ir_expr node signature IRBool) :
  eval_ir_rule node_eq_dec config state event rule = IRRuleEnabled ->
  In guard (ir_rule_guards rule) ->
  eval_ir_expr node_eq_dec config state event guard =
    Some (IRBoolValue true).
Proof.
  unfold eval_ir_rule.
  destruct (ir_event_pattern_matches (ir_rule_pattern rule) event);
    try discriminate.
  destruct (eval_ir_guards node_eq_dec config state event
    (ir_rule_guards rule)) as [guards_hold |] eqn:guards_result;
    try discriminate.
  destruct guards_hold; try discriminate.
  intros _ member.
  eapply eval_ir_guards_true_member; eauto.
Qed.

Theorem eval_ir_rule_enabled_pattern
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (state : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (rule : ir_rule node signature) :
  eval_ir_rule node_eq_dec config state event rule = IRRuleEnabled ->
  ir_event_pattern_matches (ir_rule_pattern rule) event = true.
Proof.
  unfold eval_ir_rule.
  destruct (ir_event_pattern_matches (ir_rule_pattern rule) event);
    try discriminate.
  reflexivity.
Qed.

Theorem enabled_rules_with_complementary_guards_exclusive
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (state : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (positive_rule negated_rule : ir_rule node signature)
    (guard : ir_expr node signature IRBool) :
  In guard (ir_rule_guards positive_rule) ->
  In (IRNotExpr guard) (ir_rule_guards negated_rule) ->
  eval_ir_rule node_eq_dec config state event positive_rule =
    IRRuleEnabled ->
  eval_ir_rule node_eq_dec config state event negated_rule =
    IRRuleEnabled ->
  False.
Proof.
  intros positive_member negated_member positive_enabled negated_enabled.
  pose proof (eval_ir_rule_enabled_guard
    node_eq_dec config state event positive_rule guard
    positive_enabled positive_member) as positive.
  pose proof (eval_ir_rule_enabled_guard
    node_eq_dec config state event negated_rule (IRNotExpr guard)
    negated_enabled negated_member) as negated.
  exact (eval_ir_expr_not_both_true
    node_eq_dec config state event guard positive negated).
Qed.

Inductive ir_rule_selection
    (node : Type) (signature : protocol_signature) : Type :=
  | IRNoRuleSelected
  | IRUniqueRuleSelected (rule : ir_rule node signature)
  | IRAmbiguousRulesSelected
  | IRMalformedRuleObserved.

Arguments IRNoRuleSelected {node signature}.
Arguments IRUniqueRuleSelected {node signature} _.
Arguments IRAmbiguousRulesSelected {node signature}.
Arguments IRMalformedRuleObserved {node signature}.

Fixpoint select_ir_rule
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (state : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (rules : list (ir_rule node signature)) :
    ir_rule_selection node signature :=
  match rules with
  | [] => IRNoRuleSelected
  | rule :: rest =>
      match eval_ir_rule node_eq_dec config state event rule with
      | IRRuleMismatch
      | IRRuleDisabled =>
          select_ir_rule node_eq_dec config state event rest
      | IRRuleMalformed => IRMalformedRuleObserved
      | IRRuleEnabled =>
          match select_ir_rule node_eq_dec config state event rest with
          | IRNoRuleSelected => IRUniqueRuleSelected rule
          | IRUniqueRuleSelected _ => IRAmbiguousRulesSelected
          | IRAmbiguousRulesSelected => IRAmbiguousRulesSelected
          | IRMalformedRuleObserved => IRMalformedRuleObserved
          end
      end
  end.

Inductive ir_step_error : Type :=
  | IRUnqueuedMessage
  | IRNoEnabledRule
  | IRAmbiguousEnabledRules
  | IRMalformedGuard
  | IRMalformedAction.

Inductive ir_step_result
    (node : Type) (signature : protocol_signature) : Type :=
  | IRStepSuccess
      (rule : signature_rule_id signature)
      (successor : ir_protocol_state node signature)
  | IRStepFailure (error : ir_step_error).

Arguments IRStepSuccess {node signature} _ _.
Arguments IRStepFailure {node signature} _.

Definition interpret_protocol_rules
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (rules : list (ir_rule node signature))
    (state : ir_protocol_state node signature)
    (external_event : ir_external_event node signature) :
    ir_step_result node signature :=
  match ir_resolve_event state external_event with
  | None => IRStepFailure IRUnqueuedMessage
  | Some event =>
      match select_ir_rule node_eq_dec config state event rules with
      | IRNoRuleSelected => IRStepFailure IRNoEnabledRule
      | IRAmbiguousRulesSelected => IRStepFailure IRAmbiguousEnabledRules
      | IRMalformedRuleObserved => IRStepFailure IRMalformedGuard
      | IRUniqueRuleSelected rule =>
          match eval_ir_action
            node_eq_dec config state event (ir_rule_action rule) with
          | Some successor => IRStepSuccess (ir_rule_id rule) successor
          | None => IRStepFailure IRMalformedAction
          end
      end
  end.

(** A successful public interpreter result exposes the resolved event, the
    uniquely selected rule, and the action evaluation that produced the
    successor.  Protocol-specific reverse simulations can use this theorem
    without unfolding the interpreter at every call site. *)
Theorem interpret_protocol_rules_success_components
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (rules : list (ir_rule node signature))
    (state : ir_protocol_state node signature)
    (external_event : ir_external_event node signature)
    (rule_id : signature_rule_id signature)
    (successor : ir_protocol_state node signature) :
  interpret_protocol_rules node_eq_dec config rules state external_event =
    IRStepSuccess rule_id successor ->
  exists runtime_event selected_rule,
    ir_resolve_event state external_event = Some runtime_event /\
    select_ir_rule node_eq_dec config state runtime_event rules =
      IRUniqueRuleSelected selected_rule /\
    ir_rule_id selected_rule = rule_id /\
    eval_ir_action node_eq_dec config state runtime_event
      (ir_rule_action selected_rule) = Some successor.
Proof.
  unfold interpret_protocol_rules.
  destruct (ir_resolve_event state external_event)
    as [runtime_event |] eqn:resolved; try discriminate.
  destruct (select_ir_rule node_eq_dec config state runtime_event rules)
    as [|selected_rule| |] eqn:selected; try discriminate.
  destruct (eval_ir_action node_eq_dec config state runtime_event
      (ir_rule_action selected_rule))
    as [computed_successor |] eqn:action; try discriminate.
  intro interpreted. inversion interpreted. subst.
  exists runtime_event, selected_rule.
  repeat split; assumption.
Qed.

(** A successful generic protocol step cannot move the message allocator
    backwards.  The property follows from the selected action and therefore
    applies uniformly to every generated protocol program. *)
Theorem interpret_protocol_rules_next_message_id_monotone
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (rules : list (ir_rule node signature))
    (state successor : ir_protocol_state node signature)
    (external_event : ir_external_event node signature)
    (rule_id : signature_rule_id signature) :
  interpret_protocol_rules node_eq_dec config rules state external_event =
    IRStepSuccess rule_id successor ->
  ir_next_message_id state <= ir_next_message_id successor.
Proof.
  intro interpreted.
  destruct (interpret_protocol_rules_success_components
    node_eq_dec config rules state external_event rule_id successor
    interpreted) as
    [runtime_event [selected_rule
      [resolved [selected [identifier action]]]]].
  exact (eval_ir_action_next_message_id_monotone
    node_eq_dec config state successor runtime_event
    (ir_rule_action selected_rule) action).
Qed.

Lemma ir_resolve_event_respects_state_equivalence
    {node : Type} {signature : protocol_signature}
    (left right : ir_protocol_state node signature)
    (event : ir_external_event node signature) :
  ir_states_equivalent left right ->
  ir_resolve_event left event = ir_resolve_event right event.
Proof.
  intros [_ [messages_equal _]].
  destruct event; cbn; [reflexivity | now rewrite messages_equal].
Qed.

Lemma eval_ir_guards_respects_state_equivalence
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (left right : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (guards : list (ir_expr node signature IRBool)) :
  ir_states_equivalent left right ->
  eval_ir_guards node_eq_dec config left event guards =
    eval_ir_guards node_eq_dec config right event guards.
Proof.
  intro equivalent.
  induction guards as [|guard rest IH].
  - reflexivity.
  - cbn.
    rewrite (eval_ir_expr_respects_state_equivalence
      node_eq_dec config left right event _ guard equivalent).
    destruct (eval_ir_expr node_eq_dec config right event guard)
      as [value |] eqn:evaluated; try reflexivity.
    destruct value; try reflexivity.
    destruct b; [exact IH | reflexivity].
Qed.

Lemma eval_ir_rule_respects_state_equivalence
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (left right : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (rule : ir_rule node signature) :
  ir_states_equivalent left right ->
  eval_ir_rule node_eq_dec config left event rule =
    eval_ir_rule node_eq_dec config right event rule.
Proof.
  intro equivalent.
  unfold eval_ir_rule.
  destruct (ir_event_pattern_matches (ir_rule_pattern rule) event);
    try reflexivity.
  now rewrite (eval_ir_guards_respects_state_equivalence
    node_eq_dec config left right event (ir_rule_guards rule) equivalent).
Qed.

Lemma select_ir_rule_respects_state_equivalence
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (left right : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (rules : list (ir_rule node signature)) :
  ir_states_equivalent left right ->
  select_ir_rule node_eq_dec config left event rules =
    select_ir_rule node_eq_dec config right event rules.
Proof.
  intro equivalent.
  induction rules as [|rule rest IH].
  - reflexivity.
  - cbn.
    rewrite (eval_ir_rule_respects_state_equivalence
      node_eq_dec config left right event rule equivalent).
    now rewrite IH.
Qed.

(** A successful interpreter step transports across equivalent input states,
    reports the same rule identifier, and produces an equivalent successor. *)
Theorem interpret_protocol_rules_respects_state_equivalence
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (rules : list (ir_rule node signature))
    (left right left_successor : ir_protocol_state node signature)
    (external_event : ir_external_event node signature)
    (rule_id : signature_rule_id signature) :
  ir_states_equivalent left right ->
  interpret_protocol_rules node_eq_dec config rules left external_event =
    IRStepSuccess rule_id left_successor ->
  exists right_successor,
    interpret_protocol_rules node_eq_dec config rules right external_event =
      IRStepSuccess rule_id right_successor /\
    ir_states_equivalent left_successor right_successor.
Proof.
  intros equivalent interpreted.
  unfold interpret_protocol_rules in interpreted |- *.
  rewrite (ir_resolve_event_respects_state_equivalence
    left right external_event equivalent) in interpreted.
  destruct (ir_resolve_event right external_event)
    as [runtime_event |] eqn:resolved; try discriminate.
  rewrite (select_ir_rule_respects_state_equivalence
    node_eq_dec config left right runtime_event rules equivalent)
    in interpreted.
  destruct (select_ir_rule node_eq_dec config right runtime_event rules)
    as [|selected| |] eqn:selected_rule; try discriminate.
  destruct (eval_ir_action node_eq_dec config left runtime_event
      (ir_rule_action selected))
      as [computed_successor |] eqn:left_action; try discriminate.
  inversion interpreted. subst rule_id left_successor.
  destruct (eval_ir_action_respects_state_equivalence
    node_eq_dec config runtime_event (ir_rule_action selected)
    left right computed_successor equivalent left_action) as
    [right_successor [right_action successors_equivalent]].
  exists right_successor. split.
  - now rewrite right_action.
  - exact successors_equivalent.
Qed.

Definition protocol_step
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (rules : list (ir_rule node signature))
    (state : ir_protocol_state node signature)
    (event : ir_external_event node signature) :
    option (ir_protocol_state node signature) :=
  match interpret_protocol_rules node_eq_dec config rules state event with
  | IRStepSuccess _ successor => Some successor
  | IRStepFailure _ => None
  end.

Theorem protocol_step_deterministic
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (rules : list (ir_rule node signature))
    (state : ir_protocol_state node signature)
    (event : ir_external_event node signature)
    (left right : ir_protocol_state node signature) :
  protocol_step node_eq_dec config rules state event = Some left ->
  protocol_step node_eq_dec config rules state event = Some right ->
  left = right.
Proof.
  intros left_result right_result.
  rewrite left_result in right_result.
  now inversion right_result.
Qed.

Theorem select_ir_rule_unique_is_enabled
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (state : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (rules : list (ir_rule node signature))
    (selected : ir_rule node signature) :
  select_ir_rule node_eq_dec config state event rules =
    IRUniqueRuleSelected selected ->
  eval_ir_rule node_eq_dec config state event selected = IRRuleEnabled.
Proof.
  induction rules as [|rule rest IH]; cbn.
  - discriminate.
  - destruct (eval_ir_rule node_eq_dec config state event rule) eqn:status.
    + apply IH.
    + apply IH.
    + destruct (select_ir_rule node_eq_dec config state event rest)
        eqn:rest_selection; try discriminate.
      intro selected_rule. inversion selected_rule. subst selected.
      exact status.
    + discriminate.
Qed.

Theorem select_ir_rule_unique_in
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (state : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (rules : list (ir_rule node signature))
    (selected : ir_rule node signature) :
  select_ir_rule node_eq_dec config state event rules =
    IRUniqueRuleSelected selected ->
  In selected rules.
Proof.
  induction rules as [|rule rest IH]; cbn.
  - discriminate.
  - destruct (eval_ir_rule node_eq_dec config state event rule).
    + intro selected_from_rest. right. now apply IH.
    + intro selected_from_rest. right. now apply IH.
    + destruct (select_ir_rule node_eq_dec config state event rest);
        try discriminate.
      intro selected_rule. inversion selected_rule. now left.
    + discriminate.
Qed.

(** Pairwise-exclusive enabled rules and distinct rule identifiers are enough
    to rule out ambiguity for any concrete program. *)
Theorem select_ir_rule_not_ambiguous_if_pairwise
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (state : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (rules : list (ir_rule node signature)) :
  NoDup (List.map ir_rule_id rules) ->
  (forall first second,
    In first rules ->
    In second rules ->
    ir_rule_id first <> ir_rule_id second ->
    eval_ir_rule node_eq_dec config state event first = IRRuleEnabled ->
    eval_ir_rule node_eq_dec config state event second = IRRuleEnabled ->
    False) ->
  select_ir_rule node_eq_dec config state event rules <>
    IRAmbiguousRulesSelected.
Proof.
  induction rules as [|rule rest IH]; intros identifiers_unique exclusive.
  - discriminate.
  - inversion identifiers_unique as [|identifier identifiers
      identifier_not_in rest_identifiers_unique].
    cbn.
    destruct (eval_ir_rule node_eq_dec config state event rule)
        eqn:rule_status.
    + apply IH.
      * exact rest_identifiers_unique.
      * intros first second first_in second_in different.
        apply exclusive; [now right | now right | exact different].
    + apply IH.
      * exact rest_identifiers_unique.
      * intros first second first_in second_in different.
        apply exclusive; [now right | now right | exact different].
    + destruct (select_ir_rule node_eq_dec config state event rest)
        as [|selected| |] eqn:rest_selection; try discriminate.
      * intro ambiguous.
        pose proof (select_ir_rule_unique_in
          node_eq_dec config state event rest selected rest_selection)
          as selected_in.
        pose proof (select_ir_rule_unique_is_enabled
          node_eq_dec config state event rest selected rest_selection)
          as selected_enabled.
        eapply exclusive with (first := rule) (second := selected).
        -- now left.
        -- now right.
        -- intro same_identifier. apply identifier_not_in.
           rewrite same_identifier. now apply in_map.
        -- exact rule_status.
        -- exact selected_enabled.
      * exfalso.
        eapply IH.
        -- exact rest_identifiers_unique.
        -- intros first second first_in second_in different.
           apply exclusive; [now right | now right | exact different].
        -- reflexivity.
    + discriminate.
Qed.

Theorem resolved_delivery_was_queued
    {node : Type} {signature : protocol_signature}
    (state : ir_protocol_state node signature)
    (selected_id : nat)
    (certificates : ir_delivery_certificates node signature)
    (runtime_event : ir_runtime_event node signature) :
  ir_resolve_event state (IRProtocolDeliver selected_id certificates) =
    Some runtime_event ->
  exists message,
    In message (ir_message_store state) /\
    selected_id = ir_message_id message /\
    runtime_event = IRRuntimeDeliver message certificates.
Proof.
  cbn [ir_resolve_event].
  destruct (ir_find_message selected_id (ir_message_store state))
    as [message |] eqn:found.
  - intro resolved. inversion resolved. subst runtime_event.
    apply ir_find_message_sound in found as [queued identifier_matches].
    exists message. repeat split; assumption.
  - discriminate.
Qed.
