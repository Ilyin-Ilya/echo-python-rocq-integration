(** * Static uniqueness of generic Echo rule selection

    The proof is stronger than a reachable-state result: for every generic
    Echo state and resolved runtime event, at most one of the nine rule values
    can be enabled.  It relies only on complementary guards and event patterns,
    not on scheduler-selected branch tags. *)

From Stdlib Require Import List Bool Arith.
Import ListNotations.
Require Import ProtocolIRTypes ProtocolIRExpressions ProtocolIRActions
  ProtocolIRInterpreter EchoIRSignature EchoIRProgram.

Section EchoIRRuleUniqueness.

Variable node : Type.
Variable node_eq : forall left right : node,
  {left = right} + {left <> right}.
Variable config : ir_protocol_config node echo_ir_signature.
Variable state : ir_protocol_state node echo_ir_signature.
Variable event : ir_runtime_event node echo_ir_signature.

Local Notation echo_ir_start_rule := (@echo_ir_start_rule node).
Local Notation echo_ir_first_request_nonleaf_rule :=
  (@echo_ir_first_request_nonleaf_rule node).
Local Notation echo_ir_first_request_leaf_rule :=
  (@echo_ir_first_request_leaf_rule node).
Local Notation echo_ir_repeated_request_rule :=
  (@echo_ir_repeated_request_rule node).
Local Notation echo_ir_initiator_request_rule :=
  (@echo_ir_initiator_request_rule node).
Local Notation echo_ir_participant_reply_more_rule :=
  (@echo_ir_participant_reply_more_rule node).
Local Notation echo_ir_participant_reply_final_rule :=
  (@echo_ir_participant_reply_final_rule node).
Local Notation echo_ir_initiator_reply_more_rule :=
  (@echo_ir_initiator_reply_more_rule node).
Local Notation echo_ir_initiator_reply_final_rule :=
  (@echo_ir_initiator_reply_final_rule node).
Local Notation echo_ir_receiver := (@echo_ir_receiver node).
Local Notation echo_ir_initiator := (@echo_ir_initiator node).
Local Notation echo_ir_forward_targets := (@echo_ir_forward_targets node).
Local Notation echo_ir_process_seen := (@echo_ir_process_seen node).
Local Notation echo_ir_is_empty := (@echo_ir_is_empty node).
Local Notation echo_ir_removed_pending := (@echo_ir_removed_pending node).
Local Notation echo_ir_equal := (@echo_ir_equal node).

Local Definition enabled (rule : ir_rule node echo_ir_signature) : Prop :=
  eval_ir_rule node_eq config state event rule = IRRuleEnabled.

Lemma echo_ir_first_nonleaf_leaf_exclusive :
  enabled echo_ir_first_request_nonleaf_rule ->
  enabled echo_ir_first_request_leaf_rule ->
  False.
Proof.
  intros nonleaf leaf.
  eapply enabled_rules_with_complementary_guards_exclusive
    with (positive_rule := echo_ir_first_request_leaf_rule)
         (negated_rule := echo_ir_first_request_nonleaf_rule)
         (guard := echo_ir_is_empty echo_ir_forward_targets).
  - cbn [echo_ir_first_request_leaf_rule echo_ir_process_initial].
    repeat (first [left; reflexivity | right]).
  - cbn [echo_ir_first_request_nonleaf_rule echo_ir_process_initial
      echo_ir_nonempty].
    repeat (first [left; reflexivity | right]).
  - exact leaf.
  - exact nonleaf.
Qed.

Lemma echo_ir_first_nonleaf_repeated_exclusive :
  enabled echo_ir_first_request_nonleaf_rule ->
  enabled echo_ir_repeated_request_rule ->
  False.
Proof.
  intros first repeated.
  eapply enabled_rules_with_complementary_guards_exclusive
    with (positive_rule := echo_ir_repeated_request_rule)
         (negated_rule := echo_ir_first_request_nonleaf_rule)
         (guard := echo_ir_process_seen echo_ir_receiver).
  - cbn [echo_ir_repeated_request_rule].
    repeat (first [left; reflexivity | right]).
  - cbn [echo_ir_first_request_nonleaf_rule echo_ir_process_initial].
    repeat (first [left; reflexivity | right]).
  - exact repeated.
  - exact first.
Qed.

Lemma echo_ir_first_leaf_repeated_exclusive :
  enabled echo_ir_first_request_leaf_rule ->
  enabled echo_ir_repeated_request_rule ->
  False.
Proof.
  intros first repeated.
  eapply enabled_rules_with_complementary_guards_exclusive
    with (positive_rule := echo_ir_repeated_request_rule)
         (negated_rule := echo_ir_first_request_leaf_rule)
         (guard := echo_ir_process_seen echo_ir_receiver).
  - cbn [echo_ir_repeated_request_rule].
    repeat (first [left; reflexivity | right]).
  - cbn [echo_ir_first_request_leaf_rule echo_ir_process_initial].
    repeat (first [left; reflexivity | right]).
  - exact repeated.
  - exact first.
Qed.

Lemma echo_ir_first_nonleaf_initiator_exclusive :
  enabled echo_ir_first_request_nonleaf_rule ->
  enabled echo_ir_initiator_request_rule ->
  False.
Proof.
  intros participant initiator.
  eapply enabled_rules_with_complementary_guards_exclusive
    with (positive_rule := echo_ir_initiator_request_rule)
         (negated_rule := echo_ir_first_request_nonleaf_rule)
         (guard := echo_ir_equal echo_ir_receiver echo_ir_initiator).
  - cbn [echo_ir_initiator_request_rule].
    repeat (first [left; reflexivity | right]).
  - cbn [echo_ir_first_request_nonleaf_rule echo_ir_not_equal].
    repeat (first [left; reflexivity | right]).
  - exact initiator.
  - exact participant.
Qed.

Lemma echo_ir_first_leaf_initiator_exclusive :
  enabled echo_ir_first_request_leaf_rule ->
  enabled echo_ir_initiator_request_rule ->
  False.
Proof.
  intros participant initiator.
  eapply enabled_rules_with_complementary_guards_exclusive
    with (positive_rule := echo_ir_initiator_request_rule)
         (negated_rule := echo_ir_first_request_leaf_rule)
         (guard := echo_ir_equal echo_ir_receiver echo_ir_initiator).
  - cbn [echo_ir_initiator_request_rule].
    repeat (first [left; reflexivity | right]).
  - cbn [echo_ir_first_request_leaf_rule echo_ir_not_equal].
    repeat (first [left; reflexivity | right]).
  - exact initiator.
  - exact participant.
Qed.

Lemma echo_ir_repeated_initiator_exclusive :
  enabled echo_ir_repeated_request_rule ->
  enabled echo_ir_initiator_request_rule ->
  False.
Proof.
  intros participant initiator.
  eapply enabled_rules_with_complementary_guards_exclusive
    with (positive_rule := echo_ir_initiator_request_rule)
         (negated_rule := echo_ir_repeated_request_rule)
         (guard := echo_ir_equal echo_ir_receiver echo_ir_initiator).
  - cbn [echo_ir_initiator_request_rule].
    repeat (first [left; reflexivity | right]).
  - cbn [echo_ir_repeated_request_rule echo_ir_not_equal].
    repeat (first [left; reflexivity | right]).
  - exact initiator.
  - exact participant.
Qed.

Lemma echo_ir_participant_reply_more_final_exclusive :
  enabled echo_ir_participant_reply_more_rule ->
  enabled echo_ir_participant_reply_final_rule ->
  False.
Proof.
  intros more final.
  eapply enabled_rules_with_complementary_guards_exclusive
    with (positive_rule := echo_ir_participant_reply_final_rule)
         (negated_rule := echo_ir_participant_reply_more_rule)
         (guard := echo_ir_is_empty
           (echo_ir_removed_pending echo_ir_receiver)).
  - cbn [echo_ir_participant_reply_final_rule].
    repeat (first [left; reflexivity | right]).
  - cbn [echo_ir_participant_reply_more_rule echo_ir_nonempty].
    repeat (first [left; reflexivity | right]).
  - exact final.
  - exact more.
Qed.

Lemma echo_ir_initiator_reply_more_final_exclusive :
  enabled echo_ir_initiator_reply_more_rule ->
  enabled echo_ir_initiator_reply_final_rule ->
  False.
Proof.
  intros more final.
  eapply enabled_rules_with_complementary_guards_exclusive
    with (positive_rule := echo_ir_initiator_reply_final_rule)
         (negated_rule := echo_ir_initiator_reply_more_rule)
         (guard := echo_ir_is_empty
           (echo_ir_removed_pending echo_ir_initiator)).
  - cbn [echo_ir_initiator_reply_final_rule].
    repeat (first [left; reflexivity | right]).
  - cbn [echo_ir_initiator_reply_more_rule echo_ir_nonempty].
    repeat (first [left; reflexivity | right]).
  - exact final.
  - exact more.
Qed.

Lemma echo_ir_participant_more_initiator_more_exclusive :
  enabled echo_ir_participant_reply_more_rule ->
  enabled echo_ir_initiator_reply_more_rule ->
  False.
Proof.
  intros participant initiator.
  eapply enabled_rules_with_complementary_guards_exclusive
    with (positive_rule := echo_ir_initiator_reply_more_rule)
         (negated_rule := echo_ir_participant_reply_more_rule)
         (guard := echo_ir_equal echo_ir_receiver echo_ir_initiator).
  - cbn [echo_ir_initiator_reply_more_rule].
    repeat (first [left; reflexivity | right]).
  - cbn [echo_ir_participant_reply_more_rule echo_ir_not_equal].
    repeat (first [left; reflexivity | right]).
  - exact initiator.
  - exact participant.
Qed.

Lemma echo_ir_participant_more_initiator_final_exclusive :
  enabled echo_ir_participant_reply_more_rule ->
  enabled echo_ir_initiator_reply_final_rule ->
  False.
Proof.
  intros participant initiator.
  eapply enabled_rules_with_complementary_guards_exclusive
    with (positive_rule := echo_ir_initiator_reply_final_rule)
         (negated_rule := echo_ir_participant_reply_more_rule)
         (guard := echo_ir_equal echo_ir_receiver echo_ir_initiator).
  - cbn [echo_ir_initiator_reply_final_rule].
    repeat (first [left; reflexivity | right]).
  - cbn [echo_ir_participant_reply_more_rule echo_ir_not_equal].
    repeat (first [left; reflexivity | right]).
  - exact initiator.
  - exact participant.
Qed.

Lemma echo_ir_participant_final_initiator_more_exclusive :
  enabled echo_ir_participant_reply_final_rule ->
  enabled echo_ir_initiator_reply_more_rule ->
  False.
Proof.
  intros participant initiator.
  eapply enabled_rules_with_complementary_guards_exclusive
    with (positive_rule := echo_ir_initiator_reply_more_rule)
         (negated_rule := echo_ir_participant_reply_final_rule)
         (guard := echo_ir_equal echo_ir_receiver echo_ir_initiator).
  - cbn [echo_ir_initiator_reply_more_rule].
    repeat (first [left; reflexivity | right]).
  - cbn [echo_ir_participant_reply_final_rule echo_ir_not_equal].
    repeat (first [left; reflexivity | right]).
  - exact initiator.
  - exact participant.
Qed.

Lemma echo_ir_participant_final_initiator_final_exclusive :
  enabled echo_ir_participant_reply_final_rule ->
  enabled echo_ir_initiator_reply_final_rule ->
  False.
Proof.
  intros participant initiator.
  eapply enabled_rules_with_complementary_guards_exclusive
    with (positive_rule := echo_ir_initiator_reply_final_rule)
         (negated_rule := echo_ir_participant_reply_final_rule)
         (guard := echo_ir_equal echo_ir_receiver echo_ir_initiator).
  - cbn [echo_ir_initiator_reply_final_rule].
    repeat (first [left; reflexivity | right]).
  - cbn [echo_ir_participant_reply_final_rule echo_ir_not_equal].
    repeat (first [left; reflexivity | right]).
  - exact initiator.
  - exact participant.
Qed.

Lemma echo_ir_rule_ids_nodup :
  NoDup (List.map ir_rule_id (@echo_ir_rules node)).
Proof.
  repeat constructor; cbn; intros member;
    repeat destruct member as [same | member]; try contradiction;
    discriminate.
Qed.

(** Within the concrete Echo program, rule identifiers are an injective key.
    Reverse-simulation proofs can therefore recover the actual selected rule
    value from the identifier reported at the public interpreter boundary. *)
Lemma echo_ir_rule_identifier_injective
    (left right : ir_rule node echo_ir_signature) :
  In left (@echo_ir_rules node) ->
  In right (@echo_ir_rules node) ->
  ir_rule_id left = ir_rule_id right ->
  left = right.
Proof.
  intros left_in right_in same_identifier.
  cbn [echo_ir_rules] in left_in, right_in.
  repeat destruct left_in as [same | left_in]; try contradiction;
    subst left;
    repeat destruct right_in as [same | right_in]; try contradiction;
    subst right;
    cbn [echo_ir_start_rule echo_ir_first_request_nonleaf_rule
      echo_ir_first_request_leaf_rule echo_ir_repeated_request_rule
      echo_ir_initiator_request_rule echo_ir_participant_reply_more_rule
      echo_ir_participant_reply_final_rule echo_ir_initiator_reply_more_rule
      echo_ir_initiator_reply_final_rule ir_rule_id] in same_identifier;
    try discriminate; reflexivity.
Qed.

Lemma echo_ir_distinct_enabled_rules_exclusive
    (first second : ir_rule node echo_ir_signature) :
  In first (@echo_ir_rules node) ->
  In second (@echo_ir_rules node) ->
  ir_rule_id first <> ir_rule_id second ->
  enabled first ->
  enabled second ->
  False.
Proof.
  intros first_in second_in identifiers_different first_enabled second_enabled.
  cbn [echo_ir_rules] in first_in, second_in.
  repeat destruct first_in as [same | first_in]; try contradiction;
    subst first;
    repeat destruct second_in as [same | second_in]; try contradiction;
    subst second.
  all: try solve [apply identifiers_different; reflexivity].
  all: try solve [eauto using
    echo_ir_first_nonleaf_leaf_exclusive,
    echo_ir_first_nonleaf_repeated_exclusive,
    echo_ir_first_leaf_repeated_exclusive,
    echo_ir_first_nonleaf_initiator_exclusive,
    echo_ir_first_leaf_initiator_exclusive,
    echo_ir_repeated_initiator_exclusive,
    echo_ir_participant_reply_more_final_exclusive,
    echo_ir_initiator_reply_more_final_exclusive,
    echo_ir_participant_more_initiator_more_exclusive,
    echo_ir_participant_more_initiator_final_exclusive,
    echo_ir_participant_final_initiator_more_exclusive,
    echo_ir_participant_final_initiator_final_exclusive].
  all:
    pose proof (eval_ir_rule_enabled_pattern
      node_eq config state event _ first_enabled) as first_pattern;
    pose proof (eval_ir_rule_enabled_pattern
      node_eq config state event _ second_enabled) as second_pattern;
    destruct event as [|start_certificates|message delivery_certificates];
    cbn [echo_ir_start_rule echo_ir_first_request_nonleaf_rule
      echo_ir_first_request_leaf_rule echo_ir_repeated_request_rule
      echo_ir_initiator_request_rule echo_ir_participant_reply_more_rule
      echo_ir_participant_reply_final_rule echo_ir_initiator_reply_more_rule
      echo_ir_initiator_reply_final_rule ir_event_pattern_matches]
      in first_pattern, second_pattern;
    try discriminate;
    destruct message as [identifier kind sender receiver payload];
    destruct kind;
    cbn [echo_ir_start_rule echo_ir_first_request_nonleaf_rule
      echo_ir_first_request_leaf_rule echo_ir_repeated_request_rule
      echo_ir_initiator_request_rule echo_ir_participant_reply_more_rule
      echo_ir_participant_reply_final_rule echo_ir_initiator_reply_more_rule
      echo_ir_initiator_reply_final_rule ir_event_pattern_matches]
      in first_pattern, second_pattern;
    discriminate.
Qed.

Theorem echo_ir_rule_selection_unambiguous :
  select_ir_rule node_eq config state event (@echo_ir_rules node) <>
    IRAmbiguousRulesSelected.
Proof.
  eapply select_ir_rule_not_ambiguous_if_pairwise.
  - apply echo_ir_rule_ids_nodup.
  - exact echo_ir_distinct_enabled_rules_exclusive.
Qed.

End EchoIRRuleUniqueness.

Section EchoIRInterpreterUniqueness.

Variable node : Type.
Variable node_eq : forall left right : node,
  {left = right} + {left <> right}.
Variable config : ir_protocol_config node echo_ir_signature.
Variable state : ir_protocol_state node echo_ir_signature.

(** The property is visible at the public interpreter boundary as well: an
    external start or delivery may still be rejected for another reason, but
    never because two Echo rules were enabled together. *)
Theorem echo_ir_interpreter_never_reports_ambiguity
    (external_event : ir_external_event node echo_ir_signature) :
  interpret_protocol_rules node_eq config (@echo_ir_rules node) state
      external_event <>
    IRStepFailure IRAmbiguousEnabledRules.
Proof.
  intro interpreted.
  unfold interpret_protocol_rules in interpreted.
  destruct (ir_resolve_event state external_event)
    as [resolved |] eqn:resolved_event; try discriminate.
  destruct (select_ir_rule node_eq config state resolved
    (@echo_ir_rules node)) as [|selected_rule| |]
    eqn:selected; try discriminate.
  - destruct (eval_ir_action node_eq config state resolved
      (ir_rule_action selected_rule)); discriminate.
  - exact (@echo_ir_rule_selection_unambiguous
      node node_eq config state resolved selected).
Qed.

End EchoIRInterpreterUniqueness.
