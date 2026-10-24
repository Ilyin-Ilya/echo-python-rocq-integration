(** * Immutable actions for the protocol-neutral transition IR *)

From Stdlib Require Import List Bool Arith Lia.
Import ListNotations.
Require Import ProtocolIRTypes ProtocolIRExpressions.

Inductive ir_payload_expr_entry
    (node : Type) (signature : protocol_signature) : Type :=
  | mkIRPayloadExprEntry :
      forall field : signature_payload_field signature,
      ir_expr node signature
        (signature_payload_field_type signature field) ->
      ir_payload_expr_entry node signature.

Arguments mkIRPayloadExprEntry {node signature} _ _.

Definition ir_payload_exprs
    (node : Type) (signature : protocol_signature) : Type :=
  list (ir_payload_expr_entry node signature).

Inductive ir_action
    (node : Type) (signature : protocol_signature) : Type :=
  | IRSkipAction : ir_action node signature
  | IRSetGlobalAction :
      forall field : signature_global_field signature,
      ir_expr node signature
        (signature_global_field_type signature field) ->
      ir_action node signature
  | IRSetLocalAction :
      ir_expr node signature IRNode ->
      forall field : signature_local_field signature,
      ir_expr node signature
        (signature_local_field_type signature field) ->
      ir_action node signature
  | IRRemoveSelectedMessageAction : ir_action node signature
  | IREmitAction :
      signature_message_kind signature ->
      ir_expr node signature IRNode ->
      ir_expr node signature IRNode ->
      ir_payload_exprs node signature ->
      ir_action node signature
  | IREmitManyAction :
      signature_message_kind signature ->
      ir_expr node signature IRNode ->
      ir_expr node signature IRListNode ->
      ir_payload_exprs node signature ->
      ir_action node signature
  | IRSequenceAction :
      ir_action node signature ->
      ir_action node signature ->
      ir_action node signature.

Arguments IRSkipAction {node signature}.
Arguments IRSetGlobalAction {node signature} _ _.
Arguments IRSetLocalAction {node signature} _ _ _.
Arguments IRRemoveSelectedMessageAction {node signature}.
Arguments IREmitAction {node signature} _ _ _ _.
Arguments IREmitManyAction {node signature} _ _ _ _.
Arguments IRSequenceAction {node signature} _ _.

Fixpoint ir_remove_message
    {node : Type} {signature : protocol_signature}
    (selected_id : nat)
    (messages : list (ir_message node signature)) :
    list (ir_message node signature) :=
  match messages with
  | [] => []
  | message :: rest =>
      if Nat.eqb selected_id (ir_message_id message)
      then rest
      else message :: ir_remove_message selected_id rest
  end.

Fixpoint ir_materialize_messages
    {node : Type} {signature : protocol_signature}
    (next_id : nat)
    (kind : signature_message_kind signature)
    (sender : node)
    (receivers : list node)
    (payload : ir_payload_store node signature) :
    list (ir_message node signature) :=
  match receivers with
  | [] => []
  | receiver :: rest =>
      @mkIRMessage node signature next_id kind sender receiver payload ::
      ir_materialize_messages (S next_id) kind sender rest payload
  end.

Definition ir_emit_messages
    {node : Type} {signature : protocol_signature}
    (state : ir_protocol_state node signature)
    (kind : signature_message_kind signature)
    (sender : node)
    (receivers : list node)
    (payload : ir_payload_store node signature) :
    ir_protocol_state node signature :=
  mkIRProtocolState
    (ir_processes state)
    (ir_message_store state ++
      ir_materialize_messages
        (ir_next_message_id state) kind sender receivers payload)
    (ir_global_fields state)
    (ir_next_message_id state + List.length receivers).

Definition ir_remove_selected_message
    {node : Type} {signature : protocol_signature}
    (state : ir_protocol_state node signature)
    (selected_id : nat) :
    ir_protocol_state node signature :=
  mkIRProtocolState
    (ir_processes state)
    (ir_remove_message selected_id (ir_message_store state))
    (ir_global_fields state)
    (ir_next_message_id state).

Lemma ir_set_local_field_preserves_state_equivalence
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (left right : ir_protocol_state node signature)
    (process : node)
    (field : signature_local_field signature)
    (value : ir_value node
      (signature_local_field_type signature field)) :
  ir_states_equivalent left right ->
  ir_states_equivalent
    (ir_set_local_field node_eq_dec left process field value)
    (ir_set_local_field node_eq_dec right process field value).
Proof.
  intros [processes_equal
    [messages_equal [globals_equal next_id_equal]]].
  unfold ir_states_equivalent.
  repeat split.
  - intros candidate observed.
    cbn [ir_set_local_field ir_processes].
    destruct (node_eq_dec process candidate) as [same_process | other_process].
    + subst candidate.
      repeat rewrite ir_update_processes_same.
      destruct (signature_local_field_eq_dec signature field observed)
        as [same_field | other_field].
      * subst observed. repeat rewrite ir_update_field_same. reflexivity.
      * repeat rewrite ir_update_field_different by exact other_field.
        apply processes_equal.
    + repeat rewrite ir_update_processes_different by exact other_process.
      apply processes_equal.
  - exact messages_equal.
  - exact globals_equal.
  - exact next_id_equal.
Qed.

Lemma ir_set_global_field_preserves_state_equivalence
    {node : Type} {signature : protocol_signature}
    (left right : ir_protocol_state node signature)
    (field : signature_global_field signature)
    (value : ir_value node
      (signature_global_field_type signature field)) :
  ir_states_equivalent left right ->
  ir_states_equivalent
    (ir_set_global_field left field value)
    (ir_set_global_field right field value).
Proof.
  intros [processes_equal
    [messages_equal [globals_equal next_id_equal]]].
  unfold ir_states_equivalent.
  repeat split.
  - exact processes_equal.
  - exact messages_equal.
  - intro observed.
    cbn [ir_set_global_field ir_global_fields].
    destruct (signature_global_field_eq_dec signature field observed)
      as [same_field | other_field].
    + subst observed. repeat rewrite ir_update_field_same. reflexivity.
    + repeat rewrite ir_update_field_different by exact other_field.
      apply globals_equal.
  - exact next_id_equal.
Qed.

Lemma ir_remove_selected_message_preserves_state_equivalence
    {node : Type} {signature : protocol_signature}
    (left right : ir_protocol_state node signature)
    (selected_id : nat) :
  ir_states_equivalent left right ->
  ir_states_equivalent
    (ir_remove_selected_message left selected_id)
    (ir_remove_selected_message right selected_id).
Proof.
  intros [processes_equal
    [messages_equal [globals_equal next_id_equal]]].
  unfold ir_states_equivalent.
  repeat split; cbn [ir_remove_selected_message ir_processes
    ir_message_store ir_global_fields ir_next_message_id].
  - exact processes_equal.
  - now rewrite messages_equal.
  - exact globals_equal.
  - exact next_id_equal.
Qed.

Lemma ir_emit_messages_preserves_state_equivalence
    {node : Type} {signature : protocol_signature}
    (left right : ir_protocol_state node signature)
    (kind : signature_message_kind signature)
    (sender : node)
    (receivers : list node)
    (payload : ir_payload_store node signature) :
  ir_states_equivalent left right ->
  ir_states_equivalent
    (ir_emit_messages left kind sender receivers payload)
    (ir_emit_messages right kind sender receivers payload).
Proof.
  intros [processes_equal
    [messages_equal [globals_equal next_id_equal]]].
  unfold ir_states_equivalent.
  repeat split; cbn [ir_emit_messages ir_processes ir_message_store
    ir_global_fields ir_next_message_id].
  - exact processes_equal.
  - now rewrite messages_equal, next_id_equal.
  - exact globals_equal.
  - now rewrite next_id_equal.
Qed.

Fixpoint eval_ir_payload_exprs
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (state : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (payload_exprs : ir_payload_exprs node signature) :
    option (ir_payload_store node signature) :=
  match payload_exprs with
  | [] => Some []
  | mkIRPayloadExprEntry field expr :: rest =>
      match eval_ir_expr node_eq_dec config state event expr,
            eval_ir_payload_exprs
              node_eq_dec config state event rest with
      | Some value, Some payload =>
          Some (@mkIRPayloadEntry node signature field value :: payload)
      | _, _ => None
      end
  end.

Lemma eval_ir_payload_exprs_respects_state_equivalence
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (left right : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (payload_exprs : ir_payload_exprs node signature) :
  ir_states_equivalent left right ->
  eval_ir_payload_exprs node_eq_dec config left event payload_exprs =
    eval_ir_payload_exprs node_eq_dec config right event payload_exprs.
Proof.
  intro equivalent.
  induction payload_exprs as [|entry rest IH].
  - reflexivity.
  - destruct entry as [field expr]. cbn.
    rewrite (eval_ir_expr_respects_state_equivalence
      node_eq_dec config left right event _ expr equivalent).
    now rewrite IH.
Qed.

Fixpoint eval_ir_action
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (state : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (action : ir_action node signature) :
    option (ir_protocol_state node signature) :=
  match action with
  | IRSkipAction => Some state
  | IRSetGlobalAction field value_expr =>
      match eval_ir_expr node_eq_dec config state event value_expr with
      | Some value => Some (ir_set_global_field state field value)
      | None => None
      end
  | IRSetLocalAction process_expr field value_expr =>
      match eval_ir_expr node_eq_dec config state event process_expr,
            eval_ir_expr node_eq_dec config state event value_expr with
      | Some (IRNodeValue process), Some value =>
          Some (ir_set_local_field
            node_eq_dec state process field value)
      | _, _ => None
      end
  | IRRemoveSelectedMessageAction =>
      match event with
      | IRRuntimeQuery => None
      | IRRuntimeStart _ => None
      | IRRuntimeDeliver message _ =>
          Some (ir_remove_selected_message state (ir_message_id message))
      end
  | IREmitAction kind sender_expr receiver_expr payload_exprs =>
      match eval_ir_expr node_eq_dec config state event sender_expr,
            eval_ir_expr node_eq_dec config state event receiver_expr,
            eval_ir_payload_exprs
              node_eq_dec config state event payload_exprs with
      | Some (IRNodeValue sender), Some (IRNodeValue receiver), Some payload =>
          Some (ir_emit_messages state kind sender [receiver] payload)
      | _, _, _ => None
      end
  | IREmitManyAction kind sender_expr receivers_expr payload_exprs =>
      match eval_ir_expr node_eq_dec config state event sender_expr,
            eval_ir_expr node_eq_dec config state event receivers_expr,
            eval_ir_payload_exprs
              node_eq_dec config state event payload_exprs with
      | Some (IRNodeValue sender),
        Some (IRListNodeValue receivers), Some payload =>
          Some (ir_emit_messages state kind sender receivers payload)
      | _, _, _ => None
      end
  | IRSequenceAction first second =>
      match eval_ir_action node_eq_dec config state event first with
      | Some successor =>
          eval_ir_action node_eq_dec config successor event second
      | None => None
      end
  end.

(** Successful action evaluation transports across observationally equivalent
    states and produces equivalent successors.  The theorem is directional so
    clients can chain simulations; symmetry of [ir_states_equivalent] gives the
    converse whenever it is needed. *)
Theorem eval_ir_action_respects_state_equivalence
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (event : ir_runtime_event node signature)
    (action : ir_action node signature)
    (left right left_successor : ir_protocol_state node signature) :
  ir_states_equivalent left right ->
  eval_ir_action node_eq_dec config left event action =
    Some left_successor ->
  exists right_successor,
    eval_ir_action node_eq_dec config right event action =
      Some right_successor /\
    ir_states_equivalent left_successor right_successor.
Proof.
  revert left right left_successor.
  induction action; intros left right left_successor equivalent evaluated.
  - cbn in evaluated. inversion evaluated. subst left_successor.
    exists right. split; [reflexivity | exact equivalent].
  - cbn in evaluated |- *.
    rewrite (eval_ir_expr_respects_state_equivalence
      node_eq_dec config left right event _ i equivalent) in evaluated.
    destruct (eval_ir_expr node_eq_dec config right event i)
      as [value |] eqn:value_result; try discriminate.
    inversion evaluated. subst left_successor.
    eexists. split.
    + reflexivity.
    + now apply ir_set_global_field_preserves_state_equivalence.
  - cbn in evaluated |- *.
    rewrite (eval_ir_expr_respects_state_equivalence
      node_eq_dec config left right event _ i equivalent) in evaluated.
    rewrite (eval_ir_expr_respects_state_equivalence
      node_eq_dec config left right event _ i0 equivalent) in evaluated.
    destruct (eval_ir_expr node_eq_dec config right event i)
      as [process_value |] eqn:process_result; try discriminate.
    destruct process_value; try discriminate.
    destruct (eval_ir_expr node_eq_dec config right event i0)
      as [value |] eqn:value_result; try discriminate.
    inversion evaluated. subst left_successor.
    eexists. split.
    + reflexivity.
    + now apply ir_set_local_field_preserves_state_equivalence.
  - destruct event; cbn in evaluated |- *; try discriminate.
    inversion evaluated. subst left_successor.
    eexists. split.
    + reflexivity.
    + now apply ir_remove_selected_message_preserves_state_equivalence.
  - cbn in evaluated |- *.
    rewrite (eval_ir_expr_respects_state_equivalence
      node_eq_dec config left right event _ i equivalent) in evaluated.
    rewrite (eval_ir_expr_respects_state_equivalence
      node_eq_dec config left right event _ i0 equivalent) in evaluated.
    rewrite (eval_ir_payload_exprs_respects_state_equivalence
      node_eq_dec config left right event i1 equivalent) in evaluated.
    destruct (eval_ir_expr node_eq_dec config right event i)
      as [sender_value |] eqn:sender_result; try discriminate.
    destruct sender_value; try discriminate.
    destruct (eval_ir_expr node_eq_dec config right event i0)
      as [receiver_value |] eqn:receiver_result; try discriminate.
    destruct receiver_value; try discriminate.
    destruct (eval_ir_payload_exprs node_eq_dec config right event i1)
      as [payload |] eqn:payload_result; try discriminate.
    inversion evaluated. subst left_successor.
    eexists. split.
    + reflexivity.
    + now apply ir_emit_messages_preserves_state_equivalence.
  - cbn in evaluated |- *.
    rewrite (eval_ir_expr_respects_state_equivalence
      node_eq_dec config left right event _ i equivalent) in evaluated.
    rewrite (eval_ir_expr_respects_state_equivalence
      node_eq_dec config left right event _ i0 equivalent) in evaluated.
    rewrite (eval_ir_payload_exprs_respects_state_equivalence
      node_eq_dec config left right event i1 equivalent) in evaluated.
    destruct (eval_ir_expr node_eq_dec config right event i)
      as [sender_value |] eqn:sender_result; try discriminate.
    destruct sender_value; try discriminate.
    destruct (eval_ir_expr node_eq_dec config right event i0)
      as [receivers_value |] eqn:receivers_result; try discriminate.
    destruct receivers_value; try discriminate.
    destruct (eval_ir_payload_exprs node_eq_dec config right event i1)
      as [payload |] eqn:payload_result; try discriminate.
    inversion evaluated. subst left_successor.
    eexists. split.
    + reflexivity.
    + now apply ir_emit_messages_preserves_state_equivalence.
  - cbn in evaluated |- *.
    destruct (eval_ir_action node_eq_dec config left event action1)
      as [left_intermediate |] eqn:first_result; try discriminate.
    destruct (IHaction1 left right left_intermediate
      equivalent first_result) as
      [right_intermediate [right_first intermediate_equivalent]].
    rewrite right_first.
    now apply (IHaction2 left_intermediate right_intermediate
      left_successor intermediate_equivalent evaluated).
Qed.

Theorem eval_ir_action_deterministic
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (state : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (action : ir_action node signature)
    (left right : ir_protocol_state node signature) :
  eval_ir_action node_eq_dec config state event action = Some left ->
  eval_ir_action node_eq_dec config state event action = Some right ->
  left = right.
Proof.
  intros left_result right_result.
  rewrite left_result in right_result.
  now inversion right_result.
Qed.

Theorem ir_emit_messages_next_id
    {node : Type} {signature : protocol_signature}
    (state : ir_protocol_state node signature)
    (kind : signature_message_kind signature)
    (sender : node)
    (receivers : list node)
    (payload : ir_payload_store node signature) :
  ir_next_message_id
    (ir_emit_messages state kind sender receivers payload) =
  ir_next_message_id state + List.length receivers.
Proof. reflexivity. Qed.

(** Actions may preserve the allocator or advance it when they emit messages;
    they never move it backwards.  This protocol-neutral fact is the base for
    direct message-identifier invariants in programs interpreted by the IR. *)
Theorem eval_ir_action_next_message_id_monotone
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (state successor : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (action : ir_action node signature) :
  eval_ir_action node_eq_dec config state event action = Some successor ->
  ir_next_message_id state <= ir_next_message_id successor.
Proof.
  revert state successor.
  induction action;
    intros state successor evaluated; cbn in evaluated.
  - injection evaluated as <-. lia.
  - destruct (eval_ir_expr node_eq_dec config state event i);
      try discriminate.
    injection evaluated as <-.
    change (ir_next_message_id state <= ir_next_message_id state).
    apply Nat.le_refl.
  - destruct (eval_ir_expr node_eq_dec config state event i)
      as [process_value |]; try discriminate.
    destruct process_value; try discriminate.
    destruct (eval_ir_expr node_eq_dec config state event i0);
      try discriminate.
    injection evaluated as <-.
    change (ir_next_message_id state <= ir_next_message_id state).
    apply Nat.le_refl.
  - destruct event; try discriminate.
    injection evaluated as <-.
    change (ir_next_message_id state <= ir_next_message_id state).
    apply Nat.le_refl.
  - destruct (eval_ir_expr node_eq_dec config state event i)
      as [sender_value |]; try discriminate.
    destruct sender_value; try discriminate.
    destruct (eval_ir_expr node_eq_dec config state event i0)
      as [receiver_value |]; try discriminate.
    destruct receiver_value; try discriminate.
    destruct (eval_ir_payload_exprs node_eq_dec config state event i1);
      try discriminate.
    injection evaluated as <-.
    rewrite ir_emit_messages_next_id. lia.
  - destruct (eval_ir_expr node_eq_dec config state event i)
      as [sender_value |]; try discriminate.
    destruct sender_value; try discriminate.
    destruct (eval_ir_expr node_eq_dec config state event i0)
      as [receivers_value |]; try discriminate.
    destruct receivers_value; try discriminate.
    destruct (eval_ir_payload_exprs node_eq_dec config state event i1);
      try discriminate.
    injection evaluated as <-.
    rewrite ir_emit_messages_next_id. lia.
  - destruct (eval_ir_action node_eq_dec config state event action1)
      as [intermediate |] eqn:first; try discriminate.
    specialize (IHaction1 state intermediate first).
    specialize (IHaction2 intermediate successor evaluated).
    lia.
Qed.
