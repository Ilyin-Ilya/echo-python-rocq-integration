(** * Direct queued-request accounting for the public Echo IR executable

    Request-edge uniqueness is maintained together with a minimal provenance
    invariant: every queued request sender is the initiator or has an installed
    parent.  This is sufficient to show that the fresh sender introduced by a
    first-request rule cannot collide with an older request sender. *)

From Stdlib Require Import List Bool Arith Sorting.Permutation.
Import ListNotations.
Require Import ProtocolIRTypes ProtocolIRExpressions ProtocolIRActions
  ProtocolIRInterpreter ProtocolIRRunner EchoIRSignature EchoIRProgram
  EchoIRExecutable EchoIRExecutableInvariants EchoIRExecutableLifecycle
  EchoIRExecutablePending EchoIRExecutableDiscovery
  EchoIRExecutableTopology.

Section EchoIRExecutableRequestAccounting.

Variable node : Type.
Variable node_eq : forall left right : node,
  {left = right} + {left <> right}.

Definition echo_ir_request_edges_unique
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall first second,
    In first (ir_message_store state) ->
    In second (ir_message_store state) ->
    ir_message_kind first = EchoIRRequest ->
    ir_message_kind second = EchoIRRequest ->
    ir_message_sender first = ir_message_sender second ->
    ir_message_receiver first = ir_message_receiver second ->
    first = second.

Definition echo_ir_request_senders_provenanced
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall message,
    In message (ir_message_store state) ->
    ir_message_kind message = EchoIRRequest ->
    ir_message_sender message = echo_ir_config_initiator node config \/
    exists parent,
      echo_ir_parent_value node state (ir_message_sender message) =
        Some parent.

Definition echo_ir_request_accounting
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  echo_ir_request_edges_unique state /\
  echo_ir_request_senders_provenanced config state.

Lemma echo_ir_request_edges_unique_sublist
    (smaller larger : list (ir_message node echo_ir_signature)) :
  (forall message, In message smaller -> In message larger) ->
  (forall first second,
    In first larger -> In second larger ->
    ir_message_kind first = EchoIRRequest ->
    ir_message_kind second = EchoIRRequest ->
    ir_message_sender first = ir_message_sender second ->
    ir_message_receiver first = ir_message_receiver second ->
    first = second) ->
  forall first second,
    In first smaller -> In second smaller ->
    ir_message_kind first = EchoIRRequest ->
    ir_message_kind second = EchoIRRequest ->
    ir_message_sender first = ir_message_sender second ->
    ir_message_receiver first = ir_message_receiver second ->
    first = second.
Proof.
  intros subset unique first second first_in second_in.
  eapply unique; eauto.
Qed.

Lemma echo_ir_request_edges_unique_app_no_requests
    (left right : list (ir_message node echo_ir_signature)) :
  (forall first second,
    In first left -> In second left ->
    ir_message_kind first = EchoIRRequest ->
    ir_message_kind second = EchoIRRequest ->
    ir_message_sender first = ir_message_sender second ->
    ir_message_receiver first = ir_message_receiver second ->
    first = second) ->
  (forall message, In message right ->
    ir_message_kind message <> EchoIRRequest) ->
  forall first second,
    In first (left ++ right) -> In second (left ++ right) ->
    ir_message_kind first = EchoIRRequest ->
    ir_message_kind second = EchoIRRequest ->
    ir_message_sender first = ir_message_sender second ->
    ir_message_receiver first = ir_message_receiver second ->
    first = second.
Proof.
  intros left_unique no_requests first second first_in second_in
    first_kind second_kind same_sender same_receiver.
  apply in_app_or in first_in. apply in_app_or in second_in.
  destruct first_in as [first_old | first_new];
    destruct second_in as [second_old | second_new].
  - eapply left_unique; eauto.
  - exfalso. exact (no_requests second second_new second_kind).
  - exfalso. exact (no_requests first first_new first_kind).
  - exfalso. exact (no_requests first first_new first_kind).
Qed.

Lemma echo_ir_request_edges_unique_app_fresh_sender
    (left right : list (ir_message node echo_ir_signature))
    (fresh_sender : node) :
  (forall first second,
    In first left -> In second left ->
    ir_message_kind first = EchoIRRequest ->
    ir_message_kind second = EchoIRRequest ->
    ir_message_sender first = ir_message_sender second ->
    ir_message_receiver first = ir_message_receiver second ->
    first = second) ->
  (forall first second,
    In first right -> In second right ->
    ir_message_kind first = EchoIRRequest ->
    ir_message_kind second = EchoIRRequest ->
    ir_message_sender first = ir_message_sender second ->
    ir_message_receiver first = ir_message_receiver second ->
    first = second) ->
  (forall message, In message left ->
    ir_message_kind message = EchoIRRequest ->
    ir_message_sender message <> fresh_sender) ->
  (forall message, In message right ->
    ir_message_kind message = EchoIRRequest ->
    ir_message_sender message = fresh_sender) ->
  forall first second,
    In first (left ++ right) -> In second (left ++ right) ->
    ir_message_kind first = EchoIRRequest ->
    ir_message_kind second = EchoIRRequest ->
    ir_message_sender first = ir_message_sender second ->
    ir_message_receiver first = ir_message_receiver second ->
    first = second.
Proof.
  intros left_unique right_unique old_sender new_sender
    first second first_in second_in first_kind second_kind
    same_sender same_receiver.
  apply in_app_or in first_in. apply in_app_or in second_in.
  destruct first_in as [first_old | first_new];
    destruct second_in as [second_old | second_new].
  - eapply left_unique; eauto.
  - exfalso. apply (old_sender first first_old first_kind).
    rewrite same_sender. now apply new_sender.
  - exfalso. apply (old_sender second second_old second_kind).
    rewrite <- same_sender. now apply new_sender.
  - eapply right_unique; eauto.
Qed.

Lemma echo_ir_materialized_message_kind
    (next_id : nat) (kind : echo_ir_message_kind)
    (sender : node) (receivers : list node)
    (payload : ir_payload_store node echo_ir_signature)
    (message : ir_message node echo_ir_signature) :
  In message (@ir_materialize_messages node echo_ir_signature
    next_id kind sender receivers payload) ->
  ir_message_kind message = kind.
Proof.
  revert next_id.
  induction receivers as [|receiver rest IH]; intros next_id member.
  - contradiction.
  - cbn [ir_materialize_messages] in member.
    destruct member as [same | member].
    + subst message. reflexivity.
    + now apply (IH (S next_id)).
Qed.

Lemma echo_ir_materialized_receivers_injective
    (next_id : nat) (kind : echo_ir_message_kind)
    (sender : node) (receivers : list node)
    (payload : ir_payload_store node echo_ir_signature) :
  NoDup receivers ->
  forall first second,
    In first (@ir_materialize_messages node echo_ir_signature
      next_id kind sender receivers payload) ->
    In second (@ir_materialize_messages node echo_ir_signature
      next_id kind sender receivers payload) ->
    ir_message_receiver first = ir_message_receiver second ->
    first = second.
Proof.
  revert next_id.
  induction receivers as [|receiver rest IH];
    intros next_id nodup first second first_in second_in same_receiver.
  - contradiction.
  - inversion nodup as [|? ? receiver_not_in rest_nodup]; subst.
    cbn [ir_materialize_messages] in first_in, second_in.
    destruct first_in as [first_head | first_tail];
      destruct second_in as [second_head | second_tail].
    + now subst first; subst second.
    + subst first.
      destruct (echo_ir_materialized_message_fields node
        (S next_id) kind sender rest payload second second_tail)
        as [second_sender second_receiver_in].
      cbn in same_receiver. exfalso. apply receiver_not_in.
      now rewrite same_receiver.
    + subst second.
      destruct (echo_ir_materialized_message_fields node
        (S next_id) kind sender rest payload first first_tail)
        as [first_sender first_receiver_in].
      cbn in same_receiver. exfalso. apply receiver_not_in.
      now rewrite <- same_receiver.
    + eapply IH; eauto.
Qed.

Lemma echo_ir_materialized_requests_unique
    (next_id : nat) (sender : node) (receivers : list node) :
  NoDup receivers ->
  forall first second,
    In first (@ir_materialize_messages node echo_ir_signature
      next_id EchoIRRequest sender receivers []) ->
    In second (@ir_materialize_messages node echo_ir_signature
      next_id EchoIRRequest sender receivers []) ->
    ir_message_kind first = EchoIRRequest ->
    ir_message_kind second = EchoIRRequest ->
    ir_message_sender first = ir_message_sender second ->
    ir_message_receiver first = ir_message_receiver second ->
    first = second.
Proof.
  intros nodup first second first_in second_in
    first_kind second_kind same_sender same_receiver.
  eapply echo_ir_materialized_receivers_injective; eauto.
Qed.

Lemma echo_ir_request_edges_unique_store
    (left right : ir_protocol_state node echo_ir_signature) :
  echo_ir_request_edges_unique left ->
  ir_message_store right = ir_message_store left ->
  echo_ir_request_edges_unique right.
Proof.
  intros unique store first second first_in second_in.
  rewrite store in first_in, second_in.
  now eapply unique.
Qed.

Lemma echo_ir_update_process_preserves_request_edges_unique
    (state : ir_protocol_state node echo_ir_signature)
    (owner : node) (parent : ir_value node IROptionNode)
    (pending : ir_value node IRListNode) (finished : bool) :
  echo_ir_request_edges_unique state ->
  echo_ir_request_edges_unique
    (echo_ir_update_process node node_eq state owner
      parent pending finished).
Proof.
  intro unique. eapply echo_ir_request_edges_unique_store.
  - exact unique.
  - reflexivity.
Qed.

Lemma echo_ir_set_global_preserves_request_edges_unique
    (state : ir_protocol_state node echo_ir_signature)
    (value : ir_value node IRBool) :
  echo_ir_request_edges_unique state ->
  echo_ir_request_edges_unique
    (ir_set_global_field state EchoIRStarted value).
Proof.
  intro unique. eapply echo_ir_request_edges_unique_store.
  - exact unique.
  - reflexivity.
Qed.

Lemma echo_ir_remove_preserves_request_edges_unique
    (state : ir_protocol_state node echo_ir_signature)
    (selected_id : nat) :
  echo_ir_request_edges_unique state ->
  echo_ir_request_edges_unique
    (ir_remove_selected_message state selected_id).
Proof.
  intros unique first second first_in second_in.
  apply unique.
  - cbn [ir_remove_selected_message ir_message_store] in first_in.
    now apply (echo_ir_remove_message_in node selected_id _ first).
  - cbn [ir_remove_selected_message ir_message_store] in second_in.
    now apply (echo_ir_remove_message_in node selected_id _ second).
Qed.

Lemma echo_ir_emit_nonrequest_preserves_request_edges_unique
    (state : ir_protocol_state node echo_ir_signature)
    (kind : echo_ir_message_kind) (sender : node)
    (receivers : list node)
    (payload : ir_payload_store node echo_ir_signature) :
  kind <> EchoIRRequest ->
  echo_ir_request_edges_unique state ->
  echo_ir_request_edges_unique
    (ir_emit_messages state kind sender receivers payload).
Proof.
  intros not_request unique.
  unfold echo_ir_request_edges_unique in unique |- *.
  cbn [ir_emit_messages ir_message_store].
  eapply echo_ir_request_edges_unique_app_no_requests.
  - exact unique.
  - intros message member message_request.
    apply not_request.
    rewrite <- message_request.
    symmetry. now apply (echo_ir_materialized_message_kind
      (ir_next_message_id state) kind sender receivers payload message).
Qed.

Lemma echo_ir_emit_fresh_requests_preserves_request_edges_unique
    (state : ir_protocol_state node echo_ir_signature)
    (sender : node) (receivers : list node) :
  echo_ir_request_edges_unique state ->
  NoDup receivers ->
  (forall message,
    In message (ir_message_store state) ->
    ir_message_kind message = EchoIRRequest ->
    ir_message_sender message <> sender) ->
  echo_ir_request_edges_unique
    (ir_emit_messages state EchoIRRequest sender receivers []).
Proof.
  intros unique receivers_nodup fresh.
  unfold echo_ir_request_edges_unique in unique |- *.
  cbn [ir_emit_messages ir_message_store].
  eapply echo_ir_request_edges_unique_app_fresh_sender
    with (fresh_sender := sender).
  - exact unique.
  - now apply echo_ir_materialized_requests_unique.
  - exact fresh.
  - intros message member _.
    exact (proj1 (echo_ir_materialized_message_fields node
      (ir_next_message_id state) EchoIRRequest sender receivers []
      message member)).
Qed.

Lemma echo_ir_request_senders_provenanced_store_processes
    (config : ir_protocol_config node echo_ir_signature)
    (left right : ir_protocol_state node echo_ir_signature) :
  echo_ir_request_senders_provenanced config left ->
  ir_message_store right = ir_message_store left ->
  ir_processes right = ir_processes left ->
  echo_ir_request_senders_provenanced config right.
Proof.
  intros provenance store processes message member request.
  rewrite store in member.
  specialize (provenance message member request).
  destruct provenance as [root | [parent installed]].
  - now left.
  - right. exists parent. unfold echo_ir_parent_value in installed |- *.
    now rewrite processes.
Qed.

Lemma echo_ir_set_global_preserves_request_senders_provenanced
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (value : ir_value node IRBool) :
  echo_ir_request_senders_provenanced config state ->
  echo_ir_request_senders_provenanced config
    (ir_set_global_field state EchoIRStarted value).
Proof.
  intro provenance.
  eapply echo_ir_request_senders_provenanced_store_processes.
  - exact provenance.
  - reflexivity.
  - reflexivity.
Qed.

Lemma echo_ir_remove_preserves_request_senders_provenanced
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (selected_id : nat) :
  echo_ir_request_senders_provenanced config state ->
  echo_ir_request_senders_provenanced config
    (ir_remove_selected_message state selected_id).
Proof.
  intros provenance message member request.
  apply provenance; [|exact request].
  cbn [ir_remove_selected_message ir_message_store] in member.
  now apply (echo_ir_remove_message_in node selected_id _ message).
Qed.

Lemma echo_ir_update_process_some_preserves_request_senders_provenanced
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (owner parent : node) (pending : ir_value node IRListNode)
    (finished : bool) :
  echo_ir_request_senders_provenanced config state ->
  echo_ir_request_senders_provenanced config
    (echo_ir_update_process node node_eq state owner
      (IROptionNodeValue (Some parent)) pending finished).
Proof.
  intros provenance message member request.
  specialize (provenance message member request).
  destruct provenance as [root | [old_parent installed]].
  - now left.
  - right. unfold echo_ir_parent_value, echo_ir_update_process
      in installed |- *.
    destruct (node_eq owner (ir_message_sender message))
      as [same | different].
    + subst owner. exists parent.
      rewrite ir_set_local_field_read_different by discriminate.
      rewrite ir_set_local_field_read_different by discriminate.
      now rewrite ir_set_local_field_same.
    + exists old_parent.
      repeat rewrite ir_set_local_field_read_other_process by exact different.
      exact installed.
Qed.

Lemma echo_ir_update_initiator_preserves_request_senders_provenanced
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (parent : ir_value node IROptionNode)
    (pending : ir_value node IRListNode) (finished : bool) :
  echo_ir_request_senders_provenanced config state ->
  echo_ir_request_senders_provenanced config
    (echo_ir_update_process node node_eq state
      (echo_ir_config_initiator node config) parent pending finished).
Proof.
  intros provenance message member request.
  specialize (provenance message member request).
  destruct provenance as [root | [old_parent installed]].
  - now left.
  - destruct (node_eq (echo_ir_config_initiator node config)
      (ir_message_sender message)) as [same | different].
    + now left.
    + right. exists old_parent.
      unfold echo_ir_parent_value, echo_ir_update_process
        in installed |- *.
      repeat rewrite ir_set_local_field_read_other_process by exact different.
      exact installed.
Qed.

Lemma echo_ir_emit_nonrequest_preserves_request_senders_provenanced
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (kind : echo_ir_message_kind) (sender : node)
    (receivers : list node)
    (payload : ir_payload_store node echo_ir_signature) :
  kind <> EchoIRRequest ->
  echo_ir_request_senders_provenanced config state ->
  echo_ir_request_senders_provenanced config
    (ir_emit_messages state kind sender receivers payload).
Proof.
  intros not_request provenance message member request.
  cbn [ir_emit_messages ir_message_store] in member.
  apply in_app_or in member as [old | emitted].
  - exact (provenance message old request).
  - exfalso. apply not_request. rewrite <- request.
    symmetry. now apply (echo_ir_materialized_message_kind
      (ir_next_message_id state) kind sender receivers payload message).
Qed.

Lemma echo_ir_emit_requests_from_provenanced_sender
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (sender : node) (receivers : list node) :
  echo_ir_request_senders_provenanced config state ->
  (sender = echo_ir_config_initiator node config \/
   exists parent,
     echo_ir_parent_value node state sender = Some parent) ->
  echo_ir_request_senders_provenanced config
    (ir_emit_messages state EchoIRRequest sender receivers []).
Proof.
  intros provenance sender_provenance message member request.
  cbn [ir_emit_messages ir_message_store] in member.
  apply in_app_or in member as [old | emitted].
  - exact (provenance message old request).
  - destruct (echo_ir_materialized_message_fields node
      (ir_next_message_id state) EchoIRRequest sender receivers []
      message emitted) as [same_sender _].
    destruct sender_provenance as [root | [parent installed]].
    + left. now rewrite same_sender.
    + right. exists parent. now rewrite same_sender.
Qed.

Lemma echo_ir_update_some_remove_preserves_request_accounting
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (owner parent : node) (pending : ir_value node IRListNode)
    (finished : bool) :
  echo_ir_request_accounting config state ->
  echo_ir_request_accounting config
    (ir_remove_selected_message
      (echo_ir_update_process node node_eq state owner
        (IROptionNodeValue (Some parent)) pending finished)
      (ir_message_id message)).
Proof.
  intros [unique provenance]. split.
  - apply echo_ir_remove_preserves_request_edges_unique.
    now apply echo_ir_update_process_preserves_request_edges_unique.
  - apply echo_ir_remove_preserves_request_senders_provenanced.
    now apply echo_ir_update_process_some_preserves_request_senders_provenanced.
Qed.

Lemma echo_ir_update_initiator_remove_preserves_request_accounting
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (parent : ir_value node IROptionNode)
    (pending : ir_value node IRListNode) (finished : bool) :
  echo_ir_request_accounting config state ->
  echo_ir_request_accounting config
    (ir_remove_selected_message
      (echo_ir_update_process node node_eq state
        (echo_ir_config_initiator node config) parent pending finished)
      (ir_message_id message)).
Proof.
  intros [unique provenance]. split.
  - apply echo_ir_remove_preserves_request_edges_unique.
    now apply echo_ir_update_process_preserves_request_edges_unique.
  - apply echo_ir_remove_preserves_request_senders_provenanced.
    now apply echo_ir_update_initiator_preserves_request_senders_provenanced.
Qed.

Lemma echo_ir_emit_nonrequest_preserves_request_accounting
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (kind : echo_ir_message_kind) (sender : node)
    (receivers : list node)
    (payload : ir_payload_store node echo_ir_signature) :
  kind <> EchoIRRequest ->
  echo_ir_request_accounting config state ->
  echo_ir_request_accounting config
    (ir_emit_messages state kind sender receivers payload).
Proof.
  intros not_request [unique provenance]. split.
  - now apply echo_ir_emit_nonrequest_preserves_request_edges_unique.
  - now apply echo_ir_emit_nonrequest_preserves_request_senders_provenanced.
Qed.

Lemma echo_ir_remove_emit_nonrequest_preserves_request_accounting
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (kind : echo_ir_message_kind) (sender : node)
    (receivers : list node)
    (payload : ir_payload_store node echo_ir_signature) :
  kind <> EchoIRRequest ->
  echo_ir_request_accounting config state ->
  echo_ir_request_accounting config
    (ir_emit_messages
      (ir_remove_selected_message state (ir_message_id message))
      kind sender receivers payload).
Proof.
  intros not_request [unique provenance].
  apply echo_ir_emit_nonrequest_preserves_request_accounting;
    [exact not_request |].
  split.
  - now apply echo_ir_remove_preserves_request_edges_unique.
  - now apply echo_ir_remove_preserves_request_senders_provenanced.
Qed.

Lemma echo_ir_update_some_remove_emit_nonrequest_preserves_request_accounting
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (owner parent : node) (pending : ir_value node IRListNode)
    (finished : bool) (kind : echo_ir_message_kind)
    (sender : node) (receivers : list node)
    (payload : ir_payload_store node echo_ir_signature) :
  kind <> EchoIRRequest ->
  echo_ir_request_accounting config state ->
  echo_ir_request_accounting config
    (ir_emit_messages
      (ir_remove_selected_message
        (echo_ir_update_process node node_eq state owner
          (IROptionNodeValue (Some parent)) pending finished)
        (ir_message_id message))
      kind sender receivers payload).
Proof.
  intros not_request accounting.
  apply echo_ir_emit_nonrequest_preserves_request_accounting;
    [exact not_request |].
  now apply echo_ir_update_some_remove_preserves_request_accounting.
Qed.

Lemma echo_ir_start_action_preserves_request_accounting
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (certificates : ir_start_certificates node echo_ir_signature) :
  echo_ir_request_accounting config state ->
  ir_message_store state = [] ->
  NoDup (ir_config_neighbors config
    (echo_ir_config_initiator node config)) ->
  eval_ir_action node_eq config state (IRRuntimeStart certificates)
    (ir_rule_action (@echo_ir_start_rule node)) = Some successor ->
  echo_ir_request_accounting config successor.
Proof.
  intros [unique provenance] store_empty order_nodup action.
  unfold echo_ir_start_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_bool, echo_ir_initiator, echo_ir_start_order,
    echo_ir_neighbors, echo_ir_emit_many, echo_ir_empty_payload,
    echo_ir_option_none in action.
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
  assert (updated_unique : echo_ir_request_edges_unique updated).
  { unfold updated. now apply echo_ir_update_process_preserves_request_edges_unique. }
  assert (updated_provenance :
    echo_ir_request_senders_provenanced config updated).
  { unfold updated.
    now apply echo_ir_update_initiator_preserves_request_senders_provenanced. }
  assert (started_unique : echo_ir_request_edges_unique started).
  { unfold started. now apply echo_ir_set_global_preserves_request_edges_unique. }
  assert (started_provenance :
    echo_ir_request_senders_provenanced config started).
  { unfold started.
    now apply echo_ir_set_global_preserves_request_senders_provenanced. }
  split.
  - apply echo_ir_emit_fresh_requests_preserves_request_edges_unique.
    + exact started_unique.
    + exact order_nodup.
    + intros message member request.
      exfalso. unfold started, updated in member.
      change (In message (ir_message_store state)) in member.
      rewrite store_empty in member. contradiction.
  - apply echo_ir_emit_requests_from_provenanced_sender.
    + exact started_provenance.
    + now left.
Qed.

Lemma echo_ir_first_request_nonleaf_action_preserves_request_accounting
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_request_accounting config state ->
  NoDup (ir_remove_node node_eq (ir_message_sender message)
    (ir_config_neighbors config (ir_message_receiver message))) ->
  (forall old,
    In old (ir_message_store state) ->
    ir_message_kind old = EchoIRRequest ->
    ir_message_sender old <> ir_message_receiver message) ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_nonleaf_rule node)) =
      Some successor ->
  echo_ir_request_accounting config successor.
Proof.
  intros [unique provenance] order_nodup fresh action.
  unfold echo_ir_first_request_nonleaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_forward_order,
    echo_ir_remove, echo_ir_neighbors,
    echo_ir_emit_many, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  set (updated := echo_ir_update_process node node_eq state
    (ir_message_receiver message)
    (IROptionNodeValue (Some (ir_message_sender message)))
    (IRListNodeValue
      (ir_remove_node node_eq (ir_message_sender message)
        (ir_config_neighbors config (ir_message_receiver message)))) false).
  set (removed := ir_remove_selected_message updated
    (ir_message_id message)).
  assert (removed_unique : echo_ir_request_edges_unique removed).
  { unfold removed, updated.
    apply echo_ir_remove_preserves_request_edges_unique.
    now apply echo_ir_update_process_preserves_request_edges_unique. }
  assert (removed_provenance :
    echo_ir_request_senders_provenanced config removed).
  { unfold removed, updated.
    apply echo_ir_remove_preserves_request_senders_provenanced.
    now apply echo_ir_update_process_some_preserves_request_senders_provenanced. }
  split.
  - apply echo_ir_emit_fresh_requests_preserves_request_edges_unique.
    + exact removed_unique.
    + exact order_nodup.
    + intros old member request same_sender.
      apply (fresh old).
      * unfold removed, updated in member.
        cbn [ir_remove_selected_message echo_ir_update_process
          ir_message_store] in member.
        now apply (echo_ir_remove_message_in node
          (ir_message_id message) _ old).
      * exact request.
      * exact same_sender.
  - apply echo_ir_emit_requests_from_provenanced_sender.
    + exact removed_provenance.
    + right. exists (ir_message_sender message).
      unfold removed, updated, echo_ir_parent_value,
        ir_remove_selected_message, echo_ir_update_process.
      cbn [ir_processes].
      rewrite ir_set_local_field_read_different by discriminate.
      rewrite ir_set_local_field_read_different by discriminate.
      now rewrite ir_set_local_field_same.
Qed.

Lemma echo_ir_first_request_leaf_action_preserves_request_accounting
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_request_accounting config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_leaf_rule node)) =
      Some successor ->
  echo_ir_request_accounting config successor.
Proof.
  intros accounting action.
  unfold echo_ir_first_request_leaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_empty_nodes,
    echo_ir_emit_one, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  change (echo_ir_request_accounting config
    (ir_emit_messages
      (ir_remove_selected_message
        (echo_ir_update_process node node_eq state
          (ir_message_receiver message)
          (IROptionNodeValue (Some (ir_message_sender message)))
          (IRListNodeValue []) true)
        (ir_message_id message))
      EchoIRReply (ir_message_receiver message)
      [ir_message_sender message] [])).
  eapply echo_ir_update_some_remove_emit_nonrequest_preserves_request_accounting.
  - discriminate.
  - exact accounting.
Qed.

Lemma echo_ir_message_reply_action_preserves_request_accounting
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature)
    (rule : ir_rule node echo_ir_signature) :
  ir_rule_action rule =
    echo_ir_sequence node
      [IRRemoveSelectedMessageAction;
       echo_ir_emit_one node EchoIRReply
         (echo_ir_receiver node) (echo_ir_sender node)] ->
  echo_ir_request_accounting config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates) (ir_rule_action rule) =
      Some successor ->
  echo_ir_request_accounting config successor.
Proof.
  intros rule_action accounting action.
  rewrite rule_action in action.
  unfold echo_ir_emit_one, echo_ir_receiver, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  change (echo_ir_request_accounting config
    (ir_emit_messages
      (ir_remove_selected_message state (ir_message_id message))
      EchoIRReply (ir_message_receiver message)
      [ir_message_sender message] [])).
  eapply echo_ir_remove_emit_nonrequest_preserves_request_accounting.
  - discriminate.
  - exact accounting.
Qed.

Lemma echo_ir_initiator_request_action_preserves_request_accounting
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_request_accounting config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_request_rule node)) =
      Some successor ->
  echo_ir_request_accounting config successor.
Proof.
  intros accounting action.
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
  change (echo_ir_request_accounting config
    (ir_emit_messages
      (ir_remove_selected_message state (ir_message_id message))
      EchoIRReply (echo_ir_config_initiator node config)
      [ir_message_sender message] [])).
  eapply echo_ir_remove_emit_nonrequest_preserves_request_accounting.
  - discriminate.
  - exact accounting.
Qed.

Lemma echo_ir_participant_reply_more_action_preserves_request_accounting
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_request_accounting config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_more_rule node)) =
      Some successor ->
  echo_ir_request_accounting config successor.
Proof.
  intros accounting action.
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
    change (echo_ir_request_accounting config
      (ir_remove_selected_message
        (echo_ir_update_process node node_eq state
          (ir_message_receiver message)
          (IROptionNodeValue (Some parent_node))
          (IRListNodeValue
            (ir_remove_node node_eq (ir_message_sender message)
              (ir_list_node_value_contents
                (ir_processes state
                  (ir_message_receiver message) EchoIRPending))))
          false)
        (ir_message_id message))).
    now apply echo_ir_update_some_remove_preserves_request_accounting.
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_participant_reply_final_action_preserves_request_accounting
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_request_accounting config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_final_rule node)) =
      Some successor ->
  echo_ir_request_accounting config successor.
Proof.
  intros accounting action.
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
    change (echo_ir_request_accounting config
      (ir_emit_messages
        (ir_remove_selected_message
          (echo_ir_update_process node node_eq state
            (ir_message_receiver message)
            (IROptionNodeValue (Some parent_node))
            (IRListNodeValue []) true)
          (ir_message_id message))
        EchoIRReply (ir_message_receiver message) [parent_node] [])).
    eapply echo_ir_update_some_remove_emit_nonrequest_preserves_request_accounting.
    + discriminate.
    + exact accounting.
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_initiator_reply_more_action_preserves_request_accounting
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_request_accounting config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_more_rule node)) =
      Some successor ->
  echo_ir_request_accounting config successor.
Proof.
  intros accounting action.
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
  change (echo_ir_request_accounting config
    (ir_remove_selected_message
      (echo_ir_update_process node node_eq state
        (echo_ir_config_initiator node config)
        (IROptionNodeValue None)
        (IRListNodeValue
          (ir_remove_node node_eq (ir_message_sender message)
            (ir_list_node_value_contents
              (ir_processes state
                (echo_ir_config_initiator node config) EchoIRPending))))
        false)
      (ir_message_id message))).
  now apply echo_ir_update_initiator_remove_preserves_request_accounting.
Qed.

Lemma echo_ir_initiator_reply_final_action_preserves_request_accounting
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_request_accounting config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_final_rule node)) =
      Some successor ->
  echo_ir_request_accounting config successor.
Proof.
  intros accounting action.
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
  change (echo_ir_request_accounting config
    (ir_remove_selected_message
      (echo_ir_update_process node node_eq state
        (echo_ir_config_initiator node config)
        (IROptionNodeValue None) (IRListNodeValue []) true)
      (ir_message_id message))).
  now apply echo_ir_update_initiator_remove_preserves_request_accounting.
Qed.

Lemma echo_ir_start_enabled_store_empty
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (certificates : ir_start_certificates node echo_ir_signature) :
  eval_ir_rule node_eq config state (IRRuntimeStart certificates)
    (@echo_ir_start_rule node) = IRRuleEnabled ->
  ir_message_store state = [].
Proof.
  intro enabled.
  pose proof (eval_ir_rule_enabled_guard node_eq config state
    (IRRuntimeStart certificates) (@echo_ir_start_rule node)
    (@IRMessageStoreEmptyExpr node echo_ir_signature) enabled)
    as guard.
  assert (member : In (@IRMessageStoreEmptyExpr node echo_ir_signature)
    (ir_rule_guards (@echo_ir_start_rule node))).
  { cbn [echo_ir_start_rule]. repeat (first [left; reflexivity | right]). }
  specialize (guard member).
  cbn [eval_ir_expr] in guard.
  destruct (ir_message_store state) as [|message rest];
    [reflexivity | discriminate].
Qed.

Lemma echo_ir_first_nonleaf_enabled_parent_none
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  eval_ir_rule node_eq config state
    (IRRuntimeDeliver message certificates)
    (@echo_ir_first_request_nonleaf_rule node) = IRRuleEnabled ->
  echo_ir_parent_value node state (ir_message_receiver message) = None.
Proof.
  intro enabled.
  pose proof (eval_ir_rule_enabled_guard node_eq config state
    (IRRuntimeDeliver message certificates)
    (@echo_ir_first_request_nonleaf_rule node)
    (echo_ir_equal node
      (echo_ir_parent node (echo_ir_receiver node))
      (echo_ir_option_none node)) enabled) as guard.
  assert (member :
    In (echo_ir_equal node
      (echo_ir_parent node (echo_ir_receiver node))
      (echo_ir_option_none node))
      (ir_rule_guards (@echo_ir_first_request_nonleaf_rule node))).
  {
    cbn [echo_ir_first_request_nonleaf_rule echo_ir_process_initial].
    now right; left.
  }
  specialize (guard member).
  unfold echo_ir_equal, echo_ir_parent, echo_ir_receiver,
    echo_ir_option_none in guard.
  cbn [eval_ir_expr ir_event_message] in guard.
  injection guard as equal.
  unfold echo_ir_parent_value.
  rewrite (ir_option_node_value_eta
    (ir_processes state
      (ir_message_receiver message) EchoIRParent)) in equal |- *.
  cbn in equal |- *.
  destruct (ir_option_node_value_contents
    (ir_processes state
      (ir_message_receiver message) EchoIRParent)) as [parent |].
  - discriminate.
  - reflexivity.
Qed.

Theorem EchoStep_preserves_request_accounting
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (external_event : ir_external_event node echo_ir_signature) :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_topology_well_formed node config state ->
  echo_ir_request_accounting config state ->
  EchoStep node node_eq config state external_event successor ->
  echo_ir_request_accounting config successor.
Proof.
  intros initiator_in neighbors_valid topology accounting step.
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
    eapply echo_ir_start_action_preserves_request_accounting.
    + exact accounting.
    + now apply (echo_ir_start_enabled_store_empty
        config state certificates).
    + pose proof (@echo_ir_start_enabled_order
        node node_eq config state certificates enabled) as permutation.
      eapply Permutation_NoDup.
      * symmetry. exact permutation.
      * exact (proj1 (neighbors_valid
          (echo_ir_config_initiator node config) initiator_in)).
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
      pose proof (echo_ir_enabled_noninitiator_guard node node_eq config state
        message certificates (@echo_ir_first_request_nonleaf_rule node)
        enabled ltac:(cbn [echo_ir_first_request_nonleaf_rule]; now left))
        as receiver_not_root.
      pose proof (echo_ir_first_nonleaf_enabled_parent_none
        config state message certificates enabled) as receiver_parent_none.
      eapply echo_ir_first_request_nonleaf_action_preserves_request_accounting.
      * exact accounting.
      * pose proof (@echo_ir_nonleaf_enabled_order
          node node_eq config state message certificates enabled)
          as permutation.
        eapply Permutation_NoDup.
        -- symmetry. exact permutation.
        -- apply echo_ir_remove_node_nodup.
           exact (proj1 (neighbors_valid
             (ir_message_receiver message) receiver_in)).
      * intros old old_in old_kind same_sender.
        destruct (proj2 accounting old old_in old_kind)
          as [old_root | [parent installed]].
        -- apply receiver_not_root. now rewrite <- same_sender.
        -- rewrite same_sender in installed.
           rewrite receiver_parent_none in installed. discriminate.
      * exact action.
    + destruct selected_in as [same | selected_in].
      * subst selected_rule.
        pose proof (eval_ir_rule_enabled_pattern node_eq config state
          runtime_event (@echo_ir_first_request_leaf_rule node) enabled)
          as pattern.
        destruct runtime_event as [|start_certificates|message certificates];
          cbn [echo_ir_first_request_leaf_rule ir_event_pattern_matches]
            in pattern; try discriminate.
        eapply echo_ir_first_request_leaf_action_preserves_request_accounting.
        -- exact accounting.
        -- exact action.
      * destruct selected_in as [same | selected_in].
        -- subst selected_rule.
           pose proof (eval_ir_rule_enabled_pattern node_eq config state
             runtime_event (@echo_ir_repeated_request_rule node) enabled)
             as pattern.
           destruct runtime_event as
             [|start_certificates|message certificates];
             cbn [echo_ir_repeated_request_rule ir_event_pattern_matches]
               in pattern; try discriminate.
           eapply echo_ir_message_reply_action_preserves_request_accounting
             with (rule := @echo_ir_repeated_request_rule node).
           ++ reflexivity.
           ++ exact accounting.
           ++ exact action.
        -- destruct selected_in as [same | selected_in].
           ++ subst selected_rule.
              pose proof (eval_ir_rule_enabled_pattern node_eq config state
                runtime_event (@echo_ir_initiator_request_rule node) enabled)
                as pattern.
              destruct runtime_event as
                [|start_certificates|message certificates];
                cbn [echo_ir_initiator_request_rule ir_event_pattern_matches]
                  in pattern; try discriminate.
              eapply
                echo_ir_initiator_request_action_preserves_request_accounting.
              ** exact accounting.
              ** exact action.
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
                 eapply
                   echo_ir_participant_reply_more_action_preserves_request_accounting.
                 --- exact accounting.
                 --- exact action.
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
                     eapply
                       echo_ir_participant_reply_final_action_preserves_request_accounting.
                     +++ exact accounting.
                     +++ exact action.
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
                         eapply
                           echo_ir_initiator_reply_more_action_preserves_request_accounting.
                         *** exact accounting.
                         *** exact action.
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
                               echo_ir_initiator_reply_final_action_preserves_request_accounting.
                             ---- exact accounting.
                             ---- exact action.
                         *** contradiction.
Qed.

Lemma echo_ir_initial_request_accounting
    (config : ir_protocol_config node echo_ir_signature) :
  echo_ir_request_accounting config (@echo_initial_state node).
Proof.
  split; intros message; contradiction.
Qed.

Theorem echo_ir_path_preserves_request_accounting
    (config : ir_protocol_config node echo_ir_signature)
    (initial final : ir_protocol_state node echo_ir_signature) :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  ir_protocol_reachable node_eq config
    (ir_program_rules (@echo_program node)) initial final ->
  echo_ir_topology_well_formed node config initial ->
  echo_ir_request_accounting config initial ->
  echo_ir_request_accounting config final.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  induction reachable; intros topology accounting.
  - exact accounting.
  - apply IHreachable.
    + eapply EchoStep_preserves_topology_well_formed.
      * exact initiator_in.
      * exact neighbors_valid.
      * exact symmetric.
      * exact topology.
      * exists rule. exact H.
    + eapply EchoStep_preserves_request_accounting.
      * exact initiator_in.
      * exact neighbors_valid.
      * exact topology.
      * exact accounting.
      * exists rule. exact H.
Qed.

Theorem echo_reachable_request_accounting
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_reachable node node_eq config state ->
  echo_ir_request_accounting config state.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  eapply echo_ir_path_preserves_request_accounting.
  - exact initiator_in.
  - exact neighbors_valid.
  - exact symmetric.
  - exact reachable.
  - apply echo_ir_initial_topology_well_formed.
  - apply echo_ir_initial_request_accounting.
Qed.

Corollary echo_reachable_request_edges_unique
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_reachable node node_eq config state ->
  echo_ir_request_edges_unique state.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  exact (proj1 (echo_reachable_request_accounting config state
    initiator_in neighbors_valid symmetric reachable)).
Qed.

End EchoIRExecutableRequestAccounting.
