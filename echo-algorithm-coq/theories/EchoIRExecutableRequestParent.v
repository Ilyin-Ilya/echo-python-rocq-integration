(** * Direct consumed-parent-request accounting for generic Echo IR

    A queued request cannot be the request by which its receiver installed
    the sender as parent: that request has already been consumed.  The proof
    keeps a small causal ghost invariant saying that every installed parent
    is the initiator or itself already has a parent. *)

From Stdlib Require Import List Bool Arith Lia Sorting.Permutation.
Import ListNotations.
Require Import ProtocolIRTypes ProtocolIRExpressions ProtocolIRActions
  ProtocolIRInterpreter ProtocolIRRunner EchoIRSignature EchoIRProgram
  EchoIRExecutable EchoIRExecutableInvariants EchoIRExecutableLifecycle
  EchoIRExecutablePending EchoIRExecutableDiscovery EchoIRExecutableTopology
  EchoIRExecutableRequestAccounting.

Section EchoIRExecutableRequestParent.

Variable node : Type.
Variable node_eq : forall left right : node,
  {left = right} + {left <> right}.

Definition echo_ir_parent_sources_provenanced
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall child parent,
    echo_ir_parent_value node state child = Some parent ->
    parent = echo_ir_config_initiator node config \/
    exists grandparent,
      echo_ir_parent_value node state parent = Some grandparent.

Definition echo_ir_request_parent_distinct
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  forall message,
    In message (ir_message_store state) ->
    ir_message_kind message = EchoIRRequest ->
    echo_ir_parent_value node state (ir_message_receiver message) <>
      Some (ir_message_sender message).

Definition echo_ir_message_ids_well_formed
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  (forall message,
    In message (ir_message_store state) ->
    ir_message_id message < ir_next_message_id state) /\
  NoDup (List.map ir_message_id (ir_message_store state)).

Definition echo_ir_request_parent_accounting
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  echo_ir_request_accounting node config state /\
  echo_ir_message_ids_well_formed state /\
  echo_ir_parent_sources_provenanced config state /\
  echo_ir_request_parent_distinct state.

(** The part of request-parent accounting that is independent of queued
    request provenance.  Keeping it named lets rule proofs compose the three
    purely operational obligations uniformly. *)
Definition echo_ir_request_parent_tail
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) : Prop :=
  echo_ir_message_ids_well_formed state /\
  echo_ir_parent_sources_provenanced config state /\
  echo_ir_request_parent_distinct state.

Lemma echo_ir_remove_message_selected_not_in
    (selected : ir_message node echo_ir_signature)
    (messages : list (ir_message node echo_ir_signature)) :
  NoDup (List.map ir_message_id messages) ->
  ~ In selected (ir_remove_message (ir_message_id selected) messages).
Proof.
  induction messages as [|head rest IH]; intro nodup; cbn.
  - tauto.
  - inversion nodup as [|? ? head_not_in rest_nodup]; subst.
    destruct (Nat.eqb (ir_message_id selected) (ir_message_id head))
      eqn:same_id.
    + intro member. apply head_not_in.
      apply in_map_iff. exists selected. split; [|exact member].
      now apply Nat.eqb_eq in same_id.
    + intro member. destruct member as [same | member].
      * subst head. rewrite Nat.eqb_refl in same_id. discriminate.
      * exact (IH rest_nodup member).
Qed.

Lemma echo_ir_remove_message_ids_nodup
    (selected_id : nat)
    (messages : list (ir_message node echo_ir_signature)) :
  NoDup (List.map ir_message_id messages) ->
  NoDup (List.map ir_message_id
    (ir_remove_message selected_id messages)).
Proof.
  induction messages as [|head rest IH]; intro nodup.
  - constructor.
  - inversion nodup as [|? ? head_not_in rest_nodup]; subst.
    cbn [ir_remove_message].
    destruct (Nat.eqb selected_id (ir_message_id head)).
    + exact rest_nodup.
    + cbn. constructor.
      * intro member. apply head_not_in.
        apply in_map_iff in member as [message [identifier removed]].
        apply in_map_iff. exists message. split; [exact identifier |].
        now apply (echo_ir_remove_message_in node selected_id rest message).
      * now apply IH.
Qed.

Lemma echo_ir_materialized_message_ids
    (next_id : nat) (kind : echo_ir_message_kind)
    (sender : node) (receivers : list node)
    (payload : ir_payload_store node echo_ir_signature) :
  List.map ir_message_id
    (@ir_materialize_messages node echo_ir_signature
      next_id kind sender receivers payload) =
  List.seq next_id (List.length receivers).
Proof.
  revert next_id.
  induction receivers as [|receiver rest IH]; intro next_id.
  - reflexivity.
  - change
      (next_id :: List.map ir_message_id
          (@ir_materialize_messages node echo_ir_signature
            (S next_id) kind sender rest payload) =
       next_id :: List.seq (S next_id) (List.length rest)).
    f_equal. apply IH.
Qed.

Lemma echo_ir_materialized_message_id_bounds
    (next_id : nat) (kind : echo_ir_message_kind)
    (sender : node) (receivers : list node)
    (payload : ir_payload_store node echo_ir_signature)
    (message : ir_message node echo_ir_signature) :
  In message (@ir_materialize_messages node echo_ir_signature
    next_id kind sender receivers payload) ->
  next_id <= ir_message_id message /\
  ir_message_id message < next_id + List.length receivers.
Proof.
  revert next_id.
  induction receivers as [|receiver rest IH]; intros next_id member.
  - contradiction.
  - cbn [ir_materialize_messages] in member.
    destruct member as [same | member].
    + subst message. cbn. lia.
    + specialize (IH (S next_id) member). cbn. lia.
Qed.

Lemma echo_ir_nodup_app_disjoint {A : Type} (left right : list A) :
  NoDup left -> NoDup right ->
  (forall item, In item left -> In item right -> False) ->
  NoDup (left ++ right).
Proof.
  intros left_nodup.
  induction left_nodup as [|item rest item_not_in rest_nodup IH];
    intros right_nodup disjoint.
  - exact right_nodup.
  - cbn. constructor.
    + intro member. apply in_app_or in member as [old | new].
      * now apply item_not_in.
      * eapply disjoint; [now left | exact new].
    + apply IH; [exact right_nodup |].
      intros candidate old new. eapply disjoint.
      * right. exact old.
      * exact new.
Qed.

Lemma echo_ir_update_process_preserves_message_ids
    (state : ir_protocol_state node echo_ir_signature)
    (owner : node) (parent : ir_value node IROptionNode)
    (pending : ir_value node IRListNode) (finished : bool) :
  echo_ir_message_ids_well_formed state ->
  echo_ir_message_ids_well_formed
    (echo_ir_update_process node node_eq state owner parent pending finished).
Proof.
  exact (fun invariant => invariant).
Qed.

Lemma echo_ir_set_global_preserves_message_ids
    (state : ir_protocol_state node echo_ir_signature)
    (value : ir_value node IRBool) :
  echo_ir_message_ids_well_formed state ->
  echo_ir_message_ids_well_formed
    (ir_set_global_field state EchoIRStarted value).
Proof.
  exact (fun invariant => invariant).
Qed.

Lemma echo_ir_remove_preserves_message_ids
    (state : ir_protocol_state node echo_ir_signature)
    (selected_id : nat) :
  echo_ir_message_ids_well_formed state ->
  echo_ir_message_ids_well_formed
    (ir_remove_selected_message state selected_id).
Proof.
  intros [below nodup]. split.
  - intros message member. apply below.
    cbn [ir_remove_selected_message ir_message_store] in member.
    now apply (echo_ir_remove_message_in node selected_id _ message).
  - cbn [ir_remove_selected_message ir_message_store].
    now apply echo_ir_remove_message_ids_nodup.
Qed.

Lemma echo_ir_emit_preserves_message_ids
    (state : ir_protocol_state node echo_ir_signature)
    (kind : echo_ir_message_kind) (sender : node)
    (receivers : list node)
    (payload : ir_payload_store node echo_ir_signature) :
  echo_ir_message_ids_well_formed state ->
  echo_ir_message_ids_well_formed
    (ir_emit_messages state kind sender receivers payload).
Proof.
  intros [below nodup].
  unfold echo_ir_message_ids_well_formed.
  cbn [ir_emit_messages ir_message_store ir_next_message_id]. split.
  - intros message member. apply in_app_or in member as [old | emitted].
    + specialize (below message old). lia.
    + apply echo_ir_materialized_message_id_bounds in emitted. lia.
  - rewrite List.map_app. apply echo_ir_nodup_app_disjoint.
    + exact nodup.
    + rewrite echo_ir_materialized_message_ids. apply seq_NoDup.
    + intros identifier old new.
      apply in_map_iff in old as [old_message [old_id old_member]].
      apply in_map_iff in new as [new_message [new_id new_member]].
      specialize (below old_message old_member).
      apply echo_ir_materialized_message_id_bounds in new_member.
      lia.
Qed.

Lemma echo_ir_remove_node_member_different
    (selected candidate : node) (items : list node) :
  NoDup items ->
  In candidate (ir_remove_node node_eq selected items) ->
  candidate <> selected.
Proof.
  induction items as [|head rest IH]; cbn; intros nodup member.
  - contradiction.
  - inversion nodup as [|? ? head_not_in rest_nodup]; subst.
    destruct (node_eq selected head) as [same | different].
    + subst head. intro candidate_selected. subst candidate.
      exact (head_not_in member).
    + destruct member as [same | member].
      * subst candidate. now intro backwards; apply different.
      * now apply IH.
Qed.

Lemma echo_ir_update_process_some_preserves_parent_sources
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (owner parent : node) (pending : ir_value node IRListNode)
    (finished : bool) :
  echo_ir_parent_sources_provenanced config state ->
  (parent = echo_ir_config_initiator node config \/
   exists grandparent,
     echo_ir_parent_value node state parent = Some grandparent) ->
  echo_ir_parent_sources_provenanced config
    (echo_ir_update_process node node_eq state owner
      (IROptionNodeValue (Some parent)) pending finished).
Proof.
  intros invariant parent_provenance child source installed.
  unfold echo_ir_parent_value, echo_ir_update_process in installed.
  destruct (node_eq owner child) as [same_child | different_child].
  - subst child.
    rewrite ir_set_local_field_read_different in installed by discriminate.
    rewrite ir_set_local_field_read_different in installed by discriminate.
    rewrite ir_set_local_field_same in installed.
    inversion installed. subst source.
    destruct parent_provenance as [root | [grandparent parented]].
    + now left.
    + right.
      destruct (node_eq owner parent) as [same_parent | different_parent].
      * subst parent. exists owner.
        unfold echo_ir_parent_value, echo_ir_update_process.
        rewrite ir_set_local_field_read_different by discriminate.
        rewrite ir_set_local_field_read_different by discriminate.
        now rewrite ir_set_local_field_same.
      * exists grandparent.
        unfold echo_ir_parent_value, echo_ir_update_process.
        repeat rewrite ir_set_local_field_read_other_process
          by exact different_parent.
        exact parented.
  - repeat rewrite ir_set_local_field_read_other_process in installed
      by exact different_child.
    specialize (invariant child source installed).
    destruct invariant as [root | [grandparent source_parented]].
    + now left.
    + right.
      destruct (node_eq owner source) as [same_source | different_source].
      * subst source. exists parent.
        unfold echo_ir_parent_value, echo_ir_update_process.
        rewrite ir_set_local_field_read_different by discriminate.
        rewrite ir_set_local_field_read_different by discriminate.
        now rewrite ir_set_local_field_same.
      * exists grandparent.
        unfold echo_ir_parent_value, echo_ir_update_process.
        repeat rewrite ir_set_local_field_read_other_process
          by exact different_source.
        exact source_parented.
Qed.

Lemma echo_ir_update_initiator_preserves_parent_sources
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (pending : ir_value node IRListNode) (finished : bool) :
  echo_ir_parent_sources_provenanced config state ->
  echo_ir_parent_sources_provenanced config
    (echo_ir_update_process node node_eq state
      (echo_ir_config_initiator node config)
      (IROptionNodeValue None) pending finished).
Proof.
  intros invariant child source installed.
  unfold echo_ir_parent_value, echo_ir_update_process in installed.
  destruct (node_eq (echo_ir_config_initiator node config) child)
    as [same_child | different_child].
  - subst child.
    rewrite ir_set_local_field_read_different in installed by discriminate.
    rewrite ir_set_local_field_read_different in installed by discriminate.
    rewrite ir_set_local_field_same in installed. discriminate.
  - repeat rewrite ir_set_local_field_read_other_process in installed
      by exact different_child.
    specialize (invariant child source installed).
    destruct invariant as [root | [grandparent source_parented]].
    + now left.
    + destruct (node_eq (echo_ir_config_initiator node config) source)
        as [same_source | different_source].
      * now left.
      * right. exists grandparent.
        unfold echo_ir_parent_value, echo_ir_update_process.
        repeat rewrite ir_set_local_field_read_other_process
          by exact different_source.
        exact source_parented.
Qed.

Lemma echo_ir_processes_unchanged_preserves_parent_sources
    (config : ir_protocol_config node echo_ir_signature)
    (left right : ir_protocol_state node echo_ir_signature) :
  echo_ir_parent_sources_provenanced config left ->
  ir_processes right = ir_processes left ->
  echo_ir_parent_sources_provenanced config right.
Proof.
  intros invariant processes child parent installed.
  unfold echo_ir_parent_value in installed |- *.
  rewrite processes in installed |- *.
  now apply (invariant child parent installed).
Qed.

Lemma echo_ir_remove_preserves_parent_sources
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (selected_id : nat) :
  echo_ir_parent_sources_provenanced config state ->
  echo_ir_parent_sources_provenanced config
    (ir_remove_selected_message state selected_id).
Proof.
  intro invariant. eapply echo_ir_processes_unchanged_preserves_parent_sources.
  - exact invariant.
  - reflexivity.
Qed.

Lemma echo_ir_emit_preserves_parent_sources
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (kind : echo_ir_message_kind) (sender : node)
    (receivers : list node)
    (payload : ir_payload_store node echo_ir_signature) :
  echo_ir_parent_sources_provenanced config state ->
  echo_ir_parent_sources_provenanced config
    (ir_emit_messages state kind sender receivers payload).
Proof.
  intro invariant. eapply echo_ir_processes_unchanged_preserves_parent_sources.
  - exact invariant.
  - reflexivity.
Qed.

Lemma echo_ir_remove_preserves_request_parent_distinct
    (state : ir_protocol_state node echo_ir_signature)
    (selected_id : nat) :
  echo_ir_request_parent_distinct state ->
  echo_ir_request_parent_distinct
    (ir_remove_selected_message state selected_id).
Proof.
  intros invariant message member request.
  apply invariant; [|exact request].
  cbn [ir_remove_selected_message ir_message_store] in member.
  now apply (echo_ir_remove_message_in node selected_id _ message).
Qed.

Lemma echo_ir_emit_nonrequest_preserves_request_parent_distinct
    (state : ir_protocol_state node echo_ir_signature)
    (kind : echo_ir_message_kind) (sender : node)
    (receivers : list node)
    (payload : ir_payload_store node echo_ir_signature) :
  kind <> EchoIRRequest ->
  echo_ir_request_parent_distinct state ->
  echo_ir_request_parent_distinct
    (ir_emit_messages state kind sender receivers payload).
Proof.
  intros not_request invariant message member request.
  cbn [ir_emit_messages ir_message_store] in member.
  apply in_app_or in member as [old | emitted].
  - now apply invariant.
  - exfalso. apply not_request. rewrite <- request. symmetry.
    now apply (echo_ir_materialized_message_kind node
      (ir_next_message_id state) kind sender receivers payload message).
Qed.

Lemma echo_ir_update_initiator_preserves_request_parent_distinct
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (parent : ir_value node IROptionNode)
    (pending : ir_value node IRListNode) (finished : bool) :
  parent = IROptionNodeValue None ->
  echo_ir_request_parent_distinct state ->
  echo_ir_request_parent_distinct
    (echo_ir_update_process node node_eq state
      (echo_ir_config_initiator node config) parent pending finished).
Proof.
  intros parent_none invariant message member request.
  subst parent.
  unfold echo_ir_parent_value, ir_remove_selected_message,
    echo_ir_update_process.
  destruct (node_eq (echo_ir_config_initiator node config)
      (ir_message_receiver message)) as [same | different].
  - rewrite <- same.
    rewrite ir_set_local_field_read_different by discriminate.
    rewrite ir_set_local_field_read_different by discriminate.
    rewrite ir_set_local_field_same. discriminate.
  - repeat rewrite ir_set_local_field_read_other_process by exact different.
    now apply invariant.
Qed.

Lemma echo_ir_update_same_parent_preserves_request_parent_distinct
    (state : ir_protocol_state node echo_ir_signature)
    (owner parent : node) (pending : ir_value node IRListNode)
    (finished : bool) :
  echo_ir_parent_value node state owner = Some parent ->
  echo_ir_request_parent_distinct state ->
  echo_ir_request_parent_distinct
    (echo_ir_update_process node node_eq state owner
      (IROptionNodeValue (Some parent)) pending finished).
Proof.
  intros same_parent invariant message member request.
  unfold echo_ir_parent_value, echo_ir_update_process.
  destruct (node_eq owner (ir_message_receiver message))
    as [same | different].
  - subst owner.
    rewrite ir_set_local_field_read_different by discriminate.
    rewrite ir_set_local_field_read_different by discriminate.
    rewrite ir_set_local_field_same.
    unfold echo_ir_parent_value in same_parent.
    rewrite <- same_parent. now apply invariant.
  - repeat rewrite ir_set_local_field_read_other_process by exact different.
    now apply invariant.
Qed.

Lemma echo_ir_first_request_remove_distinct
    (state : ir_protocol_state node echo_ir_signature)
    (selected : ir_message node echo_ir_signature)
    (pending : ir_value node IRListNode) (finished : bool) :
  echo_ir_request_parent_distinct state ->
  echo_ir_request_edges_unique node state ->
  echo_ir_message_ids_well_formed state ->
  In selected (ir_message_store state) ->
  ir_message_kind selected = EchoIRRequest ->
  echo_ir_request_parent_distinct
    (ir_remove_selected_message
      (echo_ir_update_process node node_eq state
        (ir_message_receiver selected)
        (IROptionNodeValue (Some (ir_message_sender selected)))
        pending finished)
      (ir_message_id selected)).
Proof.
  intros distinct unique [below ids_nodup] selected_in selected_kind
    message member request_kind.
  assert (old_member : In message (ir_message_store state)).
  {
    cbn [ir_remove_selected_message echo_ir_update_process
      ir_message_store] in member.
    now apply (echo_ir_remove_message_in node
      (ir_message_id selected) _ message).
  }
  unfold echo_ir_parent_value, ir_remove_selected_message,
    echo_ir_update_process.
  cbn [ir_processes].
  destruct (node_eq (ir_message_receiver selected)
      (ir_message_receiver message)) as [same_receiver | different_receiver].
  - rewrite <- same_receiver.
    rewrite ir_set_local_field_read_different by discriminate.
    rewrite ir_set_local_field_read_different by discriminate.
    rewrite ir_set_local_field_same.
    intro same_parent. injection same_parent as same_sender.
    assert (same_message : message = selected).
    {
      eapply unique.
      - exact old_member.
      - exact selected_in.
      - exact request_kind.
      - exact selected_kind.
      - now symmetry.
      - now symmetry.
    }
    subst message.
    cbn [ir_remove_selected_message echo_ir_update_process
      ir_message_store] in member.
    exact (echo_ir_remove_message_selected_not_in selected
      (ir_message_store state) ids_nodup member).
  - repeat rewrite ir_set_local_field_read_other_process
      by exact different_receiver.
    now apply distinct.
Qed.

Lemma echo_ir_emit_requests_preserves_request_parent_distinct
    (state : ir_protocol_state node echo_ir_signature)
    (sender : node) (receivers : list node) :
  echo_ir_request_parent_distinct state ->
  (forall receiver, In receiver receivers ->
    echo_ir_parent_value node state receiver <> Some sender) ->
  echo_ir_request_parent_distinct
    (ir_emit_messages state EchoIRRequest sender receivers []).
Proof.
  intros invariant receivers_distinct message member request_kind.
  cbn [ir_emit_messages ir_message_store] in member.
  apply in_app_or in member as [old | emitted].
  - now apply invariant.
  - destruct (echo_ir_materialized_message_fields node
      (ir_next_message_id state) EchoIRRequest sender receivers []
      message emitted) as [same_sender receiver_in].
    rewrite same_sender.
    now apply receivers_distinct.
Qed.

Lemma echo_ir_set_global_preserves_request_parent_distinct
    (state : ir_protocol_state node echo_ir_signature)
    (value : ir_value node IRBool) :
  echo_ir_request_parent_distinct state ->
  echo_ir_request_parent_distinct
    (ir_set_global_field state EchoIRStarted value).
Proof.
  exact (fun invariant => invariant).
Qed.

Lemma echo_ir_set_global_preserves_parent_sources
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (value : ir_value node IRBool) :
  echo_ir_parent_sources_provenanced config state ->
  echo_ir_parent_sources_provenanced config
    (ir_set_global_field state EchoIRStarted value).
Proof.
  intro invariant.
  eapply echo_ir_processes_unchanged_preserves_parent_sources.
  - exact invariant.
  - reflexivity.
Qed.

Lemma echo_ir_remove_preserves_request_parent_tail
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (selected_id : nat) :
  echo_ir_request_parent_tail config state ->
  echo_ir_request_parent_tail config
    (ir_remove_selected_message state selected_id).
Proof.
  intros [ids [sources distinct]]. split.
  - now apply echo_ir_remove_preserves_message_ids.
  - split.
    + now apply echo_ir_remove_preserves_parent_sources.
    + now apply echo_ir_remove_preserves_request_parent_distinct.
Qed.

Lemma echo_ir_emit_nonrequest_preserves_request_parent_tail
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (kind : echo_ir_message_kind) (sender : node)
    (receivers : list node)
    (payload : ir_payload_store node echo_ir_signature) :
  kind <> EchoIRRequest ->
  echo_ir_request_parent_tail config state ->
  echo_ir_request_parent_tail config
    (ir_emit_messages state kind sender receivers payload).
Proof.
  intros not_request [ids [sources distinct]]. split.
  - now apply echo_ir_emit_preserves_message_ids.
  - split.
    + now apply echo_ir_emit_preserves_parent_sources.
    + now apply echo_ir_emit_nonrequest_preserves_request_parent_distinct.
Qed.

Lemma echo_ir_remove_emit_nonrequest_preserves_request_parent_tail
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (selected : ir_message node echo_ir_signature)
    (kind : echo_ir_message_kind) (sender : node)
    (receivers : list node)
    (payload : ir_payload_store node echo_ir_signature) :
  kind <> EchoIRRequest ->
  echo_ir_request_parent_tail config state ->
  echo_ir_request_parent_tail config
    (ir_emit_messages
      (ir_remove_selected_message state (ir_message_id selected))
      kind sender receivers payload).
Proof.
  intros not_request tail.
  apply echo_ir_emit_nonrequest_preserves_request_parent_tail;
    [exact not_request |].
  now apply echo_ir_remove_preserves_request_parent_tail.
Qed.

Lemma echo_ir_update_initiator_remove_preserves_request_parent_tail
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (selected : ir_message node echo_ir_signature)
    (pending : ir_value node IRListNode) (finished : bool) :
  echo_ir_request_parent_tail config state ->
  echo_ir_request_parent_tail config
    (ir_remove_selected_message
      (echo_ir_update_process node node_eq state
        (echo_ir_config_initiator node config)
        (IROptionNodeValue None) pending finished)
      (ir_message_id selected)).
Proof.
  intros [ids [sources distinct]].
  apply echo_ir_remove_preserves_request_parent_tail. split.
  - now apply echo_ir_update_process_preserves_message_ids.
  - split.
    + now apply echo_ir_update_initiator_preserves_parent_sources.
    + eapply echo_ir_update_initiator_preserves_request_parent_distinct;
        [reflexivity | exact distinct].
Qed.

Lemma echo_ir_update_same_parent_remove_preserves_request_parent_tail
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (selected : ir_message node echo_ir_signature)
    (owner parent : node) (pending : ir_value node IRListNode)
    (finished : bool) :
  echo_ir_parent_value node state owner = Some parent ->
  echo_ir_request_parent_tail config state ->
  echo_ir_request_parent_tail config
    (ir_remove_selected_message
      (echo_ir_update_process node node_eq state owner
        (IROptionNodeValue (Some parent)) pending finished)
      (ir_message_id selected)).
Proof.
  intros same_parent [ids [sources distinct]].
  apply echo_ir_remove_preserves_request_parent_tail. split.
  - now apply echo_ir_update_process_preserves_message_ids.
  - split.
    + apply echo_ir_update_process_some_preserves_parent_sources.
      * exact sources.
      * now apply sources with (child := owner).
    + now apply echo_ir_update_same_parent_preserves_request_parent_distinct.
Qed.

Lemma echo_ir_first_request_remove_preserves_request_parent_tail
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (selected : ir_message node echo_ir_signature)
    (pending : ir_value node IRListNode) (finished : bool) :
  echo_ir_request_accounting node config state ->
  echo_ir_request_parent_tail config state ->
  In selected (ir_message_store state) ->
  ir_message_kind selected = EchoIRRequest ->
  echo_ir_request_parent_tail config
    (ir_remove_selected_message
      (echo_ir_update_process node node_eq state
        (ir_message_receiver selected)
        (IROptionNodeValue (Some (ir_message_sender selected)))
        pending finished)
      (ir_message_id selected)).
Proof.
  intros accounting [ids [sources distinct]] selected_in selected_kind.
  split.
  - apply echo_ir_remove_preserves_message_ids.
    now apply echo_ir_update_process_preserves_message_ids.
  - split.
    + apply echo_ir_remove_preserves_parent_sources.
      apply echo_ir_update_process_some_preserves_parent_sources.
      * exact sources.
      * now apply (proj2 accounting selected selected_in selected_kind).
    + eapply echo_ir_first_request_remove_distinct.
      * exact distinct.
      * exact (proj1 accounting).
      * exact ids.
      * exact selected_in.
      * exact selected_kind.
Qed.

Lemma echo_ir_first_request_leaf_action_preserves_request_parent_tail
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_request_accounting node config state ->
  echo_ir_request_parent_tail config state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRRequest ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_leaf_rule node)) =
      Some successor ->
  echo_ir_request_parent_tail config successor.
Proof.
  intros accounting tail queued request_kind action.
  unfold echo_ir_first_request_leaf_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_some, echo_ir_sender, echo_ir_receiver, echo_ir_empty_nodes,
    echo_ir_emit_one, echo_ir_empty_payload, echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  apply echo_ir_emit_nonrequest_preserves_request_parent_tail;
    [discriminate |].
  now apply echo_ir_first_request_remove_preserves_request_parent_tail
    with (config := config).
Qed.

Lemma echo_ir_start_action_preserves_request_parent_tail
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (certificates : ir_start_certificates node echo_ir_signature) :
  echo_ir_request_parent_tail config state ->
  (forall receiver,
    In receiver (ir_config_neighbors config
      (echo_ir_config_initiator node config)) ->
    echo_ir_parent_value node state receiver <>
      Some (echo_ir_config_initiator node config)) ->
  eval_ir_action node_eq config state (IRRuntimeStart certificates)
    (ir_rule_action (@echo_ir_start_rule node)) = Some successor ->
  echo_ir_request_parent_tail config successor.
Proof.
  intros [ids [sources distinct]] receivers_distinct action.
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
  - apply echo_ir_emit_preserves_message_ids.
    apply echo_ir_set_global_preserves_message_ids.
    now apply echo_ir_update_process_preserves_message_ids.
  - split.
    + apply echo_ir_emit_preserves_parent_sources.
      apply echo_ir_set_global_preserves_parent_sources.
      now apply echo_ir_update_initiator_preserves_parent_sources.
    + apply echo_ir_emit_requests_preserves_request_parent_distinct.
      * apply echo_ir_set_global_preserves_request_parent_distinct.
        eapply echo_ir_update_initiator_preserves_request_parent_distinct;
          [reflexivity | exact distinct].
      * intros receiver receiver_in.
        unfold started, updated, echo_ir_parent_value,
          echo_ir_update_process.
        cbn [ir_set_global_field ir_processes].
        destruct (node_eq (echo_ir_config_initiator node config) receiver)
          as [same | different].
        -- subst receiver.
           rewrite ir_set_local_field_read_different by discriminate.
           rewrite ir_set_local_field_read_different by discriminate.
           rewrite ir_set_local_field_same. discriminate.
        -- repeat rewrite ir_set_local_field_read_other_process
             by exact different.
           now apply receivers_distinct.
Qed.

Lemma echo_ir_first_request_nonleaf_action_preserves_request_parent_tail
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_request_accounting node config state ->
  echo_ir_request_parent_tail config state ->
  In message (ir_message_store state) ->
  ir_message_kind message = EchoIRRequest ->
  (forall receiver,
    In receiver (ir_remove_node node_eq (ir_message_sender message)
      (ir_config_neighbors config (ir_message_receiver message))) ->
    echo_ir_parent_value node
      (ir_remove_selected_message
        (echo_ir_update_process node node_eq state
          (ir_message_receiver message)
          (IROptionNodeValue (Some (ir_message_sender message)))
          (IRListNodeValue
            (ir_remove_node node_eq (ir_message_sender message)
              (ir_config_neighbors config
                (ir_message_receiver message)))) false)
        (ir_message_id message)) receiver <>
      Some (ir_message_receiver message)) ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_first_request_nonleaf_rule node)) =
      Some successor ->
  echo_ir_request_parent_tail config successor.
Proof.
  intros accounting tail queued request_kind receivers_distinct action.
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
  pose proof
    (echo_ir_first_request_remove_preserves_request_parent_tail
      config state message
      (IRListNodeValue
        (ir_remove_node node_eq (ir_message_sender message)
          (ir_config_neighbors config (ir_message_receiver message))))
      false accounting tail queued request_kind) as removed_tail.
  split.
  - apply echo_ir_emit_preserves_message_ids.
    exact (proj1 removed_tail).
  - split.
    + apply echo_ir_emit_preserves_parent_sources.
      exact (proj1 (proj2 removed_tail)).
    + apply echo_ir_emit_requests_preserves_request_parent_distinct.
      * exact (proj2 (proj2 removed_tail)).
      * exact receivers_distinct.
Qed.

Lemma echo_ir_message_reply_action_preserves_request_parent_tail
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
  echo_ir_request_parent_tail config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates) (ir_rule_action rule) =
      Some successor ->
  echo_ir_request_parent_tail config successor.
Proof.
  intros rule_action tail action. rewrite rule_action in action.
  unfold echo_ir_emit_one, echo_ir_receiver, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  injection action as <-.
  eapply echo_ir_remove_emit_nonrequest_preserves_request_parent_tail.
  - discriminate.
  - exact tail.
Qed.

Lemma echo_ir_initiator_request_action_preserves_request_parent_tail
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_request_parent_tail config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_request_rule node)) =
      Some successor ->
  echo_ir_request_parent_tail config successor.
Proof.
  intros tail action. unfold echo_ir_initiator_request_rule in action.
  unfold echo_ir_emit_one, echo_ir_initiator, echo_ir_sender,
    echo_ir_empty_payload in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    eval_ir_payload_exprs ir_event_message] in action.
  rewrite (ir_node_value_eta
    (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
    ir_event_message] in action.
  injection action as <-.
  eapply echo_ir_remove_emit_nonrequest_preserves_request_parent_tail.
  - discriminate.
  - exact tail.
Qed.

Lemma echo_ir_participant_reply_more_action_preserves_request_parent_tail
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_request_parent_tail config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_more_rule node)) =
      Some successor ->
  echo_ir_request_parent_tail config successor.
Proof.
  intros tail action.
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
    apply echo_ir_update_same_parent_remove_preserves_request_parent_tail.
    + unfold echo_ir_parent_value. rewrite parent_value. reflexivity.
    + exact tail.
  - cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_participant_reply_final_action_preserves_request_parent_tail
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_request_parent_tail config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_participant_reply_final_rule node)) =
      Some successor ->
  echo_ir_request_parent_tail config successor.
Proof.
  intros tail action.
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
    apply echo_ir_emit_nonrequest_preserves_request_parent_tail;
      [discriminate |].
    apply echo_ir_update_same_parent_remove_preserves_request_parent_tail.
    + unfold echo_ir_parent_value. rewrite parent_value. reflexivity.
    + exact tail.
  - cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    rewrite parent_value in action.
    cbn [eval_ir_expr eval_ir_action eval_ir_payload_exprs
      ir_event_message] in action.
    discriminate action.
Qed.

Lemma echo_ir_initiator_reply_more_action_preserves_request_parent_tail
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_request_parent_tail config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_more_rule node)) =
      Some successor ->
  echo_ir_request_parent_tail config successor.
Proof.
  intros tail action. unfold echo_ir_initiator_reply_more_rule in action.
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
  now apply echo_ir_update_initiator_remove_preserves_request_parent_tail.
Qed.

Lemma echo_ir_initiator_reply_final_action_preserves_request_parent_tail
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature) :
  echo_ir_request_parent_tail config state ->
  eval_ir_action node_eq config state
    (IRRuntimeDeliver message certificates)
    (ir_rule_action (@echo_ir_initiator_reply_final_rule node)) =
      Some successor ->
  echo_ir_request_parent_tail config successor.
Proof.
  intros tail action. unfold echo_ir_initiator_reply_final_rule in action.
  unfold echo_ir_set_parent, echo_ir_set_pending, echo_ir_set_finished,
    echo_ir_initiator, echo_ir_option_none, echo_ir_empty_nodes,
    echo_ir_bool in action.
  cbn [ir_rule_action echo_ir_sequence eval_ir_action eval_ir_expr
    ir_event_message] in action.
  rewrite (ir_node_value_eta
    (ir_config_fields config EchoIRInitiator)) in action.
  cbn [eval_ir_expr eval_ir_action ir_event_message] in action.
  injection action as <-.
  now apply echo_ir_update_initiator_remove_preserves_request_parent_tail.
Qed.

Lemma echo_ir_enabled_request_pattern_kind
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (message : ir_message node echo_ir_signature)
    (certificates : ir_delivery_certificates node echo_ir_signature)
    (rule : ir_rule node echo_ir_signature) :
  ir_rule_pattern rule =
    (@IRDeliveryPattern echo_ir_signature EchoIRRequest) ->
  eval_ir_rule node_eq config state
    (IRRuntimeDeliver message certificates) rule = IRRuleEnabled ->
  ir_message_kind message = EchoIRRequest.
Proof.
  intros rule_pattern enabled.
  pose proof (eval_ir_rule_enabled_pattern node_eq config state
    (IRRuntimeDeliver message certificates) rule enabled) as pattern.
  rewrite rule_pattern in pattern.
  cbn [ir_event_pattern_matches] in pattern.
  destruct (signature_message_kind_eq_dec echo_ir_signature
    EchoIRRequest (ir_message_kind message)) as [same | different].
  - now symmetry.
  - discriminate.
Qed.

Lemma echo_ir_start_enabled_configured_parent_none
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature)
    (certificates : ir_start_certificates node echo_ir_signature) :
  eval_ir_rule node_eq config state (IRRuntimeStart certificates)
    (@echo_ir_start_rule node) = IRRuleEnabled ->
  forall owner,
    In owner (ir_config_nodes config) ->
    echo_ir_parent_value node state owner = None.
Proof.
  intros enabled owner owner_in.
  pose proof (eval_ir_rule_enabled_guard node_eq config state
    (IRRuntimeStart certificates) (@echo_ir_start_rule node)
    (@IRAllNodesLocalEqualExpr node echo_ir_signature
      EchoIRParent (echo_ir_option_none node)) enabled) as guard.
  assert (member :
    In (@IRAllNodesLocalEqualExpr node echo_ir_signature
      EchoIRParent (echo_ir_option_none node))
      (ir_rule_guards (@echo_ir_start_rule node))).
  { cbn [echo_ir_start_rule]. now right; left. }
  specialize (guard member).
  unfold echo_ir_option_none in guard.
  cbn [eval_ir_expr] in guard.
  injection guard as all_none.
  apply forallb_forall with (x := owner) in all_none; [|exact owner_in].
  unfold echo_ir_parent_value.
  rewrite (ir_option_node_value_eta
    (ir_processes state owner EchoIRParent)) in all_none |- *.
  cbn [ir_value_eqb] in all_none.
  destruct (ir_option_node_value_contents
    (ir_processes state owner EchoIRParent)) as [parent |].
  - discriminate.
  - reflexivity.
Qed.

Theorem EchoStep_preserves_request_parent_accounting
    (config : ir_protocol_config node echo_ir_signature)
    (state successor : ir_protocol_state node echo_ir_signature)
    (external_event : ir_external_event node echo_ir_signature) :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_topology_well_formed node config state ->
  echo_ir_request_parent_accounting config state ->
  EchoStep node node_eq config state external_event successor ->
  echo_ir_request_parent_accounting config successor.
Proof.
  intros initiator_in neighbors_valid topology invariant step.
  destruct invariant as [accounting [ids [sources distinct]]].
  assert (tail : echo_ir_request_parent_tail config state).
  { split; [exact ids |]. split; assumption. }
  assert (accounting_after : echo_ir_request_accounting node config successor).
  {
    eapply EchoStep_preserves_request_accounting; eauto.
  }
  split; [exact accounting_after |].
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
    eapply echo_ir_start_action_preserves_request_parent_tail.
    + exact tail.
    + intros receiver ordered.
      pose proof (@echo_ir_start_enabled_order
        node node_eq config state certificates enabled) as permutation.
      assert (neighbor : In receiver
        (ir_config_neighbors config
          (echo_ir_config_initiator node config))).
      { eapply Permutation_in; eauto. }
      assert (configured : In receiver (ir_config_nodes config)).
      { exact (proj1 (proj2 (neighbors_valid
          (echo_ir_config_initiator node config) initiator_in)
          receiver neighbor)). }
      rewrite (echo_ir_start_enabled_configured_parent_none
        config state certificates enabled receiver configured).
      discriminate.
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
      pose proof (echo_ir_first_nonleaf_enabled_parent_none node node_eq
        config state message certificates enabled) as receiver_parent_none.
      assert (request_kind : ir_message_kind message = EchoIRRequest).
      {
        exact (echo_ir_enabled_request_pattern_kind config state message
          certificates (@echo_ir_first_request_nonleaf_rule node)
          eq_refl enabled).
      }
      eapply echo_ir_first_request_nonleaf_action_preserves_request_parent_tail.
      * exact accounting.
      * exact tail.
      * exact queued.
      * exact request_kind.
      * intros target ordered.
        pose proof (@echo_ir_nonleaf_enabled_order
          node node_eq config state message certificates enabled)
          as permutation.
        assert (remaining : In target
          (ir_remove_node node_eq (ir_message_sender message)
            (ir_config_neighbors config (ir_message_receiver message)))).
        { eapply Permutation_in; eauto. }
        assert (target_not_sender : target <> ir_message_sender message).
        {
          eapply echo_ir_remove_node_member_different.
          - exact (proj1 (neighbors_valid
              (ir_message_receiver message) receiver_in)).
          - exact remaining.
        }
        unfold echo_ir_parent_value, ir_remove_selected_message,
          echo_ir_update_process. cbn [ir_processes].
        destruct (node_eq (ir_message_receiver message) target)
          as [same_target | different_target].
        -- subst target.
           rewrite ir_set_local_field_read_different by discriminate.
           rewrite ir_set_local_field_read_different by discriminate.
           rewrite ir_set_local_field_same.
           intro same_parent. injection same_parent as same_sender.
           now apply target_not_sender.
        -- repeat rewrite ir_set_local_field_read_other_process
             by exact different_target.
           intro target_parent.
           destruct (sources target (ir_message_receiver message)
             target_parent) as [root | [grandparent receiver_parent]].
           ++ now apply receiver_not_root.
           ++ rewrite receiver_parent_none in receiver_parent. discriminate.
      * exact action.
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
        assert (request_kind : ir_message_kind message = EchoIRRequest).
        {
          exact (echo_ir_enabled_request_pattern_kind config state message
            certificates (@echo_ir_first_request_leaf_rule node)
            eq_refl enabled).
        }
        eapply echo_ir_first_request_leaf_action_preserves_request_parent_tail.
        -- exact accounting.
        -- exact tail.
        -- exact queued.
        -- exact request_kind.
        -- exact action.
      * destruct selected_in as [same | selected_in].
        -- subst selected_rule.
           pose proof (eval_ir_rule_enabled_pattern node_eq config state
             runtime_event (@echo_ir_repeated_request_rule node) enabled)
             as pattern.
           destruct runtime_event as [|start_certificates|message certificates];
             cbn [echo_ir_repeated_request_rule ir_event_pattern_matches]
               in pattern; try discriminate.
           eapply echo_ir_message_reply_action_preserves_request_parent_tail
             with (rule := @echo_ir_repeated_request_rule node).
           ++ reflexivity.
           ++ exact tail.
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
                echo_ir_initiator_request_action_preserves_request_parent_tail;
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
                 pose proof (echo_ir_enabled_expected_parent node node_eq
                   config state message certificates
                   (@echo_ir_participant_reply_more_rule node) enabled
                   ltac:(cbn [echo_ir_participant_reply_more_rule];
                     now right; left)) as same_parent.
                 eapply
                   echo_ir_participant_reply_more_action_preserves_request_parent_tail;
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
                     pose proof (echo_ir_enabled_expected_parent node node_eq
                       config state message certificates
                       (@echo_ir_participant_reply_final_rule node) enabled
                       ltac:(cbn [echo_ir_participant_reply_final_rule];
                         now right; left)) as same_parent.
                     eapply
                       echo_ir_participant_reply_final_action_preserves_request_parent_tail;
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
                         eapply
                           echo_ir_initiator_reply_more_action_preserves_request_parent_tail;
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
                               echo_ir_initiator_reply_final_action_preserves_request_parent_tail;
                               eauto.
                         *** contradiction.
Qed.

Lemma echo_ir_initial_request_parent_accounting
    (config : ir_protocol_config node echo_ir_signature) :
  echo_ir_request_parent_accounting config (@echo_initial_state node).
Proof.
  split.
  - apply echo_ir_initial_request_accounting.
  - split.
    + split.
      * intros message queued. contradiction.
      * constructor.
    + split.
      * intros child parent installed. discriminate.
      * intros message queued. contradiction.
Qed.

Theorem echo_ir_path_preserves_request_parent_accounting
    (config : ir_protocol_config node echo_ir_signature)
    (initial final : ir_protocol_state node echo_ir_signature) :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  ir_protocol_reachable node_eq config
    (ir_program_rules (@echo_program node)) initial final ->
  echo_ir_topology_well_formed node config initial ->
  echo_ir_request_parent_accounting config initial ->
  echo_ir_request_parent_accounting config final.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  induction reachable; intros topology invariant.
  - exact invariant.
  - apply IHreachable.
    + eapply EchoStep_preserves_topology_well_formed.
      * exact initiator_in.
      * exact neighbors_valid.
      * exact symmetric.
      * exact topology.
      * exists rule. exact H.
    + eapply EchoStep_preserves_request_parent_accounting.
      * exact initiator_in.
      * exact neighbors_valid.
      * exact topology.
      * exact invariant.
      * exists rule. exact H.
Qed.

Theorem echo_reachable_request_parent_accounting
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_reachable node node_eq config state ->
  echo_ir_request_parent_accounting config state.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  eapply echo_ir_path_preserves_request_parent_accounting.
  - exact initiator_in.
  - exact neighbors_valid.
  - exact symmetric.
  - exact reachable.
  - apply echo_ir_initial_topology_well_formed.
  - apply echo_ir_initial_request_parent_accounting.
Qed.

Corollary echo_reachable_request_parent_distinct
    (config : ir_protocol_config node echo_ir_signature)
    (state : ir_protocol_state node echo_ir_signature) :
  In (echo_ir_config_initiator node config) (ir_config_nodes config) ->
  echo_ir_config_neighbors_well_formed node config ->
  echo_ir_config_neighbors_symmetric node config ->
  echo_reachable node node_eq config state ->
  echo_ir_request_parent_distinct state.
Proof.
  intros initiator_in neighbors_valid symmetric reachable.
  exact (proj2 (proj2 (proj2
    (echo_reachable_request_parent_accounting config state
      initiator_in neighbors_valid symmetric reachable)))).
Qed.

End EchoIRExecutableRequestParent.
