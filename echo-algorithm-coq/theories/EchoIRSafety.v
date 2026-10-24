(** * Reachable-state safety exposed directly on generic Echo IR states

    The generic statements below mention only IR reachability and projections
    from the generated IR state.  Topology, parent/lifecycle, and pending-list
    properties are proved directly from the generic interpreter. *)

From Stdlib Require Import List Bool.
Import ListNotations.
Require Import EchoTopology ProtocolIRTypes
  ProtocolIRInterpreter ProtocolIRRunner EchoIRSignature EchoIRConfig
  EchoIRProgram EchoIRExecutableInvariants EchoIRExecutableLifecycle
  EchoIRExecutablePending EchoIRExecutableTopology
  EchoIRExecutableObligations.

Module MakeEchoIRSafety (C : ECHO_CORRECTNESS_CONFIG).

Module Tree.

Definition echo_ir_parent
    (state : ir_protocol_state C.node echo_ir_signature)
    (owner : C.node) : option C.node :=
  match ir_processes state owner EchoIRParent with
  | IROptionNodeValue parent => parent
  end.

End Tree.

Local Notation node := C.node.
Local Notation node_eq := C.node_eq.
Local Notation initiator := C.initiator.
Local Notation all_nodes := C.all_nodes.
Local Notation adj := C.adj.
Local Notation ir_config :=
  (make_echo_ir_config initiator all_nodes adj).
Local Notation ir_program := (@echo_ir_program node).

Lemma echo_ir_encoded_neighbors_well_formed :
  EchoIRExecutablePending.echo_ir_config_neighbors_well_formed node ir_config.
Proof.
  intros owner owner_in.
  unfold EchoIRExecutablePending.echo_ir_pending_valid.
  unfold ir_config, make_echo_ir_config.
  cbn [ir_config_nodes ir_config_neighbors].
  unfold nbrs. split.
  - apply NoDup_filter. exact C.nodup_nodes.
  - intros neighbor neighbor_in.
    apply filter_In in neighbor_in as [configured adjacent].
    split.
    + exact configured.
    + apply filter_In. now split.
Qed.

Lemma echo_ir_encoded_initiator_configured :
  In (EchoIRExecutableInvariants.echo_ir_config_initiator node ir_config)
    (ir_config_nodes ir_config).
Proof.
  unfold EchoIRExecutableInvariants.echo_ir_config_initiator,
    ir_config, make_echo_ir_config, echo_ir_config_fields.
  cbn [ir_config_fields ir_config_nodes ir_node_value_contents].
  exact C.initiator_in_nodes.
Qed.

Lemma echo_ir_encoded_neighbors_symmetric :
  EchoIRExecutableTopology.echo_ir_config_neighbors_symmetric node ir_config.
Proof.
  intros left right left_in right_neighbor.
  unfold ir_config, make_echo_ir_config in *.
  cbn [ir_config_nodes ir_config_neighbors] in *.
  unfold nbrs in *.
  apply filter_In in right_neighbor as [right_in adjacent].
  apply filter_In. split.
  - exact left_in.
  - now apply C.adj_sym.
Qed.

Definition echo_ir_finished
    (state : ir_protocol_state node echo_ir_signature)
    (owner : node) : bool :=
  match ir_processes state owner EchoIRFinished with
  | IRBoolValue finished => finished
  end.

Definition echo_ir_pending
    (state : ir_protocol_state node echo_ir_signature)
    (owner : node) : list node :=
  match ir_processes state owner EchoIRPending with
  | IRListNodeValue pending => pending
  end.

(** Every installed IR parent is a configured node connected by a topology
    edge to its child. *)
Theorem echo_ir_reachable_parent_edges_valid
    (ir_state : ir_protocol_state node echo_ir_signature) :
  ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
  forall child parent,
    In child all_nodes ->
    Tree.echo_ir_parent ir_state child = Some parent ->
    In parent all_nodes /\ adj child parent = true.
Proof.
  intros reachable child parent child_in parent_value.
  pose proof
    (@EchoIRExecutableTopology.echo_reachable_topology_well_formed
      node node_eq ir_config ir_state
      echo_ir_encoded_initiator_configured
      echo_ir_encoded_neighbors_well_formed
      echo_ir_encoded_neighbors_symmetric reachable) as topology.
  destruct topology as [parents_valid queued_valid].
  unfold EchoIRExecutableTopology.echo_ir_parent_edges_valid
    in parents_valid.
  assert (direct_parent :
    EchoIRExecutableDiscovery.echo_ir_parent_value node ir_state child =
      Some parent).
  {
    unfold EchoIRExecutableDiscovery.echo_ir_parent_value,
      Tree.echo_ir_parent in *.
    exact parent_value.
  }
  destruct (parents_valid child parent child_in direct_parent)
    as [parent_in parent_neighbor].
  split.
  - exact parent_in.
  - unfold ir_config, make_echo_ir_config in parent_neighbor.
    cbn [ir_config_neighbors] in parent_neighbor.
    unfold nbrs in parent_neighbor.
    now apply filter_In in parent_neighbor as [_ adjacent].
Qed.

(** Every queued IR message follows a configured topology edge. *)
Theorem echo_ir_reachable_queued_edges_valid
    (ir_state : ir_protocol_state node echo_ir_signature) :
  ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
  forall message,
    In message (ir_message_store ir_state) ->
    In (ir_message_sender message) all_nodes /\
    In (ir_message_receiver message) all_nodes /\
    adj (ir_message_sender message) (ir_message_receiver message) = true.
Proof.
  intros reachable message queued.
  pose proof
    (@EchoIRExecutableTopology.echo_reachable_topology_well_formed
      node node_eq ir_config ir_state
      echo_ir_encoded_initiator_configured
      echo_ir_encoded_neighbors_well_formed
      echo_ir_encoded_neighbors_symmetric reachable) as topology.
  destruct topology as [parents_valid queued_valid].
  specialize (queued_valid message queued).
  unfold EchoIRExecutableTopology.echo_ir_message_edge_valid
    in queued_valid.
  destruct queued_valid as [sender_in [receiver_in edge]].
  repeat split; try assumption.
  unfold ir_config, make_echo_ir_config in edge.
  cbn [ir_config_neighbors] in edge.
  unfold nbrs in edge.
  now apply filter_In in edge as [_ adjacent].
Qed.

(** The initiator never acquires a parent in a reachable IR state. *)
Theorem echo_ir_reachable_initiator_parent_none
    (ir_state : ir_protocol_state node echo_ir_signature) :
  ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
  Tree.echo_ir_parent ir_state initiator = None.
Proof.
  intro reachable.
  pose proof
    (@EchoIRExecutableInvariants.echo_reachable_initiator_parent_none
      node node_eq ir_config ir_state reachable) as direct.
  unfold EchoIRExecutableInvariants.echo_ir_initiator_parent_none,
    EchoIRExecutableInvariants.echo_ir_config_initiator in direct.
  unfold ir_config, make_echo_ir_config,
    echo_ir_config_fields in direct.
  cbn [ir_config_fields ir_node_value_contents] in direct.
  unfold Tree.echo_ir_parent.
  now rewrite direct.
Qed.

(** A finished non-initiator in a reachable IR state has a parent. *)
Theorem echo_ir_reachable_finished_participant_has_parent
    (ir_state : ir_protocol_state node echo_ir_signature)
    (owner : node) :
  ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
  In owner all_nodes ->
  owner <> initiator ->
  echo_ir_finished ir_state owner = true ->
  exists parent, Tree.echo_ir_parent ir_state owner = Some parent.
Proof.
  intros reachable owner_in not_initiator finished.
  pose proof
    (@EchoIRExecutableLifecycle.echo_reachable_finished_participants_parented
      node node_eq ir_config ir_state reachable) as direct.
  unfold EchoIRExecutableLifecycle.echo_ir_finished_participants_parented,
    EchoIRExecutableInvariants.echo_ir_config_initiator in direct.
  unfold ir_config, make_echo_ir_config,
    echo_ir_config_fields in direct.
  cbn [ir_config_fields ir_node_value_contents] in direct.
  specialize (direct owner not_initiator).
  destruct (ir_bool_value_view
    (ir_processes ir_state owner EchoIRFinished)) as
    [finished_value finished_shape].
  unfold echo_ir_finished in finished.
  rewrite finished_shape in finished. cbn in finished.
  subst finished_value.
  destruct (direct finished_shape) as [parent parent_value].
  exists parent.
  unfold Tree.echo_ir_parent.
  now rewrite parent_value.
Qed.

(** Every reachable IR pending list is duplicate-free. *)
Theorem echo_ir_reachable_pending_nodup
    (ir_state : ir_protocol_state node echo_ir_signature)
    (owner : node) :
  ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
  In owner all_nodes ->
  NoDup (echo_ir_pending ir_state owner).
Proof.
  intros reachable owner_in.
  pose proof
    (@EchoIRExecutablePending.echo_reachable_pending_well_formed
      node node_eq ir_config ir_state
      echo_ir_encoded_neighbors_well_formed reachable) as direct.
  specialize (direct owner owner_in).
  destruct direct as [nodup neighbors].
  pose proof (ir_list_node_value_eta
    (ir_processes ir_state owner EchoIRPending)) as pending_shape.
  unfold EchoIRExecutablePending.echo_ir_pending_contents in nodup.
  unfold echo_ir_pending.
  rewrite pending_shape in nodup |- *.
  cbn in nodup |- *.
  exact nodup.
Qed.

(** Every item in a reachable IR pending list is a configured neighbor. *)
Theorem echo_ir_reachable_pending_neighbor
    (ir_state : ir_protocol_state node echo_ir_signature)
    (owner neighbor : node) :
  ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
  In owner all_nodes ->
  In neighbor (echo_ir_pending ir_state owner) ->
  In neighbor all_nodes /\ adj owner neighbor = true.
Proof.
  intros reachable owner_in neighbor_pending.
  pose proof
    (@EchoIRExecutablePending.echo_reachable_pending_well_formed
      node node_eq ir_config ir_state
      echo_ir_encoded_neighbors_well_formed reachable) as direct.
  specialize (direct owner owner_in).
  destruct direct as [nodup valid].
  pose proof (ir_list_node_value_eta
    (ir_processes ir_state owner EchoIRPending)) as pending_shape.
  unfold EchoIRExecutablePending.echo_ir_pending_contents in valid.
  unfold echo_ir_pending in neighbor_pending.
  rewrite pending_shape in valid, neighbor_pending.
  cbn in valid, neighbor_pending.
  specialize (valid neighbor neighbor_pending).
  destruct valid as [configured neighbor_of_owner].
  split.
  - exact configured.
  - unfold ir_config, make_echo_ir_config in neighbor_of_owner.
    cbn [ir_config_neighbors] in neighbor_of_owner.
    unfold nbrs in neighbor_of_owner.
    now apply filter_In in neighbor_of_owner as [_ adjacent].
Qed.

(** A finished process has no outstanding IR pending entries. *)
Theorem echo_ir_reachable_finished_pending_empty
    (ir_state : ir_protocol_state node echo_ir_signature)
    (owner : node) :
  ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
  In owner all_nodes ->
  echo_ir_finished ir_state owner = true ->
  echo_ir_pending ir_state owner = [].
Proof.
  intros reachable owner_in finished.
  pose proof
    (@EchoIRExecutableObligations.echo_reachable_completion
      node node_eq ir_config ir_state reachable) as direct.
  unfold EchoIRExecutableObligations.echo_ir_completion_well_formed in direct.
  specialize (direct owner owner_in).
  unfold EchoIRExecutableDiscovery.echo_ir_finished_value,
    EchoIRExecutableDiscovery.echo_ir_pending_value in direct.
  exact (direct finished).
Qed.

(** Once the IR initiator is finished, no message remains queued. *)
Theorem echo_ir_reachable_finished_initiator_store_empty
    (ir_state : ir_protocol_state node echo_ir_signature) :
  ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
  echo_ir_finished ir_state initiator = true ->
  ir_message_store ir_state = [].
Proof.
  intros reachable finished.
  destruct (ir_message_store ir_state) as [|message rest] eqn:store;
    [reflexivity |].
  assert (queued : In message (ir_message_store ir_state)).
  { rewrite store. now left. }
  pose proof
    (@EchoIRExecutableTopology.echo_reachable_topology_well_formed
      node node_eq ir_config ir_state
      echo_ir_encoded_initiator_configured
      echo_ir_encoded_neighbors_well_formed
      echo_ir_encoded_neighbors_symmetric reachable) as topology.
  destruct topology as [parents_valid queued_edges].
  destruct (queued_edges message queued) as
    [sender_in [receiver_in edge]].
  assert (root_pending : exists root_item,
      In root_item
        (EchoIRExecutableDiscovery.echo_ir_pending_value node ir_state
          (EchoIRExecutableInvariants.echo_ir_config_initiator node ir_config))).
  { destruct (ir_message_kind message) eqn:kind.
    - pose proof
        (@EchoIRExecutableObligations.echo_reachable_queued_requests_pending
          node node_eq ir_config ir_state
          echo_ir_encoded_initiator_configured
          echo_ir_encoded_neighbors_well_formed
          echo_ir_encoded_neighbors_symmetric reachable) as requests.
      pose proof (requests message queued kind) as pending.
      eapply
        (@EchoIRExecutableObligations.echo_reachable_pending_reaches_initiator
          node node_eq ir_config ir_state
          (ir_message_sender message) (ir_message_receiver message)).
      + exact echo_ir_encoded_initiator_configured.
      + exact echo_ir_encoded_neighbors_well_formed.
      + exact echo_ir_encoded_neighbors_symmetric.
      + exact reachable.
      + exact sender_in.
      + exact pending.
    - pose proof
        (@EchoIRExecutableObligations.echo_reachable_queued_replies_pending
          node node_eq ir_config ir_state
          echo_ir_encoded_initiator_configured
          echo_ir_encoded_neighbors_well_formed
          echo_ir_encoded_neighbors_symmetric reachable) as replies.
      pose proof (replies message queued kind) as pending.
      eapply
        (@EchoIRExecutableObligations.echo_reachable_pending_reaches_initiator
          node node_eq ir_config ir_state
          (ir_message_receiver message) (ir_message_sender message)).
      + exact echo_ir_encoded_initiator_configured.
      + exact echo_ir_encoded_neighbors_well_formed.
      + exact echo_ir_encoded_neighbors_symmetric.
      + exact reachable.
      + exact receiver_in.
      + exact pending. }
  destruct root_pending as [root_item root_pending].
  pose proof
    (@EchoIRExecutableObligations.echo_reachable_completion
      node node_eq ir_config ir_state reachable) as completion.
  specialize (completion
    (EchoIRExecutableInvariants.echo_ir_config_initiator node ir_config)
    echo_ir_encoded_initiator_configured).
  assert (direct_finished :
    EchoIRExecutableDiscovery.echo_ir_finished_value node ir_state
      (EchoIRExecutableInvariants.echo_ir_config_initiator node ir_config) =
      true).
  { unfold echo_ir_finished,
      EchoIRExecutableDiscovery.echo_ir_finished_value in finished |- *.
    unfold ir_config, make_echo_ir_config, echo_ir_config_fields,
      EchoIRExecutableInvariants.echo_ir_config_initiator.
    cbn [ir_config_fields ir_node_value_contents] in *.
    exact finished. }
  specialize (completion direct_finished).
  rewrite completion in root_pending. contradiction.
Qed.

(** Reachable IR states contain no self-parent edge. *)
Theorem echo_ir_reachable_no_self_parent
    (ir_state : ir_protocol_state node echo_ir_signature)
    (owner : node) :
  ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
  In owner all_nodes ->
  Tree.echo_ir_parent ir_state owner <> Some owner.
Proof.
  intros reachable owner_in self_parent.
  eapply (@EchoIRExecutableObligations.echo_reachable_no_self_parent
    node node_eq ir_config ir_state owner
    echo_ir_encoded_initiator_configured
    echo_ir_encoded_neighbors_well_formed
    echo_ir_encoded_neighbors_symmetric reachable owner_in).
  unfold EchoIRExecutableDiscovery.echo_ir_parent_value,
    Tree.echo_ir_parent in *.
  exact self_parent.
Qed.

(** Reachable IR states contain no two-node parent cycle. *)
Theorem echo_ir_reachable_no_mutual_parent
    (ir_state : ir_protocol_state node echo_ir_signature)
    (left right : node) :
  ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
  In left all_nodes ->
  In right all_nodes ->
  Tree.echo_ir_parent ir_state left = Some right ->
  Tree.echo_ir_parent ir_state right <> Some left.
Proof.
  intros reachable left_in right_in left_parent right_parent.
  eapply (@EchoIRExecutableObligations.echo_reachable_no_mutual_parent
    node node_eq ir_config ir_state left right
    echo_ir_encoded_initiator_configured
    echo_ir_encoded_neighbors_well_formed
    echo_ir_encoded_neighbors_symmetric reachable left_in).
  - unfold EchoIRExecutableDiscovery.echo_ir_parent_value,
      Tree.echo_ir_parent in *.
    exact left_parent.
  - unfold EchoIRExecutableDiscovery.echo_ir_parent_value,
      Tree.echo_ir_parent in *.
    exact right_parent.
Qed.

End MakeEchoIRSafety.
