(** * Direct topology invariants for executable Echo

    The statements in this module concern only the canonical executable
    configuration, state, [EchoStep], and reachability relation.  No
    Python-shaped transition or refinement model is imported. *)

From Stdlib Require Import List Bool Sorting.Permutation.
Import ListNotations.
Require Import EchoAlgorithm EchoExecutableTypes EchoTransitionIR
  EchoExecutableReachability.

Section EchoExecutableTopology.

Variable node : Type.
Variable node_eq : forall (n m : node), {n = m} + {n <> m}.
Variable config : @echo_config node.

Local Notation initiator := (config_initiator config).
Local Notation all_nodes := (config_nodes config).
Local Notation adj := (config_adjacent config).
Local Notation EchoStep := (@EchoStep node node_eq config).

Hypothesis initiator_in_nodes : In initiator all_nodes.
Hypothesis adj_symmetric :
  forall left right, adj left right = true -> adj right left = true.

Definition echo_parent_edges_valid
    (state : @executable_echo_state node) : Prop :=
  forall child parent,
    In child all_nodes ->
    process_parent (processes state child) = Some parent ->
    In parent all_nodes /\ adj child parent = true.

Definition echo_queued_edges_valid
    (state : @executable_echo_state node) : Prop :=
  forall message,
    In message (message_store state) ->
    In (message_sender message) all_nodes /\
    In (message_receiver message) all_nodes /\
    adj (message_sender message) (message_receiver message) = true.

Definition echo_topology_well_formed
    (state : @executable_echo_state node) : Prop :=
  echo_parent_edges_valid state /\ echo_queued_edges_valid state.

Lemma neighbor_member_valid (source target : node) :
  In target (nbrs all_nodes adj source) ->
  In target all_nodes /\ adj source target = true.
Proof.
  unfold nbrs. intro Hin. now apply filter_In in Hin.
Qed.

Lemma remove_echo_node_in
    (removed candidate : node) (nodes : list node) :
  In candidate (remove_echo_node node_eq removed nodes) ->
  In candidate nodes.
Proof.
  induction nodes as [| head rest IH]; intro Hin.
  - contradiction.
  - cbn [remove_echo_node] in Hin.
    destruct (node_eq removed head).
    + now right.
    + destruct Hin as [Heq | Hin].
      * now left.
      * right. now apply IH.
Qed.

Lemma update_process_self
    (roles : node -> @echo_process node)
    (target : node) (new_process : @echo_process node) :
  update_process node_eq roles target new_process target = new_process.
Proof.
  unfold update_process.
  destruct (node_eq target target); [reflexivity | contradiction].
Qed.

Lemma update_process_other
    (roles : node -> @echo_process node)
    (target : node) (new_process : @echo_process node)
    (candidate : node) :
  target <> candidate ->
  update_process node_eq roles target new_process candidate = roles candidate.
Proof.
  intro Hdifferent. unfold update_process.
  destruct (node_eq target candidate); [contradiction | reflexivity].
Qed.

Lemma materialized_message_from_outbound
    (next_id : nat) (sender : node)
    (outbound : list (@echo_outbound node))
    (message : @echo_message node) :
  In message (materialize_echo_outbound next_id sender outbound) ->
  exists item,
    In item outbound /\
    message_sender message = sender /\
    message_receiver message = outbound_receiver item.
Proof.
  revert next_id.
  induction outbound as [| item rest IH]; intros next_id Hin.
  - contradiction.
  - cbn [materialize_echo_outbound] in Hin.
    destruct Hin as [Heq | Hin].
    + subst message. exists item. cbn. auto.
    + destruct (IH (S next_id) Hin)
        as [found [Hfound [Hsender Hreceiver]]].
      exists found. repeat split.
      * right. exact Hfound.
      * exact Hsender.
      * exact Hreceiver.
Qed.

Lemma apply_echo_delivery_preserves_topology
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (outbound : list (@echo_outbound node)) :
  echo_topology_well_formed state ->
  In selected (message_store state) ->
  (forall parent,
      process_parent new_process = Some parent ->
      In parent all_nodes /\
      adj (message_receiver selected) parent = true) ->
  (forall item,
      In item outbound ->
      In (outbound_receiver item) all_nodes /\
      adj (message_receiver selected) (outbound_receiver item) = true) ->
  echo_topology_well_formed
    (apply_echo_delivery node_eq state selected new_process outbound).
Proof.
  intros [Hparents Hqueued] Hselected Hnew_parent Houtbound.
  pose proof (Hqueued selected Hselected)
    as [Hsender_node [Hreceiver_node Hselected_edge]].
  split.
  - intros child parent Hchild Hparent.
    cbn [apply_echo_delivery] in Hparent.
    change
      (process_parent
        (if node_eq (message_receiver selected) child
         then new_process else processes state child) = Some parent)
      in Hparent.
    destruct (node_eq (message_receiver selected) child)
      as [Heq | Hdifferent].
    + subst child. now apply Hnew_parent.
    + eapply Hparents; eauto.
  - intros message Hin.
    cbn [apply_echo_delivery] in Hin.
    apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + apply remove_echo_message_in in Hin. now apply Hqueued.
    + destruct (materialized_message_from_outbound
        (next_message_id state) (message_receiver selected)
        outbound message Hin)
        as [item [Hitem [Hmessage_sender Hmessage_receiver]]].
      specialize (Houtbound item Hitem).
      destruct Houtbound as [Hitem_node Hitem_edge].
      rewrite Hmessage_sender, Hmessage_receiver. auto.
Qed.

Lemma apply_echo_start_topology
    (state : @executable_echo_state node)
    (ordered_neighbors : list node) :
  echo_initial_on config state ->
  Permutation ordered_neighbors (nbrs all_nodes adj initiator) ->
  echo_topology_well_formed
    (apply_echo_start node_eq initiator state ordered_neighbors).
Proof.
  intros [Hstarted [Hprocesses [Hstore Hnext]]] Hpermutation.
  split.
  - intros child parent Hchild Hparent.
    cbn [apply_echo_start] in Hparent.
    change
      (process_parent
        (if node_eq initiator child
         then mkEchoProcess None ordered_neighbors false
         else processes state child) = Some parent)
      in Hparent.
    destruct (node_eq initiator child) as [Heq | Hdifferent].
    + cbn in Hparent. discriminate.
    + rewrite (Hprocesses child Hchild) in Hparent. discriminate.
  - intros message Hin.
    cbn [apply_echo_start] in Hin.
    change
      (In message
        (message_store state ++
         materialize_echo_outbound (next_message_id state) initiator
           (List.map (mkEchoOutbound EchoRequest) ordered_neighbors)))
      in Hin.
    rewrite Hstore in Hin. cbn in Hin.
    destruct (materialized_message_from_outbound
        (next_message_id state) initiator
        (List.map (mkEchoOutbound EchoRequest) ordered_neighbors)
        message Hin)
      as [item [Hitem [Hmessage_sender Hmessage_receiver]]].
    apply in_map_iff in Hitem.
    destruct Hitem as [neighbor [Hitem Hneighbor]]. subst item.
    cbn in Hmessage_receiver.
    assert (Hneighbor_configured :
        In neighbor (nbrs all_nodes adj initiator)).
    { eapply Permutation_in; eauto. }
    pose proof (neighbor_member_valid initiator neighbor
      Hneighbor_configured) as [Hneighbor_node Hneighbor_edge].
    rewrite Hmessage_sender, Hmessage_receiver. auto.
Qed.

Theorem EchoStep_start_topology
    (state successor : @executable_echo_state node)
    (ordered_neighbors : list node) :
  EchoStep state (EchoStart ordered_neighbors) successor ->
  echo_topology_well_formed successor.
Proof.
  intro Hstep.
  pose proof (@EchoStep_start_guards node node_eq config
    state successor ordered_neighbors Hstep)
    as [Hinitial Hpermutation].
  apply echo_exec_success_rule in Hstep.
  destruct Hstep as [rule [Hrule [Hguards Haction]]].
  cbn [event_tag echo_program lookup_rule ir_event_tag_eqb] in Hrule.
  inversion Hrule. subst rule. clear Hrule Hguards.
  cbn [eval_action start_rule ir_rule_action eval_nodes_expr] in Haction.
  subst successor.
  now apply apply_echo_start_topology.
Qed.

Theorem EchoStep_first_request_nonleaf_topology
    (state successor : @executable_echo_state node)
    (message : @echo_message node)
    (ordered_forwards : list node) :
  echo_topology_well_formed state ->
  EchoStep state (EchoFirstRequestNonLeaf message ordered_forwards) successor ->
  echo_topology_well_formed successor.
Proof.
  intros Htopology Hstep.
  destruct Htopology as [Hparents Hqueued].
  assert (Hselected : In message (message_store state)).
  { exact (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoFirstRequestNonLeaf message ordered_forwards)
      Hstep I). }
  pose proof (Hqueued message Hselected)
    as [Hsender_node [Hreceiver_node Hmessage_edge]].
  assert (Hlookup :
      lookup_rule
        (@event_tag node (EchoFirstRequestNonLeaf message ordered_forwards))
        echo_program = Some first_echo_nonleaf_rule) by reflexivity.
  pose proof (EchoStep_selected_guard_holds state successor
    (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule
    (IRGuardPermutation IRNodesOrdered
      (IRNodesRemove IRMessageSender
        (IRNodesNeighbors IRMessageReceiver)))
    Hstep Hlookup ltac:(
      cbn [first_echo_nonleaf_rule];
      repeat (first [left; reflexivity | right]))) as Hpermutation.
  cbn [guard_holds eval_nodes_expr eval_node_expr event_ordered_nodes
    event_message] in Hpermutation.
  pose proof (EchoStep_selected_action state successor
    (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule Hstep Hlookup) as Haction.
  cbn [eval_action first_echo_nonleaf_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message event_ordered_nodes] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_topology.
  - split; assumption.
  - exact Hselected.
  - intros parent Hparent. cbn in Hparent. inversion Hparent. subst parent.
    split; [exact Hsender_node | now apply adj_symmetric].
  - intros item Hitem. apply in_map_iff in Hitem.
    destruct Hitem as [forward [Hitem Hforward]]. subst item. cbn.
    assert (Hremaining : In forward
        (remove_echo_node node_eq (message_sender message)
          (nbrs all_nodes adj (message_receiver message)))).
    { eapply Permutation_in; eauto. }
    apply remove_echo_node_in in Hremaining.
    now apply neighbor_member_valid in Hremaining.
Qed.

Theorem EchoStep_first_request_leaf_topology
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_topology_well_formed state ->
  EchoStep state (EchoFirstRequestLeaf message) successor ->
  echo_topology_well_formed successor.
Proof.
  intros Htopology Hstep.
  destruct Htopology as [Hparents Hqueued].
  assert (Hselected : In message (message_store state)).
  { exact (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoFirstRequestLeaf message) Hstep I). }
  pose proof (Hqueued message Hselected)
    as [Hsender_node [Hreceiver_node Hmessage_edge]].
  assert (Hlookup :
      lookup_rule (@event_tag node (EchoFirstRequestLeaf message))
        echo_program = Some first_echo_leaf_rule) by reflexivity.
  pose proof (EchoStep_selected_action state successor
    (EchoFirstRequestLeaf message) first_echo_leaf_rule
    Hstep Hlookup) as Haction.
  cbn [eval_action first_echo_leaf_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_topology.
  - split; assumption.
  - exact Hselected.
  - intros parent Hparent. cbn in Hparent. inversion Hparent. subst parent.
    split; [exact Hsender_node | now apply adj_symmetric].
  - intros item Hitem. cbn in Hitem.
    destruct Hitem as [Heq | Hin]; [subst item | contradiction].
    cbn. split; [exact Hsender_node | now apply adj_symmetric].
Qed.

Theorem EchoStep_repeated_request_topology
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_topology_well_formed state ->
  EchoStep state (EchoRepeatedRequest message) successor ->
  echo_topology_well_formed successor.
Proof.
  intros Htopology Hstep.
  destruct Htopology as [Hparents Hqueued].
  assert (Hselected : In message (message_store state)).
  { exact (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoRepeatedRequest message) Hstep I). }
  pose proof (Hqueued message Hselected)
    as [Hsender_node [Hreceiver_node Hmessage_edge]].
  assert (Hlookup :
      lookup_rule (@event_tag node (EchoRepeatedRequest message))
        echo_program = Some repeated_echo_rule) by reflexivity.
  pose proof (EchoStep_selected_action state successor
    (EchoRepeatedRequest message) repeated_echo_rule
    Hstep Hlookup) as Haction.
  cbn [eval_action repeated_echo_rule ir_rule_action
    eval_process_expr eval_node_expr eval_outbound_expr event_message]
    in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_topology.
  - split; assumption.
  - exact Hselected.
  - intros parent Hparent.
    now apply (Hparents (message_receiver message) parent Hreceiver_node).
  - intros item Hitem. cbn in Hitem.
    destruct Hitem as [Heq | Hin]; [subst item | contradiction].
    cbn. split; [exact Hsender_node | now apply adj_symmetric].
Qed.

Theorem EchoStep_initiator_request_topology
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_topology_well_formed state ->
  EchoStep state (EchoInitiatorRequest message) successor ->
  echo_topology_well_formed successor.
Proof.
  intros Htopology Hstep.
  destruct Htopology as [Hparents Hqueued].
  assert (Hselected : In message (message_store state)).
  { exact (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoInitiatorRequest message) Hstep I). }
  pose proof (Hqueued message Hselected)
    as [Hsender_node [Hreceiver_node Hmessage_edge]].
  assert (Hlookup :
      lookup_rule (@event_tag node (EchoInitiatorRequest message))
        echo_program = Some initiator_echo_rule) by reflexivity.
  pose proof (EchoStep_selected_guard_holds state successor
    (EchoInitiatorRequest message) initiator_echo_rule
    (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
    Hstep Hlookup ltac:(
      cbn [initiator_echo_rule];
      repeat (first [left; reflexivity | right]))) as Hreceiver_eq.
  cbn [guard_holds eval_node_expr event_message] in Hreceiver_eq.
  pose proof (EchoStep_selected_action state successor
    (EchoInitiatorRequest message) initiator_echo_rule
    Hstep Hlookup) as Haction.
  cbn [eval_action initiator_echo_rule ir_rule_action
    eval_process_expr eval_node_expr eval_outbound_expr event_message]
    in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_topology.
  - split; assumption.
  - exact Hselected.
  - intros parent Hparent.
    rewrite Hreceiver_eq.
    now apply (Hparents initiator parent initiator_in_nodes).
  - intros item Hitem. cbn in Hitem.
    destruct Hitem as [Heq | Hin]; [subst item | contradiction].
    cbn. split; [exact Hsender_node | now apply adj_symmetric].
Qed.

Theorem EchoStep_participant_reply_more_topology
    (state successor : @executable_echo_state node)
    (message : @echo_message node) (parent : node) :
  echo_topology_well_formed state ->
  EchoStep state (EchoParticipantReplyMore message parent) successor ->
  echo_topology_well_formed successor.
Proof.
  intros Htopology Hstep.
  destruct Htopology as [Hparents Hqueued].
  assert (Hselected : In message (message_store state)).
  { exact (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoParticipantReplyMore message parent) Hstep I). }
  pose proof (Hqueued message Hselected)
    as [Hsender_node [Hreceiver_node Hmessage_edge]].
  assert (Hlookup :
      lookup_rule
        (@event_tag node (EchoParticipantReplyMore message parent))
        echo_program = Some participant_ack_more_rule) by reflexivity.
  pose proof (EchoStep_selected_guard_holds state successor
    (EchoParticipantReplyMore message parent) participant_ack_more_rule
    (IRGuardParentEqual IRMessageReceiver (IRSomeParent IREventParent))
    Hstep Hlookup ltac:(
      cbn [participant_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as Hparent.
  cbn [guard_holds eval_node_expr eval_parent_expr event_message
    event_parent] in Hparent.
  pose proof (Hparents (message_receiver message) parent
    Hreceiver_node Hparent) as Hparent_valid.
  pose proof (EchoStep_selected_action state successor
    (EchoParticipantReplyMore message parent) participant_ack_more_rule
    Hstep Hlookup) as Haction.
  cbn [eval_action participant_ack_more_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message event_parent] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_topology.
  - split; assumption.
  - exact Hselected.
  - intros selected_parent Hselected_parent.
    cbn in Hselected_parent. inversion Hselected_parent.
    subst selected_parent.
    exact Hparent_valid.
  - intros item Hitem. contradiction.
Qed.

Theorem EchoStep_participant_reply_final_topology
    (state successor : @executable_echo_state node)
    (message : @echo_message node) (parent : node) :
  echo_topology_well_formed state ->
  EchoStep state (EchoParticipantReplyFinal message parent) successor ->
  echo_topology_well_formed successor.
Proof.
  intros Htopology Hstep.
  destruct Htopology as [Hparents Hqueued].
  assert (Hselected : In message (message_store state)).
  { exact (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoParticipantReplyFinal message parent) Hstep I). }
  pose proof (Hqueued message Hselected)
    as [Hsender_node [Hreceiver_node Hmessage_edge]].
  assert (Hlookup :
      lookup_rule
        (@event_tag node (EchoParticipantReplyFinal message parent))
        echo_program = Some participant_ack_final_rule) by reflexivity.
  pose proof (EchoStep_selected_guard_holds state successor
    (EchoParticipantReplyFinal message parent) participant_ack_final_rule
    (IRGuardParentEqual IRMessageReceiver (IRSomeParent IREventParent))
    Hstep Hlookup ltac:(
      cbn [participant_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as Hparent.
  cbn [guard_holds eval_node_expr eval_parent_expr event_message
    event_parent] in Hparent.
  pose proof (Hparents (message_receiver message) parent
    Hreceiver_node Hparent) as Hparent_valid.
  pose proof (EchoStep_selected_action state successor
    (EchoParticipantReplyFinal message parent) participant_ack_final_rule
    Hstep Hlookup) as Haction.
  cbn [eval_action participant_ack_final_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message event_parent] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_topology.
  - split; assumption.
  - exact Hselected.
  - intros selected_parent Hselected_parent.
    cbn in Hselected_parent. inversion Hselected_parent.
    subst selected_parent.
    exact Hparent_valid.
  - intros item Hitem. cbn in Hitem.
    destruct Hitem as [Heq | Hin]; [subst item | contradiction].
    cbn. exact Hparent_valid.
Qed.

Theorem EchoStep_initiator_reply_more_topology
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_topology_well_formed state ->
  EchoStep state (EchoInitiatorReplyMore message) successor ->
  echo_topology_well_formed successor.
Proof.
  intros Htopology Hstep.
  destruct Htopology as [Hparents Hqueued].
  assert (Hselected : In message (message_store state)).
  { exact (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoInitiatorReplyMore message) Hstep I). }
  assert (Hlookup :
      lookup_rule (@event_tag node (EchoInitiatorReplyMore message))
        echo_program = Some initiator_ack_more_rule) by reflexivity.
  pose proof (EchoStep_selected_action state successor
    (EchoInitiatorReplyMore message) initiator_ack_more_rule
    Hstep Hlookup) as Haction.
  cbn [eval_action initiator_ack_more_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_topology.
  - split; assumption.
  - exact Hselected.
  - intros parent Hparent. discriminate.
  - intros item Hitem. contradiction.
Qed.

Theorem EchoStep_initiator_reply_final_topology
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_topology_well_formed state ->
  EchoStep state (EchoInitiatorReplyFinal message) successor ->
  echo_topology_well_formed successor.
Proof.
  intros Htopology Hstep.
  destruct Htopology as [Hparents Hqueued].
  assert (Hselected : In message (message_store state)).
  { exact (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoInitiatorReplyFinal message) Hstep I). }
  assert (Hlookup :
      lookup_rule (@event_tag node (EchoInitiatorReplyFinal message))
        echo_program = Some initiator_ack_final_rule) by reflexivity.
  pose proof (EchoStep_selected_action state successor
    (EchoInitiatorReplyFinal message) initiator_ack_final_rule
    Hstep Hlookup) as Haction.
  cbn [eval_action initiator_ack_final_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message] in Haction.
  subst successor.
  apply apply_echo_delivery_preserves_topology.
  - split; assumption.
  - exact Hselected.
  - intros parent Hparent. discriminate.
  - intros item Hitem. contradiction.
Qed.

Theorem EchoStep_preserves_topology
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  echo_topology_well_formed state ->
  EchoStep state event successor ->
  echo_topology_well_formed successor.
Proof.
  intros Htopology Hstep. destruct event.
  - exact (EchoStep_start_topology state successor ordered_neighbors Hstep).
  - eapply EchoStep_first_request_nonleaf_topology;
      [exact Htopology | exact Hstep].
  - eapply EchoStep_first_request_leaf_topology;
      [exact Htopology | exact Hstep].
  - eapply EchoStep_repeated_request_topology;
      [exact Htopology | exact Hstep].
  - eapply EchoStep_initiator_request_topology;
      [exact Htopology | exact Hstep].
  - eapply EchoStep_participant_reply_more_topology;
      [exact Htopology | exact Hstep].
  - eapply EchoStep_participant_reply_final_topology;
      [exact Htopology | exact Hstep].
  - eapply EchoStep_initiator_reply_more_topology;
      [exact Htopology | exact Hstep].
  - eapply EchoStep_initiator_reply_final_topology;
      [exact Htopology | exact Hstep].
Qed.

Lemma initial_executable_echo_state_topology :
  echo_topology_well_formed initial_executable_echo_state.
Proof.
  split.
  - intros child parent Hchild Hparent. discriminate.
  - intros message Hin. contradiction.
Qed.

Theorem echo_reachable_topology
    (state : @executable_echo_state node) :
  @echo_reachable node node_eq config state ->
  echo_topology_well_formed state.
Proof.
  intro Hreachable.
  induction Hreachable as [| before event after Hbefore IH Hstep].
  - apply initial_executable_echo_state_topology.
  - eapply EchoStep_preserves_topology.
    + exact IH.
    + exact Hstep.
Qed.

End EchoExecutableTopology.

Arguments echo_parent_edges_valid {node} config _.
Arguments echo_queued_edges_valid {node} config _.
Arguments echo_topology_well_formed {node} config _.
