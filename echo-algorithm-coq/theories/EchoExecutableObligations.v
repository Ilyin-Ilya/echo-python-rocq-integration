(** * Direct pending/message obligations for executable Echo

    This module connects the canonical message store to process pending lists.
    It establishes the causal facts needed to remove a pending slot safely,
    proves both directions of the queue-to-pending correspondence, and proves
    the local unfinished-child link used to propagate obligations toward the
    root. *)

From Stdlib Require Import List Bool Lia Sorting.Permutation.
Import ListNotations.
Require Import EchoAlgorithm EchoExecutableTypes EchoTransitionIR
  EchoExecutableReachability EchoExecutableTopology EchoExecutablePending
  EchoExecutableLifecycle EchoExecutableCompletion EchoExecutableForest
  EchoExecutableDiscovery EchoExecutableRequestAccounting.

Section EchoExecutableObligations.

Variable node : Type.
Variable node_eq : forall (n m : node), {n = m} + {n <> m}.
Variable config : @echo_config node.

Local Notation initiator := (config_initiator config).
Local Notation all_nodes := (config_nodes config).
Local Notation adj := (config_adjacent config).
Local Notation EchoStep := (@EchoStep node node_eq config).

Hypothesis nodes_nodup : NoDup all_nodes.
Hypothesis initiator_in_nodes : In initiator all_nodes.
Hypothesis adj_symmetric :
  forall left right, adj left right = true -> adj right left = true.

(** Every reply emitted by a non-initiator comes from a process that has
    already left its initial state.  The initiator is excluded because its
    parent is always [None], and only non-initiator senders matter when a
    first request installs a parent. *)
Definition echo_reply_noninitiator_senders_discovered
    (state : @executable_echo_state node) : Prop :=
  forall message,
    In message (message_store state) ->
    message_kind message = EchoReply ->
    message_sender message <> initiator ->
    echo_discovered state (message_sender message).

Lemma parent_or_finished_process_discovered
    (process : @echo_process node) :
  ((exists parent, process_parent process = Some parent) \/
    process_finished process = true) ->
  process <> initial_echo_process.
Proof.
  intros [[parent Hparent] | Hfinished] Hequal;
    rewrite Hequal in *; discriminate.
Qed.

Lemma apply_echo_delivery_preserves_reply_noninitiator_senders_discovered
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (outbound : list (@echo_outbound node)) :
  echo_reply_noninitiator_senders_discovered state ->
  (echo_discovered state (message_receiver selected) ->
    new_process <> initial_echo_process) ->
  (forall item,
      In item outbound ->
      outbound_kind item = EchoReply ->
      message_receiver selected <> initiator ->
      new_process <> initial_echo_process) ->
  echo_reply_noninitiator_senders_discovered
    (apply_echo_delivery node_eq state selected new_process outbound).
Proof.
  intros Hold Hmonotone Hnew message Hin Hkind Hnot_initiator.
  cbn [apply_echo_delivery] in Hin.
  apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - pose proof (@remove_echo_message_in node
      (message_id selected) (message_store state) message Hin) as Hold_message.
    eapply apply_echo_delivery_discovered_monotone.
    + exact Hmonotone.
    + now eapply Hold.
  - destruct (@materialized_echo_message_complete_fields node
      (next_message_id state) (message_receiver selected)
      outbound message Hin)
      as [item [Hitem [Hsender [Hreceiver Hitem_kind]]]].
    unfold echo_discovered. rewrite Hsender.
    rewrite apply_echo_delivery_process_self.
    apply Hnew with (item := item).
    + exact Hitem.
    + now rewrite <- Hitem_kind.
    + now rewrite <- Hsender.
Qed.

Theorem EchoStep_start_reply_noninitiator_senders_discovered
    (state successor : @executable_echo_state node)
    (ordered_neighbors : list node) :
  EchoStep state (EchoStart ordered_neighbors) successor ->
  echo_reply_noninitiator_senders_discovered successor.
Proof.
  intro Hstep.
  pose proof (@EchoStep_start_guards node node_eq config
    state successor ordered_neighbors Hstep) as [Hinitial Hpermutation].
  destruct Hinitial as [Hstarted [Hprocesses [Hstore Hnext]]].
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoStart ordered_neighbors) start_rule Hstep eq_refl) as Haction.
  cbn [eval_action start_rule ir_rule_action eval_nodes_expr] in Haction.
  subst successor.
  intros message Hin Hkind Hnot_initiator.
  change (In message
    (message_store state ++
      materialize_echo_outbound (next_message_id state) initiator
        (List.map (mkEchoOutbound EchoRequest) ordered_neighbors))) in Hin.
  rewrite Hstore in Hin. cbn in Hin.
  destruct (@materialized_request_block_fields node
      (next_message_id state) initiator ordered_neighbors message Hin)
    as [Hsender [Hrequest_kind Hreceiver]].
  congruence.
Qed.

Theorem EchoStep_preserves_reply_noninitiator_senders_discovered
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  echo_reply_noninitiator_senders_discovered state ->
  EchoStep state event successor ->
  echo_reply_noninitiator_senders_discovered successor.
Proof.
  intros Hreplies Hstep. destruct event.
  - now apply EchoStep_start_reply_noninitiator_senders_discovered in Hstep.
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoFirstRequestNonLeaf message ordered_forwards)
      first_echo_nonleaf_rule (IRGuardProcessInitial IRMessageReceiver)
      Hstep eq_refl ltac:(
        cbn [first_echo_nonleaf_rule];
        repeat (first [left; reflexivity | right]))) as Hinitial.
    cbn [guard_holds eval_node_expr event_message] in Hinitial.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoFirstRequestNonLeaf message ordered_forwards)
      first_echo_nonleaf_rule Hstep eq_refl) as Haction.
    cbn [eval_action first_echo_nonleaf_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_ordered_nodes] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_reply_noninitiator_senders_discovered.
    + exact Hreplies.
    + intro Hdiscovered. unfold echo_discovered in Hdiscovered.
      rewrite Hinitial in Hdiscovered. contradiction.
    + intros item Hitem Hkind Hnot_initiator.
      apply in_map_iff in Hitem.
      destruct Hitem as [receiver [Hequal Hreceiver]].
      subst item. discriminate.
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoFirstRequestLeaf message) first_echo_leaf_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action first_echo_leaf_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_reply_noninitiator_senders_discovered.
    + exact Hreplies.
    + intros Hdiscovered. apply parented_process_discovered.
    + intros item Hitem Hkind Hnot_initiator.
      apply parented_process_discovered.
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoRepeatedRequest message) repeated_echo_rule
      (IRGuardHasParentOrFinished IRMessageReceiver)
      Hstep eq_refl ltac:(
        cbn [repeated_echo_rule];
        repeat (first [left; reflexivity | right]))) as Hactive.
    cbn [guard_holds eval_node_expr event_message] in Hactive.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoRepeatedRequest message) repeated_echo_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action repeated_echo_rule ir_rule_action
      eval_process_expr eval_node_expr eval_outbound_expr event_message]
      in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_reply_noninitiator_senders_discovered.
    + exact Hreplies.
    + intros Hdiscovered. exact Hdiscovered.
    + intros item Hitem Hkind Hnot_initiator.
      now apply parent_or_finished_process_discovered.
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorRequest message) initiator_echo_rule
      (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [initiator_echo_rule];
        repeat (first [left; reflexivity | right]))) as Hequal.
    cbn [guard_holds eval_node_expr event_message] in Hequal.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorRequest message) initiator_echo_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_echo_rule ir_rule_action
      eval_process_expr eval_node_expr eval_outbound_expr event_message]
      in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_reply_noninitiator_senders_discovered.
    + exact Hreplies.
    + intros Hdiscovered. rewrite Hequal in Hdiscovered.
      exact Hdiscovered.
    + intros item Hitem Hkind Hnot_initiator.
      rewrite Hequal in Hnot_initiator. contradiction.
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoParticipantReplyMore message parent) participant_ack_more_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action participant_ack_more_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_parent] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_reply_noninitiator_senders_discovered.
    + exact Hreplies.
    + intros Hdiscovered. apply parented_process_discovered.
    + intros item Hitem. contradiction.
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoParticipantReplyFinal message parent) participant_ack_final_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action participant_ack_final_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_parent] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_reply_noninitiator_senders_discovered.
    + exact Hreplies.
    + intros Hdiscovered. apply parented_process_discovered.
    + intros item Hitem Hkind Hnot_initiator.
      apply parented_process_discovered.
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorReplyMore message) initiator_ack_more_rule
      (IRGuardNodesNonempty
        (IRNodesRemove IRMessageSender
          (IRNodesPending IRInitiatorNode)))
      Hstep eq_refl ltac:(
        cbn [initiator_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hnonempty.
    cbn [guard_holds eval_nodes_expr eval_node_expr event_message]
      in Hnonempty.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorReplyMore message) initiator_ack_more_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_ack_more_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_reply_noninitiator_senders_discovered.
    + exact Hreplies.
    + intros Hdiscovered. now apply nonempty_root_discovered.
    + intros item Hitem. contradiction.
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorReplyFinal message) initiator_ack_final_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_ack_final_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_reply_noninitiator_senders_discovered.
    + exact Hreplies.
    + intros Hdiscovered. apply finished_root_discovered.
    + intros item Hitem. contradiction.
Qed.

Lemma initial_executable_echo_state_reply_noninitiator_senders_discovered :
  echo_reply_noninitiator_senders_discovered initial_executable_echo_state.
Proof.
  intros message Hin. contradiction.
Qed.

Theorem echo_reachable_reply_noninitiator_senders_discovered
    (state : @executable_echo_state node) :
  echo_reachable node_eq config state ->
  echo_reply_noninitiator_senders_discovered state.
Proof.
  intro Hreachable.
  induction Hreachable as [| before event after Hbefore IH Hstep].
  - apply initial_executable_echo_state_reply_noninitiator_senders_discovered.
  - eapply EchoStep_preserves_reply_noninitiator_senders_discovered; eauto.
Qed.

(** A queued reply that follows the sender's installed parent edge is the
    sender's final reply.  Therefore the sender is already finished.  Cycle
    replies point to non-parent neighbors and do not satisfy the antecedent. *)
Definition echo_parent_replies_from_finished
    (state : @executable_echo_state node) : Prop :=
  forall message,
    In message (message_store state) ->
    message_kind message = EchoReply ->
    process_parent (processes state (message_sender message)) =
      Some (message_receiver message) ->
    process_finished (processes state (message_sender message)) = true.

Lemma apply_echo_delivery_preserves_parent_replies_from_finished
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (outbound : list (@echo_outbound node)) :
  echo_parent_replies_from_finished state ->
  (forall message,
      In message (message_store state) ->
      message_kind message = EchoReply ->
      message_sender message = message_receiver selected ->
      process_parent new_process = Some (message_receiver message) ->
      process_finished new_process = true) ->
  (forall item,
      In item outbound ->
      outbound_kind item = EchoReply ->
      process_parent new_process = Some (outbound_receiver item) ->
      process_finished new_process = true) ->
  echo_parent_replies_from_finished
    (apply_echo_delivery node_eq state selected new_process outbound).
Proof.
  intros Hold Hupdated Hnew message Hin Hkind Hparent.
  cbn [apply_echo_delivery] in Hin.
  apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - pose proof (@remove_echo_message_in node
      (message_id selected) (message_store state) message Hin) as Hold_message.
    destruct (node_eq (message_receiver selected)
        (message_sender message)) as [Hequal | Hdifferent].
    + rewrite <- Hequal in Hparent |- *.
      rewrite apply_echo_delivery_process_self in Hparent |- *.
      apply Hupdated with (message := message).
      * exact Hold_message.
      * exact Hkind.
      * now symmetry.
      * exact Hparent.
    + rewrite apply_echo_delivery_process_other in Hparent
        by exact Hdifferent.
      rewrite apply_echo_delivery_process_other by exact Hdifferent.
      now eapply Hold.
  - destruct (@materialized_echo_message_complete_fields node
      (next_message_id state) (message_receiver selected)
      outbound message Hin)
      as [item [Hitem [Hsender [Hreceiver Hitem_kind]]]].
    rewrite Hsender in Hparent |- *.
    rewrite apply_echo_delivery_process_self in Hparent |- *.
    apply Hnew with (item := item).
    + exact Hitem.
    + now rewrite <- Hitem_kind.
    + now rewrite <- Hreceiver.
Qed.

Theorem EchoStep_start_parent_replies_from_finished
    (state successor : @executable_echo_state node)
    (ordered_neighbors : list node) :
  EchoStep state (EchoStart ordered_neighbors) successor ->
  echo_parent_replies_from_finished successor.
Proof.
  intro Hstep.
  pose proof (@EchoStep_start_guards node node_eq config
    state successor ordered_neighbors Hstep) as [Hinitial Hpermutation].
  destruct Hinitial as [Hstarted [Hprocesses [Hstore Hnext]]].
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoStart ordered_neighbors) start_rule Hstep eq_refl) as Haction.
  cbn [eval_action start_rule ir_rule_action eval_nodes_expr] in Haction.
  subst successor.
  intros message Hin Hkind Hparent.
  change (In message
    (message_store state ++
      materialize_echo_outbound (next_message_id state) initiator
        (List.map (mkEchoOutbound EchoRequest) ordered_neighbors))) in Hin.
  rewrite Hstore in Hin. cbn in Hin.
  destruct (@materialized_request_block_fields node
      (next_message_id state) initiator ordered_neighbors message Hin)
    as [Hsender [Hrequest_kind Hreceiver]].
  congruence.
Qed.

Theorem EchoStep_preserves_parent_replies_from_finished
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  echo_lifecycle_well_formed config state ->
  echo_request_parent_distinct state ->
  echo_reply_noninitiator_senders_discovered state ->
  echo_parent_replies_from_finished state ->
  EchoStep state event successor ->
  echo_parent_replies_from_finished successor.
Proof.
  intros Hlifecycle Hrequest_parent Hreply_senders Hparent_replies Hstep.
  destruct event.
  - now apply EchoStep_start_parent_replies_from_finished in Hstep.
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoFirstRequestNonLeaf message ordered_forwards)
      first_echo_nonleaf_rule
      (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [first_echo_nonleaf_rule];
        repeat (first [left; reflexivity | right]))) as Hnot_initiator.
    cbn [guard_holds eval_node_expr event_message] in Hnot_initiator.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoFirstRequestNonLeaf message ordered_forwards)
      first_echo_nonleaf_rule (IRGuardProcessInitial IRMessageReceiver)
      Hstep eq_refl ltac:(
        cbn [first_echo_nonleaf_rule];
        repeat (first [left; reflexivity | right]))) as Hinitial.
    cbn [guard_holds eval_node_expr event_message] in Hinitial.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoFirstRequestNonLeaf message ordered_forwards)
      first_echo_nonleaf_rule Hstep eq_refl) as Haction.
    cbn [eval_action first_echo_nonleaf_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_ordered_nodes] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_parent_replies_from_finished.
    + exact Hparent_replies.
    + intros reply Hreply Hkind Hsender Hparent.
      pose proof (Hreply_senders reply Hreply Hkind) as Hdiscovered.
      specialize (Hdiscovered ltac:(now rewrite Hsender)).
      unfold echo_discovered in Hdiscovered.
      rewrite Hsender, Hinitial in Hdiscovered. contradiction.
    + intros item Hitem Hkind Hparent.
      apply in_map_iff in Hitem.
      destruct Hitem as [receiver [Hequal Hreceiver]].
      subst item. discriminate.
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoFirstRequestLeaf message) first_echo_leaf_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action first_echo_leaf_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_parent_replies_from_finished.
    + exact Hparent_replies.
    + intros reply Hreply Hkind Hsender Hparent. reflexivity.
    + intros item Hitem Hkind Hparent. reflexivity.
  - pose proof (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoRepeatedRequest message) Hstep I) as Hselected.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoRepeatedRequest message) repeated_echo_rule
      (IRGuardKind EchoRequest) Hstep eq_refl ltac:(left; reflexivity))
      as Hkind.
    cbn [guard_holds event_message] in Hkind.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoRepeatedRequest message) repeated_echo_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action repeated_echo_rule ir_rule_action
      eval_process_expr eval_node_expr eval_outbound_expr event_message]
      in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_parent_replies_from_finished.
    + exact Hparent_replies.
    + intros reply Hreply Hreply_kind Hsender Hparent.
      rewrite <- Hsender.
      apply (Hparent_replies reply Hreply Hreply_kind).
      now rewrite Hsender.
    + intros item Hitem Hitem_kind Hparent.
      cbn in Hitem. destruct Hitem as [Hequal | Hin]; [| contradiction].
      subst item. cbn in Hparent.
      exfalso. exact (Hrequest_parent message Hselected Hkind Hparent).
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorRequest message) initiator_echo_rule
      (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [initiator_echo_rule];
        repeat (first [left; reflexivity | right]))) as Hequal.
    cbn [guard_holds eval_node_expr event_message] in Hequal.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorRequest message) initiator_echo_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_echo_rule ir_rule_action
      eval_process_expr eval_node_expr eval_outbound_expr event_message]
      in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_parent_replies_from_finished.
    + exact Hparent_replies.
    + intros reply Hreply Hreply_kind Hsender Hparent.
      rewrite Hequal in Hsender.
      rewrite <- Hsender.
      apply (Hparent_replies reply Hreply Hreply_kind).
      now rewrite Hsender.
    + intros item Hitem Hitem_kind Hparent.
      destruct (Hlifecycle initiator initiator_in_nodes) as [Hroot _].
      specialize (Hroot eq_refl). rewrite Hroot in Hparent.
      discriminate.
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoParticipantReplyMore message parent)
      participant_ack_more_rule
      (IRGuardParentEqual IRMessageReceiver (IRSomeParent IREventParent))
      Hstep eq_refl ltac:(
        cbn [participant_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hparent.
    cbn [guard_holds eval_node_expr eval_parent_expr event_message
      event_parent] in Hparent.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoParticipantReplyMore message parent)
      participant_ack_more_rule
      (IRGuardFinished IRMessageReceiver false)
      Hstep eq_refl ltac:(
        cbn [participant_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hunfinished.
    cbn [guard_holds eval_node_expr event_message] in Hunfinished.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoParticipantReplyMore message parent) participant_ack_more_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action participant_ack_more_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_parent] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_parent_replies_from_finished.
    + exact Hparent_replies.
    + intros reply Hreply Hkind Hsender Hnew_parent.
      assert (Hreply_receiver : message_receiver reply = parent).
      { cbn in Hnew_parent. now injection Hnew_parent. }
      pose proof (Hparent_replies reply Hreply Hkind) as Hfinished.
      specialize (Hfinished ltac:(now rewrite Hsender, Hreply_receiver, Hparent)).
      rewrite Hsender, Hunfinished in Hfinished. discriminate.
    + intros item Hitem. contradiction.
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoParticipantReplyFinal message parent) participant_ack_final_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action participant_ack_final_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_parent] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_parent_replies_from_finished.
    + exact Hparent_replies.
    + intros reply Hreply Hkind Hsender Hparent'. reflexivity.
    + intros item Hitem Hkind Hparent'. reflexivity.
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorReplyMore message) initiator_ack_more_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_ack_more_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_parent_replies_from_finished.
    + exact Hparent_replies.
    + intros reply Hreply Hkind Hsender Hparent'. discriminate.
    + intros item Hitem. contradiction.
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorReplyFinal message) initiator_ack_final_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_ack_final_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_parent_replies_from_finished.
    + exact Hparent_replies.
    + intros reply Hreply Hkind Hsender Hparent'. reflexivity.
    + intros item Hitem. contradiction.
Qed.

Lemma initial_executable_echo_state_parent_replies_from_finished :
  echo_parent_replies_from_finished initial_executable_echo_state.
Proof.
  intros message Hin. contradiction.
Qed.

Theorem echo_reachable_parent_replies_from_finished
    (state : @executable_echo_state node) :
  echo_reachable node_eq config state ->
  echo_parent_replies_from_finished state.
Proof.
  intro Hreachable.
  induction Hreachable as [| before event after Hbefore IH Hstep].
  - apply initial_executable_echo_state_parent_replies_from_finished.
  - eapply EchoStep_preserves_parent_replies_from_finished.
    + exact (@echo_reachable_lifecycle node node_eq config
        initiator_in_nodes adj_symmetric before Hbefore).
    + exact (@echo_reachable_request_parent_distinct node node_eq config
        nodes_nodup before Hbefore).
    + exact (echo_reachable_reply_noninitiator_senders_discovered
        before Hbefore).
    + exact IH.
    + exact Hstep.
Qed.

(** Replies, like requests, are unique for each directed sender/receiver edge.
    A request-response rule cannot duplicate an old reply because that would
    place the selected request beside its reverse reply.  A participant's
    final reply cannot duplicate an old parent-directed reply because such an
    old reply would already imply that the participant was finished. *)
Definition reply_edges_unique
    (messages : list (@echo_message node)) : Prop :=
  forall first second,
    In first messages ->
    In second messages ->
    message_kind first = EchoReply ->
    message_kind second = EchoReply ->
    message_sender first = message_sender second ->
    message_receiver first = message_receiver second ->
    first = second.

Definition echo_reply_edges_unique
    (state : @executable_echo_state node) : Prop :=
  reply_edges_unique (message_store state).

Lemma reply_edges_unique_sublist
    (smaller larger : list (@echo_message node)) :
  (forall message, In message smaller -> In message larger) ->
  reply_edges_unique larger ->
  reply_edges_unique smaller.
Proof.
  intros Hsubset Hunique first second Hfirst Hsecond
    Hfirst_kind Hsecond_kind Hsender Hreceiver.
  eapply Hunique; eauto.
Qed.

Lemma materialized_block_has_no_replies
    (next_id : nat) (sender : node)
    (outbound : list (@echo_outbound node)) :
  (forall item,
      In item outbound -> outbound_kind item <> EchoReply) ->
  forall message,
    In message (materialize_echo_outbound next_id sender outbound) ->
    message_kind message <> EchoReply.
Proof.
  intros Houtbound message Hin Hreply.
  destruct (@materialized_echo_message_complete_fields node
      next_id sender outbound message Hin)
    as [item [Hitem [Hsender [Hreceiver Hkind]]]].
  apply (Houtbound item Hitem). now rewrite <- Hkind.
Qed.

Lemma apply_echo_delivery_preserves_reply_edges_unique_no_replies
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (outbound : list (@echo_outbound node)) :
  echo_reply_edges_unique state ->
  (forall item,
      In item outbound -> outbound_kind item <> EchoReply) ->
  echo_reply_edges_unique
    (apply_echo_delivery node_eq state selected new_process outbound).
Proof.
  intros Hunique Houtbound.
  unfold echo_reply_edges_unique in *.
  cbn [apply_echo_delivery].
  intros first second Hfirst Hsecond Hfirst_kind Hsecond_kind
    Hsender Hreceiver.
  apply in_app_or in Hfirst. apply in_app_or in Hsecond.
  destruct Hfirst as [Hfirst | Hfirst];
    destruct Hsecond as [Hsecond | Hsecond].
  - eapply Hunique.
    + exact (@remove_echo_message_in node
        (message_id selected) (message_store state) first Hfirst).
    + exact (@remove_echo_message_in node
        (message_id selected) (message_store state) second Hsecond).
    + exact Hfirst_kind.
    + exact Hsecond_kind.
    + exact Hsender.
    + exact Hreceiver.
  - exfalso. exact (materialized_block_has_no_replies
      (next_message_id state) (message_receiver selected) outbound
      Houtbound second Hsecond Hsecond_kind).
  - exfalso. exact (materialized_block_has_no_replies
      (next_message_id state) (message_receiver selected) outbound
      Houtbound first Hfirst Hfirst_kind).
  - exfalso. exact (materialized_block_has_no_replies
      (next_message_id state) (message_receiver selected) outbound
      Houtbound first Hfirst Hfirst_kind).
Qed.

Lemma apply_request_reply_preserves_reply_edges_unique
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node) :
  echo_reply_edges_unique state ->
  echo_request_reply_reverse_distinct state ->
  In selected (message_store state) ->
  message_kind selected = EchoRequest ->
  echo_reply_edges_unique
    (apply_echo_delivery node_eq state selected new_process
      [mkEchoOutbound EchoReply (message_sender selected)]).
Proof.
  intros Hunique Hreverse Hselected Hselected_kind.
  unfold echo_reply_edges_unique in *.
  cbn [apply_echo_delivery].
  intros first second Hfirst Hsecond Hfirst_kind Hsecond_kind
    Hsender Hreceiver.
  apply in_app_or in Hfirst. apply in_app_or in Hsecond.
  destruct Hfirst as [Hfirst | Hfirst];
    destruct Hsecond as [Hsecond | Hsecond].
  - eapply Hunique.
    + exact (@remove_echo_message_in node
        (message_id selected) (message_store state) first Hfirst).
    + exact (@remove_echo_message_in node
        (message_id selected) (message_store state) second Hsecond).
    + exact Hfirst_kind.
    + exact Hsecond_kind.
    + exact Hsender.
    + exact Hreceiver.
  - cbn [materialize_echo_outbound] in Hsecond.
    destruct Hsecond as [Hsecond | Hsecond]; [| contradiction].
    subst second. cbn in Hsender, Hreceiver.
    exfalso. eapply Hreverse.
    + exact Hselected.
    + exact (@remove_echo_message_in node
        (message_id selected) (message_store state) first Hfirst).
    + exact Hselected_kind.
    + exact Hfirst_kind.
    + now symmetry.
    + now symmetry.
  - cbn [materialize_echo_outbound] in Hfirst.
    destruct Hfirst as [Hfirst | Hfirst]; [| contradiction].
    subst first. cbn in Hsender, Hreceiver.
    exfalso. eapply Hreverse.
    + exact Hselected.
    + exact (@remove_echo_message_in node
        (message_id selected) (message_store state) second Hsecond).
    + exact Hselected_kind.
    + exact Hsecond_kind.
    + exact Hreceiver.
    + exact Hsender.
  - cbn [materialize_echo_outbound] in Hfirst, Hsecond.
    destruct Hfirst as [Hfirst | Hfirst]; [| contradiction].
    destruct Hsecond as [Hsecond | Hsecond]; [| contradiction].
    now subst first; subst second.
Qed.

Lemma apply_parent_reply_preserves_reply_edges_unique
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (parent : node) :
  echo_reply_edges_unique state ->
  echo_parent_replies_from_finished state ->
  process_parent (processes state (message_receiver selected)) = Some parent ->
  process_finished (processes state (message_receiver selected)) = false ->
  echo_reply_edges_unique
    (apply_echo_delivery node_eq state selected new_process
      [mkEchoOutbound EchoReply parent]).
Proof.
  intros Hunique Hparent_replies Hparent Hunfinished.
  unfold echo_reply_edges_unique in *.
  cbn [apply_echo_delivery].
  intros first second Hfirst Hsecond Hfirst_kind Hsecond_kind
    Hsender Hreceiver.
  apply in_app_or in Hfirst. apply in_app_or in Hsecond.
  destruct Hfirst as [Hfirst | Hfirst];
    destruct Hsecond as [Hsecond | Hsecond].
  - eapply Hunique.
    + exact (@remove_echo_message_in node
        (message_id selected) (message_store state) first Hfirst).
    + exact (@remove_echo_message_in node
        (message_id selected) (message_store state) second Hsecond).
    + exact Hfirst_kind.
    + exact Hsecond_kind.
    + exact Hsender.
    + exact Hreceiver.
  - cbn [materialize_echo_outbound] in Hsecond.
    destruct Hsecond as [Hsecond | Hsecond]; [| contradiction].
    subst second. cbn in Hsender, Hreceiver.
    pose proof (Hparent_replies first
      (@remove_echo_message_in node
        (message_id selected) (message_store state) first Hfirst)
      Hfirst_kind) as Hfinished.
    assert (Hedge :
        process_parent (processes state (message_sender first)) =
          Some (message_receiver first)).
    { rewrite Hsender, Hreceiver. exact Hparent. }
    specialize (Hfinished Hedge).
    rewrite Hsender, Hunfinished in Hfinished. discriminate.
  - cbn [materialize_echo_outbound] in Hfirst.
    destruct Hfirst as [Hfirst | Hfirst]; [| contradiction].
    subst first. cbn in Hsender, Hreceiver.
    pose proof (Hparent_replies second
      (@remove_echo_message_in node
        (message_id selected) (message_store state) second Hsecond)
      Hsecond_kind) as Hfinished.
    assert (Hedge :
        process_parent (processes state (message_sender second)) =
          Some (message_receiver second)).
    { rewrite <- Hsender, <- Hreceiver. exact Hparent. }
    specialize (Hfinished Hedge).
    rewrite <- Hsender, Hunfinished in Hfinished. discriminate.
  - cbn [materialize_echo_outbound] in Hfirst, Hsecond.
    destruct Hfirst as [Hfirst | Hfirst]; [| contradiction].
    destruct Hsecond as [Hsecond | Hsecond]; [| contradiction].
    now subst first; subst second.
Qed.

Theorem EchoStep_start_reply_edges_unique
    (state successor : @executable_echo_state node)
    (ordered_neighbors : list node) :
  EchoStep state (EchoStart ordered_neighbors) successor ->
  echo_reply_edges_unique successor.
Proof.
  intro Hstep.
  pose proof (@EchoStep_start_guards node node_eq config
    state successor ordered_neighbors Hstep) as [Hinitial Hpermutation].
  destruct Hinitial as [Hstarted [Hprocesses [Hstore Hnext]]].
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoStart ordered_neighbors) start_rule Hstep eq_refl) as Haction.
  cbn [eval_action start_rule ir_rule_action eval_nodes_expr] in Haction.
  subst successor.
  unfold echo_reply_edges_unique, reply_edges_unique.
  intros first second Hfirst Hsecond Hfirst_kind.
  change (In first
    (message_store state ++
      materialize_echo_outbound (next_message_id state) initiator
        (List.map (mkEchoOutbound EchoRequest) ordered_neighbors))) in Hfirst.
  rewrite Hstore in Hfirst. cbn in Hfirst.
  destruct (@materialized_request_block_fields node
      (next_message_id state) initiator ordered_neighbors first Hfirst)
    as [Hsender [Hkind Hreceiver]].
  congruence.
Qed.

Theorem EchoStep_preserves_reply_edges_unique
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  echo_request_reply_reverse_distinct state ->
  echo_parent_replies_from_finished state ->
  echo_reply_edges_unique state ->
  EchoStep state event successor ->
  echo_reply_edges_unique successor.
Proof.
  intros Hreverse Hparent_replies Hunique Hstep. destruct event.
  - now apply EchoStep_start_reply_edges_unique in Hstep.
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoFirstRequestNonLeaf message ordered_forwards)
      first_echo_nonleaf_rule Hstep eq_refl) as Haction.
    cbn [eval_action first_echo_nonleaf_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_ordered_nodes] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_reply_edges_unique_no_replies.
    + exact Hunique.
    + intros item Hitem Hkind.
      apply in_map_iff in Hitem.
      destruct Hitem as [receiver [Hequal Hreceiver]].
      subst item. discriminate.
  - pose proof (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoFirstRequestLeaf message) Hstep I) as Hselected.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoFirstRequestLeaf message) first_echo_leaf_rule
      (IRGuardKind EchoRequest) Hstep eq_refl ltac:(left; reflexivity))
      as Hkind.
    cbn [guard_holds event_message] in Hkind.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoFirstRequestLeaf message) first_echo_leaf_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action first_echo_leaf_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    eapply apply_request_reply_preserves_reply_edges_unique; eauto.
  - pose proof (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoRepeatedRequest message) Hstep I) as Hselected.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoRepeatedRequest message) repeated_echo_rule
      (IRGuardKind EchoRequest) Hstep eq_refl ltac:(left; reflexivity))
      as Hkind.
    cbn [guard_holds event_message] in Hkind.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoRepeatedRequest message) repeated_echo_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action repeated_echo_rule ir_rule_action
      eval_process_expr eval_node_expr eval_outbound_expr event_message]
      in Haction.
    subst successor.
    eapply apply_request_reply_preserves_reply_edges_unique; eauto.
  - pose proof (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoInitiatorRequest message) Hstep I) as Hselected.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorRequest message) initiator_echo_rule
      (IRGuardKind EchoRequest) Hstep eq_refl ltac:(left; reflexivity))
      as Hkind.
    cbn [guard_holds event_message] in Hkind.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorRequest message) initiator_echo_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_echo_rule ir_rule_action
      eval_process_expr eval_node_expr eval_outbound_expr event_message]
      in Haction.
    subst successor.
    eapply apply_request_reply_preserves_reply_edges_unique; eauto.
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoParticipantReplyMore message parent) participant_ack_more_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action participant_ack_more_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_parent] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_reply_edges_unique_no_replies.
    + exact Hunique.
    + intros item Hitem. contradiction.
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoParticipantReplyFinal message parent)
      participant_ack_final_rule
      (IRGuardParentEqual IRMessageReceiver (IRSomeParent IREventParent))
      Hstep eq_refl ltac:(
        cbn [participant_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hparent.
    cbn [guard_holds eval_node_expr eval_parent_expr event_message
      event_parent] in Hparent.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoParticipantReplyFinal message parent)
      participant_ack_final_rule
      (IRGuardFinished IRMessageReceiver false)
      Hstep eq_refl ltac:(
        cbn [participant_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hunfinished.
    cbn [guard_holds eval_node_expr event_message] in Hunfinished.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoParticipantReplyFinal message parent) participant_ack_final_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action participant_ack_final_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_parent] in Haction.
    subst successor.
    eapply apply_parent_reply_preserves_reply_edges_unique; eauto.
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorReplyMore message) initiator_ack_more_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_ack_more_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_reply_edges_unique_no_replies.
    + exact Hunique.
    + intros item Hitem. contradiction.
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorReplyFinal message) initiator_ack_final_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_ack_final_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_reply_edges_unique_no_replies.
    + exact Hunique.
    + intros item Hitem. contradiction.
Qed.

Lemma initial_executable_echo_state_reply_edges_unique :
  echo_reply_edges_unique initial_executable_echo_state.
Proof.
  unfold echo_reply_edges_unique, reply_edges_unique.
  intros first second Hfirst. contradiction.
Qed.

Theorem echo_reachable_reply_edges_unique
    (state : @executable_echo_state node) :
  echo_reachable node_eq config state ->
  echo_reply_edges_unique state.
Proof.
  intro Hreachable.
  induction Hreachable as [| before event after Hbefore IH Hstep].
  - apply initial_executable_echo_state_reply_edges_unique.
  - eapply EchoStep_preserves_reply_edges_unique.
    + exact (@echo_reachable_request_reply_reverse_distinct node node_eq config
        nodes_nodup initiator_in_nodes adj_symmetric before Hbefore).
    + exact (echo_reachable_parent_replies_from_finished before Hbefore).
    + exact IH.
    + exact Hstep.
Qed.

Lemma in_remove_echo_node_preserved
    (removed candidate : node) (items : list node) :
  candidate <> removed ->
  In candidate items ->
  In candidate (remove_echo_node node_eq removed items).
Proof.
  intros Hdifferent Hin.
  induction items as [| head rest IH]; cbn in *.
  - contradiction.
  - destruct (node_eq removed head) as [Hequal | Hnot_equal].
    + subst head. destruct Hin as [Hequal | Hin].
      * exfalso. apply Hdifferent. now symmetry.
      * exact Hin.
    + destruct Hin as [Hequal | Hin].
      * now left.
      * right. now apply IH.
Qed.

(** Every queued request is backed by the receiver's slot in the sender's
    pending list.  This is the exact executable counterpart of "the sender is
    still waiting for that request to return." *)
Definition echo_queued_requests_pending
    (state : @executable_echo_state node) : Prop :=
  forall message,
    In message (message_store state) ->
    message_kind message = EchoRequest ->
    In (message_receiver message)
      (process_pending (processes state (message_sender message))).

Lemma apply_echo_delivery_preserves_queued_requests_pending
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (outbound : list (@echo_outbound node)) :
  echo_queued_requests_pending state ->
  (forall message,
      In message (message_store state) ->
      message_kind message = EchoRequest ->
      message_sender message = message_receiver selected ->
      In (message_receiver message) (process_pending new_process)) ->
  (forall item,
      In item outbound ->
      outbound_kind item = EchoRequest ->
      In (outbound_receiver item) (process_pending new_process)) ->
  echo_queued_requests_pending
    (apply_echo_delivery node_eq state selected new_process outbound).
Proof.
  intros Hold Hupdated Hnew message Hin Hkind.
  cbn [apply_echo_delivery] in Hin.
  apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - pose proof (@remove_echo_message_in node
      (message_id selected) (message_store state) message Hin) as Hold_message.
    destruct (node_eq (message_receiver selected)
        (message_sender message)) as [Hequal | Hdifferent].
    + rewrite <- Hequal. rewrite apply_echo_delivery_process_self.
      apply Hupdated with (message := message); try assumption.
      now symmetry.
    + rewrite apply_echo_delivery_process_other by exact Hdifferent.
      now eapply Hold.
  - destruct (@materialized_echo_message_complete_fields node
      (next_message_id state) (message_receiver selected)
      outbound message Hin)
      as [item [Hitem [Hsender [Hreceiver Hitem_kind]]]].
    rewrite Hsender. rewrite apply_echo_delivery_process_self.
    rewrite Hreceiver. apply Hnew with (item := item).
    + exact Hitem.
    + now rewrite <- Hitem_kind.
Qed.

Theorem EchoStep_start_queued_requests_pending
    (state successor : @executable_echo_state node)
    (ordered_neighbors : list node) :
  EchoStep state (EchoStart ordered_neighbors) successor ->
  echo_queued_requests_pending successor.
Proof.
  intro Hstep.
  pose proof (@EchoStep_start_guards node node_eq config
    state successor ordered_neighbors Hstep) as [Hinitial Hpermutation].
  destruct Hinitial as [Hstarted [Hprocesses [Hstore Hnext]]].
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoStart ordered_neighbors) start_rule Hstep eq_refl) as Haction.
  cbn [eval_action start_rule ir_rule_action eval_nodes_expr] in Haction.
  subst successor.
  intros message Hin Hkind.
  change (In message
    (message_store state ++
      materialize_echo_outbound (next_message_id state) initiator
        (List.map (mkEchoOutbound EchoRequest) ordered_neighbors))) in Hin.
  rewrite Hstore in Hin. cbn in Hin.
  destruct (@materialized_request_block_fields node
      (next_message_id state) initiator ordered_neighbors message Hin)
    as [Hsender [Hrequest_kind Hreceiver]].
  rewrite Hsender. unfold apply_echo_start. cbn. unfold update_process.
  destruct (node_eq initiator initiator); [exact Hreceiver | contradiction].
Qed.

Theorem EchoStep_preserves_queued_requests_pending
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  echo_parent_forest_well_formed config state ->
  echo_request_reply_reverse_distinct state ->
  echo_queued_requests_pending state ->
  EchoStep state event successor ->
  echo_queued_requests_pending successor.
Proof.
  intros Hforest Hreverse Hrequests Hstep. destruct event.
  - now apply EchoStep_start_queued_requests_pending in Hstep.
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoFirstRequestNonLeaf message ordered_forwards)
      first_echo_nonleaf_rule (IRGuardProcessInitial IRMessageReceiver)
      Hstep eq_refl ltac:(
        cbn [first_echo_nonleaf_rule];
        repeat (first [left; reflexivity | right]))) as Hinitial.
    cbn [guard_holds eval_node_expr event_message] in Hinitial.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoFirstRequestNonLeaf message ordered_forwards)
      first_echo_nonleaf_rule Hstep eq_refl) as Haction.
    cbn [eval_action first_echo_nonleaf_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_ordered_nodes] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_queued_requests_pending.
    + exact Hrequests.
    + intros request Hrequest Hkind Hsender.
      destruct Hforest as [Htargets [Hsenders Hranked]].
      pose proof (Hsenders request Hrequest Hkind) as Hdiscovered.
      unfold echo_discovered in Hdiscovered.
      rewrite Hsender, Hinitial in Hdiscovered. contradiction.
    + intros item Hitem Hkind.
      apply in_map_iff in Hitem.
      destruct Hitem as [receiver [Hequal Hreceiver]].
      subst item. exact Hreceiver.
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoFirstRequestLeaf message) first_echo_leaf_rule
      Hstep eq_refl) as Haction.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoFirstRequestLeaf message) first_echo_leaf_rule
      (IRGuardProcessInitial IRMessageReceiver)
      Hstep eq_refl ltac:(
        cbn [first_echo_leaf_rule];
        repeat (first [left; reflexivity | right]))) as Hinitial.
    cbn [guard_holds eval_node_expr event_message] in Hinitial.
    cbn [eval_action first_echo_leaf_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_queued_requests_pending.
    + exact Hrequests.
    + intros request Hrequest Hkind Hsender.
      destruct Hforest as [Htargets [Hsenders Hranked]].
      pose proof (Hsenders request Hrequest Hkind) as Hdiscovered.
      unfold echo_discovered in Hdiscovered.
      rewrite Hsender, Hinitial in Hdiscovered. contradiction.
    + intros item Hitem Hkind. cbn in Hitem.
      destruct Hitem as [Hitem_equal | Hin];
        [subst item; discriminate | contradiction].
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoRepeatedRequest message) repeated_echo_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action repeated_echo_rule ir_rule_action
      eval_process_expr eval_node_expr eval_outbound_expr event_message]
      in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_queued_requests_pending.
    + exact Hrequests.
    + intros request Hrequest Hkind Hsender.
      pose proof (Hrequests request Hrequest Hkind) as Hin.
      now rewrite Hsender in Hin.
    + intros item Hitem Hkind. cbn in Hitem.
      destruct Hitem as [Hequal | Hin]; [subst item; discriminate | contradiction].
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorRequest message) initiator_echo_rule
      (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [initiator_echo_rule];
        repeat (first [left; reflexivity | right]))) as Hequal.
    cbn [guard_holds eval_node_expr event_message] in Hequal.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorRequest message) initiator_echo_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_echo_rule ir_rule_action
      eval_process_expr eval_node_expr eval_outbound_expr event_message]
      in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_queued_requests_pending.
    + exact Hrequests.
    + intros request Hrequest Hkind Hsender.
      pose proof (Hrequests request Hrequest Hkind) as Hin.
      rewrite Hequal in Hsender. now rewrite Hsender in Hin.
    + intros item Hitem Hkind. cbn in Hitem.
      destruct Hitem as [Hitem_equal | Hin];
        [subst item; discriminate | contradiction].
  - pose proof (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoParticipantReplyMore message parent) Hstep I)
      as Hselected.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoParticipantReplyMore message parent)
      participant_ack_more_rule (IRGuardKind EchoReply)
      Hstep eq_refl ltac:(left; reflexivity)) as Hkind.
    cbn [guard_holds event_message] in Hkind.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoParticipantReplyMore message parent) participant_ack_more_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action participant_ack_more_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_parent] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_queued_requests_pending.
    + exact Hrequests.
    + intros request Hrequest Hrequest_kind Hsender.
      apply in_remove_echo_node_preserved.
      * intro Hequal.
        eapply Hreverse.
        -- exact Hrequest.
        -- exact Hselected.
        -- exact Hrequest_kind.
        -- exact Hkind.
        -- exact Hsender.
        -- exact Hequal.
      * pose proof (Hrequests request Hrequest Hrequest_kind) as Hin.
        now rewrite Hsender in Hin.
    + intros item Hitem. contradiction.
  - pose proof (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoParticipantReplyFinal message parent) Hstep I)
      as Hselected.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoParticipantReplyFinal message parent)
      participant_ack_final_rule (IRGuardKind EchoReply)
      Hstep eq_refl ltac:(left; reflexivity)) as Hkind.
    cbn [guard_holds event_message] in Hkind.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoParticipantReplyFinal message parent)
      participant_ack_final_rule
      (IRGuardNodesEmpty
        (IRNodesRemove IRMessageSender (IRNodesPending IRMessageReceiver)))
      Hstep eq_refl ltac:(
        cbn [participant_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hempty.
    cbn [guard_holds eval_nodes_expr eval_node_expr event_message] in Hempty.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoParticipantReplyFinal message parent) participant_ack_final_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action participant_ack_final_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_parent] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_queued_requests_pending.
    + exact Hrequests.
    + intros request Hrequest Hrequest_kind Hsender.
      exfalso.
      destruct (node_eq (message_receiver request)
          (message_sender message)) as [Hequal | Hdifferent].
      * eapply Hreverse.
        -- exact Hrequest.
        -- exact Hselected.
        -- exact Hrequest_kind.
        -- exact Hkind.
        -- exact Hsender.
        -- exact Hequal.
      * pose proof (Hrequests request Hrequest Hrequest_kind) as Hpending.
        rewrite Hsender in Hpending.
        pose proof (in_remove_echo_node_preserved
          (message_sender message) (message_receiver request)
          (process_pending (processes state (message_receiver message)))
          Hdifferent Hpending) as Hin.
        rewrite Hempty in Hin. contradiction.
    + intros item Hitem Hitem_kind. cbn in Hitem.
      destruct Hitem as [Hequal | Hin]; [subst item; discriminate | contradiction].
  - pose proof (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoInitiatorReplyMore message) Hstep I) as Hselected.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorReplyMore message) initiator_ack_more_rule
      (IRGuardKind EchoReply) Hstep eq_refl ltac:(left; reflexivity))
      as Hkind.
    cbn [guard_holds event_message] in Hkind.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorReplyMore message) initiator_ack_more_rule
      (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [initiator_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hequal_receiver.
    cbn [guard_holds eval_node_expr event_message] in Hequal_receiver.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorReplyMore message) initiator_ack_more_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_ack_more_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_queued_requests_pending.
    + exact Hrequests.
    + intros request Hrequest Hrequest_kind Hsender.
      assert (Hsender_root : message_sender request = initiator).
      { now rewrite <- Hequal_receiver. }
      apply in_remove_echo_node_preserved.
      * intro Hequal.
        eapply Hreverse.
        -- exact Hrequest.
        -- exact Hselected.
        -- exact Hrequest_kind.
        -- exact Hkind.
        -- exact Hsender.
        -- exact Hequal.
      * pose proof (Hrequests request Hrequest Hrequest_kind) as Hin.
        now rewrite Hsender_root in Hin.
    + intros item Hitem. contradiction.
  - pose proof (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoInitiatorReplyFinal message) Hstep I) as Hselected.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorReplyFinal message) initiator_ack_final_rule
      (IRGuardKind EchoReply) Hstep eq_refl ltac:(left; reflexivity))
      as Hkind.
    cbn [guard_holds event_message] in Hkind.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorReplyFinal message) initiator_ack_final_rule
      (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [initiator_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hequal_receiver.
    cbn [guard_holds eval_node_expr event_message] in Hequal_receiver.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorReplyFinal message) initiator_ack_final_rule
      (IRGuardNodesEmpty
        (IRNodesRemove IRMessageSender (IRNodesPending IRInitiatorNode)))
      Hstep eq_refl ltac:(
        cbn [initiator_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hempty.
    cbn [guard_holds eval_nodes_expr eval_node_expr event_message] in Hempty.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorReplyFinal message) initiator_ack_final_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_ack_final_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_queued_requests_pending.
    + exact Hrequests.
    + intros request Hrequest Hrequest_kind Hsender.
      exfalso.
      assert (Hsender_root : message_sender request = initiator).
      { now rewrite <- Hequal_receiver. }
      destruct (node_eq (message_receiver request)
          (message_sender message)) as [Hequal | Hdifferent].
      * eapply Hreverse.
        -- exact Hrequest.
        -- exact Hselected.
        -- exact Hrequest_kind.
        -- exact Hkind.
        -- exact Hsender.
        -- exact Hequal.
      * pose proof (Hrequests request Hrequest Hrequest_kind) as Hpending.
        rewrite Hsender_root in Hpending.
        pose proof (in_remove_echo_node_preserved
          (message_sender message) (message_receiver request)
          (process_pending (processes state initiator))
          Hdifferent Hpending) as Hin.
        rewrite Hempty in Hin. contradiction.
    + intros item Hitem. contradiction.
Qed.

Lemma initial_executable_echo_state_queued_requests_pending :
  echo_queued_requests_pending initial_executable_echo_state.
Proof.
  intros message Hin. contradiction.
Qed.

Theorem echo_reachable_queued_requests_pending
    (state : @executable_echo_state node) :
  echo_reachable node_eq config state ->
  echo_queued_requests_pending state.
Proof.
  intro Hreachable.
  induction Hreachable as [| before event after Hbefore IH Hstep].
  - apply initial_executable_echo_state_queued_requests_pending.
  - eapply EchoStep_preserves_queued_requests_pending.
    + exact (@echo_reachable_parent_forest node node_eq config
        before Hbefore).
    + exact (@echo_reachable_request_reply_reverse_distinct node node_eq config
        nodes_nodup initiator_in_nodes adj_symmetric before Hbefore).
    + exact IH.
    + exact Hstep.
Qed.

(** Every unfinished child remains present in its installed parent's pending
    list.  This is the local propagation edge used later to lift any unfinished
    obligation all the way to the initiator. *)
Definition echo_unfinished_children_pending
    (state : @executable_echo_state node) : Prop :=
  forall child parent,
    In child all_nodes ->
    process_parent (processes state child) = Some parent ->
    process_finished (processes state child) = false ->
    In child (process_pending (processes state parent)).

Lemma apply_echo_delivery_preserves_unfinished_children_pending
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (outbound : list (@echo_outbound node)) :
  echo_unfinished_children_pending state ->
  (forall parent,
      In (message_receiver selected) all_nodes ->
      process_parent new_process = Some parent ->
      process_finished new_process = false ->
      In (message_receiver selected)
        (process_pending
          (update_process node_eq (processes state)
            (message_receiver selected) new_process parent))) ->
  (forall child parent,
      In child all_nodes ->
      child <> message_receiver selected ->
      process_parent (processes state child) = Some parent ->
      process_finished (processes state child) = false ->
      In child
        (process_pending
          (update_process node_eq (processes state)
            (message_receiver selected) new_process parent))) ->
  echo_unfinished_children_pending
    (apply_echo_delivery node_eq state selected new_process outbound).
Proof.
  intros Hold Hnew Hothers child parent Hchild Hparent Hunfinished.
  change (process_parent
    (update_process node_eq (processes state)
      (message_receiver selected) new_process child) = Some parent)
    in Hparent.
  change (process_finished
    (update_process node_eq (processes state)
      (message_receiver selected) new_process child) = false)
    in Hunfinished.
  change (In child
    (process_pending
      (update_process node_eq (processes state)
        (message_receiver selected) new_process parent))).
  destruct (node_eq (message_receiver selected) child)
      as [Hequal | Hdifferent].
  - subst child. rewrite update_process_self in Hparent, Hunfinished.
    now eapply Hnew.
  - rewrite update_process_other in Hparent, Hunfinished
      by exact Hdifferent.
    now eapply Hothers.
Qed.

Lemma parent_ranked_no_self
    (state : @executable_echo_state node)
    (child parent : node) :
  echo_parent_ranked config state ->
  In child all_nodes ->
  process_parent (processes state child) = Some parent ->
  child <> parent.
Proof.
  intros [rank Hrank] Hchild Hparent Hequal.
  subst parent.
  pose proof (Hrank child child Hchild Hparent).
  lia.
Qed.

Theorem EchoStep_start_unfinished_children_pending
    (state successor : @executable_echo_state node)
    (ordered_neighbors : list node) :
  EchoStep state (EchoStart ordered_neighbors) successor ->
  echo_unfinished_children_pending successor.
Proof.
  intro Hstep.
  pose proof (@EchoStep_start_guards node node_eq config
    state successor ordered_neighbors Hstep) as [Hinitial Hpermutation].
  destruct Hinitial as [Hstarted [Hprocesses [Hstore Hnext]]].
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoStart ordered_neighbors) start_rule Hstep eq_refl) as Haction.
  cbn [eval_action start_rule ir_rule_action eval_nodes_expr] in Haction.
  subst successor.
  intros child parent Hchild Hparent Hunfinished.
  change (process_parent
    (update_process node_eq (processes state) initiator
      (mkEchoProcess None ordered_neighbors false) child) = Some parent)
    in Hparent.
  destruct (node_eq initiator child) as [Hequal | Hdifferent].
  - subst child. rewrite update_process_self in Hparent. discriminate.
  - rewrite update_process_other in Hparent by exact Hdifferent.
    rewrite (Hprocesses child Hchild) in Hparent. discriminate.
Qed.

Theorem EchoStep_preserves_unfinished_children_pending
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  echo_parent_forest_well_formed config state ->
  echo_topology_well_formed config state ->
  echo_queued_requests_pending state ->
  echo_parent_replies_from_finished state ->
  echo_unfinished_children_pending state ->
  EchoStep state event successor ->
  echo_unfinished_children_pending successor.
Proof.
  intros Hforest Htopology Hrequests Hparent_replies Hchildren Hstep.
  destruct event.
  - now apply EchoStep_start_unfinished_children_pending in Hstep.
  - pose proof (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoFirstRequestNonLeaf message ordered_forwards)
      Hstep I) as Hselected.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoFirstRequestNonLeaf message ordered_forwards)
      first_echo_nonleaf_rule (IRGuardKind EchoRequest)
      Hstep eq_refl ltac:(left; reflexivity)) as Hkind.
    cbn [guard_holds event_message] in Hkind.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoFirstRequestNonLeaf message ordered_forwards)
      first_echo_nonleaf_rule (IRGuardProcessInitial IRMessageReceiver)
      Hstep eq_refl ltac:(
        cbn [first_echo_nonleaf_rule];
        repeat (first [left; reflexivity | right]))) as Hinitial.
    cbn [guard_holds eval_node_expr event_message] in Hinitial.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoFirstRequestNonLeaf message ordered_forwards)
      first_echo_nonleaf_rule Hstep eq_refl) as Haction.
    cbn [eval_action first_echo_nonleaf_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_ordered_nodes] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_unfinished_children_pending.
    + exact Hchildren.
    + intros parent Hreceiver Hparent Hunfinished.
      cbn in Hparent. injection Hparent as Hparent. subst parent.
      pose proof (Hrequests message Hselected Hkind) as Hpending.
      assert (Hdifferent :
          message_receiver message <> message_sender message).
      { intro Hequal.
        destruct Hforest as [Htargets [Hsenders Hranked]].
        pose proof (Hsenders message Hselected Hkind) as Hdiscovered.
        unfold echo_discovered in Hdiscovered.
        rewrite <- Hequal, Hinitial in Hdiscovered. contradiction. }
      unfold update_process.
      destruct (node_eq (message_receiver message)
          (message_sender message)); [contradiction | exact Hpending].
    + intros child parent Hchild Hdifferent Hparent Hunfinished.
      unfold update_process.
      destruct (node_eq (message_receiver message) parent)
          as [Hequal | Hparent_different].
      * subst parent.
        destruct Hforest as [Htargets [Hsenders Hranked]].
        pose proof (Htargets child (message_receiver message)
          Hchild Hparent) as Hdiscovered.
        unfold echo_discovered in Hdiscovered.
        rewrite Hinitial in Hdiscovered. contradiction.
      * now eapply Hchildren.
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoFirstRequestLeaf message) first_echo_leaf_rule
      (IRGuardProcessInitial IRMessageReceiver)
      Hstep eq_refl ltac:(
        cbn [first_echo_leaf_rule];
        repeat (first [left; reflexivity | right]))) as Hinitial.
    cbn [guard_holds eval_node_expr event_message] in Hinitial.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoFirstRequestLeaf message) first_echo_leaf_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action first_echo_leaf_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_unfinished_children_pending.
    + exact Hchildren.
    + intros parent Hreceiver Hparent Hunfinished. discriminate.
    + intros child parent Hchild Hdifferent Hparent Hunfinished.
      unfold update_process.
      destruct (node_eq (message_receiver message) parent)
          as [Hequal | Hparent_different].
      * subst parent.
        destruct Hforest as [Htargets [Hsenders Hranked]].
        pose proof (Htargets child (message_receiver message)
          Hchild Hparent) as Hdiscovered.
        unfold echo_discovered in Hdiscovered.
        rewrite Hinitial in Hdiscovered. contradiction.
      * now eapply Hchildren.
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoRepeatedRequest message) repeated_echo_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action repeated_echo_rule ir_rule_action
      eval_process_expr eval_node_expr eval_outbound_expr event_message]
      in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_unfinished_children_pending.
    + exact Hchildren.
    + intros parent Hreceiver Hparent Hunfinished.
      pose proof (Hchildren (message_receiver message) parent
        Hreceiver Hparent Hunfinished) as Hpending.
      unfold update_process.
      destruct (node_eq (message_receiver message) parent)
        as [Hequal | Hparent_different]; [subst parent |]; exact Hpending.
    + intros child parent Hchild Hdifferent Hparent Hunfinished.
      pose proof (Hchildren child parent Hchild Hparent Hunfinished)
        as Hpending.
      unfold update_process.
      destruct (node_eq (message_receiver message) parent)
        as [Hequal | Hparent_different]; [subst parent |]; exact Hpending.
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorRequest message) initiator_echo_rule
      (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [initiator_echo_rule];
        repeat (first [left; reflexivity | right]))) as Hequal_receiver.
    cbn [guard_holds eval_node_expr event_message] in Hequal_receiver.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorRequest message) initiator_echo_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_echo_rule ir_rule_action
      eval_process_expr eval_node_expr eval_outbound_expr event_message]
      in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_unfinished_children_pending.
    + exact Hchildren.
    + intros parent Hreceiver Hparent Hunfinished.
      rewrite Hequal_receiver in Hreceiver |- *.
      pose proof (Hchildren initiator parent initiator_in_nodes
        Hparent Hunfinished) as Hpending.
      unfold update_process.
      destruct (node_eq initiator parent)
        as [Hequal | Hparent_different]; [subst parent |]; exact Hpending.
    + intros child parent Hchild Hdifferent Hparent Hunfinished.
      pose proof (Hchildren child parent Hchild Hparent Hunfinished)
        as Hpending.
      rewrite Hequal_receiver.
      unfold update_process.
      destruct (node_eq initiator parent)
        as [Hequal | Hparent_different]; [subst parent |]; exact Hpending.
  - pose proof (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoParticipantReplyMore message parent) Hstep I)
      as Hselected.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoParticipantReplyMore message parent)
      participant_ack_more_rule (IRGuardKind EchoReply)
      Hstep eq_refl ltac:(left; reflexivity)) as Hkind.
    cbn [guard_holds event_message] in Hkind.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoParticipantReplyMore message parent)
      participant_ack_more_rule
      (IRGuardParentEqual IRMessageReceiver (IRSomeParent IREventParent))
      Hstep eq_refl ltac:(
        cbn [participant_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hparent.
    cbn [guard_holds eval_node_expr eval_parent_expr event_message
      event_parent] in Hparent.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoParticipantReplyMore message parent)
      participant_ack_more_rule (IRGuardFinished IRMessageReceiver false)
      Hstep eq_refl ltac:(
        cbn [participant_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hunfinished.
    cbn [guard_holds eval_node_expr event_message] in Hunfinished.
    destruct Htopology as [Hparents Hqueued].
    destruct (Hqueued message Hselected)
      as [Hsender_node [Hreceiver_node Hedge]].
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoParticipantReplyMore message parent) participant_ack_more_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action participant_ack_more_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_parent] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_unfinished_children_pending.
    + exact Hchildren.
    + intros parent' Hreceiver Hparent' Hunfinished'.
      cbn in Hparent'. injection Hparent' as Hparent'. subst parent'.
      pose proof (Hchildren (message_receiver message) parent
        Hreceiver_node Hparent Hunfinished) as Hpending.
      assert (Hdifferent : message_receiver message <> parent).
      { destruct Hforest as [Htargets [Hsenders Hranked]].
        exact (parent_ranked_no_self state (message_receiver message) parent
          Hranked Hreceiver_node Hparent). }
      unfold update_process.
      destruct (node_eq (message_receiver message) parent);
        [contradiction | exact Hpending].
    + intros child parent' Hchild Hdifferent Hchild_parent Hchild_unfinished.
      pose proof (Hchildren child parent' Hchild
        Hchild_parent Hchild_unfinished) as Hpending.
      unfold update_process.
      destruct (node_eq (message_receiver message) parent')
          as [Hequal | Hparent_different].
      * subst parent'. apply in_remove_echo_node_preserved.
        -- intro Hequal_child. subst child.
           pose proof (Hparent_replies message Hselected Hkind
             Hchild_parent) as Hfinished.
           rewrite Hchild_unfinished in Hfinished. discriminate.
        -- exact Hpending.
      * exact Hpending.
  - pose proof (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoParticipantReplyFinal message parent) Hstep I)
      as Hselected.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoParticipantReplyFinal message parent)
      participant_ack_final_rule (IRGuardKind EchoReply)
      Hstep eq_refl ltac:(left; reflexivity)) as Hkind.
    cbn [guard_holds event_message] in Hkind.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoParticipantReplyFinal message parent)
      participant_ack_final_rule
      (IRGuardNodesEmpty
        (IRNodesRemove IRMessageSender (IRNodesPending IRMessageReceiver)))
      Hstep eq_refl ltac:(
        cbn [participant_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hempty.
    cbn [guard_holds eval_nodes_expr eval_node_expr event_message] in Hempty.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoParticipantReplyFinal message parent) participant_ack_final_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action participant_ack_final_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_parent] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_unfinished_children_pending.
    + exact Hchildren.
    + intros parent' Hreceiver Hparent' Hunfinished'. discriminate.
    + intros child parent' Hchild Hdifferent Hchild_parent Hchild_unfinished.
      pose proof (Hchildren child parent' Hchild
        Hchild_parent Hchild_unfinished) as Hpending.
      unfold update_process.
      destruct (node_eq (message_receiver message) parent')
          as [Hequal | Hparent_different].
      * subst parent'. exfalso.
        destruct (node_eq child (message_sender message))
            as [Hequal_child | Hchild_different].
        -- subst child.
           pose proof (Hparent_replies message Hselected Hkind
             Hchild_parent) as Hfinished.
           rewrite Hchild_unfinished in Hfinished. discriminate.
        -- pose proof (in_remove_echo_node_preserved
             (message_sender message) child
             (process_pending (processes state (message_receiver message)))
             Hchild_different Hpending) as Hin.
           rewrite Hempty in Hin. contradiction.
      * exact Hpending.
  - pose proof (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoInitiatorReplyMore message) Hstep I) as Hselected.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorReplyMore message) initiator_ack_more_rule
      (IRGuardKind EchoReply) Hstep eq_refl ltac:(left; reflexivity))
      as Hkind.
    cbn [guard_holds event_message] in Hkind.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorReplyMore message) initiator_ack_more_rule
      (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [initiator_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hequal_receiver.
    cbn [guard_holds eval_node_expr event_message] in Hequal_receiver.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorReplyMore message) initiator_ack_more_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_ack_more_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_unfinished_children_pending.
    + exact Hchildren.
    + intros parent Hreceiver Hparent Hunfinished. discriminate.
    + intros child parent Hchild Hdifferent Hchild_parent Hchild_unfinished.
      pose proof (Hchildren child parent Hchild
        Hchild_parent Hchild_unfinished) as Hpending.
      rewrite Hequal_receiver.
      unfold update_process.
      destruct (node_eq initiator parent) as [Hequal | Hparent_different].
      * subst parent. apply in_remove_echo_node_preserved.
        -- intro Hequal_child. subst child.
           assert (Hchild_parent_receiver :
             process_parent (processes state (message_sender message)) =
               Some (message_receiver message)).
           { now rewrite Hequal_receiver. }
           pose proof (Hparent_replies message Hselected Hkind
             Hchild_parent_receiver) as Hfinished.
           rewrite Hchild_unfinished in Hfinished. discriminate.
        -- exact Hpending.
      * exact Hpending.
  - pose proof (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoInitiatorReplyFinal message) Hstep I) as Hselected.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorReplyFinal message) initiator_ack_final_rule
      (IRGuardKind EchoReply) Hstep eq_refl ltac:(left; reflexivity))
      as Hkind.
    cbn [guard_holds event_message] in Hkind.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorReplyFinal message) initiator_ack_final_rule
      (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [initiator_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hequal_receiver.
    cbn [guard_holds eval_node_expr event_message] in Hequal_receiver.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorReplyFinal message) initiator_ack_final_rule
      (IRGuardNodesEmpty
        (IRNodesRemove IRMessageSender (IRNodesPending IRInitiatorNode)))
      Hstep eq_refl ltac:(
        cbn [initiator_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hempty.
    cbn [guard_holds eval_nodes_expr eval_node_expr event_message] in Hempty.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorReplyFinal message) initiator_ack_final_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_ack_final_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_unfinished_children_pending.
    + exact Hchildren.
    + intros parent Hreceiver Hparent Hunfinished. discriminate.
    + intros child parent Hchild Hdifferent Hchild_parent Hchild_unfinished.
      pose proof (Hchildren child parent Hchild
        Hchild_parent Hchild_unfinished) as Hpending.
      rewrite Hequal_receiver.
      unfold update_process.
      destruct (node_eq initiator parent) as [Hequal | Hparent_different].
      * subst parent. exfalso.
        destruct (node_eq child (message_sender message))
            as [Hequal_child | Hchild_different].
        -- subst child.
           assert (Hchild_parent_receiver :
             process_parent (processes state (message_sender message)) =
               Some (message_receiver message)).
           { now rewrite Hequal_receiver. }
           pose proof (Hparent_replies message Hselected Hkind
             Hchild_parent_receiver) as Hfinished.
           rewrite Hchild_unfinished in Hfinished. discriminate.
        -- pose proof (in_remove_echo_node_preserved
             (message_sender message) child
             (process_pending (processes state initiator))
             Hchild_different Hpending) as Hin.
           rewrite Hempty in Hin. contradiction.
      * exact Hpending.
Qed.

Lemma initial_executable_echo_state_unfinished_children_pending :
  echo_unfinished_children_pending initial_executable_echo_state.
Proof.
  intros child parent Hchild Hparent.
  cbn in Hparent. discriminate.
Qed.

Theorem echo_reachable_unfinished_children_pending
    (state : @executable_echo_state node) :
  echo_reachable node_eq config state ->
  echo_unfinished_children_pending state.
Proof.
  intro Hreachable.
  induction Hreachable as [| before event after Hbefore IH Hstep].
  - apply initial_executable_echo_state_unfinished_children_pending.
  - eapply EchoStep_preserves_unfinished_children_pending.
    + exact (@echo_reachable_parent_forest node node_eq config
        before Hbefore).
    + exact (@echo_reachable_topology node node_eq config
        initiator_in_nodes adj_symmetric before Hbefore).
    + exact (echo_reachable_queued_requests_pending before Hbefore).
    + exact (echo_reachable_parent_replies_from_finished before Hbefore).
    + exact IH.
    + exact Hstep.
Qed.

(** Every queued reply is backed by the sender's slot in the receiver's
    pending list.  This is the reply half of the direct queue/pending
    correspondence. *)
Definition echo_queued_replies_pending
    (state : @executable_echo_state node) : Prop :=
  forall message,
    In message (message_store state) ->
    message_kind message = EchoReply ->
    In (message_sender message)
      (process_pending (processes state (message_receiver message))).

Lemma apply_echo_delivery_preserves_queued_replies_pending
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (outbound : list (@echo_outbound node)) :
  echo_queued_replies_pending state ->
  (forall message,
      In message
        (remove_echo_message (message_id selected) (message_store state)) ->
      message_kind message = EchoReply ->
      message_receiver message = message_receiver selected ->
      In (message_sender message) (process_pending new_process)) ->
  (forall item,
      In item outbound ->
      outbound_kind item = EchoReply ->
      In (message_receiver selected)
        (process_pending
          (update_process node_eq (processes state)
            (message_receiver selected) new_process
            (outbound_receiver item)))) ->
  echo_queued_replies_pending
    (apply_echo_delivery node_eq state selected new_process outbound).
Proof.
  intros Hold Hupdated Hnew message Hin Hkind.
  cbn [apply_echo_delivery] in Hin.
  apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - destruct (node_eq (message_receiver selected)
        (message_receiver message)) as [Hequal | Hdifferent].
    + rewrite <- Hequal. rewrite apply_echo_delivery_process_self.
      eapply Hupdated; try exact Hin; try exact Hkind. now symmetry.
    + rewrite apply_echo_delivery_process_other by exact Hdifferent.
      eapply Hold.
      * exact (@remove_echo_message_in node
          (message_id selected) (message_store state) message Hin).
      * exact Hkind.
  - destruct (@materialized_echo_message_complete_fields node
      (next_message_id state) (message_receiver selected)
      outbound message Hin)
      as [item [Hitem [Hsender [Hreceiver Hitem_kind]]]].
    rewrite Hsender, Hreceiver.
    change (In (message_receiver selected)
      (process_pending
        (update_process node_eq (processes state)
          (message_receiver selected) new_process
          (outbound_receiver item)))).
    eapply Hnew.
    + exact Hitem.
    + now rewrite <- Hitem_kind.
Qed.

Theorem EchoStep_start_queued_replies_pending
    (state successor : @executable_echo_state node)
    (ordered_neighbors : list node) :
  EchoStep state (EchoStart ordered_neighbors) successor ->
  echo_queued_replies_pending successor.
Proof.
  intro Hstep.
  pose proof (@EchoStep_start_guards node node_eq config
    state successor ordered_neighbors Hstep) as [Hinitial Hpermutation].
  destruct Hinitial as [Hstarted [Hprocesses [Hstore Hnext]]].
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoStart ordered_neighbors) start_rule Hstep eq_refl) as Haction.
  cbn [eval_action start_rule ir_rule_action eval_nodes_expr] in Haction.
  subst successor.
  intros message Hin Hkind.
  change (In message
    (message_store state ++
      materialize_echo_outbound (next_message_id state) initiator
        (List.map (mkEchoOutbound EchoRequest) ordered_neighbors))) in Hin.
  rewrite Hstore in Hin. cbn in Hin.
  destruct (@materialized_request_block_fields node
      (next_message_id state) initiator ordered_neighbors message Hin)
    as [Hsender [Hrequest_kind Hreceiver]].
  congruence.
Qed.

Lemma remaining_reply_sender_pending_after_selected_removal
    (state : @executable_echo_state node)
    (selected : @echo_message node) :
  echo_message_ids_well_formed state ->
  echo_reply_edges_unique state ->
  echo_queued_replies_pending state ->
  In selected (message_store state) ->
  message_kind selected = EchoReply ->
  forall message,
    In message
      (remove_echo_message (message_id selected) (message_store state)) ->
    message_kind message = EchoReply ->
    message_receiver message = message_receiver selected ->
    In (message_sender message)
      (remove_echo_node node_eq (message_sender selected)
        (process_pending
          (processes state (message_receiver selected)))).
Proof.
  intros [Hbelow Hids] Hunique Hreplies Hselected Hselected_kind
    message Hremaining Hkind Hreceiver.
  pose proof (@remove_echo_message_in node
    (message_id selected) (message_store state) message Hremaining)
    as Hmessage.
  pose proof (Hreplies message Hmessage Hkind) as Hpending.
  rewrite Hreceiver in Hpending.
  destruct (node_eq (message_sender message) (message_sender selected))
      as [Hsender | Hdifferent].
  - assert (Hequal : message = selected).
    { eapply Hunique.
      - exact Hmessage.
      - exact Hselected.
      - exact Hkind.
      - exact Hselected_kind.
      - exact Hsender.
      - exact Hreceiver. }
    subst message.
    exfalso. exact (@remove_echo_message_selected_not_in node
      selected (message_store state) Hids Hselected Hremaining).
  - exact (in_remove_echo_node_preserved
      (message_sender selected) (message_sender message)
      (process_pending (processes state (message_receiver selected)))
      Hdifferent Hpending).
Qed.

Theorem EchoStep_preserves_queued_replies_pending
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  echo_parent_forest_well_formed config state ->
  echo_topology_well_formed config state ->
  echo_message_ids_well_formed state ->
  echo_reply_receivers_discovered state ->
  echo_reply_edges_unique state ->
  echo_queued_requests_pending state ->
  echo_unfinished_children_pending state ->
  echo_queued_replies_pending state ->
  EchoStep state event successor ->
  echo_queued_replies_pending successor.
Proof.
  intros Hforest Htopology Hids Hreply_receivers Hunique Hrequests
    Hchildren Hreplies Hstep.
  destruct event.
  - now apply EchoStep_start_queued_replies_pending in Hstep.
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoFirstRequestNonLeaf message ordered_forwards)
      first_echo_nonleaf_rule (IRGuardProcessInitial IRMessageReceiver)
      Hstep eq_refl ltac:(
        cbn [first_echo_nonleaf_rule];
        repeat (first [left; reflexivity | right]))) as Hinitial.
    cbn [guard_holds eval_node_expr event_message] in Hinitial.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoFirstRequestNonLeaf message ordered_forwards)
      first_echo_nonleaf_rule Hstep eq_refl) as Haction.
    cbn [eval_action first_echo_nonleaf_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_ordered_nodes] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_queued_replies_pending.
    + exact Hreplies.
    + intros reply Hremaining Hkind Hreceiver.
      pose proof (@remove_echo_message_in node
        (message_id message) (message_store state) reply Hremaining)
        as Hreply.
      pose proof (Hreply_receivers reply Hreply Hkind) as Hdiscovered.
      unfold echo_discovered in Hdiscovered.
      rewrite Hreceiver, Hinitial in Hdiscovered. contradiction.
    + intros item Hitem Hkind.
      apply in_map_iff in Hitem.
      destruct Hitem as [receiver [Hequal Hreceiver]].
      subst item. discriminate.
  - pose proof (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoFirstRequestLeaf message) Hstep I) as Hselected.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoFirstRequestLeaf message) first_echo_leaf_rule
      (IRGuardKind EchoRequest) Hstep eq_refl ltac:(left; reflexivity))
      as Hkind.
    cbn [guard_holds event_message] in Hkind.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoFirstRequestLeaf message) first_echo_leaf_rule
      (IRGuardProcessInitial IRMessageReceiver)
      Hstep eq_refl ltac:(
        cbn [first_echo_leaf_rule];
        repeat (first [left; reflexivity | right]))) as Hinitial.
    cbn [guard_holds eval_node_expr event_message] in Hinitial.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoFirstRequestLeaf message) first_echo_leaf_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action first_echo_leaf_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_queued_replies_pending.
    + exact Hreplies.
    + intros reply Hremaining Hreply_kind Hreceiver.
      pose proof (@remove_echo_message_in node
        (message_id message) (message_store state) reply Hremaining)
        as Hreply.
      pose proof (Hreply_receivers reply Hreply Hreply_kind) as Hdiscovered.
      unfold echo_discovered in Hdiscovered.
      rewrite Hreceiver, Hinitial in Hdiscovered. contradiction.
    + intros item Hitem Hitem_kind.
      cbn in Hitem. destruct Hitem as [Hequal | Hin]; [subst item | contradiction].
      pose proof (Hrequests message Hselected Hkind) as Hpending.
      assert (Hdifferent :
          message_receiver message <> message_sender message).
      { intro Hequal_nodes.
        destruct Hforest as [Htargets [Hsenders Hranked]].
        pose proof (Hsenders message Hselected Hkind) as Hdiscovered.
        unfold echo_discovered in Hdiscovered.
        rewrite <- Hequal_nodes, Hinitial in Hdiscovered. contradiction. }
      cbn. unfold update_process.
      destruct (node_eq (message_receiver message)
          (message_sender message)); [contradiction | exact Hpending].
  - pose proof (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoRepeatedRequest message) Hstep I) as Hselected.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoRepeatedRequest message) repeated_echo_rule
      (IRGuardKind EchoRequest) Hstep eq_refl ltac:(left; reflexivity))
      as Hkind.
    cbn [guard_holds event_message] in Hkind.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoRepeatedRequest message) repeated_echo_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action repeated_echo_rule ir_rule_action
      eval_process_expr eval_node_expr eval_outbound_expr event_message]
      in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_queued_replies_pending.
    + exact Hreplies.
    + intros reply Hremaining Hreply_kind Hreceiver.
      pose proof (@remove_echo_message_in node
        (message_id message) (message_store state) reply Hremaining)
        as Hreply.
      pose proof (Hreplies reply Hreply Hreply_kind) as Hpending.
      now rewrite Hreceiver in Hpending.
    + intros item Hitem Hitem_kind.
      cbn in Hitem. destruct Hitem as [Hequal | Hin]; [subst item | contradiction].
      pose proof (Hrequests message Hselected Hkind) as Hpending.
      cbn. unfold update_process.
      destruct (node_eq (message_receiver message)
          (message_sender message)) as [Hequal | Hdifferent].
      * rewrite <- Hequal in Hpending. exact Hpending.
      * exact Hpending.
  - pose proof (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoInitiatorRequest message) Hstep I) as Hselected.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorRequest message) initiator_echo_rule
      (IRGuardKind EchoRequest) Hstep eq_refl ltac:(left; reflexivity))
      as Hkind.
    cbn [guard_holds event_message] in Hkind.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorRequest message) initiator_echo_rule
      (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [initiator_echo_rule];
        repeat (first [left; reflexivity | right]))) as Hequal_receiver.
    cbn [guard_holds eval_node_expr event_message] in Hequal_receiver.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorRequest message) initiator_echo_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_echo_rule ir_rule_action
      eval_process_expr eval_node_expr eval_outbound_expr event_message]
      in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_queued_replies_pending.
    + exact Hreplies.
    + intros reply Hremaining Hreply_kind Hreceiver.
      pose proof (@remove_echo_message_in node
        (message_id message) (message_store state) reply Hremaining)
        as Hreply.
      pose proof (Hreplies reply Hreply Hreply_kind) as Hpending.
      rewrite Hreceiver, Hequal_receiver in Hpending. exact Hpending.
    + intros item Hitem Hitem_kind.
      cbn in Hitem. destruct Hitem as [Hequal | Hin]; [subst item | contradiction].
      pose proof (Hrequests message Hselected Hkind) as Hpending.
      rewrite Hequal_receiver in Hpending |- *.
      cbn. unfold update_process.
      destruct (node_eq initiator (message_sender message))
        as [Hequal | Hdifferent].
      * rewrite <- Hequal in Hpending. exact Hpending.
      * exact Hpending.
  - pose proof (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoParticipantReplyMore message parent) Hstep I)
      as Hselected.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoParticipantReplyMore message parent)
      participant_ack_more_rule (IRGuardKind EchoReply)
      Hstep eq_refl ltac:(left; reflexivity)) as Hkind.
    cbn [guard_holds event_message] in Hkind.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoParticipantReplyMore message parent) participant_ack_more_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action participant_ack_more_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_parent] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_queued_replies_pending.
    + exact Hreplies.
    + intros reply Hremaining Hreply_kind Hreceiver.
      exact (remaining_reply_sender_pending_after_selected_removal
        state message Hids Hunique Hreplies Hselected Hkind
        reply Hremaining Hreply_kind Hreceiver).
    + intros item Hitem. contradiction.
  - pose proof (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoParticipantReplyFinal message parent) Hstep I)
      as Hselected.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoParticipantReplyFinal message parent)
      participant_ack_final_rule (IRGuardKind EchoReply)
      Hstep eq_refl ltac:(left; reflexivity)) as Hkind.
    cbn [guard_holds event_message] in Hkind.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoParticipantReplyFinal message parent)
      participant_ack_final_rule
      (IRGuardParentEqual IRMessageReceiver (IRSomeParent IREventParent))
      Hstep eq_refl ltac:(
        cbn [participant_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hparent.
    cbn [guard_holds eval_node_expr eval_parent_expr event_message
      event_parent] in Hparent.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoParticipantReplyFinal message parent)
      participant_ack_final_rule (IRGuardFinished IRMessageReceiver false)
      Hstep eq_refl ltac:(
        cbn [participant_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hunfinished.
    cbn [guard_holds eval_node_expr event_message] in Hunfinished.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoParticipantReplyFinal message parent)
      participant_ack_final_rule
      (IRGuardNodesEmpty
        (IRNodesRemove IRMessageSender (IRNodesPending IRMessageReceiver)))
      Hstep eq_refl ltac:(
        cbn [participant_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hempty.
    cbn [guard_holds eval_nodes_expr eval_node_expr event_message] in Hempty.
    destruct Htopology as [Hparents Hqueued].
    destruct (Hqueued message Hselected)
      as [Hsender_node [Hreceiver_node Hedge]].
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoParticipantReplyFinal message parent) participant_ack_final_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action participant_ack_final_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_parent] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_queued_replies_pending.
    + exact Hreplies.
    + intros reply Hremaining Hreply_kind Hreceiver.
      pose proof (remaining_reply_sender_pending_after_selected_removal
        state message Hids Hunique Hreplies Hselected Hkind
        reply Hremaining Hreply_kind Hreceiver) as Hpending.
      rewrite Hempty in Hpending. contradiction.
    + intros item Hitem Hitem_kind.
      cbn in Hitem. destruct Hitem as [Hequal | Hin]; [subst item | contradiction].
      pose proof (Hchildren (message_receiver message) parent
        Hreceiver_node Hparent Hunfinished) as Hpending.
      assert (Hdifferent : message_receiver message <> parent).
      { destruct Hforest as [Htargets [Hsenders Hranked]].
        exact (parent_ranked_no_self state (message_receiver message) parent
          Hranked Hreceiver_node Hparent). }
      cbn. unfold update_process.
      destruct (node_eq (message_receiver message) parent);
        [contradiction | exact Hpending].
  - pose proof (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoInitiatorReplyMore message) Hstep I) as Hselected.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorReplyMore message) initiator_ack_more_rule
      (IRGuardKind EchoReply) Hstep eq_refl ltac:(left; reflexivity))
      as Hkind.
    cbn [guard_holds event_message] in Hkind.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorReplyMore message) initiator_ack_more_rule
      (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [initiator_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hequal_receiver.
    cbn [guard_holds eval_node_expr event_message] in Hequal_receiver.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorReplyMore message) initiator_ack_more_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_ack_more_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_queued_replies_pending.
    + exact Hreplies.
    + intros reply Hremaining Hreply_kind Hreceiver.
      pose proof (remaining_reply_sender_pending_after_selected_removal
        state message Hids Hunique Hreplies Hselected Hkind
        reply Hremaining Hreply_kind Hreceiver) as Hpending.
      now rewrite Hequal_receiver in Hpending.
    + intros item Hitem. contradiction.
  - pose proof (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoInitiatorReplyFinal message) Hstep I) as Hselected.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorReplyFinal message) initiator_ack_final_rule
      (IRGuardKind EchoReply) Hstep eq_refl ltac:(left; reflexivity))
      as Hkind.
    cbn [guard_holds event_message] in Hkind.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorReplyFinal message) initiator_ack_final_rule
      (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [initiator_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hequal_receiver.
    cbn [guard_holds eval_node_expr event_message] in Hequal_receiver.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorReplyFinal message) initiator_ack_final_rule
      (IRGuardNodesEmpty
        (IRNodesRemove IRMessageSender (IRNodesPending IRInitiatorNode)))
      Hstep eq_refl ltac:(
        cbn [initiator_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hempty.
    cbn [guard_holds eval_nodes_expr eval_node_expr event_message] in Hempty.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorReplyFinal message) initiator_ack_final_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_ack_final_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_queued_replies_pending.
    + exact Hreplies.
    + intros reply Hremaining Hreply_kind Hreceiver.
      pose proof (remaining_reply_sender_pending_after_selected_removal
        state message Hids Hunique Hreplies Hselected Hkind
        reply Hremaining Hreply_kind Hreceiver) as Hpending.
      rewrite Hequal_receiver, Hempty in Hpending. contradiction.
    + intros item Hitem. contradiction.
Qed.

Lemma initial_executable_echo_state_queued_replies_pending :
  echo_queued_replies_pending initial_executable_echo_state.
Proof.
  intros message Hin. contradiction.
Qed.

Theorem echo_reachable_queued_replies_pending
    (state : @executable_echo_state node) :
  echo_reachable node_eq config state ->
  echo_queued_replies_pending state.
Proof.
  intro Hreachable.
  induction Hreachable as [| before event after Hbefore IH Hstep].
  - apply initial_executable_echo_state_queued_replies_pending.
  - eapply EchoStep_preserves_queued_replies_pending.
    + exact (@echo_reachable_parent_forest node node_eq config
        before Hbefore).
    + exact (@echo_reachable_topology node node_eq config
        initiator_in_nodes adj_symmetric before Hbefore).
    + exact (@echo_reachable_message_ids_well_formed node node_eq config
        before Hbefore).
    + exact (@echo_reachable_reply_receivers_discovered node node_eq config
        initiator_in_nodes adj_symmetric before Hbefore).
    + exact (echo_reachable_reply_edges_unique before Hbefore).
    + exact (echo_reachable_queued_requests_pending before Hbefore).
    + exact (echo_reachable_unfinished_children_pending before Hbefore).
    + exact IH.
    + exact Hstep.
Qed.

(** A nonempty pending list cannot terminate below the root.  If its owner is
    a participant, discovery supplies a parent, the local child invariant
    moves the obligation to that parent, and the ghost rank strictly
    decreases.  Natural-number induction therefore reaches the initiator. *)
Theorem pending_obligation_reaches_initiator
    (state : @executable_echo_state node) :
  echo_parent_ranked config state ->
  echo_parent_edges_valid config state ->
  echo_discovered_participants_parented config state ->
  echo_completion_well_formed config state ->
  echo_unfinished_children_pending state ->
  forall owner item,
    In owner all_nodes ->
    In item (process_pending (processes state owner)) ->
    exists root_item,
      In root_item (process_pending (processes state initiator)).
Proof.
  intros [rank Hrank] Hedges Hparented Hcompletion Hchildren.
  assert (Hprop : forall fuel owner item,
      rank owner < fuel ->
      In owner all_nodes ->
      In item (process_pending (processes state owner)) ->
      exists root_item,
        In root_item (process_pending (processes state initiator))).
  { induction fuel as [|fuel IH].
    - intros owner item Hbound. lia.
    - intros owner item Hbound Howner Hitem.
      destruct (node_eq owner initiator) as [Hequal | Hdifferent].
      + subst owner. now exists item.
      + assert (Hdiscovered : echo_discovered state owner).
        { unfold echo_discovered. intro Hequal.
          rewrite Hequal in Hitem. cbn in Hitem. contradiction. }
        destruct (Hparented owner Howner Hdifferent Hdiscovered)
          as [parent Hparent].
        destruct (Hedges owner parent Howner Hparent)
          as [Hparent_node Hedge].
        assert (Hunfinished :
            process_finished (processes state owner) = false).
        { destruct (process_finished (processes state owner))
              eqn:Hfinished; [| reflexivity].
          pose proof (Hcompletion owner Howner Hfinished) as Hempty.
          rewrite Hempty in Hitem. contradiction. }
        pose proof (Hchildren owner parent Howner Hparent Hunfinished)
          as Hparent_pending.
        apply (IH parent owner).
        * pose proof (Hrank owner parent Howner Hparent). lia.
        * exact Hparent_node.
        * exact Hparent_pending. }
  intros owner item Howner Hitem.
  apply (Hprop (S (rank owner)) owner item); try assumption. lia.
Qed.

Theorem echo_reachable_pending_reaches_initiator
    (state : @executable_echo_state node)
    (owner item : node) :
  echo_reachable node_eq config state ->
  In owner all_nodes ->
  In item (process_pending (processes state owner)) ->
  exists root_item,
    In root_item (process_pending (processes state initiator)).
Proof.
  intros Hreachable Howner Hitem.
  destruct (@echo_reachable_parent_forest node node_eq config
      state Hreachable) as [Htargets [Hsenders Hranked]].
  destruct (@echo_reachable_topology node node_eq config
      initiator_in_nodes adj_symmetric state Hreachable)
    as [Hparent_edges Hqueued_edges].
  eapply pending_obligation_reaches_initiator.
  - exact Hranked.
  - exact Hparent_edges.
  - exact (@echo_reachable_discovered_participants_parented
      node node_eq config state Hreachable).
  - exact (@echo_reachable_completion node node_eq config state Hreachable).
  - exact (echo_reachable_unfinished_children_pending state Hreachable).
  - exact Howner.
  - exact Hitem.
Qed.

(** Queue/pending correspondence plus parent-chain propagation means that any
    queued protocol message witnesses a nonempty initiator pending list. *)
Theorem echo_reachable_queued_message_initiator_pending
    (state : @executable_echo_state node)
    (message : @echo_message node) :
  echo_reachable node_eq config state ->
  In message (message_store state) ->
  exists root_item,
    In root_item (process_pending (processes state initiator)).
Proof.
  intros Hreachable Hmessage.
  destruct (@echo_reachable_topology node node_eq config
      initiator_in_nodes adj_symmetric state Hreachable)
    as [Hparent_edges Hqueued_edges].
  destruct (Hqueued_edges message Hmessage)
    as [Hsender_node [Hreceiver_node Hedge]].
  destruct (message_kind message) eqn:Hkind.
  - pose proof (echo_reachable_queued_requests_pending state Hreachable
      message Hmessage Hkind) as Hpending.
    eapply echo_reachable_pending_reaches_initiator.
    + exact Hreachable.
    + exact Hsender_node.
    + exact Hpending.
  - pose proof (echo_reachable_queued_replies_pending state Hreachable
      message Hmessage Hkind) as Hpending.
    eapply echo_reachable_pending_reaches_initiator.
    + exact Hreachable.
    + exact Hreceiver_node.
    + exact Hpending.
Qed.

End EchoExecutableObligations.

Arguments echo_reply_noninitiator_senders_discovered {node} _ _.
Arguments echo_parent_replies_from_finished {node} _.
Arguments reply_edges_unique {node} _.
Arguments echo_reply_edges_unique {node} _.
Arguments echo_queued_requests_pending {node} _.
Arguments echo_unfinished_children_pending {node} _ _.
Arguments echo_queued_replies_pending {node} _.
