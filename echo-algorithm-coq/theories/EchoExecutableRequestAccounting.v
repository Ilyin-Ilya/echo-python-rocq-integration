(** * Direct request/reply accounting for executable Echo

    This module begins the causal accounting needed for the final
    post-decision queue theorem.  It proves directed request uniqueness,
    consumption of the parent-installing request, reply-receiver discovery,
    and exclusion of a queued request together with its reverse reply.  The
    proofs are directly over the nine canonical [EchoStep] events. *)

From Stdlib Require Import List Bool Arith Sorting.Permutation.
Import ListNotations.
Require Import EchoAlgorithm EchoExecutableTypes EchoTransitionIR
  EchoExecutableReachability EchoExecutableTopology EchoExecutablePending
  EchoExecutableForest.

Section EchoExecutableRequestAccounting.

Variable node : Type.
Variable node_eq : forall (n m : node), {n = m} + {n <> m}.
Variable config : @echo_config node.

Local Notation initiator := (config_initiator config).
Local Notation all_nodes := (config_nodes config).
Local Notation adj := (config_adjacent config).
Local Notation EchoStep := (@EchoStep node node_eq config).

Hypothesis nodes_nodup : NoDup all_nodes.

(** Extensional uniqueness is more useful than uniqueness of message IDs here:
    two queued requests with the same sender and receiver must be the very same
    message. *)
Definition request_edges_unique
    (messages : list (@echo_message node)) : Prop :=
  forall first second,
    In first messages ->
    In second messages ->
    message_kind first = EchoRequest ->
    message_kind second = EchoRequest ->
    message_sender first = message_sender second ->
    message_receiver first = message_receiver second ->
    first = second.

Definition echo_request_edges_unique
    (state : @executable_echo_state node) : Prop :=
  request_edges_unique (message_store state).

Lemma request_edges_unique_sublist
    (smaller larger : list (@echo_message node)) :
  (forall message, In message smaller -> In message larger) ->
  request_edges_unique larger ->
  request_edges_unique smaller.
Proof.
  intros Hsubset Hunique first second Hfirst Hsecond
    Hfirst_kind Hsecond_kind Hsender Hreceiver.
  eapply Hunique; eauto.
Qed.

Lemma request_edges_unique_app_no_requests_right
    (left right : list (@echo_message node)) :
  request_edges_unique left ->
  (forall message,
      In message right -> message_kind message <> EchoRequest) ->
  request_edges_unique (left ++ right).
Proof.
  intros Hleft Hright first second Hfirst Hsecond
    Hfirst_kind Hsecond_kind Hsender Hreceiver.
  apply in_app_or in Hfirst. apply in_app_or in Hsecond.
  destruct Hfirst as [Hfirst | Hfirst];
    destruct Hsecond as [Hsecond | Hsecond].
  - eapply Hleft; eauto.
  - exfalso. exact (Hright second Hsecond Hsecond_kind).
  - exfalso. exact (Hright first Hfirst Hfirst_kind).
  - exfalso. exact (Hright first Hfirst Hfirst_kind).
Qed.

Lemma request_edges_unique_app_fresh_sender
    (left right : list (@echo_message node)) (fresh_sender : node) :
  request_edges_unique left ->
  request_edges_unique right ->
  (forall message,
      In message left ->
      message_kind message = EchoRequest ->
      message_sender message <> fresh_sender) ->
  (forall message,
      In message right ->
      message_kind message = EchoRequest ->
      message_sender message = fresh_sender) ->
  request_edges_unique (left ++ right).
Proof.
  intros Hleft Hright Hleft_sender Hright_sender
    first second Hfirst Hsecond Hfirst_kind Hsecond_kind Hsender Hreceiver.
  apply in_app_or in Hfirst. apply in_app_or in Hsecond.
  destruct Hfirst as [Hfirst | Hfirst];
    destruct Hsecond as [Hsecond | Hsecond].
  - eapply Hleft; eauto.
  - exfalso.
    apply (Hleft_sender first Hfirst Hfirst_kind).
    rewrite Hsender. now apply Hright_sender.
  - exfalso.
    apply (Hleft_sender second Hsecond Hsecond_kind).
    rewrite <- Hsender. now apply Hright_sender.
  - eapply Hright; eauto.
Qed.

Lemma materialized_request_block_fields
    (next_id : nat) (sender : node) (receivers : list node)
    (message : @echo_message node) :
  In message
    (materialize_echo_outbound next_id sender
      (List.map (mkEchoOutbound EchoRequest) receivers)) ->
  message_sender message = sender /\
  message_kind message = EchoRequest /\
  In (message_receiver message) receivers.
Proof.
  revert next_id.
  induction receivers as [| receiver rest IH]; intros next_id Hin.
  - contradiction.
  - cbn [materialize_echo_outbound] in Hin.
    destruct Hin as [Hequal | Hin].
    + subst message. cbn. auto.
    + destruct (IH (S next_id) Hin)
        as [Hsender [Hkind Hreceiver]].
      repeat split; try assumption. now right.
Qed.

Lemma materialized_request_block_receiver_injective
    (next_id : nat) (sender : node) (receivers : list node) :
  NoDup receivers ->
  forall first second,
    In first
      (materialize_echo_outbound next_id sender
        (List.map (mkEchoOutbound EchoRequest) receivers)) ->
    In second
      (materialize_echo_outbound next_id sender
        (List.map (mkEchoOutbound EchoRequest) receivers)) ->
    message_receiver first = message_receiver second ->
    first = second.
Proof.
  revert next_id.
  induction receivers as [| receiver rest IH];
    intros next_id Hnodup first second Hfirst Hsecond Hreceiver.
  - contradiction.
  - inversion Hnodup as [| ? ? Hnotin Hrest]; subst.
    cbn [materialize_echo_outbound] in Hfirst, Hsecond.
    destruct Hfirst as [Hfirst | Hfirst];
      destruct Hsecond as [Hsecond | Hsecond].
    + now subst first; subst second.
    + subst first.
      destruct (materialized_request_block_fields
          (S next_id) sender rest second Hsecond)
        as [Hsender [Hkind Hin]].
      cbn in Hreceiver. exfalso. apply Hnotin. now rewrite Hreceiver.
    + subst second.
      destruct (materialized_request_block_fields
          (S next_id) sender rest first Hfirst)
        as [Hsender [Hkind Hin]].
      cbn in Hreceiver. exfalso. apply Hnotin. now rewrite <- Hreceiver.
    + eapply IH; eauto.
Qed.

Lemma materialized_request_block_unique
    (next_id : nat) (sender : node) (receivers : list node) :
  NoDup receivers ->
  request_edges_unique
    (materialize_echo_outbound next_id sender
      (List.map (mkEchoOutbound EchoRequest) receivers)).
Proof.
  intros Hnodup first second Hfirst Hsecond
    Hfirst_kind Hsecond_kind Hsender Hreceiver.
  eapply materialized_request_block_receiver_injective; eauto.
Qed.

Lemma materialized_block_has_no_requests
    (next_id : nat) (sender : node)
    (outbound : list (@echo_outbound node)) :
  (forall item,
      In item outbound -> outbound_kind item <> EchoRequest) ->
  forall message,
    In message (materialize_echo_outbound next_id sender outbound) ->
    message_kind message <> EchoRequest.
Proof.
  intros Houtbound message Hin Hrequest.
  destruct (@materialized_echo_message_fields node
      next_id sender outbound message Hin)
    as [item [Hitem [Hsender Hkind]]].
  apply (Houtbound item Hitem). now rewrite <- Hkind.
Qed.

Lemma apply_echo_delivery_preserves_request_edges_unique_no_requests
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (outbound : list (@echo_outbound node)) :
  echo_request_edges_unique state ->
  (forall item,
      In item outbound -> outbound_kind item <> EchoRequest) ->
  echo_request_edges_unique
    (apply_echo_delivery node_eq state selected new_process outbound).
Proof.
  intros Hunique Houtbound.
  unfold echo_request_edges_unique in *.
  cbn [apply_echo_delivery].
  apply request_edges_unique_app_no_requests_right.
  - eapply request_edges_unique_sublist.
    + intros message Hin.
      exact (@remove_echo_message_in node
        (message_id selected) (message_store state) message Hin).
    + exact Hunique.
  - now apply materialized_block_has_no_requests.
Qed.

Lemma apply_first_request_nonleaf_preserves_request_edges_unique
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (ordered_forwards : list node) :
  echo_request_edges_unique state ->
  NoDup ordered_forwards ->
  (forall message,
      In message (message_store state) ->
      message_kind message = EchoRequest ->
      message_sender message <> message_receiver selected) ->
  echo_request_edges_unique
    (apply_echo_delivery node_eq state selected new_process
      (List.map (mkEchoOutbound EchoRequest) ordered_forwards)).
Proof.
  intros Hunique Hnodup Hfresh.
  unfold echo_request_edges_unique in *.
  cbn [apply_echo_delivery].
  apply request_edges_unique_app_fresh_sender
    with (fresh_sender := message_receiver selected).
  - eapply request_edges_unique_sublist.
    + intros message Hin.
      exact (@remove_echo_message_in node
        (message_id selected) (message_store state) message Hin).
    + exact Hunique.
  - now apply materialized_request_block_unique.
  - intros message Hin Hkind.
    apply Hfresh.
    + exact (@remove_echo_message_in node
        (message_id selected) (message_store state) message Hin).
    + exact Hkind.
  - intros message Hin Hkind.
    now destruct (materialized_request_block_fields
      (next_message_id state) (message_receiver selected)
      ordered_forwards message Hin) as [Hsender _].
Qed.

Theorem EchoStep_start_request_edges_unique
    (state successor : @executable_echo_state node)
    (ordered_neighbors : list node) :
  EchoStep state (EchoStart ordered_neighbors) successor ->
  echo_request_edges_unique successor.
Proof.
  intro Hstep.
  pose proof (@EchoStep_start_guards node node_eq config
    state successor ordered_neighbors Hstep) as [Hinitial Hpermutation].
  destruct Hinitial as [Hstarted [Hprocesses [Hstore Hnext]]].
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoStart ordered_neighbors) start_rule Hstep eq_refl) as Haction.
  cbn [eval_action start_rule ir_rule_action eval_nodes_expr] in Haction.
  subst successor.
  unfold echo_request_edges_unique.
  change (request_edges_unique
    (message_store state ++
      materialize_echo_outbound (next_message_id state) initiator
        (List.map (mkEchoOutbound EchoRequest) ordered_neighbors))).
  rewrite Hstore. cbn.
  apply materialized_request_block_unique.
  eapply Permutation_NoDup.
  - symmetry. exact Hpermutation.
  - unfold nbrs. now apply NoDup_filter.
Qed.

Theorem EchoStep_first_request_nonleaf_request_edges_unique
    (state successor : @executable_echo_state node)
    (message : @echo_message node) (ordered_forwards : list node) :
  echo_parent_forest_well_formed config state ->
  echo_request_edges_unique state ->
  EchoStep state (EchoFirstRequestNonLeaf message ordered_forwards) successor ->
  echo_request_edges_unique successor.
Proof.
  intros Hforest Hunique Hstep.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule (IRGuardProcessInitial IRMessageReceiver)
    Hstep eq_refl ltac:(
      cbn [first_echo_nonleaf_rule];
      repeat (first [left; reflexivity | right]))) as Hinitial.
  cbn [guard_holds eval_node_expr event_message] in Hinitial.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule
    (IRGuardPermutation IRNodesOrdered
      (IRNodesRemove IRMessageSender
        (IRNodesNeighbors IRMessageReceiver)))
    Hstep eq_refl ltac:(
      cbn [first_echo_nonleaf_rule];
      repeat (first [left; reflexivity | right]))) as Hpermutation.
  cbn [guard_holds eval_nodes_expr eval_node_expr event_message
    event_ordered_nodes] in Hpermutation.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule Hstep eq_refl) as Haction.
  cbn [eval_action first_echo_nonleaf_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message event_ordered_nodes] in Haction.
  subst successor.
  eapply apply_first_request_nonleaf_preserves_request_edges_unique.
  - exact Hunique.
  - eapply Permutation_NoDup.
    + symmetry. exact Hpermutation.
    + apply NoDup_remove_echo_node.
      unfold nbrs. now apply NoDup_filter.
  - intros queued Hqueued Hkind Hequal.
    destruct Hforest as [Htargets [Hsenders Hranked]].
    pose proof (Hsenders queued Hqueued Hkind) as Hdiscovered.
    unfold echo_discovered in Hdiscovered.
    rewrite Hequal, Hinitial in Hdiscovered. contradiction.
Qed.

Theorem EchoStep_preserves_request_edges_unique
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  echo_parent_forest_well_formed config state ->
  echo_request_edges_unique state ->
  EchoStep state event successor ->
  echo_request_edges_unique successor.
Proof.
  intros Hforest Hunique Hstep. destruct event.
  - now apply EchoStep_start_request_edges_unique in Hstep.
  - eapply EchoStep_first_request_nonleaf_request_edges_unique; eauto.
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoFirstRequestLeaf message) first_echo_leaf_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action first_echo_leaf_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    apply apply_echo_delivery_preserves_request_edges_unique_no_requests.
    + exact Hunique.
    + intros item Hitem Hkind.
      cbn in Hitem. destruct Hitem as [Hequal | Hin];
        [subst item; discriminate | contradiction].
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoRepeatedRequest message) repeated_echo_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action repeated_echo_rule ir_rule_action
      eval_process_expr eval_node_expr eval_outbound_expr event_message]
      in Haction.
    subst successor.
    apply apply_echo_delivery_preserves_request_edges_unique_no_requests.
    + exact Hunique.
    + intros item Hitem Hkind.
      cbn in Hitem. destruct Hitem as [Hequal | Hin];
        [subst item; discriminate | contradiction].
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorRequest message) initiator_echo_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_echo_rule ir_rule_action
      eval_process_expr eval_node_expr eval_outbound_expr event_message]
      in Haction.
    subst successor.
    apply apply_echo_delivery_preserves_request_edges_unique_no_requests.
    + exact Hunique.
    + intros item Hitem Hkind.
      cbn in Hitem. destruct Hitem as [Hequal | Hin];
        [subst item; discriminate | contradiction].
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoParticipantReplyMore message parent) participant_ack_more_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action participant_ack_more_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_parent] in Haction.
    subst successor.
    apply apply_echo_delivery_preserves_request_edges_unique_no_requests.
    + exact Hunique.
    + intros item Hitem. contradiction.
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoParticipantReplyFinal message parent) participant_ack_final_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action participant_ack_final_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_parent] in Haction.
    subst successor.
    apply apply_echo_delivery_preserves_request_edges_unique_no_requests.
    + exact Hunique.
    + intros item Hitem Hkind.
      cbn in Hitem. destruct Hitem as [Hequal | Hin];
        [subst item; discriminate | contradiction].
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorReplyMore message) initiator_ack_more_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_ack_more_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    apply apply_echo_delivery_preserves_request_edges_unique_no_requests.
    + exact Hunique.
    + intros item Hitem. contradiction.
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorReplyFinal message) initiator_ack_final_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_ack_final_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    apply apply_echo_delivery_preserves_request_edges_unique_no_requests.
    + exact Hunique.
    + intros item Hitem. contradiction.
Qed.

Lemma initial_executable_echo_state_request_edges_unique :
  echo_request_edges_unique initial_executable_echo_state.
Proof.
  unfold echo_request_edges_unique, request_edges_unique.
  intros first second Hfirst. contradiction.
Qed.

Theorem echo_reachable_request_edges_unique
    (state : @executable_echo_state node) :
  echo_reachable node_eq config state ->
  echo_request_edges_unique state.
Proof.
  intro Hreachable.
  induction Hreachable as [| before event after Hbefore IH Hstep].
  - apply initial_executable_echo_state_request_edges_unique.
  - eapply EchoStep_preserves_request_edges_unique.
    + exact (@echo_reachable_parent_forest node node_eq config
        before Hbefore).
    + exact IH.
    + exact Hstep.
Qed.

(** The selected occurrence is absent after ID-based removal when queued IDs
    are unique.  This turns directed-edge uniqueness into a usable causal
    fact for first-request delivery. *)
Lemma remove_echo_message_selected_not_in
    (selected : @echo_message node)
    (messages : list (@echo_message node)) :
  NoDup (List.map message_id messages) ->
  In selected messages ->
  ~ In selected
      (remove_echo_message (message_id selected) messages).
Proof.
  induction messages as [| head rest IH]; intros Hnodup Hin.
  - contradiction.
  - inversion Hnodup as [| head_id rest_ids Hhead_notin Hrest]; subst.
    cbn [remove_echo_message].
    destruct (Nat.eqb (message_id selected) (message_id head))
        eqn:Hsame_id.
    + apply Nat.eqb_eq in Hsame_id.
      destruct Hin as [Hequal | Hin].
      * subst head. intro Hselected.
        apply Hhead_notin. apply in_map. exact Hselected.
      * exfalso. apply Hhead_notin.
        apply in_map_iff. exists selected. auto.
    + apply Nat.eqb_neq in Hsame_id.
      destruct Hin as [Hequal | Hin].
      * subst head. contradiction.
      * intro Hremoved. destruct Hremoved as [Hequal | Hremoved].
        -- subst head. contradiction.
        -- exact (IH Hrest Hin Hremoved).
Qed.

(** A queued request never points from a participant's installed parent back
    to that participant.  The unique parent-installing request has already
    been consumed; later requests come only from other neighbors. *)
Definition echo_request_parent_distinct
    (state : @executable_echo_state node) : Prop :=
  forall message,
    In message (message_store state) ->
    message_kind message = EchoRequest ->
    process_parent
      (processes state (message_receiver message)) <>
    Some (message_sender message).

Lemma apply_parent_preserving_delivery_request_parent_distinct
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (outbound : list (@echo_outbound node)) :
  echo_request_parent_distinct state ->
  process_parent new_process =
    process_parent (processes state (message_receiver selected)) ->
  (forall item,
      In item outbound -> outbound_kind item <> EchoRequest) ->
  echo_request_parent_distinct
    (apply_echo_delivery node_eq state selected new_process outbound).
Proof.
  intros Hold Hparent Houtbound request Hrequest Hkind.
  cbn [apply_echo_delivery] in Hrequest.
  apply in_app_or in Hrequest. destruct Hrequest as [Hrequest | Hrequest].
  - pose proof (@remove_echo_message_in node
      (message_id selected) (message_store state) request Hrequest)
      as Hrequest_old.
    destruct (node_eq (message_receiver selected)
        (message_receiver request)) as [Hequal | Hdifferent].
    + rewrite <- Hequal. rewrite apply_echo_delivery_process_self.
      rewrite Hparent, Hequal. apply (Hold request Hrequest_old Hkind).
    + rewrite apply_echo_delivery_process_other by exact Hdifferent.
      apply (Hold request Hrequest_old Hkind).
  - exfalso.
    exact (materialized_block_has_no_requests
      (next_message_id state) (message_receiver selected) outbound
      Houtbound request Hrequest Hkind).
Qed.

Lemma apply_first_request_delivery_request_parent_distinct
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (outbound : list (@echo_outbound node)) :
  echo_request_parent_distinct state ->
  echo_request_edges_unique state ->
  echo_message_ids_well_formed state ->
  In selected (message_store state) ->
  message_kind selected = EchoRequest ->
  process_parent new_process = Some (message_sender selected) ->
  (forall request,
      In request
        (materialize_echo_outbound
          (next_message_id state) (message_receiver selected) outbound) ->
      message_kind request = EchoRequest ->
      process_parent
        (update_process node_eq (processes state)
          (message_receiver selected) new_process
          (message_receiver request)) <>
      Some (message_sender request)) ->
  echo_request_parent_distinct
    (apply_echo_delivery node_eq state selected new_process outbound).
Proof.
  intros Hold Hunique [Hbelow Hids] Hselected Hselected_kind
    Hnew_parent Hnew_requests request Hrequest Hkind.
  cbn [apply_echo_delivery] in Hrequest.
  apply in_app_or in Hrequest. destruct Hrequest as [Hrequest | Hrequest].
  - pose proof (@remove_echo_message_in node
      (message_id selected) (message_store state) request Hrequest)
      as Hrequest_old.
    change
      (process_parent
        (update_process node_eq (processes state)
          (message_receiver selected) new_process
          (message_receiver request)) <>
       Some (message_sender request)).
    destruct (node_eq (message_receiver selected)
        (message_receiver request)) as [Hequal | Hdifferent].
    + unfold update_process.
      destruct (node_eq (message_receiver selected)
          (message_receiver request)); [| contradiction].
      rewrite Hnew_parent.
      intro Hsame_parent. injection Hsame_parent as Hsame_sender.
      assert (Hsame_message : request = selected).
      { eapply Hunique.
        - exact Hrequest_old.
        - exact Hselected.
        - exact Hkind.
        - exact Hselected_kind.
        - now symmetry.
        - now symmetry. }
      subst request.
      exact (remove_echo_message_selected_not_in
        selected (message_store state) Hids Hselected Hrequest).
    + unfold update_process.
      destruct (node_eq (message_receiver selected)
          (message_receiver request)); [contradiction |].
      apply (Hold request Hrequest_old Hkind).
  - exact (Hnew_requests request Hrequest Hkind).
Qed.

Theorem EchoStep_start_request_parent_distinct
    (state successor : @executable_echo_state node)
    (ordered_neighbors : list node) :
  EchoStep state (EchoStart ordered_neighbors) successor ->
  echo_request_parent_distinct successor.
Proof.
  intro Hstep.
  pose proof (@EchoStep_start_guards node node_eq config
    state successor ordered_neighbors Hstep) as [Hinitial Hpermutation].
  destruct Hinitial as [Hstarted [Hprocesses [Hstore Hnext]]].
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoStart ordered_neighbors) start_rule Hstep eq_refl) as Haction.
  cbn [eval_action start_rule ir_rule_action eval_nodes_expr] in Haction.
  subst successor.
  intros request Hrequest Hkind.
  change (In request
    (message_store state ++
      materialize_echo_outbound (next_message_id state) initiator
        (List.map (mkEchoOutbound EchoRequest) ordered_neighbors)))
    in Hrequest.
  rewrite Hstore in Hrequest. cbn in Hrequest.
  destruct (materialized_request_block_fields
      (next_message_id state) initiator ordered_neighbors request Hrequest)
    as [Hsender [Hrequest_kind Hreceiver]].
  assert (Hreceiver_node : In (message_receiver request) all_nodes).
  { assert (Hneighbor : In (message_receiver request)
        (nbrs all_nodes adj initiator)).
    { eapply Permutation_in; eauto. }
    unfold nbrs in Hneighbor. now apply filter_In in Hneighbor. }
  unfold apply_echo_start. cbn. unfold update_process.
  destruct (node_eq initiator (message_receiver request))
      as [Hequal | Hdifferent].
  - cbn. rewrite Hsender. discriminate.
  - rewrite (Hprocesses (message_receiver request) Hreceiver_node).
    cbn. discriminate.
Qed.

Theorem EchoStep_first_request_nonleaf_request_parent_distinct
    (state successor : @executable_echo_state node)
    (message : @echo_message node) (ordered_forwards : list node) :
  echo_parent_forest_well_formed config state ->
  echo_request_parent_distinct state ->
  echo_request_edges_unique state ->
  echo_message_ids_well_formed state ->
  EchoStep state (EchoFirstRequestNonLeaf message ordered_forwards) successor ->
  echo_request_parent_distinct successor.
Proof.
  intros Hforest Hdistinct Hunique Hids Hstep.
  pose proof (@EchoStep_delivery_message_queued node node_eq config
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
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule
    (IRGuardPermutation IRNodesOrdered
      (IRNodesRemove IRMessageSender
        (IRNodesNeighbors IRMessageReceiver)))
    Hstep eq_refl ltac:(
      cbn [first_echo_nonleaf_rule];
      repeat (first [left; reflexivity | right]))) as Hpermutation.
  cbn [guard_holds eval_nodes_expr eval_node_expr event_message
    event_ordered_nodes] in Hpermutation.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule Hstep eq_refl) as Haction.
  cbn [eval_action first_echo_nonleaf_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message event_ordered_nodes] in Haction.
  subst successor.
  eapply apply_first_request_delivery_request_parent_distinct.
  - exact Hdistinct.
  - exact Hunique.
  - exact Hids.
  - exact Hselected.
  - exact Hkind.
  - reflexivity.
  - intros request Hrequest Hrequest_kind.
    destruct (materialized_request_block_fields
        (next_message_id state) (message_receiver message)
        ordered_forwards request Hrequest)
      as [Hsender [Hkind_new Hreceiver]].
    assert (Hreceiver_node : In (message_receiver request) all_nodes).
    { assert (Hforward : In (message_receiver request)
          (remove_echo_node node_eq (message_sender message)
            (nbrs all_nodes adj (message_receiver message)))).
      { eapply Permutation_in; eauto. }
      apply in_remove_echo_node in Hforward.
      unfold nbrs in Hforward. now apply filter_In in Hforward. }
    destruct Hforest as [Htargets [Hsenders Hranked]].
    assert (Hselected_sender_different :
        message_sender message <> message_receiver message).
    { intro Hequal.
      pose proof (Hsenders message Hselected Hkind) as Hdiscovered.
      unfold echo_discovered in Hdiscovered.
      rewrite Hequal, Hinitial in Hdiscovered. contradiction. }
    unfold update_process.
    destruct (node_eq (message_receiver message)
        (message_receiver request)) as [Hequal | Hdifferent].
    + rewrite Hsender. cbn. intro Hparent.
      injection Hparent as Hparent. contradiction.
    + rewrite Hsender. intro Hparent.
      pose proof (Htargets (message_receiver request)
        (message_receiver message) Hreceiver_node Hparent)
        as Hdiscovered.
      unfold echo_discovered in Hdiscovered.
      rewrite Hinitial in Hdiscovered. contradiction.
Qed.

Theorem EchoStep_first_request_leaf_request_parent_distinct
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_request_parent_distinct state ->
  echo_request_edges_unique state ->
  echo_message_ids_well_formed state ->
  EchoStep state (EchoFirstRequestLeaf message) successor ->
  echo_request_parent_distinct successor.
Proof.
  intros Hdistinct Hunique Hids Hstep.
  pose proof (@EchoStep_delivery_message_queued node node_eq config
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
  eapply apply_first_request_delivery_request_parent_distinct.
  - exact Hdistinct.
  - exact Hunique.
  - exact Hids.
  - exact Hselected.
  - exact Hkind.
  - reflexivity.
  - intros request Hrequest Hrequest_kind.
    cbn [materialize_echo_outbound] in Hrequest.
    destruct Hrequest as [Hequal | Hin].
    + subst request. discriminate.
    + contradiction.
Qed.

Theorem EchoStep_preserves_request_parent_distinct
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  echo_parent_forest_well_formed config state ->
  echo_request_edges_unique state ->
  echo_message_ids_well_formed state ->
  echo_request_parent_distinct state ->
  EchoStep state event successor ->
  echo_request_parent_distinct successor.
Proof.
  intros Hforest Hunique Hids Hdistinct Hstep. destruct event.
  - now apply EchoStep_start_request_parent_distinct in Hstep.
  - eapply EchoStep_first_request_nonleaf_request_parent_distinct; eauto.
  - eapply EchoStep_first_request_leaf_request_parent_distinct; eauto.
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoRepeatedRequest message) repeated_echo_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action repeated_echo_rule ir_rule_action
      eval_process_expr eval_node_expr eval_outbound_expr event_message]
      in Haction.
    subst successor.
    eapply apply_parent_preserving_delivery_request_parent_distinct.
    + exact Hdistinct.
    + reflexivity.
    + intros item Hitem Hkind.
      cbn in Hitem. destruct Hitem as [Hequal | Hin];
        [subst item; discriminate | contradiction].
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
    eapply apply_parent_preserving_delivery_request_parent_distinct.
    + exact Hdistinct.
    + now rewrite Hequal.
    + intros item Hitem Hkind.
      cbn in Hitem. destruct Hitem as [Hitem | Hin];
        [subst item; discriminate | contradiction].
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoParticipantReplyMore message parent)
      participant_ack_more_rule
      (IRGuardParentEqual IRMessageReceiver (IRSomeParent IREventParent))
      Hstep eq_refl ltac:(
        cbn [participant_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hparent.
    cbn [guard_holds eval_node_expr eval_parent_expr event_message
      event_parent] in Hparent.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoParticipantReplyMore message parent) participant_ack_more_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action participant_ack_more_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_parent] in Haction.
    subst successor.
    eapply apply_parent_preserving_delivery_request_parent_distinct.
    + exact Hdistinct.
    + now symmetry.
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
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoParticipantReplyFinal message parent) participant_ack_final_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action participant_ack_final_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_parent] in Haction.
    subst successor.
    eapply apply_parent_preserving_delivery_request_parent_distinct.
    + exact Hdistinct.
    + now symmetry.
    + intros item Hitem Hkind.
      cbn in Hitem. destruct Hitem as [Hitem | Hin];
        [subst item; discriminate | contradiction].
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorReplyMore message) initiator_ack_more_rule
      (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [initiator_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hequal.
    cbn [guard_holds eval_node_expr event_message] in Hequal.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorReplyMore message) initiator_ack_more_rule
      (IRGuardParentEqual IRInitiatorNode IRNoParent)
      Hstep eq_refl ltac:(
        cbn [initiator_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hparent.
    cbn [guard_holds eval_node_expr eval_parent_expr] in Hparent.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorReplyMore message) initiator_ack_more_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_ack_more_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    eapply apply_parent_preserving_delivery_request_parent_distinct.
    + exact Hdistinct.
    + rewrite Hequal. now symmetry.
    + intros item Hitem. contradiction.
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorReplyFinal message) initiator_ack_final_rule
      (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [initiator_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hequal.
    cbn [guard_holds eval_node_expr event_message] in Hequal.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoInitiatorReplyFinal message) initiator_ack_final_rule
      (IRGuardParentEqual IRInitiatorNode IRNoParent)
      Hstep eq_refl ltac:(
        cbn [initiator_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hparent.
    cbn [guard_holds eval_node_expr eval_parent_expr] in Hparent.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorReplyFinal message) initiator_ack_final_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_ack_final_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    eapply apply_parent_preserving_delivery_request_parent_distinct.
    + exact Hdistinct.
    + rewrite Hequal. now symmetry.
    + intros item Hitem. contradiction.
Qed.

Lemma initial_executable_echo_state_request_parent_distinct :
  echo_request_parent_distinct initial_executable_echo_state.
Proof.
  intros message Hin. contradiction.
Qed.

Theorem echo_reachable_request_parent_distinct
    (state : @executable_echo_state node) :
  echo_reachable node_eq config state ->
  echo_request_parent_distinct state.
Proof.
  intro Hreachable.
  induction Hreachable as [| before event after Hbefore IH Hstep].
  - apply initial_executable_echo_state_request_parent_distinct.
  - eapply EchoStep_preserves_request_parent_distinct.
    + exact (@echo_reachable_parent_forest node node_eq config
        before Hbefore).
    + exact (echo_reachable_request_edges_unique before Hbefore).
    + exact (@echo_reachable_message_ids_well_formed node node_eq config
        before Hbefore).
    + exact IH.
    + exact Hstep.
Qed.

(** A combined field projection for materialized messages.  The earlier
    request-only projection is convenient for request blocks; this generic
    form is used to reason about newly emitted replies. *)
Lemma materialized_echo_message_complete_fields
    (next_id : nat) (sender : node)
    (outbound : list (@echo_outbound node))
    (message : @echo_message node) :
  In message (materialize_echo_outbound next_id sender outbound) ->
  exists item,
    In item outbound /\
    message_sender message = sender /\
    message_receiver message = outbound_receiver item /\
    message_kind message = outbound_kind item.
Proof.
  revert next_id.
  induction outbound as [| item rest IH]; intros next_id Hin.
  - contradiction.
  - cbn [materialize_echo_outbound] in Hin.
    destruct Hin as [Hequal | Hin].
    + subst message. exists item. cbn. auto.
    + destruct (IH (S next_id) Hin)
        as [found [Hfound [Hsender [Hreceiver Hkind]]]].
      exists found. repeat split; try assumption. now right.
Qed.

(** Replies are addressed only to nodes that have already left their initial
    process state.  A reply to a request targets the request's discovered
    sender; a participant's final reply targets its already-discovered
    parent. *)
Definition echo_reply_receivers_discovered
    (state : @executable_echo_state node) : Prop :=
  forall message,
    In message (message_store state) ->
    message_kind message = EchoReply ->
    echo_discovered state (message_receiver message).

Lemma apply_echo_delivery_preserves_reply_receivers_discovered
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (outbound : list (@echo_outbound node)) :
  echo_reply_receivers_discovered state ->
  (echo_discovered state (message_receiver selected) ->
    new_process <> initial_echo_process) ->
  (forall item,
      In item outbound ->
      outbound_kind item = EchoReply ->
      echo_discovered
        (apply_echo_delivery node_eq state selected new_process outbound)
        (outbound_receiver item)) ->
  echo_reply_receivers_discovered
    (apply_echo_delivery node_eq state selected new_process outbound).
Proof.
  intros Hold Hnew_process Hnew_reply message Hin Hkind.
  cbn [apply_echo_delivery] in Hin.
  apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - apply remove_echo_message_in in Hin.
    eapply apply_echo_delivery_discovered_monotone.
    + exact Hnew_process.
    + now apply (Hold message Hin Hkind).
  - destruct (materialized_echo_message_complete_fields
      (next_message_id state) (message_receiver selected)
      outbound message Hin)
      as [item [Hitem [Hsender [Hreceiver Hitem_kind]]]].
    rewrite Hreceiver. apply Hnew_reply.
    + exact Hitem.
    + now rewrite <- Hitem_kind.
Qed.

Theorem EchoStep_start_reply_receivers_discovered
    (state successor : @executable_echo_state node)
    (ordered_neighbors : list node) :
  EchoStep state (EchoStart ordered_neighbors) successor ->
  echo_reply_receivers_discovered successor.
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
  destruct (materialized_request_block_fields
      (next_message_id state) initiator ordered_neighbors message Hin)
    as [Hsender [Hrequest_kind Hreceiver]].
  congruence.
Qed.

Section ReplyDiscoveryReachability.

Hypothesis initiator_in_nodes : In initiator all_nodes.
Hypothesis adj_symmetric :
  forall left right, adj left right = true -> adj right left = true.

Theorem EchoStep_preserves_reply_receivers_discovered
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  echo_parent_forest_well_formed config state ->
  echo_topology_well_formed config state ->
  echo_reply_receivers_discovered state ->
  EchoStep state event successor ->
  echo_reply_receivers_discovered successor.
Proof.
  intros Hforest Htopology Hreplies Hstep. destruct event.
  - now apply EchoStep_start_reply_receivers_discovered in Hstep.
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
    eapply apply_echo_delivery_preserves_reply_receivers_discovered.
    + exact Hreplies.
    + intro Hdiscovered. unfold echo_discovered in Hdiscovered.
      rewrite Hinitial in Hdiscovered. contradiction.
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
    eapply apply_echo_delivery_preserves_reply_receivers_discovered.
    + exact Hreplies.
    + intros Hdiscovered. apply parented_process_discovered.
    + intros item Hitem Hitem_kind.
      cbn in Hitem. destruct Hitem as [Hequal | Hin]; [| contradiction].
      subst item. cbn.
      eapply apply_echo_delivery_discovered_monotone.
      * intros Hdiscovered. apply parented_process_discovered.
      * destruct Hforest as [Htargets [Hsenders Hranked]].
        now eapply Hsenders.
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
    eapply apply_echo_delivery_preserves_reply_receivers_discovered.
    + exact Hreplies.
    + intros Hdiscovered. exact Hdiscovered.
    + intros item Hitem Hitem_kind.
      cbn in Hitem. destruct Hitem as [Hequal | Hin]; [| contradiction].
      subst item. cbn.
      eapply apply_echo_delivery_discovered_monotone.
      * intros Hdiscovered. exact Hdiscovered.
      * destruct Hforest as [Htargets [Hsenders Hranked]].
        now eapply Hsenders.
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
        repeat (first [left; reflexivity | right]))) as Hequal.
    cbn [guard_holds eval_node_expr event_message] in Hequal.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorRequest message) initiator_echo_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_echo_rule ir_rule_action
      eval_process_expr eval_node_expr eval_outbound_expr event_message]
      in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_reply_receivers_discovered.
    + exact Hreplies.
    + rewrite Hequal. intros Hdiscovered. exact Hdiscovered.
    + intros item Hitem Hitem_kind.
      cbn in Hitem. destruct Hitem as [Hitem | Hin]; [| contradiction].
      subst item. cbn.
      eapply apply_echo_delivery_discovered_monotone.
      * rewrite Hequal. intros Hdiscovered. exact Hdiscovered.
      * destruct Hforest as [Htargets [Hsenders Hranked]].
        now eapply Hsenders.
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoParticipantReplyMore message parent) participant_ack_more_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action participant_ack_more_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_parent] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_reply_receivers_discovered.
    + exact Hreplies.
    + intros Hdiscovered. apply parented_process_discovered.
    + intros item Hitem. contradiction.
  - pose proof (@EchoStep_delivery_message_queued node node_eq config
      state successor (EchoParticipantReplyFinal message parent) Hstep I)
      as Hselected.
    pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoParticipantReplyFinal message parent)
      participant_ack_final_rule
      (IRGuardParentEqual IRMessageReceiver (IRSomeParent IREventParent))
      Hstep eq_refl ltac:(
        cbn [participant_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hparent.
    cbn [guard_holds eval_node_expr eval_parent_expr event_message
      event_parent] in Hparent.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoParticipantReplyFinal message parent) participant_ack_final_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action participant_ack_final_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_parent] in Haction.
    subst successor.
    eapply apply_echo_delivery_preserves_reply_receivers_discovered.
    + exact Hreplies.
    + intros Hdiscovered. apply parented_process_discovered.
    + intros item Hitem Hitem_kind.
      cbn in Hitem. destruct Hitem as [Hequal | Hin]; [| contradiction].
      subst item. cbn.
      eapply apply_echo_delivery_discovered_monotone.
      * intros Hdiscovered. apply parented_process_discovered.
      * destruct Hforest as [Htargets [Hsenders Hranked]].
        destruct Htopology as [Hparents Hqueued].
        destruct (Hqueued message Hselected)
          as [Hsender_node [Hreceiver_node Hedge]].
        eapply Htargets.
        -- exact Hreceiver_node.
        -- now symmetry.
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
    eapply apply_echo_delivery_preserves_reply_receivers_discovered.
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
    eapply apply_echo_delivery_preserves_reply_receivers_discovered.
    + exact Hreplies.
    + intros Hdiscovered. apply finished_root_discovered.
    + intros item Hitem. contradiction.
Qed.

Lemma initial_executable_echo_state_reply_receivers_discovered :
  echo_reply_receivers_discovered initial_executable_echo_state.
Proof.
  intros message Hin. contradiction.
Qed.

Theorem echo_reachable_reply_receivers_discovered
    (state : @executable_echo_state node) :
  echo_reachable node_eq config state ->
  echo_reply_receivers_discovered state.
Proof.
  intro Hreachable.
  induction Hreachable as [| before event after Hbefore IH Hstep].
  - apply initial_executable_echo_state_reply_receivers_discovered.
  - eapply EchoStep_preserves_reply_receivers_discovered.
    + exact (@echo_reachable_parent_forest node node_eq config
        before Hbefore).
    + exact (@echo_reachable_topology node node_eq config
        initiator_in_nodes adj_symmetric before Hbefore).
    + exact IH.
    + exact Hstep.
Qed.

End ReplyDiscoveryReachability.

(** A request and its reverse reply cannot both remain in the queue.  This is
    the edge-local accounting fact that connects request consumption with
    reply production. *)
Definition echo_request_reply_reverse_distinct
    (state : @executable_echo_state node) : Prop :=
  forall request reply,
    In request (message_store state) ->
    In reply (message_store state) ->
    message_kind request = EchoRequest ->
    message_kind reply = EchoReply ->
    message_sender request = message_receiver reply ->
    message_receiver request = message_sender reply ->
    False.

Lemma request_reply_reverse_distinct_sublist
    (state : @executable_echo_state node)
    (messages : list (@echo_message node)) :
  (forall message, In message messages -> In message (message_store state)) ->
  echo_request_reply_reverse_distinct state ->
  forall request reply,
    In request messages ->
    In reply messages ->
    message_kind request = EchoRequest ->
    message_kind reply = EchoReply ->
    message_sender request = message_receiver reply ->
    message_receiver request = message_sender reply ->
    False.
Proof.
  intros Hsubset Hdistinct request reply Hrequest Hreply
    Hrequest_kind Hreply_kind Hsender Hreceiver.
  eapply Hdistinct.
  - exact (Hsubset request Hrequest).
  - exact (Hsubset reply Hreply).
  - exact Hrequest_kind.
  - exact Hreply_kind.
  - exact Hsender.
  - exact Hreceiver.
Qed.

Lemma apply_empty_delivery_preserves_request_reply_reverse_distinct
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node) :
  echo_request_reply_reverse_distinct state ->
  echo_request_reply_reverse_distinct
    (apply_echo_delivery node_eq state selected new_process []).
Proof.
  unfold echo_request_reply_reverse_distinct in *.
  intros Hdistinct request reply Hrequest Hreply
    Hrequest_kind Hreply_kind Hsender Hreceiver.
  change (In request
    (remove_echo_message (message_id selected) (message_store state) ++
      materialize_echo_outbound
        (next_message_id state) (message_receiver selected) [])) in Hrequest.
  change (In reply
    (remove_echo_message (message_id selected) (message_store state) ++
      materialize_echo_outbound
        (next_message_id state) (message_receiver selected) [])) in Hreply.
  cbn [materialize_echo_outbound] in Hrequest, Hreply.
  rewrite app_nil_r in Hrequest, Hreply.
  eapply Hdistinct.
  - exact (@remove_echo_message_in node
      (message_id selected) (message_store state) request Hrequest).
  - exact (@remove_echo_message_in node
      (message_id selected) (message_store state) reply Hreply).
  - exact Hrequest_kind.
  - exact Hreply_kind.
  - exact Hsender.
  - exact Hreceiver.
Qed.

(** Consuming a request and immediately emitting its reverse reply is safe:
    directed request-edge uniqueness says that any conflicting old request is
    the selected request itself, while message-ID uniqueness says that the
    selected occurrence was actually removed. *)
Lemma apply_request_reply_delivery_preserves_reverse_distinct
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node) :
  echo_request_reply_reverse_distinct state ->
  echo_request_edges_unique state ->
  echo_message_ids_well_formed state ->
  In selected (message_store state) ->
  message_kind selected = EchoRequest ->
  echo_request_reply_reverse_distinct
    (apply_echo_delivery node_eq state selected new_process
      [mkEchoOutbound EchoReply (message_sender selected)]).
Proof.
  unfold echo_request_reply_reverse_distinct in *.
  intros Hdistinct Hunique [Hbelow Hids] Hselected Hselected_kind
    request reply Hrequest Hreply Hrequest_kind Hreply_kind
    Hsender Hreceiver.
  cbn [apply_echo_delivery] in Hrequest, Hreply.
  apply in_app_or in Hrequest. apply in_app_or in Hreply.
  destruct Hrequest as [Hrequest | Hrequest];
    destruct Hreply as [Hreply | Hreply].
  - eapply Hdistinct.
    + exact (@remove_echo_message_in node
        (message_id selected) (message_store state) request Hrequest).
    + exact (@remove_echo_message_in node
        (message_id selected) (message_store state) reply Hreply).
    + exact Hrequest_kind.
    + exact Hreply_kind.
    + exact Hsender.
    + exact Hreceiver.
  - cbn [materialize_echo_outbound] in Hreply.
    destruct Hreply as [Hreply | Hreply]; [| contradiction].
    subst reply. cbn in Hsender, Hreceiver.
    assert (Hequal : request = selected).
    { eapply Hunique.
      - exact (@remove_echo_message_in node
          (message_id selected) (message_store state) request Hrequest).
      - exact Hselected.
      - exact Hrequest_kind.
      - exact Hselected_kind.
      - exact Hsender.
      - exact Hreceiver. }
    subst request.
    exact (remove_echo_message_selected_not_in
      selected (message_store state) Hids Hselected Hrequest).
  - cbn [materialize_echo_outbound] in Hrequest.
    destruct Hrequest as [Hrequest | Hrequest]; [| contradiction].
    subst request. discriminate.
  - cbn [materialize_echo_outbound] in Hrequest.
    destruct Hrequest as [Hrequest | Hrequest]; [| contradiction].
    subst request. discriminate.
Qed.

(** A participant's final reply is sent to its installed parent.  The
    consumed-parent-request invariant excludes the only request that could be
    reverse to this newly emitted reply. *)
Lemma apply_parent_reply_delivery_preserves_reverse_distinct
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (parent : node) :
  echo_request_reply_reverse_distinct state ->
  echo_request_parent_distinct state ->
  process_parent (processes state (message_receiver selected)) = Some parent ->
  echo_request_reply_reverse_distinct
    (apply_echo_delivery node_eq state selected new_process
      [mkEchoOutbound EchoReply parent]).
Proof.
  unfold echo_request_reply_reverse_distinct in *.
  intros Hdistinct Hparent_distinct Hparent
    request reply Hrequest Hreply Hrequest_kind Hreply_kind
    Hsender Hreceiver.
  cbn [apply_echo_delivery] in Hrequest, Hreply.
  apply in_app_or in Hrequest. apply in_app_or in Hreply.
  destruct Hrequest as [Hrequest | Hrequest];
    destruct Hreply as [Hreply | Hreply].
  - eapply Hdistinct.
    + exact (@remove_echo_message_in node
        (message_id selected) (message_store state) request Hrequest).
    + exact (@remove_echo_message_in node
        (message_id selected) (message_store state) reply Hreply).
    + exact Hrequest_kind.
    + exact Hreply_kind.
    + exact Hsender.
    + exact Hreceiver.
  - cbn [materialize_echo_outbound] in Hreply.
    destruct Hreply as [Hreply | Hreply]; [| contradiction].
    subst reply. cbn in Hsender, Hreceiver.
    apply (Hparent_distinct request
      (@remove_echo_message_in node
        (message_id selected) (message_store state) request Hrequest)
      Hrequest_kind).
    rewrite Hreceiver, Hsender. exact Hparent.
  - cbn [materialize_echo_outbound] in Hrequest.
    destruct Hrequest as [Hrequest | Hrequest]; [| contradiction].
    subst request. discriminate.
  - cbn [materialize_echo_outbound] in Hrequest.
    destruct Hrequest as [Hrequest | Hrequest]; [| contradiction].
    subst request. discriminate.
Qed.

(** The first non-leaf delivery emits the only non-start request block.  Its
    sender was initial immediately before the step, while every old reply
    receiver was discovered, so no old reverse reply can conflict with the
    new block. *)
Lemma apply_first_nonleaf_preserves_request_reply_reverse_distinct
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (ordered_forwards : list node) :
  echo_request_reply_reverse_distinct state ->
  echo_reply_receivers_discovered state ->
  processes state (message_receiver selected) = initial_echo_process ->
  echo_request_reply_reverse_distinct
    (apply_echo_delivery node_eq state selected new_process
      (List.map (mkEchoOutbound EchoRequest) ordered_forwards)).
Proof.
  unfold echo_request_reply_reverse_distinct in *.
  intros Hdistinct Hreplies Hinitial
    request reply Hrequest Hreply Hrequest_kind Hreply_kind
    Hsender Hreceiver.
  cbn [apply_echo_delivery] in Hrequest, Hreply.
  apply in_app_or in Hrequest. apply in_app_or in Hreply.
  destruct Hrequest as [Hrequest | Hrequest];
    destruct Hreply as [Hreply | Hreply].
  - eapply Hdistinct.
    + exact (@remove_echo_message_in node
        (message_id selected) (message_store state) request Hrequest).
    + exact (@remove_echo_message_in node
        (message_id selected) (message_store state) reply Hreply).
    + exact Hrequest_kind.
    + exact Hreply_kind.
    + exact Hsender.
    + exact Hreceiver.
  - destruct (materialized_echo_message_complete_fields
      (next_message_id state) (message_receiver selected)
      (List.map (mkEchoOutbound EchoRequest) ordered_forwards)
      reply Hreply) as [item [Hitem [Hitem_sender
        [Hitem_receiver Hitem_kind]]]].
    apply in_map_iff in Hitem.
    destruct Hitem as [receiver [Hequal Hreceiver_in]].
    subst item. cbn in Hitem_kind. congruence.
  - pose proof (Hreplies reply
      (@remove_echo_message_in node
        (message_id selected) (message_store state) reply Hreply)
      Hreply_kind) as Hdiscovered.
    destruct (materialized_request_block_fields
      (next_message_id state) (message_receiver selected)
      ordered_forwards request Hrequest) as [Hnew_sender _].
    unfold echo_discovered in Hdiscovered.
    rewrite <- Hsender, Hnew_sender, Hinitial in Hdiscovered.
    contradiction.
  - destruct (materialized_echo_message_complete_fields
      (next_message_id state) (message_receiver selected)
      (List.map (mkEchoOutbound EchoRequest) ordered_forwards)
      reply Hreply) as [item [Hitem [Hitem_sender
        [Hitem_receiver Hitem_kind]]]].
    apply in_map_iff in Hitem.
    destruct Hitem as [receiver [Hequal Hreceiver_in]].
    subst item. cbn in Hitem_kind. congruence.
Qed.

Theorem EchoStep_start_request_reply_reverse_distinct
    (state successor : @executable_echo_state node)
    (ordered_neighbors : list node) :
  EchoStep state (EchoStart ordered_neighbors) successor ->
  echo_request_reply_reverse_distinct successor.
Proof.
  unfold echo_request_reply_reverse_distinct.
  intro Hstep.
  pose proof (@EchoStep_start_guards node node_eq config
    state successor ordered_neighbors Hstep) as [Hinitial Hpermutation].
  destruct Hinitial as [Hstarted [Hprocesses [Hstore Hnext]]].
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoStart ordered_neighbors) start_rule Hstep eq_refl) as Haction.
  cbn [eval_action start_rule ir_rule_action eval_nodes_expr] in Haction.
  subst successor.
  intros request reply Hrequest Hreply Hrequest_kind Hreply_kind.
  change (In reply
    (message_store state ++
      materialize_echo_outbound (next_message_id state) initiator
        (List.map (mkEchoOutbound EchoRequest) ordered_neighbors))) in Hreply.
  rewrite Hstore in Hreply. cbn in Hreply.
  destruct (materialized_request_block_fields
      (next_message_id state) initiator ordered_neighbors reply Hreply)
    as [Hsender [Hkind Hreceiver]].
  congruence.
Qed.

Section RequestReplyReachability.

Hypothesis initiator_in_nodes : In initiator all_nodes.
Hypothesis adj_symmetric :
  forall left right, adj left right = true -> adj right left = true.

Theorem EchoStep_preserves_request_reply_reverse_distinct
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  echo_request_edges_unique state ->
  echo_message_ids_well_formed state ->
  echo_request_parent_distinct state ->
  echo_reply_receivers_discovered state ->
  echo_request_reply_reverse_distinct state ->
  EchoStep state event successor ->
  echo_request_reply_reverse_distinct successor.
Proof.
  intros Hunique Hids Hparent_distinct Hreply_receivers
    Hdistinct Hstep. destruct event.
  - now apply EchoStep_start_request_reply_reverse_distinct in Hstep.
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
    eapply apply_first_nonleaf_preserves_request_reply_reverse_distinct;
      eauto.
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
    eapply apply_request_reply_delivery_preserves_reverse_distinct; eauto.
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
    eapply apply_request_reply_delivery_preserves_reverse_distinct; eauto.
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
    eapply apply_request_reply_delivery_preserves_reverse_distinct; eauto.
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoParticipantReplyMore message parent) participant_ack_more_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action participant_ack_more_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_parent] in Haction.
    subst successor.
    now apply apply_empty_delivery_preserves_request_reply_reverse_distinct.
  - pose proof (@EchoStep_selected_guard_holds node node_eq config
      state successor (EchoParticipantReplyFinal message parent)
      participant_ack_final_rule
      (IRGuardParentEqual IRMessageReceiver (IRSomeParent IREventParent))
      Hstep eq_refl ltac:(
        cbn [participant_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hparent.
    cbn [guard_holds eval_node_expr eval_parent_expr event_message
      event_parent] in Hparent.
    pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoParticipantReplyFinal message parent) participant_ack_final_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action participant_ack_final_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_parent] in Haction.
    subst successor.
    eapply apply_parent_reply_delivery_preserves_reverse_distinct; eauto.
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorReplyMore message) initiator_ack_more_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_ack_more_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    now apply apply_empty_delivery_preserves_request_reply_reverse_distinct.
  - pose proof (@EchoStep_selected_action node node_eq config state successor
      (EchoInitiatorReplyFinal message) initiator_ack_final_rule
      Hstep eq_refl) as Haction.
    cbn [eval_action initiator_ack_final_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst successor.
    now apply apply_empty_delivery_preserves_request_reply_reverse_distinct.
Qed.

Lemma initial_executable_echo_state_request_reply_reverse_distinct :
  echo_request_reply_reverse_distinct initial_executable_echo_state.
Proof.
  intros request reply Hrequest. contradiction.
Qed.

Theorem echo_reachable_request_reply_reverse_distinct
    (state : @executable_echo_state node) :
  echo_reachable node_eq config state ->
  echo_request_reply_reverse_distinct state.
Proof.
  intro Hreachable.
  induction Hreachable as [| before event after Hbefore IH Hstep].
  - apply initial_executable_echo_state_request_reply_reverse_distinct.
  - eapply EchoStep_preserves_request_reply_reverse_distinct.
    + exact (echo_reachable_request_edges_unique before Hbefore).
    + exact (@echo_reachable_message_ids_well_formed node node_eq config
        before Hbefore).
    + exact (echo_reachable_request_parent_distinct before Hbefore).
    + exact (echo_reachable_reply_receivers_discovered
        initiator_in_nodes adj_symmetric before Hbefore).
    + exact IH.
    + exact Hstep.
Qed.

End RequestReplyReachability.

End EchoExecutableRequestAccounting.

Arguments request_edges_unique {node} _.
Arguments echo_request_edges_unique {node} _.
Arguments echo_request_parent_distinct {node} _.
Arguments echo_reply_receivers_discovered {node} _.
Arguments echo_request_reply_reverse_distinct {node} _.
