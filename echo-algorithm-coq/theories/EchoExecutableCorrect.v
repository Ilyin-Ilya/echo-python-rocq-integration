(** * Soundness of the canonical executable Rocq Echo transition

    A successful canonical [EchoStep] is simulated by exactly one transition
    of the original abstract Echo model, and the successor states remain in
    the established refinement relation.  The proof reads the nine canonical
    guards and actions directly; it does not pass through a second transition
    relation, replay function, or validity predicate. *)

From Stdlib Require Import List.
Require Import EchoAlgorithm EchoExecutableTypes EchoTransitionIR
  EchoExecutableReachability EchoExecutableAbstraction
  EchoExecutableRefinement.

Section EchoExecutableCorrect.

Variable node : Type.
Variable node_eq : forall (n m : node), {n = m} + {n <> m}.

Definition executable_start_ready
    (initiator : node)
    (s : @executable_echo_state node) (event : @echo_event node) : Prop :=
  match event with
  | EchoStart _ => @concrete_start_ready node initiator s
  | _ => True
  end.

Theorem echo_step_sound
    (initiator : node) (all_nodes : list node) (adj : node -> node -> bool) :
  (forall n, NoDup (nbrs all_nodes adj n)) ->
  forall (s s' : @executable_echo_state node)
         (event : @echo_event node)
         (rq : @echo_state node),
    executable_start_ready initiator s event ->
    @EchoStep node node_eq
      (mkEchoConfig initiator all_nodes adj) s event s' ->
    @ExecutableStateRefines node node_eq initiator all_nodes adj s rq ->
    exists rq' label,
      @echo_step node node_eq initiator all_nodes adj rq label rq' /\
      @ExecutableStateRefines node node_eq initiator all_nodes adj s' rq'.
Proof.
  intros Hneighbors s s' event rq Hstart_ready Hstep Hrefines.
  destruct event as
      [ordered_neighbors
      | message ordered_forwards
      | message
      | message
      | message
      | message parent
      | message parent
      | message
      | message].
  - pose proof (@EchoStep_start_guards node node_eq
      (mkEchoConfig initiator all_nodes adj)
      s s' ordered_neighbors Hstep) as [Hinitial Horder].
    pose proof (@EchoStep_selected_action node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoStart ordered_neighbors) start_rule Hstep eq_refl) as Haction.
    cbn [eval_action start_rule ir_rule_action eval_nodes_expr] in Haction.
    subst s'.
    destruct (@executable_start_step_sound node node_eq initiator all_nodes adj
      s ordered_neighbors rq Hstart_ready Horder (Hneighbors initiator)
      Hrefines) as [rq' [Habstract Hrefines']].
    exists rq', ELStart. now split.
  - destruct message as [message_id kind sender receiver].
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoFirstRequestNonLeaf
        (mkEchoMessage message_id kind sender receiver) ordered_forwards)
      first_echo_nonleaf_rule (IRGuardKind EchoRequest)
      Hstep eq_refl ltac:(left; reflexivity)) as Hkind.
    cbn [guard_holds event_message] in Hkind.
    destruct kind; try discriminate.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoFirstRequestNonLeaf
        (mkEchoMessage message_id EchoRequest sender receiver)
        ordered_forwards)
      first_echo_nonleaf_rule
      (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [first_echo_nonleaf_rule];
        repeat (first [left; reflexivity | right]))) as Hnotroot.
    cbn [guard_holds eval_node_expr event_message] in Hnotroot.
    pose proof (@EchoStep_delivery_message_queued node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoFirstRequestNonLeaf
        (mkEchoMessage message_id EchoRequest sender receiver)
        ordered_forwards) Hstep I) as Hin.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoFirstRequestNonLeaf
        (mkEchoMessage message_id EchoRequest sender receiver)
        ordered_forwards)
      first_echo_nonleaf_rule (IRGuardProcessInitial IRMessageReceiver)
      Hstep eq_refl ltac:(
        cbn [first_echo_nonleaf_rule];
        repeat (first [left; reflexivity | right]))) as Hinitial.
    cbn [guard_holds eval_node_expr event_message] in Hinitial.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoFirstRequestNonLeaf
        (mkEchoMessage message_id EchoRequest sender receiver)
        ordered_forwards)
      first_echo_nonleaf_rule
      (IRGuardPermutation IRNodesOrdered
        (IRNodesRemove IRMessageSender (IRNodesNeighbors IRMessageReceiver)))
      Hstep eq_refl ltac:(
        cbn [first_echo_nonleaf_rule];
        repeat (first [left; reflexivity | right]))) as Horder.
    cbn [guard_holds eval_node_expr eval_nodes_expr event_message
      event_ordered_nodes] in Horder.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoFirstRequestNonLeaf
        (mkEchoMessage message_id EchoRequest sender receiver)
        ordered_forwards)
      first_echo_nonleaf_rule (IRGuardNodesNonempty IRNodesOrdered)
      Hstep eq_refl ltac:(
        cbn [first_echo_nonleaf_rule];
        repeat (first [left; reflexivity | right]))) as Hnonempty.
    cbn [guard_holds eval_nodes_expr event_ordered_nodes] in Hnonempty.
    pose proof (@EchoStep_selected_action node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoFirstRequestNonLeaf
        (mkEchoMessage message_id EchoRequest sender receiver)
        ordered_forwards)
      first_echo_nonleaf_rule Hstep eq_refl) as Haction.
    cbn [eval_action first_echo_nonleaf_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_ordered_nodes] in Haction.
    subst s'.
    destruct (@executable_first_echo_nonleaf_step_sound node node_eq
      initiator all_nodes adj s message_id sender receiver ordered_forwards rq
      Hnotroot Hin Hinitial Horder Hnonempty (Hneighbors receiver) Hrefines)
      as [rq' [Habstract Hrefines']].
    exists rq', (ELDeliver (mkPkt sender receiver Token)). now split.
  - destruct message as [message_id kind sender receiver].
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoFirstRequestLeaf (mkEchoMessage message_id kind sender receiver))
      first_echo_leaf_rule (IRGuardKind EchoRequest)
      Hstep eq_refl ltac:(left; reflexivity)) as Hkind.
    cbn [guard_holds event_message] in Hkind.
    destruct kind; try discriminate.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoFirstRequestLeaf
        (mkEchoMessage message_id EchoRequest sender receiver))
      first_echo_leaf_rule
      (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [first_echo_leaf_rule];
        repeat (first [left; reflexivity | right]))) as Hnotroot.
    cbn [guard_holds eval_node_expr event_message] in Hnotroot.
    pose proof (@EchoStep_delivery_message_queued node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoFirstRequestLeaf
        (mkEchoMessage message_id EchoRequest sender receiver)) Hstep I) as Hin.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoFirstRequestLeaf
        (mkEchoMessage message_id EchoRequest sender receiver))
      first_echo_leaf_rule (IRGuardProcessInitial IRMessageReceiver)
      Hstep eq_refl ltac:(
        cbn [first_echo_leaf_rule];
        repeat (first [left; reflexivity | right]))) as Hinitial.
    cbn [guard_holds eval_node_expr event_message] in Hinitial.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoFirstRequestLeaf
        (mkEchoMessage message_id EchoRequest sender receiver))
      first_echo_leaf_rule
      (IRGuardNodesEmpty
        (IRNodesRemove IRMessageSender (IRNodesNeighbors IRMessageReceiver)))
      Hstep eq_refl ltac:(
        cbn [first_echo_leaf_rule];
        repeat (first [left; reflexivity | right]))) as Hleaf.
    cbn [guard_holds eval_node_expr eval_nodes_expr event_message] in Hleaf.
    pose proof (@EchoStep_selected_action node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoFirstRequestLeaf
        (mkEchoMessage message_id EchoRequest sender receiver))
      first_echo_leaf_rule Hstep eq_refl) as Haction.
    cbn [eval_action first_echo_leaf_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst s'.
    destruct (@executable_first_echo_leaf_step_sound node node_eq
      initiator all_nodes adj s message_id sender receiver rq
      Hnotroot Hin Hinitial Hleaf (Hneighbors receiver) Hrefines)
      as [rq' [Habstract Hrefines']].
    exists rq', (ELDeliver (mkPkt sender receiver Token)). now split.
  - destruct message as [message_id kind sender receiver].
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoRepeatedRequest (mkEchoMessage message_id kind sender receiver))
      repeated_echo_rule (IRGuardKind EchoRequest)
      Hstep eq_refl ltac:(left; reflexivity)) as Hkind.
    cbn [guard_holds event_message] in Hkind.
    destruct kind; try discriminate.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoRepeatedRequest
        (mkEchoMessage message_id EchoRequest sender receiver))
      repeated_echo_rule
      (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [repeated_echo_rule];
        repeat (first [left; reflexivity | right]))) as Hnotroot.
    cbn [guard_holds eval_node_expr event_message] in Hnotroot.
    pose proof (@EchoStep_delivery_message_queued node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoRepeatedRequest
        (mkEchoMessage message_id EchoRequest sender receiver)) Hstep I) as Hin.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoRepeatedRequest
        (mkEchoMessage message_id EchoRequest sender receiver))
      repeated_echo_rule (IRGuardHasParentOrFinished IRMessageReceiver)
      Hstep eq_refl ltac:(
        cbn [repeated_echo_rule];
        repeat (first [left; reflexivity | right]))) as Hreached.
    cbn [guard_holds eval_node_expr event_message] in Hreached.
    pose proof (@EchoStep_selected_action node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoRepeatedRequest
        (mkEchoMessage message_id EchoRequest sender receiver))
      repeated_echo_rule Hstep eq_refl) as Haction.
    cbn [eval_action repeated_echo_rule ir_rule_action
      eval_process_expr eval_node_expr eval_outbound_expr event_message]
      in Haction.
    subst s'.
    destruct (@executable_repeated_echo_step_sound node node_eq initiator all_nodes adj
      s message_id sender receiver rq Hnotroot Hin Hreached Hrefines)
      as [rq' [Habstract Hrefines']].
    exists rq', (ELDeliver (mkPkt sender receiver Token)). now split.
  - destruct message as [message_id kind sender receiver].
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorRequest (mkEchoMessage message_id kind sender receiver))
      initiator_echo_rule (IRGuardKind EchoRequest)
      Hstep eq_refl ltac:(left; reflexivity)) as Hkind.
    cbn [guard_holds event_message] in Hkind.
    destruct kind; try discriminate.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorRequest
        (mkEchoMessage message_id EchoRequest sender receiver))
      initiator_echo_rule
      (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [initiator_echo_rule];
        repeat (first [left; reflexivity | right]))) as Hreceiver.
    cbn [guard_holds eval_node_expr event_message] in Hreceiver.
    change (receiver = initiator) in Hreceiver.
    subst receiver.
    pose proof (@EchoStep_delivery_message_queued node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorRequest
        (mkEchoMessage message_id EchoRequest sender initiator)) Hstep I) as Hin.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorRequest
        (mkEchoMessage message_id EchoRequest sender initiator))
      initiator_echo_rule (IRGuardStarted true)
      Hstep eq_refl ltac:(
        cbn [initiator_echo_rule];
        repeat (first [left; reflexivity | right]))) as Hstarted.
    cbn [guard_holds] in Hstarted.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorRequest
        (mkEchoMessage message_id EchoRequest sender initiator))
      initiator_echo_rule (IRGuardFinished IRInitiatorNode false)
      Hstep eq_refl ltac:(
        cbn [initiator_echo_rule];
        repeat (first [left; reflexivity | right]))) as Hunfinished.
    cbn [guard_holds eval_node_expr] in Hunfinished.
    pose proof (@EchoStep_selected_action node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorRequest
        (mkEchoMessage message_id EchoRequest sender initiator))
      initiator_echo_rule Hstep eq_refl) as Haction.
    cbn [eval_action initiator_echo_rule ir_rule_action
      eval_process_expr eval_node_expr eval_outbound_expr event_message]
      in Haction.
    subst s'.
    destruct (@executable_initiator_echo_step_sound node node_eq initiator all_nodes adj
      s message_id sender rq Hstarted Hunfinished Hin Hrefines)
      as [rq' [Habstract Hrefines']].
    exists rq', (ELDeliver (mkPkt sender initiator Token)). now split.
  - destruct message as [message_id kind sender receiver].
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoParticipantReplyMore
        (mkEchoMessage message_id kind sender receiver) parent)
      participant_ack_more_rule (IRGuardKind EchoReply)
      Hstep eq_refl ltac:(left; reflexivity)) as Hkind.
    cbn [guard_holds event_message] in Hkind.
    destruct kind; try discriminate.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoParticipantReplyMore
        (mkEchoMessage message_id EchoReply sender receiver) parent)
      participant_ack_more_rule
      (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [participant_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hnotroot.
    cbn [guard_holds eval_node_expr event_message] in Hnotroot.
    pose proof (@EchoStep_delivery_message_queued node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoParticipantReplyMore
        (mkEchoMessage message_id EchoReply sender receiver) parent)
      Hstep I) as Hin.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoParticipantReplyMore
        (mkEchoMessage message_id EchoReply sender receiver) parent)
      participant_ack_more_rule
      (IRGuardParentEqual IRMessageReceiver (IRSomeParent IREventParent))
      Hstep eq_refl ltac:(
        cbn [participant_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hparent.
    cbn [guard_holds eval_node_expr eval_parent_expr event_message
      event_parent] in Hparent.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoParticipantReplyMore
        (mkEchoMessage message_id EchoReply sender receiver) parent)
      participant_ack_more_rule
      (IRGuardNodeIn IRMessageSender (IRNodesPending IRMessageReceiver))
      Hstep eq_refl ltac:(
        cbn [participant_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hsender.
    cbn [guard_holds eval_node_expr eval_nodes_expr event_message] in Hsender.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoParticipantReplyMore
        (mkEchoMessage message_id EchoReply sender receiver) parent)
      participant_ack_more_rule
      (IRGuardNodesNonempty
        (IRNodesRemove IRMessageSender (IRNodesPending IRMessageReceiver)))
      Hstep eq_refl ltac:(
        cbn [participant_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hmore.
    cbn [guard_holds eval_node_expr eval_nodes_expr event_message] in Hmore.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoParticipantReplyMore
        (mkEchoMessage message_id EchoReply sender receiver) parent)
      participant_ack_more_rule (IRGuardFinished IRMessageReceiver false)
      Hstep eq_refl ltac:(
        cbn [participant_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hunfinished.
    cbn [guard_holds eval_node_expr event_message] in Hunfinished.
    pose proof (@EchoStep_selected_action node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoParticipantReplyMore
        (mkEchoMessage message_id EchoReply sender receiver) parent)
      participant_ack_more_rule Hstep eq_refl) as Haction.
    cbn [eval_action participant_ack_more_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_parent] in Haction.
    subst s'.
    destruct (@executable_participant_ack_more_step_sound node node_eq
      initiator all_nodes adj s message_id sender receiver parent rq
      Hnotroot Hin Hparent Hsender Hmore Hunfinished
      (Hneighbors receiver) Hrefines) as [rq' [Habstract Hrefines']].
    exists rq', (ELDeliver (mkPkt sender receiver Echo)). now split.
  - destruct message as [message_id kind sender receiver].
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoParticipantReplyFinal
        (mkEchoMessage message_id kind sender receiver) parent)
      participant_ack_final_rule (IRGuardKind EchoReply)
      Hstep eq_refl ltac:(left; reflexivity)) as Hkind.
    cbn [guard_holds event_message] in Hkind.
    destruct kind; try discriminate.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoParticipantReplyFinal
        (mkEchoMessage message_id EchoReply sender receiver) parent)
      participant_ack_final_rule
      (IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [participant_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hnotroot.
    cbn [guard_holds eval_node_expr event_message] in Hnotroot.
    pose proof (@EchoStep_delivery_message_queued node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoParticipantReplyFinal
        (mkEchoMessage message_id EchoReply sender receiver) parent)
      Hstep I) as Hin.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoParticipantReplyFinal
        (mkEchoMessage message_id EchoReply sender receiver) parent)
      participant_ack_final_rule
      (IRGuardParentEqual IRMessageReceiver (IRSomeParent IREventParent))
      Hstep eq_refl ltac:(
        cbn [participant_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hparent.
    cbn [guard_holds eval_node_expr eval_parent_expr event_message
      event_parent] in Hparent.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoParticipantReplyFinal
        (mkEchoMessage message_id EchoReply sender receiver) parent)
      participant_ack_final_rule
      (IRGuardNodeIn IRMessageSender (IRNodesPending IRMessageReceiver))
      Hstep eq_refl ltac:(
        cbn [participant_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hsender.
    cbn [guard_holds eval_node_expr eval_nodes_expr event_message] in Hsender.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoParticipantReplyFinal
        (mkEchoMessage message_id EchoReply sender receiver) parent)
      participant_ack_final_rule
      (IRGuardNodesEmpty
        (IRNodesRemove IRMessageSender (IRNodesPending IRMessageReceiver)))
      Hstep eq_refl ltac:(
        cbn [participant_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hfinal.
    cbn [guard_holds eval_node_expr eval_nodes_expr event_message] in Hfinal.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoParticipantReplyFinal
        (mkEchoMessage message_id EchoReply sender receiver) parent)
      participant_ack_final_rule (IRGuardFinished IRMessageReceiver false)
      Hstep eq_refl ltac:(
        cbn [participant_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hunfinished.
    cbn [guard_holds eval_node_expr event_message] in Hunfinished.
    pose proof (@EchoStep_selected_action node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoParticipantReplyFinal
        (mkEchoMessage message_id EchoReply sender receiver) parent)
      participant_ack_final_rule Hstep eq_refl) as Haction.
    cbn [eval_action participant_ack_final_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message event_parent] in Haction.
    subst s'.
    destruct (@executable_participant_ack_final_step_sound node node_eq
      initiator all_nodes adj s message_id sender receiver parent rq
      Hnotroot Hin Hparent Hsender Hfinal Hunfinished
      (Hneighbors receiver) Hrefines) as [rq' [Habstract Hrefines']].
    exists rq', (ELDeliver (mkPkt sender receiver Echo)). now split.
  - destruct message as [message_id kind sender receiver].
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorReplyMore
        (mkEchoMessage message_id kind sender receiver))
      initiator_ack_more_rule (IRGuardKind EchoReply)
      Hstep eq_refl ltac:(left; reflexivity)) as Hkind.
    cbn [guard_holds event_message] in Hkind.
    destruct kind; try discriminate.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorReplyMore
        (mkEchoMessage message_id EchoReply sender receiver))
      initiator_ack_more_rule
      (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [initiator_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hreceiver.
    cbn [guard_holds eval_node_expr event_message] in Hreceiver.
    change (receiver = initiator) in Hreceiver.
    subst receiver.
    pose proof (@EchoStep_delivery_message_queued node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorReplyMore
        (mkEchoMessage message_id EchoReply sender initiator)) Hstep I) as Hin.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorReplyMore
        (mkEchoMessage message_id EchoReply sender initiator))
      initiator_ack_more_rule (IRGuardStarted true)
      Hstep eq_refl ltac:(
        cbn [initiator_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hstarted.
    cbn [guard_holds] in Hstarted.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorReplyMore
        (mkEchoMessage message_id EchoReply sender initiator))
      initiator_ack_more_rule
      (IRGuardParentEqual IRInitiatorNode IRNoParent)
      Hstep eq_refl ltac:(
        cbn [initiator_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hroot_parent.
    cbn [guard_holds eval_node_expr eval_parent_expr] in Hroot_parent.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorReplyMore
        (mkEchoMessage message_id EchoReply sender initiator))
      initiator_ack_more_rule
      (IRGuardNodeIn IRMessageSender (IRNodesPending IRInitiatorNode))
      Hstep eq_refl ltac:(
        cbn [initiator_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hsender.
    cbn [guard_holds eval_node_expr eval_nodes_expr event_message] in Hsender.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorReplyMore
        (mkEchoMessage message_id EchoReply sender initiator))
      initiator_ack_more_rule
      (IRGuardNodesNonempty
        (IRNodesRemove IRMessageSender (IRNodesPending IRInitiatorNode)))
      Hstep eq_refl ltac:(
        cbn [initiator_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hmore.
    cbn [guard_holds eval_node_expr eval_nodes_expr event_message] in Hmore.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorReplyMore
        (mkEchoMessage message_id EchoReply sender initiator))
      initiator_ack_more_rule (IRGuardFinished IRInitiatorNode false)
      Hstep eq_refl ltac:(
        cbn [initiator_ack_more_rule];
        repeat (first [left; reflexivity | right]))) as Hunfinished.
    cbn [guard_holds eval_node_expr] in Hunfinished.
    pose proof (@EchoStep_selected_action node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorReplyMore
        (mkEchoMessage message_id EchoReply sender initiator))
      initiator_ack_more_rule Hstep eq_refl) as Haction.
    cbn [eval_action initiator_ack_more_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst s'.
    destruct (@executable_initiator_ack_more_step_sound node node_eq
      initiator all_nodes adj s message_id sender rq
      Hstarted Hroot_parent Hin Hsender Hmore Hunfinished
      (Hneighbors initiator) Hrefines) as [rq' [Habstract Hrefines']].
    exists rq', (ELDeliver (mkPkt sender initiator Echo)). now split.
  - destruct message as [message_id kind sender receiver].
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorReplyFinal
        (mkEchoMessage message_id kind sender receiver))
      initiator_ack_final_rule (IRGuardKind EchoReply)
      Hstep eq_refl ltac:(left; reflexivity)) as Hkind.
    cbn [guard_holds event_message] in Hkind.
    destruct kind; try discriminate.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorReplyFinal
        (mkEchoMessage message_id EchoReply sender receiver))
      initiator_ack_final_rule
      (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
      Hstep eq_refl ltac:(
        cbn [initiator_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hreceiver.
    cbn [guard_holds eval_node_expr event_message] in Hreceiver.
    change (receiver = initiator) in Hreceiver.
    subst receiver.
    pose proof (@EchoStep_delivery_message_queued node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorReplyFinal
        (mkEchoMessage message_id EchoReply sender initiator)) Hstep I) as Hin.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorReplyFinal
        (mkEchoMessage message_id EchoReply sender initiator))
      initiator_ack_final_rule (IRGuardStarted true)
      Hstep eq_refl ltac:(
        cbn [initiator_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hstarted.
    cbn [guard_holds] in Hstarted.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorReplyFinal
        (mkEchoMessage message_id EchoReply sender initiator))
      initiator_ack_final_rule
      (IRGuardParentEqual IRInitiatorNode IRNoParent)
      Hstep eq_refl ltac:(
        cbn [initiator_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hroot_parent.
    cbn [guard_holds eval_node_expr eval_parent_expr] in Hroot_parent.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorReplyFinal
        (mkEchoMessage message_id EchoReply sender initiator))
      initiator_ack_final_rule
      (IRGuardNodeIn IRMessageSender (IRNodesPending IRInitiatorNode))
      Hstep eq_refl ltac:(
        cbn [initiator_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hsender.
    cbn [guard_holds eval_node_expr eval_nodes_expr event_message] in Hsender.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorReplyFinal
        (mkEchoMessage message_id EchoReply sender initiator))
      initiator_ack_final_rule
      (IRGuardNodesEmpty
        (IRNodesRemove IRMessageSender (IRNodesPending IRInitiatorNode)))
      Hstep eq_refl ltac:(
        cbn [initiator_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hfinal.
    cbn [guard_holds eval_node_expr eval_nodes_expr event_message] in Hfinal.
    pose proof (@EchoStep_selected_guard_holds node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorReplyFinal
        (mkEchoMessage message_id EchoReply sender initiator))
      initiator_ack_final_rule (IRGuardFinished IRInitiatorNode false)
      Hstep eq_refl ltac:(
        cbn [initiator_ack_final_rule];
        repeat (first [left; reflexivity | right]))) as Hunfinished.
    cbn [guard_holds eval_node_expr] in Hunfinished.
    pose proof (@EchoStep_selected_action node node_eq
      (mkEchoConfig initiator all_nodes adj) s s'
      (EchoInitiatorReplyFinal
        (mkEchoMessage message_id EchoReply sender initiator))
      initiator_ack_final_rule Hstep eq_refl) as Haction.
    cbn [eval_action initiator_ack_final_rule ir_rule_action
      eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
      eval_outbound_expr event_message] in Haction.
    subst s'.
    destruct (@executable_initiator_ack_final_step_sound node node_eq
      initiator all_nodes adj s message_id sender rq
      Hstarted Hroot_parent Hin Hsender Hfinal Hunfinished
      (Hneighbors initiator) Hrefines) as [rq' [Habstract Hrefines']].
    exists rq', (ELDeliver (mkPkt sender initiator Echo)). now split.
Qed.

End EchoExecutableCorrect.
