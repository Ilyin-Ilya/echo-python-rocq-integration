(** * Echo as data in the protocol-neutral typed IR

    The scheduler-facing event is only Start or Deliver(message-id).  The
    interpreter selects one of these nine rules from message kind, state, and
    certificate data; neither Python nor the scheduler chooses a branch. *)

From Stdlib Require Import List Bool Arith String.
Import ListNotations.
Open Scope string_scope.
Require Import ProtocolIRTypes ProtocolIRExpressions ProtocolIRActions
  ProtocolIRInterpreter ProtocolIRRunner EchoIRSignature.

Section EchoIRProgram.

Variable node : Type.

Definition echo_ir_bool (value : bool) :
    ir_expr node echo_ir_signature IRBool :=
  IRLiteral (IRBoolValue value).

Definition echo_ir_nat (value : nat) :
    ir_expr node echo_ir_signature IRNat :=
  IRLiteral (IRNatValue value).

Definition echo_ir_option_none :
    ir_expr node echo_ir_signature IROptionNode :=
  IRLiteral (IROptionNodeValue None).

Definition echo_ir_empty_nodes :
    ir_expr node echo_ir_signature IRListNode :=
  IRLiteral (IRListNodeValue []).

Definition echo_ir_initiator :
    ir_expr node echo_ir_signature IRNode :=
  @IRConfigRead node echo_ir_signature EchoIRInitiator.

Definition echo_ir_sender :
    ir_expr node echo_ir_signature IRNode := IRMessageSenderExpr.

Definition echo_ir_receiver :
    ir_expr node echo_ir_signature IRNode := IRMessageReceiverExpr.

Definition echo_ir_started :
    ir_expr node echo_ir_signature IRBool :=
  @IRGlobalRead node echo_ir_signature EchoIRStarted.

Definition echo_ir_parent
    (process : ir_expr node echo_ir_signature IRNode) :
    ir_expr node echo_ir_signature IROptionNode :=
  @IRLocalRead node echo_ir_signature EchoIRParent process.

Definition echo_ir_pending
    (process : ir_expr node echo_ir_signature IRNode) :
    ir_expr node echo_ir_signature IRListNode :=
  @IRLocalRead node echo_ir_signature EchoIRPending process.

Definition echo_ir_finished
    (process : ir_expr node echo_ir_signature IRNode) :
    ir_expr node echo_ir_signature IRBool :=
  @IRLocalRead node echo_ir_signature EchoIRFinished process.

Definition echo_ir_some
    (process : ir_expr node echo_ir_signature IRNode) :
    ir_expr node echo_ir_signature IROptionNode :=
  IROptionSomeExpr process.

Definition echo_ir_neighbors
    (process : ir_expr node echo_ir_signature IRNode) :
    ir_expr node echo_ir_signature IRListNode :=
  IRNeighborsExpr process.

Definition echo_ir_remove
    (selected : ir_expr node echo_ir_signature IRNode)
    (items : ir_expr node echo_ir_signature IRListNode) :
    ir_expr node echo_ir_signature IRListNode :=
  IRListRemoveExpr selected items.

Definition echo_ir_is_empty
    (items : ir_expr node echo_ir_signature IRListNode) :
    ir_expr node echo_ir_signature IRBool :=
  IRListIsEmptyExpr items.

Definition echo_ir_nonempty
    (items : ir_expr node echo_ir_signature IRListNode) :
    ir_expr node echo_ir_signature IRBool :=
  IRNotExpr (echo_ir_is_empty items).

Definition echo_ir_equal
    {kind : ir_type}
    (left right : ir_expr node echo_ir_signature kind) :
    ir_expr node echo_ir_signature IRBool :=
  IREqualExpr left right.

Definition echo_ir_not_equal
    {kind : ir_type}
    (left right : ir_expr node echo_ir_signature kind) :
    ir_expr node echo_ir_signature IRBool :=
  IRNotExpr (echo_ir_equal left right).

Definition echo_ir_start_order :
    ir_expr node echo_ir_signature IRListNode :=
  echo_ir_neighbors echo_ir_initiator.

Definition echo_ir_forward_order :
    ir_expr node echo_ir_signature IRListNode :=
  echo_ir_remove echo_ir_sender (echo_ir_neighbors echo_ir_receiver).

Definition echo_ir_expected_parent :
    ir_expr node echo_ir_signature IRNode :=
  IROptionGetExpr (echo_ir_parent echo_ir_receiver).

Definition echo_ir_process_initial
    (process : ir_expr node echo_ir_signature IRNode) :
    list (ir_expr node echo_ir_signature IRBool) :=
  [echo_ir_equal (echo_ir_parent process) echo_ir_option_none;
   echo_ir_equal (echo_ir_pending process) echo_ir_empty_nodes;
   echo_ir_equal (echo_ir_finished process) (echo_ir_bool false)].

Definition echo_ir_removed_pending
    (process : ir_expr node echo_ir_signature IRNode) :
    ir_expr node echo_ir_signature IRListNode :=
  echo_ir_remove echo_ir_sender (echo_ir_pending process).

Definition echo_ir_process_seen
    (process : ir_expr node echo_ir_signature IRNode) :
    ir_expr node echo_ir_signature IRBool :=
  IROrExpr
    (IROptionIsSomeExpr (echo_ir_parent process))
    (echo_ir_finished process).

Definition echo_ir_forward_targets :
    ir_expr node echo_ir_signature IRListNode :=
  echo_ir_remove echo_ir_sender (echo_ir_neighbors echo_ir_receiver).

Definition echo_ir_empty_payload :
    ir_payload_exprs node echo_ir_signature := [].

Fixpoint echo_ir_sequence
    (actions : list (ir_action node echo_ir_signature)) :
    ir_action node echo_ir_signature :=
  match actions with
  | [] => IRSkipAction
  | action :: rest => IRSequenceAction action (echo_ir_sequence rest)
  end.

Definition echo_ir_set_parent
    (process : ir_expr node echo_ir_signature IRNode)
    (value : ir_expr node echo_ir_signature IROptionNode) :
    ir_action node echo_ir_signature :=
  @IRSetLocalAction node echo_ir_signature process EchoIRParent value.

Definition echo_ir_set_pending
    (process : ir_expr node echo_ir_signature IRNode)
    (value : ir_expr node echo_ir_signature IRListNode) :
    ir_action node echo_ir_signature :=
  @IRSetLocalAction node echo_ir_signature process EchoIRPending value.

Definition echo_ir_set_finished
    (process : ir_expr node echo_ir_signature IRNode)
    (value : bool) : ir_action node echo_ir_signature :=
  @IRSetLocalAction node echo_ir_signature process EchoIRFinished
    (echo_ir_bool value).

Definition echo_ir_emit_one
    (kind : echo_ir_message_kind)
    (sender receiver : ir_expr node echo_ir_signature IRNode) :
    ir_action node echo_ir_signature :=
  @IREmitAction node echo_ir_signature kind sender receiver
    echo_ir_empty_payload.

Definition echo_ir_emit_many
    (kind : echo_ir_message_kind)
    (sender : ir_expr node echo_ir_signature IRNode)
    (receivers : ir_expr node echo_ir_signature IRListNode) :
    ir_action node echo_ir_signature :=
  @IREmitManyAction node echo_ir_signature kind sender receivers
    echo_ir_empty_payload.

Definition echo_ir_start_rule : ir_rule node echo_ir_signature :=
  @mkIRRule node echo_ir_signature EchoIRStartRule IRStartPattern
    [IRNotExpr echo_ir_started;
     @IRAllNodesLocalEqualExpr node echo_ir_signature
       EchoIRParent echo_ir_option_none;
     @IRAllNodesLocalEqualExpr node echo_ir_signature
       EchoIRPending echo_ir_empty_nodes;
     @IRAllNodesLocalEqualExpr node echo_ir_signature
       EchoIRFinished (echo_ir_bool false);
     IRMessageStoreEmptyExpr;
     echo_ir_equal IRNextMessageIdExpr (echo_ir_nat 1)]
    (echo_ir_sequence
      [echo_ir_set_parent echo_ir_initiator echo_ir_option_none;
       echo_ir_set_pending echo_ir_initiator echo_ir_start_order;
       echo_ir_set_finished echo_ir_initiator false;
       @IRSetGlobalAction node echo_ir_signature
         EchoIRStarted (echo_ir_bool true);
       echo_ir_emit_many EchoIRRequest echo_ir_initiator
         echo_ir_start_order]).

Definition echo_ir_first_request_nonleaf_rule :
    ir_rule node echo_ir_signature :=
  @mkIRRule node echo_ir_signature EchoIRFirstRequestNonLeafRule
    (@IRDeliveryPattern echo_ir_signature EchoIRRequest)
    ([echo_ir_not_equal echo_ir_receiver echo_ir_initiator] ++
      echo_ir_process_initial echo_ir_receiver ++
      [IRNotExpr (echo_ir_process_seen echo_ir_receiver);
       echo_ir_nonempty echo_ir_forward_targets])
    (echo_ir_sequence
      [echo_ir_set_parent echo_ir_receiver (echo_ir_some echo_ir_sender);
       echo_ir_set_pending echo_ir_receiver echo_ir_forward_order;
       echo_ir_set_finished echo_ir_receiver false;
       IRRemoveSelectedMessageAction;
       echo_ir_emit_many EchoIRRequest echo_ir_receiver
         echo_ir_forward_order]).

Definition echo_ir_first_request_leaf_rule :
    ir_rule node echo_ir_signature :=
  @mkIRRule node echo_ir_signature EchoIRFirstRequestLeafRule
    (@IRDeliveryPattern echo_ir_signature EchoIRRequest)
    ([echo_ir_not_equal echo_ir_receiver echo_ir_initiator] ++
      echo_ir_process_initial echo_ir_receiver ++
      [IRNotExpr (echo_ir_process_seen echo_ir_receiver);
       echo_ir_is_empty echo_ir_forward_targets])
    (echo_ir_sequence
      [echo_ir_set_parent echo_ir_receiver (echo_ir_some echo_ir_sender);
       echo_ir_set_pending echo_ir_receiver echo_ir_empty_nodes;
       echo_ir_set_finished echo_ir_receiver true;
       IRRemoveSelectedMessageAction;
       echo_ir_emit_one EchoIRReply echo_ir_receiver echo_ir_sender]).

Definition echo_ir_repeated_request_rule :
    ir_rule node echo_ir_signature :=
  @mkIRRule node echo_ir_signature EchoIRRepeatedRequestRule
    (@IRDeliveryPattern echo_ir_signature EchoIRRequest)
    [echo_ir_not_equal echo_ir_receiver echo_ir_initiator;
     echo_ir_process_seen echo_ir_receiver]
    (echo_ir_sequence
      [IRRemoveSelectedMessageAction;
       echo_ir_emit_one EchoIRReply echo_ir_receiver echo_ir_sender]).

Definition echo_ir_initiator_request_rule :
    ir_rule node echo_ir_signature :=
  @mkIRRule node echo_ir_signature EchoIRInitiatorRequestRule
    (@IRDeliveryPattern echo_ir_signature EchoIRRequest)
    [echo_ir_equal echo_ir_receiver echo_ir_initiator;
     echo_ir_started;
     echo_ir_equal (echo_ir_finished echo_ir_initiator)
       (echo_ir_bool false)]
    (echo_ir_sequence
      [IRRemoveSelectedMessageAction;
       echo_ir_emit_one EchoIRReply echo_ir_initiator echo_ir_sender]).

Definition echo_ir_participant_reply_more_rule :
    ir_rule node echo_ir_signature :=
  @mkIRRule node echo_ir_signature EchoIRParticipantReplyMoreRule
    (@IRDeliveryPattern echo_ir_signature EchoIRReply)
    [echo_ir_not_equal echo_ir_receiver echo_ir_initiator;
     IROptionIsSomeExpr (echo_ir_parent echo_ir_receiver);
     IRListContainsExpr echo_ir_sender
       (echo_ir_pending echo_ir_receiver);
     echo_ir_nonempty (echo_ir_removed_pending echo_ir_receiver);
     echo_ir_equal (echo_ir_finished echo_ir_receiver)
       (echo_ir_bool false)]
    (echo_ir_sequence
      [echo_ir_set_parent echo_ir_receiver
         (echo_ir_some echo_ir_expected_parent);
       echo_ir_set_pending echo_ir_receiver
         (echo_ir_removed_pending echo_ir_receiver);
       echo_ir_set_finished echo_ir_receiver false;
       IRRemoveSelectedMessageAction]).

Definition echo_ir_participant_reply_final_rule :
    ir_rule node echo_ir_signature :=
  @mkIRRule node echo_ir_signature EchoIRParticipantReplyFinalRule
    (@IRDeliveryPattern echo_ir_signature EchoIRReply)
    [echo_ir_not_equal echo_ir_receiver echo_ir_initiator;
     IROptionIsSomeExpr (echo_ir_parent echo_ir_receiver);
     IRListContainsExpr echo_ir_sender
       (echo_ir_pending echo_ir_receiver);
     echo_ir_is_empty (echo_ir_removed_pending echo_ir_receiver);
     echo_ir_equal (echo_ir_finished echo_ir_receiver)
       (echo_ir_bool false)]
    (echo_ir_sequence
      [echo_ir_set_parent echo_ir_receiver
         (echo_ir_some echo_ir_expected_parent);
       echo_ir_set_pending echo_ir_receiver echo_ir_empty_nodes;
       echo_ir_set_finished echo_ir_receiver true;
       IRRemoveSelectedMessageAction;
       echo_ir_emit_one EchoIRReply echo_ir_receiver
         echo_ir_expected_parent]).

Definition echo_ir_initiator_reply_more_rule :
    ir_rule node echo_ir_signature :=
  @mkIRRule node echo_ir_signature EchoIRInitiatorReplyMoreRule
    (@IRDeliveryPattern echo_ir_signature EchoIRReply)
    [echo_ir_equal echo_ir_receiver echo_ir_initiator;
     echo_ir_started;
     echo_ir_equal (echo_ir_parent echo_ir_initiator)
       echo_ir_option_none;
     IRListContainsExpr echo_ir_sender
       (echo_ir_pending echo_ir_initiator);
     echo_ir_nonempty (echo_ir_removed_pending echo_ir_initiator);
     echo_ir_equal (echo_ir_finished echo_ir_initiator)
       (echo_ir_bool false)]
    (echo_ir_sequence
      [echo_ir_set_parent echo_ir_initiator echo_ir_option_none;
       echo_ir_set_pending echo_ir_initiator
         (echo_ir_removed_pending echo_ir_initiator);
       echo_ir_set_finished echo_ir_initiator false;
       IRRemoveSelectedMessageAction]).

Definition echo_ir_initiator_reply_final_rule :
    ir_rule node echo_ir_signature :=
  @mkIRRule node echo_ir_signature EchoIRInitiatorReplyFinalRule
    (@IRDeliveryPattern echo_ir_signature EchoIRReply)
    [echo_ir_equal echo_ir_receiver echo_ir_initiator;
     echo_ir_started;
     echo_ir_equal (echo_ir_parent echo_ir_initiator)
       echo_ir_option_none;
     IRListContainsExpr echo_ir_sender
       (echo_ir_pending echo_ir_initiator);
     echo_ir_is_empty (echo_ir_removed_pending echo_ir_initiator);
     echo_ir_equal (echo_ir_finished echo_ir_initiator)
       (echo_ir_bool false)]
    (echo_ir_sequence
      [echo_ir_set_parent echo_ir_initiator echo_ir_option_none;
       echo_ir_set_pending echo_ir_initiator echo_ir_empty_nodes;
       echo_ir_set_finished echo_ir_initiator true;
       IRRemoveSelectedMessageAction]).

Definition echo_ir_rules : list (ir_rule node echo_ir_signature) :=
  [echo_ir_start_rule;
   echo_ir_first_request_nonleaf_rule;
   echo_ir_first_request_leaf_rule;
   echo_ir_repeated_request_rule;
   echo_ir_initiator_request_rule;
   echo_ir_participant_reply_more_rule;
   echo_ir_participant_reply_final_rule;
   echo_ir_initiator_reply_more_rule;
   echo_ir_initiator_reply_final_rule].

Definition echo_ir_initial_local : ir_local_store node echo_ir_signature :=
  fun field =>
    match field as selected
      return ir_value node
        (signature_local_field_type echo_ir_signature selected) with
    | EchoIRParent => IROptionNodeValue None
    | EchoIRPending => IRListNodeValue []
    | EchoIRFinished => IRBoolValue false
    end.

Definition echo_ir_initial_global : ir_global_store node echo_ir_signature :=
  fun field =>
    match field as selected
      return ir_value node
        (signature_global_field_type echo_ir_signature selected) with
    | EchoIRStarted => IRBoolValue false
    end.

Definition echo_ir_complete_expr :
    ir_expr node echo_ir_signature IRBool :=
  IRAndExpr echo_ir_started
    (IRAndExpr
      (echo_ir_is_empty (echo_ir_pending echo_ir_initiator))
      (IRAndExpr IRMessageStoreEmptyExpr
        (IROrExpr (echo_ir_finished echo_ir_initiator)
          (echo_ir_is_empty (echo_ir_neighbors echo_ir_initiator))))).

Definition echo_ir_stuck_expr :
    ir_expr node echo_ir_signature IRBool :=
  IRAndExpr echo_ir_started IRMessageStoreEmptyExpr.

Definition echo_ir_program :
    ir_protocol_program node echo_ir_signature :=
  mkIRProtocolProgram
    1 1 "echo"
    echo_ir_initial_local
    echo_ir_initial_global
    1
    echo_ir_rules
    echo_ir_complete_expr
    echo_ir_stuck_expr.

End EchoIRProgram.

Arguments echo_ir_program {node}.
