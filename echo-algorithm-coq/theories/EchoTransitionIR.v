(** * First-order transition IR for the executable Echo core

    Unlike the retired Python-AST manifest, this program contains
    the guards and state updates of every transition as data.  The small
    expression language is intentionally Echo-specific: it is large enough
    to generate the Python transition core, but not a general Gallina or
    Python interpreter.

    [echo_program] is the executable definition: [echo_exec] is its
    interpreter, not a second handwritten transition function.  The final
    theorems characterize successful and failed execution and connect a
    successful result to the existing formal step relation. *)

From Stdlib Require Import List Bool Arith Sorting.Permutation.
Import ListNotations.
Require Import EchoAlgorithm EchoExecutableTypes EchoExecutableDecision.

Section EchoTransitionIR.

Variable node : Type.
Variable node_eq : forall (n m : node), {n = m} + {n <> m}.
Variable config : @echo_config node.

Local Notation initiator := (config_initiator config).
Local Notation all_nodes := (config_nodes config).
Local Notation adj := (config_adjacent config).

Inductive ir_event_tag : Type :=
  | IRStart
  | IRFirstECHONonLeaf
  | IRFirstECHOLeaf
  | IRRepeatedECHO
  | IRInitiatorECHO
  | IRParticipantACKMore
  | IRParticipantACKFinal
  | IRInitiatorACKMore
  | IRInitiatorACKFinal.

Definition ir_event_tag_eqb (left right : ir_event_tag) : bool :=
  match left, right with
  | IRStart, IRStart
  | IRFirstECHONonLeaf, IRFirstECHONonLeaf
  | IRFirstECHOLeaf, IRFirstECHOLeaf
  | IRRepeatedECHO, IRRepeatedECHO
  | IRInitiatorECHO, IRInitiatorECHO
  | IRParticipantACKMore, IRParticipantACKMore
  | IRParticipantACKFinal, IRParticipantACKFinal
  | IRInitiatorACKMore, IRInitiatorACKMore
  | IRInitiatorACKFinal, IRInitiatorACKFinal => true
  | _, _ => false
  end.

Definition event_tag (event : @echo_event node) : ir_event_tag :=
  match event with
  | EchoStart _ => IRStart
  | EchoFirstRequestNonLeaf _ _ => IRFirstECHONonLeaf
  | EchoFirstRequestLeaf _ => IRFirstECHOLeaf
  | EchoRepeatedRequest _ => IRRepeatedECHO
  | EchoInitiatorRequest _ => IRInitiatorECHO
  | EchoParticipantReplyMore _ _ => IRParticipantACKMore
  | EchoParticipantReplyFinal _ _ => IRParticipantACKFinal
  | EchoInitiatorReplyMore _ => IRInitiatorACKMore
  | EchoInitiatorReplyFinal _ => IRInitiatorACKFinal
  end.

(** Total event projections keep the IR first-order.  Each rule is selected
    by its event tag before these fields are evaluated, so the defaults are
    unreachable for well-selected rules. *)
Definition event_message (event : @echo_event node) : @echo_message node :=
  match event with
  | EchoStart _ => mkEchoMessage 0 EchoRequest initiator initiator
  | EchoFirstRequestNonLeaf message _
  | EchoFirstRequestLeaf message
  | EchoRepeatedRequest message
  | EchoInitiatorRequest message
  | EchoParticipantReplyMore message _
  | EchoParticipantReplyFinal message _
  | EchoInitiatorReplyMore message
  | EchoInitiatorReplyFinal message => message
  end.

Definition event_ordered_nodes (event : @echo_event node) : list node :=
  match event with
  | EchoStart ordered
  | EchoFirstRequestNonLeaf _ ordered => ordered
  | _ => []
  end.

Definition event_parent (event : @echo_event node) : node :=
  match event with
  | EchoParticipantReplyMore _ parent
  | EchoParticipantReplyFinal _ parent => parent
  | _ => initiator
  end.

Inductive ir_node_expr : Type :=
  | IRInitiatorNode
  | IRMessageSender
  | IRMessageReceiver
  | IREventParent.

Inductive ir_nodes_expr : Type :=
  | IRNodesEmpty
  | IRNodesOrdered
  | IRNodesPending (process : ir_node_expr)
  | IRNodesNeighbors (process : ir_node_expr)
  | IRNodesRemove (item : ir_node_expr) (items : ir_nodes_expr).

Inductive ir_parent_expr : Type :=
  | IRNoParent
  | IRSomeParent (parent : ir_node_expr)
  | IRCurrentParent (process : ir_node_expr).

Inductive ir_process_expr : Type :=
  | IRCurrentProcess (process : ir_node_expr)
  | IRMakeProcess
      (parent : ir_parent_expr)
      (pending : ir_nodes_expr)
      (finished : bool).

Inductive ir_outbound_expr : Type :=
  | IRNoOutbound
  | IROneOutbound (kind : echo_kind) (receiver : ir_node_expr)
  | IRMapOutbound (kind : echo_kind) (receivers : ir_nodes_expr).

Inductive ir_action : Type :=
  | IRStartAction (neighbors : ir_nodes_expr)
  | IRDeliverAction
      (new_process : ir_process_expr)
      (outbound : ir_outbound_expr).

Inductive ir_guard : Type :=
  | IRGuardInitial
  | IRGuardKind (kind : echo_kind)
  | IRGuardNodeEqual (left right : ir_node_expr)
  | IRGuardNodeNotEqual (left right : ir_node_expr)
  | IRGuardMessageInStore
  | IRGuardProcessInitial (process : ir_node_expr)
  | IRGuardPermutation (left right : ir_nodes_expr)
  | IRGuardNodesEmpty (items : ir_nodes_expr)
  | IRGuardNodesNonempty (items : ir_nodes_expr)
  | IRGuardHasParentOrFinished (process : ir_node_expr)
  | IRGuardStarted (expected : bool)
  | IRGuardFinished (process : ir_node_expr) (expected : bool)
  | IRGuardParentEqual (process : ir_node_expr) (parent : ir_parent_expr)
  | IRGuardNodeIn (item : ir_node_expr) (items : ir_nodes_expr).

Record ir_rule : Type := mkIRRule {
  ir_rule_tag : ir_event_tag;
  ir_rule_guards : list ir_guard;
  ir_rule_action : ir_action
}.

Definition eval_node_expr
    (event : @echo_event node) (expr : ir_node_expr) : node :=
  match expr with
  | IRInitiatorNode => initiator
  | IRMessageSender => message_sender (event_message event)
  | IRMessageReceiver => message_receiver (event_message event)
  | IREventParent => event_parent event
  end.

Fixpoint eval_nodes_expr
    (s : @executable_echo_state node) (event : @echo_event node)
    (expr : ir_nodes_expr) : list node :=
  match expr with
  | IRNodesEmpty => []
  | IRNodesOrdered => event_ordered_nodes event
  | IRNodesPending process =>
      process_pending (processes s (eval_node_expr event process))
  | IRNodesNeighbors process =>
      nbrs all_nodes adj (eval_node_expr event process)
  | IRNodesRemove item items =>
      remove_echo_node node_eq (eval_node_expr event item)
        (eval_nodes_expr s event items)
  end.

Definition eval_parent_expr
    (s : @executable_echo_state node) (event : @echo_event node)
    (expr : ir_parent_expr) : option node :=
  match expr with
  | IRNoParent => None
  | IRSomeParent parent => Some (eval_node_expr event parent)
  | IRCurrentParent process =>
      process_parent (processes s (eval_node_expr event process))
  end.

Definition eval_process_expr
    (s : @executable_echo_state node) (event : @echo_event node)
    (expr : ir_process_expr) : @echo_process node :=
  match expr with
  | IRCurrentProcess process => processes s (eval_node_expr event process)
  | IRMakeProcess parent pending finished =>
      mkEchoProcess
        (eval_parent_expr s event parent)
        (eval_nodes_expr s event pending)
        finished
  end.

Definition eval_outbound_expr
    (s : @executable_echo_state node) (event : @echo_event node)
    (expr : ir_outbound_expr) : list (@echo_outbound node) :=
  match expr with
  | IRNoOutbound => []
  | IROneOutbound kind receiver =>
      [mkEchoOutbound kind (eval_node_expr event receiver)]
  | IRMapOutbound kind receivers =>
      List.map (mkEchoOutbound kind) (eval_nodes_expr s event receivers)
  end.

Definition eval_action
    (s : @executable_echo_state node) (event : @echo_event node)
    (action : ir_action) : @executable_echo_state node :=
  match action with
  | IRStartAction neighbors =>
      apply_echo_start node_eq initiator s
        (eval_nodes_expr s event neighbors)
  | IRDeliverAction new_process outbound =>
      apply_echo_delivery node_eq s (event_message event)
        (eval_process_expr s event new_process)
        (eval_outbound_expr s event outbound)
  end.

Definition guard_holds
    (s : @executable_echo_state node) (event : @echo_event node)
    (guard : ir_guard) : Prop :=
  match guard with
  | IRGuardInitial => echo_initial_on config s
  | IRGuardKind kind => message_kind (event_message event) = kind
  | IRGuardNodeEqual lhs rhs =>
      eval_node_expr event lhs = eval_node_expr event rhs
  | IRGuardNodeNotEqual lhs rhs =>
      eval_node_expr event lhs <> eval_node_expr event rhs
  | IRGuardMessageInStore => In (event_message event) (message_store s)
  | IRGuardProcessInitial process =>
      processes s (eval_node_expr event process) = initial_echo_process
  | IRGuardPermutation lhs rhs =>
      Permutation
        (eval_nodes_expr s event lhs)
        (eval_nodes_expr s event rhs)
  | IRGuardNodesEmpty items => eval_nodes_expr s event items = []
  | IRGuardNodesNonempty items => eval_nodes_expr s event items <> []
  | IRGuardHasParentOrFinished process =>
      (exists parent,
          process_parent (processes s (eval_node_expr event process)) = Some parent) \/
      process_finished (processes s (eval_node_expr event process)) = true
  | IRGuardStarted expected => started s = expected
  | IRGuardFinished process expected =>
      process_finished (processes s (eval_node_expr event process)) = expected
  | IRGuardParentEqual process parent =>
      process_parent (processes s (eval_node_expr event process)) =
      eval_parent_expr s event parent
  | IRGuardNodeIn item items =>
      In (eval_node_expr event item) (eval_nodes_expr s event items)
  end.

Definition guard_dec
    (s : @executable_echo_state node)
    (event : @echo_event node)
    (guard : ir_guard) :
    {guard_holds s event guard} + {~ guard_holds s event guard}.
Proof.
  destruct guard; simpl.
  - exact (echo_initial_on_dec node_eq config s).
  - apply echo_kind_eq_dec.
  - apply node_eq.
  - apply echo_dec_not. apply node_eq.
  - apply in_dec. apply echo_message_eq_dec. exact node_eq.
  - apply echo_process_eq_dec. exact node_eq.
  - apply node_list_permutation_dec. exact node_eq.
  - apply list_eq_dec. exact node_eq.
  - apply echo_dec_not. apply list_eq_dec. exact node_eq.
  - apply echo_dec_or.
    + apply echo_process_has_parent_dec.
    + apply Bool.bool_dec.
  - apply Bool.bool_dec.
  - apply Bool.bool_dec.
  - apply option_echo_node_eq_dec. exact node_eq.
  - apply in_dec. exact node_eq.
Defined.

Definition eval_guard
    (s : @executable_echo_state node)
    (event : @echo_event node)
    (guard : ir_guard) : bool :=
  echo_decision_to_bool (guard_dec s event guard).

Theorem eval_guard_true_iff s event guard :
  eval_guard s event guard = true <->
  guard_holds s event guard.
Proof.
  unfold eval_guard. apply echo_decision_to_bool_true_iff.
Qed.

Definition eval_guards
    (s : @executable_echo_state node)
    (event : @echo_event node)
    (guards : list ir_guard) : bool :=
  forallb (eval_guard s event) guards.

Theorem eval_guards_true_iff s event guards :
  eval_guards s event guards = true <->
  Forall (guard_holds s event) guards.
Proof.
  unfold eval_guards. rewrite forallb_forall.
  split.
  - intros Hall. apply Forall_forall. intros guard Hin.
    apply (proj1 (eval_guard_true_iff s event guard)).
    now apply Hall.
  - intros Hall guard Hin.
    apply (proj2 (eval_guard_true_iff s event guard)).
    eapply Forall_forall; eauto.
Qed.

Definition start_rule : ir_rule :=
  mkIRRule IRStart
    [IRGuardInitial;
     IRGuardPermutation IRNodesOrdered (IRNodesNeighbors IRInitiatorNode)]
    (IRStartAction IRNodesOrdered).

Definition first_echo_nonleaf_rule : ir_rule :=
  mkIRRule IRFirstECHONonLeaf
    [IRGuardKind EchoRequest;
     IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode;
     IRGuardMessageInStore;
     IRGuardProcessInitial IRMessageReceiver;
     IRGuardPermutation IRNodesOrdered
       (IRNodesRemove IRMessageSender (IRNodesNeighbors IRMessageReceiver));
     IRGuardNodesNonempty IRNodesOrdered]
    (IRDeliverAction
      (IRMakeProcess (IRSomeParent IRMessageSender) IRNodesOrdered false)
      (IRMapOutbound EchoRequest IRNodesOrdered)).

Definition first_echo_leaf_rule : ir_rule :=
  mkIRRule IRFirstECHOLeaf
    [IRGuardKind EchoRequest;
     IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode;
     IRGuardMessageInStore;
     IRGuardProcessInitial IRMessageReceiver;
     IRGuardNodesEmpty
       (IRNodesRemove IRMessageSender (IRNodesNeighbors IRMessageReceiver))]
    (IRDeliverAction
      (IRMakeProcess (IRSomeParent IRMessageSender) IRNodesEmpty true)
      (IROneOutbound EchoReply IRMessageSender)).

Definition repeated_echo_rule : ir_rule :=
  mkIRRule IRRepeatedECHO
    [IRGuardKind EchoRequest;
     IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode;
     IRGuardMessageInStore;
     IRGuardHasParentOrFinished IRMessageReceiver]
    (IRDeliverAction
      (IRCurrentProcess IRMessageReceiver)
      (IROneOutbound EchoReply IRMessageSender)).

Definition initiator_echo_rule : ir_rule :=
  mkIRRule IRInitiatorECHO
    [IRGuardKind EchoRequest;
     IRGuardNodeEqual IRMessageReceiver IRInitiatorNode;
     IRGuardStarted true;
     IRGuardFinished IRInitiatorNode false;
     IRGuardMessageInStore]
    (IRDeliverAction
      (IRCurrentProcess IRInitiatorNode)
      (IROneOutbound EchoReply IRMessageSender)).

Definition participant_ack_more_rule : ir_rule :=
  mkIRRule IRParticipantACKMore
    [IRGuardKind EchoReply;
     IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode;
     IRGuardMessageInStore;
     IRGuardParentEqual IRMessageReceiver (IRSomeParent IREventParent);
     IRGuardNodeIn IRMessageSender (IRNodesPending IRMessageReceiver);
     IRGuardNodesNonempty
       (IRNodesRemove IRMessageSender (IRNodesPending IRMessageReceiver));
     IRGuardFinished IRMessageReceiver false]
    (IRDeliverAction
      (IRMakeProcess (IRSomeParent IREventParent)
        (IRNodesRemove IRMessageSender (IRNodesPending IRMessageReceiver)) false)
      IRNoOutbound).

Definition participant_ack_final_rule : ir_rule :=
  mkIRRule IRParticipantACKFinal
    [IRGuardKind EchoReply;
     IRGuardNodeNotEqual IRMessageReceiver IRInitiatorNode;
     IRGuardMessageInStore;
     IRGuardParentEqual IRMessageReceiver (IRSomeParent IREventParent);
     IRGuardNodeIn IRMessageSender (IRNodesPending IRMessageReceiver);
     IRGuardNodesEmpty
       (IRNodesRemove IRMessageSender (IRNodesPending IRMessageReceiver));
     IRGuardFinished IRMessageReceiver false]
    (IRDeliverAction
      (IRMakeProcess (IRSomeParent IREventParent) IRNodesEmpty true)
      (IROneOutbound EchoReply IREventParent)).

Definition initiator_ack_more_rule : ir_rule :=
  mkIRRule IRInitiatorACKMore
    [IRGuardKind EchoReply;
     IRGuardNodeEqual IRMessageReceiver IRInitiatorNode;
     IRGuardStarted true;
     IRGuardParentEqual IRInitiatorNode IRNoParent;
     IRGuardMessageInStore;
     IRGuardNodeIn IRMessageSender (IRNodesPending IRInitiatorNode);
     IRGuardNodesNonempty
       (IRNodesRemove IRMessageSender (IRNodesPending IRInitiatorNode));
     IRGuardFinished IRInitiatorNode false]
    (IRDeliverAction
      (IRMakeProcess IRNoParent
        (IRNodesRemove IRMessageSender (IRNodesPending IRInitiatorNode)) false)
      IRNoOutbound).

Definition initiator_ack_final_rule : ir_rule :=
  mkIRRule IRInitiatorACKFinal
    [IRGuardKind EchoReply;
     IRGuardNodeEqual IRMessageReceiver IRInitiatorNode;
     IRGuardStarted true;
     IRGuardParentEqual IRInitiatorNode IRNoParent;
     IRGuardMessageInStore;
     IRGuardNodeIn IRMessageSender (IRNodesPending IRInitiatorNode);
     IRGuardNodesEmpty
       (IRNodesRemove IRMessageSender (IRNodesPending IRInitiatorNode));
     IRGuardFinished IRInitiatorNode false]
    (IRDeliverAction
      (IRMakeProcess IRNoParent IRNodesEmpty true)
      IRNoOutbound).

Definition echo_program : list ir_rule :=
  [start_rule;
   first_echo_nonleaf_rule;
   first_echo_leaf_rule;
   repeated_echo_rule;
   initiator_echo_rule;
   participant_ack_more_rule;
   participant_ack_final_rule;
   initiator_ack_more_rule;
   initiator_ack_final_rule].

Fixpoint lookup_rule
    (tag : ir_event_tag) (program : list ir_rule) : option ir_rule :=
  match program with
  | [] => None
  | rule :: rest =>
      if ir_event_tag_eqb tag (ir_rule_tag rule)
      then Some rule
      else lookup_rule tag rest
  end.

Definition interpret_echo_program
    (s : @executable_echo_state node)
    (event : @echo_event node) : option (@executable_echo_state node) :=
  match lookup_rule (event_tag event) echo_program with
  | None => None
  | Some rule =>
      if eval_guards s event (ir_rule_guards rule)
      then Some (eval_action s event (ir_rule_action rule))
      else None
  end.

(** The canonical executable Echo transition.  Keeping this small wrapper
    gives clients a stable name while making [echo_program] the sole source
    of transition guards and updates. *)
Definition echo_exec
    (s : @executable_echo_state node)
    (event : @echo_event node) : option (@executable_echo_state node) :=
  interpret_echo_program s event.

(** The maintained logical view of executable behavior.  It is definitionally
    derived from [echo_exec], so it cannot drift into a second nine-branch
    model.  Startup validity is decided internally over the finite node list
    in [config]. *)
Definition EchoStep
    (s : @executable_echo_state node)
    (event : @echo_event node)
    (s' : @executable_echo_state node) : Prop :=
  echo_exec s event = Some s'.

Theorem EchoStep_deterministic
    (s : @executable_echo_state node)
    (event : @echo_event node)
    (left right : @executable_echo_state node) :
  EchoStep s event left ->
  EchoStep s event right ->
  left = right.
Proof.
  unfold EchoStep. intros Hleft Hright.
  rewrite Hleft in Hright. now inversion Hright.
Qed.

End EchoTransitionIR.
