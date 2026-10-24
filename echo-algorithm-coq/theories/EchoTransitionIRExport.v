(** * Deterministic export of the verified Echo transition program

    [echo_program_sexpr] is a canonical, first-order representation of the
    actual [echo_program] value.  The Python generator evaluates this
    definition with Rocq; it does not parse the source text of the rules. *)

From Stdlib Require Import List String.
Import ListNotations.
Open Scope string_scope.

Require Import EchoExecutableTypes EchoTransitionIR.

Definition bool_atom (value : bool) : string :=
  if value then "true" else "false".

Definition message_kind_atom (kind : echo_kind) : string :=
  match kind with
  | EchoRequest => "echo"
  | EchoReply => "ack"
  end.

Definition event_tag_atom (tag : ir_event_tag) : string :=
  match tag with
  | IRStart => "start"
  | IRFirstECHONonLeaf => "first-echo-nonleaf"
  | IRFirstECHOLeaf => "first-echo-leaf"
  | IRRepeatedECHO => "repeated-echo"
  | IRInitiatorECHO => "initiator-echo"
  | IRParticipantACKMore => "participant-ack-more"
  | IRParticipantACKFinal => "participant-ack-final"
  | IRInitiatorACKMore => "initiator-ack-more"
  | IRInitiatorACKFinal => "initiator-ack-final"
  end.

Definition unary (head argument : string) : string :=
  "(" ++ head ++ " " ++ argument ++ ")".

Definition binary (head left right : string) : string :=
  "(" ++ head ++ " " ++ left ++ " " ++ right ++ ")".

Definition node_expr_sexpr (expr : ir_node_expr) : string :=
  match expr with
  | IRInitiatorNode => "initiator"
  | IRMessageSender => "message-sender"
  | IRMessageReceiver => "message-receiver"
  | IREventParent => "event-parent"
  end.

Fixpoint nodes_expr_sexpr (expr : ir_nodes_expr) : string :=
  match expr with
  | IRNodesEmpty => "empty-nodes"
  | IRNodesOrdered => "ordered-nodes"
  | IRNodesPending process =>
      unary "pending" (node_expr_sexpr process)
  | IRNodesNeighbors process =>
      unary "neighbors" (node_expr_sexpr process)
  | IRNodesRemove item items =>
      binary "remove" (node_expr_sexpr item) (nodes_expr_sexpr items)
  end.

Definition parent_expr_sexpr (expr : ir_parent_expr) : string :=
  match expr with
  | IRNoParent => "no-parent"
  | IRSomeParent parent => unary "some-parent" (node_expr_sexpr parent)
  | IRCurrentParent process =>
      unary "current-parent" (node_expr_sexpr process)
  end.

Definition process_expr_sexpr (expr : ir_process_expr) : string :=
  match expr with
  | IRCurrentProcess process =>
      unary "current-process" (node_expr_sexpr process)
  | IRMakeProcess parent pending finished =>
      "(make-process " ++ parent_expr_sexpr parent ++ " " ++
        nodes_expr_sexpr pending ++ " " ++ bool_atom finished ++ ")"
  end.

Definition outbound_expr_sexpr (expr : ir_outbound_expr) : string :=
  match expr with
  | IRNoOutbound => "no-outbound"
  | IROneOutbound kind receiver =>
      binary "one-outbound" (message_kind_atom kind)
        (node_expr_sexpr receiver)
  | IRMapOutbound kind receivers =>
      binary "map-outbound" (message_kind_atom kind)
        (nodes_expr_sexpr receivers)
  end.

Definition action_sexpr (action : ir_action) : string :=
  match action with
  | IRStartAction neighbors =>
      unary "start-action" (nodes_expr_sexpr neighbors)
  | IRDeliverAction new_process outbound =>
      binary "deliver-action" (process_expr_sexpr new_process)
        (outbound_expr_sexpr outbound)
  end.

Definition guard_sexpr (guard : ir_guard) : string :=
  match guard with
  | IRGuardInitial => "initial"
  | IRGuardKind kind => unary "kind" (message_kind_atom kind)
  | IRGuardNodeEqual lhs rhs =>
      binary "node-equal" (node_expr_sexpr lhs) (node_expr_sexpr rhs)
  | IRGuardNodeNotEqual lhs rhs =>
      binary "node-not-equal" (node_expr_sexpr lhs)
        (node_expr_sexpr rhs)
  | IRGuardMessageInStore => "message-in-store"
  | IRGuardProcessInitial process =>
      unary "process-initial" (node_expr_sexpr process)
  | IRGuardPermutation lhs rhs =>
      binary "permutation" (nodes_expr_sexpr lhs) (nodes_expr_sexpr rhs)
  | IRGuardNodesEmpty items => unary "nodes-empty" (nodes_expr_sexpr items)
  | IRGuardNodesNonempty items =>
      unary "nodes-nonempty" (nodes_expr_sexpr items)
  | IRGuardHasParentOrFinished process =>
      unary "has-parent-or-finished" (node_expr_sexpr process)
  | IRGuardStarted expected => unary "started" (bool_atom expected)
  | IRGuardFinished process expected =>
      binary "finished" (node_expr_sexpr process) (bool_atom expected)
  | IRGuardParentEqual process parent =>
      binary "parent-equal" (node_expr_sexpr process)
        (parent_expr_sexpr parent)
  | IRGuardNodeIn item items =>
      binary "node-in" (node_expr_sexpr item) (nodes_expr_sexpr items)
  end.

Fixpoint guards_sexpr (guards : list ir_guard) : string :=
  match guards with
  | [] => ""
  | guard :: rest => " " ++ guard_sexpr guard ++ guards_sexpr rest
  end.

Definition rule_sexpr (rule : ir_rule) : string :=
  "(rule " ++ event_tag_atom (ir_rule_tag rule) ++
    " (guards" ++ guards_sexpr (ir_rule_guards rule) ++ ") " ++
    action_sexpr (ir_rule_action rule) ++ ")".

Fixpoint rules_sexpr (rules : list ir_rule) : string :=
  match rules with
  | [] => ""
  | rule :: rest => " " ++ rule_sexpr rule ++ rules_sexpr rest
  end.

Definition program_sexpr (program : list ir_rule) : string :=
  "(program" ++ rules_sexpr program ++ ")".

Definition echo_program_sexpr : string := program_sexpr echo_program.

Example echo_program_exports_nine_rules :
  List.length echo_program = 9.
Proof. reflexivity. Qed.
