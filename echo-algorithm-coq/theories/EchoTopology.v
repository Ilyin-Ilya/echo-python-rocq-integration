(** * Protocol-neutral topology interface used by Echo developments

    This module contains only finite-node configuration data, graph laws used
    by correctness proofs, and the deterministic neighbor-list projection. It
    deliberately contains no Echo message, process state, transition, or
    reachability definition. *)

From Stdlib Require Import List.

Module Type ECHO_CONFIG.
  Parameter node : Type.
  Parameter node_eq : forall (n m : node), {n = m} + {n <> m}.
  Parameter initiator : node.
  Parameter all_nodes : list node.
  Parameter adj : node -> node -> bool.
End ECHO_CONFIG.

Module Type ECHO_CORRECTNESS_CONFIG.
  Include ECHO_CONFIG.

  Parameter adj_sym : forall n m, adj n m = true -> adj m n = true.
  Parameter adj_irrefl : forall n, adj n n = false.
  Parameter initiator_in_nodes : In initiator all_nodes.
  Parameter nodup_nodes : NoDup all_nodes.
End ECHO_CORRECTNESS_CONFIG.

Definition nbrs {node : Type}
    (all_nodes : list node)
    (adj : node -> node -> bool)
    (owner : node) : list node :=
  List.filter (fun candidate => adj owner candidate) all_nodes.

Arguments nbrs {node}.
