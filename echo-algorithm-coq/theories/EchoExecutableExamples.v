(** * Computation examples for the canonical executable Echo transition

    These examples cover all nine event forms on a concrete five-node
    topology. They call [echo_exec] directly and supply the reference values
    serialized for the Python generator. *)

From Stdlib Require Import List Arith.
Import ListNotations.
Require Import EchoExecutableTypes EchoTransitionIR.

(** The undirected topology has edges 0--1, 0--2, 1--3, and 1--4. *)
Definition executable_example_nodes : list nat := [0; 1; 2; 3; 4].

Definition executable_example_adj (left right : nat) : bool :=
  match left, right with
  | 0, 1 | 1, 0
  | 0, 2 | 2, 0
  | 1, 3 | 3, 1
  | 1, 4 | 4, 1 => true
  | _, _ => false
  end.

Definition executable_example_config : @echo_config nat :=
  mkEchoConfig 0 executable_example_nodes executable_example_adj.

Definition executable_example_roles : nat -> @echo_process nat :=
  fun _ => initial_echo_process.

Definition executable_example_initial : @executable_echo_state nat :=
  mkExecutableEchoState executable_example_roles [] false 1.

Definition single_role_state
    (target : nat) (process : @echo_process nat)
    (message : @echo_message nat) : @executable_echo_state nat :=
  mkExecutableEchoState
    (update_process Nat.eq_dec executable_example_roles target process)
    [message]
    true
    2.

Example execute_start_computes :
  @echo_exec nat Nat.eq_dec executable_example_config
    executable_example_initial (EchoStart [1; 2]) =
  Some (apply_echo_start Nat.eq_dec 0 executable_example_initial [1; 2]).
Proof. vm_compute. reflexivity. Qed.

Definition first_nonleaf_message : @echo_message nat :=
  mkEchoMessage 1 EchoRequest 0 1.

Definition first_nonleaf_state : @executable_echo_state nat :=
  single_role_state 1 initial_echo_process first_nonleaf_message.

Example execute_first_echo_nonleaf_computes :
  @echo_exec nat Nat.eq_dec executable_example_config
    first_nonleaf_state
    (EchoFirstRequestNonLeaf first_nonleaf_message [3; 4]) =
  Some (apply_echo_delivery Nat.eq_dec first_nonleaf_state
    first_nonleaf_message
    (mkEchoProcess (Some 0) [3; 4] false)
    (List.map (mkEchoOutbound EchoRequest) [3; 4])).
Proof. vm_compute. reflexivity. Qed.

Definition first_leaf_message : @echo_message nat :=
  mkEchoMessage 1 EchoRequest 0 2.

Definition first_leaf_state : @executable_echo_state nat :=
  single_role_state 2 initial_echo_process first_leaf_message.

Example execute_first_echo_leaf_computes :
  @echo_exec nat Nat.eq_dec executable_example_config
    first_leaf_state (EchoFirstRequestLeaf first_leaf_message) =
  Some (apply_echo_delivery Nat.eq_dec first_leaf_state
    first_leaf_message
    (mkEchoProcess (Some 0) [] true)
    [mkEchoOutbound EchoReply 0]).
Proof. vm_compute. reflexivity. Qed.

Definition repeated_echo_message : @echo_message nat :=
  mkEchoMessage 1 EchoRequest 3 1.

Definition repeated_echo_process : @echo_process nat :=
  mkEchoProcess (Some 0) [3; 4] false.

Definition repeated_echo_state : @executable_echo_state nat :=
  single_role_state 1 repeated_echo_process repeated_echo_message.

Example execute_repeated_echo_computes :
  @echo_exec nat Nat.eq_dec executable_example_config
    repeated_echo_state (EchoRepeatedRequest repeated_echo_message) =
  Some (apply_echo_delivery Nat.eq_dec repeated_echo_state
    repeated_echo_message repeated_echo_process
    [mkEchoOutbound EchoReply 3]).
Proof. vm_compute. reflexivity. Qed.

Definition initiator_echo_message : @echo_message nat :=
  mkEchoMessage 1 EchoRequest 1 0.

Definition active_initiator_process : @echo_process nat :=
  mkEchoProcess None [1; 2] false.

Definition initiator_echo_state : @executable_echo_state nat :=
  single_role_state 0 active_initiator_process initiator_echo_message.

Example execute_initiator_echo_computes :
  @echo_exec nat Nat.eq_dec executable_example_config
    initiator_echo_state (EchoInitiatorRequest initiator_echo_message) =
  Some (apply_echo_delivery Nat.eq_dec initiator_echo_state
    initiator_echo_message active_initiator_process
    [mkEchoOutbound EchoReply 1]).
Proof. vm_compute. reflexivity. Qed.

Definition participant_ack_more_message : @echo_message nat :=
  mkEchoMessage 1 EchoReply 3 1.

Definition participant_ack_more_state : @executable_echo_state nat :=
  single_role_state 1 (mkEchoProcess (Some 0) [3; 4] false)
    participant_ack_more_message.

Example execute_participant_ack_more_computes :
  @echo_exec nat Nat.eq_dec executable_example_config
    participant_ack_more_state
    (EchoParticipantReplyMore participant_ack_more_message 0) =
  Some (apply_echo_delivery Nat.eq_dec participant_ack_more_state
    participant_ack_more_message
    (mkEchoProcess (Some 0) [4] false)
    []).
Proof. vm_compute. reflexivity. Qed.

Definition participant_ack_final_message : @echo_message nat :=
  mkEchoMessage 1 EchoReply 3 1.

Definition participant_ack_final_state : @executable_echo_state nat :=
  single_role_state 1 (mkEchoProcess (Some 0) [3] false)
    participant_ack_final_message.

Example execute_participant_ack_final_computes :
  @echo_exec nat Nat.eq_dec executable_example_config
    participant_ack_final_state
    (EchoParticipantReplyFinal participant_ack_final_message 0) =
  Some (apply_echo_delivery Nat.eq_dec participant_ack_final_state
    participant_ack_final_message
    (mkEchoProcess (Some 0) [] true)
    [mkEchoOutbound EchoReply 0]).
Proof. vm_compute. reflexivity. Qed.

Definition initiator_ack_more_message : @echo_message nat :=
  mkEchoMessage 1 EchoReply 1 0.

Definition initiator_ack_more_state : @executable_echo_state nat :=
  single_role_state 0 (mkEchoProcess None [1; 2] false)
    initiator_ack_more_message.

Example execute_initiator_ack_more_computes :
  @echo_exec nat Nat.eq_dec executable_example_config
    initiator_ack_more_state
    (EchoInitiatorReplyMore initiator_ack_more_message) =
  Some (apply_echo_delivery Nat.eq_dec initiator_ack_more_state
    initiator_ack_more_message
    (mkEchoProcess None [2] false)
    []).
Proof. vm_compute. reflexivity. Qed.

Definition initiator_ack_final_message : @echo_message nat :=
  mkEchoMessage 1 EchoReply 1 0.

Definition initiator_ack_final_state : @executable_echo_state nat :=
  single_role_state 0 (mkEchoProcess None [1] false)
    initiator_ack_final_message.

Example execute_initiator_ack_final_computes :
  @echo_exec nat Nat.eq_dec executable_example_config
    initiator_ack_final_state
    (EchoInitiatorReplyFinal initiator_ack_final_message) =
  Some (apply_echo_delivery Nat.eq_dec initiator_ack_final_state
    initiator_ack_final_message
    (mkEchoProcess None [] true)
    []).
Proof. vm_compute. reflexivity. Qed.
