(** * Computed outcome examples for the canonical Echo runner *)

From Stdlib Require Import List Arith Bool.
Import ListNotations.
Require Import EchoExecutableTypes EchoRunner.

Definition two_node_adj (left right : nat) : bool :=
  ((Nat.eqb left 0) && (Nat.eqb right 1)) ||
  ((Nat.eqb left 1) && (Nat.eqb right 0)).

Definition two_node_config : @echo_config nat :=
  mkEchoConfig 0 [0; 1] two_node_adj.

Definition two_node_request : @echo_message nat :=
  mkEchoMessage 1 EchoRequest 0 1.

Definition two_node_reply : @echo_message nat :=
  mkEchoMessage 2 EchoReply 1 0.

Definition two_node_complete_schedule : list (@echo_event nat) :=
  [EchoStart [1];
   EchoFirstRequestLeaf two_node_request;
   EchoInitiatorReplyFinal two_node_reply].

(** A full non-singleton run starts, discovers the participant, returns the
    final reply, and consumes exactly three scheduled events. *)
Example two_node_run_completes :
  exists final_state,
    run_schedule Nat.eq_dec two_node_config 3
      initial_executable_echo_state two_node_complete_schedule =
    EchoRunComplete final_state 3.
Proof. eexists. vm_compute. reflexivity. Qed.

Definition singleton_config : @echo_config nat :=
  mkEchoConfig 0 [0] (fun _ _ => false).

(** Completion is derived from canonical state, so the singleton needs only
    its valid empty-neighbor startup event and no special transition rule. *)
Example singleton_run_completes :
  exists final_state,
    run_schedule Nat.eq_dec singleton_config 1
      initial_executable_echo_state [EchoStart []] =
    EchoRunComplete final_state 1.
Proof. eexists. vm_compute. reflexivity. Qed.

Definition two_node_stuck_state : @executable_echo_state nat :=
  mkExecutableEchoState
    (fun candidate =>
      if Nat.eq_dec candidate 0
      then mkEchoProcess None [1] false
      else initial_echo_process)
    [] true 1.

Example started_empty_store_can_be_stuck :
  run_schedule Nat.eq_dec two_node_config 5 two_node_stuck_state [] =
  EchoRunStuck two_node_stuck_state 0.
Proof. vm_compute. reflexivity. Qed.

Example zero_fuel_is_bounded :
  run_schedule Nat.eq_dec two_node_config 0
    initial_executable_echo_state two_node_complete_schedule =
  EchoRunBounded initial_executable_echo_state 0.
Proof. vm_compute. reflexivity. Qed.

Example rejected_start_is_invalid_choice :
  run_schedule Nat.eq_dec two_node_config 1
    initial_executable_echo_state [EchoStart [0]] =
  EchoRunInvalidChoice initial_executable_echo_state 0 (EchoStart [0]).
Proof. vm_compute. reflexivity. Qed.

Definition three_node_star_adj (left right : nat) : bool :=
  ((Nat.eqb left 0) && ((Nat.eqb right 1) || (Nat.eqb right 2))) ||
  (((Nat.eqb left 1) || (Nat.eqb left 2)) && (Nat.eqb right 0)).

Definition three_node_star_config : @echo_config nat :=
  mkEchoConfig 0 [0; 1; 2] three_node_star_adj.

Definition star_request_1 : @echo_message nat :=
  mkEchoMessage 1 EchoRequest 0 1.

Definition star_request_2 : @echo_message nat :=
  mkEchoMessage 2 EchoRequest 0 2.

Definition star_reply_1_when_first : @echo_message nat :=
  mkEchoMessage 3 EchoReply 1 0.

Definition star_reply_2_when_second : @echo_message nat :=
  mkEchoMessage 4 EchoReply 2 0.

Definition star_left_first_schedule : list (@echo_event nat) :=
  [EchoStart [1; 2];
   EchoFirstRequestLeaf star_request_1;
   EchoFirstRequestLeaf star_request_2;
   EchoInitiatorReplyMore star_reply_1_when_first;
   EchoInitiatorReplyFinal star_reply_2_when_second].

Definition star_reply_2_when_first : @echo_message nat :=
  mkEchoMessage 3 EchoReply 2 0.

Definition star_reply_1_when_second : @echo_message nat :=
  mkEchoMessage 4 EchoReply 1 0.

Definition star_right_first_schedule : list (@echo_event nat) :=
  [EchoStart [1; 2];
   EchoFirstRequestLeaf star_request_2;
   EchoFirstRequestLeaf star_request_1;
   EchoInitiatorReplyMore star_reply_2_when_first;
   EchoInitiatorReplyFinal star_reply_1_when_second].

(** Different legal delivery orders compute complete states through the same
    runner.  Their message IDs record the chosen order, while the parent tree
    and terminal classification agree. *)
Example three_node_star_left_first_completes :
  exists final_state,
    run_schedule Nat.eq_dec three_node_star_config 5
      initial_executable_echo_state star_left_first_schedule =
    EchoRunComplete final_state 5.
Proof. eexists. vm_compute. reflexivity. Qed.

Example three_node_star_right_first_completes :
  exists final_state,
    run_schedule Nat.eq_dec three_node_star_config 5
      initial_executable_echo_state star_right_first_schedule =
    EchoRunComplete final_state 5.
Proof. eexists. vm_compute. reflexivity. Qed.
