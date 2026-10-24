(** * Rocq-computed cross-language evaluation vectors

    The vectors below serialize concrete inputs and the actual result of
    canonical [echo_exec].  Python generation evaluates this value with Rocq
    and then executes the generated interpreter against every exported case.
    This makes the cross-language comparison mechanical rather than
    maintaining parallel expected values by hand. *)

From Stdlib Require Import List String Arith DecimalString.
Import ListNotations.
Open Scope string_scope.

Require Import EchoExecutableTypes EchoTransitionIR EchoTransitionIRExport
  EchoExecutableExamples.

Definition vector_nat_atom (value : nat) : string :=
  NilEmpty.string_of_uint (Nat.to_uint value).

Fixpoint vector_nat_atoms (values : list nat) : string :=
  match values with
  | [] => ""
  | value :: rest => " " ++ vector_nat_atom value ++ vector_nat_atoms rest
  end.

Definition vector_nodes_sexpr (head : string) (values : list nat) : string :=
  "(" ++ head ++ vector_nat_atoms values ++ ")".

Definition vector_parent_sexpr (parent : option nat) : string :=
  match parent with
  | None => "none"
  | Some node => unary "some" (vector_nat_atom node)
  end.

Definition vector_process_sexpr
    (node : nat) (process : @echo_process nat) : string :=
  "(process " ++ vector_nat_atom node ++ " " ++
    vector_parent_sexpr (process_parent process) ++ " " ++
    vector_nodes_sexpr "pending" (process_pending process) ++ " " ++
    bool_atom (process_finished process) ++ ")".

Fixpoint vector_roles_sexpr
    (nodes : list nat) (roles : nat -> @echo_process nat) : string :=
  match nodes with
  | [] => ""
  | node :: rest => " " ++ vector_process_sexpr node (roles node) ++
      vector_roles_sexpr rest roles
  end.

Definition vector_message_sexpr (message : @echo_message nat) : string :=
  "(message " ++ vector_nat_atom (message_id message) ++ " " ++
    message_kind_atom (message_kind message) ++ " " ++
    vector_nat_atom (message_sender message) ++ " " ++
    vector_nat_atom (message_receiver message) ++ ")".

Fixpoint vector_messages_sexpr (messages : list (@echo_message nat)) : string :=
  match messages with
  | [] => ""
  | message :: rest => " " ++ vector_message_sexpr message ++
      vector_messages_sexpr rest
  end.

Definition vector_state_on_nodes_sexpr
    (nodes : list nat) (state : @executable_echo_state nat) : string :=
  "(state " ++ bool_atom (started state) ++ " " ++
    vector_nat_atom (next_message_id state) ++
    " (roles" ++ vector_roles_sexpr nodes
      (processes state) ++ ")" ++
    " (store" ++ vector_messages_sexpr (message_store state) ++ "))".

Definition vector_state_sexpr (state : @executable_echo_state nat) : string :=
  vector_state_on_nodes_sexpr executable_example_nodes state.

Definition vector_event_message_sexpr
    (event : @echo_event nat) : string :=
  match event with
  | EchoStart _ => "no-message"
  | EchoFirstRequestNonLeaf message _
  | EchoFirstRequestLeaf message
  | EchoRepeatedRequest message
  | EchoInitiatorRequest message
  | EchoParticipantReplyMore message _
  | EchoParticipantReplyFinal message _
  | EchoInitiatorReplyMore message
  | EchoInitiatorReplyFinal message => vector_message_sexpr message
  end.

Definition vector_event_ordered_nodes
    (event : @echo_event nat) : list nat :=
  match event with
  | EchoStart ordered
  | EchoFirstRequestNonLeaf _ ordered => ordered
  | _ => []
  end.

Definition vector_event_parent (event : @echo_event nat) : option nat :=
  match event with
  | EchoParticipantReplyMore _ parent
  | EchoParticipantReplyFinal _ parent => Some parent
  | _ => None
  end.

Definition vector_event_sexpr (event : @echo_event nat) : string :=
  "(event " ++ event_tag_atom (@event_tag nat event) ++ " " ++
    vector_event_message_sexpr event ++ " " ++
    vector_nodes_sexpr "ordered" (vector_event_ordered_nodes event) ++ " " ++
    vector_parent_sexpr (vector_event_parent event) ++ ")".

Definition vector_result_sexpr (result : option (@executable_echo_state nat)) : string :=
  match result with
  | None => "none"
  | Some state => unary "some" (vector_state_sexpr state)
  end.

Definition evaluation_vector_sexpr
    (name : string)
    (state : @executable_echo_state nat)
    (event : @echo_event nat) : string :=
  "(vector " ++ name ++ " " ++ vector_state_sexpr state ++ " " ++
    vector_event_sexpr event ++ " " ++
    vector_result_sexpr
      (@echo_exec nat Nat.eq_dec executable_example_config state event) ++ ")".

Definition echo_evaluation_config_sexpr : string :=
  "(config 0 (nodes 0 1 2 3 4) " ++
  "(adjacency (node 0 1 2) (node 1 0 3 4) (node 2 0) " ++
  "(node 3 1) (node 4 1)))".

Definition echo_evaluation_vector_entries : list string :=
  [ evaluation_vector_sexpr "start"
      executable_example_initial
      (EchoStart [1; 2]);
    evaluation_vector_sexpr "first-echo-nonleaf"
      first_nonleaf_state
      (EchoFirstRequestNonLeaf first_nonleaf_message [3; 4]);
    evaluation_vector_sexpr "first-echo-leaf"
      first_leaf_state
      (EchoFirstRequestLeaf first_leaf_message);
    evaluation_vector_sexpr "repeated-echo"
      repeated_echo_state
      (EchoRepeatedRequest repeated_echo_message);
    evaluation_vector_sexpr "initiator-echo"
      initiator_echo_state
      (EchoInitiatorRequest initiator_echo_message);
    evaluation_vector_sexpr "participant-ack-more"
      participant_ack_more_state
      (EchoParticipantReplyMore participant_ack_more_message 0);
    evaluation_vector_sexpr "participant-ack-final"
      participant_ack_final_state
      (EchoParticipantReplyFinal participant_ack_final_message 0);
    evaluation_vector_sexpr "initiator-ack-more"
      initiator_ack_more_state
      (EchoInitiatorReplyMore initiator_ack_more_message);
    evaluation_vector_sexpr "initiator-ack-final"
      initiator_ack_final_state
      (EchoInitiatorReplyFinal initiator_ack_final_message);
    evaluation_vector_sexpr "invalid-first-echo-nonleaf-order"
      first_nonleaf_state
      (EchoFirstRequestNonLeaf first_nonleaf_message [3]) ].

Fixpoint evaluation_vector_entries_sexpr (entries : list string) : string :=
  match entries with
  | [] => ""
  | entry :: rest => " " ++ entry ++ evaluation_vector_entries_sexpr rest
  end.

Definition echo_evaluation_vectors_sexpr : string :=
  "(evaluation-vectors " ++ echo_evaluation_config_sexpr ++
    evaluation_vector_entries_sexpr echo_evaluation_vector_entries ++ ")".

Example echo_evaluation_exports_ten_vectors :
  List.length echo_evaluation_vector_entries = 10.
Proof. reflexivity. Qed.
