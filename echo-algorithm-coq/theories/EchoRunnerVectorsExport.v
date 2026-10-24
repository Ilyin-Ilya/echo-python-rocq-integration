(** * Rocq-computed full-run vectors

    Each entry contains a complete configuration, fuel bound, initial state,
    event schedule, and the actual result of [run_schedule].  These vectors
    are the Phase 4 cross-language oracle for generation of the Python runner. *)

From Stdlib Require Import List String Arith.
Import ListNotations.
Open Scope string_scope.

Require Import EchoExecutableTypes EchoRunner EchoRunnerExamples
  EchoTransitionIRExport EchoEvaluationVectorsExport.

Fixpoint run_schedule_events_sexpr
    (schedule : list (@echo_event nat)) : string :=
  match schedule with
  | [] => ""
  | event :: rest =>
      " " ++ vector_event_sexpr event ++ run_schedule_events_sexpr rest
  end.

Definition run_schedule_sexpr
    (schedule : list (@echo_event nat)) : string :=
  "(schedule" ++ run_schedule_events_sexpr schedule ++ ")".

Definition run_outcome_sexpr
    (nodes : list nat) (outcome : @run_outcome nat) : string :=
  match outcome with
  | EchoRunComplete state steps =>
      "(complete " ++ vector_nat_atom steps ++ " " ++
        vector_state_on_nodes_sexpr nodes state ++ ")"
  | EchoRunStuck state steps =>
      "(stuck " ++ vector_nat_atom steps ++ " " ++
        vector_state_on_nodes_sexpr nodes state ++ ")"
  | EchoRunBounded state steps =>
      "(bounded " ++ vector_nat_atom steps ++ " " ++
        vector_state_on_nodes_sexpr nodes state ++ ")"
  | EchoRunInvalidChoice state steps event =>
      "(invalid-choice " ++ vector_nat_atom steps ++ " " ++
        vector_state_on_nodes_sexpr nodes state ++ " " ++
        vector_event_sexpr event ++ ")"
  end.

Definition run_vector_sexpr
    (name config_sexpr : string)
    (nodes : list nat)
    (config : @echo_config nat)
    (fuel : nat)
    (initial : @executable_echo_state nat)
    (schedule : list (@echo_event nat)) : string :=
  "(run-vector " ++ name ++ " " ++ config_sexpr ++ " " ++
    vector_nat_atom fuel ++ " " ++
    vector_state_on_nodes_sexpr nodes initial ++ " " ++
    run_schedule_sexpr schedule ++ " " ++
    run_outcome_sexpr nodes
      (run_schedule Nat.eq_dec config fuel initial schedule) ++ ")".

Definition two_node_config_sexpr : string :=
  "(config 0 (nodes 0 1) (adjacency (node 0 1) (node 1 0)))".

Definition three_node_star_config_sexpr : string :=
  "(config 0 (nodes 0 1 2) " ++
  "(adjacency (node 0 1 2) (node 1 0) (node 2 0)))".

Definition singleton_config_sexpr : string :=
  "(config 0 (nodes 0) (adjacency (node 0)))".

Definition echo_run_vector_entries : list string :=
  [run_vector_sexpr "two-node-complete"
      two_node_config_sexpr [0; 1] two_node_config 3
      initial_executable_echo_state two_node_complete_schedule;
   run_vector_sexpr "star-left-first"
      three_node_star_config_sexpr [0; 1; 2] three_node_star_config 5
      initial_executable_echo_state star_left_first_schedule;
   run_vector_sexpr "star-right-first"
      three_node_star_config_sexpr [0; 1; 2] three_node_star_config 5
      initial_executable_echo_state star_right_first_schedule;
   run_vector_sexpr "singleton-complete"
      singleton_config_sexpr [0] singleton_config 1
      initial_executable_echo_state [EchoStart []];
   run_vector_sexpr "started-stuck"
      two_node_config_sexpr [0; 1] two_node_config 5
      two_node_stuck_state [];
   run_vector_sexpr "zero-fuel-bounded"
      two_node_config_sexpr [0; 1] two_node_config 0
      initial_executable_echo_state two_node_complete_schedule;
   run_vector_sexpr "invalid-start"
      two_node_config_sexpr [0; 1] two_node_config 1
      initial_executable_echo_state [EchoStart [0]]].

Fixpoint run_vector_entries_sexpr (entries : list string) : string :=
  match entries with
  | [] => ""
  | entry :: rest => " " ++ entry ++ run_vector_entries_sexpr rest
  end.

Definition echo_run_vectors_sexpr : string :=
  "(run-vectors" ++ run_vector_entries_sexpr echo_run_vector_entries ++ ")".

Example echo_run_exports_seven_vectors :
  List.length echo_run_vector_entries = 7.
Proof. reflexivity. Qed.

