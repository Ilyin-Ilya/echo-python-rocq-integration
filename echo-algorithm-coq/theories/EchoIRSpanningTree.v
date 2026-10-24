(** * Generic Echo IR completion implies a spanning tree

    This public wrapper is proved directly over the generated generic IR
    program.  It constructs the runtime configuration with
    [make_echo_ir_config] and applies the rule-preserved discovery-frontier
    theorem.  No legacy Echo state, compatibility relation, or simulation
    direction is imported. *)

From Stdlib Require Import List Arith Sorting.Permutation.
Import ListNotations.
Require Import EchoTopology ProtocolIRTypes ProtocolIRRunner
  EchoIRSignature EchoIRProgram EchoIRConfig EchoIRExecutable
  EchoIRExecutableInvariants EchoIRExecutablePending EchoIRExecutableTopology
  EchoIRExecutableSpanningTree.

Module MakeEchoIRSpanningTree (C : ECHO_CORRECTNESS_CONFIG).

Local Notation node := C.node.
Local Notation node_eq := C.node_eq.
Local Notation initiator := C.initiator.
Local Notation all_nodes := C.all_nodes.
Local Notation adj := C.adj.
Local Notation ir_config :=
  (make_echo_ir_config initiator all_nodes adj).
Local Notation ir_program := (@echo_ir_program node).

Definition echo_ir_parent
    (state : ir_protocol_state node echo_ir_signature)
    (owner : node) : option node :=
  EchoIRExecutableSpanningTree.echo_ir_parent node state owner.

Definition echo_ir_parent_path
    (state : ir_protocol_state node echo_ir_signature)
    (owner : node) (steps : nat) : option node :=
  EchoIRExecutableSpanningTree.echo_ir_parent_path node state owner steps.

Definition echo_ir_reaches_initiator
    (state : ir_protocol_state node echo_ir_signature)
    (owner : node) : Prop :=
  EchoIRExecutableSpanningTree.echo_ir_reaches_initiator
    node ir_config state owner.

Lemma echo_ir_direct_neighbors_well_formed :
  echo_ir_config_neighbors_well_formed node ir_config.
Proof.
  intros owner owner_in.
  unfold echo_ir_pending_valid.
  change (NoDup (nbrs all_nodes adj owner) /\
    forall neighbor,
      In neighbor (nbrs all_nodes adj owner) ->
      In neighbor all_nodes /\ In neighbor (nbrs all_nodes adj owner)).
  split.
  - unfold nbrs. apply NoDup_filter. exact C.nodup_nodes.
  - intros neighbor neighbor_in. split; [|exact neighbor_in].
    unfold nbrs in neighbor_in. now apply filter_In in neighbor_in.
Qed.

Lemma echo_ir_direct_neighbors_symmetric :
  echo_ir_config_neighbors_symmetric node ir_config.
Proof.
  intros left right left_in neighbor.
  change (In right (nbrs all_nodes adj left)) in neighbor.
  change (In left (nbrs all_nodes adj right)).
  unfold nbrs in neighbor |- *.
  apply filter_In in neighbor as [right_in edge].
  apply filter_In. split; [exact left_in |].
  now apply C.adj_sym.
Qed.

Lemma echo_ir_wave_depth_connects
    (wave_depth : node -> nat)
    (wave_depth_props :
      wave_depth initiator = 0 /\
      forall owner,
        In owner all_nodes -> owner <> initiator ->
        exists parent,
          In parent all_nodes /\
          adj owner parent = true /\
          wave_depth parent < wave_depth owner) :
  forall owner,
    In owner (ir_config_nodes ir_config) ->
    owner <> echo_ir_config_initiator node ir_config ->
    exists parent,
      In parent (ir_config_nodes ir_config) /\
      In owner (ir_config_neighbors ir_config parent) /\
      wave_depth parent < wave_depth owner.
Proof.
  intros owner owner_in nonroot.
  change (In owner all_nodes) in owner_in.
  change (owner <> initiator) in nonroot.
  destruct (proj2 wave_depth_props owner owner_in nonroot) as
    [parent [parent_in [edge lower]]].
  exists parent. repeat split; try assumption.
  change (In owner (nbrs all_nodes adj parent)).
  unfold nbrs. apply filter_In. split; [exact owner_in |].
  now apply C.adj_sym.
Qed.

(** Every generically reachable state accepted by the generated completion
    predicate has a parent path to the initiator for every configured node. *)
Theorem echo_ir_complete_builds_spanning_tree
    (wave_depth : node -> nat)
    (wave_depth_props :
      wave_depth initiator = 0 /\
      forall owner,
        In owner all_nodes -> owner <> initiator ->
        exists parent,
          In parent all_nodes /\
          adj owner parent = true /\
          wave_depth parent < wave_depth owner) :
  forall ir_state,
    ir_protocol_reachable node_eq ir_config (@echo_ir_rules node)
      (initialize_ir_protocol ir_program) ir_state ->
    eval_ir_state_predicate node_eq ir_config ir_state
      (@echo_ir_complete_expr node) = Some true ->
    forall owner,
      In owner all_nodes ->
      echo_ir_reaches_initiator ir_state owner.
Proof.
  intros ir_state reachable complete owner owner_in.
  eapply (@echo_reachable_complete_spanning_tree
    node node_eq ir_config ir_state wave_depth).
  - exact C.initiator_in_nodes.
  - exact echo_ir_direct_neighbors_well_formed.
  - exact echo_ir_direct_neighbors_symmetric.
  - now apply echo_ir_wave_depth_connects.
  - exact reachable.
  - exact complete.
  - exact owner_in.
Qed.

(** End-to-end generic runner theorem.  A scheduler supplies only external IR
    events; any result classified complete has a generated parent path from
    every configured node to the initiator. *)
Theorem echo_ir_complete_run_builds_spanning_tree
    (wave_depth : node -> nat)
    (wave_depth_props :
      wave_depth initiator = 0 /\
      forall owner,
        In owner all_nodes -> owner <> initiator ->
        exists parent,
          In parent all_nodes /\
          adj owner parent = true /\
          wave_depth parent < wave_depth owner) :
  forall fuel schedule final_state steps,
    run_ir_protocol node_eq ir_config ir_program fuel schedule =
      IRRunComplete final_state steps ->
    forall owner,
      In owner all_nodes ->
      echo_ir_reaches_initiator final_state owner.
Proof.
  intros fuel schedule final_state steps run_result owner owner_in.
  eapply echo_ir_complete_builds_spanning_tree; eauto.
  - pose proof (run_ir_protocol_reachable
      node_eq ir_config ir_program fuel schedule) as reached.
    now rewrite run_result in reached.
  - unfold run_ir_protocol in run_result.
    exact (run_ir_protocol_schedule_complete_sound
      node_eq ir_config ir_program fuel
      (initialize_ir_protocol ir_program) schedule
      final_state steps run_result).
Qed.

End MakeEchoIRSpanningTree.
