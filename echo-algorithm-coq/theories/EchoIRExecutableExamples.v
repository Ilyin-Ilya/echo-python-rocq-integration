(** * Legacy-free computed examples for the public Echo IR executable API *)

From Stdlib Require Import List Arith Bool.
Import ListNotations.
Require Import ProtocolIRTypes ProtocolIRRunner EchoIRSignature
  EchoIRExecutable EchoIRExecutableInvariants EchoIRExecutableLifecycle
  EchoIRExecutablePending EchoIRExecutableDiscovery
  EchoIRExecutableTopology EchoIRExecutableRequestAccounting.
Require Import EchoIRExecutableSpanningTree.

Definition direct_two_node_config_fields :
    ir_config_store nat echo_ir_signature :=
  fun field =>
    match field as selected
      return ir_value nat
        (signature_config_field_type echo_ir_signature selected) with
    | EchoIRInitiator => IRNodeValue 0
    end.

Definition direct_two_node_config :
    ir_protocol_config nat echo_ir_signature :=
  mkIRProtocolConfig
    [0; 1]
    (fun owner => if Nat.eq_dec owner 0 then [1] else [0])
    direct_two_node_config_fields.

Definition direct_start_certificates :
    ir_start_certificates nat echo_ir_signature :=
  fun field =>
    match field as selected
      return ir_value nat
        (signature_start_certificate_field_type echo_ir_signature selected) with
    | EchoIRStartOrder => IRListNodeValue [1]
    end.

Definition direct_delivery_certificates :
    ir_delivery_certificates nat echo_ir_signature :=
  fun field =>
    match field as selected
      return ir_value nat
        (signature_delivery_certificate_field_type
          echo_ir_signature selected) with
    | EchoIRForwardOrder => IRListNodeValue []
    | EchoIRExpectedParent => IRNodeValue 0
    end.

Definition direct_two_node_schedule :
    list (ir_external_event nat echo_ir_signature) :=
  [IRProtocolStart direct_start_certificates;
   IRProtocolDeliver 1 direct_delivery_certificates;
   IRProtocolDeliver 2 direct_delivery_certificates].

Example direct_echo_public_run_completes :
  exists final_state,
    echo_run nat Nat.eq_dec direct_two_node_config 3
      direct_two_node_schedule = IRRunComplete final_state 3.
Proof. eexists. vm_compute. reflexivity. Qed.

Example direct_echo_public_run_is_reachable :
  echo_reachable nat Nat.eq_dec direct_two_node_config
    (ir_run_outcome_state
      (echo_run nat Nat.eq_dec direct_two_node_config 3
        direct_two_node_schedule)).
Proof. apply echo_run_reachable. Qed.

Example direct_echo_public_run_respects_bound :
  ir_run_outcome_steps
    (echo_run nat Nat.eq_dec direct_two_node_config 3
      direct_two_node_schedule) <= 3.
Proof. apply echo_run_step_bound. Qed.

Example direct_echo_public_run_completion_is_sound :
  forall final_state,
    echo_run nat Nat.eq_dec direct_two_node_config 3
      direct_two_node_schedule = IRRunComplete final_state 3 ->
    echo_complete nat Nat.eq_dec direct_two_node_config final_state.
Proof.
  intros final_state run_result.
  eapply echo_run_complete_sound. exact run_result.
Qed.

Example direct_echo_public_run_next_message_id :
  ir_next_message_id
    (ir_run_outcome_state
      (echo_run nat Nat.eq_dec direct_two_node_config 3
        direct_two_node_schedule)) = 3.
Proof. vm_compute. reflexivity. Qed.

Example direct_echo_public_run_next_message_id_positive :
  1 <= ir_next_message_id
    (ir_run_outcome_state
      (echo_run nat Nat.eq_dec direct_two_node_config 3
        direct_two_node_schedule)).
Proof.
  apply (@echo_reachable_next_message_id_positive
    nat Nat.eq_dec direct_two_node_config).
  apply echo_run_reachable.
Qed.

Example direct_echo_public_run_initiator_parent_none :
  echo_ir_initiator_parent_none nat direct_two_node_config
    (ir_run_outcome_state
      (echo_run nat Nat.eq_dec direct_two_node_config 3
        direct_two_node_schedule)).
Proof.
  apply (@echo_reachable_initiator_parent_none
    nat Nat.eq_dec direct_two_node_config).
  apply echo_run_reachable.
Qed.

Example direct_echo_public_run_finished_participants_parented :
  echo_ir_finished_participants_parented nat direct_two_node_config
    (ir_run_outcome_state
      (echo_run nat Nat.eq_dec direct_two_node_config 3
        direct_two_node_schedule)).
Proof.
  apply (@echo_reachable_finished_participants_parented
    nat Nat.eq_dec direct_two_node_config).
  apply echo_run_reachable.
Qed.

Example direct_two_node_neighbors_well_formed :
  echo_ir_config_neighbors_well_formed nat direct_two_node_config.
Proof.
  intros owner [same | [same | impossible]]; subst.
  - cbn [direct_two_node_config echo_ir_pending_valid].
    split.
    + repeat constructor; cbn; tauto.
    + intros neighbor [same | impossible]; [subst | contradiction].
      cbn. tauto.
  - cbn [direct_two_node_config echo_ir_pending_valid].
    split.
    + repeat constructor; cbn; tauto.
    + intros neighbor [same | impossible]; [subst | contradiction].
      cbn. tauto.
  - contradiction.
Qed.

Example direct_echo_public_run_pending_well_formed :
  echo_ir_pending_well_formed nat direct_two_node_config
    (ir_run_outcome_state
      (echo_run nat Nat.eq_dec direct_two_node_config 3
        direct_two_node_schedule)).
Proof.
  apply (@echo_reachable_pending_well_formed
    nat Nat.eq_dec direct_two_node_config).
  - apply direct_two_node_neighbors_well_formed.
  - apply echo_run_reachable.
Qed.

Example direct_echo_public_run_discovered_participants_parented :
  echo_ir_discovered_participants_parented nat direct_two_node_config
    (ir_run_outcome_state
      (echo_run nat Nat.eq_dec direct_two_node_config 3
        direct_two_node_schedule)).
Proof.
  apply (@echo_reachable_discovered_participants_parented
    nat Nat.eq_dec direct_two_node_config).
  apply echo_run_reachable.
Qed.

Example direct_two_node_neighbors_symmetric :
  echo_ir_config_neighbors_symmetric nat direct_two_node_config.
Proof.
  intros left right left_in neighbor.
  destruct left_in as [same | [same | impossible]].
  - subst left. cbn [direct_two_node_config] in neighbor |- *.
    destruct neighbor as [same | impossible]; [subst right | contradiction].
    cbn. tauto.
  - subst left. cbn [direct_two_node_config] in neighbor |- *.
    destruct neighbor as [same | impossible]; [subst right | contradiction].
    cbn. tauto.
  - contradiction.
Qed.

Example direct_echo_public_run_all_configured_reach_initiator :
  forall owner,
    In owner [0; 1] ->
    echo_ir_reaches_initiator nat direct_two_node_config
      (ir_run_outcome_state
        (echo_run nat Nat.eq_dec direct_two_node_config 3
          direct_two_node_schedule)) owner.
Proof.
  intros owner owner_in.
  eapply (@echo_reachable_discovered_reaches_initiator
    nat Nat.eq_dec direct_two_node_config); try eassumption.
  - change (In 0 [0; 1]). now left.
  - apply direct_two_node_neighbors_well_formed.
  - apply direct_two_node_neighbors_symmetric.
  - apply echo_run_reachable.
  - destruct owner_in as [root | [participant | impossible]].
    + now left.
    + subst owner. right. vm_compute. intuition discriminate.
    + contradiction.
Qed.

Example direct_echo_public_run_topology_well_formed :
  echo_ir_topology_well_formed nat direct_two_node_config
    (ir_run_outcome_state
      (echo_run nat Nat.eq_dec direct_two_node_config 3
        direct_two_node_schedule)).
Proof.
  apply (@echo_reachable_topology_well_formed
    nat Nat.eq_dec direct_two_node_config).
  - change (In 0 [0; 1]). now left.
  - apply direct_two_node_neighbors_well_formed.
  - apply direct_two_node_neighbors_symmetric.
  - apply echo_run_reachable.
Qed.

Example direct_echo_public_run_request_edges_unique :
  echo_ir_request_edges_unique nat
    (ir_run_outcome_state
      (echo_run nat Nat.eq_dec direct_two_node_config 3
        direct_two_node_schedule)).
Proof.
  apply (@echo_reachable_request_edges_unique
    nat Nat.eq_dec direct_two_node_config).
  - change (In 0 [0; 1]). now left.
  - apply direct_two_node_neighbors_well_formed.
  - apply direct_two_node_neighbors_symmetric.
  - apply echo_run_reachable.
Qed.
