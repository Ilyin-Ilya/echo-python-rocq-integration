(** * Legacy-free computed audit of the generic Echo IR spanning tree *)

From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.
Require Import EchoTopology ProtocolIRTypes ProtocolIRRunner
  EchoIRSignature EchoIRConfig EchoIRProgram EchoIRExecutable
  EchoIRSpanningTree EchoIRSafety.

Module DirectTwoNodeConfig <: ECHO_CORRECTNESS_CONFIG.

Definition node := nat.
Definition node_eq := Nat.eq_dec.
Definition initiator := 0.
Definition all_nodes := [0; 1].
Definition adj (left right : nat) : bool :=
  ((left =? 0) && (right =? 1)) ||
  ((left =? 1) && (right =? 0)).

Lemma adj_sym :
  forall left right, adj left right = true -> adj right left = true.
Proof.
  intros left right edge.
  unfold adj in *.
  destruct (Nat.eqb left 0);
    destruct (Nat.eqb left 1);
    destruct (Nat.eqb right 0);
    destruct (Nat.eqb right 1);
    cbn in *; try discriminate; reflexivity.
Qed.

Lemma adj_irrefl : forall owner, adj owner owner = false.
Proof.
  intro owner. unfold adj.
  destruct (Nat.eqb owner 0) eqn:zero;
    destruct (Nat.eqb owner 1) eqn:one; cbn; try reflexivity.
  apply Nat.eqb_eq in zero. apply Nat.eqb_eq in one. lia.
Qed.

Lemma initiator_in_nodes : In initiator all_nodes.
Proof. now left. Qed.

Lemma nodup_nodes : NoDup all_nodes.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

End DirectTwoNodeConfig.

Module DirectTwoNodeSpanning :=
  MakeEchoIRSpanningTree DirectTwoNodeConfig.
Module DirectTwoNodeSafety :=
  MakeEchoIRSafety DirectTwoNodeConfig.

Definition direct_two_node_config :
    ir_protocol_config nat echo_ir_signature :=
  make_echo_ir_config DirectTwoNodeConfig.initiator
    DirectTwoNodeConfig.all_nodes DirectTwoNodeConfig.adj.

Definition direct_two_node_start_certificates :
    ir_start_certificates nat echo_ir_signature :=
  fun field =>
    match field as selected
      return ir_value nat
        (signature_start_certificate_field_type echo_ir_signature selected) with
    | EchoIRStartOrder => IRListNodeValue [1]
    end.

Definition direct_two_node_delivery_certificates :
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
  [IRProtocolStart direct_two_node_start_certificates;
   IRProtocolDeliver 1 direct_two_node_delivery_certificates;
   IRProtocolDeliver 2 direct_two_node_delivery_certificates].

Definition direct_two_node_wave_depth (owner : nat) : nat :=
  if Nat.eq_dec owner 0 then 0 else 1.

Lemma direct_two_node_wave_depth_props :
  direct_two_node_wave_depth 0 = 0 /\
  forall owner,
    In owner [0; 1] -> owner <> 0 ->
    exists parent,
      In parent [0; 1] /\
      DirectTwoNodeConfig.adj owner parent = true /\
      direct_two_node_wave_depth parent < direct_two_node_wave_depth owner.
Proof.
  split.
  - unfold direct_two_node_wave_depth.
    destruct (Nat.eq_dec 0 0); [reflexivity | contradiction].
  - intros owner owner_in nonroot.
    destruct owner_in as [root | [participant | impossible]].
    + exfalso. apply nonroot. now symmetry.
    + subst owner. exists 0. split; [now left |]. split.
      * reflexivity.
      * unfold direct_two_node_wave_depth.
        destruct (Nat.eq_dec 0 0); [|contradiction].
        destruct (Nat.eq_dec 1 0); lia.
    + contradiction.
Qed.

Example direct_two_node_generic_ir_run_completes :
  exists final_state,
    run_ir_protocol Nat.eq_dec direct_two_node_config
      (@echo_ir_program nat) 3 direct_two_node_schedule =
    IRRunComplete final_state 3.
Proof. eexists. vm_compute. reflexivity. Qed.

Example direct_two_node_generic_ir_complete_run_spans :
  exists final_state,
    run_ir_protocol Nat.eq_dec direct_two_node_config
      (@echo_ir_program nat) 3 direct_two_node_schedule =
      IRRunComplete final_state 3 /\
    forall owner,
      In owner [0; 1] ->
      DirectTwoNodeSpanning.echo_ir_reaches_initiator final_state owner.
Proof.
  destruct direct_two_node_generic_ir_run_completes as
    [final_state run_result].
  exists final_state. split; [exact run_result |].
  eapply DirectTwoNodeSpanning.echo_ir_complete_run_builds_spanning_tree.
  - exact direct_two_node_wave_depth_props.
  - exact run_result.
Qed.

Example direct_two_node_generic_ir_complete_root_is_parentless :
  forall final_state,
    run_ir_protocol Nat.eq_dec direct_two_node_config
      (@echo_ir_program nat) 3 direct_two_node_schedule =
      IRRunComplete final_state 3 ->
    DirectTwoNodeSpanning.echo_ir_parent final_state 0 = None.
Proof.
  intros final_state run_result.
  apply DirectTwoNodeSafety.echo_ir_reachable_initiator_parent_none.
  pose proof (run_ir_protocol_reachable Nat.eq_dec direct_two_node_config
    (@echo_ir_program nat) 3 direct_two_node_schedule) as reachable.
  now rewrite run_result in reachable.
Qed.

Print Assumptions
  DirectTwoNodeSpanning.echo_ir_complete_run_builds_spanning_tree.
Print Assumptions direct_two_node_generic_ir_complete_run_spans.
