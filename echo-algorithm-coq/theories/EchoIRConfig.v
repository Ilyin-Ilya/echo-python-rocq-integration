(** * Direct runtime configuration for the generic Echo IR program

    This module constructs the generic IR configuration from the mathematical
    Echo parameters.  It deliberately contains no executable Echo state,
    transition relation, or old/new correspondence relation. *)

From Stdlib Require Import List Bool.
Require Import EchoTopology ProtocolIRTypes EchoIRSignature.

Definition echo_ir_config_fields {node : Type} (initiator : node) :
    ir_config_store node echo_ir_signature :=
  fun field =>
    match field as selected
      return ir_value node
        (signature_config_field_type echo_ir_signature selected) with
    | EchoIRInitiator => IRNodeValue initiator
    end.

Definition make_echo_ir_config {node : Type}
    (initiator : node)
    (all_nodes : list node)
    (adjacent : node -> node -> bool) :
    ir_protocol_config node echo_ir_signature :=
  mkIRProtocolConfig
    all_nodes
    (fun owner => nbrs all_nodes adjacent owner)
    (echo_ir_config_fields initiator).
