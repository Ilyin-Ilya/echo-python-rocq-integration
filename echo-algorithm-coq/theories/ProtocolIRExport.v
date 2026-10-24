(** * Canonical serialization of generic protocol IR programs

    A protocol supplies finite identifier enumerations and stable atom names.
    This module serializes the typed generic program itself; it contains no
    protocol-specific rule or field names. *)

From Stdlib Require Import List Bool Arith String DecimalString.
Import ListNotations.
Open Scope string_scope.
Require Import ProtocolIRTypes ProtocolIRExpressions ProtocolIRActions
  ProtocolIRInterpreter ProtocolIRRunner.

Record ir_export_descriptor
    (node : Type) (signature : protocol_signature) : Type :=
  mkIRExportDescriptor {
    ir_export_node_atom : node -> string;
    ir_export_local_fields : list (signature_local_field signature);
    ir_export_local_field_atom : signature_local_field signature -> string;
    ir_export_global_fields : list (signature_global_field signature);
    ir_export_global_field_atom : signature_global_field signature -> string;
    ir_export_config_fields : list (signature_config_field signature);
    ir_export_config_field_atom : signature_config_field signature -> string;
    ir_export_message_kinds : list (signature_message_kind signature);
    ir_export_message_kind_atom : signature_message_kind signature -> string;
    ir_export_payload_fields : list (signature_payload_field signature);
    ir_export_payload_field_atom : signature_payload_field signature -> string;
    ir_export_start_certificate_fields :
      list (signature_start_certificate_field signature);
    ir_export_start_certificate_field_atom :
      signature_start_certificate_field signature -> string;
    ir_export_delivery_certificate_fields :
      list (signature_delivery_certificate_field signature);
    ir_export_delivery_certificate_field_atom :
      signature_delivery_certificate_field signature -> string;
    ir_export_rule_ids : list (signature_rule_id signature);
    ir_export_rule_id_atom : signature_rule_id signature -> string
  }.

Arguments mkIRExportDescriptor {node signature}
  _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _.
Arguments ir_export_node_atom {node signature} _ _.
Arguments ir_export_local_fields {node signature} _.
Arguments ir_export_local_field_atom {node signature} _ _.
Arguments ir_export_global_fields {node signature} _.
Arguments ir_export_global_field_atom {node signature} _ _.
Arguments ir_export_config_fields {node signature} _.
Arguments ir_export_config_field_atom {node signature} _ _.
Arguments ir_export_message_kinds {node signature} _.
Arguments ir_export_message_kind_atom {node signature} _ _.
Arguments ir_export_payload_fields {node signature} _.
Arguments ir_export_payload_field_atom {node signature} _ _.
Arguments ir_export_start_certificate_fields {node signature} _.
Arguments ir_export_start_certificate_field_atom {node signature} _ _.
Arguments ir_export_delivery_certificate_fields {node signature} _.
Arguments ir_export_delivery_certificate_field_atom {node signature} _ _.
Arguments ir_export_rule_ids {node signature} _.
Arguments ir_export_rule_id_atom {node signature} _ _.

Definition ir_bool_atom (value : bool) : string :=
  if value then "true" else "false".

Definition ir_nat_atom (value : nat) : string :=
  NilEmpty.string_of_uint (Nat.to_uint value).

Definition ir_type_atom (kind : ir_type) : string :=
  match kind with
  | IRBool => "bool"
  | IRNat => "nat"
  | IRNode => "node"
  | IROptionNode => "option-node"
  | IRListNode => "list-node"
  | IRMessageRef => "message-ref"
  end.

Definition ir_unary (head argument : string) : string :=
  "(" ++ head ++ " " ++ argument ++ ")".

Definition ir_binary (head left right : string) : string :=
  "(" ++ head ++ " " ++ left ++ " " ++ right ++ ")".

Definition ir_ternary
    (head first second third : string) : string :=
  "(" ++ head ++ " " ++ first ++ " " ++ second ++ " " ++ third ++ ")".

Fixpoint ir_atoms_body
    {identifier : Type}
    (atom : identifier -> string)
    (identifiers : list identifier) : string :=
  match identifiers with
  | [] => ""
  | identifier :: rest =>
      " " ++ atom identifier ++ ir_atoms_body atom rest
  end.

Definition ir_atoms_sexpr
    {identifier : Type}
    (head : string)
    (atom : identifier -> string)
    (identifiers : list identifier) : string :=
  "(" ++ head ++ ir_atoms_body atom identifiers ++ ")".

(** The capability manifest is deliberately linked to the actual typed
    syntax by exhaustive constructor classifiers. Adding an expression or
    action constructor therefore makes this module fail to compile until the
    cross-language manifest is updated. *)

Definition ir_all_types : list ir_type :=
  [IRBool; IRNat; IRNode; IROptionNode; IRListNode; IRMessageRef].

Definition ir_expression_constructors : list string :=
  ["literal"; "config"; "global"; "local"; "option-some"; "option-get";
   "message-id"; "message-sender"; "message-receiver";
   "message-kind-is"; "payload"; "start-certificate";
   "delivery-certificate"; "is-start"; "is-delivery";
   "message-store-empty"; "message-store-length"; "next-message-id";
   "neighbors"; "not"; "and"; "or"; "equal"; "option-is-some";
   "list-is-empty"; "list-contains"; "list-remove"; "list-append";
   "list-permutation"; "list-length"; "nat-add"; "nat-succ";
   "all-nodes-local-equal"].

Definition ir_action_constructors : list string :=
  ["skip"; "set-global"; "set-local"; "remove-selected-message";
   "emit"; "emit-many"; "sequence"].

Definition ir_event_pattern_constructors : list string :=
  ["start"; "deliver"].

Definition ir_expr_constructor_atom
    {node : Type} {signature : protocol_signature} {kind : ir_type}
    (expr : ir_expr node signature kind) : string :=
  match expr with
  | IRLiteral _ => "literal"
  | IRConfigRead _ => "config"
  | IRGlobalRead _ => "global"
  | IRLocalRead _ _ => "local"
  | IROptionSomeExpr _ => "option-some"
  | IROptionGetExpr _ => "option-get"
  | IRMessageIdExpr => "message-id"
  | IRMessageSenderExpr => "message-sender"
  | IRMessageReceiverExpr => "message-receiver"
  | IRMessageKindIs _ => "message-kind-is"
  | IRPayloadRead _ => "payload"
  | IRStartCertificateRead _ => "start-certificate"
  | IRDeliveryCertificateRead _ => "delivery-certificate"
  | IRIsStartExpr => "is-start"
  | IRIsDeliveryExpr => "is-delivery"
  | IRMessageStoreEmptyExpr => "message-store-empty"
  | IRMessageStoreLengthExpr => "message-store-length"
  | IRNextMessageIdExpr => "next-message-id"
  | IRNeighborsExpr _ => "neighbors"
  | IRNotExpr _ => "not"
  | IRAndExpr _ _ => "and"
  | IROrExpr _ _ => "or"
  | IREqualExpr _ _ => "equal"
  | IROptionIsSomeExpr _ => "option-is-some"
  | IRListIsEmptyExpr _ => "list-is-empty"
  | IRListContainsExpr _ _ => "list-contains"
  | IRListRemoveExpr _ _ => "list-remove"
  | IRListAppendExpr _ _ => "list-append"
  | IRListPermutationExpr _ _ => "list-permutation"
  | IRListLengthExpr _ => "list-length"
  | IRNatAddExpr _ _ => "nat-add"
  | IRNatSuccExpr _ => "nat-succ"
  | IRAllNodesLocalEqualExpr _ _ => "all-nodes-local-equal"
  end.

Definition ir_action_constructor_atom
    {node : Type} {signature : protocol_signature}
    (action : ir_action node signature) : string :=
  match action with
  | IRSkipAction => "skip"
  | IRSetGlobalAction _ _ => "set-global"
  | IRSetLocalAction _ _ _ => "set-local"
  | IRRemoveSelectedMessageAction => "remove-selected-message"
  | IREmitAction _ _ _ _ => "emit"
  | IREmitManyAction _ _ _ _ => "emit-many"
  | IRSequenceAction _ _ => "sequence"
  end.

Lemma ir_type_atom_is_declared (kind : ir_type) :
  In kind ir_all_types.
Proof. destruct kind; cbv [ir_all_types In]; intuition. Qed.

Lemma ir_expr_constructor_atom_is_declared
    {node : Type} {signature : protocol_signature} {kind : ir_type}
    (expr : ir_expr node signature kind) :
  In (ir_expr_constructor_atom expr) ir_expression_constructors.
Proof.
  unfold ir_expression_constructors.
  destruct expr; simpl; auto 40.
Qed.

Lemma ir_action_constructor_atom_is_declared
    {node : Type} {signature : protocol_signature}
    (action : ir_action node signature) :
  In (ir_action_constructor_atom action) ir_action_constructors.
Proof.
  unfold ir_action_constructors.
  destruct action; simpl; auto 10.
Qed.

Definition ir_capability_manifest_sexpr : string :=
  "(protocol-ir-capabilities " ++
    ir_unary "schema-version" "1" ++ " " ++
    ir_unary "ir-version" "1" ++ " " ++
    ir_atoms_sexpr "types" ir_type_atom ir_all_types ++ " " ++
    ir_atoms_sexpr "expressions" (fun atom => atom)
      ir_expression_constructors ++ " " ++
    ir_atoms_sexpr "actions" (fun atom => atom)
      ir_action_constructors ++ " " ++
    ir_atoms_sexpr "event-patterns" (fun atom => atom)
      ir_event_pattern_constructors ++ ")".

Fixpoint ir_nodes_body
    {node : Type} (node_atom : node -> string) (nodes : list node) : string :=
  match nodes with
  | [] => ""
  | node :: rest => " " ++ node_atom node ++ ir_nodes_body node_atom rest
  end.

Definition ir_value_sexpr
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    {kind : ir_type}
    (value : ir_value node kind) : string :=
  match value with
  | IRBoolValue boolean => ir_unary "bool" (ir_bool_atom boolean)
  | IRNatValue natural => ir_unary "nat" (ir_nat_atom natural)
  | IRNodeValue selected =>
      ir_unary "node" (ir_export_node_atom descriptor selected)
  | IROptionNodeValue optional =>
      match optional with
      | None => ir_unary "option-node" "none"
      | Some selected =>
          ir_unary "option-node"
            (ir_unary "some" (ir_export_node_atom descriptor selected))
      end
  | IRListNodeValue nodes =>
      "(list-node" ++ ir_nodes_body (ir_export_node_atom descriptor) nodes ++ ")"
  | IRMessageRefValue identifier =>
      ir_unary "message-ref" (ir_nat_atom identifier)
  end.

Fixpoint ir_local_field_declarations
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (fields : list (signature_local_field signature)) : string :=
  match fields with
  | [] => ""
  | field :: rest =>
      " (field " ++ ir_export_local_field_atom descriptor field ++ " " ++
        ir_type_atom (signature_local_field_type signature field) ++ ")" ++
        ir_local_field_declarations descriptor rest
  end.

Fixpoint ir_global_field_declarations
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (fields : list (signature_global_field signature)) : string :=
  match fields with
  | [] => ""
  | field :: rest =>
      " (field " ++ ir_export_global_field_atom descriptor field ++ " " ++
        ir_type_atom (signature_global_field_type signature field) ++ ")" ++
        ir_global_field_declarations descriptor rest
  end.

Fixpoint ir_config_field_declarations
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (fields : list (signature_config_field signature)) : string :=
  match fields with
  | [] => ""
  | field :: rest =>
      " (field " ++ ir_export_config_field_atom descriptor field ++ " " ++
        ir_type_atom (signature_config_field_type signature field) ++ ")" ++
        ir_config_field_declarations descriptor rest
  end.

Fixpoint ir_payload_field_declarations
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (fields : list (signature_payload_field signature)) : string :=
  match fields with
  | [] => ""
  | field :: rest =>
      " (field " ++ ir_export_payload_field_atom descriptor field ++ " " ++
        ir_type_atom (signature_payload_field_type signature field) ++ ")" ++
        ir_payload_field_declarations descriptor rest
  end.

Fixpoint ir_start_certificate_field_declarations
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (fields : list (signature_start_certificate_field signature)) : string :=
  match fields with
  | [] => ""
  | field :: rest =>
      " (field " ++
        ir_export_start_certificate_field_atom descriptor field ++ " " ++
        ir_type_atom
          (signature_start_certificate_field_type signature field) ++ ")" ++
        ir_start_certificate_field_declarations descriptor rest
  end.

Fixpoint ir_delivery_certificate_field_declarations
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (fields : list (signature_delivery_certificate_field signature)) : string :=
  match fields with
  | [] => ""
  | field :: rest =>
      " (field " ++
        ir_export_delivery_certificate_field_atom descriptor field ++ " " ++
        ir_type_atom
          (signature_delivery_certificate_field_type signature field) ++ ")" ++
        ir_delivery_certificate_field_declarations descriptor rest
  end.

Definition ir_signature_sexpr
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature) : string :=
  "(signature " ++
    "(local-fields" ++
      ir_local_field_declarations descriptor
        (ir_export_local_fields descriptor) ++ ") " ++
    "(global-fields" ++
      ir_global_field_declarations descriptor
        (ir_export_global_fields descriptor) ++ ") " ++
    "(config-fields" ++
      ir_config_field_declarations descriptor
        (ir_export_config_fields descriptor) ++ ") " ++
    ir_atoms_sexpr "message-kinds"
      (ir_export_message_kind_atom descriptor)
      (ir_export_message_kinds descriptor) ++ " " ++
    "(payload-fields" ++
      ir_payload_field_declarations descriptor
        (ir_export_payload_fields descriptor) ++ ") " ++
    "(start-certificate-fields" ++
      ir_start_certificate_field_declarations descriptor
        (ir_export_start_certificate_fields descriptor) ++ ") " ++
    "(delivery-certificate-fields" ++
      ir_delivery_certificate_field_declarations descriptor
        (ir_export_delivery_certificate_fields descriptor) ++ ") " ++
    ir_atoms_sexpr "rule-ids"
      (ir_export_rule_id_atom descriptor)
      (ir_export_rule_ids descriptor) ++ ")".

Fixpoint ir_initial_local_fields_body
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (initial : ir_local_store node signature)
    (fields : list (signature_local_field signature)) : string :=
  match fields with
  | [] => ""
  | field :: rest =>
      " (field " ++ ir_export_local_field_atom descriptor field ++ " " ++
        ir_value_sexpr descriptor (initial field) ++ ")" ++
        ir_initial_local_fields_body descriptor initial rest
  end.

Fixpoint ir_initial_global_fields_body
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (initial : ir_global_store node signature)
    (fields : list (signature_global_field signature)) : string :=
  match fields with
  | [] => ""
  | field :: rest =>
      " (field " ++ ir_export_global_field_atom descriptor field ++ " " ++
        ir_value_sexpr descriptor (initial field) ++ ")" ++
        ir_initial_global_fields_body descriptor initial rest
  end.

(** Runtime serializers are protocol-neutral.  They enumerate only the nodes
    and typed identifiers supplied by the export descriptor; they do not
    interpret protocol rules or reconstruct behavior. *)
Fixpoint ir_payload_store_body
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (payload : ir_payload_store node signature) : string :=
  match payload with
  | [] => ""
  | mkIRPayloadEntry field value :: rest =>
      " (field " ++ ir_export_payload_field_atom descriptor field ++ " " ++
        ir_value_sexpr descriptor value ++ ")" ++
        ir_payload_store_body descriptor rest
  end.

Definition ir_payload_store_sexpr
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (payload : ir_payload_store node signature) : string :=
  "(payload" ++ ir_payload_store_body descriptor payload ++ ")".

Definition ir_message_sexpr
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (message : ir_message node signature) : string :=
  "(message " ++ ir_nat_atom (ir_message_id message) ++ " " ++
    ir_export_message_kind_atom descriptor (ir_message_kind message) ++ " " ++
    ir_export_node_atom descriptor (ir_message_sender message) ++ " " ++
    ir_export_node_atom descriptor (ir_message_receiver message) ++ " " ++
    ir_payload_store_sexpr descriptor (ir_message_payload message) ++ ")".

Fixpoint ir_messages_body
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (messages : list (ir_message node signature)) : string :=
  match messages with
  | [] => ""
  | message :: rest =>
      " " ++ ir_message_sexpr descriptor message ++
        ir_messages_body descriptor rest
  end.

Fixpoint ir_processes_body
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (state : ir_protocol_state node signature)
    (nodes : list node) : string :=
  match nodes with
  | [] => ""
  | process :: rest =>
      " (process " ++ ir_export_node_atom descriptor process ++
        " (local-fields" ++
        ir_initial_local_fields_body descriptor
          (ir_processes state process)
          (ir_export_local_fields descriptor) ++ "))" ++
        ir_processes_body descriptor state rest
  end.

Definition ir_state_sexpr
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (nodes : list node)
    (state : ir_protocol_state node signature) : string :=
  "(state (processes" ++ ir_processes_body descriptor state nodes ++ ") " ++
    "(messages" ++
      ir_messages_body descriptor (ir_message_store state) ++ ") " ++
    "(global-fields" ++
      ir_initial_global_fields_body descriptor
        (ir_global_fields state) (ir_export_global_fields descriptor) ++ ") " ++
    ir_unary "next-message-id"
      (ir_nat_atom (ir_next_message_id state)) ++ ")".

Fixpoint ir_config_fields_body
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (config : ir_protocol_config node signature)
    (fields : list (signature_config_field signature)) : string :=
  match fields with
  | [] => ""
  | field :: rest =>
      " (field " ++ ir_export_config_field_atom descriptor field ++ " " ++
        ir_value_sexpr descriptor (ir_config_fields config field) ++ ")" ++
        ir_config_fields_body descriptor config rest
  end.

Fixpoint ir_neighbor_rows_body
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (config : ir_protocol_config node signature)
    (nodes : list node) : string :=
  match nodes with
  | [] => ""
  | owner :: rest =>
      " (neighbors " ++ ir_export_node_atom descriptor owner ++
        ir_nodes_body (ir_export_node_atom descriptor)
          (ir_config_neighbors config owner) ++ ")" ++
        ir_neighbor_rows_body descriptor config rest
  end.

Definition ir_config_sexpr
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (config : ir_protocol_config node signature) : string :=
  "(config " ++
    ir_atoms_sexpr "nodes" (ir_export_node_atom descriptor)
      (ir_config_nodes config) ++ " " ++
    "(topology" ++
      ir_neighbor_rows_body descriptor config (ir_config_nodes config) ++ ") " ++
    "(config-fields" ++
      ir_config_fields_body descriptor config
        (ir_export_config_fields descriptor) ++ "))".

Fixpoint ir_start_certificates_body
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (certificates : ir_start_certificates node signature)
    (fields : list (signature_start_certificate_field signature)) : string :=
  match fields with
  | [] => ""
  | field :: rest =>
      " (field " ++
        ir_export_start_certificate_field_atom descriptor field ++ " " ++
        ir_value_sexpr descriptor (certificates field) ++ ")" ++
        ir_start_certificates_body descriptor certificates rest
  end.

Fixpoint ir_delivery_certificates_body
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (certificates : ir_delivery_certificates node signature)
    (fields : list (signature_delivery_certificate_field signature)) : string :=
  match fields with
  | [] => ""
  | field :: rest =>
      " (field " ++
        ir_export_delivery_certificate_field_atom descriptor field ++ " " ++
        ir_value_sexpr descriptor (certificates field) ++ ")" ++
        ir_delivery_certificates_body descriptor certificates rest
  end.

Definition ir_external_event_sexpr
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (event : ir_external_event node signature) : string :=
  match event with
  | IRProtocolStart certificates =>
      "(start (certificates" ++
        ir_start_certificates_body descriptor certificates
          (ir_export_start_certificate_fields descriptor) ++ "))"
  | IRProtocolDeliver identifier certificates =>
      "(deliver " ++ ir_nat_atom identifier ++ " (certificates" ++
        ir_delivery_certificates_body descriptor certificates
          (ir_export_delivery_certificate_fields descriptor) ++ "))"
  end.

Fixpoint ir_external_events_body
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (events : list (ir_external_event node signature)) : string :=
  match events with
  | [] => ""
  | event :: rest =>
      " " ++ ir_external_event_sexpr descriptor event ++
        ir_external_events_body descriptor rest
  end.

Definition ir_external_events_sexpr
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (events : list (ir_external_event node signature)) : string :=
  "(events" ++ ir_external_events_body descriptor events ++ ")".

Definition ir_step_error_atom (error : ir_step_error) : string :=
  match error with
  | IRUnqueuedMessage => "unqueued-message"
  | IRNoEnabledRule => "no-enabled-rule"
  | IRAmbiguousEnabledRules => "ambiguous-enabled-rules"
  | IRMalformedGuard => "malformed-guard"
  | IRMalformedAction => "malformed-action"
  end.

Definition ir_step_result_sexpr
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (nodes : list node)
    (result : ir_step_result node signature) : string :=
  match result with
  | IRStepSuccess rule successor =>
      "(success " ++ ir_export_rule_id_atom descriptor rule ++ " " ++
        ir_state_sexpr descriptor nodes successor ++ ")"
  | IRStepFailure error =>
      ir_unary "failure" (ir_step_error_atom error)
  end.

Definition ir_run_error_sexpr (error : ir_run_error) : string :=
  match error with
  | IRCompletionPredicateMalformed => "completion-predicate-malformed"
  | IRStuckPredicateMalformed => "stuck-predicate-malformed"
  | IRTransitionRejected step_error =>
      ir_unary "transition-rejected" (ir_step_error_atom step_error)
  end.

Definition ir_optional_event_sexpr
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (event : option (ir_external_event node signature)) : string :=
  match event with
  | None => "none"
  | Some selected => ir_unary "some" (ir_external_event_sexpr descriptor selected)
  end.

Definition ir_run_outcome_sexpr
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (nodes : list node)
    (outcome : ir_run_outcome node signature) : string :=
  match outcome with
  | IRRunComplete state steps =>
      "(complete " ++ ir_nat_atom steps ++ " " ++
        ir_state_sexpr descriptor nodes state ++ ")"
  | IRRunStuck state steps =>
      "(stuck " ++ ir_nat_atom steps ++ " " ++
        ir_state_sexpr descriptor nodes state ++ ")"
  | IRRunScheduleExhausted state steps =>
      "(schedule-exhausted " ++ ir_nat_atom steps ++ " " ++
        ir_state_sexpr descriptor nodes state ++ ")"
  | IRRunBounded state steps =>
      "(bounded " ++ ir_nat_atom steps ++ " " ++
        ir_state_sexpr descriptor nodes state ++ ")"
  | IRRunInvalid state event error steps =>
      "(invalid " ++ ir_nat_atom steps ++ " " ++
        ir_optional_event_sexpr descriptor event ++ " " ++
        ir_run_error_sexpr error ++ " " ++
        ir_state_sexpr descriptor nodes state ++ ")"
  end.

Fixpoint ir_expr_sexpr
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    {kind : ir_type}
    (expr : ir_expr node signature kind) : string :=
  match expr with
  | IRLiteral value => ir_unary "literal" (ir_value_sexpr descriptor value)
  | IRConfigRead field =>
      ir_unary "config" (ir_export_config_field_atom descriptor field)
  | IRGlobalRead field =>
      ir_unary "global" (ir_export_global_field_atom descriptor field)
  | IRLocalRead field process =>
      ir_binary "local" (ir_expr_sexpr descriptor process)
        (ir_export_local_field_atom descriptor field)
  | IROptionSomeExpr operand =>
      ir_unary "option-some" (ir_expr_sexpr descriptor operand)
  | IROptionGetExpr operand =>
      ir_unary "option-get" (ir_expr_sexpr descriptor operand)
  | IRMessageIdExpr => "message-id"
  | IRMessageSenderExpr => "message-sender"
  | IRMessageReceiverExpr => "message-receiver"
  | IRMessageKindIs message_kind =>
      ir_unary "message-kind-is"
        (ir_export_message_kind_atom descriptor message_kind)
  | IRPayloadRead field =>
      ir_unary "payload" (ir_export_payload_field_atom descriptor field)
  | IRStartCertificateRead field =>
      ir_unary "start-certificate"
        (ir_export_start_certificate_field_atom descriptor field)
  | IRDeliveryCertificateRead field =>
      ir_unary "delivery-certificate"
        (ir_export_delivery_certificate_field_atom descriptor field)
  | IRIsStartExpr => "is-start"
  | IRIsDeliveryExpr => "is-delivery"
  | IRMessageStoreEmptyExpr => "message-store-empty"
  | IRMessageStoreLengthExpr => "message-store-length"
  | IRNextMessageIdExpr => "next-message-id"
  | IRNeighborsExpr process =>
      ir_unary "neighbors" (ir_expr_sexpr descriptor process)
  | IRNotExpr operand => ir_unary "not" (ir_expr_sexpr descriptor operand)
  | IRAndExpr left_expr right_expr =>
      ir_binary "and" (ir_expr_sexpr descriptor left_expr)
        (ir_expr_sexpr descriptor right_expr)
  | IROrExpr left_expr right_expr =>
      ir_binary "or" (ir_expr_sexpr descriptor left_expr)
        (ir_expr_sexpr descriptor right_expr)
  | IREqualExpr left_expr right_expr =>
      ir_binary "equal" (ir_expr_sexpr descriptor left_expr)
        (ir_expr_sexpr descriptor right_expr)
  | IROptionIsSomeExpr operand =>
      ir_unary "option-is-some" (ir_expr_sexpr descriptor operand)
  | IRListIsEmptyExpr operand =>
      ir_unary "list-is-empty" (ir_expr_sexpr descriptor operand)
  | IRListContainsExpr item items =>
      ir_binary "list-contains" (ir_expr_sexpr descriptor item)
        (ir_expr_sexpr descriptor items)
  | IRListRemoveExpr item items =>
      ir_binary "list-remove" (ir_expr_sexpr descriptor item)
        (ir_expr_sexpr descriptor items)
  | IRListAppendExpr left_expr right_expr =>
      ir_binary "list-append" (ir_expr_sexpr descriptor left_expr)
        (ir_expr_sexpr descriptor right_expr)
  | IRListPermutationExpr left_expr right_expr =>
      ir_binary "list-permutation" (ir_expr_sexpr descriptor left_expr)
        (ir_expr_sexpr descriptor right_expr)
  | IRListLengthExpr operand =>
      ir_unary "list-length" (ir_expr_sexpr descriptor operand)
  | IRNatAddExpr left_expr right_expr =>
      ir_binary "nat-add" (ir_expr_sexpr descriptor left_expr)
        (ir_expr_sexpr descriptor right_expr)
  | IRNatSuccExpr operand =>
      ir_unary "nat-succ" (ir_expr_sexpr descriptor operand)
  | IRAllNodesLocalEqualExpr field expected =>
      ir_binary "all-nodes-local-equal"
        (ir_export_local_field_atom descriptor field)
        (ir_expr_sexpr descriptor expected)
  end.

Fixpoint ir_payload_exprs_body
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (payload : ir_payload_exprs node signature) : string :=
  match payload with
  | [] => ""
  | mkIRPayloadExprEntry field expr :: rest =>
      " (field " ++ ir_export_payload_field_atom descriptor field ++ " " ++
        ir_expr_sexpr descriptor expr ++ ")" ++
        ir_payload_exprs_body descriptor rest
  end.

Fixpoint ir_action_sexpr
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (action : ir_action node signature) : string :=
  match action with
  | IRSkipAction => "skip"
  | IRSetGlobalAction field value =>
      ir_binary "set-global"
        (ir_export_global_field_atom descriptor field)
        (ir_expr_sexpr descriptor value)
  | IRSetLocalAction process field value =>
      ir_ternary "set-local"
        (ir_expr_sexpr descriptor process)
        (ir_export_local_field_atom descriptor field)
        (ir_expr_sexpr descriptor value)
  | IRRemoveSelectedMessageAction => "remove-selected-message"
  | IREmitAction message_kind sender receiver payload =>
      "(emit " ++ ir_export_message_kind_atom descriptor message_kind ++ " " ++
        ir_expr_sexpr descriptor sender ++ " " ++
        ir_expr_sexpr descriptor receiver ++ " (payload" ++
        ir_payload_exprs_body descriptor payload ++ "))"
  | IREmitManyAction message_kind sender receivers payload =>
      "(emit-many " ++ ir_export_message_kind_atom descriptor message_kind ++
        " " ++ ir_expr_sexpr descriptor sender ++ " " ++
        ir_expr_sexpr descriptor receivers ++ " (payload" ++
        ir_payload_exprs_body descriptor payload ++ "))"
  | IRSequenceAction first second =>
      ir_binary "sequence" (ir_action_sexpr descriptor first)
        (ir_action_sexpr descriptor second)
  end.

Definition ir_event_pattern_sexpr
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (pattern : ir_event_pattern signature) : string :=
  match pattern with
  | IRStartPattern => "start"
  | IRDeliveryPattern message_kind =>
      ir_unary "deliver"
        (ir_export_message_kind_atom descriptor message_kind)
  end.

Fixpoint ir_guards_body
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (guards : list (ir_expr node signature IRBool)) : string :=
  match guards with
  | [] => ""
  | guard :: rest =>
      " " ++ ir_expr_sexpr descriptor guard ++
        ir_guards_body descriptor rest
  end.

Definition ir_rule_sexpr
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (rule : ir_rule node signature) : string :=
  "(rule " ++ ir_export_rule_id_atom descriptor (ir_rule_id rule) ++ " " ++
    ir_event_pattern_sexpr descriptor (ir_rule_pattern rule) ++
    " (guards" ++ ir_guards_body descriptor (ir_rule_guards rule) ++ ") " ++
    ir_action_sexpr descriptor (ir_rule_action rule) ++ ")".

Fixpoint ir_rules_body
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (rules : list (ir_rule node signature)) : string :=
  match rules with
  | [] => ""
  | rule :: rest =>
      " " ++ ir_rule_sexpr descriptor rule ++
        ir_rules_body descriptor rest
  end.

Definition ir_program_sexpr
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (program : ir_protocol_program node signature) : string :=
  "(program " ++
    "(initial " ++
      "(local-fields" ++
        ir_initial_local_fields_body descriptor
          (ir_program_initial_local program)
          (ir_export_local_fields descriptor) ++ ") " ++
      "(global-fields" ++
        ir_initial_global_fields_body descriptor
          (ir_program_initial_global program)
          (ir_export_global_fields descriptor) ++ ") " ++
      ir_unary "next-message-id"
        (ir_nat_atom (ir_program_initial_next_message_id program)) ++ ") " ++
    "(rules" ++
      ir_rules_body descriptor (ir_program_rules program) ++ ") " ++
    ir_unary "complete"
      (ir_expr_sexpr descriptor (ir_program_complete program)) ++ " " ++
    ir_unary "stuck"
      (ir_expr_sexpr descriptor (ir_program_stuck program)) ++ ")".

Definition ir_protocol_envelope_sexpr
    {node : Type} {signature : protocol_signature}
    (descriptor : ir_export_descriptor node signature)
    (program : ir_protocol_program node signature) : string :=
  "(protocol-ir " ++
    ir_unary "schema-version"
      (ir_nat_atom (ir_program_schema_version program)) ++ " " ++
    ir_unary "ir-version"
      (ir_nat_atom (ir_program_ir_version program)) ++ " " ++
    ir_unary "protocol-id" (ir_program_id program) ++ " " ++
    ir_signature_sexpr descriptor ++ " " ++
    ir_program_sexpr descriptor program ++ ")".
