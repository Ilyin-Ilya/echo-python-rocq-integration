(** * Typed expressions for the protocol-neutral transition IR

    Every expression carries its result type in its Rocq type.  Evaluation can
    fail only when an expression asks for data absent from the external event
    (for example, a message payload during startup); it cannot return a value
    of the wrong IR type. *)

From Stdlib Require Import List Bool Arith Sorting.Permutation.
Import ListNotations.
Require Import ProtocolIRTypes.

Inductive ir_expr
    (node : Type) (signature : protocol_signature) : ir_type -> Type :=
  | IRLiteral : forall kind : ir_type,
      ir_value node kind -> ir_expr node signature kind
  | IRConfigRead : forall field : signature_config_field signature,
      ir_expr node signature
        (signature_config_field_type signature field)
  | IRGlobalRead : forall field : signature_global_field signature,
      ir_expr node signature
        (signature_global_field_type signature field)
  | IRLocalRead : forall field : signature_local_field signature,
      ir_expr node signature IRNode ->
      ir_expr node signature
        (signature_local_field_type signature field)
  | IROptionSomeExpr : ir_expr node signature IRNode ->
      ir_expr node signature IROptionNode
  | IROptionGetExpr : ir_expr node signature IROptionNode ->
      ir_expr node signature IRNode
  | IRMessageIdExpr : ir_expr node signature IRNat
  | IRMessageSenderExpr : ir_expr node signature IRNode
  | IRMessageReceiverExpr : ir_expr node signature IRNode
  | IRMessageKindIs : signature_message_kind signature ->
      ir_expr node signature IRBool
  | IRPayloadRead : forall field : signature_payload_field signature,
      ir_expr node signature
        (signature_payload_field_type signature field)
  | IRStartCertificateRead :
      forall field : signature_start_certificate_field signature,
      ir_expr node signature
        (signature_start_certificate_field_type signature field)
  | IRDeliveryCertificateRead :
      forall field : signature_delivery_certificate_field signature,
      ir_expr node signature
        (signature_delivery_certificate_field_type signature field)
  | IRIsStartExpr : ir_expr node signature IRBool
  | IRIsDeliveryExpr : ir_expr node signature IRBool
  | IRMessageStoreEmptyExpr : ir_expr node signature IRBool
  | IRMessageStoreLengthExpr : ir_expr node signature IRNat
  | IRNextMessageIdExpr : ir_expr node signature IRNat
  | IRNeighborsExpr : ir_expr node signature IRNode ->
      ir_expr node signature IRListNode
  | IRNotExpr : ir_expr node signature IRBool ->
      ir_expr node signature IRBool
  | IRAndExpr :
      ir_expr node signature IRBool ->
      ir_expr node signature IRBool ->
      ir_expr node signature IRBool
  | IROrExpr :
      ir_expr node signature IRBool ->
      ir_expr node signature IRBool ->
      ir_expr node signature IRBool
  | IREqualExpr : forall kind : ir_type,
      ir_expr node signature kind ->
      ir_expr node signature kind ->
      ir_expr node signature IRBool
  | IROptionIsSomeExpr : ir_expr node signature IROptionNode ->
      ir_expr node signature IRBool
  | IRListIsEmptyExpr : ir_expr node signature IRListNode ->
      ir_expr node signature IRBool
  | IRListContainsExpr :
      ir_expr node signature IRNode ->
      ir_expr node signature IRListNode ->
      ir_expr node signature IRBool
  | IRListRemoveExpr :
      ir_expr node signature IRNode ->
      ir_expr node signature IRListNode ->
      ir_expr node signature IRListNode
  | IRListAppendExpr :
      ir_expr node signature IRListNode ->
      ir_expr node signature IRListNode ->
      ir_expr node signature IRListNode
  | IRListPermutationExpr :
      ir_expr node signature IRListNode ->
      ir_expr node signature IRListNode ->
      ir_expr node signature IRBool
  | IRListLengthExpr : ir_expr node signature IRListNode ->
      ir_expr node signature IRNat
  | IRNatAddExpr :
      ir_expr node signature IRNat ->
      ir_expr node signature IRNat ->
      ir_expr node signature IRNat
  | IRNatSuccExpr : ir_expr node signature IRNat ->
      ir_expr node signature IRNat
  | IRAllNodesLocalEqualExpr :
      forall field : signature_local_field signature,
      ir_expr node signature
        (signature_local_field_type signature field) ->
      ir_expr node signature IRBool.

Arguments IRLiteral {node signature kind} _.
Arguments IRConfigRead {node signature} _.
Arguments IRGlobalRead {node signature} _.
Arguments IRLocalRead {node signature} _ _.
Arguments IROptionSomeExpr {node signature} _.
Arguments IROptionGetExpr {node signature} _.
Arguments IRMessageIdExpr {node signature}.
Arguments IRMessageSenderExpr {node signature}.
Arguments IRMessageReceiverExpr {node signature}.
Arguments IRMessageKindIs {node signature} _.
Arguments IRPayloadRead {node signature} _.
Arguments IRStartCertificateRead {node signature} _.
Arguments IRDeliveryCertificateRead {node signature} _.
Arguments IRIsStartExpr {node signature}.
Arguments IRIsDeliveryExpr {node signature}.
Arguments IRMessageStoreEmptyExpr {node signature}.
Arguments IRMessageStoreLengthExpr {node signature}.
Arguments IRNextMessageIdExpr {node signature}.
Arguments IRNeighborsExpr {node signature} _.
Arguments IRNotExpr {node signature} _.
Arguments IRAndExpr {node signature} _ _.
Arguments IROrExpr {node signature} _ _.
Arguments IREqualExpr {node signature kind} _ _.
Arguments IROptionIsSomeExpr {node signature} _.
Arguments IRListIsEmptyExpr {node signature} _.
Arguments IRListContainsExpr {node signature} _ _.
Arguments IRListRemoveExpr {node signature} _ _.
Arguments IRListAppendExpr {node signature} _ _.
Arguments IRListPermutationExpr {node signature} _ _.
Arguments IRListLengthExpr {node signature} _.
Arguments IRNatAddExpr {node signature} _ _.
Arguments IRNatSuccExpr {node signature} _.
Arguments IRAllNodesLocalEqualExpr {node signature} _ _.

Fixpoint ir_node_in
    {node : Type}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (selected : node) (nodes : list node) : bool :=
  match nodes with
  | [] => false
  | candidate :: rest =>
      if node_eq_dec selected candidate
      then true
      else ir_node_in node_eq_dec selected rest
  end.

Fixpoint ir_remove_node
    {node : Type}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (selected : node) (nodes : list node) : list node :=
  match nodes with
  | [] => []
  | candidate :: rest =>
      if node_eq_dec selected candidate
      then rest
      else candidate :: ir_remove_node node_eq_dec selected rest
  end.

Fixpoint ir_extract_node
    {node : Type}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (selected : node) (nodes : list node) : option (list node) :=
  match nodes with
  | [] => None
  | candidate :: rest =>
      if node_eq_dec selected candidate
      then Some rest
      else
        match ir_extract_node node_eq_dec selected rest with
        | Some residual => Some (candidate :: residual)
        | None => None
        end
  end.

(** Order certificates are checked as multisets: each item removes exactly one
    equal item from the other list.  This keeps the operation generic while
    preserving duplicate multiplicities. *)
Fixpoint ir_node_list_permutationb
    {node : Type}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (left right : list node) : bool :=
  match left with
  | [] =>
      match right with
      | [] => true
      | _ :: _ => false
      end
  | selected :: rest =>
      match ir_extract_node node_eq_dec selected right with
      | Some residual =>
          ir_node_list_permutationb node_eq_dec rest residual
      | None => false
      end
  end.

Lemma ir_extract_node_some_permutation
    {node : Type}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (selected : node) (nodes residual : list node) :
  ir_extract_node node_eq_dec selected nodes = Some residual ->
  Permutation nodes (selected :: residual).
Proof.
  revert residual. induction nodes as [|candidate rest IH];
    intros residual extracted; cbn in extracted.
  - discriminate.
  - destruct (node_eq_dec selected candidate) as [equal | different].
    + inversion extracted. subst candidate residual. apply Permutation_refl.
    + destruct (ir_extract_node node_eq_dec selected rest)
        as [tail |] eqn:tail_result; try discriminate.
      inversion extracted. subst residual.
      eapply Permutation_trans.
      * apply perm_skip. now apply IH.
      * apply perm_swap.
Qed.

Lemma ir_extract_node_none_not_in
    {node : Type}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (selected : node) (nodes : list node) :
  ir_extract_node node_eq_dec selected nodes = None ->
  ~ In selected nodes.
Proof.
  induction nodes as [|candidate rest IH]; intro extracted; cbn in *.
  - tauto.
  - destruct (node_eq_dec selected candidate) as [equal | different].
    + discriminate.
    + destruct (ir_extract_node node_eq_dec selected rest)
        eqn:tail_result; try discriminate.
      intros [same | in_rest].
      * apply different. now symmetry.
      * exact (IH eq_refl in_rest).
Qed.

Theorem ir_node_list_permutationb_true_iff
    {node : Type}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (left right : list node) :
  ir_node_list_permutationb node_eq_dec left right = true <->
  Permutation left right.
Proof.
  revert right. induction left as [|selected rest IH]; intro right; cbn.
  - destruct right as [|candidate tail].
    + split; intro; constructor.
    + split.
      * discriminate.
      * intro permutation. now apply Permutation_nil_cons in permutation.
  - destruct (ir_extract_node node_eq_dec selected right)
      as [residual |] eqn:extracted.
    + rewrite IH. split.
      * intro rest_permutation.
        eapply Permutation_trans.
        -- apply perm_skip. exact rest_permutation.
        -- symmetry.
           now apply ir_extract_node_some_permutation in extracted.
      * intro permutation.
        apply Permutation_cons_inv with selected.
        eapply Permutation_trans.
        -- exact permutation.
        -- now apply ir_extract_node_some_permutation in extracted.
    + split.
      * discriminate.
      * intro permutation. exfalso.
        apply (ir_extract_node_none_not_in
          node_eq_dec selected right extracted).
        eapply Permutation_in.
        -- exact permutation.
        -- now left.
Qed.

Definition ir_event_message
    {node : Type} {signature : protocol_signature}
    (event : ir_runtime_event node signature) :
    option (ir_message node signature) :=
  match event with
  | IRRuntimeQuery => None
  | IRRuntimeStart _ => None
  | IRRuntimeDeliver message _ => Some message
  end.

Fixpoint eval_ir_expr
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (state : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    {kind : ir_type}
    (expr : ir_expr node signature kind) : option (ir_value node kind) :=
  match expr with
  | IRLiteral value => Some value
  | IRConfigRead field => Some (ir_config_fields config field)
  | IRGlobalRead field => Some (ir_global_fields state field)
  | IRLocalRead field process_expr =>
      match eval_ir_expr node_eq_dec config state event process_expr with
      | Some (IRNodeValue process) =>
          Some (ir_processes state process field)
      | Some _ => None
      | None => None
      end
  | IROptionSomeExpr operand =>
      match eval_ir_expr node_eq_dec config state event operand with
      | Some (IRNodeValue value) =>
          Some (IROptionNodeValue (Some value))
      | Some _ => None
      | None => None
      end
  | IROptionGetExpr operand =>
      match eval_ir_expr node_eq_dec config state event operand with
      | Some (IROptionNodeValue (Some value)) => Some (IRNodeValue value)
      | Some (IROptionNodeValue None) => None
      | Some _ => None
      | None => None
      end
  | IRMessageIdExpr =>
      match event with
      | IRRuntimeQuery => None
      | IRRuntimeStart _ => None
      | IRRuntimeDeliver message _ =>
          Some (IRNatValue (ir_message_id message))
      end
  | IRMessageSenderExpr =>
      match ir_event_message event with
      | Some message =>
          Some (IRNodeValue (ir_message_sender message))
      | None => None
      end
  | IRMessageReceiverExpr =>
      match ir_event_message event with
      | Some message =>
          Some (IRNodeValue (ir_message_receiver message))
      | None => None
      end
  | IRMessageKindIs expected =>
      match ir_event_message event with
      | Some message =>
          Some (IRBoolValue
            (if signature_message_kind_eq_dec signature
                  (ir_message_kind message) expected
             then true else false))
      | None => None
      end
  | IRPayloadRead field =>
      match ir_event_message event with
      | Some message =>
          ir_payload_lookup field (ir_message_payload message)
      | None => None
      end
  | IRStartCertificateRead field =>
      match event with
      | IRRuntimeQuery => None
      | IRRuntimeStart certificates => Some (certificates field)
      | IRRuntimeDeliver _ _ => None
      end
  | IRDeliveryCertificateRead field =>
      match event with
      | IRRuntimeQuery => None
      | IRRuntimeStart _ => None
      | IRRuntimeDeliver _ certificates => Some (certificates field)
      end
  | IRIsStartExpr =>
      Some (IRBoolValue
        (match event with
         | IRRuntimeQuery => false
         | IRRuntimeStart _ => true
         | IRRuntimeDeliver _ _ => false
         end))
  | IRIsDeliveryExpr =>
      Some (IRBoolValue
        (match event with
         | IRRuntimeQuery => false
         | IRRuntimeStart _ => false
         | IRRuntimeDeliver _ _ => true
         end))
  | IRMessageStoreEmptyExpr =>
      Some (IRBoolValue
        (match ir_message_store state with
         | [] => true
         | _ :: _ => false
         end))
  | IRMessageStoreLengthExpr =>
      Some (IRNatValue (List.length (ir_message_store state)))
  | IRNextMessageIdExpr =>
      Some (IRNatValue (ir_next_message_id state))
  | IRNeighborsExpr process_expr =>
      match eval_ir_expr node_eq_dec config state event process_expr with
      | Some (IRNodeValue process) =>
          Some (IRListNodeValue (ir_config_neighbors config process))
      | Some _ => None
      | None => None
      end
  | IRNotExpr operand =>
      match eval_ir_expr node_eq_dec config state event operand with
      | Some (IRBoolValue value) => Some (IRBoolValue (negb value))
      | Some _ => None
      | None => None
      end
  | IRAndExpr left_expr right_expr =>
      match eval_ir_expr node_eq_dec config state event left_expr,
            eval_ir_expr node_eq_dec config state event right_expr with
      | Some (IRBoolValue left_value), Some (IRBoolValue right_value) =>
          Some (IRBoolValue (andb left_value right_value))
      | _, _ => None
      end
  | IROrExpr left_expr right_expr =>
      match eval_ir_expr node_eq_dec config state event left_expr,
            eval_ir_expr node_eq_dec config state event right_expr with
      | Some (IRBoolValue left_value), Some (IRBoolValue right_value) =>
          Some (IRBoolValue (orb left_value right_value))
      | _, _ => None
      end
  | IREqualExpr left_expr right_expr =>
      match eval_ir_expr node_eq_dec config state event left_expr,
            eval_ir_expr node_eq_dec config state event right_expr with
      | Some left_value, Some right_value =>
          Some (IRBoolValue (ir_value_eqb node_eq_dec left_value right_value))
      | _, _ => None
      end
  | IROptionIsSomeExpr operand =>
      match eval_ir_expr node_eq_dec config state event operand with
      | Some (IROptionNodeValue value) =>
          Some (IRBoolValue
            (match value with Some _ => true | None => false end))
      | Some _ => None
      | None => None
      end
  | IRListIsEmptyExpr operand =>
      match eval_ir_expr node_eq_dec config state event operand with
      | Some (IRListNodeValue value) =>
          Some (IRBoolValue
            (match value with [] => true | _ :: _ => false end))
      | Some _ => None
      | None => None
      end
  | IRListContainsExpr item items =>
      match eval_ir_expr node_eq_dec config state event item,
            eval_ir_expr node_eq_dec config state event items with
      | Some (IRNodeValue item_value), Some (IRListNodeValue item_values) =>
          Some (IRBoolValue (ir_node_in node_eq_dec item_value item_values))
      | _, _ => None
      end
  | IRListRemoveExpr item items =>
      match eval_ir_expr node_eq_dec config state event item,
            eval_ir_expr node_eq_dec config state event items with
      | Some (IRNodeValue item_value), Some (IRListNodeValue item_values) =>
          Some (IRListNodeValue
            (ir_remove_node node_eq_dec item_value item_values))
      | _, _ => None
      end
  | IRListAppendExpr left_expr right_expr =>
      match eval_ir_expr node_eq_dec config state event left_expr,
            eval_ir_expr node_eq_dec config state event right_expr with
      | Some (IRListNodeValue left_value),
        Some (IRListNodeValue right_value) =>
          Some (IRListNodeValue (left_value ++ right_value))
      | _, _ => None
      end
  | IRListPermutationExpr left_expr right_expr =>
      match eval_ir_expr node_eq_dec config state event left_expr,
            eval_ir_expr node_eq_dec config state event right_expr with
      | Some (IRListNodeValue left_value),
        Some (IRListNodeValue right_value) =>
          Some (IRBoolValue
            (ir_node_list_permutationb
              node_eq_dec left_value right_value))
      | _, _ => None
      end
  | IRListLengthExpr operand =>
      match eval_ir_expr node_eq_dec config state event operand with
      | Some (IRListNodeValue value) =>
          Some (IRNatValue (List.length value))
      | Some _ => None
      | None => None
      end
  | IRNatAddExpr left_expr right_expr =>
      match eval_ir_expr node_eq_dec config state event left_expr,
            eval_ir_expr node_eq_dec config state event right_expr with
      | Some (IRNatValue left_value), Some (IRNatValue right_value) =>
          Some (IRNatValue (left_value + right_value))
      | _, _ => None
      end
  | IRNatSuccExpr operand =>
      match eval_ir_expr node_eq_dec config state event operand with
      | Some (IRNatValue value) => Some (IRNatValue (S value))
      | Some _ => None
      | None => None
      end
  | IRAllNodesLocalEqualExpr field expected_expr =>
      match eval_ir_expr
        node_eq_dec config state event expected_expr with
      | Some expected =>
          Some (IRBoolValue
            (forallb
              (fun process =>
                ir_value_eqb node_eq_dec
                  (ir_processes state process field) expected)
              (ir_config_nodes config)))
      | None => None
      end
  end.

(** Expressions cannot distinguish observationally equivalent states.  This
    is stronger than fixed-input determinism and avoids converting functional
    stores to propositional record equality. *)
Theorem eval_ir_expr_respects_state_equivalence
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (left right : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (kind : ir_type)
    (expr : ir_expr node signature kind) :
  ir_states_equivalent left right ->
  eval_ir_expr node_eq_dec config left event expr =
    eval_ir_expr node_eq_dec config right event expr.
Proof.
  intros [processes_equal
    [messages_equal [globals_equal next_id_equal]]].
  induction expr; cbn;
    try rewrite messages_equal;
    try rewrite next_id_equal;
    try rewrite globals_equal;
    try rewrite IHexpr;
    try rewrite IHexpr1, IHexpr2;
    try reflexivity.
  - destruct (eval_ir_expr node_eq_dec config right event expr)
      as [value |] eqn:evaluated; try reflexivity.
    destruct value; try reflexivity.
    now rewrite processes_equal.
  - destruct (eval_ir_expr node_eq_dec config right event expr)
      as [value |] eqn:evaluated; try reflexivity.
    f_equal.
    induction (ir_config_nodes config) as [|process rest IH].
    + reflexivity.
    + cbn. rewrite processes_equal. now inversion IH.
Qed.

Theorem eval_ir_expr_not_both_true
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (state : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (expr : ir_expr node signature IRBool) :
  eval_ir_expr node_eq_dec config state event expr =
    Some (IRBoolValue true) ->
  eval_ir_expr node_eq_dec config state event (IRNotExpr expr) =
    Some (IRBoolValue true) ->
  False.
Proof.
  intros positive negated.
  cbn in negated. rewrite positive in negated. discriminate.
Qed.

(** Fixed-input evaluation is a function.  This theorem is deliberately
    generic and will be reused by rule and transition determinism proofs. *)
Theorem eval_ir_expr_deterministic
    {node : Type} {signature : protocol_signature}
    (node_eq_dec : forall left right : node,
      {left = right} + {left <> right})
    (config : ir_protocol_config node signature)
    (state : ir_protocol_state node signature)
    (event : ir_runtime_event node signature)
    (kind : ir_type)
    (expr : ir_expr node signature kind)
    (left right : ir_value node kind) :
  eval_ir_expr node_eq_dec config state event expr = Some left ->
  eval_ir_expr node_eq_dec config state event expr = Some right ->
  left = right.
Proof.
  intros left_result right_result.
  rewrite left_result in right_result.
  now inversion right_result.
Qed.
