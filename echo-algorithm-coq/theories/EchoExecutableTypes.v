(** * Language-neutral data for the executable Echo algorithm

    These are the only concrete state and event types used by the executable
    rule program and its refinement proof.

    [EchoAlgorithm.echo_state] already names the older abstract proof model,
    so the concrete state is called [executable_echo_state] until that model is
    retired from the maintained proof chain. *)

From Stdlib Require Import List Bool Arith.
Import ListNotations.

Section EchoExecutableTypes.

Variable node : Type.

Inductive echo_kind : Type :=
  | EchoRequest
  | EchoReply.

Definition echo_kind_eq_dec
    (left right : echo_kind) : {left = right} + {left <> right}.
Proof. decide equality. Defined.

Record echo_message : Type := mkEchoMessage {
  message_id       : nat;
  message_kind     : echo_kind;
  message_sender   : node;
  message_receiver : node
}.

Record echo_process : Type := mkEchoProcess {
  process_parent   : option node;
  process_pending  : list node;
  process_finished : bool
}.

Record executable_echo_state : Type := mkExecutableEchoState {
  processes       : node -> echo_process;
  message_store   : list echo_message;
  started         : bool;
  next_message_id : nat
}.

(** An event records the scheduler-selected branch and the order-sensitive
    witnesses required by that branch. *)
Inductive echo_event : Type :=
  | EchoStart (ordered_neighbors : list node)
  | EchoFirstRequestNonLeaf
      (message : echo_message) (ordered_forwards : list node)
  | EchoFirstRequestLeaf (message : echo_message)
  | EchoRepeatedRequest (message : echo_message)
  | EchoInitiatorRequest (message : echo_message)
  | EchoParticipantReplyMore (message : echo_message) (parent : node)
  | EchoParticipantReplyFinal (message : echo_message) (parent : node)
  | EchoInitiatorReplyMore (message : echo_message)
  | EchoInitiatorReplyFinal (message : echo_message).

(** Static topology data.  Decidable node equality remains an explicit
    parameter to executable functions because it is computational evidence,
    not protocol state. *)
Record echo_config : Type := mkEchoConfig {
  config_initiator : node;
  config_nodes     : list node;
  config_adjacent  : node -> node -> bool
}.

(** Pure state-update vocabulary used by the rule interpreter. *)
Record echo_outbound : Type := mkEchoOutbound {
  outbound_kind     : echo_kind;
  outbound_receiver : node
}.

Definition initial_echo_process : echo_process :=
  mkEchoProcess None [] false.

Definition configured_processes_initial
    (config : echo_config) (state : executable_echo_state) : Prop :=
  forall n,
    In n (config_nodes config) ->
    processes state n = initial_echo_process.

Definition echo_initial_on
    (config : echo_config) (state : executable_echo_state) : Prop :=
  started state = false /\
  configured_processes_initial config state /\
  message_store state = [] /\
  next_message_id state = 1.

Definition initial_executable_echo_state : executable_echo_state :=
  mkExecutableEchoState (fun _ => initial_echo_process) [] false 1.

Lemma initial_executable_echo_state_valid (config : echo_config) :
  echo_initial_on config initial_executable_echo_state.
Proof.
  repeat split; try reflexivity.
Qed.

Definition update_process
    (node_eq : forall (n m : node), {n = m} + {n <> m})
    (roles : node -> echo_process)
    (target : node)
    (new_process : echo_process) : node -> echo_process :=
  fun candidate =>
    if node_eq target candidate then new_process else roles candidate.

Fixpoint remove_echo_node
    (node_eq : forall (n m : node), {n = m} + {n <> m})
    (target : node) (nodes : list node) : list node :=
  match nodes with
  | [] => []
  | candidate :: rest =>
      if node_eq target candidate
      then rest
      else candidate :: remove_echo_node node_eq target rest
  end.

Fixpoint remove_echo_message
    (selected_id : nat)
    (messages : list echo_message) : list echo_message :=
  match messages with
  | [] => []
  | message :: rest =>
      if Nat.eqb selected_id (message_id message)
      then rest
      else message :: remove_echo_message selected_id rest
  end.

Fixpoint materialize_echo_outbound
    (next_id : nat)
    (sender : node)
    (outbound : list echo_outbound) : list echo_message :=
  match outbound with
  | [] => []
  | item :: rest =>
      mkEchoMessage next_id (outbound_kind item) sender
        (outbound_receiver item)
        :: materialize_echo_outbound (S next_id) sender rest
  end.

Definition next_echo_message_id_after
    (next_id : nat) (outbound : list echo_outbound) : nat :=
  next_id + List.length outbound.

Definition apply_echo_delivery
    (node_eq : forall (n m : node), {n = m} + {n <> m})
    (state : executable_echo_state)
    (message : echo_message)
    (new_process : echo_process)
    (outbound : list echo_outbound) : executable_echo_state :=
  let receiver := message_receiver message in
  mkExecutableEchoState
    (update_process node_eq (processes state) receiver new_process)
    (remove_echo_message (message_id message) (message_store state) ++
       materialize_echo_outbound
         (next_message_id state) receiver outbound)
    (started state)
    (next_echo_message_id_after (next_message_id state) outbound).

Definition apply_echo_start
    (node_eq : forall (n m : node), {n = m} + {n <> m})
    (initiator : node)
    (state : executable_echo_state)
    (ordered_neighbors : list node) : executable_echo_state :=
  let root := mkEchoProcess None ordered_neighbors false in
  let outbound := List.map (mkEchoOutbound EchoRequest) ordered_neighbors in
  mkExecutableEchoState
    (update_process node_eq (processes state) initiator root)
    (message_store state ++ materialize_echo_outbound
       (next_message_id state) initiator outbound)
    true
    (next_echo_message_id_after (next_message_id state) outbound).

Definition option_echo_node_eq_dec
    (node_eq : forall (n m : node), {n = m} + {n <> m})
    (left right : option node) : {left = right} + {left <> right}.
Proof. decide equality. Defined.

Definition echo_process_eq_dec
    (node_eq : forall (n m : node), {n = m} + {n <> m})
    (left right : echo_process) : {left = right} + {left <> right}.
Proof.
  decide equality.
  - apply Bool.bool_dec.
  - apply list_eq_dec. exact node_eq.
  - apply option_echo_node_eq_dec. exact node_eq.
Defined.

Definition echo_message_eq_dec
    (node_eq : forall (n m : node), {n = m} + {n <> m})
    (left right : echo_message) : {left = right} + {left <> right}.
Proof.
  decide equality.
  - apply echo_kind_eq_dec.
  - apply Nat.eq_dec.
Defined.

Definition echo_process_has_parent_dec (process : echo_process) :
    {exists parent, process_parent process = Some parent} +
    {~ exists parent, process_parent process = Some parent}.
Proof.
  destruct (process_parent process) as [parent |] eqn:Hparent.
  - left. now exists parent.
  - right. intros [parent Hsome]. congruence.
Defined.

End EchoExecutableTypes.

Arguments mkEchoMessage {node} _ _ _ _.
Arguments message_id {node} _.
Arguments message_kind {node} _.
Arguments message_sender {node} _.
Arguments message_receiver {node} _.
Arguments mkEchoProcess {node} _ _ _.
Arguments process_parent {node} _.
Arguments process_pending {node} _.
Arguments process_finished {node} _.
Arguments mkExecutableEchoState {node} _ _ _ _.
Arguments processes {node} _ _.
Arguments message_store {node} _.
Arguments started {node} _.
Arguments next_message_id {node} _.
Arguments EchoStart {node} _.
Arguments EchoFirstRequestNonLeaf {node} _ _.
Arguments EchoFirstRequestLeaf {node} _.
Arguments EchoRepeatedRequest {node} _.
Arguments EchoInitiatorRequest {node} _.
Arguments EchoParticipantReplyMore {node} _ _.
Arguments EchoParticipantReplyFinal {node} _ _.
Arguments EchoInitiatorReplyMore {node} _.
Arguments EchoInitiatorReplyFinal {node} _.
Arguments mkEchoConfig {node} _ _ _.
Arguments config_initiator {node} _.
Arguments config_nodes {node} _.
Arguments config_adjacent {node} _ _ _.
Arguments mkEchoOutbound {node} _ _.
Arguments outbound_kind {node} _.
Arguments outbound_receiver {node} _.
Arguments initial_echo_process {node}.
Arguments configured_processes_initial {node} _ _.
Arguments echo_initial_on {node} _ _.
Arguments initial_executable_echo_state {node}.
Arguments update_process {node} node_eq _ _ _ _.
Arguments remove_echo_node {node} node_eq _ _.
Arguments remove_echo_message {node} _ _.
Arguments materialize_echo_outbound {node} _ _ _.
Arguments next_echo_message_id_after {node} _ _.
Arguments apply_echo_delivery {node} node_eq _ _ _ _.
Arguments apply_echo_start {node} node_eq initiator _ _.
Arguments option_echo_node_eq_dec {node} node_eq _ _.
Arguments echo_process_eq_dec {node} node_eq _ _.
Arguments echo_message_eq_dec {node} node_eq _ _.
Arguments echo_process_has_parent_dec {node} _.
