(** * Abstraction from executable Echo data to the abstract Echo model

    The definitions below do not model an independently maintained Python
    transition system.  They relate the canonical executable records in
    [EchoExecutableTypes] to the abstract state in [EchoAlgorithm], erasing
    executable-only message identifiers and list ordering where appropriate.

    Python consumes generated code for the canonical executable transition;
    it is not a second endpoint of this refinement relation. *)

From Stdlib Require Import List Bool Sorting.Permutation.
Import ListNotations.
Require Import EchoAlgorithm.
Require Import EchoExecutableTypes.

Section EchoExecutableAbstraction.

Variable node : Type.
Variable node_eq : forall (n m : node), {n = m} + {n <> m}.
Variable initiator : node.
Variable all_nodes : list node.
Variable adj : node -> node -> bool.

Local Notation echo_message := (@EchoExecutableTypes.echo_message node).
Local Notation echo_process := (@EchoExecutableTypes.echo_process node).
Local Notation executable_echo_state :=
  (@EchoExecutableTypes.executable_echo_state node).

(* ------------------------------------------------------------------ *)
(** ** 1. Well-formedness predicates over canonical executable data *)

(** Runtime-generated message identifiers are unique, and every identifier
    already in the queue precedes the next identifier to allocate. *)
Definition executable_messages_well_formed (s : executable_echo_state) : Prop :=
  NoDup (List.map message_id (message_store s)) /\
  forall message,
    In message (message_store s) ->
    message_id message < next_message_id s.

(** Reachable participant states never become finished before selecting a
    tree parent.  Keeping this fact in the refinement relation excludes raw
    record combinations that the executable transition cannot construct. *)
Definition executable_processes_well_formed (s : executable_echo_state) : Prop :=
  forall n,
    n <> initiator ->
    process_finished (processes s n) = true ->
    exists parent, process_parent (processes s n) = Some parent.

(* ------------------------------------------------------------------ *)
(** ** 2. Abstraction of executable messages and process state *)

Definition alpha_kind (k : echo_kind) : echo_msg :=
  match k with
  | EchoRequest => Token
  | EchoReply  => Echo
  end.

Definition alpha_message (m : echo_message) : @echo_packet node :=
  mkPkt (message_sender m) (message_receiver m) (alpha_kind (message_kind m)).

(** Only the initiator becomes [Decided] in the current Rocq model.
    A non-initiator remains [Active] after returning its final ACK. *)
Definition alpha_phase (s : executable_echo_state) (n : node) : phase :=
  let p := processes s n in
  if node_eq n initiator then
    if process_finished p then Decided
    else if started s then Active else Idle
  else
    match process_parent p with
    | Some _ => Active
    | None   => Idle
    end.

Definition expected_replies (n : node) (p : echo_process) : list node :=
  if node_eq n initiator then
    nbrs all_nodes adj n
  else
    match process_parent p with
    | None => []
    | Some parent =>
        List.filter
          (fun candidate =>
             if node_eq candidate parent then false else true)
          (nbrs all_nodes adj n)
    end.

(** The executable representation uses an ordered list for pending replies.
    Its reachable-state invariant records both uniqueness and membership in
    the process's protocol-defined expected-reply collection. *)
Definition executable_pending_well_formed (s : executable_echo_state) : Prop :=
  forall n,
    NoDup (process_pending (processes s n)) /\
    forall candidate,
      In candidate (process_pending (processes s n)) ->
      In candidate (expected_replies n (processes s n)).

Definition node_is_pending (p : echo_process) (n : node) : bool :=
  List.existsb
    (fun pending => if node_eq n pending then true else false)
    (process_pending p).

(** [ps_children] currently records received ACK senders, including ACKs on
    non-tree edges.  It is therefore reconstructed as expected minus pending,
    but only after the node has become active. *)
Definition alpha_acknowledged (s : executable_echo_state) (n : node) : list node :=
  match alpha_phase s n with
  | Idle => []
  | Active | Decided =>
      List.filter
        (fun candidate => negb (node_is_pending (processes s n) candidate))
        (expected_replies n (processes s n))
  end.

Definition alpha_process (s : executable_echo_state) (n : node) : @proc_state node :=
  let p := processes s n in
  mkProc
    (alpha_phase s n)
    (process_parent p)
    (List.length (process_pending p))
    (alpha_acknowledged s n).

Definition alpha_state (s : executable_echo_state) : @echo_state node :=
  mkEchoState
    (fun n => alpha_process s n)
    (List.map alpha_message (message_store s)).

(* ------------------------------------------------------------------ *)
(** ** 3. State correspondence *)

(** List order is not semantically relevant for the message bag or for the
    collection of ACK senders, so correspondence uses [Permutation]. *)
Record ExecutableStateRefines
    (executable : executable_echo_state) (rq : @echo_state node) : Prop := {
  parent_refines : forall n,
    process_parent (processes executable n) = ps_parent (es_procs rq n);
  phase_refines : forall n,
    alpha_phase executable n = ps_phase (es_procs rq n);
  pending_refines : forall n,
    List.length (process_pending (processes executable n)) =
      ps_pending (es_procs rq n);
  acknowledgements_refine : forall n,
    Permutation (alpha_acknowledged executable n)
      (ps_children (es_procs rq n));
  store_refines :
    Permutation (List.map alpha_message (message_store executable))
      (es_msgs rq);
  executable_message_ids_refine :
    executable_messages_well_formed executable;
  executable_processes_refine :
    executable_processes_well_formed executable;
  executable_pending_refine : executable_pending_well_formed executable
}.

Lemma alpha_executable_state_refines (s : executable_echo_state) :
  executable_messages_well_formed s ->
  executable_processes_well_formed s ->
  executable_pending_well_formed s ->
  ExecutableStateRefines s (alpha_state s).
Proof.
  intros Hmessages Hroles Hpending.
  constructor; simpl.
  - intros n. reflexivity.
  - intros n. reflexivity.
  - intros n. reflexivity.
  - intros n. apply Permutation_refl.
  - apply Permutation_refl.
  - exact Hmessages.
  - exact Hroles.
  - exact Hpending.
Qed.

(** The one canonical executable initial value maps directly to an abstract
    initial state; no second initialization predicate is required. *)
Lemma alpha_initial_executable_echo_state :
  echo_init (alpha_state initial_executable_echo_state).
Proof.
  split.
  - intros n.
    unfold alpha_state, alpha_process, alpha_acknowledged, alpha_phase.
    unfold initial_executable_echo_state.
    simpl.
    unfold initial_echo_process.
    simpl.
    destruct (node_eq n initiator); reflexivity.
  - reflexivity.
Qed.

End EchoExecutableAbstraction.

Arguments executable_messages_well_formed {node} _.
Arguments executable_processes_well_formed {node} initiator _.
Arguments executable_pending_well_formed
  {node} node_eq initiator all_nodes adj _.
Arguments alpha_message       {node} _.
