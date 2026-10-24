(** * Direct transition facts and reachability for executable Echo

    This module starts the canonical correctness chain directly from
    [EchoStep].  It deliberately imports no Python-shaped transition,
    replay, refinement, or snapshot module. *)

From Stdlib Require Import List Arith Lia Sorting.Permutation.
Import ListNotations.
Require Import EchoAlgorithm EchoExecutableTypes EchoTransitionIR.

Section EchoExecutableReachability.

Variable node : Type.
Variable node_eq : forall (n m : node), {n = m} + {n <> m}.
Variable config : @echo_config node.

Local Notation initiator := (config_initiator config).
Local Notation all_nodes := (config_nodes config).
Local Notation adj := (config_adjacent config).
Local Notation EchoStep := (@EchoStep node node_eq config).
Local Notation echo_exec := (@echo_exec node node_eq config).
Local Notation eval_guards := (@eval_guards node node_eq config).
Local Notation eval_action := (@eval_action node node_eq config).

(** Successful interpretation exposes exactly one selected rule, its checked
    guards, and its computed action.  This is a structural fact about the
    canonical interpreter, not a second validity implementation. *)
Lemma echo_exec_success_rule
    (state : @executable_echo_state node)
    (event : @echo_event node)
    (successor : @executable_echo_state node) :
  echo_exec state event = Some successor ->
  exists rule,
    lookup_rule (@event_tag node event) echo_program = Some rule /\
    eval_guards state event (ir_rule_guards rule) = true /\
    eval_action state event (ir_rule_action rule) = successor.
Proof.
  unfold echo_exec, EchoTransitionIR.echo_exec, interpret_echo_program.
  destruct (lookup_rule (@event_tag node event) echo_program)
      as [rule |] eqn:Hrule.
  - destruct (eval_guards state event (ir_rule_guards rule))
        eqn:Hguards.
    + intro Hresult. inversion Hresult. subst successor.
      exists rule. auto.
    + discriminate.
  - discriminate.
Qed.

(** A successful startup is accepted only after the canonical finite
    initialization check and the topology-neighbor permutation check. *)
Theorem EchoStep_start_guards
    (state successor : @executable_echo_state node)
    (ordered_neighbors : list node) :
  EchoStep state (EchoStart ordered_neighbors) successor ->
  echo_initial_on config state /\
  Permutation ordered_neighbors (nbrs all_nodes adj initiator).
Proof.
  intro Hstep.
  apply echo_exec_success_rule in Hstep.
  destruct Hstep as [rule [Hrule [Hguards Haction]]].
  cbn [event_tag echo_program lookup_rule ir_event_tag_eqb] in Hrule.
  inversion Hrule. subst rule. clear Hrule Haction.
  apply (@eval_guards_true_iff node node_eq config) in Hguards.
  unfold start_rule in Hguards.
  cbn [ir_rule_guards] in Hguards.
  repeat match goal with
  | H : Forall _ (_ :: _) |- _ => inversion H; subst; clear H
  end.
  cbn [guard_holds eval_nodes_expr] in *.
  auto.
Qed.

(** Read one checked guard from the rule selected by a successful step.  This
    generic interpreter fact belongs at the base of every direct invariant
    proof, rather than in any one invariant module. *)
Lemma EchoStep_selected_guard_holds
    (state successor : @executable_echo_state node)
    (event : @echo_event node)
    (rule : ir_rule) (guard : ir_guard) :
  EchoStep state event successor ->
  lookup_rule (@event_tag node event) echo_program = Some rule ->
  In guard (ir_rule_guards rule) ->
  @guard_holds node node_eq config state event guard.
Proof.
  intros Hstep Hselected Hin.
  apply echo_exec_success_rule in Hstep.
  destruct Hstep as [actual [Hactual [Hguards Haction]]].
  rewrite Hselected in Hactual. inversion Hactual. subst actual.
  apply (@eval_guards_true_iff node node_eq config) in Hguards.
  rewrite Forall_forall in Hguards. now apply Hguards.
Qed.

(** Expose the action computed by the uniquely selected canonical rule. *)
Lemma EchoStep_selected_action
    (state successor : @executable_echo_state node)
    (event : @echo_event node)
    (rule : ir_rule) :
  EchoStep state event successor ->
  lookup_rule (@event_tag node event) echo_program = Some rule ->
  eval_action state event (ir_rule_action rule) =
    successor.
Proof.
  intros Hstep Hselected.
  apply echo_exec_success_rule in Hstep.
  destruct Hstep as [actual [Hactual [Hguards Haction]]].
  rewrite Hselected in Hactual. inversion Hactual. now subst actual.
Qed.

(** Startup has no selected message.  Every other event is a delivery event. *)
Definition is_delivery_event (event : @echo_event node) : Prop :=
  match event with
  | EchoStart _ => False
  | _ => True
  end.

(** Every successful delivery selects a message that is currently queued.
    The statement is proved from the guards of the selected canonical rule. *)
Theorem EchoStep_delivery_message_queued
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  EchoStep state event successor ->
  is_delivery_event event ->
  In (@event_message node config event) (message_store state).
Proof.
  intros Hstep Hdelivery.
  apply echo_exec_success_rule in Hstep.
  destruct Hstep as [rule [Hrule [Hguards Haction]]].
  destruct event; cbn [is_delivery_event] in Hdelivery;
    try contradiction.
  all: cbn [event_tag echo_program lookup_rule ir_event_tag_eqb] in Hrule;
    inversion Hrule; subst rule; clear Hrule Haction.
  all: apply (@eval_guards_true_iff node node_eq config) in Hguards.
  all: rewrite Forall_forall in Hguards.
  all: specialize (Hguards IRGuardMessageInStore ltac:(
    cbn [first_echo_nonleaf_rule first_echo_leaf_rule
      repeated_echo_rule initiator_echo_rule participant_ack_more_rule
      participant_ack_final_rule initiator_ack_more_rule
      initiator_ack_final_rule];
    repeat (first [left; reflexivity | right]))).
  all: exact Hguards.
Qed.

(** Removing the selected ID cannot remove a message carrying another ID. *)
Lemma remove_echo_message_preserves_distinct_id
    (selected_id : nat)
    (messages : list (@echo_message node))
    (other : @echo_message node) :
  In other messages ->
  message_id other <> selected_id ->
  In other (remove_echo_message selected_id messages).
Proof.
  induction messages as [| message rest IH]; intros Hin Hdistinct.
  - contradiction.
  - cbn [remove_echo_message].
    destruct (Nat.eqb selected_id (message_id message)) eqn:Hselected.
    + apply Nat.eqb_eq in Hselected.
      destruct Hin as [Heq | Hin].
      * subst message. exfalso. apply Hdistinct. now symmetry.
      * exact Hin.
    + destruct Hin as [Heq | Hin].
      * now left.
      * right. now apply IH.
Qed.

Lemma remove_echo_message_in
    (selected_id : nat)
    (messages : list (@echo_message node))
    (message : @echo_message node) :
  In message (remove_echo_message selected_id messages) ->
  In message messages.
Proof.
  induction messages as [| head rest IH]; intro Hin.
  - contradiction.
  - cbn [remove_echo_message] in Hin.
    destruct (Nat.eqb selected_id (message_id head)).
    + now right.
    + destruct Hin as [Heq | Hin].
      * now left.
      * right. now apply IH.
Qed.

Lemma remove_echo_message_ids_nodup
    (selected_id : nat)
    (messages : list (@echo_message node)) :
  NoDup (List.map message_id messages) ->
  NoDup (List.map message_id
    (remove_echo_message selected_id messages)).
Proof.
  induction messages as [| head rest IH]; intro Hnodup.
  - constructor.
  - cbn in Hnodup.
    inversion Hnodup as [| head_id rest_ids Hnotin Hrest]; subst.
    cbn [remove_echo_message].
    destruct (Nat.eqb selected_id (message_id head)).
    + exact Hrest.
    + cbn. constructor.
      * intro Hin.
        apply Hnotin. apply in_map_iff in Hin.
        destruct Hin as [message [Hid Hremoved]].
        apply in_map_iff. exists message. split.
        -- exact Hid.
        -- now apply remove_echo_message_in in Hremoved.
      * now apply IH.
Qed.

(** Every successful delivery has the store/counter shape of the single
    canonical delivery action.  The existential [outbound] is the result of
    evaluating the selected rule's outbound expression; this theorem does not
    define another branch dispatcher. *)
Theorem EchoStep_delivery_store_effect
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  EchoStep state event successor ->
  is_delivery_event event ->
  exists outbound : list (@echo_outbound node),
    message_store successor =
      remove_echo_message
        (message_id (@event_message node config event))
        (message_store state) ++
      materialize_echo_outbound
        (next_message_id state)
        (message_receiver (@event_message node config event))
        outbound /\
    next_message_id successor =
      next_echo_message_id_after (next_message_id state) outbound.
Proof.
  intros Hstep Hdelivery.
  apply echo_exec_success_rule in Hstep.
  destruct Hstep as [rule [Hrule [Hguards Haction]]].
  destruct event; cbn [is_delivery_event] in Hdelivery;
    try contradiction.
  all: cbn [event_tag echo_program lookup_rule ir_event_tag_eqb] in Hrule;
    inversion Hrule; subst rule; clear Hrule Hguards.
  all: cbn [eval_action first_echo_nonleaf_rule first_echo_leaf_rule
    repeated_echo_rule initiator_echo_rule participant_ack_more_rule
    participant_ack_final_rule initiator_ack_more_rule
    initiator_ack_final_rule ir_rule_action eval_nodes_expr
    eval_process_expr eval_parent_expr eval_outbound_expr] in Haction.
  all: subst successor.
  all: eexists; split; reflexivity.
Qed.

(** Startup appends its request block to the old store and advances the same
    fresh counter.  The startup guards later tell us that the old store is
    empty, but the action equation itself is stated independently. *)
Theorem EchoStep_start_store_effect
    (state successor : @executable_echo_state node)
    (ordered_neighbors : list node) :
  EchoStep state (EchoStart ordered_neighbors) successor ->
  let outbound :=
    List.map (mkEchoOutbound EchoRequest) ordered_neighbors in
  message_store successor =
    message_store state ++
      materialize_echo_outbound
        (next_message_id state) initiator outbound /\
  next_message_id successor =
    next_echo_message_id_after (next_message_id state) outbound.
Proof.
  intro Hstep.
  apply echo_exec_success_rule in Hstep.
  destruct Hstep as [rule [Hrule [Hguards Haction]]].
  cbn [event_tag echo_program lookup_rule ir_event_tag_eqb] in Hrule.
  inversion Hrule. subst rule. clear Hrule Hguards.
  cbn [eval_action start_rule ir_rule_action eval_nodes_expr] in Haction.
  subst successor. split; reflexivity.
Qed.

(** A successful delivery preserves every previously queued message whose ID
    differs from the selected message ID. *)
Theorem EchoStep_delivery_preserves_unselected
    (state successor : @executable_echo_state node)
    (event : @echo_event node)
    (other : @echo_message node) :
  EchoStep state event successor ->
  is_delivery_event event ->
  In other (message_store state) ->
  message_id other <>
    message_id (@event_message node config event) ->
  In other (message_store successor).
Proof.
  intros Hstep Hdelivery Hin Hdistinct.
  destruct (EchoStep_delivery_store_effect
      state successor event Hstep Hdelivery)
    as [outbound [Hstore Hnext]].
  rewrite Hstore. apply in_or_app. left.
  now apply remove_echo_message_preserves_distinct_id.
Qed.

(** Materialization assigns exactly the consecutive interval
    [next_id, ..., next_id + length outbound - 1]. *)
Lemma materialize_echo_outbound_ids
    (next_id : nat) (sender : node)
    (outbound : list (@echo_outbound node)) :
  List.map message_id
    (materialize_echo_outbound next_id sender outbound) =
  List.seq next_id (List.length outbound).
Proof.
  revert next_id. induction outbound as [| item rest IH]; intro next_id.
  - reflexivity.
  - change
      (next_id :: List.map message_id
          (materialize_echo_outbound (S next_id) sender rest) =
       next_id :: List.seq (S next_id) (List.length rest)).
    f_equal. apply IH.
Qed.

Corollary materialize_echo_outbound_ids_nodup
    (next_id : nat) (sender : node)
    (outbound : list (@echo_outbound node)) :
  NoDup (List.map message_id
    (materialize_echo_outbound next_id sender outbound)).
Proof.
  rewrite materialize_echo_outbound_ids. apply seq_NoDup.
Qed.

Lemma materialize_echo_outbound_id_bounds
    (next_id : nat) (sender : node)
    (outbound : list (@echo_outbound node))
    (message : @echo_message node) :
  In message (materialize_echo_outbound next_id sender outbound) ->
  next_id <= message_id message /\
  message_id message < next_id + List.length outbound.
Proof.
  revert next_id.
  induction outbound as [| item rest IH]; intros next_id Hin.
  - contradiction.
  - cbn [materialize_echo_outbound] in Hin.
    destruct Hin as [Heq | Hin].
    + subst message. cbn. lia.
    + specialize (IH (S next_id) Hin). cbn. lia.
Qed.

Lemma NoDup_app_disjoint {A : Type} (left right : list A) :
  NoDup left ->
  NoDup right ->
  (forall item, In item left -> In item right -> False) ->
  NoDup (left ++ right).
Proof.
  intros Hleft. induction Hleft as [| item rest Hnotin Hrest IH];
    intros Hright Hdisjoint.
  - exact Hright.
  - cbn. constructor.
    + intro Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * now apply Hnotin.
      * eapply Hdisjoint; [now left | exact Hin].
    + apply IH.
      * exact Hright.
      * intros candidate Hinleft Hinright.
        eapply Hdisjoint.
        -- right. exact Hinleft.
        -- exact Hinright.
Qed.

(** The emitted part of a successful delivery therefore has consecutive,
    duplicate-free IDs, and the successor counter points just beyond it. *)
Theorem EchoStep_delivery_emits_consecutive_ids
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  EchoStep state event successor ->
  is_delivery_event event ->
  exists outbound : list (@echo_outbound node),
    message_store successor =
      remove_echo_message
        (message_id (@event_message node config event))
        (message_store state) ++
      materialize_echo_outbound
        (next_message_id state)
        (message_receiver (@event_message node config event))
        outbound /\
    next_message_id successor =
      next_message_id state + List.length outbound /\
    List.map message_id
      (materialize_echo_outbound
        (next_message_id state)
        (message_receiver (@event_message node config event))
        outbound) =
      List.seq (next_message_id state) (List.length outbound) /\
    NoDup (List.map message_id
      (materialize_echo_outbound
        (next_message_id state)
        (message_receiver (@event_message node config event))
        outbound)).
Proof.
  intros Hstep Hdelivery.
  destruct (EchoStep_delivery_store_effect
      state successor event Hstep Hdelivery)
    as [outbound [Hstore Hnext]].
  exists outbound. repeat split.
  - exact Hstore.
  - exact Hnext.
  - apply materialize_echo_outbound_ids.
  - apply materialize_echo_outbound_ids_nodup.
Qed.

(** Queue-level fresh-ID invariant used by the runner and later message
    preservation proofs. *)
Definition echo_message_ids_well_formed
    (state : @executable_echo_state node) : Prop :=
  (forall message,
      In message (message_store state) ->
      message_id message < next_message_id state) /\
  NoDup (List.map message_id (message_store state)).

Theorem EchoStep_start_message_ids_well_formed
    (state successor : @executable_echo_state node)
    (ordered_neighbors : list node) :
  EchoStep state (EchoStart ordered_neighbors) successor ->
  echo_message_ids_well_formed successor.
Proof.
  intro Hstep.
  pose proof (EchoStep_start_guards
    state successor ordered_neighbors Hstep) as Hguards.
  destruct Hguards as
    [[Hstarted [Hprocesses [Hempty Hnext]]] Hpermutation].
  pose proof (EchoStep_start_store_effect
    state successor ordered_neighbors Hstep) as Heffect.
  cbn zeta in Heffect.
  destruct Heffect as [Hstore Hsuccessor_next].
  rewrite Hempty in Hstore. cbn in Hstore.
  unfold echo_message_ids_well_formed.
  rewrite Hstore, Hsuccessor_next.
  unfold next_echo_message_id_after.
  split.
  - intros message Hin.
    apply materialize_echo_outbound_id_bounds in Hin. lia.
  - apply materialize_echo_outbound_ids_nodup.
Qed.

Theorem EchoStep_delivery_preserves_message_ids_well_formed
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  echo_message_ids_well_formed state ->
  EchoStep state event successor ->
  is_delivery_event event ->
  echo_message_ids_well_formed successor.
Proof.
  intros [Hbelow Hnodup] Hstep Hdelivery.
  destruct (EchoStep_delivery_store_effect
      state successor event Hstep Hdelivery)
    as [outbound [Hstore Hsuccessor_next]].
  unfold echo_message_ids_well_formed.
  rewrite Hstore, Hsuccessor_next.
  unfold next_echo_message_id_after.
  split.
  - intros message Hin.
    apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + apply remove_echo_message_in in Hin.
      specialize (Hbelow message Hin). lia.
    + apply materialize_echo_outbound_id_bounds in Hin. lia.
  - rewrite List.map_app. apply NoDup_app_disjoint.
    + now apply remove_echo_message_ids_nodup.
    + apply materialize_echo_outbound_ids_nodup.
    + intros identifier Hold Hnew.
      apply in_map_iff in Hold.
      destruct Hold as [old_message [Hold_id Hold_in]].
      apply in_map_iff in Hnew.
      destruct Hnew as [new_message [Hnew_id Hnew_in]].
      apply remove_echo_message_in in Hold_in.
      specialize (Hbelow old_message Hold_in).
      apply materialize_echo_outbound_id_bounds in Hnew_in.
      lia.
Qed.

Theorem EchoStep_preserves_message_ids_well_formed
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  echo_message_ids_well_formed state ->
  EchoStep state event successor ->
  echo_message_ids_well_formed successor.
Proof.
  intros Hwellformed Hstep.
  destruct event.
  all: try (eapply EchoStep_delivery_preserves_message_ids_well_formed;
    [exact Hwellformed | exact Hstep | cbn [is_delivery_event]; exact I]).
  - now apply EchoStep_start_message_ids_well_formed in Hstep.
Qed.

(** Every canonical transition preserves or increases the fresh-message
    counter.  Actions allocate zero or more consecutive IDs starting at the
    old counter; no branch can move it backwards. *)
Theorem EchoStep_next_message_id_monotone
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  EchoStep state event successor ->
  next_message_id state <= next_message_id successor.
Proof.
  intro Hstep.
  apply echo_exec_success_rule in Hstep.
  destruct Hstep as [rule [Hrule [Hguards Haction]]].
  destruct event.
  all: cbn [event_tag echo_program lookup_rule ir_event_tag_eqb] in Hrule;
    inversion Hrule; subst rule; clear Hrule Hguards.
  all: cbn [eval_action start_rule first_echo_nonleaf_rule
    first_echo_leaf_rule repeated_echo_rule initiator_echo_rule
    participant_ack_more_rule participant_ack_final_rule
    initiator_ack_more_rule initiator_ack_final_rule ir_rule_action
    eval_nodes_expr eval_process_expr eval_parent_expr
    eval_outbound_expr] in Haction.
  all: subst successor.
  all: unfold apply_echo_start, apply_echo_delivery,
    next_echo_message_id_after; cbn; lia.
Qed.

(** Canonical reachability contains exactly the initial state and states
    obtained by repeatedly taking successful [EchoStep] transitions. *)
Inductive echo_reachable : @executable_echo_state node -> Prop :=
  | EchoReachInitial :
      echo_reachable initial_executable_echo_state
  | EchoReachStep :
      forall state event successor,
        echo_reachable state ->
        EchoStep state event successor ->
        echo_reachable successor.

(** The first direct reachability invariant: the fresh-message counter never
    falls below its initial value. *)
Theorem echo_reachable_next_message_id_positive
    (state : @executable_echo_state node) :
  echo_reachable state ->
  1 <= next_message_id state.
Proof.
  intro Hreachable.
  induction Hreachable as [| before event after Hbefore IH Hstep].
  - unfold initial_executable_echo_state. cbn. lia.
  - eapply Nat.le_trans.
    + exact IH.
    + now apply EchoStep_next_message_id_monotone in Hstep.
Qed.

Theorem echo_reachable_message_ids_well_formed
    (state : @executable_echo_state node) :
  echo_reachable state ->
  echo_message_ids_well_formed state.
Proof.
  intro Hreachable.
  induction Hreachable as [| before event after Hbefore IH Hstep].
  - unfold echo_message_ids_well_formed,
      initial_executable_echo_state. cbn. split.
    + intros message Hin. contradiction.
    + constructor.
  - eapply EchoStep_preserves_message_ids_well_formed.
    + exact IH.
    + exact Hstep.
Qed.

End EchoExecutableReachability.

Arguments EchoStep_selected_guard_holds
  {node node_eq config} _ _ _ _ _ _ _ _.
Arguments EchoStep_selected_action
  {node node_eq config} _ _ _ _ _ _.
Arguments is_delivery_event {node} _.
Arguments echo_reachable {node} node_eq config _.
Arguments echo_message_ids_well_formed {node} _.
