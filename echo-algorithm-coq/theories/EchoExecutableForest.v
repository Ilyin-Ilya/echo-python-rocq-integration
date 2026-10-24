(** * Direct parent-forest invariant for executable Echo

    The canonical state does not store discovery timestamps.  We therefore
    prove that every reachable state admits a ghost rank: following a parent
    pointer strictly decreases that rank.  The rank is proof-only data and is
    not exported to Python or added to runtime state. *)

From Stdlib Require Import List Bool Arith Lia Relations.Relation_Operators.
Import ListNotations.
Require Import EchoExecutableTypes EchoTransitionIR
  EchoExecutableReachability.

Section EchoExecutableForest.

Variable node : Type.
Variable node_eq : forall (n m : node), {n = m} + {n <> m}.
Variable config : @echo_config node.

Local Notation initiator := (config_initiator config).
Local Notation all_nodes := (config_nodes config).
Local Notation EchoStep := (@EchoStep node node_eq config).

Definition echo_discovered
    (state : @executable_echo_state node) (owner : node) : Prop :=
  processes state owner <> initial_echo_process.

(** A node may be used as a parent only after it has left its initial state. *)
Definition echo_parent_targets_discovered
    (state : @executable_echo_state node) : Prop :=
  forall child parent,
    In child all_nodes ->
    process_parent (processes state child) = Some parent ->
    echo_discovered state parent.

(** Every queued request was emitted by an already-discovered process. *)
Definition echo_request_senders_discovered
    (state : @executable_echo_state node) : Prop :=
  forall message,
    In message (message_store state) ->
    message_kind message = EchoRequest ->
    echo_discovered state (message_sender message).

(** The ghost rank grows away from the root, hence strictly decreases when a
    parent pointer is followed. *)
Definition echo_parent_ranked
    (state : @executable_echo_state node) : Prop :=
  exists rank : node -> nat,
    forall child parent,
      In child all_nodes ->
      process_parent (processes state child) = Some parent ->
      rank parent < rank child.

Definition echo_parent_forest_well_formed
    (state : @executable_echo_state node) : Prop :=
  echo_parent_targets_discovered state /\
  echo_request_senders_discovered state /\
  echo_parent_ranked state.

Definition echo_parent_edge
    (state : @executable_echo_state node) (child parent : node) : Prop :=
  In child all_nodes /\
  process_parent (processes state child) = Some parent.

Definition echo_parent_acyclic
    (state : @executable_echo_state node) : Prop :=
  forall owner,
    ~ clos_trans node (echo_parent_edge state) owner owner.

Lemma parented_process_discovered
    (parent : node) (pending : list node) (finished : bool) :
  mkEchoProcess (Some parent) pending finished <> initial_echo_process.
Proof.
  unfold initial_echo_process. discriminate.
Qed.

Lemma finished_root_discovered :
  mkEchoProcess (@None node) [] true <> initial_echo_process.
Proof.
  unfold initial_echo_process. discriminate.
Qed.

Lemma nonempty_root_discovered (pending : list node) :
  pending <> [] ->
  mkEchoProcess (@None node) pending false <> initial_echo_process.
Proof.
  intros Hnonempty Hequal.
  unfold initial_echo_process in Hequal.
  inversion Hequal. contradiction.
Qed.

Lemma apply_echo_delivery_process_self
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (outbound : list (@echo_outbound node)) :
  processes (apply_echo_delivery node_eq state selected new_process outbound)
    (message_receiver selected) = new_process.
Proof.
  unfold apply_echo_delivery. cbn. unfold update_process.
  destruct (node_eq (message_receiver selected) (message_receiver selected));
    [reflexivity | contradiction].
Qed.

Lemma apply_echo_delivery_process_other
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (outbound : list (@echo_outbound node))
    (owner : node) :
  message_receiver selected <> owner ->
  processes (apply_echo_delivery node_eq state selected new_process outbound)
    owner = processes state owner.
Proof.
  intro Hdifferent.
  unfold apply_echo_delivery. cbn. unfold update_process.
  destruct (node_eq (message_receiver selected) owner);
    [contradiction | reflexivity].
Qed.

Lemma apply_echo_start_process_self
    (state : @executable_echo_state node) (ordered_neighbors : list node) :
  processes (apply_echo_start node_eq initiator state ordered_neighbors)
    initiator = mkEchoProcess None ordered_neighbors false.
Proof.
  unfold apply_echo_start. cbn. unfold update_process.
  destruct (node_eq initiator initiator); [reflexivity | contradiction].
Qed.

Lemma apply_echo_start_process_other
    (state : @executable_echo_state node) (ordered_neighbors : list node)
    (owner : node) :
  initiator <> owner ->
  processes (apply_echo_start node_eq initiator state ordered_neighbors)
    owner = processes state owner.
Proof.
  intro Hdifferent.
  unfold apply_echo_start. cbn. unfold update_process.
  destruct (node_eq initiator owner); [contradiction | reflexivity].
Qed.

Lemma materialized_echo_message_fields
    (next_id : nat) (sender : node)
    (outbound : list (@echo_outbound node))
    (message : @echo_message node) :
  In message (materialize_echo_outbound next_id sender outbound) ->
  exists item,
    In item outbound /\
    message_sender message = sender /\
    message_kind message = outbound_kind item.
Proof.
  revert next_id.
  induction outbound as [| item rest IH]; intros next_id Hin.
  - contradiction.
  - cbn [materialize_echo_outbound] in Hin.
    destruct Hin as [Hequal | Hin].
    + subst message. exists item. cbn. auto.
    + destruct (IH (S next_id) Hin)
        as [found [Hfound [Hsender Hkind]]].
      exists found. split.
      * now right.
      * split; assumption.
Qed.

Lemma apply_echo_delivery_discovered_monotone
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (outbound : list (@echo_outbound node)) :
  (echo_discovered state (message_receiver selected) ->
    new_process <> initial_echo_process) ->
  forall owner,
    echo_discovered state owner ->
    echo_discovered
      (apply_echo_delivery node_eq state selected new_process outbound) owner.
Proof.
  intros Hnew owner Hold.
  unfold echo_discovered in *.
  destruct (node_eq (message_receiver selected) owner)
      as [Hequal | Hdifferent].
  - subst owner. rewrite apply_echo_delivery_process_self.
    now apply Hnew.
  - rewrite apply_echo_delivery_process_other; assumption.
Qed.

(** A delivery that keeps the receiver's parent pointer, never turns a
    discovered receiver back into its initial state, and emits no requests
    preserves the complete forest certificate. *)
Lemma apply_parent_preserving_delivery_forest
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (outbound : list (@echo_outbound node)) :
  echo_parent_forest_well_formed state ->
  process_parent new_process =
    process_parent (processes state (message_receiver selected)) ->
  (echo_discovered state (message_receiver selected) ->
    new_process <> initial_echo_process) ->
  (forall item,
    In item outbound -> outbound_kind item <> EchoRequest) ->
  echo_parent_forest_well_formed
    (apply_echo_delivery node_eq state selected new_process outbound).
Proof.
  intros [Htargets [Hrequests [rank Hrank]]]
    Hparent Hnew_discovered Hno_requests.
  set (successor :=
    apply_echo_delivery node_eq state selected new_process outbound).
  assert (Hmonotone : forall owner,
      echo_discovered state owner -> echo_discovered successor owner).
  { intros owner Hold. unfold successor.
    eapply apply_echo_delivery_discovered_monotone; eauto. }
  split.
  - intros child parent Hchild Hchild_parent.
    destruct (node_eq (message_receiver selected) child)
        as [Hequal | Hdifferent].
    + subst child. unfold successor in Hchild_parent.
      rewrite apply_echo_delivery_process_self in Hchild_parent.
      rewrite Hparent in Hchild_parent.
      apply Hmonotone.
      exact (Htargets (message_receiver selected) parent
        Hchild Hchild_parent).
    + unfold successor in Hchild_parent.
      rewrite apply_echo_delivery_process_other in Hchild_parent
        by exact Hdifferent.
      apply Hmonotone.
      exact (Htargets child parent Hchild Hchild_parent).
  - split.
    + intros message Hin Hkind.
      unfold successor in Hin.
      cbn [apply_echo_delivery] in Hin.
      apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * apply remove_echo_message_in in Hin.
        apply Hmonotone. now eapply Hrequests.
      * destruct (materialized_echo_message_fields
          (next_message_id state) (message_receiver selected)
          outbound message Hin)
          as [item [Hitem [Hsender Hitem_kind]]].
        exfalso. apply (Hno_requests item Hitem).
        now rewrite <- Hitem_kind.
    + exists rank. intros child parent Hchild Hchild_parent.
      destruct (node_eq (message_receiver selected) child)
          as [Hequal | Hdifferent].
      * subst child. unfold successor in Hchild_parent.
        rewrite apply_echo_delivery_process_self in Hchild_parent.
        rewrite Hparent in Hchild_parent.
        now eapply Hrank.
      * unfold successor in Hchild_parent.
        rewrite apply_echo_delivery_process_other in Hchild_parent
          by exact Hdifferent.
        now eapply Hrank.
Qed.

(** A first request discovers an initial receiver and adds exactly one new
    parent edge.  The receiver had neither an outgoing parent edge nor an
    incoming child edge, so assigning it rank [S (rank sender)] preserves the
    strict ranking. *)
Lemma apply_first_request_delivery_forest
    (state : @executable_echo_state node)
    (selected : @echo_message node)
    (new_process : @echo_process node)
    (outbound : list (@echo_outbound node)) :
  echo_parent_forest_well_formed state ->
  In selected (message_store state) ->
  message_kind selected = EchoRequest ->
  processes state (message_receiver selected) = initial_echo_process ->
  process_parent new_process = Some (message_sender selected) ->
  new_process <> initial_echo_process ->
  echo_parent_forest_well_formed
    (apply_echo_delivery node_eq state selected new_process outbound).
Proof.
  intros [Htargets [Hrequests [rank Hrank]]]
    Hselected Hkind Hinitial Hnew_parent Hnew_discovered.
  set (receiver := message_receiver selected).
  set (sender := message_sender selected).
  change (processes state receiver = initial_echo_process) in Hinitial.
  change (process_parent new_process = Some sender) in Hnew_parent.
  set (successor :=
    apply_echo_delivery node_eq state selected new_process outbound).
  assert (Hsender_discovered : echo_discovered state sender).
  { unfold sender. now eapply Hrequests. }
  assert (Hsender_different : receiver <> sender).
  { intros Hequal. apply Hsender_discovered.
    unfold echo_discovered. rewrite <- Hequal. exact Hinitial. }
  assert (Hmonotone : forall owner,
      echo_discovered state owner -> echo_discovered successor owner).
  { intros owner Hold. unfold successor.
    apply apply_echo_delivery_discovered_monotone.
    - intros _. exact Hnew_discovered.
    - exact Hold. }
  split.
  - intros child parent Hchild Hchild_parent.
    destruct (node_eq receiver child) as [Hequal | Hdifferent].
    + subst child. unfold successor, receiver in Hchild_parent.
      rewrite apply_echo_delivery_process_self in Hchild_parent.
      rewrite Hnew_parent in Hchild_parent. inversion Hchild_parent.
      subst parent. apply Hmonotone. exact Hsender_discovered.
    + unfold successor, receiver in Hchild_parent.
      rewrite apply_echo_delivery_process_other in Hchild_parent
        by exact Hdifferent.
      apply Hmonotone.
      exact (Htargets child parent Hchild Hchild_parent).
  - split.
    + intros message Hin Hmessage_kind.
      unfold successor in Hin.
      cbn [apply_echo_delivery] in Hin.
      apply in_app_or in Hin. destruct Hin as [Hin | Hin].
      * apply remove_echo_message_in in Hin.
        apply Hmonotone. now eapply Hrequests.
      * destruct (materialized_echo_message_fields
          (next_message_id state) (message_receiver selected)
          outbound message Hin)
          as [item [Hitem [Hmessage_sender Hitem_kind]]].
        unfold echo_discovered.
        rewrite Hmessage_sender.
        unfold successor, receiver.
        rewrite apply_echo_delivery_process_self.
        exact Hnew_discovered.
    + exists (fun owner =>
        if node_eq receiver owner then S (rank sender) else rank owner).
      intros child parent Hchild Hchild_parent.
      destruct (node_eq receiver child) as [Hequal | Hchild_different].
      * subst child. unfold successor, receiver in Hchild_parent.
        rewrite apply_echo_delivery_process_self in Hchild_parent.
        rewrite Hnew_parent in Hchild_parent. inversion Hchild_parent.
        subst parent. cbn.
        destruct (node_eq receiver sender) as [Hequal | Hdifferent].
        -- contradiction.
        -- destruct (node_eq receiver receiver);
             [apply Nat.lt_succ_diag_r | contradiction].
      * assert (Hparent_different : receiver <> parent).
        { intros Hequal. subst parent.
          unfold successor, receiver in Hchild_parent.
          rewrite apply_echo_delivery_process_other in Hchild_parent
            by exact Hchild_different.
          pose proof (Htargets child receiver Hchild Hchild_parent)
            as Hreceiver_discovered.
          apply Hreceiver_discovered. exact Hinitial. }
        unfold successor, receiver in Hchild_parent.
        rewrite apply_echo_delivery_process_other in Hchild_parent
          by exact Hchild_different.
        cbn.
        destruct (node_eq receiver parent); [contradiction |].
        destruct (node_eq receiver child); [contradiction |].
        now eapply Hrank.
Qed.

Theorem EchoStep_start_forest
    (state successor : @executable_echo_state node)
    (ordered_neighbors : list node) :
  EchoStep state (EchoStart ordered_neighbors) successor ->
  echo_parent_forest_well_formed successor.
Proof.
  intro Hstep.
  pose proof (@EchoStep_start_guards node node_eq config
    state successor ordered_neighbors Hstep) as [Hinitial Hpermutation].
  destruct Hinitial as [Hstarted [Hprocesses [Hstore Hnext]]].
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoStart ordered_neighbors) start_rule Hstep eq_refl) as Haction.
  cbn [eval_action start_rule ir_rule_action eval_nodes_expr] in Haction.
  subst successor.
  set (successor :=
    apply_echo_start node_eq initiator state ordered_neighbors).
  assert (Hno_parent : forall child,
      In child all_nodes ->
      process_parent (processes successor child) = None).
  { intros child Hchild.
    destruct (node_eq initiator child) as [Hequal | Hdifferent].
    - subst child. unfold successor.
      rewrite apply_echo_start_process_self. reflexivity.
    - unfold successor.
      rewrite apply_echo_start_process_other by exact Hdifferent.
      rewrite (Hprocesses child Hchild). reflexivity. }
  split.
  - intros child parent Hchild Hparent.
    change (process_parent (processes successor child) = Some parent)
      in Hparent.
    rewrite (Hno_parent child Hchild) in Hparent. discriminate.
  - split.
    + intros message Hin Hkind.
      unfold successor in Hin.
      unfold apply_echo_start in Hin. cbn in Hin.
      rewrite Hstore in Hin. cbn in Hin.
      destruct (materialized_echo_message_fields
          (next_message_id state) initiator
          (List.map (mkEchoOutbound EchoRequest) ordered_neighbors)
          message Hin)
        as [item [Hitem [Hsender Hitem_kind]]].
      apply in_map_iff in Hitem.
      destruct Hitem as [neighbor [Hitem Hneighbor]]. subst item.
      unfold echo_discovered. rewrite Hsender.
      unfold successor. rewrite apply_echo_start_process_self.
      cbn [event_ordered_nodes].
      apply nonempty_root_discovered.
      intros Heq. rewrite Heq in Hneighbor. contradiction.
    + exists (fun _ => 0). intros child parent Hchild Hparent.
      change (process_parent (processes successor child) = Some parent)
        in Hparent.
      rewrite (Hno_parent child Hchild) in Hparent. discriminate.
Qed.

Theorem EchoStep_first_request_nonleaf_forest
    (state successor : @executable_echo_state node)
    (message : @echo_message node) (ordered_forwards : list node) :
  echo_parent_forest_well_formed state ->
  EchoStep state (EchoFirstRequestNonLeaf message ordered_forwards) successor ->
  echo_parent_forest_well_formed successor.
Proof.
  intros Hforest Hstep.
  pose proof (@EchoStep_delivery_message_queued node node_eq config
    state successor (EchoFirstRequestNonLeaf message ordered_forwards)
    Hstep I) as Hselected.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule (IRGuardKind EchoRequest)
    Hstep eq_refl ltac:(left; reflexivity)) as Hkind.
  cbn [guard_holds event_message] in Hkind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule (IRGuardProcessInitial IRMessageReceiver)
    Hstep eq_refl ltac:(
      cbn [first_echo_nonleaf_rule];
      repeat (first [left; reflexivity | right]))) as Hinitial.
  cbn [guard_holds eval_node_expr event_message] in Hinitial.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoFirstRequestNonLeaf message ordered_forwards)
    first_echo_nonleaf_rule Hstep eq_refl) as Haction.
  cbn [eval_action first_echo_nonleaf_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message event_ordered_nodes] in Haction.
  subst successor.
  eapply apply_first_request_delivery_forest.
  - exact Hforest.
  - exact Hselected.
  - exact Hkind.
  - exact Hinitial.
  - reflexivity.
  - apply parented_process_discovered.
Qed.

Theorem EchoStep_first_request_leaf_forest
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_parent_forest_well_formed state ->
  EchoStep state (EchoFirstRequestLeaf message) successor ->
  echo_parent_forest_well_formed successor.
Proof.
  intros Hforest Hstep.
  pose proof (@EchoStep_delivery_message_queued node node_eq config
    state successor (EchoFirstRequestLeaf message) Hstep I) as Hselected.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestLeaf message) first_echo_leaf_rule
    (IRGuardKind EchoRequest)
    Hstep eq_refl ltac:(left; reflexivity)) as Hkind.
  cbn [guard_holds event_message] in Hkind.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoFirstRequestLeaf message) first_echo_leaf_rule
    (IRGuardProcessInitial IRMessageReceiver)
    Hstep eq_refl ltac:(
      cbn [first_echo_leaf_rule];
      repeat (first [left; reflexivity | right]))) as Hinitial.
  cbn [guard_holds eval_node_expr event_message] in Hinitial.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoFirstRequestLeaf message) first_echo_leaf_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action first_echo_leaf_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message] in Haction.
  subst successor.
  eapply apply_first_request_delivery_forest.
  - exact Hforest.
  - exact Hselected.
  - exact Hkind.
  - exact Hinitial.
  - reflexivity.
  - apply parented_process_discovered.
Qed.

Theorem EchoStep_repeated_request_forest
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_parent_forest_well_formed state ->
  EchoStep state (EchoRepeatedRequest message) successor ->
  echo_parent_forest_well_formed successor.
Proof.
  intros Hforest Hstep.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoRepeatedRequest message) repeated_echo_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action repeated_echo_rule ir_rule_action
    eval_process_expr eval_node_expr eval_outbound_expr event_message]
    in Haction.
  subst successor.
  eapply apply_parent_preserving_delivery_forest.
  - exact Hforest.
  - reflexivity.
  - intros Hdiscovered. exact Hdiscovered.
  - intros item Hitem Hkind.
    cbn in Hitem. destruct Hitem as [Hequal | Hin];
      [subst item; discriminate | contradiction].
Qed.

Theorem EchoStep_initiator_request_forest
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_parent_forest_well_formed state ->
  EchoStep state (EchoInitiatorRequest message) successor ->
  echo_parent_forest_well_formed successor.
Proof.
  intros Hforest Hstep.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorRequest message) initiator_echo_rule
    (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
    Hstep eq_refl ltac:(
      cbn [initiator_echo_rule];
      repeat (first [left; reflexivity | right]))) as Hequal.
  cbn [guard_holds eval_node_expr event_message] in Hequal.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoInitiatorRequest message) initiator_echo_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action initiator_echo_rule ir_rule_action
    eval_process_expr eval_node_expr eval_outbound_expr event_message]
    in Haction.
  subst successor.
  eapply apply_parent_preserving_delivery_forest.
  - exact Hforest.
  - now rewrite Hequal.
  - rewrite Hequal. intros Hdiscovered. exact Hdiscovered.
  - intros item Hitem Hkind.
    cbn in Hitem. destruct Hitem as [Hitem | Hin];
      [subst item; discriminate | contradiction].
Qed.

Theorem EchoStep_participant_reply_more_forest
    (state successor : @executable_echo_state node)
    (message : @echo_message node) (parent : node) :
  echo_parent_forest_well_formed state ->
  EchoStep state (EchoParticipantReplyMore message parent) successor ->
  echo_parent_forest_well_formed successor.
Proof.
  intros Hforest Hstep.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyMore message parent)
    participant_ack_more_rule
    (IRGuardParentEqual IRMessageReceiver (IRSomeParent IREventParent))
    Hstep eq_refl ltac:(
      cbn [participant_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as Hparent.
  cbn [guard_holds eval_node_expr eval_parent_expr event_message
    event_parent] in Hparent.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoParticipantReplyMore message parent) participant_ack_more_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action participant_ack_more_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message event_parent] in Haction.
  subst successor.
  eapply apply_parent_preserving_delivery_forest.
  - exact Hforest.
  - now symmetry.
  - intros Hdiscovered. apply parented_process_discovered.
  - intros item Hitem. contradiction.
Qed.

Theorem EchoStep_participant_reply_final_forest
    (state successor : @executable_echo_state node)
    (message : @echo_message node) (parent : node) :
  echo_parent_forest_well_formed state ->
  EchoStep state (EchoParticipantReplyFinal message parent) successor ->
  echo_parent_forest_well_formed successor.
Proof.
  intros Hforest Hstep.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoParticipantReplyFinal message parent)
    participant_ack_final_rule
    (IRGuardParentEqual IRMessageReceiver (IRSomeParent IREventParent))
    Hstep eq_refl ltac:(
      cbn [participant_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as Hparent.
  cbn [guard_holds eval_node_expr eval_parent_expr event_message
    event_parent] in Hparent.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoParticipantReplyFinal message parent) participant_ack_final_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action participant_ack_final_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message event_parent] in Haction.
  subst successor.
  eapply apply_parent_preserving_delivery_forest.
  - exact Hforest.
  - now symmetry.
  - intros Hdiscovered. apply parented_process_discovered.
  - intros item Hitem Hkind.
    cbn in Hitem. destruct Hitem as [Hitem | Hin];
      [subst item; discriminate | contradiction].
Qed.

Theorem EchoStep_initiator_reply_more_forest
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_parent_forest_well_formed state ->
  EchoStep state (EchoInitiatorReplyMore message) successor ->
  echo_parent_forest_well_formed successor.
Proof.
  intros Hforest Hstep.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyMore message) initiator_ack_more_rule
    (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
    Hstep eq_refl ltac:(
      cbn [initiator_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as Hequal.
  cbn [guard_holds eval_node_expr event_message] in Hequal.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyMore message) initiator_ack_more_rule
    (IRGuardParentEqual IRInitiatorNode IRNoParent)
    Hstep eq_refl ltac:(
      cbn [initiator_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as Hparent.
  cbn [guard_holds eval_node_expr eval_parent_expr] in Hparent.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyMore message) initiator_ack_more_rule
    (IRGuardNodesNonempty
      (IRNodesRemove IRMessageSender (IRNodesPending IRInitiatorNode)))
    Hstep eq_refl ltac:(
      cbn [initiator_ack_more_rule];
      repeat (first [left; reflexivity | right]))) as Hnonempty.
  cbn [guard_holds eval_nodes_expr eval_node_expr event_message] in Hnonempty.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoInitiatorReplyMore message) initiator_ack_more_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action initiator_ack_more_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message] in Haction.
  subst successor.
  eapply apply_parent_preserving_delivery_forest.
  - exact Hforest.
  - rewrite Hequal. now symmetry.
  - rewrite Hequal. intros Hdiscovered.
    now apply nonempty_root_discovered.
  - intros item Hitem. contradiction.
Qed.

Theorem EchoStep_initiator_reply_final_forest
    (state successor : @executable_echo_state node)
    (message : @echo_message node) :
  echo_parent_forest_well_formed state ->
  EchoStep state (EchoInitiatorReplyFinal message) successor ->
  echo_parent_forest_well_formed successor.
Proof.
  intros Hforest Hstep.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyFinal message) initiator_ack_final_rule
    (IRGuardNodeEqual IRMessageReceiver IRInitiatorNode)
    Hstep eq_refl ltac:(
      cbn [initiator_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as Hequal.
  cbn [guard_holds eval_node_expr event_message] in Hequal.
  pose proof (@EchoStep_selected_guard_holds node node_eq config
    state successor (EchoInitiatorReplyFinal message) initiator_ack_final_rule
    (IRGuardParentEqual IRInitiatorNode IRNoParent)
    Hstep eq_refl ltac:(
      cbn [initiator_ack_final_rule];
      repeat (first [left; reflexivity | right]))) as Hparent.
  cbn [guard_holds eval_node_expr eval_parent_expr] in Hparent.
  pose proof (@EchoStep_selected_action node node_eq config state successor
    (EchoInitiatorReplyFinal message) initiator_ack_final_rule
    Hstep eq_refl) as Haction.
  cbn [eval_action initiator_ack_final_rule ir_rule_action
    eval_process_expr eval_parent_expr eval_nodes_expr eval_node_expr
    eval_outbound_expr event_message] in Haction.
  subst successor.
  eapply apply_parent_preserving_delivery_forest.
  - exact Hforest.
  - rewrite Hequal. now symmetry.
  - rewrite Hequal. intros Hdiscovered.
    apply finished_root_discovered.
  - intros item Hitem. contradiction.
Qed.

Theorem EchoStep_preserves_parent_forest
    (state successor : @executable_echo_state node)
    (event : @echo_event node) :
  echo_parent_forest_well_formed state ->
  EchoStep state event successor ->
  echo_parent_forest_well_formed successor.
Proof.
  intros Hforest Hstep. destruct event.
  - exact (EchoStep_start_forest state successor ordered_neighbors Hstep).
  - eapply EchoStep_first_request_nonleaf_forest;
      [exact Hforest | exact Hstep].
  - eapply EchoStep_first_request_leaf_forest;
      [exact Hforest | exact Hstep].
  - eapply EchoStep_repeated_request_forest;
      [exact Hforest | exact Hstep].
  - eapply EchoStep_initiator_request_forest;
      [exact Hforest | exact Hstep].
  - eapply EchoStep_participant_reply_more_forest;
      [exact Hforest | exact Hstep].
  - eapply EchoStep_participant_reply_final_forest;
      [exact Hforest | exact Hstep].
  - eapply EchoStep_initiator_reply_more_forest;
      [exact Hforest | exact Hstep].
  - eapply EchoStep_initiator_reply_final_forest;
      [exact Hforest | exact Hstep].
Qed.

Lemma initial_executable_echo_state_parent_forest :
  echo_parent_forest_well_formed initial_executable_echo_state.
Proof.
  split.
  - intros child parent Hchild Hparent. cbn in Hparent. discriminate.
  - split.
    + intros message Hin. contradiction.
    + exists (fun _ => 0). intros child parent Hchild Hparent.
      cbn in Hparent. discriminate.
Qed.

Theorem echo_reachable_parent_forest
    (state : @executable_echo_state node) :
  @echo_reachable node node_eq config state ->
  echo_parent_forest_well_formed state.
Proof.
  intro Hreachable.
  induction Hreachable as [| before event after Hbefore IH Hstep].
  - apply initial_executable_echo_state_parent_forest.
  - eapply EchoStep_preserves_parent_forest.
    + exact IH.
    + exact Hstep.
Qed.

Lemma clos_trans_parent_rank_decreases
    (state : @executable_echo_state node)
    (rank : node -> nat) :
  (forall child parent,
      echo_parent_edge state child parent -> rank parent < rank child) ->
  forall child ancestor,
    clos_trans node (echo_parent_edge state) child ancestor ->
    rank ancestor < rank child.
Proof.
  intros Hedge child ancestor Hpath.
  induction Hpath.
  - now apply Hedge.
  - eapply Nat.lt_trans; eauto.
Qed.

Theorem echo_parent_ranked_acyclic
    (state : @executable_echo_state node) :
  echo_parent_ranked state ->
  echo_parent_acyclic state.
Proof.
  intros [rank Hrank] owner Hcycle.
  pose proof (clos_trans_parent_rank_decreases state rank
    ltac:(intros child parent [Hchild Hparent];
      now eapply Hrank)
    owner owner Hcycle) as Himpossible.
  lia.
Qed.

Theorem echo_reachable_parent_acyclic
    (state : @executable_echo_state node) :
  @echo_reachable node node_eq config state ->
  echo_parent_acyclic state.
Proof.
  intro Hreachable.
  apply echo_parent_ranked_acyclic.
  destruct (echo_reachable_parent_forest state Hreachable)
    as [Htargets [Hrequests Hranked]].
  exact Hranked.
Qed.

Corollary echo_reachable_no_self_parent
    (state : @executable_echo_state node) (owner : node) :
  @echo_reachable node node_eq config state ->
  In owner all_nodes ->
  process_parent (processes state owner) <> Some owner.
Proof.
  intros Hreachable Howner Hparent.
  pose proof (echo_reachable_parent_acyclic state Hreachable) as Hacyclic.
  apply (Hacyclic owner).
  apply t_step. split; assumption.
Qed.

Corollary echo_reachable_no_mutual_parent
    (state : @executable_echo_state node) (left right : node) :
  @echo_reachable node node_eq config state ->
  In left all_nodes ->
  In right all_nodes ->
  process_parent (processes state left) = Some right ->
  process_parent (processes state right) <> Some left.
Proof.
  intros Hreachable Hleft Hright Hleft_parent Hright_parent.
  pose proof (echo_reachable_parent_acyclic state Hreachable) as Hacyclic.
  apply (Hacyclic left).
  eapply t_trans with right.
  - apply t_step. split; assumption.
  - apply t_step. split; assumption.
Qed.

End EchoExecutableForest.

Arguments echo_discovered {node} _ _.
Arguments echo_parent_targets_discovered {node} config _.
Arguments echo_request_senders_discovered {node} _.
Arguments echo_parent_ranked {node} config _.
Arguments echo_parent_forest_well_formed {node} config _.
Arguments echo_parent_edge {node} config _ _ _.
Arguments echo_parent_acyclic {node} config _.
