(** * Concrete-to-abstract Echo branch refinement

    These lemmas normalize the canonical executable transition helpers into
    the list and packet operations used by [EchoAlgorithm].  They prove each
    of the nine abstract simulation branches independently of any aggregate
    concrete-step relation. *)

From Stdlib Require Import List Bool Arith Lia Sorting.Permutation.
Import ListNotations.
Require Import LTS.
Require Import EchoAlgorithm.
Require Import EchoExecutableAbstraction.
Require Import EchoExecutableTypes.

Section EchoExecutableRefinement.

Variable node : Type.
Variable node_eq : forall (n m : node), {n = m} + {n <> m}.

Lemma refinement_update_process_self
    (roles : node -> @echo_process node) target new_proc :
  update_process node_eq roles target new_proc target = new_proc.
Proof.
  unfold update_process.
  destruct (node_eq target target) as [_ | Hneq].
  - reflexivity.
  - contradiction Hneq. reflexivity.
Qed.

Lemma refinement_update_process_other
    (roles : node -> @echo_process node) target new_proc candidate :
  target <> candidate ->
  update_process node_eq roles target new_proc candidate = roles candidate.
Proof.
  intro Hneq.
  unfold update_process.
  destruct (node_eq target candidate); [contradiction | reflexivity].
Qed.

Lemma remove_node_not_in target nodes :
  ~ In target nodes -> remove_echo_node node_eq target nodes = nodes.
Proof.
  induction nodes as [| candidate rest IH]; intro Hnotin; simpl.
  - reflexivity.
  - destruct (node_eq target candidate) as [Heq | Hneq].
    + subst. exfalso. apply Hnotin. now left.
    + f_equal. apply IH. intro Hin. apply Hnotin. now right.
Qed.

Lemma remove_node_length_in target nodes :
  In target nodes ->
  S (List.length (remove_echo_node node_eq target nodes)) = List.length nodes.
Proof.
  induction nodes as [| candidate rest IH]; intro Hin; simpl in *.
  - contradiction.
  - destruct (node_eq target candidate) as [Heq | Hneq].
    + reflexivity.
    + destruct Hin as [Heq | Hin].
      * exfalso. apply Hneq. symmetry. exact Heq.
      * specialize (IH Hin). simpl. lia.
Qed.

Lemma filter_excluding_absent target nodes :
  ~ In target nodes ->
  List.filter
    (fun candidate => if node_eq candidate target then false else true)
    nodes = nodes.
Proof.
  induction nodes as [| candidate rest IH]; intro Hnotin; simpl.
  - reflexivity.
  - destruct (node_eq candidate target) as [Heq | Hneq].
    + subst candidate. exfalso. apply Hnotin. now left.
    + f_equal. apply IH. intro Hin. apply Hnotin. now right.
Qed.

(** Executable removal and abstract filtering agree on duplicate-free
    neighbor lists. *)
Lemma remove_node_eq_filter target nodes :
  NoDup nodes ->
  remove_echo_node node_eq target nodes =
  List.filter
    (fun candidate => if node_eq candidate target then false else true)
    nodes.
Proof.
  induction nodes as [| candidate rest IH]; intro Hnodup; simpl.
  - reflexivity.
  - inversion Hnodup as [| ? ? Hcandidate Hrest].
    destruct (node_eq target candidate) as [Heq | Hneq].
    + subst target.
      destruct (node_eq candidate candidate) as [_ | Hbad]; [| contradiction].
      simpl. symmetry. now apply filter_excluding_absent.
    + destruct (node_eq candidate target) as [Heq | Hneq'];
        [exfalso; apply Hneq; symmetry; exact Heq |].
      f_equal. now apply IH.
Qed.

Definition alpha_outbound
    (sender : node) (item : @echo_outbound node) : @echo_packet node :=
  mkPkt sender (outbound_receiver item) (alpha_kind (outbound_kind item)).

Lemma alpha_materialize_outbound
    (next_id : nat) (sender : node) (outbound : list (@echo_outbound node)) :
  List.map alpha_message
    (materialize_echo_outbound next_id sender outbound) =
  List.map (alpha_outbound sender) outbound.
Proof.
  revert next_id.
  induction outbound as [| item rest IH]; intros next_id; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma alpha_materialize_echo
    (next_id : nat) (sender : node) (receivers : list node) :
  List.map alpha_message
    (materialize_echo_outbound next_id sender
      (List.map (mkEchoOutbound EchoRequest) receivers)) =
  send_to_all sender receivers Token.
Proof.
  rewrite alpha_materialize_outbound.
  unfold send_to_all.
  induction receivers as [| receiver rest IH]; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

Lemma alpha_materialize_ack
    (next_id : nat) (sender receiver : node) :
  List.map alpha_message
    (materialize_echo_outbound next_id sender [mkEchoOutbound EchoReply receiver]) =
  [mkPkt sender receiver Echo].
Proof.
  reflexivity.
Qed.

Lemma materialize_outbound_length
    (next_id : nat) (sender : node) (outbound : list (@echo_outbound node)) :
  List.length (materialize_echo_outbound next_id sender outbound) =
  List.length outbound.
Proof.
  revert next_id.
  induction outbound; intros next_id; simpl.
  - reflexivity.
  - now rewrite IHoutbound.
Qed.

Lemma materialize_outbound_ids
    (next_id : nat) (sender : node) (outbound : list (@echo_outbound node)) :
  List.map message_id (materialize_echo_outbound next_id sender outbound) =
  List.seq next_id (List.length outbound).
Proof.
  revert next_id.
  induction outbound as [| item rest IH]; intros next_id; simpl.
  - reflexivity.
  - now rewrite IH.
Qed.

(** Consecutive allocation makes each freshly materialized batch unique and
    keeps every allocated identifier below the following counter value. *)
Lemma materialize_outbound_ids_nodup
    (next_id : nat) (sender : node) (outbound : list (@echo_outbound node)) :
  NoDup
    (List.map message_id
      (materialize_echo_outbound next_id sender outbound)).
Proof.
  rewrite materialize_outbound_ids.
  apply seq_NoDup.
Qed.

Lemma materialize_outbound_id_bounds
    (next_id : nat) (sender : node) (outbound : list (@echo_outbound node))
    (message : @echo_message node) :
  In message (materialize_echo_outbound next_id sender outbound) ->
  next_id <= message_id message < next_id + List.length outbound.
Proof.
  intro Hin.
  assert (Hid : In (message_id message)
      (List.map message_id
        (materialize_echo_outbound next_id sender outbound))).
  { apply in_map. exact Hin. }
  rewrite materialize_outbound_ids in Hid.
  now apply in_seq in Hid.
Qed.

Lemma executable_start_messages_well_formed
    (initiator : node) (s : @executable_echo_state node) ordered_neighbors :
  started s = false ->
  message_store s = [] ->
  next_message_id s = 1 ->
  executable_messages_well_formed
    (apply_echo_start node_eq initiator s ordered_neighbors).
Proof.
  intros Hstarted Hstore Hnext.
  unfold executable_messages_well_formed, apply_echo_start.
  simpl.
  rewrite Hstore, Hnext. simpl.
  split.
  - apply materialize_outbound_ids_nodup.
  - intros message Hin.
    pose proof (materialize_outbound_id_bounds
      1 initiator (List.map (mkEchoOutbound EchoRequest) ordered_neighbors)
      message Hin) as [_ Hupper].
    unfold next_echo_message_id_after. exact Hupper.
Qed.

Lemma node_is_pending_true
    (p : @echo_process node) candidate :
  In candidate (process_pending p) ->
  @node_is_pending node node_eq p candidate = true.
Proof.
  unfold node_is_pending.
  induction (process_pending p) as [| pending rest IH]; intro Hin; simpl in *.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + subst pending.
      destruct (node_eq candidate candidate); [reflexivity | contradiction].
    + destruct (node_eq candidate pending); [reflexivity | now apply IH].
Qed.

Lemma node_is_pending_true_iff
    (p : @echo_process node) candidate :
  @node_is_pending node node_eq p candidate = true <->
  In candidate (process_pending p).
Proof.
  unfold node_is_pending.
  rewrite existsb_exists. split.
  - intros [pending [Hin Htest]].
    destruct (node_eq candidate pending) as [Heq | Hneq].
    + now subst pending.
    + discriminate.
  - intro Hin. exists candidate. split; [exact Hin |].
    destruct (node_eq candidate candidate); [reflexivity | contradiction].
Qed.

Lemma node_is_pending_false_iff
    (p : @echo_process node) candidate :
  @node_is_pending node node_eq p candidate = false <->
  ~ In candidate (process_pending p).
Proof.
  split.
  - intros Hfalse Hin.
    pose proof (node_is_pending_true p candidate Hin) as Htrue.
    rewrite Hfalse in Htrue. discriminate.
  - intro Hnotin.
    destruct (@node_is_pending node node_eq p candidate) eqn:Hpending.
    + apply node_is_pending_true_iff in Hpending. contradiction.
    + reflexivity.
Qed.

Lemma pending_complement_in_iff
    (p : @echo_process node) expected candidate :
  In candidate
      (List.filter
        (fun item => negb (@node_is_pending node node_eq p item))
        expected) <->
  In candidate expected /\ ~ In candidate (process_pending p).
Proof.
  rewrite filter_In. split.
  - intros [Hin Hnotpending]. split; [exact Hin |].
    apply negb_true_iff in Hnotpending.
    now apply node_is_pending_false_iff in Hnotpending.
  - intros [Hin Hnotin]. split; [exact Hin |].
    apply negb_true_iff.
    now apply node_is_pending_false_iff.
Qed.

Lemma remove_node_in_iff target candidate nodes :
  NoDup nodes ->
  (In candidate (remove_echo_node node_eq target nodes) <->
   In candidate nodes /\ candidate <> target).
Proof.
  induction nodes as [| head rest IH]; intro Hnodup; simpl.
  - tauto.
  - inversion Hnodup as [| ? ? Hhead Hrest].
    destruct (node_eq target head) as [Heq | Hneq].
    + subst head. split.
      * intro Hin. split; [now right |].
        intro Hcandidate_eq. subst candidate.
        apply Hhead. now rewrite <- Heq.
      * intros [[Hcandidate_eq | Hin] Hcandidate].
        -- exfalso. apply Hcandidate.
           transitivity x; [symmetry; exact Hcandidate_eq | symmetry; exact Heq].
        -- exact Hin.
    + split.
      * intros [Hcandidate_eq | Hin_removed].
        -- subst candidate. split; [now left |].
           intro Htarget. apply Hneq. symmetry. exact Htarget.
        -- apply IH in Hin_removed; [| exact Hrest].
           destruct Hin_removed as [Hin Hcandidate].
           split; [now right | exact Hcandidate].
      * intros [[Hcandidate_eq | Hin] Hcandidate].
        -- now left.
        -- right. apply IH; [exact Hrest |]. split; assumption.
Qed.

Lemma remove_node_nodup target nodes :
  NoDup nodes -> NoDup (remove_echo_node node_eq target nodes).
Proof.
  induction nodes as [| head rest IH]; intro Hnodup; simpl.
  - constructor.
  - inversion Hnodup as [| ? ? Hhead Hrest].
    destruct (node_eq target head).
    + exact Hrest.
    + constructor.
      * intro Hin.
        apply remove_node_in_iff in Hin; [| exact Hrest].
        destruct Hin as [Hin _]. now apply Hhead in Hin.
      * now apply IH.
Qed.

(** Removing one valid pending sender adds exactly that sender to the
    acknowledged complement, modulo list order. *)
Lemma pending_complement_remove
    expected pending sender :
  NoDup expected ->
  NoDup pending ->
  In sender pending ->
  (forall candidate, In candidate pending -> In candidate expected) ->
  Permutation
    (List.filter
      (fun candidate => negb
        (@node_is_pending node node_eq
          (mkEchoProcess None (remove_echo_node node_eq sender pending) false)
          candidate)) expected)
    (sender ::
      List.filter
        (fun candidate => negb
          (@node_is_pending node node_eq
            (mkEchoProcess None pending false) candidate)) expected).
Proof.
  intros Hexpected Hpending Hsender Hsubset.
  apply NoDup_Permutation.
  - now apply NoDup_filter.
  - constructor.
    + intro Hsender_old.
      apply pending_complement_in_iff in Hsender_old as [_ Hnotpending].
      contradiction.
    + now apply NoDup_filter.
  - intro candidate. split.
    + intro Hnew.
      apply pending_complement_in_iff in Hnew as [Hin_expected Hnotnew].
      destruct (node_eq candidate sender) as [Heq | Hneq].
      * now left.
      * right. apply pending_complement_in_iff. split; [exact Hin_expected |].
        intro Hin_pending. apply Hnotnew.
        apply remove_node_in_iff; [exact Hpending |].
        split; assumption.
    + intros [Heq | Hold].
      * subst candidate. apply pending_complement_in_iff. split.
        -- now apply Hsubset.
        -- intro Hin_removed.
           apply remove_node_in_iff in Hin_removed; [| exact Hpending].
           destruct Hin_removed as [_ Hneq]. contradiction.
      * apply pending_complement_in_iff in Hold as [Hin_expected Hnotold].
        apply pending_complement_in_iff. split; [exact Hin_expected |].
        intro Hin_removed.
        apply remove_node_in_iff in Hin_removed; [| exact Hpending].
        destruct Hin_removed as [Hin_pending _].
        now apply Hnotold in Hin_pending.
Qed.

Lemma pending_complement_remove_proc
    expected (p : @echo_process node) sender :
  NoDup expected ->
  NoDup (process_pending p) ->
  In sender (process_pending p) ->
  (forall candidate, In candidate (process_pending p) -> In candidate expected) ->
  Permutation
    (List.filter
      (fun candidate => negb
        (@node_is_pending node node_eq
          (mkEchoProcess (process_parent p)
            (remove_echo_node node_eq sender (process_pending p))
            (process_finished p)) candidate)) expected)
    (sender ::
      List.filter
        (fun candidate => negb
          (@node_is_pending node node_eq p candidate)) expected).
Proof.
  intros Hexpected Hpending Hsender Hsubset.
  unfold node_is_pending. simpl.
  exact (pending_complement_remove expected (process_pending p) sender
    Hexpected Hpending Hsender Hsubset).
Qed.

Lemma pending_covers_filter_empty
    (p : @echo_process node) candidates :
  (forall candidate, In candidate candidates ->
     In candidate (process_pending p)) ->
  List.filter
    (fun candidate => negb (@node_is_pending node node_eq p candidate))
    candidates = [].
Proof.
  intro Hcovers.
  induction candidates as [| candidate rest IH]; simpl.
  - reflexivity.
  - rewrite (node_is_pending_true p candidate).
    + simpl. apply IH. intros other Hin. apply Hcovers. now right.
    + apply Hcovers. now left.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Startup branch of the forward simulation *)

Definition concrete_start_ready
    (initiator : node) (s : @executable_echo_state node) : Prop :=
  started s = false /\
  processes s initiator = initial_echo_process /\
  message_store s = [] /\
  next_message_id s = 1.

Lemma executable_start_step_sound
    (initiator : node) (all_nodes : list node) (adj : node -> node -> bool)
    (s : @executable_echo_state node) ordered_neighbors (rq : @echo_state node) :
  concrete_start_ready initiator s ->
  Permutation ordered_neighbors (nbrs all_nodes adj initiator) ->
  NoDup (nbrs all_nodes adj initiator) ->
  @ExecutableStateRefines node node_eq initiator all_nodes adj s rq ->
  exists rq',
    @echo_step node node_eq initiator all_nodes adj
      rq ELStart rq' /\
    @ExecutableStateRefines node node_eq initiator all_nodes adj
      (apply_echo_start node_eq initiator s ordered_neighbors) rq'.
Proof.
  intros Hready Horder Hneighbors Hrefines.
  destruct Hready as [Hstarted [Hroot [Hstore Hnext]]].
  destruct Hrefines as
    [Hparent Hphase Hpending Hacks Hmessages Hids Hroles_wf Hpending_wf].
  exists (@initiator_start node node_eq initiator all_nodes adj rq).
  split.
  - apply step_start.
    rewrite <- Hphase.
    unfold alpha_phase.
    rewrite Hroot, Hstarted.
    unfold initial_echo_process. simpl.
    destruct (node_eq initiator initiator); [reflexivity | contradiction].
  - constructor.
    + intro n.
      destruct (node_eq initiator n) as [Heq | Hneq].
      * subst n.
        unfold apply_echo_start, initiator_start. simpl.
        unfold update_proc.
        destruct (node_eq initiator initiator);
          [rewrite refinement_update_process_self; reflexivity | contradiction].
      * unfold apply_echo_start, initiator_start. simpl.
        unfold update_proc.
        destruct (node_eq initiator n); [contradiction |].
        rewrite refinement_update_process_other by exact Hneq.
        apply Hparent.
    + intro n.
      destruct (node_eq initiator n) as [Heq | Hneq].
      * subst n.
        unfold apply_echo_start, initiator_start. simpl.
        unfold update_proc.
        destruct (node_eq initiator initiator) as [_ | Hbad];
          [| contradiction Hbad; reflexivity].
        unfold alpha_phase.
        unfold update_process.
        destruct (node_eq initiator initiator) as [_ | Hbad];
          [simpl | contradiction Hbad; reflexivity].
        destruct (node_eq initiator initiator); [reflexivity | contradiction].
      * unfold apply_echo_start, initiator_start. simpl.
        unfold update_proc.
        destruct (node_eq initiator n); [contradiction |].
        unfold alpha_phase.
        unfold update_process.
        destruct (node_eq initiator n); [contradiction |].
        destruct (node_eq n initiator) as [Heq' | Hneq'];
          [exfalso; apply Hneq; symmetry; exact Heq' |].
        destruct (node_eq initiator n); [contradiction |].
        specialize (Hphase n).
        unfold alpha_phase in Hphase.
        destruct (node_eq n initiator); [contradiction |].
        cbn.
        destruct (node_eq initiator n); [contradiction |].
        exact Hphase.
    + intro n.
      destruct (node_eq initiator n) as [Heq | Hneq].
      * subst n.
        unfold apply_echo_start, initiator_start. simpl.
        rewrite refinement_update_process_self.
        unfold update_proc.
        destruct (node_eq initiator initiator) as [_ | Hbad];
          [| contradiction Hbad; reflexivity].
        now apply Permutation_length in Horder.
      * unfold apply_echo_start, initiator_start. simpl.
        rewrite refinement_update_process_other by exact Hneq.
        unfold update_proc.
        destruct (node_eq initiator n); [contradiction |].
        apply Hpending.
    + intro n.
      destruct (node_eq initiator n) as [Heq | Hneq].
      * subst n.
        unfold apply_echo_start, initiator_start. simpl.
        unfold update_proc.
        destruct (node_eq initiator initiator) as [_ | Hbad];
          [| contradiction Hbad; reflexivity].
        unfold alpha_acknowledged, alpha_phase, expected_replies.
        unfold update_process.
        destruct (node_eq initiator initiator) as [_ | Hbad];
          [| contradiction Hbad; reflexivity].
        simpl.
        destruct (node_eq initiator initiator) as [_ | Hbad];
          [| contradiction Hbad; reflexivity].
        simpl.
        assert (Hempty :
          List.filter
            (fun candidate => negb
              (@node_is_pending node node_eq
                (mkEchoProcess None ordered_neighbors false) candidate))
            (nbrs all_nodes adj initiator) = []).
        { apply pending_covers_filter_empty.
          intros candidate Hin.
          eapply Permutation_in.
          - apply Permutation_sym. exact Horder.
          - exact Hin. }
        rewrite Hempty. apply Permutation_refl.
      * unfold apply_echo_start, initiator_start. simpl.
        unfold update_proc.
        destruct (node_eq initiator n); [contradiction |].
        unfold alpha_acknowledged, alpha_phase, expected_replies.
        unfold update_process.
        destruct (node_eq initiator n); [contradiction |].
        destruct (node_eq n initiator) as [Heq' | Hneq'];
          [exfalso; apply Hneq; symmetry; exact Heq' |].
        cbn.
        destruct (node_eq initiator n); [contradiction |].
        specialize (Hacks n).
        unfold alpha_acknowledged, alpha_phase, expected_replies in Hacks.
        destruct (node_eq n initiator); [contradiction |].
        exact Hacks.
    + change (Permutation
        (List.map alpha_message
          (message_store s ++ materialize_echo_outbound
            (next_message_id s) initiator
            (List.map (mkEchoOutbound EchoRequest) ordered_neighbors)))
        (es_msgs rq ++ send_to_all initiator
          (nbrs all_nodes adj initiator) Token)).
      rewrite map_app, alpha_materialize_echo.
      apply Permutation_app.
      * exact Hmessages.
      * now apply Permutation_map.
    + apply executable_start_messages_well_formed.
      assumption.
      assumption.
      assumption.
    + unfold executable_processes_well_formed.
      intros n Hnotroot Hfinished.
      unfold apply_echo_start in Hfinished. simpl in Hfinished.
      rewrite refinement_update_process_other in Hfinished.
      2: { intro Heq. apply Hnotroot. symmetry. exact Heq. }
      destruct (Hroles_wf n Hnotroot Hfinished) as [parent Hparent_old].
      exists parent.
      unfold apply_echo_start. simpl.
      rewrite refinement_update_process_other.
      * exact Hparent_old.
      * intro Heq. apply Hnotroot. symmetry. exact Heq.
    + unfold executable_pending_well_formed.
      intro n.
      unfold apply_echo_start. simpl.
      destruct (node_eq initiator n) as [Heq | Hneq].
      * subst n. rewrite refinement_update_process_self.
        unfold expected_replies.
        destruct (node_eq initiator initiator) as [_ | Hbad]; [| contradiction].
        split.
        -- eapply Permutation_NoDup.
           ++ apply Permutation_sym. exact Horder.
           ++ exact Hneighbors.
        -- intros candidate Hin.
           eapply Permutation_in; [exact Horder | exact Hin].
      * rewrite refinement_update_process_other by exact Hneq.
        exact (Hpending_wf n).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Queue removal before and after message-ID erasure *)

Lemma refinement_remove_message_in
    (message : @echo_message node) selected_id messages :
  In message (remove_echo_message selected_id messages) ->
  In message messages.
Proof.
  induction messages as [| head rest IH]; simpl; intro Hin.
  - contradiction.
  - destruct (Nat.eqb selected_id (message_id head)).
    + now right.
    + destruct Hin as [Heq | Hin].
      * now left.
      * right. now apply IH.
Qed.

Lemma refinement_remove_message_ids_nodup selected_id
    (messages : list (@echo_message node)) :
  NoDup (List.map message_id messages) ->
  NoDup
    (List.map message_id (remove_echo_message selected_id messages)).
Proof.
  induction messages as [| head rest IH]; intro Hnodup; simpl.
  - constructor.
  - inversion Hnodup as [| head_id rest_ids Hhead Hrest].
    destruct (Nat.eqb selected_id (message_id head)).
    + exact Hrest.
    + simpl. constructor.
      * intro Hid.
        apply in_map_iff in Hid as [message [Heq Hin]].
        apply Hhead.
        rewrite <- Heq.
        apply in_map.
        now apply refinement_remove_message_in in Hin.
      * now apply IH.
Qed.

(** All delivery branches remove one old envelope and append a consecutive
    fresh batch.  This single lemma discharges their ID-side obligation. *)
Lemma executable_delivery_messages_well_formed
    (s : @executable_echo_state node) (message : @echo_message node)
    (new_proc : @echo_process node) outbound :
  executable_messages_well_formed s ->
  executable_messages_well_formed
    (apply_echo_delivery node_eq s message new_proc outbound).
Proof.
  intros [Hnodup Hbound].
  unfold executable_messages_well_formed, apply_echo_delivery.
  simpl. split.
  - rewrite map_app.
    apply NoDup_app.
    + now apply refinement_remove_message_ids_nodup.
    + apply materialize_outbound_ids_nodup.
    + intros old_id Hold Hnew.
      apply in_map_iff in Hold as [old_message [Heq_old Hin_old]].
      apply in_map_iff in Hnew as [new_message [Heq_new Hin_new]].
      pose proof (Hbound old_message
        (refinement_remove_message_in old_message
          (message_id message) (message_store s) Hin_old)) as Hold_bound.
      pose proof (materialize_outbound_id_bounds
        (next_message_id s) (message_receiver message) outbound
        new_message Hin_new) as [Hnew_bound _].
      rewrite Heq_old in Hold_bound.
      rewrite Heq_new in Hnew_bound.
      lia.
  - intros queued Hin.
    apply in_app_or in Hin as [Hin_old | Hin_new].
    + pose proof (Hbound queued
        (refinement_remove_message_in queued
          (message_id message) (message_store s) Hin_old)).
      unfold next_echo_message_id_after. lia.
    + pose proof (materialize_outbound_id_bounds
        (next_message_id s) (message_receiver message) outbound
        queued Hin_new) as [_ Hupper].
      unfold next_echo_message_id_after. exact Hupper.
Qed.

Lemma delivery_same_role_roles
    (s : @executable_echo_state node) (message : @echo_message node) outbound n :
  processes
    (apply_echo_delivery node_eq s message
      (processes s (message_receiver message)) outbound) n =
  processes s n.
Proof.
  unfold apply_echo_delivery. simpl.
  destruct (node_eq (message_receiver message) n) as [Heq | Hneq].
  - subst n. now rewrite refinement_update_process_self.
  - now rewrite refinement_update_process_other.
Qed.

Lemma delivery_same_role_alpha_phase
    (initiator : node) (s : @executable_echo_state node)
    (message : @echo_message node) outbound n :
  @alpha_phase node node_eq initiator
    (apply_echo_delivery node_eq s message
      (processes s (message_receiver message)) outbound) n =
  @alpha_phase node node_eq initiator s n.
Proof.
  unfold alpha_phase.
  rewrite delivery_same_role_roles. simpl. reflexivity.
Qed.

Lemma delivery_same_role_alpha_acknowledged
    (initiator : node) (all_nodes : list node) (adj : node -> node -> bool)
    (s : @executable_echo_state node) (message : @echo_message node) outbound n :
  @alpha_acknowledged node node_eq initiator all_nodes adj
    (apply_echo_delivery node_eq s message
      (processes s (message_receiver message)) outbound) n =
  @alpha_acknowledged node node_eq initiator all_nodes adj s n.
Proof.
  unfold alpha_acknowledged.
  rewrite delivery_same_role_alpha_phase.
  rewrite delivery_same_role_roles.
  unfold expected_replies.
  reflexivity.
Qed.

Lemma delivery_other_roles
    (s : @executable_echo_state node) (message : @echo_message node)
    (new_proc : @echo_process node) outbound n :
  message_receiver message <> n ->
  processes (apply_echo_delivery node_eq s message new_proc outbound) n =
  processes s n.
Proof.
  intro Hneq. unfold apply_echo_delivery. simpl.
  now rewrite refinement_update_process_other.
Qed.

Lemma delivery_other_alpha_phase
    (initiator : node) (s : @executable_echo_state node)
    (message : @echo_message node) (new_proc : @echo_process node) outbound n :
  message_receiver message <> n ->
  @alpha_phase node node_eq initiator
    (apply_echo_delivery node_eq s message new_proc outbound) n =
  @alpha_phase node node_eq initiator s n.
Proof.
  intro Hneq. unfold alpha_phase.
  rewrite delivery_other_roles by exact Hneq. simpl. reflexivity.
Qed.

Lemma delivery_other_alpha_acknowledged
    (initiator : node) (all_nodes : list node) (adj : node -> node -> bool)
    (s : @executable_echo_state node) (message : @echo_message node)
    (new_proc : @echo_process node) outbound n :
  message_receiver message <> n ->
  @alpha_acknowledged node node_eq initiator all_nodes adj
    (apply_echo_delivery node_eq s message new_proc outbound) n =
  @alpha_acknowledged node node_eq initiator all_nodes adj s n.
Proof.
  intro Hneq. unfold alpha_acknowledged.
  rewrite delivery_other_alpha_phase by exact Hneq.
  rewrite delivery_other_roles by exact Hneq.
  unfold expected_replies.
  reflexivity.
Qed.

Definition echo_packet_eq_dec
    (left right : @echo_packet node) : {left = right} + {left <> right}.
Proof.
  destruct left as [left_source left_destination left_body].
  destruct right as [right_source right_destination right_body].
  destruct (node_eq left_source right_source) as [Hsource | Hsource].
  - subst right_source.
    destruct (node_eq left_destination right_destination)
      as [Hdestination | Hdestination].
    + subst right_destination.
      destruct left_body, right_body.
      * left. reflexivity.
      * right. discriminate.
      * right. discriminate.
      * left. reflexivity.
    + right. intro Heq. inversion Heq. contradiction.
  - right. intro Heq. inversion Heq. contradiction.
Defined.

Lemma remove_pkt_head (packet : @echo_packet node) messages :
  remove_pkt node_eq packet (packet :: messages) = messages.
Proof.
  destruct packet as [source destination body].
  simpl.
  destruct (node_eq source source) as [_ | Hsource].
  - destruct (node_eq destination destination) as [_ | Hdestination].
    + now destruct body.
    + contradiction Hdestination. reflexivity.
  - contradiction Hsource. reflexivity.
Qed.

Lemma remove_pkt_cons_neq
    (packet head : @echo_packet node) messages :
  packet <> head ->
  remove_pkt node_eq packet (head :: messages) =
  head :: remove_pkt node_eq packet messages.
Proof.
  intros Hneq.
  destruct packet as [packet_source packet_destination packet_body].
  destruct head as [head_source head_destination head_body].
  simpl in *.
  destruct (node_eq head_source packet_source) as [Hsource | Hsource].
  - subst head_source.
    destruct (node_eq head_destination packet_destination)
      as [Hdestination | Hdestination].
    + subst head_destination.
      destruct head_body, packet_body; try reflexivity;
        exfalso; apply Hneq; reflexivity.
    + reflexivity.
  - reflexivity.
Qed.

Lemma remove_pkt_extract (packet : @echo_packet node) messages :
  In packet messages ->
  Permutation
    (packet :: remove_pkt node_eq packet messages)
    messages.
Proof.
  induction messages as [| head rest IH]; intro Hin.
  - contradiction.
  - destruct (echo_packet_eq_dec packet head) as [Heq | Hneq].
    + subst head. rewrite remove_pkt_head. apply Permutation_refl.
    + assert (Hin_rest : In packet rest).
      { destruct Hin as [Heq | Hin].
        - exfalso. apply Hneq. symmetry. exact Heq.
        - exact Hin. }
      rewrite remove_pkt_cons_neq by exact Hneq.
      eapply Permutation_trans.
      * apply perm_swap.
      * apply perm_skip. now apply IH.
Qed.

Lemma remove_pkt_permutation
    (packet : @echo_packet node) left right :
  Permutation left right ->
  In packet left ->
  Permutation
    (remove_pkt node_eq packet left)
    (remove_pkt node_eq packet right).
Proof.
  intros Hperm Hin_left.
  assert (Hin_right : In packet right).
  { eapply Permutation_in; eauto. }
  pose proof (remove_pkt_extract packet left Hin_left) as Hleft.
  pose proof (remove_pkt_extract packet right Hin_right) as Hright.
  eapply Permutation_cons_inv.
  eapply Permutation_trans.
  - exact Hleft.
  - eapply Permutation_trans.
    + exact Hperm.
    + now apply Permutation_sym.
Qed.

Lemma refinement_remove_message_head
    (message : @echo_message node) messages :
  remove_echo_message (message_id message) (message :: messages) = messages.
Proof.
  simpl. now rewrite Nat.eqb_refl.
Qed.

Lemma refinement_remove_message_cons_id_neq
    (target head : @echo_message node) messages :
  message_id target <> message_id head ->
  remove_echo_message (message_id target) (head :: messages) =
  head :: remove_echo_message (message_id target) messages.
Proof.
  intro Hneq. simpl.
  apply Nat.eqb_neq in Hneq. now rewrite Hneq.
Qed.

Lemma refinement_remove_message_extract
    (target : @echo_message node) messages :
  NoDup (List.map message_id messages) ->
  In target messages ->
  Permutation
    (target :: remove_echo_message (message_id target) messages)
    messages.
Proof.
  induction messages as [| head rest IH]; intros Hnodup Hin.
  - contradiction.
  - inversion Hnodup as [| head_id rest_ids Hhead_notin Hrest_nodup].
    destruct Hin as [Heq | Hin_rest].
    + subst head. rewrite refinement_remove_message_head. apply Permutation_refl.
    + assert (Hid_neq : message_id target <> message_id head).
      { intro Hid.
        apply Hhead_notin.
        rewrite <- Hid.
        apply in_map. exact Hin_rest. }
      rewrite refinement_remove_message_cons_id_neq by exact Hid_neq.
      eapply Permutation_trans.
      * apply perm_swap.
      * apply perm_skip. now apply IH.
Qed.

(** Removing a concrete envelope by its unique executable message ID
    corresponds, after ID erasure, to removing one structurally equal packet
    from the abstract Rocq bag. *)
Lemma alpha_remove_message
    (target : @echo_message node) messages :
  NoDup (List.map message_id messages) ->
  In target messages ->
  Permutation
    (List.map alpha_message
      (remove_echo_message (message_id target) messages))
    (remove_pkt node_eq (alpha_message target)
      (List.map alpha_message messages)).
Proof.
  intros Hnodup Hin.
  pose proof (refinement_remove_message_extract target messages Hnodup Hin)
    as Hpython.
  apply (Permutation_map alpha_message) in Hpython.
  assert (Habstract_in : In (alpha_message target)
      (List.map alpha_message messages)).
  { apply in_map. exact Hin. }
  pose proof (remove_pkt_extract (alpha_message target)
    (List.map alpha_message messages) Habstract_in) as Hrocq.
  eapply Permutation_cons_inv.
  eapply Permutation_trans.
  - exact Hpython.
  - now apply Permutation_sym.
Qed.

Lemma alpha_delivery_residual
    (target : @echo_message node) (s : @executable_echo_state node)
    (rq_messages : list (@echo_packet node)) :
  executable_messages_well_formed s ->
  In target (message_store s) ->
  Permutation (List.map alpha_message (message_store s)) rq_messages ->
  Permutation
    (List.map alpha_message
      (remove_echo_message (message_id target) (message_store s)))
    (remove_pkt node_eq (alpha_message target) rq_messages).
Proof.
  intros [Hnodup _] Hin Hstore.
  eapply Permutation_trans.
  - now apply alpha_remove_message.
  - apply remove_pkt_permutation.
    + exact Hstore.
    + apply in_map. exact Hin.
Qed.

(* ------------------------------------------------------------------ *)
(** ** First ECHO at a non-leaf participant *)

Lemma executable_first_echo_nonleaf_step_sound
    (initiator : node) (all_nodes : list node) (adj : node -> node -> bool)
    (s : @executable_echo_state node) selected_id sender receiver ordered_forwards
    (rq : @echo_state node) :
  receiver <> initiator ->
  In (mkEchoMessage selected_id EchoRequest sender receiver) (message_store s) ->
  processes s receiver = initial_echo_process ->
  Permutation ordered_forwards
    (remove_echo_node node_eq sender (nbrs all_nodes adj receiver)) ->
  ordered_forwards <> [] ->
  NoDup (nbrs all_nodes adj receiver) ->
  @ExecutableStateRefines node node_eq initiator all_nodes adj s rq ->
  exists rq',
    @echo_step node node_eq initiator all_nodes adj rq
      (ELDeliver (mkPkt sender receiver Token)) rq' /\
    @ExecutableStateRefines node node_eq initiator all_nodes adj
      (apply_echo_delivery node_eq s
        (mkEchoMessage selected_id EchoRequest sender receiver)
        (mkEchoProcess (Some sender) ordered_forwards false)
        (List.map (mkEchoOutbound EchoRequest) ordered_forwards)) rq'.
Proof.
  intros Hnotroot Hin Hinitial Horder Hnonempty Hneighbors Hrefines.
  destruct Hrefines as
    [Hparent Hphase Hpending Hacks Hstore Hids Hroles_wf Hpending_wf].
  assert (Hremove_filter :
    remove_echo_node node_eq sender (nbrs all_nodes adj receiver) =
    List.filter
      (fun candidate => if node_eq candidate sender then false else true)
      (nbrs all_nodes adj receiver)).
  { now apply remove_node_eq_filter. }
  rewrite Hremove_filter in Horder.
  set (forwards := List.filter
    (fun candidate => if node_eq candidate sender then false else true)
    (nbrs all_nodes adj receiver)) in *.
  assert (Hforwards_nonempty : forwards <> []).
  { intro Heq. apply Hnonempty.
    apply Permutation_nil.
    rewrite Heq in Horder. now apply Permutation_sym. }
  assert (Hforwards_length : Nat.eqb (List.length forwards) 0 = false).
  { apply Nat.eqb_neq. intro Hzero.
    apply Hforwards_nonempty. now apply length_zero_iff_nil. }
  assert (Hreceiver_idle : ps_phase (es_procs rq receiver) = Idle).
  { rewrite <- Hphase.
    unfold alpha_phase.
    destruct (node_eq receiver initiator); [contradiction |].
    rewrite Hinitial. reflexivity. }
  assert (Hin_rq : In (mkPkt sender receiver Token) (es_msgs rq)).
  { assert (Hin_alpha : In
        (alpha_message
          (mkEchoMessage selected_id EchoRequest sender receiver))
        (List.map alpha_message (message_store s))).
    { apply in_map. exact Hin. }
    eapply Permutation_in; [exact Hstore | exact Hin_alpha]. }
  set (rq' := mkEchoState
    (update_proc node_eq (es_procs rq) receiver
      (mkProc Active (Some sender) (List.length forwards) []))
    (remove_pkt node_eq (mkPkt sender receiver Token) (es_msgs rq) ++
      send_to_all receiver forwards Token)).
  exists rq'. split.
  - eapply step_deliver.
    + exact Hin_rq.
    + subst rq'.
      unfold handle_msg. simpl.
      rewrite Hreceiver_idle.
      fold forwards.
      now rewrite Hforwards_length.
  - subst rq'. constructor.
    + intro n.
      destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n.
        unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_self.
        unfold update_proc.
        destruct (node_eq receiver receiver); [reflexivity | contradiction].
      * unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_other by exact Hneq.
        unfold update_proc.
        destruct (node_eq receiver n); [contradiction |].
        apply Hparent.
    + intro n.
      destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n.
        unfold apply_echo_delivery. simpl.
        unfold alpha_phase, update_process, update_proc.
        destruct (node_eq receiver receiver) as [_ | Hbad]; [| contradiction].
        destruct (node_eq receiver initiator); [contradiction |].
        cbn.
        destruct (node_eq receiver receiver); [reflexivity | contradiction].
      * unfold apply_echo_delivery. simpl.
        unfold update_proc.
        destruct (node_eq receiver n); [contradiction |].
        unfold alpha_phase, update_process.
        destruct (node_eq receiver n); [contradiction |].
        cbn.
        destruct (node_eq receiver n); [contradiction |].
        apply Hphase.
    + intro n.
      destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n.
        unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_self.
        unfold update_proc.
        destruct (node_eq receiver receiver) as [_ | Hbad]; [| contradiction].
        now apply Permutation_length in Horder.
      * unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_other by exact Hneq.
        unfold update_proc.
        destruct (node_eq receiver n); [contradiction |].
        apply Hpending.
    + intro n.
      destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n.
        unfold apply_echo_delivery. simpl.
        unfold update_proc.
        destruct (node_eq receiver receiver) as [_ | Hbad]; [| contradiction].
        unfold alpha_acknowledged, alpha_phase, expected_replies,
          update_process.
        destruct (node_eq receiver receiver) as [_ | Hbad]; [| contradiction].
        destruct (node_eq receiver initiator); [contradiction |].
        simpl.
        assert (Hempty :
          List.filter
            (fun candidate => negb
              (@node_is_pending node node_eq
                (mkEchoProcess (Some sender) ordered_forwards false) candidate))
            forwards = []).
        { apply pending_covers_filter_empty.
          intros candidate Hcandidate.
          eapply Permutation_in.
          - apply Permutation_sym. exact Horder.
          - exact Hcandidate. }
        cbn.
        destruct (node_eq receiver receiver) as [_ | Hbad]; [| contradiction].
        destruct (node_eq receiver initiator); [contradiction |].
        fold forwards.
        change (Permutation
          (List.filter
            (fun candidate => negb
              (@node_is_pending node node_eq
                (mkEchoProcess (Some sender) ordered_forwards false) candidate))
            forwards) []).
        rewrite Hempty. apply Permutation_refl.
      * unfold apply_echo_delivery. simpl.
        unfold update_proc.
        destruct (node_eq receiver n); [contradiction |].
        unfold alpha_acknowledged, alpha_phase, expected_replies,
          update_process.
        destruct (node_eq receiver n); [contradiction |].
        cbn.
        destruct (node_eq receiver n); [contradiction |].
        specialize (Hacks n).
        unfold alpha_acknowledged, alpha_phase, expected_replies in Hacks.
        exact Hacks.
    + change (Permutation
        (List.map alpha_message
          (remove_echo_message selected_id (message_store s) ++
            materialize_echo_outbound (next_message_id s) receiver
              (List.map (mkEchoOutbound EchoRequest) ordered_forwards)))
        (remove_pkt node_eq (mkPkt sender receiver Token) (es_msgs rq) ++
          send_to_all receiver forwards Token)).
      rewrite map_app, alpha_materialize_echo.
      apply Permutation_app.
      * exact (alpha_delivery_residual
          (mkEchoMessage selected_id EchoRequest sender receiver)
          s (es_msgs rq) Hids Hin Hstore).
      * now apply Permutation_map.
    + apply executable_delivery_messages_well_formed. exact Hids.
    + unfold executable_processes_well_formed.
      intros n Hnroot Hfinished.
      destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n. exists sender.
        unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_self. reflexivity.
      * unfold apply_echo_delivery in Hfinished. simpl in Hfinished.
        rewrite refinement_update_process_other in Hfinished by exact Hneq.
        destruct (Hroles_wf n Hnroot Hfinished) as [parent Hparent_old].
        exists parent.
        unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_other by exact Hneq.
        exact Hparent_old.
    + unfold executable_pending_well_formed.
      intro n.
      destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n.
        unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_self.
        unfold expected_replies.
        destruct (node_eq receiver initiator); [contradiction |].
        simpl. fold forwards.
        split.
        -- eapply Permutation_NoDup.
           ++ apply Permutation_sym. exact Horder.
           ++ now apply NoDup_filter.
        -- intros candidate Hcandidate.
           eapply Permutation_in; [exact Horder | exact Hcandidate].
      * unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_other by exact Hneq.
        apply Hpending_wf.
Qed.

(* ------------------------------------------------------------------ *)
(** ** First ECHO at a leaf participant *)

Lemma executable_first_echo_leaf_step_sound
    (initiator : node) (all_nodes : list node) (adj : node -> node -> bool)
    (s : @executable_echo_state node) selected_id sender receiver
    (rq : @echo_state node) :
  receiver <> initiator ->
  In (mkEchoMessage selected_id EchoRequest sender receiver) (message_store s) ->
  processes s receiver = initial_echo_process ->
  remove_echo_node node_eq sender (nbrs all_nodes adj receiver) = [] ->
  NoDup (nbrs all_nodes adj receiver) ->
  @ExecutableStateRefines node node_eq initiator all_nodes adj s rq ->
  exists rq',
    @echo_step node node_eq initiator all_nodes adj rq
      (ELDeliver (mkPkt sender receiver Token)) rq' /\
    @ExecutableStateRefines node node_eq initiator all_nodes adj
      (apply_echo_delivery node_eq s
        (mkEchoMessage selected_id EchoRequest sender receiver)
        (mkEchoProcess (Some sender) [] true)
        [mkEchoOutbound EchoReply sender]) rq'.
Proof.
  intros Hnotroot Hin Hinitial Hleaf Hneighbors Hrefines.
  destruct Hrefines as
    [Hparent Hphase Hpending Hacks Hstore Hids Hroles_wf Hpending_wf].
  assert (Hforwards :
    List.filter
      (fun candidate => if node_eq candidate sender then false else true)
      (nbrs all_nodes adj receiver) = []).
  { rewrite <- remove_node_eq_filter by exact Hneighbors. exact Hleaf. }
  assert (Hreceiver_idle : ps_phase (es_procs rq receiver) = Idle).
  { rewrite <- Hphase.
    unfold alpha_phase.
    destruct (node_eq receiver initiator); [contradiction |].
    rewrite Hinitial. reflexivity. }
  assert (Hin_rq : In (mkPkt sender receiver Token) (es_msgs rq)).
  { assert (Hin_alpha : In
        (alpha_message
          (mkEchoMessage selected_id EchoRequest sender receiver))
        (List.map alpha_message (message_store s))).
    { apply in_map. exact Hin. }
    eapply Permutation_in; [exact Hstore | exact Hin_alpha]. }
  set (rq' := mkEchoState
    (update_proc node_eq (es_procs rq) receiver
      (mkProc Active (Some sender) 0 []))
    (remove_pkt node_eq (mkPkt sender receiver Token) (es_msgs rq) ++
      [mkPkt receiver sender Echo])).
  exists rq'. split.
  - eapply step_deliver.
    + exact Hin_rq.
    + subst rq'.
      unfold handle_msg. simpl.
      rewrite Hreceiver_idle, Hforwards. reflexivity.
  - subst rq'. constructor.
    + intro n.
      destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n.
        unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_self.
        unfold update_proc.
        destruct (node_eq receiver receiver); [reflexivity | contradiction].
      * unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_other by exact Hneq.
        unfold update_proc.
        destruct (node_eq receiver n); [contradiction |].
        apply Hparent.
    + intro n.
      destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n.
        unfold apply_echo_delivery. simpl.
        unfold alpha_phase, update_process, update_proc.
        destruct (node_eq receiver receiver) as [_ | Hbad]; [| contradiction].
        destruct (node_eq receiver initiator); [contradiction |].
        cbn.
        destruct (node_eq receiver receiver); [reflexivity | contradiction].
      * unfold apply_echo_delivery. simpl.
        unfold update_proc.
        destruct (node_eq receiver n); [contradiction |].
        unfold alpha_phase, update_process.
        destruct (node_eq receiver n); [contradiction |].
        cbn.
        destruct (node_eq receiver n); [contradiction |].
        apply Hphase.
    + intro n.
      destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n.
        unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_self.
        unfold update_proc.
        destruct (node_eq receiver receiver); [reflexivity | contradiction].
      * unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_other by exact Hneq.
        unfold update_proc.
        destruct (node_eq receiver n); [contradiction |].
        apply Hpending.
    + intro n.
      destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n.
        unfold apply_echo_delivery. simpl.
        unfold update_proc.
        destruct (node_eq receiver receiver) as [_ | Hbad]; [| contradiction].
        unfold alpha_acknowledged, alpha_phase, expected_replies,
          update_process.
        destruct (node_eq receiver receiver) as [_ | Hbad]; [| contradiction].
        destruct (node_eq receiver initiator); [contradiction |].
        cbn.
        destruct (node_eq receiver receiver) as [_ | Hbad]; [| contradiction].
        destruct (node_eq receiver initiator); [contradiction |].
        cbn.
        destruct (node_eq receiver receiver) as [_ | Hbad]; [| contradiction].
        destruct (node_eq receiver initiator); [contradiction |].
        cbn.
        rewrite Hforwards. apply Permutation_refl.
      * unfold apply_echo_delivery. simpl.
        unfold update_proc.
        destruct (node_eq receiver n); [contradiction |].
        unfold alpha_acknowledged, alpha_phase, expected_replies,
          update_process.
        destruct (node_eq receiver n); [contradiction |].
        cbn.
        destruct (node_eq receiver n); [contradiction |].
        specialize (Hacks n).
        unfold alpha_acknowledged, alpha_phase, expected_replies in Hacks.
        exact Hacks.
    + change (Permutation
        (List.map alpha_message
          (remove_echo_message selected_id (message_store s) ++
            materialize_echo_outbound (next_message_id s) receiver
              [mkEchoOutbound EchoReply sender]))
        (remove_pkt node_eq (mkPkt sender receiver Token) (es_msgs rq) ++
          [mkPkt receiver sender Echo])).
      rewrite map_app, alpha_materialize_ack.
      apply Permutation_app.
      * exact (alpha_delivery_residual
          (mkEchoMessage selected_id EchoRequest sender receiver)
          s (es_msgs rq) Hids Hin Hstore).
      * apply Permutation_refl.
    + apply executable_delivery_messages_well_formed. exact Hids.
    + unfold executable_processes_well_formed.
      intros n Hnroot Hfinished.
      destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n. exists sender.
        unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_self. reflexivity.
      * unfold apply_echo_delivery in Hfinished. simpl in Hfinished.
        rewrite refinement_update_process_other in Hfinished by exact Hneq.
        destruct (Hroles_wf n Hnroot Hfinished) as [parent Hparent_old].
        exists parent.
        unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_other by exact Hneq.
        exact Hparent_old.
    + unfold executable_pending_well_formed.
      intro n.
      destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n.
        unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_self.
        split; [constructor | intros candidate Hcandidate; contradiction].
      * unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_other by exact Hneq.
        apply Hpending_wf.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Duplicate ECHO at an already reached participant *)

Lemma executable_repeated_echo_step_sound
    (initiator : node) (all_nodes : list node) (adj : node -> node -> bool)
    (s : @executable_echo_state node) selected_id sender receiver
    (rq : @echo_state node) :
  receiver <> initiator ->
  In (mkEchoMessage selected_id EchoRequest sender receiver) (message_store s) ->
  or (exists parent, process_parent (processes s receiver) = Some parent)
     (process_finished (processes s receiver) = true) ->
  @ExecutableStateRefines node node_eq initiator all_nodes adj s rq ->
  exists rq',
    @echo_step node node_eq initiator all_nodes adj rq
      (ELDeliver (mkPkt sender receiver Token)) rq' /\
    @ExecutableStateRefines node node_eq initiator all_nodes adj
      (apply_echo_delivery node_eq s
        (mkEchoMessage selected_id EchoRequest sender receiver)
        (processes s receiver)
        [mkEchoOutbound EchoReply sender]) rq'.
Proof.
  intros Hnotroot Hin Hreached Hrefines.
  destruct Hrefines as
    [Hparent Hphase Hpending Hacks Hstore Hids Hroles_wf Hpending_wf].
  assert (Hhas_parent :
    exists parent, process_parent (processes s receiver) = Some parent).
  { destruct Hreached as [Hparent_exists | Hfinished].
    - exact Hparent_exists.
    - exact (Hroles_wf receiver Hnotroot Hfinished). }
  assert (Hreceiver_active : ps_phase (es_procs rq receiver) = Active).
  { rewrite <- Hphase.
    unfold alpha_phase.
    destruct (node_eq receiver initiator); [contradiction |].
    destruct Hhas_parent as [parent Hparent_receiver].
    rewrite Hparent_receiver. reflexivity. }
  assert (Hin_rq : In (mkPkt sender receiver Token) (es_msgs rq)).
  { assert (Hin_alpha : In
        (alpha_message
          (mkEchoMessage selected_id EchoRequest sender receiver))
        (List.map alpha_message (message_store s))).
    { apply in_map. exact Hin. }
    eapply Permutation_in; [exact Hstore | exact Hin_alpha]. }
  set (rq' := mkEchoState
    (es_procs rq)
    (remove_pkt node_eq (mkPkt sender receiver Token) (es_msgs rq) ++
      [mkPkt receiver sender Echo])).
  exists rq'. split.
  - eapply step_deliver.
    + exact Hin_rq.
    + subst rq'.
      unfold handle_msg. simpl.
      now rewrite Hreceiver_active.
  - subst rq'. constructor.
    + intro n. rewrite delivery_same_role_roles. apply Hparent.
    + intro n. rewrite delivery_same_role_alpha_phase. apply Hphase.
    + intro n. rewrite delivery_same_role_roles. apply Hpending.
    + intro n.
      rewrite delivery_same_role_alpha_acknowledged.
      apply Hacks.
    + change (Permutation
        (List.map alpha_message
          (remove_echo_message selected_id (message_store s) ++
            materialize_echo_outbound (next_message_id s) receiver
              [mkEchoOutbound EchoReply sender]))
        (remove_pkt node_eq (mkPkt sender receiver Token) (es_msgs rq) ++
          [mkPkt receiver sender Echo])).
      rewrite map_app, alpha_materialize_ack.
      apply Permutation_app.
      * exact (alpha_delivery_residual
          (mkEchoMessage selected_id EchoRequest sender receiver)
          s (es_msgs rq) Hids Hin Hstore).
      * apply Permutation_refl.
    + apply executable_delivery_messages_well_formed. exact Hids.
    + unfold executable_processes_well_formed.
      intros n Hnroot Hfinished.
      rewrite delivery_same_role_roles in Hfinished.
      destruct (Hroles_wf n Hnroot Hfinished) as [parent Hparent_old].
      exists parent. now rewrite delivery_same_role_roles.
    + unfold executable_pending_well_formed.
      intro n. rewrite delivery_same_role_roles.
      apply Hpending_wf.
Qed.

(* ------------------------------------------------------------------ *)
(** ** ECHO returning to the active initiator *)

Lemma executable_initiator_echo_step_sound
    (initiator : node) (all_nodes : list node) (adj : node -> node -> bool)
    (s : @executable_echo_state node) selected_id sender
    (rq : @echo_state node) :
  started s = true ->
  process_finished (processes s initiator) = false ->
  In (mkEchoMessage selected_id EchoRequest sender initiator) (message_store s) ->
  @ExecutableStateRefines node node_eq initiator all_nodes adj s rq ->
  exists rq',
    @echo_step node node_eq initiator all_nodes adj rq
      (ELDeliver (mkPkt sender initiator Token)) rq' /\
    @ExecutableStateRefines node node_eq initiator all_nodes adj
      (apply_echo_delivery node_eq s
        (mkEchoMessage selected_id EchoRequest sender initiator)
        (processes s initiator)
        [mkEchoOutbound EchoReply sender]) rq'.
Proof.
  intros Hstarted Hnotfinished Hin Hrefines.
  destruct Hrefines as
    [Hparent Hphase Hpending Hacks Hstore Hids Hroles_wf Hpending_wf].
  assert (Hinitiator_active : ps_phase (es_procs rq initiator) = Active).
  { rewrite <- Hphase.
    unfold alpha_phase.
    destruct (node_eq initiator initiator) as [_ | Hbad]; [| contradiction].
    rewrite Hnotfinished, Hstarted. reflexivity. }
  assert (Hin_rq : In (mkPkt sender initiator Token) (es_msgs rq)).
  { assert (Hin_alpha : In
        (alpha_message
          (mkEchoMessage selected_id EchoRequest sender initiator))
        (List.map alpha_message (message_store s))).
    { apply in_map. exact Hin. }
    eapply Permutation_in; [exact Hstore | exact Hin_alpha]. }
  set (rq' := mkEchoState
    (es_procs rq)
    (remove_pkt node_eq (mkPkt sender initiator Token) (es_msgs rq) ++
      [mkPkt initiator sender Echo])).
  exists rq'. split.
  - eapply step_deliver.
    + exact Hin_rq.
    + subst rq'.
      unfold handle_msg. simpl.
      now rewrite Hinitiator_active.
  - subst rq'. constructor.
    + intro n. rewrite delivery_same_role_roles. apply Hparent.
    + intro n. rewrite delivery_same_role_alpha_phase. apply Hphase.
    + intro n. rewrite delivery_same_role_roles. apply Hpending.
    + intro n.
      rewrite delivery_same_role_alpha_acknowledged.
      apply Hacks.
    + change (Permutation
        (List.map alpha_message
          (remove_echo_message selected_id (message_store s) ++
            materialize_echo_outbound (next_message_id s) initiator
              [mkEchoOutbound EchoReply sender]))
        (remove_pkt node_eq (mkPkt sender initiator Token) (es_msgs rq) ++
          [mkPkt initiator sender Echo])).
      rewrite map_app, alpha_materialize_ack.
      apply Permutation_app.
      * exact (alpha_delivery_residual
          (mkEchoMessage selected_id EchoRequest sender initiator)
          s (es_msgs rq) Hids Hin Hstore).
      * apply Permutation_refl.
    + apply executable_delivery_messages_well_formed. exact Hids.
    + unfold executable_processes_well_formed.
      intros n Hnroot Hfinished.
      rewrite delivery_same_role_roles in Hfinished.
      destruct (Hroles_wf n Hnroot Hfinished) as [parent Hparent_old].
      exists parent. now rewrite delivery_same_role_roles.
    + unfold executable_pending_well_formed.
      intro n. rewrite delivery_same_role_roles.
      apply Hpending_wf.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Participant ACK with replies still pending *)

Lemma executable_participant_ack_more_step_sound
    (initiator : node) (all_nodes : list node) (adj : node -> node -> bool)
    (s : @executable_echo_state node) selected_id sender receiver parent
    (rq : @echo_state node) :
  receiver <> initiator ->
  In (mkEchoMessage selected_id EchoReply sender receiver) (message_store s) ->
  process_parent (processes s receiver) = Some parent ->
  In sender (process_pending (processes s receiver)) ->
  remove_echo_node node_eq sender (process_pending (processes s receiver)) <> [] ->
  process_finished (processes s receiver) = false ->
  NoDup (nbrs all_nodes adj receiver) ->
  @ExecutableStateRefines node node_eq initiator all_nodes adj s rq ->
  exists rq',
    @echo_step node node_eq initiator all_nodes adj rq
      (ELDeliver (mkPkt sender receiver Echo)) rq' /\
    @ExecutableStateRefines node node_eq initiator all_nodes adj
      (apply_echo_delivery node_eq s
        (mkEchoMessage selected_id EchoReply sender receiver)
        (mkEchoProcess (Some parent)
          (remove_echo_node node_eq sender (process_pending (processes s receiver)))
          false)
        []) rq'.
Proof.
  intros Hnotroot Hin Hpyparent Hsender Hmore Hnotfinished
    Hneighbors Hrefines.
  destruct Hrefines as
    [Hparent Hphase Hpending Hacks Hstore Hids Hroles_wf Hpending_wf].
  destruct (Hpending_wf receiver) as [Hpending_nodup Hpending_subset].
  assert (Hreceiver_active : ps_phase (es_procs rq receiver) = Active).
  { rewrite <- Hphase. unfold alpha_phase.
    destruct (node_eq receiver initiator); [contradiction |].
    now rewrite Hpyparent. }
  assert (Hexecutable_receiver_active :
    @alpha_phase node node_eq initiator s receiver = Active).
  { rewrite Hphase. exact Hreceiver_active. }
  assert (Hrocq_parent : ps_parent (es_procs rq receiver) = Some parent).
  { rewrite <- Hparent. exact Hpyparent. }
  pose proof (remove_node_length_in sender
    (process_pending (processes s receiver)) Hsender) as Hremove_length.
  assert (Hpending_not_one : ps_pending (es_procs rq receiver) <> 1).
  { intro Hone.
    rewrite <- Hpending in Hone.
    assert (Hremoved_zero :
      List.length
        (remove_echo_node node_eq sender (process_pending (processes s receiver))) = 0)
      by lia.
    apply Hmore. now apply length_zero_iff_nil. }
  assert (Hpending_eqb :
    Nat.eqb (ps_pending (es_procs rq receiver)) 1 = false).
  { now apply Nat.eqb_neq. }
  assert (Hin_rq : In (mkPkt sender receiver Echo) (es_msgs rq)).
  { assert (Hin_alpha : In
        (alpha_message
          (mkEchoMessage selected_id EchoReply sender receiver))
        (List.map alpha_message (message_store s))).
    { apply in_map. exact Hin. }
    eapply Permutation_in; [exact Hstore | exact Hin_alpha]. }
  set (rq' := mkEchoState
    (update_proc node_eq (es_procs rq) receiver
      (mkProc Active (Some parent)
        (Nat.pred (ps_pending (es_procs rq receiver)))
        (sender :: ps_children (es_procs rq receiver))))
    (remove_pkt node_eq (mkPkt sender receiver Echo) (es_msgs rq))).
  exists rq'. split.
  - eapply step_deliver.
    + exact Hin_rq.
    + subst rq'. unfold handle_msg. simpl.
      rewrite Hreceiver_active, Hrocq_parent, Hpending_eqb. reflexivity.
  - subst rq'. constructor.
    + intro n. destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n. unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_self. unfold update_proc.
        destruct (node_eq receiver receiver); [reflexivity | contradiction].
      * unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_other by exact Hneq.
        unfold update_proc. destruct (node_eq receiver n); [contradiction |].
        apply Hparent.
    + intro n. destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n. unfold apply_echo_delivery. simpl.
        unfold alpha_phase, update_process, update_proc.
        destruct (node_eq receiver receiver) as [_ | Hbad]; [| contradiction].
        destruct (node_eq receiver initiator); [contradiction |].
        cbn. destruct (node_eq receiver receiver); [reflexivity | contradiction].
      * rewrite delivery_other_alpha_phase by exact Hneq.
        cbn. unfold update_proc. destruct (node_eq receiver n); [contradiction |].
        apply Hphase.
    + intro n. destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n. unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_self. unfold update_proc.
        destruct (node_eq receiver receiver) as [_ | Hbad]; [| contradiction].
        rewrite <- Hpending, <- Hremove_length. reflexivity.
      * unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_other by exact Hneq.
        unfold update_proc. destruct (node_eq receiver n); [contradiction |].
        apply Hpending.
    + intro n. destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n.
        assert (Hexpected_nodup :
          NoDup (@expected_replies node node_eq initiator all_nodes adj receiver
            (processes s receiver))).
        { unfold expected_replies.
          destruct (node_eq receiver initiator); [contradiction |].
          rewrite Hpyparent. now apply NoDup_filter. }
        assert (Hdelta : Permutation
          (List.filter
            (fun candidate => negb
              (@node_is_pending node node_eq
                (mkEchoProcess (Some parent)
                  (remove_echo_node node_eq sender
                    (process_pending (processes s receiver))) false) candidate))
            (@expected_replies node node_eq initiator all_nodes adj receiver
              (processes s receiver)))
          (sender :: alpha_acknowledged node node_eq initiator
            all_nodes adj s receiver)).
        { unfold alpha_acknowledged.
          rewrite Hexecutable_receiver_active.
          eapply pending_complement_remove_proc;
            eauto. }
        unfold expected_replies in Hdelta.
        destruct (node_eq receiver initiator); [contradiction |].
        rewrite Hpyparent in Hdelta.
        eapply Permutation_trans.
        -- unfold apply_echo_delivery, alpha_acknowledged. simpl.
           unfold alpha_phase, update_process.
           destruct (node_eq receiver receiver) as [_ | Hbad]; [| contradiction].
           destruct (node_eq receiver initiator); [contradiction |].
           simpl. unfold expected_replies.
           destruct (node_eq receiver initiator); [contradiction |].
           cbn.
           destruct (node_eq receiver receiver) as [_ | Hbad]; [| contradiction].
           cbn. exact Hdelta.
        -- cbn. unfold update_proc.
           destruct (node_eq receiver receiver) as [_ | Hbad]; [| contradiction].
           apply perm_skip. apply Hacks.
      * rewrite delivery_other_alpha_acknowledged by exact Hneq.
        cbn. unfold update_proc. destruct (node_eq receiver n); [contradiction |].
        apply Hacks.
    + unfold apply_echo_delivery. simpl.
      rewrite app_nil_r.
      exact (alpha_delivery_residual
        (mkEchoMessage selected_id EchoReply sender receiver)
        s (es_msgs rq) Hids Hin Hstore).
    + apply executable_delivery_messages_well_formed. exact Hids.
    + unfold executable_processes_well_formed.
      intros n Hnroot Hfinished.
      destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n. unfold apply_echo_delivery in Hfinished. simpl in Hfinished.
        rewrite refinement_update_process_self in Hfinished. discriminate.
      * unfold apply_echo_delivery in Hfinished. simpl in Hfinished.
        rewrite refinement_update_process_other in Hfinished by exact Hneq.
        destruct (Hroles_wf n Hnroot Hfinished) as [old_parent Hold].
        exists old_parent. rewrite delivery_other_roles by exact Hneq. exact Hold.
    + unfold executable_pending_well_formed.
      intro n. destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n. unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_self. split.
        -- now apply remove_node_nodup.
        -- intros candidate Hcandidate.
           apply remove_node_in_iff in Hcandidate; [| exact Hpending_nodup].
           destruct Hcandidate as [Hcandidate _].
           specialize (Hpending_subset candidate Hcandidate).
           unfold expected_replies in Hpending_subset.
           destruct (node_eq receiver initiator); [contradiction |].
           rewrite Hpyparent in Hpending_subset.
           unfold expected_replies.
           destruct (node_eq receiver initiator); [contradiction |].
           exact Hpending_subset.
      * unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_other by exact Hneq.
        apply Hpending_wf.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Participant's final ACK *)

Lemma executable_participant_ack_final_step_sound
    (initiator : node) (all_nodes : list node) (adj : node -> node -> bool)
    (s : @executable_echo_state node) selected_id sender receiver parent
    (rq : @echo_state node) :
  receiver <> initiator ->
  In (mkEchoMessage selected_id EchoReply sender receiver) (message_store s) ->
  process_parent (processes s receiver) = Some parent ->
  In sender (process_pending (processes s receiver)) ->
  remove_echo_node node_eq sender (process_pending (processes s receiver)) = [] ->
  process_finished (processes s receiver) = false ->
  NoDup (nbrs all_nodes adj receiver) ->
  @ExecutableStateRefines node node_eq initiator all_nodes adj s rq ->
  exists rq',
    @echo_step node node_eq initiator all_nodes adj rq
      (ELDeliver (mkPkt sender receiver Echo)) rq' /\
    @ExecutableStateRefines node node_eq initiator all_nodes adj
      (apply_echo_delivery node_eq s
        (mkEchoMessage selected_id EchoReply sender receiver)
        (mkEchoProcess (Some parent) [] true)
        [mkEchoOutbound EchoReply parent]) rq'.
Proof.
  intros Hnotroot Hin Hpyparent Hsender Hfinal Hnotfinished
    Hneighbors Hrefines.
  destruct Hrefines as
    [Hparent Hphase Hpending Hacks Hstore Hids Hroles_wf Hpending_wf].
  destruct (Hpending_wf receiver) as [Hpending_nodup Hpending_subset].
  assert (Hreceiver_active : ps_phase (es_procs rq receiver) = Active).
  { rewrite <- Hphase. unfold alpha_phase.
    destruct (node_eq receiver initiator); [contradiction |].
    now rewrite Hpyparent. }
  assert (Hexecutable_receiver_active :
    @alpha_phase node node_eq initiator s receiver = Active).
  { rewrite Hphase. exact Hreceiver_active. }
  assert (Hrocq_parent : ps_parent (es_procs rq receiver) = Some parent).
  { rewrite <- Hparent. exact Hpyparent. }
  pose proof (remove_node_length_in sender
    (process_pending (processes s receiver)) Hsender) as Hremove_length.
  assert (Hpending_one : ps_pending (es_procs rq receiver) = 1).
  { rewrite <- Hpending, <- Hremove_length, Hfinal. reflexivity. }
  assert (Hin_rq : In (mkPkt sender receiver Echo) (es_msgs rq)).
  { assert (Hin_alpha : In
        (alpha_message
          (mkEchoMessage selected_id EchoReply sender receiver))
        (List.map alpha_message (message_store s))).
    { apply in_map. exact Hin. }
    eapply Permutation_in; [exact Hstore | exact Hin_alpha]. }
  set (rq' := mkEchoState
    (update_proc node_eq (es_procs rq) receiver
      (mkProc Active (Some parent) 0
        (sender :: ps_children (es_procs rq receiver))))
    (remove_pkt node_eq (mkPkt sender receiver Echo) (es_msgs rq) ++
      [mkPkt receiver parent Echo])).
  exists rq'. split.
  - eapply step_deliver.
    + exact Hin_rq.
    + subst rq'. unfold handle_msg. simpl.
      rewrite Hreceiver_active, Hpending_one, Hrocq_parent. reflexivity.
  - subst rq'. constructor.
    + intro n. destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n. unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_self. unfold update_proc.
        destruct (node_eq receiver receiver); [reflexivity | contradiction].
      * unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_other by exact Hneq.
        unfold update_proc. destruct (node_eq receiver n); [contradiction |].
        apply Hparent.
    + intro n. destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n. unfold apply_echo_delivery. simpl.
        unfold alpha_phase, update_process, update_proc.
        destruct (node_eq receiver receiver) as [_ | Hbad]; [| contradiction].
        destruct (node_eq receiver initiator); [contradiction |].
        cbn. destruct (node_eq receiver receiver); [reflexivity | contradiction].
      * rewrite delivery_other_alpha_phase by exact Hneq.
        cbn. unfold update_proc. destruct (node_eq receiver n); [contradiction |].
        apply Hphase.
    + intro n. destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n. unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_self. unfold update_proc.
        destruct (node_eq receiver receiver); [reflexivity | contradiction].
      * unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_other by exact Hneq.
        unfold update_proc. destruct (node_eq receiver n); [contradiction |].
        apply Hpending.
    + intro n. destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n.
        assert (Hexpected_nodup :
          NoDup (@expected_replies node node_eq initiator all_nodes adj receiver
            (processes s receiver))).
        { unfold expected_replies.
          destruct (node_eq receiver initiator); [contradiction |].
          rewrite Hpyparent. now apply NoDup_filter. }
        assert (Hdelta : Permutation
          (List.filter
            (fun candidate => negb
              (@node_is_pending node node_eq
                (mkEchoProcess (Some parent) [] true) candidate))
            (@expected_replies node node_eq initiator all_nodes adj receiver
              (processes s receiver)))
          (sender :: alpha_acknowledged node node_eq initiator
            all_nodes adj s receiver)).
        { rewrite <- Hfinal.
          unfold alpha_acknowledged.
          rewrite Hexecutable_receiver_active.
          eapply pending_complement_remove_proc; eauto. }
        unfold expected_replies in Hdelta.
        destruct (node_eq receiver initiator); [contradiction |].
        rewrite Hpyparent in Hdelta.
        eapply Permutation_trans.
        -- unfold apply_echo_delivery, alpha_acknowledged. simpl.
           unfold alpha_phase, update_process.
           destruct (node_eq receiver receiver) as [_ | Hbad]; [| contradiction].
           destruct (node_eq receiver initiator); [contradiction |].
           simpl. unfold expected_replies.
           destruct (node_eq receiver initiator); [contradiction |].
           cbn.
           destruct (node_eq receiver receiver) as [_ | Hbad]; [| contradiction].
           cbn. exact Hdelta.
        -- cbn. unfold update_proc.
           destruct (node_eq receiver receiver) as [_ | Hbad]; [| contradiction].
           apply perm_skip. apply Hacks.
      * rewrite delivery_other_alpha_acknowledged by exact Hneq.
        cbn. unfold update_proc. destruct (node_eq receiver n); [contradiction |].
        apply Hacks.
    + change (Permutation
        (List.map alpha_message
          (remove_echo_message selected_id (message_store s) ++
            materialize_echo_outbound (next_message_id s) receiver
              [mkEchoOutbound EchoReply parent]))
        (remove_pkt node_eq (mkPkt sender receiver Echo) (es_msgs rq) ++
          [mkPkt receiver parent Echo])).
      rewrite map_app, alpha_materialize_ack.
      apply Permutation_app.
      * exact (alpha_delivery_residual
          (mkEchoMessage selected_id EchoReply sender receiver)
          s (es_msgs rq) Hids Hin Hstore).
      * apply Permutation_refl.
    + apply executable_delivery_messages_well_formed. exact Hids.
    + unfold executable_processes_well_formed.
      intros n Hnroot Hfinished.
      destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n. exists parent. unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_self. reflexivity.
      * unfold apply_echo_delivery in Hfinished. simpl in Hfinished.
        rewrite refinement_update_process_other in Hfinished by exact Hneq.
        destruct (Hroles_wf n Hnroot Hfinished) as [old_parent Hold].
        exists old_parent. rewrite delivery_other_roles by exact Hneq. exact Hold.
    + unfold executable_pending_well_formed.
      intro n. destruct (node_eq receiver n) as [Heq | Hneq].
      * subst n. unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_self.
        split; [constructor | intros candidate Hcandidate; contradiction].
      * unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_other by exact Hneq.
        apply Hpending_wf.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Initiator ACK with replies still pending *)

Lemma executable_initiator_ack_more_step_sound
    (initiator : node) (all_nodes : list node) (adj : node -> node -> bool)
    (s : @executable_echo_state node) selected_id sender (rq : @echo_state node) :
  started s = true ->
  process_parent (processes s initiator) = None ->
  In (mkEchoMessage selected_id EchoReply sender initiator) (message_store s) ->
  In sender (process_pending (processes s initiator)) ->
  remove_echo_node node_eq sender (process_pending (processes s initiator)) <> [] ->
  process_finished (processes s initiator) = false ->
  NoDup (nbrs all_nodes adj initiator) ->
  @ExecutableStateRefines node node_eq initiator all_nodes adj s rq ->
  exists rq',
    @echo_step node node_eq initiator all_nodes adj rq
      (ELDeliver (mkPkt sender initiator Echo)) rq' /\
    @ExecutableStateRefines node node_eq initiator all_nodes adj
      (apply_echo_delivery node_eq s
        (mkEchoMessage selected_id EchoReply sender initiator)
        (mkEchoProcess None
          (remove_echo_node node_eq sender (process_pending (processes s initiator)))
          false)
        []) rq'.
Proof.
  intros Hstarted Hroot_parent Hin Hsender Hmore Hnotfinished
    Hneighbors Hrefines.
  destruct Hrefines as
    [Hparent Hphase Hpending Hacks Hstore Hids Hroles_wf Hpending_wf].
  destruct (Hpending_wf initiator) as [Hpending_nodup Hpending_subset].
  assert (Hroot_active : ps_phase (es_procs rq initiator) = Active).
  { rewrite <- Hphase. unfold alpha_phase.
    destruct (node_eq initiator initiator) as [_ | Hbad]; [| contradiction].
    now rewrite Hnotfinished, Hstarted. }
  assert (Hexecutable_root_active :
    @alpha_phase node node_eq initiator s initiator = Active).
  { rewrite Hphase. exact Hroot_active. }
  assert (Hrocq_parent : ps_parent (es_procs rq initiator) = None).
  { rewrite <- Hparent. exact Hroot_parent. }
  pose proof (remove_node_length_in sender
    (process_pending (processes s initiator)) Hsender) as Hremove_length.
  assert (Hpending_not_one : ps_pending (es_procs rq initiator) <> 1).
  { intro Hone. rewrite <- Hpending in Hone.
    assert (List.length
      (remove_echo_node node_eq sender (process_pending (processes s initiator))) = 0)
      by lia.
    apply Hmore. now apply length_zero_iff_nil. }
  assert (Hpending_eqb :
    Nat.eqb (ps_pending (es_procs rq initiator)) 1 = false).
  { now apply Nat.eqb_neq. }
  assert (Hin_rq : In (mkPkt sender initiator Echo) (es_msgs rq)).
  { assert (Hin_alpha : In
        (alpha_message (mkEchoMessage selected_id EchoReply sender initiator))
        (List.map alpha_message (message_store s))).
    { apply in_map. exact Hin. }
    eapply Permutation_in; [exact Hstore | exact Hin_alpha]. }
  set (rq' := mkEchoState
    (update_proc node_eq (es_procs rq) initiator
      (mkProc Active None
        (Nat.pred (ps_pending (es_procs rq initiator)))
        (sender :: ps_children (es_procs rq initiator))))
    (remove_pkt node_eq (mkPkt sender initiator Echo) (es_msgs rq))).
  exists rq'. split.
  - eapply step_deliver.
    + exact Hin_rq.
    + subst rq'. unfold handle_msg. simpl.
      rewrite Hroot_active, Hrocq_parent, Hpending_eqb. reflexivity.
  - subst rq'. constructor.
    + intro n. destruct (node_eq initiator n) as [Heq | Hneq].
      * subst n. unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_self. unfold update_proc.
        destruct (node_eq initiator initiator); [reflexivity | contradiction].
      * unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_other by exact Hneq.
        unfold update_proc. destruct (node_eq initiator n); [contradiction |].
        apply Hparent.
    + intro n. destruct (node_eq initiator n) as [Heq | Hneq].
      * subst n. unfold apply_echo_delivery. simpl.
        unfold alpha_phase, update_process, update_proc.
        destruct (node_eq initiator initiator) as [_ | Hbad]; [| contradiction].
        cbn. destruct (node_eq initiator initiator); [| contradiction].
        simpl. now rewrite Hstarted.
      * rewrite delivery_other_alpha_phase by exact Hneq.
        cbn. unfold update_proc. destruct (node_eq initiator n); [contradiction |].
        apply Hphase.
    + intro n. destruct (node_eq initiator n) as [Heq | Hneq].
      * subst n. unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_self. unfold update_proc.
        destruct (node_eq initiator initiator) as [_ | Hbad]; [| contradiction].
        rewrite <- Hpending, <- Hremove_length. reflexivity.
      * unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_other by exact Hneq.
        unfold update_proc. destruct (node_eq initiator n); [contradiction |].
        apply Hpending.
    + intro n. destruct (node_eq initiator n) as [Heq | Hneq].
      * subst n.
        assert (Hdelta : Permutation
          (List.filter
            (fun candidate => negb
              (@node_is_pending node node_eq
                (mkEchoProcess None
                  (remove_echo_node node_eq sender
                    (process_pending (processes s initiator))) false) candidate))
            (nbrs all_nodes adj initiator))
          (sender :: alpha_acknowledged node node_eq initiator
            all_nodes adj s initiator)).
        { unfold alpha_acknowledged.
          rewrite Hexecutable_root_active.
          unfold expected_replies.
          destruct (node_eq initiator initiator) as [_ | Hbad]; [| contradiction].
          eapply pending_complement_remove_proc.
          - exact Hneighbors.
          - exact Hpending_nodup.
          - exact Hsender.
          - intros candidate Hcandidate.
            specialize (Hpending_subset candidate Hcandidate).
            unfold expected_replies in Hpending_subset.
            destruct (node_eq initiator initiator); [exact Hpending_subset | contradiction]. }
        eapply Permutation_trans.
        -- unfold apply_echo_delivery, alpha_acknowledged. simpl.
           unfold alpha_phase, update_process.
           destruct (node_eq initiator initiator) as [_ | Hbad]; [| contradiction].
           cbn. destruct (node_eq initiator initiator) as [_ | Hbad];
             [| contradiction].
           simpl. rewrite Hstarted. simpl.
           unfold expected_replies.
           destruct (node_eq initiator initiator) as [_ | Hbad]; [| contradiction].
           unfold node_is_pending in Hdelta.
           exact Hdelta.
        -- cbn. unfold update_proc.
           destruct (node_eq initiator initiator) as [_ | Hbad]; [| contradiction].
           apply perm_skip. apply Hacks.
      * rewrite delivery_other_alpha_acknowledged by exact Hneq.
        cbn. unfold update_proc. destruct (node_eq initiator n); [contradiction |].
        apply Hacks.
    + unfold apply_echo_delivery. simpl. rewrite app_nil_r.
      exact (alpha_delivery_residual
        (mkEchoMessage selected_id EchoReply sender initiator)
        s (es_msgs rq) Hids Hin Hstore).
    + apply executable_delivery_messages_well_formed. exact Hids.
    + unfold executable_processes_well_formed.
      intros n Hnroot Hfinished.
      assert (Hneq : initiator <> n).
      { intro Heq. apply Hnroot. symmetry. exact Heq. }
      rewrite delivery_other_roles in Hfinished by exact Hneq.
      destruct (Hroles_wf n Hnroot Hfinished) as [old_parent Hold].
      exists old_parent. now rewrite delivery_other_roles by exact Hneq.
    + unfold executable_pending_well_formed.
      intro n. destruct (node_eq initiator n) as [Heq | Hneq].
      * subst n. unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_self. split.
        -- now apply remove_node_nodup.
        -- intros candidate Hcandidate.
           apply remove_node_in_iff in Hcandidate; [| exact Hpending_nodup].
           destruct Hcandidate as [Hcandidate _].
           specialize (Hpending_subset candidate Hcandidate).
           unfold expected_replies in Hpending_subset.
           destruct (node_eq initiator initiator); [| contradiction].
           unfold expected_replies.
           destruct (node_eq initiator initiator) as [_ | Hbad]; [| contradiction].
           exact Hpending_subset.
      * unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_other by exact Hneq.
        apply Hpending_wf.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Initiator's final ACK and decision *)

Lemma executable_initiator_ack_final_step_sound
    (initiator : node) (all_nodes : list node) (adj : node -> node -> bool)
    (s : @executable_echo_state node) selected_id sender (rq : @echo_state node) :
  started s = true ->
  process_parent (processes s initiator) = None ->
  In (mkEchoMessage selected_id EchoReply sender initiator) (message_store s) ->
  In sender (process_pending (processes s initiator)) ->
  remove_echo_node node_eq sender (process_pending (processes s initiator)) = [] ->
  process_finished (processes s initiator) = false ->
  NoDup (nbrs all_nodes adj initiator) ->
  @ExecutableStateRefines node node_eq initiator all_nodes adj s rq ->
  exists rq',
    @echo_step node node_eq initiator all_nodes adj rq
      (ELDeliver (mkPkt sender initiator Echo)) rq' /\
    @ExecutableStateRefines node node_eq initiator all_nodes adj
      (apply_echo_delivery node_eq s
        (mkEchoMessage selected_id EchoReply sender initiator)
        (mkEchoProcess None [] true) []) rq'.
Proof.
  intros Hstarted Hroot_parent Hin Hsender Hfinal Hnotfinished
    Hneighbors Hrefines.
  destruct Hrefines as
    [Hparent Hphase Hpending Hacks Hstore Hids Hroles_wf Hpending_wf].
  destruct (Hpending_wf initiator) as [Hpending_nodup Hpending_subset].
  assert (Hroot_active : ps_phase (es_procs rq initiator) = Active).
  { rewrite <- Hphase. unfold alpha_phase.
    destruct (node_eq initiator initiator) as [_ | Hbad]; [| contradiction].
    now rewrite Hnotfinished, Hstarted. }
  assert (Hexecutable_root_active :
    @alpha_phase node node_eq initiator s initiator = Active).
  { rewrite Hphase. exact Hroot_active. }
  assert (Hrocq_parent : ps_parent (es_procs rq initiator) = None).
  { rewrite <- Hparent. exact Hroot_parent. }
  pose proof (remove_node_length_in sender
    (process_pending (processes s initiator)) Hsender) as Hremove_length.
  assert (Hpending_one : ps_pending (es_procs rq initiator) = 1).
  { rewrite <- Hpending, <- Hremove_length, Hfinal. reflexivity. }
  assert (Hin_rq : In (mkPkt sender initiator Echo) (es_msgs rq)).
  { assert (Hin_alpha : In
        (alpha_message (mkEchoMessage selected_id EchoReply sender initiator))
        (List.map alpha_message (message_store s))).
    { apply in_map. exact Hin. }
    eapply Permutation_in; [exact Hstore | exact Hin_alpha]. }
  set (rq' := mkEchoState
    (update_proc node_eq (es_procs rq) initiator
      (mkProc Decided None 0
        (sender :: ps_children (es_procs rq initiator))))
    (remove_pkt node_eq (mkPkt sender initiator Echo) (es_msgs rq))).
  exists rq'. split.
  - eapply step_deliver.
    + exact Hin_rq.
    + subst rq'. unfold handle_msg. simpl.
      rewrite Hroot_active, Hpending_one, Hrocq_parent. reflexivity.
  - subst rq'. constructor.
    + intro n. destruct (node_eq initiator n) as [Heq | Hneq].
      * subst n. unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_self. unfold update_proc.
        destruct (node_eq initiator initiator); [reflexivity | contradiction].
      * unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_other by exact Hneq.
        unfold update_proc. destruct (node_eq initiator n); [contradiction |].
        apply Hparent.
    + intro n. destruct (node_eq initiator n) as [Heq | Hneq].
      * subst n. unfold apply_echo_delivery. simpl.
        unfold alpha_phase, update_process, update_proc.
        destruct (node_eq initiator initiator) as [_ | Hbad]; [| contradiction].
        cbn. destruct (node_eq initiator initiator); [reflexivity | contradiction].
      * rewrite delivery_other_alpha_phase by exact Hneq.
        cbn. unfold update_proc. destruct (node_eq initiator n); [contradiction |].
        apply Hphase.
    + intro n. destruct (node_eq initiator n) as [Heq | Hneq].
      * subst n. unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_self. unfold update_proc.
        destruct (node_eq initiator initiator); [reflexivity | contradiction].
      * unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_other by exact Hneq.
        unfold update_proc. destruct (node_eq initiator n); [contradiction |].
        apply Hpending.
    + intro n. destruct (node_eq initiator n) as [Heq | Hneq].
      * subst n.
        assert (Hdelta : Permutation
          (List.filter
            (fun candidate => negb
              (@node_is_pending node node_eq (mkEchoProcess None [] true) candidate))
            (nbrs all_nodes adj initiator))
          (sender :: alpha_acknowledged node node_eq initiator
            all_nodes adj s initiator)).
        { rewrite <- Hfinal.
          unfold alpha_acknowledged.
          rewrite Hexecutable_root_active.
          unfold expected_replies.
          destruct (node_eq initiator initiator) as [_ | Hbad]; [| contradiction].
          eapply pending_complement_remove_proc.
          - exact Hneighbors.
          - exact Hpending_nodup.
          - exact Hsender.
          - intros candidate Hcandidate.
            specialize (Hpending_subset candidate Hcandidate).
            unfold expected_replies in Hpending_subset.
            destruct (node_eq initiator initiator);
              [exact Hpending_subset | contradiction]. }
        eapply Permutation_trans.
        -- unfold apply_echo_delivery, alpha_acknowledged. simpl.
           unfold alpha_phase, update_process.
           destruct (node_eq initiator initiator) as [_ | Hbad]; [| contradiction].
           cbn. destruct (node_eq initiator initiator) as [_ | Hbad];
             [| contradiction].
           unfold expected_replies.
           destruct (node_eq initiator initiator) as [_ | Hbad]; [| contradiction].
           exact Hdelta.
        -- cbn. unfold update_proc.
           destruct (node_eq initiator initiator) as [_ | Hbad]; [| contradiction].
           apply perm_skip. apply Hacks.
      * rewrite delivery_other_alpha_acknowledged by exact Hneq.
        cbn. unfold update_proc. destruct (node_eq initiator n); [contradiction |].
        apply Hacks.
    + unfold apply_echo_delivery. simpl. rewrite app_nil_r.
      exact (alpha_delivery_residual
        (mkEchoMessage selected_id EchoReply sender initiator)
        s (es_msgs rq) Hids Hin Hstore).
    + apply executable_delivery_messages_well_formed. exact Hids.
    + unfold executable_processes_well_formed.
      intros n Hnroot Hfinished.
      assert (Hneq : initiator <> n).
      { intro Heq. apply Hnroot. symmetry. exact Heq. }
      rewrite delivery_other_roles in Hfinished by exact Hneq.
      destruct (Hroles_wf n Hnroot Hfinished) as [old_parent Hold].
      exists old_parent. now rewrite delivery_other_roles by exact Hneq.
    + unfold executable_pending_well_formed.
      intro n. destruct (node_eq initiator n) as [Heq | Hneq].
      * subst n. unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_self.
        split; [constructor | intros candidate Hcandidate; contradiction].
      * unfold apply_echo_delivery. simpl.
        rewrite refinement_update_process_other by exact Hneq.
        apply Hpending_wf.
Qed.

End EchoExecutableRefinement.
