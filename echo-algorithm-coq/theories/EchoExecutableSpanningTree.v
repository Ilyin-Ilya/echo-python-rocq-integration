(** * Canonical executable completion implies a spanning tree

    The exported statements mention only the canonical executable state,
    reachability, completion predicate, and parent pointers.  For a normal
    non-singleton completion, the proof composes the direct [EchoStep]
    simulation with the established abstract safety theorem.  The singleton
    case is proved directly from the configured connectivity certificate. *)

From Stdlib Require Import List Arith Arith.Wf_nat Init.Wf
  Wellfounded.Inverse_Image.
Import ListNotations.
Require Import LTS EchoAlgorithm EchoCorrectness EchoExecutableTypes
  EchoTransitionIR EchoExecutableReachability EchoExecutableCorrect
  EchoRunner EchoExecutableAbstraction EchoExecutableRefinement.

Module MakeEchoExecutableSpanningTree (C : ECHO_CORRECTNESS_CONFIG).

Module EC := MakeEchoCorrectness C.

Local Notation node := C.node.
Local Notation node_eq := C.node_eq.
Local Notation initiator := C.initiator.
Local Notation all_nodes := C.all_nodes.
Local Notation adj := C.adj.
Local Notation config :=
  (mkEchoConfig initiator all_nodes adj).

Definition executable_parent_path
    (state : @executable_echo_state node)
    (owner : node) (steps : nat) : option node :=
  let fix follow current remaining :=
    match remaining with
    | 0 => Some current
    | S rest =>
        match process_parent (processes state current) with
        | None => None
        | Some parent => follow parent rest
        end
    end
  in follow owner steps.

Definition executable_reaches_initiator
    (state : @executable_echo_state node) (owner : node) : Prop :=
  exists steps,
    executable_parent_path state owner steps = Some initiator.

Lemma executable_parent_paths_refine
    (state : @executable_echo_state node)
    (abstract_state : @echo_state node) :
  @ExecutableStateRefines node node_eq initiator all_nodes adj
    state abstract_state ->
  forall owner steps,
    executable_parent_path state owner steps =
    EC.parent_path abstract_state owner steps.
Proof.
  intros Hrefines owner steps.
  destruct Hrefines as [Hparent _ _ _ _ _ _ _].
  revert owner.
  induction steps as [| steps IH]; intro owner; cbn.
  - reflexivity.
  - unfold EC.proc_of. rewrite <- Hparent.
    destruct (process_parent (processes state owner)) as [parent |]; cbn.
    + apply IH.
    + reflexivity.
Qed.

Lemma initial_executable_echo_state_refines :
  @ExecutableStateRefines node node_eq initiator all_nodes adj
    initial_executable_echo_state
    (@alpha_state node node_eq initiator all_nodes adj
      initial_executable_echo_state).
Proof.
  apply alpha_executable_state_refines.
  - unfold executable_messages_well_formed. cbn. split.
    + constructor.
    + intros message Hin. contradiction.
  - unfold executable_processes_well_formed. cbn.
    intros owner Hnotroot Hfinished. discriminate.
  - unfold executable_pending_well_formed. cbn.
    intro owner. split.
    + constructor.
    + intros candidate Hin. contradiction.
Qed.

Lemma executable_neighbor_lists_nodup :
  forall owner, NoDup (nbrs all_nodes adj owner).
Proof.
  intro owner. unfold nbrs. apply NoDup_filter. exact C.nodup_nodes.
Qed.

(** Canonical reachability itself is enough to construct a related reachable
    abstract state.  No replay function or compatibility transition relation
    occurs in this induction. *)
Theorem executable_reachable_refines :
  forall state,
    @echo_reachable node node_eq config state ->
    exists abstract_state,
      reachable (echo_LTS node node_eq initiator all_nodes adj)
        abstract_state /\
      @ExecutableStateRefines node node_eq initiator all_nodes adj
        state abstract_state.
Proof.
  intros state Hreachable.
  induction Hreachable as
      [| before event after Hbefore IH Hstep].
  - exists (@alpha_state node node_eq initiator all_nodes adj
      initial_executable_echo_state).
    split.
    + apply reach_init. apply alpha_initial_executable_echo_state.
    + exact initial_executable_echo_state_refines.
  - destruct IH as [abstract_before [Habstract Hrefines]].
    assert (Hready :
        @executable_start_ready node initiator before event).
    { destruct event as
        [ordered_neighbors
        | message ordered_forwards
        | message
        | message
        | message
        | message parent
        | message parent
        | message
        | message]; try exact I.
      pose proof (@EchoStep_start_guards node node_eq config
        before after ordered_neighbors Hstep) as [Hinitial Horder].
      destruct Hinitial as [Hstarted [Hconfigured [Hstore Hnext]]].
      unfold executable_start_ready, concrete_start_ready.
      repeat split; auto.
      apply Hconfigured. exact C.initiator_in_nodes. }
    destruct (@echo_step_sound node node_eq initiator all_nodes adj
      executable_neighbor_lists_nodup before after event abstract_before
      Hready Hstep Hrefines)
      as [abstract_after [label [Habstract_step Hrefines_after]]].
    exists abstract_after. split.
    + eapply reach_step; eauto.
    + exact Hrefines_after.
Qed.

Theorem executable_finished_builds_spanning_tree
    (wave_depth : node -> nat)
    (wave_depth_props :
      wave_depth initiator = 0 /\
      forall owner,
        In owner all_nodes -> owner <> initiator ->
        exists parent,
          In parent all_nodes /\
          adj owner parent = true /\
          wave_depth parent < wave_depth owner) :
  forall state,
    @echo_reachable node node_eq config state ->
    process_finished (processes state initiator) = true ->
    forall owner,
      In owner all_nodes ->
      executable_reaches_initiator state owner.
Proof.
  intros state Hreachable Hfinished owner Howner.
  destruct (executable_reachable_refines state Hreachable)
    as [abstract_state [Habstract Hrefines]].
  assert (Hdecided : EC.initiator_decided abstract_state).
  { unfold EC.initiator_decided.
    destruct Hrefines as [_ Hphase _ _ _ _ _ _].
    rewrite <- Hphase. unfold alpha_phase.
    destruct (node_eq initiator initiator) as [_ | Hbad]; [| contradiction].
    now rewrite Hfinished. }
  destruct (EC.decided_reaches_initiator wave_depth wave_depth_props
    abstract_state Habstract Hdecided owner Howner) as [steps Hpath].
  exists steps.
  rewrite (executable_parent_paths_refine
    state abstract_state Hrefines owner steps).
  exact Hpath.
Qed.

(** If the connectivity certificate covers every configured node and the
    initiator has no neighbors, then the configured graph is a singleton. *)
Lemma empty_initiator_neighbors_only_node
    (wave_depth : node -> nat)
    (wave_depth_props :
      wave_depth initiator = 0 /\
      forall owner,
        In owner all_nodes -> owner <> initiator ->
        exists parent,
          In parent all_nodes /\
          adj owner parent = true /\
          wave_depth parent < wave_depth owner) :
  nbrs all_nodes adj initiator = [] ->
  forall owner, In owner all_nodes -> owner = initiator.
Proof.
  intros Hempty.
  apply (well_founded_ind
    (wf_inverse_image node nat lt wave_depth lt_wf)
    (fun owner => In owner all_nodes -> owner = initiator)).
  intros owner IH Howner.
  destruct (node_eq owner initiator) as [Hequal | Hdifferent].
  - exact Hequal.
  - destruct (proj2 wave_depth_props owner Howner Hdifferent)
      as [parent [Hparent [Hedge Hlower]]].
    specialize (IH parent Hlower Hparent). subst parent.
    assert (Hin : In owner (nbrs all_nodes adj initiator)).
    { unfold nbrs. apply filter_In. split.
      - exact Howner.
      - now apply C.adj_sym. }
    rewrite Hempty in Hin. contradiction.
Qed.

Theorem executable_complete_builds_spanning_tree
    (wave_depth : node -> nat)
    (wave_depth_props :
      wave_depth initiator = 0 /\
      forall owner,
        In owner all_nodes -> owner <> initiator ->
        exists parent,
          In parent all_nodes /\
          adj owner parent = true /\
          wave_depth parent < wave_depth owner) :
  forall state,
    @echo_reachable node node_eq config state ->
    @echo_complete node config state ->
    forall owner,
      In owner all_nodes ->
      executable_reaches_initiator state owner.
Proof.
  intros state Hreachable Hcomplete owner Howner.
  destruct Hcomplete as
    [Hstarted [Hpending [Hstore [Hfinished | Hsingleton]]]].
  - eapply executable_finished_builds_spanning_tree; eauto.
  - pose proof (empty_initiator_neighbors_only_node
      wave_depth wave_depth_props Hsingleton owner Howner) as Hequal.
    subst owner. exists 0. reflexivity.
Qed.

(** Main complete-run theorem.  The schedule and fuel disappear from the
    conclusion: any result classified as complete has a canonical parent path
    from every configured node to the initiator. *)
Theorem complete_run_builds_spanning_tree
    (wave_depth : node -> nat)
    (wave_depth_props :
      wave_depth initiator = 0 /\
      forall owner,
        In owner all_nodes -> owner <> initiator ->
        exists parent,
          In parent all_nodes /\
          adj owner parent = true /\
          wave_depth parent < wave_depth owner) :
  forall fuel schedule final_state steps,
    @run_schedule node node_eq config fuel
      initial_executable_echo_state schedule =
      EchoRunComplete final_state steps ->
    forall owner,
      In owner all_nodes ->
      executable_reaches_initiator final_state owner.
Proof.
  intros fuel schedule final_state steps Hrun owner Howner.
  destruct (@run_schedule_complete_reachable node node_eq config
    fuel initial_executable_echo_state final_state schedule steps
    (@EchoReachInitial node node_eq config) Hrun)
    as [Hreachable Hcomplete].
  eapply executable_complete_builds_spanning_tree; eauto.
Qed.

End MakeEchoExecutableSpanningTree.
