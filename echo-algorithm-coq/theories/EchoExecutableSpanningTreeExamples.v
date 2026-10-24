(** * Concrete audit of the canonical complete-run theorem *)

From Stdlib Require Import List Arith Bool Lia.
Import ListNotations.
Require Import EchoAlgorithm EchoCorrectness EchoExecutableTypes EchoRunner
  EchoRunnerExamples EchoExecutableSpanningTree.

Module TwoNodeRunnerConfig <: ECHO_CORRECTNESS_CONFIG.

Definition node := nat.
Definition node_eq := Nat.eq_dec.
Definition initiator := 0.
Definition all_nodes := [0; 1].
Definition adj := two_node_adj.

Lemma adj_sym :
  forall left right, adj left right = true -> adj right left = true.
Proof.
  intros left right Hedge.
  unfold adj, two_node_adj in *.
  destruct (Nat.eqb left 0) eqn:Hleft0;
    destruct (Nat.eqb left 1) eqn:Hleft1;
    destruct (Nat.eqb right 0) eqn:Hright0;
    destruct (Nat.eqb right 1) eqn:Hright1;
    cbn in *; try discriminate; reflexivity.
Qed.

Lemma adj_irrefl : forall owner, adj owner owner = false.
Proof.
  intro owner. unfold adj, two_node_adj.
  destruct (Nat.eqb owner 0) eqn:Hzero;
    destruct (Nat.eqb owner 1) eqn:Hone; cbn; try reflexivity.
  apply Nat.eqb_eq in Hzero. apply Nat.eqb_eq in Hone. lia.
Qed.

Lemma initiator_in_nodes : In initiator all_nodes.
Proof. now left. Qed.

Lemma nodup_nodes : NoDup all_nodes.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

End TwoNodeRunnerConfig.

Module TwoNodeRunnerCorrect :=
  MakeEchoExecutableSpanningTree TwoNodeRunnerConfig.

Definition two_node_wave_depth (owner : nat) : nat :=
  if Nat.eq_dec owner 0 then 0 else 1.

Lemma two_node_wave_depth_props :
  two_node_wave_depth 0 = 0 /\
  forall owner,
    In owner [0; 1] -> owner <> 0 ->
    exists parent,
      In parent [0; 1] /\
      two_node_adj owner parent = true /\
      two_node_wave_depth parent < two_node_wave_depth owner.
Proof.
  split.
  - unfold two_node_wave_depth.
    destruct (Nat.eq_dec 0 0); [reflexivity | contradiction].
  - intros owner Howner Hnotroot.
    simpl in Howner. destruct Howner as [Hequal | [Hequal | Hnone]].
    + exfalso. apply Hnotroot. symmetry. exact Hequal.
    + subst owner. exists 0. split.
      * now left.
      * split.
        -- reflexivity.
        -- unfold two_node_wave_depth.
           destruct (Nat.eq_dec 0 0); [| contradiction].
           destruct (Nat.eq_dec 1 0); [lia | lia].
    + contradiction.
Qed.

Example two_node_computed_complete_run_spans :
  exists final_state,
    run_schedule Nat.eq_dec two_node_config 3
      initial_executable_echo_state two_node_complete_schedule =
      EchoRunComplete final_state 3 /\
    forall owner,
      In owner [0; 1] ->
      TwoNodeRunnerCorrect.executable_reaches_initiator
        final_state owner.
Proof.
  destruct two_node_run_completes as [final_state Hrun].
  exists final_state. split; [exact Hrun |].
  eapply TwoNodeRunnerCorrect.complete_run_builds_spanning_tree.
  - exact two_node_wave_depth_props.
  - exact Hrun.
Qed.

Module ThreeNodeStarRunnerConfig <: ECHO_CORRECTNESS_CONFIG.

Definition node := nat.
Definition node_eq := Nat.eq_dec.
Definition initiator := 0.
Definition all_nodes := [0; 1; 2].
Definition adj := three_node_star_adj.

Lemma adj_sym :
  forall left right, adj left right = true -> adj right left = true.
Proof.
  intros left right Hedge.
  unfold adj, three_node_star_adj in *.
  destruct (Nat.eqb left 0);
    destruct (Nat.eqb left 1);
    destruct (Nat.eqb left 2);
    destruct (Nat.eqb right 0);
    destruct (Nat.eqb right 1);
    destruct (Nat.eqb right 2);
    cbn in *; try discriminate; reflexivity.
Qed.

Lemma adj_irrefl : forall owner, adj owner owner = false.
Proof.
  intro owner. unfold adj, three_node_star_adj.
  destruct (Nat.eq_dec owner 0) as [Hequal | Hdifferent].
  - subst owner. reflexivity.
  - apply Nat.eqb_neq in Hdifferent. rewrite Hdifferent. cbn.
    now rewrite Bool.andb_false_r.
Qed.

Lemma initiator_in_nodes : In initiator all_nodes.
Proof. now left. Qed.

Lemma nodup_nodes : NoDup all_nodes.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

End ThreeNodeStarRunnerConfig.

Module ThreeNodeStarRunnerCorrect :=
  MakeEchoExecutableSpanningTree ThreeNodeStarRunnerConfig.

Definition three_node_star_wave_depth (owner : nat) : nat :=
  if Nat.eq_dec owner 0 then 0 else 1.

Lemma three_node_star_wave_depth_props :
  three_node_star_wave_depth 0 = 0 /\
  forall owner,
    In owner [0; 1; 2] -> owner <> 0 ->
    exists parent,
      In parent [0; 1; 2] /\
      three_node_star_adj owner parent = true /\
      three_node_star_wave_depth parent <
        three_node_star_wave_depth owner.
Proof.
  split.
  - unfold three_node_star_wave_depth.
    destruct (Nat.eq_dec 0 0); [reflexivity | contradiction].
  - intros owner Howner Hnotroot.
    simpl in Howner.
    destruct Howner as [Hequal | [Hequal | [Hequal | Hnone]]].
    + exfalso. apply Hnotroot. symmetry. exact Hequal.
    + subst owner. exists 0. split.
      * now left.
      * split.
        -- reflexivity.
        -- unfold three_node_star_wave_depth.
           destruct (Nat.eq_dec 0 0); [| contradiction].
           destruct (Nat.eq_dec 1 0); lia.
    + subst owner. exists 0. split.
      * now left.
      * split.
        -- reflexivity.
        -- unfold three_node_star_wave_depth.
           destruct (Nat.eq_dec 0 0); [| contradiction].
           destruct (Nat.eq_dec 2 0); lia.
    + contradiction.
Qed.

Example star_left_first_complete_run_spans :
  exists final_state,
    run_schedule Nat.eq_dec three_node_star_config 5
      initial_executable_echo_state star_left_first_schedule =
      EchoRunComplete final_state 5 /\
    forall owner,
      In owner [0; 1; 2] ->
      ThreeNodeStarRunnerCorrect.executable_reaches_initiator
        final_state owner.
Proof.
  destruct three_node_star_left_first_completes as [final_state Hrun].
  exists final_state. split; [exact Hrun |].
  eapply ThreeNodeStarRunnerCorrect.complete_run_builds_spanning_tree.
  - exact three_node_star_wave_depth_props.
  - exact Hrun.
Qed.

Example star_right_first_complete_run_spans :
  exists final_state,
    run_schedule Nat.eq_dec three_node_star_config 5
      initial_executable_echo_state star_right_first_schedule =
      EchoRunComplete final_state 5 /\
    forall owner,
      In owner [0; 1; 2] ->
      ThreeNodeStarRunnerCorrect.executable_reaches_initiator
        final_state owner.
Proof.
  destruct three_node_star_right_first_completes as [final_state Hrun].
  exists final_state. split; [exact Hrun |].
  eapply ThreeNodeStarRunnerCorrect.complete_run_builds_spanning_tree.
  - exact three_node_star_wave_depth_props.
  - exact Hrun.
Qed.

Module SingletonRunnerConfig <: ECHO_CORRECTNESS_CONFIG.

Definition node := nat.
Definition node_eq := Nat.eq_dec.
Definition initiator := 0.
Definition all_nodes := [0].
Definition adj : nat -> nat -> bool := fun _ _ => false.

Lemma adj_sym :
  forall left right, adj left right = true -> adj right left = true.
Proof. intros left right Hedge. discriminate. Qed.

Lemma adj_irrefl : forall owner, adj owner owner = false.
Proof. reflexivity. Qed.

Lemma initiator_in_nodes : In initiator all_nodes.
Proof. now left. Qed.

Lemma nodup_nodes : NoDup all_nodes.
Proof. repeat constructor; simpl; intuition discriminate. Qed.

End SingletonRunnerConfig.

Module SingletonRunnerCorrect :=
  MakeEchoExecutableSpanningTree SingletonRunnerConfig.

Definition singleton_wave_depth (_ : nat) : nat := 0.

Lemma singleton_wave_depth_props :
  singleton_wave_depth 0 = 0 /\
  forall owner,
    In owner [0] -> owner <> 0 ->
    exists parent,
      In parent [0] /\
      (fun _ _ : nat => false) owner parent = true /\
      singleton_wave_depth parent < singleton_wave_depth owner.
Proof.
  split; [reflexivity |].
  intros owner Howner Hnotroot.
  simpl in Howner. destruct Howner as [Hequal | Hnone].
  - exfalso. apply Hnotroot. symmetry. exact Hequal.
  - contradiction.
Qed.

Example singleton_computed_complete_run_spans :
  exists final_state,
    run_schedule Nat.eq_dec singleton_config 1
      initial_executable_echo_state [EchoStart []] =
      EchoRunComplete final_state 1 /\
    forall owner,
      In owner [0] ->
      SingletonRunnerCorrect.executable_reaches_initiator
        final_state owner.
Proof.
  destruct singleton_run_completes as [final_state Hrun].
  exists final_state. split; [exact Hrun |].
  eapply SingletonRunnerCorrect.complete_run_builds_spanning_tree.
  - exact singleton_wave_depth_props.
  - exact Hrun.
Qed.
