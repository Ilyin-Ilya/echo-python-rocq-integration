(** * Decidable helpers for the canonical executable Echo program *)

From Stdlib Require Import List Bool Arith Sorting.Permutation.
Import ListNotations.
Require Import EchoExecutableTypes.

Definition echo_dec_and {P Q : Prop}
    (left : {P} + {~ P}) (right : {Q} + {~ Q}) :
    {P /\ Q} + {~ (P /\ Q)}.
Proof. destruct left, right; intuition. Defined.

Definition echo_dec_or {P Q : Prop}
    (left : {P} + {~ P}) (right : {Q} + {~ Q}) :
    {P \/ Q} + {~ (P \/ Q)}.
Proof. destruct left, right; intuition. Defined.

Definition echo_dec_not {P : Prop} (decision : {P} + {~ P}) :
    {~ P} + {~ ~ P}.
Proof. destruct decision; intuition. Defined.

Section NodeDecisions.

Variable node : Type.
Variable node_eq : forall (n m : node), {n = m} + {n <> m}.

Fixpoint configured_processes_initial_dec
    (nodes : list node)
    (roles : node -> @echo_process node) :
    {forall n, In n nodes -> roles n = initial_echo_process} +
    {~ forall n, In n nodes -> roles n = initial_echo_process}.
Proof.
  destruct nodes as [| item rest].
  - left. intros n Hin. contradiction.
  - destruct (echo_process_eq_dec node_eq
      (roles item) initial_echo_process) as [Hitem | Hitem].
    + destruct (configured_processes_initial_dec rest roles)
        as [Hrest | Hrest].
      * left. intros n [Heq | Hin].
        -- now subst n.
        -- now apply Hrest.
      * right. intro Hall. apply Hrest.
        intros n Hin. apply Hall. now right.
    + right. intro Hall. apply Hitem. apply Hall. now left.
Defined.

Definition echo_initial_on_dec
    (config : @echo_config node)
    (state : @executable_echo_state node) :
    {echo_initial_on config state} + {~ echo_initial_on config state}.
Proof.
  unfold echo_initial_on, configured_processes_initial.
  destruct (Bool.bool_dec (started state) false) as [Hstarted | Hstarted].
  - destruct (configured_processes_initial_dec
      (config_nodes config) (processes state)) as [Hroles | Hroles].
    + destruct (list_eq_dec (echo_message_eq_dec node_eq)
        (message_store state) []) as [Hstore | Hstore].
      * destruct (Nat.eq_dec (next_message_id state) 1) as [Hnext | Hnext].
        -- left. auto.
        -- right. intros [_ [_ [_ Heq]]]. contradiction.
      * right. intros [_ [_ [Heq _]]]. contradiction.
    + right. intros [_ [Hall _]]. contradiction.
  - right. intros [Heq _]. contradiction.
Defined.

(** Remove the first matching occurrence and retain the residual list. *)
Fixpoint remove_first_node
    (item : node) (items : list node) : option (list node) :=
  match items with
  | [] => None
  | candidate :: rest =>
      if node_eq item candidate then Some rest
      else
        match remove_first_node item rest with
        | None => None
        | Some residual => Some (candidate :: residual)
        end
  end.

Lemma remove_first_node_some_permutation item items residual :
  remove_first_node item items = Some residual ->
  Permutation items (item :: residual).
Proof.
  revert residual. induction items as [| candidate rest IH];
    intros residual Hremove; simpl in Hremove.
  - discriminate.
  - destruct (node_eq item candidate) as [Heq | Hneq].
    + inversion Hremove. subst candidate residual. apply Permutation_refl.
    + destruct (remove_first_node item rest) as [tail |] eqn:Htail;
        [| discriminate].
      inversion Hremove. subst residual.
      eapply Permutation_trans.
      * apply perm_skip. now apply IH.
      * apply perm_swap.
Qed.

Lemma remove_first_node_none_not_in item items :
  remove_first_node item items = None -> ~ In item items.
Proof.
  induction items as [| candidate rest IH]; intro Hremove; simpl in *.
  - tauto.
  - destruct (node_eq item candidate) as [Heq | Hneq].
    + discriminate.
    + destruct (remove_first_node item rest) eqn:Hrest;
        [discriminate |].
      intros [Heq | Hin].
      * apply Hneq. symmetry. exact Heq.
      * exact (IH eq_refl Hin).
Qed.

Fixpoint node_list_permutation_dec
    (left right : list node) :
    {Permutation left right} + {~ Permutation left right}.
Proof.
  destruct left as [| item rest].
  - destruct right as [| candidate tail].
    + left. constructor.
    + right. apply Permutation_nil_cons.
  - destruct (remove_first_node item right) as [residual |] eqn:Hremove.
    + destruct (node_list_permutation_dec rest residual) as [Hrest | Hrest].
      * left. eapply Permutation_trans.
        -- apply perm_skip. exact Hrest.
        -- symmetry. now apply remove_first_node_some_permutation.
      * right. intro Hpermutation. apply Hrest.
        apply Permutation_cons_inv with item.
        eapply Permutation_trans.
        -- exact Hpermutation.
        -- now apply remove_first_node_some_permutation.
    + right. intro Hpermutation.
      apply (remove_first_node_none_not_in item right Hremove).
      eapply Permutation_in.
      * exact Hpermutation.
      * now left.
Defined.

End NodeDecisions.

Definition echo_decision_to_bool {P : Prop}
    (decision : {P} + {~ P}) : bool :=
  if decision then true else false.

Lemma echo_decision_to_bool_true_iff {P : Prop}
    (decision : {P} + {~ P}) :
  echo_decision_to_bool decision = true <-> P.
Proof.
  unfold echo_decision_to_bool. destruct decision as [HP | Hnot].
  - simpl. split; intro; [exact HP | reflexivity].
  - simpl. split; intro H; [discriminate | contradiction].
Qed.

Arguments remove_first_node {node} node_eq _ _.
Arguments node_list_permutation_dec {node} node_eq _ _.
Arguments configured_processes_initial_dec {node} node_eq _ _.
Arguments echo_initial_on_dec {node} node_eq _ _.
