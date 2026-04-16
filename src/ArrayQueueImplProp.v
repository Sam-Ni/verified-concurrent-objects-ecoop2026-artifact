Require Import
  Arith
  List
  LibVar
  LibEnv
  LTS
  SyncLTS
  VeriTactics
  ArrayQueueImpl
.
Import ListNotations.

Section Properties.

Variable L : nat.

Lemma noB_preserves_AEnq31: forall (acts : list event) st st' pid,
  valid_execution_fragment (array_queue_impl L) st st' acts ->
  binds pid AEnq31 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  binds pid AEnq31 st'.(pc).
Proof.
  induction 1; simpl; intros.
  - subst. assumption.
  - destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply binds_push_neq; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
Qed.

Lemma noB_preserves_ADeq31: forall (acts : list event) st st' pid,
  valid_execution_fragment (array_queue_impl L) st st' acts ->
  binds pid ADeq31 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  binds pid ADeq31 st'.(pc).
Proof.
  induction 1; simpl; intros.
  - subst. assumption.
  - destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply binds_push_neq; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
Qed.

Lemma noB_preserves_AEnq2: forall (acts : list event) st st' pid,
  valid_execution_fragment (array_queue_impl L) st st' acts ->
  binds pid AEnq2 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  binds pid AEnq2 st'.(pc).
Proof.
  induction 1; simpl; intros.
  - subst. assumption.
  - destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply binds_push_neq; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
Qed.

Lemma noB_preserves_ADeq2: forall (acts : list event) st st' pid,
  valid_execution_fragment (array_queue_impl L) st st' acts ->
  binds pid ADeq2 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  binds pid ADeq2 st'.(pc).
Proof.
  induction 1; simpl; intros.
  - subst. assumption.
  - destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply binds_push_neq; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
Qed.

Lemma noB_preserves_AEnq11: forall (acts : list event) st st' pid,
  valid_execution_fragment (array_queue_impl L) st st' acts ->
  binds pid AEnq11 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  binds pid AEnq11 st'.(pc).
Proof.
  induction 1; simpl; intros.
  - subst. assumption.
  - destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply binds_push_neq; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
Qed.

Lemma noB_preserves_ADeq11: forall (acts : list event) st st' pid,
  valid_execution_fragment (array_queue_impl L) st st' acts ->
  binds pid ADeq11 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  binds pid ADeq11 st'.(pc).
Proof.
  induction 1; simpl; intros.
  - subst. assumption.
  - destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply binds_push_neq; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
Qed.

Lemma noB_preserves_ADeq14: forall (acts : list event) st st' pid,
  valid_execution_fragment (array_queue_impl L) st st' acts ->
  binds pid ADeq14 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  binds pid ADeq14 st'.(pc).
Proof.
  induction 1; simpl; intros.
  - subst. assumption.
  - destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply binds_push_neq; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
Qed.

Lemma noB_preserves_AEnq14: forall (acts : list event) st st' pid,
  valid_execution_fragment (array_queue_impl L) st st' acts ->
  binds pid AEnq14 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  binds pid AEnq14 st'.(pc).
Proof.
  induction 1; simpl; intros.
  - subst. assumption.
  - destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply binds_push_neq; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
Qed.

Lemma noB_preserves_AEnq28: forall (acts : list event) st st' pid,
  valid_execution_fragment (array_queue_impl L) st st' acts ->
  binds pid AEnq28 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  binds pid AEnq28 st'.(pc).
Proof.
  induction 1; simpl; intros.
  - subst. assumption.
  - destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply binds_push_neq; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
Qed.

Lemma noB_preserves_ADeq28: forall (acts : list event) st st' pid,
  valid_execution_fragment (array_queue_impl L) st st' acts ->
  binds pid ADeq28 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  binds pid ADeq28 st'.(pc).
Proof.
  induction 1; simpl; intros.
  - subst. assumption.
  - destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply binds_push_neq; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
Qed.

Lemma noB_preserves_AEnq5: forall (acts : list event) st st' pid,
  valid_execution_fragment (array_queue_impl L) st st' acts ->
  binds pid AEnq5 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  binds pid AEnq5 st'.(pc).
Proof.
  induction 1; simpl; intros.
  - subst. assumption.
  - destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply binds_push_neq; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
Qed.

Lemma noB_preserves_ADeq5: forall (acts : list event) st st' pid,
  valid_execution_fragment (array_queue_impl L) st st' acts ->
  binds pid ADeq5 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  binds pid ADeq5 st'.(pc).
Proof.
  induction 1; simpl; intros.
  - subst. assumption.
  - destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply binds_push_neq; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq. subst.
      apply IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
Qed.

Lemma noB_preserves_AEnq28': forall (acts : list event) st st' pid,
  valid_execution_fragment (array_queue_impl L) st st' acts ->
  binds pid AEnq28 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  st.(x) pid = st'.(x) pid.
Proof.
  induction 1; simpl; intros.
  - subst. reflexivity.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      unfold binds in H1;
      rewrite Hbinds in H1; discriminate.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      unfold binds in H1;
      rewrite Hbinds in H1; discriminate.
      inversion H; subst; simpl in *.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      rewrite Nat.eqb_refl in H2; auto.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      unfold binds in H1;
      rewrite Hbinds in H1; discriminate.
      inversion H; subst; simpl in *;
      apply binds_push_neq; auto.
      apply Nat.eqb_neq in n; rewrite n in H2; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
      rewrite Nat.eqb_refl in H2; auto.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto.
      inversion H; subst; simpl in *; auto;
      apply remove_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H2; auto.
Qed.

Lemma noB_preserves_AEnq28'': forall (acts : list event) st st' pid,
  valid_execution_fragment (array_queue_impl L) st st' acts ->
  binds pid AEnq28 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  st.(rear) pid = st'.(rear) pid.
Proof.
  induction 1; simpl; intros.
  - subst. reflexivity.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      unfold binds in H1;
      rewrite Hbinds in H1; discriminate.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      unfold binds in H1;
      rewrite Hbinds in H1; discriminate.
      inversion H; subst; simpl in *.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      rewrite Nat.eqb_refl in H2; auto.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      unfold binds in H1;
      rewrite Hbinds in H1; discriminate.
      inversion H; subst; simpl in *;
      apply binds_push_neq; auto.
      apply Nat.eqb_neq in n; rewrite n in H2; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
      rewrite Nat.eqb_refl in H2; auto.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto.
      inversion H; subst; simpl in *; auto;
      apply remove_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H2; auto.
Qed.

Lemma noB_preserves_AEnq28''': forall (acts : list event) st st' pid,
  valid_execution_fragment (array_queue_impl L) st st' acts ->
  binds pid AEnq28 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  st.(vp) pid = st'.(vp) pid.
Proof.
  induction 1; simpl; intros.
  - subst. reflexivity.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      unfold binds in H1;
      rewrite Hbinds in H1; discriminate.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto.
      rewrite Nat.eqb_refl.
      unfold binds in H1.
      apply notin_get_none in Hnotin_pc.
      rewrite Hnotin_pc in H1; discriminate.
      inversion H; subst; simpl in *.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      rewrite Nat.eqb_refl in H2; auto.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto.
      apply Nat.eqb_neq in n.
      rewrite n. reflexivity.
      inversion H; subst; simpl in *;
      apply binds_push_neq; auto.
      apply Nat.eqb_neq in n; rewrite n in H2; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
      rewrite Nat.eqb_refl in H2; auto.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto.
      inversion H; subst; simpl in *; auto;
      apply remove_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H2; auto.
Qed.

Lemma noB_preserves_AEnq28_combine: forall (acts : list event) st st' pid,
  valid_execution_fragment (array_queue_impl L) st st' acts ->
  binds pid AEnq28 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  st.(x) pid = st'.(x) pid /\
  st.(rear) pid = st'.(rear) pid /\
  st.(vp) pid = st'.(vp) pid.
Proof.
  intros.
  intuition.
  eapply noB_preserves_AEnq28'; eauto.
  eapply noB_preserves_AEnq28''; eauto.
  eapply noB_preserves_AEnq28'''; eauto.
Qed.

Lemma noB_preserves_ADeq28': forall (acts : list event) st st' pid,
  valid_execution_fragment (array_queue_impl L) st st' acts ->
  binds pid ADeq28 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  st.(x) pid = st'.(x) pid.
Proof.
  induction 1; simpl; intros.
  - subst. reflexivity.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      unfold binds in H1;
      rewrite Hbinds in H1; discriminate.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      unfold binds in H1;
      rewrite Hbinds in H1; discriminate.
      inversion H; subst; simpl in *.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      rewrite Nat.eqb_refl in H2; auto.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      unfold binds in H1;
      rewrite Hbinds in H1; discriminate.
      inversion H; subst; simpl in *;
      apply binds_push_neq; auto.
      apply Nat.eqb_neq in n; rewrite n in H2; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
      rewrite Nat.eqb_refl in H2; auto.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto.
      inversion H; subst; simpl in *; auto;
      apply remove_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H2; auto.
Qed.

Lemma noB_preserves_ADeq28'': forall (acts : list event) st st' pid,
  valid_execution_fragment (array_queue_impl L) st st' acts ->
  binds pid ADeq28 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  st.(front) pid = st'.(front) pid.
Proof.
  induction 1; simpl; intros.
  - subst. reflexivity.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      unfold binds in H1;
      rewrite Hbinds in H1; discriminate.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      unfold binds in H1;
      rewrite Hbinds in H1; discriminate.
      inversion H; subst; simpl in *.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      rewrite Nat.eqb_refl in H2; auto.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      unfold binds in H1;
      rewrite Hbinds in H1; discriminate.
      inversion H; subst; simpl in *;
      apply binds_push_neq; auto.
      apply Nat.eqb_neq in n; rewrite n in H2; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
      rewrite Nat.eqb_refl in H2; auto.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto.
      inversion H; subst; simpl in *; auto;
      apply remove_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H2; auto.
Qed.

Lemma noB_preserves_ADeq28_combine: forall (acts : list event) st st' pid,
  valid_execution_fragment (array_queue_impl L) st st' acts ->
  binds pid ADeq28 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  st.(x) pid = st'.(x) pid /\
  st.(front) pid = st'.(front) pid.
Proof.
  intros.
  intuition.
  eapply noB_preserves_ADeq28'; eauto.
  eapply noB_preserves_ADeq28''; eauto.
Qed.

Lemma noB_preserves_AEnq5'': forall (acts : list event) st st' pid,
  valid_execution_fragment (array_queue_impl L) st st' acts ->
  binds pid AEnq5 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  st.(rear) pid = st'.(rear) pid.
Proof.
  induction 1; simpl; intros.
  - subst. reflexivity.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      unfold binds in H1;
      rewrite Hbinds in H1; discriminate.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      unfold binds in H1;
      rewrite Hbinds in H1; discriminate.
      inversion H; subst; simpl in *.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      rewrite Nat.eqb_refl in H2; auto.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      unfold binds in H1;
      rewrite Hbinds in H1; discriminate.
      inversion H; subst; simpl in *;
      apply binds_push_neq; auto.
      apply Nat.eqb_neq in n; rewrite n in H2; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
      rewrite Nat.eqb_refl in H2; auto.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto.
      inversion H; subst; simpl in *; auto;
      apply remove_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H2; auto.
Qed.

Lemma noB_preserves_ADeq5'': forall (acts : list event) st st' pid,
  valid_execution_fragment (array_queue_impl L) st st' acts ->
  binds pid ADeq5 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  st.(front) pid = st'.(front) pid.
Proof.
  induction 1; simpl; intros.
  - subst. reflexivity.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      unfold binds in H1;
      rewrite Hbinds in H1; discriminate.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      unfold binds in H1;
      rewrite Hbinds in H1; discriminate.
      inversion H; subst; simpl in *.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      apply binds_in in H1.
      unfold "#" in Hnotin_pc.
      intuition.
      rewrite Nat.eqb_refl in H2; auto.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto;
      unfold binds in H1;
      rewrite Hbinds in H1; discriminate.
      inversion H; subst; simpl in *;
      apply binds_push_neq; auto.
      apply Nat.eqb_neq in n; rewrite n in H2; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
      inversion H; subst; simpl in *;
      eapply binds_same in H1; eauto;
      discriminate.
      rewrite Nat.eqb_refl in H2; auto.
    -- rewrite <-IHvalid_execution_fragment; auto.
      inversion H; subst; simpl in *; auto.
      inversion H; subst; simpl in *; auto;
      apply remove_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H2; auto.
Qed.

End Properties.