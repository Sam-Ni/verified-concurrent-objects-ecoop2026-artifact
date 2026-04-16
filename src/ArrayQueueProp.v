Require Import
  LibVar
  LibEnv
  List
  Arith
  LibEnv
  LTS
  SyncLTS
  Compose
  Tensor
  Invariants
  Counter
  CounterProp
  ComposedLTS
  ArrayQueue
  ArrayQueueImpl.
Import ListNotations.

Section Properties.

Variable L : nat.

Lemma sync_array_fr_step_preserves_notin_inv: forall s s' pid int pid',
  step (sync (array_front_rear L)) s pid int s' ->
  pid' # s.(LState).(L2State).(LState).(L2State).(LState).(requests) ->
  pid' # s'.(LState).(L2State).(LState).(L2State).(LState).(requests).
Proof.
  intros.
  inversion H; subst; simpl in *.
  inversion H1; subst; simpl in *.
  inversion H2; subst; simpl in *.
  inversion H3; subst; simpl in *.
  inversion H4; subst; simpl in *;
  inversion H5; subst; simpl in *;
  apply remove_preserves_notin; auto.
  auto. auto.
Qed.

Lemma sync_array_fr_step_preserves_notin_inv': forall s s' pid int pid',
  step (sync (array_front_rear L)) s pid int s' ->
  pid' # s.(LState).(L2State).(LState).(L1State).(LState).(requests) ->
  pid' # s'.(LState).(L2State).(LState).(L1State).(LState).(requests).
Proof.
  intros.
  inversion H; subst; simpl in *.
  inversion H1; subst; simpl in *.
  inversion H2; subst; simpl in *.
  inversion H3; subst; simpl in *;
  inversion H4; subst; simpl in *;
  inversion H5; subst; simpl in *;
  auto.
  apply remove_preserves_notin; auto.
  apply remove_preserves_notin; auto.
  auto.
Qed.

Lemma sync_array_fr_step_preserves_notin_inv'': forall s s' pid int pid',
  step (sync (array_front_rear L)) s pid int s' ->
  pid' # s.(LState).(L1State).(LState).(Array.requests L) ->
  pid' # s'.(LState).(L1State).(LState).(Array.requests L).
Proof.
  intros.
  inversion H; subst; simpl in *.
  inversion H1; subst; simpl in *.
  auto.
  inversion H2; subst; simpl in *.
  inversion H3; subst; simpl in *;
  apply remove_preserves_notin; auto.
Qed.

Lemma sync_array_fr_initial_preserves_notin_inv: forall s s' pid int pid',
  initial_state (sync (array_front_rear L)) s pid int s' ->
  pid <> pid' ->
  pid' # s.(LState).(L2State).(LState).(L2State).(LState).(requests) ->
  pid' # s'.(LState).(L2State).(LState).(L2State).(LState).(requests).
Proof.
  intros.
  inversion H; subst; simpl in *.
  inversion H2; subst; simpl in *.
  inversion H3; subst; simpl in *.
  inversion H4; subst; simpl in *.
  inversion H5; subst; simpl in *.
  inversion H6; subst; simpl in *;
  apply notin_union; auto; intuition;
  apply notin_neq; auto.
  auto. auto.
Qed.

Lemma sync_array_fr_initial_preserves_notin_inv': forall s s' pid int pid',
  initial_state (sync (array_front_rear L)) s pid int s' ->
  pid <> pid' ->
  pid' # s.(LState).(L2State).(LState).(L1State).(LState).(requests) ->
  pid' # s'.(LState).(L2State).(LState).(L1State).(LState).(requests).
Proof.
  intros.
  inversion H; subst; simpl in *.
  inversion H2; subst; simpl in *.
  inversion H3; subst; simpl in *.
  inversion H4; subst; simpl in *.
  inversion H5; subst; simpl in *.
  inversion H6; subst; simpl in *;
  auto.
  inversion H5; subst; simpl in *.
  inversion H6; subst; simpl in *;
  apply notin_union; auto; intuition;
  apply notin_neq; auto.
  auto.
Qed.

Lemma sync_array_fr_initial_preserves_notin_inv'': forall s s' pid int pid',
  initial_state (sync (array_front_rear L)) s pid int s' ->
  pid <> pid' ->
  pid' # s.(LState).(L1State).(LState).(Array.requests L) ->
  pid' # s'.(LState).(L1State).(LState).(Array.requests L).
Proof.
  intros.
  inversion H; subst; simpl in *.
  inversion H2; subst; simpl in *.
  auto.
  inversion H3; subst; simpl in *.
  inversion H4; subst; simpl in *;
  apply notin_union; auto; intuition;
  apply notin_neq; auto.
Qed.

Lemma sync_array_fr_final_preserves_notin_inv: forall s s' pid int pid',
  final_state (sync (array_front_rear L)) s pid int s' ->
  pid' # s.(LState).(L2State).(LState).(L2State).(LState).(requests) ->
  pid' # s'.(LState).(L2State).(LState).(L2State).(LState).(requests).
Proof.
  intros.
  inversion H; subst; simpl in *; auto.
  inversion H1; subst; simpl in *; auto.
  inversion H2; subst; simpl in *; auto.
  inversion H3; subst; simpl in *; auto.
  inversion H4; subst; simpl in *; auto.
  inversion H5; subst; simpl in *; auto.
Qed.

Lemma sync_array_fr_final_preserves_notin_inv': forall s s' pid int pid',
  final_state (sync (array_front_rear L)) s pid int s' ->
  pid' # s.(LState).(L2State).(LState).(L1State).(LState).(requests) ->
  pid' # s'.(LState).(L2State).(LState).(L1State).(LState).(requests).
Proof.
  intros.
  inversion H; subst; simpl in *; auto.
  inversion H1; subst; simpl in *; auto.
  inversion H2; subst; simpl in *; auto.
  inversion H3; subst; simpl in *; auto.
  inversion H4; subst; simpl in *; auto.
  inversion H5; subst; simpl in *; auto.
Qed.

Lemma sync_array_fr_final_preserves_notin_inv'': forall s s' pid int pid',
  final_state (sync (array_front_rear L)) s pid int s' ->
  pid' # s.(LState).(L1State).(LState).(Array.requests L) ->
  pid' # s'.(LState).(L1State).(LState).(Array.requests L).
Proof.
  intros.
  inversion H; subst; simpl in *; auto.
  inversion H1; subst; simpl in *; auto.
  inversion H2; subst; simpl in *; auto.
  inversion H3; subst; simpl in *; auto.
Qed.

Lemma internal_preserves_notin: forall acts pid st st',
  valid_execution_fragment (sync (array_front_rear L)) st st' acts ->
  gather_pid_external_events acts pid = [] ->
  pid # st.(LState).(L2State).(LState).(L2State).(LState).(requests) ->
  pid # st'.(LState).(L2State).(LState).(L2State).(LState).(requests).
Proof.
  induction 1; intros.
  - subst. assumption.
  - apply IHvalid_execution_fragment; auto.
    eapply sync_array_fr_step_preserves_notin_inv; eauto.
  - destruct qa.
  - destruct ra.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      eapply sync_array_fr_initial_preserves_notin_inv; eauto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      eapply sync_array_fr_final_preserves_notin_inv; eauto.
Qed.

Lemma internal_preserves_notin_L1: forall acts pid st st',
  valid_execution_fragment (sync (array_front_rear L)) st st' acts ->
  gather_pid_external_events acts pid = [] ->
  pid # st.(LState).(L2State).(LState).(L1State).(LState).(requests) ->
  pid # st'.(LState).(L2State).(LState).(L1State).(LState).(requests).
Proof.
  induction 1; intros.
  - subst. assumption.
  - apply IHvalid_execution_fragment; auto.
    eapply sync_array_fr_step_preserves_notin_inv'; eauto.
  - destruct qa.
  - destruct ra.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      eapply sync_array_fr_initial_preserves_notin_inv'; eauto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      eapply sync_array_fr_final_preserves_notin_inv'; eauto.
Qed.

Lemma internal_preserves_notin_L1': forall acts pid st st',
  valid_execution_fragment (sync (array_front_rear L)) st st' acts ->
  gather_pid_external_events acts pid = [] ->
  pid # st.(LState).(L1State).(LState).(Array.requests L) ->
  pid # st'.(LState).(L1State).(LState).(Array.requests L).
Proof.
  induction 1; intros.
  - subst. assumption.
  - apply IHvalid_execution_fragment; auto.
    eapply sync_array_fr_step_preserves_notin_inv''; eauto.
  - destruct qa.
  - destruct ra.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      eapply sync_array_fr_initial_preserves_notin_inv''; eauto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      eapply sync_array_fr_final_preserves_notin_inv''; eauto.
Qed.

Lemma internal_preserves_notin': forall acts pid st st',
  valid_execution_fragment (sync (array_front_rear L)) st st' acts ->
  gather_pid_external_events acts pid = [] ->
  pid # st.(LState).(L2State).(PidPos) ->
  pid # st'.(LState).(L2State).(PidPos).
Proof.
  induction 1; intros.
  - subst. assumption.
  - apply IHvalid_execution_fragment; auto.
    inversion H; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *.
    auto.
    auto.
  - destruct qa.
  - destruct ra.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      inversion H4; subst; simpl in *.
      apply notin_union. intuition.
      apply notin_neq; auto.
      auto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
        apply Nat.eqb_neq in Heq.
        inversion H; subst; simpl in *.
        inversion H3; subst; simpl in *.
        inversion H4; subst; simpl in *.
        apply remove_preserves_notin; auto.
        auto.
Qed.

Lemma internal_preserves_notin_L1'': forall acts pid st st',
  valid_execution_fragment (sync (array_front_rear L)) st st' acts ->
  gather_pid_external_events acts pid = [] ->
  pid # st.(LState).(L1State).(PidPos) ->
  pid # st'.(LState).(L1State).(PidPos).
Proof.
  induction 1; intros.
  - subst. assumption.
  - apply IHvalid_execution_fragment; auto.
    inversion H; subst; simpl in *.
    inversion H3; subst; simpl in *.
    auto.
    inversion H4; subst; simpl in *.
    auto.
  - destruct qa.
  - destruct ra.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      auto.
      inversion H4; subst; simpl in *.
      apply notin_union. intuition.
      apply notin_neq; auto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
        apply Nat.eqb_neq in Heq.
        inversion H; subst; simpl in *.
        inversion H3; subst; simpl in *.
        auto.
        inversion H4; subst; simpl in *.
        apply remove_preserves_notin; auto.
Qed.

Lemma internal_preserves_notin'': forall acts pid st st',
  valid_execution_fragment (sync (array_front_rear L)) st st' acts ->
  gather_pid_external_events acts pid = [] ->
  pid # st.(LState).(L2State).(LState).(L2State).(PidPos) ->
  pid # st'.(LState).(L2State).(LState).(L2State).(PidPos).
Proof.
  induction 1; intros.
  - subst. assumption.
  - apply IHvalid_execution_fragment; auto.
    inversion H; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *.
    inversion H6; subst; simpl in *.
    auto.
    auto.
    auto.
  - destruct qa.
  - destruct ra.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      inversion H4; subst; simpl in *.
      inversion H5; subst; simpl in *.
      inversion H6; subst; simpl in *.
      apply notin_union. intuition.
      apply notin_neq; auto.
      auto.
      auto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
        apply Nat.eqb_neq in Heq.
        inversion H; subst; simpl in *.
        inversion H3; subst; simpl in *.
        inversion H4; subst; simpl in *.
        inversion H5; subst; simpl in *.
        inversion H6; subst; simpl in *.
        apply remove_preserves_notin; auto.
        auto.
        auto.
Qed.

Lemma internal_preserves_notin''': forall acts pid st st',
  valid_execution_fragment (sync (array_front_rear L)) st st' acts ->
  gather_pid_external_events acts pid = [] ->
  pid # st.(LState).(L2State).(LState).(L1State).(PidPos) ->
  pid # st'.(LState).(L2State).(LState).(L1State).(PidPos).
Proof.
  induction 1; intros.
  - subst. assumption.
  - apply IHvalid_execution_fragment; auto.
    inversion H; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *;
    auto.
    inversion H6; subst; simpl in *;
    auto.
    auto.
  - destruct qa.
  - destruct ra.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      inversion H4; subst; simpl in *.
      inversion H5; subst; simpl in *.
      auto.
      inversion H6; subst; simpl in *.
      apply notin_union. intuition.
      apply notin_neq; auto.
      auto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
        apply Nat.eqb_neq in Heq.
        inversion H; subst; simpl in *.
        inversion H3; subst; simpl in *.
        inversion H4; subst; simpl in *.
        inversion H5; subst; simpl in *.
        auto.
        inversion H6; subst; simpl in *.
        apply remove_preserves_notin; auto.
        auto.
Qed.

Lemma sync_array_fr_step_preserves_binds_inv: forall s s' pid int q pid',
  step (sync (array_front_rear L)) s pid int s' ->
  pid <> pid' ->
  binds pid' q s.(LState).(L2State).(LState).(L2State).(LState).(requests) ->
  binds pid' q s'.(LState).(L2State).(LState).(L2State).(LState).(requests).
Proof.
  intros.
  inversion H; subst; simpl in *; auto.
  inversion H2; subst; simpl in *; auto.
  inversion H3; subst; simpl in *; auto.
  inversion H4; subst; simpl in *; auto.
  inversion H5; subst; simpl in *; auto.
  inversion H6; subst; simpl in *; auto.
  apply remove_neq_preserves_binds; auto.
  apply remove_neq_preserves_binds; auto.
Qed.

Lemma sync_array_fr_step_preserves_binds_inv': forall s s' pid int q pid',
  step (sync (array_front_rear L)) s pid int s' ->
  pid <> pid' ->
  binds pid' q s.(LState).(L2State).(LState).(L1State).(LState).(requests) ->
  binds pid' q s'.(LState).(L2State).(LState).(L1State).(LState).(requests).
Proof.
  intros.
  inversion H; subst; simpl in *; auto.
  inversion H2; subst; simpl in *; auto.
  inversion H3; subst; simpl in *; auto.
  inversion H4; subst; simpl in *; auto.
  inversion H5; subst; simpl in *; auto.
  inversion H6; subst; simpl in *; auto.
  apply remove_neq_preserves_binds; auto.
  apply remove_neq_preserves_binds; auto.
Qed.

Lemma sync_array_fr_step_preserves_binds_inv'': forall s s' pid int q pid',
  step (sync (array_front_rear L)) s pid int s' ->
  pid <> pid' ->
  binds pid' q s.(LState).(L1State).(LState).(Array.requests L) ->
  binds pid' q s'.(LState).(L1State).(LState).(Array.requests L).
Proof.
  intros.
  inversion H; subst; simpl in *; auto.
  inversion H2; subst; simpl in *; auto.
  inversion H3; subst; simpl in *; auto.
  inversion H4; subst; simpl in *; auto.
  apply remove_neq_preserves_binds; auto.
  apply remove_neq_preserves_binds; auto.
Qed.

Lemma sync_array_fr_initial_preserves_binds_inv: forall s s' pid int q pid',
  initial_state (sync (array_front_rear L)) s pid int s' ->
  binds pid' q s.(LState).(L2State).(LState).(L2State).(LState).(requests) ->
  binds pid' q s'.(LState).(L2State).(LState).(L2State).(LState).(requests).
Proof.
  intros.
  inversion H; subst; simpl in *.
  inversion H1; subst; simpl in *; auto.
  inversion H2; subst; simpl in *; auto.
  inversion H3; subst; simpl in *; auto.
  inversion H4; subst; simpl in *; auto.
  inversion H5; subst; simpl in *; auto.
  unfold binds. simpl.
  destruct (pid' =? pid)eqn:Heq.
  apply Nat.eqb_eq in Heq.
  subst. apply binds_in in H0.
  unfold "#" in Hnotin_inv.
  intuition.
  assumption.
  unfold binds. simpl.
  destruct (pid' =? pid)eqn:Heq.
  apply Nat.eqb_eq in Heq.
  subst. apply binds_in in H0.
  unfold "#" in Hnotin_inv.
  intuition.
  assumption.
Qed.

Lemma sync_array_fr_initial_preserves_binds_inv': forall s s' pid int q pid',
  initial_state (sync (array_front_rear L)) s pid int s' ->
  binds pid' q s.(LState).(L2State).(LState).(L1State).(LState).(requests) ->
  binds pid' q s'.(LState).(L2State).(LState).(L1State).(LState).(requests).
Proof.
  intros.
  inversion H; subst; simpl in *.
  inversion H1; subst; simpl in *; auto.
  inversion H2; subst; simpl in *; auto.
  inversion H3; subst; simpl in *; auto.
  inversion H4; subst; simpl in *; auto.
  inversion H5; subst; simpl in *; auto.
  unfold binds. simpl.
  destruct (pid' =? pid)eqn:Heq.
  apply Nat.eqb_eq in Heq.
  subst. apply binds_in in H0.
  unfold "#" in Hnotin_inv.
  intuition.
  assumption.
  unfold binds. simpl.
  destruct (pid' =? pid)eqn:Heq.
  apply Nat.eqb_eq in Heq.
  subst. apply binds_in in H0.
  unfold "#" in Hnotin_inv.
  intuition.
  assumption.
Qed.

Lemma sync_array_fr_initial_preserves_binds_inv'': forall s s' pid int q pid',
  initial_state (sync (array_front_rear L)) s pid int s' ->
  binds pid' q s.(LState).(L1State).(LState).(Array.requests L) ->
  binds pid' q s'.(LState).(L1State).(LState).(Array.requests L).
Proof.
  intros.
  inversion H; subst; simpl in *.
  inversion H1; subst; simpl in *; auto.
  inversion H2; subst; simpl in *; auto.
  inversion H3; subst; simpl in *; auto.
  unfold binds. simpl.
  destruct (pid' =? pid)eqn:Heq.
  apply Nat.eqb_eq in Heq.
  subst. apply binds_in in H0.
  unfold "#" in Hnotin_inv.
  intuition.
  assumption.
  unfold binds. simpl.
  destruct (pid' =? pid)eqn:Heq.
  apply Nat.eqb_eq in Heq.
  subst. apply binds_in in H0.
  unfold "#" in Hnotin_inv.
  intuition.
  assumption.
Qed.

Lemma internal_preserves_request: forall acts pid st st' qb qb',
  valid_execution_fragment (sync (array_front_rear L)) st st' acts ->
  gather_pid_external_events acts pid = [] ->
  binds pid qb st.(LState).(L2State).(LState).(L2State).(LState).(requests) ->
  binds pid qb' st'.(LState).(L2State).(LState).(L2State).(LState).(requests) ->
  qb = qb'.
Proof.
  induction 1; intros.
  - subst. eapply binds_same; eauto.
  - eapply IHvalid_execution_fragment; eauto.
    clear IHvalid_execution_fragment.
    destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      inversion H5; subst; simpl in *.
      inversion H6; subst; simpl in *.
      inversion H7; subst; simpl in *.
      inversion H8; subst; simpl in *.
      assert (pid0 # st'.(LState).(L2State).(LState).(L2State).(LState).(requests)).
      eapply internal_preserves_notin; eauto.
      simpl.
      apply ok_remove_notin; auto.
      apply binds_in in H3.
      unfold "#" in H9.
      intuition.
      assert (pid0 # st'.(LState).(L2State).(LState).(L2State).(LState).(requests)).
      eapply internal_preserves_notin; eauto.
      simpl.
      apply ok_remove_notin; auto.
      apply binds_in in H3.
      unfold "#" in H9.
      intuition.
      auto.
      auto.
    -- apply Nat.eqb_neq in Heq.
      eapply sync_array_fr_step_preserves_binds_inv; eauto.
  - destruct qa.
  - destruct ra.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      eapply sync_array_fr_initial_preserves_binds_inv; eauto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      inversion H; subst; intuition.
      inversion H4; subst; simpl in *.
      inversion H6; subst; simpl in *.
      inversion H7; subst; simpl in *.
      inversion H8; subst; simpl in *.
      inversion H9; subst; simpl in *;
      intuition.
      auto.
      auto.
Qed.

Lemma internal_preserves_request': forall acts pid st st' qb qb',
  valid_execution_fragment (sync (array_front_rear L)) st st' acts ->
  gather_pid_external_events acts pid = [] ->
  binds pid qb st.(LState).(L2State).(LState).(L1State).(LState).(requests) ->
  binds pid qb' st'.(LState).(L2State).(LState).(L1State).(LState).(requests) ->
  qb = qb'.
Proof.
  induction 1; intros.
  - subst. eapply binds_same; eauto.
  - eapply IHvalid_execution_fragment; eauto.
    clear IHvalid_execution_fragment.
    destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      inversion H5; subst; simpl in *.
      inversion H6; subst; simpl in *.
      auto.
      inversion H7; subst; simpl in *.
      inversion H8; subst; simpl in *.
      assert (pid0 # st'.(LState).(L2State).(LState).(L1State).(LState).(requests)).
      eapply internal_preserves_notin_L1; eauto.
      simpl.
      apply ok_remove_notin; auto.
      apply binds_in in H3.
      unfold "#" in H9.
      intuition.
      assert (pid0 # st'.(LState).(L2State).(LState).(L1State).(LState).(requests)).
      eapply internal_preserves_notin_L1; eauto.
      simpl.
      apply ok_remove_notin; auto.
      apply binds_in in H3.
      unfold "#" in H9.
      intuition.
      auto.
    -- apply Nat.eqb_neq in Heq.
      eapply sync_array_fr_step_preserves_binds_inv'; eauto.
  - destruct qa.
  - destruct ra.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      eapply sync_array_fr_initial_preserves_binds_inv'; eauto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      inversion H; subst; intuition.
      inversion H4; subst; simpl in *.
      inversion H6; subst; simpl in *.
      inversion H7; subst; simpl in *.
      inversion H8; subst; simpl in *.
      inversion H9; subst; simpl in *;
      intuition.
      inversion H8; subst; simpl in *.
      inversion H9; subst; simpl in *;
      auto.
      auto.
Qed.

Lemma internal_preserves_request'': forall acts pid st st' qb qb',
  valid_execution_fragment (sync (array_front_rear L)) st st' acts ->
  gather_pid_external_events acts pid = [] ->
  binds pid qb st.(LState).(L1State).(LState).(Array.requests L) ->
  binds pid qb' st'.(LState).(L1State).(LState).(Array.requests L) ->
  qb = qb'.
Proof.
  induction 1; intros.
  - subst. eapply binds_same; eauto.
  - eapply IHvalid_execution_fragment; eauto.
    clear IHvalid_execution_fragment.
    destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      auto.
      inversion H5; subst; simpl in *.
      inversion H6; subst; simpl in *.
      assert (pid0 # st'.(LState).(L1State).(LState).(Array.requests L)).
      eapply internal_preserves_notin_L1'; eauto.
      simpl.
      apply ok_remove_notin; auto.
      apply binds_in in H3.
      unfold "#" in H7.
      intuition.
      assert (pid0 # st'.(LState).(L1State).(LState).(Array.requests L)).
      eapply internal_preserves_notin_L1'; eauto.
      simpl.
      apply ok_remove_notin; auto.
      apply binds_in in H3.
      unfold "#" in H7.
      intuition.
    -- apply Nat.eqb_neq in Heq.
      eapply sync_array_fr_step_preserves_binds_inv''; eauto.
  - destruct qa.
  - destruct ra.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      eapply sync_array_fr_initial_preserves_binds_inv''; eauto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      inversion H; subst; intuition.
      simpl.
      inversion H4; subst; simpl in *.
      auto.
      inversion H6; subst; simpl in *.
      inversion H7; subst; simpl in *;
      auto.
Qed.

End Properties.

Section test.

Context {liA liB : language_interface}.
Variable L : lts liA liB.

End test.

Section test.

Context {liA liB liC : language_interface }.

Variable L : composed_lts.composed_lts liA liB liC.

End test.

Section SyncCounterProp.

Definition sync_counter_guard (s : state (sync counter)) :=
  forall pid,
  pid # s.(PidPos) ->
  pid # s.(LState).(Counter.requests).

Definition sync_counter_wf (s : state (sync counter)) :=
  (sync_counter_guard s /\ counter_exclusive_wf s.(LState)).

Lemma sync_counter_wf_inv:
  invariant_ind (sync counter)
    sync_counter_wf.
Proof.
  unfold sync_counter_wf.
  apply invariant_ind'_imply_invariant_ind_land.
  unfold invariant_ind'. intuition.
  - apply sync_preserves_inv.
    apply counter_exclusive_wf_inv.
  - unfold sync_counter_guard. intros.
    simpl in *. unfold sync_new_state in H.
    intuition.
    inversion H1; subst. rewrite H3.
    unfold new_counter. simpl.
    apply notin_empty.
  - unfold sync_counter_guard in *. intros.
    inversion H1; subst.
    simpl in *.
    inversion H3; subst; simpl in *;
    apply H in H2;
    apply remove_preserves_notin; auto.
  - unfold sync_counter_guard in *. intros.
    inversion H1; subst.
    simpl in *.
    inversion H3; subst; simpl in *;
    apply notin_union in H2;
    apply notin_union; intuition.
  - destruct act.
  - destruct act.
  - unfold sync_counter_guard in *. intros.
    inversion H1; subst.
    simpl in *.
    inversion H3; subst; simpl in *.
    -- destruct (eq_nat_dec pid pid0).
      --- subst.
        unfold counter_exclusive_wf in H0.
        simpl in *.
        apply binds_in in Hbinds0.
        apply H0; auto.
      --- apply remove_neq_preserves_notin in H2; auto.
    -- destruct (eq_nat_dec pid pid0).
      --- subst.
        unfold counter_exclusive_wf in H0.
        simpl in *.
        apply binds_in in Hbinds0.
        apply H0; auto.
      --- apply remove_neq_preserves_notin in H2; auto.
Qed.

End SyncCounterProp.

Section test.

Context {liA liB : language_interface}.
Variable L1 : lts li_null liA.
Variable L2 : lts li_null liB.

Lemma tensor_preserves_L1_inv: forall inv,
  invariant_ind L1 inv ->
  invariant_ind (tensor L1 L2)
    (fun s => inv s.(Tensor.L1State).(LState)).
Proof.
  intros. unfold invariant_ind in *.
  intuition.
  - inversion H4; subst.
    inversion H6; subst.
    apply H0; auto.
  - inversion H6; subst; simpl in *.
    auto.
    inversion H7; subst; simpl in *.
    eapply H; eauto.
  - inversion H6; subst; simpl in *.
    auto.
    inversion H7; subst; simpl in *.
    eapply H1; eauto.
  - destruct act.
  - destruct act.
  - inversion H6; subst; simpl in *.
    auto.
    inversion H7; subst; simpl in *.
    eapply H5; eauto.
Qed.

Lemma tensor_preserves_L2_inv: forall inv,
  invariant_ind L2 inv ->
  invariant_ind (tensor L1 L2)
    (fun s => inv s.(Tensor.L2State).(LState)).
Proof.
  intros. unfold invariant_ind in *.
  intuition.
  - inversion H4; subst.
    inversion H7; subst.
    apply H0; auto.
  - inversion H6; subst; simpl in *.
    inversion H7; subst; simpl in *.
    eapply H; eauto.
    auto.
  - inversion H6; subst; simpl in *.
    inversion H7; subst; simpl in *.
    eapply H1; eauto.
    auto.
  - destruct act.
  - destruct act.
  - inversion H6; subst; simpl in *.
    inversion H7; subst; simpl in *.
    eapply H5; eauto.
    auto.
Qed.

Lemma tensor_preserves_sync_L1_inv: forall inv,
  invariant_ind (sync L1) inv ->
  invariant_ind (tensor L1 L2)
    (fun s => inv s.(Tensor.L1State)).
Proof.
  intros.
  intros. unfold invariant_ind in *.
  intuition.
  - inversion H4; subst.
    inversion H6; subst.
    apply H0; auto.
  - inversion H6; subst; simpl in *.
    auto.
    inversion H7; subst; simpl in *.
    eapply H; eauto.
  - inversion H6; subst; simpl in *.
    auto.
    inversion H7; subst; simpl in *.
    eapply H1; eauto.
  - destruct act.
  - destruct act.
  - inversion H6; subst; simpl in *.
    auto.
    inversion H7; subst; simpl in *.
    eapply H5; eauto.
Qed.

Lemma tensor_preserves_sync_L2_inv: forall inv,
  invariant_ind (sync L2) inv ->
  invariant_ind (tensor L1 L2)
    (fun s => inv s.(Tensor.L2State)).
Proof.
  intros. unfold invariant_ind in *.
  intuition.
  - inversion H4; subst.
    inversion H6; subst.
    apply H0; auto.
  - inversion H6; subst; simpl in *.
    inversion H7; subst; simpl in *.
    eapply H; eauto.
    auto.
  - inversion H6; subst; simpl in *.
    inversion H7; subst; simpl in *.
    eapply H1; eauto.
    auto.
  - destruct act.
  - destruct act.
  - inversion H6; subst; simpl in *.
    inversion H7; subst; simpl in *.
    eapply H5; eauto.
    auto.
Qed.

End test.

Section TensorSyncCounterProp.

Definition front_rear_wf (s : (state front_rear)) :=
  (sync_counter_wf s.(Tensor.L1State)) /\
  (sync_counter_wf s.(Tensor.L2State)).

Lemma front_rear_wf_inv:
  invariant_ind front_rear front_rear_wf.
Proof.
  unfold front_rear_wf.
  apply invariant_ind_land.
  apply tensor_preserves_sync_L1_inv.
  apply sync_counter_wf_inv.
  apply tensor_preserves_sync_L2_inv.
  apply sync_counter_wf_inv.
Qed.

End TensorSyncCounterProp.

Section ArrayFRProp.

Variable L : nat.

Definition array_front_rear_wf (s : state (array_front_rear L)) :=
  front_rear_wf s.(Tensor.L2State).(LState).

Lemma array_front_rear_inv:
  invariant_ind (array_front_rear L) array_front_rear_wf.
Proof.
  apply tensor_preserves_L2_inv.
  apply front_rear_wf_inv.
Qed.

End ArrayFRProp.

Section test.

Context {liA liB : language_interface}.
Variable L1 : lts li_null liA.
Variable L2 : lts liA liB.

Lemma compose_preserves_L1_inv: forall inv,
  invariant_ind L1 inv ->
  composed_lts.invariant_ind ((compose L1 L2))
    (fun s => inv s.(Compose.L1State).(LState)).
Proof.
  intros. unfold invariant_ind in *.
  unfold composed_lts.invariant_ind.
  intuition.
  - inversion H4; subst.
    inversion H6; subst.
    apply H0; auto.
  - inversion H6; subst; simpl in *.
    inversion H7; subst; simpl in *.
    eapply H; eauto.
  - inversion H6; subst; simpl in *.
    auto.
  - inversion H6; subst; simpl in *.
    auto.
  - destruct act.
  - destruct act.
  - inversion H6; subst; simpl in *.
    auto.
  - inversion H6; subst; simpl in *.
    inversion H8; subst; simpl in *.
    eapply H1; eauto.
  - inversion H6; subst; simpl in *.
    inversion H7; subst; simpl in *.
    eapply H5; eauto.
Qed.

End test.

Section test.

Context {liA liB : language_interface }.
Variable L : lts liA liB.

Definition invariant_mutual_ind (P Q : state L -> Prop) :=
  (forall st, L.(new_state) st -> P st /\ Q st) /\
  (forall st st' act pid,
    P st ->
    Q st ->
    step L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    Q st ->
    step L st pid act st' ->
    Q st') /\
  (forall st st' act pid,
    P st ->
    Q st ->
    initial_state L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    Q st ->
    initial_state L st pid act st' ->
    Q st') /\
  (forall st st' act pid,
    P st ->
    Q st ->
    at_external L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    Q st ->
    at_external L st pid act st' ->
    Q st') /\
  (forall st st' act pid,
    P st ->
    Q st ->
    after_external L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    Q st ->
    after_external L st pid act st' ->
    Q st') /\
  (forall st st' act pid,
    P st ->
    Q st ->
    final_state L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    Q st ->
    final_state L st pid act st' ->
    Q st')
  .

Lemma invariant_ind_break_down: forall P Q,
  invariant_mutual_ind P Q ->
  invariant_ind L (fun s => P s /\ Q s).
Proof.
  intros.
  unfold invariant_ind. 
  unfold invariant_mutual_ind in H.
  destruct H as [Hnew [Hstep [Hstep' [Hinit [Hinit' [Hat [Hat' [Hafter [Hafter' [Hfinal Hfinal']]]]]]]]]].
  intuition.
  - apply Hstep in H0; auto.
  - apply Hstep' in H0; auto.
  - apply Hinit in H0; auto.
  - apply Hinit' in H0; auto.
  - apply Hat in H0; auto.
  - apply Hat' in H0; auto.
  - apply Hafter in H0; auto.
  - apply Hafter' in H0; auto.
  - apply Hfinal in H0; auto.
  - apply Hfinal' in H0; auto.
Qed.

End test.