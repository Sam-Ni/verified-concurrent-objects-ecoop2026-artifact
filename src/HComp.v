Require Import
  List
  Arith
  LibVar
  LibEnv
  LTS
  Refinement
  ImplRefinement
  Compose
  ImplTensor
  RawTensor
  Tensor
  SyncLTS
  VE
  VerifiedConcurrentObject.
Import ListNotations.

Section SyncIdentity.

Context {liA : language_interface}.
Variable L: lts li_null liA.

Lemma sync_identity:
  refines (sync L) (sync (sync L)).
Proof.
  eapply forward_simulation_inv_ind
    with (f:=fun (x : state (sync L)) (y : state (sync (sync L))) =>
      x.(LState) = y.(LState).(LState) /\
      x.(PidPos) = y.(LState).(PidPos) /\
      y.(PidPos) = y.(LState).(PidPos)
      )
      (inv:=fun x => True).
  unfold fsim_properties_inv_ind. intuition.
  - unfold invariant_ind. intuition.
  - inversion H; subst; simpl in *.
    exists (
      mkSyncState (sync L)
      (mkSyncState 
        L
        (LState s1) []
      )
       []
    ).
    simpl. intuition.
    unfold sync_new_state.
    simpl. intuition.
    unfold sync_new_state.
    simpl. intuition.
  - inversion H1; subst; simpl in *.
    exists (
      mkSyncState (sync L)
      (mkSyncState 
        L
        st' ((pid, Run) :: pos)
      )
      ((pid, Run) :: pos)
    ).
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_initial_state_L with (pos:=PidPos); eauto.
      subst. auto.
      subst. auto.
      destruct LState; simpl in *.
      subst. auto.
      subst. auto.
  - inversion H1; subst; simpl in *.
    exists (
      mkSyncState (sync L)
      (mkSyncState 
        L
        st' (remove pos pid)
      )
      (remove pos pid)
    ).
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_final_state_L with (pos:=PidPos); eauto.
      subst. auto.
      subst. auto.
      destruct LState; simpl in *.
      subst. auto.
      subst. auto.
  - destruct qa.
  - destruct ra.
  - inversion H1; subst; simpl in *.
    exists (
      mkSyncState (sync L)
      (mkSyncState 
        L
        st' (pos)
      )
      (pos)
    ).
    simpl. intuition.
      destruct s2. simpl in *.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      subst. auto.
      subst. auto.
      destruct LState; simpl in *.
      subst. auto.
      subst. auto.
Qed.

End SyncIdentity.

Section TensorConsistency.

Context {liA liB : language_interface}.
Variable L1: lts li_null liA.
Variable L2: lts li_null liB.

Definition thread_state_map (h1 h2 h : env Position) :=
  forall pid p,
  ((binds pid p h1) \/
  (binds pid p h2) ->
  binds pid p h) /\
  (pid # h1 /\ 
    pid # h2 -> pid # h).

Definition syn_raw_tensor_wf (y : state (sync (RawTensor.tensor L1 L2))) :=
  ok (y.(PidPos)).

Lemma raw_tensor_tensor:
  refines
    (tensor L1 L2)
    (sync (RawTensor.tensor L1 L2)).
Proof.
  eapply forward_simulation_inv_ind
    with (f:=fun (x : state (tensor L1 L2)) (y : state (sync (RawTensor.tensor L1 L2))) =>
      x.(L1State).(LState) = y.(LState).(RawTensor.L1State) /\
      x.(L2State).(LState) = y.(LState).(RawTensor.L2State) /\
      thread_state_map (x.(L1State).(PidPos)) (x.(L2State).(PidPos)) y.(PidPos) /\
      syn_raw_tensor_wf y
      )
      (inv:=fun x => True).
  unfold fsim_properties_inv_ind. intuition.
  - unfold invariant_ind. intuition.
  - inversion H; subst; simpl in *.
    inversion H0; subst; simpl in *.
    inversion H1; subst; simpl in *.
    exists (
      mkSyncState (RawTensor.tensor L1 L2)
      (@RawTensor.mkTensorState liA liB
        L1 L2 
        (LState (L1State s1))
        (LState (L2State s1)))
       []
    ).
    simpl. intuition.
    unfold sync_new_state.
    simpl. intuition.
    unfold RawTensor.tensor_new_state.
    simpl. intuition.
    unfold thread_state_map.
    intuition.
    rewrite H3 in H7.
    intuition.
    rewrite H5 in H7.
    intuition.
    apply notin_empty.
    unfold syn_raw_tensor_wf.
    simpl. econstructor.
  - rename H5 into Hwf.
    inversion H1; subst; simpl in *.
    -- inversion H4; subst; simpl in *.
      exists (
        mkSyncState (RawTensor.tensor L1 L2)
        (@RawTensor.mkTensorState liA liB
          L1 L2 
          (LState st1)
          (st'))
        ((pid, Run) :: (PidPos s2))
      ).
      simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_initial_state_L with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      apply H3; auto.
      econstructor.
      eapply RawTensor.tensor_initial_state_L2; eauto.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst. apply binds_in in H7.
        unfold "#" in Hnotin. intuition.
        apply binds_push_neq; auto.
        apply H3; auto.
      apply binds_push_inv in H7; auto.
      intuition.
        subst. apply binds_push_eq; auto.
        apply binds_push_neq; auto.
        apply H3; auto.
      simpl in *.
      apply notin_union in H8.
      apply notin_union.
      intuition.
      apply H3; auto.
      unfold syn_raw_tensor_wf.
      simpl.
      econstructor; eauto.
      apply H3; auto.
      econstructor.
    -- inversion H4; subst; simpl in *.
      exists (
        mkSyncState (RawTensor.tensor L1 L2)
        (@RawTensor.mkTensorState liA liB
          L1 L2 
          (st')
          (LState st2)
          )
        ((pid, Run) :: (PidPos s2))
      ).
      simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_initial_state_L with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      apply H3; auto.
      econstructor.
      eapply RawTensor.tensor_initial_state_L1; eauto.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      apply binds_push_inv in H7; auto.
      intuition.
        subst. apply binds_push_eq; auto.
        apply binds_push_neq; auto.
        apply H3; auto.
      destruct (eq_nat_dec pid0 pid).
        subst. apply binds_in in H7.
        unfold "#" in Hnotin. intuition.
        apply binds_push_neq; auto.
        apply H3; auto.
      simpl in *.
      apply notin_union in H7.
      apply notin_union.
      intuition.
      apply H3; auto.
      unfold syn_raw_tensor_wf.
      simpl.
      econstructor; eauto.
      apply H3; auto.
      econstructor.
  - rename H5 into Hwf.
    inversion H1; subst; simpl in *.
    -- inversion H4; subst; simpl in *.
      exists (
        mkSyncState (RawTensor.tensor L1 L2)
        (@RawTensor.mkTensorState liA liB
          L1 L2 
          (LState st1)
          (st'))
        (remove (PidPos s2) pid)
      ).
      simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_final_state_L with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      apply H3; auto.
      eapply RawTensor.tensor_final_state_L2; eauto.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst. apply binds_in in H7.
        unfold "#" in Hnotin. intuition.
        apply remove_neq_preserves_binds; auto.
        apply H3; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply binds_in in H7.
        assert (pid # (remove pos pid)).
        apply ok_remove_notin; auto.
        unfold "#" in H0.
        intuition.
        apply remove_preserves_binds_notin in H7; auto.
        apply remove_neq_preserves_binds; auto.
        apply H3; auto.
      destruct (eq_nat_dec pid0 pid).
        subst. apply ok_remove_notin; auto.
        apply remove_neq_preserves_notin in H8; auto.
        apply remove_preserves_notin; auto.
        apply H3; auto.
      unfold syn_raw_tensor_wf.
      simpl.
      apply remove_preserves_ok; auto.
    -- inversion H4; subst; simpl in *.
      exists (
        mkSyncState (RawTensor.tensor L1 L2)
        (@RawTensor.mkTensorState liA liB
          L1 L2 
          (st')
          (LState st2)
          )
        (remove (PidPos s2) pid)
      ).
      simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_final_state_L with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      apply H3; auto.
      eapply RawTensor.tensor_final_state_L1; eauto.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply binds_in in H7.
        assert (pid # (remove pos pid)).
        apply ok_remove_notin; auto.
        unfold "#" in H2.
        intuition.
        apply remove_preserves_binds_notin in H7; auto.
        apply remove_neq_preserves_binds; auto.
        apply H3; auto.
      destruct (eq_nat_dec pid0 pid).
        subst. apply binds_in in H7.
        unfold "#" in Hnotin. intuition.
        apply remove_neq_preserves_binds; auto.
        apply H3; auto.
      destruct (eq_nat_dec pid0 pid).
        subst. apply ok_remove_notin; auto.
        apply remove_neq_preserves_notin in H7; auto.
        apply remove_preserves_notin; auto.
        apply H3; auto.
      unfold syn_raw_tensor_wf.
      simpl.
      apply remove_preserves_ok; auto.
  - inversion H1.
  - inversion H1.
  - rename H5 into Hwf.
    inversion H1; subst; simpl in *.
    -- inversion H4; subst; simpl in *.
      exists (
        mkSyncState (RawTensor.tensor L1 L2)
        (@RawTensor.mkTensorState liA liB
          L1 L2 
          (LState st1)
          (st'))
        ((PidPos s2))
      ).
      simpl. intuition.
      destruct s2. simpl in *.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      eapply H3; eauto.
      eapply RawTensor.tensor_step_L2_internal; eauto.
      destruct LState. simpl in *.
      subst. auto.
    -- inversion H4; subst; simpl in *.
      exists (
        mkSyncState (RawTensor.tensor L1 L2)
        (@RawTensor.mkTensorState liA liB
          L1 L2 
          (st')
          (LState st2)
          )
        ((PidPos s2))
      ).
      simpl. intuition.
      destruct s2. simpl in *.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      eapply H3; eauto.
      eapply RawTensor.tensor_step_L1_internal; eauto.
      destruct LState. simpl in *.
      subst. auto.
Qed.

Definition syn_tensor_wf (y : state (sync (tensor L1 L2))) :=
  ok (y.(PidPos)).

Lemma tensor_consistency:
  refines (tensor L1 L2) (sync (tensor L1 L2)).
Proof.
  eapply forward_simulation_inv_ind
    with (f:=fun (x : state (tensor L1 L2)) (y : state (sync (tensor L1 L2))) =>
      x.(L1State) = y.(LState).(L1State) /\
      x.(L2State) = y.(LState).(L2State) /\
      thread_state_map (y.(LState).(L1State).(PidPos)) (y.(LState).(L2State).(PidPos)) y.(PidPos) /\
      syn_tensor_wf y
      )
      (inv:=fun x => True).
  unfold fsim_properties_inv_ind. intuition.
  - unfold invariant_ind. intuition.
  - inversion H; subst; simpl in *.
    inversion H0; subst; simpl in *.
    inversion H1; subst; simpl in *.
    exists (
      mkSyncState (tensor L1 L2)
      (@mkTensorState liA liB
        L1 L2 
        ((L1State s1))
        ((L2State s1)))
       []
    ).
    simpl. intuition.
    unfold sync_new_state.
    simpl. intuition.
    unfold thread_state_map.
    intuition.
    rewrite H3 in H7.
    intuition.
    rewrite H5 in H7.
    intuition.
    apply notin_empty.
    unfold syn_tensor_wf.
    simpl.
    econstructor.
  - rename H5 into Hwf.
    exists (
      mkSyncState (tensor L1 L2)
      (@mkTensorState liA liB
        L1 L2 
        ((L1State s1'))
        ((L2State s1')))
        ((pid, Run) :: s2.(PidPos))
    ).
    simpl.
    inversion H1; subst; simpl in *.
    -- inversion H4; subst; simpl in *.
      simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_initial_state_L with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      apply H3; auto.
      econstructor.
      rewrite H6.
      simpl. intuition.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst. apply binds_in in H2.
        unfold "#" in Hnotin. intuition.
        apply binds_push_neq; auto.
        apply H3; auto.
      apply binds_push_inv in H2; auto.
      intuition.
        subst. apply binds_push_eq; auto.
        apply binds_push_neq; auto.
        apply H3; auto.
        rewrite H6. simpl.
        intuition.
      simpl in *.
      apply notin_union in H7.
      apply notin_union.
      intuition.
      apply H3; auto.
      rewrite H6. simpl.
      intuition.
      unfold syn_raw_tensor_wf.
      simpl.
      econstructor; eauto.
      apply H3; auto.
      econstructor.
      rewrite H6.
      simpl. intuition.
    -- inversion H4; subst; simpl in *.
      simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_initial_state_L with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      apply H3; auto.
      econstructor.
      rewrite H6.
      simpl. intuition.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      apply binds_push_inv in H2; auto.
      intuition.
        subst. apply binds_push_eq; auto.
        apply binds_push_neq; auto.
        apply H3; auto.
        rewrite H6. simpl.
        intuition.
      destruct (eq_nat_dec pid0 pid).
        subst. apply binds_in in H2.
        unfold "#" in Hnotin. intuition.
        apply binds_push_neq; auto.
        apply H3; auto.
      simpl in *.
      apply notin_union in H2.
      apply notin_union.
      intuition.
      apply H3; auto.
      rewrite H6. simpl.
      intuition.
      unfold syn_raw_tensor_wf.
      simpl.
      econstructor; eauto.
      apply H3; auto.
      econstructor.
      rewrite H6.
      simpl. intuition.
  - rename H5 into Hwf.
    exists (
      mkSyncState (tensor L1 L2)
      (@mkTensorState liA liB
        L1 L2 
        ((L1State s1'))
        ((L2State s1')))
        (remove s2.(PidPos) pid)
    ).
    simpl.
    inversion H1; subst; simpl in *.
    -- inversion H4; subst; simpl in *.
      simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_final_state_L with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      apply H3; auto.
      rewrite H6.
      simpl. intuition.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst. apply binds_in in H2.
        unfold "#" in Hnotin. intuition.
        apply remove_neq_preserves_binds; auto.
        apply H3; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply binds_in in H2.
        assert (pid # (remove pos pid)).
        apply ok_remove_notin; auto.
        unfold "#" in H0.
        intuition.
        apply remove_preserves_binds_notin in H2; auto.
        apply remove_neq_preserves_binds; auto.
        apply H3; auto.
        rewrite H6. simpl. intuition.
      destruct (eq_nat_dec pid0 pid).
        subst. apply ok_remove_notin; auto.
        apply remove_neq_preserves_notin in H7; auto.
        apply remove_preserves_notin; auto.
        apply H3; auto.
        rewrite H6. simpl. intuition.
      unfold syn_tensor_wf.
      simpl.
      apply remove_preserves_ok; auto.
    -- inversion H4; subst; simpl in *.
      simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_final_state_L with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      apply H3; auto.
      rewrite H6.
      simpl. intuition.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply binds_in in H2.
        assert (pid # (remove pos pid)).
        apply ok_remove_notin; auto.
        unfold "#" in H0.
        intuition.
        apply remove_preserves_binds_notin in H2; auto.
        apply remove_neq_preserves_binds; auto.
        apply H3; auto.
        rewrite H6. simpl. intuition.
      destruct (eq_nat_dec pid0 pid).
        subst. apply binds_in in H2.
        unfold "#" in Hnotin. intuition.
        apply remove_neq_preserves_binds; auto.
        apply H3; auto.
      destruct (eq_nat_dec pid0 pid).
        subst. apply ok_remove_notin; auto.
        apply remove_neq_preserves_notin in H2; auto.
        apply remove_preserves_notin; auto.
        apply H3; auto.
        rewrite H6. simpl. intuition.
      unfold syn_tensor_wf.
      simpl.
      apply remove_preserves_ok; auto.
  - inversion H1.
  - inversion H1.
  - rename H5 into Hwf.
    exists (
      mkSyncState (tensor L1 L2)
      (@mkTensorState liA liB
        L1 L2 
        ((L1State s1'))
        ((L2State s1')))
        (s2.(PidPos))
    ).
    simpl.
    inversion H1; subst; simpl in *.
    -- inversion H4; subst; simpl in *.
      simpl. intuition.
      destruct s2. simpl in *.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      apply H3; auto.
      rewrite H6.
      simpl. intuition.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      eapply H3; eauto.
      eapply H3; eauto.
      rewrite H6. simpl. intuition.
      eapply H3; eauto.
      rewrite H6. simpl. intuition.
    -- inversion H4; subst; simpl in *.
      simpl. intuition.
      destruct s2. simpl in *.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      apply H3; auto.
      rewrite H6.
      simpl. intuition.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      eapply H3; eauto.
      rewrite H6. simpl. intuition.
      eapply H3; eauto.
      eapply H3; eauto.
      rewrite H6. simpl. intuition.
Qed.

End TensorConsistency.

Section ImplTensorConsistency.

Context {liA liB : language_interface}.
Context {liC liD : language_interface}.
Variable M1: lts liA liB.
Variable M2: lts liC liD.

Require Import ImplTensor.

Definition syn_tensor_wf' (y : state (sync (tensor M1 M2))) :=
  ok (y.(PidPos)).

Lemma impl_tensor_consistency:
  impl_refines (ImplTensor.tensor M1 M2) (sync (ImplTensor.tensor M1 M2)).
Proof.
  eapply forward_simulation_inv_ind
    with (f:=fun (x : state (ImplTensor.tensor M1 M2)) (y : state (sync (ImplTensor.tensor M1 M2))) =>
      x.(ImplTensor.L1State) = y.(LState).(L1State) /\
      x.(L2State) = y.(LState).(L2State) /\
      thread_state_map (y.(LState).(L1State).(PidPos)) (y.(LState).(L2State).(PidPos)) y.(PidPos) /\
      syn_tensor_wf' y
      )
      (inv:=fun x => True).
  unfold fsim_properties_inv_ind. intuition.
  - unfold invariant_ind. intuition.
  - inversion H; subst; simpl in *.
    inversion H0; subst; simpl in *.
    inversion H1; subst; simpl in *.
    exists (
      mkSyncState (tensor M1 M2)
      (@mkTensorState liA liB liC liD
        M1 M2 
        ((L1State s1))
        ((L2State s1)))
       []
    ).
    simpl. intuition.
    unfold sync_new_state.
    simpl. intuition.
    unfold thread_state_map.
    intuition.
    rewrite H3 in H7.
    intuition.
    rewrite H5 in H7.
    intuition.
    apply notin_empty.
    unfold syn_tensor_wf'.
    simpl.
    econstructor.
  - rename H5 into Hwf.
    exists (
      mkSyncState (tensor M1 M2)
      (@mkTensorState liA liB liC liD
        M1 M2 
        ((L1State s1'))
        ((L2State s1')))
        ((pid, Run) :: s2.(PidPos))
    ).
    simpl.
    inversion H1; subst; simpl in *.
    -- inversion H4; subst; simpl in *.
      simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_initial_state_L with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      apply H3; auto.
      econstructor.
      rewrite H6.
      simpl. intuition.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst. apply binds_in in H2.
        unfold "#" in Hnotin. intuition.
        apply binds_push_neq; auto.
        apply H3; auto.
      apply binds_push_inv in H2; auto.
      intuition.
        subst. apply binds_push_eq; auto.
        apply binds_push_neq; auto.
        apply H3; auto.
        rewrite H6. simpl.
        intuition.
      simpl in *.
      apply notin_union in H7.
      apply notin_union.
      intuition.
      apply H3; auto.
      rewrite H6. simpl.
      intuition.
      unfold syn_raw_tensor_wf.
      simpl.
      econstructor; eauto.
      apply H3; auto.
      econstructor.
      rewrite H6.
      simpl. intuition.
    -- inversion H4; subst; simpl in *.
      simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_initial_state_L with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      apply H3; auto.
      econstructor.
      rewrite H6.
      simpl. intuition.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      apply binds_push_inv in H2; auto.
      intuition.
        subst. apply binds_push_eq; auto.
        apply binds_push_neq; auto.
        apply H3; auto.
        rewrite H6. simpl.
        intuition.
      destruct (eq_nat_dec pid0 pid).
        subst. apply binds_in in H2.
        unfold "#" in Hnotin. intuition.
        apply binds_push_neq; auto.
        apply H3; auto.
      simpl in *.
      apply notin_union in H2.
      apply notin_union.
      intuition.
      apply H3; auto.
      rewrite H6. simpl.
      intuition.
      unfold syn_raw_tensor_wf.
      simpl.
      econstructor; eauto.
      apply H3; auto.
      econstructor.
      rewrite H6.
      simpl. intuition.
  - rename H5 into Hwf.
    exists (
      mkSyncState (tensor M1 M2)
      (@mkTensorState liA liB liC liD
        M1 M2 
        ((L1State s1'))
        ((L2State s1')))
        (remove s2.(PidPos) pid)
    ).
    simpl.
    inversion H1; subst; simpl in *.
    -- inversion H4; subst; simpl in *.
      simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_final_state_L with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      apply H3; auto.
      rewrite H6.
      simpl. intuition.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst. apply binds_in in H2.
        unfold "#" in Hnotin. intuition.
        apply remove_neq_preserves_binds; auto.
        apply H3; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply binds_in in H2.
        assert (pid # (remove pos pid)).
        apply ok_remove_notin; auto.
        unfold "#" in H0.
        intuition.
        apply remove_preserves_binds_notin in H2; auto.
        apply remove_neq_preserves_binds; auto.
        apply H3; auto.
        rewrite H6. simpl. intuition.
      destruct (eq_nat_dec pid0 pid).
        subst. apply ok_remove_notin; auto.
        apply remove_neq_preserves_notin in H7; auto.
        apply remove_preserves_notin; auto.
        apply H3; auto.
        rewrite H6. simpl. intuition.
      unfold syn_tensor_wf.
      simpl.
      apply remove_preserves_ok; auto.
    -- inversion H4; subst; simpl in *.
      simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_final_state_L with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      apply H3; auto.
      rewrite H6.
      simpl. intuition.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply binds_in in H2.
        assert (pid # (remove pos pid)).
        apply ok_remove_notin; auto.
        unfold "#" in H0.
        intuition.
        apply remove_preserves_binds_notin in H2; auto.
        apply remove_neq_preserves_binds; auto.
        apply H3; auto.
        rewrite H6. simpl. intuition.
      destruct (eq_nat_dec pid0 pid).
        subst. apply binds_in in H2.
        unfold "#" in Hnotin. intuition.
        apply remove_neq_preserves_binds; auto.
        apply H3; auto.
      destruct (eq_nat_dec pid0 pid).
        subst. apply ok_remove_notin; auto.
        apply remove_neq_preserves_notin in H2; auto.
        apply remove_preserves_notin; auto.
        apply H3; auto.
        rewrite H6. simpl. intuition.
      unfold syn_tensor_wf.
      simpl.
      apply remove_preserves_ok; auto.
  - rename H5 into Hwf.
    exists (
      mkSyncState (tensor M1 M2)
      (@mkTensorState liA liB liC liD
        M1 M2 
        ((L1State s1'))
        ((L2State s1')))
        ((pid, Wait) :: (remove s2.(PidPos) pid))
    ).
    simpl.
    inversion H1; subst; simpl in *.
    -- inversion H4; subst; simpl in *.
      simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_at_external_L with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      rewrite H6 in H3.
      simpl in *.
      apply H3; auto.
      rewrite H6.
      simpl. intuition.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst. apply binds_in in H2.
        unfold "#" in Hnotin. intuition.
        apply binds_push_neq; auto.
        apply remove_neq_preserves_binds; auto.
        apply H3; auto.
      apply binds_push_inv in H2; auto.
      intuition.
        subst. apply binds_push_eq; auto.
        apply binds_push_neq; auto.
        apply remove_neq_preserves_binds; auto.
        apply remove_preserves_binds_notin in H7; auto.
        apply H3; auto.
        rewrite H6. simpl.
        intuition.
      simpl in *.
      apply notin_union in H7.
      apply notin_union.
      intuition.
      apply remove_preserves_notin; auto.
      apply notin_neq in H0.
      apply remove_neq_preserves_notin in H8; auto.
      apply H3; auto.
      rewrite H6. simpl.
      intuition.
      unfold syn_tensor_wf'.
      simpl.
      econstructor; eauto.
      apply remove_preserves_ok; auto.
      apply ok_remove_notin; auto.
    -- inversion H4; subst; simpl in *.
      simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_at_external_L with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      rewrite H6 in H3.
      simpl in *.
      apply H3; auto.
      rewrite H6.
      simpl. intuition.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      apply binds_push_inv in H2; auto.
      intuition.
        subst. apply binds_push_eq; auto.
        apply binds_push_neq; auto.
        apply remove_neq_preserves_binds; auto.
        apply remove_preserves_binds_notin in H7; auto.
        apply H3; auto.
        rewrite H6. simpl.
        intuition.
      destruct (eq_nat_dec pid0 pid).
        subst. apply binds_in in H2.
        unfold "#" in Hnotin. intuition.
        apply binds_push_neq; auto.
        apply remove_neq_preserves_binds; auto.
        apply H3; auto.
      simpl in *.
      apply notin_union in H2.
      apply notin_union.
      intuition.
      apply remove_preserves_notin; auto.
      apply notin_neq in H0.
      apply remove_neq_preserves_notin in H8; auto.
      apply H3; auto.
      rewrite H6. simpl.
      intuition.
      unfold syn_tensor_wf'.
      simpl.
      econstructor; eauto.
      apply remove_preserves_ok; auto.
      apply ok_remove_notin; auto.
  - rename H5 into Hwf.
    exists (
      mkSyncState (tensor M1 M2)
      (@mkTensorState liA liB liC liD
        M1 M2 
        ((L1State s1'))
        ((L2State s1')))
        ((pid, Run) :: (remove s2.(PidPos) pid))
    ).
    simpl.
    inversion H1; subst; simpl in *.
    -- inversion H4; subst; simpl in *.
      simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_after_external_L with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      rewrite H6 in H3.
      simpl in *.
      apply H3; auto.
      rewrite H6.
      simpl. intuition.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst. apply binds_in in H2.
        unfold "#" in Hnotin. intuition.
        apply binds_push_neq; auto.
        apply remove_neq_preserves_binds; auto.
        apply H3; auto.
      apply binds_push_inv in H2; auto.
      intuition.
        subst. apply binds_push_eq; auto.
        apply binds_push_neq; auto.
        apply remove_neq_preserves_binds; auto.
        apply remove_preserves_binds_notin in H7; auto.
        apply H3; auto.
        rewrite H6. simpl.
        intuition.
      simpl in *.
      apply notin_union in H7.
      apply notin_union.
      intuition.
      apply remove_preserves_notin; auto.
      apply notin_neq in H0.
      apply remove_neq_preserves_notin in H8; auto.
      apply H3; auto.
      rewrite H6. simpl.
      intuition.
      unfold syn_tensor_wf'.
      simpl.
      econstructor; eauto.
      apply remove_preserves_ok; auto.
      apply ok_remove_notin; auto.
    -- inversion H4; subst; simpl in *.
      simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_after_external_L with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      rewrite H6 in H3.
      simpl in *.
      apply H3; auto.
      rewrite H6.
      simpl. intuition.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      apply binds_push_inv in H2; auto.
      intuition.
        subst. apply binds_push_eq; auto.
        apply binds_push_neq; auto.
        apply remove_neq_preserves_binds; auto.
        apply remove_preserves_binds_notin in H7; auto.
        apply H3; auto.
        rewrite H6. simpl.
        intuition.
      destruct (eq_nat_dec pid0 pid).
        subst. apply binds_in in H2.
        unfold "#" in Hnotin. intuition.
        apply binds_push_neq; auto.
        apply remove_neq_preserves_binds; auto.
        apply H3; auto.
      simpl in *.
      apply notin_union in H2.
      apply notin_union.
      intuition.
      apply remove_preserves_notin; auto.
      apply notin_neq in H0.
      apply remove_neq_preserves_notin in H8; auto.
      apply H3; auto.
      rewrite H6. simpl.
      intuition.
      unfold syn_tensor_wf'.
      simpl.
      econstructor; eauto.
      apply remove_preserves_ok; auto.
      apply ok_remove_notin; auto.
  - rename H5 into Hwf.
    exists (
      mkSyncState (tensor M1 M2)
      (@mkTensorState liA liB liC liD
        M1 M2 
        ((L1State s1'))
        ((L2State s1')))
        (s2.(PidPos))
    ).
    simpl.
    inversion H1; subst; simpl in *.
    -- inversion H4; subst; simpl in *.
      simpl. intuition.
      destruct s2. simpl in *.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      apply H3; auto.
      rewrite H6.
      simpl. intuition.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      eapply H3; eauto.
      eapply H3; eauto.
      rewrite H6. simpl. intuition.
      eapply H3; eauto.
      rewrite H6. simpl. intuition.
    -- inversion H4; subst; simpl in *.
      simpl. intuition.
      destruct s2. simpl in *.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      apply H3; auto.
      rewrite H6.
      simpl. intuition.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      eapply H3; eauto.
      rewrite H6. simpl. intuition.
      eapply H3; eauto.
      eapply H3; eauto.
      rewrite H6. simpl. intuition.
Qed.

End ImplTensorConsistency.

Section DistributativeLaw.

Context {liA liB : language_interface}.
Context {liC liD : language_interface}.
Variable L1: lts li_null liA.
Variable M1: lts liA liB.
Variable L1': lts li_null liB.
Variable L2: lts li_null liC.
Variable M2: lts liC liD.
Variable L2': lts li_null liD.

(* Fixpoint gather_pos_from_inner_pos pos2 pos1 : env Position :=
  match pos2 with
  | nil => nil
  | (pid, p2) :: pos2' =>
    let pos' := gather_pos_from_inner_pos pos2' pos1 in
    match p2 with
    | Wait => match get pid pos1 with
              | None => (pid, Run) :: pos' (* unreachable *)
              | Some p1 => match p1 with
                          | Wait => (pid, Wait) :: pos'
                          | Run => (pid, Run) :: pos'
                          end
              end
    | Run => (pid, Run) :: pos'
    end
  end. *)

Definition thread_state_map' (h1 h2 h : env Position) :=
  forall pid p,
  (binds pid p h2 ->
  pid # h1 ->
  binds pid p h) /\
  (binds pid p h1 ->
  binds pid p h) /\
  (pid # h1 /\ 
    pid # h2 -> pid # h).

Definition thread_state_map_inv (h1 h2 h : env Position) :=
  forall pid,
  pid # h ->
  (pid # h1 /\ pid # h2).

Definition thread_state_map_inv' (h1 h2 : env Position) :=
  forall pid,
  (binds pid Run h1 -> binds pid Wait h2) /\
  (binds pid Run h2 -> pid # h1) /\
  (pid # h2 -> pid # h1)
  .

Definition thread_state_map_inv'' (h1 h2 : env Position) :=
  forall pid p,
  (binds pid p h1 -> pid # h2) /\
  (binds pid p h2 -> pid # h1).

Definition StateL1L (x : state (linked_lts
     (compose (tensor L1 L2) (ImplTensor.tensor M1 M2)))) :=
  x.(Compose.L1State).(LState).(Tensor.L1State).(LState).

Definition StateL2L (x : state (linked_lts
     (compose (tensor L1 L2) (ImplTensor.tensor M1 M2)))) :=
  x.(Compose.L1State).(LState).(Tensor.L2State).(LState).

Definition StateM1L (x : state (linked_lts
     (compose (tensor L1 L2) (ImplTensor.tensor M1 M2)))) :=
  x.(Compose.L2State).(LState).(ImplTensor.L1State).(LState).

Definition StateM2L (x : state (linked_lts
     (compose (tensor L1 L2) (ImplTensor.tensor M1 M2)))) :=
  x.(Compose.L2State).(LState).(ImplTensor.L2State).(LState).

Definition StateL1R (y : state (tensor (linked_lts (raw_compose L1 M1))
     (linked_lts (raw_compose L2 M2)))) :=
  y.(Tensor.L1State).(LState).(LTS.RawL1State).

Definition StateL2R (y : state (tensor (linked_lts (raw_compose L1 M1))
     (linked_lts (raw_compose L2 M2)))) :=
  y.(Tensor.L2State).(LState).(LTS.RawL1State).

Definition StateM1R (y : state (tensor (linked_lts (raw_compose L1 M1))
     (linked_lts (raw_compose L2 M2)))) :=
  y.(Tensor.L1State).(LState).(LTS.RawL2State).

Definition StateM2R (y : state (tensor (linked_lts (raw_compose L1 M1))
     (linked_lts (raw_compose L2 M2)))) :=
  y.(Tensor.L2State).(LState).(LTS.RawL2State).

Definition PosL1L (x : state (linked_lts
     (compose (tensor L1 L2) (ImplTensor.tensor M1 M2)))) :=
  x.(Compose.L1State).(LState).(Tensor.L1State).(PidPos).

Definition PosL2L (x : state (linked_lts
     (compose (tensor L1 L2) (ImplTensor.tensor M1 M2)))) :=
  x.(Compose.L1State).(LState).(Tensor.L2State).(PidPos).

Definition PosM1L (x : state (linked_lts
     (compose (tensor L1 L2) (ImplTensor.tensor M1 M2)))) :=
  x.(Compose.L2State).(LState).(ImplTensor.L1State).(PidPos).

Definition PosM2L (x : state (linked_lts
     (compose (tensor L1 L2) (ImplTensor.tensor M1 M2)))) :=
  x.(Compose.L2State).(LState).(ImplTensor.L2State).(PidPos).

Definition PosComp1L (x : state (linked_lts
     (compose (tensor L1 L2) (ImplTensor.tensor M1 M2)))) :=
  x.(Compose.L1State).(PidPos).

Definition PosComp2L (x : state (linked_lts
     (compose (tensor L1 L2) (ImplTensor.tensor M1 M2)))) :=
  x.(Compose.L2State).(PidPos).

Definition PosComp1R (y : state (tensor (linked_lts (raw_compose L1 M1))
     (linked_lts (raw_compose L2 M2)))) :=
  y.(Tensor.L1State).(PidPos).

Definition PosComp2R (y : state (tensor (linked_lts (raw_compose L1 M1))
     (linked_lts (raw_compose L2 M2)))) :=
  y.(Tensor.L2State).(PidPos).

Definition tensor_raw_compose_wf (y : state (tensor (linked_lts (raw_compose L1 M1))
     (linked_lts (raw_compose L2 M2)))) :=
    ok (PosComp1R y) /\
    ok (PosComp2R y).

Ltac uf :=
    unfold PosComp1R, PosComp2R, PosL1L, PosL2L, PosM1L, PosM2L in *;
    unfold PosComp1L, PosComp2L in *;
    unfold StateL1L, StateL2L, StateM1L, StateM2L, StateL1R, StateL2R, StateM1R, StateM2R in *; simpl in *.

Lemma distributative_law:
refines
  (linked_lts
     (compose (tensor L1 L2) (ImplTensor.tensor M1 M2)))
  (tensor (linked_lts (raw_compose L1 M1))
     (linked_lts (raw_compose L2 M2))).
Proof.

  eapply forward_simulation_inv_ind
    with (f:=fun (x : state (linked_lts
     (compose (tensor L1 L2) (ImplTensor.tensor M1 M2)))) (y : state (tensor (linked_lts (raw_compose L1 M1))
     (linked_lts (raw_compose L2 M2)))) =>
      StateL1L x = StateL1R y /\
      StateL2L x = StateL2R y /\
      StateM1L x = StateM1R y /\
      StateM2L x = StateM2R y /\
      thread_state_map'
        (PosL1L x)
        (PosM1L x)
        (PosComp1R y) /\
      thread_state_map'
        (PosL2L x)
        (PosM2L x)
        (PosComp2R y) /\
      thread_state_map_inv
        (PosL1L x)
        (PosL2L x)
        (PosComp1L x) /\
      thread_state_map_inv
        (PosM1L x)
        (PosM2L x)
        (PosComp2L x) /\
      tensor_raw_compose_wf y /\
      thread_state_map_inv'
        (PosL1L x)
        (PosM1L x) /\
      thread_state_map_inv'
        (PosL2L x)
        (PosM2L x) /\
      thread_state_map_inv''
        (PosM1L x)
        (PosM2L x)
      )
      (inv:=fun x => True).
  unfold fsim_properties_inv_ind. intuition.
  - unfold invariant_ind. intuition.
  - inversion H; subst; simpl in *.
    inversion H0; subst; simpl in *.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H6; subst; simpl in *.
    inversion H7; subst; simpl in *.
    inversion H8; subst; simpl in *.
    inversion H9; subst; simpl in *.
    exists (
      (@mkTensorState liB liD
        (linked_lts (raw_compose L1 M1)) (linked_lts (raw_compose L2 M2))
        (mkSyncState (linked_lts (raw_compose L1 M1))
          (@mkRawComposedState liA liB
            L1 M1 
            (StateL1L s1)
            (StateM1L s1)
          )
          []
        )
        (mkSyncState (linked_lts (raw_compose L2 M2))
          (@mkRawComposedState liC liD
            L2 M2 
            (StateL2L s1)
            (StateM2L s1)
          )
          []
        )
      )
    ).
    simpl. intuition.
    unfold tensor_new_state; simpl.
    unfold sync_new_state; simpl.
    unfold raw_composed_new_state; simpl.
    intuition.
    unfold PosComp1R, PosL1L, PosM1L.
    unfold thread_state_map' in *; simpl in *.
    rewrite H11.
    rewrite H15.
    intuition.
    unfold PosComp2R, PosL2L, PosM2L.
    unfold thread_state_map' in *; simpl in *.
    rewrite H13.
    rewrite H17.
    intuition.
    unfold thread_state_map_inv.
    unfold PosComp1L, PosL1L, PosL2L; simpl in *.
    rewrite H3, H11, H13; simpl.
    intros. intuition.
    unfold thread_state_map_inv.
    unfold PosComp2L, PosM1L, PosM2L; simpl in *.
    rewrite H5, H15, H17; simpl.
    intros. intuition.
    unfold tensor_raw_compose_wf.
    unfold PosComp1R, PosComp2R; simpl.
    intuition; econstructor.
    unfold thread_state_map_inv'.
    uf.
    rewrite H11, H15; simpl.
    intros. intuition; inversion H18.
    unfold thread_state_map_inv'.
    uf.
    rewrite H13, H17; simpl.
    intros. intuition; inversion H18.
    unfold thread_state_map_inv''.
    uf.
    rewrite H15, H17; simpl.
    intros. intuition; inversion H18.
  (* initiate state *)
  - rename H2 into HmapL1.
    rename H0 into HmapL2.
    rename H3 into HmapM1.
    rename H4 into HmapM2.
    rename H5 into Hmap1.
    rename H6 into Hmap2.
    rename H7 into Hmapinv1.
    rename H8 into Hmapinv2.
    rename H9 into Hwf.
    rename H10 into Hmapinv1'.
    rename H11 into Hmapinv2'.
    rename H13 into Hmapinv2''.
    inversion H1; subst; simpl in *.
    inversion H0; subst; simpl in *.
    inversion H2; subst; simpl in *.
    (* M2 *)
    --
      exists (
        (@mkTensorState liB liD
          (linked_lts (raw_compose L1 M1)) (linked_lts (raw_compose L2 M2))
          (mkSyncState (linked_lts (raw_compose L1 M1))
            (@mkRawComposedState liA liB
              L1 M1 
              (StateL1R s2)
              (StateM1R s2)
            )
            (PosComp1R s2)
          )
          (mkSyncState (linked_lts (raw_compose L2 M2))
            (@mkRawComposedState liC liD
              L2 M2 
              (StateL2R s2)
              (st2'.(LState))
            )
            ((pid, Run)::(PosComp2R s2))
          )
        )
      ).
      simpl. intuition.
      destruct s2. simpl in *.
      inversion H3; subst; simpl in *.
      destruct L2State; simpl in *.
      destruct LState; simpl in *.
      uf. subst.
      eapply tensor_initial_state_L2; eauto.
      unfold thread_state_map' in *; simpl in *.
      apply Hmap1; auto.
      econstructor.
      intuition.
      apply Hmapinv1; auto.
      simpl.
      eapply sync_initial_state_L with (pos:=PidPos); eauto.
      apply Hwf; auto.
      unfold thread_state_map' in *; simpl in *.
      uf.
      apply Hmap2; auto.
      econstructor.
      intuition.
      apply Hmapinv1; auto.
      eapply raw_composed_initial_state_L2; eauto.
      destruct L1State; simpl in *.
      destruct LState; simpl in *.
      uf. subst. reflexivity.
      unfold thread_state_map'.
      uf. intros.
      inversion H3; subst; simpl in *.
      intuition.
      apply binds_push_inv in H5; simpl in *.
      intuition.
        subst. apply binds_push_eq; auto.
        unfold thread_state_map_inv in *.
        apply binds_push_neq; auto.
        apply Hmap2 in H8; auto.
      destruct (eq_nat_dec pid0 pid).
        subst. unfold thread_state_map_inv in *.
        apply Hmapinv1 in Hnotin; auto.
        apply binds_in in H5.
        unfold "#" in Hnotin; intuition.
        apply binds_push_neq; auto.
        apply Hmap2; auto.
      apply notin_union in H7.
      apply notin_union.
      intuition.
      apply Hmap2; auto.
      unfold thread_state_map_inv.
      uf. intros.
      inversion H3; subst; simpl in *.
      apply notin_union in H4.
      intuition.
      apply notin_neq in H6.
      apply Hmapinv2; auto.
      apply notin_union; auto.
      intuition.
      apply Hmapinv2; auto.
      unfold tensor_raw_compose_wf in *.
      uf.
      inversion H3; subst; simpl in *.
      intuition.
      econstructor; eauto.
      apply Hmap2; auto.
      econstructor.
      intuition.
      apply Hmapinv1; auto.
      unfold thread_state_map_inv' in *.
      uf. intros.
      inversion H3; subst; simpl in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmapinv2' in Hnotin2; auto.
        apply binds_in in H5.
        unfold "#" in Hnotin2.
        intuition.
        apply binds_push_neq; auto.
        apply Hmapinv2'; auto.
      apply binds_push_inv in H5; auto.
      intuition.
        subst.
        apply Hmapinv2' in Hnotin2; auto.
        apply Hmapinv2' in H7; auto.
      apply notin_union in H5.
      intuition. apply notin_neq in H6.
        apply Hmapinv2' in H7; auto.
      unfold thread_state_map_inv'' in *.
      uf. intros.
      inversion H3; subst; simpl in *.
      intuition.
      apply notin_union.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply binds_in in H5.
        unfold "#" in Hnotin1.
        intuition.
        intuition.
        apply notin_neq; auto.
        apply Hmapinv2'' in H5; auto.
      apply binds_push_inv in H5; auto.
      intuition.
        subst. auto.
        apply Hmapinv2'' in H7; auto.
    (* M1 *)
    --
      exists (
        (@mkTensorState liB liD
          (linked_lts (raw_compose L1 M1)) (linked_lts (raw_compose L2 M2))
          (mkSyncState (linked_lts (raw_compose L1 M1))
            (@mkRawComposedState liA liB
              L1 M1 
              (StateL1R s2)
              (st1'.(LState))
            )
            ((pid, Run)::(PosComp1R s2))
          )
          (mkSyncState (linked_lts (raw_compose L2 M2))
            (@mkRawComposedState liC liD
              L2 M2 
              (StateL2R s2)
              (StateM2R s2)
            )
            ((PosComp2R s2))
          )
        )
      ).
      simpl. intuition.
      destruct s2. simpl in *.
      inversion H3; subst; simpl in *.
      destruct L1State; simpl in *.
      destruct LState; simpl in *.
      uf. subst.
      eapply tensor_initial_state_L1; eauto.
      unfold thread_state_map' in *; simpl in *.
      apply Hmap2; auto.
      econstructor.
      intuition.
      apply Hmapinv1; auto.
      simpl.
      eapply sync_initial_state_L with (pos:=PidPos); eauto.
      apply Hwf; auto.
      unfold thread_state_map' in *; simpl in *.
      uf.
      apply Hmap1; auto.
      econstructor.
      intuition.
      apply Hmapinv1; auto.
      eapply raw_composed_initial_state_L2; eauto.
      destruct L2State; simpl in *.
      destruct LState; simpl in *.
      uf. subst. reflexivity.
      unfold thread_state_map'.
      uf. intros.
      inversion H3; subst; simpl in *.
      intuition.
      apply binds_push_inv in H5; simpl in *.
      intuition.
        subst. apply binds_push_eq; auto.
        unfold thread_state_map_inv in *.
        apply binds_push_neq; auto.
        apply Hmap1 in H8; auto.
      destruct (eq_nat_dec pid0 pid).
        subst. unfold thread_state_map_inv in *.
        apply Hmapinv1 in Hnotin; auto.
        apply binds_in in H5.
        unfold "#" in Hnotin; intuition.
        apply binds_push_neq; auto.
        apply Hmap1; auto.
      apply notin_union in H7.
      apply notin_union.
      intuition.
      apply Hmap1; auto.
      unfold thread_state_map_inv.
      uf. intros.
      inversion H3; subst; simpl in *.
      apply notin_union in H4.
      intuition.
      apply notin_union; auto.
      intuition.
      apply Hmapinv2; auto.
      apply notin_neq in H6.
      apply Hmapinv2; auto.
      unfold tensor_raw_compose_wf in *.
      uf.
      inversion H3; subst; simpl in *.
      intuition.
      econstructor; eauto.
      apply Hmap1; auto.
      econstructor.
      intuition.
      apply Hmapinv1; auto.

      unfold thread_state_map_inv' in *.
      uf. intros.
      inversion H3; subst; simpl in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmapinv1' in Hnotin2; auto.
        apply binds_in in H5.
        unfold "#" in Hnotin2.
        intuition.
        apply binds_push_neq; auto.
        apply Hmapinv1'; auto.
      apply binds_push_inv in H5; auto.
      intuition.
        subst.
        apply Hmapinv1' in Hnotin2; auto.
        apply Hmapinv1' in H7; auto.
      apply notin_union in H5.
      intuition. apply notin_neq in H6.
        apply Hmapinv1' in H7; auto.
      unfold thread_state_map_inv'' in *.
      uf. intros.
      inversion H3; subst; simpl in *.
      intuition.
      apply binds_push_inv in H5; auto.
      intuition.
        subst. auto.
        apply Hmapinv2'' in H7; auto.
      apply notin_union.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply binds_in in H5.
        unfold "#" in Hnotin1.
        intuition.
        intuition.
        apply notin_neq; auto.
        apply Hmapinv2'' in H5; auto.
  (* final_state  *)
  - rename H2 into HmapL1.
    rename H0 into HmapL2.
    rename H3 into HmapM1.
    rename H4 into HmapM2.
    rename H5 into Hmap1.
    rename H6 into Hmap2.
    rename H7 into Hmapinv1.
    rename H8 into Hmapinv2.
    rename H9 into Hwf.
    rename H10 into Hmapinv1'.
    rename H11 into Hmapinv2'.
    rename H13 into Hmapinv2''.
    inversion H1; subst; simpl in *.
    inversion H0; subst; simpl in *.
    inversion H2; subst; simpl in *.
    (* M2 *)
    --
      exists (
        (@mkTensorState liB liD
          (linked_lts (raw_compose L1 M1)) (linked_lts (raw_compose L2 M2))
          (mkSyncState (linked_lts (raw_compose L1 M1))
            (@mkRawComposedState liA liB
              L1 M1 
              (StateL1R s2)
              (StateM1R s2)
            )
            (PosComp1R s2)
          )
          (mkSyncState (linked_lts (raw_compose L2 M2))
            (@mkRawComposedState liC liD
              L2 M2 
              (StateL2R s2)
              (st2'.(LState))
            )
            (remove (PosComp2R s2) pid)
          )
        )
      ).
      simpl. intuition.
      destruct s2. simpl in *.
      inversion H3; subst; simpl in *.
      destruct L2State; simpl in *.
      destruct LState; simpl in *.
      uf. subst.
      eapply tensor_final_state_L2; eauto.
      unfold thread_state_map' in *; simpl in *.
      apply Hmap2 in Hbinds1; auto.
      apply Hmapinv1; auto.
      apply Hmap1; auto.
      econstructor.
      intuition.
      apply Hmapinv1; auto.
      simpl.
      eapply sync_final_state_L with (pos:=PidPos); eauto.
      apply Hwf; auto.
      unfold thread_state_map' in *; simpl in *.
      uf.
      apply Hmap2 in Hbinds1; auto.
      apply Hmapinv1; auto.
      eapply raw_composed_final_state_L2; eauto.
      destruct L1State; simpl in *.
      destruct LState; simpl in *.
      uf. subst. reflexivity.
      unfold thread_state_map'.
      uf. intros.
      inversion H3; subst; simpl in *.
      intuition.

      destruct (eq_nat_dec pid0 pid).
        subst.
        apply binds_in in H5.
        assert (pid # (remove pos0 pid)).
        apply ok_remove_notin; auto.
        unfold "#" in H7.
        intuition.
        apply remove_preserves_binds_notin in H5; auto.
        apply remove_neq_preserves_binds; auto.
        apply Hmap2 in H5; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmapinv1 in Hnotin; auto.
        apply binds_in in H5.
        unfold "#" in Hnotin.
        intuition.
        apply remove_neq_preserves_binds; auto.
        apply Hmap2; auto.
      destruct (eq_nat_dec pid0 pid).
        subst. apply ok_remove_notin; auto.
        unfold tensor_raw_compose_wf in *; simpl in *.
        uf. intuition.
        apply remove_neq_preserves_notin in H7; auto.
        apply remove_preserves_notin; auto.
        apply Hmap2; auto.
      unfold thread_state_map_inv.
      uf. intros.
      inversion H3; subst; simpl in *.
      destruct (eq_nat_dec pid0 pid).
        subst. intuition.
        apply ok_remove_notin; auto.
      apply remove_neq_preserves_notin in H4; auto.
      intuition. apply Hmapinv2; auto.
      apply remove_preserves_notin; auto.
      apply Hmapinv2; auto.
      unfold tensor_raw_compose_wf in *.
      uf. intuition.
      apply remove_preserves_ok; auto.

      unfold thread_state_map_inv' in *.
      uf. intros.
      inversion H3; subst; simpl in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmapinv2' in Hbinds1; auto.
        apply binds_in in H5.
        unfold "#" in Hbinds1.
        intuition.
        apply remove_neq_preserves_binds; auto.
        apply Hmapinv2'; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmapinv2' in Hbinds1; auto.
        apply remove_preserves_binds_notin in H5; auto.
        apply Hmapinv2' in H5; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmapinv2' in Hbinds1; auto.
        apply remove_neq_preserves_notin in H5; auto.
        apply Hmapinv2' in H5; auto.
      unfold thread_state_map_inv'' in *.
      uf. intros.
      inversion H3; subst; simpl in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply ok_remove_notin; auto.
        apply remove_preserves_notin; auto.
        apply Hmapinv2'' in H5; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove pos0 pid)).
        apply ok_remove_notin; auto.
        apply binds_in in H5.
        unfold "#" in H6.
        intuition.
        apply remove_preserves_binds_notin in H5; auto.
        apply Hmapinv2'' in H5; auto.
    (* M1 *)
    --
      exists (
        (@mkTensorState liB liD
          (linked_lts (raw_compose L1 M1)) (linked_lts (raw_compose L2 M2))
          (mkSyncState (linked_lts (raw_compose L1 M1))
            (@mkRawComposedState liA liB
              L1 M1 
              (StateL1R s2)
              (st1'.(LState))
            )
            (remove (PosComp1R s2) pid)
          )
          (mkSyncState (linked_lts (raw_compose L2 M2))
            (@mkRawComposedState liC liD
              L2 M2 
              (StateL2R s2)
              (StateM2R s2)
            )
            (PosComp2R s2)
          )
        )
      ).
      simpl. intuition.
      destruct s2. simpl in *.
      inversion H3; subst; simpl in *.
      destruct L1State; simpl in *.
      destruct LState; simpl in *.
      uf. subst.
      eapply tensor_final_state_L1; eauto.
      unfold thread_state_map' in *; simpl in *.
      apply Hmap1 in Hbinds1; auto.
      apply Hmapinv1; auto.
      apply Hmap2; auto.
      econstructor.
      intuition.
      apply Hmapinv1; auto.
      simpl.
      eapply sync_final_state_L with (pos:=PidPos); eauto.
      apply Hwf; auto.
      unfold thread_state_map' in *; simpl in *.
      uf.
      apply Hmap1 in Hbinds1; auto.
      apply Hmapinv1; auto.
      eapply raw_composed_final_state_L2; eauto.
      destruct L2State; simpl in *.
      destruct LState; simpl in *.
      uf. subst. reflexivity.
      unfold thread_state_map'.
      uf. intros.
      inversion H3; subst; simpl in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply binds_in in H5.
        assert (pid # (remove pos0 pid)).
        apply ok_remove_notin; auto.
        unfold "#" in H7.
        intuition.
        apply remove_preserves_binds_notin in H5; auto.
        apply remove_neq_preserves_binds; auto.
        apply Hmap1 in H5; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmapinv1 in Hnotin; auto.
        apply binds_in in H5.
        unfold "#" in Hnotin.
        intuition.
        apply remove_neq_preserves_binds; auto.
        apply Hmap1; auto.
      destruct (eq_nat_dec pid0 pid).
        subst. apply ok_remove_notin; auto.
        unfold tensor_raw_compose_wf in *; simpl in *.
        uf. intuition.
        apply remove_neq_preserves_notin in H7; auto.
        apply remove_preserves_notin; auto.
        apply Hmap1; auto.
      unfold thread_state_map_inv.
      uf. intros.
      inversion H3; subst; simpl in *.
      destruct (eq_nat_dec pid0 pid).
        subst. intuition.
        apply ok_remove_notin; auto.
      apply remove_neq_preserves_notin in H4; auto.
      intuition.
      apply remove_preserves_notin; auto.
      apply Hmapinv2; auto.
      apply Hmapinv2; auto.
      unfold tensor_raw_compose_wf in *.
      uf. intuition.
      apply remove_preserves_ok; auto.
      unfold thread_state_map_inv' in *.
      uf. intros.
      inversion H3; subst; simpl in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmapinv1' in Hbinds1; auto.
        apply binds_in in H5.
        unfold "#" in Hbinds1.
        intuition.
        apply remove_neq_preserves_binds; auto.
        apply Hmapinv1'; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmapinv1' in Hbinds1; auto.
        apply remove_preserves_binds_notin in H5; auto.
        apply Hmapinv1' in H5; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmapinv1' in Hbinds1; auto.
        apply remove_neq_preserves_notin in H5; auto.
        apply Hmapinv1' in H5; auto.
      unfold thread_state_map_inv'' in *.
      uf. intros.
      inversion H3; subst; simpl in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove pos0 pid)).
        apply ok_remove_notin; auto.
        apply binds_in in H5.
        unfold "#" in H6.
        intuition.
        apply remove_preserves_binds_notin in H5; auto.
        apply Hmapinv2'' in H5; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply ok_remove_notin; auto.
        apply remove_preserves_notin; auto.
        apply Hmapinv2'' in H5; auto.
  - destruct qa.
  - destruct ra.
  - rename H2 into HmapL1.
    rename H0 into HmapL2.
    rename H3 into HmapM1.
    rename H4 into HmapM2.
    rename H5 into Hmap1.
    rename H6 into Hmap2.
    rename H7 into Hmapinv1.
    rename H8 into Hmapinv2.
    rename H9 into Hwf.
    rename H10 into Hmapinv1'.
    rename H11 into Hmapinv2'.
    rename H13 into Hmapinv2''.

    inversion H1; subst; simpl in *.
    inversion H0; subst; simpl in *.
    (* Step M1 M2 *)
    -- inversion H2; subst; simpl in *.
      inversion H3; subst; simpl in *.
      (* Step M2 *)
      --- exists (
        (@mkTensorState liB liD
          (linked_lts (raw_compose L1 M1)) (linked_lts (raw_compose L2 M2))
          (mkSyncState (linked_lts (raw_compose L1 M1))
            (@mkRawComposedState liA liB
              L1 M1 
              (StateL1R s2)
              (StateM1R s2)
            )
            (PosComp1R s2)
          )
          (mkSyncState (linked_lts (raw_compose L2 M2))
            (@mkRawComposedState liC liD
              L2 M2 
              (StateL2R s2)
              (st2'.(LState))
            )
            (PosComp2R s2)
          )
        )
      ).
      simpl. intuition.
      destruct s2. simpl in *.
      inversion H4; subst; simpl in *.
      destruct L2State; simpl in *.
      destruct LState; simpl in *.
      uf. subst.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      simpl.
      eapply tensor_step_L2_internal; eauto.
      unfold thread_state_map in *.
      simpl.
      eapply Hmap2 in Hbinds1; eauto.
      apply Hmapinv1 in Hnotin; auto.
      intuition.
      apply Hmap1; auto.
      econstructor. intuition.
      apply Hmapinv1 in Hnotin; auto.
      intuition.
      simpl.
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      unfold tensor_raw_compose_wf in *; simpl in *.
      uf. intuition.
      apply Hmap2 in Hbinds1; auto.
      apply Hmapinv1 in Hnotin; auto.
      intuition.
      simpl.
      eapply linked_step_int_L2; eauto.
      simpl.
      eapply raw_composed_step_L2_internal; eauto.
      destruct L1State; simpl in *.
      destruct LState; simpl in *.
      reflexivity.
      unfold thread_state_map'.
      uf. intros.
      inversion H4; subst; simpl in *.
      intuition.
      apply Hmap2 in H6; auto.
      apply Hmap2 in H6; auto.
      apply Hmap2.
      econstructor.
      intuition.
      unfold thread_state_map_inv.
      uf. inversion H4; subst; simpl in *.
      intros. intuition.
      apply Hmapinv2; auto.
      apply Hmapinv2; auto.

      unfold thread_state_map_inv' in *.
      uf. intros.
      inversion H4; subst; simpl in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmapinv2' in Hbinds1; auto.
        apply binds_in in H6.
        unfold "#" in Hbinds1.
        intuition.
        apply Hmapinv2'; auto.
      apply Hmapinv2' in H6; auto.
      apply Hmapinv2' in H6; auto.
      unfold thread_state_map_inv'' in *.
      uf. intros.
      inversion H4; subst; simpl in *.
      intuition.
      apply Hmapinv2'' in H6; auto.
      apply Hmapinv2'' in H6; auto.
      (* Step M1 *)
      --- exists (
        (@mkTensorState liB liD
          (linked_lts (raw_compose L1 M1)) (linked_lts (raw_compose L2 M2))
          (mkSyncState (linked_lts (raw_compose L1 M1))
            (@mkRawComposedState liA liB
              L1 M1 
              (StateL1R s2)
              (st1'.(LState))
            )
            (PosComp1R s2)
          )
          (mkSyncState (linked_lts (raw_compose L2 M2))
            (@mkRawComposedState liC liD
              L2 M2 
              (StateL2R s2)
              (StateM2R s2)
            )
            (PosComp2R s2)
          )
        )
      ).
      simpl. intuition.
      destruct s2. simpl in *.
      inversion H4; subst; simpl in *.
      destruct L1State; simpl in *.
      destruct LState; simpl in *.
      uf. subst.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      simpl.
      eapply tensor_step_L1_internal; eauto.
      unfold thread_state_map in *.
      simpl.
      eapply Hmap1 in Hbinds1; eauto.
      apply Hmapinv1 in Hnotin; auto.
      intuition.
      apply Hmap2; auto.
      econstructor. intuition.
      apply Hmapinv1 in Hnotin; auto.
      intuition.
      simpl.
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      unfold tensor_raw_compose_wf in *; simpl in *.
      uf. intuition.
      apply Hmap1 in Hbinds1; auto.
      apply Hmapinv1 in Hnotin; auto.
      intuition.
      simpl.
      eapply linked_step_int_L2; eauto.
      simpl.
      eapply raw_composed_step_L2_internal; eauto.
      destruct L2State; simpl in *.
      destruct LState; simpl in *.
      reflexivity.
      unfold thread_state_map'.
      uf. intros.
      inversion H4; subst; simpl in *.
      intuition.
      apply Hmap1 in H6; auto.
      apply Hmap1 in H6; auto.
      apply Hmap1.
      econstructor.
      intuition.
      unfold thread_state_map_inv.
      uf. inversion H4; subst; simpl in *.
      intros. intuition.
      apply Hmapinv2; auto.
      apply Hmapinv2; auto.

      unfold thread_state_map_inv' in *.
      uf. intros.
      inversion H4; subst; simpl in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmapinv1' in Hbinds1; auto.
        apply binds_in in H6.
        unfold "#" in Hbinds1.
        intuition.
        apply Hmapinv1'; auto.
      apply Hmapinv1' in H6; auto.
      apply Hmapinv1' in H6; auto.
      unfold thread_state_map_inv'' in *.
      uf. intros.
      inversion H4; subst; simpl in *.
      intuition.
      apply Hmapinv2'' in H6; auto.
      apply Hmapinv2'' in H6; auto.
    (* Step L1 L2 *)
    -- inversion H0; subst; simpl in *.
      inversion H2; subst; simpl in *.
      inversion H3; subst; simpl in *.
      (* Step L2 *)
      --- exists (
        (@mkTensorState liB liD
          (linked_lts (raw_compose L1 M1)) (linked_lts (raw_compose L2 M2))
          (mkSyncState (linked_lts (raw_compose L1 M1))
            (@mkRawComposedState liA liB
              L1 M1 
              (StateL1R s2)
              (StateM1R s2)
            )
            (PosComp1R s2)
          )
          (mkSyncState (linked_lts (raw_compose L2 M2))
            (@mkRawComposedState liC liD
              L2 M2 
              (st2'.(LState))
              (StateM2R s2)
            )
            (PosComp2R s2)
          )
        )
      ).
      simpl. intuition.
      destruct s2. simpl in *.
      inversion H4; subst; simpl in *.
      destruct L2State; simpl in *.
      destruct LState; simpl in *.
      uf. subst.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      simpl.
      eapply tensor_step_L2_internal; eauto.
      unfold thread_state_map in *.
      simpl.
      eapply Hmap2 in Hbinds1; eauto.
      (* apply Hmapinv1 in Hnotin; auto.
      intuition. *)
      apply Hmap1; auto.
      econstructor. intuition.
      unfold thread_state_map_inv'' in *.
      unfold thread_state_map_inv' in *.
      apply Hmapinv2' in Hbinds1; auto.
      apply Hmapinv2'' in Hbinds1; auto.
      simpl.
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      unfold tensor_raw_compose_wf in *; simpl in *.
      uf. intuition.
      apply Hmap2 in Hbinds1; auto.
      simpl.
      eapply linked_step_int_L1; eauto.
      simpl.
      eapply raw_composed_step_L1_internal; eauto.
      destruct L1State; simpl in *.
      destruct LState; simpl in *.
      reflexivity.
      unfold thread_state_map'.
      uf. intros.
      inversion H4; subst; simpl in *.
      intuition.
      apply Hmap2 in H6; auto.
      apply Hmap2 in H6; auto.
      apply Hmap2.
      econstructor.
      intuition.
      unfold thread_state_map_inv.
      uf. inversion H4; subst; simpl in *.
      intros. intuition.
      apply Hmapinv1; auto.
      apply Hmapinv1; auto.

      unfold thread_state_map_inv' in *.
      uf. intros.
      inversion H4; subst; simpl in *.
      intuition.
      apply Hmapinv2' in H6; auto.
      apply Hmapinv2' in H6; auto.
      apply Hmapinv2' in H6; auto.
      (* Step L1 *)
      --- exists (
        (@mkTensorState liB liD
          (linked_lts (raw_compose L1 M1)) (linked_lts (raw_compose L2 M2))
          (mkSyncState (linked_lts (raw_compose L1 M1))
            (@mkRawComposedState liA liB
              L1 M1 
              (st1'.(LState))
              (StateM1R s2)
            )
            (PosComp1R s2)
          )
          (mkSyncState (linked_lts (raw_compose L2 M2))
            (@mkRawComposedState liC liD
              L2 M2 
              (StateL2R s2)
              (StateM2R s2)
            )
            (PosComp2R s2)
          )
        )
      ).
      simpl. intuition.
      destruct s2. simpl in *.
      inversion H4; subst; simpl in *.
      destruct L1State; simpl in *.
      destruct LState; simpl in *.
      uf. subst.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      simpl.
      eapply tensor_step_L1_internal; eauto.
      unfold thread_state_map in *.
      simpl.
      eapply Hmap1 in Hbinds1; eauto.
      apply Hmap2; auto.
      econstructor. intuition.
      unfold thread_state_map_inv'' in *.
      unfold thread_state_map_inv' in *.
      apply Hmapinv1' in Hbinds1; auto.
      apply Hmapinv2'' in Hbinds1; auto.
      simpl.
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      unfold tensor_raw_compose_wf in *; simpl in *.
      uf. intuition.
      apply Hmap1 in Hbinds1; auto.
      simpl.
      eapply linked_step_int_L1; eauto.
      simpl.
      eapply raw_composed_step_L1_internal; eauto.
      destruct L2State; simpl in *.
      destruct LState; simpl in *.
      reflexivity.
      unfold thread_state_map'.
      uf. intros.
      inversion H4; subst; simpl in *.
      intuition.
      apply Hmap1 in H6; auto.
      apply Hmap1 in H6; auto.
      apply Hmap1.
      econstructor.
      intuition.
      unfold thread_state_map_inv.
      uf. inversion H4; subst; simpl in *.
      intros. intuition.
      apply Hmapinv1; auto.
      apply Hmapinv1; auto.

      unfold thread_state_map_inv' in *.
      uf. intros.
      inversion H4; subst; simpl in *.
      intuition.
      apply Hmapinv1' in H6; auto.
      apply Hmapinv1' in H6; auto.
      apply Hmapinv1' in H6; auto.
    (* internal query *)
    -- inversion H0; subst; simpl in *.
      inversion H2; subst; simpl in *.
      inversion H3; subst; simpl in *.
      inversion H4; subst; simpl in *.
      (* query M2 *)
      --- inversion H5; subst; simpl in *.
        exists (
        (@mkTensorState liB liD
          (linked_lts (raw_compose L1 M1)) (linked_lts (raw_compose L2 M2))
          (mkSyncState (linked_lts (raw_compose L1 M1))
            (@mkRawComposedState liA liB
              L1 M1 
              (StateL1R s2)
              (StateM1R s2)
            )
            (PosComp1R s2)
          )
          (mkSyncState (linked_lts (raw_compose L2 M2))
            (@mkRawComposedState liC liD
              L2 M2 
              (st2'0.(LState))
              (st2'.(LState))
            )
            ((PosComp2R s2))
          )
        )
      ).
      simpl. intuition.
      destruct s2. simpl in *.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      destruct L2State; simpl in *.
      destruct LState; simpl in *.
      uf. subst.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      simpl.
      eapply tensor_step_L2_internal; eauto.
      unfold thread_state_map in *.
      simpl.
      eapply Hmap2 in Hbinds0; eauto.
      apply Hmap1; auto.
      econstructor.
      simpl.
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      unfold tensor_raw_compose_wf in *; simpl in *.
      uf. intuition.
      apply Hmap2 in Hbinds0; auto.
      simpl.
      eapply linked_step_L2_push; eauto.
      simpl.
      eapply raw_composed_step_L2_push; eauto.
      destruct L1State; simpl in *.
      destruct LState; simpl in *.
      reflexivity.
      unfold thread_state_map'.
      uf. intros.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      intuition.
        apply notin_union in H11.
        intuition.
        apply notin_neq in H12.
        apply binds_push_inv in H10; auto.
        intuition.
        apply remove_preserves_binds_notin in H14; auto.
        apply Hmap2 in H14; auto.
      apply binds_push_inv in H10; auto.
        intuition.
        subst.
        apply Hmap2 in Hbinds0; auto.
        apply Hmap2 in H12; auto.
      apply notin_union in H11, H12.
      intuition.
      apply notin_neq in H10.
      apply remove_neq_preserves_notin in H14; auto.
      apply Hmap2; auto.
      unfold thread_state_map_inv.
      uf.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      intros.
      apply notin_union in H10.
      intuition.
      apply notin_neq in H11.
      apply Hmapinv1; auto.
      apply notin_union; auto.
      intuition.
      apply Hmapinv1; auto.

      unfold thread_state_map_inv.
      uf.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      intros.
      apply notin_union in H10.
      intuition.
      apply notin_neq in H11.
      apply remove_neq_preserves_notin in H12; auto.
      apply Hmapinv2; auto.
      apply notin_union; auto.
      intuition.
      apply notin_neq in H11; auto.
      apply remove_neq_preserves_notin in H12; auto.
      apply remove_preserves_notin; auto.
      apply Hmapinv2; auto.

      unfold thread_state_map_inv' in *.
      uf. intros.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      intuition.
      apply binds_push_inv in H10; auto.
      intuition.
        subst. apply binds_push_eq; auto.
        apply binds_push_neq; auto.
        apply remove_neq_preserves_binds; auto.
        apply Hmapinv2' in H12; auto.
      apply binds_push_inv in H10; auto.
      intuition.
        subst. discriminate.
        apply notin_union. intuition.
        apply notin_neq; auto.
        apply remove_preserves_binds_notin in H12; auto.
        apply Hmapinv2' in H12; auto.
      apply notin_union in H10; auto.
      apply notin_union; auto.
      intuition.
        apply notin_neq in H11; auto.
        apply remove_neq_preserves_notin in H12; auto.
        apply Hmapinv2' in H12; auto.

      unfold thread_state_map_inv'' in *.
      uf. intros.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      intuition.
      apply notin_union.
      destruct (eq_nat_dec pid0 pid).
        subst. apply binds_in in H10.
        unfold "#" in Hnotin0.
        intuition.
        intuition.
        apply notin_neq; auto.
        apply remove_preserves_notin; auto.
        apply Hmapinv2'' in H10; auto.
      apply binds_push_inv in H10; auto.
      intuition.
        subst. apply Hmapinv2'' in Hbinds0; auto.
        apply remove_preserves_binds_notin in H12; auto.
        apply Hmapinv2'' in H12; auto.
      (* query M1 *)
      --- inversion H5; subst; simpl in *.
        exists (
        (@mkTensorState liB liD
          (linked_lts (raw_compose L1 M1)) (linked_lts (raw_compose L2 M2))
          (mkSyncState (linked_lts (raw_compose L1 M1))
            (@mkRawComposedState liA liB
              L1 M1 
              (st1'0.(LState))
              (st1'.(LState))
            )
            (PosComp1R s2)
          )
          (mkSyncState (linked_lts (raw_compose L2 M2))
            (@mkRawComposedState liC liD
              L2 M2 
              (StateL2R s2)
              (StateM2R s2)
            )
            ((PosComp2R s2))
          )
        )
      ).
      simpl. intuition.
      destruct s2. simpl in *.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      destruct L1State; simpl in *.
      destruct LState; simpl in *.
      uf. subst.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      simpl.
      eapply tensor_step_L1_internal; eauto.
      unfold thread_state_map in *.
      simpl.
      eapply Hmap1 in Hbinds0; eauto.
      apply Hmap2; auto.
      econstructor.
      simpl.
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      unfold tensor_raw_compose_wf in *; simpl in *.
      uf. intuition.
      apply Hmap1 in Hbinds0; auto.
      simpl.
      eapply linked_step_L2_push; eauto.
      simpl.
      eapply raw_composed_step_L2_push; eauto.
      destruct L2State; simpl in *.
      destruct LState; simpl in *.
      reflexivity.
      unfold thread_state_map'.
      uf. intros.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      intuition.
        apply notin_union in H11.
        intuition.
        apply notin_neq in H12.
        apply binds_push_inv in H10; auto.
        intuition.
        apply remove_preserves_binds_notin in H14; auto.
        apply Hmap1 in H14; auto.
      apply binds_push_inv in H10; auto.
        intuition.
        subst.
        apply Hmap1 in Hbinds0; auto.
        apply Hmap1 in H12; auto.
      apply notin_union in H11, H12.
      intuition.
      apply notin_neq in H10.
      apply remove_neq_preserves_notin in H14; auto.
      apply Hmap1; auto.
      unfold thread_state_map_inv.
      uf.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      intros.
      apply notin_union in H10.
      intuition.
      apply notin_union; auto.
      intuition.
      apply Hmapinv1; auto.
      apply notin_neq in H11.
      apply Hmapinv1; auto.

      unfold thread_state_map_inv.
      uf.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      intros.
      apply notin_union in H10.
      intuition.
      apply notin_union; auto.
      intuition.
      apply notin_neq in H11; auto.
      apply remove_neq_preserves_notin in H12; auto.
      apply remove_preserves_notin; auto.
      apply Hmapinv2; auto.
      apply notin_neq in H11.
      apply remove_neq_preserves_notin in H12; auto.
      apply Hmapinv2; auto.

      unfold thread_state_map_inv' in *.
      uf. intros.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      intuition.
      apply binds_push_inv in H10; auto.
      intuition.
        subst. apply binds_push_eq; auto.
        apply binds_push_neq; auto.
        apply remove_neq_preserves_binds; auto.
        apply Hmapinv1' in H12; auto.
      apply binds_push_inv in H10; auto.
      intuition.
        subst. discriminate.
        apply notin_union. intuition.
        apply notin_neq; auto.
        apply remove_preserves_binds_notin in H12; auto.
        apply Hmapinv1' in H12; auto.
      apply notin_union in H10; auto.
      apply notin_union; auto.
      intuition.
        apply notin_neq in H11; auto.
        apply remove_neq_preserves_notin in H12; auto.
        apply Hmapinv1' in H12; auto.

      unfold thread_state_map_inv'' in *.
      uf. intros.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      intuition.
      apply binds_push_inv in H10; auto.
      intuition.
        subst. apply Hmapinv2'' in Hbinds0; auto.
        apply remove_preserves_binds_notin in H12; auto.
        apply Hmapinv2'' in H12; auto.
      apply notin_union.
      destruct (eq_nat_dec pid0 pid).
        subst. apply binds_in in H10.
        unfold "#" in Hnotin0.
        intuition.
        intuition.
        apply notin_neq; auto.
        apply remove_preserves_notin; auto.
        apply Hmapinv2'' in H10; auto.
    (* internal reply *)
    -- inversion H0; subst; simpl in *.
      inversion H3; subst; simpl in *.
      inversion H2; subst; simpl in *.
      inversion H4; subst; simpl in *.
      (* reply M2 *)
      --- inversion H5; subst; simpl in *.
        exists (
        (@mkTensorState liB liD
          (linked_lts (raw_compose L1 M1)) (linked_lts (raw_compose L2 M2))
          (mkSyncState (linked_lts (raw_compose L1 M1))
            (@mkRawComposedState liA liB
              L1 M1 
              (StateL1R s2)
              (StateM1R s2)
            )
            (PosComp1R s2)
          )
          (mkSyncState (linked_lts (raw_compose L2 M2))
            (@mkRawComposedState liC liD
              L2 M2 
              (st2'0.(LState))
              (st2'.(LState))
            )
            ((PosComp2R s2))
          )
        )
      ).
      simpl. intuition.
      destruct s2. simpl in *.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      destruct L2State; simpl in *.
      destruct LState; simpl in *.
      uf. subst.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      simpl.
      eapply tensor_step_L2_internal; eauto.
      unfold thread_state_map in *.
      simpl.
      eapply Hmap2 in Hbinds3; eauto.
      apply Hmap1; auto.
      econstructor.
      simpl.
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      unfold tensor_raw_compose_wf in *; simpl in *.
      uf. intuition.
      apply Hmap2 in Hbinds3; auto.
      simpl.
      eapply linked_step_L1_pop; eauto.
      simpl.
      eapply raw_composed_step_L1_pop; eauto.
      destruct L1State; simpl in *.
      destruct LState; simpl in *.
      reflexivity.
      unfold thread_state_map'.
      uf. intros.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      intuition.
      apply binds_push_inv in H10; auto.
        intuition.
        subst. 
        apply Hmap2 in Hbinds3; auto.
        apply remove_preserves_binds_notin in H13; auto.
        apply remove_neq_preserves_notin in H11; auto.
        apply Hmap2 in H13; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove pos2 pid)).
        apply ok_remove_notin; auto.
        apply binds_in in H10.
        unfold "#" in H11; intuition.
        apply remove_preserves_binds_notin in H10; auto.
        apply Hmap2 in H10; auto.
      apply notin_union in H12.
      intuition.
      apply notin_neq in H10.
      apply remove_neq_preserves_notin in H13; auto.
      apply remove_neq_preserves_notin in H11; auto.
      apply Hmap2; auto.
      unfold thread_state_map_inv.
      uf.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      intros.
      destruct (eq_nat_dec pid0 pid).
        subst. intuition.
        apply ok_remove_notin; auto.
        apply remove_neq_preserves_notin in H10; auto.
        intuition.
        apply Hmapinv1; auto.
        apply remove_preserves_notin; auto.
        apply Hmapinv1; auto.

      unfold thread_state_map_inv.
      uf.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      intros.
      apply notin_union in H10.
      intuition.
      apply notin_neq in H11.
      apply remove_neq_preserves_notin in H12; auto.
      apply Hmapinv2; auto.
      apply notin_union; auto.
      intuition.
      apply notin_neq in H11; auto.
      apply remove_neq_preserves_notin in H12; auto.
      apply remove_preserves_notin; auto.
      apply Hmapinv2; auto.

      unfold thread_state_map_inv' in *.
      uf. intros.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove pos2 pid)).
        apply ok_remove_notin; auto.
        apply binds_in in H10.
        unfold "#" in H11. intuition.
        apply binds_push_neq; auto.
        apply remove_neq_preserves_binds; auto.
        apply remove_preserves_binds_notin in H10; auto.
        apply Hmapinv2' in H10; auto.
      apply binds_push_inv in H10; auto.
      intuition.
        subst.
        apply ok_remove_notin; auto.
        apply remove_preserves_binds_notin in H12; auto.
        apply remove_preserves_notin; auto.
        apply Hmapinv2' in H12; auto.
      apply notin_union in H10; auto.
      intuition.
        apply notin_neq in H11; auto.
        apply remove_neq_preserves_notin in H12; auto.
        apply remove_preserves_notin; auto.
        apply Hmapinv2' in H12; auto.
      unfold thread_state_map_inv'' in *.
      uf. intros.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      intuition.
      apply notin_union.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmapinv2'' in H10.
        apply binds_in in Hbinds2.
        unfold "#" in H10; intuition.
        intuition.
        apply notin_neq; auto.
        apply remove_preserves_notin; auto.
        apply Hmapinv2'' in H10; auto.
      apply binds_push_inv in H10.
      intuition.
        subst. auto.
        apply remove_preserves_binds_notin in H12; auto.
        apply Hmapinv2'' in H12; auto.
      (* reply M1 *)
      --- inversion H5; subst; simpl in *.
        exists (
        (@mkTensorState liB liD
          (linked_lts (raw_compose L1 M1)) (linked_lts (raw_compose L2 M2))
          (mkSyncState (linked_lts (raw_compose L1 M1))
            (@mkRawComposedState liA liB
              L1 M1 
              (st1'0.(LState))
              (st1'.(LState))
            )
            (PosComp1R s2)
          )
          (mkSyncState (linked_lts (raw_compose L2 M2))
            (@mkRawComposedState liC liD
              L2 M2 
              (StateL2R s2)
              (StateM2R s2)
            )
            ((PosComp2R s2))
          )
        )
      ).
      simpl. intuition.
      destruct s2. simpl in *.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      destruct L1State; simpl in *.
      destruct LState; simpl in *.
      uf. subst.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      simpl.
      eapply tensor_step_L1_internal; eauto.
      unfold thread_state_map in *.
      simpl.
      eapply Hmap1 in Hbinds3; eauto.
      apply Hmap2; auto.
      econstructor.
      simpl.
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      unfold tensor_raw_compose_wf in *; simpl in *.
      uf. intuition.
      apply Hmap1 in Hbinds3; auto.
      simpl.
      eapply linked_step_L1_pop; eauto.
      simpl.
      eapply raw_composed_step_L1_pop; eauto.
      destruct L2State; simpl in *.
      destruct LState; simpl in *.
      reflexivity.
      unfold thread_state_map'.
      uf. intros.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      intuition.
      apply binds_push_inv in H10; auto.
        intuition.
        subst. 
        apply Hmap1 in Hbinds3; auto.
        apply remove_preserves_binds_notin in H13; auto.
        apply remove_neq_preserves_notin in H11; auto.
        apply Hmap1 in H13; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove pos2 pid)).
        apply ok_remove_notin; auto.
        apply binds_in in H10.
        unfold "#" in H11; intuition.
        apply remove_preserves_binds_notin in H10; auto.
        apply Hmap1 in H10; auto.
      apply notin_union in H12.
      intuition.
      apply notin_neq in H10.
      apply remove_neq_preserves_notin in H13; auto.
      apply remove_neq_preserves_notin in H11; auto.
      apply Hmap1; auto.
      unfold thread_state_map_inv.
      uf.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      intros.
      destruct (eq_nat_dec pid0 pid).
        subst. intuition.
        apply ok_remove_notin; auto.
        apply remove_neq_preserves_notin in H10; auto.
        intuition.
        apply remove_preserves_notin; auto.
        apply Hmapinv1; auto.
        apply Hmapinv1; auto.

      unfold thread_state_map_inv.
      uf.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      intros.
      apply notin_union in H10.
      intuition.
      apply notin_neq in H11.
      apply remove_neq_preserves_notin in H12; auto.
      apply notin_union; auto.
      intuition.
      apply notin_neq in H11; auto.
      apply remove_preserves_notin; auto.
      apply Hmapinv2; auto.
      apply notin_neq in H11.
      apply remove_neq_preserves_notin in H12; auto.
      apply Hmapinv2; auto.

      unfold thread_state_map_inv' in *.
      uf. intros.

      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove pos2 pid)).
        apply ok_remove_notin; auto.
        apply binds_in in H10.
        unfold "#" in H11; intuition.
        apply binds_push_neq; auto.
        apply remove_neq_preserves_binds; auto.
        apply remove_preserves_binds_notin in H10; auto.
        apply Hmapinv1' in H10; auto.
      apply binds_push_inv in H10.
      intuition.
        subst.
        apply ok_remove_notin; auto.
        apply remove_preserves_notin; auto.
        apply remove_preserves_binds_notin in H12; auto.
        apply Hmapinv1' in H12; auto.
      apply notin_union in H10.
      intuition.
      apply notin_neq in H11.
      apply remove_neq_preserves_notin in H12; auto.
      apply remove_preserves_notin; auto.
      apply Hmapinv1' in H12; auto.
      unfold thread_state_map_inv'' in *.
      uf. intros.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      intuition.
      apply binds_push_inv in H10.
      intuition.
        subst. auto.
        apply remove_preserves_binds_notin in H12; auto.
        apply Hmapinv2'' in H12; auto.
      apply notin_union.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmapinv2'' in H10.
        apply binds_in in Hbinds2.
        unfold "#" in H10; intuition.
        intuition.
        apply notin_neq; auto.
        apply remove_preserves_notin; auto.
        apply Hmapinv2'' in H10; auto.
Qed.

End DistributativeLaw.

Section HComp.

Context {liA liB : language_interface}.
Context {liC liD : language_interface}.
Variable L1: lts li_null liA.
Variable M1: lts liA liB.
Variable L1': lts li_null liB.
Variable L2: lts li_null liC.
Variable M2: lts liC liD.
Variable L2': lts li_null liD.

(* Notation " L ⊗-' L' " := (tensor L L') (at level 67).
Notation " M ⊗- M' " := (ImplTensor.tensor M M') (at level 67). *)

Theorem HComp:
  L1 ⊢ M1 ~: L1' ->
  L2 ⊢ M2 ~: L2' ->
  L1 ⊗-' L2 ⊢ M1 ⊗- M2 ~: (tensor L1' L2').
Proof.
  unfold veriobj.
  intros. intuition.
  apply tensor_consistency.
  apply impl_tensor_consistency.
  assert (HM1: refines (sync (linked_lts (raw_compose L1 M1))) (sync L1')).
  eapply trans_refinement; eauto.
  apply sync_raw_compose_refines_compose; auto.
  assert (HM2: refines (sync (linked_lts (raw_compose L2 M2))) (sync L2')).
  eapply trans_refinement; eauto.
  apply sync_raw_compose_refines_compose; auto.
  eapply tensor_preserves_refines in HM2.
  2 : { eapply HM1. }
  eapply trans_refinement; eauto.
  2 : { eapply tensor_consistency. }
  eapply trans_refinement; eauto.
  apply distributative_law.
Qed.

End HComp.