Require Import
  LTS
  Refinement
  SyncLTS
  Compose
  RawTensor
  ImplTensor
  Tensor
  HE
  ImplRawCompose
  ImplRefinement
  SyncCompLTS
  VE
  Link
  Register
  RegisterProp
  RegisterCounterImpl
  RegisterCounterImplProp
  Queue
  QueueProp
  Array
  Identity
  ArrayCorrectness
  ArraySC
  ArrayQueueImpl
  ArrayQueue
  AQC
  VerifiedConcurrentObject
  HComp
  VComp
  Linking
  Weaken
  ArrayCorrectness
  CounterCorrectness
  ArrayQueueImplSC
  ArrayQueueReduceSC.

Section test.

Context {liA liB liC liD : language_interface}.
Variable L1: lts li_null liA.
Variable L2: lts li_null liB.
Variable L3: lts li_null liC.
Variable M : lts (tensor_li liA (tensor_li liB liC)) liD.

Lemma reduce_sc:
  refines L2 (sync L2) ->
  refines L3 (sync L3) ->
  impl_refines M (sync M) ->

  refines
    (LTS.linked_lts
      (LTS.raw_compose
        (tensor
          L1
          (RawTensor.tensor L2 L3))
        M
    ))
    (LTS.linked_lts
      (compose
        (tensor
          L1
          (tensor L2 L3))
        M
    )).
Proof.
  intros.
  assert (Hl23: refines
                  (sync (RawTensor.tensor L2 L3))
                  (sync (tensor L2 L3))).
  eapply trans_refinement.
  apply tensor_raw_tensor; auto.
  apply tensor_consistency.
  eapply refines_tensor_refines_l with (L1:=L1) in Hl23.
  assert (Hl123: refines
                  (sync (tensor
                          L1
                          (RawTensor.tensor L2 L3)))
                  (sync (tensor L1 (tensor L2 L3)))
                  ).
  eapply trans_refinement.
  apply sync_refines_raw.
  eapply trans_refinement; eauto.
  apply tensor_consistency.
  eapply trans_refinement.
  2 : {
    eapply linked_refines_congruence; eauto.
  }
  eapply trans_refinement.
  eapply simple_raw_compose_consistency; eauto.
  apply tensor_consistency; auto.
  apply sync_raw_compose_refines_compose; auto.
  apply tensor_consistency.
Qed.
  
End test.

Section SyncIdentity.

Require Import
  List
  LibEnv
  ImplRefinement.
Import ListNotations.

Context {liA liB : language_interface}.
Variable L: lts liA liB.

Lemma sync_identity_impl:
  impl_refines (sync L) (sync (sync L)).
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
  - inversion H1; subst; simpl in *.
    exists (
      mkSyncState (sync L)
      (mkSyncState 
        L
        st' ((pid, Wait)::(remove pos pid))
      )
      ((pid, Wait)::(remove pos pid))
    ).
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_at_external_L with (pos:=PidPos); eauto.
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
        st' ((pid, Run)::(remove pos pid))
      )
      ((pid, Run)::(remove pos pid))
    ).
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_after_external_L with (pos:=PidPos); eauto.
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

Section test.

Require Import
  List
  Arith
  LibVar
  LibEnv
  LTS
  Refinement.
Import ListNotations.

Context {liA liB : language_interface}.
Context {liC liD : language_interface}.
Variable L1: lts li_null liA.
Variable M1: lts liA liB.
Variable L2: lts li_null liC.
Variable M2: lts liC liD.

Definition thread_state_map_inv (hl hm h : LibEnv.env Position) :=
  forall pid,
    (pid # h ->
    pid # hl /\ pid # hm) /\
    (binds pid Run hm \/ pid # hm ->
      pid # hl).

Lemma distributative_law':
  refines L1 (sync L1) ->
  refines L2 (sync L2) ->
  impl_refines M1 (sync M1) ->
  impl_refines M2 (sync M2) ->
  refines
    (tensor
      (LTS.linked_lts
        (LTS.raw_compose L1 M1))
      (LTS.linked_lts
        (LTS.raw_compose L2 M2))
    )
    (LTS.linked_lts
      (LTS.raw_compose
        (tensor L1 L2)
        (ImplTensor.tensor M1 M2))
    ).
Proof.
  intros.
  assert (HL1M1sc: refines 
    (sync (LTS.linked_lts (LTS.raw_compose L1 M1)))
    (sync (LTS.linked_lts (LTS.raw_compose (sync L1) (sync M1))))
    ).
  eapply trans_refinement.
  apply sync_refines_raw.
  eapply trans_refinement with (L':=(LTS.linked_lts (LTS.raw_compose (sync L1) (sync M1)))).
  eapply trans_refinement with (L':=(LTS.linked_lts (LTS.raw_compose (sync L1) M1))).
  eapply RawCompose.refines_composed_refines in H; eauto.
  eapply link_preserves_composed_refines in H; eauto.
  eapply ImplRefinement.impl_refines_composed_refines in H1; eauto.
  eapply link_preserves_composed_refines in H1; eauto.
  apply simple_raw_compose_consistency.
  apply sync_identity.
  apply sync_identity_impl.

  assert (HL2M2sc: refines 
    (sync (LTS.linked_lts (LTS.raw_compose L2 M2)))
    (sync (LTS.linked_lts (LTS.raw_compose (sync L2) (sync M2))))
    ).
  eapply trans_refinement.
  apply sync_refines_raw.
  eapply trans_refinement with (L':=(LTS.linked_lts (LTS.raw_compose (sync L2) (sync M2)))).
  eapply trans_refinement with (L':=(LTS.linked_lts (LTS.raw_compose (sync L2) M2))).
  eapply RawCompose.refines_composed_refines in H0; eauto.
  eapply link_preserves_composed_refines in H0; eauto.
  eapply ImplRefinement.impl_refines_composed_refines in H2; eauto.
  eapply link_preserves_composed_refines in H2; eauto.
  apply simple_raw_compose_consistency.
  apply sync_identity.
  apply sync_identity_impl.

  eapply tensor_preserves_refines in HL2M2sc.
  2 : { eapply HL1M1sc. }
  eapply trans_refinement; eauto.
  clear H H0 H1 H2 HL1M1sc HL2M2sc.
  eapply forward_simulation_inv_ind
    with (f:=fun (x : state (tensor (LTS.linked_lts (LTS.raw_compose (sync L1) (sync M1)))
        (LTS.linked_lts (LTS.raw_compose (sync L2) (sync M2))))) 
        (y : state (LTS.linked_lts
        (LTS.raw_compose (tensor L1 L2) (ImplTensor.tensor M1 M2)))) =>
        x.(Tensor.L1State).(SyncLTS.LState).(LTS.RawL1State) = y.(LTS.RawL1State).(Tensor.L1State) /\
        x.(Tensor.L1State).(SyncLTS.LState).(LTS.RawL2State) = y.(LTS.RawL2State).(ImplTensor.L1State) /\
        x.(Tensor.L2State).(SyncLTS.LState).(LTS.RawL1State) = y.(LTS.RawL1State).(Tensor.L2State) /\
        x.(Tensor.L2State).(SyncLTS.LState).(LTS.RawL2State) = y.(LTS.RawL2State).(ImplTensor.L2State) /\
        thread_state_map_inv
          x.(Tensor.L1State).(SyncLTS.LState).(LTS.RawL1State).(PidPos)
          x.(Tensor.L1State).(SyncLTS.LState).(LTS.RawL2State).(PidPos)
          x.(Tensor.L1State).(PidPos) /\
        thread_state_map_inv
          x.(Tensor.L2State).(SyncLTS.LState).(LTS.RawL1State).(PidPos)
          x.(Tensor.L2State).(SyncLTS.LState).(LTS.RawL2State).(PidPos)
          x.(Tensor.L2State).(PidPos)
      (* x = y.(LState) /\
      thread_state_map y.(LState).(pc) y.(PidPos) /\
      sync_array_queue_impl_wf y *)
      (* queue_wf x.(requests) x.(responses) *)
      )
      (inv:=fun x => True).
    
  unfold fsim_properties_inv_ind. intuition.
  - unfold invariant_ind. intuition.
  - inversion H; subst; simpl in *. 
    inversion H0; subst; simpl in *. 
    inversion H1; subst; simpl in *. 
    inversion H2; subst; simpl in *. 
    inversion H4; subst; simpl in *.
    exists (@LTS.mkRawComposedState (tensor_li liA liC) (tensor_li liB liD)
      (tensor L1 L2) (ImplTensor.tensor M1 M2)
      (@mkTensorState liA liC L1 L2
        (LTS.RawL1State (LState (L1State s1)))
        (LTS.RawL1State (LState (L2State s1))))
      (@ImplTensor.mkTensorState liA liB liC liD
        M1 M2
        (LTS.RawL2State (LState (L1State s1)))
        (LTS.RawL2State (LState (L2State s1))))
    ).
    simpl. intuition.
    unfold raw_composed_new_state.
    simpl.
    unfold tensor_new_state.
    simpl. intuition.
    unfold ImplTensor.tensor_new_state.
    simpl. intuition.
    rewrite H3.
    inversion H6; subst; simpl in *.
    rewrite H11.
    inversion H7; subst; simpl in *.
    rewrite H13.
    unfold thread_state_map_inv.
    intuition. inversion H15.
    rewrite H5.
    inversion H8; subst; simpl in *.
    rewrite H11.
    inversion H9; subst; simpl in *.
    rewrite H13.
    unfold thread_state_map_inv.
    intuition. inversion H15.
  - rename H2 into HL1.
    rename H0 into HM1.
    rename H3 into HL2.
    rename H4 into HM2.
    rename H5 into Hmap1.
    rename H7 into Hmap2.
    exists (@LTS.mkRawComposedState (tensor_li liA liC) (tensor_li liB liD)
      (tensor L1 L2) (ImplTensor.tensor M1 M2)
      (@mkTensorState liA liC L1 L2
        (LTS.RawL1State (LState (L1State s1')))
        (LTS.RawL1State (LState (L2State s1'))))
      (@ImplTensor.mkTensorState liA liB liC liD
        M1 M2
        (LTS.RawL2State (LState (L1State s1')))
        (LTS.RawL2State (LState (L2State s1'))))
    ).
    simpl. intuition.
    inversion H1; subst; simpl in *.
    (* (sync L2) <| (sync M2) initial_state *)
      inversion H0; subst; simpl in *.
      inversion H2; subst; simpl in *.
      inversion H3; subst; simpl in *.
      destruct s2; simpl in *.
      destruct RawL1State; simpl in *.
      destruct RawL2State; simpl in *.
      subst.
      eapply raw_composed_initial_state_L2; eauto.
      simpl.
      eapply ImplTensor.tensor_initial_state_M2; eauto.
      apply Hmap1; auto.
    (* (sync L1) <| (sync M1) initial_state *)
      inversion H0; subst; simpl in *.
      inversion H2; subst; simpl in *.
      inversion H3; subst; simpl in *.
      destruct s2; simpl in *.
      destruct RawL1State; simpl in *.
      destruct RawL2State; simpl in *.
      subst.
      eapply raw_composed_initial_state_L2; eauto.
      simpl.
      eapply ImplTensor.tensor_initial_state_M1; eauto.
      apply Hmap2; auto.
    unfold thread_state_map_inv.
    inversion H1; subst; simpl in *.
    (* (sync L2) <| (sync M2) initial_state *)
      apply Hmap1; auto.
    (* (sync L1) <| (sync M1) initial_state *)
      inversion H0; subst; simpl in *.
      inversion H2; subst; simpl in *.
      inversion H3; subst; simpl in *.
      intuition.
      apply notin_union in H6.
      intuition.
      apply Hmap1 in H8; auto. intuition.
      apply notin_union.
      apply notin_union in H6; intuition.
      subst.
      apply Hmap1 in H8; auto.
      rewrite H5 in H8.
      simpl in H8.
      intuition.
      apply binds_push_inv in H7.
      intuition.
        subst.
        apply Hmap1; auto.
        right.
        rewrite H5; simpl; auto.
        apply Hmap1; auto.
        rewrite H5; simpl; auto.
      apply notin_union in H7.
      intuition.
      apply Hmap1; auto.
      right.
      rewrite H5; simpl; auto.

    unfold thread_state_map_inv.
    inversion H1; subst; simpl in *.
    (* (sync L2) <| (sync M2) initial_state *)
      inversion H0; subst; simpl in *.
      inversion H2; subst; simpl in *.
      inversion H3; subst; simpl in *.
      intuition.
      apply notin_union in H6.
      intuition.
      apply Hmap2 in H8; auto. intuition.
      apply notin_union.
      apply notin_union in H6; intuition.
      subst.
      apply Hmap2 in H8; auto.
      rewrite H5 in H8.
      simpl in H8.
      intuition.
      apply binds_push_inv in H7.
      intuition.
        subst.
        apply Hmap2; auto.
        right.
        rewrite H5; simpl; auto.
        apply Hmap2; auto.
        rewrite H5; simpl; auto.
      apply notin_union in H7.
      intuition.
      apply Hmap2; auto.
      right.
      rewrite H5; simpl; auto.
    (* (sync L1) <| (sync M1) initial_state *)
      apply Hmap2; auto.
  - rename H2 into HL1.
    rename H0 into HM1.
    rename H3 into HL2.
    rename H4 into HM2.
    rename H5 into Hmap1.
    rename H7 into Hmap2.
    exists (@LTS.mkRawComposedState (tensor_li liA liC) (tensor_li liB liD)
      (tensor L1 L2) (ImplTensor.tensor M1 M2)
      (@mkTensorState liA liC L1 L2
        (LTS.RawL1State (LState (L1State s1')))
        (LTS.RawL1State (LState (L2State s1'))))
      (@ImplTensor.mkTensorState liA liB liC liD
        M1 M2
        (LTS.RawL2State (LState (L1State s1')))
        (LTS.RawL2State (LState (L2State s1'))))
    ).
    simpl. intuition.
    inversion H1; subst; simpl in *.
    (* (sync L2) <| (sync M2) final_state *)
      inversion H0; subst; simpl in *.
      inversion H2; subst; simpl in *.
      inversion H3; subst; simpl in *.
      destruct s2; simpl in *.
      destruct RawL1State; simpl in *.
      destruct RawL2State; simpl in *.
      subst.
      eapply raw_composed_final_state_L2; eauto.
      simpl.
      eapply ImplTensor.tensor_final_state_M2; eauto.
      simpl. auto.
      apply Hmap1; auto.
    (* (sync L1) <| (sync M1) initial_state *)
      inversion H0; subst; simpl in *.
      inversion H2; subst; simpl in *.
      inversion H3; subst; simpl in *.
      destruct s2; simpl in *.
      destruct RawL1State; simpl in *.
      destruct RawL2State; simpl in *.
      subst.
      eapply raw_composed_final_state_L2; eauto.
      simpl.
      eapply ImplTensor.tensor_final_state_M1; eauto.
      simpl. auto.
      apply Hmap2; auto.
    unfold thread_state_map_inv.
    inversion H1; subst; simpl in *.
    (* (sync L2) <| (sync M2) initial_state *)
      apply Hmap1; auto.
    (* (sync L1) <| (sync M1) initial_state *)
      inversion H0; subst; simpl in *.
      inversion H2; subst; simpl in *.
      inversion H3; subst; simpl in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmap1; auto.
        left.
        rewrite H5; simpl; auto.
        apply remove_neq_preserves_notin in H6; auto.
        apply Hmap1 in H6; auto.
        rewrite H5 in H6; simpl; auto.
        simpl in *; intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply ok_remove_notin; auto.
        apply remove_neq_preserves_notin in H6; auto.
        apply remove_preserves_notin; auto.
        apply Hmap1 in H6; auto.
        rewrite H5 in H6; simpl; auto.
        simpl in *; intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove pos0 pid)).
        apply ok_remove_notin; auto.
        apply binds_in in H7.
        unfold "#" in H6; intuition.
        apply remove_preserves_binds_notin in H7; auto.
        apply Hmap1; auto.
        left.
        rewrite H5; simpl; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmap1; auto.
        left.
        rewrite H5; simpl; auto.
        apply remove_neq_preserves_notin in H7; auto.
        apply Hmap1; auto.
        right.
        rewrite H5; simpl; auto.

    unfold thread_state_map_inv.
    inversion H1; subst; simpl in *.
    (* (sync L2) <| (sync M2) initial_state *)
      inversion H0; subst; simpl in *.
      inversion H2; subst; simpl in *.
      inversion H3; subst; simpl in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmap2; auto.
        left.
        rewrite H5; simpl; auto.
        apply remove_neq_preserves_notin in H6; auto.
        apply Hmap2 in H6; auto.
        rewrite H5 in H6; simpl; auto.
        simpl in *; intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply ok_remove_notin; auto.
        apply remove_neq_preserves_notin in H6; auto.
        apply remove_preserves_notin; auto.
        apply Hmap2 in H6; auto.
        rewrite H5 in H6; simpl; auto.
        simpl in *; intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove pos0 pid)).
        apply ok_remove_notin; auto.
        apply binds_in in H7.
        unfold "#" in H6; intuition.
        apply remove_preserves_binds_notin in H7; auto.
        apply Hmap2; auto.
        left.
        rewrite H5; simpl; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmap2; auto.
        left.
        rewrite H5; simpl; auto.
        apply remove_neq_preserves_notin in H7; auto.
        apply Hmap2; auto.
        right.
        rewrite H5; simpl; auto.
    (* (sync L1) <| (sync M1) initial_state *)
      apply Hmap2; auto.
  - rename H2 into HL1.
    rename H0 into HM1.
    rename H3 into HL2.
    rename H4 into HM2.
    rename H5 into Hmap1.
    rename H7 into Hmap2.
    exists (@LTS.mkRawComposedState (tensor_li liA liC) (tensor_li liB liD)
      (tensor L1 L2) (ImplTensor.tensor M1 M2)
      (@mkTensorState liA liC L1 L2
        (LTS.RawL1State (LState (L1State s1')))
        (LTS.RawL1State (LState (L2State s1'))))
      (@ImplTensor.mkTensorState liA liB liC liD
        M1 M2
        (LTS.RawL2State (LState (L1State s1')))
        (LTS.RawL2State (LState (L2State s1'))))
    ).
    simpl. intuition.
    inversion H1; subst; simpl in *.
    (* (sync L2) <| (sync M2) step *)
      inversion H0; subst; simpl in *.
      inversion H2; subst; simpl in *.
      (* M2 step *)
        inversion H3; subst; simpl in *.
        inversion H4; subst; simpl in *.
        destruct s2; simpl in *.
        destruct RawL1State; simpl in *.
        destruct RawL2State; simpl in *.
        subst.
        eapply Step_Internal; eauto.
        2 : { eapply Step_None; eauto. }
        simpl.
        eapply linked_step_int_L2; eauto.
        simpl.
        eapply raw_composed_step_L2_internal; eauto.
        simpl.
        eapply ImplTensor.tensor_step_LM_internal; eauto.
        simpl. auto.
        apply Hmap1; auto.
      (* L2 step *)
        inversion H3; subst; simpl in *.
        inversion H4; subst; simpl in *.
        destruct s2; simpl in *.
        destruct RawL1State; simpl in *.
        destruct RawL2State; simpl in *.
        subst.
        eapply Step_Internal; eauto.
        2 : { eapply Step_None; eauto. }
        simpl.
        eapply linked_step_int_L1; eauto.
        simpl.
        eapply raw_composed_step_L1_internal; eauto.
        simpl.
        eapply tensor_step_L2_internal; eauto.
        simpl. auto.
        apply Hmap1 in Hnotin; intuition.
      (* M2 query *)
        inversion H3; subst; simpl in *.
        inversion H4; subst; simpl in *.
        inversion H6; subst; simpl in *.
        destruct s2; simpl in *.
        destruct RawL1State; simpl in *.
        destruct RawL2State; simpl in *.
        subst.
        eapply Step_Internal; eauto.
        2 : { eapply Step_None; eauto. }
        simpl.
        eapply linked_step_L2_push; eauto.
        simpl.
        eapply raw_composed_step_L2_push; eauto.
        simpl. 
        eapply ImplTensor.tensor_at_external_M2; eauto.
        simpl. auto.
        apply Hmap1; auto.
        simpl.
        eapply tensor_initial_state_L2; eauto.
        apply Hmap1 in Hnotin; intuition.
      (* L2 reply *)
        inversion H3; subst; simpl in *.
        inversion H5; subst; simpl in *.
        inversion H4; subst; simpl in *.
        destruct s2; simpl in *.
        destruct RawL1State; simpl in *.
        destruct RawL2State; simpl in *.
        subst.
        eapply Step_Internal; eauto.
        2 : { eapply Step_None; eauto. }
        simpl.
        eapply linked_step_L1_pop; eauto.
        simpl.
        eapply raw_composed_step_L1_pop; eauto.
        simpl. 
        eapply tensor_final_state_L2; eauto.
        simpl. auto.
        apply Hmap1 in Hnotin; intuition.
        simpl.
        eapply ImplTensor.tensor_after_external_M2; eauto.
        simpl. auto.
        apply Hmap1; auto.
    (* (sync L1) <| (sync M1) step *)
      inversion H0; subst; simpl in *.
      inversion H2; subst; simpl in *.
      (* M1 step *)
        inversion H3; subst; simpl in *.
        inversion H4; subst; simpl in *.
        destruct s2; simpl in *.
        destruct RawL1State; simpl in *.
        destruct RawL2State; simpl in *.
        subst.
        eapply Step_Internal; eauto.
        2 : { eapply Step_None; eauto. }
        simpl.
        eapply linked_step_int_L2; eauto.
        simpl.
        eapply raw_composed_step_L2_internal; eauto.
        simpl.
        eapply ImplTensor.tensor_step_M1_internal; eauto.
        simpl. auto.
        apply Hmap2; auto.
      (* L1 step *)
        inversion H3; subst; simpl in *.
        inversion H4; subst; simpl in *.
        destruct s2; simpl in *.
        destruct RawL1State; simpl in *.
        destruct RawL2State; simpl in *.
        subst.
        eapply Step_Internal; eauto.
        2 : { eapply Step_None; eauto. }
        simpl.
        eapply linked_step_int_L1; eauto.
        simpl.
        eapply raw_composed_step_L1_internal; eauto.
        simpl.
        eapply tensor_step_L1_internal; eauto.
        simpl. auto.
        apply Hmap2 in Hnotin; intuition.
      (* M1 query *)
        inversion H3; subst; simpl in *.
        inversion H4; subst; simpl in *.
        inversion H6; subst; simpl in *.
        destruct s2; simpl in *.
        destruct RawL1State; simpl in *.
        destruct RawL2State; simpl in *.
        subst.
        eapply Step_Internal; eauto.
        2 : { eapply Step_None; eauto. }
        simpl.
        eapply linked_step_L2_push; eauto.
        simpl.
        eapply raw_composed_step_L2_push; eauto.
        simpl. 
        eapply ImplTensor.tensor_at_external_M1; eauto.
        simpl. auto.
        apply Hmap2; auto.
        simpl.
        eapply tensor_initial_state_L1; eauto.
        apply Hmap2 in Hnotin; intuition.
      (* L1 reply *)
        inversion H3; subst; simpl in *.
        inversion H5; subst; simpl in *.
        inversion H4; subst; simpl in *.
        destruct s2; simpl in *.
        destruct RawL1State; simpl in *.
        destruct RawL2State; simpl in *.
        subst.
        eapply Step_Internal; eauto.
        2 : { eapply Step_None; eauto. }
        simpl.
        eapply linked_step_L1_pop; eauto.
        simpl.
        eapply raw_composed_step_L1_pop; eauto.
        simpl. 
        eapply tensor_final_state_L1; eauto.
        simpl. auto.
        apply Hmap2 in Hnotin; intuition.
        simpl.
        eapply ImplTensor.tensor_after_external_M1; eauto.
        simpl. auto.
        apply Hmap2; auto.
    unfold thread_state_map_inv.
    inversion H1; subst; simpl in *.
    (* (sync L2) <| (sync M2) step *)
      inversion H0; subst; simpl in *.
      intuition.
    (* (sync L1) <| (sync M1) step *)
      inversion H0; subst; simpl in *.
      inversion H2; subst; simpl in *.
      (* M1 step *)
        inversion H3; subst; simpl in *.
        inversion H4; subst; simpl in *.
        intuition.
        apply Hmap1 in H7; intuition.
        apply Hmap1 in H7; intuition.
        rewrite H6 in H9; intuition.
        apply Hmap1; intuition.
        rewrite H6; simpl; intuition.
        apply Hmap1; intuition.
        rewrite H6; simpl; intuition.
      (* L1 step *)
        inversion H3; subst; simpl in *.
        inversion H4; subst; simpl in *.
        intuition.
        apply Hmap1 in H7; intuition.
        rewrite H6 in H8; intuition.
        apply Hmap1 in H7; intuition.
        rewrite H6 in Hmap1.
        simpl in *.
        eapply Hmap1; eauto.
        rewrite H6 in Hmap1.
        simpl in *.
        eapply Hmap1; eauto.
      (* M1 query *)
        inversion H3; subst; simpl in *.
        inversion H4; subst; simpl in *.
        inversion H6; subst; simpl in *.
        rewrite H9 in Hmap1.
        simpl in *.
        intuition.
        apply notin_union.
        destruct (eq_nat_dec pid0 pid).
          subst.
          apply binds_in in Hbinds0.
          unfold "#" in H10; intuition.
        intuition.
          apply notin_neq; auto.
          apply Hmap1 in H10; intuition.
        apply notin_union.
        destruct (eq_nat_dec pid0 pid).
          subst.
          apply binds_in in Hbinds0.
          unfold "#" in H10; intuition.
        intuition.
          apply notin_neq; auto.
          apply remove_preserves_notin; auto.
          apply Hmap1 in H10; intuition.
          rewrite H7 in H12.
          simpl in *; intuition.
        apply binds_push_inv in H11; auto.
        intuition.
          subst. discriminate.
          apply remove_preserves_binds_notin in H12; auto.
          apply notin_union.
          intuition.
          apply notin_neq; auto.
          rewrite H7 in Hmap1; simpl in *.
          apply Hmap1; auto.
        apply notin_union in H11.
        apply notin_union.
        intuition.
        apply notin_neq in H10.
        apply remove_neq_preserves_notin in H12; auto.
        rewrite H7 in Hmap1; simpl in *.
        apply Hmap1; auto.
      (* L1 reply *)
        inversion H3; subst; simpl in *.
        inversion H5; subst; simpl in *.
        inversion H4; subst; simpl in *.
        rewrite H9 in Hmap1.
        rewrite H7 in Hmap1.
        simpl in *.
        intuition.
        apply remove_preserves_notin; auto.
        apply Hmap1 in H10; intuition.
        apply notin_union.
        destruct (eq_nat_dec pid0 pid).
          subst.
          apply binds_in in Hbinds0.
          unfold "#" in H10; intuition.
          intuition.
          apply notin_neq; auto.
          apply remove_preserves_notin; auto.
          apply Hmap1 in H10; intuition.
        apply binds_push_inv in H11.
        intuition.
          subst.
          apply ok_remove_notin; auto.
          apply remove_preserves_binds_notin in H12; auto.
          apply remove_preserves_notin; auto.
          apply Hmap1; auto.
        apply notin_union in H11.
        intuition.
        apply notin_neq in H10.
        apply remove_neq_preserves_notin in H12; auto.
        apply remove_preserves_notin; auto.
        apply Hmap1; auto.

    unfold thread_state_map_inv.
    inversion H1; subst; simpl in *.
    (* (sync L2) <| (sync M2) step *)
      inversion H0; subst; simpl in *.
      inversion H2; subst; simpl in *.
      (* M2 step *)
        inversion H3; subst; simpl in *.
        inversion H4; subst; simpl in *.
        intuition.
        apply Hmap2 in H7; intuition.
        apply Hmap2 in H7; intuition.
        rewrite H6 in H9; intuition.
        apply Hmap2; intuition.
        rewrite H6; simpl; intuition.
        apply Hmap2; intuition.
        rewrite H6; simpl; intuition.
      (* L2 step *)
        inversion H3; subst; simpl in *.
        inversion H4; subst; simpl in *.
        intuition.
        apply Hmap2 in H7; intuition.
        rewrite H6 in H8; intuition.
        apply Hmap2 in H7; intuition.
        rewrite H6 in Hmap2.
        simpl in *.
        eapply Hmap2; eauto.
        rewrite H6 in Hmap2.
        simpl in *.
        eapply Hmap2; eauto.
      (* M2 query *)
        inversion H3; subst; simpl in *.
        inversion H4; subst; simpl in *.
        inversion H6; subst; simpl in *.
        rewrite H9 in Hmap2.
        simpl in *.
        intuition.
        apply notin_union.
        destruct (eq_nat_dec pid0 pid).
          subst.
          apply binds_in in Hbinds0.
          unfold "#" in H10; intuition.
        intuition.
          apply notin_neq; auto.
          apply Hmap2 in H10; intuition.
        apply notin_union.
        destruct (eq_nat_dec pid0 pid).
          subst.
          apply binds_in in Hbinds0.
          unfold "#" in H10; intuition.
        intuition.
          apply notin_neq; auto.
          apply remove_preserves_notin; auto.
          apply Hmap2 in H10; intuition.
          rewrite H7 in H12.
          simpl in *; intuition.
        apply binds_push_inv in H11; auto.
        intuition.
          subst. discriminate.
          apply remove_preserves_binds_notin in H12; auto.
          apply notin_union.
          intuition.
          apply notin_neq; auto.
          rewrite H7 in Hmap2; simpl in *.
          apply Hmap2; auto.
        apply notin_union in H11.
        apply notin_union.
        intuition.
        apply notin_neq in H10.
        apply remove_neq_preserves_notin in H12; auto.
        rewrite H7 in Hmap2; simpl in *.
        apply Hmap2; auto.
      (* L2 reply *)
        inversion H3; subst; simpl in *.
        inversion H5; subst; simpl in *.
        inversion H4; subst; simpl in *.
        rewrite H9 in Hmap2.
        rewrite H7 in Hmap2.
        simpl in *.
        intuition.
        apply remove_preserves_notin; auto.
        apply Hmap2 in H10; intuition.
        apply notin_union.
        destruct (eq_nat_dec pid0 pid).
          subst.
          apply binds_in in Hbinds0.
          unfold "#" in H10; intuition.
          intuition.
          apply notin_neq; auto.
          apply remove_preserves_notin; auto.
          apply Hmap2 in H10; intuition.
        apply binds_push_inv in H11.
        intuition.
          subst.
          apply ok_remove_notin; auto.
          apply remove_preserves_binds_notin in H12; auto.
          apply remove_preserves_notin; auto.
          apply Hmap2; auto.
        apply notin_union in H11.
        intuition.
        apply notin_neq in H10.
        apply remove_neq_preserves_notin in H12; auto.
        apply remove_preserves_notin; auto.
        apply Hmap2; auto.
    (* (sync L1) <| (sync M1) step *)
      inversion H0; subst; simpl in *.
      intuition.
Qed.
  
End test.

Section Correctness.

Variable N: nat.
Hypothesis H : 0 < N.

Lemma verified_array_queue:
  (array_front_rear N) ⊢ (array_queue_impl N) ~: (queue N).
Proof.
  unfold veriobj.
  intuition.
  unfold array_front_rear.
  apply tensor_consistency; auto.
  apply array_queue_impl_is_sc.
  eapply trans_refinement.
  eapply array_queue_correct; eauto.
  apply queue_is_sc; auto.
Qed.

(* Notation " L ⊗-' L' " := (tensor L L') (at level 67). *)
(* Notation " M ⊗- M' " := (ImplTensor.tensor M M') (at level 67). *)
(* Notation " L ⊗' L' " := (RawTensor.tensor L L') (at level 67). *)
(* Notation " M ◁ M' " := (linked_lts (ImplRawCompose.raw_compose M M')) (at level 67). *)
(* Notation " L ◁' M " := (LTS.linked_lts (LTS.raw_compose L M)) (at level 67). *)
(* Notation " L ⊑' L' " := (refines L L') (at level 67). *)

Lemma verified_counter_counter:
  Register ⊗-' Register ⊢
  register_counter_impl ⊗- register_counter_impl
   ~: (front_rear).
Proof.
  apply HComp.
  apply verified_counter.
  apply verified_counter.
Qed.

Lemma verified_array_counter_counter: 
  (array N) ⊗-' (tensor Register Register) ⊢
  (identity li_array ⊗-
    (register_counter_impl ⊗- register_counter_impl))
  ~: (array_front_rear N).
Proof.
  apply HComp.
  apply verified_array.
  apply verified_counter_counter.
Qed.

Theorem verified_whole_queue:
  ((array N) ⊗-' (Register ⊗-' Register)) ⊢
  ((identity li_array) ⊗- (register_counter_impl ⊗- register_counter_impl)) ◁ (array_queue_impl N)
  ~: (queue N).
Proof.
  eapply VComp.
  eapply verified_array_counter_counter.
  apply verified_array_queue.
Qed.

Lemma verified_queue_link:
  ((array N) ⊗-' (tensor Register Register)) ◁'
    ((identity li_array) ⊗-
      (register_counter_impl ⊗- register_counter_impl)) ⊢
  (array_queue_impl N)
  ~: (queue N).
Proof.
  apply Link.
  apply verified_whole_queue.
  apply impl_tensor_consistency.
  apply array_queue_impl_is_sc.
Qed.

Lemma verified_queue_link_and_weaken:
  (array N) ⊗-'
    (tensor 
      (Register ◁' register_counter_impl)
      (Register ◁' register_counter_impl))
  ⊢
  (array_queue_impl N)
  ~: (queue N).
Proof.
  eapply Weaken.
  apply verified_queue_link.
  2 : {
    apply tensor_consistency.
  }
  eapply trans_refinement.
  2 : {
    eapply distributative_law'.
    apply array_is_sc.
    apply tensor_consistency.
    apply identity_is_sc.
    apply impl_tensor_consistency.
  }
  eapply tensor_preserves_refines.
  2 : {
    eapply trans_refinement.
    apply sync_refines_raw.
    eapply trans_refinement.
    2 : {
      apply simple_raw_compose_consistency.
      apply tensor_consistency.
      apply impl_tensor_consistency.
    }
    eapply distributative_law'.
    apply register_sync.
    apply register_sync.
    apply register_counter_impl_sync.
    apply register_counter_impl_sync.
  }
  eapply trans_refinement; eauto.
  apply sync_refines_raw.
  eapply trans_refinement; eauto.
  2: {
    apply simple_raw_compose_consistency.
    apply array_is_sc.
    apply identity_is_sc.
  }
  apply array_refines_array_identity.
Qed.

Lemma whole_queue_correctness: 
  (array N) ⊗'
        ((Register ◁' register_counter_impl) ⊗'
        (Register ◁' register_counter_impl))
      ◁' (array_queue_impl N)
    ⊑' (queue N).
Proof.
  generalize verified_queue_link_and_weaken; intro.
  unfold veriobj in H0.
  intuition.
  clear H1 H0.
  eapply trans_refinement.
  2 : {
    apply sync_refines_raw.
  }
  eapply trans_refinement; eauto.
  clear H3.
  eapply trans_refinement.
  2 : {
    apply reduce_sc; auto.
    apply simple_raw_compose_consistency.
    apply register_sync.
    apply register_counter_impl_sync.
    apply simple_raw_compose_consistency.
    apply register_sync.
    apply register_counter_impl_sync.
    apply array_queue_impl_is_sc.
  }
  apply remove_sc.
Qed.

End Correctness.
