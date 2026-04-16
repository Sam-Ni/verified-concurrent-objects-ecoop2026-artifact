Require Import
  List
  Arith
  LibVar
  LTS
  Refinement
  SyncLTS
  RawTensor
  Tensor.

Import ListNotations.

Section test.
  
Context {liA liB : language_interface}.
Variable L1 : lts li_null liA.
Variable L2 : lts li_null liB.

Import LibEnv.

Definition sync_raw_tensor_wf (st : state (sync (RawTensor.tensor (sync L1) (sync L2)))) :=
  forall pid,
    (binds pid Run st.(LState).(RawTensor.L1State).(PidPos) ->
    pid # st.(LState).(RawTensor.L2State).(PidPos)) /\
    (binds pid Run st.(LState).(RawTensor.L2State).(PidPos) ->
    pid # st.(LState).(RawTensor.L1State).(PidPos)) /\
    (pid # st.(PidPos) -> 
      pid # st.(LState).(RawTensor.L1State).(PidPos) /\
      pid # st.(LState).(RawTensor.L2State).(PidPos)
    ).

Lemma sync_raw_tensor_wf_new: forall s,
  new_state
    (sync (RawTensor.tensor (sync L1) (sync L2)))
    s ->
  sync_raw_tensor_wf s.
Proof.
  intros.
  inversion H; subst.
  unfold sync_raw_tensor_wf.
  inversion H0; subst.
  inversion H2; subst.
  inversion H3; subst.
  rewrite H5. rewrite H7.
  intros. intuition.
  inversion H8.
  inversion H8.
  apply notin_empty.
  apply notin_empty.
Qed.


Lemma sync_raw_tensor_wf_inv: invariant_ind (sync (RawTensor.tensor (sync L1) (sync L2))) sync_raw_tensor_wf.
Proof.
  unfold invariant_ind. intuition.
  - apply sync_raw_tensor_wf_new; auto.
  - inversion H0; subst.
    simpl in *. clear H0.
    inversion H1; subst; simpl in *.
    -- clear H1. inversion H0; subst.
      simpl in *. clear H0.
      unfold sync_raw_tensor_wf in *.
      simpl in *. intros.
      specialize (H pid0). intuition.
    -- clear H1. inversion H0; subst.
      simpl in *. clear H0.
      unfold sync_raw_tensor_wf in *.
      simpl in *. intros.
      specialize (H pid0). intuition.
  - inversion H0; subst.
    simpl in *. clear H0.
    inversion H1; subst; simpl in *.
    -- clear H1. inversion H0; subst.
      simpl in *. clear H0.
      unfold sync_raw_tensor_wf in *.
      simpl in *. intros.
      destruct (eq_nat_dec pid0 pid).
      --- subst.
        specialize (H pid).
        intuition.
        apply binds_in in H2.
        unfold "#" in H3.
        intuition.
        apply notin_union in H2.
        intuition.
        apply notin_neq in H5.
        intuition.
      --- subst.
        specialize (H pid0).
        intuition.
        apply notin_union.
        intuition.
        apply notin_neq; auto.
        eapply binds_push_neq_inv in H2; eauto.
        apply notin_union in H2.
        intuition.
        apply notin_union.
        apply notin_union in H2.
        intuition.
    -- clear H1. inversion H0; subst.
      simpl in *. clear H0.
      unfold sync_raw_tensor_wf in *.
      simpl in *. intros.
      destruct (eq_nat_dec pid0 pid).
      --- subst.
        specialize (H pid).
        intuition.
        apply binds_in in H2.
        unfold "#" in H4.
        intuition.
        apply notin_union in H2.
        intuition.
        apply notin_neq in H5.
        intuition.
      --- subst.
        specialize (H pid0).
        intuition.
        apply binds_push_neq_inv in H2; auto.
        apply notin_union.
        intuition.
        apply notin_neq; auto.
        apply notin_union.
        apply notin_union in H2.
        intuition.
        apply notin_union in H2.
        intuition.
  - destruct act.
  - destruct act.
  - inversion H0; subst.
    simpl in *. clear H0.
    inversion H1; subst; simpl in *.
    -- clear H1. inversion H0; subst.
      simpl in *. clear H0.
      unfold sync_raw_tensor_wf in *.
      simpl in *. intros.
      destruct (eq_nat_dec pid0 pid).
      --- subst.
        specialize (H pid).
        intuition.
        apply ok_remove_notin; auto.
        apply ok_remove_notin; auto.
      --- subst.
        specialize (H pid0).
        intuition.
        apply remove_preserves_notin; auto.
        apply remove_preserves_binds_notin in H2; auto.
        apply remove_neq_preserves_notin in H2; auto.
        intuition.
        apply remove_neq_preserves_notin in H2; auto.
        intuition.
        apply remove_preserves_notin; auto.
    -- clear H1. inversion H0; subst.
      simpl in *. clear H0.
      unfold sync_raw_tensor_wf in *.
      simpl in *. intros.
      destruct (eq_nat_dec pid0 pid).
      --- subst.
        specialize (H pid).
        intuition.
        apply ok_remove_notin; auto.
        apply ok_remove_notin; auto.
      --- subst.
        specialize (H pid0).
        intuition.
        apply remove_preserves_binds_notin in H2; auto.
        apply remove_preserves_notin; auto.
        apply remove_preserves_notin; auto.
        apply remove_neq_preserves_notin in H2; auto.
        intuition.
        apply remove_neq_preserves_notin in H2; auto.
        intuition.
Qed.

Lemma sync_raw_tensor_sync_refines_tensor:
  refines (sync (RawTensor.tensor (sync L1) (sync L2)))
    (tensor L1 L2).
Proof.
  eapply forward_simulation_inv_ind
    with (f:=fun (x : state (sync (RawTensor.tensor (sync L1) (sync L2)))) y => 
      x.(LState).(RawTensor.L1State) = y.(L1State) /\
      x.(LState).(RawTensor.L2State) = y.(L2State)
      )
      (inv:=sync_raw_tensor_wf).
  unfold fsim_properties_inv_ind. intuition.
  - apply sync_raw_tensor_wf_inv.
  - inversion H; subst.
    destruct s1.
    destruct LState. simpl in *.
    exists (
      mkTensorState L1State L2State
    ).
    simpl. intuition.
  - intuition. destruct s2.
    destruct s1. destruct LState. simpl in *.
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst. clear H2.
    clear H1.
    inversion H0; subst; simpl in *.
    -- inversion H2; subst.
      clear H2.
      exists (
        mkTensorState st1 st2'
      ).
      simpl. intuition.
      eapply tensor_initial_state_L2; eauto.
      unfold sync_raw_tensor_wf in H.
      simpl in *.
      specialize (H pid); intuition.
    -- inversion H2; subst.
      clear H2.
      exists (
        mkTensorState st1' st2
      ).
      simpl. intuition.
      eapply tensor_initial_state_L1; eauto.
      unfold sync_raw_tensor_wf in H.
      simpl in *.
      specialize (H pid); intuition.
  - intuition. destruct s2.
    destruct s1. destruct LState. simpl in *.
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst. clear H2.
    clear H1.
    inversion H0; subst; simpl in *.
    -- inversion H2; subst.
      clear H2.
      exists (
        mkTensorState st1 st2'
      ).
      simpl. intuition.
      eapply tensor_final_state_L2; eauto.
      inversion H1; subst. assumption.
      inversion H1; subst.
      unfold sync_raw_tensor_wf in H.
      simpl in *.
      specialize (H pid); intuition.
    -- inversion H2; subst.
      clear H2.
      exists (
        mkTensorState st1' st2
      ).
      simpl. intuition.
      eapply tensor_final_state_L1; eauto.
      inversion H1; subst. assumption.
      inversion H1; subst.
      unfold sync_raw_tensor_wf in H.
      simpl in *.
      specialize (H pid); intuition.
  - intuition. destruct s2.
    destruct s1. destruct LState. simpl in *.
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst. clear H2.
    clear H1.
    inversion H0; subst; simpl in *.
    -- inversion H2; subst.
      clear H2.
      exists (
        mkTensorState st1 st2'
      ).
      simpl. intuition.
      eapply Step_Internal; eauto.
      eapply tensor_step_L2_internal; eauto.
      inversion H1; subst. assumption.
      inversion H1; subst.
      unfold sync_raw_tensor_wf in H.
      simpl in *.
      specialize (H pid); intuition.
      eapply Step_None; eauto.
    -- inversion H2; subst.
      clear H2.
      exists (
        mkTensorState st1' st2
      ).
      simpl. intuition.
      eapply Step_Internal; eauto.
      eapply tensor_step_L1_internal; eauto.
      inversion H1; subst. assumption.
      inversion H1; subst.
      unfold sync_raw_tensor_wf in H.
      simpl in *.
      specialize (H pid); intuition.
      eapply Step_None; eauto.
Qed.

End test.

Section test.
Context {liA liB : language_interface}.
Variable L1 : lts li_null liA.
Variable L2 : lts li_null liB.

Lemma tensor_raw_tensor:
  L1 ⊑' (sync L1) ->
  L2 ⊑' (sync L2) ->
  (sc (L1 ⊗' L2)) ⊑' (L1 ⊗-' L2).
Proof.
  intros.
  eapply trans_refinement.
  apply refines_sync_refines_sync_raw_tensor; auto.
  apply sync_raw_tensor_sync_refines_tensor.
Qed.

End test.