Require Import
  List
  Arith
  LibVar
  LibEnv
  LTS
  Refinement
  ImplRefinement
  SyncLTS
  VE
  Link
  RawCompose
  ImplRawCompose
  VerifiedConcurrentObject
  HComp.
Import ListNotations.

Section ImplRefinement.

Context {liA liB: language_interface}.
Variable M1: lts liA liB.
Variable M2: lts liA liB.
Variable M3: lts liA liB.

Lemma impl_refines_trans:
  impl_refines M1 M2 ->
  impl_refines M2 M3 ->
  impl_refines M1 M3.
Proof.
  unfold impl_refines; intros.
  apply H in H1. intuition.
Qed.

End ImplRefinement.

Section RawComposeConsistency.

Context {liA liB liC: language_interface}.
Variable M1: lts liA liB.
Variable M2: lts liB liC.

Definition thread_state_map (h1 h2 h : env Position) :=
  forall pid p,
  ((binds pid p h1) ->
  binds pid p h) /\
  (pid # h1 /\ 
    binds pid Run h2 -> binds pid Run h) /\
  (pid # h2 -> pid # h).

Definition thread_state_map_inv (h1 h2 h : env Position) :=
  forall pid,
  (pid # h -> (pid # h1 /\ pid # h2)).

Definition thread_state_mutual (h1 h2 : env Position) :=
  forall pid,
  (binds pid Run h2 -> pid # h1).

Definition sync_raw_compose_wf (y : state (sync (linked_lts (raw_compose M1 M2)))) :=
  ok (y.(PidPos)).

Lemma raw_compose_sync_refine_sync_raw_compose:
  impl_refines
  (linked_lts
     (raw_compose (sync M1) (sync M2)))
  (sync (linked_lts (raw_compose M1 M2))).
Proof.
  eapply forward_simulation_inv_ind
    with (f:=fun (x : state (linked_lts
     (raw_compose (sync M1) (sync M2)))) (y : state (sync (linked_lts (raw_compose M1 M2)))) =>
      x.(RawL1State).(LState) = y.(LState).(RawL1State) /\
      x.(RawL2State).(LState) = y.(LState).(RawL2State) /\
      thread_state_map x.(RawL1State).(PidPos) x.(RawL2State).(PidPos) y.(PidPos) /\
      sync_raw_compose_wf y /\
      thread_state_map_inv x.(RawL1State).(PidPos) x.(RawL2State).(PidPos) y.(PidPos) /\
      thread_state_mutual x.(RawL1State).(PidPos) x.(RawL2State).(PidPos)

      (* x.(L1State).(LState) = y.(LState).(RawTensor.L1State) /\
      x.(L2State).(LState) = y.(LState).(RawTensor.L2State) /\
      thread_state_map (x.(L1State).(PidPos)) (x.(L2State).(PidPos)) y.(PidPos) /\
      syn_raw_tensor_wf y *)
      )
      (inv:=fun x => True).
  unfold fsim_properties_inv_ind. intuition.
  - unfold invariant_ind. intuition.
  - inversion H; subst; simpl in *.
    inversion H0; subst; simpl in *.
    inversion H1; subst; simpl in *.
    exists (
      mkSyncState (linked_lts (raw_compose M1 M2))
      (@mkRawComposedState liA liB liC
        M1 M2
        (LState (RawL1State s1))
        (LState (RawL2State s1)))
      []
    ).
    simpl. intuition.
    unfold sync_new_state.
    simpl. intuition.
    unfold raw_composed_new_state.
    simpl. intuition.
    unfold thread_state_map.
    rewrite H3, H5.
    simpl. intuition.
    unfold sync_raw_compose_wf.
    simpl. econstructor.
    unfold thread_state_map_inv.
    rewrite H3, H5.
    simpl. intuition.
    unfold thread_state_mutual.
    rewrite H3, H5.
    simpl. intuition.
    inversion H6.
  - rename H3 into Hmap.
    rename H4 into Hwf.
    rename H5 into Hmap_inv.
    rename H7 into Hmutual.
    inversion H1; subst; simpl in *.
    exists (
      mkSyncState (linked_lts (raw_compose M1 M2))
      (@mkRawComposedState liA liB liC
        M1 M2
        (LState st1)
        (LState st2'))
      ((pid, Run)::(PidPos s2))
    ).
    inversion H3; subst; simpl in *.
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_initial_state_L with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      apply Hmap; auto.
      econstructor.
      simpl.
      eapply ImplRawCompose.raw_composed_initial_state_M2; eauto.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmap in Hnotin; auto.
        apply Hmap_inv in Hnotin; auto.
        apply binds_in in H5.
        unfold "#" in Hnotin; intuition.
        apply binds_push_neq; auto.
        apply Hmap; auto.
      apply binds_push_inv in H7; auto.
      intuition.
        subst. apply binds_push_eq; auto.
        apply binds_push_neq; auto.
        apply Hmap; auto.
      simpl in *.
      apply notin_union in H5.
      apply notin_union.
      intuition.
      apply Hmap; auto.
      unfold sync_raw_compose_wf.
      simpl.
      econstructor; eauto.
      apply Hmap; auto.
      econstructor.
      unfold thread_state_map_inv.
      simpl.
      intros.
      apply notin_union in H5.
      intuition.
      apply Hmap_inv in H7; intuition.
      apply notin_union. intuition.
      apply Hmap_inv; auto.
      unfold thread_state_mutual.
      simpl. intros.
      apply binds_push_inv in H5.
      intuition.
        subst.
        apply Hmap in Hnotin; auto.
        apply Hmap_inv in Hnotin; intuition.
        econstructor.
  - rename H3 into Hmap.
    rename H4 into Hwf.
    rename H5 into Hmap_inv.
    rename H7 into Hmutual.
    inversion H1; subst; simpl in *.
    exists (
      mkSyncState (linked_lts (raw_compose M1 M2))
      (@mkRawComposedState liA liB liC
        M1 M2
        (LState st1)
        (LState st2'))
      (remove (PidPos s2) pid)
    ).
    inversion H3; subst; simpl in *.
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_final_state_L with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      apply Hmap; auto.
      econstructor.
      simpl.
      eapply ImplRawCompose.raw_composed_final_state_M2; eauto.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmutual in Hbinds.
        apply binds_in in H5; auto.
        unfold "#" in Hbinds; intuition.
        apply remove_neq_preserves_binds; auto.
        apply Hmap; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove pos pid)).
        apply ok_remove_notin; auto.
        apply binds_in in H7.
        unfold "#" in H0; intuition.
        apply remove_neq_preserves_binds; auto.
        apply remove_preserves_binds_notin in H7; auto.
        apply Hmap; auto.
      destruct (eq_nat_dec pid0 pid).
        subst. apply ok_remove_notin; auto.
        apply remove_preserves_notin; auto.
        apply remove_neq_preserves_notin in H5; auto.
        apply Hmap; auto.
      unfold sync_raw_compose_wf.
      simpl.
      apply remove_preserves_ok; auto.
      unfold thread_state_map_inv.
      simpl.
      intros.
      destruct (eq_nat_dec pid0 pid).
        subst. intuition.
        apply ok_remove_notin; auto.
        apply remove_neq_preserves_notin in H5; auto.
        intuition.
        apply Hmap_inv; auto.
        apply remove_preserves_notin; auto.
        apply Hmap_inv; auto.
      unfold thread_state_mutual.
      intros.
      destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove pos pid)).
        apply ok_remove_notin; auto.
        apply binds_in in H5.
        unfold "#" in H0; intuition.
        apply remove_preserves_binds_notin in H5; auto.
  - rename H3 into Hmap.
    rename H4 into Hwf.
    rename H5 into Hmap_inv.
    rename H7 into Hmutual.
    inversion H1; subst; simpl in *.
    exists (
      mkSyncState (linked_lts (raw_compose M1 M2))
      (@mkRawComposedState liA liB liC
        M1 M2
        (LState st1')
        (LState st2))
      ((pid, Wait)::(remove (PidPos s2) pid))
    ).
    inversion H3; subst; simpl in *.
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_at_external_L with (pos:=PidPos); eauto.
      apply Hmap in Hbinds; auto.
      simpl.
      eapply ImplRawCompose.raw_composed_at_external_M1; eauto.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      apply binds_push_inv in H5; auto.
      intuition.
        subst. apply binds_push_eq; auto.
        apply remove_preserves_binds_notin in H7; auto.
        apply binds_push_neq; auto.
        apply remove_neq_preserves_binds; auto.
        apply Hmap; auto.
      simpl in H6.
      apply notin_union in H6.
      intuition.
      apply notin_neq in H5.
      apply remove_neq_preserves_notin in H8; auto.
      apply binds_push_neq; auto.
      apply remove_neq_preserves_binds; auto.
      apply Hmap; auto.
      simpl.
      apply notin_union.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmap in H5; auto.
        apply Hmap_inv in H5.
        apply binds_in in Hbinds.
        unfold "#" in H5; intuition.
        intuition.
        apply notin_neq; auto.
        apply remove_preserves_notin; auto.
        apply Hmap; auto.
      unfold sync_raw_compose_wf.
      simpl.
      econstructor; eauto.
      apply remove_preserves_ok; auto.
      apply ok_remove_notin; auto.
      unfold thread_state_map_inv.
      simpl.
      intros.
      apply notin_union in H5.
      intuition.
      apply notin_neq in H6.
      apply remove_neq_preserves_notin in H7; auto.
      apply Hmap_inv in H7; intuition.
      apply notin_union.
      intuition.
      apply notin_neq; auto.
      apply remove_preserves_notin; auto.
      apply notin_neq in H6.
      apply remove_neq_preserves_notin in H7; auto.
      apply Hmap_inv; auto.
      unfold thread_state_mutual.
      simpl. intros.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmutual in H5; auto.
        apply binds_in in Hbinds.
        unfold "#" in H5.
        intuition.
        apply notin_union.
        intuition.
        apply notin_neq; auto.
        apply remove_preserves_notin; auto.
  - rename H3 into Hmap.
    rename H4 into Hwf.
    rename H5 into Hmap_inv.
    rename H7 into Hmutual.
    inversion H1; subst; simpl in *.
    exists (
      mkSyncState (linked_lts (raw_compose M1 M2))
      (@mkRawComposedState liA liB liC
        M1 M2
        (LState st1')
        (LState st2))
      ((pid, Run)::(remove (PidPos s2) pid))
    ).
    inversion H3; subst; simpl in *.
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_after_external_L with (pos:=PidPos); eauto.
      apply Hmap in Hbinds; auto.
      simpl.
      eapply ImplRawCompose.raw_composed_after_external_M1; eauto.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      apply binds_push_inv in H5; auto.
      intuition.
        subst. apply binds_push_eq; auto.
        apply remove_preserves_binds_notin in H7; auto.
        apply binds_push_neq; auto.
        apply remove_neq_preserves_binds; auto.
        apply Hmap; auto.
      simpl in H6.
      apply notin_union in H6.
      intuition.
      apply notin_neq in H5.
      apply remove_neq_preserves_notin in H8; auto.
      apply binds_push_neq; auto.
      apply remove_neq_preserves_binds; auto.
      apply Hmap; auto.
      simpl.
      apply notin_union.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmap in H5; auto.
        apply Hmap_inv in H5.
        apply binds_in in Hbinds.
        unfold "#" in H5; intuition.
        intuition.
        apply notin_neq; auto.
        apply remove_preserves_notin; auto.
        apply Hmap; auto.
      unfold sync_raw_compose_wf.
      simpl.
      econstructor; eauto.
      apply remove_preserves_ok; auto.
      apply ok_remove_notin; auto.
      unfold thread_state_map_inv.
      simpl.
      intros.
      apply notin_union in H5.
      intuition.
      apply notin_neq in H6.
      apply remove_neq_preserves_notin in H7; auto.
      apply Hmap_inv in H7; intuition.
      apply notin_union.
      intuition.
      apply notin_neq; auto.
      apply remove_preserves_notin; auto.
      apply notin_neq in H6.
      apply remove_neq_preserves_notin in H7; auto.
      apply Hmap_inv; auto.
      unfold thread_state_mutual.
      simpl. intros.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmutual in H5; auto.
        apply binds_in in Hbinds.
        unfold "#" in H5.
        intuition.
        apply notin_union.
        intuition.
        apply notin_neq; auto.
        apply remove_preserves_notin; auto.
  - rename H3 into Hmap.
    rename H4 into Hwf.
    rename H5 into Hmap_inv.
    rename H7 into Hmutual.
    inversion H1; subst; simpl in *.
    --
    inversion H3; subst; simpl in *.
    exists (
      mkSyncState (linked_lts (raw_compose M1 M2))
      (@mkRawComposedState liA liB liC
        M1 M2
        (LState st1)
        (LState st2'))
      (PidPos s2)
    ).
    inversion H4; subst; simpl in *.
    simpl. intuition.
      destruct s2. simpl in *.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      eapply Hmap; eauto.
      econstructor.
      simpl.
      eapply linked_step_int_L2; eauto.
      eapply ImplRawCompose.raw_composed_step_M2_internal; eauto.
      destruct LState. simpl in *.
      subst. auto.
    --
    inversion H3; subst; simpl in *.
    exists (
      mkSyncState (linked_lts (raw_compose M1 M2))
      (@mkRawComposedState liA liB liC
        M1 M2
        (LState st1')
        (LState st2))
      (PidPos s2)
    ).
    inversion H4; subst; simpl in *.
    simpl. intuition.
      destruct s2. simpl in *.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      eapply Hmap in Hbinds; eauto.
      simpl.
      eapply linked_step_int_L1; eauto.
      eapply ImplRawCompose.raw_composed_step_M1_internal; eauto.
      destruct LState. simpl in *.
      subst. auto.
    --
    inversion H3; subst; simpl in *.
    exists (
      mkSyncState (linked_lts (raw_compose M1 M2))
      (@mkRawComposedState liA liB liC
        M1 M2
        (LState st1')
        (LState st2'))
      (PidPos s2)
    ).
    inversion H4; subst; simpl in *.
    inversion H6; subst; simpl in *.
    simpl. intuition.
      destruct s2. simpl in *.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      eapply Hmap; eauto.
      econstructor.
      simpl.
      eapply linked_step_L2_push; eauto.
      eapply ImplRawCompose.raw_composed_step_M2_push; eauto.
      destruct LState. simpl in *.
      subst. auto.

      unfold thread_state_map in *.
      intuition.
      apply binds_push_inv in H0; auto.
      intuition.
        subst.
        apply Hmap; auto.
        econstructor.
        apply Hmap; auto.
      simpl in H8.
      apply notin_union in H8.
      apply binds_push_inv in H9.
      intuition.
        discriminate.
        apply remove_preserves_binds_notin in H11; auto.
        apply Hmap; auto.
      simpl in H0.
        apply notin_union in H0; auto.
        intuition.
        apply notin_neq in H8.
        apply remove_neq_preserves_notin in H9; auto.
        apply Hmap; auto.
      unfold thread_state_map_inv.
      simpl.
      intros.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmap_inv in H0; auto.
        apply binds_in in Hbinds.
        unfold "#" in H0.
        intuition.
        intuition.
        apply notin_union. intuition.
        apply notin_neq; auto.
        apply Hmap_inv; auto.
        apply notin_union. intuition.
        apply notin_neq; auto.
        apply remove_preserves_notin; auto.
        apply Hmap_inv; auto.
      unfold thread_state_mutual.
      simpl. intros.
      apply binds_push_inv in H0; auto.
      intuition.
        discriminate.
        apply remove_preserves_binds_notin in H9; auto.
        apply notin_union.
        intuition.
        apply notin_neq; auto.
    --
    inversion H3; subst; simpl in *.
    exists (
      mkSyncState (linked_lts (raw_compose M1 M2))
      (@mkRawComposedState liA liB liC
        M1 M2
        (LState st1')
        (LState st2'))
      (PidPos s2)
    ).
    inversion H5; subst; simpl in *.
    inversion H4; subst; simpl in *.
    simpl. intuition.
      destruct s2. simpl in *.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      eapply Hmap in Hbinds0; eauto.
      simpl.
      eapply linked_step_L1_pop; eauto.
      eapply ImplRawCompose.raw_composed_step_M1_pop; eauto.
      destruct LState. simpl in *.
      subst. auto.

      unfold thread_state_map in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove pos0 pid)).
        apply ok_remove_notin; auto.
        unfold "#" in H2.
        apply binds_in in H0.
        intuition.
        apply remove_preserves_binds_notin in H0; auto.
        apply Hmap; auto.
      apply binds_push_inv in H9; auto.
      intuition.
        subst.
        apply Hmap in Hbinds0; auto.
        apply remove_preserves_binds_notin in H10; auto.
        apply Hmap; auto.
      simpl in H0.
      apply notin_union in H0.
      intuition.
      apply notin_neq in H8.
      apply remove_neq_preserves_notin in H9; auto.
      apply Hmap; auto.

      unfold thread_state_map_inv.
      simpl.
      intros.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmap_inv in H0.
        apply binds_in in Hbinds0.
        unfold "#" in H0; intuition.
        intuition.
        apply remove_preserves_notin; auto.
        apply Hmap_inv; auto.
        apply notin_union.
        intuition.
        apply notin_neq; auto.
        apply remove_preserves_notin; auto.
        apply Hmap_inv; auto.
      unfold thread_state_mutual.
      simpl. intros.
      apply binds_push_inv in H0; auto.
      intuition.
        subst.
        apply ok_remove_notin; auto.
        apply remove_preserves_binds_notin in H9; auto.
        apply remove_preserves_notin; auto.
Qed.

Lemma raw_compose_consistency:
  impl_refines M1 (sync M1) ->
  impl_refines M2 (sync M2) ->
  impl_refines (linked_lts (raw_compose M1 M2))
    (sync (linked_lts (raw_compose M1 M2))).
Proof.
  intros.
  eapply impl_refines_trans with (M2:=(linked_lts (raw_compose (sync M1) (sync M2)))).
  eapply impl_refines_trans with (M2:=(linked_lts (raw_compose (sync M1) M2))).
  eapply impl_refines_composed_refines in H; eauto.
  eapply link_preserves_impl_composed_refines in H; eauto.
  eapply impl_refines_impl_composed_refines in H0; eauto.
  eapply link_preserves_impl_composed_refines in H0; eauto.
  eapply raw_compose_sync_refine_sync_raw_compose.
Qed.

End RawComposeConsistency.

Section RawComposeConsistency.

Require Import LTS.
Require Import SyncCompLTS.

Context {liA liB : language_interface}.
Variable L: lts li_null liA.
Variable M: lts liA liB.

Definition sync_raw_compose_wf' (y : state (sync (linked_lts (raw_compose L M)))) :=
  ok (y.(PidPos)).

Lemma raw_compose_sync_refine_sync_raw_compose':
  refines
  (linked_lts
     (raw_compose (sync L) (sync M)))
  (sync (linked_lts (raw_compose L M))).
Proof.
  eapply Refinement.forward_simulation_inv_ind
    with (f:=fun (x : state (linked_lts
     (raw_compose (sync L) (sync M)))) (y : state (sync (linked_lts (raw_compose L M)))) =>
      x.(RawL1State).(LState) = y.(LState).(RawL1State) /\
      x.(RawL2State).(LState) = y.(LState).(RawL2State) /\
      thread_state_map x.(RawL1State).(PidPos) x.(RawL2State).(PidPos) y.(PidPos) /\
      sync_raw_compose_wf' y /\
      thread_state_map_inv x.(RawL1State).(PidPos) x.(RawL2State).(PidPos) y.(PidPos) /\
      thread_state_mutual x.(RawL1State).(PidPos) x.(RawL2State).(PidPos)

      )
      (inv:=fun x => True).
  unfold Refinement.fsim_properties_inv_ind. intuition.
  - unfold invariant_ind. intuition.
  - inversion H; subst; simpl in *.
    inversion H0; subst; simpl in *.
    inversion H1; subst; simpl in *.
    exists (
      mkSyncState (linked_lts (raw_compose L M))
      (@mkRawComposedState liA liB 
        L M
        (LState (RawL1State s1))
        (LState (RawL2State s1)))
      []
    ).
    simpl. intuition.
    unfold sync_new_state.
    simpl. intuition.
    unfold raw_composed_new_state.
    simpl. intuition.
    unfold thread_state_map.
    rewrite H3, H5.
    simpl. intuition.
    unfold sync_raw_compose_wf'.
    simpl. econstructor.
    unfold thread_state_map_inv.
    rewrite H3, H5.
    simpl. intuition.
    unfold thread_state_mutual.
    rewrite H3, H5.
    simpl. intuition.
    inversion H6.
  - rename H3 into Hmap.
    rename H4 into Hwf.
    rename H5 into Hmap_inv.
    rename H7 into Hmutual.
    inversion H1; subst; simpl in *.
    exists (
      mkSyncState (linked_lts (raw_compose L M))
      (@mkRawComposedState liA liB 
        L M
        (LState st1)
        (LState st2'))
      ((pid, Run)::(PidPos s2))
    ).
    inversion H3; subst; simpl in *.
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_initial_state_L with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      apply Hmap; auto.
      econstructor.
      simpl.
      eapply raw_composed_initial_state_L2; eauto.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmap in Hnotin; auto.
        apply Hmap_inv in Hnotin; auto.
        apply binds_in in H5.
        unfold "#" in Hnotin; intuition.
        apply binds_push_neq; auto.
        apply Hmap; auto.
      apply binds_push_inv in H7; auto.
      intuition.
        subst. apply binds_push_eq; auto.
        apply binds_push_neq; auto.
        apply Hmap; auto.
      simpl in *.
      apply notin_union in H5.
      apply notin_union.
      intuition.
      apply Hmap; auto.
      unfold sync_raw_compose_wf.
      simpl.
      econstructor; eauto.
      apply Hmap; auto.
      econstructor.
      unfold thread_state_map_inv.
      simpl.
      intros.
      apply notin_union in H5.
      intuition.
      apply Hmap_inv in H7; intuition.
      apply notin_union. intuition.
      apply Hmap_inv; auto.
      unfold thread_state_mutual.
      simpl. intros.
      apply binds_push_inv in H5.
      intuition.
        subst.
        apply Hmap in Hnotin; auto.
        apply Hmap_inv in Hnotin; intuition.
        econstructor.
  - rename H3 into Hmap.
    rename H4 into Hwf.
    rename H5 into Hmap_inv.
    rename H7 into Hmutual.
    inversion H1; subst; simpl in *.
    exists (
      mkSyncState (linked_lts (raw_compose L M))
      (@mkRawComposedState liA liB
        L M
        (LState st1)
        (LState st2'))
      (remove (PidPos s2) pid)
    ).
    inversion H3; subst; simpl in *.
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_final_state_L with (pos:=PidPos); eauto.
      unfold thread_state_map in *.
      apply Hmap; auto.
      econstructor.
      simpl.
      eapply raw_composed_final_state_L2; eauto.
      destruct LState. simpl in *.
      subst. auto.
      unfold thread_state_map in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmutual in Hbinds.
        apply binds_in in H5; auto.
        unfold "#" in Hbinds; intuition.
        apply remove_neq_preserves_binds; auto.
        apply Hmap; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove pos pid)).
        apply ok_remove_notin; auto.
        apply binds_in in H7.
        unfold "#" in H0; intuition.
        apply remove_neq_preserves_binds; auto.
        apply remove_preserves_binds_notin in H7; auto.
        apply Hmap; auto.
      destruct (eq_nat_dec pid0 pid).
        subst. apply ok_remove_notin; auto.
        apply remove_preserves_notin; auto.
        apply remove_neq_preserves_notin in H5; auto.
        apply Hmap; auto.
      unfold sync_raw_compose_wf'.
      simpl.
      apply remove_preserves_ok; auto.
      unfold thread_state_map_inv.
      simpl.
      intros.
      destruct (eq_nat_dec pid0 pid).
        subst. intuition.
        apply ok_remove_notin; auto.
        apply remove_neq_preserves_notin in H5; auto.
        intuition.
        apply Hmap_inv; auto.
        apply remove_preserves_notin; auto.
        apply Hmap_inv; auto.
      unfold thread_state_mutual.
      intros.
      destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove pos pid)).
        apply ok_remove_notin; auto.
        apply binds_in in H5.
        unfold "#" in H0; intuition.
        apply remove_preserves_binds_notin in H5; auto.
  - rename H3 into Hmap.
    rename H4 into Hwf.
    rename H5 into Hmap_inv.
    rename H7 into Hmutual.
    inversion H1; subst; simpl in *.
    --
    inversion H3; subst; simpl in *.
    exists (
      mkSyncState (linked_lts (raw_compose L M))
      (@mkRawComposedState liA liB
        L M
        (LState st1)
        (LState st2'))
      (PidPos s2)
    ).
    inversion H4; subst; simpl in *.
    simpl. intuition.
      destruct s2. simpl in *.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      eapply Hmap; eauto.
      econstructor.
      simpl.
      eapply linked_step_int_L2; eauto.
      eapply raw_composed_step_L2_internal; eauto.
      destruct LState. simpl in *.
      subst. auto.
    --
    inversion H3; subst; simpl in *.
    exists (
      mkSyncState (linked_lts (raw_compose L M))
      (@mkRawComposedState liA liB
        L M
        (LState st1')
        (LState st2))
      (PidPos s2)
    ).
    inversion H4; subst; simpl in *.
    simpl. intuition.
      destruct s2. simpl in *.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      eapply Hmap in Hbinds; eauto.
      simpl.
      eapply linked_step_int_L1; eauto.
      eapply raw_composed_step_L1_internal; eauto.
      destruct LState. simpl in *.
      subst. auto.
    --
    inversion H3; subst; simpl in *.
    exists (
      mkSyncState (linked_lts (raw_compose L M))
      (@mkRawComposedState liA liB
        L M
        (LState st1')
        (LState st2'))
      (PidPos s2)
    ).
    inversion H4; subst; simpl in *.
    inversion H6; subst; simpl in *.
    simpl. intuition.
      destruct s2. simpl in *.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      eapply Hmap; eauto.
      econstructor.
      simpl.
      eapply linked_step_L2_push; eauto.
      eapply raw_composed_step_L2_push; eauto.
      destruct LState. simpl in *.
      subst. auto.

      unfold thread_state_map in *.
      intuition.
      apply binds_push_inv in H0; auto.
      intuition.
        subst.
        apply Hmap; auto.
        econstructor.
        apply Hmap; auto.
      simpl in H8.
      apply notin_union in H8.
      apply binds_push_inv in H9.
      intuition.
        discriminate.
        apply remove_preserves_binds_notin in H11; auto.
        apply Hmap; auto.
      simpl in H0.
        apply notin_union in H0; auto.
        intuition.
        apply notin_neq in H8.
        apply remove_neq_preserves_notin in H9; auto.
        apply Hmap; auto.
      unfold thread_state_map_inv.
      simpl.
      intros.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmap_inv in H0; auto.
        apply binds_in in Hbinds.
        unfold "#" in H0.
        intuition.
        intuition.
        apply notin_union. intuition.
        apply notin_neq; auto.
        apply Hmap_inv; auto.
        apply notin_union. intuition.
        apply notin_neq; auto.
        apply remove_preserves_notin; auto.
        apply Hmap_inv; auto.
      unfold thread_state_mutual.
      simpl. intros.
      apply binds_push_inv in H0; auto.
      intuition.
        discriminate.
        apply remove_preserves_binds_notin in H9; auto.
        apply notin_union.
        intuition.
        apply notin_neq; auto.
    --
    inversion H3; subst; simpl in *.
    exists (
      mkSyncState (linked_lts (raw_compose L M))
      (@mkRawComposedState liA liB 
        L M
        (LState st1')
        (LState st2'))
      (PidPos s2)
    ).
    inversion H5; subst; simpl in *.
    inversion H4; subst; simpl in *.
    simpl. intuition.
      destruct s2. simpl in *.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      eapply Hmap in Hbinds0; eauto.
      simpl.
      eapply linked_step_L1_pop; eauto.
      eapply raw_composed_step_L1_pop; eauto.
      destruct LState. simpl in *.
      subst. auto.

      unfold thread_state_map in *.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove pos0 pid)).
        apply ok_remove_notin; auto.
        unfold "#" in H2.
        apply binds_in in H0.
        intuition.
        apply remove_preserves_binds_notin in H0; auto.
        apply Hmap; auto.
      apply binds_push_inv in H9; auto.
      intuition.
        subst.
        apply Hmap in Hbinds0; auto.
        apply remove_preserves_binds_notin in H10; auto.
        apply Hmap; auto.
      simpl in H0.
      apply notin_union in H0.
      intuition.
      apply notin_neq in H8.
      apply remove_neq_preserves_notin in H9; auto.
      apply Hmap; auto.

      unfold thread_state_map_inv.
      simpl.
      intros.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmap_inv in H0.
        apply binds_in in Hbinds0.
        unfold "#" in H0; intuition.
        intuition.
        apply remove_preserves_notin; auto.
        apply Hmap_inv; auto.
        apply notin_union.
        intuition.
        apply notin_neq; auto.
        apply remove_preserves_notin; auto.
        apply Hmap_inv; auto.
      unfold thread_state_mutual.
      simpl. intros.
      apply binds_push_inv in H0; auto.
      intuition.
        subst.
        apply ok_remove_notin; auto.
        apply remove_preserves_binds_notin in H9; auto.
        apply remove_preserves_notin; auto.
Qed.

Lemma simple_raw_compose_consistency:
  refines L (sync L) ->
  impl_refines M (sync M) ->
  refines (linked_lts (raw_compose L M))
    (sync (linked_lts (raw_compose L M))).
Proof.
  intros.
  eapply trans_refinement with (L':=(linked_lts (raw_compose (sync L) (sync M)))).
  eapply trans_refinement with (L':=(linked_lts (raw_compose (sync L) M))).
  eapply refines_composed_refines in H; eauto.
  eapply link_preserves_composed_refines in H; eauto.
  eapply ImplRefinement.impl_refines_composed_refines in H0; eauto.
  apply link_preserves_composed_refines; eauto.
  eapply raw_compose_sync_refine_sync_raw_compose'.
Qed.

End RawComposeConsistency.

Section ComposeConsistency.

Require Import LTS.
Require Import Compose.

Context {liA liB : language_interface}.
Variable L: lts li_null liA.
Variable M: lts liA liB.

Lemma compose_consistency:
  refines (linked_lts (compose L M))
    (sync (linked_lts (raw_compose L M))).
Proof.
  eapply trans_refinement; eauto.
  2: {
    eapply raw_compose_sync_refine_sync_raw_compose'; eauto.
  }
  eapply Refinement.forward_simulation_inv_ind
    with (f:=fun (x : state (linked_lts (compose L M))) (y : state (linked_lts (raw_compose (sync L) (sync M)))) =>
      x.(L1State) = y.(RawL1State) /\
      x.(L2State) = y.(RawL2State)
      (* thread_state_map (y.(LState).(L1State).(PidPos)) (y.(LState).(L2State).(PidPos)) y.(PidPos) /\ *)
      (* syn_tensor_wf y *)
      )
      (inv:=fun x => True).
  unfold Refinement.fsim_properties_inv_ind. intuition.
  - unfold invariant_ind. intuition.
  - inversion H; subst; simpl in *.
    inversion H0; subst; simpl in *.
    inversion H1; subst; simpl in *.
    exists (
      @mkRawComposedState liA liB
        (sync L) (sync M)
        (L1State s1)
        (L2State s1)
    ).
    simpl. intuition.
  - inversion H1; subst; simpl in *.
    exists (
      @mkRawComposedState liA liB
        (sync L) (sync M)
        st1
        st2'
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply raw_composed_initial_state_L2; eauto.
    subst. auto.
  - inversion H1; subst; simpl in *.
    exists (
      @mkRawComposedState liA liB
        (sync L) (sync M)
        st1
        st2'
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply raw_composed_final_state_L2; eauto.
    subst. auto.
  - inversion H1; subst; simpl in *.
    --
    inversion H0; subst; simpl in *.
    exists (
      @mkRawComposedState liA liB
        (sync L) (sync M)
        st1
        st2'
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply linked_step_int_L2; eauto.
    eapply raw_composed_step_L2_internal; eauto.
    subst. auto.
    --
    inversion H0; subst; simpl in *.
    exists (
      @mkRawComposedState liA liB
        (sync L) (sync M)
        st1'
        st2
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply linked_step_int_L1; eauto.
    eapply raw_composed_step_L1_internal; eauto.
    subst. auto.
    --
    inversion H0; subst; simpl in *.
    exists (
      @mkRawComposedState liA liB
        (sync L) (sync M)
        st1'
        st2'
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply linked_step_L2_push; eauto.
    eapply raw_composed_step_L2_push; eauto.
    subst. auto.
    --
    inversion H0; subst; simpl in *.
    exists (
      @mkRawComposedState liA liB
        (sync L) (sync M)
        st1'
        st2'
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply linked_step_L1_pop; eauto.
    eapply raw_composed_step_L1_pop; eauto.
    subst. auto.
Qed.

End ComposeConsistency.

Section VComp.

Context {liA liB liC: language_interface}.
Variable L1: lts li_null liA.
Variable M1: lts liA liB.
Variable L2: lts li_null liB.
Variable M2: lts liB liC.
Variable L3: lts li_null liC.

Lemma raw_compose_assoc: 
refines
  (sync
     (LTS.linked_lts
        (LTS.raw_compose L1 (linked_lts (raw_compose M1 M2)))))
  (sync
     (LTS.linked_lts
        (LTS.raw_compose
           (LTS.linked_lts (LTS.raw_compose L1 M1)) M2))).
Proof.
  eapply Refinement.forward_simulation_inv_ind
    with (f:=fun 
    (x : state (sync
     (LTS.linked_lts
        (LTS.raw_compose L1 (linked_lts (raw_compose M1 M2)))))) 
    (y : state (sync
     (LTS.linked_lts
        (LTS.raw_compose
           (LTS.linked_lts (LTS.raw_compose L1 M1)) M2)))) =>
      x.(LState).(LTS.RawL1State) = y.(LState).(LTS.RawL1State).(LTS.RawL1State) /\
      x.(LState).(LTS.RawL2State).(RawL1State) = y.(LState).(LTS.RawL1State).(LTS.RawL2State) /\
      x.(LState).(LTS.RawL2State).(RawL2State) = y.(LState).(LTS.RawL2State) /\
      x.(PidPos) = y.(PidPos)
      )
      (inv:=fun x => True).
  unfold Refinement.fsim_properties_inv_ind. intuition.
  - unfold invariant_ind. intuition.
  - inversion H; subst; simpl in *.
    inversion H0; subst; simpl in *.
    inversion H3; subst; simpl in *.
    exists (
      mkSyncState 
        (LTS.linked_lts
            (LTS.raw_compose
              (LTS.linked_lts (LTS.raw_compose L1 M1)) M2))
      (@LTS.mkRawComposedState liB liC 
        (LTS.linked_lts (LTS.raw_compose L1 M1)) M2
          (@LTS.mkRawComposedState liA liB
            L1 M1
            (LTS.RawL1State (LState s1))
            (RawL1State (LTS.RawL2State (LState s1))))
            (RawL2State (LTS.RawL2State (LState s1)))
      )
      []
    ).
    simpl. intuition.
    unfold sync_new_state.
    simpl. intuition.
    unfold LTS.raw_composed_new_state.
    simpl. intuition.
    unfold LTS.raw_composed_new_state.
    simpl. intuition.
  - rename H2 into Hl1.
    rename H0 into Hm1.
    rename H3 into Hm2.
    rename H5 into Hpid.
    inversion H1; subst; simpl in *.
    inversion H0; subst; simpl in *.
    inversion H2; subst; simpl in *.
    exists (
      mkSyncState 
        (LTS.linked_lts
            (LTS.raw_compose
              (LTS.linked_lts (LTS.raw_compose L1 M1)) M2))
      (@LTS.mkRawComposedState liB liC 
        (LTS.linked_lts (LTS.raw_compose L1 M1)) M2
          (@LTS.mkRawComposedState liA liB
            L1 M1
            (LTS.RawL1State (LTS.RawL1State (LState s2)))
            st3
          )
          st2'0
      )
      ((pid, Run):: (PidPos s2))
    ).
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_initial_state_L with (pos:=PidPos); eauto.
      simpl.
      eapply LTS.raw_composed_initial_state_L2; eauto.
      destruct LState. simpl in *.
      destruct RawL1State. simpl in *.
      subst. auto.
  - rename H2 into Hl1.
    rename H0 into Hm1.
    rename H3 into Hm2.
    rename H5 into Hpid.
    inversion H1; subst; simpl in *.
    inversion H0; subst; simpl in *.
    inversion H2; subst; simpl in *.
    exists (
      mkSyncState 
        (LTS.linked_lts
            (LTS.raw_compose
              (LTS.linked_lts (LTS.raw_compose L1 M1)) M2))
      (@LTS.mkRawComposedState liB liC 
        (LTS.linked_lts (LTS.raw_compose L1 M1)) M2
          (@LTS.mkRawComposedState liA liB
            L1 M1
            (LTS.RawL1State (LTS.RawL1State (LState s2)))
            st0
          )
          st2'0
      )
      (remove (PidPos s2) pid)
    ).
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_final_state_L with (pos:=PidPos); eauto.
      simpl.
      eapply LTS.raw_composed_final_state_L2; eauto.
      destruct LState. simpl in *.
      destruct RawL1State. simpl in *.
      subst. auto.
  - rename H2 into Hl1.
    rename H0 into Hm1.
    rename H3 into Hm2.
    rename H5 into Hpid.
    inversion H1; subst; simpl in *.
    inversion H0; subst; simpl in *.
    (* step of raw_compose M1 M2 *)
    --
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    (* step of M2 *)
    ---
    inversion H4; subst; simpl in *.
    exists (
      mkSyncState 
        (LTS.linked_lts
            (LTS.raw_compose
              (LTS.linked_lts (LTS.raw_compose L1 M1)) M2))
      (@LTS.mkRawComposedState liB liC 
        (LTS.linked_lts (LTS.raw_compose L1 M1)) M2
          (@LTS.mkRawComposedState liA liB
            L1 M1
            (LTS.RawL1State (LTS.RawL1State (LState s2)))
            st1
          )
          st2'0
      )
      (PidPos s2)
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply sync_step_L_internal with (pos:=PidPos); eauto.
    simpl.
    eapply LTS.linked_step_int_L2; eauto.
    eapply LTS.raw_composed_step_L2_internal; eauto.
    destruct LState. simpl in *.
    destruct RawL1State. simpl in *.
    subst. auto.
    (* step of M1 *)
    ---
    inversion H4; subst; simpl in *.
    exists (
      mkSyncState 
        (LTS.linked_lts
            (LTS.raw_compose
              (LTS.linked_lts (LTS.raw_compose L1 M1)) M2))
      (@LTS.mkRawComposedState liB liC 
        (LTS.linked_lts (LTS.raw_compose L1 M1)) M2
          (@LTS.mkRawComposedState liA liB
            L1 M1
            (LTS.RawL1State (LTS.RawL1State (LState s2)))
            st1'
          )
          st0
      )
      (PidPos s2)
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply sync_step_L_internal with (pos:=PidPos); eauto.
    simpl.
    eapply LTS.linked_step_int_L1; eauto.
    eapply LTS.raw_composed_step_L1_internal; eauto.
    simpl.
    eapply LTS.linked_step_int_L2; eauto.
    eapply LTS.raw_composed_step_L2_internal; eauto.
    destruct LState. simpl in *.
    destruct RawL1State. simpl in *.
    subst. auto.
    (* M2 query M1 *)
    ---
    inversion H4; subst; simpl in *.
    exists (
      mkSyncState 
        (LTS.linked_lts
            (LTS.raw_compose
              (LTS.linked_lts (LTS.raw_compose L1 M1)) M2))
      (@LTS.mkRawComposedState liB liC 
        (LTS.linked_lts (LTS.raw_compose L1 M1)) M2
          (@LTS.mkRawComposedState liA liB
            L1 M1
            (LTS.RawL1State (LTS.RawL1State (LState s2)))
            st1'
          )
          st2'0
      )
      (PidPos s2)
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply sync_step_L_internal with (pos:=PidPos); eauto.
    simpl.
    eapply LTS.linked_step_L2_push; eauto.
    eapply LTS.raw_composed_step_L2_push; eauto.
    2 : {
      simpl.
      eapply LTS.raw_composed_initial_state_L2; eauto.
    }
    destruct LState. simpl in *.
    destruct RawL1State. simpl in *.
    subst. auto.
    (* M1 reply M2 *)
    ---
    inversion H4; subst; simpl in *.
    exists (
      mkSyncState 
        (LTS.linked_lts
            (LTS.raw_compose
              (LTS.linked_lts (LTS.raw_compose L1 M1)) M2))
      (@LTS.mkRawComposedState liB liC 
        (LTS.linked_lts (LTS.raw_compose L1 M1)) M2
          (@LTS.mkRawComposedState liA liB
            L1 M1
            (LTS.RawL1State (LTS.RawL1State (LState s2)))
            st1'
          )
          st2'0
      )
      (PidPos s2)
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply sync_step_L_internal with (pos:=PidPos); eauto.
    simpl.
    eapply LTS.linked_step_L1_pop; eauto.
    eapply LTS.raw_composed_step_L1_pop; eauto.
      simpl.
      eapply LTS.raw_composed_final_state_L2; eauto.
    destruct LState. simpl in *.
    destruct RawL1State. simpl in *.
    subst. auto.
    (* step of L1 *)
    --
    inversion H2; subst; simpl in *.
    exists (
      mkSyncState 
        (LTS.linked_lts
            (LTS.raw_compose
              (LTS.linked_lts (LTS.raw_compose L1 M1)) M2))
      (@LTS.mkRawComposedState liB liC 
        (LTS.linked_lts (LTS.raw_compose L1 M1)) M2
          (@LTS.mkRawComposedState liA liB
            L1 M1
            st1'
            (LTS.RawL2State (LTS.RawL1State (LState s2)))
          )
          (LTS.RawL2State (LState s2))
      )
      (PidPos s2)
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply sync_step_L_internal with (pos:=PidPos); eauto.
    simpl.
    eapply LTS.linked_step_int_L1; eauto.
    eapply LTS.raw_composed_step_L1_internal; eauto.
      simpl.
      eapply LTS.linked_step_int_L1; eauto.
      eapply LTS.raw_composed_step_L1_internal; eauto.
    destruct LState. simpl in *.
    destruct RawL1State. simpl in *.
    subst. auto.
    (* (raw_compose M1 M2) query L1 *)
    --
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    exists (
      mkSyncState 
        (LTS.linked_lts
            (LTS.raw_compose
              (LTS.linked_lts (LTS.raw_compose L1 M1)) M2))
      (@LTS.mkRawComposedState liB liC 
        (LTS.linked_lts (LTS.raw_compose L1 M1)) M2
          (@LTS.mkRawComposedState liA liB
            L1 M1
            st1'
            st1'0
          )
          (LTS.RawL2State (LState s2))
      )
      (PidPos s2)
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply sync_step_L_internal with (pos:=PidPos); eauto.
    simpl.
    eapply LTS.linked_step_int_L1; eauto.
    eapply LTS.raw_composed_step_L1_internal; eauto.
      simpl.
      eapply LTS.linked_step_L2_push; eauto.
      eapply LTS.raw_composed_step_L2_push; eauto.
    destruct LState. simpl in *.
    destruct RawL1State. simpl in *.
    subst. auto.
    (* L1 reply (raw_compose M1 M2) *)
    --
    inversion H2; subst; simpl in *.
    inversion H4; subst; simpl in *.
    exists (
      mkSyncState 
        (LTS.linked_lts
            (LTS.raw_compose
              (LTS.linked_lts (LTS.raw_compose L1 M1)) M2))
      (@LTS.mkRawComposedState liB liC 
        (LTS.linked_lts (LTS.raw_compose L1 M1)) M2
          (@LTS.mkRawComposedState liA liB
            L1 M1
            st1'
            st1'0
          )
          (LTS.RawL2State (LState s2))
      )
      (PidPos s2)
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply sync_step_L_internal with (pos:=PidPos); eauto.
    simpl.
    eapply LTS.linked_step_int_L1; eauto.
    eapply LTS.raw_composed_step_L1_internal; eauto.
      simpl.
      eapply LTS.linked_step_L1_pop; eauto.
      eapply LTS.raw_composed_step_L1_pop; eauto.
    destruct LState. simpl in *.
    destruct RawL1State. simpl in *.
    subst. auto.
Qed.

(* Notation " M ◁ M' " := (linked_lts (ImplRawCompose.raw_compose M M')) (at level 67). *)

Theorem VComp:
  L1 ⊢ M1 ~: L2 ->
  L2 ⊢ M2 ~: L3 ->
  L1 ⊢ M1 ◁ M2 ~: L3.
Proof.
  unfold veriobj.
  intros. intuition.
  apply raw_compose_consistency; auto.
  eapply trans_refinement; eauto.
  clear H5.
  assert (HM1: refines (sync (LTS.linked_lts (LTS.raw_compose L1 M1))) (sync L2)).
  eapply trans_refinement; eauto.
  eapply sync_raw_compose_refines_compose; eauto.
  eapply linked_refines_congruence in HM1; eauto.
  eapply trans_refinement; eauto.
  eapply trans_refinement; eauto.
  2: {
    eapply sync_raw_compose_refines_compose; eauto.
    apply simple_raw_compose_consistency; auto.
  }
  eapply trans_refinement; eauto.
  eapply compose_consistency; eauto.
  apply raw_compose_assoc.
Qed.

End VComp.