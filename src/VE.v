Require Import
  List
  Arith
  LibVar
  LTS
  SyncLTS
  SyncCompLTS
  ImplRefinement
  Refinement
  Compose
  VeriTactics
  RawCompose
.

Import ListNotations.

Section INV.

Context {liA liB : language_interface}.
Variable L1 : lts li_null liA.
Variable L2 : lts liA liB.

Import LibEnv.

Definition sync_raw_compose_sync_wf (st : state (sync (linked_lts (raw_compose (sync L1) (sync L2))))) :=
  forall pid,
    (binds pid Run st.(LState).(RawL2State).(PidPos) ->
    pid # st.(LState).(RawL1State).(PidPos)) /\
    (pid # st.(PidPos) -> 
      pid # st.(LState).(RawL1State).(PidPos) /\
      pid # st.(LState).(RawL2State).(PidPos)
    ).

Lemma sync_raw_compose_sync_wf_new: forall s,
  new_state
    (sync (linked_lts (raw_compose (sync L1) (sync L2))))
    s ->
  sync_raw_compose_sync_wf s.
Proof.
  intros.
  inversion H; subst.
  unfold sync_raw_compose_sync_wf.
  inversion H0; subst.
  inversion H2; subst.
  inversion H3; subst.
  rewrite H5. rewrite H7.
  intros. intuition.
  inversion H8.
  apply notin_empty.
  apply notin_empty.
Qed.

Lemma sync_raw_compose_sync_wf_inv:
  invariant_ind (sync (linked_lts (raw_compose (sync L1) (sync L2)))) sync_raw_compose_sync_wf.
Proof.
  unfold invariant_ind. intuition.
  - apply sync_raw_compose_sync_wf_new; auto.
  - inversion H0; subst.
    simpl in *. clear H0.
    inversion H1; subst; simpl in *.
    -- clear H1. inversion H0; subst.
      simpl in *. clear H0.
      unfold sync_raw_compose_sync_wf in *.
      simpl in *. intros.
      specialize (H pid0).
      inversion H1; subst.
      simpl in *. intuition.
    -- clear H1. inversion H0; subst.
      simpl in *. clear H0.
      unfold sync_raw_compose_sync_wf in *.
      simpl in *. intros.
      specialize (H pid0).
      inversion H1; subst.
      simpl in *. intuition.
    -- clear H1. inversion H0; subst.
      simpl in *. clear H0.
      unfold sync_raw_compose_sync_wf in *.
      simpl in *. intros.
      inversion H1; subst.
      inversion H3; subst.
      simpl in *. intuition;
      apply notin_union;
      intuition; try apply notin_neq.
      apply binds_push_inv in H4.
      intuition; subst. discriminate.
      apply binds_push_inv in H4.
      intuition; subst. discriminate.
      apply remove_preserves_binds_notin in H6; auto.
      specialize (H pid0).
      intuition.
      specialize (H pid0).
      intuition. subst.
      apply binds_in in Hbinds0.
      unfold "#" in H8. intuition.
      specialize (H pid0).
      intuition. subst.
      apply binds_in in Hbinds0.
      specialize (H pid0).
      intuition. subst.
      unfold "#" in H8. intuition.
      specialize (H pid0).
      intuition.
      apply remove_preserves_notin; auto.
    -- clear H1. inversion H0; subst.
      simpl in *. clear H0.
      unfold sync_raw_compose_sync_wf in *.
      simpl in *. intros.
      inversion H1; subst.
      inversion H2; subst.
      simpl in *.
      specialize (H pid0). intuition.
      apply binds_push_inv in H.
      intuition. subst.
      apply ok_remove_notin; auto.
      apply remove_preserves_binds_notin in H7; auto.
      intuition.
      apply remove_preserves_notin; auto.
      apply remove_preserves_notin; auto.
      apply notin_union. intuition.
      apply notin_neq; auto.
      intro. subst.
      apply binds_in in Hbinds1.
      unfold "#" in H7. intuition.
      apply remove_preserves_notin; auto.
  - inversion H0; subst.
    simpl in *. clear H0.
    inversion H1; subst; simpl in *.
    clear H1.
    inversion H0; subst; simpl in *.
    unfold sync_raw_compose_sync_wf in *.
    simpl in *. intros.
    specialize (H pid0). intuition.
    apply binds_push_inv in H; intuition.
    subst. intuition.
    apply notin_union in H. intuition.
    apply notin_union in H.
    apply notin_union. intuition.
  - destruct act.
  - destruct act.
  - inversion H0; subst.
    simpl in *. clear H0.
    inversion H1; subst; simpl in *.
    clear H1.
    inversion H0; subst; simpl in *.
    unfold sync_raw_compose_sync_wf in *.
    simpl in *. intros.
    specialize (H pid0).
    destruct (eq_nat_dec pid0 pid).
    -- subst.
      intuition.
      apply ok_remove_notin; auto.
    -- intuition.
      apply remove_preserves_binds_notin in H; auto.
      apply remove_neq_preserves_notin in H; auto.
      intuition.
      apply remove_neq_preserves_notin in H; auto.
      intuition.
      apply remove_preserves_notin; auto.
Qed.

End INV.

Section COMPSYNC.

Context {liA liB : language_interface}.

Import LibEnv.

Fixpoint gather_comppidpos pos pos1 pos2 : env CompPosition :=
  match pos with
  | nil => nil
  | (pid, p) :: pos' =>
    let comppos' := gather_comppidpos pos' pos1 pos2 in
    match p with
    | Wait => (pid, CompWait) :: comppos'
    | Run => match get pid pos1 with
            | None => match get pid pos2 with
                      | None => (pid, CompL1Run) :: comppos' (* unreachable *)
                      | Some p2 => match p2 with
                                  | Wait => (pid, CompL1Run) :: comppos'
                                  | Run => (pid, CompL2Run) :: comppos'
                                  end
                      end
            | Some p1 => match p1 with
                        | Wait => (pid, CompL1Run) :: comppos' (* unreachable *)
                        | Run => (pid, CompL1Run) :: comppos'
                        end
            end
    end
  end.

Lemma gather_comppidpos_preserves_notin: forall pos pos1 pos2 pid,
  pid # pos ->
  pid # (gather_comppidpos pos pos1 pos2).
Proof.
  induction pos; simpl; intros.
  - assumption.
  - destruct a. simpl in *.
    apply notin_union in H.
    intuition.
    match_if_apply IHpos;
    simpl; apply notin_union; intuition; apply IHpos.
Qed.

Lemma gather_comppidpos_preserves_ok: forall pos pos1 pos2,
  ok pos ->
  ok (gather_comppidpos pos pos1 pos2).
Proof.
  induction 1; simpl; intros.
  - econstructor.
  - destruct T;
    match_if_apply IHok;
    econstructor; eauto;
    eapply gather_comppidpos_preserves_notin; eauto.
Qed.

Lemma gather_comppidpos_notin_any_pos2: forall pos pos1 pos2 pid v,
  pid # pos ->
  gather_comppidpos pos pos1 ((pid, v) :: pos2) =
  gather_comppidpos pos pos1 (pos2).
Proof.
  induction pos; simpl; intros.
  - reflexivity.
  - destruct a. simpl in *.
    apply notin_union in H. intuition.
    match_if'; subst; try rewrite IHpos; auto.
    apply Nat.eqb_eq in Heqb. subst.
    apply notin_neq in H0. intuition.
    apply Nat.eqb_eq in Heqb. subst.
    apply notin_neq in H0. intuition.
    apply Nat.eqb_eq in Heqb. subst.
    apply notin_neq in H0. intuition.
Qed.

Lemma gather_comppidpos_notin_any_pos1: forall pos pos1 pos2 pid v,
  pid # pos ->
  gather_comppidpos pos ((pid, v) :: pos1) pos2 =
  gather_comppidpos pos pos1 pos2.
Proof.
  induction pos; simpl; intros.
  - reflexivity.
  - destruct a. simpl in *.
    apply notin_union in H. intuition.
    match_if'; subst; try rewrite IHpos; auto.
    apply Nat.eqb_eq in Heqb. subst.
    apply notin_neq in H0. intuition.
    apply Nat.eqb_eq in Heqb. subst.
    apply notin_neq in H0. intuition.
Qed.

Lemma gather_comppidpos_notin_any_pos2': forall pos pos1 pos2 pid,
  pid # pos ->
  gather_comppidpos pos pos1 (remove pos2 pid) =
  gather_comppidpos pos pos1 (pos2).
Proof.
  induction pos; simpl; intros.
  - reflexivity.
  - destruct a. simpl in *.
    apply notin_union in H. intuition.
    match_if'; subst; try rewrite IHpos; auto.
    apply notin_neq in H0.
    apply remove_preserves_binds_notin in Heqo0; auto.
    rewrite Heqo0 in Heqo1. discriminate.
    apply notin_neq in H0.
    apply remove_preserves_binds_notin in Heqo0; auto.
    rewrite Heqo0 in Heqo1. discriminate.
    apply notin_neq in H0.
    apply remove_preserves_binds_notin in Heqo0; auto.
    rewrite Heqo0 in Heqo1. discriminate.
    apply notin_neq in H0.
    eapply remove_neq_preserves_binds in Heqo1; eauto.
    rewrite Heqo1 in Heqo0. discriminate.
Qed.

Lemma gather_comppidpos_notin_any_pos1': forall pos pos1 pos2 pid,
  pid # pos ->
  gather_comppidpos pos (remove pos1 pid) pos2 =
  gather_comppidpos pos pos1 pos2.
Proof.
  induction pos; simpl; intros.
  - reflexivity.
  - destruct a. simpl in *.
    apply notin_union in H. intuition.
    match_if'; subst; try rewrite IHpos; auto.
    apply notin_neq in H0.
    apply remove_preserves_binds_notin in Heqo; auto.
    rewrite Heqo in Heqo0. discriminate.
    apply notin_neq in H0.
    apply remove_preserves_binds_notin in Heqo; auto.
    rewrite Heqo in Heqo0. discriminate.
    apply notin_neq in H0.
    eapply remove_neq_preserves_binds in Heqo1; eauto.
    rewrite Heqo1 in Heqo. discriminate.
    apply notin_neq in H0.
    eapply remove_neq_preserves_binds in Heqo1; eauto.
    rewrite Heqo1 in Heqo. discriminate.
Qed.

Lemma gather_comppidpos_binds_run_pos_binds_run_pos0: forall pos pos0 pos1 pid,
  binds pid Run pos ->
  binds pid Run pos0 ->
  pid # pos1 ->
  binds pid CompL2Run (gather_comppidpos pos pos1 pos0).
Proof.
  induction pos; simpl; intros.
  - inversion H.
  - destruct a. simpl in *.
    apply binds_push_inv in H.
    intuition.
    -- subst.
      apply notin_get_none in H1.
      rewrite H1.
      rewrite H0.
      apply binds_push_eq.
    -- destruct p.
      destruct (get v pos1)eqn:Hv.
      destruct p.
      apply binds_push_neq; auto.
      apply binds_push_neq; auto.
      destruct (get v pos0)eqn:Hv'.
      destruct p.
      apply binds_push_neq; auto.
      apply binds_push_neq; auto.
      apply binds_push_neq; auto.
      apply binds_push_neq; auto.
Qed.

Lemma gather_comppidpos_binds_run_pos_binds_run_pos0': forall pos pos0 pos1 pid,
  binds pid Run pos ->
  binds pid Run pos0 ->
  binds pid CompL1Run (gather_comppidpos pos pos0 pos1).
Proof.
  induction pos; simpl; intros.
  - inversion H.
  - destruct a. simpl in *.
    apply binds_push_inv in H.
    intuition.
    -- subst.
      rewrite H0.
      apply binds_push_eq.
    -- destruct p.
      destruct (get v pos0)eqn:Hv.
      destruct p.
      apply binds_push_neq; auto.
      apply binds_push_neq; auto.
      destruct (get v pos1)eqn:Hv'.
      destruct p.
      apply binds_push_neq; auto.
      apply binds_push_neq; auto.
      apply binds_push_neq; auto.
      apply binds_push_neq; auto.
Qed.

Lemma gather_comppidpos_remove_comm: forall pos pos1 pos2 pid,
  gather_comppidpos (remove pos pid) pos1 pos2 =
  remove (gather_comppidpos pos pos1 pos2) pid.
Proof.
  induction pos; simpl; intros.
  - reflexivity.
  - destruct a. simpl in *.
    match_if'; try discriminate; subst;
    try rewrite IHpos; reflexivity.
Qed.

Lemma gather_comppidpos_dist: forall pos pos' pos1 pos2,
  gather_comppidpos (pos ++ pos') pos1 pos2 =
  gather_comppidpos pos pos1 pos2 ++
  gather_comppidpos pos' pos1 pos2.
Proof.
  induction pos; simpl; intros.
  - reflexivity.
  - destruct a; simpl in *.
    match_if'; subst; try rewrite IHpos;
    simpl; f_equal.
Qed.

Lemma tt: forall (L1 : lts li_null liA) (L2 : lts liA liB),
  refines (sync (linked_lts (raw_compose (sync L1) (sync L2))))
    (linked_lts (comp_sync (raw_compose L1 L2))).
Proof.
  intros.
  eapply forward_simulation_inv_ind
    with (f:= fun (x : state (sync (linked_lts (raw_compose (sync L1) (sync L2))))) (y : state (linked_lts (comp_sync (raw_compose L1 L2)))) =>
      x.(LState).(RawL1State).(LState) = y.(CompLState).(RawL1State) /\
      x.(LState).(RawL2State).(LState) = y.(CompLState).(RawL2State) /\
      sameset 
        (gather_comppidpos
          x.(PidPos)
          x.(LState).(RawL1State).(PidPos)
          x.(LState).(RawL2State).(PidPos)) 
        y.(CompPidPos)
      )
      (inv:=sync_raw_compose_sync_wf L1 L2).
  unfold fsim_properties_inv_ind. intuition.
  - apply sync_raw_compose_sync_wf_inv.
  - inversion H; subst.
    destruct s1.
    destruct LState. simpl in *.
    destruct RawL1State.
    destruct RawL2State.
    exists (
      mkCompSyncState
        (raw_compose L1 L2)
        (mkRawComposedState LState LState0)
        []
    ).
    simpl. intuition.
    unfold comp_sync_new_state.
    simpl. intuition.
    inversion H0; subst.
    simpl in *.
    inversion H2; subst.
    inversion H3; subst.
    simpl in *.
    unfold raw_composed_new_state.
    intuition.
    rewrite H1.
    simpl.
    apply sameset_refl.
    econstructor.
  - inversion H1; subst.
    simpl in *.
    inversion H3; subst.
    simpl in *.
    inversion H5; subst.
    simpl in *.
    exists (
      mkCompSyncState
        (raw_compose L1 L2)
        (mkRawComposedState 
          s2.(CompLState).(RawL1State)
          st')
        ((pid, CompL2Run)::s2.(CompPidPos))
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply comp_sync_initial_state_L; eauto.
    eapply sameset_ok; eauto.
    eapply gather_comppidpos_preserves_ok; eauto.
    eapply notin_sameset; eauto.
    eapply gather_comppidpos_preserves_notin; eauto.
    eapply raw_composed_initial_state_L2; eauto.
    destruct CompLState. simpl.
    rewrite H0. reflexivity.
    assert (Htmp : pid # pos) by assumption.
    apply H in Hnotin. simpl in *.
    intuition.
    apply notin_get_none in H7.
    rewrite H7.
    rewrite Nat.eqb_refl.
    f_equal.
    eapply sameset_push_eq; eauto.
    rewrite gather_comppidpos_notin_any_pos2; auto.
    apply gather_comppidpos_preserves_notin; auto.
  - inversion H1; subst.
    simpl in *.
    inversion H3; subst.
    simpl in *.
    inversion H5; subst.
    simpl in *.
    exists (
      mkCompSyncState
        (raw_compose L1 L2)
        (mkRawComposedState 
          s2.(CompLState).(RawL1State)
          st')
        (remove s2.(CompPidPos) pid)
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply comp_sync_final_state_L; eauto.
    eapply sameset_ok; eauto.
    eapply gather_comppidpos_preserves_ok; eauto.
    eapply sameset_binds; eauto.
    apply gather_comppidpos_binds_run_pos_binds_run_pos0; auto.
    apply H in Hbinds0. simpl in *.
    intuition.
    eapply raw_composed_final_state_L2; eauto.
    destruct CompLState. simpl.
    rewrite H0. reflexivity.
    eapply trans_sameset.
    2 :{
    eapply sameset_remove; eauto.
    }
    rewrite gather_comppidpos_notin_any_pos2'; auto.
    rewrite gather_comppidpos_remove_comm.
    apply sameset_refl.
    apply remove_preserves_ok; auto.
    apply gather_comppidpos_preserves_ok; auto.
    apply ok_remove_notin; auto.
  - inversion H1; subst.
    simpl in *.
    inversion H3; subst.
    simpl in *.
    --
    inversion H5; subst.
    simpl in *.
    inversion H6; subst.
    simpl in *.
    exists (
      mkCompSyncState
        (raw_compose L1 L2)
        (mkRawComposedState 
          s2.(CompLState).(RawL1State)
          st')
        (s2.(CompPidPos))
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply Step_Internal with (pid:=pid); eauto.
    2 : { eapply Step_None; eauto. }
    eapply linked_step_int_L2; eauto.
    eapply comp_sync_step_L2_internal; eauto.
    eapply sameset_ok; eauto.
    eapply gather_comppidpos_preserves_ok; eauto.
    eapply sameset_binds; eauto.
    apply gather_comppidpos_binds_run_pos_binds_run_pos0; auto.
    apply H in Hbinds0. simpl in *.
    intuition.
    eapply raw_composed_step_L2_internal; eauto.
    destruct CompLState. simpl.
    rewrite H0. reflexivity.
    --
    inversion H5; subst.
    simpl in *.
    inversion H6; subst.
    simpl in *.
    exists (
      mkCompSyncState
        (raw_compose L1 L2)
        (mkRawComposedState
          st'
          s2.(CompLState).(RawL2State)
        )
        (s2.(CompPidPos))
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply Step_Internal with (pid:=pid); eauto.
    2 : { eapply Step_None; eauto. }
    eapply linked_step_int_L1; eauto.
    eapply comp_sync_step_L1_internal; eauto.
    eapply sameset_ok; eauto.
    eapply gather_comppidpos_preserves_ok; eauto.
    eapply sameset_binds; eauto.
    apply gather_comppidpos_binds_run_pos_binds_run_pos0'; auto.
    eapply raw_composed_step_L1_internal; eauto.
    destruct CompLState. simpl.
    rewrite H2. reflexivity.
    --
    inversion H5; subst.
    simpl in *.
    inversion H6; subst.
    simpl in *.
    inversion H8; subst.
    simpl in *.
    exists (
      mkCompSyncState
        (raw_compose L1 L2)
        (mkRawComposedState
          st'0
          st'
        )
        ((pid, CompL1Run) :: (remove s2.(CompPidPos) pid))
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply Step_Internal with (pid:=pid); eauto.
    2 : { eapply Step_None; eauto. }
    eapply linked_step_L2_push; eauto.
    eapply comp_sync_internal_query_L2; eauto.
    eapply sameset_ok; eauto.
    eapply gather_comppidpos_preserves_ok; eauto.
    eapply sameset_binds; eauto.
    apply gather_comppidpos_binds_run_pos_binds_run_pos0; auto.
    eapply raw_composed_step_L2_push; eauto.
    destruct CompLState. simpl.
    rewrite H2. reflexivity.
    apply binds_reconstruct in Hbinds.
    destruct Hbinds as [l1 [l2 Hlist]].
    subst.
    repeat rewrite gather_comppidpos_dist.
    simpl.
    rewrite Nat.eqb_refl.
    eapply trans_sameset.
    eapply sameset_ExF_xEF.
    eapply ok_ExF_xEF.
    rewrite <-gather_comppidpos_dist.
    econstructor; eauto.
    apply gather_comppidpos_preserves_ok; auto.
    apply ok_remove in Hok; auto.
    apply gather_comppidpos_preserves_notin; auto.
    apply notin_concat.
    apply ok_remove_middle_inv in Hok; intuition.
    apply ok_remove_middle_inv in Hok; intuition.
    apply sameset_push_eq; auto.
    apply sameset_remove with (x:=pid) in H4.
    eapply trans_sameset; eauto.
    rewrite <-gather_comppidpos_remove_comm.
    rewrite remove_notin_app.
    simpl. rewrite Nat.eqb_refl.
    rewrite <-gather_comppidpos_dist.
    rewrite gather_comppidpos_notin_any_pos2.
    rewrite gather_comppidpos_notin_any_pos2'.
    rewrite gather_comppidpos_notin_any_pos1.
    apply sameset_refl.
    apply gather_comppidpos_preserves_ok; auto.
    apply notin_concat; auto.
    apply notin_concat; auto.
    apply notin_concat; auto.
    auto.
    rewrite <-gather_comppidpos_dist.
    apply gather_comppidpos_preserves_notin; auto.
    apply notin_concat; auto.
    --
    inversion H5; subst.
    simpl in *.
    inversion H6; subst.
    simpl in *.
    inversion H7; subst.
    simpl in *.
    exists (
      mkCompSyncState
        (raw_compose L1 L2)
        (mkRawComposedState
          st'
          st'0
        )
        ((pid, CompL2Run) :: (remove s2.(CompPidPos) pid))
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply Step_Internal with (pid:=pid); eauto.
    2 : { eapply Step_None; eauto. }
    eapply linked_step_L1_pop; eauto.
    eapply comp_sync_internal_reply_L1; eauto.
    eapply sameset_ok; eauto.
    eapply gather_comppidpos_preserves_ok; eauto.
    eapply sameset_binds; eauto.
    apply gather_comppidpos_binds_run_pos_binds_run_pos0'; auto.
    eapply raw_composed_step_L1_pop; eauto.
    destruct CompLState. simpl.
    rewrite H0. reflexivity.
    apply binds_reconstruct in Hbinds.
    destruct Hbinds as [l1 [l2 Hlist]].
    subst.
    repeat rewrite gather_comppidpos_dist.
    simpl.
    rewrite Nat.eqb_refl.
    assert (Hnotin : pid # (remove pos0 pid)).
    apply ok_remove_notin; auto.
    apply notin_get_none in Hnotin.
    rewrite Hnotin.
    eapply trans_sameset.
    simpl.
    eapply sameset_ExF_xEF.
    eapply ok_ExF_xEF.
    rewrite <-gather_comppidpos_dist.
    econstructor; eauto.
    apply gather_comppidpos_preserves_ok; auto.
    apply ok_remove in Hok; auto.
    apply gather_comppidpos_preserves_notin; auto.
    apply notin_concat.
    apply ok_remove_middle_inv in Hok; intuition.
    apply ok_remove_middle_inv in Hok; intuition.
    apply sameset_push_eq; auto.
    apply sameset_remove with (x:=pid) in H4.
    eapply trans_sameset; eauto.
    rewrite <-gather_comppidpos_remove_comm.
    rewrite remove_notin_app.
    simpl. rewrite Nat.eqb_refl.
    rewrite <-gather_comppidpos_dist.
    rewrite gather_comppidpos_notin_any_pos2.
    rewrite gather_comppidpos_notin_any_pos2'.
    rewrite gather_comppidpos_notin_any_pos1'.
    apply sameset_refl.
    apply gather_comppidpos_preserves_ok; auto.
    apply notin_concat; auto.
    apply notin_concat; auto.
    apply notin_concat; auto.
    auto.
    rewrite <-gather_comppidpos_dist.
    apply gather_comppidpos_preserves_notin; auto.
    apply notin_concat; auto.
Qed.

Lemma refines_sync_refines_raw_compose: forall (L1 : lts li_null liA) (L2 : lts liA liB),
  refines L1 (sync L1) ->
  impl_refines L2 (sync L2) ->
  refines ((linked_lts (raw_compose L1 L2)))
    ((linked_lts (raw_compose (sync L1) (sync L2)))).
Proof.
  intros.
  apply link_preserves_composed_refines.
  eapply composed_refines_trans.
  eapply refines_composed_refines; eauto.
  eapply impl_refines_composed_refines; eauto.
Qed.

Fixpoint gather_pos_from_inner_pos pos2 pos1 : env Position :=
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
  end.

Lemma gather_pos_from_inner_pos_preserves_notin: forall pos2 pos1 pid,
  pid # pos2 ->
  pid # (gather_pos_from_inner_pos pos2 pos1).
Proof.
  induction pos2; simpl; intros.
  - assumption.
  - destruct a.
    simpl in *.
    apply notin_union in H.
    intuition.
    destruct p; simpl.
    -- apply notin_union; auto.
    -- destruct (get v pos1).
      --- destruct p; simpl;
        apply notin_union; auto.
      --- simpl.
        apply notin_union; auto.
Qed.

Lemma gather_pos_from_inner_pos_binds_run_L2_preserves_binds: forall pos2 pos1 pid,
  binds pid Run pos2 ->
  binds pid Run (gather_pos_from_inner_pos pos2 pos1).
Proof.
  induction pos2; simpl; intros.
  - inversion H.
  - destruct a.
    apply binds_push_inv in H.
    intuition.
    -- subst.
      apply binds_push_eq.
    -- destruct p.
      --- apply binds_push_neq; auto.
      --- destruct (get v pos1); auto.
        destruct p; apply binds_push_neq; auto.
        apply binds_push_neq; auto.
Qed.

Lemma gather_pos_from_inner_pos_binds_wait_L2_binds_run_L1_preserves_binds: forall pos2 pos1 pid,
  binds pid Wait pos2 ->
  binds pid Run pos1 ->
  binds pid Run (gather_pos_from_inner_pos pos2 pos1).
Proof.
  induction pos2; simpl; intros.
  - inversion H.
  - destruct a.
    apply binds_push_inv in H.
    intuition.
    -- subst.
      rewrite H0.
      apply binds_push_eq.
    -- destruct p.
      --- apply binds_push_neq; auto.
      --- destruct (get v pos1); auto.
        destruct p; apply binds_push_neq; auto.
        apply binds_push_neq; auto.
Qed.

Lemma gather_pos_from_inner_pos_preserves_ok: forall pos2 pos1,
  ok pos2 ->
  ok (gather_pos_from_inner_pos pos2 pos1).
Proof.
  induction 1; simpl; intros.
  - econstructor.
  - destruct T.
    -- econstructor; eauto.
      apply gather_pos_from_inner_pos_preserves_notin; auto.
    -- match_if';
      simpl;
      econstructor; eauto;
      apply gather_pos_from_inner_pos_preserves_notin; auto.
Qed.

Lemma gather_pos_from_inner_pos_any_pos1: forall pos2 pos1 pid,
  pid # pos2 ->
  gather_pos_from_inner_pos pos2 ((pid, Run) :: pos1) =
  gather_pos_from_inner_pos pos2 pos1.
Proof.
  induction pos2; simpl; intros.
  - reflexivity.
  - destruct a.
    apply notin_union in H. intuition.
    match_if'; subst; try rewrite IHpos; 
    simpl; f_equal; auto.
    apply Nat.eqb_eq in Heqb. subst.
    apply notin_neq in H0. intuition.
Qed.

Lemma gather_pos_from_inner_pos_any_pos1': forall pos2 pos1 pid,
  pid # pos2 ->
  gather_pos_from_inner_pos pos2 (remove pos1 pid) =
  gather_pos_from_inner_pos pos2 pos1.
Proof.
  induction pos2; simpl; intros.
- reflexivity.
- destruct a.
  apply notin_union in H. intuition.
  match_if'; subst; try rewrite IHpos; 
  simpl; f_equal; auto.
  apply notin_neq in H0.
  apply remove_preserves_binds_notin in Heqo; auto.
  rewrite Heqo in Heqo0. discriminate.
  apply notin_neq in H0.
  apply remove_preserves_binds_notin in Heqo; auto.
  rewrite Heqo in Heqo0. discriminate.
  apply notin_neq in H0.
  apply remove_preserves_binds_notin in Heqo; auto.
  rewrite Heqo in Heqo0. discriminate.
  apply notin_neq in H0.
  eapply remove_neq_preserves_binds in Heqo0; eauto.
  rewrite Heqo0 in Heqo. discriminate.
Qed.

Lemma gather_pos_from_inner_pos_remove_comm: forall pos2 pos1 pid,
  gather_pos_from_inner_pos (remove pos2 pid) pos1 =
  remove (gather_pos_from_inner_pos pos2 pos1) pid.
Proof.
  induction pos2; simpl; intros.
  - reflexivity.
  - destruct a.
    match_if';
    try rewrite IHpos2; f_equal; try discriminate.
Qed.

Lemma gather_pos_from_inner_pos_dist: forall pos2 pos2' pos1,
  gather_pos_from_inner_pos (pos2 ++ pos2') pos1 =
  gather_pos_from_inner_pos pos2 pos1 ++
  gather_pos_from_inner_pos pos2' pos1.
Proof.
  induction pos2; simpl; intros.
  - reflexivity.
  - destruct a; simpl.
    match_if'; subst;
    rewrite IHpos2; simpl; f_equal.
Qed.

Definition link_raw_compose_sync_wf (L1 : lts li_null liA) (L2 : lts liA liB) (st : state ((linked_lts (raw_compose (sync L1) (sync L2))))) :=
  (ok st.(RawL2State).(PidPos)) /\
  forall pid,
    (binds pid Run st.(RawL1State).(PidPos) ->
    binds pid Wait st.(RawL2State).(PidPos)).

Lemma link_raw_compose_sync_wf_inv: forall (L1 : lts li_null liA) (L2 : lts liA liB),
  invariant_ind (linked_lts (raw_compose (sync L1) (sync L2))) (link_raw_compose_sync_wf L1 L2).
Proof.
  unfold invariant_ind. intuition.
  - inversion H; subst.
    unfold link_raw_compose_sync_wf.
    inversion H1; subst.
    inversion H0; subst.
    rewrite H3.
    rewrite H5.
    intuition.
    econstructor.
    inversion H6.
  - inversion H0; subst.
    simpl in *. clear H0.
    -- inversion H1; subst.
      simpl in *. clear H1.
      unfold link_raw_compose_sync_wf in *.
      simpl in *.
      destruct H as [Hok Hpid].
      inversion H0; subst.
      simpl in *. intuition.
    -- inversion H1; subst.
      simpl in *. clear H1.
      unfold link_raw_compose_sync_wf in *.
      simpl in *.
      destruct H as [Hok Hpid].
      inversion H2; subst.
      simpl in *. intuition.
    -- inversion H1; subst.
      simpl in *. clear H1.
      unfold link_raw_compose_sync_wf in *.
      simpl in *.
      inversion H2; subst.
      simpl in *.
      inversion H4; subst.
      simpl in *. intuition.
      econstructor; eauto.
      apply remove_preserves_ok; auto.
      apply ok_remove_notin; auto.
      apply binds_push_inv in H.
      intuition.
      --- subst.
        apply binds_push_eq.
      --- apply binds_push_neq; auto.
        apply remove_neq_preserves_binds; auto.
    -- inversion H1; subst.
      simpl in *. clear H1.
      unfold link_raw_compose_sync_wf in *.
      simpl in *.
      inversion H3; subst.
      inversion H2; subst.
      simpl in *. intuition.
      econstructor; eauto.
      apply remove_preserves_ok; auto.
      apply ok_remove_notin; auto.
      destruct (eq_nat_dec pid0 pid).
      --- subst.
        assert (pid # (remove pos0 pid)).
        apply ok_remove_notin; auto.
        apply binds_in in H.
        unfold "#" in H7. intuition.
      ---
        apply remove_preserves_binds_notin in H; auto.
        apply binds_push_neq; auto.
        apply remove_neq_preserves_binds; auto.
  - inversion H0; subst.
    simpl in *. clear H0.
    inversion H1; subst; simpl in *.
    unfold link_raw_compose_sync_wf in *.
    simpl in *. intuition.
    econstructor; eauto.
    apply H3 in H.
    apply binds_push_neq; auto.
    intro. subst.
    apply binds_in in H.
    unfold "#" in Hnotin.
    intuition.
  - destruct act.
  - destruct act.
  - inversion H0; subst.
    simpl in *. clear H0.
    inversion H1; subst; simpl in *.
    unfold link_raw_compose_sync_wf in *.
    simpl in *.
    intuition.
    apply remove_preserves_ok; auto.
    destruct (eq_nat_dec pid0 pid).
    -- subst.
      apply H3 in H.
      unfold binds in Hbinds.
      rewrite H in Hbinds.
      discriminate.
    -- apply remove_neq_preserves_binds; auto.
Qed.

Lemma raw_compose_sync_sync_refines_sync_raw_compose_sync_sync: forall (L1 : lts li_null liA) (L2 : lts liA liB),
  refines (linked_lts (raw_compose (sync L1) (sync L2)))
    (sync (linked_lts (raw_compose (sync L1) (sync L2)))).
Proof.
  intros.
  eapply forward_simulation_inv_ind
    with (f:=fun (x : state (linked_lts (raw_compose (sync L1) (sync L2)))) (y : state (sync (linked_lts (raw_compose (sync L1) (sync L2))))) => 
      x.(RawL1State) = y.(LState).(RawL1State) /\
      x.(RawL2State) = y.(LState).(RawL2State) /\
      sameset (gather_pos_from_inner_pos 
        x.(RawL2State).(PidPos)
        x.(RawL1State).(PidPos)) y.(PidPos)
      )
      (inv:=link_raw_compose_sync_wf L1 L2).
  unfold fsim_properties_inv_ind. intuition.
  - apply link_raw_compose_sync_wf_inv.
  - inversion H; subst.
    destruct s1.
    simpl in *.
    exists (
      mkSyncState (linked_lts (raw_compose (sync L1) (sync L2)))
      (@mkRawComposedState liA liB
        (sync L1) (sync L2)
          RawL1State
          RawL2State)
      []
    ).
    simpl. intuition.
    unfold sync_new_state.
    simpl. intuition.
    inversion H1; subst.
    rewrite H3. simpl.
    eapply sameset_refl.
    econstructor.
  - inversion H1; subst.
    simpl in *.
    exists (
      mkSyncState (linked_lts (raw_compose (sync L1) (sync L2)))
      (@mkRawComposedState liA liB
        (sync L1) (sync L2)
          st1
          st2')
      ((pid, Run) :: s2.(PidPos))
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    destruct LState. simpl in *.
    rewrite <-H0. rewrite <-H2.
    eapply sync_initial_state_L with (pos:=PidPos); eauto.
    inversion H3; subst.
    simpl.
    eapply sameset_ok; eauto.
    apply gather_pos_from_inner_pos_preserves_ok; auto.
    inversion H3; subst.
    simpl.
    eapply notin_sameset.
    2 : { eassumption. }
    apply gather_pos_from_inner_pos_preserves_notin; auto.
    inversion H3; subst.
    simpl.
    eapply sameset_push_eq; eauto.
    eapply trans_sameset; eauto.
    rewrite H6. simpl.
    eapply sameset_refl; eauto.
    apply gather_pos_from_inner_pos_preserves_ok; auto.
    apply gather_pos_from_inner_pos_preserves_notin; auto.
  - inversion H1; subst.
    simpl in *.
    exists (
      mkSyncState (linked_lts (raw_compose (sync L1) (sync L2)))
      (@mkRawComposedState liA liB
        (sync L1) (sync L2)
          st1
          st2')
      (remove s2.(PidPos) pid)
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply sync_final_state_L with (pos:=PidPos); eauto.
    inversion H3; subst.
    simpl.
    eapply sameset_ok; eauto.
    rewrite H6. simpl.
    apply gather_pos_from_inner_pos_preserves_ok; auto.
    inversion H3; subst.
    eapply sameset_binds; eauto.
    simpl.
    apply gather_pos_from_inner_pos_binds_run_L2_preserves_binds; auto.
    rewrite H6.
    simpl. assumption.
    destruct LState.
    rewrite H0. rewrite H2.
    simpl.
    reflexivity.
    inversion H3; subst.
    simpl.
    rewrite gather_pos_from_inner_pos_remove_comm.
    apply sameset_remove; auto.
    eapply trans_sameset; eauto.
    rewrite H6.
    simpl.
    eapply sameset_refl; eauto.
    apply gather_pos_from_inner_pos_preserves_ok; auto.
  - inversion H1; subst.
    simpl in *.
    -- inversion H3; subst.
      simpl in *.
      exists (
        mkSyncState (linked_lts (raw_compose (sync L1) (sync L2)))
        (@mkRawComposedState liA liB
          (sync L1) (sync L2)
            st1
            st2')
        (s2.(PidPos))
      ).
      simpl. intuition.
      destruct s2. simpl in *.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      inversion H5; subst.
      eapply sameset_ok; eauto.
      rewrite H7. simpl.
      apply gather_pos_from_inner_pos_preserves_ok; auto.
      inversion H5; subst.
      eapply sameset_binds; eauto.
      rewrite H7. simpl.
      apply gather_pos_from_inner_pos_binds_run_L2_preserves_binds; auto.
      destruct LState.
      rewrite H0. rewrite H2.
      simpl.
      reflexivity.
      inversion H5; subst.
      simpl.
      eapply trans_sameset; eauto.
      rewrite H7. simpl.
      eapply sameset_refl; eauto.
      apply gather_pos_from_inner_pos_preserves_ok; auto.
    -- inversion H3; subst.
      simpl in *.
      exists (
        mkSyncState (linked_lts (raw_compose (sync L1) (sync L2)))
        (@mkRawComposedState liA liB
          (sync L1) (sync L2)
            st1'
            st2)
        (s2.(PidPos))
      ).
      simpl. intuition.
      destruct s2. simpl in *.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      inversion H5; subst.
      eapply sameset_ok; eauto.
      rewrite H7. simpl.
      apply gather_pos_from_inner_pos_preserves_ok; auto.
      unfold link_raw_compose_sync_wf in *. intuition.
      inversion H5; subst.
      eapply sameset_binds; eauto.
      rewrite H7. simpl.
      apply gather_pos_from_inner_pos_binds_wait_L2_binds_run_L1_preserves_binds; auto.
      unfold link_raw_compose_sync_wf in *. intuition.
      specialize (H2 pid). simpl in H2.
      rewrite H7 in H2. simpl in *. intuition.
      destruct LState.
      simpl.
      rewrite H0. rewrite H2.
      simpl.
      reflexivity.
      inversion H5; subst.
      simpl. f_equal.
      eapply trans_sameset; eauto.
      f_equal.
      rewrite H7. simpl.
      eapply sameset_refl; eauto.
      apply gather_pos_from_inner_pos_preserves_ok; auto.
      unfold link_raw_compose_sync_wf in *; intuition.
    -- inversion H3; subst.
      simpl in *.
      exists (
        mkSyncState (linked_lts (raw_compose (sync L1) (sync L2)))
        (@mkRawComposedState liA liB
          (sync L1) (sync L2)
            st1'
            st2')
        (s2.(PidPos))
      ).
      simpl. intuition.
      destruct s2. simpl in *.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      inversion H5; subst.
      eapply sameset_ok; eauto.
      rewrite H8. simpl.
      apply gather_pos_from_inner_pos_preserves_ok; auto.
      inversion H5; subst.
      eapply sameset_binds; eauto.
      rewrite H8. simpl.
      apply gather_pos_from_inner_pos_binds_run_L2_preserves_binds; auto.
      destruct LState.
      simpl.
      rewrite H0. rewrite H2.
      simpl.
      reflexivity.
      inversion H5; subst.
      inversion H7; subst.
      simpl in *.
      rewrite Nat.eqb_refl.
      destruct s2. simpl in *.
      destruct LState. simpl in *.
      eapply trans_sameset; eauto.
      rewrite H8.
      rewrite H2.
      simpl.
      apply binds_reconstruct in Hbinds.
      destruct Hbinds as [l1 [l2 Hlist]].
      rewrite Hlist.
      rewrite Hlist in Hok.
      apply ok_remove_middle_inv in Hok.
      rewrite remove_notin_app; intuition.
      simpl.
      simpl.
      rewrite Nat.eqb_refl.
      repeat rewrite gather_pos_from_inner_pos_dist.
      simpl.
      repeat rewrite gather_pos_from_inner_pos_any_pos1; intuition.
      apply sym_sameset.
      eapply sameset_ExF_xEF; eauto.
      eapply ok_ExF_xEF; eauto.
      rewrite <-gather_pos_from_inner_pos_dist.
      econstructor; eauto.
      apply gather_pos_from_inner_pos_preserves_ok; auto.
      apply gather_pos_from_inner_pos_preserves_notin; auto.
      apply notin_concat; intuition.
    -- inversion H3; subst.
      simpl in *.
      exists (
        mkSyncState (linked_lts (raw_compose (sync L1) (sync L2)))
        (@mkRawComposedState liA liB
          (sync L1) (sync L2)
            st1'
            st2')
        (s2.(PidPos))
      ).
      simpl. intuition.
      destruct s2. simpl in *.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      inversion H6; subst.
      eapply sameset_ok; eauto.
      rewrite H8. simpl.
      apply gather_pos_from_inner_pos_preserves_ok; auto.
      inversion H6; subst.
      eapply sameset_binds; eauto.
      rewrite H8. simpl.
      inversion H5; subst.
      rewrite H2.
      apply gather_pos_from_inner_pos_binds_wait_L2_binds_run_L1_preserves_binds; auto.
      destruct LState.
      simpl.
      rewrite H0. rewrite H2.
      simpl.
      reflexivity.
      inversion H5; subst.
      inversion H6; subst.
      simpl in *.
      eapply trans_sameset; eauto.
      rewrite H8.
      rewrite H2.
      simpl.
      apply binds_reconstruct in Hbinds0.
      destruct Hbinds0 as [l1 [l2 Hlist]].
      rewrite Hlist.
      rewrite Hlist in Hok0.
      apply ok_remove_middle_inv in Hok0.
      rewrite remove_notin_app; intuition.
      simpl.
      rewrite Nat.eqb_refl.
      repeat rewrite gather_pos_from_inner_pos_dist.
      simpl.
      rewrite Hbinds.
      repeat rewrite gather_pos_from_inner_pos_any_pos1'; intuition.
      apply sym_sameset.
      eapply sameset_ExF_xEF; eauto.
      eapply ok_ExF_xEF; eauto.
      rewrite <-gather_pos_from_inner_pos_dist.
      econstructor; eauto.
      apply gather_pos_from_inner_pos_preserves_ok; auto.
      apply gather_pos_from_inner_pos_preserves_notin; auto.
      apply notin_concat; intuition.
Qed.

Lemma refines_sync_refines_sync_raw_compose: forall (L1 : lts li_null liA) (L2 : lts liA liB),
  refines L1 (sync L1) ->
  impl_refines L2 (sync L2) ->
  refines (sync (linked_lts (raw_compose L1 L2)))
    (sync (linked_lts (raw_compose (sync L1) (sync L2)))).
Proof.
  intros.
  assert (Hrefine :
  refines ((linked_lts (raw_compose L1 L2)))
    ((linked_lts (raw_compose (sync L1) (sync L2))))).
  apply refines_sync_refines_raw_compose; auto.
  eapply trans_refinement; eauto.
  2 : { 
    eapply raw_compose_sync_sync_refines_sync_raw_compose_sync_sync; eauto.
  }
  eapply trans_refinement; eauto.
  apply sync_refines_raw.
Qed.

Lemma sync_raw_compose_refines_comp_sync: forall (L1 : lts li_null liA) (L2 : lts liA liB),
  refines L1 (sync L1) ->
  impl_refines L2 (sync L2) ->
  refines (sync (linked_lts (raw_compose L1 L2)))
    (linked_lts (comp_sync (raw_compose L1 L2))).
Proof.
  intros.
  eapply trans_refinement; eauto.
  2 : {
    eapply tt; eauto.
  }
  apply refines_sync_refines_sync_raw_compose; auto.
Qed.

Theorem sync_raw_compose_refines_compose: forall (L1 : lts li_null liA) (L2 : lts liA liB),
  refines L1 (sync L1) ->
  impl_refines L2 (sync L2) ->
  refines (sync (linked_lts (raw_compose L1 L2)))
    (linked_lts (compose L1 L2)).
Proof.
  intros.
  eapply trans_refinement; eauto.
  eapply sync_raw_compose_refines_comp_sync; eauto.
  eapply link_raw_compose_refines_link_compose; eauto.
Qed.

End COMPSYNC.