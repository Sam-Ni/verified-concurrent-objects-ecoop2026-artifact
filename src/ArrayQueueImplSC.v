Require Import
  List
  Arith
  LibVar
  LibEnv
  LTS
  SyncLTS
  ImplRefinement
  ArrayQueueImpl
  ArrayQueueInvariant
  ArrayQueueInvariantBefore.
Import ListNotations.

Section ArrayQueueImplSC.

Variable N: nat.

Definition wait_pc p :=
  p = AEnq2 \/
  p = AEnq5 \/
  p = AEnq11 \/
  p = AEnq14 \/
  p = AEnq28 \/
  p = AEnq31 \/
  p = ADeq2 \/
  p = ADeq5 \/
  p = ADeq11 \/
  p = ADeq14 \/
  p = ADeq28 \/
  p = ADeq31
  .

Definition thread_state_map (pc : LibEnv.env AQueue_pc) h :=
  forall pid p,
  (binds pid p pc -> ~ wait_pc p ->
   binds pid Run h) /\
  (binds pid p pc -> wait_pc p ->
   binds pid Wait h) /\
  (pid # pc -> pid # h).

Definition sync_array_queue_impl_wf (y : state (sync (array_queue_impl N))) :=
  ok y.(PidPos).

Lemma array_queue_impl_is_sc: 
  impl_refines (array_queue_impl N)
    (sync (array_queue_impl N)).
Proof.
  eapply ImplRefinement.forward_simulation_inv_ind
    with (f:=fun (x : state (array_queue_impl N)) (y : state (sync (array_queue_impl N))) =>
      x = y.(LState) /\
      thread_state_map y.(LState).(pc) y.(PidPos) /\
      sync_array_queue_impl_wf y
      (* queue_wf x.(requests) x.(responses) *)
      )
      (inv:=fun x => True).
  unfold ImplRefinement.fsim_properties_inv_ind. intuition.
  - unfold invariant_ind. intuition.
  - exists (mkSyncState (array_queue_impl N)
      s1 []).
    simpl in *.
    unfold array_queue_new_state in H.
    unfold new_array_queue in H.
    rewrite H.
    simpl.
    unfold sync_new_state.
    simpl.
    unfold array_queue_new_state.
    simpl.
    unfold new_array_queue.
    simpl. intuition.
    unfold thread_state_map.
    intuition; inversion H0.
    unfold sync_array_queue_impl_wf.
    simpl.
    econstructor.
  - rename H0 into Hmap.
    rename H4 into Hwf.
    exists (mkSyncState (array_queue_impl N)
      s1'
      ((pid, Run)::(PidPos s2))).
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_initial_state_L with (pos:=PidPos); eauto.
      apply Hmap; auto.
      econstructor.
      inversion H1; subst; simpl in *; auto.
    subst. auto.
    subst.
    unfold thread_state_map.
    simpl. intuition.
    inversion H1; subst; simpl in *.
    apply binds_push_inv in H0; auto.
    intuition.
      subst. apply binds_push_eq; auto.
      apply binds_push_neq; auto.
      eapply Hmap; eauto.
      rewrite H3. simpl.
      eauto.
    apply binds_push_inv in H0; auto.
    intuition.
      subst. apply binds_push_eq; auto.
      apply binds_push_neq; auto.
      eapply Hmap; eauto.
      rewrite H3. simpl.
      eauto.
    inversion H1; subst; simpl in *.
      apply binds_push_inv in H0; auto.
      intuition.
        subst.
        unfold wait_pc in H2.
        intuition; discriminate.
      apply binds_push_neq; auto.
      eapply Hmap; eauto.
      rewrite H3; eauto.
      apply binds_push_inv in H0; auto.
      intuition.
        subst.
        unfold wait_pc in H2.
        intuition; discriminate.
      apply binds_push_neq; auto.
      eapply Hmap; eauto.
      rewrite H3; eauto.
    apply notin_union.
    destruct (eq_nat_dec pid0 pid).
      subst.
      inversion H1; subst; simpl in *;
      apply notin_union in H0;
      intuition;
      apply notin_neq in H3; intuition.
      inversion H1; subst; simpl in *;
      apply notin_union in H0;
      intuition;
      apply Hmap; auto;
      rewrite H2; auto.
    unfold sync_array_queue_impl_wf.
    simpl.
    econstructor; eauto.
    inversion H1; subst; simpl in *.
    apply Hmap; auto.
    econstructor.
    rewrite H0.
    simpl; auto.
    apply Hmap; auto.
    econstructor.
    rewrite H0.
    simpl; auto.
  - rename H0 into Hmap.
    rename H4 into Hwf.
    exists (mkSyncState (array_queue_impl N)
      s1'
      (remove (PidPos s2) pid)).
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_final_state_L with (pos:=PidPos); eauto.
      inversion H1; subst; simpl in *; auto;
      eapply Hmap; eauto;
      unfold wait_pc;
      intro; intuition; discriminate.
    subst. auto.
    subst.
    unfold thread_state_map.
    simpl. intuition.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply binds_in in H0.
      inversion H1; subst; simpl in *;
      assert (Hnot: pid # (remove pc pid)) by
      (apply ok_remove_notin; auto);
      unfold "#" in Hnot;
      intuition.
      inversion H1; subst; simpl in *.
      apply remove_preserves_binds_notin in H0; auto;
      apply remove_neq_preserves_binds; auto;
      eapply Hmap; eauto;
      rewrite H3; eauto.
      apply remove_preserves_binds_notin in H0; auto;
      apply remove_neq_preserves_binds; auto;
      eapply Hmap; eauto.
      rewrite H4; eauto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply binds_in in H0.
      inversion H1; subst; simpl in *;
      assert (Hnot: pid # (remove pc pid)) by
      (apply ok_remove_notin; auto);
      unfold "#" in Hnot;
      intuition.
      apply remove_neq_preserves_binds; auto.
      inversion H1; subst; simpl in *;
      apply remove_preserves_binds_notin in H0; auto;
      eapply Hmap; eauto.
      rewrite H3; eauto.
      rewrite H4; eauto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply ok_remove_notin; auto.
      apply remove_preserves_notin; auto.
      inversion H1; subst; simpl in *;
      apply remove_neq_preserves_notin in H0; auto;
      eapply Hmap; eauto.
      rewrite H2; eauto.
      rewrite H3; eauto.
    unfold sync_array_queue_impl_wf.
    simpl.
    apply remove_preserves_ok; auto.
  - rename H0 into Hmap.
    rename H4 into Hwf.
    exists (mkSyncState (array_queue_impl N)
      s1'
      ((pid, Wait)::(remove (PidPos s2) pid))
    ).
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_at_external_L with (pos:=PidPos); eauto.
      inversion H1; subst; simpl in *; auto;
      eapply Hmap; eauto;
      unfold wait_pc;
      intro; intuition; discriminate.
    subst. auto.
    unfold thread_state_map.
    simpl.
    intuition.
    destruct (eq_nat_dec pid0 pid).
      subst.
      unfold binds in H0.
      inversion H1; subst; simpl in *; auto;
      eapply substitute_eq_binds_v' in Hbinds;
      rewrite Hbinds in H0;
      inversion H0; subst;
      exfalso;
      apply H3;
      unfold wait_pc; intuition.
      apply binds_push_neq; auto.
      apply remove_neq_preserves_binds; auto.
      inversion H1; subst; simpl in *; auto;
      apply substitute_neq_preserves_binds' in H0; auto;
      eapply Hmap; eauto;
      rewrite H4; eauto.
    destruct (eq_nat_dec pid0 pid).
      subst. apply binds_push_eq; auto.
      apply binds_push_neq; auto.
      apply remove_neq_preserves_binds; auto.
      inversion H1; subst; simpl in *; auto;
      apply substitute_neq_preserves_binds' in H0; auto;
      eapply Hmap; eauto;
      rewrite H4; eauto.
    apply notin_union.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply notin_get_none in H0.
      inversion H1; subst; simpl in *;
      eapply substitute_eq_binds_v' in Hbinds; eauto;
      rewrite Hbinds in H0; discriminate.
      intuition.
      apply notin_neq; auto.
      apply remove_preserves_notin; auto;
      inversion H1; subst; simpl in *;
      apply substitute_preserves_notin' in H0;
      eapply Hmap; eauto;
      rewrite H3; eauto.
    unfold sync_array_queue_impl_wf.
    simpl.
    econstructor; eauto.
    apply remove_preserves_ok; auto.
    apply ok_remove_notin; auto.
  - rename H0 into Hmap.
    rename H4 into Hwf.
    exists (mkSyncState (array_queue_impl N)
      s1'
      ((pid, Run)::(remove (PidPos s2) pid))
    ).
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_after_external_L with (pos:=PidPos); eauto.
      inversion H1; subst; simpl in *; auto;
      eapply Hmap; eauto;
      unfold wait_pc; intuition.
    subst. auto.
    unfold thread_state_map.
    simpl.
    intuition.
    destruct (eq_nat_dec pid0 pid).
      subst. apply binds_push_eq; auto.
      apply binds_push_neq; auto.
      apply remove_neq_preserves_binds; auto.
      inversion H1; subst; simpl in *; auto;
      apply substitute_neq_preserves_binds' in H0; auto;
      eapply Hmap; eauto;
      rewrite H4; eauto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      unfold binds in H0.
      inversion H1; subst; simpl in *; auto;
      eapply substitute_eq_binds_v' in Hbinds;
      rewrite Hbinds in H0;
      inversion H0; subst;
      exfalso;
      unfold wait_pc in H3; intuition; discriminate.
      apply binds_push_neq; auto.
      apply remove_neq_preserves_binds; auto.
      inversion H1; subst; simpl in *; auto;
      apply substitute_neq_preserves_binds' in H0; auto;
      eapply Hmap; eauto;
      rewrite H4; eauto.
    apply notin_union.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply notin_get_none in H0.
      inversion H1; subst; simpl in *;
      eapply substitute_eq_binds_v' in Hbinds; eauto;
      rewrite Hbinds in H0; discriminate.
      intuition.
      apply notin_neq; auto.
      apply remove_preserves_notin; auto;
      inversion H1; subst; simpl in *;
      apply substitute_preserves_notin' in H0;
      eapply Hmap; eauto;
      rewrite H3; eauto.
    unfold sync_array_queue_impl_wf.
    simpl.
    econstructor; eauto.
    apply remove_preserves_ok; auto.
    apply ok_remove_notin; auto.
  - rename H0 into Hmap.
    rename H4 into Hwf.
    exists (mkSyncState (array_queue_impl N)
      s1'
      (PidPos s2)).
    simpl. intuition.
      destruct s2. simpl in *.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      inversion H1; subst; simpl in *;
      eapply Hmap; eauto;
      unfold wait_pc;
      intro; intuition; discriminate.
    subst. auto.
    subst.
    unfold thread_state_map.
    simpl. intuition.
    destruct (eq_nat_dec pid0 pid).
      subst.
      inversion H1; subst; simpl in *;
      try (rewrite H3 in Hmap);
      try (rewrite H4 in Hmap);
      simpl in *;
      eapply Hmap; eauto;
      unfold wait_pc; intro;
      intuition; discriminate.
      inversion H1; subst; simpl in *;
      apply substitute_neq_preserves_binds' in H0; auto;
      try (rewrite H3 in Hmap);
      try (rewrite H4 in Hmap);
      simpl in *;
      eapply Hmap; eauto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      unfold binds in H0.
      inversion H1; subst; simpl in *;
      eapply substitute_eq_binds_v' in Hbinds;
      rewrite Hbinds in H0;
      inversion H0; subst;
      unfold wait_pc in H2;
      intuition; discriminate.
      inversion H1; subst; simpl in *;
      apply substitute_neq_preserves_binds' in H0; auto;
      try (rewrite H3 in Hmap);
      try (rewrite H4 in Hmap);
      simpl in *;
      eapply Hmap; eauto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply notin_get_none in H0.
      inversion H1; subst; simpl in *;
      eapply substitute_eq_binds_v' in Hbinds;
      rewrite Hbinds in H0; discriminate.
      inversion H1; subst; simpl in *;
      apply substitute_preserves_notin' in H0; auto;
      eapply Hmap; eauto;
      try (rewrite H2);
      try (rewrite H3);
      eauto.
Qed.

End ArrayQueueImplSC.