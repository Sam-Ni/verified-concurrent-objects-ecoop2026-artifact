Require Import
  List
  Arith
  LibVar
  LibEnv
  LTS
  Refinement
  SyncLTS
  Queue.
Import ListNotations.

Section Property.

Variable N: nat.

Definition thread_state_map (req : LibEnv.env Queue_query) (res : LibEnv.env Queue_reply) h :=
  forall pid q r,
  ((binds pid q req \/
  binds pid r res) ->
  binds pid Run h) /\
  (pid # req /\ pid # res -> pid # h).

Definition sync_queue_wf (y : state (sync (queue N))) :=
  ok y.(PidPos).

Definition queue_wf (req : LibEnv.env Queue_query) (res : LibEnv.env Queue_reply) :=
  forall pid q r,
  (binds pid q req -> pid # res) /\
  (binds pid r res -> pid # req).

Lemma queue_is_sc: 
  refines (queue N) (sync (queue N)).
Proof.
  eapply forward_simulation_inv_ind
    with (f:=fun (x : state (queue N)) (y : state (sync (queue N))) =>
      x = y.(LState) /\
      thread_state_map y.(LState).(requests) y.(LState).(responses) y.(PidPos) /\
      sync_queue_wf y /\
      queue_wf x.(requests) x.(responses)
      )
      (inv:=fun x => True).
  unfold fsim_properties_inv_ind. intuition.
  - unfold invariant_ind. intuition.
  - inversion H; subst; simpl in *.
    intuition.
    exists (mkSyncState (queue N)
      s1 []).
    simpl.
    rewrite H0, H2.
    intuition.
    unfold sync_new_state.
    simpl. intuition.
    unfold thread_state_map.
    intuition; inversion H4.
    unfold sync_queue_wf.
    simpl. econstructor.
    unfold queue_wf.
    intuition; inversion H1.
  - rename H0 into Hmap.
    rename H3 into Hwf.
    rename H5 into Hqwf.
    exists (mkSyncState (queue N)
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
    apply binds_push_inv in H2; auto.
    intuition.
      subst. apply binds_push_eq; auto.
      apply binds_push_neq; auto.
      eapply Hmap; eauto.
      rewrite H0. simpl.
      eauto.
    apply binds_push_inv in H2; auto.
    intuition.
      subst. apply binds_push_eq; auto.
      apply binds_push_neq; auto.
      eapply Hmap; eauto.
      rewrite H0. simpl.
      eauto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply binds_in in H2.
      inversion H1; subst; simpl in *;
      unfold "#" in Hnotin_res; intuition.
      apply binds_push_neq; auto.
      inversion H1; subst; simpl in *;
      eapply Hmap; eauto;
      rewrite H0; simpl; eauto.
    apply notin_union.
    inversion H1; subst; simpl in *;
    apply notin_union in H2;
    intuition;
    eapply Hmap; eauto;
    rewrite H0; eauto.
    unfold sync_queue_wf.
    simpl.
    econstructor; eauto.
    eapply Hmap; eauto.
    econstructor.
    inversion H1; subst; simpl in *;
    rewrite H0; simpl; eauto.
    unfold queue_wf.
    simpl. intuition.
    inversion H1; subst; simpl in *;
    apply binds_push_inv in H0;
    intuition; subst; auto;
      rewrite H3 in Hqwf;
      simpl in Hqwf;
      eapply Hqwf; eauto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply binds_in in H0.
      inversion H1; subst; simpl in *;
      unfold "#" in Hnotin_res; intuition.
      inversion H1; subst; simpl in *.
      apply notin_union; auto.
      intuition.
      apply notin_neq; auto.
      rewrite H3 in Hqwf; simpl in *.
      eapply Hqwf; eauto.
      apply notin_union; auto.
      intuition.
      apply notin_neq; auto.
      rewrite H3 in Hqwf; simpl in *.
      eapply Hqwf; eauto.
  - rename H0 into Hmap.
    rename H3 into Hwf.
    rename H5 into Hqwf.
    exists (mkSyncState (queue N)
      s1'
      (remove (PidPos s2) pid)).
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_final_state_L with (pos:=PidPos); eauto.
      inversion H1; subst; simpl in *; auto;
      eapply Hmap; eauto.
    subst. auto.
    subst.
    unfold thread_state_map.
    simpl. intuition.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply binds_in in H2.
      inversion H1; subst; simpl in *;
      rewrite H0 in Hqwf; simpl in *;
      apply Hqwf in Hbinds; auto;
      unfold "#" in Hbinds; intuition.
      apply remove_neq_preserves_binds; auto.
      inversion H1; subst; simpl in *;
      eapply Hmap; eauto;
      rewrite H0; eauto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply binds_in in H2.
      inversion H1; subst; simpl in *;
      assert (pid # (remove res pid)) by
      (apply ok_remove_notin; auto);
      unfold "#" in H3;
      intuition.
      apply remove_neq_preserves_binds; auto.
      inversion H1; subst; simpl in *;
      apply remove_preserves_binds_notin in H2; auto;
      eapply Hmap; eauto;
      rewrite H0; simpl in *; eauto.
    destruct (eq_nat_dec pid0 pid).
      subst. apply ok_remove_notin; auto.
      apply remove_preserves_notin; auto.
      inversion H1; subst; simpl in *;
      apply remove_neq_preserves_notin in H3; auto;
      apply Hmap; auto;
      rewrite H0; simpl; auto.
    unfold sync_queue_wf.
    simpl. apply remove_preserves_ok; auto.
    unfold queue_wf.
    simpl.
    intuition.
    destruct (eq_nat_dec pid0 pid).
      subst.
      inversion H1; subst; simpl in *;
      apply ok_remove_notin; auto.
      inversion H1; subst; simpl in *;
      apply remove_preserves_notin; auto;
      rewrite H3 in Hqwf; simpl in *;
      eapply Hqwf; eauto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply binds_in in H0.
      inversion H1; subst; simpl in *;
      assert (pid # (remove res pid)) by
      (apply ok_remove_notin; auto);
      unfold "#" in H3;
      intuition.
      inversion H1; subst; simpl in *;
      apply remove_preserves_binds_notin in H0; auto;
      rewrite H3 in Hqwf; simpl in *; 
      eapply Hqwf; eauto.
  - rename H0 into Hmap.
    rename H3 into Hwf.
    rename H5 into Hqwf.
    exists (mkSyncState (queue N)
      s1'
      (PidPos s2)).
    simpl. intuition.
      destruct s2. simpl in *.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      inversion H1; subst; simpl in *;
      eapply Hmap; eauto.
    subst. auto.
    unfold thread_state_map.
    simpl.
    intuition.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply binds_in in H3.
      inversion H1; subst; simpl in *;
      assert (pid # (remove inv pid)) by
      (apply ok_remove_notin; auto);
      unfold "#" in H5;
      intuition.
      inversion H1; subst; simpl in *;
      apply remove_preserves_binds_notin in H3; auto;
      eapply Hmap; eauto;
      rewrite H0; simpl; eauto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      inversion H1; subst; simpl in *;
      eapply Hmap; eauto;
      rewrite H0; simpl; eauto.
      inversion H1; subst; simpl in *;
      eapply Hmap; eauto;
      rewrite H0; simpl; eauto;
      right;
      eapply sameset_binds in H5; eauto;
      apply binds_push_neq_inv in H5; auto;
      eauto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      inversion H1; subst; simpl in *.
      apply sym_sameset in H5.
      eapply sameset_binds with (x:=pid) in H5; eauto.
      apply binds_in in H5.
      unfold "#" in H4. intuition.
      apply binds_push_eq; auto.
      apply sym_sameset in H5.
      eapply sameset_binds with (x:=pid) in H5; eauto.
      apply binds_in in H5.
      unfold "#" in H4. intuition.
      apply binds_push_eq; auto.
      inversion H1; subst; simpl in *;
      apply remove_neq_preserves_notin in H3; auto;
      eapply notin_sameset in H6; eauto;
      simpl in H6;
      apply notin_union in H6;
      intuition;
      apply Hmap; auto;
      rewrite H0; auto.
    unfold queue_wf.
    simpl.
    intuition.
    inversion H1; subst; simpl in *.
    apply sym_sameset in H5.
    eapply notin_sameset; eauto.
    simpl.
    apply notin_union.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply binds_in in H0.
      assert (pid # (remove inv pid)) by
      (apply ok_remove_notin; auto);
      unfold "#" in H2;
      intuition.
      apply remove_preserves_binds_notin in H0; auto.
      intuition.
      apply notin_neq; auto.
      rewrite H3 in Hqwf; simpl in *;
      eapply Hqwf; eauto.
    apply sym_sameset in H5.
    eapply notin_sameset; eauto.
    simpl.
    apply notin_union.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply binds_in in H0.
      assert (pid # (remove inv pid)) by
      (apply ok_remove_notin; auto);
      unfold "#" in H2;
      intuition.
      apply remove_preserves_binds_notin in H0; auto.
      intuition.
      apply notin_neq; auto.
      rewrite H3 in Hqwf; simpl in *;
      eapply Hqwf; eauto.
    inversion H1; subst; simpl in *.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply ok_remove_notin; auto.
        apply remove_preserves_notin; auto.
        eapply sameset_binds in H5; eauto.
        apply binds_push_neq_inv in H5; auto.
        rewrite H3 in Hqwf; simpl in *;
        eapply Hqwf; eauto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply ok_remove_notin; auto.
        apply remove_preserves_notin; auto.
        eapply sameset_binds in H5; eauto.
        apply binds_push_neq_inv in H5; auto.
        rewrite H3 in Hqwf; simpl in *;
        eapply Hqwf; eauto.
  Unshelve.
  all: econstructor; econstructor.
Qed.

End Property.
