Require Import
  Arith
  List
  LibEnv
  LTS
  SyncLTS
  ImplRefinement
  VeriTactics
  Counter
  Register
  LibVar
  RegisterCounterImpl
.
Require 
  LibEnv.
Import ListNotations.

Section Properties.

Import LibEnv.
  
Definition RegCntImplStateWF st :=
  ok st.(pc).

Lemma regcntimpl_initial_preserves_ok: forall st st' pid qb,
  initial_state register_counter_impl st pid qb st' ->
  RegCntImplStateWF st ->
  RegCntImplStateWF st'.
Proof.
  inversion 1; intros; subst;
  unfold RegCntImplStateWF; simpl; intuition;
  econstructor; eauto.
Qed.

Lemma regcntimpl_final_preserves_ok: forall st st' pid qb,
  final_state register_counter_impl st pid qb st' ->
  RegCntImplStateWF st ->
  RegCntImplStateWF st'.
Proof.
  inversion 1; intros; subst;
  unfold RegCntImplStateWF in *; intuition;
  simpl; apply remove_preserves_ok; auto.
Qed.

Lemma regcntimpl_at_external_preserves_ok: forall st st' pid qb,
  at_external register_counter_impl st pid qb st' ->
  RegCntImplStateWF st ->
  RegCntImplStateWF st'.
Proof.
  inversion 1; intros; subst;
  unfold RegCntImplStateWF in *; intuition; simpl in *;
  apply substitute_preserves_ok; auto.
Qed.

Lemma regcntimpl_after_external_preserves_ok: forall st st' pid qb,
  after_external register_counter_impl st pid qb st' ->
  RegCntImplStateWF st ->
  RegCntImplStateWF st'.
Proof.
  inversion 1; intros; subst;
  unfold RegCntImplStateWF in *; intuition;
  apply substitute_preserves_ok; auto.
Qed.

Lemma regcntimpl_step_preserves_ok: forall st st' pid qb,
  step register_counter_impl st pid qb st' ->
  RegCntImplStateWF st ->
  RegCntImplStateWF st'.
Proof.
  inversion 1; intros; subst;
  unfold RegCntImplStateWF in *; intuition;
  apply substitute_preserves_ok; auto.
Qed.

Lemma regcntimpl_ok_inv: invariant_ind register_counter_impl RegCntImplStateWF.
Proof.
  unfold invariant_ind. intuition.
  - inversion H; subst.
    unfold RegCntImplStateWF.
    unfold new_register_counter.
    simpl. constructor.
  - eapply regcntimpl_step_preserves_ok; eauto.
  - eapply regcntimpl_initial_preserves_ok; eauto.
  - eapply regcntimpl_at_external_preserves_ok; eauto.
  - eapply regcntimpl_after_external_preserves_ok; eauto.
  - eapply regcntimpl_final_preserves_ok; eauto.
Qed.

Lemma regcntimpl_valid_execution_preserves_ok: forall st st' acts,
  valid_execution_fragment register_counter_impl st st' acts ->
  RegCntImplStateWF st ->
  RegCntImplStateWF st'.
Proof.
  induction 1; simpl; intros.
  - subst; auto.
  - eapply regcntimpl_step_preserves_ok in H; eauto.
  - eapply regcntimpl_at_external_preserves_ok in H; eauto.
  - eapply regcntimpl_after_external_preserves_ok in H; eauto.
  - eapply regcntimpl_initial_preserves_ok in H; eauto.
  - eapply regcntimpl_final_preserves_ok in H; eauto.
Qed.

Lemma regcntimpl_reachable_inv: forall st,
  reachable register_counter_impl st ->
  RegCntImplStateWF st.
Proof.
  intros. unfold reachable in H.
  destruct H as [init [acts [Hnew Hexe]]].
  eapply regcntimpl_valid_execution_preserves_ok; eauto.
  inversion Hnew; subst.
  unfold new_register_counter.
  unfold RegCntImplStateWF. simpl. intuition; econstructor.
Qed.

Lemma noB_preserves_RInc5: forall (acts : list event) st st' pid,
  valid_execution_fragment register_counter_impl st st' acts ->
  binds pid RInc5 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  binds pid RInc5 st'.(pc).
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

Lemma noB_preserves_RInc2: forall (acts : list event) st st' pid,
  valid_execution_fragment register_counter_impl st st' acts ->
  binds pid RInc2 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  binds pid RInc2 st'.(pc).
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

Lemma noB_preserves_RRead2: forall (acts : list event) st st' pid,
  valid_execution_fragment register_counter_impl st st' acts ->
  binds pid RRead2 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  binds pid RRead2 st'.(pc).
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

End Properties.

Section Refinement.

Import LibEnv.

Fixpoint gather_pos_from_pc pc : env Position :=
  match pc with
  | nil => nil
  | (pid, inst) :: pc' =>
    let pos' := gather_pos_from_pc pc' in
    match inst with
    | RInc2 => (pid, Wait) :: pos'
    | RInc5 => (pid, Wait) :: pos'
    | RRead2 => (pid, Wait) :: pos'
    | _ => (pid, Run) :: pos'
    end
  end.

Lemma gather_pos_from_pc_preserves_notin: forall pc pid,
  pid # pc ->
  pid # (gather_pos_from_pc pc).
Proof.
  induction pc; simpl; intros.
  - assumption.
  - destruct a; simpl in *.
    apply notin_union in H.
    match_if'; simpl; apply notin_union; intuition.
Qed.

Lemma gather_pos_from_pc_preserves_ok: forall pc,
  ok pc ->
  ok (gather_pos_from_pc pc).
Proof.
  induction 1; simpl; intros.
  - econstructor.
  - match_if'; econstructor; eauto;
    apply gather_pos_from_pc_preserves_notin; auto.
Qed.

Lemma gather_pos_from_pc_dist: forall pc pc',
  gather_pos_from_pc (pc ++ pc') =
  gather_pos_from_pc pc ++
  gather_pos_from_pc pc'.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - destruct a; simpl in *.
    match_if'; simpl; rewrite IHpc; auto.
Qed.

Lemma gather_pos_from_pc_remove_comm: forall pc pid,
  gather_pos_from_pc (remove pc pid) =
  remove (gather_pos_from_pc pc) pid.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - destruct a.
    match_if'; simpl; try rewrite IHpc; try discriminate;
    auto.
Qed.

Lemma register_counter_impl_sync: impl_refines register_counter_impl (sync register_counter_impl).
Proof.
  eapply forward_simulation_inv_ind
    with (f:=fun (x : state register_counter_impl) y => x = y.(LState) /\
              sameset (gather_pos_from_pc x.(pc)) y.(PidPos)
          )
          (inv:=fun x => True).
  unfold fsim_properties_inv_ind. intuition.
  - unfold invariant_ind. intuition.
  - inversion H; subst.
    exists (
      mkSyncState
        register_counter_impl
        new_register_counter
        []
    ).
    simpl.
    intuition.
    unfold sync_new_state.
    simpl.
    intuition.
    apply sameset_refl.
    econstructor.
  - exists (
    mkSyncState
      register_counter_impl
      s1'
      ((pid, Run)::s2.(PidPos))
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply sync_initial_state_L; eauto.
    eapply sameset_ok; eauto.
    apply gather_pos_from_pc_preserves_ok; auto.
    inversion H1; subst; simpl; auto.
    eapply notin_sameset; eauto.
    apply gather_pos_from_pc_preserves_notin; auto.
    inversion H1; subst; simpl; auto.
    subst. reflexivity.
    inversion H1; subst; simpl in *;
    rewrite H0 in H3; auto;
    apply sameset_push_eq; auto;
    apply gather_pos_from_pc_preserves_notin; auto.
  - exists (
    mkSyncState
      register_counter_impl
      s1'
      (remove s2.(PidPos) pid)
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply sync_final_state_L; eauto.
    eapply sameset_ok; eauto.
    apply gather_pos_from_pc_preserves_ok; auto.
    inversion H1; subst; simpl; auto.
    rewrite <-H3.
    inversion H1; subst; simpl; auto.
    apply binds_reconstruct in Hbinds;
    destruct Hbinds as [l1 [l2 Hlist]];
    rewrite Hlist;
    rewrite Hlist in Hok_pc;
    apply ok_remove_middle_inv in Hok_pc;
    rewrite gather_pos_from_pc_dist; auto;
    simpl;
    apply binds_concat_left.
    apply binds_push_eq.
    apply gather_pos_from_pc_preserves_notin; intuition.
    apply binds_reconstruct in Hbinds;
    destruct Hbinds as [l1 [l2 Hlist]];
    rewrite Hlist;
    rewrite Hlist in Hok_pc;
    apply ok_remove_middle_inv in Hok_pc;
    rewrite gather_pos_from_pc_dist; auto;
    simpl;
    apply binds_concat_left.
    apply binds_push_eq.
    apply gather_pos_from_pc_preserves_notin; intuition.
    subst. reflexivity.
    rewrite <-H3.
    inversion H1; subst; simpl; auto;
    rewrite H0; simpl;
    rewrite gather_pos_from_pc_remove_comm; auto;
    apply sameset_refl;
    apply remove_preserves_ok;
    apply gather_pos_from_pc_preserves_ok; auto.
  - exists (
    mkSyncState
      register_counter_impl
      s1'
      ((pid, Wait) :: (remove s2.(PidPos) pid))
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply sync_at_external_L; eauto.
    rewrite <-H3.
    apply gather_pos_from_pc_preserves_ok; auto.
    inversion H1; subst; simpl; auto.
    rewrite <-H3.
    inversion H1; subst; simpl; auto.
    apply binds_reconstruct in Hbinds;
    destruct Hbinds as [l1 [l2 Hlist]];
    rewrite Hlist;
    rewrite Hlist in Hok_pc;
    apply ok_remove_middle_inv in Hok_pc;
    rewrite gather_pos_from_pc_dist; auto;
    simpl;
    apply binds_concat_left.
    apply binds_push_eq.
    apply gather_pos_from_pc_preserves_notin; intuition.
    apply binds_reconstruct in Hbinds;
    destruct Hbinds as [l1 [l2 Hlist]];
    rewrite Hlist;
    rewrite Hlist in Hok_pc;
    apply ok_remove_middle_inv in Hok_pc;
    rewrite gather_pos_from_pc_dist; auto;
    simpl;
    apply binds_concat_left.
    apply binds_push_eq.
    apply gather_pos_from_pc_preserves_notin; intuition.
    apply binds_reconstruct in Hbinds;
    destruct Hbinds as [l1 [l2 Hlist]];
    rewrite Hlist;
    rewrite Hlist in Hok_pc;
    apply ok_remove_middle_inv in Hok_pc;
    rewrite gather_pos_from_pc_dist; auto;
    simpl;
    apply binds_concat_left.
    apply binds_push_eq.
    apply gather_pos_from_pc_preserves_notin; intuition.
    subst. reflexivity.
    inversion H1; subst; simpl; auto;
    rewrite H0 in H3; simpl in *;
    apply binds_reconstruct in Hbinds;
    destruct Hbinds as [l1 [l2 Hlist]];
    rewrite Hlist;
    rewrite Hlist in Hok_pc;
    apply ok_remove_middle_inv in Hok_pc;
    intuition;
    rewrite substitute_notin_app; auto;
    simpl; rewrite Nat.eqb_refl;
    rewrite gather_pos_from_pc_dist;
    simpl;
    eapply trans_sameset.
    apply sameset_ExF_xEF;
    apply ok_ExF_xEF;
    rewrite <-gather_pos_from_pc_dist;
    econstructor; eauto.
    apply gather_pos_from_pc_preserves_ok; auto.
    apply gather_pos_from_pc_preserves_notin; auto;
    apply notin_concat; auto.
    apply sameset_push_eq; auto.
    rewrite <-H3.
    rewrite Hlist.
    rewrite gather_pos_from_pc_dist.
    simpl.
    rewrite remove_notin_app; auto.
    simpl.
    rewrite Nat.eqb_refl.
    apply sameset_refl; auto.
    rewrite <-gather_pos_from_pc_dist.
    apply gather_pos_from_pc_preserves_ok; auto.
    apply gather_pos_from_pc_preserves_notin; auto.
    rewrite <-gather_pos_from_pc_dist.
    apply gather_pos_from_pc_preserves_notin; auto.
    apply notin_concat; auto.
    apply sameset_ExF_xEF;
    apply ok_ExF_xEF;
    rewrite <-gather_pos_from_pc_dist;
    econstructor; eauto.
    apply gather_pos_from_pc_preserves_ok; auto.
    apply gather_pos_from_pc_preserves_notin; auto;
    apply notin_concat; auto.
    apply sameset_push_eq; auto.
    rewrite <-H3.
    rewrite Hlist.
    rewrite gather_pos_from_pc_dist.
    simpl.
    rewrite remove_notin_app; auto.
    simpl.
    rewrite Nat.eqb_refl.
    apply sameset_refl; auto.
    rewrite <-gather_pos_from_pc_dist.
    apply gather_pos_from_pc_preserves_ok; auto.
    apply gather_pos_from_pc_preserves_notin; auto.
    rewrite <-gather_pos_from_pc_dist.
    apply gather_pos_from_pc_preserves_notin; auto.
    apply notin_concat; auto.
    apply sameset_ExF_xEF;
    apply ok_ExF_xEF;
    rewrite <-gather_pos_from_pc_dist;
    econstructor; eauto.
    apply gather_pos_from_pc_preserves_ok; auto.
    apply gather_pos_from_pc_preserves_notin; auto;
    apply notin_concat; auto.
    apply sameset_push_eq; auto.
    rewrite <-H3.
    rewrite Hlist.
    rewrite gather_pos_from_pc_dist.
    simpl.
    rewrite remove_notin_app; auto.
    simpl.
    rewrite Nat.eqb_refl.
    apply sameset_refl; auto.
    rewrite <-gather_pos_from_pc_dist.
    apply gather_pos_from_pc_preserves_ok; auto.
    apply gather_pos_from_pc_preserves_notin; auto.
    rewrite <-gather_pos_from_pc_dist.
    apply gather_pos_from_pc_preserves_notin; auto.
    apply notin_concat; auto.
  - exists (
    mkSyncState
      register_counter_impl
      s1'
      ((pid, Run) :: (remove s2.(PidPos) pid))
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply sync_after_external_L; eauto.
    rewrite <-H3.
    apply gather_pos_from_pc_preserves_ok; auto.
    inversion H1; subst; simpl; auto.
    rewrite <-H3.
    inversion H1; subst; simpl; auto.
    apply binds_reconstruct in Hbinds;
    destruct Hbinds as [l1 [l2 Hlist]];
    rewrite Hlist;
    rewrite Hlist in Hok_pc;
    apply ok_remove_middle_inv in Hok_pc;
    rewrite gather_pos_from_pc_dist; auto;
    simpl;
    apply binds_concat_left.
    apply binds_push_eq.
    apply gather_pos_from_pc_preserves_notin; intuition.
    apply binds_reconstruct in Hbinds;
    destruct Hbinds as [l1 [l2 Hlist]];
    rewrite Hlist;
    rewrite Hlist in Hok_pc;
    apply ok_remove_middle_inv in Hok_pc;
    rewrite gather_pos_from_pc_dist; auto;
    simpl;
    apply binds_concat_left.
    apply binds_push_eq.
    apply gather_pos_from_pc_preserves_notin; intuition.
    apply binds_reconstruct in Hbinds;
    destruct Hbinds as [l1 [l2 Hlist]];
    rewrite Hlist;
    rewrite Hlist in Hok_pc;
    apply ok_remove_middle_inv in Hok_pc;
    rewrite gather_pos_from_pc_dist; auto;
    simpl;
    apply binds_concat_left.
    apply binds_push_eq.
    apply gather_pos_from_pc_preserves_notin; intuition.
    subst. reflexivity.
    inversion H1; subst; simpl; auto;
    rewrite H0 in H3; simpl in *;
    apply binds_reconstruct in Hbinds;
    destruct Hbinds as [l1 [l2 Hlist]];
    rewrite Hlist;
    rewrite Hlist in Hok_pc;
    apply ok_remove_middle_inv in Hok_pc;
    intuition;
    rewrite substitute_notin_app; auto;
    simpl; rewrite Nat.eqb_refl;
    rewrite gather_pos_from_pc_dist;
    simpl;
    eapply trans_sameset.
    apply sameset_ExF_xEF;
    apply ok_ExF_xEF;
    rewrite <-gather_pos_from_pc_dist;
    econstructor; eauto.
    apply gather_pos_from_pc_preserves_ok; auto.
    apply gather_pos_from_pc_preserves_notin; auto;
    apply notin_concat; auto.
    apply sameset_push_eq; auto.
    rewrite <-H3.
    rewrite Hlist.
    rewrite gather_pos_from_pc_dist.
    simpl.
    rewrite remove_notin_app; auto.
    simpl.
    rewrite Nat.eqb_refl.
    apply sameset_refl; auto.
    rewrite <-gather_pos_from_pc_dist.
    apply gather_pos_from_pc_preserves_ok; auto.
    apply gather_pos_from_pc_preserves_notin; auto.
    rewrite <-gather_pos_from_pc_dist.
    apply gather_pos_from_pc_preserves_notin; auto.
    apply notin_concat; auto.
    apply sameset_ExF_xEF;
    apply ok_ExF_xEF;
    rewrite <-gather_pos_from_pc_dist;
    econstructor; eauto.
    apply gather_pos_from_pc_preserves_ok; auto.
    apply gather_pos_from_pc_preserves_notin; auto;
    apply notin_concat; auto.
    apply sameset_push_eq; auto.
    rewrite <-H3.
    rewrite Hlist.
    rewrite gather_pos_from_pc_dist.
    simpl.
    rewrite remove_notin_app; auto.
    simpl.
    rewrite Nat.eqb_refl.
    apply sameset_refl; auto.
    rewrite <-gather_pos_from_pc_dist.
    apply gather_pos_from_pc_preserves_ok; auto.
    apply gather_pos_from_pc_preserves_notin; auto.
    rewrite <-gather_pos_from_pc_dist.
    apply gather_pos_from_pc_preserves_notin; auto.
    apply notin_concat; auto.
    apply sameset_ExF_xEF;
    apply ok_ExF_xEF;
    rewrite <-gather_pos_from_pc_dist;
    econstructor; eauto.
    apply gather_pos_from_pc_preserves_ok; auto.
    apply gather_pos_from_pc_preserves_notin; auto;
    apply notin_concat; auto.
    apply sameset_push_eq; auto.
    rewrite <-H3.
    rewrite Hlist.
    rewrite gather_pos_from_pc_dist.
    simpl.
    rewrite remove_notin_app; auto.
    simpl.
    rewrite Nat.eqb_refl.
    apply sameset_refl; auto.
    rewrite <-gather_pos_from_pc_dist.
    apply gather_pos_from_pc_preserves_ok; auto.
    apply gather_pos_from_pc_preserves_notin; auto.
    rewrite <-gather_pos_from_pc_dist.
    apply gather_pos_from_pc_preserves_notin; auto.
    apply notin_concat; auto.
  - exists (
    mkSyncState
      register_counter_impl
      s1'
      (s2.(PidPos))
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply Step_Internal; eauto.
    2 : {
      eapply Step_None; eauto.
    }
    eapply sync_step_L_internal; eauto.
    rewrite <-H3.
    apply gather_pos_from_pc_preserves_ok; auto.
    inversion H1; subst; simpl; auto.
    rewrite <-H3.
    inversion H1; subst; simpl; auto.
    apply binds_reconstruct in Hbinds;
    destruct Hbinds as [l1 [l2 Hlist]];
    rewrite Hlist;
    rewrite Hlist in Hok_pc;
    apply ok_remove_middle_inv in Hok_pc;
    rewrite gather_pos_from_pc_dist; auto;
    simpl;
    apply binds_concat_left.
    apply binds_push_eq.
    apply gather_pos_from_pc_preserves_notin; intuition.
    apply binds_reconstruct in Hbinds;
    destruct Hbinds as [l1 [l2 Hlist]];
    rewrite Hlist;
    rewrite Hlist in Hok_pc;
    apply ok_remove_middle_inv in Hok_pc;
    rewrite gather_pos_from_pc_dist; auto;
    simpl;
    apply binds_concat_left.
    apply binds_push_eq.
    apply gather_pos_from_pc_preserves_notin; intuition.
    apply binds_reconstruct in Hbinds;
    destruct Hbinds as [l1 [l2 Hlist]];
    rewrite Hlist;
    rewrite Hlist in Hok_pc;
    apply ok_remove_middle_inv in Hok_pc;
    rewrite gather_pos_from_pc_dist; auto;
    simpl;
    apply binds_concat_left.
    apply binds_push_eq.
    apply gather_pos_from_pc_preserves_notin; intuition.
    subst. reflexivity.
    rewrite <-H3.
    inversion H1; subst; simpl; auto;
    rewrite H0; simpl;
    apply binds_reconstruct in Hbinds;
    destruct Hbinds as [l1 [l2 Hlist]];
    rewrite Hlist;
    rewrite Hlist in Hok_pc;
    apply ok_remove_middle_inv in Hok_pc;
    intuition;
    rewrite substitute_notin_app; auto;
    simpl; rewrite Nat.eqb_refl;

    rewrite gather_pos_from_pc_dist;
    simpl;
    rewrite gather_pos_from_pc_dist;
    simpl;
    apply sameset_refl; auto;
    apply ok_ExF_xEF;
    rewrite <-gather_pos_from_pc_dist;
    econstructor; eauto.
    apply gather_pos_from_pc_preserves_ok; auto.
    apply gather_pos_from_pc_preserves_notin; auto;
    apply notin_concat; auto.
    apply gather_pos_from_pc_preserves_ok; auto.
    apply gather_pos_from_pc_preserves_notin; auto;
    apply notin_concat; auto.
    apply gather_pos_from_pc_preserves_ok; auto.
    apply gather_pos_from_pc_preserves_notin; auto;
    apply notin_concat; auto.
Qed.

End Refinement.