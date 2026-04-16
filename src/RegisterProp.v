Require Import
  List
  Arith
  LibVar
  LibEnv
  LTS
  SyncLTS
  Refinement
  Register.
From VCO Require LibEnv.
Import ListNotations.

Section INV.

Import LibEnv.

Lemma register_step_inv: invariant_ind (sync Register) (inv Register).
Proof.
  apply step_inv.
Qed.

End INV.

Section Properties.

Lemma reg_step_preserves_notin_inv: forall s s' pid int pid',
  step Register s pid int s' ->
  pid' # s.(requests) ->
  pid' # s'.(requests).
Proof.
  intros.
  inversion H; subst; simpl in *.
  apply remove_preserves_notin; auto.
  apply remove_preserves_notin; auto.
Qed.

Lemma reg_initial_preserves_notin_inv: forall s s' pid int pid',
  initial_state Register s pid int s' ->
  pid <> pid' ->
  pid' # s.(requests) ->
  pid' # s'.(requests).
Proof.
  intros.
  inversion H; subst; simpl in *.
  apply notin_union; auto. intuition.
  apply notin_neq; auto.
  apply notin_union; auto. intuition.
  apply notin_neq; auto.
Qed.

Lemma reg_final_preserves_notin_inv: forall s s' pid int pid',
  final_state Register s pid int s' ->
  pid' # s.(requests) ->
  pid' # s'.(requests).
Proof.
  intros.
  inversion H; subst; simpl in *; auto.
Qed.

Lemma internal_preserves_notin: forall acts pid st st',
  valid_execution_fragment Register st st' acts ->
  gather_pid_external_events acts pid = [] ->
  pid # st.(requests) ->
  pid # st'.(requests).
Proof.
  induction 1; intros.
  - subst. assumption.
  - apply IHvalid_execution_fragment; auto.
    eapply reg_step_preserves_notin_inv; eauto.
  - destruct qa.
  - destruct ra.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      eapply reg_initial_preserves_notin_inv; eauto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      eapply reg_final_preserves_notin_inv; eauto.
Qed.

Lemma reg_step_preserves_binds_inv: forall s s' pid int q pid',
  step Register s pid int s' ->
  pid <> pid' ->
  binds pid' q s.(requests) ->
  binds pid' q s'.(requests).
Proof.
  intros.
  inversion H; subst; simpl in *.
  apply remove_neq_preserves_binds; auto.
  apply remove_neq_preserves_binds; auto.
Qed.

Lemma reg_initial_preserves_binds_inv: forall s s' pid int q pid',
  initial_state Register s pid int s' ->
  binds pid' q s.(requests) ->
  binds pid' q s'.(requests).
Proof.
  intros.
  inversion H; subst; simpl in *.
  unfold binds. simpl.
  destruct (pid' =? pid)eqn:Heq.
  apply Nat.eqb_eq in Heq.
  subst. apply binds_in in H0.
  unfold "#" in Hnotin_inv.
  intuition.
  assumption.
  inversion H; subst; simpl in *.
  unfold binds. simpl.
  destruct (pid' =? pid)eqn:Heq.
  apply Nat.eqb_eq in Heq.
  subst. apply binds_in in H0.
  unfold "#" in Hnotin_inv.
  intuition.
  assumption.
Qed.

Lemma internal_preserves_request: forall acts pid st st' qb qb',
  valid_execution_fragment Register st st' acts ->
  gather_pid_external_events acts pid = [] ->
  binds pid qb st.(requests) ->
  binds pid qb' st'.(requests) ->
  qb = qb'.
Proof.
  induction 1; intros.
  - subst. eapply binds_same; eauto.
  - eapply IHvalid_execution_fragment; eauto.
    destruct (pid =? pid0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst.
      assert (pid0 # st'.(requests)).
      eapply internal_preserves_notin; eauto.
      inversion H; subst; simpl in *.
      apply ok_remove_notin; auto.
      apply ok_remove_notin; auto.
      apply binds_in in H3.
      unfold "#" in H4.
      intuition.
    --
      apply Nat.eqb_neq in Heq.
      eapply reg_step_preserves_binds_inv; eauto.
  - destruct qa.
  - destruct ra.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      eapply reg_initial_preserves_binds_inv; eauto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      inversion H; subst; intuition.
Qed.

End Properties.

Section INV.

Definition register_exclusive_wf (s : state Register) :=
  forall pid,
    (pid \in dom s.(requests) ->
    pid # s.(responses)) /\
    (pid \in dom s.(requests) ->
    pid # s.(responses)).

Lemma register_exclusive_wf_inv: invariant_ind Register register_exclusive_wf.
Proof.
  unfold invariant_ind. intuition.
  - inversion H; subst.
    unfold new_register.
    unfold register_exclusive_wf.
    simpl.
    intuition.
  - inversion H0; subst; clear H0.
    -- unfold register_exclusive_wf in *;
      simpl in *; intuition.
      --- destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove inv pid)).
        apply ok_remove_notin; auto.
        unfold "#" in H1.
        intuition.
        apply notin_union.
        intuition.
        apply notin_neq; auto.
        apply remove_neq_preserves_in in H0; auto.
        apply H in H0; auto.
      --- destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove inv pid)).
        apply ok_remove_notin; auto.
        unfold "#" in H1.
        intuition.
        apply notin_union.
        intuition.
        apply notin_neq; auto.
        apply remove_neq_preserves_in in H0; auto.
        apply H in H0; auto.
    -- unfold register_exclusive_wf in *;
      simpl in *; intuition.
      --- destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove inv pid)).
        apply ok_remove_notin; auto.
        unfold "#" in H1.
        intuition.
        apply notin_union.
        intuition.
        apply notin_neq; auto.
        apply remove_neq_preserves_in in H0; auto.
        apply H in H0; auto.
      --- destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove inv pid)).
        apply ok_remove_notin; auto.
        unfold "#" in H1.
        intuition.
        apply notin_union.
        intuition.
        apply notin_neq; auto.
        apply remove_neq_preserves_in in H0; auto.
        apply H in H0; auto.
  - inversion H0; subst; clear H0.
    -- unfold register_exclusive_wf in *;
      simpl in *; intuition;
      apply in_union in H0;
      intuition;
      simpl in H1; intuition;
      subst; auto;
      apply H in H1; auto.
    -- unfold register_exclusive_wf in *;
      simpl in *; intuition;
      apply in_union in H0;
      intuition;
      simpl in H1; intuition;
      subst; auto;
      apply H in H1; auto.
  - destruct act.
  - destruct act.
  - inversion H0; subst; clear H0.
    -- unfold register_exclusive_wf in *;
      simpl in *; intuition;
      apply H in H0;
      destruct (eq_nat_dec pid0 pid);
      subst;
      apply binds_in in Hbinds;
      unfold "#" in H0; intuition;
      apply remove_preserves_notin; auto.
    -- unfold register_exclusive_wf in *;
      simpl in *; intuition;
      apply H in H0;
      destruct (eq_nat_dec pid0 pid);
      subst;
      apply binds_in in Hbinds;
      unfold "#" in H0; intuition;
      apply remove_preserves_notin; auto.
Qed.

End INV.

Section Refinement.

Import LibEnv.

Lemma register_sync: refines Register (sync Register).
Proof.
  eapply forward_simulation_inv_ind
    with (f:=fun (x : state Register) y => x = y.(LState) /\
              (forall pid, 
                (pid \in dom x.(requests) ->
                binds pid Run y.(PidPos)) /\
                (pid \in dom x.(responses) ->
                binds pid Run y.(PidPos)) /\
                (pid # x.(requests)->
                  pid # x.(responses) ->
                  pid # y.(PidPos))
              ) /\
              ok y.(PidPos)
          )
          (inv:=register_exclusive_wf).
  unfold fsim_properties_inv_ind. intuition.
  - apply register_exclusive_wf_inv.
  - inversion H; subst.
    exists (
      mkSyncState
        Register
        new_register
        []
    ).
    simpl.
    intuition.
    unfold sync_new_state.
    simpl.
    intuition.
    econstructor.
  - exists (
    mkSyncState
      Register
      s1'
      ((pid, Run)::s2.(PidPos))
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply sync_initial_state_L; eauto.
    apply H0.
    inversion H1; subst; simpl; auto.
    inversion H1; subst; simpl; auto.
    rewrite H2. reflexivity.
    destruct (eq_nat_dec pid0 pid).
    subst.
    apply binds_push_eq.
    apply binds_push_neq; auto.
    specialize (H0 pid0). intuition.
    apply H5.
    inversion H1; subst; simpl; auto;
    rewrite H6; simpl in *;
    apply in_union in H3; intuition;
    apply notin_neq in H2; intuition.
    destruct (eq_nat_dec pid0 pid).
    subst.
    apply binds_push_eq.
    apply binds_push_neq; auto.
    specialize (H0 pid0). intuition.
    apply H0.
    inversion H1; subst; simpl; auto;
    rewrite H6; simpl in *; auto.
    apply notin_union. intuition.
    apply notin_neq.
    intro.
    subst.
    inversion H1; subst; simpl in *;
    apply notin_union in H3;
    destruct H3 as [Htmp _];
    apply notin_neq in Htmp; intuition.
    apply H0; auto.
    inversion H1; subst; simpl in *;
    apply notin_union in H3;
    rewrite H6; simpl in *; intuition.
    inversion H1; subst; simpl in *;
    apply notin_union in H3;
    rewrite H6; simpl in *; intuition.
    econstructor; eauto.
    apply H0;
    inversion H1; subst; simpl in *;
    rewrite H3; simpl; auto.
  - exists (
    mkSyncState
      Register
      s1'
      (remove s2.(PidPos) pid)
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply sync_final_state_L; eauto.
    apply H0.
    2 : {
      rewrite H2. reflexivity.
    }
    5 : {
      apply remove_preserves_ok; auto.
    }
    inversion H1; subst; simpl; auto;
    apply binds_in in Hbinds; auto.
    destruct (eq_nat_dec pid0 pid).
    subst.
    inversion H1; subst; simpl in *;
    destruct s2; simpl in *;
    destruct LState; simpl in *;
    inversion H2; subst; clear H2;
    apply H in H3; simpl in *;
    apply binds_in in Hbinds;
    unfold "#" in H3; intuition.
    inversion H1; subst; simpl in *;
    destruct s2; simpl in *;
    destruct LState; simpl in *;
    inversion H5; subst; clear H5;
    apply H0 in H3;
    apply remove_neq_preserves_binds; auto.
    destruct (eq_nat_dec pid0 pid).
    subst.
    inversion H1; subst; simpl in *;
    destruct s2; simpl in *;
    destruct LState; simpl in *;
    inversion H2; subst; clear H2;
    assert (pid # (remove res pid)) by
    (apply ok_remove_notin; auto);
    unfold "#" in H2; intuition.
    inversion H1; subst; simpl in *;
    destruct s2; simpl in *;
    destruct LState; simpl in *;
    inversion H5; subst; clear H5;
    apply remove_neq_preserves_in in H3; auto;
    apply H0 in H3;
    apply remove_neq_preserves_binds; auto.
    destruct (eq_nat_dec pid0 pid).
    subst.
    apply ok_remove_notin; auto.
    apply remove_preserves_notin; auto.
    apply H0;
    subst;
    inversion H1; subst;
    rewrite H2; simpl in *; auto.
    apply remove_neq_preserves_notin in H5; auto.
    apply remove_neq_preserves_notin in H5; auto.
  - exists (
    mkSyncState
      Register
      s1'
      (s2.(PidPos))
    ).
    simpl. intuition.
    eapply Step_Internal; eauto.
    eapply sync_step_L_internal; eauto.
    subst.
    inversion H1; subst; simpl in *;
    destruct s2; simpl in *;
    destruct LState; simpl in *;
    inversion H2; subst; clear H2;
    apply binds_in in Hbinds;
    apply H0 in Hbinds; auto.
    destruct s2. simpl in *.
    subst. reflexivity.
    eapply Step_None; eauto.
    subst.
    inversion H1; subst;
    destruct s2; simpl in *;
    destruct LState; simpl in *;
    inversion H2; subst; clear H2;
    destruct (eq_nat_dec pid0 pid);
    subst; apply binds_in in Hbinds;
    apply H0 in Hbinds; intuition;
    apply remove_neq_preserves_in in H3; auto;
    apply H0 in H3; intuition.
    inversion H1; subst;
    destruct s2; simpl in *;
    destruct LState; simpl in *;
    inversion H5; subst; clear H5;
    apply in_union in H3; simpl in *;
    intuition;
    subst;
    apply binds_in in Hbinds;
    apply H0 in Hbinds; auto;
    apply H0 in H2; auto.
    inversion H1; subst;
    destruct s2; simpl in *;
    destruct LState; simpl in *;
    inversion H6; subst; clear H6;
    apply notin_union in H5;
    intuition;
    apply notin_neq in H2;
    apply remove_neq_preserves_notin in H3; auto;
    apply H0; auto.
Qed.

End Refinement.