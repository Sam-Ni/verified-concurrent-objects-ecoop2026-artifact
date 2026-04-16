Require Import
  List
  Arith
  LibVar
  LibEnv
  LTS
  SyncLTS
  Counter
  Refinement.
From VCO Require LibEnv.
Import ListNotations.

Section INV.

Import LibEnv.

Lemma counter_step_inv: invariant_ind (sync counter) (inv counter).
Proof.
  apply step_inv.
Qed.

End INV.

Section Properties.

Lemma cnt_step_preserves_notin_inv: forall s s' pid int pid',
  step counter s pid int s' ->
  pid' # s.(requests) ->
  pid' # s'.(requests).
Proof.
  intros.
  inversion H; subst; simpl in *.
  apply remove_preserves_notin; auto.
  apply remove_preserves_notin; auto.
Qed.

Lemma cnt_initial_preserves_notin_inv: forall s s' pid int pid',
  initial_state counter s pid int s' ->
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

Lemma cnt_final_preserves_notin_inv: forall s s' pid int pid',
  final_state counter s pid int s' ->
  pid' # s.(requests) ->
  pid' # s'.(requests).
Proof.
  intros.
  inversion H; subst; simpl in *; auto.
Qed.

Lemma internal_preserves_notin: forall acts pid st st',
  valid_execution_fragment counter st st' acts ->
  gather_pid_external_events acts pid = [] ->
  pid # st.(requests) ->
  pid # st'.(requests).
Proof.
  induction 1; intros.
  - subst. assumption.
  - apply IHvalid_execution_fragment; auto.
    eapply cnt_step_preserves_notin_inv; eauto.
  - destruct qa.
  - destruct ra.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      apply Nat.eqb_neq in Heq.
      eapply cnt_initial_preserves_notin_inv; eauto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      eapply cnt_final_preserves_notin_inv; eauto.
Qed.

Lemma cnt_step_preserves_binds_inv: forall s s' pid int q pid',
  step counter s pid int s' ->
  pid <> pid' ->
  binds pid' q s.(requests) ->
  binds pid' q s'.(requests).
Proof.
  intros.
  inversion H; subst; simpl in *.
  apply remove_neq_preserves_binds; auto.
  apply remove_neq_preserves_binds; auto.
Qed.

Lemma cnt_initial_preserves_binds_inv: forall s s' pid int q pid',
  initial_state counter s pid int s' ->
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
  valid_execution_fragment counter st st' acts ->
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
      eapply cnt_step_preserves_binds_inv; eauto.
  - destruct qa.
  - destruct ra.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      eapply cnt_initial_preserves_binds_inv; eauto.
  - simpl in H1.
    destruct (pid =? pid0)eqn:Heq.
    -- discriminate.
    -- apply IHvalid_execution_fragment; auto.
      inversion H; subst; intuition.
Qed.

End Properties.

Section INV.

Definition counter_exclusive_wf (s : state counter) :=
  forall pid,
    (pid \in dom s.(requests) ->
    pid # s.(responses)) /\
    (pid \in dom s.(responses) ->
    pid # s.(requests)).

Lemma counter_exclusive_wf_inv: invariant_ind counter counter_exclusive_wf.
Proof.
  unfold invariant_ind. intuition.
  - inversion H; subst.
    unfold new_counter.
    unfold counter_exclusive_wf.
    simpl.
    intuition.
  - inversion H0; subst; clear H0.
    -- unfold counter_exclusive_wf in *;
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
        apply H.
        eapply remove_neq_preserves_in; eauto.
      --- apply in_union in H0.
        simpl in H0. intuition.
        subst. apply ok_remove_notin; auto.
        apply remove_preserves_notin.
        apply H; auto.
    -- unfold counter_exclusive_wf in *;
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
        apply H.
        eapply remove_neq_preserves_in; eauto.
      --- apply in_union in H0.
        simpl in H0. intuition.
        subst. apply ok_remove_notin; auto.
        apply remove_preserves_notin.
        apply H; auto.
  - unfold counter_exclusive_wf in *.
    inversion H0; subst; simpl in *; intros.
    -- intuition.
      --- apply in_union in H1.
        simpl in H1.
        intuition.
        subst. auto.
        apply H; auto.
      --- apply notin_union.
        destruct (eq_nat_dec pid0 pid).
        subst. unfold "#" in Hnotin_res.
        intuition.
        intuition.
        apply notin_neq; auto.
        apply H; auto.
    -- intuition.
      --- apply in_union in H1.
        simpl in H1.
        intuition.
        subst. auto.
        apply H; auto.
      --- apply notin_union.
        destruct (eq_nat_dec pid0 pid).
        subst. unfold "#" in Hnotin_res.
        intuition.
        intuition.
        apply notin_neq; auto.
        apply H; auto.
  - destruct act.
  - destruct act.
  - unfold counter_exclusive_wf in *.
    inversion H0; subst; simpl in *; intros.
    -- intuition.
      --- destruct (eq_nat_dec pid0 pid).
        subst.
        apply ok_remove_notin; auto.
        apply remove_preserves_notin.
        apply H; auto.
      --- destruct (eq_nat_dec pid0 pid).
        subst. apply H; auto.
        apply binds_in in Hbinds; auto.
        apply remove_neq_preserves_in in H1; auto.
        apply H; auto.
    -- intuition.
      --- destruct (eq_nat_dec pid0 pid).
        subst.
        apply ok_remove_notin; auto.
        apply remove_preserves_notin.
        apply H; auto.
      --- destruct (eq_nat_dec pid0 pid).
        subst. apply H; auto.
        apply binds_in in Hbinds; auto.
        apply remove_neq_preserves_in in H1; auto.
        apply H; auto.
Qed.
  
End INV.

Section Refinement.

Import LibEnv.

Lemma counter_sync: refines counter (sync counter).
Proof.
  eapply forward_simulation_inv_ind
    with (f:=fun (x : state counter) y => x = y.(LState) /\
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
          (inv:=counter_exclusive_wf).
  unfold fsim_properties_inv_ind. intuition.
  - apply counter_exclusive_wf_inv.
  - inversion H; subst.
    exists (
      mkSyncState
        counter
        new_counter
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
      counter
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
      counter
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
      counter
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
