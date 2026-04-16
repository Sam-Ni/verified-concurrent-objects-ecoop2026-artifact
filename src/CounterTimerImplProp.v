Require Import
  Arith
  List
  LibEnv
  LTS
  Timer
  Counter
  LibVar
  CounterTimerImpl
.
Require 
  LibEnv.
Import ListNotations.

Section Properties.

Import LibEnv.

Definition CntTmImplStateWF st :=
  ok st.(pc).

Lemma cnttmimpl_initial_preserves_ok: forall st st' pid qb,
  initial_state counter_timer_impl st pid qb st' ->
  CntTmImplStateWF st ->
  CntTmImplStateWF st'.
Proof.
  inversion 1; intros; subst;
  unfold CntTmImplStateWF; simpl; intuition;
  econstructor; eauto.
Qed.

Lemma cnttmimpl_final_preserves_ok: forall st st' pid qb,
  final_state counter_timer_impl st pid qb st' ->
  CntTmImplStateWF st ->
  CntTmImplStateWF st'.
Proof.
  inversion 1; intros; subst;
  unfold CntTmImplStateWF in *; intuition;
  simpl; apply remove_preserves_ok; auto.
Qed.

Lemma cnttmimpl_at_external_preserves_ok: forall st st' pid qb,
  at_external counter_timer_impl st pid qb st' ->
  CntTmImplStateWF st ->
  CntTmImplStateWF st'.
Proof.
  inversion 1; intros; subst;
  unfold CntTmImplStateWF in *; intuition; simpl in *;
  apply substitute_preserves_ok; auto.
Qed.

Lemma cnttmimpl_after_external_preserves_ok: forall st st' pid qb,
  after_external counter_timer_impl st pid qb st' ->
  CntTmImplStateWF st ->
  CntTmImplStateWF st'.
Proof.
  inversion 1; intros; subst;
  unfold CntTmImplStateWF in *; intuition;
  apply substitute_preserves_ok; auto.
Qed.

Lemma cnttmimpl_step_preserves_ok: forall st st' pid qb,
  step counter_timer_impl st pid qb st' ->
  CntTmImplStateWF st ->
  CntTmImplStateWF st'.
Proof.
  inversion 1; intros; subst;
  unfold RegCntImplStateWF in *; intuition;
  apply substitute_preserves_ok; auto.
Qed.

Lemma cnttmimpl_ok_inv: invariant_ind counter_timer_impl CntTmImplStateWF.
Proof.
  unfold invariant_ind. intuition.
  - inversion H; subst.
    unfold CntTmImplStateWF.
    unfold new_counter_timer.
    simpl. constructor.
  - eapply cnttmimpl_step_preserves_ok; eauto.
  - eapply cnttmimpl_initial_preserves_ok; eauto.
  - eapply cnttmimpl_at_external_preserves_ok; eauto.
  - eapply cnttmimpl_after_external_preserves_ok; eauto.
  - eapply cnttmimpl_final_preserves_ok; eauto.
Qed.

Lemma cnttmimpl_valid_execution_preserves_ok: forall st st' acts,
  valid_execution_fragment counter_timer_impl st st' acts ->
  CntTmImplStateWF st ->
  CntTmImplStateWF st'.
Proof.
  induction 1; simpl; intros.
  - subst; auto.
  - eapply cnttmimpl_step_preserves_ok in H; eauto.
  - eapply cnttmimpl_at_external_preserves_ok in H; eauto.
  - eapply cnttmimpl_after_external_preserves_ok in H; eauto.
  - eapply cnttmimpl_initial_preserves_ok in H; eauto.
  - eapply cnttmimpl_final_preserves_ok in H; eauto.
Qed.

Lemma noB_preserves_CTick2: forall (acts : list event) st st' pid,
  valid_execution_fragment counter_timer_impl st st' acts ->
  binds pid CTick2 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  binds pid CTick2 st'.(pc).
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

Lemma noB_preserves_CRead2: forall (acts : list event) st st' pid,
  valid_execution_fragment counter_timer_impl st st' acts ->
  binds pid CRead2 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  binds pid CRead2 st'.(pc).
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