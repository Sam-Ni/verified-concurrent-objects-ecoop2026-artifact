Require Import
  List
  Arith
  LibEnv
  LTS
  SyncLTS
  Compose
  Invariants
.
Import ListNotations.

Section INV.

Context {liA liB : language_interface}.
Variable L1 : lts li_null liA.
Variable L2 : lts liA liB.
Local Definition L := (compose L1 L2).

Definition inv s :=
  forall pid,
    binds pid Run s.(L1State).(PidPos) ->
    exists s1 s2 q acts,
      composed_lts.internal_query L s1 pid q s2 /\
      composed_lts.valid_execution_fragment L s2 s acts /\
      gather_pid_events_B pid acts = []
.

Lemma step_inv : composed_lts.invariant_ind L inv.
Proof.
  unfold composed_lts.invariant_ind. intuition.
  - inversion H; subst.
    unfold inv. intros.
    inversion H0; subst.
    rewrite H4 in H2.
    inversion H2.
  - unfold inv in *. intros.
    destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst. inversion H0; subst; simpl in *.
      --- inversion H2; subst.
        simpl in *.
        apply H in H1; auto.
        destruct H1 as [s1 [s2 [q [acts [Hiq [Hvalid Hgather]]]]]].
        exists s1, s2, q, acts.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
        eapply composed_lts.Step_Internal_L1; eauto.
        eapply composed_lts.Step_None; eauto.
        rewrite app_nil_r.
        reflexivity.
    -- inversion H0; subst; simpl in *.
      --- inversion H2; subst; simpl in *.
        apply H in H1; auto.
        destruct H1 as [s1 [s2 [q [acts [Hiq [Hvalid Hgather]]]]]].
        exists s1, s2, q, acts.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
        eapply composed_lts.Step_Internal_L1; eauto.
        eapply composed_lts.Step_None; eauto.
        rewrite app_nil_r.
        reflexivity.
  - unfold inv in *. intros.
    destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst. inversion H0; subst; simpl in *.
      --- apply binds_in in H1.
        unfold "#" in Hnotin. intuition.
    -- inversion H0; subst; simpl in *.
      --- apply H in H1; auto.
        destruct H1 as [s1 [s2 [q [acts [Hiq [Hvalid Hgather]]]]]].
        exists s1, s2, q, acts.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
        eapply composed_lts.Step_Internal_L2; eauto.
        eapply composed_lts.Step_None; eauto.
        rewrite app_nil_r.
        reflexivity.
  - unfold inv in *. intros.
    destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst. inversion H0; subst.
      simpl in *.
      apply binds_in in H1.
      unfold "#" in Hnotin.
      intuition.
    -- inversion H0; subst.
      simpl in *.
      apply H in H1; auto.
      destruct H1 as [s1 [s2 [q [acts [Hiq [Hvalid Hgather]]]]]].
      exists s1, s2, q, (acts ++ [(pid, composed_lts.event_invC act)]).
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
      eapply composed_lts.Step_Initial_Call; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      rewrite Heq.
      rewrite app_nil_r.
      assumption.
  - destruct act.
  - destruct act.
  - unfold inv in *. intros.
    destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst. inversion H0; subst.
      simpl in *.
      apply H in H1.
      destruct H1 as [s1 [s2 [q [acts [Hiq [Hvalid Hgather]]]]]].
      exists s1, s2, q, (acts ++ [(pid, composed_lts.event_resC act)]).
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
      eapply composed_lts.Step_Final_Return; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist.
      simpl. rewrite Nat.eqb_refl.
      rewrite app_nil_r.
      assumption.
    -- inversion H0; subst.
      simpl in *.
      apply H in H1; auto.
      destruct H1 as [s1 [s2 [q [acts [Hiq [Hvalid Hgather]]]]]].
      exists s1, s2, q, (acts ++ [(pid, composed_lts.event_resC act)]).
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
      eapply composed_lts.Step_Final_Return; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      rewrite Heq.
      rewrite app_nil_r.
      assumption.
  - unfold inv in *. intros.
    destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst.
      exists st, st', act, [].
      intuition.
      eapply composed_lts.Step_None; eauto.
    -- inversion H0; subst.
      simpl in *.
      inversion H3; subst.
      simpl in *.
      apply binds_push_neq_inv in H1; auto.
      apply H in H1; auto.
      destruct H1 as [s1 [s2 [q [acts [Hiq [Hvalid Hgather]]]]]].
      exists s1, s2, q, (acts ++ [(pid, composed_lts.event_invB act)]).
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
      eapply composed_lts.Step_Internal_Query; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      rewrite Heq.
      rewrite app_nil_r.
      assumption.
      apply Nat.eqb_neq; intuition.
  - unfold inv in *. intros.
    destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst.
      inversion H0; subst.
      simpl in *.
      inversion H2; subst.
      simpl in *.
      assert (pid # (remove pos pid)).
      apply ok_remove_notin; auto.
      apply binds_in in H1.
      unfold "#" in H5.
      intuition.
    -- inversion H0; subst.
      simpl in *.
      inversion H2; subst.
      simpl in *.
      apply remove_preserves_binds_notin in H1; auto.
      apply H in H1; auto.
      destruct H1 as [s1 [s2 [q [acts [Hiq [Hvalid Hgather]]]]]].
      exists s1, s2, q, (acts ++ [(pid, composed_lts.event_resB act)]).
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
      eapply composed_lts.Step_Internal_Reply; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      rewrite Heq.
      rewrite app_nil_r.
      assumption.
      apply Nat.eqb_neq; intuition.
Qed.

Lemma step_invariant : composed_lts.invariant L inv.
Proof.
  apply invariant_ind_to_invariant'.
  apply step_inv.
Qed.

Definition inv' s :=
  forall pid,
    binds pid Run s.(L1State).(PidPos) ->
    exists s1 s2 q acts,
      composed_lts.internal_query L s1 pid q s2 /\
      composed_lts.valid_execution_fragment L s2 s acts /\
      gather_pid_events_B pid acts = [] /\
      composed_lts.reachable L s1
.

Lemma step_inv' : composed_lts.invariant_ind L (fun s => inv' s /\ composed_lts.reachable L s).
Proof.
  apply invariant_ind''_imply_invariant_ind_land.
  unfold invariant_ind''.
  intuition.
  apply reachable_is_invariant.
  unfold about. intuition.
  - inversion H; subst.
    unfold inv'. intros.
    inversion H0; subst.
    rewrite H4 in H2.
    inversion H2.
  - unfold inv' in *. intros.
    destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst. inversion H1; subst; simpl in *.
      --- inversion H3; subst.
        simpl in *.
        apply H in H2; auto.
        destruct H2 as [s1 [s2 [q [acts [Hiq [Hvalid Hgather]]]]]].
        exists s1, s2, q, acts.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
        eapply composed_lts.Step_Internal_L1; eauto.
        eapply composed_lts.Step_None; eauto.
        rewrite app_nil_r.
        reflexivity.
    -- inversion H1; subst; simpl in *.
      --- inversion H3; subst; simpl in *.
        apply H in H2; auto.
        destruct H2 as [s1 [s2 [q [acts [Hiq [Hvalid Hgather]]]]]].
        exists s1, s2, q, acts.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
        eapply composed_lts.Step_Internal_L1; eauto.
        eapply composed_lts.Step_None; eauto.
        rewrite app_nil_r.
        reflexivity.
  - unfold inv' in *. intros.
    destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst. inversion H1; subst; simpl in *.
      --- apply binds_in in H2.
        unfold "#" in Hnotin. intuition.
    -- inversion H1; subst; simpl in *.
      --- apply H in H2; auto.
        destruct H2 as [s1 [s2 [q [acts [Hiq [Hvalid Hgather]]]]]].
        exists s1, s2, q, acts.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
        eapply composed_lts.Step_Internal_L2; eauto.
        eapply composed_lts.Step_None; eauto.
        rewrite app_nil_r.
        reflexivity.
  - unfold inv' in *. intros.
    destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst. inversion H1; subst.
      simpl in *.
      apply binds_in in H2.
      unfold "#" in Hnotin.
      intuition.
    -- inversion H1; subst.
      simpl in *.
      apply H in H2; auto.
      destruct H2 as [s1 [s2 [q [acts [Hiq [Hvalid Hgather]]]]]].
      exists s1, s2, q, (acts ++ [(pid, composed_lts.event_invC act)]).
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
      eapply composed_lts.Step_Initial_Call; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      rewrite Heq.
      rewrite app_nil_r.
      assumption.
  - destruct act.
  - destruct act.
  - unfold inv' in *. intros.
    destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst. inversion H1; subst.
      simpl in *.
      apply H in H2.
      destruct H2 as [s1 [s2 [q [acts [Hiq [Hvalid Hgather]]]]]].
      exists s1, s2, q, (acts ++ [(pid, composed_lts.event_resC act)]).
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
      eapply composed_lts.Step_Final_Return; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist.
      simpl. rewrite Nat.eqb_refl.
      rewrite app_nil_r.
      assumption.
    -- inversion H1; subst.
      simpl in *.
      apply H in H2; auto.
      destruct H2 as [s1 [s2 [q [acts [Hiq [Hvalid Hgather]]]]]].
      exists s1, s2, q, (acts ++ [(pid, composed_lts.event_resC act)]).
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
      eapply composed_lts.Step_Final_Return; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      rewrite Heq.
      rewrite app_nil_r.
      assumption.
  - unfold inv' in *. intros.
    destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst.
      exists st, st', act, [].
      intuition.
      eapply composed_lts.Step_None; eauto.
    -- inversion H1; subst.
      simpl in *.
      inversion H4; subst.
      simpl in *.
      apply binds_push_neq_inv in H2; auto.
      apply H in H2; auto.
      destruct H2 as [s1 [s2 [q [acts [Hiq [Hvalid Hgather]]]]]].
      exists s1, s2, q, (acts ++ [(pid, composed_lts.event_invB act)]).
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
      eapply composed_lts.Step_Internal_Query; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      rewrite Heq.
      rewrite app_nil_r.
      assumption.
      apply Nat.eqb_neq; intuition.
  - unfold inv' in *. intros.
    destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst.
      inversion H1; subst.
      simpl in *.
      inversion H3; subst.
      simpl in *.
      assert (pid # (remove pos pid)).
      apply ok_remove_notin; auto.
      apply binds_in in H2.
      unfold "#" in H6.
      intuition.
    -- inversion H1; subst.
      simpl in *.
      inversion H3; subst.
      simpl in *.
      apply remove_preserves_binds_notin in H2; auto.
      apply H in H2; auto.
      destruct H2 as [s1 [s2 [q [acts [Hiq [Hvalid Hgather]]]]]].
      exists s1, s2, q, (acts ++ [(pid, composed_lts.event_resB act)]).
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
      eapply composed_lts.Step_Internal_Reply; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      rewrite Heq.
      rewrite app_nil_r.
      assumption.
      apply Nat.eqb_neq; intuition.
Qed.

Lemma step_invariant' : composed_lts.invariant L (fun s => inv' s /\ composed_lts.reachable L s).
Proof.
  apply invariant_ind_to_invariant'.
  apply step_inv'.
Qed.

End INV.
