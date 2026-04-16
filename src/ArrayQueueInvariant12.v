Require Import
  LibVar
  LibEnv
  List
  Arith
  Lia
  LibEnv
  VeriTactics
  LTS
  SyncLTS
  Tensor
  Compose
  Invariants
  KInduction
  Array
  Counter
  CounterProp
  ComposedLTS
  ArrayQueue
  ArrayQueueImpl
  ArrayQueueMapping
  ArrayQueueProp
  ArrayQueueImplProp
  Queue
  ArrayQueueInvariant
  ArrayQueueInvariant2
  ArrayQueueInvariantBefore
  ArrayQueueInvariantBefore2.
Import ListNotations.

Section test.

Variable L : nat.

Arguments get_pc {L}.
Arguments get_xp {L}.
Arguments get_ary {L}.
Arguments get_impl {L}.
Arguments get_rear {L}.
Arguments get_vec_rear {L}.

Lemma inv_rear_read_at_e2_e11_d14: forall k (s : composed_lts.state (composed_array_queue L)),
  reachable_len' (composed_array_queue L) s k ->
  (forall pid,
    binds pid CntRead (get_rear s).(Counter.requests) ->
      binds pid AEnq2 (get_pc s) \/
      binds pid AEnq11 (get_pc s) \/
      binds pid ADeq14 (get_pc s)).
Proof.
  induction k; intros.
  - unfold reachable_len' in H0.
    destruct H as [init [acts [Hnew Hvalid]]].
    inversion Hvalid; subst.
    inversion Hnew; subst.
    inversion H; subst.
    inversion H2; subst.
    inversion H5; subst.
    inversion H6; subst.
    inversion H9; subst.
    inversion H10; subst; simpl in *.
    unfold get_rear in *; simpl in *.
    rewrite H13 in H0.
    unfold new_counter in H0.
    simpl in H0.
    inversion H0.
  - apply reachable_len_reconstruct in H.
    destruct H as [st [acts [Hreach Hstep]]].
    inversion Hstep; subst; clear Hstep.
    -- inversion H3; subst; clear H3.
      destruct (eq_nat_dec pid pid0).
      --- subst.
        apply IHk with (pid:=pid0) in Hreach; auto.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *; intuition.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_rear in *; simpl in *; intuition.
        inversion H2; subst; simpl in *; auto.
        (* front_rear *)
        + inversion H3; subst; simpl in *.
          inversion H4; subst; simpl in *; auto.
          (* rear *)
          ++ inversion H5; subst; simpl in *.
            inversion H6; subst; simpl in *; auto.
            assert (Htmp : pid0 # (remove inv pid0)) by
            (apply ok_remove_notin; auto).
            apply binds_in in H0;
            unfold "#" in Htmp; intuition.
      --- 
        apply IHk with (pid:=pid) in Hreach; auto.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *; intuition.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_rear in *; simpl in *; intuition.
        inversion H2; subst; simpl in *; auto.
        inversion H3; subst; simpl in *; auto.
        inversion H4; subst; simpl in *; auto.
        inversion H5; subst; simpl in *; auto.
        inversion H6; subst; simpl in *; auto;
        unfold binds in H0;
        rewrite remove_neq_preserves_get in H0; auto.
    -- inversion H3; subst; clear H3.
      destruct (eq_nat_dec pid pid0).
      --- subst.
        apply IHk with (pid:=pid0) in Hreach; auto.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H2; subst; simpl in *;
        unfold binds in Hbinds0;
        destruct Hreach as [Hb|[Hb|Hb]];
        rewrite Hb in Hbinds0; discriminate.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_rear in *; simpl in *; auto.
      --- apply IHk with (pid:=pid) in Hreach; auto.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H2; subst; simpl in *;
        destruct Hreach as [Hb|[Hb|Hb]];
        eapply substitute_neq_preserves_binds in Hb; eauto.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_rear in *; simpl in *; auto.
    -- inversion H1.
    -- inversion H1.
    -- inversion H3; subst; clear H3.
      destruct (eq_nat_dec pid pid0).
      --- subst.
        apply IHk with (pid:=pid0) in Hreach; auto.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H2; subst; simpl in *;
        unfold "#" in Hnotin_pc;
        destruct Hreach as [Hb|[Hb|Hb]];
        apply binds_in in Hb; intuition.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_rear in *; simpl in *; auto.
      --- apply IHk with (pid:=pid) in Hreach; auto.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H2; subst; simpl in *;
        destruct Hreach as [Hb|[Hb|Hb]];
        eapply binds_push_neq in Hb; eauto;
        simpl in Hb; eauto.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_rear in *; simpl in *; auto.
    -- inversion H3; subst; clear H3.
      destruct (eq_nat_dec pid pid0).
      --- subst.
        apply IHk with (pid:=pid0) in Hreach; auto.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H2; subst; simpl in *;
        unfold binds in Hbinds0;
        destruct Hreach as [Hb|[Hb|Hb]];
        rewrite Hb in Hbinds0; discriminate.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_rear in *; simpl in *; auto.
      --- apply IHk with (pid:=pid) in Hreach; auto.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H2; subst; simpl in *;
        destruct Hreach as [Hb|[Hb|Hb]];
        eapply remove_neq_preserves_binds in Hb; eauto.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_rear in *; simpl in *; auto.
    -- inversion H3; subst; clear H3.
      destruct (eq_nat_dec pid pid0).
      --- subst.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H3; subst; simpl in *;
        pose proof Hbinds0 as HbindsTmp;
        eapply substitute_eq_binds_v' in Hbinds0; eauto;
        clear Hbinds0.
        all : try (apply IHk with (pid:=pid0) in Hreach; auto;
        unfold get_rear in *; simpl in *; auto;
        inversion H2; subst; simpl in *;
        inversion H4; subst; simpl in *; auto;
        inversion H6; subst; simpl in *; auto;
        inversion H5; subst; simpl in *; auto;
        unfold binds in HbindsTmp;
        destruct Hreach as [Hb|[Hb|Hb]];
        rewrite Hb in HbindsTmp; try discriminate).
        apply IHk with (pid:=pid0) in Hreach; auto;
        unfold get_rear in *; simpl in *; auto;
        inversion H2; subst; simpl in *;
        inversion H4; subst; simpl in *; auto;
        inversion H6; subst; simpl in *; auto;
        inversion H5; subst; simpl in *; auto;
        inversion H8; subst; simpl in *; auto;
        inversion H7; subst; simpl in *; auto;
        unfold binds in HbindsTmp.
        destruct Hreach as [Hb|[Hb|Hb]];
        rewrite Hb in HbindsTmp; try discriminate.
        apply binds_push_eq_inv in H0; discriminate.
      --- apply IHk with (pid:=pid) in Hreach; auto.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H3; subst; simpl in *;
        destruct Hreach as [Hb|[Hb|Hb]];
        eapply substitute_neq_preserves_binds in Hb; eauto.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_rear in *; simpl in *; auto.
        inversion H2; subst; simpl in *.
        inversion H4; subst; simpl in *; auto.
        inversion H5; subst; simpl in *;
        inversion H6; subst; simpl in *;
        inversion H7; subst; simpl in *;
        inversion H8; subst; simpl in *;
        try (apply binds_push_neq_inv in H0; auto); auto.
    -- inversion H3; subst; clear H3.
      destruct (eq_nat_dec pid pid0).
      --- subst.
        pose proof Hreach as HreachTmp.
        apply reachable_len_to_reachable in HreachTmp.
        apply IHk with (pid:=pid0) in Hreach; auto.
        inversion H1; subst; simpl in *.
        inversion H2; subst; simpl in *.
        unfold get_pc in *; simpl in *;
        inversion H3; subst; simpl in *;
        unfold binds in Hbinds0;
        destruct Hreach as [Hb|[Hb|Hb]];
        try (rewrite Hb in Hbinds0; discriminate).
        all : try (
            inversion H; subst; simpl in *;
            inversion H4; subst; simpl in *;
            inversion H6; subst; simpl in *;
            inversion H5; subst; simpl in *;
            inversion H8; subst; simpl in *;
            inversion H7; subst; simpl in *;
        apply compose_reachable_single_reachable in HreachTmp;
        apply tensor_reachable_single_reachable' in HreachTmp;
        apply tensor_reachable_single_reachable' in HreachTmp;
        simpl in HreachTmp;
        apply counter_exclusive_wf_invariant in HreachTmp;
        unfold counter_exclusive_wf in HreachTmp;
        simpl in HreachTmp;
        specialize (HreachTmp pid0);
        intuition;
        apply binds_in in H0;
        intuition;
        apply binds_in in Hbinds6;
        unfold "#" in H11; intuition).
        inversion H1; subst; simpl in *.
        inversion H2; subst; simpl in *.
        unfold get_rear in *; simpl in *; auto.
        inversion H; subst; simpl in *.
        inversion H4; subst; simpl in *; auto.
        inversion H5; subst; simpl in *; auto.
        inversion H6; subst; simpl in *; auto.
        inversion H7; subst; simpl in *; auto.
        inversion H8; subst; simpl in *; auto.
      --- apply IHk with (pid:=pid) in Hreach; auto.
        inversion H1; subst; simpl in *.
        inversion H2; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H3; subst; simpl in *;
        destruct Hreach as [Hb|[Hb|Hb]];
        eapply substitute_neq_preserves_binds in Hb; eauto.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_rear in *; simpl in *; auto.
        inversion H3; subst; simpl in *; auto.
        inversion H4; subst; simpl in *; auto.
        inversion H5; subst; simpl in *; auto.
        inversion H6; subst; simpl in *; auto.
        inversion H7; subst; simpl in *; auto.
      Unshelve. all : constructor.
Qed.

Lemma inv_rear_read_at_e2_e11_d14_invariant :
  composed_lts.invariant (composed_array_queue L)
  (fun s =>
  (forall pid,
    binds pid CntRead (get_rear s).(Counter.requests) ->
      binds pid AEnq2 (get_pc s) \/
      binds pid AEnq11 (get_pc s) \/
      binds pid ADeq14 (get_pc s))
  ).
Proof.
  apply reachable_len'_to_invariant.
  intros.
  eapply inv_rear_read_at_e2_e11_d14; eauto.
Qed.

Definition after_d15 v :=
  v = ADeq26 \/
  v = ADeq27 \/
  v = ADeq28.

Lemma after_d15_Deq26:
  after_d15 (ADeq26).
Proof.
  intros.
  unfold after_d15.
  intuition.
Qed.

Lemma after_d15_Deq27:
  after_d15 (ADeq27).
Proof.
  intros.
  unfold after_d15.
  intuition.
Qed.

Lemma after_d15_Deq28:
  after_d15 (ADeq28).
Proof.
  intros.
  unfold after_d15.
  intuition.
Qed.

Ltac solve_after_d15 :=
  try apply after_d15_Deq26;
  try apply after_d15_Deq27;
  try apply after_d15_Deq28.

Lemma inv_front_d27_before: forall k (s : composed_lts.state (composed_array_queue L)),
  reachable_len' (composed_array_queue L) s k ->
  (forall pid v (Hv : after_d15 v),
    binds pid v (get_pc s) ->
    exists s1 s2 it acts,
      composed_lts.valid_execution_fragment (composed_array_queue L) s2 s acts /\
      composed_lts.step_L2 (composed_array_queue L) s1 pid it s2 /\
      binds pid ADeq26 (get_pc s2) /\
      (get_impl s2).(front) pid = (get_impl s).(front) pid /\
      composed_lts.reachable (composed_array_queue L) s1
      ).
Proof.
  induction k; intros.
  - unfold reachable_len' in H0.
    destruct H as [init [acts [Hnew Hvalid]]].
    inversion Hvalid; subst.
    inversion Hnew; subst.
    inversion H1; subst.
    inversion H2; subst.
    unfold get_pc in *; simpl in *.
    rewrite H5 in H0.
    unfold new_array_queue in H0.
    simpl in H0.
    inversion H0.
  - apply reachable_len_reconstruct in H.
    destruct H as [st [acts [Hreach Hstep]]].
    inversion Hstep; subst; clear Hstep.
    -- inversion H3; subst; clear H3.
      apply IHk with (pid:=pid) (v:=v) in Hreach; auto.
      inversion H1; subst; simpl in *.
      inversion H; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      destruct Hreach as [s1 [s2 [it [acts [Hvalid [Hstep Hb]]]]]].
      exists s1, s2, it, acts. intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=[]).
      eauto.
      eapply composed_lts.Step_Internal_L1; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite app_nil_r; auto.
      inversion H1; subst; simpl in *.
      inversion H; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      inversion H2; subst; simpl in *; auto.
    -- inversion H3; subst; clear H3.
      destruct (eq_nat_dec pid pid0).
      --- subst.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        unfold binds in H0.
        inversion H2; subst; simpl in *.
        all : pose proof Hbinds0 as HbindsTmp;
        eapply substitute_eq_binds_v' in Hbinds0;
        rewrite Hbinds0 in H0; auto;
        inversion H0; subst;
        unfold after_d15 in Hv;
        intuition; try discriminate.
        eexists.
        eexists.
        eexists.
        exists []. intuition.
        eapply composed_lts.Step_None; eauto.
        eauto.
        simpl.
        eapply substitute_eq_binds_v'; eauto.
        unfold get_impl; simpl. auto.
        eapply reachable_len_to_reachable; eauto.
        eapply IHk with (pid:=pid0) in Hreach;
        simpl; eauto; solve_after_d15.
        destruct Hreach as [s1 [s2 [it [acts [Hvalid [Hstep [Hb Heq]]]]]]].
        exists s1, s2, it, acts.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a':=[]).
        eauto.
        eapply composed_lts.Step_Internal_L2; eauto.
        eapply composed_lts.Step_None; eauto.
        rewrite app_nil_r; auto.
      --- eapply IHk with (pid:=pid) in Hreach; eauto.
        destruct Hreach as [s1 [s2 [it [acts [Hvalid [Hstep [Hb [Heq Hreach]]]]]]]].
        exists s1, s2, it, acts.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a':=[]).
        eauto.
        eapply composed_lts.Step_Internal_L2; eauto.
        eapply composed_lts.Step_None; eauto.
        rewrite app_nil_r; auto.

        inversion H1; subst; simpl in *.
        unfold get_impl in *; simpl in *.
        inversion H; subst; simpl in *.
        inversion H2; subst; simpl in *; auto.
        apply Nat.eqb_neq in n; rewrite n; auto.
        inversion H1; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H; subst; simpl in *.
        inversion H2; subst; simpl in *;
        apply substitute_neq_preserves_binds' in H0; auto.
    -- inversion H1.
    -- inversion H1.
    -- inversion H3; subst; simpl in *; clear H3.
      destruct (eq_nat_dec pid pid0).
      --- subst.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H2; subst; simpl in *;
        apply binds_push_eq_inv in H0; auto;
        subst;
        unfold after_d15 in Hv; intuition; discriminate.
      --- eapply IHk with (pid:=pid) in Hreach; eauto.
        destruct Hreach as [s1 [s2 [it [acts [Hvalid [Hstep [Hb Hreach]]]]]]].
        exists s1, s2, it.
        eexists.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a:=acts).
        eauto.
        eapply composed_lts.Step_Initial_Call; eauto.
        eapply composed_lts.Step_None; eauto.
        eauto.

        inversion H1; subst; simpl in *.
        unfold get_impl in *; simpl in *.
        inversion H3; subst; simpl in *.
        inversion H4; subst; simpl in *; auto.
        inversion H1; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H; subst; simpl in *.
        inversion H2; subst; simpl in *;
        apply binds_push_neq_inv in H0; auto.
    -- inversion H3; subst; simpl in *; clear H3.
      destruct (eq_nat_dec pid pid0).
      --- subst.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H2; subst; simpl in *;
        assert (Htmp : pid0 # (remove pc pid0)) by
        (apply ok_remove_notin; auto);
        unfold "#" in Htmp;
        apply binds_in in H0;
        intuition.
      --- eapply IHk with (pid:=pid) in Hreach; eauto.
        destruct Hreach as [s1 [s2 [it [acts [Hvalid [Hstep [Hb Hreach]]]]]]].
        exists s1, s2, it.
        eexists.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a:=acts).
        eauto.
        eapply composed_lts.Step_Final_Return; eauto.
        eapply composed_lts.Step_None; eauto.
        eauto.

        inversion H1; subst; simpl in *.
        unfold get_impl in *; simpl in *.
        inversion H3; subst; simpl in *.
        inversion H4; subst; simpl in *; auto.

        inversion H1; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H; subst; simpl in *.
        inversion H2; subst; simpl in *;
        apply remove_preserves_binds_notin in H0; auto.
    -- inversion H3; subst; simpl in *; clear H3.
      destruct (eq_nat_dec pid pid0).
      --- subst.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        unfold binds in H0.
        inversion H3; subst; simpl in *;
        pose proof Hbinds0 as HbindsTmp;
        eapply substitute_eq_binds_v' in Hbinds0;
        rewrite Hbinds0 in H0;
        inversion H0; subst;
        unfold after_d15 in Hv; intuition; try discriminate.
        eapply IHk in Hreach; simpl; eauto; solve_after_d15.
        destruct Hreach as [s1 [s2 [it [acts [Hvalid [Hstep [Hb Heq]]]]]]].
        exists s1, s2, it.
        eexists.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a:=acts).
        eauto.
        eapply composed_lts.Step_Internal_Query; eauto.
        eapply composed_lts.Step_None; eauto.
        eauto.
      --- eapply IHk with (pid:=pid) in Hreach; eauto.
        destruct Hreach as [s1 [s2 [it [acts [Hvalid [Hstep [Hb [Heq Hreach]]]]]]]].
        exists s1, s2, it.
        eexists.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a:=acts).
        eauto.
        eapply composed_lts.Step_Internal_Query; eauto.
        eapply composed_lts.Step_None; eauto.
        eauto.

        inversion H1; subst; simpl in *.
        unfold get_impl in *; simpl in *.
        inversion H; subst; simpl in *.
        inversion H3; subst; simpl in *; auto.

        inversion H1; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H; subst; simpl in *.
        inversion H3; subst; simpl in *;
        apply substitute_neq_preserves_binds' in H0; auto.
    -- inversion H3; subst; simpl in *; clear H3.
      destruct (eq_nat_dec pid pid0).
      --- subst.
        inversion H1; subst; simpl in *.
        inversion H2; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        unfold binds in H0.
        inversion H3; subst; simpl in *;
        eapply substitute_eq_binds_v' in Hbinds0;
        rewrite Hbinds0 in H0;
        inversion H0; subst;
        unfold after_d15 in Hv; intuition; discriminate.
      --- eapply IHk with (pid:=pid) in Hreach; eauto.
        destruct Hreach as [s1 [s2 [it [acts [Hvalid [Hstep [Hb [Heq Hreach]]]]]]]].
        exists s1, s2, it.
        eexists.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a:=acts).
        eauto.
        eapply composed_lts.Step_Internal_Reply; eauto.
        eapply composed_lts.Step_None; eauto.
        eauto.

        inversion H1; subst; simpl in *.
        unfold get_impl in *; simpl in *.
        inversion H2; subst; simpl in *.
        inversion H3; subst; simpl in *; auto.

        inversion H1; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H2; subst; simpl in *.
        inversion H3; subst; simpl in *;
        apply substitute_neq_preserves_binds' in H0; auto.
Qed.

Lemma inv_front_d27_before_invariant: 
  composed_lts.invariant (composed_array_queue L)
  (fun (s : composed_lts.state (composed_array_queue L)) =>
  forall pid v (Hv : after_d15 v),
    binds pid v (get_pc s) ->
    exists s1 s2 it acts,
      composed_lts.valid_execution_fragment (composed_array_queue L) s2 s acts /\
      composed_lts.step_L2 (composed_array_queue L) s1 pid it s2 /\
      binds pid ADeq26 (get_pc s2) /\
      (get_impl s2).(front) pid = (get_impl s).(front) pid /\
      composed_lts.reachable (composed_array_queue L) s1
      ).
Proof.
  apply reachable_len'_to_invariant.
  intros.
  eapply inv_front_d27_before; eauto.
Qed.

Lemma inv_front_d14_ret_reply: forall k (s : composed_lts.state (composed_array_queue L)),
  reachable_len' (composed_array_queue L) s k ->
  (forall pid ret (Hb :
    binds pid (CntReadOk ret) (get_rear s).(Counter.responses)
    ),
    binds pid (ADeq14) (get_pc s) ->
    exists s1 s2 acts,
      composed_lts.valid_execution_fragment (composed_array_queue L) s2 s acts /\
      composed_lts.step_L1
        (composed_array_queue L)
        s1 pid
          (@Tensor.intL2 li_array li_cnt_cnt (array L) ArrayQueue.front_rear
            (@Tensor.intL2 li_counter li_counter counter counter (int_cnt_read)))
        s2 /\
        ret = (get_rear s2).(Counter.value)
      ).
Proof.
  induction k; intros.
  - unfold reachable_len' in H0.
    destruct H as [init [acts [Hnew Hvalid]]].
    inversion Hvalid; subst.
    inversion Hnew; subst.
    inversion H1; subst.
    inversion H2; subst.
    unfold get_pc in *; simpl in *.
    rewrite H5 in H0.
    unfold new_array_queue in H0.
    simpl in H0.
    inversion H0.
  - apply reachable_len_reconstruct in H.
    destruct H as [st [acts [Hreach Hstep]]].
    inversion Hstep; subst; clear Hstep.
    -- inversion H3; subst; clear H3.
      destruct (eq_nat_dec pid pid0).
      --- subst.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_rear in *; simpl in *.
        inversion H2; subst; simpl in *.
        (* front_rear *)
        + inversion H3; subst; simpl in *.
          inversion H4; subst; simpl in *.
          (* rear *)
          ++ inversion H5; subst; simpl in *.
            inversion H6; subst; simpl in *.
            (* INC *)
            +++ apply binds_push_eq_inv in Hb; discriminate.
            (* READ *)
            +++ eexists.
              eexists.
              exists []. intuition.
              eapply composed_lts.Step_None; eauto.
              eauto. simpl.
              apply binds_push_eq_inv in Hb.
              inversion Hb; subst. auto.
          ++ apply IHk with (pid:=pid0) (ret:=ret) in Hreach; auto.
            destruct Hreach as [s1 [s2 [acts [Hvalid Hstep]]]].
            exists s1, s2, acts. intuition.
            eapply composed_lts.valid_execution_fragment_join' with (a':=[]).
            eauto.
            eapply composed_lts.Step_Internal_L1; eauto.
            eapply composed_lts.Step_None; eauto.
            rewrite app_nil_r; auto.
        + apply IHk with (pid:=pid0) (ret:=ret) in Hreach; auto.
          destruct Hreach as [s1 [s2 [acts [Hvalid Hstep]]]].
          exists s1, s2, acts. intuition.
          eapply composed_lts.valid_execution_fragment_join' with (a':=[]).
          eauto.
          eapply composed_lts.Step_Internal_L1; eauto.
          eapply composed_lts.Step_None; eauto.
          rewrite app_nil_r; auto.
      --- apply IHk with (pid:=pid) (ret:=ret) in Hreach; auto.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        destruct Hreach as [s1 [s2 [acts [Hvalid Hstep]]]].
        exists s1, s2, acts. intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a':=[]).
        eauto.
        eapply composed_lts.Step_Internal_L1; eauto.
        eapply composed_lts.Step_None; eauto.
        rewrite app_nil_r; auto.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_rear in *; simpl in *.
        inversion H2; subst; simpl in *; auto.
        inversion H3; subst; simpl in *; auto.
        inversion H4; subst; simpl in *; auto.
        inversion H5; subst; simpl in *; auto.
        inversion H6; subst; simpl in *; auto;
        apply binds_push_neq_inv in Hb; auto.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H2; subst; simpl in *; auto.
    -- inversion H3; subst; clear H3.
      destruct (eq_nat_dec pid pid0).
      --- subst.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        unfold binds in H0.
        inversion H2; subst; simpl in *.
        all : pose proof Hbinds0 as HbindsTmp;
        eapply substitute_eq_binds_v' in Hbinds0;
        rewrite Hbinds0 in H0; auto;
        inversion H0; subst;
        unfold after_d15 in Hv;
        intuition; try discriminate.
      --- eapply IHk with (pid:=pid) in Hreach; eauto.
        destruct Hreach as [s1 [s2 [acts [Hvalid [Hstep Heq]]]]].
        exists s1, s2, acts.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a':=[]).
        eauto.
        eapply composed_lts.Step_Internal_L2; eauto.
        eapply composed_lts.Step_None; eauto.
        rewrite app_nil_r; auto.
        eauto.

        inversion H1; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H; subst; simpl in *.
        inversion H2; subst; simpl in *;
        apply substitute_neq_preserves_binds' in H0; auto.

        inversion H1; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H; subst; simpl in *.
        inversion H2; subst; simpl in *;
        apply substitute_neq_preserves_binds' in H0; auto.
    -- inversion H1.
    -- inversion H1.
    -- inversion H3; subst; simpl in *; clear H3.
      destruct (eq_nat_dec pid pid0).
      --- subst.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H2; subst; simpl in *;
        apply binds_push_eq_inv in H0; auto;
        subst;
        discriminate.
      --- eapply IHk with (pid:=pid) in Hreach; eauto.
        destruct Hreach as [s1 [s2 [acts [Hvalid Hstep]]]].
        exists s1, s2.
        eexists.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a:=acts).
        eauto.
        eapply composed_lts.Step_Initial_Call; eauto.
        eapply composed_lts.Step_None; eauto.
        eauto.
        eauto.

        inversion H1; subst; simpl in *.
        unfold get_rear in *; simpl in *.
        inversion H; subst; simpl in *.
        inversion H2; subst; simpl in *;
        apply binds_push_neq_inv in H0; auto.

        inversion H1; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H; subst; simpl in *.
        inversion H2; subst; simpl in *;
        apply binds_push_neq_inv in H0; auto.

    -- inversion H3; subst; simpl in *; clear H3.
      destruct (eq_nat_dec pid pid0).
      --- subst.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H2; subst; simpl in *;
        assert (Htmp : pid0 # (remove pc pid0)) by
        (apply ok_remove_notin; auto);
        unfold "#" in Htmp;
        apply binds_in in H0;
        intuition.
      --- eapply IHk with (pid:=pid) in Hreach; eauto.
        destruct Hreach as [s1 [s2 [acts [Hvalid Heq]]]].
        exists s1, s2.
        eexists.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a:=acts).
        eauto.
        eapply composed_lts.Step_Final_Return; eauto.
        eapply composed_lts.Step_None; eauto.
        eauto.
        eauto.

        inversion H1; subst; simpl in *.
        unfold get_rear in *; simpl in *.
        inversion H; subst; simpl in *.
        inversion H2; subst; simpl in *;
        apply remove_preserves_binds_notin in H0; auto.

        inversion H1; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H; subst; simpl in *.
        inversion H2; subst; simpl in *;
        apply remove_preserves_binds_notin in H0; auto.

    -- inversion H3; subst; simpl in *; clear H3.
      destruct (eq_nat_dec pid pid0).
      --- subst.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        unfold binds in H0.
        inversion H3; subst; simpl in *;
        pose proof Hbinds0 as HbindsTmp;
        eapply substitute_eq_binds_v' in Hbinds0;
        rewrite Hbinds0 in H0;
        inversion H0; subst;
        try discriminate.
        inversion H2; subst; simpl in *.
        inversion H4; subst; simpl in *.
        inversion H6; subst; simpl in *.
        inversion H5; subst; simpl in *.
        inversion H8; subst; simpl in *.
        exfalso.
        inversion H7; subst; simpl in *.
        unfold "#" in Hnotin_res.
        apply binds_in in Hb; intuition.
      --- eapply IHk with (pid:=pid) in Hreach; eauto.
        destruct Hreach as [s1 [s2 [acts [Hvalid Heq]]]].
        exists s1, s2.
        eexists.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a:=acts).
        eauto.
        eapply composed_lts.Step_Internal_Query; eauto.
        eapply composed_lts.Step_None; eauto.
        eauto.
        eauto.

        inversion H1; subst; simpl in *.
        unfold get_rear in *; simpl in *.
        inversion H2; subst; simpl in *.
        inversion H3; subst; simpl in *; auto.
        inversion H4; subst; simpl in *.
        inversion H5; subst; simpl in *; auto.
        inversion H6; subst; simpl in *.
        inversion H7; subst; simpl in *; auto.

        inversion H1; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H; subst; simpl in *.
        inversion H3; subst; simpl in *;
        apply substitute_neq_preserves_binds' in H0; auto.
    -- inversion H3; subst; simpl in *; clear H3.
      destruct (eq_nat_dec pid pid0).
      --- subst.
        inversion H1; subst; simpl in *.
        inversion H2; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        unfold binds in H0.
        inversion H3; subst; simpl in *;
        pose proof Hbinds0 as HbindsTmp;
        eapply substitute_eq_binds_v' in Hbinds0;
        rewrite Hbinds0 in H0;
        inversion H0; subst;
        try discriminate.
      --- eapply IHk with (pid:=pid) in Hreach; eauto.
        destruct Hreach as [s1 [s2 [acts [Hvalid Hstep]]]].
        exists s1, s2.
        eexists.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a:=acts).
        eauto.
        eapply composed_lts.Step_Internal_Reply; eauto.
        eapply composed_lts.Step_None; eauto.
        eauto.
        eauto.

        inversion H1; subst; simpl in *.
        unfold get_rear in *; simpl in *.
        inversion H; subst; simpl in *.
        inversion H3; subst; simpl in *; auto.
        inversion H4; subst; simpl in *; auto.
        inversion H5; subst; simpl in *; auto.
        inversion H6; subst; simpl in *; auto.
        inversion H7; subst; simpl in *; auto;
        apply remove_preserves_binds_notin in Hb; auto.
        inversion H1; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H2; subst; simpl in *.
        inversion H3; subst; simpl in *;
        apply substitute_neq_preserves_binds' in H0; auto.
Qed.

Lemma inv_front_d15_ret: forall k (s : composed_lts.state (composed_array_queue L)),
  reachable_len' (composed_array_queue L) s k ->
  (forall pid ret,
    binds pid (ADeq15 ret) (get_pc s) ->
    exists s1 s2 acts,
      composed_lts.valid_execution_fragment (composed_array_queue L) s2 s acts /\
      composed_lts.step_L1
        (composed_array_queue L)
        s1 pid
        (@Tensor.intL2 li_array li_cnt_cnt (array L) ArrayQueue.front_rear
          (@Tensor.intL2 li_counter li_counter counter counter (int_cnt_read)))
        s2 /\
      ret = (get_rear s2).(Counter.value)
      ).
Proof.
  induction k; intros.
  - unfold reachable_len' in H0.
    destruct H as [init [acts [Hnew Hvalid]]].
    inversion Hvalid; subst.
    inversion Hnew; subst.
    inversion H1; subst.
    inversion H2; subst.
    unfold get_pc in *; simpl in *.
    rewrite H5 in H0.
    unfold new_array_queue in H0.
    simpl in H0.
    inversion H0.
  - apply reachable_len_reconstruct in H.
    destruct H as [st [acts [Hreach Hstep]]].
    inversion Hstep; subst; clear Hstep.
    -- inversion H3; subst; clear H3.
      apply IHk with (pid:=pid) (ret:=ret) in Hreach; auto.
      inversion H1; subst; simpl in *.
      inversion H; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      destruct Hreach as [s1 [s2 [acts [Hvalid [Hstep Heq]]]]].
      exists s1, s2, acts. intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=[]).
      eauto.
      eapply composed_lts.Step_Internal_L1; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite app_nil_r; auto.
      inversion H1; subst; simpl in *.
      inversion H; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      inversion H2; subst; simpl in *; auto.
    -- inversion H3; subst; clear H3.
      destruct (eq_nat_dec pid pid0).
      --- subst.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        unfold binds in H0.
        inversion H2; subst; simpl in *.
        all : pose proof Hbinds0 as HbindsTmp;
        eapply substitute_eq_binds_v' in Hbinds0;
        rewrite Hbinds0 in H0; auto;
        inversion H0; subst;
        unfold after_d15 in Hv;
        intuition; try discriminate.
      --- eapply IHk with (pid:=pid) in Hreach; eauto.
        destruct Hreach as [s1 [s2 [acts [Hvalid [Hstep Heq]]]]].
        exists s1, s2, acts.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a':=[]).
        eauto.
        eapply composed_lts.Step_Internal_L2; eauto.
        eapply composed_lts.Step_None; eauto.
        rewrite app_nil_r; auto.
        eauto.

        inversion H1; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H; subst; simpl in *.
        inversion H2; subst; simpl in *;
        apply substitute_neq_preserves_binds' in H0; auto.
    -- inversion H1.
    -- inversion H1.
    -- inversion H3; subst; simpl in *; clear H3.
      destruct (eq_nat_dec pid pid0).
      --- subst.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H2; subst; simpl in *;
        apply binds_push_eq_inv in H0; auto;
        subst;
        discriminate.
      --- eapply IHk with (pid:=pid) in Hreach; eauto.
        destruct Hreach as [s1 [s2 [acts [Hvalid [Hstep Heq]]]]].
        exists s1, s2.
        eexists.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a:=acts).
        eauto.
        eapply composed_lts.Step_Initial_Call; eauto.
        eapply composed_lts.Step_None; eauto.
        eauto.
        eauto.

        inversion H1; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H; subst; simpl in *.
        inversion H2; subst; simpl in *;
        apply binds_push_neq_inv in H0; auto.

    -- inversion H3; subst; simpl in *; clear H3.
      destruct (eq_nat_dec pid pid0).
      --- subst.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H2; subst; simpl in *;
        assert (Htmp : pid0 # (remove pc pid0)) by
        (apply ok_remove_notin; auto);
        unfold "#" in Htmp;
        apply binds_in in H0;
        intuition.
      --- eapply IHk with (pid:=pid) in Hreach; eauto.
        destruct Hreach as [s1 [s2 [acts [Hvalid [Hstep Heq]]]]].
        exists s1, s2.
        eexists.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a:=acts).
        eauto.
        eapply composed_lts.Step_Final_Return; eauto.
        eapply composed_lts.Step_None; eauto.
        eauto.
        eauto.

        inversion H1; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H; subst; simpl in *.
        inversion H2; subst; simpl in *;
        apply remove_preserves_binds_notin in H0; auto.

    -- inversion H3; subst; simpl in *; clear H3.
      destruct (eq_nat_dec pid pid0).
      --- subst.
        inversion H1; subst; simpl in *.
        inversion H; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        unfold binds in H0.
        inversion H3; subst; simpl in *;
        pose proof Hbinds0 as HbindsTmp;
        eapply substitute_eq_binds_v' in Hbinds0;
        rewrite Hbinds0 in H0;
        inversion H0; subst;
        unfold after_d15 in Hv; intuition; try discriminate.
      --- eapply IHk with (pid:=pid) in Hreach; eauto.
        destruct Hreach as [s1 [s2 [acts [Hvalid [Hstep Heq]]]]].
        exists s1, s2.
        eexists.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a:=acts).
        eauto.
        eapply composed_lts.Step_Internal_Query; eauto.
        eapply composed_lts.Step_None; eauto.
        eauto.
        eauto.

        inversion H1; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H; subst; simpl in *.
        inversion H3; subst; simpl in *;
        apply substitute_neq_preserves_binds' in H0; auto.
    -- inversion H3; subst; simpl in *; clear H3.
      destruct (eq_nat_dec pid pid0).
      --- subst.
        inversion H1; subst; simpl in *.
        inversion H2; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        unfold binds in H0.
        inversion H3; subst; simpl in *;
        pose proof Hbinds0 as HbindsTmp;
        eapply substitute_eq_binds_v' in Hbinds0;
        rewrite Hbinds0 in H0;
        inversion H0; subst;
        try discriminate.
        apply inv_front_d14_ret_reply with (pid:=pid0) (ret:=ret) in Hreach.
        destruct Hreach as [s1 [s2 [acts [Hvalid [Hstep Heq]]]]].
        exists s1, s2.
        eexists. intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a:=acts).
        eauto.
        eapply composed_lts.Step_Internal_Reply; eauto.
        eapply composed_lts.Step_None; eauto.
        eauto.
        unfold get_rear; simpl; auto.
        inversion H; subst; simpl in *.
        inversion H4; subst; simpl in *.
        inversion H6; subst; simpl in *.
        inversion H5; subst; simpl in *.
        inversion H8; subst; simpl in *.
        inversion H7; subst; simpl in *; auto.
        unfold get_pc; simpl; auto.
      --- eapply IHk with (pid:=pid) in Hreach; eauto.
        destruct Hreach as [s1 [s2 [acts [Hvalid [Hstep Heq]]]]].
        exists s1, s2.
        eexists.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a:=acts).
        eauto.
        eapply composed_lts.Step_Internal_Reply; eauto.
        eapply composed_lts.Step_None; eauto.
        eauto.
        eauto.

        inversion H1; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H2; subst; simpl in *.
        inversion H3; subst; simpl in *;
        apply substitute_neq_preserves_binds' in H0; auto.
Qed.

Lemma inv_front_d15_ret_invariant: 
  composed_lts.invariant (composed_array_queue L)
  (fun (s : composed_lts.state (composed_array_queue L)) =>
  (forall pid ret,
    binds pid (ADeq15 ret) (get_pc s) ->
    exists s1 s2 acts,
      composed_lts.valid_execution_fragment (composed_array_queue L) s2 s acts /\
      composed_lts.step_L1
        (composed_array_queue L)
        s1 pid
        (@Tensor.intL2 li_array li_cnt_cnt (array L) ArrayQueue.front_rear
          (@Tensor.intL2 li_counter li_counter counter counter (int_cnt_read)))
        s2 /\
      ret = (get_rear s2).(Counter.value)
      )).
Proof.
  apply reachable_len'_to_invariant; auto.
  intros.
  eapply inv_front_d15_ret; eauto.
Qed.

End test.