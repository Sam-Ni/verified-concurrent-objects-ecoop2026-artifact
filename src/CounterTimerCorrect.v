Require Import
  List
  Arith
  LibEnv
  LTS
  SyncLTS
  Compose
  ComposedLTS
  Refinement
  ComposedRefinement
  Counter
  CounterProp
  CounterTimerImpl
  CounterTimerImplProp
  Timer
  CounterTimer
  CounterTimerProp
  CounterTimerMapping
  TickNat
.
Import ListNotations.

Section Correctness.

Definition f (s1 : counter_timer.(state)) (s2 : timer.(state)) :=
  (gather_requests s1.(L2State).(LState).(CounterTimerImpl.pc) s1.(L1State).(LState).(Counter.responses)) = s2.(requests) /\
  sameset (gather_responses s1.(L2State).(LState).(CounterTimerImpl.pc) s1.(L1State).(LState).(Counter.responses)) s2.(responses) /\
  (nat_to_time s1.(L1State).(LState).(Counter.value)) = s2.(t).

Theorem counter_timer_correct: refines counter_timer timer.
Proof.
  eapply composed_forward_simulation_inv_ind' with
    (f:=f) (inv:=composed_counter_timer_wf).
  unfold composed_fsim_properties_inv_ind. intuition.
  - apply composed_counter_timer_wf_inv.
  - exists (mkTmState [] [] (O,O)).
    simpl. unfold counter_new_state.
    intuition.
    unfold timer_new_state.
    unfold new_timer. reflexivity.
    unfold f.
    simpl.
    inversion H; subst.
    inversion H0; subst.
    inversion H2; subst.
    rewrite H5. unfold new_counter.
    simpl.
    inversion H1; subst.
    inversion H4; subst.
    rewrite H8.
    unfold new_counter_timer.
    simpl.
    intuition.
    eapply sameset_refl.
    econstructor.
  - unfold f in H0.
    intuition.
    inversion H1; subst.
    simpl in *. clear H1.
    inversion H3; subst.
    simpl in *. clear H3.
    inversion H1; subst; simpl in *.
    -- destruct s2. simpl in *.
      exists (
        mkTmState
          ((pid, TmTick) :: requests)
          responses
          t
      ).
      simpl. intuition.
      ---
        rewrite <-H2.
        eapply timer_initial_state_tick; eauto.
        apply gather_requests_preserves_pid_notin; auto.
        eapply notin_sameset; eauto.
        apply gather_responses_preserves_pid_notin; auto.
        apply gather_requests_preserves_ok; auto.
        eapply sameset_ok; eauto.
        apply gather_responses_preserves_ok; auto.
      --- unfold f. simpl.
        intuition.
        f_equal; assumption.
    -- destruct s2. simpl in *.
      exists (
        mkTmState
          ((pid, TmRead) :: requests)
          responses
          t
      ).
      simpl. intuition.
      ---
        rewrite <-H2.
        eapply timer_initial_state_read; eauto.
        apply gather_requests_preserves_pid_notin; auto.
        eapply notin_sameset; eauto.
        apply gather_responses_preserves_pid_notin; auto.
        apply gather_requests_preserves_ok; auto.
        eapply sameset_ok; eauto;
        apply gather_responses_preserves_ok; auto.
      --- unfold f. simpl.
        intuition.
        f_equal; assumption.
  - unfold f in H0.
    intuition.
    inversion H1; subst.
    simpl in *. clear H1.
    inversion H3; subst.
    simpl in *. clear H3.
    inversion H1; subst; simpl in *.
    -- destruct s2. simpl in *.
      exists (
        mkTmState
          requests
          (remove responses pid)
          t
      ).
      simpl. intuition.
      ---
        rewrite <-H2.
        eapply timer_final_state_tick; eauto.
        apply gather_requests_preserves_ok; auto.
        eapply sameset_ok; eauto.
        apply gather_responses_preserves_ok; auto.
        eapply sameset_binds; eauto.
        apply gather_responses_binds_CTick3; auto.
      --- unfold f. simpl.
        intuition.
        rewrite gather_requests_binds_CTick3_remove; auto.
        rewrite gather_responses_remove_comm; auto.
        apply sameset_remove; auto.
    -- destruct s2. simpl in *.
      exists (
        mkTmState
          requests
          (remove responses pid)
          t
      ).
      simpl. intuition.
      ---
        rewrite <-H2.
        eapply timer_final_state_read; eauto.
        apply gather_requests_preserves_ok; auto.
        eapply sameset_ok; eauto.
        apply gather_responses_preserves_ok; auto.
        eapply sameset_binds; eauto.
        apply gather_responses_binds_CRead3; auto.
      --- unfold f. simpl.
        intuition.
        erewrite gather_requests_binds_CRead3_remove; eauto.
        rewrite gather_responses_remove_comm; auto.
        apply sameset_remove; auto.
  - unfold f in H0.
    intuition.
    inversion H1; subst;
    simpl in *.
    -- inversion H3; subst.
      clear H3.
      inversion H5; subst; simpl in *.
      --- clear H1. subst.
        unfold composed_counter_timer_wf in H.
        simpl in H.
        destruct H as [Himpl Hbefore].
        unfold ComposedLTS.inv in Hbefore.
        simpl in Hbefore.
        apply Hbefore in Hbinds0; auto.
        clear Hbefore.
        destruct Hbinds0 as
          [s'' [s' [q [acts [Hiq [Hvalid Hgather]]]]]].
        inversion Hiq; subst.
        clear Hiq.
        inversion H; subst.
        clear H.
        inversion H3; subst.
        2 : {
        inversion H1; subst.
        inversion H; subst.
        simpl in *. clear H.
        apply valid_execution_fragment_com in Hvalid.
        simpl in Hvalid.
        eapply valid_execution_fragment_sync in Hvalid; eauto.
        eapply internal_preserves_request with (pid:=pid) (qb:=CntRead) (qb':=CntInc) in Hvalid.
        discriminate.
        eapply gather_pid_events_B_gather_pid_external_events.
        eassumption. simpl.
        apply binds_push_eq; auto.
        simpl. assumption.
        }
        inversion H1; subst.
        inversion H; subst.
        simpl in *. clear H.
        generalize (@valid_execution_fragment_com' li_counter li_timer); intro.
        specialize (H _ _ _ _ _ Hvalid).
        simpl in H.
        destruct st2. simpl in *.
        eapply valid_execution_fragment_sync in H; eauto.
        apply valid_execution_fragment_com in Hvalid.
        simpl in Hvalid.
        eapply valid_execution_fragment_sync in Hvalid; eauto.
        eapply internal_preserves_request with (pid:=pid) (qb:=CntInc) (qb':=CntInc) in Hvalid.
        inversion Hvalid; subst.
        clear Hvalid.
        + subst. 
          simpl in *. subst.
          exists (
            mkTmState
              (remove s2.(requests) pid)
              ((pid, TmTickOk) :: s2.(responses))
              (tick (t s2))
          ).
          simpl.
          destruct s2.
          simpl in *.
          unfold CntTmImplStateWF in Himpl.
          assert (Hok_sub : ok (substitute pc pid CTick2)).
          apply substitute_preserves_ok; auto.
          generalize cnttmimpl_valid_execution_preserves_ok; intro Hwf.
          specialize (Hwf _ _ _ H Hok_sub).
          eapply noB_preserves_CTick2 with (pid:=pid) in H; eauto.
          2 : {
            eapply substitute_eq_binds_v'; eauto.
          }
          2 : {
            rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
            rewrite Hgather. simpl. reflexivity.
          }
          unfold f in *.
          simpl in *. subst. intuition.
          eapply Step_Internal; eauto.
          eapply timer_step_tick with (pid:=pid); eauto.
          apply gather_requests_preserves_ok; auto.
          eapply sameset_ok; eauto.
          apply gather_responses_preserves_ok; auto.
          apply gather_requests_binds_CTick2_binds_TmTick; auto.
          eapply notin_sameset; eauto.
          apply gather_responses_binds_CTick2_notin; auto.
          subst.
          eapply Step_None; eauto.
          unfold CntTmImplStateWF in Hwf.
          apply binds_reconstruct in H.
          destruct H as [l1 [l2 Hlist]].
          rewrite Hlist.
          rewrite Hlist in Hwf.
          apply ok_middle_inv in Hwf.
          destruct Hwf as [Hnotin1 Hnotin2].
          repeat rewrite gather_requests_dist.
          simpl.
          rewrite Nat.eqb_refl.
          apply notin_get_none in Hnotin_res.
          rewrite Hnotin_res.
          rewrite remove_notin_app.
          simpl. rewrite Nat.eqb_refl.
          rewrite gather_requests_notin_res; intuition.
          rewrite gather_requests_notin_res; intuition.
          apply gather_requests_preserves_pid_notin; auto.
          apply binds_reconstruct in H.
          destruct H as [l1 [l2 Hlist]].
          rewrite Hlist.
          rewrite gather_responses_dist.
          simpl.
          rewrite Nat.eqb_refl.
          eapply trans_sameset.
          apply sameset_ExF_xEF; auto.
          apply ok_ExF_xEF.
          econstructor; eauto.
          rewrite <-gather_responses_dist.
          apply gather_responses_preserves_ok; auto.
          unfold CntTmImplStateWF in Hwf.
          rewrite Hlist in Hwf.
          apply ok_remove in Hwf; intuition.
          rewrite <-gather_responses_dist.
          apply gather_responses_preserves_pid_notin; auto.
          apply notin_concat.
          unfold CntTmImplStateWF in Hwf.
          rewrite Hlist in Hwf.
          apply ok_middle_inv in Hwf; intuition.
          apply sameset_push_eq; auto.
          eapply trans_sameset.
          2 : { eassumption. }
          rewrite Hlist.
          repeat rewrite gather_responses_dist.
          simpl.
          apply notin_get_none in Hnotin_res.
          rewrite Hnotin_res. simpl.
          unfold CntTmImplStateWF in Hwf.
          rewrite Hlist in Hwf.
          rewrite gather_responses_notin_res.
          rewrite gather_responses_notin_res.
          apply sameset_refl.
          rewrite <-gather_responses_dist.
          apply gather_responses_preserves_ok; auto.
          apply ok_remove in Hwf; intuition.
          apply ok_middle_inv in Hwf; intuition.
          apply ok_middle_inv in Hwf; intuition.
          rewrite <-gather_responses_dist.
          apply gather_responses_preserves_pid_notin; auto.
          unfold CntTmImplStateWF in Hwf.
          rewrite Hlist in Hwf.
          apply notin_concat.
          apply ok_middle_inv in Hwf; intuition.
          apply nat_to_time_S_tick.
        + rewrite gather_pid_events_B_gather_pid_external_events; auto.
        + simpl. apply binds_push_eq; auto.
        + simpl. assumption.
      ---
        simpl.
        unfold composed_counter_timer_wf in H.
        simpl in H.
        destruct H as [Himpl Hbefore].
        unfold ComposedLTS.inv in Hbefore.
        simpl in Hbefore.
        apply Hbefore in Hbinds0; auto.
        clear Hbefore.
        destruct Hbinds0 as
          [s'' [s' [q [acts [Hiq [Hvalid Hgather]]]]]].
        inversion Hiq; subst.
        clear Hiq.
        inversion H; subst.
        clear H.
        inversion H6; subst.
        inversion H3; subst.
        inversion H; subst.
        simpl in *. clear H.
        apply valid_execution_fragment_com in Hvalid.
        simpl in Hvalid.
        eapply valid_execution_fragment_sync in Hvalid; eauto.
        eapply internal_preserves_request with (pid:=pid) (qb:=CntInc) (qb':=CntRead) in Hvalid.
        discriminate.
        eapply gather_pid_events_B_gather_pid_external_events.
        eassumption. simpl.
        apply binds_push_eq; auto.
        simpl. assumption.

        simpl in *.
        generalize (@valid_execution_fragment_com' li_counter li_timer); intro.
        specialize (H _ _ _ _ _ Hvalid).
        simpl in H.
        inversion H3; subst.
        destruct st2. simpl in *.
        eapply valid_execution_fragment_sync in H; eauto.
        apply valid_execution_fragment_com in Hvalid.
        simpl in Hvalid.
        eapply valid_execution_fragment_sync in Hvalid; eauto.

        exists (
          mkTmState
            (remove s2.(requests) pid)
            ((pid, TmReadOk (t s2)) :: s2.(responses))
            (t s2)
        ).
        destruct s2.
        simpl in *.
          unfold CntTmImplStateWF in Himpl.
          assert (Hok_sub : ok (substitute pc pid (CRead2))).
          apply substitute_preserves_ok; auto.
          generalize cnttmimpl_valid_execution_preserves_ok; intro Hwf.
          specialize (Hwf _ _ _ H Hok_sub).
          eapply noB_preserves_CRead2 with (pid:=pid) in H; eauto.
          2 : {
            eapply substitute_eq_binds_v'; eauto.
          }
          2 : {
            rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
            rewrite Hgather. simpl. reflexivity.
          }
          unfold f in *.
          simpl in *.
          rewrite <-H2.
        intuition.
        eapply Step_Internal; eauto.
        eapply timer_step_read with (pid:=pid); eauto.

          apply gather_requests_preserves_ok; auto.
          eapply sameset_ok; eauto.
          apply gather_responses_preserves_ok; auto.
          apply gather_requests_binds_CRead2_binds_TmRead; auto.
          eapply notin_sameset; eauto.
          apply gather_responses_binds_CRead2_notin; auto.
          subst.
          eapply Step_None; eauto.
          unfold CntTmImplStateWF in Hwf.
          apply binds_reconstruct in H.
          destruct H as [l1 [l2 Hlist]].
          rewrite Hlist.
          rewrite Hlist in Hwf.
          apply ok_middle_inv in Hwf.
          destruct Hwf as [Hnotin1 Hnotin2].
          repeat rewrite gather_requests_dist.
          simpl.
          rewrite Nat.eqb_refl.
          apply notin_get_none in Hnotin_res.
          rewrite Hnotin_res.
          rewrite remove_notin_app.
          simpl. rewrite Nat.eqb_refl.
          rewrite gather_requests_notin_res; intuition.
          rewrite gather_requests_notin_res; intuition.
          apply gather_requests_preserves_pid_notin; auto.
          apply binds_reconstruct in H.
          destruct H as [l1 [l2 Hlist]].
          rewrite Hlist.
          rewrite gather_responses_dist.
          simpl.
          rewrite Nat.eqb_refl.
          eapply trans_sameset.
          apply sameset_ExF_xEF; auto.
          apply ok_ExF_xEF.
          econstructor; eauto.
          rewrite <-gather_responses_dist.
          apply gather_responses_preserves_ok; auto.
          unfold CntTmImplStateWF in Hwf.
          rewrite Hlist in Hwf.
          apply ok_remove in Hwf; intuition.
          rewrite <-gather_responses_dist.
          apply gather_responses_preserves_pid_notin; auto.
          apply notin_concat.
          unfold CntTmImplStateWF in Hwf.
          rewrite Hlist in Hwf.
          apply ok_middle_inv in Hwf; intuition.
          rewrite H4.
          apply sameset_push_eq; auto.
          eapply trans_sameset.
          2 : { eassumption. }
          rewrite Hlist.
          repeat rewrite gather_responses_dist.
          simpl.
          apply notin_get_none in Hnotin_res.
          rewrite Hnotin_res. simpl.
          unfold CntTmImplStateWF in Hwf.
          rewrite Hlist in Hwf.
          rewrite gather_responses_notin_res.
          rewrite gather_responses_notin_res.
          apply sameset_refl.
          rewrite <-gather_responses_dist.
          apply gather_responses_preserves_ok; auto.
          apply ok_remove in Hwf; intuition.
          apply ok_middle_inv in Hwf; intuition.
          apply ok_middle_inv in Hwf; intuition.
          rewrite <-gather_responses_dist.
          apply gather_responses_preserves_pid_notin; auto.
          unfold CntTmImplStateWF in Hwf.
          rewrite Hlist in Hwf.
          apply notin_concat.
          apply ok_middle_inv in Hwf; intuition.
  - unfold f in H0.
    intuition.
    inversion H1; subst;
    simpl in *.
    -- clear H1.
      inversion H3; subst.
      simpl in *. clear H3.
      exists s2.
      intuition.
  - inversion H1; subst.
    exists s2. intuition.
      econstructor; eauto.
      unfold f. simpl.
      unfold f in H0. simpl in H0.
      intuition.
    -- inversion H2; inversion H3; subst.
      simpl in *.
      rewrite <-H4.
      inversion H5; subst;
      inversion H13; subst; simpl in *.
      erewrite gather_requests_CTick1_substitute; auto.
      erewrite gather_requests_CRead1_substitute; auto.
    -- inversion H2; inversion H3; subst.
      simpl in *.
      eapply trans_sameset.
      2 : { eassumption. }
      inversion H5; subst;
      inversion H13; subst; simpl in *.
      erewrite gather_responses_CTick1_substitute; auto.
      apply sameset_refl; auto.
      apply gather_responses_preserves_ok; auto.
      erewrite gather_responses_CRead1_substitute; auto.
      apply sameset_refl; auto.
      apply gather_responses_preserves_ok; auto.
    -- inversion H3; subst.
      simpl in *.
      inversion H5; subst;
      intuition.
  - inversion H1; subst.
    exists s2. intuition.
      econstructor; eauto.
      unfold f. simpl.
      unfold f in H0. simpl in H0.
      intuition.
    -- inversion H2; inversion H3; subst.
      simpl in *.
      rewrite <-H4.
      inversion H5; subst;
      inversion H13; subst; simpl in *.
      erewrite gather_requests_CTick2_substitute_remove; auto.
      erewrite gather_requests_CRead2_substitute_remove; auto.
    -- inversion H2; inversion H3; subst.
      simpl in *.
      eapply trans_sameset.
      2 : { eassumption. }
      inversion H5; subst;
      inversion H13; subst; simpl in *.
      erewrite gather_responses_CTick2_substitute_remove; auto.
      apply sameset_refl; auto.
      apply gather_responses_preserves_ok; auto.
      erewrite gather_responses_CRead2_substitute_remove; auto.
      apply sameset_refl; auto.
      apply gather_responses_preserves_ok; auto.
    -- inversion H2; subst.
      simpl in *.
      inversion H5; subst;
      intuition.
Qed.

End Correctness.