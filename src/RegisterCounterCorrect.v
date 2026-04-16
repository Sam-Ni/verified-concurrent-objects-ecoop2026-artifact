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
  VE
  Register
  RegisterProp
  RegisterCounterImpl
  RegisterCounterImplProp
  Counter
  RegisterCounter
  RegisterCounterProp
  RegisterCounterMapping
.
Import ListNotations.

Section Correctness.

Definition f (s1 : register_counter.(state)) (s2 : counter.(state)) :=
  (gather_requests s1.(L2State).(LState).(RegisterCounterImpl.pc) s1.(L1State).(LState).(Register.responses)) = s2.(requests) /\
  sameset (gather_responses s1.(L2State).(LState).(RegisterCounterImpl.pc) s1.(L1State).(LState).(Register.responses)) s2.(responses) /\
  s1.(L1State).(LState).(Register.value) = s2.(value).

Theorem register_counter_correct:
  refines register_counter counter.
Proof.
  eapply composed_forward_simulation_inv_ind' with
    (f:=f) (inv:=composed_register_counter_wf).
  unfold composed_fsim_properties_inv_ind. intuition.
  - apply composed_register_counter_wf_inv.
  - exists (mkCntState [] [] O).
    simpl. unfold counter_new_state.
    intuition.
    unfold f.
    simpl.
    inversion H; subst.
    inversion H0; subst.
    inversion H2; subst.
    rewrite H5. unfold new_register.
    simpl.
    inversion H1; subst.
    inversion H4; subst.
    rewrite H8.
    unfold new_register_counter.
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
        mkCntState
          ((pid, CntInc) :: requests)
          responses
          value
      ).
      simpl. intuition.
      ---
        rewrite <-H2.
        eapply counter_initial_state_inc; eauto.
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
        mkCntState
          ((pid, CntRead) :: requests)
          responses
          value
      ).
      simpl. intuition.
      ---
        rewrite <-H2.
        eapply counter_initial_state_read; eauto.
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
        mkCntState
          requests
          (remove responses pid)
          value
      ).
      simpl. intuition.
      ---
        rewrite <-H2.
        eapply counter_final_state_inc; eauto.
        apply gather_requests_preserves_ok; auto.
        eapply sameset_ok; eauto.
        apply gather_responses_preserves_ok; auto.
        eapply sameset_binds; eauto.
        apply gather_responses_binds_RInc7; auto.
      --- unfold f. simpl.
        intuition.
        rewrite gather_requests_binds_RInc7_remove; auto.
        rewrite gather_responses_remove_comm; auto.
        apply sameset_remove; auto.
    -- destruct s2. simpl in *.
      exists (
        mkCntState
          requests
          (remove responses pid)
          value
      ).
      simpl. intuition.
      ---
        rewrite <-H2.
        eapply counter_final_state_read; eauto.
        apply gather_requests_preserves_ok; auto.
        eapply sameset_ok; eauto.
        apply gather_responses_preserves_ok; auto.
        eapply sameset_binds; eauto.
        apply gather_responses_binds_RRead3; auto.
      --- unfold f. simpl.
        intuition.
        erewrite gather_requests_binds_RRead3_remove; eauto.
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
        unfold composed_register_counter_wf in H.
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
        inversion H1; subst.
        inversion H; subst.
        simpl in *. clear H.
        apply valid_execution_fragment_com in Hvalid.
        simpl in Hvalid.
        eapply valid_execution_fragment_sync in Hvalid; eauto.
        eapply internal_preserves_request with (pid:=pid) (qb:=RegRead) (qb':=RegCAS old new) in Hvalid.
        discriminate.
        eapply gather_pid_events_B_gather_pid_external_events.
        eassumption. simpl.
        apply binds_push_eq; auto.
        simpl. assumption.
        2 : {
        inversion H1; subst.
        inversion H; subst.
        simpl in *. clear H.
        apply valid_execution_fragment_com in Hvalid.
        simpl in Hvalid.
        eapply valid_execution_fragment_sync in Hvalid; eauto.
        eapply internal_preserves_request with (pid:=pid) (qb:=RegRead) (qb':=RegCAS old new) in Hvalid.
        discriminate.
        eapply gather_pid_events_B_gather_pid_external_events.
        eassumption. simpl.
        apply binds_push_eq; auto.
        simpl. assumption.
        }
        inversion H1; subst.
        inversion H; subst.
        simpl in *. clear H.
        generalize (@valid_execution_fragment_com' li_register li_counter); intro.
        specialize (H _ _ _ _ _ Hvalid).
        simpl in H.
        destruct st2. simpl in *.
        eapply valid_execution_fragment_sync in H; eauto.
        apply valid_execution_fragment_com in Hvalid.
        simpl in Hvalid.
        eapply valid_execution_fragment_sync in Hvalid; eauto.
        eapply internal_preserves_request with (pid:=pid) (qb:=RegCAS (r pid) (S (r pid))) (qb':=RegCAS old new) in Hvalid.
        inversion Hvalid; subst.
        clear Hvalid.
        destruct (value s2 =? r pid)eqn:Heq.
        + apply Nat.eqb_eq in Heq.
          subst. 
          simpl in *. subst.
          exists (
            mkCntState
              (remove s2.(requests) pid)
              ((pid, CntIncOk) :: s2.(responses))
              (S (value s2))
          ).
          simpl.
          destruct s2.
          simpl in *.
          unfold RegCntImplStateWF in Himpl.
          assert (Hok_sub : ok (substitute pc pid RInc5)).
          apply substitute_preserves_ok; auto.
          generalize regcntimpl_valid_execution_preserves_ok; intro Hwf.
          specialize (Hwf _ _ _ H Hok_sub).
          eapply noB_preserves_RInc5 with (pid:=pid) in H; eauto.
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
          eapply counter_step_inc with (pid:=pid); eauto.
          apply gather_requests_preserves_ok; auto.
          eapply sameset_ok; eauto.
          apply gather_responses_preserves_ok; auto.
          apply gather_requests_binds_RInc5_binds_CntInc; auto.
          eapply notin_sameset; eauto.
          apply gather_responses_binds_RInc5_notin; auto.
          subst.
          eapply Step_None; eauto.
          unfold RegCntImplStateWF in Hwf.
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
          unfold RegCntImplStateWF in Hwf.
          rewrite Hlist in Hwf.
          apply ok_remove in Hwf; intuition.
          rewrite <-gather_responses_dist.
          apply gather_responses_preserves_pid_notin; auto.
          apply notin_concat.
          unfold RegCntImplStateWF in Hwf.
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
          unfold RegCntImplStateWF in Hwf.
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
          unfold RegCntImplStateWF in Hwf.
          rewrite Hlist in Hwf.
          apply notin_concat.
          apply ok_middle_inv in Hwf; intuition.
        + exists s2. intuition.
          apply Step_None; auto.
          destruct s2.
          simpl in *.
          unfold RegCntImplStateWF in Himpl.
          assert (Hok_sub : ok (substitute pc pid RInc5)).
          apply substitute_preserves_ok; auto.
          generalize regcntimpl_valid_execution_preserves_ok; intro Hwf.
          specialize (Hwf _ _ _ H Hok_sub).
          eapply noB_preserves_RInc5 with (pid:=pid) in H; eauto.
          2 : {
            eapply substitute_eq_binds_v'; eauto.
          }
          2 : {
            rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
            rewrite Hgather. simpl. reflexivity.
          }
          unfold f in *. simpl in *.
          intuition.
          rewrite <-H2.
          rewrite gather_requests_cas_false; auto.
          rewrite gather_responses_cas_false; auto.
        + rewrite gather_pid_events_B_gather_pid_external_events; auto.
        + simpl. apply binds_push_eq; auto.
        + simpl. assumption.
      ---
        simpl.
        unfold composed_register_counter_wf in H.
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
        inversion H4; subst.
        inversion H3; subst.
        inversion H; subst.
        simpl in *. clear H.
        exists s2.
        intuition.
        eapply Step_None; eauto.
        assert (Hbinds' :
          binds pid RInc2 (substitute pc pid RInc2)
        ).
        eapply substitute_eq_binds_v'; eauto.
        generalize (@valid_execution_fragment_com' li_register li_counter); intro.
        specialize (H _ _ _ _ _ Hvalid).
        simpl in H.
        destruct st2. simpl in *.
        eapply valid_execution_fragment_sync in H; eauto.

          eapply noB_preserves_RInc2 with (pid:=pid) in H; eauto.
          2 : {
            rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
            rewrite Hgather. simpl. reflexivity.
          }
        unfold f in *. simpl in *.
        intuition.
        rewrite <-H2.
        rewrite gather_requests_read_ok; auto.
        rewrite gather_responses_read_ok; auto.
        inversion H3; subst.
        inversion H; subst.
        simpl in *. clear H.
        apply valid_execution_fragment_com in Hvalid.
        simpl in Hvalid.
        eapply valid_execution_fragment_sync in Hvalid; eauto.
        eapply internal_preserves_request with (pid:=pid) (qb':=RegRead) (qb:=RegCAS _ _) in Hvalid.
        discriminate.
        eapply gather_pid_events_B_gather_pid_external_events.
        eassumption. simpl.
        apply binds_push_eq; auto.
        simpl. assumption.

        inversion H3; subst.
        inversion H; subst.
        simpl in *. clear H.
        generalize (@valid_execution_fragment_com' li_register li_counter); intro.
        specialize (H _ _ _ _ _ Hvalid).
        simpl in H.
        destruct st2. simpl in *.
        eapply valid_execution_fragment_sync in H; eauto.
        apply valid_execution_fragment_com in Hvalid.
        simpl in Hvalid.
        eapply valid_execution_fragment_sync in Hvalid; eauto.

        exists (
          mkCntState
            (remove s2.(requests) pid)
            ((pid, CntReadOk (value s2)) :: s2.(responses))
            (value s2)
        ).
        destruct s2.
        simpl in *.
          unfold RegCntImplStateWF in Himpl.
          assert (Hok_sub : ok (substitute pc pid RRead2)).
          apply substitute_preserves_ok; auto.
          generalize regcntimpl_valid_execution_preserves_ok; intro Hwf.
          specialize (Hwf _ _ _ H Hok_sub).
          eapply noB_preserves_RRead2 with (pid:=pid) in H; eauto.
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
        eapply counter_step_read with (pid:=pid); eauto.

          apply gather_requests_preserves_ok; auto.
          eapply sameset_ok; eauto.
          apply gather_responses_preserves_ok; auto.
          apply gather_requests_binds_RRead2_binds_CntRead; auto.
          eapply notin_sameset; eauto.
          apply gather_responses_binds_RRead2_notin; auto.
          subst.
          eapply Step_None; eauto.
          unfold RegCntImplStateWF in Hwf.
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
          unfold RegCntImplStateWF in Hwf.
          rewrite Hlist in Hwf.
          apply ok_remove in Hwf; intuition.
          rewrite <-gather_responses_dist.
          apply gather_responses_preserves_pid_notin; auto.
          apply notin_concat.
          unfold RegCntImplStateWF in Hwf.
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
          unfold RegCntImplStateWF in Hwf.
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
          unfold RegCntImplStateWF in Hwf.
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
      intuition. apply Step_None; auto.
      unfold f. simpl.
      intuition.
      inversion H1; subst; simpl in *.
        erewrite gather_requests_binds_RInc3_substitute; eauto.
        erewrite gather_requests_binds_RInc6_substitute; eauto.
        erewrite gather_requests_binds_RInc6_substitute'; eauto.
      inversion H1; subst; simpl in *.
        erewrite gather_responses_binds_RInc3_substitute; eauto.
        erewrite gather_responses_binds_RInc6_substitute; eauto.
        erewrite gather_responses_binds_RInc6_substitute'; eauto.
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
      erewrite gather_requests_RInc1_substitute; auto.
      erewrite gather_requests_RInc4_substitute; auto.
      erewrite gather_requests_RRead1_substitute; auto.
    -- inversion H2; inversion H3; subst.
      simpl in *.
      eapply trans_sameset.
      2 : { eassumption. }
      inversion H5; subst;
      inversion H13; subst; simpl in *.
      erewrite gather_responses_RInc1_substitute; auto.
      apply sameset_refl; auto.
      apply gather_responses_preserves_ok; auto.
      erewrite gather_responses_RInc4_substitute; auto.
      apply sameset_refl; auto.
      apply gather_responses_preserves_ok; auto.
      erewrite gather_responses_RRead1_substitute; auto.
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
      destruct b.
      erewrite gather_requests_RInc5_substitute_remove; auto.
      erewrite gather_requests_RInc5_substitute_remove'; auto.
      erewrite gather_requests_RInc2_substitute_remove; auto.
      erewrite gather_requests_RRead2_substitute_remove; auto.
    -- inversion H2; inversion H3; subst.
      simpl in *.
      eapply trans_sameset.
      2 : { eassumption. }
      inversion H5; subst;
      inversion H13; subst; simpl in *.
      destruct b.
      erewrite gather_responses_RInc5_substitute_remove; auto.
      apply sameset_refl; auto.
      apply gather_responses_preserves_ok; auto.
      erewrite gather_responses_RInc5_substitute_remove'; auto.
      apply sameset_refl; auto.
      apply gather_responses_preserves_ok; auto.
      erewrite gather_responses_RInc2_substitute_remove; auto.
      apply sameset_refl; auto.
      apply gather_responses_preserves_ok; auto.
      erewrite gather_responses_RRead2_substitute_remove; auto.
      apply sameset_refl; auto.
      apply gather_responses_preserves_ok; auto.
    -- inversion H2; subst.
      simpl in *.
      inversion H5; subst;
      intuition.
Qed.

Lemma sync_raw_register_counter_correct:
  refines (sync (linked_lts (raw_compose Register register_counter_impl)))
    counter.
Proof.
  eapply trans_refinement; eauto.
  2 : {
    eapply register_counter_correct.
  }
  apply sync_raw_compose_refines_compose.
  apply register_sync.
  apply register_counter_impl_sync.
Qed.

End Correctness.