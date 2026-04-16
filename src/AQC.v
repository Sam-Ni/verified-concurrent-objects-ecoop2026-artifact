Require Import
  List
  Arith
  LibVar
  LibEnv
  VeriTactics
  LTS
  SyncLTS
  Compose
  ComposedLTS
  Refinement
  ComposedRefinement
  BSim
  Invariants
  VE
  Counter
  Array
  Queue
  ArrayQueueImpl
  ArrayQueueImplProp
  ArrayQueue
  ArrayQueueMapping
  ArrayQueueProp
  ArrayQueueInvariant
  ArrayQueueInvariant2
  ArrayQueueInvariant3
  ArrayToQueue
.
Import ListNotations.

Section test.

Lemma dequeue_some: forall q (v : nat),
  dequeue (q ++ [Some v]) = (Some v, q).
Proof.
  induction q; simpl; intros.
  reflexivity.
  rewrite IHq.
  destruct (q ++ [Some v])eqn:Heq.
  destruct q. inversion Heq.
  inversion Heq.
  reflexivity.
Qed.

Lemma list_reconstruct: forall A (l : list A),
  l = nil \/ (exists l' (x : A), l = l' ++ [x]).
Proof.
  induction l; simpl; intros.
  left. reflexivity.
  intuition. subst. right. exists []. simpl.
  exists a. reflexivity.
  destruct H as [l' [x Hl]].
  subst. right.
  exists (a :: l').
  exists x. simpl. reflexivity.
Qed.



End test.

Section a.

Lemma length_equality : 
  forall A (l l' : list A), l = l' -> length l = length l'.
Proof.
  intros A l l' H.
  rewrite H.
  reflexivity.
Qed.

Lemma not_none_exist: forall x,
  not_none_wrapper x ->
  exists v, x = Some v.
Proof.
  intros. unfold not_none_wrapper in H.
  destruct x.
  exists n. reflexivity.
  intuition.
Qed.

End a.

Section t.

Context {liA liB liC : language_interface}.
Variable L : composed_lts.composed_lts liA liB liC.

Lemma invariant_step: forall s s' pid i,
  composed_lts.reachable L s ->
  composed_lts.step_L1 L s pid i s' ->
  composed_lts.reachable L s'.
Proof.
  intros.
  unfold composed_lts.reachable.
  unfold composed_lts.reachable in H.
  destruct H as [init [acts [Hnew Hvalid]]].
  exists init.
  exists acts. intuition.
  eapply composed_lts.valid_execution_fragment_join'; eauto.
  eapply composed_lts.Step_Internal_L1; eauto.
  eapply composed_lts.Step_None; eauto.
  rewrite app_nil_r.
  reflexivity.
Qed.

End t.

Section test.

Lemma queue_reconstruct: forall (l : list nat),
  l = [] \/
  exists l' e, l = l' ++ [e].
Proof.
  induction l; intros.
  - left. reflexivity.
  - right. intuition.
    rewrite H. exists [], a. 
    reflexivity.
    destruct H as [l' [e Hle]].
    rewrite Hle.
    exists (a :: l').
    exists e.
    reflexivity.
Qed.

End test.

Require Import Program.Wf.

Require Import Lia.

Section Correctness.

Variable L : nat.
Hypothesis H : 0 < L.

Arguments array_to_queue {L}.

Lemma array_to_queue_not_empty: forall f r vec,
  f < r ->
  array_to_queue H f r vec <> [].
Proof.
  intros. intro.
  assert (length (array_to_queue H f r vec) = 0).
  rewrite H1. simpl. reflexivity.
  rewrite array_to_queue_length in H2.
  lia.
Qed.

Lemma lt_neq_0: forall f r,
  f < r -> r <> 0.
Proof.
  intros. lia.
Qed.

Lemma neq_0_exist: forall r,
  r <> 0 -> exists r', r = S r'.
Proof.
  intros. destruct r.
  intuition.
  exists r. reflexivity.
Qed.

Definition AQ := composed_array_queue L.
Definition Q := queue L.

Definition f (s1 : composed_lts.state AQ) (s2 : state Q) :=
  let sync_acc := s1.(Compose.L1State) in
  let acc := sync_acc.(LState) in
  let sync_ary := acc.(Tensor.L1State) in
  let ary := sync_ary.(LState) in
  let sync_front_rear := acc.(Tensor.L2State) in
  let front_rear := sync_front_rear.(LState) in
  let sync_front := front_rear.(Tensor.L1State) in
  let front := sync_front.(LState) in
  let sync_rear := front_rear.(Tensor.L2State) in
  let rear := sync_rear.(LState) in
  let sync_aqimpl := s1.(Compose.L2State) in
  let aqimpl := sync_aqimpl.(LState) in
  let pc := aqimpl.(pc) in
  (gather_requests pc aqimpl.(vp) aqimpl.(ArrayQueueImpl.front) aqimpl.(ArrayQueueImpl.rear) 
    ary.(Array.responses L) front.(Counter.responses) rear.(Counter.responses))
    = (s2.(requests)) /\
  ((gather_responses pc aqimpl.(ArrayQueueImpl.front) aqimpl.(ArrayQueueImpl.rear) aqimpl.(x)
    ary.(Array.responses L) front.(Counter.responses) rear.(Counter.responses))
     = s2.(responses)) /\
    (array_to_queue H
      (F L s1) (R L s1)
      ary.(vec L)
    )
    = s2.(q)
.

Arguments inv {liA liB L1 L2}.

Definition array_queue_wf (s : composed_lts.state AQ) :=
  let sync_aqimpl := s.(Compose.L2State) in
  let aqimpl := sync_aqimpl.(LState) in
  let pc := aqimpl.(pc) in
  ok pc /\
  inv s.

Lemma array_queue_wf_inv: composed_lts.invariant_ind (composed_array_queue L) array_queue_wf.
Proof.
  unfold array_queue_wf.
  apply composed_lts.invariant_ind_land.
  2 : { apply step_inv. }
  unfold composed_lts.invariant_ind. intuition.
  - inversion H0; subst.
    inversion H2; subst.
    inversion H3; subst.
    rewrite H6.
    unfold new_array_queue.
    simpl.
    econstructor.
  - inversion H1; subst; simpl in *; intuition.
  - inversion H1; subst.
    inversion H2; subst.
    inversion H3; subst; simpl in *;
    apply substitute_preserves_ok; auto.
  - inversion H1; subst.
    inversion H2; subst.
    inversion H3; subst; simpl in *;
    econstructor; eauto.
  - destruct act.
  - destruct act.
  - inversion H1; subst.
    inversion H2; subst.
    inversion H3; subst; simpl in *;
    apply remove_preserves_ok; auto.
  - inversion H1; subst.
    inversion H2; subst.
    inversion H3; subst.
    inversion H4; subst; simpl in *;
    apply substitute_preserves_ok; auto.
  - inversion H1; subst.
    inversion H2; subst.
    inversion H3; subst.
    inversion H5; subst; simpl in *;
    apply substitute_preserves_ok; auto.
Qed.

Definition array_queue_wf' (s : composed_lts.state (composed_array_queue L)) :=
  array_queue_wf s /\
  composed_lts.reachable (composed_array_queue L) s.

Lemma array_queue_wf'_inv: composed_lts.invariant_ind (composed_array_queue L) array_queue_wf'.
Proof.
  unfold array_queue_wf'.
  apply composed_lts.invariant_ind_land.
  2 : { apply reachable_is_invariant. }
  apply array_queue_wf_inv.
Qed.

Theorem array_queue_correct:
  refines (array_queue L) (queue L).
  eapply composed_backward_simulation_inv_ind' with
    (f:=f) (inv:=array_queue_wf').
  unfold composed_bsim_properties_inv_ind. intuition.
  - apply array_queue_wf'_inv.
  - pose s1 as s11.
    destruct s1 as (sync_acc, sync_arimpl).
    destruct sync_acc as (acc, acc_pos).
    destruct acc as (sync_ary, sync_cc).
    destruct sync_ary as (ary, ary_pos).
    destruct sync_cc as (cc, cc_pos).
    destruct cc as (sync_Front, sync_Rear).
    destruct sync_Front as (Front, Front_cc).
    destruct sync_Rear as (Rear, Rear_cc).
    destruct sync_arimpl as (arimpl, arimpl_pos).
    destruct arimpl as (pc, front, rear, x, vp, f, r).
    exists (mkQState 
      (gather_requests pc vp front rear 
        ary.(Array.responses L) Front.(Counter.responses) Rear.(Counter.responses))
      (gather_responses pc front rear x 
        ary.(Array.responses L) Front.(Counter.responses) Rear.(Counter.responses))
        (
        (array_to_queue H
          (F L s11) (R L s11)
          ary.(vec L)
        )
      )
    ).
    unfold Correctness.f. simpl. intuition.
  - destruct s1 as (sync_acc, sync_arimpl).
    destruct sync_acc as (acc, acc_pos).
    destruct acc as (sync_ary, sync_cc).
    destruct sync_ary as (ary, ary_pos).
    destruct sync_cc as (cc, cc_pos).
    destruct cc as (sync_Front, sync_Rear).
    destruct sync_Front as (Front, Front_cc).
    destruct sync_Rear as (Rear, Rear_cc).
    destruct sync_arimpl as (arimpl, arimpl_pos).
    destruct arimpl as (pc, front, rear, x, vp, f, r).
    simpl in *.
    inversion H0; subst. clear H0.
    inversion H2; subst. clear H2. simpl in *.
    inversion H3; subst. clear H3. simpl in *.
    inversion H0; subst. clear H0. simpl in *.
    inversion H3; subst. clear H3. simpl in *.
    inversion H0; subst.
    inversion H2; subst.
    inversion H4; subst. clear H4.
    inversion H3; subst. clear H3. simpl in *.
    inversion H4; subst. clear H4. simpl in *.
    inversion H3; subst.
    inversion H6; subst. clear H6. simpl in *.
    inversion H4; subst. simpl in *.
    unfold Correctness.f in H1. intuition. simpl in *.
    unfold queue_new_state. intuition.
  - unfold f in H1.
    destruct H1 as [Hreq [Hres Hmap]].
    inversion H2; subst.
    simpl in *. clear H2.
    inversion H1; subst.
    simpl in *. clear H1.
    inversion H2; subst; simpl in *.
    -- destruct s2'. simpl in *.
      exists (mkQState
        (remove requests pid)
        responses
        q
      ).
      simpl. intuition.
      ---
        rewrite <-Hreq.
        simpl. rewrite Nat.eqb_refl.
        eapply queue_initial_state_enq; eauto.
        apply gather_requests_preserves_notin; auto.
        rewrite <-Hres.
        apply gather_responses_preserves_notin; auto.
        apply gather_requests_preserves_ok; auto.
        rewrite <-Hres.
        apply gather_responses_preserves_ok; auto.
      --- unfold f. simpl.
        intuition.
        rewrite <-Hreq.
        simpl. rewrite Nat.eqb_refl.
        rewrite gather_requests_vp; auto.
    -- destruct s2'. simpl in *.
      exists (mkQState
        (remove requests pid)
        responses
        q
      ).
      simpl. intuition.
      ---
        rewrite <-Hreq.
        simpl. rewrite Nat.eqb_refl.
        eapply queue_initial_state_deq; eauto.
        apply gather_requests_preserves_notin; auto.
        rewrite <-Hres.
        apply gather_responses_preserves_notin; auto.
        apply gather_requests_preserves_ok; auto.
        rewrite <-Hres.
        apply gather_responses_preserves_ok; auto.
      --- unfold f. simpl.
        intuition.
        rewrite <-Hreq.
        simpl. rewrite Nat.eqb_refl.
        reflexivity.
  - unfold f in H1.
    destruct H1 as [Hreq [Hres Hmap]].
    inversion H2; subst.
    simpl in *. clear H2.
    inversion H1; subst.
    simpl in *. clear H1.
    inversion H2; subst; simpl in *.
    -- destruct s2'. simpl in *.
      exists (mkQState
        requests
(gather_responses (pc) front rear x
            (Array.responses L (LState (Tensor.L1State (LState st1))))
            (Counter.responses
               (LState
                  (Tensor.L1State
                     (LState (Tensor.L2State (LState st1))))))
            (Counter.responses
               (LState
                  (Tensor.L2State
                     (LState (Tensor.L2State (LState st1)))))))
        q
      ).
      simpl. intuition.
      ---
        rewrite <-Hreq.
        eapply queue_final_state_enq; eauto.
        apply gather_requests_preserves_ok; auto.
        apply remove_preserves_ok; auto.
        apply gather_responses_preserves_ok; auto.
        apply gather_responses_binds_AEnq32; auto.
        rewrite <-Hres.
        rewrite gather_responses_remove_comm; auto.
      --- unfold f. simpl.
        intuition.
        f_equal.
        rewrite <-Hreq.
        rewrite gather_requests_binds_AEnq32_remove; auto.
        clear H2.
        clear Hreq.
        clear Hres.
        rewrite <-Hmap.
        apply binds_reconstruct in Hbinds0.
        destruct Hbinds0 as [l1 [l2 Hlist]].
        rewrite Hlist in Hok_pc.
        rewrite Hlist.
        apply ok_remove_middle_inv in Hok_pc.
        rewrite remove_notin_app; intuition.
        simpl. rewrite Nat.eqb_refl.
        unfold R, F.
        unfold get_front, get_rear, get_ary, get_pc.
        simpl.
        rewrite get_f'_dist.
        rewrite get_f'_dist. simpl get_f'.
        rewrite get_r'_dist.
        rewrite get_r'_dist. simpl get_r'.
        reflexivity.
    -- destruct s2'. simpl in *.
      exists (mkQState
        requests
(gather_responses (pc) front rear x
            (Array.responses L (LState (Tensor.L1State (LState st1))))
            (Counter.responses
               (LState
                  (Tensor.L1State
                     (LState (Tensor.L2State (LState st1))))))
            (Counter.responses
               (LState
                  (Tensor.L2State
                     (LState (Tensor.L2State (LState st1)))))))
        q
      ).
      simpl. intuition.
      ---
        rewrite <-Hreq.
        eapply queue_final_state_deq; eauto.
        apply gather_requests_preserves_ok; auto.
        apply remove_preserves_ok; auto.
        apply gather_responses_preserves_ok; auto.
        apply gather_responses_binds_ADeq32; auto.
        rewrite <-Hres.
        rewrite gather_responses_remove_comm; auto.
      --- unfold f. simpl.
        intuition.
        f_equal.
        rewrite <-Hreq.
        rewrite gather_requests_binds_ADeq32_remove; auto.
        clear H2.
        clear Hreq.
        clear Hres.
        rewrite <-Hmap.
        apply binds_reconstruct in Hbinds0.
        destruct Hbinds0 as [l1 [l2 Hlist]].
        rewrite Hlist in Hok_pc.
        rewrite Hlist.
        apply ok_remove_middle_inv in Hok_pc.
        rewrite remove_notin_app; intuition.
        simpl. rewrite Nat.eqb_refl.
        unfold R, F;
        unfold get_front, get_rear, get_ary, get_pc;
        simpl;
        rewrite get_f'_dist;
        rewrite get_f'_dist; simpl get_f';
        rewrite get_r'_dist;
        rewrite get_r'_dist; simpl get_r';
        reflexivity.
  - unfold f in H1.
    destruct H1 as [Hreq [Hres Hmap]].
    inversion H2; subst.
    simpl in *.
    inversion H1; subst.
    simpl in *. 
    inversion H3; subst; simpl in *.
    (* front_rear step *)
    -- inversion H4; subst; simpl in *.
      inversion H5; subst.
      (* rear step *)
      --- inversion H6; subst; simpl in *.
        inversion H7; subst; simpl in *.
        (* rear inc, not a linearization point*)
        + exists s2'.
          intuition.
          apply Step_None; auto.
          unfold f. simpl.
          intuition.
          ++ rewrite <-Hreq.
            apply H0 in Hbinds0.
            destruct Hbinds0 as [s1 [s2 [qb [acts [Hint_query [Hvalid Hgather]]]]]].
            inversion Hint_query; subst.
            simpl in qb.
            (* try to exclude other query *)
            destruct qb; simpl in *.
            (* exclude query of array *)
            +++ apply valid_execution_fragment_com in Hvalid.
                simpl in Hvalid.
                eapply internal_preserves_notin' with (pid:=pid) in Hvalid; simpl in *.
                apply binds_in in Hbinds1.
                unfold "#" in Hvalid.
                intuition.
                eapply gather_pid_events_B_gather_pid_external_events.
                eassumption.
                inversion H9; subst; simpl in *; intuition.
                inversion H10; subst; simpl in *; intuition.
            (* case of query front_rear *)
            +++ destruct q; simpl in *.
              (* exclude query front *)
              * apply valid_execution_fragment_com in Hvalid.
                simpl in Hvalid.
                eapply internal_preserves_notin'' with (pid:=pid) in Hvalid; simpl in *.
                apply binds_in in Hbinds4.
                unfold "#" in Hvalid.
                intuition.
                eapply gather_pid_events_B_gather_pid_external_events.
                eassumption.
                inversion H9; subst; simpl in *; intuition.
                inversion H10; subst; simpl in *; intuition.
                inversion H12; subst; simpl in *; intuition.
                inversion H11; subst; simpl in *; intuition.
              (* case of query rear *)
              * destruct q.
                ** apply valid_execution_fragment_com' in Hvalid.
                  simpl in Hvalid.
                  destruct st2', st2.
                  eapply valid_execution_fragment_sync in Hvalid; eauto.
                  simpl.
                  inversion H8; subst.
                  inversion H10; subst; simpl.
                  *** eapply noB_preserves_AEnq31 with (pid:=pid) in Hvalid; eauto.
                    2 : {
                      destruct LState.
                      inversion H12; subst.
                      simpl.
                      eapply substitute_eq_binds_v'; eauto.
                    }
                    2 : {
                      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil).
                      rewrite Hgather. simpl. reflexivity.
                      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
                      assumption.
                    }
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                    apply binds_reconstruct in Hvalid.
                    destruct Hvalid as [l1 [l2 Hlist]].
                    rewrite Hlist in Hok_wf.
                    apply ok_remove_middle_inv in Hok_wf.
                    rewrite Hlist.
                    repeat rewrite gather_requests_dist.
                    simpl.
                    repeat rewrite gather_requests_res_rear'; intuition.
                (* exclude rear read *)
                ** apply valid_execution_fragment_com in Hvalid.
                  simpl in Hvalid.
                  inversion H9; subst.
                  inversion H10; subst.
                  inversion H12; subst.
                  inversion H11; subst.
                  inversion H14; subst.
                  inversion H13; subst.
                  eapply internal_preserves_request with (pid:=pid) in Hvalid; simpl in *.
                  4 : { apply Hbinds5. }
                  3 : {
                    apply binds_push_eq.
                  }
                  discriminate.
                  eapply gather_pid_events_B_gather_pid_external_events.
                  eassumption.
          ++ rewrite <-Hres.
            apply H0 in Hbinds0.
            destruct Hbinds0 as [s1 [s2 [qb [acts [Hint_query [Hvalid Hgather]]]]]].
            inversion Hint_query; subst.
            simpl in qb.
            destruct qb; simpl in *.
            +++ apply valid_execution_fragment_com in Hvalid.
                simpl in Hvalid.
                eapply internal_preserves_notin' with (pid:=pid) in Hvalid; simpl in *.
                apply binds_in in Hbinds1.
                unfold "#" in Hvalid.
                intuition.
                eapply gather_pid_events_B_gather_pid_external_events.
                eassumption.
                inversion H9; subst; simpl in *; intuition.
                inversion H10; subst; simpl in *; intuition.
            +++ destruct q; simpl in *.
              * apply valid_execution_fragment_com in Hvalid.
                simpl in Hvalid.
                eapply internal_preserves_notin'' with (pid:=pid) in Hvalid; simpl in *.
                apply binds_in in Hbinds4.
                unfold "#" in Hvalid.
                intuition.
                eapply gather_pid_events_B_gather_pid_external_events.
                eassumption.
                inversion H9; subst; simpl in *; intuition.
                inversion H10; subst; simpl in *; intuition.
                inversion H12; subst; simpl in *; intuition.
                inversion H11; subst; simpl in *; intuition.
              * destruct q.
                ** apply valid_execution_fragment_com' in Hvalid.
                  simpl in Hvalid.
                  destruct st2', st2.
                  eapply valid_execution_fragment_sync in Hvalid; eauto.
                  simpl.
                  inversion H8; subst.
                  inversion H10; subst; simpl.
                  *** eapply noB_preserves_AEnq31 with (pid:=pid) in Hvalid; eauto.
                    2 : {
                      destruct LState.
                      inversion H12; subst.
                      simpl.
                      eapply substitute_eq_binds_v'; eauto.
                    }
                    2 : {
                      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil).
                      rewrite Hgather. simpl. reflexivity.
                      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
                      assumption.
                    }
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    destruct Hwf as [Hok_wf _].
                    unfold array_queue_wf in Hok_wf.
                    simpl in Hok_wf.
                    apply binds_reconstruct in Hvalid.
                    destruct Hvalid as [l1 [l2 Hlist]].
                    rewrite Hlist in Hok_wf.
                    apply ok_remove_middle_inv in Hok_wf.
                    rewrite Hlist.
                    repeat rewrite gather_responses_dist.
                    simpl.
                    repeat rewrite gather_responses_res_rear'; intuition.
                ** apply valid_execution_fragment_com in Hvalid.
                  simpl in Hvalid.
                  inversion H9; subst.
                  inversion H10; subst.
                  inversion H12; subst.
                  inversion H11; subst.
                  inversion H14; subst.
                  inversion H13; subst.
                  eapply internal_preserves_request with (pid:=pid) in Hvalid; simpl in *.
                  4 : { apply Hbinds5. }
                  3 : {
                    apply binds_push_eq.
                  }
                  discriminate.
                  eapply gather_pid_events_B_gather_pid_external_events.
                  eassumption.
          ++ unfold F, R;
            unfold get_front, get_rear, get_ary, get_pc;
            simpl.
            unfold F, R in Hmap;
            unfold get_front, get_rear, get_ary, get_pc in Hmap.
            simpl in Hmap.
            rewrite <-Hmap.
            
            f_equal.
            destruct H0 as [Hwf Hreach].
            apply inv_rear_inc_at_e31_invariant in Hreach.
            apply Hreach in Hbinds5.
            simpl in Hbinds5.
            unfold array_queue_wf in Hwf.
            destruct Hwf as [Hok_wf _].
            simpl in Hok_wf.
            apply binds_reconstruct in Hbinds5.
            destruct Hbinds5 as [l1 [l2 Hlist]].
            rewrite Hlist in Hok_wf.
            apply ok_remove_middle_inv in Hok_wf.
            destruct Hok_wf as [Hokwf1 Hokwf2].
            destruct Hokwf2 as [Hokwf21 Hokwf22].
            rewrite Hlist.
            repeat rewrite get_r'_dist; auto.
            simpl.
            rewrite Nat.eqb_refl.
            apply notin_get_none in Hnotin_res.
            rewrite Hnotin_res.
            simpl.
            repeat rewrite get_r'_any_rear_push; auto.
            rewrite plus_n_Sm.
            rewrite plus_n_Sm.
            reflexivity.

        (* rear read, not a linearization point in the blocking queue *)
        + exists s2'.
          intuition.
          apply Step_None; auto.
          unfold f. simpl. intuition.
          ++ rewrite <-Hreq.
            apply H0 in Hbinds0.
            destruct Hbinds0 as [s1 [s2 [qb [acts [Hint_query [Hvalid Hgather]]]]]].
            inversion Hint_query; subst.
            simpl in qb.
            (* try to exclude other query *)
            destruct qb; simpl in *.
            (* exclude query of array *)
            +++ apply valid_execution_fragment_com in Hvalid.
                simpl in Hvalid.
                eapply internal_preserves_notin' with (pid:=pid) in Hvalid; simpl in *.
                apply binds_in in Hbinds1.
                unfold "#" in Hvalid.
                intuition.
                eapply gather_pid_events_B_gather_pid_external_events.
                eassumption.
                inversion H9; subst; simpl in *; intuition.
                inversion H10; subst; simpl in *; intuition.
            (* case of query front_rear *)
            +++ destruct q; simpl in *.
              (* exclude query front *)
              * apply valid_execution_fragment_com in Hvalid.
                simpl in Hvalid.
                eapply internal_preserves_notin'' with (pid:=pid) in Hvalid; simpl in *.
                apply binds_in in Hbinds4.
                unfold "#" in Hvalid.
                intuition.
                eapply gather_pid_events_B_gather_pid_external_events.
                eassumption.
                inversion H9; subst; simpl in *; intuition.
                inversion H10; subst; simpl in *; intuition.
                inversion H12; subst; simpl in *; intuition.
                inversion H11; subst; simpl in *; intuition.
              (* case of query rear *)
              * destruct q.
                (* exclude rear inc *)
                ** apply valid_execution_fragment_com in Hvalid.
                  simpl in Hvalid.
                  inversion H9; subst.
                  inversion H10; subst.
                  inversion H12; subst.
                  inversion H11; subst.
                  inversion H14; subst.
                  inversion H13; subst.
                  eapply internal_preserves_request with (pid:=pid) in Hvalid; simpl in *.
                  4 : { apply Hbinds5. }
                  3 : {
                    apply binds_push_eq.
                  }
                  discriminate.
                  eapply gather_pid_events_B_gather_pid_external_events.
                  eassumption.
                ** apply valid_execution_fragment_com' in Hvalid.
                  simpl in Hvalid.
                  destruct st2', st2.
                  eapply valid_execution_fragment_sync in Hvalid; eauto.
                  simpl.
                  inversion H8; subst.
                  inversion H10; subst; simpl.
                  *** eapply noB_preserves_AEnq2 with (pid:=pid) in Hvalid; eauto.
                    2 : {
                      destruct LState.
                      inversion H12; subst.
                      simpl.
                      eapply substitute_eq_binds_v'; eauto.
                    }
                    2 : {
                      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil).
                      rewrite Hgather. simpl. reflexivity.
                      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
                      assumption.
                    }
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                    apply binds_reconstruct in Hvalid.
                    destruct Hvalid as [l1 [l2 Hlist]].
                    rewrite Hlist in Hok_wf.
                    apply ok_remove_middle_inv in Hok_wf.
                    rewrite Hlist.
                    repeat rewrite gather_requests_dist.
                    simpl.
                    repeat rewrite gather_requests_res_rear'; intuition.
                  *** eapply noB_preserves_AEnq11 with (pid:=pid) in Hvalid; eauto.
                    2 : {
                      destruct LState.
                      inversion H12; subst.
                      simpl.
                      eapply substitute_eq_binds_v'; eauto.
                    }
                    2 : {
                      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil).
                      rewrite Hgather. simpl. reflexivity.
                      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
                      assumption.
                    }
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                    apply binds_reconstruct in Hvalid.
                    destruct Hvalid as [l1 [l2 Hlist]].
                    rewrite Hlist in Hok_wf.
                    apply ok_remove_middle_inv in Hok_wf.
                    rewrite Hlist.
                    repeat rewrite gather_requests_dist.
                    simpl.
                    repeat rewrite gather_requests_res_rear'; intuition.
                  *** eapply noB_preserves_ADeq14 with (pid:=pid) in Hvalid; eauto.
                    2 : {
                      destruct LState.
                      inversion H12; subst.
                      simpl.
                      eapply substitute_eq_binds_v'; eauto.
                    }
                    2 : {
                      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil).
                      rewrite Hgather. simpl. reflexivity.
                      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
                      assumption.
                    }
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                    apply binds_reconstruct in Hvalid.
                    destruct Hvalid as [l1 [l2 Hlist]].
                    rewrite Hlist in Hok_wf.
                    apply ok_remove_middle_inv in Hok_wf.
                    rewrite Hlist.
                    repeat rewrite gather_requests_dist.
                    simpl.
                    repeat rewrite gather_requests_res_rear'; intuition.
          ++ rewrite <-Hres.
            apply H0 in Hbinds0.
            destruct Hbinds0 as [s1 [s2 [qb [acts [Hint_query [Hvalid Hgather]]]]]].
            inversion Hint_query; subst.
            simpl in qb.
            (* try to exclude other query *)
            destruct qb; simpl in *.
            (* exclude query of array *)
            +++ apply valid_execution_fragment_com in Hvalid.
                simpl in Hvalid.
                eapply internal_preserves_notin' with (pid:=pid) in Hvalid; simpl in *.
                apply binds_in in Hbinds1.
                unfold "#" in Hvalid.
                intuition.
                eapply gather_pid_events_B_gather_pid_external_events.
                eassumption.
                inversion H9; subst; simpl in *; intuition.
                inversion H10; subst; simpl in *; intuition.
            (* case of query front_rear *)
            +++ destruct q; simpl in *.
              (* exclude query front *)
              * apply valid_execution_fragment_com in Hvalid.
                simpl in Hvalid.
                eapply internal_preserves_notin'' with (pid:=pid) in Hvalid; simpl in *.
                apply binds_in in Hbinds4.
                unfold "#" in Hvalid.
                intuition.
                eapply gather_pid_events_B_gather_pid_external_events.
                eassumption.
                inversion H9; subst; simpl in *; intuition.
                inversion H10; subst; simpl in *; intuition.
                inversion H12; subst; simpl in *; intuition.
                inversion H11; subst; simpl in *; intuition.
              (* case of query rear *)
              * destruct q.
                (* exclude rear inc *)
                ** apply valid_execution_fragment_com in Hvalid.
                  simpl in Hvalid.
                  inversion H9; subst.
                  inversion H10; subst.
                  inversion H12; subst.
                  inversion H11; subst.
                  inversion H14; subst.
                  inversion H13; subst.
                  eapply internal_preserves_request with (pid:=pid) in Hvalid; simpl in *.
                  4 : { apply Hbinds5. }
                  3 : {
                    apply binds_push_eq.
                  }
                  discriminate.
                  eapply gather_pid_events_B_gather_pid_external_events.
                  eassumption.
                ** apply valid_execution_fragment_com' in Hvalid.
                  simpl in Hvalid.
                  destruct st2', st2.
                  eapply valid_execution_fragment_sync in Hvalid; eauto.
                  simpl.
                  inversion H8; subst.
                  inversion H10; subst; simpl.
                  *** eapply noB_preserves_AEnq2 with (pid:=pid) in Hvalid; eauto.
                    2 : {
                      destruct LState.
                      inversion H12; subst.
                      simpl.
                      eapply substitute_eq_binds_v'; eauto.
                    }
                    2 : {
                      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil).
                      rewrite Hgather. simpl. reflexivity.
                      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
                      assumption.
                    }
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                    apply binds_reconstruct in Hvalid.
                    destruct Hvalid as [l1 [l2 Hlist]].
                    rewrite Hlist in Hok_wf.
                    apply ok_remove_middle_inv in Hok_wf.
                    rewrite Hlist.
                    repeat rewrite gather_responses_dist.
                    simpl.
                    repeat rewrite gather_responses_res_rear'; intuition.
                  *** eapply noB_preserves_AEnq11 with (pid:=pid) in Hvalid; eauto.
                    2 : {
                      destruct LState.
                      inversion H12; subst.
                      simpl.
                      eapply substitute_eq_binds_v'; eauto.
                    }
                    2 : {
                      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil).
                      rewrite Hgather. simpl. reflexivity.
                      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
                      assumption.
                    }
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                    apply binds_reconstruct in Hvalid.
                    destruct Hvalid as [l1 [l2 Hlist]].
                    rewrite Hlist in Hok_wf.
                    apply ok_remove_middle_inv in Hok_wf.
                    rewrite Hlist.
                    repeat rewrite gather_responses_dist.
                    simpl.
                    repeat rewrite gather_responses_res_rear'; intuition.
                  *** eapply noB_preserves_ADeq14 with (pid:=pid) in Hvalid; eauto.
                    2 : {
                      destruct LState.
                      inversion H12; subst.
                      simpl.
                      eapply substitute_eq_binds_v'; eauto.
                    }
                    2 : {
                      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil).
                      rewrite Hgather. simpl. reflexivity.
                      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
                      assumption.
                    }
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                    apply binds_reconstruct in Hvalid.
                    destruct Hvalid as [l1 [l2 Hlist]].
                    rewrite Hlist in Hok_wf.
                    apply ok_remove_middle_inv in Hok_wf.
                    rewrite Hlist.
                    repeat rewrite gather_responses_dist.
                    simpl.
                    repeat rewrite gather_responses_res_rear'; intuition.
          ++ unfold F, R;
            unfold get_front, get_rear, get_ary, get_pc;
            simpl.
            unfold F, R in Hmap;
            unfold get_front, get_rear, get_ary, get_pc in Hmap.
            simpl in Hmap.
            rewrite <-Hmap.
            f_equal.
            repeat rewrite get_r'_any_rear_read; auto.

      (* front step *)
      --- inversion H6; subst; simpl in *.
        inversion H7; subst; simpl in *.
        (* front inc, not a linearization point*)
        + exists s2'.
          intuition.
          apply Step_None; auto.
          unfold f. simpl. intuition.
          ++ rewrite <-Hreq.
            apply H0 in Hbinds0.
            destruct Hbinds0 as [s1 [s2 [qb [acts [Hint_query [Hvalid Hgather]]]]]].
            inversion Hint_query; subst.
            simpl in qb.
            (* try to exclude other query *)
            destruct qb; simpl in *.
            (* exclude query of array *)
            +++ apply valid_execution_fragment_com in Hvalid.
                simpl in Hvalid.
                eapply internal_preserves_notin' with (pid:=pid) in Hvalid; simpl in *.
                apply binds_in in Hbinds1.
                unfold "#" in Hvalid.
                intuition.
                eapply gather_pid_events_B_gather_pid_external_events.
                eassumption.
                inversion H9; subst; simpl in *; intuition.
                inversion H10; subst; simpl in *; intuition.
            (* case of query front_rear *)
            +++ destruct q; simpl in *.
              (* case of query front *)
              * destruct q.
                ** apply valid_execution_fragment_com' in Hvalid.
                  simpl in Hvalid.
                  destruct st2', st2.
                  eapply valid_execution_fragment_sync in Hvalid; eauto.
                  simpl.
                  inversion H8; subst.
                  inversion H10; subst; simpl.
                  *** eapply noB_preserves_ADeq31 with (pid:=pid) in Hvalid; eauto.
                    2 : {
                      destruct LState.
                      inversion H12; subst.
                      simpl.
                      eapply substitute_eq_binds_v'; eauto.
                    }
                    2 : {
                      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil).
                      rewrite Hgather. simpl. reflexivity.
                      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
                      assumption.
                    }
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                    apply binds_reconstruct in Hvalid.
                    destruct Hvalid as [l1 [l2 Hlist]].
                    rewrite Hlist in Hok_wf.
                    apply ok_remove_middle_inv in Hok_wf.
                    rewrite Hlist.
                    repeat rewrite gather_requests_dist.
                    simpl.
                    repeat rewrite gather_requests_res_front'; intuition.
                (* exclude front read *)
                ** apply valid_execution_fragment_com in Hvalid.
                  simpl in Hvalid.
                  inversion H9; subst.
                  inversion H10; subst.
                  inversion H12; subst.
                  inversion H11; subst.
                  inversion H14; subst.
                  inversion H13; subst.
                  eapply internal_preserves_request' with (pid:=pid) in Hvalid; simpl in *.
                  4 : { apply Hbinds5. }
                  3 : {
                    apply binds_push_eq.
                  }
                  discriminate.
                  eapply gather_pid_events_B_gather_pid_external_events.
                  eassumption.
              (* exclude query rear *)
              * apply valid_execution_fragment_com in Hvalid.
                simpl in Hvalid.
                eapply internal_preserves_notin''' with (pid:=pid) in Hvalid; simpl in *.
                apply binds_in in Hbinds4.
                unfold "#" in Hvalid.
                intuition.
                eapply gather_pid_events_B_gather_pid_external_events.
                eassumption.
                inversion H9; subst; simpl in *; intuition.
                inversion H10; subst; simpl in *; intuition.
                inversion H12; subst; simpl in *; intuition.
                inversion H11; subst; simpl in *; intuition.
          ++ rewrite <-Hres.
            apply H0 in Hbinds0.
            destruct Hbinds0 as [s1 [s2 [qb [acts [Hint_query [Hvalid Hgather]]]]]].
            inversion Hint_query; subst.
            simpl in qb.
            (* try to exclude other query *)
            destruct qb; simpl in *.
            (* exclude query of array *)
            +++ apply valid_execution_fragment_com in Hvalid.
                simpl in Hvalid.
                eapply internal_preserves_notin' with (pid:=pid) in Hvalid; simpl in *.
                apply binds_in in Hbinds1.
                unfold "#" in Hvalid.
                intuition.
                eapply gather_pid_events_B_gather_pid_external_events.
                eassumption.
                inversion H9; subst; simpl in *; intuition.
                inversion H10; subst; simpl in *; intuition.
            (* case of query front_rear *)
            +++ destruct q; simpl in *.
              (* case of query front *)
              * destruct q.
                ** apply valid_execution_fragment_com' in Hvalid.
                  simpl in Hvalid.
                  destruct st2', st2.
                  eapply valid_execution_fragment_sync in Hvalid; eauto.
                  simpl.
                  inversion H8; subst.
                  inversion H10; subst; simpl.
                  *** eapply noB_preserves_ADeq31 with (pid:=pid) in Hvalid; eauto.
                    2 : {
                      destruct LState.
                      inversion H12; subst.
                      simpl.
                      eapply substitute_eq_binds_v'; eauto.
                    }
                    2 : {
                      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil).
                      rewrite Hgather. simpl. reflexivity.
                      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
                      assumption.
                    }
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                    apply binds_reconstruct in Hvalid.
                    destruct Hvalid as [l1 [l2 Hlist]].
                    rewrite Hlist in Hok_wf.
                    apply ok_remove_middle_inv in Hok_wf.
                    rewrite Hlist.
                    repeat rewrite gather_responses_dist.
                    simpl.
                    repeat rewrite gather_responses_res_front'; intuition.
                (* exclude front read *)
                ** apply valid_execution_fragment_com in Hvalid.
                  simpl in Hvalid.
                  inversion H9; subst.
                  inversion H10; subst.
                  inversion H12; subst.
                  inversion H11; subst.
                  inversion H14; subst.
                  inversion H13; subst.
                  eapply internal_preserves_request' with (pid:=pid) in Hvalid; simpl in *.
                  4 : { apply Hbinds5. }
                  3 : {
                    apply binds_push_eq.
                  }
                  discriminate.
                  eapply gather_pid_events_B_gather_pid_external_events.
                  eassumption.
              (* exclude query rear *)
              * apply valid_execution_fragment_com in Hvalid.
                simpl in Hvalid.
                eapply internal_preserves_notin''' with (pid:=pid) in Hvalid; simpl in *.
                apply binds_in in Hbinds4.
                unfold "#" in Hvalid.
                intuition.
                eapply gather_pid_events_B_gather_pid_external_events.
                eassumption.
                inversion H9; subst; simpl in *; intuition.
                inversion H10; subst; simpl in *; intuition.
                inversion H12; subst; simpl in *; intuition.
                inversion H11; subst; simpl in *; intuition.
          ++ unfold F, R;
            unfold get_front, get_rear, get_ary, get_pc;
            simpl.
            unfold F, R in Hmap;
            unfold get_front, get_rear, get_ary, get_pc in Hmap.
            simpl in Hmap.
            rewrite <-Hmap.
            
            f_equal.
            destruct H0 as [Hwf Hreach].
            apply inv_front_inc_at_d31_invariant in Hreach.
            apply Hreach in Hbinds5.
            simpl in Hbinds5.
            unfold array_queue_wf in Hwf.
            destruct Hwf as [Hok_wf _].
            simpl in Hok_wf.
            apply binds_reconstruct in Hbinds5.
            destruct Hbinds5 as [l1 [l2 Hlist]].
            rewrite Hlist in Hok_wf.
            apply ok_remove_middle_inv in Hok_wf.
            destruct Hok_wf as [Hokwf1 Hokwf2].
            destruct Hokwf2 as [Hokwf21 Hokwf22].
            rewrite Hlist.
            repeat rewrite get_r'_dist; auto.
            repeat rewrite get_f'_dist; auto.
            simpl.
            rewrite Nat.eqb_refl.
            apply notin_get_none in Hnotin_res.
            rewrite Hnotin_res.
            simpl.
            repeat rewrite get_f'_any_front_push; auto.
            rewrite plus_n_Sm.
            rewrite plus_n_Sm.
            reflexivity.

        (* front read, not a linearization point in the blocking queue *)
        + exists s2'.
          intuition.
          apply Step_None; auto.
          unfold f. simpl. intuition.
          ++ rewrite <-Hreq.
            apply H0 in Hbinds0.
            destruct Hbinds0 as [s1 [s2 [qb [acts [Hint_query [Hvalid Hgather]]]]]].
            inversion Hint_query; subst.
            simpl in qb.
            (* try to exclude other query *)
            destruct qb; simpl in *.
            (* exclude query of array *)
            +++ apply valid_execution_fragment_com in Hvalid.
                simpl in Hvalid.
                eapply internal_preserves_notin' with (pid:=pid) in Hvalid; simpl in *.
                apply binds_in in Hbinds1.
                unfold "#" in Hvalid.
                intuition.
                eapply gather_pid_events_B_gather_pid_external_events.
                eassumption.
                inversion H9; subst; simpl in *; intuition.
                inversion H10; subst; simpl in *; intuition.
            (* case of query front_rear *)
            +++ destruct q; simpl in *.
              (* case of query rear *)
              * destruct q.
                (* exclude rear inc *)
                ** apply valid_execution_fragment_com in Hvalid.
                  simpl in Hvalid.
                  inversion H9; subst.
                  inversion H10; subst.
                  inversion H12; subst.
                  inversion H11; subst.
                  inversion H14; subst.
                  inversion H13; subst.
                  eapply internal_preserves_request' with (pid:=pid) in Hvalid; simpl in *.
                  4 : { apply Hbinds5. }
                  3 : {
                    apply binds_push_eq.
                  }
                  discriminate.
                  eapply gather_pid_events_B_gather_pid_external_events.
                  eassumption.
                ** apply valid_execution_fragment_com' in Hvalid.
                  simpl in Hvalid.
                  destruct st2', st2.
                  eapply valid_execution_fragment_sync in Hvalid; eauto.
                  simpl.
                  inversion H8; subst.
                  inversion H10; subst; simpl.
                  *** eapply noB_preserves_AEnq14 with (pid:=pid) in Hvalid; eauto.
                    2 : {
                      destruct LState.
                      inversion H12; subst.
                      simpl.
                      eapply substitute_eq_binds_v'; eauto.
                    }
                    2 : {
                      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil).
                      rewrite Hgather. simpl. reflexivity.
                      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
                      assumption.
                    }
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                    apply binds_reconstruct in Hvalid.
                    destruct Hvalid as [l1 [l2 Hlist]].
                    rewrite Hlist in Hok_wf.
                    apply ok_remove_middle_inv in Hok_wf.
                    rewrite Hlist.
                    repeat rewrite gather_requests_dist.
                    simpl.
                    repeat rewrite gather_requests_res_front'; intuition.
                  *** eapply noB_preserves_ADeq2 with (pid:=pid) in Hvalid; eauto.
                    2 : {
                      destruct LState.
                      inversion H12; subst.
                      simpl.
                      eapply substitute_eq_binds_v'; eauto.
                    }
                    2 : {
                      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil).
                      rewrite Hgather. simpl. reflexivity.
                      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
                      assumption.
                    }
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                    apply binds_reconstruct in Hvalid.
                    destruct Hvalid as [l1 [l2 Hlist]].
                    rewrite Hlist in Hok_wf.
                    apply ok_remove_middle_inv in Hok_wf.
                    rewrite Hlist.
                    repeat rewrite gather_requests_dist.
                    simpl.
                    repeat rewrite gather_requests_res_front'; intuition.
                  *** eapply noB_preserves_ADeq11 with (pid:=pid) in Hvalid; eauto.
                    2 : {
                      destruct LState.
                      inversion H12; subst.
                      simpl.
                      eapply substitute_eq_binds_v'; eauto.
                    }
                    2 : {
                      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil).
                      rewrite Hgather. simpl. reflexivity.
                      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
                      assumption.
                    }
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                    apply binds_reconstruct in Hvalid.
                    destruct Hvalid as [l1 [l2 Hlist]].
                    rewrite Hlist in Hok_wf.
                    apply ok_remove_middle_inv in Hok_wf.
                    rewrite Hlist.
                    repeat rewrite gather_requests_dist.
                    simpl.
                    repeat rewrite gather_requests_res_front'; intuition.
              (* exclude query front *)
              * apply valid_execution_fragment_com in Hvalid.
                simpl in Hvalid.
                eapply internal_preserves_notin''' with (pid:=pid) in Hvalid; simpl in *.
                apply binds_in in Hbinds4.
                unfold "#" in Hvalid.
                intuition.
                eapply gather_pid_events_B_gather_pid_external_events.
                eassumption.
                inversion H9; subst; simpl in *; intuition.
                inversion H10; subst; simpl in *; intuition.
                inversion H12; subst; simpl in *; intuition.
                inversion H11; subst; simpl in *; intuition.
          ++ rewrite <-Hres.
            apply H0 in Hbinds0.
            destruct Hbinds0 as [s1 [s2 [qb [acts [Hint_query [Hvalid Hgather]]]]]].
            inversion Hint_query; subst.
            simpl in qb.
            (* try to exclude other query *)
            destruct qb; simpl in *.
            (* exclude query of array *)
            +++ apply valid_execution_fragment_com in Hvalid.
                simpl in Hvalid.
                eapply internal_preserves_notin' with (pid:=pid) in Hvalid; simpl in *.
                apply binds_in in Hbinds1.
                unfold "#" in Hvalid.
                intuition.
                eapply gather_pid_events_B_gather_pid_external_events.
                eassumption.
                inversion H9; subst; simpl in *; intuition.
                inversion H10; subst; simpl in *; intuition.
            (* case of query front_rear *)
            +++ destruct q; simpl in *.
              (* case of query rear *)
              * destruct q.
                (* exclude rear inc *)
                ** apply valid_execution_fragment_com in Hvalid.
                  simpl in Hvalid.
                  inversion H9; subst.
                  inversion H10; subst.
                  inversion H12; subst.
                  inversion H11; subst.
                  inversion H14; subst.
                  inversion H13; subst.
                  eapply internal_preserves_request' with (pid:=pid) in Hvalid; simpl in *.
                  4 : { apply Hbinds5. }
                  3 : {
                    apply binds_push_eq.
                  }
                  discriminate.
                  eapply gather_pid_events_B_gather_pid_external_events.
                  eassumption.
                ** apply valid_execution_fragment_com' in Hvalid.
                  simpl in Hvalid.
                  destruct st2', st2.
                  eapply valid_execution_fragment_sync in Hvalid; eauto.
                  simpl.
                  inversion H8; subst.
                  inversion H10; subst; simpl.
                  *** eapply noB_preserves_AEnq14 with (pid:=pid) in Hvalid; eauto.
                    2 : {
                      destruct LState.
                      inversion H12; subst.
                      simpl.
                      eapply substitute_eq_binds_v'; eauto.
                    }
                    2 : {
                      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil).
                      rewrite Hgather. simpl. reflexivity.
                      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
                      assumption.
                    }
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                    apply binds_reconstruct in Hvalid.
                    destruct Hvalid as [l1 [l2 Hlist]].
                    rewrite Hlist in Hok_wf.
                    apply ok_remove_middle_inv in Hok_wf.
                    rewrite Hlist.
                    repeat rewrite gather_responses_dist.
                    simpl.
                    repeat rewrite gather_responses_res_front'; intuition.
                  *** eapply noB_preserves_ADeq2 with (pid:=pid) in Hvalid; eauto.
                    2 : {
                      destruct LState.
                      inversion H12; subst.
                      simpl.
                      eapply substitute_eq_binds_v'; eauto.
                    }
                    2 : {
                      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil).
                      rewrite Hgather. simpl. reflexivity.
                      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
                      assumption.
                    }
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                    apply binds_reconstruct in Hvalid.
                    destruct Hvalid as [l1 [l2 Hlist]].
                    rewrite Hlist in Hok_wf.
                    apply ok_remove_middle_inv in Hok_wf.
                    rewrite Hlist.
                    repeat rewrite gather_responses_dist.
                    simpl.
                    repeat rewrite gather_responses_res_front'; intuition.
                  *** eapply noB_preserves_ADeq11 with (pid:=pid) in Hvalid; eauto.
                    2 : {
                      destruct LState.
                      inversion H12; subst.
                      simpl.
                      eapply substitute_eq_binds_v'; eauto.
                    }
                    2 : {
                      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil).
                      rewrite Hgather. simpl. reflexivity.
                      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
                      assumption.
                    }
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                    apply binds_reconstruct in Hvalid.
                    destruct Hvalid as [l1 [l2 Hlist]].
                    rewrite Hlist in Hok_wf.
                    apply ok_remove_middle_inv in Hok_wf.
                    rewrite Hlist.
                    repeat rewrite gather_responses_dist.
                    simpl.
                    repeat rewrite gather_responses_res_front'; intuition.
              (* exclude query front *)
              * apply valid_execution_fragment_com in Hvalid.
                simpl in Hvalid.
                eapply internal_preserves_notin''' with (pid:=pid) in Hvalid; simpl in *.
                apply binds_in in Hbinds4.
                unfold "#" in Hvalid.
                intuition.
                eapply gather_pid_events_B_gather_pid_external_events.
                eassumption.
                inversion H9; subst; simpl in *; intuition.
                inversion H10; subst; simpl in *; intuition.
                inversion H12; subst; simpl in *; intuition.
                inversion H11; subst; simpl in *; intuition.
          ++ unfold F, R;
            unfold get_front, get_rear, get_ary, get_pc;
            simpl.
            unfold F, R in Hmap;
            unfold get_front, get_rear, get_ary, get_pc in Hmap.
            simpl in Hmap.
            rewrite <-Hmap.
            f_equal.
            repeat rewrite get_f'_any_rear_read; auto.
    (* array step *)
    -- inversion H4; subst; simpl in *.
      inversion H5; subst.
      (* array cas *)
      ---
            apply H0 in Hbinds0.
            destruct Hbinds0 as [s1 [s2 [qb [acts [Hint_query [Hvalid Hgather]]]]]].
            inversion Hint_query; subst.
            simpl in qb.
            (* try to exclude other query *)
            destruct qb; simpl in *.
            (* case of query array *)
            +++ destruct q; simpl in *.
              (* case of cas *)
              * assert (Hparam: i = i0 /\ old = old0 /\ new = new0).
                ** apply valid_execution_fragment_com in Hvalid.
                  simpl in Hvalid.
                  inversion H7; subst.
                  inversion H8; subst.
                  inversion H10; subst.
                  inversion H9; subst.
                  eapply internal_preserves_request'' with (pid:=pid) in Hvalid; simpl in *.
                  4 : { apply Hbinds3. }
                  3 : {
                    apply binds_push_eq.
                  }
                  inversion Hvalid; subst.
                  intuition.
                  eapply gather_pid_events_B_gather_pid_external_events.
                  eassumption.
                ** intuition. subst.
                apply valid_execution_fragment_com' in Hvalid.
                  simpl in Hvalid.
                  destruct st2', st2.
                  eapply valid_execution_fragment_sync in Hvalid; eauto.
                  simpl.
                  inversion H6; subst.
                  inversion H10; subst.
                  clear H10.
                  inversion H8; subst; simpl in *.
                  (* enq *)
                  *** pose proof Hvalid as HvalidTmp.
                    eapply noB_preserves_AEnq28 with (pid:=pid) in Hvalid; eauto.
                    2 : {
                      destruct LState.
                      simpl.
                      eapply substitute_eq_binds_v'; eauto.
                    }
                    2 : {
                      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil).
                      rewrite Hgather. simpl. reflexivity.
                      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
                      assumption.
                    }
                    destruct (entry_eqb
                                 (Vector.nth vec (Fin.of_nat_lt Hlt))
                                 (x pid))eqn:Heq.
                    (* cas succeed, linearize *)
                    {
                      unfold array_queue_wf' in H0.
                      simpl in H0.
                      destruct H0 as [Hwf Hreach].
                      eapply noB_preserves_AEnq28_combine in HvalidTmp.
                      2 : {
                        simpl.
                        eapply substitute_eq_binds_v'; eauto.
                      }
                      2 : {
                        assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil).
                        rewrite Hgather. simpl. reflexivity.
                        rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
                        assumption.
                      }
                      simpl in HvalidTmp.
                      destruct HvalidTmp as [Hvalid1 [Hvalid2 Hvalid3]].
                      pose proof Hreach as HreachTmp.
                      pose proof Hreach as HreachTmp2.
                      apply inv_e28_x_none_invariant in HreachTmp.
                      simpl in HreachTmp.
                      pose proof Hvalid as HvalidTmp.
                      apply HreachTmp in HvalidTmp.
                      simpl in HvalidTmp.
                      apply entry_eqb_eq in Heq.
                      destruct ((Vector.nth vec (Fin.of_nat_lt Hlt)))eqn:Heq'.
                      rewrite <-Hvalid1 in HvalidTmp.
                      rewrite <-Heq in HvalidTmp.
                      simpl in HvalidTmp.
                      subst.

                      eapply invariant_step in HreachTmp2.
                      2 : {
                        eassumption.
                      }
                      apply inv_5_invariant in HreachTmp2; auto.
                      unfold inv_5 in HreachTmp2.
                      simpl in HreachTmp2.

                      destruct s2'. simpl in *.
                        destruct LState0. simpl in *.
                        destruct q.
                        (* by contradiction *)
                        -- exfalso.
                          simpl in HreachTmp2.
                          specialize (HreachTmp2 pid).
                          generalize array_to_queue_not_empty; intro.
                          eapply H0.
                          2 : {
                            eassumption.
                          }
                          apply HreachTmp2.
                          unfold enq_not_inc.
                          left. intuition.
                          simpl.
                          apply binds_push_eq.
                        --
                        exists ( mkQState
                          (gather_requests pc0 vp0
                            front0 rear0 res
                            st0.(LState).(Tensor.L1State).(LState).(Counter.responses)
                            st0.(LState).(Tensor.L2State).(LState).(Counter.responses)
                            )
                          (remove responses pid)
                          q
                        ).
                        simpl. intuition.
                        --- 

                          unfold array_queue_wf in Hwf.
                          simpl in Hwf.
                          destruct Hwf as [Hok_wf _].
                          simpl in Hok_wf.

                        eapply Step_Internal with (pid:=pid) (int:=int_q_enq); eauto.
                          2 : {
                            eapply Step_None; eauto.
                          }
                          eapply queue_step_enq with (v:=vp0 pid) (q':=Some (vp0 pid) :: q) (res':=responses).
                          5 : {
                            reflexivity.
                          }
                          7 : {
                            pose proof Hvalid as HvalidTmp.
                            f_equal.
                            rewrite <-Hreq.
                            apply binds_reconstruct in Hvalid.
                            destruct Hvalid as [l1 [l2 Hlist]].
                            rewrite Hlist in Hok_wf.
                            apply ok_remove_middle_inv in Hok_wf.
                            rewrite Hlist.
                            repeat rewrite gather_requests_dist.
                            simpl.
                            rewrite Nat.eqb_refl.
                            apply notin_get_none in Hnotin_res.
                            rewrite Hnotin_res.
                            rewrite remove_notin_app.
                            simpl.
                            rewrite Nat.eqb_refl.
                            rewrite gather_requests_res_ary'; intuition.
                            rewrite gather_requests_res_ary'; intuition.
                            apply gather_requests_preserves_notin; intuition.
                            specialize (HreachTmp2 pid).
                            f_equal.

                            assert (HTT : 
                            enq_not_inc L pid pc0
                            (mkAryState L (remove inv pid)
                              ((pid, AryCASOk true) :: res)
                              (Vector.replace vec (Fin.of_nat_lt Hlt)
                     (Some (vp pid), snd (x pid) + 1)))
                     (LState (Tensor.L2State (LState st0)))).
                            unfold enq_not_inc.
                            left. intuition.
                            simpl.
                            apply binds_push_eq.
                            intuition.
                            generalize lt_neq_0; intro Hltneq.
                            pose proof H0 as HFR.
                            apply Hltneq in H0.
                            apply neq_0_exist in H0.
                            destruct H0 as [r' Hr'].
                            rewrite Hr' in Hmap.
                            rewrite array_to_queue_S_r in Hmap; auto.
                            assert (Hmap' : fst
         (Vector.nth
            (Vector.replace vec (Fin.of_nat_lt Hlt)
               (Some (vp pid), snd (x pid) + 1))
            (Fin.of_nat_lt (mod_lt H r'))) = o).
                            inversion Hmap; subst; intuition.
                            clear Hmap.
                            rename Hmap' into Hmap.
                            (* apply array_to_queue_reconstruct' in Hmap. *)
                            pose proof Hreach as HreachTmp3.
                            generalize inv_e28_clean_invariant; intro He28.
                            specialize (He28 L H).
                            apply He28 in HreachTmp3.
                            apply HreachTmp3 in Hvalid.
                            simpl in Hvalid.
                            intuition.
                            rewrite <-Hvalid1 in Hvalid.
                            rewrite <-Hvalid2 in Hvalid.

                    assert (Htmp : (Fin.of_nat_lt Hlt) =
                      (Fin.of_nat_lt (mod_lt H (rear pid)))).
                    apply Fin.of_nat_ext.
                            rewrite <-Htmp in Hvalid.
                            
                            rewrite Heq' in Hvalid.
                            rewrite Heq in Hvalid.
                            specialize (Hvalid eq_refl).
                            destruct Hvalid as [Hv1 Hv2].

                            unfold F, R in Hr';
                            unfold get_rear, get_front, get_ary, get_pc in Hr';
                            simpl in Hr'.

                          apply binds_reconstruct in HvalidTmp.
                          destruct HvalidTmp as [l1 [l2 Hlist]].
                          rewrite Hlist in Hok_wf.
                          apply ok_remove_middle_inv in Hok_wf.
                          rewrite Hlist in Hr'.
                          rewrite Hlist in Hv1.
                          unfold F, R in Hr';
                          unfold get_front, get_rear, get_ary, get_pc in Hr';
                          simpl in Hr'.
                          unfold F, R in Hv1;
                          unfold get_front, get_rear, get_ary, get_pc in Hv1;
                          simpl in Hv1.
                          repeat rewrite get_f'_dist in Hr'.
                          repeat rewrite get_r'_dist in Hr'.
                          repeat rewrite get_f'_dist in Hv1.
                          repeat rewrite get_r'_dist in Hv1.
                          simpl in Hr'.
                          rewrite Nat.eqb_refl in Hr'.
                          simpl in Hr'.
                          rewrite <-plus_n_Sm in Hr'.
                          rewrite <-plus_n_Sm in Hr'.
                          simpl in Hr'.
                          apply notin_get_none in Hnotin_res.
                          simpl in Hv1.
                          rewrite Hnotin_res in Hv1.
                          rewrite get_r'_any_ary in Hr'; intuition.
                          rewrite get_r'_any_ary in Hr'; intuition.
                          simpl in Hr'.
                          rewrite <-Hv1 in Hr'.
                          inversion Hr'; subst.
                          rewrite Htmp.
                          rewrite Vector.nth_replace_eq.
                          simpl.
                          rewrite Hvalid3.
                          reflexivity.
                          apply inv_6_invariant in Hreach; auto.
                          unfold inv_6 in Hreach.
                          simpl in Hreach.

                          apply binds_reconstruct in HvalidTmp.
                          destruct HvalidTmp as [l1 [l2 Hlist]].
                          rewrite Hlist in Hok_wf.
                          apply ok_remove_middle_inv in Hok_wf.
                          destruct Hok_wf as [Hokl [Hnt1 Hnt2]].
                          rewrite Hlist in Hreach.
                          unfold F, R in *;
                          unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
                          repeat rewrite get_f'_dist in Hreach.
                          repeat rewrite get_r'_dist in Hreach.
                          simpl in Hreach.
                          apply notin_get_none in Hnotin_res.
                          rewrite Hnotin_res in Hreach.
                          simpl in Hreach.
                          rewrite Hlist.
                          repeat rewrite get_f'_dist.
                          repeat rewrite get_r'_dist.
                          simpl.
                          rewrite get_f'_any_ary; auto.
                          rewrite get_f'_any_ary; auto.

                          rewrite Hlist in Hr'.
                          repeat rewrite get_f'_dist in Hr'.
                          repeat rewrite get_r'_dist in Hr'.
                          simpl in Hr'.
                          rewrite Nat.eqb_refl in Hr'.
                          repeat rewrite Nat.add_succ_r in Hr'.
                          inversion Hr'; subst; simpl in *.
                          rewrite get_r'_any_ary; auto.
                          rewrite get_r'_any_ary; auto.
                          intuition.
                          }
                          apply gather_requests_preserves_ok; auto.
                          apply remove_preserves_ok; auto.
                          rewrite <-Hres.
                          apply gather_responses_preserves_ok; auto.
                          apply binds_reconstruct in Hvalid.
                          destruct Hvalid as [l1 [l2 Hlist]].
                          rewrite Hlist in Hok_wf.
                          apply ok_remove_middle_inv in Hok_wf.
                          rewrite Hlist.
                          repeat rewrite gather_requests_dist.
                          simpl.
                          apply notin_get_none in Hnotin_res.
                          rewrite Hnotin_res.
                          apply binds_concat_left.
                          apply binds_push_eq.
                          apply gather_requests_preserves_notin; auto.
                          intuition.
                          apply ok_remove_notin; auto.
                          rewrite <-Hres.
                          apply gather_responses_preserves_ok; auto.
                          unfold enqueue.
                          assert (HTT : length (o :: q) <= L).
                          apply length_equality in Hmap; auto.
                          rewrite <-Hmap.
                          rewrite array_to_queue_length.
                          pose proof Hreach as HreachTmp3.

                          eapply invariant_step in HreachTmp3.
                          2 : {
                            eassumption.
                          }
                          apply inv_6_invariant in HreachTmp3; auto.
                          unfold inv_6 in HreachTmp3.
                          simpl in HreachTmp3.
                          lia.
                          simpl in HTT.
                          apply leb_correct in HTT.
                          unfold "<?".
                          rewrite HTT.
                          reflexivity.
                          rewrite <-Hres.
                          apply binds_reconstruct in Hvalid.
                          destruct Hvalid as [l1 [l2 Hlist]].
                          rewrite Hlist in Hok_wf.
                          apply ok_remove_middle_inv in Hok_wf.
                          rewrite Hlist.
                          repeat rewrite gather_responses_dist.
                          simpl.
                          rewrite Nat.eqb_refl.
                          rewrite remove_notin_app.
                          simpl.
                          rewrite Nat.eqb_refl.
                          2 : {
                            apply gather_responses_preserves_notin; auto.
                            intuition.
                          }
                          apply sameset_ExF_xEF; auto.
                          apply ok_ExF_xEF; auto.
                          rewrite <-gather_responses_dist.
                          econstructor; eauto.
                          apply gather_responses_preserves_ok; auto.
                          intuition.
                          apply gather_responses_preserves_notin; auto.
                          apply notin_concat; intuition.
                        --- unfold f. simpl. intuition.
                          (* here needs sameset *)
                          rewrite <-Hres.
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                          apply binds_reconstruct in Hvalid.
                          destruct Hvalid as [l1 [l2 Hlist]].
                          rewrite Hlist in Hok_wf.
                          apply ok_remove_middle_inv in Hok_wf.
                          rewrite Hlist.
                          repeat rewrite gather_responses_dist.
                          simpl.
                          rewrite Nat.eqb_refl.
                          apply notin_get_none in Hnotin_res.
                          rewrite Hnotin_res.
                          rewrite remove_notin_app.
                          simpl.
                          rewrite Nat.eqb_refl.
                          2 : {
                            apply gather_responses_preserves_notin; auto.
                            intuition.
                          }
                          rewrite gather_responses_res_ary'; intuition.
                          rewrite gather_responses_res_ary'; intuition.
                          simpl in Hmap.
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                          pose proof Hvalid as HvalidTmp.
                          apply binds_reconstruct in Hvalid.
                          destruct Hvalid as [l1 [l2 Hlist]].
                          rewrite Hlist in Hok_wf.
                          apply ok_remove_middle_inv in Hok_wf.
                          rewrite Hlist in Hmap.
                          rewrite Hlist.
                          unfold F, R;
                          unfold get_front, get_rear, get_ary, get_pc;
                          simpl.
                          unfold F, R in Hmap;
                          unfold get_front, get_rear, get_ary, get_pc in Hmap;
                          simpl in Hmap.
                          repeat rewrite get_f'_dist in Hmap.
                          repeat rewrite get_r'_dist in Hmap.
                          repeat rewrite get_f'_dist.
                          repeat rewrite get_r'_dist.
                          simpl in Hmap.
                          rewrite Nat.eqb_refl in Hmap.
                          simpl in Hmap.
                          rewrite <-plus_n_Sm in Hmap.
                          rewrite <-plus_n_Sm in Hmap.
                          simpl in Hmap.
                          rewrite get_f'_any_ary in Hmap; intuition.
                          rewrite get_f'_any_ary in Hmap; intuition.
                          rewrite get_r'_any_ary in Hmap; intuition.
                          rewrite get_r'_any_ary in Hmap; intuition.
                          simpl.
                          apply notin_get_none in Hnotin_res.
                          rewrite Hnotin_res.
                          simpl.
                          rewrite array_to_queue_S_r in Hmap; auto; try lia.
                          simpl in Hmap.
                          inversion Hmap.

                            pose proof Hreach as HreachTmp3.
                            generalize inv_e28_clean_invariant; intro He28.
                            specialize (He28 L H).
                            apply He28 in HreachTmp3.
                            pose proof HvalidTmp as HvalidTmp'.
                            apply HreachTmp3 in HvalidTmp.
                            simpl in HvalidTmp.
                            intuition.
                            rewrite <-Hvalid1 in HvalidTmp.
                            rewrite <-Hvalid2 in HvalidTmp.
                            intuition.

                    assert (Htmp : (Fin.of_nat_lt Hlt) =
                      (Fin.of_nat_lt (mod_lt H (rear pid)))).
                    apply Fin.of_nat_ext.
                            rewrite <-Htmp in HvalidTmp.
                            
                            rewrite Heq' in HvalidTmp.
                            rewrite Heq in HvalidTmp.
                            specialize (HvalidTmp eq_refl).
                            destruct HvalidTmp as [Hv1 Hv2].

                          rewrite Hlist in Hv1.
                          unfold F, R in Hv1;
                          unfold get_front, get_rear, get_ary, get_pc in Hv1;
                          simpl in Hv1.
                          repeat rewrite get_f'_dist in Hv1.
                          repeat rewrite get_r'_dist in Hv1.
                          simpl in Hv1.
                          rewrite Hnotin_res in Hv1.
                          rewrite <-Hv1.
                          rewrite Htmp.
                          apply array_to_queue_replace_r.
                          (* apply array_to_queue_replace_last_eq. *)
                          3 : {
                          apply inv_6_invariant in Hreach; auto.
                          unfold inv_6 in Hreach.
                          unfold F, R in *;
                          unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
                          rewrite Hlist in Hreach.
                          repeat rewrite get_f'_dist in Hreach.
                          repeat rewrite get_r'_dist in Hreach.
                          simpl in Hreach.
                          rewrite Hnotin_res in Hreach.
                          intuition.
                          }
                          rewrite Hv1.
                          apply inv_6_invariant in Hreach; auto.
                          unfold inv_6 in Hreach.
                          unfold F, R in *;
                          unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
                          rewrite Hlist in Hreach.
                          repeat rewrite get_f'_dist in Hreach.
                          repeat rewrite get_r'_dist in Hreach.
                          simpl in Hreach.
                          rewrite Hnotin_res in Hreach.
                          intuition.
                          rewrite Hv1.
                          apply inv_e28_clean_invariant with (H:=H) in Hreach; auto.
                          unfold inv_e28_clean in Hreach.
                          unfold F, R in *;
                          unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
                          rewrite Hlist in Hreach.
                          repeat rewrite get_f'_dist in Hreach.
                          repeat rewrite get_r'_dist in Hreach.
                          simpl in Hreach.
                          rewrite Hnotin_res in Hreach.
                          simpl in Hlist; rewrite <-Hlist in Hreach.
                          apply Hreach in HvalidTmp'; auto.
                          intuition.
                          rewrite <-Hvalid2.
                          rewrite <-Htmp.
                          rewrite <-Hvalid1.
                          rewrite <-Heq.
                          rewrite Heq'.
                          reflexivity.
                    }
                    (* CAS fail *)
                    {
                      exists s2'.
                      intuition.
                      eapply Step_None; eauto.
                      unfold f. simpl. intuition.
                      - rewrite <-Hreq.
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                          apply binds_reconstruct in Hvalid.
                          destruct Hvalid as [l1 [l2 Hlist]].
                          rewrite Hlist in Hok_wf.
                          apply ok_remove_middle_inv in Hok_wf.
                          rewrite Hlist.
                          repeat rewrite gather_requests_dist.
                          simpl.
                          apply notin_get_none in Hnotin_res.
                          rewrite Hnotin_res.
                          rewrite Nat.eqb_refl.
                          repeat rewrite gather_requests_res_ary'; intuition.
                      - rewrite <-Hres.
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                          apply binds_reconstruct in Hvalid.
                          destruct Hvalid as [l1 [l2 Hlist]].
                          rewrite Hlist in Hok_wf.
                          apply ok_remove_middle_inv in Hok_wf.
                          rewrite Hlist.
                          repeat rewrite gather_responses_dist.
                          simpl.
                          apply notin_get_none in Hnotin_res.
                          rewrite Hnotin_res.
                          rewrite Nat.eqb_refl.
                          repeat rewrite gather_responses_res_ary'; intuition.
                      - 
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                          apply binds_reconstruct in Hvalid.
                          destruct Hvalid as [l1 [l2 Hlist]].
                          rewrite Hlist in Hok_wf.
                          apply ok_remove_middle_inv in Hok_wf.
                          unfold F, R;
                          unfold get_front, get_rear, get_ary, get_pc;
                          simpl.
                          unfold F, R in Hmap;
                          unfold get_front, get_rear, get_ary, get_pc in Hmap;
                          simpl in Hmap.
                          rewrite Hlist in Hmap.
                          rewrite Hlist.
                          repeat rewrite get_f'_dist in Hmap.
                          repeat rewrite get_r'_dist in Hmap.
                          repeat rewrite get_f'_dist.
                          repeat rewrite get_r'_dist.
                          simpl in Hmap.
                          rewrite Nat.eqb_refl in Hmap.
                          simpl in Hmap.
                          rewrite get_f'_any_ary in Hmap; intuition.
                          rewrite get_f'_any_ary in Hmap; intuition.
                          rewrite get_r'_any_ary in Hmap; intuition.
                          rewrite get_r'_any_ary in Hmap; intuition.
                          simpl.
                          apply notin_get_none in Hnotin_res.
                          rewrite Hnotin_res.
                          simpl. auto.
                    }
                  (* deq *)
                  *** 
                  pose proof Hvalid as HvalidTmp.
                  eapply noB_preserves_ADeq28 with (pid:=pid) in Hvalid; eauto.
                    2 : {
                      destruct LState.
                      simpl.
                      eapply substitute_eq_binds_v'; eauto.
                    }
                    2 : {
                      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil).
                      rewrite Hgather. simpl. reflexivity.
                      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
                      assumption.
                    }
                    destruct ((entry_eqb
                                 (Vector.nth vec (Fin.of_nat_lt Hlt))
                                 (x pid)))eqn:Heq.
                    (* cas succeed, linearize *)
                    {
                      unfold array_queue_wf' in H0.
                      simpl in H0.
                      destruct H0 as [Hwf Hreach].
                      eapply noB_preserves_ADeq28_combine in HvalidTmp.
                      2 : {
                        simpl.
                        eapply substitute_eq_binds_v'; eauto.
                      }
                      2 : {
                        assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil).
                        rewrite Hgather. simpl. reflexivity.
                        rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
                        assumption.
                      }
                      simpl in HvalidTmp.
                      destruct HvalidTmp as [Hvalid1 Hvalid2].
                      pose proof Hreach as HreachTmp.
                      pose proof Hreach as HreachTmp2.

                      eapply invariant_step in HreachTmp.
                      2 : {
                        eassumption.
                      }

                      apply inv_d28_x_none_invariant in HreachTmp.
                      simpl in HreachTmp.
                      pose proof Hvalid as HvalidTmp.
                      apply HreachTmp in HvalidTmp.
                      simpl in HvalidTmp.
                      apply not_none_exist in HvalidTmp.
                      destruct HvalidTmp as [v Hv].

                      subst.

                      eapply invariant_step in HreachTmp2.
                      2 : {
                        eassumption.
                      }
                      apply inv_5_invariant in HreachTmp2; auto.
                      unfold inv_5 in HreachTmp2.
                      simpl in HreachTmp2.

                      destruct s2'. simpl in *.
                        destruct LState0. simpl in *.
                        exists ( mkQState
                          (gather_requests pc0 vp0
                            front0 rear0 res
                            st0.(LState).(Tensor.L1State).(LState).(Counter.responses)
                            st0.(LState).(Tensor.L2State).(LState).(Counter.responses)
                            )
                          (remove responses pid)
                          (q ++ [fst (x0 pid)])
                        ).
                        simpl. intuition.
                        --- 

                          unfold array_queue_wf in Hwf.
                          simpl in Hwf.
                          destruct Hwf as [Hok_wf _].
                          simpl in Hok_wf.

                        eapply Step_Internal with (pid:=pid) (int:=int_q_deq); eauto.
                          2 : {
                            eapply Step_None; eauto.
                          }
                          eapply queue_step_deq with (v:=v) (res':=responses).
                          5 : {
                            reflexivity.
                          }
                          7 : {
                            f_equal.
                            rewrite <-Hreq.
                            apply binds_reconstruct in Hvalid.
                            destruct Hvalid as [l1 [l2 Hlist]].
                            rewrite Hlist in Hok_wf.
                            apply ok_remove_middle_inv in Hok_wf.
                            rewrite Hlist.
                            repeat rewrite gather_requests_dist.
                            simpl.
                            rewrite Nat.eqb_refl.
                            apply notin_get_none in Hnotin_res.
                            rewrite Hnotin_res.
                            rewrite remove_notin_app.
                            simpl.
                            rewrite Nat.eqb_refl.
                            rewrite gather_requests_res_ary'; intuition.
                            rewrite gather_requests_res_ary'; intuition.
                            apply gather_requests_preserves_notin; intuition.
                          }
                          apply gather_requests_preserves_ok; auto.
                          apply remove_preserves_ok; auto.
                          rewrite <-Hres.
                          apply gather_responses_preserves_ok; auto.
                          apply binds_reconstruct in Hvalid.
                          destruct Hvalid as [l1 [l2 Hlist]].
                          rewrite Hlist in Hok_wf.
                          apply ok_remove_middle_inv in Hok_wf.
                          rewrite Hlist.
                          repeat rewrite gather_requests_dist.
                          simpl.
                          apply notin_get_none in Hnotin_res.
                          rewrite Hnotin_res.
                          apply binds_concat_left.
                          apply binds_push_eq.
                          apply gather_requests_preserves_notin; auto.
                          intuition.
                          apply ok_remove_notin; auto.
                          rewrite <-Hres.
                          apply gather_responses_preserves_ok; auto.
                          rewrite Hv.
                          simpl.
                          apply dequeue_some.
                          rewrite <-Hres.
                          apply binds_reconstruct in Hvalid.
                          destruct Hvalid as [l1 [l2 Hlist]].
                          rewrite Hlist in Hok_wf.
                          apply ok_remove_middle_inv in Hok_wf.
                          rewrite Hlist.
                          repeat rewrite gather_responses_dist.
                          simpl.
                          rewrite Nat.eqb_refl.
                          rewrite remove_notin_app.
                          rewrite Hv.
                          simpl.
                          rewrite Nat.eqb_refl.
                          2 : {
                            apply gather_responses_preserves_notin; auto.
                            intuition.
                          }
                          apply sameset_ExF_xEF; auto.
                          apply ok_ExF_xEF; auto.
                          rewrite <-gather_responses_dist.
                          econstructor; eauto.
                          apply gather_responses_preserves_ok; auto.
                          intuition.
                          apply gather_responses_preserves_notin; auto.
                          apply notin_concat; intuition.
                        --- unfold f. simpl.
                          pose proof Hvalid as HvalidTmp.
                        intuition.
                          (* here needs sameset *)
                          rewrite <-Hres.
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                          apply binds_reconstruct in Hvalid.
                          destruct Hvalid as [l1 [l2 Hlist]].
                          rewrite Hlist in Hok_wf.
                          apply ok_remove_middle_inv in Hok_wf.
                          pose proof Hok_wf as Hok_wf'.
                          destruct Hok_wf as [Hokl [Hnt1 Hnt2]].
                          apply ok_concat_inv in Hokl.
                          destruct Hokl as [Hokl1 Hokl2].
                          rewrite Hlist.
                          repeat rewrite gather_responses_dist.
                          simpl.
                          rewrite Nat.eqb_refl.
                          apply notin_get_none in Hnotin_res.
                          rewrite Hnotin_res.
                          rewrite remove_notin_app.
                          rewrite Hv.
                          simpl.
                          rewrite Nat.eqb_refl.
                          2 : {
                            apply gather_responses_preserves_notin; auto.
                          }
                          rewrite gather_responses_res_ary'; intuition.
                          rewrite gather_responses_res_ary'; intuition.
                          simpl in Hmap.
                          pose proof HvalidTmp as HvalidTmp'.
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                          apply binds_reconstruct in Hvalid.
                          destruct Hvalid as [l1 [l2 Hlist]].
                          rewrite Hlist in Hok_wf.
                          apply ok_remove_middle_inv in Hok_wf.
                          rewrite Hlist in Hmap.
                          rewrite Hlist.
                          unfold F, R;
                          unfold get_front, get_rear, get_ary, get_pc;
                          simpl.
                          unfold F, R in Hmap;
                          unfold get_front, get_rear, get_ary, get_pc in Hmap;
                          simpl in Hmap.
                          repeat rewrite get_f'_dist in Hmap.
                          repeat rewrite get_r'_dist in Hmap.
                          repeat rewrite get_f'_dist.
                          repeat rewrite get_r'_dist.
                          simpl in Hmap.
                          rewrite Nat.eqb_refl in Hmap.
                          simpl in Hmap.
                          rewrite <-plus_n_Sm in Hmap.
                          rewrite <-plus_n_Sm in Hmap.
                          simpl in Hmap.
                          rewrite get_f'_any_ary in Hmap; intuition.
                          rewrite get_f'_any_ary in Hmap; intuition.
                          rewrite get_r'_any_ary in Hmap; intuition.
                          rewrite get_r'_any_ary in Hmap; intuition.
                          simpl.
                          apply notin_get_none in Hnotin_res.
                          rewrite Hnotin_res.
                          simpl.
                          rewrite <-Hmap.
                          apply entry_eqb_eq in Heq.
                          rewrite Hvalid1 in Heq.
                          rewrite <-Heq.

                            pose proof Hreach as HreachTmp3.
                            generalize inv_d28_clean_invariant; intro He28.
                            specialize (He28 L H).
                            apply He28 in HreachTmp3.
                            pose proof HvalidTmp as Hvalid.
                            apply HreachTmp3 in HvalidTmp.
                            simpl in HvalidTmp.
                            intuition.
                            rewrite <-Hvalid1 in HvalidTmp.
                            rewrite <-Hvalid2 in HvalidTmp.

                    assert (Htmp : (Fin.of_nat_lt Hlt) =
                      (Fin.of_nat_lt (mod_lt H (front pid)))).
                    apply Fin.of_nat_ext.
                            rewrite <-Htmp in HvalidTmp.
                            
                            rewrite Hvalid1 in HvalidTmp.
                            rewrite Heq in HvalidTmp.
                            specialize (HvalidTmp eq_refl).
                            destruct HvalidTmp as [Hv1 Hv2].

                          rewrite Hlist in Hv1.
                          unfold F, R in Hv1;
                          unfold get_front, get_rear, get_ary, get_pc in Hv1;
                          simpl in Hv1.
                          repeat rewrite get_f'_dist in Hv1.
                          repeat rewrite get_r'_dist in Hv1.
                          simpl in Hv1.
                          rewrite Hnotin_res in Hv1.
                          rewrite <-Hv1.
                          rewrite Htmp.
                          rewrite array_to_queue_S_f; auto.
                          f_equal.
                          erewrite array_to_queue_replace_f; eauto.
                          (* apply array_to_queue_replace_first_eq. *)
                          rewrite Hv1.
                          apply inv_6_invariant in Hreach; auto.
                          unfold inv_6 in Hreach.
                          destruct Hreach as [_ [HRF _]].
                          unfold F, R in HRF;
                          unfold get_front, get_rear, get_ary, get_pc in HRF;
                          simpl in HRF.
                          rewrite Hlist in HRF.
                          repeat rewrite get_f'_dist in HRF.
                          repeat rewrite get_r'_dist in HRF.
                          simpl in HRF.
                          rewrite Hnotin_res in HRF.
                          simpl in HRF.
                          assumption.

                          rewrite Hv1.
                          apply inv_6_invariant in Hreach; auto.
                          unfold inv_6 in Hreach.
                          destruct Hreach as [_ [_ HRF]].
                          unfold F, R in HRF;
                          unfold get_front, get_rear, get_ary, get_pc in HRF;
                          simpl in HRF.
                          rewrite Hlist in HRF.
                          repeat rewrite get_f'_dist in HRF.
                          repeat rewrite get_r'_dist in HRF.
                          simpl in HRF.
                          rewrite Hnotin_res in HRF.
                          simpl in HRF.
                          assumption.
                          rewrite Hv1.

                          apply He28 in Hreach.

                          unfold inv_d28_clean in Hreach.
                          simpl in Hreach.
                          apply Hreach in HvalidTmp'.
                          rename HvalidTmp' into HRF.
                          unfold F, R in HRF;
                          unfold get_front, get_rear, get_ary, get_pc in HRF;
                          simpl in HRF.
                          rewrite Hlist in HRF.
                          repeat rewrite get_f'_dist in HRF.
                          repeat rewrite get_r'_dist in HRF.
                          simpl in HRF.
                          rewrite Hnotin_res in HRF.
                          simpl in HRF.
                          intuition.
                          rewrite <-Hvalid2.
                          rewrite <-Htmp.
                          intuition.
                          }
                    (* CAS fail *)
                    {
                      exists s2'.
                      intuition.
                      eapply Step_None; eauto.
                      unfold f. simpl. intuition.
                      - rewrite <-Hreq.
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                          apply binds_reconstruct in Hvalid.
                          destruct Hvalid as [l1 [l2 Hlist]].
                          rewrite Hlist in Hok_wf.
                          apply ok_remove_middle_inv in Hok_wf.
                          rewrite Hlist.
                          repeat rewrite gather_requests_dist.
                          simpl.
                          apply notin_get_none in Hnotin_res.
                          rewrite Hnotin_res.
                          rewrite Nat.eqb_refl.
                          repeat rewrite gather_requests_res_ary'; intuition.
                      - rewrite <-Hres.
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                          apply binds_reconstruct in Hvalid.
                          destruct Hvalid as [l1 [l2 Hlist]].
                          rewrite Hlist in Hok_wf.
                          apply ok_remove_middle_inv in Hok_wf.
                          rewrite Hlist.
                          repeat rewrite gather_responses_dist.
                          simpl.
                          apply notin_get_none in Hnotin_res.
                          rewrite Hnotin_res.
                          rewrite Nat.eqb_refl.
                          repeat rewrite gather_responses_res_ary'; intuition.
                      -
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                          apply binds_reconstruct in Hvalid.
                          destruct Hvalid as [l1 [l2 Hlist]].
                          rewrite Hlist in Hok_wf.
                          apply ok_remove_middle_inv in Hok_wf.
                          unfold F, R;
                          unfold get_front, get_rear, get_ary, get_pc;
                          simpl.
                          unfold F, R in Hmap;
                          unfold get_front, get_rear, get_ary, get_pc in Hmap;
                          simpl in Hmap.

                          rewrite Hlist in Hmap.
                          rewrite Hlist.
                          repeat rewrite get_f'_dist in Hmap.
                          repeat rewrite get_r'_dist in Hmap.
                          repeat rewrite get_f'_dist.
                          repeat rewrite get_r'_dist.
                          simpl in Hmap.
                          rewrite Nat.eqb_refl in Hmap.
                          simpl in Hmap.
                          rewrite get_f'_any_ary in Hmap; intuition.
                          rewrite get_f'_any_ary in Hmap; intuition.
                          rewrite get_r'_any_ary in Hmap; intuition.
                          rewrite get_r'_any_ary in Hmap; intuition.
                          simpl.
                          apply notin_get_none in Hnotin_res.
                          rewrite Hnotin_res.
                          simpl. auto.
                    }
              (* exclude read *)
              * 
                ** apply valid_execution_fragment_com in Hvalid.
                  simpl in Hvalid.
                  inversion H7; subst.
                  inversion H8; subst.
                  inversion H10; subst.
                  inversion H9; subst.
                  eapply internal_preserves_request'' with (pid:=pid) in Hvalid; simpl in *.
                  4 : { apply Hbinds3. }
                  3 : {
                    apply binds_push_eq.
                  }
                  discriminate.
                  eapply gather_pid_events_B_gather_pid_external_events.
                  eassumption.
            (* exclude query of front_rear *)
            +++ apply valid_execution_fragment_com in Hvalid.
                simpl in Hvalid.
                eapply internal_preserves_notin_L1'' with (pid:=pid) in Hvalid; simpl in *.
                apply binds_in in Hbinds1.
                unfold "#" in Hvalid.
                intuition.
                eapply gather_pid_events_B_gather_pid_external_events.
                eassumption.
                inversion H7; subst; simpl in *; intuition.
                inversion H8; subst; simpl in *; intuition.
      (* array read *)
      --- exists s2'.
        intuition.
        eapply Step_None; eauto.
            apply H0 in Hbinds0.
            destruct Hbinds0 as [s1 [s2 [qb [acts [Hint_query [Hvalid Hgather]]]]]].
            inversion Hint_query; subst.
            simpl in qb.
            (* try to exclude other query *)
            destruct qb; simpl in *.
            (* case of query array *)
            +++ destruct q; simpl in *.
              (* exclude cas *)
              * 
                apply valid_execution_fragment_com in Hvalid.
                  simpl in Hvalid.
                  inversion H7; subst.
                  inversion H8; subst.
                  inversion H10; subst.
                  inversion H9; subst.
                  eapply internal_preserves_request'' with (pid:=pid) in Hvalid; simpl in *.
                  4 : { apply Hbinds3. }
                  3 : {
                    apply binds_push_eq.
                  }
                  discriminate.
                  eapply gather_pid_events_B_gather_pid_external_events.
                  eassumption.


              (* case of read *)
              * 
                apply valid_execution_fragment_com' in Hvalid.
                  simpl in Hvalid.
                  destruct st2', st2.
                  eapply valid_execution_fragment_sync in Hvalid; eauto.
                  simpl.
                  inversion H6; subst.
                  inversion H10; subst.
                  clear H10.
                  inversion H8; subst; simpl in *.
                  (* enq *)
                  *** eapply noB_preserves_AEnq5 with (pid:=pid) in Hvalid; eauto.
                    2 : {
                      destruct LState.
                      simpl.
                      eapply substitute_eq_binds_v'; eauto.
                    }
                    2 : {
                      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil).
                      rewrite Hgather. simpl. reflexivity.
                      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
                      assumption.
                    }
                    apply binds_reconstruct in Hvalid.
                          destruct Hvalid as [l1 [l2 Hlist]].
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                          rewrite Hlist in Hok_wf.
                          apply ok_remove_middle_inv in Hok_wf.
                    unfold f. simpl. intuition.
                    {
                      rewrite <-Hreq.
                          rewrite Hlist.
                          repeat rewrite gather_requests_dist.
                          simpl.
                          repeat rewrite gather_requests_res_ary'; intuition.
                    }
                    {
                      rewrite <-Hres.
                      rewrite Hlist.
                      repeat rewrite gather_responses_dist.
                      simpl.
                      repeat rewrite gather_responses_res_ary'; intuition.
                    }
                    {
                          unfold F, R;
                          unfold get_front, get_rear, get_ary, get_pc;
                          simpl.
                          unfold F, R in Hmap;
                          unfold get_front, get_rear, get_ary, get_pc in Hmap;
                          simpl in Hmap.

                          rewrite Hlist in Hmap.
                          rewrite Hlist.
                          repeat rewrite get_f'_dist in Hmap.
                          repeat rewrite get_r'_dist in Hmap.
                          repeat rewrite get_f'_dist.
                          repeat rewrite get_r'_dist.
                          simpl in Hmap.
                          rewrite get_f'_any_ary in Hmap; intuition.
                          rewrite get_f'_any_ary in Hmap; intuition.
                          rewrite get_r'_any_ary in Hmap; intuition.
                          rewrite get_r'_any_ary in Hmap; intuition.
                    }
                  *** eapply noB_preserves_ADeq5 with (pid:=pid) in Hvalid; eauto.
                    2 : {
                      destruct LState.
                      simpl.
                      eapply substitute_eq_binds_v'; eauto.
                    }
                    2 : {
                      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil).
                      rewrite Hgather. simpl. reflexivity.
                      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B.
                      assumption.
                    }
                    apply binds_reconstruct in Hvalid.
                          destruct Hvalid as [l1 [l2 Hlist]].
                    unfold array_queue_wf' in H0.
                    simpl in H0.
                    destruct H0 as [Hwf Hreach].
                    unfold array_queue_wf in Hwf.
                    simpl in Hwf.
                    destruct Hwf as [Hok_wf _].
                          rewrite Hlist in Hok_wf.
                          apply ok_remove_middle_inv in Hok_wf.
                    unfold f. simpl. intuition.
                    {
                      rewrite <-Hreq.
                          rewrite Hlist.
                          repeat rewrite gather_requests_dist.
                          simpl.
                          repeat rewrite gather_requests_res_ary'; intuition.
                    }
                    {
                      rewrite <-Hres.
                      rewrite Hlist.
                      repeat rewrite gather_responses_dist.
                      simpl.
                      repeat rewrite gather_responses_res_ary'; intuition.
                    }
                    {
                          unfold F, R;
                          unfold get_front, get_rear, get_ary, get_pc;
                          simpl.
                          unfold F, R in Hmap;
                          unfold get_front, get_rear, get_ary, get_pc in Hmap;
                          simpl in Hmap.
                          rewrite Hlist in Hmap.
                          rewrite Hlist.
                          repeat rewrite get_f'_dist in Hmap.
                          repeat rewrite get_r'_dist in Hmap.
                          repeat rewrite get_f'_dist.
                          repeat rewrite get_r'_dist.
                          simpl in Hmap.
                          rewrite get_f'_any_ary in Hmap; intuition.
                          rewrite get_f'_any_ary in Hmap; intuition.
                          rewrite get_r'_any_ary in Hmap; intuition.
                          rewrite get_r'_any_ary in Hmap; intuition.
                    }
            (* exclude query of front_rear *)
            +++ apply valid_execution_fragment_com in Hvalid.
                simpl in Hvalid.
                eapply internal_preserves_notin_L1'' with (pid:=pid) in Hvalid; simpl in *.
                apply binds_in in Hbinds1.
                unfold "#" in Hvalid.
                intuition.
                eapply gather_pid_events_B_gather_pid_external_events.
                eassumption.
                inversion H7; subst; simpl in *; intuition.
                inversion H8; subst; simpl in *; intuition.
  - unfold f in H1.
    destruct H1 as [Hreq [Hres Hmap]].
    inversion H2; subst.
    simpl in *. clear H2.
    inversion H1; subst.
    simpl in *. clear H1.
    exists s2'.
    intuition. eapply Step_None; auto.
    unfold f. simpl. intuition.
    -- inversion H2; subst; simpl in *;
      rewrite <-Hreq;
      apply binds_reconstruct in Hbinds0;
      destruct Hbinds0 as [l1 [l2 Hlist]];
      rewrite Hlist in Hok_pc;
      rewrite Hlist;
      apply ok_remove_middle_inv in Hok_pc;
      rewrite substitute_notin_app; intuition;
      repeat rewrite gather_requests_dist;
      simpl;
      rewrite Nat.eqb_refl;
      simpl;
      repeat rewrite gather_requests_rear; auto;
      repeat rewrite gather_requests_front; auto.
    -- inversion H2; subst; simpl in *;
      rewrite <-Hres;
      apply binds_reconstruct in Hbinds0;
      destruct Hbinds0 as [l1 [l2 Hlist]];
      rewrite Hlist in Hok_pc;
      rewrite Hlist;
      apply ok_remove_middle_inv in Hok_pc;
      rewrite substitute_notin_app; intuition;
      repeat rewrite gather_responses_dist;
      simpl;
      rewrite Nat.eqb_refl;
      simpl;
      repeat rewrite gather_responses_rear; auto;
      repeat rewrite gather_responses_front; auto;
      repeat rewrite gather_responses_x; auto.
      match_if'.
    -- clear Hreq Hres.
      rewrite <-Hmap.
      clear Hmap.
      inversion H2; subst;
      simpl;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        unfold F, R;
        unfold get_front, get_rear, get_ary, get_pc;
        rewrite Hlist in Hok_pc;
        simpl;
        rewrite Hlist;
        apply ok_remove_middle_inv in Hok_pc;
        rewrite substitute_notin_app; intuition;
        simpl; rewrite Nat.eqb_refl;
        repeat rewrite get_f'_dist;
        simpl get_f';
        repeat rewrite get_r'_dist;
        simpl get_r';
        reflexivity.
  - inversion H2; subst.
    exists s2'. intuition.
    eapply Step_None; eauto.
      unfold f. simpl.
      unfold f in H1. simpl in H1.
      destruct H1 as [Hreq [Hres Hmap]].
      intuition.
    -- inversion H3; inversion H4; subst.
      simpl in *.
      rewrite <-Hreq.
      inversion H1; subst;
       simpl;
      inversion H11; subst; simpl in *;
      inversion H6; subst; simpl in *;
      inversion H5; subst; simpl in *;
      (try inversion H8; subst; simpl in *);
      (try inversion H7; subst; simpl in *);
      generalize binds_reconstruct; intro Hre;
      specialize (Hre _ _ _ _ Hbinds0);
      destruct Hre as [l1 [l2 Hlist]];
      rewrite Hlist;
      rewrite Hlist in Hok_pc;
      apply ok_remove_middle_inv in Hok_pc;
      rewrite substitute_notin_app; intuition;
      repeat rewrite gather_requests_dist;
      simpl;
      rewrite Nat.eqb_refl;
      simpl; try reflexivity.
      apply notin_get_none in Hnotin_res.
      rewrite Hnotin_res. reflexivity.
      apply notin_get_none in Hnotin_res.
      rewrite Hnotin_res. reflexivity.
    -- inversion H3; inversion H4; subst.
      simpl in *.
      rewrite <-Hres.
      inversion H1; subst;
       simpl;
      inversion H11; subst; simpl in *;
      inversion H6; subst; simpl in *;
      inversion H5; subst; simpl in *;
      (try inversion H8; subst; simpl in *);
      (try inversion H7; subst; simpl in *);
      generalize binds_reconstruct; intro Hre;
      specialize (Hre _ _ _ _ Hbinds0);
      destruct Hre as [l1 [l2 Hlist]];
      rewrite Hlist;
      rewrite Hlist in Hok_pc;
      apply ok_remove_middle_inv in Hok_pc;
      rewrite substitute_notin_app; intuition;
      repeat rewrite gather_responses_dist;
      simpl;
      rewrite Nat.eqb_refl;
      simpl; try reflexivity.
      apply notin_get_none in Hnotin_res.
      rewrite Hnotin_res. reflexivity.
      apply notin_get_none in Hnotin_res.
      rewrite Hnotin_res. reflexivity.
      match_if'.
    -- rewrite <-Hmap.
      inversion H3; inversion H4; subst.
      simpl in *.
      inversion H1; subst; simpl;
       simpl;
      inversion H11; subst; simpl in *;
      inversion H6; subst; simpl in *;
      inversion H5; subst; simpl in *;
      try (inversion H8; subst; simpl in *);
      try (inversion H7; subst; simpl in *);
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        rewrite Hlist in Hok_pc;
        rewrite Hlist;
        unfold F, R;
        unfold get_front, get_rear, get_ary, get_pc;
        simpl;
        apply ok_remove_middle_inv in Hok_pc;
        rewrite substitute_notin_app; intuition;
        simpl; rewrite Nat.eqb_refl;
        repeat rewrite get_f'_dist;
        simpl get_f';
        repeat rewrite get_r'_dist;
        simpl get_r';
        try reflexivity.
        apply notin_get_none in Hnotin_res.
        rewrite Hnotin_res. reflexivity.
        apply notin_get_none in Hnotin_res.
        rewrite Hnotin_res. reflexivity.
        apply notin_get_none in Hnotin_res.
        rewrite Hnotin_res. reflexivity.
        apply notin_get_none in Hnotin_res.
        rewrite Hnotin_res. reflexivity.
  - inversion H2; subst.
    exists s2'. intuition.
    eapply Step_None; eauto.
      unfold f. simpl.
      unfold f in H1. simpl in H1.
      destruct H1 as [Hreq [Hres Hmap]].
      intuition.
    -- inversion H3; inversion H4; subst.
      simpl in *.
      rewrite <-Hreq.
      inversion H11; subst;
       simpl;
      inversion H1; subst; simpl in *;
      inversion H6; subst; simpl in *;
      inversion H5; subst; simpl in *;
      (try inversion H8; subst; simpl in *);
      (try inversion H7; subst; simpl in *);
      generalize binds_reconstruct; intro Hre;
      specialize (Hre _ _ _ _ Hbinds1);
      destruct Hre as [l1 [l2 Hlist]];
      rewrite Hlist;
      rewrite Hlist in Hok_pc;
      apply ok_remove_middle_inv in Hok_pc;
      rewrite substitute_notin_app; intuition;
      repeat rewrite gather_requests_dist;
      simpl;
      rewrite Nat.eqb_refl;
      simpl;
      repeat rewrite gather_requests_res_ary;
      repeat rewrite gather_requests_res_front;
      repeat rewrite gather_requests_res_rear;
      auto.
      simpl.
      rewrite Hbinds4.
      match_if'.
      rewrite Hbinds4.
      match_if'.
    -- inversion H3; inversion H4; subst.
      simpl in *.
      rewrite <-Hres.
      inversion H11; subst;
       simpl;
      inversion H1; subst; simpl in *;
      inversion H6; subst; simpl in *;
      inversion H5; subst; simpl in *;
      (try inversion H8; subst; simpl in *);
      (try inversion H7; subst; simpl in *);
      generalize binds_reconstruct; intro Hre;
      specialize (Hre _ _ _ _ Hbinds1);
      destruct Hre as [l1 [l2 Hlist]];
      rewrite Hlist;
      rewrite Hlist in Hok_pc;
      apply ok_remove_middle_inv in Hok_pc;
      rewrite substitute_notin_app; intuition;
      repeat rewrite gather_responses_dist;
      simpl;
      rewrite Nat.eqb_refl;
      simpl;
      repeat rewrite gather_responses_res_ary;
      repeat rewrite gather_responses_res_front;
      repeat rewrite gather_responses_res_rear;
      auto.
      simpl.
      rewrite Hbinds4.
      match_if'.
      rewrite Hbinds4.
      match_if'.
      match_if'.
    -- rewrite <-Hmap.
      inversion H3; inversion H4; subst.
      simpl in *.
      inversion H11; subst; simpl;
       simpl;
      inversion H1; subst; simpl in *;
      inversion H6; subst; simpl in *;
      inversion H5; subst; simpl in *;
      try (inversion H8; subst; simpl in *);
      try (inversion H7; subst; simpl in *);
        apply binds_reconstruct in Hbinds1;
        destruct Hbinds1 as [l1 [l2 Hlist]];
        rewrite Hlist in Hok_pc;
        unfold F, R;
        unfold get_front, get_rear, get_ary, get_pc;
        simpl;
        rewrite Hlist;
        apply ok_remove_middle_inv in Hok_pc;
        destruct Hok_pc as [Hok_pc1 Hok_pc2];
        apply ok_concat_inv in Hok_pc1;
        rewrite substitute_notin_app; intuition;
        simpl; rewrite Nat.eqb_refl;
        repeat rewrite get_f'_dist;
        simpl get_f';
        repeat rewrite get_r'_dist;
        simpl get_r';
        repeat rewrite get_f'_res_ary;
        repeat rewrite get_r'_res_ary;
        repeat rewrite get_r'_any_rear_remove;
        repeat rewrite get_f'_any_rear_remove;
        repeat rewrite get_r'_any_ary_remove;
        repeat rewrite get_f'_any_ary_remove;
        auto;
        try reflexivity.
        simpl.
      rewrite Hbinds4.
      match_if'.
      Import Lia.
      f_equal.
      rewrite Hbinds6.
      lia.
      rewrite Hbinds4.
      match_if'.
      Import Lia.
      f_equal.
      rewrite Hbinds6.
      lia.
Qed.
  
End Correctness.
