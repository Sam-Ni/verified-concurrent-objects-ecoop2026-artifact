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
  Array
  Counter
  CounterProp
  ComposedLTS
  KInduction
  ArrayQueue
  ArrayQueueImpl
  ArrayQueueMapping
  ArrayQueueProp
  ArrayQueueImplProp
  ArrayQueueImplProp2
  Queue
  ArrayQueueInvariant
  ArrayQueueInvariant2
  ArrayProp
  ArrayQueueInvariantBefore
  ArrayQueueInvariantBefore2
  ArrayQueueInvariant11
  ArrayQueueInvariant12
  ArrayToQueue.
Import ListNotations.

Section test.

Variable L : nat.

Arguments get_pc {L}.
Arguments R {L}.
Arguments F {L}.

Lemma R_not_decrease: forall s s' acts
  (Hreach : composed_lts.reachable (composed_array_queue L) s),
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  (R s) <= (R s').
Proof.
  induction 2; intros.
  - subst. lia.
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Internal_L1; eauto;
    eapply composed_lts.Step_None; eauto.
    specialize (IHvalid_execution_fragment Htmp).
    clear Htmp.
    inversion H; subst; simpl in *.
    inversion H1; subst; simpl in *.
    unfold F, R in *; simpl in *.
    unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
    inversion H2; subst; simpl in *.
    (* front_rear *)
    -- inversion H3; subst; simpl in *.
      inversion H4; subst; simpl in *.
      (* rear *)
      --- inversion H5; subst; simpl in *.
        inversion H6; subst; simpl in *.
        (* INC *)
        + pose proof Hreach as HreachTmp.
          apply inv_rear_inc_at_e31_invariant in Hreach.
          unfold inv_rear_inc_at_e31 in Hreach.
          apply Hreach in Hbinds5; auto.
          simpl in Hbinds5.
          apply binds_reconstruct in Hbinds5.
          destruct Hbinds5 as [l1 [l2 Hlist]].
          apply array_queue_wf_invarint in HreachTmp.
          unfold array_queue_wf in HreachTmp.
          simpl in HreachTmp.
          rewrite Hlist in HreachTmp.
          apply ok_remove_middle_inv in HreachTmp.
          destruct HreachTmp as [Hokl [Hnt1 Hnt2]].
          rewrite Hlist in IHvalid_execution_fragment.
          repeat rewrite get_r'_dist in IHvalid_execution_fragment; auto.
          repeat rewrite get_f'_dist in IHvalid_execution_fragment; auto.
          simpl in *.
          apply notin_get_none in Hnotin_res.
          rewrite Hnotin_res in IHvalid_execution_fragment.
          rewrite Nat.eqb_refl in IHvalid_execution_fragment.
          rewrite get_r'_any_rear_push in IHvalid_execution_fragment; auto.
          rewrite get_r'_any_rear_push in IHvalid_execution_fragment; auto.
          simpl in *.
          rewrite Hlist.
          repeat rewrite get_r'_dist; auto.
          repeat rewrite get_f'_dist; auto.
          simpl.
          rewrite Hnotin_res.
          repeat rewrite Nat.add_succ_r; auto.
        (* READ *)
        + rewrite get_r'_any_rear_read in IHvalid_execution_fragment; auto.
      (* front *)
      --- intuition.
    (* array *)
    -- inversion H3; subst; simpl in *.
      inversion H4; subst; simpl in *.
      (* CAS *)
      --- destruct ((entry_eqb (Vector.nth vec (Fin.of_nat_lt Hlt))
                     old)).
        (* success *)
        + pose proof Hreach as HreachTmp.
          apply inv_ary_cas_at_e28_d28_invariant in Hreach.
          unfold inv_ary_cas_at_e28_d28 in Hreach.
          apply Hreach in Hbinds3; auto.
          simpl in Hbinds3.
          destruct Hbinds3 as [Hb|Hb].
          (* e28 *)
          ++ apply binds_reconstruct in Hb.
            destruct Hb as [l1 [l2 Hlist]].
            apply array_queue_wf_invarint in HreachTmp.
            unfold array_queue_wf in HreachTmp.
            simpl in HreachTmp.
            rewrite Hlist in HreachTmp.
            apply ok_remove_middle_inv in HreachTmp.
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]].

            rewrite Hlist in IHvalid_execution_fragment.
            repeat rewrite get_r'_dist in IHvalid_execution_fragment; auto.
            repeat rewrite get_f'_dist in IHvalid_execution_fragment; auto.
            simpl in *.
            apply notin_get_none in Hnotin_res.
            rewrite Hnotin_res in IHvalid_execution_fragment.
            rewrite Nat.eqb_refl in IHvalid_execution_fragment.
            rewrite get_r'_any_ary in IHvalid_execution_fragment; auto.
            rewrite get_r'_any_ary in IHvalid_execution_fragment; auto.
            repeat rewrite Nat.add_succ_r in IHvalid_execution_fragment.
            simpl in *.
            rewrite Hlist.
            repeat rewrite get_r'_dist; auto.
            repeat rewrite get_f'_dist; auto.
            simpl.
            rewrite Hnotin_res.
            lia.
          (* d28 *)
          ++ apply binds_reconstruct in Hb.
            destruct Hb as [l1 [l2 Hlist]].
            apply array_queue_wf_invarint in HreachTmp.
            unfold array_queue_wf in HreachTmp.
            simpl in HreachTmp.
            rewrite Hlist in HreachTmp.
            apply ok_remove_middle_inv in HreachTmp.
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]].

            rewrite Hlist in IHvalid_execution_fragment.
            repeat rewrite get_r'_dist in IHvalid_execution_fragment; auto.
            repeat rewrite get_f'_dist in IHvalid_execution_fragment; auto.
            simpl in *.
            rewrite get_r'_any_ary in IHvalid_execution_fragment; auto.
            rewrite get_r'_any_ary in IHvalid_execution_fragment; auto.
            repeat rewrite Nat.add_succ_r in IHvalid_execution_fragment.
            simpl in *.
            rewrite Hlist.
            repeat rewrite get_r'_dist; auto.
        (* fail *)
        + rewrite get_r'_any_ary_cas_false in IHvalid_execution_fragment; auto.
      (* READ *)
      --- rewrite get_r'_any_ary_read in IHvalid_execution_fragment; auto.
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Internal_L2; eauto;
    eapply composed_lts.Step_None; eauto.
    specialize (IHvalid_execution_fragment Htmp).
    clear Htmp.
    inversion H; subst; simpl in *.
    inversion H1; subst; simpl in *.
    unfold F, R in *; simpl in *.
    unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
    inversion H2; subst; simpl in *;
          apply binds_reconstruct in Hbinds0;
            destruct Hbinds0 as [l1 [l2 Hlist]];
            pose Hreach as HreachTmp;
            apply array_queue_wf_invarint in HreachTmp;
            unfold array_queue_wf in HreachTmp;
            simpl in HreachTmp;
            rewrite Hlist in HreachTmp;
            apply ok_remove_middle_inv in HreachTmp;
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
            rewrite Hlist in IHvalid_execution_fragment;
            rewrite substitute_notin_app in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Nat.eqb_refl in IHvalid_execution_fragment; auto;
            repeat rewrite get_r'_dist in IHvalid_execution_fragment; auto;
            repeat rewrite get_f'_dist in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto.
  - inversion H.
  - inversion H.
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Initial_Call; eauto;
    eapply composed_lts.Step_None; eauto.
    specialize (IHvalid_execution_fragment Htmp).
    clear Htmp.
    inversion H; subst; simpl in *.
    inversion H1; subst; simpl in *.
    unfold F, R in *; simpl in *.
    unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
    inversion H2; subst; simpl in *; auto.
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Final_Return; eauto;
    eapply composed_lts.Step_None; eauto.
    specialize (IHvalid_execution_fragment Htmp).
    clear Htmp.
    inversion H; subst; simpl in *.
    inversion H1; subst; simpl in *.
    unfold F, R in *; simpl in *.
    unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
    inversion H2; subst; simpl in *;
          apply binds_reconstruct in Hbinds0;
            destruct Hbinds0 as [l1 [l2 Hlist]];
            pose Hreach as HreachTmp;
            apply array_queue_wf_invarint in HreachTmp;
            unfold array_queue_wf in HreachTmp;
            simpl in HreachTmp;
            rewrite Hlist in HreachTmp;
            apply ok_remove_middle_inv in HreachTmp;
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
            rewrite Hlist in IHvalid_execution_fragment;
            rewrite remove_notin_app in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Nat.eqb_refl in IHvalid_execution_fragment; auto;
            repeat rewrite get_r'_dist in IHvalid_execution_fragment; auto;
            repeat rewrite get_f'_dist in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto.
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Internal_Query; eauto;
    eapply composed_lts.Step_None; eauto.
    specialize (IHvalid_execution_fragment Htmp).
    clear Htmp.
    inversion H; subst; simpl in *.
    inversion H1; subst; simpl in *.
    unfold F, R in *; simpl in *.
    unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
    inversion H3; subst; simpl in *.
          all : try (apply binds_reconstruct in Hbinds0;
            destruct Hbinds0 as [l1 [l2 Hlist]];
            pose Hreach as HreachTmp;
            apply array_queue_wf_invarint in HreachTmp;
            unfold array_queue_wf in HreachTmp;
            simpl in HreachTmp;
            rewrite Hlist in HreachTmp;
            apply ok_remove_middle_inv in HreachTmp;
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
            rewrite Hlist in IHvalid_execution_fragment;
            rewrite substitute_notin_app in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Nat.eqb_refl in IHvalid_execution_fragment; auto;
            repeat rewrite get_r'_dist in IHvalid_execution_fragment; auto;
            repeat rewrite get_f'_dist in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto;
            simpl; auto;
            inversion H2; subst; simpl in *;
            inversion H4; subst; simpl in *;
            inversion H6; subst; simpl in *;
            inversion H5; subst; simpl in *;
            try (inversion H8; subst; simpl in *);
            try (inversion H7; subst; simpl in *);
            try (apply notin_get_none in Hnotin_res);
            try (rewrite Hnotin_res in IHvalid_execution_fragment);
            lia).
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Internal_Reply; eauto;
    eapply composed_lts.Step_None; eauto.
    specialize (IHvalid_execution_fragment Htmp).
    clear Htmp.
    inversion H; subst; simpl in *.
    inversion H2; subst; simpl in *.
    unfold F, R in *; simpl in *.
    unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
    inversion H3; subst; simpl in *.
          all : try (apply binds_reconstruct in Hbinds0;
            destruct Hbinds0 as [l1 [l2 Hlist]];
            pose Hreach as HreachTmp;
            apply array_queue_wf_invarint in HreachTmp;
            unfold array_queue_wf in HreachTmp;
            simpl in HreachTmp;
            rewrite Hlist in HreachTmp;
            apply ok_remove_middle_inv in HreachTmp;
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
            rewrite Hlist in IHvalid_execution_fragment;
            rewrite substitute_notin_app in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Nat.eqb_refl in IHvalid_execution_fragment; auto;
            repeat rewrite get_r'_dist in IHvalid_execution_fragment; auto;
            repeat rewrite get_f'_dist in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto;
            simpl; auto;
            inversion H1; subst; simpl in *;
            inversion H4; subst; simpl in *;
            inversion H6; subst; simpl in *;
            inversion H5; subst; simpl in *;
            try (inversion H8; subst; simpl in *);
            try (inversion H7; subst; simpl in *);
            try (apply notin_get_none in Hnotin_res);
            try (rewrite Hnotin_res in IHvalid_execution_fragment);
            lia).
          all : apply binds_reconstruct in Hbinds0;
            destruct Hbinds0 as [l1 [l2 Hlist]];
            pose Hreach as HreachTmp;
            apply array_queue_wf_invarint in HreachTmp;
            unfold array_queue_wf in HreachTmp;
            simpl in HreachTmp;
            rewrite Hlist in HreachTmp;
            apply ok_remove_middle_inv in HreachTmp;
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
            apply ok_concat_inv in Hokl;
            destruct Hokl as [Hokl1 Hokl2];
            rewrite Hlist in IHvalid_execution_fragment;
            rewrite substitute_notin_app in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Nat.eqb_refl in IHvalid_execution_fragment; auto;
            repeat rewrite get_r'_dist in IHvalid_execution_fragment; auto;
            repeat rewrite get_f'_dist in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto;
            simpl; auto;
            inversion H1; subst; simpl in *;
            inversion H4; subst; simpl in *;
            inversion H6; subst; simpl in *;
            inversion H5; subst; simpl in *;
            try (inversion H8; subst; simpl in *);
            try (inversion H7; subst; simpl in *);
            try (rewrite get_r'_any_rear_remove in IHvalid_execution_fragment; auto);
            try (rewrite get_r'_any_rear_remove in IHvalid_execution_fragment; auto);
            try (rewrite get_r'_any_ary_remove in IHvalid_execution_fragment; auto);
            try (rewrite get_r'_any_ary_remove in IHvalid_execution_fragment; auto);
            try (unfold binds in Hbinds3);
            try (unfold binds in Hbinds5);
            try (rewrite Hbinds3; auto);
            try (rewrite Hbinds5; auto).
Qed.

Lemma inv_R_increase_step_L1: forall (s s' : composed_lts.state (composed_array_queue L)) acts
  (Hreach : composed_lts.reachable (composed_array_queue L) s),
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s' acts ->
  R s < R s' ->
  exists s1 s2 acts1 acts2 pid,
    composed_lts.valid_execution_fragment (composed_array_queue L)
      s s1 acts1 /\
      composed_lts.step_L1
        (composed_array_queue L)
        s1 pid
          (@Tensor.intL1 li_array li_cnt_cnt (array L) ArrayQueue.front_rear
            int_ary_cas
            (* (@Tensor.intL2 li_counter li_counter counter counter (int_ary_cas)) *)
          )
        s2 /\
    composed_lts.valid_execution_fragment (composed_array_queue L)
      s2 s' acts2 /\
      acts = acts1 ++ acts2 /\
      R s1 = R s /\
      binds pid AEnq28 (get_pc s1).
Proof.
  induction 2; intros.
  - subst. lia.
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Internal_L1; eauto;
    eapply composed_lts.Step_None; eauto.
    specialize (IHvalid_execution_fragment Htmp).
    inversion H; subst; simpl in *.
    inversion H2; subst; simpl in *.
    unfold F, R in *; simpl in *.
    unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
    inversion H3; subst; simpl in *.
    (* front_rear *)
    -- inversion H4; subst; simpl in *.
      inversion H5; subst; simpl in *.
      (* rear *)
      --- inversion H6; subst; simpl in *.
        inversion H7; subst; simpl in *.
        (* INC *)
        + pose proof Hreach as HreachTmp.
          apply inv_rear_inc_at_e31_invariant in Hreach.
          unfold inv_rear_inc_at_e31 in Hreach.
          apply Hreach in Hbinds5; auto.
          simpl in Hbinds5.
          apply binds_reconstruct in Hbinds5.
          destruct Hbinds5 as [l1 [l2 Hlist]].
          apply array_queue_wf_invarint in HreachTmp.
          unfold array_queue_wf in HreachTmp.
          simpl in HreachTmp.
          rewrite Hlist in HreachTmp.
          apply ok_remove_middle_inv in HreachTmp.
          destruct HreachTmp as [Hokl [Hnt1 Hnt2]].
          rewrite Hlist in H1, IHvalid_execution_fragment.
          repeat rewrite get_r'_dist in H1, IHvalid_execution_fragment; auto.
          repeat rewrite get_f'_dist in H1, IHvalid_execution_fragment; auto.
          simpl in *.
          apply notin_get_none in Hnotin_res.
          rewrite Hnotin_res in H1, IHvalid_execution_fragment.
          rewrite Nat.eqb_refl in IHvalid_execution_fragment.
          rewrite get_r'_any_rear_push in IHvalid_execution_fragment; auto.
          rewrite get_r'_any_rear_push in IHvalid_execution_fragment; auto.
          simpl in *.
          repeat rewrite Nat.add_succ_r in H1.
          intuition.
          rewrite Hlist.
          repeat rewrite get_r'_dist; auto.
          repeat rewrite get_f'_dist; auto.
          simpl.
          rewrite Hnotin_res.
          repeat rewrite Nat.add_succ_r; auto.

          destruct H10 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts Heq]]]]]]]]].
          exists s1, s2, acts1, acts2, pid0. intuition.
          eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
          eapply composed_lts.Step_Internal_L1.
          eauto.
          eapply composed_lts.Step_None; eauto.
          eauto.
          simpl. auto.
        (* READ *)
        + rewrite get_r'_any_rear_read in IHvalid_execution_fragment; auto.
          intuition.
          destruct H8 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts Heq]]]]]]]]].
          exists s1, s2, acts1, acts2, pid0. intuition.
          eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
          eapply composed_lts.Step_Internal_L1.
          eauto.
          eapply composed_lts.Step_None; eauto.
          eauto.
          simpl. auto.
      (* front *)
      --- intuition.
          destruct H7 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts Heq]]]]]]]]].
          exists s1, s2, acts1, acts2, pid0. intuition.
          eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
          eapply composed_lts.Step_Internal_L1.
          eauto.
          eapply composed_lts.Step_None; eauto.
          eauto.
          simpl. auto.
    (* array *)
    -- inversion H4; subst; simpl in *.
      inversion H5; subst; simpl in *.
      (* CAS *)
      --- destruct ((entry_eqb (Vector.nth vec (Fin.of_nat_lt Hlt)) old)).
        (* success *)
        + pose proof Hreach as HreachTmp.
          apply inv_ary_cas_at_e28_d28_invariant in Hreach.
          unfold inv_ary_cas_at_e28_d28 in Hreach.
          apply Hreach in Hbinds3; auto.
          simpl in Hbinds3.
          destruct Hbinds3 as [Hb|Hb].
          (* e28 *)
          ++ pose proof Hb as HbindsTmp.
            apply binds_reconstruct in Hb.
            destruct Hb as [l1 [l2 Hlist]].
            pose proof HreachTmp as HreachTmp2.
            apply array_queue_wf_invarint in HreachTmp.
            unfold array_queue_wf in HreachTmp.
            simpl in HreachTmp.
            rewrite Hlist in HreachTmp.
            apply ok_remove_middle_inv in HreachTmp.
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]].
            rewrite Hlist in H1, IHvalid_execution_fragment.
            repeat rewrite get_r'_dist in H1, IHvalid_execution_fragment; auto.
            repeat rewrite get_f'_dist in H1, IHvalid_execution_fragment; auto.
            simpl in *.
            apply notin_get_none in Hnotin_res.
            rewrite Hnotin_res in H1, IHvalid_execution_fragment.
            rewrite Nat.eqb_refl in IHvalid_execution_fragment.
            rewrite get_r'_any_ary in IHvalid_execution_fragment; auto.
            rewrite get_r'_any_ary in IHvalid_execution_fragment; auto.
            simpl in *.
            repeat rewrite Nat.add_succ_r in H1.
            intuition.
            rewrite Hlist.
            repeat rewrite get_r'_dist; auto.
            repeat rewrite get_f'_dist; auto.
            simpl.
            rewrite Hnotin_res.
            repeat rewrite Nat.add_succ_r; auto.
            eapply R_not_decrease in Htmp; eauto.
            unfold F, R in *; simpl in *.
            unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
            rewrite Hlist in Htmp.
            repeat rewrite get_r'_dist in Htmp; auto.
            repeat rewrite get_f'_dist in Htmp; auto.
            simpl in *.
            rewrite Hnotin_res in Htmp.
            rewrite Nat.eqb_refl in Htmp.
            rewrite get_r'_any_ary in Htmp; auto.
            rewrite get_r'_any_ary in Htmp; auto.
            repeat rewrite Nat.add_succ_r in Htmp.
            repeat rewrite Nat.add_succ_r in IHvalid_execution_fragment.
            eexists.
            eexists.
            exists [].
            exists acts.
            exists pid.
            intuition.
            eapply composed_lts.Step_None; eauto.
            eauto.
            eauto.
            simpl.
            rewrite Hlist.
            repeat rewrite get_r'_dist; auto.
            repeat rewrite get_f'_dist; auto.
            simpl in *.
            rewrite Hnotin_res. auto.
            simpl.
            auto.
          (* d28 *)
          ++ apply binds_reconstruct in Hb.
            destruct Hb as [l1 [l2 Hlist]].
            pose proof HreachTmp as HreachTmp2.
            apply array_queue_wf_invarint in HreachTmp.
            unfold array_queue_wf in HreachTmp.
            simpl in HreachTmp.
            rewrite Hlist in HreachTmp.
            apply ok_remove_middle_inv in HreachTmp.
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]].
            rewrite Hlist in H1, IHvalid_execution_fragment.
            repeat rewrite get_r'_dist in H1, IHvalid_execution_fragment; auto.
            repeat rewrite get_f'_dist in H1, IHvalid_execution_fragment; auto.
            simpl in *.
            apply notin_get_none in Hnotin_res.
            rewrite get_r'_any_ary in IHvalid_execution_fragment; auto.
            rewrite get_r'_any_ary in IHvalid_execution_fragment; auto.
            simpl in *.
            repeat rewrite Nat.add_succ_r in H1.
            intuition.
            rewrite Hlist.
            repeat rewrite get_r'_dist; auto.
            repeat rewrite get_f'_dist; auto.
            simpl.
            repeat rewrite Nat.add_succ_r; auto.
            destruct H8 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts Heq]]]]]]]]].
            exists s1, s2, acts1, acts2, pid0. intuition.
            eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
            eapply composed_lts.Step_Internal_L1.
            eauto.
            eapply composed_lts.Step_None; eauto.
            eauto.
            simpl. auto.
        (* fail *)
        + rewrite get_r'_any_ary_cas_false in IHvalid_execution_fragment; auto.
          intuition.
            destruct H6 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts Heq]]]]]]]]].
            exists s1, s2, acts1, acts2, pid0. intuition.
            eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
            eapply composed_lts.Step_Internal_L1.
            eauto.
            eapply composed_lts.Step_None; eauto.
            eauto.
            simpl. auto.
      (* READ *)
      --- rewrite get_r'_any_ary_read in IHvalid_execution_fragment; auto.
        intuition.
        destruct H6 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts Heq]]]]]]]]].
        exists s1, s2, acts1, acts2, pid0. intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
        eapply composed_lts.Step_Internal_L1.
        eauto.
        eapply composed_lts.Step_None; eauto.
        eauto.
        simpl. auto.
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Internal_L2; eauto;
    eapply composed_lts.Step_None; eauto.
    specialize (IHvalid_execution_fragment Htmp).
    inversion H; subst; simpl in *.
    inversion H2; subst; simpl in *.
    unfold F, R in *; simpl in *.
    unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
    inversion H3; subst; simpl in *.

          all : try (apply binds_reconstruct in Hbinds0;
            destruct Hbinds0 as [l1 [l2 Hlist]];
            pose Hreach as HreachTmp;
            apply array_queue_wf_invarint in HreachTmp;
            unfold array_queue_wf in HreachTmp;
            simpl in HreachTmp;
            rewrite Hlist in HreachTmp;
            apply ok_remove_middle_inv in HreachTmp;
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
            rewrite Hlist in IHvalid_execution_fragment at 1;
            rewrite substitute_notin_app in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Nat.eqb_refl in IHvalid_execution_fragment; auto;
            repeat rewrite get_r'_dist in IHvalid_execution_fragment; auto;
            repeat rewrite get_f'_dist in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto;
            rewrite Hlist in H1;
            simpl in *;
            repeat rewrite get_r'_dist in H1; auto;
            repeat rewrite get_f'_dist in H1; auto;
            simpl in *;
            intuition;
            try (destruct H4 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq Hb]]]]]]]]]]);
            try (destruct H5 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq Hb]]]]]]]]]]);
            exists s1, s2, acts1, acts2, pid0; intuition; auto;
            try rewrite <-Hlist in *;

            [eapply composed_lts.valid_execution_fragment_join' with (a':=acts1);
            [eapply composed_lts.Step_Internal_L2;
            try (eapply composed_lts.Step_None; eauto);
            eauto;
            eauto| eauto | simpl; auto] |
            rewrite Heq;
            rewrite Hlist;
            rewrite substitute_notin_app; auto;
            simpl in *;
            rewrite Nat.eqb_refl; auto;
            repeat rewrite get_r'_dist; auto;
            repeat rewrite get_f'_dist; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto]).
  - inversion H.
  - inversion H.
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Initial_Call; eauto;
    eapply composed_lts.Step_None; eauto.
    specialize (IHvalid_execution_fragment Htmp).
    inversion H; subst; simpl in *.
    inversion H2; subst; simpl in *.
    unfold F, R in *; simpl in *.
    unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
    inversion H3; subst; simpl in *.
      intuition.
        destruct H4 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts Heq]]]]]]]]].
        exists s1, s2.
        eexists.
        exists acts2, pid0. intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
        eapply composed_lts.Step_Initial_Call.
        eauto.
        eapply composed_lts.Step_None; eauto.
        eauto.
        simpl. auto.
        simpl.
        rewrite Hacts. auto.
      intuition.
        destruct H4 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts Heq]]]]]]]]].
        exists s1, s2.
        eexists.
        exists acts2, pid0. intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
        eapply composed_lts.Step_Initial_Call.
        eauto.
        eapply composed_lts.Step_None; eauto.
        eauto.
        simpl. auto.
        simpl.
        rewrite Hacts. auto.
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Final_Return; eauto;
    eapply composed_lts.Step_None; eauto.
    specialize (IHvalid_execution_fragment Htmp).
    inversion H; subst; simpl in *.
    inversion H2; subst; simpl in *.
    unfold F, R in *; simpl in *.
    unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
    inversion H3; subst; simpl in *;
      intuition;

          apply binds_reconstruct in Hbinds0;
            destruct Hbinds0 as [l1 [l2 Hlist]];
            pose Hreach as HreachTmp;
            apply array_queue_wf_invarint in HreachTmp;
            unfold array_queue_wf in HreachTmp;
            simpl in HreachTmp;
            rewrite Hlist in HreachTmp;
            apply ok_remove_middle_inv in HreachTmp;
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
            rewrite Hlist in IHvalid_execution_fragment at 1;
            rewrite remove_notin_app in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Nat.eqb_refl in IHvalid_execution_fragment; auto;
            repeat rewrite get_r'_dist in IHvalid_execution_fragment; auto;
            repeat rewrite get_f'_dist in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto;
            rewrite Hlist in H1;
            simpl in *;
            repeat rewrite get_r'_dist in H1; auto;
            repeat rewrite get_f'_dist in H1; auto;
            simpl in *;
            intuition;
            try rewrite <-Hlist in *.
        destruct H4 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq Hb]]]]]]]]]].
        exists s1, s2.
        eexists.
        exists acts2, pid0. intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
        eapply composed_lts.Step_Final_Return.
        eauto.
        eapply composed_lts.Step_None; eauto.
        eauto.
        simpl. auto.
        simpl.
        rewrite Hacts. auto.
            rewrite Heq;
            rewrite Hlist;
            rewrite remove_notin_app; auto;
            simpl in *;
            rewrite Nat.eqb_refl; auto;
            repeat rewrite get_r'_dist; auto;
            repeat rewrite get_f'_dist; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto.

        destruct H5 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq Hb]]]]]]]]]].
        exists s1, s2.
        eexists.
        exists acts2, pid0. intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
        eapply composed_lts.Step_Final_Return.
        eauto.
        eapply composed_lts.Step_None; eauto.
        eauto.
        simpl. auto.
        simpl.
        rewrite Hacts. auto.
            rewrite Heq;
            rewrite Hlist;
            rewrite remove_notin_app; auto;
            simpl in *;
            rewrite Nat.eqb_refl; auto;
            repeat rewrite get_r'_dist; auto;
            repeat rewrite get_f'_dist; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto.
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Internal_Query; eauto;
    eapply composed_lts.Step_None; eauto.
    specialize (IHvalid_execution_fragment Htmp).
    inversion H; subst; simpl in *.
    inversion H2; subst; simpl in *.
    unfold F, R in *; simpl in *.
    unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
    inversion H4; subst; simpl in *.

          all : try (apply binds_reconstruct in Hbinds0;
            destruct Hbinds0 as [l1 [l2 Hlist]];
            pose Hreach as HreachTmp;
            apply array_queue_wf_invarint in HreachTmp;
            unfold array_queue_wf in HreachTmp;
            simpl in HreachTmp;
            rewrite Hlist in HreachTmp;
            apply ok_remove_middle_inv in HreachTmp;
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
            rewrite Hlist in IHvalid_execution_fragment at 1;
            rewrite substitute_notin_app in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Nat.eqb_refl in IHvalid_execution_fragment; auto;
            repeat rewrite get_r'_dist in IHvalid_execution_fragment; auto;
            repeat rewrite get_f'_dist in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto;
            rewrite Hlist in H1;
            simpl in *;
            repeat rewrite get_r'_dist in H1; auto;
            repeat rewrite get_f'_dist in H1; auto;
            simpl in *;
            intuition;
            inversion H3; subst; simpl in *;
            inversion H5; subst; simpl in *;
            inversion H7; subst; simpl in *;
            inversion H6; subst; simpl in *;
            try (inversion H9; subst; simpl in *);
            try (inversion H8; subst; simpl in *);
            apply notin_get_none in Hnotin_res;
            try (rewrite Hnotin_res in IHvalid_execution_fragment);
            intuition;

            try rewrite <-Hlist in *;
        try (destruct H8 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq Hb]]]]]]]]]]);
        try (destruct H10 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq Hb]]]]]]]]]]);
        try (destruct H11 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq Hb]]]]]]]]]]);
        exists s1, s2;
        eexists;
        exists acts2, pid0; intuition;
        [eapply composed_lts.valid_execution_fragment_join' with (a':=acts1);
        [eapply composed_lts.Step_Internal_Query;
        try (eapply composed_lts.Step_None; eauto); eauto
        |eauto|
        simpl; auto]|
        simpl;
        rewrite Hacts; auto|
            rewrite Heq;
            rewrite substitute_notin_app; auto;
            simpl in *;
            rewrite Nat.eqb_refl; auto;
            repeat rewrite get_r'_dist; auto;
            repeat rewrite get_f'_dist; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto]).


          all : apply binds_reconstruct in Hbinds0;
            destruct Hbinds0 as [l1 [l2 Hlist]];
            pose Hreach as HreachTmp;
            apply array_queue_wf_invarint in HreachTmp;
            unfold array_queue_wf in HreachTmp;
            simpl in HreachTmp;
            rewrite Hlist in HreachTmp;
            apply ok_remove_middle_inv in HreachTmp;
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
            rewrite Hlist in IHvalid_execution_fragment at 1;
            rewrite substitute_notin_app in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Nat.eqb_refl in IHvalid_execution_fragment; auto;
            repeat rewrite get_r'_dist in IHvalid_execution_fragment; auto;
            repeat rewrite get_f'_dist in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto;
            rewrite Hlist in H1;
            simpl in *;
            repeat rewrite get_r'_dist in H1; auto;
            repeat rewrite get_f'_dist in H1; auto;
            simpl in *;
            intuition;
            inversion H3; subst; simpl in *;
            inversion H5; subst; simpl in *;
            inversion H7; subst; simpl in *;
            inversion H6; subst; simpl in *;
            try (inversion H9; subst; simpl in *);
            try (inversion H8; subst; simpl in *);
            intuition;
            apply notin_get_none in Hnotin_res;
            rewrite Hnotin_res in IHvalid_execution_fragment;
            intuition;

        try (destruct H8 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq Hb]]]]]]]]]]);
        try (destruct H9 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq Hb]]]]]]]]]]);
        try (destruct H10 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq Hb]]]]]]]]]]);
        exists s1, s2;
        eexists;
        exists acts2, pid0; intuition;
        [eapply composed_lts.valid_execution_fragment_join' with (a':=acts1);
        [eapply composed_lts.Step_Internal_Query;
        try (eapply composed_lts.Step_None; eauto); eauto
        |eauto|
        simpl; auto]|
        simpl;
        rewrite Hacts; auto|
            rewrite Heq;
            rewrite substitute_notin_app; auto;
            simpl in *;
            rewrite Nat.eqb_refl; auto;
            repeat rewrite get_r'_dist; auto;
            repeat rewrite get_f'_dist; auto;
            simpl in *;
            rewrite Hnotin_res;
            repeat rewrite get_r'_dist; auto].
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Internal_Reply; eauto;
    eapply composed_lts.Step_None; eauto.
    specialize (IHvalid_execution_fragment Htmp).
    inversion H; subst; simpl in *.
    inversion H3; subst; simpl in *.
    unfold F, R in *; simpl in *.
    unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
    inversion H4; subst; simpl in *.

          all : try (apply binds_reconstruct in Hbinds0;
            destruct Hbinds0 as [l1 [l2 Hlist]];
            pose Hreach as HreachTmp;
            apply array_queue_wf_invarint in HreachTmp;
            unfold array_queue_wf in HreachTmp;
            simpl in HreachTmp;
            rewrite Hlist in HreachTmp;
            apply ok_remove_middle_inv in HreachTmp;
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
            apply ok_concat_inv in Hokl;
            destruct Hokl as [Hokl1 Hokl2];
            rewrite Hlist in IHvalid_execution_fragment at 1;
            rewrite substitute_notin_app in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Nat.eqb_refl in IHvalid_execution_fragment; auto;
            repeat rewrite get_r'_dist in IHvalid_execution_fragment; auto;
            repeat rewrite get_f'_dist in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto;
            rewrite Hlist in H1;
            simpl in *;
            repeat rewrite get_r'_dist in H1; auto;
            repeat rewrite get_f'_dist in H1; auto;
            simpl in *;
            intuition;
            inversion H2; subst; simpl in *;
            inversion H5; subst; simpl in *;
            inversion H7; subst; simpl in *;
            inversion H6; subst; simpl in *;
            try (inversion H9; subst; simpl in *);
            try (inversion H8; subst; simpl in *);
            try (unfold binds in Hbinds3);
            try (unfold binds in Hbinds5);
            try (rewrite Hbinds3 in IHvalid_execution_fragment; auto);
            try (rewrite Hbinds5 in IHvalid_execution_fragment; auto);
            try (rewrite get_r'_any_ary_remove in IHvalid_execution_fragment; auto);
            try (rewrite get_r'_any_rear_remove in IHvalid_execution_fragment; auto);
            intuition;
            try (rewrite get_r'_any_ary_remove in IHvalid_execution_fragment; auto);
            try (rewrite get_r'_any_rear_remove in IHvalid_execution_fragment; auto);
            apply IHvalid_execution_fragment in H1; auto;
            try rewrite <-Hlist in *;

        destruct H1 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq Hb]]]]]]]]]];
        exists s1, s2;
        eexists;
        exists acts2, pid0; intuition;
        [eapply composed_lts.valid_execution_fragment_join' with (a':=acts1);
        [eapply composed_lts.Step_Internal_Reply;
        try (eapply composed_lts.Step_None; eauto); eauto
        |eauto|
        simpl; auto] |
        simpl;
        rewrite Hacts; auto |
            rewrite Heq;
            rewrite substitute_notin_app; auto;
            simpl in *;
            rewrite Nat.eqb_refl; auto;
            repeat rewrite get_r'_dist; auto;
            repeat rewrite get_f'_dist; auto;
            simpl in *;
            (* rewrite Hlist; *)
            try (rewrite get_r'_any_ary_remove; auto);
            try (rewrite get_r'_any_ary_remove; auto);
            try (rewrite get_r'_any_rear_remove; auto);
            try (rewrite get_r'_any_rear_remove; auto)]).

          all : try (apply binds_reconstruct in Hbinds0;
            destruct Hbinds0 as [l1 [l2 Hlist]];
            pose Hreach as HreachTmp;
            apply array_queue_wf_invarint in HreachTmp;
            unfold array_queue_wf in HreachTmp;
            simpl in HreachTmp;
            rewrite Hlist in HreachTmp;
            apply ok_remove_middle_inv in HreachTmp;
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
            apply ok_concat_inv in Hokl;
            destruct Hokl as [Hokl1 Hokl2];
            rewrite Hlist in IHvalid_execution_fragment at 1;
            rewrite substitute_notin_app in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Nat.eqb_refl in IHvalid_execution_fragment; auto;
            repeat rewrite get_r'_dist in IHvalid_execution_fragment; auto;
            repeat rewrite get_f'_dist in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto;
            rewrite Hlist in H1;
            simpl in *;
            repeat rewrite get_r'_dist in H1; auto;
            repeat rewrite get_f'_dist in H1; auto;
            simpl in *;
            intuition;
            inversion H2; subst; simpl in *;
            inversion H5; subst; simpl in *;
            inversion H7; subst; simpl in *;
            inversion H6; subst; simpl in *;
            try (inversion H9; subst; simpl in *);
            try (inversion H8; subst; simpl in *);
            try (unfold binds in Hbinds3);
            try (unfold binds in Hbinds5);
            try (rewrite Hbinds3 in IHvalid_execution_fragment; auto);
            try (rewrite Hbinds5 in IHvalid_execution_fragment; auto);
            try (rewrite get_r'_any_ary_remove in IHvalid_execution_fragment; auto);
            try (rewrite get_r'_any_rear_remove in IHvalid_execution_fragment; auto);
            intuition;
            (* try (rewrite get_r'_any_ary_remove in IHvalid_execution_fragment; auto);
            try (rewrite get_r'_any_rear_remove in IHvalid_execution_fragment; auto);
            apply IHvalid_execution_fragment in H1; auto; *)
            try rewrite <-Hlist in *;

        try (destruct H10 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq Hb]]]]]]]]]]);
        try (destruct H9 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq Hb]]]]]]]]]]);
        try (destruct H8 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq Hb]]]]]]]]]]);
        exists s1, s2;
        eexists;
        exists acts2, pid0; intuition;
        [eapply composed_lts.valid_execution_fragment_join' with (a':=acts1);
        [eapply composed_lts.Step_Internal_Reply;
        try (eapply composed_lts.Step_None; eauto); eauto
        |eauto|
        simpl; auto] |
        simpl;
        rewrite Hacts; auto |
            rewrite Heq;
            rewrite substitute_notin_app; auto;
            simpl in *;
            rewrite Nat.eqb_refl; auto;
            repeat rewrite get_r'_dist; auto;
            repeat rewrite get_f'_dist; auto;
            simpl in *;
            (* rewrite Hlist; *)
            try (rewrite get_r'_any_ary_remove; auto);
            try (rewrite get_r'_any_ary_remove; auto);
            try (rewrite get_r'_any_rear_remove; auto);
            try (rewrite get_r'_any_rear_remove; auto)]).

          all : apply binds_reconstruct in Hbinds0;
            destruct Hbinds0 as [l1 [l2 Hlist]];
            pose Hreach as HreachTmp;
            apply array_queue_wf_invarint in HreachTmp;
            unfold array_queue_wf in HreachTmp;
            simpl in HreachTmp;
            rewrite Hlist in HreachTmp;
            apply ok_remove_middle_inv in HreachTmp;
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
            apply ok_concat_inv in Hokl;
            destruct Hokl as [Hokl1 Hokl2];
            rewrite Hlist in IHvalid_execution_fragment at 1;
            rewrite substitute_notin_app in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Nat.eqb_refl in IHvalid_execution_fragment; auto;
            repeat rewrite get_r'_dist in IHvalid_execution_fragment; auto;
            repeat rewrite get_f'_dist in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto;
            rewrite Hlist in H1;
            simpl in *;
            repeat rewrite get_r'_dist in H1; auto;
            repeat rewrite get_f'_dist in H1; auto;
            simpl in *;
            intuition;
            inversion H2; subst; simpl in *;
            inversion H5; subst; simpl in *;
            inversion H7; subst; simpl in *;
            inversion H6; subst; simpl in *;
            try (inversion H9; subst; simpl in *);
            try (inversion H8; subst; simpl in *);
            try (unfold binds in Hbinds3);
            try (unfold binds in Hbinds5);
            try (rewrite Hbinds3 in IHvalid_execution_fragment; auto);
            try (rewrite Hbinds5 in IHvalid_execution_fragment; auto);
            try (rewrite get_r'_any_ary_remove in IHvalid_execution_fragment; auto);
            try (rewrite get_r'_any_rear_remove in IHvalid_execution_fragment; auto);
            intuition;
            try (rewrite get_r'_any_ary_remove in IHvalid_execution_fragment; auto);
            try (rewrite get_r'_any_rear_remove in IHvalid_execution_fragment; auto);
            try (rewrite Hbinds3 in H1; auto);
            try (rewrite Hbinds5 in H1; auto);
            intuition;

        try (destruct H8 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq Hb]]]]]]]]]]);
        try (destruct H10 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq Hb]]]]]]]]]]);
        exists s1, s2;
        eexists;
        exists acts2, pid0; intuition;
        [eapply composed_lts.valid_execution_fragment_join' with (a':=acts1);
        [eapply composed_lts.Step_Internal_Reply;
        try (eapply composed_lts.Step_None; eauto); eauto
        |eauto|
        simpl; auto] |
        simpl;
        rewrite Hacts; auto |
            rewrite Heq;
            rewrite substitute_notin_app; auto;
            simpl in *;
            rewrite Nat.eqb_refl; auto;
            repeat rewrite get_r'_dist; auto;
            repeat rewrite get_f'_dist; auto;
            simpl in *;
            (* rewrite Hlist; *)
            try (rewrite get_r'_any_ary_remove; auto);
            try (rewrite get_r'_any_ary_remove; auto);
            try (rewrite get_r'_any_rear_remove; auto);
            try (rewrite get_r'_any_rear_remove; auto)];
            try (rewrite Hbinds3; auto);
            try (rewrite Hbinds5; auto).
Qed.

Lemma inv_R_increase_step_L1': forall (s s' : composed_lts.state (composed_array_queue L)) acts n
  (Hreach : composed_lts.reachable (composed_array_queue L) s),
  valid_execution_fragment_len' (composed_array_queue L)
    s s' acts n ->
  R s < R s' ->
  exists s1 s2 acts1 acts2 pid n1 n2,
    valid_execution_fragment_len' (composed_array_queue L)
      s s1 acts1 n1 /\
      composed_lts.step_L1
        (composed_array_queue L)
        s1 pid
          (@Tensor.intL1 li_array li_cnt_cnt (array L) ArrayQueue.front_rear
            int_ary_cas
            (* (@Tensor.intL2 li_counter li_counter counter counter (int_ary_cas)) *)
          )
        s2 /\
    valid_execution_fragment_len' (composed_array_queue L)
      s2 s' acts2 n2 /\
      acts = acts1 ++ acts2 /\
      R s1 = R s /\
      binds pid AEnq28 (get_pc s1) /\
      n = n1 + 1 + n2 /\
      R s2 = R s1 + 1.
Proof.
  induction 2; intros.
  - subst. lia.
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Internal_L1; eauto;
    eapply composed_lts.Step_None; eauto.
    rename IHvalid_execution_fragment_len' into IHvalid_execution_fragment.
    specialize (IHvalid_execution_fragment Htmp).
    inversion H; subst; simpl in *.
    inversion H2; subst; simpl in *.
    unfold F, R in *; simpl in *.
    unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
    inversion H3; subst; simpl in *.
    (* front_rear *)
    -- inversion H4; subst; simpl in *.
      inversion H5; subst; simpl in *.
      (* rear *)
      --- inversion H6; subst; simpl in *.
        inversion H7; subst; simpl in *.
        (* INC *)
        + pose proof Hreach as HreachTmp.
          apply inv_rear_inc_at_e31_invariant in Hreach.
          unfold inv_rear_inc_at_e31 in Hreach.
          apply Hreach in Hbinds5; auto.
          simpl in Hbinds5.
          apply binds_reconstruct in Hbinds5.
          destruct Hbinds5 as [l1 [l2 Hlist]].
          apply array_queue_wf_invarint in HreachTmp.
          unfold array_queue_wf in HreachTmp.
          simpl in HreachTmp.
          rewrite Hlist in HreachTmp.
          apply ok_remove_middle_inv in HreachTmp.
          destruct HreachTmp as [Hokl [Hnt1 Hnt2]].
          rewrite Hlist in H1, IHvalid_execution_fragment.
          repeat rewrite get_r'_dist in H1, IHvalid_execution_fragment; auto.
          repeat rewrite get_f'_dist in H1, IHvalid_execution_fragment; auto.
          simpl in *.
          apply notin_get_none in Hnotin_res.
          rewrite Hnotin_res in H1, IHvalid_execution_fragment.
          rewrite Nat.eqb_refl in IHvalid_execution_fragment.
          rewrite get_r'_any_rear_push in IHvalid_execution_fragment; auto.
          rewrite get_r'_any_rear_push in IHvalid_execution_fragment; auto.
          simpl in *.
          repeat rewrite Nat.add_succ_r in H1.
          intuition.
          rewrite Hlist.
          repeat rewrite get_r'_dist; auto.
          repeat rewrite get_f'_dist; auto.
          simpl.
          rewrite Hnotin_res.
          repeat rewrite Nat.add_succ_r; auto.

          destruct H10 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]].
          exists s1, s2, acts1, acts2, pid0, (1 + n1), n2. intuition.
          subst.
          eapply valid_execution_fragment_len'_join' with (a:=[]) (a':=acts1) (n := 1) (n' := n1).
          eapply Step_Internal_L1_len'.
          eauto.
          eapply Step_None_len'; eauto.
          eauto.
          simpl. auto.
          eauto.
          subst. lia.
        (* READ *)
        + rewrite get_r'_any_rear_read in IHvalid_execution_fragment; auto.
          intuition.
          destruct H8 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]].
          exists s1, s2, acts1, acts2, pid0, (1 + n1), n2. intuition.
          subst.
          eapply valid_execution_fragment_len'_join' with (a:=[]) (a':=acts1) (n := 1) (n' := n1).
          eapply Step_Internal_L1_len'.
          eauto.
          eapply Step_None_len'; eauto.
          eauto.
          simpl. auto.
          eauto.
          subst. lia.
      (* front *)
      --- intuition.
          destruct H7 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]].
          exists s1, s2, acts1, acts2, pid0, (1 + n1), n2. intuition.
          subst.
          eapply valid_execution_fragment_len'_join' with (a:=[]) (a':=acts1) (n := 1) (n' := n1).
          eapply Step_Internal_L1_len'.
          eauto.
          eapply Step_None_len'; eauto.
          eauto.
          simpl. auto.
          eauto.
          subst. lia.
    (* array *)
    -- inversion H4; subst; simpl in *.
      inversion H5; subst; simpl in *.
      (* CAS *)
      --- destruct ((entry_eqb (Vector.nth vec (Fin.of_nat_lt Hlt)) old)).
        (* success *)
        + pose proof Hreach as HreachTmp.
          apply inv_ary_cas_at_e28_d28_invariant in Hreach.
          unfold inv_ary_cas_at_e28_d28 in Hreach.
          apply Hreach in Hbinds3; auto.
          simpl in Hbinds3.
          destruct Hbinds3 as [Hb|Hb].
          (* e28 *)
          ++ pose proof Hb as HbindsTmp.
            apply binds_reconstruct in Hb.
            destruct Hb as [l1 [l2 Hlist]].
            pose proof HreachTmp as HreachTmp2.
            apply array_queue_wf_invarint in HreachTmp.
            unfold array_queue_wf in HreachTmp.
            simpl in HreachTmp.
            rewrite Hlist in HreachTmp.
            apply ok_remove_middle_inv in HreachTmp.
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]].
            rewrite Hlist in H1, IHvalid_execution_fragment.
            repeat rewrite get_r'_dist in H1, IHvalid_execution_fragment; auto.
            repeat rewrite get_f'_dist in H1, IHvalid_execution_fragment; auto.
            simpl in *.
            apply notin_get_none in Hnotin_res.
            rewrite Hnotin_res in H1, IHvalid_execution_fragment.
            rewrite Nat.eqb_refl in IHvalid_execution_fragment.
            rewrite get_r'_any_ary in IHvalid_execution_fragment; auto.
            rewrite get_r'_any_ary in IHvalid_execution_fragment; auto.
            simpl in *.
            repeat rewrite Nat.add_succ_r in H1.
            intuition.
            rewrite Hlist.
            repeat rewrite get_r'_dist; auto.
            repeat rewrite get_f'_dist; auto.
            simpl.
            rewrite Hnotin_res.
            repeat rewrite Nat.add_succ_r; auto.
            eapply R_not_decrease in Htmp; eauto.
            unfold F, R in *; simpl in *.
            unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
            rewrite Hlist in Htmp.
            repeat rewrite get_r'_dist in Htmp; auto.
            repeat rewrite get_f'_dist in Htmp; auto.
            simpl in *.
            rewrite Hnotin_res in Htmp.
            rewrite Nat.eqb_refl in Htmp.
            rewrite get_r'_any_ary in Htmp; auto.
            rewrite get_r'_any_ary in Htmp; auto.
            repeat rewrite Nat.add_succ_r in Htmp.
            repeat rewrite Nat.add_succ_r in IHvalid_execution_fragment.
            eexists.
            eexists.
            exists [].
            exists acts.
            exists pid.
            exists 0.
            exists n.
            intuition.
            eapply Step_None_len'; eauto.
            eauto.
            eauto.
            simpl.
            rewrite Hlist.
            repeat rewrite get_r'_dist; auto.
            repeat rewrite get_f'_dist; auto.
            simpl in *.
            rewrite Hnotin_res. auto.
            simpl.
            auto.
            simpl.
            rewrite Hlist.
            repeat rewrite get_r'_dist; auto.
            repeat rewrite get_f'_dist; auto.
            simpl.
            rewrite Hnotin_res.
            rewrite Nat.eqb_refl.
            rewrite get_r'_any_ary; auto.
            rewrite get_r'_any_ary; auto.
            lia.
            eapply valid_execution_fragment_len'_to_valid_execution_fragment; eauto.
          (* d28 *)
          ++ apply binds_reconstruct in Hb.
            destruct Hb as [l1 [l2 Hlist]].
            pose proof HreachTmp as HreachTmp2.
            apply array_queue_wf_invarint in HreachTmp.
            unfold array_queue_wf in HreachTmp.
            simpl in HreachTmp.
            rewrite Hlist in HreachTmp.
            apply ok_remove_middle_inv in HreachTmp.
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]].
            rewrite Hlist in H1, IHvalid_execution_fragment.
            repeat rewrite get_r'_dist in H1, IHvalid_execution_fragment; auto.
            repeat rewrite get_f'_dist in H1, IHvalid_execution_fragment; auto.
            simpl in *.
            apply notin_get_none in Hnotin_res.
            rewrite get_r'_any_ary in IHvalid_execution_fragment; auto.
            rewrite get_r'_any_ary in IHvalid_execution_fragment; auto.
            simpl in *.
            repeat rewrite Nat.add_succ_r in H1.
            intuition.
            rewrite Hlist.
            repeat rewrite get_r'_dist; auto.
            repeat rewrite get_f'_dist; auto.
            simpl.
            repeat rewrite Nat.add_succ_r; auto.
            destruct H8 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]].
            exists s1, s2, acts1, acts2, pid0, (1 + n1), n2. intuition.
            subst.
            eapply valid_execution_fragment_len'_join' with (a:=[]) (a':=acts1) (n := 1) (n' := n1).
            eapply Step_Internal_L1_len'.
            eauto.
            eapply Step_None_len'; eauto.
            eauto.
            simpl. auto.
            eauto.
            subst. lia.
        (* fail *)
        + rewrite get_r'_any_ary_cas_false in IHvalid_execution_fragment; auto.
          intuition.
            destruct H6 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]].
            exists s1, s2, acts1, acts2, pid0, (1 + n1), n2. intuition.
            subst.
            eapply valid_execution_fragment_len'_join' with (a:=[]) (a':=acts1) (n := 1) (n' := n1).
            eapply Step_Internal_L1_len'.
            eauto.
            eapply Step_None_len'; eauto.
            eauto.
            simpl. auto.
            eauto.
            subst. lia.
      (* READ *)
      --- rewrite get_r'_any_ary_read in IHvalid_execution_fragment; auto.
        intuition.
            destruct H6 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]].
            exists s1, s2, acts1, acts2, pid0, (1 + n1), n2. intuition.
            subst.
            eapply valid_execution_fragment_len'_join' with (a:=[]) (a':=acts1) (n := 1) (n' := n1).
            eapply Step_Internal_L1_len'.
            eauto.
            eapply Step_None_len'; eauto.
            eauto.
            simpl. auto.
            eauto.
            subst. lia.
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Internal_L2; eauto;
    eapply composed_lts.Step_None; eauto.
    rename IHvalid_execution_fragment_len' into IHvalid_execution_fragment.
    specialize (IHvalid_execution_fragment Htmp).
    inversion H; subst; simpl in *.
    inversion H2; subst; simpl in *.
    unfold F, R in *; simpl in *.
    unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
    inversion H3; subst; simpl in *.

          all : try (apply binds_reconstruct in Hbinds0;
            destruct Hbinds0 as [l1 [l2 Hlist]];
            pose Hreach as HreachTmp;
            apply array_queue_wf_invarint in HreachTmp;
            unfold array_queue_wf in HreachTmp;
            simpl in HreachTmp;
            rewrite Hlist in HreachTmp;
            apply ok_remove_middle_inv in HreachTmp;
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
            rewrite Hlist in IHvalid_execution_fragment at 1;
            rewrite substitute_notin_app in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Nat.eqb_refl in IHvalid_execution_fragment; auto;
            repeat rewrite get_r'_dist in IHvalid_execution_fragment; auto;
            repeat rewrite get_f'_dist in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto;
            rewrite Hlist in H1;
            simpl in *;
            repeat rewrite get_r'_dist in H1; auto;
            repeat rewrite get_f'_dist in H1; auto;
            simpl in *;
            intuition;
            try (destruct H4 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]]);
            try (destruct H5 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]]);
            exists s1, s2, ([] ++ acts1), acts2, pid0, (1 + n1), n2; intuition;
            (* try (destruct H4 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq Hb]]]]]]]]]]);
            try (destruct H5 as [s1 [s2 [acts1 [acts2 [pid0 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq Hb]]]]]]]]]]);
            exists s1, s2, acts1, acts2, pid0; intuition; auto; *)
            try rewrite <-Hlist in *;

            [eapply valid_execution_fragment_len'_join' with (a:=[]) (a':=acts1) (n:=1) (n':=n1);
            [eapply Step_Internal_L2_len';
            try (eapply Step_None_len'; eauto);
            eauto;
            eauto| eauto | simpl; auto | eauto]|
            rewrite Heq;
            rewrite Hlist;
            rewrite substitute_notin_app; auto;
            simpl in *;
            rewrite Nat.eqb_refl; auto;
            repeat rewrite get_r'_dist; auto;
            repeat rewrite get_f'_dist; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto|
            subst; lia]).
  - inversion H.
  - inversion H.
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Initial_Call; eauto;
    eapply composed_lts.Step_None; eauto.
    rename IHvalid_execution_fragment_len' into IHvalid_execution_fragment.
    specialize (IHvalid_execution_fragment Htmp).
    inversion H; subst; simpl in *.
    inversion H2; subst; simpl in *.
    unfold F, R in *; simpl in *.
    unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
    inversion H3; subst; simpl in *.
      intuition.
        try (destruct H4 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]]);
        exists s1, s2.
        eexists.
        exists acts2, pid0.
        exists (1 + n1), n2. intuition.
        eapply valid_execution_fragment_len'_join' with (a':=acts1).
        eapply Step_Initial_Call_len'.
        eauto.
        eapply Step_None_len'; eauto.
        eauto.
        simpl. auto.
        eauto.
        simpl.
        rewrite Hacts. auto.
        subst; lia.
      intuition.
        try (destruct H4 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]]);
        exists s1, s2.
        eexists.
        exists acts2, pid0.
        exists (1 + n1), n2. intuition.
        eapply valid_execution_fragment_len'_join' with (a':=acts1).
        eapply Step_Initial_Call_len'.
        eauto.
        eapply Step_None_len'; eauto.
        eauto.
        simpl. auto.
        eauto.
        simpl.
        rewrite Hacts. auto.
        subst; lia.
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Final_Return; eauto;
    eapply composed_lts.Step_None; eauto.
    rename IHvalid_execution_fragment_len' into IHvalid_execution_fragment.
    specialize (IHvalid_execution_fragment Htmp).
    inversion H; subst; simpl in *.
    inversion H2; subst; simpl in *.
    unfold F, R in *; simpl in *.
    unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
    inversion H3; subst; simpl in *;
      intuition;

          apply binds_reconstruct in Hbinds0;
            destruct Hbinds0 as [l1 [l2 Hlist]];
            pose Hreach as HreachTmp;
            apply array_queue_wf_invarint in HreachTmp;
            unfold array_queue_wf in HreachTmp;
            simpl in HreachTmp;
            rewrite Hlist in HreachTmp;
            apply ok_remove_middle_inv in HreachTmp;
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
            rewrite Hlist in IHvalid_execution_fragment at 1;
            rewrite remove_notin_app in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Nat.eqb_refl in IHvalid_execution_fragment; auto;
            repeat rewrite get_r'_dist in IHvalid_execution_fragment; auto;
            repeat rewrite get_f'_dist in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto;
            rewrite Hlist in H1;
            simpl in *;
            repeat rewrite get_r'_dist in H1; auto;
            repeat rewrite get_f'_dist in H1; auto;
            simpl in *;
            intuition;
            try rewrite <-Hlist in *.
        try (destruct H4 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]]);
        exists s1, s2.
        eexists.
        exists acts2, pid0.
        exists (1 + n1), n2. intuition.
        eapply valid_execution_fragment_len'_join' with (a':=acts1).
        eapply Step_Final_Return_len'.
        eauto.
        eapply Step_None_len'; eauto.
        eauto.
        simpl. auto.
        eauto.
        simpl.
        rewrite Hacts. auto.
            rewrite Heq;
            rewrite Hlist;
            rewrite remove_notin_app; auto;
            simpl in *;
            rewrite Nat.eqb_refl; auto;
            repeat rewrite get_r'_dist; auto;
            repeat rewrite get_f'_dist; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto.
        subst; lia.

        try (destruct H5 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]]);
        exists s1, s2.
        eexists.
        exists acts2, pid0.
        exists (1 + n1), n2. intuition.
        eapply valid_execution_fragment_len'_join' with (a':=acts1).
        eapply Step_Final_Return_len'.
        eauto.
        eapply Step_None_len'; eauto.
        eauto.
        simpl. auto.
        eauto.
        simpl.
        rewrite Hacts. auto.
            rewrite Heq;
            rewrite Hlist;
            rewrite remove_notin_app; auto;
            simpl in *;
            rewrite Nat.eqb_refl; auto;
            repeat rewrite get_r'_dist; auto;
            repeat rewrite get_f'_dist; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto.
        subst; lia.
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Internal_Query; eauto;
    eapply composed_lts.Step_None; eauto.
    rename IHvalid_execution_fragment_len' into IHvalid_execution_fragment.
    specialize (IHvalid_execution_fragment Htmp).
    inversion H; subst; simpl in *.
    inversion H2; subst; simpl in *.
    unfold F, R in *; simpl in *.
    unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
    inversion H4; subst; simpl in *.

          all : try (apply binds_reconstruct in Hbinds0;
            destruct Hbinds0 as [l1 [l2 Hlist]];
            pose Hreach as HreachTmp;
            apply array_queue_wf_invarint in HreachTmp;
            unfold array_queue_wf in HreachTmp;
            simpl in HreachTmp;
            rewrite Hlist in HreachTmp;
            apply ok_remove_middle_inv in HreachTmp;
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
            rewrite Hlist in IHvalid_execution_fragment at 1;
            rewrite substitute_notin_app in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Nat.eqb_refl in IHvalid_execution_fragment; auto;
            repeat rewrite get_r'_dist in IHvalid_execution_fragment; auto;
            repeat rewrite get_f'_dist in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto;
            rewrite Hlist in H1;
            simpl in *;
            repeat rewrite get_r'_dist in H1; auto;
            repeat rewrite get_f'_dist in H1; auto;
            simpl in *;
            intuition;
            inversion H3; subst; simpl in *;
            inversion H5; subst; simpl in *;
            inversion H7; subst; simpl in *;
            inversion H6; subst; simpl in *;
            try (inversion H9; subst; simpl in *);
            try (inversion H8; subst; simpl in *);
            apply notin_get_none in Hnotin_res;
            try (rewrite Hnotin_res in IHvalid_execution_fragment);
            intuition;

            try rewrite <-Hlist in *;



        try (destruct H8 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]]);
        try (destruct H10 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]]);
        try (destruct H11 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]]);
        exists s1, s2;
        eexists;
        exists acts2, pid0;
        exists (1 + n1), n2; intuition;

            [
              eapply valid_execution_fragment_len'_join' with (a':=acts1) (n:=1) (n':=n1);
            [eapply Step_Internal_Query_len';
            try (eapply Step_None_len'; eauto);
            eauto;
            eauto| eauto | simpl; auto | eauto]|
            simpl; subst; auto|
            rewrite Heq;
            (* rewrite Hlist; *)
            rewrite substitute_notin_app; auto;
            simpl in *;
            rewrite Nat.eqb_refl; auto;
            repeat rewrite get_r'_dist; auto;
            repeat rewrite get_f'_dist; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto|
            subst; lia]).

          all : try (apply binds_reconstruct in Hbinds0;
            destruct Hbinds0 as [l1 [l2 Hlist]];
            pose Hreach as HreachTmp;
            apply array_queue_wf_invarint in HreachTmp;
            unfold array_queue_wf in HreachTmp;
            simpl in HreachTmp;
            rewrite Hlist in HreachTmp;
            apply ok_remove_middle_inv in HreachTmp;
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
            rewrite Hlist in IHvalid_execution_fragment at 1;
            rewrite substitute_notin_app in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Nat.eqb_refl in IHvalid_execution_fragment; auto;
            repeat rewrite get_r'_dist in IHvalid_execution_fragment; auto;
            repeat rewrite get_f'_dist in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto;
            rewrite Hlist in H1;
            simpl in *;
            repeat rewrite get_r'_dist in H1; auto;
            repeat rewrite get_f'_dist in H1; auto;
            simpl in *;
            intuition;
            inversion H3; subst; simpl in *;
            inversion H5; subst; simpl in *;
            inversion H7; subst; simpl in *;
            inversion H6; subst; simpl in *;
            try (inversion H9; subst; simpl in *);
            try (inversion H8; subst; simpl in *);
            intuition;
            apply notin_get_none in Hnotin_res;
            try (rewrite Hnotin_res in IHvalid_execution_fragment);
            intuition;

        try (destruct H8 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]]);
        try (destruct H10 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]]);
        try (destruct H11 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]]);
        exists s1, s2;
        eexists;
        exists acts2, pid0;
        exists (1 + n1), n2; intuition;

            [
              eapply valid_execution_fragment_len'_join' with (a':=acts1) (n:=1) (n':=n1);
            [eapply Step_Internal_Query_len';
            try (eapply Step_None_len'; eauto);
            eauto;
            eauto| eauto | simpl; auto | eauto]|
            simpl; subst; auto|
            rewrite Heq;
            (* rewrite Hlist; *)
            rewrite substitute_notin_app; auto;
            simpl in *;
            rewrite Nat.eqb_refl; auto;
            repeat rewrite get_r'_dist; auto;
            repeat rewrite get_f'_dist; auto;
            simpl in *;
            rewrite Hnotin_res;
            repeat rewrite get_r'_dist; auto|
            subst; lia]).
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Internal_Reply; eauto;
    eapply composed_lts.Step_None; eauto.
    rename IHvalid_execution_fragment_len' into IHvalid_execution_fragment.
    specialize (IHvalid_execution_fragment Htmp).
    inversion H; subst; simpl in *.
    inversion H3; subst; simpl in *.
    unfold F, R in *; simpl in *.
    unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
    inversion H4; subst; simpl in *.

          all : try (apply binds_reconstruct in Hbinds0;
            destruct Hbinds0 as [l1 [l2 Hlist]];
            pose Hreach as HreachTmp;
            apply array_queue_wf_invarint in HreachTmp;
            unfold array_queue_wf in HreachTmp;
            simpl in HreachTmp;
            rewrite Hlist in HreachTmp;
            apply ok_remove_middle_inv in HreachTmp;
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
            apply ok_concat_inv in Hokl;
            destruct Hokl as [Hokl1 Hokl2];
            rewrite Hlist in IHvalid_execution_fragment at 1;
            rewrite substitute_notin_app in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Nat.eqb_refl in IHvalid_execution_fragment; auto;
            repeat rewrite get_r'_dist in IHvalid_execution_fragment; auto;
            repeat rewrite get_f'_dist in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto;
            rewrite Hlist in H1;
            simpl in *;
            repeat rewrite get_r'_dist in H1; auto;
            repeat rewrite get_f'_dist in H1; auto;
            simpl in *;
            intuition;
            inversion H2; subst; simpl in *;
            inversion H5; subst; simpl in *;
            inversion H7; subst; simpl in *;
            inversion H6; subst; simpl in *;
            try (inversion H9; subst; simpl in *);
            try (inversion H8; subst; simpl in *);
            try (unfold binds in Hbinds3);
            try (unfold binds in Hbinds5);
            try (rewrite Hbinds3 in IHvalid_execution_fragment; auto);
            try (rewrite Hbinds5 in IHvalid_execution_fragment; auto);
            try (rewrite get_r'_any_ary_remove in IHvalid_execution_fragment; auto);
            try (rewrite get_r'_any_rear_remove in IHvalid_execution_fragment; auto);
            intuition;
            try (rewrite get_r'_any_ary_remove in IHvalid_execution_fragment; auto);
            try (rewrite get_r'_any_rear_remove in IHvalid_execution_fragment; auto);
            apply IHvalid_execution_fragment in H1; auto;
            try rewrite <-Hlist in *;

        destruct H1 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]];
        exists s1, s2;
        eexists;
        exists acts2, pid0;
        exists (1 + n1), n2; intuition;
            [
              eapply valid_execution_fragment_len'_join' with (a':=acts1) (n:=1) (n':=n1);
            [eapply Step_Internal_Reply_len';
            try (eapply Step_None_len'; eauto);
            eauto;
            eauto| eauto | simpl; auto | eauto]|
            simpl; subst; auto|
            rewrite Heq;
            rewrite substitute_notin_app; auto;
            simpl in *;
            rewrite Nat.eqb_refl; auto;
            repeat rewrite get_r'_dist; auto;
            repeat rewrite get_f'_dist; auto;
            simpl in *;
            try (rewrite get_r'_any_ary_remove; auto);
            try (rewrite get_r'_any_ary_remove; auto);
            try (rewrite get_r'_any_rear_remove; auto);
            try (rewrite get_r'_any_rear_remove; auto)|
            subst; lia]).

          all : try (apply binds_reconstruct in Hbinds0;
            destruct Hbinds0 as [l1 [l2 Hlist]];
            pose Hreach as HreachTmp;
            apply array_queue_wf_invarint in HreachTmp;
            unfold array_queue_wf in HreachTmp;
            simpl in HreachTmp;
            rewrite Hlist in HreachTmp;
            apply ok_remove_middle_inv in HreachTmp;
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
            apply ok_concat_inv in Hokl;
            destruct Hokl as [Hokl1 Hokl2];
            rewrite Hlist in IHvalid_execution_fragment at 1;
            rewrite substitute_notin_app in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Nat.eqb_refl in IHvalid_execution_fragment; auto;
            repeat rewrite get_r'_dist in IHvalid_execution_fragment; auto;
            repeat rewrite get_f'_dist in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto;
            rewrite Hlist in H1;
            simpl in *;
            repeat rewrite get_r'_dist in H1; auto;
            repeat rewrite get_f'_dist in H1; auto;
            simpl in *;
            intuition;
            inversion H2; subst; simpl in *;
            inversion H5; subst; simpl in *;
            inversion H7; subst; simpl in *;
            inversion H6; subst; simpl in *;
            try (inversion H9; subst; simpl in *);
            try (inversion H8; subst; simpl in *);
            try (unfold binds in Hbinds3);
            try (unfold binds in Hbinds5);
            try (rewrite Hbinds3 in IHvalid_execution_fragment; auto);
            try (rewrite Hbinds5 in IHvalid_execution_fragment; auto);
            try (rewrite get_r'_any_ary_remove in IHvalid_execution_fragment; auto);
            try (rewrite get_r'_any_rear_remove in IHvalid_execution_fragment; auto);
            intuition;
            (* try (rewrite get_r'_any_ary_remove in IHvalid_execution_fragment; auto);
            try (rewrite get_r'_any_rear_remove in IHvalid_execution_fragment; auto);
            apply IHvalid_execution_fragment in H1; auto; *)
            try rewrite <-Hlist in *;

        try (destruct H10 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]]);
        try (destruct H9 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]]);
        try (destruct H8 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]]);
        exists s1, s2;
        eexists;
        exists acts2, pid0;
        exists (1 + n1), n2; intuition;
            [
              eapply valid_execution_fragment_len'_join' with (a':=acts1) (n:=1) (n':=n1);
            [eapply Step_Internal_Reply_len';
            try (eapply Step_None_len'; eauto);
            eauto;
            eauto| eauto | simpl; auto | eauto]|
            simpl; subst; auto|
            rewrite Heq;
            rewrite substitute_notin_app; auto;
            simpl in *;
            rewrite Nat.eqb_refl; auto;
            repeat rewrite get_r'_dist; auto;
            repeat rewrite get_f'_dist; auto;
            simpl in *;
            try (rewrite get_r'_any_ary_remove; auto);
            try (rewrite get_r'_any_ary_remove; auto);
            try (rewrite get_r'_any_rear_remove; auto);
            try (rewrite get_r'_any_rear_remove; auto)|
            subst; lia]).

          all : apply binds_reconstruct in Hbinds0;
            destruct Hbinds0 as [l1 [l2 Hlist]];
            pose Hreach as HreachTmp;
            apply array_queue_wf_invarint in HreachTmp;
            unfold array_queue_wf in HreachTmp;
            simpl in HreachTmp;
            rewrite Hlist in HreachTmp;
            apply ok_remove_middle_inv in HreachTmp;
            destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
            apply ok_concat_inv in Hokl;
            destruct Hokl as [Hokl1 Hokl2];
            rewrite Hlist in IHvalid_execution_fragment at 1;
            rewrite substitute_notin_app in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Nat.eqb_refl in IHvalid_execution_fragment; auto;
            repeat rewrite get_r'_dist in IHvalid_execution_fragment; auto;
            repeat rewrite get_f'_dist in IHvalid_execution_fragment; auto;
            simpl in *;
            rewrite Hlist;
            repeat rewrite get_r'_dist; auto;
            rewrite Hlist in H1;
            simpl in *;
            repeat rewrite get_r'_dist in H1; auto;
            repeat rewrite get_f'_dist in H1; auto;
            simpl in *;
            intuition;
            inversion H2; subst; simpl in *;
            inversion H5; subst; simpl in *;
            inversion H7; subst; simpl in *;
            inversion H6; subst; simpl in *;
            try (inversion H9; subst; simpl in *);
            try (inversion H8; subst; simpl in *);
            try (unfold binds in Hbinds3);
            try (unfold binds in Hbinds5);
            try (rewrite Hbinds3 in IHvalid_execution_fragment; auto);
            try (rewrite Hbinds5 in IHvalid_execution_fragment; auto);
            try (rewrite get_r'_any_ary_remove in IHvalid_execution_fragment; auto);
            try (rewrite get_r'_any_rear_remove in IHvalid_execution_fragment; auto);
            intuition;
            try (rewrite get_r'_any_ary_remove in IHvalid_execution_fragment; auto);
            try (rewrite get_r'_any_rear_remove in IHvalid_execution_fragment; auto);
            try (rewrite Hbinds3 in H1; auto);
            try (rewrite Hbinds5 in H1; auto);
            intuition;

        try (destruct H10 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]]);
        try (destruct H9 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]]);
        try (destruct H8 as [s1 [s2 [acts1 [acts2 [pid0 [n1 [n2 [Hvalid1 [Hstep [Hvalid2 [Hacts [Heq [Hb Heq']]]]]]]]]]]]]);
        exists s1, s2;
        eexists;
        exists acts2, pid0;
        exists (1 + n1), n2; intuition;
            [
              eapply valid_execution_fragment_len'_join' with (a':=acts1) (n:=1) (n':=n1);
            [eapply Step_Internal_Reply_len';
            try (eapply Step_None_len'; eauto);
            eauto;
            eauto| eauto | simpl; auto | eauto]|
            simpl; subst; auto|
            rewrite Heq;
            rewrite substitute_notin_app; auto;
            simpl in *;
            rewrite Nat.eqb_refl; auto;
            repeat rewrite get_r'_dist; auto;
            repeat rewrite get_f'_dist; auto;
            simpl in *;
            try (rewrite get_r'_any_ary_remove; auto);
            try (rewrite get_r'_any_ary_remove; auto);
            try (rewrite get_r'_any_rear_remove; auto);
            try (rewrite get_r'_any_rear_remove; auto)|
            subst; lia];
            try (rewrite Hbinds3; auto);
            try (rewrite Hbinds5; auto).
Qed.

End test.
