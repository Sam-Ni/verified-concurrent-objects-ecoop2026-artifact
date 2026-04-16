Require Import
  List
  Arith
  LibVar
  LibEnv
  LTS
  Refinement
  SyncLTS
  Compose
  Array
  ArraySC
  VerifiedConcurrentObject
  HComp
  ArrayQueueInvariant
  ArrayQueueInvariantBefore
  Identity.
Import ListNotations.

Section VerfiedArray.

Variable N: nat.

Definition buffer_map
  (req: LibEnv.env Array_query)
  (res: LibEnv.env Array_reply)
  (buffer: LibEnv.env (id_state li_array))
  (req': LibEnv.env Array_query)
  (res': LibEnv.env Array_reply) :=
  forall pid,
    (forall (q : query li_array),
    (binds pid q req \/ binds pid (GetQuery q) buffer
      -> binds pid q req')) /\
    (forall (r : reply li_array),
    (binds pid r res \/ binds pid (GetReply r) buffer
      -> binds pid r res')) /\
    (pid # buffer -> pid # req') /\
    (pid # buffer -> pid # res').

Definition buffer_inv
  (req: LibEnv.env Array_query)
  (res: LibEnv.env Array_reply)
  (buffer: LibEnv.env (id_state li_array)) :=
  forall pid,
    (pid # buffer ->
      pid # req /\ pid # res) /\
    (forall q,
      binds pid q req -> binds pid Pending buffer) /\
    (forall r,
      binds pid r res -> binds pid Pending buffer).

Definition thread_state_map' (pc : LibEnv.env Position) h :=
  forall pid,
  (forall p, (binds pid p pc -> binds pid Run h)) /\
  (pid # pc -> pid # h).

Definition sync_array_wf (y : state (SyncLTS.sync (array N))) :=
  ok (y.(PidPos)) /\
  ok (y.(LState).(requests N)) /\
  ok (y.(LState).(responses N)).

Definition req_res_mutual 
  (req: LibEnv.env Array_query)
  (res: LibEnv.env Array_reply) :=
  forall pid,
  (forall q, binds pid q req -> pid # res) /\
  (forall r, binds pid r res -> pid # req).

Definition req_res_pos_inv
  (req: LibEnv.env Array_query)
  (res: LibEnv.env Array_reply)
  (h : LibEnv.env Position) :=
  forall pid,
  pid # h -> pid # req /\ pid # res.

Lemma verified_array:
  veriobj (array N) (identity li_array) (array N).
Proof.
  unfold veriobj.
  intuition.
  apply array_is_sc.
  apply identity_is_sc.
  eapply forward_simulation_inv_ind
    with (f:=fun (x : state (linked_lts
     (Compose.compose (array N) (identity li_array)))) (y : state (SyncLTS.sync (array N))) =>
      x.(L1State).(LState).(vec N) = y.(LState).(vec N) /\
      buffer_map
        (x.(L1State).(LState).(requests N))
        (x.(L1State).(LState).(responses N))
        (x.(L2State).(LState).(buffer))
        (y.(LState).(requests N))
        (y.(LState).(responses N)) /\
      (* x = y.(LState) /\ *)
      thread_state_map' x.(L2State).(PidPos) y.(PidPos) /\
      sync_array_wf y /\
      buffer_inv
        (x.(L1State).(LState).(requests N))
        (x.(L1State).(LState).(responses N))
        (x.(L2State).(LState).(buffer)) /\
      req_res_mutual
        (y.(LState).(requests N))
        (y.(LState).(responses N)) /\
      req_res_pos_inv
        (x.(L1State).(LState).(requests N))
        (x.(L1State).(LState).(responses N))
        (x.(L1State).(PidPos)) /\
      req_res_mutual
        (x.(L1State).(LState).(requests N))
        (x.(L1State).(LState).(responses N))
      )
      (inv:=fun x => True).
  unfold fsim_properties_inv_ind. intuition.
  - unfold invariant_ind. intuition.
  - inversion H; subst; simpl in *.
    inversion H0; subst; simpl in *.
    inversion H1; subst; simpl in *.
    exists (mkSyncState (array N)
      (new_array N) []).
    inversion H2; subst; simpl in *.
    inversion H4; subst; simpl in *.
    rewrite H2.
    rewrite H4.
    simpl in *.
    unfold sync_new_state.
    simpl. intuition.
    unfold array_new_state. intuition.
    unfold buffer_map.
    intuition; inversion H9.
    unfold thread_state_map'.
    rewrite H5.
    intuition. inversion H6.
    unfold sync_array_wf.
    simpl. intuition;
    econstructor.
    unfold buffer_inv.
    intuition; inversion H6.
    unfold req_res_mutual.
    intuition; inversion H6.
    unfold req_res_pos_inv.
    intuition;
    apply notin_empty; auto.
    unfold req_res_mutual.
    intuition; inversion H6.
  - rename H2 into Hvec.
    rename H0 into Hmap_buffer.
    rename H3 into Hmap.
    rename H4 into Hwf.
    rename H5 into Hmap_buffer_inv.
    rename H6 into Hmutual.
    rename H7 into Hmutual_inv.
    rename H9 into Hmutual'.
    inversion H1; subst; simpl in *.
    exists (
      mkSyncState (array N)
        (mkAryState N
          ((pid, qb)::(s2).(LState).(requests N))
          (s2.(LState).(responses N))
          (s2.(LState).(vec N))
        )
        ((pid, Run)::(PidPos s2))
    ).
    inversion H0; subst; simpl in *.
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_initial_state_L with (pos:=PidPos); eauto.
      apply Hwf; auto.
      unfold thread_state_map' in *.
      apply Hmap; auto.
      inversion H2; subst; simpl in *; auto.
      simpl.
      inversion H2; subst; simpl in *; auto.
      destruct qb.
        eapply array_initial_state_cas; eauto.
        apply Hmap_buffer; auto.
        apply Hmap_buffer; auto.
        apply Hwf; auto.
        apply Hwf; auto.
        destruct LState. simpl in *.
        subst. auto.
        eapply array_initial_state_read; eauto.
        apply Hmap_buffer; auto.
        apply Hmap_buffer; auto.
        apply Hwf; auto.
        apply Hwf; auto.
        destruct LState. simpl in *.
        subst. auto.
      unfold buffer_map.
      inversion H2; subst; simpl in *.
      intuition.
      assert (Hneq: pid0 <> pid).
        intro. subst.
        apply Hmap_buffer_inv in Hnotin_buffer; auto.
        apply binds_in in H4; auto.
        unfold "#" in Hnotin_buffer; intuition.
      apply binds_push_neq; auto.
      apply Hmap_buffer; auto.
      apply binds_push_inv in H4.
      intuition.
        subst. inversion H5; subst; simpl in *.
        apply binds_push_eq; auto.
        apply binds_push_neq; auto.
        apply Hmap_buffer; auto.
      apply Hmap_buffer; auto.
      apply binds_push_inv in H4.
      intuition.
        subst. discriminate.
        apply Hmap_buffer; auto.
      apply notin_union in H3.
      apply notin_union.
      intuition.
      apply Hmap_buffer; auto.
      apply notin_union in H3.
      intuition.
      apply Hmap_buffer; auto.
      unfold thread_state_map'.
      inversion H2; subst; simpl in *.
      intuition.
      apply binds_push_inv in H3; auto.
      intuition.
        subst. apply binds_push_eq; auto.
        apply binds_push_neq; auto.
        eapply Hmap; eauto.
      apply notin_union in H3.
      apply notin_union.
      intuition.
      eapply Hmap; eauto.
      unfold sync_array_wf.
      simpl. intuition.
      econstructor; eauto.
      apply Hwf; auto.
      inversion H2; subst; simpl in *.
      apply Hmap; auto.
      econstructor; eauto.
      apply Hwf; auto.
      inversion H2; subst; simpl in *.
      apply Hmap_buffer; auto.
      apply Hwf; auto.
      unfold buffer_inv.
      inversion H2; subst; simpl in *.
      simpl. intuition.
      apply notin_union in H3; auto.
      intuition.
      apply Hmap_buffer_inv; auto.
      apply notin_union in H3; auto.
      intuition.
      apply Hmap_buffer_inv; auto.
      assert (Hneq: pid0 <> pid).
        intro. subst.
        apply Hmap_buffer_inv in Hnotin_buffer.
        apply binds_in in H3.
        unfold "#" in Hnotin_buffer; intuition.
      apply binds_push_neq; auto.
        apply Hmap_buffer_inv in H3; auto.
      assert (Hneq: pid0 <> pid).
        intro. subst.
        apply Hmap_buffer_inv in Hnotin_buffer.
        apply binds_in in H3.
        unfold "#" in Hnotin_buffer; intuition.
      apply binds_push_neq; auto.
        apply Hmap_buffer_inv in H3; auto.
      unfold req_res_mutual.
      simpl.
      intuition.
      apply binds_push_inv in H3; auto.
      intuition.
        subst.
        apply Hmap_buffer; auto.
        inversion H2; subst; simpl in *; auto.
        eapply Hmutual; eauto.
      apply notin_union.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply binds_in in H3.
        inversion H2; subst; simpl in *.
        apply Hmap_buffer in Hnotin_buffer; auto.
        unfold "#" in Hnotin_buffer; intuition.
        intuition.
        apply notin_neq; auto.
        eapply Hmutual; eauto.
  - rename H2 into Hvec.
    rename H0 into Hmap_buffer.
    rename H3 into Hmap.
    rename H4 into Hwf.
    rename H5 into Hmap_buffer_inv.
    rename H6 into Hmutual.
    rename H7 into Hmutual_inv.
    rename H9 into Hmutual'.
    inversion H1; subst; simpl in *.
    exists (
      mkSyncState (array N)
        (mkAryState N
          ((s2).(LState).(requests N))
          (remove (s2).(LState).(responses N) pid)
          (s2.(LState).(vec N))
        )
        (remove (PidPos s2) pid)
    ).
    inversion H0; subst; simpl in *.
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_final_state_L with (pos:=PidPos); eauto.
      apply Hwf; auto.
      unfold thread_state_map' in *.
      apply Hmap in Hbinds; auto.
      inversion H2; subst; simpl in *; auto.
      simpl.
      destruct rb.
        eapply array_final_state_cas; eauto.
        apply Hwf; auto.
        apply Hwf; auto.
        apply Hmap_buffer; auto.
        destruct LState. simpl in *.
        subst. auto.
        eapply array_final_state_read; eauto.
        apply Hwf; auto.
        apply Hwf; auto.
        apply Hmap_buffer; auto.
        destruct LState. simpl in *.
        subst. auto.
      unfold buffer_map.
      inversion H2; subst; simpl in *.
      intuition.
      apply Hmap_buffer; auto.
      assert (Hneq: pid0 <> pid).
        intro. subst.
        assert (pid # (remove buffer pid)).
        apply ok_remove_notin; auto.
        apply binds_in in H4.
        unfold "#" in H3; intuition.
      apply remove_preserves_binds_notin in H4; auto.
      apply Hmap_buffer; auto.
      assert (Hneq: pid0 <> pid).
        intro. subst.
        apply Hmap_buffer_inv in H4; auto.
        unfold binds in Hbinds0.
        rewrite H4 in Hbinds0.
        discriminate.
      apply remove_neq_preserves_binds; auto.
      apply Hmap_buffer; auto.
      assert (Hneq: pid0 <> pid).
        intro. subst.
        assert (pid # (remove buffer pid)).
        apply ok_remove_notin; auto.
        apply binds_in in H4.
        unfold "#" in H3; intuition.
      apply remove_preserves_binds_notin in H4; auto.
      apply remove_neq_preserves_binds; auto.
      apply Hmap_buffer; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        eapply Hmutual; eauto.
        eapply Hmap_buffer; eauto.
        apply remove_neq_preserves_notin in H3; auto.
        apply Hmap_buffer; auto.
      destruct (eq_nat_dec pid0 pid).
        subst. apply ok_remove_notin; auto.
        apply Hwf; auto.
        apply remove_preserves_notin; auto.
        apply remove_neq_preserves_notin in H3; auto.
        apply Hmap_buffer; auto.
      unfold thread_state_map'.
      inversion H2; subst; simpl in *.
      simpl. intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove pos pid))
        by (apply ok_remove_notin; auto).
        apply binds_in in H3.
        unfold "#" in H4; intuition.
        apply remove_neq_preserves_binds; auto.
        apply remove_preserves_binds_notin in H3; auto.
        eapply Hmap; eauto.
      destruct (eq_nat_dec pid0 pid).
        subst. apply ok_remove_notin; auto.
        apply Hwf; auto.
        apply remove_preserves_notin; auto.
        apply remove_neq_preserves_notin in H3; auto.
        apply Hmap; auto.
      unfold sync_array_wf. simpl.
      intuition.
      apply remove_preserves_ok; auto.
      apply Hwf; auto.
      apply Hwf; auto.
      apply remove_preserves_ok; auto.
      apply Hwf; auto.
      unfold buffer_inv.
      inversion H2; subst; simpl in *.
      simpl.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmutual_inv; auto.
        apply remove_neq_preserves_notin in H3; auto.
        apply Hmap_buffer_inv; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hmutual_inv; auto.
        apply remove_neq_preserves_notin in H3; auto.
        apply Hmap_buffer_inv; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply binds_in in H3.
        apply Hmutual_inv in Hnotin; auto.
        unfold "#" in Hnotin; intuition.
        apply remove_neq_preserves_binds; auto.
        eapply Hmap_buffer_inv in H3; eauto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply binds_in in H3.
        apply Hmutual_inv in Hnotin; auto.
        unfold "#" in Hnotin; intuition.
        apply remove_neq_preserves_binds; auto.
        eapply Hmap_buffer_inv in H3; eauto.
      unfold req_res_mutual.
      simpl. intuition.
      destruct (eq_nat_dec pid0 pid).
        subst. apply ok_remove_notin; auto.
        apply Hwf; auto.
        apply remove_preserves_notin; auto.
        eapply Hmutual; eauto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove (responses N (LState s2)) pid)).
        apply ok_remove_notin; auto.
        apply Hwf; auto.
        unfold "#" in H4.
        apply binds_in in H3.
        intuition.
        apply remove_preserves_binds_notin in H3; auto.
        eapply Hmutual; eauto.
  - rename H2 into Hvec.
    rename H0 into Hmap_buffer.
    rename H3 into Hmap.
    rename H4 into Hwf.
    rename H5 into Hmap_buffer_inv.
    rename H6 into Hmutual.
    rename H7 into Hmutual_inv.
    rename H9 into Hmutual'.
    inversion H1; subst; simpl in *.
    (* step of identity *)
    --
    inversion H0; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3.
    (* step of array *)
    --
    inversion H0; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    (* cas *)
    ---
    exists (
      mkSyncState (array N)
        (mkAryState N
          (remove (s2).(LState).(requests N) pid)
          ((pid, AryCASOk (entry_eqb (Vector.nth vec (Fin.of_nat_lt Hlt)) old)) :: (s2).(LState).(responses N))
          (if
                    entry_eqb (Vector.nth vec (Fin.of_nat_lt Hlt))
                      old
                   then Vector.replace vec (Fin.of_nat_lt Hlt) new
                   else vec)
        )
        (PidPos s2)
    ).
    simpl. intuition.
      destruct s2. simpl in *.
      destruct LState; simpl in *.
      subst.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos).
      apply Hwf; auto.
      eapply Hmap; eauto.
      2: {
        eauto.
      }
      2: {
        eauto.
      }
      simpl.
      eapply array_step_cas.
      5 : { eauto. }
      6 : { eauto. }
      apply Hwf; auto.
      apply Hwf; auto.
      eapply Hmap_buffer; eauto.
      eapply Hmutual; eauto.
      eapply Hmap_buffer; eauto.
      eauto.
    unfold buffer_map.
    simpl. intuition.
    destruct (eq_nat_dec pid0 pid).
      subst.
      assert (pid # (remove inv pid)).
      apply ok_remove_notin; auto.
      apply binds_in in H5.
      unfold "#" in H4; intuition.
      apply remove_neq_preserves_binds; auto.
      apply remove_preserves_binds_notin in H5; auto.
      apply Hmap_buffer; auto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply Hmap_buffer_inv in Hbinds1; auto.
      unfold binds in Hbinds1.
      rewrite H5 in Hbinds1.
      discriminate.
      apply remove_neq_preserves_binds; auto.
      apply Hmap_buffer; auto.
    apply binds_push_inv in H5; auto.
    intuition.
      subst. apply binds_push_eq; auto.
      apply binds_push_neq; auto.
      apply Hmap_buffer; auto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply Hmap_buffer_inv in Hbinds1.
      unfold binds in Hbinds1.
      rewrite H5 in Hbinds1.
      discriminate.
      apply binds_push_neq; auto.
      apply Hmap_buffer; auto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply ok_remove_notin; auto.
      apply Hwf; auto.
      apply remove_preserves_notin; auto.
      apply Hmap_buffer; auto.
    apply notin_union.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply Hmap_buffer_inv in H4.
      apply binds_in in Hbinds1.
      unfold "#" in H4; intuition.
      intuition.
      apply notin_neq; auto.
      apply Hmap_buffer; auto.
    unfold sync_array_wf.
    simpl. intuition.
    apply Hwf; auto.
    apply remove_preserves_ok; auto.
    apply Hwf; auto.
    econstructor; eauto.
    apply Hwf; auto.
    eapply Hmutual; eauto.
    eapply Hmap_buffer; eauto.
    unfold buffer_inv.
    simpl. intuition.
    destruct (eq_nat_dec pid0 pid).
      subst. apply ok_remove_notin; auto.
      apply remove_preserves_notin; auto.
      apply Hmap_buffer_inv in H4; intuition.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply Hmap_buffer_inv in H4.
      apply binds_in in Hbinds1.
      unfold "#" in H4; intuition.
      apply notin_union.
      intuition.
      apply notin_neq; auto.
      apply Hmap_buffer_inv; auto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      assert (pid # (remove inv pid)).
      apply ok_remove_notin; auto.
      unfold "#" in H5.
      apply binds_in in H4; intuition.
      apply remove_preserves_binds_notin in H4; auto.
      apply Hmap_buffer_inv in H4; auto.
    apply binds_push_inv in H4; auto.
    intuition.
      subst.
      apply Hmap_buffer_inv in Hbinds1; auto.
      apply Hmap_buffer_inv in H6; auto.
    unfold req_res_mutual.
    simpl. intuition.
    apply notin_union.
    destruct (eq_nat_dec pid0 pid).
      subst.
      assert (pid # (remove (requests N (LState s2)) pid)).
      apply ok_remove_notin; auto.
      apply Hwf; auto.
      apply binds_in in H4.
      unfold "#" in H5; intuition.
      intuition.
      apply notin_neq; auto.
      apply remove_preserves_binds_notin in H4; auto.
      eapply Hmutual; eauto.
    apply binds_push_inv in H4; auto.
    intuition.
      subst. apply ok_remove_notin; auto.
      apply Hwf; auto.
      apply remove_preserves_notin; auto.
      eapply Hmutual; eauto.
    unfold req_res_pos_inv.
    simpl. intuition.
    destruct (eq_nat_dec pid0 pid).
      subst. apply ok_remove_notin; auto.
      apply remove_preserves_notin; auto.
      eapply Hmutual_inv; eauto.
    apply notin_union.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply Hmutual_inv in H4; auto.
      apply binds_in in Hbinds1.
      unfold "#" in H4; intuition.
      intuition.
      apply notin_neq; auto.
      eapply Hmutual_inv; eauto.
    unfold req_res_mutual.
    simpl. intuition.
    apply notin_union.
      destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove inv pid)).
        apply ok_remove_notin; auto.
        apply binds_in in H4.
        unfold "#" in H5; intuition.
        intuition.
        apply notin_neq; auto.
        apply remove_preserves_binds_notin in H4; auto.
        apply Hmutual' in H4; auto.
      apply binds_push_inv in H4; auto.
      intuition.
        subst. apply ok_remove_notin; auto.
        apply remove_preserves_notin; auto.
        apply Hmutual' in H6; auto.
    (* read *)
    ---
    exists (
      mkSyncState (array N)
        (mkAryState N
          (remove (s2).(LState).(requests N) pid)
          ((pid, AryReadOk (Vector.nth vec (Fin.of_nat_lt Hlt))) :: (s2).(LState).(responses N))
          vec
        )
        (PidPos s2)
    ).
    simpl. intuition.
      destruct s2. simpl in *.
      destruct LState; simpl in *.
      subst.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos).
      apply Hwf; auto.
      eapply Hmap; eauto.
      2: {
        eauto.
      }
      2: {
        eauto.
      }
      simpl.
      eapply array_step_read.
      5 : { eauto. }
      6 : { eauto. }
      apply Hwf; auto.
      apply Hwf; auto.
      eapply Hmap_buffer; eauto.
      eapply Hmutual; eauto.
      eapply Hmap_buffer; eauto.
      eauto.
    unfold buffer_map.
    simpl. intuition.
    destruct (eq_nat_dec pid0 pid).
      subst.
      assert (pid # (remove inv pid)).
      apply ok_remove_notin; auto.
      apply binds_in in H5.
      unfold "#" in H4; intuition.
      apply remove_neq_preserves_binds; auto.
      apply remove_preserves_binds_notin in H5; auto.
      apply Hmap_buffer; auto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply Hmap_buffer_inv in Hbinds1; auto.
      unfold binds in Hbinds1.
      rewrite H5 in Hbinds1.
      discriminate.
      apply remove_neq_preserves_binds; auto.
      apply Hmap_buffer; auto.
    apply binds_push_inv in H5; auto.
    intuition.
      subst. apply binds_push_eq; auto.
      apply binds_push_neq; auto.
      apply Hmap_buffer; auto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply Hmap_buffer_inv in Hbinds1.
      unfold binds in Hbinds1.
      rewrite H5 in Hbinds1.
      discriminate.
      apply binds_push_neq; auto.
      apply Hmap_buffer; auto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply ok_remove_notin; auto.
      apply Hwf; auto.
      apply remove_preserves_notin; auto.
      apply Hmap_buffer; auto.
    apply notin_union.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply Hmap_buffer_inv in H4.
      apply binds_in in Hbinds1.
      unfold "#" in H4; intuition.
      intuition.
      apply notin_neq; auto.
      apply Hmap_buffer; auto.
    unfold sync_array_wf.
    simpl. intuition.
    apply Hwf; auto.
    apply remove_preserves_ok; auto.
    apply Hwf; auto.
    econstructor; eauto.
    apply Hwf; auto.
    eapply Hmutual; eauto.
    eapply Hmap_buffer; eauto.
    unfold buffer_inv.
    simpl. intuition.
    destruct (eq_nat_dec pid0 pid).
      subst. apply ok_remove_notin; auto.
      apply remove_preserves_notin; auto.
      apply Hmap_buffer_inv in H4; intuition.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply Hmap_buffer_inv in H4.
      apply binds_in in Hbinds1.
      unfold "#" in H4; intuition.
      apply notin_union.
      intuition.
      apply notin_neq; auto.
      apply Hmap_buffer_inv; auto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      assert (pid # (remove inv pid)).
      apply ok_remove_notin; auto.
      unfold "#" in H5.
      apply binds_in in H4; intuition.
      apply remove_preserves_binds_notin in H4; auto.
      apply Hmap_buffer_inv in H4; auto.
    apply binds_push_inv in H4; auto.
    intuition.
      subst.
      apply Hmap_buffer_inv in Hbinds1; auto.
      apply Hmap_buffer_inv in H6; auto.
    unfold req_res_mutual.
    simpl. intuition.
    apply notin_union.
    destruct (eq_nat_dec pid0 pid).
      subst.
      assert (pid # (remove (requests N (LState s2)) pid)).
      apply ok_remove_notin; auto.
      apply Hwf; auto.
      apply binds_in in H4.
      unfold "#" in H5; intuition.
      intuition.
      apply notin_neq; auto.
      apply remove_preserves_binds_notin in H4; auto.
      eapply Hmutual; eauto.
    apply binds_push_inv in H4; auto.
    intuition.
      subst. apply ok_remove_notin; auto.
      apply Hwf; auto.
      apply remove_preserves_notin; auto.
      eapply Hmutual; eauto.
    unfold req_res_pos_inv.
    simpl. intuition.
    destruct (eq_nat_dec pid0 pid).
      subst. apply ok_remove_notin; auto.
      apply remove_preserves_notin; auto.
      eapply Hmutual_inv; eauto.
    apply notin_union.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply Hmutual_inv in H4; auto.
      apply binds_in in Hbinds1.
      unfold "#" in H4; intuition.
      intuition.
      apply notin_neq; auto.
      eapply Hmutual_inv; eauto.
    unfold req_res_mutual.
    simpl. intuition.
    apply notin_union.
      destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove inv pid)).
        apply ok_remove_notin; auto.
        apply binds_in in H4.
        unfold "#" in H5; intuition.
        intuition.
        apply notin_neq; auto.
        apply remove_preserves_binds_notin in H4; auto.
        apply Hmutual' in H4; auto.
      apply binds_push_inv in H4; auto.
      intuition.
        subst. apply ok_remove_notin; auto.
        apply remove_preserves_notin; auto.
        apply Hmutual' in H6; auto.
    (* query from identity to array *)
    --
    inversion H0; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    exists (
      mkSyncState (array N)
        (mkAryState N
          ((s2).(LState).(requests N))
          ((s2).(LState).(responses N))
          (vec N st0)
        )
        (PidPos s2)
    ).
    simpl. intuition.
      destruct s2. simpl in *.
      destruct LState; simpl in *.
      subst.
      eapply Step_None; eauto.
    inversion H5; subst; simpl in *; auto.
    unfold buffer_map.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *; auto.
      simpl. intuition.
      apply binds_push_inv in H7; auto.
      intuition.
        subst.
        apply Hmap_buffer; auto.
        apply Hmap_buffer; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        eapply substitute_eq_binds_v' in Hbinds0; eauto.
        unfold binds in H7.
        rewrite Hbinds0 in H7.
        discriminate.
        apply substitute_neq_preserves_binds' in H7; auto.
        apply Hmap_buffer; auto.
      apply Hmap_buffer; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        eapply substitute_eq_binds_v' in Hbinds0; eauto.
        unfold binds in H7.
        rewrite Hbinds0 in H7.
        discriminate.
        apply substitute_neq_preserves_binds' in H7; auto.
        apply Hmap_buffer; auto.
      apply substitute_preserves_notin' in H6; auto.
      apply Hmap_buffer; auto.
      apply substitute_preserves_notin' in H6; auto.
      apply Hmap_buffer; auto.

      simpl. intuition.
      apply binds_push_inv in H7; auto.
      intuition.
        subst.
        apply Hmap_buffer; auto.
        apply Hmap_buffer; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        eapply substitute_eq_binds_v' in Hbinds0; eauto.
        unfold binds in H7.
        rewrite Hbinds0 in H7.
        discriminate.
        apply substitute_neq_preserves_binds' in H7; auto.
        apply Hmap_buffer; auto.
      apply Hmap_buffer; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        eapply substitute_eq_binds_v' in Hbinds0; eauto.
        unfold binds in H7.
        rewrite Hbinds0 in H7.
        discriminate.
        apply substitute_neq_preserves_binds' in H7; auto.
        apply Hmap_buffer; auto.
      apply substitute_preserves_notin' in H6; auto.
      apply Hmap_buffer; auto.
      apply substitute_preserves_notin' in H6; auto.
      apply Hmap_buffer; auto.
    unfold thread_state_map'.
    simpl. intuition.
    apply binds_push_inv in H6; auto.
    intuition.
      subst.
      eapply Hmap; eauto.
      apply remove_preserves_binds_notin in H8; auto.
      eapply Hmap; eauto.
    apply notin_union in H6.
    intuition.
    apply notin_neq in H7.
    apply remove_neq_preserves_notin in H8; auto.
    eapply Hmap; eauto.
    unfold buffer_inv.
    simpl.
    inversion H5; subst; simpl in *.
    inversion H4; subst; simpl in *.
    intuition.
    apply notin_union.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply substitute_preserves_notin' in H6; auto.
      apply binds_in in Hbinds0.
      unfold "#" in H6; intuition.
      intuition.
      apply notin_neq; auto.
      apply substitute_preserves_notin' in H6; auto.
      apply Hmap_buffer_inv; auto.
      apply substitute_preserves_notin' in H6; auto.
      apply Hmap_buffer_inv; auto.
    apply binds_push_inv in H6; auto.
    intuition.
      subst.
      eapply substitute_eq_binds_v'; eauto.
      eapply substitute_neq_preserves_binds; eauto.
      apply Hmap_buffer_inv in H8; auto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      eapply substitute_eq_binds_v'; eauto.
      eapply substitute_neq_preserves_binds; eauto.
      apply Hmap_buffer_inv in H6; auto.
    inversion H4; subst; simpl in *.
    intuition.
    apply notin_union.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply substitute_preserves_notin' in H6; auto.
      apply binds_in in Hbinds0.
      unfold "#" in H6; intuition.
      intuition.
      apply notin_neq; auto.
      apply substitute_preserves_notin' in H6; auto.
      apply Hmap_buffer_inv; auto.
      apply substitute_preserves_notin' in H6; auto.
      apply Hmap_buffer_inv; auto.
    apply binds_push_inv in H6; auto.
    intuition.
      subst.
      eapply substitute_eq_binds_v'; eauto.
      eapply substitute_neq_preserves_binds; eauto.
      apply Hmap_buffer_inv in H8; auto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      eapply substitute_eq_binds_v'; eauto.
      eapply substitute_neq_preserves_binds; eauto.
      apply Hmap_buffer_inv in H6; auto.
    unfold req_res_pos_inv.
    simpl.
    inversion H5; subst; simpl in *.
      intuition.
      apply notin_union in H6.
      apply notin_union.
      intuition.
      apply Hmutual_inv in H8; intuition.
      apply notin_union in H6.
      intuition.
      apply Hmutual_inv in H8; intuition.
      intuition.
      apply notin_union in H6.
      apply notin_union.
      intuition.
      apply Hmutual_inv in H8; intuition.
      apply notin_union in H6.
      intuition.
      apply Hmutual_inv in H8; intuition.
    unfold req_res_mutual.
    inversion H5; subst; simpl in *.
    inversion H4; subst; simpl in *.
      intuition.
      apply binds_push_inv in H6.
      intuition.
        subst. auto.
        eapply Hmutual'; eauto.
      apply notin_union.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply binds_in in H6.
        unfold "#" in Hnotin_res; intuition.
        intuition.
        apply notin_neq; intuition.
        eapply Hmutual'; eauto.
    inversion H4; subst; simpl in *.
      intuition.
      apply binds_push_inv in H6.
      intuition.
        subst. auto.
        eapply Hmutual'; eauto.
      apply notin_union.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply binds_in in H6.
        unfold "#" in Hnotin_res; intuition.
        intuition.
        apply notin_neq; intuition.
        eapply Hmutual'; eauto.
    (* reply from array to identity *)
    --
    inversion H0; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H2; subst; simpl in *.
    exists (
      mkSyncState (array N)
        (mkAryState N
          ((s2).(LState).(requests N))
          ((s2).(LState).(responses N))
          (vec N st0)
        )
        (PidPos s2)
    ).
    simpl. intuition.
      destruct s2. simpl in *.
      destruct LState; simpl in *.
      subst.
      eapply Step_None; eauto.
    inversion H5; subst; simpl in *; auto.
    unfold buffer_map.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *; auto.
      simpl. intuition.
      apply Hmap_buffer; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        eapply substitute_eq_binds_v' in Hbinds1; eauto.
        unfold binds in H7.
        rewrite Hbinds1 in H7.
        discriminate.
        apply substitute_neq_preserves_binds' in H7; auto.
        apply Hmap_buffer; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove res pid)).
        apply ok_remove_notin; auto.
        apply binds_in in H7.
        unfold "#" in H6; intuition.
        apply remove_preserves_binds_notin in H7; auto.
        apply Hmap_buffer; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        eapply substitute_eq_binds_v' in Hbinds1; eauto.
        unfold binds in H7.
        rewrite Hbinds1 in H7.
        inversion H7; subst; simpl in *.
        apply Hmap_buffer; auto.
        apply substitute_neq_preserves_binds' in H7; auto.
        apply Hmap_buffer; auto.
      apply substitute_preserves_notin' in H6; auto.
      apply Hmap_buffer; auto.
      apply substitute_preserves_notin' in H6; auto.
      apply Hmap_buffer; auto.
      simpl. intuition.
      apply Hmap_buffer; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        eapply substitute_eq_binds_v' in Hbinds1; eauto.
        unfold binds in H7.
        rewrite Hbinds1 in H7.
        discriminate.
        apply substitute_neq_preserves_binds' in H7; auto.
        apply Hmap_buffer; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove res pid)).
        apply ok_remove_notin; auto.
        apply binds_in in H7.
        unfold "#" in H6; intuition.
        apply remove_preserves_binds_notin in H7; auto.
        apply Hmap_buffer; auto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        eapply substitute_eq_binds_v' in Hbinds1; eauto.
        unfold binds in H7.
        rewrite Hbinds1 in H7.
        inversion H7; subst; simpl in *.
        apply Hmap_buffer; auto.
        apply substitute_neq_preserves_binds' in H7; auto.
        apply Hmap_buffer; auto.
      apply substitute_preserves_notin' in H6; auto.
      apply Hmap_buffer; auto.
      apply substitute_preserves_notin' in H6; auto.
      apply Hmap_buffer; auto.
      unfold thread_state_map'.
      inversion H4; subst; simpl in *.
      simpl. intuition.
      apply binds_push_inv in H6; auto.
      intuition.
        subst.
        eapply Hmap; eauto.
        apply remove_preserves_binds_notin in H8; auto.
        eapply Hmap; eauto.
      apply notin_union in H6.
      intuition.
      apply notin_neq in H7.
      apply remove_neq_preserves_notin in H8; auto.
      eapply Hmap; eauto.
      unfold buffer_inv.
      simpl.
      inversion H5; subst; simpl in *.
      inversion H4; subst; simpl in *.
      intuition.
        destruct (eq_nat_dec pid0 pid).
          subst.
          eapply substitute_eq_binds_v' in Hbinds2; eauto.
          apply notin_get_none in H6.
          rewrite Hbinds2 in H6.
          discriminate.
          apply substitute_preserves_notin' in H6; auto.
          eapply Hmap_buffer_inv; eauto.
        destruct (eq_nat_dec pid0 pid).
          subst.
          apply ok_remove_notin; auto.
          apply remove_preserves_notin; auto.
          apply substitute_preserves_notin' in H6; auto.
          eapply Hmap_buffer_inv; eauto.
        destruct (eq_nat_dec pid0 pid).
          subst.
          unfold buffer_map in *.
          assert (binds pid q (requests N (LState s2))).
          eapply Hmap_buffer; eauto.
          assert (binds pid (AryCASOk b) (responses N (LState s2))).
          eapply Hmap_buffer; eauto.
          eapply Hmutual in H7; eauto.
          apply binds_in in H8.
          unfold "#" in H7.
          intuition.
          apply substitute_neq_preserves_binds; auto.
          apply Hmap_buffer_inv in H6; auto.
        destruct (eq_nat_dec pid0 pid).
          subst.
          assert (pid # (remove res pid)).
          apply ok_remove_notin; auto.
          apply binds_in in H6.
          unfold "#" in H7.
          intuition.
          apply substitute_neq_preserves_binds; auto.
          apply remove_preserves_binds_notin in H6; auto.
          apply Hmap_buffer_inv in H6; auto.
      inversion H4; subst; simpl in *.
      intuition.
        destruct (eq_nat_dec pid0 pid).
          subst.
          eapply substitute_eq_binds_v' in Hbinds2; eauto.
          apply notin_get_none in H6.
          rewrite Hbinds2 in H6.
          discriminate.
          apply substitute_preserves_notin' in H6; auto.
          eapply Hmap_buffer_inv; eauto.
        destruct (eq_nat_dec pid0 pid).
          subst.
          apply ok_remove_notin; auto.
          apply remove_preserves_notin; auto.
          apply substitute_preserves_notin' in H6; auto.
          eapply Hmap_buffer_inv; eauto.
        destruct (eq_nat_dec pid0 pid).
          subst.
          unfold buffer_map in *.
          assert (binds pid q (requests N (LState s2))).
          eapply Hmap_buffer; eauto.
          assert (binds pid (AryReadOk ret) (responses N (LState s2))).
          eapply Hmap_buffer; eauto.
          eapply Hmutual in H7; eauto.
          apply binds_in in H8.
          unfold "#" in H7.
          intuition.
          apply substitute_neq_preserves_binds; auto.
          apply Hmap_buffer_inv in H6; auto.
        destruct (eq_nat_dec pid0 pid).
          subst.
          assert (pid # (remove res pid)).
          apply ok_remove_notin; auto.
          apply binds_in in H6.
          unfold "#" in H7.
          intuition.
          apply substitute_neq_preserves_binds; auto.
          apply remove_preserves_binds_notin in H6; auto.
          apply Hmap_buffer_inv in H6; auto.
        unfold req_res_pos_inv.
        simpl.
        inversion H5; subst; simpl in *.
        inversion H4; subst; simpl in *.
        intuition.
        destruct (eq_nat_dec pid0 pid).
          subst.
          eapply Hmutual' in Hbinds1; eauto.
          apply remove_neq_preserves_notin in H6; auto.
          apply Hmutual_inv in H6; intuition.
        destruct (eq_nat_dec pid0 pid).
          subst.
          apply ok_remove_notin; auto.
          apply remove_preserves_notin; auto.
          apply remove_neq_preserves_notin in H6; auto.
          apply Hmutual_inv in H6; intuition.
        inversion H4; subst; simpl in *.
        intuition.
        destruct (eq_nat_dec pid0 pid).
          subst.
          eapply Hmutual' in Hbinds1; eauto.
          apply remove_neq_preserves_notin in H6; auto.
          apply Hmutual_inv in H6; intuition.
        destruct (eq_nat_dec pid0 pid).
          subst.
          apply ok_remove_notin; auto.
          apply remove_preserves_notin; auto.
          apply remove_neq_preserves_notin in H6; auto.
          apply Hmutual_inv in H6; intuition.
        unfold req_res_mutual.
        inversion H5; subst; simpl in *.
        inversion H4; subst; simpl in *.
          intuition.
          apply remove_preserves_notin; auto.
          eapply Hmutual'; eauto.
          destruct (eq_nat_dec pid0 pid).
            subst.
            assert (pid # (remove res pid)).
            apply ok_remove_notin; auto.
            apply binds_in in H6.
            unfold "#" in H7; intuition.
            apply remove_preserves_binds_notin in H6; auto.
            eapply Hmutual'; eauto.
        inversion H4; subst; simpl in *.
          intuition.
          apply remove_preserves_notin; auto.
          eapply Hmutual'; eauto.
          destruct (eq_nat_dec pid0 pid).
            subst.
            assert (pid # (remove res pid)).
            apply ok_remove_notin; auto.
            apply binds_in in H6.
            unfold "#" in H7; intuition.
            apply remove_preserves_binds_notin in H6; auto.
            eapply Hmutual'; eauto.
Qed.

End VerfiedArray.