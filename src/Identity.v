Require Import
  List
  LibVar
  LTS.
Import ListNotations.

Require 
  LibEnv.

Section Identity.

Variable liA: language_interface.

  Inductive id_state :=
  | GetQuery(q: query liA)
  | Pending
  | GetReply(r: reply liA).

  Record Identity_state := mkIdState {
    buffer : LibEnv.env id_state;
  }.

  Definition new_identity := mkIdState nil.

  Definition identity_new_state id_st := id_st = new_identity.

  Inductive Internal :=.

  Import LibEnv.

  Inductive identity_initial_state : Identity_state -> Pid -> query liA -> Identity_state -> Prop :=
  | identity_initial_state_get: forall buffer st st' pid q
    (Hnotin_buffer : pid # buffer)
    (Hok_buffer : ok buffer),
    st = mkIdState buffer ->
    st' = mkIdState ((pid, (GetQuery q))::buffer) ->
    identity_initial_state st pid q st'.

  Inductive identity_final_state : Identity_state -> Pid -> reply liA -> Identity_state -> Prop :=
  | identity_final_state_ret: forall buffer st st' pid r
    (Hok_buffer : ok buffer)
    (Hbinds : binds pid (GetReply r) buffer),
    st = mkIdState buffer ->
    st' = mkIdState (remove buffer pid) ->
    identity_final_state st pid r st'.

  Inductive identity_step : Identity_state -> Pid -> Internal -> Identity_state -> Prop :=.

  Inductive identity_at_external : Identity_state -> Pid -> query liA -> Identity_state -> Prop :=
  | identity_at_external_query: forall buffer st st' pid q
    (Hok_buffer : ok buffer)
    (Hbinds : binds pid (GetQuery q) buffer),
    st = mkIdState buffer ->
    st' = mkIdState (substitute buffer pid Pending) ->
    identity_at_external st pid q st'.

  Inductive identity_after_external : Identity_state -> Pid -> reply liA -> Identity_state -> Prop :=
  | identity_after_external_reply: forall buffer st st' pid r
    (Hok_buffer : ok buffer)
    (Hbinds : binds pid Pending buffer),
    st = mkIdState buffer ->
    st' = mkIdState (substitute buffer pid (GetReply r)) ->
    identity_after_external st pid r st'.

  Definition identity : lts liA liA := mkLTS liA liA
    Identity_state
    Internal
    identity_step
    identity_new_state
    identity_initial_state
    identity_at_external
    identity_after_external
    identity_final_state
  .

End Identity.

Arguments GetQuery {liA}.
Arguments Pending {liA}.
Arguments GetReply {liA}.
Arguments buffer {liA}.

Section IdentityProp.

Require Import
  Arith
  LibVar
  LibEnv
  SyncLTS
  ImplRefinement
  ArrayQueueInvariant
  ArrayQueueInvariantBefore.

Variable liA: language_interface.

Definition thread_state_map (pc : LibEnv.env (id_state liA)) h :=
  forall pid p,
  (binds pid p pc -> p <> Pending ->
   binds pid Run h) /\
  (binds pid Pending pc ->
   binds pid Wait h) /\
  (pid # pc -> pid # h).

Definition sync_identity_wf (y : state (sync (identity liA))) :=
  ok y.(PidPos).

Lemma identity_is_sc: 
  impl_refines (identity liA)
    (sync (identity liA)).
Proof.
  eapply forward_simulation_inv_ind
    with (f:=fun (x : state (identity liA)) (y : state (sync (identity liA))) =>
      x = y.(LState) /\
      thread_state_map y.(LState).(buffer) y.(PidPos) /\
      sync_identity_wf y
      )
      (inv:=fun x => True).
  unfold fsim_properties_inv_ind. intuition.
  - unfold invariant_ind. intuition.
  - exists (mkSyncState (identity liA)
      s1 []).
    simpl in *.
    unfold identity_new_state in H.
    unfold new_identity in H.
    rewrite H.
    simpl.
    unfold sync_new_state.
    simpl.
    unfold identity_new_state.
    simpl.
    unfold new_identity.
    simpl. intuition.
    unfold thread_state_map.
    intuition; inversion H0.
    unfold sync_identity_wf.
    simpl.
    econstructor.
  - rename H0 into Hmap.
    rename H4 into Hwf.
    exists (mkSyncState (identity liA)
      s1'
      ((pid, Run)::(PidPos s2))).
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_initial_state_L with (pos:=PidPos); eauto.
      apply Hmap; auto.
      econstructor.
      apply qb.
      inversion H1; subst; simpl in *; auto.
    subst. auto.
    subst.
    unfold thread_state_map.
    simpl. intuition.
    inversion H1; subst; simpl in *.
    apply binds_push_inv in H0; auto.
    intuition.
      subst. apply binds_push_eq; auto.
      apply binds_push_neq; auto.
      eapply Hmap; eauto.
      rewrite H3. simpl.
      eauto.
    inversion H1; subst; simpl in *.
    apply binds_push_inv in H0; auto.
    intuition.
      discriminate.
      apply binds_push_neq; auto.
      eapply Hmap; eauto.
      rewrite H2. simpl.
      eauto.
    apply notin_union.
    destruct (eq_nat_dec pid0 pid).
      subst.
      inversion H1; subst; simpl in *;
      apply notin_union in H0;
      intuition;
      apply notin_neq in H3; intuition.
      inversion H1; subst; simpl in *;
      apply notin_union in H0;
      intuition;
      apply Hmap; auto;
      rewrite H2; auto.
    unfold sync_identity_wf.
    simpl.
    econstructor; eauto.
    inversion H1; subst; simpl in *.
    apply Hmap; auto.
    econstructor.
    apply qb.
    rewrite H0.
    simpl; auto.
  - rename H0 into Hmap.
    rename H4 into Hwf.
    exists (mkSyncState (identity liA)
      s1'
      (remove (PidPos s2) pid)).
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_final_state_L with (pos:=PidPos); eauto.
      inversion H1; subst; simpl in *; auto;
      eapply Hmap; eauto;
      intro; intuition; discriminate.
    subst. auto.
    subst.
    unfold thread_state_map.
    simpl. intuition.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply binds_in in H0.
      inversion H1; subst; simpl in *;
      assert (Hnot: pid # (remove buffer0 pid)) by
      (apply ok_remove_notin; auto);
      unfold "#" in Hnot;
      intuition.
      inversion H1; subst; simpl in *.
      apply remove_preserves_binds_notin in H0; auto;
      apply remove_neq_preserves_binds; auto;
      eapply Hmap; eauto;
      rewrite H3; eauto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply binds_in in H0.
      inversion H1; subst; simpl in *;
      assert (Hnot: pid # (remove buffer0 pid)) by
      (apply ok_remove_notin; auto);
      unfold "#" in Hnot;
      intuition.
      apply remove_neq_preserves_binds; auto.
      inversion H1; subst; simpl in *;
      apply remove_preserves_binds_notin in H0; auto;
      eapply Hmap; eauto;
      rewrite H2; eauto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply ok_remove_notin; auto.
      apply remove_preserves_notin; auto.
      inversion H1; subst; simpl in *;
      apply remove_neq_preserves_notin in H0; auto;
      eapply Hmap; eauto;
      rewrite H2; eauto.
    unfold sync_identity_wf.
    simpl.
    apply remove_preserves_ok; auto.
  - rename H0 into Hmap.
    rename H4 into Hwf.
    exists (mkSyncState (identity liA)
      s1'
      ((pid, Wait)::(remove (PidPos s2) pid))
    ).
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_at_external_L with (pos:=PidPos); eauto.
      inversion H1; subst; simpl in *; auto;
      eapply Hmap; eauto;
      intro; intuition; discriminate.
    subst. auto.
    unfold thread_state_map.
    simpl.
    intuition.
    destruct (eq_nat_dec pid0 pid).
      subst.
      unfold binds in H0.
      inversion H1; subst; simpl in *; auto;
      eapply substitute_eq_binds_v' in Hbinds;
      rewrite Hbinds in H0;
      inversion H0; subst;
      exfalso;
      apply H3. reflexivity.
      apply binds_push_neq; auto.
      apply remove_neq_preserves_binds; auto.
      inversion H1; subst; simpl in *; auto.
      apply substitute_neq_preserves_binds' in H0; auto;
      eapply Hmap; eauto;
      rewrite H4; eauto.
    destruct (eq_nat_dec pid0 pid).
      subst. apply binds_push_eq; auto.
      apply binds_push_neq; auto.
      apply remove_neq_preserves_binds; auto.
      inversion H1; subst; simpl in *; auto;
      apply substitute_neq_preserves_binds' in H0; auto;
      eapply Hmap; eauto;
      rewrite H3; eauto.
    apply notin_union.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply notin_get_none in H0.
      inversion H1; subst; simpl in *;
      eapply substitute_eq_binds_v' in Hbinds; eauto;
      rewrite Hbinds in H0; discriminate.
      intuition.
      apply notin_neq; auto.
      apply remove_preserves_notin; auto;
      inversion H1; subst; simpl in *;
      apply substitute_preserves_notin' in H0;
      eapply Hmap; eauto;
      rewrite H3; eauto.
    unfold sync_identity_wf.
    simpl.
    econstructor; eauto.
    apply remove_preserves_ok; auto.
    apply ok_remove_notin; auto.
  - rename H0 into Hmap.
    rename H4 into Hwf.
    exists (mkSyncState (identity liA)
      s1'
      ((pid, Run)::(remove (PidPos s2) pid))
    ).
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_after_external_L with (pos:=PidPos); eauto.
      inversion H1; subst; simpl in *; auto.
      unfold thread_state_map in *.
      apply Hmap in Hbinds; auto.
      apply (GetReply ra).
    subst. auto.
    unfold thread_state_map.
    simpl.
    intuition.
    destruct (eq_nat_dec pid0 pid).
      subst. apply binds_push_eq; auto.
      apply binds_push_neq; auto.
      apply remove_neq_preserves_binds; auto.
      inversion H1; subst; simpl in *; auto;
      apply substitute_neq_preserves_binds' in H0; auto;
      eapply Hmap; eauto;
      rewrite H4; eauto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      unfold binds in H0.
      inversion H1; subst; simpl in *; auto;
      eapply substitute_eq_binds_v' in Hbinds;
      rewrite Hbinds in H0;
      inversion H0; subst;
      exfalso;
      unfold wait_pc in H3; intuition; discriminate.
      apply binds_push_neq; auto.
      apply remove_neq_preserves_binds; auto.
      inversion H1; subst; simpl in *; auto;
      apply substitute_neq_preserves_binds' in H0; auto;
      eapply Hmap; eauto;
      rewrite H3; eauto.
    apply notin_union.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply notin_get_none in H0.
      inversion H1; subst; simpl in *;
      eapply substitute_eq_binds_v' in Hbinds; eauto;
      rewrite Hbinds in H0; discriminate.
      intuition.
      apply notin_neq; auto.
      apply remove_preserves_notin; auto;
      inversion H1; subst; simpl in *;
      apply substitute_preserves_notin' in H0;
      eapply Hmap; eauto;
      rewrite H3; eauto.
    unfold sync_identity_wf.
    simpl.
    econstructor; eauto.
    apply remove_preserves_ok; auto.
    apply ok_remove_notin; auto.
  - rename H0 into Hmap.
    rename H4 into Hwf.
    exists (mkSyncState (identity liA)
      s1'
      (PidPos s2)).
    simpl. intuition.
      destruct s2. simpl in *.
      eapply Step_Internal; eauto.
      2 : { eapply Step_None; eauto. }
      eapply sync_step_L_internal with (pos:=PidPos); eauto.
      inversion H1; subst; simpl in *;
      eapply Hmap; eauto;
      unfold wait_pc;
      intro; intuition; discriminate.
    subst. auto.
    subst.
    unfold thread_state_map.
    simpl. intuition.
    destruct (eq_nat_dec pid0 pid).
      subst.
      inversion H1; subst; simpl in *;
      try (rewrite H3 in Hmap);
      try (rewrite H4 in Hmap);
      simpl in *;
      eapply Hmap; eauto;
      unfold wait_pc; intro;
      intuition; discriminate.
      inversion H1; subst; simpl in *;
      apply substitute_neq_preserves_binds' in H0; auto;
      try (rewrite H3 in Hmap);
      try (rewrite H4 in Hmap);
      simpl in *;
      eapply Hmap; eauto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      unfold binds in H0.
      inversion H1; subst; simpl in *;
      eapply substitute_eq_binds_v' in Hbinds;
      rewrite Hbinds in H0;
      inversion H0; subst;
      unfold wait_pc in H2;
      intuition; discriminate.
      inversion H1; subst; simpl in *;
      apply substitute_neq_preserves_binds' in H0; auto;
      try (rewrite H3 in Hmap);
      try (rewrite H4 in Hmap);
      simpl in *;
      eapply Hmap; eauto.
    destruct (eq_nat_dec pid0 pid).
      subst.
      apply notin_get_none in H0.
      inversion H1; subst; simpl in *;
      eapply substitute_eq_binds_v' in Hbinds;
      rewrite Hbinds in H0; discriminate.
      inversion H1; subst; simpl in *;
      apply substitute_preserves_notin' in H0; auto;
      eapply Hmap; eauto;
      try (rewrite H2);
      try (rewrite H3);
      eauto.
Qed.

End IdentityProp.

Section ArrayRefinement.

Require Import
  Nat
  List
  Arith
  LTS
  LibVar
  LibEnv
  Refinement
  Array
  ArrayProp.
Import ListNotations.

Variable N: nat.

Definition buffer_map'
  (req: LibEnv.env Array_query)
  (res: LibEnv.env Array_reply)
  (buffer: LibEnv.env (id_state li_array)) :=
  forall pid,
    (forall (q : query li_array), binds pid q req -> binds pid (GetQuery q) buffer) /\
    (forall (r : reply li_array), binds pid r res -> binds pid (GetReply r) buffer) /\
    (pid # req -> pid # res -> pid # buffer).

Definition array_id_wf (buffer: LibEnv.env (id_state li_array)) :=
  ok buffer.

Lemma array_refines_array_identity: 
  refines (array N)
    (linked_lts (raw_compose (array N) (identity li_array))).
Proof.
  eapply forward_simulation_inv_ind
    with (f:=fun (x : state (array N)) (y : state (linked_lts (raw_compose (array N) (identity li_array)))) =>
        x.(vec N) = y.(RawL1State).(vec N) /\
        buffer_map'
          x.(requests N)
          x.(responses N)
          y.(RawL2State).(buffer) /\
        y.(RawL1State).(requests N) = [] /\
        y.(RawL1State).(responses N) = [] /\
        array_id_wf y.(RawL2State).(buffer li_array)
      )
      (inv:=fun x => array_exclusive_wf N x).
  unfold fsim_properties_inv_ind. intuition.
  - apply array_exclusive_wf_inv.
  - exists (@mkRawComposedState li_array li_array
              (array N) (identity li_array)
              (new_array N)
              (new_identity li_array)
              ).
    simpl.
    inversion H; subst; simpl in *.
    intuition.
    unfold new_array.
    unfold raw_composed_new_state.
    simpl.
    unfold array_new_state.
    unfold new_array.
    unfold identity_new_state.
    intuition.
    unfold buffer_map'.
    intuition; inversion H0.
    unfold array_id_wf.
    econstructor.
  - rename H into Hmutual.
    rename H2 into Hvec.
    rename H0 into Hmap.
    rename H3 into Hreq.
    rename H4 into Hres.
    rename H6 into Hwf.
    exists (@mkRawComposedState li_array li_array
              (array N) (identity li_array)
              (mkAryState N
                [] [] (vec N s1'))
              (mkIdState li_array
                ((pid, GetQuery qb)::(buffer (RawL2State s2))))
              ).
    simpl. intuition.
      destruct s2. simpl in *.
      destruct RawL1State; simpl in *.
      destruct RawL2State; simpl in *.
      subst.
      eapply raw_composed_initial_state_L2; eauto.
      eapply identity_initial_state_get; eauto.
      inversion H1; subst; simpl in *;
      apply Hmap; auto.
      inversion H1; subst; simpl in *; auto.
      unfold buffer_map'.
      simpl.
      inversion H1; subst; simpl in *.
        intuition.
        apply binds_push_inv in H.
        intuition.
          subst.
          apply binds_push_eq; auto.
          apply binds_push_neq; auto.
          apply Hmap; auto.
        destruct (eq_nat_dec pid0 pid).
          subst.
          apply binds_in in H.
          unfold "#" in Hnotin_res; intuition.
          apply binds_push_neq; auto.
          apply Hmap; auto.
        apply notin_union.
        apply notin_union in H.
        intuition.
        apply Hmap; auto.
        intuition.
        apply binds_push_inv in H.
        intuition.
          subst.
          apply binds_push_eq; auto.
          apply binds_push_neq; auto.
          apply Hmap; auto.
        destruct (eq_nat_dec pid0 pid).
          subst.
          apply binds_in in H.
          unfold "#" in Hnotin_res; intuition.
          apply binds_push_neq; auto.
          apply Hmap; auto.
        apply notin_union.
        apply notin_union in H.
        intuition.
        apply Hmap; auto.
      unfold array_id_wf.
      econstructor; eauto.
      inversion H1; subst; simpl in *;
      apply Hmap; auto.
  - rename H into Hmutual.
    rename H2 into Hvec.
    rename H0 into Hmap.
    rename H3 into Hreq.
    rename H4 into Hres.
    rename H6 into Hwf.
    exists (@mkRawComposedState li_array li_array
              (array N) (identity li_array)
              (mkAryState N
                [] [] (vec N s1'))
              (mkIdState li_array
                (remove (buffer (RawL2State s2)) pid))
              ).
    simpl. intuition.
      destruct s2. simpl in *.
      destruct RawL1State; simpl in *.
      destruct RawL2State; simpl in *.
      subst.
      eapply raw_composed_final_state_L2; eauto.
      eapply identity_final_state_ret; eauto.
      inversion H1; subst; simpl in *;
      apply Hmap; auto.
      inversion H1; subst; simpl in *; auto.
      unfold buffer_map'.
      simpl.
      inversion H1; subst; simpl in *.
        intuition.
        destruct (eq_nat_dec pid0 pid).
          subst.
          apply binds_in in Hbinds.
          apply Hmutual in Hbinds.
          simpl in Hbinds.
          apply binds_in in H.
          unfold "#" in Hbinds; intuition.
        apply remove_neq_preserves_binds; auto.
        apply Hmap; auto.
        destruct (eq_nat_dec pid0 pid).
          subst.
          assert (pid # (remove res pid)).
          apply ok_remove_notin; auto.
          apply binds_in in H.
          unfold "#" in H0; intuition.
          apply remove_preserves_binds_notin in H; auto.
          apply remove_neq_preserves_binds; auto.
          apply Hmap; auto.
        destruct (eq_nat_dec pid0 pid).
          subst.
          apply ok_remove_notin; auto.
          apply remove_preserves_notin; auto.
          apply remove_neq_preserves_notin in H0; auto.
          apply Hmap; auto.
        intuition.
        destruct (eq_nat_dec pid0 pid).
          subst.
          apply binds_in in Hbinds.
          apply Hmutual in Hbinds.
          simpl in Hbinds.
          apply binds_in in H.
          unfold "#" in Hbinds; intuition.
        apply remove_neq_preserves_binds; auto.
        apply Hmap; auto.
        destruct (eq_nat_dec pid0 pid).
          subst.
          assert (pid # (remove res pid)).
          apply ok_remove_notin; auto.
          apply binds_in in H.
          unfold "#" in H0; intuition.
          apply remove_preserves_binds_notin in H; auto.
          apply remove_neq_preserves_binds; auto.
          apply Hmap; auto.
        destruct (eq_nat_dec pid0 pid).
          subst.
          apply ok_remove_notin; auto.
          apply remove_preserves_notin; auto.
          apply remove_neq_preserves_notin in H0; auto.
          apply Hmap; auto.
        unfold array_id_wf.
        apply remove_preserves_ok; auto.
  - rename H into Hmutual.
    rename H2 into Hvec.
    rename H0 into Hmap.
    rename H3 into Hreq.
    rename H4 into Hres.
    rename H6 into Hwf.
    inversion H1; subst; simpl in *.
    (* arycas *)
    --
    exists (@mkRawComposedState li_array li_array
              (array N) (identity li_array)
              (mkAryState N
                [] [] (if
            entry_eqb
              (Vector.nth vec (Fin.of_nat_lt Hlt)) old
           then
            Vector.replace vec (Fin.of_nat_lt Hlt) new
           else vec))
              (mkIdState li_array
                (substitute (substitute (buffer (RawL2State s2)) pid Pending) pid
          (@GetReply li_array
             (AryCASOk
              (entry_eqb (Vector.nth vec (Fin.of_nat_lt Hlt)) old))))
                (* ((pid, @GetReply li_array (AryCASOk
              (entry_eqb
                 (Vector.nth vec (Fin.of_nat_lt Hlt))
                 old)))::(remove (buffer (RawL2State s2)) pid))) *)
              )).
    simpl. intuition.
      destruct s2. simpl in *.
      destruct RawL1State; simpl in *.
      destruct RawL2State; simpl in *.
      subst.
      eapply Step_Internal; eauto.
      simpl.
      eapply linked_step_L2_push; eauto.
      simpl.
      eapply raw_composed_step_L2_push; eauto.
      simpl.
      eapply identity_at_external_query; eauto.
      eapply Hmap; eauto.
      simpl.
      eapply array_initial_state_cas with (inv:=[]) (res:=[]); eauto.
      apply notin_empty.
      apply notin_empty.
      econstructor.
      econstructor.
      eapply Step_Internal; eauto.
      simpl.
      eapply linked_step_int_L1; eauto.
      simpl.
      eapply raw_composed_step_L1_internal.
      2 : { eauto. }
      2 : { eauto. }
      simpl.
      eapply array_step_cas.
      5 : { eauto. }
      6 : { eauto. }
      econstructor; eauto.
      econstructor.
      apply notin_empty.
      econstructor.
      apply binds_push_eq; auto.
      apply notin_empty.
      eauto.
      eapply Step_Internal; eauto.
      simpl.
      eapply linked_step_L1_pop; eauto.
      simpl.
      eapply raw_composed_step_L1_pop; eauto.
      simpl.
      rewrite Nat.eqb_refl.
      eapply array_final_state_cas.
      4 : { eauto. }
      4 : { eauto. }
      econstructor.
      econstructor; eauto.
      econstructor.
      apply notin_empty.
      apply binds_push_eq; auto.
      simpl.
      eapply identity_after_external_reply.
      3 : { eauto. }
      3 : { eauto. }
      apply substitute_preserves_ok; auto.
      apply Hmap in Hbinds; auto.
      eapply substitute_eq_binds_v'; eauto.
      simpl.
      rewrite Nat.eqb_refl.
      eapply Step_None; eauto.
      unfold buffer_map'.
      simpl.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove inv pid)).
        apply ok_remove_notin; auto.
        apply binds_in in H.
        unfold "#" in H0; intuition.
        apply remove_preserves_binds_notin in H; auto.
        apply substitute_neq_preserves_binds; auto.
        apply substitute_neq_preserves_binds; auto.
        apply Hmap in H; auto.
      apply binds_push_inv in H.
      intuition.
        subst.
        apply Hmap in Hbinds; auto.
        eapply substitute_eq_binds_v'; eauto.
        eapply substitute_eq_binds_v'; eauto.
        apply substitute_neq_preserves_binds; auto.
        apply substitute_neq_preserves_binds; auto.
        apply Hmap; auto.
      apply notin_union in H0.
      intuition.
      apply substitute_preserves_notin; auto.
      apply substitute_preserves_notin; auto.
      apply notin_neq in H2.
      apply remove_neq_preserves_notin in H; auto.
      apply Hmap; auto.
      unfold array_id_wf.
      apply substitute_preserves_ok; auto.
      apply substitute_preserves_ok; auto.
    (* aryread *)
    --
    exists (@mkRawComposedState li_array li_array
              (array N) (identity li_array)
              (mkAryState N
                [] [] (vec
           )
           )
              (mkIdState li_array
                (substitute (substitute (buffer (RawL2State s2)) pid Pending) pid
          (@GetReply li_array
             (AryReadOk (Vector.nth vec (Fin.of_nat_lt Hlt)))))
                (* ((pid, @GetReply li_array (AryCASOk
              (entry_eqb
                 (Vector.nth vec (Fin.of_nat_lt Hlt))
                 old)))::(remove (buffer (RawL2State s2)) pid))) *)
              )).
    simpl. intuition.
      destruct s2. simpl in *.
      destruct RawL1State; simpl in *.
      destruct RawL2State; simpl in *.
      subst.
      eapply Step_Internal; eauto.
      simpl.
      eapply linked_step_L2_push; eauto.
      simpl.
      eapply raw_composed_step_L2_push; eauto.
      simpl.
      eapply identity_at_external_query; eauto.
      eapply Hmap; eauto.
      simpl.
      eapply array_initial_state_read with (inv:=[]) (res:=[]); eauto.
      apply notin_empty.
      apply notin_empty.
      econstructor.
      econstructor.
      eapply Step_Internal; eauto.
      simpl.
      eapply linked_step_int_L1; eauto.
      simpl.
      eapply raw_composed_step_L1_internal.
      2 : { eauto. }
      2 : { eauto. }
      simpl.
      eapply array_step_read.
      5 : { eauto. }
      6 : { eauto. }
      econstructor; eauto.
      econstructor.
      apply notin_empty.
      econstructor.
      apply binds_push_eq; auto.
      apply notin_empty.
      eauto.
      eapply Step_Internal; eauto.
      simpl.
      eapply linked_step_L1_pop; eauto.
      simpl.
      eapply raw_composed_step_L1_pop; eauto.
      simpl.
      rewrite Nat.eqb_refl.
      eapply array_final_state_read.
      4 : { eauto. }
      4 : { eauto. }
      econstructor.
      econstructor; eauto.
      econstructor.
      apply notin_empty.
      apply binds_push_eq; auto.
      simpl.
      eapply identity_after_external_reply.
      3 : { eauto. }
      3 : { eauto. }
      apply substitute_preserves_ok; auto.
      apply Hmap in Hbinds; auto.
      eapply substitute_eq_binds_v'; eauto.
      simpl.
      rewrite Nat.eqb_refl.
      eapply Step_None; eauto.
      unfold buffer_map'.
      simpl.
      intuition.
      destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove inv pid)).
        apply ok_remove_notin; auto.
        apply binds_in in H.
        unfold "#" in H0; intuition.
        apply remove_preserves_binds_notin in H; auto.
        apply substitute_neq_preserves_binds; auto.
        apply substitute_neq_preserves_binds; auto.
        apply Hmap in H; auto.
      apply binds_push_inv in H.
      intuition.
        subst.
        apply Hmap in Hbinds; auto.
        eapply substitute_eq_binds_v'; eauto.
        eapply substitute_eq_binds_v'; eauto.
        apply substitute_neq_preserves_binds; auto.
        apply substitute_neq_preserves_binds; auto.
        apply Hmap; auto.
      apply notin_union in H0.
      intuition.
      apply substitute_preserves_notin; auto.
      apply substitute_preserves_notin; auto.
      apply notin_neq in H2.
      apply remove_neq_preserves_notin in H; auto.
      apply Hmap; auto.
      unfold array_id_wf.
      apply substitute_preserves_ok; auto.
      apply substitute_preserves_ok; auto.
Qed.

End ArrayRefinement.
