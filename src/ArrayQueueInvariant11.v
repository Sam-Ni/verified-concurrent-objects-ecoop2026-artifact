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
Hypothesis H : L > 0.

Arguments get_pc {L}.
Arguments get_xp {L}.
Arguments get_ary {L}.
Arguments get_impl {L}.
Arguments get_rear {L}.
Arguments get_vec_rear {L}.

Lemma inv_vec_not_decrease: forall s s' acts i,
  new_valid_execution_fragment (composed_array_queue L) s s' acts ->
  composed_lts.reachable (composed_array_queue L) s ->
  snd 
  (Vector.nth
    ((get_ary s).(Array.vec L)) i) <=
  snd (Vector.nth
    ((get_ary s').(Array.vec L)) i).
Proof.
  induction 1; intros.
  - subst. lia.
  - intuition.
    eapply Nat.le_trans. eauto.
    clear H3.
    eapply reachable_valid_execution in H2; eauto.
    2 : {
      apply new_valid_execution_fragment_to_valid_execution_fragment; auto.
      eauto.
    }
    clear H1.
    inversion H0; subst; simpl in *.
    inversion H1; subst; simpl in *.
    unfold get_ary, get_impl in *; simpl in *.
    inversion H3; subst; simpl in *; auto.
    inversion H4; subst; simpl in *; auto.
    inversion H5; subst; simpl in *; auto.
    destruct (entry_eqb (Vector.nth vec (Fin.of_nat_lt Hlt)) old)eqn:Heq; auto.
    apply entry_eqb_eq in Heq.
    subst.
    pose proof H2 as Hreach.
    apply step_invariant in H2.
    unfold ComposedLTS.inv in H2.
    simpl in H2.
    eapply H2 in Hbinds0; eauto.
    clear acts.
    destruct Hbinds0 as [s1 [s2 [q [acts [Hint_query [Hvalid Hgather]]]]]].
    apply inv_ary_cas_at_e28_d28_invariant in Hreach.
    unfold inv_ary_cas_at_e28_d28 in Hreach.
    simpl in Hreach.
    pose proof Hbinds3 as Hbinds3Tmp.
    apply Hreach in Hbinds3.
    destruct Hbinds3 as [Hb3|Hb3].
    (* Enq *)
    -- unfold binds in Hb3.
      inversion Hint_query; subst; simpl in *.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
                Ltac tmp' H Hvalid st2 pid acts Hgather Hb3 :=
                apply valid_execution_fragment_com' in Hvalid;
                simpl in Hvalid;
                destruct st2; simpl in *;
  eapply valid_execution_fragment_sync in Hvalid; eauto;
  eapply H with (pid:=pid) in Hvalid; eauto;
  try (simpl; eapply substitute_eq_binds_v'; eauto);
  try (
      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil) by
      (rewrite Hgather; simpl; reflexivity);
      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B;
      assumption);
      (rewrite Hvalid in Hb3; discriminate).

  tmp' noB_preserves_AEnq2 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_AEnq5 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_AEnq11 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_AEnq14 Hvalid st2 pid acts Hgather Hb3.

  pose proof Hvalid as HvalidTmp;
                apply valid_execution_fragment_com' in Hvalid;
                simpl in Hvalid;
                destruct st2; simpl in *;
  eapply valid_execution_fragment_sync in Hvalid; eauto;
  eapply noB_preserves_AEnq28_combine with (pid:=pid) in Hvalid; eauto;
  try (simpl; eapply substitute_eq_binds_v'; eauto);
  try (
      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil) by
      (rewrite Hgather; simpl; reflexivity);
      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B;
      assumption).
  simpl in Hvalid.
  destruct Hvalid as [Hx [Hrear _]].
  inversion H7; subst; simpl in *.
  inversion H9; subst; simpl in *.
  inversion H11; subst; simpl in *.
  inversion H10; subst; simpl in *.
  apply valid_execution_fragment_com in HvalidTmp;
  simpl in HvalidTmp;
  eapply internal_preserves_request'' with (pid:=pid) in HvalidTmp; simpl in *; eauto;
  try apply binds_push_eq;
  try (eapply gather_pid_events_B_gather_pid_external_events;
      eassumption).
  inversion HvalidTmp; subst; simpl in *.
  assert (Htmp : (Fin.of_nat_lt Hlt) =
    (Fin.of_nat_lt (mod_lt H (rear pid)))).
  apply Fin.of_nat_ext.
  rewrite Htmp.
  rewrite Hrear.
  destruct (Fin.eq_dec (Fin.of_nat_lt (mod_lt H (ArrayQueueImpl.rear LState pid)))
    i).
    rewrite e.
    rewrite Vector.nth_replace_eq.
    simpl. rewrite H14.
    rewrite Htmp.
    rewrite Hrear.
    rewrite <-e.
    simpl in Hreach.
    lia.
    simpl in Hreach.
  rewrite Vector.nth_replace_neq; auto.
  tmp' noB_preserves_AEnq31 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_ADeq2 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_ADeq5 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_ADeq11 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_ADeq14 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_ADeq28 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_ADeq31 Hvalid st2 pid acts Hgather Hb3.
  (* Deq *)
    -- unfold binds in Hb3.
      inversion Hint_query; subst; simpl in *.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
  tmp' noB_preserves_AEnq2 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_AEnq5 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_AEnq11 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_AEnq14 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_AEnq28 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_AEnq31 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_ADeq2 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_ADeq5 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_ADeq11 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_ADeq14 Hvalid st2 pid acts Hgather Hb3.

  pose proof Hvalid as HvalidTmp;
                apply valid_execution_fragment_com' in Hvalid;
                simpl in Hvalid;
                destruct st2; simpl in *;
  eapply valid_execution_fragment_sync in Hvalid; eauto;
  eapply noB_preserves_ADeq28_combine with (pid:=pid) in Hvalid; eauto;
  try (simpl; eapply substitute_eq_binds_v'; eauto);
  try (
      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil) by
      (rewrite Hgather; simpl; reflexivity);
      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B;
      assumption).
  simpl in Hvalid.
  destruct Hvalid as [Hx Hrear].
  inversion H7; subst; simpl in *.
  inversion H9; subst; simpl in *.
  inversion H11; subst; simpl in *.
  inversion H10; subst; simpl in *.
  apply valid_execution_fragment_com in HvalidTmp;
  simpl in HvalidTmp;
  eapply internal_preserves_request'' with (pid:=pid) in HvalidTmp; simpl in *; eauto;
  try apply binds_push_eq;
  try (eapply gather_pid_events_B_gather_pid_external_events;
      eassumption).
  inversion HvalidTmp; subst; simpl in *.
  assert (Htmp : (Fin.of_nat_lt Hlt) =
    (Fin.of_nat_lt (mod_lt H (front pid)))).
  apply Fin.of_nat_ext.
  rewrite Htmp.
  rewrite Hrear.
  destruct (Fin.eq_dec (Fin.of_nat_lt (mod_lt H (ArrayQueueImpl.front LState pid)))
    i).
    rewrite e.
    rewrite Vector.nth_replace_eq.
    simpl. rewrite H14.
    rewrite Htmp.
    rewrite Hrear.
    rewrite <-e.
    simpl in Hreach.
    lia.
    simpl in Hreach.
  rewrite Vector.nth_replace_neq; auto.
  tmp' noB_preserves_ADeq31 Hvalid st2 pid acts Hgather Hb3.
  - intuition.
    eapply Nat.le_trans. eauto.
    clear H3.
    eapply reachable_valid_execution in H2; eauto.
    2 : {
      apply new_valid_execution_fragment_to_valid_execution_fragment; auto.
      eauto.
    }
    clear H1.
    inversion H0; subst; simpl in *.
    inversion H1; subst; simpl in *.
    unfold get_vec_rear in *; simpl in *.
    unfold get_ary, get_impl in *; simpl in *; auto.
  - inversion H0.
  - inversion H0.
  - intuition.
    eapply Nat.le_trans. eauto.
    clear H3.
    eapply reachable_valid_execution in H2; eauto.
    2 : {
      apply new_valid_execution_fragment_to_valid_execution_fragment; auto.
      eauto.
    }
    clear H1.
    inversion H0; subst; simpl in *.
    inversion H1; subst; simpl in *.
    unfold get_vec_rear in *; simpl in *.
    unfold get_ary, get_impl in *; simpl in *; auto.
  - intuition.
    eapply Nat.le_trans. eauto.
    clear H3.
    eapply reachable_valid_execution in H2; eauto.
    2 : {
      apply new_valid_execution_fragment_to_valid_execution_fragment; auto.
      eauto.
    }
    clear H1.
    inversion H0; subst; simpl in *.
    inversion H1; subst; simpl in *.
    unfold get_vec_rear in *; simpl in *.
    unfold get_ary, get_impl in *; simpl in *; auto.
  - intuition.
    eapply Nat.le_trans. eauto.
    clear H3.
    eapply reachable_valid_execution in H2; eauto.
    2 : {
      apply new_valid_execution_fragment_to_valid_execution_fragment; auto.
      eauto.
    }
    clear H1.
    inversion H0; subst; simpl in *.
    inversion H1; subst; simpl in *.
    unfold get_vec_rear in *; simpl in *.
    unfold get_ary, get_impl in *; simpl in *; auto.
    inversion H3; subst; simpl in *; auto.
    inversion H5; subst; simpl in *; auto.
    inversion H6; subst; simpl in *; auto.
    inversion H7; subst; simpl in *; auto.
  - intuition.
    eapply Nat.le_trans. eauto.
    clear H3.
    eapply reachable_valid_execution in H2; eauto.
    2 : {
      apply new_valid_execution_fragment_to_valid_execution_fragment; auto.
      eauto.
    }
    clear H1.
    inversion H0; subst; simpl in *.
    inversion H3; subst; simpl in *.
    unfold get_vec_rear in *; simpl in *.
    unfold get_ary, get_impl in *; simpl in *; auto.
    inversion H1; subst; simpl in *; auto.
    inversion H5; subst; simpl in *; auto.
    inversion H6; subst; simpl in *; auto.
    inversion H7; subst; simpl in *; auto.
Qed.

Lemma inv_vec_not_decrease': forall s s' acts i,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  composed_lts.reachable (composed_array_queue L) s ->
  snd 
  (Vector.nth
    ((get_ary s).(Array.vec L)) i) <=
  snd (Vector.nth
    ((get_ary s').(Array.vec L)) i).
Proof.
  intros.
  eapply inv_vec_not_decrease; eauto.
  eapply valid_execution_fragment_to_new_valid_execution_fragment; eauto.
Qed.

End test.

Section test.

Variable L : nat.

Arguments get_pc {L}.
Arguments get_xp {L}.
Arguments get_ary {L}.
Arguments get_impl {L}.
Arguments get_rear {L}.
Arguments get_vec_rear {L}.

Definition e5_or_e6 v ret :=
  v = AEnq5 \/
  v = (AEnq6 ret).

Definition calculate_before6 v :=
  match v with
  | AEnq1 => 4
  | AEnq2 => 3
  | AEnq3 r => 2
  | AEnq4 => 2
  | AEnq5 => 1
  | AEnq6 r => 0
  | AEnq10 => 6
  | AEnq11 => 5
  | AEnq12 r => 4
  | AEnq13 => 6
  | AEnq14 => 5
  | AEnq15 r => 4
  | AEnq26 => 4
  | AEnq27 => 6
  | AEnq28 => 5
  | AEnq29 r => 4
  | AEnq30 => 4
  | AEnq31 => 4
  | AEnq32 => 4
  | _ => 0
  end.

Lemma e5_or_e6_Enq5: forall ret,
  e5_or_e6 AEnq5 ret.
Proof.
  intros.
  unfold e5_or_e6. intuition.
Qed.

Lemma e5_or_e6_Enq6: forall ret,
  e5_or_e6 (AEnq6 ret) ret.
Proof.
  intros.
  unfold e5_or_e6. intuition.
Qed.

Ltac solve_e5_or_e6 :=
  try apply e5_or_e6_Enq5;
  try apply e5_or_e6_Enq6.

Lemma inv_e10_e6: forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  binds pid (AEnq10) (get_pc s) ->
  binds pid (AEnq6 ret) (get_pc s') ->
  length (gather_pid_events_B pid acts) > 0.
Proof.
  induction 1; intros.
  - subst. unfold binds in H0.
    rewrite H1 in H0; discriminate.
  (* - destruct (eq_nat_dec pid pid0). *)
  - inversion H; subst; simpl in *.
    inversion H3; subst; simpl in *.
    unfold get_pc in *; simpl in *.
    intuition.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      inversion H4; subst; simpl in *;
      rewrite Hbinds0 in H1; discriminate.
    -- inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      apply IHvalid_execution_fragment; auto.
      inversion H4; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - inversion H.
  - inversion H.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      rewrite Nat.eqb_refl.
      unfold get_pc in *; simpl in *.
      apply binds_in in H1.
      inversion H4; subst; simpl in *;
      unfold "#" in Hnotin_pc; intuition.
    -- inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      apply IHvalid_execution_fragment in H2; auto.
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H4; subst; simpl in *;
      apply binds_push_neq; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      rewrite Nat.eqb_refl.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      inversion H4; subst; simpl in *;
      rewrite Hbinds0 in H1; discriminate.
    -- inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      apply IHvalid_execution_fragment in H2; auto.
      apply Nat.eqb_neq in n; rewrite n; auto.
      unfold binds in H1.
      inversion H4; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      rewrite Nat.eqb_refl.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      inversion H5; subst; simpl in *;
      try (rewrite Hbinds0 in H1; discriminate).
      lia.
    -- inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      apply IHvalid_execution_fragment in H2; auto.
      apply Nat.eqb_neq in n; rewrite n; auto.
      unfold binds in H1.
      inversion H5; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      rewrite Nat.eqb_refl.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      inversion H5; subst; simpl in *;
      try (rewrite Hbinds0 in H1; discriminate).
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      apply IHvalid_execution_fragment in H2; auto.
      apply Nat.eqb_neq in n; rewrite n; auto.
      unfold binds in H1.
      inversion H5; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
Qed.

Lemma inv_e6_stuttering : forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  binds pid (AEnq6 ret) (get_pc s) ->
  length (gather_pid_events_B pid acts) = 0 ->
  binds pid (AEnq6 ret) (get_pc s') \/
  binds pid AEnq10 (get_pc s').
Proof.
  induction 1; simpl; intros.
  - subst. intuition.
  - unfold get_pc in *; simpl in *.
    inversion H; subst; simpl in *.
    intuition.
  - destruct (eq_nat_dec pid0 pid).
    -- subst.
      unfold get_pc in *; intros.
      inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      unfold binds in H1.
      inversion H4; subst; simpl in *.
      all : try (rewrite Hbinds0 in H1; discriminate).
      eapply inv_e10_stuttering in H0; eauto;
      unfold get_pc; simpl; auto.
      eapply substitute_eq_binds_v'; eauto.
    -- inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      inversion H4; subst; simpl in *;
      apply IHvalid_execution_fragment; auto;
      apply substitute_neq_preserves_binds; auto.
  - inversion H; subst.
  - inversion H; subst.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      unfold get_pc in *; intros.
      inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      apply binds_in in H1.
      inversion H4; subst; simpl in *;
      unfold "#" in Hnotin_pc; intuition.
    -- inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      inversion H4; subst; simpl in *;
      apply IHvalid_execution_fragment; auto.
      apply binds_push_neq; auto.
      apply Nat.eqb_neq in n; rewrite n in H2; auto.
      apply binds_push_neq; auto.
      apply Nat.eqb_neq in n; rewrite n in H2; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      unfold get_pc in *; intros.
      inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      unfold binds in H1.
      inversion H4; subst; simpl in *;
      rewrite Hbinds0 in H1; discriminate.
    -- inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      inversion H4; subst; simpl in *;
      apply IHvalid_execution_fragment; auto.
      apply remove_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H2; auto.
      apply remove_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H2; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      unfold get_pc in *; intros.
      inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      unfold binds in H1.
      inversion H5; subst; simpl in *;
      rewrite Hbinds0 in H1; discriminate.
    -- inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      inversion H5; subst; simpl in *.
      all : apply IHvalid_execution_fragment; auto;
      [apply substitute_neq_preserves_binds; auto|
      apply Nat.eqb_neq in n; rewrite n in H2; auto].
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      unfold get_pc in *; intros.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold binds in H1.
      inversion H5; subst; simpl in *;
      rewrite Hbinds0 in H1; discriminate.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      inversion H5; subst; simpl in *.
      all : apply IHvalid_execution_fragment; auto;
      [apply substitute_neq_preserves_binds; auto|
      apply Nat.eqb_neq in n; rewrite n in H2; auto].
Qed.

Lemma inv_impl_rear_keep': forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s' acts ->
  forall v (Hv : e5_or_e6 v ret),
  binds pid v (get_pc s) ->
  length (gather_pid_events_B pid acts) = calculate_before6 v ->
  binds pid (AEnq6 ret) (get_pc s') ->
  (get_impl s).(ArrayQueueImpl.rear) pid = (get_impl s').(ArrayQueueImpl.rear) pid.
Proof.
  induction 1; intros.
  - subst. auto.
  - inversion H; subst; simpl in *.
    inversion H4; subst; simpl in *.
    unfold get_impl, get_pc in *; simpl in *.
    eapply IHvalid_execution_fragment; eauto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_impl, get_pc in *; simpl in *.
      unfold binds in H1.
      unfold e5_or_e6 in Hv.
      inversion H5; subst; simpl in *;
      rewrite Hbinds0 in H1; intuition; subst; try discriminate.
      eapply inv_e10_e6 in H0; eauto.
      simpl in H2; lia.
      unfold get_pc; simpl.
      eapply substitute_eq_binds_v'; eauto.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_impl, get_pc in *; simpl in *.
      erewrite <-IHvalid_execution_fragment; eauto.
      inversion H5; subst; simpl in *.
      apply Nat.eqb_neq in n; rewrite n.
      all : try reflexivity.
      inversion H5; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - inversion H.
  - inversion H.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_impl, get_pc in *; simpl in *.
      apply binds_in in H1.
      inversion H5; subst; simpl in *;
      unfold "#" in Hnotin_pc; intuition.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_impl, get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
      2 : {
        inversion H5; subst; simpl in *;
        apply binds_push_neq; auto.
      }
      inversion H5; subst; simpl in *;
      rewrite H3; auto.
      apply Nat.eqb_neq in n; rewrite n in H2;
      rewrite H2; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_impl, get_pc in *; simpl in *.
      unfold binds in H1.
      inversion H5; subst; simpl in *;
      rewrite Hbinds0 in H1;
      inversion H1; subst;
      unfold e5_or_e6 in Hv;
      intuition; subst; try discriminate;
      try (destruct H6; subst; discriminate);
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate).
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_impl, get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
      2 : {
        inversion H5; subst; simpl in *;
        apply remove_neq_preserves_binds; auto.
      }
      inversion H5; subst; simpl in *;
      rewrite H3; auto.
      apply Nat.eqb_neq in n; rewrite n in H2;
      rewrite H2; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_impl, get_pc in *; simpl in *.
      unfold binds in H1.
      rewrite Nat.eqb_refl in H2.
      simpl in H2.
      inversion H6; subst; simpl in *;
      rewrite Hbinds0 in H1; inversion H1; subst;
      unfold e5_or_e6 in Hv;
      intuition; subst; discriminate.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_impl, get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
      2 : {
        inversion H6; subst; simpl in *;
        apply substitute_neq_preserves_binds; auto.
      }
      inversion H6; subst; simpl in *;
      rewrite H3; auto.
      apply Nat.eqb_neq in n; rewrite n in H2;
      rewrite H2; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_impl, get_pc in *; simpl in *.
      unfold binds in H1.
      rewrite Nat.eqb_refl in H2.
      simpl in H2.
      inversion H6; subst; simpl in *;
      rewrite Hbinds0 in H1;
      inversion H1; subst;
      unfold e5_or_e6 in Hv; intuition; try discriminate.
      simpl in H2. inversion H2; subst.
      erewrite <-IHvalid_execution_fragment; eauto;
      try (eapply substitute_eq_binds_v'; eauto);
      solve_e5_or_e6; simpl; auto.
      eapply inv_e6_stuttering in H0; eauto;
      unfold get_pc; simpl;
      try (eapply substitute_eq_binds_v'; eauto).
      intuition.
      unfold binds in H3.
      rewrite H8 in H3.
      inversion H3; subst; solve_e5_or_e6.
      unfold binds in H3.
      rewrite H8 in H3; discriminate.
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_impl, get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
      2 : {
        inversion H6; subst; simpl in *;
        apply substitute_neq_preserves_binds; auto.
      }
      inversion H6; subst; simpl in *;
      rewrite H3; auto.
      apply Nat.eqb_neq in n; rewrite n in H2;
      rewrite H2; auto.
Qed.

End test.

Section test.

Variable L : nat.
Hypothesis H : L > 0.

Arguments get_pc {L}.
Arguments get_xp {L}.
Arguments get_ary {L}.
Arguments get_impl {L}.
Arguments get_rear {L}.
Arguments get_vec_rear {L}.

Lemma inv_xp_ref_le_vec_rear_ref : forall k s,
  reachable_len' (composed_array_queue L) s k ->
  forall pid v (Hv : after_e6 v) (Hb : binds pid v (get_pc s)),
    snd ((get_xp s) pid) <= snd (get_vec_rear H s pid).
Proof.
  induction k; intros.
  - unfold reachable_len' in H0.
    destruct H0 as [init [acts [Hnew Hvalid]]].
    inversion Hvalid; subst.
    inversion Hnew; subst.
    inversion H0; subst.
    inversion H1; subst.
    inversion H2; subst.
    inversion H4; subst; simpl in *.
    inversion H6; subst; simpl in *.
    inversion H7; subst; simpl in *.
    inversion H8; subst; simpl in *.
    inversion H11; subst; simpl in *.
    inversion H13; subst; simpl in *.
    inversion H15; subst; simpl in *.
    inversion H16; subst; simpl in *.
    inversion H18; subst; simpl in *.
    unfold get_xp, get_vec_rear; simpl in *.
    unfold get_ary, get_impl; simpl in *.
    rewrite H9.
    rewrite H14.
    unfold new_array_queue.
    unfold new_array.
    simpl. lia.
  - apply reachable_len_reconstruct in H0.
    destruct H0 as [st [acts [Hreach Hstep]]].
    inversion Hstep; subst; clear Hstep.
    -- inversion H3; subst; clear H3.
      pose proof Hreach as HreachTmp.
      (* eapply IHk with (pid:=pid) in Hreach; eauto. *)
      inversion H1; subst; simpl in *.
      inversion H0; subst; simpl in *.
      unfold get_xp, get_vec_rear in *; simpl in *.
      unfold get_ary, get_impl in *; simpl in *.
      inversion H2; subst; simpl in *; auto.
      (* front_rear *)
      * inversion H3; subst; simpl in *; auto.
        eapply IHk with (pid:=pid) in Hreach; eauto.
      *
      inversion H3; subst; simpl in *; auto.
        eapply IHk with (pid:=pid) in Hreach; eauto.
      inversion H4; subst; simpl in *; auto.
      destruct (entry_eqb (Vector.nth vec (Fin.of_nat_lt Hlt)) old)eqn:Heq; auto.
      apply entry_eqb_eq in Heq. subst.
      pose proof Hbinds3 as Hbind3Tmp.
      apply reachable_len_to_reachable in HreachTmp.
      pose proof HreachTmp as HreachTmp2.
      apply inv_ary_cas_at_e28_d28_invariant in HreachTmp2.
      unfold inv_ary_cas_at_e28_d28 in HreachTmp2.
      simpl in HreachTmp2.
      apply HreachTmp2 in Hbind3Tmp; auto.
      destruct Hbind3Tmp as [H31|H31].
      (* Enq *)
      --- clear HreachTmp2.
        apply step_invariant in HreachTmp.
        unfold ComposedLTS.inv in HreachTmp.
        simpl in HreachTmp.
        apply HreachTmp in Hbinds0; auto.
        destruct Hbinds0 as [s1 [s2 [q [acts [Hint_query [Hvalid Hgather]]]]]].
        inversion Hint_query; subst; simpl in *.
        inversion H5; subst; simpl in *.
        unfold binds in H31.
        inversion H7; subst; simpl in *.

                Ltac tmp' H Hvalid st2 pid0 acts Hgather H31 :=
                apply valid_execution_fragment_com' in Hvalid;
                simpl in Hvalid;
                destruct st2; simpl in *;
  eapply valid_execution_fragment_sync in Hvalid; eauto;
  eapply H with (pid:=pid0) in Hvalid; eauto;
  try (simpl; eapply substitute_eq_binds_v'; eauto);
  try (
      assert (clts_events_B_to_events_B (gather_pid_events_B pid0 acts) = nil) by
      (rewrite Hgather; simpl; reflexivity);
      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B;
      assumption);
      (rewrite Hvalid in H31; discriminate).
  tmp' noB_preserves_AEnq2 Hvalid st2 pid0 acts Hgather H31.
  tmp' noB_preserves_AEnq5 Hvalid st2 pid0 acts Hgather H31.
  tmp' noB_preserves_AEnq11 Hvalid st2 pid0 acts Hgather H31.
  tmp' noB_preserves_AEnq14 Hvalid st2 pid0 acts Hgather H31.

  pose proof Hvalid as HvalidTmp;
                apply valid_execution_fragment_com' in Hvalid;
                simpl in Hvalid;
                destruct st2; simpl in *;
  eapply valid_execution_fragment_sync in Hvalid; eauto;
  eapply noB_preserves_AEnq28_combine with (pid:=pid0) in Hvalid; eauto;
  try (simpl; eapply substitute_eq_binds_v'; eauto);
  try (
      assert (clts_events_B_to_events_B (gather_pid_events_B pid0 acts) = nil) by
      (rewrite Hgather; simpl; reflexivity);
      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B;
      assumption).
  simpl in Hvalid.
  destruct Hvalid as [Hx [Hrear _]].
  inversion H6; subst; simpl in *.
  inversion H8; subst; simpl in *.
  inversion H10; subst; simpl in *.
  inversion H9; subst; simpl in *.
  apply valid_execution_fragment_com in HvalidTmp;
  simpl in HvalidTmp;
  eapply internal_preserves_request'' with (pid:=pid0) in HvalidTmp; simpl in *; eauto;
  try apply binds_push_eq;
  try (eapply gather_pid_events_B_gather_pid_external_events;
      eassumption).
  inversion HvalidTmp; subst; simpl in *.
  assert (Htmp : (Fin.of_nat_lt Hlt) =
    (Fin.of_nat_lt (mod_lt H (rear pid0)))).
  apply Fin.of_nat_ext.
  rewrite Htmp.
  rewrite Hrear.
  destruct (Fin.eq_dec (Fin.of_nat_lt (mod_lt H (ArrayQueueImpl.rear LState pid)))
    (Fin.of_nat_lt (mod_lt H (ArrayQueueImpl.rear LState pid0)))).
    rewrite e.
    rewrite Vector.nth_replace_eq.
    simpl. rewrite H13.
    rewrite Htmp.
    rewrite Hrear.
    rewrite <-e.
    simpl in Hreach.
    lia.
    simpl in Hreach.
  rewrite Vector.nth_replace_neq; auto.
  tmp' noB_preserves_AEnq31 Hvalid st2 pid0 acts Hgather H31.
  tmp' noB_preserves_ADeq2 Hvalid st2 pid0 acts Hgather H31.
  tmp' noB_preserves_ADeq5 Hvalid st2 pid0 acts Hgather H31.
  tmp' noB_preserves_ADeq11 Hvalid st2 pid0 acts Hgather H31.
  tmp' noB_preserves_ADeq14 Hvalid st2 pid0 acts Hgather H31.
  tmp' noB_preserves_ADeq28 Hvalid st2 pid0 acts Hgather H31.
  tmp' noB_preserves_ADeq31 Hvalid st2 pid0 acts Hgather H31.
      (* Deq *)
      --- clear HreachTmp2.
        apply step_invariant in HreachTmp.
        unfold ComposedLTS.inv in HreachTmp.
        simpl in HreachTmp.
        apply HreachTmp in Hbinds0; auto.
        destruct Hbinds0 as [s1 [s2 [q [acts [Hint_query [Hvalid Hgather]]]]]].
        inversion Hint_query; subst; simpl in *.
        inversion H5; subst; simpl in *.
        unfold binds in H31.
        inversion H7; subst; simpl in *.

  tmp' noB_preserves_AEnq2 Hvalid st2 pid0 acts Hgather H31.
  tmp' noB_preserves_AEnq5 Hvalid st2 pid0 acts Hgather H31.
  tmp' noB_preserves_AEnq11 Hvalid st2 pid0 acts Hgather H31.
  tmp' noB_preserves_AEnq14 Hvalid st2 pid0 acts Hgather H31.
  tmp' noB_preserves_AEnq28 Hvalid st2 pid0 acts Hgather H31.
  tmp' noB_preserves_AEnq31 Hvalid st2 pid0 acts Hgather H31.
  tmp' noB_preserves_ADeq2 Hvalid st2 pid0 acts Hgather H31.
  tmp' noB_preserves_ADeq5 Hvalid st2 pid0 acts Hgather H31.
  tmp' noB_preserves_ADeq11 Hvalid st2 pid0 acts Hgather H31.
  tmp' noB_preserves_ADeq14 Hvalid st2 pid0 acts Hgather H31.

  pose proof Hvalid as HvalidTmp;
                apply valid_execution_fragment_com' in Hvalid;
                simpl in Hvalid;
                destruct st2; simpl in *;
  eapply valid_execution_fragment_sync in Hvalid; eauto;
  eapply noB_preserves_ADeq28_combine with (pid:=pid0) in Hvalid; eauto;
  try (simpl; eapply substitute_eq_binds_v'; eauto);
  try (
      assert (clts_events_B_to_events_B (gather_pid_events_B pid0 acts) = nil) by
      (rewrite Hgather; simpl; reflexivity);
      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B;
      assumption).
  simpl in Hvalid.
  destruct Hvalid as [Hx Hrear].
  inversion H6; subst; simpl in *.
  inversion H8; subst; simpl in *.
  inversion H10; subst; simpl in *.
  inversion H9; subst; simpl in *.
  apply valid_execution_fragment_com in HvalidTmp;
  simpl in HvalidTmp;
  eapply internal_preserves_request'' with (pid:=pid0) in HvalidTmp; simpl in *; eauto;
  try apply binds_push_eq;
  try (eapply gather_pid_events_B_gather_pid_external_events;
      eassumption).
  inversion HvalidTmp; subst; simpl in *.
  assert (Htmp : (Fin.of_nat_lt Hlt) =
    (Fin.of_nat_lt (mod_lt H (front pid0)))).
  apply Fin.of_nat_ext.
  rewrite Htmp.
  rewrite Hrear.
  destruct (Fin.eq_dec (Fin.of_nat_lt (mod_lt H (ArrayQueueImpl.front LState pid0)))
    (Fin.of_nat_lt (mod_lt H (ArrayQueueImpl.rear LState pid)))).
    rewrite e.
    rewrite Vector.nth_replace_eq.
    simpl. rewrite H13.
    rewrite Htmp.
    rewrite Hrear.
    rewrite e.
    simpl in Hreach.
    lia.
    simpl in Hreach.
  rewrite Vector.nth_replace_neq; auto.
  tmp' noB_preserves_ADeq31 Hvalid st2 pid0 acts Hgather H31.
  -- inversion H3; subst; simpl in *; clear H3.
    destruct (eq_nat_dec pid pid0).
    --- subst.
      inversion H1; subst; simpl in *.
      inversion H0; subst; simpl in *.
      unfold get_xp, get_vec_rear in *; simpl in *.
      unfold get_ary, get_impl, get_pc in *; simpl in *.
      unfold binds in Hb.
      inversion H2; subst; simpl in *.
      eapply substitute_eq_binds_v' in Hbinds0; eauto;
      rewrite Hbinds0 in Hb; try discriminate;
      unfold after_e6 in Hv;
      intuition; subst; try discriminate;
      try (destruct H3; subst; discriminate);
      try (destruct H4; subst; discriminate).
      rewrite Nat.eqb_refl.
      eapply inv_e6_ret_e5_internal_step with (v:=AEnq6 ret) (pid:=pid0) in Hreach; eauto.
      2 : {
        unfold has_read_ary. simpl. intuition.
      }
      destruct Hreach as [s1 [s2 [acts [n [Hvalid [Hstep [Hb1 [Hgather [Hreach' Hlt]]]]]]]]].
      inversion Hstep; subst; simpl in *.
      inversion H3; subst; simpl in *.
      inversion H4; subst; simpl in *.
      inversion H6; subst; simpl in *.
      inversion H5; subst; simpl in *.
      simpl in Hgather.
      pose proof Hvalid as HvalidTmp.
      eapply inv_e5_ret_e6_ret in Hvalid; eauto.
      2 : {
        unfold get_ary; simpl in *.
        apply binds_push_eq; auto.
      }
      rewrite <-Hvalid.
      pose proof Hstep as HstepTmp.
      apply inv_e5_instant with (k:=n) in Hstep; auto.
      simpl in Hstep.
      unfold get_impl in *; simpl in *.
      unfold binds in Hbinds5.
      rewrite Hstep in Hbinds5.
      inversion Hbinds5; subst; simpl in *.
      assert (Htmp : (Fin.of_nat_lt Hlt0) =
        (Fin.of_nat_lt (mod_lt H (ArrayQueueImpl.rear (LState st2) pid0)))).
      apply Fin.of_nat_ext.
      rewrite Htmp.
Ltac solve_e5_or_e6 :=
  try apply e5_or_e6_Enq5;
  try apply e5_or_e6_Enq6.
      pose proof HvalidTmp as HvalidTmp2.
      eapply inv_impl_rear_keep' with (pid:=pid0) in HvalidTmp; eauto; simpl; auto; solve_e5_or_e6.
      unfold get_impl in *; simpl in *.
      rewrite HvalidTmp.
      apply reachable_len_to_reachable in Hreach'.
      eapply inv_vec_not_decrease' in HvalidTmp2; eauto.
      eapply reachable_valid_execution; eauto.
      eapply composed_lts.Step_Internal_L1; eauto.
      eapply composed_lts.Step_None; eauto.

      all : pose proof Hbinds0 as Hbinds0Tmp;
      eapply substitute_eq_binds_v' in Hbinds0; eauto;
      rewrite Hbinds0 in Hb; try discriminate;
      unfold after_e6 in Hv;
      intuition; subst; try discriminate;
      try (destruct H3; subst; discriminate);
      try (destruct H4; subst; discriminate);
      try (destruct H5; subst; discriminate).

Ltac solve_after_e6 :=
  try apply after_e6_Enq10;
  try apply after_e6_Enq11;
  try apply after_e6_Enq12;
  try apply after_e6_Enq13;
  try apply after_e6_Enq14;
  try apply after_e6_Enq15;
  try apply after_e6_Enq26;
  try apply after_e6_Enq27.

      all : eapply IHk in Hreach; eauto;
      simpl; solve_after_e6.
    --- inversion H1; subst; simpl in *.
      inversion H0; subst; simpl in *.
      unfold get_xp, get_vec_rear in *; simpl in *.
      unfold get_ary, get_impl, get_pc in *; simpl in *.
      inversion H2; subst; simpl in *.

      all : try (apply substitute_neq_preserves_binds' in Hb; auto;
      apply Nat.eqb_neq in n; rewrite n;
      eapply IHk in Hreach; eauto;
      simpl; auto).
      all : try (apply substitute_neq_preserves_binds' in Hb; auto;
      eapply IHk in Hreach; eauto;
      simpl; auto).

  -- inversion H1.
  -- inversion H1.
  -- inversion H3; subst; clear H3.
    eapply IHk with (pid:=pid) in Hreach; eauto.
    inversion H1; subst; simpl in *.
    inversion H0; subst; simpl in *.
    unfold get_xp, get_vec_rear in *; simpl in *.
    unfold get_ary, get_impl in *; simpl in *.
    inversion H2; subst; simpl in *; auto.
    inversion H1; subst; simpl in *.
    inversion H0; subst; simpl in *.
    unfold get_pc in *; simpl in *.
    inversion H2; subst; simpl in *; auto;
    apply binds_push_inv in Hb; auto;
    intuition; subst;
    unfold after_e6 in Hv;
    intuition; subst; try discriminate;
    try (destruct H3; subst; discriminate);
    try (destruct H4; subst; discriminate).
  -- inversion H3; subst; clear H3.
    eapply IHk with (pid:=pid) in Hreach; eauto.
    inversion H1; subst; simpl in *.
    inversion H0; subst; simpl in *.
    unfold get_xp, get_vec_rear in *; simpl in *.
    unfold get_ary, get_impl in *; simpl in *.
    inversion H2; subst; simpl in *; auto.
    inversion H1; subst; simpl in *.
    inversion H0; subst; simpl in *.
    unfold get_pc in *; simpl in *.
    destruct (eq_nat_dec pid pid0).
    subst.
    inversion H2; subst; simpl in *; auto;
      assert (Htmp : pid0 # (remove pc pid0)) by
      (apply ok_remove_notin; auto);
      apply binds_in in Hb;
      unfold "#" in Htmp; intuition.
    inversion H2; subst; simpl in *; auto;
    apply remove_preserves_binds_notin in Hb; auto.
  -- inversion H3; subst; clear H3.
    destruct (eq_nat_dec pid pid0).
    --- subst.
    inversion H1; subst; simpl in *.
    inversion H0; subst; simpl in *.
    unfold get_xp, get_vec_rear in *; simpl in *.
    unfold get_ary, get_impl, get_pc in *; simpl in *.
    unfold binds in Hb.
    inversion H3; subst; simpl in *; auto.
    all : pose proof Hbinds0 as HbindsTmp;
    eapply substitute_eq_binds_v' in Hbinds0;
    rewrite Hbinds0 in Hb;
    inversion Hb; subst;
    unfold after_e6 in Hv; intuition; subst; try discriminate;
    try (destruct H4; subst; discriminate);
    try (destruct H5; subst; discriminate).
    
    all : eapply IHk with (pid:=pid0) in Hreach; eauto; solve_after_e6;
    simpl in Hreach; auto; simpl;
    inversion H2; subst; simpl in *; auto;
    inversion H4; subst; simpl in *; auto;
    inversion H5; subst; simpl in *; auto;
    inversion H7; subst; simpl in *; auto;
    inversion H6; subst; simpl in *; auto.
    --- eapply IHk with (pid:=pid) in Hreach; eauto.
      inversion H1; subst; simpl in *.
      inversion H0; subst; simpl in *.
    unfold get_xp, get_vec_rear in *; simpl in *.
    unfold get_ary, get_impl, get_pc in *; simpl in *.
      inversion H3; subst; simpl in *;
      inversion H2; subst; simpl in *; auto;
      inversion H4; subst; simpl in *; auto;
      inversion H6; subst; simpl in *; auto;
      inversion H5; subst; simpl in *; auto.

      inversion H1; subst; simpl in *.
      inversion H0; subst; simpl in *.
    unfold get_xp, get_vec_rear in *; simpl in *.
    unfold get_ary, get_impl, get_pc in *; simpl in *.
      inversion H3; subst; simpl in *;
      apply substitute_neq_preserves_binds' in Hb; auto.
  -- inversion H3; subst; clear H3.
    destruct (eq_nat_dec pid pid0).
    --- subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    unfold get_xp, get_vec_rear in *; simpl in *.
    unfold get_ary, get_impl, get_pc in *; simpl in *.
    unfold binds in Hb.
    inversion H3; subst; simpl in *; auto.
    all : pose proof Hbinds0 as HbindsTmp;
    eapply substitute_eq_binds_v' in Hbinds0;
    rewrite Hbinds0 in Hb;
    inversion Hb; subst;
    unfold after_e6 in Hv; intuition; subst; try discriminate;
    try (destruct H4; subst; discriminate);
    try (destruct H5; subst; discriminate).
    
    all : eapply IHk with (pid:=pid0) in Hreach; eauto; solve_after_e6;
    simpl in Hreach; auto; simpl;
    inversion H0; subst; simpl in *; auto;
    inversion H4; subst; simpl in *; auto;
    inversion H5; subst; simpl in *; auto.
    --- eapply IHk with (pid:=pid) in Hreach; eauto.
      inversion H1; subst; simpl in *.
      inversion H2; subst; simpl in *.
    unfold get_xp, get_vec_rear in *; simpl in *.
    unfold get_ary, get_impl, get_pc in *; simpl in *.
      inversion H3; subst; simpl in *;
      inversion H0; subst; simpl in *; auto;
      inversion H4; subst; simpl in *; auto;
      inversion H6; subst; simpl in *; auto;
      inversion H5; subst; simpl in *; auto.

      inversion H1; subst; simpl in *.
      inversion H2; subst; simpl in *.
    unfold get_xp, get_vec_rear in *; simpl in *.
    unfold get_ary, get_impl, get_pc in *; simpl in *.
      inversion H3; subst; simpl in *;
      apply substitute_neq_preserves_binds' in Hb; auto.
Qed.

Lemma inv_xp_ref_le_vec_rear_ref_invariant:
  composed_lts.invariant (composed_array_queue L)
  (fun s => forall pid v (Hv : after_e6 v) (Hb : binds pid v (get_pc s)),
    snd ((get_xp s) pid) <= snd (get_vec_rear H s pid)).
Proof.
  apply reachable_len'_to_invariant; eauto.
  intros.
  eapply inv_xp_ref_le_vec_rear_ref; eauto.
Qed.

Lemma inv_vec_rear_ref_not_decrease : forall s s' acts i
  (Hreach : composed_lts.reachable (composed_array_queue L) s),
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  snd (Vector.nth
    ((get_ary s).(Array.vec L)) i) <= 
  snd (Vector.nth
    ((get_ary s').(Array.vec L)) i).
Proof.
  induction 2; intros.
  - subst. lia.
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Internal_L1; eauto;
    eapply composed_lts.Step_None; eauto.
    specialize (IHvalid_execution_fragment Htmp).
    eapply Nat.le_trans.
    2 : { eauto. }
    clear IHvalid_execution_fragment.
    clear Htmp.
    clear H1.
    inversion H0; subst; simpl in *.
    inversion H1; subst; simpl in *.
    unfold get_ary; simpl.
    inversion H2; subst; simpl in *; auto.
    inversion H3; subst; simpl in *; auto.
    inversion H4; subst; simpl in *; auto.
    destruct (entry_eqb (Vector.nth vec (Fin.of_nat_lt Hlt)) old)eqn:Heq; auto.
    apply entry_eqb_eq in Heq; subst.
    pose proof Hreach as HreachTmp.
    apply inv_ary_cas_at_e28_d28_invariant in Hreach.
    unfold inv_ary_cas_at_e28_d28 in Hreach.
    simpl in Hreach.
    pose proof Hbinds3 as HbindsTmp.
    apply Hreach in Hbinds3; auto.
    destruct Hbinds3 as [Hb|Hb].
    (* e28 *)
    -- apply step_invariant in HreachTmp.
      unfold ComposedLTS.inv in HreachTmp.
      simpl in HreachTmp.
      apply HreachTmp in Hbinds0; auto.
                destruct Hbinds0 as [s1 [s2 [q [acts' [Hint_query [Hvalid Hgather]]]]]].
                inversion Hint_query; subst; simpl in *.
                inversion H5; subst; simpl in *.
                unfold binds in Hb.
                inversion H7; subst; simpl in *.
                Ltac tmp H Hvalid st2 pid acts' Hgather Hb :=
                (
                apply valid_execution_fragment_com' in Hvalid;
                simpl in Hvalid;
                destruct st2; simpl in *;
  eapply valid_execution_fragment_sync in Hvalid; eauto;
  eapply H with (pid:=pid) in Hvalid; eauto;
  try (simpl; eapply substitute_eq_binds_v'; eauto);
  try (
      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts') = nil) by
      (rewrite Hgather; simpl; reflexivity);
      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B;
      assumption);
      (rewrite Hvalid in Hb; discriminate)).
  tmp noB_preserves_AEnq2 Hvalid st2 pid acts' Hgather Hb.
  tmp noB_preserves_AEnq5 Hvalid st2 pid acts' Hgather Hb.
  tmp noB_preserves_AEnq11 Hvalid st2 pid acts' Hgather Hb.
  tmp noB_preserves_AEnq14 Hvalid st2 pid acts' Hgather Hb.
  pose proof Hvalid as HvalidTmp';
                apply valid_execution_fragment_com' in Hvalid;
                simpl in Hvalid;
                destruct st2; simpl in *;
  eapply valid_execution_fragment_sync in Hvalid; eauto;
  eapply noB_preserves_AEnq28_combine with (pid:=pid) in Hvalid; eauto;
  try (simpl; eapply substitute_eq_binds_v'; eauto);
  try (
      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts') = nil) by
      (rewrite Hgather; simpl; reflexivity);
      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B;
      assumption).
  simpl in Hvalid.
  destruct Hvalid as [Hx [Hrear _]].
  inversion H6; subst; simpl in *.
  inversion H8; subst; simpl in *.
  inversion H10; subst; simpl in *.
  inversion H9; subst; simpl in *.
  apply valid_execution_fragment_com in HvalidTmp';
  simpl in HvalidTmp';
  eapply internal_preserves_request'' with (pid:=pid) in HvalidTmp'; simpl in *; eauto;
  try apply binds_push_eq;
  try (eapply gather_pid_events_B_gather_pid_external_events;
      eassumption).
  inversion HvalidTmp'; subst; simpl in *.
  assert (Htmp : (Fin.of_nat_lt Hlt) =
    (Fin.of_nat_lt (mod_lt H (rear pid)))).
  apply Fin.of_nat_ext.

  destruct (Fin.eq_dec i ((Fin.of_nat_lt Hlt))).
  subst.
  rewrite Vector.nth_replace_eq; auto.
  rewrite <-H13.
  simpl. lia.
  rewrite Vector.nth_replace_neq; auto.

  tmp noB_preserves_AEnq31 Hvalid st2 pid acts' Hgather Hb.
  tmp noB_preserves_ADeq2 Hvalid st2 pid acts' Hgather Hb.
  tmp noB_preserves_ADeq5 Hvalid st2 pid acts' Hgather Hb.
  tmp noB_preserves_ADeq11 Hvalid st2 pid acts' Hgather Hb.
  tmp noB_preserves_ADeq14 Hvalid st2 pid acts' Hgather Hb.
  tmp noB_preserves_ADeq28 Hvalid st2 pid acts' Hgather Hb.
  tmp noB_preserves_ADeq31 Hvalid st2 pid acts' Hgather Hb.
    (* d28 *)
    -- apply step_invariant in HreachTmp.
      unfold ComposedLTS.inv in HreachTmp.
      simpl in HreachTmp.
      apply HreachTmp in Hbinds0; auto.
                destruct Hbinds0 as [s1 [s2 [q [acts' [Hint_query [Hvalid Hgather]]]]]].
                inversion Hint_query; subst; simpl in *.
                inversion H5; subst; simpl in *.
                unfold binds in Hb.
                inversion H7; subst; simpl in *.
  tmp noB_preserves_AEnq2 Hvalid st2 pid acts' Hgather Hb.
  tmp noB_preserves_AEnq5 Hvalid st2 pid acts' Hgather Hb.
  tmp noB_preserves_AEnq11 Hvalid st2 pid acts' Hgather Hb.
  tmp noB_preserves_AEnq14 Hvalid st2 pid acts' Hgather Hb.
  tmp noB_preserves_AEnq28 Hvalid st2 pid acts' Hgather Hb.
  tmp noB_preserves_AEnq31 Hvalid st2 pid acts' Hgather Hb.
  tmp noB_preserves_ADeq2 Hvalid st2 pid acts' Hgather Hb.
  tmp noB_preserves_ADeq5 Hvalid st2 pid acts' Hgather Hb.
  tmp noB_preserves_ADeq11 Hvalid st2 pid acts' Hgather Hb.
  tmp noB_preserves_ADeq14 Hvalid st2 pid acts' Hgather Hb.

  pose proof Hvalid as HvalidTmp';
                apply valid_execution_fragment_com' in Hvalid;
                simpl in Hvalid;
                destruct st2; simpl in *;
  eapply valid_execution_fragment_sync in Hvalid; eauto;
  eapply noB_preserves_ADeq28_combine with (pid:=pid) in Hvalid; eauto;
  try (simpl; eapply substitute_eq_binds_v'; eauto);
  try (
      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts') = nil) by
      (rewrite Hgather; simpl; reflexivity);
      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B;
      assumption).
  simpl in Hvalid.
  destruct Hvalid as [Hx Hrear].
  inversion H6; subst; simpl in *.
  inversion H8; subst; simpl in *.
  inversion H10; subst; simpl in *.
  inversion H9; subst; simpl in *.
  apply valid_execution_fragment_com in HvalidTmp';
  simpl in HvalidTmp';
  eapply internal_preserves_request'' with (pid:=pid) in HvalidTmp'; simpl in *; eauto;
  try apply binds_push_eq;
  try (eapply gather_pid_events_B_gather_pid_external_events;
      eassumption).
  inversion HvalidTmp'; subst; simpl in *.
  assert (Htmp : (Fin.of_nat_lt Hlt) =
    (Fin.of_nat_lt (mod_lt H (front pid)))).
  apply Fin.of_nat_ext.

  destruct (Fin.eq_dec i ((Fin.of_nat_lt Hlt))).
  subst.
  rewrite Vector.nth_replace_eq; auto.
  rewrite <-H13.
  simpl. lia.
  rewrite Vector.nth_replace_neq; auto.

  tmp noB_preserves_ADeq31 Hvalid st2 pid acts' Hgather Hb.
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Internal_L2; eauto;
    eapply composed_lts.Step_None; eauto.
    specialize (IHvalid_execution_fragment Htmp).
    eapply Nat.le_trans.
    2 : { eauto. }
    clear IHvalid_execution_fragment.
    clear Htmp.
    clear H1.
    inversion H0; subst; simpl in *.
    inversion H1; subst; simpl in *.
    unfold get_ary; simpl.
    inversion H2; subst; simpl in *; auto.
  - inversion H0.
  - inversion H0.
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Initial_Call; eauto;
    eapply composed_lts.Step_None; eauto.
    specialize (IHvalid_execution_fragment Htmp).
    eapply Nat.le_trans.
    2 : { eauto. }
    clear IHvalid_execution_fragment.
    clear Htmp.
    clear H1.
    inversion H0; subst; simpl in *.
    inversion H1; subst; simpl in *.
    unfold get_ary; simpl.
    inversion H2; subst; simpl in *; auto.
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Final_Return; eauto;
    eapply composed_lts.Step_None; eauto.
    specialize (IHvalid_execution_fragment Htmp).
    eapply Nat.le_trans.
    2 : { eauto. }
    clear IHvalid_execution_fragment.
    clear Htmp.
    clear H1.
    inversion H0; subst; simpl in *.
    inversion H1; subst; simpl in *.
    unfold get_ary; simpl.
    inversion H2; subst; simpl in *; auto.
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Internal_Query; eauto;
    eapply composed_lts.Step_None; eauto.
    specialize (IHvalid_execution_fragment Htmp).
    eapply Nat.le_trans.
    2 : { eauto. }
    clear IHvalid_execution_fragment.
    clear Htmp.
    clear H1.
    inversion H0; subst; simpl in *.
    unfold get_ary; simpl.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *; auto.
    inversion H4; subst; simpl in *; auto.
    inversion H5; subst; simpl in *; auto.
  - assert (Htmp : composed_lts.reachable (composed_array_queue L) st'').
    eapply reachable_valid_execution; eauto;
    eapply composed_lts.Step_Internal_Reply; eauto;
    eapply composed_lts.Step_None; eauto.
    specialize (IHvalid_execution_fragment Htmp).
    eapply Nat.le_trans.
    2 : { eauto. }
    clear IHvalid_execution_fragment.
    clear Htmp.
    clear H1.
    inversion H0; subst; simpl in *.
    unfold get_ary; simpl.
    inversion H1; subst; simpl in *.
    inversion H3; subst; simpl in *; auto.
    inversion H4; subst; simpl in *; auto.
    inversion H5; subst; simpl in *; auto.
Qed.

End test.
