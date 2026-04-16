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
  ArrayQueue
  ArrayQueueImpl
  ArrayQueueMapping
  ArrayQueueProp
  ArrayQueueImplProp
  Queue
  ArrayQueueInvariant
  ArrayProp.
Import ListNotations.

Section Compose.

Context {liA liB : language_interface}.
Variable L1 : lts li_null liA.
Variable L2 : lts liA liB.

Lemma compose_reachable_single_reachable: forall s,
  composed_lts.reachable (compose L1 L2) s ->
  reachable L1 s.(Compose.L1State).(LState).
Proof.
  intros. unfold reachable.
  unfold composed_lts.reachable in H.
  destruct H as [init [acts [Hnew Hvalid]]].
  apply valid_execution_fragment_com in Hvalid.
  destruct init, s. simpl in *.
  destruct L1State, L1State0. simpl in *.
  eapply valid_execution_fragment_sync in Hvalid; eauto.
  exists LState.
  exists (gatherAB acts).
  intuition.
  inversion Hnew; subst; simpl in *.
  inversion H; subst; simpl in *. intuition.
Qed.

End Compose.

Section Tensor.

Context {liA liB : language_interface}.
Variable L1 : lts li_null liA.
Variable L2 : lts li_null liB.

Lemma tensor_reachable_single_reachable: forall s,
  reachable (tensor L1 L2) s ->
  reachable L1 s.(Tensor.L1State).(LState).
Proof.
  intros. unfold reachable.
  unfold reachable in H.
  destruct H as [init [acts [Hnew Hvalid]]].
  apply Tensor.valid_execution_fragment_com in Hvalid.
  destruct init, s. simpl in *.
  destruct L1State, L1State0. simpl in *.
  eapply valid_execution_fragment_sync in Hvalid; eauto.
  exists LState.
  exists (gatherL1 acts).
  intuition.
  inversion Hnew; subst; simpl in *.
  inversion H; subst; simpl in *. intuition.
Qed.

Lemma tensor_reachable_single_reachable': forall s,
  reachable (tensor L1 L2) s ->
  reachable L2 s.(Tensor.L2State).(LState).
Proof.
  intros. unfold reachable.
  unfold reachable in H.
  destruct H as [init [acts [Hnew Hvalid]]].
  apply Tensor.valid_execution_fragment_com' in Hvalid.
  destruct init, s. simpl in *.
  destruct L2State, L2State0. simpl in *.
  eapply valid_execution_fragment_sync in Hvalid; eauto.
  exists LState.
  exists (gatherL2 acts).
  intuition.
  inversion Hnew; subst; simpl in *.
  inversion H0; subst; simpl in *. intuition.
Qed.

End Tensor.

Section test.

Lemma entry_eqb_eq: forall e e',
  entry_eqb e e' = true  ->
  e = e'.
Proof.
  intros.
  destruct e, e'.
  simpl in H.
  destruct (op_nat_eqb o o0)eqn:Heq.
  - apply Nat.eqb_eq in H.
    subst.
    unfold op_nat_eqb in Heq.
    destruct o.
    destruct o0.
    apply Nat.eqb_eq in Heq; subst.
    reflexivity.
    discriminate.
    destruct o0.
    discriminate.
    reflexivity.
  - discriminate.
Qed.

End test.

Section INV.

Variable L : nat.
Hypothesis H : L > 0.

Definition inv_e10_x_rear_p (s : composed_lts.state (composed_array_queue L)) :=
  let sync_acc := s.(Compose.L1State) in
  let acc := sync_acc.(LState) in
  let sync_ary := acc.(Tensor.L1State) in
  let ary := sync_ary.(LState) in
  let sync_front_rear := acc.(Tensor.L2State) in
  let front_rear := sync_front_rear.(LState) in
  let sync_front := front_rear.(Tensor.L1State) in
  let front := sync_front.(LState) in
  let sync_rear := front_rear.(Tensor.L2State) in
  let rear := sync_rear.(LState) in
  let sync_aqimpl := s.(Compose.L2State) in
  let aqimpl := sync_aqimpl.(LState) in
  let pc := aqimpl.(pc) in
  (forall pid,
    binds pid AEnq10 pc ->
     (aqimpl.(ArrayQueueImpl.x) pid) =
     (Vector.nth
      (ary.(Array.vec L))
      (Fin.of_nat_lt (mod_lt H
                      (aqimpl.(ArrayQueueImpl.rear) pid))))
  ) /\
  composed_lts.reachable (composed_array_queue L) s.

Definition inv_ary_read_at_e5_d5 (s : composed_lts.state (composed_array_queue L)) :=
  let sync_acc := s.(Compose.L1State) in
  let acc := sync_acc.(LState) in
  let sync_ary := acc.(Tensor.L1State) in
  let ary := sync_ary.(LState) in
  let sync_front_rear := acc.(Tensor.L2State) in
  let front_rear := sync_front_rear.(LState) in
  let sync_front := front_rear.(Tensor.L1State) in
  let front := sync_front.(LState) in
  let sync_rear := front_rear.(Tensor.L2State) in
  let rear := sync_rear.(LState) in
  let sync_aqimpl := s.(Compose.L2State) in
  let aqimpl := sync_aqimpl.(LState) in
  let pc := aqimpl.(pc) in
  (forall pid i,
    binds pid (AryRead i) ary.(Array.requests L) ->
      binds pid AEnq5 pc \/
      binds pid ADeq5 pc) /\
  composed_lts.reachable (composed_array_queue L) s.

Lemma inv_ary_read_at_e5_d5_inv:
  composed_lts.invariant_ind (composed_array_queue L)
  inv_ary_read_at_e5_d5.
Proof.
  unfold inv_ary_read_at_e5_d5.
  apply invariant_ind''_imply_invariant_ind_land.
  unfold invariant_ind''. intuition.
  apply reachable_is_invariant.
  unfold about. intuition.
  - rename H1 into Hb.
    inversion H0; subst.
    inversion H1; subst.
    inversion H2; subst.
    inversion H3; subst.
    inversion H5; subst.
    inversion H7; subst.
    inversion H8; subst.
    inversion H9; subst.
    inversion H12; subst.
    inversion H14; subst.
    inversion H16; subst.
    inversion H17; subst.
    inversion H19; subst.
    simpl in *.
    rewrite H15 in Hb.
    unfold new_array in Hb.
    inversion Hb.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    apply H0 in Hb; auto.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *;
    assert (Htmp : pid0 # (remove inv pid0)) by
    (apply ok_remove_notin; auto);
    unfold "#" in Htmp;
    apply binds_in in Hb; intuition.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    apply H0 in Hb; auto.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *;
    apply remove_preserves_binds_notin in Hb; auto;
    apply H0 in Hb; auto.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply H0 in Hb; auto;
    unfold binds in Hb;
    rewrite Hbinds0 in Hb;
    destruct Hb as [Hb1|Hb2];
    discriminate.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    all : apply H0 in Hb; auto;
    destruct Hb as [Hb1|Hb2];
    [left|right];
    apply substitute_neq_preserves_binds; auto.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    all : apply H0 in Hb; auto;
    destruct Hb as [Hb1|Hb2];
    unfold "#" in Hnotin_pc;
    [apply binds_in in Hb1|
     apply binds_in in Hb2];
     intuition.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    all : apply H0 in Hb; auto;
    destruct Hb as [Hb1|Hb2];
    [left|right];
    apply binds_push_neq; auto.
  - destruct act.
  - destruct act.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    all : apply H0 in Hb; auto;
    unfold binds in Hb;
    rewrite Hbinds0 in Hb; intuition;
    discriminate.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    all : apply H0 in Hb; auto;
    destruct Hb as [Hb1|Hb2];
    [left|right];
    apply remove_neq_preserves_binds; auto.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H4; subst; simpl in *.
    all : try (
    inversion H3; subst; simpl in *;
    inversion H5; subst; simpl in *;
    apply H0 in Hb; auto;
    unfold binds in Hb;
    rewrite Hbinds0 in Hb; intuition;
    discriminate).
    all : try (inversion H3; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    apply binds_push_eq_inv in Hb; discriminate).
    left.
    eapply substitute_eq_binds_v'; eauto.
    right.
    eapply substitute_eq_binds_v'; eauto.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H4; subst; simpl in *.
    all : try (inversion H3; subst; simpl in *;
    inversion H5; subst; simpl in *;
    apply H0 in Hb; auto;
    destruct Hb as [Hb1|Hb2];
    [left|right];
    apply substitute_neq_preserves_binds; auto).
    all : inversion H3; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    apply binds_push_neq_inv in Hb; auto;
    apply H0 in Hb; auto;
    destruct Hb as [Hb1|Hb2];
    [left|right];
    apply substitute_neq_preserves_binds; auto.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *.
    all : try (
    inversion H2; subst; simpl in *;
    inversion H5; subst; simpl in *;
    apply H0 in Hb; auto;
    unfold binds in Hb;
    rewrite Hbinds0 in Hb; intuition;
    discriminate).
    all : try (inversion H2; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    apply H0 in Hb; auto;
    unfold binds in Hb;
    rewrite Hbinds0 in Hb; intuition;
    discriminate).
    inversion H2; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *.
    apply compose_reachable_single_reachable in Hreach.
    apply tensor_reachable_single_reachable in Hreach.
    simpl in Hreach.
    apply array_exclusive_wf_invariant in Hreach.
    simpl in Hreach.
    unfold array_exclusive_wf in Hreach.
    specialize (Hreach pid0).
    simpl in Hreach.
    intuition.
    apply binds_in in Hbinds4.
    intuition.
    apply binds_in in Hb.
    unfold "#" in H10; intuition.
    inversion H2; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *.
    apply compose_reachable_single_reachable in Hreach.
    apply tensor_reachable_single_reachable in Hreach.
    simpl in Hreach.
    apply array_exclusive_wf_invariant in Hreach.
    simpl in Hreach.
    unfold array_exclusive_wf in Hreach.
    specialize (Hreach pid0).
    simpl in Hreach.
    intuition.
    apply binds_in in Hbinds4.
    intuition.
    apply binds_in in Hb.
    unfold "#" in H10; intuition.
    -- inversion H1; subst; simpl in *.
      inversion H3; subst; simpl in *.
      inversion H4; subst; simpl in *.
      all : try (inversion H2; subst; simpl in *;
      inversion H5; subst; simpl in *;
      apply H0 in Hb; auto;
      destruct Hb as [Hb1|Hb2];
      [left|right];
      apply substitute_neq_preserves_binds; auto).
      all : try (inversion H2; subst; simpl in *;
      inversion H5; subst; simpl in *;
      inversion H7; subst; simpl in *;
      inversion H6; subst; simpl in *;
      apply H0 in Hb; auto;
      destruct Hb as [Hb1|Hb2];
      [left|right];
      apply substitute_neq_preserves_binds; auto).
Qed.

Lemma inv_ary_read_at_e5_d5_invariant:
  composed_lts.invariant (composed_array_queue L)
  inv_ary_read_at_e5_d5.
Proof.
  apply invariant_ind_to_invariant'.
  apply inv_ary_read_at_e5_d5_inv.
Qed.

Definition inv_ary_cas_at_e28_d28 (s : composed_lts.state (composed_array_queue L)) :=
  let sync_acc := s.(Compose.L1State) in
  let acc := sync_acc.(LState) in
  let sync_ary := acc.(Tensor.L1State) in
  let ary := sync_ary.(LState) in
  let sync_front_rear := acc.(Tensor.L2State) in
  let front_rear := sync_front_rear.(LState) in
  let sync_front := front_rear.(Tensor.L1State) in
  let front := sync_front.(LState) in
  let sync_rear := front_rear.(Tensor.L2State) in
  let rear := sync_rear.(LState) in
  let sync_aqimpl := s.(Compose.L2State) in
  let aqimpl := sync_aqimpl.(LState) in
  let pc := aqimpl.(pc) in
  (forall pid i old new,
    binds pid (AryCAS i old new) ary.(Array.requests L) ->
      binds pid AEnq28 pc \/
      binds pid ADeq28 pc) /\
  composed_lts.reachable (composed_array_queue L) s.

Lemma inv_ary_cas_at_e28_d28_inv:
  composed_lts.invariant_ind (composed_array_queue L)
  inv_ary_cas_at_e28_d28.
Proof.
  unfold inv_ary_cas_at_e28_d28.
  apply invariant_ind''_imply_invariant_ind_land.
  unfold invariant_ind''. intuition.
  apply reachable_is_invariant.
  unfold about. intuition.
  - rename H1 into Hb.
    inversion H0; subst.
    inversion H1; subst.
    inversion H2; subst.
    inversion H3; subst.
    inversion H5; subst.
    inversion H7; subst.
    inversion H8; subst.
    inversion H9; subst.
    inversion H12; subst.
    inversion H14; subst.
    inversion H16; subst.
    inversion H17; subst.
    inversion H19; subst.
    simpl in *.
    rewrite H15 in Hb.
    unfold new_array in Hb.
    inversion Hb.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    apply H0 in Hb; auto.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *;
    assert (Htmp : pid0 # (remove inv pid0)) by
    (apply ok_remove_notin; auto);
    unfold "#" in Htmp;
    apply binds_in in Hb; intuition.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    apply H0 in Hb; auto.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *;
    apply remove_preserves_binds_notin in Hb; auto;
    apply H0 in Hb; auto.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply H0 in Hb; auto;
    unfold binds in Hb;
    rewrite Hbinds0 in Hb;
    destruct Hb as [Hb1|Hb2];
    discriminate.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    all : apply H0 in Hb; auto;
    destruct Hb as [Hb1|Hb2];
    [left|right];
    apply substitute_neq_preserves_binds; auto.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    all : apply H0 in Hb; auto;
    destruct Hb as [Hb1|Hb2];
    unfold "#" in Hnotin_pc;
    [apply binds_in in Hb1|
     apply binds_in in Hb2];
     intuition.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    all : apply H0 in Hb; auto;
    destruct Hb as [Hb1|Hb2];
    [left|right];
    apply binds_push_neq; auto.
  - destruct act.
  - destruct act.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    all : apply H0 in Hb; auto;
    unfold binds in Hb;
    rewrite Hbinds0 in Hb; intuition;
    discriminate.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    all : apply H0 in Hb; auto;
    destruct Hb as [Hb1|Hb2];
    [left|right];
    apply remove_neq_preserves_binds; auto.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H4; subst; simpl in *.
    all : try (
    inversion H3; subst; simpl in *;
    inversion H5; subst; simpl in *;
    apply H0 in Hb; auto;
    unfold binds in Hb;
    rewrite Hbinds0 in Hb; intuition;
    discriminate).
    all : try (inversion H3; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    apply binds_push_eq_inv in Hb; discriminate).
    left.
    eapply substitute_eq_binds_v'; eauto.
    right.
    eapply substitute_eq_binds_v'; eauto.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H4; subst; simpl in *.
    all : try (inversion H3; subst; simpl in *;
    inversion H5; subst; simpl in *;
    apply H0 in Hb; auto;
    destruct Hb as [Hb1|Hb2];
    [left|right];
    apply substitute_neq_preserves_binds; auto).
    all : inversion H3; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    apply binds_push_neq_inv in Hb; auto;
    apply H0 in Hb; auto;
    destruct Hb as [Hb1|Hb2];
    [left|right];
    apply substitute_neq_preserves_binds; auto.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *.
    all : try (
    inversion H2; subst; simpl in *;
    inversion H5; subst; simpl in *;
    apply H0 in Hb; auto;
    unfold binds in Hb;
    rewrite Hbinds0 in Hb; intuition;
    discriminate).
    all : try (inversion H2; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    apply H0 in Hb; auto;
    unfold binds in Hb;
    rewrite Hbinds0 in Hb; intuition;
    discriminate).
    inversion H2; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *.
    apply compose_reachable_single_reachable in Hreach.
    apply tensor_reachable_single_reachable in Hreach.
    simpl in Hreach.
    apply array_exclusive_wf_invariant in Hreach.
    simpl in Hreach.
    unfold array_exclusive_wf in Hreach.
    specialize (Hreach pid0).
    simpl in Hreach.
    intuition.
    apply binds_in in Hbinds4.
    intuition.
    apply binds_in in Hb.
    unfold "#" in H10; intuition.
    inversion H2; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *.
    apply compose_reachable_single_reachable in Hreach.
    apply tensor_reachable_single_reachable in Hreach.
    simpl in Hreach.
    apply array_exclusive_wf_invariant in Hreach.
    simpl in Hreach.
    unfold array_exclusive_wf in Hreach.
    specialize (Hreach pid0).
    simpl in Hreach.
    intuition.
    apply binds_in in Hbinds4.
    intuition.
    apply binds_in in Hb.
    unfold "#" in H10; intuition.
    -- inversion H1; subst; simpl in *.
      inversion H3; subst; simpl in *.
      inversion H4; subst; simpl in *.
      all : try (inversion H2; subst; simpl in *;
      inversion H5; subst; simpl in *;
      apply H0 in Hb; auto;
      destruct Hb as [Hb1|Hb2];
      [left|right];
      apply substitute_neq_preserves_binds; auto).
      all : try (inversion H2; subst; simpl in *;
      inversion H5; subst; simpl in *;
      inversion H7; subst; simpl in *;
      inversion H6; subst; simpl in *;
      apply H0 in Hb; auto;
      destruct Hb as [Hb1|Hb2];
      [left|right];
      apply substitute_neq_preserves_binds; auto).
Qed.

Lemma inv_ary_cas_at_e28_d28_invariant:
  composed_lts.invariant (composed_array_queue L)
  inv_ary_cas_at_e28_d28.
Proof.
  apply invariant_ind_to_invariant'.
  apply inv_ary_cas_at_e28_d28_inv.
Qed.

Definition get_front (s : composed_lts.state (composed_array_queue L)) :=
  let sync_acc := s.(Compose.L1State) in
  let acc := sync_acc.(LState) in
  let sync_ary := acc.(Tensor.L1State) in
  let ary := sync_ary.(LState) in
  let sync_front_rear := acc.(Tensor.L2State) in
  let front_rear := sync_front_rear.(LState) in
  let sync_front := front_rear.(Tensor.L1State) in
  let front := sync_front.(LState) in
  let sync_rear := front_rear.(Tensor.L2State) in
  let rear := sync_rear.(LState) in
  let sync_aqimpl := s.(Compose.L2State) in
  let aqimpl := sync_aqimpl.(LState) in
  let pc := aqimpl.(pc) in
  front.

Fixpoint get_f' pc res_ary res_front : nat :=
  match pc with
  | nil => O
  | (pid, p) :: pc' =>
    let r' := get_f' pc' res_ary res_front in
    match p with
    | ADeq28 => match get pid res_ary with
                | None => r'
                | Some res => match res with
                              | AryCASOk b => if b then (S r') else r'
                              | AryReadOk _ => r'
                              end
                end
    | ADeq29 ret => if ret then (S r') else r'
    | ADeq30 => (S r')
    | ADeq31 => match get pid res_front with
                | None => (S r')
                | Some res => match res with
                              | CntIncOk => r'
                              | CntReadOk _ => (S r') (* unreachable *)
                              end
                end
    | _ => r'
    end
  end.

Lemma get_f'_dist: forall pc pc' res_ary res_front,
  get_f' (pc ++ pc') res_ary res_front =
  get_f' (pc) res_ary res_front +
  get_f' (pc') res_ary res_front.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - destruct a.
    match_if'; rewrite IHpc; auto.
Qed.

Lemma get_f'_any_ary: forall pc res_ary res_front pid v,
  pid # pc ->
  get_f' pc ((pid, v) :: res_ary) res_front =
  get_f' pc res_ary res_front.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - apply notin_union in H0.
    intuition.
    destruct a. simpl in *.
    apply notin_neq in H1.
    erewrite IHpc; eauto.
    destruct a; simpl; match_if'.
    all : apply Nat.eqb_eq in Heqb; subst; intuition.
Qed.

Lemma get_f'_any_ary_cas_false: forall pc res_ary res_front pid,
  pid # res_ary ->
  get_f' pc ((pid, AryCASOk false) :: res_ary) res_front =
  get_f' pc res_ary res_front.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - destruct a. simpl in *.
    erewrite IHpc; eauto.
    destruct a; simpl; match_if'.
    apply binds_in in Heqo.
    unfold "#" in H0.
    all : apply Nat.eqb_eq in Heqb; subst; intuition.
Qed.

Lemma get_f'_any_rear_remove: forall pc res_ary res_front pid,
  ok pc ->
  pid # pc ->
  get_f' pc res_ary (remove res_front pid) =
  get_f' pc res_ary res_front.
Proof.
  induction 1; simpl; intros.
  - reflexivity.
  - apply notin_union in H2.
    destruct H2 as [H21 H22];
    apply notin_neq in H21; intuition.
    destruct T; simpl in *;
    erewrite H2; eauto.
    match_if';
    try (eapply remove_neq_preserves_binds in Heqo0; eauto;
    rewrite Heqo0 in Heqo; discriminate).
    rewrite remove_neq_preserves_get in Heqo; auto.
    rewrite Heqo in Heqo0; discriminate.
Qed.

Lemma get_f'_any_front_push: forall pc res_ary res_front pid v,
  pid # pc ->
  get_f' pc res_ary ((pid, v) :: res_front) =
  get_f' pc res_ary res_front.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - destruct a. simpl in *.
    apply notin_union in H0;
    destruct H0 as [H1 H2];
    apply notin_neq in H1.
    erewrite IHpc; eauto.
    destruct a; simpl; match_if'.
    apply Nat.eqb_eq in Heqb;
    subst; intuition.
    apply Nat.eqb_eq in Heqb;
    subst; intuition.
    apply Nat.eqb_eq in Heqb;
    subst; intuition.
Qed.

Lemma get_f'_any_rear_read: forall pc res_ary res_front pid v,
  pid # res_front ->
  get_f' pc res_ary ((pid, CntReadOk v) :: res_front) =
  get_f' pc res_ary res_front.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - destruct a. simpl in *.
    erewrite IHpc; eauto.
    destruct a; simpl; match_if'.
    apply binds_in in Heqo.
    unfold "#" in H0.
    all : apply Nat.eqb_eq in Heqb; subst; intuition.
Qed.

Lemma get_f'_any_rear_push: forall pc res_ary res_rear pid v,
  pid # pc ->
  get_f' pc res_ary ((pid, v) :: res_rear) =
  get_f' pc res_ary res_rear.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - destruct a. simpl in *.
    apply notin_union in H0;
    destruct H0 as [H1 H2];
    apply notin_neq in H1.
    erewrite IHpc; eauto.
    destruct a; simpl; match_if'.
    apply Nat.eqb_eq in Heqb;
    subst; intuition.
    apply Nat.eqb_eq in Heqb;
    subst; intuition.
    apply Nat.eqb_eq in Heqb;
    subst; intuition.
Qed.

Lemma get_f'_any_ary_read: forall pc res_ary res_front pid v,
  pid # res_ary ->
  get_f' pc ((pid, AryReadOk v) :: res_ary) res_front =
  get_f' pc res_ary res_front.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - destruct a. simpl in *.
    erewrite IHpc; eauto.
    destruct a; simpl; match_if'.
    apply binds_in in Heqo.
    unfold "#" in H0.
    all : apply Nat.eqb_eq in Heqb; subst; intuition.
Qed.

Lemma get_f'_any_ary_remove: forall pc res_ary res_front pid,
  ok pc ->
  pid # pc ->
  get_f' pc (remove res_ary pid) res_front =
  get_f' pc res_ary res_front.
Proof.
  induction 1; simpl; intros.
  - reflexivity.
  - apply notin_union in H2.
    destruct H2 as [H21 H22];
    apply notin_neq in H21; intuition.
    destruct T; simpl in *;
    erewrite H2; eauto.
    match_if';
    try (eapply remove_neq_preserves_binds in Heqo0; eauto;
    rewrite Heqo0 in Heqo; discriminate).
    rewrite remove_neq_preserves_get in Heqo; auto.
    rewrite Heqo in Heqo0; discriminate.
Qed.

Arguments get_ary {L}.
Arguments get_pc {L}.
Arguments R {L}.

Definition F (s : composed_lts.state (composed_array_queue L)) :=
  let front := get_front s in
  let ary := get_ary s in
  let pc := get_pc s in
  front.(Counter.value) + get_f' pc ary.(Array.responses L) front.(Counter.responses).

Definition inv_e28 (s : composed_lts.state (composed_array_queue L)) :=
  let sync_acc := s.(Compose.L1State) in
  let acc := sync_acc.(LState) in
  let sync_ary := acc.(Tensor.L1State) in
  let ary := sync_ary.(LState) in
  let sync_front_rear := acc.(Tensor.L2State) in
  let front_rear := sync_front_rear.(LState) in
  let sync_front := front_rear.(Tensor.L1State) in
  let front := sync_front.(LState) in
  let sync_rear := front_rear.(Tensor.L2State) in
  let rear := sync_rear.(LState) in
  let sync_aqimpl := s.(Compose.L2State) in
  let aqimpl := sync_aqimpl.(LState) in
  let pc := aqimpl.(pc) in
  (forall pid,
    binds pid AEnq28 pc ->
    (aqimpl.(ArrayQueueImpl.x) pid) = 
     (Vector.nth
      (ary.(Array.vec L))
      (Fin.of_nat_lt (mod_lt H
                      (aqimpl.(ArrayQueueImpl.rear) pid)))) ->
    aqimpl.(ArrayQueueImpl.rear) pid = R s /\ R s < F s + L
  ) /\
  composed_lts.reachable (composed_array_queue L) s.

Definition inv_rear_inc_at_e31 (s : composed_lts.state (composed_array_queue L)) :=
  let sync_acc := s.(Compose.L1State) in
  let acc := sync_acc.(LState) in
  let sync_ary := acc.(Tensor.L1State) in
  let ary := sync_ary.(LState) in
  let sync_front_rear := acc.(Tensor.L2State) in
  let front_rear := sync_front_rear.(LState) in
  let sync_front := front_rear.(Tensor.L1State) in
  let front := sync_front.(LState) in
  let sync_rear := front_rear.(Tensor.L2State) in
  let rear := sync_rear.(LState) in
  let sync_aqimpl := s.(Compose.L2State) in
  let aqimpl := sync_aqimpl.(LState) in
  let pc := aqimpl.(pc) in
  (forall pid,
    binds pid CntInc rear.(Counter.requests) ->
      binds pid AEnq31 pc) /\
  composed_lts.reachable (composed_array_queue L) s.

Lemma counter_exclusive_wf_invariant: invariant counter counter_exclusive_wf.
Proof.
  apply invariant_ind_to_invariant.
  apply counter_exclusive_wf_inv.
Qed.

Lemma inv_rear_inc_at_e31_inv:
  composed_lts.invariant_ind (composed_array_queue L)
  inv_rear_inc_at_e31.
Proof.
  unfold inv_rear_inc_at_e31.
  apply invariant_ind''_imply_invariant_ind_land.
  unfold invariant_ind''. intuition.
  apply reachable_is_invariant.
  unfold about. intuition.
  - rename H1 into Hb.
    inversion H0; subst.
    inversion H1; subst.
    inversion H2; subst.
    inversion H3; subst.
    inversion H5; subst.
    inversion H7; subst.
    inversion H8; subst.
    inversion H9; subst.
    inversion H12; subst.
    inversion H14; subst.
    inversion H16; subst.
    inversion H17; subst.
    inversion H19; subst.
    simpl in *.
    rewrite H23 in Hb.
    unfold new_counter in Hb.
    inversion Hb.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    ---
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *.
    +
    inversion H6; subst; simpl in *.
    inversion H7; subst; simpl in *;
    assert (Htmp : pid0 # (remove inv pid0)) by
    (apply ok_remove_notin; auto);
    unfold "#" in Htmp;
    apply binds_in in Hb; intuition.
    +
    apply H0; auto.
    ---
    apply H0; auto.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    ---
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *.
    +
    inversion H6; subst; simpl in *.
    inversion H7; subst; simpl in *;
    apply remove_preserves_binds_notin in Hb; auto.
    +
    apply H0; auto.
    ---
    apply H0; auto.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply H0 in Hb; auto;
    unfold binds in Hbinds0;
    rewrite Hb in Hbinds0;
    discriminate.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply H0 in Hb; auto;
    apply substitute_neq_preserves_binds; auto.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply H0 in Hb; auto;
    apply binds_in in Hb;
    unfold "#" in Hnotin_pc;
    intuition.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply H0 in Hb; auto;
    apply binds_push_neq; auto.
  - destruct act.
  - destruct act.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply H0 in Hb; auto;
    unfold binds in Hbinds0;
    rewrite Hb in Hbinds0; discriminate.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply H0 in Hb; auto;
    apply remove_neq_preserves_binds; auto.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H4; subst; simpl in *.
    all : try (inversion H3; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    inversion H9; subst; simpl in *;
    inversion H8; subst; simpl in *;
    apply binds_push_eq_inv in Hb; discriminate).
    all : try(inversion H3; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    apply H0 in Hb; auto;
    unfold binds in Hbinds0;
    rewrite Hb in Hbinds0;
    discriminate).
    eapply substitute_eq_binds_v'; eauto.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H4; subst; simpl in *.
    all : try (inversion H3; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    inversion H9; subst; simpl in *;
    inversion H8; subst; simpl in *;
    apply binds_push_neq_inv in Hb; auto;
    apply H0 in Hb; auto;
    apply substitute_neq_preserves_binds; auto).
    all : try (inversion H3; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    apply H0 in Hb; auto;
    apply substitute_neq_preserves_binds; auto).
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *.
    all : try (inversion H2; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    inversion H9; subst; simpl in *;
    inversion H8; subst; simpl in *;
    apply H0 in Hb; auto;
    unfold binds in Hbinds0;
    rewrite Hb in Hbinds0; discriminate).
    all : try (inversion H2; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    apply H0 in Hb; auto;
    unfold binds in Hbinds0;
    rewrite Hb in Hbinds0; discriminate).
    (inversion H2; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    inversion H9; subst; simpl in *;
    inversion H8; subst; simpl in *).
    apply compose_reachable_single_reachable in Hreach.
    apply tensor_reachable_single_reachable' in Hreach.
    apply tensor_reachable_single_reachable' in Hreach.
    simpl in Hreach.
    apply counter_exclusive_wf_invariant in Hreach.
    unfold counter_exclusive_wf in Hreach;
    simpl in Hreach.
    specialize (Hreach pid0).
    intuition.
    apply binds_in in Hbinds6.
    intuition.
    apply binds_in in Hb.
    unfold "#" in H12; intuition.
    -- inversion H1; subst; simpl in *.
      inversion H3; subst; simpl in *.
      inversion H4; subst; simpl in *.
      all : try (inversion H2; subst; simpl in *;
      inversion H5; subst; simpl in *;
      inversion H7; subst; simpl in *;
      inversion H6; subst; simpl in *;
      inversion H9; subst; simpl in *;
      inversion H8; subst; simpl in *;
      apply H0 in Hb; auto;
      apply substitute_neq_preserves_binds; auto).
      all : try (inversion H2; subst; simpl in *;
      inversion H5; subst; simpl in *;
      inversion H7; subst; simpl in *;
      inversion H6; subst; simpl in *;
      apply H0 in Hb; auto;
      apply substitute_neq_preserves_binds; auto).
Qed.

Lemma inv_rear_inc_at_e31_invariant:
  composed_lts.invariant (composed_array_queue L)
  inv_rear_inc_at_e31.
Proof.
  apply invariant_ind_to_invariant'.
  apply inv_rear_inc_at_e31_inv.
Qed.

Definition inv_front_inc_at_d31 (s : composed_lts.state (composed_array_queue L)) :=
  let sync_acc := s.(Compose.L1State) in
  let acc := sync_acc.(LState) in
  let sync_ary := acc.(Tensor.L1State) in
  let ary := sync_ary.(LState) in
  let sync_front_rear := acc.(Tensor.L2State) in
  let front_rear := sync_front_rear.(LState) in
  let sync_front := front_rear.(Tensor.L1State) in
  let front := sync_front.(LState) in
  let sync_rear := front_rear.(Tensor.L2State) in
  let rear := sync_rear.(LState) in
  let sync_aqimpl := s.(Compose.L2State) in
  let aqimpl := sync_aqimpl.(LState) in
  let pc := aqimpl.(pc) in
  (forall pid,
    binds pid CntInc front.(Counter.requests) ->
      binds pid ADeq31 pc) /\
  composed_lts.reachable (composed_array_queue L) s.

Lemma inv_front_inc_at_d31_inv:
  composed_lts.invariant_ind (composed_array_queue L)
  inv_front_inc_at_d31.
Proof.
  unfold inv_front_inc_at_d31.
  apply invariant_ind''_imply_invariant_ind_land.
  unfold invariant_ind''. intuition.
  apply reachable_is_invariant.
  unfold about. intuition.
  - rename H1 into Hb.
    inversion H0; subst.
    inversion H1; subst.
    inversion H2; subst.
    inversion H3; subst.
    inversion H5; subst.
    inversion H7; subst.
    inversion H8; subst.
    inversion H9; subst.
    inversion H12; subst.
    inversion H14; subst.
    inversion H16; subst.
    inversion H17; subst.
    inversion H19; subst.
    simpl in *.
    rewrite H22 in Hb.
    unfold new_counter in Hb.
    inversion Hb.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    ---
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *.
    +
    apply H0; auto.
    +
    inversion H6; subst; simpl in *.
    inversion H7; subst; simpl in *;
    assert (Htmp : pid0 # (remove inv pid0)) by
    (apply ok_remove_notin; auto);
    unfold "#" in Htmp;
    apply binds_in in Hb; intuition.
    ---
    apply H0; auto.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    ---
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *.
    +
    apply H0; auto.
    +
    inversion H6; subst; simpl in *.
    inversion H7; subst; simpl in *;
    apply remove_preserves_binds_notin in Hb; auto.
    ---
    apply H0; auto.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply H0 in Hb; auto;
    unfold binds in Hbinds0;
    rewrite Hb in Hbinds0;
    discriminate.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply H0 in Hb; auto;
    apply substitute_neq_preserves_binds; auto.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply H0 in Hb; auto;
    apply binds_in in Hb;
    unfold "#" in Hnotin_pc;
    intuition.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply H0 in Hb; auto;
    apply binds_push_neq; auto.
  - destruct act.
  - destruct act.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply H0 in Hb; auto;
    unfold binds in Hbinds0;
    rewrite Hb in Hbinds0; discriminate.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply H0 in Hb; auto;
    apply remove_neq_preserves_binds; auto.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H4; subst; simpl in *.
    all : try (inversion H3; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    inversion H9; subst; simpl in *;
    inversion H8; subst; simpl in *;
    apply binds_push_eq_inv in Hb; discriminate).
    all : try(inversion H3; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    apply H0 in Hb; auto;
    unfold binds in Hbinds0;
    rewrite Hb in Hbinds0;
    discriminate).
    eapply substitute_eq_binds_v'; eauto.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H4; subst; simpl in *.
    all : try (inversion H3; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    inversion H9; subst; simpl in *;
    inversion H8; subst; simpl in *;
    apply binds_push_neq_inv in Hb; auto;
    apply H0 in Hb; auto;
    apply substitute_neq_preserves_binds; auto).
    all : try (inversion H3; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    apply H0 in Hb; auto;
    apply substitute_neq_preserves_binds; auto).
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *.
    all : try (inversion H2; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    inversion H9; subst; simpl in *;
    inversion H8; subst; simpl in *;
    apply H0 in Hb; auto;
    unfold binds in Hbinds0;
    rewrite Hb in Hbinds0; discriminate).
    all : try (inversion H2; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    apply H0 in Hb; auto;
    unfold binds in Hbinds0;
    rewrite Hb in Hbinds0; discriminate).
    (inversion H2; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    inversion H9; subst; simpl in *;
    inversion H8; subst; simpl in *).
    apply compose_reachable_single_reachable in Hreach.
    apply tensor_reachable_single_reachable' in Hreach.
    apply tensor_reachable_single_reachable in Hreach.
    simpl in Hreach.
    apply counter_exclusive_wf_invariant in Hreach.
    unfold counter_exclusive_wf in Hreach;
    simpl in Hreach.
    specialize (Hreach pid0).
    intuition.
    apply binds_in in Hbinds6.
    intuition.
    apply binds_in in Hb.
    unfold "#" in H12; intuition.
    -- inversion H1; subst; simpl in *.
      inversion H3; subst; simpl in *.
      inversion H4; subst; simpl in *.
      all : try (inversion H2; subst; simpl in *;
      inversion H5; subst; simpl in *;
      inversion H7; subst; simpl in *;
      inversion H6; subst; simpl in *;
      inversion H9; subst; simpl in *;
      inversion H8; subst; simpl in *;
      apply H0 in Hb; auto;
      apply substitute_neq_preserves_binds; auto).
      all : try (inversion H2; subst; simpl in *;
      inversion H5; subst; simpl in *;
      inversion H7; subst; simpl in *;
      inversion H6; subst; simpl in *;
      apply H0 in Hb; auto;
      apply substitute_neq_preserves_binds; auto).
Qed.

Lemma inv_front_inc_at_d31_invariant:
  composed_lts.invariant (composed_array_queue L)
  inv_front_inc_at_d31.
Proof.
  apply invariant_ind_to_invariant'.
  apply inv_front_inc_at_d31_inv.
Qed.

Definition inv_e27_x_none (s : composed_lts.state (composed_array_queue L)) :=
  let sync_acc := s.(Compose.L1State) in
  let acc := sync_acc.(LState) in
  let sync_ary := acc.(Tensor.L1State) in
  let ary := sync_ary.(LState) in
  let sync_front_rear := acc.(Tensor.L2State) in
  let front_rear := sync_front_rear.(LState) in
  let sync_front := front_rear.(Tensor.L1State) in
  let front := sync_front.(LState) in
  let sync_rear := front_rear.(Tensor.L2State) in
  let rear := sync_rear.(LState) in
  let sync_aqimpl := s.(Compose.L2State) in
  let aqimpl := sync_aqimpl.(LState) in
  let pc := aqimpl.(pc) in
  (forall pid,
    binds pid AEnq27 pc ->
      fst (aqimpl.(ArrayQueueImpl.x) pid) = None
  ) /\ composed_lts.reachable (composed_array_queue L) s.

Lemma inv_e27_x_none_inv:
  composed_lts.invariant_ind (composed_array_queue L)
  inv_e27_x_none.
Proof.
  unfold inv_e27_x_none.
  apply invariant_ind''_imply_invariant_ind_land.
  unfold invariant_ind''. intuition.
  apply reachable_is_invariant.
  unfold about. intuition.
  - rename H1 into Hb.
    inversion H0; subst.
    inversion H1; subst.
    inversion H2; subst.
    inversion H3; subst.
    inversion H5; subst.
    inversion H7; subst.
    inversion H8; subst.
    inversion H9; subst.
    inversion H12; subst.
    inversion H14; subst.
    inversion H16; subst.
    inversion H17; subst.
    inversion H19; subst.
    simpl in *.
    rewrite H10 in Hb.
    unfold new_array_queue in Hb.
    inversion Hb.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    intuition.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    intuition.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    all : try (eapply substitute_eq_binds_v' in Hbinds0;
    unfold binds in Hbinds0;
    rewrite Hb in Hbinds0;
    discriminate).
    auto.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply substitute_neq_preserves_binds' in Hb; auto.
    all : assert (Htmp : pid0 =? pid = false) by
    (apply Nat.eqb_neq; intuition);
    rewrite Htmp; auto.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply binds_push_eq_inv in Hb; discriminate.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply binds_push_neq_inv in Hb; auto.
  - destruct act.
  - destruct act.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    assert (Htmp : pid0 # (remove pc pid0)) by
    (apply ok_remove_notin; auto);
    apply binds_in in Hb;
    unfold "#" in Htmp; intuition.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply remove_preserves_binds_notin in Hb; auto.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H4; subst; simpl in *;
    (eapply substitute_eq_binds_v' in Hbinds0;
    unfold binds in Hbinds0;
    rewrite Hb in Hbinds0;
    discriminate).
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H4; subst; simpl in *;
    apply substitute_neq_preserves_binds' in Hb; auto.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    subst.
    inversion H1; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *;
    (eapply substitute_eq_binds_v' in Hbinds0;
    unfold binds in Hbinds0;
    rewrite Hb in Hbinds0;
    discriminate).
    inversion H1; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *;
    apply substitute_neq_preserves_binds' in Hb; auto.
Qed.

Lemma inv_e27_x_none_invariant:
  composed_lts.invariant (composed_array_queue L)
  inv_e27_x_none.
Proof.
  apply invariant_ind_to_invariant'.
  apply inv_e27_x_none_inv.
Qed.

Definition inv_e28_x_none (s : composed_lts.state (composed_array_queue L)) :=
  let sync_acc := s.(Compose.L1State) in
  let acc := sync_acc.(LState) in
  let sync_ary := acc.(Tensor.L1State) in
  let ary := sync_ary.(LState) in
  let sync_front_rear := acc.(Tensor.L2State) in
  let front_rear := sync_front_rear.(LState) in
  let sync_front := front_rear.(Tensor.L1State) in
  let front := sync_front.(LState) in
  let sync_rear := front_rear.(Tensor.L2State) in
  let rear := sync_rear.(LState) in
  let sync_aqimpl := s.(Compose.L2State) in
  let aqimpl := sync_aqimpl.(LState) in
  let pc := aqimpl.(pc) in
  (forall pid,
    binds pid AEnq28 pc ->
      fst (aqimpl.(ArrayQueueImpl.x) pid) = None
  ) /\ composed_lts.reachable (composed_array_queue L) s.

Lemma inv_e28_x_none_inv:
  composed_lts.invariant_ind (composed_array_queue L)
  inv_e28_x_none.
Proof.
  unfold inv_e28_x_none.
  apply invariant_ind''_imply_invariant_ind_land.
  unfold invariant_ind''. intuition.
  apply reachable_is_invariant.
  unfold about. intuition.
  - rename H1 into Hb.
    inversion H0; subst.
    inversion H1; subst.
    inversion H2; subst.
    inversion H3; subst.
    inversion H5; subst.
    inversion H7; subst.
    inversion H8; subst.
    inversion H9; subst.
    inversion H12; subst.
    inversion H14; subst.
    inversion H16; subst.
    inversion H17; subst.
    inversion H19; subst.
    simpl in *.
    rewrite H10 in Hb.
    unfold new_array_queue in Hb.
    inversion Hb.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    --
    subst.
    inversion H1; subst; simpl in *.
    intuition.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    intuition.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    all : try (eapply substitute_eq_binds_v' in Hbinds0;
    unfold binds in Hbinds0;
    rewrite Hb in Hbinds0;
    discriminate).
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply substitute_neq_preserves_binds' in Hb; auto.
    all : assert (Htmp : pid0 =? pid = false) by
    (apply Nat.eqb_neq; intuition);
    rewrite Htmp; auto.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply binds_push_eq_inv in Hb; discriminate.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply binds_push_neq_inv in Hb; auto.
  - destruct act.
  - destruct act.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    assert (Htmp : pid0 # (remove pc pid0)) by
    (apply ok_remove_notin; auto);
    apply binds_in in Hb;
    unfold "#" in Htmp; intuition.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply remove_preserves_binds_notin in Hb; auto.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H4; subst; simpl in *;
    try (eapply substitute_eq_binds_v' in Hbinds0;
    unfold binds in Hbinds0;
    rewrite Hb in Hbinds0;
    discriminate).
    apply inv_e27_x_none_invariant in Hreach.
    apply Hreach in Hbinds0.
    simpl in Hbinds0.
    auto.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H4; subst; simpl in *;
    apply substitute_neq_preserves_binds' in Hb; auto.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb.
    destruct (eq_nat_dec pid pid0).
    subst.
    inversion H1; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *;
    (eapply substitute_eq_binds_v' in Hbinds0;
    unfold binds in Hbinds0;
    rewrite Hb in Hbinds0;
    discriminate).
    inversion H1; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *;
    apply substitute_neq_preserves_binds' in Hb; auto.
Qed.

Lemma inv_e28_x_none_invariant:
  composed_lts.invariant (composed_array_queue L)
  inv_e28_x_none.
Proof.
  apply invariant_ind_to_invariant'.
  apply inv_e28_x_none_inv.
Qed.

End INV.
