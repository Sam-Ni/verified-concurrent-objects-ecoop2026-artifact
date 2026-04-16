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
  ArrayQueueInvariantBefore0
  ArrayQueueInvariantBefore02.
Import ListNotations.

Section test.

Arguments get_pc {L}.
Arguments get_xp {L}.
Arguments get_ary {L}.
Arguments get_impl {L}.
Arguments get_rear {L}.
Arguments get_front {L}.
Arguments R {L}.

Variable L : nat.

Lemma inv_d27_stuttering : forall s s' acts pid,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  binds pid ADeq27 (get_pc s) ->
  length (gather_pid_events_B pid acts) = 0 ->
  (get_impl s).(front) pid = (get_impl s').(front) pid.
Proof.
  induction 1; simpl; intros.
  - subst. intuition.
  - unfold get_pc in *; simpl in *.
    inversion H; subst; simpl in *.
    intuition.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      unfold get_pc in *; intros.
      inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      unfold binds in H1.
      inversion H4; subst; simpl in *.
      all : try (rewrite Hbinds0 in H1; discriminate).
    -- rewrite <-IHvalid_execution_fragment; auto.
      unfold get_pc, get_impl in *; simpl in *.
      inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      inversion H4; subst; simpl in *.
      all : auto.
      apply Nat.eqb_neq in n; rewrite n; auto.
      unfold get_pc, get_impl in *; simpl in *.
      inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      inversion H4; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - inversion H.
  - inversion H.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      unfold get_pc in H1.
      apply binds_in in H1.
      unfold get_pc in H1; simpl in H1.
      inversion H4; subst; simpl in *;
      unfold "#" in Hnotin_pc; intuition.
    -- inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *. 
      unfold get_pc in *; simpl in *.
      inversion H4; subst; simpl in *.
      eapply IHvalid_execution_fragment; eauto.
      apply binds_push_neq; auto.
      apply Nat.eqb_neq in n; rewrite n in H2; auto.
      eapply IHvalid_execution_fragment; eauto.
      apply binds_push_neq; auto.
      apply Nat.eqb_neq in n; rewrite n in H2; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      unfold get_pc in H1; simpl in *.
      unfold binds in H1.
      inversion H4; subst; simpl in *;
      rewrite Hbinds0 in H1; discriminate.
    -- inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *. 
      unfold get_pc in *; simpl in *.
      inversion H4; subst; simpl in *.
      eapply IHvalid_execution_fragment; eauto.
      apply remove_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H2; auto.
      eapply IHvalid_execution_fragment; eauto.
      apply remove_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H2; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      rewrite Nat.eqb_refl in H2.
      simpl in H2.
      inversion H2.
    -- inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *. 
      unfold get_pc in *; simpl in *.
      inversion H5; subst; simpl in *.
      all : eapply IHvalid_execution_fragment; eauto;
      [apply substitute_neq_preserves_binds; auto |
      apply Nat.eqb_neq in n; rewrite n in H2; auto].
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      rewrite Nat.eqb_refl in H2.
      simpl in H2.
      inversion H2.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      inversion H5; subst; simpl in *.
      all : eapply IHvalid_execution_fragment; eauto;
      [apply substitute_neq_preserves_binds; auto |
      apply Nat.eqb_neq in n; rewrite n in H2; auto].
Qed.

Lemma inv_impl_front_keep'': forall s s' acts pid,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s' acts ->
  forall v 
  (Hv: before_d27 v)
  (Hv' : after_d3 v),
  binds pid v (get_pc s) ->
  length (gather_pid_events_B pid acts) = calculate_before27 v ->
  binds pid (ADeq27) (get_pc s') ->
  (get_impl s).(ArrayQueueImpl.front) pid = (get_impl s').(ArrayQueueImpl.front) pid.
Proof.
  induction 1; intros.
  - subst. simpl in H1.
    unfold after_d3 in Hv'.
    unfold after_d6 in Hv'.
    intuition; try discriminate.
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
      inversion H5; subst; simpl in *.
      rewrite Hbinds0 in H1;
      inversion H1; subst;
      unfold after_d3 in Hv';
      unfold after_d6 in Hv';
      intuition; subst; try discriminate;
      try (destruct H6; subst; discriminate);
      try (destruct H7; subst; discriminate).


Ltac solve_before_d13 :=
  try apply before_d13_Deq1;
  try apply before_d13_Deq2;
  try apply before_d13_Deq3;
  try apply before_d13_Deq4;
  try apply before_d13_Deq5;
  try apply before_d13_Deq6;
  try apply before_d13_Deq10;
  try apply before_d13_Deq11;
  try apply before_d13_Deq12.

Ltac solve_before_d27 :=
  try apply before_d27_Deq13;
  try apply before_d27_Deq14;
  try apply before_d27_Deq15;
  try apply before_d27_Deq26;
  try (unfold before_d27;
  left;
  solve_before_d13).

      Ltac solve_after_d6 :=
        try apply after_d6_Deq10;
        try apply after_d6_Deq11;
        try apply after_d6_Deq12;
        try apply after_d6_Deq13;
        try apply after_d6_Deq14;
        try apply after_d6_Deq15;
        try apply after_d6_Deq26;
        try apply after_d6_Deq27;
        try apply after_d6_Deq28.

Ltac solve_after_d3 :=
  try apply after_d3_Deq4;
  try apply after_d3_Deq5;
  try apply after_d3_Deq6;
  try (unfold after_d6;
  right; right; right;
  solve_after_d6).

      all : try (eapply inv_before_d27_least_B_events in H0;
      unfold get_pc; simpl;
      try (eapply substitute_eq_binds_v'; eauto); solve_before_d27; auto;
      simpl in H0;
      rewrite Hbinds0 in H1;
      inversion H1; subst;
      simpl in H2; lia).

      all : rewrite Hbinds0 in H1;
      inversion H1; subst;
      unfold before_d27 in Hv;
      unfold before_d13  in Hv;
      intuition; try discriminate;
      try (destruct H6; subst; discriminate);
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate).

      unfold after_d3 in Hv'.
      unfold after_d6 in Hv'.
      intuition; try discriminate;
      try (destruct H6 as [r' Hr']; subst; discriminate);
      try (destruct H8 as [r' Hr']; subst; discriminate).

      erewrite IHvalid_execution_fragment;
      try (eapply substitute_eq_binds_v'; eauto);
      eauto;
      [solve_before_d27|solve_after_d3].

      erewrite IHvalid_execution_fragment;
      try (eapply substitute_eq_binds_v'; eauto);
      eauto;
      [solve_before_d27|solve_after_d3].

      erewrite IHvalid_execution_fragment;
      try (eapply substitute_eq_binds_v'; eauto);
      eauto;
      [solve_before_d27|solve_after_d3].

      simpl in H2.
      eapply inv_d27_stuttering in H0; eauto;
      unfold get_pc; simpl;
      eapply substitute_eq_binds_v'; eauto.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_impl, get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
      2 : {
        inversion H5; subst; simpl in *;
        apply substitute_neq_preserves_binds; auto.
      }
      inversion H5; subst; simpl in *.
      all : try rewrite H3; auto.
      apply Nat.eqb_neq in n; rewrite n in H3;
      rewrite H3; auto.
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
      unfold before_d27 in Hv;
      unfold before_d13 in Hv;
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
      rewrite Hbinds0 in H1;
      inversion H1; subst;
      unfold before_d27 in Hv;
      unfold before_d13 in Hv;
      intuition; subst; try discriminate;
      try (destruct H6; subst; discriminate);
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate).
      unfold after_d3 in Hv'.
      unfold after_d6 in Hv'.
      intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      try (destruct H9; subst; discriminate).
      all : erewrite IHvalid_execution_fragment;
      try (eapply substitute_eq_binds_v'; eauto);
      auto; [solve_before_d27|solve_after_d3].
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
      unfold before_d27 in Hv;
      unfold before_d13 in Hv;
      intuition; subst; try discriminate;
      try (destruct H6; subst; discriminate);
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate).
      unfold after_d3 in Hv'.
      unfold after_d6 in Hv'.
      intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      try (destruct H9; subst; discriminate).
      all : erewrite IHvalid_execution_fragment;
      try (eapply substitute_eq_binds_v'; eauto);
      auto; [solve_before_d27|solve_after_d3].
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