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

Arguments get_pc {L}.
Arguments get_xp {L}.
Arguments get_ary {L}.
Arguments get_impl {L}.
Arguments get_rear {L}.
Arguments R {L}.

Variable L : nat.

Lemma inv_e27_stuttering : forall s s' acts pid,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  binds pid AEnq27 (get_pc s) ->
  length (gather_pid_events_B pid acts) = 0 ->
  (get_impl s).(rear) pid = (get_impl s').(rear) pid.
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
      apply Nat.eqb_neq in n; rewrite n; auto.
      all : auto.
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

Lemma inv_impl_rear_keep'': forall s s' acts pid,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s' acts ->
  forall v 
  (Hv: before_e27 v)
  (Hv' : after_e3 v),
  binds pid v (get_pc s) ->
  length (gather_pid_events_B pid acts) = calculate_before27 v ->
  binds pid (AEnq27) (get_pc s') ->
  (get_impl s).(ArrayQueueImpl.rear) pid = (get_impl s').(ArrayQueueImpl.rear) pid.
Proof.
  induction 1; intros.
  - subst. simpl in H1.
    unfold after_e3 in Hv'.
    unfold after_e6 in Hv'.
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
      unfold after_e3 in Hv';
      unfold after_e6 in Hv';
      intuition; subst; try discriminate;
      try (destruct H6; subst; discriminate);
      try (destruct H7; subst; discriminate).

Ltac solve_before_e13 :=
  try apply before_e13_Enq1;
  try apply before_e13_Enq2;
  try apply before_e13_Enq3;
  try apply before_e13_Enq4;
  try apply before_e13_Enq5;
  try apply before_e13_Enq6;
  try apply before_e13_Enq10;
  try apply before_e13_Enq11;
  try apply before_e13_Enq12.

Ltac solve_before_e27 :=
  try apply before_e27_Enq13;
  try apply before_e27_Enq14;
  try apply before_e27_Enq15;
  try apply before_e27_Enq26;
  try (unfold before_e27;
  left;
  solve_before_e13).

      Ltac solve_after_e6 :=
        try apply after_e6_Enq10;
        try apply after_e6_Enq11;
        try apply after_e6_Enq12;
        try apply after_e6_Enq13;
        try apply after_e6_Enq14;
        try apply after_e6_Enq15;
        try apply after_e6_Enq26;
        try apply after_e6_Enq27;
        try apply after_e6_Enq28.

Ltac solve_after_e3 :=
  try apply after_e3_Enq4;
  try apply after_e3_Enq5;
  try apply after_e3_Enq6;
  try (unfold after_e6;
  right; right; right;
  solve_after_e6).

      erewrite IHvalid_execution_fragment;
      try (eapply substitute_eq_binds_v'; eauto);
      rewrite Hbinds0 in H1;
      inversion H1; subst;
      auto;
      [solve_before_e27|solve_after_e3].

      all : try (eapply inv_before27_least_B_events in H0;
      unfold get_pc; simpl;
      try (eapply substitute_eq_binds_v'; eauto); solve_before_e27; auto;
      simpl in H0;
      rewrite Hbinds0 in H1;
      inversion H1; subst;
      simpl in H2; lia).

      erewrite IHvalid_execution_fragment;
      try (eapply substitute_eq_binds_v'; eauto);
      rewrite Hbinds0 in H1;
      inversion H1; subst;
      auto;
      [solve_before_e27|solve_after_e3].

      erewrite IHvalid_execution_fragment;
      try (eapply substitute_eq_binds_v'; eauto);
      rewrite Hbinds0 in H1;
      inversion H1; subst;
      auto;
      [solve_before_e27|solve_after_e3].

      rewrite Hbinds0 in H1;
      inversion H1; subst.
      simpl in H2.
      eapply inv_e27_stuttering in H0; eauto;
      unfold get_pc; simpl;
      eapply substitute_eq_binds_v'; eauto.
      all : rewrite Hbinds0 in H1;
      inversion H1; subst;
      unfold before_e27 in Hv;
      unfold before_e13  in Hv;
      intuition; try discriminate;
      try (destruct H6; subst; discriminate);
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate).
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_impl, get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
      2 : {
        inversion H5; subst; simpl in *;
        apply substitute_neq_preserves_binds; auto.
      }
      inversion H5; subst; simpl in *.
      apply Nat.eqb_neq in n; rewrite n in H3;
      rewrite H3; auto.
      all : rewrite H3; auto.
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
      unfold before_e27 in Hv;
      unfold before_e13 in Hv;
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
      unfold before_e27 in Hv;
      unfold before_e13 in Hv;
      intuition; subst; try discriminate;
      try (destruct H6; subst; discriminate);
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate).
      unfold after_e3 in Hv'.
      unfold after_e6 in Hv'.
      intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      try (destruct H9; subst; discriminate).
      all : erewrite IHvalid_execution_fragment;
      try (eapply substitute_eq_binds_v'; eauto);
      auto; [solve_before_e27|solve_after_e3].
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
      unfold before_e27 in Hv;
      unfold before_e13 in Hv;
      intuition; subst; try discriminate;
      try (destruct H6; subst; discriminate);
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate).
      unfold after_e3 in Hv'.
      unfold after_e6 in Hv'.
      intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      try (destruct H9; subst; discriminate).
      all : erewrite IHvalid_execution_fragment;
      try (eapply substitute_eq_binds_v'; eauto);
      auto; [solve_before_e27|solve_after_e3].
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