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
  ArrayQueueInvariantBefore0.
Import ListNotations.

Section test.

Arguments get_pc {L}.
Arguments get_xp {L}.
Arguments get_ary {L}.
Arguments get_impl {L}.
Arguments get_rear {L}.

Variable L : nat.

Ltac solve_after_d6 :=
  try apply after_d6_Deq10;
  try apply after_d6_Deq11;
  try apply after_d6_Deq12;
  try apply after_d6_Deq13;
  try apply after_d6_Deq14;
  try apply after_d6_Deq15;
  try apply after_d6_Deq26;
  try apply after_d6_Deq27.

Lemma inv_d27_from_d6_ret': forall k s,
  reachable_len' (composed_array_queue L) s k ->
  forall pid,
    binds pid ADeq27 (get_pc s) ->
    exists s' acts ret n,
      composed_lts.valid_execution_fragment (composed_array_queue L) s' s acts /\
      binds pid (ADeq6 ret) (get_pc s') /\
      length (gather_pid_events_B pid acts) = 4 /\
      reachable_len' (composed_array_queue L) s' n /\
      n < k /\
      (get_xp s) pid = ret.
Proof.
  intros. eapply inv_d27_from_d6_ret in H; eauto; solve_after_d6.
  destruct H as [s' [acts [ret [n [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]].
  exists s', acts, ret, n.
  intuition.
  eapply inv_d6_ret_d27_xp; eauto; solve_after_d6.
  apply valid_execution_fragment_to_new_valid_execution_fragment; auto.
Qed.

Lemma inv_d27_from_d6_ret_k_step': forall k s,
  reachable_len' (composed_array_queue L) s k ->
  forall pid,
    binds pid ADeq27 (get_pc s) ->
    exists s' acts ret n t,
      valid_execution_fragment_len' (composed_array_queue L) s' s acts t /\
      binds pid (ADeq6 ret) (get_pc s') /\
      length (gather_pid_events_B pid acts) = 4 /\
      reachable_len' (composed_array_queue L) s' n /\
      n < k /\
      k = n + t /\
      (get_xp s) pid = ret.
Proof.
  intros. eapply inv_d27_from_d6_ret_k_step in H; eauto; solve_after_d6.
  destruct H as [s' [acts [ret [n [t [Hvalid [Hb [Hgather [Hr [Hlt Heq]]]]]]]]]].
  exists s', acts, ret, n, t.
  intuition.
  eapply inv_d6_ret_d27_xp; eauto; solve_after_d6.
  apply valid_execution_fragment_to_new_valid_execution_fragment; auto.
  eapply valid_execution_fragment_len'_to_valid_execution_fragment; eauto.
Qed.

Lemma inv_d27_from_d5_internal_ret: forall k s,
  reachable_len' (composed_array_queue L) s k ->
  forall pid,
    binds pid ADeq27 (get_pc s) ->
    exists s1 s2 acts ret n,
      composed_lts.valid_execution_fragment (composed_array_queue L) s2 s acts /\
      composed_lts.step_L1 (composed_array_queue L)
      s1 pid ((@intL1 li_array li_cnt_cnt (array L) ArrayQueue.front_rear int_ary_read)) s2 /\
      binds pid (ADeq5) (get_pc s1) /\
      (length (gather_pid_events_B pid acts)) = 5 /\
      reachable_len' (composed_array_queue L) s1 n /\
      n < k /\
      binds pid (AryReadOk ret) (get_ary s2).(Array.responses L) /\
      (get_xp s) pid = ret.
Proof.
  intros.
  eapply inv_d27_from_d6_ret' in H; eauto; solve_after_d6.
  destruct H as [s' [acts [ret [n [Hvalid [Hb [Hgather [Hr [Hlt Hxp]]]]]]]]].
  eapply inv_d6_ret_d5_internal_step with (pid:=pid) (v:=ADeq6 ret) (ret:=ret) in Hr; eauto.
  2 : {
    unfold has_read_ary. intuition.
  }
  destruct Hr as [s1 [s2 [acts' [n' [Hvalid' [Hstep [Hb' [Hgather' [Hr' Hlt']]]]]]]]].
  exists s1, s2. exists (acts' ++ acts).
  exists ret, n'.
  intuition.
  eapply composed_lts.valid_execution_fragment_join' with (a':=acts); eauto.
  rewrite gather_pid_events_B_dist.
  rewrite app_length.
  rewrite Hgather, Hgather'.
  simpl. reflexivity.
  lia.
  inversion Hstep; subst; simpl in *.
  inversion H; subst; simpl in *.
  inversion H1; subst; simpl in *.
  inversion H3; subst; simpl in *.
  inversion H2; subst; simpl in *.
  eapply inv_d5_ret_d6_ret in Hb; eauto.
  erewrite <-Hb.
  apply binds_push_eq; auto.
  simpl.
  apply binds_push_eq; auto.
Qed.

Lemma inv_d27_from_d5_internal_ret_k_step: forall k s,
  reachable_len' (composed_array_queue L) s k ->
  forall pid,
    binds pid ADeq27 (get_pc s) ->
    exists s1 s2 acts ret n t,
      valid_execution_fragment_len' (composed_array_queue L) s2 s acts t /\
      composed_lts.step_L1 (composed_array_queue L)
      s1 pid ((@intL1 li_array li_cnt_cnt (array L) ArrayQueue.front_rear int_ary_read)) s2 /\
      binds pid (ADeq5) (get_pc s1) /\
      (length (gather_pid_events_B pid acts)) = 5 /\
      reachable_len' (composed_array_queue L) s1 n /\
      n < k /\
      k = n + 1 + t /\
      binds pid (AryReadOk ret) (get_ary s2).(Array.responses L) /\
      (get_xp s) pid = ret.
Proof.
  intros.
  eapply inv_d27_from_d6_ret_k_step' in H; eauto; solve_after_d6.
  destruct H as [s' [acts [ret [n [t [Hvalid [Hb [Hgather [Hr [Hlt [Heq Hxp]]]]]]]]]]].
  eapply inv_d6_ret_d5_internal_step_k_step with (pid:=pid) (v:=ADeq6 ret) (ret:=ret) in Hr; eauto.
  2 : {
    unfold has_read_ary. intuition.
  }
  destruct Hr as [s1 [s2 [acts' [n' [t' [Hvalid' [Hstep [Hb' [Hgather' [Hr' [Hlt' Heq']]]]]]]]]]].
  exists s1, s2. exists (acts' ++ acts).
  exists ret, n', (t' + t).
  intuition.
  eapply valid_execution_fragment_len'_join' with (a':=acts); eauto.
  rewrite gather_pid_events_B_dist.
  rewrite app_length.
  rewrite Hgather, Hgather'.
  simpl. reflexivity.
  lia.
  subst; lia.
  inversion Hstep; subst; simpl in *.
  inversion H; subst; simpl in *.
  inversion H1; subst; simpl in *.
  inversion H3; subst; simpl in *.
  inversion H2; subst; simpl in *.
  apply valid_execution_fragment_len'_to_valid_execution_fragment in Hvalid'; eauto.
  eapply inv_d5_ret_d6_ret in Hb; eauto.
  erewrite <-Hb.
  apply binds_push_eq; auto.
  simpl.
  apply binds_push_eq; auto.
Qed.

Lemma inv_d13_stuttering : forall s s' acts pid,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  binds pid ADeq13 (get_pc s) ->
  length (gather_pid_events_B pid acts) = 0 ->
  binds pid ADeq13 (get_pc s').
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
    -- unfold get_pc in *; simpl in *.
      inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      inversion H4; subst; simpl in *;
      eapply IHvalid_execution_fragment; eauto;
      eapply substitute_neq_preserves_binds; eauto.
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

End test.

Section test.

Arguments get_pc {L}.
Arguments get_xp {L}.
Arguments get_ary {L}.
Arguments get_impl {L}.

Variable L : nat.
Hypothesis H : L > 0.

Definition get_vec_front s pid :=
  (Vector.nth
    ((get_ary s).(Array.vec L))
    (Fin.of_nat_lt (mod_lt H
                    ((get_impl s).(ArrayQueueImpl.front) pid)))).
  
Lemma inv_d27_from_d5_keeps_vec_rear: forall k s,
  reachable_len' (composed_array_queue L) s k ->
  forall pid,
    binds pid ADeq27 (get_pc s) ->
    exists s1 s2 acts ret n,
      composed_lts.valid_execution_fragment (composed_array_queue L) s2 s acts /\
      composed_lts.step_L1 (composed_array_queue L)
      s1 pid ((@intL1 li_array li_cnt_cnt (array L) ArrayQueue.front_rear int_ary_read)) s2 /\
      binds pid (ADeq5) (get_pc s1) /\
      (length (gather_pid_events_B pid acts)) = 5 /\
      reachable_len' (composed_array_queue L) s1 n /\
      n < k /\
      binds pid (AryReadOk ret) (get_ary s2).(Array.responses L) /\
      (get_xp s) pid = ret /\
      (
        ((get_impl s).(ArrayQueueImpl.x) pid) = get_vec_front s pid ->
        get_vec_front s pid = get_vec_front s2 pid
      ).
Proof.
  intros.
  unfold get_vec_front.
  eapply inv_d27_from_d5_internal_ret in H0; eauto.
  destruct H0 as [s1 [s2 [acts [ret [n [Hvalid [Hstep [Hb [Hgather [Hr [Hlt [Hb' Hxp]]]]]]]]]]]].
  exists s1, s2, acts, ret, n. intuition.
  unfold get_impl in H0; simpl in H0.
  unfold get_xp in Hxp; simpl in Hxp.
  rewrite Hxp in H0.
  unfold get_impl; simpl in *.
  rewrite <-H0.
  inversion Hstep; subst; simpl in *.
  inversion H2; subst; simpl in *.
  inversion H3; subst; simpl in *.
  inversion H5; subst; simpl in *.
  inversion H4; subst; simpl in *.
  apply binds_push_eq_inv in Hb'.
  inversion Hb'; subst; simpl in *.
  rewrite H7.
  eapply inv_d5_instant in Hr; eauto.
  simpl in Hr.
  unfold get_impl in Hr; simpl in Hr.
  unfold binds in Hbinds3.
  rewrite Hr in Hbinds3.
  inversion Hbinds3; subst; simpl in *.
  erewrite Fin.of_nat_ext; eauto.
Qed.

Lemma inv_d27_from_d5_keeps_vec_rear_k_step: forall k s,
  reachable_len' (composed_array_queue L) s k ->
  forall pid,
    binds pid ADeq27 (get_pc s) ->
    exists s1 s2 acts ret n t,
      valid_execution_fragment_len' (composed_array_queue L) s2 s acts t /\
      composed_lts.step_L1 (composed_array_queue L)
      s1 pid ((@intL1 li_array li_cnt_cnt (array L) ArrayQueue.front_rear int_ary_read)) s2 /\
      binds pid (ADeq5) (get_pc s1) /\
      (length (gather_pid_events_B pid acts)) = 5 /\
      reachable_len' (composed_array_queue L) s1 n /\
      n < k /\
      k = n + 1 + t /\
      binds pid (AryReadOk ret) (get_ary s2).(Array.responses L) /\
      (get_xp s) pid = ret /\
      (
        ((get_impl s).(ArrayQueueImpl.x) pid) = get_vec_front s pid ->
        get_vec_front s pid = get_vec_front s2 pid
      ).
Proof.
  intros.
  unfold get_vec_front.
  eapply inv_d27_from_d5_internal_ret_k_step in H0; eauto.
  destruct H0 as [s1 [s2 [acts [ret [n [t [Hvalid [Hstep [Hb [Hgather [Hr [Hlt [Heq [Hb' Hxp]]]]]]]]]]]]]].
  exists s1, s2, acts, ret, n, t. intuition.
  unfold get_impl in H0; simpl in H0.
  unfold get_xp in Hxp; simpl in Hxp.
  rewrite Hxp in H0.
  unfold get_impl; simpl in *.
  rewrite <-H0.
  inversion Hstep; subst; simpl in *.
  inversion H2; subst; simpl in *.
  inversion H3; subst; simpl in *.
  inversion H5; subst; simpl in *.
  inversion H4; subst; simpl in *.
  apply binds_push_eq_inv in Hb'.
  inversion Hb'; subst; simpl in *.
  rewrite H7.
  eapply inv_d5_instant in Hr; eauto.
  simpl in Hr.
  unfold get_impl in Hr; simpl in Hr.
  unfold binds in Hbinds3.
  rewrite Hr in Hbinds3.
  inversion Hbinds3; subst; simpl in *.
  erewrite Fin.of_nat_ext; eauto.
Qed.

End test.

Section test.

Context {liA liB liC : language_interface}.
Variable L: composed_lts.composed_lts liA liB liC.

Definition automaton_step' st st' pid : Prop :=
  (
  (exists int, composed_lts.step_L1 L st pid int st') \/
  (exists int, composed_lts.step_L2 L st pid int st') \/
  (exists qc, composed_lts.initial_state L st pid qc st') \/
  (exists rc, composed_lts.final_state L st pid rc st') \/
  (exists qa, composed_lts.at_external L st pid qa st') \/
  (exists ra, composed_lts.after_external L st pid ra st') \/
  (exists qb, composed_lts.internal_query L st pid qb st') \/
  (exists rb, composed_lts.internal_reply L st pid rb st')
  ).

Lemma reachable_valid_execution: forall s s' acts,
  composed_lts.reachable L s ->
  composed_lts.valid_execution_fragment L s s' acts ->
  composed_lts.reachable L s'.
Proof.
  unfold composed_lts.reachable.
  intros.
  destruct H as [init [acts' [Hnew Hvalid]]].
  exists init, (acts' ++ acts).
  intuition.
  eapply composed_lts.valid_execution_fragment_join' with (a':=acts); eauto.
Qed.

End test.

Section test.

Arguments get_pc {L}.
Arguments get_xp {L}.
Arguments get_ary {L}.
Arguments get_impl {L}.
Arguments get_rear {L}.
Arguments get_front {L}.
Arguments R {L}.

Variable L : nat.

Definition before_d13 v :=
  v = ADeq1 \/
  v = ADeq2 \/
  (exists r, v = ADeq3 r) \/
  v = ADeq4 \/
  v = ADeq5 \/
  (exists r, v = ADeq6 r) \/
  v = ADeq10 \/
  v = ADeq11 \/
  (exists r, v = ADeq12 r).

Lemma before_d13_Deq1:
  before_d13 (ADeq1).
Proof.
  intros.
  unfold before_d13.
  intuition.
Qed.

Lemma before_d13_Deq2:
  before_d13 (ADeq2).
Proof.
  intros.
  unfold before_d13.
  intuition.
Qed.

Lemma before_d13_Deq3: forall ret,
  before_d13 (ADeq3 ret).
Proof.
  intros.
  unfold before_d13.
  right. right. left.
  exists ret.
  reflexivity.
Qed.

Lemma before_d13_Deq4:
  before_d13 (ADeq4).
Proof.
  intros.
  unfold before_d13.
  intuition.
Qed.

Lemma before_d13_Deq5:
  before_d13 (ADeq5).
Proof.
  intros.
  unfold before_d13.
  intuition.
Qed.

Lemma before_d13_Deq6: forall ret,
  before_d13 (ADeq6 ret).
Proof.
  intros.
  unfold before_d13.
  right. right. right. right. right. left.
  exists ret.
  reflexivity.
Qed.

Lemma before_d13_Deq10:
  before_d13 (ADeq10).
Proof.
  intros.
  unfold before_d13.
  intuition.
Qed.

Lemma before_d13_Deq11:
  before_d13 (ADeq11).
Proof.
  intros.
  unfold before_d13.
  intuition.
Qed.

Lemma before_d13_Deq12: forall ret,
  before_d13 (ADeq12 ret).
Proof.
  intros.
  unfold before_d13.
  right. right. right. right. right.
  right. right. right.
  exists ret.
  reflexivity.
Qed.

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

Definition before_d27 v :=
  before_d13 v \/
  v = ADeq13 \/
  v = ADeq14  \/
  (exists r, v = ADeq15 r) \/
  v = ADeq26.

Lemma before_d27_Deq13:
  before_d27 (ADeq13).
Proof.
  intros.
  unfold before_d27.
  intuition.
Qed.

Lemma before_d27_Deq14:
  before_d27 (ADeq14).
Proof.
  intros.
  unfold before_d27.
  intuition.
Qed.

Lemma before_d27_Deq15: forall ret,
  before_d27 (ADeq15 ret).
Proof.
  intros.
  unfold before_d27.
  right. right. right. left.
  exists ret.
  reflexivity.
Qed.

Lemma before_d27_Deq26:
  before_d27 (ADeq26).
Proof.
  intros.
  unfold before_d27.
  intuition.
Qed.

Ltac solve_before_d27 :=
  (* try unfold before_e27;
  try unfold before_e13; *)
  try apply before_d27_Deq13;
  try apply before_d27_Deq14;
  try apply before_d27_Deq15;
  try apply before_d27_Deq26;
  try (unfold before_d27;
  left;
  solve_before_d13).

Definition calculate_before27 v :=
  match v with
  | ADeq1 => 8
  | ADeq2 => 7
  | ADeq3 r => 6
  | ADeq4 => 6
  | ADeq5 => 5
  | ADeq6 r => 4
  | ADeq10 => 4
  | ADeq11 => 3
  | ADeq12 r => 2
  | ADeq13 => 2
  | ADeq14  => 1
  | ADeq15 r => 0
  | ADeq26 => 0
  | _ => 0
  end.

Lemma inv_before_d27_least_B_events: forall s s' acts pid,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  forall v,
  before_d27 v ->
  binds pid v (get_pc s) ->
  binds pid ADeq27 (get_pc s') ->
  length (gather_pid_events_B pid acts) >= calculate_before27 v.
Proof.
  induction 1; intros.
  - subst. unfold before_d27 in H0.
    unfold binds in H2.
    intuition; subst; try (rewrite H1 in H2; discriminate).
    unfold before_d13 in H.
    intuition; subst; try (rewrite H1 in H2; discriminate).
    (* destruct H as [r Hr]; subst.
    rewrite H1 in H2; discriminate. *)
    all : try (destruct H0 as [r Hr]; subst;
    rewrite H1 in H2; discriminate).
    all : try (destruct H as [r Hr]; subst;
    rewrite H1 in H2; discriminate).
  - inversion H; subst; simpl in *.
    unfold get_pc in *; simpl in *.
    eapply IHvalid_execution_fragment; eauto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H2.
      inversion H5; subst; simpl in *.
      all : try (rewrite Hbinds0 in H2;
      inversion H2; subst; simpl in *;
      eapply IHvalid_execution_fragment in H3;
      try (eapply substitute_eq_binds_v'; eauto); solve_before_d27;
      simpl in H3; lia).
      all : try (rewrite Hbinds0 in H2;
      inversion H2; subst; simpl in *; lia).
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      (* unfold binds in H2. *)
      inversion H5; subst; simpl in *;
      eapply IHvalid_execution_fragment; eauto;
      apply substitute_neq_preserves_binds; auto.
  - inversion H.
  - inversion H.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      apply binds_in in H2.
      inversion H5; subst; simpl in *;
      unfold "#" in Hnotin_pc; intuition.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H5; subst; simpl in *;
      apply binds_push_neq; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      rewrite Nat.eqb_refl.
      unfold binds in H2.
      inversion H5; subst; simpl in *; simpl;
      rewrite Hbinds0 in H2;
      inversion H2; subst; simpl; lia.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H5; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      rewrite Nat.eqb_refl.
      unfold binds in H2.
      simpl.
      inversion H6; subst; simpl in *.
      all : try (rewrite Hbinds0 in H2;
      inversion H2; subst;
      eapply IHvalid_execution_fragment in H3;
      try (eapply substitute_eq_binds_v'; eauto); solve_before_d27;
      simpl in H3; simpl; lia).
      all : rewrite Hbinds0 in H2;
      inversion H2; subst; simpl; lia.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H6; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      rewrite Nat.eqb_refl.
      unfold binds in H2.
      simpl.
      inversion H6; subst; simpl in *.
      all : try (rewrite Hbinds0 in H2;
      inversion H2; subst;
      eapply IHvalid_execution_fragment in H3;
      try (eapply substitute_eq_binds_v'; eauto); solve_before_d27;
      simpl in H3; simpl; lia).
      all : rewrite Hbinds0 in H2;
      inversion H2; subst; simpl; lia.
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H6; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
Qed.

Lemma inv_before_d13_go_through_13: forall s s' acts pid,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  forall v (Hv : before_d13 v),
  binds pid v (get_pc s) ->
  binds pid ADeq27 (get_pc s') ->
  length (gather_pid_events_B pid acts) = calculate_before27 v ->
  exists s1 s2 acts1 acts2 it,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 /\
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s2 s' acts2 /\
  composed_lts.step_L2 (composed_array_queue L)
  s1 pid it s2 /\
  binds pid ADeq13 (get_pc s2).
Proof.
  induction 1; intros.
  - subst. simpl in H2.
    unfold before_d13 in Hv.
    intuition; subst; simpl in H2; try discriminate.
    destruct H; subst; discriminate.
    destruct H3; subst; discriminate.
    destruct H3; subst; discriminate.
  - inversion H; subst; simpl in *.
    unfold get_pc in *; simpl in *.
    eapply IHvalid_execution_fragment in H1; eauto.
    destruct H1 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
    exists s1, s2, acts1, acts2, it. intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L1; eauto.
    eapply composed_lts.Step_None; eauto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      inversion H5; subst; simpl in *;
      rewrite Hbinds0 in H1; try discriminate.
      all : try (
        unfold before_d13 in Hv;
        intuition; subst; try discriminate;
      try (destruct H6 as [t Ht]; subst);
      try (destruct H7 as [t Ht]; subst);
      try (destruct H8 as [t Ht]; subst);
      inversion H1; subst;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_d13;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2, acts1, acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto;
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto).
      inversion H1; subst.
      simpl in H3.
      eapply inv_before_d27_least_B_events in H0;
      unfold get_pc; simpl in *;
      eauto; simpl;
      try (eapply substitute_eq_binds_v'; eauto); solve_before_d27.
      simpl in H0. lia.
      eexists.
      eexists.
      exists [].
      exists acts.
      eexists.
      intuition.
      3 : { eauto. }
      eapply composed_lts.Step_None; eauto.
      eauto. simpl.
      eapply substitute_eq_binds_v'; eauto.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      inversion H5; subst; simpl in *;
      eapply IHvalid_execution_fragment in H2; eauto;
      try apply substitute_neq_preserves_binds; auto;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2, acts1, acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto;
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto.
  - inversion H.
  - inversion H.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      apply binds_in in H1.
      inversion H5; subst; simpl in *;
      unfold "#" in Hnotin_pc;
      intuition.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2; eauto.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
      exists s1, s2.
      eexists.
      exists acts2.
      eexists.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
      2 : { eauto. }
      eapply composed_lts.Step_Initial_Call; eauto.
      eapply composed_lts.Step_None; eauto.
      eauto.
      eauto.
      inversion H5; subst; simpl in *;
      apply binds_push_neq; auto.
      apply Nat.eqb_neq in n; rewrite n in H3; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      inversion H5; subst; simpl in *;
      rewrite Hbinds0 in H1;
      unfold before_d13 in Hv; intuition; subst; try discriminate;
      try (destruct H6; subst; discriminate);
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate).
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2; eauto.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
      exists s1, s2.
      eexists.
      exists acts2.
      eexists.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
      2 : { eauto. }
      eapply composed_lts.Step_Final_Return; eauto.
      eapply composed_lts.Step_None; eauto.
      eauto.
      eauto.
      inversion H5; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H3; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      rewrite Nat.eqb_refl in H3.
      simpl in H3.
      inversion H6; subst; simpl in *.
      all : rewrite Hbinds0 in H1;
      unfold before_d13 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      simpl in H3;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_d13;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join'; eauto;
      eapply composed_lts.Step_Internal_Query; eauto;
      eapply composed_lts.Step_None; eauto.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto.
      2 : { eauto. }
      eapply composed_lts.Step_Internal_Query; eauto.
      eapply composed_lts.Step_None; eauto.
      inversion H6; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H3; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      rewrite Nat.eqb_refl in H3.
      simpl in H3.
      inversion H6; subst; simpl in *;
      rewrite Hbinds0 in H1;
      unfold before_d13 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      simpl in H3;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_d13;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join'; eauto;
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto.
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto.
      2 : { eauto. }
      eapply composed_lts.Step_Internal_Reply; eauto.
      eapply composed_lts.Step_None; eauto.
      inversion H6; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H3; auto.
Qed.

Lemma inv_before_d13_go_through_13': forall s s' acts pid,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  forall v (Hv : before_d13 v),
  binds pid v (get_pc s) ->
  binds pid ADeq27 (get_pc s') ->
  length (gather_pid_events_B pid acts) = calculate_before27 v ->
  exists s1 s2 acts1 acts2 it,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 /\
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s2 s' acts2 /\
  composed_lts.step_L2 (composed_array_queue L)
  s1 pid it s2 /\
  binds pid ADeq13 (get_pc s2) /\
  acts = acts1 ++ acts2.
Proof.
  induction 1; intros.
  - subst. simpl in H2.
    unfold before_d13 in Hv.
    intuition; subst; simpl in H2; try discriminate.
    destruct H; subst; discriminate.
    destruct H3; subst; discriminate.
    destruct H3; subst; discriminate.
  - inversion H; subst; simpl in *.
    unfold get_pc in *; simpl in *.
    eapply IHvalid_execution_fragment in H1; eauto.
    destruct H1 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
    exists s1, s2, acts1, acts2, it. intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L1; eauto.
    eapply composed_lts.Step_None; eauto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      inversion H5; subst; simpl in *;
      rewrite Hbinds0 in H1; try discriminate.
      all : try (
        unfold before_d13 in Hv;
        intuition; subst; try discriminate;
      try (destruct H6 as [t Ht]; subst);
      try (destruct H7 as [t Ht]; subst);
      try (destruct H8 as [t Ht]; subst);
      inversion H1; subst;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_d13;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2, acts1, acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto;
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto).
      inversion H1; subst.
      simpl in H3.
      eapply inv_before_d27_least_B_events in H0;
      unfold get_pc; simpl in *;
      eauto; simpl;
      try (eapply substitute_eq_binds_v'; eauto); solve_before_d27.
      simpl in H0. lia.
      eexists.
      eexists.
      exists [].
      exists acts.
      eexists.
      intuition.
      3 : { eauto. }
      eapply composed_lts.Step_None; eauto.
      eauto. simpl.
      eapply substitute_eq_binds_v'; eauto.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      inversion H5; subst; simpl in *;
      eapply IHvalid_execution_fragment in H2; eauto;
      try apply substitute_neq_preserves_binds; auto;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2, acts1, acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto;
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto.
  - inversion H.
  - inversion H.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      apply binds_in in H1.
      inversion H5; subst; simpl in *;
      unfold "#" in Hnotin_pc;
      intuition.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2; eauto.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
      exists s1, s2.
      eexists.
      exists acts2.
      eexists.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
      2 : { eauto. }
      eapply composed_lts.Step_Initial_Call; eauto.
      eapply composed_lts.Step_None; eauto.
      eauto.
      eauto.
      rewrite H6. simpl; auto.
      inversion H5; subst; simpl in *;
      apply binds_push_neq; auto.
      apply Nat.eqb_neq in n; rewrite n in H3; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      inversion H5; subst; simpl in *;
      rewrite Hbinds0 in H1;
      unfold before_d13 in Hv; intuition; subst; try discriminate;
      try (destruct H6; subst; discriminate);
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate).
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2; eauto.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
      exists s1, s2.
      eexists.
      exists acts2.
      eexists.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
      2 : { eauto. }
      eapply composed_lts.Step_Final_Return; eauto.
      eapply composed_lts.Step_None; eauto.
      eauto.
      eauto.
      rewrite H6. simpl; auto.
      inversion H5; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H3; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      rewrite Nat.eqb_refl in H3.
      simpl in H3.
      inversion H6; subst; simpl in *.
      all : rewrite Hbinds0 in H1;
      unfold before_d13 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      simpl in H3;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_d13;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition;
      try (eapply composed_lts.valid_execution_fragment_join'; eauto;
      eapply composed_lts.Step_Internal_Query; eauto;
      eapply composed_lts.Step_None; eauto);
      try (rewrite H7; simpl; auto).
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto.
      3 : { eauto. }
      eapply composed_lts.Step_Internal_Query; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite H7. simpl; auto.
      inversion H6; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H3; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      rewrite Nat.eqb_refl in H3.
      simpl in H3.
      inversion H6; subst; simpl in *;
      rewrite Hbinds0 in H1;
      unfold before_d13 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      simpl in H3;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_d13;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition;
      try (eapply composed_lts.valid_execution_fragment_join'; eauto;
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto);
      rewrite H7; simpl; auto.
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto.
      3 : { eauto. }
      eapply composed_lts.Step_Internal_Reply; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite H7; simpl; auto.
      inversion H6; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H3; auto.
Qed.

Definition after_d3 v :=
  v = ADeq4 \/
  v = ADeq5 \/
  (exists ret, v = ADeq6 ret) \/
  after_d6 v.

Lemma after_d3_Deq4:
  after_d3 (ADeq4).
Proof.
  intros.
  unfold after_d3.
  intuition.
Qed.

Lemma after_d3_Deq5:
  after_d3 (ADeq5).
Proof.
  intros.
  unfold after_d3.
  intuition.
Qed.

Lemma after_d3_Deq6: forall ret,
  after_d3 (ADeq6 ret).
Proof.
  intros.
  unfold after_d3.
  right. right. left.
  exists ret.
  reflexivity.
Qed.

Ltac solve_after_d6 :=
  try apply after_d6_Deq10;
  try apply after_d6_Deq11;
  try apply after_d6_Deq12;
  try apply after_d6_Deq13;
  try apply after_d6_Deq14;
  try apply after_d6_Deq15;
  try apply after_d6_Deq26;
  try apply after_d6_Deq27.

Ltac solve_after_d3 :=
  try apply after_d3_Deq4;
  try apply after_d3_Deq5;
  try apply after_d3_Deq6;
  try (unfold after_d6;
  right; right; right;
  solve_after_d6).

Definition calculate_before13 v :=
  match v with
  | ADeq1 => 6
  | ADeq2 => 5
  | ADeq3 r => 4
  | ADeq4 => 4
  | ADeq5 => 3
  | ADeq6 r => 2
  | ADeq10 => 2
  | ADeq11 => 1
  | ADeq12 r => 0
  | _ => 0
  end.

Lemma inv_before_d12_least_B_events: forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  forall v,
  before_d13 v ->
  binds pid v (get_pc s) ->
  binds pid (ADeq12 ret) (get_pc s') ->
  length (gather_pid_events_B pid acts) >= calculate_before13 v.
Proof.
  induction 1; intros.
  - subst. unfold before_d13 in H0.
    unfold binds in H2.
    intuition; subst; try (rewrite H1 in H2; discriminate).
    unfold before_d13 in H.
    intuition; subst; try (rewrite H1 in H2; discriminate).
    (* destruct H as [r Hr]; subst.
    rewrite H1 in H2; discriminate. *)
    all : try (destruct H0 as [r Hr]; subst;
    rewrite H1 in H2; discriminate).
    all : try (destruct H as [r Hr]; subst;
    rewrite H1 in H2; discriminate).
    destruct H0 as [r Hr]; subst.
    simpl. lia.
  - inversion H; subst; simpl in *.
    unfold get_pc in *; simpl in *.
    eapply IHvalid_execution_fragment; eauto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H2.
      inversion H5; subst; simpl in *.
      all : try (rewrite Hbinds0 in H2;
      inversion H2; subst; simpl in *;
      eapply IHvalid_execution_fragment in H3;
      try (eapply substitute_eq_binds_v'; eauto); solve_before_d13;
      simpl in H3; lia).
      all : try (rewrite Hbinds0 in H2;
      inversion H2; subst; simpl in *; lia).
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      (* unfold binds in H2. *)
      inversion H5; subst; simpl in *;
      eapply IHvalid_execution_fragment; eauto;
      apply substitute_neq_preserves_binds; auto.
  - inversion H.
  - inversion H.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      apply binds_in in H2.
      inversion H5; subst; simpl in *;
      unfold "#" in Hnotin_pc; intuition.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H5; subst; simpl in *;
      apply binds_push_neq; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      rewrite Nat.eqb_refl.
      unfold binds in H2.
      inversion H5; subst; simpl in *; simpl;
      rewrite Hbinds0 in H2;
      inversion H2; subst; simpl; lia.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H5; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      rewrite Nat.eqb_refl.
      unfold binds in H2.
      simpl.
      inversion H6; subst; simpl in *.
      all : try (rewrite Hbinds0 in H2;
      inversion H2; subst;
      eapply IHvalid_execution_fragment in H3;
      try (eapply substitute_eq_binds_v'; eauto); solve_before_d13;
      simpl in H3; simpl; lia).
      all : rewrite Hbinds0 in H2;
      inversion H2; subst; simpl; lia.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H6; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      rewrite Nat.eqb_refl.
      unfold binds in H2.
      simpl.
      inversion H6; subst; simpl in *.
      all : try (rewrite Hbinds0 in H2;
      inversion H2; subst;
      eapply IHvalid_execution_fragment in H3;
      try (eapply substitute_eq_binds_v'; eauto); solve_before_d13;
      simpl in H3; simpl; lia).
      all : rewrite Hbinds0 in H2;
      inversion H2; subst; simpl; lia.
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H6; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
Qed.

Lemma inv_d1_stuttering : forall s s' acts pid,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  binds pid (ADeq1) (get_pc s) ->
  length (gather_pid_events_B pid acts) = 0 ->
  binds pid (ADeq1) (get_pc s').
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
    -- unfold get_pc in *; simpl in *.
      inversion H; subst; simpl in *.
      inversion H3; subst; simpl in *.
      inversion H4; subst; simpl in *;
      eapply IHvalid_execution_fragment; eauto;
      eapply substitute_neq_preserves_binds; eauto.
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

Lemma inv_d12_stuttering : forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  binds pid (ADeq12 ret) (get_pc s) ->
  length (gather_pid_events_B pid acts) = 0 ->
  binds pid (ADeq12 ret) (get_pc s') \/
  binds pid ADeq13 (get_pc s') \/
  binds pid ADeq1 (get_pc s').
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
      eapply inv_d1_stuttering in H0; eauto.
      unfold get_pc; simpl; auto.
      eapply substitute_eq_binds_v'; eauto.
      eapply inv_d13_stuttering in H0; eauto.
      unfold get_pc; simpl.
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

Lemma inv_d11_ret_d12_ret: forall s s' pid acts,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  binds pid (ADeq11) (get_pc s) ->
  forall ret ret0,
  binds pid (CntReadOk ret) (get_rear s).(Counter.responses) ->
  binds pid (ADeq12 ret0) (get_pc s') ->
  (length (gather_pid_events_B pid acts)) = 1 ->
  ret = ret0.
Proof.
  induction 1; intros.
  - subst. simpl in H3. discriminate.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold get_rear in *; simpl in *.
      intuition.
      eapply H7; eauto.
      inversion H6; subst; simpl in *; auto.
      inversion H8; subst; simpl in *.
      inversion H9; subst; simpl in *; auto.
      inversion H10; subst; simpl in *; auto.
      inversion H11; subst; simpl in *; auto;
      apply binds_in in H2;
      unfold "#" in Hnotin_res; intuition.
    --
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold get_rear in *; simpl in *.
      intuition.
      eapply H7; eauto.
      inversion H6; subst; simpl in *; auto.
      inversion H8; subst; simpl in *; auto.
      inversion H9; subst; simpl in *; auto.
      inversion H10; subst; simpl in *; auto.
      inversion H11; subst; simpl in *; auto;
      apply binds_push_neq; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      unfold binds in H1.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold get_ary in *; simpl in *.
      inversion H6; subst; simpl in *;
      try (rewrite Hbinds0 in H1; discriminate).
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold get_ary in *; simpl in *.
      inversion H6; subst; simpl in *;
      eapply IHvalid_execution_fragment; eauto;
      apply substitute_neq_preserves_binds; auto.
  - inversion H.
  - inversion H.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      unfold binds in H1.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold get_ary in *; simpl in *.
      apply binds_in in H1.
      inversion H6; subst; simpl in *;
      unfold "#" in Hnotin_pc; intuition.
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold get_ary in *; simpl in *.
      inversion H6; subst; simpl in *;
      eapply IHvalid_execution_fragment; eauto.
      apply binds_push_neq; auto.
      apply Nat.eqb_neq in n; rewrite n in H4; auto.
      apply binds_push_neq; auto.
      apply Nat.eqb_neq in n; rewrite n in H4; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      unfold binds in H1.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold get_ary in *; simpl in *.
      unfold binds in H1.
      inversion H6; subst; simpl in *;
      rewrite Hbinds0 in H1; discriminate.
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold get_ary in *; simpl in *.
      inversion H6; subst; simpl in *;
      eapply IHvalid_execution_fragment; eauto.
      apply remove_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H4; auto.
      apply remove_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H4; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      unfold binds in H1.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold get_ary in *; simpl in *.
      unfold binds in H1.
      inversion H7; subst; simpl in *;
      rewrite Hbinds0 in H1; discriminate.
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold get_rear in *; simpl in *.
      inversion H7; subst; simpl in *.
      all : eapply IHvalid_execution_fragment; eauto;
      [apply substitute_neq_preserves_binds; auto|
      inversion H6; subst; simpl in *;
      inversion H8; subst; simpl in *; auto|
      apply Nat.eqb_neq in n; rewrite n in H4; auto].
      all : inversion H10; subst; simpl in *; auto;
      inversion H9; subst; simpl in *; auto.
      all : inversion H12; subst; simpl in *; auto;
      inversion H11; subst; simpl in *; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      unfold binds in H1.
      inversion H; subst; simpl in *.
      inversion H6; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold get_rear in *; simpl in *.
      unfold binds in H1.
      inversion H7; subst; simpl in *;
      rewrite Hbinds0 in H1; try discriminate.
    -- inversion H; subst; simpl in *.
      inversion H6; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold get_rear in *; simpl in *.
      inversion H7; subst; simpl in *.
      all : eapply IHvalid_execution_fragment; eauto;
      [apply substitute_neq_preserves_binds; auto|
      inversion H5; subst; simpl in *;
      inversion H8; subst; simpl in *; auto|
      apply Nat.eqb_neq in n; rewrite n in H4; auto].
      all : inversion H10; subst; simpl in *; auto;
      inversion H9; subst; simpl in *;
      inversion H12; subst; simpl in *;
      inversion H11; subst; simpl in *.
      all : try (apply remove_neq_preserves_binds; auto); auto.
Qed.

Lemma inv_d13_d12: forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  binds pid (ADeq13) (get_pc s) ->
  binds pid (ADeq12 ret) (get_pc s') ->
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

Lemma inv_impl_front_keep: forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s' acts ->
  forall v 
  (Hv: before_d13 v)
  (Hv' : after_d3 v),
  binds pid v (get_pc s) ->
  length (gather_pid_events_B pid acts) = calculate_before13 v ->
  binds pid (ADeq12 ret) (get_pc s') ->
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

      all : rewrite Hbinds0 in H1;
      inversion H1; subst;
      unfold before_d13 in Hv;
      intuition; subst; try discriminate;
      try (destruct H6; subst; discriminate);
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate).

      unfold after_d3 in Hv'.
      unfold after_d6 in Hv'.
      intuition; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate).

      erewrite IHvalid_execution_fragment;
      try (eapply substitute_eq_binds_v'; eauto); auto;
      [solve_before_d13|solve_after_d3].
      eapply inv_before_d12_least_B_events with (pid:=pid0) (v:=ADeq1) in H0;
      try (eapply substitute_eq_binds_v'; eauto);
      eauto;
      unfold get_pc; simpl; solve_before_d13;
      simpl in H0;
      rewrite H2 in H0; simpl in H0; lia.
      inversion H7; subst; simpl in H2.
      inversion H6; subst; simpl in *.
      eapply inv_d13_d12 in H0; eauto;
      try (rewrite H2 in H0; lia);
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
      unfold before_d13 in Hv;
      intuition; subst; try discriminate;
      try (destruct H6; subst; discriminate);
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate).
      unfold after_d3 in Hv'.
      unfold after_d6 in Hv'.
      intuition; subst; try discriminate;
      try (destruct H8; subst; discriminate).
      try (destruct H9; subst; discriminate).
      all : erewrite IHvalid_execution_fragment;
      try (eapply substitute_eq_binds_v'; eauto);
      auto; [solve_before_d13|solve_after_d3].
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
      auto; [solve_before_d13|solve_after_d3].
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

Lemma inv_impl_pc_keep: forall s s' acts pid ret ret0,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s' acts ->
  binds pid (ADeq12 ret) (get_pc s) ->
  length (gather_pid_events_B pid acts) = 0 ->
  binds pid (ADeq12 ret0) (get_pc s') ->
  ret = ret0.
Proof.
  induction 1; intros.
  - subst.
    unfold binds in H0.
    rewrite H2 in H0.
    inversion H0; subst; auto.
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
      inversion H5; subst; simpl in *;
      try (rewrite Hbinds0 in H1; discriminate).
      eapply inv_before_d12_least_B_events with (pid:=pid0) (v:=ADeq1) in H0;
      unfold get_pc in *; simpl in *;
      solve_before_d13; eauto;
      try (eapply substitute_eq_binds_v'; eauto);
      rewrite H2 in H0; lia.
      eapply inv_d13_d12 in H0; eauto;
      try (rewrite H2 in H0; lia);
      unfold get_pc; simpl;
      eapply substitute_eq_binds_v'; eauto.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_impl, get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
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
        inversion H5; subst; simpl in *;
        apply binds_push_neq; auto.
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
      unfold before_e13 in Hv;
      intuition; subst; try discriminate;
      try (destruct H6; subst; discriminate);
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate).
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_impl, get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
        inversion H5; subst; simpl in *;
        apply remove_neq_preserves_binds; auto.
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
      unfold before_e13 in Hv;
      intuition; subst; try discriminate;
      try (destruct H6; subst; discriminate);
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate).
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_impl, get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
        inversion H6; subst; simpl in *;
        apply substitute_neq_preserves_binds; auto.
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
      unfold before_e13 in Hv;
      intuition; subst; try discriminate;
      try (destruct H6; subst; discriminate);
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate).
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_impl, get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
        inversion H6; subst; simpl in *;
        apply substitute_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H2;
      rewrite H2; auto.
Qed.

Lemma inv_before_d13_least_B_events: forall s s' acts pid,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  forall v,
  before_d13 v ->
  binds pid v (get_pc s) ->
  binds pid (ADeq13) (get_pc s') ->
  length (gather_pid_events_B pid acts) >= calculate_before13 v.
Proof.
  induction 1; intros.
  - subst. unfold before_d13 in H0.
    unfold binds in H2.
    intuition; subst; try (rewrite H1 in H2; discriminate).
    unfold before_d13 in H.
    intuition; subst; try (rewrite H1 in H2; discriminate).
    (* destruct H as [r Hr]; subst.
    rewrite H1 in H2; discriminate. *)
    all : try (destruct H0 as [r Hr]; subst;
    rewrite H1 in H2; discriminate).
    all : try (destruct H as [r Hr]; subst;
    rewrite H1 in H2; discriminate).
  - inversion H; subst; simpl in *.
    unfold get_pc in *; simpl in *.
    eapply IHvalid_execution_fragment; eauto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H2.
      inversion H5; subst; simpl in *.
      all : try (rewrite Hbinds0 in H2;
      inversion H2; subst; simpl in *;
      eapply IHvalid_execution_fragment in H3;
      try (eapply substitute_eq_binds_v'; eauto); solve_before_d13;
      simpl in H3; lia).
      all : try (rewrite Hbinds0 in H2;
      inversion H2; subst; simpl in *; lia).
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      (* unfold binds in H2. *)
      inversion H5; subst; simpl in *;
      eapply IHvalid_execution_fragment; eauto;
      apply substitute_neq_preserves_binds; auto.
  - inversion H.
  - inversion H.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      apply binds_in in H2.
      inversion H5; subst; simpl in *;
      unfold "#" in Hnotin_pc; intuition.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H5; subst; simpl in *;
      apply binds_push_neq; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      rewrite Nat.eqb_refl.
      unfold binds in H2.
      inversion H5; subst; simpl in *; simpl;
      rewrite Hbinds0 in H2;
      inversion H2; subst; simpl; lia.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H5; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      rewrite Nat.eqb_refl.
      unfold binds in H2.
      simpl.
      inversion H6; subst; simpl in *.
      all : try (rewrite Hbinds0 in H2;
      inversion H2; subst;
      eapply IHvalid_execution_fragment in H3;
      try (eapply substitute_eq_binds_v'; eauto); solve_before_d13;
      simpl in H3; simpl; lia).
      all : rewrite Hbinds0 in H2;
      inversion H2; subst; simpl; lia.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H6; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      rewrite Nat.eqb_refl.
      unfold binds in H2.
      simpl.
      inversion H6; subst; simpl in *.
      all : try (rewrite Hbinds0 in H2;
      inversion H2; subst;
      eapply IHvalid_execution_fragment in H3;
      try (eapply substitute_eq_binds_v'; eauto); solve_before_d13;
      simpl in H3; simpl; lia).
      all : rewrite Hbinds0 in H2;
      inversion H2; subst; simpl; lia.
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H6; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
Qed.

Definition before_d12 v :=
  v = ADeq1 \/
  v = ADeq2 \/
  (exists r, v = ADeq3 r) \/
  v = ADeq4 \/
  v = ADeq5 \/
  (exists r, v = ADeq6 r) \/
  v = ADeq10 \/
  v = ADeq11.

Lemma before_d12_Deq1:
  before_d12 (ADeq1).
Proof.
  intros.
  unfold before_d12.
  intuition.
Qed.

Lemma before_d12_Deq2:
  before_d12 (ADeq2).
Proof.
  intros.
  unfold before_d12.
  intuition.
Qed.

Lemma before_d12_Deq3: forall ret,
  before_d12 (ADeq3 ret).
Proof.
  intros.
  unfold before_d12.
  right. right. left.
  exists ret.
  reflexivity.
Qed.

Lemma before_d12_Deq4:
  before_d12 (ADeq4).
Proof.
  intros.
  unfold before_d12.
  intuition.
Qed.

Lemma before_d12_Deq5:
  before_d12 (ADeq5).
Proof.
  intros.
  unfold before_d12.
  intuition.
Qed.

Lemma before_d12_Deq6: forall ret,
  before_d12 (ADeq6 ret).
Proof.
  intros.
  unfold before_d12.
  right. right. right. right. right. left.
  exists ret.
  reflexivity.
Qed.

Lemma before_d12_Deq10:
  before_d12 (ADeq10).
Proof.
  intros.
  unfold before_d12.
  intuition.
Qed.

Lemma before_d12_Deq11:
  before_d12 (ADeq11).
Proof.
  intros.
  unfold before_d12.
  intuition.
Qed.

Ltac solve_before_d12 :=
  try apply before_d12_Deq1;
  try apply before_d12_Deq2;
  try apply before_d12_Deq3;
  try apply before_d12_Deq4;
  try apply before_d12_Deq5;
  try apply before_d12_Deq6;
  try apply before_d12_Deq10;
  try apply before_d12_Deq11.

Lemma inv_before_d12_go_through_11: forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  forall v (Hv : before_d12 v),
  binds pid v (get_pc s) ->
  binds pid (ADeq12 ret) (get_pc s') ->
  length (gather_pid_events_B pid acts) = calculate_before13 v ->
  exists s1 s2 acts1 acts2 it,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 /\
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s2 s' acts2 /\
  composed_lts.internal_reply (composed_array_queue L)
  s1 pid it s2 /\
  binds pid (ADeq12 ret) (get_pc s2).
Proof.
  induction 1; intros.
  - subst. simpl in H2.
    unfold before_d12 in Hv.
    intuition; subst; simpl in H2; try discriminate.
    destruct H; subst; discriminate.
    destruct H3; subst; discriminate.
  - inversion H; subst; simpl in *.
    unfold get_pc in *; simpl in *.
    eapply IHvalid_execution_fragment in H1; eauto.
    destruct H1 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
    exists s1, s2, acts1, acts2, it. intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L1; eauto.
    eapply composed_lts.Step_None; eauto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      inversion H5; subst; simpl in *;
      rewrite Hbinds0 in H1; try discriminate.
      all : try (
        unfold before_d12 in Hv;
        intuition; subst; try discriminate;
      try (destruct H6 as [t Ht]; subst);
      try (destruct H7 as [t Ht]; subst);
      try (destruct H8 as [t Ht]; subst);
      inversion H1; subst;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_d12;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2, acts1, acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto;
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto).
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      inversion H5; subst; simpl in *;
      eapply IHvalid_execution_fragment in H2; eauto;
      try apply substitute_neq_preserves_binds; auto;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2, acts1, acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto;
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto.
  - inversion H.
  - inversion H.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      apply binds_in in H1.
      inversion H5; subst; simpl in *;
      unfold "#" in Hnotin_pc;
      intuition.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2; eauto.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
      exists s1, s2.
      eexists.
      exists acts2.
      eexists.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
      2 : { eauto. }
      eapply composed_lts.Step_Initial_Call; eauto.
      eapply composed_lts.Step_None; eauto.
      eauto.
      eauto.
      inversion H5; subst; simpl in *;
      apply binds_push_neq; auto.
      apply Nat.eqb_neq in n; rewrite n in H3; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      inversion H5; subst; simpl in *;
      rewrite Hbinds0 in H1;
      unfold before_d12 in Hv; intuition; subst; try discriminate;
      try (destruct H6; subst; discriminate);
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate).
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2; eauto.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
      exists s1, s2.
      eexists.
      exists acts2.
      eexists.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
      2 : { eauto. }
      eapply composed_lts.Step_Final_Return; eauto.
      eapply composed_lts.Step_None; eauto.
      eauto.
      eauto.
      inversion H5; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H3; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      rewrite Nat.eqb_refl in H3.
      simpl in H3.
      inversion H6; subst; simpl in *.
      all : rewrite Hbinds0 in H1;
      unfold before_d12 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      simpl in H3;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_d12;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join'; eauto;
      eapply composed_lts.Step_Internal_Query; eauto;
      eapply composed_lts.Step_None; eauto.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto.
      2 : { eauto. }
      eapply composed_lts.Step_Internal_Query; eauto.
      eapply composed_lts.Step_None; eauto.
      inversion H6; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H3; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      rewrite Nat.eqb_refl in H3.
      simpl in H3.
      inversion H6; subst; simpl in *.
      all : try (rewrite Hbinds0 in H1;
      unfold before_d12 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      simpl in H3;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_d12;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join'; eauto;
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto).
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto.
      2 : { eauto. }
      eapply composed_lts.Step_Internal_Reply; eauto.
      eapply composed_lts.Step_None; eauto.
      inversion H6; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H3; auto.
Qed.

Lemma inv_before_d12_go_through_11': forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  forall v (Hv : before_d12 v),
  binds pid v (get_pc s) ->
  binds pid (ADeq12 ret) (get_pc s') ->
  length (gather_pid_events_B pid acts) = calculate_before13 v ->
  exists s1 s2 acts1 acts2 it,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 /\
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s2 s' acts2 /\
  composed_lts.internal_reply (composed_array_queue L)
  s1 pid it s2 /\
  binds pid (ADeq12 ret) (get_pc s2) /\
  acts = acts1 ++ [(pid, composed_lts.event_resB it)] ++ acts2.
Proof.
  induction 1; intros.
  - subst. simpl in H2.
    unfold before_d12 in Hv.
    intuition; subst; simpl in H2; try discriminate.
    destruct H; subst; discriminate.
    destruct H3; subst; discriminate.
  - inversion H; subst; simpl in *.
    unfold get_pc in *; simpl in *.
    eapply IHvalid_execution_fragment in H1; eauto.
    destruct H1 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
    exists s1, s2, acts1, acts2, it. intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L1; eauto.
    eapply composed_lts.Step_None; eauto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      inversion H5; subst; simpl in *;
      rewrite Hbinds0 in H1; try discriminate.
      all : try (
        unfold before_d12 in Hv;
        intuition; subst; try discriminate;
      try (destruct H6 as [t Ht]; subst);
      try (destruct H7 as [t Ht]; subst);
      try (destruct H8 as [t Ht]; subst);
      inversion H1; subst;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_d12;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2, acts1, acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto;
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto).
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      inversion H5; subst; simpl in *;
      eapply IHvalid_execution_fragment in H2; eauto;
      try apply substitute_neq_preserves_binds; auto;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2, acts1, acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto;
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto.
  - inversion H.
  - inversion H.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      apply binds_in in H1.
      inversion H5; subst; simpl in *;
      unfold "#" in Hnotin_pc;
      intuition.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2; eauto.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
      exists s1, s2.
      eexists.
      exists acts2.
      eexists.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
      2 : { eauto. }
      eapply composed_lts.Step_Initial_Call; eauto.
      eapply composed_lts.Step_None; eauto.
      eauto.
      eauto.
      rewrite H6; simpl; auto.
      inversion H5; subst; simpl in *;
      apply binds_push_neq; auto.
      apply Nat.eqb_neq in n; rewrite n in H3; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      inversion H5; subst; simpl in *;
      rewrite Hbinds0 in H1;
      unfold before_d12 in Hv; intuition; subst; try discriminate;
      try (destruct H6; subst; discriminate);
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate).
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2; eauto.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
      exists s1, s2.
      eexists.
      exists acts2.
      eexists.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
      2 : { eauto. }
      eapply composed_lts.Step_Final_Return; eauto.
      eapply composed_lts.Step_None; eauto.
      eauto.
      eauto.
      rewrite H6; simpl; auto.
      inversion H5; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H3; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      rewrite Nat.eqb_refl in H3.
      simpl in H3.
      inversion H6; subst; simpl in *.
      all : rewrite Hbinds0 in H1;
      unfold before_d12 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      simpl in H3;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_d12;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition;
      try (eapply composed_lts.valid_execution_fragment_join'; eauto;
      eapply composed_lts.Step_Internal_Query; eauto;
      eapply composed_lts.Step_None; eauto);
      rewrite H7; simpl; auto.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto.
      3 : { eauto. }
      eapply composed_lts.Step_Internal_Query; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite H7; simpl; auto.
      inversion H6; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H3; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      rewrite Nat.eqb_refl in H3.
      simpl in H3.
      inversion H6; subst; simpl in *.
      all : try (rewrite Hbinds0 in H1;
      unfold before_d12 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      simpl in H3;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_d12;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep [Hb Heq]]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition;
      try (eapply composed_lts.valid_execution_fragment_join'; eauto;
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto);
      rewrite Heq; simpl; auto).
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto.
      3 : { eauto. }
      eapply composed_lts.Step_Internal_Reply; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite H7; simpl; auto.
      inversion H6; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H3; auto.
Qed.

Definition before_d11 v :=
  v = ADeq1 \/
  v = ADeq2 \/
  (exists r, v = ADeq3 r) \/
  v = ADeq4 \/
  v = ADeq5 \/
  (exists r, v = ADeq6 r) \/
  v = ADeq10.

Lemma before_d11_Deq1:
  before_d11 (ADeq1).
Proof.
  intros.
  unfold before_d11.
  intuition.
Qed.

Lemma before_d11_Deq2:
  before_d11 (ADeq2).
Proof.
  intros.
  unfold before_d11.
  intuition.
Qed.

Lemma before_d11_Deq3: forall ret,
  before_d11 (ADeq3 ret).
Proof.
  intros.
  unfold before_d11.
  right. right. left.
  exists ret.
  reflexivity.
Qed.

Lemma before_d11_Deq4:
  before_d11 (ADeq4).
Proof.
  intros.
  unfold before_d11.
  intuition.
Qed.

Lemma before_d11_Deq5:
  before_d11 (ADeq5).
Proof.
  intros.
  unfold before_d11.
  intuition.
Qed.

Lemma before_d11_Deq6: forall ret,
  before_d11 (ADeq6 ret).
Proof.
  intros.
  unfold before_d11.
  right. right. right. right. right. left.
  exists ret.
  reflexivity.
Qed.

Lemma before_d11_Deq10:
  before_d11 (ADeq10).
Proof.
  intros.
  unfold before_d11.
  intuition.
Qed.

Ltac solve_before_d11 :=
  try apply before_d11_Deq1;
  try apply before_d11_Deq2;
  try apply before_d11_Deq3;
  try apply before_d11_Deq4;
  try apply before_d11_Deq5;
  try apply before_d11_Deq6;
  try apply before_d11_Deq10.

Lemma inv_d11_internal_step: forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  binds pid (ADeq11) (get_pc s) ->
  binds pid (CntRead) (get_front s).(Counter.requests) ->
  pid # (get_front s).(Counter.responses) ->
  binds pid (ADeq11) (get_pc s') ->
  binds pid (CntReadOk ret) (get_front s').(Counter.responses) ->
  length (gather_pid_events_B pid acts) = 0 ->
  exists s1 s2 acts1 acts2 it,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 /\
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s2 s' acts2 /\
  composed_lts.step_L1 (composed_array_queue L)
  s1 pid it s2 /\
  binds pid (ADeq11) (get_pc s2).
Proof.
  induction 1; intros.
  - subst.
    apply binds_in in H4.
    unfold "#" in H2; intuition.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      exists st, st'', [], acts, int.
        intuition.
        eapply composed_lts.Step_None; eauto.
      inversion H; subst; simpl in *; auto.
    -- inversion H; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H1; eauto.
      destruct H1 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
      exists s1, s2, acts1, acts2, it. intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
      eapply composed_lts.Step_Internal_L1; eauto.
      eapply composed_lts.Step_None; eauto.
      inversion H7; subst; simpl in *.
      unfold get_rear in *; simpl in *.
      inversion H8; subst; simpl in *; auto.
      inversion H9; subst; simpl in *.
      inversion H10; subst; simpl in *; auto.
      inversion H11; subst; simpl in *; auto.
      inversion H12; subst; simpl in *; 
      apply remove_neq_preserves_binds; auto.
      inversion H7; subst; simpl in *.
      unfold get_rear in *; simpl in *.
      inversion H8; subst; simpl in *; auto.
      inversion H9; subst; simpl in *.
      inversion H10; subst; simpl in *; auto.
      inversion H11; subst; simpl in *; auto.
      inversion H12; subst; simpl in *;
      apply notin_union; auto;
      intuition; apply notin_neq; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H7; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      inversion H8; subst; simpl in *;
      rewrite Hbinds0 in H1; try discriminate.
    -- inversion H; subst; simpl in *.
      inversion H7; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      inversion H8; subst; simpl in *;
      eapply IHvalid_execution_fragment in H2; eauto;
      try apply substitute_neq_preserves_binds; auto;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2, acts1, acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto;
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto.
  - inversion H.
  - inversion H.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H7; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      apply binds_in in H1.
      inversion H8; subst; simpl in *;
      unfold "#" in Hnotin_pc;
      intuition.
    -- inversion H; subst; simpl in *.
      inversion H7; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2; eauto.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
      exists s1, s2.
      eexists.
      exists acts2.
      eexists.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
      2 : { eauto. }
      eapply composed_lts.Step_Initial_Call; eauto.
      eapply composed_lts.Step_None; eauto.
      eauto.
      eauto.
      inversion H8; subst; simpl in *;
      apply binds_push_neq; auto.
      apply Nat.eqb_neq in n; rewrite n in H6; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H7; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      inversion H8; subst; simpl in *;
      rewrite Hbinds0 in H1; discriminate.
    -- inversion H; subst; simpl in *.
      inversion H7; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2; eauto.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
      exists s1, s2.
      eexists.
      exists acts2.
      eexists.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
      2 : { eauto. }
      eapply composed_lts.Step_Final_Return; eauto.
      eapply composed_lts.Step_None; eauto.
      eauto.
      eauto.
      inversion H8; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H6; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H7; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      rewrite Nat.eqb_refl in H6.
      simpl in H6.
      inversion H9; subst; simpl in *.
      all : rewrite Hbinds0 in H1; discriminate.
    -- inversion H; subst; simpl in *.
      inversion H7; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H4.
      destruct H4 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto.
      eapply composed_lts.Step_Internal_Query; eauto.
      eapply composed_lts.Step_None; eauto.
      inversion H9; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
      unfold get_rear in *; simpl in *; auto;
      inversion H8; subst; simpl in *;
      inversion H10; subst; simpl in *; auto;
      inversion H11; subst; simpl in *;
      inversion H12; subst; simpl in *; auto;
      inversion H13; subst; simpl in *;
      inversion H14; subst; simpl in *;
      apply binds_push_neq; auto.
      unfold get_rear in *; simpl in *; auto;
      inversion H8; subst; simpl in *;
      inversion H10; subst; simpl in *; auto;
      inversion H11; subst; simpl in *;
      inversion H12; subst; simpl in *; auto;
      inversion H13; subst; simpl in *;
      inversion H14; subst; simpl in *; auto.
      auto.
      auto.
      apply Nat.eqb_neq in n; rewrite n in H6; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H8; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      rewrite Nat.eqb_refl in H6.
      simpl in H6.
      inversion H9; subst; simpl in *.
      all : try (rewrite Hbinds0 in H1; discriminate;
      simpl in H3;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_d12;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join'; eauto;
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto).
    -- inversion H; subst; simpl in *.
      inversion H8; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H4.
      destruct H4 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto.
      eapply composed_lts.Step_Internal_Reply; eauto.
      eapply composed_lts.Step_None; eauto.
      inversion H9; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
      unfold get_rear in *; simpl in *; auto;
      inversion H7; subst; simpl in *;
      inversion H10; subst; simpl in *; auto;
      inversion H11; subst; simpl in *;
      inversion H12; subst; simpl in *; auto;
      inversion H13; subst; simpl in *;
      inversion H14; subst; simpl in *; auto.
      unfold get_rear in *; simpl in *; auto;
      inversion H7; subst; simpl in *;
      inversion H10; subst; simpl in *; auto;
      inversion H11; subst; simpl in *;
      inversion H12; subst; simpl in *; auto;
      inversion H13; subst; simpl in *;
      inversion H14; subst; simpl in *;
      apply remove_preserves_notin; auto.
      auto.
      apply Nat.eqb_neq in n; rewrite n in H6; auto.
Qed.

Lemma inv_d11_internal_step': forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  binds pid (ADeq11) (get_pc s) ->
  binds pid (CntRead) (get_front s).(Counter.requests) ->
  pid # (get_front s).(Counter.responses) ->
  binds pid (ADeq11) (get_pc s') ->
  binds pid (CntReadOk ret) (get_front s').(Counter.responses) ->
  length (gather_pid_events_B pid acts) = 0 ->
  exists s1 s2 acts1 acts2 it,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 /\
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s2 s' acts2 /\
  composed_lts.step_L1 (composed_array_queue L)
  s1 pid it s2 /\
  binds pid (ADeq11) (get_pc s2) /\
  acts = acts1 ++ acts2.
Proof.
  induction 1; intros.
  - subst.
    apply binds_in in H4.
    unfold "#" in H2; intuition.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      exists st, st'', [], acts, int.
        intuition.
        eapply composed_lts.Step_None; eauto.
      inversion H; subst; simpl in *; auto.
    -- inversion H; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H1; eauto.
      destruct H1 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
      exists s1, s2, acts1, acts2, it. intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
      eapply composed_lts.Step_Internal_L1; eauto.
      eapply composed_lts.Step_None; eauto.
      inversion H7; subst; simpl in *.
      unfold get_rear in *; simpl in *.
      inversion H8; subst; simpl in *; auto.
      inversion H9; subst; simpl in *.
      inversion H10; subst; simpl in *; auto.
      inversion H11; subst; simpl in *; auto.
      inversion H12; subst; simpl in *; 
      apply remove_neq_preserves_binds; auto.
      inversion H7; subst; simpl in *.
      unfold get_rear in *; simpl in *.
      inversion H8; subst; simpl in *; auto.
      inversion H9; subst; simpl in *.
      inversion H10; subst; simpl in *; auto.
      inversion H11; subst; simpl in *; auto.
      inversion H12; subst; simpl in *;
      apply notin_union; auto;
      intuition; apply notin_neq; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H7; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      inversion H8; subst; simpl in *;
      rewrite Hbinds0 in H1; try discriminate.
    -- inversion H; subst; simpl in *.
      inversion H7; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      inversion H8; subst; simpl in *;
      eapply IHvalid_execution_fragment in H2; eauto;
      try apply substitute_neq_preserves_binds; auto;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2, acts1, acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto;
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto.
  - inversion H.
  - inversion H.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H7; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      apply binds_in in H1.
      inversion H8; subst; simpl in *;
      unfold "#" in Hnotin_pc;
      intuition.
    -- inversion H; subst; simpl in *.
      inversion H7; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2; eauto.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
      exists s1, s2.
      eexists.
      exists acts2.
      eexists.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
      2 : { eauto. }
      eapply composed_lts.Step_Initial_Call; eauto.
      eapply composed_lts.Step_None; eauto.
      eauto.
      eauto.
      rewrite H9; simpl; auto.
      inversion H8; subst; simpl in *;
      apply binds_push_neq; auto.
      apply Nat.eqb_neq in n; rewrite n in H6; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H7; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      inversion H8; subst; simpl in *;
      rewrite Hbinds0 in H1; discriminate.
    -- inversion H; subst; simpl in *.
      inversion H7; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2; eauto.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
      exists s1, s2.
      eexists.
      exists acts2.
      eexists.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
      2 : { eauto. }
      eapply composed_lts.Step_Final_Return; eauto.
      eapply composed_lts.Step_None; eauto.
      eauto.
      eauto.
      rewrite H9; simpl; auto.
      inversion H8; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H6; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H7; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      rewrite Nat.eqb_refl in H6.
      simpl in H6.
      inversion H9; subst; simpl in *.
      all : rewrite Hbinds0 in H1; discriminate.
    -- inversion H; subst; simpl in *.
      inversion H7; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H4.
      destruct H4 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep [Hb Heq]]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto.
      eapply composed_lts.Step_Internal_Query; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite Heq; simpl; auto.
      inversion H9; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
      unfold get_rear in *; simpl in *; auto;
      inversion H8; subst; simpl in *;
      inversion H10; subst; simpl in *; auto;
      inversion H11; subst; simpl in *;
      inversion H12; subst; simpl in *; auto;
      inversion H13; subst; simpl in *;
      inversion H14; subst; simpl in *;
      apply binds_push_neq; auto.
      unfold get_rear in *; simpl in *; auto;
      inversion H8; subst; simpl in *;
      inversion H10; subst; simpl in *; auto;
      inversion H11; subst; simpl in *;
      inversion H12; subst; simpl in *; auto;
      inversion H13; subst; simpl in *;
      inversion H14; subst; simpl in *; auto.
      auto.
      auto.
      apply Nat.eqb_neq in n; rewrite n in H6; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H8; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      rewrite Nat.eqb_refl in H6.
      simpl in H6.
      inversion H9; subst; simpl in *.
      all : try (rewrite Hbinds0 in H1; discriminate;
      simpl in H3;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_d12;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join'; eauto;
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto).
    -- inversion H; subst; simpl in *.
      inversion H8; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H4.
      destruct H4 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep [Hb Heq]]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto.
      eapply composed_lts.Step_Internal_Reply; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite Heq; simpl; auto.
      inversion H9; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
      unfold get_rear in *; simpl in *; auto;
      inversion H7; subst; simpl in *;
      inversion H10; subst; simpl in *; auto;
      inversion H11; subst; simpl in *;
      inversion H12; subst; simpl in *; auto;
      inversion H13; subst; simpl in *;
      inversion H14; subst; simpl in *; auto.
      unfold get_rear in *; simpl in *; auto;
      inversion H7; subst; simpl in *;
      inversion H10; subst; simpl in *; auto;
      inversion H11; subst; simpl in *;
      inversion H12; subst; simpl in *; auto;
      inversion H13; subst; simpl in *;
      inversion H14; subst; simpl in *;
      apply remove_preserves_notin; auto.
      auto.
      apply Nat.eqb_neq in n; rewrite n in H6; auto.
Qed.

Lemma inv_d10_internal_step: forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  binds pid (ADeq10) (get_pc s) ->
  (* binds pid (CntRead) (get_rear s').(Counter.requests) -> *)
  binds pid (ADeq11) (get_pc s') ->
  (* pid # (get_rear s').(Counter.requests) -> *)
  binds pid (CntReadOk ret) (get_front s').(Counter.responses) ->
  length (gather_pid_events_B pid acts) = 0 ->
  exists s1 s2 acts1 acts2 it,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 /\
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s2 s' acts2 /\
  composed_lts.step_L1 (composed_array_queue L)
  s1 pid it s2 /\
  binds pid (ADeq11) (get_pc s2).
Proof.
  induction 1; intros.
  - subst.
    unfold binds in H1.
    rewrite H0 in H1.
    discriminate.
  - inversion H; subst; simpl in *.
    unfold get_pc in *; simpl in *.
    eapply IHvalid_execution_fragment in H1; eauto.
    destruct H1 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
    exists s1, s2, acts1, acts2, it. intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L1; eauto.
    eapply composed_lts.Step_None; eauto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      inversion H6; subst; simpl in *;
      rewrite Hbinds0 in H1; try discriminate.
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      inversion H6; subst; simpl in *;
      eapply IHvalid_execution_fragment in H2; eauto;
      try apply substitute_neq_preserves_binds; auto;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2, acts1, acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto;
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto.
  - inversion H.
  - inversion H.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      apply binds_in in H1.
      inversion H6; subst; simpl in *;
      unfold "#" in Hnotin_pc;
      intuition.
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2; eauto.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
      exists s1, s2.
      eexists.
      exists acts2.
      eexists.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
      2 : { eauto. }
      eapply composed_lts.Step_Initial_Call; eauto.
      eapply composed_lts.Step_None; eauto.
      eauto.
      eauto.
      inversion H6; subst; simpl in *;
      apply binds_push_neq; auto.
      apply Nat.eqb_neq in n; rewrite n in H4; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      inversion H6; subst; simpl in *;
      rewrite Hbinds0 in H1; discriminate.
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2; eauto.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
      exists s1, s2.
      eexists.
      exists acts2.
      eexists.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
      2 : { eauto. }
      eapply composed_lts.Step_Final_Return; eauto.
      eapply composed_lts.Step_None; eauto.
      eauto.
      eauto.
      inversion H6; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H4; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      rewrite Nat.eqb_refl in H4.
      simpl in H4.
      inversion H7; subst; simpl in *.
      all : rewrite Hbinds0 in H1; discriminate.
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto.
      eapply composed_lts.Step_Internal_Query; eauto.
      eapply composed_lts.Step_None; eauto.
      inversion H7; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H4; auto.
      auto.
      auto.
      apply Nat.eqb_neq in n; rewrite n in H4; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H6; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      rewrite Nat.eqb_refl in H4.
      simpl in H4.
      inversion H7; subst; simpl in *.
      all : try (rewrite Hbinds0 in H1; discriminate;
      simpl in H3;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_d12;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join'; eauto;
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto).
    -- inversion H; subst; simpl in *.
      inversion H6; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto.
      eapply composed_lts.Step_Internal_Reply; eauto.
      eapply composed_lts.Step_None; eauto.
      inversion H7; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
      auto.
      auto.
      auto.
      apply Nat.eqb_neq in n; rewrite n in H4; auto.
Qed.

Definition calculate_before11 v :=
  match v with
  | ADeq1 => 5
  | ADeq2 => 4
  | ADeq3 r => 3
  | ADeq4 => 3
  | ADeq5 => 2
  | ADeq6 r => 1
  | ADeq10 => 1
  | ADeq11 => 0
  | ADeq12 r => 0
  | _ => 0
  end.

Lemma inv_before_d11_go_through_internal: forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  forall v (Hv : before_d11 v),
  binds pid v (get_pc s) ->
  binds pid (ADeq11) (get_pc s') ->
  binds pid (CntReadOk ret) (get_front s').(Counter.responses) ->
  length (gather_pid_events_B pid acts) = calculate_before11 v ->
  exists s1 s2 acts1 acts2 it,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 /\
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s2 s' acts2 /\
  composed_lts.step_L1 (composed_array_queue L)
  s1 pid it s2 /\
  binds pid (ADeq11) (get_pc s2).
Proof.
  induction 1; intros.
  - subst. simpl in H2.
    unfold before_d11 in Hv.
    intuition; subst; simpl in H2; try discriminate.
    destruct H; subst; discriminate.
    destruct H4; subst; discriminate.
  - inversion H; subst; simpl in *.
    unfold get_pc in *; simpl in *.
    eapply IHvalid_execution_fragment in H1; eauto.
    destruct H1 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
    exists s1, s2, acts1, acts2, it. intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L1; eauto.
    eapply composed_lts.Step_None; eauto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      inversion H6; subst; simpl in *;
      rewrite Hbinds0 in H1; try discriminate.
      all : try (
        unfold before_d11 in Hv;
        intuition; subst; try discriminate;
      try (destruct H6 as [t Ht]; subst);
      try (destruct H7 as [t Ht]; subst);
      try (destruct H8 as [t Ht]; subst);
      inversion H1; subst;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_d11;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2, acts1, acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto;
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto).
      all : unfold before_d11 in Hv;
      inversion H1; subst;
      intuition; subst; try discriminate;
      try (destruct H6 as [t Ht]; subst; discriminate);
      try (destruct H7 as [t Ht]; subst; discriminate);
      try (destruct H8 as [t Ht]; subst; discriminate);
      try (destruct H9 as [t Ht]; subst; discriminate).
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      inversion H6; subst; simpl in *;
      eapply IHvalid_execution_fragment in H2; eauto;
      try apply substitute_neq_preserves_binds; auto;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2, acts1, acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto;
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto.
  - inversion H.
  - inversion H.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      apply binds_in in H1.
      inversion H6; subst; simpl in *;
      unfold "#" in Hnotin_pc;
      intuition.
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2; eauto.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
      exists s1, s2.
      eexists.
      exists acts2.
      eexists.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
      2 : { eauto. }
      eapply composed_lts.Step_Initial_Call; eauto.
      eapply composed_lts.Step_None; eauto.
      eauto.
      eauto.
      inversion H6; subst; simpl in *;
      apply binds_push_neq; auto.
      apply Nat.eqb_neq in n; rewrite n in H4; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      inversion H6; subst; simpl in *;
      rewrite Hbinds0 in H1;
      unfold before_d11 in Hv; intuition; subst; try discriminate;
      try (destruct H6; subst; discriminate);
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      try (destruct H9; subst; discriminate).
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2; eauto.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
      exists s1, s2.
      eexists.
      exists acts2.
      eexists.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
      2 : { eauto. }
      eapply composed_lts.Step_Final_Return; eauto.
      eapply composed_lts.Step_None; eauto.
      eauto.
      eauto.
      inversion H6; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H4; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      rewrite Nat.eqb_refl in H4.
      simpl in H4.
      inversion H7; subst; simpl in *.

      all : try (rewrite Hbinds0 in H1;
      unfold before_d11 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      try (destruct H9; subst; discriminate);
      simpl in H4;
      eapply IHvalid_execution_fragment in H3;
      try eapply substitute_eq_binds_v'; eauto; solve_before_d11;
      destruct H3 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join'; eauto;
      eapply composed_lts.Step_Internal_Query; eauto;
      eapply composed_lts.Step_None; eauto).

      eapply inv_d11_internal_step in H0.
      destruct H0 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
      exists s1, s2.
      eexists.
      exists acts2.
      exists it. intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=acts1); eauto.
      eapply composed_lts.Step_Internal_Query; eauto.
      eapply composed_lts.Step_None; eauto.
      eauto.
      eauto.
      unfold get_pc; simpl.
      eapply substitute_eq_binds_v'; eauto.
      unfold get_rear in *; simpl in *.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      inversion H10; subst; simpl in *.
      inversion H9; subst; simpl in *.
      auto.
      inversion H12; subst; simpl in *.
      inversion H11; subst; simpl in *.
      apply binds_push_eq; auto.
      unfold get_rear in *; simpl in *.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      inversion H10; subst; simpl in *.
      inversion H9; subst; simpl in *.
      inversion H12; subst; simpl in *.
      inversion H11; subst; simpl in *.
      auto.
      auto.
      eauto.
      rewrite Hbinds0 in H1.
      inversion H1; subst.
      simpl in H4.
      lia.
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto.
      2 : { eauto. }
      eapply composed_lts.Step_Internal_Query; eauto.
      eapply composed_lts.Step_None; eauto.
      inversion H7; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H4; auto.
      apply Nat.eqb_neq in n; rewrite n in H4; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H6; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      rewrite Nat.eqb_refl in H4.
      simpl in H4.
      inversion H7; subst; simpl in *.
      all : try (rewrite Hbinds0 in H1;
      unfold before_d11 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      try (destruct H9; subst; discriminate);
      simpl in H4;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_d11;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join'; eauto;
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto).
    -- inversion H; subst; simpl in *.
      inversion H6; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto.
      2 : { eauto. }
      eapply composed_lts.Step_Internal_Reply; eauto.
      eapply composed_lts.Step_None; eauto.
      inversion H7; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H4; auto.
      apply Nat.eqb_neq in n; rewrite n in H4; auto.
Qed.

Lemma inv_before11_go_through_internal': forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  forall v (Hv : before_d11 v),
  binds pid v (get_pc s) ->
  binds pid (ADeq11) (get_pc s') ->
  binds pid (CntReadOk ret) (get_front s').(Counter.responses) ->
  length (gather_pid_events_B pid acts) = calculate_before11 v ->
  exists s1 s2 acts1 acts2 it,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 /\
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s2 s' acts2 /\
  composed_lts.step_L1 (composed_array_queue L)
  s1 pid it s2 /\
  binds pid (ADeq11) (get_pc s2) /\
  acts = acts1 ++ acts2.
Proof.
  induction 1; intros.
  - subst. simpl in H2.
    unfold before_d11 in Hv.
    intuition; subst; simpl in H2; try discriminate.
    destruct H; subst; discriminate.
    destruct H4; subst; discriminate.
  - inversion H; subst; simpl in *.
    unfold get_pc in *; simpl in *.
    eapply IHvalid_execution_fragment in H1; eauto.
    destruct H1 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
    exists s1, s2, acts1, acts2, it. intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L1; eauto.
    eapply composed_lts.Step_None; eauto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      inversion H6; subst; simpl in *;
      rewrite Hbinds0 in H1; try discriminate.
      all : try (
        unfold before_d11 in Hv;
        intuition; subst; try discriminate;
      try (destruct H6 as [t Ht]; subst);
      try (destruct H7 as [t Ht]; subst);
      try (destruct H8 as [t Ht]; subst);
      inversion H1; subst;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_d11;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2, acts1, acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto;
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto).
      all : unfold before_d11 in Hv;
      inversion H1; subst;
      intuition; subst; try discriminate;
      try (destruct H6 as [t Ht]; subst; discriminate);
      try (destruct H7 as [t Ht]; subst; discriminate);
      try (destruct H8 as [t Ht]; subst; discriminate);
      try (destruct H9 as [t Ht]; subst; discriminate).
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      inversion H6; subst; simpl in *;
      eapply IHvalid_execution_fragment in H2; eauto;
      try apply substitute_neq_preserves_binds; auto;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2, acts1, acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto;
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto.
  - inversion H.
  - inversion H.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      apply binds_in in H1.
      inversion H6; subst; simpl in *;
      unfold "#" in Hnotin_pc;
      intuition.
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2; eauto.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
      exists s1, s2.
      eexists.
      exists acts2.
      eexists.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
      2 : { eauto. }
      eapply composed_lts.Step_Initial_Call; eauto.
      eapply composed_lts.Step_None; eauto.
      eauto.
      eauto.
      rewrite H7; simpl; auto.
      inversion H6; subst; simpl in *;
      apply binds_push_neq; auto.
      apply Nat.eqb_neq in n; rewrite n in H4; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      inversion H6; subst; simpl in *;
      rewrite Hbinds0 in H1;
      unfold before_d11 in Hv; intuition; subst; try discriminate;
      try (destruct H6; subst; discriminate);
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      try (destruct H9; subst; discriminate).
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2; eauto.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]].
      exists s1, s2.
      eexists.
      exists acts2.
      eexists.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=acts1).
      2 : { eauto. }
      eapply composed_lts.Step_Final_Return; eauto.
      eapply composed_lts.Step_None; eauto.
      eauto.
      eauto.
      rewrite H7; simpl; auto.
      inversion H6; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H4; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      rewrite Nat.eqb_refl in H4.
      simpl in H4.
      inversion H7; subst; simpl in *.

      all : try (rewrite Hbinds0 in H1;
      unfold before_d11 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      try (destruct H9; subst; discriminate);
      simpl in H4;
      eapply IHvalid_execution_fragment in H3;
      try eapply substitute_eq_binds_v'; eauto; solve_before_d11;
      destruct H3 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep [Hb Heq]]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition;
      try (eapply composed_lts.valid_execution_fragment_join'; eauto;
      eapply composed_lts.Step_Internal_Query; eauto;
      eapply composed_lts.Step_None; eauto);
      rewrite Heq; simpl; auto).

      eapply inv_d11_internal_step' in H0.
      destruct H0 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep [Hb Heq]]]]]]]]].
      exists s1, s2.
      eexists.
      exists acts2.
      exists it. intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=acts1); eauto.
      eapply composed_lts.Step_Internal_Query; eauto.
      eapply composed_lts.Step_None; eauto.
      eauto.
      eauto.
      rewrite Heq; simpl; auto.
      unfold get_pc; simpl.
      eapply substitute_eq_binds_v'; eauto.
      unfold get_front in *; simpl in *.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      inversion H10; subst; simpl in *.
      inversion H9; subst; simpl in *.
      inversion H12; subst; simpl in *.
      inversion H11; subst; simpl in *.
      apply binds_push_eq; auto.
      unfold get_front in *; simpl in *.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      inversion H10; subst; simpl in *.
      inversion H9; subst; simpl in *.
      inversion H12; subst; simpl in *.
      inversion H11; subst; simpl in *.
      auto.
      auto.
      eauto.
      rewrite Hbinds0 in H1.
      inversion H1; subst.
      simpl in H4.
      lia.
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep [Hb Heq]]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto.
      3 : { eauto. }
      eapply composed_lts.Step_Internal_Query; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite Heq; simpl; auto.
      inversion H7; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H4; auto.
      apply Nat.eqb_neq in n; rewrite n in H4; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H6; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H1.
      rewrite Nat.eqb_refl in H4.
      simpl in H4.
      inversion H7; subst; simpl in *.
      all : try (rewrite Hbinds0 in H1;
      unfold before_d11 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      try (destruct H9; subst; discriminate);
      simpl in H4;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_d11;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition;
      try (eapply composed_lts.valid_execution_fragment_join'; eauto;
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto);
      rewrite H8; simpl; auto).
    -- inversion H; subst; simpl in *.
      inversion H6; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H2.
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep [Hb Heq]]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto.
      3 : { eauto. }
      eapply composed_lts.Step_Internal_Reply; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite Heq; simpl; auto.
      inversion H7; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
      apply Nat.eqb_neq in n; rewrite n in H4; auto.
      apply Nat.eqb_neq in n; rewrite n in H4; auto.
Qed.

Lemma inv_before_d11_least_B_events: forall s s' acts pid,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  forall v,
  before_d11 v ->
  binds pid v (get_pc s) ->
  binds pid (ADeq11) (get_pc s') ->
  length (gather_pid_events_B pid acts) >= calculate_before11 v.
Proof.
  induction 1; intros.
  - subst. unfold before_d11 in H0.
    unfold binds in H2.
    intuition; subst; try (rewrite H1 in H2; discriminate).
    unfold before_d11 in H.
    intuition; subst; try (rewrite H1 in H2; discriminate).
    (* destruct H as [r Hr]; subst.
    rewrite H1 in H2; discriminate. *)
    all : try (destruct H0 as [r Hr]; subst;
    rewrite H1 in H2; discriminate).
    all : try (destruct H as [r Hr]; subst;
    rewrite H1 in H2; discriminate).
  - inversion H; subst; simpl in *.
    unfold get_pc in *; simpl in *.
    eapply IHvalid_execution_fragment; eauto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold binds in H2.
      inversion H5; subst; simpl in *.
      all : try (rewrite Hbinds0 in H2;
      inversion H2; subst; simpl in *;
      eapply IHvalid_execution_fragment in H3;
      try (eapply substitute_eq_binds_v'; eauto); solve_before_d11;
      simpl in H3; lia).
      all : try (rewrite Hbinds0 in H2;
      inversion H2; subst; simpl in *; lia).
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      (* unfold binds in H2. *)
      inversion H5; subst; simpl in *;
      eapply IHvalid_execution_fragment; eauto;
      apply substitute_neq_preserves_binds; auto.
  - inversion H.
  - inversion H.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      apply binds_in in H2.
      inversion H5; subst; simpl in *;
      unfold "#" in Hnotin_pc; intuition.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H5; subst; simpl in *;
      apply binds_push_neq; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      rewrite Nat.eqb_refl.
      unfold binds in H2.
      inversion H5; subst; simpl in *; simpl;
      rewrite Hbinds0 in H2;
      inversion H2; subst; simpl; lia.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H5; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      rewrite Nat.eqb_refl.
      unfold binds in H2.
      simpl.
      inversion H6; subst; simpl in *.
      all : try (rewrite Hbinds0 in H2;
      inversion H2; subst;
      eapply IHvalid_execution_fragment in H3;
      try (eapply substitute_eq_binds_v'; eauto); solve_before_d11;
      simpl in H3; simpl; lia).
      all : rewrite Hbinds0 in H2;
      inversion H2; subst; simpl; lia.
    -- inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H6; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      rewrite Nat.eqb_refl.
      unfold binds in H2.
      simpl.
      inversion H6; subst; simpl in *.
      all : try (rewrite Hbinds0 in H2;
      inversion H2; subst;
      eapply IHvalid_execution_fragment in H3;
      try (eapply substitute_eq_binds_v'; eauto); solve_before_d11;
      simpl in H3; simpl; lia).
      all : rewrite Hbinds0 in H2;
      inversion H2; subst; simpl; lia.
    -- inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      eapply IHvalid_execution_fragment in H3; eauto.
      apply Nat.eqb_neq in n; rewrite n; auto.
      inversion H6; subst; simpl in *;
      apply substitute_neq_preserves_binds; auto.
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
Arguments get_front {L}.
Arguments get_vec_front {L}.

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

Ltac solve_after_d6 :=
  try apply after_d6_Deq10;
  try apply after_d6_Deq11;
  try apply after_d6_Deq12;
  try apply after_d6_Deq13;
  try apply after_d6_Deq14;
  try apply after_d6_Deq15;
  try apply after_d6_Deq26;
  try apply after_d6_Deq27.

Ltac solve_after_d3 :=
  try apply after_d3_Deq4;
  try apply after_d3_Deq5;
  try apply after_d3_Deq6;
  try (unfold after_d6;
  right; right; right;
  solve_after_d6).

Ltac solve_before_d12 :=
  try apply before_d12_Deq1;
  try apply before_d12_Deq2;
  try apply before_d12_Deq3;
  try apply before_d12_Deq4;
  try apply before_d12_Deq5;
  try apply before_d12_Deq6;
  try apply before_d12_Deq10;
  try apply before_d12_Deq11.

Ltac solve_before_d11 :=
  try apply before_d11_Deq1;
  try apply before_d11_Deq2;
  try apply before_d11_Deq3;
  try apply before_d11_Deq4;
  try apply before_d11_Deq5;
  try apply before_d11_Deq6;
  try apply before_d11_Deq10.

Lemma inv_d11_front_read : forall s pid it s',
  composed_lts.reachable (composed_array_queue L) s ->
  binds pid ADeq11 (get_pc s') ->
  composed_lts.step_L1 (composed_array_queue L) s pid it s' ->
  it = (@Tensor.intL2 li_array li_cnt_cnt (array L) ArrayQueue.front_rear
        (@Tensor.intL1 li_counter li_counter counter counter (int_cnt_read))).
Proof.
  intros.
  apply step_invariant in H0.
  unfold inv in H0.
  inversion H2; subst; simpl in *.
  inversion H3; subst; simpl in *.
  apply H0 in Hbinds0; auto.
  destruct Hbinds0 as [s1 [s2 [q [acts [Hint_query [Hvalid Hgather]]]]]].
  inversion Hint_query; subst; simpl in *.
  inversion H5; subst; simpl in *.
  unfold get_pc in *; simpl in *.
  unfold binds in H1.
  inversion H7; subst; simpl in *.
  Ltac tmp H Hvalid st2 pid acts Hgather H1 :=
  (apply valid_execution_fragment_com' in Hvalid;
  simpl in Hvalid;
  destruct st2;
  eapply valid_execution_fragment_sync in Hvalid; eauto;
  eapply H with (pid:=pid) in Hvalid; eauto;
  try (simpl; eapply substitute_eq_binds_v'; eauto);
  try (
      assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil) by
      (rewrite Hgather; simpl; reflexivity);
      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B;
      assumption);
    rewrite Hvalid in H1; discriminate).
  tmp noB_preserves_AEnq2 Hvalid st2 pid acts Hgather H1.
  tmp noB_preserves_AEnq5 Hvalid st2 pid acts Hgather H1.
  tmp noB_preserves_AEnq11 Hvalid st2 pid acts Hgather H1.
  tmp noB_preserves_AEnq14 Hvalid st2 pid acts Hgather H1.
  tmp noB_preserves_AEnq28 Hvalid st2 pid acts Hgather H1.
  tmp noB_preserves_AEnq31 Hvalid st2 pid acts Hgather H1.
  tmp noB_preserves_ADeq2 Hvalid st2 pid acts Hgather H1.
  tmp noB_preserves_ADeq5 Hvalid st2 pid acts Hgather H1.
  inversion H4; subst; simpl in *.
  (* front_rear *)
  inversion H8; subst; simpl in *.
    inversion H9; subst; simpl in *.

    apply valid_execution_fragment_com in Hvalid;
        simpl in Hvalid.
        inversion H6; subst; simpl in *.
        inversion H11; subst; simpl in *.
        inversion H13; subst; simpl in *.
        inversion H12; subst; simpl in *.
        eapply internal_preserves_notin'' with (pid:=pid) in Hvalid; simpl in *; eauto.
        unfold "#" in Hvalid.
        apply binds_in in Hbinds4; intuition.
                  eapply gather_pid_events_B_gather_pid_external_events.
                  eassumption.

    (* front *)
    inversion H10; subst; simpl in *.
      inversion H11; subst; simpl in *.
      (* Inc *)
      inversion H6; subst; simpl in *.
        inversion H12; subst; simpl in *.
        inversion H14; subst; simpl in *.
        inversion H13; subst; simpl in *.
        inversion H16; subst; simpl in *.
        inversion H15; subst; simpl in *.
        apply valid_execution_fragment_com in Hvalid;
        simpl in Hvalid.
        eapply internal_preserves_request' with (pid:=pid) in Hvalid; simpl in *; eauto.
        3 : {
          apply binds_push_eq.
        }
        discriminate.
                  eapply gather_pid_events_B_gather_pid_external_events.
                  eassumption.
      auto.
  inversion H8; subst; simpl in *.
    apply valid_execution_fragment_com in Hvalid;
        simpl in Hvalid.
        inversion H6; subst; simpl in *.
        inversion H10; subst; simpl in *.
        inversion H12; subst; simpl in *.
        inversion H11; subst; simpl in *.
        inversion H14; subst; simpl in *.
        inversion H13; subst; simpl in *.
        eapply internal_preserves_notin_L1'' with (pid:=pid) in Hvalid; simpl in *; eauto.
        apply binds_in in Hbinds2.
        unfold "#" in Hvalid; intuition.
                  eapply gather_pid_events_B_gather_pid_external_events.
                  eassumption.
  tmp noB_preserves_ADeq14 Hvalid st2 pid acts Hgather H1.
  tmp noB_preserves_ADeq28 Hvalid st2 pid acts Hgather H1.
  tmp noB_preserves_ADeq31 Hvalid st2 pid acts Hgather H1.
Qed.

Ltac solve_before_d27 :=
  try apply before_d27_Deq13;
  try apply before_d27_Deq14;
  try apply before_d27_Deq15;
  try apply before_d27_Deq26;
  try (unfold before_d27;
  left;
  solve_before_d13).

Lemma inv_d5_d13_d27: forall s s1 acts1 pid,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 ->
  binds pid (ADeq5) (get_pc s) ->
  forall s' acts2,
  composed_lts.valid_execution_fragment (composed_array_queue L) s1 s' acts2 ->
  binds pid ADeq27 (get_pc s') ->
  length (gather_pid_events_B pid (acts1 ++ acts2)) = calculate_before27 ADeq5 ->
  binds pid ADeq13 (get_pc s1) ->
  length (gather_pid_events_B pid acts1) = calculate_before13 ADeq5.
Proof.
  simpl; intros.
  rewrite gather_pid_events_B_dist in H4.
  rewrite app_length in H4.
  eapply inv_before_d27_least_B_events in H2; eauto; solve_before_d27.
  simpl in H2.
  eapply inv_before_d13_least_B_events in H0; eauto; solve_before_d13.
  simpl in H0. lia.
Qed.

Lemma inv_d5_d12_d27: forall s s1 acts1 pid,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 ->
  binds pid (ADeq5) (get_pc s) ->
  forall s' acts2 ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s1 s' acts2 ->
  binds pid ADeq27 (get_pc s') ->
  length (gather_pid_events_B pid (acts1 ++ acts2)) = calculate_before27 ADeq5 ->
  binds pid (ADeq12 ret) (get_pc s1) ->
  length (gather_pid_events_B pid acts1) = calculate_before13 ADeq5.
Proof.
  simpl; intros.
  rewrite gather_pid_events_B_dist in H4.
  rewrite app_length in H4.
  eapply inv_before_d27_least_B_events in H2; eauto; solve_before_d27.
  simpl in H2.
  eapply inv_before_d12_least_B_events in H0; eauto; solve_before_d13.
  simpl in H0. lia.
Qed.

Lemma inv_d5_d11_d27: forall s s1 acts1 pid,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 ->
  binds pid (ADeq5) (get_pc s) ->
  forall s' acts2,
  composed_lts.valid_execution_fragment (composed_array_queue L) s1 s' acts2 ->
  binds pid ADeq27 (get_pc s') ->
  length (gather_pid_events_B pid (acts1 ++ acts2)) = calculate_before27 ADeq5 ->
  binds pid (ADeq11) (get_pc s1) ->
  length (gather_pid_events_B pid acts1) = calculate_before11 ADeq5.
Proof.
  simpl; intros.
  rewrite gather_pid_events_B_dist in H4.
  rewrite app_length in H4.
  eapply inv_before_d27_least_B_events in H2; eauto; solve_before_d27.
  simpl in H2.
  eapply inv_before_d11_least_B_events in H0; eauto; solve_before_d11.
  simpl in H0. lia.
Qed.

Lemma inv_d5_d11_d12: forall s s1 acts1 pid,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 ->
  binds pid (ADeq5) (get_pc s) ->
  forall s' acts2 ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s1 s' acts2 ->
  binds pid (ADeq12 ret) (get_pc s') ->
  length (gather_pid_events_B pid (acts1 ++ acts2)) = calculate_before13 AEnq5 ->
  binds pid (ADeq11) (get_pc s1) ->
  length (gather_pid_events_B pid acts1) = calculate_before11 ADeq5.
Proof.
  simpl; intros.
  rewrite gather_pid_events_B_dist in H4.
  rewrite app_length in H4.
  eapply inv_before_d12_least_B_events in H2; eauto; solve_before_d13.
  simpl in H2.
  eapply inv_before_d11_least_B_events in H0; eauto; solve_before_d11.
  simpl in H0. lia.
Qed.

Lemma inv_d5_d11_d13: forall s s1 acts1 pid,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 ->
  binds pid (ADeq5) (get_pc s) ->
  forall s' acts2,
  composed_lts.valid_execution_fragment (composed_array_queue L) s1 s' acts2 ->
  binds pid (ADeq13) (get_pc s') ->
  length (gather_pid_events_B pid (acts1 ++ acts2)) = calculate_before13 AEnq5 ->
  binds pid (ADeq11) (get_pc s1) ->
  length (gather_pid_events_B pid acts1) = calculate_before11 ADeq5.
Proof.
  simpl; intros.
  rewrite gather_pid_events_B_dist in H4.
  rewrite app_length in H4.
  eapply inv_before_d13_least_B_events in H2; eauto; solve_before_d13.
  simpl in H2.
  eapply inv_before_d11_least_B_events in H0; eauto; solve_before_d11.
  simpl in H0. lia.
Qed.

Lemma inv_d5_d27_impl_front_eq_front: forall k s pid,
  reachable_len' (composed_array_queue L) s k ->
  binds pid (ADeq5) (get_pc s) ->
  forall s' acts,
    composed_lts.valid_execution_fragment (composed_array_queue L)
      s s' acts ->
    length (gather_pid_events_B pid acts) = calculate_before27 ADeq5 ->
    binds pid ADeq27 (get_pc s') ->
    (get_impl s).(ArrayQueueImpl.front) pid = (get_front s).(Counter.value).
Proof.
  intros.
  eapply inv_before_d13_go_through_13' in H2; eauto; solve_before_d13.
  destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid1 [Hvalid2 [Hstep [Hb Heq]]]]]]]]].
  pose proof H0 as Hreach.
  apply reachable_len_to_reachable in H0.
  apply inv_front_invariant in H0; auto.
  unfold inv_front in H0.
  unfold get_impl in *; simpl in *.
  unfold get_front in *; simpl in *.
  intuition.
  specialize (H2 pid).
  inversion Hstep; subst; simpl in *.
  inversion H0; subst; simpl in *.
  unfold get_pc in *; simpl in *.
  unfold binds in Hb.
  inversion H6; subst; simpl in *;
  pose proof Hbinds0 as HbindsTmp;
  eapply substitute_eq_binds_v' in Hbinds0; eauto;
  rewrite Hbinds0 in Hb; try discriminate.
  pose proof Hvalid1 as Hvalid1Tmp.
  eapply inv_impl_front_keep in Hvalid1; eauto; solve_before_d13; solve_after_d3.
  2 : {
    eapply inv_d5_d13_d27.
    eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto.
    eapply composed_lts.Step_Internal_L2; eauto.
    eapply composed_lts.Step_None; eauto.
    rewrite app_nil_r; auto.
    auto. eauto. auto.
    auto.
    unfold get_pc; simpl.
    eapply substitute_eq_binds_v'; eauto.
  }
  unfold get_impl in *; simpl in *.
  assert (Hlen : length (gather_pid_events_B pid acts1) = calculate_before13 ADeq5).
    eapply inv_d5_d12_d27.
    eauto.
    auto.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]).
    eapply composed_lts.Step_Internal_L2; eauto.
    eapply composed_lts.Step_None; eauto.
    eauto. eauto.
    auto.
    eauto. eauto.
  eapply inv_before_d12_go_through_11' in Hvalid1Tmp; eauto; solve_before_d12.
  destruct Hvalid1Tmp as [s1' [s2' [acts1' [acts2' [it' [Hvalid1' [Hvalid2' [Hint_reply [Hb' Heq']]]]]]]]].
  inversion Hint_reply; subst; simpl in *.
  inversion H8; subst; simpl in *.
  unfold get_pc in *; simpl in *.
  unfold binds in Hb'.
  inversion H9; subst; simpl in *;
  pose proof Hbinds2 as Hbinds2Tmp;
  eapply substitute_eq_binds_v' in Hbinds2; eauto;
  rewrite Hbinds2 in Hb'; try discriminate.
Qed.

Lemma inv_d27_from_d5_keeps_vec_front_impl_front_eq_front: forall k s,
  reachable_len' (composed_array_queue L) s k ->
  forall pid,
    binds pid ADeq27 (get_pc s) ->
    exists s1 s2 acts ret n,
      composed_lts.valid_execution_fragment (composed_array_queue L) s2 s acts /\
      composed_lts.step_L1 (composed_array_queue L)
      s1 pid ((@intL1 li_array li_cnt_cnt (array L) ArrayQueue.front_rear int_ary_read)) s2 /\
      binds pid (ADeq5) (get_pc s1) /\
      (length (gather_pid_events_B pid acts)) = 5 /\
      reachable_len' (composed_array_queue L) s1 n /\
      n < k /\
      binds pid (AryReadOk ret) (get_ary s2).(Array.responses L) /\
      (get_xp s) pid = ret /\
      (
        ((get_impl s).(ArrayQueueImpl.x) pid) = get_vec_front H s pid ->
        get_vec_front H s pid = get_vec_front H s2 pid
      ) /\
      (get_impl s1).(ArrayQueueImpl.front) pid = (get_front s1).(Counter.value).
Proof.
  intros.
  eapply inv_d27_from_d5_keeps_vec_rear with (H:=H) in H0; eauto.
  destruct H0 as [s1 [s2 [acts [ret [n [Hvalid [Hstep [Hb [Hgather [Hreach [Hlt [Hb' [Hxp Himply]]]]]]]]]]]]].
  exists s1, s2, acts, ret, n. intuition.
  eapply inv_d5_d27_impl_front_eq_front with (s:=s1).
  eauto.
  auto.
  3 : { eauto. }
  eapply composed_lts.valid_execution_fragment_join' with (a':=acts).
  eapply composed_lts.Step_Internal_L1.
  eauto.
  eapply composed_lts.Step_None; eauto.
  auto.
  simpl.
  eauto.
  simpl. auto.
Qed.

Lemma inv_d27_from_d5_keeps_vec_front_impl_front_eq_front_k_step: forall k s,
  reachable_len' (composed_array_queue L) s k ->
  forall pid,
    binds pid ADeq27 (get_pc s) ->
    exists s1 s2 acts ret n t,
      valid_execution_fragment_len' (composed_array_queue L) s2 s acts t /\
      composed_lts.step_L1 (composed_array_queue L)
      s1 pid ((@intL1 li_array li_cnt_cnt (array L) ArrayQueue.front_rear int_ary_read)) s2 /\
      binds pid (ADeq5) (get_pc s1) /\
      (length (gather_pid_events_B pid acts)) = 5 /\
      reachable_len' (composed_array_queue L) s1 n /\
      n < k /\
      k = n + 1 + t /\
      binds pid (AryReadOk ret) (get_ary s2).(Array.responses L) /\
      (get_xp s) pid = ret /\
      (
        ((get_impl s).(ArrayQueueImpl.x) pid) = get_vec_front H s pid ->
        get_vec_front H s pid = get_vec_front H s2 pid
      ) /\
      (get_impl s1).(ArrayQueueImpl.front) pid = (get_front s1).(Counter.value).
Proof.
  intros.
  eapply inv_d27_from_d5_keeps_vec_rear_k_step with (H:=H) in H0; eauto.
  destruct H0 as [s1 [s2 [acts [ret [n [t [Hvalid [Hstep [Hb [Hgather [Hreach [Hlt [Heq [Hb' [Hxp Himply]]]]]]]]]]]]]]].
  exists s1, s2, acts, ret, n, t. intuition.
  eapply inv_d5_d27_impl_front_eq_front with (s:=s1).
  eauto.
  auto.
  3 : { eauto. }
  eapply composed_lts.valid_execution_fragment_join' with (a':=acts).
  eapply composed_lts.Step_Internal_L1.
  eauto.
  eapply composed_lts.Step_None; eauto.
  eapply valid_execution_fragment_len'_to_valid_execution_fragment; eauto.
  auto.
  simpl.
  eauto.
Qed.

End test.