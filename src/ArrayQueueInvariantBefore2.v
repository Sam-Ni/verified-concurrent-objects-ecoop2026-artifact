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
  ArrayQueueInvariantBefore.
Import ListNotations.

Section test.

Arguments get_pc {L}.
Arguments get_xp {L}.
Arguments get_ary {L}.
Arguments get_impl {L}.
Arguments get_rear {L}.

Variable L : nat.

Ltac solve_after_e6 :=
  try apply after_e6_Enq10;
  try apply after_e6_Enq11;
  try apply after_e6_Enq12;
  try apply after_e6_Enq13;
  try apply after_e6_Enq14;
  try apply after_e6_Enq15;
  try apply after_e6_Enq26;
  try apply after_e6_Enq27.

Lemma inv_e27_from_e6_ret': forall k s,
  reachable_len' (composed_array_queue L) s k ->
  forall pid,
    binds pid AEnq27 (get_pc s) ->
    exists s' acts ret n,
      composed_lts.valid_execution_fragment (composed_array_queue L) s' s acts /\
      binds pid (AEnq6 ret) (get_pc s') /\
      length (gather_pid_events_B pid acts) = 4 /\
      reachable_len' (composed_array_queue L) s' n /\
      n < k /\
      (get_xp s) pid = ret.
Proof.
  intros. eapply inv_e27_from_e6_ret in H; eauto; solve_after_e6.
  destruct H as [s' [acts [ret [n [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]].
  exists s', acts, ret, n.
  intuition.
  eapply inv_e6_ret_e27_xp; eauto; solve_after_e6.
  apply valid_execution_fragment_to_new_valid_execution_fragment; auto.
Qed.

Lemma inv_e27_from_e6_ret_k_step': forall k s,
  reachable_len' (composed_array_queue L) s k ->
  forall pid,
    binds pid AEnq27 (get_pc s) ->
    exists s' acts ret n t,
      valid_execution_fragment_len' (composed_array_queue L) s' s acts t /\
      binds pid (AEnq6 ret) (get_pc s') /\
      length (gather_pid_events_B pid acts) = 4 /\
      reachable_len' (composed_array_queue L) s' n /\
      n < k /\
      k = n + t /\
      (get_xp s) pid = ret.
Proof.
  intros. eapply inv_e27_from_e6_ret_k_step in H; eauto; solve_after_e6.
  destruct H as [s' [acts [ret [n [t [Hvalid [Hb [Hgather [Hr [Hlt Heq]]]]]]]]]].
  exists s', acts, ret, n, t.
  intuition.
  eapply inv_e6_ret_e27_xp; eauto; solve_after_e6.
  apply valid_execution_fragment_to_new_valid_execution_fragment; auto.
  eapply valid_execution_fragment_len'_to_valid_execution_fragment; eauto.
Qed.

Lemma inv_e27_from_e5_internal_ret: forall k s,
  reachable_len' (composed_array_queue L) s k ->
  forall pid,
    binds pid AEnq27 (get_pc s) ->
    exists s1 s2 acts ret n,
      composed_lts.valid_execution_fragment (composed_array_queue L) s2 s acts /\
      composed_lts.step_L1 (composed_array_queue L)
      s1 pid ((@intL1 li_array li_cnt_cnt (array L) ArrayQueue.front_rear int_ary_read)) s2 /\
      binds pid (AEnq5) (get_pc s1) /\
      (length (gather_pid_events_B pid acts)) = 5 /\
      reachable_len' (composed_array_queue L) s1 n /\
      n < k /\
      binds pid (AryReadOk ret) (get_ary s2).(Array.responses L) /\
      (get_xp s) pid = ret.
Proof.
  intros.
  eapply inv_e27_from_e6_ret' in H; eauto; solve_after_e6.
  destruct H as [s' [acts [ret [n [Hvalid [Hb [Hgather [Hr [Hlt Hxp]]]]]]]]].
  eapply inv_e6_ret_e5_internal_step with (pid:=pid) (v:=AEnq6 ret) (ret:=ret) in Hr; eauto.
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
  eapply inv_e5_ret_e6_ret in Hb; eauto.
  erewrite <-Hb.
  apply binds_push_eq; auto.
  simpl.
  apply binds_push_eq; auto.
Qed.

Lemma inv_e27_from_e5_internal_ret_k_step: forall k s,
  reachable_len' (composed_array_queue L) s k ->
  forall pid,
    binds pid AEnq27 (get_pc s) ->
    exists s1 s2 acts ret n t,
      valid_execution_fragment_len' (composed_array_queue L) s2 s acts t /\
      composed_lts.step_L1 (composed_array_queue L)
      s1 pid ((@intL1 li_array li_cnt_cnt (array L) ArrayQueue.front_rear int_ary_read)) s2 /\
      binds pid (AEnq5) (get_pc s1) /\
      (length (gather_pid_events_B pid acts)) = 5 /\
      reachable_len' (composed_array_queue L) s1 n /\
      n < k /\
      k = n + 1 + t /\
      binds pid (AryReadOk ret) (get_ary s2).(Array.responses L) /\
      (get_xp s) pid = ret.
Proof.
  intros.
  eapply inv_e27_from_e6_ret_k_step' in H; eauto; solve_after_e6.
  destruct H as [s' [acts [ret [n [t [Hvalid [Hb [Hgather [Hr [Hlt [Heq Hxp]]]]]]]]]]].
  eapply inv_e6_ret_e5_internal_step_k_step with (pid:=pid) (v:=AEnq6 ret) (ret:=ret) in Hr; eauto.
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
  eapply inv_e5_ret_e6_ret in Hb; eauto.
  erewrite <-Hb.
  apply binds_push_eq; auto.
  simpl.
  apply binds_push_eq; auto.
Qed.

Lemma inv_e13_stuttering : forall s s' acts pid,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  binds pid AEnq13 (get_pc s) ->
  length (gather_pid_events_B pid acts) = 0 ->
  binds pid AEnq13 (get_pc s').
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

Definition get_vec_rear s pid :=
  (Vector.nth
    ((get_ary s).(Array.vec L))
    (Fin.of_nat_lt (mod_lt H
                    ((get_impl s).(ArrayQueueImpl.rear) pid)))).
  
Lemma inv_e27_from_e5_keeps_vec_rear: forall k s,
  reachable_len' (composed_array_queue L) s k ->
  forall pid,
    binds pid AEnq27 (get_pc s) ->
    exists s1 s2 acts ret n,
      composed_lts.valid_execution_fragment (composed_array_queue L) s2 s acts /\
      composed_lts.step_L1 (composed_array_queue L)
      s1 pid ((@intL1 li_array li_cnt_cnt (array L) ArrayQueue.front_rear int_ary_read)) s2 /\
      binds pid (AEnq5) (get_pc s1) /\
      (length (gather_pid_events_B pid acts)) = 5 /\
      reachable_len' (composed_array_queue L) s1 n /\
      n < k /\
      binds pid (AryReadOk ret) (get_ary s2).(Array.responses L) /\
      (get_xp s) pid = ret /\
      (
        ((get_impl s).(ArrayQueueImpl.x) pid) = get_vec_rear s pid ->
        get_vec_rear s pid = get_vec_rear s2 pid
      ).
Proof.
  intros.
  unfold get_vec_rear.
  eapply inv_e27_from_e5_internal_ret in H0; eauto.
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
  eapply inv_e5_instant in Hr; eauto.
  simpl in Hr.
  unfold get_impl in Hr; simpl in Hr.
  unfold binds in Hbinds3.
  rewrite Hr in Hbinds3.
  inversion Hbinds3; subst; simpl in *.
  erewrite Fin.of_nat_ext; eauto.
Qed.

Lemma inv_e27_from_e5_keeps_vec_rear_k_step: forall k s,
  reachable_len' (composed_array_queue L) s k ->
  forall pid,
    binds pid AEnq27 (get_pc s) ->
    exists s1 s2 acts ret n t,
      valid_execution_fragment_len' (composed_array_queue L) s2 s acts t /\
      composed_lts.step_L1 (composed_array_queue L)
      s1 pid ((@intL1 li_array li_cnt_cnt (array L) ArrayQueue.front_rear int_ary_read)) s2 /\
      binds pid (AEnq5) (get_pc s1) /\
      (length (gather_pid_events_B pid acts)) = 5 /\
      reachable_len' (composed_array_queue L) s1 n /\
      n < k /\
      k = n + 1 + t /\
      binds pid (AryReadOk ret) (get_ary s2).(Array.responses L) /\
      (get_xp s) pid = ret /\
      (
        ((get_impl s).(ArrayQueueImpl.x) pid) = get_vec_rear s pid ->
        get_vec_rear s pid = get_vec_rear s2 pid
      ).
Proof.
  intros.
  unfold get_vec_rear.
  eapply inv_e27_from_e5_internal_ret_k_step in H0; eauto.
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
  eapply inv_e5_instant in Hr; eauto.
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
Arguments R {L}.

Variable L : nat.

Definition before_e13 v :=
  v = AEnq1 \/
  v = AEnq2 \/
  (exists r, v = AEnq3 r) \/
  v = AEnq4 \/
  v = AEnq5 \/
  (exists r, v = AEnq6 r) \/
  v = AEnq10 \/
  v = AEnq11 \/
  (exists r, v = AEnq12 r).

Lemma before_e13_Enq1:
  before_e13 (AEnq1).
Proof.
  intros.
  unfold before_e13.
  intuition.
Qed.

Lemma before_e13_Enq2:
  before_e13 (AEnq2).
Proof.
  intros.
  unfold before_e13.
  intuition.
Qed.

Lemma before_e13_Enq3: forall ret,
  before_e13 (AEnq3 ret).
Proof.
  intros.
  unfold before_e13.
  right. right. left.
  exists ret.
  reflexivity.
Qed.

Lemma before_e13_Enq4:
  before_e13 (AEnq4).
Proof.
  intros.
  unfold before_e13.
  intuition.
Qed.

Lemma before_e13_Enq5:
  before_e13 (AEnq5).
Proof.
  intros.
  unfold before_e13.
  intuition.
Qed.

Lemma before_e13_Enq6: forall ret,
  before_e13 (AEnq6 ret).
Proof.
  intros.
  unfold before_e13.
  right. right. right. right. right. left.
  exists ret.
  reflexivity.
Qed.

Lemma before_e13_Enq10:
  before_e13 (AEnq10).
Proof.
  intros.
  unfold before_e13.
  intuition.
Qed.

Lemma before_e13_Enq11:
  before_e13 (AEnq11).
Proof.
  intros.
  unfold before_e13.
  intuition.
Qed.

Lemma before_e13_Enq12: forall ret,
  before_e13 (AEnq12 ret).
Proof.
  intros.
  unfold before_e13.
  right. right. right. right. right.
  right. right. right.
  exists ret.
  reflexivity.
Qed.

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

Definition before_e27 v :=
  before_e13 v \/
  v = AEnq13 \/
  v = AEnq14  \/
  (exists r, v = AEnq15 r) \/
  v = AEnq26.

Lemma before_e27_Enq13:
  before_e27 (AEnq13).
Proof.
  intros.
  unfold before_e27.
  intuition.
Qed.

Lemma before_e27_Enq14:
  before_e27 (AEnq14).
Proof.
  intros.
  unfold before_e27.
  intuition.
Qed.

Lemma before_e27_Enq15: forall ret,
  before_e27 (AEnq15 ret).
Proof.
  intros.
  unfold before_e27.
  right. right. right. left.
  exists ret.
  reflexivity.
Qed.

Lemma before_e27_Enq26:
  before_e27 (AEnq26).
Proof.
  intros.
  unfold before_e27.
  intuition.
Qed.

Ltac solve_before_e27 :=
  (* try unfold before_e27;
  try unfold before_e13; *)
  try apply before_e27_Enq13;
  try apply before_e27_Enq14;
  try apply before_e27_Enq15;
  try apply before_e27_Enq26;
  try (unfold before_e27;
  left;
  solve_before_e13).

Definition calculate_before27 v :=
  match v with
  | AEnq1 => 8
  | AEnq2 => 7
  | AEnq3 r => 6
  | AEnq4 => 6
  | AEnq5 => 5
  | AEnq6 r => 4
  | AEnq10 => 4
  | AEnq11 => 3
  | AEnq12 r => 2
  | AEnq13 => 2
  | AEnq14  => 1
  | AEnq15 r => 0
  | AEnq26 => 0
  | _ => 0
  end.

Lemma inv_before27_least_B_events: forall s s' acts pid,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  forall v,
  before_e27 v ->
  binds pid v (get_pc s) ->
  binds pid AEnq27 (get_pc s') ->
  length (gather_pid_events_B pid acts) >= calculate_before27 v.
Proof.
  induction 1; intros.
  - subst. unfold before_e27 in H0.
    unfold binds in H2.
    intuition; subst; try (rewrite H1 in H2; discriminate).
    unfold before_e13 in H.
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
      try (eapply substitute_eq_binds_v'; eauto); solve_before_e27;
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
      try (eapply substitute_eq_binds_v'; eauto); solve_before_e27;
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
      try (eapply substitute_eq_binds_v'; eauto); solve_before_e27;
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

Lemma inv_before13_go_through_13: forall s s' acts pid,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  forall v (Hv : before_e13 v),
  binds pid v (get_pc s) ->
  binds pid AEnq27 (get_pc s') ->
  length (gather_pid_events_B pid acts) = calculate_before27 v ->
  exists s1 s2 acts1 acts2 it,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 /\
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s2 s' acts2 /\
  composed_lts.step_L2 (composed_array_queue L)
  s1 pid it s2 /\
  binds pid AEnq13 (get_pc s2).
Proof.
  induction 1; intros.
  - subst. simpl in H2.
    unfold before_e13 in Hv.
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
        unfold before_e13 in Hv;
        intuition; subst; try discriminate;
      try (destruct H6 as [t Ht]; subst);
      try (destruct H7 as [t Ht]; subst);
      try (destruct H8 as [t Ht]; subst);
      inversion H1; subst;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_e13;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2, acts1, acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto;
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto).
      inversion H1; subst.
      simpl in H3.
      eapply inv_before27_least_B_events in H0;
      unfold get_pc; simpl in *;
      eauto; simpl;
      try (eapply substitute_eq_binds_v'; eauto); solve_before_e27.
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
      unfold before_e13 in Hv; intuition; subst; try discriminate;
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
      unfold before_e13 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      simpl in H3;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_e13;
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
      unfold before_e13 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      simpl in H3;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_e13;
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

Lemma inv_before13_go_through_13': forall s s' acts pid,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  forall v (Hv : before_e13 v),
  binds pid v (get_pc s) ->
  binds pid AEnq27 (get_pc s') ->
  length (gather_pid_events_B pid acts) = calculate_before27 v ->
  exists s1 s2 acts1 acts2 it,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 /\
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s2 s' acts2 /\
  composed_lts.step_L2 (composed_array_queue L)
  s1 pid it s2 /\
  binds pid AEnq13 (get_pc s2) /\
  acts = acts1 ++ acts2.
Proof.
  induction 1; intros.
  - subst. simpl in H2.
    unfold before_e13 in Hv.
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
        unfold before_e13 in Hv;
        intuition; subst; try discriminate;
      try (destruct H6 as [t Ht]; subst);
      try (destruct H7 as [t Ht]; subst);
      try (destruct H8 as [t Ht]; subst);
      inversion H1; subst;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_e13;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2, acts1, acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto;
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto).
      inversion H1; subst.
      simpl in H3.
      eapply inv_before27_least_B_events in H0;
      unfold get_pc; simpl in *;
      eauto; simpl;
      try (eapply substitute_eq_binds_v'; eauto); solve_before_e27.
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
      unfold before_e13 in Hv; intuition; subst; try discriminate;
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
      unfold before_e13 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      simpl in H3;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_e13;
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
      unfold before_e13 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      simpl in H3;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_e13;
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

Definition after_e3 v :=
  v = AEnq4 \/
  v = AEnq5 \/
  (exists ret, v = AEnq6 ret) \/
  after_e6 v.

Lemma after_e3_Enq4:
  after_e3 (AEnq4).
Proof.
  intros.
  unfold after_e3.
  intuition.
Qed.

Lemma after_e3_Enq5:
  after_e3 (AEnq5).
Proof.
  intros.
  unfold after_e3.
  intuition.
Qed.

Lemma after_e3_Enq6: forall ret,
  after_e3 (AEnq6 ret).
Proof.
  intros.
  unfold after_e3.
  right. right. left.
  exists ret.
  reflexivity.
Qed.

Ltac solve_after_e6 :=
  try apply after_e6_Enq10;
  try apply after_e6_Enq11;
  try apply after_e6_Enq12;
  try apply after_e6_Enq13;
  try apply after_e6_Enq14;
  try apply after_e6_Enq15;
  try apply after_e6_Enq26;
  try apply after_e6_Enq27.

Ltac solve_after_e3 :=
  try apply after_e3_Enq4;
  try apply after_e3_Enq5;
  try apply after_e3_Enq6;
  try (unfold after_e6;
  right; right; right;
  solve_after_e6).

Definition calculate_before13 v :=
  match v with
  | AEnq1 => 6
  | AEnq2 => 5
  | AEnq3 r => 4
  | AEnq4 => 4
  | AEnq5 => 3
  | AEnq6 r => 2
  | AEnq10 => 2
  | AEnq11 => 1
  | AEnq12 r => 0
  | _ => 0
  end.

Lemma inv_before12_least_B_events: forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  forall v,
  before_e13 v ->
  binds pid v (get_pc s) ->
  binds pid (AEnq12 ret) (get_pc s') ->
  length (gather_pid_events_B pid acts) >= calculate_before13 v.
Proof.
  induction 1; intros.
  - subst. unfold before_e13 in H0.
    unfold binds in H2.
    intuition; subst; try (rewrite H1 in H2; discriminate).
    unfold before_e13 in H.
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
      try (eapply substitute_eq_binds_v'; eauto); solve_before_e13;
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
      try (eapply substitute_eq_binds_v'; eauto); solve_before_e13;
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
      try (eapply substitute_eq_binds_v'; eauto); solve_before_e13;
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

Lemma inv_e1_stuttering : forall s s' acts pid,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  binds pid (AEnq1) (get_pc s) ->
  length (gather_pid_events_B pid acts) = 0 ->
  binds pid (AEnq1) (get_pc s').
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

Lemma inv_e12_stuttering : forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  binds pid (AEnq12 ret) (get_pc s) ->
  length (gather_pid_events_B pid acts) = 0 ->
  binds pid (AEnq12 ret) (get_pc s') \/
  binds pid AEnq13 (get_pc s') \/
  binds pid AEnq1 (get_pc s').
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
      eapply inv_e1_stuttering in H0; eauto.
      unfold get_pc; simpl; auto.
      eapply substitute_eq_binds_v'; eauto.
      eapply inv_e13_stuttering in H0; eauto.
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

Lemma inv_e11_ret_e12_ret: forall s s' pid acts,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  binds pid (AEnq11) (get_pc s) ->
  forall ret ret0,
  binds pid (CntReadOk ret) (get_rear s).(Counter.responses) ->
  binds pid (AEnq12 ret0) (get_pc s') ->
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
      rewrite Nat.eqb_refl in H4.
      simpl in H4.
      inversion H5; subst; simpl in *.
      inversion H8; subst; simpl in *.
      inversion H10; subst; simpl in *.
      inversion H9; subst; simpl in *.
      unfold binds in H2.
      inversion H12; subst; simpl in *.
      inversion H11; subst; simpl in *.
      rewrite Hbinds6 in H2.
      inversion H2; subst.
      eapply inv_e12_stuttering with (ret:=ret) in H0; eauto.
      intuition.
      unfold get_pc in H13; simpl in H13.
      unfold binds in H13.
      rewrite H3 in H13.
      inversion H13; subst; auto.
      unfold get_pc in H0; simpl in H0.
      unfold binds in H0.
      rewrite H3 in H0.
      inversion H0; subst; auto.
      unfold get_pc in H0; simpl in H0.
      unfold binds in H0.
      rewrite H3 in H0.
      inversion H0; subst; auto.
      unfold get_pc; simpl.
      eapply substitute_eq_binds_v'; eauto.
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

Lemma inv_e13_e12: forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  binds pid (AEnq13) (get_pc s) ->
  binds pid (AEnq12 ret) (get_pc s') ->
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

Lemma inv_impl_rear_keep: forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s' acts ->
  forall v 
  (Hv: before_e13 v)
  (Hv' : after_e3 v),
  binds pid v (get_pc s) ->
  length (gather_pid_events_B pid acts) = calculate_before13 v ->
  binds pid (AEnq12 ret) (get_pc s') ->
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
      erewrite IHvalid_execution_fragment;
      try (eapply substitute_eq_binds_v'; eauto);
      rewrite Hbinds0 in H1;
      inversion H1; subst;
      auto;
      [solve_before_e13|solve_after_e3]. 
      all : try (rewrite Hbinds0 in H1;
      inversion H1; subst; simpl in *;
      eapply inv_before12_least_B_events with (pid:=pid0) (v:=AEnq1) in H0;
      unfold get_pc in *; simpl in *;
      solve_before_e13; eauto;
      try (eapply substitute_eq_binds_v'; eauto);
      rewrite H2 in H0; lia).
      rewrite Hbinds0 in H1;
      inversion H1; subst; simpl in H2.
      eapply inv_e13_e12 in H0; eauto;
      try (rewrite H2 in H0; lia);
      unfold get_pc; simpl;
      eapply substitute_eq_binds_v'; eauto.
      all : rewrite Hbinds0 in H1;
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
      unfold before_e13 in Hv;
      intuition; subst; try discriminate;
      try (destruct H6; subst; discriminate);
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate).
      unfold after_e3 in Hv'.
      unfold after_e6 in Hv'.
      intuition; subst; try discriminate;
      try (destruct H8; subst; discriminate).
      try (destruct H9; subst; discriminate).
      all : erewrite IHvalid_execution_fragment;
      try (eapply substitute_eq_binds_v'; eauto);
      auto; [solve_before_e13|solve_after_e3].
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
      auto; [solve_before_e13|solve_after_e3].
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
  binds pid (AEnq12 ret) (get_pc s) ->
  length (gather_pid_events_B pid acts) = 0 ->
  binds pid (AEnq12 ret0) (get_pc s') ->
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
      eapply inv_before12_least_B_events with (pid:=pid0) (v:=AEnq1) in H0;
      unfold get_pc in *; simpl in *;
      solve_before_e13; eauto;
      try (eapply substitute_eq_binds_v'; eauto);
      rewrite H2 in H0; lia.
      eapply inv_e13_e12 in H0; eauto;
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

Lemma inv_before13_least_B_events: forall s s' acts pid,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  forall v,
  before_e13 v ->
  binds pid v (get_pc s) ->
  binds pid (AEnq13) (get_pc s') ->
  length (gather_pid_events_B pid acts) >= calculate_before13 v.
Proof.
  induction 1; intros.
  - subst. unfold before_e13 in H0.
    unfold binds in H2.
    intuition; subst; try (rewrite H1 in H2; discriminate).
    unfold before_e13 in H.
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
      try (eapply substitute_eq_binds_v'; eauto); solve_before_e13;
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
      try (eapply substitute_eq_binds_v'; eauto); solve_before_e13;
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
      try (eapply substitute_eq_binds_v'; eauto); solve_before_e13;
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

Definition before_e12 v :=
  v = AEnq1 \/
  v = AEnq2 \/
  (exists r, v = AEnq3 r) \/
  v = AEnq4 \/
  v = AEnq5 \/
  (exists r, v = AEnq6 r) \/
  v = AEnq10 \/
  v = AEnq11.

Lemma before_e12_Enq1:
  before_e12 (AEnq1).
Proof.
  intros.
  unfold before_e12.
  intuition.
Qed.

Lemma before_e12_Enq2:
  before_e12 (AEnq2).
Proof.
  intros.
  unfold before_e12.
  intuition.
Qed.

Lemma before_e12_Enq3: forall ret,
  before_e12 (AEnq3 ret).
Proof.
  intros.
  unfold before_e12.
  right. right. left.
  exists ret.
  reflexivity.
Qed.

Lemma before_e12_Enq4:
  before_e12 (AEnq4).
Proof.
  intros.
  unfold before_e12.
  intuition.
Qed.

Lemma before_e12_Enq5:
  before_e12 (AEnq5).
Proof.
  intros.
  unfold before_e12.
  intuition.
Qed.

Lemma before_e12_Enq6: forall ret,
  before_e12 (AEnq6 ret).
Proof.
  intros.
  unfold before_e12.
  right. right. right. right. right. left.
  exists ret.
  reflexivity.
Qed.

Lemma before_e12_Enq10:
  before_e12 (AEnq10).
Proof.
  intros.
  unfold before_e12.
  intuition.
Qed.

Lemma before_e12_Enq11:
  before_e12 (AEnq11).
Proof.
  intros.
  unfold before_e12.
  intuition.
Qed.

Ltac solve_before_e12 :=
  try apply before_e12_Enq1;
  try apply before_e12_Enq2;
  try apply before_e12_Enq3;
  try apply before_e12_Enq4;
  try apply before_e12_Enq5;
  try apply before_e12_Enq6;
  try apply before_e12_Enq10;
  try apply before_e12_Enq11.

Lemma inv_before12_go_through_11: forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  forall v (Hv : before_e12 v),
  binds pid v (get_pc s) ->
  binds pid (AEnq12 ret) (get_pc s') ->
  length (gather_pid_events_B pid acts) = calculate_before13 v ->
  exists s1 s2 acts1 acts2 it,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 /\
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s2 s' acts2 /\
  composed_lts.internal_reply (composed_array_queue L)
  s1 pid it s2 /\
  binds pid (AEnq12 ret) (get_pc s2).
Proof.
  induction 1; intros.
  - subst. simpl in H2.
    unfold before_e12 in Hv.
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
        unfold before_e12 in Hv;
        intuition; subst; try discriminate;
      try (destruct H6 as [t Ht]; subst);
      try (destruct H7 as [t Ht]; subst);
      try (destruct H8 as [t Ht]; subst);
      inversion H1; subst;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_e12;
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
      unfold before_e12 in Hv; intuition; subst; try discriminate;
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
      unfold before_e12 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      simpl in H3;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_e12;
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
      unfold before_e12 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      simpl in H3;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_e12;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join'; eauto;
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto).
      eexists.
      eexists.
      eexists.
      eexists.
      eexists.
      intuition.
      eapply composed_lts.Step_None; eauto.
      eauto.
      eassumption.
      simpl.
      rewrite Hbinds0 in H1.
      inversion H1; subst.
      simpl in H3.
      eapply inv_impl_pc_keep with (ret:=ret0) in H0; eauto.
      subst.
      eapply substitute_eq_binds_v'; eauto.
      unfold get_pc.
      simpl.
      eapply substitute_eq_binds_v'; eauto.
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

Lemma inv_before12_go_through_11': forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  forall v (Hv : before_e12 v),
  binds pid v (get_pc s) ->
  binds pid (AEnq12 ret) (get_pc s') ->
  length (gather_pid_events_B pid acts) = calculate_before13 v ->
  exists s1 s2 acts1 acts2 it,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 /\
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s2 s' acts2 /\
  composed_lts.internal_reply (composed_array_queue L)
  s1 pid it s2 /\
  binds pid (AEnq12 ret) (get_pc s2) /\
  acts = acts1 ++ [(pid, composed_lts.event_resB it)] ++ acts2.
Proof.
  induction 1; intros.
  - subst. simpl in H2.
    unfold before_e12 in Hv.
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
        unfold before_e12 in Hv;
        intuition; subst; try discriminate;
      try (destruct H6 as [t Ht]; subst);
      try (destruct H7 as [t Ht]; subst);
      try (destruct H8 as [t Ht]; subst);
      inversion H1; subst;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_e12;
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
      unfold before_e12 in Hv; intuition; subst; try discriminate;
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
      unfold before_e12 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      simpl in H3;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_e12;
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
      unfold before_e12 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      simpl in H3;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_e12;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep [Hb Heq]]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition;
      try (eapply composed_lts.valid_execution_fragment_join'; eauto;
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto);
      rewrite Heq; simpl; auto).
      eexists.
      eexists.
      eexists.
      eexists.
      eexists.
      intuition.
      eapply composed_lts.Step_None; eauto.
      eauto.
      eassumption.
      simpl.
      rewrite Hbinds0 in H1.
      inversion H1; subst.
      simpl in H3.
      eapply inv_impl_pc_keep with (ret:=ret0) in H0; eauto.
      subst.
      eapply substitute_eq_binds_v'; eauto.
      unfold get_pc.
      simpl.
      eapply substitute_eq_binds_v'; eauto.
      simpl. reflexivity.
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

Definition before_e11 v :=
  v = AEnq1 \/
  v = AEnq2 \/
  (exists r, v = AEnq3 r) \/
  v = AEnq4 \/
  v = AEnq5 \/
  (exists r, v = AEnq6 r) \/
  v = AEnq10.

Lemma before_e11_Enq1:
  before_e11 (AEnq1).
Proof.
  intros.
  unfold before_e11.
  intuition.
Qed.

Lemma before_e11_Enq2:
  before_e11 (AEnq2).
Proof.
  intros.
  unfold before_e11.
  intuition.
Qed.

Lemma before_e11_Enq3: forall ret,
  before_e11 (AEnq3 ret).
Proof.
  intros.
  unfold before_e11.
  right. right. left.
  exists ret.
  reflexivity.
Qed.

Lemma before_e11_Enq4:
  before_e11 (AEnq4).
Proof.
  intros.
  unfold before_e11.
  intuition.
Qed.

Lemma before_e11_Enq5:
  before_e11 (AEnq5).
Proof.
  intros.
  unfold before_e11.
  intuition.
Qed.

Lemma before_e11_Enq6: forall ret,
  before_e11 (AEnq6 ret).
Proof.
  intros.
  unfold before_e11.
  right. right. right. right. right. left.
  exists ret.
  reflexivity.
Qed.

Lemma before_e11_Enq10:
  before_e11 (AEnq10).
Proof.
  intros.
  unfold before_e11.
  intuition.
Qed.

Ltac solve_before_e11 :=
  try apply before_e11_Enq1;
  try apply before_e11_Enq2;
  try apply before_e11_Enq3;
  try apply before_e11_Enq4;
  try apply before_e11_Enq5;
  try apply before_e11_Enq6;
  try apply before_e11_Enq10.

Lemma inv_e11_internal_step: forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  binds pid (AEnq11) (get_pc s) ->
  binds pid (CntRead) (get_rear s).(Counter.requests) ->
  pid # (get_rear s).(Counter.responses) ->
  binds pid (AEnq11) (get_pc s') ->
  binds pid (CntReadOk ret) (get_rear s').(Counter.responses) ->
  length (gather_pid_events_B pid acts) = 0 ->
  exists s1 s2 acts1 acts2 it,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 /\
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s2 s' acts2 /\
  composed_lts.step_L1 (composed_array_queue L)
  s1 pid it s2 /\
  binds pid (AEnq11) (get_pc s2).
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
      try eapply substitute_eq_binds_v'; eauto; solve_before_e12;
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

Lemma inv_e11_internal_step': forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  binds pid (AEnq11) (get_pc s) ->
  binds pid (CntRead) (get_rear s).(Counter.requests) ->
  pid # (get_rear s).(Counter.responses) ->
  binds pid (AEnq11) (get_pc s') ->
  binds pid (CntReadOk ret) (get_rear s').(Counter.responses) ->
  length (gather_pid_events_B pid acts) = 0 ->
  exists s1 s2 acts1 acts2 it,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 /\
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s2 s' acts2 /\
  composed_lts.step_L1 (composed_array_queue L)
  s1 pid it s2 /\
  binds pid (AEnq11) (get_pc s2) /\
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
      try eapply substitute_eq_binds_v'; eauto; solve_before_e12;
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

Lemma inv_e10_internal_step: forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  binds pid (AEnq10) (get_pc s) ->
  (* binds pid (CntRead) (get_rear s').(Counter.requests) -> *)
  binds pid (AEnq11) (get_pc s') ->
  (* pid # (get_rear s').(Counter.requests) -> *)
  binds pid (CntReadOk ret) (get_rear s').(Counter.responses) ->
  length (gather_pid_events_B pid acts) = 0 ->
  exists s1 s2 acts1 acts2 it,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 /\
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s2 s' acts2 /\
  composed_lts.step_L1 (composed_array_queue L)
  s1 pid it s2 /\
  binds pid (AEnq11) (get_pc s2).
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
      try eapply substitute_eq_binds_v'; eauto; solve_before_e12;
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
  | AEnq1 => 5
  | AEnq2 => 4
  | AEnq3 r => 3
  | AEnq4 => 3
  | AEnq5 => 2
  | AEnq6 r => 1
  | AEnq10 => 1
  | AEnq11 => 0
  | AEnq12 r => 0
  | _ => 0
  end.

Lemma inv_before11_go_through_internal: forall s s' acts pid ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  forall v (Hv : before_e11 v),
  binds pid v (get_pc s) ->
  binds pid (AEnq11) (get_pc s') ->
  binds pid (CntReadOk ret) (get_rear s').(Counter.responses) ->
  length (gather_pid_events_B pid acts) = calculate_before11 v ->
  exists s1 s2 acts1 acts2 it,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 /\
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s2 s' acts2 /\
  composed_lts.step_L1 (composed_array_queue L)
  s1 pid it s2 /\
  binds pid (AEnq11) (get_pc s2).
Proof.
  induction 1; intros.
  - subst. simpl in H2.
    unfold before_e11 in Hv.
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
        unfold before_e11 in Hv;
        intuition; subst; try discriminate;
      try (destruct H6 as [t Ht]; subst);
      try (destruct H7 as [t Ht]; subst);
      try (destruct H8 as [t Ht]; subst);
      inversion H1; subst;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_e11;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2, acts1, acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto;
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto).
      all : unfold before_e11 in Hv;
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
      unfold before_e11 in Hv; intuition; subst; try discriminate;
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
      unfold before_e11 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      try (destruct H9; subst; discriminate);
      simpl in H4;
      eapply IHvalid_execution_fragment in H3;
      try eapply substitute_eq_binds_v'; eauto; solve_before_e11;
      destruct H3 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join'; eauto;
      eapply composed_lts.Step_Internal_Query; eauto;
      eapply composed_lts.Step_None; eauto).

      eapply inv_e11_internal_step in H0.
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
      unfold before_e11 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      try (destruct H9; subst; discriminate);
      simpl in H4;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_e11;
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
  forall v (Hv : before_e11 v),
  binds pid v (get_pc s) ->
  binds pid (AEnq11) (get_pc s') ->
  binds pid (CntReadOk ret) (get_rear s').(Counter.responses) ->
  length (gather_pid_events_B pid acts) = calculate_before11 v ->
  exists s1 s2 acts1 acts2 it,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 /\
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s2 s' acts2 /\
  composed_lts.step_L1 (composed_array_queue L)
  s1 pid it s2 /\
  binds pid (AEnq11) (get_pc s2) /\
  acts = acts1 ++ acts2.
Proof.
  induction 1; intros.
  - subst. simpl in H2.
    unfold before_e11 in Hv.
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
        unfold before_e11 in Hv;
        intuition; subst; try discriminate;
      try (destruct H6 as [t Ht]; subst);
      try (destruct H7 as [t Ht]; subst);
      try (destruct H8 as [t Ht]; subst);
      inversion H1; subst;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_e11;
      destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep Hb]]]]]]]];
      exists s1, s2, acts1, acts2, it; intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto;
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto).
      all : unfold before_e11 in Hv;
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
      unfold before_e11 in Hv; intuition; subst; try discriminate;
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
      unfold before_e11 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      try (destruct H9; subst; discriminate);
      simpl in H4;
      eapply IHvalid_execution_fragment in H3;
      try eapply substitute_eq_binds_v'; eauto; solve_before_e11;
      destruct H3 as [s1 [s2 [acts1 [acts2 [it [Hvalid [Hvalid' [Hstep [Hb Heq]]]]]]]]];
      exists s1, s2;
      eexists;
      exists acts2, it; intuition;
      try (eapply composed_lts.valid_execution_fragment_join'; eauto;
      eapply composed_lts.Step_Internal_Query; eauto;
      eapply composed_lts.Step_None; eauto);
      rewrite Heq; simpl; auto).

      eapply inv_e11_internal_step' in H0.
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
      unfold get_rear in *; simpl in *.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      inversion H10; subst; simpl in *.
      inversion H9; subst; simpl in *.
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
      unfold before_e11 in Hv; intuition; subst; try discriminate;
      try (destruct H7; subst; discriminate);
      try (destruct H8; subst; discriminate);
      try (destruct H9; subst; discriminate);
      simpl in H4;
      eapply IHvalid_execution_fragment in H2;
      try eapply substitute_eq_binds_v'; eauto; solve_before_e11;
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

Lemma inv_before11_least_B_events: forall s s' acts pid,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  forall v,
  before_e11 v ->
  binds pid v (get_pc s) ->
  binds pid (AEnq11) (get_pc s') ->
  length (gather_pid_events_B pid acts) >= calculate_before11 v.
Proof.
  induction 1; intros.
  - subst. unfold before_e11 in H0.
    unfold binds in H2.
    intuition; subst; try (rewrite H1 in H2; discriminate).
    unfold before_e11 in H.
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
      try (eapply substitute_eq_binds_v'; eauto); solve_before_e11;
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
      try (eapply substitute_eq_binds_v'; eauto); solve_before_e11;
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
      try (eapply substitute_eq_binds_v'; eauto); solve_before_e11;
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
Arguments get_vec_rear {L}.

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

Ltac solve_after_e6 :=
  try apply after_e6_Enq10;
  try apply after_e6_Enq11;
  try apply after_e6_Enq12;
  try apply after_e6_Enq13;
  try apply after_e6_Enq14;
  try apply after_e6_Enq15;
  try apply after_e6_Enq26;
  try apply after_e6_Enq27.

Ltac solve_after_e3 :=
  try apply after_e3_Enq4;
  try apply after_e3_Enq5;
  try apply after_e3_Enq6;
  try (unfold after_e6;
  right; right; right;
  solve_after_e6).

Ltac solve_before_e12 :=
  try apply before_e12_Enq1;
  try apply before_e12_Enq2;
  try apply before_e12_Enq3;
  try apply before_e12_Enq4;
  try apply before_e12_Enq5;
  try apply before_e12_Enq6;
  try apply before_e12_Enq10;
  try apply before_e12_Enq11.

Ltac solve_before_e11 :=
  try apply before_e11_Enq1;
  try apply before_e11_Enq2;
  try apply before_e11_Enq3;
  try apply before_e11_Enq4;
  try apply before_e11_Enq5;
  try apply before_e11_Enq6;
  try apply before_e11_Enq10.

Lemma inv_e11_rear_read : forall s pid it s',
  composed_lts.reachable (composed_array_queue L) s ->
  binds pid AEnq11 (get_pc s') ->
  composed_lts.step_L1 (composed_array_queue L) s pid it s' ->
  it = (@Tensor.intL2 li_array li_cnt_cnt (array L) ArrayQueue.front_rear
        (@Tensor.intL2 li_counter li_counter counter counter (int_cnt_read))).
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
  inversion H4; subst; simpl in *.
  (* front_rear *)
  inversion H8; subst; simpl in *.
    inversion H9; subst; simpl in *.
    (* rear *)
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
        eapply internal_preserves_request with (pid:=pid) in Hvalid; simpl in *; eauto.
        3 : {
          apply binds_push_eq.
        }
        discriminate.
                  eapply gather_pid_events_B_gather_pid_external_events.
                  eassumption.
      auto.
    apply valid_execution_fragment_com in Hvalid;
        simpl in Hvalid.
        inversion H6; subst; simpl in *.
        inversion H11; subst; simpl in *.
        inversion H13; subst; simpl in *.
        inversion H12; subst; simpl in *.
        eapply internal_preserves_notin''' with (pid:=pid) in Hvalid; simpl in *; eauto.
        unfold "#" in Hvalid.
        apply binds_in in Hbinds4; intuition.
                  eapply gather_pid_events_B_gather_pid_external_events.
                  eassumption.
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
  tmp noB_preserves_AEnq14 Hvalid st2 pid acts Hgather H1.
  tmp noB_preserves_AEnq28 Hvalid st2 pid acts Hgather H1.
  tmp noB_preserves_AEnq31 Hvalid st2 pid acts Hgather H1.
  tmp noB_preserves_ADeq2 Hvalid st2 pid acts Hgather H1.
  tmp noB_preserves_ADeq5 Hvalid st2 pid acts Hgather H1.
  tmp noB_preserves_ADeq11 Hvalid st2 pid acts Hgather H1.
  tmp noB_preserves_ADeq14 Hvalid st2 pid acts Hgather H1.
  tmp noB_preserves_ADeq28 Hvalid st2 pid acts Hgather H1.
  tmp noB_preserves_ADeq31 Hvalid st2 pid acts Hgather H1.
Qed.

Ltac solve_before_e27 :=
  try apply before_e27_Enq13;
  try apply before_e27_Enq14;
  try apply before_e27_Enq15;
  try apply before_e27_Enq26;
  try (unfold before_e27;
  left;
  solve_before_e13).

Lemma inv_e5_e13_e27: forall s s1 acts1 pid,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 ->
  binds pid (AEnq5) (get_pc s) ->
  forall s' acts2,
  composed_lts.valid_execution_fragment (composed_array_queue L) s1 s' acts2 ->
  binds pid AEnq27 (get_pc s') ->
  length (gather_pid_events_B pid (acts1 ++ acts2)) = calculate_before27 AEnq5 ->
  binds pid AEnq13 (get_pc s1) ->
  length (gather_pid_events_B pid acts1) = calculate_before13 AEnq5.
Proof.
  simpl; intros.
  rewrite gather_pid_events_B_dist in H4.
  rewrite app_length in H4.
  eapply inv_before27_least_B_events in H2; eauto; solve_before_e27.
  simpl in H2.
  eapply inv_before13_least_B_events in H0; eauto; solve_before_e13.
  simpl in H0. lia.
Qed.

Lemma inv_e5_e12_e27: forall s s1 acts1 pid,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 ->
  binds pid (AEnq5) (get_pc s) ->
  forall s' acts2 ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s1 s' acts2 ->
  binds pid AEnq27 (get_pc s') ->
  length (gather_pid_events_B pid (acts1 ++ acts2)) = calculate_before27 AEnq5 ->
  binds pid (AEnq12 ret) (get_pc s1) ->
  length (gather_pid_events_B pid acts1) = calculate_before13 AEnq5.
Proof.
  simpl; intros.
  rewrite gather_pid_events_B_dist in H4.
  rewrite app_length in H4.
  eapply inv_before27_least_B_events in H2; eauto; solve_before_e27.
  simpl in H2.
  eapply inv_before12_least_B_events in H0; eauto; solve_before_e13.
  simpl in H0. lia.
Qed.

Lemma inv_e5_e11_e27: forall s s1 acts1 pid,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 ->
  binds pid (AEnq5) (get_pc s) ->
  forall s' acts2,
  composed_lts.valid_execution_fragment (composed_array_queue L) s1 s' acts2 ->
  binds pid AEnq27 (get_pc s') ->
  length (gather_pid_events_B pid (acts1 ++ acts2)) = calculate_before27 AEnq5 ->
  binds pid (AEnq11) (get_pc s1) ->
  length (gather_pid_events_B pid acts1) = calculate_before11 AEnq5.
Proof.
  simpl; intros.
  rewrite gather_pid_events_B_dist in H4.
  rewrite app_length in H4.
  eapply inv_before27_least_B_events in H2; eauto; solve_before_e27.
  simpl in H2.
  eapply inv_before11_least_B_events in H0; eauto; solve_before_e11.
  simpl in H0. lia.
Qed.

Lemma inv_e5_e11_e12: forall s s1 acts1 pid,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 ->
  binds pid (AEnq5) (get_pc s) ->
  forall s' acts2 ret,
  composed_lts.valid_execution_fragment (composed_array_queue L) s1 s' acts2 ->
  binds pid (AEnq12 ret) (get_pc s') ->
  length (gather_pid_events_B pid (acts1 ++ acts2)) = calculate_before13 AEnq5 ->
  binds pid (AEnq11) (get_pc s1) ->
  length (gather_pid_events_B pid acts1) = calculate_before11 AEnq5.
Proof.
  simpl; intros.
  rewrite gather_pid_events_B_dist in H4.
  rewrite app_length in H4.
  eapply inv_before12_least_B_events in H2; eauto; solve_before_e13.
  simpl in H2.
  eapply inv_before11_least_B_events in H0; eauto; solve_before_e11.
  simpl in H0. lia.
Qed.

Lemma inv_e5_e11_e13: forall s s1 acts1 pid,
  composed_lts.valid_execution_fragment (composed_array_queue L)
    s s1 acts1 ->
  binds pid (AEnq5) (get_pc s) ->
  forall s' acts2,
  composed_lts.valid_execution_fragment (composed_array_queue L) s1 s' acts2 ->
  binds pid (AEnq13) (get_pc s') ->
  length (gather_pid_events_B pid (acts1 ++ acts2)) = calculate_before13 AEnq5 ->
  binds pid (AEnq11) (get_pc s1) ->
  length (gather_pid_events_B pid acts1) = calculate_before11 AEnq5.
Proof.
  simpl; intros.
  rewrite gather_pid_events_B_dist in H4.
  rewrite app_length in H4.
  eapply inv_before13_least_B_events in H2; eauto; solve_before_e13.
  simpl in H2.
  eapply inv_before11_least_B_events in H0; eauto; solve_before_e11.
  simpl in H0. lia.
Qed.

Lemma inv_e5_e27_impl_rear_eq_rear: forall k s pid,
  reachable_len' (composed_array_queue L) s k ->
  binds pid (AEnq5) (get_pc s) ->
  forall s' acts,
    composed_lts.valid_execution_fragment (composed_array_queue L)
      s s' acts ->
    length (gather_pid_events_B pid acts) = calculate_before27 AEnq5 ->
    binds pid AEnq27 (get_pc s') ->
    (get_impl s).(ArrayQueueImpl.rear) pid = (get_rear s).(Counter.value).
Proof.
  intros.
  eapply inv_before13_go_through_13' in H2; eauto; solve_before_e13.
  destruct H2 as [s1 [s2 [acts1 [acts2 [it [Hvalid1 [Hvalid2 [Hstep [Hb Heq]]]]]]]]].
  pose proof H0 as Hreach.
  apply reachable_len_to_reachable in H0.
  apply inv_rear_invariant in H0; auto.
  unfold inv_rear in H0.
  unfold get_impl in *; simpl in *.
  unfold get_rear in *; simpl in *.
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
  eapply inv_impl_rear_keep in Hvalid1; eauto; solve_before_e13; solve_after_e3.
  2 : {
    eapply inv_e5_e13_e27.
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
  assert (Hlen : length (gather_pid_events_B pid acts1) = calculate_before13 AEnq5).
    eapply inv_e5_e12_e27.
    eauto.
    auto.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]).
    eapply composed_lts.Step_Internal_L2; eauto.
    eapply composed_lts.Step_None; eauto.
    eauto. eauto.
    auto.
    eauto. eauto.
  eapply inv_before12_go_through_11' in Hvalid1Tmp; eauto; solve_before_e12.
  destruct Hvalid1Tmp as [s1' [s2' [acts1' [acts2' [it' [Hvalid1' [Hvalid2' [Hint_reply [Hb' Heq']]]]]]]]].
  inversion Hint_reply; subst; simpl in *.
  inversion H8; subst; simpl in *.
  unfold get_pc in *; simpl in *.
  unfold binds in Hb'.
  inversion H9; subst; simpl in *;
  pose proof Hbinds2 as Hbinds2Tmp;
  eapply substitute_eq_binds_v' in Hbinds2; eauto;
  rewrite Hbinds2 in Hb'; try discriminate.
  inversion H7; subst; simpl in *.
  inversion H10; subst; simpl in *.
  inversion H12; subst; simpl in *.
  inversion H11; subst; simpl in *.
  inversion H14; subst; simpl in *.
  inversion H13; subst; simpl in *.
  assert (Hlen' : length (gather_pid_events_B pid acts1') = calculate_before11 AEnq5).
    eapply inv_e5_e11_e12.
    2 : { eauto. }
    eauto.
    eapply composed_lts.valid_execution_fragment_join' with (a':=acts2').
    2 : { eauto. }
    eapply composed_lts.Step_Internal_Reply; eauto.
    eapply composed_lts.Step_None; eauto.
    eauto.
    unfold get_pc; simpl. eauto.
    simpl. auto.
    unfold get_pc; simpl. eauto.
  eapply inv_before11_go_through_internal' in Hvalid1'; eauto; solve_before_e11.
  destruct Hvalid1' as [s1'' [s2'' [acts1'' [acts2'' [it'' [Hvalid1'' [Hvalid2'' [Hstep' [Hb'' Heq'']]]]]]]]].
  assert (Hlen'' : length (gather_pid_events_B pid acts1'') = calculate_before11 AEnq5).
    eapply inv_e5_e11_e12.
    eauto.
    auto.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[] ++ acts2'').
    eapply composed_lts.valid_execution_fragment_join' with (a':=acts2'').
    eapply composed_lts.Step_Internal_L1.
    eauto.
    eapply composed_lts.Step_None; eauto.
    eauto.
    reflexivity.
    eapply composed_lts.Step_Internal_Reply.
    eauto.
    eapply composed_lts.Step_None; eauto.
    simpl. eauto.
    unfold get_pc; simpl; auto.
    eapply substitute_eq_binds_v'; eauto.
    simpl.
    repeat rewrite gather_pid_events_B_dist.
    simpl.
    rewrite Nat.eqb_refl.
    repeat rewrite app_length.
    simpl. simpl in Hlen'.
    rewrite Heq'' in Hlen'.
    rewrite gather_pid_events_B_dist in Hlen'.
    rewrite app_length in Hlen'.
    lia.
    unfold get_pc; simpl; auto.
    inversion Hstep'; subst; simpl in *; auto.
  pose proof Hb'' as Hb''Tmp.
  eapply inv_e11_rear_read in Hb''.
  3 : { eauto. }
  2 : {
    eapply reachable_valid_execution; eauto.
    eapply reachable_len_to_reachable; eauto.
  }
  subst.
  apply REAR_not_decrease in Hvalid1''; auto.
  inversion Hstep'; subst; simpl in *.
  inversion H15; subst; simpl in *.
  inversion H16; subst; simpl in *.
  inversion H18; subst; simpl in *.
  inversion H17; subst; simpl in *.
  inversion H20; subst; simpl in *.
  inversion H19; subst; simpl in *.
  rewrite Hvalid1.
  assert (Htmp : v0 = ret).
  unfold get_pc in *; simpl in *.
  eapply inv_e11_ret_e12_ret.
  eapply composed_lts.valid_execution_fragment_join' with (a:=acts2'').
  eauto.
  eapply composed_lts.Step_Internal_Reply; eauto.
  eauto.
  unfold get_pc; simpl. eauto.
  unfold get_rear; simpl; auto.
  apply binds_push_eq; auto.
  unfold get_pc; simpl; eauto.
  inversion Hb'; subst.
  auto.
  repeat rewrite gather_pid_events_B_dist.
  simpl.
  rewrite Nat.eqb_refl.
  repeat rewrite app_length.
  simpl.
  simpl in Hlen.
  repeat rewrite gather_pid_events_B_dist in Hlen.
  simpl in Hlen.
  rewrite Nat.eqb_refl in Hlen.
  repeat rewrite app_length in Hlen.
  simpl in Hlen.
  simpl in Hlen''. lia.
  subst.
  rewrite Hvalid1 in H2.
  inversion Hb'; subst.
  unfold get_rear in Hvalid1''; simpl in *.
  lia.
Qed.

Lemma inv_e27_from_e5_keeps_vec_rear_impl_rear_eq_rear: forall k s,
  reachable_len' (composed_array_queue L) s k ->
  forall pid,
    binds pid AEnq27 (get_pc s) ->
    exists s1 s2 acts ret n,
      composed_lts.valid_execution_fragment (composed_array_queue L) s2 s acts /\
      composed_lts.step_L1 (composed_array_queue L)
      s1 pid ((@intL1 li_array li_cnt_cnt (array L) ArrayQueue.front_rear int_ary_read)) s2 /\
      binds pid (AEnq5) (get_pc s1) /\
      (length (gather_pid_events_B pid acts)) = 5 /\
      reachable_len' (composed_array_queue L) s1 n /\
      n < k /\
      binds pid (AryReadOk ret) (get_ary s2).(Array.responses L) /\
      (get_xp s) pid = ret /\
      (
        ((get_impl s).(ArrayQueueImpl.x) pid) = get_vec_rear H s pid ->
        get_vec_rear H s pid = get_vec_rear H s2 pid
      ) /\
      (get_impl s1).(ArrayQueueImpl.rear) pid = (get_rear s1).(Counter.value).
Proof.
  intros.
  eapply inv_e27_from_e5_keeps_vec_rear with (H:=H) in H0; eauto.
  destruct H0 as [s1 [s2 [acts [ret [n [Hvalid [Hstep [Hb [Hgather [Hreach [Hlt [Hb' [Hxp Himply]]]]]]]]]]]]].
  exists s1, s2, acts, ret, n. intuition.
  eapply inv_e5_e27_impl_rear_eq_rear with (s:=s1).
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

Lemma inv_e27_from_e5_keeps_vec_rear_impl_rear_eq_rear_k_step: forall k s,
  reachable_len' (composed_array_queue L) s k ->
  forall pid,
    binds pid AEnq27 (get_pc s) ->
    exists s1 s2 acts ret n t,
      valid_execution_fragment_len' (composed_array_queue L) s2 s acts t /\
      composed_lts.step_L1 (composed_array_queue L)
      s1 pid ((@intL1 li_array li_cnt_cnt (array L) ArrayQueue.front_rear int_ary_read)) s2 /\
      binds pid (AEnq5) (get_pc s1) /\
      (length (gather_pid_events_B pid acts)) = 5 /\
      reachable_len' (composed_array_queue L) s1 n /\
      n < k /\
      k = n + 1 + t /\
      binds pid (AryReadOk ret) (get_ary s2).(Array.responses L) /\
      (get_xp s) pid = ret /\
      (
        ((get_impl s).(ArrayQueueImpl.x) pid) = get_vec_rear H s pid ->
        get_vec_rear H s pid = get_vec_rear H s2 pid
      ) /\
      (get_impl s1).(ArrayQueueImpl.rear) pid = (get_rear s1).(Counter.value).
Proof.
  intros.
  eapply inv_e27_from_e5_keeps_vec_rear_k_step with (H:=H) in H0; eauto.
  destruct H0 as [s1 [s2 [acts [ret [n [t [Hvalid [Hstep [Hb [Hgather [Hreach [Hlt [Heq [Hb' [Hxp Himply]]]]]]]]]]]]]]].
  exists s1, s2, acts, ret, n, t. intuition.
  eapply inv_e5_e27_impl_rear_eq_rear with (s:=s1).
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