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
  ArrayQueueInvariant2.
Import ListNotations.

Section test.

Variable L : nat.

Definition after_e6 v :=
  v = AEnq10 \/
  v = AEnq11 \/
  (exists ret, v = AEnq12 ret) \/
  v = AEnq13 \/
  v = AEnq14 \/
  (exists ret, v = AEnq15 ret) \/
  v = AEnq26 \/
  v = AEnq27 \/
  v = AEnq28.

Lemma after_e6_Enq12: forall ret,
  after_e6 (AEnq12 ret).
Proof.
  intros.
  unfold after_e6.
  right. right. left.
  exists ret.
  reflexivity.
Qed.

Lemma after_e6_Enq15: forall ret,
  after_e6 (AEnq15 ret).
Proof.
  intros.
  unfold after_e6.
  right. right. right. right. right. left.
  exists ret.
  reflexivity.
Qed.

Lemma after_e6_Enq26:
  after_e6 (AEnq26).
Proof.
  intros.
  unfold after_e6.
  intuition.
Qed.

Lemma after_e6_Enq10:
  after_e6 (AEnq10).
Proof.
  intros.
  unfold after_e6.
  intuition.
Qed.

Lemma after_e6_Enq13:
  after_e6 (AEnq13).
Proof.
  intros.
  unfold after_e6.
  intuition.
Qed.

Lemma after_e6_Enq27:
  after_e6 (AEnq27).
Proof.
  intros.
  unfold after_e6.
  intuition.
Qed.

Lemma after_e6_Enq11:
  after_e6 (AEnq11).
Proof.
  intros.
  unfold after_e6.
  intuition.
Qed.

Lemma after_e6_Enq14:
  after_e6 (AEnq14).
Proof.
  intros.
  unfold after_e6.
  intuition.
Qed.

Lemma after_e6_Enq28:
  after_e6 (AEnq28).
Proof.
  intros.
  unfold after_e6.
  intuition.
Qed.

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

Arguments get_pc {L}.

Definition calculate_events v :=
  match v with
  | AEnq1 => 0
  | AEnq2 => 0
  | AEnq3 ret => 0
  | AEnq4 => 0
  | AEnq5  => 0
  | AEnq6 ret => 0
  | AEnq10 => 0
  | AEnq11 => 1
  | AEnq12 ret => 2
  | AEnq13 => 2
  | AEnq14 => 3
  | AEnq15 ret => 4
  | AEnq26 => 4
  | AEnq27 => 4
  | AEnq28 => 5
  | AEnq29 ret => 6
  | AEnq30 => 6
  | AEnq31 => 7
  | AEnq32 => 8
  | _ => 0
  end.

Lemma inv_e27_from_e6_ret : forall k (s : composed_lts.state (composed_array_queue L)),
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
  let rearp := aqimpl.(ArrayQueueImpl.rear) in
  let xp := aqimpl.(ArrayQueueImpl.x) in
    reachable_len' (composed_array_queue L) s k ->
  forall pid v,
    after_e6 v ->
    binds pid v pc ->
    exists s' acts ret n,
      composed_lts.valid_execution_fragment (composed_array_queue L) s' s acts /\
      binds pid (AEnq6 ret) (get_pc s') /\
      length (gather_pid_events_B pid acts) = calculate_events v /\
      reachable_len' (composed_array_queue L) s' n /\
      n < k.
Proof.
  induction k; intros.
  - unfold reachable_len' in H.
    destruct H as [init [acts [Hnew Hvalid]]].
    inversion Hvalid; subst.
    inversion Hnew; subst.
    inversion H2; subst.
    inversion H3; subst.
    unfold pc in H1.
    unfold aqimpl in H1.
    unfold sync_aqimpl in H1.
    rewrite H6 in H1.
    unfold new_array_queue in H1.
    simpl in H1.
    unfold after_e6 in H0.
    intuition; subst; inversion H1.
  - apply reachable_len_reconstruct in H.
    destruct H as [st [acts [Hreach Hstep]]].
    inversion Hstep; subst; clear Hstep.
    -- inversion H4; subst; clear H4.
      eapply IHk with (pid:=pid) in Hreach; eauto.
      destruct Hreach as [s' [acts [ret [n [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]].
      exists s', acts, ret, n.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto.
      eapply composed_lts.Step_Internal_L1; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite app_nil_r; auto.
      inversion H2; subst.
      inversion H; subst; simpl in *.
      unfold pc in H1.
      unfold aqimpl in H1.
      unfold sync_aqimpl in H1.
      assumption.
    -- inversion H4; subst; clear H4.
      inversion H2; subst; simpl in *.
      inversion H; subst; simpl in *.
      unfold pc in H1.
      unfold aqimpl in H1.
      inversion H3; subst; simpl in *.
      all : try (assert (Htmp : pid0 <> pid) by
      (intro Heq; subst;
      eapply substitute_eq_binds_v' in Hbinds0; eauto;
      unfold binds in Hbinds0;
      rewrite H1 in Hbinds0;
      unfold after_e6 in H0;
      intuition; subst; try discriminate;
      try (destruct H; subst; discriminate);
      try (destruct H0; subst; discriminate);
      try (destruct H4; subst; discriminate);
      try (destruct H5; subst; discriminate));
      apply substitute_neq_preserves_binds' in H1; auto;
      eapply IHk in Hreach; eauto;
      destruct Hreach as [s' [acts [ret' [n [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]];
      exists s', acts, ret', n;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto;
      try (rewrite app_nil_r; auto);
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto).

      destruct (eq_nat_dec pid0 pid).
        subst.
        eexists.
        exists [].
        exists ret.
        exists k. intuition; unfold get_pc; simpl; eauto.
        eapply composed_lts.Step_Internal_L2; eauto.
        eapply composed_lts.Step_None; eauto.
        simpl. auto.
        unfold after_e6 in H0.
        unfold binds in H1.
        eapply substitute_eq_binds_v' in Hbinds0.
        rewrite Hbinds0 in H1.
        intuition; subst; try discriminate.
        simpl. reflexivity.
        destruct H6 as [r' Hr']; subst; discriminate.
        destruct H0 as [r' Hr']; subst; discriminate.
      apply substitute_neq_preserves_binds' in H1; auto.
      eapply IHk in Hreach; eauto;
      destruct Hreach as [s' [acts [ret' [n' [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]];
      exists s', acts, ret', n';
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto;
      try (rewrite app_nil_r; auto);
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto.

      destruct (eq_nat_dec pid0 pid).
        subst.
        eapply IHk with (pid:=pid) in Hreach; simpl.
        destruct Hreach as [s' [acts [ret' [n [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]];
        exists s', acts, ret', n;
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto;
        try (rewrite app_nil_r; auto);
        eapply composed_lts.Step_Internal_L2; eauto;
        eapply composed_lts.Step_None; eauto.
        3 : {
          eauto.
        }
        2 : {
          solve_after_e6.
        }
        rewrite Hgather.
        unfold after_e6 in H0.
        unfold binds in H1.
        eapply substitute_eq_binds_v' in Hbinds0.
        rewrite Hbinds0 in H1.
        intuition; subst; try discriminate.
        destruct H6 as [r' Hr']; subst; discriminate.
        simpl. reflexivity.
        destruct H0 as [r' Hr']; subst; discriminate.

      apply substitute_neq_preserves_binds' in H1; auto;
      eapply IHk in Hreach; eauto;
      destruct Hreach as [s' [acts [ret' [n' [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]];
      exists s', acts, ret', n';
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto;
      try (rewrite app_nil_r; auto);
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto.

      destruct (eq_nat_dec pid0 pid).
        subst.
        eapply IHk with (pid:=pid) in Hreach; simpl.
        destruct Hreach as [s' [acts [ret' [n [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]];
        exists s', acts, ret', n;
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto;
        try (rewrite app_nil_r; auto);
        eapply composed_lts.Step_Internal_L2; eauto;
        eapply composed_lts.Step_None; eauto.
        3 : {
          eauto.
        }
        2 : {
          solve_after_e6.
        }
        rewrite Hgather.
        unfold after_e6 in H0.
        unfold binds in H1.
        eapply substitute_eq_binds_v' in Hbinds0.
        rewrite Hbinds0 in H1.
        intuition; subst; try discriminate.
        destruct H7 as [r' Hr']; subst; discriminate.
        destruct H0 as [r' Hr']; subst; discriminate.
        simpl. reflexivity.

      apply substitute_neq_preserves_binds' in H1; auto;
      eapply IHk in Hreach; eauto;
      destruct Hreach as [s' [acts [ret' [n' [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]];
      exists s', acts, ret', n';
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto;
      try (rewrite app_nil_r; auto);
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto.

      destruct (eq_nat_dec pid0 pid).
        subst.
        eapply IHk with (pid:=pid) in Hreach; simpl.
        destruct Hreach as [s' [acts [ret' [n [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]];
        exists s', acts, ret', n;
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto;
        try (rewrite app_nil_r; auto);
        eapply composed_lts.Step_Internal_L2; eauto;
        eapply composed_lts.Step_None; eauto.
        3 : {
          eauto.
        }
        2 : {
          solve_after_e6.
        }
        rewrite Hgather.
        unfold after_e6 in H0.
        unfold binds in H1.
        eapply substitute_eq_binds_v' in Hbinds0.
        rewrite Hbinds0 in H1.
        intuition; subst; try discriminate.
        destruct H7 as [r' Hr']; subst; discriminate.
        destruct H0 as [r' Hr']; subst; discriminate.
        simpl. reflexivity.

      apply substitute_neq_preserves_binds' in H1; auto;
      eapply IHk in Hreach; eauto;
      destruct Hreach as [s' [acts [ret' [n' [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]];
      exists s', acts, ret', n';
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto;
      try (rewrite app_nil_r; auto);
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto.
  -- inversion H2.
  -- inversion H2.
  -- inversion H4; subst. clear H4.
    inversion H2; subst; simpl in *.
    inversion H; subst; simpl in *.
    unfold pc in H1.
    unfold aqimpl in H1.
    unfold sync_aqimpl in H1.
      destruct (eq_nat_dec pid0 pid).
        subst.
      inversion H3; subst; simpl in *;
      apply binds_push_eq_inv in H1; auto;
      subst; unfold after_e6 in H0;
      intuition; try discriminate;
      try (destruct H1; subst; discriminate);
      try (destruct H0; subst; discriminate);
      try (destruct H4; subst; discriminate);
      try (destruct H5; subst; discriminate).

      eapply IHk with (pid:=pid) in Hreach; eauto.
      destruct Hreach as [s' [acts [ret' [n' [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]];
      exists s'.
      eexists.
      exists ret', n';
      intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto.
      try (rewrite app_nil_r; auto).
      eapply composed_lts.Step_Initial_Call; eauto;
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      assert (Htmp : pid <> pid0)
      by (intro; subst;
      inversion H3; subst; simpl in *;
      apply binds_push_eq_inv in H1; auto;
      subst; unfold after_e6 in H0;
      intuition; try discriminate;
      try (destruct H1; subst; discriminate);
      try (destruct H0; subst; discriminate);
      try (destruct H4; subst; discriminate);
      try (destruct H5; subst; discriminate)).
      apply Nat.eqb_neq in Htmp; rewrite Htmp.
      rewrite app_nil_r; auto.
      simpl.
      inversion H3; subst; simpl in *;
      apply binds_push_neq_inv in H1; auto.
  -- inversion H4; subst. clear H4.
    inversion H2; subst; simpl in *.
    inversion H; subst; simpl in *.
    unfold pc in H1.
    unfold aqimpl in H1.
    unfold sync_aqimpl in H1.
      destruct (eq_nat_dec pid0 pid).
        subst.
      inversion H3; subst; simpl in *;
      assert (Htmp : pid # (remove pc0 pid))
      by (apply ok_remove_notin; auto);
      apply notin_get_none in Htmp;
      rewrite H1 in Htmp; discriminate.

      eapply IHk with (pid:=pid) in Hreach; eauto.
      destruct Hreach as [s' [acts [ret' [n' [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]];
      exists s'.
      eexists.
      exists ret', n';
      intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto.
      try (rewrite app_nil_r; auto).
      eapply composed_lts.Step_Final_Return; eauto;
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      
      assert (Htmp' : pid <> pid0) by auto.
      apply Nat.eqb_neq in Htmp'; rewrite Htmp'.
      rewrite app_nil_r; auto.
      simpl.
      inversion H3; subst; simpl in *;
      unfold binds in H1;
      rewrite remove_neq_preserves_get in H1; auto.
  -- inversion H4; subst. clear H4.
    inversion H2; subst; simpl in *.
    inversion H; subst; simpl in *.
    unfold pc in H1.
    unfold aqimpl in H1.
    unfold sync_aqimpl in H1.
      destruct (eq_nat_dec pid0 pid).
        subst.
      inversion H4; subst; simpl in *.
      all : try pose proof Hbinds0 as HbindsTmp.

      all : try
      (eapply substitute_eq_binds_v' in Hbinds0; eauto;
      unfold binds in Hbinds0;
      rewrite H1 in Hbinds0;
      unfold after_e6 in H0;
      intuition; subst; try discriminate;
      try (destruct H; subst; discriminate);
      try (destruct H0; subst; discriminate);
      try (destruct H4; subst; discriminate);
      try (destruct H5; subst; discriminate)).

      eapply IHk with (pid:=pid) in Hreach; eauto; solve_after_e6.
      destruct Hreach as [s' [acts [ret' [n' [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]];
      exists s'.
      eexists.
      exists ret', n';
      intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto;
      try (rewrite app_nil_r; auto).
      eapply composed_lts.Step_Internal_Query; eauto;
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist;
      simpl; rewrite Nat.eqb_refl;
      rewrite app_length;
      rewrite Hgather;
      simpl; reflexivity.

      eapply IHk with (pid:=pid) in Hreach; eauto; solve_after_e6.
      destruct Hreach as [s' [acts [ret' [n' [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]];
      exists s'.
      eexists.
      exists ret', n';
      intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto;
      try (rewrite app_nil_r; auto).
      eapply composed_lts.Step_Internal_Query; eauto;
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist;
      simpl; rewrite Nat.eqb_refl;
      rewrite app_length;
      rewrite Hgather;
      simpl; reflexivity.

      eapply IHk with (pid:=pid) in Hreach; eauto; solve_after_e6.
      destruct Hreach as [s' [acts [ret' [n' [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]];
      exists s'.
      eexists.
      exists ret', n';
      intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto;
      try (rewrite app_nil_r; auto).
      eapply composed_lts.Step_Internal_Query; eauto;
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist;
      simpl; rewrite Nat.eqb_refl;
      rewrite app_length;
      rewrite Hgather;
      simpl; reflexivity.

      eapply IHk with (pid:=pid) in Hreach; eauto; solve_after_e6.
      destruct Hreach as [s' [acts [ret' [n' [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]];
      exists s'.
      eexists.
      exists ret', n';
      intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto;
      try (rewrite app_nil_r; auto).
      eapply composed_lts.Step_Internal_Query; eauto;
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      assert (Htmp : pid <> pid0) by auto.
      apply Nat.eqb_neq in Htmp.
      rewrite Htmp.
      rewrite app_nil_r; auto.
      simpl.
      inversion H4; subst; simpl in *;
      eapply substitute_neq_preserves_binds' in H1; eauto.
  -- inversion H4; subst. clear H4.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    unfold pc in H1.
    unfold aqimpl in H1.
    unfold sync_aqimpl in H1.
      destruct (eq_nat_dec pid0 pid).
        subst.
      inversion H4; subst; simpl in *.
      all : try pose proof Hbinds0 as HbindsTmp.
      all : try
      (eapply substitute_eq_binds_v' in Hbinds0; eauto;
      unfold binds in Hbinds0;
      rewrite H1 in Hbinds0;
      unfold after_e6 in H0;
      intuition; subst; try discriminate;
      try (destruct H; subst; discriminate);
      try (destruct H0; subst; discriminate);
      try (destruct H4; subst; discriminate);
      try (destruct H5; subst; discriminate)).
      eapply IHk with (pid:=pid) in Hreach; eauto; solve_after_e6.
      destruct Hreach as [s' [acts [ret' [n' [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]];
      exists s'.
      eexists.
      exists ret', n';
      intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto;
      try (rewrite app_nil_r; auto).
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist.
      simpl; rewrite Nat.eqb_refl.
      rewrite app_length.
      rewrite Hgather.
      destruct H5; subst.
      simpl. reflexivity.
      
      eapply IHk with (pid:=pid) in Hreach; eauto; solve_after_e6.
      destruct Hreach as [s' [acts [ret' [n' [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]];
      exists s'.
      eexists.
      exists ret', n';
      intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto;
      try (rewrite app_nil_r; auto).
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist.
      simpl; rewrite Nat.eqb_refl.
      rewrite app_length.
      rewrite Hgather.
      destruct H0; subst.
      simpl. reflexivity.
      eapply IHk with (pid:=pid) in Hreach.
      destruct Hreach as [s' [acts [ret' [n' [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]];
      exists s'.
      eexists.
      exists ret', n';
      intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto;
      try (rewrite app_nil_r; auto).
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist;
      simpl.
      assert (Htmp : pid <> pid0) by auto;
      apply Nat.eqb_neq in Htmp; rewrite Htmp.
      rewrite app_nil_r; auto.
      eauto.
      eauto.
      inversion H4; subst; simpl in *;
      apply substitute_neq_preserves_binds' in H1; auto.
Qed.

Lemma inv_e27_from_e6_ret_k_step : forall k (s : composed_lts.state (composed_array_queue L)),
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
  let rearp := aqimpl.(ArrayQueueImpl.rear) in
  let xp := aqimpl.(ArrayQueueImpl.x) in
    reachable_len' (composed_array_queue L) s k ->
  forall pid v,
    after_e6 v ->
    binds pid v pc ->
    exists s' acts ret n t,
      valid_execution_fragment_len' (composed_array_queue L) s' s acts t /\
      binds pid (AEnq6 ret) (get_pc s') /\
      length (gather_pid_events_B pid acts) = calculate_events v /\
      reachable_len' (composed_array_queue L) s' n /\
      n < k /\
      k = n + t.
Proof.
  induction k; intros.
  - unfold reachable_len' in H.
    destruct H as [init [acts [Hnew Hvalid]]].
    inversion Hvalid; subst.
    inversion Hnew; subst.
    inversion H2; subst.
    inversion H3; subst.
    unfold pc in H1.
    unfold aqimpl in H1.
    unfold sync_aqimpl in H1.
    rewrite H6 in H1.
    unfold new_array_queue in H1.
    simpl in H1.
    unfold after_e6 in H0.
    intuition; subst; inversion H1.
  - apply reachable_len_reconstruct in H.
    destruct H as [st [acts [Hreach Hstep]]].
    inversion Hstep; subst; clear Hstep.
    -- inversion H4; subst; clear H4.
      eapply IHk with (pid:=pid) in Hreach; eauto.
      destruct Hreach as [s' [acts [ret [n [t [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]]].
      exists s', (acts ++ []), ret, n, (t + 1).
      intuition.
      eapply valid_execution_fragment_len'_join' with (a:=acts) (a':=[]) (n:=t) (n':=1); eauto.
      eapply Step_Internal_L1_len'; eauto.
      eapply Step_None_len'; eauto.
      rewrite app_nil_r; auto.
      subst. lia.
      inversion H2; subst.
      inversion H; subst; simpl in *.
      unfold pc in H1.
      unfold aqimpl in H1.
      unfold sync_aqimpl in H1.
      assumption.
    -- inversion H4; subst; clear H4.
      inversion H2; subst; simpl in *.
      inversion H; subst; simpl in *.
      unfold pc in H1.
      unfold aqimpl in H1.
      inversion H3; subst; simpl in *.

      all : try (assert (Htmp : pid0 <> pid) by
      (intro Heq; subst;
      eapply substitute_eq_binds_v' in Hbinds0; eauto;
      unfold binds in Hbinds0;
      rewrite H1 in Hbinds0;
      unfold after_e6 in H0;
      intuition; subst; try discriminate;
      try (destruct H; subst; discriminate);
      try (destruct H0; subst; discriminate);
      try (destruct H4; subst; discriminate);
      try (destruct H5; subst; discriminate));
      apply substitute_neq_preserves_binds' in H1; auto;
      eapply IHk in Hreach; eauto;
      destruct Hreach as [s' [acts [ret' [n [t [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]]];

      exists s', (acts ++ []), ret', n, (t + 1);
      intuition;

      try (eapply valid_execution_fragment_len'_join' with (a:=acts) (a':=[]) (n:=t) (n':=1); eauto);
      try (rewrite app_nil_r; auto);
      try (subst; lia);
      eapply Step_Internal_L2_len'; eauto;
      eapply Step_None_len'; eauto).

      destruct (eq_nat_dec pid0 pid).
        subst.
        eexists.
        exists [].
        exists ret.
        exists k.
        exists 1. intuition; unfold get_pc; simpl; eauto.
        eapply Step_Internal_L2_len'; eauto.
        eapply Step_None_len'; eauto.
        simpl. auto.
        unfold after_e6 in H0.
        unfold binds in H1.
        eapply substitute_eq_binds_v' in Hbinds0.
        rewrite Hbinds0 in H1.
        intuition; subst; try discriminate.
        simpl. reflexivity.
        destruct H6 as [r' Hr']; subst; discriminate.
        destruct H0 as [r' Hr']; subst; discriminate.
        lia.
      apply substitute_neq_preserves_binds' in H1; auto.

      eapply IHk in Hreach; eauto;
      destruct Hreach as [s' [acts [ret' [n' [t [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]]];
      exists s', (acts ++ []), ret', n', (t + 1);
      intuition;
      try (eapply valid_execution_fragment_len'_join' with (a:=acts) (a':=[]) (n:=t) (n':=1); eauto);
      try (rewrite app_nil_r; auto);
      try (subst; lia);
      eapply Step_Internal_L2_len'; eauto;
      eapply Step_None_len'; eauto.

      destruct (eq_nat_dec pid0 pid).
        subst.
        eapply IHk with (pid:=pid) in Hreach; simpl.
      destruct Hreach as [s' [acts [ret' [n' [t [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]]];
      exists s', (acts ++ []), ret', n', (t + 1);
      intuition.
      eapply valid_execution_fragment_len'_join' with (a:=acts) (a':=[]) (n:=t) (n':=1); eauto;
        try (rewrite app_nil_r; auto);
        eapply Step_Internal_L2_len'; eauto;
        eapply Step_None_len'; eauto.
        4 : {
          eauto.
        }
        3 : {
          solve_after_e6.
        }
        rewrite app_nil_r.
        rewrite Hgather.
        unfold after_e6 in H0.
        unfold binds in H1.
        eapply substitute_eq_binds_v' in Hbinds0.
        rewrite Hbinds0 in H1.
        intuition; subst; try discriminate.
        destruct H8 as [r' Hr']; subst; discriminate.
        simpl. reflexivity.
        destruct H0 as [r' Hr']; subst; discriminate.
        subst. lia.

      apply substitute_neq_preserves_binds' in H1; auto;
      eapply IHk in Hreach; eauto;
      destruct Hreach as [s' [acts [ret' [n' [t [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]]];
      exists s', (acts ++ []), ret', n', (t + 1);
      intuition;
      try (eapply valid_execution_fragment_len'_join' with (a:=acts) (a':=[]) (n:=t) (n':=1); eauto);
      try (rewrite app_nil_r; auto);
      try (subst; lia);
      eapply Step_Internal_L2_len'; eauto;
      eapply Step_None_len'; eauto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        eapply IHk with (pid:=pid) in Hreach; simpl.
      destruct Hreach as [s' [acts [ret' [n' [t [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]]];
      exists s', (acts ++ []), ret', n', (t + 1);
        intuition.
      eapply valid_execution_fragment_len'_join' with (a:=acts) (a':=[]) (n:=t) (n':=1); eauto;
        try (rewrite app_nil_r; auto);
        eapply Step_Internal_L2_len'; eauto;
        eapply Step_None_len'; eauto.
        4 : {
          eauto.
        }
        3 : {
          solve_after_e6.
        }
        rewrite app_nil_r.
        rewrite Hgather.
        unfold after_e6 in H0.
        unfold binds in H1.
        eapply substitute_eq_binds_v' in Hbinds0.
        rewrite Hbinds0 in H1.
        intuition; subst; try discriminate.
        destruct H9 as [r' Hr']; subst; discriminate.
        destruct H0 as [r' Hr']; subst; discriminate.
        simpl. reflexivity.
        subst. lia.
      apply substitute_neq_preserves_binds' in H1; auto;
      eapply IHk in Hreach; eauto;
      destruct Hreach as [s' [acts [ret' [n' [t [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]]];
      exists s', (acts ++ []), ret', n', (t + 1);
      intuition;
      try (eapply valid_execution_fragment_len'_join' with (a:=acts) (a':=[]) (n:=t) (n':=1); eauto);
      try (rewrite app_nil_r; auto);
      try (subst; lia);
      eapply Step_Internal_L2_len'; eauto;
      eapply Step_None_len'; eauto.
      destruct (eq_nat_dec pid0 pid).
        subst.
        eapply IHk with (pid:=pid) in Hreach; simpl.
      destruct Hreach as [s' [acts [ret' [n' [t [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]]];
      exists s', (acts ++ []), ret', n', (t + 1);
        intuition.
      eapply valid_execution_fragment_len'_join' with (a:=acts) (a':=[]) (n:=t) (n':=1); eauto;
        try (rewrite app_nil_r; auto);
        eapply Step_Internal_L2_len'; eauto;
        eapply Step_None_len'; eauto.
        4 : {
          eauto.
        }
        3 : {
          solve_after_e6.
        }
        rewrite app_nil_r.
        rewrite Hgather.
        unfold after_e6 in H0.
        unfold binds in H1.
        eapply substitute_eq_binds_v' in Hbinds0.
        rewrite Hbinds0 in H1.
        intuition; subst; try discriminate.
        destruct H9 as [r' Hr']; subst; discriminate.
        destruct H0 as [r' Hr']; subst; discriminate.
        simpl. reflexivity.
        subst. lia.
      apply substitute_neq_preserves_binds' in H1; auto;
      eapply IHk in Hreach; eauto;
      destruct Hreach as [s' [acts [ret' [n' [t [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]]];
      exists s', (acts ++ []), ret', n', (t + 1);
      intuition;
      try (eapply valid_execution_fragment_len'_join' with (a:=acts) (a':=[]) (n:=t) (n':=1); eauto);
      try (rewrite app_nil_r; auto);
      try (subst; lia);
      eapply Step_Internal_L2_len'; eauto;
      eapply Step_None_len'; eauto.
  -- inversion H2.
  -- inversion H2.
  -- inversion H4; subst. clear H4.
    inversion H2; subst; simpl in *.
    inversion H; subst; simpl in *.
    unfold pc in H1.
    unfold aqimpl in H1.
    unfold sync_aqimpl in H1.
      destruct (eq_nat_dec pid0 pid).
        subst.
      inversion H3; subst; simpl in *;
      apply binds_push_eq_inv in H1; auto;
      subst; unfold after_e6 in H0;
      intuition; try discriminate;
      try (destruct H1; subst; discriminate);
      try (destruct H0; subst; discriminate);
      try (destruct H4; subst; discriminate);
      try (destruct H5; subst; discriminate).

      eapply IHk with (pid:=pid) in Hreach; eauto.
      destruct Hreach as [s' [acts [ret' [n' [t [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]]];
      (* destruct Hreach as [s' [acts [ret' [n' [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]]; *)
      exists s'.
      eexists.
      exists ret', n', (t + 1);
      intuition.
      eapply valid_execution_fragment_len'_join'; eauto.
      try (rewrite app_nil_r; auto).
      eapply Step_Initial_Call_len'; eauto;
      eapply Step_None_len'; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      assert (Htmp : pid <> pid0)
      by (intro; subst;
      inversion H3; subst; simpl in *;
      apply binds_push_eq_inv in H1; auto;
      subst; unfold after_e6 in H0;
      intuition; try discriminate;
      try (destruct H1; subst; discriminate);
      try (destruct H0; subst; discriminate);
      try (destruct H4; subst; discriminate);
      try (destruct H5; subst; discriminate)).
      apply Nat.eqb_neq in Htmp; rewrite Htmp.
      rewrite app_nil_r; auto.
      subst; lia.
      simpl.
      inversion H3; subst; simpl in *;
      apply binds_push_neq_inv in H1; auto.
  -- inversion H4; subst. clear H4.
    inversion H2; subst; simpl in *.
    inversion H; subst; simpl in *.
    unfold pc in H1.
    unfold aqimpl in H1.
    unfold sync_aqimpl in H1.
      destruct (eq_nat_dec pid0 pid).
        subst.
      inversion H3; subst; simpl in *;
      assert (Htmp : pid # (remove pc0 pid))
      by (apply ok_remove_notin; auto);
      apply notin_get_none in Htmp;
      rewrite H1 in Htmp; discriminate.

      eapply IHk with (pid:=pid) in Hreach; eauto.
      destruct Hreach as [s' [acts [ret' [n' [t [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]]];
      exists s'.
      eexists.
      exists ret', n', (t + 1);
      intuition.
      eapply valid_execution_fragment_len'_join'; eauto.
      try (rewrite app_nil_r; auto).
      eapply Step_Final_Return_len'; eauto;
      eapply Step_None_len'; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      
      assert (Htmp' : pid <> pid0) by auto.
      apply Nat.eqb_neq in Htmp'; rewrite Htmp'.
      rewrite app_nil_r; auto.
      subst; lia.
      simpl.
      inversion H3; subst; simpl in *;
      unfold binds in H1;
      rewrite remove_neq_preserves_get in H1; auto.
  -- inversion H4; subst. clear H4.
    inversion H2; subst; simpl in *.
    inversion H; subst; simpl in *.
    unfold pc in H1.
    unfold aqimpl in H1.
    unfold sync_aqimpl in H1.
      destruct (eq_nat_dec pid0 pid).
        subst.
      inversion H4; subst; simpl in *.
      all : try pose proof Hbinds0 as HbindsTmp.

      all : try
      (eapply substitute_eq_binds_v' in Hbinds0; eauto;
      unfold binds in Hbinds0;
      rewrite H1 in Hbinds0;
      unfold after_e6 in H0;
      intuition; subst; try discriminate;
      try (destruct H; subst; discriminate);
      try (destruct H0; subst; discriminate);
      try (destruct H4; subst; discriminate);
      try (destruct H5; subst; discriminate)).

      eapply IHk with (pid:=pid) in Hreach; eauto; solve_after_e6.
      destruct Hreach as [s' [acts [ret' [n' [t [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]]];
      exists s'.
      eexists.
      exists ret', n', (t + 1);
      intuition.
      eapply valid_execution_fragment_len'_join'; eauto;
      try (rewrite app_nil_r; auto).
      eapply Step_Internal_Query_len'; eauto;
      eapply Step_None_len'; eauto.
      rewrite gather_pid_events_B_dist;
      simpl; rewrite Nat.eqb_refl;
      rewrite app_length;
      rewrite Hgather;
      simpl; reflexivity.
      subst; lia.

      eapply IHk with (pid:=pid) in Hreach; eauto; solve_after_e6.
      destruct Hreach as [s' [acts [ret' [n' [t [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]]];
      exists s'.
      eexists.
      exists ret', n', (t + 1);
      intuition.
      eapply valid_execution_fragment_len'_join'; eauto;
      try (rewrite app_nil_r; auto).
      eapply Step_Internal_Query_len'; eauto;
      eapply Step_None_len'; eauto.
      rewrite gather_pid_events_B_dist;
      simpl; rewrite Nat.eqb_refl;
      rewrite app_length;
      rewrite Hgather;
      simpl; reflexivity.
      subst; lia.

      eapply IHk with (pid:=pid) in Hreach; eauto; solve_after_e6.
      destruct Hreach as [s' [acts [ret' [n' [t [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]]];
      exists s'.
      eexists.
      exists ret', n', (t + 1);
      intuition.
      eapply valid_execution_fragment_len'_join'; eauto;
      try (rewrite app_nil_r; auto).
      eapply Step_Internal_Query_len'; eauto;
      eapply Step_None_len'; eauto.
      rewrite gather_pid_events_B_dist;
      simpl; rewrite Nat.eqb_refl;
      rewrite app_length;
      rewrite Hgather;
      simpl; reflexivity.
      subst; lia.

      eapply IHk with (pid:=pid) in Hreach; eauto; solve_after_e6.
      destruct Hreach as [s' [acts [ret' [n' [t [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]]];
      exists s'.
      eexists.
      exists ret', n', (t + 1);
      intuition.
      eapply valid_execution_fragment_len'_join'; eauto;
      try (rewrite app_nil_r; auto).
      eapply Step_Internal_Query_len'; eauto;
      eapply Step_None_len'; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      assert (Htmp : pid <> pid0) by auto.
      apply Nat.eqb_neq in Htmp.
      rewrite Htmp.
      rewrite app_nil_r; auto.
      simpl.
      subst; lia.
      inversion H4; subst; simpl in *;
      eapply substitute_neq_preserves_binds' in H1; eauto.
  -- inversion H4; subst. clear H4.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    unfold pc in H1.
    unfold aqimpl in H1.
    unfold sync_aqimpl in H1.
      destruct (eq_nat_dec pid0 pid).
        subst.
      inversion H4; subst; simpl in *.
      all : try pose proof Hbinds0 as HbindsTmp.
      all : try
      (eapply substitute_eq_binds_v' in Hbinds0; eauto;
      unfold binds in Hbinds0;
      rewrite H1 in Hbinds0;
      unfold after_e6 in H0;
      intuition; subst; try discriminate;
      try (destruct H; subst; discriminate);
      try (destruct H0; subst; discriminate);
      try (destruct H4; subst; discriminate);
      try (destruct H5; subst; discriminate)).
      eapply IHk with (pid:=pid) in Hreach; eauto; solve_after_e6.
      destruct Hreach as [s' [acts [ret' [n' [t [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]]];
      exists s'.
      eexists.
      exists ret', n', (t + 1);
      intuition.
      eapply valid_execution_fragment_len'_join'; eauto;
      try (rewrite app_nil_r; auto).
      eapply Step_Internal_Reply_len'; eauto;
      eapply Step_None_len'; eauto.
      rewrite gather_pid_events_B_dist.
      simpl; rewrite Nat.eqb_refl.
      rewrite app_length.
      rewrite Hgather.
      destruct H5; subst.
      simpl. reflexivity.
      subst; lia.

      eapply IHk with (pid:=pid) in Hreach; eauto; solve_after_e6.
      destruct Hreach as [s' [acts [ret' [n' [t [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]]];
      exists s'.
      eexists.
      exists ret', n', (t + 1);
      intuition.
      eapply valid_execution_fragment_len'_join'; eauto;
      try (rewrite app_nil_r; auto).
      eapply Step_Internal_Reply_len'; eauto;
      eapply Step_None_len'; eauto.
      rewrite gather_pid_events_B_dist.
      simpl; rewrite Nat.eqb_refl.
      rewrite app_length.
      rewrite Hgather.
      destruct H0; subst.
      simpl. reflexivity.
      subst; lia.

      eapply IHk with (pid:=pid) in Hreach.
      destruct Hreach as [s' [acts [ret' [n' [t [Hvalid [Hb [Hgather [Hr Hlt]]]]]]]]];
      exists s'.
      eexists.
      exists ret', n', (t + 1);
      intuition.
      eapply valid_execution_fragment_len'_join'; eauto;
      try (rewrite app_nil_r; auto).
      eapply Step_Internal_Reply_len'; eauto;
      eapply Step_None_len'; eauto.
      rewrite gather_pid_events_B_dist;
      simpl.
      assert (Htmp : pid <> pid0) by auto;
      apply Nat.eqb_neq in Htmp; rewrite Htmp.
      rewrite app_nil_r; auto.
      eauto.
      subst; lia.
      eauto.
      inversion H4; subst; simpl in *;
      apply substitute_neq_preserves_binds' in H1; auto.
Qed.

Definition has_read_ary v pid pc res_ary ret :=
    (binds pid v pc /\
      binds pid (AryReadOk ret) res_ary /\ v = AEnq5) \/
    (binds pid v pc /\ v = AEnq6 ret).

Local Lemma substitute_neq_preserves_has_read_ary_inv : forall pid pc res_ary ret pid' v p,
  has_read_ary p pid (substitute pc pid' v) res_ary ret ->
  pid <> pid' ->
  has_read_ary p pid pc res_ary ret.
Proof.
  unfold has_read_ary.
  intros. intuition; subst.
  - apply substitute_neq_preserves_binds' in H; intuition.
  - apply substitute_neq_preserves_binds' in H; intuition.
Qed.

Definition calculate_inv_e6_ret_e5_internal_step e :=
  match e with
  | AEnq5 => 0
  | AEnq6 r => 1
  | _ => 0
  end.

Lemma inv_e6_ret_e5_internal_step : forall k (s : composed_lts.state (composed_array_queue L)),
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
  let rearp := aqimpl.(ArrayQueueImpl.rear) in
  let xp := aqimpl.(ArrayQueueImpl.x) in
    reachable_len' (composed_array_queue L) s k ->
  forall pid ret v,
    has_read_ary v pid pc ary.(Array.responses L) ret  ->
    exists s1 s2 acts n,
      composed_lts.valid_execution_fragment (composed_array_queue L) s2 s acts /\
      composed_lts.step_L1 (composed_array_queue L)
      s1 pid ((@intL1 li_array li_cnt_cnt (array L) ArrayQueue.front_rear int_ary_read)) s2 /\
      binds pid (AEnq5) (get_pc s1) /\
      (length (gather_pid_events_B pid acts)) = calculate_inv_e6_ret_e5_internal_step v /\
      reachable_len' (composed_array_queue L) s1 n /\
      n < k.
Proof.
  induction k; intros.
  - unfold reachable_len' in H.
    destruct H as [init [acts [Hnew Hvalid]]].
    inversion Hvalid; subst.
    inversion Hnew; subst.
    inversion H1; subst.
    inversion H2; subst.
    unfold pc in H0.
    unfold aqimpl in H0.
    unfold sync_aqimpl in H0.
    rewrite H5 in H0.
    unfold new_array_queue in H0.
    simpl in H0.
    unfold has_read_ary in H0. intuition; subst.
    inversion H0.
    inversion H0.
  - apply reachable_len_reconstruct in H.
    destruct H as [st [acts [Hreach Hstep]]].
    inversion Hstep; subst; clear Hstep.
    -- inversion H3; subst.
      pose proof H3 as HvalidTmp.
      clear H3.
      destruct (eq_nat_dec pid0 pid).
        subst.
        (* exists st, s.
        exists [].
        exists (S k). *)
        inversion H1; subst.
        inversion H; subst; simpl in *.
        inversion H2; subst; simpl in *.
        (* front_rear *)
        eapply IHk with (pid:=pid) (ret:=ret) in Hreach; eauto.
        destruct Hreach as [s1 [s2 [acts [n [Hvalid [Hst [Hb [Hgather [Hr Hlt]]]]]]]]].
        exists s1, s2, acts, n.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto.
        eapply composed_lts.Step_Internal_L1; eauto.
        eapply composed_lts.Step_None; eauto.
        rewrite app_nil_r; auto.
        (* array *)
        inversion H3; subst.
        inversion H4; subst; simpl in *.
        (* cas *)
          unfold has_read_ary in H0.
          intuition; subst.
          apply binds_push_eq_inv in H5; discriminate.
        eapply IHk with (pid:=pid) (ret:=ret) (v:=AEnq6 ret) in Hreach; eauto.
        destruct Hreach as [s1 [s2 [acts [n [Hvalid [Hst [Hb [Hgather [Hr Hlt']]]]]]]]].
        exists s1, s2, acts, n.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto.
        eapply composed_lts.Step_Internal_L1; eauto.
        eapply composed_lts.Step_None; eauto.
        rewrite app_nil_r; auto.
        unfold pc in H5.
        unfold aqimpl in H5.
        unfold sync_aqimpl in H5.
        unfold has_read_ary. intuition; subst.
        (* read *)
        eexists.
        eexists.
        exists [].
        exists (k).
        intuition; eauto.
        eapply composed_lts.Step_None; eauto.
        unfold get_pc. simpl.
        unfold has_read_ary in H0.
        intuition; subst.
        unfold pc in H0.
        unfold aqimpl in H0.
        unfold sync_aqimpl in H0.
        auto.
        apply reachable_len_to_reachable in Hreach.
        apply inv_ary_read_at_e5_d5_invariant in Hreach.
        unfold inv_ary_read_at_e5_d5 in Hreach.
        simpl in Hreach.
        apply Hreach in Hbinds3; auto.
        intuition.
        unfold binds in H9.
        unfold pc in H0.
        unfold aqimpl in H0.
        unfold sync_aqimpl in H0.
        rewrite H0 in H9.
        discriminate.
        simpl.
        unfold has_read_ary in H0.
        intuition; subst.
        simpl. reflexivity.
        apply reachable_len_to_reachable in Hreach.
        apply inv_ary_read_at_e5_d5_invariant in Hreach.
        unfold inv_ary_read_at_e5_d5 in Hreach.
        simpl in Hreach.
        apply Hreach in Hbinds3; auto.
        intuition.
        unfold binds in H9.
        unfold pc in H0.
        unfold aqimpl in H0.
        unfold sync_aqimpl in H0.
        rewrite H0 in H9.
        discriminate.
        unfold binds in H9.
        unfold pc in H0.
        unfold aqimpl in H0.
        unfold sync_aqimpl in H0.
        rewrite H0 in H9.
        discriminate.
        (* eapply valid_execution_fragment_reach_len' with (n':=1) in Hreach; eauto.
        assert (Htmp : k + 1 = (S k)) by lia;
        rewrite Htmp in Hreach; eauto.
        eapply Step_Internal_L1_len'; eauto. *)
      eapply IHk with (pid:=pid) (ret:=ret) in Hreach; eauto.
      destruct Hreach as [s1 [s2 [acts [n' [Hvalid [Hst [Hb [Hgather [Hr Hlt']]]]]]]]].
      exists s1, s2, acts, n'.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto.
      eapply composed_lts.Step_Internal_L1; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite app_nil_r; auto.
      rewrite Hgather. eauto.
      inversion H1; subst.
      inversion H; subst; simpl in *.
      unfold pc in H0.
      unfold aqimpl in H0.
      unfold sync_aqimpl in H0.
      unfold ary in H0.
      unfold sync_ary in H0.
      unfold acc in H0.
      unfold sync_acc in H0.
      inversion H2; subst; simpl in *.
      assumption.
      inversion H3; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold has_read_ary in H0.
      intuition; subst.
      apply binds_push_inv in H5; auto.
      intuition. subst. discriminate.
      unfold has_read_ary. intuition.
      unfold has_read_ary. intuition.
      unfold has_read_ary in H0.
      intuition; subst.
      apply binds_push_neq_inv in H5; auto.
      unfold has_read_ary. left. intuition.
      unfold has_read_ary. intuition.
    -- inversion H3; subst; clear H3.
      inversion H1; subst; simpl in *.
      inversion H; subst; simpl in *.
      unfold pc in H0.
      unfold aqimpl in H0.
      destruct (eq_nat_dec pid pid0).
        subst.
        unfold has_read_ary in H0.
        inversion H2; subst; simpl in *.
        all : try (destruct H0 as [[H01 [H01' H01'']]|[H02 H02']];
        subst;
        eapply substitute_eq_binds_v' in Hbinds0;
        unfold binds in Hbinds0;
        [rewrite H01 in Hbinds0|rewrite H02 in Hbinds0]; discriminate).
      (* inversion H2; subst; simpl in *.
      apply substitute_neq_preserves_binds' in H0; auto; *)
      eapply IHk with (pid:=pid) (ret:=ret) in Hreach; eauto.
      destruct Hreach as [s1 [s2 [acts [n' [Hvalid [Hst [Hb [Hgather [Hr Hlt]]]]]]]]];
      exists s1, s2, acts, n';
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto;
      try (rewrite app_nil_r; auto);
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto.
      rewrite Hgather. eauto.
      inversion H2; subst; simpl in *;
      eapply substitute_neq_preserves_has_read_ary_inv; eauto.
  -- inversion H1.
  -- inversion H1.
  -- inversion H3; subst. clear H3.
    inversion H1; subst; simpl in *.
    inversion H; subst; simpl in *.
    unfold pc in H0.
    unfold aqimpl in H0.
    unfold sync_aqimpl in H0.
      destruct (eq_nat_dec pid pid0).
        subst.
        unfold has_read_ary in H0.
      inversion H2; subst; simpl in *.
      destruct H0 as [[H01 [H01' H01'']]|[H02 H02']]; subst;
      [apply binds_push_eq_inv in H01 | apply binds_push_eq_inv in H02]; discriminate.
      destruct H0 as [[H01 [H01' H01'']]|[H02 H02']]; subst;
      [apply binds_push_eq_inv in H01 | apply binds_push_eq_inv in H02]; discriminate.

      eapply IHk with (pid:=pid) (ret:=ret) in Hreach; eauto; simpl.
      destruct Hreach as [s1 [s2 [acts [n' [Hvalid [Hst [Hb [Hgather [Hr Hlt]]]]]]]]];
      exists s1, s2.
      eexists.
      exists n';
      intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto;
      try (rewrite app_nil_r; auto);
      eapply composed_lts.Step_Initial_Call; eauto;
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      apply Nat.eqb_neq in n; rewrite n.
      rewrite app_nil_r; auto.
      rewrite Hgather.
      eauto.
      unfold has_read_ary in H0.
      unfold has_read_ary.
      inversion H2; subst; simpl in *.
      destruct H0 as [[H01 [H01' H01'']]|[H02 H02']]; subst;
      [apply binds_push_neq_inv in H01 | apply binds_push_neq_inv in H02]; auto.
      destruct H0 as [[H01 [H01' H01'']]|[H02 H02']]; subst;
      [apply binds_push_neq_inv in H01 | apply binds_push_neq_inv in H02]; auto.
  -- inversion H3; subst. clear H3.
    inversion H1; subst; simpl in *.
    inversion H; subst; simpl in *.
    unfold pc in H0.
    unfold aqimpl in H0.
    unfold sync_aqimpl in H0.
      destruct (eq_nat_dec pid pid0).
        subst.
      unfold has_read_ary in H0.

      inversion H2; subst; simpl in *.
      assert (Htmp : pid0 # (remove pc0 pid0))
      by (apply ok_remove_notin; auto);
      apply notin_get_none in Htmp;
      destruct H0 as [[H01 [H01' H01'']]|[H02 H02']]; subst;
      [rewrite H01 in Htmp | rewrite H02 in Htmp]; discriminate.
      assert (Htmp : pid0 # (remove pc0 pid0))
      by (apply ok_remove_notin; auto);
      apply notin_get_none in Htmp;
      destruct H0 as [[H01 [H01' H01'']]|[H02 H02']]; subst;
      [rewrite H01 in Htmp | rewrite H02 in Htmp]; discriminate.

      eapply IHk with (pid:=pid) (ret:=ret) in Hreach; eauto; simpl.
      destruct Hreach as [s1 [s2 [acts [n' [Hvalid [Hst [Hb [Hgather [Hr Hlt]]]]]]]]];
      exists s1, s2.
      eexists.
      exists n';
      intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto;
      try (rewrite app_nil_r; auto);
      eapply composed_lts.Step_Final_Return; eauto;
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      apply Nat.eqb_neq in n; rewrite n.
      rewrite app_nil_r; auto.
      rewrite Hgather.
      eauto.

      unfold has_read_ary in H0.
      unfold has_read_ary.
      inversion H2; subst; simpl in *.
      unfold binds in H0;
      destruct H0 as [[H01 H01']|H02];
      [rewrite remove_neq_preserves_get in H01 | rewrite remove_neq_preserves_get in H02]; auto.
      unfold binds in H0;
      destruct H0 as [[H01 H01']|H02];
      [rewrite remove_neq_preserves_get in H01 | rewrite remove_neq_preserves_get in H02]; auto.
  -- inversion H3; subst. clear H3.
    inversion H1; subst; simpl in *.
    inversion H; subst; simpl in *.
    unfold pc in H0.
    unfold aqimpl in H0.
    unfold sync_aqimpl in H0.
      destruct (eq_nat_dec pid pid0).
        subst.
      inversion H3; subst; simpl in *.
      all : try pose proof Hbinds0 as HbindsTmp.
      all : try
      (eapply substitute_eq_binds_v' in Hbinds0; eauto;
      unfold binds in Hbinds0;
      unfold has_read_ary in H0;
      unfold binds in H0;
      rewrite Hbinds0 in H0;
      destruct H0 as [[H01 [H01' H01'']]|[H02 H02']]; subst; discriminate).
      inversion H2; subst; simpl in *.
      inversion H4; subst; simpl in *.
      inversion H6; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold has_read_ary in H0.
      intuition; subst.
      apply binds_in in H7.
      unfold "#" in Hnotin_res; intuition.
      eapply substitute_eq_binds_v' in Hbinds0;
      unfold binds in Hbinds0;
      rewrite H0 in Hbinds0; discriminate.
      eapply IHk with (pid:=pid) (ret:=ret) in Hreach; eauto; simpl.
      destruct Hreach as [s1 [s2 [acts [n' [Hvalid [Hst [Hb [Hgather [Hr Hlt]]]]]]]]];
      exists s1, s2.
      eexists.
      exists n';
      intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto;
      try (rewrite app_nil_r; auto);
      eapply composed_lts.Step_Internal_Query; eauto;
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      apply Nat.eqb_neq in n; rewrite n.
      rewrite app_nil_r; auto.
      rewrite Hgather.
      eauto.
      unfold ary in H0.
      unfold sync_ary in H0.
      unfold acc in H0.
      unfold sync_acc in H0.
      inversion H2; subst; simpl in *.
      inversion H4; subst; simpl in *.
      inversion H3; subst; simpl in *;
      eapply substitute_neq_preserves_has_read_ary_inv; eauto.
      inversion H3; subst; simpl in *;
      inversion H5; subst; simpl in *;
      inversion H6; subst; simpl in *;
      eapply substitute_neq_preserves_has_read_ary_inv; eauto.
  -- inversion H3; subst. clear H3.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    unfold pc in H0.
    unfold aqimpl in H0.
    unfold sync_aqimpl in H0.
      destruct (eq_nat_dec pid pid0).
        subst.
      inversion H3; subst; simpl in *.
      all : try pose proof Hbinds0 as HbindsTmp.
      all : try
      (eapply substitute_eq_binds_v' in Hbinds0; eauto;
      unfold binds in Hbinds0;
      unfold has_read_ary in H0;
      unfold binds in H0;
      rewrite Hbinds0 in H0;
      destruct H0 as [[H01 [H01' H01'']]|[H02 H02']]; subst; discriminate).

      eapply IHk with (pid:=pid0) (ret:=ret) (v:=AEnq5) in Hreach; eauto; simpl.
      destruct Hreach as [s1 [s2 [acts [n' [Hvalid [Hst [Hb [Hgather [Hr Hlt]]]]]]]]];
      exists s1, s2.
      eexists.
      exists n';
      intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto;
      try (rewrite app_nil_r; auto);
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      rewrite Nat.eqb_refl.
      simpl in Hgather.
      rewrite app_length.
      rewrite Hgather.
      simpl.
      unfold has_read_ary in H0.
      intuition; subst.
      exfalso.
      eapply substitute_eq_binds_v' in Hbinds0; eauto.
      unfold binds in H0.
      rewrite Hbinds0 in H0; discriminate.
      simpl. reflexivity.
      unfold ary in H0.
      unfold sync_ary in H0.
      unfold acc in H0.
      unfold sync_acc in H0.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      inversion H6; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold has_read_ary in H0.
      unfold has_read_ary. intuition; subst.
      eapply substitute_eq_binds_v' in Hbinds0.
      unfold binds in Hbinds0.
      rewrite H0 in Hbinds0; discriminate.
      eapply substitute_eq_binds_v' in Hbinds0.
      unfold binds in Hbinds0.
      rewrite H0 in Hbinds0.
      inversion Hbinds0; subst. intuition.

      eapply IHk with (pid:=pid) (ret:=ret) in Hreach; eauto; simpl.
      destruct Hreach as [s1 [s2 [acts [n' [Hvalid [Hst [Hb [Hgather [Hr Hlt]]]]]]]]];
      exists s1, s2.
      eexists.
      exists n';
      intuition.
      eapply composed_lts.valid_execution_fragment_join'; eauto;
      try (rewrite app_nil_r; auto);
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      apply Nat.eqb_neq in n; rewrite n.
      rewrite app_nil_r; auto.
      rewrite Hgather; eauto.
      unfold ary in H0.
      unfold sync_ary in H0.
      unfold acc in H0.
      unfold sync_acc in H0.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      inversion H3; subst; simpl in *;
      eapply substitute_neq_preserves_has_read_ary_inv; eauto.
      inversion H5; subst; simpl in *.
      unfold has_read_ary in H0.
      unfold has_read_ary.
      inversion H6; subst; simpl in *.
      intuition; subst. left. intuition; subst.
      inversion H3; subst; simpl in *; auto;
      apply substitute_neq_preserves_binds' in H0; auto.
      unfold binds in H7.
      rewrite remove_neq_preserves_get in H7; eauto.
      right.
      inversion H3; subst; simpl in *; auto;
      apply substitute_neq_preserves_binds' in H0; auto.
      intuition; subst. left. intuition.
      inversion H3; subst; simpl in *; auto;
      apply substitute_neq_preserves_binds' in H0; auto.
      unfold binds in H7.
      rewrite remove_neq_preserves_get in H7; eauto.
      right.
      inversion H3; subst; simpl in *; auto;
      apply substitute_neq_preserves_binds' in H0; auto.
Qed.

Lemma inv_e6_ret_e5_internal_step_k_step : forall k (s : composed_lts.state (composed_array_queue L)),
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
  let rearp := aqimpl.(ArrayQueueImpl.rear) in
  let xp := aqimpl.(ArrayQueueImpl.x) in
    reachable_len' (composed_array_queue L) s k ->
  forall pid ret v,
    has_read_ary v pid pc ary.(Array.responses L) ret  ->
    exists s1 s2 acts n t,
      valid_execution_fragment_len' (composed_array_queue L) s2 s acts t /\
      composed_lts.step_L1 (composed_array_queue L)
      s1 pid ((@intL1 li_array li_cnt_cnt (array L) ArrayQueue.front_rear int_ary_read)) s2 /\
      binds pid (AEnq5) (get_pc s1) /\
      (length (gather_pid_events_B pid acts)) = calculate_inv_e6_ret_e5_internal_step v /\
      reachable_len' (composed_array_queue L) s1 n /\
      n < k /\
      k = n + 1 + t.
Proof.
  induction k; intros.
  - unfold reachable_len' in H.
    destruct H as [init [acts [Hnew Hvalid]]].
    inversion Hvalid; subst.
    inversion Hnew; subst.
    inversion H1; subst.
    inversion H2; subst.
    unfold pc in H0.
    unfold aqimpl in H0.
    unfold sync_aqimpl in H0.
    rewrite H5 in H0.
    unfold new_array_queue in H0.
    simpl in H0.
    unfold has_read_ary in H0. intuition; subst.
    inversion H0.
    inversion H0.
  - apply reachable_len_reconstruct in H.
    destruct H as [st [acts [Hreach Hstep]]].
    inversion Hstep; subst; clear Hstep.
    -- inversion H3; subst.
      pose proof H3 as HvalidTmp.
      clear H3.
      destruct (eq_nat_dec pid0 pid).
        subst.
        (* exists st, s.
        exists [].
        exists (S k). *)
        inversion H1; subst.
        inversion H; subst; simpl in *.
        inversion H2; subst; simpl in *.
        (* front_rear *)
        eapply IHk with (pid:=pid) (ret:=ret) in Hreach; eauto.
        destruct Hreach as [s1 [s2 [acts [n [t [Hvalid [Hst [Hb [Hgather [Hr [Hlt Heq]]]]]]]]]]].
        exists s1, s2, (acts ++ []), n, (t + 1).
        intuition.
        eapply valid_execution_fragment_len'_join' with (a:=acts) (a':=[]) (n:=t) (n':=1); eauto.
        eapply Step_Internal_L1_len'; eauto.
        rewrite app_nil_r; auto.
        subst; lia.
        (* array *)
        inversion H3; subst.
        inversion H4; subst; simpl in *.
        (* cas *)
          unfold has_read_ary in H0.
          intuition; subst.
          apply binds_push_eq_inv in H5; discriminate.
        eapply IHk with (pid:=pid) (ret:=ret) (v:=AEnq6 ret) in Hreach; eauto.
        destruct Hreach as [s1 [s2 [acts [n [t [Hvalid [Hst [Hb [Hgather [Hr [Hlt' Heq]]]]]]]]]]].
        exists s1, s2, (acts ++ []), n, (t + 1).
        intuition.
        eapply valid_execution_fragment_len'_join' with (a:=acts) (a':=[]) (n:=t) (n':=1); eauto.
        eapply Step_Internal_L1_len'; eauto.
        rewrite app_nil_r; auto.
        subst; lia.

        (* eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto.
        eapply composed_lts.Step_Internal_L1; eauto.
        eapply composed_lts.Step_None; eauto.
        rewrite app_nil_r; auto. *)
        unfold pc in H5.
        unfold aqimpl in H5.
        unfold sync_aqimpl in H5.
        unfold has_read_ary. intuition; subst.
        (* read *)
        eexists.
        eexists.
        exists [].
        exists (k).
        exists 0.
        intuition; eauto.
        unfold get_pc. simpl.
        unfold has_read_ary in H0.
        intuition; subst.
        unfold pc in H0.
        unfold aqimpl in H0.
        unfold sync_aqimpl in H0.
        auto.
        apply reachable_len_to_reachable in Hreach.
        apply inv_ary_read_at_e5_d5_invariant in Hreach.
        unfold inv_ary_read_at_e5_d5 in Hreach.
        simpl in Hreach.
        apply Hreach in Hbinds3; auto.
        intuition.
        unfold binds in H9.
        unfold pc in H0.
        unfold aqimpl in H0.
        unfold sync_aqimpl in H0.
        rewrite H0 in H9.
        discriminate.
        simpl.
        unfold has_read_ary in H0.
        intuition; subst.
        simpl. reflexivity.
        apply reachable_len_to_reachable in Hreach.
        apply inv_ary_read_at_e5_d5_invariant in Hreach.
        unfold inv_ary_read_at_e5_d5 in Hreach.
        simpl in Hreach.
        apply Hreach in Hbinds3; auto.
        intuition.
        unfold binds in H9.
        unfold pc in H0.
        unfold aqimpl in H0.
        unfold sync_aqimpl in H0.
        rewrite H0 in H9.
        discriminate.
        unfold binds in H9.
        unfold pc in H0.
        unfold aqimpl in H0.
        unfold sync_aqimpl in H0.
        rewrite H0 in H9.
        discriminate.
        lia.
        (* eapply valid_execution_fragment_reach_len' with (n':=1) in Hreach; eauto.
        assert (Htmp : k + 1 = (S k)) by lia;
        rewrite Htmp in Hreach; eauto.
        eapply Step_Internal_L1_len'; eauto. *)
      eapply IHk with (pid:=pid) (ret:=ret) in Hreach; eauto.

        destruct Hreach as [s1 [s2 [acts [n' [t [Hvalid [Hst [Hb [Hgather [Hr [Hlt' Heq]]]]]]]]]]].
        exists s1, s2, (acts ++ []), n', (t + 1).
      intuition.
        eapply valid_execution_fragment_len'_join' with (a:=acts) (a':=[]) (n:=t) (n':=1); eauto.
      eapply Step_Internal_L1_len'; eauto.
      rewrite app_nil_r; auto.
      rewrite Hgather. eauto.
      subst; lia.
      inversion H1; subst.
      inversion H; subst; simpl in *.
      unfold pc in H0.
      unfold aqimpl in H0.
      unfold sync_aqimpl in H0.
      unfold ary in H0.
      unfold sync_ary in H0.
      unfold acc in H0.
      unfold sync_acc in H0.
      inversion H2; subst; simpl in *.
      assumption.
      inversion H3; subst; simpl in *.
      inversion H4; subst; simpl in *.
      unfold has_read_ary in H0.
      intuition; subst.
      apply binds_push_inv in H5; auto.
      intuition. subst. discriminate.
      unfold has_read_ary. intuition.
      unfold has_read_ary. intuition.
      unfold has_read_ary in H0.
      intuition; subst.
      apply binds_push_neq_inv in H5; auto.
      unfold has_read_ary. left. intuition.
      unfold has_read_ary. intuition.
    -- inversion H3; subst; clear H3.
      inversion H1; subst; simpl in *.
      inversion H; subst; simpl in *.
      unfold pc in H0.
      unfold aqimpl in H0.
      destruct (eq_nat_dec pid pid0).
        subst.
        unfold has_read_ary in H0.
        inversion H2; subst; simpl in *.
        all : try (destruct H0 as [[H01 [H01' H01'']]|[H02 H02']];
        subst;
        eapply substitute_eq_binds_v' in Hbinds0;
        unfold binds in Hbinds0;
        [rewrite H01 in Hbinds0|rewrite H02 in Hbinds0]; discriminate).
      (* inversion H2; subst; simpl in *.
      apply substitute_neq_preserves_binds' in H0; auto; *)
      eapply IHk with (pid:=pid) (ret:=ret) in Hreach; eauto.
        destruct Hreach as [s1 [s2 [acts [n' [t [Hvalid [Hst [Hb [Hgather [Hr [Hlt' Heq]]]]]]]]]]];
        exists s1, s2, (acts ++ []), n', (t + 1);
      (* destruct Hreach as [s1 [s2 [acts [n' [Hvalid [Hst [Hb [Hgather [Hr Hlt]]]]]]]]];
      exists s1, s2, acts, n'; *)
      intuition.
        eapply valid_execution_fragment_len'_join' with (a:=acts) (a':=[]) (n:=t) (n':=1); eauto.
      try (rewrite app_nil_r; auto);
      eapply Step_Internal_L2_len'; eauto;
      eapply Step_None_len'; eauto.
      rewrite app_nil_r.
      rewrite Hgather. eauto.
      subst; lia.
      inversion H2; subst; simpl in *;
      eapply substitute_neq_preserves_has_read_ary_inv; eauto.
  -- inversion H1.
  -- inversion H1.
  -- inversion H3; subst. clear H3.
    inversion H1; subst; simpl in *.
    inversion H; subst; simpl in *.
    unfold pc in H0.
    unfold aqimpl in H0.
    unfold sync_aqimpl in H0.
      destruct (eq_nat_dec pid pid0).
        subst.
        unfold has_read_ary in H0.
      inversion H2; subst; simpl in *.
      destruct H0 as [[H01 [H01' H01'']]|[H02 H02']]; subst;
      [apply binds_push_eq_inv in H01 | apply binds_push_eq_inv in H02]; discriminate.
      destruct H0 as [[H01 [H01' H01'']]|[H02 H02']]; subst;
      [apply binds_push_eq_inv in H01 | apply binds_push_eq_inv in H02]; discriminate.

      eapply IHk with (pid:=pid) (ret:=ret) in Hreach; eauto; simpl.
        destruct Hreach as [s1 [s2 [acts [n' [t [Hvalid [Hst [Hb [Hgather [Hr [Hlt' Heq]]]]]]]]]]];
      exists s1, s2.
      eexists.
      exists n', (t + 1);
      intuition.
      eapply valid_execution_fragment_len'_join'; eauto;
      try (rewrite app_nil_r; auto);
      eapply Step_Initial_Call_len'; eauto;
      eapply Step_None_len'; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      apply Nat.eqb_neq in n; rewrite n.
      rewrite app_nil_r; auto.
      rewrite Hgather.
      eauto.
      subst; lia.
      unfold has_read_ary in H0.
      unfold has_read_ary.
      inversion H2; subst; simpl in *.
      destruct H0 as [[H01 [H01' H01'']]|[H02 H02']]; subst;
      [apply binds_push_neq_inv in H01 | apply binds_push_neq_inv in H02]; auto.
      destruct H0 as [[H01 [H01' H01'']]|[H02 H02']]; subst;
      [apply binds_push_neq_inv in H01 | apply binds_push_neq_inv in H02]; auto.
  -- inversion H3; subst. clear H3.
    inversion H1; subst; simpl in *.
    inversion H; subst; simpl in *.
    unfold pc in H0.
    unfold aqimpl in H0.
    unfold sync_aqimpl in H0.
      destruct (eq_nat_dec pid pid0).
        subst.
      unfold has_read_ary in H0.

      inversion H2; subst; simpl in *.
      assert (Htmp : pid0 # (remove pc0 pid0))
      by (apply ok_remove_notin; auto);
      apply notin_get_none in Htmp;
      destruct H0 as [[H01 [H01' H01'']]|[H02 H02']]; subst;
      [rewrite H01 in Htmp | rewrite H02 in Htmp]; discriminate.
      assert (Htmp : pid0 # (remove pc0 pid0))
      by (apply ok_remove_notin; auto);
      apply notin_get_none in Htmp;
      destruct H0 as [[H01 [H01' H01'']]|[H02 H02']]; subst;
      [rewrite H01 in Htmp | rewrite H02 in Htmp]; discriminate.

      eapply IHk with (pid:=pid) (ret:=ret) in Hreach; eauto; simpl.
        destruct Hreach as [s1 [s2 [acts [n' [t [Hvalid [Hst [Hb [Hgather [Hr [Hlt' Heq]]]]]]]]]]];
      exists s1, s2.
      eexists.
      exists n', (t + 1);
      intuition.
      eapply valid_execution_fragment_len'_join'; eauto;
      try (rewrite app_nil_r; auto);
      eapply Step_Final_Return_len'; eauto;
      eapply Step_None_len'; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      apply Nat.eqb_neq in n; rewrite n.
      rewrite app_nil_r; auto.
      rewrite Hgather.
      eauto.
      subst; lia.

      unfold has_read_ary in H0.
      unfold has_read_ary.
      inversion H2; subst; simpl in *.
      unfold binds in H0;
      destruct H0 as [[H01 H01']|H02];
      [rewrite remove_neq_preserves_get in H01 | rewrite remove_neq_preserves_get in H02]; auto.
      unfold binds in H0;
      destruct H0 as [[H01 H01']|H02];
      [rewrite remove_neq_preserves_get in H01 | rewrite remove_neq_preserves_get in H02]; auto.
  -- inversion H3; subst. clear H3.
    inversion H1; subst; simpl in *.
    inversion H; subst; simpl in *.
    unfold pc in H0.
    unfold aqimpl in H0.
    unfold sync_aqimpl in H0.
      destruct (eq_nat_dec pid pid0).
        subst.
      inversion H3; subst; simpl in *.
      all : try pose proof Hbinds0 as HbindsTmp.
      all : try
      (eapply substitute_eq_binds_v' in Hbinds0; eauto;
      unfold binds in Hbinds0;
      unfold has_read_ary in H0;
      unfold binds in H0;
      rewrite Hbinds0 in H0;
      destruct H0 as [[H01 [H01' H01'']]|[H02 H02']]; subst; discriminate).
      inversion H2; subst; simpl in *.
      inversion H4; subst; simpl in *.
      inversion H6; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold has_read_ary in H0.
      intuition; subst.
      apply binds_in in H7.
      unfold "#" in Hnotin_res; intuition.
      eapply substitute_eq_binds_v' in Hbinds0;
      unfold binds in Hbinds0;
      rewrite H0 in Hbinds0; discriminate.
      eapply IHk with (pid:=pid) (ret:=ret) in Hreach; eauto; simpl.
        destruct Hreach as [s1 [s2 [acts [n' [t [Hvalid [Hst [Hb [Hgather [Hr [Hlt' Heq]]]]]]]]]]];
      (* destruct Hreach as [s1 [s2 [acts [n' [Hvalid [Hst [Hb [Hgather [Hr Hlt]]]]]]]]]; *)
      exists s1, s2.
      eexists.
      exists n', (t + 1);
      intuition.
      eapply valid_execution_fragment_len'_join'; eauto;
      try (rewrite app_nil_r; auto);
      eapply Step_Internal_Query_len'; eauto;
      eapply Step_None_len'; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      apply Nat.eqb_neq in n; rewrite n.
      rewrite app_nil_r; auto.
      rewrite Hgather.
      eauto.
      subst; lia.
      unfold ary in H0.
      unfold sync_ary in H0.
      unfold acc in H0.
      unfold sync_acc in H0.
      inversion H2; subst; simpl in *.
      inversion H4; subst; simpl in *.
      inversion H3; subst; simpl in *;
      eapply substitute_neq_preserves_has_read_ary_inv; eauto.
      inversion H3; subst; simpl in *;
      inversion H5; subst; simpl in *;
      inversion H6; subst; simpl in *;
      eapply substitute_neq_preserves_has_read_ary_inv; eauto.
  -- inversion H3; subst. clear H3.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    unfold pc in H0.
    unfold aqimpl in H0.
    unfold sync_aqimpl in H0.
      destruct (eq_nat_dec pid pid0).
        subst.
      inversion H3; subst; simpl in *.
      all : try pose proof Hbinds0 as HbindsTmp.
      all : try
      (eapply substitute_eq_binds_v' in Hbinds0; eauto;
      unfold binds in Hbinds0;
      unfold has_read_ary in H0;
      unfold binds in H0;
      rewrite Hbinds0 in H0;
      destruct H0 as [[H01 [H01' H01'']]|[H02 H02']]; subst; discriminate).

      eapply IHk with (pid:=pid0) (ret:=ret) (v:=AEnq5) in Hreach; eauto; simpl.
        destruct Hreach as [s1 [s2 [acts [n' [t [Hvalid [Hst [Hb [Hgather [Hr [Hlt' Heq]]]]]]]]]]];
      exists s1, s2.
      eexists.
      exists n', (t + 1);
      intuition.
      eapply valid_execution_fragment_len'_join'; eauto;
      try (rewrite app_nil_r; auto);
      eapply Step_Internal_Reply_len'; eauto;
      eapply Step_None_len'; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      rewrite Nat.eqb_refl.
      simpl in Hgather.
      rewrite app_length.
      rewrite Hgather.
      simpl.
      unfold has_read_ary in H0.
      intuition; subst.
      exfalso.
      eapply substitute_eq_binds_v' in Hbinds0; eauto.
      unfold binds in H0.
      rewrite Hbinds0 in H0; discriminate.
      simpl. reflexivity.
      subst; lia.
      unfold ary in H0.
      unfold sync_ary in H0.
      unfold acc in H0.
      unfold sync_acc in H0.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      inversion H6; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold has_read_ary in H0.
      unfold has_read_ary. intuition; subst.
      eapply substitute_eq_binds_v' in Hbinds0.
      unfold binds in Hbinds0.
      rewrite H0 in Hbinds0; discriminate.
      eapply substitute_eq_binds_v' in Hbinds0.
      unfold binds in Hbinds0.
      rewrite H0 in Hbinds0.
      inversion Hbinds0; subst. intuition.

      eapply IHk with (pid:=pid) (ret:=ret) in Hreach; eauto; simpl.
        destruct Hreach as [s1 [s2 [acts [n' [t [Hvalid [Hst [Hb [Hgather [Hr [Hlt' Heq]]]]]]]]]]];
      exists s1, s2.
      eexists.
      exists n', (t + 1);
      intuition.
      eapply valid_execution_fragment_len'_join'; eauto;
      try (rewrite app_nil_r; auto);
      eapply Step_Internal_Reply_len'; eauto;
      eapply Step_None_len'; eauto.
      rewrite gather_pid_events_B_dist.
      simpl.
      apply Nat.eqb_neq in n; rewrite n.
      rewrite app_nil_r; auto.
      rewrite Hgather; eauto.
      subst; lia.
      unfold ary in H0.
      unfold sync_ary in H0.
      unfold acc in H0.
      unfold sync_acc in H0.
      inversion H; subst; simpl in *.
      inversion H4; subst; simpl in *.
      inversion H3; subst; simpl in *;
      eapply substitute_neq_preserves_has_read_ary_inv; eauto.
      inversion H5; subst; simpl in *.
      unfold has_read_ary in H0.
      unfold has_read_ary.
      inversion H6; subst; simpl in *.
      intuition; subst. left. intuition; subst.
      inversion H3; subst; simpl in *; auto;
      apply substitute_neq_preserves_binds' in H0; auto.
      unfold binds in H7.
      rewrite remove_neq_preserves_get in H7; eauto.
      right.
      inversion H3; subst; simpl in *; auto;
      apply substitute_neq_preserves_binds' in H0; auto.
      intuition; subst. left. intuition.
      inversion H3; subst; simpl in *; auto;
      apply substitute_neq_preserves_binds' in H0; auto.
      unfold binds in H7.
      rewrite remove_neq_preserves_get in H7; eauto.
      right.
      inversion H3; subst; simpl in *; auto;
      apply substitute_neq_preserves_binds' in H0; auto.
Qed.

End test.

Section test.

Variable A : Type.

Lemma substitute_preserves_notin': forall (l : env A) pid k v,
  pid # (substitute l k v) ->
  pid # l.
Proof.
  induction l; simpl; intros.
  - assumption.
  - destruct a.
    destruct (k =? v0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq; subst.
      simpl in H. apply notin_union in H.
      apply notin_union.
      intuition.
    -- simpl in H. apply notin_union.
      apply notin_union in H.
      simpl in *. intuition.
      eapply IHl; eauto.
Qed.

End test.

Section test.

Arguments get_pc {L}.
Arguments get_ary {L}.

Variable L : nat.
  
Definition get_xp (s : composed_lts.state (composed_array_queue L)) :=
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
  let xp := aqimpl.(ArrayQueueImpl.x) in
  xp.

Lemma inv_e10_stuttering : forall s s' acts pid,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  binds pid AEnq10 (get_pc s) ->
  length (gather_pid_events_B pid acts) = 0 ->
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
      eapply inv_e10_stuttering in H0; eauto.
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

Ltac solve_after_e6 :=
  try apply after_e6_Enq10;
  try apply after_e6_Enq11;
  try apply after_e6_Enq12;
  try apply after_e6_Enq13;
  try apply after_e6_Enq14;
  try apply after_e6_Enq15;
  try apply after_e6_Enq26;
  try apply after_e6_Enq27.

Lemma inv_e6_ret_e27_xp : forall (s : composed_lts.state (composed_array_queue L)) s',
  forall pid ret acts,
    (* reachable_len' (composed_array_queue L) s k -> *)
    new_valid_execution_fragment (composed_array_queue L) s s' acts ->
    (* s <> s' -> *)
    (* has_read_ary pid (get_pc s) res_ary ret -> *)
    forall v,
    binds pid (AEnq6 ret) (get_pc s) ->
    length (gather_pid_events_B pid acts) = calculate_events v ->
    after_e6 v ->
    binds pid v (get_pc s') ->
    (get_xp s') pid = ret.
Proof.
  induction 1; intros.
  - subst.
    unfold after_e6 in H2.
    unfold binds in H0.
    intuition; subst.
    all :  try (rewrite H3 in H0; discriminate).
    destruct H as [r Hr]. subst.
    rewrite H3 in H0; discriminate.
    destruct H2 as [r Hr]. subst.
    rewrite H3 in H0; discriminate.
  - intuition.
    unfold get_pc, get_xp in *; simpl in *.
    inversion H; subst; simpl in *.
    eapply IHnew_valid_execution_fragment; eauto.
  - intuition.
    unfold get_pc, get_xp in *; simpl in *.
    destruct (eq_nat_dec pid pid0).
      --
      subst.
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold binds in H4.
      inversion H6; subst; simpl in *.
      eapply substitute_eq_binds_v' in Hbinds0; eauto.
      rewrite Hbinds0 in H4.
      unfold after_e6 in H3;
      intuition; subst; try discriminate;
      try (destruct H8; subst; discriminate);
      try (destruct H7; subst; discriminate);
      try (destruct H3; subst; discriminate).
      rewrite Nat.eqb_refl.
      assert (Htmp : v = AEnq10).
      eapply substitute_eq_binds_v' in Hbinds0.
      rewrite Hbinds0 in H4.
      inversion H4; subst; auto.
      subst.
      apply new_valid_execution_fragment_to_valid_execution_fragment in H0; auto.
      eapply inv_e6_stuttering in H0; eauto.
      unfold get_pc in H0; simpl in H0. intuition.
      unfold binds in H7.
      rewrite Hbinds0 in H7.
      inversion H7; subst; auto.
      unfold binds in H7.
      rewrite Hbinds0 in H7; discriminate.

      all : try
      (
        pose proof Hbinds0 as HbindsTmp;
        eapply substitute_eq_binds_v' in Hbinds0; eauto;
      rewrite Hbinds0 in H4;
      unfold after_e6 in H3;
      intuition; subst; try discriminate;
      try (destruct H8; subst; discriminate);
      try (destruct H7; subst; discriminate);
      try (destruct H3; subst; discriminate);
      try (destruct H9; subst; discriminate)).
      eapply IHnew_valid_execution_fragment.
      auto.
      3 : { eauto. }
      rewrite H2. simpl. reflexivity.
      solve_after_e6.
      eapply IHnew_valid_execution_fragment.
      auto.
      3 : { eauto. }
      rewrite H2. simpl. reflexivity.
      solve_after_e6.
      eapply IHnew_valid_execution_fragment.
      auto.
      3 : { eauto. }
      rewrite H2. simpl. reflexivity.
      solve_after_e6.
      --
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      inversion H6; subst; simpl in *.
      all : try (eapply IHnew_valid_execution_fragment; eauto;
      apply substitute_neq_preserves_binds' in H4; auto).
      destruct (pid =? pid0)eqn:Heq.
        apply Nat.eqb_eq in Heq; intuition.
      eapply IHnew_valid_execution_fragment; eauto;
      apply substitute_neq_preserves_binds' in H4; auto.
      destruct (pid =? pid0)eqn:Heq.
        apply Nat.eqb_eq in Heq; intuition.
      eapply IHnew_valid_execution_fragment; eauto;
      apply substitute_neq_preserves_binds' in H4; auto.
  - inversion H.
  - inversion H.
  - destruct (eq_nat_dec pid pid0).
    subst.
      -- inversion H; subst; simpl in *.
        inversion H5; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H6; subst; simpl in *;
        apply binds_push_eq_inv in H4; subst;
        unfold after_e6 in H3; intuition; subst; try discriminate;
        try (destruct H; subst; discriminate);
        try (destruct H0; subst; discriminate);
        try (destruct H3; subst; discriminate);
        try (destruct H4; subst; discriminate);
        try (destruct H5; subst; discriminate).
      -- inversion H; subst; simpl in *.
        inversion H5; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H6; subst; simpl in *;
        eapply IHnew_valid_execution_fragment; eauto.
        rewrite gather_pid_events_B_dist in H2.
        simpl in H2.
        apply Nat.eqb_neq in n; rewrite n in H2.
        rewrite app_nil_r in H2; rewrite H2; auto.
        apply binds_push_neq_inv in H4; auto.
        rewrite gather_pid_events_B_dist in H2.
        simpl in H2.
        apply Nat.eqb_neq in n; rewrite n in H2.
        rewrite app_nil_r in H2; rewrite H2; auto.
        apply binds_push_neq_inv in H4; auto.
  - destruct (eq_nat_dec pid pid0).
    subst.
      -- inversion H; subst; simpl in *.
        inversion H5; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H6; subst; simpl in *;
        assert (Htmp : pid0 # (remove pc pid0)) by
        (apply ok_remove_notin; auto);
        apply notin_get_none in Htmp;
        rewrite H4 in Htmp; discriminate.
      -- inversion H; subst; simpl in *.
        inversion H5; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H6; subst; simpl in *;
        eapply IHnew_valid_execution_fragment; eauto.
        rewrite gather_pid_events_B_dist in H2.
        simpl in H2.
        apply Nat.eqb_neq in n; rewrite n in H2.
        rewrite app_nil_r in H2; rewrite H2; auto.
        eapply remove_preserves_binds_notin in H4; eauto.
        rewrite gather_pid_events_B_dist in H2.
        simpl in H2.
        apply Nat.eqb_neq in n; rewrite n in H2.
        rewrite app_nil_r in H2; rewrite H2; auto.
        eapply remove_preserves_binds_notin in H4; eauto.
  - destruct (eq_nat_dec pid pid0).
    subst.
      -- inversion H; subst; simpl in *.
        inversion H5; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        unfold binds in H4.
        inversion H7; subst; simpl in *.
        all : 
        pose proof Hbinds0 as HbindsTmp;
        eapply substitute_eq_binds_v' in Hbinds0;
        rewrite Hbinds0 in H4;
        unfold after_e6 in H3;
        intuition; subst; try discriminate;
        try (destruct H; subst; discriminate);
        try (destruct H0; subst; discriminate);
        try (destruct H3; subst; discriminate);
        try (destruct H4; subst; discriminate);
        try (destruct H8; subst; discriminate);
        try (destruct H5; subst; discriminate).
        eapply IHnew_valid_execution_fragment; eauto.
        rewrite gather_pid_events_B_dist in H2.
        simpl in H2.
        rewrite Nat.eqb_refl in H2.
        rewrite app_length in H2; simpl in H2.
        simpl.
        lia.
        solve_after_e6.
        eapply IHnew_valid_execution_fragment; eauto.
        rewrite gather_pid_events_B_dist in H2.
        simpl in H2.
        rewrite Nat.eqb_refl in H2.
        rewrite app_length in H2; simpl in H2.
        simpl.
        lia.
        solve_after_e6.

        eapply IHnew_valid_execution_fragment; eauto.
        rewrite gather_pid_events_B_dist in H2.
        simpl in H2.
        rewrite Nat.eqb_refl in H2.
        rewrite app_length in H2; simpl in H2.
        simpl.
        lia.
        solve_after_e6.
      -- inversion H; subst; simpl in *.
        inversion H5; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H7; subst; simpl in *.
        all :
        eapply IHnew_valid_execution_fragment; eauto;
        [rewrite gather_pid_events_B_dist in H2;
        simpl in H2;
        apply Nat.eqb_neq in n; rewrite n in H2;
        rewrite app_nil_r in H2; rewrite H2; auto|
        eapply substitute_neq_preserves_binds'; eauto].
  - destruct (eq_nat_dec pid pid0).
    subst.
      -- inversion H; subst; simpl in *.
        inversion H6; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        unfold binds in H4.
        inversion H7; subst; simpl in *.
        all : 
        pose proof Hbinds0 as HbindsTmp;
        eapply substitute_eq_binds_v' in Hbinds0;
        rewrite Hbinds0 in H4;
        unfold after_e6 in H3;
        intuition; subst; try discriminate;
        try (destruct H; subst; discriminate);
        try (destruct H0; subst; discriminate);
        try (destruct H3; subst; discriminate);
        try (destruct H4; subst; discriminate);
        try (destruct H8; subst; discriminate);
        try (destruct H5; subst; discriminate).
        eapply IHnew_valid_execution_fragment; eauto.
        rewrite gather_pid_events_B_dist in H2.
        simpl in H2.
        rewrite Nat.eqb_refl in H2.
        rewrite app_length in H2; simpl in H2.
        simpl.
        destruct H8 as [r' Hr']; subst.
        simpl in H2.
        lia.
        solve_after_e6.
        eapply IHnew_valid_execution_fragment; eauto.
        rewrite gather_pid_events_B_dist in H2.
        simpl in H2.
        rewrite Nat.eqb_refl in H2.
        rewrite app_length in H2; simpl in H2.
        simpl.
        destruct H3 as [r' Hr']; subst.
        simpl in H2.
        lia.
        solve_after_e6.
      -- inversion H; subst; simpl in *.
        inversion H6; subst; simpl in *.
        unfold get_pc in *; simpl in *.
        inversion H7; subst; simpl in *.
        all :
        eapply IHnew_valid_execution_fragment; eauto;
        [rewrite gather_pid_events_B_dist in H2;
        simpl in H2;
        apply Nat.eqb_neq in n; rewrite n in H2;
        rewrite app_nil_r in H2; rewrite H2; auto|
        eapply substitute_neq_preserves_binds'; eauto].
Qed.

Lemma inv_e5_ret_e6_ret: forall s s' pid acts,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  binds pid (AEnq5) (get_pc s) ->
  forall ret ret0,
  binds pid (AryReadOk ret) (get_ary s).(Array.responses L) ->
  binds pid (AEnq6 ret0) (get_pc s') ->
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
      unfold get_ary in *; simpl in *.
      intuition.
      eapply H7; eauto.
      inversion H6; subst; simpl in *.
      intuition.
      inversion H8; subst; simpl in *.
      inversion H9; subst; simpl in *;
      apply binds_in in H2;
      unfold "#" in Hnotin_res; intuition.
    --
      inversion H; subst; simpl in *.
      inversion H5; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold get_ary in *; simpl in *.
      intuition.
      eapply H7; eauto.
      inversion H6; subst; simpl in *.
      intuition.
      inversion H8; subst; simpl in *.
      inversion H9; subst; simpl in *;
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
      unfold get_ary in *; simpl in *.
      inversion H7; subst; simpl in *.
      all : eapply IHvalid_execution_fragment; eauto;
      [apply substitute_neq_preserves_binds; auto|
      inversion H6; subst; simpl in *;
      inversion H8; subst; simpl in *; auto|
      apply Nat.eqb_neq in n; rewrite n in H4; auto].
      all : inversion H10; subst; simpl in *; auto;
      inversion H9; subst; simpl in *; auto.
  - destruct (eq_nat_dec pid pid0).
    -- subst.
      unfold binds in H1.
      inversion H; subst; simpl in *.
      inversion H6; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold get_ary in *; simpl in *.
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
      rewrite Hbinds4 in H2.
      inversion H2; subst.
      eapply inv_e6_stuttering with (ret:=ret) in H0; eauto.
      intuition.
      unfold get_pc in H11; simpl in H11.
      unfold binds in H11.
      rewrite H3 in H11.
      inversion H11; subst; auto.
      unfold binds in H11.
      rewrite H3 in H11; discriminate.
      unfold get_pc; simpl.
      eapply substitute_eq_binds_v'; eauto.
    -- inversion H; subst; simpl in *.
      inversion H6; subst; simpl in *.
      unfold get_pc in *; simpl in *.
      unfold get_ary in *; simpl in *.
      inversion H7; subst; simpl in *.
      all : eapply IHvalid_execution_fragment; eauto;
      [apply substitute_neq_preserves_binds; auto|
      inversion H5; subst; simpl in *;
      inversion H8; subst; simpl in *; auto|
      apply Nat.eqb_neq in n; rewrite n in H4; auto].
      all : inversion H10; subst; simpl in *; auto;
      inversion H9; subst; simpl in *;
      apply remove_neq_preserves_binds; auto.
Qed.

Definition get_impl (s : composed_lts.state (composed_array_queue L)) :=
  let sync_aqimpl := s.(Compose.L2State) in
  let aqimpl := sync_aqimpl.(LState) in
  aqimpl.

Lemma inv_e5_instant : forall k s s' pid,
  reachable_len' (composed_array_queue L) s k ->
  binds pid (AEnq5) (get_pc s) ->
  composed_lts.step_L1 (composed_array_queue L)
  s pid ((@intL1 li_array li_cnt_cnt (array L) ArrayQueue.front_rear int_ary_read)) s' ->
  binds pid (AryRead ((get_impl s).(ArrayQueueImpl.rear) pid mod L)) (get_ary s).(Array.requests L).
Proof.
  intros.
  apply reachable_len_to_reachable in H.
  apply step_invariant in H.
  unfold inv in H.
  inversion H1; subst; simpl in *.
  inversion H2; subst; simpl in *.
  eapply H in Hbinds0; eauto.
  unfold get_impl, get_ary in *; simpl in *.
  destruct Hbinds0 as [s1 [s2 [q [acts [Hint_query [Hvalid Hgather]]]]]].
  (* inversion Hint_query; subst; simpl in *.
  inversion H4; subst; simpl in *.
  unfold get_pc in H0; simpl in H0.
  unfold binds in H0.
  inversion H6; subst; simpl in *.
  rewrite Hbinds1 in H0. *)

  pose proof Hvalid as HvalidTmp.
  apply valid_execution_fragment_com' in Hvalid.
    simpl in Hvalid.
    inversion Hint_query; subst; simpl in *.
    inversion H4; subst; simpl in *.
    destruct st2; simpl in *.
    eapply valid_execution_fragment_sync in Hvalid; eauto.
    unfold get_pc in H0; simpl in H0.
    unfold binds in H0.
    inversion H6; subst; simpl in *.
    Ltac aa H Hvalid pid H0 acts Hgather :=
    eapply H with (pid:=pid) in Hvalid; simpl; eauto;
    [(rewrite Hvalid in H0; discriminate)|
    (eapply substitute_eq_binds_v'; eauto)|
      (assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil) by
      (rewrite Hgather; simpl; reflexivity);
      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B;
      assumption)].
    aa noB_preserves_AEnq2 Hvalid pid H0 acts Hgather.

    inversion H5; subst; simpl in *.
    inversion H7; subst; simpl in *.
    inversion H9; subst; simpl in *.
    inversion H8; subst; simpl in *.
    apply valid_execution_fragment_com in HvalidTmp.
      simpl in HvalidTmp.
    inversion H3; subst; simpl in *.
    inversion H11; subst; simpl in *.
    inversion H10; subst; simpl in *.
      (* inversion H9; subst.
      inversion H10; subst.
      inversion H12; subst.
      inversion H11; subst.
      inversion H14; subst.
      inversion H13; subst. *)
      eapply internal_preserves_request'' with (pid:=pid) in HvalidTmp; simpl in *.
      4 : { eauto.
      }
      3 : {
        apply binds_push_eq.
      }
      inversion HvalidTmp; subst.
      eapply noB_preserves_AEnq5'' with (pid:=pid) in Hvalid; simpl; eauto.
      2 : {
        (eapply substitute_eq_binds_v'; eauto).
      }
      2 : {
        (assert (clts_events_B_to_events_B (gather_pid_events_B pid acts) = nil) by
      (rewrite Hgather; simpl; reflexivity);
      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B;
      assumption).
      }
      simpl in Hvalid.
      rewrite Hvalid in Hbinds4; auto.
      rewrite gather_pid_events_B_gather_pid_external_events; auto.
    aa noB_preserves_AEnq11 Hvalid pid H0 acts Hgather.
    aa noB_preserves_AEnq14 Hvalid pid H0 acts Hgather.
    aa noB_preserves_AEnq28 Hvalid pid H0 acts Hgather.
    aa noB_preserves_AEnq31 Hvalid pid H0 acts Hgather.
    aa noB_preserves_ADeq2 Hvalid pid H0 acts Hgather.
    aa noB_preserves_ADeq5 Hvalid pid H0 acts Hgather.
    aa noB_preserves_ADeq11 Hvalid pid H0 acts Hgather.
    aa noB_preserves_ADeq14 Hvalid pid H0 acts Hgather.
    aa noB_preserves_ADeq28 Hvalid pid H0 acts Hgather.
    aa noB_preserves_ADeq31 Hvalid pid H0 acts Hgather.
Qed.

End test.