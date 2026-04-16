Require Import
  LibVar
  LibEnv
  List
  Arith
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
  Queue.
Import ListNotations.

Section test.
  
Variable A : Type.

Lemma remove_neq_preserves_get: forall (pc : env A) pid pid',
  pid <> pid' ->
  get pid (remove pc pid') =
  get pid pc.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - destruct a.
    match_if'.
    apply Nat.eqb_eq in Heqb.
    apply Nat.eqb_eq in Heqb0.
    subst.
    intuition.
    rewrite IHpc; auto.
Qed.

End test.

Section test.

Context {liA liB : language_interface }.
Variable L : lts liA liB.

Lemma valid_execution_fragment_preserves_inv: forall s s' acts inv,
  valid_execution_fragment L s s' acts ->
  invariant_ind L inv ->
  inv s ->
  inv s'.
Proof.
  induction 1; intros.
  subst. assumption.
  all : apply IHvalid_execution_fragment; auto;
    apply H1 in H; auto.
Qed.

Lemma invariant_ind_to_invariant: forall P,
  invariant_ind L P ->
  invariant L P.
Proof.
  intros.
  unfold invariant. intros.
  unfold reachable in H0.
  destruct H0 as [init [acts [Hnew Hvalid]]].
  eapply valid_execution_fragment_preserves_inv; eauto.
  apply H; auto.
Qed.

End test.

Section test.

Variable A : Type.

Lemma substitute_neq_preserves_binds':
  forall (l : env A) pid pid' v v',
  binds pid v (substitute l pid' v') ->
  pid' <> pid ->
  binds pid v l.
Proof.
  induction l; simpl; intros.
  - inversion H.
  - destruct a.
    unfold binds in *.
    simpl in *.
    destruct (pid =? v0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst.
      destruct (pid' =? v0)eqn:Heq'.
      --- apply Nat.eqb_eq in Heq'.
        intuition.
      --- simpl in *.
        rewrite Nat.eqb_refl in H.
        assumption.
    -- destruct (pid' =? v0)eqn:Heq'.
      --- apply Nat.eqb_eq in Heq'.
        subst. simpl in *.
        rewrite Heq in H. assumption.
      --- simpl in *.
        rewrite Heq in H.
        erewrite IHl; eauto.
Qed.
  
End test.

Require Import
  Lia.

Section INV.

Variable L : nat.
Hypothesis H : L > 0.

Definition get_rear (s : composed_lts.state (composed_array_queue L)) :=
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
  rear.

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

Definition get_pc (s : composed_lts.state (composed_array_queue L)) :=
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
  pc.

Lemma REAR_not_decrease: forall s s' acts,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  (get_rear s).(Counter.value) <= (get_rear s').(Counter.value).
Proof. 
  induction 1; intros.
  - subst. lia.
  - eapply Nat.le_trans.
    2 : { eassumption. }
    clear IHvalid_execution_fragment.
    clear H1.
    inversion H0; subst.
    inversion H1; subst.
    inversion H2; subst; simpl in *.
    -- inversion H3; subst; simpl in *.
      inversion H4; subst; simpl in *.
      inversion H5; subst; simpl in *;
        inversion H6; subst; simpl in *; lia.
      inversion H5; subst; simpl in *.
        inversion H6; subst; simpl in *;
        unfold get_rear; simpl;
          lia.
    -- inversion H3; subst; simpl in *.
      inversion H4; subst; simpl in *;
      unfold get_rear; simpl; lia.
  - eapply Nat.le_trans.
    2 : { eassumption. }
    clear IHvalid_execution_fragment.
    clear H1.
    inversion H0; subst.
    inversion H1; subst.
    inversion H2; subst; simpl in *;
    unfold get_rear; simpl; lia.
  - inversion H0.
  - inversion H0.
  - eapply Nat.le_trans.
    2 : { eassumption. }
    clear IHvalid_execution_fragment.
    clear H1.
    inversion H0; subst.
    inversion H1; subst.
    inversion H2; subst; simpl in *;
    unfold get_rear; simpl; lia.
  - eapply Nat.le_trans.
    2 : { eassumption. }
    clear IHvalid_execution_fragment.
    clear H1.
    inversion H0; subst.
    inversion H1; subst.
    inversion H2; subst; simpl in *;
    unfold get_rear; simpl; lia.
  - eapply Nat.le_trans.
    2 : { eassumption. }
    clear IHvalid_execution_fragment.
    clear H1.
    inversion H0; subst.
    inversion H1; subst.
    inversion H2; subst; simpl in *.
    inversion H4; subst; simpl in *.
    -- inversion H5; subst; simpl in *.
      inversion H6; subst; simpl in *.
      inversion H7; subst; simpl in *.
        inversion H8; subst; simpl in *; lia.
      inversion H7; subst; simpl in *.
        inversion H8; subst; simpl in *;
        unfold get_rear; simpl; lia.
    -- inversion H5; subst; simpl in *.
      inversion H6; subst; simpl in *;
        unfold get_rear; simpl; lia.
  - eapply Nat.le_trans.
    2 : { eassumption. }
    clear IHvalid_execution_fragment.
    clear H1.
    inversion H0; subst.
    inversion H1; subst.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    -- inversion H5; subst; simpl in *.
      inversion H6; subst; simpl in *.
      inversion H7; subst; simpl in *.
        inversion H8; subst; simpl in *; lia.
      inversion H7; subst; simpl in *.
        inversion H8; subst; simpl in *;
        unfold get_rear; simpl; lia.
    -- inversion H5; subst; simpl in *.
      inversion H6; subst; simpl in *;
        unfold get_rear; simpl; lia.
Qed.

Lemma FRONT_not_decrease: forall s s' acts,
  composed_lts.valid_execution_fragment (composed_array_queue L) s s' acts ->
  (get_front s).(Counter.value) <= (get_front s').(Counter.value).
Proof. 
  induction 1; intros.
  - subst. lia.
  - eapply Nat.le_trans.
    2 : { eassumption. }
    clear IHvalid_execution_fragment.
    clear H1.
    inversion H0; subst.
    inversion H1; subst.
    inversion H2; subst; simpl in *.
    -- inversion H3; subst; simpl in *.
      inversion H4; subst; simpl in *.
      inversion H5; subst; simpl in *.
        inversion H6; subst; simpl in *;
        unfold get_front; simpl;
          lia.
      inversion H5; subst; simpl in *;
        inversion H6; subst; simpl in *; lia.
    -- inversion H3; subst; simpl in *.
      inversion H4; subst; simpl in *;
      unfold get_front; simpl; lia.
  - eapply Nat.le_trans.
    2 : { eassumption. }
    clear IHvalid_execution_fragment.
    clear H1.
    inversion H0; subst.
    inversion H1; subst.
    inversion H2; subst; simpl in *;
    unfold get_front; simpl; lia.
  - inversion H0.
  - inversion H0.
  - eapply Nat.le_trans.
    2 : { eassumption. }
    clear IHvalid_execution_fragment.
    clear H1.
    inversion H0; subst.
    inversion H1; subst.
    inversion H2; subst; simpl in *;
    unfold get_front; simpl; lia.
  - eapply Nat.le_trans.
    2 : { eassumption. }
    clear IHvalid_execution_fragment.
    clear H1.
    inversion H0; subst.
    inversion H1; subst.
    inversion H2; subst; simpl in *;
    unfold get_front; simpl; lia.
  - eapply Nat.le_trans.
    2 : { eassumption. }
    clear IHvalid_execution_fragment.
    clear H1.
    inversion H0; subst.
    inversion H1; subst.
    inversion H2; subst; simpl in *.
    inversion H4; subst; simpl in *.
    -- inversion H5; subst; simpl in *.
      inversion H6; subst; simpl in *.
      inversion H7; subst; simpl in *.
        inversion H8; subst; simpl in *;
        unfold get_front; simpl; lia.
      inversion H7; subst; simpl in *.
        inversion H8; subst; simpl in *; lia.
    -- inversion H5; subst; simpl in *.
      inversion H6; subst; simpl in *;
        unfold get_front; simpl; lia.
  - eapply Nat.le_trans.
    2 : { eassumption. }
    clear IHvalid_execution_fragment.
    clear H1.
    inversion H0; subst.
    inversion H1; subst.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    -- inversion H5; subst; simpl in *.
      inversion H6; subst; simpl in *.
      inversion H7; subst; simpl in *.
        inversion H8; subst; simpl in *;
        unfold get_front; simpl; lia.
      inversion H7; subst; simpl in *.
        inversion H8; subst; simpl in *; lia.
    -- inversion H5; subst; simpl in *.
      inversion H6; subst; simpl in *;
        unfold get_front; simpl; lia.
Qed.

Definition inv_ret (s : composed_lts.state (composed_array_queue L)) :=
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
  forall pid ret,
    binds pid (AEnq3 ret) pc ->
    exists s1 s2 acts,
      composed_lts.internal_reply
        (composed_array_queue L)
        s1 pid
          (@Tensor.replyR li_array li_cnt_cnt
            (@Tensor.replyR li_counter li_counter (CntReadOk ret)))
        s2 /\
      composed_lts.valid_execution_fragment (composed_array_queue L) s2 s acts.

Lemma inv_ret_inv:
  composed_lts.invariant_ind (composed_array_queue L)
  inv_ret.
Proof.
  unfold composed_lts.invariant_ind. intuition.
  - inversion H0; subst.
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
    unfold inv_ret.
    rewrite H10.
    intros.
    unfold new_array_queue in H21.
    inversion H21.
  - unfold inv_ret. intros.
      inversion H1; subst.
      simpl in H2.
      unfold inv_ret in H0.
      apply H0 in H2.
      destruct H2 as [s1 [s2 [acts [Hint_reply Hvalid]]]].
      exists s1, s2, acts.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
      eapply composed_lts.Step_Internal_L1; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite app_nil_r.
      reflexivity.
  - unfold inv_ret. intros.
    destruct (eq_nat_dec pid pid0).
      subst.
      inversion H1; subst.
      simpl in H2.
      inversion H3; subst.
      simpl in H2.
      inversion H4; subst;
      simpl in H2;
      eapply substitute_eq_binds_v' in Hbinds0; eauto;
      unfold binds in Hbinds0;
      erewrite H2 in Hbinds0;
      discriminate.
    inversion H1; subst.
    inversion H3; subst.
    inversion H4; subst;
    apply substitute_neq_preserves_binds' in H2; auto;
    apply H0 in H2;
    destruct H2 as [s1 [s2 [acts [Hint_reply Hvalid]]]];
      exists s1, s2, acts;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts) (a':=[]); eauto;
      try rewrite app_nil_r; auto;
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto.
  - unfold inv_ret. intros.
    destruct (eq_nat_dec pid pid0).
      subst.
      inversion H1; subst.
      simpl in H2.
      inversion H3; subst.
      simpl in H2.
      inversion H4; subst;
      simpl in H2;
      apply binds_push_eq_inv in H2; discriminate.
    inversion H1; subst.
    inversion H3; subst.
    inversion H4; subst;
    simpl in H2;
    apply binds_push_neq_inv in H2; auto;
    apply H0 in H2;
    destruct H2 as [s1 [s2 [acts [Hint_reply Hvalid]]]];
      exists s1, s2;
      eexists;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
      try rewrite app_nil_r; auto;
      eapply composed_lts.Step_Initial_Call; eauto;
      eapply composed_lts.Step_None; eauto.
  - destruct act.
  - destruct act.
  - unfold inv_ret. intros.
    destruct (eq_nat_dec pid pid0).
      subst.
      inversion H1; subst.
      simpl in H2.
      inversion H3; subst;
      simpl in H2;
      inversion H4; subst;
      simpl in H2;
      assert (Htmp : pid0 # (remove pc pid0)) by (apply ok_remove_notin; auto);
      apply binds_in in H2;
      unfold "#" in Htmp; intuition.
    inversion H1; subst.
    inversion H3; subst.
    inversion H4; subst;
    simpl in H2;
    apply remove_preserves_binds_notin in H2; auto;
    apply H0 in H2;
    destruct H2 as [s1 [s2 [acts [Hint_reply Hvalid]]]];
      exists s1, s2;
      eexists;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
      try rewrite app_nil_r; auto;
      eapply composed_lts.Step_Final_Return; eauto;
      eapply composed_lts.Step_None; eauto.
  - unfold inv_ret. intros.
    destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H1; subst.
      inversion H3; subst.
      inversion H5; subst;
      eapply substitute_eq_binds_v' in Hbinds0;
      unfold binds in Hbinds0;
      simpl in H2;
      erewrite H2 in Hbinds0;
      discriminate.
    -- specialize (H0 pid0 ret).
      inversion H1; subst.
      inversion H3; subst.
      inversion H5; subst;
      apply substitute_neq_preserves_binds' in H2; auto;
      intuition;
      destruct H6 as [s1 [s2 [acts [Hstep Hvalid]]]];
      exists s1, s2;
      eexists;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
      eapply composed_lts.Step_Internal_Query; eauto;
      eapply composed_lts.Step_None; eauto.
  - unfold inv_ret. intros.
    destruct (eq_nat_dec pid pid0).
    -- subst.
      exists st, st'.
      exists [].
      inversion H1; subst.
      inversion H4; subst.
      inversion H5; subst; simpl in *.
      intuition.
      2 : {
        eapply composed_lts.Step_None; eauto.
      }
      eapply substitute_eq_binds_v' with (v':=(AEnq3 ret0)) in Hbinds0.
      unfold binds in Hbinds0.
      rewrite H2 in Hbinds0.
      inversion Hbinds0; subst.
      assumption.
      all : eapply substitute_eq_binds_v' in Hbinds0;
      unfold binds in Hbinds0;
      simpl in H2;
      erewrite H2 in Hbinds0;
      discriminate.
    -- specialize (H0 pid0 ret).
      inversion H1; subst.
      inversion H4; subst.
      inversion H5; subst;
      apply substitute_neq_preserves_binds' in H2; auto;
      intuition;
      destruct H6 as [s1 [s2 [acts [Hstep Hvalid]]]];
      exists s1, s2;
      eexists;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto.
Qed.

Definition inv_ret_with_reachable (s : composed_lts.state (composed_array_queue L)) :=
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
  (forall pid ret,
    binds pid (AEnq3 ret) pc ->
    exists s1 s2 acts,
      composed_lts.internal_reply
        (composed_array_queue L)
        s1 pid
          (@Tensor.replyR li_array li_cnt_cnt
            (@Tensor.replyR li_counter li_counter (CntReadOk ret)))
        s2 /\
      composed_lts.valid_execution_fragment (composed_array_queue L) s2 s acts /\
      composed_lts.reachable (composed_array_queue L) s1 /\
      binds pid (AEnq2) (get_pc s1) /\
       binds pid (CntReadOk ret) (get_rear s1).(Counter.responses)
      ) /\
      composed_lts.reachable (composed_array_queue L) s.

Lemma inv_ret_inv_with_reachble:
  composed_lts.invariant_ind (composed_array_queue L)
  inv_ret_with_reachable.
Proof.
  unfold inv_ret_with_reachable.
  apply invariant_ind''_imply_invariant_ind_land.
  unfold invariant_ind''. intuition.
  apply reachable_is_invariant.
  unfold about.
  intuition; rename H1 into Hbinds.
  - inversion H0; subst.
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
    rewrite H10 in Hbinds.
    intros.
    unfold new_array_queue in Hbinds.
    inversion Hbinds.
  - unfold inv_ret_with_reachable. intros.
    rename H2 into H1.
    rename H3 into H2.
      inversion H1; subst.
      simpl in H2.
      unfold inv_ret in H0.
      apply H0 in H2.
      destruct H2 as [s1 [s2 [acts [Hint_reply Hvalid]]]].
      exists s1, s2, acts.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
      eapply composed_lts.Step_Internal_L1; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite app_nil_r.
      reflexivity.
  - unfold inv_ret_with_reachable. intros.
    rename H2 into H1.
    rename H3 into H2.
    destruct (eq_nat_dec pid pid0).
      subst.
      inversion H1; subst.
      simpl in H2.
      inversion H3; subst.
      simpl in H2.
      inversion H4; subst;
      simpl in H2;
      eapply substitute_eq_binds_v' in Hbinds1; eauto;
      unfold binds in Hbinds1;
      erewrite H2 in Hbinds1;
      discriminate.
    inversion H1; subst.
    inversion H3; subst.
    inversion H4; subst;
    apply substitute_neq_preserves_binds' in H2; auto;
    apply H0 in H2;
    destruct H2 as [s1 [s2 [acts [Hint_reply Hvalid]]]];
      exists s1, s2, acts;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts) (a':=[]); eauto;
      try rewrite app_nil_r; auto;
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto.
  - unfold inv_ret_with_reachable. intros.
    rename H2 into H1.
    rename H3 into H2.
    destruct (eq_nat_dec pid pid0).
      subst.
      inversion H1; subst.
      simpl in H2.
      inversion H3; subst.
      simpl in H2.
      inversion H4; subst;
      simpl in H2;
      apply binds_push_eq_inv in H2; discriminate.
    inversion H1; subst.
    inversion H3; subst.
    inversion H4; subst;
    simpl in H2;
    apply binds_push_neq_inv in H2; auto;
    apply H0 in H2;
    destruct H2 as [s1 [s2 [acts [Hint_reply Hvalid]]]];
      exists s1, s2;
      eexists;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
      try rewrite app_nil_r; auto;
      eapply composed_lts.Step_Initial_Call; eauto;
      eapply composed_lts.Step_None; eauto.
  - destruct act.
  - destruct act.
  - unfold inv_ret_with_reachable. intros.
    rename H2 into H1.
    rename H3 into H2.
    destruct (eq_nat_dec pid pid0).
      subst.
      inversion H1; subst.
      simpl in H2.
      inversion H3; subst;
      simpl in H2;
      inversion H4; subst;
      simpl in H2;
      assert (Htmp : pid0 # (remove pc pid0)) by (apply ok_remove_notin; auto);
      apply binds_in in H2;
      unfold "#" in Htmp; intuition.
    inversion H1; subst.
    inversion H3; subst.
    inversion H4; subst;
    simpl in H2;
    apply remove_preserves_binds_notin in H2; auto;
    apply H0 in H2;
    destruct H2 as [s1 [s2 [acts [Hint_reply Hvalid]]]];
      exists s1, s2;
      eexists;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
      try rewrite app_nil_r; auto;
      eapply composed_lts.Step_Final_Return; eauto;
      eapply composed_lts.Step_None; eauto.
  - unfold inv_ret_with_reachable. intros.
    rename H2 into H1.
    rename H3 into H2.
    destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H1; subst.
      inversion H3; subst.
      inversion H5; subst;
      eapply substitute_eq_binds_v' in Hbinds1;
      unfold binds in Hbinds1;
      simpl in H2;
      erewrite H2 in Hbinds1;
      discriminate.
    -- specialize (H0 pid0 ret).
      inversion H1; subst.
      inversion H3; subst.
      inversion H5; subst;
      apply substitute_neq_preserves_binds' in H2; auto;
      intuition;
      destruct H6 as [s1 [s2 [acts [Hstep Hvalid]]]];
      exists s1, s2;
      eexists;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
      eapply composed_lts.Step_Internal_Query; eauto;
      eapply composed_lts.Step_None; eauto.
  - unfold inv_ret_with_reachable. intros.
    rename H2 into H1.
    rename H3 into H2.
    destruct (eq_nat_dec pid pid0).
    -- subst.
      exists st, st'.
      exists [].
      inversion H1; subst.
      inversion H4; subst.
      inversion H5; subst; simpl in *.
      intuition.
      2 : {
        eapply composed_lts.Step_None; eauto.
      }
      eapply substitute_eq_binds_v' with (v':=(AEnq3 ret0)) in Hbinds1.
      unfold binds in Hbinds1.
      rewrite H2 in Hbinds1.
      inversion Hbinds1; subst.
      assumption.
      eapply substitute_eq_binds_v' with (v':=(AEnq3 ret0)) in Hbinds1.
      unfold binds in Hbinds1.
      rewrite H2 in Hbinds1.
      inversion Hbinds1; subst.
      unfold get_rear.
      simpl in *.
      inversion H3; subst; simpl in *.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      inversion H7; subst; simpl in *.
      inversion H10; subst; simpl in *.
      inversion H9; subst; simpl in *.
      assumption.
      all : eapply substitute_eq_binds_v' in Hbinds1;
      unfold binds in Hbinds1;
      simpl in H2;
      erewrite H2 in Hbinds1;
      discriminate.
    -- specialize (H0 pid0 ret).
      inversion H1; subst.
      inversion H4; subst.
      inversion H5; subst;
      apply substitute_neq_preserves_binds' in H2; auto;
      intuition;
      destruct H6 as [s1 [s2 [acts [Hstep Hvalid]]]];
      exists s1, s2;
      eexists;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto.
Qed.

Definition inv_ret_step (s : composed_lts.state (composed_array_queue L)) :=
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
  forall pid ret,
      binds pid (AEnq2) pc ->
       binds pid (CntReadOk ret) rear.(Counter.responses) ->
    exists s1 s2 acts,
      composed_lts.step_L1
        (composed_array_queue L)
        s1 pid
          (@Tensor.intL2 li_array li_cnt_cnt (array L) ArrayQueue.front_rear
            (@Tensor.intL2 li_counter li_counter counter counter (int_cnt_read)))
        s2 /\
      composed_lts.valid_execution_fragment (composed_array_queue L) s2 s acts /\
      ret <= rear.(Counter.value).

Lemma inv_ret_inv':
  composed_lts.invariant_ind (composed_array_queue L)
  inv_ret_step.
Proof.
  unfold composed_lts.invariant_ind. intuition.
  - inversion H0; subst.
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
    unfold inv_ret_step.
    rewrite H10.
    rewrite H23.
    unfold new_array_queue.
    unfold new_counter.
    simpl.
    intros. intuition.
    inversion H24.
  - unfold inv_ret_step. intros.
    unfold inv_ret_step in H0.
    inversion H1; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *.
    -- inversion H6; subst; simpl in *.
      inversion H7; subst; simpl in *.
      --- inversion H8; subst; simpl in *.
        inversion H9; subst; simpl in *.
        + apply binds_push_inv in H3.
          intuition.
          ++ discriminate.
          ++ eapply H0 in H11; eauto.
            destruct H11 as [s1 [s2 [acts [Hstep Hvalid]]]].
            exists s1, s2.
            eexists.
            intuition.
            eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
            eapply composed_lts.Step_Internal_L1; eauto.
            eapply composed_lts.Step_None; eauto.
        + apply binds_push_inv in H3.
          intuition.
          ++ inversion H11; subst.
            eexists.
            eexists.
            eexists.
            intuition.
            apply H1.
            eapply composed_lts.Step_None; eauto.
          ++ eapply H0 in H11; eauto.
            destruct H11 as [s1 [s2 [acts [Hstep Hvalid]]]].
            exists s1, s2.
            eexists.
            intuition.
            eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
            eapply composed_lts.Step_Internal_L1; eauto.
            eapply composed_lts.Step_None; eauto.
      --- eapply H0 in H3; eauto.
        destruct H3 as [s1 [s2 [acts [Hstep Hvalid]]]].
        exists s1, s2.
        eexists.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
        eapply composed_lts.Step_Internal_L1; eauto.
        eapply composed_lts.Step_None; eauto.
    -- eapply H0 in H3; eauto.
      destruct H3 as [s1 [s2 [acts [Hstep Hvalid]]]].
      exists s1, s2.
      eexists.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
      eapply composed_lts.Step_Internal_L1; eauto.
      eapply composed_lts.Step_None; eauto.
  - unfold inv_ret_step. intros.
    unfold inv_ret_step in H0.
    destruct (eq_nat_dec pid pid0).
    subst.
    inversion H1; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *;
    eapply substitute_eq_binds_v' in Hbinds0;
    unfold binds in Hbinds0;
    simpl in *;
    rewrite H2 in Hbinds0;
    discriminate.
    inversion H1; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *;
    apply substitute_neq_preserves_binds' in H2; auto;
    eapply H0 in H3; eauto;
    destruct H3 as [s1 [s2 [acts [Hstep Hvalid]]]];
    exists s1, s2;
    eexists;
    intuition;
    eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
    eapply composed_lts.Step_Internal_L2; eauto;
    eapply composed_lts.Step_None; eauto.
  - unfold inv_ret_step. intros.
    unfold inv_ret_step in H0.
    destruct (eq_nat_dec pid pid0).
    subst.
    inversion H1; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *;
    apply binds_push_eq_inv in H2; discriminate.
    inversion H1; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *;
    apply binds_push_neq_inv in H2; auto;
    eapply H0 in H3; eauto;
    destruct H3 as [s1 [s2 [acts [Hstep Hvalid]]]];
    exists s1, s2;
    eexists;
    intuition;
    eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
    eapply composed_lts.Step_Initial_Call; eauto;
    eapply composed_lts.Step_None; eauto.
  - destruct act.
  - destruct act.
  - unfold inv_ret_step. intros.
    unfold inv_ret_step in H0.
    destruct (eq_nat_dec pid pid0).
    subst.
    inversion H1; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *;
    assert (Htmp : pid0 # (remove pc pid0)) by (apply ok_remove_notin; auto);
    apply binds_in in H2;
    unfold "#" in Htmp;
    intuition.
    inversion H1; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *;
    apply remove_preserves_binds_notin in H2; auto;
    eapply H0 in H3; eauto;
    destruct H3 as [s1 [s2 [acts [Hstep Hvalid]]]];
    exists s1, s2;
    eexists;
    intuition;
    eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
    eapply composed_lts.Step_Final_Return; eauto;
    eapply composed_lts.Step_None; eauto.
  - unfold inv_ret_step. intros.
    unfold inv_ret_step in H0.
    destruct (eq_nat_dec pid pid0).
    subst.
    *
    inversion H1; subst; simpl in *.
    inversion H5; subst; simpl in *.
    inversion H6; subst; simpl in *.
    -- inversion H7; subst; simpl in *.
      inversion H8; subst; simpl in *.
      --- inversion H9; subst; simpl in *.
        inversion H10; subst; simpl in *;
        apply binds_in in H3;
          unfold "#" in Hnotin_res;
          intuition.
      --- inversion H4; subst; simpl in *.
        inversion H10; subst; simpl in *;
        eapply substitute_eq_binds_v' in Hbinds0;
        unfold binds in H2;
        rewrite Hbinds0 in H2;
        discriminate.
    -- inversion H4; subst; simpl in *.
      inversion H8; subst; simpl in *;
        eapply substitute_eq_binds_v' in Hbinds0;
        unfold binds in H2;
        rewrite Hbinds0 in H2;
        discriminate.
    * inversion H1; subst; simpl in *.
      inversion H4; subst; simpl in *.
      inversion H6; subst; simpl in *.
      all : try (apply substitute_neq_preserves_binds' in H2; auto;
      inversion H5; subst; simpl in *;
      inversion H7; subst; simpl in *;
      inversion H9; subst; simpl in *;
      inversion H8; subst; simpl in *;
      inversion H11; subst; simpl in *;
      inversion H10; subst; simpl in *;
      eapply H0 in H3; eauto;
      destruct H3 as [s1 [s2 [acts [Hstep Hvalid]]]];
      exists s1, s2;
      eexists;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
      eapply composed_lts.Step_Internal_Query; eauto;
      eapply composed_lts.Step_None; eauto).
      all : try (apply substitute_neq_preserves_binds' in H2; auto;
      inversion H5; subst; simpl in *;
      inversion H7; subst; simpl in *;
      inversion H9; subst; simpl in *;
      eapply H0 in H3; eauto;
      destruct H3 as [s1 [s2 [acts [Hstep Hvalid]]]];
      exists s1, s2;
      eexists;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
      eapply composed_lts.Step_Internal_Query; eauto;
      eapply composed_lts.Step_None; eauto).
  - unfold inv_ret_step. intros.
    unfold inv_ret_step in H0.
    destruct (eq_nat_dec pid pid0).
    subst.
    inversion H1; subst; simpl in *.
    inversion H5; subst; simpl in *.
    inversion H6; subst; simpl in *;
      eapply substitute_eq_binds_v' in Hbinds0;
      unfold binds in H2;
      rewrite Hbinds0 in H2;
      discriminate.

    inversion H1; subst; simpl in *.
    inversion H5; subst; simpl in *.
    inversion H6; subst; simpl in *;
    apply substitute_neq_preserves_binds' in H2; auto.
    all : try (
    inversion H4; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H9; subst; simpl in *;
    inversion H8; subst; simpl in *;
    inversion H11; subst; simpl in *;
    inversion H10; subst; simpl in *;
    apply remove_preserves_binds_notin in H3; auto;
      eapply H0 in H3; eauto;
      destruct H3 as [s1 [s2 [acts [Hstep Hvalid]]]];
      exists s1, s2;
      eexists;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto).
    all : try (inversion H4; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H9; subst; simpl in *;
      eapply H0 in H3; eauto;
      destruct H3 as [s1 [s2 [acts [Hstep Hvalid]]]];
      exists s1, s2;
      eexists;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto).
    all : try (inversion H4; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H9; subst; simpl in *;
    inversion H8; subst; simpl in *;
    inversion H11; subst; simpl in *;
      eapply H0 in H3; eauto;
      destruct H3 as [s1 [s2 [acts [Hstep Hvalid]]]];
      exists s1, s2;
      eexists;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto).
Qed.

Lemma inv_ret_invariant:
  composed_lts.invariant (composed_array_queue L)
  inv_ret_step.
Proof.
  apply invariant_ind_to_invariant'.
  apply inv_ret_inv'.
Qed.

Definition inv_ret_step' (s : composed_lts.state (composed_array_queue L)) :=
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
  forall pid ret,
      binds pid (ADeq2) pc ->
       binds pid (CntReadOk ret) front.(Counter.responses) ->
    exists s1 s2 acts,
      composed_lts.step_L1
        (composed_array_queue L)
        s1 pid
          (@Tensor.intL2 li_array li_cnt_cnt (array L) ArrayQueue.front_rear
            (@Tensor.intL1 li_counter li_counter counter counter (int_cnt_read)))
        s2 /\
      composed_lts.valid_execution_fragment (composed_array_queue L) s2 s acts /\
      ret <= front.(Counter.value).

Lemma inv_ret_inv'':
  composed_lts.invariant_ind (composed_array_queue L)
  inv_ret_step'.
Proof.
  unfold composed_lts.invariant_ind. intuition.
  - inversion H0; subst.
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
    unfold inv_ret_step'.
    rewrite H10.
    rewrite H22.
    unfold new_array_queue.
    unfold new_counter.
    simpl.
    intros. intuition.
    inversion H24.
  - unfold inv_ret_step'. intros.
    unfold inv_ret_step' in H0.
    inversion H1; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *.
    -- inversion H6; subst; simpl in *.
      inversion H7; subst; simpl in *.
      --- eapply H0 in H3; eauto.
        destruct H3 as [s1 [s2 [acts [Hstep Hvalid]]]].
        exists s1, s2.
        eexists.
        intuition.
        eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
        eapply composed_lts.Step_Internal_L1; eauto.
        eapply composed_lts.Step_None; eauto.
      --- inversion H8; subst; simpl in *.
        inversion H9; subst; simpl in *.
        + apply binds_push_inv in H3.
          intuition.
          ++ discriminate.
          ++ eapply H0 in H11; eauto.
            destruct H11 as [s1 [s2 [acts [Hstep Hvalid]]]].
            exists s1, s2.
            eexists.
            intuition.
            eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
            eapply composed_lts.Step_Internal_L1; eauto.
            eapply composed_lts.Step_None; eauto.
        + apply binds_push_inv in H3.
          intuition.
          ++ inversion H11; subst.
            eexists.
            eexists.
            eexists.
            intuition.
            apply H1.
            eapply composed_lts.Step_None; eauto.
          ++ eapply H0 in H11; eauto.
            destruct H11 as [s1 [s2 [acts [Hstep Hvalid]]]].
            exists s1, s2.
            eexists.
            intuition.
            eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
            eapply composed_lts.Step_Internal_L1; eauto.
            eapply composed_lts.Step_None; eauto.
    -- eapply H0 in H3; eauto.
      destruct H3 as [s1 [s2 [acts [Hstep Hvalid]]]].
      exists s1, s2.
      eexists.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
      eapply composed_lts.Step_Internal_L1; eauto.
      eapply composed_lts.Step_None; eauto.
  - unfold inv_ret_step'. intros.
    unfold inv_ret_step' in H0.
    destruct (eq_nat_dec pid pid0).
    subst.
    inversion H1; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *;
    eapply substitute_eq_binds_v' in Hbinds0;
    unfold binds in Hbinds0;
    simpl in *;
    rewrite H2 in Hbinds0;
    discriminate.
    inversion H1; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *;
    apply substitute_neq_preserves_binds' in H2; auto;
    eapply H0 in H3; eauto;
    destruct H3 as [s1 [s2 [acts [Hstep Hvalid]]]];
    exists s1, s2;
    eexists;
    intuition;
    eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
    eapply composed_lts.Step_Internal_L2; eauto;
    eapply composed_lts.Step_None; eauto.
  - unfold inv_ret_step'. intros.
    unfold inv_ret_step' in H0.
    destruct (eq_nat_dec pid pid0).
    subst.
    inversion H1; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *;
    apply binds_push_eq_inv in H2; discriminate.
    inversion H1; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *;
    apply binds_push_neq_inv in H2; auto;
    eapply H0 in H3; eauto;
    destruct H3 as [s1 [s2 [acts [Hstep Hvalid]]]];
    exists s1, s2;
    eexists;
    intuition;
    eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
    eapply composed_lts.Step_Initial_Call; eauto;
    eapply composed_lts.Step_None; eauto.
  - destruct act.
  - destruct act.
  - unfold inv_ret_step'. intros.
    unfold inv_ret_step' in H0.
    destruct (eq_nat_dec pid pid0).
    subst.
    inversion H1; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *;
    assert (Htmp : pid0 # (remove pc pid0)) by (apply ok_remove_notin; auto);
    apply binds_in in H2;
    unfold "#" in Htmp;
    intuition.
    inversion H1; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *;
    apply remove_preserves_binds_notin in H2; auto;
    eapply H0 in H3; eauto;
    destruct H3 as [s1 [s2 [acts [Hstep Hvalid]]]];
    exists s1, s2;
    eexists;
    intuition;
    eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
    eapply composed_lts.Step_Final_Return; eauto;
    eapply composed_lts.Step_None; eauto.
  - unfold inv_ret_step'. intros.
    unfold inv_ret_step' in H0.
    destruct (eq_nat_dec pid pid0).
    subst.
    *
    inversion H1; subst; simpl in *.
    inversion H5; subst; simpl in *.
    inversion H6; subst; simpl in *.
    -- inversion H7; subst; simpl in *.
      inversion H8; subst; simpl in *.
      --- inversion H4; subst; simpl in *.
        inversion H10; subst; simpl in *;
        eapply substitute_eq_binds_v' in Hbinds0;
        unfold binds in H2;
        rewrite Hbinds0 in H2;
        discriminate.
      --- inversion H9; subst; simpl in *.
        inversion H10; subst; simpl in *;
        apply binds_in in H3;
          unfold "#" in Hnotin_res;
          intuition.
    -- inversion H4; subst; simpl in *.
      inversion H8; subst; simpl in *;
        eapply substitute_eq_binds_v' in Hbinds0;
        unfold binds in H2;
        rewrite Hbinds0 in H2;
        discriminate.
    * inversion H1; subst; simpl in *.
      inversion H4; subst; simpl in *.
      inversion H6; subst; simpl in *.
      all : try (apply substitute_neq_preserves_binds' in H2; auto;
      inversion H5; subst; simpl in *;
      inversion H7; subst; simpl in *;
      inversion H9; subst; simpl in *;
      inversion H8; subst; simpl in *;
      inversion H11; subst; simpl in *;
      inversion H10; subst; simpl in *;
      eapply H0 in H3; eauto;
      destruct H3 as [s1 [s2 [acts [Hstep Hvalid]]]];
      exists s1, s2;
      eexists;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
      eapply composed_lts.Step_Internal_Query; eauto;
      eapply composed_lts.Step_None; eauto).
      all : try (apply substitute_neq_preserves_binds' in H2; auto;
      inversion H5; subst; simpl in *;
      inversion H7; subst; simpl in *;
      inversion H9; subst; simpl in *;
      eapply H0 in H3; eauto;
      destruct H3 as [s1 [s2 [acts [Hstep Hvalid]]]];
      exists s1, s2;
      eexists;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
      eapply composed_lts.Step_Internal_Query; eauto;
      eapply composed_lts.Step_None; eauto).
  - unfold inv_ret_step'. intros.
    unfold inv_ret_step' in H0.
    destruct (eq_nat_dec pid pid0).
    subst.
    inversion H1; subst; simpl in *.
    inversion H5; subst; simpl in *.
    inversion H6; subst; simpl in *;
      eapply substitute_eq_binds_v' in Hbinds0;
      unfold binds in H2;
      rewrite Hbinds0 in H2;
      discriminate.

    inversion H1; subst; simpl in *.
    inversion H5; subst; simpl in *.
    inversion H6; subst; simpl in *;
    apply substitute_neq_preserves_binds' in H2; auto.
    all : try (
    inversion H4; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H9; subst; simpl in *;
    inversion H8; subst; simpl in *;
    inversion H11; subst; simpl in *;
    inversion H10; subst; simpl in *;
    apply remove_preserves_binds_notin in H3; auto;
      eapply H0 in H3; eauto;
      destruct H3 as [s1 [s2 [acts [Hstep Hvalid]]]];
      exists s1, s2;
      eexists;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto).
    all : try (inversion H4; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H9; subst; simpl in *;
      eapply H0 in H3; eauto;
      destruct H3 as [s1 [s2 [acts [Hstep Hvalid]]]];
      exists s1, s2;
      eexists;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto).
    all : try (inversion H4; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H9; subst; simpl in *;
    inversion H8; subst; simpl in *;
    inversion H11; subst; simpl in *;
      eapply H0 in H3; eauto;
      destruct H3 as [s1 [s2 [acts [Hstep Hvalid]]]];
      exists s1, s2;
      eexists;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto).
Qed.

Lemma inv_ret_invariant':
  composed_lts.invariant (composed_array_queue L)
  inv_ret_step'.
Proof.
  apply invariant_ind_to_invariant'.
  apply inv_ret_inv''.
Qed.

Definition inv_rear (s : composed_lts.state (composed_array_queue L)) :=
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
  (forall pid, aqimpl.(ArrayQueueImpl.rear) pid <= rear.(Counter.value)) /\
  inv_ret_with_reachable s.

Lemma inv_rear_inv:
  composed_lts.invariant_ind (composed_array_queue L)
  inv_rear.
Proof.
  unfold inv_rear.
  apply invariant_ind''_imply_invariant_ind_land.
  unfold invariant_ind''. intuition.
  apply inv_ret_inv_with_reachble.
  unfold about. intuition.
  - inversion H0; subst.
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
    unfold inv_rear.
    rewrite H10.
    rewrite H23.
    unfold new_array_queue.
    unfold new_counter.
    simpl.
    intros.
    lia.
  - rename H1 into Hinv.
    rename H2 into H1.
    inversion H1; subst.
    inversion H2; subst.
    inversion H3; subst; simpl in *.
    -- inversion H4; subst;
      inversion H5; subst; simpl in *;
      inversion H6; subst;
        inversion H7; subst; simpl in *;
          unfold inv_rear in *;
          simpl in *;
          intros;
          specialize (H0 pid0);
          lia.
    -- inversion H4; subst.
      inversion H5; subst; simpl in *;
      unfold inv_rear in *;
        simpl in *;
        intros;
          specialize (H0 pid0);
          lia.
  - rename H1 into Hinv.
    rename H2 into H1.
    destruct (eq_nat_dec pid pid0).
    subst.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    rewrite Nat.eqb_refl.
    apply Hinv in Hbinds0.
    destruct Hbinds0 as [s1 [s2 [acts [Hint_reply [Hvalid [Hreach [Hb1 Hb2]]]]]]].
    generalize inv_ret_invariant; intro Hret.
    apply Hret in Hreach.
    eapply Hreach in Hb2; eauto.
    destruct Hb2 as [s3 [s4 [acts1 [Hstep [Hvalid1 Hle]]]]].
    eapply Nat.le_trans.
    eauto.
    eapply REAR_not_decrease in Hvalid.
    unfold get_rear in Hvalid.
    simpl in Hvalid.
    eapply Nat.le_trans.
    2 : {
      eauto.
    }
    eapply REAR_not_decrease.
    eapply composed_lts.Step_Internal_Reply; eauto.
    eapply composed_lts.Step_None; eauto.
    all : apply H0.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    assert (Htmp : pid0 <> pid) by intuition.
    apply Nat.eqb_neq in Htmp.
    rewrite Htmp.
    all : apply H0.
  - inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *;
    apply H0.
  - destruct act.
  - destruct act.
  - inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *;
    apply H0.
  - inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *.
    all : try (inversion H6; subst; simpl in *;
    inversion H8; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H10; subst; simpl in *;
    inversion H9; subst; simpl in *;
    apply H0).
    all : try (inversion H6; subst; simpl in *;
    inversion H8; subst; simpl in *;
    inversion H7; subst; simpl in *;
    apply H0).
  - inversion H2; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H5; subst; simpl in *.
    all : try (inversion H6; subst; simpl in *;
    inversion H8; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H10; subst; simpl in *;
    inversion H9; subst; simpl in *;
    apply H0).
    all : try (inversion H6; subst; simpl in *;
    inversion H8; subst; simpl in *;
    inversion H7; subst; simpl in *;
    apply H0).
Qed.

Lemma inv_rear_invariant:
  composed_lts.invariant (composed_array_queue L)
  inv_rear.
Proof.
  apply invariant_ind_to_invariant'.
  apply inv_rear_inv.
Qed.

Definition inv_ret_with_reachable' (s : composed_lts.state (composed_array_queue L)) :=
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
  (forall pid ret,
    binds pid (ADeq3 ret) pc ->
    exists s1 s2 acts,
      composed_lts.internal_reply
        (composed_array_queue L)
        s1 pid
          (@Tensor.replyR li_array li_cnt_cnt
            (@Tensor.replyL li_counter li_counter (CntReadOk ret)))
        s2 /\
      composed_lts.valid_execution_fragment (composed_array_queue L) s2 s acts /\
      composed_lts.reachable (composed_array_queue L) s1 /\
      binds pid (ADeq2) (get_pc s1) /\
       binds pid (CntReadOk ret) (get_front s1).(Counter.responses)
      ) /\
      composed_lts.reachable (composed_array_queue L) s.

Lemma inv_ret_inv_with_reachble':
  composed_lts.invariant_ind (composed_array_queue L)
  inv_ret_with_reachable'.
Proof.
  unfold inv_ret_with_reachable'.
  apply invariant_ind''_imply_invariant_ind_land.
  unfold invariant_ind''. intuition.
  apply reachable_is_invariant.
  unfold about.
  intuition; rename H1 into Hbinds.
  - inversion H0; subst.
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
    rewrite H10 in Hbinds.
    intros.
    unfold new_array_queue in Hbinds.
    inversion Hbinds.
  - unfold inv_ret_with_reachable. intros.
    rename H2 into H1.
    rename H3 into H2.
      inversion H1; subst.
      simpl in H2.
      unfold inv_ret in H0.
      apply H0 in H2.
      destruct H2 as [s1 [s2 [acts [Hint_reply Hvalid]]]].
      exists s1, s2, acts.
      intuition.
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto.
      eapply composed_lts.Step_Internal_L1; eauto.
      eapply composed_lts.Step_None; eauto.
      rewrite app_nil_r.
      reflexivity.
  - unfold inv_ret_with_reachable. intros.
    rename H2 into H1.
    rename H3 into H2.
    destruct (eq_nat_dec pid pid0).
      subst.
      inversion H1; subst.
      simpl in H2.
      inversion H3; subst.
      simpl in H2.
      inversion H4; subst;
      simpl in H2;
      eapply substitute_eq_binds_v' in Hbinds1; eauto;
      unfold binds in Hbinds1;
      erewrite H2 in Hbinds1;
      discriminate.
    inversion H1; subst.
    inversion H3; subst.
    inversion H4; subst;
    apply substitute_neq_preserves_binds' in H2; auto;
    apply H0 in H2;
    destruct H2 as [s1 [s2 [acts [Hint_reply Hvalid]]]];
      exists s1, s2, acts;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts) (a':=[]); eauto;
      try rewrite app_nil_r; auto;
      eapply composed_lts.Step_Internal_L2; eauto;
      eapply composed_lts.Step_None; eauto.
  - unfold inv_ret_with_reachable. intros.
    rename H2 into H1.
    rename H3 into H2.
    destruct (eq_nat_dec pid pid0).
      subst.
      inversion H1; subst.
      simpl in H2.
      inversion H3; subst.
      simpl in H2.
      inversion H4; subst;
      simpl in H2;
      apply binds_push_eq_inv in H2; discriminate.
    inversion H1; subst.
    inversion H3; subst.
    inversion H4; subst;
    simpl in H2;
    apply binds_push_neq_inv in H2; auto;
    apply H0 in H2;
    destruct H2 as [s1 [s2 [acts [Hint_reply Hvalid]]]];
      exists s1, s2;
      eexists;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
      try rewrite app_nil_r; auto;
      eapply composed_lts.Step_Initial_Call; eauto;
      eapply composed_lts.Step_None; eauto.
  - destruct act.
  - destruct act.
  - unfold inv_ret_with_reachable. intros.
    rename H2 into H1.
    rename H3 into H2.
    destruct (eq_nat_dec pid pid0).
      subst.
      inversion H1; subst.
      simpl in H2.
      inversion H3; subst;
      simpl in H2;
      inversion H4; subst;
      simpl in H2;
      assert (Htmp : pid0 # (remove pc pid0)) by (apply ok_remove_notin; auto);
      apply binds_in in H2;
      unfold "#" in Htmp; intuition.
    inversion H1; subst.
    inversion H3; subst.
    inversion H4; subst;
    simpl in H2;
    apply remove_preserves_binds_notin in H2; auto;
    apply H0 in H2;
    destruct H2 as [s1 [s2 [acts [Hint_reply Hvalid]]]];
      exists s1, s2;
      eexists;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
      try rewrite app_nil_r; auto;
      eapply composed_lts.Step_Final_Return; eauto;
      eapply composed_lts.Step_None; eauto.
  - unfold inv_ret_with_reachable. intros.
    rename H2 into H1.
    rename H3 into H2.
    destruct (eq_nat_dec pid pid0).
    -- subst.
      inversion H1; subst.
      inversion H3; subst.
      inversion H5; subst;
      eapply substitute_eq_binds_v' in Hbinds1;
      unfold binds in Hbinds1;
      simpl in H2;
      erewrite H2 in Hbinds1;
      discriminate.
    -- specialize (H0 pid0 ret).
      inversion H1; subst.
      inversion H3; subst.
      inversion H5; subst;
      apply substitute_neq_preserves_binds' in H2; auto;
      intuition;
      destruct H6 as [s1 [s2 [acts [Hstep Hvalid]]]];
      exists s1, s2;
      eexists;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
      eapply composed_lts.Step_Internal_Query; eauto;
      eapply composed_lts.Step_None; eauto.
  - unfold inv_ret_with_reachable'. intros.
    rename H2 into H1.
    rename H3 into H2.
    destruct (eq_nat_dec pid pid0).
    -- subst.
      exists st, st'.
      exists [].
      inversion H1; subst.
      inversion H4; subst.
      inversion H5; subst; simpl in *.

      all : pose proof Hbinds1 as Hbinds1';
      eapply substitute_eq_binds_v' in Hbinds1;
      unfold binds in Hbinds1;
      simpl in H2;
      erewrite H2 in Hbinds1;
      try discriminate.
      intuition.
      2 : {
        eapply composed_lts.Step_None; eauto.
      }
      inversion Hbinds1; subst.
      auto.
      unfold get_front.
      simpl in *.
      inversion H3; subst; simpl in *.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *.
      inversion H7; subst; simpl in *.
      inversion H10; subst; simpl in *.
      inversion H9; subst; simpl in *.
      inversion Hbinds1; subst.
      assumption.
    -- specialize (H0 pid0 ret).
      inversion H1; subst.
      inversion H4; subst.
      inversion H5; subst;
      apply substitute_neq_preserves_binds' in H2; auto;
      intuition;
      destruct H6 as [s1 [s2 [acts [Hstep Hvalid]]]];
      exists s1, s2;
      eexists;
      intuition;
      eapply composed_lts.valid_execution_fragment_join' with (a:=acts); eauto;
      eapply composed_lts.Step_Internal_Reply; eauto;
      eapply composed_lts.Step_None; eauto.
Qed.

Definition inv_front (s : composed_lts.state (composed_array_queue L)) :=
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
  (forall pid, aqimpl.(ArrayQueueImpl.front) pid <= front.(Counter.value)) /\
  inv_ret_with_reachable' s.

Lemma inv_front_inv:
  composed_lts.invariant_ind (composed_array_queue L)
  inv_front.
Proof.
  unfold inv_front.
  apply invariant_ind''_imply_invariant_ind_land.
  unfold invariant_ind''. intuition.
  apply inv_ret_inv_with_reachble'.
  unfold about. intuition.
  - inversion H0; subst.
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
    unfold inv_front.
    rewrite H10.
    rewrite H22.
    unfold new_array_queue.
    unfold new_counter.
    simpl.
    intros.
    lia.
  - rename H1 into Hinv.
    rename H2 into H1.
    inversion H1; subst.
    inversion H2; subst.
    inversion H3; subst; simpl in *.
    -- inversion H4; subst;
      inversion H5; subst; simpl in *;
      inversion H6; subst;
        inversion H7; subst; simpl in *;
          unfold inv_rear in *;
          simpl in *;
          intros;
          specialize (H0 pid0);
          lia.
    -- inversion H4; subst.
      inversion H5; subst; simpl in *;
      unfold inv_rear in *;
        simpl in *;
        intros;
          specialize (H0 pid0);
          lia.
  - rename H1 into Hinv.
    rename H2 into H1.
    destruct (eq_nat_dec pid pid0).
    subst.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    all : try apply H0.
    rewrite Nat.eqb_refl.
    apply Hinv in Hbinds0.
    destruct Hbinds0 as [s1 [s2 [acts [Hint_reply [Hvalid [Hreach [Hb1 Hb2]]]]]]].
    generalize inv_ret_invariant'; intro Hret.
    apply Hret in Hreach.
    eapply Hreach in Hb2; eauto.
    destruct Hb2 as [s3 [s4 [acts1 [Hstep [Hvalid1 Hle]]]]].
    eapply Nat.le_trans.
    eauto.
    eapply FRONT_not_decrease in Hvalid.
    unfold get_front in Hvalid.
    simpl in Hvalid.
    eapply Nat.le_trans.
    2 : {
      eauto.
    }
    eapply FRONT_not_decrease.
    eapply composed_lts.Step_Internal_Reply; eauto.
    eapply composed_lts.Step_None; eauto.
    all : apply H0.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.

    all : try apply H0.
    assert (Htmp : pid0 <> pid) by intuition.
    apply Nat.eqb_neq in Htmp.
    rewrite Htmp.
    apply H0.
  - inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *;
    apply H0.
  - destruct act.
  - destruct act.
  - inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *;
    apply H0.
  - inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *.
    all : try (inversion H6; subst; simpl in *;
    inversion H8; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H10; subst; simpl in *;
    inversion H9; subst; simpl in *;
    apply H0).
    all : try (inversion H6; subst; simpl in *;
    inversion H8; subst; simpl in *;
    inversion H7; subst; simpl in *;
    apply H0).
  - inversion H2; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H5; subst; simpl in *.
    all : try (inversion H6; subst; simpl in *;
    inversion H8; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H10; subst; simpl in *;
    inversion H9; subst; simpl in *;
    apply H0).
    all : try (inversion H6; subst; simpl in *;
    inversion H8; subst; simpl in *;
    inversion H7; subst; simpl in *;
    apply H0).
Qed.

Lemma inv_front_invariant:
  composed_lts.invariant (composed_array_queue L)
  inv_front.
Proof.
  apply invariant_ind_to_invariant'.
  apply inv_front_inv.
Qed.

Fixpoint get_r' pc res_ary res_rear : nat :=
  match pc with
  | nil => O
  | (pid, p) :: pc' =>
    let r' := get_r' pc' res_ary res_rear in
    match p with
    | AEnq28 => match get pid res_ary with
                | None => r'
                | Some res => match res with
                              | AryCASOk b => if b then (S r') else r'
                              | AryReadOk _ => r'
                              end
                end
    | AEnq29 ret => if ret then (S r') else r'
    | AEnq30 => (S r')
    | AEnq31 => match get pid res_rear with
                | None => (S r')
                | Some res => match res with
                              | CntIncOk => r'
                              | CntReadOk _ => (S r') (* unreachable *)
                              end
                end
    | _ => r'
    end
  end.



Lemma get_r'_dist: forall pc pc' res_ary res_rear,
  get_r' (pc ++ pc') res_ary res_rear =
  get_r' (pc) res_ary res_rear +
  get_r' (pc') res_ary res_rear.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - destruct a.
    match_if'; rewrite IHpc; auto.
Qed.

Lemma get_r'_binds_AEnq3_substitute_AEnq4: forall pc pid ret res_ary res_rear,
  ok pc ->
  binds pid (AEnq3 ret) pc ->
  get_r' (substitute pc pid AEnq4) res_ary res_rear =
  get_r' pc res_ary res_rear.
Proof.
  intros.
  apply binds_reconstruct in H1.
  destruct H1 as [l1 [l2 Hlist]].
  rewrite Hlist in H0.
  rewrite Hlist.
  apply ok_remove_middle_inv in H0.
  rewrite substitute_notin_app; intuition.
  repeat rewrite get_r'_dist.
  simpl.
  rewrite Nat.eqb_refl.
  simpl.
  reflexivity.
Qed.

Lemma get_r'_any_ary: forall pc res_ary res_rear pid v,
  pid # pc ->
  get_r' pc ((pid, v) :: res_ary) res_rear =
  get_r' pc res_ary res_rear.
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

Lemma get_r'_any_ary_cas_false: forall pc res_ary res_rear pid,
  pid # res_ary ->
  get_r' pc ((pid, AryCASOk false) :: res_ary) res_rear =
  get_r' pc res_ary res_rear.
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

Lemma get_r'_any_ary_read: forall pc res_ary res_rear pid v,
  pid # res_ary ->
  get_r' pc ((pid, AryReadOk v) :: res_ary) res_rear =
  get_r' pc res_ary res_rear.
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

Lemma get_r'_any_rear_read: forall pc res_ary res_rear pid v,
  pid # res_rear ->
  get_r' pc res_ary ((pid, CntReadOk v) :: res_rear) =
  get_r' pc res_ary res_rear.
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

Lemma get_r'_any_rear_push: forall pc res_ary res_rear pid v,
  pid # pc ->
  get_r' pc res_ary ((pid, v) :: res_rear) =
  get_r' pc res_ary res_rear.
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

Lemma get_r'_any_rear_remove: forall pc res_ary res_rear pid,
  ok pc ->
  pid # pc ->
  get_r' pc res_ary (remove res_rear pid) =
  get_r' pc res_ary res_rear.
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

Lemma get_r'_any_ary_remove: forall pc res_ary res_rear pid,
  ok pc ->
  pid # pc ->
  get_r' pc (remove res_ary pid) res_rear =
  get_r' pc res_ary res_rear.
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

Lemma get_r'_any_ary': forall pc res_ary res_rear pid v,
  pid # res_ary ->
  get_r' pc res_ary res_rear <=
  get_r' pc ((pid, v) :: res_ary) res_rear.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - destruct a. simpl in *.
    destruct a; simpl; match_if';
    try apply le_n_S;
    try apply IHpc; auto.
    apply Nat.eqb_eq in Heqb. subst.
    apply binds_in in Heqo.
    unfold "#" in H0.
    intuition.
    apply Nat.eqb_eq in Heqb. subst.
    apply binds_in in Heqo.
    unfold "#" in H0.
    intuition.
Qed.

Definition get_ary (s : composed_lts.state (composed_array_queue L)) :=
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
  ary.

Definition R (s : composed_lts.state (composed_array_queue L)) :=
  let rear := get_rear s in
  let ary := get_ary s in
  let pc := get_pc s in
  rear.(Counter.value) + get_r' pc ary.(Array.responses L) rear.(Counter.responses).

Definition inv_e31 (s : composed_lts.state (composed_array_queue L)) :=
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
      binds pid (AEnq31) pc ->
        pid # rear.(Counter.responses) ->
       rear.(Counter.value) < R s) /\
  composed_lts.reachable (composed_array_queue L) s.

Definition array_queue_wf (s : composed_lts.state (composed_array_queue L)) :=
  let sync_aqimpl := s.(Compose.L2State) in
  let aqimpl := sync_aqimpl.(LState) in
  let pc := aqimpl.(pc) in
  ok pc.

Lemma array_queue_wf_inv: composed_lts.invariant_ind (composed_array_queue L) array_queue_wf.
Proof.
  unfold array_queue_wf.
  unfold composed_lts.invariant_ind. intuition.
  - inversion H0; subst.
    inversion H2; subst.
    inversion H3; subst.
    rewrite H6.
    unfold new_array_queue.
    simpl.
    econstructor.
  - inversion H1; subst; simpl in *; intuition.
  - inversion H1; subst.
    inversion H2; subst.
    inversion H3; subst; simpl in *;
    apply substitute_preserves_ok; auto.
  - inversion H1; subst.
    inversion H2; subst.
    inversion H3; subst; simpl in *;
    econstructor; eauto.
  - destruct act.
  - destruct act.
  - inversion H1; subst.
    inversion H2; subst.
    inversion H3; subst; simpl in *;
    apply remove_preserves_ok; auto.
  - inversion H1; subst.
    inversion H2; subst.
    inversion H3; subst.
    inversion H4; subst; simpl in *;
    apply substitute_preserves_ok; auto.
  - inversion H1; subst.
    inversion H2; subst.
    inversion H3; subst.
    inversion H5; subst; simpl in *;
    apply substitute_preserves_ok; auto.
Qed.

Lemma array_queue_wf_invarint: composed_lts.invariant (composed_array_queue L) array_queue_wf.
Proof.
  apply invariant_ind_to_invariant'.
  apply array_queue_wf_inv.
Qed.

Lemma inv_e31_inv:
  composed_lts.invariant_ind (composed_array_queue L)
  inv_e31.
Proof.
  unfold inv_e31.
  apply invariant_ind''_imply_invariant_ind_land.
  unfold invariant_ind''. intuition.
  apply reachable_is_invariant.
  unfold about. intuition.
  - rename H1 into Hb1.
    rename H2 into Hb2.
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
    rewrite H10 in Hb1.
    unfold new_array_queue in Hb1.
    simpl in *.
    intuition.
    inversion Hb1.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb1.
    rename H4 into Hb2.
    unfold inv_e31 in *. intros.
    destruct (eq_nat_dec pid pid0).
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *.
    inversion H6; subst; simpl in *;
    inversion H7; subst; simpl in *;
    apply notin_union in Hb2;
    destruct Hb2 as [Hb21 Hb22];
    apply notin_neq in Hb21; intuition.
    apply H0 in Hb2; auto.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *;
    apply H0 in Hb2; auto;
    eapply Nat.lt_stepr; eauto;
    unfold R; simpl;
    unfold get_rear; simpl;
    unfold get_pc; simpl;
    f_equal;
    apply array_queue_wf_invarint in Hreach;
    unfold array_queue_wf in Hreach; simpl in Hreach;
    apply binds_reconstruct in Hb1;
    destruct Hb1 as [l1 [l2 Hlist]];
    rewrite Hlist in Hreach;
    apply ok_remove_middle_inv in Hreach;
    rewrite Hlist;
    repeat rewrite get_r'_dist;
    simpl;
    repeat rewrite get_r'_any_ary; intuition.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *.
    inversion H6; subst; simpl in *.
    inversion H7; subst; simpl in *.
    apply notin_union in Hb2;
    destruct Hb2 as [Hb21 Hb22];
    apply notin_neq in Hb21; intuition.
    unfold R. simpl.
    rewrite <-plus_Sn_m.
    unfold get_pc. simpl get_pc.
    simpl pc.
    apply array_queue_wf_invarint in Hreach.
    unfold array_queue_wf in Hreach; simpl in Hreach.
    apply binds_reconstruct in Hb1.
    destruct Hb1 as [l1 [l2 Hlist]];
    rewrite Hlist in Hreach.
    apply ok_remove_middle_inv in Hreach;
    rewrite Hlist;
    repeat rewrite get_r'_dist.
    simpl.
    assert (Htmp : pid0 =? pid = false) by
    (apply Nat.eqb_neq; intuition).
    rewrite Htmp.
    apply notin_get_none in Hb22.
    rewrite Hb22. lia.
    apply notin_union in Hb2;
    destruct Hb2 as [Hb21 Hb22];
    apply notin_neq in Hb21; intuition.
    apply H0 in Hb1; auto.
    eapply Nat.lt_stepr; eauto.
    unfold R. simpl.
    f_equal.
    unfold get_pc. simpl.
    unfold get_ary. simpl.
    rewrite get_r'_any_rear_read; auto.
    apply H0 in Hb1; auto.
    apply H0 in Hb1; auto.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *;
    eapply Nat.lt_le_trans; eauto;
    unfold R; simpl;
    unfold get_rear; simpl;
    unfold get_pc; simpl;
    generalize get_r'_any_ary'; intro Hary;
    apply add_le_mono_l_proj_l2r; auto;
    eapply Hary in Hnotin_res.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb1.
    rename H4 into Hb2.
    destruct (eq_nat_dec pid pid0).
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    eapply substitute_eq_binds_v' in Hbinds0;
    unfold binds in Hbinds0;
    rewrite Hb1 in Hbinds0; discriminate.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply substitute_neq_preserves_binds' in Hb1; auto;
    apply H0 in Hb1; auto;
    eapply Nat.lt_stepr; eauto;
    unfold R;
    unfold get_rear;
    unfold get_pc;
    unfold get_ary;
    simpl in *;
    f_equal;
    apply binds_reconstruct in Hbinds0;
    destruct Hbinds0 as [l1 [l2 Hlist]];
    rewrite Hlist in Hok_pc;
    rewrite Hlist;
    apply ok_remove_middle_inv in Hok_pc;
    rewrite substitute_notin_app; intuition;
    repeat rewrite get_r'_dist;
    simpl;
    rewrite Nat.eqb_refl;
    simpl;
    reflexivity.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb1.
    rename H4 into Hb2.
    destruct (eq_nat_dec pid pid0).
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply binds_push_eq_inv in Hb1; discriminate.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply binds_push_neq_inv in Hb1; auto;
    apply H0 in Hb1; auto;
    eapply Nat.lt_stepr; eauto;
    unfold R;
    unfold get_rear;
    unfold get_pc;
    unfold get_ary;
    simpl in *;
    f_equal;
    apply binds_reconstruct in Hbinds0;
    destruct Hbinds0 as [l1 [l2 Hlist]];
    rewrite Hlist in Hok_pc;
    rewrite Hlist;
    apply ok_remove_middle_inv in Hok_pc;
    rewrite substitute_notin_app; intuition;
    repeat rewrite get_r'_dist;
    simpl;
    rewrite Nat.eqb_refl;
    simpl;
    reflexivity.
  - destruct act.
  - destruct act.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb1.
    rename H4 into Hb2.
    destruct (eq_nat_dec pid pid0).
    subst.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    assert (Htmp : pid0 # (remove pc pid0)) by
    (apply ok_remove_notin; auto);
    apply binds_in in Hb1;
    unfold "#" in Htmp; intuition.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *;
    apply remove_preserves_binds_notin in Hb1; auto;
    apply H0 in Hb1; auto;
    eapply Nat.lt_stepr; eauto;
    unfold R;
    unfold get_rear;
    unfold get_pc;
    unfold get_ary;
    simpl in *;
    f_equal;
    apply binds_reconstruct in Hbinds0;
    destruct Hbinds0 as [l1 [l2 Hlist]];
    rewrite Hlist in Hok_pc;
    rewrite Hlist;
    apply ok_remove_middle_inv in Hok_pc;
    rewrite remove_notin_app; intuition;
    repeat rewrite get_r'_dist;
    simpl;
    rewrite Nat.eqb_refl;
    simpl;
    reflexivity.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb1.
    rename H4 into Hb2.
    destruct (eq_nat_dec pid pid0).
    subst.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H4; subst; simpl in *;
    try (eapply substitute_eq_binds_v' in Hbinds0;
    unfold binds in Hbinds0;
    rewrite Hb1 in Hbinds0;
    discriminate).
    unfold R.
    unfold get_pc, get_ary, get_rear.
    simpl.
    apply binds_reconstruct in Hbinds0;
    destruct Hbinds0 as [l1 [l2 Hlist]];
    rewrite Hlist in Hok_pc;
    rewrite Hlist;
    apply ok_remove_middle_inv in Hok_pc;
    rewrite substitute_notin_app; intuition;
    repeat rewrite get_r'_dist;
    simpl;
    rewrite Nat.eqb_refl;
    simpl.
    apply notin_get_none in Hb2.
    rewrite Hb2. lia.
    --
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    inversion H4; subst; simpl in *.
    all : try (
    apply substitute_neq_preserves_binds' in Hb1; auto;
    inversion H3; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    inversion H9; subst; simpl in *;
    inversion H8; subst; simpl in *;
    apply H0 in Hb1; auto;
    eapply Nat.lt_stepr; eauto;
    unfold R;
    unfold get_rear;
    unfold get_pc;
    unfold get_ary;
    simpl in *;
    f_equal;
    apply binds_reconstruct in Hbinds0;
    destruct Hbinds0 as [l1 [l2 Hlist]];
    rewrite Hlist in Hok_pc;
    rewrite Hlist;
    apply ok_remove_middle_inv in Hok_pc;
    rewrite substitute_notin_app; intuition;
    repeat rewrite get_r'_dist;
    simpl;
    rewrite Nat.eqb_refl;
    simpl;
    reflexivity).
    all : try (
    apply substitute_neq_preserves_binds' in Hb1; auto;
    inversion H3; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    apply H0 in Hb1; auto;
    eapply Nat.lt_stepr; eauto;
    unfold R;
    unfold get_rear;
    unfold get_pc;
    unfold get_ary;
    simpl in *;
    f_equal;
    apply binds_reconstruct in Hbinds0;
    destruct Hbinds0 as [l1 [l2 Hlist]];
    rewrite Hlist in Hok_pc;
    rewrite Hlist;
    apply ok_remove_middle_inv in Hok_pc;
    rewrite substitute_notin_app; intuition;
    repeat rewrite get_r'_dist;
    simpl;
    rewrite Nat.eqb_refl;
    simpl;
    reflexivity).
    all : 
    apply substitute_neq_preserves_binds' in Hb1; auto;
    inversion H3; subst; simpl in *;
    inversion H5; subst; simpl in *.
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    apply H0 in Hb1; auto;
    eapply Nat.lt_stepr; eauto;
    unfold R;
    unfold get_rear;
    unfold get_pc;
    unfold get_ary;
    simpl in *;
    f_equal;
    apply binds_reconstruct in Hbinds0;
    destruct Hbinds0 as [l1 [l2 Hlist]];
    rewrite Hlist in Hok_pc;
    rewrite Hlist;
    apply ok_remove_middle_inv in Hok_pc;
    rewrite substitute_notin_app; intuition;
    repeat rewrite get_r'_dist;
    simpl;
    rewrite Nat.eqb_refl;
    simpl;
    apply notin_get_none in Hnotin_res;
    rewrite Hnotin_res;
    reflexivity.
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *.
    inversion H9; subst; simpl in *.
    inversion H8; subst; simpl in *.
    apply H0 in Hb1; auto.
    eapply Nat.lt_stepr; eauto;
    unfold R;
    unfold get_rear;
    unfold get_pc;
    unfold get_ary;
    simpl in *;
    f_equal;
    apply binds_reconstruct in Hbinds0;
    destruct Hbinds0 as [l1 [l2 Hlist]];
    rewrite Hlist in Hok_pc;
    rewrite Hlist;
    apply ok_remove_middle_inv in Hok_pc;
    rewrite substitute_notin_app; intuition;
    repeat rewrite get_r'_dist;
    simpl;
    rewrite Nat.eqb_refl;
    simpl;
    apply notin_get_none in Hnotin_res;
    rewrite Hnotin_res;
    reflexivity.
  - rename H1 into Hreach.
    rename H2 into H1.
    rename H3 into Hb1.
    rename H4 into Hb2.
    destruct (eq_nat_dec pid pid0).
    subst.
    --
    inversion H1; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *;
    try (eapply substitute_eq_binds_v' in Hbinds0;
    unfold binds in Hbinds0;
    rewrite Hb1 in Hbinds0;
    discriminate).
    --
    inversion H1; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *.
    all : try (apply substitute_neq_preserves_binds' in Hb1; auto;
    inversion H2; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    inversion H9; subst; simpl in *;
    inversion H8; subst; simpl in *;
    apply remove_neq_preserves_notin in Hb2; auto;
    apply H0 in Hb1; auto;
    eapply Nat.lt_stepr; eauto;
    unfold R;
    unfold get_rear;
    unfold get_pc;
    unfold get_ary;
    simpl in *;
    f_equal;
    apply binds_reconstruct in Hbinds0;
    destruct Hbinds0 as [l1 [l2 Hlist]];
    rewrite Hlist in Hok_pc;
    rewrite Hlist;
    apply ok_remove_middle_inv in Hok_pc;
    destruct Hok_pc as [Hok_pc1 Hok_pc2];
    apply ok_concat_inv in Hok_pc1;
    rewrite substitute_notin_app; intuition;
    repeat rewrite get_r'_dist;
    simpl;
    rewrite Nat.eqb_refl;
    simpl;
    repeat rewrite get_r'_any_rear_remove; intuition).
    all : try (apply substitute_neq_preserves_binds' in Hb1; auto;
    inversion H2; subst; simpl in *;
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
    inversion H6; subst; simpl in *;
    apply H0 in Hb1; auto;
    eapply Nat.lt_stepr; eauto;
    unfold R;
    unfold get_rear;
    unfold get_pc;
    unfold get_ary;
    simpl in *;
    f_equal;
    apply binds_reconstruct in Hbinds0;
    destruct Hbinds0 as [l1 [l2 Hlist]];
    rewrite Hlist in Hok_pc;
    rewrite Hlist;
    apply ok_remove_middle_inv in Hok_pc;
    destruct Hok_pc as [Hok_pc1 Hok_pc2];
    apply ok_concat_inv in Hok_pc1;
    rewrite substitute_notin_app; intuition;
    repeat rewrite get_r'_dist;
    simpl;
    rewrite Nat.eqb_refl;
    simpl;
    repeat rewrite get_r'_any_rear_remove; intuition;
    repeat rewrite get_r'_any_ary_remove; intuition).
    rewrite Hbinds4.
    match_if'.
    rewrite Hbinds6.
    match_if'.
Qed.

Lemma inv_e31_invariant:
  composed_lts.invariant (composed_array_queue L)
  inv_e31.
Proof.
  apply invariant_ind_to_invariant'.
  apply inv_e31_inv.
Qed.

End INV.