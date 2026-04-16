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
  KInduction
  ArrayQueue
  ArrayQueueImpl
  ArrayQueueMapping
  ArrayQueueProp
  ArrayQueueImplProp
  ArrayQueueImplProp2
  Queue
  ArrayQueueInvariant
  ArrayQueueInvariant2
  ArrayProp
  ArrayQueueInvariantBefore0
  ArrayQueueInvariantBefore02
  ArrayQueueInvariantBefore03
  ArrayQueueInvariantBefore
  ArrayQueueInvariantBefore2
  ArrayQueueInvariantBefore3
  ArrayQueueInvariant011
  ArrayQueueInvariant012
  ArrayQueueInvariant021
  ArrayQueueInvariant11
  ArrayQueueInvariant12
  ArrayQueueInvariant21
  ArrayToQueue.
Import ListNotations.

Section test.

Variable L : nat.
Hypothesis H : L > 0.

Arguments array_to_queue {L}.

Lemma all_none_const_none: forall n m,
  m < n ->
  all_none (array_to_queue H m n (Vector.const (None, 0) L)).
Proof.
  induction 1; intros.
  - rewrite array_to_queue_S_f; auto.
    rewrite array_queue_equal_nil; auto.
    simpl.
    rewrite Vector.const_nth; auto.
    simpl. reflexivity.
  - rewrite array_to_queue_S_r; auto; try lia.
    simpl.
    rewrite Vector.const_nth; auto.
Qed.

End test.

Section test.

Variable L : nat.
Hypothesis H : L > 0.

Lemma mod_L_eq_mod_lt_eq : forall n m,
  n mod L = m mod L ->
  Fin.of_nat_lt (mod_lt H n) = Fin.of_nat_lt (mod_lt H m).
Proof.
  intros.
  apply Fin.to_nat_inj.
  rewrite Fin.to_nat_of_nat.
  rewrite Fin.to_nat_of_nat.
  simpl.
  auto.
Qed.

End test.

Section t.

Context {liA liB liC : language_interface}.
Variable L : composed_lts.composed_lts liA liB liC.

Lemma invariant_land_l : forall P Q,
  composed_lts.invariant L (fun s => P s /\ Q s) ->
  composed_lts.invariant L P.
Proof.
  intros.
  unfold composed_lts.invariant.
  intros. apply H in H0. intuition.
Qed.

Lemma invariant_land_r : forall P Q,
  composed_lts.invariant L (fun s => P s /\ Q s) ->
  composed_lts.invariant L Q.
Proof.
  intros.
  unfold composed_lts.invariant.
  intros. apply H in H0. intuition.
Qed.
  
End t.

Section INV.

Variable L : nat.
Hypothesis H : L > 0.

Definition inv_ref' (s : composed_lts.state (composed_array_queue L)) :=
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
    binds pid ADeq28 pc ->
     snd (aqimpl.(ArrayQueueImpl.x) pid) <=
     snd (Vector.nth
      (ary.(Array.vec L))
      (Fin.of_nat_lt (mod_lt H
                      (aqimpl.(ArrayQueueImpl.front) pid))))
  ) /\
  composed_lts.reachable (composed_array_queue L) s.

Arguments get_ary {L}.
Arguments get_pc {L}.
Arguments R {L}.
Arguments F {L}.

Definition inv_d28 (s : composed_lts.state (composed_array_queue L)) :=
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
    binds pid ADeq28 pc ->
    (aqimpl.(ArrayQueueImpl.x) pid) = 
     (Vector.nth
      (ary.(Array.vec L))
      (Fin.of_nat_lt (mod_lt H
                      (aqimpl.(ArrayQueueImpl.front) pid)))) ->
    aqimpl.(ArrayQueueImpl.front) pid = F s /\ F s < R s
  ) /\
  composed_lts.reachable (composed_array_queue L) s.

Definition not_none_wrapper (t : option nat) := t <> None.

Definition inv_d27_x_none (s : composed_lts.state (composed_array_queue L)) :=
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
    binds pid ADeq27 pc ->
      not_none_wrapper (fst (aqimpl.(ArrayQueueImpl.x) pid))
  ) /\ composed_lts.reachable (composed_array_queue L) s.

Lemma inv_d27_x_none_inv:
  composed_lts.invariant_ind (composed_array_queue L)
  inv_d27_x_none.
Proof.
  unfold inv_d27_x_none.
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

Lemma inv_d27_x_none_invariant:
  composed_lts.invariant (composed_array_queue L)
  inv_d27_x_none.
Proof.
  apply invariant_ind_to_invariant'.
  apply inv_d27_x_none_inv.
Qed.

Definition inv_d28_x_none (s : composed_lts.state (composed_array_queue L)) :=
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
    binds pid ADeq28 pc ->
      not_none_wrapper (fst (aqimpl.(ArrayQueueImpl.x) pid))
  ) /\ composed_lts.reachable (composed_array_queue L) s.

Lemma inv_d28_x_none_inv:
  composed_lts.invariant_ind (composed_array_queue L)
  inv_d28_x_none.
Proof.
  unfold inv_d28_x_none.
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
    apply inv_d27_x_none_invariant in Hreach.
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

Lemma inv_d28_x_none_invariant:
  composed_lts.invariant (composed_array_queue L)
  inv_d28_x_none.
Proof.
  apply invariant_ind_to_invariant'.
  apply inv_d28_x_none_inv.
Qed.

Definition enq_not_inc pid pc ary rear :=
    (binds pid AEnq28 pc /\
      binds pid (AryCASOk true) ary.(Array.responses L)) \/
    (binds pid (AEnq29 true) pc) \/
    (binds pid AEnq30 pc) \/
    (binds pid AEnq31 pc /\
      pid # rear.(Counter.responses)).

Lemma enq_not_inc_push_neq: forall pid pc ary rear pid' p,
  enq_not_inc pid pc ary rear ->
  pid <> pid' ->
  enq_not_inc pid ((pid', p) :: pc) ary rear.
Proof.
  unfold enq_not_inc.
  intros. intuition.
  - left. intuition.
    apply binds_push_neq; auto.
  - right. left.
    apply binds_push_neq; auto.
  - right. right. left.
    apply binds_push_neq; auto.
  - right. right. right.
    intuition.
    apply binds_push_neq; auto.
Qed.

Lemma enq_not_inc_remove_neq: forall pid pc ary rear pid',
  enq_not_inc pid pc ary rear ->
  pid <> pid' ->
  enq_not_inc pid (remove pc pid') ary rear.
Proof.
  unfold enq_not_inc.
  intros. intuition.
  - left. intuition.
    apply remove_neq_preserves_binds; auto.
  - right. left.
    apply remove_neq_preserves_binds; auto.
  - right. right. left.
    apply remove_neq_preserves_binds; auto.
  - right. right. right.
    intuition.
    apply remove_neq_preserves_binds; auto.
Qed.

Lemma enq_not_inc_remove_neq_inv: forall pid pc ary rear pid',
  enq_not_inc pid (remove pc pid') ary rear ->
  pid <> pid' ->
  enq_not_inc pid pc ary rear.
Proof.
  unfold enq_not_inc.
  intros. intuition.
  - apply remove_preserves_binds_notin in H0; auto.
  - apply remove_preserves_binds_notin in H0; auto.
  - apply remove_preserves_binds_notin in H2; auto.
  - apply remove_preserves_binds_notin in H0; auto.
Qed.

Lemma enq_not_inc_remove_eq_false: forall pid pc ary rear,
  ok pc ->
  ~ enq_not_inc pid (remove pc pid) ary rear.
Proof.
  induction 1; unfold enq_not_inc; simpl; intros.
  - intro. intuition.
    inversion H0.
    inversion H0.
    inversion H1.
    inversion H0.
  - intro. apply IHok.
    destruct (pid =? x)eqn:Heq.
    -- apply Nat.eqb_eq in Heq; subst.
      unfold "#" in H1.
      intuition.
      apply binds_in in H2;
      intuition.
      apply binds_in in H2;
      intuition.
      apply binds_in in H3;
      intuition.
      apply binds_in in H2;
      intuition.
    -- apply Nat.eqb_neq in Heq.
      assert (Htmp : pid # (remove E pid)) by
      (apply ok_remove_notin; auto).
      unfold "#" in Htmp.
      intuition.
      apply binds_push_neq_inv in H2; auto;
      apply binds_in in H2; intuition.
      apply binds_push_neq_inv in H2; auto;
      apply binds_in in H2; intuition.
      apply binds_push_neq_inv in H3; auto;
      apply binds_in in H3; intuition.
      apply binds_push_neq_inv in H2; auto;
      apply binds_in in H2; intuition.
Qed.

Lemma enq_not_inc_remove_rear_neq: forall pid pc ary inv res v pid',
  enq_not_inc pid pc ary (mkCntState inv res v) ->
  pid <> pid' ->
  enq_not_inc pid pc ary (mkCntState inv (remove res pid') v).
Proof.
  unfold enq_not_inc.
  intros. intuition.
  simpl in *.
  right. right. right.
  intuition.
  eapply remove_preserves_notin; eauto.
Qed.

Lemma enq_not_inc_remove_rear_neq_inv: forall pid pc ary inv res v pid',
  enq_not_inc pid pc ary (mkCntState inv (remove res pid') v) ->
  pid <> pid' ->
  enq_not_inc pid pc ary (mkCntState inv res v).
Proof.
  unfold enq_not_inc.
  intros. intuition.
  simpl in *.
  right. right. right.
  intuition.
  eapply remove_neq_preserves_notin; eauto.
Qed.

Lemma enq_not_inc_remove_ary_neq: forall pid pc rear inv res v pid',
  enq_not_inc pid pc (mkAryState L inv res v) rear ->
  pid <> pid' ->
  enq_not_inc pid pc (mkAryState L inv (remove res pid') v) rear.
Proof.
  unfold enq_not_inc.
  intros. intuition.
  simpl in *.
  left. intuition.
  apply remove_neq_preserves_binds; auto.
Qed.

Lemma enq_not_inc_remove_ary_neq_inv: forall pid pc rear inv res v pid',
  enq_not_inc pid pc (mkAryState L inv (remove res pid') v) rear ->
  pid <> pid' ->
  enq_not_inc pid pc (mkAryState L inv res v) rear.
Proof.
  unfold enq_not_inc.
  intros. intuition.
  simpl in *.
  left. intuition.
  unfold binds in H3.
  rewrite remove_neq_preserves_get in H3; auto.
Qed.

Definition deq_not_inc pid pc ary front :=
    (binds pid ADeq28 pc /\
      binds pid (AryCASOk true) ary.(Array.responses L)) \/
    (binds pid (ADeq29 true) pc) \/
    (binds pid ADeq30 pc) \/
    (binds pid ADeq31 pc /\
      pid # front.(Counter.responses)).

Lemma deq_not_inc_remove_rear_neq: forall pid pc ary inv res v pid',
  deq_not_inc pid pc ary (mkCntState inv res v) ->
  pid <> pid' ->
  deq_not_inc pid pc ary (mkCntState inv (remove res pid') v).
Proof.
  unfold deq_not_inc.
  intros. intuition.
  simpl in *.
  right. right. right.
  intuition.
  eapply remove_preserves_notin; eauto.
Qed.

Lemma deq_not_inc_remove_rear_neq_inv: forall pid pc ary inv res v pid',
  deq_not_inc pid pc ary (mkCntState inv (remove res pid') v) ->
  pid <> pid' ->
  deq_not_inc pid pc ary (mkCntState inv res v).
Proof.
  unfold deq_not_inc.
  intros. intuition.
  simpl in *.
  right. right. right.
  intuition.
  eapply remove_neq_preserves_notin; eauto.
Qed.

Lemma deq_not_inc_remove_ary_neq: forall pid pc rear inv res v pid',
  deq_not_inc pid pc (mkAryState L inv res v) rear ->
  pid <> pid' ->
  deq_not_inc pid pc (mkAryState L inv (remove res pid') v) rear.
Proof.
  unfold deq_not_inc.
  intros. intuition.
  simpl in *.
  left. intuition.
  apply remove_neq_preserves_binds; auto.
Qed.

Lemma deq_not_inc_remove_ary_neq_inv: forall pid pc rear inv res v pid',
  deq_not_inc pid pc (mkAryState L inv (remove res pid') v) rear ->
  pid <> pid' ->
  deq_not_inc pid pc (mkAryState L inv res v) rear.
Proof.
  unfold deq_not_inc.
  intros. intuition.
  simpl in *.
  left. intuition.
  unfold binds in H3.
  rewrite remove_neq_preserves_get in H3; auto.
Qed.

Lemma enq_not_inc_push_neq_inv: forall pid pc ary rear pid' p,
  enq_not_inc pid ((pid', p) :: pc) ary rear ->
  pid <> pid' ->
  enq_not_inc pid pc ary rear.
Proof.
  unfold enq_not_inc. intros.
  intuition.
  - apply binds_push_neq_inv in H0; auto.
  - apply binds_push_neq_inv in H0; auto.
  - apply binds_push_neq_inv in H2; auto.
  - apply binds_push_neq_inv in H0; auto.
Qed.

Lemma deq_not_inc_push_neq: forall pid pc ary front pid' p,
  deq_not_inc pid pc ary front ->
  pid <> pid' ->
  deq_not_inc pid ((pid', p) :: pc) ary front.
Proof.
  unfold deq_not_inc.
  intros. intuition.
  - left. intuition.
    apply binds_push_neq; auto.
  - right. left.
    apply binds_push_neq; auto.
  - right. right. left.
    apply binds_push_neq; auto.
  - right. right. right.
    intuition.
    apply binds_push_neq; auto.
Qed.

Lemma deq_not_inc_remove_neq: forall pid pc ary front pid',
  deq_not_inc pid pc ary front ->
  pid <> pid' ->
  deq_not_inc pid (remove pc pid') ary front.
Proof.
  unfold deq_not_inc.
  intros. intuition.
  - left. intuition.
    apply remove_neq_preserves_binds; auto.
  - right. left.
    apply remove_neq_preserves_binds; auto.
  - right. right. left.
    apply remove_neq_preserves_binds; auto.
  - right. right. right.
    intuition.
    apply remove_neq_preserves_binds; auto.
Qed.

Lemma deq_not_inc_remove_neq_inv: forall pid pc ary front pid',
  deq_not_inc pid (remove pc pid') ary front ->
  pid <> pid' ->
  deq_not_inc pid pc ary front.
Proof.
  unfold deq_not_inc.
  intros. intuition.
  - apply remove_preserves_binds_notin in H0; auto.
  - apply remove_preserves_binds_notin in H0; auto.
  - apply remove_preserves_binds_notin in H2; auto.
  - apply remove_preserves_binds_notin in H0; auto.
Qed.

Lemma deq_not_inc_push_neq_inv: forall pid pc ary front pid' p,
  deq_not_inc pid ((pid', p) :: pc) ary front ->
  pid <> pid' ->
  deq_not_inc pid pc ary front.
Proof.
  unfold deq_not_inc. intros.
  intuition.
  - apply binds_push_neq_inv in H0; auto.
  - apply binds_push_neq_inv in H0; auto.
  - apply binds_push_neq_inv in H2; auto.
  - apply binds_push_neq_inv in H0; auto.
Qed.

Lemma deq_not_inc_remove_eq_false: forall pid pc ary front,
  ok pc ->
  ~ deq_not_inc pid (remove pc pid) ary front.
Proof.
  induction 1; unfold deq_not_inc; simpl; intros.
  - intro. intuition.
    inversion H0.
    inversion H0.
    inversion H1.
    inversion H0.
  - intro. apply IHok.
    destruct (pid =? x)eqn:Heq.
    -- apply Nat.eqb_eq in Heq; subst.
      unfold "#" in H1.
      intuition.
      apply binds_in in H2;
      intuition.
      apply binds_in in H2;
      intuition.
      apply binds_in in H3;
      intuition.
      apply binds_in in H2;
      intuition.
    -- apply Nat.eqb_neq in Heq.
      assert (Htmp : pid # (remove E pid)) by
      (apply ok_remove_notin; auto).
      unfold "#" in Htmp.
      intuition.
      apply binds_push_neq_inv in H2; auto;
      apply binds_in in H2; intuition.
      apply binds_push_neq_inv in H2; auto;
      apply binds_in in H2; intuition.
      apply binds_push_neq_inv in H3; auto;
      apply binds_in in H3; intuition.
      apply binds_push_neq_inv in H2; auto;
      apply binds_in in H2; intuition.
Qed.

Lemma enq_not_inc_subst_neq: forall pid pc ary rear pid' v,
  enq_not_inc pid pc ary rear ->
  pid <> pid' ->
  enq_not_inc pid (substitute pc pid' v) ary rear.
Proof.
  unfold enq_not_inc.
  intros. intuition.
  - left. intuition.
    apply substitute_neq_preserves_binds; auto.
  - right. left.
    apply substitute_neq_preserves_binds; auto.
  - right. right. left.
    apply substitute_neq_preserves_binds; auto.
  - right. right. right.
    intuition.
    apply substitute_neq_preserves_binds; auto.
Qed.

Lemma deq_not_inc_subst_neq: forall pid pc ary front pid' v,
  deq_not_inc pid pc ary front ->
  pid <> pid' ->
  deq_not_inc pid (substitute pc pid' v) ary front.
Proof.
  unfold deq_not_inc.
  intros. intuition.
  - left. intuition.
    apply substitute_neq_preserves_binds; auto.
  - right. left.
    apply substitute_neq_preserves_binds; auto.
  - right. right. left.
    apply substitute_neq_preserves_binds; auto.
  - right. right. right.
    intuition.
    apply substitute_neq_preserves_binds; auto.
Qed.

Definition normal_inst v :=
  v <> AEnq28 /\
  v <> AEnq29 true /\
  v <> AEnq30 /\
  v <> AEnq31.

Lemma enq_not_inc_normal_false: forall pid pc ary rear v,
  ok pc ->
  binds pid v pc ->
  normal_inst v ->
  ~ enq_not_inc pid pc ary rear.
Proof.
  unfold normal_inst.
  intros.
  intuition.
  unfold enq_not_inc in H3.
  unfold binds in H3.
  rewrite H1 in H3. intuition.
  inversion H3; subst; intuition.
  inversion H3; subst; intuition.
  inversion H6; subst; intuition.
  inversion H3; subst; intuition.
Qed.

Definition normal_inst' v :=
  v <> ADeq28 /\
  v <> ADeq29 true /\
  v <> ADeq30 /\
  v <> ADeq31.

Lemma deq_not_inc_normal_false: forall pid pc ary front v,
  ok pc ->
  binds pid v pc ->
  normal_inst' v ->
  ~ deq_not_inc pid pc ary front.
Proof.
  unfold normal_inst'.
  intros.
  intuition.
  unfold deq_not_inc in H3.
  unfold binds in H3.
  rewrite H1 in H3. intuition.
  inversion H3; subst; intuition.
  inversion H3; subst; intuition.
  inversion H6; subst; intuition.
  inversion H3; subst; intuition.
Qed.

Lemma enq_not_inc_subst_neq_inv: forall pid pc ary rear pid' v,
  enq_not_inc pid (substitute pc pid' v) ary rear ->
  pid <> pid' ->
  enq_not_inc pid pc ary rear.
Proof.
  unfold enq_not_inc.
  intros. intuition.
  - apply substitute_neq_preserves_binds' in H0; auto.
  - apply substitute_neq_preserves_binds' in H0; auto.
  - apply substitute_neq_preserves_binds' in H2; auto.
  - apply substitute_neq_preserves_binds' in H0; auto.
Qed.

Lemma deq_not_inc_subst_neq_inv: forall pid pc ary front pid' v,
  deq_not_inc pid (substitute pc pid' v) ary front ->
  pid <> pid' ->
  deq_not_inc pid pc ary front.
Proof.
  unfold deq_not_inc.
  intros. intuition.
  - apply substitute_neq_preserves_binds' in H0; auto.
  - apply substitute_neq_preserves_binds' in H0; auto.
  - apply substitute_neq_preserves_binds' in H2; auto.
  - apply substitute_neq_preserves_binds' in H0; auto.
Qed.

Lemma enq_not_inc_subst_normal_false: forall pid pc ary rear v v',
  ok pc ->
  binds pid v pc ->
  normal_inst v' ->
  ~ enq_not_inc pid (substitute pc pid v') ary rear.
Proof.
  unfold normal_inst.
  intros.
  intuition.
  unfold enq_not_inc in H3.
  unfold binds in H3.
  eapply substitute_eq_binds_v' in H1.
  rewrite H1 in H3.
  intuition.
  inversion H3; subst; intuition.
  inversion H3; subst; intuition.
  inversion H6; subst; intuition.
  inversion H3; subst; intuition.
Qed.

Lemma deq_not_inc_subst_normal_false: forall pid pc ary front v v',
  ok pc ->
  binds pid v pc ->
  normal_inst' v' ->
  ~ deq_not_inc pid (substitute pc pid v') ary front.
Proof.
  unfold normal_inst'.
  intros.
  intuition.
  unfold deq_not_inc in H3.
  unfold binds in H3.
  eapply substitute_eq_binds_v' in H1.
  rewrite H1 in H3.
  intuition.
  inversion H3; subst; intuition.
  inversion H3; subst; intuition.
  inversion H6; subst; intuition.
  inversion H3; subst; intuition.
Qed.

Lemma get_r'_normal_remove: forall pc res_ary res_rear pid v,
  ok pc ->
  binds pid v pc ->
  v <> AEnq28 ->
  (~ exists ret, v = AEnq29 ret) ->
  v <> AEnq30 ->
  v <> AEnq31 ->
  get_r' (remove pc pid) res_ary res_rear =
  get_r' pc res_ary res_rear.
Proof.
  intros.
  apply binds_reconstruct in H1; auto.
  destruct H1 as [l1 [l2 Hlist]].
  rewrite Hlist.
  rewrite Hlist in H0.
  apply ok_remove_middle_inv in H0.
  destruct H0 as [H01 H02].
  apply ok_concat_inv in H01.
  rewrite remove_notin_app; intuition.
  simpl.
  rewrite Nat.eqb_refl.
  repeat rewrite get_r'_dist.
  simpl.
  destruct v; intuition.
  exfalso. apply H3.
  exists ret. reflexivity.
Qed.

Lemma get_r'_normal_subst: forall pc res_ary res_rear pid v v',
  ok pc ->
  binds pid v pc ->
  normal_inst v ->
  normal_inst v' ->
  get_r' (substitute pc pid v') res_ary res_rear =
  get_r' pc res_ary res_rear.
Proof.
  intros.
  apply binds_reconstruct in H1; auto.
  destruct H1 as [l1 [l2 Hlist]].
  rewrite Hlist.
  rewrite Hlist in H0.
  apply ok_remove_middle_inv in H0.
  destruct H0 as [H01 H02].
  apply ok_concat_inv in H01.
  rewrite substitute_notin_app; intuition.
  simpl.
  rewrite Nat.eqb_refl.
  repeat rewrite get_r'_dist.
  f_equal.
  simpl.
  f_equal.
  unfold normal_inst in H2.
  unfold normal_inst in H3.
  destruct v'; intuition.
  all : destruct v; intuition.
  all : destruct ret; intuition.
  all : destruct ret0; intuition.
Qed.

Lemma get_f'_normal_remove: forall pc res_ary res_front pid v,
  ok pc ->
  binds pid v pc ->
  v <> ADeq28 ->
  (~ exists ret, v = ADeq29 ret) ->
  v <> ADeq30 ->
  v <> ADeq31 ->
  get_f' (remove pc pid) res_ary res_front =
  get_f' pc res_ary res_front.
Proof.
  intros.
  apply binds_reconstruct in H1; auto.
  destruct H1 as [l1 [l2 Hlist]].
  rewrite Hlist.
  rewrite Hlist in H0.
  apply ok_remove_middle_inv in H0.
  destruct H0 as [H01 H02].
  apply ok_concat_inv in H01.
  rewrite remove_notin_app; intuition.
  simpl.
  rewrite Nat.eqb_refl.
  repeat rewrite get_f'_dist.
  simpl.
  destruct v; intuition.
  exfalso. apply H3.
  exists ret. reflexivity.
Qed.

Lemma get_f'_normal_subst: forall pc res_ary res_front pid v v',
  ok pc ->
  binds pid v pc ->
  normal_inst' v ->
  normal_inst' v' ->
  get_f' (substitute pc pid v') res_ary res_front =
  get_f' pc res_ary res_front.
Proof.
  intros.
  apply binds_reconstruct in H1; auto.
  destruct H1 as [l1 [l2 Hlist]].
  rewrite Hlist.
  rewrite Hlist in H0.
  apply ok_remove_middle_inv in H0.
  destruct H0 as [H01 H02].
  apply ok_concat_inv in H01.
  rewrite substitute_notin_app; intuition.
  simpl.
  rewrite Nat.eqb_refl.
  repeat rewrite get_f'_dist.
  f_equal.
  simpl.
  f_equal.
  unfold normal_inst' in H2.
  unfold normal_inst' in H3.
  destruct v'; intuition.
  all : destruct v; intuition.
  all : destruct ret; intuition.
  all : destruct ret0; intuition.
Qed.

Lemma normal_inst_AEnq1 :
  normal_inst AEnq1.
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq1' :
  normal_inst' AEnq1.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq2 :
  normal_inst AEnq2.
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq2' :
  normal_inst' AEnq2.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq3 : forall ret,
  normal_inst (AEnq3 ret).
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq3' : forall ret,
  normal_inst' (AEnq3 ret).
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq4 :
  normal_inst AEnq4.
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq4' :
  normal_inst' AEnq4.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq5 :
  normal_inst AEnq5.
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq5' :
  normal_inst' AEnq5.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq6 : forall ret,
  normal_inst (AEnq6 ret).
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq6' : forall ret,
  normal_inst' (AEnq6 ret).
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq10 :
  normal_inst AEnq10.
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq10' :
  normal_inst' AEnq10.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq11 :
  normal_inst AEnq11.
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq11' :
  normal_inst' AEnq11.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq12 : forall ret,
  normal_inst (AEnq12 ret).
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq12' : forall ret,
  normal_inst' (AEnq12 ret).
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq13 :
  normal_inst AEnq13.
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq13' :
  normal_inst' AEnq13.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq14 :
  normal_inst AEnq14.
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq14' :
  normal_inst' AEnq14.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq15 : forall ret,
  normal_inst (AEnq15 ret).
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq15' : forall ret,
  normal_inst' (AEnq15 ret).
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq1 :
  normal_inst ADeq1.
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq1' :
  normal_inst' ADeq1.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq2 :
  normal_inst ADeq2.
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq2' :
  normal_inst' ADeq2.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq3 : forall ret,
  normal_inst (ADeq3 ret).
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq3' : forall ret,
  normal_inst' (ADeq3 ret).
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq4 :
  normal_inst ADeq4.
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq4' :
  normal_inst' ADeq4.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq5 :
  normal_inst ADeq5.
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq5' :
  normal_inst' ADeq5.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq6 : forall ret,
  normal_inst (ADeq6 ret).
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq6' : forall ret,
  normal_inst' (ADeq6 ret).
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq10 :
  normal_inst ADeq10.
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq10' :
  normal_inst' ADeq10.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq11 :
  normal_inst ADeq11.
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq11' :
  normal_inst' ADeq11.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq12 : forall ret,
  normal_inst (ADeq12 ret).
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq12' : forall ret,
  normal_inst' (ADeq12 ret).
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq13 :
  normal_inst ADeq13.
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq13' :
  normal_inst' ADeq13.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq14 :
  normal_inst ADeq14.
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq14' :
  normal_inst' ADeq14.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq15 : forall ret,
  normal_inst (ADeq15 ret).
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq15' : forall ret,
  normal_inst' (ADeq15 ret).
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq27 :
  normal_inst ADeq27.
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq27' :
  normal_inst' ADeq27.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq26 :
  normal_inst AEnq26.
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq26' :
  normal_inst' AEnq26.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq26 :
  normal_inst ADeq26.
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq26' :
  normal_inst' ADeq26.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq27 :
  normal_inst AEnq27.
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq27' :
  normal_inst' AEnq27.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq28' :
  normal_inst' AEnq28.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq28 :
  normal_inst ADeq28.
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq29 :
  normal_inst (AEnq29 false).
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq29' : forall ret,
  normal_inst' (AEnq29 ret).
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq29 : forall ret,
  normal_inst (ADeq29 ret).
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq29' :
  normal_inst' (ADeq29 false).
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq30 :
  normal_inst (ADeq30).
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq31 :
  normal_inst (ADeq31).
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_ADeq32 :
  normal_inst (ADeq32).
Proof.
  unfold normal_inst.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq30' :
  normal_inst' AEnq30.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq31' :
  normal_inst' AEnq31.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Lemma normal_inst_AEnq32' :
  normal_inst' AEnq32.
Proof.
  unfold normal_inst'.
  intuition; try discriminate.
Qed.

Ltac solve_normal :=
  try apply normal_inst_AEnq1;
  try apply normal_inst_AEnq1';
  try apply normal_inst_AEnq2;
  try apply normal_inst_AEnq2';
  try apply normal_inst_AEnq3;
  try apply normal_inst_AEnq3';
  try apply normal_inst_AEnq4;
  try apply normal_inst_AEnq4';
  try apply normal_inst_AEnq5;
  try apply normal_inst_AEnq5';
  try apply normal_inst_AEnq6;
  try apply normal_inst_AEnq6';
  try apply normal_inst_AEnq10;
  try apply normal_inst_AEnq10';
  try apply normal_inst_AEnq11;
  try apply normal_inst_AEnq11';
  try apply normal_inst_AEnq12;
  try apply normal_inst_AEnq12';
  try apply normal_inst_AEnq13;
  try apply normal_inst_AEnq13';
  try apply normal_inst_AEnq14;
  try apply normal_inst_AEnq14';
  try apply normal_inst_AEnq15;
  try apply normal_inst_AEnq15';
  try apply normal_inst_AEnq26;
  try apply normal_inst_AEnq26';
  try apply normal_inst_AEnq27;
  try apply normal_inst_AEnq27';
  try apply normal_inst_AEnq28';
  try apply normal_inst_AEnq29;
  try apply normal_inst_AEnq29';
  try apply normal_inst_AEnq30';
  try apply normal_inst_AEnq31';
  try apply normal_inst_AEnq32';
  try apply normal_inst_ADeq1;
  try apply normal_inst_ADeq1';
  try apply normal_inst_ADeq2;
  try apply normal_inst_ADeq2';
  try apply normal_inst_ADeq3;
  try apply normal_inst_ADeq3';
  try apply normal_inst_ADeq4;
  try apply normal_inst_ADeq4';
  try apply normal_inst_ADeq5;
  try apply normal_inst_ADeq5';
  try apply normal_inst_ADeq6;
  try apply normal_inst_ADeq6';
  try apply normal_inst_ADeq10;
  try apply normal_inst_ADeq10';
  try apply normal_inst_ADeq11;
  try apply normal_inst_ADeq11';
  try apply normal_inst_ADeq12;
  try apply normal_inst_ADeq12';
  try apply normal_inst_ADeq13;
  try apply normal_inst_ADeq13';
  try apply normal_inst_ADeq14;
  try apply normal_inst_ADeq14';
  try apply normal_inst_ADeq15;
  try apply normal_inst_ADeq15';
  try apply normal_inst_ADeq26;
  try apply normal_inst_ADeq26';
  try apply normal_inst_ADeq27;
  try apply normal_inst_ADeq27';
  try apply normal_inst_ADeq28;
  try apply normal_inst_ADeq29;
  try apply normal_inst_ADeq29';
  try apply normal_inst_ADeq30;
  try apply normal_inst_ADeq31;
  try apply normal_inst_ADeq32
  .



(* Definition enq_not_inc pid pc ary rear :=
    (binds pid AEnq28 pc /\
      binds pid (AryCASOk true) ary.(Array.responses L)) \/
    (binds pid (AEnq29 true) pc) \/
    (binds pid AEnq30 pc) \/
    (binds pid AEnq31 pc /\
      pid # rear.(Counter.responses)).

Definition deq_not_inc pid pc ary front :=
    (binds pid ADeq28 pc /\
      binds pid (AryCASOk true) ary.(Array.responses L)) \/
    (binds pid (ADeq29 true) pc) \/
    (binds pid ADeq30 pc) \/
    (binds pid ADeq31 pc /\
      pid # front.(Counter.responses)). *)

Arguments get_ary {L}.
Arguments get_pc {L}.
Arguments R {L}.
Arguments F {L}.

Definition inv_1 (s : composed_lts.state (composed_array_queue L)) :=
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
  R s > 0 ->
  rear.(Counter.value) = R s - 1 ->
  exists pid,
    enq_not_inc pid pc ary rear /\
    (forall pid', pid' <> pid -> ~ enq_not_inc pid' pc ary rear).

Definition inv_1' (s : composed_lts.state (composed_array_queue L)) :=
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
  F s > 0 ->
  front.(Counter.value) = F s - 1 ->
  exists pid,
    deq_not_inc pid pc ary front /\
    (forall pid', pid' <> pid -> ~ deq_not_inc pid' pc ary front).

Definition inv_2 (s : composed_lts.state (composed_array_queue L)) :=
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
  rear.(Counter.value) = R s \/
  rear.(Counter.value) = R s - 1.

Definition inv_2' (s : composed_lts.state (composed_array_queue L)) :=
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
  front.(Counter.value) = F s \/
  front.(Counter.value) = F s - 1.

Definition inv_3 (s : composed_lts.state (composed_array_queue L)) :=
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
    enq_not_inc pid pc ary rear ->
    rear.(Counter.value) = R s - 1).

Definition inv_3' (s : composed_lts.state (composed_array_queue L)) :=
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
    deq_not_inc pid pc ary front ->
    front.(Counter.value) = F s - 1).

Definition inv_4 (s : composed_lts.state (composed_array_queue L)) :=
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
  rear.(Counter.value) = R s ->
  (forall pid,
    ~ (enq_not_inc pid pc ary rear)).

Definition inv_4' (s : composed_lts.state (composed_array_queue L)) :=
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
  front.(Counter.value) = F s ->
  (forall pid,
    ~ (deq_not_inc pid pc ary front)).

Definition inv_5 (s : composed_lts.state (composed_array_queue L)) :=
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
    enq_not_inc pid pc ary rear ->
    F s < R s).

Definition inv_5' (s : composed_lts.state (composed_array_queue L)) :=
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
    deq_not_inc pid pc ary front ->
    R s < F s + L).

Definition inv_6 (s : composed_lts.state (composed_array_queue L)) :=
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
  0 <= F s /\ 
  F s <= R s /\
  R s <= F s + L.

(* Theorem array_to_queue_obligation : forall (f r : nat), f < r -> r - S f < r - f.
Proof.
  intros * ha.
  abstract nia.
Qed.

Fixpoint array_to_queue_rec (f r : nat) (vec : Vector.t entry L)
  (acc : Acc lt (r - f)) : list (option nat) := 
  match lt_dec f r with 
    | left pf => (array_to_queue_rec (S f) r vec (Acc_inv acc (array_to_queue_obligation _ _ pf))) ++ 
          [fst (Vector.nth vec (Fin.of_nat_lt (@mod_lt L H f)))]
    | right _ => nil 
  end.

Definition array_to_queue (f r : nat) (vec : Vector.t entry L) := 
  match lt_dec f r with 
    | left pf => (array_to_queue_rec f r vec (lt_wf (r - f))) 
    | right _ => nil 
  end.

Fixpoint all_some (l : list (option nat)) :=
  match l with
  | nil => True
  | h :: l' =>
    match h with
    | None => False
    | Some _ => all_some l'
    end
  end.

Fixpoint all_none (l : list (option nat)) :=
  match l with
  | nil => True
  | h :: l' =>
    match h with
    | None => all_none l'
    | Some _ => False
    end
  end. *)

Arguments array_to_queue {L}.

Definition inv_range (s : composed_lts.state (composed_array_queue L)) :=
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
  all_some (array_to_queue H (F s) (R s) ary.(Array.vec L)) /\
  all_none (array_to_queue H (R s) (F s + L) ary.(Array.vec L)).

Definition inv_d28_clean (s : composed_lts.state (composed_array_queue L)) :=
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
    binds pid ADeq28 pc ->
    (aqimpl.(ArrayQueueImpl.x) pid) = 
     (Vector.nth
      (ary.(Array.vec L))
      (Fin.of_nat_lt (mod_lt H
                      (aqimpl.(ArrayQueueImpl.front) pid)))) ->
    aqimpl.(ArrayQueueImpl.front) pid = F s /\ F s < R s
  ).

Definition inv_e28_clean (s : composed_lts.state (composed_array_queue L)) :=
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
  ).

Definition inv_total (s : composed_lts.state (composed_array_queue L)) :=
  (* composed_lts.reachable (composed_array_queue L) s /\ *)
  inv_e28_clean s /\
  inv_d28_clean s /\
  inv_1  s  /\
  inv_1' s /\
  inv_2  s /\
  inv_2' s /\
  inv_3  s /\
  inv_3' s /\
  inv_4  s /\
  inv_4' s /\
  inv_5  s /\
  inv_5' s /\
  inv_6  s /\
  inv_range s
  .

Ltac unfold_FR_simpl :=
  unfold F, R;
  unfold get_front, get_rear, get_ary, get_pc;
  simpl.

Ltac unfold_FR_simpl' :=
  unfold F, R in *;
  unfold get_front, get_rear, get_ary, get_pc in *;
  simpl in *.

Lemma get_r'_subst_Enq28_notin_ary: forall pc res_ary res_rear pid v,
  ok pc ->
  binds pid v pc ->
  normal_inst v ->
  pid # res_ary ->
  get_r' (substitute pc pid AEnq28) res_ary res_rear =
  get_r' pc res_ary res_rear.
Proof.
  intros.
  apply binds_reconstruct in H1; auto.
  destruct H1 as [l1 [l2 Hlist]].
  rewrite Hlist.
  rewrite Hlist in H0.
  apply ok_remove_middle_inv in H0.
  destruct H0 as [H01 H02].
  apply ok_concat_inv in H01.
  rewrite substitute_notin_app; intuition.
  simpl.
  rewrite Nat.eqb_refl.
  repeat rewrite get_r'_dist.
  f_equal.
  simpl.
  f_equal.
  unfold normal_inst in H2.
  unfold normal_inst in H3.
  apply notin_get_none in H3.
  rewrite H3.
  destruct v; intuition.
  destruct ret; intuition.
Qed.

Lemma get_r'_subst_Enq30_notin_ary: forall pc res_ary res_rear pid,
  ok pc ->
  binds pid AEnq30 pc ->
  pid # res_rear ->
  get_r' (substitute pc pid AEnq31) res_ary res_rear =
  get_r' pc res_ary res_rear.
Proof.
  intros.
  apply binds_reconstruct in H1; auto.
  destruct H1 as [l1 [l2 Hlist]].
  rewrite Hlist.
  rewrite Hlist in H0.
  apply ok_remove_middle_inv in H0.
  destruct H0 as [H01 H02].
  apply ok_concat_inv in H01.
  rewrite substitute_notin_app; intuition.
  simpl.
  rewrite Nat.eqb_refl.
  repeat rewrite get_r'_dist.
  simpl.
  apply notin_get_none in H2.
  rewrite H2.
  reflexivity.
Qed.

Lemma enq_not_inc_subst_Enq28_notin_res_false : forall pid pc ary rear,
  binds pid AEnq27 pc ->
  pid # ary.(Array.responses L) ->
  ~ enq_not_inc pid (substitute pc pid AEnq28) ary rear.
Proof.
  intros. intro.
  unfold enq_not_inc in H2.
  intuition.
  apply binds_in in H4; auto.
  eapply substitute_eq_binds_v' in H0; eauto;
  unfold binds in H0;
  rewrite H2 in H0; discriminate.
  eapply substitute_eq_binds_v' in H0; eauto;
  unfold binds in H0;
  rewrite H3 in H0; discriminate.
  eapply substitute_eq_binds_v' in H0; eauto;
  unfold binds in H0;
  rewrite H2 in H0; discriminate.
Qed.

Ltac unfold_total :=
  unfold inv_total;
  unfold 
  inv_e28_clean, 
  inv_d28_clean, 
  inv_1,
  inv_1',
  inv_2,
  inv_2', 
  inv_3,
  inv_3',
  inv_4, inv_4', inv_5, inv_5', inv_6, inv_range.

Lemma inv_total_inv': 
  invariant_len' (composed_array_queue L) inv_total.
Proof.
  apply k_induction_to_invariant_len'.
  unfold k_induction'. split; intros.
  -
    unfold reachable_len' in H0.
    rename H0 into Hnew.
    (* destruct H0 as [init [acts [Hnew Hvalid]]]. *)
    (* inversion Hvalid; subst. *)
    inversion Hnew; subst.
    inversion H1; subst.
    inversion H2; subst.
    inversion H0; subst.
    inversion H4; subst.
    inversion H7; subst.
    inversion H8; subst.
    inversion H9; subst.
    inversion H11; subst.
    inversion H13; subst.
    inversion H15; subst.
    inversion H16; subst.
    inversion H18; subst.
    unfold inv_total.
    intuition.
    -- unfold inv_e28_clean.
      try (rewrite H5);
      try (rewrite H21);
      try (rewrite H22).
      unfold new_array_queue.
      unfold new_counter.
      unfold new_array.
      simpl. intros.
      inversion H20.
    -- unfold inv_d28_clean.
      try (rewrite H5);
      try (rewrite H21);
      try (rewrite H22).
      unfold new_array_queue.
      unfold new_counter.
      unfold new_array.
      simpl. intros.
      inversion H20.
    -- unfold inv_1.
      unfold R.
      unfold get_pc, get_ary, get_rear.
      try (rewrite H5);
      try (rewrite H21);
      try (rewrite H22).
      unfold new_array_queue.
      unfold new_counter.
      unfold new_array.
      simpl.
       intros. inversion H20.
    -- unfold inv_1'.
      unfold R.
      unfold F.
      unfold get_pc, get_ary, get_rear, get_front.
      try (rewrite H5);
      try (rewrite H21);
      try (rewrite H22).
      unfold new_array_queue.
      unfold new_counter.
      unfold new_array.
      simpl.
       intros. inversion H20.
    -- unfold inv_2.
      unfold R.
      unfold F.
      unfold get_pc, get_ary, get_rear, get_front.
      try (rewrite H5);
      try (rewrite H21);
      try (rewrite H22).
      unfold new_array_queue.
      unfold new_counter.
      unfold new_array.
      simpl. intuition.
    -- unfold inv_2'.
      unfold R.
      unfold F.
      unfold get_pc, get_ary, get_rear, get_front.
      try (rewrite H5);
      try (rewrite H21);
      try (rewrite H22).
      unfold new_array_queue.
      unfold new_counter.
      unfold new_array.
      simpl. intuition.
    -- unfold inv_3.
      unfold R.
      unfold F.
      unfold get_pc, get_ary, get_rear, get_front.
      try (rewrite H5);
      try (rewrite H21);
      try (rewrite H22).
      unfold new_array_queue.
      unfold new_counter.
      unfold new_array.
      simpl. intros. intuition.
    -- unfold inv_3'.
      unfold R.
      unfold F.
      unfold get_pc, get_ary, get_rear, get_front.
      try (rewrite H5);
      try (rewrite H21);
      try (rewrite H22).
      unfold new_array_queue.
      unfold new_counter.
      unfold new_array.
      simpl. intros. intuition.
    -- unfold inv_4.
      unfold R.
      unfold F.
      unfold get_pc, get_ary, get_rear, get_front.
      unfold enq_not_inc.
      try (rewrite H5);
      try (rewrite H21);
      try (rewrite H22).
      unfold new_array_queue.
      unfold new_counter.
      unfold new_array.
      simpl. intros. intro. intuition;
      try inversion H23.
      inversion H24.
    -- unfold inv_4'.
      unfold R.
      unfold F.
      unfold get_pc, get_ary, get_rear, get_front.
      unfold enq_not_inc, deq_not_inc.
      try (rewrite H5);
      try (rewrite H21);
      try (rewrite H22).
      unfold new_array_queue.
      unfold new_counter.
      unfold new_array.
      simpl. intros. intro. intuition;
      try inversion H23.
      inversion H24.
    -- unfold inv_5.
      unfold R.
      unfold F.
      unfold get_pc, get_ary, get_rear, get_front.
      unfold enq_not_inc, deq_not_inc.
      try (rewrite H5);
      try (rewrite H21);
      try (rewrite H22).
      unfold new_array_queue.
      unfold new_counter.
      unfold new_array.
      simpl. intros.
      intuition;
      try inversion H20.
      inversion H23.
    -- unfold inv_5'.
      unfold R.
      unfold F.
      unfold get_pc, get_ary, get_rear, get_front.
      unfold enq_not_inc, deq_not_inc.
      try (rewrite H5);
      try (rewrite H21);
      try (rewrite H22).
      unfold new_array_queue.
      unfold new_counter.
      unfold new_array.
      simpl. intros.
      auto.
    -- unfold inv_6.
      unfold R.
      unfold F.
      unfold get_pc, get_ary, get_rear, get_front.
      unfold enq_not_inc, deq_not_inc.
      try (rewrite H5);
      try (rewrite H21);
      try (rewrite H22).
      unfold new_array_queue.
      unfold new_counter.
      unfold new_array.
      simpl. intuition.
    -- unfold inv_range.
      unfold R.
      unfold F.
      unfold get_pc, get_ary, get_rear, get_front.
      unfold enq_not_inc, deq_not_inc.
      try (rewrite H5);
      try (rewrite H21);
      try (rewrite H22);
      try (rewrite H14).
      unfold new_array_queue.
      unfold new_counter.
      unfold new_array.
      simpl. intuition.
      apply all_none_const_none; auto.
  - rename H0 into IHk.
    rename H1 into H0.
    apply reachable_len_reconstruct in H0.
    destruct H0 as [st [acts [Hreach Hstep]]].
    inversion Hstep; subst; clear Hstep.
    (* internal_step_L1 *)
    -- inversion H3; subst; clear H3.
      unfold inv_total.
      intuition.
      (* inv_e28 *)
      --- unfold inv_e28_clean.
        intros.
        destruct (eq_nat_dec pid pid0).
        + subst.
          pose proof Hreach as HreachTmp.
          apply IHk in Hreach; try lia.
          unfold inv_total in Hreach.
          destruct Hreach as [Hinv _].
          unfold inv_e28_clean in Hinv.
          inversion H1; subst; simpl in *.
          inversion H3; subst; simpl in *.
          unfold R, F; simpl.
          unfold get_pc, get_rear, get_front, get_ary; simpl.
          inversion H4; subst; simpl in *.
          (* front_rear *)
          ++ inversion H5; subst; simpl in *.
            inversion H6; subst; simpl in *.
            (* rear *)
            +++ inversion H7; subst; simpl in *.
              inversion H8; subst; simpl in *.
              (* INC *)
              * apply reachable_len_to_reachable in HreachTmp.
                apply inv_rear_inc_at_e31_invariant in HreachTmp.
                unfold inv_rear_inc_at_e31 in HreachTmp.
                apply HreachTmp in Hbinds5; auto.
                simpl in Hbinds5.
                unfold binds in H0.
                rewrite Hbinds5 in H0; discriminate.
              * rewrite get_r'_any_rear_read; auto.
            (* front *)
            +++ inversion H7; subst; simpl in *.
              inversion H8; subst; simpl in *.
              (* INC *)
              * apply reachable_len_to_reachable in HreachTmp.
                apply inv_front_inc_at_d31_invariant in HreachTmp.
                unfold inv_front_inc_at_d31 in HreachTmp.
                apply HreachTmp in Hbinds5; auto.
                simpl in Hbinds5.
                unfold binds in H0.
                rewrite Hbinds5 in H0; discriminate.
              * rewrite get_f'_any_rear_read; auto.
          (* array *)
          ++ inversion H5; subst; simpl in *.
            inversion H6; subst; simpl in *.
            (* CAS *)
            +++ destruct ((entry_eqb
              (Vector.nth vec (Fin.of_nat_lt Hlt))
              (old)))eqn:Heq.
              (* success *)
              * apply entry_eqb_eq in Heq.
                subst.
                apply reachable_len_to_reachable in HreachTmp.
                apply step_invariant in HreachTmp.
                unfold ComposedLTS.inv in HreachTmp.
                simpl in HreachTmp.
                apply HreachTmp in Hbinds0; auto.
                destruct Hbinds0 as [s1 [s2 [q [acts [Hint_query [Hvalid Hgather]]]]]].
                inversion Hint_query; subst; simpl in *.
                inversion H7; subst; simpl in *.
                unfold binds in H0.
                inversion H9; subst; simpl in *.
                Ltac tmp H Hvalid st2 pid0 acts Hgather H0 :=
                (
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
      (rewrite Hvalid in H0; discriminate)).
  tmp noB_preserves_AEnq2 Hvalid st2 pid0 acts Hgather H0.
  tmp noB_preserves_AEnq5 Hvalid st2 pid0 acts Hgather H0.
  tmp noB_preserves_AEnq11 Hvalid st2 pid0 acts Hgather H0.
  tmp noB_preserves_AEnq14 Hvalid st2 pid0 acts Hgather H0.
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
  inversion H8; subst; simpl in *.
  inversion H10; subst; simpl in *.
  inversion H12; subst; simpl in *.
  inversion H11; subst; simpl in *.
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
  rewrite Htmp in H2.
  rewrite Hrear in H2.
  rewrite Vector.nth_replace_eq in H2.
  rewrite Hx in H2.
  destruct (ArrayQueueImpl.x LState pid0).
  simpl in H2.
  inversion H2; subst.
  lia.

  tmp noB_preserves_AEnq31 Hvalid st2 pid0 acts Hgather H0.
  tmp noB_preserves_ADeq2 Hvalid st2 pid0 acts Hgather H0.
  tmp noB_preserves_ADeq5 Hvalid st2 pid0 acts Hgather H0.
  tmp noB_preserves_ADeq11 Hvalid st2 pid0 acts Hgather H0.
  tmp noB_preserves_ADeq14 Hvalid st2 pid0 acts Hgather H0.
  tmp noB_preserves_ADeq28 Hvalid st2 pid0 acts Hgather H0.
  tmp noB_preserves_ADeq31 Hvalid st2 pid0 acts Hgather H0.
        (* false *)
        * rewrite get_r'_any_ary_cas_false; auto.
          rewrite get_f'_any_ary_cas_false; auto.
      (* READ *)
      +++ rewrite get_r'_any_ary_read; auto.
        rewrite get_f'_any_ary_read; auto.
    + pose proof Hreach as HreachTmp;
      apply IHk in Hreach; try lia.
      unfold inv_total in Hreach.
      destruct Hreach as [Hinve28 [_ [_ [_ [_ [_ [Hinv3 _]]]]]]].
      inversion H1; subst; simpl in *.
      inversion H3; subst; simpl in *.
      unfold R, F in *; simpl in *.
      unfold get_rear, get_pc, get_front, get_ary in *; simpl in *.
      inversion H4; subst; simpl in *.
      (* front_rear *)
      ++ inversion H5; subst; simpl in *.
        inversion H6; subst; simpl in *.
        (* rear *)
        +++ inversion H7; subst; simpl in *.
          inversion H8; subst; simpl in *.
          (* inc *)
          * unfold inv_e28_clean in Hinve28.
            apply Hinve28 in H0; auto.
            apply reachable_len_to_reachable in HreachTmp.
            pose proof HreachTmp as HreachTmp2.
            apply inv_rear_inc_at_e31_invariant in HreachTmp.
            unfold inv_rear_inc_at_e31 in HreachTmp.
            simpl in HreachTmp.
            apply HreachTmp in Hbinds5; auto.
            exfalso.
            destruct H0 as [HrearR _].
            unfold R in HrearR.
            unfold get_rear, get_ary, get_pc in HrearR; simpl in HrearR.
            assert (Hgt : 0 < v + get_r' (pc (LState st2)) (Array.responses L (LState st1)) res).
            pose proof Hbinds5 as HbindsTmp.
            apply binds_reconstruct in Hbinds5.
            destruct Hbinds5 as [l1 [l2 Hlist]].
            rewrite Hlist.
            rewrite get_r'_dist.
            rewrite get_r'_dist.
            simpl.
            apply notin_get_none in Hnotin_res.
            rewrite Hnotin_res. lia.
            rewrite <-HrearR in Hgt.
            assert (Hsub1 : forall x y, x = y -> x - 1 = y - 1).
            intros; lia.
            apply Hsub1 in HrearR.
            unfold inv_3 in Hinv3.
            simpl in Hinv3.
            unfold R in Hinv3.
            unfold get_rear, get_ary, get_pc in Hinv3; simpl in Hinv3.
            erewrite <-Hinv3 with (pid:=pid) in HrearR; eauto.
            apply inv_rear_invariant in HreachTmp2; auto.
            unfold inv_rear in HreachTmp2.
            simpl in HreachTmp2.
            intuition.
            specialize (H10 pid0). lia.
            unfold enq_not_inc.
            right. right. right.
            intuition.
          (* read *)
          * rewrite get_r'_any_rear_read; auto.
        (* front *)
        +++ unfold inv_e28_clean in Hinve28.
          simpl in Hinve28.
          apply Hinve28 in H0; auto.
            unfold R, F in H0.
            unfold get_front, get_rear, get_ary, get_pc in H0; simpl in H0.
            intuition.
          inversion H7; subst; simpl in *.
          inversion H0; subst; simpl in *.
          (* inc *)
          * apply reachable_len_to_reachable in HreachTmp.
            pose proof HreachTmp as HreachTmp2.
            apply inv_front_inc_at_d31_invariant in HreachTmp.
            unfold inv_front_inc_at_d31 in HreachTmp.
            simpl in HreachTmp.
            apply HreachTmp in Hbinds5; auto.
            apply array_queue_wf_invarint in HreachTmp2.
            unfold array_queue_wf in HreachTmp2.
            simpl in HreachTmp2.
            apply binds_reconstruct in Hbinds5.
            destruct Hbinds5 as [l1 [l2 Hlist]].
            rewrite Hlist in HreachTmp2.
            apply ok_remove_middle_inv in HreachTmp2.
            destruct HreachTmp2 as [Hokapp [Hnti1 Hnti2]].
            rewrite Hlist.
            rewrite get_f'_dist.
            rewrite <-Hlist.
            rewrite get_f'_dist.
            simpl.
            rewrite Nat.eqb_refl. simpl.
            rewrite get_f'_any_front_push; auto.
            rewrite get_f'_any_front_push; auto.
            rewrite Hlist in H9.
            rewrite get_f'_dist in H9.
            rewrite <-Hlist in H9.
            rewrite get_f'_dist in H9.
            simpl in H9.
            apply notin_get_none in Hnotin_res.
            rewrite Hnotin_res in H9. lia.
          * rewrite get_f'_any_rear_read; auto.
      (* array *)
      ++ inversion H5; subst; simpl in *.
        inversion H6; subst; simpl in *.
        (* CAS *)
            +++ destruct ((entry_eqb
              (Vector.nth vec (Fin.of_nat_lt Hlt))
              (old)))eqn:Heq.
              (* success *)
              * apply entry_eqb_eq in Heq.
                subst.
                apply reachable_len_to_reachable in HreachTmp.
                pose proof HreachTmp as HreachTmp2.
                apply step_invariant in HreachTmp.
                unfold ComposedLTS.inv in HreachTmp.
                simpl in HreachTmp.
                apply HreachTmp in Hbinds0; auto.
                destruct Hbinds0 as [s1 [s2 [q [acts [Hint_query [Hvalid Hgather]]]]]].
                inversion Hint_query; subst; simpl in *.
                inversion H7; subst; simpl in *.
                unfold binds in H0.
                pose proof HreachTmp2 as HreachTmp3.
                apply inv_ary_cas_at_e28_d28_invariant in HreachTmp2.
                unfold inv_ary_cas_at_e28_d28 in HreachTmp2.
                simpl in HreachTmp2.
                pose proof Hbinds3 as Hbind3Tmp.
                apply HreachTmp2 in Hbinds3.
                destruct Hbinds3 as [Hb3|Hb3].
                (* Enq28 *)
                ** unfold binds in Hb3.
                  inversion H9; subst; simpl in *.
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
  inversion H8; subst; simpl in *.
  inversion H10; subst; simpl in *.
  inversion H12; subst; simpl in *.
  inversion H11; subst; simpl in *.
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
  rewrite Htmp in H2.
  rewrite Hrear in H2.

  rewrite Hx in H15.
  rewrite Htmp in H15.
  rewrite Hrear in H15.
  unfold inv_e28_clean in Hinve28.
  simpl in Hinve28.
  apply Hinve28 in H15; auto.

  destruct (Fin.eq_dec (Fin.of_nat_lt (mod_lt H (ArrayQueueImpl.rear LState pid)))
    (Fin.of_nat_lt (mod_lt H (ArrayQueueImpl.rear LState pid0)))).
    rewrite e in H2.
    rewrite Vector.nth_replace_eq in H2.

    rewrite Hx in H2.
    apply inv_e28_x_none_invariant in HreachTmp3.
    unfold inv_e28_x_none in HreachTmp3.
    simpl in HreachTmp3.
    apply HreachTmp3 in H0; auto.
    destruct (ArrayQueueImpl.x LState pid0).
    simpl in H2.
    rewrite H2 in H0.
    simpl in H0. discriminate.
  rewrite Vector.nth_replace_neq in H2; auto.
    apply Hinve28 in H2; auto.
    destruct H15 as [H151 H152].
    destruct H2 as [H21 H22].
    rewrite <-H21 in H151.
    rewrite H151 in n1. intuition.

  tmp' noB_preserves_AEnq31 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_ADeq2 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_ADeq5 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_ADeq11 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_ADeq14 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_ADeq28 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_ADeq31 Hvalid st2 pid acts Hgather Hb3.
          (* Deq28 *)
          ** unfold binds in Hb3.
            inversion H9; subst; simpl in *.
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
  inversion H8; subst; simpl in *.
  inversion H10; subst; simpl in *.
  inversion H12; subst; simpl in *.
  inversion H11; subst; simpl in *.
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
  rewrite Htmp in H2.
  rewrite Hrear in H2.

  rewrite Hx in H15.
  rewrite Htmp in H15.
  rewrite Hrear in H15.
  (* unfold inv_e28_clean in Hinve28.
  simpl in Hinve28.
  apply Hinve28 in H15; auto. *)

  destruct (Fin.eq_dec (Fin.of_nat_lt (mod_lt H (ArrayQueueImpl.front LState pid)))
    (Fin.of_nat_lt (mod_lt H (ArrayQueueImpl.rear LState pid0)))).
    rewrite e in H2.
    rewrite Vector.nth_replace_eq in H2.
    rewrite e in H15.
    rewrite Hx in H2.
    rewrite H15 in H2.
    eapply inv_xp_ref_le_vec_rear_ref_invariant with (H:=H) in HreachTmp3; eauto.
    unfold get_pc, get_xp, get_vec_rear in *; simpl in *.
    unfold get_impl in *; simpl in *.
    specialize (HreachTmp3 pid0 AEnq28).
    rewrite H2 in HreachTmp3.
    simpl in HreachTmp3.
    assert (Hafter : after_e6 AEnq28).

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
          solve_after_e6.
          apply HreachTmp3 in Hafter; auto. lia.

    rewrite Vector.nth_replace_neq in H2; auto.
    unfold inv_e28_clean in Hinve28.
    simpl in Hinve28.
    apply Hinve28 in H2; auto.
    destruct H2 as [H21 H22].
    (* intuition. *)
    rewrite H21.
    unfold F, R in *; simpl.
    unfold get_rear, get_front, get_pc in *; simpl in *.
    apply array_queue_wf_invarint in HreachTmp3.
    unfold array_queue_wf in HreachTmp3.
    simpl in HreachTmp3.
    apply binds_reconstruct in Hb3.
    destruct Hb3 as [l1 [l2 Hlist]].
    rewrite Hlist.
    rewrite Hlist in HreachTmp3.
    apply ok_remove_middle_inv in HreachTmp3.
    destruct HreachTmp3 as [Hokl [Hnt1 Hnt2]].
    repeat rewrite get_r'_dist.
    simpl.
    repeat rewrite get_r'_any_ary; auto.
    intuition.
    repeat rewrite get_f'_dist.
    simpl.
    rewrite Nat.eqb_refl.
    repeat rewrite get_f'_any_ary; auto.
    rewrite Hlist in H22.
    repeat rewrite get_r'_dist in H22.
    simpl in H22.
    repeat rewrite get_r'_any_ary in H22; auto.
    repeat rewrite get_f'_dist in H22; auto.
    simpl in H22.
    apply notin_get_none in Hnotin_res.
    rewrite Hnotin_res in H22.
    lia.

  tmp' noB_preserves_ADeq31 Hvalid st2 pid acts Hgather Hb3.
        (* false *)
        * rewrite get_r'_any_ary_cas_false; auto.
          rewrite get_f'_any_ary_cas_false; auto.
        (* REAR *)
      +++ rewrite get_r'_any_ary_read; auto.
        rewrite get_f'_any_ary_read; auto.
      --- unfold inv_d28_clean.
        intros.
        destruct (eq_nat_dec pid pid0).
        + subst.
          pose proof Hreach as HreachTmp.
          apply IHk in Hreach; try lia.
          unfold inv_total in Hreach.
          destruct Hreach as [_ [Hinv _]].
          unfold inv_d28_clean in Hinv.
          inversion H1; subst; simpl in *.
          inversion H3; subst; simpl in *.
          unfold R, F; simpl.
          unfold get_pc, get_rear, get_front, get_ary; simpl.
          inversion H4; subst; simpl in *.
          (* front_rear *)
          ++ inversion H5; subst; simpl in *.
            inversion H6; subst; simpl in *.
            (* rear *)
            +++ inversion H7; subst; simpl in *.
              inversion H8; subst; simpl in *.
              (* INC *)
              * apply reachable_len_to_reachable in HreachTmp.
                apply inv_rear_inc_at_e31_invariant in HreachTmp.
                unfold inv_rear_inc_at_e31 in HreachTmp.
                apply HreachTmp in Hbinds5; auto.
                simpl in Hbinds5.
                unfold binds in H0.
                rewrite Hbinds5 in H0; discriminate.
              * rewrite get_r'_any_rear_read; auto.
            (* front *)
            +++ inversion H7; subst; simpl in *.
              inversion H8; subst; simpl in *.
              (* INC *)
              * apply reachable_len_to_reachable in HreachTmp.
                apply inv_front_inc_at_d31_invariant in HreachTmp.
                unfold inv_front_inc_at_d31 in HreachTmp.
                apply HreachTmp in Hbinds5; auto.
                simpl in Hbinds5.
                unfold binds in H0.
                rewrite Hbinds5 in H0; discriminate.
              * rewrite get_f'_any_rear_read; auto.
          (* array *)
          ++ inversion H5; subst; simpl in *.
            inversion H6; subst; simpl in *.
            (* CAS *)
            +++ destruct ((entry_eqb
              (Vector.nth vec (Fin.of_nat_lt Hlt))
              (old)))eqn:Heq.
              (* success *)
              * apply entry_eqb_eq in Heq.
                subst.
                apply reachable_len_to_reachable in HreachTmp.
                apply step_invariant in HreachTmp.
                unfold ComposedLTS.inv in HreachTmp.
                simpl in HreachTmp.
                apply HreachTmp in Hbinds0; auto.
                destruct Hbinds0 as [s1 [s2 [q [acts [Hint_query [Hvalid Hgather]]]]]].
                inversion Hint_query; subst; simpl in *.
                inversion H7; subst; simpl in *.
                unfold binds in H0.
                inversion H9; subst; simpl in *.
                (* Ltac tmp H Hvalid st2 pid0 acts Hgather H0 :=
                (
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
      (rewrite Hvalid in H0; discriminate)). *)
  tmp noB_preserves_AEnq2 Hvalid st2 pid0 acts Hgather H0.
  tmp noB_preserves_AEnq5 Hvalid st2 pid0 acts Hgather H0.
  tmp noB_preserves_AEnq11 Hvalid st2 pid0 acts Hgather H0.
  tmp noB_preserves_AEnq14 Hvalid st2 pid0 acts Hgather H0.
  tmp noB_preserves_AEnq28 Hvalid st2 pid0 acts Hgather H0.
  tmp noB_preserves_AEnq31 Hvalid st2 pid0 acts Hgather H0.
  tmp noB_preserves_ADeq2 Hvalid st2 pid0 acts Hgather H0.
  tmp noB_preserves_ADeq5 Hvalid st2 pid0 acts Hgather H0.
  tmp noB_preserves_ADeq11 Hvalid st2 pid0 acts Hgather H0.
  tmp noB_preserves_ADeq14 Hvalid st2 pid0 acts Hgather H0.

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
  inversion H8; subst; simpl in *.
  inversion H10; subst; simpl in *.
  inversion H12; subst; simpl in *.
  inversion H11; subst; simpl in *.
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
  rewrite Htmp in H2.
  rewrite Hrear in H2.
  rewrite Vector.nth_replace_eq in H2.
  rewrite Hx in H2.
  destruct (ArrayQueueImpl.x LState pid0).
  simpl in H2.
  inversion H2; subst.
  lia.
  tmp noB_preserves_ADeq31 Hvalid st2 pid0 acts Hgather H0.
        (* false *)
        * rewrite get_r'_any_ary_cas_false; auto.
          rewrite get_f'_any_ary_cas_false; auto.
      (* READ *)
      +++ rewrite get_r'_any_ary_read; auto.
        rewrite get_f'_any_ary_read; auto.
    + pose proof Hreach as HreachTmp;
      apply IHk in Hreach; try lia.
      unfold inv_total in Hreach.
      destruct Hreach as [_ [Hinve28 [_ [_ [_ [_ [_ [Hinv3 _]]]]]]]].
      inversion H1; subst; simpl in *.
      inversion H3; subst; simpl in *.
      unfold R, F in *; simpl in *.
      unfold get_rear, get_pc, get_front, get_ary in *; simpl in *.
      inversion H4; subst; simpl in *.
      (* front_rear *)
      ++ inversion H5; subst; simpl in *.
        inversion H6; subst; simpl in *.
        (* rear *)
        +++ unfold inv_d28_clean in Hinve28.
          simpl in Hinve28.
          apply Hinve28 in H0; auto.
            unfold R, F in H0.
            unfold get_front, get_rear, get_ary, get_pc in H0; simpl in H0.
            intuition.
          inversion H7; subst; simpl in *.
          inversion H0; subst; simpl in *.
          (* inc *)
          * apply reachable_len_to_reachable in HreachTmp.
            pose proof HreachTmp as HreachTmp2.
            apply inv_rear_inc_at_e31_invariant in HreachTmp.
            unfold inv_rear_inc_at_e31 in HreachTmp.
            simpl in HreachTmp.
            apply HreachTmp in Hbinds5; auto.
            apply array_queue_wf_invarint in HreachTmp2.
            unfold array_queue_wf in HreachTmp2.
            simpl in HreachTmp2.
            apply binds_reconstruct in Hbinds5.
            destruct Hbinds5 as [l1 [l2 Hlist]].
            rewrite Hlist in HreachTmp2.
            apply ok_remove_middle_inv in HreachTmp2.
            destruct HreachTmp2 as [Hokapp [Hnti1 Hnti2]].
            rewrite Hlist.
            rewrite get_r'_dist.
            rewrite <-Hlist.
            rewrite get_r'_dist.
            simpl.
            rewrite Nat.eqb_refl.
            simpl.
            rewrite get_r'_any_rear_push; auto.
            rewrite get_r'_any_rear_push; auto.
            rewrite Hlist in H9.
            rewrite get_r'_dist in H9.
            rewrite <-Hlist in H9.
            rewrite get_r'_dist in H9.
            simpl in H9.
            apply notin_get_none in Hnotin_res.
            rewrite Hnotin_res in H9. lia.
          * rewrite get_r'_any_rear_read; auto.
        (* front *)
        +++ inversion H7; subst; simpl in *.
          inversion H8; subst; simpl in *.
          (* inc *)
          * unfold inv_d28_clean in Hinve28.
            apply Hinve28 in H0; auto.
            apply reachable_len_to_reachable in HreachTmp.
            pose proof HreachTmp as HreachTmp2.
            apply inv_front_inc_at_d31_invariant in HreachTmp.
            unfold inv_front_inc_at_d31 in HreachTmp.
            simpl in HreachTmp.
            apply HreachTmp in Hbinds5; auto.
            exfalso.
            destruct H0 as [HrearR _].
            unfold F, R in HrearR.
            unfold get_front, get_rear, get_ary, get_pc in HrearR; simpl in HrearR.
            assert (Hgt : 0 < v + get_f' (pc (LState st2)) (Array.responses L (LState st1)) res).
            pose proof Hbinds5 as HbindsTmp.
            apply binds_reconstruct in Hbinds5.
            destruct Hbinds5 as [l1 [l2 Hlist]].
            rewrite Hlist.
            rewrite get_f'_dist.
            rewrite get_f'_dist.
            simpl.
            apply notin_get_none in Hnotin_res.
            rewrite Hnotin_res. lia.
            rewrite <-HrearR in Hgt.
            assert (Hsub1 : forall x y, x = y -> x - 1 = y - 1).
            intros; lia.
            apply Hsub1 in HrearR.
            unfold inv_3' in Hinv3.
            simpl in Hinv3.
            unfold F, R in Hinv3.
            unfold get_front, get_rear, get_ary, get_pc in Hinv3; simpl in Hinv3.
            erewrite <-Hinv3 with (pid:=pid) in HrearR; eauto.
            apply inv_front_invariant in HreachTmp2; auto.
            unfold inv_front in HreachTmp2.
            simpl in HreachTmp2.
            intuition.
            specialize (H10 pid0). lia.
            unfold deq_not_inc.
            right. right. right.
            intuition.
          (* read *)
          * rewrite get_f'_any_rear_read; auto.
      (* array *)
      ++ inversion H5; subst; simpl in *.
        inversion H6; subst; simpl in *.
        (* CAS *)
            +++ destruct ((entry_eqb
              (Vector.nth vec (Fin.of_nat_lt Hlt))
              (old)))eqn:Heq.
              (* success *)
              * apply entry_eqb_eq in Heq.
                subst.
                apply reachable_len_to_reachable in HreachTmp.
                pose proof HreachTmp as HreachTmp2.
                apply step_invariant in HreachTmp.
                unfold ComposedLTS.inv in HreachTmp.
                simpl in HreachTmp.
                apply HreachTmp in Hbinds0; auto.
                destruct Hbinds0 as [s1 [s2 [q [acts [Hint_query [Hvalid Hgather]]]]]].
                inversion Hint_query; subst; simpl in *.
                inversion H7; subst; simpl in *.
                unfold binds in H0.
                pose proof HreachTmp2 as HreachTmp3.
                apply inv_ary_cas_at_e28_d28_invariant in HreachTmp2.
                unfold inv_ary_cas_at_e28_d28 in HreachTmp2.
                simpl in HreachTmp2.
                pose proof Hbinds3 as Hbind3Tmp.
                apply HreachTmp2 in Hbinds3.
                destruct Hbinds3 as [Hb3|Hb3].

          (* Enq28 *)
          ** unfold binds in Hb3.
            inversion H9; subst; simpl in *.
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
  inversion H8; subst; simpl in *.
  inversion H10; subst; simpl in *.
  inversion H12; subst; simpl in *.
  inversion H11; subst; simpl in *.
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
  rewrite Htmp in H2.
  rewrite Hrear in H2.

  rewrite Hx in H15.
  rewrite Htmp in H15.
  rewrite Hrear in H15.
  (* unfold inv_e28_clean in Hinve28.
  simpl in Hinve28.
  apply Hinve28 in H15; auto. *)

  destruct (Fin.eq_dec (Fin.of_nat_lt (mod_lt H (ArrayQueueImpl.rear LState pid)))
    (Fin.of_nat_lt (mod_lt H (ArrayQueueImpl.front LState pid0)))).
    rewrite e in H2.
    rewrite Vector.nth_replace_eq in H2.
    rewrite e in H15.
    rewrite Hx in H2.
    rewrite H15 in H2.
    eapply inv_xp_ref_le_vec_front_ref_invariant with (H:=H) in HreachTmp3; eauto.
    unfold get_pc, ArrayQueueInvariantBefore0.get_xp, get_vec_front in *; simpl in *.
    unfold ArrayQueueInvariantBefore0.get_impl in *; simpl in *.
    specialize (HreachTmp3 pid0 ADeq28).
    rewrite H2 in HreachTmp3.
    simpl in HreachTmp3.
    assert (Hafter : after_d6 ADeq28).

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
          solve_after_d6.
          apply HreachTmp3 in Hafter; auto.
          simpl in Hafter. lia.

    rewrite Vector.nth_replace_neq in H2; auto.
    unfold inv_d28_clean in Hinve28.
    simpl in Hinve28.
    apply Hinve28 in H2; auto.
    destruct H2 as [H21 H22].
    (* intuition. *)
    rewrite H21.
    unfold F, R in *; simpl.
    unfold get_rear, get_front, get_pc in *; simpl in *.
    apply array_queue_wf_invarint in HreachTmp3.
    unfold array_queue_wf in HreachTmp3.
    simpl in HreachTmp3.
    apply binds_reconstruct in Hb3.
    destruct Hb3 as [l1 [l2 Hlist]].
    rewrite Hlist.
    rewrite Hlist in HreachTmp3.
    apply ok_remove_middle_inv in HreachTmp3.
    destruct HreachTmp3 as [Hokl [Hnt1 Hnt2]].
    repeat rewrite get_f'_dist.
    simpl.
    repeat rewrite get_f'_any_ary; auto.
    intuition.
    repeat rewrite get_r'_dist.
    simpl.
    rewrite Nat.eqb_refl.
    repeat rewrite get_r'_any_ary; auto.
    rewrite Hlist in H22.
    repeat rewrite get_f'_dist in H22.
    simpl in H22.
    repeat rewrite get_f'_any_ary in H22; auto.
    repeat rewrite get_r'_dist in H22; auto.
    simpl in H22.
    apply notin_get_none in Hnotin_res.
    rewrite Hnotin_res in H22.
    lia.

  tmp' noB_preserves_AEnq31 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_ADeq2 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_ADeq5 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_ADeq11 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_ADeq14 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_ADeq28 Hvalid st2 pid acts Hgather Hb3.
  tmp' noB_preserves_ADeq31 Hvalid st2 pid acts Hgather Hb3.

                (* Deq28 *)
                ** unfold binds in Hb3.
                  inversion H9; subst; simpl in *.
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
  inversion H8; subst; simpl in *.
  inversion H10; subst; simpl in *.
  inversion H12; subst; simpl in *.
  inversion H11; subst; simpl in *.
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
  rewrite Htmp in H2.
  rewrite Hrear in H2.

  rewrite Hx in H15.
  rewrite Htmp in H15.
  rewrite Hrear in H15.
  unfold inv_d28_clean in Hinve28.
  simpl in Hinve28.
  apply Hinve28 in H15; auto.

  destruct (Fin.eq_dec (Fin.of_nat_lt (mod_lt H (ArrayQueueImpl.front LState pid)))
    (Fin.of_nat_lt (mod_lt H (ArrayQueueImpl.front LState pid0)))).
    rewrite e in H2.
    rewrite Vector.nth_replace_eq in H2.

    rewrite Hx in H2.
    apply inv_d28_x_none_invariant in HreachTmp3.
    unfold inv_d28_x_none in HreachTmp3.
    simpl in HreachTmp3.
    apply HreachTmp3 in H0; auto.
    destruct (ArrayQueueImpl.x LState pid0).
    simpl in H2.
    rewrite H2 in H0.
    simpl in H0. unfold not_none_wrapper in H0.
    intuition.
  rewrite Vector.nth_replace_neq in H2; auto.
    apply Hinve28 in H2; auto.
    destruct H15 as [H151 H152].
    destruct H2 as [H21 H22].
    rewrite <-H21 in H151.
    rewrite H151 in n1. intuition.
  tmp' noB_preserves_ADeq31 Hvalid st2 pid acts Hgather Hb3.
        (* false *)
        * rewrite get_r'_any_ary_cas_false; auto.
          rewrite get_f'_any_ary_cas_false; auto.
        (* REAR *)
      +++ rewrite get_r'_any_ary_read; auto.
        rewrite get_f'_any_ary_read; auto.
    --- unfold inv_1. intros.
      pose proof Hreach as HreachTmp.
      apply IHk in Hreach; try lia.
      unfold inv_total in Hreach.
      destruct Hreach as [_ [_ [Hinv1 [_ [Hinv2 [_ [_ [_ [Hinv4 _]]]]]]]]].
      inversion H1; subst; simpl in *.
      inversion H3; subst; simpl in *.
      unfold R in *; simpl in *.
      unfold get_rear, get_pc, get_ary in *; simpl in *.
      inversion H4; subst; simpl in *.
      (* front_rear *)
      + inversion H5; subst; simpl in *.
        inversion H6; subst; simpl in *.
        (* rear *)
        ++ inversion H7; subst; simpl in *.
          inversion H8; subst; simpl in *.
          (* Inc *)
          +++ unfold inv_2 in Hinv2.
            simpl in Hinv2.
            unfold R, F in *; simpl in *.
            unfold get_rear, get_front, get_pc, get_ary in *; simpl in *.
            intuition.
            * apply eq_S in H9.
              rewrite H2 in H9.
              apply reachable_len_to_reachable in HreachTmp.
              pose proof HreachTmp as HreachTmp2.
              apply inv_rear_inc_at_e31_invariant in HreachTmp.
              unfold inv_rear_inc_at_e31 in HreachTmp.
              simpl in HreachTmp.
              apply HreachTmp in Hbinds5; auto.
              apply binds_reconstruct in Hbinds5.
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              destruct Hbinds5 as [l1 [l2 Hlist]].
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              apply ok_concat_inv in Hokl.
              rewrite Hlist in H9.
              repeat rewrite get_r'_dist in H9.
              simpl in H9.
              rewrite Nat.eqb_refl in H9.
              apply notin_get_none in Hnotin_res.
              rewrite Hnotin_res in H9.
              simpl in H9.
              rewrite get_r'_any_rear_push in H9; auto.
              rewrite get_r'_any_rear_push in H9; auto.
              exfalso.
              simpl in H9.
              rewrite Nat.sub_0_r in H9.
              lia.
            * apply eq_S in H9.
              rewrite H2 in H9.
              apply reachable_len_to_reachable in HreachTmp.
              pose proof HreachTmp as HreachTmp2.
              apply inv_rear_inc_at_e31_invariant in HreachTmp.
              unfold inv_rear_inc_at_e31 in HreachTmp.
              simpl in HreachTmp.
              apply HreachTmp in Hbinds5; auto.
              apply binds_reconstruct in Hbinds5.
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              destruct Hbinds5 as [l1 [l2 Hlist]].
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              apply ok_concat_inv in Hokl.
              rewrite Hlist in H9.
              repeat rewrite get_r'_dist in H9.
              simpl in H9.
              rewrite Nat.eqb_refl in H9.
              apply notin_get_none in Hnotin_res.
              rewrite Hnotin_res in H9.
              simpl in H9.
              rewrite get_r'_any_rear_push in H9; auto.
              rewrite get_r'_any_rear_push in H9; auto.
              exfalso.
              simpl in H9.
              rewrite Nat.sub_0_r in H9.
              lia.
          (* read *)
          +++ rewrite get_r'_any_rear_read in H2; auto.
            rewrite get_r'_any_rear_read in H0; auto.
            unfold inv_1 in Hinv1.
            unfold R, F in *; simpl in *.
            unfold get_rear, get_front, get_pc, get_ary in *; simpl in *.
            apply Hinv1 in H2; auto.
            destruct H2 as [pid' [Hpid1 Hpid2]].
            exists pid'.
            destruct (eq_nat_dec pid pid').
            * subst.
              unfold enq_not_inc in Hpid1.
              simpl in Hpid1.
              apply inv_rear_read_at_e2_e11_d14 with (pid:=pid') in HreachTmp; auto.
              unfold get_pc in *; simpl in *.
              unfold binds in HreachTmp.
              exfalso.
              destruct HreachTmp as [Hn|[Hn|Hn]];
              intuition;
              try (rewrite H9 in Hn; discriminate);
              try (rewrite H2 in Hn; discriminate).
            * intuition.
              ** unfold enq_not_inc in *; simpl in *.
                intuition.
                right. right. right.
                intuition.
                apply notin_union; intuition.
                apply notin_neq; auto.
              ** eapply Hpid2; eauto.
                unfold enq_not_inc in *; simpl in *.
                clear Hpid1.
                intuition.
                right. right. right.
                apply notin_union in H12.
                intuition.
        ++ unfold inv_1 in Hinv1.
          unfold R in *; simpl in *.
          unfold get_rear, get_pc, get_ary in *; simpl in *.
          intuition.
      (* array *)
      + unfold inv_1 in Hinv1.
          unfold R in *; simpl in *.
          unfold get_rear, get_pc, get_ary in *; simpl in *.
          inversion H5; subst; simpl in *.
          inversion H6; subst; simpl in *.
          (* CAS *)
          ++ destruct (entry_eqb (Vector.nth vec (Fin.of_nat_lt Hlt)))eqn:Heq.
            (* success *)
            +++ apply reachable_len_to_reachable in HreachTmp.
              apply inv_ary_cas_at_e28_d28_invariant in HreachTmp.
              unfold inv_ary_cas_at_e28_d28 in HreachTmp.
              simpl in HreachTmp.
              apply HreachTmp in Hbinds3; auto.
              intuition.
              (* e28 *)
              * exists pid.
                intuition.
                ** unfold enq_not_inc.
                  left. intuition.
                  simpl. apply binds_push_eq; auto.
                ** unfold inv_4 in Hinv4.
                  simpl in Hinv4.
                  unfold R in *; simpl in *.
                  unfold get_rear, get_pc, get_ary in *; simpl in *.
                  apply binds_reconstruct in H9.
                  destruct H9 as [l1 [l2 Hlist]].
                  apply array_queue_wf_invarint in H8.
                  unfold array_queue_wf in H8.
                  simpl in H8.
                  rewrite Hlist in H8.
                  apply ok_remove_middle_inv in H8.
                  destruct H8 as [Hokl [Hnt1 Hnt2]].
                  rewrite Hlist in H2.
                  repeat rewrite get_r'_dist in H2; auto.
                  simpl in H2.
                  rewrite Nat.eqb_refl in H2.
                  rewrite get_r'_any_ary in H2; auto.
                  rewrite get_r'_any_ary in H2; auto.
                  simpl in H2.
                  rewrite Nat.add_succ_r in H2; simpl.
                  rewrite Nat.add_succ_r in H2; simpl.
                  assert (Htmp : forall m, (S m) - 1 = m)
                  by lia.
                  rewrite Htmp in H2.
                  apply notin_get_none in Hnotin_res.
                  rewrite Hlist in Hinv4.
                  repeat rewrite get_r'_dist in Hinv4; auto.
                  simpl in Hinv4.
                  rewrite Hnotin_res in Hinv4.
                  simpl in Hinv4. intuition.
                  apply H8 with (pid:=pid'); auto.
                  simpl in Hlist.
                  rewrite <-Hlist.
                  unfold enq_not_inc in *; simpl in *.
                  intuition.
                  apply binds_push_neq_inv in H12; auto.
              (* Deq *)
              * pose proof H9 as HbindsTmp.
                apply binds_reconstruct in H9.
                destruct H9 as [l1 [l2 Hlist]].
                apply array_queue_wf_invarint in H8.
                unfold array_queue_wf in H8.
                simpl in H8.
                rewrite Hlist in H8.
                apply ok_remove_middle_inv in H8.
                destruct H8 as [Hokl [Hnt1 Hnt2]].
                rewrite Hlist in H2.
                repeat rewrite get_r'_dist in H2; auto.
                simpl in H2.
                unfold inv_1 in Hinv1.
                simpl in Hinv1.
                rewrite Hlist in Hinv1.
                repeat rewrite get_r'_dist in Hinv1; auto.
                simpl in Hinv1.
                rewrite Hlist in H0.
                repeat rewrite get_r'_dist in H0; auto.
                simpl in H0.
                rewrite get_r'_any_ary in H2; auto.
                rewrite get_r'_any_ary in H2; auto.
                rewrite get_r'_any_ary in H0; auto.
                rewrite get_r'_any_ary in H0; auto.
                intuition.
                destruct H9 as [pid0 [Hpid1 Hpid2]].
                simpl in Hlist.
                rewrite <-Hlist in Hpid1.
                rewrite <-Hlist in Hpid2.
                destruct (eq_nat_dec pid pid0).
                ** subst.
                  unfold enq_not_inc in Hpid1; simpl in Hpid1.
                  unfold binds in HbindsTmp.
                  intuition;
                  try (rewrite H9 in HbindsTmp; discriminate);
                  try (rewrite H8 in HbindsTmp; discriminate).
                ** exists pid0. split.
                  *** unfold enq_not_inc in *; simpl in *.
                    intuition.
                    left. intuition.
                    apply binds_push_neq; auto.
                  *** intuition.
                    apply Hpid2 in H8; auto.
                    unfold enq_not_inc in *; simpl in *.
                    clear Hpid1.
                    intuition.
                    left. intuition.
                    apply binds_push_inv in H11.
                    intuition.
                    subst. unfold binds in HbindsTmp.
                    rewrite H9 in HbindsTmp; discriminate.
            (* fail *)
            +++ rewrite get_r'_any_ary_cas_false in H2; auto.
              rewrite get_r'_any_ary_cas_false in H0; auto.
              unfold inv_1 in Hinv1.
              unfold R in *; simpl in *.
              unfold get_rear, get_pc, get_ary in *; simpl in *.
              intuition.
              destruct H8 as [pid' [Hpid1 Hpid2]].
              exists pid'. intuition.
              * unfold enq_not_inc in *; simpl in *.
                intuition.
                left. intuition.
                destruct (eq_nat_dec pid pid').
                subst.
                apply binds_in in H9.
                unfold "#" in Hnotin_res; intuition.
                apply binds_push_neq; auto.
              * apply Hpid2 in H7; auto.
                unfold enq_not_inc in *; simpl in *.
                clear Hpid1.
                intuition.
                left.
                intuition.
                apply binds_push_inv in H10; auto.
                intuition.
                discriminate.
          (* READ *)
          ++ rewrite get_r'_any_ary_read in H2; auto.
            rewrite get_r'_any_ary_read in H0; auto.
              unfold inv_1 in Hinv1.
              unfold R in *; simpl in *.
              unfold get_rear, get_pc, get_ary in *; simpl in *.
              intuition.
              destruct H8 as [pid' [Hpid1 Hpid2]].
              exists pid'. intuition.
              * unfold enq_not_inc in *; simpl in *.
                intuition.
                left. intuition.
                destruct (eq_nat_dec pid pid').
                subst.
                apply binds_in in H9.
                unfold "#" in Hnotin_res; intuition.
                apply binds_push_neq; auto.
              * apply Hpid2 in H7; auto.
                unfold enq_not_inc in *; simpl in *.
                clear Hpid1.
                intuition.
                left.
                intuition.
                apply binds_push_inv in H10; auto.
                intuition.
                discriminate.
      (* inv_1' *)
    --- unfold inv_1'. intros.
      pose proof Hreach as HreachTmp.
      apply IHk in Hreach; try lia.
      unfold inv_total in Hreach.
      destruct Hreach as [_ [_ [_ [Hinv1 [_ [Hinv2 [_ [_ [_ [Hinv4 _]]]]]]]]]].
      inversion H1; subst; simpl in *.
      inversion H3; subst; simpl in *.
      unfold F, R in *; simpl in *.
      unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
      inversion H4; subst; simpl in *.
      (* front_rear *)
      + inversion H5; subst; simpl in *.
        inversion H6; subst; simpl in *.
        (* rear *)
        ++ unfold inv_1' in Hinv1.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          intuition.
        (* front *)
        ++ inversion H7; subst; simpl in *.
          inversion H8; subst; simpl in *.
          (* Inc *)
          +++ unfold inv_2' in Hinv2.
            simpl in Hinv2.
            unfold R, F in *; simpl in *.
            unfold get_rear, get_front, get_pc, get_ary in *; simpl in *.
            intuition.
            * apply eq_S in H9.
              rewrite H2 in H9.
              apply reachable_len_to_reachable in HreachTmp.
              pose proof HreachTmp as HreachTmp2.
              apply inv_front_inc_at_d31_invariant in HreachTmp.
              unfold inv_front_inc_at_d31 in HreachTmp.
              simpl in HreachTmp.
              apply HreachTmp in Hbinds5; auto.
              apply binds_reconstruct in Hbinds5.
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              destruct Hbinds5 as [l1 [l2 Hlist]].
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              apply ok_concat_inv in Hokl.
              rewrite Hlist in H9.
              repeat rewrite get_r'_dist in H9.
              repeat rewrite get_f'_dist in H9.
              simpl in H9.
              rewrite Nat.eqb_refl in H9.
              apply notin_get_none in Hnotin_res.
              rewrite Hnotin_res in H9.
              simpl in H9.
              rewrite get_f'_any_rear_push in H9; auto.
              rewrite get_f'_any_rear_push in H9; auto.
              exfalso.
              simpl in H9.
              rewrite Nat.sub_0_r in H9.
              lia.
            * apply eq_S in H9.
              rewrite H2 in H9.
              apply reachable_len_to_reachable in HreachTmp.
              pose proof HreachTmp as HreachTmp2.
              apply inv_front_inc_at_d31_invariant in HreachTmp.
              unfold inv_front_inc_at_d31 in HreachTmp.
              simpl in HreachTmp.
              apply HreachTmp in Hbinds5; auto.
              apply binds_reconstruct in Hbinds5.
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              destruct Hbinds5 as [l1 [l2 Hlist]].
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              apply ok_concat_inv in Hokl.
              rewrite Hlist in H9.
              repeat rewrite get_r'_dist in H9.
              repeat rewrite get_f'_dist in H9.
              simpl in H9.
              rewrite Nat.eqb_refl in H9.
              apply notin_get_none in Hnotin_res.
              rewrite Hnotin_res in H9.
              simpl in H9.
              rewrite get_f'_any_rear_push in H9; auto.
              rewrite get_f'_any_rear_push in H9; auto.
              exfalso.
              simpl in H9.
              rewrite Nat.sub_0_r in H9.
              lia.
          (* read *)
          +++ rewrite get_f'_any_rear_read in H2; auto.
            rewrite get_f'_any_rear_read in H0; auto.
            unfold inv_1 in Hinv1.
            unfold R, F in *; simpl in *.
            unfold get_rear, get_front, get_pc, get_ary in *; simpl in *.
            apply Hinv1 in H2; auto.
            destruct H2 as [pid' [Hpid1 Hpid2]].
            exists pid'.
            destruct (eq_nat_dec pid pid').
            * subst.
              unfold deq_not_inc in Hpid1.
              simpl in Hpid1.
              apply inv_front_read_at_d2_d11_e14 with (pid:=pid') in HreachTmp; auto.
              unfold get_pc in *; simpl in *.
              unfold binds in HreachTmp.
              exfalso.
              destruct HreachTmp as [Hn|[Hn|Hn]];
              intuition;
              try (rewrite H9 in Hn; discriminate);
              try (rewrite H2 in Hn; discriminate).
            * intuition.
              ** unfold deq_not_inc in *; simpl in *.
                intuition.
                right. right. right.
                intuition.
                apply notin_union; intuition.
                apply notin_neq; auto.
              ** eapply Hpid2; eauto.
                unfold deq_not_inc in *; simpl in *.
                clear Hpid1.
                intuition.
                right. right. right.
                apply notin_union in H11.
                intuition.
        (* ++ unfold inv_1 in Hinv1.
          unfold R in *; simpl in *.
          unfold get_rear, get_pc, get_ary in *; simpl in *.
          intuition. *)
      (* array *)
      + unfold inv_1' in Hinv1.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          inversion H5; subst; simpl in *.
          inversion H6; subst; simpl in *.
          (* CAS *)
          ++ destruct (entry_eqb (Vector.nth vec (Fin.of_nat_lt Hlt)))eqn:Heq.
            (* success *)
            +++ apply reachable_len_to_reachable in HreachTmp.
              apply inv_ary_cas_at_e28_d28_invariant in HreachTmp.
              unfold inv_ary_cas_at_e28_d28 in HreachTmp.
              simpl in HreachTmp.
              apply HreachTmp in Hbinds3; auto.
              intuition.

              (* e28 *)
              * pose proof H9 as HbindsTmp.
                apply binds_reconstruct in H9.
                destruct H9 as [l1 [l2 Hlist]].
                apply array_queue_wf_invarint in H8.
                unfold array_queue_wf in H8.
                simpl in H8.
                rewrite Hlist in H8.
                apply ok_remove_middle_inv in H8.
                destruct H8 as [Hokl [Hnt1 Hnt2]].
                rewrite Hlist in H2.
                repeat rewrite get_f'_dist in H2; auto.
                simpl in H2.
                unfold inv_1 in Hinv1.
                simpl in Hinv1.
                rewrite Hlist in Hinv1.
                repeat rewrite get_f'_dist in Hinv1; auto.
                simpl in Hinv1.
                rewrite Hlist in H0.
                repeat rewrite get_f'_dist in H0; auto.
                simpl in H0.
                rewrite get_f'_any_ary in H2; auto.
                rewrite get_f'_any_ary in H2; auto.
                rewrite get_f'_any_ary in H0; auto.
                rewrite get_f'_any_ary in H0; auto.
                intuition.
                destruct H9 as [pid0 [Hpid1 Hpid2]].
                simpl in Hlist.
                rewrite <-Hlist in Hpid1.
                rewrite <-Hlist in Hpid2.
                destruct (eq_nat_dec pid pid0).
                ** subst.
                  unfold deq_not_inc in Hpid1; simpl in Hpid1.
                  unfold binds in HbindsTmp.
                  intuition;
                  try (rewrite H9 in HbindsTmp; discriminate);
                  try (rewrite H8 in HbindsTmp; discriminate).
                ** exists pid0. split.
                  *** unfold deq_not_inc in *; simpl in *.
                    intuition.
                    left. intuition.
                    apply binds_push_neq; auto.
                  *** intuition.
                    apply Hpid2 in H8; auto.
                    unfold deq_not_inc in *; simpl in *.
                    clear Hpid1.
                    intuition.
                    left. intuition.
                    apply binds_push_inv in H11.
                    intuition.
                    subst. unfold binds in HbindsTmp.
                    rewrite H9 in HbindsTmp; discriminate.

              (* d28 *)
              * exists pid.
                intuition.
                ** unfold deq_not_inc.
                  left. intuition.
                  simpl. apply binds_push_eq; auto.
                ** unfold inv_4' in Hinv4.
                  simpl in Hinv4.
                  unfold F, R in *; simpl in *.
                  unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
                  apply binds_reconstruct in H9.
                  destruct H9 as [l1 [l2 Hlist]].
                  apply array_queue_wf_invarint in H8.
                  unfold array_queue_wf in H8.
                  simpl in H8.
                  rewrite Hlist in H8.
                  apply ok_remove_middle_inv in H8.
                  destruct H8 as [Hokl [Hnt1 Hnt2]].
                  rewrite Hlist in H2.
                  repeat rewrite get_f'_dist in H2; auto.
                  simpl in H2.
                  rewrite Nat.eqb_refl in H2.
                  rewrite get_f'_any_ary in H2; auto.
                  rewrite get_f'_any_ary in H2; auto.
                  simpl in H2.
                  rewrite Nat.add_succ_r in H2; simpl.
                  rewrite Nat.add_succ_r in H2; simpl.
                  assert (Htmp : forall m, (S m) - 1 = m)
                  by lia.
                  rewrite Htmp in H2.
                  apply notin_get_none in Hnotin_res.
                  rewrite Hlist in Hinv4.
                  repeat rewrite get_f'_dist in Hinv4; auto.
                  simpl in Hinv4.
                  rewrite Hnotin_res in Hinv4.
                  simpl in Hinv4. intuition.
                  apply H8 with (pid:=pid'); auto.
                  simpl in Hlist.
                  rewrite <-Hlist.
                  unfold deq_not_inc in *; simpl in *.
                  intuition.
                  apply binds_push_neq_inv in H12; auto.
            (* fail *)
            +++ rewrite get_f'_any_ary_cas_false in H2; auto.
              rewrite get_f'_any_ary_cas_false in H0; auto.
              unfold inv_1' in Hinv1.
              unfold F, R in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              intuition.
              destruct H8 as [pid' [Hpid1 Hpid2]].
              exists pid'. intuition.
              * unfold deq_not_inc in *; simpl in *.
                intuition.
                left. intuition.
                destruct (eq_nat_dec pid pid').
                subst.
                apply binds_in in H9.
                unfold "#" in Hnotin_res; intuition.
                apply binds_push_neq; auto.
              * apply Hpid2 in H7; auto.
                unfold deq_not_inc in *; simpl in *.
                clear Hpid1.
                intuition.
                left.
                intuition.
                apply binds_push_inv in H10; auto.
                intuition.
                discriminate.
          (* READ *)
          ++ rewrite get_f'_any_ary_read in H2; auto.
            rewrite get_f'_any_ary_read in H0; auto.
              unfold inv_1' in Hinv1.
              unfold F, R in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              intuition.
              destruct H8 as [pid' [Hpid1 Hpid2]].
              exists pid'. intuition.
              * unfold deq_not_inc in *; simpl in *.
                intuition.
                left. intuition.
                destruct (eq_nat_dec pid pid').
                subst.
                apply binds_in in H9.
                unfold "#" in Hnotin_res; intuition.
                apply binds_push_neq; auto.
              * apply Hpid2 in H7; auto.
                unfold deq_not_inc in *; simpl in *.
                clear Hpid1.
                intuition.
                left.
                intuition.
                apply binds_push_inv in H10; auto.
                intuition.
                discriminate.
      (* inv_2 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [Hinv_e28 [_ [_ [_ [Hinv2 [_ [Hinv3 _]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_2.
        simpl.
        unfold R; simpl in *.
        unfold get_pc, get_rear, get_ary; simpl in *.
        inversion H2; subst; simpl in *.
        (* front_rear *)
        + inversion H3; subst; simpl in *.
          inversion H4; subst; simpl in *.
          (* rear *)
          ++ inversion H5; subst; simpl in *.
            inversion H6; subst; simpl in *.
            (* INC *)
            +++ unfold inv_2 in Hinv2.
              unfold R in *; simpl in *.
              unfold get_pc, get_rear, get_ary in *; simpl in *.
              intuition.
              * apply reachable_len_to_reachable in HreachTmp.
                pose proof HreachTmp as HreachTmp2.
                apply inv_rear_inc_at_e31_invariant in HreachTmp.
                unfold inv_rear_inc_at_e31 in HreachTmp.
                simpl in HreachTmp.
                apply HreachTmp in Hbinds5; auto.
                apply binds_reconstruct in Hbinds5.
                destruct Hbinds5 as [l1 [l2 Hlist]].
                apply array_queue_wf_invarint in HreachTmp2.
                unfold array_queue_wf in HreachTmp2.
                simpl in HreachTmp2.
                rewrite Hlist in HreachTmp2.
                apply ok_remove_middle_inv in HreachTmp2.
                destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
                rewrite Hlist.
                repeat rewrite get_r'_dist; auto.
                simpl.
                rewrite Nat.eqb_refl.
                rewrite get_r'_any_rear_push; auto.
                rewrite get_r'_any_rear_push; auto.
                simpl.
                rewrite Hlist in H7.
                repeat rewrite get_r'_dist in H7; auto.
                simpl in H7.
                apply notin_get_none in Hnotin_res.
                rewrite Hnotin_res in H7.
                exfalso.
                lia.
              * apply reachable_len_to_reachable in HreachTmp.
                pose proof HreachTmp as HreachTmp2.
                apply inv_rear_inc_at_e31_invariant in HreachTmp.
                unfold inv_rear_inc_at_e31 in HreachTmp.
                simpl in HreachTmp.
                apply HreachTmp in Hbinds5; auto.
                apply binds_reconstruct in Hbinds5.
                destruct Hbinds5 as [l1 [l2 Hlist]].
                apply array_queue_wf_invarint in HreachTmp2.
                unfold array_queue_wf in HreachTmp2.
                simpl in HreachTmp2.
                rewrite Hlist in HreachTmp2.
                apply ok_remove_middle_inv in HreachTmp2.
                destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
                rewrite Hlist.
                repeat rewrite get_r'_dist; auto.
                simpl.
                rewrite Nat.eqb_refl.
                rewrite get_r'_any_rear_push; auto.
                rewrite get_r'_any_rear_push; auto.
                simpl.
                rewrite Hlist in H7.
                repeat rewrite get_r'_dist in H7; auto.
                simpl in H7.
                apply notin_get_none in Hnotin_res.
                rewrite Hnotin_res in H7.
                simpl in H7.
                rewrite Nat.add_succ_r in H7.
                rewrite Nat.add_succ_r in H7.
                assert (Htmp : forall m, (S m) - 1 = m)
                by lia.
                rewrite Htmp in H7.
                rewrite <-H7. intuition.
            (* READ *)
            +++ rewrite get_r'_any_rear_read; auto.
          ++ auto.
        (* array *)
        + inversion H3; subst; simpl in *.
          inversion H4; subst; simpl in *.
          (* cas *)
          ++ destruct (entry_eqb (Vector.nth vec (Fin.of_nat_lt Hlt)))eqn:Heq.
            (* success *)
            +++ unfold inv_2 in Hinv2.
              unfold R in Hinv2; simpl in *.
              unfold get_rear, get_pc, get_ary in Hinv2; simpl in *.
              intuition.
              * apply reachable_len_to_reachable in HreachTmp.
                pose proof HreachTmp as HreachTmp2.
                apply inv_ary_cas_at_e28_d28_invariant in HreachTmp.
                unfold inv_ary_cas_at_e28_d28 in HreachTmp.
                simpl in HreachTmp.
                apply HreachTmp in Hbinds3.
                intuition.
                (* e28 *)
                ** apply binds_reconstruct in H8.
                  apply array_queue_wf_invarint in HreachTmp2.
                  unfold array_queue_wf in HreachTmp2.
                  simpl in HreachTmp2.
                  destruct H8 as [l1 [l2 Hlist]].
                  rewrite Hlist in HreachTmp2.
                  apply ok_remove_middle_inv in HreachTmp2.
                  destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
                  rewrite Hlist.
                  repeat rewrite get_r'_dist; auto.
                  simpl.
                  apply notin_get_none in Hnotin_res.
                  rewrite Hnotin_res.
                  rewrite Nat.eqb_refl.
                  simpl.
                  assert (Htmp : forall m, (S m) - 1 = m) by
                  lia.
                  rewrite get_r'_any_ary; auto.
                  rewrite get_r'_any_ary; auto.
                  right.
                  repeat rewrite Nat.add_succ_r.
                  rewrite Htmp.
                  
                  rewrite Hlist in H5.
                  repeat rewrite get_r'_dist in H5; auto.
                  simpl in H5.
                  rewrite Hnotin_res in H5.
                  simpl in H5. intuition.
                (* d28 *)
                ** apply binds_reconstruct in H8.
                  apply array_queue_wf_invarint in HreachTmp2.
                  unfold array_queue_wf in HreachTmp2.
                  simpl in HreachTmp2.
                  destruct H8 as [l1 [l2 Hlist]].
                  rewrite Hlist in HreachTmp2.
                  apply ok_remove_middle_inv in HreachTmp2.
                  destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
                  rewrite Hlist.
                  repeat rewrite get_r'_dist; auto.
                  simpl.
                  apply notin_get_none in Hnotin_res.
                  simpl.
                  rewrite get_r'_any_ary; auto.
                  rewrite get_r'_any_ary; auto.
                  left.
                  rewrite Hlist in H5.
                  repeat rewrite get_r'_dist in H5; auto.
              * apply reachable_len_to_reachable in HreachTmp.
                pose proof HreachTmp as HreachTmp2.
                apply inv_ary_cas_at_e28_d28_invariant in HreachTmp.
                unfold inv_ary_cas_at_e28_d28 in HreachTmp.
                simpl in HreachTmp.
                pose proof Hbinds3 as Hbind3Tmp.
                apply HreachTmp in Hbinds3.
                intuition.
                (* e28 *)
                ** unfold inv_e28_clean in Hinv_e28.
                  simpl in Hinv_e28.
                  unfold R, F in *; simpl in *.
                  unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
                  apply entry_eqb_eq in Heq.
                  pose proof H8 as HbindsTmp.
                  apply Hinv_e28 in H8; auto.
                  destruct H8 as [H81 _].
                  rewrite <-H81 in H5.
                  apply inv_rear_invariant in H7; auto.
                  unfold inv_rear in H7.
                  simpl in H7.
                  destruct H7 as [H71 _].
                  specialize (H71 pid).

                  rewrite H81 in H5.

                  rename HbindsTmp into H8.
                  apply binds_reconstruct in H8.
                  destruct H8 as [l1 [l2 Hlist]].
                  apply array_queue_wf_invarint in HreachTmp2.
                  unfold array_queue_wf in HreachTmp2.
                  simpl in HreachTmp2.
                  rewrite Hlist in HreachTmp2.
                  apply ok_remove_middle_inv in HreachTmp2.
                  destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
                  rewrite Hlist in H5.
                  repeat rewrite get_r'_dist in H5; auto.
                  simpl in H5.
                  apply notin_get_none in Hnotin_res.
                  rewrite Hnotin_res in H5.
                  simpl in H5.

                  rewrite Hlist.
                  repeat rewrite get_r'_dist; auto.
                  simpl.
                  rewrite Nat.eqb_refl.
                  rewrite get_r'_any_ary; auto.
                  rewrite get_r'_any_ary; auto.
                  repeat rewrite Nat.add_succ_r; auto.
                  assert (Htmp : forall m, (S m) - 1 = m) by lia.
                  rewrite Htmp.

                  destruct ( value (LState (Tensor.L2State (LState st0))) +
     (get_r' l1 res
        (Counter.responses (LState (Tensor.L2State (LState st0)))) +
      get_r' l2 res
        (Counter.responses (LState (Tensor.L2State (LState st0))))))eqn:Heq'.
                  intuition.

                  rewrite Hlist in H81.
                  repeat rewrite get_r'_dist in H81; auto.
                  simpl in H81.
                  rewrite Hnotin_res in H81.
                  simpl in H81.
                  rewrite Heq' in H81.
                  rewrite H81 in H71.
                  rewrite H5 in H71. lia.
                  apply step_invariant in H7; auto.
                  unfold ComposedLTS.inv in H7.
                  simpl in H7.
                  apply H7 in Hbinds0.
                  destruct Hbinds0 as [s1 [s2 [q [acts [Hint_query [Hvalid Hgather]]]]]].
                  inversion Hint_query; subst; simpl in *.
                  inversion H9; subst; simpl in *.
                  unfold binds in H8.
                  inversion H11; subst; simpl in *.

                Ltac tmp'' H Hvalid st2 pid acts Hgather H8 :=
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
      (rewrite Hvalid in H8; discriminate).
  tmp'' noB_preserves_AEnq2 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_AEnq5 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_AEnq11 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_AEnq14 Hvalid st2 pid acts Hgather H8.

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
  inversion H10; subst; simpl in *.
  inversion H12; subst; simpl in *.
  inversion H14; subst; simpl in *.
  inversion H13; subst; simpl in *.
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
  rewrite <-Hx.
  rewrite H17.
  rewrite Htmp.
  rewrite Hrear.
  auto.

  tmp'' noB_preserves_AEnq31 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_ADeq2 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_ADeq5 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_ADeq11 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_ADeq14 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_ADeq28 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_ADeq31 Hvalid st2 pid acts Hgather H8.
                (* deq28 *)
                ** apply binds_reconstruct in H8.
                  destruct H8 as [l1 [l2 Hlist]].
                  apply array_queue_wf_invarint in HreachTmp2.
                  unfold array_queue_wf in HreachTmp2.
                  simpl in HreachTmp2.
                  rewrite Hlist in HreachTmp2.
                  apply ok_remove_middle_inv in HreachTmp2.
                  destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
                  rewrite Hlist in H5.
                  repeat rewrite get_r'_dist in H5; auto.
                  simpl in H5.
                  rewrite Hlist.
                  repeat rewrite get_r'_dist; auto.
                  simpl.
                  rewrite get_r'_any_ary; auto.
                  rewrite get_r'_any_ary; auto.
            (* fail *)
            +++ rewrite get_r'_any_ary_cas_false; auto.
          ++ rewrite get_r'_any_ary_read; auto.
      (* inv_2' *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [Hinv_e28 [_ [_ [_ [Hinv2 [_ [Hinv3 _]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_2'.
        simpl.
        unfold F, R; simpl in *.
        unfold get_front, get_pc, get_rear, get_ary; simpl in *.
        inversion H2; subst; simpl in *.
        (* front_rear *)
        + inversion H3; subst; simpl in *.
          inversion H4; subst; simpl in *.
          ++ auto.
          (* front *)
          ++ inversion H5; subst; simpl in *.
            inversion H6; subst; simpl in *.
            (* INC *)
            +++ unfold inv_2' in Hinv2.
              unfold F, R in *; simpl in *.
              unfold get_front, get_pc, get_rear, get_ary in *; simpl in *.
              intuition.
              * apply reachable_len_to_reachable in HreachTmp.
                pose proof HreachTmp as HreachTmp2.
                apply inv_front_inc_at_d31_invariant in HreachTmp.
                unfold inv_front_inc_at_d31 in HreachTmp.
                simpl in HreachTmp.
                apply HreachTmp in Hbinds5; auto.
                apply binds_reconstruct in Hbinds5.
                destruct Hbinds5 as [l1 [l2 Hlist]].
                apply array_queue_wf_invarint in HreachTmp2.
                unfold array_queue_wf in HreachTmp2.
                simpl in HreachTmp2.
                rewrite Hlist in HreachTmp2.
                apply ok_remove_middle_inv in HreachTmp2.
                destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
                rewrite Hlist.
                repeat rewrite get_f'_dist; auto.
                simpl.
                rewrite Nat.eqb_refl.
                rewrite get_f'_any_rear_push; auto.
                rewrite get_f'_any_rear_push; auto.
                simpl.
                rewrite Hlist in H7.
                repeat rewrite get_f'_dist in H7; auto.
                simpl in H7.
                apply notin_get_none in Hnotin_res.
                rewrite Hnotin_res in H7.
                exfalso.
                lia.
              * apply reachable_len_to_reachable in HreachTmp.
                pose proof HreachTmp as HreachTmp2.
                apply inv_front_inc_at_d31_invariant in HreachTmp.
                unfold inv_front_inc_at_d31 in HreachTmp.
                simpl in HreachTmp.
                apply HreachTmp in Hbinds5; auto.
                apply binds_reconstruct in Hbinds5.
                destruct Hbinds5 as [l1 [l2 Hlist]].
                apply array_queue_wf_invarint in HreachTmp2.
                unfold array_queue_wf in HreachTmp2.
                simpl in HreachTmp2.
                rewrite Hlist in HreachTmp2.
                apply ok_remove_middle_inv in HreachTmp2.
                destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
                rewrite Hlist.
                repeat rewrite get_f'_dist; auto.
                simpl.
                rewrite Nat.eqb_refl.
                rewrite get_f'_any_rear_push; auto.
                rewrite get_f'_any_rear_push; auto.
                simpl.
                rewrite Hlist in H7.
                repeat rewrite get_f'_dist in H7; auto.
                simpl in H7.
                apply notin_get_none in Hnotin_res.
                rewrite Hnotin_res in H7.
                simpl in H7.
                rewrite Nat.add_succ_r in H7.
                rewrite Nat.add_succ_r in H7.
                assert (Htmp : forall m, (S m) - 1 = m)
                by lia.
                rewrite Htmp in H7.
                rewrite <-H7. intuition.
            (* READ *)
            +++ rewrite get_f'_any_rear_read; auto.
        (* array *)
        + inversion H3; subst; simpl in *.
          inversion H4; subst; simpl in *.
          (* cas *)
          ++ destruct (entry_eqb (Vector.nth vec (Fin.of_nat_lt Hlt)))eqn:Heq.
            (* success *)
            +++ unfold inv_2' in Hinv2.
              unfold F, R in Hinv2; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in Hinv2; simpl in *.
              intuition.
              * apply reachable_len_to_reachable in HreachTmp.
                pose proof HreachTmp as HreachTmp2.
                apply inv_ary_cas_at_e28_d28_invariant in HreachTmp.
                unfold inv_ary_cas_at_e28_d28 in HreachTmp.
                simpl in HreachTmp.
                apply HreachTmp in Hbinds3.
                intuition.
                (* e28 *)
                ** apply binds_reconstruct in H8.
                  apply array_queue_wf_invarint in HreachTmp2.
                  unfold array_queue_wf in HreachTmp2.
                  simpl in HreachTmp2.
                  destruct H8 as [l1 [l2 Hlist]].
                  rewrite Hlist in HreachTmp2.
                  apply ok_remove_middle_inv in HreachTmp2.
                  destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
                  rewrite Hlist.
                  repeat rewrite get_f'_dist; auto.
                  simpl.
                  apply notin_get_none in Hnotin_res.
                  simpl.
                  rewrite get_f'_any_ary; auto.
                  rewrite get_f'_any_ary; auto.
                  left.
                  rewrite Hlist in H5.
                  repeat rewrite get_f'_dist in H5; auto.
                (* d28 *)
                ** apply binds_reconstruct in H8.
                  apply array_queue_wf_invarint in HreachTmp2.
                  unfold array_queue_wf in HreachTmp2.
                  simpl in HreachTmp2.
                  destruct H8 as [l1 [l2 Hlist]].
                  rewrite Hlist in HreachTmp2.
                  apply ok_remove_middle_inv in HreachTmp2.
                  destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
                  rewrite Hlist.
                  repeat rewrite get_f'_dist; auto.
                  simpl.
                  apply notin_get_none in Hnotin_res.
                  rewrite Hnotin_res.
                  rewrite Nat.eqb_refl.
                  simpl.
                  assert (Htmp : forall m, (S m) - 1 = m) by
                  lia.
                  rewrite get_f'_any_ary; auto.
                  rewrite get_f'_any_ary; auto.
                  right.
                  repeat rewrite Nat.add_succ_r.
                  rewrite Htmp.
                  
                  rewrite Hlist in H5.
                  repeat rewrite get_f'_dist in H5; auto.
                  simpl in H5.
                  rewrite Hnotin_res in H5.
                  simpl in H5. intuition.
              * apply reachable_len_to_reachable in HreachTmp.
                pose proof HreachTmp as HreachTmp2.
                apply inv_ary_cas_at_e28_d28_invariant in HreachTmp.
                unfold inv_ary_cas_at_e28_d28 in HreachTmp.
                simpl in HreachTmp.
                pose proof Hbinds3 as Hbind3Tmp.
                apply HreachTmp in Hbinds3.
                intuition.
                (* e28 *)
                ** apply binds_reconstruct in H8.
                  destruct H8 as [l1 [l2 Hlist]].
                  apply array_queue_wf_invarint in HreachTmp2.
                  unfold array_queue_wf in HreachTmp2.
                  simpl in HreachTmp2.
                  rewrite Hlist in HreachTmp2.
                  apply ok_remove_middle_inv in HreachTmp2.
                  destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
                  rewrite Hlist in H5.
                  repeat rewrite get_f'_dist in H5; auto.
                  simpl in H5.
                  rewrite Hlist.
                  repeat rewrite get_f'_dist; auto.
                  simpl.
                  rewrite get_f'_any_ary; auto.
                  rewrite get_f'_any_ary; auto.
                (* d28 *)
                ** unfold inv_d28_clean in Hinv_e28.
                  simpl in Hinv_e28.
                  unfold R, F in *; simpl in *.
                  unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
                  apply entry_eqb_eq in Heq.
                  pose proof H8 as HbindsTmp.
                  apply Hinv_e28 in H8; auto.
                  destruct H8 as [H81 _].
                  rewrite <-H81 in H5.
                  apply inv_front_invariant in H7; auto.
                  unfold inv_front in H7.
                  simpl in H7.
                  destruct H7 as [H71 _].
                  specialize (H71 pid).

                  rewrite H81 in H5.

                  rename HbindsTmp into H8.
                  apply binds_reconstruct in H8.
                  destruct H8 as [l1 [l2 Hlist]].
                  apply array_queue_wf_invarint in HreachTmp2.
                  unfold array_queue_wf in HreachTmp2.
                  simpl in HreachTmp2.
                  rewrite Hlist in HreachTmp2.
                  apply ok_remove_middle_inv in HreachTmp2.
                  destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
                  rewrite Hlist in H5.
                  repeat rewrite get_f'_dist in H5; auto.
                  simpl in H5.
                  apply notin_get_none in Hnotin_res.
                  rewrite Hnotin_res in H5.
                  simpl in H5.

                  rewrite Hlist.
                  repeat rewrite get_f'_dist; auto.
                  simpl.
                  rewrite Nat.eqb_refl.
                  rewrite get_f'_any_ary; auto.
                  rewrite get_f'_any_ary; auto.
                  repeat rewrite Nat.add_succ_r; auto.
                  assert (Htmp : forall m, (S m) - 1 = m) by lia.
                  rewrite Htmp.

                  destruct ( value (LState (Tensor.L1State (LState st0))) +
     (get_f' l1 res
        (Counter.responses (LState (Tensor.L1State (LState st0)))) +
      get_f' l2 res
        (Counter.responses (LState (Tensor.L1State (LState st0))))))eqn:Heq'.
                  intuition.

                  rewrite Hlist in H81.
                  repeat rewrite get_f'_dist in H81; auto.
                  simpl in H81.
                  rewrite Hnotin_res in H81.
                  simpl in H81.
                  rewrite Heq' in H81.
                  rewrite H81 in H71.
                  rewrite H5 in H71. lia.
                  apply step_invariant in H7; auto.
                  unfold ComposedLTS.inv in H7.
                  simpl in H7.
                  apply H7 in Hbinds0.
                  destruct Hbinds0 as [s1 [s2 [q [acts [Hint_query [Hvalid Hgather]]]]]].
                  inversion Hint_query; subst; simpl in *.
                  inversion H9; subst; simpl in *.
                  unfold binds in H8.
                  inversion H11; subst; simpl in *.

                (* Ltac tmp'' H Hvalid st2 pid acts Hgather H8 :=
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
      (rewrite Hvalid in H8; discriminate). *)
  tmp'' noB_preserves_AEnq2 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_AEnq5 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_AEnq11 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_AEnq14 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_AEnq28 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_AEnq31 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_ADeq2 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_ADeq5 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_ADeq11 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_ADeq14 Hvalid st2 pid acts Hgather H8.

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
  inversion H10; subst; simpl in *.
  inversion H12; subst; simpl in *.
  inversion H14; subst; simpl in *.
  inversion H13; subst; simpl in *.
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
  rewrite <-Hx.
  rewrite H17.
  rewrite Htmp.
  rewrite Hrear.
  auto.

  tmp'' noB_preserves_ADeq31 Hvalid st2 pid acts Hgather H8.
            (* fail *)
            +++ rewrite get_f'_any_ary_cas_false; auto.
          ++ rewrite get_f'_any_ary_read; auto.
      (* inv_3 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; auto; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [Hinv_e28 [_ [Hinv_1 [_ [_ [_ [Hinv_3 _]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_3. simpl in *.
        intros pid0 Hpid0.
        unfold R in *; simpl in *.
        unfold get_rear, get_pc, get_ary in *; simpl in *.
        inversion H2; subst; simpl in *.
        (* front_rear *)
        + inversion H3; subst; simpl in *.
          inversion H4; subst; simpl in *.
          (* rear *)
          ++ inversion H5; subst; simpl in *.
            inversion H6; subst; simpl in *.
            (* INC *)
            +++ unfold inv_3 in Hinv_3.
              unfold inv_1 in Hinv_1.
              unfold R, F in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              specialize (Hinv_3 pid0).
              apply reachable_len_to_reachable in HreachTmp.
              pose proof HreachTmp as HreachTmp2.
              apply inv_rear_inc_at_e31_invariant in HreachTmp.
              unfold inv_rear_inc_at_e31 in HreachTmp.
              simpl in HreachTmp.
              apply HreachTmp in Hbinds5; auto.
              pose proof Hbinds5 as HbindsTmp.
              apply binds_reconstruct in Hbinds5.
              destruct Hbinds5 as [l1 [l2 Hlist]].
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              rewrite Hlist in Hinv_3.
              repeat rewrite get_r'_dist in Hinv_3; auto.
              simpl in Hinv_3.
              pose proof Hnotin_res as Hnotin_res'.
              apply notin_get_none in Hnotin_res.
              rewrite Hnotin_res in Hinv_3.
              repeat rewrite Nat.add_succ_r in Hinv_3.
              assert (Htmp : forall m, (S m) - 1 = m) by lia.
              rewrite Htmp in Hinv_3.

              destruct (eq_nat_dec pid pid0).
              * subst.
                unfold enq_not_inc in Hpid0.
                unfold binds in Hpid0.
                rewrite HbindsTmp in Hpid0.
                intuition; try discriminate.
                simpl in H11.
                apply notin_union in H11.
                intuition.
                apply notin_neq in H9; intuition.
              *
              rewrite Hlist in Hinv_1.
              repeat rewrite get_r'_dist in Hinv_1; auto.
              simpl in Hinv_1.
              rewrite Hnotin_res in Hinv_1.
              repeat rewrite Nat.add_succ_r in Hinv_1.
              rewrite Htmp in Hinv_1.
              simpl in Hlist.
              rewrite <-Hlist in Hinv_1.
              rewrite <-Hlist in Hinv_3.
              apply Hinv_1 in Hinv_3; auto; try lia.
              destruct Hinv_3 as [pid' [Hpid1 Hpid2]].
              destruct (eq_nat_dec pid0 pid').
              ** subst.
                apply Hpid2 in n0; auto.
                exfalso.
                apply n0; auto.
                unfold enq_not_inc.
                right. right. right.
                intuition.
              ** apply Hpid2 in n1; auto.
                exfalso.
                apply n1.
                clear Hpid1.
                unfold enq_not_inc in *; simpl in *.
                intuition.
                right. right. right.
                apply notin_union in H11; auto.
                intuition.
              ** unfold enq_not_inc in *; simpl in *.
                intuition.
                right. right. right.
                apply notin_union in H11; auto.
                intuition.
          (* READ *)
          +++ unfold inv_3 in Hinv_3.
            simpl in Hinv_3.
            unfold R in *; simpl in *.
            unfold get_rear, get_pc, get_ary in *; simpl in *.
            rewrite get_r'_any_rear_read; auto.
            rewrite <-Hinv_3 with (pid:=pid0); auto.
            unfold enq_not_inc in *; simpl in *.
            intuition.
            apply notin_union in H9; auto.
            intuition.
        (* FRONT *)
        ++ unfold inv_3 in Hinv_3.
            simpl in Hinv_3.
            unfold R in *; simpl in *.
            unfold get_rear, get_pc, get_ary in *; simpl in *.
            rewrite <-Hinv_3 with (pid:=pid0); auto.
      (* array *)
      + inversion H3; subst; simpl in *.
        inversion H4; subst; simpl in *.
        (* CAS *)
        ++ destruct ((entry_eqb (Vector.nth vec (Fin.of_nat_lt Hlt)) old))eqn:Heq.
          (* success *)
          +++ apply entry_eqb_eq in Heq.
            apply reachable_len_to_reachable in HreachTmp.
            pose proof HreachTmp as HreachTmp2.
            apply inv_ary_cas_at_e28_d28_invariant in HreachTmp.
            unfold inv_ary_cas_at_e28_d28 in HreachTmp.
            simpl in HreachTmp.
            pose proof Hbinds3 as HbindsTmp'.
            apply HreachTmp in Hbinds3; auto.
            intuition.
            (* e28 *)
            * unfold inv_e28_clean in Hinv_e28.
              unfold inv_3 in Hinv_3.
              simpl in Hinv_e28.
              pose proof H7 as HbindsTmp.
              apply Hinv_e28 in H7; auto.
              unfold F, R in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              apply binds_reconstruct in HbindsTmp.
              destruct HbindsTmp as [l1 [l2 Hlist]].
              pose proof HreachTmp2 as HreachTmp3.
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              rewrite Hlist.
              repeat rewrite get_r'_dist; auto.
              simpl.
              rewrite Nat.eqb_refl.
              repeat rewrite Nat.add_succ_r; auto.
              assert (Htmp : forall m, (S m) - 1 = m) by lia.
              rewrite Htmp.
              rewrite get_r'_any_ary; auto.
              rewrite get_r'_any_ary; auto.
              destruct H7 as [H71 _].
              rewrite Hlist in H71.
              repeat rewrite get_r'_dist in H71; auto.
              simpl in H71.
              apply notin_get_none in Hnotin_res.
              rewrite Hnotin_res in H71.
              simpl in H71.
              rewrite <-H71.
              apply inv_rear_invariant in HreachTmp3; auto.
              unfold inv_rear in HreachTmp3.
              simpl in HreachTmp3.
              destruct HreachTmp3 as [H31 _].
              specialize (H31 pid).
              lia.

                  apply step_invariant in HreachTmp2; auto.
                  unfold ComposedLTS.inv in HreachTmp2.
                  simpl in HreachTmp2.
                  apply HreachTmp2 in Hbinds0.
                  destruct Hbinds0 as [s1 [s2 [q [acts [Hint_query [Hvalid Hgather]]]]]].
                  inversion Hint_query; subst; simpl in *.
                  rename H9 into H10.
                  rename H8 into H9.
                  rename H7 into H8.
                  inversion H9; subst; simpl in *.
                  unfold binds in H8.
                  inversion H7; subst; simpl in *.

                (* Ltac tmp'' H Hvalid st2 pid acts Hgather H8 :=
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
      (rewrite Hvalid in H8; discriminate). *)
  tmp'' noB_preserves_AEnq2 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_AEnq5 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_AEnq11 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_AEnq14 Hvalid st2 pid acts Hgather H8.

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
  inversion H10; subst; simpl in *.
  inversion H11; subst; simpl in *.
  inversion H13; subst; simpl in *.
  inversion H12; subst; simpl in *.
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
  rewrite <-Hx.
  rewrite H16.
  rewrite Htmp.
  rewrite Hrear.
  auto.

  tmp'' noB_preserves_AEnq31 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_ADeq2 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_ADeq5 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_ADeq11 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_ADeq14 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_ADeq28 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_ADeq31 Hvalid st2 pid acts Hgather H8.
            (* deq28 *)
            *
              pose proof H7 as HbindsTmp.
              unfold inv_3 in Hinv_3.
              unfold F, R in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *. 
             (* unfold inv_e28_clean in Hinv_e28.
              simpl in Hinv_e28.
              apply Hinv_e28 in H7; auto.*)
              apply binds_reconstruct in HbindsTmp.
              destruct HbindsTmp as [l1 [l2 Hlist]].
              pose proof HreachTmp2 as HreachTmp3.
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              rewrite Hlist.
              repeat rewrite get_r'_dist; auto.
              simpl.
              rewrite get_r'_any_ary; auto.
              rewrite get_r'_any_ary; auto.
              specialize (Hinv_3 pid0).

              rewrite Hlist in Hinv_3.
              repeat rewrite get_r'_dist in Hinv_3; auto.
              simpl in Hinv_3.
              simpl in Hlist.
              rewrite <-Hlist in Hinv_3.
              rewrite <-Hinv_3; auto.
              unfold enq_not_inc in *; simpl in *.
              intuition.
              unfold binds in H7.
              apply binds_push_inv in H10; auto.
              intuition. subst.
              rewrite H9 in H7; discriminate.
          (* fail *)
          +++ rewrite get_r'_any_ary_cas_false; auto.
              unfold inv_3 in Hinv_3.
              unfold F, R in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              rewrite <-Hinv_3 with (pid:=pid0); auto.
              unfold enq_not_inc in *; simpl in *.
              intuition.
              apply binds_push_inv in H7; auto.
              intuition.
              discriminate.
        (* READ *)
        ++ rewrite get_r'_any_ary_read; auto.
              unfold inv_3 in Hinv_3.
              unfold F, R in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              rewrite <-Hinv_3 with (pid:=pid0); auto.
              unfold enq_not_inc in *; simpl in *.
              intuition.
              apply binds_push_inv in H7; auto.
              intuition.
              discriminate.
      (* inv_3' *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; auto; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [Hinv_e28 [_ [Hinv_1 [_ [_ [_ [Hinv_3 _]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_3'. simpl in *.
        intros pid0 Hpid0.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
        inversion H2; subst; simpl in *.
        (* front_rear *)
        + inversion H3; subst; simpl in *.
          inversion H4; subst; simpl in *.

          (* rear *)
          ++ unfold inv_3' in Hinv_3.
            simpl in Hinv_3.
            unfold F, R in *; simpl in *.
            unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
            rewrite <-Hinv_3 with (pid:=pid0); auto.
          (* front *)
          ++ inversion H5; subst; simpl in *.
            inversion H6; subst; simpl in *.
            (* INC *)
            +++ unfold inv_3' in Hinv_3.
              unfold inv_1' in Hinv_1.
              unfold R, F in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              specialize (Hinv_3 pid0).
              apply reachable_len_to_reachable in HreachTmp.
              pose proof HreachTmp as HreachTmp2.
              apply inv_front_inc_at_d31_invariant in HreachTmp.
              unfold inv_front_inc_at_d31 in HreachTmp.
              simpl in HreachTmp.
              apply HreachTmp in Hbinds5; auto.
              pose proof Hbinds5 as HbindsTmp.
              apply binds_reconstruct in Hbinds5.
              destruct Hbinds5 as [l1 [l2 Hlist]].
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              rewrite Hlist in Hinv_3.
              repeat rewrite get_f'_dist in Hinv_3; auto.
              simpl in Hinv_3.
              pose proof Hnotin_res as Hnotin_res'.
              apply notin_get_none in Hnotin_res.
              rewrite Hnotin_res in Hinv_3.
              repeat rewrite Nat.add_succ_r in Hinv_3.
              assert (Htmp : forall m, (S m) - 1 = m) by lia.
              rewrite Htmp in Hinv_3.

              destruct (eq_nat_dec pid pid0).
              * subst.
                unfold deq_not_inc in Hpid0.
                unfold binds in Hpid0.
                rewrite HbindsTmp in Hpid0.
                intuition; try discriminate.
                simpl in H11.
                apply notin_union in H11.
                intuition.
                apply notin_neq in H9; intuition.
              *
              rewrite Hlist in Hinv_1.
              repeat rewrite get_f'_dist in Hinv_1; auto.
              simpl in Hinv_1.
              rewrite Hnotin_res in Hinv_1.
              repeat rewrite Nat.add_succ_r in Hinv_1.
              rewrite Htmp in Hinv_1.
              simpl in Hlist.
              rewrite <-Hlist in Hinv_1.
              rewrite <-Hlist in Hinv_3.
              apply Hinv_1 in Hinv_3; auto; try lia.
              destruct Hinv_3 as [pid' [Hpid1 Hpid2]].
              destruct (eq_nat_dec pid0 pid').
              ** subst.
                apply Hpid2 in n0; auto.
                exfalso.
                apply n0; auto.
                unfold enq_not_inc.
                right. right. right.
                intuition.
              ** apply Hpid2 in n1; auto.
                exfalso.
                apply n1.
                clear Hpid1.
                unfold deq_not_inc in *; simpl in *.
                intuition.
                right. right. right.
                apply notin_union in H11; auto.
                intuition.
              ** unfold deq_not_inc in *; simpl in *.
                intuition.
                right. right. right.
                apply notin_union in H11; auto.
                intuition.
          (* READ *)
          +++ unfold inv_3' in Hinv_3.
            simpl in Hinv_3.
            unfold F, R in *; simpl in *.
            unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
            rewrite get_f'_any_rear_read; auto.
            rewrite <-Hinv_3 with (pid:=pid0); auto.
            unfold deq_not_inc in *; simpl in *.
            intuition.
            apply notin_union in H9; auto.
            intuition.
      (* array *)
      + inversion H3; subst; simpl in *.
        inversion H4; subst; simpl in *.
        (* CAS *)
        ++ destruct ((entry_eqb (Vector.nth vec (Fin.of_nat_lt Hlt)) old))eqn:Heq.
          (* success *)
          +++ apply entry_eqb_eq in Heq.
            apply reachable_len_to_reachable in HreachTmp.
            pose proof HreachTmp as HreachTmp2.
            apply inv_ary_cas_at_e28_d28_invariant in HreachTmp.
            unfold inv_ary_cas_at_e28_d28 in HreachTmp.
            simpl in HreachTmp.
            pose proof Hbinds3 as HbindsTmp'.
            apply HreachTmp in Hbinds3; auto.
            intuition.

            (* enq28 *)
            *
              pose proof H7 as HbindsTmp.
              unfold inv_3' in Hinv_3.
              unfold F, R in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *. 
             (* unfold inv_e28_clean in Hinv_e28.
              simpl in Hinv_e28.
              apply Hinv_e28 in H7; auto.*)
              apply binds_reconstruct in HbindsTmp.
              destruct HbindsTmp as [l1 [l2 Hlist]].
              pose proof HreachTmp2 as HreachTmp3.
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              rewrite Hlist.
              repeat rewrite get_f'_dist; auto.
              simpl.
              rewrite get_f'_any_ary; auto.
              rewrite get_f'_any_ary; auto.
              specialize (Hinv_3 pid0).

              rewrite Hlist in Hinv_3.
              repeat rewrite get_f'_dist in Hinv_3; auto.
              simpl in Hinv_3.
              simpl in Hlist.
              rewrite <-Hlist in Hinv_3.
              rewrite <-Hinv_3; auto.
              unfold deq_not_inc in *; simpl in *.
              intuition.
              unfold binds in H7.
              apply binds_push_inv in H10; auto.
              intuition. subst.
              rewrite H9 in H7; discriminate.

            (* d28 *)
            * unfold inv_d28_clean in Hinv_e28.
              unfold inv_3' in Hinv_3.
              simpl in Hinv_e28.
              pose proof H7 as HbindsTmp.
              apply Hinv_e28 in H7; auto.
              unfold F, R in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              apply binds_reconstruct in HbindsTmp.
              destruct HbindsTmp as [l1 [l2 Hlist]].
              pose proof HreachTmp2 as HreachTmp3.
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              rewrite Hlist.
              repeat rewrite get_f'_dist; auto.
              simpl.
              rewrite Nat.eqb_refl.
              repeat rewrite Nat.add_succ_r; auto.
              assert (Htmp : forall m, (S m) - 1 = m) by lia.
              rewrite Htmp.
              rewrite get_f'_any_ary; auto.
              rewrite get_f'_any_ary; auto.
              destruct H7 as [H71 _].
              rewrite Hlist in H71.
              repeat rewrite get_f'_dist in H71; auto.
              simpl in H71.
              apply notin_get_none in Hnotin_res.
              rewrite Hnotin_res in H71.
              simpl in H71.
              rewrite <-H71.
              apply inv_front_invariant in HreachTmp3; auto.
              unfold inv_front in HreachTmp3.
              simpl in HreachTmp3.
              destruct HreachTmp3 as [H31 _].
              specialize (H31 pid).
              lia.

                  apply step_invariant in HreachTmp2; auto.
                  unfold ComposedLTS.inv in HreachTmp2.
                  simpl in HreachTmp2.
                  apply HreachTmp2 in Hbinds0.
                  destruct Hbinds0 as [s1 [s2 [q [acts [Hint_query [Hvalid Hgather]]]]]].
                  inversion Hint_query; subst; simpl in *.
                  rename H9 into H10.
                  rename H8 into H9.
                  rename H7 into H8.
                  inversion H9; subst; simpl in *.
                  unfold binds in H8.
                  inversion H7; subst; simpl in *.

                (* Ltac tmp'' H Hvalid st2 pid acts Hgather H8 :=
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
      (rewrite Hvalid in H8; discriminate). *)
  tmp'' noB_preserves_AEnq2 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_AEnq5 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_AEnq11 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_AEnq14 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_AEnq28 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_AEnq31 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_ADeq2 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_ADeq5 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_ADeq11 Hvalid st2 pid acts Hgather H8.
  tmp'' noB_preserves_ADeq14 Hvalid st2 pid acts Hgather H8.

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
  inversion H10; subst; simpl in *.
  inversion H11; subst; simpl in *.
  inversion H13; subst; simpl in *.
  inversion H12; subst; simpl in *.
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
  rewrite <-Hx.
  rewrite H16.
  rewrite Htmp.
  rewrite Hrear.
  auto.

  tmp'' noB_preserves_ADeq31 Hvalid st2 pid acts Hgather H8.
          (* fail *)
          +++ rewrite get_f'_any_ary_cas_false; auto.
              unfold inv_3' in Hinv_3.
              unfold F, R in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              rewrite <-Hinv_3 with (pid:=pid0); auto.
              unfold deq_not_inc in *; simpl in *.
              intuition.
              apply binds_push_inv in H7; auto.
              intuition.
              discriminate.
        (* READ *)
        ++ rewrite get_f'_any_ary_read; auto.
              unfold inv_3' in Hinv_3.
              unfold F, R in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              rewrite <-Hinv_3 with (pid:=pid0); auto.
              unfold deq_not_inc in *; simpl in *.
              intuition.
              apply binds_push_inv in H7; auto.
              intuition.
              discriminate.
    (* inv_4 *)
    --- pose proof Hreach as HreachTmp.
      apply IHk in Hreach; try lia.
      unfold inv_total in Hreach.
      destruct Hreach as [Hinv_e28 [_ [Hinv_1 [_ [Hinv_2 [_ [_ [_ [Hinv_4 _]]]]]]]]].
      inversion H1; subst; simpl in *.
      inversion H0; subst; simpl in *.
      unfold inv_4.
      simpl.
      unfold R in *; simpl in *.
      unfold get_rear, get_ary, get_pc in *; simpl in *.
      intros.
      inversion H2; subst; simpl in *.
      (* front_rear *)
      + inversion H4; subst; simpl in *.
        inversion H5; subst; simpl in *.
        (* rear *)
        ++ inversion H6; subst; simpl in *.
          inversion H7; subst; simpl in *.
          (* INC *)
          +++ unfold inv_2 in Hinv_2.
            simpl in Hinv_2.
            unfold R, F in *; simpl in *.
            unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
            intuition.
            * apply reachable_len_to_reachable in HreachTmp.
              pose proof HreachTmp as HreachTmp2.
              apply inv_rear_inc_at_e31_invariant in HreachTmp.
              unfold inv_rear_inc_at_e31 in HreachTmp.
              simpl in HreachTmp.
              apply HreachTmp in Hbinds5; auto.
              apply binds_reconstruct in Hbinds5.
              destruct Hbinds5 as [l1 [l2 Hlist]].
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              rewrite Hlist in H9.
              repeat rewrite get_r'_dist in H9; auto.
              simpl in H9.
              apply notin_get_none in Hnotin_res.
              rewrite Hnotin_res in H9.
              repeat rewrite Nat.add_succ_r in H9; auto.
              rewrite Hlist in H3.
              repeat rewrite get_r'_dist in H3; auto.
              simpl in H3.
              rewrite Hnotin_res in H3.
              repeat rewrite Nat.add_succ_r in H3; auto.
              rewrite Nat.eqb_refl in H3.
              rewrite get_r'_any_rear_push in H3; auto.
              rewrite get_r'_any_rear_push in H3; auto.
              simpl in H3.
              rewrite <-H9 in H3.
              lia.
            * destruct (eq_nat_dec pid pid0).
              ** subst.
                unfold enq_not_inc in H8.
                apply reachable_len_to_reachable in HreachTmp.
                apply inv_rear_inc_at_e31_invariant in HreachTmp.
                unfold inv_rear_inc_at_e31 in HreachTmp.
                simpl in HreachTmp.
                apply HreachTmp in Hbinds5.
                unfold binds in H8.
                rewrite Hbinds5 in H8.
                simpl in H8.
                intuition; try discriminate.
                apply notin_union in H13.
                destruct H13.
                apply notin_neq in H12; intuition.
              ** apply Hinv_1 in H9; auto.
                simpl in H9.
                destruct H9 as [pid' [Hpid1 Hpid2]].
                destruct (eq_nat_dec pid0 pid').
                *** subst.
                  apply Hpid2 in n0; auto.
                  apply n0.
                  apply reachable_len_to_reachable in HreachTmp.
                  apply inv_rear_inc_at_e31_invariant in HreachTmp.
                  unfold inv_rear_inc_at_e31 in HreachTmp.
                  simpl in HreachTmp.
                  apply HreachTmp in Hbinds5.
                  unfold enq_not_inc. intuition.
                *** apply Hpid2 in n1; auto.
                  apply n1.
                  unfold enq_not_inc in H8; simpl in *.
                  unfold enq_not_inc; simpl in *.
                  intuition.
                  apply notin_union in H10.
                  intuition.
                *** unfold R; simpl.
                  unfold get_ary, get_rear, get_pc; simpl.

                  apply reachable_len_to_reachable in HreachTmp.
                  apply inv_rear_inc_at_e31_invariant in HreachTmp.
                  unfold inv_rear_inc_at_e31 in HreachTmp.
                  simpl in HreachTmp.
                  apply HreachTmp in Hbinds5.
                  apply binds_reconstruct in Hbinds5.
                  destruct Hbinds5 as [l1 [l2 Hlist]].
                  rewrite Hlist.
                  repeat rewrite get_r'_dist; auto.
                  simpl.
                  apply notin_get_none in Hnotin_res.
                  rewrite Hnotin_res.
                  lia.
          (* READ *)
          +++ intro.
            unfold inv_4 in Hinv_4.
            simpl in Hinv_4.
            unfold R in *; simpl in *.
            unfold get_rear, get_pc, get_ary in *; simpl in *.
            rewrite get_r'_any_rear_read in H3; auto.
            intuition.
            apply H9 with (pid:=pid0); auto.
            clear H9.
            unfold enq_not_inc in *; simpl in *.
            intuition.
            apply notin_union in H10.
            intuition.
        (* front *)
        ++ intro.
            unfold inv_4 in Hinv_4.
            simpl in Hinv_4.
            unfold R in *; simpl in *.
            unfold get_rear, get_pc, get_ary in *; simpl in *.
            intuition.
            apply H8 with (pid:=pid0); auto.
      (* array *)
      + intro.
            unfold inv_4 in Hinv_4.
            simpl in Hinv_4.
            unfold R in *; simpl in *.
            unfold get_rear, get_pc, get_ary in *; simpl in *.
            inversion H4; subst; simpl in *.
            inversion H6; subst; simpl in *.
            (* CAS *)
            ++ destruct (entry_eqb (Vector.nth vec (Fin.of_nat_lt Hlt)))eqn:Heq.
              (* success *)
              +++ apply reachable_len_to_reachable in HreachTmp.
                pose proof HreachTmp as HreachTmp2.
                apply inv_ary_cas_at_e28_d28_invariant in HreachTmp.
                unfold inv_ary_cas_at_e28_d28 in HreachTmp.
                simpl in HreachTmp.
                apply HreachTmp in Hbinds3; auto.
                intuition.
                (* e28 *)
                * unfold inv_2 in Hinv_2.
                  simpl in Hinv_2.
                  unfold R in *; simpl in *.
                  unfold get_rear, get_pc, get_ary in *; simpl in *.
                  intuition.
                  ** apply binds_reconstruct in H9.
                    destruct H9 as [l1 [l2 Hlist]].
                    apply array_queue_wf_invarint in HreachTmp2.
                    unfold array_queue_wf in HreachTmp2.
                    simpl in HreachTmp2.
                    rewrite Hlist in HreachTmp2.
                    apply ok_remove_middle_inv in HreachTmp2.
                    destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
                    rewrite Hlist in H10; auto.
                    repeat rewrite get_r'_dist in H10; auto.
                    simpl in H10.
                    apply notin_get_none in Hnotin_res.
                    rewrite Hnotin_res in H10.
                    simpl in H10.

                    rewrite Hlist in H3; auto.
                    repeat rewrite get_r'_dist in H3; auto.
                    simpl in H3.
                    rewrite Hnotin_res in H3.
                    rewrite Nat.eqb_refl in H3.
                    simpl in H3.
                    repeat rewrite Nat.add_succ_r in H3.
                    rewrite get_r'_any_ary in H3; auto.
                    rewrite get_r'_any_ary in H3; auto.
                    rewrite <-H10 in H3. lia.
                  ** apply binds_reconstruct in H9.
                    destruct H9 as [l1 [l2 Hlist]].
                    apply array_queue_wf_invarint in HreachTmp2.
                    unfold array_queue_wf in HreachTmp2.
                    simpl in HreachTmp2.
                    rewrite Hlist in HreachTmp2.
                    apply ok_remove_middle_inv in HreachTmp2.
                    destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
                    rewrite Hlist in H10; auto.
                    repeat rewrite get_r'_dist in H10; auto.
                    simpl in H10.
                    apply notin_get_none in Hnotin_res.
                    rewrite Hnotin_res in H10.
                    simpl in H10.

                    rewrite Hlist in H3; auto.
                    repeat rewrite get_r'_dist in H3; auto.
                    simpl in H3.
                    rewrite Hnotin_res in H3.
                    rewrite Nat.eqb_refl in H3.
                    simpl in H3.
                    repeat rewrite Nat.add_succ_r in H3.
                    rewrite get_r'_any_ary in H3; auto.
                    rewrite get_r'_any_ary in H3; auto.
                    assert (Htmp : forall m n, n = m - 1 -> (S n) = m) by lia.
                    apply Htmp in H10.
                    rewrite <-H10 in H3. lia.
                (* d18 *)
                * unfold inv_4 in Hinv_4.
                  pose proof H9 as HbindsTmp.
                  apply binds_reconstruct in H9.
                  destruct H9 as [l1 [l2 Hlist]].
                  apply array_queue_wf_invarint in HreachTmp2.
                  unfold array_queue_wf in HreachTmp2.
                  simpl in HreachTmp2.
                  rewrite Hlist in HreachTmp2.
                  apply ok_remove_middle_inv in HreachTmp2.
                  destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
                  rewrite Hlist in H3.
                  repeat rewrite get_r'_dist in H3; auto.
                  simpl in H3.
                  rewrite get_r'_any_ary in H3; auto.
                  rewrite get_r'_any_ary in H3; auto.

                  rewrite Hlist in Hinv_4.
                  repeat rewrite get_r'_dist in Hinv_4; auto.
                  simpl in Hinv_4.
                  intuition.
                  apply H9 with (pid:=pid0); auto.
                  simpl in Hlist.
                  rewrite <-Hlist.
                  unfold enq_not_inc in *; simpl in *.
                  intuition.
                  apply binds_push_inv in H11; auto.
                  intuition.
                  subst.
                  unfold binds in HbindsTmp.
                  rewrite H5 in HbindsTmp; discriminate.
              (* fail *)
              +++ rewrite get_r'_any_ary_cas_false in H3; auto.
                unfold inv_4 in Hinv_4.
                simpl in Hinv_4.
                intuition.
                apply H7 with (pid:=pid0); auto.
                unfold enq_not_inc in *; simpl in *.
                intuition.
                apply binds_push_inv in H9; auto.
                intuition.
                discriminate.
            ++ rewrite get_r'_any_ary_read in H3; auto.
                unfold inv_4 in Hinv_4.
                simpl in Hinv_4.
                intuition.
                apply H7 with (pid:=pid0); auto.
                unfold enq_not_inc in *; simpl in *.
                intuition.
                apply binds_push_inv in H9; auto.
                intuition.
                discriminate.
    (* inv_4' *)
    --- pose proof Hreach as HreachTmp.
      apply IHk in Hreach; try lia.
      unfold inv_total in Hreach.
      destruct Hreach as [_ [Hinv_e28 [_ [Hinv_1 [_ [Hinv_2 [_ [_ [_ [Hinv_4 _]]]]]]]]]].
      inversion H1; subst; simpl in *.
      inversion H0; subst; simpl in *.
      unfold inv_4'.
      simpl.
      unfold F, R in *; simpl in *.
      unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
      intros.
      inversion H2; subst; simpl in *.
      (* front_rear *)
      + inversion H4; subst; simpl in *.
        inversion H5; subst; simpl in *.
        (* rear *)
        ++ intro.
            unfold inv_4' in Hinv_4.
            simpl in Hinv_4.
            unfold F, R in *; simpl in *.
            unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
            intuition.
            apply H8 with (pid:=pid0); auto.
        (* front *)
        ++ inversion H6; subst; simpl in *.
          inversion H7; subst; simpl in *.
          (* INC *)
          +++ unfold inv_2' in Hinv_2.
            simpl in Hinv_2.
            unfold R, F in *; simpl in *.
            unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
            intuition.
            * apply reachable_len_to_reachable in HreachTmp.
              pose proof HreachTmp as HreachTmp2.
              apply inv_front_inc_at_d31_invariant in HreachTmp.
              unfold inv_front_inc_at_d31 in HreachTmp.
              simpl in HreachTmp.
              apply HreachTmp in Hbinds5; auto.
              apply binds_reconstruct in Hbinds5.
              destruct Hbinds5 as [l1 [l2 Hlist]].
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              rewrite Hlist in H9.
              repeat rewrite get_f'_dist in H9; auto.
              simpl in H9.
              apply notin_get_none in Hnotin_res.
              rewrite Hnotin_res in H9.
              repeat rewrite Nat.add_succ_r in H9; auto.
              rewrite Hlist in H3.
              repeat rewrite get_f'_dist in H3; auto.
              simpl in H3.
              rewrite Hnotin_res in H3.
              repeat rewrite Nat.add_succ_r in H3; auto.
              rewrite Nat.eqb_refl in H3.
              rewrite get_f'_any_rear_push in H3; auto.
              rewrite get_f'_any_rear_push in H3; auto.
              simpl in H3.
              rewrite <-H9 in H3.
              lia.
            * destruct (eq_nat_dec pid pid0).
              ** subst.
                unfold deq_not_inc in H8.
                apply reachable_len_to_reachable in HreachTmp.
                apply inv_front_inc_at_d31_invariant in HreachTmp.
                unfold inv_front_inc_at_d31 in HreachTmp.
                simpl in HreachTmp.
                apply HreachTmp in Hbinds5.
                unfold binds in H8.
                rewrite Hbinds5 in H8.
                simpl in H8.
                intuition; try discriminate.
                apply notin_union in H13.
                destruct H13.
                apply notin_neq in H12; intuition.
              ** apply Hinv_1 in H9; auto.
                simpl in H9.
                destruct H9 as [pid' [Hpid1 Hpid2]].
                destruct (eq_nat_dec pid0 pid').
                *** subst.
                  apply Hpid2 in n0; auto.
                  apply n0.
                  apply reachable_len_to_reachable in HreachTmp.
                  apply inv_front_inc_at_d31_invariant in HreachTmp.
                  unfold inv_front_inc_at_d31 in HreachTmp.
                  simpl in HreachTmp.
                  apply HreachTmp in Hbinds5.
                  unfold deq_not_inc. intuition.
                *** apply Hpid2 in n1; auto.
                  apply n1.
                  unfold deq_not_inc in H8; simpl in *.
                  unfold deq_not_inc; simpl in *.
                  intuition.
                  apply notin_union in H10.
                  intuition.
                *** unfold F, R; simpl.
                  unfold get_front, get_ary, get_rear, get_pc; simpl.

                  apply reachable_len_to_reachable in HreachTmp.
                  apply inv_front_inc_at_d31_invariant in HreachTmp.
                  unfold inv_front_inc_at_d31 in HreachTmp.
                  simpl in HreachTmp.
                  apply HreachTmp in Hbinds5.
                  apply binds_reconstruct in Hbinds5.
                  destruct Hbinds5 as [l1 [l2 Hlist]].
                  rewrite Hlist.
                  repeat rewrite get_f'_dist; auto.
                  simpl.
                  apply notin_get_none in Hnotin_res.
                  rewrite Hnotin_res.
                  lia.
          (* READ *)
          +++ intro.
            unfold inv_4' in Hinv_4.
            simpl in Hinv_4.
            unfold F, R in *; simpl in *.
            unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
            rewrite get_f'_any_rear_read in H3; auto.
            intuition.
            apply H9 with (pid:=pid0); auto.
            clear H9.
            unfold deq_not_inc in *; simpl in *.
            intuition.
            apply notin_union in H10.
            intuition.
      (* array *)
      + intro.
            unfold inv_4' in Hinv_4.
            simpl in Hinv_4.
            unfold F, R in *; simpl in *.
            unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
            inversion H4; subst; simpl in *.
            inversion H6; subst; simpl in *.
            (* CAS *)
            ++ destruct (entry_eqb (Vector.nth vec (Fin.of_nat_lt Hlt)))eqn:Heq.
              (* success *)
              +++ apply reachable_len_to_reachable in HreachTmp.
                pose proof HreachTmp as HreachTmp2.
                apply inv_ary_cas_at_e28_d28_invariant in HreachTmp.
                unfold inv_ary_cas_at_e28_d28 in HreachTmp.
                simpl in HreachTmp.
                apply HreachTmp in Hbinds3; auto.
                intuition.

                (* e18 *)
                * unfold inv_4' in Hinv_4.
                  pose proof H9 as HbindsTmp.
                  apply binds_reconstruct in H9.
                  destruct H9 as [l1 [l2 Hlist]].
                  apply array_queue_wf_invarint in HreachTmp2.
                  unfold array_queue_wf in HreachTmp2.
                  simpl in HreachTmp2.
                  rewrite Hlist in HreachTmp2.
                  apply ok_remove_middle_inv in HreachTmp2.
                  destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
                  rewrite Hlist in H3.
                  repeat rewrite get_f'_dist in H3; auto.
                  simpl in H3.
                  rewrite get_f'_any_ary in H3; auto.
                  rewrite get_f'_any_ary in H3; auto.

                  rewrite Hlist in Hinv_4.
                  repeat rewrite get_f'_dist in Hinv_4; auto.
                  simpl in Hinv_4.
                  intuition.
                  apply H9 with (pid:=pid0); auto.
                  simpl in Hlist.
                  rewrite <-Hlist.
                  unfold deq_not_inc in *; simpl in *.
                  intuition.
                  apply binds_push_inv in H11; auto.
                  intuition.
                  subst.
                  unfold binds in HbindsTmp.
                  rewrite H5 in HbindsTmp; discriminate.

                (* d28 *)
                * unfold inv_2' in Hinv_2.
                  simpl in Hinv_2.
                  unfold F, R in *; simpl in *.
                  unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
                  intuition.
                  ** apply binds_reconstruct in H9.
                    destruct H9 as [l1 [l2 Hlist]].
                    apply array_queue_wf_invarint in HreachTmp2.
                    unfold array_queue_wf in HreachTmp2.
                    simpl in HreachTmp2.
                    rewrite Hlist in HreachTmp2.
                    apply ok_remove_middle_inv in HreachTmp2.
                    destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
                    rewrite Hlist in H10; auto.
                    repeat rewrite get_f'_dist in H10; auto.
                    simpl in H10.
                    apply notin_get_none in Hnotin_res.
                    rewrite Hnotin_res in H10.
                    simpl in H10.

                    rewrite Hlist in H3; auto.
                    repeat rewrite get_f'_dist in H3; auto.
                    simpl in H3.
                    rewrite Hnotin_res in H3.
                    rewrite Nat.eqb_refl in H3.
                    simpl in H3.
                    repeat rewrite Nat.add_succ_r in H3.
                    rewrite get_f'_any_ary in H3; auto.
                    rewrite get_f'_any_ary in H3; auto.
                    rewrite <-H10 in H3. lia.
                  ** apply binds_reconstruct in H9.
                    destruct H9 as [l1 [l2 Hlist]].
                    apply array_queue_wf_invarint in HreachTmp2.
                    unfold array_queue_wf in HreachTmp2.
                    simpl in HreachTmp2.
                    rewrite Hlist in HreachTmp2.
                    apply ok_remove_middle_inv in HreachTmp2.
                    destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
                    rewrite Hlist in H10; auto.
                    repeat rewrite get_f'_dist in H10; auto.
                    simpl in H10.
                    apply notin_get_none in Hnotin_res.
                    rewrite Hnotin_res in H10.
                    simpl in H10.

                    rewrite Hlist in H3; auto.
                    repeat rewrite get_f'_dist in H3; auto.
                    simpl in H3.
                    rewrite Hnotin_res in H3.
                    rewrite Nat.eqb_refl in H3.
                    simpl in H3.
                    repeat rewrite Nat.add_succ_r in H3.
                    rewrite get_f'_any_ary in H3; auto.
                    rewrite get_f'_any_ary in H3; auto.
                    assert (Htmp : forall m n, n = m - 1 -> (S n) = m) by lia.
                    apply Htmp in H10.
                    rewrite <-H10 in H3. lia.
              (* fail *)
              +++ rewrite get_f'_any_ary_cas_false in H3; auto.
                unfold inv_4' in Hinv_4.
                simpl in Hinv_4.
                intuition.
                apply H7 with (pid:=pid0); auto.
                unfold deq_not_inc in *; simpl in *.
                intuition.
                apply binds_push_inv in H9; auto.
                intuition.
                discriminate.
            ++ rewrite get_f'_any_ary_read in H3; auto.
                unfold inv_4' in Hinv_4.
                simpl in Hinv_4.
                intuition.
                apply H7 with (pid:=pid0); auto.
                unfold deq_not_inc in *; simpl in *.
                intuition.
                apply binds_push_inv in H9; auto.
                intuition.
                discriminate.
      (* inv_5 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; auto; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [Hinv_d28 [_ [_ [_ [_ [Hinv_3 [_ [_ [_ [Hinv_5 [_ [Hinv_6 _]]]]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_5; simpl. intros.
        unfold F, R; simpl.
        unfold get_front, get_rear, get_pc, get_ary; simpl.
        inversion H2; subst; simpl in *.
        (* front_rear *)
        + inversion H4; subst; simpl in *.
          inversion H5; subst; simpl in *.
          (* rear *)
          ++ inversion H6; subst; simpl in *.
            inversion H7; subst; simpl in *.
            (* INC *)
            +++ apply reachable_len_to_reachable in HreachTmp.
              pose proof HreachTmp as HreachTmp2.
              apply inv_rear_inc_at_e31_invariant in HreachTmp.
              unfold inv_rear_inc_at_e31 in HreachTmp.
              simpl in HreachTmp.
              apply HreachTmp in Hbinds5.
              apply binds_reconstruct in Hbinds5.
              destruct Hbinds5 as [l1 [l2 Hlist]].
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              rewrite Hlist.
              repeat rewrite get_r'_dist; auto.
              repeat rewrite get_f'_dist; auto.
              simpl.
              rewrite Nat.eqb_refl.
              simpl.
              rewrite get_r'_any_rear_push; auto.
              rewrite get_r'_any_rear_push; auto.

              unfold inv_5 in Hinv_5.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              specialize (Hinv_5 pid0).
              rewrite Hlist in Hinv_5.
              repeat rewrite get_r'_dist in Hinv_5; auto.
              repeat rewrite get_f'_dist in Hinv_5; auto.
              simpl in Hinv_5.
              apply notin_get_none in Hnotin_res.
              rewrite Hnotin_res in Hinv_5.
              assert (Htmp :
              value (LState st0) +
         (get_f' l1 (Array.responses L (LState st1))
            (Counter.responses (LState st0)) +
          get_f' l2 (Array.responses L (LState st1))
            (Counter.responses (LState st0))) <
         v +
         (get_r' l1 (Array.responses L (LState st1)) res +
          S (get_r' l2 (Array.responses L (LState st1)) res))
              ).
              apply Hinv_5.
              simpl in Hlist.
              rewrite <-Hlist.
              clear Hinv_5.
              unfold enq_not_inc in *; simpl in *.
              intuition.
              apply notin_union in H11.
              intuition.
              lia.
          +++ rewrite get_r'_any_rear_read; auto.
            unfold inv_5 in Hinv_5.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
            apply Hinv_5 with (pid:=pid0); auto.
            unfold enq_not_inc in *; simpl in *.
            intuition.
            apply notin_union in H9.
            intuition.
        (* front *)
          ++ inversion H6; subst; simpl in *.
            inversion H7; subst; simpl in *.
            (* INC *)
            +++ apply reachable_len_to_reachable in HreachTmp.
              pose proof HreachTmp as HreachTmp2.
              apply inv_front_inc_at_d31_invariant in HreachTmp.
              unfold inv_front_inc_at_d31 in HreachTmp.
              simpl in HreachTmp.
              apply HreachTmp in Hbinds5.
              apply binds_reconstruct in Hbinds5.
              destruct Hbinds5 as [l1 [l2 Hlist]].
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              rewrite Hlist.
              repeat rewrite get_r'_dist; auto.
              repeat rewrite get_f'_dist; auto.
              simpl.
              rewrite Nat.eqb_refl.
              simpl.
              rewrite get_f'_any_front_push; auto.
              rewrite get_f'_any_front_push; auto.

              unfold inv_5 in Hinv_5.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              specialize (Hinv_5 pid0).
              rewrite Hlist in Hinv_5.
              repeat rewrite get_r'_dist in Hinv_5; auto.
              repeat rewrite get_f'_dist in Hinv_5; auto.
              simpl in Hinv_5.
              apply notin_get_none in Hnotin_res.
              rewrite Hnotin_res in Hinv_5.
              repeat rewrite Nat.add_succ_r in Hinv_5.
              apply Hinv_5; auto.
              simpl in Hlist.
              rewrite <-Hlist.
              clear Hinv_5.
              unfold enq_not_inc in *; simpl in *.
              intuition.
          +++ rewrite get_f'_any_rear_read; auto.
            unfold inv_5 in Hinv_5.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
            apply Hinv_5 with (pid:=pid0); auto.
      (* array *)
      + inversion H4; subst; simpl in *.
        inversion H5; subst; simpl in *.
        (* CAS *)
        ++ destruct ((entry_eqb (Vector.nth vec (Fin.of_nat_lt Hlt)) old))eqn:Heq.
          (* success *)
          +++ apply reachable_len_to_reachable in HreachTmp.
            pose proof HreachTmp as HreachTmp2.
            apply inv_ary_cas_at_e28_d28_invariant in HreachTmp.
            unfold inv_ary_cas_at_e28_d28 in HreachTmp.
            simpl in HreachTmp.
            pose proof Hbinds3 as HbindsTmp.
            apply HreachTmp in Hbinds3.
            intuition.
            (* e28 *)
            * unfold inv_5 in *; simpl in *.
              unfold inv_6 in Hinv_6.
              unfold F, R in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              specialize (Hinv_5 pid0).
              apply binds_reconstruct in H8.
              destruct H8 as [l1 [l2 Hlist]].
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              rewrite Hlist.
              repeat rewrite get_r'_dist; auto.
              repeat rewrite get_f'_dist; auto.
              simpl.
              rewrite Nat.eqb_refl.
              rewrite get_r'_any_ary; auto.
              rewrite get_r'_any_ary; auto.
              rewrite get_f'_any_ary; auto.
              rewrite get_f'_any_ary; auto.
              repeat rewrite Nat.add_succ_r.
              destruct Hinv_6 as [_ [Hfr _]].

              rewrite Hlist in Hfr.
              repeat rewrite get_r'_dist in Hfr; auto.
              repeat rewrite get_f'_dist in Hfr; auto.
              simpl in Hfr.
              apply notin_get_none in Hnotin_res.
              rewrite Hnotin_res in Hfr.
              simpl in Hfr. lia.
            (* d28 *)
            * unfold inv_d28_clean in Hinv_d28.
              unfold inv_3 in Hinv_3.
              unfold F, R in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              (* specialize (Hinv_5 pid0). *)
              pose proof H8 as HbindsTmp'.
              apply binds_reconstruct in H8.
              destruct H8 as [l1 [l2 Hlist]].
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              rewrite Hlist.
              repeat rewrite get_r'_dist; auto.
              repeat rewrite get_f'_dist; auto.
              simpl.
              rewrite Nat.eqb_refl.
              rewrite get_r'_any_ary; auto.
              rewrite get_r'_any_ary; auto.
              rewrite get_f'_any_ary; auto.
              rewrite get_f'_any_ary; auto.
              repeat rewrite Nat.add_succ_r.

              specialize (Hinv_3 pid0).

              assert (Htmp : forall m n, m < n - 1 -> (S m) < n) by lia.
              apply Htmp.

              rewrite Hlist in Hinv_3.
              repeat rewrite get_r'_dist in Hinv_3; auto.
              repeat rewrite get_f'_dist in Hinv_3; auto.
              simpl in Hinv_3.
              rewrite <-Hinv_3.
              pose proof HbindsTmp' as HbindsTmp''.
              apply Hinv_d28 in HbindsTmp'; auto.
              destruct HbindsTmp' as [Hb1 _].
              rewrite Hlist in Hb1.
              repeat rewrite get_r'_dist in Hb1; auto.
              repeat rewrite get_f'_dist in Hb1; auto.
              simpl in Hb1.
              apply notin_get_none in Hnotin_res.
              rewrite Hnotin_res in Hb1.
              simpl in Hb1.
              rewrite <-Hb1.
              pose proof H7 as HreachTmp.
              apply inv_front_d27_before_invariant in H7; auto.
              unfold get_pc in *; simpl in *.
              specialize (H7 pid ADeq28).
Ltac solve_after_d15 :=
  try apply after_d15_Deq26;
  try apply after_d15_Deq27;
  try apply after_d15_Deq28.
              apply H7 in HbindsTmp''; auto; solve_after_d15.
              unfold get_impl in *; simpl in *.
              destruct HbindsTmp'' as [s1 [s2 [it [acts [Hvalid [Hstep [Hb [Heq' Hreach]]]]]]]].
              inversion Hstep; subst; simpl in *.
              inversion H8; subst; simpl in *.
              unfold binds in Hb.
              inversion H9; subst; simpl in *;
              pose proof Hbinds4 as HbindsTmp'''; eauto;
              eapply substitute_eq_binds_v' in Hbinds4; eauto;
              rewrite Hbinds4 in Hb; try discriminate.
              rewrite Heq' in H10.
              apply inv_front_d15_ret_invariant in Hreach; auto.
              unfold get_pc in *; simpl in *.
              apply Hreach in HbindsTmp'''; auto.
              destruct HbindsTmp''' as [s1 [s2 [acts' [Hvalid' [Hstep' Hret]]]]].
              subst.
              unfold get_rear in *; simpl in *.
              eapply Nat.lt_le_trans.
              eauto.
              generalize REAR_not_decrease; intro.
              unfold get_rear in *; simpl in *.
              apply REAR_not_decrease in Hvalid'; auto.
              unfold get_rear in *; simpl in *.
              eapply Nat.le_trans.
              eauto.
              apply REAR_not_decrease in Hvalid; auto.
              apply entry_eqb_eq in Heq; auto.
              subst.

                  apply step_invariant in H7; auto.
                  unfold ComposedLTS.inv in H7.
                  simpl in H7.
                  apply H7 in Hbinds0.
                  destruct Hbinds0 as [s1 [s2 [q [acts [Hint_query [Hvalid Hgather]]]]]].
                  inversion Hint_query; subst; simpl in *.
                  inversion H8; subst; simpl in *.
                  unfold binds in HbindsTmp'.
                  inversion H10; subst; simpl in *.

  tmp'' noB_preserves_AEnq2 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq5 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq11 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq14 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq28 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq31 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq2 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq5 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq11 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq14 Hvalid st2 pid acts Hgather HbindsTmp'.

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
  inversion H9; subst; simpl in *.
  inversion H11; subst; simpl in *.
  inversion H13; subst; simpl in *.
  inversion H12; subst; simpl in *.
  apply valid_execution_fragment_com in HvalidTmp;
  simpl in HvalidTmp;
  eapply internal_preserves_request'' with (pid:=pid) in HvalidTmp; simpl in *; eauto;
  try apply binds_push_eq;
  try (eapply gather_pid_events_B_gather_pid_external_events;
      eassumption).
  inversion HvalidTmp; subst; simpl in *.
  assert (Htmp' : (Fin.of_nat_lt Hlt) =
    (Fin.of_nat_lt (mod_lt H (front pid)))).
  apply Fin.of_nat_ext.
  rewrite <-Hx.
  rewrite H16.
  rewrite Htmp'.
  rewrite Hrear. auto.

  tmp'' noB_preserves_ADeq31 Hvalid st2 pid acts Hgather HbindsTmp'.
  simpl in Hlist.
  rewrite <-Hlist.
  unfold enq_not_inc in *; simpl in *.
  intuition.
  apply binds_push_inv in H9; auto.
  intuition. subst.
  unfold binds in H3.
  rewrite HbindsTmp' in H3; discriminate.
        (* fail *)
        +++ rewrite get_f'_any_ary_cas_false; auto.
          rewrite get_r'_any_ary_cas_false; auto.
          unfold inv_5 in Hinv_5.
          simpl in Hinv_5.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          eapply Hinv_5 with (pid:=pid0); eauto.
          unfold enq_not_inc in *; simpl in *.
          intuition.
          apply binds_push_inv in H7; auto.
          intuition. discriminate.
      (* READ *)
      ++ rewrite get_f'_any_ary_read; auto.
        rewrite get_r'_any_ary_read; auto.
        unfold inv_5 in Hinv_5.
        simpl in Hinv_5.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
        eapply Hinv_5 with (pid:=pid0); eauto.
        unfold enq_not_inc in *; simpl in *.
        intuition.
        apply binds_push_inv in H7; auto.
        intuition. discriminate.
      (* inv_5' *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; auto; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [Hinv_d28 [_ [_ [_ [_ [_ [_ [Hinv_3 [_ [Hinv_4' [_ [Hinv_5 [Hinv_6 _]]]]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_5'; simpl. intros.
        unfold F, R; simpl.
        unfold get_front, get_rear, get_pc, get_ary; simpl.
        inversion H2; subst; simpl in *.
        (* front_rear *)
        + inversion H4; subst; simpl in *.
          inversion H5; subst; simpl in *.

        (* rear *)
          ++ inversion H6; subst; simpl in *.
            inversion H7; subst; simpl in *.
            (* INC *)
            +++ apply reachable_len_to_reachable in HreachTmp.
              pose proof HreachTmp as HreachTmp2.
              apply inv_rear_inc_at_e31_invariant in HreachTmp.
              unfold inv_rear_inc_at_e31 in HreachTmp.
              simpl in HreachTmp.
              apply HreachTmp in Hbinds5.
              apply binds_reconstruct in Hbinds5.
              destruct Hbinds5 as [l1 [l2 Hlist]].
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              rewrite Hlist.
              repeat rewrite get_r'_dist; auto.
              repeat rewrite get_f'_dist; auto.
              simpl.
              rewrite Nat.eqb_refl.
              simpl.
              rewrite get_r'_any_rear_push; auto.
              rewrite get_r'_any_rear_push; auto.

              unfold inv_5' in Hinv_5.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              specialize (Hinv_5 pid0).
              rewrite Hlist in Hinv_5.
              repeat rewrite get_r'_dist in Hinv_5; auto.
              repeat rewrite get_f'_dist in Hinv_5; auto.
              simpl in Hinv_5.
              apply notin_get_none in Hnotin_res.
              rewrite Hnotin_res in Hinv_5.
              repeat rewrite Nat.add_succ_r in Hinv_5.
              apply Hinv_5; auto.
              simpl in Hlist.
              rewrite <-Hlist.
              clear Hinv_5.
              unfold deq_not_inc in *; simpl in *.
              intuition.
          +++ rewrite get_r'_any_rear_read; auto.
            unfold inv_5' in Hinv_5.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
            apply Hinv_5 with (pid:=pid0); auto.

          (* front *)
          ++ inversion H6; subst; simpl in *.
            inversion H7; subst; simpl in *.
            (* INC *)
            +++ apply reachable_len_to_reachable in HreachTmp.
              pose proof HreachTmp as HreachTmp2.
              apply inv_front_inc_at_d31_invariant in HreachTmp.
              unfold inv_front_inc_at_d31 in HreachTmp.
              simpl in HreachTmp.
              apply HreachTmp in Hbinds5.
              apply binds_reconstruct in Hbinds5.
              destruct Hbinds5 as [l1 [l2 Hlist]].
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              rewrite Hlist.
              repeat rewrite get_r'_dist; auto.
              repeat rewrite get_f'_dist; auto.
              simpl.
              rewrite Nat.eqb_refl.
              simpl.
              rewrite get_f'_any_front_push; auto.
              rewrite get_f'_any_front_push; auto.

              unfold inv_5' in Hinv_5.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              specialize (Hinv_5 pid0).
              rewrite Hlist in Hinv_5.
              repeat rewrite get_r'_dist in Hinv_5; auto.
              repeat rewrite get_f'_dist in Hinv_5; auto.
              simpl in Hinv_5.
              apply notin_get_none in Hnotin_res.
              rewrite Hnotin_res in Hinv_5.
              assert (Htmp :
              value (LState st3) +
         (get_r' l1 (Array.responses L (LState st1))
            (Counter.responses (LState st3)) +
          get_r' l2 (Array.responses L (LState st1))
            (Counter.responses (LState st3))) <
         v +
         (get_f' l1 (Array.responses L (LState st1)) res +
          S (get_f' l2 (Array.responses L (LState st1)) res)) + L
              ).
              apply Hinv_5.
              simpl in Hlist.
              rewrite <-Hlist.
              clear Hinv_5.
              unfold deq_not_inc in *; simpl in *.
              intuition.
              apply notin_union in H11.
              intuition.
              lia.
          +++ rewrite get_f'_any_rear_read; auto.
            unfold inv_5' in Hinv_5.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
            apply Hinv_5 with (pid:=pid0); auto.
            unfold deq_not_inc in *; simpl in *.
            intuition.
            apply notin_union in H9.
            intuition.
      (* array *)
      + inversion H4; subst; simpl in *.
        inversion H5; subst; simpl in *.
        (* CAS *)
        ++ destruct ((entry_eqb (Vector.nth vec (Fin.of_nat_lt Hlt)) old))eqn:Heq.
          (* success *)
          +++ apply reachable_len_to_reachable in HreachTmp.
            pose proof HreachTmp as HreachTmp2.
            apply inv_ary_cas_at_e28_d28_invariant in HreachTmp.
            unfold inv_ary_cas_at_e28_d28 in HreachTmp.
            simpl in HreachTmp.
            pose proof Hbinds3 as HbindsTmp.
            apply HreachTmp in Hbinds3.
            intuition.
            (* e28 *)
            * unfold inv_e28_clean in Hinv_d28.
              unfold inv_3' in Hinv_3.
              unfold inv_4' in Hinv_4'.
              unfold F, R in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              (* specialize (Hinv_5 pid0). *)
              pose proof H8 as HbindsTmp'.
              apply binds_reconstruct in H8.
              destruct H8 as [l1 [l2 Hlist]].
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              rewrite Hlist.
              repeat rewrite get_r'_dist; auto.
              repeat rewrite get_f'_dist; auto.
              simpl.
              rewrite Nat.eqb_refl.
              rewrite get_r'_any_ary; auto.
              rewrite get_r'_any_ary; auto.
              rewrite get_f'_any_ary; auto.
              rewrite get_f'_any_ary; auto.
              repeat rewrite Nat.add_succ_r.

              specialize (Hinv_3 pid0).

              assert (Htmp : forall m n, m < n - 1 -> (S m) < n) by lia.
              apply Htmp.

              rewrite Hlist in Hinv_3.
              repeat rewrite get_r'_dist in Hinv_3; auto.
              repeat rewrite get_f'_dist in Hinv_3; auto.
              simpl in Hinv_3.

              destruct (value (LState (Tensor.L1State (LState st0))) +
         (get_f' l1 res
            (Counter.responses (LState (Tensor.L1State (LState st0)))) +
          get_f' l2 res
            (Counter.responses (LState (Tensor.L1State (LState st0))))))eqn:Heq''.

              assert (Hf : value (LState (Tensor.L1State (LState st0))) = 0) by lia.
              rewrite <-Heq'' in Hf.

              rewrite Hlist in Hinv_4'.
              repeat rewrite get_r'_dist in Hinv_4'; auto.
              repeat rewrite get_f'_dist in Hinv_4'; auto.
              simpl in Hinv_4'.
              apply Hinv_4' with (pid:=pid0) in Hf; auto.
              exfalso.
              apply Hf.
              simpl in Hlist.
              try rewrite <-Hlist in *.
              unfold deq_not_inc in *.
              clear Hf.
              intuition. left.
              intuition.
              simpl in H9.
              simpl.
              apply binds_push_inv in H9; auto.
              intuition. subst.
              unfold binds in H3.
              rewrite HbindsTmp' in H3.
              discriminate.
              try rewrite <-Heq'' in *.
              assert (Htt :
                value (LState (Tensor.L1State (LState st0))) +
(get_f' l1 res
   (Counter.responses (LState (Tensor.L1State (LState st0)))) +
 get_f' l2 res
   (Counter.responses (LState (Tensor.L1State (LState st0))))) + L -
1 =
value (LState (Tensor.L1State (LState st0))) +
(get_f' l1 res
   (Counter.responses (LState (Tensor.L1State (LState st0)))) +
 get_f' l2 res
   (Counter.responses (LState (Tensor.L1State (LState st0))))) - 1 + L
              ) by lia.
              rewrite Htt.

              rewrite <-Hinv_3.
              pose proof HbindsTmp' as HbindsTmp''.
              apply Hinv_d28 in HbindsTmp'; auto.
              destruct HbindsTmp' as [Hb1 Hb2].
              rewrite Hlist in Hb1.
              repeat rewrite get_r'_dist in Hb1; auto.
              repeat rewrite get_f'_dist in Hb1; auto.
              simpl in Hb1.
              apply notin_get_none in Hnotin_res.
              rewrite Hnotin_res in Hb1.
              simpl in Hb1.
              rewrite <-Hb1.

              rewrite Hlist in Hb2.
              repeat rewrite get_r'_dist in Hb2; auto.
              repeat rewrite get_f'_dist in Hb2; auto.
              simpl in Hb2.
              rewrite Hnotin_res in Hb2.
              simpl in Hb2.
              pose proof H7 as HreachTmp.
              apply inv_rear_e27_before_invariant in H7; auto.
              unfold get_pc in *; simpl in *.
              specialize (H7 pid AEnq28).

Ltac solve_after_e15 :=
  try apply after_e15_Enq26;
  try apply after_e15_Enq27;
  try apply after_e15_Enq28.
              apply H7 in HbindsTmp''; auto; solve_after_e15.
              unfold ArrayQueueInvariantBefore0.get_impl in *; simpl in *.
              destruct HbindsTmp'' as [s1 [s2 [it [acts [Hvalid [Hstep [Hb [Heq' Hreach]]]]]]]].
              inversion Hstep; subst; simpl in *.
              inversion H8; subst; simpl in *.
              unfold binds in Hb.
              inversion H9; subst; simpl in *;
              pose proof Hbinds4 as HbindsTmp'''; eauto;
              eapply substitute_eq_binds_v' in Hbinds4; eauto;
              rewrite Hbinds4 in Hb; try discriminate.
              rewrite Heq' in H10.
              apply inv_rear_e15_ret_invariant in Hreach; auto.
              unfold get_pc in *; simpl in *.
              apply Hreach in HbindsTmp'''; auto.
              destruct HbindsTmp''' as [s1 [s2 [acts' [Hvalid' [Hstep' Hret]]]]].
              subst.
              unfold get_front in *; simpl in *.
              eapply Nat.lt_le_trans.
              eauto.
              generalize FRONT_not_decrease; intro.
              unfold ArrayQueueInvariant.get_front in *; simpl in *.
              apply FRONT_not_decrease in Hvalid'; auto.
              unfold ArrayQueueInvariant.get_front in *; simpl in *.
              eapply Nat.le_trans.
              eauto.
              unfold ArrayQueueInvariant.get_front in *; simpl in *.
              apply FRONT_not_decrease in Hvalid; auto.
              unfold ArrayQueueInvariant.get_front in *; simpl in *.
              auto. lia.
              apply entry_eqb_eq in Heq; auto.
              subst.

                  apply step_invariant in H7; auto.
                  unfold ComposedLTS.inv in H7.
                  simpl in H7.
                  apply H7 in Hbinds0.
                  destruct Hbinds0 as [s1 [s2 [q [acts [Hint_query [Hvalid Hgather]]]]]].
                  inversion Hint_query; subst; simpl in *.
                  inversion H8; subst; simpl in *.
                  unfold binds in HbindsTmp'.
                  inversion H10; subst; simpl in *.

  tmp'' noB_preserves_AEnq2 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq5 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq11 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq14 Hvalid st2 pid acts Hgather HbindsTmp'.

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
  inversion H9; subst; simpl in *.
  inversion H11; subst; simpl in *.
  inversion H13; subst; simpl in *.
  inversion H12; subst; simpl in *.
  apply valid_execution_fragment_com in HvalidTmp;
  simpl in HvalidTmp;
  eapply internal_preserves_request'' with (pid:=pid) in HvalidTmp; simpl in *; eauto;
  try apply binds_push_eq;
  try (eapply gather_pid_events_B_gather_pid_external_events;
      eassumption).
  inversion HvalidTmp; subst; simpl in *.
  assert (Htmp' : (Fin.of_nat_lt Hlt) =
    (Fin.of_nat_lt (mod_lt H (rear pid)))).
  apply Fin.of_nat_ext.
  rewrite <-Hx.
  rewrite H16.
  rewrite Htmp'.
  rewrite Hrear. auto.

  tmp'' noB_preserves_AEnq31 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq2 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq5 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq11 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq14 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq28 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq31 Hvalid st2 pid acts Hgather HbindsTmp'.
  simpl in Hlist.
  rewrite <-Hlist.
  unfold deq_not_inc in *; simpl in *.
  intuition.
  apply binds_push_inv in H9; auto.
  intuition. subst.
  unfold binds in H3.
  rewrite HbindsTmp' in H3; discriminate.

            (* d28 *)
            * unfold inv_5' in *; simpl in *.
              unfold inv_6 in Hinv_6.
              unfold F, R in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              specialize (Hinv_5 pid0).
              apply binds_reconstruct in H8.
              destruct H8 as [l1 [l2 Hlist]].
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              rewrite Hlist.
              repeat rewrite get_r'_dist; auto.
              repeat rewrite get_f'_dist; auto.
              simpl.
              rewrite Nat.eqb_refl.
              rewrite get_r'_any_ary; auto.
              rewrite get_r'_any_ary; auto.
              rewrite get_f'_any_ary; auto.
              rewrite get_f'_any_ary; auto.
              repeat rewrite Nat.add_succ_r.
              destruct Hinv_6 as [_ [_ Hfr]].

              rewrite Hlist in Hfr.
              repeat rewrite get_r'_dist in Hfr; auto.
              repeat rewrite get_f'_dist in Hfr; auto.
              simpl in Hfr.
              apply notin_get_none in Hnotin_res.
              rewrite Hnotin_res in Hfr.
              simpl in Hfr. lia.
        (* fail *)
        +++ rewrite get_r'_any_ary_cas_false; auto.
          rewrite get_f'_any_ary_cas_false; auto.
          unfold inv_5' in Hinv_5.
          simpl in Hinv_5.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          eapply Hinv_5 with (pid:=pid0); eauto.
          unfold deq_not_inc in *; simpl in *.
          intuition.
          apply binds_push_inv in H7; auto.
          intuition. discriminate.
      (* READ *)
      ++ rewrite get_f'_any_ary_read; auto.
        rewrite get_r'_any_ary_read; auto.
        unfold inv_5' in Hinv_5.
        simpl in Hinv_5.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
        eapply Hinv_5 with (pid:=pid0); eauto.
        unfold deq_not_inc in *; simpl in *.
        intuition.
        apply binds_push_inv in H7; auto.
        intuition. discriminate.
    --- pose proof Hreach as HreachTmp.
      apply IHk in Hreach; try lia.
      unfold inv_total in Hreach.
      destruct Hreach as [Hinv_e28 [Hinv_d28 [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_6 _]]]]]]]]]]]]].
      inversion H1; subst; simpl in *.
      inversion H0; subst; simpl in *.
      unfold inv_6; simpl.
      unfold F, R; simpl.
      unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
      inversion H2; subst; simpl in *.
      (* front_rear *)
      + inversion H3; subst; simpl in *.
        inversion H4; subst; simpl in *.
        (* rear *)
        ++ inversion H5; subst; simpl in *.
          inversion H6; subst; simpl in *.
          (* INC *)
          +++ unfold inv_6 in *; simpl in *.
            unfold F, R in *; simpl in *.
            unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
            intuition.
            eapply Nat.le_trans.
            eauto.
            apply reachable_len_to_reachable in HreachTmp.
            pose proof HreachTmp as HreachTmp2.
            apply inv_rear_inc_at_e31_invariant in HreachTmp.
            unfold inv_rear_inc_at_e31 in HreachTmp.
            simpl in HreachTmp.
            apply HreachTmp in Hbinds5.
            apply binds_reconstruct in Hbinds5.
            destruct Hbinds5 as [l1 [l2 Hlist]].
            apply array_queue_wf_invarint in HreachTmp2.
            unfold array_queue_wf in HreachTmp2.
            simpl in HreachTmp2.
            rewrite Hlist in HreachTmp2.
            apply ok_remove_middle_inv in HreachTmp2.
            destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
            rewrite Hlist.
            repeat rewrite get_r'_dist; auto.
            simpl.
            rewrite Nat.eqb_refl.
            apply notin_get_none in Hnotin_res.
            rewrite Hnotin_res.
            simpl.
            rewrite get_r'_any_rear_push; auto.
            rewrite get_r'_any_rear_push; auto.
            lia.
            eapply Nat.le_trans.
            2 : { eauto. }
            apply reachable_len_to_reachable in HreachTmp.
            pose proof HreachTmp as HreachTmp2.
            apply inv_rear_inc_at_e31_invariant in HreachTmp.
            unfold inv_rear_inc_at_e31 in HreachTmp.
            simpl in HreachTmp.
            apply HreachTmp in Hbinds5.
            apply binds_reconstruct in Hbinds5.
            destruct Hbinds5 as [l1 [l2 Hlist]].
            apply array_queue_wf_invarint in HreachTmp2.
            unfold array_queue_wf in HreachTmp2.
            simpl in HreachTmp2.
            rewrite Hlist in HreachTmp2.
            apply ok_remove_middle_inv in HreachTmp2.
            destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
            rewrite Hlist.
            repeat rewrite get_r'_dist; auto.
            simpl.
            rewrite Nat.eqb_refl.
            apply notin_get_none in Hnotin_res.
            rewrite Hnotin_res.
            simpl.
            rewrite get_r'_any_rear_push; auto.
            rewrite get_r'_any_rear_push; auto.
            lia.
          (* READ *)
          +++ rewrite get_r'_any_rear_read; auto.
        (* front *)
        ++ inversion H5; subst; simpl in *.
          inversion H6; subst; simpl in *.
          (* INC *)
          +++ unfold inv_6 in *; simpl in *.
            unfold F, R in *; simpl in *.
            unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
            split. lia.
            intuition.
            eapply Nat.le_trans.
            2 : { eauto. }
            apply reachable_len_to_reachable in HreachTmp.
            pose proof HreachTmp as HreachTmp2.
            apply inv_front_inc_at_d31_invariant in HreachTmp.
            unfold inv_front_inc_at_d31 in HreachTmp.
            simpl in HreachTmp.
            apply HreachTmp in Hbinds5.
            apply binds_reconstruct in Hbinds5.
            destruct Hbinds5 as [l1 [l2 Hlist]].
            apply array_queue_wf_invarint in HreachTmp2.
            unfold array_queue_wf in HreachTmp2.
            simpl in HreachTmp2.
            rewrite Hlist in HreachTmp2.
            apply ok_remove_middle_inv in HreachTmp2.
            destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
            rewrite Hlist.
            repeat rewrite get_f'_dist; auto.
            simpl.
            rewrite Nat.eqb_refl.
            apply notin_get_none in Hnotin_res.
            rewrite Hnotin_res.
            simpl.
            rewrite get_f'_any_front_push; auto.
            rewrite get_f'_any_front_push; auto.
            lia.

            eapply Nat.le_trans.
            eauto.
            apply reachable_len_to_reachable in HreachTmp.
            pose proof HreachTmp as HreachTmp2.
            apply inv_front_inc_at_d31_invariant in HreachTmp.
            unfold inv_front_inc_at_d31 in HreachTmp.
            simpl in HreachTmp.
            apply HreachTmp in Hbinds5.
            apply binds_reconstruct in Hbinds5.
            destruct Hbinds5 as [l1 [l2 Hlist]].
            apply array_queue_wf_invarint in HreachTmp2.
            unfold array_queue_wf in HreachTmp2.
            simpl in HreachTmp2.
            rewrite Hlist in HreachTmp2.
            apply ok_remove_middle_inv in HreachTmp2.
            destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
            rewrite Hlist.
            repeat rewrite get_f'_dist; auto.
            simpl.
            rewrite Nat.eqb_refl.
            apply notin_get_none in Hnotin_res.
            rewrite Hnotin_res.
            simpl.
            rewrite get_f'_any_front_push; auto.
            rewrite get_f'_any_front_push; auto.
            lia.
          +++ rewrite get_f'_any_rear_read; auto.
      (* array *)
      + inversion H3; subst; simpl in *.
        inversion H4; subst; simpl in *.
        (* CAS *)
        ++ destruct (entry_eqb (Vector.nth vec (Fin.of_nat_lt Hlt)))eqn:Heq.
          (* success *)
          +++ apply reachable_len_to_reachable in HreachTmp.
            pose proof HreachTmp as HreachTmp2.
            apply inv_ary_cas_at_e28_d28_invariant in HreachTmp.
            unfold inv_ary_cas_at_e28_d28 in HreachTmp.
            simpl in HreachTmp.
            pose proof Hbinds3 as HbindsTmp.
            apply HreachTmp in Hbinds3.
            destruct Hbinds3 as [Hb|Hb].
            (* e28 *)
            * unfold inv_6 in *; simpl in *.
              unfold F, R in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              split. lia.
              pose proof Hb as HbindsTmp'.
              apply binds_reconstruct in Hb.
              destruct Hb as [l1 [l2 Hlist]].
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              rewrite Hlist.
              repeat rewrite get_f'_dist; auto.
              repeat rewrite get_r'_dist; auto.
              simpl.
              rewrite Nat.eqb_refl.
              simpl.
              rewrite get_r'_any_ary; auto.
              rewrite get_r'_any_ary; auto.
              rewrite get_f'_any_ary; auto.
              rewrite get_f'_any_ary; auto.
              rewrite Hlist in Hinv_6.
              repeat rewrite get_f'_dist in Hinv_6; auto.
              repeat rewrite get_r'_dist in Hinv_6; auto.
              simpl in Hinv_6.
              apply notin_get_none in Hnotin_res.
              rewrite Hnotin_res in Hinv_6.
              simpl in Hinv_6.
              intuition. lia.
              unfold inv_e28_clean in Hinv_e28.
              simpl in Hinv_e28.
              unfold F, R in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              apply Hinv_e28 in HbindsTmp'.
              intuition.
              rewrite Hlist in H11.
              repeat rewrite get_f'_dist in H11; auto.
              repeat rewrite get_r'_dist in H11; auto.
              simpl in H11.
              rewrite Hnotin_res in H11.
              simpl in H11. lia.

              apply entry_eqb_eq in Heq; auto.
              subst.

                  apply step_invariant in H8; auto.
                  unfold ComposedLTS.inv in H8.
                  simpl in H8.
                  apply H8 in Hbinds0.
                  destruct Hbinds0 as [s1 [s2 [q [acts [Hint_query [Hvalid Hgather]]]]]].
                  inversion Hint_query; subst; simpl in *.
                  inversion H6; subst; simpl in *.
                  unfold binds in HbindsTmp'.
                  inversion H12; subst; simpl in *.

  tmp'' noB_preserves_AEnq2 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq5 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq11 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq14 Hvalid st2 pid acts Hgather HbindsTmp'.

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
  inversion H11; subst; simpl in *.
  inversion H13; subst; simpl in *.
  inversion H15; subst; simpl in *.
  inversion H14; subst; simpl in *.
  apply valid_execution_fragment_com in HvalidTmp;
  simpl in HvalidTmp;
  eapply internal_preserves_request'' with (pid:=pid) in HvalidTmp; simpl in *; eauto;
  try apply binds_push_eq;
  try (eapply gather_pid_events_B_gather_pid_external_events;
      eassumption).
  inversion HvalidTmp; subst; simpl in *.
  assert (Htmp' : (Fin.of_nat_lt Hlt) =
    (Fin.of_nat_lt (mod_lt H (rear pid)))).
  apply Fin.of_nat_ext.
  rewrite <-Hx.
  rewrite H18.
  rewrite Htmp'.
  rewrite Hrear. auto.

  tmp'' noB_preserves_AEnq31 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq2 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq5 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq11 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq14 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq28 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq31 Hvalid st2 pid acts Hgather HbindsTmp'.
                (* d28 *)
            * unfold inv_6 in *; simpl in *.
              unfold F, R in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              split. lia.
              pose proof Hb as HbindsTmp'.
              apply binds_reconstruct in Hb.
              destruct Hb as [l1 [l2 Hlist]].
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              rewrite Hlist.
              repeat rewrite get_f'_dist; auto.
              repeat rewrite get_r'_dist; auto.
              simpl.
              rewrite Nat.eqb_refl.
              simpl.
              rewrite get_r'_any_ary; auto.
              rewrite get_r'_any_ary; auto.
              rewrite get_f'_any_ary; auto.
              rewrite get_f'_any_ary; auto.
              rewrite Hlist in Hinv_6.
              repeat rewrite get_f'_dist in Hinv_6; auto.
              repeat rewrite get_r'_dist in Hinv_6; auto.
              simpl in Hinv_6.
              apply notin_get_none in Hnotin_res.
              rewrite Hnotin_res in Hinv_6.
              simpl in Hinv_6.
              intuition. 2 : { lia. }
              unfold inv_d28_clean in Hinv_d28.
              simpl in Hinv_d28.
              unfold F, R in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              apply Hinv_d28 in HbindsTmp'.
              intuition.
              rewrite Hlist in H11.
              repeat rewrite get_f'_dist in H11; auto.
              repeat rewrite get_r'_dist in H11; auto.
              simpl in H11.
              rewrite Hnotin_res in H11.
              simpl in H11. lia.

              apply entry_eqb_eq in Heq; auto.
              subst.

                  apply step_invariant in H8; auto.
                  unfold ComposedLTS.inv in H8.
                  simpl in H8.
                  apply H8 in Hbinds0.
                  destruct Hbinds0 as [s1 [s2 [q [acts [Hint_query [Hvalid Hgather]]]]]].
                  inversion Hint_query; subst; simpl in *.
                  inversion H6; subst; simpl in *.
                  unfold binds in HbindsTmp'.
                  inversion H12; subst; simpl in *.

  tmp'' noB_preserves_AEnq2 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq5 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq11 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq14 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq28 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq31 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq2 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq5 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq11 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq14 Hvalid st2 pid acts Hgather HbindsTmp'.

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
  inversion H11; subst; simpl in *.
  inversion H13; subst; simpl in *.
  inversion H15; subst; simpl in *.
  inversion H14; subst; simpl in *.
  apply valid_execution_fragment_com in HvalidTmp;
  simpl in HvalidTmp;
  eapply internal_preserves_request'' with (pid:=pid) in HvalidTmp; simpl in *; eauto;
  try apply binds_push_eq;
  try (eapply gather_pid_events_B_gather_pid_external_events;
      eassumption).
  inversion HvalidTmp; subst; simpl in *.
  assert (Htmp' : (Fin.of_nat_lt Hlt) =
    (Fin.of_nat_lt (mod_lt H (front pid)))).
  apply Fin.of_nat_ext.
  rewrite <-Hx.
  rewrite H18.
  rewrite Htmp'.
  rewrite Hrear. auto.

  tmp'' noB_preserves_ADeq31 Hvalid st2 pid acts Hgather HbindsTmp'.
                (* fail *)
                +++ rewrite get_f'_any_ary_cas_false; auto.
                  rewrite get_r'_any_ary_cas_false; auto.
              (* READ *)
              ++ rewrite get_f'_any_ary_read; auto.
                rewrite get_r'_any_ary_read; auto.
    --- pose proof Hreach as HreachTmp.
      apply IHk in Hreach; try lia.
      unfold inv_total in Hreach.
      destruct Hreach as [Hinv_e28 [Hinv_d28 [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_6 Hinv_range]]]]]]]]]]]]].
      inversion H1; subst; simpl in *.
      inversion H0; subst; simpl in *.
      unfold inv_range; simpl.
      unfold F, R in *; simpl in *.
      unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
      inversion H2; subst; simpl in *.
      (* front_rear *)
      + inversion H3; subst; simpl in *.
        inversion H4; subst; simpl in *.
        (* rear *)
        ++ inversion H5; subst; simpl in *.
          inversion H6; subst; simpl in *.
          (* INC *)
          +++ unfold inv_range in *; simpl in *.
            unfold F, R in *; simpl in *.
            unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
            apply reachable_len_to_reachable in HreachTmp.
            pose proof HreachTmp as HreachTmp2.
            apply inv_rear_inc_at_e31_invariant in HreachTmp.
            unfold inv_rear_inc_at_e31 in HreachTmp.
            simpl in HreachTmp.
            apply HreachTmp in Hbinds5.
            apply binds_reconstruct in Hbinds5.
            destruct Hbinds5 as [l1 [l2 Hlist]].
            apply array_queue_wf_invarint in HreachTmp2.
            unfold array_queue_wf in HreachTmp2.
            simpl in HreachTmp2.
            rewrite Hlist in HreachTmp2.
            apply ok_remove_middle_inv in HreachTmp2.
            destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
            rewrite Hlist.
            repeat rewrite get_r'_dist; auto.
            repeat rewrite get_f'_dist; auto.
            simpl.
            rewrite Nat.eqb_refl.
            apply notin_get_none in Hnotin_res.
            (* rewrite Hnotin_res. *)
            simpl.
            rewrite get_r'_any_rear_push; auto.
            rewrite get_r'_any_rear_push; auto.

            rewrite Hlist in Hinv_range.
            repeat rewrite get_r'_dist in Hinv_range; auto.
            repeat rewrite get_f'_dist in Hinv_range; auto.
            simpl in Hinv_range.
            rewrite Hnotin_res in Hinv_range.
            simpl in Hinv_range.
            repeat rewrite Nat.add_succ_r in Hinv_range.
            intuition.
          +++ rewrite get_r'_any_rear_read; auto.
        (* front *)
        ++ inversion H5; subst; simpl in *.
          inversion H6; subst; simpl in *.
          (* INC *)
          +++ unfold inv_range in *; simpl in *.
            unfold F, R in *; simpl in *.
            unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
            apply reachable_len_to_reachable in HreachTmp.
            pose proof HreachTmp as HreachTmp2.
            apply inv_front_inc_at_d31_invariant in HreachTmp.
            unfold inv_front_inc_at_d31 in HreachTmp.
            simpl in HreachTmp.
            apply HreachTmp in Hbinds5.
            apply binds_reconstruct in Hbinds5.
            destruct Hbinds5 as [l1 [l2 Hlist]].
            apply array_queue_wf_invarint in HreachTmp2.
            unfold array_queue_wf in HreachTmp2.
            simpl in HreachTmp2.
            rewrite Hlist in HreachTmp2.
            apply ok_remove_middle_inv in HreachTmp2.
            destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
            rewrite Hlist.
            repeat rewrite get_r'_dist; auto.
            repeat rewrite get_f'_dist; auto.
            simpl.
            rewrite Nat.eqb_refl.
            apply notin_get_none in Hnotin_res.
            (* rewrite Hnotin_res. *)
            simpl.
            rewrite get_f'_any_front_push; auto.
            rewrite get_f'_any_front_push; auto.

            rewrite Hlist in Hinv_range.
            repeat rewrite get_r'_dist in Hinv_range; auto.
            repeat rewrite get_f'_dist in Hinv_range; auto.
            simpl in Hinv_range.
            rewrite Hnotin_res in Hinv_range.
            simpl in Hinv_range.
            repeat rewrite Nat.add_succ_r in Hinv_range.
            intuition.
          +++ rewrite get_f'_any_rear_read; auto.
      (* array *)
      + inversion H3; subst; simpl in *.
        inversion H4; subst; simpl in *.
        (* CAS *)
        ++ destruct (entry_eqb (Vector.nth vec (Fin.of_nat_lt Hlt)) old)eqn:Heq.
          (* success *)
          +++ apply reachable_len_to_reachable in HreachTmp.
            pose proof HreachTmp as HreachTmp2.
            apply inv_ary_cas_at_e28_d28_invariant in HreachTmp.
            unfold inv_ary_cas_at_e28_d28 in HreachTmp.
            simpl in HreachTmp.
            pose proof Hbinds3 as HbindsTmp.
            apply HreachTmp in Hbinds3.
            destruct Hbinds3 as [Hb|Hb].
            (* e28 *)
            * unfold inv_range in *; simpl in *.
              unfold inv_6 in *; simpl in *.
              unfold F, R in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              pose proof Hb as HbindsTmp'.
              apply binds_reconstruct in Hb.
              destruct Hb as [l1 [l2 Hlist]].
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              rewrite Hlist.
              repeat rewrite get_f'_dist; auto.
              repeat rewrite get_r'_dist; auto.
              simpl.
              rewrite Nat.eqb_refl.
              simpl.
              rewrite get_r'_any_ary; auto.
              rewrite get_r'_any_ary; auto.
              rewrite get_f'_any_ary; auto.
              rewrite get_f'_any_ary; auto.
              rewrite Hlist in Hinv_range.
              repeat rewrite get_f'_dist in Hinv_range; auto.
              repeat rewrite get_r'_dist in Hinv_range; auto.
              simpl in Hinv_range.
              apply notin_get_none in Hnotin_res.
              rewrite Hnotin_res in Hinv_range.
              simpl in Hinv_range.
              unfold inv_e28_clean in Hinv_e28.
              simpl in Hinv_e28.
              unfold F, R in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.

              destruct HreachTmp as [HreachTmp H8].
              apply entry_eqb_eq in Heq; auto.
              subst.

                  apply step_invariant in H8; auto.
                  unfold ComposedLTS.inv in H8.
                  simpl in H8.
                  apply H8 in Hbinds0.
                  destruct Hbinds0 as [s1 [s2 [q [acts [Hint_query [Hvalid Hgather]]]]]].
                  inversion Hint_query; subst; simpl in *.
                  inversion H5; subst; simpl in *.
                  unfold binds in HbindsTmp'.
                  inversion H7; subst; simpl in *.

  tmp'' noB_preserves_AEnq2 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq5 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq11 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq14 Hvalid st2 pid acts Hgather HbindsTmp'.

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
  inversion H6; subst; simpl in *.
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
  assert (Htmp' : (Fin.of_nat_lt Hlt) =
    (Fin.of_nat_lt (mod_lt H (rear pid)))).
  apply Fin.of_nat_ext.


              apply Hinv_e28 in HbindsTmp'; auto.
              rewrite Hlist in HbindsTmp'.
              repeat rewrite get_f'_dist in HbindsTmp'; auto.
              repeat rewrite get_r'_dist in HbindsTmp'; auto.
              simpl in HbindsTmp'.
              rewrite Hnotin_res in HbindsTmp'.
              simpl in HbindsTmp'.
              destruct HbindsTmp' as [Hb1 Hb2].
              repeat rewrite Nat.add_succ_r.

              rewrite Hlist in Hinv_6.
              repeat rewrite get_f'_dist in Hinv_6; auto.
              repeat rewrite get_r'_dist in Hinv_6; auto.
              simpl in Hinv_6.
              rewrite Hnotin_res in Hinv_6.
              simpl in Hinv_6.
              destruct Hinv_range as [Hinv_range1 Hinv_range2].

              intuition.
              apply all_some_S_r; simpl; auto.
              rewrite Htmp'.
              rewrite Hrear.
              rewrite Hb1.

              erewrite <-array_to_queue_replace_r; eauto.
              rewrite <-Hb1.
              rewrite Htmp'.
              rewrite <-Hrear.
              rewrite Vector.nth_replace_eq; auto.
              simpl. intuition. discriminate.
              simpl.
              rewrite array_to_queue_S_f in Hinv_range2; try lia.
              apply all_none_dist_inv in Hinv_range2.
              intuition.
              rewrite Htmp'.
              rewrite Hrear.
              rewrite Hb1.
              rewrite <-array_to_queue_replace_f; auto.
              lia.

              rewrite <-Hx.
              rewrite <-Hrear.
              rewrite <-Htmp'.
              auto.
  tmp'' noB_preserves_AEnq31 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq2 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq5 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq11 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq14 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq28 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq31 Hvalid st2 pid acts Hgather HbindsTmp'.
            (* d28 *)
            * unfold inv_range in *; simpl in *.
              unfold inv_6 in *; simpl in *.
              unfold F, R in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
              pose proof Hb as HbindsTmp'.
              apply binds_reconstruct in Hb.
              destruct Hb as [l1 [l2 Hlist]].
              apply array_queue_wf_invarint in HreachTmp2.
              unfold array_queue_wf in HreachTmp2.
              simpl in HreachTmp2.
              rewrite Hlist in HreachTmp2.
              apply ok_remove_middle_inv in HreachTmp2.
              destruct HreachTmp2 as [Hokl [Hnt1 Hnt2]].
              rewrite Hlist.
              repeat rewrite get_f'_dist; auto.
              repeat rewrite get_r'_dist; auto.
              simpl.
              rewrite Nat.eqb_refl.
              simpl.
              rewrite get_r'_any_ary; auto.
              rewrite get_r'_any_ary; auto.
              rewrite get_f'_any_ary; auto.
              rewrite get_f'_any_ary; auto.
              rewrite Hlist in Hinv_range.
              repeat rewrite get_f'_dist in Hinv_range; auto.
              repeat rewrite get_r'_dist in Hinv_range; auto.
              simpl in Hinv_range.
              apply notin_get_none in Hnotin_res.
              rewrite Hnotin_res in Hinv_range.
              simpl in Hinv_range.
              unfold inv_d28_clean in Hinv_d28.
              simpl in Hinv_d28.
              unfold F, R in *; simpl in *.
              unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.

              destruct HreachTmp as [HreachTmp H8].
              apply entry_eqb_eq in Heq; auto.
              subst.

                  apply step_invariant in H8; auto.
                  unfold ComposedLTS.inv in H8.
                  simpl in H8.
                  apply H8 in Hbinds0.
                  destruct Hbinds0 as [s1 [s2 [q [acts [Hint_query [Hvalid Hgather]]]]]].
                  inversion Hint_query; subst; simpl in *.
                  inversion H5; subst; simpl in *.
                  unfold binds in HbindsTmp'.
                  inversion H7; subst; simpl in *.

  tmp'' noB_preserves_AEnq2 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq5 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq11 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq14 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq28 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_AEnq31 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq2 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq5 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq11 Hvalid st2 pid acts Hgather HbindsTmp'.
  tmp'' noB_preserves_ADeq14 Hvalid st2 pid acts Hgather HbindsTmp'.

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
  inversion H6; subst; simpl in *.
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
  assert (Htmp' : (Fin.of_nat_lt Hlt) =
    (Fin.of_nat_lt (mod_lt H (front pid)))).
  apply Fin.of_nat_ext.


              apply Hinv_d28 in HbindsTmp'; auto.
              rewrite Hlist in HbindsTmp'.
              repeat rewrite get_f'_dist in HbindsTmp'; auto.
              repeat rewrite get_r'_dist in HbindsTmp'; auto.
              simpl in HbindsTmp'.
              rewrite Hnotin_res in HbindsTmp'.
              simpl in HbindsTmp'.
              destruct HbindsTmp' as [Hb1 Hb2].
              repeat rewrite Nat.add_succ_r.

              rewrite Hlist in Hinv_6.
              repeat rewrite get_f'_dist in Hinv_6; auto.
              repeat rewrite get_r'_dist in Hinv_6; auto.
              simpl in Hinv_6.
              rewrite Hnotin_res in Hinv_6.
              simpl in Hinv_6.
              destruct Hinv_range as [Hinv_range1 Hinv_range2].

              intuition.
              (* apply all_some_S_r; simpl; auto.
              rewrite Htmp'.
              rewrite Hrear.
              rewrite Hb1.

              erewrite <-array_to_queue_replace_r; eauto.
              rewrite <-Hb1.
              rewrite Htmp'.
              rewrite <-Hrear.
              rewrite Vector.nth_replace_eq; auto.
              simpl. intuition. discriminate.
              simpl.
              rewrite array_to_queue_S_f in Hinv_range2; try lia. *)
              rewrite array_to_queue_S_f in Hinv_range1; try lia.
              apply all_some_dist_inv in Hinv_range1.
              intuition.
              rewrite Htmp'.
              rewrite Hrear.
              rewrite Hb1.
              rewrite <-array_to_queue_replace_f; auto.

              rewrite plus_Sn_m.
              apply all_none_S_r; simpl; auto.
              rewrite Htmp'.
              rewrite Hrear.
              rewrite Hb1.

              erewrite mod_L_eq_mod_lt_eq.
              erewrite <-array_to_queue_replace_r; eauto.
              rewrite <-Hb1.
              lia.
              assert (Htmp : L = 1 * L) by lia.
              rewrite Htmp at 2.
              rewrite Nat.Div0.mod_add.
              auto.
              rewrite <-Hb1.
              rewrite Htmp'.
              rewrite <-Hrear.
              erewrite mod_L_eq_mod_lt_eq.
              rewrite Vector.nth_replace_eq; auto.
              assert (Htmp : L = 1 * L) by lia.
              rewrite Htmp at 2.
              rewrite Nat.Div0.mod_add. auto.

              rewrite <-Hx.
              rewrite <-Hrear.
              rewrite <-Htmp'.
              auto.
  tmp'' noB_preserves_ADeq31 Hvalid st2 pid acts Hgather HbindsTmp'.
        (* fail *)
        +++ rewrite get_f'_any_ary_cas_false; auto.
          rewrite get_r'_any_ary_cas_false; auto.
      (* READ *)
      ++ rewrite get_f'_any_ary_read; auto.
        rewrite get_r'_any_ary_read; auto.
    -- inversion H3; subst; clear H3.
      unfold inv_total.
      intuition.
      (* inv_e28 *)
      --- unfold inv_e28_clean.
        intros.
        pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [Hinv_e28 _].
        destruct (eq_nat_dec pid0 pid).
        + subst.
          inversion H1; subst; simpl in *.
          inversion H3; subst; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          unfold binds in H0.
          inversion H4; subst; simpl in *;
          eapply substitute_eq_binds_v' in Hbinds0;
          rewrite Hbinds0 in H0; discriminate.
        + inversion H1; subst; simpl in *.
          inversion H3; subst; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          inversion H4; subst; simpl in *;
          apply substitute_neq_preserves_binds' in H0; auto;
          apply Hinv_e28 in H0; auto;
          unfold F, R in *; simpl in *;
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *;
          apply Nat.eqb_neq in n0; try rewrite n0 in *;
          apply H0 in H2;
          apply binds_reconstruct in Hbinds0;
          destruct Hbinds0 as [l1 [l2 Hlist]];
          rewrite Hlist in H2;
          repeat rewrite get_r'_dist in H2; auto;
          repeat rewrite get_f'_dist in H2; auto;
          destruct H2 as [H21 H22];
          rewrite H21;
          apply reachable_len_to_reachable in HreachTmp;
          apply array_queue_wf_invarint in HreachTmp;
          unfold array_queue_wf in HreachTmp;
          simpl in HreachTmp;
          rewrite Hlist in HreachTmp;
          apply ok_remove_middle_inv in HreachTmp;
          destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
          rewrite Hlist;
          rewrite substitute_notin_app; auto;
          repeat rewrite get_r'_dist; auto;
          repeat rewrite get_f'_dist; auto;
          simpl;
          rewrite Nat.eqb_refl;
          simpl;
          intuition.
      (* inv_d28 *)
      --- unfold inv_d28_clean.
        intros.
        pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [Hinv_e28 _]].
        destruct (eq_nat_dec pid0 pid).
        + subst.
          inversion H1; subst; simpl in *.
          inversion H3; subst; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          unfold binds in H0.
          inversion H4; subst; simpl in *;
          eapply substitute_eq_binds_v' in Hbinds0;
          rewrite Hbinds0 in H0; discriminate.
        + inversion H1; subst; simpl in *.
          inversion H3; subst; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          inversion H4; subst; simpl in *;
          apply substitute_neq_preserves_binds' in H0; auto;
          apply Hinv_e28 in H0; auto;
          unfold F, R in *; simpl in *;
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *;
          apply Nat.eqb_neq in n0; try rewrite n0 in *;
          apply H0 in H2;
          apply binds_reconstruct in Hbinds0;
          destruct Hbinds0 as [l1 [l2 Hlist]];
          rewrite Hlist in H2;
          repeat rewrite get_r'_dist in H2; auto;
          repeat rewrite get_f'_dist in H2; auto;
          destruct H2 as [H21 H22];
          rewrite H21;
          apply reachable_len_to_reachable in HreachTmp;
          apply array_queue_wf_invarint in HreachTmp;
          unfold array_queue_wf in HreachTmp;
          simpl in HreachTmp;
          rewrite Hlist in HreachTmp;
          apply ok_remove_middle_inv in HreachTmp;
          destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
          rewrite Hlist;
          rewrite substitute_notin_app; auto;
          repeat rewrite get_r'_dist; auto;
          repeat rewrite get_f'_dist; auto;
          simpl;
          rewrite Nat.eqb_refl;
          simpl;
          intuition.
      (* inv_1 *)
      --- unfold inv_1.
        pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [Hinv_1 _]]].
          inversion H1; subst; simpl in *.
          inversion H0; subst; simpl in *.
          unfold inv_1 in *; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          inversion H2; subst; simpl in *.

          all : pose proof Hbinds0 as HbindsTmp;
          apply binds_reconstruct in Hbinds0;
          destruct Hbinds0 as [l1 [l2 Hlist]];
          rewrite Hlist in Hinv_1 at 1 2;
          repeat rewrite get_r'_dist in Hinv_1; auto;
          repeat rewrite get_f'_dist in Hinv_1; auto;
          simpl in Hinv_1;
          apply reachable_len_to_reachable in HreachTmp;
          apply array_queue_wf_invarint in HreachTmp;
          unfold array_queue_wf in HreachTmp;
          simpl in HreachTmp;
          rewrite Hlist in HreachTmp;
          apply ok_remove_middle_inv in HreachTmp;
          destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
          rewrite Hlist at 1 2;
          rewrite substitute_notin_app; auto;
          repeat rewrite get_r'_dist; auto;
          repeat rewrite get_f'_dist; auto;
          simpl;
          rewrite Nat.eqb_refl;
          simpl in *;
          intuition.
          all : try (destruct H6 as [pid0 [Hpid1 Hpid2]];
          exists pid0;
          intuition;
          try (destruct (eq_nat_dec pid pid0);
          try (apply enq_not_inc_subst_neq; auto);
          subst pid;
          exfalso;
          eapply enq_not_inc_normal_false; eauto; solve_normal);
          (* apply enq_not_inc_subst_neq; auto. *)
          apply Hpid2 in H5; auto;
          destruct (eq_nat_dec pid pid');
          [subst pid;
          exfalso;
          eapply enq_not_inc_subst_normal_false in H6; eauto; solve_normal|
          eapply enq_not_inc_subst_neq_inv; eauto
          ]).

          all : try (destruct H7 as [pid0 [Hpid1 Hpid2]];
          exists pid0;
          intuition;
          try (destruct (eq_nat_dec pid pid0);
          try (apply enq_not_inc_subst_neq; auto);
          subst pid;
          exfalso;
          eapply enq_not_inc_normal_false; eauto; solve_normal);
          apply Hpid2 in H6; auto;
          destruct (eq_nat_dec pid pid');
          [subst pid;
          exfalso;
          eapply enq_not_inc_subst_normal_false in H7; eauto; solve_normal|
          eapply enq_not_inc_subst_neq_inv; eauto
          ]).

          exists pid.
          destruct H6 as [pid0 [Hpid1 Hpid2]].
          destruct (eq_nat_dec pid pid0).
          subst pid. intuition.
          unfold enq_not_inc.
          right. right. left.
          eapply substitute_eq_binds_v'; eauto.
          apply Hpid2 in H5; auto.
          apply enq_not_inc_subst_neq_inv in H6; auto.
          intuition.
          unfold enq_not_inc.
          right. right. left.
          eapply substitute_eq_binds_v'; eauto.
          apply Hpid2 in n0; auto.
          unfold enq_not_inc. intuition.
      --- unfold inv_1'.
        pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [Hinv_1 _]]]].
          inversion H1; subst; simpl in *.
          inversion H0; subst; simpl in *.
          unfold inv_1' in *; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          inversion H2; subst; simpl in *.

          all : pose proof Hbinds0 as HbindsTmp;
          apply binds_reconstruct in Hbinds0;
          destruct Hbinds0 as [l1 [l2 Hlist]];
          rewrite Hlist in Hinv_1 at 1 2;
          repeat rewrite get_r'_dist in Hinv_1; auto;
          repeat rewrite get_f'_dist in Hinv_1; auto;
          simpl in Hinv_1;
          apply reachable_len_to_reachable in HreachTmp;
          apply array_queue_wf_invarint in HreachTmp;
          unfold array_queue_wf in HreachTmp;
          simpl in HreachTmp;
          rewrite Hlist in HreachTmp;
          apply ok_remove_middle_inv in HreachTmp;
          destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
          rewrite Hlist at 1 2;
          rewrite substitute_notin_app; auto;
          repeat rewrite get_r'_dist; auto;
          repeat rewrite get_f'_dist; auto;
          simpl;
          rewrite Nat.eqb_refl;
          simpl in *;
          intuition.
          all : try (destruct H6 as [pid0 [Hpid1 Hpid2]];
          exists pid0;
          intuition;
          try (destruct (eq_nat_dec pid pid0);
          try (apply deq_not_inc_subst_neq; auto);
          subst pid;
          exfalso;
          eapply deq_not_inc_normal_false; eauto; solve_normal);
          (* apply enq_not_inc_subst_neq; auto. *)
          apply Hpid2 in H5; auto;
          destruct (eq_nat_dec pid pid');
          [subst pid;
          exfalso;
          eapply deq_not_inc_subst_normal_false in H6; eauto; solve_normal|
          eapply deq_not_inc_subst_neq_inv; eauto
          ]).

          all : try (destruct H7 as [pid0 [Hpid1 Hpid2]];
          exists pid0;
          intuition;
          try (destruct (eq_nat_dec pid pid0);
          try (apply deq_not_inc_subst_neq; auto);
          subst pid;
          exfalso;
          eapply deq_not_inc_normal_false; eauto; solve_normal);
          apply Hpid2 in H6; auto;
          destruct (eq_nat_dec pid pid');
          [subst pid;
          exfalso;
          eapply deq_not_inc_subst_normal_false in H7; eauto; solve_normal|
          eapply deq_not_inc_subst_neq_inv; eauto
          ]).

          exists pid.
          destruct H6 as [pid0 [Hpid1 Hpid2]].
          destruct (eq_nat_dec pid pid0).
          subst pid. intuition.
          unfold deq_not_inc.
          right. right. left.
          eapply substitute_eq_binds_v'; eauto.
          apply Hpid2 in H5; auto.
          apply deq_not_inc_subst_neq_inv in H6; auto.
          intuition.
          unfold deq_not_inc.
          right. right. left.
          eapply substitute_eq_binds_v'; eauto.
          apply Hpid2 in n0; auto.
          unfold deq_not_inc. intuition.
      (* inv_2 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [Hinv_2 _]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_2; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H2; subst; simpl in *;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        unfold inv_2 in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_2;
        repeat rewrite get_r'_dist in Hinv_2; auto;
        repeat rewrite get_f'_dist in Hinv_2; auto;
        simpl in Hinv_2;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.
      (* inv_2' *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [Hinv_2 _]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_2'; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H2; subst; simpl in *;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        unfold inv_2' in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_2;
        repeat rewrite get_r'_dist in Hinv_2; auto;
        repeat rewrite get_f'_dist in Hinv_2; auto;
        simpl in Hinv_2;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.
      (* inv_3 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [Hinv_3 _]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_3; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        intros pid0 Henq.

        inversion H2; subst; simpl in *.

        all : pose proof Hbinds0 as HbindsTmp;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];

        unfold inv_3 in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_3;
        repeat rewrite get_r'_dist in Hinv_3; auto;
        repeat rewrite get_f'_dist in Hinv_3; auto;
        simpl in Hinv_3;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.
        all : try (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        exfalso;
        eapply enq_not_inc_subst_normal_false; eauto; solve_normal);
        apply enq_not_inc_subst_neq_inv in Henq; auto;
        rewrite <-Hlist in Hinv_3;
        apply Hinv_3 in Henq; auto).
        rewrite <-Hlist in Hinv_3.
        apply Hinv_3 with (pid:=pid); eauto.
        unfold enq_not_inc. intuition.

      (* inv_3' *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [Hinv_3 _]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_3'; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        intros pid0 Henq.

        inversion H2; subst; simpl in *.

        all : pose proof Hbinds0 as HbindsTmp;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];

        unfold inv_3' in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_3;
        repeat rewrite get_r'_dist in Hinv_3; auto;
        repeat rewrite get_f'_dist in Hinv_3; auto;
        simpl in Hinv_3;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.
        all : try (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        exfalso;
        eapply deq_not_inc_subst_normal_false; eauto; solve_normal);
        apply deq_not_inc_subst_neq_inv in Henq; auto;
        rewrite <-Hlist in Hinv_3;
        apply Hinv_3 in Henq; auto).
        rewrite <-Hlist in Hinv_3.
        apply Hinv_3 with (pid:=pid); eauto.
        unfold deq_not_inc. intuition.
      (* inv_4 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_4 _]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_4; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        (* intros pid0 Henq. *)

        inversion H2; subst; simpl in *.

        all : pose proof Hbinds0 as HbindsTmp;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];

        unfold inv_4 in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_4;
        repeat rewrite get_r'_dist in Hinv_4; auto;
        repeat rewrite get_f'_dist in Hinv_4; auto;
        simpl in Hinv_4;
        rewrite Hlist at 1;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        rewrite <-Hlist in Hinv_4;
        simpl; intuition.
        all : try (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        eapply enq_not_inc_subst_normal_false; eauto; solve_normal);
        try (eapply enq_not_inc_subst_neq_inv in H5);
        try (eapply enq_not_inc_subst_neq_inv in H6);
        eauto).
        exfalso.
        specialize (H4 pid0).
        unfold enq_not_inc in H4. intuition.
        exfalso.
        specialize (H4 pid0).
        unfold enq_not_inc in H4. intuition.
      (* inv_4' *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_4 _]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_4'; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        (* intros pid0 Henq. *)

        inversion H2; subst; simpl in *.

        all : pose proof Hbinds0 as HbindsTmp;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];

        unfold inv_4' in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_4;
        repeat rewrite get_r'_dist in Hinv_4; auto;
        repeat rewrite get_f'_dist in Hinv_4; auto;
        simpl in Hinv_4;
        rewrite Hlist at 1;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        rewrite <-Hlist in Hinv_4;
        simpl; intuition.
        all : try (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        eapply deq_not_inc_subst_normal_false; eauto; solve_normal);
        try (eapply deq_not_inc_subst_neq_inv in H5);
        try (eapply deq_not_inc_subst_neq_inv in H6);
        eauto).
        exfalso.
        specialize (H4 pid0).
        unfold deq_not_inc in H4. intuition.
        exfalso.
        specialize (H4 pid0).
        unfold deq_not_inc in H4. intuition.
      (* inv_5 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_5 _]]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_5; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        intros pid0 Henq.

        inversion H2; subst; simpl in *.

        all : pose proof Hbinds0 as HbindsTmp;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];

        unfold inv_5 in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_5;
        repeat rewrite get_r'_dist in Hinv_5; auto;
        repeat rewrite get_f'_dist in Hinv_5; auto;
        simpl in Hinv_5;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.

        all : try (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        exfalso;
        eapply enq_not_inc_subst_normal_false; eauto; solve_normal);
        apply enq_not_inc_subst_neq_inv in Henq; auto;
        rewrite <-Hlist in Hinv_5;
        apply Hinv_5 in Henq; auto).
        rewrite <-Hlist in Hinv_5.
        apply Hinv_5 with (pid:=pid); eauto.
        unfold enq_not_inc. intuition.

      (* inv_5' *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_5 _]]]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_5'; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        intros pid0 Henq.

        inversion H2; subst; simpl in *.

        all : pose proof Hbinds0 as HbindsTmp;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];

        unfold inv_5' in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_5;
        repeat rewrite get_r'_dist in Hinv_5; auto;
        repeat rewrite get_f'_dist in Hinv_5; auto;
        simpl in Hinv_5;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.

        all : try (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        exfalso;
        eapply deq_not_inc_subst_normal_false; eauto; solve_normal);
        apply deq_not_inc_subst_neq_inv in Henq; auto;
        rewrite <-Hlist in Hinv_5;
        apply Hinv_5 in Henq; auto).
        rewrite <-Hlist in Hinv_5.
        apply Hinv_5 with (pid:=pid); eauto.
        unfold deq_not_inc. intuition.
      (* inv_6 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_6 _]]]]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_6; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H2; subst; simpl in *;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        unfold inv_6 in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_6;
        repeat rewrite get_r'_dist in Hinv_6; auto;
        repeat rewrite get_f'_dist in Hinv_6; auto;
        simpl in Hinv_6;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.
      (* inv_range *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hinv_range]]]]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_range; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H2; subst; simpl in *;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        unfold inv_range in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_range;
        repeat rewrite get_r'_dist in Hinv_range; auto;
        repeat rewrite get_f'_dist in Hinv_range; auto;
        simpl in Hinv_range;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.
    -- inversion H1.
    -- inversion H1.
    -- inversion H3; subst; clear H3.
      unfold inv_total.
      intuition.
      (* inv_e28 *)
      --- unfold inv_e28_clean.
        intros.
        pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [Hinv_e28 _].
        destruct (eq_nat_dec pid0 pid).
        + subst.
          inversion H1; subst; simpl in *.
          inversion H3; subst; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          unfold binds in H0.
          inversion H4; subst; simpl in *;
          rewrite Nat.eqb_refl in H0;
          discriminate.
        + inversion H1; subst; simpl in *.
          inversion H3; subst; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          inversion H4; subst; simpl in *;
          apply binds_push_neq_inv in H0; auto;
          apply Hinv_e28 in H0; auto;
          unfold F, R in *; simpl in *;
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *;
          apply Nat.eqb_neq in n; try rewrite n in *;
          apply H0 in H2;
          apply binds_reconstruct in Hbinds0;
          destruct Hbinds0 as [l1 [l2 Hlist]];
          rewrite Hlist in H2;
          repeat rewrite get_r'_dist in H2; auto;
          repeat rewrite get_f'_dist in H2; auto;
          destruct H2 as [H21 H22];
          rewrite H21;
          apply reachable_len_to_reachable in HreachTmp;
          apply array_queue_wf_invarint in HreachTmp;
          unfold array_queue_wf in HreachTmp;
          simpl in HreachTmp;
          rewrite Hlist in HreachTmp;
          apply ok_remove_middle_inv in HreachTmp;
          destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
          rewrite Hlist;
          rewrite substitute_notin_app; auto;
          repeat rewrite get_r'_dist; auto;
          repeat rewrite get_f'_dist; auto;
          simpl;
          rewrite Nat.eqb_refl;
          simpl;
          intuition.
      (* inv_d28 *)
      --- unfold inv_d28_clean.
        intros.
        pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [Hinv_e28 _]].
        destruct (eq_nat_dec pid0 pid).
        + subst.
          inversion H1; subst; simpl in *.
          inversion H3; subst; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          unfold binds in H0.
          inversion H4; subst; simpl in *;
          rewrite Nat.eqb_refl in H0;
          discriminate.
        + inversion H1; subst; simpl in *.
          inversion H3; subst; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          inversion H4; subst; simpl in *;
          apply binds_push_neq_inv in H0; auto;
          apply Hinv_e28 in H0; auto;
          unfold F, R in *; simpl in *;
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *;
          apply Nat.eqb_neq in n; try rewrite n in *;
          apply H0 in H2;
          apply binds_reconstruct in Hbinds0;
          destruct Hbinds0 as [l1 [l2 Hlist]];
          rewrite Hlist in H2;
          repeat rewrite get_r'_dist in H2; auto;
          repeat rewrite get_f'_dist in H2; auto;
          destruct H2 as [H21 H22];
          rewrite H21;
          apply reachable_len_to_reachable in HreachTmp;
          apply array_queue_wf_invarint in HreachTmp;
          unfold array_queue_wf in HreachTmp;
          simpl in HreachTmp;
          rewrite Hlist in HreachTmp;
          apply ok_remove_middle_inv in HreachTmp;
          destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
          rewrite Hlist;
          rewrite substitute_notin_app; auto;
          repeat rewrite get_r'_dist; auto;
          repeat rewrite get_f'_dist; auto;
          simpl;
          rewrite Nat.eqb_refl;
          simpl;
          intuition.
      (* inv_1 *)
      --- unfold inv_1.
        pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [Hinv_1 _]]].
          inversion H1; subst; simpl in *.
          inversion H0; subst; simpl in *.
          unfold inv_1 in *; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          inversion H2; subst; simpl in *.
          intros. intuition.
          destruct H6 as [pid0 [Hpid1 Hpid2]].

          exists pid0.
          intuition.
          destruct (eq_nat_dec pid pid0).
          subst.
          unfold enq_not_inc in Hpid1.
          unfold binds in Hpid1.
          apply notin_get_none in Hnotin_pc.
          rewrite Hnotin_pc in Hpid1. intuition; discriminate.
          try (apply enq_not_inc_push_neq; auto).
          apply Hpid2 in H5; auto.
          destruct (eq_nat_dec pid' pid).
          subst. unfold enq_not_inc in H6.
          simpl in H6.
          intuition.
          apply binds_push_eq_inv in H6; intuition; discriminate.
          apply binds_push_eq_inv in H6; intuition; discriminate.
          apply binds_push_eq_inv in H7; intuition; discriminate.
          apply binds_push_eq_inv in H6; intuition; discriminate.
          apply enq_not_inc_push_neq_inv in H6; auto.

          intros. intuition.
          destruct H6 as [pid0 [Hpid1 Hpid2]].
          exists pid0.
          intuition.
          destruct (eq_nat_dec pid pid0).
          subst.
          unfold enq_not_inc in Hpid1.
          unfold binds in Hpid1.
          apply notin_get_none in Hnotin_pc.
          rewrite Hnotin_pc in Hpid1. intuition; discriminate.
          try (apply enq_not_inc_push_neq; auto).
          apply Hpid2 in H5; auto.
          destruct (eq_nat_dec pid' pid).
          subst. unfold enq_not_inc in H6.
          simpl in H6.
          intuition.
          apply binds_push_eq_inv in H6; intuition; discriminate.
          apply binds_push_eq_inv in H6; intuition; discriminate.
          apply binds_push_eq_inv in H7; intuition; discriminate.
          apply binds_push_eq_inv in H6; intuition; discriminate.
          apply enq_not_inc_push_neq_inv in H6; auto.
      (* inv_1' *)
      --- unfold inv_1'.
        pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [Hinv_1 _]]]].
          inversion H1; subst; simpl in *.
          inversion H0; subst; simpl in *.
          unfold inv_1' in *; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          inversion H2; subst; simpl in *.
          intros. intuition.
          destruct H6 as [pid0 [Hpid1 Hpid2]].

          exists pid0.
          intuition.
          destruct (eq_nat_dec pid pid0).
          subst.
          unfold deq_not_inc in Hpid1.
          unfold binds in Hpid1.
          apply notin_get_none in Hnotin_pc.
          rewrite Hnotin_pc in Hpid1. intuition; discriminate.
          try (apply deq_not_inc_push_neq; auto).
          apply Hpid2 in H5; auto.
          destruct (eq_nat_dec pid' pid).
          subst. unfold deq_not_inc in H6.
          simpl in H6.
          intuition.
          apply binds_push_eq_inv in H6; intuition; discriminate.
          apply binds_push_eq_inv in H6; intuition; discriminate.
          apply binds_push_eq_inv in H7; intuition; discriminate.
          apply binds_push_eq_inv in H6; intuition; discriminate.
          apply deq_not_inc_push_neq_inv in H6; auto.

          intros. intuition.
          destruct H6 as [pid0 [Hpid1 Hpid2]].
          exists pid0.
          intuition.
          destruct (eq_nat_dec pid pid0).
          subst.
          unfold deq_not_inc in Hpid1.
          unfold binds in Hpid1.
          apply notin_get_none in Hnotin_pc.
          rewrite Hnotin_pc in Hpid1. intuition; discriminate.
          try (apply deq_not_inc_push_neq; auto).
          apply Hpid2 in H5; auto.
          destruct (eq_nat_dec pid' pid).
          subst. unfold deq_not_inc in H6.
          simpl in H6.
          intuition.
          apply binds_push_eq_inv in H6; intuition; discriminate.
          apply binds_push_eq_inv in H6; intuition; discriminate.
          apply binds_push_eq_inv in H7; intuition; discriminate.
          apply binds_push_eq_inv in H6; intuition; discriminate.
          apply deq_not_inc_push_neq_inv in H6; auto.
      (* inv_2 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [Hinv_2 _]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_2; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H2; subst; simpl in *;
        intuition.
      (* inv_2' *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [Hinv_2 _]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_2'; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H2; subst; simpl in *;
        intuition.
      (* inv_3 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [Hinv_3 _]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_3; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        intros pid0 Henq.

        inversion H2; subst; simpl in *.
        destruct (eq_nat_dec pid pid0).
        try (subst;
        unfold enq_not_inc in Henq;
        apply notin_get_none in Hnotin_pc;
        intuition;
        try (apply binds_push_eq_inv in H4; auto; discriminate);
        try (apply binds_push_eq_inv in H3; auto; discriminate)).
        apply enq_not_inc_push_neq_inv in Henq; auto;
        apply Hinv_3 in Henq; auto.
        destruct (eq_nat_dec pid pid0).
        try (subst;
        unfold enq_not_inc in Henq;
        apply notin_get_none in Hnotin_pc;
        intuition;
        try (apply binds_push_eq_inv in H4; auto; discriminate);
        try (apply binds_push_eq_inv in H3; auto; discriminate)).
        apply enq_not_inc_push_neq_inv in Henq; auto;
        apply Hinv_3 in Henq; auto.
      (* inv_3' *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [Hinv_3 _]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_3'; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        intros pid0 Henq.

        inversion H2; subst; simpl in *.
        destruct (eq_nat_dec pid pid0).
        try (subst;
        unfold deq_not_inc in Henq;
        apply notin_get_none in Hnotin_pc;
        intuition;
        try (apply binds_push_eq_inv in H4; auto; discriminate);
        try (apply binds_push_eq_inv in H3; auto; discriminate)).
        apply deq_not_inc_push_neq_inv in Henq; auto;
        apply Hinv_3 in Henq; auto.
        destruct (eq_nat_dec pid pid0).
        try (subst;
        unfold deq_not_inc in Henq;
        apply notin_get_none in Hnotin_pc;
        intuition;
        try (apply binds_push_eq_inv in H4; auto; discriminate);
        try (apply binds_push_eq_inv in H3; auto; discriminate)).
        apply deq_not_inc_push_neq_inv in Henq; auto;
        apply Hinv_3 in Henq; auto.

      (* inv_4 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_4 _]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_4; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H2; subst; simpl in *.
        all :
        unfold inv_4 in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        simpl; intuition.
        destruct (eq_nat_dec pid pid0).
        subst;
        unfold enq_not_inc in H5;
        intuition;
        try (apply binds_push_eq_inv in H6; auto; discriminate);
        try (apply binds_push_eq_inv in H5; auto; discriminate).
        apply enq_not_inc_push_neq_inv in H5; auto;
        apply H4 in H5; auto.
        destruct (eq_nat_dec pid pid0).
        subst;
        unfold enq_not_inc in H5;
        intuition;
        try (apply binds_push_eq_inv in H6; auto; discriminate);
        try (apply binds_push_eq_inv in H5; auto; discriminate).
        apply enq_not_inc_push_neq_inv in H5; auto;
        apply H4 in H5; auto.

      (* inv_4' *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_4 _]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_4'; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H2; subst; simpl in *.
        all :
        unfold inv_4' in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        simpl; intuition.
        destruct (eq_nat_dec pid pid0).
        subst;
        unfold deq_not_inc in H5;
        intuition;
        try (apply binds_push_eq_inv in H6; auto; discriminate);
        try (apply binds_push_eq_inv in H5; auto; discriminate).
        apply deq_not_inc_push_neq_inv in H5; auto;
        apply H4 in H5; auto.
        destruct (eq_nat_dec pid pid0).
        subst;
        unfold deq_not_inc in H5;
        intuition;
        try (apply binds_push_eq_inv in H6; auto; discriminate);
        try (apply binds_push_eq_inv in H5; auto; discriminate).
        apply deq_not_inc_push_neq_inv in H5; auto;
        apply H4 in H5; auto.
      (* inv_5 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_5 _]]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_5; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        intros pid0 Henq.

        inversion H2; subst; simpl in *.
        destruct (eq_nat_dec pid pid0).
        try (subst;
        unfold enq_not_inc in Henq;
        apply notin_get_none in Hnotin_pc;
        intuition;
        try (apply binds_push_eq_inv in H4; auto; discriminate);
        try (apply binds_push_eq_inv in H3; auto; discriminate)).
        apply enq_not_inc_push_neq_inv in Henq; auto;
        apply Hinv_5 in Henq; auto.
        destruct (eq_nat_dec pid pid0).
        try (subst;
        unfold enq_not_inc in Henq;
        apply notin_get_none in Hnotin_pc;
        intuition;
        try (apply binds_push_eq_inv in H4; auto; discriminate);
        try (apply binds_push_eq_inv in H3; auto; discriminate)).
        apply enq_not_inc_push_neq_inv in Henq; auto;
        apply Hinv_5 in Henq; auto.
      (* inv_5' *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_5 _]]]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_5'; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        intros pid0 Henq.

        inversion H2; subst; simpl in *.
        destruct (eq_nat_dec pid pid0).
        try (subst;
        unfold deq_not_inc in Henq;
        apply notin_get_none in Hnotin_pc;
        intuition;
        try (apply binds_push_eq_inv in H4; auto; discriminate);
        try (apply binds_push_eq_inv in H3; auto; discriminate)).
        apply deq_not_inc_push_neq_inv in Henq; auto;
        apply Hinv_5 in Henq; auto.
        destruct (eq_nat_dec pid pid0).
        try (subst;
        unfold deq_not_inc in Henq;
        apply notin_get_none in Hnotin_pc;
        intuition;
        try (apply binds_push_eq_inv in H4; auto; discriminate);
        try (apply binds_push_eq_inv in H3; auto; discriminate)).
        apply deq_not_inc_push_neq_inv in Henq; auto;
        apply Hinv_5 in Henq; auto.
      (* inv_6 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_6 _]]]]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_6; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H2; subst; simpl in *;
        unfold inv_6 in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        simpl; intuition.
      (* inv_range *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hinv_range]]]]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_range; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H2; subst; simpl in *;
        unfold inv_range in *; simpl in *;
        simpl; intuition.
    -- inversion H3; subst; clear H3.
      unfold inv_total.
      intuition.
      (* inv_e28 *)
      --- unfold inv_e28_clean.
        intros.
        pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [Hinv_e28 _].
        destruct (eq_nat_dec pid0 pid).
        + subst.
          inversion H1; subst; simpl in *.
          inversion H3; subst; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          apply binds_in in H0.
          inversion H4; subst; simpl in *;
          assert (Htmp : pid # (remove pc pid)) by
          (apply ok_remove_notin; auto);
          unfold "#" in Htmp; intuition.
        + inversion H1; subst; simpl in *.
          inversion H3; subst; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          inversion H4; subst; simpl in *;
          apply remove_preserves_binds_notin in H0; auto;
          apply Hinv_e28 in H0; auto;
          unfold F, R in *; simpl in *;
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *;
          apply Nat.eqb_neq in n0; try rewrite n0 in *;
          apply H0 in H2;
          apply binds_reconstruct in Hbinds0;
          destruct Hbinds0 as [l1 [l2 Hlist]];
          rewrite Hlist in H2;
          repeat rewrite get_r'_dist in H2; auto;
          repeat rewrite get_f'_dist in H2; auto;
          destruct H2 as [H21 H22];
          rewrite H21;
          apply reachable_len_to_reachable in HreachTmp;
          apply array_queue_wf_invarint in HreachTmp;
          unfold array_queue_wf in HreachTmp;
          simpl in HreachTmp;
          rewrite Hlist in HreachTmp;
          apply ok_remove_middle_inv in HreachTmp;
          destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
          rewrite Hlist;
          rewrite remove_notin_app; auto;
          repeat rewrite get_r'_dist; auto;
          repeat rewrite get_f'_dist; auto;
          simpl;
          rewrite Nat.eqb_refl;
          simpl;
          intuition.
      (* inv_d28 *)
      --- unfold inv_d28_clean.
        intros.
        pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [Hinv_e28 _]].
        destruct (eq_nat_dec pid0 pid).
        + subst.
          inversion H1; subst; simpl in *.
          inversion H3; subst; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          apply binds_in in H0.
          inversion H4; subst; simpl in *;
          assert (Htmp : pid # (remove pc pid)) by
          (apply ok_remove_notin; auto);
          unfold "#" in Htmp; intuition.
        + inversion H1; subst; simpl in *.
          inversion H3; subst; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          inversion H4; subst; simpl in *;
          apply remove_preserves_binds_notin in H0; auto;
          apply Hinv_e28 in H0; auto;
          unfold F, R in *; simpl in *;
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *;
          apply Nat.eqb_neq in n0; try rewrite n0 in *;
          apply H0 in H2;
          apply binds_reconstruct in Hbinds0;
          destruct Hbinds0 as [l1 [l2 Hlist]];
          rewrite Hlist in H2;
          repeat rewrite get_r'_dist in H2; auto;
          repeat rewrite get_f'_dist in H2; auto;
          destruct H2 as [H21 H22];
          rewrite H21;
          apply reachable_len_to_reachable in HreachTmp;
          apply array_queue_wf_invarint in HreachTmp;
          unfold array_queue_wf in HreachTmp;
          simpl in HreachTmp;
          rewrite Hlist in HreachTmp;
          apply ok_remove_middle_inv in HreachTmp;
          destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
          rewrite Hlist;
          rewrite remove_notin_app; auto;
          repeat rewrite get_r'_dist; auto;
          repeat rewrite get_f'_dist; auto;
          simpl;
          rewrite Nat.eqb_refl;
          simpl;
          intuition.

      (* inv_1 *)
      --- unfold inv_1.
        pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [Hinv_1 _]]].
          inversion H1; subst; simpl in *.
          inversion H0; subst; simpl in *.
          unfold inv_1 in *; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          inversion H2; subst; simpl in *.

          all : pose proof Hbinds0 as HbindsTmp;
          apply binds_reconstruct in Hbinds0;
          destruct Hbinds0 as [l1 [l2 Hlist]];
          rewrite Hlist in Hinv_1 at 1 2;
          repeat rewrite get_r'_dist in Hinv_1; auto;
          repeat rewrite get_f'_dist in Hinv_1; auto;
          simpl in Hinv_1;
          apply reachable_len_to_reachable in HreachTmp;
          apply array_queue_wf_invarint in HreachTmp;
          unfold array_queue_wf in HreachTmp;
          simpl in HreachTmp;
          rewrite Hlist in HreachTmp;
          apply ok_remove_middle_inv in HreachTmp;
          destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
          rewrite Hlist at 1 2;
          rewrite remove_notin_app; auto;
          repeat rewrite get_r'_dist; auto;
          repeat rewrite get_f'_dist; auto;
          simpl;
          rewrite Nat.eqb_refl;
          simpl in *;
          intuition.
          destruct H6 as [pid0 [Hpid1 Hpid2]];
          exists pid0.
          intuition.
          destruct (eq_nat_dec pid pid0).
          subst pid;
          exfalso;
          unfold enq_not_inc in Hpid1;
          unfold binds in Hpid1;
          rewrite HbindsTmp in Hpid1;
          intuition; discriminate.
          eapply enq_not_inc_remove_neq; eauto.
          apply Hpid2 in H5; auto;
          destruct (eq_nat_dec pid pid');
          [subst pid;
          exfalso;
          eapply enq_not_inc_remove_eq_false in H6; eauto; solve_normal|
          eapply enq_not_inc_remove_neq_inv; eauto
          ].

          destruct H7 as [pid0 [Hpid1 Hpid2]];
          exists pid0.
          intuition.
          destruct (eq_nat_dec pid pid0).
          subst pid;
          exfalso;
          unfold enq_not_inc in Hpid1;
          unfold binds in Hpid1;
          rewrite HbindsTmp in Hpid1;
          intuition; discriminate.
          eapply enq_not_inc_remove_neq; eauto.
          apply Hpid2 in H6; auto;
          destruct (eq_nat_dec pid pid');
          [subst pid;
          exfalso;
          eapply enq_not_inc_remove_eq_false in H7; eauto; solve_normal|
          eapply enq_not_inc_remove_neq_inv; eauto
          ].
      (* inv_1' *)
      --- unfold inv_1'.
        pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [Hinv_1 _]]]].
          inversion H1; subst; simpl in *.
          inversion H0; subst; simpl in *.
          unfold inv_1' in *; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          inversion H2; subst; simpl in *.

          all : pose proof Hbinds0 as HbindsTmp;
          apply binds_reconstruct in Hbinds0;
          destruct Hbinds0 as [l1 [l2 Hlist]];
          rewrite Hlist in Hinv_1 at 1 2;
          repeat rewrite get_r'_dist in Hinv_1; auto;
          repeat rewrite get_f'_dist in Hinv_1; auto;
          simpl in Hinv_1;
          apply reachable_len_to_reachable in HreachTmp;
          apply array_queue_wf_invarint in HreachTmp;
          unfold array_queue_wf in HreachTmp;
          simpl in HreachTmp;
          rewrite Hlist in HreachTmp;
          apply ok_remove_middle_inv in HreachTmp;
          destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
          rewrite Hlist at 1 2;
          rewrite remove_notin_app; auto;
          repeat rewrite get_r'_dist; auto;
          repeat rewrite get_f'_dist; auto;
          simpl;
          rewrite Nat.eqb_refl;
          simpl in *;
          intuition.
          destruct H6 as [pid0 [Hpid1 Hpid2]];
          exists pid0.
          intuition.
          destruct (eq_nat_dec pid pid0).
          subst pid;
          exfalso;
          unfold deq_not_inc in Hpid1;
          unfold binds in Hpid1;
          rewrite HbindsTmp in Hpid1;
          intuition; discriminate.
          eapply deq_not_inc_remove_neq; eauto.
          apply Hpid2 in H5; auto;
          destruct (eq_nat_dec pid pid');
          [subst pid;
          exfalso;
          eapply deq_not_inc_remove_eq_false in H6; eauto; solve_normal|
          eapply deq_not_inc_remove_neq_inv; eauto
          ].

          destruct H7 as [pid0 [Hpid1 Hpid2]];
          exists pid0.
          intuition.
          destruct (eq_nat_dec pid pid0).
          subst pid;
          exfalso;
          unfold deq_not_inc in Hpid1;
          unfold binds in Hpid1;
          rewrite HbindsTmp in Hpid1;
          intuition; discriminate.
          eapply deq_not_inc_remove_neq; eauto.
          apply Hpid2 in H6; auto;
          destruct (eq_nat_dec pid pid');
          [subst pid;
          exfalso;
          eapply deq_not_inc_remove_eq_false in H7; eauto; solve_normal|
          eapply deq_not_inc_remove_neq_inv; eauto
          ].

      (* inv_2 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [Hinv_2 _]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_2; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H2; subst; simpl in *;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        unfold inv_2 in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_2;
        repeat rewrite get_r'_dist in Hinv_2; auto;
        repeat rewrite get_f'_dist in Hinv_2; auto;
        simpl in Hinv_2;
        rewrite Hlist;
        repeat rewrite remove_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.

      (* inv_2' *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [Hinv_2 _]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_2'; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H2; subst; simpl in *;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        unfold inv_2' in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_2;
        repeat rewrite get_r'_dist in Hinv_2; auto;
        repeat rewrite get_f'_dist in Hinv_2; auto;
        simpl in Hinv_2;
        rewrite Hlist;
        repeat rewrite remove_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.
      (* inv_3 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [Hinv_3 _]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_3; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        intros pid0 Henq.

        inversion H2; subst; simpl in *.

        all : pose proof Hbinds0 as HbindsTmp;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];

        unfold inv_3 in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_3;
        repeat rewrite get_r'_dist in Hinv_3; auto;
        repeat rewrite get_f'_dist in Hinv_3; auto;
        simpl in Hinv_3;
        rewrite Hlist;
        repeat rewrite remove_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.

        all : try (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        exfalso;
        eapply enq_not_inc_remove_eq_false; eauto; solve_normal);
        apply enq_not_inc_remove_neq_inv in Henq; auto;
        rewrite <-Hlist in Hinv_3;
        apply Hinv_3 in Henq; auto).

      (* inv_3' *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [Hinv_3 _]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_3'; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        intros pid0 Henq.

        inversion H2; subst; simpl in *.

        all : pose proof Hbinds0 as HbindsTmp;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];

        unfold inv_3' in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_3;
        repeat rewrite get_r'_dist in Hinv_3; auto;
        repeat rewrite get_f'_dist in Hinv_3; auto;
        simpl in Hinv_3;
        rewrite Hlist;
        repeat rewrite remove_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.

        all : (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        exfalso;
        eapply deq_not_inc_remove_eq_false; eauto; solve_normal);
        apply deq_not_inc_remove_neq_inv in Henq; auto;
        rewrite <-Hlist in Hinv_3;
        apply Hinv_3 in Henq; auto).
      (* inv_4 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_4 _]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_4; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        (* intros pid0 Henq. *)

        inversion H2; subst; simpl in *.

        all : pose proof Hbinds0 as HbindsTmp;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];

        unfold inv_4 in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_4;
        repeat rewrite get_r'_dist in Hinv_4; auto;
        repeat rewrite get_f'_dist in Hinv_4; auto;
        simpl in Hinv_4;
        rewrite Hlist at 1;
        repeat rewrite remove_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        rewrite <-Hlist in Hinv_4;
        simpl; intuition.
        all : try (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        eapply enq_not_inc_remove_eq_false; eauto; solve_normal);
        try (eapply enq_not_inc_remove_neq_inv in H5);
        try (eapply enq_not_inc_remove_neq_inv in H6);
        eauto).
      (* inv_4' *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_4 _]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_4'; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        (* intros pid0 Henq. *)

        inversion H2; subst; simpl in *.

        all : pose proof Hbinds0 as HbindsTmp;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];

        unfold inv_4' in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_4;
        repeat rewrite get_r'_dist in Hinv_4; auto;
        repeat rewrite get_f'_dist in Hinv_4; auto;
        simpl in Hinv_4;
        rewrite Hlist at 1;
        repeat rewrite remove_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        rewrite <-Hlist in Hinv_4;
        simpl; intuition.
        all : try (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        eapply deq_not_inc_remove_eq_false; eauto; solve_normal);
        try (eapply deq_not_inc_remove_neq_inv in H5);
        try (eapply deq_not_inc_remove_neq_inv in H6);
        eauto).
      (* inv_5 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_5 _]]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_5; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        intros pid0 Henq.

        inversion H2; subst; simpl in *.

        all : pose proof Hbinds0 as HbindsTmp;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];

        unfold inv_5 in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_5;
        repeat rewrite get_r'_dist in Hinv_5; auto;
        repeat rewrite get_f'_dist in Hinv_5; auto;
        simpl in Hinv_5;
        rewrite Hlist;
        repeat rewrite remove_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.

        all : try (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        exfalso;
        eapply enq_not_inc_remove_eq_false; eauto; solve_normal);
        apply enq_not_inc_remove_neq_inv in Henq; auto;
        rewrite <-Hlist in Hinv_5;
        apply Hinv_5 in Henq; auto).

      (* inv_5' *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_5 _]]]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_5'; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        intros pid0 Henq.

        inversion H2; subst; simpl in *.

        all : pose proof Hbinds0 as HbindsTmp;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];

        unfold inv_5' in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_5;
        repeat rewrite get_r'_dist in Hinv_5; auto;
        repeat rewrite get_f'_dist in Hinv_5; auto;
        simpl in Hinv_5;
        rewrite Hlist;
        repeat rewrite remove_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.

        all : try (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        exfalso;
        eapply deq_not_inc_remove_eq_false; eauto; solve_normal);
        apply deq_not_inc_remove_neq_inv in Henq; auto;
        rewrite <-Hlist in Hinv_5;
        apply Hinv_5 in Henq; auto).
      (* inv_6 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_6 _]]]]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_6; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H2; subst; simpl in *;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        unfold inv_6 in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_6;
        repeat rewrite get_r'_dist in Hinv_6; auto;
        repeat rewrite get_f'_dist in Hinv_6; auto;
        simpl in Hinv_6;
        rewrite Hlist;
        repeat rewrite remove_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.
      (* inv_range *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hinv_range]]]]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_range; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H2; subst; simpl in *;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        unfold inv_range in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_range;
        repeat rewrite get_r'_dist in Hinv_range; auto;
        repeat rewrite get_f'_dist in Hinv_range; auto;
        simpl in Hinv_range;
        rewrite Hlist;
        repeat rewrite remove_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.
    -- inversion H3; subst; clear H3.
      unfold inv_total.
      intuition.
      (* inv_e28 *)
      --- unfold inv_e28_clean.
        intros.
        pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [Hinv_e28 [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_6 Hinv_range']]]]]]]]]]]]].
        destruct (eq_nat_dec pid0 pid).
        + subst.
          inversion H1; subst; simpl in *.
          inversion H3; subst; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          unfold binds in H0.
          inversion H5; subst; simpl in *;
          pose proof Hbinds0 as Hbinds_e27;
          eapply substitute_eq_binds_v' in Hbinds0;
          rewrite Hbinds0 in H0; try discriminate.

          assert (Hrear_R :
rear pid =
value (LState (Tensor.L2State (LState (Tensor.L2State (LState st1'))))) +
get_r' (substitute pc pid AEnq28)
  (Array.responses L (LState (Tensor.L1State (LState st1'))))
  (Counter.responses
     (LState (Tensor.L2State (LState (Tensor.L2State (LState st1'))))))
          ).
          {

          clear Hinv_e28.
            pose proof HreachTmp as HreachTmp2.
            apply reachable_len_to_reachable in HreachTmp2.
            pose proof HreachTmp2 as HreachTmp3.
            apply inv_rear_invariant in HreachTmp2; auto.
            unfold inv_rear in HreachTmp2.
            simpl in HreachTmp2.
            destruct HreachTmp2 as [Hr21 Hr22].
            specialize (Hr21 pid).
            assert (Hrear_R : rear pid <=
  value
    (LState (Tensor.L2State (LState (Tensor.L2State (LState st1'))))) +
  get_r' (substitute pc pid AEnq28)
    (Array.responses L (LState (Tensor.L1State (LState st1'))))
    (Counter.responses
      (LState (Tensor.L2State (LState (Tensor.L2State (LState st1'))))))
            ).
            eapply Nat.le_trans; eauto.
            inversion H4; subst; simpl in *.
            inversion H6; subst; simpl in *.
            inversion H8; subst; simpl in *.
            inversion H7; subst; simpl in *.
            lia.
            inversion Hrear_R; subst. auto.
            (* < is impossible *)
            (* exfalso. *)
            apply inv_e27_from_e5_keeps_vec_rear_impl_rear_eq_rear_k_step with (pid:=pid) (H:=H) in HreachTmp; simpl; auto.
            destruct HreachTmp as [s1 [s2 [acts [ret [n' [t [Hvalid [Hstep_e5 [Hb_e5 [Hgather [Hreach_e5 [Hlt [Heq [Hb_ary_read [Hxp [Hvec_rear Hrear_keep]]]]]]]]]]]]]]]].
            simpl in *.
            unfold get_vec_rear in *; simpl in *.
            unfold get_ary in *; simpl in *.
            inversion H4; subst; simpl in *.
            inversion H8; subst; simpl in *.
            inversion H10; subst; simpl in *.
            inversion H9; subst; simpl in *.
            intuition.

            assert (Hreach_e5' : reachable_len' (composed_array_queue L) s2 (n' + 1)).
            eapply valid_execution_fragment_reach_len'; eauto.
            eapply Step_Internal_L1_len'; eauto.
            eapply Step_None_len'; eauto.
            pose proof Hreach_e5' as Hreach_e5''.
            apply IHk in Hreach_e5'; try lia.
            unfold inv_total in Hreach_e5'.
            destruct Hreach_e5' as [_ [_ [He5_inv_1 [_ [He5_inv_2 [_ [_ [_ [_ [_ [He5_inv_5 [_ [_ He5_inv_range]]]]]]]]]]]]].
            unfold inv_range in He5_inv_range.
            pose proof HreachTmp3 as HreachTmp4.
            apply inv_e27_x_none_invariant in HreachTmp3.
            unfold inv_e27_x_none in HreachTmp3.
            simpl in HreachTmp3.
            pose proof Hbinds_e27 as Hbinds_e27'.
            apply HreachTmp3 in Hbinds_e27.
            rewrite H2 in Hbinds_e27.
            rewrite H11 in Hbinds_e27.
            assert (Hrear_s2 : ArrayQueueImpl.rear (get_impl L s2) pid =
              value (get_rear L s2)).
              unfold get_impl, get_rear in *; simpl in *.
              inversion Hstep_e5; subst; simpl in *.
              inversion H12; subst; simpl in *.
              inversion H13; subst; simpl in *.
              inversion H15; subst; simpl in *.
              inversion H14; subst; simpl in *.
              auto.
            rewrite Hrear_s2 in Hbinds_e27.
            (* unfold inv_2 in He5_inv_2. *)
            
            assert (
              Haa : value
                (LState
                  (Tensor.L2State
                    (LState (Tensor.L2State (LState (L1State s2)))))) =
              R s2 -> False
            ). intros H16. intuition.

              unfold get_rear in *; simpl in *.
                rewrite <-Hrear_s2 in H16.
                unfold get_impl in *; simpl in *.
                unfold R in *; simpl in *.
                unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
                assert (Hrear_e5_e27 : (rear pid) = (ArrayQueueImpl.rear (LState (L2State s2)) pid)).
                apply valid_execution_fragment_len'_to_valid_execution_fragment in Hvalid; auto.

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

Ltac solve_after_e3 :=
  try apply after_e3_Enq4;
  try apply after_e3_Enq5;
  try apply after_e3_Enq6;
  try (unfold after_e6;
  right; right; right;
  solve_after_e6).

                eapply inv_impl_rear_keep'' with (v:=AEnq5) in Hvalid.
                unfold get_impl in *; simpl in *. eauto.
                solve_before_e27.
                solve_after_e3.
                unfold get_pc; simpl.
                inversion Hstep_e5; subst; simpl in *; auto.
                simpl; auto.
                unfold get_pc; simpl. auto.

                rewrite <-Hrear_e5_e27 in H16.
                assert (Hgt :
                  rear pid <
                  value (LState (Tensor.L2State (LState st2))) +
     get_r' (substitute pc pid AEnq28) res
       (Counter.responses (LState (Tensor.L2State (LState st2))))
                ) by lia.
                rewrite H16 in Hgt.
                generalize inv_R_increase_step_L1'; intros Hmiddle.
                unfold R in Hmiddle.
                unfold get_rear, get_ary, get_pc in Hmiddle; simpl in Hmiddle.
                specialize (Hmiddle L s2).
                apply Hmiddle in Hvalid; simpl; auto; try lia.
                2 : {
                  eapply reachable_len_to_reachable; eauto.
                }
                2 : {
                  eapply Nat.lt_le_trans; eauto.
                  apply binds_reconstruct in Hbinds_e27'.
                  destruct Hbinds_e27' as [l1 [l2 Hlist]].
                  apply array_queue_wf_invarint in HreachTmp4.
                  unfold array_queue_wf in HreachTmp4.
                  simpl in HreachTmp4.
                  rewrite Hlist in HreachTmp4.
                  apply ok_remove_middle_inv in HreachTmp4.
                  destruct HreachTmp4 as [Hokl [Hnt1 Hnt2]].
                  apply ok_concat_inv in Hokl;
                  destruct Hokl as [Hokl1 Hokl2].
                  rewrite Hlist.
                  rewrite substitute_notin_app; auto.
                  simpl.
                  rewrite Nat.eqb_refl.
                  repeat rewrite get_r'_dist; auto.
                  repeat rewrite get_f'_dist; auto.
                  simpl.
                  apply notin_get_none in Hnotin_res.
                  rewrite Hnotin_res. lia.
                }
                destruct Hvalid as [s3 [s4 [acts3 [acts4 [pid' [n3 [n4 [Hvalid3 [Hstep34 [Hvalid4 [Hacts34 [Heq34 [Hb34 [Ht34 HR]]]]]]]]]]]]]].
                assert (Hreach_e28 : reachable_len' (composed_array_queue L) s3 (n' + 1 + n3)).
                eapply valid_execution_fragment_reach_len'; eauto.
                pose proof Hreach_e28 as Hreach_e28';
                apply IHk in Hreach_e28; try lia.
                unfold inv_total in Hreach_e28.
                destruct Hreach_e28 as [Hinv_e28 _].
                unfold inv_e28_clean in Hinv_e28.
                pose proof Hb34 as Hb34'.
                apply Hinv_e28 in Hb34.
                2 : {
                  apply reachable_len_to_reachable in Hreach_e28'.
                  apply step_invariant in Hreach_e28'.
                  unfold ComposedLTS.inv in Hreach_e28'.
                  inversion Hstep34; subst; simpl in *.
                  inversion H17; subst; simpl in *.
                  apply Hreach_e28' in Hbinds2; auto.
                  destruct Hbinds2 as [s1' [s2' [q [acts' [Hint_query [Hvalid' Hgather']]]]]].
                  inversion Hint_query; subst; simpl in *.
                  inversion H19; subst; simpl in *.
                  unfold binds in Hb34.
                  inversion H21; subst; simpl in *.
                Ltac tmp''' H Hvalid' st0 pid' acts' Hgather' Hb34 :=
                apply valid_execution_fragment_com' in Hvalid';
                simpl in Hvalid';
                destruct st0; simpl in *;
  eapply valid_execution_fragment_sync in Hvalid'; eauto;
  eapply H with (pid:=pid') in Hvalid'; eauto;
  try (simpl; eapply substitute_eq_binds_v'; eauto);
  try (
      assert (clts_events_B_to_events_B (gather_pid_events_B pid' acts') = nil) by
      (rewrite Hgather'; simpl; reflexivity);
      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B;
      assumption
      );
      (rewrite Hvalid' in Hb34; discriminate).
                  tmp''' noB_preserves_AEnq2 Hvalid' st0 pid' acts' Hgather' Hb34.
                  tmp''' noB_preserves_AEnq5 Hvalid' st0 pid' acts' Hgather' Hb34.
                  tmp''' noB_preserves_AEnq11 Hvalid' st0 pid' acts' Hgather' Hb34.
                  tmp''' noB_preserves_AEnq14 Hvalid' st0 pid' acts' Hgather' Hb34.

  pose proof Hvalid' as HvalidTmp';
                apply valid_execution_fragment_com' in Hvalid';
                simpl in Hvalid';
                destruct st0; simpl in *;
  eapply valid_execution_fragment_sync in Hvalid'; eauto;
  eapply noB_preserves_AEnq28_combine with (pid:=pid') in Hvalid'; eauto;
  try (simpl; eapply substitute_eq_binds_v'; eauto);
  try (
      assert (clts_events_B_to_events_B (gather_pid_events_B pid' acts') = nil) by
      (rewrite Hgather'; simpl; reflexivity);
      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B;
      assumption).
  simpl in Hvalid'.
  destruct Hvalid' as [Hx [Hrear _]].
  inversion H20; subst; simpl in *.
  inversion H22; subst; simpl in *.
  inversion H24; subst; simpl in *.
  inversion H23; subst; simpl in *.
  inversion H18; subst; simpl in *.
  inversion H26; subst; simpl in *.
  inversion H25; subst; simpl in *.
  destruct (entry_eqb (Vector.nth vec1 (Fin.of_nat_lt Hlt0)) old)eqn:Heq_entry.
  2 : { 
    rewrite get_r'_any_ary_cas_false in HR; auto.
    lia.
  }
  apply entry_eqb_eq in Heq_entry.
  subst.
  apply valid_execution_fragment_com in HvalidTmp';
  simpl in HvalidTmp';
  eapply internal_preserves_request'' with (pid:=pid') in HvalidTmp'; simpl in *; eauto;
  try apply binds_push_eq;
  try (eapply gather_pid_events_B_gather_pid_external_events;
      eassumption).
  inversion HvalidTmp'; subst; simpl in *.
  assert (Htmp' : (Fin.of_nat_lt Hlt0) =
    (Fin.of_nat_lt (mod_lt H (rear0 pid')))).
  apply Fin.of_nat_ext.
  rewrite <-Hrear.
  rewrite <-Htmp'.
  rewrite <-Hx. auto.
                  tmp''' noB_preserves_AEnq31 Hvalid' st0 pid' acts' Hgather' Hb34.
                  tmp''' noB_preserves_ADeq2 Hvalid' st0 pid' acts' Hgather' Hb34.
                  tmp''' noB_preserves_ADeq5 Hvalid' st0 pid' acts' Hgather' Hb34.
                  tmp''' noB_preserves_ADeq11 Hvalid' st0 pid' acts' Hgather' Hb34.
                  tmp''' noB_preserves_ADeq14 Hvalid' st0 pid' acts' Hgather' Hb34.
                  tmp''' noB_preserves_ADeq28 Hvalid' st0 pid' acts' Hgather' Hb34.
                  tmp''' noB_preserves_ADeq31 Hvalid' st0 pid' acts' Hgather' Hb34.
                }
  intuition.
  unfold R in *.
  unfold get_rear, get_ary, get_pc in *.
  rewrite <-H17 in Heq34.
  rewrite <-Heq34 in H16.
  rewrite Hrear_e5_e27 in H16.
  apply valid_execution_fragment_len'_to_valid_execution_fragment in Hvalid4.
  eapply inv_vec_rear_ref_not_decrease in Hvalid4; eauto.
  2 : {
    eapply reachable_valid_execution.
    eapply reachable_len_to_reachable; eauto.
    eapply composed_lts.Step_Internal_L1; eauto;
    eapply composed_lts.Step_None; eauto.
  }
  unfold get_ary in *; simpl in *.
  rewrite H11 in Hvalid4; auto.
  rewrite Hrear_e5_e27 in Hvalid4.

  apply valid_execution_fragment_len'_to_valid_execution_fragment in Hvalid3.
  eapply inv_vec_rear_ref_not_decrease in Hvalid3; eauto.
  2 : {
    eapply reachable_len_to_reachable; eauto.
  }
  unfold get_ary in *; simpl in *.
  eapply Nat.le_trans in Hvalid3; eauto.
  rewrite H16 in Hvalid3.

                  apply reachable_len_to_reachable in Hreach_e28'.
                  apply step_invariant in Hreach_e28'.
                  unfold ComposedLTS.inv in Hreach_e28'.
                  inversion Hstep34; subst; simpl in *.
                  inversion H19; subst; simpl in *.
                  apply Hreach_e28' in Hbinds2; auto.
                  destruct Hbinds2 as [s1' [s2' [q [acts' [Hint_query [Hvalid' Hgather']]]]]].
                  inversion Hint_query; subst; simpl in *.
                  inversion H21; subst; simpl in *.
                  unfold binds in Hb34'.
                  inversion H23; subst; simpl in *.
                  tmp''' noB_preserves_AEnq2 Hvalid' st0 pid' acts' Hgather' Hb34'.
                  tmp''' noB_preserves_AEnq5 Hvalid' st0 pid' acts' Hgather' Hb34'.
                  tmp''' noB_preserves_AEnq11 Hvalid' st0 pid' acts' Hgather' Hb34'.
                  tmp''' noB_preserves_AEnq14 Hvalid' st0 pid' acts' Hgather' Hb34'.

  pose proof Hvalid' as HvalidTmp';
                apply valid_execution_fragment_com' in Hvalid';
                simpl in Hvalid';
                destruct st0; simpl in *;
  eapply valid_execution_fragment_sync in Hvalid'; eauto;
  eapply noB_preserves_AEnq28_combine with (pid:=pid') in Hvalid'; eauto;
  try (simpl; eapply substitute_eq_binds_v'; eauto);
  try (
      assert (clts_events_B_to_events_B (gather_pid_events_B pid' acts') = nil) by
      (rewrite Hgather'; simpl; reflexivity);
      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B;
      assumption).
  simpl in Hvalid'.
  destruct Hvalid' as [Hx [Hrear _]].

  inversion H22; subst; simpl in *.
  inversion H24; subst; simpl in *.
  inversion H26; subst; simpl in *.
  inversion H25; subst; simpl in *.

  inversion H20; subst; simpl in *.
  inversion H28; subst; simpl in *.
  inversion H27; subst; simpl in *.

  destruct ((entry_eqb (Vector.nth vec1 (Fin.of_nat_lt Hlt0)) old))eqn:Heq_entry.
  2 : { 
    rewrite get_r'_any_ary_cas_false in HR; auto.
    lia.
  }
  apply entry_eqb_eq in Heq_entry.
  subst.
  apply valid_execution_fragment_com in HvalidTmp';
  simpl in HvalidTmp';
  eapply internal_preserves_request'' with (pid:=pid') in HvalidTmp'; simpl in *; eauto;
  try apply binds_push_eq;
  try (eapply gather_pid_events_B_gather_pid_external_events;
      eassumption).
  inversion HvalidTmp'; subst; simpl in *.
  assert (Htmp' : (Fin.of_nat_lt Hlt0) =
    (Fin.of_nat_lt (mod_lt H (rear0 pid')))).
  apply Fin.of_nat_ext.
  rewrite Htmp' in Hvalid3.
  rewrite <-Hrear in Hvalid3.
  rewrite Vector.nth_replace_eq in Hvalid3; auto.
  rewrite H31 in Hvalid3.
  simpl in Hvalid3.
  rewrite Htmp' in Hvalid3. lia.

                  tmp''' noB_preserves_AEnq31 Hvalid' st0 pid' acts' Hgather' Hb34'.
                  tmp''' noB_preserves_ADeq2 Hvalid' st0 pid' acts' Hgather' Hb34'.
                  tmp''' noB_preserves_ADeq5 Hvalid' st0 pid' acts' Hgather' Hb34'.
                  tmp''' noB_preserves_ADeq11 Hvalid' st0 pid' acts' Hgather' Hb34'.
                  tmp''' noB_preserves_ADeq14 Hvalid' st0 pid' acts' Hgather' Hb34'.
                  tmp''' noB_preserves_ADeq28 Hvalid' st0 pid' acts' Hgather' Hb34'.
                  tmp''' noB_preserves_ADeq31 Hvalid' st0 pid' acts' Hgather' Hb34'.
              unfold inv_2 in He5_inv_2.
            intuition.
          (* REAR = R - 1 in s2 *)
          +++ assert (Hle : R s2 = 0 \/ R s2 > 0) by lia.
            intuition.
            rewrite H17 in H16. simpl in H16.
            rewrite <-H17 in H16. intuition.
            pose proof H16 as H16Tmp.
            apply He5_inv_1 in H16; auto.
            destruct H16 as [pid' [Hpid1 Hpid2]].
            apply He5_inv_5 in Hpid1; auto.
            destruct (R s2)eqn:HR2. lia.
            rewrite array_to_queue_S_r in H14; auto; try lia.
            simpl in H14.
            simpl in H16Tmp.
            rewrite Nat.sub_0_r in H16Tmp.
            rewrite <-H16Tmp in H14.
            unfold get_rear in *; simpl in *.
            rewrite Hbinds_e27 in H14.
            intuition.
          }
          intuition.
        (* lt *)
        ++ rewrite Hrear_R in H2.
          unfold inv_6 in Hinv_6.
          destruct Hinv_6 as [_ [_ Hrfl]].
          unfold inv_range in Hinv_range'.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.

          pose proof Hbinds_e27 as Hbinds_e27'.
          apply reachable_len_to_reachable in HreachTmp.
          pose proof HreachTmp as HreachTmp2.
            pose proof HreachTmp2 as HreachTmp3.
            apply inv_e27_x_none_invariant in HreachTmp2.
            unfold inv_e27_x_none in HreachTmp2.
            simpl in HreachTmp2.
            apply HreachTmp2 in Hbinds_e27'.
            rewrite H2 in Hbinds_e27'.

          apply binds_reconstruct in Hbinds_e27.
          inversion H4; subst; simpl in *.
          inversion H6; subst; simpl in *.
          inversion H8; subst; simpl in *.
          inversion H7; subst; simpl in *.
          destruct Hbinds_e27 as [l1 [l2 Hlist]].
          apply array_queue_wf_invarint in HreachTmp.
          unfold array_queue_wf in HreachTmp.
          simpl in HreachTmp.
          rewrite Hlist in HreachTmp.
          apply ok_remove_middle_inv in HreachTmp.
          destruct HreachTmp as [Hokl [Hnt1 Hnt2]].
          apply ok_concat_inv in Hokl.
          destruct Hokl as [Hokl1 Hokl2].
          rewrite Hlist.
          rewrite substitute_notin_app; auto.
          simpl.
          rewrite Nat.eqb_refl.
          apply notin_get_none in Hnotin_res.
          repeat rewrite get_r'_dist; auto.
          repeat rewrite get_f'_dist; auto.
          simpl.
          rewrite Hnotin_res.
          rewrite Hlist in Hrfl.
          repeat rewrite get_r'_dist in Hrfl; auto.
          repeat rewrite get_f'_dist in Hrfl; auto.
          simpl in Hrfl.
          rewrite Hlist in Hinv_range'.
          repeat rewrite get_r'_dist in Hinv_range'; auto.
          repeat rewrite get_f'_dist in Hinv_range'; auto.
          simpl in Hinv_range'.
          rewrite Hlist in Hbinds_e27'.
          rewrite substitute_notin_app in Hbinds_e27'; auto.
          simpl in Hbinds_e27'.
          rewrite Nat.eqb_refl in Hbinds_e27'.
          repeat rewrite get_r'_dist in Hbinds_e27'; auto.
          repeat rewrite get_f'_dist in Hbinds_e27'; auto.
          simpl in Hbinds_e27'.
          rewrite Hnotin_res in Hbinds_e27'.
          inversion Hrfl; subst; try lia.
          exfalso.
          intuition.
          rewrite H10 in H9.
          rewrite H10 in Hbinds_e27'.
          erewrite mod_L_eq_mod_lt_eq in Hbinds_e27'.
          2 : {
            assert (Htmp : L = 1 * L) by lia.
            rewrite Htmp at 1.
            rewrite Nat.Div0.mod_add.
            eauto.
          }
          rewrite array_to_queue_S_f in H9; auto; try lia.
          apply all_some_dist_inv in H9; auto.
          intuition.
          simpl in H15.
          rewrite Hbinds_e27' in H15.
          intuition.
        + unfold inv_e28_clean in Hinv_e28.
          inversion H1; subst; simpl in *.
          inversion H3; subst; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
          inversion H5; subst; simpl in *.
          all : apply substitute_neq_preserves_binds' in H0; auto;
          inversion H4; subst; simpl in *;
          inversion H6; subst; simpl in *;
          inversion H8; subst; simpl in *;
          inversion H7; subst; simpl in *;
          try (inversion H10; subst; simpl in *);
          try (inversion H9; subst; simpl in *);
          try (apply notin_get_none in Hnotin_res);
          apply Hinv_e28 in H0; auto;
          apply binds_reconstruct in Hbinds0;
          destruct Hbinds0 as [l1 [l2 Hlist]];
          apply reachable_len_to_reachable in HreachTmp;
          apply array_queue_wf_invarint in HreachTmp;
          unfold array_queue_wf in HreachTmp;
          simpl in HreachTmp;
          rewrite Hlist in HreachTmp;
          apply ok_remove_middle_inv in HreachTmp;
          destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
          apply ok_concat_inv in Hokl;
          destruct Hokl as [Hokl1 Hokl2];
          rewrite Hlist;
          rewrite substitute_notin_app; auto;
          repeat rewrite get_r'_dist; auto;
          repeat rewrite get_f'_dist; auto;
          simpl;
          try (rewrite Hnotin_res);
          rewrite Nat.eqb_refl;
          simpl;
          rewrite Hlist in H0;
          repeat rewrite get_r'_dist in H0; auto;
          repeat rewrite get_f'_dist in H0; auto.
          rewrite Hnotin_res. intuition.
          rewrite Hnotin_res. intuition.
          rewrite Hnotin_res. intuition.
          rewrite Hnotin_res. intuition.
      (* inv_d28 *)
      --- unfold inv_d28_clean.
        intros.
        pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [Hinv_e28 [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_6 Hinv_range']]]]]]]]]]]]].
        destruct (eq_nat_dec pid0 pid).
        + subst.
          inversion H1; subst; simpl in *.
          inversion H3; subst; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          unfold binds in H0.
          inversion H5; subst; simpl in *;
          pose proof Hbinds0 as Hbinds_e27;
          eapply substitute_eq_binds_v' in Hbinds0;
          rewrite Hbinds0 in H0; try discriminate.

          assert (Hrear_R :
front pid =
value
  (LState (Tensor.L1State (LState (Tensor.L2State (LState st1'))))) +
get_f' (substitute pc pid ADeq28)
  (Array.responses L (LState (Tensor.L1State (LState st1'))))
  (Counter.responses
     (LState
        (Tensor.L1State (LState (Tensor.L2State (LState st1'))))))
          ).
          {

          clear Hinv_e28.
            pose proof HreachTmp as HreachTmp2.
            apply reachable_len_to_reachable in HreachTmp2.
            pose proof HreachTmp2 as HreachTmp3.
            apply inv_front_invariant in HreachTmp2; auto.
            unfold inv_front in HreachTmp2.
            simpl in HreachTmp2.
            destruct HreachTmp2 as [Hr21 Hr22].
            specialize (Hr21 pid).
            assert (Hrear_R :
front pid <=
value
  (LState (Tensor.L1State (LState (Tensor.L2State (LState st1'))))) +
get_f' (substitute pc pid ADeq28)
  (Array.responses L (LState (Tensor.L1State (LState st1'))))
  (Counter.responses
     (LState
        (Tensor.L1State (LState (Tensor.L2State (LState st1'))))))
            ).
            eapply Nat.le_trans; eauto.
            inversion H4; subst; simpl in *.
            inversion H6; subst; simpl in *.
            inversion H8; subst; simpl in *.
            inversion H7; subst; simpl in *.
            lia.
            inversion Hrear_R; subst. auto.
            (* < is impossible *)
            (* exfalso. *)
            apply inv_d27_from_d5_keeps_vec_front_impl_front_eq_front_k_step with (pid:=pid) (H:=H) in HreachTmp; simpl; auto.
            destruct HreachTmp as [s1 [s2 [acts [ret [n' [t [Hvalid [Hstep_e5 [Hb_e5 [Hgather [Hreach_e5 [Hlt [Heq [Hb_ary_read [Hxp [Hvec_rear Hrear_keep]]]]]]]]]]]]]]]].
            simpl in *.
            unfold get_vec_front in *; simpl in *.
            unfold get_ary in *; simpl in *.
            inversion H4; subst; simpl in *.
            inversion H8; subst; simpl in *.
            inversion H10; subst; simpl in *.
            inversion H9; subst; simpl in *.
            intuition.

            assert (Hreach_e5' : reachable_len' (composed_array_queue L) s2 (n' + 1)).
            eapply valid_execution_fragment_reach_len'; eauto.
            eapply Step_Internal_L1_len'; eauto.
            eapply Step_None_len'; eauto.
            pose proof Hreach_e5' as Hreach_e5''.
            apply IHk in Hreach_e5'; try lia.
            unfold inv_total in Hreach_e5'.
            destruct Hreach_e5' as [_ [_ [_ [He5_inv_1 [_ [He5_inv_2 [_ [_ [_ [_ [_ [He5_inv_5 [_ He5_inv_range]]]]]]]]]]]]].
            unfold inv_range in He5_inv_range.
            pose proof HreachTmp3 as HreachTmp4.
            apply inv_d27_x_none_invariant in HreachTmp3.
            unfold inv_d27_x_none in HreachTmp3.
            simpl in HreachTmp3.
            pose proof Hbinds_e27 as Hbinds_e27'.
            apply HreachTmp3 in Hbinds_e27.
            rewrite H2 in Hbinds_e27.
            rewrite H11 in Hbinds_e27.
            assert (Hrear_s2 : ArrayQueueImpl.front (get_impl L s2) pid =
              value (get_front L s2)).
              unfold get_impl, get_rear in *; simpl in *.
              inversion Hstep_e5; subst; simpl in *.
              inversion H12; subst; simpl in *.
              inversion H13; subst; simpl in *.
              inversion H15; subst; simpl in *.
              inversion H14; subst; simpl in *.
              auto.
              assert (Ha: forall x, (ArrayQueueInvariantBefore0.get_impl L x =
              get_impl L x)).
              unfold get_impl, ArrayQueueInvariantBefore0.get_impl.
              simpl. reflexivity.
              rewrite Ha in Hbinds_e27.
              rewrite Hrear_s2 in Hbinds_e27.
              unfold not_none_wrapper in Hbinds_e27.
            (* unfold inv_2 in He5_inv_2. *)
            
            assert (
              Haa : value
                (LState
                  (Tensor.L1State
                    (LState (Tensor.L2State (LState (L1State s2)))))) =
              F s2 -> False
            ). intros H16. intuition.

              unfold get_front in *; simpl in *.
                rewrite <-Hrear_s2 in H16.
                unfold get_impl in *; simpl in *.
                unfold F, R in *; simpl in *.
                unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
                assert (Hrear_e5_e27 : (front pid) = (ArrayQueueImpl.front (LState (L2State s2)) pid)).
                apply valid_execution_fragment_len'_to_valid_execution_fragment in Hvalid; auto.

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

Ltac solve_after_d3 :=
  try apply after_d3_Deq4;
  try apply after_d3_Deq5;
  try apply after_d3_Deq6;
  try (unfold after_d6;
  right; right; right;
  solve_after_d6).

                eapply inv_impl_front_keep'' with (v:=ADeq5) in Hvalid.
                unfold get_impl in *; simpl in *. eauto.
                solve_before_d27.
                solve_after_d3.
                unfold get_pc; simpl.
                inversion Hstep_e5; subst; simpl in *; auto.
                simpl; auto.
                unfold get_pc; simpl. auto.

                rewrite <-Hrear_e5_e27 in H16.
                assert (Hgt :
                  front pid <
                  value (LState (Tensor.L1State (LState st2))) +
     get_f' (substitute pc pid ADeq28) res
       (Counter.responses (LState (Tensor.L1State (LState st2))))
                ) by lia.
                rewrite H16 in Hgt.
                generalize inv_F_increase_step_L1'; intros Hmiddle.
                unfold F in Hmiddle.
                unfold get_front, get_rear, get_ary, get_pc in Hmiddle; simpl in Hmiddle.
                specialize (Hmiddle L s2).
                apply Hmiddle in Hvalid; simpl; auto; try lia.
                2 : {
                  eapply reachable_len_to_reachable; eauto.
                }
                2 : {
                  eapply Nat.lt_le_trans; eauto.
                  apply binds_reconstruct in Hbinds_e27'.
                  destruct Hbinds_e27' as [l1 [l2 Hlist]].
                  apply array_queue_wf_invarint in HreachTmp4.
                  unfold array_queue_wf in HreachTmp4.
                  simpl in HreachTmp4.
                  rewrite Hlist in HreachTmp4.
                  apply ok_remove_middle_inv in HreachTmp4.
                  destruct HreachTmp4 as [Hokl [Hnt1 Hnt2]].
                  apply ok_concat_inv in Hokl;
                  destruct Hokl as [Hokl1 Hokl2].
                  rewrite Hlist.
                  rewrite substitute_notin_app; auto.
                  simpl.
                  rewrite Nat.eqb_refl.
                  repeat rewrite get_r'_dist; auto.
                  repeat rewrite get_f'_dist; auto.
                  simpl.
                  apply notin_get_none in Hnotin_res.
                  rewrite Hnotin_res. lia.
                }
                destruct Hvalid as [s3 [s4 [acts3 [acts4 [pid' [n3 [n4 [Hvalid3 [Hstep34 [Hvalid4 [Hacts34 [Heq34 [Hb34 [Ht34 HR]]]]]]]]]]]]]].
                assert (Hreach_e28 : reachable_len' (composed_array_queue L) s3 (n' + 1 + n3)).
                eapply valid_execution_fragment_reach_len'; eauto.
                pose proof Hreach_e28 as Hreach_e28';
                apply IHk in Hreach_e28; try lia.
                unfold inv_total in Hreach_e28.
                destruct Hreach_e28 as [_ [Hinv_e28 _]].
                unfold inv_d28_clean in Hinv_e28.
                pose proof Hb34 as Hb34'.
                apply Hinv_e28 in Hb34.
                2 : {
                  apply reachable_len_to_reachable in Hreach_e28'.
                  apply step_invariant in Hreach_e28'.
                  unfold ComposedLTS.inv in Hreach_e28'.
                  inversion Hstep34; subst; simpl in *.
                  inversion H17; subst; simpl in *.
                  apply Hreach_e28' in Hbinds2; auto.
                  destruct Hbinds2 as [s1' [s2' [q [acts' [Hint_query [Hvalid' Hgather']]]]]].
                  inversion Hint_query; subst; simpl in *.
                  inversion H19; subst; simpl in *.
                  unfold binds in Hb34.
                  inversion H21; subst; simpl in *.
                (* Ltac tmp''' H Hvalid' st0 pid' acts' Hgather' Hb34 :=
                apply valid_execution_fragment_com' in Hvalid';
                simpl in Hvalid';
                destruct st0; simpl in *;
  eapply valid_execution_fragment_sync in Hvalid'; eauto;
  eapply H with (pid:=pid') in Hvalid'; eauto;
  try (simpl; eapply substitute_eq_binds_v'; eauto);
  try (
      assert (clts_events_B_to_events_B (gather_pid_events_B pid' acts') = nil) by
      (rewrite Hgather'; simpl; reflexivity);
      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B;
      assumption
      );
      (rewrite Hvalid' in Hb34; discriminate). *)
                  tmp''' noB_preserves_AEnq2 Hvalid' st0 pid' acts' Hgather' Hb34.
                  tmp''' noB_preserves_AEnq5 Hvalid' st0 pid' acts' Hgather' Hb34.
                  tmp''' noB_preserves_AEnq11 Hvalid' st0 pid' acts' Hgather' Hb34.
                  tmp''' noB_preserves_AEnq14 Hvalid' st0 pid' acts' Hgather' Hb34.
                  tmp''' noB_preserves_AEnq28 Hvalid' st0 pid' acts' Hgather' Hb34.
                  tmp''' noB_preserves_AEnq31 Hvalid' st0 pid' acts' Hgather' Hb34.
                  tmp''' noB_preserves_ADeq2 Hvalid' st0 pid' acts' Hgather' Hb34.
                  tmp''' noB_preserves_ADeq5 Hvalid' st0 pid' acts' Hgather' Hb34.
                  tmp''' noB_preserves_ADeq11 Hvalid' st0 pid' acts' Hgather' Hb34.
                  tmp''' noB_preserves_ADeq14 Hvalid' st0 pid' acts' Hgather' Hb34.

  pose proof Hvalid' as HvalidTmp';
                apply valid_execution_fragment_com' in Hvalid';
                simpl in Hvalid';
                destruct st0; simpl in *;
  eapply valid_execution_fragment_sync in Hvalid'; eauto;
  eapply noB_preserves_ADeq28_combine with (pid:=pid') in Hvalid'; eauto;
  try (simpl; eapply substitute_eq_binds_v'; eauto);
  try (
      assert (clts_events_B_to_events_B (gather_pid_events_B pid' acts') = nil) by
      (rewrite Hgather'; simpl; reflexivity);
      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B;
      assumption).
  simpl in Hvalid'.
  destruct Hvalid' as [Hx Hrear].
  inversion H20; subst; simpl in *.
  inversion H22; subst; simpl in *.
  inversion H24; subst; simpl in *.
  inversion H23; subst; simpl in *.
  inversion H18; subst; simpl in *.
  inversion H26; subst; simpl in *.
  inversion H25; subst; simpl in *.
  destruct (entry_eqb (Vector.nth vec1 (Fin.of_nat_lt Hlt0)) old)eqn:Heq_entry.
  2 : { 
    rewrite get_f'_any_ary_cas_false in HR; auto.
    lia.
  }
  apply entry_eqb_eq in Heq_entry.
  subst.
  apply valid_execution_fragment_com in HvalidTmp';
  simpl in HvalidTmp';
  eapply internal_preserves_request'' with (pid:=pid') in HvalidTmp'; simpl in *; eauto;
  try apply binds_push_eq;
  try (eapply gather_pid_events_B_gather_pid_external_events;
      eassumption).
  inversion HvalidTmp'; subst; simpl in *.
  assert (Htmp' : (Fin.of_nat_lt Hlt0) =
    (Fin.of_nat_lt (mod_lt H (front0 pid')))).
  apply Fin.of_nat_ext.
  rewrite <-Hrear.
  rewrite <-Htmp'.
  rewrite <-Hx. auto.
                  tmp''' noB_preserves_ADeq31 Hvalid' st0 pid' acts' Hgather' Hb34.
                }
  intuition.
  unfold F in *.
  unfold get_front, get_rear, get_ary, get_pc in *.
  rewrite <-H17 in Heq34.
  rewrite <-Heq34 in H16.
  rewrite Hrear_e5_e27 in H16.
  apply valid_execution_fragment_len'_to_valid_execution_fragment in Hvalid4.
  eapply inv_vec_front_ref_not_decrease in Hvalid4; eauto.
  2 : {
    eapply reachable_valid_execution.
    eapply reachable_len_to_reachable; eauto.
    eapply composed_lts.Step_Internal_L1; eauto;
    eapply composed_lts.Step_None; eauto.
  }
  unfold get_ary in *; simpl in *.
  rewrite H11 in Hvalid4; auto.
  rewrite Hrear_e5_e27 in Hvalid4.
  rewrite Ha in Hvalid4.

  apply valid_execution_fragment_len'_to_valid_execution_fragment in Hvalid3.
  eapply inv_vec_front_ref_not_decrease in Hvalid3; eauto.
  2 : {
    eapply reachable_len_to_reachable; eauto.
  }
  unfold get_ary in *; simpl in *.
  eapply Nat.le_trans in Hvalid3; eauto.
  rewrite H16 in Hvalid3.

                  apply reachable_len_to_reachable in Hreach_e28'.
                  apply step_invariant in Hreach_e28'.
                  unfold ComposedLTS.inv in Hreach_e28'.
                  inversion Hstep34; subst; simpl in *.
                  inversion H19; subst; simpl in *.
                  apply Hreach_e28' in Hbinds2; auto.
                  destruct Hbinds2 as [s1' [s2' [q [acts' [Hint_query [Hvalid' Hgather']]]]]].
                  inversion Hint_query; subst; simpl in *.
                  inversion H21; subst; simpl in *.
                  unfold binds in Hb34'.
                  inversion H23; subst; simpl in *.
                  tmp''' noB_preserves_AEnq2 Hvalid' st0 pid' acts' Hgather' Hb34'.
                  tmp''' noB_preserves_AEnq5 Hvalid' st0 pid' acts' Hgather' Hb34'.
                  tmp''' noB_preserves_AEnq11 Hvalid' st0 pid' acts' Hgather' Hb34'.
                  tmp''' noB_preserves_AEnq14 Hvalid' st0 pid' acts' Hgather' Hb34'.
                  tmp''' noB_preserves_AEnq28 Hvalid' st0 pid' acts' Hgather' Hb34'.
                  tmp''' noB_preserves_AEnq31 Hvalid' st0 pid' acts' Hgather' Hb34'.
                  tmp''' noB_preserves_ADeq2 Hvalid' st0 pid' acts' Hgather' Hb34'.
                  tmp''' noB_preserves_ADeq5 Hvalid' st0 pid' acts' Hgather' Hb34'.
                  tmp''' noB_preserves_ADeq11 Hvalid' st0 pid' acts' Hgather' Hb34'.
                  tmp''' noB_preserves_ADeq14 Hvalid' st0 pid' acts' Hgather' Hb34'.

  pose proof Hvalid' as HvalidTmp';
                apply valid_execution_fragment_com' in Hvalid';
                simpl in Hvalid';
                destruct st0; simpl in *;
  eapply valid_execution_fragment_sync in Hvalid'; eauto;
  eapply noB_preserves_ADeq28_combine with (pid:=pid') in Hvalid'; eauto;
  try (simpl; eapply substitute_eq_binds_v'; eauto);
  try (
      assert (clts_events_B_to_events_B (gather_pid_events_B pid' acts') = nil) by
      (rewrite Hgather'; simpl; reflexivity);
      rewrite gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B;
      assumption).
  simpl in Hvalid'.
  destruct Hvalid' as [Hx Hrear].

  inversion H22; subst; simpl in *.
  inversion H24; subst; simpl in *.
  inversion H26; subst; simpl in *.
  inversion H25; subst; simpl in *.

  inversion H20; subst; simpl in *.
  inversion H28; subst; simpl in *.
  inversion H27; subst; simpl in *.

  destruct ((entry_eqb (Vector.nth vec1 (Fin.of_nat_lt Hlt0)) old))eqn:Heq_entry.
  2 : { 
    rewrite get_f'_any_ary_cas_false in HR; auto.
    lia.
  }
  apply entry_eqb_eq in Heq_entry.
  subst.
  apply valid_execution_fragment_com in HvalidTmp';
  simpl in HvalidTmp';
  eapply internal_preserves_request'' with (pid:=pid') in HvalidTmp'; simpl in *; eauto;
  try apply binds_push_eq;
  try (eapply gather_pid_events_B_gather_pid_external_events;
      eassumption).
  inversion HvalidTmp'; subst; simpl in *.
  assert (Htmp' : (Fin.of_nat_lt Hlt0) =
    (Fin.of_nat_lt (mod_lt H (front0 pid')))).
  apply Fin.of_nat_ext.
  rewrite Htmp' in Hvalid3.
  rewrite <-Hrear in Hvalid3.
  rewrite Vector.nth_replace_eq in Hvalid3; auto.
  rewrite H31 in Hvalid3.
  simpl in Hvalid3.
  rewrite Htmp' in Hvalid3.
  rewrite Hrear in Hvalid3.
  lia.

                  tmp''' noB_preserves_ADeq31 Hvalid' st0 pid' acts' Hgather' Hb34'.
              unfold inv_2' in He5_inv_2.
            intuition.
          (* FRONT = F - 1 in s2 *)
          +++ assert (Hle : F s2 = 0 \/ F s2 > 0) by lia.
            intuition.
            rewrite H17 in H16. simpl in H16.
            rewrite <-H17 in H16. intuition.
            pose proof H16 as H16Tmp.
            apply He5_inv_1 in H16; auto.
            destruct H16 as [pid' [Hpid1 Hpid2]].
            apply He5_inv_5 in Hpid1; auto.
            destruct (F s2)eqn:HR2. lia.
            simpl in H15.
            (* destruct (R s2)eqn:HR2. lia. *)
            rewrite array_to_queue_S_r in H15; auto; try lia.
            simpl in H15.
            simpl in H16Tmp.
            rewrite Nat.sub_0_r in H16Tmp.
            rewrite <-H16Tmp in H15.
            unfold get_front in *; simpl in *.
            assert (Hpp : forall A v, v <> (@None A) -> exists ret, v = Some ret).
            intros. destruct v.
            exists a. intuition. intuition.
            apply Hpp in Hbinds_e27.
            destruct Hbinds_e27 as [ret Hret].
            intuition.
            erewrite mod_L_eq_mod_lt_eq in H15.
            rewrite Hret in H15.
            intuition.
            assert (Htmp : L = 1 * L) by lia.
            symmetry.
            erewrite <-Nat.Div0.mod_add.
            rewrite <-Htmp. auto.
          }
          intuition.
        (* lt *)
        ++ rewrite Hrear_R in H2.
          unfold inv_6 in Hinv_6.
          destruct Hinv_6 as [_ [Hrfl _]].
          unfold inv_range in Hinv_range'.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.

          pose proof Hbinds_e27 as Hbinds_e27'.
          apply reachable_len_to_reachable in HreachTmp.
          pose proof HreachTmp as HreachTmp2.
            pose proof HreachTmp2 as HreachTmp3.
            apply inv_d27_x_none_invariant in HreachTmp2.
            unfold inv_d27_x_none in HreachTmp2.
            simpl in HreachTmp2.
            apply HreachTmp2 in Hbinds_e27'.
            rewrite H2 in Hbinds_e27'.

          apply binds_reconstruct in Hbinds_e27.
          inversion H4; subst; simpl in *.
          inversion H6; subst; simpl in *.
          inversion H8; subst; simpl in *.
          inversion H7; subst; simpl in *.
          destruct Hbinds_e27 as [l1 [l2 Hlist]].
          apply array_queue_wf_invarint in HreachTmp.
          unfold array_queue_wf in HreachTmp.
          simpl in HreachTmp.
          rewrite Hlist in HreachTmp.
          apply ok_remove_middle_inv in HreachTmp.
          destruct HreachTmp as [Hokl [Hnt1 Hnt2]].
          apply ok_concat_inv in Hokl.
          destruct Hokl as [Hokl1 Hokl2].
          rewrite Hlist.
          rewrite substitute_notin_app; auto.
          simpl.
          rewrite Nat.eqb_refl.
          apply notin_get_none in Hnotin_res.
          repeat rewrite get_r'_dist; auto.
          repeat rewrite get_f'_dist; auto.
          simpl.
          rewrite Hnotin_res.
          rewrite Hlist in Hrfl.
          repeat rewrite get_r'_dist in Hrfl; auto.
          repeat rewrite get_f'_dist in Hrfl; auto.
          simpl in Hrfl.
          rewrite Hlist in Hinv_range'.
          repeat rewrite get_r'_dist in Hinv_range'; auto.
          repeat rewrite get_f'_dist in Hinv_range'; auto.
          simpl in Hinv_range'.
          rewrite Hlist in Hbinds_e27'.
          rewrite substitute_notin_app in Hbinds_e27'; auto.
          simpl in Hbinds_e27'.
          rewrite Nat.eqb_refl in Hbinds_e27'.
          repeat rewrite get_r'_dist in Hbinds_e27'; auto.
          repeat rewrite get_f'_dist in Hbinds_e27'; auto.
          simpl in Hbinds_e27'.
          rewrite Hnotin_res in Hbinds_e27'.
          inversion Hrfl; subst; try lia.
          exfalso.
          intuition.
          rewrite H10 in H11.
          rewrite H10 in Hbinds_e27'.
          (* erewrite mod_L_eq_mod_lt_eq in Hbinds_e27'.
          2 : {
            assert (Htmp : L = 1 * L) by lia.
            rewrite Htmp at 1.
            rewrite Nat.Div0.mod_add.
            eauto.
          } *)
          rewrite array_to_queue_S_f in H11; auto; try lia.
          apply all_none_dist_inv in H11; auto.
          intuition.
          simpl in H15.
          unfold not_none_wrapper in Hbinds_e27'.
          assert (Hpp : forall A v, v <> (@None A) -> exists ret, v = Some ret).
          intros. destruct v.
          exists a. intuition. intuition.
          apply Hpp in Hbinds_e27'.
          destruct Hbinds_e27' as [ret Hret].
          rewrite Hret in H15. intuition.
        + unfold inv_d28_clean in Hinv_e28.
          inversion H1; subst; simpl in *.
          inversion H3; subst; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
          inversion H5; subst; simpl in *.
          all : apply substitute_neq_preserves_binds' in H0; auto;
          inversion H4; subst; simpl in *;
          inversion H6; subst; simpl in *;
          inversion H8; subst; simpl in *;
          inversion H7; subst; simpl in *;
          try (inversion H10; subst; simpl in *);
          try (inversion H9; subst; simpl in *);
          try (apply notin_get_none in Hnotin_res);
          apply Hinv_e28 in H0; auto;
          apply binds_reconstruct in Hbinds0;
          destruct Hbinds0 as [l1 [l2 Hlist]];
          apply reachable_len_to_reachable in HreachTmp;
          apply array_queue_wf_invarint in HreachTmp;
          unfold array_queue_wf in HreachTmp;
          simpl in HreachTmp;
          rewrite Hlist in HreachTmp;
          apply ok_remove_middle_inv in HreachTmp;
          destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
          apply ok_concat_inv in Hokl;
          destruct Hokl as [Hokl1 Hokl2];
          rewrite Hlist;
          rewrite substitute_notin_app; auto;
          repeat rewrite get_r'_dist; auto;
          repeat rewrite get_f'_dist; auto;
          simpl;
          try (rewrite Hnotin_res);
          rewrite Nat.eqb_refl;
          simpl;
          rewrite Hlist in H0;
          repeat rewrite get_r'_dist in H0; auto;
          repeat rewrite get_f'_dist in H0; auto.
          rewrite Hnotin_res. intuition.
          rewrite Hnotin_res. intuition.
          rewrite Hnotin_res. intuition.
          rewrite Hnotin_res. intuition.
      (* inv_1 *)
      --- unfold inv_1.
        pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [Hinv_1 _]]].
          inversion H1; subst; simpl in *.
          inversion H0; subst; simpl in *.
          unfold inv_1 in *; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          inversion H3; subst; simpl in *.

          all : pose proof Hbinds0 as HbindsTmp;
          apply binds_reconstruct in Hbinds0;
          inversion H2; subst; simpl in *;
          inversion H4; subst; simpl in *;
          inversion H6; subst; simpl in *;
          inversion H5; subst; simpl in *;
          try (inversion H8; subst; simpl in *);
          try (inversion H7; subst; simpl in *);
          destruct Hbinds0 as [l1 [l2 Hlist]];
          rewrite Hlist in Hinv_1 at 1 2;
          repeat rewrite get_r'_dist in Hinv_1; auto;
          repeat rewrite get_f'_dist in Hinv_1; auto;
          simpl in Hinv_1;
          apply reachable_len_to_reachable in HreachTmp;
          apply array_queue_wf_invarint in HreachTmp;
          unfold array_queue_wf in HreachTmp;
          simpl in HreachTmp;
          rewrite Hlist in HreachTmp;
          apply ok_remove_middle_inv in HreachTmp;
          destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
          rewrite Hlist at 1 2;
          rewrite substitute_notin_app; auto;
          repeat rewrite get_r'_dist; auto;
          repeat rewrite get_f'_dist; auto;
          simpl;
          rewrite Nat.eqb_refl;
          simpl in *;
          try rewrite <-Hlist in *;
          intuition.
          all : try (
          try (destruct H12 as [pid0 [Hpid1 Hpid2]]);
          try (destruct H10 as [pid0 [Hpid1 Hpid2]]);
          exists pid0;
          intuition;
          [destruct (eq_nat_dec pid pid0);
          [subst pid;
          exfalso;
          unfold enq_not_inc in Hpid1;
          unfold binds in Hpid1;
          rewrite HbindsTmp in Hpid1;
          intuition; discriminate|
          eapply enq_not_inc_subst_neq; eauto]|
          try (apply Hpid2 in H11; auto);
          try (apply Hpid2 in H9; auto);
          destruct (eq_nat_dec pid pid');
          [subst pid;
          exfalso;
          try (eapply enq_not_inc_subst_normal_false in H12; eauto; solve_normal);
          try (eapply enq_not_inc_subst_normal_false in H10; eauto; solve_normal)|
          eapply enq_not_inc_subst_neq_inv; eauto
          ]]).
          apply notin_get_none in Hnotin_res;
          try (rewrite Hnotin_res in H7, H8);
          try (rewrite Hnotin_res in H9, H10);
          intuition;
          try (destruct H10 as [pid0 [Hpid1 Hpid2]]);
          try (destruct H12 as [pid0 [Hpid1 Hpid2]]);
          destruct (eq_nat_dec pid pid0);
          [subst pid;
          unfold enq_not_inc in *;
          unfold binds in Hpid1;
          rewrite HbindsTmp in Hpid1;
          intuition; discriminate|
          exists pid0;
          intuition;
          try (eapply enq_not_inc_subst_neq; eauto);
          destruct (eq_nat_dec pid pid');
          try (apply enq_not_inc_subst_neq_inv in H10; auto;
          apply Hpid2 in H9; auto);
          subst pid;
          unfold enq_not_inc in H10;
          eapply substitute_eq_binds_v' in HbindsTmp;
          unfold binds in H10;
          rewrite HbindsTmp in H10;
          intuition; try discriminate;
          simpl in H12;
          rewrite Hnotin_res in H12; discriminate].

          pose proof Hnotin_res as Hnotin_res';
          apply notin_get_none in Hnotin_res;
          try (rewrite Hnotin_res in H9, H10);
          intuition;
          destruct H12 as [pid0 [Hpid1 Hpid2]];
          exists pid;
          intuition;
          [unfold enq_not_inc;
          right; right; right;
          intuition;
          eapply substitute_eq_binds_v'; eauto|
          destruct (eq_nat_dec pid' pid0);
          [subst pid';
          apply enq_not_inc_subst_neq_inv in H12; auto;
          eapply Hpid2; eauto;
          unfold enq_not_inc;
          right; right; left;
          auto|
          apply Hpid2 in n0; auto;
          apply enq_not_inc_subst_neq_inv in H12; auto]].
      (* inv_1' *)
      --- unfold inv_1'.
        pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [Hinv_1 _]]]].
          inversion H1; subst; simpl in *.
          inversion H0; subst; simpl in *.
          unfold inv_1' in *; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          inversion H3; subst; simpl in *.

          all : pose proof Hbinds0 as HbindsTmp;
          apply binds_reconstruct in Hbinds0;
          inversion H2; subst; simpl in *;
          inversion H4; subst; simpl in *;
          inversion H6; subst; simpl in *;
          inversion H5; subst; simpl in *;
          try (inversion H8; subst; simpl in *);
          try (inversion H7; subst; simpl in *);
          destruct Hbinds0 as [l1 [l2 Hlist]];
          rewrite Hlist in Hinv_1;
          repeat rewrite get_r'_dist in Hinv_1; auto;
          repeat rewrite get_f'_dist in Hinv_1; auto;
          simpl in Hinv_1;
          apply reachable_len_to_reachable in HreachTmp;
          apply array_queue_wf_invarint in HreachTmp;
          unfold array_queue_wf in HreachTmp;
          simpl in HreachTmp;
          rewrite Hlist in HreachTmp;
          apply ok_remove_middle_inv in HreachTmp;
          destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
          rewrite Hlist at 1 2;
          rewrite substitute_notin_app; auto;
          repeat rewrite get_r'_dist; auto;
          repeat rewrite get_f'_dist; auto;
          simpl;
          rewrite Nat.eqb_refl;
          simpl in *;
          try rewrite <-Hlist in *;
          intuition.
          all : try (
          try (destruct H12 as [pid0 [Hpid1 Hpid2]]);
          try (destruct H10 as [pid0 [Hpid1 Hpid2]]);
          exists pid0;
          intuition;
          [destruct (eq_nat_dec pid pid0);
          [subst pid;
          exfalso;
          unfold deq_not_inc in Hpid1;
          unfold binds in Hpid1;
          rewrite HbindsTmp in Hpid1;
          intuition; discriminate|
          eapply deq_not_inc_subst_neq; eauto]|
          try (apply Hpid2 in H11; auto);
          try (apply Hpid2 in H9; auto);
          destruct (eq_nat_dec pid pid');
          [subst pid;
          exfalso;
          try (eapply deq_not_inc_subst_normal_false in H12; eauto; solve_normal);
          try (eapply deq_not_inc_subst_normal_false in H10; eauto; solve_normal)|
          eapply deq_not_inc_subst_neq_inv; eauto
          ]]).
          apply notin_get_none in Hnotin_res;
          try (rewrite Hnotin_res in H7, H8);
          try (rewrite Hnotin_res in H9, H10);
          intuition;
          try (destruct H10 as [pid0 [Hpid1 Hpid2]]);
          try (destruct H12 as [pid0 [Hpid1 Hpid2]]);
          destruct (eq_nat_dec pid pid0);
          [subst pid;
          unfold deq_not_inc in *;
          unfold binds in Hpid1;
          rewrite HbindsTmp in Hpid1;
          intuition; discriminate|
          exists pid0;
          intuition;
          try (eapply deq_not_inc_subst_neq; eauto);
          destruct (eq_nat_dec pid pid');
          try (apply deq_not_inc_subst_neq_inv in H10; auto;
          apply Hpid2 in H9; auto);
          subst pid;
          unfold deq_not_inc in H10;
          eapply substitute_eq_binds_v' in HbindsTmp;
          unfold binds in H10;
          rewrite HbindsTmp in H10;
          intuition; try discriminate;
          simpl in H12;
          rewrite Hnotin_res in H12; discriminate].

          pose proof Hnotin_res as Hnotin_res';
          apply notin_get_none in Hnotin_res;
          try (rewrite Hnotin_res in H9, H10);
          intuition;
          destruct H12 as [pid0 [Hpid1 Hpid2]];
          exists pid;
          intuition;
          [unfold deq_not_inc;
          right; right; right;
          intuition;
          eapply substitute_eq_binds_v'; eauto|
          destruct (eq_nat_dec pid' pid0);
          [subst pid';
          apply deq_not_inc_subst_neq_inv in H12; auto;
          eapply Hpid2; eauto;
          unfold deq_not_inc;
          right; right; left;
          auto|
          apply Hpid2 in n0; auto;
          apply deq_not_inc_subst_neq_inv in H12; auto]].
      (* inv_2 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [Hinv_2 _]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_2; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H3; subst; simpl in *;
        inversion H2; subst; simpl in *;
        inversion H4; subst; simpl in *;
        inversion H6; subst; simpl in *;
        inversion H5; subst; simpl in *;
        try (inversion H8; subst; simpl in *);
        try (inversion H7; subst; simpl in *);
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        unfold inv_2 in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_2;
        repeat rewrite get_r'_dist in Hinv_2; auto;
        repeat rewrite get_f'_dist in Hinv_2; auto;
        simpl in Hinv_2;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.
        all : apply notin_get_none in Hnotin_res;
        rewrite Hnotin_res; intuition.
      (* inv_2' *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [Hinv_2 _]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_2'; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H3; subst; simpl in *;
        inversion H2; subst; simpl in *;
        inversion H4; subst; simpl in *;
        inversion H6; subst; simpl in *;
        inversion H5; subst; simpl in *;
        try (inversion H8; subst; simpl in *);
        try (inversion H7; subst; simpl in *);
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        unfold inv_2' in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_2;
        repeat rewrite get_r'_dist in Hinv_2; auto;
        repeat rewrite get_f'_dist in Hinv_2; auto;
        simpl in Hinv_2;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.
        all : apply notin_get_none in Hnotin_res;
        rewrite Hnotin_res; intuition.
      (* inv_3 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [Hinv_3 _]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_3; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        intros pid0 Henq.

        inversion H3; subst; simpl in *.

        all : pose proof Hbinds0 as HbindsTmp;
        inversion H2; subst; simpl in *;
        inversion H4; subst; simpl in *;
        inversion H6; subst; simpl in *;
        inversion H5; subst; simpl in *;
        try (inversion H8; subst; simpl in *);
        try (inversion H7; subst; simpl in *);
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];

        unfold inv_3 in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_3;
        repeat rewrite get_r'_dist in Hinv_3; auto;
        repeat rewrite get_f'_dist in Hinv_3; auto;
        simpl in Hinv_3;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.
        all : try (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        exfalso;
        eapply enq_not_inc_subst_normal_false; eauto; solve_normal);
        apply enq_not_inc_subst_neq_inv in Henq; auto;
        rewrite <-Hlist in Hinv_3;
        apply Hinv_3 in Henq; auto).

        apply notin_get_none in Hnotin_res;
        rewrite Hnotin_res;
        destruct (eq_nat_dec pid pid0).
        subst pid;
        unfold enq_not_inc in Henq;
        unfold binds in Henq;
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in Henq;
        intuition; try discriminate;
        simpl in H9;
        rewrite Hnotin_res in H9; discriminate.
        apply enq_not_inc_subst_neq_inv in Henq; auto;
        try rewrite <-Hlist in *;
        apply Hinv_3 with (pid:=pid0) in Henq; auto.
      
        apply notin_get_none in Hnotin_res;
        rewrite Hnotin_res;
        erewrite <-Hinv_3 with (pid:=pid); eauto;
        try rewrite <-Hlist in *;
        unfold enq_not_inc; auto.
      (* inv_3' *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [Hinv_3 _]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_3'; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        intros pid0 Henq.

        inversion H3; subst; simpl in *.

        all : pose proof Hbinds0 as HbindsTmp;
        inversion H2; subst; simpl in *;
        inversion H4; subst; simpl in *;
        inversion H6; subst; simpl in *;
        inversion H5; subst; simpl in *;
        try (inversion H8; subst; simpl in *);
        try (inversion H7; subst; simpl in *);
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];

        unfold inv_3' in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_3;
        repeat rewrite get_r'_dist in Hinv_3; auto;
        repeat rewrite get_f'_dist in Hinv_3; auto;
        simpl in Hinv_3;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.
        all : try (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        exfalso;
        eapply deq_not_inc_subst_normal_false; eauto; solve_normal);
        apply deq_not_inc_subst_neq_inv in Henq; auto;
        rewrite <-Hlist in Hinv_3;
        apply Hinv_3 in Henq; auto).

        apply notin_get_none in Hnotin_res;
        rewrite Hnotin_res;
        destruct (eq_nat_dec pid pid0).
        subst pid;
        unfold deq_not_inc in Henq;
        unfold binds in Henq;
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in Henq;
        intuition; try discriminate;
        simpl in H9;
        rewrite Hnotin_res in H9; discriminate.
        apply deq_not_inc_subst_neq_inv in Henq; auto;
        try rewrite <-Hlist in *;
        apply Hinv_3 with (pid:=pid0) in Henq; auto.
      
        apply notin_get_none in Hnotin_res;
        rewrite Hnotin_res;
        erewrite <-Hinv_3 with (pid:=pid); eauto;
        try rewrite <-Hlist in *;
        unfold deq_not_inc; auto.
      (* inv_4 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_4 _]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_4; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H3; subst; simpl in *.
        all :
        inversion H2; subst; simpl in *;
        inversion H4; subst; simpl in *;
        inversion H6; subst; simpl in *;
        inversion H5; subst; simpl in *;
        try (inversion H8; subst; simpl in *);
        try (inversion H7; subst; simpl in *);
        pose proof Hbinds0 as HbindsTmp;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        unfold inv_4 in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_4;
        repeat rewrite get_r'_dist in Hinv_4; auto;
        repeat rewrite get_f'_dist in Hinv_4; auto;
        simpl in Hinv_4;
        rewrite Hlist at 1;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        rewrite <-Hlist in Hinv_4;
        simpl; intuition.
        all : try (apply notin_get_none in Hnotin_res;
        rewrite Hnotin_res in H9;
        intuition;
        apply H11 with (pid:=pid);
        unfold enq_not_inc; intuition).
        all : try (apply notin_get_none in Hnotin_res;
        try (rewrite Hnotin_res in H9);
        try (rewrite Hnotin_res in H7);
        destruct (eq_nat_dec pid pid0);
        [subst pid;
        unfold enq_not_inc in H8;
        unfold binds in H8;
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in H8;
        intuition; try discriminate;
        simpl in H10;
        rewrite Hnotin_res in H10; discriminate|
        try (eapply enq_not_inc_subst_neq_inv in H11);
        try (eapply enq_not_inc_subst_neq_inv in H10);
        try (eapply enq_not_inc_subst_neq_inv in H9);
        try (eapply enq_not_inc_subst_neq_inv in H8);
        eauto]).
        all : try (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        eapply enq_not_inc_subst_normal_false; eauto; solve_normal);
        try (eapply enq_not_inc_subst_neq_inv in H11);
        try (eapply enq_not_inc_subst_neq_inv in H9);
        eauto).
      (* inv_4' *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_4 _]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_4'; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H3; subst; simpl in *.
        all :
        inversion H2; subst; simpl in *;
        inversion H4; subst; simpl in *;
        inversion H6; subst; simpl in *;
        inversion H5; subst; simpl in *;
        try (inversion H8; subst; simpl in *);
        try (inversion H7; subst; simpl in *);
        pose proof Hbinds0 as HbindsTmp;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        unfold inv_4' in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_4;
        repeat rewrite get_r'_dist in Hinv_4; auto;
        repeat rewrite get_f'_dist in Hinv_4; auto;
        simpl in Hinv_4;
        rewrite Hlist at 1;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        rewrite <-Hlist in Hinv_4;
        simpl; intuition.
        all : try (apply notin_get_none in Hnotin_res;
        rewrite Hnotin_res in H9;
        intuition;
        apply H11 with (pid:=pid);
        unfold deq_not_inc; intuition).
        all : try (apply notin_get_none in Hnotin_res;
        try (rewrite Hnotin_res in H9);
        try (rewrite Hnotin_res in H7);
        destruct (eq_nat_dec pid pid0);
        [subst pid;
        unfold deq_not_inc in H8;
        unfold binds in H8;
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in H8;
        intuition; try discriminate;
        simpl in H10;
        rewrite Hnotin_res in H10; discriminate|
        try (eapply deq_not_inc_subst_neq_inv in H11);
        try (eapply deq_not_inc_subst_neq_inv in H10);
        try (eapply deq_not_inc_subst_neq_inv in H9);
        try (eapply deq_not_inc_subst_neq_inv in H8);
        eauto]).
        all : try (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        eapply deq_not_inc_subst_normal_false; eauto; solve_normal);
        try (eapply deq_not_inc_subst_neq_inv in H11);
        try (eapply deq_not_inc_subst_neq_inv in H9);
        eauto).
      (* inv_5 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_5 _]]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_5; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        intros pid0 Henq.
        inversion H3; subst; simpl in *.
        all :
        inversion H2; subst; simpl in *;
        inversion H4; subst; simpl in *;
        inversion H6; subst; simpl in *;
        inversion H5; subst; simpl in *;
        try (inversion H8; subst; simpl in *);
        try (inversion H7; subst; simpl in *);
        pose proof Hbinds0 as HbindsTmp;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        unfold inv_5 in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_5;
        repeat rewrite get_r'_dist in Hinv_5; auto;
        repeat rewrite get_f'_dist in Hinv_5; auto;
        simpl in Hinv_5;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.
        all : try (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        exfalso;
        eapply enq_not_inc_subst_normal_false; eauto; solve_normal);
        apply enq_not_inc_subst_neq_inv in Henq; auto;
        rewrite <-Hlist in Hinv_5;
        apply Hinv_5 in Henq; auto).
        all : try (apply notin_get_none in Hnotin_res;
        rewrite Hnotin_res;
        destruct (eq_nat_dec pid pid0);
        [subst pid;
        unfold enq_not_inc in Henq;
        unfold binds in Henq;
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in Henq;
        intuition; try discriminate;
        simpl in H9;
        rewrite Hnotin_res in H9; discriminate|
        apply enq_not_inc_subst_neq_inv in Henq; auto;
        rewrite <-Hlist in Hinv_5;
        apply Hinv_5 in Henq; auto]).
        all : try (apply notin_get_none in Hnotin_res;
        rewrite Hnotin_res;
        rewrite <-Hlist in Hinv_5;
        apply Hinv_5 with (pid:=pid); eauto;
        unfold enq_not_inc; intuition).
        all : apply notin_get_none in Hnotin_res;
        rewrite Hnotin_res; intuition.
      (* inv_5' *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_5 _]]]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_5'; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        intros pid0 Henq.
        inversion H3; subst; simpl in *.
        all :
        inversion H2; subst; simpl in *;
        inversion H4; subst; simpl in *;
        inversion H6; subst; simpl in *;
        inversion H5; subst; simpl in *;
        try (inversion H8; subst; simpl in *);
        try (inversion H7; subst; simpl in *);
        pose proof Hbinds0 as HbindsTmp;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        unfold inv_5' in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_5;
        repeat rewrite get_r'_dist in Hinv_5; auto;
        repeat rewrite get_f'_dist in Hinv_5; auto;
        simpl in Hinv_5;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.
        all : try (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        exfalso;
        eapply deq_not_inc_subst_normal_false; eauto; solve_normal);
        apply deq_not_inc_subst_neq_inv in Henq; auto;
        rewrite <-Hlist in Hinv_5;
        apply Hinv_5 in Henq; auto).
        all : try (apply notin_get_none in Hnotin_res;
        rewrite Hnotin_res;
        destruct (eq_nat_dec pid pid0);
        [subst pid;
        unfold deq_not_inc in Henq;
        unfold binds in Henq;
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in Henq;
        intuition; try discriminate;
        simpl in H9;
        rewrite Hnotin_res in H9; discriminate|
        apply deq_not_inc_subst_neq_inv in Henq; auto;
        rewrite <-Hlist in Hinv_5;
        apply Hinv_5 in Henq; auto]).
        all : try (apply notin_get_none in Hnotin_res;
        rewrite Hnotin_res;
        rewrite <-Hlist in Hinv_5;
        apply Hinv_5 with (pid:=pid); eauto;
        unfold deq_not_inc; intuition).
        all : apply notin_get_none in Hnotin_res;
        rewrite Hnotin_res; intuition.
      (* inv_6 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_6 _]]]]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_6; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H3; subst; simpl in *;
        inversion H2; subst; simpl in *;
        inversion H4; subst; simpl in *;
        inversion H6; subst; simpl in *;
        inversion H5; subst; simpl in *;
        try (inversion H8; subst; simpl in *);
        try (inversion H7; subst; simpl in *);
        apply notin_get_none in Hnotin_res;
        try (rewrite Hnotin_res);
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        unfold inv_6 in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_6;
        repeat rewrite get_r'_dist in Hinv_6; auto;
        repeat rewrite get_f'_dist in Hinv_6; auto;
        simpl in Hinv_6;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.
        all : rewrite Hnotin_res; intuition.
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hinv_range]]]]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H0; subst; simpl in *.
        unfold inv_range; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H3; subst; simpl in *;
        inversion H2; subst; simpl in *;
        inversion H4; subst; simpl in *;
        inversion H6; subst; simpl in *;
        inversion H5; subst; simpl in *;
        try (inversion H8; subst; simpl in *);
        try (inversion H7; subst; simpl in *);
        apply notin_get_none in Hnotin_res;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        unfold inv_range in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_range;
        repeat rewrite get_r'_dist in Hinv_range; auto;
        repeat rewrite get_f'_dist in Hinv_range; auto;
        simpl in Hinv_range;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.
        all : rewrite Hnotin_res; intuition.
    -- inversion H3; subst; clear H3.
      unfold inv_total.
      intuition.
      (* inv_e28 *)
      --- unfold inv_e28_clean.
        intros.
        pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [Hinv_e28 [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_6 Hinv_range']]]]]]]]]]]]].
        destruct (eq_nat_dec pid0 pid).
        + subst.
          inversion H1; subst; simpl in *.
          inversion H4; subst; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          unfold binds in H0.
          inversion H5; subst; simpl in *;
          pose proof Hbinds0 as Hbinds_e27;
          eapply substitute_eq_binds_v' in Hbinds0;
          rewrite Hbinds0 in H0; try discriminate.
        + unfold inv_e28_clean in Hinv_e28.
          inversion H1; subst; simpl in *.
          inversion H4; subst; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
          inversion H5; subst; simpl in *.
          all : apply substitute_neq_preserves_binds' in H0; auto;
          inversion H3; subst; simpl in *;
          inversion H6; subst; simpl in *;
          inversion H8; subst; simpl in *;
          inversion H7; subst; simpl in *;
          try (inversion H10; subst; simpl in *);
          try (inversion H9; subst; simpl in *);
          try (apply notin_get_none in Hnotin_res);
          apply Hinv_e28 in H0; auto;
          apply binds_reconstruct in Hbinds0;
          destruct Hbinds0 as [l1 [l2 Hlist]];
          apply reachable_len_to_reachable in HreachTmp;
          apply array_queue_wf_invarint in HreachTmp;
          unfold array_queue_wf in HreachTmp;
          simpl in HreachTmp;
          rewrite Hlist in HreachTmp;
          apply ok_remove_middle_inv in HreachTmp;
          destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
          apply ok_concat_inv in Hokl;
          destruct Hokl as [Hokl1 Hokl2];
          rewrite Hlist;
          rewrite substitute_notin_app; auto;
          repeat rewrite get_r'_dist; auto;
          repeat rewrite get_f'_dist; auto;
          simpl;
          try (rewrite Hnotin_res);
          rewrite Nat.eqb_refl;
          simpl;
          rewrite Hlist in H0;
          repeat rewrite get_r'_dist in H0; auto;
          repeat rewrite get_f'_dist in H0; auto;
          try (rewrite get_r'_any_ary_remove; auto);
          try (rewrite get_r'_any_ary_remove; auto);
          try (rewrite get_r'_any_rear_remove; auto);
          try (rewrite get_r'_any_rear_remove; auto);
          try (rewrite get_f'_any_ary_remove; auto);
          try (rewrite get_f'_any_ary_remove; auto);
          try (rewrite get_f'_any_rear_remove; auto);
          try (rewrite get_f'_any_rear_remove; auto).
          simpl in H0;
          unfold binds in Hbinds4;
          rewrite Hbinds4 in H0;
          destruct ret; auto.
          simpl in H0; auto;
          unfold binds in Hbinds6;
          rewrite Hbinds6 in H0; auto.
          simpl in H0;
          unfold binds in Hbinds4;
          rewrite Hbinds4 in H0;
          destruct ret; auto.
          simpl in H0; auto;
          unfold binds in Hbinds6;
          rewrite Hbinds6 in H0; auto.
      (* inv_d28 *)
      --- unfold inv_d28_clean.
        intros.
        pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [Hinv_e28 [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_6 Hinv_range']]]]]]]]]]]]].
        destruct (eq_nat_dec pid0 pid).
        + subst.
          inversion H1; subst; simpl in *.
          inversion H4; subst; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          unfold binds in H0.
          inversion H5; subst; simpl in *;
          pose proof Hbinds0 as Hbinds_e27;
          eapply substitute_eq_binds_v' in Hbinds0;
          rewrite Hbinds0 in H0; try discriminate.
        + unfold inv_d28_clean in Hinv_e28.
          inversion H1; subst; simpl in *.
          inversion H4; subst; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_ary, get_pc in *; simpl in *.
          inversion H5; subst; simpl in *.
          all : apply substitute_neq_preserves_binds' in H0; auto;
          inversion H3; subst; simpl in *;
          inversion H6; subst; simpl in *;
          inversion H8; subst; simpl in *;
          inversion H7; subst; simpl in *;
          try (inversion H10; subst; simpl in *);
          try (inversion H9; subst; simpl in *);
          try (apply notin_get_none in Hnotin_res);
          apply Hinv_e28 in H0; auto;
          apply binds_reconstruct in Hbinds0;
          destruct Hbinds0 as [l1 [l2 Hlist]];
          apply reachable_len_to_reachable in HreachTmp;
          apply array_queue_wf_invarint in HreachTmp;
          unfold array_queue_wf in HreachTmp;
          simpl in HreachTmp;
          rewrite Hlist in HreachTmp;
          apply ok_remove_middle_inv in HreachTmp;
          destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
          apply ok_concat_inv in Hokl;
          destruct Hokl as [Hokl1 Hokl2];
          rewrite Hlist;
          rewrite substitute_notin_app; auto;
          repeat rewrite get_r'_dist; auto;
          repeat rewrite get_f'_dist; auto;
          simpl;
          try (rewrite Hnotin_res);
          rewrite Nat.eqb_refl;
          simpl;
          rewrite Hlist in H0;
          repeat rewrite get_r'_dist in H0; auto;
          repeat rewrite get_f'_dist in H0; auto;
          try (rewrite get_r'_any_ary_remove; auto);
          try (rewrite get_r'_any_ary_remove; auto);
          try (rewrite get_r'_any_rear_remove; auto);
          try (rewrite get_r'_any_rear_remove; auto);
          try (rewrite get_f'_any_ary_remove; auto);
          try (rewrite get_f'_any_ary_remove; auto);
          try (rewrite get_f'_any_rear_remove; auto);
          try (rewrite get_f'_any_rear_remove; auto).
          simpl in H0;
          unfold binds in Hbinds4;
          rewrite Hbinds4 in H0;
          destruct ret; auto.
          simpl in H0; auto;
          unfold binds in Hbinds6;
          rewrite Hbinds6 in H0; auto.
          simpl in H0;
          unfold binds in Hbinds4;
          rewrite Hbinds4 in H0;
          destruct ret; auto.
          simpl in H0; auto;
          unfold binds in Hbinds6;
          rewrite Hbinds6 in H0; auto.
      (* inv_1 *)
      --- unfold inv_1.
        pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [Hinv_1 _]]].
          inversion H1; subst; simpl in *.
          inversion H2; subst; simpl in *.
          unfold inv_1 in *; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          inversion H3; subst; simpl in *.

          all : pose proof Hbinds0 as HbindsTmp;
          apply binds_reconstruct in Hbinds0;
          inversion H0; subst; simpl in *;
          inversion H4; subst; simpl in *;
          inversion H6; subst; simpl in *;
          inversion H5; subst; simpl in *;
          try (inversion H8; subst; simpl in *);
          try (inversion H7; subst; simpl in *);
          destruct Hbinds0 as [l1 [l2 Hlist]];
          rewrite Hlist in Hinv_1 at 1 2;
          repeat rewrite get_r'_dist in Hinv_1; auto;
          repeat rewrite get_f'_dist in Hinv_1; auto;
          simpl in Hinv_1;
          apply reachable_len_to_reachable in HreachTmp;
          apply array_queue_wf_invarint in HreachTmp;
          unfold array_queue_wf in HreachTmp;
          simpl in HreachTmp;
          rewrite Hlist in HreachTmp;
          apply ok_remove_middle_inv in HreachTmp;
          destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
          apply ok_concat_inv in Hokl;
          destruct Hokl as [Hokl1 Hokl2];
          rewrite Hlist at 1 2;
          rewrite substitute_notin_app; auto;
          repeat rewrite get_r'_dist; auto;
          repeat rewrite get_f'_dist; auto;
          simpl;
          rewrite Nat.eqb_refl;
          simpl in *;
          try (rewrite get_r'_any_ary_remove; auto);
          try (rewrite get_r'_any_ary_remove; auto);
          try (rewrite get_r'_any_rear_remove; auto);
          try (rewrite get_r'_any_rear_remove; auto);
          try (rewrite get_f'_any_ary_remove; auto);
          try (rewrite get_f'_any_ary_remove; auto);
          try (rewrite get_f'_any_rear_remove; auto);
          try (rewrite get_f'_any_rear_remove; auto);
          try (unfold binds in Hbinds4);
          try (unfold binds in Hbinds6);
          try (rewrite Hbinds4 in Hinv_1);
          try (rewrite Hbinds6 in Hinv_1);
          try rewrite <-Hlist in *;
          intuition.
          all :
          try (
          try (destruct H12 as [pid0 [Hpid1 Hpid2]]);
          try (destruct H10 as [pid0 [Hpid1 Hpid2]]);
          exists pid0;
          intuition;
          [
            destruct (eq_nat_dec pid pid0);
          [
            subst pid;
          exfalso;
          unfold enq_not_inc in Hpid1;
          unfold binds in Hpid1;
          rewrite HbindsTmp in Hpid1;
          intuition; discriminate
          |
          eapply enq_not_inc_subst_neq; eauto;
          try (eapply enq_not_inc_remove_rear_neq; eauto);
          try (eapply enq_not_inc_remove_ary_neq; auto)
          ]
          |
          try (apply Hpid2 in H11; auto);
          try (apply Hpid2 in H9; auto);
          destruct (eq_nat_dec pid pid');
          [subst pid;
          exfalso;
          try (eapply enq_not_inc_subst_normal_false in H12; eauto; solve_normal);
          try (eapply enq_not_inc_subst_normal_false in H10; eauto; solve_normal)|
          eapply enq_not_inc_subst_neq_inv in H12; eauto;
          try (eapply enq_not_inc_remove_rear_neq_inv; eauto);
          try (eapply enq_not_inc_remove_rear_neq_inv; eauto)
          ]]).

          try (destruct H12 as [pid0 [Hpid1 Hpid2]]);
          try (destruct H10 as [pid0 [Hpid1 Hpid2]]);
          exists pid0;
          intuition;
          [
            destruct (eq_nat_dec pid pid0);
          [
            subst pid;
          exfalso;
          unfold enq_not_inc in Hpid1;
          unfold binds in Hpid1;
          rewrite HbindsTmp in Hpid1;
          intuition; discriminate
          |
          eapply enq_not_inc_subst_neq; eauto;
          eapply enq_not_inc_remove_ary_neq; auto
          ]
          |
          try (apply Hpid2 in H11; auto);
          try (apply Hpid2 in H9; auto);
          destruct (eq_nat_dec pid pid');
          [subst pid;
          exfalso;
          try (eapply enq_not_inc_subst_normal_false in H12; eauto; solve_normal);
          try (eapply enq_not_inc_subst_normal_false in H10; eauto; solve_normal)|
          eapply enq_not_inc_subst_neq_inv in H10; eauto;
          eapply enq_not_inc_remove_ary_neq_inv; eauto
          ]].

          all : try (try (destruct H12 as [pid0 [Hpid1 Hpid2]]);
          try (destruct H10 as [pid0 [Hpid1 Hpid2]]);
          destruct (eq_nat_dec pid pid0);
          [subst pid;
          exists pid0;
          intuition;
          [
            unfold enq_not_inc in *;
          unfold binds in Hpid1;
          rewrite HbindsTmp in Hpid1;
          intuition; try discriminate;
          simpl in H13;
          apply notin_get_none in H13;
          rewrite Hbinds6 in H13; discriminate
          |
          apply enq_not_inc_subst_neq_inv in H12; auto;
          apply enq_not_inc_remove_rear_neq_inv in H12; auto;
          apply Hpid2 in H11; auto]|
          exists pid0;
          intuition;
          try (apply enq_not_inc_subst_neq; auto;
          apply enq_not_inc_remove_rear_neq; auto);
          destruct (eq_nat_dec pid' pid);
          [subst pid';
          unfold enq_not_inc in H12;
          unfold binds in H12;
          pose proof HbindsTmp as HbindsTmp';
          eapply substitute_eq_binds_v' in HbindsTmp;
          rewrite HbindsTmp in H12;
          intuition; try discriminate|
          apply enq_not_inc_subst_neq_inv in H12; auto;
          apply enq_not_inc_remove_rear_neq_inv in H12; auto;
          apply Hpid2 in H11; auto]]).

          all : try (destruct H12 as [pid0 [Hpid1 Hpid2]]);
          try (destruct H10 as [pid0 [Hpid1 Hpid2]]);
          destruct (eq_nat_dec pid pid0);
          [subst pid;
          exists pid0;
          intuition;
          [unfold enq_not_inc in *;
          unfold binds in Hpid1;
          rewrite HbindsTmp in Hpid1;
          intuition; try discriminate;
          simpl in H11;
          rewrite Hbinds4 in H11;
          inversion H11;
          subst ret; simpl in *;
          right; left;
          eapply substitute_eq_binds_v'; eauto|
          apply enq_not_inc_subst_neq_inv in H10; auto;
          apply enq_not_inc_remove_ary_neq_inv in H10; auto;
          apply Hpid2 in H9; auto]|
          exists pid0;
          intuition;
          try (apply enq_not_inc_subst_neq; auto;
          apply enq_not_inc_remove_ary_neq; auto);
          destruct (eq_nat_dec pid' pid);
          [subst pid';
          unfold enq_not_inc in H10;
          unfold binds in H10;
          pose proof HbindsTmp as HbindsTmp';
          eapply substitute_eq_binds_v' in HbindsTmp;
          rewrite HbindsTmp in H10;
          intuition; try discriminate;
          inversion H10; subst ret; simpl in *;
          apply Hpid2 in H9; auto;
          unfold enq_not_inc; intuition;
          apply enq_not_inc_subst_neq_inv in H10; auto;
          apply enq_not_inc_remove_ary_neq_inv in H10; auto;
          apply Hpid2 in H9; auto|
          apply enq_not_inc_subst_neq_inv in H10; auto;
          apply enq_not_inc_remove_ary_neq_inv in H10; auto;
          apply Hpid2 in H9; auto]].
      (* inv_1' *)
      --- unfold inv_1'.
        pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [Hinv_1 _]]]].
          inversion H1; subst; simpl in *.
          inversion H2; subst; simpl in *.
          unfold inv_1' in *; simpl in *.
          unfold F, R in *; simpl in *.
          unfold get_front, get_rear, get_pc, get_ary in *; simpl in *.
          inversion H3; subst; simpl in *.

          all : pose proof Hbinds0 as HbindsTmp;
          apply binds_reconstruct in Hbinds0;
          inversion H0; subst; simpl in *;
          inversion H4; subst; simpl in *;
          inversion H6; subst; simpl in *;
          inversion H5; subst; simpl in *;
          try (inversion H8; subst; simpl in *);
          try (inversion H7; subst; simpl in *);
          destruct Hbinds0 as [l1 [l2 Hlist]];
          rewrite Hlist in Hinv_1 at 1 2;
          repeat rewrite get_r'_dist in Hinv_1; auto;
          repeat rewrite get_f'_dist in Hinv_1; auto;
          simpl in Hinv_1;
          apply reachable_len_to_reachable in HreachTmp;
          apply array_queue_wf_invarint in HreachTmp;
          unfold array_queue_wf in HreachTmp;
          simpl in HreachTmp;
          rewrite Hlist in HreachTmp;
          apply ok_remove_middle_inv in HreachTmp;
          destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
          apply ok_concat_inv in Hokl;
          destruct Hokl as [Hokl1 Hokl2];
          rewrite Hlist at 1 2;
          rewrite substitute_notin_app; auto;
          repeat rewrite get_r'_dist; auto;
          repeat rewrite get_f'_dist; auto;
          simpl;
          rewrite Nat.eqb_refl;
          simpl in *;
          try (rewrite get_r'_any_ary_remove; auto);
          try (rewrite get_r'_any_ary_remove; auto);
          try (rewrite get_r'_any_rear_remove; auto);
          try (rewrite get_r'_any_rear_remove; auto);
          try (rewrite get_f'_any_ary_remove; auto);
          try (rewrite get_f'_any_ary_remove; auto);
          try (rewrite get_f'_any_rear_remove; auto);
          try (rewrite get_f'_any_rear_remove; auto);
          try (unfold binds in Hbinds4);
          try (unfold binds in Hbinds6);
          try (rewrite Hbinds4 in Hinv_1);
          try (rewrite Hbinds6 in Hinv_1);
          try rewrite <-Hlist in *;
          intuition.
          all :
          try (
          try (destruct H12 as [pid0 [Hpid1 Hpid2]]);
          try (destruct H10 as [pid0 [Hpid1 Hpid2]]);
          exists pid0;
          intuition;
          [
            destruct (eq_nat_dec pid pid0);
          [
            subst pid;
          exfalso;
          unfold deq_not_inc in Hpid1;
          unfold binds in Hpid1;
          rewrite HbindsTmp in Hpid1;
          intuition; discriminate
          |
          eapply deq_not_inc_subst_neq; eauto;
          try (eapply deq_not_inc_remove_rear_neq; eauto);
          try (eapply deq_not_inc_remove_ary_neq; auto)
          ]
          |
          try (apply Hpid2 in H11; auto);
          try (apply Hpid2 in H9; auto);
          destruct (eq_nat_dec pid pid');
          [subst pid;
          exfalso;
          try (eapply deq_not_inc_subst_normal_false in H12; eauto; solve_normal);
          try (eapply deq_not_inc_subst_normal_false in H10; eauto; solve_normal)|
          eapply deq_not_inc_subst_neq_inv in H12; eauto;
          try (eapply deq_not_inc_remove_rear_neq_inv; eauto);
          try (eapply deq_not_inc_remove_rear_neq_inv; eauto)
          ]]).

          try (destruct H12 as [pid0 [Hpid1 Hpid2]]);
          try (destruct H10 as [pid0 [Hpid1 Hpid2]]);
          exists pid0;
          intuition;
          [
            destruct (eq_nat_dec pid pid0);
          [
            subst pid;
          exfalso;
          unfold deq_not_inc in Hpid1;
          unfold binds in Hpid1;
          rewrite HbindsTmp in Hpid1;
          intuition; discriminate
          |
          eapply deq_not_inc_subst_neq; eauto;
          eapply deq_not_inc_remove_ary_neq; auto
          ]
          |
          try (apply Hpid2 in H11; auto);
          try (apply Hpid2 in H9; auto);
          destruct (eq_nat_dec pid pid');
          [subst pid;
          exfalso;
          try (eapply deq_not_inc_subst_normal_false in H12; eauto; solve_normal);
          try (eapply deq_not_inc_subst_normal_false in H10; eauto; solve_normal)|
          eapply deq_not_inc_subst_neq_inv in H10; eauto;
          eapply deq_not_inc_remove_ary_neq_inv; eauto
          ]].

          all : try (try (destruct H12 as [pid0 [Hpid1 Hpid2]]);
          try (destruct H10 as [pid0 [Hpid1 Hpid2]]);
          destruct (eq_nat_dec pid pid0);
          [subst pid;
          exists pid0;
          intuition;
          [
            unfold deq_not_inc in *;
          unfold binds in Hpid1;
          rewrite HbindsTmp in Hpid1;
          intuition; try discriminate;
          simpl in H13;
          apply notin_get_none in H13;
          rewrite Hbinds6 in H13; discriminate
          |
          apply deq_not_inc_subst_neq_inv in H12; auto;
          apply deq_not_inc_remove_rear_neq_inv in H12; auto;
          apply Hpid2 in H11; auto]|
          exists pid0;
          intuition;
          try (apply deq_not_inc_subst_neq; auto;
          apply deq_not_inc_remove_rear_neq; auto);
          destruct (eq_nat_dec pid' pid);
          [subst pid';
          unfold deq_not_inc in H12;
          unfold binds in H12;
          pose proof HbindsTmp as HbindsTmp';
          eapply substitute_eq_binds_v' in HbindsTmp;
          rewrite HbindsTmp in H12;
          intuition; try discriminate|
          apply deq_not_inc_subst_neq_inv in H12; auto;
          apply deq_not_inc_remove_rear_neq_inv in H12; auto;
          apply Hpid2 in H11; auto]]).

          all : try (destruct H12 as [pid0 [Hpid1 Hpid2]]);
          try (destruct H10 as [pid0 [Hpid1 Hpid2]]);
          destruct (eq_nat_dec pid pid0);
          [subst pid;
          exists pid0;
          intuition;
          [unfold deq_not_inc in *;
          unfold binds in Hpid1;
          rewrite HbindsTmp in Hpid1;
          intuition; try discriminate;
          simpl in H11;
          rewrite Hbinds4 in H11;
          inversion H11;
          subst ret; simpl in *;
          right; left;
          eapply substitute_eq_binds_v'; eauto|
          apply deq_not_inc_subst_neq_inv in H10; auto;
          apply deq_not_inc_remove_ary_neq_inv in H10; auto;
          apply Hpid2 in H9; auto]|
          exists pid0;
          intuition;
          try (apply deq_not_inc_subst_neq; auto;
          apply deq_not_inc_remove_ary_neq; auto);
          destruct (eq_nat_dec pid' pid);
          [subst pid';
          unfold deq_not_inc in H10;
          unfold binds in H10;
          pose proof HbindsTmp as HbindsTmp';
          eapply substitute_eq_binds_v' in HbindsTmp;
          rewrite HbindsTmp in H10;
          intuition; try discriminate;
          inversion H10; subst ret; simpl in *;
          apply Hpid2 in H9; auto;
          unfold deq_not_inc; intuition;
          apply deq_not_inc_subst_neq_inv in H10; auto;
          apply deq_not_inc_remove_ary_neq_inv in H10; auto;
          apply Hpid2 in H9; auto|
          apply deq_not_inc_subst_neq_inv in H10; auto;
          apply deq_not_inc_remove_ary_neq_inv in H10; auto;
          apply Hpid2 in H9; auto]].
      (* inv_2 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [Hinv_2 _]]]]].
        inversion H1; subst; simpl in *.
        inversion H2; subst; simpl in *.
        unfold inv_2; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H3; subst; simpl in *;
        inversion H0; subst; simpl in *;
        inversion H4; subst; simpl in *;
        inversion H6; subst; simpl in *;
        inversion H5; subst; simpl in *;
        try (inversion H8; subst; simpl in *);
        try (inversion H7; subst; simpl in *);
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        apply ok_concat_inv in Hokl;
        destruct Hokl as [Hokl1 Hokl2];
        unfold inv_2 in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_2;
        repeat rewrite get_r'_dist in Hinv_2; auto;
        repeat rewrite get_f'_dist in Hinv_2; auto;
        simpl in Hinv_2;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.
        all : try (rewrite get_r'_any_rear_remove; auto;
        rewrite get_r'_any_rear_remove; auto).
        all : try (rewrite get_r'_any_ary_remove; auto;
        rewrite get_r'_any_ary_remove; auto).
        unfold binds in Hbinds4.
        all :
          try (rewrite Hbinds4 in H7; intuition);
          try (rewrite Hbinds6 in H9; intuition).
      (* inv_2' *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [Hinv_2 _]]]]]].
        inversion H1; subst; simpl in *.
        inversion H2; subst; simpl in *.
        unfold inv_2'; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H3; subst; simpl in *;
        inversion H0; subst; simpl in *;
        inversion H4; subst; simpl in *;
        inversion H6; subst; simpl in *;
        inversion H5; subst; simpl in *;
        try (inversion H8; subst; simpl in *);
        try (inversion H7; subst; simpl in *);
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        apply ok_concat_inv in Hokl;
        destruct Hokl as [Hokl1 Hokl2];
        unfold inv_2' in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_2;
        repeat rewrite get_r'_dist in Hinv_2; auto;
        repeat rewrite get_f'_dist in Hinv_2; auto;
        simpl in Hinv_2;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; intuition.
        all : try (rewrite get_f'_any_rear_remove; auto;
        rewrite get_f'_any_rear_remove; auto).
        all : try (rewrite get_f'_any_ary_remove; auto;
        rewrite get_f'_any_ary_remove; auto).
        unfold binds in Hbinds4.
        all :
          try (rewrite Hbinds4 in H7; intuition);
          try (rewrite Hbinds6 in H9; intuition).
      (* inv_3 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [Hinv_3 _]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H2; subst; simpl in *.
        unfold inv_3; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        intros pid0 Henq.
        inversion H3; subst; simpl in *.
        all : pose proof Hbinds0 as HbindsTmp;
        inversion H0; subst; simpl in *;
        inversion H4; subst; simpl in *;
        inversion H6; subst; simpl in *;
        inversion H5; subst; simpl in *;
        try (inversion H8; subst; simpl in *);
        try (inversion H7; subst; simpl in *);
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        apply ok_concat_inv in Hokl;
        destruct Hokl as [Hokl1 Hokl2];
        unfold inv_3 in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_3;
        repeat rewrite get_r'_dist in Hinv_3; auto;
        repeat rewrite get_f'_dist in Hinv_3; auto;
        simpl in Hinv_3;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; 
        try (rewrite get_r'_any_rear_remove; auto);
        try (rewrite get_r'_any_rear_remove; auto);
        try (rewrite get_r'_any_ary_remove; auto);
        try (rewrite get_r'_any_ary_remove; auto);
        intuition.
        all : try (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        exfalso;
        eapply enq_not_inc_subst_normal_false; eauto; solve_normal);
        apply enq_not_inc_subst_neq_inv in Henq; auto;
        rewrite <-Hlist in Hinv_3;
        apply Hinv_3 in Henq; auto).
        all : try (destruct (eq_nat_dec pid pid0);
        [subst pid;
        unfold enq_not_inc in Henq;
        unfold binds in Henq;
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in Henq;
        intuition; try discriminate;
        simpl in H9;
        rewrite Hnotin_res in H9; discriminate|
        apply enq_not_inc_subst_neq_inv in Henq; auto;
        try rewrite <-Hlist in *;
        try (apply enq_not_inc_remove_rear_neq_inv in Henq; auto);
        try (apply enq_not_inc_remove_ary_neq_inv in Henq; auto);
        apply Hinv_3 with (pid:=pid0) in Henq; auto]).
        unfold binds in Hbinds4;
        rewrite Hbinds4 in Hinv_3;
        destruct (eq_nat_dec pid pid0).
        subst pid;
        unfold enq_not_inc in Henq;
        unfold binds in Henq;
        pose proof HbindsTmp as HbindsTmp';
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in Henq;
        intuition; try discriminate;
        inversion H8; subst ret; simpl in *;
        erewrite <-Hinv_3 with (pid:=pid0); eauto;
        try rewrite <-Hlist in *;
        unfold enq_not_inc; auto.
        erewrite <-Hinv_3 with (pid:=pid0); eauto;
        try rewrite <-Hlist in *;
        apply enq_not_inc_subst_neq_inv in Henq; auto;
        apply enq_not_inc_remove_ary_neq_inv in Henq; auto.
        unfold binds in Hbinds6;
        rewrite Hbinds6 in Henq; intuition.

      (* inv_3' *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [Hinv_3 _]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H2; subst; simpl in *.
        unfold inv_3'; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        intros pid0 Henq.
        inversion H3; subst; simpl in *.
        all : pose proof Hbinds0 as HbindsTmp;
        inversion H0; subst; simpl in *;
        inversion H4; subst; simpl in *;
        inversion H6; subst; simpl in *;
        inversion H5; subst; simpl in *;
        try (inversion H8; subst; simpl in *);
        try (inversion H7; subst; simpl in *);
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        apply ok_concat_inv in Hokl;
        destruct Hokl as [Hokl1 Hokl2];
        unfold inv_3' in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_3;
        repeat rewrite get_r'_dist in Hinv_3; auto;
        repeat rewrite get_f'_dist in Hinv_3; auto;
        simpl in Hinv_3;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; 
        try (rewrite get_r'_any_rear_remove; auto);
        try (rewrite get_r'_any_rear_remove; auto);
        try (rewrite get_r'_any_ary_remove; auto);
        try (rewrite get_r'_any_ary_remove; auto);
        try (rewrite get_f'_any_rear_remove; auto);
        try (rewrite get_f'_any_rear_remove; auto);
        try (rewrite get_f'_any_ary_remove; auto);
        try (rewrite get_f'_any_ary_remove; auto);
        intuition.
        all : try (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        exfalso;
        eapply deq_not_inc_subst_normal_false; eauto; solve_normal);
        apply deq_not_inc_subst_neq_inv in Henq; auto;
        rewrite <-Hlist in Hinv_3;
        apply Hinv_3 in Henq; auto).
        all : try (destruct (eq_nat_dec pid pid0);
        [subst pid;
        unfold deq_not_inc in Henq;
        unfold binds in Henq;
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in Henq;
        intuition; try discriminate;
        simpl in H9;
        rewrite Hnotin_res in H9; discriminate|
        apply deq_not_inc_subst_neq_inv in Henq; auto;
        try rewrite <-Hlist in *;
        try (apply deq_not_inc_remove_rear_neq_inv in Henq; auto);
        try (apply deq_not_inc_remove_ary_neq_inv in Henq; auto);
        apply Hinv_3 with (pid:=pid0) in Henq; auto]).
        unfold binds in Hbinds4;
        rewrite Hbinds4 in Hinv_3;
        destruct (eq_nat_dec pid pid0).
        subst pid;
        unfold deq_not_inc in Henq;
        unfold binds in Henq;
        pose proof HbindsTmp as HbindsTmp';
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in Henq;
        intuition; try discriminate;
        inversion H8; subst ret; simpl in *;
        erewrite <-Hinv_3 with (pid:=pid0); eauto;
        try rewrite <-Hlist in *;
        unfold deq_not_inc; auto.
        erewrite <-Hinv_3 with (pid:=pid0); eauto;
        try rewrite <-Hlist in *;
        apply deq_not_inc_subst_neq_inv in Henq; auto;
        apply deq_not_inc_remove_ary_neq_inv in Henq; auto.
        unfold binds in Hbinds6;
        rewrite Hbinds6 in Henq; intuition.
      (* inv_4 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_4 _]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H2; subst; simpl in *.
        unfold inv_4; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H3; subst; simpl in *.
        all :
        inversion H0; subst; simpl in *;
        inversion H4; subst; simpl in *;
        inversion H6; subst; simpl in *;
        inversion H5; subst; simpl in *;
        try (inversion H8; subst; simpl in *);
        try (inversion H7; subst; simpl in *);
        pose proof Hbinds0 as HbindsTmp;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        apply ok_concat_inv in Hokl;
        destruct Hokl as [Hokl1 Hokl2];
        unfold inv_4 in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_4;
        repeat rewrite get_r'_dist in Hinv_4; auto;
        repeat rewrite get_f'_dist in Hinv_4; auto;
        simpl in Hinv_4;
        rewrite Hlist at 1;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl;
        try (rewrite get_r'_any_rear_remove; auto);
        try (rewrite get_r'_any_rear_remove; auto);
        try (rewrite get_r'_any_ary_remove; auto);
        try (rewrite get_r'_any_ary_remove; auto);
        try (rewrite get_f'_any_rear_remove; auto);
        try (rewrite get_f'_any_rear_remove; auto);
        try (rewrite get_f'_any_ary_remove; auto);
        try (rewrite get_f'_any_ary_remove; auto);
        rewrite <-Hlist in Hinv_4;
        simpl; intuition.
        all : try (destruct (eq_nat_dec pid pid0);
        [subst pid;
        unfold enq_not_inc in H11;
        unfold binds in H11;
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in H11;
        intuition; try discriminate|
        apply enq_not_inc_subst_neq_inv in H11; auto;
        apply enq_not_inc_remove_rear_neq_inv in H11; auto;
        apply H10 in H11; auto]).
        all : try (
        unfold binds in HbindsTmp;
        try (rewrite Hbinds4 in Hinv_4);
        intuition;
        destruct (eq_nat_dec pid pid0);
        [subst pid;
        unfold enq_not_inc in H9;
        unfold binds in H9;
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in H9;
        intuition; try discriminate|
        apply enq_not_inc_subst_neq_inv in H9; auto;
        try (apply enq_not_inc_remove_ary_neq_inv in H9; auto);
        try (apply enq_not_inc_remove_rear_neq_inv in H9; auto);
        apply H8 in H9; auto]).
        all : try (destruct (eq_nat_dec pid pid0);
        [subst pid;
        unfold enq_not_inc in H11;
        unfold binds in H11;
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in H11;
        intuition; try discriminate|
        apply enq_not_inc_subst_neq_inv in H11; auto;
        apply H10 in H11; auto]).
        unfold binds in HbindsTmp.
        rewrite Hbinds4 in Hinv_4.
        intuition.
        destruct (eq_nat_dec pid pid0).
          subst pid;
        unfold enq_not_inc in H8;
        unfold binds in H8;
        pose proof HbindsTmp as HbindsTmp';
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in H8;
        intuition; try discriminate;
        inversion H8; subst ret; simpl in *;
        apply H9 with (pid:=pid0);
        unfold enq_not_inc; intuition.
        apply enq_not_inc_subst_neq_inv in H8; auto.
        apply enq_not_inc_remove_ary_neq_inv in H8; auto.
        apply H9 in H8; auto.
        unfold binds in HbindsTmp.
        rewrite Hbinds6 in Hinv_4.
        intuition.
        destruct (eq_nat_dec pid pid0).
          subst pid;
        unfold enq_not_inc in H10;
        unfold binds in H10;
        pose proof HbindsTmp as HbindsTmp';
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in H10;
        intuition; try discriminate;
        inversion H10; subst ret; simpl in *;
        apply H9 with (pid:=pid0);
        unfold enq_not_inc; intuition.
        apply enq_not_inc_subst_neq_inv in H10; auto.
        apply enq_not_inc_remove_rear_neq_inv in H10; auto.
        apply H11 in H10; auto.
      (* inv_4' *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_4 _]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H2; subst; simpl in *.
        unfold inv_4'; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H3; subst; simpl in *.
        all :
        inversion H0; subst; simpl in *;
        inversion H4; subst; simpl in *;
        inversion H6; subst; simpl in *;
        inversion H5; subst; simpl in *;
        try (inversion H8; subst; simpl in *);
        try (inversion H7; subst; simpl in *);
        pose proof Hbinds0 as HbindsTmp;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        apply ok_concat_inv in Hokl;
        destruct Hokl as [Hokl1 Hokl2];
        unfold inv_4' in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_4;
        repeat rewrite get_r'_dist in Hinv_4; auto;
        repeat rewrite get_f'_dist in Hinv_4; auto;
        simpl in Hinv_4;
        rewrite Hlist at 1;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl;
        try (rewrite get_r'_any_rear_remove; auto);
        try (rewrite get_r'_any_rear_remove; auto);
        try (rewrite get_r'_any_ary_remove; auto);
        try (rewrite get_r'_any_ary_remove; auto);
        try (rewrite get_f'_any_rear_remove; auto);
        try (rewrite get_f'_any_rear_remove; auto);
        try (rewrite get_f'_any_ary_remove; auto);
        try (rewrite get_f'_any_ary_remove; auto);
        rewrite <-Hlist in Hinv_4;
        simpl; intuition.
        all : try (destruct (eq_nat_dec pid pid0);
        [subst pid;
        unfold deq_not_inc in H11;
        unfold binds in H11;
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in H11;
        intuition; try discriminate|
        apply deq_not_inc_subst_neq_inv in H11; auto;
        apply deq_not_inc_remove_rear_neq_inv in H11; auto;
        apply H10 in H11; auto]).
        all : try (
        unfold binds in HbindsTmp;
        try (rewrite Hbinds4 in Hinv_4);
        intuition;
        destruct (eq_nat_dec pid pid0);
        [subst pid;
        unfold deq_not_inc in H9;
        unfold binds in H9;
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in H9;
        intuition; try discriminate|
        apply deq_not_inc_subst_neq_inv in H9; auto;
        try (apply deq_not_inc_remove_ary_neq_inv in H9; auto);
        try (apply deq_not_inc_remove_rear_neq_inv in H9; auto);
        apply H8 in H9; auto]).
        all : try (destruct (eq_nat_dec pid pid0);
        [subst pid;
        unfold deq_not_inc in H11;
        unfold binds in H11;
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in H11;
        intuition; try discriminate|
        apply deq_not_inc_subst_neq_inv in H11; auto;
        apply H10 in H11; auto]).
        unfold binds in HbindsTmp.
        rewrite Hbinds4 in Hinv_4.
        intuition.
        destruct (eq_nat_dec pid pid0).
          subst pid;
        unfold deq_not_inc in H8;
        unfold binds in H8;
        pose proof HbindsTmp as HbindsTmp';
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in H8;
        intuition; try discriminate;
        inversion H8; subst ret; simpl in *;
        apply H9 with (pid:=pid0);
        unfold deq_not_inc; intuition.
        apply deq_not_inc_subst_neq_inv in H8; auto.
        apply deq_not_inc_remove_ary_neq_inv in H8; auto.
        apply H9 in H8; auto.
        unfold binds in HbindsTmp.
        rewrite Hbinds6 in Hinv_4.
        intuition.
        destruct (eq_nat_dec pid pid0).
          subst pid;
        unfold deq_not_inc in H10;
        unfold binds in H10;
        pose proof HbindsTmp as HbindsTmp';
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in H10;
        intuition; try discriminate;
        inversion H10; subst ret; simpl in *;
        apply H9 with (pid:=pid0);
        unfold deq_not_inc; intuition.
        apply deq_not_inc_subst_neq_inv in H10; auto.
        apply deq_not_inc_remove_rear_neq_inv in H10; auto.
        apply H11 in H10; auto.
      (* inv_5 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_5 _]]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H2; subst; simpl in *.
        unfold inv_5; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        intros pid0 Henq.
        inversion H3; subst; simpl in *.
        all :
        inversion H0; subst; simpl in *;
        inversion H4; subst; simpl in *;
        inversion H6; subst; simpl in *;
        inversion H5; subst; simpl in *;
        try (inversion H8; subst; simpl in *);
        try (inversion H7; subst; simpl in *);
        pose proof Hbinds0 as HbindsTmp;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        apply ok_concat_inv in Hokl;
        destruct Hokl as [Hokl1 Hokl2];
        unfold inv_5 in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_5;
        repeat rewrite get_r'_dist in Hinv_5; auto;
        repeat rewrite get_f'_dist in Hinv_5; auto;
        simpl in Hinv_5;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl;
        try (rewrite get_r'_any_rear_remove; auto);
        try (rewrite get_r'_any_rear_remove; auto);
        try (rewrite get_r'_any_ary_remove; auto);
        try (rewrite get_r'_any_ary_remove; auto);
        try (rewrite get_f'_any_rear_remove; auto);
        try (rewrite get_f'_any_rear_remove; auto);
        try (rewrite get_f'_any_ary_remove; auto);
        try (rewrite get_f'_any_ary_remove; auto);
        simpl; 
        try rewrite <-Hlist in *;
        intuition.
        all : try (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        exfalso;
        eapply enq_not_inc_subst_normal_false; eauto; solve_normal);
        apply enq_not_inc_subst_neq_inv in Henq; auto;
        simpl in *;
        apply Hinv_5 in Henq; auto).
        all : try (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        exfalso;
        eapply enq_not_inc_subst_normal_false; eauto; solve_normal);
        apply enq_not_inc_subst_neq_inv in Henq; auto;
        try (apply enq_not_inc_remove_rear_neq_inv in Henq; auto);
        try (apply enq_not_inc_remove_ary_neq_inv in Henq; auto);
        apply Hinv_5 in Henq; auto).
        unfold binds in Hbinds4;
        try (rewrite Hbinds4 in Hinv_5);
        destruct (eq_nat_dec pid pid0).
        subst pid;
        eapply Hinv_5 with (pid:=pid0); eauto;
        unfold enq_not_inc in *;
        unfold binds in Henq;
        pose proof HbindsTmp as HbindsTmp';
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in Henq;
        intuition; try discriminate;
        inversion H8; subst ret; simpl in *;
        intuition.
        apply enq_not_inc_subst_neq_inv in Henq; auto;
        try (apply enq_not_inc_remove_rear_neq_inv in Henq; auto);
        try (apply enq_not_inc_remove_ary_neq_inv in Henq; auto);
        apply Hinv_5 in Henq; auto.
        unfold binds in Hbinds6;
        try (rewrite Hbinds6 in Hinv_5);
        destruct (eq_nat_dec pid pid0).
        subst pid;
        eapply Hinv_5 with (pid:=pid0); eauto;
        unfold enq_not_inc in *;
        unfold binds in Henq;
        pose proof HbindsTmp as HbindsTmp';
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in Henq;
        intuition; try discriminate;
        inversion H8; subst ret; simpl in *;
        intuition.
        apply enq_not_inc_subst_neq_inv in Henq; auto;
        try (apply enq_not_inc_remove_rear_neq_inv in Henq; auto);
        try (apply enq_not_inc_remove_ary_neq_inv in Henq; auto);
        apply Hinv_5 in Henq; auto.
        unfold binds in Hbinds4;
        try (rewrite Hbinds4 in Henq);
        try (rewrite Hbinds4 in Hinv_5);
        intuition.
        unfold binds in Hbinds6;
        try (rewrite Hbinds6 in Henq);
        try (rewrite Hbinds6 in Hinv_5);
        intuition.
      (* inv_5' *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_5 _]]]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H2; subst; simpl in *.
        unfold inv_5'; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        intros pid0 Henq.
        inversion H3; subst; simpl in *.
        all :
        inversion H0; subst; simpl in *;
        inversion H4; subst; simpl in *;
        inversion H6; subst; simpl in *;
        inversion H5; subst; simpl in *;
        try (inversion H8; subst; simpl in *);
        try (inversion H7; subst; simpl in *);
        pose proof Hbinds0 as HbindsTmp;
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        apply ok_concat_inv in Hokl;
        destruct Hokl as [Hokl1 Hokl2];
        unfold inv_5' in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_5;
        repeat rewrite get_r'_dist in Hinv_5; auto;
        repeat rewrite get_f'_dist in Hinv_5; auto;
        simpl in Hinv_5;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl;
        try (rewrite get_r'_any_rear_remove; auto);
        try (rewrite get_r'_any_rear_remove; auto);
        try (rewrite get_r'_any_ary_remove; auto);
        try (rewrite get_r'_any_ary_remove; auto);
        try (rewrite get_f'_any_rear_remove; auto);
        try (rewrite get_f'_any_rear_remove; auto);
        try (rewrite get_f'_any_ary_remove; auto);
        try (rewrite get_f'_any_ary_remove; auto);
        simpl; 
        try rewrite <-Hlist in *;
        intuition.
        all : try (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        exfalso;
        eapply deq_not_inc_subst_normal_false; eauto; solve_normal);
        apply deq_not_inc_subst_neq_inv in Henq; auto;
        simpl in *;
        apply Hinv_5 in Henq; auto).
        all : try (destruct (eq_nat_dec pid pid0);
        try (subst pid;
        exfalso;
        eapply deq_not_inc_subst_normal_false; eauto; solve_normal);
        apply deq_not_inc_subst_neq_inv in Henq; auto;
        try (apply deq_not_inc_remove_rear_neq_inv in Henq; auto);
        try (apply deq_not_inc_remove_ary_neq_inv in Henq; auto);
        apply Hinv_5 in Henq; auto).
        all : try (unfold binds in Hbinds4;
        try (rewrite Hbinds4 in Hinv_5);
        destruct (eq_nat_dec pid pid0);
        [subst pid;
        eapply Hinv_5 with (pid:=pid0); eauto;
        unfold deq_not_inc in *;
        unfold binds in Henq;
        pose proof HbindsTmp as HbindsTmp';
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in Henq;
        intuition; try discriminate;
        inversion H8; subst ret; simpl in *;
        intuition|
        apply deq_not_inc_subst_neq_inv in Henq; auto;
        try (apply deq_not_inc_remove_rear_neq_inv in Henq; auto);
        try (apply deq_not_inc_remove_ary_neq_inv in Henq; auto);
        apply Hinv_5 in Henq; auto]).
        all : try (unfold binds in Hbinds6;
        try (rewrite Hbinds6 in Hinv_5);
        destruct (eq_nat_dec pid pid0);
        [subst pid;
        eapply Hinv_5 with (pid:=pid0); eauto;
        unfold deq_not_inc in *;
        unfold binds in Henq;
        pose proof HbindsTmp as HbindsTmp';
        eapply substitute_eq_binds_v' in HbindsTmp;
        rewrite HbindsTmp in Henq;
        intuition; try discriminate;
        inversion H8; subst ret; simpl in *;
        intuition|
        apply deq_not_inc_subst_neq_inv in Henq; auto;
        try (apply deq_not_inc_remove_rear_neq_inv in Henq; auto);
        try (apply deq_not_inc_remove_ary_neq_inv in Henq; auto);
        apply Hinv_5 in Henq; auto]).
        unfold binds in Hbinds4;
        try (rewrite Hbinds4 in Henq);
        try (rewrite Hbinds4 in Hinv_5);
        intuition.
        unfold binds in Hbinds6;
        try (rewrite Hbinds6 in Henq);
        try (rewrite Hbinds6 in Hinv_5);
        intuition.
      (* inv_6 *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [Hinv_6 _]]]]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H2; subst; simpl in *.
        unfold inv_6; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *.
        inversion H3; subst; simpl in *;
        inversion H0; subst; simpl in *;
        inversion H4; subst; simpl in *;
        inversion H6; subst; simpl in *;
        inversion H5; subst; simpl in *;
        try (inversion H8; subst; simpl in *);
        try (inversion H7; subst; simpl in *);
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        apply ok_concat_inv in Hokl;
        destruct Hokl as [Hokl1 Hokl2];
        unfold inv_6 in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_6;
        repeat rewrite get_r'_dist in Hinv_6; auto;
        repeat rewrite get_f'_dist in Hinv_6; auto;
        simpl in Hinv_6;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl; 
        try (rewrite get_r'_any_rear_remove; auto);
        try (rewrite get_r'_any_rear_remove; auto);
        try (rewrite get_r'_any_ary_remove; auto);
        try (rewrite get_r'_any_ary_remove; auto);
        try (rewrite get_f'_any_rear_remove; auto);
        try (rewrite get_f'_any_rear_remove; auto);
        try (rewrite get_f'_any_ary_remove; auto);
        try (rewrite get_f'_any_ary_remove; auto);
        simpl;
        try (unfold binds in Hbinds4; rewrite Hbinds4);
        try (unfold binds in Hbinds6; rewrite Hbinds6);
        simpl;
        intuition.
        all : try (unfold binds in Hbinds4;
        rewrite Hbinds4 in H9, H10; intuition).
        all : try (unfold binds in Hbinds6;
        rewrite Hbinds6 in H11, H12; intuition).
      (* inv_range *)
      --- pose proof Hreach as HreachTmp.
        apply IHk in Hreach; try lia.
        unfold inv_total in Hreach.
        destruct Hreach as [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ [_ Hinv_range]]]]]]]]]]]]].
        inversion H1; subst; simpl in *.
        inversion H2; subst; simpl in *.
        unfold inv_range; simpl.
        unfold F, R in *; simpl in *.
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        inversion H3; subst; simpl in *;
        inversion H0; subst; simpl in *;
        inversion H4; subst; simpl in *;
        inversion H6; subst; simpl in *;
        inversion H5; subst; simpl in *;
        try (inversion H8; subst; simpl in *);
        try (inversion H7; subst; simpl in *);
        apply binds_reconstruct in Hbinds0;
        destruct Hbinds0 as [l1 [l2 Hlist]];
        apply reachable_len_to_reachable in HreachTmp;
        apply array_queue_wf_invarint in HreachTmp;
        unfold array_queue_wf in HreachTmp;
        simpl in HreachTmp;
        rewrite Hlist in HreachTmp;
        apply ok_remove_middle_inv in HreachTmp;
        destruct HreachTmp as [Hokl [Hnt1 Hnt2]];
        apply ok_concat_inv in Hokl;
        destruct Hokl as [Hokl1 Hokl2];
        unfold inv_range in *; simpl in *;
        unfold F, R in *; simpl in *;
        unfold get_front, get_rear, get_pc, get_ary  in *; simpl in *;
        rewrite Hlist in Hinv_range;
        repeat rewrite get_r'_dist in Hinv_range; auto;
        repeat rewrite get_f'_dist in Hinv_range; auto;
        simpl in Hinv_range;
        rewrite Hlist;
        repeat rewrite substitute_notin_app; auto;
        repeat rewrite get_r'_dist; auto;
        repeat rewrite get_f'_dist; auto;
        simpl;
        rewrite Nat.eqb_refl;
        simpl;
        try (rewrite get_r'_any_rear_remove; auto);
        try (rewrite get_r'_any_rear_remove; auto);
        try (rewrite get_r'_any_ary_remove; auto);
        try (rewrite get_r'_any_ary_remove; auto);
        try (rewrite get_f'_any_rear_remove; auto);
        try (rewrite get_f'_any_rear_remove; auto);
        try (rewrite get_f'_any_ary_remove; auto);
        try (rewrite get_f'_any_ary_remove; auto);
        simpl;
        simpl; intuition.
        all : try (unfold binds in Hbinds4;
        rewrite Hbinds4 in H7, H8; intuition).
        all : try (unfold binds in Hbinds6;
        rewrite Hbinds6 in H9, H10; intuition).
Qed.

Lemma inv_total_invariant:
  composed_lts.invariant (composed_array_queue L)
  inv_total.
Proof.
  apply invariant_len_to_invariant'.
  apply inv_total_inv'.
Qed.

Lemma inv_e28_clean_invariant:
  composed_lts.invariant (composed_array_queue L)
  inv_e28_clean.
Proof.
  generalize inv_total_invariant; intro.
  unfold inv_total in H0.
  apply invariant_land_l in H0.
  intuition.
Qed.

Lemma inv_d28_clean_invariant:
  composed_lts.invariant (composed_array_queue L)
  inv_d28_clean.
Proof.
  generalize inv_total_invariant; intro.
  unfold inv_total in H0.
  apply invariant_land_r in H0.
  apply invariant_land_l in H0.
  intuition.
Qed.

Lemma inv_6_invariant:
  composed_lts.invariant (composed_array_queue L)
  inv_6.
Proof.
  generalize inv_total_invariant; intro.
  unfold inv_total in H0.
  apply invariant_land_r in H0.
  apply invariant_land_r in H0.
  apply invariant_land_r in H0.
  apply invariant_land_r in H0.
  apply invariant_land_r in H0.
  apply invariant_land_r in H0.
  apply invariant_land_r in H0.
  apply invariant_land_r in H0.
  apply invariant_land_r in H0.
  apply invariant_land_r in H0.
  apply invariant_land_r in H0.
  apply invariant_land_r in H0.
  apply invariant_land_l in H0.
  intuition.
Qed.

Lemma inv_5_invariant:
  composed_lts.invariant (composed_array_queue L)
  inv_5.
Proof.
  generalize inv_total_invariant; intro.
  unfold inv_total in H0.
  apply invariant_land_r in H0.
  apply invariant_land_r in H0.
  apply invariant_land_r in H0.
  apply invariant_land_r in H0.
  apply invariant_land_r in H0.
  apply invariant_land_r in H0.
  apply invariant_land_r in H0.
  apply invariant_land_r in H0.
  apply invariant_land_r in H0.
  apply invariant_land_r in H0.
  apply invariant_land_l in H0.
  intuition.
Qed.

End INV.