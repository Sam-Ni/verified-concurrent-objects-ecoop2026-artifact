Require Import
  List
  LTS
  Arith
  LibVar
  LibEnv
  Refinement
  Array
  Counter
  ArrayQueueImpl
  Queue
  VeriTactics.
Import ListNotations.

Section Mapping.

Fixpoint gather_requests (pc : LibEnv.env AQueue_pc)
  (vp : Pid -> nat) (front : Pid -> nat) (rear : Pid -> nat)
  (res_ary : env Array_reply) (res_front : env Counter_reply) (res_rear : env Counter_reply)
  : LibEnv.env Queue_query :=
  match pc with
  | nil => nil
  | ins :: pc' => 
      let requests' := gather_requests pc' vp front rear res_ary res_front res_rear in
      let (pid, inst) := ins in
        (match inst with
        | AEnq1 => (pid, QEnq (vp pid)) :: requests'
        | AEnq2 => (pid, QEnq (vp pid)) :: requests'
        | AEnq3 _ => (pid, QEnq (vp pid)) :: requests'
        | AEnq4 => (pid, QEnq (vp pid)) :: requests'
        | AEnq5 => (pid, QEnq (vp pid)) :: requests'
        | AEnq6 _ => (pid, QEnq (vp pid)) :: requests'
        | AEnq10 => (pid, QEnq (vp pid)) :: requests'
        | AEnq11 => (pid, QEnq (vp pid)) :: requests'
        | AEnq12 _ => (pid, QEnq (vp pid)) :: requests'
        | AEnq13 => (pid, QEnq (vp pid)) :: requests'
        | AEnq14 => (pid, QEnq (vp pid)) :: requests'
        | AEnq15 _ => (pid, QEnq (vp pid)) :: requests'
        | AEnq26 => (pid, QEnq (vp pid)) :: requests'
        | AEnq27 => (pid, QEnq (vp pid)) :: requests'
        | AEnq28 => 
                    match get pid res_ary with
                              | None => (pid, QEnq (vp pid)) :: requests'
                              | Some res => match res with
                                          | AryCASOk b => if b then requests'
                                                          else (pid, QEnq (vp pid)) :: requests'
                                          | AryReadOk v => (pid, QEnq (vp pid)) :: requests' (* unreachable *)
                                          end
                              end
        | AEnq29 ret => if ret then requests'
                                  else (pid, QEnq (vp pid)) :: requests'
        | AEnq30 => requests'
        | AEnq31 => requests'
        | AEnq32 => requests'
        | ADeq1 => (pid, QDeq) :: requests'
        | ADeq2 => (pid, QDeq) :: requests'
        | ADeq3 _ => (pid, QDeq) :: requests'
        | ADeq4 => (pid, QDeq) :: requests'
        | ADeq5 => (pid, QDeq) :: requests'
        | ADeq6 _ => (pid, QDeq) :: requests'
        | ADeq10 => (pid, QDeq) :: requests'
        | ADeq11 => (pid, QDeq) :: requests'
        | ADeq12 _ => (pid, QDeq) :: requests'
        | ADeq13 => (pid, QDeq) :: requests'
        | ADeq14 => (pid, QDeq) :: requests'
        | ADeq15 _ => (pid, QDeq) :: requests'
        | ADeq26 => (pid, QDeq) :: requests'
        | ADeq27 => (pid, QDeq) :: requests'
        | ADeq28 => 
                    match get pid res_ary with
                              | None => (pid, QDeq) :: requests'
                              | Some res => match res with
                                          | AryCASOk b => if b then requests'
                                                          else (pid, QDeq) :: requests'
                                          | AryReadOk v => (pid, QDeq) :: requests'
                                          end
                              end
        | ADeq29 ret => if ret then requests'
                                  else (pid, QDeq) :: requests'
        | ADeq30 => requests'
        | ADeq31 => requests'
        | ADeq32 => requests'
        end)
  end.

Fixpoint gather_responses (pc : LibEnv.env AQueue_pc)
  (front : Pid -> nat) (rear : Pid -> nat)
  (x : Pid -> entry)
  (res_ary : env Array_reply) (res_front : env Counter_reply) (res_rear : env Counter_reply)
  : LibEnv.env Queue_reply :=
  match pc with
  | nil => nil
  | ins :: pc' => 
      let responses' := gather_responses pc' front rear x res_ary res_front res_rear in
      let (pid, inst) := ins in
        (match inst with
        | AEnq1 => responses'
        | AEnq2 => responses'
        | AEnq3 _ => responses'
        | AEnq4 => responses'
        | AEnq5 => responses'
        | AEnq6 _ => responses'
        | AEnq10 => responses'
        | AEnq11 => responses'
        | AEnq12 _ => responses'
        | AEnq13 => responses'
        | AEnq14 => responses'
        | AEnq15 _ => responses'
        | AEnq26 => responses'
        | AEnq27 => responses'
        | AEnq28 => match get pid res_ary with
                    | None => responses'
                    | Some res => match res with
                                  | AryCASOk b => if b then (pid, QEnqOk) :: responses'
                                                  else responses'
                                  | AryReadOk v => responses'
                                  end
                    end
        | AEnq29 ret => if ret then (pid, QEnqOk ) :: responses'
                                  else responses'
        | AEnq30 => (pid, QEnqOk) :: responses'
        | AEnq31 => (pid, QEnqOk) :: responses'
        | AEnq32 => (pid, QEnqOk) :: responses'
        | ADeq1 => responses'
        | ADeq2 => responses'
        | ADeq3 _ => responses'
        | ADeq4 => responses'
        | ADeq5 => responses'
        | ADeq6 _ => responses'
        | ADeq10 => responses'
        | ADeq11 => responses'
        | ADeq12 _ => responses'
        | ADeq13 => responses'
        | ADeq14 => responses'
        | ADeq15 _ => responses'
        | ADeq26 => responses'
        | ADeq27 => responses'
        | ADeq28 => match get pid res_ary with
                    | None => responses'
                    | Some res => match res with
                                  | AryCASOk b => if b then match (fst (x pid)) with
                                                            | None => responses'
                                                            | Some v => (pid, QDeqOk v) :: responses'
                                                            end
                                                  else responses'
                                  | AryReadOk v => responses'
                                  end
                    end
        | ADeq29 ret => if ret then match (fst (x pid)) with
                                    | None => responses'
                                    | Some v => (pid, QDeqOk v) :: responses'
                                    end
                                  else responses'
        | ADeq30 => match (fst (x pid)) with
                    | None => responses'
                    | Some v => (pid, QDeqOk v) :: responses'
                    end
        | ADeq31 => match (fst (x pid)) with
                    | None => responses'
                    | Some v => (pid, QDeqOk v) :: responses'
                    end
        | ADeq32 => match (fst (x pid)) with
                    | None => responses'
                    | Some v => (pid, QDeqOk v) :: responses'
                    end
        end)
  end.

Lemma gather_requests_preserves_notin: forall pc pid vp front rear res_ary res_front res_rear,
  pid # pc ->
  pid # gather_requests pc vp front rear res_ary res_front res_rear.
Proof.
  induction pc; intros.
  - apply notin_empty.
  - destruct a. simpl.
    simpl. simpl in H.
    apply notin_union in H. intuition.
    match_if'; simpl; try apply notin_union; intuition.
Qed.

Lemma gather_responses_preserves_notin: forall pc pid front rear x res_ary res_front res_rear,
  pid # pc ->
  pid # gather_responses pc front rear x res_ary res_front res_rear.
Proof.
  induction pc; intros.
  - apply notin_empty.
  - destruct a. simpl.
    simpl. simpl in H.
    apply notin_union in H. intuition.
    match_if'; simpl; try apply notin_union; intuition.
Qed.

Lemma gather_requests_preserves_ok: forall pc vp front rear res_ary res_front res_rear,
  ok pc ->
  ok (gather_requests pc vp front rear res_ary res_front res_rear).
Proof.
  induction pc using env_ind; simpl; intros.
  - constructor.
  - inversion H; subst.
    match_if'; try apply IHpc; auto;
    econstructor; eauto;
    apply gather_requests_preserves_notin; auto.
Qed.

Lemma gather_responses_preserves_ok: forall pc front rear x res_ary res_front res_rear,
  ok pc ->
  ok (gather_responses pc front rear x res_ary res_front res_rear).
Proof.
  induction pc using env_ind; simpl; intros.
  - constructor.
  - inversion H; subst.
    match_if'; try apply IHpc; auto;
    econstructor; eauto;
    apply gather_responses_preserves_notin; auto.
Qed.

Lemma gather_requests_vp: forall pc vp front rear s pid v,
  pid # pc ->
  gather_requests pc (fun p : Pid => if p =? pid then v else vp p) front rear s =
  gather_requests pc vp front rear s.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - apply notin_union in H.
    intuition.
    destruct a. simpl in *.
    apply notin_neq in H0.
    assert (Hneq: v0 =? pid = false).
    apply Nat.eqb_neq. intuition.
    repeat rewrite Hneq. erewrite IHpc.
    destruct a; simpl; match_if'.
    assumption.
Qed.

Lemma gather_responses_dist: forall pc pc' front rear x res_ary res_front res_rear,
  (gather_responses (pc ++ pc') front rear x res_ary res_front res_rear) =
  (gather_responses pc front rear x res_ary res_front res_rear) ++
  (gather_responses pc' front rear x res_ary res_front res_rear).
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - destruct a.
    match_if'; rewrite IHpc; reflexivity.
Qed.

Lemma gather_requests_dist: forall pc pc' vp front rear res_ary res_front res_rear,
  (gather_requests (pc ++ pc') vp front rear res_ary res_front res_rear) =
  (gather_requests pc vp front rear res_ary res_front res_rear) ++
  (gather_requests pc' vp front rear res_ary res_front res_rear).
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - destruct a.
    match_if'; rewrite IHpc; reflexivity.
Qed.

Lemma gather_responses_remove_comm: forall pc pid front rear x res_ary res_front res_rear,
  ok pc ->
  (gather_responses (remove pc pid) front rear x res_ary res_front res_rear) =
  remove (gather_responses pc front rear x res_ary res_front res_rear) pid.
Proof.
  induction 1; simpl; intros.
  - reflexivity.
  - destruct (pid =? x0)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst.
      rewrite notin_remove in IHok; auto.
      destruct T;
      match_if_apply IHok.
      all : simpl;
      rewrite Nat.eqb_refl; reflexivity.
    -- simpl.
      destruct T; match_if_apply IHok.
      all : simpl; rewrite Heq; f_equal; auto.
Qed.

Lemma gather_responses_binds_AEnq32: forall pc pid front rear x res_ary res_front res_rear,
  ok pc ->
  binds pid AEnq32 pc ->
  binds pid (QEnqOk) (gather_responses pc front rear x res_ary res_front res_rear).
Proof.
  intros.
  apply binds_reconstruct in H0.
  destruct H0 as [l1 [l2 Hlist]].
  rewrite Hlist in H.
  rewrite Hlist.
  rewrite gather_responses_dist.
  simpl.
  apply binds_concat_left.
  apply binds_push_eq.
  apply gather_responses_preserves_notin; auto.
  apply ok_remove_middle_inv in H; intuition.
Qed.

Lemma gather_requests_binds_AEnq32_remove: forall pc vp front rear s pid,
  binds pid AEnq32 pc ->
  gather_requests (remove pc pid) vp front rear s =
  gather_requests pc vp front rear s.
Proof.
  induction pc; intros.
  - inversion H.
  - unfold binds in *.
    destruct a.
    simpl in *.
    destruct (pid =? v)eqn:Heq.
    -- inversion H; subst.
      simpl.
      reflexivity.
    -- simpl.
      destruct a; simpl; try rewrite Heq; simpl; rewrite IHpc; auto.
Qed.

Lemma gather_responses_binds_ADeq32: forall pc pid front rear x res_ary res_front res_rear v,
  ok pc ->
  binds pid ADeq32 pc ->
  fst (x pid) = Some v ->
  binds pid (QDeqOk v) (gather_responses pc front rear x res_ary res_front res_rear).
Proof.
  intros.
  apply binds_reconstruct in H0.
  destruct H0 as [l1 [l2 Hlist]].
  rewrite Hlist in H.
  rewrite Hlist.
  rewrite gather_responses_dist.
  simpl.
  rewrite H1.
  apply binds_concat_left.
  apply binds_push_eq.
  apply gather_responses_preserves_notin; auto.
  apply ok_remove_middle_inv in H; intuition.
Qed.

Lemma gather_requests_binds_ADeq32_remove: forall pc vp front rear s pid,
  binds pid ADeq32 pc ->
  gather_requests (remove pc pid) vp front rear s =
  gather_requests pc vp front rear s.
Proof.
  induction pc; intros.
  - inversion H.
  - unfold binds in *.
    destruct a.
    simpl in *.
    destruct (pid =? v)eqn:Heq.
    -- inversion H; subst.
      simpl.
      reflexivity.
    -- simpl.
      destruct a; simpl; try rewrite Heq; simpl; rewrite IHpc; auto.
Qed.

Lemma gather_requests_rear: forall pc vp front rear s pid v,
  pid # pc ->
  gather_requests pc vp front (fun p : Pid => if p =? pid then v else rear p) s =
  gather_requests pc vp front rear s.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - apply notin_union in H.
    intuition.
    destruct a. simpl in *.
    apply notin_neq in H0.
    assert (Hneq: v0 =? pid = false).
    apply Nat.eqb_neq. intuition.
    repeat rewrite Hneq. erewrite IHpc.
    destruct a; simpl; match_if'.
    assumption.
Qed.

Lemma gather_requests_res_rear: forall pc vp front rear pid res_ary res_front res_rear,
  pid # pc ->
  gather_requests pc vp front rear res_ary res_front (remove res_rear pid) =
  gather_requests pc vp front rear res_ary res_front res_rear.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - apply notin_union in H.
    intuition.
    destruct a. simpl in *.
    apply notin_neq in H0.
    erewrite IHpc; eauto.
Qed.

Lemma gather_requests_res_rear': forall pc vp front rear pid res_ary res_front res_rear v,
  pid # pc ->
  gather_requests pc vp front rear res_ary res_front ((pid, v) :: res_rear) =
  gather_requests pc vp front rear res_ary res_front res_rear.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - apply notin_union in H.
    intuition.
    destruct a. simpl in *.
    apply notin_neq in H0.
    erewrite IHpc; eauto.
Qed.

Lemma gather_requests_res_front': forall pc vp front rear pid res_ary res_front res_rear v,
  pid # pc ->
  gather_requests pc vp front rear res_ary ((pid, v) :: res_front) res_rear =
  gather_requests pc vp front rear res_ary res_front res_rear.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - apply notin_union in H.
    intuition.
    destruct a. simpl in *.
    apply notin_neq in H0.
    erewrite IHpc; eauto.
Qed.

Lemma gather_requests_res_ary: forall pc vp front rear pid res_ary res_front res_rear,
  pid # pc ->
  gather_requests pc vp front rear (remove res_ary pid) res_front res_rear =
  gather_requests pc vp front rear res_ary res_front res_rear.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - apply notin_union in H.
    intuition.
    destruct a. simpl in *.
    apply notin_neq in H0.
    erewrite IHpc; eauto.
    destruct a; simpl; match_if'.
    all : try (eapply remove_neq_preserves_binds in Heqo0; eauto;
    rewrite Heqo0 in Heqo;
    discriminate).
    all : apply remove_preserves_binds_notin in Heqo; auto;
    rewrite Heqo in Heqo0;
    discriminate.
Qed.

Lemma gather_requests_res_ary': forall pc vp front rear pid res_ary res_front res_rear v,
  pid # pc ->
  gather_requests pc vp front rear ((pid, v) :: res_ary) res_front res_rear =
  gather_requests pc vp front rear res_ary res_front res_rear.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - apply notin_union in H.
    intuition.
    destruct a. simpl in *.
    apply notin_neq in H0.
    erewrite IHpc; eauto.
    destruct a; simpl; match_if'.
    all : apply Nat.eqb_eq in Heqb; subst; intuition.
Qed.

Lemma gather_requests_res_front: forall pc vp front rear pid res_ary res_front res_rear,
  pid # pc ->
  gather_requests pc vp front rear res_ary (remove res_front pid) res_rear =
  gather_requests pc vp front rear res_ary res_front res_rear.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - apply notin_union in H.
    intuition.
    destruct a. simpl in *.
    apply notin_neq in H0.
    erewrite IHpc; eauto.
Qed.

Lemma gather_responses_res_front: forall pc front rear x pid res_ary res_front res_rear,
  pid # pc ->
  gather_responses pc front rear x res_ary (remove res_front pid) res_rear =
  gather_responses pc front rear x res_ary res_front res_rear.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - apply notin_union in H.
    intuition.
    destruct a. simpl in *.
    apply notin_neq in H0.
    erewrite IHpc; eauto.
Qed.

Lemma gather_responses_res_ary: forall pc front rear x pid res_ary res_front res_rear,
  pid # pc ->
  gather_responses pc front rear x (remove res_ary pid) res_front res_rear =
  gather_responses pc front rear x res_ary res_front res_rear.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - apply notin_union in H.
    intuition.
    destruct a. simpl in *.
    apply notin_neq in H0.
    erewrite IHpc; eauto.
    destruct a; simpl; match_if'.
    all : try (eapply remove_neq_preserves_binds in Heqo0; eauto;
    rewrite Heqo0 in Heqo;
    discriminate).
    all : apply remove_preserves_binds_notin in Heqo; auto.
    rewrite Heqo in Heqo0.
    discriminate.
    rewrite Heqo in Heqo1.
    discriminate.
    rewrite Heqo in Heqo1.
    discriminate.
    rewrite Heqo in Heqo1.
    discriminate.
Qed.

Lemma gather_responses_res_ary': forall pc front rear x pid res_ary res_front res_rear v,
  pid # pc ->
  gather_responses pc front rear x ((pid, v) :: res_ary) res_front res_rear =
  gather_responses pc front rear x res_ary res_front res_rear.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - apply notin_union in H.
    intuition.
    destruct a. simpl in *.
    apply notin_neq in H0.
    erewrite IHpc; eauto.
    destruct a; simpl; match_if'.
    all : apply Nat.eqb_eq in Heqb; subst; intuition.
Qed.

Lemma gather_responses_res_rear: forall pc front rear x pid res_ary res_front res_rear,
  pid # pc ->
  gather_responses pc front rear x res_ary res_front (remove res_rear pid) =
  gather_responses pc front rear x res_ary res_front res_rear.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - apply notin_union in H.
    intuition.
    destruct a. simpl in *.
    apply notin_neq in H0.
    erewrite IHpc; eauto.
Qed.

Lemma gather_responses_res_rear': forall pc front rear x pid res_ary res_front res_rear v,
  pid # pc ->
  gather_responses pc front rear x res_ary res_front ((pid, v) :: res_rear) =
  gather_responses pc front rear x res_ary res_front res_rear.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - apply notin_union in H.
    intuition.
    destruct a. simpl in *.
    apply notin_neq in H0.
    assert (Hneq: v0 =? pid = false).
    apply Nat.eqb_neq. intuition.
    repeat rewrite Hneq. erewrite IHpc.
    destruct a; simpl; match_if'.
    assumption.
Qed.

Lemma gather_responses_res_front': forall pc front rear x pid res_ary res_front res_rear v,
  pid # pc ->
  gather_responses pc front rear x res_ary ((pid, v) :: res_front) res_rear =
  gather_responses pc front rear x res_ary res_front res_rear.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - apply notin_union in H.
    intuition.
    destruct a. simpl in *.
    apply notin_neq in H0.
    assert (Hneq: v0 =? pid = false).
    apply Nat.eqb_neq. intuition.
    repeat rewrite Hneq. erewrite IHpc.
    destruct a; simpl; match_if'.
    assumption.
Qed.

Lemma gather_requests_front: forall pc vp front rear s pid v,
  pid # pc ->
  gather_requests pc vp (fun p : Pid => if p =? pid then v else front p) rear s =
  gather_requests pc vp front rear s.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - apply notin_union in H.
    intuition.
    destruct a. simpl in *.
    apply notin_neq in H0.
    assert (Hneq: v0 =? pid = false).
    apply Nat.eqb_neq. intuition.
    repeat rewrite Hneq. erewrite IHpc.
    destruct a; simpl; match_if'.
    assumption.
Qed.

Lemma gather_responses_rear: forall pc front rear x s pid v,
  pid # pc ->
  gather_responses pc front (fun p : Pid => if p =? pid then v else rear p) x s =
  gather_responses pc front rear x s.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - apply notin_union in H.
    intuition.
    destruct a. simpl in *.
    apply notin_neq in H0.
    assert (Hneq: v0 =? pid = false).
    apply Nat.eqb_neq. intuition.
    repeat rewrite Hneq. erewrite IHpc.
    destruct a; simpl; match_if'.
    assumption.
Qed.

Lemma gather_responses_front: forall pc front rear x s pid v,
  pid # pc ->
  gather_responses pc (fun p : Pid => if p =? pid then v else front p) rear x s =
  gather_responses pc front rear x s.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - apply notin_union in H.
    intuition.
    destruct a. simpl in *.
    apply notin_neq in H0.
    assert (Hneq: v0 =? pid = false).
    apply Nat.eqb_neq. intuition.
    repeat rewrite Hneq. erewrite IHpc.
    destruct a; simpl; match_if'.
    assumption.
Qed.

Lemma gather_responses_x: forall pc front rear x s pid v,
  pid # pc ->
  gather_responses pc front rear (fun p : Pid => if p =? pid then v else x p) s =
  gather_responses pc front rear x s.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - apply notin_union in H.
    intuition.
    destruct a. simpl in *.
    apply notin_neq in H0.
    assert (Hneq: v0 =? pid = false).
    apply Nat.eqb_neq. intuition.
    repeat rewrite Hneq. erewrite IHpc.
    destruct a; simpl; match_if'.
    assumption.
Qed.

Lemma gather_requests_binds_AEnq3_substitute_AEnq4: forall pc vp front rear res_ary res_front res_rear pid ret,
  ok pc ->
  binds pid (AEnq3 ret) pc ->
  gather_requests (substitute pc pid AEnq4) vp front 
    (fun p => if p =? pid then ret else rear p) res_ary res_front res_rear =
  gather_requests pc vp front rear res_ary res_front res_rear.
Proof.
  intros.
  apply binds_reconstruct in H0.
  destruct H0 as [l1 [l2 Hlist]].
  rewrite Hlist in H.
  rewrite Hlist.
  apply ok_remove_middle_inv in H.
  rewrite substitute_notin_app; intuition.
  repeat rewrite gather_requests_dist.
  simpl.
  rewrite Nat.eqb_refl.
  simpl.
  rewrite gather_requests_rear; auto.
  rewrite gather_requests_rear; auto.
Qed.

Lemma gather_responses_binds_AEnq3_substitute_AEnq4: forall pc front rear x res_ary res_front res_rear pid ret,
  ok pc ->
  binds pid (AEnq3 ret) pc ->
  gather_responses (substitute pc pid AEnq4) front
    (fun p => if p =? pid then ret else rear p) x res_ary res_front res_rear =
  gather_responses pc front rear x res_ary res_front res_rear.
Proof.
  intros.
  apply binds_reconstruct in H0.
  destruct H0 as [l1 [l2 Hlist]].
  rewrite Hlist in H.
  rewrite Hlist.
  apply ok_remove_middle_inv in H.
  rewrite substitute_notin_app; intuition.
  repeat rewrite gather_responses_dist.
  simpl.
  rewrite Nat.eqb_refl.
  simpl.
  rewrite gather_responses_rear; auto.
  rewrite gather_responses_rear; auto.
Qed.

Lemma gather_requests_AEnq1_substitute: forall pc vp front rear res_ary res_front res_rear pid,
  binds pid AEnq1 pc ->
  ok pc ->
  gather_requests (substitute pc pid AEnq2) vp front rear res_ary res_front res_rear =
  gather_requests pc vp front rear res_ary res_front res_rear.
Proof.
  intros.
  apply binds_reconstruct in H.
  destruct H as [l1 [l2 Hlist]].
  rewrite Hlist.
  rewrite Hlist in H0.
  rewrite substitute_notin_app.
  rewrite gather_requests_dist.
  rewrite gather_requests_dist.
  simpl.
  rewrite Nat.eqb_refl.
  simpl. reflexivity.
  apply ok_middle_inv in H0; intuition.
Qed.

End Mapping.

Section Mapping2.
Context {L : nat}.
Hypothesis H : 0 < L.

Fixpoint get_f (pc : LibEnv.env AQueue_pc)
  (res_ary : env Array_reply)
: nat :=
  match pc with
  | nil => O
  | ins :: pc' => 
      let f' := get_f pc' res_ary in
      let (pid, inst) := ins in
        (match inst with
        | ADeq28 => match get pid res_ary with
                    | None => f'
                    | Some res => match res with
                                | AryCASOk b => if b then (S f')
                                                else f'
                                | AryReadOk v => f'
                                end
                    end
        | _ => f'
        end)
  end.

Lemma get_f_dist: forall pc1 pc2 ary,
  get_f (pc1 ++ pc2) ary =
  get_f pc1 ary + get_f pc2 ary.
Proof.
  induction pc1; simpl; intros.
  - reflexivity.
  - destruct a.
    match_if'; rewrite IHpc1; auto.
Qed.

Import LibVar.
Import LibEnv.

Lemma get_f_res_ary: forall pc pid res_ary,
  pid # pc ->
  get_f pc (remove res_ary pid) =
  get_f pc res_ary.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - apply notin_union in H0.
    intuition.
    destruct a. simpl in *.
    apply notin_neq in H1.
    erewrite IHpc; eauto.
    destruct a; simpl; match_if'.
    all : try (eapply remove_neq_preserves_binds in Heqo0; eauto;
    rewrite Heqo0 in Heqo;
    discriminate).
    all : apply remove_preserves_binds_notin in Heqo; auto;
    rewrite Heqo in Heqo0;
    discriminate.
Qed.

Lemma get_f_res_ary': forall pc pid res_ary v,
  pid # pc ->
  get_f pc ((pid, v) :: res_ary) =
  get_f pc res_ary.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - apply notin_union in H0.
    intuition.
    destruct a. simpl in *.
    apply notin_neq in H1.
    erewrite IHpc; eauto.
    destruct a; simpl; match_if'.
    apply Nat.eqb_eq in Heqb. subst. intuition.
    apply Nat.eqb_eq in Heqb. subst. intuition.
    apply Nat.eqb_eq in Heqb. subst. intuition.
    apply Nat.eqb_eq in Heqb. subst. intuition.
    apply Nat.eqb_eq in Heqb. subst. intuition.
Qed.


Fixpoint get_r (pc : LibEnv.env AQueue_pc)
  (res_ary : env Array_reply) 
: nat :=
  match pc with
  | nil => O
  | ins :: pc' => 
      let r' := get_r pc' res_ary in
      let (pid, inst) := ins in
        (match inst with
        | AEnq28 => match get pid res_ary with
                    | None => r'
                    | Some res => match res with
                                | AryCASOk b => if b then (S r')
                                                else r'
                                | AryReadOk v => r'
                                end
                    end
        | _ => r'
        end)
  end.

Lemma get_r_res_ary: forall pc pid res_ary,
  pid # pc ->
  get_r pc (remove res_ary pid) =
  get_r pc res_ary.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - apply notin_union in H0.
    intuition.
    destruct a. simpl in *.
    apply notin_neq in H1.
    erewrite IHpc; eauto.
    destruct a; simpl; match_if'.
    all : try (eapply remove_neq_preserves_binds in Heqo0; eauto;
    rewrite Heqo0 in Heqo;
    discriminate).
    all : apply remove_preserves_binds_notin in Heqo; auto;
    rewrite Heqo in Heqo0;
    discriminate.
Qed.

Lemma get_r_res_ary': forall pc pid res_ary v,
  pid # pc ->
  get_r pc ((pid, v) :: res_ary) =
  get_r pc res_ary.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - apply notin_union in H0.
    intuition.
    destruct a. simpl in *.
    apply notin_neq in H1.
    erewrite IHpc; eauto.
    destruct a; simpl; match_if'.
    all : try (eapply remove_neq_preserves_binds in Heqo0; eauto;
    rewrite Heqo0 in Heqo;
    discriminate).
    all :
    apply Nat.eqb_eq in Heqb; subst; intuition.
Qed.

Lemma get_r_dist: forall pc1 pc2 ary,
  get_r (pc1 ++ pc2) ary =
  get_r pc1 ary + get_r pc2 ary.
Proof.
  induction pc1; simpl; intros.
  - reflexivity.
  - destruct a.
    match_if'; rewrite IHpc1; auto.
Qed.

Lemma mod_lt: forall f,
  f mod L < L.
Proof.
  intros. apply Nat.mod_upper_bound.
  inversion H; subst. auto. auto.
Qed.

End Mapping2.