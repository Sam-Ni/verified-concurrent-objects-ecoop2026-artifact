Require Import
  List
  Arith
  LibVar
  LibEnv
  LTS
  SyncLTS
  RawCompose
  RawTensor
  Tensor
  Invariants
  RegisterProp
  ArrayQueueImpl
  RegisterCounterImpl
  Queue
  Register.
Import ListNotations.

Section test.

Variable A: Type.

Lemma binds_remove_eq_false: forall pid (l : LibEnv.env A) v,
   ok l -> binds pid v (remove l pid) -> False.
Proof.
  intros.
  assert (pid # (remove l pid)).
  apply ok_remove_notin; auto.
  apply binds_in in H0.
  unfold "#" in H1; intuition.
Qed.

Lemma binds_remove_inv: forall pid0 pid (l : LibEnv.env A) v,
   ok l -> binds pid0 v (remove l pid) ->
   binds pid0 v l.
Proof.
  intros.
  assert (pid0 <> pid).
  intro. subst.
  apply binds_remove_eq_false in H0; auto.
  apply remove_preserves_binds_notin in H0; auto.
Qed.

Lemma in_remove_eq_false: forall pid (l : LibEnv.env A),
   ok l -> pid \in dom (remove l pid) -> False.
Proof.
  intros.
  assert (pid # (remove l pid)).
  apply ok_remove_notin; auto.
  unfold "#" in H1; intuition.
Qed.

Lemma in_remove_inv: forall pid0 pid (l : LibEnv.env A),
   ok l -> pid0 \in dom (remove l pid) ->
   pid0 \in dom l.
Proof.
  intros.
  assert (pid0 <> pid).
  intro. subst.
  apply in_remove_eq_false in H0; auto.
  apply remove_neq_preserves_in in H0; auto.
Qed.

Lemma substitute_preserves_in: forall (l : env A) pid k v,
  pid \in dom l ->
  pid \in dom (substitute l k v).
Proof.
  induction l; simpl; intros.
  - intuition.
  - destruct a. simpl in *.
    destruct (eq_nat_dec k v0).
    -- subst.
      rewrite Nat.eqb_refl.
      simpl; auto.
    -- apply Nat.eqb_neq in n.
      rewrite n. simpl.
      apply in_union; auto.
      apply in_union in H; auto.
      intuition.
Qed.

Lemma remove_neq_preserves_in': forall (l : env A) pid0 pid,
  pid0 \in dom l ->
  pid0 <> pid ->
  pid0 \in dom (remove l pid).
Proof.
  induction l; simpl; intros.
  - intuition.
  - destruct a. simpl in *.
    destruct (eq_nat_dec pid v).
    -- subst.
      rewrite Nat.eqb_refl.
      apply in_union in H. intuition.
      simpl in H1. intuition.
      subst. intuition.
    -- apply Nat.eqb_neq in n.
      rewrite n. simpl.
      apply in_union; auto.
      apply in_union in H; auto.
      intuition.
Qed.

End test.

Section Link.

Context {liA liB : language_interface}.
Variable L1 : lts li_null liA.
Variable L2 : lts liA liB.

Lemma raw_compose_reachable_single_reachable: forall s,
  composed_lts.reachable (LTS.raw_compose L1 L2) s ->
  reachable L1 s.(LTS.RawL1State).
Proof.
  intros. unfold reachable.
  unfold composed_lts.reachable in H.
  destruct H as [init [acts [Hnew Hvalid]]].
  apply RawCompose.valid_execution_fragment_com in Hvalid.
  destruct init, s. simpl in *.
  (* destruct RawL1State, L1State0. simpl in *. *)
  (* eapply valid_execution_fragment_sync in Hvalid; eauto. *)
  exists RawL1State.
  exists (gatherAB acts).
  intuition.
  inversion Hnew; subst; simpl in *; auto.
Qed.

Lemma link_valid_compose_valid: forall st st' acts,
  valid_execution_fragment (LTS.linked_lts (LTS.raw_compose L1 L2)) st st' acts ->
  exists c_acts, composed_lts.valid_execution_fragment (LTS.raw_compose L1 L2) st st' c_acts /\
    filterB c_acts = acts.
Proof.
  induction 1; intros.
  - subst. exists []. intuition.
    econstructor; eauto.
  - destruct IHvalid_execution_fragment as
    [c_acts [Hcvalid Hfilter]].
    simpl in H. inversion H; subst.
    -- inversion H; subst.
      exists c_acts. intuition.
      eapply composed_lts.Step_Internal_L2; eauto.
    -- inversion H; subst.
      exists c_acts. intuition.
      eapply composed_lts.Step_Internal_L1; eauto.
    -- exists ((pid, composed_lts.event_invB qb) :: c_acts).
      intuition.
      eapply composed_lts.Step_Internal_Query; eauto.
    -- exists ((pid, composed_lts.event_resB rb) :: c_acts).
      intuition.
      eapply composed_lts.Step_Internal_Reply; eauto.
  - destruct qa.
  - destruct ra.
  - destruct IHvalid_execution_fragment as
    [c_acts [Hcvalid Hfilter]].
    subst.
    simpl in H.
    exists ((pid, composed_lts.event_invC qb):: c_acts).
    simpl. intuition.
    eapply composed_lts.Step_Initial_Call; eauto.
  - destruct IHvalid_execution_fragment as
    [c_acts [Hcvalid Hfilter]].
    subst.
    simpl in H.
    exists ((pid, composed_lts.event_resC rb):: c_acts).
    simpl. intuition.
    eapply composed_lts.Step_Final_Return; eauto.
Qed.

Lemma link_reachable_single_reachable: forall s,
  reachable (LTS.linked_lts (LTS.raw_compose L1 L2)) s ->
  reachable L1 s.(LTS.RawL1State).
Proof.
  intros.
  apply raw_compose_reachable_single_reachable; auto.
  unfold reachable in H.
  unfold composed_lts.reachable.
  destruct H as [init [acts [Hnew Hvalid]]].
  apply link_valid_compose_valid in Hvalid; auto.
  destruct Hvalid as [c_acts [Hvalid Hfilter]].
  exists init.
  exists c_acts. intuition.
Qed.

End Link.

Section Tensor.

Context {liA liB : language_interface}.
Variable L1 : lts li_null liA.
Variable L2 : lts li_null liB.

Lemma raw_tensor_reachable_single_reachable: forall s,
  reachable (RawTensor.tensor L1 L2) s ->
  reachable L1 s.(RawTensor.L1State).
Proof.
  intros. unfold reachable.
  unfold reachable in H.
  destruct H as [init [acts [Hnew Hvalid]]].
  apply RawTensor.valid_execution_fragment_com in Hvalid.
  destruct init, s. simpl in *.
  (* destruct L1State, L1State0. simpl in *. *)
  (* eapply valid_execution_fragment_sync in Hvalid; eauto. *)
  exists L1State.
  exists (gatherL1 acts).
  intuition.
  inversion Hnew; subst; simpl in *; auto.
Qed.

Lemma raw_tensor_reachable_single_reachable': forall s,
  reachable (RawTensor.tensor L1 L2) s ->
  reachable L2 s.(RawTensor.L2State).
Proof.
  intros. unfold reachable.
  unfold reachable in H.
  destruct H as [init [acts [Hnew Hvalid]]].
  apply RawTensor.valid_execution_fragment_com' in Hvalid.
  exists (RawTensor.L2State init).
  exists (gatherL2 acts).
  intuition.
  inversion Hnew; subst; simpl in *; auto.
Qed.

End Tensor.

Section RegCntProp.

Definition cnt_p (p : RCounter_pc) :=
  p = RInc2 \/
	p = RInc5  \/
	p = RRead2
  .

Definition regcnt_binds_req_binds_pc
  (s : state (linked_lts (LTS.raw_compose Register register_counter_impl))) :=
  forall pid,
    (pid \in (dom s.(LTS.RawL1State).(requests)) ->
    exists p, binds pid p s.(LTS.RawL2State).(RegisterCounterImpl.pc) /\ cnt_p p) /\
    (pid \in (dom s.(LTS.RawL1State).(responses)) ->
    exists p, binds pid p s.(LTS.RawL2State).(RegisterCounterImpl.pc) /\ cnt_p p).

Lemma register_exclusive_wf_invariant: invariant Register register_exclusive_wf.
Proof.
  apply invariant_ind_to_invariant.
  apply register_exclusive_wf_inv.
Qed.

Lemma regcnt_binds_req_binds_pc_inv:
  invariant_ind (linked_lts (LTS.raw_compose Register register_counter_impl))
  (fun x => regcnt_binds_req_binds_pc x /\ reachable _ x).
Proof.
  apply invariant_ind'_imply_invariant_ind_land.
  unfold invariant_ind'. split.
  apply reachable_is_invariant'.
  intuition.
  - unfold regcnt_binds_req_binds_pc.
    inversion H; subst; simpl in *.
    inversion H0; subst; simpl in *.
    rewrite H3.
    unfold new_register. simpl.
    intros. intuition.
  - rename H0 into Hreach.
    unfold regcnt_binds_req_binds_pc.
    simpl. intros.
    inversion H1; subst; simpl in *.
    (* reg_cnt step *)
    --
    intuition;
    inversion H0; subst; simpl in *;
    inversion H3; subst; simpl in *;
    apply H in H2; auto; simpl in *;
    destruct H2 as [p Hp];
    destruct Hp as [Hb Hc];
    destruct (eq_nat_dec pid0 pid);
      subst;
      try (unfold binds in Hb;
      rewrite Hbinds in Hb;
      inversion Hb; subst;
      unfold cnt_p in *; intuition; discriminate);
      try (eexists; intuition; eauto;
      eapply substitute_neq_preserves_binds; eauto).
    (* reg step *)
    --
    intuition.
    inversion H0; subst; simpl in *;
    inversion H3; subst; simpl in *;
    apply in_remove_inv in H2; auto;
    apply H in H2; auto.

    inversion H0; subst; simpl in *;
    inversion H3; subst; simpl in *.
    apply in_union in H2; intuition.
    simpl in H4. intuition; subst.
    apply binds_in in Hbinds.
    apply H in Hbinds; auto.
    apply H in H4; auto.

    apply in_union in H2; intuition.
    simpl in H4. intuition; subst.
    apply binds_in in Hbinds.
    apply H in Hbinds; auto.
    apply H in H4; auto.
    (* reg_cnt query *)
    --
    intuition.
    inversion H0; subst; simpl in *.
    inversion H5; subst; simpl in *.
    inversion H3; subst; simpl in *;
        apply in_union in H2;
        intuition.
          simpl in H4; intuition;
          subst;
          eexists; intuition;
          try (eapply substitute_eq_binds_v'; eauto);
          unfold cnt_p; intuition.
          eapply H in H4; simpl in *;
          destruct H4 as [p Hp];
          destruct Hp as [Hb Hc];
          assert (Hneq: pid0 <> pid) by
            (intro; subst;
            unfold binds in Hbinds;
            rewrite Hb in Hbinds;
            inversion Hbinds; subst;
            unfold cnt_p in *; intuition; discriminate);
          eexists; intuition; eauto;
          eapply substitute_neq_preserves_binds; eauto.
    inversion H3; subst; simpl in *;
        apply in_union in H2;
        intuition.
          simpl in H4; intuition;
          subst;
          eexists; intuition;
          try (eapply substitute_eq_binds_v'; eauto);
          unfold cnt_p; intuition.
          eapply H in H4; simpl in *;
          destruct H4 as [p Hp];
          destruct Hp as [Hb Hc];
          assert (Hneq: pid0 <> pid) by
            (intro; subst;
            unfold binds in Hbinds;
            rewrite Hb in Hbinds;
            inversion Hbinds; subst;
            unfold cnt_p in *; intuition; discriminate);
          eexists; intuition; eauto;
          eapply substitute_neq_preserves_binds; eauto.
        intuition.
          simpl in H4; intuition;
          subst;
          eexists; intuition;
          try (eapply substitute_eq_binds_v'; eauto);
          unfold cnt_p; intuition.
          eapply H in H4; simpl in *;
          destruct H4 as [p Hp];
          destruct Hp as [Hb Hc];
          assert (Hneq: pid0 <> pid) by
            (intro; subst;
            unfold binds in Hbinds;
            rewrite Hb in Hbinds;
            inversion Hbinds; subst;
            unfold cnt_p in *; intuition; discriminate);
          eexists; intuition; eauto;
          eapply substitute_neq_preserves_binds; eauto.
    intuition.
    inversion H0; subst; simpl in *.
    inversion H5; subst; simpl in *.
    inversion H3; subst; simpl in *.
    apply H in H2; auto; simpl in *.
    destruct H2 as [p Hp].
    destruct Hp as [Hb Hc].
    destruct (eq_nat_dec pid0 pid).
      subst.
      eexists. intuition.
      eapply substitute_eq_binds_v'; eauto.
      unfold cnt_p; intuition; discriminate.
      eexists; intuition; eauto;
      apply substitute_neq_preserves_binds; auto.
    inversion H3; subst; simpl in *.
    apply H in H2; auto; simpl in *.
    destruct H2 as [p Hp].
    destruct Hp as [Hb Hc].
    destruct (eq_nat_dec pid0 pid).
      subst.
      eexists. intuition.
      eapply substitute_eq_binds_v'; eauto.
      unfold cnt_p; intuition; discriminate.
      eexists; intuition; eauto;
      apply substitute_neq_preserves_binds; auto.
    apply H in H2; auto; simpl in *.
    destruct H2 as [p Hp].
    destruct Hp as [Hb Hc].
    destruct (eq_nat_dec pid0 pid).
      subst.
      eexists. intuition.
      eapply substitute_eq_binds_v'; eauto.
      unfold cnt_p; intuition; discriminate.
      eexists; intuition; eauto;
      apply substitute_neq_preserves_binds; auto.
    (* reg reply *)
    --
    intuition. 
    inversion H0; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *.
    destruct (eq_nat_dec pid0 pid);
        subst.
        apply link_reachable_single_reachable in Hreach.
        apply register_exclusive_wf_invariant in Hreach.
        simpl in *.
        apply Hreach  in H2; simpl in *.
        apply binds_in in Hbinds.
        unfold "#" in H2; intuition.
        apply H in H2; auto; simpl in *.
        destruct H2 as [p Hp].
        destruct Hp as [Hb Hc].
        eexists; intuition; eauto.
        apply substitute_neq_preserves_binds; auto.
    inversion H4; subst; simpl in *.
    destruct (eq_nat_dec pid0 pid);
        subst.
        apply link_reachable_single_reachable in Hreach.
        apply register_exclusive_wf_invariant in Hreach.
        simpl in *.
        apply Hreach  in H2; simpl in *.
        apply binds_in in Hbinds.
        unfold "#" in H2; intuition.
        apply H in H2; auto; simpl in *.
        destruct H2 as [p Hp].
        destruct Hp as [Hb Hc].
        eexists; intuition; eauto.
        apply substitute_neq_preserves_binds; auto.
    destruct (eq_nat_dec pid0 pid);
        subst.
        apply link_reachable_single_reachable in Hreach.
        apply register_exclusive_wf_invariant in Hreach.
        simpl in *.
        apply Hreach  in H2; simpl in *.
        apply binds_in in Hbinds.
        unfold "#" in H2; intuition.
        apply H in H2; auto; simpl in *.
        destruct H2 as [p Hp].
        destruct Hp as [Hb Hc].
        eexists; intuition; eauto.
        apply substitute_neq_preserves_binds; auto.
    inversion H0; subst; simpl in *.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *.
    destruct (eq_nat_dec pid0 pid);
        subst.
        assert (pid # (remove res pid)).
        apply ok_remove_notin; auto.
        unfold "#" in H5; intuition.
        apply remove_neq_preserves_in in H2; auto.
        apply H in H2; auto; simpl in *.
        destruct H2 as [p Hp].
        destruct Hp as [Hb Hc].
        eexists; intuition; eauto.
        apply substitute_neq_preserves_binds; auto.
    inversion H4; subst; simpl in *.
    destruct (eq_nat_dec pid0 pid);
        subst.
        assert (pid # (remove res pid)).
        apply ok_remove_notin; auto.
        unfold "#" in H5; intuition.
        apply remove_neq_preserves_in in H2; auto.
        apply H in H2; auto; simpl in *.
        destruct H2 as [p Hp].
        destruct Hp as [Hb Hc].
        eexists; intuition; eauto.
        apply substitute_neq_preserves_binds; auto.
    destruct (eq_nat_dec pid0 pid);
        subst.
        assert (pid # (remove res pid)).
        apply ok_remove_notin; auto.
        unfold "#" in H5; intuition.
        apply remove_neq_preserves_in in H2; auto.
        apply H in H2; auto; simpl in *.
        destruct H2 as [p Hp].
        destruct Hp as [Hb Hc].
        eexists; intuition; eauto.
        apply substitute_neq_preserves_binds; auto.
  - rename H0 into Hreach.
    unfold regcnt_binds_req_binds_pc.
    simpl. intros.
    intuition.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    destruct (eq_nat_dec pid0 pid);
      subst.
      apply H in H0; auto; simpl in *.
      destruct H0 as [p Hp].
      intuition.
      apply notin_get_none in Hnotin_pc.
      rewrite H0 in Hnotin_pc. discriminate.
      apply H in H0; auto; simpl in *.
      destruct H0 as [p Hp].
      destruct Hp as [Hb Hc].
      eexists; intuition; eauto.
      apply binds_push_neq; auto.
    destruct (eq_nat_dec pid0 pid);
      subst.
      apply H in H0; auto; simpl in *.
      destruct H0 as [p Hp].
      intuition.
      apply notin_get_none in Hnotin_pc.
      rewrite H0 in Hnotin_pc. discriminate.
      apply H in H0; auto; simpl in *.
      destruct H0 as [p Hp].
      destruct Hp as [Hb Hc].
      eexists; intuition; eauto.
      apply binds_push_neq; auto.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    destruct (eq_nat_dec pid0 pid);
      subst.
      apply H in H0; auto; simpl in *.
      destruct H0 as [p Hp].
      intuition.
      apply notin_get_none in Hnotin_pc.
      rewrite H0 in Hnotin_pc. discriminate.
      apply H in H0; auto; simpl in *.
      destruct H0 as [p Hp].
      destruct Hp as [Hb Hc].
      eexists; intuition; eauto.
      apply binds_push_neq; auto.
    destruct (eq_nat_dec pid0 pid);
      subst.
      apply H in H0; auto; simpl in *.
      destruct H0 as [p Hp].
      intuition.
      apply notin_get_none in Hnotin_pc.
      rewrite H0 in Hnotin_pc. discriminate.
      apply H in H0; auto; simpl in *.
      destruct H0 as [p Hp].
      destruct Hp as [Hb Hc].
      eexists; intuition; eauto.
      apply binds_push_neq; auto.
  - inversion H1.
  - inversion H1.
  - rename H0 into Hreach.
    unfold regcnt_binds_req_binds_pc.
    simpl. intros.
    intuition.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    destruct (eq_nat_dec pid0 pid);
      subst.
      apply H in H0; auto; simpl in *.
      destruct H0 as [p Hp].
      intuition.
      unfold binds in H0.
      rewrite Hbinds in H0.
      inversion H0; subst.
      unfold cnt_p in *; intuition; discriminate.
      apply H in H0; auto; simpl in *.
      destruct H0 as [p Hp].
      destruct Hp as [Hb Hc].
      eexists; intuition; eauto.
      apply remove_neq_preserves_binds; auto.
    destruct (eq_nat_dec pid0 pid);
      subst.
      apply H in H0; auto; simpl in *.
      destruct H0 as [p Hp].
      intuition.
      unfold binds in H0.
      rewrite Hbinds in H0.
      inversion H0; subst.
      unfold cnt_p in *; intuition; discriminate.
      apply H in H0; auto; simpl in *.
      destruct H0 as [p Hp].
      destruct Hp as [Hb Hc].
      eexists; intuition; eauto.
      apply remove_neq_preserves_binds; auto.
    inversion H1; subst; simpl in *.
    inversion H2; subst; simpl in *.
    destruct (eq_nat_dec pid0 pid);
      subst.
      apply H in H0; auto; simpl in *.
      destruct H0 as [p Hp].
      intuition.
      unfold binds in H0.
      rewrite Hbinds in H0.
      inversion H0; subst.
      unfold cnt_p in *; intuition; discriminate.
      apply H in H0; auto; simpl in *.
      destruct H0 as [p Hp].
      destruct Hp as [Hb Hc].
      eexists; intuition; eauto.
      apply remove_neq_preserves_binds; auto.
    destruct (eq_nat_dec pid0 pid);
      subst.
      apply H in H0; auto; simpl in *.
      destruct H0 as [p Hp].
      intuition.
      unfold binds in H0.
      rewrite Hbinds in H0.
      inversion H0; subst.
      unfold cnt_p in *; intuition; discriminate.
      apply H in H0; auto; simpl in *.
      destruct H0 as [p Hp].
      destruct Hp as [Hb Hc].
      eexists; intuition; eauto.
      apply remove_neq_preserves_binds; auto.
Qed.

Lemma regcnt_binds_req_binds_pc_invariant:
  invariant (linked_lts (LTS.raw_compose Register register_counter_impl))
  (fun x => regcnt_binds_req_binds_pc x /\ reachable _ x).
Proof.
  apply invariant_ind_to_invariant; auto.
  apply regcnt_binds_req_binds_pc_inv.
Qed.

End RegCntProp.

Section test.

Require Import
  List
  Arith
  LibVar
  LibEnv
  LTS
  Invariants
  Refinement
  Counter
  RegisterCounterImpl
  Array
  ArrayQueueInvariant
  ArrayQueueInvariantBefore.
Import ListNotations.

Variable N: nat.

Definition cnt_pc p :=
  p = AEnq2 \/
  p = AEnq11 \/
  p = AEnq14 \/
  p = AEnq31 \/
  p = ADeq2 \/
  p = ADeq11 \/
  p = ADeq14 \/
  p = ADeq31.

Definition ary_pc p :=
  p = AEnq5 \/
  p = AEnq28 \/
  p = ADeq5 \/
  p = ADeq28.

Definition cnt1_pc p :=
  p = AEnq14 \/
  p = ADeq2 \/
  p = ADeq11 \/
  p = ADeq31.

Definition cnt2_pc p :=
  p = AEnq2 \/
  p = AEnq11 \/
  p = AEnq31 \/
  p = ADeq14.

Definition pc_inv (pc : LibEnv.env AQueue_pc) h1 h2 :=
  forall pid,
  (forall p, binds pid p pc ->
    (cnt_pc p -> binds pid Run h2 /\ pid # h1) /\
    (ary_pc p -> binds pid Run h1 /\ pid # h2) /\
    (~ cnt_pc p -> ~ ary_pc p -> pid # h1 /\ pid # h2)) /\
  (pid # pc -> pid # h1 /\ pid # h2).

Definition cnt_pc_inv (pc : LibEnv.env RCounter_pc) h :=
  forall pid,
  (forall p, binds pid p pc -> binds pid Run h).
   (* /\
  (pid # pc -> pid # h). *)

Definition reg_pc_inv
  (req: LibEnv.env Register_query)
  (res: LibEnv.env Register_reply)
  h :=
  forall pid,
  (forall q, binds pid q req -> binds pid Run h) /\
  (forall r, binds pid r res -> binds pid Run h).

Definition array_reg_cnt_mutual
  (h1 : LibEnv.env Position)
  (h2 : LibEnv.env Position) :=
  forall pid,
    (binds pid Run h1 -> pid # h2) /\
    (binds pid Run h2 -> pid # h1).

Definition pos_wf
  (h1 : LibEnv.env Position)
  (h2 : LibEnv.env Position) :=
  ok h1 /\ ok h2.

Definition ary_pc_inv
  (req: LibEnv.env Array_query)
  (res: LibEnv.env Array_reply)
  h :=
  forall pid,
  (forall q, binds pid q req -> binds pid Run h) /\
  (forall r, binds pid r res -> binds pid Run h).

Definition pc_cnt_pc (pc : LibEnv.env AQueue_pc) (pc1 pc2 : LibEnv.env RCounter_pc) :=
  forall pid,
  (forall p, binds pid p pc ->
    (cnt1_pc p -> pid \in dom pc1 /\ pid # pc2) /\
    (cnt2_pc p -> pid \in dom pc2 /\ pid # pc1) /\
    (~ cnt1_pc p -> ~ cnt2_pc p -> pid # pc1 /\ pid # pc2)) /\
  (pid # pc -> pid # pc1 /\ pid # pc2).

Lemma remove_sc:
refines
  (LTS.linked_lts
     (LTS.raw_compose
        (RawTensor.tensor (array N)
           (RawTensor.tensor
              (LTS.linked_lts
                 (LTS.raw_compose Register
                    register_counter_impl))
              (LTS.linked_lts
                 (LTS.raw_compose Register
                    register_counter_impl))))
        (array_queue_impl N)))
  (LTS.linked_lts
     (LTS.raw_compose
        (tensor (array N)
           (RawTensor.tensor
              (LTS.linked_lts
                 (LTS.raw_compose Register
                    register_counter_impl))
              (LTS.linked_lts
                 (LTS.raw_compose Register
                    register_counter_impl))))
        (array_queue_impl N))).
Proof.
  eapply forward_simulation_inv_ind
    with (f:=fun (x : state 
  (LTS.linked_lts
     (LTS.raw_compose
        (RawTensor.tensor (array N)
           (RawTensor.tensor
              (LTS.linked_lts
                 (LTS.raw_compose Register
                    register_counter_impl))
              (LTS.linked_lts
                 (LTS.raw_compose Register
                    register_counter_impl))))
        (array_queue_impl N)))
) (y : state (LTS.linked_lts
     (LTS.raw_compose
        (tensor (array N)
           (RawTensor.tensor
              (LTS.linked_lts
                 (LTS.raw_compose Register
                    register_counter_impl))
              (LTS.linked_lts
                 (LTS.raw_compose Register
                    register_counter_impl))))
        (array_queue_impl N)))) =>
        x.(LTS.RawL1State).(RawTensor.L1State) =
        y.(LTS.RawL1State).(Tensor.L1State).(LState) /\
        x.(LTS.RawL1State).(RawTensor.L2State) =
        y.(LTS.RawL1State).(Tensor.L2State).(LState) /\
        x.(LTS.RawL2State) =
        y.(LTS.RawL2State) /\

        (* reg_cnt_pos
          x.(LTS.RawL1State).(RawTensor.L2State).(RawTensor.L1State).(LTS.RawL2State).(RegisterCounterImpl.pc)
          x.(LTS.RawL1State).(RawTensor.L2State).(RawTensor.L2State).(LTS.RawL2State).(RegisterCounterImpl.pc)
          x.(LTS.RawL1State).(RawTensor.L2State).(RawTensor.L1State).(LTS.RawL1State).(Register.requests)
          x.(LTS.RawL1State).(RawTensor.L2State).(RawTensor.L1State).(LTS.RawL1State).(Register.responses)
          x.(LTS.RawL1State).(RawTensor.L2State).(RawTensor.L2State).(LTS.RawL1State).(Register.requests)
          x.(LTS.RawL1State).(RawTensor.L2State).(RawTensor.L2State).(LTS.RawL1State).(Register.responses)
          y.(LTS.RawL1State).(Tensor.L2State).(PidPos) /\ *)

        pc_inv
          y.(LTS.RawL2State).(ArrayQueueImpl.pc)
          y.(LTS.RawL1State).(Tensor.L1State).(PidPos)
          y.(LTS.RawL1State).(Tensor.L2State).(PidPos) /\
        cnt_pc_inv
          x.(LTS.RawL1State).(RawTensor.L2State).(RawTensor.L1State).(LTS.RawL2State).(RegisterCounterImpl.pc)
          y.(LTS.RawL1State).(Tensor.L2State).(PidPos) /\
        cnt_pc_inv
          x.(LTS.RawL1State).(RawTensor.L2State).(RawTensor.L2State).(LTS.RawL2State).(RegisterCounterImpl.pc)
          y.(LTS.RawL1State).(Tensor.L2State).(PidPos) /\
        (* reg_pc_inv
          x.(LTS.RawL1State).(RawTensor.L2State).(RawTensor.L1State).(LTS.RawL1State).(Register.requests)
          x.(LTS.RawL1State).(RawTensor.L2State).(RawTensor.L1State).(LTS.RawL1State).(Register.responses)
          y.(LTS.RawL1State).(Tensor.L2State).(PidPos) /\
        reg_pc_inv
          x.(LTS.RawL1State).(RawTensor.L2State).(RawTensor.L2State).(LTS.RawL1State).(Register.requests)
          x.(LTS.RawL1State).(RawTensor.L2State).(RawTensor.L2State).(LTS.RawL1State).(Register.responses)
          y.(LTS.RawL1State).(Tensor.L2State).(PidPos) /\ *)
        array_reg_cnt_mutual
          y.(LTS.RawL1State).(Tensor.L1State).(PidPos)
          y.(LTS.RawL1State).(Tensor.L2State).(PidPos) /\
        pos_wf
          y.(LTS.RawL1State).(Tensor.L1State).(PidPos)
          y.(LTS.RawL1State).(Tensor.L2State).(PidPos) /\
        ary_pc_inv
          x.(LTS.RawL1State).(RawTensor.L1State).(Array.requests N)
          x.(LTS.RawL1State).(RawTensor.L1State).(responses N)
          y.(LTS.RawL1State).(Tensor.L1State).(PidPos) /\
        pc_cnt_pc
          y.(LTS.RawL2State).(ArrayQueueImpl.pc)
          x.(LTS.RawL1State).(RawTensor.L2State).(RawTensor.L1State).(LTS.RawL2State).(RegisterCounterImpl.pc)
          x.(LTS.RawL1State).(RawTensor.L2State).(RawTensor.L2State).(LTS.RawL2State).(RegisterCounterImpl.pc)
        (* cnt_pc_mutual
          x.(LTS.RawL1State).(RawTensor.L2State).(RawTensor.L1State).(LTS.RawL2State).(RegisterCounterImpl.pc)
          x.(LTS.RawL1State).(RawTensor.L2State).(RawTensor.L2State).(LTS.RawL2State).(RegisterCounterImpl.pc) *)
        (* pc_mutual
          x.(LTS.RawL1State).(RawTensor.L2State).(RawTensor.L1State).(LTS.RawL2State).(RegisterCounterImpl.pc)
          x.(LTS.RawL1State).(RawTensor.L2State).(RawTensor.L2State).(LTS.RawL2State).(RegisterCounterImpl.pc) *)
        (* reg_cnt_pos_inv
          x.(LTS.RawL1State).(RawTensor.L2State).(RawTensor.L1State).(LTS.RawL2State).(RegisterCounterImpl.pc)
          x.(LTS.RawL1State).(RawTensor.L2State).(RawTensor.L2State).(LTS.RawL2State).(RegisterCounterImpl.pc)
          y.(LTS.RawL1State).(Tensor.L2State).(PidPos) *)
      )
      (inv:=fun x => reachable _ x).
  unfold fsim_properties_inv_ind. intuition.
  - apply reachable_is_invariant'.
  - simpl in *.
    inversion H; subst; simpl in *.
    inversion H0; subst; simpl in *.
    exists (@mkRawComposedState 
      (tensor_li li_array (tensor_li li_counter li_counter)) li_queue
        (tensor (array N)
            (RawTensor.tensor
               (linked_lts
                  (raw_compose Register
                     register_counter_impl))
               (linked_lts
                  (raw_compose Register
                     register_counter_impl))))
      (array_queue_impl N)
      (@Tensor.mkTensorState li_array (tensor_li li_counter li_counter)
        (array N) ((RawTensor.tensor
               (linked_lts
                  (raw_compose Register register_counter_impl))
               (linked_lts
                  (raw_compose Register register_counter_impl))))
        (mkSyncState (array N)
          (RawTensor.L1State (RawL1State s1))
          []
        )
        (mkSyncState ((RawTensor.tensor
               (linked_lts
                  (raw_compose Register register_counter_impl))
               (linked_lts
                  (raw_compose Register register_counter_impl))))
          (RawTensor.L2State (RawL1State s1))
          []
        )
      )
      (RawL2State s1)
    ).
    simpl. intuition.
    unfold raw_composed_new_state.
    simpl. intuition.
    unfold tensor_new_state.
    simpl.
    unfold sync_new_state.
    simpl in *.
    inversion H2; subst; simpl in *.
    rewrite H5.
    intuition.
    unfold array_new_state.
    intuition.
    inversion H1; subst; simpl in *.
    rewrite H5.
    unfold new_array_queue.
    simpl.
    unfold pc_inv.
    simpl. intuition; inversion H4.
    unfold cnt_pc_inv.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *.
    inversion H7; subst; simpl in *.
    inversion H9; subst; simpl in *.
    rewrite H11.
    unfold new_register_counter. simpl.
    intuition; inversion H10.
    unfold cnt_pc_inv.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *.
    inversion H7; subst; simpl in *.
    inversion H9; subst; simpl in *.
    rewrite H12.
    unfold new_register_counter. simpl.
    intuition; inversion H10.
    (* unfold reg_pc_inv.
    simpl.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *.
    inversion H6; subst; simpl in *.
    inversion H8; subst; simpl in *.
    rewrite H11.
    unfold new_register. simpl.
    intuition; inversion H10.
    unfold reg_pc_inv.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *.
    inversion H6; subst; simpl in *.
    inversion H8; subst; simpl in *.
    rewrite H12.
    unfold new_register. simpl.
    intuition; inversion H10. *)
    unfold array_reg_cnt_mutual.
    intuition; inversion H4; subst.
    unfold pos_wf.
    intuition; econstructor.
    unfold ary_pc_inv.
    simpl.
    inversion H2; subst; simpl in *.
    rewrite H5.
    unfold new_array. simpl.
    intuition; inversion H4.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *.
    inversion H7; subst; simpl in *.
    inversion H9; subst; simpl in *.
    rewrite H11, H12.
    inversion H1; subst; simpl in *.
    rewrite H13.
    unfold new_array_queue. simpl.
    unfold pc_cnt_pc. simpl.
    intuition; inversion H10.
    (* inversion H1; subst; simpl in *. *)
    (* rewrite H5. *)
    (* unfold cnt_pc_mutual.
    inversion H3; subst; simpl in *.
    inversion H4; subst; simpl in *.
    inversion H5; subst; simpl in *.
    inversion H7; subst; simpl in *.
    inversion H9; subst; simpl in *.
    rewrite H11, H12.
    simpl. intuition; inversion H10. *)
  - rename H2 into Hary.
    rename H0 into Hcnt.
    rename H3 into Hqueue.
    rename H4 into Hpc_inv.
    rename H5 into Hcnt_pc_inv1.
    rename H6 into Hcnt_pc_inv2.
    (* rename H7 into Hreg_pc_inv1.
    rename H8 into Hreg_pc_inv2. *)
    rename H7 into Hmutual.
    rename H8 into Hwf.
    rename H9 into Hary_pc_inv.
    rename H11 into Hpc_cnt_pc.
    (* rename H13 into Hcnt_pc_mutual. *)
    inversion H1; subst; simpl in *.
    exists (@mkRawComposedState 
      (tensor_li li_array (tensor_li li_counter li_counter)) li_queue
        (tensor (array N)
            (RawTensor.tensor
               (linked_lts
                  (raw_compose Register
                     register_counter_impl))
               (linked_lts
                  (raw_compose Register
                     register_counter_impl))))
      (array_queue_impl N)
      (@Tensor.mkTensorState li_array (tensor_li li_counter li_counter)
        (array N) ((RawTensor.tensor
               (linked_lts
                  (raw_compose Register register_counter_impl))
               (linked_lts
                  (raw_compose Register register_counter_impl))))
        (mkSyncState (array N)
          (RawTensor.L1State st1)
          (PidPos (L1State (RawL1State s2)))
        )
        (mkSyncState ((RawTensor.tensor
               (linked_lts
                  (raw_compose Register register_counter_impl))
               (linked_lts
                  (raw_compose Register register_counter_impl))))
          (RawTensor.L2State st1)
          (PidPos (L2State (RawL1State s2)))
        )
      )
      st2'
    ).
    simpl. intuition.
     destruct s2; simpl in *.
     destruct RawL1State; simpl in *.
     destruct L1State; simpl in *.
     destruct L2State; simpl in *.
     subst.
     eapply raw_composed_initial_state_L2; eauto.
     unfold pc_inv.
     simpl.
     2 : {
      inversion H0; subst; simpl in *;
      rewrite H2 in Hpc_cnt_pc; simpl in *.
      unfold pc_cnt_pc.
      simpl. intros. split.
        intros. apply binds_push_inv in H3; auto.
        destruct H3.
          destruct H3. subst.
          unfold cnt1_pc, cnt2_pc in *; intuition; try discriminate;
          eapply Hpc_cnt_pc in Hnotin_pc; eauto; intuition.
          destruct H3. subst. intuition;
            eapply Hpc_cnt_pc in H5; eauto; intuition.
      intros. apply notin_union in H3.
      intuition;
      eapply Hpc_cnt_pc in H5; eauto; intuition.

      unfold pc_cnt_pc.
      simpl. intros. split.
        intros. apply binds_push_inv in H3; auto.
        destruct H3.
          destruct H3. subst.
          unfold cnt1_pc, cnt2_pc in *; intuition; try discriminate;
          eapply Hpc_cnt_pc in Hnotin_pc; eauto; intuition.
          destruct H3. subst. intuition;
            eapply Hpc_cnt_pc in H5; eauto; intuition.
      intros. apply notin_union in H3.
      intuition;
      eapply Hpc_cnt_pc in H5; eauto; intuition.
     }

     inversion H0; subst; simpl in *.
     all : rewrite H2 in Hpc_inv;
     simpl in *;
     intros; split;
     [
      intros;
      apply binds_push_inv in H3; auto;
      destruct H3;
      [intuition; subst;
      unfold cnt_pc, ary_pc in *;
      intuition; try discriminate;
      apply Hpc_inv in Hnotin_pc; auto; intuition |
      destruct H3; intuition; subst;
      eapply Hpc_inv in H5; eauto; intuition]|
      intuition;
      apply notin_union in H3;
      intuition;
      apply Hpc_inv in H5; intuition].
  - rename H2 into Hary.
    rename H0 into Hcnt.
    rename H3 into Hqueue.
    rename H4 into Hpc_inv.
    rename H5 into Hcnt_pc_inv1.
    rename H6 into Hcnt_pc_inv2.
    (* rename H7 into Hreg_pc_inv1.
    rename H8 into Hreg_pc_inv2. *)
    rename H7 into Hmutual.
    rename H8 into Hwf.
    rename H9 into Hary_pc_inv.
    rename H11 into Hpc_cnt_pc.
    (* rename H13 into Hcnt_pc_mutual. *)
    inversion H1; subst; simpl in *.

    exists (@mkRawComposedState 
      (tensor_li li_array (tensor_li li_counter li_counter)) li_queue
        (tensor (array N)
            (RawTensor.tensor
               (linked_lts
                  (raw_compose Register
                     register_counter_impl))
               (linked_lts
                  (raw_compose Register
                     register_counter_impl))))
      (array_queue_impl N)
      (@Tensor.mkTensorState li_array (tensor_li li_counter li_counter)
        (array N) ((RawTensor.tensor
               (linked_lts
                  (raw_compose Register register_counter_impl))
               (linked_lts
                  (raw_compose Register register_counter_impl))))
        (mkSyncState (array N)
          (RawTensor.L1State st1)
          (PidPos (L1State (RawL1State s2)))
        )
        (mkSyncState ((RawTensor.tensor
               (linked_lts
                  (raw_compose Register register_counter_impl))
               (linked_lts
                  (raw_compose Register register_counter_impl))))
          (RawTensor.L2State st1)
          (PidPos (L2State (RawL1State s2)))
        )
      )
      st2'
    ).
    simpl. intuition.
     destruct s2; simpl in *.
     destruct RawL1State; simpl in *.
     destruct L1State; simpl in *.
     destruct L2State; simpl in *.
     subst.
     eapply raw_composed_final_state_L2; eauto.
     unfold pc_inv.
     simpl.
     inversion H0; subst; simpl in *.
     rewrite H2 in Hpc_inv; simpl in *;
     simpl in *;
     intros; split;
      [intros;
      apply binds_remove_inv in H3; auto;
      intuition;
      eapply Hpc_inv in H4; eauto; intuition|
      intuition;
      destruct (eq_nat_dec pid0 pid);
      try (apply remove_neq_preserves_notin in H3; auto;
        eapply Hpc_inv in H3; eauto; intuition);
        subst;
        eapply Hpc_inv in Hbinds; eauto;
        apply Hbinds; eauto; clear Hbinds;
        unfold cnt_pc, ary_pc in *;
        intuition; discriminate].
     rewrite H3 in Hpc_inv; simpl in *;
     simpl in *;
     intros; split;
      [intros;
      apply binds_remove_inv in H4; auto;
      intuition;
      eapply Hpc_inv in H5; eauto; intuition|
      intuition;
      destruct (eq_nat_dec pid0 pid);
      try (apply remove_neq_preserves_notin in H4; auto;
        eapply Hpc_inv in H4; eauto; intuition);
        subst;
        eapply Hpc_inv in Hbinds; eauto;
        apply Hbinds; eauto; clear Hbinds;
        unfold cnt_pc, ary_pc in *;
        intuition; discriminate].

      inversion H0; subst; simpl in *.
      rewrite H2 in Hpc_cnt_pc; simpl in *.
      unfold pc_cnt_pc.
      simpl. intros. split.
        intros. apply binds_remove_inv in H3; auto.
        apply Hpc_cnt_pc in H3; auto.
      intros.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hpc_cnt_pc in Hbinds; auto.
        apply Hbinds; auto; clear Hbinds; auto;
        unfold cnt1_pc, cnt2_pc; intuition; discriminate.
        apply remove_neq_preserves_notin in H3; auto.
        apply Hpc_cnt_pc in H3; auto.

      rewrite H3 in Hpc_cnt_pc; simpl in *.
      unfold pc_cnt_pc.
      simpl. intros. split.
        intros. apply binds_remove_inv in H4; auto.
        apply Hpc_cnt_pc in H4; auto.
      intros.
      destruct (eq_nat_dec pid0 pid).
        subst.
        apply Hpc_cnt_pc in Hbinds; auto.
        apply Hbinds; auto; clear Hbinds; auto;
        unfold cnt1_pc, cnt2_pc; intuition; discriminate.
        apply remove_neq_preserves_notin in H4; auto.
        apply Hpc_cnt_pc in H4; auto.
      
  - rename H2 into Hary.
    rename H0 into Hcnt.
    rename H3 into Hqueue.
    rename H4 into Hpc_inv.
    rename H5 into Hcnt_pc_inv1.
    rename H6 into Hcnt_pc_inv2.
    (* rename H7 into Hreg_pc_inv1.
    rename H8 into Hreg_pc_inv2. *)
    rename H7 into Hmutual.
    rename H8 into Hwf.
    rename H9 into Hary_pc_inv.
    rename H11 into Hpc_cnt_pc.
    (* rename H13 into Hcnt_pc_mutual. *)
    inversion H1; subst; simpl in *.

    (* M_queue step *)
    --
    inversion H0; subst; simpl in *.
    exists (@mkRawComposedState 
      (tensor_li li_array (tensor_li li_counter li_counter)) li_queue
        (tensor (array N)
            (RawTensor.tensor
               (linked_lts
                  (raw_compose Register
                     register_counter_impl))
               (linked_lts
                  (raw_compose Register
                     register_counter_impl))))
      (array_queue_impl N)
      (@Tensor.mkTensorState li_array (tensor_li li_counter li_counter)
        (array N) ((RawTensor.tensor
               (linked_lts
                  (raw_compose Register register_counter_impl))
               (linked_lts
                  (raw_compose Register register_counter_impl))))
        (mkSyncState (array N)
          (RawTensor.L1State st1)
          (PidPos (L1State (RawL1State s2)))
        )
        (mkSyncState ((RawTensor.tensor
               (linked_lts
                  (raw_compose Register register_counter_impl))
               (linked_lts
                  (raw_compose Register register_counter_impl))))
          (RawTensor.L2State st1)
          (PidPos (L2State (RawL1State s2)))
        )
      )
      st2'
    ).
    simpl. intuition.
     destruct s2; simpl in *.
     destruct RawL1State; simpl in *.
     destruct L1State; simpl in *.
     destruct L2State; simpl in *.
     subst.
     eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply linked_step_int_L2; eauto.
    simpl.
    eapply raw_composed_step_L2_internal; eauto.
    unfold pc_inv.
      intros. split.
      intros.
      inversion H2; subst; simpl in *.
      all : try (rewrite H4 in Hpc_inv; simpl in *;
      destruct (eq_nat_dec pid0 pid);
      try (apply substitute_neq_preserves_binds' in H3; auto;
        eapply Hpc_inv in H3; eauto);
        subst;
        pose proof Hbinds as Hbinds';
        eapply substitute_eq_binds_v' in Hbinds;
        unfold binds in Hbinds;
        rewrite H3 in Hbinds; auto;
        inversion Hbinds; subst; simpl in *;
        eapply Hpc_inv in Hbinds'; eauto;
        destruct Hbinds' as [Hb1 Hb2];
        destruct Hb2 as [Hb2 Hb3];
        unfold ary_pc, cnt_pc; intuition; try discriminate;
        apply Hb3; auto;
        unfold ary_pc, cnt_pc; intuition; try discriminate).

      all : try (rewrite H5 in Hpc_inv; simpl in *;
      destruct (eq_nat_dec pid0 pid);
      try (apply substitute_neq_preserves_binds' in H3; auto;
        eapply Hpc_inv in H3; eauto);
        subst;
        pose proof Hbinds as Hbinds';
        eapply substitute_eq_binds_v' in Hbinds;
        unfold binds in Hbinds;
        rewrite H3 in Hbinds; auto;
        inversion Hbinds; subst; simpl in *;
        eapply Hpc_inv in Hbinds'; eauto;
        destruct Hbinds' as [Hb1 Hb2];
        destruct Hb2 as [Hb2 Hb3];
        unfold ary_pc, cnt_pc; intuition; try discriminate;
        apply Hb3; auto;
        unfold ary_pc, cnt_pc; intuition; try discriminate).
    inversion H2; subst; simpl in *.
      all : try (
      try (rewrite H3 in Hpc_inv);
      try (rewrite H4 in Hpc_inv);
      simpl in *;
      intros;
      try (apply substitute_preserves_notin' in H3; auto;
      apply Hpc_inv in H3; auto);
      try (apply substitute_preserves_notin' in H4; auto;
      apply Hpc_inv in H4; auto);
      try (apply substitute_preserves_notin' in H5; auto;
      apply Hpc_inv in H5; auto)).

      unfold pc_cnt_pc.
      simpl. intros. split.
        intros.
        inversion H2; subst; simpl in *.
        all: try(
        rewrite H4 in Hpc_cnt_pc; simpl in *;
        destruct (eq_nat_dec pid0 pid);
          subst;
          try (apply substitute_neq_preserves_binds' in H3; auto;
          apply Hpc_cnt_pc in H3; auto);
            split; intros;

            try (split; intros;
              try (pose proof Hbinds as Hbinds';
              eapply Hpc_cnt_pc in Hbinds'; eauto;
              eapply Hbinds'; eauto; clear Hbinds';
              unfold cnt1_pc, cnt2_pc; intuition; discriminate);
              eapply substitute_eq_binds_v' in Hbinds; eauto;
              unfold binds in Hbinds;
              rewrite H3 in Hbinds;
              inversion Hbinds; subst;
              unfold cnt1_pc, cnt2_pc in *; intuition; discriminate)).

        all: try(
        rewrite H5 in Hpc_cnt_pc; simpl in *;
        destruct (eq_nat_dec pid0 pid);
          subst;
          try (apply substitute_neq_preserves_binds' in H3; auto;
          apply Hpc_cnt_pc in H3; auto);
            split; intros;

            try (split; intros;
              try (pose proof Hbinds as Hbinds';
              eapply Hpc_cnt_pc in Hbinds'; eauto;
              eapply Hbinds'; eauto; clear Hbinds';
              unfold cnt1_pc, cnt2_pc; intuition; discriminate);
              eapply substitute_eq_binds_v' in Hbinds; eauto;
              unfold binds in Hbinds;
              rewrite H3 in Hbinds;
              inversion Hbinds; subst;
              unfold cnt1_pc, cnt2_pc in *; intuition; discriminate)).
        intros.
        inversion H2; subst; simpl in *;
        try (rewrite H4 in Hpc_cnt_pc; simpl in *);
        try (rewrite H5 in Hpc_cnt_pc; simpl in *);
        apply substitute_preserves_notin' in H3; auto;
        apply Hpc_cnt_pc in H3; auto.
    (* L_ary-(L_reg <| M_cnt)-(L_reg <| M_cnt) step *)
    --
    inversion H0; subst; simpl in *.
    inversion H2; subst; simpl in *.
    (* (L_reg <| M_cnt)-(L_reg <| M_cnt) step *)
    ---
    exists (@mkRawComposedState 
      (tensor_li li_array (tensor_li li_counter li_counter)) li_queue
        (tensor (array N)
            (RawTensor.tensor
               (linked_lts
                  (raw_compose Register
                     register_counter_impl))
               (linked_lts
                  (raw_compose Register
                     register_counter_impl))))
      (array_queue_impl N)
      (@Tensor.mkTensorState li_array (tensor_li li_counter li_counter)
        (array N) ((RawTensor.tensor
               (linked_lts
                  (raw_compose Register register_counter_impl))
               (linked_lts
                  (raw_compose Register register_counter_impl))))
        (mkSyncState (array N)
          st0
          (PidPos (L1State (RawL1State s2)))
        )
        (mkSyncState ((RawTensor.tensor
               (linked_lts
                  (raw_compose Register register_counter_impl))
               (linked_lts
                  (raw_compose Register register_counter_impl))))
          st2'
          (PidPos (L2State (RawL1State s2)))
        )
      )
      (RawL2State s2)
    ).
    simpl. intuition.
     destruct s2; simpl in *.
     destruct RawL1State; simpl in *.
     destruct L1State; simpl in *.
     destruct L2State; simpl in *.
     subst.
     eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply linked_step_int_L1; eauto.
    simpl.
    eapply raw_composed_step_L1_internal; eauto.
    simpl.

    assert (Hb : binds pid Run PidPos0).

    inversion H3; subst; simpl in *.
    (* (L_reg <| M_cnt)2 step *)
    inversion H4; subst; simpl in *.
    (* M_cnt 2 step *)
    inversion H5; subst; simpl in *;
    inversion H6; subst; simpl in *;
      apply Hcnt_pc_inv2 in Hbinds; auto.
    (* L_reg 2 step *)
    inversion H5; subst; simpl in *;
    inversion H6; subst; simpl in *;
      apply link_reachable_single_reachable in H;
      apply raw_tensor_reachable_single_reachable' in H;
      simpl in *;
      apply raw_tensor_reachable_single_reachable' in H;
      apply regcnt_binds_req_binds_pc_invariant in H;
      destruct H as [H _];
      simpl in *;
      apply binds_in in Hbinds;
    apply H in Hbinds; auto; simpl in *;
    destruct Hbinds as [p [Hb Hc]];
    apply Hcnt_pc_inv2 in Hb; auto.
    (* M_cnt 2 query *)
    inversion H5; subst; simpl in *;
    inversion H6; subst; simpl in *;
      apply Hcnt_pc_inv2 in Hbinds; auto.
    (* M_cnt 2 reply *)
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
      apply Hcnt_pc_inv2 in Hbinds; auto.

    (* (L_reg <| M_cnt)1 step *)
    inversion H4; subst; simpl in *.
    (* M_cnt 1 step *)
    inversion H5; subst; simpl in *;
    inversion H6; subst; simpl in *;
      apply Hcnt_pc_inv1 in Hbinds; auto.
    (* L_reg 1 step *)
    inversion H5; subst; simpl in *;
    inversion H6; subst; simpl in *;
      apply link_reachable_single_reachable in H;
      apply raw_tensor_reachable_single_reachable' in H;
      simpl in *;
      apply raw_tensor_reachable_single_reachable in H;
      apply regcnt_binds_req_binds_pc_invariant in H;
      destruct H as [H _];
      simpl in *;
      apply binds_in in Hbinds;
    apply H in Hbinds; auto; simpl in *;
    destruct Hbinds as [p [Hb Hc]];
    apply Hcnt_pc_inv1 in Hb; auto.
    (* M_cnt 1 query *)
    inversion H5; subst; simpl in *;
    inversion H6; subst; simpl in *;
      apply Hcnt_pc_inv1 in Hbinds; auto.
    (* M_cnt 1 reply *)
    inversion H5; subst; simpl in *;
    inversion H7; subst; simpl in *;
      apply Hcnt_pc_inv1 in Hbinds; auto.

    eapply tensor_step_L2_internal with (pid:=pid); eauto.
    simpl in *.
    auto.
    simpl.
    apply Hmutual; auto.
    simpl.
    eapply sync_step_L_internal; eauto.
    apply Hwf; auto.
    unfold cnt_pc_inv.
    intuition.
      inversion H3; subst; simpl in *;
    (* (L_reg <| M_cnt)2 step *)
      rewrite H6 in Hcnt_pc_inv1; simpl in *;
      rewrite H6 in Hcnt_pc_inv2; simpl in *.
      apply Hcnt_pc_inv1 in H4; auto.
    (* (L_reg <| M_cnt)1 step *)
      inversion H5; subst; simpl in *.
      (* M_cnt 1 step *)
        inversion H7; subst; simpl in *;
        inversion H8; subst; simpl in *;
          destruct (eq_nat_dec pid0 pid);
            subst;
            try (eapply Hcnt_pc_inv1; eauto);
            eapply substitute_neq_preserves_binds' in H4; eauto.
      (* L_reg 1 step *)
        inversion H7; subst; simpl in *.
        eapply Hcnt_pc_inv1; eauto.
      (* M_cnt 1 query *)
        inversion H7; subst; simpl in *;
        inversion H8; subst; simpl in *;
          destruct (eq_nat_dec pid0 pid);
            subst;
            try (eapply Hcnt_pc_inv1; eauto);
            eapply substitute_neq_preserves_binds' in H4; eauto.
      (* L_reg 1 reply *)
        inversion H7; subst; simpl in *;
        inversion H9; subst; simpl in *;
          destruct (eq_nat_dec pid0 pid);
            subst;
            try (eapply Hcnt_pc_inv1; eauto);
            eapply substitute_neq_preserves_binds' in H4; eauto.

    unfold cnt_pc_inv.
    intuition.
      inversion H3; subst; simpl in *;
    (* (L_reg <| M_cnt)2 step *)
      rewrite H6 in Hcnt_pc_inv1; simpl in *;
      rewrite H6 in Hcnt_pc_inv2; simpl in *.
      (* apply Hcnt_pc_inv1 in H4; auto. *)
    (* (L_reg <| M_cnt)1 step *)
      inversion H5; subst; simpl in *.
      (* M_cnt 1 step *)
        inversion H7; subst; simpl in *;
        inversion H8; subst; simpl in *;
          destruct (eq_nat_dec pid0 pid);
            subst;
            try (eapply Hcnt_pc_inv2; eauto);
            eapply substitute_neq_preserves_binds' in H4; eauto.
      (* L_reg 1 step *)
        inversion H7; subst; simpl in *.
        eapply Hcnt_pc_inv2; eauto.
      (* M_cnt 1 query *)
        inversion H7; subst; simpl in *;
        inversion H8; subst; simpl in *;
          destruct (eq_nat_dec pid0 pid);
            subst;
            try (eapply Hcnt_pc_inv2; eauto);
            eapply substitute_neq_preserves_binds' in H4; eauto.
      (* L_reg 1 reply *)
        inversion H7; subst; simpl in *;
        inversion H9; subst; simpl in *;
          destruct (eq_nat_dec pid0 pid);
            subst;
            try (eapply Hcnt_pc_inv2; eauto);
            eapply substitute_neq_preserves_binds' in H4; eauto.
      apply Hcnt_pc_inv2 in H4; auto.

    (* unfold reg_pc_inv.
    intuition.
      inversion H3; subst; simpl in *;
    (* (L_reg <| M_cnt)2 step *)
      rewrite H6 in Hreg_pc_inv1; simpl in *;
      rewrite H6 in Hreg_pc_inv2; simpl in *;
      rewrite H6 in Hcnt_pc_inv1; simpl in *;
      rewrite H6 in Hcnt_pc_inv2; simpl in *.
      apply Hreg_pc_inv1 in H4; auto.
    (* (L_reg <| M_cnt)1 step *)
      inversion H5; subst; simpl in *.
      (* M_cnt 1 step *)
        inversion H7; subst; simpl in *;
        eapply Hreg_pc_inv1 in H4; eauto.
      (* L_reg 1 step *)
        inversion H7; subst; simpl in *.
        inversion H8; subst; simpl in *;
        apply binds_remove_inv in H4; auto;
        eapply Hreg_pc_inv1 in H4; eauto.
      (* M_cnt 1 query *)
        inversion H7; subst; simpl in *;
        inversion H10; subst; simpl in *;
        apply binds_push_inv in H4; auto;
        intuition;
        try (eapply Hreg_pc_inv1 in H11; eauto);
          subst;
          inversion H8; subst; simpl in *;
          eapply Hcnt_pc_inv1; eauto.
      (* L_reg 1 reply *)
        inversion H7; subst; simpl in *.
        inversion H8; subst; simpl in *;
        apply Hreg_pc_inv1 in H4; auto.

    unfold reg_pc_inv.
    intuition.
      inversion H3; subst; simpl in *;
    (* (L_reg <| M_cnt)2 step *)
      rewrite H6 in Hreg_pc_inv1; simpl in *;
      rewrite H6 in Hreg_pc_inv2; simpl in *;
      rewrite H6 in Hcnt_pc_inv1; simpl in *;
      rewrite H6 in Hcnt_pc_inv2; simpl in *.
      apply Hreg_pc_inv1 in H4; auto.
    (* (L_reg <| M_cnt)1 step *)
      inversion H5; subst; simpl in *.
      (* M_cnt 1 step *)
        inversion H7; subst; simpl in *;
        eapply Hreg_pc_inv1 in H4; eauto.
      (* L_reg 1 step *)
        inversion H7; subst; simpl in *.
        inversion H8; subst; simpl in *.
        apply binds_push_inv in H4; auto;
        intuition.
          subst. apply Hreg_pc_inv1 in Hbinds; auto.
          apply Hreg_pc_inv1 in H10; auto.
      (* M_cnt 1 query *)
        apply binds_push_inv in H4; auto.
        intuition.
          subst. apply Hreg_pc_inv1 in Hbinds; auto.
          apply Hreg_pc_inv1 in H10; auto.
      (* L_reg 1 reply *)
        inversion H7; subst; simpl in *.
        inversion H10; subst; simpl in *;
          apply Hreg_pc_inv1 in H4; auto.
        inversion H7; subst; simpl in *.
        inversion H8; subst; simpl in *;
        apply binds_remove_inv in H4; auto;
        apply Hreg_pc_inv1 in H4; auto.

    unfold reg_pc_inv.
    intuition.
      inversion H3; subst; simpl in *;
    (* (L_reg <| M_cnt)2 step *)
      rewrite H6 in Hreg_pc_inv1; simpl in *;
      rewrite H6 in Hreg_pc_inv2; simpl in *;
      rewrite H6 in Hcnt_pc_inv1; simpl in *;
      rewrite H6 in Hcnt_pc_inv2; simpl in *.
      (* apply Hreg_pc_inv1 in H4; auto. *)
    (* (L_reg <| M_cnt)1 step *)
      inversion H5; subst; simpl in *.
      (* M_cnt 1 step *)
        inversion H7; subst; simpl in *;
        eapply Hreg_pc_inv2 in H4; eauto.
      (* L_reg 1 step *)
        inversion H7; subst; simpl in *.
        inversion H8; subst; simpl in *;
        apply binds_remove_inv in H4; auto;
        apply Hreg_pc_inv2 in H4; auto.
      (* M_cnt 1 query *)
        inversion H7; subst; simpl in *.
        inversion H10; subst; simpl in *.
        apply binds_push_inv in H4; auto.
        intuition.
          subst.
          inversion H8; subst; simpl in *.
          apply Hcnt_pc_inv2 in Hbinds; auto.
          apply Hreg_pc_inv2 in H11; auto.
      (* L_reg 1 reply *)
        apply binds_push_inv in H4; auto.
        intuition.
          subst.
          inversion H8; subst; simpl in *;
          apply Hcnt_pc_inv2 in Hbinds; auto.
          apply Hreg_pc_inv2 in H11; auto.
        inversion H7; subst; simpl in *.
        inversion H8; subst; simpl in *;
          apply Hreg_pc_inv2 in H4; auto.
        apply Hreg_pc_inv2 in H4; auto.
      inversion H3; subst; simpl in *;
    (* (L_reg <| M_cnt)2 step *)
      rewrite H6 in Hreg_pc_inv1; simpl in *;
      rewrite H6 in Hreg_pc_inv2; simpl in *;
      rewrite H6 in Hcnt_pc_inv1; simpl in *;
      rewrite H6 in Hcnt_pc_inv2; simpl in *.
      (* apply Hreg_pc_inv1 in H4; auto. *)
    (* (L_reg <| M_cnt)1 step *)
      inversion H5; subst; simpl in *.
      (* M_cnt 1 step *)
        inversion H7; subst; simpl in *;
        eapply Hreg_pc_inv2 in H4; eauto.
      (* L_reg 1 step *)
        inversion H7; subst; simpl in *.
        inversion H8; subst; simpl in *.
        apply binds_push_inv in H4; auto.
        intuition.
          subst.
          apply Hreg_pc_inv2 in Hbinds; auto.
          apply Hreg_pc_inv2 in H10; auto.
      (* M_cnt 1 query *)
        apply binds_push_inv in H4; auto.
        intuition.
          subst.
          apply Hreg_pc_inv2 in Hbinds; auto.
          apply Hreg_pc_inv2 in H10; auto.
      (* L_reg 1 reply *)
        inversion H7; subst; simpl in *.
        inversion H10; subst; simpl in *;
        apply Hreg_pc_inv2 in H4; auto.
        inversion H7; subst; simpl in *.
        inversion H8; subst; simpl in *;
          apply binds_remove_inv in H4; auto;
          apply Hreg_pc_inv2 in H4; auto.
        apply Hreg_pc_inv2 in H4; auto. *)

      unfold pc_cnt_pc.
      simpl. intros. split.
        intros.
        inversion H3; subst; simpl in *;
        rewrite H6 in Hpc_cnt_pc; simpl in *;
          inversion H5; subst; simpl in *;
            inversion H7; subst; simpl in *;
            inversion H8; subst; simpl in *;
            try (inversion H9; subst; simpl in *);
            apply Hpc_cnt_pc in H4; auto;
            intuition;
            try (apply substitute_preserves_notin; auto);
            try (apply substitute_preserves_in; auto).
        intros.
        inversion H3; subst; simpl in *;
        rewrite H6 in Hpc_cnt_pc; simpl in *;
          inversion H5; subst; simpl in *;
            inversion H7; subst; simpl in *;
            inversion H8; subst; simpl in *;
            try (inversion H9; subst; simpl in *);
            apply Hpc_cnt_pc in H4; auto;
            intuition;
            try (apply substitute_preserves_notin; auto);
            try (apply substitute_preserves_in; auto).
    (* L_ary step *)
    ---
    exists (@mkRawComposedState 
      (tensor_li li_array (tensor_li li_counter li_counter)) li_queue
        (tensor (array N)
            (RawTensor.tensor
               (linked_lts
                  (raw_compose Register
                     register_counter_impl))
               (linked_lts
                  (raw_compose Register
                     register_counter_impl))))
      (array_queue_impl N)
      (@Tensor.mkTensorState li_array (tensor_li li_counter li_counter)
        (array N) ((RawTensor.tensor
               (linked_lts
                  (raw_compose Register register_counter_impl))
               (linked_lts
                  (raw_compose Register register_counter_impl))))
        (mkSyncState (array N)
          st1'0
          (PidPos (L1State (RawL1State s2)))
        )
        (mkSyncState ((RawTensor.tensor
               (linked_lts
                  (raw_compose Register register_counter_impl))
               (linked_lts
                  (raw_compose Register register_counter_impl))))
          st3
          (PidPos (L2State (RawL1State s2)))
        )
      )
      (RawL2State s2)
    ).
    simpl. intuition.
     destruct s2; simpl in *.
     destruct RawL1State; simpl in *.
     destruct L1State; simpl in *.
     destruct L2State; simpl in *.
     subst.
     eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply linked_step_int_L1; eauto.
    simpl.
    eapply raw_composed_step_L1_internal; eauto.
    simpl.
    eapply tensor_step_L1_internal with (pid:=pid); eauto.
    simpl in *.
    inversion H3; subst; simpl in *;
      apply Hary_pc_inv in Hbinds; auto.
    simpl in *.
    apply Hmutual; auto.
    inversion H3; subst; simpl in *;
      apply Hary_pc_inv in Hbinds; auto.
    simpl.
    eapply sync_step_L_internal; eauto.
    apply Hwf; auto.
    inversion H3; subst; simpl in *;
      apply Hary_pc_inv in Hbinds; auto.
    unfold ary_pc_inv.
    simpl. intuition.
      inversion H3; subst; simpl in *;
      rewrite H5 in Hary_pc_inv; simpl in *;
      apply binds_remove_inv in H4; auto;
      apply Hary_pc_inv in H4; auto.
      inversion H3; subst; simpl in *;
      rewrite H5 in Hary_pc_inv; simpl in *.
      apply binds_push_inv in H4; auto.
      intuition.
        subst.
        apply Hary_pc_inv in Hbinds; auto.
        apply Hary_pc_inv in H7; auto.
      apply binds_push_inv in H4; auto.
      intuition.
        subst.
        apply Hary_pc_inv in Hbinds; auto.
        apply Hary_pc_inv in H7; auto.
    (* M_queue query *)
    --
    inversion H0; subst; simpl in *.
    inversion H4; subst; simpl in *.
      (* regcnt_regcnt initial *)
    ---
    exists (@mkRawComposedState 
      (tensor_li li_array (tensor_li li_counter li_counter)) li_queue
        (tensor (array N)
            (RawTensor.tensor
               (linked_lts
                  (raw_compose Register
                     register_counter_impl))
               (linked_lts
                  (raw_compose Register
                     register_counter_impl))))
      (array_queue_impl N)
      (@Tensor.mkTensorState li_array (tensor_li li_counter li_counter)
        (array N) ((RawTensor.tensor
               (linked_lts
                  (raw_compose Register register_counter_impl))
               (linked_lts
                  (raw_compose Register register_counter_impl))))
        (mkSyncState (array N)
          st3
          (PidPos (L1State (RawL1State s2)))
        )
        (mkSyncState ((RawTensor.tensor
               (linked_lts
                  (raw_compose Register register_counter_impl))
               (linked_lts
                  (raw_compose Register register_counter_impl))))
          st2'0
          ((pid, Run)::(PidPos (L2State (RawL1State s2))))
        )
      )
      st2'
    ).
    simpl. intuition.
     destruct s2; simpl in *.
     destruct RawL1State; simpl in *.
     destruct L1State; simpl in *.
     destruct L2State; simpl in *.
     subst.
     eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply linked_step_L2_push; eauto.
    simpl.
    eapply raw_composed_step_L2_push; eauto.
    simpl.
    eapply tensor_initial_state_L2; eauto.
    simpl in *.
    inversion H2; subst; simpl in *;
    apply Hpc_inv in Hbinds; auto;
    apply Hbinds; auto;
    unfold cnt_pc;
    unfold ary_pc; intuition; discriminate.
    simpl.
    eapply sync_initial_state_L; eauto.
    apply Hwf; auto.
    inversion H2; subst; simpl in *;
    apply Hpc_inv in Hbinds; auto;
    apply Hbinds; auto;
    unfold cnt_pc;
    unfold ary_pc; intuition; discriminate.
    unfold pc_inv.
    simpl. intros. split.
      intros.
      inversion H2; subst; simpl in *;
      rewrite H7 in Hpc_inv; simpl in *;

      destruct (eq_nat_dec pid0 pid);
        subst;
      try ((apply substitute_neq_preserves_binds' in H5; auto;
        eapply Hpc_inv in H5; eauto);
        intuition;
        try (apply binds_push_neq; auto);
        apply notin_union;
        intuition;
        apply notin_neq; auto);
        pose proof Hbinds as Hbinds';
        eapply substitute_eq_binds_v' in Hbinds;
        unfold binds in Hbinds;
        rewrite H5 in Hbinds; auto;
        inversion Hbinds; subst; simpl in *;
        eapply Hpc_inv in Hbinds'; eauto;
        destruct Hbinds' as [Hb1 Hb2];
        destruct Hb2 as [Hb2 Hb3];
        unfold ary_pc, cnt_pc; intuition; try discriminate;
        try (apply binds_push_eq; auto);
        apply Hb3; auto;
        unfold ary_pc, cnt_pc; intuition; try discriminate.

      intros.
      inversion H2; subst; simpl in *;
      rewrite H7 in Hpc_inv; simpl in *;
      apply substitute_preserves_notin' in H5; auto;
      destruct (eq_nat_dec pid0 pid);
        subst;
        apply binds_in in Hbinds;
        pose proof H5 as H5';
        unfold "#" in H5; intuition;
        try (apply Hpc_inv in H5'; auto;
        intuition;
        apply notin_union; intuition;
        apply notin_neq; auto).
    unfold cnt_pc_inv.
    simpl. intros.
    intros. inversion H3; subst; simpl in *;
      rewrite H7 in Hcnt_pc_inv2; simpl in *;
      rewrite H7 in Hcnt_pc_inv1; simpl in *.
      destruct (eq_nat_dec pid0 pid);
      subst; try (apply binds_push_eq; auto);
      apply binds_push_neq; auto;
      eapply Hcnt_pc_inv1 in H5; eauto.
    
      destruct (eq_nat_dec pid0 pid);
      subst; try (apply binds_push_eq; auto);
      apply binds_push_neq; auto.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *;
      apply binds_push_inv in H5; auto;
      intuition;
      eapply Hcnt_pc_inv1 in H10; eauto.
    unfold cnt_pc_inv.
    simpl. intros.
    intros. inversion H3; subst; simpl in *;
      rewrite H7 in Hcnt_pc_inv2; simpl in *;
      rewrite H7 in Hcnt_pc_inv1; simpl in *.
      destruct (eq_nat_dec pid0 pid);
      subst; try (apply binds_push_eq; auto);
      apply binds_push_neq; auto.
      inversion H6; subst; simpl in *.
      inversion H8; subst; simpl in *;
      apply binds_push_inv in H5; auto;
      intuition;
      eapply Hcnt_pc_inv2 in H10; eauto.
      destruct (eq_nat_dec pid0 pid);
      subst; try (apply binds_push_eq; auto);
      apply binds_push_neq; auto;
      eapply Hcnt_pc_inv2 in H5; eauto.
    unfold array_reg_cnt_mutual.
    simpl. intuition.
    apply notin_union.
    destruct (eq_nat_dec pid0 pid).
      subst.
      inversion H2; subst; simpl in *;
        rewrite H7 in Hpc_inv; simpl in *;
        apply Hpc_inv in Hbinds; auto;
        apply binds_in in H5;
        destruct Hbinds;
        destruct H8;
        apply H9 in H5; auto;
        try (destruct H5); clear H10;
        unfold cnt_pc, ary_pc; intuition; discriminate.
      apply Hmutual in H5; auto.
      intuition.
      apply notin_neq; auto.
    apply binds_push_inv in H5; auto.
    intuition.
      subst.
      inversion H2; subst; simpl in *;
      rewrite H6 in Hpc_inv; simpl in *;
      apply Hpc_inv in Hbinds; auto;
      apply Hbinds; auto; clear Hbinds;
      unfold cnt_pc, ary_pc; intuition; discriminate.
      apply Hmutual in H7; auto.
    unfold pos_wf. intuition.
    apply Hwf; auto.
    econstructor; eauto.
    apply Hwf; auto.
    inversion H2; subst; simpl in *;
    rewrite H6 in Hpc_inv; auto;
    apply Hpc_inv in Hbinds; auto;
    apply Hbinds; auto; clear Hbinds;
    unfold cnt_pc, ary_pc; intuition; discriminate.

    unfold pc_cnt_pc.
      simpl. intros. split.
        intros.
        inversion H3; subst; simpl in *.
        rewrite H7 in Hpc_cnt_pc; simpl in *;
          inversion H6; subst; simpl in *.
            inversion H8; subst; simpl in *.
            inversion H2; subst; simpl in *;
            rewrite H9 in Hpc_cnt_pc; simpl in *.
            split; intros.
              destruct (eq_nat_dec pid0 pid).
                subst.
                eapply substitute_eq_binds_v' in Hbinds; eauto.
                unfold binds in Hbinds.
                rewrite H5 in Hbinds; auto.
                inversion Hbinds; subst.
                unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                apply substitute_neq_preserves_binds' in H5; auto.
                apply Hpc_cnt_pc in H5; auto.
                intuition.
                apply notin_union; auto; intuition.
                apply notin_neq; auto.
              split; intros.
                destruct (eq_nat_dec pid0 pid).
                  subst.
                  intuition.
                  apply in_union. simpl. intuition.
                  apply Hpc_cnt_pc in Hbinds; auto.
                  apply Hbinds; auto; clear Hbinds;
                  unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                  apply substitute_neq_preserves_binds' in H5; auto.
                  apply Hpc_cnt_pc in H5; auto.
                  intuition.
                  apply in_union; auto; intuition.
                destruct (eq_nat_dec pid0 pid).
                  subst.
                  eapply substitute_eq_binds_v' in Hbinds; eauto.
                  unfold binds in Hbinds.
                  rewrite H5 in Hbinds.
                  inversion Hbinds; subst.
                  unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                  apply substitute_neq_preserves_binds' in H5; auto.
                  eapply Hpc_cnt_pc in H10; eauto; intuition.
                  apply notin_union; auto; intuition.
                  apply notin_neq; auto.
            inversion H2; subst; simpl in *;
            rewrite H9 in Hpc_cnt_pc; simpl in *.
            split; intros.
              destruct (eq_nat_dec pid0 pid).
                subst.
                eapply substitute_eq_binds_v' in Hbinds; eauto.
                unfold binds in Hbinds.
                rewrite H5 in Hbinds; auto.
                inversion Hbinds; subst.
                unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                apply substitute_neq_preserves_binds' in H5; auto.
                apply Hpc_cnt_pc in H5; auto.
                intuition.
                apply notin_union; auto; intuition.
                apply notin_neq; auto.
              split; intros.
                destruct (eq_nat_dec pid0 pid).
                  subst.
                  intuition.
                  apply in_union. simpl. intuition.
                  apply Hpc_cnt_pc in Hbinds; auto.
                  apply Hbinds; auto; clear Hbinds;
                  unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                  apply substitute_neq_preserves_binds' in H5; auto.
                  apply Hpc_cnt_pc in H5; auto.
                  intuition.
                  apply in_union; auto; intuition.
                destruct (eq_nat_dec pid0 pid).
                  subst.
                  eapply substitute_eq_binds_v' in Hbinds; eauto.
                  unfold binds in Hbinds.
                  rewrite H5 in Hbinds.
                  inversion Hbinds; subst.
                  unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                  apply substitute_neq_preserves_binds' in H5; auto.
                  eapply Hpc_cnt_pc in H10; eauto; intuition.
                  apply notin_union; auto; intuition.
                  apply notin_neq; auto.
            split; intros.
              destruct (eq_nat_dec pid0 pid).
                subst.
                eapply substitute_eq_binds_v' in Hbinds; eauto.
                unfold binds in Hbinds.
                rewrite H5 in Hbinds; auto.
                inversion Hbinds; subst.
                unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                apply substitute_neq_preserves_binds' in H5; auto.
                apply Hpc_cnt_pc in H5; auto.
                intuition.
                apply notin_union; auto; intuition.
                apply notin_neq; auto.
              split; intros.
                destruct (eq_nat_dec pid0 pid).
                  subst.
                  intuition.
                  apply in_union. simpl. intuition.
                  apply Hpc_cnt_pc in Hbinds; auto.
                  apply Hbinds; auto; clear Hbinds;
                  unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                  apply substitute_neq_preserves_binds' in H5; auto.
                  apply Hpc_cnt_pc in H5; auto.
                  intuition.
                  apply in_union; auto; intuition.
                destruct (eq_nat_dec pid0 pid).
                  subst.
                  eapply substitute_eq_binds_v' in Hbinds; eauto.
                  unfold binds in Hbinds.
                  rewrite H5 in Hbinds.
                  inversion Hbinds; subst.
                  unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                  apply substitute_neq_preserves_binds' in H5; auto.
                  eapply Hpc_cnt_pc in H10; eauto; intuition.
                  apply notin_union; auto; intuition.
                  apply notin_neq; auto.
            split; intros.
              destruct (eq_nat_dec pid0 pid).
                subst.
                eapply substitute_eq_binds_v' in Hbinds; eauto.
                unfold binds in Hbinds.
                rewrite H5 in Hbinds; auto.
                inversion Hbinds; subst.
                unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                apply substitute_neq_preserves_binds' in H5; auto.
                apply Hpc_cnt_pc in H5; auto.
                intuition.
                apply notin_union; auto; intuition.
                apply notin_neq; auto.
              split; intros.
                destruct (eq_nat_dec pid0 pid).
                  subst.
                  intuition.
                  apply in_union. simpl. intuition.
                  apply Hpc_cnt_pc in Hbinds; auto.
                  apply Hbinds; auto; clear Hbinds;
                  unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                  apply substitute_neq_preserves_binds' in H5; auto.
                  apply Hpc_cnt_pc in H5; auto.
                  intuition.
                  apply in_union; auto; intuition.
                destruct (eq_nat_dec pid0 pid).
                  subst.
                  eapply substitute_eq_binds_v' in Hbinds; eauto.
                  unfold binds in Hbinds.
                  rewrite H5 in Hbinds.
                  inversion Hbinds; subst.
                  unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                  apply substitute_neq_preserves_binds' in H5; auto.
                  eapply Hpc_cnt_pc in H10; eauto; intuition.
                  apply notin_union; auto; intuition.
                  apply notin_neq; auto.
        rewrite H7 in Hpc_cnt_pc; simpl in *;
          inversion H6; subst; simpl in *.
            inversion H8; subst; simpl in *.
            inversion H2; subst; simpl in *;
            rewrite H9 in Hpc_cnt_pc; simpl in *.
            split; intros.

                destruct (eq_nat_dec pid0 pid).
                  subst.
                  intuition.
                  apply in_union. simpl. intuition.
                  apply Hpc_cnt_pc in Hbinds; auto.
                  apply Hbinds; auto; clear Hbinds;
                  unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                  apply substitute_neq_preserves_binds' in H5; auto.
                  apply Hpc_cnt_pc in H5; auto.
                  intuition.
                  apply in_union; auto; intuition.

              split; intros.
                destruct (eq_nat_dec pid0 pid).
                  subst.
                  eapply substitute_eq_binds_v' in Hbinds; eauto.
                  unfold binds in Hbinds.
                  rewrite H5 in Hbinds; auto.
                  inversion Hbinds; subst.
                  unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                  apply substitute_neq_preserves_binds' in H5; auto.
                  apply Hpc_cnt_pc in H5; auto.
                  intuition.
                  apply notin_union; auto; intuition.
                  apply notin_neq; auto.
                destruct (eq_nat_dec pid0 pid).
                  subst.
                  eapply substitute_eq_binds_v' in Hbinds; eauto.
                  unfold binds in Hbinds.
                  rewrite H5 in Hbinds.
                  inversion Hbinds; subst.
                  unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                  apply substitute_neq_preserves_binds' in H5; auto.
                  eapply Hpc_cnt_pc in H10; eauto; intuition.
                  apply notin_union; auto; intuition.
                  apply notin_neq; auto.
            inversion H2; subst; simpl in *;
            rewrite H9 in Hpc_cnt_pc; simpl in *.
            split; intros.
                destruct (eq_nat_dec pid0 pid).
                  subst.
                  intuition.
                  apply in_union. simpl. intuition.
                  apply Hpc_cnt_pc in Hbinds; auto.
                  apply Hbinds; auto; clear Hbinds;
                  unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                  apply substitute_neq_preserves_binds' in H5; auto.
                  apply Hpc_cnt_pc in H5; auto.
                  intuition.
                  apply in_union; auto; intuition.
              split; intros.
                destruct (eq_nat_dec pid0 pid).
                  subst.
                  eapply substitute_eq_binds_v' in Hbinds; eauto.
                  unfold binds in Hbinds.
                  rewrite H5 in Hbinds; auto.
                  inversion Hbinds; subst.
                  unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                  apply substitute_neq_preserves_binds' in H5; auto.
                  apply Hpc_cnt_pc in H5; auto.
                  intuition.
                  apply notin_union; auto; intuition.
                  apply notin_neq; auto.
                destruct (eq_nat_dec pid0 pid).
                  subst.
                  eapply substitute_eq_binds_v' in Hbinds; eauto.
                  unfold binds in Hbinds.
                  rewrite H5 in Hbinds.
                  inversion Hbinds; subst.
                  unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                  apply substitute_neq_preserves_binds' in H5; auto.
                  eapply Hpc_cnt_pc in H10; eauto; intuition.
                  apply notin_union; auto; intuition.
                  apply notin_neq; auto.
            split; intros.
                destruct (eq_nat_dec pid0 pid).
                  subst.
                  intuition.
                  apply in_union. simpl. intuition.
                  apply Hpc_cnt_pc in Hbinds; auto.
                  apply Hbinds; auto; clear Hbinds;
                  unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                  apply substitute_neq_preserves_binds' in H5; auto.
                  apply Hpc_cnt_pc in H5; auto.
                  intuition.
                  apply in_union; auto; intuition.
              split; intros.
                destruct (eq_nat_dec pid0 pid).
                  subst.
                  eapply substitute_eq_binds_v' in Hbinds; eauto.
                  unfold binds in Hbinds.
                  rewrite H5 in Hbinds; auto.
                  inversion Hbinds; subst.
                  unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                  apply substitute_neq_preserves_binds' in H5; auto.
                  apply Hpc_cnt_pc in H5; auto.
                  intuition.
                  apply notin_union; auto; intuition.
                  apply notin_neq; auto.
                destruct (eq_nat_dec pid0 pid).
                  subst.
                  eapply substitute_eq_binds_v' in Hbinds; eauto.
                  unfold binds in Hbinds.
                  rewrite H5 in Hbinds.
                  inversion Hbinds; subst.
                  unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                  apply substitute_neq_preserves_binds' in H5; auto.
                  eapply Hpc_cnt_pc in H10; eauto; intuition.
                  apply notin_union; auto; intuition.
                  apply notin_neq; auto.
            split; intros.
                destruct (eq_nat_dec pid0 pid).
                  subst.
                  intuition.
                  apply in_union. simpl. intuition.
                  apply Hpc_cnt_pc in Hbinds; auto.
                  apply Hbinds; auto; clear Hbinds;
                  unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                  apply substitute_neq_preserves_binds' in H5; auto.
                  apply Hpc_cnt_pc in H5; auto.
                  intuition.
                  apply in_union; auto; intuition.
              split; intros.
                destruct (eq_nat_dec pid0 pid).
                  subst.
                  eapply substitute_eq_binds_v' in Hbinds; eauto.
                  unfold binds in Hbinds.
                  rewrite H5 in Hbinds; auto.
                  inversion Hbinds; subst.
                  unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                  apply substitute_neq_preserves_binds' in H5; auto.
                  apply Hpc_cnt_pc in H5; auto.
                  intuition.
                  apply notin_union; auto; intuition.
                  apply notin_neq; auto.
                destruct (eq_nat_dec pid0 pid).
                  subst.
                  eapply substitute_eq_binds_v' in Hbinds; eauto.
                  unfold binds in Hbinds.
                  rewrite H5 in Hbinds.
                  inversion Hbinds; subst.
                  unfold cnt1_pc, cnt2_pc in *; intuition; discriminate.
                  apply substitute_neq_preserves_binds' in H5; auto.
                  eapply Hpc_cnt_pc in H10; eauto; intuition.
                  apply notin_union; auto; intuition.
                  apply notin_neq; auto.
            intros.
            inversion H2; subst; simpl in *;
            rewrite H7 in Hpc_cnt_pc; simpl in *;
            inversion H3; subst; simpl in *;
            rewrite H9 in Hpc_cnt_pc; simpl in *;
            inversion H8; subst; simpl in *;
            inversion H6; subst; simpl in *;
              destruct (eq_nat_dec pid0 pid);
                subst; apply binds_in in Hbinds;
                pose proof H5 as H5';
                apply substitute_preserves_notin' in H5'; auto;
                unfold "#" in H5'; intuition;
                apply substitute_preserves_notin' in H5; auto;
                apply Hpc_cnt_pc in H5; auto;
                intuition;
                apply notin_union; intuition;
                apply notin_neq; auto.
      (* ary initial *)
    ---
    exists (@mkRawComposedState 
      (tensor_li li_array (tensor_li li_counter li_counter)) li_queue
        (tensor (array N)
            (RawTensor.tensor
               (linked_lts
                  (raw_compose Register
                     register_counter_impl))
               (linked_lts
                  (raw_compose Register
                     register_counter_impl))))
      (array_queue_impl N)
      (@Tensor.mkTensorState li_array (tensor_li li_counter li_counter)
        (array N) ((RawTensor.tensor
               (linked_lts
                  (raw_compose Register register_counter_impl))
               (linked_lts
                  (raw_compose Register register_counter_impl))))
        (mkSyncState (array N)
          st1'0
          ((pid, Run)::(PidPos (L1State (RawL1State s2))))
        )
        (mkSyncState ((RawTensor.tensor
               (linked_lts
                  (raw_compose Register register_counter_impl))
               (linked_lts
                  (raw_compose Register register_counter_impl))))
          st3
          (PidPos (L2State (RawL1State s2)))
        )
      )
      st2'
    ).
    simpl. intuition.
     destruct s2; simpl in *.
     destruct RawL1State; simpl in *.
     destruct L1State; simpl in *.
     destruct L2State; simpl in *.
     subst.
     eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply linked_step_L2_push; eauto.
    simpl.
    eapply raw_composed_step_L2_push; eauto.
    simpl.
    eapply tensor_initial_state_L1; eauto.
    simpl in *.
    simpl in *.
    inversion H2; subst; simpl in *;
    apply Hpc_inv in Hbinds; auto;
    apply Hbinds; auto;
    unfold cnt_pc;
    unfold ary_pc; intuition; discriminate.
    simpl.
    eapply sync_initial_state_L; eauto.
    apply Hwf; auto.
    inversion H2; subst; simpl in *;
    apply Hpc_inv in Hbinds; auto;
    apply Hbinds; auto;
    unfold cnt_pc;
    unfold ary_pc; intuition; discriminate.
    unfold pc_inv.
    simpl. intros. split.
      intros.
      inversion H2; subst; simpl in *;
      rewrite H7 in Hpc_inv; simpl in *;

      destruct (eq_nat_dec pid0 pid);
        subst;
      try ((apply substitute_neq_preserves_binds' in H5; auto;
        eapply Hpc_inv in H5; eauto);
        intuition;
        try (apply binds_push_neq; auto);
        apply notin_union;
        intuition;
        apply notin_neq; auto);
        pose proof Hbinds as Hbinds';
        eapply substitute_eq_binds_v' in Hbinds;
        unfold binds in Hbinds;
        rewrite H5 in Hbinds; auto;
        inversion Hbinds; subst; simpl in *;
        eapply Hpc_inv in Hbinds'; eauto;
        destruct Hbinds' as [Hb1 Hb2];
        destruct Hb2 as [Hb2 Hb3];
        unfold ary_pc, cnt_pc; intuition; try discriminate;
        try (apply binds_push_eq; auto);
        apply Hb3; auto;
        unfold ary_pc, cnt_pc; intuition; try discriminate.

      intros.
      inversion H2; subst; simpl in *;
      rewrite H7 in Hpc_inv; simpl in *;
      apply substitute_preserves_notin' in H5; auto;
      destruct (eq_nat_dec pid0 pid);
        subst;
        apply binds_in in Hbinds;
        pose proof H5 as H5';
        unfold "#" in H5; intuition;
        try (apply Hpc_inv in H5'; auto;
        intuition;
        apply notin_union; intuition;
        apply notin_neq; auto).
    unfold array_reg_cnt_mutual.
    simpl. intuition.
    apply binds_push_inv in H5; auto.
    intuition.
      subst.
      inversion H2; subst; simpl in *;
      rewrite H6 in Hpc_inv; simpl in *;
      apply Hpc_inv in Hbinds; auto;
      apply Hbinds; auto; clear Hbinds;
      unfold cnt_pc, ary_pc; intuition; discriminate.
      apply Hmutual in H7; auto.
    apply notin_union.
    destruct (eq_nat_dec pid0 pid).
      subst.
      inversion H2; subst; simpl in *;
        rewrite H7 in Hpc_inv; simpl in *;
        apply Hpc_inv in Hbinds; auto;
        apply binds_in in H5;
        destruct Hbinds;
        destruct H8;
        apply H9 in H5; auto;
        try (destruct H5); clear H10;
        unfold cnt_pc, ary_pc; intuition; discriminate.
      apply Hmutual in H5; auto.
      intuition.
      apply notin_neq; auto.
    unfold pos_wf. intuition.
    econstructor; eauto.
    apply Hwf; auto.
    inversion H2; subst; simpl in *;
    rewrite H6 in Hpc_inv; auto;
    apply Hpc_inv in Hbinds; auto;
    apply Hbinds; auto; clear Hbinds;
    unfold cnt_pc, ary_pc; intuition; discriminate.
    apply Hwf; auto.
    unfold ary_pc_inv.
    simpl. intuition.
      inversion H3; subst; simpl in *;
      rewrite H6 in Hary_pc_inv; simpl in *;
      apply binds_push_inv in H5; auto;
      intuition;
        subst; try (apply binds_push_eq; auto);
        apply binds_push_neq; auto;
        apply Hary_pc_inv in H8; auto.
      inversion H3; subst; simpl in *;
      rewrite H6 in Hary_pc_inv; simpl in *;
      destruct (eq_nat_dec pid0 pid);
        subst; try (apply binds_push_eq; auto);
        apply binds_push_neq; auto;
        apply Hary_pc_inv in H5; auto.
    unfold pc_cnt_pc.
      simpl. intros. split.
        intros.
        inversion H2; subst; simpl in *;
        rewrite H7 in Hpc_cnt_pc; simpl in *;
        destruct (eq_nat_dec pid0 pid);
          subst;
          try (apply substitute_neq_preserves_binds' in H5; auto;
            apply Hpc_cnt_pc in H5; auto);
        split; intros; (try split; intros);
            try (eapply substitute_eq_binds_v' in Hbinds; eauto;
            unfold binds in Hbinds;
            rewrite H5 in Hbinds;
            inversion Hbinds; subst;
            unfold cnt1_pc, cnt2_pc in *; intuition; discriminate);
              apply Hpc_cnt_pc in Hbinds; auto;
              apply Hbinds; auto; clear Hbinds;
              unfold cnt1_pc, cnt2_pc; intuition; discriminate.
        intros.
        inversion H2; subst; simpl in *;
        rewrite H7 in Hpc_cnt_pc; simpl in *;
        apply substitute_preserves_notin' in H5; auto;
        apply Hpc_cnt_pc in H5; auto.
    (* ary_cnt_cnt reply *)
    --
    inversion H0; subst; simpl in *.
    inversion H2; subst; simpl in *.
      (* regcnt_regcnt final *)
    ---
    exists (@mkRawComposedState 
      (tensor_li li_array (tensor_li li_counter li_counter)) li_queue
        (tensor (array N)
            (RawTensor.tensor
               (linked_lts
                  (raw_compose Register
                     register_counter_impl))
               (linked_lts
                  (raw_compose Register
                     register_counter_impl))))
      (array_queue_impl N)
      (@Tensor.mkTensorState li_array (tensor_li li_counter li_counter)
        (array N) ((RawTensor.tensor
               (linked_lts
                  (raw_compose Register register_counter_impl))
               (linked_lts
                  (raw_compose Register register_counter_impl))))
        (mkSyncState (array N)
          st0
          (PidPos (L1State (RawL1State s2)))
        )
        (mkSyncState ((RawTensor.tensor
               (linked_lts
                  (raw_compose Register register_counter_impl))
               (linked_lts
                  (raw_compose Register register_counter_impl))))
          st2'0
          (remove (PidPos (L2State (RawL1State s2))) pid)
        )
      )
      st2'
    ).
    simpl. intuition.
     destruct s2; simpl in *.
     destruct RawL1State; simpl in *.
     destruct L1State; simpl in *.
     destruct L2State; simpl in *.
     subst.
     eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply linked_step_L1_pop; eauto.
    simpl.
    eapply raw_composed_step_L1_pop; eauto.
    simpl.
    eapply tensor_final_state_L2; eauto.
    simpl in *.
    inversion H3; subst; simpl in *;
    eapply Hpc_inv; eauto; intuition;
    unfold cnt_pc in *;
    unfold ary_pc in *; intuition; discriminate.
    simpl.
    apply Hmutual; auto.
    inversion H3; subst; simpl in *;
    eapply Hpc_inv; eauto; intuition;
    unfold cnt_pc in *;
    unfold ary_pc in *; intuition; discriminate.
    simpl.
    eapply sync_final_state_L; eauto.
    apply Hwf; auto.
    inversion H3; subst; simpl in *;
    eapply Hpc_inv; eauto; intuition;
    unfold cnt_pc in *;
    unfold ary_pc in *; intuition; discriminate.
    unfold pc_inv.
    simpl. intros. split.
      intros.
      inversion H3; subst; simpl in *;
      rewrite H7 in Hpc_inv; simpl in *;

      destruct (eq_nat_dec pid0 pid);
        subst;
        try (apply substitute_neq_preserves_binds' in H5; auto;
        split; intros;
          try (eapply Hpc_inv in H6; eauto; intuition);
          try (apply remove_neq_preserves_binds; auto);
          split; intros;
            eapply Hpc_inv in H6; eauto; intuition;
            apply remove_preserves_notin; auto;
            eapply Hpc_inv in H6; eauto; intuition;
            apply remove_preserves_notin; auto);
        pose proof Hbinds as Hbinds';
        eapply substitute_eq_binds_v' in Hbinds;
        unfold binds in Hbinds;
        rewrite H5 in Hbinds; auto;
        inversion Hbinds; subst; simpl in *;
        eapply Hpc_inv in Hbinds'; eauto;
        destruct Hbinds' as [Hb1 Hb2];
        destruct Hb2 as [Hb2 Hb3];
        unfold ary_pc, cnt_pc; intuition; try discriminate;
        try (apply Hb1; auto;
        unfold ary_pc, cnt_pc; intuition; try discriminate);
        try (apply Hb2; auto;
        unfold ary_pc, cnt_pc; intuition; try discriminate);
        apply ok_remove_notin; auto;
        apply Hwf; auto.
      intros.
      inversion H3; subst; simpl in *;
      rewrite H7 in Hpc_inv; simpl in *;
      apply substitute_preserves_notin' in H5; auto;
      apply Hpc_inv in H5; auto; intuition;
      apply remove_preserves_notin; auto.
      unfold cnt_pc_inv.
      simpl. intuition.
      inversion H4; subst; simpl in *;
      rewrite H7 in Hcnt_pc_inv1, Hcnt_pc_inv2, Hpc_cnt_pc; simpl in *.
      destruct (eq_nat_dec pid0 pid).
        subst;
        inversion H3; subst; simpl in *;
        rewrite H9 in Hpc_cnt_pc; simpl in *;
        apply Hpc_cnt_pc in Hbinds; auto;
        apply binds_in in H5;
        destruct Hbinds as [Hb1 Hb2];
        destruct Hb2 as [Hb2 _];
        apply Hb2 in H5; auto;
        try (destruct H5);
        unfold cnt2_pc, cnt1_pc; intuition; discriminate.
        apply remove_neq_preserves_binds; auto;
        apply Hcnt_pc_inv1 in H5; auto.
      inversion H6; subst; simpl in *;
      inversion H8; subst; simpl in *;
        destruct (eq_nat_dec pid0 pid);
          subst; try (apply binds_remove_eq_false in H5; intuition);
          apply remove_neq_preserves_binds; auto;
          apply remove_preserves_binds_notin in H5; auto;
          apply Hcnt_pc_inv1 in H5; auto.

      unfold cnt_pc_inv.
      simpl. intuition.
      inversion H4; subst; simpl in *;
      rewrite H7 in Hcnt_pc_inv1, Hcnt_pc_inv2, Hpc_cnt_pc; simpl in *.
      inversion H6; subst; simpl in *;
      inversion H8; subst; simpl in *;
        destruct (eq_nat_dec pid0 pid);
          subst; try (apply binds_remove_eq_false in H5; intuition);
          apply remove_neq_preserves_binds; auto;
          apply remove_preserves_binds_notin in H5; auto;
          apply Hcnt_pc_inv2 in H5; auto.
      destruct (eq_nat_dec pid0 pid).
        subst;
        inversion H3; subst; simpl in *;
        rewrite H9 in Hpc_cnt_pc; simpl in *;
        apply Hpc_cnt_pc in Hbinds; auto;
        apply binds_in in H5;
        destruct Hbinds as [Hb1 Hb2];
        destruct Hb2 as [Hb2 _];
        apply Hb1 in H5; auto;
        try (destruct H5);
        unfold cnt2_pc, cnt1_pc; intuition; discriminate.
        apply remove_neq_preserves_binds; auto;
        apply Hcnt_pc_inv2 in H5; auto.
    unfold array_reg_cnt_mutual.
    simpl. intuition.
    apply Hmutual in H5; auto;
    apply remove_preserves_notin; auto.
    apply binds_remove_inv in H5; auto.
    apply Hmutual in H5; auto;
    apply remove_preserves_notin; auto.
    apply Hwf; auto.
    unfold pos_wf. intuition.
    apply Hwf; auto.
    apply remove_preserves_ok; auto.
    apply Hwf; auto.
    unfold pc_cnt_pc.
    simpl. intros. split.
      intros.
      inversion H3; subst; simpl in *;
      rewrite H7 in Hpc_cnt_pc; simpl in *;
      destruct (eq_nat_dec pid0 pid);
        subst;
        try (apply substitute_neq_preserves_binds' in H5; auto;
        inversion H4; subst; simpl in *;
        rewrite H9 in Hpc_cnt_pc; simpl in *;
        inversion H8; subst; simpl in *;
        inversion H6; subst; simpl in *;
        apply Hpc_cnt_pc in H5; auto;
        split; intros; (try split; intros);
          try (apply H5 in H10; auto; intuition;
          try (apply remove_preserves_notin; auto);
          try (apply remove_neq_preserves_in'; auto)));
        pose proof Hbinds as Hbinds';
        eapply substitute_eq_binds_v' in Hbinds;
        unfold binds in Hbinds;
        rewrite H5 in Hbinds;
        inversion Hbinds; subst;
        split; intros;
        try (unfold cnt1_pc, cnt2_pc  in *; intuition; discriminate);
        split; intros;
        try (unfold cnt1_pc, cnt2_pc  in *; intuition; discriminate);
        inversion H4; subst; simpl in *;
        rewrite H11 in Hpc_cnt_pc; simpl in *;
        inversion H10; subst; simpl in *;
        inversion H9; subst; simpl in *;
        intuition;
        try (apply ok_remove_notin; auto);
        apply Hpc_cnt_pc in Hbinds'; eauto;
        destruct Hbinds' as [Hb1 [Hb2 Hb3]];
        try (apply Hb2; auto);
        try (apply Hb1; auto);
        unfold cnt1_pc, cnt2_pc; intuition; discriminate.
    intros.
    inversion H3; subst; simpl in *;
    rewrite H7 in Hpc_cnt_pc; simpl in *;
    inversion H4; subst; simpl in *;
    rewrite H9 in Hpc_cnt_pc; simpl in *;
    inversion H8; subst; simpl in *;
    inversion H6; subst; simpl in *;
    apply substitute_preserves_notin' in H5; auto;
    apply Hpc_cnt_pc in H5; auto; simpl in *;
    intuition;
    apply remove_preserves_notin; auto.
      (* ary final *)
    ---
    exists (@mkRawComposedState 
      (tensor_li li_array (tensor_li li_counter li_counter)) li_queue
        (tensor (array N)
            (RawTensor.tensor
               (linked_lts
                  (raw_compose Register
                     register_counter_impl))
               (linked_lts
                  (raw_compose Register
                     register_counter_impl))))
      (array_queue_impl N)
      (@Tensor.mkTensorState li_array (tensor_li li_counter li_counter)
        (array N) ((RawTensor.tensor
               (linked_lts
                  (raw_compose Register register_counter_impl))
               (linked_lts
                  (raw_compose Register register_counter_impl))))
        (mkSyncState (array N)
          st1'0
          (remove (PidPos (L1State (RawL1State s2))) pid)
        )
        (mkSyncState ((RawTensor.tensor
               (linked_lts
                  (raw_compose Register register_counter_impl))
               (linked_lts
                  (raw_compose Register register_counter_impl))))
          st3
          (PidPos (L2State (RawL1State s2)))
        )
      )
      st2'
    ).
    simpl. intuition.
     destruct s2; simpl in *.
     destruct RawL1State; simpl in *.
     destruct L1State; simpl in *.
     destruct L2State; simpl in *.
     subst.
     eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply linked_step_L1_pop; eauto.
    simpl.
    eapply raw_composed_step_L1_pop; eauto.
    simpl.
    eapply tensor_final_state_L1; eauto.
    simpl in *.
    inversion H3; subst; simpl in *;
    eapply Hpc_inv; eauto; intuition;
    unfold cnt_pc in *;
    unfold ary_pc in *; intuition; discriminate.
    simpl.
    apply Hmutual; auto.
    inversion H3; subst; simpl in *;
    eapply Hpc_inv; eauto; intuition;
    unfold cnt_pc in *;
    unfold ary_pc in *; intuition; discriminate.
    simpl.
    eapply sync_final_state_L; eauto.
    apply Hwf; auto.
    inversion H3; subst; simpl in *;
    eapply Hpc_inv; eauto; intuition;
    unfold cnt_pc in *;
    unfold ary_pc in *; intuition; discriminate.
    unfold pc_inv.
    simpl. intros. split.
      intros.
      inversion H3; subst; simpl in *;
      rewrite H7 in Hpc_inv; simpl in *;
      destruct (eq_nat_dec pid0 pid);
        subst;
        try (
                  apply substitute_neq_preserves_binds' in H5; auto;
        split; intros; try (split; intros);
          eapply Hpc_inv in H6; eauto; intuition;
          try (apply remove_preserves_notin; auto);
          try (apply remove_neq_preserves_binds; auto)
        );
        pose proof Hbinds as Hbinds';
        eapply substitute_eq_binds_v' in Hbinds;
        unfold binds in Hbinds;
        rewrite H5 in Hbinds; auto;
        inversion Hbinds; subst; simpl in *;
        eapply Hpc_inv in Hbinds'; eauto;
        destruct Hbinds' as [Hb1 Hb2];
        destruct Hb2 as [Hb2 Hb3];
        unfold ary_pc, cnt_pc; intuition; try discriminate;
        try (apply Hb1; auto;
        unfold ary_pc, cnt_pc; intuition; try discriminate);
        try (apply Hb2; auto;
        unfold ary_pc, cnt_pc; intuition; try discriminate);
        apply ok_remove_notin; auto;
        apply Hwf; auto.
      intros.
      inversion H3; subst; simpl in *;
      rewrite H7 in Hpc_inv; simpl in *;
      apply substitute_preserves_notin' in H5; auto;
      apply Hpc_inv in H5; auto; intuition;
      apply remove_preserves_notin; auto.
    unfold array_reg_cnt_mutual.
    simpl. intuition.
    apply binds_remove_inv in H5; auto.
    apply Hmutual in H5; auto;
    apply remove_preserves_notin; auto.
    apply Hwf; auto.
    apply Hmutual in H5; auto;
    apply remove_preserves_notin; auto.
    unfold pos_wf. intuition.
    apply remove_preserves_ok; auto.
    apply Hwf; auto.
    apply Hwf; auto.
    unfold ary_pc_inv.
      Require Import
      ArrayProp.
      apply link_reachable_single_reachable in H;
      apply raw_tensor_reachable_single_reachable in H;
      simpl in *.
    intuition.
    inversion H4; subst; simpl in *;
    rewrite H6 in Hary_pc_inv, H; simpl in *.
    destruct (eq_nat_dec pid0 pid);
      subst;
      apply array_exclusive_wf_invariant in H.
      simpl in *.
      apply binds_in in Hbinds.
      apply H in Hbinds.
      simpl in *.
      apply binds_in in H5.
      unfold "#" in Hbinds; intuition.
      apply remove_neq_preserves_binds; auto.
      apply Hary_pc_inv in H5; auto.
    destruct (eq_nat_dec pid0 pid);
      subst;
      apply array_exclusive_wf_invariant in H.
      simpl in *.
      apply binds_in in Hbinds.
      apply H in Hbinds.
      simpl in *.
      apply binds_in in H5.
      unfold "#" in Hbinds; intuition.
      apply remove_neq_preserves_binds; auto.
      apply Hary_pc_inv in H5; auto.
    inversion H4; subst; simpl in *;
    rewrite H6 in Hary_pc_inv, H; simpl in *.
    destruct (eq_nat_dec pid0 pid);
      subst.
      apply binds_remove_eq_false in H5; intuition.
      apply remove_neq_preserves_binds; auto.
      apply remove_preserves_binds_notin in H5; auto.
      apply Hary_pc_inv in H5; auto.
    destruct (eq_nat_dec pid0 pid);
      subst.
      apply binds_remove_eq_false in H5; intuition.
      apply remove_neq_preserves_binds; auto.
      apply remove_preserves_binds_notin in H5; auto.
      apply Hary_pc_inv in H5; auto.
    unfold pc_cnt_pc.
    simpl. intros. split.
      intros.
      inversion H3; subst; simpl in *;
      rewrite H7 in Hpc_cnt_pc; simpl in *;
      destruct (eq_nat_dec pid0 pid);
        subst;
        try (apply substitute_neq_preserves_binds' in H5; auto;
        apply Hpc_cnt_pc in H5; auto;
        split; intros; (try split; intros);
          try (apply H5 in H10; auto; intuition;
          try (apply remove_preserves_notin; auto);
          try (apply remove_neq_preserves_in'; auto)));
        pose proof Hbinds as Hbinds';
        eapply substitute_eq_binds_v' in Hbinds;
        unfold binds in Hbinds;
        rewrite H5 in Hbinds;
        inversion Hbinds; subst;
        split; intros;
        try (unfold cnt1_pc, cnt2_pc  in *; intuition; discriminate);
        split; intros;
        try (unfold cnt1_pc, cnt2_pc  in *; intuition; discriminate);
        apply Hpc_cnt_pc in Hbinds'; auto;
        apply Hbinds'; auto;
        unfold cnt1_pc, cnt2_pc; intuition; discriminate.
    intros.
    inversion H3; subst; simpl in *;
    rewrite H7 in Hpc_cnt_pc; simpl in *;
    apply substitute_preserves_notin' in H5; auto;
    apply Hpc_cnt_pc in H5; auto; simpl in *;
    intuition;
    apply remove_preserves_notin; auto.
Qed.

End test.