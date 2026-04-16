Require Import
  Arith
  LibVar
  List
  LTS
  Refinement
.

Require LibEnv.

Import ListNotations.

Section SYNC.
  
  Context {liA liB : language_interface}.
  Variable L: lts liA liB.

  Inductive Position : Set :=
  | Run
  | Wait
  .

  Record sync_state : Type := mkSyncState {
    LState : L.(state);
    PidPos : LibEnv.env Position;
  }.

  Definition sync_internal := L.(internal).

  Definition sync_new_state sst : Prop :=
    L.(new_state) sst.(LState) /\
    sst.(PidPos) = [].

  Import LibEnv.

  Inductive sync_initial_state : sync_state -> Pid -> query liB -> sync_state -> Prop :=
  | sync_initial_state_L : forall sst sst' st st' qb pid pos
      (Hok : ok pos) (Hnotin : pid # pos),
      initial_state L st pid qb st' ->
      sst = mkSyncState st pos ->
      sst' = mkSyncState st' ((pid, Run) :: pos) ->
      sync_initial_state sst pid qb sst'
  .

  Inductive sync_step : sync_state -> Pid -> sync_internal -> sync_state -> Prop :=
  | sync_step_L_internal : forall st st' act sst sst' pid pos
      (Hok : ok pos) (Hbinds : binds pid Run pos),
      step L st pid act st' ->
      sst = mkSyncState st pos ->
      sst' = mkSyncState st' pos ->
      sync_step sst pid act sst'
  .

  Inductive sync_at_external : sync_state -> Pid -> query liA -> sync_state -> Prop :=
  | sync_at_external_L : forall qa st sst st' sst' pid pos
      (Hok : ok pos) (Hbinds : binds pid Run pos),
      at_external L st pid qa st' ->
      sst = mkSyncState st pos ->
      sst' = mkSyncState st' ((pid, Wait) :: (remove pos pid)) ->
      sync_at_external sst pid qa sst'
  .

  Inductive sync_after_external : sync_state -> Pid -> reply liA -> sync_state -> Prop :=
  | sync_after_external_L : forall st ra st' sst sst' pid pos
      (Hok : ok pos) (Hbinds : binds pid Wait pos),
      after_external L st pid ra st' ->
      sst = mkSyncState st pos ->
      sst' = mkSyncState st' ((pid, Run) :: (remove pos pid)) ->
      sync_after_external sst pid ra sst'
  .

  Inductive sync_final_state : sync_state -> Pid -> reply liB -> sync_state -> Prop :=
  | sync_final_state_L : forall st rb st' sst sst' pid pos
      (Hok : ok pos) (Hbinds : binds pid Run pos),
      final_state L st pid rb st' ->
      sst = mkSyncState st pos ->
      sst' = mkSyncState st' (remove pos pid) ->
      sync_final_state sst pid rb sst'
  .

  Definition sync : lts liA liB :=
    mkLTS liA liB
      sync_state
      sync_internal
      sync_step
      sync_new_state
      sync_initial_state
      sync_at_external
      sync_after_external
      sync_final_state.

End SYNC.

Arguments PidPos {liA liB L}.
Arguments LState {liA liB L}.

Notation " 'sc' M " := (sync M) (at level 67).

Section SYNC_INV.

Context {liA liB : language_interface}.
Variable L : lts liA liB.

Import LibEnv.

Definition disjoint (pos : env Position) (pos' : env Position) :=
  forall pid v, 
  (binds pid v pos ->
  pid # pos') /\
  (binds pid v pos' ->
  pid # pos).

Lemma disjoint_push_l: forall pos pos' pid p,
  disjoint pos pos' ->
  pid # pos' ->
  disjoint ((pid, p) :: pos) pos'.
Proof.
  intros. unfold disjoint in *.
  intros. intuition.
  - unfold binds in H1.
    simpl in H1.
    destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst. assumption.
    -- apply H in H1. assumption.
  - unfold "#". simpl.
    apply notin_union.
    intuition.
    -- apply notin_neq. intro.
      subst.
      unfold "#" in H0.
      apply binds_in in H1.
      intuition.
    -- apply H in H1; intuition.
Qed.

Lemma disjoint_remove_l: forall pos pos' pid,
  disjoint pos pos' ->
  ok pos ->
  disjoint (remove pos pid) pos'.
Proof.
  intros.
  unfold disjoint in *.
  intros. intuition.
  - destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst.
      assert (pid # (remove pos pid)).
      apply ok_remove_notin; auto.
      apply binds_in in H1.
      unfold "#" in H2. intuition.
    -- apply Nat.eqb_neq in Heq.
      apply remove_preserves_binds_notin in H1; auto.
      apply H in H1. assumption.
  - apply H in H1.
    apply remove_preserves_notin; auto.
Qed.

Lemma disjoint_comm: forall pos pos',
  disjoint pos pos' ->
  disjoint pos' pos.
Proof.
  intros.
  unfold disjoint in *.
  intros. intuition;
  apply H in H0; intuition.
Qed.

Lemma disjoint_remove_r: forall pos pos' pid,
  disjoint pos pos' ->
  ok pos' ->
  disjoint pos (remove pos' pid).
Proof.
  intros.
  apply disjoint_comm.
  apply disjoint_remove_l; auto.
  apply disjoint_comm in H; intuition.
Qed.

Lemma disjoint_push_r: forall pos pos' pid p,
  disjoint pos pos' ->
  pid # pos ->
  disjoint pos ((pid, p) :: pos').
Proof.
  intros. unfold disjoint in *.
  intros. intuition.
  - unfold "#". simpl.
    apply notin_union.
    intuition.
    -- apply notin_neq. intro.
      subst.
      unfold "#" in H0.
      apply binds_in in H1.
      intuition.
    -- apply H in H1; intuition.
  - unfold binds in H1.
    simpl in H1.
    destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst. assumption.
    -- apply H in H1. assumption.
Qed.

Lemma valid_execution_fragment_nil_preserves_pos: forall s s',
  valid_execution_fragment (sync L) s s' [] ->
  s.(PidPos) = s'.(PidPos).
Proof.
  intros. remember [] as acts.
  induction H; try inversion Heqacts.
  - subst. reflexivity.
  - intuition.
    rewrite <-H2.
    inversion H; subst. simpl in *.
    reflexivity.
Qed.

Import LibEnv.

Fixpoint test_pos pos (acts : list (@event liA liB)) : env Position :=
  match acts with
  | nil => pos
  | (pid, act) :: acts' =>
    match act with
    | event_invB _ =>
      test_pos ((pid, Run) :: pos) acts'
    | event_resB _ =>
      test_pos (remove pos pid) acts'
    | event_invA _ =>
      test_pos ((pid, Wait) :: (remove pos pid)) acts'
    | event_resA _ =>
      test_pos ((pid, Run) :: (remove pos pid)) acts'
    end
  end.

Fixpoint compatible_pos pos (acts : list (@event liA liB)) :=
  match acts with
  | nil => True
  | (pid, act) :: acts' =>
    match act with
    | event_invB _ =>
        pid # pos /\ compatible_pos ((pid, Run) :: pos) acts'
    | event_resB _ =>
      binds pid Run pos /\ compatible_pos (remove pos pid) acts'
    | event_invA _ =>
        binds pid Run pos /\ compatible_pos ((pid, Wait) :: (remove pos pid)) acts'
    | event_resA _ =>
        binds pid Wait pos /\ compatible_pos ((pid, Run) :: (remove pos pid)) acts'
    end
  end.

Lemma sameset_compatible_pos : forall (acts : list (@event liA liB)) (pos : env Position) pos' ,
  compatible_pos pos acts ->
  sameset pos pos' ->
  compatible_pos pos' acts.
Proof.
  induction acts; simpl; intros.
  - auto.
  - destruct a. destruct _e; simpl in *.
    -- intuition.
      eapply notin_sameset; eauto.
      eapply IHacts; eauto.
      apply sameset_concat with (F:=[(n,Run)]); auto.
      econstructor; eauto.
      apply sameset_ok_inv in H0; intuition.
    -- intuition.
      rewrite <-H0. assumption.
      eapply IHacts; eauto.
      apply sameset_remove; auto.
    -- intuition.
      rewrite <-H0. assumption.
      eapply IHacts; eauto.
      apply sameset_concat with (F:=[(n,Wait)]); auto.
      apply sameset_remove; auto.
      econstructor; eauto.
      apply remove_preserves_ok; auto.
      apply sameset_ok_inv in H0; intuition.
      apply ok_remove_notin; auto.
      apply sameset_ok_inv in H0; intuition.
    -- intuition.
      rewrite <-H0. assumption.
      eapply IHacts; eauto.
      apply sameset_concat with (F:=[(n,Run)]); auto.
      apply sameset_remove; auto.
      econstructor; eauto.
      apply remove_preserves_ok; auto.
      apply sameset_ok_inv in H0; intuition.
      apply ok_remove_notin; auto.
      apply sameset_ok_inv in H0; intuition.
Qed.

Lemma valid_execution_fragment_compatible_pos: forall s s' acts,
  valid_execution_fragment (sync L) s s' acts ->
  compatible_pos s.(PidPos) acts.
Proof.
  induction 1; simpl; intros.
  - auto.
  - inversion H; subst. simpl in *.
    assumption.
  - inversion H; subst. simpl in *.
    intuition.
  - inversion H; subst. simpl in *.
    intuition.
  - inversion H; subst. simpl in *.
    intuition.
  - inversion H; subst. simpl in *.
    intuition.
Qed.

Lemma step_preserves_pos: forall s s' pid int,
  step (sync L) s pid int s' ->
  s.(PidPos) = s'.(PidPos).
Proof.
  intros. inversion H; subst.
  simpl in *. reflexivity.
Qed.

Lemma valid_execution_fragment_pos: forall s s' acts,
  valid_execution_fragment (sync L) s s' acts ->
  test_pos s.(PidPos) acts = s'.(PidPos).
Proof.
  induction 1; simpl; intros.
  - subst. reflexivity.
  - rewrite <-IHvalid_execution_fragment.
    inversion H; subst.
    reflexivity.
  - rewrite <-IHvalid_execution_fragment.
    inversion H; subst.
    reflexivity.
  - rewrite <-IHvalid_execution_fragment.
    inversion H; subst.
    reflexivity.
  - rewrite <-IHvalid_execution_fragment.
    inversion H; subst.
    reflexivity.
  - rewrite <-IHvalid_execution_fragment.
    inversion H; subst.
    reflexivity.
Qed.
  
End SYNC_INV.

Section test.

Context {liA liB : language_interface}.
Variable L : lts liA liB.

Lemma valid_execution_fragment_sync: forall sst sst' st st' pos pos' acts,
  valid_execution_fragment (sync L)
    sst sst' acts ->
  sst = (mkSyncState L st pos) ->
  sst' = (mkSyncState L st' pos') ->
  valid_execution_fragment L st st' acts.
Proof.
  intros.
  generalize dependent pos'.
  generalize dependent pos.
  generalize dependent st'.
  generalize dependent st.
  induction H; intros.
  - subst. inversion H1; subst.
    eapply Step_None; eauto.
  - subst.
    inversion H; subst. inversion H2; subst. clear H2.
    eapply valid_execution_fragment_join' with (a:=[]).
    2 : {
      eapply IHvalid_execution_fragment; auto.
    }
    eapply Step_Internal; eauto.
    eapply Step_None; eauto.
    reflexivity.
  - subst.
    inversion H; subst. inversion H2; subst. clear H2.
    eapply valid_execution_fragment_join' with (a:=[(pid, event_invA qa)]).
    2 : {
      eapply IHvalid_execution_fragment; auto.
    }
    eapply Step_At_External; eauto.
    eapply Step_None; eauto.
    reflexivity.
  - subst.
    inversion H; subst. inversion H2; subst. clear H2.
    eapply valid_execution_fragment_join' with (a:=[(pid, event_resA ra)]).
    2 : {
      eapply IHvalid_execution_fragment; auto.
    }
    eapply Step_After_External; eauto.
    eapply Step_None; eauto.
    reflexivity.
  - subst.
    inversion H; subst. inversion H2; subst. clear H2.
    eapply valid_execution_fragment_join' with (a:=[(pid, event_invB qb)]).
    2 : {
      eapply IHvalid_execution_fragment; auto.
    }
    eapply Step_Initial_Call; eauto.
    eapply Step_None; eauto.
    reflexivity.
  - subst.
    inversion H; subst. inversion H2; subst. clear H2.
    eapply valid_execution_fragment_join' with (a:=[(pid, event_resB rb)]).
    2 : {
      eapply IHvalid_execution_fragment; auto.
    }
    eapply Step_Final_Return; eauto.
    eapply Step_None; eauto.
    reflexivity.
Qed.
  
End test.


Section Refinement.

Context {liA : language_interface}.
Variable L : lts li_null liA.

Lemma sync_refines_raw:
  refines (sync L) L.
Proof.
  intros. unfold refines.
  intros. unfold in_traces in H.
  destruct H as [init [final [Hnew Hvalid]]].
  destruct init, final. simpl in *.
  eapply valid_execution_fragment_sync in Hvalid; eauto.
  unfold in_traces.
  exists LState0.
  exists LState1.
  intuition.
  inversion Hnew; subst; intuition.
Qed.

Inductive sequential : list (@_event li_null liA) -> Prop :=
| sequential_nil : sequential nil
| sequential_inv : forall q,
    sequential [q]
| sequential_pair : forall q r events,
  sequential events ->
  sequential (q :: (r :: events))
.

Import LibEnv.

Definition compatible (pos : env Position) (acts : list (@event li_null  liA)) : Prop :=
  forall pid,
    let events := get_pid_events acts pid in
    match events with
    | nil => True
    | e :: events' =>
      match e with
      | event_invB qb => 
        pid # pos /\ sequential events
      | event_resB rb =>
        binds pid Run pos /\ sequential events'
      | event_invA _ => False
      | event_resA _ => False
      end
    end.

Lemma sync_compatible: forall s s' acts,
  valid_execution_fragment (sync L) s s' acts ->
  compatible s.(PidPos) acts.
Proof.
  induction 1; intros.
  - subst.
    unfold compatible. simpl. auto.
  - inversion H; subst; simpl in *; assumption.
  - destruct qa.
  - destruct ra.
  - inversion H; subst; simpl in *.
    -- unfold compatible. intros.
      unfold compatible in IHvalid_execution_fragment.
      simpl in *.
      destruct (pid =? pid0)eqn:Heq.
      --- apply Nat.eqb_eq in Heq. subst.
        intuition.
        specialize (IHvalid_execution_fragment pid0).
        destruct (get_pid_events acts pid0).
        econstructor; eauto.
        destruct _e; simpl in *.
        + intuition. apply notin_union in H2.
          intuition. apply notin_neq in H4; intuition.
        + intuition. unfold binds in H2. simpl in H2.
          rewrite Nat.eqb_refl in H2. inversion H2.
          econstructor; eauto.
        + intuition.
        + intuition.
      --- specialize (IHvalid_execution_fragment pid0).
        destruct (get_pid_events acts pid0).
        auto.
        destruct _e; simpl in *.
        + intuition. apply notin_union in H2; intuition.
        + intuition. unfold binds in H2. simpl in H2.
          apply Nat.eqb_neq in Heq.
          assert (Hneq : pid0 =? pid = false).
          apply Nat.eqb_neq; intuition.
          rewrite Hneq in H2. assumption.
        + intuition.
        + intuition.
  - inversion H; subst; simpl in *.
    -- unfold compatible. intros.
      unfold compatible in IHvalid_execution_fragment.
      simpl in *.
      destruct (pid =? pid0)eqn:Heq.
      --- apply Nat.eqb_eq in Heq. subst.
        intuition.
        specialize (IHvalid_execution_fragment pid0).
        destruct (get_pid_events acts pid0).
        econstructor; eauto.
        destruct _e; simpl in *.
        + intuition.
        + intuition.
          assert (pid0 # (remove pos pid0)).
          apply ok_remove_notin; auto.
          apply binds_in in H2.
          unfold "#" in H4.
          intuition.
        + intuition.
        + intuition.
      --- specialize (IHvalid_execution_fragment pid0).
        destruct (get_pid_events acts pid0).
        auto.
        destruct _e; simpl in *.
        + intuition.
          apply Nat.eqb_neq in Heq.
          eapply remove_neq_preserves_notin; eauto.
        + intuition.
          apply Nat.eqb_neq in Heq.
          eapply remove_preserves_binds_notin; eauto.
        + intuition.
        + intuition.
Qed.

Lemma sync_sequential_compatible: forall acts,
  in_traces (sync L) acts ->
  compatible [] acts.
Proof.
  intros. unfold in_traces in H.
  destruct H as [init [final [Hnew Hvalid]]].
  apply sync_compatible in Hvalid.
  inversion Hnew; subst.
  rewrite H0 in Hvalid. assumption.
Qed.

Definition all_sequential (acts : list (@event li_null liA)) :=
  forall pid,
    sequential (get_pid_events acts pid).

Lemma compatible_nil_sequential: forall acts,
  compatible [] acts ->
  all_sequential acts.
Proof.
  intros.
  unfold compatible in H.
  unfold all_sequential.
  intros.
  specialize (H pid).
  destruct (get_pid_events acts pid).
  - constructor.
  - destruct _e; simpl in *.
    -- intuition.
    -- intuition. inversion H0.
    -- intuition.
    -- intuition.
Qed.

Lemma sync_trace_all_sequential: forall acts,
  in_traces (sync L) acts ->
  all_sequential acts.
Proof.
  intros.
  apply compatible_nil_sequential.
  apply sync_sequential_compatible.
  assumption.
Qed.

Fixpoint test (pos : env Position) (acts : list (@event li_null liA)) : env Position :=
  match acts with
  | nil => pos
  | (pid, act) :: acts' =>
    match act with
    | event_invB qb =>
      test ((pid, Run) :: pos) acts'
    | event_resB rb =>
      test (remove pos pid) acts'
    | event_invA _ => pos
    | event_resA _ => pos
    end
  end.

End Refinement.

Section INV'.

Context {liA : language_interface}.
Variable _L : lts li_null liA.
Local Definition L := (sync _L).

Import LibEnv.

Definition inv s :=
  forall pid,
    binds pid Run s.(PidPos) ->
    exists s1 s2 q acts,
      initial_state L s1 pid q s2 /\
      valid_execution_fragment L s2 s acts /\
      gather_pid_B_events acts pid = []
.

Lemma step_inv : invariant_ind L inv.
Proof.
  unfold invariant_ind. intuition.
  - unfold inv. intros.
    inversion H; subst. simpl in *.
    rewrite H2 in H0.
    inversion H0.
  - unfold inv in *. intros.
    inversion H0; subst.
    simpl in *.
    apply H in H1.
    destruct H1 as [s1 [s2 [q [acts [Hinit [Hvalid Hgather]]]]]].
    exists s1, s2, q, acts.
    intuition.
    eapply valid_execution_fragment_join' with (a:=acts); eauto.
    eapply Step_Internal; eauto.
    eapply Step_None; eauto.
    rewrite app_nil_r.
    reflexivity.
  - unfold inv in *. intros.
    inversion H0; subst.
    simpl in *.
    unfold binds in H1. simpl in H1.
    destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst.
      repeat (eexists; eauto).
      eapply Step_None; eauto.
      simpl. reflexivity.
    -- apply H in H1.
      destruct H1 as [s1 [s2 [q [acts [Hinit [Hvalid Hgather]]]]]].
      exists s1, s2, q, (acts ++ [(pid, event_invB act)]).
      intuition.
      eapply valid_execution_fragment_join' with (a:=acts); eauto.
      eapply Step_Initial_Call; eauto.
      eapply Step_None; eauto.
      rewrite gather_pid_B_events_dist.
      simpl.
      rewrite Heq.
      rewrite app_nil_r. assumption.
  - destruct act.
  - destruct act.
  - unfold inv in *. intros.
    inversion H0; subst.
    simpl in *.
    destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst.
      assert (pid # (remove pos pid)).
      apply ok_remove_notin; auto.
      apply binds_in in H1.
      unfold "#" in H3. intuition.
    -- apply remove_preserves_binds_notin in H1; auto.
      apply H in H1.
      destruct H1 as [s1 [s2 [q [acts [Hinit [Hvalid Hgather]]]]]].
      exists s1, s2, q, (acts ++ [(pid, event_resB act)]).
      intuition.
      eapply valid_execution_fragment_join' with (a:=acts); eauto.
      eapply Step_Final_Return; eauto.
      eapply Step_None; eauto.
      rewrite gather_pid_B_events_dist.
      simpl.
      rewrite Heq.
      rewrite app_nil_r. assumption.
      apply Nat.eqb_neq; intuition.
Qed.
  
End INV'.