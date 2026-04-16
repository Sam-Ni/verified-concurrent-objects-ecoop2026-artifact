Require Import
  List
  Arith
  LibVar
  LTS
  Refinement
  SyncLTS
  Compose.

Import ListNotations.

Section COMP_SYNC.

  Context {liA liB : language_interface}.
  Variable L : composed_lts.composed_lts li_null liA liB.

  Inductive CompPosition : Set :=
  | CompL2Run
  | CompL1Run
  | CompWait
  .

  Record comp_sync_state : Type := mkCompSyncState {
    CompLState : L.(composed_lts.state);

    CompPidPos : LibEnv.env CompPosition;
  }.

  Definition comp_sync_internal_L1 := L.(composed_lts.internal_L1).
  Definition comp_sync_internal_L2 := L.(composed_lts.internal_L2).

  Definition comp_sync_new_state sst : Prop :=
    L.(composed_lts.new_state) sst.(CompLState) /\
    sst.(CompPidPos) = [].

  Import LibEnv.

  Inductive comp_sync_initial_state : comp_sync_state -> Pid -> query liB -> comp_sync_state -> Prop :=
  | comp_sync_initial_state_L : forall sst sst' st st' qb pid pos
      (Hok : ok pos) (Hnotin : pid # pos),
      composed_lts.initial_state L st pid qb st' ->
      sst = mkCompSyncState st pos ->
      sst' = mkCompSyncState st' ((pid, CompL2Run) :: pos) ->
      comp_sync_initial_state sst pid qb sst'
  .

  Inductive comp_sync_step_L2 : comp_sync_state -> Pid -> comp_sync_internal_L2 -> comp_sync_state -> Prop :=
  | comp_sync_step_L2_internal : forall st st' act sst sst' pid pos
      (Hok : ok pos) (Hbinds : binds pid CompL2Run pos),
      composed_lts.step_L2 L st pid act st' ->
      sst = mkCompSyncState st pos ->
      sst' = mkCompSyncState st' pos ->
      comp_sync_step_L2 sst pid act sst'.

  Inductive comp_sync_step_L1 : comp_sync_state -> Pid -> comp_sync_internal_L1 -> comp_sync_state -> Prop :=
  | comp_sync_step_L1_internal : forall st st' act sst sst' pid pos
      (Hok : ok pos) (Hbinds : binds pid CompL1Run pos),
      composed_lts.step_L1 L st pid act st' ->
      sst = mkCompSyncState st pos ->
      sst' = mkCompSyncState st' pos ->
      comp_sync_step_L1 sst pid act sst'.

  Inductive comp_sync_at_external : comp_sync_state -> Pid -> query li_null -> comp_sync_state -> Prop :=.

  Inductive comp_sync_after_external : comp_sync_state -> Pid -> reply li_null -> comp_sync_state -> Prop :=.

  Inductive comp_sync_final_state : comp_sync_state -> Pid -> reply liB -> comp_sync_state -> Prop :=
  | comp_sync_final_state_L : forall st rb st' sst sst' pid pos
      (Hok : ok pos) (Hbinds : binds pid CompL2Run pos),
      composed_lts.final_state L st pid rb st' ->
      sst = mkCompSyncState st pos ->
      sst' = mkCompSyncState st' (remove pos pid) ->
      comp_sync_final_state sst pid rb sst'
  .

  Inductive comp_sync_internal_query : comp_sync_state -> Pid -> query liA -> comp_sync_state -> Prop :=
  | comp_sync_internal_query_L2 : forall st qa st' sst sst' pid pos
      (Hok : ok pos) (Hbinds : binds pid CompL2Run pos),
      composed_lts.internal_query L st pid qa st' ->
      sst = mkCompSyncState st pos ->
      sst' = mkCompSyncState st' ((pid, CompL1Run):: (remove pos pid)) ->
      comp_sync_internal_query sst pid qa sst'
  .

  Inductive comp_sync_internal_reply : comp_sync_state -> Pid -> reply liA -> comp_sync_state -> Prop :=
  | comp_sync_internal_reply_L1 : forall st ra st' sst sst' pid pos
      (Hok : ok pos) (Hbinds : binds pid CompL1Run pos),
      composed_lts.internal_reply L st pid ra st' ->
      sst = mkCompSyncState st pos ->
      sst' = mkCompSyncState st' ((pid, CompL2Run):: (remove pos pid)) ->
      comp_sync_internal_reply sst pid ra sst'
  .

  Definition comp_sync : composed_lts.composed_lts li_null liA liB :=
    composed_lts.mkComposedLTS li_null liA liB
      comp_sync_state
      comp_sync_internal_L1
      comp_sync_internal_L2
      comp_sync_step_L1
      comp_sync_step_L2
      comp_sync_new_state
      comp_sync_initial_state
      comp_sync_at_external
      comp_sync_after_external
      comp_sync_final_state
      comp_sync_internal_query
      comp_sync_internal_reply.
  
End COMP_SYNC.

Arguments CompLState {liA liB L}.
Arguments CompPidPos {liA liB L}.

Section Properties.

Context {liA liB : language_interface}.

Record fsim_properties (L1 L2 : composed_lts.composed_lts li_null liA liB) 
                       (match_states: composed_lts.state L1 -> composed_lts.state L2 -> Prop) : Prop := {
    fsim_match_new_states:
      forall s1, composed_lts.new_state L1 s1 -> 
      exists s2, composed_lts.new_state L2 s2 /\ match_states s1 s2;
    fsim_match_initial_states:
      forall s1 s1' s2 qb pid, match_states s1 s2 -> composed_lts.initial_state L1 s1 pid qb s1' ->
      exists s2', composed_lts.initial_state L2 s2 pid qb s2' /\ match_states s1' s2';
    fsim_match_final_states:
      forall s1 s1' s2 rb pid, match_states s1 s2 -> composed_lts.final_state L1 s1 pid rb s1' ->
      exists s2', composed_lts.final_state L2 s2 pid rb s2' /\ match_states s1' s2';
    fsim_match_internal_query:
      forall s1 s1' s2 qa pid, match_states s1 s2 -> composed_lts.internal_query L1 s1 pid qa s1' ->
      exists s2', composed_lts.internal_query L2 s2 pid qa s2' /\ match_states s1' s2';
    fsim_match_internal_reply:
      forall s1 s1' s2 ra pid, match_states s1 s2 -> composed_lts.internal_reply L1 s1 pid ra s1' ->
      exists s2', composed_lts.internal_reply L2 s2 pid ra s2' /\ match_states s1' s2';
    fsim_simulation:
      forall s1 s1' s2 int pid, match_states s1 s2 -> composed_lts.step_L1 L1 s1 pid int s1' ->
      exists s2', composed_lts.valid_execution_fragment L2 s2 s2' [] /\ match_states s1' s2';
    fsim_simulation':
      forall s1 s1' s2 int pid, match_states s1 s2 -> composed_lts.step_L2 L1 s1 pid int s1' ->
      exists s2', composed_lts.valid_execution_fragment L2 s2 s2' [] /\ match_states s1' s2'
  }.

Definition fsim_properties_inv_ind (L1 L2 : composed_lts.composed_lts li_null liA liB)
                       (match_states: composed_lts.state L1 -> composed_lts.state L2 -> Prop)
                       (inv : L1.(composed_lts.state) -> Prop) : Prop :=
  (composed_lts.invariant_ind _ inv) /\
  (forall s1, composed_lts.new_state L1 s1 -> 
      exists s2, composed_lts.new_state L2 s2 /\ match_states s1 s2) /\
  (forall s1 s1' s2 qb pid, inv s1 -> match_states s1 s2 -> composed_lts.initial_state L1 s1 pid qb s1' ->
    exists s2', composed_lts.initial_state L2 s2 pid qb s2' /\ match_states s1' s2') /\
  (forall s1 s1' s2 rb pid, inv s1 -> match_states s1 s2 -> composed_lts.final_state L1 s1 pid rb s1' ->
    exists s2', composed_lts.final_state L2 s2 pid rb s2' /\ match_states s1' s2') /\
  (forall s1 s1' s2 qa pid, inv s1 -> match_states s1 s2 -> composed_lts.internal_query L1 s1 pid qa s1' ->
    exists s2', composed_lts.internal_query L2 s2 pid qa s2' /\ match_states s1' s2') /\
  (forall s1 s1' s2 ra pid, inv s1 -> match_states s1 s2 -> composed_lts.internal_reply L1 s1 pid ra s1' ->
    exists s2', composed_lts.internal_reply L2 s2 pid ra s2' /\ match_states s1' s2') /\
  (forall s1 s1' s2 int pid, inv s1 -> match_states s1 s2 -> composed_lts.step_L1 L1 s1 pid int s1' ->
    exists s2', composed_lts.valid_execution_fragment L2 s2 s2' [] /\ match_states s1' s2') /\
  (forall s1 s1' s2 int pid, inv s1 -> match_states s1 s2 -> composed_lts.step_L2 L1 s1 pid int s1' ->
    exists s2', composed_lts.valid_execution_fragment L2 s2 s2' [] /\ match_states s1' s2').

Lemma forward_simulation_ind_reconstruct: 
  forall (L1 L2 : composed_lts.composed_lts li_null liA liB) f s1' s1 acts s2',
  fsim_properties _ _ f ->
  composed_lts.valid_execution_fragment L1 s1' s1 acts ->
  f s1' s2' ->
  exists s2,
    f s1 s2 /\ composed_lts.valid_execution_fragment L2 s2' s2 acts.
Proof.
  intros L1 L2 f s1' s1 acts s2'.
  intros Hforward Htrace1 Hrelinit.
  inversion Hforward.
  generalize dependent s2'.
  induction Htrace1; subst; eauto; intros s2' Hrel.
  - exists s2'. intuition.
    econstructor; eauto.
  - 
    specialize (fsim_simulation0 st st'' s2' int pid Hrel H).
    inversion fsim_simulation0 as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply composed_lts.valid_execution_fragment_join'; eauto.
  - 
    specialize (fsim_simulation'0 st st'' s2' int pid Hrel H).
    inversion fsim_simulation'0 as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply composed_lts.valid_execution_fragment_join'; eauto.
  - destruct qa.
  - destruct ra.
  -
    specialize (fsim_match_initial_states0 st st'' s2' qc pid Hrel H).
    inversion fsim_match_initial_states0 as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply composed_lts.Step_Initial_Call; eauto.
  -
    specialize (fsim_match_final_states0 st st'' s2' rc pid Hrel H).
    inversion fsim_match_final_states0 as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply composed_lts.Step_Final_Return; eauto.
  -
    specialize (fsim_match_internal_query0 st st'' s2' qb pid Hrel H).
    inversion fsim_match_internal_query0 as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply composed_lts.Step_Internal_Query; eauto.
  -
    specialize (fsim_match_internal_reply0 st st'' s2' rb pid Hrel H).
    inversion fsim_match_internal_reply0 as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply composed_lts.Step_Internal_Reply; eauto.
Qed.

Theorem forward_simulation_ind :
  forall (L1 L2 : composed_lts.composed_lts li_null liA liB),
  forall (f : L1.(composed_lts.state) -> L2.(composed_lts.state) -> Prop),
    fsim_properties _ _ f ->
    composed_refines L1 L2.
Proof.
  intros L1 L2 f Hforward.
  unfold composed_refines.
  intros acts Htrace1.
  unfold in_traces in *.
  destruct Htrace1 as [s1init [s1final [Hstart1 Hfrag1]]].
  inversion Hforward as [Hrel_start Hrel_trace].
  specialize (Hrel_start s1init Hstart1).
  inversion Hrel_start as [s2init [Hs2start Hs2rel]].
  pose proof (forward_simulation_ind_reconstruct _ _
                f
                s1init
                s1final
                acts
                s2init
                Hforward
                Hfrag1
                Hs2rel) as [s2final [in_acts' Hs2final]].
  repeat eexists; intuition; eauto.
Qed.

Lemma forward_simulation_inv_ind_reconstruct: 
  forall (L1 L2 : composed_lts.composed_lts li_null liA liB) f inv s1' s1 acts s2',
  fsim_properties_inv_ind _ _ f inv ->
  composed_lts.valid_execution_fragment L1 s1' s1 acts ->
  inv s1' ->
  f s1' s2' ->
  exists s2,
    f s1 s2 /\ composed_lts.valid_execution_fragment L2 s2' s2 acts.
Proof.
  intros L1 L2 f inv s1' s1 acts s2'.
  intros Hforward Htrace1 Hrelinit.
  inversion Hforward as [Hinv [_ Hrel_trace]].
  generalize dependent s2'.
  induction Htrace1; subst; eauto; intros s2' Hrel.
  - exists s2'. intuition.
    econstructor; eauto.
  - destruct Hinv as [Hinvstart [Hinvstep [Hinvinit [Hinvat [Hinvafter Hinvfinal]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final [Hrel_trace_query [Hrel_trace_reply [Hrel_trace_step Hrel_trace_step']]]]].
    specialize (Hrel_trace_step st st'' s2' int pid Hinvst Hrel H).
    inversion Hrel_trace_step as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 Hinvst'' s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply composed_lts.valid_execution_fragment_join'; eauto.
  - destruct Hinv as [Hinvstart [Hinvstep [Hinvinit [Hinvat [Hinvafter Hinvfinal]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final [Hrel_trace_query [Hrel_trace_reply [Hrel_trace_step Hrel_trace_step']]]]].
    specialize (Hrel_trace_step' st st'' s2' int pid Hinvst Hrel H).
    inversion Hrel_trace_step' as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 Hinvst'' s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply composed_lts.valid_execution_fragment_join'; eauto.
  - destruct qa.
  - destruct ra.
  - destruct Hinv as [Hinvstart [Hinvstep [Hinvinit [Hinvat [Hinvafter Hinvfinal]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final [Hrel_trace_query [Hrel_trace_reply [Hrel_trace_step Hrel_trace_step']]]]].
    specialize (Hrel_trace_init st st'' s2' qc pid Hinvst Hrel H).
    inversion Hrel_trace_init as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 Hinvst'' s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply composed_lts.Step_Initial_Call; eauto.
  - destruct Hinv as [_ [Hinvstep [Hinvstep' [_ [_ [_ [Hinvfinal _]]]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final [Hrel_trace_query [Hrel_trace_reply [Hrel_trace_step Hrel_trace_step']]]]].
    specialize (Hrel_trace_final st st'' s2' rc pid Hinvst Hrel H).
    inversion Hrel_trace_final as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 Hinvst'' s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply composed_lts.Step_Final_Return; eauto.
  - destruct Hinv as [_ [_ [_ [_ [_ [_ [Hinvfinal [Hinvquery Hinvreply]]]]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final [Hrel_trace_query [Hrel_trace_reply [Hrel_trace_step Hrel_trace_step']]]]].
    specialize (Hrel_trace_query st st'' s2' qb pid Hinvst Hrel H).
    inversion Hrel_trace_query as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 Hinvst'' s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply composed_lts.Step_Internal_Query; eauto.
  - destruct Hinv as [_ [_ [_ [_ [_ [_ [Hinvfinal [Hinvquery Hinvreply]]]]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final [Hrel_trace_query [Hrel_trace_reply [Hrel_trace_step Hrel_trace_step']]]]].
    specialize (Hrel_trace_reply st st'' s2' rb pid Hinvst Hrel H).
    inversion Hrel_trace_reply as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 Hinvst'' s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply composed_lts.Step_Internal_Reply; eauto.
Qed.

Theorem forward_simulation_inv_ind :
  forall (L1 L2 : composed_lts.composed_lts li_null liA liB),
  forall (f : L1.(composed_lts.state) -> L2.(composed_lts.state) -> Prop)
         (inv : L1.(composed_lts.state) -> Prop),
    fsim_properties_inv_ind _ _ f inv ->
    composed_refines L1 L2.
Proof.
  intros L1 L2 f inv Hforward.
  unfold composed_refines.
  intros acts Htrace1.
  unfold in_traces in *.
  destruct Htrace1 as [s1init [s1final [Hstart1 Hfrag1]]].
  inversion Hforward as [[Hrel_inv_start _] [Hrel_start Hrel_trace]].
  specialize (Hrel_start s1init Hstart1).
  inversion Hrel_start as [s2init [Hs2start Hs2rel]].
  assert (inv s1init) as Hinvs1init by eauto.
  pose proof (forward_simulation_inv_ind_reconstruct _ _
                f
                inv
                s1init
                s1final
                acts
                s2init
                Hforward
                Hfrag1
                Hinvs1init
                Hs2rel) as [s2final [in_acts' Hs2final]].
  repeat eexists; intuition; eauto.
Qed.

End Properties.

Section RAWCOMPOSE.

Context {liA liB : language_interface}.

Import LibEnv.

Fixpoint mapL1Pidpos (comppos : env CompPosition) :=
  match comppos with
  | nil => nil
  | (pid, p) :: comppos' =>
    let pos' := mapL1Pidpos comppos' in
    match p with
    | CompL1Run => (pid, Run) :: pos'
    | CompL2Run => pos'
    | CompWait => (pid, Wait) :: pos'
    end
  end.

Fixpoint mapL2Pidpos (comppos : env CompPosition) :=
  match comppos with
  | nil => nil
  | (pid, p) :: comppos' =>
    let pos' := mapL2Pidpos comppos' in
    match p with
    | CompL1Run => (pid, Wait) :: pos'
    | CompL2Run => (pid, Run) :: pos'
    | CompWait => (pid, Wait) :: pos'
    end
  end.

Lemma mapL1Pidpos_preserves_notin: forall comppos pid,
  pid # comppos ->
  pid # (mapL1Pidpos comppos).
Proof.
  induction comppos; simpl; intros.
  - assumption.
  - apply notin_union in H.
    destruct a. simpl in *. intuition.
    apply IHcomppos in H1.
    destruct c; auto.
    simpl. apply notin_union; auto.
    simpl. apply notin_union; auto.
Qed.

Lemma mapL2Pidpos_preserves_notin: forall comppos pid,
  pid # comppos ->
  pid # (mapL2Pidpos comppos).
Proof.
  induction comppos; simpl; intros.
  - assumption.
  - apply notin_union in H.
    destruct a. simpl in *. intuition.
    apply IHcomppos in H1.
    destruct c; auto.
    simpl. apply notin_union; auto.
    simpl. apply notin_union; auto.
    simpl. apply notin_union; auto.
Qed.

Lemma mapL2Pidpos_preserves_ok: forall comppos,
  ok comppos ->
  ok (mapL2Pidpos comppos).
Proof.
  induction 1; simpl; intros.
  - econstructor.
  - destruct T; auto;
    econstructor; eauto;
    apply mapL2Pidpos_preserves_notin; auto.
Qed.

Lemma mapL1Pidpos_preserves_ok: forall comppos,
  ok comppos ->
  ok (mapL1Pidpos comppos).
Proof.
  induction 1; simpl; intros.
  - econstructor.
  - destruct T; auto;
    econstructor; eauto;
    apply mapL1Pidpos_preserves_notin; auto.
Qed.

Lemma mapL1Pidpos_remove_comm: forall comppos pid,
  ok comppos ->
  mapL1Pidpos (remove comppos pid) =
  remove (mapL1Pidpos comppos) pid.
Proof.
  induction 1; simpl; intros.
  - reflexivity.
  - destruct (pid =? x)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst.
      destruct T.
      --- rewrite notin_remove; auto.
        apply mapL1Pidpos_preserves_notin; auto.
      --- simpl. rewrite Nat.eqb_refl.
        reflexivity.
      --- simpl. rewrite Nat.eqb_refl.
        reflexivity.
    -- simpl. rewrite IHok.
      destruct T; simpl.
      reflexivity.
      rewrite Heq. reflexivity.
      rewrite Heq. reflexivity.
Qed.

Lemma mapL2Pidpos_remove_comm: forall comppos pid,
  ok comppos ->
  mapL2Pidpos (remove comppos pid) =
  remove (mapL2Pidpos comppos) pid.
Proof.
  induction 1; simpl; intros.
  - reflexivity.
  - destruct (pid =? x)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst.
      destruct T.
      --- simpl. rewrite Nat.eqb_refl.
        reflexivity.
      --- simpl. rewrite Nat.eqb_refl.
        reflexivity.
      --- simpl. rewrite Nat.eqb_refl.
        reflexivity.
    -- simpl. rewrite IHok.
      destruct T; simpl.
      rewrite Heq. reflexivity.
      rewrite Heq. reflexivity.
      rewrite Heq. reflexivity.
Qed.

Lemma ok_binds_L2_notin_mapL1: forall comppos pid,
  ok comppos ->
  binds pid CompL2Run comppos ->
  pid # (mapL1Pidpos comppos).
Proof.
  induction 1; simpl; intros.
  - inversion H.
  - apply binds_push_inv in H1.
    intuition.
    -- subst.
      apply mapL1Pidpos_preserves_notin; auto.
    -- destruct T.
      --- assumption.
      --- simpl.
        apply notin_union.
        intuition.
        apply notin_neq; auto.
      --- simpl.
        apply notin_union.
        intuition.
        apply notin_neq; auto.
Qed.

Lemma binds_L2_binds_run: forall comppos pid,
  binds pid CompL2Run comppos ->
  binds pid Run (mapL2Pidpos comppos).
Proof.
  induction comppos; simpl; intros.
  - inversion H.
  - destruct a.
    apply binds_push_inv in H.
    intuition.
    -- subst.
      apply binds_push_eq.
    -- destruct c; apply binds_push_neq; auto.
Qed.

Lemma binds_L1_binds_run: forall comppos pid,
  binds pid CompL1Run comppos ->
  binds pid Run (mapL1Pidpos comppos).
Proof.
  induction comppos; simpl; intros.
  - inversion H.
  - destruct a.
    apply binds_push_inv in H.
    intuition.
    -- subst.
      apply binds_push_eq.
    -- destruct c; auto; apply binds_push_neq; auto.
Qed.

Lemma binds_L1_binds_wait_L2: forall comppos pid,
  binds pid CompL1Run comppos ->
  binds pid Wait (mapL2Pidpos comppos).
Proof.
  induction comppos; simpl; intros.
  - inversion H.
  - destruct a.
    apply binds_push_inv in H.
    intuition.
    -- subst.
      apply binds_push_eq.
    -- destruct c; auto; apply binds_push_neq; auto.
Qed.

Lemma raw_compose_refines_compose: forall (L1 : lts li_null liA) (L2 : lts liA liB),
  composed_refines (comp_sync (raw_compose L1 L2)) 
    (compose L1 L2).
Proof.
  intros.
  eapply forward_simulation_inv_ind
    with (f:=fun (x : composed_lts.state (comp_sync (raw_compose L1 L2))) y => 
      x.(CompLState).(RawL1State) = y.(L1State).(LState) /\
      x.(CompLState).(RawL2State) = y.(L2State).(LState) /\
      mapL1Pidpos x.(CompPidPos) = y.(L1State).(PidPos) /\
      mapL2Pidpos x.(CompPidPos) = y.(L2State).(PidPos)
      )
      (inv:=fun x => True).
  unfold fsim_properties_inv_ind. intuition.
  - unfold composed_lts.invariant_ind. intuition.
  - inversion H; subst.
    destruct s1.
    destruct CompLState0. simpl in *.
    inversion H0; subst. simpl in *.
    exists (
      mkComposedState
        (mkSyncState L1 RawL1State [])
        (mkSyncState L2 RawL2State [])
    ).
    simpl. intuition.
    unfold composed_new_state. simpl.
    unfold sync_new_state.
    simpl. intuition.
  - inversion H1; subst.
    simpl in *.
    inversion H4; subst.
    simpl in *.
    exists (
      mkComposedState
        (L1State s2)
        (mkSyncState L2 st2' 
          ((pid, Run)::s2.(L2State).(PidPos)))
    ).
    simpl. intuition.
    2 : { f_equal. assumption. }
    destruct s2. simpl in *.
    eapply composed_initial_state_L2; eauto.
    rewrite <-H3.
    apply mapL1Pidpos_preserves_notin; auto.
    eapply sync_initial_state_L; eauto.
    rewrite <-H5.
    apply mapL2Pidpos_preserves_ok; auto.
    rewrite <-H5.
    apply mapL2Pidpos_preserves_notin; auto.
    destruct L2State. simpl.
    rewrite H0. reflexivity.
  - inversion H1; subst.
    simpl in *.
    inversion H4; subst.
    simpl in *.
    exists (
      mkComposedState
        (L1State s2)
        (mkSyncState L2 st2' 
          (remove s2.(L2State).(PidPos) pid))
    ).
    simpl. intuition.
    2 : { rewrite mapL1Pidpos_remove_comm; auto.
      rewrite <-H3.
      rewrite notin_remove; auto.
      apply ok_binds_L2_notin_mapL1; auto.
    }
    2 : { rewrite mapL2Pidpos_remove_comm; auto.
      rewrite <-H5.
      reflexivity.
    }
    destruct s2. simpl in *.
    eapply composed_final_state_L2; eauto.
    rewrite <-H3.
    apply ok_binds_L2_notin_mapL1; auto.
    eapply sync_final_state_L; eauto.
    rewrite <-H5.
    apply mapL2Pidpos_preserves_ok; auto.
    rewrite <-H5.
    apply binds_L2_binds_run; auto.
    destruct L2State. simpl.
    rewrite H0. reflexivity.
  - inversion H1; subst.
    simpl in *.
    inversion H4; subst.
    simpl in *.
    exists (
      mkComposedState
        (mkSyncState L1 st1' 
          ((pid, Run)::s2.(L1State).(PidPos)))
        (mkSyncState L2 st2' 
          ((pid, Wait):: (remove s2.(L2State).(PidPos) pid)))
    ).
    simpl. intuition.
    2 : {
      f_equal.
      rewrite mapL1Pidpos_remove_comm; auto.
      rewrite <-H3.
      rewrite notin_remove; auto.
      apply ok_binds_L2_notin_mapL1; auto.
    }
    2 : { rewrite mapL2Pidpos_remove_comm; auto.
      rewrite <-H5.
      reflexivity.
    }
    destruct s2. simpl in *.
    eapply composed_step_L2_push; eauto.
    simpl.
    eapply sync_at_external_L; eauto.
    rewrite <-H5.
    apply mapL2Pidpos_preserves_ok; auto.
    rewrite <-H5.
    apply binds_L2_binds_run; auto.
    destruct L2State. simpl.
    rewrite H0. reflexivity.
    rewrite <-H3.
    eapply sync_initial_state_L; eauto.
    apply mapL1Pidpos_preserves_ok; auto.
    apply ok_binds_L2_notin_mapL1; auto.
    destruct L1State. simpl.
    rewrite H2. simpl.
    rewrite H3. reflexivity.
  - inversion H1; subst.
    simpl in *.
    inversion H4; subst.
    simpl in *.
    exists (
      mkComposedState
        (mkSyncState L1 st1' 
          (remove s2.(L1State).(PidPos) pid))
        (mkSyncState L2 st2' 
          ((pid, Run):: (remove s2.(L2State).(PidPos) pid)))
    ).
    simpl. intuition.
    2 : {
      rewrite mapL1Pidpos_remove_comm; auto.
      rewrite <-H3. reflexivity.
    }
    2 : { f_equal.
      rewrite mapL2Pidpos_remove_comm; auto.
      rewrite <-H5.
      reflexivity.
    }
    destruct s2. simpl in *.
    eapply composed_step_L1_pop; eauto.
    simpl.
    eapply sync_final_state_L; eauto.
    rewrite <-H3.
    apply mapL1Pidpos_preserves_ok; auto.
    rewrite <-H3.
    apply binds_L1_binds_run; auto.
    destruct L1State. simpl.
    rewrite H2. simpl.
    reflexivity.
    rewrite <-H5.
    simpl.
    eapply sync_after_external_L; eauto.
    apply mapL2Pidpos_preserves_ok; auto.
    apply binds_L1_binds_wait_L2; auto.
    destruct L2State. simpl.
    rewrite H0. simpl.
    rewrite H5. reflexivity.
  - inversion H1; subst.
    simpl in *.
    inversion H4; subst.
    simpl in *.
    exists (
      mkComposedState
        (mkSyncState L1 st1' 
          (s2.(L1State).(PidPos)))
        (L2State s2)
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply composed_lts.Step_Internal_L1 with (pid:=pid); eauto.
    eapply composed_step_L1_internal; eauto.
    rewrite <-H5.
    apply binds_L1_binds_wait_L2; auto.
    2 : {
      eapply composed_lts.Step_None; eauto.
    }
    rewrite <-H3.
    eapply sync_step_L_internal; eauto.
    apply mapL1Pidpos_preserves_ok; auto.
    apply binds_L1_binds_run; auto.
    destruct L1State. simpl.
    rewrite H2. simpl.
    rewrite H3. simpl. reflexivity.
  - inversion H1; subst.
    simpl in *.
    inversion H4; subst.
    simpl in *.
    exists (
      mkComposedState
        (L1State s2)
        (mkSyncState L2 st2' 
          (s2.(L2State).(PidPos)))
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply composed_lts.Step_Internal_L2 with (pid:=pid); eauto.
    eapply composed_step_L2_internal; eauto.
    rewrite <-H3.
    apply ok_binds_L2_notin_mapL1; auto.
    2 : {
      eapply composed_lts.Step_None; eauto.
    }
    rewrite <-H5.
    eapply sync_step_L_internal; eauto.
    apply mapL2Pidpos_preserves_ok; auto.
    apply binds_L2_binds_run; auto.
    destruct L2State. simpl.
    rewrite H0. simpl.
    rewrite H5. simpl. reflexivity.
Qed.

Lemma link_valid_compose_valid: forall (L : composed_lts.composed_lts li_null liA liB) st st' acts,
  valid_execution_fragment (linked_lts L) st st' acts ->
  exists c_acts, composed_lts.valid_execution_fragment L st st' c_acts /\
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

Lemma link_in_trace_compose_in_trace : forall (L : composed_lts.composed_lts li_null liA liB) acts,
  in_traces (linked_lts L) acts ->
  exists c_acts, composed_lts.in_traces L c_acts
    /\ filterB c_acts = acts.
Proof.
  intros. unfold in_traces in H.
  destruct H as [init [final [Hnew Hvalid]]].
  eapply link_valid_compose_valid in Hvalid.
  destruct Hvalid as [c_acts [Hcvalid Hfilter]].
  subst. exists c_acts. intuition.
  unfold composed_lts.in_traces.
  eexists; eauto.
Qed.

Lemma link_preserves_valid_exe: forall (L : composed_lts.composed_lts li_null liA liB) st st' acts,
  composed_lts.valid_execution_fragment L st st' acts ->
  valid_execution_fragment (linked_lts L) st st' (filterB acts).
Proof.
  induction 1; simpl; intros.
  - subst. simpl. econstructor; eauto.
  - assert (valid_execution_fragment (linked_lts L) st st'' []).
    eapply Step_Internal; eauto. simpl.
    eapply linked_step_int_L1; eauto.
    econstructor; eauto.
    eapply valid_execution_fragment_join'; eauto.
  - assert (valid_execution_fragment (linked_lts L) st st'' []).
    eapply Step_Internal; eauto. simpl.
    eapply linked_step_int_L2; eauto.
    econstructor; eauto.
    eapply valid_execution_fragment_join'; eauto.
  - eapply Step_At_External; eauto.
  - eapply Step_After_External; eauto.
  - eapply Step_Initial_Call; eauto.
  - eapply Step_Final_Return; eauto.
  - assert (valid_execution_fragment (linked_lts L) st st'' []).
    eapply Step_Internal; eauto. simpl.
    eapply linked_step_L2_push; eauto.
    econstructor; eauto.
    eapply valid_execution_fragment_join'; eauto.
  - assert (valid_execution_fragment (linked_lts L) st st'' []).
    eapply Step_Internal; eauto. simpl.
    eapply linked_step_L1_pop; eauto.
    econstructor; eauto.
    eapply valid_execution_fragment_join'; eauto.
Qed.

Lemma link_preserves_in_traces : forall (L : composed_lts.composed_lts li_null liA liB) acts,
  composed_lts.in_traces L acts ->
  in_traces (linked_lts L) (filterB acts).
Proof.
  intros. unfold in_traces.
  unfold composed_lts.in_traces in H.
  destruct H as [init [final [Hnew Hvalid]]].
  eapply link_preserves_valid_exe in Hvalid.
  exists init, final. intuition.
Qed.

Lemma link_preserves_composed_refines: forall (L1 L2 : composed_lts.composed_lts li_null liA liB),
  composed_refines L1 L2 ->
  refines (linked_lts L1) (linked_lts L2).
Proof.
  intros. unfold refines. intros.
  apply link_in_trace_compose_in_trace in H0.
  destruct H0 as [c_acts [Hcin_trace Hfilter]].
  apply H in Hcin_trace. subst.
  eapply link_preserves_in_traces. assumption.
Qed.


Lemma link_raw_compose_refines_link_compose: forall (L1 : lts li_null liA) (L2 : lts liA liB),
  refines (linked_lts (comp_sync (raw_compose L1 L2)))
    (linked_lts (compose L1 L2)).
Proof.
  intros.
  apply link_preserves_composed_refines.
  apply raw_compose_refines_compose; auto.
Qed.

End RAWCOMPOSE.
