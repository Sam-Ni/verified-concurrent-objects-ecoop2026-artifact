Require Import
  List
  LTS
  SyncLTS
  Refinement
  Compose.

Import ListNotations.

Section t.

Context {liA liB liC : language_interface}.
Variable L1 : lts liA liB.
Variable L2 : lts liB liC.

Fixpoint filterB (acts : list (@composed_lts.event liA liB liC)) : list event :=
  match acts with
  | nil => nil
  | (pid, act) :: acts' =>
    let events' := filterB acts' in
    match act with
    | composed_lts.event_invC qc => (pid, event_invB qc) :: events'
    | composed_lts.event_resC rc => (pid, event_resB rc) :: events'
    | composed_lts.event_invB _ => events'
    | composed_lts.event_resB _ => events'
    | composed_lts.event_invA qa => (pid, event_invA qa) :: events'
    | composed_lts.event_resA ra => (pid, event_resA ra) :: events'
    end
  end.

End t.

Section LinkTrace.

Context {liA liB : language_interface}.
Variable L1 : lts li_null liA.
Variable L1' : lts li_null liA.
Variable L2 : lts liA liB.

Lemma link_valid_compose_valid: forall st st' acts,
  valid_execution_fragment (linked_lts (compose L1 L2)) st st' acts ->
  exists c_acts, composed_lts.valid_execution_fragment (compose L1 L2) st st' c_acts /\
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

Lemma link_in_trace_compose_in_trace : forall acts,
  in_traces (linked_lts (compose L1 L2)) acts ->
  exists c_acts, composed_lts.in_traces (compose L1 L2) c_acts
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

Lemma link_preserves_valid_exe: forall st st' acts,
  composed_lts.valid_execution_fragment (compose L1 L2) st st' acts ->
  valid_execution_fragment (linked_lts (compose L1 L2)) st st' (filterB acts).
Proof.
  induction 1; simpl; intros.
  - subst. simpl. econstructor; eauto.
  - assert (valid_execution_fragment (linked_lts (compose L1 L2)) st st'' []).
    eapply Step_Internal; eauto. simpl.
    eapply linked_step_int_L1; eauto.
    econstructor; eauto.
    eapply valid_execution_fragment_join'; eauto.
  - assert (valid_execution_fragment (linked_lts (compose L1 L2)) st st'' []).
    eapply Step_Internal; eauto. simpl.
    eapply linked_step_int_L2; eauto.
    econstructor; eauto.
    eapply valid_execution_fragment_join'; eauto.
  - eapply Step_At_External; eauto.
  - eapply Step_After_External; eauto.
  - eapply Step_Initial_Call; eauto.
  - eapply Step_Final_Return; eauto.
  - assert (valid_execution_fragment (linked_lts (compose L1 L2)) st st'' []).
    eapply Step_Internal; eauto. simpl.
    eapply linked_step_L2_push; eauto.
    econstructor; eauto.
    eapply valid_execution_fragment_join'; eauto.
  - assert (valid_execution_fragment (linked_lts (compose L1 L2)) st st'' []).
    eapply Step_Internal; eauto. simpl.
    eapply linked_step_L1_pop; eauto.
    econstructor; eauto.
    eapply valid_execution_fragment_join'; eauto.
Qed.

Lemma link_preserves_in_traces : forall acts,
  composed_lts.in_traces (compose L1 L2) acts ->
  in_traces (linked_lts (compose L1 L2)) (filterB acts).
Proof.
  intros. unfold in_traces.
  unfold composed_lts.in_traces in H.
  destruct H as [init [final [Hnew Hvalid]]].
  eapply link_preserves_valid_exe in Hvalid.
  exists init, final. intuition.
Qed.

End LinkTrace.

Section LINKCOMPOSE.

Context {liA liB : language_interface}.

Lemma composed_refines_linked_refines: forall (L1 L1' : lts li_null liA) (L2 : lts liA liB),
  composed_refines (compose L1 L2) (compose L1' L2) ->
  refines (linked_lts (compose L1 L2)) (linked_lts (compose L1' L2)).
Proof.
  intros. unfold refines. intros.
  apply link_in_trace_compose_in_trace in H0.
  destruct H0 as [c_acts [Hcin_trace Hfilter]].
  apply H in Hcin_trace. subst.
  eapply link_preserves_in_traces. assumption.
Qed.

Lemma linked_refines_congruence: forall (L1 L1' : lts li_null liA) (L2 : lts liA liB),
  refines (sync L1) (sync L1') ->
  refines (linked_lts (compose L1 L2)) (linked_lts (compose L1' L2)).
Proof.
  intros.
  eapply refines_composed_refines in H.
  apply composed_refines_linked_refines; eauto.
Qed.

End LINKCOMPOSE.

Notation " L ◁-' M " := (linked_lts (compose L M)) (at level 67).

Section LinkedRefinement.

Context {liA liB liC: language_interface}.
Variable L1: lts li_null liA.
Variable L1': lts li_null liA.
Variable L2: lts liA liB.
Variable L2': lts li_null liB.

Theorem linked_refinement:
  (sc L1) ⊑' (sc L1') ->
  (L1' ◁-' L2) ⊑' L2' ->
  (L1 ◁-' L2) ⊑' L2'.
Proof.
  intros. eapply trans_refinement; eauto.
  apply linked_refines_congruence; auto.
Qed.

End LinkedRefinement.
