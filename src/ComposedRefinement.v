Require Import
  List
  LTS
  Refinement
  Compose
  Link.

Import ListNotations.

Section ComposedSimulation.
  
Context {liA liB : language_interface}.

Definition composed_refines_spec (L : composed_lts.composed_lts li_null liA liB) (L2 : lts li_null liB) : Prop :=
  forall acts, composed_lts.in_traces L acts ->
    in_traces L2 (filterB acts).

Lemma composed_refines_spec_imply_refines:
  forall (L1 : lts li_null liA) (L1' : lts liA liB) (L2 : lts li_null liB),
  composed_refines_spec (compose L1 L1') L2 ->
  refines (linked_lts (compose L1 L1')) L2.
Proof.
  intros. unfold refines. intros.
  unfold composed_refines_spec in H.
  apply link_in_trace_compose_in_trace in H0.
  destruct H0 as [c_acts [Hcin_trace Hfilter]].
  apply H in Hcin_trace. subst. assumption.
Qed.

Record composed_fsim_properties 
        (L1 : lts li_null liA) (L1' : lts liA liB) (L2 : lts li_null liB) 
        (match_states: composed_lts.state (compose L1 L1') -> state L2 -> Prop) : Prop := {
    fsim_match_new_states:
      forall s1, composed_lts.new_state (compose L1 L1') s1 -> 
      exists s2, new_state L2 s2 /\ match_states s1 s2;
    fsim_match_initial_states:
      forall s1 s1' s2 qb pid, match_states s1 s2 -> composed_lts.initial_state (compose L1 L1') s1 pid qb s1' ->
      exists s2', initial_state L2 s2 pid qb s2' /\ match_states s1' s2';
    fsim_match_final_states:
      forall s1 s1' s2 rb pid, match_states s1 s2 -> composed_lts.final_state (compose L1 L1') s1 pid rb s1' ->
      exists s2', final_state L2 s2 pid rb s2' /\ match_states s1' s2';
    fsim_simulation:
      forall s1 s1' s2 int pid, match_states s1 s2 -> composed_lts.step_L1 (compose L1 L1') s1 pid int s1' ->
      exists s2', valid_execution_fragment L2 s2 s2' [] /\ match_states s1' s2';
    fsim_simulation':
      forall s1 s1' s2 int pid, match_states s1 s2 -> composed_lts.step_L2 (compose L1 L1') s1 pid int s1' ->
      exists s2', valid_execution_fragment L2 s2 s2' [] /\ match_states s1' s2';
    fsim_match_internal_query:
      forall s1 s1' s2 qa pid, match_states s1 s2 -> composed_lts.internal_query (compose L1 L1') s1 pid qa s1' ->
      exists s2', valid_execution_fragment L2 s2 s2' [] /\ match_states s1' s2';
    fsim_match_internal_reply:
      forall s1 s1' s2 ra pid, match_states s1 s2 -> composed_lts.internal_reply (compose L1 L1') s1 pid ra s1' ->
      exists s2', valid_execution_fragment L2 s2 s2' [] /\ match_states s1' s2';
  }.

Definition composed_fsim_properties_inv_ind
        (L1 : lts li_null liA) (L1' : lts liA liB) (L2 : lts li_null liB) 
        (match_states: composed_lts.state (compose L1 L1') -> state L2 -> Prop)
        (inv : composed_lts.state (compose L1 L1') -> Prop) : Prop :=
  (composed_lts.invariant_ind _ inv) /\
      (forall s1, composed_lts.new_state (compose L1 L1') s1 -> 
      exists s2, new_state L2 s2 /\ match_states s1 s2) /\
      (forall s1 s1' s2 qb pid, inv s1 -> match_states s1 s2 -> composed_lts.initial_state (compose L1 L1') s1 pid qb s1' ->
      exists s2', initial_state L2 s2 pid qb s2' /\ match_states s1' s2') /\
      (forall s1 s1' s2 rb pid, inv s1 -> match_states s1 s2 -> composed_lts.final_state (compose L1 L1') s1 pid rb s1' ->
      exists s2', final_state L2 s2 pid rb s2' /\ match_states s1' s2') /\
      (forall s1 s1' s2 int pid, inv s1 -> match_states s1 s2 -> composed_lts.step_L1 (compose L1 L1') s1 pid int s1' ->
      exists s2', valid_execution_fragment L2 s2 s2' [] /\ match_states s1' s2') /\
      (forall s1 s1' s2 int pid, inv s1 -> match_states s1 s2 -> composed_lts.step_L2 (compose L1 L1') s1 pid int s1' ->
      exists s2', valid_execution_fragment L2 s2 s2' [] /\ match_states s1' s2') /\
      (forall s1 s1' s2 qa pid, inv s1 -> match_states s1 s2 -> composed_lts.internal_query (compose L1 L1') s1 pid qa s1' ->
      exists s2', valid_execution_fragment L2 s2 s2' [] /\ match_states s1' s2') /\
      (forall s1 s1' s2 ra pid, inv s1 -> match_states s1 s2 -> composed_lts.internal_reply (compose L1 L1') s1 pid ra s1' ->
      exists s2', valid_execution_fragment L2 s2 s2' [] /\ match_states s1' s2')
  .

Lemma composed_forward_simulation_ind_reconstruct: 
  forall (L1 : lts li_null liA) (L1' : lts liA liB) (L2 : lts li_null liB)
    f s1' s1 acts s2',
  composed_fsim_properties _ _ _ f ->
  composed_lts.valid_execution_fragment (compose L1 L1') s1' s1 acts ->
  f s1' s2' ->
  exists s2,
    f s1 s2 /\ valid_execution_fragment L2 s2' s2 (filterB acts).
Proof.
  intros L1 L1' L2 f s1' s1 acts s2'.
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
    eapply valid_execution_fragment_join'; eauto.
  - 
    specialize (fsim_simulation'0 st st'' s2' int pid Hrel H).
    inversion fsim_simulation'0 as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply valid_execution_fragment_join'; eauto.
  - destruct qa.
  - destruct ra.
  -
    specialize (fsim_match_initial_states0 st st'' s2' qc pid Hrel H).
    inversion fsim_match_initial_states0 as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply Step_Initial_Call; eauto.
  -
    specialize (fsim_match_final_states0 st st'' s2' rc pid Hrel H).
    inversion fsim_match_final_states0 as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply Step_Final_Return; eauto.
  -
    specialize (fsim_match_internal_query0 st st'' s2' qb pid Hrel H).
    inversion fsim_match_internal_query0 as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    simpl.
    eapply valid_execution_fragment_join'; eauto.
  -
    specialize (fsim_match_internal_reply0 st st'' s2' rb pid Hrel H).
    inversion fsim_match_internal_reply0 as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    simpl.
    eapply valid_execution_fragment_join'; eauto.
Qed.

Lemma composed_forward_simulation_inv_ind_reconstruct: 
  forall (L1 : lts li_null liA) (L1' : lts liA liB) (L2 : lts li_null liB)
    f inv s1' s1 acts s2',
  composed_fsim_properties_inv_ind _ _ _ f inv ->
  composed_lts.valid_execution_fragment (compose L1 L1') s1' s1 acts ->
  inv s1' ->
  f s1' s2' ->
  exists s2,
    f s1 s2 /\ valid_execution_fragment L2 s2' s2 (filterB acts).
Proof.
  intros L1 L1' L2 f inv s1' s1 acts s2'.
  intros Hforward Htrace1 Hrelinit.
  inversion Hforward as [Hinv [_ Hrel_trace]].
  generalize dependent s2'.
  induction Htrace1; subst; eauto; intros s2' Hrel.
  - exists s2'. intuition.
    econstructor; eauto.
  - destruct Hinv as [Hinvstart [Hinvstep [Hinvinit [Hinvat [Hinvafter Hinvfinal]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final [Hrel_trace_step [Hrel_trace_query Hrel_trace_reply]]]].
    specialize (Hrel_trace_step st st'' s2' int pid Hinvst Hrel H).
    inversion Hrel_trace_step as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 Hinvst'' s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply valid_execution_fragment_join'; eauto.
  - destruct Hinv as [Hinvstart [Hinvstep [Hinvinit [Hinvat [Hinvafter Hinvfinal]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final [Hrel_trace_step [Hrel_trace_step' [Hrel_trace_query Hrel_trace_reply]]]]].
    specialize (Hrel_trace_step' st st'' s2' int pid Hinvst Hrel H).
    inversion Hrel_trace_step' as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 Hinvst'' s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply valid_execution_fragment_join'; eauto.
  - destruct qa.
  - destruct ra.
  - destruct Hinv as [Hinvstart [Hinvstep [Hinvinit [Hinvat [Hinvafter Hinvfinal]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final [Hrel_trace_step [Hrel_trace_step' [Hrel_trace_query Hrel_trace_reply]]]]].
    specialize (Hrel_trace_init st st'' s2' qc pid Hinvst Hrel H).
    inversion Hrel_trace_init as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 Hinvst'' s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply Step_Initial_Call; eauto.
  - destruct Hinv as [_ [Hinvstep [Hinvstep' [_ [_ [_ [Hinvfinal _]]]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final [Hrel_trace_step [Hrel_trace_step' [Hrel_trace_query Hrel_trace_reply]]]]].
    specialize (Hrel_trace_final st st'' s2' rc pid Hinvst Hrel H).
    inversion Hrel_trace_final as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 Hinvst'' s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply Step_Final_Return; eauto.
  - destruct Hinv as [_ [_ [_ [_ [_ [_ [Hinvfinal [Hinvquery Hinvreply]]]]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final [Hrel_trace_step [Hrel_trace_step' [Hrel_trace_query Hrel_trace_reply]]]]].
    specialize (Hrel_trace_query st st'' s2' qb pid Hinvst Hrel H).
    inversion Hrel_trace_query as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 Hinvst'' s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    simpl.
    eapply valid_execution_fragment_join'; eauto.
  - destruct Hinv as [_ [_ [_ [_ [_ [_ [Hinvfinal [Hinvquery Hinvreply]]]]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final [Hrel_trace_step [Hrel_trace_step' [Hrel_trace_query Hrel_trace_reply]]]]].
    specialize (Hrel_trace_reply st st'' s2' rb pid Hinvst Hrel H).
    inversion Hrel_trace_reply as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 Hinvst'' s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    simpl.
    eapply valid_execution_fragment_join'; eauto.
Qed.

Theorem composed_forward_simulation_inv_ind :
  forall (L1 : lts li_null liA) (L1' : lts liA liB) (L2 : lts li_null liB),
  forall (f : composed_lts.state (compose L1 L1') -> L2.(state) -> Prop)
         (inv : composed_lts.state (compose L1 L1') -> Prop),
    composed_fsim_properties_inv_ind _ _ _ f inv ->
    composed_refines_spec (compose L1 L1') L2.
Proof.
  intros L1 L1' L2 f inv Hforward.
  unfold composed_refines_spec.
  intros acts Htrace1.
  unfold in_traces in *.
  destruct Htrace1 as [s1init [s1final [Hstart1 Hfrag1]]].
  inversion Hforward as [[Hrel_inv_start _] [Hrel_start Hrel_trace]].
  specialize (Hrel_start s1init Hstart1).
  inversion Hrel_start as [s2init [Hs2start Hs2rel]].
  assert (inv s1init) as Hinvs1init by eauto.
  pose proof (composed_forward_simulation_inv_ind_reconstruct _ _ _
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

Theorem composed_forward_simulation_inv_ind' :
  forall (L1 : lts li_null liA) (L1' : lts liA liB) (L2 : lts li_null liB),
  forall (f : composed_lts.state (compose L1 L1') -> L2.(state) -> Prop)
         (inv : composed_lts.state (compose L1 L1') -> Prop),
    composed_fsim_properties_inv_ind _ _ _ f inv ->
    refines (linked_lts (compose L1 L1')) L2.
Proof.
  intros.
  eapply composed_refines_spec_imply_refines; eauto.
  eapply composed_forward_simulation_inv_ind; eauto.
Qed.

End ComposedSimulation.