Require Import
  List
  LTS
  Refinement
  RawCompose.
Import ListNotations.

Section ImplRefinement.

Context {liA liB : language_interface}.

Definition impl_refines (L1 L2 : lts liA liB) : Prop :=
  forall acts, in_traces L1 acts -> in_traces L2 acts.

Lemma impl_refines_composed_refines : forall (L1 : lts li_null liA) (L2 L2' : lts liA liB),
  impl_refines (L2) (L2') ->
  composed_refines (raw_compose L1 L2) (raw_compose L1 L2').
Proof.
  intros.
  unfold composed_refines. intros.
  unfold impl_refines in H.
  unfold composed_lts.in_traces in H0.
  destruct H0 as [init [final [Hnew Hvalid]]].
  assert (Hvalidtmp : composed_lts.valid_execution_fragment (raw_compose L1 L2) init final c_acts).
  assumption.
  assert (Hvalidtmp' : composed_lts.valid_execution_fragment (raw_compose L1 L2) init final c_acts).
  assumption.
  apply valid_execution_fragment_com in Hvalidtmp.
  apply valid_execution_fragment_com' in Hvalid.
  assert (in_traces (L2') (gatherBC c_acts)).
  apply H.
  unfold in_traces. simpl in init, final.
  destruct init. destruct final. simpl in *.
  inversion Hnew; subst. simpl in *.
  eexists; eauto.
  unfold in_traces in H0.
  destruct H0 as [init' [final' [Hnew' Hvalid']]].
  unfold composed_lts.in_traces. simpl in *.
  destruct init. destruct final.
  inversion Hnew; subst. simpl in *.
  exists (mkRawComposedState RawL1State init').
  exists (mkRawComposedState RawL1State0 final').
  intuition.
  unfold raw_composed_new_state. simpl. intuition.
  eapply valid_execution_fragment_join; eauto.
Qed.

End ImplRefinement.

Notation " M ⊑ M' " := (impl_refines M M') (at level 67).

Section Simulation.

Context {liA liB : language_interface}.

Record fsim_properties (L1 L2 : lts liA liB) 
                       (match_states: state L1 -> state L2 -> Prop) : Prop := {
    fsim_match_new_states:
      forall s1, new_state L1 s1 -> 
      exists s2, new_state L2 s2 /\ match_states s1 s2;
    fsim_match_initial_states:
      forall s1 s1' s2 qb pid, match_states s1 s2 -> initial_state L1 s1 pid qb s1' ->
      exists s2', initial_state L2 s2 pid qb s2' /\ match_states s1' s2';
    fsim_match_final_states:
      forall s1 s1' s2 rb pid, match_states s1 s2 -> final_state L1 s1 pid rb s1' ->
      exists s2', final_state L2 s2 pid rb s2' /\ match_states s1' s2';
    fsim_match_at_external:
      forall s1 s1' s2 qa pid, match_states s1 s2 -> at_external L1 s1 pid qa s1' ->
      exists s2', at_external L2 s2 pid qa s2' /\ match_states s1' s2';
    fsim_match_after_external:
      forall s1 s1' s2 ra pid, match_states s1 s2 -> after_external L1 s1 pid ra s1' ->
      exists s2', after_external L2 s2 pid ra s2' /\ match_states s1' s2';
    fsim_simulation:
      forall s1 s1' s2 int pid, match_states s1 s2 -> step L1 s1 pid int s1' ->
      exists s2', valid_execution_fragment L2 s2 s2' [] /\ match_states s1' s2'
  }.

Definition fsim_properties_inv_ind (L1 L2 : lts liA liB)
                       (match_states: state L1 -> state L2 -> Prop)
                       (inv : L1.(state) -> Prop) : Prop :=
  (invariant_ind _ inv) /\
      (forall s1, new_state L1 s1 -> 
      exists s2, new_state L2 s2 /\ match_states s1 s2) /\
      (forall s1 s1' s2 qb pid, inv s1 -> match_states s1 s2 -> initial_state L1 s1 pid qb s1' ->
      exists s2', initial_state L2 s2 pid qb s2' /\ match_states s1' s2') /\
      (forall s1 s1' s2 rb pid, inv s1 -> match_states s1 s2 -> final_state L1 s1 pid rb s1' ->
      exists s2', final_state L2 s2 pid rb s2' /\ match_states s1' s2') /\
      (forall s1 s1' s2 qa pid, inv s1 -> match_states s1 s2 -> at_external L1 s1 pid qa s1' ->
      exists s2', at_external L2 s2 pid qa s2' /\ match_states s1' s2') /\
      (forall s1 s1' s2 ra pid, inv s1 -> match_states s1 s2 -> after_external L1 s1 pid ra s1' ->
      exists s2', after_external L2 s2 pid ra s2' /\ match_states s1' s2') /\
      (forall s1 s1' s2 int pid, inv s1 -> match_states s1 s2 -> step L1 s1 pid int s1' ->
      exists s2', valid_execution_fragment L2 s2 s2' [] /\ match_states s1' s2')
    .

Lemma forward_simulation_ind_reconstruct: 
  forall (L1 L2 : lts liA liB) f s1' s1 acts s2',
  fsim_properties _ _ f ->
  valid_execution_fragment L1 s1' s1 acts ->
  f s1' s2' ->
  exists s2,
    f s1 s2 /\ valid_execution_fragment L2 s2' s2 acts.
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
    eapply valid_execution_fragment_join'; eauto.
  - 
    specialize (fsim_match_at_external0 st st'' s2' qa pid Hrel H).
    inversion fsim_match_at_external0 as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply Step_At_External; eauto.
  - 
    specialize (fsim_match_after_external0 st st'' s2' ra pid Hrel H).
    inversion fsim_match_after_external0 as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply Step_After_External; eauto.
  -
    specialize (fsim_match_initial_states0 st st'' s2' qb pid Hrel H).
    inversion fsim_match_initial_states0 as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply Step_Initial_Call; eauto.
  -
    specialize (fsim_match_final_states0 st st'' s2' rb pid Hrel H).
    inversion fsim_match_final_states0 as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply Step_Final_Return; eauto.
Qed.

Theorem forward_simulation_ind :
  forall (L1 L2 : lts liA liB),
  forall (f : L1.(state) -> L2.(state) -> Prop),
    fsim_properties _ _ f ->
    impl_refines L1 L2.
Proof.
  intros L1 L2 f Hforward.
  unfold refines.
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
  forall (L1 L2 : lts liA liB) f inv s1' s1 acts s2',
  fsim_properties_inv_ind _ _ f inv ->
  valid_execution_fragment L1 s1' s1 acts ->
  inv s1' ->
  f s1' s2' ->
  exists s2,
    f s1 s2 /\ valid_execution_fragment L2 s2' s2 acts.
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
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final [Hrel_trace_at [Hrel_trace_after Hrel_trace_step]]]].
    specialize (Hrel_trace_step st st'' s2' int pid Hinvst Hrel H).
    inversion Hrel_trace_step as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 Hinvst'' s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply valid_execution_fragment_join'; eauto.
  - destruct Hinv as [Hinvstart [Hinvstep [Hinvinit [Hinvat [Hinvafter Hinvfinal]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final [Hrel_trace_at [Hrel_trace_after Hrel_trace_step]]]].
    specialize (Hrel_trace_at st st'' s2' qa pid Hinvst Hrel H).
    inversion Hrel_trace_at as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 Hinvst'' s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply Step_At_External; eauto.
  - destruct Hinv as [Hinvstart [Hinvstep [Hinvinit [Hinvat [Hinvafter Hinvfinal]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final [Hrel_trace_at [Hrel_trace_after Hrel_trace_step]]]].
    specialize (Hrel_trace_after st st'' s2' ra pid Hinvst Hrel H).
    inversion Hrel_trace_after as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 Hinvst'' s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply Step_After_External; eauto.
  - destruct Hinv as [Hinvstart [Hinvstep [Hinvinit [Hinvat [Hinvafter Hinvfinal]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final [Hrel_trace_at [Hrel_trace_after Hrel_trace_step]]]].
    specialize (Hrel_trace_init st st'' s2' qb pid Hinvst Hrel H).
    inversion Hrel_trace_init as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 Hinvst'' s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply Step_Initial_Call; eauto.
  - destruct Hinv as [Hinvstart [Hinvstep [Hinvinit [Hinvat [Hinvafter Hinvfinal]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final [Hrel_trace_at [Hrel_trace_after Hrel_trace_step]]]].
    specialize (Hrel_trace_final st st'' s2' rb pid Hinvst Hrel H).
    inversion Hrel_trace_final as [s2'' [Hs2''rel Hs2''valid]].
    specialize (IHHtrace1 Hinvst'' s2'' Hs2''valid).
    inversion IHHtrace1 as [s2 [in_acts' Hs2]].
    eexists; subst; intuition; eauto.
    eapply Step_Final_Return; eauto.
Qed.

Theorem forward_simulation_inv_ind :
  forall (L1 L2 : lts liA liB),
  forall (f : L1.(state) -> L2.(state) -> Prop)
         (inv : L1.(state) -> Prop),
    fsim_properties_inv_ind _ _ f inv ->
    impl_refines L1 L2.
Proof.
  intros L1 L2 f inv Hforward.
  unfold impl_refines.
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

End Simulation.
