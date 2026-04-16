Require Import
  List
  LTS
  Refinement
  Compose
  ComposedRefinement.
Import ListNotations.

Section BSim.

Context {liA liB : language_interface}.
  
Record composed_bsim_properties 
        (L1 : lts li_null liA) (L1' : lts liA liB) (L2 : lts li_null liB) 
        (match_states: composed_lts.state (compose L1 L1') -> state L2 -> Prop) : Prop := {
    bsim_exists:
      forall s1, exists s2, match_states s1 s2;
    bsim_match_new_states:
      forall s1, composed_lts.new_state (compose L1 L1') s1 -> 
      forall s2, match_states s1 s2 -> new_state L2 s2;
    bsim_match_initial_states:
      forall s1 s1' s2' qb pid, match_states s1' s2' -> composed_lts.initial_state (compose L1 L1') s1 pid qb s1' ->
      exists s2, initial_state L2 s2 pid qb s2' /\ match_states s1 s2;
    bsim_match_final_states:
      forall s1 s1' s2' rb pid, match_states s1' s2' -> composed_lts.final_state (compose L1 L1') s1 pid rb s1' ->
      exists s2, final_state L2 s2 pid rb s2' /\ match_states s1 s2;
    bsim_simulation:
      forall s1 s1' s2' int pid, match_states s1' s2' -> composed_lts.step_L1 (compose L1 L1') s1 pid int s1' ->
      exists s2, valid_execution_fragment L2 s2 s2' [] /\ match_states s1 s2;
    bsim_simulation':
      forall s1 s1' s2' int pid, match_states s1' s2' -> composed_lts.step_L2 (compose L1 L1') s1 pid int s1' ->
      exists s2, valid_execution_fragment L2 s2 s2' [] /\ match_states s1 s2;
    bsim_match_internal_query:
      forall s1 s1' s2' qa pid, match_states s1' s2' -> composed_lts.internal_query (compose L1 L1') s1 pid qa s1' ->
      exists s2, valid_execution_fragment L2 s2 s2' [] /\ match_states s1 s2;
    bsim_match_internal_reply:
      forall s1 s1' s2' ra pid, match_states s1' s2' -> composed_lts.internal_reply (compose L1 L1') s1 pid ra s1' ->
      exists s2, valid_execution_fragment L2 s2 s2' [] /\ match_states s1 s2;
  }.

Definition composed_bsim_properties_inv_ind
        (L1 : lts li_null liA) (L1' : lts liA liB) (L2 : lts li_null liB) 
        (match_states: composed_lts.state (compose L1 L1') -> state L2 -> Prop)
        (inv : composed_lts.state (compose L1 L1') -> Prop) : Prop :=
  (composed_lts.invariant_ind _ inv) /\
      (forall s1, inv s1 -> exists s2, match_states s1 s2) /\
      (forall s1, composed_lts.new_state (compose L1 L1') s1 -> 
      forall s2, match_states s1 s2 -> new_state L2 s2) /\
      (forall s1 s1' s2' qb pid, inv s1 -> match_states s1' s2' -> composed_lts.initial_state (compose L1 L1') s1 pid qb s1' ->
      exists s2, initial_state L2 s2 pid qb s2' /\ match_states s1 s2) /\
      (forall s1 s1' s2' rb pid, inv s1 -> match_states s1' s2' -> composed_lts.final_state (compose L1 L1') s1 pid rb s1' ->
      exists s2, final_state L2 s2 pid rb s2' /\ match_states s1 s2) /\
      (forall s1 s1' s2' int pid, inv s1 -> match_states s1' s2' -> composed_lts.step_L1 (compose L1 L1') s1 pid int s1' ->
      exists s2, valid_execution_fragment L2 s2 s2' [] /\ match_states s1 s2) /\
      (forall s1 s1' s2' int pid, inv s1 -> match_states s1' s2' -> composed_lts.step_L2 (compose L1 L1') s1 pid int s1' ->
      exists s2, valid_execution_fragment L2 s2 s2' [] /\ match_states s1 s2) /\
      (forall s1 s1' s2' qa pid, inv s1 -> match_states s1' s2' -> composed_lts.internal_query (compose L1 L1') s1 pid qa s1' ->
      exists s2, valid_execution_fragment L2 s2 s2' [] /\ match_states s1 s2) /\
      (forall s1 s1' s2' ra pid, inv s1 -> match_states s1' s2' -> composed_lts.internal_reply (compose L1 L1') s1 pid ra s1' ->
      exists s2, valid_execution_fragment L2 s2 s2' [] /\ match_states s1 s2)
  .

Lemma composed_backward_simulation_ind_reconstruct: 
  forall (L1 : lts li_null liA) (L1' : lts liA liB) (L2 : lts li_null liB)
    f s1' s1 acts s2',
  composed_bsim_properties _ _ _ f ->
  composed_lts.valid_execution_fragment (compose L1 L1') s1 s1' acts ->
  f s1' s2' ->
  exists s2,
    f s1 s2 /\ valid_execution_fragment L2 s2 s2' (filterB acts).
Proof.
  intros L1 L1' L2 f s1' s1 acts s2'.
  intros Hbackward Htrace1 Hrelinit.
  inversion Hbackward.
  generalize dependent s2'.
  induction Htrace1; subst; eauto; intros s2' Hrel.
  - exists s2'. intuition.
    econstructor; eauto.
  -
    specialize (IHHtrace1 s2' Hrel).
    inversion IHHtrace1 as [s2 [Hs2rel Hs2valid]].
    specialize (bsim_simulation0 st st'' s2 int pid Hs2rel H).
    inversion bsim_simulation0 as [s2'' [Hs2''valid Hs2''rel]].
    eexists; subst; intuition; eauto.
    eapply valid_execution_fragment_join'; eauto.
  -
    specialize (IHHtrace1 s2' Hrel).
    inversion IHHtrace1 as [s2 [Hs2rel Hs2valid]].
    specialize (bsim_simulation'0 st st'' s2 int pid Hs2rel H).
    inversion bsim_simulation'0 as [s2'' [Hs2''valid Hs2''rel]].
    eexists; subst; intuition; eauto.
    eapply valid_execution_fragment_join'; eauto.
  - destruct qa.
  - destruct ra.
  -
    specialize (IHHtrace1 s2' Hrel).
    inversion IHHtrace1 as [s2 [Hs2rel Hs2valid]].
    specialize (bsim_match_initial_states0 st st'' s2 qc pid Hs2rel H).
    inversion bsim_match_initial_states0 as [s2'' [Hs2''valid Hs2''rel]].
    eexists; subst; intuition; eauto.
    eapply Step_Initial_Call; eauto.
  -
    specialize (IHHtrace1 s2' Hrel).
    inversion IHHtrace1 as [s2 [Hs2rel Hs2valid]].
    specialize (bsim_match_final_states0 st st'' s2 rc pid Hs2rel H).
    inversion bsim_match_final_states0 as [s2'' [Hs2''valid Hs2''rel]].
    eexists; subst; intuition; eauto.
    eapply Step_Final_Return; eauto.
  -
    specialize (IHHtrace1 s2' Hrel).
    inversion IHHtrace1 as [s2 [Hs2rel Hs2valid]].
    specialize (bsim_match_internal_query0 st st'' s2 qb pid Hs2rel H).
    inversion bsim_match_internal_query0 as [s2'' [Hs2''valid Hs2''rel]].
    eexists; subst; intuition; eauto.
    simpl.
    eapply valid_execution_fragment_join'; eauto.
  -
    specialize (IHHtrace1 s2' Hrel).
    inversion IHHtrace1 as [s2 [Hs2rel Hs2valid]].
    specialize (bsim_match_internal_reply0 st st'' s2 rb pid Hs2rel H).
    inversion bsim_match_internal_reply0 as [s2'' [Hs2''valid Hs2''rel]].
    eexists; subst; intuition; eauto.
    simpl.
    eapply valid_execution_fragment_join'; eauto.
Qed.

Lemma composed_backward_simulation_inv_ind_reconstruct: 
  forall (L1 : lts li_null liA) (L1' : lts liA liB) (L2 : lts li_null liB)
    f inv s1' s1 acts s2',
  composed_bsim_properties_inv_ind _ _ _ f inv ->
  composed_lts.valid_execution_fragment (compose L1 L1') s1 s1' acts ->
  inv s1 ->
  f s1' s2' ->
  exists s2,
    f s1 s2 /\ valid_execution_fragment L2 s2 s2' (filterB acts).
Proof.
  intros L1 L1' L2 f inv s1' s1 acts s2'.
  intros Hbackward Htrace1 Hrelinit.
  inversion Hbackward as [Hinv [_ [_ Hrel_trace]]].
  generalize dependent s2'.
  induction Htrace1; subst; eauto; intros s2' Hrel.
  - exists s2'. intuition.
    econstructor; eauto.
  - destruct Hinv as [Hinvstart [Hinvstep [Hinvinit [Hinvat [Hinvafter Hinvfinal]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final [Hrel_trace_step [Hrel_trace_query Hrel_trace_reply]]]].
    specialize (IHHtrace1 Hinvst'' s2' Hrel).
    inversion IHHtrace1 as [s2 [Hs2rel Hs2valid]].
    specialize (Hrel_trace_step st st'' s2 int pid Hinvst Hs2rel H).
    inversion Hrel_trace_step as [s2'' [Hs2''valid Hs2''rel]].
    eexists; subst; intuition; eauto.
    eapply valid_execution_fragment_join'; eauto.
  - destruct Hinv as [Hinvstart [Hinvstep [Hinvinit [Hinvat [Hinvafter Hinvfinal]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final [Hrel_trace_step [Hrel_trace_step' [Hrel_trace_query Hrel_trace_reply]]]]].
    specialize (IHHtrace1 Hinvst'' s2' Hrel).
    inversion IHHtrace1 as [s2 [Hs2rel Hs2valid]].
    specialize (Hrel_trace_step' st st'' s2 int pid Hinvst Hs2rel H).
    inversion Hrel_trace_step' as [s2'' [Hs2''valid Hs2''rel]].
    eexists; subst; intuition; eauto.
    eapply valid_execution_fragment_join'; eauto.
  - destruct qa.
  - destruct ra.
  - destruct Hinv as [Hinvstart [Hinvstep [Hinvinit [Hinvat [Hinvafter Hinvfinal]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final [Hrel_trace_step [Hrel_trace_query Hrel_trace_reply]]]].
    specialize (IHHtrace1 Hinvst'' s2' Hrel).
    inversion IHHtrace1 as [s2 [Hs2rel Hs2valid]].
    specialize (Hrel_trace_init st st'' s2 qc pid Hinvst Hs2rel H).
    inversion Hrel_trace_init as [s2'' [Hs2''valid Hs2''rel]].
    eexists; subst; intuition; eauto.
    eapply Step_Initial_Call; eauto.
  - destruct Hinv as [_ [Hinvstep [Hinvstep' [_ [_ [_ [Hinvfinal _]]]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final [Hrel_trace_step [Hrel_trace_query Hrel_trace_reply]]]].
    specialize (IHHtrace1 Hinvst'' s2' Hrel).
    inversion IHHtrace1 as [s2 [Hs2rel Hs2valid]].
    specialize (Hrel_trace_final st st'' s2 rc pid Hinvst Hs2rel H).
    inversion Hrel_trace_final as [s2'' [Hs2''valid Hs2''rel]].
    eexists; subst; intuition; eauto.
    eapply Step_Final_Return; eauto.
  - destruct Hinv as [_ [_ [_ [_ [_ [_ [Hinvfinal [Hinvquery Hinvreply]]]]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final [Hrel_trace_step [Hrel_trace_step' [Hrel_trace_query Hrel_trace_reply]]]]].
    specialize (IHHtrace1 Hinvst'' s2' Hrel).
    inversion IHHtrace1 as [s2 [Hs2rel Hs2valid]].
    specialize (Hrel_trace_query st st'' s2 qb pid Hinvst Hs2rel H).
    inversion Hrel_trace_query as [s2'' [Hs2''valid Hs2''rel]].
    eexists; subst; intuition; eauto.
    simpl.
    eapply valid_execution_fragment_join'; eauto.
  - destruct Hinv as [_ [_ [_ [_ [_ [_ [Hinvfinal [Hinvquery Hinvreply]]]]]]]].
    assert (inv st) as Hinvst by eauto.
    assert (inv st'') as Hinvst'' by eauto.
    destruct Hrel_trace as [Hrel_trace_init [Hrel_trace_final [Hrel_trace_step [Hrel_trace_step' [Hrel_trace_query Hrel_trace_reply]]]]].
    specialize (IHHtrace1 Hinvst'' s2' Hrel).
    inversion IHHtrace1 as [s2 [Hs2rel Hs2valid]].
    specialize (Hrel_trace_reply st st'' s2 rb pid Hinvst Hs2rel H).
    inversion Hrel_trace_reply as [s2'' [Hs2''valid Hs2''rel]].
    eexists; subst; intuition; eauto.
    simpl.
    eapply valid_execution_fragment_join'; eauto.
Qed.

Lemma inv_ind_valid: 
  forall (L : lts li_null liA) (L' : lts liA liB)
    (inv : composed_state L L' -> Prop) s s' acts,
  composed_lts.valid_execution_fragment (compose L L') s s' acts ->
  composed_lts.invariant_ind (compose L L') inv ->
  inv s ->
  inv s'.
Proof.
  intros. induction H.
  - subst. assumption.
  - apply IHvalid_execution_fragment.
    destruct H0 as [Hnew [Hstep [Hinit [_ [_ [Hfinal [Hquery Hreply]]]]]]].
    eapply Hstep; eauto.
  - apply IHvalid_execution_fragment.
    destruct H0 as [Hnew [Hstep [Hstep' [Hinit [_ [_ [Hfinal [Hquery Hreply]]]]]]]].
    eapply Hstep'; eauto.
  - destruct qa.
  - destruct ra.
  - apply IHvalid_execution_fragment.
    destruct H0 as [Hnew [Hstep [Hstep' [Hinit [_ [_ [Hfinal [Hquery Hreply]]]]]]]].
    eapply Hinit; eauto.
  - apply IHvalid_execution_fragment.
    destruct H0 as [Hnew [Hstep [Hstep' [Hinit [_ [_ [Hfinal [Hquery Hreply]]]]]]]].
    eapply Hfinal; eauto.
  - apply IHvalid_execution_fragment.
    destruct H0 as [Hnew [Hstep [Hstep' [Hinit [_ [_ [Hfinal [Hquery Hreply]]]]]]]].
    eapply Hquery; eauto.
  - apply IHvalid_execution_fragment.
    destruct H0 as [Hnew [Hstep [Hstep' [Hinit [_ [_ [Hfinal [Hquery Hreply]]]]]]]].
    eapply Hreply; eauto.
Qed.

Theorem composed_backward_simulation_inv_ind :
  forall (L1 : lts li_null liA) (L1' : lts liA liB) (L2 : lts li_null liB),
  forall (f : composed_lts.state (compose L1 L1') -> L2.(state) -> Prop)
         (inv : composed_lts.state (compose L1 L1') -> Prop),
    composed_bsim_properties_inv_ind _ _ _ f inv ->
    composed_refines_spec (compose L1 L1') L2.
Proof.
  intros L1 L1' L2 f inv Hbackward.
  unfold composed_refines_spec.
  intros acts Htrace1.
  unfold in_traces in *.
  destruct Htrace1 as [s1init [s1final [Hstart1 Hfrag1]]].
  inversion Hbackward as [[Hrel_inv_start _] [Hrel_exists [Hrel_start Htrace]]].
  specialize (Hrel_exists s1final).
  assert (Hinvfinal: inv s1final).
  eapply inv_ind_valid; eauto. inversion Hbackward; intuition.
  specialize (Hrel_exists Hinvfinal).
  inversion Hrel_exists as [s2final Hrels2final].
  assert (inv s1init) as Hinvs1init by eauto.

  pose proof (composed_backward_simulation_inv_ind_reconstruct _ _ _
                f
                inv
                s1final
                s1init
                acts
                s2final
                Hbackward
                Hfrag1
                Hinvs1init
                Hrels2final) as [s2init [in_acts' Hs2init]].
  repeat eexists; intuition; eauto.
Qed.

Theorem composed_backward_simulation_inv_ind' :
  forall (L1 : lts li_null liA) (L1' : lts liA liB) (L2 : lts li_null liB),
  forall (f : composed_lts.state (compose L1 L1') -> L2.(state) -> Prop)
         (inv : composed_lts.state (compose L1 L1') -> Prop),
    composed_bsim_properties_inv_ind _ _ _ f inv ->
    refines (linked_lts (compose L1 L1')) L2.
Proof.
  intros.
  eapply composed_refines_spec_imply_refines; eauto.
  eapply composed_backward_simulation_inv_ind; eauto.
Qed.

End BSim.
