Require Import
  List
  LTS
  ImplRefinement.
Import ListNotations.

Section RAWCOMPOSITION.
  Context {liA liB liC: language_interface}.
  Variable M1: lts liA liB.
  Variable M2: lts liB liC.

  Record raw_composed_state : Type := mkRawComposedState {
    RawL1State : M1.(state);
    RawL2State : M2.(state);
  }.

  Definition raw_composed_internal_M1 := M1.(internal).
  Definition raw_composed_internal_M2 := M2.(internal).

  Definition raw_composed_new_state lst : Prop :=
    M1.(new_state) lst.(RawL1State) /\ 
    M2.(new_state) lst.(RawL2State).

  Inductive raw_composed_initial_state : raw_composed_state -> Pid -> query liC -> raw_composed_state -> Prop :=
  | raw_composed_initial_state_M2 : forall lst lst' st2 st2' qc st1 pid,
      initial_state M2 st2 pid qc st2' ->
      lst = mkRawComposedState st1 st2 ->
      lst' = mkRawComposedState st1 st2' ->
      raw_composed_initial_state lst pid qc lst'
  .

  Import LibEnv.

  Inductive raw_composed_step_M2 : raw_composed_state -> Pid -> raw_composed_internal_M2 -> raw_composed_state -> Prop :=
  | raw_composed_step_M2_internal : forall st1 st2 st2' act lst lst' pid,
      step M2 st2 pid act st2' ->
      lst = mkRawComposedState st1 st2 ->
      lst' = mkRawComposedState st1 st2' ->
      raw_composed_step_M2 lst pid act lst'.

  Inductive raw_composed_step_M1 : raw_composed_state -> Pid -> raw_composed_internal_M1 -> raw_composed_state -> Prop :=
  | raw_composed_step_M1_internal : forall st1 st2 st1' act lst lst' pid,
      step M1 st1 pid act st1' ->
      lst = mkRawComposedState st1 st2 ->
      lst' = mkRawComposedState st1' st2 ->
      raw_composed_step_M1 lst pid act lst'
  .

  Inductive raw_composed_at_external : raw_composed_state -> Pid -> query liA -> raw_composed_state -> Prop := 
  | raw_composed_at_external_M1 : forall lst lst' st2 qa st1 st1' pid,
      at_external M1 st1 pid qa st1' ->
      lst = mkRawComposedState st1 st2 ->
      lst' = mkRawComposedState st1' st2 ->
      raw_composed_at_external lst pid qa lst'
  .

  Inductive raw_composed_after_external : raw_composed_state -> Pid -> reply liA -> raw_composed_state -> Prop := 
  | raw_composed_after_external_M1 : forall lst lst' st2 ra st1 st1' pid,
      after_external M1 st1 pid ra st1' ->
      lst = mkRawComposedState st1 st2 ->
      lst' = mkRawComposedState st1' st2 ->
      raw_composed_after_external lst pid ra lst'
  .

  Inductive raw_composed_final_state : raw_composed_state -> Pid -> reply liC -> raw_composed_state -> Prop :=
  | raw_composed_final_state_M2 : forall st1 st2 rc st2' lst lst' pid,
      final_state M2 st2 pid rc st2' ->
      lst = mkRawComposedState st1 st2 ->
      lst' = mkRawComposedState st1 st2' ->
      raw_composed_final_state lst pid rc lst'
  .

  Inductive raw_composed_internal_query : raw_composed_state -> Pid -> query liB -> raw_composed_state -> Prop :=
  | raw_composed_step_M2_push : forall st1 st2 st1' qb lst lst' st2' pid,
      at_external M2 st2 pid qb st2' ->
      lst = mkRawComposedState st1 st2 ->
      initial_state M1 st1 pid qb st1' ->
      lst' = mkRawComposedState st1' st2' ->
      raw_composed_internal_query lst pid qb lst'
  .

  Inductive raw_composed_internal_reply : raw_composed_state -> Pid -> reply liB -> raw_composed_state -> Prop :=
  | raw_composed_step_M1_pop : forall st1 st1' rb st2 st2' lst lst' pid,
      final_state M1 st1 pid rb st1' ->
      after_external M2 st2 pid rb st2' ->
      lst = mkRawComposedState st1 st2 ->
      lst' = mkRawComposedState st1' st2' ->
      raw_composed_internal_reply lst pid rb lst'
  .

  Definition raw_compose : composed_lts.composed_lts liA liB liC :=
    composed_lts.mkComposedLTS liA liB liC
      raw_composed_state
      raw_composed_internal_M1
      raw_composed_internal_M2
      raw_composed_step_M1
      raw_composed_step_M2
      raw_composed_new_state
      raw_composed_initial_state
      raw_composed_at_external
      raw_composed_after_external
      raw_composed_final_state
      raw_composed_internal_query
      raw_composed_internal_reply.

End RAWCOMPOSITION.

Arguments RawL1State {liA liB liC M1 M2}.
Arguments RawL2State {liA liB liC M1 M2}.
Arguments raw_compose {liA liB liC}.
Arguments mkRawComposedState {liA liB liC M1 M2}.

Section LINK.

Context {liA liB liC: language_interface}.
Variable L : composed_lts.composed_lts liA liB liC.

Definition linked_state := composed_lts.state L.

Inductive linked_internal : Type :=
| intIntL1 (act : composed_lts.internal_L1 L)
| intIntL2 (act : composed_lts.internal_L2 L)
| intQuery (act : query liB)
| intReply (act : reply liB).

Definition linked_new_state :=
  composed_lts.new_state L.

Definition linked_initial_state := 
  composed_lts.initial_state L.

Import LibEnv.

Inductive linked_step : linked_state -> Pid -> linked_internal -> linked_state -> Prop :=
| linked_step_int_L2 : forall st pid st' int,
  composed_lts.step_L2 L st pid int st' ->
  linked_step st pid (intIntL2 int) st'
| linked_step_int_L1 : forall st pid st' int,
  composed_lts.step_L1 L st pid int st' ->
  linked_step st pid (intIntL1 int) st'
| linked_step_L2_push : forall st pid qb st',
  composed_lts.internal_query L st pid qb st' ->
  linked_step st pid (intQuery qb) st'
| linked_step_L1_pop : forall st pid rb st',
  composed_lts.internal_reply L st pid rb st' ->
  linked_step st pid (intReply rb) st'
.

Definition linked_at_external :=
  composed_lts.at_external L.

Definition linked_after_external := 
  composed_lts.after_external L.

Definition linked_final_state := 
  composed_lts.final_state L.

Definition linked_lts : lts liA liC :=
  mkLTS liA liC linked_state
    linked_internal
    linked_step
    linked_new_state
    linked_initial_state
    linked_at_external
    linked_after_external
    linked_final_state.

End LINK.

Arguments linked_after_external {liA liB liC L}.
Arguments intQuery {liA liB liC L}.
Arguments intReply {liA liB liC L}.

Notation " M ◁ M' " := (linked_lts (ImplRawCompose.raw_compose M M')) (at level 67).

Section ComposedRefinement.

Context {liA liB liC: language_interface}.

Definition impl_composed_refines (L L' : composed_lts.composed_lts liA liB liC) := 
  forall c_acts,
  composed_lts.in_traces L c_acts ->
  composed_lts.in_traces L' c_acts.

Lemma impl_composed_refines_trans: forall (L : composed_lts.composed_lts liA liB liC) L' L'',
  impl_composed_refines L L' ->
  impl_composed_refines L' L'' ->
  impl_composed_refines L L''.
Proof.
  intros.
  unfold impl_composed_refines. intros.
  apply H in H1. apply H0 in H1; intuition.
Qed.

Lemma link_valid_compose_valid: forall (L : composed_lts.composed_lts liA liB liC) st st' acts,
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
  - destruct IHvalid_execution_fragment as
    [c_acts [Hcvalid Hfilter]].
    subst.
    simpl in H.
    exists ((pid, composed_lts.event_invA qa):: c_acts).
    simpl. intuition.
    eapply composed_lts.Step_At_External; eauto.
  - destruct IHvalid_execution_fragment as
    [c_acts [Hcvalid Hfilter]].
    subst.
    simpl in H.
    exists ((pid, composed_lts.event_resA ra):: c_acts).
    simpl. intuition.
    eapply composed_lts.Step_After_External; eauto.
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

Lemma link_in_trace_compose_in_trace : forall (L : composed_lts.composed_lts liA liB liC) acts,
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

Lemma link_preserves_valid_exe: forall (L : composed_lts.composed_lts liA liB liC) st st' acts,
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
  
End ComposedRefinement.

Section ComposedTrace.

Context {liA liB liC : language_interface}.
Variable M1 : lts liA liB.
Variable M2 : lts liB liC.

Fixpoint gatherAB (acts : list (@composed_lts.event liA liB liC)) : list event :=
  match acts with
  | nil => nil
  | (pid, act) :: acts' =>
    let eventsAB' := gatherAB acts' in
    match act with
    | composed_lts.event_invA qa => (pid, event_invA qa) :: eventsAB'
    | composed_lts.event_resA ra => (pid, event_resA ra) :: eventsAB'
    | composed_lts.event_invB qb => (pid, event_invB qb) :: eventsAB'
    | composed_lts.event_resB rb => (pid, event_resB rb) :: eventsAB'
    | _ => eventsAB'
    end
  end.

Lemma valid_execution_fragment_com: forall st st' acts,
  composed_lts.valid_execution_fragment (raw_compose M1 M2) st st' acts ->
  valid_execution_fragment (M1) st.(RawL1State) st'.(RawL1State) (gatherAB acts).
Proof.
  induction 1; simpl; intros.
  - subst. econstructor; eauto.
  - eapply valid_execution_fragment_join' with (a:=[]); eauto.
    clear IHvalid_execution_fragment. clear H0.
    simpl in H. inversion H; subst.
    simpl. eapply Step_Internal; eauto.
    eapply Step_None; eauto.
  - eapply valid_execution_fragment_join' with (a:=[]); eauto.
    clear IHvalid_execution_fragment. clear H0.
    simpl in H. inversion H; subst.
    simpl.
    eapply Step_None; eauto.
  - eapply Step_At_External; eauto.
    simpl in H. inversion H; subst; simpl; assumption.
  - eapply Step_After_External; eauto.
    simpl in H. inversion H; subst; simpl; assumption.
  - eapply valid_execution_fragment_join' with (a:=[]); eauto.
    simpl in H. inversion H; subst; simpl.
    eapply Step_None; eauto.
  - eapply valid_execution_fragment_join' with (a:=[]); eauto.
    simpl in H. inversion H; subst; simpl.
    eapply Step_None; eauto.
  - eapply Step_Initial_Call; eauto.
    simpl in H. inversion H; subst; simpl; assumption.
  - eapply Step_Final_Return; eauto.
    simpl in H. inversion H; subst; simpl; assumption.
Qed.

Lemma valid_execution_fragment_com': forall st st' acts,
  composed_lts.valid_execution_fragment (raw_compose M1 M2) st st' acts ->
  valid_execution_fragment (M2) st.(RawL2State) st'.(RawL2State) (gatherBC acts).
Proof.
  induction 1; simpl; intros.
  - subst. econstructor; eauto.
  - eapply valid_execution_fragment_join' with (a:=[]); eauto.
    clear IHvalid_execution_fragment. clear H0.
    simpl in H. inversion H; subst; simpl.
    eapply Step_None; eauto.
  - eapply valid_execution_fragment_join' with (a:=[]); eauto.
    clear IHvalid_execution_fragment. clear H0.
    simpl in H. inversion H; subst; simpl.
    eapply Step_Internal; eauto.
      eapply Step_None; eauto.
  - eapply valid_execution_fragment_join' with (a:=[]); eauto.
    clear IHvalid_execution_fragment. clear H0.
    simpl in H. inversion H; subst; simpl.
    eapply Step_None; eauto.
  - eapply valid_execution_fragment_join' with (a:=[]); eauto.
    clear IHvalid_execution_fragment. clear H0.
    simpl in H. inversion H; subst; simpl.
    eapply Step_None; eauto.
  - eapply Step_Initial_Call; eauto.
    simpl in H. inversion H; subst; simpl; assumption.
  - eapply Step_Final_Return; eauto.
    simpl in H. inversion H; subst; simpl; assumption.
  - eapply Step_At_External; eauto.
    simpl in H. inversion H; subst; simpl; assumption.
  - eapply Step_After_External; eauto.
    simpl in H. inversion H; subst; simpl; assumption.
Qed.

Lemma valid_execution_fragment_com_nil_nil: forall st1 st1' st2 st2',
  valid_execution_fragment (M1) st1 st1' nil ->
  valid_execution_fragment (M2) st2 st2' nil ->
  composed_lts.valid_execution_fragment (raw_compose M1 M2)
          (mkRawComposedState st1 st2) (mkRawComposedState st1' st2') nil.
Proof.
  intros.
  remember [] as acts1.
  remember (@nil (@event liB liC)) as acts2.
  induction H; induction H0; subst; simpl in *; intuition; try (inversion Heqacts1); try (inversion Heqacts2).
  - eapply composed_lts.Step_None; eauto.
  - eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L2; eauto. simpl.
    eapply raw_composed_step_M2_internal; eauto.
    eapply composed_lts.Step_None; eauto.
  - eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    clear H0.
    eapply composed_lts.Step_Internal_L1; eauto. simpl.
    eapply raw_composed_step_M1_internal; eauto.
    eapply composed_lts.Step_None; eauto.
  - eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L1; eauto. simpl.
    eapply raw_composed_step_M1_internal; eauto.
    simpl.
    eapply composed_lts.Step_None; eauto.
Qed.

Lemma valid_execution_fragment_single_right: forall st1 st1' st2 st2' pid qc,
  valid_execution_fragment (M1) st1 st1' nil ->
  valid_execution_fragment (M2) st2 st2' ((pid, event_invB qc) :: nil) ->
  composed_lts.valid_execution_fragment (raw_compose M1 M2)
    (mkRawComposedState st1 st2) 
    (mkRawComposedState st1' st2')
    ((pid, composed_lts.event_invC qc)::nil).
Proof.
  intros. remember [(pid, event_invB qc)] as acts2.
  remember [] as acts1.
  induction H0; induction H; subst; intuition.
  all : try inversion Heqacts2.
  all : try inversion Heqacts1.
  -
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L2 with (pid:=pid0); eauto.
    simpl. eapply raw_composed_step_M2_internal; eauto.
    eapply composed_lts.Step_None; eauto.
  -
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L2 with (pid:=pid0); eauto.
    simpl. eapply raw_composed_step_M2_internal; eauto.
    eapply composed_lts.Step_None; eauto.
  - subst. clear IHvalid_execution_fragment.
    intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto.
    eapply composed_lts.Step_Initial_Call; eauto.
    simpl. eapply raw_composed_initial_state_M2; eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    econstructor; eauto.
    eapply composed_lts.Step_None; eauto.
    reflexivity.
  - subst. clear IHvalid_execution_fragment.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    eapply Step_Internal; eauto.
    eapply Step_None; eauto.
    2 : { reflexivity. }
    eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto.
    eapply composed_lts.Step_Initial_Call; eauto.
    simpl. eapply raw_composed_initial_state_M2; eauto.
    simpl in H3. 
    eapply valid_execution_fragment_com_nil_nil; eauto.
    econstructor; eauto.
    eapply composed_lts.Step_None; eauto.
    reflexivity.
Qed.

Lemma valid_execution_fragment_single_right': forall st1 st1' st2 st2' pid rc,
  valid_execution_fragment (M1) st1 st1' nil ->
  valid_execution_fragment (M2) st2 st2' ((pid, event_resB rc) :: nil) ->
  composed_lts.valid_execution_fragment (raw_compose M1 M2)
    (mkRawComposedState st1 st2) 
    (mkRawComposedState st1' st2')
    ((pid, composed_lts.event_resC rc)::nil).
Proof.
  intros. remember [(pid, event_resB rc)] as acts2.
  remember [] as acts1.
  induction H0; induction H; subst; intuition.
  all : try inversion Heqacts2.
  all : try inversion Heqacts1.
  -
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L2 with (pid:=pid0); eauto.
    simpl. eapply raw_composed_step_M2_internal; eauto.
    eapply composed_lts.Step_None; eauto.
  - 
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L2 with (pid:=pid0); eauto.
    simpl. eapply raw_composed_step_M2_internal; eauto.
    eapply composed_lts.Step_None; eauto.
  - subst. clear IHvalid_execution_fragment.
    intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto.
    eapply composed_lts.Step_Final_Return; eauto.
    simpl. eapply raw_composed_final_state_M2; eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    econstructor; eauto.
    eapply composed_lts.Step_None; eauto.
    reflexivity.
  - subst. clear IHvalid_execution_fragment.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    eapply Step_Internal; eauto.
    eapply Step_None; eauto.
    2 : { reflexivity. }
    eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto.
    eapply composed_lts.Step_Final_Return; eauto.
    simpl. eapply raw_composed_final_state_M2; eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    econstructor; eauto.
    eapply composed_lts.Step_None; eauto.
    reflexivity.
Qed.

Lemma valid_execution_fragment_single_both: forall st1 st1' st2 st2' pid qb,
  valid_execution_fragment (M1) st1 st1' ((pid, event_invB qb) :: nil) ->
  valid_execution_fragment (M2) st2 st2' ((pid, event_invA qb) :: nil) ->
  composed_lts.valid_execution_fragment (raw_compose M1 M2)
    (mkRawComposedState st1 st2)
    (mkRawComposedState st1' st2')
    ((pid, composed_lts.event_invB qb)::nil).
Proof.
  intros. remember [(pid, event_invB qb)] as acts1.
  remember [(pid, event_invA qb)] as acts2.
  induction H0; induction H; subst; intuition.
  all : try inversion Heqacts2.
  all : try inversion Heqacts1.
  - 
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    eapply Step_None; eauto.
    eapply Step_Internal; eauto.
    eapply Step_None; eauto.
  - 
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    eapply Step_None; eauto.
    eapply Step_Internal; eauto.
    eapply Step_None; eauto.
  - subst.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    eapply Step_Internal; eauto.
    eapply Step_None; eauto.
    eapply Step_None; eauto.
    2 : { reflexivity. }
    clear IHvalid_execution_fragment.
    apply valid_execution_fragment_inv1 in H2.
    destruct H2 as [st1'' [st1''' [Hv1 [Hinit1 Hv2]]]].
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    eapply Step_None; eauto.
    2 : { simpl. reflexivity. }
    eapply composed_lts.Step_Internal_Query; eauto.
    simpl.
    eapply raw_composed_step_M2_push; eauto.
    simpl in H3. intuition.
    eapply valid_execution_fragment_com_nil_nil; eauto.
  - subst.
    eapply composed_lts.Step_Internal_Query; eauto.
    simpl.
    eapply raw_composed_step_M2_push; eauto.
    simpl in H2; intuition.
    eapply valid_execution_fragment_com_nil_nil; eauto.
Qed.

Lemma valid_execution_fragment_single_both': forall st1 st1' st2 st2' pid rb,
  valid_execution_fragment (M1) st1 st1' ((pid, event_resB rb) :: nil) ->
  valid_execution_fragment (M2) st2 st2' ((pid, event_resA rb) :: nil) ->
  composed_lts.valid_execution_fragment (raw_compose M1 M2)
    (mkRawComposedState st1 st2)
    (mkRawComposedState st1' st2')
    ((pid, composed_lts.event_resB rb)::nil).
Proof.
  intros. remember [(pid, event_resB rb)] as acts1.
  remember [(pid, event_resA rb)] as acts2.
  induction H0; induction H; subst; intuition.
  all : try inversion Heqacts2.
  all : try inversion Heqacts1.
  - 
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    eapply Step_None; eauto.
    eapply Step_Internal; eauto.
    eapply Step_None; eauto.
  - 
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    eapply Step_None; eauto.
    eapply Step_Internal; eauto.
    eapply Step_None; eauto.
  - subst.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    eapply Step_Internal; eauto.
    eapply Step_None; eauto.
    eapply Step_None; eauto.
    2 : { reflexivity. }
    clear IHvalid_execution_fragment.
    apply valid_execution_fragment_inv1' in H2.
    destruct H2 as [st1'' [st1''' [Hv1 [Hinit1 Hv2]]]].
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    eapply Step_None; eauto.
    2 : { simpl. reflexivity. }
    eapply composed_lts.Step_Internal_Reply; eauto.
    simpl.
    eapply raw_composed_step_M1_pop; eauto.
    simpl in H3. intuition.
    eapply valid_execution_fragment_com_nil_nil; eauto.
  - subst.
    eapply composed_lts.Step_Internal_Reply; eauto.
    simpl.
    eapply raw_composed_step_M1_pop; eauto.
    simpl in H2; intuition.
    eapply valid_execution_fragment_com_nil_nil; eauto.
Qed.

Lemma valid_execution_fragment_single_left: forall st1 st1' st2 st2' pid qc,
  valid_execution_fragment (M1) st1 st1' ((pid, event_invA qc) :: nil) ->
  valid_execution_fragment (M2) st2 st2' nil ->
  composed_lts.valid_execution_fragment (raw_compose M1 M2)
    (mkRawComposedState st1 st2) 
    (mkRawComposedState st1' st2')
    ((pid, composed_lts.event_invA qc)::nil).
Proof.
  intros.
  remember [(pid, event_invA qc)] as acts1.
  remember (@nil (@event liB liC)) as acts2.
  induction H; induction H0; subst; intuition.
  all : try inversion Heqacts2.
  all : try inversion Heqacts1.
  -
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L1 with (pid:=pid0); eauto.
    simpl. eapply raw_composed_step_M1_internal; eauto.
    eapply composed_lts.Step_None; eauto.
  -
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L1 with (pid:=pid0); eauto.
    simpl. eapply raw_composed_step_M1_internal; eauto.
    eapply composed_lts.Step_None; eauto.
  - subst. clear IHvalid_execution_fragment.
    intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto.
    eapply composed_lts.Step_At_External; eauto.
    simpl. eapply raw_composed_at_external_M1; eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    econstructor; eauto.
    eapply composed_lts.Step_None; eauto.
    reflexivity.
  - subst. clear IHvalid_execution_fragment.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    (* eapply Step_Internal; eauto. *)
    eapply Step_None; eauto.
    eapply Step_Internal; eauto.
    2 : { reflexivity. }
    eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto.
    eapply composed_lts.Step_At_External; eauto.
    simpl. eapply raw_composed_at_external_M1; eauto.
    simpl in H3. 
    eapply valid_execution_fragment_com_nil_nil; eauto.
    econstructor; eauto.
    eapply composed_lts.Step_None; eauto.
    reflexivity.
Qed.

Lemma valid_execution_fragment_single_left': forall st1 st1' st2 st2' pid rc,
  valid_execution_fragment (M1) st1 st1' ((pid, event_resA rc) :: nil) ->
  valid_execution_fragment (M2) st2 st2' nil ->
  composed_lts.valid_execution_fragment (raw_compose M1 M2)
    (mkRawComposedState st1 st2) 
    (mkRawComposedState st1' st2')
    ((pid, composed_lts.event_resA rc)::nil).
Proof.
  intros.
  remember [(pid, event_resA rc)] as acts1.
  remember (@nil (@event liB liC)) as acts2.
  induction H; induction H0; subst; intuition.
  all : try inversion Heqacts2.
  all : try inversion Heqacts1.
  -
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L1 with (pid:=pid0); eauto.
    simpl. eapply raw_composed_step_M1_internal; eauto.
    eapply composed_lts.Step_None; eauto.
  -
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L1 with (pid:=pid0); eauto.
    simpl. eapply raw_composed_step_M1_internal; eauto.
    eapply composed_lts.Step_None; eauto.
  - subst. clear IHvalid_execution_fragment.
    intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto.
    eapply composed_lts.Step_After_External; eauto.
    simpl. eapply raw_composed_after_external_M1; eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    econstructor; eauto.
    eapply composed_lts.Step_None; eauto.
    reflexivity.
  - subst. clear IHvalid_execution_fragment.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    (* eapply Step_Internal; eauto. *)
    eapply Step_None; eauto.
    eapply Step_Internal; eauto.
    2 : { reflexivity. }
    eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto.
    eapply composed_lts.Step_After_External; eauto.
    simpl. eapply raw_composed_after_external_M1; eauto.
    simpl in H3. 
    eapply valid_execution_fragment_com_nil_nil; eauto.
    econstructor; eauto.
    eapply composed_lts.Step_None; eauto.
    reflexivity.
Qed.

Lemma valid_execution_fragment_join: forall acts st st',
  valid_execution_fragment (M1) st.(RawL1State) st'.(RawL1State) (gatherAB acts) ->
  valid_execution_fragment (M2) st.(RawL2State) st'.(RawL2State) (gatherBC acts) ->
  composed_lts.valid_execution_fragment (raw_compose M1 M2) st st' acts.
Proof.
  induction acts; simpl; intros.
  - destruct st, st'. simpl in *. subst.
    eapply valid_execution_fragment_com_nil_nil; eauto.
  - destruct a. destruct _e; simpl in *.
    -- apply valid_execution_fragment_inv in H0.
      destruct H0 as [st2'' [Hv1 Hv2]].
      assert (valid_execution_fragment (M1)
        (RawL1State (mkRawComposedState 
                    (RawL1State st) st2''))
        (RawL1State st')
        (gatherAB acts)).
      simpl. assumption.
      apply IHacts in H0; auto.
      eapply composed_lts.valid_execution_fragment_join' with (a:=[(n, composed_lts.event_invC q)]); eauto.
      clear H0. destruct st. simpl in *.
      eapply valid_execution_fragment_single_right; eauto.
      intuition.
      eapply Step_None; eauto.
    -- apply valid_execution_fragment_inv in H0.
      destruct H0 as [st2'' [Hv1 Hv2]].
      assert (valid_execution_fragment (M1)
        (RawL1State (mkRawComposedState 
                    (RawL1State st) st2''))
        (RawL1State st')
        (gatherAB acts)).
      simpl. assumption.
      apply IHacts in H0; auto.
      eapply composed_lts.valid_execution_fragment_join' with (a:=[(n, composed_lts.event_resC r)]); eauto.
      clear H0. destruct st. simpl in *.
      eapply valid_execution_fragment_single_right'; eauto.
      intuition.
      eapply Step_None; eauto.
    -- apply valid_execution_fragment_inv in H0.
      apply valid_execution_fragment_inv in H.
      destruct H0 as [st2'' [Hv1 Hv2]].
      destruct H as [st1'' [Hv11 Hv21]].
      assert (valid_execution_fragment (M1)
        (RawL1State (mkRawComposedState 
                    st1'' st2''))
        (RawL1State st')
        (gatherAB acts)).
      simpl. assumption.
      apply IHacts in H; auto.
      eapply composed_lts.valid_execution_fragment_join' with (a:=[(n, composed_lts.event_invB q)]); eauto.
      clear H.
      destruct st. simpl in *.
      eapply valid_execution_fragment_single_both; eauto.
    -- apply valid_execution_fragment_inv in H0.
      apply valid_execution_fragment_inv in H.
      destruct H0 as [st2'' [Hv1 Hv2]].
      destruct H as [st1'' [Hv11 Hv21]].
      assert (valid_execution_fragment (M1)
        (RawL1State (mkRawComposedState 
                    st1'' st2''))
        (RawL1State st')
        (gatherAB acts)).
      simpl. assumption.
      apply IHacts in H; auto.
      eapply composed_lts.valid_execution_fragment_join' with (a:=[(n, composed_lts.event_resB r)]); eauto.
      clear H.
      destruct st.
      intuition.
      eapply valid_execution_fragment_single_both'; eauto.
    -- apply valid_execution_fragment_inv in H.
      destruct H as [st1'' [Hv1 Hv2]].
      assert (valid_execution_fragment (M2)
        (RawL2State (mkRawComposedState 
                    st1'' (RawL2State st)))
        (RawL2State st')
        (gatherBC acts)).
      simpl. assumption.
      apply IHacts in H; auto.
      eapply composed_lts.valid_execution_fragment_join' with (a:=[(n, composed_lts.event_invA q)]); eauto.
      clear H0. destruct st. simpl in *.
      eapply valid_execution_fragment_single_left; eauto.
      intuition.
      eapply Step_None; eauto.
    -- apply valid_execution_fragment_inv in H.
      destruct H as [st1'' [Hv1 Hv2]].
      assert (valid_execution_fragment (M2)
        (RawL2State (mkRawComposedState 
                    st1'' (RawL2State st)))
        (RawL2State st')
        (gatherBC acts)).
      simpl. assumption.
      apply IHacts in H; auto.
      eapply composed_lts.valid_execution_fragment_join' with (a:=[(n, composed_lts.event_resA r)]); eauto.
      clear H0. destruct st. simpl in *.
      eapply valid_execution_fragment_single_left'; eauto.
      intuition.
      eapply Step_None; eauto.
Qed.

End ComposedTrace.

Section RAWCOMPOSE.

Context {liA liB liC : language_interface}.

Lemma link_preserves_in_traces : forall (L : composed_lts.composed_lts liA liB liC) acts,
  composed_lts.in_traces L acts ->
  in_traces (linked_lts L) (filterB acts).
Proof.
  intros. unfold in_traces.
  unfold composed_lts.in_traces in H.
  destruct H as [init [final [Hnew Hvalid]]].
  eapply link_preserves_valid_exe in Hvalid.
  exists init, final. intuition.
Qed.

Lemma link_preserves_impl_composed_refines: forall (M1 M2 : composed_lts.composed_lts liA liB liC),
  impl_composed_refines M1 M2 ->
  impl_refines (linked_lts M1) (linked_lts M2).
Proof.
  intros. unfold impl_refines. intros.
  apply link_in_trace_compose_in_trace in H0.
  destruct H0 as [c_acts [Hcin_trace Hfilter]].
  apply H in Hcin_trace. subst.
  eapply link_preserves_in_traces. assumption.
Qed.

Lemma impl_refines_composed_refines : forall (M1 M1' : lts liA liB) (M2 : lts liB liC),
  impl_refines (M1) (M1') ->
  impl_composed_refines (raw_compose M1 M2) (raw_compose M1' M2).
Proof.
  intros.
  unfold impl_composed_refines. intros.
  unfold impl_refines in H.
  unfold composed_lts.in_traces in H0.
  destruct H0 as [init [final [Hnew Hvalid]]].
  assert (Hvalidtmp : composed_lts.valid_execution_fragment (raw_compose M1 M2) init final c_acts).
  assumption.
  assert (Hvalidtmp' : composed_lts.valid_execution_fragment (raw_compose M1 M2) init final c_acts).
  assumption.
  apply valid_execution_fragment_com in Hvalidtmp.
  apply valid_execution_fragment_com' in Hvalid.
  assert (in_traces (M1') (gatherAB c_acts)).
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
  exists (mkRawComposedState init' RawL2State0).
  exists (mkRawComposedState final' RawL2State1).
  intuition.
  unfold raw_composed_new_state. simpl. intuition.
  eapply valid_execution_fragment_join; eauto.
Qed.

Lemma impl_refines_impl_composed_refines : forall (M1 : lts liA liB) (M2 M2' : lts liB liC),
  impl_refines (M2) (M2') ->
  impl_composed_refines (raw_compose M1 M2) (raw_compose M1 M2').
Proof.
  intros.
  unfold impl_composed_refines. intros.
  unfold impl_refines in H.
  unfold composed_lts.in_traces in H0.
  destruct H0 as [init [final [Hnew Hvalid]]].
  assert (Hvalidtmp : composed_lts.valid_execution_fragment (raw_compose M1 M2) init final c_acts).
  assumption.
  assert (Hvalidtmp' : composed_lts.valid_execution_fragment (raw_compose M1 M2) init final c_acts).
  assumption.
  apply valid_execution_fragment_com in Hvalidtmp.
  apply valid_execution_fragment_com' in Hvalid.
  assert (in_traces (M2') (gatherBC c_acts)).
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
  exists (mkRawComposedState RawL1State0 init').
  exists (mkRawComposedState RawL1State1 final').
  intuition.
  unfold raw_composed_new_state. simpl. intuition.
  eapply valid_execution_fragment_join; eauto.
Qed.

End RAWCOMPOSE.