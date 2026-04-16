Require Import
  List
  Nat
  LTS
  Refinement.
Import ListNotations.

(* 
  The idea is try to prove composed_lts preserves refinement
  and linking after composing preserves refinement.
*)

Section ComposedTrace.

Context {liA liB : language_interface}.
Variable L1 : lts li_null liA.
Variable L2 : lts liA liB.

Fixpoint gatherAB (acts : list (@composed_lts.event li_null liA liB)) : list event :=
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
  composed_lts.valid_execution_fragment (raw_compose L1 L2) st st' acts ->
  valid_execution_fragment (L1) st.(RawL1State) st'.(RawL1State) (gatherAB acts).
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
  composed_lts.valid_execution_fragment (raw_compose L1 L2) st st' acts ->
  valid_execution_fragment (L2) st.(RawL2State) st'.(RawL2State) (gatherBC acts).
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
  - destruct qa.
  - destruct ra.
  - eapply Step_Initial_Call; eauto.
    simpl in H. inversion H; subst; simpl; assumption.
  - eapply Step_Final_Return; eauto.
    simpl in H. inversion H; subst; simpl; assumption.
  - eapply Step_At_External; eauto.
    simpl in H. inversion H; subst; simpl; assumption.
  - eapply Step_After_External; eauto.
    simpl in H. inversion H; subst; simpl; assumption.
Qed.

Import LibEnv.

Lemma valid_execution_fragment_com_nil_nil: forall st1 st1' st2 st2',
  valid_execution_fragment (L1) st1 st1' nil ->
  valid_execution_fragment (L2) st2 st2' nil ->
  composed_lts.valid_execution_fragment (raw_compose L1 L2)
          (mkRawComposedState st1 st2) (mkRawComposedState st1' st2') nil.
Proof.
  intros.
  remember [] as acts1.
  remember (@nil (@event liA liB)) as acts2.
  induction H; induction H0; subst; simpl in *; intuition; try (inversion Heqacts1); try (inversion Heqacts2).
  - eapply composed_lts.Step_None; eauto.
  - eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L2; eauto. simpl.
    eapply raw_composed_step_L2_internal; eauto.
    eapply composed_lts.Step_None; eauto.
  - eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    clear H0.
    eapply composed_lts.Step_Internal_L1; eauto. simpl.
    eapply raw_composed_step_L1_internal; eauto.
    eapply composed_lts.Step_None; eauto.
  - eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L1; eauto. simpl.
    eapply raw_composed_step_L1_internal; eauto.
    simpl.
    eapply composed_lts.Step_None; eauto.
Qed.

Import LibEnv.

Lemma valid_execution_fragment_single_right: forall st1 st1' st2 st2' pid qc,
  valid_execution_fragment (L1) st1 st1' nil ->
  valid_execution_fragment (L2) st2 st2' ((pid, event_invB qc) :: nil) ->
  composed_lts.valid_execution_fragment (raw_compose L1 L2)
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
    simpl. eapply raw_composed_step_L2_internal; eauto.
    eapply composed_lts.Step_None; eauto.
  -
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L2 with (pid:=pid0); eauto.
    simpl. eapply raw_composed_step_L2_internal; eauto.
    eapply composed_lts.Step_None; eauto.
  - subst. clear IHvalid_execution_fragment.
    intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto.
    eapply composed_lts.Step_Initial_Call; eauto.
    simpl. eapply raw_composed_initial_state_L2; eauto.
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
    simpl. eapply raw_composed_initial_state_L2; eauto.
    simpl in H3. 
    eapply valid_execution_fragment_com_nil_nil; eauto.
    econstructor; eauto.
    eapply composed_lts.Step_None; eauto.
    reflexivity.
Qed.

Lemma valid_execution_fragment_single_right': forall st1 st1' st2 st2' pid rc,
  valid_execution_fragment (L1) st1 st1' nil ->
  valid_execution_fragment (L2) st2 st2' ((pid, event_resB rc) :: nil) ->
  composed_lts.valid_execution_fragment (raw_compose L1 L2)
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
    simpl. eapply raw_composed_step_L2_internal; eauto.
    eapply composed_lts.Step_None; eauto.
  - 
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L2 with (pid:=pid0); eauto.
    simpl. eapply raw_composed_step_L2_internal; eauto.
    eapply composed_lts.Step_None; eauto.
  - subst. clear IHvalid_execution_fragment.
    intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto.
    eapply composed_lts.Step_Final_Return; eauto.
    simpl. eapply raw_composed_final_state_L2; eauto.
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
    simpl. eapply raw_composed_final_state_L2; eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    econstructor; eauto.
    eapply composed_lts.Step_None; eauto.
    reflexivity.
Qed.

Lemma valid_execution_fragment_single_both: forall st1 st1' st2 st2' pid qb,
  valid_execution_fragment (L1) st1 st1' ((pid, event_invB qb) :: nil) ->
  valid_execution_fragment (L2) st2 st2' ((pid, event_invA qb) :: nil) ->
  composed_lts.valid_execution_fragment (raw_compose L1 L2)
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
    eapply raw_composed_step_L2_push; eauto.
    simpl in H3. intuition.
    eapply valid_execution_fragment_com_nil_nil; eauto.
  - subst.
    eapply composed_lts.Step_Internal_Query; eauto.
    simpl.
    eapply raw_composed_step_L2_push; eauto.
    simpl in H2; intuition.
    eapply valid_execution_fragment_com_nil_nil; eauto.
Qed.

Lemma valid_execution_fragment_single_both': forall st1 st1' st2 st2' pid rb,
  valid_execution_fragment (L1) st1 st1' ((pid, event_resB rb) :: nil) ->
  valid_execution_fragment (L2) st2 st2' ((pid, event_resA rb) :: nil) ->
  composed_lts.valid_execution_fragment (raw_compose L1 L2)
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
    eapply raw_composed_step_L1_pop; eauto.
    simpl in H3. intuition.
    eapply valid_execution_fragment_com_nil_nil; eauto.
  - subst.
    eapply composed_lts.Step_Internal_Reply; eauto.
    simpl.
    eapply raw_composed_step_L1_pop; eauto.
    simpl in H2; intuition.
    eapply valid_execution_fragment_com_nil_nil; eauto.
Qed.

Lemma valid_execution_fragment_join: forall acts st st',
  valid_execution_fragment (L1) st.(RawL1State) st'.(RawL1State) (gatherAB acts) ->
  valid_execution_fragment (L2) st.(RawL2State) st'.(RawL2State) (gatherBC acts) ->
  composed_lts.valid_execution_fragment (raw_compose L1 L2) st st' acts.
Proof.
  induction acts; simpl; intros.
  - destruct st, st'. simpl in *. subst.
    eapply valid_execution_fragment_com_nil_nil; eauto.
  - destruct a. destruct _e; simpl in *.
    -- apply valid_execution_fragment_inv in H0.
      destruct H0 as [st2'' [Hv1 Hv2]].
      assert (valid_execution_fragment (L1)
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
      assert (valid_execution_fragment (L1)
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
      assert (valid_execution_fragment (L1)
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
      assert (valid_execution_fragment (L1)
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
    -- destruct q.
    -- destruct r.
Qed.

End ComposedTrace.

Section Refinement.

Context {liA liB : language_interface}.

Import LibEnv.

Lemma refines_composed_refines : forall (L1 L1' : lts li_null liA) (L2 : lts liA liB),
  refines (L1) (L1') ->
  composed_refines (raw_compose L1 L2) (raw_compose L1' L2).
Proof.
  intros.
  unfold composed_refines. intros.
  unfold refines in H.
  unfold composed_lts.in_traces in H0.
  destruct H0 as [init [final [Hnew Hvalid]]].
  assert (Hvalidtmp : composed_lts.valid_execution_fragment (raw_compose L1 L2) init final c_acts).
  assumption.
  assert (Hvalidtmp' : composed_lts.valid_execution_fragment (raw_compose L1 L2) init final c_acts).
  assumption.
  apply valid_execution_fragment_com in Hvalidtmp.
  apply valid_execution_fragment_com' in Hvalid.
  assert (in_traces (L1') (gatherAB c_acts)).
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
  exists (mkRawComposedState init' RawL2State).
  exists (mkRawComposedState final' RawL2State0).
  intuition.
  unfold raw_composed_new_state. simpl. intuition.
  eapply valid_execution_fragment_join; eauto.
Qed.

End Refinement.
