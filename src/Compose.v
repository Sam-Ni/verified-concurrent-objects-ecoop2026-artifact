Require Import
	List
  Nat
  Arith
  LibVar
	LTS
	Refinement
  SyncLTS.
Require LibEnv.
Import ListNotations.

Section COMPOSITION.
  Context {liA liB: language_interface}.
  Variable _L1: lts li_null liA.
  Variable _L2: lts liA liB.

  Definition L1 := sync _L1.
  Definition L2 := sync _L2.

  Record composed_state : Type := mkComposedState {
    L1State : L1.(state);
    L2State : L2.(state);
  }.

  Definition composed_internal_L1 := L1.(internal).
  Definition composed_internal_L2 := L2.(internal).

  Definition composed_new_state lst : Prop :=
    L1.(new_state) lst.(L1State) /\ 
    L2.(new_state) lst.(L2State).

  Import LibEnv.

  Inductive composed_initial_state : composed_state -> Pid -> query liB -> composed_state -> Prop :=
  | composed_initial_state_L2 : forall lst lst' st2 st2' qc st1 pid
      (Hnotin: pid # st1.(PidPos)),
      initial_state L2 st2 pid qc st2' ->
      lst = mkComposedState st1 st2 ->
      lst' = mkComposedState st1 st2' ->
      composed_initial_state lst pid qc lst'
  .

  Inductive composed_step_L2 : composed_state -> Pid -> composed_internal_L2 -> composed_state -> Prop :=
  | composed_step_L2_internal : forall st1 st2 st2' act lst lst' pid
      (Hnotin: pid # st1.(PidPos)),
      step L2 st2 pid act st2' ->
      lst = mkComposedState st1 st2 ->
      lst' = mkComposedState st1 st2' ->
      composed_step_L2 lst pid act lst'.

  Inductive composed_step_L1 : composed_state -> Pid -> composed_internal_L1 -> composed_state -> Prop :=
  | composed_step_L1_internal : forall st1 st2 st1' act lst lst' pid
      (Hbinds: binds pid Wait st2.(PidPos)),
      step L1 st1 pid act st1' ->
      lst = mkComposedState st1 st2 ->
      lst' = mkComposedState st1' st2 ->
      composed_step_L1 lst pid act lst'.

  Inductive composed_at_external : composed_state -> Pid -> query li_null -> composed_state -> Prop := .

  Inductive composed_after_external : composed_state -> Pid -> reply li_null -> composed_state -> Prop := .

  Inductive composed_final_state : composed_state -> Pid -> reply liB -> composed_state -> Prop :=
  | composed_final_state_L2 : forall st1 st2 rc st2' lst lst' pid
      (Hnotin: pid # st1.(PidPos)),
      final_state L2 st2 pid rc st2' ->
      lst = mkComposedState st1 st2 ->
      lst' = mkComposedState st1 st2' ->
      composed_final_state lst pid rc lst'
  .

  Inductive composed_internal_query : composed_state -> Pid -> query liA -> composed_state -> Prop :=
  | composed_step_L2_push : forall st1 st2 st1' qb lst lst' st2' pid,
      at_external L2 st2 pid qb st2' ->
      initial_state L1 st1 pid qb st1' ->
      lst = mkComposedState st1 st2 ->
      lst' = mkComposedState st1' st2' ->
      composed_internal_query lst pid qb lst'
  .

  Inductive composed_internal_reply : composed_state -> Pid -> reply liA -> composed_state -> Prop :=
  | composed_step_L1_pop : forall st1 st1' rb st2 st2' lst lst' pid,
      final_state L1 st1 pid rb st1' ->
      after_external L2 st2 pid rb st2' ->
      lst = mkComposedState st1 st2 ->
      lst' = mkComposedState st1' st2' ->
      composed_internal_reply lst pid rb lst'
  .

  Definition compose : composed_lts.composed_lts li_null liA liB :=
    composed_lts.mkComposedLTS li_null liA liB
      composed_state
      composed_internal_L1
      composed_internal_L2
      composed_step_L1
      composed_step_L2
      composed_new_state
      composed_initial_state
      composed_at_external
      composed_after_external
      composed_final_state
      composed_internal_query
      composed_internal_reply.

End COMPOSITION.

Arguments L1State {liA liB _L1 _L2}.
Arguments L2State {liA liB _L1 _L2}.
Arguments mkComposedState {liA liB _L1 _L2}.

Notation " L ‖-' M " := (compose L M) (at level 67).

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
  composed_lts.valid_execution_fragment (compose L1 L2) st st' acts ->
  valid_execution_fragment (sync L1) st.(L1State) st'.(L1State) (gatherAB acts).
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
  composed_lts.valid_execution_fragment (compose L1 L2) st st' acts ->
  valid_execution_fragment (sync L2) st.(L2State) st'.(L2State) (gatherBC acts).
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

Definition disjoint (pos1 : env Position) (pos2 : env Position) :=
  forall pid,
  (binds pid Run pos1 ->
  binds pid Wait pos2) /\
  (binds pid Run pos2 ->
  pid # pos1).

Lemma disjoint_push_r_run: forall pos1 pos2 pid,
  disjoint pos1 pos2 ->
  pid # pos1 ->
  disjoint pos1 ((pid, Run) :: pos2).
Proof.
  intros. unfold disjoint in *.
  intros. intuition.
  - unfold binds. simpl.
    destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst. apply binds_in in H1.
      unfold "#" in H0.
      intuition.
    -- apply H in H1; intuition.
  - unfold binds in H1.
    simpl in H1.
    destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst. assumption.
    -- apply H in H1. assumption.
Qed.

Lemma disjoint_remove_r: forall pos1 pos2 pid,
  disjoint pos1 pos2 ->
  pid # pos1 ->
  disjoint pos1 (remove pos2 pid).
Proof.
  intros. unfold disjoint in *.
  intros. intuition.
  - destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst.
      apply binds_in in H1.
      unfold "#" in H0. intuition.
    -- apply Nat.eqb_neq in Heq.
      apply remove_neq_preserves_binds; auto.
      apply H in H1; intuition.
  - destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst. assumption.
    -- apply Nat.eqb_neq in Heq.
      apply remove_preserves_binds_notin in H1; auto.
      apply H in H1; intuition.
Qed.

Lemma disjoint_push_l_run_r_wait_remove : forall pos1 pos2 pid,
  disjoint pos1 pos2 ->
  disjoint ((pid, Run) :: pos1)
    ((pid, Wait) :: remove pos2 pid).
Proof.
  intros. unfold disjoint in *.
  intros. intuition.
  - unfold binds.
    unfold binds in H0. 
    simpl in *.
    destruct (pid0 =? pid)eqn:Heq.
    -- reflexivity.
    -- apply H in H0.
      apply Nat.eqb_neq in Heq; intuition.
      eapply remove_neq_preserves_binds; eauto.
  - unfold binds in H0.
    unfold "#". simpl in *.
    apply notin_union.
    destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst. discriminate.
    -- apply Nat.eqb_neq in Heq.
      intuition.
      apply notin_neq; intuition.
      apply remove_preserves_binds_notin in H0; auto.
      apply H in H0; intuition.
Qed.

Lemma disjoint_remove_l_r_run_remove : forall pos1 pos2 pid,
  disjoint pos1 pos2 ->
  ok pos1 ->
  disjoint (remove pos1 pid)
    ((pid, Run) :: remove pos2 pid).
Proof.
  intros. unfold disjoint in *.
  intros. intuition.
  - unfold binds. simpl.
    destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst.
      assert (pid # (remove pos1 pid)).
      apply ok_remove_notin; auto.
      apply binds_in in H1.
      unfold "#" in H2.
      intuition.
    -- apply Nat.eqb_neq in Heq.
      apply remove_preserves_binds_notin in H1; auto.
      apply H in H1; intuition.
      apply remove_neq_preserves_binds; auto.
  - unfold binds in H1. simpl in H1.
    destruct (pid0 =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst.
      apply ok_remove_notin; auto.
    -- apply Nat.eqb_neq in Heq.
      eapply remove_preserves_binds_notin in H1; eauto.
      apply H in H1.
      apply remove_preserves_notin; auto.
Qed.

Lemma valid_execution_fragment_com_nil_nil: forall st1 st1' st2 st2',
  valid_execution_fragment (sync L1) st1 st1' nil ->
  valid_execution_fragment (sync L2) st2 st2' nil ->
  disjoint (st1.(PidPos)) (st2.(PidPos)) ->
  composed_lts.valid_execution_fragment (compose L1 L2)
          (mkComposedState st1 st2) (mkComposedState st1' st2') nil.
Proof.
  intros.
  remember [] as acts1.
  remember (@nil (@event liA liB)) as acts2.
  induction H; induction H0; subst; simpl in *; intuition; try (inversion Heqacts1); try (inversion Heqacts2).
  - eapply composed_lts.Step_None; eauto.
  - inversion H0; subst. simpl in *.
    intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L2; eauto. simpl.
    eapply composed_step_L2_internal; eauto.
    apply H1 in Hbinds. assumption.
    eapply composed_lts.Step_None; eauto.
  -  inversion H; subst. simpl in *.
    specialize (H0 H1).
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    clear H0.
    eapply composed_lts.Step_Internal_L1; eauto. simpl.
    eapply composed_step_L1_internal; eauto.
    apply H1 in Hbinds; intuition.
    eapply composed_lts.Step_None; eauto.
  - inversion H; subst.
    inversion H0; subst. simpl in *.
    intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L1; eauto. simpl.
    eapply composed_step_L1_internal; eauto.
    simpl.
    apply H1 in Hbinds; intuition.
    eapply composed_lts.Step_None; eauto.
Qed.

Import LibEnv.

Lemma valid_execution_fragment_single_right: forall st1 st1' st2 st2' pid qc
  (Hnotin: pid # st1.(PidPos)),
  valid_execution_fragment (sync L1) st1 st1' nil ->
  valid_execution_fragment (sync L2) st2 st2' ((pid, event_invB qc) :: nil) ->
  disjoint (st1.(PidPos)) (st2.(PidPos)) ->
  composed_lts.valid_execution_fragment (compose L1 L2)
    (mkComposedState st1 st2) 
    (mkComposedState st1' st2')
    ((pid, composed_lts.event_invC qc)::nil).
Proof.
  intros. remember [(pid, event_invB qc)] as acts2.
  remember [] as acts1.
  induction H0; induction H; subst; intuition.
  all : try inversion Heqacts2.
  all : try inversion Heqacts1.
  - inversion H0; subst. simpl in *.
    intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L2 with (pid:=pid0); eauto.
    simpl. eapply composed_step_L2_internal; eauto.
    apply H1 in Hbinds; intuition.
    eapply composed_lts.Step_None; eauto.
  - inversion H0; subst. simpl in *.
    intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L2 with (pid:=pid0); eauto.
    simpl. eapply composed_step_L2_internal; eauto.
    apply H1 in Hbinds; intuition.
    eapply composed_lts.Step_None; eauto.
  - subst. clear IHvalid_execution_fragment.
    intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto.
    eapply composed_lts.Step_Initial_Call; eauto.
    simpl. eapply composed_initial_state_L2; eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    econstructor; eauto.
    inversion H0; subst. simpl in *.
    apply disjoint_push_r_run; auto.
    eapply composed_lts.Step_None; eauto.
    reflexivity.
  - subst. clear IHvalid_execution_fragment.
    inversion H; subst. simpl in *. intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    eapply Step_Internal; eauto.
    eapply Step_None; eauto.
    2 : { reflexivity. }
    eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto.
    eapply composed_lts.Step_Initial_Call; eauto.
    simpl. eapply composed_initial_state_L2; eauto.
    apply valid_execution_fragment_pos in H3.
    simpl in H3. rewrite <-H3.
    assumption.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    econstructor; eauto.
    apply valid_execution_fragment_pos in H3.
    simpl in H3. rewrite <-H3.
    inversion H0; subst. simpl in *.
    apply disjoint_push_r_run; auto.
    eapply composed_lts.Step_None; eauto.
    reflexivity.
Qed.

Lemma valid_execution_fragment_single_right': forall st1 st1' st2 st2' pid rc
  (Hnotin: pid # st1.(PidPos)),
  valid_execution_fragment (sync L1) st1 st1' nil ->
  valid_execution_fragment (sync L2) st2 st2' ((pid, event_resB rc) :: nil) ->
  disjoint (st1.(PidPos)) (st2.(PidPos)) ->
  composed_lts.valid_execution_fragment (compose L1 L2)
    (mkComposedState st1 st2) 
    (mkComposedState st1' st2')
    ((pid, composed_lts.event_resC rc)::nil).
Proof.
  intros. remember [(pid, event_resB rc)] as acts2.
  remember [] as acts1.
  induction H0; induction H; subst; intuition.
  all : try inversion Heqacts2.
  all : try inversion Heqacts1.
  - inversion H0; subst. simpl in *.
    intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L2 with (pid:=pid0); eauto.
    simpl. eapply composed_step_L2_internal; eauto.
    apply H1 in Hbinds; intuition.
    eapply composed_lts.Step_None; eauto.
  - inversion H0; subst. simpl in *.
    intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply composed_lts.Step_Internal_L2 with (pid:=pid0); eauto.
    simpl. eapply composed_step_L2_internal; eauto.
    apply H1 in Hbinds; intuition.
    eapply composed_lts.Step_None; eauto.
  - subst. clear IHvalid_execution_fragment.
    intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto.
    eapply composed_lts.Step_Final_Return; eauto.
    simpl. eapply composed_final_state_L2; eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    econstructor; eauto.
    inversion H0; subst. simpl in *.
    apply disjoint_remove_r; auto.
    eapply composed_lts.Step_None; eauto.
    reflexivity.
  - subst. clear IHvalid_execution_fragment.
    inversion H; subst. simpl in *. intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    eapply Step_Internal; eauto.
    eapply Step_None; eauto.
    2 : { reflexivity. }
    eapply composed_lts.valid_execution_fragment_join' with (a':=[]); eauto.
    eapply composed_lts.Step_Final_Return; eauto.
    simpl. eapply composed_final_state_L2; eauto.
    apply valid_execution_fragment_pos in H3.
    simpl in H3. rewrite <-H3.
    assumption.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    econstructor; eauto.
    apply valid_execution_fragment_pos in H3.
    simpl in H3. rewrite <-H3.
    inversion H0; subst. simpl in *.
    apply disjoint_remove_r; auto.
    eapply composed_lts.Step_None; eauto.
    reflexivity.
Qed.

Lemma valid_execution_fragment_single_both: forall st1 st1' st2 st2' pid qb,
  valid_execution_fragment (sync L1) st1 st1' ((pid, event_invB qb) :: nil) ->
  valid_execution_fragment (sync L2) st2 st2' ((pid, event_invA qb) :: nil) ->
  disjoint (st1.(PidPos)) (st2.(PidPos)) ->
  composed_lts.valid_execution_fragment (compose L1 L2)
    (mkComposedState st1 st2)
    (mkComposedState st1' st2')
    ((pid, composed_lts.event_invB qb)::nil).
Proof.
  intros. remember [(pid, event_invB qb)] as acts1.
  remember [(pid, event_invA qb)] as acts2.
  induction H0; induction H; subst; intuition.
  all : try inversion Heqacts2.
  all : try inversion Heqacts1.
  - inversion H0; subst. simpl in *. intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    eapply Step_None; eauto.
    eapply Step_Internal; eauto.
    eapply Step_None; eauto.
  - inversion H0; subst. simpl in *. intuition.
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
    apply valid_execution_fragment_inv1 in H3.
    destruct H3 as [st1'' [st1''' [Hv1 [Hinit1 Hv2]]]].
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    eapply Step_None; eauto.
    3 : { simpl. reflexivity. }
    inversion H; subst. simpl in *.
    assumption.
    inversion H; subst. simpl in *. subst.
    eapply composed_lts.Step_Internal_Query; eauto.
    simpl.
    eapply composed_step_L2_push; eauto.
    simpl in H3. intuition.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    inversion H0; subst. simpl in *.
    clear H5.
    inversion Hinit1; subst.
    simpl in *.
    apply valid_execution_fragment_pos in Hv1.
    simpl in Hv1. subst.
    apply disjoint_push_l_run_r_wait_remove; auto.
  - subst.
    eapply composed_lts.Step_Internal_Query; eauto.
    simpl.
    eapply composed_step_L2_push; eauto.
    simpl in H3; intuition.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    clear IHvalid_execution_fragment.
    clear IHvalid_execution_fragment0.
    inversion H; subst. simpl in *.
    inversion H0; subst. simpl in *.
    apply disjoint_push_l_run_r_wait_remove; auto.
Qed.

Lemma valid_execution_fragment_single_both': forall st1 st1' st2 st2' pid rb,
  valid_execution_fragment (sync L1) st1 st1' ((pid, event_resB rb) :: nil) ->
  valid_execution_fragment (sync L2) st2 st2' ((pid, event_resA rb) :: nil) ->
  disjoint (st1.(PidPos)) (st2.(PidPos)) ->
  composed_lts.valid_execution_fragment (compose L1 L2)
    (mkComposedState st1 st2)
    (mkComposedState st1' st2')
    ((pid, composed_lts.event_resB rb)::nil).
Proof.
  intros. remember [(pid, event_resB rb)] as acts1.
  remember [(pid, event_resA rb)] as acts2.
  induction H0; induction H; subst; intuition.
  all : try inversion Heqacts2.
  all : try inversion Heqacts1.
  - inversion H0; subst. simpl in *. intuition.
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    eapply Step_None; eauto.
    eapply Step_Internal; eauto.
    eapply Step_None; eauto.
  - inversion H0; subst. simpl in *. intuition.
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
    apply valid_execution_fragment_inv1' in H3.
    destruct H3 as [st1'' [st1''' [Hv1 [Hinit1 Hv2]]]].
    eapply composed_lts.valid_execution_fragment_join' with (a:=[]); eauto.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    eapply Step_None; eauto.
    3 : { simpl. reflexivity. }
    inversion H; subst. simpl in *.
    assumption.
    inversion H; subst. simpl in *. subst.
    eapply composed_lts.Step_Internal_Reply; eauto.
    simpl.
    eapply composed_step_L1_pop; eauto.
    simpl in H3. intuition.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    inversion H0; subst. simpl in *.
    clear H5.
    inversion Hinit1; subst.
    simpl in *.
    apply valid_execution_fragment_pos in Hv1.
    simpl in Hv1. subst.
    apply disjoint_remove_l_r_run_remove; auto.
  - subst.
    eapply composed_lts.Step_Internal_Reply; eauto.
    simpl.
    eapply composed_step_L1_pop; eauto.
    simpl in H3; intuition.
    eapply valid_execution_fragment_com_nil_nil; eauto.
    clear IHvalid_execution_fragment.
    clear IHvalid_execution_fragment0.
    inversion H; subst. simpl in *.
    inversion H0; subst. simpl in *.
    apply disjoint_remove_l_r_run_remove; auto.
Qed.

Fixpoint compatible_compose_pos (pos1 pos2 : env Position) (acts : list (@composed_lts.event li_null liA liB)) : Prop :=
  match acts with
  | nil => True
  | (pid, act) :: acts' =>
    match act with
    | composed_lts.event_invC _ =>
      pid # pos1 /\ pid # pos2 /\
      compatible_compose_pos pos1 ((pid, Run) :: pos2) acts'
    | composed_lts.event_invB _ =>
      pid # pos1 /\ binds pid Run pos2 /\
      compatible_compose_pos ((pid, Run) :: pos1) ((pid, Wait) :: (remove pos2 pid)) acts'
    | composed_lts.event_resB _ =>
      binds pid Run pos1 /\ binds pid Wait pos2 /\
      compatible_compose_pos (remove pos1 pid) ((pid, Run) :: (remove pos2 pid)) acts'
    | composed_lts.event_resC _ =>
      pid # pos1 /\ binds pid Run pos2 /\
      compatible_compose_pos pos1 (remove pos2 pid) acts'
    | composed_lts.event_invA _ => True
    | composed_lts.event_resA _ => True
    end
  end.

Lemma valid_execution_fragment_join: forall acts st st',
  valid_execution_fragment (sync L1) st.(L1State) st'.(L1State) (gatherAB acts) ->
  valid_execution_fragment (sync L2) st.(L2State) st'.(L2State) (gatherBC acts) ->
  disjoint st.(L1State).(PidPos) st.(L2State).(PidPos) ->
  ok (PidPos (L1State st)) ->
  ok (PidPos (L2State st)) ->
  compatible_compose_pos st.(L1State).(PidPos) st.(L2State).(PidPos) acts ->
  composed_lts.valid_execution_fragment (compose L1 L2) st st' acts.
Proof.
  induction acts; simpl; intros.
  - destruct st, st'. simpl in *. subst.
    eapply valid_execution_fragment_com_nil_nil; eauto.
  - destruct a. destruct _e; simpl in *.
    -- apply valid_execution_fragment_inv in H0.
      destruct H0 as [st2'' [Hv1 Hv2]].
      assert (valid_execution_fragment (sync L1)
        (L1State (mkComposedState 
                    (L1State st) st2''))
        (L1State st')
        (gatherAB acts)).
      simpl. assumption.
      apply IHacts in H0; auto.
      eapply composed_lts.valid_execution_fragment_join' with (a:=[(n, composed_lts.event_invC q)]); eauto.
      clear H0. destruct st. simpl in *.
      eapply valid_execution_fragment_single_right; eauto.
      intuition.
      eapply Step_None; eauto.
      simpl.
      apply valid_execution_fragment_pos in Hv1.
      simpl in Hv1.
      rewrite <-Hv1.
      apply disjoint_push_r_run; auto.
      intuition.
      simpl.
      apply valid_execution_fragment_pos in Hv1.
      simpl in Hv1.
      rewrite <-Hv1.
      econstructor; eauto.
      intuition.
      apply valid_execution_fragment_pos in Hv1.
      simpl in Hv1.
      simpl.
      rewrite <-Hv1.
      intuition.
    -- apply valid_execution_fragment_inv in H0.
      destruct H0 as [st2'' [Hv1 Hv2]].
      assert (valid_execution_fragment (sync L1)
        (L1State (mkComposedState 
                    (L1State st) st2''))
        (L1State st')
        (gatherAB acts)).
      simpl. assumption.
      apply IHacts in H0; auto.
      eapply composed_lts.valid_execution_fragment_join' with (a:=[(n, composed_lts.event_resC r)]); eauto.
      clear H0. destruct st. simpl in *.
      eapply valid_execution_fragment_single_right'; eauto.
      intuition.
      eapply Step_None; eauto.
      simpl.
      apply valid_execution_fragment_pos in Hv1.
      simpl in Hv1.
      rewrite <-Hv1.
      apply disjoint_remove_r; auto.
      intuition.
      simpl.
      apply valid_execution_fragment_pos in Hv1.
      simpl in Hv1.
      rewrite <-Hv1.
      apply remove_preserves_ok; auto.
      simpl.
      apply valid_execution_fragment_pos in Hv1.
      simpl in Hv1.
      rewrite <-Hv1.
      intuition.
    -- apply valid_execution_fragment_inv in H0.
      apply valid_execution_fragment_inv in H.
      destruct H0 as [st2'' [Hv1 Hv2]].
      destruct H as [st1'' [Hv11 Hv21]].
      assert (valid_execution_fragment (sync L1)
        (L1State (mkComposedState 
                    st1'' st2''))
        (L1State st')
        (gatherAB acts)).
      simpl. assumption.
      apply IHacts in H; auto.
      eapply composed_lts.valid_execution_fragment_join' with (a:=[(n, composed_lts.event_invB q)]); eauto.
      clear H.
      destruct st. simpl in *.
      eapply valid_execution_fragment_single_both; eauto.
      simpl.
      apply valid_execution_fragment_pos in Hv11.
      simpl in Hv11.
      rewrite <-Hv11.
      apply valid_execution_fragment_pos in Hv1.
      simpl in Hv1.
      rewrite <-Hv1.
      apply disjoint_push_l_run_r_wait_remove; auto.
      simpl.
      apply valid_execution_fragment_pos in Hv11.
      simpl in Hv11.
      rewrite <-Hv11.
      econstructor; eauto.
      intuition.
      simpl.
      apply valid_execution_fragment_pos in Hv1.
      simpl in Hv1.
      rewrite <-Hv1.
      econstructor; eauto.
      apply remove_preserves_ok; auto.
      apply ok_remove_notin; auto.
      simpl.
      apply valid_execution_fragment_pos in Hv11.
      simpl in Hv11.
      rewrite <-Hv11.
      apply valid_execution_fragment_pos in Hv1.
      simpl in Hv1.
      rewrite <-Hv1.
      intuition.
    -- apply valid_execution_fragment_inv in H0.
      apply valid_execution_fragment_inv in H.
      destruct H0 as [st2'' [Hv1 Hv2]].
      destruct H as [st1'' [Hv11 Hv21]].
      assert (valid_execution_fragment (sync L1)
        (L1State (mkComposedState 
                    st1'' st2''))
        (L1State st')
        (gatherAB acts)).
      simpl. assumption.
      apply IHacts in H; auto.
      eapply composed_lts.valid_execution_fragment_join' with (a:=[(n, composed_lts.event_resB r)]); eauto.
      clear H.
      destruct st.
      intuition.
      eapply valid_execution_fragment_single_both'; eauto.
      simpl.
      apply valid_execution_fragment_pos in Hv11.
      simpl in Hv11.
      rewrite <-Hv11.
      apply valid_execution_fragment_pos in Hv1.
      simpl in Hv1.
      rewrite <-Hv1.
      apply disjoint_remove_l_r_run_remove; auto.
      simpl.
      apply valid_execution_fragment_pos in Hv11.
      simpl in Hv11.
      rewrite <-Hv11.
      apply remove_preserves_ok; auto.
      intuition.
      simpl.
      apply valid_execution_fragment_pos in Hv1.
      simpl in Hv1.
      rewrite <-Hv1.
      econstructor; eauto.
      apply remove_preserves_ok; auto.
      apply ok_remove_notin; auto.
      simpl.
      apply valid_execution_fragment_pos in Hv11.
      simpl in Hv11.
      rewrite <-Hv11.
      apply valid_execution_fragment_pos in Hv1.
      simpl in Hv1.
      rewrite <-Hv1.
      intuition.
    -- destruct q.
    -- destruct r.
Qed.

Lemma valid_execution_fragment_compatible_compose_pos: forall s s' acts,
  composed_lts.valid_execution_fragment (compose L1 L2) s s' acts ->
  compatible_compose_pos s.(L1State).(PidPos) s.(L2State).(PidPos) acts.
Proof.
  induction 1; simpl; intros.
  - auto.
  - inversion H; subst; simpl in *;
    inversion H1; subst;
    assumption.
  - inversion H; subst; simpl in *;
    inversion H1; subst;
    assumption.
  - inversion H; subst.
  - inversion H; subst.
  - inversion H; subst; simpl in *;
    inversion H1; subst; intuition.
  - inversion H; subst; simpl in *;
    inversion H1; subst; intuition.
  - inversion H; subst; simpl in *;
    inversion H1; subst;
    inversion H2; subst;
    intuition.
  - inversion H; subst; simpl in *;
    inversion H1; subst;
    inversion H2; subst;
    intuition.
Qed.

End ComposedTrace.

Section Refinement.

Context {liA liB : language_interface}.

Import LibEnv.

Lemma refines_composed_refines : forall (L1 L1' : lts li_null liA) (L2 : lts liA liB),
  refines (sync L1) (sync L1') ->
  composed_refines (compose L1 L2) (compose L1' L2).
Proof.
  intros.
  unfold composed_refines. intros.
  unfold refines in H.
  unfold composed_lts.in_traces in H0.
  destruct H0 as [init [final [Hnew Hvalid]]].
  assert (Hvalidtmp : composed_lts.valid_execution_fragment (compose L3 L4) init final c_acts).
  assumption.
  assert (Hvalidtmp' : composed_lts.valid_execution_fragment (compose L3 L4) init final c_acts).
  assumption.
  assert (Hcompatible : compatible_compose_pos init.(L1State).(PidPos) init.(L2State).(PidPos) c_acts).
  eapply valid_execution_fragment_compatible_compose_pos; eauto.
  apply valid_execution_fragment_com in Hvalidtmp.
  apply valid_execution_fragment_com' in Hvalid.
  assert (in_traces (sync L1') (gatherAB c_acts)).
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
  exists (mkComposedState init' L2State0).
  exists (mkComposedState final' L2State1).
  intuition.
  unfold composed_new_state. simpl. intuition.
  eapply valid_execution_fragment_join; eauto.
  simpl. inversion Hnew'.
  rewrite H3.
  unfold disjoint. intuition.
  inversion H4. apply notin_empty.
  simpl.
  inversion Hnew'.
  rewrite H3. econstructor.
  simpl.
  inversion H1; subst.
  rewrite H3. econstructor.
  simpl.
  inversion Hnew'.
  rewrite H3.
  inversion H1; subst.
  rewrite H5.
  inversion H0; subst.
  rewrite H7 in Hcompatible.
  rewrite H5 in Hcompatible.
  assumption.
Qed.

End Refinement.

Section Compatibility.

Context {liA liB : language_interface}.
  
Lemma gather_pid_events_B_gather_pid_external_events: forall 
  (acts : list (@composed_lts.event li_null liA liB)) pid,
  gather_pid_events_B pid acts = [] ->
  gather_pid_external_events (gatherAB acts) pid = [].
Proof.
  induction acts; simpl; intros.
  - reflexivity.
  - destruct a.
    destruct _e; simpl;
    destruct (pid =? n);
      try discriminate; simpl; intuition.
    destruct q. destruct r.
Qed.

End Compatibility.