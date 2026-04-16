Require Import
	List
  Nat
  Arith
  LibVar
	LTS
	Refinement
  Tensor
  SyncLTS.
Require LibEnv.
Import ListNotations.

Section test.
  Context {liA liB : language_interface }.
  Fixpoint get_pid_events (acts : list (@event liA liB)) (pid : Pid) :=
    match acts with
    | nil => nil
    | (pid', act) :: acts' =>
      let events' := get_pid_events acts' pid in
      if pid' =? pid then act :: events'
      else events'
    end.

End test.

Section RAWTensorLTS.
  Context {liA liB : language_interface}.
  Variable L1 : lts li_null liA.
  Variable L2 : lts li_null liB.

  Record tensor_state : Type := mkTensorState {
    L1State : L1.(state);
    L2State : L2.(state);
  }.

  Inductive tensor_internal : Type :=
  | intL1 (act : L1.(internal))
  | intL2 (act : L2.(internal)).

  Definition tensor_new_state tst : Prop := 
    L1.(new_state) tst.(L1State) /\ 
    L2.(new_state) tst.(L2State).

  Import LibEnv.

  Inductive tensor_initial_state : tensor_state -> Pid -> (tensor_query liA liB) -> tensor_state -> Prop :=
  | tensor_initial_state_L2 : forall tst tst' st2 st2' qd st1 pid,
      initial_state L2 st2 pid qd st2' ->
      tst = mkTensorState st1 st2 ->
      tst' = mkTensorState st1 st2' ->
      tensor_initial_state tst pid (queryR qd) tst'
  | tensor_initial_state_L1 : forall tst tst' st1 st1' qb st2 pid,
      initial_state L1 st1 pid qb st1' ->
      tst = mkTensorState st1 st2 ->
      tst' = mkTensorState st1' st2 ->
      tensor_initial_state tst pid (queryL qb) tst'
  .

  Inductive tensor_step : tensor_state -> Pid -> tensor_internal -> tensor_state -> Prop :=
  | tensor_step_L2_internal : forall st1 st2 st2' act tst tst' pid,
      step L2 st2 pid act st2' ->
      tst = mkTensorState st1 st2 ->
      tst' = mkTensorState st1 st2' ->
      tensor_step tst pid (intL2 act) tst'
  | tensor_step_L1_internal : forall st1 st2 st1' act tst tst' pid,
      step L1 st1 pid act st1' ->
      tst = mkTensorState st1 st2 ->
      tst' = mkTensorState st1' st2 ->
      tensor_step tst pid (intL1 act) tst'
  .

  Inductive tensor_at_external : tensor_state -> Pid -> query li_null -> tensor_state -> Prop :=.

  Inductive tensor_after_external : tensor_state -> Pid -> reply li_null -> tensor_state -> Prop :=.

  Inductive tensor_final_state : tensor_state -> Pid -> (tensor_reply liA liB) -> tensor_state -> Prop :=
  | tensor_final_state_L2 : forall st1 st2 rd st2' tst tst' pid,
      final_state L2 st2 pid rd st2' ->
      tst = mkTensorState st1 st2 ->
      tst' = mkTensorState st1 st2' ->
      tensor_final_state tst pid (replyR rd) tst'
  | tensor_final_state_L1 : forall st1 st2 rb st1' tst tst' pid,
      final_state L1 st1 pid rb st1' ->
      tst = mkTensorState st1 st2 ->
      tst' = mkTensorState st1' st2 ->
      tensor_final_state tst pid (replyL rb) tst'
  .

  Definition tensor
    : lts li_null (tensor_li liA liB)
    := mkLTS li_null (tensor_li liA liB)
      tensor_state
      tensor_internal
      tensor_step
      tensor_new_state
      tensor_initial_state
      tensor_at_external
      tensor_after_external
      tensor_final_state.

End RAWTensorLTS.

Arguments L1State {liA liB L1 L2}.
Arguments L2State {liA liB L1 L2}.
Arguments mkTensorState {liA liB L1 L2}.

Notation " L ⊗' L' " := (RawTensor.tensor L L') (at level 67).

Section TensorTrace.

Context {liA liB : language_interface}.
Variable L1 : lts li_null liA.
Variable L2 : lts li_null liB.

Fixpoint gatherL1 (acts : list (@event li_null (tensor_li liA liB))) : list (@event li_null liA) :=
	match acts with
	| nil => nil
	| (pid, act) :: acts' =>
		let events' := gatherL1 acts' in
		match act with
		| event_invB qb =>
			match qb with
			| queryL q => (pid, event_invB q) :: events'
			| queryR _ => events'
			end
		| event_resB rb =>
			match rb with
			| replyL r => (pid, event_resB r) :: events'
			| replyR _ => events'
			end
		| _ => events'
		end
	end.

Fixpoint gatherL2 (acts : list (@event li_null (tensor_li liA liB))) : list (@event li_null liB) :=
	match acts with
	| nil => nil
	| (pid, act) :: acts' =>
		let events' := gatherL2 acts' in
		match act with
		| event_invB qb =>
			match qb with
			| queryR q => (pid, event_invB q) :: events'
			| queryL _ => events'
			end
		| event_resB rb =>
			match rb with
			| replyR r => (pid, event_resB r) :: events'
			| replyL _ => events'
			end
		| _ => events'
		end
	end.

Lemma valid_execution_fragment_com: forall st st' acts,
  valid_execution_fragment (tensor L1 L2) st st' acts ->
  valid_execution_fragment L1 st.(L1State) st'.(L1State) (gatherL1 acts).
Proof.
  induction 1; simpl; intros.
  - subst. econstructor; eauto.
  - eapply valid_execution_fragment_join' with (a:=[]); eauto.
    clear IHvalid_execution_fragment. clear H0.
    simpl in H. inversion H; subst.
    -- eapply Step_None; eauto.
    -- simpl. eapply Step_Internal; eauto.
      eapply Step_None; eauto.
  - destruct qa.
	- destruct ra.
  - destruct qb.
		-- simpl in *.
			eapply valid_execution_fragment_join' with (a:=[(pid, event_invB q)]); eauto.
			simpl in H. inversion H; subst; simpl.
			eapply Step_Initial_Call; eauto.
			eapply Step_None; eauto.
		-- eapply valid_execution_fragment_join' with (a:=[]); eauto.
			simpl in H. inversion H; subst; simpl.
			eapply Step_None; eauto.
  - destruct rb.
		-- simpl in *.
			eapply valid_execution_fragment_join' with (a:=[(pid, event_resB r)]); eauto.
			simpl in H. inversion H; subst; simpl.
			eapply Step_Final_Return; eauto.
			eapply Step_None; eauto.
		-- eapply valid_execution_fragment_join' with (a:=[]); eauto.
			simpl in H. inversion H; subst; simpl.
			eapply Step_None; eauto.
Qed.

Lemma valid_execution_fragment_com': forall st st' acts,
  valid_execution_fragment (tensor L1 L2) st st' acts ->
  valid_execution_fragment L2 st.(L2State) st'.(L2State) (gatherL2 acts).
Proof.
  induction 1; simpl; intros.
  - subst. econstructor; eauto.
  - eapply valid_execution_fragment_join' with (a:=[]); eauto.
    clear IHvalid_execution_fragment. clear H0.
    simpl in H. inversion H; subst; simpl.
    -- eapply Step_Internal; eauto.
      eapply Step_None; eauto.
    -- eapply Step_None; eauto.
  - destruct qa.
	- destruct ra.
  - destruct qb.
		-- eapply valid_execution_fragment_join' with (a:=[]); eauto.
			simpl in H. inversion H; subst; simpl.
			eapply Step_None; eauto.
		-- simpl in *.
			eapply valid_execution_fragment_join' with (a:=[(pid, event_invB q)]); eauto.
			simpl in H. inversion H; subst; simpl.
			eapply Step_Initial_Call; eauto.
			eapply Step_None; eauto.
  - destruct rb.
		-- eapply valid_execution_fragment_join' with (a:=[]); eauto.
			simpl in H. inversion H; subst; simpl.
			eapply Step_None; eauto.
		-- simpl in *.
			eapply valid_execution_fragment_join' with (a:=[(pid, event_resB r)]); eauto.
			simpl in H. inversion H; subst; simpl.
			eapply Step_Final_Return; eauto.
			eapply Step_None; eauto.
Qed.

Lemma valid_execution_fragment_com_nil_nil: forall st1 st1' st2 st2',
  valid_execution_fragment L1 st1 st1' nil ->
  valid_execution_fragment L2 st2 st2' nil ->
  valid_execution_fragment (tensor L1 L2)
          (mkTensorState st1 st2) (mkTensorState st1' st2') nil.
Proof.
  intros.
  remember [] as acts1.
  remember (@nil (@event li_null liB)) as acts2.
  induction H; induction H0; subst; simpl in *; intuition; try (inversion Heqacts1); try (inversion Heqacts2).
  - eapply Step_None; eauto.
  - eapply valid_execution_fragment_join' with (a:=[]); eauto.
    clear H.
    eapply Step_Internal; eauto. simpl.
    eapply tensor_step_L2_internal; eauto.
    eapply Step_None; eauto.
  - eapply valid_execution_fragment_join' with (a:=[]); eauto.
    clear H0.
    eapply Step_Internal; eauto. simpl.
    eapply tensor_step_L1_internal; eauto.
    eapply Step_None; eauto.
  - eapply valid_execution_fragment_join' with (a:=[]); eauto.
    clear H4.
    eapply Step_Internal; eauto. simpl.
    eapply tensor_step_L1_internal; eauto.
    eapply Step_None; eauto.
Qed.

Import LibEnv.

Lemma valid_execution_fragment_single_left: forall st1 st1' st2 st2' pid qa,
  valid_execution_fragment L1 st1 st1' ((pid, event_invB qa) :: nil) ->
  valid_execution_fragment L2 st2 st2' nil ->
  valid_execution_fragment (tensor L1 L2)
    (mkTensorState st1 st2) (mkTensorState st1' st2') ((pid, @event_invB li_null (tensor_li liA liB) (@queryL liA liB qa))::nil).
Proof.
  intros. remember [(pid, event_invB qa)] as acts1.
  remember (@nil event) as acts2.
  induction H; induction H0; subst; intuition.
  all : try inversion Heqacts2.
  all : try inversion Heqacts1.
  - eapply valid_execution_fragment_join' with (a:=[]); eauto.
    eapply Step_Internal; eauto.
    simpl. eapply tensor_step_L1_internal; eauto.
    eapply Step_None; eauto.
  - eapply valid_execution_fragment_join' with (a:=[]); eauto.
    eapply Step_Internal; eauto.
    simpl. eapply tensor_step_L1_internal; eauto.
    eapply Step_None; eauto.
  - subst.
		eapply valid_execution_fragment_join' with (a:=[(pid, @event_invB li_null (tensor_li liA liB) (queryL qa))]); eauto.
		3 : { reflexivity. }
		2 : {
			eapply valid_execution_fragment_com_nil_nil; eauto.
			eapply Step_None; eauto. }
    eapply Step_Initial_Call; eauto.
    simpl. eapply tensor_initial_state_L1; eauto.
    eapply Step_None; eauto.
  - subst.
		eapply valid_execution_fragment_join' with (a:=[(pid, @event_invB li_null (tensor_li liA liB) (queryL qa))]); eauto.
		3 : { reflexivity. }
		2 : { eapply valid_execution_fragment_com_nil_nil; eauto. }
    eapply Step_Initial_Call; eauto.
    simpl. eapply tensor_initial_state_L1; eauto.
    eapply Step_Internal; eauto.
    simpl. eapply tensor_step_L2_internal; eauto.
    eapply Step_None; eauto.
Qed.

Lemma valid_execution_fragment_single_right: forall st1 st1' st2 st2' pid qc,
  valid_execution_fragment L1 st1 st1' nil ->
  valid_execution_fragment L2 st2 st2' ((pid, event_invB qc) :: nil) ->
  valid_execution_fragment (tensor L1 L2)
    (mkTensorState st1 st2) (mkTensorState st1' st2') ((pid, @event_invB li_null (tensor_li liA liB) (queryR qc))::nil).
Proof.
  intros. remember [(pid, event_invB qc)] as acts1.
  remember (@nil event) as acts2.
  induction H; induction H0; subst; intuition.
  all : try inversion Heqacts2.
  all : try inversion Heqacts1.
  - eapply valid_execution_fragment_join' with (a:=[]); eauto.
    eapply Step_Internal; eauto.
    simpl. eapply tensor_step_L2_internal; eauto.
    eapply Step_None; eauto.
  - subst.
		eapply valid_execution_fragment_join' with (a:=[(pid, @event_invB li_null (tensor_li liA liB) (queryR qc))]); eauto.
		3 : { reflexivity. }
		2 : {
			eapply valid_execution_fragment_com_nil_nil; eauto.
			eapply Step_None; eauto. }
    eapply Step_Initial_Call; eauto.
    simpl. eapply tensor_initial_state_L2; eauto.
    eapply Step_None; eauto.
  - eapply valid_execution_fragment_join' with (a:=[]); eauto.
    eapply Step_Internal; eauto.
    simpl. eapply tensor_step_L1_internal; eauto.
    eapply Step_None; eauto.
  - subst.
		eapply valid_execution_fragment_join' with (a:=[]); eauto.
		eapply valid_execution_fragment_com_nil_nil; eauto.
		eapply Step_Internal; eauto.
		eapply Step_None; eauto.
		eapply Step_None; eauto.
Qed.

Lemma valid_execution_fragment_single_left': forall st1 st1' st2 st2' pid qa,
  valid_execution_fragment L1 st1 st1' ((pid, event_resB qa) :: nil) ->
  valid_execution_fragment L2 st2 st2' nil ->
  valid_execution_fragment (tensor L1 L2)
    (mkTensorState st1 st2) (mkTensorState st1' st2') ((pid, @event_resB li_null (tensor_li liA liB) (@replyL liA liB qa))::nil).
Proof.
  intros. remember [(pid, event_resB qa)] as acts1.
  remember (@nil event) as acts2.
  induction H; induction H0; subst; intuition.
  all : try inversion Heqacts2.
  all : try inversion Heqacts1.
  - eapply valid_execution_fragment_join' with (a:=[]); eauto.
    eapply Step_Internal; eauto.
    simpl. eapply tensor_step_L1_internal; eauto.
    eapply Step_None; eauto.
  - eapply valid_execution_fragment_join' with (a:=[]); eauto.
    eapply Step_Internal; eauto.
    simpl. eapply tensor_step_L1_internal; eauto.
    eapply Step_None; eauto.
  - subst.
		eapply valid_execution_fragment_join' with (a:=[(pid, @event_resB li_null (tensor_li liA liB) (replyL qa))]); eauto.
		3 : { reflexivity. }
		2 : {
			eapply valid_execution_fragment_com_nil_nil; eauto.
			eapply Step_None; eauto. }
    eapply Step_Final_Return; eauto.
    simpl. eapply tensor_final_state_L1; eauto.
    eapply Step_None; eauto.
  - subst.
		eapply valid_execution_fragment_join' with (a:=[(pid, @event_resB li_null (tensor_li liA liB) (replyL qa))]); eauto.
		3 : { reflexivity. }
		2 : { eapply valid_execution_fragment_com_nil_nil; eauto. }
    eapply Step_Final_Return; eauto.
    simpl. eapply tensor_final_state_L1; eauto.
    eapply Step_Internal; eauto.
    simpl. eapply tensor_step_L2_internal; eauto.
    eapply Step_None; eauto.
Qed.

Lemma valid_execution_fragment_single_right': forall st1 st1' st2 st2' pid qc,
  valid_execution_fragment L1 st1 st1' nil ->
  valid_execution_fragment L2 st2 st2' ((pid, event_resB qc) :: nil) ->
  valid_execution_fragment (tensor L1 L2)
    (mkTensorState st1 st2) (mkTensorState st1' st2') ((pid, @event_resB li_null (tensor_li liA liB) (replyR qc))::nil).
Proof.
  intros. remember [(pid, event_resB qc)] as acts1.
  remember (@nil event) as acts2.
  induction H; induction H0; subst; intuition.
  all : try inversion Heqacts2.
  all : try inversion Heqacts1.
  - eapply valid_execution_fragment_join' with (a:=[]); eauto.
    eapply Step_Internal; eauto.
    simpl. eapply tensor_step_L2_internal; eauto.
    eapply Step_None; eauto.
  - subst.
		eapply valid_execution_fragment_join' with (a:=[(pid, @event_resB li_null (tensor_li liA liB) (replyR qc))]); eauto.
		3 : { reflexivity. }
		2 : {
			eapply valid_execution_fragment_com_nil_nil; eauto.
			eapply Step_None; eauto. }
    eapply Step_Final_Return; eauto.
    simpl. eapply tensor_final_state_L2; eauto.
    eapply Step_None; eauto.
  - eapply valid_execution_fragment_join' with (a:=[]); eauto.
    eapply Step_Internal; eauto.
    simpl. eapply tensor_step_L1_internal; eauto.
    eapply Step_None; eauto.
  - subst.
		eapply valid_execution_fragment_join' with (a:=[]); eauto.
		eapply valid_execution_fragment_com_nil_nil; eauto.
		eapply Step_Internal; eauto.
		eapply Step_None; eauto.
		eapply Step_None; eauto.
Qed.

Lemma valid_execution_fragment_join: forall acts st st',
  valid_execution_fragment L1 st.(L1State) st'.(L1State) (gatherL1 acts) ->
  valid_execution_fragment L2 st.(L2State) st'.(L2State) (gatherL2 acts) ->
  valid_execution_fragment (tensor L1 L2) st st' acts.
Proof.
  induction acts; simpl; intros.
  - destruct st, st'.
    eapply valid_execution_fragment_com_nil_nil; eauto.
  - destruct a. destruct _e; simpl in *.
    -- destruct q.
    	--- apply valid_execution_fragment_inv in H.
				destruct H as [st1'' [Hv1 Hv2]].
				assert (valid_execution_fragment L2 
          (L2State (mkTensorState st1'' 
                    (L2State st)))
          (L2State st') (gatherL2 acts)).
				simpl. assumption.
				apply IHacts in H; auto.
				eapply valid_execution_fragment_join' with (a:=[(n, _)]); eauto.
				2 : { reflexivity. }
				clear H. destruct st. simpl in *.
				eapply valid_execution_fragment_single_left; eauto.
				eapply Step_None; eauto.
    	--- apply valid_execution_fragment_inv in H0.
				destruct H0 as [st2'' [Hv1 Hv2]].
				assert (valid_execution_fragment L1 
          (L1State (mkTensorState
                    (L1State st) st2''))
          (L1State st') (gatherL1 acts)).
				simpl. assumption.
				apply IHacts in H0; auto.
				eapply valid_execution_fragment_join' with (a:=[(n, _)]); eauto.
				2 : { reflexivity. }
				clear H. destruct st. simpl in *.
				eapply valid_execution_fragment_single_right; eauto.
				eapply Step_None; eauto.
		-- destruct r.
    	--- apply valid_execution_fragment_inv in H.
				destruct H as [st1'' [Hv1 Hv2]].
				assert (valid_execution_fragment L2 
          (L2State (mkTensorState st1'' 
                    (L2State st)))
          (L2State st') (gatherL2 acts)).
				simpl. assumption.
				apply IHacts in H; auto.
				eapply valid_execution_fragment_join' with (a:=[(n, _)]); eauto.
				2 : { reflexivity. }
				clear H. destruct st. simpl in *.
				eapply valid_execution_fragment_single_left'; eauto.
				eapply Step_None; eauto.
    	--- apply valid_execution_fragment_inv in H0.
				destruct H0 as [st2'' [Hv1 Hv2]].
				assert (valid_execution_fragment L1 
                (L1State (mkTensorState 
                  (L1State st) 
                    st2''))
                (L1State st')
                (gatherL1 acts)).
				simpl. assumption.
				apply IHacts in H0; auto.
				eapply valid_execution_fragment_join' with (a:=[(n, _)]); eauto.
				2 : { reflexivity. }
				clear H. destruct st. simpl in *.
				eapply valid_execution_fragment_single_right'; eauto.
				eapply Step_None; eauto.
    -- destruct q.
    -- destruct r.
Qed.

End TensorTrace.

Section Refinement.

Context {liA liB : language_interface }.

Import LibEnv.

Lemma refines_tensor_refines_r: forall (L1 L1' : lts li_null liA) (L2 : lts li_null liB),
	refines L1 L1' ->
	refines (tensor L1 L2) (tensor L1' L2).
Proof.
  intros.
  unfold refines. intros.
  unfold refines in H.
  unfold in_traces in H0.
  destruct H0 as [init [final [Hnew Hvalid]]].
  assert (Hvalidtmp : valid_execution_fragment (tensor L1 L2) init final acts).
  assumption.
  apply valid_execution_fragment_com in Hvalidtmp.
  apply valid_execution_fragment_com' in Hvalid.
  assert (in_traces L1' (gatherL1 acts)).
  apply H.
  unfold in_traces. simpl in init, final.
  destruct init. destruct final. simpl in *.
  inversion Hnew; subst. simpl in *.
  eexists; eauto.
  unfold in_traces in H0.
  destruct H0 as [init' [final' [Hnew' Hvalid']]].
  unfold in_traces. simpl in *.
  destruct init. destruct final.
  inversion Hnew; subst. simpl in *. intuition. subst.
  exists (mkTensorState init' L2State0).
  exists (mkTensorState final' L2State1).
  intuition.
  unfold tensor_new_state. simpl. intuition.
  eapply valid_execution_fragment_join; eauto.
Qed.

Lemma refines_tensor_refines_l: forall (L1 : lts li_null liA) (L2 L2' : lts li_null liB),
	refines L2 L2' ->
	refines (tensor L1 L2) (tensor L1 L2').
Proof.
  intros.
  unfold refines. intros.
  unfold refines in H.
  unfold in_traces in H0.
  destruct H0 as [init [final [Hnew Hvalid]]].
  assert (Hvalidtmp : valid_execution_fragment (tensor L1 L2) init final acts).
  assumption.
  apply valid_execution_fragment_com in Hvalidtmp.
  apply valid_execution_fragment_com' in Hvalid.
  assert (in_traces L2' (gatherL2 acts)).
  apply H.
  unfold in_traces. simpl in init, final.
  destruct init. destruct final. simpl in *.
  inversion Hnew; subst. simpl in *. intuition.
  eexists; eauto.
  unfold in_traces in H0.
  destruct H0 as [init' [final' [Hnew' Hvalid']]].
  unfold in_traces. simpl in *.
  destruct init. destruct final.
  inversion Hnew; subst. simpl in *. intuition. subst.
  exists (mkTensorState L1State0 init').
  exists (mkTensorState L1State1 final').
  intuition.
  unfold tensor_new_state. simpl. intuition.
  eapply valid_execution_fragment_join; eauto.
Qed.
  
Theorem tensor_preserves_refines: forall (L1 L1' : lts li_null liA) (L2 L2' : lts li_null liB),
	refines L1 L1' ->
	refines L2 L2' ->
	refines (tensor L1 L2) (tensor L1' L2').
Proof.
	intros.
	eapply trans_refinement.
	eapply refines_tensor_refines_r; eauto.
	eapply refines_tensor_refines_l; eauto.
Qed.

End Refinement.


Section test.
  
Context {liA liB : language_interface}.
Variable L1 : lts li_null liA.
Variable L1' : lts li_null liA.
Variable L2 : lts li_null liB.

Import LibEnv.

Lemma refines_sync_refines_raw_tensor:
  refines L1 (sync L1) ->
  refines L2 (sync L2) ->
  refines (tensor L1 L2)
    (tensor (sync L1) (sync L2)).
Proof.
  intros.
  apply tensor_preserves_refines; auto.
Qed.

Definition sync_raw_tensor_wf (st : state (sync (tensor (sync L1) (sync L2)))) :=
  forall pid,
    (binds pid Run st.(LState).(L1State).(PidPos) ->
    pid # st.(LState).(L2State).(PidPos)) /\
    (binds pid Run st.(LState).(L2State).(PidPos) ->
    pid # st.(LState).(L1State).(PidPos)) /\
    (pid # st.(PidPos) -> 
      pid # st.(LState).(L1State).(PidPos) /\
      pid # st.(LState).(L2State).(PidPos)
    ) /\
    (binds pid Run st.(LState).(L1State).(PidPos) ->
      binds pid Run st.(PidPos)) /\
    (binds pid Run st.(LState).(L2State).(PidPos) ->
      binds pid Run st.(PidPos))
.

Lemma sync_raw_tensor_wf_new: forall s,
  new_state
    (sync (tensor (sync L1) (sync L2)))
    s ->
  sync_raw_tensor_wf s.
Proof.
  intros.
  inversion H; subst.
  unfold sync_raw_tensor_wf.
  inversion H0; subst.
  inversion H2; subst.
  inversion H3; subst.
  rewrite H5. rewrite H7.
  intros. intuition.
  inversion H8.
  inversion H8.
  apply notin_empty.
  apply notin_empty.
  inversion H8.
  inversion H8.
Qed.

Lemma valid_execution_fragment_tensor_sync_sync_tensor: forall s s' acts pos,
  valid_execution_fragment
    (tensor (sync L1) (sync L2))
    s s' acts ->
  compatible_pos pos acts ->
  ok pos ->
  sync_raw_tensor_wf
    (mkSyncState
      (tensor (sync L1) (sync L2))
      s pos
    ) ->
  valid_execution_fragment
    (sync (tensor (sync L1) (sync L2)))
    (mkSyncState
      (tensor (sync L1) (sync L2))
      s pos
    )
    (mkSyncState
      (tensor (sync L1) (sync L2))
      s' (test pos acts)
    )
    acts.
Proof.
  intros.
  generalize dependent pos.
  induction H; intros.
  - subst. simpl.
    eapply Step_None; eauto.
  - assert (binds pid Run pos).
    inversion H; subst.
    inversion H4; subst.
      unfold sync_raw_tensor_wf in *.
      simpl in *.
      specialize (H3 pid).
      intuition.
    inversion H4; subst.
      unfold sync_raw_tensor_wf in *.
      simpl in *.
      specialize (H3 pid).
      intuition.
    eapply valid_execution_fragment_join' with (a:=[]).
    2 : {
      eapply IHvalid_execution_fragment; eauto.
      inversion H; subst.
      - inversion H5; subst.
        unfold sync_raw_tensor_wf in *.
        simpl in *. intuition.
      - inversion H5; subst.
        unfold sync_raw_tensor_wf in *.
        simpl in *. intuition.
    }
    eapply Step_Internal; eauto.
    eapply sync_step_L_internal; eauto.
    eapply Step_None; eauto.
    reflexivity.
  - destruct qa.
  - destruct ra.
  - eapply valid_execution_fragment_join' with (a:=[(pid, event_invB qb)]).
    2 : {
      eapply IHvalid_execution_fragment; eauto.
      simpl in H1. intuition.
      simpl in H1. intuition.
      econstructor; eauto.
      inversion H; subst; simpl in *.
      - inversion H4; subst; simpl in *.
        unfold sync_raw_tensor_wf in *.
        simpl in *.
        intros.
        destruct (eq_nat_dec pid0 pid).
        -- subst.
          specialize (H3 pid).
          intuition.
          unfold "#" in H8.
          apply binds_in in H10.
          intuition.
          apply notin_union in H10.
          intuition.
          apply notin_neq in H13; intuition.
          apply binds_push_eq; auto.
          apply binds_push_eq; auto.
        -- specialize (H3 pid0).
          intuition.
          apply notin_union.
          intuition.
          apply notin_neq; auto.
          unfold binds in H10.
          simpl in H10.
          apply Nat.eqb_neq in n.
          rewrite n in H10.
          intuition.
          apply notin_union in H10.
          intuition.
          apply notin_union.
          apply notin_union in H10.
          intuition.
          apply binds_push_neq; auto.
          apply binds_push_neq_inv in H10; intuition.
          apply binds_push_neq; intuition.
      - inversion H4; subst; simpl in *.
        unfold sync_raw_tensor_wf in *.
        simpl in *.
        intros.
        destruct (eq_nat_dec pid0 pid).
        -- subst.
          specialize (H3 pid).
          intuition.
          unfold "#" in H6.
          apply binds_in in H3.
          intuition.
          apply notin_union in H10.
          intuition.
          apply notin_neq in H13; intuition.
          apply binds_push_eq; auto.
          apply binds_push_eq; auto.
        -- specialize (H3 pid0).
          intuition.
          apply binds_push_neq_inv in H10; intuition.
          apply notin_union.
          intuition.
          apply notin_neq; auto.
          apply notin_union.
          apply notin_union in H10.
          intuition.
          apply notin_union in H10.
          intuition.
          apply binds_push_neq; auto.
          apply binds_push_neq_inv in H10; intuition.
          apply binds_push_neq; auto.
    }
    2 : { reflexivity. }
    eapply Step_Initial_Call; eauto.
    eapply sync_initial_state_L; eauto.
    simpl in H1. intuition.
    eapply Step_None; eauto.
  - eapply valid_execution_fragment_join' with (a:=[(pid, event_resB rb)]).
    2 : {
      eapply IHvalid_execution_fragment; eauto.
      simpl in H1. intuition.
      apply remove_preserves_ok; auto.
      inversion H; subst; simpl in *.
      - inversion H4; subst; simpl in *.
        unfold sync_raw_tensor_wf in *.
        simpl in *.
        intros.
        destruct (eq_nat_dec pid0 pid).
        -- subst.
          specialize (H3 pid).
          intuition.
          apply remove_preserves_notin; auto.
          apply ok_remove_notin; auto.
          unfold "#" in H10.
          apply binds_in in H11.
          intuition.
          assert (pid # (remove pos0 pid)).
          apply ok_remove_notin; auto.
          apply binds_in in H11.
          unfold "#" in H12.
          intuition.
        -- specialize (H3 pid0).
          intuition.
          apply remove_preserves_notin; auto.
          apply remove_preserves_binds_notin in H10; auto.
          apply remove_neq_preserves_notin in H10; auto.
          intuition.
          apply remove_neq_preserves_notin in H10; auto.
          intuition.
          apply remove_preserves_notin; auto.
          apply remove_neq_preserves_binds; auto.
          apply remove_neq_preserves_binds; auto.
          apply remove_preserves_binds_notin in H10; auto.
      - inversion H4; subst; simpl in *.
        unfold sync_raw_tensor_wf in *.
        simpl in *.
        intros.
        destruct (eq_nat_dec pid0 pid).
        -- subst.
          specialize (H3 pid).
          intuition.
          apply remove_preserves_notin; auto.
          apply ok_remove_notin; auto.
          unfold "#" in H10.
          apply binds_in in H11.
          intuition.
          assert (pid # (remove pos0 pid)).
          apply ok_remove_notin; auto.
          apply binds_in in H9.
          unfold "#" in H12.
          intuition.
          assert (pid # (remove pos0 pid)).
          apply ok_remove_notin; auto.
          apply binds_in in H9.
          unfold "#" in H12.
          intuition.
          apply binds_in in H9.
          unfold "#" in H10.
          intuition.
        -- specialize (H3 pid0).
          intuition.
          apply remove_preserves_binds_notin in H10; auto.
          apply remove_preserves_notin; auto.
          apply remove_neq_preserves_notin in H10; intuition.
          apply remove_preserves_notin; auto.
          apply remove_neq_preserves_notin in H10; intuition.
          apply remove_preserves_binds_notin in H10; auto.
          apply remove_neq_preserves_binds; auto.
          apply remove_neq_preserves_binds; auto.
    }
    2 : { reflexivity. }
    eapply Step_Final_Return; eauto.
    eapply sync_final_state_L; eauto.
    simpl in H1. intuition.
    eapply Step_None; eauto.
Qed.

Lemma refines_sync_refines_sync_raw_tensor: 
  refines L1 (sync L1) ->
  refines L2 (sync L2) ->
  refines (sync (tensor L1 L2))
    (sync (tensor (sync L1) (sync L2))).
Proof.
  intros.
  unfold refines.
  intros.
  assert (Hrefine :
      refines (tensor L1 L2)
    (tensor (sync L1) (sync L2))).
  apply refines_sync_refines_raw_tensor; auto.
  assert (Hvalidtmp :
    in_traces (sync (tensor L1 L2)) acts).
  assumption.
  apply sync_refines_raw in H1.
  apply Hrefine in H1. clear Hrefine.
  unfold in_traces in H1.
  destruct H1 as [init [final [Hnew Hvalid]]].
  unfold in_traces in Hvalidtmp.
  destruct Hvalidtmp as [s [s' [Hnew' Hvalid']]].
  inversion Hnew'; subst.
  eapply valid_execution_fragment_tensor_sync_sync_tensor with (pos:=[]) in Hvalid; eauto.
  unfold in_traces.
  exists (
    mkSyncState
      (tensor (sync L1) (sync L2))
      init
      []
  ).
  exists (
    mkSyncState
      (tensor (sync L1) (sync L2))
      final
      (test [] acts)
  ).
  intuition.
  simpl. unfold sync_new_state.
  intuition.
  apply valid_execution_fragment_compatible_pos in Hvalid'.
  rewrite H2 in Hvalid'. assumption.
  econstructor.
  apply sync_raw_tensor_wf_new; auto.
  simpl.
  unfold sync_new_state.
  intuition.
Qed.

End test.
