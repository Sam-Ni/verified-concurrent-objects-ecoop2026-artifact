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

Section TensorLI.
  Variable liA : language_interface.
  Variable liB : language_interface.

  Inductive tensor_query :=
  | queryL : liA.(query) -> tensor_query
  | queryR : liB.(query) -> tensor_query.

  Inductive tensor_reply :=
  | replyL : liA.(reply) -> tensor_reply
  | replyR : liB.(reply) -> tensor_reply.

  Definition tensor_li :=
    mk_language_interface tensor_query tensor_reply.

End TensorLI.

Arguments queryL {liA liB}.
Arguments queryR {liA liB}.
Arguments replyL {liA liB}.
Arguments replyR {liA liB}.

Section TensorLTS.
  Context {liA liB : language_interface}.
  Variable _L1 : lts li_null liA.
  Variable _L2 : lts li_null liB.

  Definition L1 := sync _L1.
  Definition L2 := sync _L2.

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
  | tensor_initial_state_L2 : forall tst tst' st2 st2' qd st1 pid
      (Hnotin: pid # st1.(PidPos)),
      initial_state L2 st2 pid qd st2' ->
      tst = mkTensorState st1 st2 ->
      tst' = mkTensorState st1 st2' ->
      tensor_initial_state tst pid (queryR qd) tst'
  | tensor_initial_state_L1 : forall tst tst' st1 st1' qb st2 pid
      (Hnotin: pid # st2.(PidPos)),
      initial_state L1 st1 pid qb st1' ->
      tst = mkTensorState st1 st2 ->
      tst' = mkTensorState st1' st2 ->
      tensor_initial_state tst pid (queryL qb) tst'
  .

  Inductive tensor_step : tensor_state -> Pid -> tensor_internal -> tensor_state -> Prop :=
  | tensor_step_L2_internal : forall st1 st2 st2' act tst tst' pid
      (Hbinds : binds pid Run st2.(PidPos))
      (Hnotin: pid # st1.(PidPos)),
      step L2 st2 pid act st2' ->
      tst = mkTensorState st1 st2 ->
      tst' = mkTensorState st1 st2' ->
      tensor_step tst pid (intL2 act) tst'
  | tensor_step_L1_internal : forall st1 st2 st1' act tst tst' pid
      (Hbinds : binds pid Run st1.(PidPos))
      (Hnotin: pid # st2.(PidPos)),
      step L1 st1 pid act st1' ->
      tst = mkTensorState st1 st2 ->
      tst' = mkTensorState st1' st2 ->
      tensor_step tst pid (intL1 act) tst'
  .

  Inductive tensor_at_external : tensor_state -> Pid -> query li_null -> tensor_state -> Prop :=.

  Inductive tensor_after_external : tensor_state -> Pid -> reply li_null -> tensor_state -> Prop :=.

  Inductive tensor_final_state : tensor_state -> Pid -> (tensor_reply liA liB) -> tensor_state -> Prop :=
  | tensor_final_state_L2 : forall st1 st2 rd st2' tst tst' pid
      (Hbinds : binds pid Run st2.(PidPos))
      (Hnotin: pid # st1.(PidPos)),
      final_state L2 st2 pid rd st2' ->
      tst = mkTensorState st1 st2 ->
      tst' = mkTensorState st1 st2' ->
      tensor_final_state tst pid (replyR rd) tst'
  | tensor_final_state_L1 : forall st1 st2 rb st1' tst tst' pid
      (Hbinds : binds pid Run st1.(PidPos))
      (Hnotin: pid # st2.(PidPos)),
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

End TensorLTS.

Arguments L1State {liA liB _L1 _L2}.
Arguments L2State {liA liB _L1 _L2}.
Arguments mkTensorState {liA liB _L1 _L2}.

Notation " L ⊗-' L' " := (tensor L L') (at level 67).

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
  valid_execution_fragment (sync L1) st.(L1State) st'.(L1State) (gatherL1 acts).
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
  valid_execution_fragment (sync L2) st.(L2State) st'.(L2State) (gatherL2 acts).
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

Import LibEnv.

Lemma valid_execution_fragment_com_nil_nil: forall st1 st1' st2 st2',
  valid_execution_fragment (sync L1) st1 st1' nil ->
  valid_execution_fragment (sync L2) st2 st2' nil ->

  disjoint (st1.(PidPos)) (st2.(PidPos)) ->

  valid_execution_fragment (tensor L1 L2)
          (mkTensorState st1 st2) (mkTensorState st1' st2') nil.
Proof.
  intros.
  remember [] as acts1.
  remember (@nil (@event li_null liB)) as acts2.
  induction H; induction H0; subst; simpl in *; intuition; try (inversion Heqacts1); try (inversion Heqacts2).
  - eapply Step_None; eauto.
  - inversion H0; subst. simpl in *.
    intuition.
    eapply valid_execution_fragment_join' with (a:=[]); eauto.
    eapply Step_Internal; eauto. simpl.
    eapply tensor_step_L2_internal; eauto.
    assumption.
    apply H1 in Hbinds.
    assumption.
    eapply Step_None; eauto.
  - inversion H; subst. simpl in *.
    eapply valid_execution_fragment_join' with (a:=[]); eauto.
    eapply Step_Internal; eauto. simpl.
    eapply tensor_step_L1_internal; eauto.
    assumption.
    apply H1 in Hbinds. 
    assumption.
    eapply Step_None; eauto.
  - inversion H; subst.
    inversion H0; subst.
    simpl in *.
    eapply valid_execution_fragment_join' with (a:=[]); eauto.
    eapply Step_Internal; eauto. simpl.
    eapply tensor_step_L1_internal; eauto.
    assumption.
    simpl. apply H1 in Hbinds.
    assumption.
    eapply Step_None; eauto.
Qed.

Lemma valid_execution_fragment_single_left: forall st1 st1' st2 st2' pid qa
  (Hnotin: pid # st2.(PidPos)),
  valid_execution_fragment (sync L1) st1 st1' ((pid, event_invB qa) :: nil) ->
  valid_execution_fragment (sync L2) st2 st2' nil ->
  disjoint (st1.(PidPos)) (st2.(PidPos)) ->
  valid_execution_fragment (tensor L1 L2)
    (mkTensorState st1 st2) (mkTensorState st1' st2') ((pid, @event_invB li_null (tensor_li liA liB) (@queryL liA liB qa))::nil).
Proof.
  intros. remember [(pid, event_invB qa)] as acts1.
  remember (@nil event) as acts2.
  induction H; induction H0; subst; intuition.
  all : try inversion Heqacts2.
  all : try inversion Heqacts1.
  - inversion H; subst. simpl in *.
    intuition.
    eapply valid_execution_fragment_join' with (a:=[]); eauto.
    eapply Step_Internal; eauto.
    simpl.
    eapply tensor_step_L1_internal with (pid:=pid0); eauto.
    assumption.
    apply H1 in Hbinds. assumption.
    eapply Step_None; eauto.
  - inversion H; subst.
    inversion H0; subst.
    simpl in *.
    intuition.
    eapply valid_execution_fragment_join' with (a:=[]); eauto.
    eapply Step_Internal; eauto.
    simpl. eapply tensor_step_L1_internal; eauto.
    assumption.
    apply H1 in Hbinds. assumption.
    eapply Step_None; eauto.
  - subst.
    clear IHvalid_execution_fragment.
		eapply valid_execution_fragment_join' with (a:=[(pid, @event_invB li_null (tensor_li liA liB) (queryL qa))]); eauto.
		3 : { reflexivity. }
		2 : {
			eapply valid_execution_fragment_com_nil_nil; eauto.
			eapply Step_None; eauto.
      inversion H; subst. simpl in *.
      apply disjoint_push_l; auto. }
    eapply Step_Initial_Call; eauto.
    simpl. eapply tensor_initial_state_L1; eauto.
    eapply Step_None; eauto.
  - subst.
    clear IHvalid_execution_fragment.
    clear IHvalid_execution_fragment0.
      inversion H; subst.
      inversion H0; subst.
      simpl in *.
		eapply valid_execution_fragment_join' with (a:=[(pid, @event_invB li_null (tensor_li liA liB) (queryL qa))]); eauto.
		3 : { reflexivity. }
		2 : { eapply valid_execution_fragment_com_nil_nil; eauto.
      simpl in *.
      apply disjoint_push_l; auto. }
    eapply Step_Initial_Call; eauto.
    simpl. eapply tensor_initial_state_L1; eauto.
    assumption.
    eapply Step_Internal; eauto.
    simpl. eapply tensor_step_L2_internal; eauto.
    assumption. simpl.
    apply notin_union. intuition.
    apply notin_neq. intro.
    subst.
    apply binds_in in Hbinds.
    unfold "#" in Hnotin. intuition.
    apply H1 in Hbinds; intuition.
    eapply Step_None; eauto.
Qed.

Lemma valid_execution_fragment_single_right: forall st1 st1' st2 st2' pid qc
  (Hnotin: pid # st1.(PidPos)),
  valid_execution_fragment (sync L1) st1 st1' nil ->
  valid_execution_fragment (sync L2) st2 st2' ((pid, event_invB qc) :: nil) ->
  disjoint (st1.(PidPos)) (st2.(PidPos)) ->
  valid_execution_fragment (tensor L1 L2)
    (mkTensorState st1 st2)
      (mkTensorState st1' st2')
      ((pid, @event_invB li_null 
        (tensor_li liA liB) (queryR qc))::nil).
Proof.
  intros. remember [(pid, event_invB qc)] as acts1.
  remember (@nil event) as acts2.
  induction H; induction H0; subst; intuition.
  all : try inversion Heqacts2.
  all : try inversion Heqacts1.
  - inversion H0; subst.
    simpl in *. intuition.
    eapply valid_execution_fragment_join' with (a:=[]); eauto.
    eapply Step_Internal; eauto.
    simpl.
    eapply tensor_step_L2_internal with (pid:=pid0); eauto.
    assumption.
    apply H1 in Hbinds. assumption.
    eapply Step_None; eauto.
  - subst.
    clear IHvalid_execution_fragment.
		eapply valid_execution_fragment_join' with (a:=[(pid, @event_invB li_null (tensor_li liA liB) (queryR qc))]); eauto.
		3 : { reflexivity. }
		2 : {
			eapply valid_execution_fragment_com_nil_nil; eauto.
			eapply Step_None; eauto.
      inversion H0; subst.
      simpl in *.
      apply disjoint_push_r; auto.
      }
    eapply Step_Initial_Call; eauto.
    simpl. eapply tensor_initial_state_L2; eauto.
    eapply Step_None; eauto.
  - inversion H; subst.
    simpl in *. intuition.
    eapply valid_execution_fragment_join' with (a:=[]); eauto.
    eapply Step_Internal; eauto.
    simpl.
    eapply tensor_step_L1_internal with (pid:=pid0); eauto.
    assumption.
    apply H1 in Hbinds. assumption.
    eapply Step_None; eauto.
  - subst.
    clear IHvalid_execution_fragment.
    clear IHvalid_execution_fragment0.
    inversion H; subst.
    inversion H0; subst.
    simpl in *.
		eapply valid_execution_fragment_join' with (a:=[(pid, @event_invB li_null (tensor_li liA liB) (queryR qc))]); eauto.
		3 : { reflexivity. }
		2 : { eapply valid_execution_fragment_com_nil_nil; eauto.
      simpl in *.
      apply disjoint_push_r; auto. }
    eapply Step_Initial_Call; eauto.
    simpl. eapply tensor_initial_state_L2; eauto.
    assumption.
    eapply Step_Internal; eauto.
    simpl. eapply tensor_step_L1_internal; eauto.
    assumption. simpl.
    apply notin_union. intuition.
    apply notin_neq. intro.
    subst.
    apply binds_in in Hbinds.
    unfold "#" in Hnotin. intuition.
    apply H1 in Hbinds; intuition.
    eapply Step_None; eauto.
Qed.

Lemma valid_execution_fragment_single_left': forall st1 st1' st2 st2' pid qa,
  valid_execution_fragment (sync L1) st1 st1' ((pid, event_resB qa) :: nil) ->
  valid_execution_fragment (sync L2) st2 st2' nil ->
  disjoint (st1.(PidPos)) (st2.(PidPos)) ->
  valid_execution_fragment (tensor L1 L2)
    (mkTensorState st1 st2)
    (mkTensorState st1' st2')
    ((pid, @event_resB li_null (tensor_li liA liB) (@replyL liA liB qa))::nil).
Proof.
  intros. remember [(pid, event_resB qa)] as acts1.
  remember (@nil event) as acts2.
  induction H; induction H0; subst; intuition.
  all : try inversion Heqacts2.
  all : try inversion Heqacts1.
  - inversion H; subst. simpl in *.
    intuition.
    eapply valid_execution_fragment_join' with (a:=[]); eauto.
    eapply Step_Internal; eauto.
    simpl.
    eapply tensor_step_L1_internal with (pid:=pid0); eauto.
    assumption.
    apply H1 in Hbinds. assumption.
    eapply Step_None; eauto.
  - inversion H; subst.
    inversion H0; subst.
    simpl in *.
    intuition.
    eapply valid_execution_fragment_join' with (a:=[]); eauto.
    eapply Step_Internal; eauto.
    simpl. eapply tensor_step_L1_internal; eauto.
    assumption.
    apply H1 in Hbinds. assumption.
    eapply Step_None; eauto.
  - subst.
    clear IHvalid_execution_fragment.
		eapply valid_execution_fragment_join' with (a:=[(pid, @event_resB li_null (tensor_li liA liB) (replyL qa))]); eauto.
		3 : { reflexivity. }
		2 : {
			eapply valid_execution_fragment_com_nil_nil; eauto.
			eapply Step_None; eauto.
      inversion H; subst. simpl in *.
      apply disjoint_remove_l; auto. }
    eapply Step_Final_Return; eauto.
    simpl. eapply tensor_final_state_L1; eauto.
    inversion H; subst.
    simpl in *. assumption.
    inversion H; subst.
    simpl in *.
    apply H1 in Hbinds.
    assumption.
    eapply Step_None; eauto.
  - subst.
    clear IHvalid_execution_fragment.
      inversion H; subst.
      inversion H0; subst.
      simpl in *.
		eapply valid_execution_fragment_join' with (a:=[(pid, @event_resB li_null (tensor_li liA liB) (replyL qa))]); eauto.
		3 : { reflexivity. }
		2 : { eapply valid_execution_fragment_com_nil_nil; eauto.
      simpl in *.
      apply disjoint_remove_l; auto. }
    eapply Step_Final_Return; eauto.
    simpl. eapply tensor_final_state_L1; eauto.
    assumption.
    inversion H; subst.
    simpl in *.
    apply H1 in Hbinds.
    assumption.
    eapply Step_Internal; eauto.
    simpl. eapply tensor_step_L2_internal; eauto.
    assumption. simpl.
    2 : { eapply Step_None; eauto. }
    apply remove_preserves_notin; auto.
    apply H1 in Hbinds0; intuition.
Qed.

Lemma valid_execution_fragment_single_right': forall st1 st1' st2 st2' pid qc,
  valid_execution_fragment (sync L1) st1 st1' nil ->
  valid_execution_fragment (sync L2) st2 st2' ((pid, event_resB qc) :: nil) ->
  disjoint (st1.(PidPos)) (st2.(PidPos)) ->
  valid_execution_fragment (tensor L1 L2)
    (mkTensorState st1 st2)
    (mkTensorState st1' st2')
    ((pid, @event_resB li_null (tensor_li liA liB) (replyR qc))::nil).
Proof.
  intros. remember [(pid, event_resB qc)] as acts1.
  remember (@nil event) as acts2.
  induction H; induction H0; subst; intuition.
  all : try inversion Heqacts2.
  all : try inversion Heqacts1.
  - inversion H0; subst. simpl in *.
    intuition.
    eapply valid_execution_fragment_join' with (a:=[]); eauto.
    eapply Step_Internal; eauto.
    simpl.
    eapply tensor_step_L2_internal with (pid:=pid0); eauto.
    assumption.
    apply H1 in Hbinds. assumption.
    eapply Step_None; eauto.
  - subst.
    clear IHvalid_execution_fragment.
		eapply valid_execution_fragment_join' with (a:=[(pid, @event_resB li_null (tensor_li liA liB) (replyR qc))]); eauto.
		3 : { reflexivity. }
		2 : {
			eapply valid_execution_fragment_com_nil_nil; eauto.
			eapply Step_None; eauto.
      inversion H0; subst.
      simpl in *.
      apply disjoint_remove_r; auto.
      }
    eapply Step_Final_Return; eauto.
    simpl. eapply tensor_final_state_L2; eauto.
    inversion H0; subst.
    simpl in *. assumption.
    inversion H0; subst.
    simpl in *.
    apply H1 in Hbinds.
    assumption.
    eapply Step_None; eauto.
  - inversion H; subst.
    inversion H0; subst.
    simpl in *.
    intuition.
    eapply valid_execution_fragment_join' with (a:=[]); eauto.
    eapply Step_Internal; eauto.
    simpl. eapply tensor_step_L1_internal; eauto.
    assumption.
    apply H1 in Hbinds. assumption.
    eapply Step_None; eauto.
  - subst.
    clear IHvalid_execution_fragment0.
		eapply valid_execution_fragment_join' with (a:=[(pid, @event_resB li_null (tensor_li liA liB) (replyR qc))]); eauto.
		3 : { reflexivity. }
		2 : {
			eapply valid_execution_fragment_com_nil_nil; eauto.
      inversion H0; subst.
      inversion H; subst.
      simpl in *.
      apply disjoint_remove_r; auto. }
    eapply Step_Final_Return; eauto.
    simpl. eapply tensor_final_state_L2; eauto.
    inversion H0; subst.
    simpl in *. assumption.
    inversion H0; subst.
    simpl in *.
    apply H1 in Hbinds.
    assumption.
    eapply Step_Internal; eauto.
    simpl. eapply tensor_step_L1_internal; eauto.
    inversion H; subst.
    assumption.
    inversion H0; subst.
    simpl in *.
    apply remove_preserves_notin; auto.
    inversion H; subst.
    simpl in *.
    apply H1 in Hbinds0; intuition.
    eapply Step_None; eauto.
Qed.

Section test.

Variable A : Type.

Lemma in_binds : forall (E : env A) x,
x \in dom E ->
exists v,
binds x v E.
Proof.
  induction E; intros.
  - inversion H.
  - unfold binds. simpl in *.
    destruct a.
    destruct (x =? v)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst. exists a. reflexivity.
    -- apply Nat.eqb_neq in Heq.
      apply IHE.
      apply in_union in H.
      intuition.
      simpl in H0. intuition.
      subst. intuition.
Qed.
  
End test.

Fixpoint compatible_tensor_pos (pos1 pos2 : env Position) (acts : list (@event li_null (tensor_li liA liB))) : Prop :=
  match acts with
  | nil => True
  | (pid, act) :: acts' =>
    (match act with
    | event_invB q =>
      match q with
      | queryL _ =>
        pid # pos1 /\ pid # pos2 /\
        compatible_tensor_pos ((pid, Run) :: pos1) pos2 acts'
      | queryR _ =>
        pid # pos1 /\ pid # pos2 /\
        compatible_tensor_pos pos1 ((pid, Run) :: pos2) acts'
      end
    | event_resB r =>
      match r with
      | replyL _ =>
        binds pid Run pos1 /\ pid # pos2 /\
        compatible_tensor_pos (remove pos1 pid) pos2 acts'
      | replyR _ =>
        binds pid Run pos2 /\ pid # pos1 /\
        compatible_tensor_pos pos1 (remove pos2 pid) acts'
      end
    | event_invA _ => True
    | event_resA _ => True
    end)
  end.

Lemma valid_execution_fragment_join: forall acts st st',
  valid_execution_fragment (sync L1) st.(L1State) st'.(L1State) (gatherL1 acts) ->
  valid_execution_fragment (sync L2) st.(L2State) st'.(L2State) (gatherL2 acts) ->
  disjoint st.(L1State).(PidPos) st.(L2State).(PidPos) ->
  ok (PidPos (L1State st)) ->
  ok (PidPos (L2State st)) ->
  compatible_tensor_pos st.(L1State).(PidPos) st.(L2State).(PidPos) acts ->
  valid_execution_fragment (tensor L1 L2) st st' acts.
Proof.
  induction acts; simpl; intros.
  - destruct st, st'. simpl in *. subst.
    eapply valid_execution_fragment_com_nil_nil; eauto.
  - destruct a. destruct _e; simpl in *.
    -- destruct q.
    	--- apply valid_execution_fragment_inv in H.
				destruct H as [st1'' [Hv1 Hv2]].
				assert (valid_execution_fragment (sync L2)
          (L2State (mkTensorState st1'' 
                    (L2State st)))
          (L2State st') (gatherL2 acts)).
				simpl. assumption.
				apply IHacts in H; auto.
				eapply valid_execution_fragment_join' with (a:=[(n, _)]); eauto.
				2 : { reflexivity. }
				clear H. destruct st. simpl in *.
				eapply valid_execution_fragment_single_left; eauto.
        intuition.
				eapply Step_None; eauto.
        simpl.
        apply valid_execution_fragment_pos in Hv1.
        simpl in Hv1.
        rewrite <-Hv1.
        apply disjoint_push_l; auto.
        intuition.
        simpl in *.
        apply valid_execution_fragment_pos in Hv1.
        simpl in Hv1.
        rewrite <-Hv1.
        econstructor; eauto. intuition.
        simpl in *.
        apply valid_execution_fragment_pos in Hv1.
        simpl in Hv1.
        rewrite <-Hv1.
        intuition.
    	--- apply valid_execution_fragment_inv in H0.
				destruct H0 as [st2'' [Hv1 Hv2]].
				assert (valid_execution_fragment (sync L1)
          (L1State (mkTensorState 
                    (L1State st) st2''))
          (L1State st')
          (gatherL1 acts)).
				simpl. assumption.
				apply IHacts in H0; auto.
				eapply valid_execution_fragment_join' with (a:=[(n, _)]); eauto.
				2 : { reflexivity. }
				clear H. destruct st. simpl in *.
				eapply valid_execution_fragment_single_right; eauto.
        intuition.
				eapply Step_None; eauto.
        simpl.
        apply valid_execution_fragment_pos in Hv1.
        simpl in Hv1.
        rewrite <-Hv1.
        apply disjoint_push_r; auto.
        intuition.
        simpl in *.
        apply valid_execution_fragment_pos in Hv1.
        simpl in Hv1.
        rewrite <-Hv1.
        econstructor; eauto. intuition.
        simpl in *.
        apply valid_execution_fragment_pos in Hv1.
        simpl in Hv1.
        rewrite <-Hv1.
        intuition.
		-- destruct r.
    	--- apply valid_execution_fragment_inv in H.
				destruct H as [st1'' [Hv1 Hv2]].
				assert (valid_execution_fragment (sync L2)
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
        simpl.
        apply valid_execution_fragment_pos in Hv1.
        simpl in Hv1.
        rewrite <-Hv1.
        apply disjoint_remove_l; auto.
        simpl in H2.
        simpl.
        simpl in *.
        apply valid_execution_fragment_pos in Hv1.
        simpl in Hv1.
        rewrite <-Hv1.
        apply remove_preserves_ok; auto.
        simpl in *.
        apply valid_execution_fragment_pos in Hv1.
        simpl in Hv1.
        rewrite <-Hv1. intuition.
    	--- apply valid_execution_fragment_inv in H0.
				destruct H0 as [st2'' [Hv1 Hv2]].
				assert (valid_execution_fragment (sync L1)
          (L1State (mkTensorState 
                    (L1State st) st2''))
          (L1State st') (gatherL1 acts)).
				simpl. assumption.
				apply IHacts in H0; auto.
				eapply valid_execution_fragment_join' with (a:=[(n, _)]); eauto.
				2 : { reflexivity. }
				clear H. destruct st. simpl in *.
				eapply valid_execution_fragment_single_right'; eauto.
				eapply Step_None; eauto.
        simpl.
        apply valid_execution_fragment_pos in Hv1.
        simpl in Hv1.
        rewrite <-Hv1.
        apply disjoint_remove_r; auto.
        simpl in H2.
        simpl.
        simpl in *.
        apply valid_execution_fragment_pos in Hv1.
        simpl in Hv1.
        rewrite <-Hv1.
        apply remove_preserves_ok; auto.
        simpl in *.
        apply valid_execution_fragment_pos in Hv1.
        simpl in Hv1.
        rewrite <-Hv1. intuition.
    -- destruct q.
    -- destruct r.
Qed.

Lemma valid_execution_fragment_compatible_tensor_pos: forall s s' acts,
  valid_execution_fragment (tensor L1 L2) s s' acts ->
  compatible_tensor_pos s.(L1State).(PidPos) s.(L2State).(PidPos) acts.
Proof.
  induction 1; simpl; intros.
  - auto.
  - inversion H; subst; simpl in *;
    inversion H1; subst;
    assumption.
  - inversion H; subst.
  - inversion H; subst.
  - inversion H; subst; simpl in *;
    inversion H1; subst; intuition.
  - inversion H; subst; simpl in *;
    inversion H1; subst; intuition.
Qed.

End TensorTrace.

Section Refinement.

Context {liA liB : language_interface }.

Lemma refines_tensor_refines_r: forall (L1 L1' : lts li_null liA) (L2 : lts li_null liB),
	refines (sync L1) (sync L1') ->
	refines (tensor L1 L2) (tensor L1' L2).
Proof.
  intros.
  unfold refines. intros.
  unfold refines in H.
  unfold in_traces in H0.
  destruct H0 as [init [final [Hnew Hvalid]]].
  assert (Hcompatible : compatible_tensor_pos init.(L1State).(PidPos) init.(L2State).(PidPos) acts).
  eapply valid_execution_fragment_compatible_tensor_pos; eauto.
  assert (Hvalidtmp : 
    valid_execution_fragment (tensor L3 L4) init final acts).
  assumption.
  apply valid_execution_fragment_com in Hvalidtmp.
  apply valid_execution_fragment_com' in Hvalid.
  assert (in_traces (sync L1') (gatherL1 acts)).
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

Lemma refines_tensor_refines_l: forall (L1 : lts li_null liA) (L2 L2' : lts li_null liB),
	refines (sync L2) (sync L2') ->
	refines (tensor L1 L2) (tensor L1 L2').
Proof.
  intros.
  unfold refines. intros.
  unfold refines in H.
  unfold in_traces in H0.
  destruct H0 as [init [final [Hnew Hvalid]]].
  assert (Hcompatible : compatible_tensor_pos init.(L1State).(PidPos) init.(L2State).(PidPos) acts).
  eapply valid_execution_fragment_compatible_tensor_pos; eauto.
  assert (Hvalidtmp : valid_execution_fragment 
    (tensor L3 L4) init final acts).
  assumption.
  apply valid_execution_fragment_com in Hvalidtmp.
  apply valid_execution_fragment_com' in Hvalid.
  assert (in_traces (sync L2') (gatherL2 acts)).
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
  simpl. inversion Hnew'.
  rewrite H3.
  unfold disjoint. intuition.
  inversion H4. apply notin_empty.
  simpl.
  inversion H0.
  rewrite H6. apply notin_empty.
  simpl.
  inversion H0; subst.
  rewrite H3. econstructor.
  simpl.
  inversion Hnew'.
  rewrite H3. econstructor.
  simpl.
  inversion H1; subst.
  rewrite H3 in Hcompatible.
  inversion Hnew'.
  rewrite H5. assumption.
Qed.

Theorem tensor_preserves_refines: forall (L1 L1' : lts li_null liA) (L2 L2' : lts li_null liB),
	(sync L1) ⊑' (sync L1') ->
	(sync L2) ⊑' (sync L2') ->
	(L1 ⊗-' L2) ⊑' (L1' ⊗-' L2').
Proof.
	intros.
	eapply trans_refinement.
	eapply refines_tensor_refines_r; eauto.
	eapply refines_tensor_refines_l; eauto.
Qed.

End Refinement.