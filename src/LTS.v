Require Import
  List
  Nat.
From VCO Require LibEnv.
Import ListNotations.

(*
  Concurrent objects are formalized as (restricted) labeled transition systems (lts).
*)

Notation Pid := nat.

Section LTS.

(* 
  A general lts is parameterized with language interfaces liA and liB
  (the name'language interface' is adopted from CompCert.
  The name 'object interface' or 'type interface' is more appropriate in this context).

  The functions called by the lts are specified in liA and
  the functions provided by the lts are specified in liB.
  A function is specified with its invocations (query) and responses (reply).
*)
Structure language_interface :=
  mk_language_interface {
    query: Type;
    reply: Type;
  }.

(* 
  A lts comprises of 
  state - set of possible values of variables in the lts (e.g., value in a register object)
  internal - set of internal actions which are not observable by environment (e.g., assignment)
  step - transition enabled by internal actions
  new_state - set of states when the lts is created (e.g., constructors in c++)
  initial_state - transition enabled by query in liB
  at_external - transition enabled by query in liA
  after_external - transition enabled by reply in liB
  final_state - transition enable by reply in liB.

  A lts is created in the new_state,
  waiting for queries from the environment.

  When it gets query 'q' from process 'pid',
  its state get updated through initial_state, which marks that q from pid started.
  Then the lts can do one of the following things (if enabled):
  1. get another query q' in liB
  2. progress in the query q through step
  3. call external functions in liA through at_external
  4. get a reply from external functions in liA through after_external
  5. reply the query q in liB through final_state
*)
Record lts liA liB: Type := mkLTS {
  state : Type;
  internal : Type;
  step : state -> Pid -> internal -> state -> Prop;
  new_state : state -> Prop;
  initial_state: state -> Pid -> query liB -> state -> Prop;
  at_external: state -> Pid -> query liA -> state -> Prop;
  after_external: state -> Pid -> reply liA -> state -> Prop;
  final_state: state -> Pid -> reply liB -> state -> Prop;
}.

(* 
  Special language interface with no queries and replies.
  A concurrent object can be formalized as lts li_null liB.
  We can get such an object by composing its implementation of type lts liA liB
  with lower objects of type lts li_null liA (see Section LINK).
*)
Definition li_null :=
  {|
    query := Empty_set;
    reply := Empty_set;
  |}.

End LTS.

Arguments state {liA} {liB}.
Arguments internal {liA} {liB}.
Arguments step {liA} {liB}.
Arguments new_state {liA} {liB}.
Arguments initial_state {liA} {liB}.
Arguments at_external {liA} {liB}.
Arguments after_external {liA} {liB}.
Arguments final_state {liA} {liB}.

(* 
  An object (of type lts li_null liB) can be specified by its observable executions from new_state.
  A possible execution can be described by a list of events.
*)
Section Trace.

Context {liA liB : language_interface}.
Variable L: lts liA liB.

Definition automaton_step st st' : Prop :=
  exists pid,
  ((exists qb, initial_state L st pid qb st') \/
  (exists rb, final_state L st pid rb st') \/
  (exists qa, at_external L st pid qa st') \/
  (exists ra, after_external L st pid ra st') \/
  (exists int, step L st pid int st')
  ).

Inductive _event :=
| event_invB : query liB -> _event
| event_resB : reply liB -> _event
| event_invA : query liA -> _event
| event_resA : reply liA -> _event
.

Definition event := (nat * _event)%type.

(* 
  valid_execution_fragment records the list of events from state st to st'.
*)
Inductive valid_execution_fragment (st st' : L.(state)) : list event -> Prop :=
| Step_None :
    st = st' ->
    valid_execution_fragment st st' nil
| Step_Internal : forall st'' acts (int : L.(internal)) pid,
    step L st pid int st'' ->
    valid_execution_fragment st'' st' acts ->
    valid_execution_fragment st st' acts
| Step_At_External : forall st'' acts qa pid,
    at_external L st pid qa st'' ->
    valid_execution_fragment st'' st' acts ->
    valid_execution_fragment st st' ((pid, event_invA qa) :: acts)
| Step_After_External : forall st'' acts ra pid,
    after_external L st pid ra st'' ->
    valid_execution_fragment st'' st' acts ->
    valid_execution_fragment st st' ((pid, event_resA ra) :: acts)
| Step_Initial_Call : forall st'' acts qb pid,
    initial_state L st pid qb st'' ->
    valid_execution_fragment st'' st' acts ->
    valid_execution_fragment st st' ((pid, event_invB qb) :: acts)
| Step_Final_Return : forall st'' acts rb pid,
    final_state L st pid rb st'' ->
    valid_execution_fragment st'' st' acts ->
    valid_execution_fragment st st' ((pid, event_resB rb) :: acts)
.

Hint Constructors valid_execution_fragment : core.

Lemma valid_execution_fragment_join : forall (s s' s'' : L.(state)) a a',
    valid_execution_fragment s s' a ->
    valid_execution_fragment s' s'' a' ->
    valid_execution_fragment s s'' (a ++ a').
Proof.
  intros.
  induction H; subst; simpl; intros; eauto.
Qed.

Lemma valid_execution_fragment_join' : forall (s s' s'' : L.(state)) a a' a'',
    valid_execution_fragment s s' a ->
    valid_execution_fragment s' s'' a' ->
    a'' = a ++ a' ->
    valid_execution_fragment s s'' a''.
Proof.
  intros; subst; eauto using valid_execution_fragment_join.
Qed.

Lemma valid_execution_fragment_inv: forall st st' pid act acts,
  valid_execution_fragment st st' ((pid, act):: acts) ->
  exists st'', valid_execution_fragment st st'' [(pid, act)] /\
                valid_execution_fragment st'' st' acts.
Proof.
  intros. remember ((pid, act):: acts) as aacts.
  induction H; intuition.
  - inversion Heqaacts.
  - destruct H1 as [st''' [Hv1 Hv2]].
    exists st'''. intuition.
    eapply valid_execution_fragment_join' with (a:=[]); eauto.
  - inversion Heqaacts; subst.
    exists st''. intuition.
    eapply Step_At_External; eauto.
  - inversion Heqaacts; subst.
    exists st''. intuition.
    eapply Step_After_External; eauto.
  - inversion Heqaacts; subst.
    exists st''. intuition.
    eapply Step_Initial_Call; eauto.
  - inversion Heqaacts; subst.
    exists st''. intuition.
    eapply Step_Final_Return; eauto.
Qed.

Lemma valid_execution_fragment_inv1: forall st st' pid qb,
  valid_execution_fragment st st' ((pid, event_invB qb):: nil) ->
  exists st'' st''', 
    valid_execution_fragment st st'' nil /\
    initial_state L st'' pid qb st''' /\
    valid_execution_fragment st''' st' nil.
Proof.
  intros. remember [(pid, event_invB qb)] as aacts.
  induction H; intuition.
  all : inversion Heqaacts.
  - subst.  destruct H1 as [st''' [st'''' [Hv1 [Hinit Hv2]]]].
    exists st'''. exists st''''.
    intuition.
    eapply Step_Internal; eauto.
  - subst.
    exists st. exists st''.
    intuition.
Qed.

Lemma valid_execution_fragment_inv1': forall st st' pid rb,
  valid_execution_fragment st st' ((pid, event_resB rb):: nil) ->
  exists st'' st''', 
    valid_execution_fragment st st'' nil /\
    final_state L st'' pid rb st''' /\
    valid_execution_fragment st''' st' nil.
Proof.
  intros. remember [(pid, event_resB rb)] as aacts.
  induction H; intuition.
  all : inversion Heqaacts.
  - subst.  destruct H1 as [st''' [st'''' [Hv1 [Hinit Hv2]]]].
    exists st'''. exists st''''.
    intuition.
    eapply Step_Internal; eauto.
  - subst.
    exists st. exists st''.
    intuition.
Qed.

Fixpoint gather_pid_external_events events pid : list event :=
  match events with
  | nil => nil
  | (pid', act) :: events' =>
      let remaining_events := gather_pid_external_events events' pid in
      if pid =? pid' then (pid', act) :: remaining_events
                      else remaining_events
  end.

Fixpoint get_pid_events (acts : list event) (pid : Pid) :=
  match acts with
  | nil => nil
  | (pid', act) :: acts' =>
    let events' := get_pid_events acts' pid in
    if pid' =? pid then act :: events'
    else events'
  end.

Fixpoint gather_pid_B_events (acts : list event) (pid : Pid) :=
  match acts with
  | nil => nil
  | (pid', act) :: acts' =>
    let events' := gather_pid_B_events acts' pid in
    if pid =? pid' then
      match act with
      | event_invB _ => (pid, act) :: events'
      | event_resB _ => (pid, act) :: events'
      | event_invA _ => events'
      | event_resA _ => events'
      end
    else events'
  end.

(* 
  A list of events 'acts' is a trace of the object
  if 'acts' is an execution from new_state to some state.
*)
Definition in_traces acts :=
  exists init final, L.(new_state) init /\ valid_execution_fragment init final acts.

Definition reachable st :=
  exists init acts, L.(new_state) init /\ valid_execution_fragment init st acts.

Definition invariant (P : state L -> Prop) :=
  forall st, reachable st -> P st.

Definition invariant_ind (P : state L -> Prop) :=
  (forall st, L.(new_state) st -> P st) /\
  (forall st st' act pid,
    P st ->
    step L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    initial_state L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    at_external L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    after_external L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    final_state L st pid act st' ->
    P st').

Fixpoint gather_pid_A_from_AB pid (acts : list event) : list event :=
  match acts with
  | nil => nil
  | (pid', act) :: acts' =>
    let events' := gather_pid_A_from_AB pid acts' in
    if (pid =? pid') then
      match act with
      | event_invA _ => (pid, act) :: events'
      | event_resA _ => (pid, act) :: events'
      | event_invB _ => events'
      | event_resB _ => events'
      end
    else events'
  end.

Lemma invariant_ind_land: forall P Q,
  invariant_ind P ->
  invariant_ind Q ->
  invariant_ind (fun x => P x /\ Q x).
Proof.
  intros.
  destruct H as [Hnew [Hstep [Hinit [Hat [Hafter Hfinal]]]]].
  destruct H0 as [Hnew' [Hstep' [Hinit' [Hat' [Hafter' Hfinal']]]]].
  unfold invariant_ind. intuition.
  - apply Hstep in H0; intuition.
  - apply Hstep' in H0; intuition.
  - apply Hinit in H0; intuition.
  - apply Hinit' in H0; intuition.
  - apply Hat in H0; intuition.
  - apply Hat' in H0; intuition.
  - apply Hafter in H0; intuition.
  - apply Hafter' in H0; intuition.
  - apply Hfinal in H0; intuition.
  - apply Hfinal' in H0; intuition.
Qed.

Lemma gather_pid_A_from_AB_dist : forall (acts : list event) acts' pid,
  gather_pid_A_from_AB pid (acts ++ acts') = gather_pid_A_from_AB pid acts ++ gather_pid_A_from_AB pid acts'.
Proof.
  induction acts; simpl; intros; intuition.
  destruct a.
  destruct (pid =? n);
  destruct _e; simpl; f_equal; intuition.
Qed.

Lemma gather_pid_B_events_dist : forall (acts : list event) acts' pid,
  gather_pid_B_events (acts ++ acts') pid =
  gather_pid_B_events acts pid ++ gather_pid_B_events acts' pid.
Proof.
  induction acts; simpl; intros; intuition.
  destruct a.
  destruct (pid =? n);
  destruct _e; simpl; f_equal; intuition.
Qed.

End Trace.

Module composed_lts.

Record composed_lts liA liB liC : Type := mkComposedLTS {
  state : Type;
  internal_L1 : Type;
  internal_L2 : Type;
  step_L1 : state -> Pid -> internal_L1 -> state -> Prop;
  step_L2 : state -> Pid -> internal_L2 -> state -> Prop;
  new_state : state -> Prop;
  initial_state: state -> Pid -> query liC -> state -> Prop;
  at_external: state -> Pid -> query liA -> state -> Prop;
  after_external: state -> Pid -> reply liA -> state -> Prop;
  final_state: state -> Pid -> reply liC -> state -> Prop;
  internal_query : state -> Pid -> query liB -> state -> Prop;
  internal_reply : state -> Pid -> reply liB -> state -> Prop;
}.

Arguments state {liA} {liB} {liC}.
Arguments internal_L1 {liA} {liB} {liC}.
Arguments internal_L2 {liA} {liB} {liC}.
Arguments step_L1 {liA} {liB} {liC}.
Arguments step_L2 {liA} {liB} {liC}.
Arguments new_state {liA} {liB} {liC}.
Arguments initial_state {liA} {liB} {liC}.
Arguments at_external {liA} {liB} {liC}.
Arguments after_external {liA} {liB} {liC}.
Arguments final_state {liA} {liB} {liC}.
Arguments internal_query {liA} {liB} {liC}.
Arguments internal_reply {liA} {liB} {liC}.

Section Trace.

Context {liA liB liC : language_interface}.
Variable L: composed_lts liA liB liC.

Inductive _event :=
| event_invC : query liC -> _event
| event_resC : reply liC -> _event
| event_invB : query liB -> _event
| event_resB : reply liB -> _event
| event_invA : query liA -> _event
| event_resA : reply liA -> _event
.

Definition event := (nat * _event)%type.

Inductive valid_execution_fragment (st st' : L.(state)) : list event -> Prop :=
| Step_None :
    st = st' ->
    valid_execution_fragment st st' nil
| Step_Internal_L1 : forall st'' acts (int : L.(internal_L1)) pid,
    step_L1 L st pid int st'' ->
    valid_execution_fragment st'' st' acts ->
    valid_execution_fragment st st' acts
| Step_Internal_L2 : forall st'' acts (int : L.(internal_L2)) pid,
    step_L2 L st pid int st'' ->
    valid_execution_fragment st'' st' acts ->
    valid_execution_fragment st st' acts
| Step_At_External : forall st'' acts qa pid,
    at_external L st pid qa st'' ->
    valid_execution_fragment st'' st' acts ->
    valid_execution_fragment st st' ((pid, event_invA qa) :: acts)
| Step_After_External : forall st'' acts ra pid,
    after_external L st pid ra st'' ->
    valid_execution_fragment st'' st' acts ->
    valid_execution_fragment st st' ((pid, event_resA ra) :: acts)
| Step_Initial_Call : forall st'' acts qc pid,
    initial_state L st pid qc st'' ->
    valid_execution_fragment st'' st' acts ->
    valid_execution_fragment st st' ((pid, event_invC qc) :: acts)
| Step_Final_Return : forall st'' acts rc pid,
    final_state L st pid rc st'' ->
    valid_execution_fragment st'' st' acts ->
    valid_execution_fragment st st' ((pid, event_resC rc) :: acts)
| Step_Internal_Query : forall st'' acts qb pid,
    internal_query L st pid qb st'' ->
    valid_execution_fragment st'' st' acts ->
    valid_execution_fragment st st' ((pid, event_invB qb) :: acts)
| Step_Internal_Reply : forall st'' acts rb pid,
    internal_reply L st pid rb st'' ->
    valid_execution_fragment st'' st' acts ->
    valid_execution_fragment st st' ((pid, event_resB rb) :: acts)
.

Hint Constructors valid_execution_fragment : core.

Lemma valid_execution_fragment_join : forall (s s' s'' : L.(state)) a a',
  valid_execution_fragment s s' a ->
  valid_execution_fragment s' s'' a' ->
  valid_execution_fragment s s'' (a ++ a').
Proof.
  intros.
  induction H; subst; simpl; intros; eauto.
Qed.

Lemma valid_execution_fragment_join' : forall (s s' s'' : L.(state)) a a' a'',
    valid_execution_fragment s s' a ->
    valid_execution_fragment s' s'' a' ->
    a'' = a ++ a' ->
    valid_execution_fragment s s'' a''.
Proof.
  intros; subst; eauto using valid_execution_fragment_join.
Qed.

Fixpoint gather_pid_external_events events pid : list event :=
  match events with
  | nil => nil
  | (pid', act) :: events' =>
      let remaining_events := gather_pid_external_events events' pid in
      if pid =? pid' then (pid', act) :: remaining_events
                      else remaining_events
  end.

Definition in_traces acts :=
  exists init final, L.(new_state) init /\ valid_execution_fragment init final acts.

Definition reachable st :=
  exists init acts, L.(new_state) init /\ valid_execution_fragment init st acts.

Definition invariant (P : state L -> Prop) :=
  forall st, reachable st -> P st.

Definition invariant_ind (P : state L -> Prop) :=
  (forall st, L.(new_state) st -> P st) /\
  (forall st st' act pid,
    P st ->
    step_L1 L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    step_L2 L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    initial_state L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    at_external L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    after_external L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    final_state L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    internal_query L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    internal_reply L st pid act st' ->
    P st')
    .

Lemma invariant_ind_land: forall P Q,
  invariant_ind P ->
  invariant_ind Q ->
  invariant_ind (fun x => P x /\ Q x).
Proof.
  intros.
  destruct H as [Hnew [Hstep [Hstep1 [Hinit [Hat [Hafter [Hfinal [Hiq Hir]]]]]]]].
  destruct H0 as [Hnew' [Hstep' [Hstep1' [Hinit' [Hat' [Hafter' [Hfinal' [Hiq' Hir']]]]]]]].
  unfold invariant_ind. intuition.
  - apply Hstep in H0; intuition.
  - apply Hstep' in H0; intuition.
  - apply Hstep1 in H0; intuition.
  - apply Hstep1' in H0; intuition.
  - apply Hinit in H0; intuition.
  - apply Hinit' in H0; intuition.
  - apply Hat in H0; intuition.
  - apply Hat' in H0; intuition.
  - apply Hafter in H0; intuition.
  - apply Hafter' in H0; intuition.
  - apply Hfinal in H0; intuition.
  - apply Hfinal' in H0; intuition.
  - apply Hiq in H0; intuition.
  - apply Hiq' in H0; intuition.
  - apply Hir in H0; intuition.
  - apply Hir' in H0; intuition.
Qed.

End Trace.

End composed_lts.

Section ComposedEvent.

Context {liA liB liC : language_interface}.

Fixpoint clts_events_B_to_events_B (acts : list (@composed_lts.event liA liB liC)) : list (@event liB liC) :=
  match acts with
  | nil => nil
  | (pid, act) :: acts' =>
    let events' := clts_events_B_to_events_B acts' in
    match act with
    | composed_lts.event_invB qb => (pid, event_invA qb) :: events'
    | composed_lts.event_resB rb => (pid, event_resA rb) :: events'
    | composed_lts.event_invC _ => events'
    | composed_lts.event_resC _ => events'
    | composed_lts.event_invA _ => events'
    | composed_lts.event_resA _ => events'
    end
  end.

Fixpoint gatherBC (acts : list (@composed_lts.event liA liB liC)) : list event :=
  match acts with
  | nil => nil
  | (pid, act) :: acts' =>
    let eventsBC' := gatherBC acts' in
    match act with
    | composed_lts.event_invB qb => (pid, event_invA qb) :: eventsBC'
    | composed_lts.event_resB rb => (pid, event_resA rb) :: eventsBC'
    | composed_lts.event_invC qc => (pid, event_invB qc) :: eventsBC'
    | composed_lts.event_resC rc => (pid, event_resB rc) :: eventsBC'
    | _ => eventsBC'
    end
  end.

Fixpoint gather_pid_events_B pid (acts : list (@composed_lts.event liA liB liC)) :=
  match acts with
  | nil => nil
  | (pid', act) :: acts' =>
    let events' := gather_pid_events_B pid acts' in
    if (pid =? pid') then
      match act with
      | composed_lts.event_invC _ => events'
      | composed_lts.event_resC _ => events'
      | composed_lts.event_invB _ => (pid, act) :: events'
      | composed_lts.event_resB _ => (pid, act) :: events'
      | composed_lts.event_invA _ => events'
      | composed_lts.event_resA _ => events'
      end
    else events'
  end.

Lemma gatherBC_dist : forall (acts : list (@composed_lts.event liA liB liC)) acts',
  gatherBC (acts ++ acts') = gatherBC acts ++ gatherBC acts'.
Proof.
  induction acts; simpl; intros; intuition.
  destruct a. destruct _e; simpl; f_equal; intuition.
Qed.

Lemma gather_pid_events_B_dist: forall acts acts' pid,
  gather_pid_events_B pid (acts ++ acts') =
  gather_pid_events_B pid acts ++ gather_pid_events_B pid acts'.
Proof.
  induction acts; simpl; intros.
  - reflexivity.
  - destruct a.
    destruct (pid =? n)eqn:Heq;
    destruct _e; simpl;
      try f_equal; intuition.
Qed.

Lemma clts_events_B_to_events_B_dist : forall (acts : list (@composed_lts.event liA liB liC)) acts',
  clts_events_B_to_events_B (acts ++ acts') = clts_events_B_to_events_B acts ++ clts_events_B_to_events_B acts'.
Proof.
  induction acts; simpl; intros; intuition.
  destruct a. destruct _e; simpl; f_equal; intuition.
Qed.

Lemma gatherBC_gather_pid_A_from_AB_equal_gather_pid_events_B:
  forall acts pid,
  gather_pid_A_from_AB pid (gatherBC acts) = clts_events_B_to_events_B (gather_pid_events_B pid acts).
Proof.
  induction acts; intros.
  - simpl. reflexivity.
  - replace (a :: acts) with ([a] ++ acts).
    rewrite gatherBC_dist.
    rewrite gather_pid_events_B_dist.
    rewrite gather_pid_A_from_AB_dist.
    rewrite clts_events_B_to_events_B_dist.
    rewrite IHacts. simpl.
    destruct a. destruct _e; simpl;
    destruct (pid =? n); simpl; reflexivity.
    simpl; reflexivity.
Qed.

Fixpoint gather_pid_events_C pid (acts : list (@composed_lts.event liA liB liC)) :=
  match acts with
  | nil => nil
  | (pid', act) :: acts' =>
    let events' := gather_pid_events_C pid acts' in
    if (pid =? pid') then
      match act with
      | composed_lts.event_invB _ => events'
      | composed_lts.event_resB _ => events'
      | composed_lts.event_invC _ => (pid, act) :: events'
      | composed_lts.event_resC _ => (pid, act) :: events'
      | composed_lts.event_invA _ => events'
      | composed_lts.event_resA _ => events'
      end
    else events'
  end.

Lemma gather_pid_events_C_dist: forall acts acts' pid,
  gather_pid_events_C pid (acts ++ acts') =
  gather_pid_events_C pid acts ++ gather_pid_events_C pid acts'.
Proof.
  induction acts; simpl; intros.
  - reflexivity.
  - destruct a.
    destruct (pid =? n)eqn:Heq;
    destruct _e; simpl;
      try f_equal; intuition.
Qed.
  
End ComposedEvent.

Section Trace.
  
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

End Trace.

Section RAWCOMPOSITION.
  Context {liA liB: language_interface}.
  Variable L1: lts li_null liA.
  Variable L2: lts liA liB.

  Record raw_composed_state : Type := mkRawComposedState {
    RawL1State : L1.(state);
    RawL2State : L2.(state);
  }.

  Definition raw_composed_internal_L1 := L1.(internal).
  Definition raw_composed_internal_L2 := L2.(internal).

  Definition raw_composed_new_state lst : Prop :=
    L1.(new_state) lst.(RawL1State) /\ 
    L2.(new_state) lst.(RawL2State).

  Inductive raw_composed_initial_state : raw_composed_state -> Pid -> query liB -> raw_composed_state -> Prop :=
  | raw_composed_initial_state_L2 : forall lst lst' st2 st2' qc st1 pid,
      initial_state L2 st2 pid qc st2' ->
      lst = mkRawComposedState st1 st2 ->
      lst' = mkRawComposedState st1 st2' ->
      raw_composed_initial_state lst pid qc lst'
  .

  Import LibEnv.

  Inductive raw_composed_step_L2 : raw_composed_state -> Pid -> raw_composed_internal_L2 -> raw_composed_state -> Prop :=
  | raw_composed_step_L2_internal : forall st1 st2 st2' act lst lst' pid,
      step L2 st2 pid act st2' ->
      lst = mkRawComposedState st1 st2 ->
      lst' = mkRawComposedState st1 st2' ->
      raw_composed_step_L2 lst pid act lst'.

  Inductive raw_composed_step_L1 : raw_composed_state -> Pid -> raw_composed_internal_L1 -> raw_composed_state -> Prop :=
  | raw_composed_step_L1_internal : forall st1 st2 st1' act lst lst' pid,
      step L1 st1 pid act st1' ->
      lst = mkRawComposedState st1 st2 ->
      lst' = mkRawComposedState st1' st2 ->
      raw_composed_step_L1 lst pid act lst'
  .

  Inductive raw_composed_at_external : raw_composed_state -> Pid -> query li_null -> raw_composed_state -> Prop := .

  Inductive raw_composed_after_external : raw_composed_state -> Pid -> reply li_null -> raw_composed_state -> Prop := .

  Inductive raw_composed_final_state : raw_composed_state -> Pid -> reply liB -> raw_composed_state -> Prop :=
  | raw_composed_final_state_L2 : forall st1 st2 rc st2' lst lst' pid,
      final_state L2 st2 pid rc st2' ->
      lst = mkRawComposedState st1 st2 ->
      lst' = mkRawComposedState st1 st2' ->
      raw_composed_final_state lst pid rc lst'
  .

  Inductive raw_composed_internal_query : raw_composed_state -> Pid -> query liA -> raw_composed_state -> Prop :=
  | raw_composed_step_L2_push : forall st1 st2 st1' qb lst lst' st2' pid,
      at_external L2 st2 pid qb st2' ->
      lst = mkRawComposedState st1 st2 ->
      initial_state L1 st1 pid qb st1' ->
      lst' = mkRawComposedState st1' st2' ->
      raw_composed_internal_query lst pid qb lst'
  .

  Inductive raw_composed_internal_reply : raw_composed_state -> Pid -> reply liA -> raw_composed_state -> Prop :=
  | raw_composed_step_L1_pop : forall st1 st1' rb st2 st2' lst lst' pid,
      final_state L1 st1 pid rb st1' ->
      after_external L2 st2 pid rb st2' ->
      lst = mkRawComposedState st1 st2 ->
      lst' = mkRawComposedState st1' st2' ->
      raw_composed_internal_reply lst pid rb lst'
  .

  Definition raw_compose : composed_lts.composed_lts li_null liA liB :=
    composed_lts.mkComposedLTS li_null liA liB
      raw_composed_state
      raw_composed_internal_L1
      raw_composed_internal_L2
      raw_composed_step_L1
      raw_composed_step_L2
      raw_composed_new_state
      raw_composed_initial_state
      raw_composed_at_external
      raw_composed_after_external
      raw_composed_final_state
      raw_composed_internal_query
      raw_composed_internal_reply.

End RAWCOMPOSITION.

Arguments RawL1State {liA liB L1 L2}.
Arguments RawL2State {liA liB L1 L2}.
Arguments raw_compose {liA liB}.
Arguments mkRawComposedState {liA liB L1 L2}.

Section LINK.

Context {liA liB: language_interface}.
Variable L : composed_lts.composed_lts li_null liA liB.

Definition linked_state := composed_lts.state L.

Inductive linked_internal : Type :=
| intIntL1 (act : composed_lts.internal_L1 L)
| intIntL2 (act : composed_lts.internal_L2 L)
| intQuery (act : query liA)
| intReply (act : reply liA).

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

Definition linked_lts : lts li_null liB :=
  mkLTS li_null liB linked_state
    linked_internal
    linked_step
    linked_new_state
    linked_initial_state
    linked_at_external
    linked_after_external
    linked_final_state.

End LINK.

Arguments linked_after_external {liA liB L}.
Arguments intQuery {liA liB L}.
Arguments intReply {liA liB L}.

Notation " L ◁' M " := (LTS.linked_lts (LTS.raw_compose L M)) (at level 67).