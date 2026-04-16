Require Import
	List
  Nat
  Arith
  LibVar
	LTS
	Refinement
  SyncLTS
  Tensor.
Require LibEnv.
Import ListNotations.

Arguments queryL {liA liB}.
Arguments queryR {liA liB}.
Arguments replyL {liA liB}.
Arguments replyR {liA liB}.

Section TensorLTS.
  Context {liA liB : language_interface}.
  Context {liC liD : language_interface}.
  Variable _M1 : lts liA liB.
  Variable _M2 : lts liC liD.

  Definition M1 := sync _M1.
  Definition M2 := sync _M2.

  Record tensor_state : Type := mkTensorState {
    L1State : M1.(state);
    L2State : M2.(state);
  }.

  Inductive tensor_internal : Type :=
  | intL1 (act : M1.(internal))
  | intL2 (act : M2.(internal)).

  Definition tensor_new_state tst : Prop := 
    M1.(new_state) tst.(L1State) /\ 
    M2.(new_state) tst.(L2State).

  Import LibEnv.

  Inductive tensor_initial_state : tensor_state -> Pid -> (tensor_query liB liD) -> tensor_state -> Prop :=
  | tensor_initial_state_M2 : forall tst tst' st2 st2' qd st1 pid
      (Hnotin: pid # st1.(PidPos)),
      initial_state M2 st2 pid qd st2' ->
      tst = mkTensorState st1 st2 ->
      tst' = mkTensorState st1 st2' ->
      tensor_initial_state tst pid (queryR qd) tst'
  | tensor_initial_state_M1 : forall tst tst' st1 st1' qb st2 pid
      (Hnotin: pid # st2.(PidPos)),
      initial_state M1 st1 pid qb st1' ->
      tst = mkTensorState st1 st2 ->
      tst' = mkTensorState st1' st2 ->
      tensor_initial_state tst pid (queryL qb) tst'
  .

  Inductive tensor_step : tensor_state -> Pid -> tensor_internal -> tensor_state -> Prop :=
  | tensor_step_LM_internal : forall st1 st2 st2' act tst tst' pid
      (Hbinds : binds pid Run st2.(PidPos))
      (Hnotin: pid # st1.(PidPos)),
      step M2 st2 pid act st2' ->
      tst = mkTensorState st1 st2 ->
      tst' = mkTensorState st1 st2' ->
      tensor_step tst pid (intL2 act) tst'
  | tensor_step_M1_internal : forall st1 st2 st1' act tst tst' pid
      (Hbinds : binds pid Run st1.(PidPos))
      (Hnotin: pid # st2.(PidPos)),
      step M1 st1 pid act st1' ->
      tst = mkTensorState st1 st2 ->
      tst' = mkTensorState st1' st2 ->
      tensor_step tst pid (intL1 act) tst'
  .

  Inductive tensor_at_external : tensor_state -> Pid -> (tensor_query liA liC) -> tensor_state -> Prop :=
  | tensor_at_external_M2 : forall tst tst' st2 st2' qc st1 pid
      (Hnotin: pid # st1.(PidPos)),
      at_external M2 st2 pid qc st2' ->
      tst = mkTensorState st1 st2 ->
      tst' = mkTensorState st1 st2' ->
      tensor_at_external tst pid (queryR qc) tst'
  | tensor_at_external_M1 : forall tst tst' st1 st1' qa st2 pid
      (Hnotin: pid # st2.(PidPos)),
      at_external M1 st1 pid qa st1' ->
      tst = mkTensorState st1 st2 ->
      tst' = mkTensorState st1' st2 ->
      tensor_at_external tst pid (queryL qa) tst'
  .

  Inductive tensor_after_external : tensor_state -> Pid -> (tensor_reply liA liC) -> tensor_state -> Prop :=
  | tensor_after_external_M2 : forall st1 st2 rc st2' tst tst' pid
      (Hnotin: pid # st1.(PidPos)),
      after_external M2 st2 pid rc st2' ->
      tst = mkTensorState st1 st2 ->
      tst' = mkTensorState st1 st2' ->
      tensor_after_external tst pid (replyR rc) tst'
  | tensor_after_external_M1 : forall st1 st2 ra st1' tst tst' pid
      (Hnotin: pid # st2.(PidPos)),
      after_external M1 st1 pid ra st1' ->
      tst = mkTensorState st1 st2 ->
      tst' = mkTensorState st1' st2 ->
      tensor_after_external tst pid (replyL ra) tst'
  .

  Inductive tensor_final_state : tensor_state -> Pid -> (tensor_reply liB liD) -> tensor_state -> Prop :=
  | tensor_final_state_M2 : forall st1 st2 rd st2' tst tst' pid
      (Hbinds : binds pid Run st2.(PidPos))
      (Hnotin: pid # st1.(PidPos)),
      final_state M2 st2 pid rd st2' ->
      tst = mkTensorState st1 st2 ->
      tst' = mkTensorState st1 st2' ->
      tensor_final_state tst pid (replyR rd) tst'
  | tensor_final_state_M1 : forall st1 st2 rb st1' tst tst' pid
      (Hbinds : binds pid Run st1.(PidPos))
      (Hnotin: pid # st2.(PidPos)),
      final_state M1 st1 pid rb st1' ->
      tst = mkTensorState st1 st2 ->
      tst' = mkTensorState st1' st2 ->
      tensor_final_state tst pid (replyL rb) tst'
  .

  Definition tensor
    : lts (tensor_li liA liC) (tensor_li liB liD)
    := mkLTS (tensor_li liA liC) (tensor_li liB liD)
      tensor_state
      tensor_internal
      tensor_step
      tensor_new_state
      tensor_initial_state
      tensor_at_external
      tensor_after_external
      tensor_final_state.

End TensorLTS.

Arguments L1State {liA liB liC liD _M1 _M2}.
Arguments L2State {liA liB liC liD _M1 _M2}.
Arguments mkTensorState {liA liB liC liD _M1 _M2}.

Notation " M ⊗- M' " := (ImplTensor.tensor M M') (at level 67).