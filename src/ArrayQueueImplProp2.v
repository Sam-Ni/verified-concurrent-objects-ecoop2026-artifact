Require Import
  Arith
  List
  LibVar
  LibEnv
  LTS
  SyncLTS
  VeriTactics
  ArrayQueueImpl
  ArrayQueueImplProp
.
Import ListNotations.

Section Properties.

Variable L : nat.

Lemma noB_preserves_ADeq28_combine: forall (acts : list event) st st' pid,
  valid_execution_fragment (array_queue_impl L) st st' acts ->
  binds pid ADeq28 st.(pc) ->
  gather_pid_A_from_AB pid acts = [] ->
  st.(x) pid = st'.(x) pid /\
  st.(front) pid = st'.(front) pid.
Proof.
  intros.
  intuition.
  eapply noB_preserves_ADeq28'; eauto.
  eapply noB_preserves_ADeq28''; eauto.
Qed.

End Properties.