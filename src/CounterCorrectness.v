Require Import
  LTS
  Refinement
  SyncLTS
  ImplRefinement
  Compose
  VerifiedConcurrentObject
  Register
  Counter
  RegisterCounterImpl
  RegisterProp
  CounterProp
  RegisterCounterImplProp
  RegisterCounterCorrect.

Section VerifiedCounter.

Lemma verified_counter:
  veriobj Register register_counter_impl counter.
Proof.
  unfold veriobj.
  intuition.
  apply register_sync.
  apply register_counter_impl_sync.
  eapply trans_refinement; eauto.
  apply register_counter_correct.
  apply counter_sync.
Qed.

End VerifiedCounter.

