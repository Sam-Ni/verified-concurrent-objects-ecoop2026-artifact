Require Import
  LTS
  Compose
  SyncLTS
  Link
  RegisterCounter
  Register
  RegisterCounterImpl
  Counter
  CounterProp
  CounterTimer
  CounterTimerImpl
  Timer
  Refinement
  RegisterCounterCorrect
  CounterTimerCorrect
  VE.

Section RegisterTimer.

Definition register_timer : lts li_null li_timer :=
  linked_lts 
    (compose 
      (linked_lts (raw_compose Register register_counter_impl))
      counter_timer_impl).

Theorem register_timer_correct: refines register_timer timer.
Proof.
  unfold register_timer.
  generalize sync_raw_register_counter_correct; intro.
  generalize counter_sync; intro.
  eapply trans_refinement in H0; eauto.
  clear H.
  eapply linked_refinement; eauto.
  apply counter_timer_correct.
Qed.

End RegisterTimer.