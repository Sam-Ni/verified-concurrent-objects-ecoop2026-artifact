Require Import
  List
  Arith
  LTS
  Counter
  CounterTimerImpl
  Timer
  Compose
.
Import ListNotations.

Section CounterTimer.

Definition composed_counter_timer :=
  compose counter counter_timer_impl.

Definition counter_timer : lts li_null li_timer :=
  linked_lts composed_counter_timer.

End CounterTimer.