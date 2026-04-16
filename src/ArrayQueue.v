Require Import
  LTS
  Tensor
  Compose
  Counter
  Array
  ArrayQueueImpl.

Section ArrayQueue.

Variable L : nat.

Definition front_rear := tensor counter counter.

Definition array_front_rear := tensor (array L) front_rear.

Definition composed_array_queue :=
  (compose array_front_rear (array_queue_impl L)).

Definition array_queue :=
  linked_lts composed_array_queue.

End ArrayQueue.