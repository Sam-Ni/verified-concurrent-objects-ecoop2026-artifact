Require Import
  List
  Arith
  LTS
  Register
  RegisterCounterImpl
  Counter
  Compose
.
Import ListNotations.

Section RegisterCounter.

Definition composed_register_counter :=
  compose Register register_counter_impl.

Definition register_counter : lts li_null li_counter :=
  linked_lts composed_register_counter.

End RegisterCounter.

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

