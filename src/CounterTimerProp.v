Require Import
  LTS
  SyncLTS
  Compose
  ComposedLTS
  CounterTimer
  CounterTimerImplProp
.

Section Properties.

Arguments inv {liA liB L1 L2}.

Definition composed_counter_timer_wf (st : composed_lts.state composed_counter_timer) :=
  CntTmImplStateWF st.(L2State).(LState) /\
  inv st.

Lemma composed_counter_timer_wf_inv: composed_lts.invariant_ind composed_counter_timer composed_counter_timer_wf.
Proof.
  unfold composed_counter_timer_wf.
  apply composed_lts.invariant_ind_land.
  2 : { apply step_inv. }
  generalize cnttmimpl_ok_inv; intro.
  destruct H as [Hnew [Hstep [Hinit [Hat [Hafter Hfinal]]]]].
  unfold composed_lts.invariant_ind. intuition.
  - inversion H; subst.
    inversion H1; subst.
    apply Hnew in H2; intuition.
  - inversion H0; subst.
    -- intuition.
  - inversion H0; subst.
    -- inversion H1; subst.
      apply Hstep in H2; intuition.
  - inversion H0; subst.
    inversion H1; subst.
    apply Hinit in H2; intuition.
  - destruct act.
  - destruct act.
  - inversion H0; subst.
    inversion H1; subst.
    apply Hfinal in H2; intuition.
  - inversion H0; subst.
    inversion H1; subst.
    apply Hat in H3; intuition.
  - inversion H0; subst.
    inversion H1; subst.
    inversion H2; subst.
    apply Hafter in H4; intuition.
Qed.

End Properties.