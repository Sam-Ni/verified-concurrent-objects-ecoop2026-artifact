Require Import 
  List
  Nat
  LTS
  Counter
  Timer
  LibVar
  TickNat
.
Require 
  LibEnv.
Import ListNotations.

(* 
  An implementation (lts li_counter li_timer) of atomic timer is defined.

  The pseudocode of function Tick and Read is shown as follows.
  The line numbers correspond to CTimer_pc, the program counter.

  void Tick ()
  1. call Counter.Inc()
  2. get result from Counter.Inc()
  3. return

  time Read ()
  1. call Counter.Read()
  2. get result from Counter.Read()
  3. assign the result to local variable 'r'
  4. return (r / 60 % 12, r % 60)
*)
Section CounterTimerImpl.

  Inductive CTimer_pc :=
  | CTick1
  | CTick2
  | CTick3
  | CRead1
  | CRead2
  | CRead3 (ret : nat)
  .

  Inductive Internal.

  (* pc - program counter for each process
     r - local variable used in inc for each process *)
  Record CTimer_state := mkCTmState {
    pc : LibEnv.env CTimer_pc;
  }.

  Definition new_counter_timer := mkCTmState nil.

  Definition counter_timer_new_state cnt_tm_st := cnt_tm_st = new_counter_timer.

  Import LibEnv.

  Inductive counter_timer_initial_state : CTimer_state -> Pid -> query li_timer -> CTimer_state -> Prop :=
  | counter_timer_initial_state_inc : forall pc st st' pid
    (Hnotin_pc : pid # pc)
    (Hok_pc : ok pc),
    st = mkCTmState pc ->
    st' = mkCTmState ((pid, CTick1)::pc) ->
    counter_timer_initial_state st pid TmTick st'
  | counter_timer_initial_state_read : forall pc st st' pid
    (Hnotin_pc : pid # pc)
    (Hok_pc : ok pc),
    st = mkCTmState pc ->
    st' = mkCTmState ((pid, CRead1)::pc) ->
    counter_timer_initial_state st pid TmRead st'
  .

  Inductive counter_timer_final_state : CTimer_state -> Pid -> reply li_timer -> CTimer_state -> Prop :=
  | counter_timer_final_state_inc : forall pc st st' pid
    (Hok_pc : ok pc)
    (Hbinds : binds pid (CTick3) pc),
    st = mkCTmState pc ->
    st' = mkCTmState (remove pc pid) ->
    counter_timer_final_state st pid TmTickOk st'
  | counter_timer_final_state_read : forall pc st st' pid ret
    (Hok_pc : ok pc)
    (Hbinds : binds pid (CRead3 ret) pc),
    st = mkCTmState pc ->
    st' = mkCTmState (remove pc pid) ->
    counter_timer_final_state st pid (TmReadOk (nat_to_time ret)) st'
  .

  Inductive counter_timer_step : CTimer_state -> Pid -> Internal -> CTimer_state -> Prop :=.

  Inductive counter_timer_at_external : CTimer_state -> Pid -> query li_counter -> CTimer_state -> Prop :=
  | counter_timer_at_external_tick_inc : forall pc st pid st'
    (Hok_pc : ok pc)
    (Hbinds : binds pid CTick1 pc),
    st = mkCTmState pc ->
    st' = mkCTmState ((substitute pc pid CTick2)) ->
    counter_timer_at_external st pid CntInc st'
  | counter_timer_at_external_read_read : forall pc st pid st'
    (Hok_pc : ok pc)
    (Hbinds : binds pid CRead1 pc),
    st = mkCTmState pc ->
    st' = mkCTmState ((substitute pc pid CRead2)) ->
    counter_timer_at_external st pid CntRead st'
  .

  Inductive counter_timer_after_external : CTimer_state -> Pid -> reply li_counter -> CTimer_state -> Prop :=
  | counter_timer_after_external_tick_inc_ok : forall pc st st' pid
    (Hok_pc : ok pc)
    (Hbinds : binds pid CTick2 pc),
    st = mkCTmState pc ->
    st' = mkCTmState ((substitute pc pid (CTick3))) ->
    counter_timer_after_external st pid (CntIncOk) st'
  | counter_timer_after_external_read_read_ok : forall pc st st' pid ret
    (Hok_pc : ok pc)
    (Hbinds : binds pid CRead2 pc),
    st = mkCTmState pc ->
    st' = mkCTmState ((substitute pc pid (CRead3 ret))) ->
    counter_timer_after_external st pid (CntReadOk ret) st'
  .

  Definition counter_timer_impl : lts li_counter li_timer := mkLTS li_counter li_timer
    CTimer_state
    Internal
    counter_timer_step
    counter_timer_new_state
    counter_timer_initial_state
    counter_timer_at_external
    counter_timer_after_external
    counter_timer_final_state
  .
  
End CounterTimerImpl.
