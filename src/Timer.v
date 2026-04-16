Require Import 
  Arith
  List
  LTS
  TickNat.
Require LibEnv.
Import ListNotations.

Section Timer.

  Inductive Timer_query :=
  | TmTick
  | TmRead
  .

  Inductive Timer_reply :=
  | TmTickOk
  | TmReadOk (t : time)
  .

  Definition li_timer :=
    {|
      query := Timer_query;
      reply := Timer_reply;
    |}.

  Inductive Internal := 
  | int_tm_tick
  | int_tm_read.

  Record Timer_state := mkTmState {
    requests : LibEnv.env Timer_query; 
    responses : LibEnv.env Timer_reply;
    t : time
  }.

  Definition new_timer := mkTmState nil nil (O, O).

  Definition timer_new_state tm_st := tm_st = new_timer.

  Import LibEnv.

  Inductive timer_initial_state : Timer_state -> Pid -> query li_timer -> Timer_state -> Prop :=
  | timer_initial_state_tick : forall pid st st' inv res t
    (Hnotin_inv : pid # inv) (Hnotin_res : pid # res)
    (Hok_inv : ok inv) (Hok_res : ok res),
    st = mkTmState inv res t ->
    st' = mkTmState ((pid, TmTick)::inv) res t ->
    timer_initial_state st pid TmTick st'
  | timer_initial_state_read : forall pid st st' inv res t
    (Hnotin_inv : pid # inv) (Hnotin_res : pid # res)
    (Hok_inv : ok inv) (Hok_res : ok res),
    st = mkTmState inv res t ->
    st' = mkTmState ((pid, TmRead)::inv) res t ->
    timer_initial_state st pid TmRead st'
  .

  Inductive timer_final_state : Timer_state -> Pid -> reply li_timer -> Timer_state -> Prop :=
  | timer_final_state_tick : forall pid inv res t st st'
    (Hok_inv : ok inv) (Hok_res : ok res)
    (Hbinds : binds pid (TmTickOk) res),
    st = mkTmState inv res t ->
    st' = mkTmState inv (remove res pid) t ->
    timer_final_state st pid TmTickOk st'
  | timer_final_state_read : forall pid inv res t st st' ret
    (Hok_inv : ok inv) (Hok_res : ok res)
    (Hbinds : binds pid (TmReadOk ret) res),
    st = mkTmState inv res t ->
    st' = mkTmState inv (remove res pid) t ->
    timer_final_state st pid (TmReadOk ret) st'
  .

  Inductive timer_step : Timer_state -> Pid -> Internal -> Timer_state -> Prop :=
  | timer_step_tick : forall pid st st' inv res t
    (Hok_inv : ok inv) (Hok_res : ok res)
    (Hbinds : binds pid (TmTick) inv)
    (Hnotin_res : pid # res),
    st = mkTmState inv res t ->
    st' = mkTmState (remove inv pid) ((pid, TmTickOk)::res) (tick t) ->
    timer_step st pid int_tm_tick st'
  | timer_step_read : forall pid st st' inv res t
    (Hok_inv : ok inv) (Hok_res : ok res)
    (Hbinds : binds pid (TmRead) inv)
    (Hnotin_res : pid # res),
    st = mkTmState inv res t ->
    st' = mkTmState (remove inv pid) ((pid, TmReadOk t)::res) t ->
    timer_step st pid int_tm_read st' 
  .

  Inductive timer_at_external : Timer_state -> Pid -> query li_null -> Timer_state -> Prop :=.

  Inductive timer_after_external : Timer_state -> Pid -> reply li_null -> Timer_state -> Prop :=.

  Definition timer : lts li_null li_timer := mkLTS li_null li_timer
    Timer_state
    Internal
    timer_step
    timer_new_state
    timer_initial_state
    timer_at_external
    timer_after_external
    timer_final_state
  .
  
End Timer.
