Require Import 
  List
  Arith
  LibVar
  LTS.
Require LibEnv.
Import ListNotations.

(* 
  Specification of an atomic counter (lts li_null li_counter) is defined.
  The structure of the definitions are similar to the one of Register.
*)
Section Counter.

  Inductive Counter_query :=
  | CntInc
  | CntRead
  .

  Inductive Counter_reply :=
  | CntIncOk
  | CntReadOk (value : nat)
  .

  Definition li_counter :=
    {|
      query := Counter_query;
      reply := Counter_reply;
    |}.

  Inductive Internal := 
  | int_cnt_inc
  | int_cnt_read.

  Record Counter_state := mkCntState {
    requests : LibEnv.env Counter_query; 
    responses : LibEnv.env Counter_reply;
    value : nat
  }.

  Definition new_counter := mkCntState nil nil O.

  Definition counter_new_state cnt_st := cnt_st = new_counter.

  Import LibEnv.

  Inductive counter_initial_state : Counter_state -> Pid -> query li_counter -> Counter_state -> Prop :=
  | counter_initial_state_inc : forall pid st st' inv res v
    (Hnotin_inv : pid # inv) (Hnotin_res : pid # res)
    (Hok_inv : ok inv) (Hok_res : ok res),
    st = mkCntState inv res v ->
    st' = mkCntState ((pid, CntInc)::inv) res v ->
    counter_initial_state st pid CntInc st'
  | counter_initial_state_read : forall pid st st' inv res v
    (Hnotin_inv : pid # inv) (Hnotin_res : pid # res)
    (Hok_inv : ok inv) (Hok_res : ok res),
    st = mkCntState inv res v ->
    st' = mkCntState ((pid, CntRead)::inv) res v ->
    counter_initial_state st pid CntRead st'
  .

  Inductive counter_final_state : Counter_state -> Pid -> reply li_counter -> Counter_state -> Prop :=
  | counter_final_state_inc : forall pid inv res v st st'
    (Hok_inv : ok inv) (Hok_res : ok res)
    (Hbinds : binds pid (CntIncOk) res),
    st = mkCntState inv res v ->
    st' = mkCntState inv (remove res pid) v ->
    counter_final_state st pid CntIncOk st'
  | counter_final_state_read : forall pid inv res v st st' ret
    (Hok_inv : ok inv) (Hok_res : ok res)
    (Hbinds : binds pid (CntReadOk ret) res),
    st = mkCntState inv res v ->
    st' = mkCntState inv (remove res pid) v ->
    counter_final_state st pid (CntReadOk ret) st'
  .

  Inductive counter_step : Counter_state -> Pid -> Internal -> Counter_state -> Prop :=
  | counter_step_inc : forall pid st st' inv res v
    (Hok_inv : ok inv) (Hok_res : ok res)
    (Hbinds : binds pid (CntInc) inv)
    (Hnotin_res : pid # res),
    st = mkCntState inv res v ->
    st' = mkCntState (remove inv pid) ((pid, CntIncOk)::res) (S v) ->
    counter_step st pid int_cnt_inc st'
  | counter_step_read : forall pid st st' inv res v
    (Hok_inv : ok inv) (Hok_res : ok res)
    (Hbinds : binds pid (CntRead) inv)
    (Hnotin_res : pid # res),
    st = mkCntState inv res v ->
    st' = mkCntState (remove inv pid) ((pid, CntReadOk v)::res) v ->
    counter_step st pid int_cnt_read st' 
  .

  Inductive counter_at_external : Counter_state -> Pid -> query li_null -> Counter_state -> Prop :=.

  Inductive counter_after_external : Counter_state -> Pid -> reply li_null -> Counter_state -> Prop :=.

  Definition counter : lts li_null li_counter := mkLTS li_null li_counter
    Counter_state
    Internal
    counter_step
    counter_new_state
    counter_initial_state
    counter_at_external
    counter_after_external
    counter_final_state
  .
  
End Counter.
