Require Import
  List
  Arith
  LTS.
Require LibEnv.
Import ListNotations.

Section Queue.

  Variable L : nat.

  Definition enqueue {A} q (v : A) : bool * (list (option A)) :=
    if length q <? L then (true, Some v :: q)
                    else (false, q).

  Fixpoint dequeue {A} (l : list (option A)) : (option A * list (option A)) :=
      match l with
      | nil => (None, nil)
      | [x] => (x, nil)
      | x :: xs => 
          match dequeue xs with
          | (ret, ys) => (ret, x :: ys)
          end
      end.

  Inductive Queue_query :=
  | QEnq (e : nat)
  | QDeq
  .

  Inductive Queue_reply :=
  | QEnqOk
  | QDeqOk (ret : nat)
  .

  Definition li_queue :=
    {|
      query := Queue_query;
      reply := Queue_reply;
    |}.

  Inductive Internal := 
  | int_q_enq
  | int_q_deq.


  Record Queue_state := mkQState {
    requests : LibEnv.env Queue_query; 
    responses : LibEnv.env Queue_reply;
    q : list (option nat);
  }.

  Definition queue_new_state q_st :=
    q_st.(requests) = [] /\
    q_st.(responses) = [] /\
    q_st.(q) = [].

  Import LibEnv.

  Inductive queue_initial_state : Queue_state -> Pid -> query li_queue -> Queue_state -> Prop :=
  | queue_initial_state_enq : forall pid st st' inv res q v
    (Hnotin_inv : pid # inv) (Hnotin_res : pid # res)
    (Hok_inv : ok inv) (Hok_res : ok res),
    st = mkQState inv res q ->
    st' = mkQState ((pid, QEnq v)::inv) res q ->
    queue_initial_state st pid (QEnq v) st'
  | queue_initial_state_deq : forall pid st st' inv res q
    (Hnotin_inv : pid # inv) (Hnotin_res : pid # res)
    (Hok_inv : ok inv) (Hok_res : ok res),
    st = mkQState inv res q ->
    st' = mkQState ((pid, QDeq)::inv) res q ->
    queue_initial_state st pid (QDeq) st'
  .

  Inductive queue_final_state : Queue_state -> Pid -> reply li_queue -> Queue_state -> Prop :=
  | queue_final_state_enq : forall pid inv res q st st'
    (Hok_inv : ok inv) (Hok_res : ok res)
    (Hbinds : binds pid (QEnqOk) res),
    st = mkQState inv res q ->
    st' = mkQState inv (remove res pid) q ->
    queue_final_state st pid (QEnqOk) st'
  | queue_final_state_deq : forall pid inv res q st st' ret
    (Hok_inv : ok inv) (Hok_res : ok res)
    (Hbinds : binds pid (QDeqOk ret) res),
    st = mkQState inv res q ->
    st' = mkQState inv (remove res pid) q ->
    queue_final_state st pid (QDeqOk ret) st'
  .

  Inductive queue_step : Queue_state -> Pid -> Internal -> Queue_state -> Prop :=
  | queue_step_enq : forall pid st st' inv res q v q' res'
    (Hok_inv : ok inv) (Hok_res : ok res)
    (Hbinds : binds pid (QEnq v) inv)
    (Hnotin_res : pid # res),
    st = mkQState inv res q ->
    enqueue q v = (true, q') ->
    sameset res' ((pid, QEnqOk)::res) ->
    st' = mkQState (remove inv pid) res' q' ->
    queue_step st pid int_q_enq st'
  | queue_step_deq : forall pid st st' inv res q q' (v : nat) res'
    (Hok_inv : ok inv) (Hok_res : ok res)
    (Hbinds : binds pid (QDeq) inv)
    (Hnotin_res : pid # res),
    st = mkQState inv res q ->
    dequeue q = (Some v, q') ->
    sameset res' ((pid, QDeqOk v)::res) ->
    st' = mkQState (remove inv pid) (res') q' ->
    queue_step st pid int_q_deq st'
  .

  Inductive queue_at_external : Queue_state -> Pid -> query li_null -> Queue_state -> Prop :=.

  Inductive queue_after_external : Queue_state -> Pid -> reply li_null -> Queue_state -> Prop :=.

  Definition queue : lts li_null li_queue := mkLTS li_null li_queue
    Queue_state
    Internal
    queue_step
    queue_new_state
    queue_initial_state
    queue_at_external
    queue_after_external
    queue_final_state
  .
  
End Queue.
