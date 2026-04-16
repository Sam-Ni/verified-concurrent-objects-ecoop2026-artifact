Require Import
  List
  Nat
  Arith
  LTS
  LibVar.
From VCO Require LibEnv.
Import ListNotations.

(* 
  Linearizability is a special kind of refinement which additionally requires that
  there is only one internal action for each function in
  the specification.

  Our goal is to build up objects from smaller objects and
  verify them with the specification (simpler than implementation) of these smaller ones.

  The specification of an atomic register (lts li_null li_register)
  equipped with functions CAS and Read is defined below.
  It is the smallest object in our example.
*)
Section Register.

  (* 
    Queries and replies provided by Register.
    The first parameter of each constructor is the process 'pid'
    who calls to or returns from Register.
  *)
  Inductive Register_query :=
  | RegCAS (old : nat) (new : nat)
  | RegRead
  .

  Inductive Register_reply :=
  | RegCASOk (success : bool)
  | RegReadOk (value : nat)
  .

  Definition li_register :=
    {|
      query := Register_query;
      reply := Register_reply;
    |}.

  Inductive Internal := 
  | int_cas
  | int_read.

  (* 
    A register state comprises of
    requests - set of pending invocations (by process pid)
    responses - set of functions which has taken effect but yet returned (to pid)
    value - the value of the register.

    LibEnv.env T := list (nat*T)
  *)
  Record Register_state := mkRegState {
    requests : LibEnv.env Register_query; 
    responses : LibEnv.env Register_reply;
    value : nat
  }.

  Definition new_register := mkRegState nil nil O.

  Definition register_new_state reg_st := reg_st = new_register.

  Import LibEnv.

  (* 
    Called by environment
  *)
  Inductive register_initial_state : Register_state -> Pid -> query li_register -> Register_state -> Prop :=
  | register_initial_state_cas : forall pid old new st st' inv res v
    (Hnotin_inv : pid # inv) (Hnotin_res : pid # res)
    (Hok_inv : ok inv) (Hok_res : ok res),
    st = mkRegState inv res v ->
    st' = mkRegState ((pid, RegCAS old new)::inv) res v ->
    register_initial_state st pid (RegCAS old new) st'
  | register_initial_state_read : forall pid st st' inv res v
    (Hnotin_inv : pid # inv) (Hnotin_res : pid # res)
    (Hok_inv : ok inv) (Hok_res : ok res),
    st = mkRegState inv res v ->
    st' = mkRegState ((pid, RegRead)::inv) res v ->
    register_initial_state st pid (RegRead) st'
  .

  (* 
    Return to environment
  *)
  Inductive register_final_state : Register_state -> Pid -> reply li_register -> Register_state -> Prop :=
  | register_final_state_cas : forall pid inv res b v st st'
    (Hok_inv : ok inv) (Hok_res : ok res)
    (Hbinds : binds pid (RegCASOk b) res),
    st = mkRegState inv res v ->
    st' = mkRegState inv (remove res pid) v ->
    register_final_state st pid (RegCASOk b) st'
  | register_final_state_read : forall pid inv res v st st' ret
    (Hok_inv : ok inv) (Hok_res : ok res)
    (Hbinds : binds pid (RegReadOk ret) res),
    st = mkRegState inv res v ->
    st' = mkRegState inv (remove res pid) v ->
    register_final_state st pid (RegReadOk ret) st'
  .

  (* 
    Internal execution
  *)
  Inductive register_step : Register_state -> Pid -> Internal -> Register_state -> Prop :=
  | register_step_cas : forall pid st st' inv res v old new
    (Hok_inv : ok inv) (Hok_res : ok res)
    (Hbinds : binds pid (RegCAS old new) inv)
    (Hnotin_res : pid # res),
    st = mkRegState inv res v ->
    st' = mkRegState (remove inv pid) ((pid, RegCASOk (st.(value) =? old))::res) (if value st =? old then new else value st) ->
    register_step st pid int_cas st'
  | register_step_read : forall pid st st' inv res v
    (Hok_inv : ok inv) (Hok_res : ok res)
    (Hbinds : binds pid (RegRead) inv)
    (Hnotin_res : pid # res),
    st = mkRegState inv res v ->
    st' = mkRegState (remove inv pid) ((pid, RegReadOk v)::res) v ->
    register_step st pid int_read st' 
  .

  (* 
    No external calls since Register does not rely on other objects
  *)
  Inductive register_at_external : Register_state -> Pid -> query li_null -> Register_state -> Prop :=.

  Inductive register_after_external : Register_state -> Pid -> reply li_null -> Register_state -> Prop :=.

  Definition Register : lts li_null li_register  := mkLTS li_null li_register
    Register_state
    Internal
    register_step
    register_new_state
    register_initial_state
    register_at_external
    register_after_external
    register_final_state
  .
  
End Register.
