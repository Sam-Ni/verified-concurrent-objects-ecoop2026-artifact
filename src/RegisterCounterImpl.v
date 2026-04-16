Require Import 
  List
  Nat
  LTS
  Counter
  Register
  LibVar
.
Require 
  LibEnv.
Import ListNotations.

(* 
  An implementation (lts li_register li_counter) of atomic counter is defined.

  The pseudocode of function Increment and Read is shown as follows.
  The line numbers correspond to RCounter_pc, the program counter.

  void Increment ()
  1. call Register.Read()
  2. get result from Register.Read()
  3. assign the result to local variable 'r'
  4. call Register.CAS(r, r + 1)
  5. get result from Register.CAS(r, r + 1)
  6. if result is false goto 1
  7. return

  nat Read ()
  1. call Register.Read()
  2. get result from Register.Read()
  3. return result
*)
Section RegisterCounterImpl.

  Inductive RCounter_pc :=
  | RInc1
  | RInc2
  | RInc3 (ret : nat)
  | RInc4
	| RInc5 
	| RInc6 (ret : bool)
	| RInc7
	| RRead1
	| RRead2
	| RRead3 (ret : nat)
  .

  Inductive Internal :=
  | Assign
  | Goto.

  (* pc - program counter for each process
     r - local variable used in inc for each process *)
  Record RCounter_state := mkRCntState {
    pc : LibEnv.env RCounter_pc;
    r : nat -> nat
  }.

  Definition new_register_counter := mkRCntState nil (fun _ => O).

  Definition register_counter_new_state reg_cnt_st := reg_cnt_st = new_register_counter.

  Import LibEnv.

  Inductive register_counter_initial_state : RCounter_state -> Pid -> query li_counter -> RCounter_state -> Prop :=
  | register_counter_initial_state_inc : forall pc st st' pid r
    (Hnotin_pc : pid # pc)
    (Hok_pc : ok pc),
    st = mkRCntState pc r ->
    st' = mkRCntState ((pid, RInc1)::pc) r ->
    register_counter_initial_state st pid CntInc st'
  | register_counter_initial_state_read : forall pc st st' pid r
    (Hnotin_pc : pid # pc)
    (Hok_pc : ok pc),
    st = mkRCntState pc r ->
    st' = mkRCntState ((pid, RRead1)::pc) r ->
    register_counter_initial_state st pid CntRead st'
  .

  Inductive register_counter_final_state : RCounter_state -> Pid -> reply li_counter -> RCounter_state -> Prop :=
  | register_counter_final_state_inc : forall pc st st' pid r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (RInc7) pc),
    st = mkRCntState pc r ->
    st' = mkRCntState (remove pc pid) r ->
    register_counter_final_state st pid CntIncOk st'
  | register_counter_final_state_read : forall pc st st' pid r ret
    (Hok_pc : ok pc)
    (Hbinds : binds pid (RRead3 ret) pc),
    st = mkRCntState pc r ->
    st' = mkRCntState (remove pc pid) r ->
    register_counter_final_state st pid (CntReadOk ret) st'
  .

  Inductive register_counter_step : RCounter_state -> Pid -> Internal -> RCounter_state -> Prop :=
  | register_counter_step_inc_assign : forall pc st st' pid ret r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (RInc3 ret) pc),
    st = mkRCntState pc r ->
    st' = mkRCntState ((substitute pc pid RInc4)) (fun x => if x =? pid then ret else r x) ->
    register_counter_step st pid Assign st'
  | register_counter_step_inc_goto_t : forall pc st st' pid r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (RInc6 true) pc),
    st = mkRCntState pc r ->
    st' = mkRCntState ((substitute pc pid RInc7)) r ->
    register_counter_step st pid Goto st'
  | register_counter_step_inc_goto_f : forall pc st st' pid r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (RInc6 false) pc),
    st = mkRCntState pc r ->
    st' = mkRCntState ((substitute pc pid RInc1)) r ->
    register_counter_step st pid Goto st'
  .

  Inductive register_counter_at_external : RCounter_state -> Pid -> query li_register -> RCounter_state -> Prop :=
  | register_counter_at_external_inc_read : forall pc st pid r st'
    (Hok_pc : ok pc)
    (Hbinds : binds pid RInc1 pc),
    st = mkRCntState pc r ->
    st' = mkRCntState ((substitute pc pid RInc2)) r ->
    register_counter_at_external st pid RegRead st'
  | register_counter_at_external_inc_cas : forall pc st pid r st'
    (Hok_pc : ok pc)
    (Hbinds : binds pid RInc4 pc),
    st = mkRCntState pc r ->
    st' = mkRCntState ((substitute pc pid RInc5)) r ->
    register_counter_at_external st pid (RegCAS (r pid) (S (r pid))) st'
  | register_counter_at_external_read_read : forall pc st pid r st'
    (Hok_pc : ok pc)
    (Hbinds : binds pid RRead1 pc),
    st = mkRCntState pc r ->
    st' = mkRCntState ((substitute pc pid RRead2)) r ->
    register_counter_at_external st pid RegRead st'
  .

  Inductive register_counter_after_external : RCounter_state -> Pid -> reply li_register -> RCounter_state -> Prop :=
  | register_counter_after_external_inc_read_ok : forall pc st st' pid ret r
    (Hok_pc : ok pc)
    (Hbinds : binds pid RInc2 pc),
    st = mkRCntState pc r ->
    st' = mkRCntState ((substitute pc pid (RInc3 ret))) r ->
    register_counter_after_external st pid (RegReadOk ret) st'
  | register_counter_after_external_inc_cas : forall pc st st' pid r ret
    (Hok_pc : ok pc)
    (Hbinds : binds pid RInc5 pc),
    st = mkRCntState pc r ->
    st' = mkRCntState ((substitute pc pid (RInc6 ret))) r ->
    register_counter_after_external st pid (RegCASOk ret) st'
  | register_counter_after_external_read_read_ok : forall pc st st' pid ret r
    (Hok_pc : ok pc)
    (Hbinds : binds pid RRead2 pc),
    st = mkRCntState pc r ->
    st' = mkRCntState ((substitute pc pid (RRead3 ret))) r ->
    register_counter_after_external st pid (RegReadOk ret) st'
  .

  Definition register_counter_impl : lts Register.li_register Counter.li_counter := mkLTS Register.li_register Counter.li_counter
    RCounter_state
    Internal
    register_counter_step
    register_counter_new_state
    register_counter_initial_state
    register_counter_at_external
    register_counter_after_external
    register_counter_final_state
  .
  
End RegisterCounterImpl.
