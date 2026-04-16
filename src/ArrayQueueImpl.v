Require Import 
  List
  Nat
  LTS
  Queue
  LibVar
  Tensor
  Compose
  Counter
  Array
.
Require 
  LibEnv.
Import ListNotations.

(* 
  An implementation (lts li_ary_cnt_cnt li_queue) of atomic queue is defined.

  The pseudocode of function Enq and Deq is shown as follows.
  The line numbers correspond to CTimer_pc, the program counter.

  void Enq (v : nat)
  1. call Rear.Read()
  2. get result from Rear.Read()
  3. assign the result to local variable 'rear'
  4. call Q.Read(rear mod L)
  5. get result from Q.Read(rear mod L)
  6. assign the result to local variable 'x'

  10. call Rear.Read()
  11. get result from Rear.Read()
  12. if rear != result goto 1
  13. call Front.Read()
  14. get result from Front.Read()
  15. if rear == result + L goto 1 // full queue

  26. if x != None goto 1
  27. call Q.CAS(rear mod L, x, Some v)
  28. get result from Q.CAS(rear mod L, x, Some v)
  29. if result == false goto 1
  30. call Rear.Inc()
  31. get result from Rear.Inc()
  32. return

  nat Deq ()
  1. call Front.Read()
  2. get result from Front.Read()
  3. assign the result to local variable 'front'
  4. call Q.Read(front mod L)
  5. get result from Q.Read(front mod L)
  6. assign the result to local variable 'x'

  10. call Front.Read()
  11. get result from Front.Read()
  12. if front != result goto 1
  13. call Rear.Read()
  14. get result from Rear.Read()
  15. if front == result goto 1 // empty queue

  26. if x == None goto 1
  27. call Q.CAS(front mod L, x, None)
  28. get result from Q.CAS(front mod L, x, None)
  29. if result == false goto 1
  30. call Front.Inc()
  31. get result from Front.Inc()
  32. return x

*)

Section ArrayQueueImpl.
  
  Variable L : nat.

  Definition li_cnt_cnt := tensor_li li_counter li_counter.

  Definition li_array_cnt_cnt := tensor_li li_array li_cnt_cnt.

  Inductive AQueue_pc : Set :=
  | AEnq1
  | AEnq2
  | AEnq3 (ret : nat)
  | AEnq4
  | AEnq5 
  | AEnq6 (ret : entry)
  | AEnq10
  | AEnq11 
  | AEnq12 (ret : nat)
  | AEnq13
  | AEnq14 
  | AEnq15 (ret : nat)
  | AEnq26
  | AEnq27
  | AEnq28 
  | AEnq29 (ret : bool)
  | AEnq30
  | AEnq31
  | AEnq32
  | ADeq1
  | ADeq2
  | ADeq3 (ret : nat)
  | ADeq4
  | ADeq5 
  | ADeq6 (ret : entry)

  | ADeq10
  | ADeq11 
  | ADeq12 (ret : nat)
  | ADeq13
  | ADeq14 
  | ADeq15 (ret : nat)
  | ADeq26
  | ADeq27
  | ADeq28 
  | ADeq29 (ret : bool)
  | ADeq30
  | ADeq31
  | ADeq32
  .

  Inductive Internal :=
  | Assign
  | Goto.

  Record AQueue_state := mkAQState {
    pc : LibEnv.env AQueue_pc;
    front : Pid -> nat;
    rear : Pid -> nat;
    x : Pid -> entry;
    vp : Pid -> nat;
    f : nat;
    r : nat;
  }.

  Definition new_array_queue := mkAQState nil (fun _ => O) (fun _ => O) (fun _ => (None, O)) (fun _ => O) O O.

  Definition array_queue_new_state ary_q_st := ary_q_st = new_array_queue.

  Import LibEnv.

  Inductive array_queue_initial_state : AQueue_state -> Pid -> query li_queue -> AQueue_state -> Prop :=
  | array_queue_initial_state_enq : forall pc st st' pid front rear x vp v f r
    (Hnotin_pc : pid # pc)
    (Hok_pc : ok pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState ((pid, AEnq1)::pc) front rear x (fun p => if p =? pid then v else vp p) f r ->
      array_queue_initial_state st pid (QEnq v) st'
  | array_queue_initial_state_deq : forall pc st st' pid front rear x vp f r
    (Hnotin_pc : pid # pc)
    (Hok_pc : ok pc),
      st = mkAQState pc front rear x vp f r->
      st' = mkAQState ((pid, ADeq1)::pc) front rear x vp f r->
      array_queue_initial_state st pid QDeq st'
  .

  Inductive array_queue_final_state : AQueue_state -> Pid -> reply li_queue -> AQueue_state -> Prop :=
  | array_queue_final_state_enq_t : forall pc st st' pid front rear x vp f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (AEnq32) pc),
      st = mkAQState pc front rear x vp f r->
      st' = mkAQState (remove pc pid) front rear x vp f r->
      array_queue_final_state st pid (QEnqOk) st'
  | array_queue_final_state_deq_t : forall pc st st' pid front rear x vp f r v
    (Hok_pc : ok pc)
    (Hbinds : binds pid (ADeq32) pc),
      fst (x pid) = Some v ->
      st = mkAQState pc front rear x vp f r->
      st' = mkAQState (remove pc pid) front rear x vp f r->
      array_queue_final_state st pid (QDeqOk v) st'
  .

  Inductive array_queue_step : AQueue_state -> Pid -> Internal -> AQueue_state -> Prop :=
  | array_queue_step_enq3_assign_rear : forall pc st st' pid ret front rear x vp f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (AEnq3 ret) pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid AEnq4) front (fun p => if p =? pid then ret else rear p) x vp f r ->
      array_queue_step st pid Assign st'
  | array_queue_step_enq6_assign_x : forall pc st st' pid ret front rear x vp f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (AEnq6 ret) pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid AEnq10) front rear (fun p => if p =? pid then ret else x p) vp f r ->
      array_queue_step st pid Assign st'
  | array_queue_step_enq12_goto_1 : forall pc st st' pid ret front rear x vp f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (AEnq12 ret) pc),
      rear pid <> ret ->
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid AEnq1) front rear x vp f r ->
      array_queue_step st pid Assign st'
  | array_queue_step_enq12_goto_13 : forall pc st st' pid ret front rear x vp f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (AEnq12 ret) pc),
      rear pid = ret ->
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid AEnq13) front rear x vp f r ->
      array_queue_step st pid Assign st'
  | array_queue_step_enq15_goto_26 : forall pc st st' pid ret front rear x vp f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (AEnq15 ret) pc),
      rear pid >= ret + L ->
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid AEnq1) front rear x vp f r ->
      array_queue_step st pid Goto st'
  | array_queue_step_enq15_goto_16 : forall pc st st' pid ret front rear x vp f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (AEnq15 ret) pc),
      rear pid < ret + L ->
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid AEnq26) front rear x vp f r ->
      array_queue_step st pid Goto st'
  | array_queue_step_enq26_goto_1 : forall pc st st' pid front rear x vp f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (AEnq26) pc),
      st = mkAQState pc front rear x vp f r ->
      fst (x pid) <> None ->
      st' = mkAQState (substitute pc pid AEnq1) front rear x vp f r ->
      array_queue_step st pid Assign st'
  | array_queue_step_enq26_goto_27 : forall pc st st' pid front rear x vp f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (AEnq26) pc),
      st = mkAQState pc front rear x vp f r ->
      fst (x pid) = None ->
      st' = mkAQState (substitute pc pid AEnq27) front rear x vp f r ->
      array_queue_step st pid Assign st'
  | array_queue_step_enq29_goto_33 : forall pc st st' pid front rear x vp f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (AEnq29 false) pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid AEnq1) front rear x vp f r ->
      array_queue_step st pid Assign st'
  | array_queue_step_enq29_goto_30 : forall pc st st' pid front rear x vp f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (AEnq29 true) pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid AEnq30) front rear x vp f r ->
      array_queue_step st pid Assign st'
  | array_queue_step_deq3_assign_front : forall pc st st' pid ret front rear x vp f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (ADeq3 ret) pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid ADeq4) (fun p => if p =? pid then ret else front p) rear x vp f r ->
      array_queue_step st pid Assign st'
  | array_queue_step_deq6_assign_x : forall pc st st' pid ret front rear x vp f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (ADeq6 ret) pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid ADeq10) front rear (fun p => if p =? pid then ret else x p) vp f r ->
      array_queue_step st pid Assign st'
  | array_queue_step_deq12_goto_1 : forall pc st st' pid ret front rear x vp f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (ADeq12 ret) pc),
      front pid <> ret ->
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid ADeq1) front rear x vp f r ->
      array_queue_step st pid Assign st'
  | array_queue_step_deq12_goto_13 : forall pc st st' pid ret front rear x vp f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (ADeq12 ret) pc),
      front pid = ret ->
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid ADeq13) front rear x vp f r ->
      array_queue_step st pid Assign st'
  | array_queue_step_deq15_goto_26 : forall pc st st' pid ret front rear x vp f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (ADeq15 ret) pc),
      front pid >= ret ->
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid ADeq1) front rear x vp f r ->
      array_queue_step st pid Goto st'
  | array_queue_step_deq15_goto_16 : forall pc st st' pid ret front rear x vp f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (ADeq15 ret) pc),
      front pid < ret ->
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid ADeq26) front rear x vp f r ->
      array_queue_step st pid Goto st'
  | array_queue_step_deq26_goto_1 : forall pc st st' pid front rear x vp f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (ADeq26) pc),
      st = mkAQState pc front rear x vp f r ->
      fst (x pid) = None ->
      st' = mkAQState (substitute pc pid ADeq1) front rear x vp f r ->
      array_queue_step st pid Assign st'
  | array_queue_step_deq26_goto_27 : forall pc st st' pid front rear x vp f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (ADeq26) pc),
      st = mkAQState pc front rear x vp f r ->
      fst (x pid) <> None ->
      st' = mkAQState (substitute pc pid ADeq27) front rear x vp f r ->
      array_queue_step st pid Assign st'
  | array_queue_step_deq29_goto_1 : forall pc st st' pid front rear x vp f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (ADeq29 false) pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid ADeq1) front rear x vp f r ->
      array_queue_step st pid Assign st'
  | array_queue_step_deq29_goto_30 : forall pc st st' pid front rear x vp f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid (ADeq29 true) pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid ADeq30) front rear x vp f r ->
      array_queue_step st pid Assign st'
      .

  Inductive array_queue_at_external : AQueue_state -> Pid -> query li_array_cnt_cnt -> AQueue_state -> Prop :=
  | array_queue_at_external_enq1_read : forall pc st pid front rear x vp st' f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid AEnq1 pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid AEnq2) front rear x vp f r ->
      array_queue_at_external st pid (@queryR _ li_cnt_cnt (@queryR _ li_counter (CntRead))) st'
  | array_queue_at_external_enq4_read : forall pc st pid front rear x vp st' f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid AEnq4 pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid AEnq5) front rear x vp f r ->
      array_queue_at_external st pid (@queryL li_array li_cnt_cnt (AryRead ((rear pid) mod L))) st'
  | array_queue_at_external_enq10_read : forall pc st pid front rear x vp st' f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid AEnq10 pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid AEnq11) front rear x vp f r ->
      array_queue_at_external st pid (@queryR _ li_cnt_cnt (@queryR _ li_counter (CntRead))) st'
  | array_queue_at_external_enq13_read : forall pc st pid front rear x vp st' f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid AEnq13 pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid AEnq14) front rear x vp f r ->
      array_queue_at_external st pid (@queryR _ li_cnt_cnt (@queryL li_counter li_counter (CntRead))) st'
  | array_queue_at_external_enq27_cas : forall pc st pid front rear x vp st' f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid AEnq27 pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid AEnq28) front rear x vp f r ->
      array_queue_at_external st pid (@queryL li_array li_cnt_cnt (AryCAS ((rear pid) mod L) (x pid) (Some (vp pid), snd (x pid) + 1))) st'
  | array_queue_at_external_enq30_inc : forall pc st pid front rear x vp st' f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid AEnq30 pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid AEnq31) front rear x vp f r ->
      array_queue_at_external st pid (@queryR _ li_cnt_cnt (@queryR li_counter li_counter (CntInc))) st'
  | array_queue_at_external_deq1_read : forall pc st pid front rear x vp st' f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid ADeq1 pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid ADeq2) front rear x vp f r ->
      array_queue_at_external st pid (@queryR _ li_cnt_cnt (@queryL li_counter li_counter (CntRead))) st'
  | array_queue_at_external_deq4_read : forall pc st pid front rear x vp st' f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid ADeq4 pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid ADeq5) front rear x vp f r ->
      array_queue_at_external st pid (@queryL li_array li_cnt_cnt (AryRead ((front pid) mod L))) st'
  | array_queue_at_external_deq10_read : forall pc st pid front rear x vp st' f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid ADeq10 pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid ADeq11) front rear x vp f r ->
      array_queue_at_external st pid (@queryR _ li_cnt_cnt (@queryL li_counter li_counter (CntRead))) st'
  | array_queue_at_external_deq13_read : forall pc st pid front rear x vp st' f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid ADeq13 pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid ADeq14) front rear x vp f r ->
      array_queue_at_external st pid (@queryR _ li_cnt_cnt (@queryR li_counter li_counter (CntRead))) st'
  | array_queue_at_external_deq27_cas : forall pc st pid front rear x vp st' f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid ADeq27 pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid ADeq28) front rear x vp f r ->
      array_queue_at_external st pid (@queryL li_array li_cnt_cnt (AryCAS ((front pid) mod L) (x pid) (None, snd (x pid) + 1))) st'
  | array_queue_at_external_deq30_read : forall pc st pid front rear x vp st' f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid ADeq30 pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid ADeq31) front rear x vp f r ->
      array_queue_at_external st pid (@queryR _ li_cnt_cnt (@queryL li_counter li_counter (CntInc))) st'
  .

  Inductive array_queue_after_external : AQueue_state -> Pid -> reply li_array_cnt_cnt -> AQueue_state -> Prop :=
  | array_queue_after_external_enq2_read : forall pc st pid front rear x vp st' ret f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid AEnq2 pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid (AEnq3 ret)) front rear x vp f r ->
      array_queue_after_external st pid (@replyR li_array li_cnt_cnt (@replyR li_counter li_counter (CntReadOk ret))) st'
  | array_queue_after_external_enq5_read : forall pc st pid front rear x vp st' ret f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid AEnq5 pc),
      st = mkAQState pc front rear x vp f r->
      st' = mkAQState (substitute pc pid (AEnq6 ret)) front rear x vp  f r->
      array_queue_after_external st pid (@replyL li_array _ (AryReadOk ret)) st'
  | array_queue_after_external_enq11_read : forall pc st pid front rear x vp st' ret f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid AEnq11 pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid (AEnq12 ret)) front rear x vp f r ->
      array_queue_after_external st pid (@replyR li_array li_cnt_cnt (@replyR li_counter li_counter (CntReadOk ret))) st'
  | array_queue_after_external_enq14_read : forall pc st pid front rear x vp st' ret f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid AEnq14 pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid (AEnq15 ret)) front rear x vp f r ->
      array_queue_after_external st pid (@replyR li_array li_cnt_cnt (@replyL li_counter li_counter (CntReadOk ret))) st'
  | array_queue_after_external_enq28_cas : forall pc st pid front rear x vp st' ret f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid AEnq28 pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid (AEnq29 ret)) front rear x vp f (if ret then (S r) else r) ->
      array_queue_after_external st pid (@replyL li_array _ (AryCASOk ret)) st'
  | array_queue_after_external_enq31_read : forall pc st pid front rear x vp st' f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid AEnq31 pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid (AEnq32)) front rear x vp f r ->
      array_queue_after_external st pid (@replyR li_array li_cnt_cnt (@replyR li_counter li_counter (CntIncOk))) st'
  | array_queue_after_external_deq2_read : forall pc st pid front rear x vp st' ret f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid ADeq2 pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid (ADeq3 ret)) front rear x vp f r ->
      array_queue_after_external st pid (@replyR li_array li_cnt_cnt (@replyL li_counter li_counter (CntReadOk ret))) st'
  | array_queue_after_external_deq5_read : forall pc st pid front rear x vp st' ret f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid ADeq5 pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid (ADeq6 ret)) front rear x vp f r ->
      array_queue_after_external st pid (@replyL li_array _ (AryReadOk ret)) st'
  | array_queue_after_external_deq14_read : forall pc st pid front rear x vp st' ret f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid ADeq14 pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid (ADeq15 ret)) front rear x vp f r ->
      array_queue_after_external st pid (@replyR li_array li_cnt_cnt (@replyR li_counter li_counter (CntReadOk ret))) st'
  | array_queue_after_external_deq28_cas : forall pc st pid front rear x vp st' ret f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid ADeq28 pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid (ADeq29 ret)) front rear x vp (if ret then (S f) else f) r ->
      array_queue_after_external st pid (@replyL li_array _ (AryCASOk ret)) st'
  | array_queue_after_external_deq31_read : forall pc st pid front rear x vp st' f r
    (Hok_pc : ok pc)
    (Hbinds : binds pid ADeq31 pc),
      st = mkAQState pc front rear x vp f r ->
      st' = mkAQState (substitute pc pid (ADeq32)) front rear x vp f r ->
      array_queue_after_external st pid (@replyR li_array li_cnt_cnt (@replyL li_counter li_counter (CntIncOk))) st'
	.

  Definition array_queue_impl : lts li_array_cnt_cnt li_queue := mkLTS li_array_cnt_cnt li_queue
    AQueue_state
    Internal
    array_queue_step
    array_queue_new_state
    array_queue_initial_state
    array_queue_at_external
    array_queue_after_external
    array_queue_final_state
  .

End ArrayQueueImpl.
