Require Import
  Arith
  List
  LTS
  Fin
.
Require LibEnv Vector.
Import ListNotations.

Definition entry := ((option nat) * nat)%type.

  Definition op_nat_eqb v1 v2 :=
    match v1, v2 with
    | None, None => true
    | Some n1, Some n2 => (n1 =? n2)
    | _, _ => false
    end.

  Definition entry_eqb (e1 e2 : entry) :=
    let (v1, r1) := e1 in
    let (v2, r2) := e2 in
    if op_nat_eqb v1 v2 then
      r1 =? r2
    else false.

(* 
  Specification of an atomic array (lts li_null li_array) is defined.
  The structure of the definitions are similar to the one of Register.
*)
Section Array.

  Variable L : nat.


  Inductive Array_query :=
  | AryCAS (i : nat) (old : entry) (new : entry)
  | AryRead (i : nat)
  .

  Inductive Array_reply :=
  | AryCASOk (success : bool)
  | AryReadOk (value : entry)
  .

  Definition li_array :=
    {|
      query := Array_query;
      reply := Array_reply;
    |}.

  Inductive Internal := 
  | int_ary_cas
  | int_ary_read.

  Record Array_state := mkAryState {
    requests : LibEnv.env Array_query; 
    responses : LibEnv.env Array_reply;
    vec : Vector.t entry L
  }.

  Definition new_array := mkAryState nil nil (Vector.const (None, O) L).

  Definition array_new_state ary_st := ary_st = new_array.

  Import LibEnv.

  Inductive array_initial_state : Array_state -> Pid -> query li_array -> Array_state -> Prop :=
  | array_initial_state_cas : forall pid st st' inv res vec i old new
    (Hnotin_inv : pid # inv) (Hnotin_res : pid # res)
    (Hok_inv : ok inv) (Hok_res : ok res),
    st = mkAryState inv res vec ->
    st' = mkAryState ((pid, AryCAS i old new)::inv) res vec ->
    array_initial_state st pid (AryCAS i old new) st'
  | array_initial_state_read : forall pid st st' inv res vec i
    (Hnotin_inv : pid # inv) (Hnotin_res : pid # res)
    (Hok_inv : ok inv) (Hok_res : ok res),
    st = mkAryState inv res vec ->
    st' = mkAryState ((pid, AryRead i)::inv) res vec ->
    array_initial_state st pid (AryRead i) st'
  .

  Inductive array_final_state : Array_state -> Pid -> reply li_array -> Array_state -> Prop :=
  | array_final_state_cas : forall pid inv res v st st' b
    (Hok_inv : ok inv) (Hok_res : ok res)
    (Hbinds : binds pid (AryCASOk b) res),
    st = mkAryState inv res v ->
    st' = mkAryState inv (remove res pid) v ->
    array_final_state st pid (AryCASOk b) st'
  | array_final_state_read : forall pid inv res v st st' ret
    (Hok_inv : ok inv) (Hok_res : ok res)
    (Hbinds : binds pid (AryReadOk ret) res),
    st = mkAryState inv res v ->
    st' = mkAryState inv (remove res pid) v ->
    array_final_state st pid (AryReadOk ret) st'
  .


  Inductive array_step : Array_state -> Pid -> Internal -> Array_state -> Prop :=
  | array_step_cas : forall pid st st' inv res vec i old new (Hlt : i < L) index
    (Hok_inv : ok inv) (Hok_res : ok res)
    (Hbinds : binds pid (AryCAS i old new) inv)
    (Hnotin_res : pid # res),
    st = mkAryState inv res vec ->
    index = Fin.of_nat_lt Hlt ->
    st' = mkAryState (remove inv pid)
      ((pid, AryCASOk (entry_eqb (Vector.nth vec index) old))::res)
      (if entry_eqb (Vector.nth vec index) old then Vector.replace vec index new else vec) ->
    array_step st pid int_ary_cas st'
  | array_step_read : forall pid st st' inv res vec i (Hlt : i < L) index
    (Hok_inv : ok inv) (Hok_res : ok res)
    (Hbinds : binds pid (AryRead i) inv)
    (Hnotin_res : pid # res),
    st = mkAryState inv res vec ->
    index = Fin.of_nat_lt Hlt ->
    st' = mkAryState (remove inv pid) ((pid, AryReadOk (Vector.nth vec index))::res) vec ->
    array_step st pid int_ary_read st' 
  .

  Inductive array_at_external : Array_state -> Pid -> query li_null -> Array_state -> Prop :=.

  Inductive array_after_external : Array_state -> Pid -> reply li_null -> Array_state -> Prop :=.

  Definition array : lts li_null li_array := mkLTS li_null li_array
    Array_state
    Internal
    array_step
    array_new_state
    array_initial_state
    array_at_external
    array_after_external
    array_final_state
  .
  
End Array.
