Require Import
  List
  LibEnv
  LTS
  VerifiedConcurrentObject
  HComp
  ImplRawCompose
  Refinement
  ImplRefinement
  SyncLTS
  VE
  Compose
  Link
  VComp.
Import ListNotations.

Section Link.
  
Context {liA liB liC: language_interface}.
Variable L1: lts li_null liA.
Variable M1: lts liA liB.
Variable M2: lts liB liC.
Variable L2: lts li_null liC.

Lemma raw_compose_assoc': 
refines
  (sync
     (LTS.linked_lts
        (LTS.raw_compose
           (LTS.linked_lts (LTS.raw_compose L1 M1)) M2)))
  (sync
     (LTS.linked_lts
        (LTS.raw_compose L1 (linked_lts (raw_compose M1 M2))))).
Proof.
  eapply Refinement.forward_simulation_inv_ind
    with (f:=fun 
    (x : state (sync
     (LTS.linked_lts
        (LTS.raw_compose
           (LTS.linked_lts (LTS.raw_compose L1 M1)) M2)))) 
    (y : state (sync
     (LTS.linked_lts
        (LTS.raw_compose L1 (linked_lts (raw_compose M1 M2)))))) =>
      x.(LState).(LTS.RawL1State).(LTS.RawL1State) =
      y.(LState).(LTS.RawL1State) /\
      x.(LState).(LTS.RawL1State).(LTS.RawL2State) =
      y.(LState).(LTS.RawL2State).(RawL1State) /\
      x.(LState).(LTS.RawL2State) =
      y.(LState).(LTS.RawL2State).(RawL2State) /\
      x.(PidPos) = y.(PidPos)
      )
      (inv:=fun x => True).
  unfold Refinement.fsim_properties_inv_ind. intuition.
  - unfold invariant_ind. intuition.
  - inversion H; subst; simpl in *.
    inversion H0; subst; simpl in *.
    inversion H2; subst; simpl in *.
    exists (
      mkSyncState 
        (LTS.linked_lts
          (LTS.raw_compose L1 (linked_lts (raw_compose M1 M2))))
      (@LTS.mkRawComposedState liA liC 
        L1 (ImplRawCompose.linked_lts (ImplRawCompose.raw_compose M1 M2))
          (LTS.RawL1State
            (LTS.RawL1State (LState s1)))
          (@ImplRawCompose.mkRawComposedState liA liB liC
            M1 M2
            (LTS.RawL2State
                (LTS.RawL1State (LState s1)))
            (LTS.RawL2State (LState s1))
          )
      )
      []
    ).
    simpl. intuition.
    unfold sync_new_state.
    simpl. intuition.
    unfold LTS.raw_composed_new_state.
    simpl. intuition.
    unfold raw_composed_new_state.
    simpl. intuition.
  - rename H2 into Hl1.
    rename H0 into Hm1.
    rename H3 into Hm2.
    rename H5 into Hpid.
    inversion H1; subst; simpl in *.
    inversion H0; subst; simpl in *.
    exists (
      mkSyncState 
        (LTS.linked_lts
          (LTS.raw_compose L1 (linked_lts (raw_compose M1 M2))))
      (@LTS.mkRawComposedState liA liC 
        L1 (ImplRawCompose.linked_lts (ImplRawCompose.raw_compose M1 M2))
          (LTS.RawL1State st1)
          (@ImplRawCompose.mkRawComposedState liA liB liC
            M1 M2
            (LTS.RawL2State st1)
            st2'
          )
      )
      ((pid, Run) :: PidPos s2)
    ).
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_initial_state_L with (pos:=PidPos); eauto.
      simpl.
      eapply LTS.raw_composed_initial_state_L2; eauto.
      simpl.
      eapply ImplRawCompose.raw_composed_initial_state_M2; eauto.
      destruct LState. simpl in *.
      destruct RawL2State. simpl in *.
      subst. auto.
  - rename H2 into Hl1.
    rename H0 into Hm1.
    rename H3 into Hm2.
    rename H5 into Hpid.
    inversion H1; subst; simpl in *.
    inversion H0; subst; simpl in *.
    exists (
      mkSyncState 
        (LTS.linked_lts
          (LTS.raw_compose L1 (linked_lts (raw_compose M1 M2))))
      (@LTS.mkRawComposedState liA liC 
        L1 (ImplRawCompose.linked_lts (ImplRawCompose.raw_compose M1 M2))
          (LTS.RawL1State st1)
          (@ImplRawCompose.mkRawComposedState liA liB liC
            M1 M2
            (LTS.RawL2State st1)
            st2'
          )
      )
      (remove (PidPos s2) pid)
    ).
    simpl. intuition.
      destruct s2. simpl in *.
      eapply sync_final_state_L with (pos:=PidPos); eauto.
      simpl.
      eapply LTS.raw_composed_final_state_L2; eauto.
      simpl.
      eapply ImplRawCompose.raw_composed_final_state_M2; eauto.
      destruct LState. simpl in *.
      destruct RawL2State. simpl in *.
      subst. auto.
  - rename H2 into Hl1.
    rename H0 into Hm1.
    rename H3 into Hm2.
    rename H5 into Hpid.
    inversion H1; subst; simpl in *.
    inversion H0; subst; simpl in *.
    (* step of M2 *)
    --
    inversion H2; subst; simpl in *.
    exists (
      mkSyncState 
        (LTS.linked_lts
          (LTS.raw_compose L1 (linked_lts (raw_compose M1 M2))))
      (@LTS.mkRawComposedState liA liC 
        L1 (ImplRawCompose.linked_lts (ImplRawCompose.raw_compose M1 M2))
          (LTS.RawL1State st1)
          (@ImplRawCompose.mkRawComposedState liA liB liC
            M1 M2
            (LTS.RawL2State st1)
            st2'
          )
      )
      (PidPos s2)
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply sync_step_L_internal with (pos:=PidPos); eauto.
    simpl.
    eapply LTS.linked_step_int_L2; eauto.
    eapply LTS.raw_composed_step_L2_internal; eauto.
      simpl.
      eapply ImplRawCompose.linked_step_int_L2; eauto.
      eapply ImplRawCompose.raw_composed_step_M2_internal; eauto.
    destruct LState. simpl in *.
    destruct RawL2State. simpl in *.
    subst. auto.
    (* step of (rawcompose L1 M1) *)
    --
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    (* step of M1 *)
    ---
    inversion H4; subst; simpl in *.
    exists (
      mkSyncState 
        (LTS.linked_lts
          (LTS.raw_compose L1 (linked_lts (raw_compose M1 M2))))
      (@LTS.mkRawComposedState liA liC 
        L1 (ImplRawCompose.linked_lts (ImplRawCompose.raw_compose M1 M2))
          st0
          (@ImplRawCompose.mkRawComposedState liA liB liC
            M1 M2
            st2'
            (RawL2State (LTS.RawL2State (LState s2)))
          )
      )
      (PidPos s2)
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply sync_step_L_internal with (pos:=PidPos); eauto.
    simpl.
    eapply LTS.linked_step_int_L2; eauto.
    eapply LTS.raw_composed_step_L2_internal; eauto.
    simpl.
    eapply ImplRawCompose.linked_step_int_L1; eauto.
    eapply ImplRawCompose.raw_composed_step_M1_internal; eauto.
    destruct LState. simpl in *.
    destruct RawL2State. simpl in *.
    subst. auto.
    (* step of L1 *)
    ---
    inversion H4; subst; simpl in *.
    exists (
      mkSyncState 
        (LTS.linked_lts
          (LTS.raw_compose L1 (linked_lts (raw_compose M1 M2))))
      (@LTS.mkRawComposedState liA liC 
        L1 (ImplRawCompose.linked_lts (ImplRawCompose.raw_compose M1 M2))
          st1'0
          (@ImplRawCompose.mkRawComposedState liA liB liC
            M1 M2
            st2
            (RawL2State (LTS.RawL2State (LState s2)))
          )
      )
      (PidPos s2)
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply sync_step_L_internal with (pos:=PidPos); eauto.
    simpl.
    eapply LTS.linked_step_int_L1; eauto.
    eapply LTS.raw_composed_step_L1_internal; eauto.
    simpl.
    destruct LState. simpl in *.
    destruct RawL2State. simpl in *.
    subst. auto.
    (* M1 query L1 *)
    ---
    inversion H4; subst; simpl in *.
    exists (
      mkSyncState 
        (LTS.linked_lts
          (LTS.raw_compose L1 (linked_lts (raw_compose M1 M2))))
      (@LTS.mkRawComposedState liA liC 
        L1 (ImplRawCompose.linked_lts (ImplRawCompose.raw_compose M1 M2))
          st1'0
          (@ImplRawCompose.mkRawComposedState liA liB liC
            M1 M2
            st2'
            (RawL2State (LTS.RawL2State (LState s2)))
          )
      )
      (PidPos s2)
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply sync_step_L_internal with (pos:=PidPos); eauto.
    simpl.
    eapply LTS.linked_step_L2_push; eauto.
    eapply LTS.raw_composed_step_L2_push; eauto.
      simpl.
      eapply ImplRawCompose.raw_composed_at_external_M1; eauto.
    destruct LState. simpl in *.
    destruct RawL2State. simpl in *.
    subst. auto.
    (* L1 reply M1 *)
    ---
    inversion H4; subst; simpl in *.
    exists (
      mkSyncState 
        (LTS.linked_lts
          (LTS.raw_compose L1 (linked_lts (raw_compose M1 M2))))
      (@LTS.mkRawComposedState liA liC 
        L1 (ImplRawCompose.linked_lts (ImplRawCompose.raw_compose M1 M2))
          st1'0
          (@ImplRawCompose.mkRawComposedState liA liB liC
            M1 M2
            st2'
            (RawL2State (LTS.RawL2State (LState s2)))
          )
      )
      (PidPos s2)
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply sync_step_L_internal with (pos:=PidPos); eauto.
    simpl.
    eapply LTS.linked_step_L1_pop; eauto.
    eapply LTS.raw_composed_step_L1_pop; eauto.
      simpl.
      eapply ImplRawCompose.raw_composed_after_external_M1; eauto.
    destruct LState. simpl in *.
    destruct RawL2State. simpl in *.
    subst. auto.
    (* M2 query (raw_compose L1 M1) *)
    --
    inversion H2; subst; simpl in *.
    inversion H5; subst; simpl in *.
    exists (
      mkSyncState 
        (LTS.linked_lts
          (LTS.raw_compose L1 (linked_lts (raw_compose M1 M2))))
      (@LTS.mkRawComposedState liA liC 
        L1 (ImplRawCompose.linked_lts (ImplRawCompose.raw_compose M1 M2))
          st3
          (@ImplRawCompose.mkRawComposedState liA liB liC
            M1 M2
            st2'0
            st2'
          )
      )
      (PidPos s2)
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply sync_step_L_internal with (pos:=PidPos); eauto.
    simpl.
    eapply LTS.linked_step_int_L2; eauto.
    eapply LTS.raw_composed_step_L2_internal; eauto.
      simpl.
      eapply ImplRawCompose.linked_step_L2_push; eauto.
      eapply ImplRawCompose.raw_composed_step_M2_push; eauto.
    destruct LState. simpl in *.
    destruct RawL2State. simpl in *.
    subst. auto.
    (* (raw_compose L1 M1) reply M2 *)
    --
    inversion H2; subst; simpl in *.
    inversion H3; subst; simpl in *.
    exists (
      mkSyncState 
        (LTS.linked_lts
          (LTS.raw_compose L1 (linked_lts (raw_compose M1 M2))))
      (@LTS.mkRawComposedState liA liC 
        L1 (ImplRawCompose.linked_lts (ImplRawCompose.raw_compose M1 M2))
          st0
          (@ImplRawCompose.mkRawComposedState liA liB liC
            M1 M2
            st2'0
            st2'
          )
      )
      (PidPos s2)
    ).
    simpl. intuition.
    destruct s2. simpl in *.
    eapply Step_Internal; eauto.
    2 : { eapply Step_None; eauto. }
    simpl.
    eapply sync_step_L_internal with (pos:=PidPos); eauto.
    simpl.
    eapply LTS.linked_step_int_L2; eauto.
    eapply LTS.raw_composed_step_L2_internal; eauto.
      simpl.
      eapply ImplRawCompose.linked_step_L1_pop; eauto.
      eapply ImplRawCompose.raw_composed_step_M1_pop; eauto.
    destruct LState. simpl in *.
    destruct RawL2State. simpl in *.
    subst. auto.
Qed.

(* Notation " M ◁ M' " := (linked_lts (ImplRawCompose.raw_compose M M')) (at level 67).
Notation " M ⊑ M' " := (impl_refines M M') (at level 67).
Notation " 'sc' M " := (sync M) (at level 67). *)

Theorem Link:
  L1 ⊢ M1 ◁ M2 ~: L2 ->
  M1 ⊑ (sc M1) ->
  M2 ⊑ (sc M2) ->
  (LTS.linked_lts (LTS.raw_compose L1 M1)) ⊢ M2 ~: L2.
Proof.
  unfold veriobj.
  intros. intuition.
  apply simple_raw_compose_consistency; auto.
  eapply trans_refinement; eauto.
  eapply trans_refinement; eauto.
  2: {
    eapply sync_raw_compose_refines_compose; eauto.
  }
  eapply trans_refinement; eauto.
  eapply compose_consistency; eauto.
  apply raw_compose_assoc'.
Qed.

End Link.