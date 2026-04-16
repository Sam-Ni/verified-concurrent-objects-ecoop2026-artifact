Require Import
  List
  LTS
  SyncLTS.
Import ListNotations.

Section INV.

Context {liA liB liC : language_interface }.
Variable L : composed_lts.composed_lts liA liB liC.

Lemma valid_execution_fragment_preserves_inv': forall s s' acts inv,
  composed_lts.valid_execution_fragment L s s' acts ->
  composed_lts.invariant_ind L inv ->
  inv s ->
  inv s'.
Proof.
  induction 1; intros.
  subst. assumption.
  all : apply IHvalid_execution_fragment; auto;
    apply H1 in H; auto.
Qed.

Lemma invariant_ind_to_invariant': forall P,
  composed_lts.invariant_ind L P ->
  composed_lts.invariant L P.
Proof.
  intros.
  unfold composed_lts.invariant. intros.
  unfold composed_lts.reachable in H0.
  destruct H0 as [init [acts [Hnew Hvalid]]].
  eapply valid_execution_fragment_preserves_inv'; eauto.
  apply H; auto.
Qed.

Lemma reachable_is_invariant: composed_lts.invariant_ind L (composed_lts.reachable L).
Proof.
  unfold composed_lts.invariant_ind. intuition.
  - unfold composed_lts.reachable.
    exists st.
    exists [].
    intuition.
    eapply composed_lts.Step_None; eauto.
  - unfold composed_lts.reachable in *.
    destruct H as [init [acts [Hnew Hvalid]]].
    exists init.
    exists acts.
    intuition.
    eapply composed_lts.valid_execution_fragment_join'
      with (a:=acts) (a':=[]); simpl; eauto.
    eapply composed_lts.Step_Internal_L1; eauto.
    eapply composed_lts.Step_None; eauto.
    rewrite app_nil_r; auto.
  - unfold composed_lts.reachable in *.
    destruct H as [init [acts [Hnew Hvalid]]].
    exists init.
    exists acts.
    intuition.
    eapply composed_lts.valid_execution_fragment_join'
      with (a:=acts) (a':=[]); simpl; eauto.
    eapply composed_lts.Step_Internal_L2; eauto.
    eapply composed_lts.Step_None; eauto.
    rewrite app_nil_r; auto.
  - unfold composed_lts.reachable in *.
    destruct H as [init [acts [Hnew Hvalid]]].
    exists init.
    eexists.
    intuition.
    eapply composed_lts.valid_execution_fragment_join'
      with (a:=acts); simpl; eauto.
    eapply composed_lts.Step_Initial_Call; eauto.
    eapply composed_lts.Step_None; eauto.
  - unfold composed_lts.reachable in *.
    destruct H as [init [acts [Hnew Hvalid]]].
    exists init.
    eexists.
    intuition.
    eapply composed_lts.valid_execution_fragment_join'
      with (a:=acts); simpl; eauto.
    eapply composed_lts.Step_At_External; eauto.
    eapply composed_lts.Step_None; eauto.
  - unfold composed_lts.reachable in *.
    destruct H as [init [acts [Hnew Hvalid]]].
    exists init.
    eexists.
    intuition.
    eapply composed_lts.valid_execution_fragment_join'
      with (a:=acts); simpl; eauto.
    eapply composed_lts.Step_After_External; eauto.
    eapply composed_lts.Step_None; eauto.
  - unfold composed_lts.reachable in *.
    destruct H as [init [acts [Hnew Hvalid]]].
    exists init.
    eexists.
    intuition.
    eapply composed_lts.valid_execution_fragment_join'
      with (a:=acts); simpl; eauto.
    eapply composed_lts.Step_Final_Return; eauto.
    eapply composed_lts.Step_None; eauto.
  - unfold composed_lts.reachable in *.
    destruct H as [init [acts [Hnew Hvalid]]].
    exists init.
    eexists.
    intuition.
    eapply composed_lts.valid_execution_fragment_join'
      with (a:=acts); simpl; eauto.
    eapply composed_lts.Step_Internal_Query; eauto.
    eapply composed_lts.Step_None; eauto.
  - unfold composed_lts.reachable in *.
    destruct H as [init [acts [Hnew Hvalid]]].
    exists init.
    eexists.
    intuition.
    eapply composed_lts.valid_execution_fragment_join'
      with (a:=acts); simpl; eauto.
    eapply composed_lts.Step_Internal_Reply; eauto.
    eapply composed_lts.Step_None; eauto.
Qed.

End INV.

Section test.

Context {liA liB : language_interface }.
Variable L : lts liA liB.

Lemma reachable_is_invariant': invariant_ind L (reachable L).
Proof.
  unfold invariant_ind. intuition.
  - unfold reachable.
    exists st.
    exists [].
    intuition.
    eapply Step_None; eauto.
  - unfold reachable in *.
    destruct H as [init [acts [Hnew Hvalid]]].
    exists init.
    exists acts.
    intuition.
    eapply valid_execution_fragment_join'
      with (a:=acts) (a':=[]); simpl; eauto.
    eapply Step_Internal; eauto.
    eapply Step_None; eauto.
    rewrite app_nil_r; auto.
  - unfold reachable in *.
    destruct H as [init [acts [Hnew Hvalid]]].
    exists init.
    eexists.
    intuition.
    eapply valid_execution_fragment_join'
      with (a:=acts); simpl; eauto.
    eapply Step_Initial_Call; eauto.
    eapply Step_None; eauto.
  - unfold reachable in *.
    destruct H as [init [acts [Hnew Hvalid]]].
    exists init.
    eexists.
    intuition.
    eapply valid_execution_fragment_join'
      with (a:=acts); simpl; eauto.
    eapply Step_At_External; eauto.
    eapply Step_None; eauto.
  - unfold reachable in *.
    destruct H as [init [acts [Hnew Hvalid]]].
    exists init.
    eexists.
    intuition.
    eapply valid_execution_fragment_join'
      with (a:=acts); simpl; eauto.
    eapply Step_After_External; eauto.
    eapply Step_None; eauto.
  - unfold reachable in *.
    destruct H as [init [acts [Hnew Hvalid]]].
    exists init.
    eexists.
    intuition.
    eapply valid_execution_fragment_join'
      with (a:=acts); simpl; eauto.
    eapply Step_Final_Return; eauto.
    eapply Step_None; eauto.
Qed.

Lemma sync_preserves_inv: forall inv,
  invariant_ind L inv ->
  invariant_ind (sync L) (fun s => inv s.(LState)).
Proof.
  intros.
  unfold invariant_ind in *. intuition.
  - destruct st; simpl in *.
    inversion H4; subst. intuition.
  - inversion H6; subst; simpl in *.
    eapply H; eauto.
  - inversion H6; subst; simpl in *.
    eapply H1; eauto.
  - inversion H6; subst; simpl in *.
    eapply H2; eauto.
  - inversion H6; subst; simpl in *.
    eapply H3; eauto.
  - inversion H6; subst; simpl in *.
    eapply H5; eauto.
Qed.

Definition invariant_ind' (P : state L -> Prop) (Q : state L -> Prop) :=
  invariant_ind L Q /\
  (forall st, L.(new_state) st -> P st) /\
  (forall st st' act pid,
    P st ->
    Q st ->
    step L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    Q st ->
    initial_state L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    Q st ->
    at_external L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    Q st ->
    after_external L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    Q st ->
    final_state L st pid act st' ->
    P st').

Lemma invariant_ind'_imply_invariant_ind_land: forall P Q,
  invariant_ind' P Q ->
  invariant_ind L (fun s => P s /\ Q s).
Proof.
  intros. unfold invariant_ind' in H.
  unfold invariant_ind. intuition.
  - apply H0. assumption.
  - eapply H1; eauto.
  - apply H0 in H7; auto.
  - eapply H2; eauto.
  - apply H0 in H7; auto.
  - eapply H3; eauto.
  - apply H0 in H7; auto.
  - eapply H4; eauto.
  - apply H0 in H7; auto.
  - eapply H6; eauto.
  - apply H0 in H7; auto.
Qed.

Lemma valid_execution_fragment_preserves_inv: forall s s' acts inv,
  valid_execution_fragment L s s' acts ->
  invariant_ind L inv ->
  inv s ->
  inv s'.
Proof.
  induction 1; intros.
  subst. assumption.
  all : apply IHvalid_execution_fragment; auto;
    apply H1 in H; auto.
Qed.

Lemma invariant_ind_to_invariant: forall P,
  invariant_ind L P ->
  invariant L P.
Proof.
  intros.
  unfold invariant. intros.
  unfold reachable in H0.
  destruct H0 as [init [acts [Hnew Hvalid]]].
  eapply valid_execution_fragment_preserves_inv; eauto.
  apply H; auto.
Qed.

Lemma test: forall P,
  invariant L P ->
  invariant_ind L (fun s => P s /\ reachable L s).
Proof.
  intros.
  apply invariant_ind'_imply_invariant_ind_land.
  unfold invariant_ind'.
  intuition.
  apply reachable_is_invariant'.
  unfold invariant in H.
  assert (reachable L st).
  unfold reachable.
  exists st, []. intuition.
  eapply Step_None; eauto.
  intuition.
  assert (reachable L st').
  unfold reachable in *.
  destruct H1 as [init [acts [Hnew Hvalid]]].
  exists init.
  eexists. intuition.
  eapply valid_execution_fragment_join' with (a:=acts); eauto.
  eapply Step_Internal; eauto.
  eapply Step_None; eauto.
  intuition.
  assert (reachable L st').
  unfold reachable in *.
  destruct H1 as [init [acts [Hnew Hvalid]]].
  exists init.
  eexists. intuition.
  eapply valid_execution_fragment_join' with (a:=acts); eauto.
  eapply Step_Initial_Call; eauto.
  eapply Step_None; eauto.
  intuition.
  assert (reachable L st').
  unfold reachable in *.
  destruct H1 as [init [acts [Hnew Hvalid]]].
  exists init.
  eexists. intuition.
  eapply valid_execution_fragment_join' with (a:=acts); eauto.
  eapply Step_At_External; eauto.
  eapply Step_None; eauto.
  intuition.
  assert (reachable L st').
  unfold reachable in *.
  destruct H1 as [init [acts [Hnew Hvalid]]].
  exists init.
  eexists. intuition.
  eapply valid_execution_fragment_join' with (a:=acts); eauto.
  eapply Step_After_External; eauto.
  eapply Step_None; eauto.
  intuition.
  assert (reachable L st').
  unfold reachable in *.
  destruct H1 as [init [acts [Hnew Hvalid]]].
  exists init.
  eexists. intuition.
  eapply valid_execution_fragment_join' with (a:=acts); eauto.
  eapply Step_Final_Return; eauto.
  eapply Step_None; eauto.
  intuition.
Qed.

Lemma invariant_weaken: forall P Q,
  invariant L (fun s => P s /\ Q s) ->
  invariant L P.
Proof.
  intros.
  unfold invariant in *.
  intros.
  apply H in H0.
  intuition.
Qed.

End test.

Section test.

Context {liA liB liC : language_interface }.

Variable L : composed_lts.composed_lts liA liB liC.

Definition about (P Q : composed_lts.state L -> Prop) :=
  (forall st, L.(composed_lts.new_state) st -> P st) /\
  (forall st st' act pid,
    P st ->
    Q st ->
    composed_lts.step_L1 L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    Q st ->
    composed_lts.step_L2 L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    Q st ->
    composed_lts.initial_state L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    Q st ->
    composed_lts.at_external L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    Q st ->
    composed_lts.after_external L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    Q st ->
    composed_lts.final_state L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    Q st ->
    composed_lts.internal_query L st pid act st' ->
    P st') /\
  (forall st st' act pid,
    P st ->
    Q st ->
    composed_lts.internal_reply L st pid act st' ->
    P st')
  .

Definition invariant_ind'' (P : composed_lts.state L -> Prop) (Q : composed_lts.state L -> Prop) :=
  composed_lts.invariant_ind L Q /\
  about P Q.

Lemma invariant_ind''_imply_invariant_ind_land: forall P Q,
  invariant_ind'' P Q ->
  composed_lts.invariant_ind L (fun s => P s /\ Q s).
Proof.
  intros. unfold invariant_ind'' in H.
  unfold about in H.
  unfold composed_lts.invariant_ind. intuition.
  - apply H0. assumption.
  - eapply H1; eauto.
  - apply H0 in H10; auto.
  - eapply H2; eauto.
  - apply H0 in H10; auto.
  - eapply H3; eauto.
  - apply H0 in H10; auto.
  - eapply H4; eauto.
  - apply H0 in H10; auto.
  - eapply H5; eauto.
  - apply H0 in H10; auto.
  - eapply H6; eauto.
  - apply H0 in H10; auto.
  - eapply H7; eauto.
  - apply H0 in H10; auto.
  - eapply H9; eauto.
  - apply H0 in H10; auto.
Qed.

Lemma invariant_ind_sym : forall P Q,
  composed_lts.invariant_ind L (fun s => Q s /\ P s) ->
  composed_lts.invariant_ind L (fun s => P s /\ Q s).
Proof.
  intros. unfold composed_lts.invariant_ind in H.
  unfold composed_lts.invariant_ind.
  intuition.
  - apply H0; auto.
  - apply H0; auto.
  - eapply H; eauto.
  - eapply H; eauto.
  - eapply H1; eauto.
  - eapply H1; eauto.
  - eapply H2; eauto.
  - eapply H2; eauto.
  - eapply H3; eauto.
  - eapply H3; eauto.
  - eapply H4; eauto.
  - eapply H4; eauto.
  - eapply H5; eauto.
  - eapply H5; eauto.
  - eapply H6; eauto.
  - eapply H6; eauto.
  - eapply H8; eauto.
  - eapply H8; eauto.
Qed.

Definition invariant_mutual_ind' (P Q : composed_lts.state L -> Prop) :=
  about P Q /\ about Q P.

Lemma invariant_ind_break_down': forall P Q,
  invariant_mutual_ind' P Q ->
  composed_lts.invariant_ind L (fun s => P s /\ Q s).
Proof.
  intros.
  unfold composed_lts.invariant_ind.
  unfold invariant_mutual_ind' in H.
  destruct H as [HP HQ].
  destruct HP as [HnewP [Hstep1P [Hstep2P [HinitP [HatP [HafterP [HfinalP [Hint_queryP Hint_replyP]]]]]]]].
  destruct HQ as [HnewQ [Hstep1Q [Hstep2Q [HinitQ [HatQ [HafterQ [HfinalQ [Hint_queryQ Hint_replyQ]]]]]]]].
  intuition.
  - apply Hstep1P in H0; auto.
  - apply Hstep1Q in H0; auto.
  - apply Hstep2P in H0; auto.
  - apply Hstep2Q in H0; auto.
  - apply HinitP in H0; auto.
  - apply HinitQ in H0; auto.
  - apply HatP in H0; auto.
  - apply HatQ in H0; auto.
  - apply HafterP in H0; auto.
  - apply HafterQ in H0; auto.
  - apply HfinalP in H0; auto.
  - apply HfinalQ in H0; auto.
  - apply Hint_queryP in H0; auto.
  - apply Hint_queryQ in H0; auto.
  - apply Hint_replyP in H0; auto.
  - apply Hint_replyQ in H0; auto.
Qed.

End test.