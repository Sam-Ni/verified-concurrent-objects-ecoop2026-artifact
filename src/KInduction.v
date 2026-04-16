Require Import
  List
  Arith
  Lia
  LTS.
Import ListNotations.

Section NatInduction.

Definition strong_induct (nP : nat->Prop) : Prop :=
  nP 0 /\
  (forall n : nat,
    (forall k : nat, k <= n -> nP k) ->
    nP (S n))
.

Lemma leq_implies_le_or_eq: forall m n : nat,
  m <= S n -> m <= n \/ m = S n.
Proof.
  lia.
Qed.

Lemma strong_induct_is_correct : forall (nP : nat->Prop),
  strong_induct nP -> (forall n k, k <= n -> nP k).
Proof.
  intros nP [Hl Hr] n.
  induction n as [|n' IHn].
  - intros k Hk. inversion Hk. apply Hl.
  - intros k Hk. apply leq_implies_le_or_eq in Hk.
    destruct Hk as [Hkle | Hkeq].
    + apply IHn. apply Hkle.
    + rewrite Hkeq. apply Hr in IHn. apply IHn.
Qed.

Lemma strong_induct_is_correct_prettier : forall (nP : nat->Prop),
  strong_induct nP -> (forall n, nP n).
Proof.
  intros nP H n.
  apply (strong_induct_is_correct nP H n n).
  auto.
Qed.

Lemma nat_ind2 (P : nat -> Prop) : 
  P 0 ->
  (forall n : nat,
    (forall k : nat, k <= n -> P k) ->
    P (S n)) ->
  forall n, P n.
Proof.
  intros Hl Hr n.
  apply strong_induct_is_correct_prettier.
  unfold strong_induct. intuition.
Qed.

End NatInduction.

Section test.

Context {liA liB : language_interface}.
Variable L : lts liA liB.

Inductive valid_execution_fragment_len (st st' : L.(state)) : list event -> nat -> Prop :=
| Step_None_len :
    st = st' ->
    valid_execution_fragment_len st st' nil O
| Step_Internal_len : forall st'' acts (int : L.(internal)) pid n,
    step L st pid int st'' ->
    valid_execution_fragment_len st'' st' acts n ->
    valid_execution_fragment_len st st' acts (S n)
| Step_At_External_len : forall st'' acts qa pid n,
    at_external L st pid qa st'' ->
    valid_execution_fragment_len st'' st' acts n ->
    valid_execution_fragment_len st st' ((pid, event_invA qa) :: acts) (S n)
| Step_After_External_len : forall st'' acts ra pid n,
    after_external L st pid ra st'' ->
    valid_execution_fragment_len st'' st' acts n ->
    valid_execution_fragment_len st st' ((pid, event_resA ra) :: acts) (S n)
| Step_Initial_Call_len : forall st'' acts qb pid n,
    initial_state L st pid qb st'' ->
    valid_execution_fragment_len st'' st' acts n ->
    valid_execution_fragment_len st st' ((pid, event_invB qb) :: acts) (S n)
| Step_Final_Return_len : forall st'' acts rb pid n,
    final_state L st pid rb st'' ->
    valid_execution_fragment_len st'' st' acts n ->
    valid_execution_fragment_len st st' ((pid, event_resB rb) :: acts) (S n)
.

Definition reachable_len st n :=
  exists init acts , L.(new_state) init /\ valid_execution_fragment_len init st acts n.

Definition k_induction (P : L.(state) -> Prop) :=
  (forall s, L.(new_state) s -> P s) /\
  (forall n s,
    (forall k, k <= n -> forall st, reachable_len st k -> P st) ->
    reachable_len s (S n) -> P s).

Definition invariant_len (P : state L -> Prop) :=
  forall st n, reachable_len st n -> P st.

Lemma k_induction_to_invariant_len P :
  k_induction P ->
  invariant_len P.
Proof.
  intros. unfold k_induction in H.
  unfold invariant_len.
  intros.
  generalize dependent st.
  induction n using nat_ind2; intros; auto.
  - unfold reachable_len in H0.
    destruct H0 as [init [acts [Hnew Hvalid]]].
    inversion Hvalid; subst.
    apply H; auto.
  -  
   simpl.
   apply H in H1; auto.
Qed.

Lemma valid_execution_fragment_to_valid_execution_fragment_len : forall st st' acts,
  valid_execution_fragment L st st' acts ->
  exists n, valid_execution_fragment_len st st' acts n.
Proof.
  induction 1; intros.
  - subst. exists O.
    eapply Step_None_len; eauto.
  - destruct IHvalid_execution_fragment as [n Hvalid].
    exists (S n).
    eapply Step_Internal_len; eauto.
  - destruct IHvalid_execution_fragment as [n Hvalid].
    exists (S n).
    eapply Step_At_External_len; eauto.
  - destruct IHvalid_execution_fragment as [n Hvalid].
    exists (S n).
    eapply Step_After_External_len; eauto.
  - destruct IHvalid_execution_fragment as [n Hvalid].
    exists (S n).
    eapply Step_Initial_Call_len; eauto.
  - destruct IHvalid_execution_fragment as [n Hvalid].
    exists (S n).
    eapply Step_Final_Return_len; eauto.
Qed.

Lemma reachable_to_reachable_len: forall st,
  reachable L st ->
  exists n, reachable_len st n.
Proof.
  unfold reachable.
  unfold reachable_len.
  intros.
  destruct H as [init [acts [Hnew Hvalid]]].
  apply valid_execution_fragment_to_valid_execution_fragment_len in Hvalid.
  destruct Hvalid as [n Hvalid'].
  exists n.
  exists init.
  exists acts.
  intuition.
Qed.

Lemma invariant_len_to_invariant: forall P,
  invariant_len P ->
  invariant L P.
Proof.
  unfold invariant_len.
  unfold invariant.
  intros.
  apply reachable_to_reachable_len in H0.
  destruct H0 as [n Hvalid].
  eapply H; eauto.
Qed.

Lemma k_induction_to_invariant : forall P,
  k_induction P ->
  invariant L P.
Proof.
  intros.
  apply invariant_len_to_invariant.
  apply k_induction_to_invariant_len; auto.
Qed.

Hint Constructors valid_execution_fragment_len : core.

Lemma valid_execution_fragment_len_join : forall (s s' s'' : L.(state)) a a' n n',
    valid_execution_fragment_len s s' a n ->
    valid_execution_fragment_len s' s'' a' n' ->
    valid_execution_fragment_len s s'' (a ++ a') (n + n').
Proof.
  intros.
  induction H; subst; simpl; intros; eauto.
Qed.

Lemma valid_execution_fragment_len_join' : forall (s s' s'' : L.(state)) a a' a'' n n' n'',
    valid_execution_fragment_len s s' a n ->
    valid_execution_fragment_len s' s'' a' n' ->
    a'' = a ++ a' ->
    n'' = n + n' ->
    valid_execution_fragment_len s s'' (a ++ a') (n + n').
Proof.
  intros; subst; eauto using valid_execution_fragment_len_join.
Qed.

Lemma valid_execution_fragment_reach_len : forall s s' n n' acts,
  valid_execution_fragment_len s s' acts n' ->
  reachable_len s n ->
  reachable_len s' (n + n').
Proof.
  intros.
  generalize dependent n.
  induction H; intros.
  - subst.
    rewrite Nat.add_0_r. assumption.
  - rewrite <-Nat.add_succ_comm.
    eapply IHvalid_execution_fragment_len; eauto.
    unfold reachable_len in H1.
    unfold reachable_len.
    destruct H1 as [init [acts' [Hnew Hvalid]]].
    exists init.
    exists (acts' ++ []). 
    intuition.
    replace (S n0) with (n0 + 1).
    eapply valid_execution_fragment_len_join' with (a:=acts') (n:=n0); eauto.
    lia.
  - rewrite <-Nat.add_succ_comm.
    eapply IHvalid_execution_fragment_len; eauto.
    unfold reachable_len in H1.
    unfold reachable_len.
    destruct H1 as [init [acts' [Hnew Hvalid]]].
    exists init.
    eexists.
    intuition.
    replace (S n0) with (n0 + 1).
    eapply valid_execution_fragment_len_join' with (a:=acts') (n:=n0); eauto.
    eapply Step_At_External_len; eauto.
    lia.
  - rewrite <-Nat.add_succ_comm.
    eapply IHvalid_execution_fragment_len; eauto.
    unfold reachable_len in H1.
    unfold reachable_len.
    destruct H1 as [init [acts' [Hnew Hvalid]]].
    exists init.
    eexists.
    intuition.
    replace (S n0) with (n0 + 1).
    eapply valid_execution_fragment_len_join' with (a:=acts') (n:=n0); eauto.
    eapply Step_After_External_len; eauto.
    lia.
  - rewrite <-Nat.add_succ_comm.
    eapply IHvalid_execution_fragment_len; eauto.
    unfold reachable_len in H1.
    unfold reachable_len.
    destruct H1 as [init [acts' [Hnew Hvalid]]].
    exists init.
    eexists.
    intuition.
    replace (S n0) with (n0 + 1).
    eapply valid_execution_fragment_len_join' with (a:=acts') (n:=n0); eauto.
    eapply Step_Initial_Call_len; eauto.
    lia.
  - rewrite <-Nat.add_succ_comm.
    eapply IHvalid_execution_fragment_len; eauto.
    unfold reachable_len in H1.
    unfold reachable_len.
    destruct H1 as [init [acts' [Hnew Hvalid]]].
    exists init.
    eexists.
    intuition.
    replace (S n0) with (n0 + 1).
    eapply valid_execution_fragment_len_join' with (a:=acts') (n:=n0); eauto.
    eapply Step_Final_Return_len; eauto.
    lia.
Qed.

End test.

Section KInduction.

Context {liA liB liC: language_interface}.
Variable L : composed_lts.composed_lts liA liB liC.

Inductive valid_execution_fragment_len' (st st' : L.(composed_lts.state)) : list (@composed_lts.event liA liB liC) -> nat -> Prop :=
| Step_None_len' :
    st = st' ->
    valid_execution_fragment_len' st st' nil 0
| Step_Internal_L1_len' : forall st'' acts (int : L.(composed_lts.internal_L1)) pid n,
    composed_lts.step_L1 L st pid int st'' ->
    valid_execution_fragment_len' st'' st' acts n ->
    valid_execution_fragment_len' st st' acts (S n)
| Step_Internal_L2_len' : forall st'' acts (int : L.(composed_lts.internal_L2)) pid n,
    composed_lts.step_L2 L st pid int st'' ->
    valid_execution_fragment_len' st'' st' acts n ->
    valid_execution_fragment_len' st st' acts (S n)
| Step_At_External_len' : forall st'' acts qa pid n,
    composed_lts.at_external L st pid qa st'' ->
    valid_execution_fragment_len' st'' st' acts n ->
    valid_execution_fragment_len' st st' ((pid, composed_lts.event_invA qa) :: acts) (S n)
| Step_After_External_len' : forall st'' acts ra pid n,
    composed_lts.after_external L st pid ra st'' ->
    valid_execution_fragment_len' st'' st' acts n ->
    valid_execution_fragment_len' st st' ((pid, composed_lts.event_resA ra) :: acts) (S n)
| Step_Initial_Call_len' : forall st'' acts qc pid n,
    composed_lts.initial_state L st pid qc st'' ->
    valid_execution_fragment_len' st'' st' acts n ->
    valid_execution_fragment_len' st st' ((pid, composed_lts.event_invC qc) :: acts) (S n)
| Step_Final_Return_len' : forall st'' acts rc pid n,
    composed_lts.final_state L st pid rc st'' ->
    valid_execution_fragment_len' st'' st' acts n ->
    valid_execution_fragment_len' st st' ((pid, composed_lts.event_resC rc) :: acts) (S n)
| Step_Internal_Query_len' : forall st'' acts qb pid n,
    composed_lts.internal_query L st pid qb st'' ->
    valid_execution_fragment_len' st'' st' acts n ->
    valid_execution_fragment_len' st st' ((pid, composed_lts.event_invB qb) :: acts) (S n)
| Step_Internal_Reply_len' : forall st'' acts rb pid n,
    composed_lts.internal_reply L st pid rb st'' ->
    valid_execution_fragment_len' st'' st' acts n ->
    valid_execution_fragment_len' st st' ((pid, composed_lts.event_resB rb) :: acts) (S n)
.

Definition reachable_len' st n :=
  exists init acts , L.(composed_lts.new_state) init /\ valid_execution_fragment_len' init st acts n.

Definition k_induction' (P : L.(composed_lts.state) -> Prop) :=
  (forall s, L.(composed_lts.new_state) s -> P s) /\
  (forall n s,
    (forall k, k <= n -> forall st, reachable_len' st k -> P st) ->
    reachable_len' s (S n) -> P s).

Definition invariant_len' (P : composed_lts.state L -> Prop) :=
  forall st n, reachable_len' st n -> P st.

Lemma k_induction_to_invariant_len' P :
  k_induction' P ->
  invariant_len' P.
Proof.
  intros. unfold k_induction' in H.
  unfold invariant_len'.
  intros.
  generalize dependent st.
  induction n using nat_ind2; intros; auto.
  - unfold reachable_len' in H0.
    destruct H0 as [init [acts [Hnew Hvalid]]].
    inversion Hvalid; subst.
    apply H; auto.
  -  
   simpl.
   apply H in H1; auto.
Qed.

Lemma valid_execution_fragment_to_valid_execution_fragment_len' : forall st st' acts,
  composed_lts.valid_execution_fragment L st st' acts ->
  exists n, valid_execution_fragment_len' st st' acts n.
Proof.
  induction 1; intros.
  - subst. exists O.
    eapply Step_None_len'; eauto.
  - destruct IHvalid_execution_fragment as [n Hvalid].
    exists (S n).
    eapply Step_Internal_L1_len'; eauto.
  - destruct IHvalid_execution_fragment as [n Hvalid].
    exists (S n).
    eapply Step_Internal_L2_len'; eauto.
  - destruct IHvalid_execution_fragment as [n Hvalid].
    exists (S n).
    eapply Step_At_External_len'; eauto.
  - destruct IHvalid_execution_fragment as [n Hvalid].
    exists (S n).
    eapply Step_After_External_len'; eauto.
  - destruct IHvalid_execution_fragment as [n Hvalid].
    exists (S n).
    eapply Step_Initial_Call_len'; eauto.
  - destruct IHvalid_execution_fragment as [n Hvalid].
    exists (S n).
    eapply Step_Final_Return_len'; eauto.
  - destruct IHvalid_execution_fragment as [n Hvalid].
    exists (S n).
    eapply Step_Internal_Query_len'; eauto.
  - destruct IHvalid_execution_fragment as [n Hvalid].
    exists (S n).
    eapply Step_Internal_Reply_len'; eauto.
Qed.

Lemma reachable_to_reachable_len': forall st,
  composed_lts.reachable L st ->
  exists n, reachable_len' st n.
Proof.
  unfold composed_lts.reachable.
  unfold reachable_len'.
  intros.
  destruct H as [init [acts [Hnew Hvalid]]].
  apply valid_execution_fragment_to_valid_execution_fragment_len' in Hvalid.
  destruct Hvalid as [n Hvalid'].
  exists n.
  exists init.
  exists acts.
  intuition.
Qed.

Lemma invariant_len_to_invariant': forall P,
  invariant_len' P ->
  composed_lts.invariant L P.
Proof.
  unfold invariant_len'.
  unfold composed_lts.invariant.
  intros.
  apply reachable_to_reachable_len' in H0.
  destruct H0 as [n Hvalid].
  eapply H; eauto.
Qed.

Lemma k_induction_to_invariant' : forall P,
  k_induction' P ->
  composed_lts.invariant L P.
Proof.
  intros.
  apply invariant_len_to_invariant'.
  apply k_induction_to_invariant_len'; auto.
Qed.

Hint Constructors valid_execution_fragment_len' : core.

Lemma valid_execution_fragment_len'_join : forall (s s' s'' : L.(composed_lts.state)) a a' n n',
    valid_execution_fragment_len' s s' a n ->
    valid_execution_fragment_len' s' s'' a' n' ->
    valid_execution_fragment_len' s s'' (a ++ a') (n + n').
Proof.
  intros.
  induction H; subst; simpl; intros; eauto.
Qed.

Lemma valid_execution_fragment_len'_join' : forall (s s' s'' : L.(composed_lts.state)) a a' a'' n n' n'',
    valid_execution_fragment_len' s s' a n ->
    valid_execution_fragment_len' s' s'' a' n' ->
    a'' = a ++ a' ->
    n'' = n + n' ->
    valid_execution_fragment_len' s s'' (a ++ a') (n + n').
Proof.
  intros; subst; eauto using valid_execution_fragment_len'_join.
Qed.

Lemma valid_execution_fragment_reach_len' : forall s s' n n' acts,
  valid_execution_fragment_len' s s' acts n' ->
  reachable_len' s n ->
  reachable_len' s' (n + n').
Proof.
  intros.
  generalize dependent n.
  induction H; intros.
  - subst.
    rewrite Nat.add_0_r. assumption.
  - rewrite <-Nat.add_succ_comm.
    eapply IHvalid_execution_fragment_len'; eauto.
    unfold reachable_len' in H1.
    unfold reachable_len'.
    destruct H1 as [init [acts' [Hnew Hvalid]]].
    exists init.
    exists (acts' ++ []). 
    intuition.
    replace (S n0) with (n0 + 1).
    eapply valid_execution_fragment_len'_join' with (a:=acts') (n:=n0); eauto.
    lia.
  - rewrite <-Nat.add_succ_comm.
    eapply IHvalid_execution_fragment_len'; eauto.
    unfold reachable_len' in H1.
    unfold reachable_len'.
    destruct H1 as [init [acts' [Hnew Hvalid]]].
    exists init.
    exists (acts' ++ []). 
    intuition.
    replace (S n0) with (n0 + 1).
    eapply valid_execution_fragment_len'_join' with (a:=acts') (n:=n0); eauto.
    lia.
  - rewrite <-Nat.add_succ_comm.
    eapply IHvalid_execution_fragment_len'; eauto.
    unfold reachable_len' in H1.
    unfold reachable_len'.
    destruct H1 as [init [acts' [Hnew Hvalid]]].
    exists init.
    eexists.
    intuition.
    replace (S n0) with (n0 + 1).
    eapply valid_execution_fragment_len'_join' with (a:=acts') (n:=n0); eauto.
    eapply Step_At_External_len'; eauto.
    lia.
  - rewrite <-Nat.add_succ_comm.
    eapply IHvalid_execution_fragment_len'; eauto.
    unfold reachable_len' in H1.
    unfold reachable_len'.
    destruct H1 as [init [acts' [Hnew Hvalid]]].
    exists init.
    eexists.
    intuition.
    replace (S n0) with (n0 + 1).
    eapply valid_execution_fragment_len'_join' with (a:=acts') (n:=n0); eauto.
    eapply Step_After_External_len'; eauto.
    lia.
  - rewrite <-Nat.add_succ_comm.
    eapply IHvalid_execution_fragment_len'; eauto.
    unfold reachable_len' in H1.
    unfold reachable_len'.
    destruct H1 as [init [acts' [Hnew Hvalid]]].
    exists init.
    eexists.
    intuition.
    replace (S n0) with (n0 + 1).
    eapply valid_execution_fragment_len'_join' with (a:=acts') (n:=n0); eauto.
    eapply Step_Initial_Call_len'; eauto.
    lia.
  - rewrite <-Nat.add_succ_comm.
    eapply IHvalid_execution_fragment_len'; eauto.
    unfold reachable_len' in H1.
    unfold reachable_len'.
    destruct H1 as [init [acts' [Hnew Hvalid]]].
    exists init.
    eexists.
    intuition.
    replace (S n0) with (n0 + 1).
    eapply valid_execution_fragment_len'_join' with (a:=acts') (n:=n0); eauto.
    eapply Step_Final_Return_len'; eauto.
    lia.
  - rewrite <-Nat.add_succ_comm.
    eapply IHvalid_execution_fragment_len'; eauto.
    unfold reachable_len' in H1.
    unfold reachable_len'.
    destruct H1 as [init [acts' [Hnew Hvalid]]].
    exists init.
    eexists.
    intuition.
    replace (S n0) with (n0 + 1).
    eapply valid_execution_fragment_len'_join' with (a:=acts') (n:=n0); eauto.
    eapply Step_Internal_Query_len'; eauto.
    lia.
  - rewrite <-Nat.add_succ_comm.
    eapply IHvalid_execution_fragment_len'; eauto.
    unfold reachable_len' in H1.
    unfold reachable_len'.
    destruct H1 as [init [acts' [Hnew Hvalid]]].
    exists init.
    eexists.
    intuition.
    replace (S n0) with (n0 + 1).
    eapply valid_execution_fragment_len'_join' with (a:=acts') (n:=n0); eauto.
    eapply Step_Internal_Reply_len'; eauto.
    lia.
Qed.

Lemma valid_execution_fragment_len_inv: forall st st' acts n,
  valid_execution_fragment_len' st st' acts (S n) ->
  exists st'' acts' acts'', valid_execution_fragment_len' st st'' acts' n /\
                valid_execution_fragment_len' st'' st' acts'' 1 /\
                acts = acts' ++ acts''.
Proof.
  intros. remember (S n) as sn.
  generalize dependent n.
  induction H; intuition.
  - inversion Heqsn.
  - inversion Heqsn; subst.
    destruct n0.
    inversion H0; subst.
    exists st. exists [], [].
    intuition.
    eapply Step_Internal_L1_len'; eauto.
    specialize (IHvalid_execution_fragment_len' n0).
    intuition.
    destruct H1 as [s [a1 [a2 [Hvalid1 [Hvalid2 Hacts]]]]].
    exists s.
    exists a1.
    exists a2.
    intuition.
    eapply Step_Internal_L1_len'; eauto.
  - inversion Heqsn; subst.
    destruct n0.
    inversion H0; subst.
    exists st. exists [], [].
    intuition.
    eapply Step_Internal_L2_len'; eauto.
    specialize (IHvalid_execution_fragment_len' n0).
    intuition.
    destruct H1 as [s [a1 [a2 [Hvalid1 [Hvalid2 Hacts]]]]].
    exists s.
    exists a1.
    exists a2.
    intuition.
    eapply Step_Internal_L2_len'; eauto.
  - inversion Heqsn; subst.
    destruct n0.
    inversion H0; subst.
    exists st.
    exists [].
    eexists.
    intuition.
    eapply Step_At_External_len'; eauto.
    specialize (IHvalid_execution_fragment_len' n0).
    intuition.
    destruct H1 as [s [a1 [a2 [Hvalid1 [Hvalid2 Hacts]]]]].
    exists s.
    eexists.
    exists a2.
    intuition.
    eapply Step_At_External_len'; eauto.
    simpl. rewrite Hacts.
    reflexivity.
  - inversion Heqsn; subst.
    destruct n0.
    inversion H0; subst.
    exists st.
    exists [].
    eexists.
    intuition.
    eapply Step_After_External_len'; eauto.
    specialize (IHvalid_execution_fragment_len' n0).
    intuition.
    destruct H1 as [s [a1 [a2 [Hvalid1 [Hvalid2 Hacts]]]]].
    exists s.
    eexists.
    exists a2.
    intuition.
    eapply Step_After_External_len'; eauto.
    simpl. rewrite Hacts.
    reflexivity.
  - inversion Heqsn; subst.
    destruct n0.
    inversion H0; subst.
    exists st.
    exists [].
    eexists.
    intuition.
    eapply Step_Initial_Call_len'; eauto.
    specialize (IHvalid_execution_fragment_len' n0).
    intuition.
    destruct H1 as [s [a1 [a2 [Hvalid1 [Hvalid2 Hacts]]]]].
    exists s.
    eexists.
    exists a2.
    intuition.
    eapply Step_Initial_Call_len'; eauto.
    simpl. rewrite Hacts.
    reflexivity.
  - inversion Heqsn; subst.
    destruct n0.
    inversion H0; subst.
    exists st.
    exists [].
    eexists.
    intuition.
    eapply Step_Final_Return_len'; eauto.
    specialize (IHvalid_execution_fragment_len' n0).
    intuition.
    destruct H1 as [s [a1 [a2 [Hvalid1 [Hvalid2 Hacts]]]]].
    exists s.
    eexists.
    exists a2.
    intuition.
    eapply Step_Final_Return_len'; eauto.
    simpl. rewrite Hacts.
    reflexivity.
  - inversion Heqsn; subst.
    destruct n0.
    inversion H0; subst.
    exists st.
    exists [].
    eexists.
    intuition.
    eapply Step_Internal_Query_len'; eauto.
    specialize (IHvalid_execution_fragment_len' n0).
    intuition.
    destruct H1 as [s [a1 [a2 [Hvalid1 [Hvalid2 Hacts]]]]].
    exists s.
    eexists.
    exists a2.
    intuition.
    eapply Step_Internal_Query_len'; eauto.
    simpl. rewrite Hacts.
    reflexivity.
  - inversion Heqsn; subst.
    destruct n0.
    inversion H0; subst.
    exists st.
    exists [].
    eexists.
    intuition.
    eapply Step_Internal_Reply_len'; eauto.
    specialize (IHvalid_execution_fragment_len' n0).
    intuition.
    destruct H1 as [s [a1 [a2 [Hvalid1 [Hvalid2 Hacts]]]]].
    exists s.
    eexists.
    exists a2.
    intuition.
    eapply Step_Internal_Reply_len'; eauto.
    simpl. rewrite Hacts.
    reflexivity.
Qed.

Lemma reachable_len_reconstruct : forall s n,
  reachable_len' s (S n) ->
  exists st acts, 
    reachable_len' st n /\
    valid_execution_fragment_len' st s acts 1.
Proof.
  intros.
  unfold reachable_len' in H.
    destruct H as [init [acts [Hnew Hvalid]]].
    apply valid_execution_fragment_len_inv in Hvalid.
    destruct Hvalid as [st [a1 [a2 [Hvalid1 [Hvalid2 Hacts]]]]].
    exists st. exists a2. intuition.
    unfold reachable_len'.
    exists init. exists a1. intuition.
Qed.

Lemma valid_execution_fragment_len'_to_valid_execution_fragment : forall st st' acts n,
  valid_execution_fragment_len' st st' acts n ->
  composed_lts.valid_execution_fragment L st st' acts.
Proof.
  induction 1; intros.
  subst. eapply composed_lts.Step_None; eauto.
  all : eapply composed_lts.valid_execution_fragment_join' with (a':=acts); eauto.
    eapply composed_lts.Step_Internal_L1; eauto.
    eapply composed_lts.Step_None; eauto.
    simpl. reflexivity.
    eapply composed_lts.Step_Internal_L2; eauto.
    eapply composed_lts.Step_None; eauto.
    simpl. reflexivity.
    eapply composed_lts.Step_At_External; eauto.
    eapply composed_lts.Step_None; eauto.
    simpl. reflexivity.
    eapply composed_lts.Step_After_External; eauto.
    eapply composed_lts.Step_None; eauto.
    simpl. reflexivity.
    eapply composed_lts.Step_Initial_Call; eauto.
    eapply composed_lts.Step_None; eauto.
    simpl. reflexivity.
    eapply composed_lts.Step_Final_Return; eauto.
    eapply composed_lts.Step_None; eauto.
    simpl. reflexivity.
    eapply composed_lts.Step_Internal_Query; eauto.
    eapply composed_lts.Step_None; eauto.
    simpl. reflexivity.
    eapply composed_lts.Step_Internal_Reply; eauto.
    eapply composed_lts.Step_None; eauto.
    simpl. reflexivity.
Qed.

Lemma reachable_len_to_reachable : forall s n,
  reachable_len' s n ->
  composed_lts.reachable L s.
Proof.
  intros.
  unfold reachable_len' in H.
  destruct H as [init [acts [Hnew Hvalid]]].
  unfold composed_lts.reachable.
  exists init, acts. intuition.
  eapply valid_execution_fragment_len'_to_valid_execution_fragment; eauto.
Qed.

Lemma reachable_len'_to_invariant: forall P,
  (forall s n,
    reachable_len' s n ->
    P s) ->
  composed_lts.invariant L P.
Proof.
  intros.
  unfold composed_lts.invariant. intros.
  unfold composed_lts.reachable in H0.
  destruct H0 as [init [acts [Hnew Hvalid]]].
  apply valid_execution_fragment_to_valid_execution_fragment_len' in Hvalid; auto.
  destruct Hvalid as [n Hvalid'].
  unfold reachable_len' in H.
  eapply H; eauto.
Qed.

End KInduction.

Section new_execution.

Context {liA liB liC: language_interface}.
Variable L : composed_lts.composed_lts liA liB liC.
  
Inductive new_valid_execution_fragment (st st' : L.(composed_lts.state)) : list (@composed_lts.event liA liB liC) -> Prop :=
| New_Step_None :
    st = st' ->
    new_valid_execution_fragment st st' nil
| New_Step_Internal_L1 : forall st'' acts (int : L.(composed_lts.internal_L1)) pid,
    composed_lts.step_L1 L st'' pid int st' ->
    new_valid_execution_fragment st st'' acts ->
    new_valid_execution_fragment st st' acts
| New_Step_Internal_L2 : forall st'' acts (int : L.(composed_lts.internal_L2)) pid,
    composed_lts.step_L2 L st'' pid int st' ->
    new_valid_execution_fragment st st'' acts ->
    new_valid_execution_fragment st st' acts
| New_Step_At_External : forall st'' acts qa pid,
    composed_lts.at_external L st'' pid qa st' ->
    new_valid_execution_fragment st st'' acts ->
    new_valid_execution_fragment st st' (acts ++ [(pid, composed_lts.event_invA qa)])
| New_Step_After_External : forall st'' acts ra pid,
    composed_lts.after_external L st'' pid ra st' ->
    new_valid_execution_fragment st st'' acts ->
    new_valid_execution_fragment st st' (acts ++ [(pid, composed_lts.event_resA ra)])
| New_Step_Initial_Call : forall st'' acts qc pid,
    composed_lts.initial_state L st'' pid qc st' ->
    new_valid_execution_fragment st st'' acts ->
    new_valid_execution_fragment st st' (acts ++  [(pid, composed_lts.event_invC qc)])
| New_Step_Final_Return : forall st'' acts rc pid,
    composed_lts.final_state L st'' pid rc st' ->
    new_valid_execution_fragment st st'' acts ->
    new_valid_execution_fragment st st' (acts ++ [(pid, composed_lts.event_resC rc)])
| New_Step_Internal_Query : forall st'' acts qb pid,
    composed_lts.internal_query L st'' pid qb st' ->
    new_valid_execution_fragment st st'' acts ->
    new_valid_execution_fragment st st' (acts ++ [(pid, composed_lts.event_invB qb)])
| New_Step_Internal_Reply : forall st'' acts rb pid,
    composed_lts.internal_reply L st'' pid rb st' ->
    new_valid_execution_fragment st st'' acts ->
    new_valid_execution_fragment st st' (acts ++ [(pid, composed_lts.event_resB rb)])
.

Hint Constructors new_valid_execution_fragment : core.

Lemma new_valid_execution_fragment_join : forall (s s' s'' : L.(composed_lts.state)) a a',
    new_valid_execution_fragment s s' a ->
    new_valid_execution_fragment s' s'' a' ->
    new_valid_execution_fragment s s'' (a ++ a').
Proof.
  intros.
  induction H0; subst; intros; eauto.
  rewrite app_nil_r; auto.
  all : try rewrite app_assoc.
    eapply New_Step_At_External; eauto.
    eapply New_Step_After_External; eauto.
    eapply New_Step_Initial_Call; eauto.
    eapply New_Step_Final_Return; eauto.
    eapply New_Step_Internal_Query; eauto.
    eapply New_Step_Internal_Reply; eauto.
Qed.

Lemma new_valid_execution_fragment_join' : forall (s s' s'' : L.(composed_lts.state)) a a' a'',
    new_valid_execution_fragment s s' a ->
    new_valid_execution_fragment s' s'' a' ->
    a'' = a ++ a' ->
    new_valid_execution_fragment s s'' (a ++ a').
Proof.
  intros; subst; eauto using new_valid_execution_fragment_join.
Qed.

Lemma valid_execution_fragment_to_new_valid_execution_fragment: forall s s' acts,
  composed_lts.valid_execution_fragment L s s' acts ->
  new_valid_execution_fragment s s' acts.
Proof.
  induction 1; intros.
  - subst.
    apply New_Step_None; auto.
  - eapply new_valid_execution_fragment_join' with (a:=[]) in IHvalid_execution_fragment; eauto.
  - eapply new_valid_execution_fragment_join' with (a:=[]) in IHvalid_execution_fragment; eauto.
  - eapply new_valid_execution_fragment_join' with (a:=[(pid, composed_lts.event_invA qa)]) in IHvalid_execution_fragment; eauto.
    eapply New_Step_At_External in H; eauto.
    simpl in H; auto.
  - eapply new_valid_execution_fragment_join' with (a:=[(pid, composed_lts.event_resA ra)]) in IHvalid_execution_fragment; eauto.
    eapply New_Step_After_External in H; eauto.
    simpl in H; auto.
  - eapply new_valid_execution_fragment_join' with (a:=[(pid, composed_lts.event_invC qc)]) in IHvalid_execution_fragment; eauto.
    eapply New_Step_Initial_Call in H; eauto.
    simpl in H; auto.
  - eapply new_valid_execution_fragment_join' with (a:=[(pid, composed_lts.event_resC rc)]) in IHvalid_execution_fragment; eauto.
    eapply New_Step_Final_Return in H; eauto.
    simpl in H; auto.
  - eapply new_valid_execution_fragment_join' with (a:=[(pid, composed_lts.event_invB qb)]) in IHvalid_execution_fragment; eauto.
    eapply New_Step_Internal_Query in H; eauto.
    simpl in H; auto.
  - eapply new_valid_execution_fragment_join' with (a:=[(pid, composed_lts.event_resB rb)]) in IHvalid_execution_fragment; eauto.
    eapply New_Step_Internal_Reply in H; eauto.
    simpl in H; auto.
Qed.

Lemma new_valid_execution_fragment_to_valid_execution_fragment: forall s s' acts,
  new_valid_execution_fragment s s' acts ->
  composed_lts.valid_execution_fragment L s s' acts.
Proof.
  induction 1; intros.
  - subst.
    eapply composed_lts.Step_None; eauto.
  - eapply composed_lts.valid_execution_fragment_join'
    with (a':=[]) in IHnew_valid_execution_fragment; eauto.
    eapply composed_lts.Step_Internal_L1; eauto.
    eapply composed_lts.Step_None; eauto.
    rewrite app_nil_r; auto.
  - eapply composed_lts.valid_execution_fragment_join'
    with (a':=[]) in IHnew_valid_execution_fragment; eauto.
    eapply composed_lts.Step_Internal_L2; eauto.
    eapply composed_lts.Step_None; eauto.
    rewrite app_nil_r; auto.
  - eapply composed_lts.valid_execution_fragment_join'
    with (a':=[(pid, composed_lts.event_invA qa)]) in IHnew_valid_execution_fragment; eauto.
    eapply composed_lts.Step_At_External; eauto.
    eapply composed_lts.Step_None; eauto.
  - eapply composed_lts.valid_execution_fragment_join'
    with (a':=[(pid, composed_lts.event_resA ra)]) in IHnew_valid_execution_fragment; eauto.
    eapply composed_lts.Step_After_External; eauto.
    eapply composed_lts.Step_None; eauto.
  - eapply composed_lts.valid_execution_fragment_join'
    with (a':=[(pid, composed_lts.event_invC qc)]) in IHnew_valid_execution_fragment; eauto.
    eapply composed_lts.Step_Initial_Call; eauto.
    eapply composed_lts.Step_None; eauto.
  - eapply composed_lts.valid_execution_fragment_join'
    with (a':=[(pid, composed_lts.event_resC rc)]) in IHnew_valid_execution_fragment; eauto.
    eapply composed_lts.Step_Final_Return; eauto.
    eapply composed_lts.Step_None; eauto.
  - eapply composed_lts.valid_execution_fragment_join'
    with (a':=[(pid, composed_lts.event_invB qb)]) in IHnew_valid_execution_fragment; eauto.
    eapply composed_lts.Step_Internal_Query; eauto.
    eapply composed_lts.Step_None; eauto.
  - eapply composed_lts.valid_execution_fragment_join'
    with (a':=[(pid, composed_lts.event_resB rb)]) in IHnew_valid_execution_fragment; eauto.
    eapply composed_lts.Step_Internal_Reply; eauto.
    eapply composed_lts.Step_None; eauto.
Qed.

End new_execution.
