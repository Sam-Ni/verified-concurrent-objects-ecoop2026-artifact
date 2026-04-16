Require Import
  Arith
  LibVar
  LibEnv
  LTS
  Array
  Invariants.

Section INV.

Variable L : nat.

Definition array_exclusive_wf (s : state (array L)) :=
  forall pid,
    (pid \in dom s.(requests L) ->
    pid # s.(responses L)) /\
    (pid \in dom s.(responses L) ->
    pid # s.(requests L)).

Lemma array_exclusive_wf_inv: invariant_ind (array L) array_exclusive_wf.
Proof.
  unfold invariant_ind. intuition.
  - inversion H; subst.
    unfold new_array.
    unfold array_exclusive_wf.
    simpl.
    intuition.
  - inversion H0; subst; clear H0.
    -- unfold array_exclusive_wf in *;
      simpl in *; intuition.
      --- destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove inv pid)).
        apply ok_remove_notin; auto.
        unfold "#" in H1.
        intuition.
        apply notin_union.
        intuition.
        apply notin_neq; auto.
        apply H.
        eapply remove_neq_preserves_in; eauto.
      --- apply in_union in H0.
        simpl in H0. intuition.
        subst. apply ok_remove_notin; auto.
        apply remove_preserves_notin.
        apply H; auto.
    -- unfold array_exclusive_wf in *;
      simpl in *; intuition.
      --- destruct (eq_nat_dec pid0 pid).
        subst.
        assert (pid # (remove inv pid)).
        apply ok_remove_notin; auto.
        unfold "#" in H1.
        intuition.
        apply notin_union.
        intuition.
        apply notin_neq; auto.
        apply H.
        eapply remove_neq_preserves_in; eauto.
      --- apply in_union in H0.
        simpl in H0. intuition.
        subst. apply ok_remove_notin; auto.
        apply remove_preserves_notin.
        apply H; auto.
  - unfold array_exclusive_wf in *.
    inversion H0; subst; simpl in *; intros.
    -- intuition.
      --- apply in_union in H1.
        simpl in H1.
        intuition.
        subst. auto.
        apply H; auto.
      --- apply notin_union.
        destruct (eq_nat_dec pid0 pid).
        subst. unfold "#" in Hnotin_res.
        intuition.
        intuition.
        apply notin_neq; auto.
        apply H; auto.
    -- intuition.
      --- apply in_union in H1.
        simpl in H1.
        intuition.
        subst. auto.
        apply H; auto.
      --- apply notin_union.
        destruct (eq_nat_dec pid0 pid).
        subst. unfold "#" in Hnotin_res.
        intuition.
        intuition.
        apply notin_neq; auto.
        apply H; auto.
  - destruct act.
  - destruct act.
  - unfold array_exclusive_wf in *.
    inversion H0; subst; simpl in *; intros.
    -- intuition.
      --- destruct (eq_nat_dec pid0 pid).
        subst.
        apply ok_remove_notin; auto.
        apply remove_preserves_notin.
        apply H; auto.
      --- destruct (eq_nat_dec pid0 pid).
        subst. apply H; auto.
        apply binds_in in Hbinds; auto.
        apply remove_neq_preserves_in in H1; auto.
        apply H; auto.
    -- intuition.
      --- destruct (eq_nat_dec pid0 pid).
        subst.
        apply ok_remove_notin; auto.
        apply remove_preserves_notin.
        apply H; auto.
      --- destruct (eq_nat_dec pid0 pid).
        subst. apply H; auto.
        apply binds_in in Hbinds; auto.
        apply remove_neq_preserves_in in H1; auto.
        apply H; auto.
Qed.

Lemma array_exclusive_wf_invariant: invariant (array L) array_exclusive_wf.
Proof.
  apply invariant_ind_to_invariant.
  apply array_exclusive_wf_inv.
Qed.

End INV.