Require Import
  Arith
  NDiv0
  Lia.

Section tick_nat.

Definition time : Type := nat * nat.

Definition nat_to_time n : time :=
  (n / 60 mod 12, n mod 60).

Definition tick (t : time) :=
  let (h, m) := t in
  if m =? 59 then
    if h =? 11 then (O, O)
    else (S h, O)
  else (h, S m).

Lemma nat_reconstruct: forall n,
  exists h m, n = h * 60 + m /\ m < 60.
Proof.
  induction n.
  - exists O. exists O. split.
    reflexivity. lia.
  - destruct IHn as [h [m [Hhm Hneq]]].
    subst.
    destruct (m =? 59)eqn: Heq.
    -- exists (S h). exists O. split.
      + apply Nat.eqb_eq in Heq. subst.
        lia.
      + lia.
    -- exists h. exists (S m). split.
      + lia.
      + unfold "<" in Hneq.
        inversion Hneq.
        ++ subst. simpl in Heq. discriminate.
        ++ lia.
Qed.

Lemma suc_comm: forall m n,
  S (m + n) = m + (S n).
Proof.
  intros. lia.
Qed.

Lemma nat_to_time_S_tick: forall v,
  nat_to_time (S v) = tick (nat_to_time v).
Proof.
  intros v.
  unfold nat_to_time, tick.
  generalize nat_reconstruct; intro.
  specialize (H v).
  destruct H as [h [m [Hhm Hneq]]].
  subst.
  destruct (m =? 59) eqn:Hcase.
  - apply Nat.eqb_eq in Hcase; subst m.
    destruct (h mod 12 =? 11) eqn:Hhmod.
    + apply Nat.eqb_eq in Hhmod.
      replace (S (h * 60 + 59)) with (h * 60 + 60) by lia.
      rewrite Nat.div_add_l by auto.
      rewrite Nat.div_add_l by auto.
      rewrite Nat.add_comm with (n:=h * 60).
      rewrite Nat.Div0.mod_add by auto.
      rewrite Nat.div_small with (a:=59) by lia.
      rewrite Nat.add_0_r.
      rewrite Hhmod. rewrite Nat.eqb_refl.
      rewrite Nat.div_same by lia.
      rewrite Nat.Div0.mod_same.
      rewrite Nat.add_comm with (m:=59).
      rewrite Nat.Div0.mod_add.
      assert (59 mod 60 =? 59 = true).
      simpl. reflexivity.
      rewrite H.
      assert (h + 1 = (12 * (h / 12) + (h mod 12) + 1)).
      rewrite Nat.add_comm.
      rewrite Nat.add_comm with (m:=1).
      f_equal. apply Nat.div_mod. lia.
      rewrite H0.
      rewrite Hhmod. f_equal.
      rewrite <-Nat.add_assoc.
      rewrite Nat.mul_comm.
      replace (11 + 1) with (12) by lia.
      rewrite Nat.add_comm.
      rewrite Nat.Div0.mod_add.
      apply Nat.Div0.mod_same.
    + apply Nat.eqb_neq in Hhmod.
      replace (S (h * 60 + 59)) with (h * 60 + 60) by lia.
      rewrite Nat.div_add_l by auto.
      rewrite Nat.div_add_l by auto.
      rewrite Nat.add_comm with (n:=h * 60).
      rewrite Nat.Div0.mod_add by auto.
      rewrite Nat.div_small with (a:=59) by lia.
      rewrite Nat.add_0_r.
      rewrite Nat.div_same by lia.
      rewrite Nat.Div0.mod_same.
      rewrite Nat.add_comm with (m:=59).
      rewrite Nat.Div0.mod_add.
      assert (59 mod 60 =? 59 = true).
      simpl. reflexivity.
      rewrite H.
      assert (h mod 12 =? 11 = false).
      apply Nat.eqb_neq in Hhmod. assumption.
      rewrite H0.
      f_equal.
      assert (h mod 12 < 11).
      assert (h mod 12 < 12).
      apply Nat.mod_upper_bound. lia.
      lia.
      rewrite Nat.Div0.add_mod.
      rewrite Nat.mod_small.
      assert (1 mod 12 = 1). simpl. reflexivity.
      rewrite H2.
      rewrite Nat.add_comm. reflexivity.
      assert (1 mod 12 = 1). simpl. reflexivity.
      rewrite H2. lia.
  - apply Nat.eqb_neq in Hcase.
    replace (S (h * 60 + m)) with (h * 60 + S m) by lia.
    rewrite Nat.div_add_l by auto.
    rewrite Nat.div_add_l by auto.
      rewrite Nat.add_comm with (n:=h * 60).
      rewrite Nat.Div0.mod_add by auto.
      rewrite Nat.add_comm with (n:=h * 60).
      rewrite Nat.Div0.mod_add by auto.
      rewrite Nat.div_small by lia.
      rewrite Nat.div_small by lia.
      rewrite Nat.mod_small with (a:=m) by lia.
      rewrite Nat.mod_small with (a:=S m) by lia.
      apply Nat.eqb_neq in Hcase. rewrite Hcase.
      reflexivity.
Qed.

End tick_nat.