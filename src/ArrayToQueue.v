Require Import
  Lia
  List
  Arith
  Array
  ArrayQueueMapping.
Import ListNotations.

Section test.

Variable L : nat.
Hypothesis H : L > 0.

Theorem array_to_queue_obligation : forall (f r : nat), f < r -> r - S f < r - f.
Proof.
  intros * ha.
  abstract nia.
Qed.

Fixpoint array_to_queue_rec (f r : nat) (vec : Vector.t entry L)
  (acc : Acc lt (r - f)) : list (option nat) := 
  match lt_dec f r with 
    | left pf => (array_to_queue_rec (S f) r vec (Acc_inv acc (array_to_queue_obligation _ _ pf))) ++ 
          [fst (Vector.nth vec (Fin.of_nat_lt (@mod_lt L H f)))]
    | right _ => nil 
  end.

Definition array_to_queue (f r : nat) (vec : Vector.t entry L) := 
  match lt_dec f r with 
    | left pf => (array_to_queue_rec f r vec (lt_wf (r - f))) 
    | right _ => nil 
  end.

Lemma rec_irr : forall r f vec (acc acc' : Acc lt (r - f)),
    array_to_queue_rec f r vec acc = array_to_queue_rec f r vec acc'.
Proof.
  fix ihn 4.
  intros *.
  destruct acc, acc'.
  cbn. destruct (lt_dec f r).
  f_equal.
  eapply ihn.
  exact eq_refl.
Qed.

Theorem array_to_queue_rec_length_aux : forall x (vec : Vector.t entry L) 
  f r acc, x = r - f -> length (array_to_queue_rec f r vec acc) = x.
Proof.
  intro x.
  induction (Wf_nat.lt_wf x) as [x _ ihn].
  intros * ha.
  specialize (ihn (r - S f)).  subst.
  destruct (lt_dec f r) as [ha | ha].
  + 
    specialize (ihn ltac:(nia) vec (S f) r).
    assert (hb : Acc lt (r - S f)).
    constructor.  intros. 
    inversion acc as [hacc]. 
    apply hacc. nia.
    specialize (ihn hb eq_refl).
    destruct acc; cbn. 
    destruct (lt_dec f r) as [hc | hc]; try nia.
    cbn. rewrite app_length. cbn.
    rewrite rec_irr with (acc' := hb).
    rewrite ihn. nia.
  +
    destruct acc; cbn.
    destruct (lt_dec f r); try nia.
    cbn. nia.
Qed.

Theorem array_to_queue_length : forall (vec : Vector.t entry L) f r,
  length (array_to_queue f r vec) = r - f.
Proof.
  intros *. unfold array_to_queue. 
  destruct (lt_dec f r) as [ha | ha].
  + 
    eapply array_to_queue_rec_length_aux. 
    reflexivity.
  + 
    cbn; nia. 
Qed.

Theorem array_queue_equal_nil_aux : forall x (vec : Vector.t entry L) 
  f acc, x = f - f -> (array_to_queue_rec f f vec acc) = [].
Proof.
  intro x.
  induction (Wf_nat.lt_wf x) as [x _ ihn].
  intros * ha.
  specialize (ihn (f - S f)). subst.
  destruct (lt_dec f f) as [ha | ha].
  + lia.
  +
    destruct acc; cbn.
    destruct (lt_dec f f); try nia.
    reflexivity.
Qed.

Lemma array_queue_equal_nil: forall f vec,
  array_to_queue f f vec = [].
Proof.
  intros. unfold array_to_queue. 
  destruct (lt_dec f f) as [ha | ha].
  + 
    eapply array_queue_equal_nil_aux with (x:=0).
    lia.
  + 
    reflexivity.
Qed.

Lemma array_to_queue_S_f: forall f r vec,
  f < r ->
  array_to_queue f r vec = 
  array_to_queue (S f) r vec ++
    [fst (Vector.nth vec (Fin.of_nat_lt (@mod_lt L H f)))].
Proof.
  intros f r vec Hlt.
  unfold array_to_queue at 1.
  simpl.
  destruct (lt_dec f r) as [Hl | Hr]; [| contradiction].
  rewrite rec_irr with (acc' := lt_wf (r - S f)).
  f_equal.
  unfold array_to_queue.
  destruct (lt_dec (S f) r) as [Hlt' | Heq].
  - 
    reflexivity.
  - assert (S f = r) by lia.
    subst.
    rewrite array_queue_equal_nil_aux with (x:=0).
    auto.
    lia.
Qed.

Lemma array_to_queue_S_f_aux: forall f r vec acc acc',
  f < r ->
  array_to_queue_rec f r vec acc =
  array_to_queue_rec (S f) r vec acc' ++
  [fst (Vector.nth vec (Fin.of_nat_lt (mod_lt H f)))].
Proof.
  intros.
  generalize array_to_queue_S_f; intro.
  unfold array_to_queue in H1.
  specialize (H1 f r vec).
  specialize (H1 ltac:(lia)).
  destruct (lt_dec f r).
  - destruct (lt_dec (S f) r).
    -- erewrite rec_irr in H1.
      rewrite H1.
      erewrite rec_irr with (f:=(S f)).
      eauto.
    -- assert (S f = r) by lia.
      subst.
      rewrite array_queue_equal_nil_aux with (x:=0).
      simpl.
      erewrite rec_irr; eauto.
      lia.
  - lia.
Qed.

Theorem array_to_queue_S_r_aux : forall x (vec : Vector.t entry L) 
  f r acc acc', x = r - f -> f < r ->
    (array_to_queue_rec f (S r) vec acc) = 
    fst (Vector.nth vec (Fin.of_nat_lt (mod_lt H r))) ::
    (array_to_queue_rec f r vec acc').
Proof.
  intro x.
  induction (Wf_nat.lt_wf x) as [x _ ihn].
  intros * ha Hlt.
  specialize (ihn (r - S f)). subst.
    specialize (ihn ltac:(nia) vec (S f) r).
    assert (hb : Acc lt (r - S f)).
    constructor.  intros. 
    inversion acc as [hacc]. 
    apply hacc. nia.
    assert (hb' : Acc lt (S r - S f)).
    constructor.  intros. 
    inversion acc as [hacc]. 
    apply hacc. nia.
    specialize (ihn hb' hb eq_refl).
    destruct (lt_dec (S f) r).
    - intuition.
      erewrite array_to_queue_S_f_aux.
      rewrite H0. simpl.
      f_equal.
      erewrite array_to_queue_S_f_aux with (f:=f).
      eauto. auto.
      lia.
    - assert (S f = r) by lia.
      subst.
      destruct acc. simpl.
      destruct (lt_dec f (S (S f))).
      --
       erewrite array_to_queue_S_f_aux.
        rewrite array_queue_equal_nil_aux with (x:=0).
        simpl.
        destruct acc'. simpl.
        destruct (lt_dec f (S f)).
        --- rewrite array_queue_equal_nil_aux with (x:=0).
          simpl. reflexivity. lia.
        --- lia.
        --- lia.
        --- lia.
      -- lia.
      Unshelve.
      constructor.
      intros. lia.
Qed.

Lemma array_to_queue_S_r: forall f r vec,
  f <= r ->
  array_to_queue f (S r) vec =
    (fst (Vector.nth vec (Fin.of_nat_lt (@mod_lt L H r)))) ::
    (array_to_queue f r vec).
Proof.
  intros. unfold array_to_queue.
  destruct (lt_dec f r) as [ha | ha].
  + 
    destruct (lt_dec f (S r)) as [hb | hb].
    ++ eapply array_to_queue_S_r_aux; eauto.
    ++ lia.
  + assert (f = r) by lia.
    subst.
    destruct (lt_dec r (S r)).
    ++ erewrite array_to_queue_S_f_aux.
      rewrite array_queue_equal_nil_aux with (x:=0).
      simpl. auto. lia. lia.
    ++ lia.
    Unshelve.
    constructor.
    intros. lia.
Qed.

Fixpoint all_some (l : list (option nat)) :=
  match l with
  | nil => True
  | h :: l' =>
    match h with
    | None => False
    | Some _ => all_some l'
    end
  end.

Fixpoint all_none (l : list (option nat)) :=
  match l with
  | nil => True
  | h :: l' =>
    match h with
    | None => all_none l'
    | Some _ => False
    end
  end.

Lemma all_some_dist: forall l l',
  all_some l ->
  all_some l' ->
  all_some (l ++ l').
Proof.
  induction l; intros.
  - simpl. auto.
  - simpl. destruct a.
    simpl in H0.
    apply IHl; auto.
    inversion H0.
Qed.

Lemma all_some_S_r: forall f r vec,
  f <= r ->
  all_some (array_to_queue f r vec) ->
    fst (Vector.nth vec (Fin.of_nat_lt (@mod_lt L H r))) <> None ->
  all_some (array_to_queue f (S r) vec).
Proof.
  intros.
  rewrite array_to_queue_S_r; auto.
  assert (Htmp : forall A (a : A) l, a :: l = [a] ++ l)
  by reflexivity.
  rewrite Htmp.
  apply all_some_dist; auto.
  simpl.
  destruct (fst (Vector.nth vec (Fin.of_nat_lt (mod_lt H r)))); intuition.
Qed.

Lemma nat_reconstruct: forall n,
  exists k b, n = b + k * L /\ b < L.
Proof.
  induction n.
  - exists O. exists O. split.
    reflexivity. lia.
  - destruct IHn as [h [m [Hhm Hneq]]].
    subst.
    destruct L. lia.
    destruct (m =? n)eqn: Heq.
    -- exists (S h). exists O. split.
      + apply Nat.eqb_eq in Heq. subst.
        lia.
      + lia.
    -- exists h. exists (S m). split.
      + lia.
      + unfold "<" in Hneq.
        inversion Hneq.
        ++ subst. apply Nat.eqb_neq in Heq.
          intuition.
        ++ lia.
Qed.

Lemma mod_neq_in_range: forall i r, i < r -> r < i + L -> i mod L <> r mod L.
Proof.
  intros i r H1 H2 Heq.
  assert (0 < r - i) by nia.
  assert (r - i < L) by nia.
  assert ( (r - i) mod L = r - i ) by (apply Nat.mod_small; assumption).
  assert ( (i - i) mod L = i - i ).
  apply Nat.mod_small. lia.
  generalize nat_reconstruct; intro.
  specialize (H6 i).
  destruct H6 as [k1 [b1 [Heq1 Hlt1]]].
  generalize nat_reconstruct; intro.
  specialize (H6 r).
  destruct H6 as [k2 [b2 [Heq2 Hlt2]]].
  subst.
  rewrite Nat.Div0.mod_add in Heq.
  rewrite Nat.Div0.mod_add in Heq.
  rewrite Nat.mod_small in Heq; auto.
  rewrite Nat.mod_small in Heq; auto.
  subst.
  assert (Htmp : 0 < k2 * L - k1 * L) by lia.
  destruct (eq_nat_dec k1 k2).
  - subst. lia.
  - assert (Htmp' : (b2 + k2 * L - (b2 + k1 * L)) = k2 * L - k1 * L) by lia.
    rewrite Htmp' in H4.
    assert ((k2 * L - k1 * L) = (k2 - k1) * L) by nia.
    rewrite H6 in H4.
    assert (k1 <= k2) by lia.
    inversion H7; subst.
    intuition.
    assert ((S m - k1) * L >= L) by nia.
    nia.
Qed.

Theorem array_to_queue_replace_r_aux : forall x (vec : Vector.t entry L) 
  f r acc new, x = r - f ->
  f <= r ->
  r < f + L ->
  (array_to_queue_rec f r vec acc) =
  (array_to_queue_rec f r (Vector.replace vec ((Fin.of_nat_lt (@mod_lt L H r))) new) acc).
Proof.
  intro x.
  induction (Wf_nat.lt_wf x) as [x _ ihn].
  intros * ha Hlt Hlt'.
  specialize (ihn (r - S f)).  subst.
  destruct (lt_dec f r) as [ha | ha].
  + 
    specialize (ihn ltac:(nia) vec (S f) r).
    assert (hb : Acc lt (r - S f)).
    constructor.  intros. 
    inversion acc as [hacc]. 
    apply hacc. nia.
    specialize (ihn hb new eq_refl).
    destruct acc; cbn.
    destruct (lt_dec f r) as [hc | hc]; try nia.
    cbn.
    rewrite rec_irr with (acc' := hb).
    rewrite ihn. f_equal.
    erewrite rec_irr. eauto.
    rewrite Vector.nth_replace_neq. auto.
    intro.
    assert (Htmp : f mod L <> r mod L).
    apply mod_neq_in_range; auto.
    assert (Fin.to_nat (Fin.of_nat_lt (mod_lt H f)) = 
      Fin.to_nat (Fin.of_nat_lt (mod_lt H r))
    ).
    rewrite H0. reflexivity.
    rewrite Fin.to_nat_of_nat in H1.
    rewrite Fin.to_nat_of_nat in H1.
    inversion H1; subst. intuition.
    lia.
    lia.
  + assert (Htmp : f = r) by lia.
    subst.
    rewrite array_queue_equal_nil_aux with (x:=0).
    rewrite array_queue_equal_nil_aux with (x:=0).
    reflexivity.
    lia.
    lia.
Qed.

Lemma array_to_queue_replace_r: forall f r vec new,
  f <= r ->
  r < f + L ->
  array_to_queue f r vec = 
  array_to_queue f r (Vector.replace vec ((Fin.of_nat_lt (@mod_lt L H r))) new).
Proof.
  intros. unfold array_to_queue.
  destruct (lt_dec f r).
  - erewrite array_to_queue_replace_r_aux; eauto.
  - reflexivity. 
Qed.

Lemma array_to_queue_gt: forall f r vec,
  f > r -> array_to_queue f r vec = [].
Proof.
  intros.
  unfold array_to_queue.
  destruct (lt_dec f r).
  - lia.
  - reflexivity.
Qed.

Lemma all_none_dist: forall l l',
  all_none l ->
  all_none l' ->
  all_none (l ++ l').
Proof.
  induction l; intros.
  - simpl. auto.
  - simpl. destruct a.
    inversion H0.
    simpl in H0.
    apply IHl; auto.
Qed.

Lemma all_none_dist_inv: forall l l',
  all_none (l ++ l') ->
  all_none l /\
  all_none l'.
Proof.
  induction l; simpl; intros.
  - simpl. auto.
  - simpl. destruct a. intuition.
    apply IHl in H0; intuition.
Qed.

Lemma array_to_queue_replace_f: forall f r vec new,
  f <= r ->
  r <= f + L ->
  array_to_queue (S f) r vec = 
  array_to_queue (S f) r (Vector.replace vec ((Fin.of_nat_lt (@mod_lt L H f))) new).
Proof.
  intros.
  induction H0.
  rewrite array_to_queue_gt; simpl; try lia.
  rewrite array_to_queue_gt; simpl; try lia.
  auto.
  destruct (eq_nat_dec f m).
  subst.
  rewrite array_queue_equal_nil; simpl; try lia.
  rewrite array_queue_equal_nil; simpl; try lia.
  auto.
  rewrite array_to_queue_S_r; try nia.
  rewrite array_to_queue_S_r with (r:=m); try nia.
  specialize (IHle ltac:(nia)).
  rewrite <-IHle.
  f_equal.
  rewrite Vector.nth_replace_neq. auto.
  intro.
    assert (Htmp : Fin.to_nat (Fin.of_nat_lt (mod_lt H m)) = 
      Fin.to_nat (Fin.of_nat_lt (mod_lt H f))
    ).
  rewrite H2. reflexivity.
  rewrite Fin.to_nat_of_nat in Htmp.
  rewrite Fin.to_nat_of_nat in Htmp.
  inversion Htmp; subst.
  assert (Htt : f < m) by lia.
  eapply mod_neq_in_range.
  apply Htt. lia.
  auto.
Qed.

Lemma all_some_dist_inv: forall l l',
  all_some (l ++ l') ->
  all_some l /\
  all_some l'.
Proof.
  induction l; simpl; intros.
  - simpl. auto.
  - simpl. destruct a.
    apply IHl in H0; intuition.
    intuition.
Qed.

Lemma all_none_S_r: forall f r vec,
  f <= r ->
  all_none (array_to_queue f r vec) ->
    fst (Vector.nth vec (Fin.of_nat_lt (@mod_lt L H r))) = None ->
  all_none (array_to_queue f (S r) vec).
Proof.
  intros.
  rewrite array_to_queue_S_r; auto.
  assert (Htmp : forall A (a : A) l, a :: l = [a] ++ l)
  by reflexivity.
  rewrite Htmp.
  apply all_none_dist; auto.
  simpl.
  destruct (fst (Vector.nth vec (Fin.of_nat_lt (mod_lt H r)))); intuition.
  discriminate.
Qed.

End test.