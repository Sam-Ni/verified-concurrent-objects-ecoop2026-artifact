Require Import
  List
  LTS
  Arith
  LibVar
  LibEnv
  Refinement
  Register
  RegisterCounterImpl
  Counter
  RegisterCounter
  VeriTactics.
Import ListNotations.

Section Mapping.

Fixpoint gather_requests (pc : LibEnv.env RCounter_pc)
  (res : env Register_reply) : LibEnv.env Counter_query :=
  match pc with
  | nil => nil
  | ins :: pc' => 
      let requests' := gather_requests pc' res in
      let (pid, inst) := ins in
        (match inst with
        | RInc1 => (pid, CntInc)::requests'
        | RInc2 => (pid, CntInc)::requests'
        | RInc3 _ => (pid, CntInc)::requests'
        | RInc4 => (pid, CntInc)::requests'
        | RInc5 => match get pid res with
                  | None => (pid, CntInc)::requests'
                  | Some res => match res with
                                | RegCASOk b => if b then requests' else (pid, CntInc)::requests'
                                | RegReadOk _ => (pid, CntInc)::requests'
                                end
                  end
        | RInc6 ret => match ret with
                      | true => requests'
                      | false => (pid, CntInc)::requests'
                      end
        | RInc7 => requests'
        | RRead1 => (pid, CntRead)::requests'
        | RRead2 => match get pid res with
                    | None => (pid, CntRead)::requests'
                    | Some res => match res with
                                  | RegCASOk _ => (pid, CntRead)::requests'
                                  | RegReadOk _ => requests'
                                  end
                    end
        | RRead3 _ => requests'
        end)
  end.

Fixpoint gather_responses (pc : LibEnv.env RCounter_pc)
  (res : env Register_reply) : LibEnv.env Counter_reply :=
  match pc with
  | nil => nil
  | ins :: pc' => 
      let responses' := gather_responses pc' res in
      let (pid, inst) := ins in
        (match inst with
        | RInc1 => responses' 
        | RInc2 => responses' 
        | RInc3 _ => responses' 
        | RInc4 => responses'
        | RInc5 => match get pid res with
                  | None => responses'
                  | Some res => match res with
                                | RegCASOk b => if b then (pid, CntIncOk)::responses' else responses'
                                | RegReadOk _ => responses'
                                end
                  end
        | RInc6 ret => match ret with
                      | true => (pid, CntIncOk)::responses'
                      | false => responses'
                      end
        | RInc7 => (pid, CntIncOk)::responses'
        | RRead1 => responses' 
        | RRead2 => match get pid res with
                  | None => responses'
                  | Some res => match res with
                                | RegCASOk _ => responses'
                                | RegReadOk ret => (pid, CntReadOk ret)::responses'
                                end
                  end
        | RRead3 ret => (pid, CntReadOk ret)::responses'
        end)
  end.

Lemma gather_requests_preserves_pid_notin: forall pc pid res,
  pid # pc ->
  pid # gather_requests pc res.
Proof.
  induction pc; intros.
  - apply notin_empty.
  - destruct a. simpl.
    simpl. simpl in H.
    apply notin_union in H. intuition.
    eapply IHpc in H1.
    destruct r; simpl; try apply notin_union; eauto.
      -- destruct (get v res).
        ++ destruct r.
          +++ destruct success; simpl; intuition.
            apply notin_union; auto.
          +++ simpl. apply notin_union; auto.
        ++ simpl. apply notin_union; auto.
    -- destruct ret; eauto. simpl. apply notin_union; eauto.
      -- destruct (get v res).
        ++ destruct r.
          +++ destruct success; simpl; intuition.
            apply notin_union; auto.
            apply notin_union; auto.
          +++ assumption.
        ++ simpl. apply notin_union; auto.
Qed.

Lemma gather_responses_preserves_pid_notin: forall pc pid res,
  pid # pc ->
  pid # gather_responses pc res.
Proof.
  induction pc; intros.
  - apply notin_empty.
  - destruct a. simpl.
    simpl. simpl in H.
    apply notin_union in H. intuition.
    eapply IHpc in H1.
    destruct r; simpl; try apply notin_union; eauto.
      -- destruct (get v res).
        ++ destruct r.
          +++ destruct success; simpl; intuition.
            apply notin_union; auto.
          +++ assumption.
        ++ assumption.
    -- destruct ret; eauto. simpl. apply notin_union; eauto.
      -- destruct (get v res).
        ++ destruct r.
          +++ destruct success; simpl; intuition.
          +++ apply notin_union; auto.
        ++ assumption.
Qed.

Lemma gather_requests_dist: forall pc pc' res,
  gather_requests (pc ++ pc') res =
  gather_requests pc res ++ gather_requests pc' res.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - destruct a.
    destruct r; simpl; rewrite IHpc; try reflexivity.
      -- destruct (get v res); simpl.
        ++ destruct r; simpl.
          +++ destruct success; simpl; intuition.
          +++ reflexivity.
        ++ reflexivity.
    -- destruct ret; reflexivity.
      -- destruct (get v res); simpl.
        ++ destruct r; simpl.
          +++ destruct success; simpl; intuition.
          +++ reflexivity.
        ++ reflexivity.
Qed.

Lemma gather_responses_dist: forall pc pc' res,
  gather_responses (pc ++ pc') res =
  gather_responses pc res ++ gather_responses pc' res.
Proof.
  induction pc; simpl; intros.
  - reflexivity.
  - destruct a.
    destruct r; simpl; rewrite IHpc; try reflexivity.
      -- destruct (get v res); simpl.
        ++ destruct r; simpl.
          +++ destruct success; simpl; intuition.
          +++ reflexivity.
        ++ reflexivity.
    -- destruct ret; reflexivity.
      -- destruct (get v res); simpl.
        ++ destruct r; simpl.
          +++ destruct success; simpl; intuition.
          +++ reflexivity.
        ++ reflexivity.
Qed.

Lemma gather_requests_notin_res: forall pc pid res pid_res,
  pid # pc ->
  gather_requests pc ((pid, pid_res) :: res) =
  gather_requests pc res.
Proof.
  induction pc using env_ind; simpl; intros.
  - reflexivity.
  - apply notin_union in H. intuition.
    destruct v; simpl;
    try (f_equal; eapply IHpc; eauto);
    try (eapply IHpc; eauto).
    -- apply notin_neq in H0. 
      assert (Hneq: x =? pid = false).
      apply Nat.eqb_neq; intuition .
      rewrite Hneq.
      --- destruct (get x res); simpl; try (f_equal; eapply IHpc; eauto).
        destruct r; try (f_equal; eapply IHpc; eauto).
        destruct success.
          +++ eapply IHpc; eauto.
          +++ f_equal; eapply IHpc; eauto.
    -- destruct ret; simpl; try (f_equal; eapply IHpc; eauto).
      eapply IHpc; eauto.
    -- apply notin_neq in H0.
      assert (Hneq: x =? pid = false).
      apply Nat.eqb_neq; intuition .
      rewrite Hneq.
      --- destruct (get x res); simpl; try (f_equal; eapply IHpc; eauto).
        destruct r; try (f_equal; eapply IHpc; eauto).
        eapply IHpc; eauto.
Qed.

Lemma gather_responses_notin_res: forall pc pid res pid_res,
  pid # pc ->
  gather_responses pc ((pid, pid_res) :: res) =
  gather_responses pc res.
Proof.
  induction pc using env_ind; simpl; intros.
  - reflexivity.
  - apply notin_union in H. intuition.
    destruct v; simpl;
    try (f_equal; eapply IHpc; eauto);
    try (eapply IHpc; eauto).
    -- apply notin_neq in H0.
      assert (Hneq: x =? pid = false).
      apply Nat.eqb_neq; intuition .
      rewrite Hneq.
      --- destruct (get x res); simpl; try (f_equal; eapply IHpc; eauto).
        destruct r; try (f_equal; eapply IHpc; eauto).
        destruct success; simpl; try (f_equal; eapply IHpc; eauto); try (eapply IHpc; eauto).
          +++ eapply IHpc; eauto.
          +++ eapply IHpc; eauto.
    -- destruct ret; simpl; try (f_equal; eapply IHpc; eauto).
      eapply IHpc; eauto.
    -- apply notin_neq in H0.
      assert (Hneq: x =? pid = false).
      apply Nat.eqb_neq; intuition .
      rewrite Hneq.
      --- destruct (get x res); simpl; try (f_equal; eapply IHpc; eauto).
        destruct r; try (f_equal; eapply IHpc; eauto).
        destruct success; simpl; try (f_equal; eapply IHpc; eauto); try (eapply IHpc; eauto).
        eapply IHpc; eauto.
Qed.

Lemma gather_requests_preserves_ok: forall pc res,
  ok pc ->
  ok (gather_requests pc res).
Proof.
  induction pc using env_ind; simpl; intros.
  - constructor.
  - inversion H; subst. destruct v; simpl.
    all : try (econstructor; eauto).
    all : try (eapply gather_requests_preserves_pid_notin; eauto).
    --
      destruct (get x res).
      destruct r; simpl. destruct success; simpl.
      eauto.
      all : econstructor; eauto; eapply gather_requests_preserves_pid_notin; eauto.
    -- destruct ret; simpl.
      eauto.
      econstructor; eauto. eapply gather_requests_preserves_pid_notin; eauto.
    -- eauto.
    --
      destruct (get x res).
      destruct r; simpl. destruct success; simpl.
      eauto.
      econstructor; eauto. eapply gather_requests_preserves_pid_notin; eauto.
      econstructor; eauto. eapply gather_requests_preserves_pid_notin; eauto.
      eapply IHpc; eauto.
      econstructor; eauto. eapply gather_requests_preserves_pid_notin; eauto.
    -- eauto.
Qed.

Lemma gather_responses_preserves_ok: forall pc res,
  ok pc ->
  ok (gather_responses pc res).
Proof.
  induction pc using env_ind; simpl; intros.
  - constructor.
  - inversion H; subst. destruct v; simpl.
    all : try (econstructor; eauto).
    all : try (eapply gather_responses_preserves_pid_notin; eauto).
    all : eauto.
    --
      destruct (get x res).
      destruct r; simpl. destruct success; simpl.
      econstructor; eauto. eapply gather_responses_preserves_pid_notin; eauto.
      eauto.
      eauto.
      eauto.
    -- destruct ret; simpl.
      econstructor; eauto. eapply gather_responses_preserves_pid_notin; eauto.
      eauto.
    --
      destruct (get x res).
      destruct r; simpl. destruct success; simpl.
      eapply IHpc; eauto.
      eapply IHpc; eauto.
      econstructor; eauto. eapply gather_responses_preserves_pid_notin; eauto.
      eapply IHpc; eauto.
Qed.

Lemma gather_responses_binds_RInc7: forall pc pid res,
  binds pid RInc7 pc ->
  binds pid CntIncOk
    (gather_responses pc res).
Proof.
  induction pc; intros.
  - inversion H.
  - unfold binds in *.
    destruct a.
    simpl in *.
    destruct (pid =? v)eqn:Heq.
    -- inversion H; subst.
      simpl. rewrite Heq. reflexivity.
    -- match_if_apply IHpc.
      all : simpl; rewrite Heq; rewrite IHpc; auto.
Qed.

Lemma gather_requests_binds_RInc7_remove: forall pc pid res,
  binds pid RInc7 pc ->
  gather_requests (remove pc pid) res =
  gather_requests pc res.
Proof.
  induction pc; intros.
  - inversion H.
  - unfold binds in *.
    destruct a.
    simpl in *.
    destruct (pid =? v)eqn:Heq.
    -- inversion H; subst.
      simpl.
      reflexivity.
    -- simpl.
      destruct r; simpl; try rewrite Heq; match_if_apply IHpc;
      try f_equal; auto.
Qed.

Lemma gather_responses_remove_comm: forall pc pid res,
  ok pc ->
  gather_responses (remove pc pid) res =
  remove (gather_responses pc res) pid.
Proof.
  induction 1; simpl; intros.
  - reflexivity.
  - destruct (pid =? x)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst.
      rewrite notin_remove in IHok; auto.
      destruct T;
      match_if_apply IHok.
      all : simpl;
      rewrite Nat.eqb_refl; reflexivity.
    -- simpl.
      destruct T; match_if_apply IHok.
      all : simpl; rewrite Heq; f_equal; auto.
Qed.

Lemma gather_responses_binds_RRead3: forall pc pid res ret,
  binds pid (RRead3 ret) pc ->
  binds pid (CntReadOk ret)
    (gather_responses pc res).
Proof.
  induction pc; intros.
  - inversion H.
  - unfold binds in *.
    destruct a.
    simpl in *.
    destruct (pid =? v)eqn:Heq.
    -- inversion H; subst.
      simpl. rewrite Heq. reflexivity.
    -- match_if_apply IHpc.
      all : simpl; rewrite Heq; erewrite IHpc; eauto.
Qed.

Lemma gather_requests_binds_RRead3_remove: forall pc pid res ret,
  binds pid (RRead3 ret) pc ->
  gather_requests (remove pc pid) res =
  gather_requests pc res.
Proof.
  induction pc; intros.
  - inversion H.
  - unfold binds in *.
    destruct a.
    simpl in *.
    destruct (pid =? v)eqn:Heq.
    -- inversion H; subst.
      simpl.
      reflexivity.
    -- simpl.
      apply IHpc with (res:=res) in H; auto.
      rewrite H.
      destruct r; simpl; try reflexivity.
Qed.

Lemma gather_requests_binds_RInc3_substitute: forall pc pid res ret,
  binds pid (RInc3 ret) pc ->
  gather_requests (substitute pc pid RInc4) res =
  gather_requests pc res.
Proof.
  induction pc; intros.
  - inversion H.
  - unfold binds in *.
    destruct a.
    simpl in *.
    destruct (pid =? v)eqn:Heq.
    -- inversion H; subst.
      simpl.
      reflexivity.
    -- simpl.
      apply IHpc with (res:=res) in H; auto.
      rewrite H.
      destruct r; simpl; try reflexivity.
Qed.

Lemma gather_responses_binds_RInc3_substitute: forall pc pid res ret,
  binds pid (RInc3 ret) pc ->
  gather_responses (substitute pc pid RInc4) res =
  gather_responses pc res.
Proof.
  induction pc; intros.
  - inversion H.
  - unfold binds in *.
    destruct a.
    simpl in *.
    destruct (pid =? v)eqn:Heq.
    -- inversion H; subst.
      simpl.
      reflexivity.
    -- simpl.
      apply IHpc with (res:=res) in H; auto.
      rewrite H.
      destruct r; simpl; try reflexivity.
Qed.

Lemma gather_requests_binds_RInc6_substitute: forall pc pid res,
  binds pid (RInc6 true) pc ->
  gather_requests (substitute pc pid RInc7) res =
  gather_requests pc res.
Proof.
  induction pc; intros.
  - inversion H.
  - unfold binds in *.
    destruct a.
    simpl in *.
    destruct (pid =? v)eqn:Heq.
    -- inversion H; subst.
      simpl.
      reflexivity.
    -- simpl.
      apply IHpc with (res:=res) in H; auto.
      rewrite H.
      destruct r; simpl; try reflexivity.
Qed.

Lemma gather_responses_binds_RInc6_substitute: forall pc pid res,
  binds pid (RInc6 true) pc ->
  gather_responses (substitute pc pid RInc7) res =
  gather_responses pc res.
Proof.
  induction pc; intros.
  - inversion H.
  - unfold binds in *.
    destruct a.
    simpl in *.
    destruct (pid =? v)eqn:Heq.
    -- inversion H; subst.
      simpl.
      reflexivity.
    -- simpl.
      apply IHpc with (res:=res) in H; auto.
      rewrite H.
      destruct r; simpl; try reflexivity.
Qed.

Lemma gather_requests_binds_RInc6_substitute': forall pc pid res,
  binds pid (RInc6 false) pc ->
  gather_requests (substitute pc pid RInc1) res =
  gather_requests pc res.
Proof.
  induction pc; intros.
  - inversion H.
  - unfold binds in *.
    destruct a.
    simpl in *.
    destruct (pid =? v)eqn:Heq.
    -- inversion H; subst.
      simpl.
      reflexivity.
    -- simpl.
      apply IHpc with (res:=res) in H; auto.
      rewrite H.
      destruct r; simpl; try reflexivity.
Qed.

Lemma gather_responses_binds_RInc6_substitute': forall pc pid res,
  binds pid (RInc6 false) pc ->
  gather_responses (substitute pc pid RInc1) res =
  gather_responses pc res.
Proof.
  induction pc; intros.
  - inversion H.
  - unfold binds in *.
    destruct a.
    simpl in *.
    destruct (pid =? v)eqn:Heq.
    -- inversion H; subst.
      simpl.
      reflexivity.
    -- simpl.
      apply IHpc with (res:=res) in H; auto.
      rewrite H.
      destruct r; simpl; try reflexivity.
Qed.

Lemma gather_requests_binds_RInc5_binds_CntInc: forall pc pid res,
  binds pid RInc5 pc ->
  pid # res ->
  binds pid CntInc 
    (gather_requests pc res).
Proof.
  induction pc; intros.
  - inversion H.
  - unfold binds in *.
    destruct a.
    simpl in *.
    destruct (pid =? v)eqn:Heq.
    -- inversion H; subst.
      apply Nat.eqb_eq in Heq.
      subst.
      apply notin_get_none in H0.
      rewrite H0.
      apply binds_push_eq; auto.
    -- simpl.
      apply IHpc with (res:=res) in H; auto.
      destruct r; simpl; try rewrite Heq;
      try rewrite H; match_if'; try assumption.
      discriminate. discriminate.
Qed.

Lemma gather_requests_binds_RRead2_binds_CntRead: forall pc pid res,
  binds pid RRead2 pc ->
  pid # res ->
  binds pid CntRead 
    (gather_requests pc res).
Proof.
  induction pc; intros.
  - inversion H.
  - unfold binds in *.
    destruct a.
    simpl in *.
    destruct (pid =? v)eqn:Heq.
    -- inversion H; subst.
      apply Nat.eqb_eq in Heq.
      subst.
      apply notin_get_none in H0.
      rewrite H0.
      apply binds_push_eq; auto.
    -- simpl.
      apply IHpc with (res:=res) in H; auto.
      destruct r; simpl; try rewrite Heq;
      try rewrite H; match_if'; try assumption.
      discriminate. discriminate.
      discriminate. discriminate.
Qed.

Lemma gather_responses_binds_RInc5_notin: forall pc pid res,
  ok pc ->
  binds pid RInc5 pc ->
  pid # res ->
  pid # (gather_responses pc res).
Proof.
  induction 1; intros.
  - inversion H.
  - unfold binds in *.
    simpl in *.
    destruct (pid =? x)eqn:Heq.
    -- inversion H1; subst.
      apply Nat.eqb_eq in Heq.
      subst.
      apply notin_get_none in H2.
      rewrite H2.
      apply gather_responses_preserves_pid_notin; auto.
    -- simpl.
      apply IHok in H1; auto.
      destruct T; simpl; try rewrite Heq;
      apply Nat.eqb_neq in Heq;
      try rewrite H; match_if'; try assumption;
      try apply notin_dom_push_get;
      try apply notin_union; intuition; auto;
      try apply notin_neq; intuition.
Qed.

Lemma gather_responses_binds_RRead2_notin: forall pc pid res,
  ok pc ->
  binds pid RRead2 pc ->
  pid # res ->
  pid # (gather_responses pc res).
Proof.
  induction 1; intros.
  - inversion H.
  - unfold binds in *.
    simpl in *.
    destruct (pid =? x)eqn:Heq.
    -- inversion H1; subst.
      apply Nat.eqb_eq in Heq.
      subst.
      apply notin_get_none in H2.
      rewrite H2.
      apply gather_responses_preserves_pid_notin; auto.
    -- simpl.
      apply IHok in H1; auto.
      destruct T; simpl; try rewrite Heq;
      apply Nat.eqb_neq in Heq;
      try rewrite H; match_if'; try assumption;
      try apply notin_dom_push_get;
      try apply notin_union; intuition; auto;
      try apply notin_neq; intuition.
Qed.

Lemma gather_requests_cas_false: forall pc pid res,
  pid # res ->
  gather_requests pc ((pid, RegCASOk false) :: res) =
  gather_requests pc res.
Proof.
  induction pc; intros.
  - simpl. reflexivity.
  - destruct a.
    simpl in *.
    destruct (v =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst.
      destruct r.
      all : try rewrite IHpc; auto.
      apply notin_get_none in H.
      rewrite H.
      reflexivity.
      apply notin_get_none in H.
      rewrite H.
      reflexivity.
    -- destruct r.
      all : try rewrite IHpc; auto.
Qed.

Lemma gather_responses_cas_false: forall pc pid res,
  pid # res ->
  gather_responses pc ((pid, RegCASOk false) :: res) =
  gather_responses pc res.
Proof.
  induction pc; intros.
  - simpl. reflexivity.
  - destruct a.
    simpl in *.
    destruct (v =? pid)eqn:Heq.
    -- apply Nat.eqb_eq in Heq.
      subst.
      destruct r.
      all : try rewrite IHpc; auto.
      apply notin_get_none in H.
      rewrite H.
      reflexivity.
      apply notin_get_none in H.
      rewrite H.
      reflexivity.
    -- destruct r.
      all : try rewrite IHpc; auto.
Qed.

Lemma gather_requests_read_ok: forall pc pid res ret,
  binds pid RInc2 pc ->
  ok pc ->
  gather_requests pc ((pid, RegReadOk ret) :: res) =
  gather_requests pc res.
Proof.
  intros.
  apply binds_reconstruct in H.
  destruct H as [l1 [l2 Hlist]].
  rewrite Hlist.
  rewrite Hlist in H0.
  rewrite gather_requests_dist.
  rewrite gather_requests_notin_res; auto.
  rewrite gather_requests_dist.
  simpl.
  rewrite gather_requests_notin_res; auto.
  rewrite gather_requests_dist.
  simpl. reflexivity.
  apply ok_middle_inv in H0; intuition.
  apply ok_middle_inv in H0; intuition.
Qed.

Lemma gather_responses_read_ok: forall pc pid res ret,
  binds pid RInc2 pc ->
  ok pc ->
  gather_responses pc ((pid, RegReadOk ret) :: res) =
  gather_responses pc res.
Proof.
  intros.
  apply binds_reconstruct in H.
  destruct H as [l1 [l2 Hlist]].
  rewrite Hlist.
  rewrite Hlist in H0.
  rewrite gather_responses_dist.
  rewrite gather_responses_notin_res; auto.
  rewrite gather_responses_dist.
  simpl.
  rewrite gather_responses_notin_res; auto.
  rewrite gather_responses_dist.
  simpl. reflexivity.
  apply ok_middle_inv in H0; intuition.
  apply ok_middle_inv in H0; intuition.
Qed.

Lemma gather_requests_RInc1_substitute: forall pc pid res,
  binds pid RInc1 pc ->
  ok pc ->
  gather_requests (substitute pc pid RInc2) res =
  gather_requests pc res.
Proof.
  intros.
  apply binds_reconstruct in H.
  destruct H as [l1 [l2 Hlist]].
  rewrite Hlist.
  rewrite Hlist in H0.
  rewrite substitute_notin_app.
  rewrite gather_requests_dist.
  rewrite gather_requests_dist.
  simpl.
  rewrite Nat.eqb_refl.
  simpl. reflexivity.
  apply ok_middle_inv in H0; intuition.
Qed.

Lemma gather_requests_RInc4_substitute: forall pc pid res,
  binds pid RInc4 pc ->
  ok pc ->
  pid # res ->
  gather_requests (substitute pc pid RInc5) res =
  gather_requests pc res.
Proof.
  intros.
  apply binds_reconstruct in H.
  destruct H as [l1 [l2 Hlist]].
  rewrite Hlist.
  rewrite Hlist in H0.
  rewrite substitute_notin_app.
  rewrite gather_requests_dist.
  rewrite gather_requests_dist.
  simpl.
  rewrite Nat.eqb_refl.
  simpl.
  apply notin_get_none in H1.
  rewrite H1. reflexivity.
  apply ok_middle_inv in H0; intuition.
Qed.

Lemma gather_requests_RRead1_substitute: forall pc pid res,
  binds pid RRead1 pc ->
  ok pc ->
  pid # res ->
  gather_requests (substitute pc pid RRead2) res =
  gather_requests pc res.
Proof.
  intros.
  apply binds_reconstruct in H.
  destruct H as [l1 [l2 Hlist]].
  rewrite Hlist.
  rewrite Hlist in H0.
  rewrite substitute_notin_app.
  rewrite gather_requests_dist.
  rewrite gather_requests_dist.
  simpl.
  rewrite Nat.eqb_refl.
  simpl.
  apply notin_get_none in H1.
  rewrite H1. reflexivity.
  apply ok_middle_inv in H0; intuition.
Qed.

Lemma gather_responses_RInc1_substitute: forall pc pid res,
  binds pid RInc1 pc ->
  ok pc ->
  gather_responses (substitute pc pid RInc2) res =
  gather_responses pc res.
Proof.
  intros.
  apply binds_reconstruct in H.
  destruct H as [l1 [l2 Hlist]].
  rewrite Hlist.
  rewrite Hlist in H0.
  rewrite substitute_notin_app.
  rewrite gather_responses_dist.
  rewrite gather_responses_dist.
  simpl.
  rewrite Nat.eqb_refl.
  simpl. reflexivity.
  apply ok_middle_inv in H0; intuition.
Qed.

Lemma gather_responses_RInc4_substitute: forall pc pid res,
  binds pid RInc4 pc ->
  ok pc ->
  pid # res ->
  gather_responses (substitute pc pid RInc5) res =
  gather_responses pc res.
Proof.
  intros.
  apply binds_reconstruct in H.
  destruct H as [l1 [l2 Hlist]].
  rewrite Hlist.
  rewrite Hlist in H0.
  rewrite substitute_notin_app.
  rewrite gather_responses_dist.
  rewrite gather_responses_dist.
  simpl.
  rewrite Nat.eqb_refl.
  simpl.
  apply notin_get_none in H1.
  rewrite H1. reflexivity.
  apply ok_middle_inv in H0; intuition.
Qed.

Lemma gather_responses_RRead1_substitute: forall pc pid res,
  binds pid RRead1 pc ->
  ok pc ->
  pid # res ->
  gather_responses (substitute pc pid RRead2) res =
  gather_responses pc res.
Proof.
  intros.
  apply binds_reconstruct in H.
  destruct H as [l1 [l2 Hlist]].
  rewrite Hlist.
  rewrite Hlist in H0.
  rewrite substitute_notin_app.
  rewrite gather_responses_dist.
  rewrite gather_responses_dist.
  simpl.
  rewrite Nat.eqb_refl.
  simpl.
  apply notin_get_none in H1.
  rewrite H1. reflexivity.
  apply ok_middle_inv in H0; intuition.
Qed.

Lemma gather_requests_notin_env': forall pc pid res,
  pid # pc ->
  gather_requests pc (remove res pid) =
  gather_requests pc res.
Proof.
  induction pc using env_ind; simpl; intros.
  - reflexivity.
  - apply notin_union in H. intuition.
    apply notin_neq in H0.
    destruct v; simpl;
    try (f_equal; eapply IHpc; eauto);
    try (eapply IHpc; eauto).
    match_if'; subst.
    rewrite IHpc; auto.
    all : try
    eapply remove_neq_preserves_binds in Heqo0; eauto.
    all : try unfold binds in Heqo0.
    all : try rewrite Heqo in Heqo0.
    all : try discriminate.
    all : try f_equal.
    all : try (rewrite IHpc; auto).
    apply remove_preserves_binds_notin in Heqo.
    unfold binds in Heqo.
    rewrite Heqo in Heqo0. discriminate.
    intuition.
    match_if'; subst.
    all : try
    eapply remove_neq_preserves_binds in Heqo0; eauto.
    all : try unfold binds in Heqo0.
    all : try rewrite Heqo in Heqo0.
    all : try discriminate.
    apply remove_preserves_binds_notin in Heqo.
    unfold binds in Heqo.
    rewrite Heqo in Heqo0. discriminate.
    intuition.
Qed.

Lemma gather_requests_RInc5_substitute_remove: forall pc pid res,
  binds pid RInc5 pc ->
  ok pc ->
  binds pid (RegCASOk true) res ->
  gather_requests (substitute pc pid (RInc6 true)) (remove res pid) =
  gather_requests pc res.
Proof.
  intros.
  apply binds_reconstruct in H.
  destruct H as [l1 [l2 Hlist]].
  rewrite Hlist.
  rewrite Hlist in H0.
  rewrite substitute_notin_app.
  rewrite gather_requests_dist.
  rewrite gather_requests_dist.
  simpl.
  rewrite Nat.eqb_refl.
  unfold binds in H1.
  rewrite H1.
  simpl.
  rewrite gather_requests_notin_env'.
  rewrite gather_requests_notin_env'.
  reflexivity.
  apply ok_middle_inv in H0; intuition.
  apply ok_middle_inv in H0; intuition.
  apply ok_middle_inv in H0; intuition.
Qed.

Lemma gather_responses_notin_env': forall pc pid res,
  pid # pc ->
  gather_responses pc (remove res pid) =
  gather_responses pc res.
Proof.
  induction pc using env_ind; simpl; intros.
  - reflexivity.
  - apply notin_union in H. intuition.
    apply notin_neq in H0.
    destruct v; simpl;
    try (f_equal; eapply IHpc; eauto);
    try (eapply IHpc; eauto).
    match_if'; subst.
    rewrite IHpc; auto.
    all : try
    eapply remove_neq_preserves_binds in Heqo0; eauto.
    all : try unfold binds in Heqo0.
    all : try rewrite Heqo in Heqo0.
    all : try discriminate.
    all : try f_equal.
    all : try (rewrite IHpc; auto).
    apply remove_preserves_binds_notin in Heqo.
    unfold binds in Heqo.
    rewrite Heqo in Heqo0. discriminate.
    intuition.
    match_if'; subst.
    all : try
    eapply remove_neq_preserves_binds in Heqo0; eauto.
    all : try unfold binds in Heqo0.
    all : try rewrite Heqo in Heqo0.
    all : try discriminate.
    all : try f_equal.
    inversion Heqo0; subst.
    reflexivity.
    apply remove_preserves_binds_notin in Heqo.
    unfold binds in Heqo.
    rewrite Heqo in Heqo0. discriminate.
    intuition.
Qed.

Lemma gather_responses_RInc5_substitute_remove: forall pc pid res,
  binds pid RInc5 pc ->
  ok pc ->
  binds pid (RegCASOk true) res ->
  gather_responses (substitute pc pid (RInc6 true)) (remove res pid) =
  gather_responses pc res.
Proof.
  intros.
  apply binds_reconstruct in H.
  destruct H as [l1 [l2 Hlist]].
  rewrite Hlist.
  rewrite Hlist in H0.
  rewrite substitute_notin_app.
  rewrite gather_responses_dist.
  rewrite gather_responses_dist.
  simpl.
  rewrite Nat.eqb_refl.
  unfold binds in H1.
  rewrite H1.
  simpl.
  rewrite gather_responses_notin_env'.
  rewrite gather_responses_notin_env'.
  reflexivity.
  apply ok_middle_inv in H0; intuition.
  apply ok_middle_inv in H0; intuition.
  apply ok_middle_inv in H0; intuition.
Qed.

Lemma gather_requests_RInc5_substitute_remove': forall pc pid res,
  binds pid RInc5 pc ->
  ok pc ->
  binds pid (RegCASOk false) res ->
  gather_requests (substitute pc pid (RInc6 false)) (remove res pid) =
  gather_requests pc res.
Proof.
  intros.
  apply binds_reconstruct in H.
  destruct H as [l1 [l2 Hlist]].
  rewrite Hlist.
  rewrite Hlist in H0.
  rewrite substitute_notin_app.
  rewrite gather_requests_dist.
  rewrite gather_requests_dist.
  simpl.
  rewrite Nat.eqb_refl.
  unfold binds in H1.
  rewrite H1.
  simpl.
  rewrite gather_requests_notin_env'.
  rewrite gather_requests_notin_env'.
  reflexivity.
  apply ok_middle_inv in H0; intuition.
  apply ok_middle_inv in H0; intuition.
  apply ok_middle_inv in H0; intuition.
Qed.

Lemma gather_responses_RInc5_substitute_remove': forall pc pid res,
  binds pid RInc5 pc ->
  ok pc ->
  binds pid (RegCASOk false) res ->
  gather_responses (substitute pc pid (RInc6 false)) (remove res pid) =
  gather_responses pc res.
Proof.
  intros.
  apply binds_reconstruct in H.
  destruct H as [l1 [l2 Hlist]].
  rewrite Hlist.
  rewrite Hlist in H0.
  rewrite substitute_notin_app.
  rewrite gather_responses_dist.
  rewrite gather_responses_dist.
  simpl.
  rewrite Nat.eqb_refl.
  unfold binds in H1.
  rewrite H1.
  simpl.
  rewrite gather_responses_notin_env'.
  rewrite gather_responses_notin_env'.
  reflexivity.
  apply ok_middle_inv in H0; intuition.
  apply ok_middle_inv in H0; intuition.
  apply ok_middle_inv in H0; intuition.
Qed.

Lemma gather_requests_RInc2_substitute_remove: forall pc pid res ret,
  binds pid RInc2 pc ->
  ok pc ->
  binds pid (RegReadOk ret) res ->
  gather_requests (substitute pc pid (RInc3 ret)) (remove res pid) =
  gather_requests pc res.
Proof.
  intros.
  apply binds_reconstruct in H.
  destruct H as [l1 [l2 Hlist]].
  rewrite Hlist.
  rewrite Hlist in H0.
  rewrite substitute_notin_app.
  rewrite gather_requests_dist.
  rewrite gather_requests_dist.
  simpl.
  rewrite Nat.eqb_refl.
  unfold binds in H1.
  simpl.
  rewrite gather_requests_notin_env'.
  rewrite gather_requests_notin_env'.
  reflexivity.
  apply ok_middle_inv in H0; intuition.
  apply ok_middle_inv in H0; intuition.
  apply ok_middle_inv in H0; intuition.
Qed.

Lemma gather_responses_RInc2_substitute_remove: forall pc pid res ret,
  binds pid RInc2 pc ->
  ok pc ->
  binds pid (RegReadOk ret) res ->
  gather_responses (substitute pc pid (RInc3 ret)) (remove res pid) =
  gather_responses pc res.
Proof.
  intros.
  apply binds_reconstruct in H.
  destruct H as [l1 [l2 Hlist]].
  rewrite Hlist.
  rewrite Hlist in H0.
  rewrite substitute_notin_app.
  rewrite gather_responses_dist.
  rewrite gather_responses_dist.
  simpl.
  rewrite Nat.eqb_refl.
  unfold binds in H1.
  simpl.
  rewrite gather_responses_notin_env'.
  rewrite gather_responses_notin_env'.
  reflexivity.
  apply ok_middle_inv in H0; intuition.
  apply ok_middle_inv in H0; intuition.
  apply ok_middle_inv in H0; intuition.
Qed.

Lemma gather_requests_RRead2_substitute_remove: forall pc pid res ret,
  binds pid RRead2 pc ->
  ok pc ->
  binds pid (RegReadOk ret) res ->
  gather_requests (substitute pc pid (RRead3 ret)) (remove res pid) =
  gather_requests pc res.
Proof.
  intros.
  apply binds_reconstruct in H.
  destruct H as [l1 [l2 Hlist]].
  rewrite Hlist.
  rewrite Hlist in H0.
  rewrite substitute_notin_app.
  rewrite gather_requests_dist.
  rewrite gather_requests_dist.
  simpl.
  rewrite Nat.eqb_refl.
  unfold binds in H1.
  rewrite H1.
  simpl.
  rewrite gather_requests_notin_env'.
  rewrite gather_requests_notin_env'.
  reflexivity.
  apply ok_middle_inv in H0; intuition.
  apply ok_middle_inv in H0; intuition.
  apply ok_middle_inv in H0; intuition.
Qed.

Lemma gather_responses_RRead2_substitute_remove: forall pc pid res ret,
  binds pid RRead2 pc ->
  ok pc ->
  binds pid (RegReadOk ret) res ->
  gather_responses (substitute pc pid (RRead3 ret)) (remove res pid) =
  gather_responses pc res.
Proof.
  intros.
  apply binds_reconstruct in H.
  destruct H as [l1 [l2 Hlist]].
  rewrite Hlist.
  rewrite Hlist in H0.
  rewrite substitute_notin_app.
  rewrite gather_responses_dist.
  rewrite gather_responses_dist.
  simpl.
  rewrite Nat.eqb_refl.
  unfold binds in H1.
  rewrite H1.
  simpl.
  rewrite gather_responses_notin_env'.
  rewrite gather_responses_notin_env'.
  reflexivity.
  apply ok_middle_inv in H0; intuition.
  apply ok_middle_inv in H0; intuition.
  apply ok_middle_inv in H0; intuition.
Qed.

End Mapping.