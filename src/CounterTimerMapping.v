Require Import
  List
  LTS
  Arith
  LibVar
  LibEnv
  Refinement
  Counter
  CounterTimerImpl
  Timer
  CounterTimer
  TickNat
  VeriTactics.
Import ListNotations.

Section Mapping.

Fixpoint gather_requests (pc : LibEnv.env CTimer_pc)
  (res : env Counter_reply) : LibEnv.env Timer_query :=
  match pc with
  | nil => nil
  | ins :: pc' => 
      let requests' := gather_requests pc' res in
      let (pid, inst) := ins in
        (match inst with
        | CTick1 => (pid, TmTick)::requests'
        | CTick2 => match get pid res with
                    | None => (pid, TmTick)::requests'
                    | Some res => match res with
                                | CntIncOk => requests'
                                | CntReadOk _ => (pid, TmTick)::requests'
                                end
                    end
        | CTick3 => requests'
        | CRead1 => (pid, TmRead)::requests'
        | CRead2 => match get pid res with
                    | None => (pid, TmRead)::requests'
                    | Some res => match res with
                                | CntIncOk => (pid, TmRead)::requests'
                                | CntReadOk _ => requests'
                                end
                    end
        | CRead3 _ => requests'
        end)
  end.

Fixpoint gather_responses (pc : LibEnv.env CTimer_pc)
  (res : env Counter_reply) : LibEnv.env Timer_reply :=
  match pc with
  | nil => nil
  | ins :: pc' => 
      let responses' := gather_responses pc' res in
      let (pid, inst) := ins in
        (match inst with
        | CTick1 => responses'
        | CTick2 => match get pid res with
                    | None => responses'
                    | Some res => match res with
                                | CntIncOk => (pid, TmTickOk)::responses'
                                | CntReadOk _ => responses'
                                end
                    end
        | CTick3 => (pid, TmTickOk)::responses'
        | CRead1 => responses'
        | CRead2 => match get pid res with
                    | None => responses'
                    | Some res => match res with
                                | CntIncOk => responses'
                                | CntReadOk ret => (pid, TmReadOk (nat_to_time ret))::responses'
                                end
                    end
        | CRead3 ret => (pid, TmReadOk (nat_to_time ret))::responses'
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
    destruct c; simpl; try apply notin_union; eauto.
      -- destruct (get v res).
        ++ destruct c.
          +++ intuition.
          +++ simpl. apply notin_union; auto.
        ++ simpl. apply notin_union; auto.
    -- destruct (get v res).
        ++ destruct c.
          +++ simpl; intuition.
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
    destruct c; simpl; try apply notin_union; eauto.
      -- destruct (get v res).
        ++ destruct c.
          +++ simpl; intuition.
            apply notin_union; auto.
          +++ assumption.
        ++ assumption.
    -- destruct (get v res).
        ++ destruct c.
          +++ simpl; intuition.
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
    destruct c; simpl; rewrite IHpc; try reflexivity.
      -- destruct (get v res); simpl.
        ++ destruct c; simpl.
          +++ simpl; intuition.
          +++ reflexivity.
        ++ reflexivity.
    -- destruct (get v res); simpl.
        ++ destruct c; simpl.
          +++ simpl; intuition.
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
    destruct c; simpl; rewrite IHpc; try reflexivity.
      -- destruct (get v res); simpl.
        ++ destruct c; simpl.
          +++ simpl; intuition.
          +++ reflexivity.
        ++ reflexivity.
    -- destruct (get v res); simpl.
        ++ destruct c; simpl.
          +++ simpl; intuition.
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
        destruct c; try (f_equal; eapply IHpc; eauto).
          +++ eapply IHpc; eauto.
    -- apply notin_neq in H0.
      assert (Hneq: x =? pid = false).
      apply Nat.eqb_neq; intuition .
      rewrite Hneq.
      --- destruct (get x res); simpl; try (f_equal; eapply IHpc; eauto).
        destruct c; try (f_equal; eapply IHpc; eauto).
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
        destruct c; try (f_equal; eapply IHpc; eauto).
          +++ eapply IHpc; eauto.
          +++ eapply IHpc; eauto.
    -- apply notin_neq in H0.
      assert (Hneq: x =? pid = false).
      apply Nat.eqb_neq; intuition .
      rewrite Hneq.
      --- destruct (get x res); simpl; try (f_equal; eapply IHpc; eauto).
        destruct c; try (f_equal; eapply IHpc; eauto).
        simpl; try (f_equal; eapply IHpc; eauto); try (eapply IHpc; eauto).
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
      destruct c; simpl. simpl.
      eauto.
      all : econstructor; eauto; eapply gather_requests_preserves_pid_notin; eauto.
    -- eauto.
    --
      destruct (get x res).
      destruct c; simpl. simpl.
      eauto.
      econstructor; eauto. eapply gather_requests_preserves_pid_notin; eauto.
      eauto.
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
      destruct c; simpl. simpl.
      econstructor; eauto. eapply gather_responses_preserves_pid_notin; eauto.
      eauto.
      eauto.
    --
      destruct (get x res).
      destruct c; simpl. simpl.
      eapply IHpc; eauto.
      econstructor; eauto. eapply gather_responses_preserves_pid_notin; eauto.
      eapply IHpc; eauto.
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

Lemma gather_responses_binds_CTick3: forall pc pid res,
  binds pid CTick3 pc ->
  binds pid TmTickOk
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

Lemma gather_requests_binds_CTick3_remove: forall pc pid res,
  binds pid CTick3 pc ->
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
      destruct c; simpl; try rewrite Heq; match_if_apply IHpc;
      try f_equal; auto.
Qed.

Lemma gather_responses_binds_CRead3: forall pc pid res ret,
  binds pid (CRead3 ret) pc ->
  binds pid (TmReadOk (nat_to_time ret))
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

Lemma gather_requests_binds_CRead3_remove: forall pc pid res ret,
  binds pid (CRead3 ret) pc ->
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
      destruct c; simpl; try reflexivity.
Qed.

Lemma gather_requests_binds_CTick2_binds_TmTick: forall pc pid res,
  binds pid CTick2 pc ->
  pid # res ->
  binds pid TmTick 
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
      destruct c; simpl; try rewrite Heq;
      try rewrite H; match_if'; try assumption.
      discriminate. discriminate.
Qed.

Lemma gather_responses_binds_CTick2_notin: forall pc pid res,
  ok pc ->
  binds pid CTick2 pc ->
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

Lemma gather_requests_binds_CRead2_binds_TmRead: forall pc pid res,
  binds pid CRead2 pc ->
  pid # res ->
  binds pid TmRead 
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
      destruct c; simpl; try rewrite Heq;
      try rewrite H; match_if'; try assumption.
      discriminate. discriminate.
Qed.

Lemma gather_responses_binds_CRead2_notin: forall pc pid res,
  ok pc ->
  binds pid CRead2 pc ->
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

Lemma gather_requests_CTick1_substitute: forall pc pid res,
  binds pid CTick1 pc ->
  ok pc ->
  pid # res ->
  gather_requests (substitute pc pid CTick2) res =
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

Lemma gather_requests_CRead1_substitute: forall pc pid res,
  binds pid CRead1 pc ->
  ok pc ->
  pid # res ->
  gather_requests (substitute pc pid CRead2) res =
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

Lemma gather_responses_CTick1_substitute: forall pc pid res,
  binds pid CTick1 pc ->
  ok pc ->
  pid # res ->
  gather_responses (substitute pc pid CTick2) res =
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

Lemma gather_responses_CRead1_substitute: forall pc pid res,
  binds pid CRead1 pc ->
  ok pc ->
  pid # res ->
  gather_responses (substitute pc pid CRead2) res =
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

Lemma gather_requests_CTick2_substitute_remove: forall pc pid res,
  binds pid CTick2 pc ->
  ok pc ->
  binds pid CntIncOk res ->
  gather_requests (substitute pc pid CTick3) (remove res pid) =
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

Lemma gather_requests_CRead2_substitute_remove: forall pc pid res ret,
  binds pid CRead2 pc ->
  ok pc ->
  binds pid (CntReadOk ret) res ->
  gather_requests (substitute pc pid (CRead3 ret)) (remove res pid) =
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

Lemma gather_responses_CTick2_substitute_remove: forall pc pid res,
  binds pid CTick2 pc ->
  ok pc ->
  binds pid CntIncOk res ->
  gather_responses (substitute pc pid CTick3) (remove res pid) =
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

Lemma gather_responses_CRead2_substitute_remove: forall pc pid res ret,
  binds pid CRead2 pc ->
  ok pc ->
  binds pid (CntReadOk ret) res ->
  gather_responses (substitute pc pid (CRead3 ret)) (remove res pid) =
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