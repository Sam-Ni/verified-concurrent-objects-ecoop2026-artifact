Require Import
  List
  LibEnv
  LTS
  VerifiedConcurrentObject
  ImplRawCompose
  Refinement
  ImplRefinement
  SyncLTS
  VE
  Compose
  Link
  VComp.
Import ListNotations.

Section Weaken.

Context {liA liB : language_interface}.
Variable L1: lts li_null liA.
Variable L1': lts li_null liA.
Variable M1: lts liA liB.
Variable L2: lts li_null liB.

(* Notation " L ⊑' L' " := (refines L L') (at level 67). *)

Theorem Weaken: 
  L1 ⊢ M1 ~: L2 ->
  L1' ⊑' L1 ->
  L1' ⊑' (sync L1') ->
  L1' ⊢ M1 ~: L2.
Proof.
  unfold veriobj.
  intros.
  intuition.
  eapply trans_refinement; eauto.
  eapply linked_refines_congruence; eauto.
  eapply trans_refinement; eauto.
  eapply trans_refinement; eauto.
  eapply sync_refines_raw; eauto.
Qed.

End Weaken.
