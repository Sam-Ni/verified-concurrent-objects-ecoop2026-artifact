Require Import
  List
  Arith
  LibVar
  LibEnv
  LTS
  Refinement
  ImplRefinement
  Compose
  ImplTensor
  RawTensor
  Tensor
  SyncLTS
  VE.
Import ListNotations.

Section VerifiedConcurrentObject.

Context {liA liB : language_interface}.
Variable L: lts li_null liA.
Variable M: lts liA liB.
Variable L': lts li_null liB.

Definition veriobj := 
  refines L (sync L) /\
  impl_refines M (sync M) /\
  refines (linked_lts (compose L M)) (sync L').

End VerifiedConcurrentObject.

Notation " L ⊢ M ~: L' " := (veriobj L M L') (at level 67).

Require Import
  BSim.

Section BSim.

Context {liA liB : language_interface}.
Variable L: lts li_null liA.
Variable M: lts liA liB.
Variable L': lts li_null liB.

Theorem backward_simulation: 
  forall (b : composed_lts.state (compose L M) -> L'.(state) -> Prop)
         (inv : composed_lts.state (compose L M) -> Prop),
  refines L (sc L) ->
  impl_refines M (sc M) ->
  refines L' (sc L') ->
  composed_bsim_properties_inv_ind _ _ _ b inv ->
  veriobj L M L'.
Proof.
  intros.
  unfold veriobj.
  intuition.
  eapply trans_refinement; eauto.
  eapply composed_backward_simulation_inv_ind'; eauto.
Qed.

End BSim.
