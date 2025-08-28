Require List.
Import List.ListNotations.
Require Import Morphisms.

Require Import SMTLib.

Infix "⊧" := satisfied_by (at level 20).

Definition smt_reflect (q: query) (P : valuation -> Prop): Prop :=
  forall ρ, ρ ⊧ q <-> P ρ.

Lemma combine_wf q1 q2 :
  List.Forall
    (fun n : nat => exists s : sort, List.In (n, s) (declarations q1 ++ declarations q2))
    (lst_domain (assertions q1 ++ assertions q2)).
Proof.
  destruct q1, q2.
  unfold lst_domain in *.
  rewrite ! List.Forall_forall in *.
  simpl in *.
  rewrite List.Forall_forall in *.
  intros n H.
  rewrite
    <- List.flat_map_concat_map,
    List.flat_map_app,
    List.in_app_iff
    in *.
  setoid_rewrite List.in_app_iff.
  destruct H.
  - edestruct wf as [n' Hwf]. eapply H.
    eauto.
  - edestruct wf0 as [n' Hwf]. eapply H.
    eauto.
Qed.

Definition combine (q1 q2: query) : query :=
  {|
    declarations := declarations q1 ++ declarations q2;
    assertions := assertions q1 ++ assertions q2;
    wf := combine_wf q1 q2
  |}.

Lemma concat_conj :
  forall q1 q2 P1 P2,
    smt_reflect q1 P1 ->
    smt_reflect q2 P2 ->
    smt_reflect (combine q1 q2) (fun ρ => P1 ρ /\ P2 ρ).
Proof.
  destruct q1, q2.
  unfold smt_reflect, satisfied_by, combine.
  simpl.
  intros.
  setoid_rewrite List.Forall_app.
  firstorder.
Qed.

Local Open Scope list.

Lemma unsat_smt_reflect_false q :
  UNSAT q <-> smt_reflect q (fun _ => False).
Proof.
  unfold UNSAT, smt_reflect, satisfied_by, combine.
  simpl.
  intros.
  firstorder.
Qed.

Lemma smt_reflect_rewrite : forall P2 P1 q,
    (forall ρ, P1 ρ <-> P2 ρ) ->
    (smt_reflect q P1 <-> smt_reflect q P2).
Proof.
  unfold smt_reflect.
  intros * HP.
  split; intros Hsmt_reflect ρ.
  - rewrite <- HP.
    apply Hsmt_reflect.
  - rewrite HP.
    apply Hsmt_reflect.
Qed.

Definition equisatisfiable q1 q2 := SAT q1 <-> SAT q2.

Lemma equisatisfiable_reflect q1 q2 P1 P2 :
  smt_reflect q1 P1 ->
  smt_reflect q2 P2 ->
  equisatisfiable q1 q2 ->
  ((exists ρ, P1 ρ) <-> (exists ρ, P2 ρ)).
Proof.
  unfold smt_reflect, equisatisfiable, SAT.
  intros Hq1P1 Hq2P2 [q1q2 q2q1] *.
  split.
  - intros [ρ1 H1].
    apply Hq1P1 in H1.
    edestruct q1q2 as [ρ2 H2]. exists ρ1. exact H1.
    exists ρ2. apply Hq2P2. apply H2.
  - intros [ρ2 H2].
    apply Hq2P2 in H2.
    edestruct q2q1 as [ρ1 H1]. exists ρ2. exact H2.
    exists ρ1. apply Hq1P1. apply H1.
Qed.

Lemma unsat_negation q P :
  smt_reflect q P ->
  UNSAT q ->
  (forall ρ, ~ P ρ).
Proof.
  intros Hreflect Hunsat * contra.
  unfold UNSAT, smt_reflect in *.
  repeat match goal with
         | [ H : forall (_ : valuation), _ |- _ ] => specialize (H ρ)
         end.
  apply Hreflect in contra.
  contradiction.
Qed.

Lemma incompatible_reflect q1 q2 P1 P2 :
  smt_reflect q1 P1 ->
  smt_reflect q2 P2 ->
  UNSAT (combine q1 q2) ->
  (forall ρ, ~ (P1 ρ /\ P2 ρ)).
Proof.
  intros Hq1P1 Hq2P2 Hunsat.
  eapply unsat_negation.
  - eauto using concat_conj.
  - eauto.
Qed.
