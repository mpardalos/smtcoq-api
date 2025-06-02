Require List.
Import List.ListNotations.

Require Import SMTLib.

Fixpoint term_domain (t : SMTLib.term) : list const_sym :=
  match t with
  | SMTLib.Term_Const sym => [sym]
  | SMTLib.Term_Int _ => []
  | SMTLib.Term_Geq l r => (term_domain l) ++ (term_domain r)
  | SMTLib.Term_Eq l r => (term_domain l) ++ (term_domain r)
  | SMTLib.Term_And l r => (term_domain l) ++ (term_domain r)
  | SMTLib.Term_Or l r => (term_domain l) ++ (term_domain r)
  | SMTLib.Term_Not e => term_domain e
  | SMTLib.Term_ITE c t f => (term_domain c) ++ (term_domain t) ++ (term_domain f)
  | SMTLib.Term_True => []
  | SMTLib.Term_False => []
  | SMTLib.Term_BVLit _ _ => []
  | SMTLib.Term_BVConcat l r => (term_domain l) ++ (term_domain r)
  | SMTLib.Term_BVExtract _ _ e => term_domain e
  | SMTLib.Term_BVUnaryOp _ e => term_domain e
  | SMTLib.Term_BVBinOp _ l r => (term_domain l) ++ (term_domain r)
  | SMTLib.Term_BVUlt l r => (term_domain l) ++ (term_domain r)
  end
.

Definition domain (q : query) : list const_sym := List.concat (List.map term_domain q).

Definition list_disjoint {A} (l1 l2 : list A) :=
  forall x, (List.In x l1 -> ~ List.In x l2) /\ (List.In x l2 -> ~ List.In x l1).

Lemma list_disjoint_cons {A} (a : A) l1 l2 :
  list_disjoint (a :: l1) l2 -> list_disjoint l1 l2.
Proof.
  unfold list_disjoint in *.
  intros H; split.
  - destruct H with x; intuition eauto with datatypes.
  - destruct H with x; intuition eauto with datatypes.
Qed.

Lemma list_disjoint_concat {A} (l1 l2 l3 : list A) :
  list_disjoint (l1 ++ l2) l3 -> list_disjoint l2 l3.
Proof.
  revert l2 l3.
  induction l1.
  - trivial.
  - intros.
    rewrite <- List.app_comm_cons in H.
    apply list_disjoint_cons in H.
    eauto.
Qed.

Definition disjoint (q1 q2 : query) := list_disjoint (domain q1) (domain q2).

Lemma disjoint_cons (t : term) q1 q2 :
  disjoint (t :: q1)%list q2 -> disjoint q1 q2.
Proof.
  unfold disjoint in *.
  intros H.
  unfold domain in H; simpl in H.
  eapply list_disjoint_concat.
  eassumption.
Qed.

Infix "⊧" := satisfied_by (at level 20).

Lemma concat_same_model : forall q1 q2 ρ,
    ρ ⊧ q1 ->
    ρ ⊧ q2 ->
    ρ ⊧ (q1 ++ q2)%list.
Proof.
  induction q1.
  - intros.
    simpl in *.
    assumption.
  - intros * Hq1 Hq2.
    inversion Hq1; subst; clear Hq1.
    rewrite <- List.app_comm_cons.
    constructor; eauto.
    apply IHq1; eauto.
Qed.

Definition smt_reflect (q: query) (P : valuation -> Prop): Prop :=
  forall ρ, ρ ⊧ q <-> P ρ.

Lemma concat_conj :
  forall q1 q2 P1 P2,
    smt_reflect q1 P1 ->
    smt_reflect q2 P2 ->
    smt_reflect (q1 ++ q2)%list (fun ρ => P1 ρ /\ P2 ρ).
Proof.
  induction q1; intros * * HPq1 HPq2.
  - simpl. split. intros H.
    + split.
      * apply HPq1. constructor.
      * apply HPq2. assumption.
    + intros [HP1 HP2].
      apply HPq2.
      assumption.
  - split.
    + intros Hρ.
      unfold "⊧" in Hρ.
      rewrite List.Forall_app in Hρ; destruct Hρ.
      fold (ρ ⊧ (a :: q1)%list) in *; fold (ρ ⊧ q2) in *.
      split.
      * apply HPq1. assumption.
      * apply HPq2. assumption.
    + intros [HP1 HP2].
      unfold "⊧".
      rewrite List.Forall_app.
      fold (ρ ⊧ (a :: q1)%list) in *; fold (ρ ⊧ q2) in *.
      split.
      * apply HPq1. assumption.
      * apply HPq2. assumption.
Qed.

Local Open Scope list.

Lemma unsat_smt_reflect_false q :
  UNSAT q <-> smt_reflect q (fun _ => False).
Proof.
  unfold UNSAT.
  split.
  - intros Hunsat.
    split; intuition eauto.
  - intros Hq * contra.
    apply Hq in contra.
    contradiction.
Qed.

Definition Qa := [ Term_Const 0 ].
Definition a_is_true := (fun ρ => ρ 0 = Some (Value_Bool true)).
Definition a_is_false := (fun ρ => ρ 0 = Some (Value_Bool false)).

Lemma Qa_prop : smt_reflect Qa a_is_true.
Proof.
  unfold Qa, a_is_true.
  split; intros.
  - inversion H; subst; clear H.
    inversion H2; subst; clear H2.
    reflexivity.
  - repeat constructor.
    unfold term_satisfied_by; simpl.
    rewrite H; clear H.
    reflexivity.
Qed.

Definition Qnota := [ Term_Not (Term_Const 0) ].
Lemma Qnota_prop : smt_reflect Qnota a_is_false.
Proof.
  unfold Qnota, a_is_false.
  split; intros.
  - inversion H; subst; clear H.
    inversion H2; subst; clear H2.
    destruct (ρ 0); try discriminate.
    destruct v; try discriminate.
    inversion H0.
    symmetry in H1. apply Bool.negb_sym in H1. simpl in H1.
    subst. reflexivity.
  - repeat constructor.
    unfold term_satisfied_by; simpl.
    rewrite H; clear H.
    reflexivity.
Qed.

Lemma Qa_Qnota_concat : smt_reflect (Qa ++ Qnota) (fun ρ => a_is_true ρ /\ a_is_false ρ).
Proof. auto using concat_conj, Qa_prop, Qnota_prop. Qed.

(* Global Instance x : Morphisms.Proper (Morphisms.pointwise_relation valuation iff => Basics.flip Basics.impl) (smt_reflect (Qa ++ Qnota)). *)

Require Import Relation_Definitions Setoid.

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

Lemma Qa_Qnota_unsat : UNSAT (Qa ++ Qnota).
  apply unsat_smt_reflect_false.
  rewrite (smt_reflect_rewrite (fun ρ => a_is_true ρ /\ a_is_false ρ)).
  - apply Qa_Qnota_concat.
  - split; try contradiction.
    intros [Htrue Hfalse].
    unfold a_is_true, a_is_false in *.
    rewrite Htrue in Hfalse.
    discriminate.
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
  UNSAT (q1 ++ q2) ->
  (forall ρ, ~ (P1 ρ /\ P2 ρ)).
Proof.
  intros Hq1P1 Hq2P2 Hunsat.
  eapply unsat_negation.
  - eauto using concat_conj.
  - eauto.
Qed.
