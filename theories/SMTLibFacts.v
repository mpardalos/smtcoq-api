Require List.
Import List.ListNotations.

Require Import SMTLib.

Fixpoint term_domain (t : SMTLib.term) : list fun_sym :=
  match t with
  | SMTLib.Term_Fun sym args => sym :: (List.concat (List.map term_domain args))
  | SMTLib.Term_Int _ => []
  | SMTLib.Term_Geq l r => (term_domain l) ++ (term_domain r)
  | SMTLib.Term_Eq l r => (term_domain l) ++ (term_domain r)
  | SMTLib.Term_And l r => (term_domain l) ++ (term_domain r)
  | SMTLib.Term_Or l r => (term_domain l) ++ (term_domain r)
  | SMTLib.Term_Not e => term_domain e
  | SMTLib.Term_ITE c t f => (term_domain c) ++ (term_domain t) ++ (term_domain f)
  | SMTLib.Term_True => []
  | SMTLib.Term_False => []
  | SMTLib.Term_BVLit _ => []
  | SMTLib.Term_BVConcat l r => (term_domain l) ++ (term_domain r)
  | SMTLib.Term_BVExtract _ _ e => term_domain e
  | SMTLib.Term_BVUnaryOp _ e => term_domain e
  | SMTLib.Term_BVBinOp _ l r => (term_domain l) ++ (term_domain r)
  | SMTLib.Term_BVUlt l r => (term_domain l) ++ (term_domain r)
  end
.

Definition domain (q : query) : list fun_sym := List.concat (List.map term_domain q).

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

Lemma concat_same_model : forall q1 q2,
    disjoint q1 q2 ->
    forall ρ, ρ ⊧ q1 -> ρ ⊧ q2 -> ρ ⊧ (q1 ++ q2)%list.
Proof.
  induction q1.
  - intros.
    simpl in *.
    assumption.
  - intros * Hdisjoint * Hq1 Hq2.
    inversion Hq1; subst; clear Hq1.
    rewrite <- List.app_comm_cons.
    constructor; eauto.
    apply IHq1; eauto.
    eapply disjoint_cons. eassumption.
Qed.
