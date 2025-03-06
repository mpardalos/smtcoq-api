Require Import ZArith.

(* Import the SMTCoq-API Library *)
Require Import SMTCoqApi.
Require Import SMTCoq.bva.BVList.
Import BITVECTOR_LIST.

Import ListNotations.
Import EqNotations.

Definition model1 := model_set_fun default_model 0 [] Sort_Int 5%Z.

Definition query1 :=
    {|
      declarations := [];
      assertions := [
        Term_Eq (Term_Fun (0, ([], Sort_Int)) []) (Term_Int 5)
      ]
    |}.

Goal SAT query1.
  exists model1. repeat constructor.
Qed.

Definition query2 :=
    {|
      declarations := [];
      assertions := [
        Term_Eq (Term_Int 5) (Term_Int 5)
      ]
    |}.

Goal valid query2.
  unfold valid, satisfied_by.
  intros.
  repeat constructor.
Qed.

Definition query3 :=
    {|
      declarations := [];
      assertions := [
        Term_Eq (Term_Int 2) (Term_Int 5)
      ]
    |}.

(* The injection tactic fails for terms like Some (existT _ _ _ ) = Some (existT _ _ _), so we use this lemma instead *)
Lemma some_injection {A} (x y : A) :
  Some x = Some y -> x = y.
Proof. congruence. Qed.

Goal invalid query3.
  unfold invalid, satisfied_by.
  intros.
  exists default_model.
  inversion 1; subst.
  match goal with
  | [ H : term_satisfied_by _ _ |- _ ] => inversion H
  end.
  simpl in *.
  apply some_injection in H0.
  inversion_sigma; rewrite <- Eqdep_dec.eq_rect_eq_dec in * by exact dec_sort.
  discriminate.
Qed.

Example t2 :
  UNSAT
    {|
      declarations := [];
      assertions := [
        Term_Eq (Term_Fun (0, ([], Sort_Int)) []) (Term_Int 5);
        Term_Eq (Term_Fun (0, ([], Sort_Int)) []) (Term_Int 2)
      ]
    |}.
Proof.
  unfold UNSAT, not, satisfied_by. intros.
  simpl in *.
  repeat match goal with
         | [ H : Forall _ _ |- _ ] => inversion H; subst; clear H
         end.
  unfold term_satisfied_by in *.
  simpl in *.
  apply some_injection in H1.
  apply some_injection in H2.
  inversion_sigma.
  rewrite <- Eqdep_dec.eq_rect_eq_dec in * by exact dec_sort.
  rewrite Z.eqb_eq in *.
  congruence.
Qed.
