(**************************************************************************)
(*                                                                        *)
(*     SMTCoq-Api                                                         *)
(*     Copyright (C) 2020 - 2022                                          *)
(*                                                                        *)
(*     Author: Chantal Keller - LMF, Université Paris-Saclay              *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


Require Import SMTCoq.SMTCoq.
Require Import ZArith.


(* A high-level, simple syntax for SMT-LIB *)
(* TO BE EXTENDED *)
Section SMTLib.

  (* Uninterpreted sorts *)
  Local Notation sort_sym := nat.

  Inductive sort : Set :=
  | Sort_Bool
  | Sort_Int
  | Sort_Uninterpreted (_:sort_sym)
  .

  (* Uninterpreted functions. Remarks:
     - predicate symbols are function symbols of codomain Bool
     - variables are function symbols without arguments
   *)
  Local Notation fun_sym := (nat * ((list sort) * sort))%type.

  Inductive term : Set :=
  | Term_Fun : fun_sym -> list term -> term
  | Term_Int : Z -> term
  | Term_Geq : term -> term -> term
  | Term_Eq : term -> term -> term
  | Term_And : term -> term -> term
  .


  (* To be able to interpret function symbol application, we introduce
     an informative cast between sorts

     See
     https://www.lri.fr/~keller/Documents-recherche/Publications/thesis13.pdf
     Sec.3.2.2 *)
  Section Cast.
    Definition cast_result (A:Type) (n m:A) :=
      option (forall (P:A -> Type), P n -> P m).
    Definition idcast (A:Type) (n:A) : cast_result A n n :=
      Some (fun P x => x).
    Arguments idcast {A n}.

    Fixpoint nat_cast (n m:nat) : cast_result nat n m :=
      match n, m with
      | O, O => idcast
      | S n, S m =>
          match nat_cast n m with
          | Some k => Some (fun P => k (fun x => P (S x)))
          | None => None
          end
      | _, _ => None
      end.

    Lemma nat_cast_refl:
      forall n, nat_cast n n = idcast.
    Proof. induction n as [ |n IHn]; simpl; try rewrite IHn; auto. Qed.

    Definition cast (A B:sort) : cast_result sort A B :=
      match A, B return cast_result sort A B with
      | Sort_Bool, Sort_Bool => idcast
      | Sort_Int, Sort_Int => idcast
      | Sort_Uninterpreted n1, Sort_Uninterpreted n2 =>
          match nat_cast n1 n2 with
          | Some k => Some (fun P => k (fun x => P (Sort_Uninterpreted x)))
          | None => None
          end
      | _, _ => None
      end.

    Lemma cast_refl:
      forall s, cast s s = idcast.
    Proof. destruct s as [ | |n]; simpl; auto. now rewrite nat_cast_refl. Qed.

  End Cast.


  (* Interpretation *)
  Section Interpretation.

    (* Interpretation of sorts *)
    Variable interp_sort_sym : sort_sym -> Type.

    Definition interp_sort (s:sort) : Type :=
      match s with
      | Sort_Bool => bool
      | Sort_Int => Z
      | Sort_Uninterpreted sy => interp_sort_sym sy
      end.

    (* Interpretation of function types *)
    Fixpoint interp_fun_type (dom:list sort) (codom:sort) : Type :=
      match dom with
      | nil => interp_sort codom
      | s::dom => (interp_sort s) -> (interp_fun_type dom codom)
      end.

    (* Applying function symbols *)
    Fixpoint apply_fun (dom:list sort) (codom:sort) :
      (interp_fun_type dom codom) ->
      (list (option {A:sort & interp_sort A})) ->
      option (interp_sort codom) :=
      match dom return
            (interp_fun_type dom codom) ->
            (list (option {A:sort & interp_sort A})) ->
            option (interp_sort codom)
      with
      | nil => fun f _ => Some f
      | s::dom => fun f arg =>
                  match arg with
                  | (Some (existT _ s' a))::arg =>
                      match cast s' s with
                      | Some k => apply_fun dom codom (f (k _ a)) arg
                      | None => None
                      end
                  | _ => None
                  end
      end.

    (* Interpretation of terms *)
    Variable interp_fun_sym :
      nat -> forall (dom:list sort) (codom:sort), interp_fun_type dom codom.

    Fixpoint interp_term (t:term) : option {A : sort & interp_sort A} :=
      match t with
      | Term_Fun (n, (dom, codom)) arg =>
          match apply_fun dom codom (interp_fun_sym n dom codom)
                  (List.map interp_term arg)
          with
          | Some i => Some (existT _ codom i)
          | None => None
          end
      | Term_Int z => Some (existT _ Sort_Int z)
      | Term_Geq t1 t2 =>
          match interp_term t1, interp_term t2 with
          | Some (existT _ Sort_Int z1), Some (existT _ Sort_Int z2) =>
              Some (existT _ Sort_Bool (z1 >=? z2)%Z)
          | _, _ => None
          end
      | Term_Eq t1 t2 =>
          match interp_term t1, interp_term t2 with
          | Some (existT _ Sort_Int z1), Some (existT _ Sort_Int z2) =>
              Some (existT _ Sort_Bool (z1 =? z2)%Z)
          | _, _ => None
          end
      | Term_And t1 t2 =>
          match interp_term t1, interp_term t2 with
          | Some (existT _ Sort_Bool b1), Some (existT _ Sort_Bool b2) =>
              Some (existT _ Sort_Bool (b1 && b2)%bool)
          | _, _ => None
          end
      end.

    Definition interp_formula (t:term) : bool :=
      match interp_term t with
      | Some (existT _ Sort_Bool b) => b
      | _ => true
      end.

  End Interpretation.

  (* Default values for interpreted sorts *)
  Section Default.
    Variable interp_sort_sym : sort_sym -> Type.
    Variable interp_sort_sym_def : forall (sy:sort_sym), interp_sort_sym sy.

    Definition interp_sort_def (s:sort) : interp_sort interp_sort_sym s :=
      match s return interp_sort interp_sort_sym s with
      | Sort_Bool => true
      | Sort_Int => 0%Z
      | Sort_Uninterpreted sy => interp_sort_sym_def sy
      end.

    Fixpoint interp_fun_type_def (dom:list sort) (codom:sort) :
      interp_fun_type interp_sort_sym dom codom :=
      match dom return interp_fun_type interp_sort_sym dom codom with
      | nil => interp_sort_def codom
      | _::dom => fun _ => interp_fun_type_def dom codom
      end.
  End Default.

End SMTLib.


(* Register constants for OCaml access *)
Register Sort_Bool as SMTCoqAPI.SMTLib.Sort_Bool.
Register Sort_Int as SMTCoqAPI.SMTLib.Sort_Int.
Register Sort_Uninterpreted as SMTCoqAPI.SMTLib.Sort_Uninterpreted.
Register Term_Fun as SMTCoqAPI.SMTLib.Term_Fun.
Register Term_Int as SMTCoqAPI.SMTLib.Term_Int.
Register Term_Geq as SMTCoqAPI.SMTLib.Term_Geq.
Register Term_Eq as SMTCoqAPI.SMTLib.Term_Eq.
Register Term_And as SMTCoqAPI.SMTLib.Term_And.
