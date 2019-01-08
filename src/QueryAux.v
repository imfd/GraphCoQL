From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.
From extructures Require Import ord fmap.

Require Import Query.

Require Import Ssromega.

Section QueryAux.

  Variables Name Vals : ordType.

  Implicit Type query_set : @QuerySet Name Vals.
  Implicit Type query : @Query Name Vals.
  Implicit Type response : @ResponseObject Name Vals.
  Implicit Type result : @Result Name Vals.

  (*
  Equations query_set_size query_set : nat :=
    {
      query_set_size (SingleQuery q) := query_size q;
      query_set_size (SelectionSet q q') := query_size q + query_set_size q'
    }
  where
  query_size query : nat :=
    {
      query_size (NestedField _ _ q') := 1 + (query_set_size q');
      query_size (NestedLabeledField _ _ _ q') := 1 + (query_set_size q');
      query_size (InlineFragment _ q') := 1 + (query_set_size q');
      query_size _ := 1
    }.
  *)
  Fixpoint query_set_size query_set : nat :=
    match query_set with
    | SingleQuery q => query_size q
    | SelectionSet q q' => query_size q + query_set_size q'
    end

  with query_size query : nat :=
         match query with
         | NestedField _ _ q' => 1 + (query_set_size q')
         | NestedLabeledField _ _ _ q' => 1 + (query_set_size q')
         | InlineFragment _ q' => 1 + (query_set_size q')
         | _ => 1
         end.

  Definition queries_size (queries : seq Query) := sumn (map query_size queries).
 

  
  Definition partial_query_eq (q1 q2 : @Query Name Vals) : bool :=
    match q1, q2 with
    | SingleField n α, SingleField n' α'
    | NestedField n α _, NestedField n' α' _ => (n == n') && (α == α')
    | LabeledField l n α, LabeledField l' n' α'
    | NestedLabeledField l n α _, NestedLabeledField l' n' α' _ => (l == l') && (n == n') && (α == α')
    | InlineFragment t _, InlineFragment t' _ => t == t'
    | _, _ => false
    end.

  Equations(noind) result_size result : nat :=
    {
      result_size (Results [::]) := 1;
      result_size (Results (cons hd tl)) := 1 + (response_size hd) + (responses_size tl)
    }
  with
  response_size response : nat :=
    {
      response_size (Null _) := 3;
      response_size (SingleResult _ _) := 3;
      response_size (ListResult _ vals) := 4 + size vals;
      response_size (NestedResult _ r') := 4 + result_size r';
      response_size (NestedListResult _ rs) := 4 + 2 * size rs + results_size rs
    }
  where
  responses_size (responses : seq (@ResponseObject Name Vals)) : nat :=
    {
      responses_size [::] := 0;
      responses_size (cons hd tl) := response_size hd + responses_size tl
    }
  where
  results_size (results : seq (@Result Name Vals)) : nat :=
    {
      results_size [::] := 0;
      results_size (cons hd tl) := (result_size hd) + (results_size tl)
    }.



  
  Fixpoint app_responses r1 r2 : @Result Name Vals :=
    match r1, r2 with
   | Results rs, Results rs' => Results (rs ++ rs')
    end.

  
  Lemma responses_size_app (l1 l2 : seq.seq (@ResponseObject Name Vals)) : responses_size (l1 ++ l2) = responses_size l1 + responses_size l2.
  Proof.
    elim: l1 => [//| n l' IH].
    by simpl; rewrite IH addnA.
  Qed.
  
  Lemma responses_lt_result (l : list (@ResponseObject Name Vals)) (r : @Result Name Vals) :
    responses_size l < result_size (Results l).
  Proof.
    elim: l => [| x l' IH].
    - by simpl; rewrite result_size_equation_1.
    - by simpl; rewrite result_size_equation_2;  ssromega.
  Qed.

  
  Lemma response_size_n_0 (r : @ResponseObject Name Vals) : 0 < response_size r.
  Proof. by case: r. Qed.
  
End QueryAux.


Arguments partial_query_eq [Name Vals].
Arguments response_size [Name Vals].