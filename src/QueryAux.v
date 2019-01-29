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

  Implicit Type queries : seq (@Query Name Vals).
  Implicit Type query : @Query Name Vals.
  Implicit Type response : @ResponseObject Name Vals.


  Equations query_size query : nat :=
    {
      query_size (NestedField _ _ q') := 1 + queries_size q';
      query_size (NestedLabeledField _ _ _ q') => 1 + (queries_size q');
      query_size (InlineFragment _ q') => 1 + (queries_size q');
      query_size _ := 1
    }
  where
  queries_size queries : nat :=
    {
      queries_size [::] := 0;
      queries_size (cons hd tl) := query_size hd + queries_size tl
    }.

  
  Definition partial_query_eq (q1 q2 : @Query Name Vals) : bool :=
    match q1, q2 with
    | SingleField n α, SingleField n' α'
    | NestedField n α _, NestedField n' α' _ => (n == n') && (α == α')
    | LabeledField l n α, LabeledField l' n' α'
    | NestedLabeledField l n α _, NestedLabeledField l' n' α' _ => (l == l') && (n == n') && (α == α')
    | InlineFragment t _, InlineFragment t' _ => t == t'
    | _, _ => false
    end.

  Equations(noind) response_size response : nat :=
    {
      response_size (Null _) := 3;
      response_size (SingleResult _ _) := 3;
      response_size (ListResult _ vals) := 4 + size vals;
      response_size (NestedResult _ r') := 4 + responses_size r';
      response_size (NestedListResult _ rs) := 4 + 2 * size rs + responses_size' rs
    }
  where
  responses_size (responses : seq (@ResponseObject Name Vals)) : nat :=
    {
      responses_size [::] := 0;
      responses_size (cons hd tl) := response_size hd + responses_size tl
    }
  where responses_size' (responses : seq (seq (@ResponseObject Name Vals))) : nat :=
    {
      responses_size' [::] := 0;
      responses_size' (cons hd tl) := responses_size hd + responses_size' tl
    }.
  
  Lemma responses_size_app (l1 l2 : seq.seq (@ResponseObject Name Vals)) : responses_size (l1 ++ l2) = responses_size l1 + responses_size l2.
  Proof. 
    elim: l1 => [//| n l' IH].
    by simpl; rewrite IH addnA.
  Qed.
  
  

  
  Lemma response_size_n_0 (r : @ResponseObject Name Vals) : 0 < response_size r.
  Proof. by case: r. Qed.
  
End QueryAux.


Arguments partial_query_eq [Name Vals].
Arguments response_size [Name Vals].