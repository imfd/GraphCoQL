From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From extructures Require Import ord fmap.

Require Import Query.



Section QueryAux.

  Variables Name Vals : ordType.

  Implicit Type query_set : @QuerySet Name Vals.
  Implicit Type query : @Query Name Vals.
  Implicit Type response : @ResponseObject Name Vals.
  Implicit Type result : @Result Name Vals.
  
  Fixpoint query_set_size query_set : nat :=
    let: SelectionSet queries := query_set in
        sumn (map query_size queries)

  with query_size query : nat :=
         match query with
         | NestedField _ _ q' => 1 + (query_set_size q')
         | NestedLabeledField _ _ _ q' => 1 + (query_set_size q')
         | InlineFragment _ q' => 1 + (query_set_size q')
         | _ => 1
         end.

  Definition queries_size (queries : seq Query) := sumn (map query_size queries).
 

  Definition app_query_sets q1 q2 : @QuerySet Name Vals :=
      match q1, q2 with
      | SelectionSet ϕ, SelectionSet ϕ' => SelectionSet (ϕ ++ ϕ')
      end.
  
  Definition app_queries q1 q2 : @QuerySet Name Vals := SelectionSet [:: q1 ; q2].

  
  Definition partial_query_eq (q1 q2 : @Query Name Vals) : bool :=
    match q1, q2 with
    | SingleField n α, SingleField n' α'
    | NestedField n α _, NestedField n' α' _ => (n == n') && (α == α')
    | LabeledField l n α, LabeledField l' n' α'
    | NestedLabeledField l n α _, NestedLabeledField l' n' α' _ => (l == l') && (n == n') && (α == α')
    | InlineFragment t _, InlineFragment t' _ => t == t'
    | _, _ => false
    end.
  
  Fixpoint response_size response : nat :=
    match response with
    | Response r => sumn (map result_size r)
    end
  with result_size result : nat :=
    match result with
    | Empty => 1
    | Null _ => 3
    | SingleResult _ _ => 3
    | ListResult _ vals => 4 + size vals
    | NestedResult _ r' => 4 + response_size r'
    | NestedListResult _ rs => 4 + 2 * (size rs) + sumn (map response_size rs)
    end.

  Definition responses_size (responses : seq (@ResponseObject Name Vals)) : nat :=
    sumn (map response_size responses).

  Definition results_size (results : seq (@Result Name Vals)) : nat :=
    sumn (map result_size results).
  
  Fixpoint app_responses r1 r2 : @ResponseObject Name Vals :=
    match r1, r2 with
    | Response r, Response r' => Response (r ++ r')
    end.
  
End QueryAux.


Arguments partial_query_eq [Name Vals].
Arguments response_size [Name Vals].