From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From extructures Require Import ord.

Require Import Query.



Section QueryAux.

  Variables Name Vals : ordType.

  Implicit Type selection : @SelectionSet Name Vals.
  Implicit Type query : @Query Name Vals.
  Implicit Type response : @ResponseObject Name Vals.
  Implicit Type result : @Result Name Vals.
  
  Fixpoint selection_size selection : nat :=
    match selection with
    | Selection queries => sumn (map query_size queries)
    end
  with query_size query : nat :=
         match query with
         | NestedField _ _ q' => 1 + (selection_size q')
         | NestedLabeledField _ _ _ q' => 1 + (selection_size q')
         | InlineFragment _ q' => 1 + (selection_size q')
         | _ => 1
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

Arguments response_size [Name Vals].