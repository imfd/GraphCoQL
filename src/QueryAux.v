From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From extructures Require Import ord.

Require Import Query.



Section QueryAux.

  Variables Name Vals : ordType.

  Implicit Type query : @Query Name Vals.
  Implicit Type response : @ResponseObject Name Vals.
  
  Fixpoint query_size query : nat :=
    match query with
    | NestedField _ _ q' => 1 + (query_size q')
    | NestedLabeledField _ _ _ q' => 1 + (query_size q')
    | InlineFragment _ q' => 1 + (query_size q')
    | SelectionSet q' q'' => (query_size q') + (query_size q'')
    | _ => 1
    end.

  
  Fixpoint app_response (r1 r2 : @ResponseObject Name Vals) : ResponseObject :=
    match r1, r2 with
    | ResponseList rs, ResponseList rs' => ResponseList (rs ++ rs')
    | ResponseList rs, _ => ResponseList (rs ++ [:: r2])
    | _, ResponseList rs' => ResponseList (r1 :: rs')
    | _, _ => ResponseList [:: r1; r2]
    end.

  Program Fixpoint response_size response : {m : nat | 0 < m} :=
    match response with
    | Empty => 1
    | Null _ => 3
    | SingleResult _ _ => 3
    | ListResult _ vals => 4 + size vals
    | NestedResult _ r' => 4 + response_size r'
    | NestedListResult _ rs => 4 + 2 * (size rs) + sumn (map (fun r => proj1_sig (response_size r)) rs)
    | ResponseList rs => 1 + sumn (map (fun r => proj1_sig (response_size r)) rs)
    end.

  Check response_size.
  Print response_size.

  Definition responses_size (responses : seq (@ResponseObject Name Vals)) : nat :=
    sumn (map (fun r => proj1_sig (response_size r)) responses).



End QueryAux.

Arguments response_size [Name Vals].