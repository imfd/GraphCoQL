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
    | SingleSelection q => query_size q
    | MultipleSelection q tl => query_size q + selection_size tl
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
    | SingleResponse r => result_size r
    | MultipleResponses hd tl => result_size hd + response_size tl
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

  
  Fixpoint app_responses r1 r2 : @ResponseObject Name Vals :=
    match r1 with
    | SingleResponse r => MultipleResponses r r2
    | MultipleResponses hd tl => MultipleResponses hd (app_responses tl r2)
    end.
  (*
  Fixpoint cleanup_empty_results response : option ResponseObject :=
    match response with
    | SingleResponse Empty => None
    | SingleResponse _ => Some response
    | MultipleResponses Empty tl => cleanup_empty_results tl
    | MultipleResponses hd tl => Multiple                                     
    end
  with cleanup_empty result :=
         match result with
         | Empty => None
         | NestedResult l r => let clean := (cleanup_empty_results r) in
                              if clean is Some r' then
                                Some (NestedResult l r')
                              else
                                None
         | NestedListResult 
         | _ => Some result *)
  
End QueryAux.

Arguments response_size [Name Vals].