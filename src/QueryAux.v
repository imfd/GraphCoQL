From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From extructures Require Import ord.

Require Import Query.



Section QueryAux.

  Variables S Vals : ordType.

  Implicit Type query : @Query S Vals.
  Implicit Type response : @ResponseObject S Vals.
  
  Fixpoint size query : nat :=
    match query with
    | NestedField _ _ q' => 1 + (size q')
    | NestedLabeledField _ _ _ q' => 1 + (size q')
    | InlineFragment _ q' => 1 + (size q')
    | SelectionSet q' q'' => (size q') + (size q'')
    | _ => 1
    end.

  
  Fixpoint isFieldSelection query :=
    match query with
    | SingleField _ _ => true
    | LabeledField _ _ _ => true
    | NestedField _ _ _ => true
    | NestedLabeledField _ _ _ _ => true
    | SelectionSet hd tl => isFieldSelection hd && isFieldSelection tl
    | _ => false
    end.

  Fixpoint isInlineFragmentSelection query :=
    match query with
    | InlineFragment _ _ => true
    | SelectionSet hd tl => isInlineFragmentSelection hd && isInlineFragmentSelection tl
    | _ => false
    end.

  Fixpoint collect_nested_queries query : seq Query :=
    match query with
    | SelectionSet hd tl => (collect_nested_queries hd) ++ (collect_nested_queries tl)
    | _ => [:: query]
    end.

  Lemma cat_not_empty_not_empty (A : eqType) (l1 l2 : seq A) :
    [|| l1 != [::] | l2 != [::]] -> l1 ++ l2 != [::].
  Proof. by case: l1. Qed.
  
  Lemma collect_query_not_empty query : (collect_nested_queries query) != [::].
  Proof.
    elim: query => //=.
      by move=> q IH q' IH'; apply: cat_not_empty_not_empty; apply: Bool.orb_true_intro; left.
  Qed.

  Fixpoint query_of_list (s : seq (@Query S Vals)) : option Query :=
    match s with
    | [::] => None
    | hd :: tl => if query_of_list tl is Some q then
                   Some (SelectionSet hd q)
                 else
                   Some hd
    end.

  Lemma query_of_list_not_none (s : seq Query) : s != [::] -> query_of_list s <> None.
  Proof.
    elim: s => //.
    by move=> q s' IH _ /=; case (query_of_list s') => //.
  Qed.

  

 
       
  Fixpoint flatten_query query : Query :=
    match query with
    | SingleField _ _ => query
    | LabeledField _ _ _ => query
    | NestedField n args ϕ => NestedField n args (flatten_query ϕ)
    | NestedLabeledField l n args ϕ => NestedLabeledField l n args (flatten_query ϕ)
    | InlineFragment t ϕ => InlineFragment t (flatten_query ϕ)
    | SelectionSet hd tl => let flattened_hd := flatten_query hd in
                           let flattened_tl := flatten_query tl in
                           let fix merge_queries_to_selection (q1 q2 : Query) : Query :=
                               match q1, q2 with
                               | SelectionSet hd tl, SelectionSet hd' tl' => SelectionSet hd (merge_queries_to_selection tl q2)
                               | SelectionSet hd tl, _ => SelectionSet hd (merge_queries_to_selection tl q2)
                               | _, _ => SelectionSet q1 q2
                               end
                           in
                           merge_queries_to_selection flattened_hd flattened_tl
    end.

  Fixpoint flatten_response response : ResponseObject :=
    match response with
    | NestedResult l r' => NestedResult l (flatten_response r')
    | NestedListResult l rs => NestedListResult l (map flatten_response rs)
    | ResponseList hd tl => let flattened_hd := flatten_response hd in
                          let flattened_tl := flatten_response tl in
                          let fix merge_responses_to_list (r1 r2 : ResponseObject) : ResponseObject :=
                              match r1, r2 with
                              | ResponseList hd tl, ResponseList hd' tl' => ResponseList hd (merge_responses_to_list tl r2)
                              | ResponseList hd tl, _ => ResponseList hd (merge_responses_to_list tl r2)
                              | _, _ => ResponseList r1 r2
                               end
                          in
                           merge_responses_to_list flattened_hd flattened_tl
    | _ => response
    end.         

  
End QueryAux.