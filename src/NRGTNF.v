From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From extructures Require Import ord fmap.


Require Import Query.
Require Import QueryAux.
Require Import QueryConformance.
Require Import SchemaWellFormedness.

Section NRGTNF.

  Variables Name Vals : ordType.

  Implicit Type query : @Query Name Vals.
  
  Inductive GroundTypedNormalForm : @Query Name Vals -> Prop :=
  | GT_Field : forall f args,
      GroundTypedNormalForm (SingleField f args)

  | GT_LabeledField : forall label f args,
      GroundTypedNormalForm (LabeledField label f args)

  | GT_NestedField : forall f args ϕ,
      GroundTypedNormalForm ϕ ->
      GroundTypedNormalForm (NestedField f args ϕ)

  | GT_NestedLabeledField : forall label f args ϕ,
      GroundTypedNormalForm ϕ ->
      GroundTypedNormalForm (NestedLabeledField label f args ϕ)

  | GT_InlineFragment : forall t ϕ,
       isFieldSelection ϕ ->
      GroundTypedNormalForm ϕ ->
      GroundTypedNormalForm (InlineFragment t ϕ)

  | GT_SelectionSet : forall ϕ ϕ',
      (isFieldSelection ϕ && isFieldSelection ϕ') || (isInlineFragmentSelection ϕ && isInlineFragmentSelection ϕ') ->
      GroundTypedNormalForm ϕ ->
      GroundTypedNormalForm ϕ' ->
      GroundTypedNormalForm (SelectionSet ϕ ϕ').

  Fixpoint is_ground_typed_normal_form query :=
    match query with
    | NestedField _ _ ϕ => is_ground_typed_normal_form ϕ
    | NestedLabeledField _ _ _ ϕ => is_ground_typed_normal_form ϕ
    | InlineFragment _ ϕ => isFieldSelection ϕ && is_ground_typed_normal_form ϕ
    | SelectionSet ϕ ϕ' => ((isFieldSelection ϕ && isFieldSelection ϕ')
                           || (isInlineFragmentSelection ϕ && isInlineFragmentSelection ϕ'))
                            && is_ground_typed_normal_form ϕ && is_ground_typed_normal_form ϕ'
    | _ => true
    end.






    Fixpoint partial_query_eq (q1 q2 : @Query Name Vals) : bool :=
    match q1, q2 with
    | SingleField name args, SingleField name' args' => (name == name') && (args == args')
    | LabeledField label name args, LabeledField label' name' args' => (label == label') && (name == name') && (args == args')
    | NestedField name args ϕ, NestedField name' args' ϕ' => (name == name') && (args == args')
    | NestedLabeledField label name args ϕ, NestedLabeledField label' name' args' ϕ' =>
      (label == label') && (name == name') && (args == args')
    | InlineFragment t ϕ, InlineFragment t' ϕ' => (t == t')
    | SelectionSet ϕ ϕ', SelectionSet ψ ψ' => (partial_query_eq ϕ ψ) &&  (partial_query_eq ϕ' ψ')
    | _,  _ => false
    end.

    Fixpoint applies_to_query (p : pred Query) (q : @Query Name Vals) :=
     match q with
    | SelectionSet ϕ ϕ' => if p ϕ then true else applies_to_query p ϕ'
    | _ => p q
    end.

    (*
    Inductive NonRedundant : Query -> Prop :=
    | NR_Field : forall name args, NonRedundant (SingleField name args)
                                         
    | NR_LabeledField : forall label name args, NonRedundant (LabeledField label name args)
                                                        
    | NR_NestedField : forall name args ϕ,
        NonRedundant ϕ ->
        NonRedundant (NestedField name args ϕ)
                     
    | NR_NestedLabeledField : forall label name args ϕ,
        NonRedundant ϕ ->
        NonRedundant (NestedLabeledField label name args ϕ)
                     
    | NR_InlineFragment : forall t ϕ,
        NonRedundant ϕ ->
        NonRedundant (InlineFragment t ϕ)
                     
  | NR_SelectionSet : forall ϕ ϕ',
      ~~ (applies_to_query (partial_query_eq ϕ) ϕ') ->
      NonRedundant ϕ ->
      NonRedundant ϕ' ->
      NonRedundant (SelectionSet ϕ ϕ')
    .
     *)
    
    Definition is_non_redundant query : bool :=
      let flattened_query := flatten_query query in
      let fix loop q :=
          match q with
          | SingleField _ _ => true
          | LabeledField _ _ _ => true
          | NestedField _ _ ϕ => loop ϕ
          | NestedLabeledField _ _ _ ϕ => loop ϕ
          | InlineFragment _ ϕ => loop ϕ 
          | SelectionSet ϕ ϕ' => ~~(applies_to_query (partial_query_eq ϕ) ϕ') &&
                                  loop ϕ &&
                                  loop ϕ'
          end
      in
      loop flattened_query.



    Structure normalizedQuery := NormalQuery {
                                    query : Query;
                                    _ : is_non_redundant query;
                                    _ : is_ground_typed_normal_form query
                              }.

    Coercion query_of_normalized_query (q : normalizedQuery) := let: NormalQuery q _ _ := q in q.



    Implicit Type schema : @wfSchema Name Vals.
    

    Fixpoint normalize_query (query : wfQuery) : Query :=
      let: WFQuery q _ := query in
      let flattened_query := flatten_query q in
      let fix aux q := 
          match q with
          | SingleField _ _ => q
          | LabeledField _ _ _ => q
          | NestedField n args ϕ => NestedField n args (aux ϕ)
          | NestedLabeledField l n args ϕ => NestedLabeledField l n args (aux ϕ)
          | InlineFragment t ϕ => 
            
          end
      in
      aux flattened_query.

End NRGTNF.