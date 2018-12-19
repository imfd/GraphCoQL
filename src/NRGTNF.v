From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From extructures Require Import ord fmap.

Require Import List.

Require Import Query.
Require Import QueryAux.
Require Import SchemaWellFormedness.

Section NRGTNF.

  Variables Name Vals : ordType.
  
  Implicit Type selection : @SelectionSet Name Vals.
  Implicit Type query : @Query Name Vals.

    
  
  Definition is_field_selection query : bool :=
    if query is InlineFragment _ _ then false else true.

  Definition is_inline_fragment query : bool :=
    if query is InlineFragment _ _ then true else false.
  
  
  Inductive GroundTypedNormalForm : SelectionSet -> Prop :=
  | GT_MS_Field : forall queries,
      all is_field_selection queries ->
      Forall qGroundTypedNormalForm queries ->
      GroundTypedNormalForm (Selection queries)
  | GT_MS_Inline : forall queries,
      all is_inline_fragment queries ->
      Forall qGroundTypedNormalForm queries ->
      GroundTypedNormalForm (Selection queries)
                            
  with qGroundTypedNormalForm : Query -> Prop :=
       | GT_Field : forall f args,
           qGroundTypedNormalForm (SingleField f args)

       | GT_LabeledField : forall label f args,
           qGroundTypedNormalForm (LabeledField label f args)

       | GT_NestedField : forall f args ϕ,
           GroundTypedNormalForm ϕ ->
           qGroundTypedNormalForm (NestedField f args ϕ)

       | GT_NestedLabeledField : forall label f args ϕ,
           GroundTypedNormalForm ϕ ->
           qGroundTypedNormalForm (NestedLabeledField label f args ϕ)

       | GT_InlineFragment : forall t ϕ,
           all is_field_selection ϕ ->
           GroundTypedNormalForm (Selection ϕ) ->
           qGroundTypedNormalForm (InlineFragment t (Selection ϕ)).
  

  Fixpoint is_ground_typed_normal_form selection : bool := 
    match selection with
    | Selection queries => ((all is_field_selection queries) || (all is_inline_fragment queries))
                            && (all is_query_in_normal_form queries)
    end
  with is_query_in_normal_form query : bool :=
          match query with
          | NestedField _ _ ϕ => is_ground_typed_normal_form ϕ
          | NestedLabeledField _ _ _ ϕ => is_ground_typed_normal_form ϕ
          | InlineFragment _ (Selection ϕ) => (all is_field_selection ϕ) && (all is_query_in_normal_form ϕ)
          | _ => true
          end.



  


  Fixpoint partial_query_eq (q1 q2 : @Query Name Vals) : bool :=
    match q1, q2 with
    | SingleField name args, SingleField name' args' => (name == name') && (args == args')
    | LabeledField label name args, LabeledField label' name' args' => (label == label') && (name == name') && (args == args')
    | NestedField name args _, NestedField name' args' _ => (name == name') && (args == args')
    | NestedLabeledField label name args _, NestedLabeledField label' name' args' _ =>
      (label == label') && (name == name') && (args == args')
    | InlineFragment t _, InlineFragment t' _ => (t == t')
    | _,  _ => false
    end.

  (*
    Fixpoint applies_to_query (p : pred Query) (q : @Query Name Vals) :=
     match q with
    | SelectionSet ϕ ϕ' => if p ϕ then true else applies_to_query p ϕ'
    | _ => p q
    end.
*)

  Fixpoint no_repeated_query (queries : list Query) : bool :=
     match queries with
        | [::] => true
        | hd :: tl => if has (partial_query_eq hd) tl then
                       false
                     else
                       no_repeated_query tl
     end.
  
  Fixpoint is_non_redundant selection : bool :=
    let: Selection queries := selection in
    (all is_query_non_redundant queries) && (no_repeated_query queries)
                                         
  with is_query_non_redundant q : bool :=
         match q with
         | SingleField _ _ => true
         | LabeledField _ _ _ => true
         | NestedField _ _ ϕ => is_non_redundant ϕ
         | NestedLabeledField _ _ _ ϕ => is_non_redundant ϕ
         | InlineFragment _ ϕ => is_non_redundant ϕ 
         end.
  


    Structure normalizedSelection := NormalizedSelection {
                                    selection : SelectionSet;
                                    _ : is_non_redundant selection;
                                    _ : is_ground_typed_normal_form selection
                              }.

    Coercion selection_of_normalized_selection (s : normalizedSelection) := let: NormalizedSelection s _ _ := s in s.



      


End NRGTNF.