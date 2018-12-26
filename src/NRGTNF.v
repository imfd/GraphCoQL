From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From extructures Require Import ord fmap.

Require Import List.

Require Import Query.
Require Import QueryAux.
Require Import SchemaWellFormedness.

Require Import Schema.
Require Import SchemaAux.

Require Import Program.

Section NRGTNF.

  Variables Name Vals : ordType.
  
  Implicit Type query_set : @QuerySet Name Vals.
  Implicit Type query : @Query Name Vals.

    
  
  Definition is_field_query query : bool :=
    if query is InlineFragment _ _ then false else true.

  Definition is_inline_fragment query : bool :=
    if query is InlineFragment _ _ then true else false.
  
  
  Inductive GroundTypedNormalForm : QuerySet -> Prop :=
  | GT_MultipleSelection : forall queries,
      (all is_field_query queries) \/ (all is_inline_fragment queries) ->
      Forall qGroundTypedNormalForm queries ->
      GroundTypedNormalForm (SelectionSet queries)
                            
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
           all is_field_query ϕ ->      (* repeated in next check? *)
           GroundTypedNormalForm (SelectionSet ϕ) ->
           qGroundTypedNormalForm (InlineFragment t (SelectionSet ϕ)).
  

  Fixpoint is_ground_typed_normal_form query_set : bool :=
    let: SelectionSet queries := query_set in
    ((all is_field_query queries) || (all is_inline_fragment queries))
      &&
    (all is_query_in_normal_form queries)
      
  with is_query_in_normal_form query : bool :=
          match query with
          | NestedField _ _ ϕ => is_ground_typed_normal_form ϕ
          | NestedLabeledField _ _ _ ϕ => is_ground_typed_normal_form ϕ
          | InlineFragment _ (SelectionSet ϕ) => (all is_field_query ϕ) && (all is_query_in_normal_form ϕ)
          | _ => true
          end.



  


 

  

  Fixpoint no_repeated_query (queries : list (@Query Name Vals)) : bool :=
     match queries with
        | [::] => true
        | hd :: tl => if has (partial_query_eq hd) tl then
                       false
                     else
                       no_repeated_query tl
     end.

      
  Fixpoint is_non_redundant selection : bool :=
    let: SelectionSet queries := selection in
    (all is_query_non_redundant queries) && (no_repeated_query queries)
                                         
  with is_query_non_redundant query : bool :=
         match query with
         | NestedField _ _ ϕ => is_non_redundant ϕ
         | NestedLabeledField _ _ _ ϕ => is_non_redundant ϕ
         | InlineFragment _ ϕ => is_non_redundant ϕ
         | _ => true
         end.
  


    Structure normalizedSelection := NormalizedSelection {
                                    selection : QuerySet;
                                    _ : is_non_redundant selection;
                                    _ : is_ground_typed_normal_form selection
                              }.

    Coercion selection_of_normalized_selection (s : normalizedSelection) := let: NormalizedSelection s _ _ := s in s.


                                         

    Program Fixpoint normalize_list schema (queries : seq.seq (@Query Name Vals)) {measure (queries_size queries)} : seq.seq Query :=
       match queries with
          | [::] => [::]
          | hd :: tl =>
            match hd with
            | SingleField _ _
            | LabeledField _ _ _ => hd :: normalize_list schema (filter (fun q => ~~(partial_query_eq q hd)) tl)
            | NestedField n α (SelectionSet ϕ) =>
              let collected_subqueries :=
                  (foldr (fun q acc => if q is NestedField n' α' (SelectionSet β) then
                                      if (n == n') && (α == α') then
                                        acc ++ β
                                      else
                                        acc
                                    else
                                      acc)
                         ϕ tl)
              in
              (NestedField n α (SelectionSet (normalize_list schema collected_subqueries))) :: normalize_list schema (filter (fun q => ~~(partial_query_eq q hd)) tl)
            | InlineFragment t (SelectionSet [:: (InlineFragment t' ϕ)]) =>
              (InlineFragment t ϕ) :: normalize_list schema tl
            | InlineFragment t (SelectionSet ϕ) =>
              let norm := normalize_list schema ϕ in
              let possible_types := get_possible_types schema (NamedType t) in
              (map (fun t' => InlineFragment (name_of_type t') (SelectionSet norm)) possible_types) ++ normalize_list schema tl
            | _ => normalize_list schema tl
            end
          end.

    Fixpoint normalize query_set : QuerySet :=
      let fix normalize_list (queries : seq Query) : seq Query :=
          match queries with
          | [::] => [::]
          | hd :: tl =>
            match hd with
            | SingleField l args => hd :: (filter (fun q => q != hd) tl) 
            | LabeledField
            | NestedField
            | NestedLabeledField
            | InlineFragment
            end
          end
      in
      let: SelectionSet queries := query_set in
          SelectionSet (normalize_list queries)

      

End NRGTNF.

Arguments normalizedSelection [Name Vals].