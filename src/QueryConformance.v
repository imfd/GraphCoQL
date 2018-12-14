From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import List.


From extructures Require Import ord fmap.

Require Import Schema.
Require Import SchemaAux.
Require Import Query.
Require Import SchemaWellFormedness.


Section QueryConformance.

  Variables Name Vals : ordType.

  Implicit Type schema : @wfSchema Name Vals.


  Definition argumentConforms schema (α : {fmap Name -> Vals}) (arg : FieldArgumentDefinition) : bool :=
    match arg with
    | (FieldArgument argname ty) => match (α argname) with
                                   | Some value => schema.(hasType) ty value
                                   | _ => false
                                   end
    end.
  

  Definition argumentsConform schema (α : {fmap Name -> Vals}) (args : seq.seq FieldArgumentDefinition) : bool :=
    all (argumentConforms schema α) args.
     

  (*
  Inductive SelectionConforms schema : Query -> type -> Prop :=
  | FieldConforms : forall tname fty fname α args,
      lookup_field_in_type schema (NamedType tname) fname = Some (Field fname args fty) ->
      argumentsConform schema α args ->
      SelectionConforms schema (SingleField fname α) (NamedType tname)
                        
  | LabeledFieldConforms : forall tname fname α args ty label,
      lookup_field_in_type schema tname fname = Some (Field fname args ty) ->
      argumentsConform schema α args ->
      SelectionConforms schema (LabeledField label fname α) (NamedType tname)
                        
  | NestedFieldConforms : forall ty fty fname α ϕ args,
      lookup_field_in_type schema ty fname = Some (Field fname args fty) ->
      argumentsConform schema α args ->
      SelectionConforms schema ϕ fty ->
      SelectionConforms schema (NestedField fname α ϕ) ty
                        
  | NestedLabeledFieldConforms : forall tname fname α ϕ args ty label,
      lookup_field_in_type schema tname fname = Some (Field fname args ty) ->
      argumentsConform schema α args ->
      SelectionConforms schema ϕ (NamedType ty) ->
      SelectionConforms schema (NestedLabeledField label fname α ϕ) (NamedType tname)
                        
  | InlineFragmentConforms : forall ty ty' ϕ,
      is_object_type schema (NamedType ty) || is_interface_type schema (NamedType ty) || is_union_type schema (NamedType ty) -> 
      (exists name, (name \in get_possible_types schema (NamedType ty)) && (name \in get_possible_types schema (NamedType ty'))) ->
      SelectionConforms schema ϕ (NamedType ty) ->
      SelectionConforms schema (InlineFragment ty ϕ) (NamedType ty')
                        
  | SelectionSetConforms : forall ϕ ϕ' ty,
      SelectionConforms schema ϕ ty ->
      SelectionConforms schema ϕ' ty ->
      SelectionConforms schema (SelectionSet ϕ ϕ') ty 
  .

   *)
  
  Fixpoint selection_conforms schema (query : Query) (ty : type) :=
    match query with
    | SingleField fname α => match lookup_field_in_type schema ty fname with
                            | Some (Field fname args ty) => argumentsConform schema α args
                            | _ => false
                            end
    | LabeledField _ fname α =>  match lookup_field_in_type schema ty fname with
                                    | Some (Field fname args ty) => argumentsConform schema α args
                                    | _ => false
                                    end
    | NestedField fname α ϕ =>  match lookup_field_in_type schema ty fname with
                               | Some (Field fname args ty') => argumentsConform schema α args && selection_conforms schema ϕ ty'
                               | _ => false
                               end
    | NestedLabeledField _ fname α ϕ =>  match lookup_field_in_type schema ty fname with
                                        | Some (Field fname args ty') => argumentsConform schema α args && selection_conforms schema ϕ ty'
                                        | _ => false
                                        end
    | InlineFragment t ϕ => if is_object_type schema (NamedType t) || is_interface_type schema (NamedType t) || is_union_type schema (NamedType t) then
                             let possible_t_types := get_possible_types schema (NamedType t) in
                             let possible_ty_types := get_possible_types schema ty in
                             (has (fun x => x \in possible_ty_types) possible_t_types) &&
                               selection_conforms schema ϕ (NamedType t)
                           else
                             false 
    | SelectionSet ϕ => all (fun q => selection_conforms schema q ty) ϕ
    end.

  Definition wf_query_conforms schema (query : @wfQuery Name Vals) (ty : type) :=
    let: WFQuery q _ := query in
    selection_conforms schema q ty.
    
  
  Structure conformedQuery (schema : @wfSchema Name Vals) := ConformedQuery {
                              query : @wfQuery Name Vals;
                              queryConforms : wf_query_conforms schema query schema.(query_root)
                            }.


End QueryConformance.