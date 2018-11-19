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
     
    
  Inductive SelectionConforms schema : Query -> type -> Prop :=
  | FieldConforms : forall tname fname α args ty,
      lookupField schema tname fname = Some (Field fname args ty) ->
      argumentsConform schema α args ->
      SelectionConforms schema (SingleField fname α) (NamedType tname)
                        
  | LabeledFieldConforms : forall tname fname α args ty label,
      lookupField schema tname fname = Some (Field fname args ty) ->
      argumentsConform schema α args ->
      SelectionConforms schema (LabeledField label fname α) (NamedType tname)
                        
  | NestedFieldConforms : forall tname fname α ϕ args ty,
      lookupField schema tname fname = Some (Field fname args ty) ->
      argumentsConform schema α args ->
      SelectionConforms schema ϕ (NamedType ty) ->
      SelectionConforms schema (NestedField fname α ϕ) (NamedType tname)
                        
  | NestedLabeledFieldConforms : forall tname fname α ϕ args ty label,
      lookupField schema tname fname = Some (Field fname args ty) ->
      argumentsConform schema α args ->
      SelectionConforms schema ϕ (NamedType ty) ->
      SelectionConforms schema (NestedLabeledField label fname α ϕ) (NamedType tname)
                        
  | InlineFragmentConforms : forall ty ty' ϕ,
      isObjectType schema ty || isInterfaceType schema ty || isUnionType schema ty -> 
      (exists name, (name \in get_possible_types schema ty) && (name \in get_possible_types schema ty')) ->
      SelectionConforms schema ϕ (NamedType ty) ->
      SelectionConforms schema (InlineFragment ty ϕ) ty'
                        
  | SelectionSetConforms : forall ϕ ϕ' ty,
      SelectionConforms schema ϕ (NamedType ty) ->
      SelectionConforms schema ϕ' (NamedType ty) ->
      SelectionConforms schema (SelectionSet ϕ ϕ') (NamedType ty) 
  .


  Fixpoint selection_conforms schema (query : Query) (ty : type) :=
    match query with
    | SingleField fname α => match lookupField schema ty fname with
                            | Some (Field fname args ty) => argumentsConform schema α args
                            | _ => false
                            end
    | LabeledField _ fname α =>  match lookupField schema ty fname with
                                    | Some (Field fname args ty) => argumentsConform schema α args
                                    | _ => false
                                    end
    | NestedField fname α ϕ =>  match lookupField schema ty fname with
                               | Some (Field fname args ty') => argumentsConform schema α args && selection_conforms schema ϕ ty'
                               | _ => false
                               end
    | NestedLabeledField _ fname α ϕ =>  match lookupField schema ty fname with
                                        | Some (Field fname args ty') => argumentsConform schema α args && selection_conforms schema ϕ ty'
                                        | _ => false
                                        end
    | InlineFragment t ϕ => if isObjectType schema t || isInterfaceType schema t || isUnionType schema t then
                             let possible_t_types := get_possible_types schema t in
                             let possible_ty_types := get_possible_types schema ty in
                             (has (fun x => x \in possible_ty_types) possible_t_types) &&
                               selection_conforms schema ϕ t
                           else
                             false 
    | SelectionSet ϕ ϕ' => selection_conforms schema ϕ ty && selection_conforms schema ϕ' ty
    end.

    
  
  Structure wfQuery (schema : @wfSchema Name Vals) := WFQuery {
                              query : Query;
                              queryConforms : SelectionConforms schema query (root schema)
                            }.


End QueryConformance.