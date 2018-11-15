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
      SelectionConforms schema ϕ ty ->
      SelectionConforms schema (NestedField fname α ϕ) (NamedType tname)
                        
  | NestedLabeledFieldConforms : forall tname fname α ϕ args ty label,
      lookupField schema tname fname = Some (Field fname args ty) ->
      argumentsConform schema α args ->
      SelectionConforms schema ϕ ty ->
      SelectionConforms schema (NestedLabeledField label fname α ϕ) (NamedType tname)
                        
  | InlineFragmentConforms : forall ty ty' ϕ,
      isObjectType schema ty || isInterfaceType schema ty || isUnionType schema ty -> 
      subtype schema ty ty' ->
      SelectionConforms schema ϕ ty ->
      SelectionConforms schema (InlineFragment ty ϕ) ty'
                        
  | SelectionSetConforms : forall ϕ ϕ' ty,
      SelectionConforms schema ϕ' ty ->
      SelectionConforms schema ϕ ty ->
      SelectionConforms schema (SelectionSet ϕ ϕ') ty 
  .


  (*
  Record wfQuery (schema : @wfSchema Name Vals) := WFQuery {
                              query : Query;
                              queryConforms : SelectionConforms schema query (root schema)
                            }.


  Coercion query_from_wf_query (q : wfQuery schema) := let: WFQuery q' _ := q in q'.
   *)
  
End QueryConformance.