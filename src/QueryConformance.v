From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Schema.
Require Import SchemaAux.
Require Import Query.
Require Import SchemaWellFormedness.


Section QueryConformance.

  Variables Name Vals : finType.

  Implicit Type schema : @wfSchema Name Vals.


  Definition argumentsConform schema (tname fname : Name) (α : {ffun Name -> Vals}) : Prop :=
    forall arg value ty,
      α arg = value ->
      lookupArgument schema tname fname arg = Some (FieldArgument arg ty) ->
      (hasType schema) ty value.

  Inductive SelectionConforms schema : @Query Name Name Name Vals -> Name -> Prop :=
  | FieldConforms : forall tname fname α args ty,
      lookupField schema tname fname = Some (Field fname args ty) ->
      argumentsConform schema tname fname α ->
      SelectionConforms schema (SingleField fname α) tname
  | LabeledFieldConforms : forall tname fname α args ty label,
      lookupField schema tname fname = Some (Field fname args ty) ->
      argumentsConform schema tname fname α ->
      SelectionConforms schema (LabeledField label fname α) tname
  | NestedFieldConforms : forall tname fname α ϕ args ty,
      lookupField schema tname fname = Some (Field fname args ty) ->
      argumentsConform schema tname fname α ->
      SelectionConforms schema ϕ ty ->
      SelectionConforms schema (NestedField fname α ϕ) tname
  | NestedLabeledFieldConforms : forall tname fname α ϕ args ty label,
      lookupField schema tname fname = Some (Field fname args ty) ->
      argumentsConform schema tname fname α ->
      SelectionConforms schema ϕ ty ->
      SelectionConforms schema (NestedLabeledField label fname α ϕ) tname
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

  Definition QueryConforms schema (q : @Query Name Name Name Vals) : Prop :=
    SelectionConforms schema q (root schema).

  Record wfQuery schema := WFQuery {
                              query : @Query Name Name Name Vals;
                              _ : QueryConforms schema query
                            }.


End QueryConformance.