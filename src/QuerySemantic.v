From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import SchemaWellFormedness.
Require Import Conformance.
Require Import QueryConformance.
Require Import SchemaAux.

Require Import Query.
Require Import Graph.
Require Import Schema.



Section QuerySemantic.

  Variables N Name Vals : finType.

  Inductive eval (schema : @wfSchema Name Vals) (graph : @conformedGraph N Vals Name schema) : @Query Name Name Name Vals  -> @ResponseObject Name Vals  -> Prop :=
  | EvField : forall (u : N) (f : fld) (value : Vals),
      (λ graph) (u, f) = Some (inl value) ->
      SelectionConforms schema (SingleField (label f) (args f)) ((τ graph) u) ->
      eval graph (SingleField (label f) (args f)) (SingleResult (label f) value)

  | EvNullField : forall (u : N) (f : fld),
      (λ graph) (u, f) = None ->
      eval graph (SingleField (label f) (args f)) (Null (label f))

  | EvLabeledField :  forall (u : N) (f : fld) (value : Vals) (l : Name),
      (λ graph) (u, f) = Some (inl value) ->
      SelectionConforms schema (LabeledField l (label f) (args f)) ((τ graph) u) ->
      eval graph (LabeledField l (label f) (args f)) (SingleResult (label f) value)

  | EvNullLabeledField :  forall (u : N) (f : fld) (l : Name),
      (λ graph) (u, f) = None ->
      eval graph (LabeledField l (label f) (args f)) (Null (label f))
(*
  | EvNestedListField :

  | EvNestedField :

  | EvNullNestedField :

  | EvNestedLabeledListField :

  | EvNestedLabeledField :

  | EvNullNestedLabeledField : *)

  | EvInlineFragment : forall (u : N) (t : Name) (ϕ : Query),
      ((isObjectType schema (NamedType t)) && (((τ graph) u) == t)) ||
       ((isInterfaceType schema (NamedType t)) && (declaresImplementation schema t ((τ graph) u)))  ->
       eval graph (InlineFragment t ϕ) (Null t)
    .


End QuerySemantic.