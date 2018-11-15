From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From extructures Require Import ord fmap.

Require Import Schema.

Section Query.


  Variables Name Vals : ordType.
  
  Inductive Query : Type :=
  | SingleField : Name -> {fmap Name -> Vals} -> Query
  | LabeledField : Name -> Name -> {fmap Name -> Vals} -> Query
  | NestedField : Name -> {fmap Name -> Vals} -> Query -> Query
  | NestedLabeledField : Name -> Name -> {fmap Name -> Vals} -> Query -> Query
  | InlineFragment : @type Name -> Query -> Query
  | SelectionSet : Query -> Query -> Query.   (* seq Query but not empty... *)


  Inductive ResponseObject : Type :=
  | Empty : ResponseObject
  | Null : Name -> ResponseObject
  | SingleResult : Name -> Vals -> ResponseObject
  | ListResult : Name -> list Vals -> ResponseObject
  | NestedResult : Name -> ResponseObject -> ResponseObject
  | NestedListResult : Name -> list ResponseObject -> ResponseObject
  | ResponseList : ResponseObject -> ResponseObject -> ResponseObject.


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
  
  Inductive GroundTypedNormalForm : Query -> Prop :=
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
      (* isObjectType schema t *)
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
  
End Query.

Arguments Query [Name Vals].
Arguments SingleField [Name Vals].
Arguments LabeledField [Name Vals].
Arguments NestedField [Name Vals].
Arguments NestedLabeledField [Name Vals].
Arguments InlineFragment [Name Vals].
Arguments SelectionSet [Name Vals].

Arguments Null [Name Vals].