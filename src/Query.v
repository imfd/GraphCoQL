From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From extructures Require Import ord fmap.

Section Query.


  Variables L Vals : ordType.
  
  Inductive Query : Type :=
  | SingleField : L -> {fmap L -> Vals} -> Query
  | LabeledField : L -> L -> {fmap L -> Vals} -> Query
  | NestedField : L -> {fmap L -> Vals} -> Query -> Query
  | NestedLabeledField : L -> L -> {fmap L -> Vals} -> Query -> Query
  | InlineFragment : L -> Query -> Query
  | SelectionSet : Query -> Query -> Query.   (* seq Query but not empty... *)


  Inductive ResponseObject : Type :=
  | Empty : ResponseObject
  | Null : L -> ResponseObject
  | SingleResult : L -> Vals -> ResponseObject
  | ListResult : L -> list Vals -> ResponseObject
  | NestedResult : L -> ResponseObject -> ResponseObject
  | NestedListResult : L -> list ResponseObject -> ResponseObject
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

Arguments Query [L Vals].
Arguments SingleField [L Vals].
Arguments LabeledField [L Vals].
Arguments NestedField [L Vals].
Arguments NestedLabeledField [L Vals].
Arguments InlineFragment [L Vals].
Arguments SelectionSet [L Vals].

Arguments Null [L Vals].