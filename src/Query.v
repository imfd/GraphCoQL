From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.



Section Query.


  Variables  F A T Vals : finType.
  
  Inductive Query : Type :=
  | SingleField : F -> {ffun A -> Vals} -> Query
  | LabeledField : F -> F -> {ffun A -> Vals} -> Query
  | NestedField : F -> {ffun A -> Vals} -> Query -> Query
  | NestedLabeledField : F -> F -> {ffun A -> Vals} -> Query -> Query
  | InlineFragment : T -> Query -> Query
  | SelectionSet : Query -> Query -> Query.


  Inductive ResponseObject : Type :=
  | Empty : ResponseObject
  | Null : F -> ResponseObject
  | SingleResult : F -> Vals -> ResponseObject
  | ListResult : F -> list Vals -> ResponseObject
  | NestedResult : F -> ResponseObject -> ResponseObject
  | NestedListResult : F -> list ResponseObject -> ResponseObject
  | ResponseList : ResponseObject -> ResponseObject -> ResponseObject.


  
End Query.

Arguments Query [F] [A] [T] [Vals].
Arguments SingleField [F] [A] [T] [Vals].
Arguments LabeledField [F] [A] [T] [Vals].
Arguments NestedField [F] [A] [T] [Vals].
Arguments NestedLabeledField [F] [A] [T] [Vals].
Arguments InlineFragment [F] [A] [T] [Vals].
Arguments SelectionSet [F] [A] [T] [Vals].