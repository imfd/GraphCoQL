From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From extructures Require Import ord fmap.

Section Query.


  Variables S Vals : ordType.
  
  Inductive Query : Type :=
  | SingleField : S -> {fmap S -> Vals} -> Query
  | LabeledField : S -> S -> {fmap S -> Vals} -> Query
  | NestedField : S -> {fmap S -> Vals} -> Query -> Query
  | NestedLabeledField : S -> S -> {fmap S -> Vals} -> Query -> Query
  | InlineFragment : S -> Query -> Query
  | SelectionSet : Query -> Query -> Query.


  Inductive ResponseObject : Type :=
  | Empty : ResponseObject
  | Null : S -> ResponseObject
  | SingleResult : S -> Vals -> ResponseObject
  | ListResult : S -> list Vals -> ResponseObject
  | NestedResult : S -> ResponseObject -> ResponseObject
  | NestedListResult : S -> list ResponseObject -> ResponseObject
  | ResponseList : ResponseObject -> ResponseObject -> ResponseObject.


  
End Query.

Arguments Query [S Vals].
Arguments SingleField [S Vals].
Arguments LabeledField [S Vals].
Arguments NestedField [S Vals].
Arguments NestedLabeledField [S Vals].
Arguments InlineFragment [S Vals].
Arguments SelectionSet [S Vals].

Arguments Null [S Vals].