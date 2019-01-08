From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Asymmetric Patterns.

From extructures Require Import ord fmap.

Require Import treeordtype.
Require Import Schema.
Require Import SchemaAux.


Require Import CpdtTactics.


Require Import List.


Section Query.


  Variables Name Vals : ordType.

  Inductive QuerySet : Type :=
  | SingleQuery : Query -> QuerySet
  | SelectionSet : Query -> QuerySet -> QuerySet
  with Query : Type :=
       | SingleField : Name -> {fmap Name -> Vals} -> Query
       | LabeledField : Name -> Name -> {fmap Name -> Vals} -> Query
       | NestedField : Name -> {fmap Name -> Vals} -> QuerySet -> Query
       | NestedLabeledField : Name -> Name -> {fmap Name -> Vals} -> QuerySet -> Query
       | InlineFragment : Name -> QuerySet -> Query.


  Unset Elimination Schemes.
  Inductive Result : Type :=
  | Results : list ResponseObject -> Result
  with ResponseObject : Type :=
       | Null : Name -> ResponseObject
       | SingleResult : Name -> Vals -> ResponseObject
       | ListResult : Name -> list Vals -> ResponseObject
       | NestedResult : Name -> Result -> ResponseObject
       | NestedListResult : Name -> list Result -> ResponseObject.
  
  Set Elimination Schemes.


  Coercion responses_of_result (result : Result) := let: Results rs := result in rs.


  
  

  
End Query.


Arguments QuerySet [Name Vals].
Arguments Query [Name Vals].
Arguments SingleField [Name Vals].
Arguments LabeledField [Name Vals].
Arguments NestedField [Name Vals].
Arguments NestedLabeledField [Name Vals].
Arguments InlineFragment [Name Vals].
Arguments SelectionSet [Name Vals].

Arguments Results [Name Vals].
Arguments ResponseObject [Name Vals].
Arguments Null [Name Vals].
Arguments SingleResult [Name Vals].


