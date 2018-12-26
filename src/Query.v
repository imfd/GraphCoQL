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
  | SelectionSet : list Query -> QuerySet
  with Query : Type :=
       | SingleField : Name -> {fmap Name -> Vals} -> Query
       | LabeledField : Name -> Name -> {fmap Name -> Vals} -> Query
       | NestedField : Name -> {fmap Name -> Vals} -> QuerySet -> Query
       | NestedLabeledField : Name -> Name -> {fmap Name -> Vals} -> QuerySet -> Query
       | InlineFragment : Name -> QuerySet -> Query.

  
  Unset Elimination Schemes.
  Inductive ResponseObject : Type :=
  | Response : list Result -> ResponseObject
  with Result : Type :=
  | Empty : Result
  | Null : Name -> Result
  | SingleResult : Name -> Vals -> Result
  | ListResult : Name -> list Vals -> Result
  | NestedResult : Name -> ResponseObject -> Result
  | NestedListResult : Name -> list ResponseObject -> Result.
  Set Elimination Schemes.

         

  
  

  
End Query.


Arguments QuerySet [Name Vals].
Arguments Query [Name Vals].
Arguments SingleField [Name Vals].
Arguments LabeledField [Name Vals].
Arguments NestedField [Name Vals].
Arguments NestedLabeledField [Name Vals].
Arguments InlineFragment [Name Vals].
Arguments SelectionSet [Name Vals].


Arguments ResponseObject [Name Vals].
Arguments Null [Name Vals].
Arguments Empty [Name Vals].


