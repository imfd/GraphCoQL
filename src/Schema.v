From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import List.
Import ListNotations.


From Coq Require Import Bool String.


Section Schema.

  (** Names for everything, from operations, fields, arguments, types, etc.

      https://facebook.github.io/graphql/June2018/#sec-Names **)
  Variable Name : finType.


  (** Same as names, except that it can't be true, false or null

      https://facebook.github.io/graphql/June2018/#EnumValue **)
  Definition EnumValue := Name.


  (** Types of data expected by query variables.

      https://facebook.github.io/graphql/June2018/#sec-Type-References **)

  Inductive type : Type :=
  | NamedType : Name -> type
  | ListType : type -> type.



  (** In the specification it is named "InputValue" (InputValueDefinition) but 
      it is not very descriptive of what it is. Besides, it is constantly refered 
      as "argument", therefore it is named as FieldArgument (only fields can have
      arguments so it may sound redundant to name it like this but I feel it is
      more descriptive and reinforces this notion). 

      https://facebook.github.io/graphql/June2018/#sec-Field-Arguments **)
  Inductive FieldArgumentDefinition : Type :=
  | FieldArgument : Name -> type -> FieldArgumentDefinition.


  (** https://facebook.github.io/graphql/June2018/#FieldDefinition **)
  (* Actually, if we are using list of arguments, then a single constructor suffices, right? *)
  Inductive FieldDefinition : Type :=
  | FieldWithoutArgs : Name  -> type -> FieldDefinition
  | FieldWithArgs : Name -> list FieldArgumentDefinition -> type -> FieldDefinition.



  (** Possible type definitions one can make in a GraphQL service. Some observations:

    1. Objects' interfaces: Objects *may* declare one or more implemented interfaces. This is 
    is implemented as a list of <type>, which can be empty or not. As it is, an
    object may declare an interface as a list type (eg. "type A implements [B]"), therefore
    in the wf property there is a check that restricts this declaration to a 
    named type.

    2. Fields: Objects and interfaces must declare at least one field but the current
    definition allows an empty list of fields. In the wf property it is checked that
    this list is not empty.

    3. InputObjects: Currently not included to simplify the formalization.


https://facebook.github.io/graphql/June2018/#TypeDefinition **)

  Inductive TypeDefinition : Type :=
  | ScalarTypeDefinition : Name -> TypeDefinition
  | ObjectTypeDefinition : Name -> list type -> list FieldDefinition -> TypeDefinition
  | InterfaceTypeDefinition : Name -> list FieldDefinition -> TypeDefinition
  | UnionTypeDefinition : Name -> list type -> TypeDefinition
  | EnumTypeDefinition : Name -> list EnumValue -> TypeDefinition.
  

  (** 
      The Schema corresponds to the type system - the collective types defined and a
      reference to the Query type (the entry point for queries).

      This differs from the Schema mentioned in the specification. I believe there is
      some naming clashes when they refer to a Schema:
 
          A GraphQL service’s collective type system capabilities are referred to as
          that service’s “schema”. A schema is defined in terms of the types and 
          directives it supports as well as the root operation types for each kind of
          operation: query, mutation, and subscription [...]

    This description matches the definition given in this file, but one can also define 
    a "schema", which only describes the types for the operations: query, mutation and suscription.



   **)
  (* 
 - Omitting mutations and suscriptions, therefore only leaving query as possible operation
 - Omitting directives for simplicity

As per the spec: Directives provide a way to describe alternate runtime execution and type validation behavior in a GraphQL document. 
   *)
  Definition Schema := (type * list TypeDefinition)%type.



End Schema.

Arguments type [Name].
Arguments FieldArgumentDefinition [Name].
Arguments FieldDefinition [Name].
Arguments TypeDefinition [Name].
Arguments Schema [Name].