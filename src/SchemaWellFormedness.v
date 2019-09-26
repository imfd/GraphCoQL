(* begin hide *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

Require Import QString.

Require Import Schema.
Require Import SchemaAux.

(* end hide *)

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">Schema Well-formedness</h1>
        <p class="lead">
         This file contains the necessary definitions to validate 
         when a GraphQL Schema is well-formed. 
        </p>

        <p>
         This notion includes things such as: 
         <ul>
           <li> An object type cannot have empty fields. </li>
           <li> A field's return type must be defined in the Schema. </li>
           <li> Union type must contain existent object types. </li>
           <li> Etc. </li>
         </ul>
        </p>
        <p>
         We will progressively define predicates that check if a structure is well-formed;
    check if an argument is well-formed, then a field, the implementation of an interface, etc.
    From these we will ultimately define a well-formed GraphQL Schema, which will 
    be the collection of the predicates defined previously.  
        </p>
  </div>
</div>#
 *)


Section WellFormedness.

  Variables (Vals : eqType).

  (** * Well-formedness predicates

      In this section we define the predicates necessary to establish the well-formedness
      of a GraphQL Schema 
   *)
  
  Section Defs.
    
    Variable (s : graphQLSchema).

   

    (** ---- *)
    (** ** Well-formed Argument

      The following predicate checks whether an argument definition is well-formed.
      This is done by simply checking that its type is a valid type for an argument. 

      This check is necessary when checking that an Object or Interface type is well-formed.

      #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
      **** Observations:
      - Introspection : There is no check as to whether the argument's name 
         begins with '__' because introspection is not implemented in this 
         formalisation.

      - InputObject : The spec allows the Input Object type as well as the
          scalar and enum types, but since we are not currently implementing it, 
          we discard it in this definition.

      - Non-Null type : Similarly as the previous point.
     *)
    Definition is_wf_field_argument (arg : FieldArgumentDefinition) : bool :=
      let fix is_valid_argument_type (ty : type) : bool :=
          match ty with
          | ListType ty' => is_valid_argument_type ty'
          | NamedType name => is_scalar_type s name || is_enum_type s name
          end
      in
      is_valid_argument_type arg.(argtype).


    
    (** ---- *)
    (** ** Well-formed Field

     The following predicate checks whether a field is well-formed. This is done by
     checking the following things:
     - Its return type is valid.
     - There are no two arguments with the same name.
     - All of its arguments are well-formed.

     This check is necessary when checking that an Object or Interface are well-formed.
     
     #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
     **** Observations:
     - Introspection : There is no check as to whether the argument's name 
         begins with '__' because introspection is not implemented in this 
         formalisation.

     - InputObject : The spec does not allow Input Object type to be
           a valid return type but since we are not implementing it, we
           simply ignore it. This allows for every other type to be a valid
           return type (as long as it is declared in the Schema).

     - Argument's uniqueness : We could not find a reference in the spec
        stating whether it is valid or not to have repeated arguments
        but we are including this notion in this definition (although there is
        one when checking the validity of a query).
     *)
    Definition is_wf_field (fld : FieldDefinition) : bool :=
      let fix is_valid_field_type (ty : type) : bool :=
          match ty with
          | ListType ty' => is_valid_field_type ty'
          | NamedType name => is_declared s name
          end
      in
      [&& is_valid_field_type fld.(return_type),
          uniq [seq arg.(argname) | arg <- fld.(fargs)] &  (* Not currently in the spec *)
          all is_wf_field_argument fld.(fargs)].


    
    (** ---- *)
    (** ** Valid interface implementation

     The following predicate checks whether an object correctly implements an interface,
     by properly implementing _every_ field defined in the interface.

     For an Object to properly implement an interface field, there must exist a field in the Object type 
     such that:
     - The object's field has the same name as the interface's.
     - The arguments of the interface field must be a subset of the arguments contained in the object's field
       (the types of the arguments are invariant, therefore we can simply check that it's a subset).
     - The object's field return type must be a subtype of the interface's field return type.

     OR 
     ∀ interface_field ∈ interface_fields, 
           ∃ object_field ∈ object_fields, 
             object_field.name = interface_field.name ∧
             interface_field.arguments ⊆ object_field.arguments ∧
             object_field.return_type <: interface_field.return_type


     #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
     **** Observations
     - Non-null extra arguments : The spec requires that any additional argument included in the object's
       field must not be of a non-null type. Since we do not implement non-null types, we are not including 
       this check. 
     - Implementation : From an implementation point of view, this definition might seem
        a bit redundant (considering its posterior use). For the moment it is left here 
        for readibility purposes.
     *)
    Definition implements_interface_correctly (object_tdef : TypeDefinition) (interface_type : Name) : bool :=
      match object_tdef, lookup_type s interface_type with
      | Object _ implements _ { object_fields }, Some (Interface _ { interface_fields }) =>
        all (fun interface_field =>
               has (fun object_field =>
                      [&& object_field.(fname) == interface_field.(fname),
                       all (mem object_field.(fargs)) interface_field.(fargs) & 
                       s ⊢ object_field.(return_type) <: interface_field.(return_type)]
                   ) object_fields
            ) interface_fields
      | _, _ => false
      end.
    

    (** ---- *)
    (** ** Well-formed TypeDefinition

        The following predicate checks whether a type definition is well-formed.
        This is used when checking that a Schema is well-formed.
        Later on we will check that there are no duplicated names in the type definitions;
        this predicate only checks for a particular definition and see if it holds by itself.

     **** Observations
     - Enums : The spec does not specify whether the enum members must be different from 
       other defined types in the schema (eg. Object type 'Human' cannot be part of a 
       defined Enum type). We follow the same approach.
     
     *)
    Fixpoint is_wf_type_def (tdef : TypeDefinition) : bool :=
      match tdef with
      | Scalar _ => true
                                   
      | Object name implements interfaces { fields } =>
        [&& fields != [::],
            uniq [seq fld.(fname) | fld <- fields],
            all is_wf_field fields,
            uniq interfaces,
            all (is_interface_type s) interfaces &
            all (implements_interface_correctly tdef) interfaces]
 
      | Interface _ { fields } =>
        [&& fields != [::],
            uniq [seq fld.(fname) | fld <- fields] &
            all is_wf_field fields]

      | Union name { members } =>
        [&& members != [::],
            uniq members &
            all (is_object_type s) members]

      | Enum _ { enumValues } => enumValues != [::]
                                                     
      end.


    (** ---- *)
    (** ** Well-formed Schema 

    The following predicate checks whether a Schema is well-formed.

    *)
    Definition is_wf_schema : bool :=
      [&& is_object_type s s.(query_type),
          uniq s.(schema_names) &
          all is_wf_type_def s.(type_definitions)].


    (**
       This finishes the necessary predicates to establish whether a GraphQL Schema is well-formed. 
       With them in hand we can proceed to define the structure that holds it all together.
     *)
  End Defs.

  
  (** ---- *)
  (** * Well-formed GraphQL Schema

      A well-formed GraphQL Schema is a Schema which satisfies the well-formedness property.
   
   *)
  Record wfGraphQLSchema := WFGraphQLSchema {
                           schema : graphQLSchema;
                           _ : is_wf_schema schema;
                           is_valid_value : type -> Vals -> bool;
                         }.

  
  Coercion schema : wfGraphQLSchema >-> graphQLSchema.


End WellFormedness.


(** 
    #<div>
        <a href='GraphCoQL.Schema.html' class="btn btn-light" role='button'> Previous ← Schema  </a>
        <a href='GraphCoQL.Query.html' class="btn btn-info" role='button'>Continue Reading → Query </a>
    </div>#
*)




Arguments wfGraphQLSchema [Vals].

