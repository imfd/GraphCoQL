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

  (** * Well-formedness predicates
      ----

      In this section we define the predicates necessary to establish the well-formedness
      of a GraphQL Schema 
   *)
  
  Section Defs.
    
    Variable (s : graphQLSchema).

   

    (** ** Well-formed Argument
        (cf. 
        #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Objects'><span>&#167;</span>3.6</a>#,
        #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Interfaces'><span>&#167;</span>3.7</a>#-Type validation)
        ----

      The following predicate checks whether an argument definition is well-formed.
      This is done by simply checking that its type is a valid type for an argument (cf. #https://graphql.github.io/graphql-spec/June2018/##IsInputType()'><span>&#167;</span>3.4.2</a>#). 

      This check is necessary when checking that an Object or Interface type is well-formed.
     *)
    Definition is_a_wf_field_argument (arg : FieldArgumentDefinition) : bool :=
      let fix is_valid_argument_type (ty : type) : bool :=
          match ty with
          | ListType ty' => is_valid_argument_type ty'
          | NamedType name => is_scalar_type s name || is_enum_type s name
          end
      in
      is_valid_argument_type arg.(argtype).


    
    (** ** Well-formed Field
        (cf. 
        #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Objects'><span>&#167;</span>3.6</a>#,
        #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Interfaces'><span>&#167;</span>3.7</a>#-Type validation)
        ----

     The following predicate checks whether a field is well-formed. This is done by
     checking the following things:
     - Its return type is valid (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##IsOutputType()'><span>&#167;</span>3.4.2</a>#).
     - There are no two arguments with the same name.
     - All of its arguments are well-formed.

     This check is necessary when checking that an Object or Interface are well-formed.
     
     #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
     **** Observations:
     - Arguments's uniqueness : We could not find a reference in the spec
        stating whether it is valid or not to have repeated arguments in a type's field
        but we are including this notion in this definition.
     *)
    Definition is_a_wf_field (fld : FieldDefinition) : bool :=
      let fix is_valid_field_type (ty : type) : bool :=
          match ty with
          | ListType ty' => is_valid_field_type ty'
          | NamedType name => is_declared s name
          end
      in
      [&& is_valid_field_type fld.(ftype),
          uniq [seq arg.(argname) | arg <- fld.(fargs)] &  (* Not currently in the spec *)
          all is_a_wf_field_argument fld.(fargs)].


    
    (** ** Valid interface implementation
        (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Objects'><span>&#167;</span>3.6</a>#-Type validation)
        ----

     The following predicate checks whether an object correctly implements an interface,
     by properly implementing _every_ field defined in the interface.

     For an Object to properly implement an interface field, there must exist a field in the Object type 
     such that:
     - The object's field has the same name as the interface's.
     - The arguments of the interface field must be a subset of the arguments contained in the object's field
       (the types of the arguments are invariant, therefore we can simply check that it's a subset).
     - The object's field return type must be a subtype of the interface's field return type.
     *)
    Definition implements_interface_correctly (object_tdef : TypeDefinition) (interface_type : Name) : bool :=
      match object_tdef, lookup_type s interface_type with
      | object _ implements _ { object_fields }, Some (interface _ { interface_fields }) =>
        all (fun interface_field =>
               has (fun object_field =>
                      [&& object_field.(fname) == interface_field.(fname),
                       all (mem object_field.(fargs)) interface_field.(fargs) & 
                       s ⊢ object_field.(ftype) <: interface_field.(ftype)]
                   ) object_fields
            ) interface_fields
      | _, _ => false
      end.
    

    (** ** Well-formed TypeDefinition
        (cf. 
        #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Objects'><span>&#167;</span>3.6</a>#,
        #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Interfaces'><span>&#167;</span>3.7</a>#,
        #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Unions'><span>&#167;</span>3.8</a>#,
        #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Enums'><span>&#167;</span>3.9</a>#-Type validation)
        ----

        The following predicate checks whether a type definition is _well-formed_, which in turn is used
        when checking that a Schema is _well-formed_.

     **** Observations
     - Enums : The spec does not specify whether the enum members must be different from 
       other defined types in the schema (eg. object type 'Human' cannot be part of a 
       defined Enum type). We follow the same approach.
     
     *)
    Fixpoint is_a_wf_type_def (tdef : TypeDefinition) : bool :=
      match tdef with
      | scalar _ => true
                                   
      | object name implements interfaces { fields } =>
        [&& fields != [::],
            uniq [seq fld.(fname) | fld <- fields],
            all is_a_wf_field fields,
            uniq interfaces,
            all (is_interface_type s) interfaces &
            all (implements_interface_correctly tdef) interfaces]
 
      | interface _ { fields } =>
        [&& fields != [::],
            uniq [seq fld.(fname) | fld <- fields] &
            all is_a_wf_field fields]

      | union name { members } =>
        [&& members != [::],
            uniq members &
            all (is_object_type s) members]

      | enum _ { enumValues } => enumValues != [::]
                                                     
      end.


    (** ** Well-formed Schema 
        ----

        A schema is _well-formed_ if:
        - its root type (is defined and) is an object type,
        - there are no duplicated type names, and
        - every type definition is _well-formed_.
    *)
    Definition is_a_wf_schema : bool :=
      [&& is_object_type s s.(query_type),
          uniq s.(schema_names) &
          all is_a_wf_type_def s.(type_definitions)].


   
  End Defs.
  (**
     This finishes the necessary predicates to establish whether a GraphQL Schema is well-formed. 
     With them in hand we can proceed to define the structure that holds it all together.
   *)
  
  (** * Well-formed GraphQL Schema
      ----

      A well-formed GraphQL Schema is a Schema that satisfies the _well-formedness_ property.
   
   *)
  Record wfGraphQLSchema := WFGraphQLSchema {
                           schema : graphQLSchema;
                           _ : is_a_wf_schema schema;
                         }.

  
  Coercion schema : wfGraphQLSchema >-> graphQLSchema.


End WellFormedness.


(** 
    #<div>
        <a href='GraphCoQL.Schema.html' class="btn btn-light" role='button'> Previous ← Schema  </a>
        <a href='GraphCoQL.Query.html' class="btn btn-info" role='button'>Continue Reading → Query </a>
    </div>#
*)

