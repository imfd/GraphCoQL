(* begin hide *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import String.
Require Import QString.

From extructures Require Import ord fset fmap.

From Equations Require Import Equations.

Require Import Schema.
Require Import SchemaAux.

(* end hide *)


(** * Schema Well-Formedness

    This file contains the necessary definitions to validate 
    when a GraphQL Schema is well-formed. 

    This notion includes things such as: 
    - An object type cannot have empty fields.
    - A field's return type must be defined in the Schema.
    - Union type must contain existent object types.
    - Etc.

    #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
    
    We will progressively define predicates that check if a structure is well-formed;
    check if an argument is well-formed, then a field, the implementation of an interface, etc.
    From these we will ultimately define a well-formed GraphQL Schema, which will 
    be the collection of the predicates defined previously.  

 *)

(** ---- *)

Section WellFormedness.

  Variables (Vals : eqType).

  
  Section Defs.
    
    Variable (s : graphQLSchema).
   

    (** ---- *)
    (** *** Well-formed Argument

      The following predicate checks whether an argument definition is well-formed.
      This is done by simply checking that its type is a valid type for an argument. 

      This check is necessary when checking that an Object or Interface type is well-formed.

      #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
      **** Observations:
      - Introspection : There is no check as to whether the argument's name 
         begins with '__' because introspection is not implemented in this 
         formalisation.

      - IsInputType : The predicate that checks whether the argument type is valid
        is named "IsInputType" in the spec. Here it is renamed to [is_valid_argument_type]
        to make it more clear that it is a check on the argument's type.

        - InputObject : The spec allows the Input Object type as well as the
          scalar and enum types, but since we are not currently implementing it, 
          we discard it in this definition.

        - Non-Null type : Similarly as the previous point.

      #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
      **** Spec Reference
      - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Field-Arguments'>Field Arguments</a>#
      - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Input-and-Output-Types'>Input and Output Types</a>#
      - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Objects'>Objects (Section 'Type Validation') </a>#
      - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Interfaces'>Interfaces (Section 'Type Validation')</a># 
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
    (** *** Well-formed Field

     The following predicate checks whether a field is well-formed. This is done by
     checking the following things:
     - Its return type is valid.
     - There are no two arguments with the same name.
     - All of its arguments are well-formed.

     
     #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
     **** Observations:
     - Introspection : There is no check as to whether the argument's name 
         begins with '__' because introspection is not implemented in this 
         formalisation.
     - IsOutputType : The predicate that checks whether the field's return type is valid
        is named  "IsOutputType" in the spec. Here it is renamed to [is_valid_field_type] 
        to make it more clear that it is a check on the field's return type.

        - InputObject : The spec does not allow Input Object type to be
           a valid return type but since we are not implementing it, we
           simply ignore it. This allows for every other type to be a valid
           return type (as long as it is declared in the Schema).

     - Argument's uniqueness : We could not find a reference in the spec
        stating whether it is valid or not to have repeated arguments
        but we are including this notion in this definition (although there is
        one when checking the validity of a query).


     #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
     **** Spec Reference 
     - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Input-and-Output-Types'>Input and Output Types</a>#
     - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Objects'>Objects (Section 'Type Validation') </a>#
     - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Interfaces'>Interfaces (Section 'Type Validation')</a>#         
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
    (** *** Valid interface implementation

     The following predicate checks whether an object correctly implements an interface,
     by properly implementing _every_ field defined in the interface.

     To properly implement an interface field, there must exist a field in the object type 
     such that:
     - The object's field has the same name as the interface's.
     - The arguments of the interface field must be a subset of the arguments contained in the object's field
       (the types of the arguments are invariant, therefore we can simply check that it's a subset).
     - The object's field return type must be a subtype of the interface's field return type.

     Using Schema as the lookup function in the schema (Schema : Name -> TypeDefinition).




     #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
     **** Observations
     - Non-null extra arguments : The spec requires that any additional argument included in the object's
       field must not be of a non-null type. Since we do not implement non-null types, we are not including 
       this check. 
     - J&O : In Perez & Hartig's paper, there is no check regarding arguments between an object 
       type and its interface. This is posteriorly included in Hartig's and Hidders 
       "Defining Schemas for Property Graphs by using the GraphQL Schema Definition Language" work.
     - Implementation : From an implementation point of view, this definition might seem
        a bit redundant (considering its posterior use). For the moment it is left here 
        for readibility purposes.

     #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
     **** Spec Reference 
     - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Objects'>Objects (Section 'Type Validation') </a>#
    
     *)
    Definition implements_interface_correctly (object_tdef : TypeDefinition) (interface_type : Name) : bool :=
      match object_tdef, lookup_type s interface_type with
      | Object _ implements _ { object_fields }, Some (Interface _ { interface_fields }) =>
        (* ∀ interface_field ∈ interface_fields, 
           ∃ object_field ∈ object_fields, 
             object_field.name = interface_field.name ∧
             interface_field.arguments ⊆ object_field.arguments ∧
             object_field.return_type <: interface_field.return_type 
         *)
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
    (** *** Well-formed TypeDefinition

        The following predicate checks whether a type definition is well-formed.
        This is used when checking that a Schema is well-formed.
        Later on we will check that there are no duplicated names in the type definitions;
        this predicate only checks for a particular definition and see if it holds by itself.

        The rules are the following:
        - Scalar: Nothing to check, scalars are ok by themselves.
        - Object: 
          - Fields are not empty.
          - There are no duplicated field names.
          - Fields are well-formed.
          - There are no duplicated names in the list of implemented interfaces.
          - Names in the list of implemented interfaces are _actually_ defined as interfaces in
            the Schema.
          - Every interface in the list of implemented interfaces is correctly implemented. 
        - Interface:
          - Fields are not empty. 
          - There are no duplicated field names.
          - Fields are well-formed.
        - Union:
          - Members are not empty. 
          - There are no duplicated member names.
          - Every member is _actually_ defined as an Object type in the Schema.
        - Enum:
          - Members are not empty.

                   
     #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
     **** Observations
     - Enums : The spec does not specify whether the enum members must be different from 
       other defined types in the schema (eg. Object type 'Human' cannot be part of a 
       defined Enum type). We follow the same approach.
     
     
     #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
     **** Spec Reference
     - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Scalars'>Scalars</a># 
     - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Objects'>Objects (Section 'Type Validation') </a>#
     - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Interfaces'>Interfaces (Section 'Type Validation')</a>#   
     - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Unions'>Unions (Section 'Type Validation') </a>#
     - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Enums'>Enums (Section 'Type Validation')</a>#
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


    
    (** ** Schema Well-formedness 

    This checks whether a schema is well-formed. 
    1. The Query root operation is actually defined in the schema.

    2. The Query type is an Object type.

    3. Type names are unique. 

    4. Every type definition is well-formed.

    Observations:

    1. J&O : In Jorge and Olaf's paper, they describe a schema as being 'consistent'
       if "every object type that implements an interface type i defines at least all 
       the fields that i defines". Because they work with functions and sets they can 
       simplify some checks about uniqueness of names, etc. Their notion does not capture, 
       I believe, that fields' arguments between an object type and its interface have 
       to satisfy some property (being a subset of the other).
       
    *)
    Definition is_wf_schema : bool :=
      [&& s.(query_type) \in s.(schema_names),      (* This is a bit redundant with the check about Query ∈ Ot *)
          is_object_type s s.(query_type),
          uniq s.(schema_names) &
          all is_wf_type_def s.(type_definitions)].

  End Defs.
  

  (** *** Well-formed Schema

  A well-formed schema is a schema which satisfies the well-formedness property.
  We also include the predicate "has_type", which 
   *)
  Structure wfGraphQLSchema := WFGraphQLSchema {
                           schema : graphQLSchema;
                           has_type :  Name -> Vals -> bool;
                           _ : is_wf_schema schema;
                         }.

  
  Coercion schema : wfGraphQLSchema >-> graphQLSchema.


End WellFormedness.


Arguments wfGraphQLSchema [Vals].

