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
    
    We will progressively define predicates that check if a structure is well-formed
    and from them build up to ultimately define a well-formed GraphQL Schema, which will 
    be the collection of predicates defined previously.  

    This predicates will validate arguments, fields, implementations of objects, and so on.

 *)

(** ---- *)

Section WellFormedness.

  Variables (Vals : eqType).

  
  Section Defs.
    
    Variable (s : graphQLSchema).

     
    
    (** *** Valid argument's type

       The following predicate checks whether a given type is valid for a field argument.
       
       This is necessary when checking that an Object or Interface type is well-formed.

        
       #<div class="hidden-xs hidden-md hidden-lg"><br></div>#

       **** Observations:
       - IsInputType : This predicate is named "IsInputType" in the spec but here it is renamed to make it more clear
         that it is a check on the argument's type.

       - InputObject : The spec allows the Input Object type as well as the
         scalar and enum types, but since we are not currently implementing it, 
         we discard it in this definition.

       - Non-Null type : Similarly as the previous point.

       #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
       **** Spec Reference
       - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Input-and-Output-Types'>Input and Output Types</a># 
       - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Field-Arguments'>Field Arguments</a>#
        - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Objects'>Objects (Section 'Type Validation') </a>#
        - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Interfaces'>Interfaces (Section 'Type Validation')</a># 
    *)
    Equations is_valid_argument_type (ty : type) : bool :=
      {
        is_valid_argument_type [ ty ] := is_valid_argument_type ty;
        is_valid_argument_type (NamedType name) := is_scalar_type s name || is_enum_type s name
      }.


    (** ---- *)
    (** *** Valid field's return type 
        
        The following predicate checks whether a given type is valid for a field's return type.
        
        This is necessary when checking that an Object or Interface type is well-formed.

        #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
        **** Observations:
        - IsOutputType : This predicate is named "IsOutputType" in the spec but here it is renamed to make it more clear
          that it is a check on the field's return type.

        - InputObject : The spec does not allow Input Object type to be
           a valid return type but since we are not implementing it, we
           simply ignore it. This allows for every other type to be a valid
           return type (as long as it is declared in the Schema).

        #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
        **** Spec Reference
        - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Input-and-Output-Types'>Input and Output Types</a>#
        - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Objects'>Objects (Section 'Type Validation') </a>#
        - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Interfaces'>Interfaces (Section 'Type Validation')</a># 
    *)
    Equations is_valid_field_type (ty : type) : bool :=
      {
        is_valid_field_type [ ty ] := is_valid_field_type ty;
        is_valid_field_type (NamedType name) := is_declared s name
      }.
    

    (** ---- *)
    (** *** Well-formed Argument

      The following predicate checks whether an argument definition is well-formed.
      This is done simply by checking that its type is a valid type for an argument. 

      This check is necessary when checking that an Object or Interface type is well-formed.

      #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
      **** Observations:
      - Introspection : There is no check as to whether the argument's name 
         begins with '__' because introspection is not implemented in this 
         formalisation.

      #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
      **** Spec Reference
      - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Field-Arguments'>Field Arguments</a>#
      - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Objects'>Objects (Section 'Type Validation') </a>#
      - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Interfaces'>Interfaces (Section 'Type Validation')</a># 
     *)
    Definition is_wf_field_argument (arg : FieldArgumentDefinition) : bool :=
      is_valid_argument_type arg.(argtype).


    (** ---- *)
    (** *** Well-formed Field

     The following predicate checks whether a field is well-formed. This is done by
     checking the following things:
     - It's return type is valid.
     - There are no two arguments with the same name.
     - All of its arguments are well-formed.

     
     #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
     **** Observations:
     - Introspection : There is no check as to whether the argument's name 
         begins with '__' because introspection is not implemented in this 
         formalisation.
     - Argument's uniqueness : We could not find a reference in the spec
        stating whether it is valid or not to have repeated arguments
        but we are including this notion in this definition (although there is
        one when checking the validity of a query).
               
    *)
    Definition is_wf_field (fld : FieldDefinition) : bool :=
      [&& is_valid_field_type fld.(return_type),
          uniq [seq arg.(argname) | arg <- fld.(fargs)] &  (* Not currently in the spec *)
          all is_wf_field_argument fld.(fargs)].


    (** ---- *)
    (** *** Valid field implementation

    This checks whether a field is valid w/r to another. This is used to check 
    whether an Object type is correctly implementing an interface's fields.
    
    It checks the following:
      1. Both fields have the same name.
      2. The arguments of the interface field must be a subset of the object's arguments
         (the types of the arguments are invariant, therefore we can simply check that it's a subset).
      3. The object's field return type must be a subtype of the interface's field.

     
    Observations:
    1. Non-null extra arguments : The spec requires that any additional argument included in the object's
       field must not be of a non-null type. Since we do not implement non-null types, we are not including 
       this check. 
    2. J&O : In Jorge and Olaf's paper, there is no check regarding arguments between an object 
       type and its interface.

      https://graphql.github.io/graphql-spec/June2018/#sec-Objects (Section 'Type Validation')
    *)
    Definition is_valid_field_implementation (object_field interface_field : FieldDefinition) : bool :=
      [&& object_field.(fname) == interface_field.(fname),
          all (mem object_field.(fargs)) interface_field.(fargs) & 
          s ⊢ object_field.(return_type) <: interface_field.(return_type)].
    
	


    (** ---- *)
    (** *** Valid interface implementation

     This checks whether an object type correctly implements an interface, 
     by properly implementing every field defined in the interface.
     Using Schema as the lookup function in the schema (Schema : Name -> TypeDefinition).


            Schema(O) = type O implements ... I ... { Flds }   
                    Schema(I) = interface I { Flds' }
      ∀ ifld ∈ Flds', ∃ ofld ∈ Flds s.t ofld is_valid_field_implementation ifld
            ------------------------------------------------
                        O implements_correctly I


     Observations:
     1. Implementation : From an implementation point of view, this definition might seem
        a bit redundant (considering its posterior use). For the moment it is left here 
        for readibility purposes.
     *)
    Definition implements_interface_correctly (object_type interface_type : Name) : bool :=
      let interface_fields := fields s interface_type in
      let object_fields := fields s object_type in
      all (fun ifld => has (fun ofld => is_valid_field_implementation ofld ifld) object_fields) interface_fields.
    

    
    (** ---- *)
    (** ** TypeDefinition Well-formedness
        Using Schema as the lookup function in the schema (Schema : Name -> TypeDefinition).


                       Schema(S) = scalar S 
                       -----------------------
                           scalar S is_wf_type_def


                 Schema(O) = Object O implements Intfs { Flds }
                           Flds ≠ ∅
                           Flds are_unique
                    ∀ field ∈ Flds, field is_wf_field
                           Intfs are_unique
                  ∀ intf ∈ Intfs, S(intf) = interface intf { ... }
                  ∀ intf ∈ Intfs, O implements_interface_correctly intf 
                -----------------------------------------
                  Object O implements Intfs { Flds } is_wf_type_def



                    Schema(I) = interface I { Flds }
                           Flds ≠ ∅
                          Flds are_unique
                         ∀ field ∈ Flds, field is_wf_field
                ----------------------------------------
                        interface I { Flds }  is_wf_type_def



                       Schema(U) = union U { Mbs }
                           Mbs ≠ ∅
                         Mbs are_unique
                     ∀ mb ∈ Mbs, Schema(mb) = Object mb implements ... { ... }
                -----------------------------------------
                          union U { Mbs } is_wf_type_def


                       Schema(E) = enum E { Evs }
                           Evs ≠ ∅
                          Evs are_unique
                -----------------------------------------
                          enum E { Evs } 



     Observations:
     1. Enums : The spec does not specify whether the enum members must be different from 
        other defined types in the schema (eg. Object type 'Human' cannot be part of a 
        defined Enum type).
     

     https://graphql.github.io/graphql-spec/June2018/#sec-Scalars
     https://graphql.github.io/graphql-spec/June2018/#sec-Objects (Section 'Type Validation')
     https://graphql.github.io/graphql-spec/June2018/#sec-Interfaces (Section 'Type Validation')
     https://graphql.github.io/graphql-spec/June2018/#sec-Unions (Section 'Type Validation')
     https://graphql.github.io/graphql-spec/June2018/#sec-Enums (Section 'Type Validation')
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
            all (implements_interface_correctly name) interfaces]
 
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

