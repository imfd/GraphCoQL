From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From CoqUtils Require Import string.
Require Import Base.

Section Schema.

 
  Section TypeSystem.

    
    (** *** Argument for a field.

        In the specification it is named "InputValue" (InputValueDefinition) but 
        it is not very descriptive of what it is. Besides, it is constantly refered 
        as "argument", therefore it is here named as FieldArgument (only fields can have
        arguments so it may sound redundant to name it like this but I feel like it is
        more descriptive and reinforces this notion). 

        https://graphql.github.io/graphql-spec/June2018/#sec-Field-Arguments
     **)
    Structure FieldArgumentDefinition := FieldArgument {
                                            argname : Name;
                                            argtype : type
                                          }.


       
    (** Packing and unpacking of a field argument, needed for canonical instances **)
    Definition prod_of_arg (arg : FieldArgumentDefinition) := let: FieldArgument n t := arg in (n, t).
    Definition arg_of_prod (p : prod Name type) := let: (n, t) := p in FieldArgument n t.

    (** Cancelation lemma for field arguments **)
    Lemma prod_of_argK : cancel prod_of_arg arg_of_prod.  Proof. by case. Qed.
  
    Canonical arg_eqType := EqType FieldArgumentDefinition (CanEqMixin prod_of_argK).
    Canonical arg_choiceType := ChoiceType FieldArgumentDefinition (CanChoiceMixin prod_of_argK).



    
    (** *** Field of an object or interface in the schema. 
        Represents a leaf or an edge between nodes of the underlying tree structure.

        https://graphql.github.io/graphql-spec/June2018/#FieldsDefinition
     **)
    Structure FieldDefinition := Field {
                                    fname : Name;
                                    fargs : seq FieldArgumentDefinition;
                                    return_type : type
                                  }.


    
    (** Packing and unpacking of a field, needed for canonical instances **)
    Definition prod_of_field (f : FieldDefinition) := let: Field n args t := f in (n, args, t).
    Definition field_of_prod (p : Name * (seq FieldArgumentDefinition) * type)  := let: (n, args, t) := p in Field n args t.

    (** Cancelation lemma for a field **)
    Lemma prod_of_fieldK : cancel prod_of_field field_of_prod. Proof. by case. Qed.

    
    Canonical field_eqType := EqType FieldDefinition (CanEqMixin prod_of_fieldK).
    Canonical field_choiceType := ChoiceType FieldDefinition (CanChoiceMixin prod_of_fieldK).

 

    
  
    (** *** Type Definition 

        Possible type definitions one can make in a GraphQL service.

        Some observations:

        1. Objects and Union types are defined with "NamedType" in the list of implemented
           interfaces and members, respectively. Because NamedType is defined only as a Name,
           we directly use this instead (https://graphql.github.io/graphql-spec/June2018/#NamedType).

        2. Fields: Objects and interfaces must declare at least one field but the current
           definition allows an empty list of fields. In the wf property it is checked that
           this list is not empty.

        3. InputObjects: Currently not included in the formalization.


        https://graphql.github.io/graphql-spec/June2018/#TypeDefinition
     **)

    Inductive TypeDefinition : Type :=
    | ScalarTypeDefinition (scalar_name : Name)
                           
    | ObjectTypeDefinition (object_name : Name)
                           (interfaces : seq Name)
                           (fields : seq FieldDefinition)
                           
    | InterfaceTypeDefinition (interface_name : Name)
                              (fields : seq FieldDefinition)
                              
    | UnionTypeDefinition (union_name : Name)
                          (union_members : seq Name)
                          
    | EnumTypeDefinition (enum_name : Name)
                         (enum_members : seq EnumValue).
    

  

  
    (** Packing and unpacking of a type definition, needed for canonical instances **)
    Notation tdefRep := (Name + (Name * (seq Name) * seq FieldDefinition) + (Name * seq FieldDefinition) +
                        (Name * (seq Name)) + (Name * (seq EnumValue)))%type.

    
    Definition tdef_rep tdef : tdefRep :=
      match tdef with 
      | ScalarTypeDefinition name => inl (inl (inl (inl name)))
      | ObjectTypeDefinition name intfs flds => inl (inl (inl (inr (name, intfs, flds))))
      | InterfaceTypeDefinition name flds => inl (inl (inr (name, flds)))
      | UnionTypeDefinition name mbs => inl (inr (name, mbs))
      | EnumTypeDefinition name enums => inr (name, enums)
      end.

    Definition tdef_con (trep : tdefRep) : TypeDefinition :=
      match trep with
      | inl (inl (inl (inl name))) => ScalarTypeDefinition name
      | inl (inl (inl (inr (name, intfs, flds)))) => ObjectTypeDefinition name intfs flds
      | inl (inl (inr (name, flds))) => InterfaceTypeDefinition name flds
      | inl (inr (name, mbs)) => UnionTypeDefinition name mbs
      | inr (name, enums) => EnumTypeDefinition name enums
      end.

    (** Cancelation lemma for a type definition **)
    Lemma tdef_repK : cancel tdef_rep tdef_con.
    Proof. by case. Qed.

    
    Canonical tdef_eqType := EqType TypeDefinition (CanEqMixin tdef_repK).
    Canonical tdef_choiceType := ChoiceType TypeDefinition (CanChoiceMixin tdef_repK).

    
    
      
    (** *** Schema Definition 

        There is some name clashing when the spec refers to a schema, by which it can
        refer to:
        1.- The type system of the GraphQL service.
        2.- The root operation types (Query, Mutation, Subscription).
        3.- Both.
 
        As per the spec:
       
        > A GraphQL service’s collective type system capabilities are referred to as
          that service’s “schema”. A schema is defined in terms of the types and 
          directives it supports as well as the root operation types for each kind of
          operation: query, mutation, and subscription [...]

        In this formalisation we take this latter approach, in which a schema is both 
        the root operations as well as the types defined. Some observations:
        
        1. Only the Query type is included as root operation (Mutation and Subscription are not).
        
        
        https://graphql.github.io/graphql-spec/June2018/#sec-Schema
    *)
    Structure graphQLSchema := GraphQLSchema {
                                  query_type : Name;
                                  type_definitions : seq TypeDefinition
                                }.
    
    (* Definition fun_of_schema sch := fun p => sch.(type_definitions) p. *)

    (* Coercion fun_of_schema : graphQLSchema >-> Funclass. *)

    (** Packing and unpacking of a schema **)
    Definition prod_of_schema (s : graphQLSchema) := let: GraphQLSchema q tdefs := s in (q, tdefs).
    Definition schema_of_prod p := let: (q, tdefs) := p in GraphQLSchema q tdefs.

    (** Cancelation lemma for a schema **)
    Lemma prod_of_schemaK : cancel prod_of_schema schema_of_prod.  Proof. by case. Qed.
 
    Canonical schema_eqType := EqType graphQLSchema (CanEqMixin prod_of_schemaK).
    Canonical schema_choiceType := ChoiceType graphQLSchema (CanChoiceMixin prod_of_schemaK).


    
  End TypeSystem.
    
    
End Schema.




Delimit Scope schema_scope with SCHEMA.
Open Scope schema_scope.

Notation "argname : ty" := (FieldArgument argname ty) : schema_scope.
Notation "fname '(' args ')' ':' ty" := (Field fname args ty) (at level 50) : schema_scope.


Notation "'Scalar' scalar_name" := (ScalarTypeDefinition scalar_name) (at level 0) : schema_scope.

Notation "'Object' object_name 'implements' interfaces '{' fields '}'" :=
  (ObjectTypeDefinition object_name interfaces fields)
    (object_name at next level, interfaces at next level, fields at next level) : schema_scope.

Notation "'Interface' interface_name '{' fields '}'" :=
  (InterfaceTypeDefinition interface_name fields)
  (interface_name at next level, fields at next level) : schema_scope.

Notation "'Union' union_name '{' union_members '}'" :=
  (UnionTypeDefinition union_name union_members)
  (union_name at next level, union_members at next level) : schema_scope.

Notation "'Enum' enum_name '{' enum_members '}'" :=
  (EnumTypeDefinition enum_name enum_members)
  (enum_name at next level, enum_members at next level) : schema_scope.