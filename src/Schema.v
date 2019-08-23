From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import String.
Require Import QString.


Notation Name := string.

(**
     Same as names, except that it can't be true, false or null. 
     Right now it is just the same as Name.

     https://facebook.github.io/graphql/June2018/#EnumValue 
 *)
Notation EnumValue := string.

  
Section Schema.
  
  Section Base.

    
    (** *** Types of data expected by query variables.
        
        - NonNull types are omitted in this current version.
        
        https://graphql.github.io/graphql-spec/June2018/#sec-Type-References

     *)
    Inductive type : Type :=
    | NamedType : Name -> type
    | ListType : type -> type.



    
    (** Get a type's wrapped name.
        Corresponds to a named type's actual name or the name used in a list type

        https://facebook.github.io/graphql/June2018/#sec-Type-References
        https://facebook.github.io/graphql/June2018/#sec-Wrapping-Types **)
    Fixpoint tname (ty : type) : Name :=
      match ty with
      | NamedType name => name
      | ListType ty' => tname ty'
      end.

    Coercion tname : type >-> Name.

  End Base.



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


       
  
    
    (** *** Field of an object or interface in the schema. 
        Represents a leaf or an edge between nodes of the underlying tree structure.

        https://graphql.github.io/graphql-spec/June2018/#FieldsDefinition
     **)
    Structure FieldDefinition := Field {
                                    fname : Name;
                                    fargs : seq FieldArgumentDefinition;
                                    return_type : type
                                  }.


  

    
  
    (** *** Type Definition 

        Possible type definitions one can make in a GraphQL service.

        Some observations:

        1. Objects and Union types are defined with "NamedType" in the list of implemented
           interfaces and members, respectively. Because NamedType is defined only as a Name,
           we directly use this instead (https://graphql.github.io/graphql-spec/June2018/#NamedType). #<br>#

        2. Fields: Objects and interfaces must declare at least one field but the current
           definition allows an empty list of fields. In the wf property it is checked that
           this list is not empty.                                                                    #<br>#

        3. InputObjects: Currently not included in the formalization.                                 #<br>#


        https://graphql.github.io/graphql-spec/June2018/#TypeDefinition
     **)

    Inductive TypeDefinition : Type :=
    | ScalarTypeDefinition (name : Name)
                           
    | ObjectTypeDefinition (name : Name)
                           (interfaces : seq Name)
                           (fields : seq FieldDefinition)
                           
    | InterfaceTypeDefinition (name : Name)
                              (fields : seq FieldDefinition)
                              
    | UnionTypeDefinition (name : Name)
                          (members : seq Name)
                          
    | EnumTypeDefinition (name : Name)
                         (members : seq EnumValue).
    

  

  
    
      
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
    
    
  End TypeSystem.  
    
End Schema.



Section Equality.
  (**
     This section deals with some SSReflect bureaucratic things, in particular 
     establishing that the different components in the schema (type, fields, type definitions, etc.)
     do have a decidable procedure to establish equality between them (they belong to the 
     SSReflect type - eqType).

     This is basically done by establishing isomorphisms between the different structures
     to others that already have a decidable procedure.
   *)

  
  (** 
      The two following functions serve to establish the ismorphism between [type]
      and a tree structure.
   *)
  Fixpoint tree_of_type (ty : type) : GenTree.tree Name :=
    match ty with
    | NamedType n => GenTree.Node 0 [:: GenTree.Leaf n]
    | ListType ty' => GenTree.Node 1 [:: tree_of_type ty']
    end.
  
  Fixpoint type_of_tree (t : GenTree.tree Name) : option type :=
    match t with
    | GenTree.Node 0 [:: GenTree.Leaf n] => Some (NamedType n)
    | GenTree.Node 1 [:: t'] => if (type_of_tree t') is Some ty then
                                 Some (ListType ty)
                               else
                                 None
    | _ => None
    end.


  (**
     This lemma states that effectively both functions establish 
     an isomorphism between [type] and a tree structure.
   *)
  Lemma pcan_tree_of_type : pcancel tree_of_type type_of_tree.
  Proof. by elim=> [| t /= ->]. Qed.


  
  Canonical type_eqType := EqType type (PcanEqMixin pcan_tree_of_type).
  Canonical type_choiceType := ChoiceType type (PcanChoiceMixin pcan_tree_of_type).



  (** Packing and unpacking of a field argument, needed for canonical instances **)
  Definition prod_of_arg (arg : FieldArgumentDefinition) := let: FieldArgument n t := arg in (n, t).
  Definition arg_of_prod (p : prod Name type) := let: (n, t) := p in FieldArgument n t.

  (** Cancelation lemma for field arguments **)
  Lemma prod_of_argK : cancel prod_of_arg arg_of_prod.  Proof. by case. Qed.
  
  Canonical arg_eqType := EqType FieldArgumentDefinition (CanEqMixin prod_of_argK).
  Canonical arg_choiceType := ChoiceType FieldArgumentDefinition (CanChoiceMixin prod_of_argK).


  
  (** Packing and unpacking of a field, needed for canonical instances **)
  Definition prod_of_field (f : FieldDefinition) := let: Field n args t := f in (n, args, t).
  Definition field_of_prod (p : Name * (seq FieldArgumentDefinition) * type)  := let: (n, args, t) := p in Field n args t.

  (** Cancelation lemma for a field **)
  Lemma prod_of_fieldK : cancel prod_of_field field_of_prod. Proof. by case. Qed.

  
  Canonical field_eqType := EqType FieldDefinition (CanEqMixin prod_of_fieldK).
  Canonical field_choiceType := ChoiceType FieldDefinition (CanChoiceMixin prod_of_fieldK).


  
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

  

  
  (** Packing and unpacking of a schema **)
  Definition prod_of_schema (s : graphQLSchema) := let: GraphQLSchema q tdefs := s in (q, tdefs).
  Definition schema_of_prod p := let: (q, tdefs) := p in GraphQLSchema q tdefs.

  (** Cancelation lemma for a schema **)
  Lemma prod_of_schemaK : cancel prod_of_schema schema_of_prod.  Proof. by case. Qed.
  
  Canonical schema_eqType := EqType graphQLSchema (CanEqMixin prod_of_schemaK).
  Canonical schema_choiceType := ChoiceType graphQLSchema (CanChoiceMixin prod_of_schemaK).

  
End Equality.



Delimit Scope schema_scope with SCHEMA.
Open Scope schema_scope.

Notation "[ name ]" := (ListType name).

  
Notation "argname : ty" := (FieldArgument argname ty) : schema_scope.
Notation "fname '(' args ')' ':' ty" := (Field fname args ty) (at level 50) : schema_scope.


Notation "'Scalar' scalar_name" := (ScalarTypeDefinition scalar_name) (at level 0) : schema_scope.

(* Using 'type', as in the spec, clashes with the actual type called 'type'... So I preferred Object instead *)
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