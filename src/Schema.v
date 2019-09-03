(* begin hide *)
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

(* end hide *)

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">GraphQL Schema</h1>
        <p class="lead">
         This file contains the basic definitions necessary to build a GraphQL Schema. 
        </p>

        <p>
         Some of these are: Type definitions (Objects, Interfaces, etc.), Field definitions and its arguments, amongst others.
        </p>
        <p>
        These definitions allow building a Schema but they do not guarantee that the schema is well-formed.
        This notion of well-formedness is covered in the <a href='GraphCoQL.SchemaWellFormedness.html'>SchemaWellFormedness</a> file.
    
        </p>
  </div>
</div>#
 *)


(** * Schema *)
(** ---- *)
Section Schema.


  (** ** Base types 

      This section includes the basic definition for base types.
   *)
  (** ---- *)
  Section Base.
    
    (** *** Type
        
        Types of data expected by query variables.

        #<div class="hidden-xs hidden-md hidden-lg"><br></div>#

        **** Observations

        - NonNull types are omitted in this current version.
     *)
    Inductive type : Type :=
    | NamedType : Name -> type
    | ListType : type -> type.


    (** ---- *)    
    (** 
        #<strong> tname </strong>#: type → Name 

        Get a type's wrapped name.

        Corresponds to a named type's actual name or the name used in a list type
     *)
    Fixpoint tname (ty : type) : Name :=
      match ty with
      | NamedType name => name
      | ListType ty' => tname ty'
      end.

    
    Coercion tname : type >-> Name.

  End Base.

  (** ** Type System

      In this section we will define the necessary types and structures needed 
      to build a GraphQL Schema. These are:
      - Arguments
      - Fields 
      - Type definition 
      - Schema 
   *)
  (** ---- *)
  Section TypeSystem.

    (** *** Argument Definition

        Arguments are defined for fields in a type (Object or Interface).
        They contain a name and a type.

     *)
    Structure FieldArgumentDefinition := FieldArgument {
                                            argname : Name;
                                            argtype : type
                                          }.


    (** ---- *)
    (** *** Field Definition

        Fields are defined for an Object or Interface type.

        They ultimately represent the things we can query in our system.

    *)
    Structure FieldDefinition := Field {
                                    fname : Name;
                                    fargs : seq FieldArgumentDefinition;
                                    return_type : type
                                  }.


    (** ---- *)
    (** *** Type Definition 

        Possible type definitions one can make in a GraphQL service.

        #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
        **** Observations

        - This definition allows building Schemas which are not correct, such as 
          Schemas where the fields are empty or where an Object type implements 
          types which are not interfaces, amongst others. All these aspects are 
          covered in the well-formedness predicate, which validates the defined 
          schema.

        - InputObjects: Currently not included in the formalization.                         

     *)

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
    

  

    (** ---- *)
    (** *** Schema Definition 

        Here we define the actual structure of a GraphQL Schema, which is made up of:
        - A root type operation for query.
        - A list of type definitions.

        #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
        **** Observations

        - Mutation and Subscription are not currently implemented.
        
    *)
    Structure graphQLSchema := GraphQLSchema {
                                  query_type : Name;
                                  type_definitions : seq TypeDefinition
                                }.
    
    
  End TypeSystem.  
    
End Schema.
(** ---- *)

(** *** Notations
    Just some notations to make it easier to read (or at least closer to how it is in
    the Spec).
 *)


Delimit Scope schema_scope with SCHEMA.
Open Scope schema_scope.

Notation "[ name ]" := (ListType name).

  

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



(** ---- *)

(**
   We also establish that all these structures have a decidable procedure for equality but 
   we omit them here, as they are mostyl bureaucratic things (they may still be seen in the source code).
 *)

(** ---- *)

(** #<a href='GraphCoQL.SchemaWellFormedness.html' class="btn btn-info" role='button'>Continue Reading → Schema Well-Formedness </a># *)



Section Equality.
  (** ** Equality 
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
