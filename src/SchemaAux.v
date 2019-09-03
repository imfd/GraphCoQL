(* begin hide *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

Require Import String.
Require Import QString.


Require Import Schema.
Require Import SeqExtra.

(* end hide *)

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">GraphQL Schema Auxiliary</h1>
        <p class="lead">
         This file contains auxiliary definitions used with a GraphQL Schema.
        </p>

        <p>
         Some of these are: extractors for type definitions, lookup functions, subtype relation, etc.
        </p>
  </div>
</div>#
 *)


Section SchemaAux.


  Section TypeDefExtractors.
    
    (** *** Extractors for type definitions *)
    
    (** ---- *)
    (** Get type definition's name *)
    Definition tdname tdef : Name :=
      match tdef with
      | Scalar name
      | Object name implements _ { _ }
      | Interface name { _ }
      | Union name { _ }
      | Enum name { _ } => name
      end.

    (** ---- *)
    (** Get type definition's field *)
    Definition tfields tdef : seq FieldDefinition :=
      match tdef with 
      | Object _ implements _ { flds }
      | Interface _ { flds } => flds
      | _ => [::]
      end.

    
    (** ---- *)
    (** Get type definition's declared interfaces *)
    Definition tintfs tdef : seq Name :=
      match tdef with
      | Object _ implements intfs { _ } => intfs
      | _ => [::]
      end.

    
    (** ---- *)
    (** Get type definition's members (only valid for union type) *)
    Definition tmbs tdef : seq Name :=
      match tdef with
      | Union _ { mbs }=> mbs
      | _ => [::]
      end.

    
    (** ---- *)
    (** Get type definition's members (only valid for enum type) *) 
    Definition tenums tdef : seq EnumValue :=
      match tdef with
      | Enum _ { enums } => enums
      | _ => [::]
      end.


    Variable schema : graphQLSchema.

    (** ---- *)
    (** Get all type definitions' names from a schema *)
    Definition schema_names : seq Name := [seq tdef.(tdname) | tdef <- schema.(type_definitions)]. 


  End TypeDefExtractors.
  
  (** ---- *)
  (** *** General purpose predicates *)
  Section Predicates.

    Variable schema : graphQLSchema.

    (** ---- *)
    (** Checks whether the given type definition has the given name *)
    Definition has_name (name : Name) (tdef : TypeDefinition) : bool :=
      name == tdef.(tdname).

    (** ---- *)
    (** Checks whether a given name is declared in the schema, as a type definition *)
    Definition is_declared (name : Name) : bool := name \in schema.(schema_names).


    (** ---- *)
    (** Checks whether the field definition has the given name *)
    Definition has_field_name (name : Name) (fld : FieldDefinition) :=
      name == fld.(fname).

  End Predicates.

  

  
  Variable schema : graphQLSchema.

  (** ---- *)
  (** *** Lookup functions *)
  Section Lookup.

    (** ---- *)
    (**
       Looks up for a type definition with the given name.
     *)
    Definition lookup_type (ty : Name) :=
      get_first (fun tdef => tdef.(tdname) == ty) schema.(type_definitions).
    

    (** ---- *)
    (**
     Gets the first field definition from a given type that matches the given field name. 
     *)
    Definition lookup_field_in_type (ty : Name) (fname : Name) : option FieldDefinition :=
      if lookup_type ty is Some tdef then
        get_first (has_field_name fname) tdef.(tfields)
      else
        None.


    (** ---- *)
    (** 
      Gets the type of the first field definition from a given type that matches the given field name. 
     *)
    Definition lookup_field_type (ty : Name) (fname : Name)  : option type :=
      match lookup_field_in_type ty fname with
      | Some fld => Some fld.(return_type)
      | None => None
      end.


    (** ---- *)
    (**
     Gets the first argument definition that matches the given argument name, from the
     given type and field. 
     *)
    Definition lookup_argument_in_type_and_field (ty : Name) (fname aname : Name) : option FieldArgumentDefinition :=
      match lookup_field_in_type ty fname with
      | Some (Field fname args _) => get_first (fun arg => arg.(argname) == aname) args
      | _ => None
      end.

    (** ---- *)
    (**
       Gets the list of fields declared in an Object or Interface type definition
     *)
    Definition fields (ty : Name) : seq FieldDefinition :=
      match lookup_type ty with
      | Some (Object _ implements _ { flds })
      | Some (Interface _ { flds }) => flds
      | _ => [::]
      end.
    
  End Lookup.


  (** ---- *)
  (** *** Predicates about types *)
  Section TypePredicates.

    (** ---- *)
    (** Checks whether the given type is defined as a Scalar in the Schema *)
    Definition is_scalar_type (ty : Name) : bool :=
      match lookup_type ty with
      | Some (Scalar _) => true
      | _ => false
      end.


    (** ---- *)
    (** Checks whether the given type is defined as an Object in the Schema *)
    Equations is_object_type (ty : Name) : bool :=
      is_object_type ty with lookup_type ty :=
        {
        | Some (Object _ implements _ { _ }) := true;
        | _ := false
        }.


    (** ---- *)
    (** Checks whether the given type is defined as an Interface in the Schema *)
    Equations is_interface_type (ty : Name) : bool :=
      is_interface_type ty with lookup_type ty :=
        {
        | Some (Interface _ { _ }) := true;
        | _ := false
        }.

    
    (** ---- *)
    (** Checks whether the given type is defined as a Union in the Schema *)
    Equations is_union_type (ty : Name) : bool :=
      is_union_type ty with lookup_type ty :=
        {
        | Some (Union _ { _ }) := true;
        | _ := false
        }.


    (** ---- *)
    (** Checks whether the given type is defined as an Enum in the Schema *)
    Definition is_enum_type (ty : Name) : bool :=
      match lookup_type ty with
      | Some (Enum _ { _ }) => true
      | _ => false
      end.


    (** ---- *)
    (** Checks whether the given type is a list type. *)
    Definition is_list_type (ty : type) : bool :=
      match ty with
      | [ ty' ] => true
      | _ => false
      end.

    
    (** ---- *)
    (**
       Checks whether the given type is an abstract type.
     *)
    Definition is_abstract_type (ty : Name) : bool :=
      is_interface_type ty ||  is_union_type ty.


    (** ---- *)
    (**
       Checks whether the given type is a composite type.
     *)
    Definition is_composite_type (ty : Name) : bool :=
      [|| is_object_type ty, is_interface_type ty | is_union_type ty].

    
    (** ---- *)
    (**
       Checks whether the given type is a leaf type.
     *)
    Definition is_leaf_type (ty : Name) : bool :=
      is_scalar_type ty || is_enum_type ty.


    
  End TypePredicates.
  

  (** ---- *)
  (** *** Definitions related to subtyping
      
      This includes the definition of the subtyping relation.
   *)
  Section Subtypes.

    (** ---- *)
    (** *** Subtyping relation.
       
       Some observations:

        - Subtyping is strictly between objects and interfaces.
          There cannot be an object that is subtype of another, as well as an
          interface implementing another interface.

        - Because of the previous limitation, there is no need to specify or worry about transitivity of the relation.
    *)
    Reserved Infix "<:" (at level 60).
    Fixpoint is_subtype (ty ty' : type) : bool :=
      match ty, ty' with
      | NamedType name, NamedType name' => 
        match lookup_type name, lookup_type name' with
        | Some (Scalar name), Some (Scalar name') => name == name'
        | Some (Enum name { _ }), Some (Enum name' { _ }) => name == name'
        | Some (Object name implements _ { _ }), Some (Object name' implements _ { _ }) => name == name'
        | Some (Interface name { _ }), Some (Interface name' { _ }) => name == name'
        | Some (Union name { _ }), Some (Union name' { _ }) => name == name'
        | Some (Object name implements interfaces { _ }), Some (Interface name' { _ }) => name' \in interfaces
        | Some (Object name implements _ { _ }), Some (Union name' { members }) => name \in members
        | _, _ => false
        end

      | ListType ty1, ListType ty2 => (ty1 <: ty2)

      | _, _ => false
      end

    where "ty1 <: ty2" := (is_subtype ty1 ty2).


    (** ---- *)
    (**
       Gets the union's members.
     *)
    Definition union_members (ty : Name) : seq Name :=
      match lookup_type ty with
      | Some (Union _ { mbs }) => mbs
      | _ => [::]
      end.
    
    

    Definition implementation (ty : Name) : seq Name :=
      undup [seq tdef.(tdname) | tdef <- schema.(type_definitions) & ty \in tdef.(tintfs)].

    (** ---- *)
    (**
       Gets "possible" types from a given type, as #<a href='https://graphql.github.io/graphql-spec/June2018/#GetPossibleTypes()'>defined in the GraphQL Spec</a>#.

       If the type is:
       - Object : Possible types are only the type itself.
       - Interface : Possible types are all types that declare implementation of this interface.
       - Union : Possible types are all members of the union.
    
     *)
    Equations get_possible_types (ty : Name) : seq Name :=
      {
        get_possible_types ty with lookup_type ty :=
          {
          | Some (Object _ implements _ { _ }) => [:: ty];
          | Some (Interface iname { _ }) => implementation iname;
          | Some (Union _ { mbs }) => mbs;
          | _ => [::]
          }
      }.


  End Subtypes.
  

  
  
  
End SchemaAux.


Notation "s ⊢ ty1 <: ty2" := (is_subtype s ty1 ty2) (at level 50, ty1 at next level) : schema_scope.
