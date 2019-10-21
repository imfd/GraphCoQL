(* begin hide *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

Require Import String.
Require Import QString.

Require Import Value.

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
      | scalar name
      | object name implements _ { _ }
      | interface name { _ }
      | union name { _ }
      | enum name { _ } => name
      end.

    (** ---- *)
    (** Get type definition's field *)
    Definition tfields tdef : seq FieldDefinition :=
      match tdef with 
      | object _ implements _ { flds }
      | interface _ { flds } => flds
      | _ => [::]
      end.

    
    (** ---- *)
    (** Get type definition's declared interfaces *)
    Definition tintfs tdef : seq Name :=
      match tdef with
      | object _ implements intfs { _ } => intfs
      | _ => [::]
      end.

    
    (** ---- *)
    (** Get type definition's members (empty for anything else than union) *)
    Definition tmbs tdef : seq Name :=
      match tdef with
      | union _ { mbs }=> mbs
      | _ => [::]
      end.

    
    (** ---- *)
    (** Get type definition's members (empty for anything else than enum) *) 
    Definition tenums tdef : seq EnumValue :=
      match tdef with
      | enum _ { enums } => enums
      | _ => [::]
      end.


    Variable schema : graphQLSchema.

    (** ---- *)
    (** Get all type definitions' names from a schema *)
    Definition type_names : seq Name := [seq tdef.(tdname) | tdef <- schema.(type_definitions)]. 


  End TypeDefExtractors.
  
  (** *** General purpose predicates *)
  (** ---- *)
  Section Predicates.

    Variable schema : graphQLSchema.

    (** ---- *)
    (** Checks whether the given type definition has the given name *)
    Definition has_name (name : Name) (tdef : TypeDefinition) : bool :=
      name == tdef.(tdname).

    (** ---- *)
    (** Checks whether a given name is declared in the schema, as a type definition *)
    Definition is_declared (name : Name) : bool := name \in schema.(type_names).


    (** ---- *)
    (** Checks whether the field definition has the given name *)
    Definition has_field_name (name : Name) (fld : FieldDefinition) :=
      name == fld.(fname).

  End Predicates.

  

  
  Variable schema : graphQLSchema.

  (** *** Lookup functions *)
  (** ---- *)
  Section Lookup.

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
      | Some fld => Some fld.(ftype)
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
       Gets the list of fields declared in an object or interface type definition
     *)
    Definition fields (ty : Name) : seq FieldDefinition :=
      match lookup_type ty with
      | Some (object _ implements _ { flds })
      | Some (interface _ { flds }) => flds
      | _ => [::]
      end.
    
  End Lookup.


  (** *** Predicates about types *)
  (** ---- *)
  Section TypePredicates.

    (** ---- *)
    (** Checks whether the given type is defined as a scalar in the Schema *)
    Definition is_scalar_type (ty : Name) : bool :=
      match lookup_type ty with
      | Some (scalar _) => true
      | _ => false
      end.


    (** ---- *)
    (** Checks whether the given type is defined as an object in the Schema *)
    Equations is_object_type (ty : Name) : bool :=
      is_object_type ty with lookup_type ty :=
        {
        | Some (object _ implements _ { _ }) := true;
        | _ := false
        }.


    (** ---- *)
    (** Checks whether the given type is defined as an interface in the Schema *)
    Equations is_interface_type (ty : Name) : bool :=
      is_interface_type ty with lookup_type ty :=
        {
        | Some (interface _ { _ }) := true;
        | _ := false
        }.

    
    (** ---- *)
    (** Checks whether the given type is defined as a union in the Schema *)
    Equations is_union_type (ty : Name) : bool :=
      is_union_type ty with lookup_type ty :=
        {
        | Some (union _ { _ }) := true;
        | _ := false
        }.


    (** ---- *)
    (** Checks whether the given type is defined as an enum in the Schema *)
    Definition is_enum_type (ty : Name) : bool :=
      match lookup_type ty with
      | Some (enum _ { _ }) => true
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

  (** *** Predicates about types *)
  (** ---- *)
  Section ValuePredicates.
    
    Variables (Scalar : eqType)
              (s : graphQLSchema)
              (is_valid_scalar_value : graphQLSchema -> Name -> Scalar -> bool).

    (** ---- *)
    (**
       Checks whether the given value matches the expected type in the schema. 
       To determine scalar values, the [is_valid_scalar_value] predicate must be 
       provided.
     *)
    Equations is_valid_value (ty : type) (value : @Value Scalar) : bool :=
      {
        is_valid_value (NamedType n) (SValue value) := is_valid_scalar_value s n value;
        is_valid_value (ListType wty) (LValue ls) := all (is_valid_value wty) ls;
        is_valid_value _ _ := false
      }.

  End ValuePredicates.

  Arguments is_valid_value [Scalar].
  

  (** *** Definitions related to subtyping
      ----

      This includes the definition of the subtyping relation.
   *)
  Section Subtypes.

    (** **** Subtyping relation.
        ----

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
        | Some (scalar name), Some (scalar name') => name == name'
        | Some (enum name { _ }), Some (enum name' { _ }) => name == name'
        | Some (object name implements _ { _ }), Some (object name' implements _ { _ }) => name == name'
        | Some (interface name { _ }), Some (interface name' { _ }) => name == name'
        | Some (union name { _ }), Some (union name' { _ }) => name == name'
        | Some (object name implements interfaces { _ }), Some (interface name' { _ }) => name' \in interfaces
        | Some (object name implements _ { _ }), Some (union name' { members }) => name \in members
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
      | Some (union _ { mbs }) => mbs
      | _ => [::]
      end.
    
    
    (** ---- *)
    (**
       Gets all object types that implement the given interface.
     *)
    Definition implementation (ty : Name) : seq Name :=
      undup [seq tdef.(tdname) | tdef <- schema.(type_definitions) & ty \in tdef.(tintfs)].

    (** ---- *)
    (**
       Gets "possible" types from a given type (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##GetPossibleTypes()'><span>&#167;</span>5.5.2.3</a>#)

       If the type is:
       - object : Possible types are only the type itself.
       - interface : Possible types are all types that declare implementation of this interface.
       - union : Possible types are all members of the union.    
     *)
    Equations get_possible_types (ty : Name) : seq Name :=
      {
        get_possible_types ty with lookup_type ty :=
          {
          | Some (object _ implements _ { _ }) => [:: ty];
          | Some (interface iname { _ }) => implementation iname;
          | Some (union _ { mbs }) => mbs;
          | _ => [::]
          }
      }.


  End Subtypes.
  

  
  
  
End SchemaAux.


Notation "s ⊢ ty1 <: ty2" := (is_subtype s ty1 ty2) (at level 50, ty1 at next level) : schema_scope.


(** ---- *)

(** 
    #<div>
        <a href='GraphCoQL.Schema.html' class="btn btn-light" role='button'> Previous ← Schema  </a>
        <a href='GraphCoQL.SchemaWellFormedness.html' class="btn btn-info" role='button'>Next → Schema Well-Formedness </a>
    </div>#
*)