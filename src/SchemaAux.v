From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.
From CoqUtils Require Import string.
Require Import Base.

Require Import Schema.
Require Import SeqExtra.


Section SchemaAux.


  Section TypeDefExtractors.
    
    (** Extractors for type definitions **)

    (** Get type definition's name **)
    Definition tdname tdef : Name :=
      match tdef with
      | Scalar name
      | Object name implements _ { _ }
      | Interface name { _ }
      | Union name { _ }
      | Enum name { _ } => name
      end.

    (** Get type definition's field **)
    Definition tfields tdef : seq FieldDefinition :=
      match tdef with 
      | Object _ implements _ { flds }
      | Interface _ { flds } => flds
      | _ => [::]
      end.

    (** Get type definition's declared interfaces **)
    Definition tintfs tdef : seq Name :=
      match tdef with
      | Object _ implements intfs { _ } => intfs
      | _ => [::]
      end.

    (** Get type definition's members (only valid for union type) **)
    Definition tmbs tdef : seq Name :=
      match tdef with
      | Union _ { mbs }=> mbs
      | _ => [::]
      end.

    (** Get type definition's members (only valid for enum type) **) 
    Definition tenums tdef : seq EnumValue :=
      match tdef with
      | Enum _ { enums } => enums
      | _ => [::]
      end.

    
    (* (** Get all unduplicated field names from a type definition **) *)
    (* Definition tdef_field_names (tdef : TypeDefinition) : seq Name := undup [seq fld.(fname) | fld <- tdef.(tfields)]. *)


  End TypeDefExtractors.
  



  (** Checks whether the given type definition has the given name **)
  Definition has_name (name : Name) (tdef : TypeDefinition) : bool :=
    name == tdef.(tdname).
  

  
  Variable schema : graphQLSchema.

  (* (** Finds the first type definitions that has the given name **) *)
  (* Equations find_tdef_with_name (tdefs : seq TypeDefinition) (ty : Name) : option TypeDefinition := *)
  (*   { *)
  (*     find_tdef_with_name [::] _ := None; *)
  (*     find_tdef_with_name (tdef :: tdefs) ty *)
  (*       with tdef.(tdname) == ty := *)
  (*       { *)
  (*       | true := Some tdef; *)
  (*       | _ := find_tdef_with_name tdefs ty *)
  (*       } *)
  (*   }. *)
  
  Definition lookup_type (ty : Name) :=
    get_first (fun tdef => tdef.(tdname) == ty) schema.(type_definitions).

  
  
  Section TypePredicates.
    
    (** Checks whether the given type is defined as a Scalar in the Schema **)
    Definition is_scalar_type (ty : Name) : bool :=
      match lookup_type ty with
      | Some (Scalar _) => true
      | _ => false
      end.


    
    (** Checks whether the given type is defined as an Object in the Schema **)
    Equations is_object_type (ty : Name) : bool :=
      is_object_type ty with lookup_type ty :=
        {
        | Some (Object _ implements _ { _ }) := true;
        | _ := false
        }.



    (** Checks whether the given type is defined as an Interface in the Schema **)
    Equations is_interface_type (ty : Name) : bool :=
      is_interface_type ty with lookup_type ty :=
        {
        | Some (Interface _ { _ }) := true;
        | _ := false
        }.

    
    
    (** Checks whether the given type is defined as a Union in the Schema **)
    Equations is_union_type (ty : Name) : bool :=
      is_union_type ty with lookup_type ty :=
        {
        | Some (Union _ { _ }) := true;
        | _ := false
        }.

    
    (** Checks whether the given type is defined as an Enum in the Schema **)
    Definition is_enum_type (ty : Name) : bool :=
      match lookup_type ty with
      | Some (Enum _ { _ }) => true
      | _ => false
      end.

    (** Checks whether the given type is a list type (does not care for the wrapped type) **)
    Definition is_list_type (ty : type) : bool :=
      match ty with
      | [ ty' ] => true
      | _ => false
      end.

    Definition is_abstract_type (ty : Name) : bool :=
      is_interface_type ty ||  is_union_type ty.

    Definition is_composite_type (ty : Name) : bool :=
      [|| is_object_type ty, is_interface_type ty | is_union_type ty].

    Definition is_leaf_type (ty : Name) : bool :=
      is_scalar_type ty || is_enum_type ty.
    
  End TypePredicates.
  

  

  (** Get all type definitions' names from a schema **)
  Definition schema_names : seq Name := [seq tdef.(tdname) | tdef <- schema.(type_definitions)]. 


  (** Check whether a given name is declared in the schema, as a type definition **)
  Definition is_declared (name : Name) : bool := name \in schema_names.


  (** Checks whether the field has the given name **)
  Definition has_field_name (name : Name) (fld : FieldDefinition) :=
    name == fld.(fname).



  Section Lookup.
    
    (**
     Gets the first field definition from a given type that matches the given field name. 
     If the type is not declared in the Schema or the field does not belong to the type, then it returns None.
     **)
    Definition lookup_field_in_type (ty : Name) (fname : Name) : option FieldDefinition :=
      if lookup_type ty is Some tdef then
        get_first (has_field_name fname) tdef.(tfields)
      else
        None.


    
    (** 
      Gets the type of the first field definition from a given type that matches the given field name. 
      If the type is not declared in the Schema or the field does not belong to the type, then it returns None.

     **)
    Definition lookup_field_type (ty : Name) (fname : Name)  : option type :=
      match lookup_field_in_type ty fname with
      | Some fld => Some fld.(return_type)
      | None => None
      end.

    (**
     Gets the first argument definition that matches the given argument name, from the
     given type and field. If the argument is not defined then it returns None.
     If the field is not declared in that type, then it returns None.
     **)
    Definition lookup_argument_in_type_and_field (ty : Name) (fname aname : Name) : option FieldArgumentDefinition :=
      match lookup_field_in_type ty fname with
      | Some (Field fname args _) => get_first (fun arg => arg.(argname) == aname) args
      | _ => None
      end.

    (** Get list of fields declared in an Object or Interface type definition **)
    Definition fields (ty : Name) : seq FieldDefinition :=
      match lookup_type ty with
      | Some (Object _ implements _ { flds })
      | Some (Interface _ { flds }) => flds
      | _ => [::]
      end.
    
  End Lookup.


  Section Subtypes.
    
    (**
     Get the union's types' names.
     If the type is not declared as Union in the Schema, then returns None.
     **)
    Definition union_members (ty : Name) : seq Name :=
      match lookup_type ty with
      | Some (Union _ { mbs }) => mbs
      | _ => [::]
      end.

    
    (**
     Checks whether the given type declares implementation of another type.
     **)
    Definition declares_implementation (ty ty' : Name) : bool :=
      match lookup_type ty with
      | Some (Object _ implements intfs { _ }) => ty' \in intfs
      | _ => false
      end.


    
    Definition implements_interface (iname : Name) (tdef : TypeDefinition) : bool :=
      iname \in tdef.(tintfs).



    
    

    Definition implementation (ty : Name) : seq Name :=
      undup [seq tdef.(tdname) | tdef <- schema.(type_definitions) & implements_interface ty tdef].

    
    (**
     Gets "possible" types from a given type, as defined in the GraphQL Spec
     (https://facebook.github.io/graphql/June2018/#GetPossibleTypes())

     If the type is:
     1. Object : Possible types are only the type itself.
     2. Interface : Possible types are all types that declare implementation of this interface.
     3. Union : Possible types are all members of the union.

     ---- 
     See also:

     https://graphql.github.io/graphql-spec/June2018/#GetPossibleTypes()
     **)
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


