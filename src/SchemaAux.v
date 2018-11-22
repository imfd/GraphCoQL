From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From extructures Require Import ord.

Require Import List.
Import ListNotations.

Require Import Schema.
Require Import treeordtype.

Set Implicit Arguments.

Section SchemaAux.


  Variable Name : ordType.

  
  (* Schema used as parameter in later functions *) 
  Implicit Type schema : @schema Name.


  (** Get the query root type for the given Schema **)
  Definition query_root schema : type := schema.(query_type). 

  
  (**
   Looks up a name in the given document, returning the type definition if it
   was declared in the document.
   **)
  Definition lookup_type schema (ty : type)  : option TypeDefinition :=
    let: (Schema _ tdefs) := schema in
    let n_eq nt tdef := match tdef with
                       | ScalarTypeDefinition name =>  (name_of_type nt) == name 
                       | ObjectTypeDefinition name _  _ =>  (name_of_type nt) == name
                       | InterfaceTypeDefinition name _ => (name_of_type nt) == name
                       | UnionTypeDefinition name _ => (name_of_type nt) == name
                       | EnumTypeDefinition name _ =>  (name_of_type nt) == name
                       end
    in
    find (n_eq ty) tdefs.
    


  (** Checks whether the given type is defined as a Scalar in the Schema **)
  Definition is_scalar_type schema (ty : type) : bool :=
    match ty with
    | (NamedType _) =>
      match (lookup_type schema ty) with
      | Some (ScalarTypeDefinition _) => true
      | _ => false
      end
    | _ => false
    end.

  (** Checks whether the given type is defined as an Object in the Schema **)
  Definition is_object_type schema (ty : type) : bool :=
    match ty with
    | (NamedType _) =>
      match (lookup_type schema ty) with
      | Some (ObjectTypeDefinition _ _ _) => true
      | _ => false
      end
    | _ => false
    end.

  (** Checks whether the given type is defined as an Interface in the Schema **)
  Definition is_interface_type schema (ty : type) : bool :=
    match ty with
    | (NamedType _) =>
      match (lookup_type schema ty) with
      | Some (InterfaceTypeDefinition _ _) => true
      | _ => false
      end
    | _ => false
    end.

  (** Checks whether the given type is defined as a Union in the Schema **)
  Definition is_union_type schema (ty : type) : bool :=
    match ty with
    | (NamedType _) =>
      match (lookup_type schema ty) with
      | Some (UnionTypeDefinition _ _) => true
      | _ => false
      end
    | _ => false
    end.

  (** Checks whether the given type is defined as an Enum in the Schema **)
  Definition is_enum_type schema (ty : type) : bool :=
    match ty with
    | (NamedType _) =>
      match (lookup_type schema ty) with
      | Some (EnumTypeDefinition _ _) => true
      | _ => false
      end
    | _ => false
    end.

  (** Checks whether the given type is a list type (does not care for the wrapped type) **)
  Definition is_list_type (ty : @type Name) : bool :=
    match ty with
    | (ListType ty') => true
    | _ => false
    end.



  Definition types_names (tys : seq.seq type) := map (@name_of_type Name) tys.

  (** Get a type definition's name.
      Corresponds to the name one gives to an object, interface, etc.
   **)
  Definition type_def_name (tdef : TypeDefinition) : Name :=
    match tdef with 
    | ScalarTypeDefinition name => name
    | ObjectTypeDefinition name _ _ => name
    | InterfaceTypeDefinition name _ => name
    | UnionTypeDefinition name _ => name
    | EnumTypeDefinition name _ => name
    end.

  (** Get type definitions' names *)
  Definition type_defs_names (tdefs : seq.seq TypeDefinition) := map type_def_name tdefs.


  (** Get names from a list of arguments **)
  Definition arguments_names (args : seq.seq FieldArgumentDefinition) : seq.seq Name :=
    map (@name_of_argument Name) args.

 
  (** Get list of fields declared in an Object or Interface type definition **)
  Definition field_definitions schema (ty : type) : list FieldDefinition :=
    match lookup_type schema ty with
    | Some (ObjectTypeDefinition _ _ flds) => flds
    | Some (InterfaceTypeDefinition _ flds) => flds
    | _ => []
    end.


  Definition fields_names (flds : seq.seq FieldDefinition) : seq.seq Name := map (@name_of_field Name) flds.

  
  
  (**
     Gets the first field definition from a given type that matches the given field name. 
     If the type is not declared in the Schema or the field does not belong to the type, then it returns None.
   **)
  Definition lookup_field_in_type schema (ty : type) (fname : Name) : option FieldDefinition :=
    let n_eq nt fld := let: Field name _ _ := fld in nt == name
    in
    find (n_eq fname) (field_definitions schema ty).


  (** 
      Gets the type of the first field definition from a given type that matches the given field name. 
      If the type is not declared in the Schema or the field does not belong to the type, then it returns None.

   **)
  Definition lookup_field_type schema (ty : type) (fname : Name)  : option type :=
    match lookup_field_in_type schema ty fname with
    | Some fieldDef => Some (type_of_field fieldDef) 
    | None => None
    end.


  (**
     Get the union's types' names.
     If the type is not declared as Union in the Schema, then returns None.
   **)
  Definition union_members schema (ty : type) : seq.seq Name :=
    match lookup_type schema ty with
    | Some (UnionTypeDefinition name mbs) => map (@name_of_type Name) mbs
    | _ => []
    end.


  (**
     Checks whether the given type declares implementation of another type.
   **)
  Definition declares_implementation schema (ty ty' : type) : bool :=
    match lookup_type schema ty with
    | Some (ObjectTypeDefinition _ intfs _) => has (fun i => i == ty') intfs
    | _ => false
    end.


  (**
     Gets the first argument definition that matches the given argument name, from the
     given type and field. If the argument is not defined then it returns None.
     If the field is not declared in that type, then it returns None.
   **)
  Definition lookup_argument_in_type_and_field schema (ty : type) (fname argname : Name) : option FieldArgumentDefinition :=
    match lookup_field_in_type schema ty fname with
    | Some (Field fname args _) => let n_eq n arg := let: FieldArgument name _ := arg in n == name
                                  in
                                  find (n_eq argname) args
    | _ => None
    end.

  (**
     Gets "possible" types from a given type, as defined in the GraphQL Spec
     (https://facebook.github.io/graphql/June2018/#GetPossibleTypes())

     If the type is:
     1. Object : Possible types are only the type itself.
     2. Interface : Possible types are all types that declare implementation of this interface.
     3. Union : Possible types are all members of the union.

   **)
  Definition get_possible_types schema (ty : type) : seq.seq type  :=
    match lookup_type schema ty with
    | Some (ObjectTypeDefinition _ _ _) => [:: ty]
    | Some (InterfaceTypeDefinition iname _) =>
      map (fun n => NamedType n)
          (type_defs_names (filter (fun tdef => match tdef with
                                             | (ObjectTypeDefinition _ intfs _) => has (fun i => (name_of_type i) == iname) intfs
                                             | _ => false
                                             end) schema.(typeDefinitions)))
    | Some (UnionTypeDefinition _ mbs) => mbs
    | _ => [::]
    end.
    
        

End SchemaAux.


Arguments query_root [Name].
Arguments lookup_type [Name].
Arguments is_enum_type [Name].

Arguments lookup_field_in_type [Name].
Arguments lookup_field_type [Name].
Arguments union_members [Name].
