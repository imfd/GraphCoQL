Require Import List.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.
From extructures Require Import ord.


Require Import Schema.
Require Import treeordtype.

Set Implicit Arguments.

Section SchemaAux.


  Variable Name : ordType.

  
  (* Schema used as parameter in later functions *) 
  Implicit Type schema : @schema Name.

  

  Fixpoint get_first {A} p (lst : seq A) :=
    if lst is hd :: tl then
      if p hd then
        Some hd
      else
        get_first p tl
    else
      None.
  
  (** Get the query root type for the given Schema **)
  Definition query_root schema : NamedType := schema.(query_type). 

  
  (**
   Looks up a name in the given document, returning the type definition if it
   was declared in the document.
   **)
  Definition lookup_type schema (ty : NamedType)  : option TypeDefinition :=
    let: (Schema _ tdefs) := schema in
    let n_eq nt tdef := match tdef with
                       | ScalarTypeDefinition name =>  nt == name 
                       | ObjectTypeDefinition name _  _ =>  nt == name
                       | InterfaceTypeDefinition name _ => nt == name
                       | UnionTypeDefinition name _ => nt == name
                       | EnumTypeDefinition name _ =>  nt == name
                       end
    in
    get_first (n_eq ty) tdefs.
    


  (** Checks whether the given type is defined as a Scalar in the Schema **)
  Definition is_scalar_type schema (ty : NamedType) : bool :=
    match (lookup_type schema ty) with
    | Some (ScalarTypeDefinition _) => true
    | _ => false
    end.

  (** Checks whether the given type is defined as an Object in the Schema **)
  Equations is_object_type schema (ty : @NamedType Name) : bool :=
    is_object_type schema ty with (lookup_type schema ty) =>
    {
      | Some (ObjectTypeDefinition _ _ _) := true;
      | _ => false
    }.


  (** Checks whether the given type is defined as an Interface in the Schema **)
  Definition is_interface_type schema (ty : NamedType) : bool :=
   match (lookup_type schema ty) with
   | Some (InterfaceTypeDefinition _ _) => true
   | _ => false
   end.

  (** Checks whether the given type is defined as a Union in the Schema **)
  Definition is_union_type schema (ty : NamedType) : bool :=
   match (lookup_type schema ty) with
   | Some (UnionTypeDefinition _ _) => true
   | _ => false
   end.

  (** Checks whether the given type is defined as an Enum in the Schema **)
  Definition is_enum_type schema (ty : NamedType) : bool :=
    match (lookup_type schema ty) with
    | Some (EnumTypeDefinition _ _) => true
    | _ => false
    end.

  (** Checks whether the given type is a list type (does not care for the wrapped type) **)
  Definition is_list_type (ty : @type Name) : bool :=
    match ty with
    | (ListType ty') => true
    | _ => false
    end.



  Definition types_names (tys : seq type) : seq Name := map (@name_of_type Name) tys.

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
  Definition type_defs_names (tdefs : seq TypeDefinition) : seq Name := map type_def_name tdefs.

  Definition is_named tdef (name : Name) : bool :=
    match tdef with
    | ScalarTypeDefinition n => n == name
    | ObjectTypeDefinition n _ _ => n == name
    | InterfaceTypeDefinition n _ => n == name
    | UnionTypeDefinition n _ => n == name
    | EnumTypeDefinition n _ => n == name
    end.

  (** Get names from a list of arguments **)
  Definition arguments_names (args : seq FieldArgumentDefinition) : seq Name :=
    map (@argname Name) args.

 
  (** Get list of fields declared in an Object or Interface type definition **)
  Definition fields schema (ty : NamedType) : list FieldDefinition :=
    match lookup_type schema ty with
    | Some (ObjectTypeDefinition _ _ flds) => flds
    | Some (InterfaceTypeDefinition _ flds) => flds
    | _ => []
    end.


  Definition fields_names (flds : seq FieldDefinition) : seq Name := map (@field_name Name) flds.

  
  
  (**
     Gets the first field definition from a given type that matches the given field name. 
     If the type is not declared in the Schema or the field does not belong to the type, then it returns None.
   **)
  Definition lookup_field_in_type schema (ty : NamedType) (fname : Name) : option FieldDefinition :=
    let n_eq nt fld := let: Field name _ _ := fld in nt == name
    in
    get_first (n_eq fname) (fields schema ty).


  (** 
      Gets the type of the first field definition from a given type that matches the given field name. 
      If the type is not declared in the Schema or the field does not belong to the type, then it returns None.

   **)
  Definition lookup_field_type schema (ty : NamedType) (fname : Name)  : option type :=
    match lookup_field_in_type schema ty fname with
    | Some fieldDef => Some (return_type fieldDef) 
    | None => None
    end.


  (**
     Get the union's types' names.
     If the type is not declared as Union in the Schema, then returns None.
   **)
  Definition union_members schema (ty : NamedType) : seq NamedType :=
    match lookup_type schema ty with
    | Some (UnionTypeDefinition name mbs) => mbs
    | _ => []
    end.


  (**
     Checks whether the given type declares implementation of another type.
   **)
  Definition declares_implementation schema (ty ty' : NamedType) : bool :=
    match lookup_type schema ty with
    | Some (ObjectTypeDefinition _ intfs _) => has (fun i => i == ty') intfs
    | _ => false
    end.


  Definition implements_interface (tdef : @TypeDefinition Name) (iname : NamedType) : bool :=
    match tdef with
    | ObjectTypeDefinition _ intfs _ => has (xpred1 iname) intfs
    | _ => false
    end.
  
  (**
     Gets the first argument definition that matches the given argument name, from the
     given type and field. If the argument is not defined then it returns None.
     If the field is not declared in that type, then it returns None.
   **)
  Definition lookup_argument_in_type_and_field schema (ty : NamedType) (fname argname : Name) : option FieldArgumentDefinition :=
    match lookup_field_in_type schema ty fname with
    | Some (Field fname args _) => let n_eq n arg := let: FieldArgument name _ := arg in n == name
                                  in
                                  get_first (n_eq argname) args
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
  Definition get_possible_types schema (ty : NamedType) : seq NamedType  :=
    match lookup_type schema ty with
    | Some (ObjectTypeDefinition _ _ _) => [:: ty]
    | Some (InterfaceTypeDefinition iname _) =>
      (type_defs_names (filter (fun tdef => match tdef with
                                         | (ObjectTypeDefinition _ intfs _) => has (fun i => i == iname) intfs
                                         | _ => false
                                         end) schema.(typeDefinitions)))
    | Some (UnionTypeDefinition _ mbs) => mbs
    | _ => [::]
    end.



  Definition implementation schema (ty : NamedType) : seq NamedType :=
     match lookup_type schema ty with
    | Some (InterfaceTypeDefinition iname _) =>
      type_defs_names [seq tdef <- schema |  implements_interface tdef iname]
    | _ => [::]
    end.
        

End SchemaAux.


Arguments query_root [Name].
Arguments lookup_type [Name].
Arguments is_enum_type [Name].

Arguments lookup_field_in_type [Name].
Arguments lookup_field_type [Name].
Arguments union_members [Name].
