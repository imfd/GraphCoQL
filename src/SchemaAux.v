From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import List.
Import ListNotations.

Require Import Schema.



Section SchemaAux.


  Variable Name : finType.

  
  Definition root (doc : @Schema Name) : type := fst doc.
  (**
   Looks up a name in the given document, returning the type definition if it
   was declared in the document.
   **)
  Definition lookupName (nt : Name) (doc : Schema) : option TypeDefinition :=
    match doc with
    | (_ , tdefs) =>
      let n_eq nt tdef := match tdef with
                         | ScalarTypeDefinition name =>  nt == name
                         | ObjectTypeDefinition name _  _ =>  nt == name
                         | InterfaceTypeDefinition name _ => nt == name
                         | UnionTypeDefinition name _ => nt == name
                         | EnumTypeDefinition name _ =>  nt == name
                         end
      in
      find (n_eq nt) tdefs
    end.


  Definition ScalarType (doc : Schema) (t : type) : bool :=
    match t with
    | (NamedType name) =>
      match (lookupName name doc) with
      | Some (ScalarTypeDefinition name) => true
      | _ => false
      end
    | _ => false
    end.

  Definition ObjectType (doc : Schema) (t : type) : bool :=
    match t with
    | (NamedType name) =>
      match (lookupName name doc) with
      | Some (ObjectTypeDefinition name _ _) => true
      | _ => false
      end
    | _ => false
    end.

  Definition InterfaceType (doc : Schema) (t : type) : bool :=
    match t with
    | (NamedType name) =>
      match (lookupName name doc) with
      | Some (InterfaceTypeDefinition name _) => true
      | _ => false
      end
    | _ => false
    end.

  Definition UnionType (doc : Schema) (t : type) : bool :=
    match t with
    | (NamedType name) =>
      match (lookupName name doc) with
      | Some (UnionTypeDefinition name _) => true
      | _ => false
      end
    | _ => false
    end.

  Definition EnumType (doc : Schema) (t : type) : bool :=
    match t with
    | (NamedType name) =>
      match (lookupName name doc) with
      | Some (EnumTypeDefinition name _) => true
      | _ => false
      end
    | _ => false
    end.

  Definition isListType (t : @type Name) : bool :=
    match t with
    | (ListType t') => true
    | _ => false
    end.



  (** Get a type definition's name.
 Corresponds to the name one gives to an object, interface, etc. **)
  Definition name (tdef : TypeDefinition) : Name :=
    match tdef with 
    | ScalarTypeDefinition name => name
    | ObjectTypeDefinition name _ _ => name
    | InterfaceTypeDefinition name _ => name
    | UnionTypeDefinition name _ => name
    | EnumTypeDefinition name _ => name
    end.

  (** Get type definitions' names *)
  Definition names (tdefs : list TypeDefinition) := map name tdefs.


  (** Get a type's name.
    Corresponds to named type actual name or the name used in a list type **)
  Fixpoint unwrapTypeName (ty : type) : Name :=
    match ty with
    | NamedType name => name
    | ListType ty' => unwrapTypeName ty'
    end.

  Coercion unwrapTypeName : type >-> Finite.sort.

  (** Get types' names **)
  Definition typesNames (tys : list type) : list Name := map unwrapTypeName tys.

  (** Get arguments' names **)
  Definition argNames (args : list FieldArgumentDefinition) : list Name :=
    let extract arg := match arg with
                      | FieldArgument name _ => name
                      end
    in
    map extract args.

  (** Get a field's name **)
  Definition fieldName (fld : FieldDefinition) : Name :=
    match fld with
    | FieldWithoutArgs name _ => name
    | FieldWithArgs name _ _ => name
    end.

  (** Get fields' names **)
  Definition fieldNames (flds : list FieldDefinition) : list Name := map fieldName flds.


  (** Get list of fields declared in an Object or Interface type definition **)
  Definition fields (name : Name) (doc : Schema) : list FieldDefinition :=
    match lookupName name doc with
    | Some (ObjectTypeDefinition _ _ flds) => flds
    | Some (InterfaceTypeDefinition _ flds) => flds
    | _ => []
    end.

  Definition fieldType (f : FieldDefinition) : @type Name :=
    match f with
    | FieldWithoutArgs _ t => t
    | FieldWithArgs _ _ t => t
    end.

  Definition lookupField (fname : Name) (tname : Name) (doc : Schema) : option FieldDefinition :=
    let n_eq nt fld := match fld with
                      | FieldWithoutArgs name _ => nt == name
                      | FieldWithArgs name _ _ => nt == name
                      end
    in
    find (n_eq fname) (fields tname doc).

  Definition lookupFieldType (fname : Name) (tname : Name) (doc : Schema) : option type :=
    match lookupField fname tname doc with
    | Some fieldDef => Some (fieldType fieldDef)
    | None => None
    end.


  Definition union (doc : Schema) (tname : Name) :=
    match lookupName tname doc with
    | Some (EnumTypeDefinition name mbs) => mbs
    | _ => []
    end.


  
  Definition declaresImplementation (doc : Schema) (name iname : Name) : bool :=
    match lookupName name doc with
    | Some (ObjectTypeDefinition _ intfs _) => existsb (fun el => ((unwrapTypeName el) == iname) && InterfaceType doc el) intfs
    | _ => false
    end.



End SchemaAux.


Arguments root [Name].
Arguments lookupName [Name].
Arguments EnumType [Name].
Arguments fields [Name].
Arguments fieldType [Name].
Arguments unwrapTypeName [Name].
Arguments lookupField [Name].
Arguments lookupFieldType [Name].
Arguments union [Name].