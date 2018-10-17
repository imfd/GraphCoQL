From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import List.
Import ListNotations.

Require Import Schema.

Set Implicit Arguments.

Section SchemaAux.


  Variable Name : finType.

  
  Fixpoint typeEq (ty ty' : @type Name) : bool :=
    match ty, ty' with
    | NamedType n, NamedType n' => n == n'
    | ListType ty, ListType ty' => typeEq ty ty'
    | _, _ => false
    end.
(*
  Lemma typeEqP : Equality.axiom typeEq.
  Proof.
    move => ty ty'. apply (iffP idP). *)
    
  
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


  Definition isScalarType (doc : Schema) (t : type) : bool :=
    match t with
    | (NamedType name) =>
      match (lookupName name doc) with
      | Some (ScalarTypeDefinition name) => true
      | _ => false
      end
    | _ => false
    end.

  Definition isObjectType (doc : Schema) (t : type) : bool :=
    match t with
    | (NamedType name) =>
      match (lookupName name doc) with
      | Some (ObjectTypeDefinition name _ _) => true
      | _ => false
      end
    | _ => false
    end.

  Definition isInterfaceType (doc : Schema) (t : type) : bool :=
    match t with
    | (NamedType name) =>
      match (lookupName name doc) with
      | Some (InterfaceTypeDefinition name _) => true
      | _ => false
      end
    | _ => false
    end.

  Definition isUnionType (doc : Schema) (t : type) : bool :=
    match t with
    | (NamedType name) =>
      match (lookupName name doc) with
      | Some (UnionTypeDefinition name _) => true
      | _ => false
      end
    | _ => false
    end.

  Definition isEnumType (doc : Schema) (t : type) : bool :=
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
    let: Field name _ _ := fld in name.

  (** Get fields' names **)
  Definition fieldNames (flds : list FieldDefinition) : list Name := map fieldName flds.


  (** Get list of fields declared in an Object or Interface type definition **)
  Definition fieldDefinitions (name : Name) (doc : Schema) : list FieldDefinition :=
    match lookupName name doc with
    | Some (ObjectTypeDefinition _ _ flds) => flds
    | Some (InterfaceTypeDefinition _ flds) => flds
    | _ => []
    end.


  Definition fields (schema : Schema) (name : Name) : list Name :=
    match lookupName name schema with
    | Some (ObjectTypeDefinition _ _ flds) => fieldNames flds
    | Some (InterfaceTypeDefinition _ flds) => fieldNames flds
    | _ => []
    end.

  Definition fieldType (fld : FieldDefinition) : @type Name :=
    let: Field _ _ ty := fld in ty.

  Definition lookupField (schema : Schema) (tname fname : Name) : option FieldDefinition :=
    let n_eq nt fld := let: Field name _ _ := fld in nt == name
    in
    find (n_eq fname) (fieldDefinitions tname schema).

  Definition lookupFieldType (schema : Schema) (tname fname : Name)  : option type :=
    match lookupField schema fname tname with
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
    | Some (ObjectTypeDefinition _ intfs _) => existsb (fun el => ((unwrapTypeName el) == iname) && isInterfaceType doc el) intfs
    | _ => false
    end.


  Definition lookupArgument (schema : Schema) (tname fname argname : Name) : option FieldArgumentDefinition :=
    match lookupField schema tname fname with
    | Some (Field fname args _) => let n_eq n arg := let: FieldArgument name _ := arg in n == name
                                  in
                                  find (n_eq argname) args
    | _ => None
    end.

End SchemaAux.


Arguments root [Name].
Arguments lookupName [Name].
Arguments isEnumType [Name].
Arguments fields [Name].
Arguments fieldType [Name].
Arguments unwrapTypeName [Name].
Arguments lookupField [Name].
Arguments lookupFieldType [Name].
Arguments union [Name].
