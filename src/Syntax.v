From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import List.
Import ListNotations.


From Coq Require Import Bool String.


Section Schema.

(** Names for everything, from operations, fields, arguments, types, etc.

   https://facebook.github.io/graphql/June2018/#sec-Names **)
Variable Name : finType.


(** Same as names, except that it can't be true, false or null

https://facebook.github.io/graphql/June2018/#EnumValue **)
Definition EnumValue := Name.


(** Types of data expected by query variables.

https://facebook.github.io/graphql/June2018/#sec-Type-References **)

Inductive type : Type :=
| NamedType : Name -> type
| ListType : type -> type.



(** In the specification it is named "InputValue" (InputValueDefinition) but 
it is not very descriptive of what it is. Besides, it is constantly refered 
as "argument", therefore it is named as FieldArgument (only fields can have
arguments so it may sound redundant to name it like this but I feel it is
more descriptive and reinforces this notion). 

https://facebook.github.io/graphql/June2018/#sec-Field-Arguments **)
Inductive FieldArgumentDefinition : Type :=
| FieldArgument : Name -> type -> FieldArgumentDefinition.


(** https://facebook.github.io/graphql/June2018/#FieldDefinition **)
(* Actually, if we are using list of arguments, then a single constructor suffices, right? *)
Inductive FieldDefinition : Type :=
| FieldWithoutArgs : Name  -> type -> FieldDefinition
| FieldWithArgs : Name -> list FieldArgumentDefinition -> type -> FieldDefinition.



(** Possible type definitions one can make in a GraphQL service. Some observations:

    1. Objects' interfaces: Objects *may* declare one or more implemented interfaces. This is 
    is implemented as a list of <type>, which can be empty or not. As it is, an
    object may declare an interface as a list type (eg. "type A implements [B]"), therefore
    in the wf property there is a check that restricts this declaration to a 
    named type.

    2. Fields: Objects and interfaces must declare at least one field but the current
    definition allows an empty list of fields. In the wf property it is checked that
    this list is not empty.

    3. InputObjects: Currently not included to simplify the formalization.


https://facebook.github.io/graphql/June2018/#TypeDefinition **)

Inductive TypeDefinition : Type :=
| ScalarTypeDefinition : Name -> TypeDefinition
| ObjectTypeDefinition : Name -> list type -> list FieldDefinition -> TypeDefinition
| InterfaceTypeDefinition : Name -> list FieldDefinition -> TypeDefinition
| UnionTypeDefinition : Name -> list type -> TypeDefinition
| EnumTypeDefinition : Name -> list EnumValue -> TypeDefinition.
                                           

(* 
 - Omitting mutations and suscriptions, therefore only leaving query as possible operation
 - Omitting directives for simplicity

As per the spec: Directives provide a way to describe alternate runtime execution and type validation behavior in a GraphQL document. 
 *)
Definition Document := (type * list TypeDefinition)%type.



Definition root (doc : Document) : type := fst doc.
(**
   Looks up a name in the given document, returning the type definition if it
   was declared in the document.
**)
Definition lookupName (nt : Name) (doc : Document) : option TypeDefinition :=
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


Definition ScalarType (doc : Document) (t : type) : bool :=
  match t with
  | (NamedType name) =>
    match (lookupName name doc) with
    | Some (ScalarTypeDefinition name) => true
    | _ => false
    end
  | _ => false
  end.

Definition ObjectType (doc : Document) (t : type) : bool :=
  match t with
  | (NamedType name) =>
    match (lookupName name doc) with
    | Some (ObjectTypeDefinition name _ _) => true
    | _ => false
    end
  | _ => false
  end.

Definition InterfaceType (doc : Document) (t : type) : bool :=
  match t with
  | (NamedType name) =>
    match (lookupName name doc) with
    | Some (InterfaceTypeDefinition name _) => true
    | _ => false
    end
  | _ => false
  end.

Definition UnionType (doc : Document) (t : type) : bool :=
  match t with
  | (NamedType name) =>
    match (lookupName name doc) with
    | Some (UnionTypeDefinition name _) => true
    | _ => false
    end
  | _ => false
  end.

Definition EnumType (doc : Document) (t : type) : bool :=
  match t with
  | (NamedType name) =>
    match (lookupName name doc) with
    | Some (EnumTypeDefinition name _) => true
    | _ => false
    end
  | _ => false
  end.

Definition isListType (t : type) : bool :=
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
Definition fields (name : Name) (doc : Document) : list FieldDefinition :=
  match lookupName name doc with
  | Some (ObjectTypeDefinition _ _ flds) => flds
  | Some (InterfaceTypeDefinition _ flds) => flds
  | _ => []
  end.

Definition fieldType (f : FieldDefinition) :=
  match f with
  | FieldWithoutArgs _ t => t
  | FieldWithArgs _ _ t => t
  end.

Definition lookupField (fname : Name) (tname : Name) (doc : Document) : option FieldDefinition :=
  let n_eq nt fld := match fld with
                    | FieldWithoutArgs name _ => nt == name
                    | FieldWithArgs name _ _ => nt == name
                    end
  in
  find (n_eq fname) (fields tname doc).

Definition lookupFieldType (fname : Name) (tname : Name) (doc : Document) : option type :=
   match lookupField fname tname doc with
    | Some fieldDef => Some (fieldType fieldDef)
    | None => None
    end.


Definition union (doc : Document) (tname : Name) :=
  match lookupName tname doc with
  | Some (EnumTypeDefinition name mbs) => mbs
  | _ => []
  end.


                                                                
Definition declaresImplementation (doc : Document) (name iname : Name) : bool :=
  match lookupName name doc with
  | Some (ObjectTypeDefinition _ intfs _) => existsb (fun el => ((unwrapTypeName el) == iname) && InterfaceType doc el) intfs
  | _ => false
  end.



End Schema.

Arguments type [Name].
Arguments FieldArgumentDefinition [Name].
Arguments FieldDefinition [Name].
Arguments TypeDefinition [Name].
Arguments Document [Name].
Arguments root [Name].
Arguments lookupName [Name].
Arguments EnumType [Name].
Arguments fields [Name].
Arguments fieldType [Name].
Arguments unwrapTypeName [Name].
Arguments lookupField [Name].
Arguments lookupFieldType [Name].
Arguments union [Name].