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

(** Subtype relation

   
                 ----------------------- (ST_Refl)
                       ty <: ty

                  
       Doc(O) = type O implements ... I ... { ... }
                Doc(I) = interface I { ...}
       ------------------------------------------- (ST_Object)
                         O <: I

           
                         T <: U
                ------------------------- (ST_ListType)
                       [T] <: [U]


Some observations:
    1. Transitivity : There is no need to specify this because only objects can 
    be subtype of an interface and not between objects. Interfaces cannot be
    subtype of another interface.
**)

Inductive subtype (doc : Document) : type -> type -> Prop :=
| ST_Refl : forall ty, subtype doc ty ty
| ST_Object : forall name intfs iname fields ifields,
    lookupName name doc = Some (ObjectTypeDefinition name intfs fields) ->
    In (NamedType iname) intfs ->
    lookupName iname doc = Some (InterfaceTypeDefinition iname ifields) ->
    subtype doc (NamedType name) (NamedType iname)
| ST_ListType : forall ty ty',
    subtype doc ty ty' ->
    subtype doc (ListType ty) (ListType ty').

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




(** The two following definitions describe whether a given type is a valid type
for a field argument (IsValidArgumentType) and if it is a valid type for a field itself 
(IsValidFieldType).

In the spec they are correspondently named "IsInputField" and "IsOutputField".

https://facebook.github.io/graphql/June2018/#sec-Input-and-Output-Types **)

Fixpoint isValidArgumentType (doc : Document) (ty : type) : bool :=
  match ty with
  | NamedType _ => ScalarType doc ty || EnumType doc ty
  | ListType ty' => isValidArgumentType doc ty'
  end.
    

(* Because we are not considering InputObjects, a field may have any type, 
as long as it is declared in the document.

Not really sure how to name this case... Named seems weird? *)
Fixpoint isValidFieldType (doc : Document) (ty : type) : bool :=
  match ty with
  | NamedType n => match lookupName n doc with
                  | Some tdef => true
                  | _ => false
                  end
  | ListType ty' => isValidFieldType doc ty'
  end.




Inductive wfFieldArgument (doc : Document) : FieldArgumentDefinition -> Prop :=
| WF_InputValue : forall ty name,
    isValidArgumentType doc ty ->
    wfFieldArgument doc (FieldArgument name ty).


Inductive wfField (doc : Document) : FieldDefinition -> Prop :=
| WF_Field : forall name outputType,
    isValidFieldType doc outputType -> 
    wfField doc (FieldWithoutArgs name outputType)
| WF_FieldArgs : forall name args outputType,
    isValidFieldType doc outputType ->
    args <> [] ->
    NoDup (argNames args) ->               (* This is not actually explicit in the spec I believe *)
    Forall (wfFieldArgument doc) args ->
    wfField doc (FieldWithArgs name args outputType).
                                                                
Definition declaresImplementation (doc : Document) (name iname : Name) : bool :=
  match lookupName name doc with
  | Some (ObjectTypeDefinition _ intfs _) => existsb (fun el => ((unwrapTypeName el) == iname) && InterfaceType doc el) intfs
  | _ => false
  end.

(** This checks whether an object field is valid w/r to another from an implemented interface.
The possible options are:

    1.                  T <: U
               -------------------------
               (fname : T) OK (fname : U)

    2.               T ∈ unionTypes(U)
                 -------------------------
                (fname : T) OK (fname : U)

    3.      T <: U     ∀ arg in args', arg ∈ args          
            -------------------------------------------
             (fname (args) : T) OK (fname (args') : U)

    4.      T ∈ unionTypes(U)     ∀ arg in args', arg ∈ args
           --------------------------------------------------------
                 (fname (args) : T) OK (fname (args') : U)


The arguments have to be completed included, both their names and types (invariant).

If we consider a Field  having a list of arguments, instead of two 
constructors, we could simplify this definition I guess.

**)
Inductive fieldOk (doc : Document) : FieldDefinition -> FieldDefinition -> Prop :=
  
| SimpleInterfaceField : forall fname ty ty',
    subtype doc ty ty' ->
    fieldOk doc (FieldWithoutArgs fname ty) (FieldWithoutArgs fname ty')
| SimpleUnionField : forall fname ename ty objs,
    lookupName ename doc = Some (UnionTypeDefinition ename objs) ->
    In ty objs ->
    fieldOk doc (FieldWithoutArgs fname ty) (FieldWithoutArgs fname (NamedType ename))
            
| InterfaceFieldArgs : forall fname ty ty' args args',
    subtype doc ty ty' ->
    incl args' args ->
    fieldOk doc (FieldWithArgs fname args ty) (FieldWithArgs fname args' ty')

| UnionFieldArgs : forall fname ename ty args args' objs,
    lookupName ename doc = Some (UnionTypeDefinition ename objs) ->
    In ty objs ->
    incl args' args ->
    fieldOk doc (FieldWithArgs fname args ty) (FieldWithArgs fname args' (NamedType ename)).



(**
   This checks whether an object type implements correctly an interface, 
   by properly defining every field defined in the interface.


            Doc(name) = type name implements ... iname ... { Flds }   
                    Doc(iname) = interface iname { Flds' }
                 ∀ fld' ∈ Flds', ∃ fld ∈ Flds s.t fld OK fld'
            ------------------------------------------------
                        name implementsOK iname

**)
Inductive implementsOK (doc : Document ) : type -> type -> Prop :=
| ImplementsAll : forall name intfs fields iname ifields,
    lookupName name doc = Some (ObjectTypeDefinition name intfs fields) ->
    In (NamedType iname) intfs ->
    lookupName iname doc = Some (InterfaceTypeDefinition iname ifields) ->
    (forall ifld, In ifld ifields ->
           exists ofld, In ofld fields ->
                   fieldOk doc ofld ifld)  ->
    implementsOK doc (NamedType name) (NamedType iname).



(**

                       Doc(S) = scalar S 
                       -----------------------
                           scalar S OK


                 Doc(O) = type O implements Ifs { Flds }
                           notEmpty Flds
                         NoDuplicates Flds
                            Flds OK in O
                            Ifs OK in O
                -----------------------------------------
                          type O { Flds } 



                    Doc(I) = interface I { Flds }
                           notEmpty Flds
                         NoDuplicates Flds
                            Flds OK in I
                ----------------------------------------
                        interface I { Flds } 



                       Doc(U) = union U { Mbs }
                           notEmpty Mbs
                         NoDuplicates Mbs
                     ∀ mb ∈ Mbs, mb ObjectType
                -----------------------------------------
                          union U { Mbs } 


                       Doc(E) = enum E { Evs }
                           notEmpty Evs
                         NoDuplicates Evs
                -----------------------------------------
                          enum E { Evs } 

**)
Inductive wfTypeDefinition (doc : Document) : TypeDefinition -> Prop :=
| WF_Scalar : forall name,
    ScalarType doc (NamedType name) ->
    wfTypeDefinition doc (ScalarTypeDefinition name)
 
| WF_ObjectWithInterfaces : forall name interfaces fields,
    lookupName name doc = Some (ObjectTypeDefinition name interfaces fields) ->
    fields <> [] ->
    NoDup (fieldNames fields) ->
    Forall (wfField doc) fields ->
    NoDup (typesNames interfaces) ->
    Forall (implementsOK doc (NamedType name)) interfaces ->
    wfTypeDefinition doc (ObjectTypeDefinition name interfaces fields)
    
| WF_Interface : forall name fields,
    lookupName name doc = Some (InterfaceTypeDefinition name fields) ->
    fields <> [] ->
    NoDup (fieldNames fields) ->
    Forall (wfField doc) fields ->
    wfTypeDefinition doc (InterfaceTypeDefinition name fields)
                     
| WF_Union : forall name members,
    lookupName name doc = Some (UnionTypeDefinition name members) ->
    members <> [] ->
    NoDup (typesNames members) ->
    Forall (ObjectType doc) members ->
    wfTypeDefinition doc (UnionTypeDefinition name members)
                     
| WF_Enum : forall name enumValues,
    lookupName name doc = Some (EnumTypeDefinition name enumValues) ->
    enumValues <> [] ->
    NoDup enumValues ->
    wfTypeDefinition doc (EnumTypeDefinition name enumValues).

           
Inductive wfDocument : Document -> Prop :=
| WF_Document : forall tdefs root,
    NoDup (names tdefs) ->
    In root (names tdefs) -> 
    Forall (wfTypeDefinition ((NamedType root), tdefs)) tdefs ->
    wfDocument ((NamedType root), tdefs).




End Schema.

Arguments Document [Name].
Arguments root [Name].
Arguments fields [Name].
Arguments fieldType [Name].
Arguments unwrapTypeName [Name].
Arguments lookupField [Name].
Arguments lookupFieldType [Name].
Arguments union [Name].