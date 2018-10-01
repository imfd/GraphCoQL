Require Import List.
Import ListNotations.




Require Import Coq.Arith.EqNat.




Definition Name := nat.
Definition EnumValue := Name.


Inductive type : Type :=
| NamedType : Name -> type
| ListType : type -> type.
 

Inductive InputValueDefinition : Type :=
| InputValue : Name -> type -> InputValueDefinition.

Inductive ArgumentsDefinition : Type :=
| SingleArgument : InputValueDefinition -> ArgumentsDefinition
| MultipleArguments : InputValueDefinition -> ArgumentsDefinition -> ArgumentsDefinition.

Inductive FieldDefinition : Type :=
| Field : Name  -> type -> FieldDefinition
| FieldArgs : Name -> ArgumentsDefinition -> type -> FieldDefinition.

Inductive FieldsDefinition : Type :=
| SingleField : FieldDefinition -> FieldsDefinition
| MultipleFields : FieldDefinition -> FieldsDefinition -> FieldsDefinition.
  

(*
Inductive ImplementsInterfaces : Type :=
| SingleInterface : type -> ImplementsInterfaces
| MultipleInterfaces : type -> ImplementsInterfaces -> ImplementsInterfaces.
*)

(* Omitting InputObjects for now, to make it simpler *)
Inductive TypeDefinition : Type :=
| ScalarTypeDefinition : Name -> TypeDefinition
| ObjectTypeDefinition : Name -> FieldsDefinition -> TypeDefinition
| ObjectTypeWithInterfaces : Name -> list type -> FieldsDefinition -> TypeDefinition
| InterfaceTypeDefinition : Name -> FieldsDefinition -> TypeDefinition
| UnionTypeDefinition : Name -> list type -> TypeDefinition
| EnumTypeDefinition : Name -> list EnumValue -> TypeDefinition.
                                           

(* 
 - Omitting mutations and suscriptions, therefore only leaving query as possible operation
 - Omitting directives for simplicity

As per the spec: Directives provide a way to describe alternate runtime execution and type validation behavior in a GraphQL document. 
 *)
Definition Document := (type * list TypeDefinition)%type.



Definition lookupName (nt : Name) (doc : Document) : option TypeDefinition :=
  match doc with
    | (_ , tdefs) =>
      let n_eq nt tdef := match tdef with
                         | ScalarTypeDefinition name => beq_nat nt name
                         | ObjectTypeDefinition name _  => beq_nat nt name
                         | ObjectTypeWithInterfaces name _ _ => beq_nat nt name
                         | InterfaceTypeDefinition name _ => beq_nat nt name
                         | UnionTypeDefinition name _ => beq_nat nt name
                         | EnumTypeDefinition name _ => beq_nat nt name
                         end
      in
      find (n_eq nt) tdefs
  end.

Fixpoint lookupType (ty : type) (doc : Document) :=
  match ty with
  | NamedType name => lookupName name doc
  | ListType ty' => lookupType ty' doc
  end.




Inductive ScalarType (doc : Document) : type -> Prop :=
| Scalar : forall sname,
    lookupName sname doc = Some (ScalarTypeDefinition sname) ->
    ScalarType doc (NamedType sname).

Inductive ObjectType (doc : Document) : type -> Prop :=
| Object : forall name fields,
    lookupName name doc = Some (ObjectTypeDefinition name fields) ->
    ObjectType doc (NamedType name)
| ObjectWithInterfaces : forall name fields intfs,
    lookupName name doc = Some (ObjectTypeWithInterfaces name intfs fields) ->
    ObjectType doc (NamedType name).

Inductive InterfaceType (doc : Document) : type -> Prop :=
| Interface : forall name flds,
    lookupName name doc = Some (InterfaceTypeDefinition name flds) ->
    InterfaceType doc (NamedType name).


Inductive UnionType (doc : Document) : type -> Prop :=
| Union : forall name objs,
    lookupName name doc = Some (UnionTypeDefinition name objs) ->
    UnionType doc (NamedType name).

Inductive EnumType (doc : Document) : type -> Prop :=
| Enum : forall ename enums,
    lookupName ename doc = Some (EnumTypeDefinition ename enums) ->
    EnumType doc (NamedType ename).



Inductive subtype (doc : Document) : type -> type -> Prop :=
| ST_Refl : forall ty, subtype doc ty ty
| ST_Object : forall name intfs iname fields ifields,
    lookupName name doc = Some (ObjectTypeWithInterfaces name intfs fields) ->
    In (NamedType iname) intfs ->
    lookupName iname doc = Some (InterfaceTypeDefinition iname ifields) ->
    subtype doc (NamedType name) (NamedType iname)
| ST_ListType : forall ty ty',
    subtype doc ty ty' ->
    subtype doc (ListType ty) (ListType ty').
    
Definition name tdef : Name :=
  match tdef with 
  | ScalarTypeDefinition name => name
  | ObjectTypeDefinition name  _ => name
  | ObjectTypeWithInterfaces name _ _ => name
  | InterfaceTypeDefinition name _ => name
  | UnionTypeDefinition name _ => name
  | EnumTypeDefinition name _ => name
  end.

Definition names tdefs := map name tdefs.

Fixpoint unwrapTypeName (ty : type) : Name :=
  match ty with
  | NamedType name => name
  | ListType ty' => unwrapTypeName ty'
  end.

Definition typesNames tys := map unwrapTypeName tys.

Inductive IsInputField (doc : Document) : type -> Prop :=
| ScalarInput : forall ty,
    ScalarType doc ty ->
    IsInputField doc ty
| EnumInput : forall ty,
    EnumType doc ty ->
    IsInputField doc ty
| ListInput : forall ty,
    IsInputField doc ty ->
    IsInputField doc (ListType ty).
    

(* Because we are not considering InputObjects, every type is valid if it is in the document *)
Inductive IsOutputField (doc : Document) : type -> Prop :=
| OutputField : forall name tdef,
    lookupName name doc = Some tdef ->
    IsOutputField doc (NamedType name)
| OutputListField : forall ty,
    IsOutputField doc ty ->
    IsOutputField doc (ListType ty).




Inductive wfInputValue (doc : Document) : InputValueDefinition -> Prop :=
| WF_InputValue : forall ty name,
    IsInputField doc ty ->
    wfInputValue doc (InputValue name ty).

Inductive wfArgumentsDefinition (doc : Document) : ArgumentsDefinition -> Prop :=
| WF_SingleArgument : forall arg,
    wfInputValue doc arg ->
    wfArgumentsDefinition doc (SingleArgument arg)
| WF_MultipleArguments : forall arg args,
    wfArgumentsDefinition doc args ->
    wfInputValue doc arg ->
    wfArgumentsDefinition doc (MultipleArguments arg args).
    

Inductive wfField (doc : Document) : FieldDefinition -> Prop :=
| WF_Field : forall name outputType,
    IsOutputField doc outputType -> 
    wfField doc (Field name outputType)
| WF_FieldArgs : forall name args outputType,
    IsOutputField doc outputType ->
    wfArgumentsDefinition doc args ->
    wfField doc (FieldArgs name args outputType).

Inductive wfFieldsDefinition (doc : Document) : FieldsDefinition -> Prop :=
| WF_SingleField : forall fld,
    wfField doc fld ->
    wfFieldsDefinition doc (SingleField fld)
| WF_MultipleFields : forall fld fields,
    wfFieldsDefinition doc fields ->
    wfField doc fld ->
    wfFieldsDefinition doc (MultipleFields fld fields).
                                                                


Inductive wfTypeDefinition (doc : Document) : TypeDefinition -> Prop :=
| WF_Scalar : forall name,
    ScalarType doc (NamedType name) ->
    wfTypeDefinition doc (ScalarTypeDefinition name)
                     
| WF_Object : forall name fields,
    ObjectType doc (NamedType name) ->
    wfFieldsDefinition doc fields ->
    wfTypeDefinition doc (ObjectTypeDefinition name fields)
                     
| WF_ObjectWithInterfaces : forall name interfaces fields,
    ObjectType doc (NamedType name) ->
    NoDup (typesNames interfaces) ->
    Forall (InterfaceType doc) interfaces ->
    wfFieldsDefinition doc fields ->
    wfTypeDefinition doc (ObjectTypeWithInterfaces name interfaces fields)
    
| WF_Interface : forall name fields,
    InterfaceType doc (NamedType name) ->
    wfFieldsDefinition doc fields ->
    wfTypeDefinition doc (InterfaceTypeDefinition name fields)
                     
| WF_Union : forall name members,
    UnionType doc (NamedType name) ->
    members <> [] ->
    NoDup (typesNames members) ->
    Forall (ObjectType doc) members ->
    wfTypeDefinition doc (UnionTypeDefinition name members)
                     
| WF_Enum : forall name enumValues,
    EnumType doc (NamedType name) ->
    enumValues <> [] ->
    NoDup enumValues ->
    wfTypeDefinition doc (EnumTypeDefinition name enumValues).

           
Inductive wfDocument : Document -> Prop :=
| WF_Document : forall tdefs root,
    NoDup (names tdefs) ->
    In root (names tdefs) -> 
    Forall (wfTypeDefinition ((NamedType root), tdefs)) tdefs ->
    wfDocument ((NamedType root), tdefs).





                                                      