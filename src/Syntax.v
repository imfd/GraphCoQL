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
  

Inductive ImplementsInterfaces : Type :=
| SingleInterface : Name -> ImplementsInterfaces
| MultipleInterfaces : Name -> ImplementsInterfaces -> ImplementsInterfaces.


(* Omitting InputObjects for now, to make it simpler *)
Inductive TypeDefinition : Type :=
| ScalarTypeDefinition : Name -> TypeDefinition
| ObjectTypeDefinition : Name -> FieldsDefinition -> TypeDefinition
| ObjectTypeWithInterfaces : Name -> ImplementsInterfaces -> FieldsDefinition -> TypeDefinition
| InterfaceTypeDefinition : Name -> FieldsDefinition -> TypeDefinition
| UnionTypeDefinition : Name -> list Name -> TypeDefinition
| EnumTypeDefinition : Name -> list EnumValue -> TypeDefinition.
                                           

(* 
 - Omitting mutations and suscriptions, therefore only leaving query as possible operation
 - Omitting directives for simplicity

As per the spec: Directives provide a way to describe alternate runtime execution and type validation behavior in a GraphQL document. 
 *)
Definition Document := (Name * list TypeDefinition)%type.



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

Definition typeName tdef : Name :=
  match tdef with 
  | ScalarTypeDefinition name => name
  | ObjectTypeDefinition name  _ => name
  | ObjectTypeWithInterfaces name _ _ => name
  | InterfaceTypeDefinition name _ => name
  | UnionTypeDefinition name _ => name
  | EnumTypeDefinition name _ => name
  end.
  
Definition names tdefs :=  map typeName tdefs.

Definition fieldName fld :=
  match fld with
  | Field name _ => name
  | FieldArgs name _ _ => name
  end.

Definition fieldsNames flds := map fieldName flds.

Definition getFields tdef :=
  match tdef with
  | ObjectTypeDefinition _ fields => Some fields
  | ObjectTypeWithInterfaces _ _ fields => Some fields
  | InterfaceTypeDefinition _ fields => Some fields
  | _ => None
  end.


Inductive ScalarType (doc : Document) : type -> Prop :=
| Scalar : forall ty sname,
    lookupType ty doc = Some (ScalarTypeDefinition sname) ->
    ScalarType doc ty.

Inductive EnumType (doc : Document) : type -> Prop :=
| Enum : forall ty ename enums,
    lookupType ty doc = Some (EnumTypeDefinition ename enums) ->
    EnumType doc ty.



Inductive IsInputField (doc : Document) : type -> Prop :=
| ScalarInput : forall ty,
    ScalarType doc ty ->
    IsInputField doc ty
| EnumInput : forall ty,
    EnumType doc ty ->
    IsInputField doc ty.
    

(* Because we are not considering InputObjects, every type is valid if it is in the document *)
Inductive IsOutputField (doc : Document) : type -> Prop :=
| OutputField : forall ty tdef,
    lookupType ty doc = Some tdef ->
    IsOutputField doc ty.




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

Inductive wfImplementsInterfaces (doc : Document) : ImplementsInterfaces -> Prop :=
| WF_SingleInterface : forall name fields,
    lookupName name doc = Some (InterfaceTypeDefinition name fields) -> 
    wfImplementsInterfaces doc (SingleInterface name)
| WF_MultipleInterfaces : forall name fields interfaces,
    lookupName name doc = Some (InterfaceTypeDefinition name fields) ->
    wfImplementsInterfaces doc interfaces ->
    wfImplementsInterfaces doc (MultipleInterfaces name interfaces).
                                                                            


Inductive wfTypeDefinition (doc : Document) : TypeDefinition -> Prop :=
| WF_Scalar : forall name,
    lookupName name doc = Some (ScalarTypeDefinition name) ->
    wfTypeDefinition doc (ScalarTypeDefinition name)
| WF_Object : forall name fields,
    lookupName name doc = Some (ObjectTypeDefinition name fields) ->
    wfFieldsDefinition doc fields ->
    wfTypeDefinition doc (ObjectTypeDefinition name fields)
| WF_ObjectWithInterfaces : forall name interfaces fields,
    lookupName name doc = Some (ObjectTypeWithInterfaces name interfaces fields) ->
    wfImplementsInterfaces doc interfaces ->
    wfFieldsDefinition doc fields ->
    wfTypeDefinition doc (ObjectTypeWithInterfaces name interfaces fields)
    
| WF_Interface : forall name fields,
    lookupName name doc = Some (InterfaceTypeDefinition name fields) ->
    wfFieldsDefinition doc fields ->
    wfTypeDefinition doc (InterfaceTypeDefinition name fields)
| WF_Union : forall name members,
    lookupName name doc = Some (UnionTypeDefinition name members) ->
    members <> [] ->
    NoDup members ->
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
    Forall (wfTypeDefinition (root, tdefs)) tdefs ->
    wfDocument (root, tdefs).




Inductive subtype (doc : Document) : type -> type -> Prop :=
| ST_Refl : forall ty, subtype doc ty ty
| ST_Trans : forall s u t,
    subtype doc s u ->
    subtype doc u t ->
    subtype doc s t
| ST_ObjectWidth : forall ty I,
    lookupType ty doc = Some (ObjectTypeWithInterfaces oname  