Require Import List.
Import ListNotations.

Require Import Coq.Arith.EqNat.


Require Export Meta.


Definition Name := nat.
Definition EnumValue := Name.

Definition NamedType := Name.

Inductive type : Type :=
| NType : NamedType -> type
| ListType : type -> type.
 

Inductive InputValueDefinition : Type :=
| InputValue : Name -> type -> InputValueDefinition.

Inductive FieldDefinition : Type :=
| Field : Name -> list InputValueDefinition -> type -> FieldDefinition.


(* Omitting InputObjects for now, to make it simpler *)
Inductive TypeDefinition : Type :=
| ScalarTypeDefinition : Name -> TypeDefinition
| ObjectTypeDefinition : Name -> list NamedType -> list FieldDefinition -> TypeDefinition
| InterfaceTypeDefinition : Name -> list FieldDefinition -> TypeDefinition
| UnionTypeDefinition : Name -> list NamedType -> TypeDefinition
| EnumTypeDefinition : Name -> list EnumValue -> TypeDefinition.
                                           

(* 
 - Omitting mutations and suscriptions, therefore only leaving query as possible operation
 - Omitting directives for simplicity

As per the spec: Directives provide a way to describe alternate runtime execution and type validation behavior in a GraphQL document. 
 *)
Definition Document := (NamedType * list TypeDefinition)%type.


Definition lookupInterface (doc : Document ) (name : Name) :=
  match doc with
  | (_ , tdefs) =>
    let i_eq n tdef := match tdef with
                      | InterfaceTypeDefinition _ _ => true
                      | _ => false
                      end
    in
    find (i_eq name) tdefs
  end.

Definition lookupInterfaces doc names := map (lookupInterface doc) names.

Definition lookupName (nt : Name) (doc : Document) : option TypeDefinition :=
  match doc with
    | (_ , tdefs) =>
      let n_eq nt tdef := match tdef with
                         | ScalarTypeDefinition name => beq_nat nt name
                         | ObjectTypeDefinition name _ _ => beq_nat nt name
                         | InterfaceTypeDefinition name _ => beq_nat nt name
                         | UnionTypeDefinition name _ => beq_nat nt name
                         | EnumTypeDefinition name _ => beq_nat nt name
                         end
      in
      find (n_eq nt) tdefs
  end.

Fixpoint lookupType (ty : type) (doc : Document) :=
  match ty with
  | NType name => lookupName name doc
  | ListType ty' => lookupType ty' doc
  end.

Definition typeName tdef : Name :=
  match tdef with 
  | ScalarTypeDefinition name => name
  | ObjectTypeDefinition name _ _ => name
  | InterfaceTypeDefinition name _ => name
  | UnionTypeDefinition name _ => name
  | EnumTypeDefinition name _ => name
  end.
  
Definition names tdefs :=  map typeName tdefs.

Definition fieldName fld := match fld with | Field name _ _ => name end.

Definition fieldsNames flds := map fieldName flds.

Definition getFields tdef :=
  match tdef with
  | ObjectTypeDefinition _ _ fields => fields
  | InterfaceTypeDefinition _ fields => fields
  | _ => []
  end.

Inductive IsInputField (doc : Document) : type -> Prop :=
| ScalarInput : forall ty sname,
    lookupType ty doc = Some (ScalarTypeDefinition sname) ->
    IsInputField doc ty
| EnumInput : forall ty ename enums,
    lookupType ty doc = Some (EnumTypeDefinition ename enums) ->
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


Inductive wfField (doc : Document) : FieldDefinition -> Prop :=
| WF_Field : forall name args outputType,
    IsOutputField doc outputType ->  
    Forall (wfInputValue doc) args ->
    wfField doc (Field name args outputType). 

Inductive subtype (doc : Document) : Name -> Name -> Prop :=
| Same : forall name i ifs iflds flds,
    lookupName name doc = Some (ObjectTypeDefinition name ifs flds) ->
    In name (fiel

Inductive wfTypeDefinition (doc : Document) : TypeDefinition -> Prop :=
| WF_Scalar : forall name,
    lookupName name doc = Some (ScalarTypeDefinition name) ->
    wfTypeDefinition doc (ScalarTypeDefinition name)
| WF_Object : forall name interfaces fields,
    lookupName name doc = Some (ObjectTypeDefinition name interfaces fields) ->
    fields <> [] ->
    NoDup (fieldsNames fields) ->
    Forall (wfField doc) fields ->
   (* (interfaces <> [] ->
     forall i iname flds,
       In i interfaces ->
       lookupName i doc = Some (InterfaceTypeDefinition iname flds) ->
       wfTypeDefinition doc (InterfaceTypeDefinition iname flds) ->
       forall f, In f flds -> In f fields ->
            
    ) ->*)
    wfTypeDefinition doc (ObjectTypeDefinition name interfaces fields)
| WF_Interface : forall name fields,
    lookupName name doc = Some (InterfaceTypeDefinition name fields) ->
    fields <> [] ->
    NoDup (fieldsNames fields) ->
    Forall (wfField doc) fields ->
    wfTypeDefinition doc (InterfaceTypeDefinition name fields)
| WF_Union : forall name members,
    lookupName name doc = Some (UnionTypeDefinition name members) ->
    members <> [] ->
    NoDup members ->
    (forall m oname ifs flds, In m members ->
                         lookupName m doc = Some (ObjectTypeDefinition oname ifs flds) ->
                         wfTypeDefinition doc (ObjectTypeDefinition oname ifs flds)) ->
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






Notation "fn : t" := (Field fn [] t)
                      (at level 99).

Notation "fn args : t" := (Field fn args t)
                           (at level 99).


Notation "'type' O 'implements' I '{{' fds '}}'" := (Object O I fds)
                                               (at level 80).

Notation "'interface' I {{ fds }}" := (Interface I [fds])
                                       (at level 79,
                                        format "'[v    ' 'interface'  I  '{{' '/' '[' fds ']' '/' '}}' ']'").
