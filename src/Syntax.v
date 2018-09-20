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

Definition lookupName (nt : Name) (doc : Document) :=
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

Definition typeName tdef :=
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
    
Inductive wfTypeDefinition (doc : Document) : TypeDefinition -> Prop :=
| WF_Scalar : forall name,
    lookupName name doc = Some (ScalarTypeDefinition name) ->
    wfTypeDefinition doc (ScalarTypeDefinition name)
| WF_Object : forall name interfaces fields,
    lookupName name doc = Some (ObjectTypeDefinition name interfaces fields) ->
    fields <> [] ->
    NoDup (fieldsNames fields) ->
    Forall (wfField doc) fields ->
    Forall (wfTypeDefinition doc) (lookupInterfaces doc interfaces) ->
    (forall interface, In interface interfaces -> forall fld, In fld (getFields interface) ->
                                                     In fld fields)
    wfTypeDefinition doc (ObjectTypeDefinition name interfaces fields).
| WF_Interface : forall name fields,
    lookup name doc = Some (InterfaceTypeDefinition name fields) ->
    fields <> [] ->
    NoDup (fieldNames fields) ->
    Forall (wfField doc) fields ->
    wfTypeDefinition doc (InterfaceTypeDefinition name fields).
           
Inductive wfDocument : Document -> Prop :=
| WF_Document : forall tdefs root,
    NoDup (names tdefs) ->
    In root (names tdefs) -> 
    Forall (wfTypeDefinition (root, tdefs)) tdefs ->
    wfDocument (root, tdefs).




(*
======
Types
======
*)

Inductive ty : Type :=
| TScalar : scalar_id -> ty
| TEnum : enum_id -> ty
| TObject : object_id -> ty
| TInterface : interface_id -> ty
(*| TUnion : union_id -> ty    *)                             
| TList : ty -> ty.




(*
========
Program
========
*)

Inductive fieldDecl : Type :=
  | Field : field_id -> list (var * ty) -> ty -> fieldDecl.


Inductive objectDecl : Type :=
  | Object : object_id -> interface_id -> list fieldDecl -> objectDecl.	(* Only one interface *)


Inductive interfaceDecl : Type :=
  | Interface : interface_id -> list fieldDecl -> interfaceDecl.  (* Omitting interface implementing other interfaces *)	

Inductive scalarDecl : Type :=
  | Scalar : scalar_id -> scalarDecl.

Inductive enumDecl : Type :=
  | Enum : enum_id -> enumDecl.   

(*Inductive unionDecl : Type :=
  | Union : *)

Definition schema := (list objectDecl * list interfaceDecl * list scalarDecl * list enumDecl)%type.	





Definition objectLookup (S : schema) (obj : object_id) : option objectDecl :=
  match S with
    | (objs, _, _, _) =>
      let o_eq o ob := match ob with
                          | Object o' _ _ => beq_nat o o'
                        end
      in
      find (o_eq obj) objs
  end.

Definition interfaceLookup (S : schema) (i : interface_id) : option interfaceDecl :=
  match S with
    | (_, ifs, _, _) =>
      let i_eq i intr := match intr with
                          | Interface i' _ => beq_nat i i'
                        end
      in
      find (i_eq i) ifs
  end.

Definition scalarLookup (S : schema) (s : scalar_id) : option scalarDecl :=
  match S with
  | (_, _, ss, _) =>
    let s_eq s sclr := match sclr with
                          | Scalar s' => beq_nat s s'
                        end
      in
    find (s_eq s) ss
  end.

Definition enumLookup (S : schema) (e : enum_id) : option enumDecl :=
  match S with
  | (_, _, _, ens) =>
    let en_eq e enms := match enms with
                          | Enum e' => beq_nat e e'
                        end
      in
    find (en_eq e) ens
  end.


Definition fieldLookup (fs : list fieldDecl) (f : field_id) :=
  let f_eq f fld := match fld with
                   | Field f' _ _ => beq_nat f f'
                   end
  in
  find (f_eq f) fs.


Inductive fields (S : schema) : ty -> list fieldDecl -> Prop :=
| Fields_Object :
  forall o i fs,
    objectLookup S o = Some (Object o i fs) ->
    fields S (TObject o) fs
| Fields_Interface :
    forall i fs,
      interfaceLookup S i = Some (Interface i fs) ->
      fields S (TInterface i) fs.


Definition get_fields (S : schema) (t : ty) :=
  match t with
  | TObject o => match objectLookup S o with
                | Some (Object _ _ fs) => Some fs
                | None => None
                end
  | TInterface i => match interfaceLookup S i with
                   | Some (Interface _ fs) => Some fs
                   | None => None
                   end
  (*| TList t' => fields S t'*)
  | _ => None
  end. 



(*
-------
Types
-------
*)

Inductive wfType (S : schema) : ty -> Prop :=
  | WF_TObject :
      forall o,
        objectLookup S o <> None ->
        wfType S (TObject o)
  | WF_TInterface :
      forall i,
        interfaceLookup S i <> None ->
        wfType S (TInterface i)
  | WF_TScalar :
      forall s,
        scalarLookup S s <> None ->
        wfType S (TScalar s)
  | WF_TEnum :
      forall e,
        enumLookup S e <> None ->
        wfType S (TEnum e).


Inductive subtypeOf (S : schema) : ty -> ty -> Prop :=
  | Sub_Class :
      forall o i fs,
        objectLookup S o = Some (Object o i fs) ->
        subtypeOf S (TObject o) (TInterface i)
 
  | Sub_Refl :
      forall t,
        wfType S t ->
        subtypeOf S t t
  | Sub_Trans :
      forall t1 t2 t3,
        subtypeOf S t1 t2 ->
        subtypeOf S t2 t3 ->
        subtypeOf S t1 t3.


(*
-------
 Well-formedness
-------
*)

Inductive wfField (S : schema) : fieldDecl -> Prop :=
  | WF_Field :
      forall f args t,
        (forall x, In x args -> wfType S (snd x)) ->   (* Otra forma? *)
        wfType S t ->
        wfField S (Field f args t).

Inductive wfInterface (S : schema) : interfaceDecl -> Prop :=
  | WF_Interface :
      forall i fs,
        Forall (wfField S) fs ->
        wfInterface S (Interface i fs).
 


Inductive wfObject (S : schema) : objectDecl -> Prop :=
  | WF_Object :
      forall o i fs ifs,
        fields S (TInterface i) ifs ->
        incl ifs fs ->
        Forall (wfField S) fs ->
        wfObject S (Object o i fs).

Inductive wfSchema : schema -> Prop :=
  | WF_Schema :
      forall objs ifs scs ens,
        Forall (wfObject (objs, ifs, scs, ens)) objs ->
        Forall (wfInterface (objs, ifs, scs, ens)) ifs ->
        wfSchema (objs, ifs, scs, ens).


Notation "fn : t" := (Field fn [] t)
                      (at level 99).

Notation "fn args : t" := (Field fn args t)
                           (at level 99).


Notation "'type' O 'implements' I '{{' fds '}}'" := (Object O I fds)
                                               (at level 80).

Notation "'interface' I {{ fds }}" := (Interface I [fds])
                                       (at level 79,
                                        format "'[v    ' 'interface'  I  '{{' '/' '[' fds ']' '/' '}}' ']'").
