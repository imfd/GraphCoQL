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


Inductive FieldDefinition : Type :=
| Field : Name  -> type -> FieldDefinition
| FieldArgs : Name -> list InputValueDefinition -> type -> FieldDefinition.



(* Omitting InputObjects for now, to make it simpler *)
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



Definition lookupName (nt : Name) (doc : Document) : option TypeDefinition :=
  match doc with
    | (_ , tdefs) =>
      let n_eq nt tdef := match tdef with
                         | ScalarTypeDefinition name => beq_nat nt name
                         | ObjectTypeDefinition name _  _ => beq_nat nt name
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
| Object : forall name intfs fields,
    lookupName name doc = Some (ObjectTypeDefinition name intfs fields) ->
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
    lookupName name doc = Some (ObjectTypeDefinition name intfs fields) ->
    In (NamedType iname) intfs ->
    lookupName iname doc = Some (InterfaceTypeDefinition iname ifields) ->
    subtype doc (NamedType name) (NamedType iname)
| ST_ListType : forall ty ty',
    subtype doc ty ty' ->
    subtype doc (ListType ty) (ListType ty').
    
Definition name tdef : Name :=
  match tdef with 
  | ScalarTypeDefinition name => name
  | ObjectTypeDefinition name _ _ => name
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

Definition argNames args :=
  let extract arg := match arg with
                    | InputValue name _ => name
                    end
  in
  map extract args.


Definition fieldName fld :=
  match fld with
  | Field name _ => name
  | FieldArgs name _ _ => name
  end.

Definition fieldNames flds := map fieldName flds.


Definition fields name doc :=
  match lookupType name doc with
  | Some (ObjectTypeDefinition _ _ flds) => flds
  | Some (InterfaceTypeDefinition _ flds) => flds
  | _ => []
  end.




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


Inductive wfField (doc : Document) : FieldDefinition -> Prop :=
| WF_Field : forall name outputType,
    IsOutputField doc outputType -> 
    wfField doc (Field name outputType)
| WF_FieldArgs : forall name args outputType,
    IsOutputField doc outputType ->
    args <> [] ->
    NoDup (argNames args) ->
    Forall (wfInputValue doc) args ->
    wfField doc (FieldArgs name args outputType).
                                                                
Inductive declaresImplementation (doc : Document) : Name -> Name -> Prop :=
| ImplementsInterface : forall name iname fields intfs,
    lookupName name doc = Some (ObjectTypeDefinition name intfs fields) ->
    In (NamedType iname) intfs ->
    InterfaceType doc (NamedType iname) ->
    declaresImplementation doc name iname.


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
    fieldOk doc (Field fname ty) (Field fname ty')
| SimpleUnionField : forall fname ename ty objs,
    lookupName ename doc = Some (UnionTypeDefinition ename objs) ->
    In ty objs ->
    fieldOk doc (Field fname ty) (Field fname (NamedType ename))
            
| InterfaceFieldArgs : forall fname ty ty' args args',
    subtype doc ty ty' ->
    incl args' args ->
    fieldOk doc (FieldArgs fname args ty) (FieldArgs fname args' ty')

| UnionFieldArgs : forall fname ename ty args args' objs,
    lookupName ename doc = Some (UnionTypeDefinition ename objs) ->
    In ty objs ->
    incl args' args ->
    fieldOk doc (FieldArgs fname args ty) (FieldArgs fname args' (NamedType ename)).



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





                                                      