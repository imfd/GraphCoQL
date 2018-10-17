From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import List.
Import ListNotations.

Require Import Schema.
Require Import SchemaAux.


Section WellFormedness.

  Variables Name Vals : finType.

  Implicit Type schema : @schema Name.
  
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
  Inductive subtype schema : type -> type -> Prop :=
  | ST_Refl : forall ty, subtype schema ty ty
  | ST_Object : forall name intfs iname fields ifields,
      lookupName schema name = Some (ObjectTypeDefinition name intfs fields) ->
      In (NamedType iname) intfs ->
      lookupName schema iname = Some (InterfaceTypeDefinition iname ifields) ->
      subtype schema (NamedType name) (NamedType iname)
  | ST_ListType : forall ty ty',
      subtype schema ty ty' ->
      subtype schema (ListType ty) (@ListType Name ty').

  
  (** The two following definitions describe whether a given type is a valid type
      for a field argument (IsValidArgumentType) and if it is a valid type for a field itself 
      (IsValidFieldType).

      In the spec they are correspondently named "IsInputField" and "IsOutputField".

      https://facebook.github.io/graphql/June2018/#sec-Input-and-Output-Types **)

  Fixpoint isValidArgumentType schema (ty : type) : bool :=
    match ty with
    | NamedType _ => isScalarType schema ty || @isEnumType Name schema ty
    | ListType ty' => isValidArgumentType schema ty'
    end.
    

  (* Because we are not considering InputObjects, a field may have any type, 
     as long as it is declared in the Schema. *)
  Fixpoint isValidFieldType schema (ty : type) : bool :=
    match ty with
    | NamedType n => match lookupName schema n with
                    | Some tdef => true
                    | _ => false
                    end
    | ListType ty' => isValidFieldType schema ty'
    end.
  


  (** 
      It checks whether an argument is well-formed by checking that
      its type is a valid type for an argument **)
  Definition wfFieldArgument schema (argDef : FieldArgumentDefinition) : bool :=
    let: FieldArgument aname ty := argDef in isValidArgumentType schema ty.

  
  (**
     It states whether a field is well-formed.

                 ty isValidFieldType
                  NoDuplicates args
           ∀ arg ∈ args, arg isWellFormed
           ------------------------------
           (fname (args) : ty) isAWellFormedField
  **)
  Inductive wfField schema : FieldDefinition -> Prop :=
  | WF_Field : forall name args outputType,
      isValidFieldType schema outputType ->
      NoDup (argNames args) ->               (* This is not actually explicit in the spec I believe *)
      Forall (wfFieldArgument schema) args ->
      wfField schema (Field name args outputType).



  (** This checks whether an object field is valid w/r to another from an implemented interface.
      The possible options are:


    3.      T <: U     ∀ arg ∈ args', arg ∈ args          
            -------------------------------------------
             (fname (args) : T) OK (fname (args') : U)

    4.      T ∈ unionTypes(U)     ∀ arg ∈ args', arg ∈ args
           --------------------------------------------------------
                 (fname (args) : T) OK (fname (args') : U)


    The arguments have to be completed included, both their names and types (invariant).

   **)
  Inductive fieldOk schema : FieldDefinition -> FieldDefinition -> Prop :=              
  | InterfaceField : forall fname ty ty' args args',
      subtype schema ty ty' ->
      incl args' args ->
      fieldOk schema (Field fname args ty) (Field fname args' ty')
              
  | UnionField : forall fname ename ty args args' objs,
      lookupName schema ename = Some (UnionTypeDefinition ename objs) ->
      In ty objs ->
      incl args' args ->
      fieldOk schema (Field fname args ty) (Field fname args' (@NamedType Name ename)).



  (**
     This checks whether an object type implements correctly an interface, 
     by properly defining every field defined in the interface.


            Schema(O) = type O implements ... I ... { Flds }   
                    Schema(I) = interface I { Flds' }
                 ∀ fld' ∈ Flds', ∃ fld ∈ Flds s.t fld OK fld'
            ------------------------------------------------
                        O implementsOK I

   **)
  Inductive implementsOK schema : type -> type -> Prop :=
  | ImplementsAll : forall name intfs fields iname ifields,
      lookupName schema name = Some (ObjectTypeDefinition name intfs fields) ->
      In (NamedType iname) intfs ->
      lookupName schema iname = Some (InterfaceTypeDefinition iname ifields) ->
      (forall ifld, In ifld ifields ->
               exists ofld, In ofld fields ->
                       fieldOk schema ofld ifld)  ->
      implementsOK schema (NamedType name) (NamedType iname).
  


  (**

                       Schema(S) = scalar S 
                       -----------------------
                           scalar S OK


                 Schema(O) = type O implements Ifs { Flds }
                           notEmpty Flds
                         NoDuplicates Flds
                            Flds OK in O
                            Ifs OK in O
                -----------------------------------------
                          type O { Flds } 



                    Schema(I) = interface I { Flds }
                           notEmpty Flds
                         NoDuplicates Flds
                            Flds OK in I
                ----------------------------------------
                        interface I { Flds } 



                       Schema(U) = union U { Mbs }
                           notEmpty Mbs
                         NoDuplicates Mbs
                     ∀ mb ∈ Mbs, mb ObjectType
                -----------------------------------------
                          union U { Mbs } 


                       Schema(E) = enum E { Evs }
                           notEmpty Evs
                         NoDuplicates Evs
                -----------------------------------------
                          enum E { Evs } 

   **)
  Inductive wfTypeDefinition schema : TypeDefinition -> Prop :=
  | WF_Scalar : forall name,
      isScalarType schema (NamedType name) ->
      wfTypeDefinition schema (ScalarTypeDefinition name)
                       
  | WF_ObjectWithInterfaces : forall name interfaces fields,
      lookupName schema name = Some (ObjectTypeDefinition name interfaces fields) ->
      fields <> [] ->
      NoDup (fieldNames fields) ->
      Forall (wfField schema) fields ->
      NoDup (typesNames interfaces) ->
      Forall (implementsOK schema (NamedType name)) interfaces ->
      wfTypeDefinition schema (ObjectTypeDefinition name interfaces fields)
                       
  | WF_Interface : forall name fields,
      lookupName schema name = Some (InterfaceTypeDefinition name fields) ->
      fields <> [] ->
      NoDup (fieldNames fields) ->
      Forall (wfField schema) fields ->
      wfTypeDefinition schema (InterfaceTypeDefinition name fields)
                       
  | WF_Union : forall name members,
      lookupName schema name = Some (UnionTypeDefinition name members) ->
      members <> [] ->
      NoDup (typesNames members) ->
      Forall (isObjectType schema) members ->
      wfTypeDefinition schema (UnionTypeDefinition name members)
                       
  | WF_Enum : forall name enumValues,
      lookupName schema name = Some (EnumTypeDefinition name enumValues) ->
      enumValues <> [] ->
      NoDup enumValues ->
      wfTypeDefinition schema (EnumTypeDefinition name enumValues).
  
           
  Inductive schemaIsWellFormed : @schema Name -> Prop :=
  | WF_Schema : forall tdefs root,
      NoDup (typeDefsNames tdefs) ->
      In root (typeDefsNames tdefs) -> 
      Forall (wfTypeDefinition (Schema (NamedType root) tdefs)) tdefs ->
      schemaIsWellFormed (Schema (NamedType root) tdefs).

  
  Record wfSchema := WFSchema {
                        schema : @schema Name ;
                        hasType :  Name -> Vals -> bool;
                        _ : schemaIsWellFormed schema;
                      }.


  Coercion schema_from_wfSchema (wfschema : wfSchema) := let: WFSchema schema _ _ := wfschema in schema.

End WellFormedness.

