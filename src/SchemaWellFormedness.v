From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import List.
Import ListNotations.

Require Import Syntax.


Section WellFormedness.

  Variable Name : finType.

  
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
      subtype doc (ListType ty) (@ListType Name ty').

  
  (** The two following definitions describe whether a given type is a valid type
      for a field argument (IsValidArgumentType) and if it is a valid type for a field itself 
      (IsValidFieldType).

      In the spec they are correspondently named "IsInputField" and "IsOutputField".

      https://facebook.github.io/graphql/June2018/#sec-Input-and-Output-Types **)

  Fixpoint isValidArgumentType (doc : Document) (ty : type) : bool :=
    match ty with
    | NamedType _ => ScalarType doc ty || @EnumType Name doc ty
    | ListType ty' => isValidArgumentType doc ty'
    end.
    

  (* Because we are not considering InputObjects, a field may have any type, 
     as long as it is declared in the document.

     Not really sure how to name this case... Named seems weird? *)
  Fixpoint isValidFieldType (doc : Document) (ty : type) : bool :=
    match ty with
    | NamedType n => match @lookupName Name n doc with
                    | Some tdef => true
                    | _ => false
                    end
    | ListType ty' => isValidFieldType doc ty'
    end.
  


  Definition wfFieldArgument (doc : Document) (argDef : FieldArgumentDefinition) : bool :=
    let: FieldArgument aname ty := argDef in isValidArgumentType doc ty.

  
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
      fieldOk doc (FieldWithArgs fname args ty) (FieldWithArgs fname args' (@NamedType Name ename)).



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




End WellFormedness.