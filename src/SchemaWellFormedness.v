From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From extructures Require Import ord.

Require Import List.
Import ListNotations.

Require Import Schema.
Require Import SchemaAux.


Section WellFormedness.

  Variables (Name Vals : ordType).

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
  | ST_Object : forall n n',
      declares_implementation schema (NamedType n) (NamedType n') ->
      subtype schema (NamedType n) (NamedType n')
  | ST_ListType : forall ty ty',
      subtype schema ty ty' ->
      subtype schema (ListType ty) (ListType ty'). 

  Fixpoint is_subtype schema (ty ty' : type) : bool :=
    match ty, ty' with
    | (ListType lty), (ListType lty') => is_subtype schema lty lty'
    | (NamedType name), (NamedType name') => if name == name' then
                                              true
                                            else
                                              declares_implementation schema ty ty'
    | _, _ => false
    end.


  Variable sch : @schema Name.

  Lemma subtypeP : forall ty ty', reflect (subtype sch ty ty') (is_subtype sch ty ty').
  Proof.
    move=> ty ty'; apply: (iffP idP).
    move: ty'; elim: ty => n.
    case => //.
      move=> n' /=.
      case E: (n == n').
        by move/eqP: E => -> _; apply ST_Refl.
        by apply ST_Object.
      by move=> IH; case=> // => t' /= /IH; apply ST_ListType.
    elim.
      elim=> //.
        by move=> n /=; rewrite (_ : n == n).
      move=> n n' H /=.
        by case (n == n').
      by [].
  Qed.
      

        
  (** The two following definitions describe whether a given type is a valid type
      for a field argument (IsValidArgumentType) and if it is a valid type for a field itself 
      (IsValidFieldType).

      In the spec they are correspondently named "IsInputField" and "IsOutputField".

      https://facebook.github.io/graphql/June2018/#sec-Input-and-Output-Types **)

  Fixpoint isValidArgumentType schema (ty : type) : bool :=
    match ty with
    | NamedType _ => is_scalar_type schema ty || is_enum_type schema ty
    | ListType ty' => isValidArgumentType schema ty'
    end.
    

  (* Because we are not considering InputObjects, a field may have any type, 
     as long as it is declared in the Schema. *)
  Fixpoint isValidFieldType schema (ty : type) : bool :=
    match ty with
    | NamedType _ => match lookup_type schema ty with
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
  Definition wfField schema (fld : FieldDefinition) : bool :=
    let: Field name args outputType := fld in
    isValidFieldType schema outputType &&
                     uniq (arguments_names args) &&
                     all (wfFieldArgument schema) args.



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
      is_subtype schema ty ty' ->
      incl args' args ->
      fieldOk schema (Field fname args ty) (Field fname args' ty')
              
  | UnionField : forall fname ename ty args args' objs,
      lookup_type schema ename = Some (UnionTypeDefinition ename objs) ->
      ty \in objs ->
      incl args' args ->
      fieldOk schema (Field fname args ty) (Field fname args' (@NamedType Name ename)).

  Definition isFieldOK schema (fld fld' : @FieldDefinition Name) : bool :=
    match fld, fld' with
    | Field fname args ty, Field fname' args' ty' =>
      if fname == fname' then
        all (fun x => x \in args) args' &&
            match ty' with
            | (NamedType _) => match lookup_type schema ty' with
                                  | Some (UnionTypeDefinition _ objs) => ty \in objs
                                  | _ => is_subtype schema ty ty'
                                  end
            | _ => is_subtype schema ty ty'
            end
      else
        false
    end.

  (**
     This checks whether an object type implements correctly an interface, 
     by properly defining every field defined in the interface.


            Schema(O) = type O implements ... I ... { Flds }   
                    Schema(I) = interface I { Flds' }
                 ∀ fld' ∈ Flds', ∃ fld ∈ Flds s.t fld OK fld'
            ------------------------------------------------
                        O implementsOK I

   **)
 (* Inductive implementsOK schema : type -> type -> Prop :=
  | ImplementsAll : forall name intfs fields iname ifields,
      lookupName schema name = Some (ObjectTypeDefinition name intfs fields) ->
      In (NamedType iname) intfs ->
      lookupName schema iname = Some (InterfaceTypeDefinition iname ifields) ->
      (forall ifld, In ifld ifields ->
               exists ofld, In ofld fields ->
                       fieldOk schema ofld ifld)  ->
      implementsOK schema (NamedType name) (NamedType iname).

*)
  Definition implementsOK schema (objTDef : TypeDefinition) (ty' : type) : bool :=
    match objTDef, ty' with
    | (ObjectTypeDefinition _ intfs fields), (NamedType name') =>
      (ty' \in intfs)
        &&  match lookup_type schema ty' with
            | Some (InterfaceTypeDefinition name' ifields) =>
              all (fun f' => has (fun f => isFieldOK schema f f') fields) ifields
            | _ => false
            end
    | _, _ => false
    end.


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
 (* Inductive wfTypeDefinition schema : TypeDefinition -> Prop :=
  | WF_Scalar : forall name,
      isScalarType schema (NamedType name) ->
      wfTypeDefinition schema (ScalarTypeDefinition name)
                       
  | WF_ObjectWithInterfaces : forall name interfaces fields,
      lookupName schema name = Some (ObjectTypeDefinition name interfaces fields) ->
      fields <> [] ->
      uniq (fieldNames fields) ->
      Forall (wfField schema) fields ->
      uniq (typesNames interfaces) ->
      Forall (implementsOK schema (NamedType name)) interfaces ->
      wfTypeDefinition schema (ObjectTypeDefinition name interfaces fields)
                       
  | WF_Interface : forall name fields,
      lookupName schema name = Some (InterfaceTypeDefinition name fields) ->
      fields <> [] ->
      uniq (fieldNames fields) ->
      Forall (wfField schema) fields ->
      wfTypeDefinition schema (InterfaceTypeDefinition name fields)
                       
  | WF_Union : forall name members,
      lookupName schema name = Some (UnionTypeDefinition name members) ->
      members <> [] ->
      uniq (typesNames members) ->
      Forall (isObjectType schema) members ->
      wfTypeDefinition schema (UnionTypeDefinition name members)
                       
  | WF_Enum : forall name enumValues,
      lookupName schema name = Some (EnumTypeDefinition name enumValues) ->
      enumValues <> [] ->
      uniq enumValues ->
      wfTypeDefinition schema (EnumTypeDefinition name enumValues).*)


  Fixpoint isWFTypeDef schema (tdef : TypeDefinition) : bool :=
    match tdef with
    | ScalarTypeDefinition _ => true
    | ObjectTypeDefinition name interfaces fields =>
      (fields != [::])
        && uniq (fields_names fields)
        && all (wfField schema) fields
        && uniq (types_names interfaces)
        && all (implementsOK schema tdef) interfaces
    | InterfaceTypeDefinition _ fields =>
      (fields != [::])
        &&  uniq (fields_names fields)
        && all (wfField schema) fields
    | UnionTypeDefinition name members =>
      (members != [::])
        && uniq (types_names members)
        && all (is_object_type schema) members
    | EnumTypeDefinition _ enumValues =>
      (enumValues != [::]) && uniq enumValues
        
    end.
                
                                     

                 
  Definition schemaIsWF schema : bool :=
    match schema with
    | Schema query tdefs => match query with
                           | (NamedType root) =>
                             (root \in (type_defs_names tdefs)) &&
                             uniq (type_defs_names tdefs) &&                              
                             all (isWFTypeDef schema) tdefs                                                            
                           | _ => false
                           end
    end.
      
  
  Structure wfSchema := WFSchema {
                        schema : @schema Name ;
                        hasType :  Name -> Vals -> bool;
                        _ : schemaIsWF schema;
                      }.


  Coercion schema_from_wfSchema (wfschema : wfSchema) := let: WFSchema schema _ _ := wfschema in schema.

End WellFormedness.


Arguments wfSchema [Name Vals].