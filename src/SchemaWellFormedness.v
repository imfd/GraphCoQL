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
  | ST_Interface : forall n n',
      declares_implementation schema (NamedType n) (NamedType n') ->
      subtype schema (NamedType n) (NamedType n')
  | ST_Union : forall n n',
      (NamedType n) \in (union_members schema (NamedType n')) ->
      subtype schema (NamedType n) (NamedType n')
  | ST_ListType : forall ty ty',
      subtype schema ty ty' ->
      subtype schema (ListType ty) (ListType ty'). 

  Fixpoint is_subtype schema (ty ty' : type) : bool :=
    match ty, ty' with
    | (ListType lty), (ListType lty') => is_subtype schema lty lty'
    | (NamedType name), (NamedType name') => (name == name') ||
                                            declares_implementation schema ty ty' || 
                                            (ty \in (union_members schema ty'))
    | _, _ => false
    end.


  Variable sch : @schema Name.

  Lemma subtypeP : forall ty ty', reflect (subtype sch ty ty') (is_subtype sch ty ty').
  Proof.
    move=> ty ty'; apply: (iffP idP).
    move: ty'; elim: ty => n.
    case=>  //.
      by move=> n' /=; move/orP=> [/orP [/eqP -> | Hi] | Hu]; [apply ST_Refl | apply ST_Interface | apply ST_Union].
      by move=> IH; case=> // => t' /= /IH; apply ST_ListType.
    elim=> //=.
      elim=> //=.
      by move=> n; rewrite eqxx.
      by move=> n n' H; apply Bool.orb_true_intro; left; apply Bool.orb_true_intro; right.
      by move=> n n' H; apply Bool.orb_true_intro; right.
  Qed.
      

        
  (** The two following definitions describe whether a given type is a valid type
      for a field argument (IsValidArgumentType) and if it is a valid type for a field itself 
      (IsValidFieldType).

      In the spec they are correspondently named "IsInputField" and "IsOutputField".

      https://facebook.github.io/graphql/June2018/#sec-Input-and-Output-Types **)

  Inductive valid_argument_type schema : type -> Prop :=
  | VScalar_Arg : forall ty,
      is_scalar_type schema ty ->
      valid_argument_type schema ty
  | VEnum_Arg : forall ty,
      is_enum_type schema ty ->
      valid_argument_type schema ty
  | VList_Arg : forall ty,
      valid_argument_type schema ty ->
      valid_argument_type schema (ListType ty).
  
  Fixpoint is_valid_argument_type schema (ty : type) : bool :=
    match ty with
    | NamedType _ => is_scalar_type schema ty || is_enum_type schema ty
    | ListType ty' => is_valid_argument_type schema ty'
    end.


  Lemma valid_argument_typeP : forall ty, reflect (valid_argument_type sch ty) (is_valid_argument_type sch ty).
  Proof.
    move=> ty; apply: (iffP idP).
    elim: ty.
      by move=> n; move/orP=> [Hs | He]; [apply (VScalar_Arg Hs) | apply (VEnum_Arg He)].
      by move=> t IH /= /IH; apply VList_Arg.
    elim.
       by case=> //; move=> n H; apply Bool.orb_true_iff; left.
       by case=> //; move=> n H; apply Bool.orb_true_iff; right.
       by case.
  Qed.
  
  (* Because we are not considering InputObjects, a field may have any type, 
     as long as it is declared in the Schema. *)
  Inductive valid_field_type schema : type -> Prop :=
  | VBase_Type : forall n,
      lookup_type schema (NamedType n) != None ->
      valid_field_type schema (NamedType n)      
  | VList_Type : forall ty,
      valid_field_type schema ty ->
      valid_field_type schema (ListType ty).
  
  Fixpoint is_valid_field_type schema (ty : type) : bool :=
    match ty with
    | NamedType _ => ~~ ((lookup_type schema ty) == None)
    | ListType ty' => is_valid_field_type schema ty'
    end.
  

  Lemma valid_field_typeP : forall ty, reflect (valid_field_type sch ty) (is_valid_field_type sch ty).
  Proof.
    move=> ty; apply: (iffP idP); last by elim.
    elim: ty.
      move=> n /=. apply VBase_Type.
      move=> t H /= /H; apply VList_Type.
  Qed.

  
  (** 
      It checks whether an argument is well-formed by checking that
      its type is a valid type for an argument **)
  Definition is_field_argument_wf schema (argDef : FieldArgumentDefinition) : bool :=
    let: FieldArgument aname ty := argDef in is_valid_argument_type schema ty.

  
  (**
     It states whether a field is well-formed.

                 ty isValidFieldType
                  NoDuplicates args
           ∀ arg ∈ args, arg isWellFormed
           ------------------------------
           (fname (args) : ty) isAWellFormedField
   **)
  Definition is_field_wf schema (fld : FieldDefinition) : bool :=
    let: Field name args outputType := fld in
    is_valid_field_type schema outputType &&
                     uniq (arguments_names args) &&
                     all (is_field_argument_wf schema) args.



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
  Inductive field_ok schema : FieldDefinition -> FieldDefinition -> Prop :=              
  | AnyField : forall ty ty' fname args args',
      is_subtype schema ty ty' ->
      perm_eq args' args ->
      field_ok schema (Field fname args ty) (Field fname args' ty').

  Definition is_field_ok schema (fld fld' : @FieldDefinition Name) : bool :=
    match fld, fld' with
    | Field fname args ty, Field fname' args' ty' =>
      (fname == fname') &&
      perm_eq args' args &&
      is_subtype schema ty ty'
    end.


  Lemma field_okP schema : forall f f', reflect (field_ok sch f f') (is_field_ok sch f f').
  Proof.
    move=> f f'; apply: (iffP idP).
    case: f => n args ty; case: f' => n' args' ty' /=.
      by move/andP=> [/andP [/eqP -> Hperm] H]; apply AnyField.
    case.
      move=> ty ty' fname args args' Hs Hp /=; rewrite eqxx => /=.
      by apply andb_true_intro; split.
  Qed.

  
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
  Definition implements_interface_correctly schema (objTDef : TypeDefinition) (ty' : type) : bool :=
    match objTDef, ty' with
    | (ObjectTypeDefinition _ intfs fields), (NamedType name') =>
      match lookup_type schema ty' with
      | Some (InterfaceTypeDefinition name' ifields) =>
        all (fun f' => has (fun f => is_field_ok schema f f') fields) ifields
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
  Inductive wfTypeDefinition schema : TypeDefinition -> Prop :=
  | WF_Scalar : forall name, wfTypeDefinition schema (ScalarTypeDefinition name)
                       
  | WF_Object : forall name interfaces fields,
      fields <> [] ->
      uniq (fields_names fields) ->
      all (is_field_wf schema) fields ->
      uniq (types_names interfaces) ->
      all (implements_interface_correctly schema (ObjectTypeDefinition name interfaces fields)) interfaces ->
      wfTypeDefinition schema (ObjectTypeDefinition name interfaces fields)
                       
  | WF_Interface : forall name fields,
      fields <> [] ->
      uniq (fields_names fields) ->
      all (is_field_wf schema) fields ->
      wfTypeDefinition schema (InterfaceTypeDefinition name fields)
                       
  | WF_Union : forall name members,
      members <> [] ->
      uniq (types_names members) ->
      all (is_object_type schema) members ->
      wfTypeDefinition schema (UnionTypeDefinition name members)
                       
  | WF_Enum : forall name enumValues,
      enumValues <> [] ->
      uniq enumValues ->
      wfTypeDefinition schema (EnumTypeDefinition name enumValues).


  Fixpoint is_type_def_wf schema (tdef : TypeDefinition) : bool :=
    match tdef with
    | ScalarTypeDefinition _ => true
    | ObjectTypeDefinition name interfaces fields =>
      (fields != [::])
        && uniq (fields_names fields)
        && all (is_field_wf schema) fields
        && uniq (types_names interfaces)
        && all (implements_interface_correctly schema tdef) interfaces
    | InterfaceTypeDefinition _ fields =>
      (fields != [::])
        &&  uniq (fields_names fields)
        && all (is_field_wf schema) fields
    | UnionTypeDefinition name members =>
      (members != [::])
        && uniq (types_names members)
        && all (is_object_type schema) members
    | EnumTypeDefinition _ enumValues =>
      (enumValues != [::]) && uniq enumValues
        
    end.
                
                                     

                 
  Definition is_schema_wf schema : bool :=
    let: Schema query_type tdefs := schema in
    match query_type with
    | (NamedType name) =>
      (name \in (type_defs_names tdefs)) &&
       uniq (type_defs_names tdefs) &&                              
       all (is_type_def_wf schema) tdefs                                                            
    | _ => false
    end
  .
      
  
  Structure wfSchema := WFSchema {
                        schema : @schema Name ;
                        hasType :  Name -> Vals -> bool;
                        _ : is_schema_wf schema;
                      }.


  Coercion schema_from_wfSchema (wfschema : wfSchema) := let: WFSchema schema _ _ := wfschema in schema.

End WellFormedness.


Arguments wfSchema [Name Vals].