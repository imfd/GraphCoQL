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
  Inductive Subtype schema : type -> type -> Prop :=
  | ST_Refl : forall ty, Subtype schema ty ty
                            
  | ST_Interface : forall n n',
      declares_implementation schema n n' ->
      Subtype schema (NT n) (NT n')
              
  | ST_Union : forall n n',
      n \in (union_members schema n') ->
            Subtype schema (NT n) (NT n')
                    
  | ST_ListType : forall ty ty',
      Subtype schema ty ty' ->
      Subtype schema (ListType ty) (ListType ty'). 

  Fixpoint is_subtype schema (ty ty' : type) : bool :=
    match ty, ty' with
    | (ListType lty), (ListType lty') => is_subtype schema lty lty'
    | (NT name), (NT name') => [|| (name == name'),
                               declares_implementation schema ty ty' | 
                              (name \in (union_members schema name'))]
    | _, _ => false
    end.


  Variable sch : @schema Name.

  Lemma subtypeP ty ty': reflect (Subtype sch ty ty') (is_subtype sch ty ty').
  Proof.
    apply: (iffP idP).
    elim: ty ty' => n.
      - case=>  //.
        * by move=> n' /= /or3P [/eqP -> | Hi | Hu]; [apply ST_Refl | apply ST_Interface | apply ST_Union].
        by move=> IH; case=> // => t' /= /IH; apply ST_ListType.
    elim=> //=.
      - elim=> //=.
        * by move=> *; apply/or3P; constructor 1.
      - by move=> * /=; apply/or3P; constructor 2.
      by move=> * /=; apply/or3P; constructor 3.
  Qed.
      

        
  (** The two following definitions describe whether a given type is a valid type
      for a field argument (IsValidArgumentType) and if it is a valid type for a field itself 
      (IsValidFieldType).

      In the spec they are correspondently named "IsInputField" and "IsOutputField".

      https://facebook.github.io/graphql/June2018/#sec-Input-and-Output-Types **)

  Inductive valid_argument_type schema : type -> Prop :=
  | VScalar_Arg : forall ty,
      is_scalar_type schema ty ->
      valid_argument_type schema (NT ty)
  | VEnum_Arg : forall ty,
      is_enum_type schema ty ->
      valid_argument_type schema (NT ty)
  | VList_Arg : forall ty,
      valid_argument_type schema ty ->
      valid_argument_type schema (ListType ty).
  
  Fixpoint is_valid_argument_type schema (ty : type) : bool :=
    match ty with
    | NT name => is_scalar_type schema ty || is_enum_type schema ty
    | ListType ty' => is_valid_argument_type schema ty'
    end.


  Lemma valid_argument_typeP : forall ty, reflect (valid_argument_type sch ty) (is_valid_argument_type sch ty).
  Proof.
    move=> ty; apply: (iffP idP).
    elim: ty.
      - by move=> n /orP [Hs | He]; [apply (VScalar_Arg Hs) | apply (VEnum_Arg He)].
      by move=> t IH /= /IH; apply VList_Arg.
    elim=> //.
       - by move=> n H; apply/orP; left.
       by move=> n H; apply/orP; right.
  Qed.
  
  (* Because we are not considering InputObjects, a field may have any type, 
     as long as it is declared in the Schema. *)
  Inductive valid_field_type schema : type -> Prop :=
  | VBase_Type : forall n,
      n \in schema ->
      valid_field_type schema (NT n)      
  | VList_Type : forall ty,
      valid_field_type schema ty ->
      valid_field_type schema (ListType ty).
  
  Fixpoint is_valid_field_type schema (ty : type) : bool :=
    match ty with
    | NT n => n \in schema  
    | ListType ty' => is_valid_field_type schema ty'
    end.
  

  Lemma valid_field_typeP : forall ty, reflect (valid_field_type sch ty) (is_valid_field_type sch ty).
  Proof.
    move=> ty; apply: (iffP idP); last by elim.
    elim: ty.
      by move=> n /=; apply VBase_Type.
      by move=> t H /= /H; apply VList_Type.
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
    [&& is_valid_field_type schema outputType,
     uniq (arguments_names args) &
     all (is_field_argument_wf schema) args].



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
      [&& (fname == fname'),
       perm_eq args' args &
       is_subtype schema ty ty']
    end.


  Lemma field_okP schema : forall f f', reflect (field_ok sch f f') (is_field_ok sch f f').
  Proof.
    move=> f f'; apply: (iffP idP).
    case: f => n args ty; case: f' => n' args' ty' /=.
      by move/and3P=> [/eqP -> Hperm H]; apply AnyField.
    by case=> * /=; apply/and3P.
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
  Definition implements_interface_correctly schema (objTDef : TypeDefinition) (ty' : NamedType) : bool :=
    match objTDef with
    | (ObjectTypeDefinition _ intfs fields) =>
      match lookup_type schema ty' with
      | Some (InterfaceTypeDefinition name' ifields) =>
        all (fun f' => has (fun f => is_field_ok schema f f') fields) ifields
      | _ => false
      end
    | _ => false
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
  Inductive wf_type_definition schema : TypeDefinition -> Prop :=
  | WF_Scalar : forall name, wf_type_definition schema (ScalarTypeDefinition name)
                       
  | WF_Object : forall name interfaces fields,
      fields != [::] ->
      uniq (fields_names fields) ->
      all (is_field_wf schema) fields ->
      uniq interfaces ->
      all (implements_interface_correctly schema (ObjectTypeDefinition name interfaces fields)) interfaces ->
      wf_type_definition schema (ObjectTypeDefinition name interfaces fields)
                       
  | WF_Interface : forall name fields,
      fields != [::] ->
      uniq (fields_names fields) ->
      all (is_field_wf schema) fields ->
      wf_type_definition schema (InterfaceTypeDefinition name fields)
                       
  | WF_Union : forall name members,
      members != [::] ->
      uniq members ->
      all (is_object_type schema) members ->
      wf_type_definition schema (UnionTypeDefinition name members)
                       
  | WF_Enum : forall name enumValues,
      enumValues != [::] ->
      uniq enumValues ->
      wf_type_definition schema (EnumTypeDefinition name enumValues).


  Fixpoint is_type_def_wf schema (tdef : TypeDefinition) : bool :=
    match tdef with
    | ScalarTypeDefinition _ => true
                                 
    | ObjectTypeDefinition name interfaces fields =>
      [&& (fields != [::]),
       uniq (fields_names fields),
       all (is_field_wf schema) fields,
       uniq interfaces &
       all (implements_interface_correctly schema tdef) interfaces]

    | InterfaceTypeDefinition _ fields =>
      [&& (fields != [::]),
       uniq (fields_names fields) &
       all (is_field_wf schema) fields]

    | UnionTypeDefinition name members =>
      [&& (members != [::]),
       uniq members &
       all (is_object_type schema) members]

    | EnumTypeDefinition _ enumValues =>
      (enumValues != [::]) && uniq enumValues
        
    end.


  Lemma wf_type_definitionP schema : forall tdef, reflect (wf_type_definition sch tdef) (is_type_def_wf sch tdef).
  Proof.
    move=> tdef; apply (iffP idP).
    case: tdef; move=> n //=.
      by move=> _; apply WF_Scalar.
      by move=> intfs flds /and5P [H1 H2 H3 H4 H']; apply WF_Object.
      by move=> flds /and3P [H1 H2 H3]; apply WF_Interface.  
      by move=> mbs /and3P [H1 H2 H3]; apply WF_Union.
      by move=> es /andP [H1 H2]; apply WF_Enum.
    by case => // * /=; [apply/and5P | apply/and3P | apply/and3P | apply/andP].
  Qed.
  
  Definition is_schema_wf schema : bool :=
    let: Schema query_type tdefs := schema in
    [&& (query_type \in schema),
     is_object_type schema query_type,
     uniq (type_defs_names tdefs) &                   
     all (is_type_def_wf schema) tdefs].
      
  
  Structure wfSchema := WFSchema {
                        schema : @schema Name ;
                        hasType :  Name -> Vals -> bool;
                        _ : is_schema_wf schema;
                      }.


  Coercion schema : wfSchema >-> Schema.schema.


  Lemma query_type_object_schema schema :
    is_schema_wf schema ->
    is_object_type schema schema.(query_type).
  Proof.
    case: schema => query_type tdefs.
    rewrite /is_schema_wf.
      by move/and4P=> [_ Hobj _ _].
  Qed.

  Lemma query_type_object_wf_schema (schema : wfSchema) :
    is_object_type schema schema.(query_type).
  Proof. case: schema => schema Ht H.
    by apply: (query_type_object_schema H).
  Qed.

        
End WellFormedness.


Arguments wfSchema [Name Vals].