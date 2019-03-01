From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From extructures Require Import ord fset.


Require Import Schema.
Require Import SchemaAux.


Section WellFormedness.

  Variables (Name Vals : ordType).
  Variable sch : @schema Name.


  
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
  Inductive Subtype : type -> type -> Prop :=
  | ST_Refl : forall ty, Subtype ty ty
                            
  | ST_Interface : forall n n',
      declares_implementation sch n n' ->
      Subtype (NT n) (NT n')
              
  | ST_Union : forall n n',
      (n \in (union_members sch n')) ->
      Subtype (NT n) (NT n')
                    
  | ST_ListType : forall ty ty',
      Subtype ty ty' ->
      Subtype (ListType ty) (ListType ty'). 

  Fixpoint is_subtype (ty ty' : type) : bool :=
    match ty, ty' with
    | (ListType lty), (ListType lty') => is_subtype lty lty'
    | (NT name), (NT name') => [|| (name == name'),
                               declares_implementation sch ty ty' | 
                              (name \in (union_members sch name'))]
    | _, _ => false
    end.

   Lemma subtypeP ty ty': reflect (Subtype ty ty') (is_subtype ty ty').
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

  Inductive valid_argument_type : type -> Prop :=
  | VScalar_Arg : forall ty,
      is_scalar_type sch ty ->
      valid_argument_type (NT ty)
  | VEnum_Arg : forall ty,
      is_enum_type sch ty ->
      valid_argument_type (NT ty)
  | VList_Arg : forall ty,
      valid_argument_type ty ->
      valid_argument_type (ListType ty).
  
  Fixpoint is_valid_argument_type (ty : type) : bool :=
    match ty with
    | NT name => is_scalar_type sch ty || is_enum_type sch ty
    | ListType ty' => is_valid_argument_type ty'
    end.


  Lemma valid_argument_typeP : forall ty, reflect (valid_argument_type ty) (is_valid_argument_type ty).
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
  Inductive valid_field_type : type -> Prop :=
  | VBase_Type : forall n,
      is_declared sch n ->
      valid_field_type (NT n)      
  | VList_Type : forall ty,
      valid_field_type ty ->
      valid_field_type (ListType ty).
  
  Fixpoint is_valid_field_type (ty : type) : bool :=
    match ty with
    | NT n => is_declared sch n
    | ListType ty' => is_valid_field_type ty'
    end.
  

  Lemma valid_field_typeP : forall ty, reflect (valid_field_type ty) (is_valid_field_type ty).
  Proof.
    move=> ty; apply: (iffP idP); last by elim.
    elim: ty.
      by move=> n /=; apply VBase_Type.
      by move=> t H /= /H; apply VList_Type.
  Qed.

  
  (** 
      It checks whether an argument is well-formed by checking that
      its type is a valid type for an argument **)
  Definition is_field_argument_wf (arg : FieldArgumentDefinition) : bool :=
    is_valid_argument_type arg.(argtype).

  
  (**
     It states whether a field is well-formed.

                 ty isValidFieldType
                  NoDuplicates args
           ∀ arg ∈ args, arg isWellFormed
           ------------------------------
           (fname (args) : ty) isAWellFormedField
   **)
  Definition is_field_wf (fld : FieldDefinition) : bool :=
    [&& is_valid_field_type fld.(return_type),
     uniq [seq arg.(argname) | arg <- fld.(fargs)] &
     all (is_field_argument_wf) fld.(fargs)].



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
  Definition is_field_ok (fld fld' : FieldDefinition) : bool :=
    match fld, fld' with
    | Field fname args ty, Field fname' args' ty' =>
      [&& (fname == fname'),
       fsubset args' args &
       is_subtype ty ty']
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
  Definition implements_interface_correctly (ty ty' : NamedType) : bool :=
    let ifields := fields sch ty' in
    let ofields := fields sch ty in
    all (fun f' => has (fun f => is_field_ok f f') ofields) ifields.
     

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
  (*
  Inductive wf_type_definition : TypeDefinition -> Prop :=
  | WF_Scalar : forall name, wf_type_definition (ScalarTypeDefinition name)
                       
  | WF_Object : forall name (interfaces : {fset NamedType}) fields,
      fields != [::] ->
      uniq [seq fld.(field_name) | fld <- fields] ->
      all is_field_wf fields ->
      all (implements_interface_correctly name) interfaces ->
      wf_type_definition (ObjectTypeDefinition name interfaces fields)
                       
  | WF_Interface : forall name fields,
      fields != [::] ->
      uniq [seq fld.(field_name) | fld <- fields] ->
      all is_field_wf fields ->
      wf_type_definition (InterfaceTypeDefinition name fields)
                       
  | WF_Union : forall name (members : {fset NamedType}),
      members != fset0 ->
      all (is_object_type schema) members ->
      wf_type_definition (UnionTypeDefinition name members)
                       
  | WF_Enum : forall name enumValues,
      enumValues != fset0 ->
      wf_type_definition (EnumTypeDefinition name enumValues).
   *)

  Fixpoint is_type_def_wf (tdef : TypeDefinition) : bool :=
    match tdef with
    | ScalarTypeDefinition _ => true
                                 
    | ObjectTypeDefinition name interfaces fields =>
      [&& (fields != [::]),
       uniq [seq fld.(fname) | fld <- fields],
       all is_field_wf fields &
       all (implements_interface_correctly name) interfaces]

    | InterfaceTypeDefinition _ fields =>
      [&& (fields != [::]),
       uniq [seq fld.(fname) | fld <- fields] &
       all is_field_wf fields]

    | UnionTypeDefinition name members =>
      (members != fset0) && all (is_object_type sch) members

    | EnumTypeDefinition _ enumValues => enumValues != fset0
        
    end.


  
  Definition is_schema_wf schema : bool :=
    [&& (schema.(query_type) \in schema_names schema),
     is_object_type schema schema.(query_type),
     uniq [seq tdef.(tdname) | tdef <- schema] &                   
     all is_type_def_wf schema.(type_definitions)].
      
  
  Structure wfSchema := WFSchema {
                        schem : @schema Name;
                        hasType :  Name -> Vals -> bool;
                        _ : is_schema_wf schem;
                      }.

  
  Coercion schem : wfSchema >-> Schema.schema.



  

  Lemma query_has_object_type schema :
    is_schema_wf schema ->
    is_object_type schema schema.(query_type).
  Proof.
    by rewrite /is_schema_wf => /and4P [_ Hobj _ _].
  Qed.

  Lemma query_has_object_type_wf_schema (schema : wfSchema) :
    is_object_type schema schema.(query_type).
  Proof. case: schema => schema Ht H.
    by apply: (query_has_object_type H).
  Qed.

  Lemma tdefs_N_nil schema :
    is_schema_wf schema ->
    schema.(type_definitions) != [::].
  Proof.
    rewrite /is_schema_wf => /and4P [H _ _ _].
    rewrite /schema_names in_fset in H.
    by case: schema.(type_definitions) H => //.
  Qed.

  
  Lemma has_implementation_is_interface (schema : wfSchema) ty :
    implementation schema ty != fset0 ->
    is_interface_type schema ty.
  Proof.
  Abort.
  
  Lemma field_in_interface_in_object (schema : wfSchema) ty ti f :
    ty \in implementation schema ti ->
    lookup_field_in_type schema ty f = lookup_field_in_type schema ti f.
  Proof.
    Admitted.
           
End WellFormedness.


Arguments wfSchema [Name Vals].