From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.


Require Import Schema.
Require Import SchemaAux.




Section WellFormedness.

  Variables (Name Vals : ordType).
  Implicit Type sch : @schema Name.


  
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
  Inductive Subtype sch : type -> type -> Prop :=
  | ST_Refl : forall ty, Subtype sch ty ty
                            
  | ST_Interface : forall n n',
      declares_implementation sch n n' ->
      Subtype sch (NT n) (NT n')
              
  | ST_Union : forall n n',
      (n \in (union_members sch n')) ->
      Subtype sch (NT n) (NT n')
                    
  | ST_ListType : forall ty ty',
      Subtype sch ty ty' ->
      Subtype sch (ListType ty) (ListType ty'). 

  Fixpoint is_subtype sch (ty ty' : type) : bool :=
    match ty, ty' with
    | (ListType lty), (ListType lty') => is_subtype sch lty lty'
    | (NT name), (NT name') => [|| (name == name'),
                               declares_implementation sch ty ty' | 
                              (name \in (union_members sch name'))]
    | _, _ => false
    end.

   Lemma subtypeP sch ty ty': reflect (Subtype sch ty ty') (is_subtype sch ty ty').
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

  Inductive valid_argument_type sch : type -> Prop :=
  | VScalar_Arg : forall ty,
      is_scalar_type sch ty ->
      valid_argument_type sch (NT ty)
  | VEnum_Arg : forall ty,
      is_enum_type sch ty ->
      valid_argument_type sch (NT ty)
  | VList_Arg : forall ty,
      valid_argument_type sch ty ->
      valid_argument_type sch (ListType ty).
  
  Fixpoint is_valid_argument_type sch (ty : type) : bool :=
    match ty with
    | NT name => is_scalar_type sch ty || is_enum_type sch ty
    | ListType ty' => is_valid_argument_type sch ty'
    end.


  Lemma valid_argument_typeP sch : forall ty, reflect (valid_argument_type sch ty) (is_valid_argument_type sch ty).
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
  Inductive valid_field_type sch : type -> Prop :=
  | VBase_Type : forall n,
      is_declared sch n ->
      valid_field_type sch (NT n)      
  | VList_Type : forall ty,
      valid_field_type sch ty ->
      valid_field_type sch (ListType ty).
  
  Fixpoint is_valid_field_type sch (ty : type) : bool :=
    match ty with
    | NT n => is_declared sch n
    | ListType ty' => is_valid_field_type sch ty'
    end.
  

  Lemma valid_field_typeP sch : forall ty, reflect (valid_field_type sch ty) (is_valid_field_type sch ty).
  Proof.
    move=> ty; apply: (iffP idP); last by elim.
    elim: ty.
      by move=> n /=; apply VBase_Type.
      by move=> t H /= /H; apply VList_Type.
  Qed.

  
  (** 
      It checks whether an argument is well-formed by checking that
      its type is a valid type for an argument **)
  Definition is_field_argument_wf sch (arg : FieldArgumentDefinition) : bool :=
    is_valid_argument_type sch arg.(argtype).

  
  (**
     It states whether a field is well-formed.

                 ty isValidFieldType
                  NoDuplicates args
           ∀ arg ∈ args, arg isWellFormed
           ------------------------------
           (fname (args) : ty) isAWellFormedField
   **)
  Definition is_field_wf sch (fld : FieldDefinition) : bool :=
    is_valid_field_type sch fld.(return_type) &&
     (* uniq [seq arg.(argname) | arg <- fld.(fargs)] &  // Not specified... But should be? *)
     all (is_field_argument_wf sch) fld.(fargs).



  (** This checks whether an object field is valid w/r to another from an implemented interface.
      It checks the following:
      1. Both fields have the same name.
      2. The arguments of the interface field must be a subset of the object's arguments.
      3. The object's field return type must be a subtype of the interface's field.

      This is not checking that any additional argument in the object must be a "non-required" field.
   **)
  Definition is_field_ok sch (fld fld' : FieldDefinition) : bool :=
    [&& (fld.(fname) == fld'.(fname)),
     fsubset fld'.(fargs) fld.(fargs) &
     is_subtype sch fld.(return_type) fld'.(return_type)].
    



  
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
  Definition implements_interface_correctly sch (ty ty' : NamedType) : bool :=
    let ifields := fields sch ty' in
    let ofields := fields sch ty in
    all (fun f' => has (fun f => is_field_ok sch f f') ofields) ifields.
     

  Lemma implements_interface_correctlyP sch (ity ty : NamedType) :
    reflect (forall fi, fi \in fields sch ity ->
                          exists f, f \in fields sch ty /\ is_field_ok sch f fi)
            (implements_interface_correctly sch ty ity).
  Proof.
    apply: (iffP idP).
    - rewrite /implements_interface_correctly => /allP H.
      by move=> fi /H /hasP [f Hin Hok]; exists f.
    - move=> H.
      rewrite /implements_interface_correctly.
      apply/allP => fi Hin.
      apply/hasP.
      by move: (H fi Hin) => [f [Hin' Hok]]; exists f.
  Qed.
  
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
  

  Fixpoint is_type_def_wf sch (tdef : TypeDefinition) : bool :=
    match tdef with
    | ScalarTypeDefinition _ => true
                                 
    | ObjectTypeDefinition name interfaces fields =>
      [&& (fields != [::]),
       uniq [seq fld.(fname) | fld <- fields],
       all (is_field_wf sch) fields,
       all (is_interface_type sch) interfaces &
       all (implements_interface_correctly sch name) interfaces]

    | InterfaceTypeDefinition _ fields =>
      [&& (fields != [::]),
       uniq [seq fld.(fname) | fld <- fields] &
       all (is_field_wf sch) fields]

    | UnionTypeDefinition name members =>
      (members != fset0) && all (is_object_type sch) members

    | EnumTypeDefinition _ enumValues => enumValues != fset0
        
    end.


  Lemma is_type_def_wf_objE sch name interfaces fields :
    is_type_def_wf sch (ObjectTypeDefinition name interfaces fields) =
    [&& (fields != [::]),
       uniq [seq fld.(fname) | fld <- fields],
       all (is_field_wf sch) fields,
       all (is_interface_type sch) interfaces &
       all (implements_interface_correctly sch name) interfaces].
  Proof.
      by case: sch. Qed.

  Lemma is_type_def_wf_unionE sch name mbs :
    is_type_def_wf sch (UnionTypeDefinition name mbs) = (mbs != fset0) && all (is_object_type sch) mbs.
  Proof. by case: sch. Qed.

    
  
  Definition is_schema_wf sch : bool :=
    [&& (sch.(query_type) \in schema_names sch),
     is_object_type sch sch.(query_type),
     all (fun p => has_name p.1 p.2) sch.(type_definitions) &
     all (fun p => is_type_def_wf sch p.2) sch.(type_definitions)].
      
  
  Structure wfSchema := WFSchema {
                           sch;
                           hasType :  Name -> Vals -> bool;
                           _ : is_schema_wf sch;
                      }.

  
  Coercion sch : wfSchema >-> Schema.schema.



  

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
    schema.(type_definitions) != emptym.
  Proof.
    rewrite /is_schema_wf => /and4P [H _ _ _].
    rewrite /schema_names in_fset in H.
    move/mapP: H => [x /codommP [t Hs] H].
    case: (type_definitions schema) Hs.
    by case.
  Qed.

  Lemma lookup_type_name_wf schema ty tdef :
    is_schema_wf schema ->
    lookup_type schema ty = Some tdef ->
    ty = tdef.(tdname).
  Proof.
    rewrite /is_schema_wf => /and4P [_ _ /allP H _].
    rewrite /lookup_type.
    move/getmP=> Hin.
    by move/has_nameP: (H (ty, tdef) Hin) => /=.
  Qed.

  


  Lemma lookup_in_schema_wfP schema ty tdef :
    is_schema_wf schema ->
    reflect (lookup_type schema ty = Some tdef /\ ty = tdef.(tdname))
            ((ty, tdef) \in schema.(type_definitions)).
  Proof.
    move=> Hwf.
    apply: (iffP idP).
    - move: Hwf; rewrite /is_schema_wf => /and4P [_ _ /allP H _].
      move=> Hin.
      move/has_nameP: (H (ty, tdef) Hin) => /= Heq.
      rewrite Heq in Hin *.
        by move/lookup_in_schemaP: Hin; split.
    - move=> [Hlook Heq].
      by apply/lookup_in_schemaP.
  Qed.

 
  Lemma is_scalar_type_wfE schema ty :
    is_schema_wf schema ->
    reflect (lookup_type schema ty = Some (ScalarTypeDefinition ty))
            (is_scalar_type schema ty).
  Proof.
    move=> Hwf.
    apply: (iffP idP).
    - rewrite /is_scalar_type.
      case Hlook: lookup_type => [tdef|] //.
      move: (lookup_type_name_wf Hwf Hlook) => ->.
        by case: tdef {Hlook}.
    - move=> Hlook.
      by rewrite /is_scalar_type Hlook.
  Qed.

  Lemma is_object_type_wfP schema ty :
    is_schema_wf schema ->
    reflect (exists intfs flds, lookup_type schema ty = Some (ObjectTypeDefinition ty intfs flds))
            (is_object_type schema ty).
  Proof.
    move=> Hwf.
    apply: (iffP idP)=> //.
    - funelim (is_object_type schema ty) => // _.
      exists f, l; move: (lookup_type_name_wf Hwf Heq) => H.
        by rewrite H in Heq * => /=.
    - move=> [intfs [flds Hlook]].
        by rewrite /is_object_type Hlook.
  Qed.

  Lemma is_interface_type_wfP schema ty :
    is_schema_wf schema ->
    reflect (exists flds, lookup_type schema ty = Some (InterfaceTypeDefinition ty flds))
            (is_interface_type schema ty).
  Proof.
    move=> Hwf.
    apply: (iffP idP).
    - funelim (is_interface_type schema ty) => // _.
      exists l0; move: (lookup_type_name_wf Hwf Heq) => H.
        by rewrite H in Heq *.
    - move=> [flds Hlook].
      by rewrite /is_interface_type Hlook.
  Qed.
 

  Lemma is_union_type_wfP schema ty :
    is_schema_wf schema ->
    reflect (exists mbs, lookup_type schema ty = Some (UnionTypeDefinition ty mbs))
            (is_union_type schema ty).
  Proof.
    move=> Hwf.
    apply: (iffP idP).
    - funelim (is_union_type schema ty) => // _.
      exists f0; move: (lookup_type_name_wf Hwf Heq) => H.
        by rewrite H in Heq *.
    - move=> [mbs Hlook].
      by rewrite /is_union_type Hlook.
  Qed.

      
  Lemma implements_declares_implementation schema (ity : Name) (tdef : TypeDefinition) :
    is_schema_wf schema ->
    (tdef.(tdname), tdef) \in schema.(type_definitions) ->
    declares_implementation schema tdef.(tdname) ity <-> implements_interface ity tdef.
  Proof.
    move=> Hwf.
    move/lookup_in_schemaP=> Htdef.
    split.
    - rewrite /declares_implementation.
      rewrite Htdef.
      case: tdef Htdef => // o i f Hin.
    - rewrite /implements_interface /declares_implementation Htdef.
      by case: tdef Htdef.
  Qed.
    
  Lemma declares_implementation_are_interfaces schema tdef (ity : Name) :
    is_schema_wf schema ->
    declares_implementation schema tdef ity ->
    is_interface_type schema ity.
  Proof.
    move=> Hwf Hdecl.
    move: (declares_implementation_is_object Hdecl).
    move/(is_object_type_wfP tdef Hwf) => [intfs [flds /lookup_in_schemaP Hlook]].
    move/and4P: Hwf => [_ _ _ /allP Hok].
    move: (Hok (tdef, ObjectTypeDefinition tdef intfs flds) Hlook).
    rewrite is_type_def_wf_objE => /and5P [_ _ _ /allP Hintf _].
    rewrite /declares_implementation in Hdecl.
    move/lookup_in_schemaP: Hlook => Hlook.
    rewrite Hlook in Hdecl.
    apply (Hintf ity Hdecl).
  Qed.    
    
    
  Lemma has_implementation_is_interface schema ty :
    is_schema_wf schema ->
    implementation schema ty != fset0 ->
    is_interface_type schema ty.
  Proof.
    move=> Hwf.
    move/implementationP=> [tdef /codommP [t  Hlook]].
    move: (lookup_type_name_wf Hwf Hlook) => Heq; rewrite Heq in Hlook.
    move/lookup_in_schemaP: Hlook => Hin.
    move/(implements_declares_implementation ty Hwf Hin).
    by apply: declares_implementation_are_interfaces.
  Qed.

 
    
  Lemma field_in_interface_in_object schema ty ti f :
    is_schema_wf schema ->
    ty \in implementation schema ti ->
    lookup_field_in_type schema ti f -> lookup_field_in_type schema ty f.
  Proof.
    move=> Hwf Hin.
    move/declares_in_implementation: Hin => Hdecl.
    move: (declares_implementation_is_object Hdecl) => /(is_object_type_wfP ty Hwf).
    case=> [intfs [flds Hlook]].
    rewrite {2}/lookup_field_in_type Hlook.
    move/lookup_field_in_typeP=> [tdef [ty' [Hlook' Hfin]]] Heq /=.
    move: (lookup_type_name_wf Hwf Hlook') => Heq'.
    rewrite /declares_implementation Hlook in Hdecl.
    move: (lookup_type_name_wf Hwf Hlook) => Hneq.

    move/lookup_in_schemaP: Hlook => Hin.
    move/and4P: Hwf => [_ _ _ /allP Hok].
    move: (Hok (ty, (ObjectTypeDefinition ty intfs flds)) Hin) => {Hok}.
    rewrite is_type_def_wf_objE => /and5P [_ _ _ _ /allP Hintfs].
    move: (Hintfs ti Hdecl) => {Hintfs Hdecl}.
    move/implements_interface_correctlyP => H'.
    move/lookup_in_schemaP: Hlook'.
    rewrite Heq' => Hin'.
    move: Hfin.
    rewrite -(fields_E Hin') => Hfields.
    rewrite -Heq' in Hfields.
    move: (H' ty' Hfields) => [fld [Hfin Hok]].
    apply/get_firstP.
    exists fld.
    rewrite Hneq in Hin.
      by rewrite (fields_E Hin) in Hfin => /=.
      apply/has_field_nameP.
      move: Hok; rewrite /is_field_ok => [/and3P [/eqP HE]] _ _.
      by rewrite -Heq.
  Qed.


  Lemma union_members_nfset0Pwf schema ty :
    is_schema_wf schema ->
    reflect (is_union_type schema ty) (union_members schema ty != fset0).
  Proof.
    move=> Hwf.
    apply: (iffP idP).
    - move/fset0Pn=> [x].
      rewrite /union_members.
      funelim (is_union_type schema ty) => //; rewrite Heq //.
    - funelim (is_union_type schema ty) => // _.
      rewrite /union_members Heq.
      move/lookup_in_schemaP: Heq.
      move/and4P: Hwf => [_ _ _ /allP Hok].
      move/(Hok (ty, UnionTypeDefinition s2 f0)) => /=.
      by rewrite is_type_def_wf_unionE => /andP [H _].
  Qed.
  
  
End WellFormedness.


Arguments wfSchema [Name Vals].