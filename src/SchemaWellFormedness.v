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

  Section Defs.
    
    Variable (s : @schema Name).

    
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
        declares_implementation s n n' ->
        Subtype (NT n) (NT n')
                
    | ST_Union : forall n n',
        (n \in (union_members s n')) ->
        Subtype (NT n) (NT n')
                
    | ST_ListType : forall ty ty',
        Subtype ty ty' ->
        Subtype [ ty ] [ ty' ]. 

    Reserved Infix "<:" (at level 60).
    Equations is_subtype (ty ty' : @type Name) : bool :=
      {
        [ lty ] <: [ lty' ] := lty <: lty';

        NT name <: NT name' :=
          [|| (name == name'),
           declares_implementation s name name' | 
           (name \in (union_members s name'))];
        
        _ <: _ := false
      }
    where "ty1 <: ty2" := (is_subtype ty1 ty2).

    
    
    
    (** The two following definitions describe whether a given type is a valid type
      for a field argument (IsValidArgumentType) and if it is a valid type for a field itself 
      (IsValidFieldType).

      In the spec they are correspondently named "IsInputField" and "IsOutputField".

      https://facebook.github.io/graphql/June2018/#sec-Input-and-Output-Types **)

    Inductive valid_argument_type  : type -> Prop :=
    | VScalar_Arg : forall ty,
        is_scalar_type s ty ->
        valid_argument_type (NT ty)
    | VEnum_Arg : forall ty,
        is_enum_type s ty ->
        valid_argument_type (NT ty)
    | VList_Arg : forall ty,
        valid_argument_type ty ->
        valid_argument_type (ListType ty).
    
    Fixpoint is_valid_argument_type  (ty : type) : bool :=
      match ty with
      | NT name => is_scalar_type s ty || is_enum_type s ty
      | [ ty' ] => is_valid_argument_type  ty'
      end.


    
    (* Because we are not considering InputObjects, a field may have any type, 
     as long as it is declared in the Schema. *)
    Inductive valid_field_type  : type -> Prop :=
    | VBase_Type : forall n,
        is_declared s n ->
        valid_field_type (NT n)      
    | VList_Type : forall ty,
        valid_field_type ty ->
        valid_field_type (ListType ty).
    
    Fixpoint is_valid_field_type (ty : type) : bool :=
      match ty with
      | NT n => is_declared s n
      | [ ty' ] => is_valid_field_type  ty'
      end.
    

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
      is_valid_field_type fld.(return_type) &&
                                            (* uniq [seq arg.(argname) | arg <- fld.(fargs)] &  // Not specified... But should be? *)
                                            all (is_field_argument_wf) fld.(fargs).



    (** This checks whether an object field is valid w/r to another from an implemented interface.
      It checks the following:
      1. Both fields have the same name.
      2. The arguments of the interface field must be a subset of the object's arguments.
      3. The object's field return type must be a subtype of the interface's field.

      This is not checking that any additional argument in the object must be a "non-required" field.
     **)
    Definition is_field_ok (fld fld' : FieldDefinition) : bool :=
      [&& (fld.(fname) == fld'.(fname)),
       fsubset fld'.(fargs) fld.(fargs) &
       fld.(return_type) <: fld'.(return_type)].
    



    
    (**
     This checks whether an object type implements correctly an interface, 
     by properly defining every field defined in the interface.


            Schema(O) = type O implements ... I ... { Flds }   
                    Schema(I) = interface I { Flds' }
                 ∀ fld' ∈ Flds', ∃ fld ∈ Flds s.t fld OK fld'
            ------------------------------------------------
                        O implementsOK I

     **)
    
    Definition implements_interface_correctly (ty ty' : NamedType) : bool :=
      let ifields := fields s ty' in
      let ofields := fields s ty in
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
    

    Fixpoint is_type_def_wf (tdef : TypeDefinition) : bool :=
      match tdef with
      | Scalar _ => true
                                   
      | Object name implements interfaces { fields } =>
        [&& (fields != [::]),
         uniq [seq fld.(fname) | fld <- fields],
         all (is_field_wf) fields,
         all (is_interface_type s) interfaces &
         all (implements_interface_correctly name) interfaces]

      | Interface _ { fields } =>
        [&& (fields != [::]),
         uniq [seq fld.(fname) | fld <- fields] &
         all (is_field_wf) fields]

      | Union name { members } =>
        (members != fset0) && all (is_object_type s) members

      | Enum _ { enumValues } => enumValues != fset0
                                                     
      end.


    
    
    Definition is_schema_wf : bool :=
      [&& s.(query_type) \in s.(schema_names),
                             is_object_type s s.(query_type),
                             all (fun p => has_name p.1 p.2) s.(type_definitions) &
                             all (fun p => is_type_def_wf p.2) s.(type_definitions)].

  End Defs.
  
  
  Structure wfSchema := WFSchema {
                           sch : @schema Name;
                           hasType :  Name -> Vals -> bool;
                           _ : is_schema_wf sch;
                         }.

  
  Coercion sch : wfSchema >-> Schema.schema.


End WellFormedness.


Arguments wfSchema [Name Vals].

Infix "<:" := is_subtype (at level 50) : schema_scope.
