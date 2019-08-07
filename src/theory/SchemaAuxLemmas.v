From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.
From CoqUtils Require Import string.

Require Import Base.
Require Import Schema.
Require Import SchemaAux.
Require Import SeqExtra.

Section Theory.

  
  Variable (s : graphQLSchema).
  

  
  Lemma has_nameP name tdef : reflect (name = tdef.(tdname)) (has_name name tdef).
  Proof. by apply: (iffP eqP). Qed.
  

  
  Section Lookup.
    

    
    Lemma lookup_type_in_tdefs ty tdef :
      lookup_type s ty = Some tdef -> tdef \in s.(type_definitions).
    Proof.
      rewrite /lookup_type.
      elim: type_definitions => //= tdef' tdefs IH; case: ifP => /= [_ | _ Hgf].
      - case=> ->; apply: mem_head.
      - by apply: mem_tail; apply: IH.
    Qed.
   

    Lemma lookup_type_name_wf ty tdef :
      lookup_type s ty = Some tdef ->
      ty = tdef.(tdname).
    Proof.
        by rewrite /lookup_type => /get_first_pred /eqP ->.
    Qed.


    Lemma has_field_nameP (name : string) (fld : FieldDefinition) :
      reflect (name = fld.(fname)) (has_field_name name fld).
    Proof.
        by apply: (iffP eqP). Qed.

    Lemma lookup_field_in_typeP ty name :
      reflect (exists tdef fld, [/\ lookup_type s ty = Some tdef,
                            fld \in tdef.(tfields) &
                                    fld.(fname) = name]) (lookup_field_in_type s ty name).
    Proof.
      apply: (iffP idP).
      - rewrite /lookup_field_in_type.
        case Hlook: lookup_type => [tdef|] //.
        move/get_firstP=> [fld Hin /has_field_nameP ->].
          by exists tdef, fld.
      - case=> [tdef [fld [Hlook Hin <-]]].
        rewrite /lookup_field_in_type Hlook /=.
        apply/get_firstP.
          by exists fld => //; rewrite /has_field_name.
    Qed.

    Lemma lookup_field_in_type_is_obj_or_intf ty fname :
      lookup_field_in_type s ty fname ->
      is_object_type s ty \/ is_interface_type s ty.
    Proof.
      move/lookup_field_in_typeP=> [tdef [fld [Hlook Hin Heq]]].
      rewrite /tfields in Hin.
      case: tdef Hlook Hin => //.
      - move=> o intfs flds Hlook _.
          by left; rewrite is_object_type_equation_1 Hlook.
      - move=> i flds Hlook _.
          by right; rewrite is_interface_type_equation_1 Hlook.
    Qed.

    
    Lemma lookup_field_in_union_empty ty fname :
      is_union_type s ty ->
      lookup_field_in_type s ty fname = None.
    Proof.
      funelim (is_union_type s ty) => //.
        by rewrite /lookup_field_in_type Heq /=.
    Qed.

    
    Lemma lookup_field_typeP ty ty' fname :
      reflect (exists2 fld, lookup_field_in_type s ty fname = Some fld & fld.(return_type) = ty')
              (lookup_field_type s ty fname == Some ty').
    Proof.
      apply: (iffP eqP).
      - rewrite /lookup_field_type.
        case lookup_field_in_type => // fld.
          by case=> <-; exists fld.
                               - move=> [fld Hlook <-].
                                   by rewrite /lookup_field_type Hlook.
    Qed.

    
    

  End Lookup.




  Section Predicates.

    Lemma is_object_type_E ty :
      is_object_type s ty ->
      exists t intfs flds, lookup_type s ty = Some (ObjectTypeDefinition t intfs flds).
    Proof.
      funelim (is_object_type s ty) => // _.
        by exists object_name , interfaces, fields.
    Qed.

    Lemma is_interface_type_E ty :
      is_interface_type s ty <->
      exists i flds, lookup_type s ty = Some (InterfaceTypeDefinition i flds).
    Proof.
      split.
      funelim (is_interface_type s ty) => // _.
        by exists interface_name, fields0.
        case=> i; case=> flds Hlook.
          by rewrite is_interface_type_equation_1 Hlook.
    Qed.

    Lemma is_union_type_E ty:
      is_union_type s ty <->
      exists u mbs, lookup_type s ty = Some (UnionTypeDefinition u mbs).
    Proof.
      split.
      funelim (is_union_type s ty) => // _.
        by exists union_name, union_members.
        case=> u; case=> mbs Hlook.
          by rewrite is_union_type_equation_1 Hlook.  
    Qed.
    
    Lemma is_object_type_interfaceN ty :
      is_object_type s ty ->
      is_interface_type s ty = false.
    Proof.
      funelim (is_object_type s ty) => //.
        by rewrite is_interface_type_equation_1 Heq /=.
    Qed.

    Lemma is_object_type_unionN ty :
      is_object_type s ty ->
      is_union_type s ty = false.
    Proof.
        by funelim (is_object_type s ty); rewrite is_union_type_equation_1 Heq /=.
    Qed.

    Lemma is_interface_type_objectN ty :
      is_interface_type s ty ->
      is_object_type s ty = false.
    Proof.
        by funelim (is_interface_type s ty); simp is_object_type; rewrite Heq.
    Qed.
    
    Lemma is_interface_type_unionN ty :
      is_interface_type s ty ->
      is_union_type s ty = false.
    Proof.
        by funelim (is_interface_type s ty); rewrite is_union_type_equation_1 Heq /=.
    Qed.


    
    Lemma is_interface_is_abstract ty :
      is_interface_type s ty ->
      is_abstract_type s ty.
    Proof.
        by intros; rewrite /is_abstract_type; apply/orP; left.
    Qed.

    Lemma is_union_is_abstract ty :
      is_union_type s ty  ->
      is_abstract_type s ty.
    Proof.
        by intros; rewrite /is_abstract_type; apply/orP; right.
    Qed.

    Lemma is_union_type_objectN ty :
      is_union_type s ty ->
      is_object_type s ty = false.
    Proof.
        by funelim (is_union_type s ty); simp is_object_type; rewrite Heq.
    Qed.
    

    Lemma is_object_ifT {A : Type} ty (Tb Fb : A) :
      is_object_type s ty -> (if is_object_type s ty then Tb else Fb) = Tb.
    Proof.
        by case is_object_type.
    Qed.

    

    Lemma is_object_ifinterfaceF {A : Type} ty (Tb Fb : A) :
      is_object_type s ty -> (if is_interface_type s ty then Tb else Fb) = Fb.
    Proof.
        by move=> Hobj; move: (is_object_type_interfaceN Hobj) => ->. 
    Qed.

    Lemma is_object_ifunionF {A : Type} ty (Tb Fb : A) :
      is_object_type s ty -> (if is_union_type s ty then Tb else Fb) = Fb.
    Proof.
        by move=> Hobj; move: (is_object_type_unionN Hobj) => ->.
    Qed.

    
    Lemma abstract_type_N_obj ty :
      is_abstract_type s ty -> is_object_type s ty = false.
    Proof.
        by rewrite /is_abstract_type => /orP [/is_interface_type_objectN -> | /is_union_type_objectN ->].
    Qed.

    
    Lemma ty_not_scalar_or_enum ty tdef:
      lookup_type s ty = Some tdef ->
      ~~(is_scalar_type s ty || is_enum_type s ty) ->
      [\/ is_object_type s ty, is_interface_type s ty | is_union_type s ty].
    Proof. 
      rewrite /negb.
      case: ifP => //.
      rewrite /is_scalar_type /is_enum_type.
      case Hlook: lookup_type => [sm|] //.
      case: sm Hlook => //.
        by move=> o intfs flds Hlook _ _ _; constructor; rewrite is_object_type_equation_1 Hlook.
          by move=> i flds Hlook _ _; constructor; rewrite is_interface_type_equation_1 Hlook.
            by move=> u mbs Hlook _ _; constructor; rewrite is_union_type_equation_1 Hlook.
    Qed.



    

  End Predicates.


  
  
  Section Subtypes.

    (* Lemma union_members_E tdef : *)
    (*   (tdef.(tdname), tdef) \in s.(type_definitions) -> *)
    (*                             union_members s tdef.(tdname) = tdef.(tmbs). *)
    (* Proof. *)
    (*   move/lookup_in_schemaP => Hlook. *)
    (*   rewrite /union_members /tmbs {}Hlook . *)
    (*     by case: tdef. *)
    (* Qed. *)

    Lemma in_union (t ty : string) :
      t \in union_members s ty ->
            is_union_type s ty.      
    Proof.
      rewrite /union_members is_union_type_equation_1.
        by case lookup_type => //; case=> //.
    Qed.

    
    Lemma in_intfs ty (tdef : TypeDefinition):
      ty \in tdef.(tintfs) ->
             exists n flds, tdef = ObjectTypeDefinition n tdef.(tintfs) flds.
    Proof.
      rewrite /tintfs.
      case: tdef => // o i flds Hin.
        by exists o, flds.
    Qed.
    
    
    (* Lemma declares_implementationP ty ity : *)
    (*   reflect (exists2 tdef, lookup_type s ty = Some tdef & ity \in tdef.(tintfs)) *)
    (*           (declares_implementation s ty ity). *)
    (* Proof. *)
    (*   apply: (iffP idP). *)
    (*   - rewrite /declares_implementation. *)
    (*     case Hlook : lookup_type => [tdef|] //. *)
    (*       by exists tdef => // {Hlook}; case: tdef H => //. *)
    (*                 - move=> [tdef Hlook Hin]. *)
    (*                   rewrite /declares_implementation Hlook. *)
    (*                     by move: (in_intfs Hin) => [n [flds ->]]. *)
    (* Qed. *)

   

    
    
    

    (* Lemma declares_in_implementation t ty : *)
    (*   (declares_implementation s t ty) <-> (t \in implementation s ty). *)
    (* Proof. *)
    (* Admitted. *)

    (* Lemma qimplements_interface_is_object (ity : string) tdef : *)
    (*   (tdef.(tdname), tdef) \in s.(type_definitions) -> *)
    (*                             implements_interface ity tdef -> *)
    (*                             is_object_type s tdef.(tdname). *)
    (* Proof. *)
    (*   move/lookup_in_schemaP => Hlook. *)
    (*   rewrite /implements_interface. *)
    (*   move/in_intfs=> [n [flds Heq]]. *)
    (*   rewrite Heq in Hlook * => /=. *)
    (*   rewrite is_object_type_equation_1. *)
    (*     by rewrite Hlook. *)
    (* Qed. *)

    Lemma declares_implementation_is_object (ity oty : string) :
      declares_implementation s oty ity ->
      is_object_type s oty.
    Proof.
      rewrite /declares_implementation.
      case Hlook: lookup_type => [tdef|] //.
      case: tdef Hlook => // o intfs flds Hlook Hin.
        by rewrite is_object_type_equation_1 Hlook.
    Qed.

  
    
    (* Lemma implements_declares_implementation (ity : string) (tdef : TypeDefinition) : *)
    (*   (tdef.(tdname), tdef) \in s.(type_definitions) -> *)
    (*                             declares_implementation s tdef.(tdname) ity <-> implements_interface ity tdef. *)
    (* Proof. *)
    (*   move/lookup_in_schemaP=> Htdef. *)
    (*   split. *)
    (*   - rewrite /declares_implementation. *)
    (*     rewrite Htdef. *)
    (*     case: tdef Htdef => // o i f Hin. *)
    (*   - rewrite /implements_interface /declares_implementation Htdef. *)
    (*       by case: tdef Htdef. *)
    (* Qed. *)

    
    Lemma get_possible_types_objectE ty :
      is_object_type s ty ->
      get_possible_types s ty = [:: ty].
    Proof.
      move/is_object_type_E=> [o [intfs [flds Hlook]]].
        by simp get_possible_types; rewrite Hlook.
    Qed.

    Lemma in_object_possible_types t ty :
      is_object_type s ty ->
      t \in get_possible_types s ty ->
            t = ty.
    Proof.
      move/get_possible_types_objectE => ->.
        by rewrite mem_seq1 => /eqP.
    Qed.
    
    Lemma get_possible_types_unionE ty :
      is_union_type s ty ->
      get_possible_types s ty = union_members s ty.
    Proof.
      move/is_union_type_E => [u [mbs Hlook]].
        by simp get_possible_types; rewrite /union_members Hlook.
    Qed.

   

  End Subtypes.

End Theory.