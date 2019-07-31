From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaAuxLemmas.
Require Import SchemaWellFormedness.

Section Theory.

  Variable (Name Vals : ordType).
  Variable (s : @wfSchema Name Vals).
  


  
  Lemma implements_interface_correctlyP (ity ty : NamedType) :
    reflect (forall fi, fi \in fields s ity ->
                          exists f, f \in fields s ty /\ is_field_ok s f fi)
            (implements_interface_correctly s ty ity).
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

  
  Lemma is_type_def_wf_objE name interfaces fields :
    is_type_def_wf s (ObjectTypeDefinition name interfaces fields) =
    [&& (fields != [::]),
       uniq [seq fld.(fname) | fld <- fields],
       all (is_field_wf s) fields,
       all (is_interface_type s) interfaces &
       all (implements_interface_correctly s name) interfaces].
  Proof.
      by case: sch. Qed.

  Lemma is_type_def_wf_unionE name mbs :
    is_type_def_wf s (UnionTypeDefinition name mbs) = (mbs != fset0) && all (is_object_type s) mbs.
  Proof. by case: sch. Qed.

  Ltac wfschema := case: s => sch Hhty; rewrite /is_schema_wf => /= /and4P [Hqin Hqobj Hhn /allP Hok].

  Lemma query_has_object_type :
    is_object_type s s.(query_type).
  Proof.
      by  wfschema.
  Qed.


  Lemma tdefs_N_nil :
    s.(type_definitions) != emptym.
  Proof.
    wfschema.
    rewrite /schema_names in_fset in Hqin.
    move/mapP: Hqin => [x /codommP [t Hs] Hqin].
    case: (type_definitions sch) Hs.
    by case.
  Qed.

  Lemma lookup_type_name_wf ty tdef :
    lookup_type s ty = Some tdef ->
    ty = tdef.(tdname).
  Proof.
    wfschema.
    rewrite /lookup_type.
    move/getmP=> Hin.
    move/allP: Hhn.
    by move/(_ (ty, tdef) Hin) => /has_nameP /=.
  Qed.

  
  Lemma lookup_in_schema_wfP ty tdef :
    reflect (lookup_type s ty = Some tdef /\ ty = tdef.(tdname))
            ((ty, tdef) \in s.(type_definitions)).
  Proof.
    wfschema.
    apply: (iffP idP).
    - move=> Hin.
      move/allP: Hhn.
      move/(_ (ty, tdef) Hin) => /has_nameP /= Heq.
      rewrite Heq in Hin *.
        by move/lookup_in_schemaP: Hin; split.
    - move=> [Hlook Heq].
      by apply/lookup_in_schemaP.
  Qed.

 
  Lemma is_scalar_type_wfE ty :
    reflect (lookup_type s ty = Some (ScalarTypeDefinition ty))
            (is_scalar_type s ty).
  Proof.
    apply: (iffP idP).
    - rewrite /is_scalar_type.
      case Hlook: lookup_type => [tdef|] //.
      move/lookup_type_name_wf: Hlook => ->.
        by case: tdef.
    - move=> Hlook.
      by rewrite /is_scalar_type Hlook.
  Qed.

  
  Lemma is_object_type_wfP ty :
    reflect (exists intfs flds, lookup_type s ty = Some (ObjectTypeDefinition ty intfs flds))
            (is_object_type s ty).
  Proof.
    apply: (iffP idP)=> //.
    - funelim (is_object_type s ty) => // _.
      by exists interfaces, fields; rewrite Heq; move/lookup_type_name_wf: Heq => ->.
    - move=> [intfs [flds Hlook]].
        by rewrite is_object_type_equation_1 Hlook.
  Qed.

  Lemma is_interface_type_wfP ty :
    reflect (exists flds, lookup_type s ty = Some (InterfaceTypeDefinition ty flds))
            (is_interface_type s ty).
  Proof.
    apply: (iffP idP).
    - funelim (is_interface_type s ty) => // _.
        by exists fields0; rewrite Heq; move/lookup_type_name_wf: Heq => ->.
    - move=> [flds Hlook].
        by rewrite is_interface_type_equation_1 Hlook.
  Qed.
 

  Lemma is_union_type_wfP ty :
    reflect (exists mbs, lookup_type s ty = Some (UnionTypeDefinition ty mbs))
            (is_union_type s ty).
  Proof.
    apply: (iffP idP).
    - funelim (is_union_type s ty) => // _.
        by exists union_members; rewrite Heq; move/lookup_type_name_wf: Heq => ->.
    - move=> [mbs Hlook].
        by rewrite is_union_type_equation_1 Hlook.
  Qed.

    
  Lemma declares_implementation_are_interfaces tdef (ity : Name) :
    declares_implementation s tdef ity ->
    is_interface_type s ity.
  Proof.
    move=> Hdecl.
    move: (declares_implementation_is_object Name s ity tdef Hdecl).
    move/is_object_type_wfP=> [intfs [flds /lookup_in_schemaP Hlook]].
    move: Hdecl Hlook; wfschema => Hdecl Hlook.
    move: (Hok (tdef, ObjectTypeDefinition tdef intfs flds) Hlook).
    move=> /= /and5P [_ _ _ /allP Hintf _].
    rewrite /declares_implementation in Hdecl.
    move/lookup_in_schemaP: Hlook => Hlook.
    rewrite Hlook in Hdecl.
    by apply: (Hintf ity Hdecl).
  Qed.
  
  
  Lemma has_implementation_is_interface ty t :
    t \in implementation s ty ->
    is_interface_type s ty.
  Proof.  
  Admitted.

      
  Lemma field_in_interface_in_object ty ti f :
    ty \in implementation s ti ->
    lookup_field_in_type s ti f -> lookup_field_in_type s ty f.
  Proof.
    move=> Hin.
    move/declares_in_implementation: Hin => Hdecl.
    move: (declares_implementation_is_object Name s ti ty  Hdecl) => /is_object_type_wfP.
    case=> [intfs [flds Hlook]].
    rewrite {2}/lookup_field_in_type Hlook.
    move/lookup_field_in_typeP=> [tdef [ty' [Hlook' Hfin]]] Heq /=.
    move: (lookup_type_name_wf ti tdef Hlook') => Heq'.
    rewrite /declares_implementation Hlook in Hdecl.
    move: (lookup_type_name_wf ty _ Hlook) => Hneq.

    move/lookup_in_schemaP: Hlook => Hin.
    move: Hlook' Hin; wfschema => Hlook' Hin.
    move: (Hok (ty, (ObjectTypeDefinition ty intfs flds)) Hin) => {Hok}.
    move=> /= /and5P [_ _ _ _ /allP Hintfs].
    move: (Hintfs ti Hdecl) => {Hintfs Hdecl}.
    (* I think the problem is that it is defined on "s" which is the variable... *)
    (* Should probably be solved by modularizing. *)
    (* move=> /(implements_interface_correctlyP ti ty) H'. *)
    (*   move/lookup_in_schemaP: Hlook'. *)
    (*   rewrite Heq' => Hin'. *)
    (*   move: Hfin. *)
    (*   rewrite -(fields_E Hin') => Hfields. *)
    (*   rewrite -Heq' in Hfields. *)
    (*   move: (H' ty' Hfields) => [fld [Hfin Hok]]. *)
    (*   apply/get_firstP. *)
    (*   exists fld. *)
    (*   rewrite Hneq in Hin. *)
    (*     by rewrite (fields_E Hin) in Hfin => /=. *)
    (*     apply/has_field_nameP. *)
    (*     move: Hok; rewrite /is_field_ok => [/and3P [/eqP HE]] _ _. *)
    (*     by rewrite -Heq. *)
    (* Qed. *)
  Admitted.
  

  
   Lemma field_in_interface_in_object_E ty ti f fld fld' :
    ty \in implementation s ti ->
           lookup_field_in_type s ti f = Some fld ->
           [/\ lookup_field_in_type s ty f = Some fld',
            fld.(fname) = fld'.(fname) &
            fld.(return_type) = fld'.(return_type)].
  Proof.
  Admitted.

  
  Lemma field_in_interface_in_object_same_return_type ty ti f fld :
    ty \in implementation s ti ->
           lookup_field_in_type s ti f = Some fld ->
           exists2 fld', lookup_field_in_type s ty f = Some fld' & fld.(return_type) = fld'.(return_type).
  Admitted.
           
  
  Lemma union_members_has_objects ty :
    all (is_object_type s) (union_members s ty).
  Proof.
    rewrite /union_members.
    case Hlook: lookup_type => [tdef|] //.
    case: tdef Hlook => // u mbs /lookup_in_schemaP Hlook.
    move: Hlook; wfschema => Hlook.
    move/Hok: Hlook => /=; by case/andP.
  Qed.


    

  Lemma in_union_is_object ty uty :
    ty \in union_members s uty ->
           is_object_type s ty.
  Proof.
    move=> Hin.
    move/allP: (union_members_has_objects uty).
    by move/(_ ty Hin).
  Qed.

   Lemma in_possible_typesPwf t ty :
    is_object_type s t ->
    reflect
      ([\/ t = ty,
        t \in implementation s ty |
        t \in union_members s ty])
      (t \in get_possible_types s ty).
  Proof.
    move=> Hobj.
    apply: (iffP idP).
    - apply_funelim (get_possible_types s ty) => //=.
      * by move=> ty' o i flds _;  rewrite in_fset1 => /eqP ->; constructor 1.
      * by move=> ty' i flds /lookup_type_name_wf /= ->; constructor 2.
      * by move=> ty' u mbs Hlook; rewrite /union_members Hlook; constructor 3.
      
        
    - move=> [<- | Hintfs | Hunion]; simp get_possible_types.
      * move/is_object_type_wfP: Hobj => [intfs [flds Hlook]].
          by rewrite Hlook; apply/fset1P.
      * move: (declares_in_implementation Name s t ty).
        case=> _ H.
        move: (H Hintfs) => /declares_implementation_are_interfaces.
        move/is_interface_type_wfP=> [flds Hlook].
        by rewrite Hlook.
      - move: (in_union Name s t ty Hunion) => /is_union_type_wfP [mbs Hlook].
        by rewrite /union_members Hlook in Hunion *.
  Qed. 


    Lemma in_possible_types_is_object ty :
    forall t,
    t \in get_possible_types s ty ->
          is_object_type s t.
  Proof.
    funelim (get_possible_types s ty) => // t.
    - rewrite in_fset1 => /eqP ->.
      by simp is_object_type; rewrite Heq.
    - by move/in_implementation_is_object.
    - have <-: union_members s ty = union_members0 by rewrite /union_members Heq.
        by move/in_union_is_object.
  Qed.
  
  Lemma get_possible_types_interfaceE ty :
    is_interface_type s ty ->
    get_possible_types s ty = implementation s ty.
  Proof.
    move/is_interface_type_E=> [i [flds Hlook]].
    simp get_possible_types; rewrite Hlook.
    by move/lookup_type_name_wf: Hlook => ->.
  Qed.

   Lemma is_subtype_obj_eq ty ty' :
     is_object_type s ty' ->
     is_subtype s (NT ty) (NT ty') ->
     ty = ty'.
   Proof.
     funelim (is_subtype s (NT ty) (NT ty')) => //= Hobj.
     case: H => ->.
     case: H0 => ->.
     case/or3P; first by apply/eqP.
     
     move/declares_implementation_are_interfaces.
     by move: (is_object_type_interfaceN Name s ty' Hobj) => ->.
     move/in_union.
     by move: (is_object_type_unionN Name s ty' Hobj) => ->.
   Qed.

   
   Lemma args_are_subset_in_implementation ity oty  :
     oty \in implementation s ity ->
      forall fld, fld \in ity.(fields s) ->
      exists fld', fld' \in oty.(fields s) ->                                     
      [/\ fld'.(fname) = fld.(fname),                
       fsubset fld.(fargs) fld'.(fargs) &
       is_subtype s fld'.(return_type) fld.(return_type)].
   Proof.
   Admitted.


End Theory.

   