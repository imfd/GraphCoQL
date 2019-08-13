From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From CoqUtils Require Import string.
From Equations Require Import Equations.

Require Import Base.
Require Import Schema.
Require Import SchemaAux.
Require Import SchemaAuxLemmas.
Require Import SchemaWellFormedness.

Require Import SeqExtra.

Section Theory.

  Variable (Vals : eqType).
  Variable (s : @wfGraphQLSchema Vals).
  

  Ltac wfschema s :=
    let sch := fresh "s" in
    let Hhty := fresh "Hhty" in
    let Hqin := fresh "Hqin" in
    let Hqobj := fresh "Hqboj" in
    let Huniq := fresh "Huniq" in
    let Hok := fresh "Hok" in
    case: s => sch Hhty; rewrite /is_wf_schema => /=  /and4P [Hqin Hqobj Huniq /allP Hok].


  (**
     Reflection lemma between [implements_interface_correctly] and its Prop counterpart.
     It states that [implements_interface_correctly] corresponds to :

     ∀ ifields ∈ interface.fields →
       ∃ ofield ∈ object.fields, ofield is_valid_field_implementation ifield.
   *)
  Lemma implements_interface_correctlyP (object_type interface_type : string) :
    reflect (forall ifield, ifield \in fields s interface_type ->
                          exists2 ofield, ofield \in fields s object_type & is_valid_field_implementation s ofield ifield)
            (implements_interface_correctly s object_type interface_type).
  Proof.
    apply: (iffP idP).
    - rewrite /implements_interface_correctly => /allP H.
      by move=> ifield /H /hasP [ofield Hin Hok]; exists ofield.
    - move=> H.
      rewrite /implements_interface_correctly.
      apply/allP => ifield Hin.
      apply/hasP.
      by move: (H ifield Hin) => [ofield Hin' Hok]; exists ofield.
  Qed.

  (**
     This lemma states that the query type in the schema is an Object type.
   *)
  Lemma query_has_object_type :
    is_object_type s s.(query_type).
  Proof.
    by wfschema s. 
  Qed.


  (**
     Reflection lemma between [is_object_type] and its Prop counterpart.
     It states that saying that there is a name which is  an Object type is
     the same as saying that looking that name up in the schema results in an Object type definition.
   *)
  Lemma is_object_type_wfP ty :
    reflect (exists intfs flds, lookup_type s ty = Some (ObjectTypeDefinition ty intfs flds))
            (is_object_type s ty).
  Proof.
    apply: (iffP idP)=> //.
    - funelim (is_object_type s ty) => // _.
      by exists interfaces, fields; rewrite Heq; move/lookup_type_name_wf: Heq =>  -> /=.
    - by move=> [intfs [flds Hlook]]; simp is_object_type; rewrite Hlook.
  Qed.

  (**
     This lemma states that if a type [t] belongs to a union's members, 
     then that type must be an Object type.
   *)
  Lemma union_has_objects ty :
    forall t, t \in union_members s ty ->
               is_object_type s t.
  Proof.
    wfschema s.
    rewrite /union_members.
    case Hlook: lookup_type => [tdef|] //.
    case: tdef Hlook => // u mbs /lookup_type_in_tdefs Hin.
      by have /= := (Hok _ Hin) => /and3P [_ _ /allP].
  Qed.


  (**
     This lemma states that if a list of type definitions has no duplicate names, 
     then looking up the name of one of its members should return that same 
     type definition.
   *)
  Lemma in_tdefs_get_first tdef tdefs :
    uniq [seq t.(tdname) | t <- tdefs] ->
    tdef \in tdefs ->
             get_first (fun t => t.(tdname) == tdef.(tdname)) tdefs = Some tdef.
  Proof.
    elim: tdefs => //= t tdefs IH /andP [Hnin Huniq].
    rewrite inE => /orP [/eqP -> | Hin]; first by case: eqP.
    move/memPn: Hnin.
    have /(_ tdefs tdef Hin) : forall xs x, x \in xs -> x.(tdname) \in [seq y.(tdname) | y <- xs].
    elim=> //= hd tl IH' x; rewrite inE => /orP [/eqP -> | Hxin]; first by apply: mem_head.
      by apply: mem_tail; apply: IH'.
      move=> Hnamein /(_ tdef.(tdname) Hnamein) /negbTE; rewrite eq_sym => ->.
      by apply: IH.
  Qed.

  (**
     This lemma states that if a type definition belongs to a well-formed schema's
     list of type definitions, then looking that definition's name should return
     the same definition.
   *)
  Lemma in_tdefs_lookup tdef :
    tdef \in s.(type_definitions) ->
             lookup_type s tdef.(tdname) = Some tdef.
  Proof.
      by rewrite /lookup_type => *; apply: in_tdefs_get_first => //; wfschema s.
  Qed.

  (**
     This lemma states that if a type [t] belongs to the implementors of 
     another type [ty], then [t] must be an Object type. This is valid 
     for well-formed schemas.
   *)
  Lemma in_implementation_is_object ty t :
      t \in implementation s ty ->
             is_object_type s t.
  Proof.
    rewrite /implementation -in_undup => /mapP [tdef].
    rewrite mem_filter; case/andP.
    rewrite /implements_interface /tintfs.
    case: tdef => //= object_name interfaces fields Hinintfs Hintdefs Heq.
    apply/is_object_type_wfP.
    exists interfaces, fields.
    rewrite Heq.
    have -> : object_name = (Object (object_name) implements interfaces {fields}).(tdname) by [].
    by apply: in_tdefs_lookup.
  Qed.

  (**
     This lemma states that the list of possible types of a type [ty]
     has no duplicates in a well-formed schema.
   *)
  Lemma uniq_get_possible_types (ty : Name) :
    uniq (get_possible_types s ty).
  Proof.
    funelim (get_possible_types s ty) => //=; first by apply: undup_uniq.
    move: Heq; wfschema s => Heq.
    by move: (Hok _ (lookup_type_in_tdefs Heq)) => /=; case/and3P.
  Qed.

  (**
     This lemma states that if a type [t] belongs to the possible types 
     of another type [ty], then [t] must be an Object type. This is valid 
     for well-formed schemas.
   *)
  Lemma in_possible_types_is_object ty :
    forall t,
    t \in get_possible_types s ty ->
          is_object_type s t.
  Proof.
    funelim (get_possible_types s ty) => // t.
    - rewrite mem_seq1 => /eqP ->.
      by simp is_object_type; rewrite Heq.
    - by move/in_implementation_is_object.
    - have <-: union_members s ty = union_members0 by rewrite /union_members Heq.
        by apply: union_has_objects.
  Qed.
  


End Theory.









(* Unused lemmas *)




  (* Lemma is_scalar_type_wfE ty : *)
  (*   reflect (lookup_type s ty = Some (ScalarTypeDefinition ty)) *)
  (*           (is_scalar_type s ty). *)
  (* Proof. *)
  (*   apply: (iffP idP). *)
  (*   - rewrite /is_scalar_type. *)
  (*     case Hlook: lookup_type => [tdef|] //. *)
  (*     move/lookup_type_name_wf: Hlook => ->. *)
  (*       by case: tdef. *)
  (*   - move=> Hlook. *)
  (*     by rewrite /is_scalar_type Hlook. *)
(* Qed. *)




  (*   move/declares_in_implementation: Hin => Hdecl. *)
  (*   move: (declares_implementation_is_object  Hdecl) => /is_object_type_wfP. *)
  (*   case=> [intfs [flds Hlook]]. *)
  (*   rewrite {2}/lookup_field_in_type Hlook. *)
  (*   move/lookup_field_in_typeP=> [tdef [ty' [Hlook' Hfin]]] Heq /=. *)
  (*   move: (lookup_type_name_wf Hlook') => Heq'. *)
  (*   rewrite /declares_implementation Hlook in Hdecl. *)
  (*   move: (lookup_type_name_wf Hlook) => Hneq. *)

  (*   (* move/lookup_in_schemaP: Hlook => Hin. *) *)
  (*   (* move: Hlook' Hin; wfschema => Hlook' Hin. *) *)
  (*   (* move: (Hok (ty, (ObjectTypeDefinition ty intfs flds)) Hin) => {Hok}. *) *)
  (*   (* move=> /= /and5P [_ _ _ _ /allP Hintfs]. *) *)
  (*   (* move: (Hintfs ti Hdecl) => {Hintfs Hdecl}. *) *)
  (*   (* I think the problem is that it is defined on "s" which is the variable... *) *)
  (*   (* Should probably be solved by modularizing. *) *)
  (*   (* move=> /(implements_interface_correctlyP ti ty) H'. *) *)
  (*   (*   move/lookup_in_schemaP: Hlook'. *) *)
  (*   (*   rewrite Heq' => Hin'. *) *)
  (*   (*   move: Hfin. *) *)
  (*   (*   rewrite -(fields_E Hin') => Hfields. *) *)
  (*   (*   rewrite -Heq' in Hfields. *) *)
  (*   (*   move: (H' ty' Hfields) => [fld [Hfin Hok]]. *) *)
  (*   (*   apply/get_firstP. *) *)
  (*   (*   exists fld. *) *)
  (*   (*   rewrite Hneq in Hin. *) *)
  (*   (*     by rewrite (fields_E Hin) in Hfin => /=. *) *)
  (*   (*     apply/has_field_nameP. *) *)
  (*   (*     move: Hok; rewrite /is_valid_field_implementation => [/and3P [/eqP HE]] _ _. *) *)
  (*   (*     by rewrite -Heq. *) *)
  (*   (* Qed. *) *)
  (* Admitted. *)
  

  
  (*  Lemma field_in_interface_in_object_E ty ti f fld fld' : *)
  (*   ty \in implementation s ti -> *)
  (*          lookup_field_in_type s ti f = Some fld -> *)
  (*          [/\ lookup_field_in_type s ty f = Some fld', *)
  (*           fld.(fname) = fld'.(fname) & *)
  (*           fld.(return_type) = fld'.(return_type)]. *)
  (* Proof. *)
  (* Admitted. *)

  
  (* Lemma field_in_interface_in_object_same_return_type ty ti f fld : *)
  (*   ty \in implementation s ti -> *)
  (*          lookup_field_in_type s ti f = Some fld -> *)
  (*          exists2 fld', lookup_field_in_type s ty f = Some fld' & fld.(return_type) = fld'.(return_type). *)
(* Admitted. *)



 (* Lemma is_interface_type_wfP ty : *)
  (*   reflect (exists flds, lookup_type s ty = Some (InterfaceTypeDefinition ty flds)) *)
  (*           (is_interface_type s ty). *)
  (* Proof. *)
  (*   apply: (iffP idP). *)
  (*   - funelim (is_interface_type s ty) => // _. *)
  (*       by exists fields0; rewrite Heq; move/lookup_type_name_wf: Heq => ->. *)
  (*   - move=> [flds Hlook]. *)
  (*       by rewrite is_interface_type_equation_1 Hlook. *)
  (* Qed. *)
 

  (* Lemma is_union_type_wfP ty : *)
  (*   reflect (exists mbs, lookup_type s ty = Some (UnionTypeDefinition ty mbs)) *)
  (*           (is_union_type s ty). *)
  (* Proof. *)
  (*   apply: (iffP idP). *)
  (*   - funelim (is_union_type s ty) => // _. *)
  (*       by exists union_members; rewrite Heq; move/lookup_type_name_wf: Heq => ->. *)
  (*   - move=> [mbs Hlook]. *)
  (*       by rewrite is_union_type_equation_1 Hlook. *)
  (* Qed. *)

    
  (* Lemma declares_implementation_are_interfaces tdef (interface_type : string) : *)
  (*   declares_implementation s tdef interface_type -> *)
  (*   is_interface_type s interface_type. *)
  (* Proof. *)
  (*   move=> Hdecl. *)
  (*   have /is_object_type_wfP [intfs [flds Hlook]] := (declares_implementation_is_object Hdecl). *)
  (*   move: Hdecl Hlook; wfschema s => Hdecl Hlook. *)
  (*   move: (Hok (ObjectTypeDefinition tdef intfs flds)). *)
  (* (*   move=> /= /and5P [_ _ _ /allP Hintf _]. *) *)
  (* (*   rewrite /declares_implementation in Hdecl. *) *)
  (* (*   move/lookup_in_schemaP: Hlook => Hlook. *) *)
  (* (*   rewrite Hlook in Hdecl. *) *)
  (* (*   by apply: (Hintf interface_type Hdecl). *) *)
  (* (* Qed. *) *)
  (* Admitted. *)
  
  (* Lemma has_implementation_is_interface ty t : *)
  (*   t \in implementation s ty -> *)
  (*   is_interface_type s ty. *)
  (* Proof.   *)
  (* Admitted. *)

      
  (* Lemma field_in_interface_in_object ty ti f : *)
  (*   ty \in implementation s ti -> *)
  (*   lookup_field_in_type s ti f -> lookup_field_in_type s ty f. *)
  (* Proof. *)
(*   move=> Hin. *)



  (*  Lemma in_possible_typesPwf t ty : *)
  (*   is_object_type s t -> *)
  (*   reflect *)
  (*     ([\/ t = ty, *)
  (*       t \in implementation s ty | *)
  (*       t \in union_members s ty]) *)
  (*     (t \in get_possible_types s ty). *)
  (* Proof. *)
  (*   move=> Hobj. *)
  (*   apply: (iffP idP). *)
  (*   - apply_funelim (get_possible_types s ty) => //=. *)
  (*     * by move=> ty' o i flds _;  rewrite mem_seq1 => /eqP ->; constructor 1. *)
  (*     * by move=> ty' i flds /lookup_type_name_wf /= ->; constructor 2. *)
  (*     * by move=> ty' u mbs Hlook; rewrite /union_members Hlook; constructor 3. *)
      
        
  (*   - move=> [<- | Hintfs | Hunion]; simp get_possible_types. *)
  (*     * move/is_object_type_wfP: Hobj => [intfs [flds Hlook]]. *)
  (*         by rewrite Hlook /= mem_seq1; apply/eqP. *)
  (*     * (* move: (declares_in_implementation s t ty). *) *)
  (* (*       case=> _ H. *) *)
  (* (*       move: (H Hintfs) => /declares_implementation_are_interfaces. *) *)
  (* (*       move/is_interface_type_wfP=> [flds Hlook]. *) *)
  (* (*       by rewrite Hlook. *) *)
  (* (*     - move: (in_union Hunion) => /is_union_type_wfP [mbs Hlook]. *) *)
  (* (*       by rewrite /union_members Hlook in Hunion *. *) *)
  (* (* Qed.  *) *)
  (* Admitted. *)


 (* Lemma get_possible_types_interfaceE ty : *)
  (*   is_interface_type s ty -> *)
  (*   get_possible_types s ty = implementation s ty. *)
  (* Proof. *)
  (*   move/is_interface_type_E=> [i [flds Hlook]]. *)
  (*   simp get_possible_types; rewrite Hlook. *)
  (*   by move/lookup_type_name_wf: Hlook => ->. *)
  (* Qed. *)

   (* Lemma is_subtype_obj_eq ty ty' : *)
   (*   is_object_type s ty' -> *)
   (*   is_subtype s (NamedType ty) (NamedType ty') -> *)
   (*   ty = ty'. *)
   (* Proof. *)
   (*   funelim (is_subtype s (NamedType ty) (NamedType ty')) => //= Hobj. *)
   (*   case: H => ->. *)
   (*   case: H0 => ->. *)
   (*   case/or3P; first by apply/eqP. *)
     
   (*   move/declares_implementation_are_interfaces. *)
   (*   by move: (is_object_type_interfaceN Hobj) => ->. *)
   (*   move/in_union. *)
   (*   by move: (is_object_type_unionN Hobj) => ->. *)
   (* Qed. *)

   
   (* Lemma args_are_subset_in_implementation interface_type oty  : *)
   (*   oty \in implementation s interface_type -> *)
   (*    forall fld, fld \in interface_type.(fields s) -> *)
   (*    exists fld', fld' \in oty.(fields s) ->                                      *)
   (*    [/\ fld'.(fname) = fld.(fname),                 *)
   (*     fld.(fargs) fld'.(fargs) & *)
   (*     is_subtype s fld'.(return_type) fld.(return_type)]. *)
   (* Proof. *)
   (* Admitted. *)

    (* Lemma get_possible_types_N_nil_are_Ot ty : *)
    (*   get_possible_types s ty != [::] -> *)
    (*   all (is_object_type s) (get_possible_types s ty). *)
    (* Proof. *)
    (*   funelim (get_possible_types s ty) => //= _. *)
    (*   - by simp is_object_type; rewrite Heq. *)
    (*   - apply/allP=> x; apply: in_implementation_is_object. *)
    (*   - apply/allP=> x. *)
    (*     have <- : union_members s ty = union_members0 by rewrite /union_members Heq.  *)
    (*       by apply: in_union_is_object. *)
    (* Qed. *)
