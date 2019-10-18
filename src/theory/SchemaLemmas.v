(* begin hide *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

Require Import String.
Require Import QString.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaWellFormedness.

Require Import SeqExtra.

(* end hide *)

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">Schema Theory</h1>
        <p class="lead">
         This file contains lemmas about the auxiliary definitions for a 
         GraphQL Schema and for the well-formedness predicates.
        </p>         
  </div>
</div>#
 *)


(** * Auxiliary *)
(** ---- *)
Section Aux.

  
  Variable (s : graphQLSchema).
  
  (** *** Lookup *)
  (** ---- *)
  Section Lookup.

    (**
       This lemma states that if looking up a type definition by name
       returns a valid definition, then that definition is in the list 
       of type definitions of the schema.
     *)
    Lemma lookup_type_in_tdefs ty tdef :
      lookup_type s ty = Some tdef -> tdef \in s.(type_definitions).
    Proof.
      rewrite /lookup_type.
      elim: type_definitions => //= tdef' tdefs IH; case: ifP => /= [_ | _ Hgf].
      - case=> ->; apply: mem_head.
      - by apply: mem_tail; apply: IH.
    Qed.

    (** ---- *)
    (**
       This lemma states that if looking up a type definition by name
       returns a valid definition, then that definition's name is the same 
       as the one used to look it up.
     *)
    Lemma lookup_type_name_wf ty tdef :
      lookup_type s ty = Some tdef ->
      ty = tdef.(tdname).
    Proof.
        by rewrite /lookup_type => /get_first_pred /eqP ->.
    Qed.



  End Lookup.

  
  (** *** Subtyping *)
  (** ---- *)
  Section Subtypes. 

    (**
       This lemma states that if a type is an Object type, then its 
       possible subtypes are only itself.
     *)
    Lemma get_possible_types_objectE ty :
      is_object_type s ty ->
      get_possible_types s ty = [:: ty].
    Proof.
      simp is_object_type; simp get_possible_types.
        by case lookup_type => //; case=> //=.
    Qed.

    (** ---- *)
    (**
       This lemma states that if a type [t] is in
       the possible types of [ty], which is an Object type, then 
       that [t] is equal to [ty].
     *)
    Lemma in_object_possible_types t ty :
      is_object_type s ty ->
      t \in get_possible_types s ty ->
            t = ty.
    Proof.
      move/get_possible_types_objectE => ->.
        by rewrite mem_seq1 => /eqP.
    Qed.
      

  End Subtypes.

End Aux.


(** * Well-Formedness *)
(** ---- *)
Section WellFormedness.

  Variable (s : wfGraphQLSchema).
  
  
  (** Tactic to destroy a wf schema *)
  Ltac wfschema s :=
    let sch := fresh "s" in
    let Hhty := fresh "Hhty" in
    let Hqobj := fresh "Hqboj" in
    let Huniq := fresh "Huniq" in
    let Hok := fresh "Hok" in
    case: s => sch; rewrite /is_a_wf_schema => /=  /and3P [Hqobj Huniq /allP Hok].


  (** ---- *)
  (**
     This lemma states that the query type in a wf schema is an object type.
   *)
  Lemma query_has_object_type :
    is_object_type s s.(query_type).
  Proof.
     by wfschema s. 
  Qed.


  (** ---- *)
  (**
     Reflection lemma between [is_object_type] and its Prop counterpart.
     It states that being an object type means looking that name up in the schema and getting an object type definition.
   *)
  Lemma is_object_type_wfP ty :
    reflect (exists intfs flds, lookup_type s ty = Some (ObjectTypeDefinition ty intfs flds))
            (is_object_type s ty).
  Proof.
    apply: (iffP idP)=> //.
    - funelim (is_object_type s ty) => // _.
      by exists interfaces, fields0; rewrite Heq; move/lookup_type_name_wf: Heq =>  -> /=.
    - by move=> [intfs [flds Hlook]]; simp is_object_type; rewrite Hlook.
  Qed.

  (** ---- *)
  (**
     Reflection lemma between [is_interface_type] and its Prop counterpart.
     It states that being an interface type means looking that name up in the schema and getting an interface type definition.
   *)
  Lemma is_interface_type_wfP ty :
    reflect (exists flds, lookup_type s ty = Some (InterfaceTypeDefinition ty flds))
            (is_interface_type s ty).
  Proof.
    apply: (iffP idP)=> //.
    - funelim (is_interface_type s ty) => // _.
      by exists fields1; rewrite Heq; move/lookup_type_name_wf: Heq =>  -> /=.
    - by move=> [flds Hlook]; simp is_interface_type; rewrite Hlook.
  Qed.

  (** ---- *)
  (**
     Reflection lemma between [is_union_type] and its Prop counterpart.
     It states that being a union type means looking that name up in the schema and getting a union type definition.
   *)
  Lemma is_union_type_wfP ty :
    reflect (exists mbs, lookup_type s ty = Some (UnionTypeDefinition ty mbs))
            (is_union_type s ty).
  Proof.
    apply: (iffP idP)=> //.
    - funelim (is_union_type s ty) => // _.
      by exists members; rewrite Heq; move/lookup_type_name_wf: Heq =>  -> /=.
    - by move=> [mbs Hlook]; simp is_union_type; rewrite Hlook.
  Qed.
  
  
  (** ---- *)
  (**
     This lemma states that if a type [t] belongs to a union's members, then that type must be an Object type.
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

  
  (** ---- *)
  (**
     This lemma states that if a list of type definitions has no duplicate names, 
     then looking up the name of one of its members should return that same type definition.
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


  (** ---- *)
  (**
     This lemma states that if a type definition belongs to a wf schema's
     list of type definitions, then looking that definition's name should return
     the same definition.
   *)
  Lemma in_tdefs_lookup tdef :
    tdef \in s.(type_definitions) ->
             lookup_type s tdef.(tdname) = Some tdef.
  Proof.
      by rewrite /lookup_type => *; apply: in_tdefs_get_first => //; wfschema s.
  Qed.

  
  (** ---- *)
  (**
     This lemma states that if a type [t] belongs to the [implementation] of 
     another type [ty], then [t] must be an object type. This is valid only
     for well-formed schemas.
   *)
  Lemma in_implementation_is_object ty t :
      t \in implementation s ty ->
             is_object_type s t.
  Proof.
    rewrite /implementation -in_undup => /mapP [tdef].
    rewrite mem_filter; case/andP.
    rewrite /tintfs.
    case: tdef => //= object_name interfaces fields Hinintfs Hintdefs Heq.
    apply/is_object_type_wfP.
    exists interfaces, fields.
    rewrite Heq.
    have -> : object_name = (object (object_name) implements interfaces {fields}).(tdname) by [].
    by apply: in_tdefs_lookup.
  Qed.

  
  (** ---- *)
  (**
     This lemma states that there are no duplicate names when getting the subtypes of another type [ty].
   *)
  Lemma uniq_get_possible_types (ty : Name) :
    uniq (get_possible_types s ty).
  Proof.
    funelim (get_possible_types s ty) => //=; first by apply: undup_uniq.
    move: Heq; wfschema s => Heq.
    by move: (Hok _ (lookup_type_in_tdefs Heq)) => /=; case/and3P.
  Qed.


  (** ---- *)
  (**
     This lemma states that if a type [t] belongs to the possible types 
     of another type [ty], then [t] must be an object type. 
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
    - have <-: union_members s ty = members by rewrite /union_members Heq.
        by apply: union_has_objects.
  Qed.
  


End WellFormedness.



(** ---- *)
(** 
    #<div>
        <a href='GraphCoQL.SchemaWellFormedness.html' class="btn btn-info" role='button'> Go Back ← Schema Well-Formedness </a>
        <a href='GraphCoQL.Query.html' class="btn btn-info" role='button'>Continue Reading → Query </a>
    </div>#
*)

   