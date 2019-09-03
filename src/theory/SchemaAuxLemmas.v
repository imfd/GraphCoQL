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
Require Import SeqExtra.

(* begin hide *)


Section Theory.

  
  Variable (s : graphQLSchema).
  
  
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
   
    (**
       This lemma states that if looking up a type definition by name
       returns a valid definition, then that definition has the same 
       as the one used to look it up.
     *)
    Lemma lookup_type_name_wf ty tdef :
      lookup_type s ty = Some tdef ->
      ty = tdef.(tdname).
    Proof.
        by rewrite /lookup_type => /get_first_pred /eqP ->.
    Qed.



  End Lookup.

  
  Section Subtypes. 

    (**
       This lemma states that if a type is an Object type, then its 
       possible types are only itself.
     *)
    Lemma get_possible_types_objectE ty :
      is_object_type s ty ->
      get_possible_types s ty = [:: ty].
    Proof.
      simp is_object_type; simp get_possible_types.
        by case lookup_type => //; case=> //=.
    Qed.

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

End Theory.


   