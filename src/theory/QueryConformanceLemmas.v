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
Require Import SchemaLemmas.
Require Import SchemaWellFormedness.

Require Import Query.
Require Import QueryAux.
Require Import QueryConformance.

Require Import SeqExtra.


Require Import Ssromega.

(* end hide *)


Section Theory.
  Transparent qresponse_name.




  Variables (Scalar : eqType).
  
  Section FragmentSpread.

    Variable (s : wfGraphQLSchema).

    
    (**
       
       https://graphql.github.io/graphql-spec/June2018/#sec-Object-Spreads-In-Object-Scope
     *)
    Lemma object_spreads_in_object_scope type_in_scope type_condition :
      is_object_type s type_in_scope ->
      is_object_type s type_condition ->
      is_fragment_spread_possible s type_in_scope type_condition <->
      type_in_scope = type_condition.
    Proof.
      move=> /get_possible_types_objectE Hobj1 /get_possible_types_objectE Hobj2.
      - rewrite /is_fragment_spread_possible Hobj1 Hobj2 /=.
        rewrite /seqI /= mem_seq1; case: ifP => /= [/eqP -> |] //.
        case: eqP => //.
    Qed.


    (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Abstract-Spreads-in-Object-Scope
     *)
    Lemma interface_spreads_in_object_scope type_in_scope type_condition :
      is_object_type s type_in_scope ->
      is_interface_type s type_condition ->
      is_fragment_spread_possible s type_in_scope type_condition <->
      type_in_scope \in implementation s type_condition.
    Proof.
      move=> /get_possible_types_objectE Hobj /is_interface_type_wfP [flds Hlook].
      rewrite /is_fragment_spread_possible; rewrite Hobj.
      simp get_possible_types; rewrite Hlook /=.
        by rewrite mem_seqI1 seqI1_Nnil.
    Qed.

    (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Abstract-Spreads-in-Object-Scope
     *)
    Lemma union_spreads_in_object_scope type_in_scope type_condition :
      is_object_type s type_in_scope ->
      is_union_type s type_condition ->
      is_fragment_spread_possible s type_in_scope type_condition <->
      type_in_scope \in union_members s type_condition.
    Proof.
      move=> /get_possible_types_objectE Hobj /is_union_type_wfP [mbs Hlook].
      rewrite /is_fragment_spread_possible; rewrite Hobj.
      simp get_possible_types; rewrite /union_members Hlook /=.
        by rewrite mem_seqI1 seqI1_Nnil.
    Qed.
 
    (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Object-Spreads-In-Abstract-Scope
     *)
    Lemma object_spreads_in_interface_scope type_in_scope type_condition :
      is_interface_type s type_in_scope ->
      is_object_type s type_condition ->
      is_fragment_spread_possible s type_in_scope type_condition <->
      type_condition \in implementation s type_in_scope.
    Proof.
      move=> /is_interface_type_wfP [flds Hlook] /get_possible_types_objectE Hobj.
      rewrite /is_fragment_spread_possible; rewrite Hobj.
      simp get_possible_types; rewrite Hlook /=.
        by rewrite mem_seq1I seq1I_Nnil.
    Qed.

    
    (**
       https://graphql.github.io/graphql-spec/June2018/#sec-Object-Spreads-In-Abstract-Scope
     *)
    Lemma object_spreads_in_union_scope type_in_scope type_condition :
      is_union_type s type_in_scope ->
      is_object_type s type_condition ->
      is_fragment_spread_possible s type_in_scope type_condition <->
      type_condition \in union_members s type_in_scope.
    Proof.
      move=> /is_union_type_wfP [mbs Hlook] /get_possible_types_objectE Hobj.
      rewrite /is_fragment_spread_possible; rewrite Hobj.
      simp get_possible_types; rewrite /union_members Hlook /=.
        by rewrite mem_seq1I seq1I_Nnil.
    Qed.

    
    
    
  End FragmentSpread.

  
End Theory.