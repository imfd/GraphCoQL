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

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">Query Conformance Theory</h1>
        <p class="lead">
         This file contains proofs about the conformance of queries. 
        </p>         
        <p>
        For the  moment we only include proofs about fragment spreadibility, based on 
        sections from the spec. The definitions of semantics, normal form, etc. are 
        done, both in the spec and here, under the implicit assumption that queries are 
        valid.
        </p>
  </div>
</div>#
 *)


Section Theory.
  Transparent qresponse_name.




  Variables (Scalar : eqType).

  (** *** Fragment spreadibility *)
  (** ---- *)
  Section FragmentSpread.

    Variable (s : wfGraphQLSchema).

    
    (** **** Object spreads in object scope (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Object-Spreads-In-Object-Scope'><span>&#167;</span>5.5.2.3.1</a>#)
        ----
     *)

    (**
       This lemma states that object types can spread in object scope
       iff they are the same type.
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


    (** **** Abstract spreads in object scope (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Abstract-Spreads-in-Object-Scope'><span>&#167;</span>5.5.2.3.2</a>#)
       ----
     *)

    (**
       This lemma states that interface types spread in object scope iff
       the object implements the interface.
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

    (** ---- *)
    (**
       This lemma states that union types spread in object scope iff
       the object belongs to the union.
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
 
    (** **** Object spreads in abstract scope (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Object-Spreads-In-Abstract-Scope'><span>&#167;</span>5.5.2.3.3</a>#)
        ----
     *)

    (**
       This lemma states that object types spread in interface scope iff
       they implement the interface.
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

    (** ---- *)
    (**
       This lemma states that object types spread in interface scope iff
       they belong to the union.
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


(** ---- *)
(** 
    #<div>
        <a href='GraphCoQL.QueryConformance.html' class="btn btn-light" role='button'>Previous ← Query Conformance</a>
        <a href='GraphCoQL.QueryNormalForm.html' class="btn btn-info" role='button'>Continue Reading → Query Normal Form</a>
    </div>#
 *)
