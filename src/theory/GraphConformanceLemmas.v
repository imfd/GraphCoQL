(* begin hide *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import String.
Require Import QString.

Require Import Schema.
Require Import SchemaWellFormedness.
Require Import SchemaAux.
Require Import Graph.
Require Import GraphAux.

Require Import GraphConformance.

Require Import SeqExtra.

(* end hide *)


Section Theory.

  Variables (Vals: eqType).

  Variable (s : @wfGraphQLSchema Vals) (g : conformedGraph s).



  (**
     This lemma states that if the root node's type conforms to the schema, 
     then its type must be the Query type.
   *)
  Lemma aux_root_query_type graph :
    root_type_conforms s graph -> graph.(root).(ntype) = s.(query_type).
  Proof. by rewrite /root_type_conforms; move/eqP. Qed.

  (**
     This lemma states that 
   *)
  Lemma root_query_type :
    g.(root).(ntype) = s.(query_type).
  Proof.
    case: g => g' H *.
      by move: (aux_root_query_type H).
  Qed.

  Lemma nodes_conform_have_object_type :
    nodes_conform s g -> forall u, u \in g.(nodes) -> is_object_type s u.(ntype).
  Proof.
    rewrite /nodes_conform /= => /allP Hconf u Hin.
      by case/andP : (Hconf u Hin).
  Qed.
    
  (**
     This lemma states that every node in the conforming graph 
     must have Object type.
   *)
  Lemma node_in_graph_has_object_type :
    forall u, u \in g.(nodes) -> is_object_type s u.(ntype).
  Proof.
    apply: nodes_conform_have_object_type.
      by case: g.
  Qed.

  
  (**
     This lemma states that every node reached by a labeled edge 
     must have a type that is subtype of the type associated to the 
     field used in the edge.
   *)
  Lemma neighbours_are_subtype_of_field u fld fdef  :
    lookup_field_in_type s u.(ntype) fld.(label) = Some fdef ->
    forall v, v \in neighbours_with_field g u fld ->
               v.(ntype) \in get_possible_types s fdef.(return_type).
  Proof.
    move=> Hlook.
    case: g => g' Hroot Hedges Hnodes v.
    rewrite /neighbours_with_field -in_undup => /mapP [v'].
    case: v' => [[src' fld'] target].
    rewrite mem_filter => /andP [/andP [/eqP /= Hsrc /eqP Hfld] Hin] Htrgt.
    simpl in Hin.
    move: Hedges; rewrite /edges_conform /=.
    case/andP=> _ /allP-/(_ _ Hin).
    rewrite Hsrc Hfld Htrgt Hlook /=.
      by case: ifP => //= _; [case/and3P | case/andP].  
  Qed.

  
End Theory.