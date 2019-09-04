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
Require Import GraphConformance.

Require Import SeqExtra.

(* end hide *)


(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">Graph Theory</h1>
        <p class="lead">
         This file contains lemmas about functions and conformance predicates over GraphQL Graphs.
        </p>         
  </div>
</div>#
 *)

Section Theory.

  Variables (Vals: eqType).

  (** *** Auxiliary definitions *)
  Section Aux.

    Variable (graph :  @graphQLGraph Vals).
    Implicit Type edge : @node Vals * @fld Vals * @node Vals.

  
    (** ---- *)
    (**
       This lemma states that the graph's root node is also
       included when asking for the graph's list of nodes.
     *)
    Lemma root_in_nodes : graph.(root) \in graph.(nodes).
    Proof.
      rewrite /nodes -in_undup.
        by apply/orP; left; apply/eqP.
    Qed.

    (** ---- *)
    (**
       This lemma states that neighbours of a node are also
       nodes in the graph.
     *)
    Lemma neighbours_are_in_nodes u fld:
      forall x, x \in neighbours_with_field graph u fld -> x \in graph.(nodes).
    Proof.
      rewrite /neighbours_with_field /nodes => x.
      rewrite -?in_undup => /mapP [v].
      rewrite mem_filter => /andP [/andP [/eqP Hsrc /eqP Hfld] Hin] /= Heq.
      apply/orP; right.
      apply/flatten_mapP.
      exists v => //=.
      rewrite /enodes inE; apply/orP; right.
        by rewrite mem_seq1; apply/eqP.
    Qed.
    
    
    (** ---- *)
    (**
       This lemma states that getting the head of a list of nodes 
       from the graph, returns a node that is in the graph.
     *)
    Lemma ohead_in_nodes nds v :
      all (fun node => node \in graph.(nodes)) nds ->
      ohead nds = Some v ->
      v \in graph.(nodes). 
    Proof.
      elim: nds => // x nds IH /=.
        by move=> H; case=> Heq; rewrite Heq in H; move/andP: H => [H _]. 
    Qed.
  

  End Aux.



  (** ---- *)
  (** *** Graph Conformance *)
  Section Conformance.
    
    Variable (s : @wfGraphQLSchema Vals) (g : conformedGraph s).

    (** ---- *)
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

    (** ---- *)
    (**
       This lemma states that conformed nodes must have object type.
     *)
    Lemma nodes_conform_have_object_type :
      nodes_conform s g -> forall u, u \in g.(nodes) -> is_object_type s u.(ntype).
    Proof.
      rewrite /nodes_conform /= => /allP Hconf u Hin.
        by case/andP : (Hconf u Hin).
    Qed.


    (** ---- *)
    (**
       This lemma states that every node in the conformed graph 
       must have Object type.
     *)
    Lemma node_in_graph_has_object_type :
      forall u, u \in g.(nodes) -> is_object_type s u.(ntype).
    Proof.
      apply: nodes_conform_have_object_type.
        by case: g.
    Qed.


    (** ---- *)
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

  End Conformance.
End Theory.