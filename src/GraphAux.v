From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From extructures Require Import ord fset fmap.

Require Import Graph.


Section GraphAux.

  Variables (F Vals : ordType).
  Implicit Type graph :  @graphQLGraph F Vals.
  Implicit Type edge : @node F Vals * @fld F Vals * @node F Vals.
  

  (** Extractors for an edge **)
  Definition edge_nodes edge : seq node :=
    let: (u, _, v) := edge in [:: u ; v].

  Definition edge_target edge : node :=
    let: (_, _, v) := edge in v.

  Definition edge_source edge : node :=
    let: (u, _, _) := edge in u.

  Definition edge_field edge : fld :=
    let: (_, f, _) := edge in f.

  
  (** Get all nodes from a graph **)
  Definition nodes graph : {fset node} :=
    fset (graph.(root) :: (flatten [seq (edge_nodes edge) | edge <- graph.(E)])).


  Lemma root_in_nodes graph : graph.(root) \in nodes graph.
  Proof.
    rewrite /nodes.
    rewrite in_fset inE. 
    by apply/orP; left; apply/eqP.
  Qed.


  (** Get all neighbours of a node irrespective of the field in the edge 
      connecting the two **)
  Definition neighbours graph (u : node) : {fset node} :=
    fset (foldr (fun e acc =>
                   let: (u', _, v) := e in
                   if u' == u then
                     v :: acc
                   else
                     acc) [::] graph.(E)).
  
  (* fset [seq (edge_target edge) | edge <- [seq edge <- graph.(E) | edge_source edge == u]]. *)


  (** Get all neighbours of a node that are linked via an edge with a given
      field. **)
  Definition neighbours_with_field graph (u : node) (f : fld) : {fset node} :=
    fset [seq (edge_target edge) |  edge <- graph.(E) & ((edge_source edge == u) && (edge_field edge == f))].


  (** 
      Checks whether there is only one edge coming out of the source node and 
      having the given field.
   **)
  Definition is_field_unique_for_src_node graph (src_node : node) (f : fld) :=
    let edges :=
        [seq edge <- graph.(E) | (edge_source edge == src_node) & (edge_field edge == f)]
    in
    uniq edges.


  

  
  
  Lemma u_and_target_nodes_in_nodes graph u fld :
    u \in graph.(nodes) -> all (fun v => v \in graph.(nodes)) (neighbours_with_field graph u fld).
  Proof.
  Admitted.

  
    
  Lemma ohead_in_nodes graph nds v :
    all (fun node => node \in graph.(nodes)) nds ->
    ohead nds = Some v ->
    v \in graph.(nodes). 
  Proof.
    elim: nds => // x nds IH /=.
    by move=> H; case=> Heq; rewrite Heq in H; move/andP: H => [H _]. 
  Qed.

End GraphAux.