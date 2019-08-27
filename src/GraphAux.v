(* begin hide *)

From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import Graph.

(* end hide *)



Section GraphAux.

  Variables (Vals : eqType).
  Variable (graph :  @graphQLGraph Vals).
  Implicit Type edge : @node Vals * @fld Vals * @node Vals.

  
  
  (** Extractors for an edge **)


  Definition etarget edge : node :=
    let: (_, _, v) := edge in v.

  Definition esource edge : node :=
    let: (u, _, _) := edge in u.

  Definition efield edge : fld :=
    let: (_, f, _) := edge in f.

  Definition enodes edge : seq node := [:: edge.(esource) ; edge.(etarget)].
  
  (** Get all nodes from a graph **)
  Definition nodes graph : seq node :=
    undup (graph.(root) ::  flatten [seq edge.(enodes) | edge <- graph.(E)]).



  (** Get all neighbours of a node irrespective of the field in the edge 
      connecting the two **)
  Definition neighbours (u : node) (edges : seq (node * fld * node)) : seq node :=
    undup [seq edge.(etarget) | edge <- edges & edge.(esource) == u]. 

  


  (** Get all neighbours of a node that are linked via an edge with a given
      field. **)
  Definition neighbours_with_field (u : node) (f : fld) : seq node :=
    undup [seq edge.(etarget) |  edge <- [seq edge <- graph.(E) | (esource edge == u) & (efield edge == f)]].


  (** 
      Checks whether there is only one edge coming out of the source node and 
      having the given field.
   **)
  Definition is_field_unique_for_src_node graph (src_node : node) (f : fld) : bool :=
    uniq [seq edge <- graph.(E) | (esource edge == src_node) & (efield edge == f)].
    
 
  

End GraphAux.

Arguments etarget [Vals].
Arguments esource [Vals].
Arguments efield [Vals].
Arguments enodes [Vals].
Arguments nodes [Vals].
Arguments neighbours [Vals].
Arguments neighbours_with_field [Vals].
Arguments is_field_unique_for_src_node [Vals].