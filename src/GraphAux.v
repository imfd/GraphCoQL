From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From extructures Require Import ord fset fmap.

Require Import Graph.


Section GraphAux.

  Variables (N F A T Vals : ordType).

  Definition is_src_in_edge (edge : N * @fld F A Vals * N) (node : N) :=
    let: (n, f, v) := edge in n == node.
  
  Definition node_edges (E : seq (N * fld * N)) (node : N)  :=
    [seq edge <- E | is_src_in_edge edge node].

  Definition node_labels (E : seq (N * @fld F A Vals * N)) (node : N) : seq F :=
    map (fun edge => let: (_, f, _) := edge in
                  let: Field label _ := f in label) (node_edges E node).

  Definition label_ocurrences_for_node (E : seq (N * @fld F A Vals * N)) (node : N) (label : F) :=
    count (fun l => l == label) (node_labels E node).


  (** 
      Checks whether a label 
   **)
  Definition is_label_unique_for_src_node (E : seq (N * @fld F A Vals * N)) (src_node : N) (label : F) :=
    let nb_of_ocurrences := foldr (fun edge acc =>
                                    let: (u, f, _) := edge in
                                    if u == src_node then
                                      let: Field l _ := f in
                                      if l == label then acc + 1 else acc
                                    else
                                      acc) 0 E
    in
    nb_of_ocurrences == 1.


  Definition graph_s_nodes (graph : @graphQLGraph N F A T Vals) : seq node :=
    undup (unzip1 (map (fun edge => let: (u, _, v) := edge in (u, v)) graph.(E))).


End GraphAux.