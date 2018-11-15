From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From extructures Require Import ord fset fmap.

Require Import Graph.


Section GraphAux.

  Variables (N S Vals : ordType).

  Definition is_src_in_edge (edge : N * @fld S Vals * N) (node : N) :=
    let: (n, f, v) := edge in n == node.
  
  Definition node_edges (E : seq (N * fld * N)) (node : N)  :=
    [seq edge <- E | is_src_in_edge edge node].

  Definition node_labels (E : seq (N * @fld S Vals * N)) (node : N) : seq S :=
    map (fun edge => let: (_, f, _) := edge in
                  let: Field label _ := f in label) (node_edges E node).

  Definition label_ocurrences_for_node (E : seq (N * @fld S Vals * N)) (node : N) (label : S) :=
    count (fun l => l == label) (node_labels E node).


  (** 
      Checks whether a label 
   **)
  Definition is_label_unique_for_src_node (E : seq (N * @fld S Vals * N)) (src_node : N) (f : fld) :=
    let nb_of_ocurrences := foldr (fun edge acc =>
                                    let: (u, f', _) := edge in
                                    if u == src_node then
                                      if f == f' then acc + 1 else acc
                                    else
                                      acc) 0 E
    in
    nb_of_ocurrences == 1.


  Fixpoint unzip T (s : seq (T * T)) : seq T :=
    match s with
    | (x, y) :: tl => x :: y :: unzip tl
    | _ => [::]
    end.
  
  Definition graph_s_nodes (graph : @graphQLGraph N S Vals) : seq node :=
    undup (unzip (map (fun edge => let: (u, _, v) := edge in (u, v)) graph.(E))).


End GraphAux.