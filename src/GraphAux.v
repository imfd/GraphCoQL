From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From extructures Require Import ord fset fmap.

Require Import Graph.


Section GraphAux.

  Variables (N S Vals : ordType).
  Implicit Type graph :  @graphQLGraph N S Vals.
  
  
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

  (* Change to use set *)
  Definition nodes graph : seq node :=
    graph.(root) :: (undup (unzip (map (fun edge => let: (u, _, v) := edge in (u, v)) graph.(E)))).


  Lemma root_in_nodes graph : graph.(root) \in nodes graph.
  Proof.
    rewrite /nodes.
    rewrite inE.
    by apply/orP; left; apply/eqP.
  Qed.
  
  Definition get_neighbours graph (u : node) :=
    fset_filter (fun edge => let: (u', _, _) := edge in u'  == u) graph.(E).
    
  Definition get_target_nodes_with_field graph (u : node) (f : fld) :=
    let edges_with_field :=
        filter (fun e => let: (u', f', _) := e in (u' == u) && (f' == f)) graph.(E)
    in
    map (fun e => let: (_, _, v) := e in v) edges_with_field.

  

End GraphAux.