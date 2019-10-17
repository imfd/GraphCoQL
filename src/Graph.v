(* begin hide *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import String.
Require Import QString.

Require Import Value.

Notation Name := string.

(* end hide *)

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">GraphQL Graph</h1>
        <p class="lead">
         This file contains the basic building blocks to define a GraphQL Graph.
        </p>
         
  </div>
</div>#
 *)

Section GraphQLGraph.

  Variables (Scalar : eqType).

  (** * Definition *)
  
  (** ---- *)
  (** *** Label 

      It corresponds to an edge's label or a property's key.
   **)
  Record label := Label {
                      lname : string;
                      args : seq (string * @Value Scalar)
                    }.

  
  
  Coercion label_of_label (f : label) := let: Label l _ := f in l.
  Coercion fun_of_label (f : label) := let: Label _ a := f in a.

  (** ---- *)
  (** *** Node
      It corresponds to a node in a graph.
      It contains its type and its properties (as a partial mapping between
      fields and values).
   *)
  Record node := Node {
                       ntype : Name;
                       nprops : seq (label * @Value Scalar)
                     }.



  (** ---- *)
  (** *** GraphQL Graph 
      The collection of edges and a root node.
   *)
  Record graphQLGraph := GraphQLGraph {
                            root : node;
                            edges : seq (node * label * node)
                          }.
  

  Coercion edges_of_graph (g : graphQLGraph) := g.(edges).


  
  (** ---- *)
End GraphQLGraph.



Arguments label [Scalar].
Arguments node [Scalar].
Arguments graphQLGraph [Scalar].

Delimit Scope graph_scope with graph.
Open Scope graph_scope.

(* Keep an eye that → is the symbol, not pretty printing of '->' *)
Notation "src '⟜' lab '→' tgt" := (src, lab, tgt) (at level 20) : graph_scope.




(** ---- *)
(** 
    #<div>
        <a href='GraphCoQL.QueryNormalization.html' class="btn btn-light" role='button'> Previous ← Normalisation</a>
        <a href='GraphCoQL.GraphConformance.html' class="btn btn-info" role='button'>Continue Reading → Graph Conformance </a>
    </div>#
*)

Section Equality.

  (** * Equality 
     This section deals with some SSReflect bureaucratic things needed to establish 
     that the different components have a decidable procedure to establish equality (they belong to the 
     SSReflect type - eqType).

     This is basically done by establishing isomorphisms between the different structures
     to others that already have a decidable procedure.
   *)
  
  Variable (Scalar : eqType).
  

  (** Packing and unpacking of graph fields, needed for canonical instances  **)
  Definition prod_of_label (f : @label Scalar) := let: Label l a := f in (l, a).
  Definition label_of_prod (p : string * seq (string * @Value Scalar)) := let: (l, a) := p in Label l a.

  (** Cancelation lemma **)
  Lemma can_label_of_prod : cancel prod_of_label label_of_prod.
  Proof. by case. Qed.

  Canonical label_eqType := EqType label (CanEqMixin can_label_of_prod).


  
  (** Packing and unpacking of graph nodes, needed for canonical instances **)
  Definition prod_of_node (n : @node Scalar) := let: Node t f := n in (t, f).
  Definition node_of_prod (p : string * seq (label * @Value Scalar)) :=
    let: (t, f) := p in Node t f.

  (** Cancelation lemma for a node **)
  Definition prod_of_nodeK : cancel prod_of_node node_of_prod.
  Proof. by case. Qed.

  
  Canonical node_eqType := EqType node (CanEqMixin prod_of_nodeK).
  
  
  Fixpoint mem_seq_field (labels :  seq (label * @Value Scalar)) f : bool :=
    match labels with
    | [::] => false
    | (label, _) :: labels => (f == label) || mem_seq_field labels f
    end.
    
  Definition mem_field (n : node) f := mem_seq_field n.(nprops) f.
  
  Definition pred_of_node (n : node) : pred_class :=
    [eta mem_field n].

  Canonical node_predType := mkPredType pred_of_node.


  

  Fixpoint field_seq_value (labels :  seq (label * @Value Scalar)) f : option (@ Value Scalar) :=
    match labels with
    | [::] => None
    | (label, val) :: labels => if f == label then
                              Some val
                            else
                              field_seq_value labels f
    end.


   (** Packing and unpacking for graphs, needed for canonical instances **)
  Definition prod_of_graph (g : @graphQLGraph Scalar) := let: GraphQLGraph r e := g in (r, e).
  Definition graph_of_prod (p : node * seq (node * label * node)) :=
    let: (r, e) := p in @GraphQLGraph Scalar r e.


  (** Cancelation lemma for a graph **)
  Definition prod_of_graphK : cancel prod_of_graph graph_of_prod.
  Proof. by case. Qed.
  
  Canonical graph_eqType := EqType graphQLGraph (CanEqMixin prod_of_graphK).

  
  (* Definition fun_of_graph (g : graphQLGraph) := fun v1 f v2 => (v1, f, v2) \in (E g). *)
  (* Coercion fun_of_graph : graphQLGraph >-> Funclass. *)

  (* Lemma graphE (g : graphQLGraph) v1 f v2 : g v1 f v2 = ((v1, f, v2) \in g.(E)). *)
  (* Proof. done. Qed. *)


    


End Equality.