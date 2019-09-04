(* begin hide *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import String.
Require Import QString.


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

  Variables (Vals : eqType).

  (** * Definition *)
  
  (** ---- *)
  (** *** Field 

      It corresponds to an edge's label or a property's key.
   **)
  Structure fld := Field {
                      label : string;
                      args : seq (string * Vals)
                    }.

  
  
  Coercion label_of_fld (f : fld) := let: Field l _ := f in l.
  Coercion fun_of_fld (f : fld) := let: Field _ a := f in a.

  (** ---- *)
  (** *** Node
      It corresponds to a node in a graph.
      It contains its type and its properties (as a partial mapping between
      fields and values).
   *)
  Structure node := Node {
                       ntype : Name;
                       nprops : seq (fld * (Vals + seq Vals)%type)  (* Vals could include list values? *)
                     }.



  (** ---- *)
  (** *** GraphQL Graph 
      The collection of edges and a root node.
   *)
  Structure graphQLGraph := GraphQLGraph {
                            root : node;
                            E : seq (node * fld * node)
                          }.
  

  Coercion edges_of_graph (g : graphQLGraph) := g.(E).


  
  (** ---- *)
End GraphQLGraph.


Arguments fld [Vals].
Arguments node [Vals].
Arguments graphQLGraph [Vals].



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
  
  Variable (Vals : eqType).
  

  (** Packing and unpacking of graph fields, needed for canonical instances  **)
  Definition prod_of_fld (f : @fld Vals) := let: Field l a := f in (l, a).
  Definition fld_of_prod (p : string * seq (string * Vals)) := let: (l, a) := p in Field l a.

  (** Cancelation lemma **)
  Lemma can_fld_of_prod : cancel prod_of_fld fld_of_prod.
  Proof. by case. Qed.

  Canonical fld_eqType := EqType fld (CanEqMixin can_fld_of_prod).


  
  (** Packing and unpacking of graph nodes, needed for canonical instances **)
  Definition prod_of_node (n : @node Vals) := let: Node t f := n in (t, f).
  Definition node_of_prod (p : string * seq (fld * (Vals + seq Vals)%type)) :=
    let: (t, f) := p in Node t f.

  (** Cancelation lemma for a node **)
  Definition prod_of_nodeK : cancel prod_of_node node_of_prod.
  Proof. by case. Qed.

  
  Canonical node_eqType := EqType node (CanEqMixin prod_of_nodeK).
  
  
  Fixpoint mem_seq_field (flds :  seq (fld * (Vals + seq Vals)%type)) f : bool :=
    match flds with
    | [::] => false
    | (fld, _) :: flds => (f == fld) || mem_seq_field flds f
    end.
    
  Definition mem_field (n : node) f := mem_seq_field n.(nprops) f.
  
  Definition pred_of_node (n : node) : pred_class :=
    [eta mem_field n].

  Canonical node_predType := mkPredType pred_of_node.


  

  Fixpoint field_seq_value (flds :  seq (fld * (Vals + seq Vals)%type)) f : option (Vals + seq Vals) :=
    match flds with
    | [::] => None
    | (fld, vals) :: flds => if f == fld then
                              Some vals
                            else
                              field_seq_value flds f
    end.


   (** Packing and unpacking for graphs, needed for canonical instances **)
  Definition prod_of_graph (g : @graphQLGraph Vals) := let: GraphQLGraph r e := g in (r, e).
  Definition graph_of_prod (p : node * seq (node * fld * node)) :=
    let: (r, e) := p in @GraphQLGraph Vals r e.


  (** Cancelation lemma for a graph **)
  Definition prod_of_graphK : cancel prod_of_graph graph_of_prod.
  Proof. by case. Qed.
  
  Canonical graph_eqType := EqType graphQLGraph (CanEqMixin prod_of_graphK).

  
  (* Definition fun_of_graph (g : graphQLGraph) := fun v1 f v2 => (v1, f, v2) \in (E g). *)
  (* Coercion fun_of_graph : graphQLGraph >-> Funclass. *)

  (* Lemma graphE (g : graphQLGraph) v1 f v2 : g v1 f v2 = ((v1, f, v2) \in g.(E)). *)
  (* Proof. done. Qed. *)


    


End Equality.