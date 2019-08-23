From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Require Import String.
Require Import QString.

Require Import Base.

Section GraphQLGraph.

  Variables (Vals : eqType).


  (** *** Field 

      It corresponds to an edge's label or a property's key, with a list of arguments
   **)
  Record fld := Field {
                   label : string;
                   args : seq (string * Vals)
                 }.

  
  Coercion label_of_fld (f : fld) := let: Field l _ := f in l.
  Coercion fun_of_fld (f : fld) := let: Field _ a := f in a.


  (** Packing and unpacking of graph fields, needed for canonical instances  **)
  Definition prod_of_fld (f : fld) := let: Field l a := f in (l, a).
  Definition fld_of_prod (p : string * seq (string * Vals)) := let: (l, a) := p in Field l a.

  (** Cancelation lemma **)
  Lemma can_fld_of_prod : cancel prod_of_fld fld_of_prod.
  Proof. by case. Qed.

  Canonical fld_eqType := EqType fld (CanEqMixin can_fld_of_prod).

  
  


  (** *** Node
      It corresponds to a node in a graph.
      It contains its type and its fields (as a partial mapping between
      Fields and values).
   *)
  Record node := Node {
                    ntype : Name;
                    nfields : seq (fld * (Vals + seq Vals)%type)  (* Vals could include list values? *)
                  }.



  (** Packing and unpacking of graph nodes, needed for canonical instances **)
  Definition prod_of_node (n : node) := let: Node t f := n in (t, f).
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
    
  Definition mem_field (n : node) f := mem_seq_field n.(nfields) f.
  
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

  (* FIXME *)
  Coercion fun_of_node (n : node) := field_seq_value n.(nfields).
  
  (** *** GraphQL Graph 
      The collection of edges and a root node 
   *)
  Record graphQLGraph := GraphQLGraph {
                            root : node;
                            E : seq (node * fld * node)
                          }.


  
  (** Packing and unpacking for graphs, needed for canonical instances **)
  Definition prod_of_graph (g : graphQLGraph) := let: GraphQLGraph r e := g in (r, e).
  Definition graph_of_prod (p : node * seq (node * fld * node)) :=
    let: (r, e) := p in GraphQLGraph r e.


  (** Cancelation lemma for a graph **)
  Definition prod_of_graphK : cancel prod_of_graph graph_of_prod.
  Proof. by case. Qed.
  
  Canonical graph_eqType := EqType graphQLGraph (CanEqMixin prod_of_graphK).

  
  Definition fun_of_graph (g : graphQLGraph) := fun v1 f v2 => (v1, f, v2) \in (E g).
  Coercion fun_of_graph : graphQLGraph >-> Funclass.

  Lemma graphE (g : graphQLGraph) v1 f v2 : g v1 f v2 = ((v1, f, v2) \in g.(E)).
  Proof. done. Qed.


    
  Coercion edges_of_graph (g : graphQLGraph) := g.(E).

  
  



End GraphQLGraph.


Arguments fld [Vals].
Arguments node [Vals].
Arguments graphQLGraph [Vals].

  