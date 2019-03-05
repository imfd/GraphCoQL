From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From extructures Require Import ord fset fmap.



Section GraphQLGraph.

  Variables (F Vals : ordType).


  (** Field 
      It corresponds to an edge's label or a property's key, with a list of arguments
   **)
  Record fld := Field {
                   label : F;
                   args : {fmap F -> Vals}
                 }.

  
  Coercion label_of_fld (f : fld) := let: Field l _ := f in l.
  Coercion fun_of_fld (f : fld) := let: Field _ a := f in a.


  (** Packing and unpacking of graph fields, needed for canonical instances  **)
  Definition prod_of_fld (f : fld) := let: Field l a := f in (l, a).
  Definition fld_of_prod (p : F * {fmap F -> Vals}) := let: (l, a) := p in Field l a.

  (** Cancelation lemma **)
  Lemma can_fld_of_prod : cancel prod_of_fld fld_of_prod.
  Proof. by case. Qed.

  Canonical fld_eqType := EqType fld (CanEqMixin can_fld_of_prod).
  Canonical fld_choiceType := ChoiceType fld (CanChoiceMixin can_fld_of_prod).
  Canonical fld_ordType := OrdType fld (CanOrdMixin can_fld_of_prod).
  


  (** Node
      It corresponds to a node in a graph.
      It contains its type and its fields (as a partial mapping between
      Fields and values).
   **)
  Record node := Node {
                    type : F;
                    fields : {fmap fld -> (Vals + (seq Vals))}  (* Vals could include list values? *)
                  }.

  Coercion fun_of_node (n : node) := let: Node _ f := n in f.

  (** Packing and unpacking of graph nodes, needed for canonical instances **)
  Definition prod_of_node (n : node) := let: Node t f := n in (t, f).
  Definition node_of_prod (p : F *  {fmap fld -> (Vals + (seq Vals)) }) :=
    let: (t, f) := p in Node t f.

  (** Cancelation lemma for a node **)
  Definition prod_of_nodeK : cancel prod_of_node node_of_prod.
  Proof. by case. Qed.

  
  Canonical node_eqType := EqType node (CanEqMixin prod_of_nodeK).
  Canonical node_choiceType := ChoiceType node (CanChoiceMixin prod_of_nodeK).
  Canonical node_ordType := OrdType node (CanOrdMixin prod_of_nodeK).
  
  
  Definition mem_field (n : node) f := (n f).
  
  Definition pred_of_node (n : node) : pred_class :=
    [eta mem_field n].

  Canonical node_predType := mkPredType pred_of_node.


  Lemma mem_fieldE (n : node) f : f \in n = (n f).
  Proof. done. Qed.

  
  (** GraphQL Graph 
      The collection of edges, and a root node 
   **)
  Record graphQLGraph := GraphQLGraph {
                            root : node;
                            E : {fset node * fld * node};
                          }.

  (*
    Record graphQLGraph := GraphQLGraph {
           root : node;
           nodes : {fset node};
           E : {fset node * fld * node}
    }

    Record wfGraph := WFGraph {
           graph : graphQLGraph;
           _ : root \in nodes;
           _ : forall n f v, (n, f, v) \in E -> n \in nodes /\ v \in nodes
   }
   *)

  
  (** Packing and unpacking for graphs, needed for canonical instances **)
  Definition prod_of_graph (g : graphQLGraph) := let: GraphQLGraph r e := g in (r, e).
  Definition graph_of_prod (p : node * {fset node * fld * node}) :=
    let: (r, e) := p in GraphQLGraph r e.


  (** Cancelation lemma for a graph **)
  Definition prod_of_graphK : cancel prod_of_graph graph_of_prod.
  Proof. by case. Qed.
  
  Canonical graph_eqType := EqType graphQLGraph (CanEqMixin prod_of_graphK).
  Canonical graph_choiceType := ChoiceType graphQLGraph (CanChoiceMixin prod_of_graphK).
  Canonical graph_ordType := OrdType graphQLGraph (CanOrdMixin prod_of_graphK).
  
    
    

  Definition fun_of_graph (g : graphQLGraph) := fun v1 f v2 => (v1, f, v2) \in (E g).
  Coercion fun_of_graph : graphQLGraph >-> Funclass.

  Lemma graphE (g : graphQLGraph) v1 f v2 : g v1 f v2 = ((v1, f, v2) \in g.(E)).
  Proof. done. Qed.


    
  Coercion edges_of_graph (g : graphQLGraph) := g.(E).

  
  



End GraphQLGraph.


Arguments fld [F Vals].
Arguments node [F Vals].
Arguments graphQLGraph [F Vals].

  