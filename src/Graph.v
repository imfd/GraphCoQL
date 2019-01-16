From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From extructures Require Import ord fset fmap.



Section GraphQLGraph.

  Variables (N S Vals : ordType).


  (** Field 
      It corresponds to a field's name and list of arguments but without
      its associated value.
   **)
  Structure fld := Field {
                   label : S;
                   args : {fmap S -> Vals}
                 }.



  
  Definition prod_of_fld (f : fld) := let: Field l a := f in (l, a).
  Definition fld_of_prod (p : prod S {fmap S -> Vals}) := let: (l, a) := p in Field l a.

  Lemma can_fld_of_prod : cancel prod_of_fld fld_of_prod.
  Proof. by case. Qed.

  Definition fld_eqMixin := CanEqMixin can_fld_of_prod.
  Canonical fld_eqType := EqType fld fld_eqMixin.
  Definition fld_choiceMixin := CanChoiceMixin can_fld_of_prod.
  Canonical fld_choiceType := ChoiceType fld fld_choiceMixin.
  Definition fld_ordMixin := CanOrdMixin can_fld_of_prod.
  Canonical fld_ordType := OrdType fld fld_ordMixin.
  


  (** Node
      It corresponds to a node in a graph, containing
      an identifier, its type and its fields (as a partial mapping between
      Fields and values).
   **)
  Structure node := Node {
                    id : N;
                    type : S;
                    fields : {fmap fld -> (Vals + (seq Vals))}
                  }.


  
  Definition prod_of_node (n : node) := let: Node i t f := n in (i, t, f).
  Definition node_of_prod (p : N * S *  {fmap fld -> (Vals + (seq Vals)) }) :=
    let: (i, t, f) := p in Node i t f.

  Definition prod_of_nodeK : cancel prod_of_node node_of_prod.
  Proof. by case. Qed.
  
  Definition node_eqMixin := CanEqMixin prod_of_nodeK.
  Canonical node_eqType := EqType node node_eqMixin.
  Definition node_choiceMixin := CanChoiceMixin prod_of_nodeK.
  Canonical node_choiceType := ChoiceType node node_choiceMixin.
  Definition node_ordMixin := CanOrdMixin prod_of_nodeK.
  Canonical node_ordType := OrdType node node_ordMixin.
  

  Definition pred_of_node (n : node) : collective_pred fld :=
    [pred f : fld | isSome (n.(fields) f)].

  Canonical node_predType := mkPredType pred_of_node.

  
  
  (** GraphQL Graph 
      The collection of edges, and a root node 
   **)
  Record graphQLGraph := GraphQLGraph {
                            root : node;
                            E : {fset node * fld * node};
                          }.
                                    

  

  Definition prod_of_graph (g : graphQLGraph) := let: GraphQLGraph r e := g in (r, e).
  Definition graph_of_prod (p : node * {fset node * fld * node}) :=
    let: (r, e) := p in GraphQLGraph r e.

  Definition prod_of_graphK : cancel prod_of_graph graph_of_prod.
  Proof. by case. Qed.
  
  Definition graph_eqMixin := CanEqMixin prod_of_graphK.
  Canonical graph_eqType := EqType graphQLGraph graph_eqMixin.
  Definition graph_choiceMixin := CanChoiceMixin prod_of_graphK.
  Canonical graph_choiceType := ChoiceType graphQLGraph graph_choiceMixin.
  Definition graph_ordMixin := CanOrdMixin prod_of_graphK.
  Canonical graph_ordType := OrdType graphQLGraph graph_ordMixin.
  
  
  Coercion label_of_fld (f : fld) := let: Field l _ := f in l.
  Coercion fun_of_fld (f : fld) := let: Field _ a := f in a.

  Coercion type_of_node (n : node) := let: Node _ t _ := n in t.
  Coercion fun_of_node (n : node) := let: Node _ _ f := n in f.
  
    

  Definition fun_of_graph (g : graphQLGraph) := fun v1 f v2 => (v1, f, v2) \in (E g).
  Coercion fun_of_graph : graphQLGraph >-> Funclass.
  
  Lemma graphE (g : graphQLGraph) v1 f v2 : g v1 f v2 = ((v1, f, v2) \in g.(E)).
    Proof. done. Qed.
    
  Coercion edges_of_graph (g : graphQLGraph) := g.(E).






End GraphQLGraph.


Arguments fld [S Vals].
Arguments node [N S Vals].
Arguments graphQLGraph [N S Vals].

  