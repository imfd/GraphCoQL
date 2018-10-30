From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From extructures Require Import ord fset fmap.

Section GraphQLGraph.

  Variables (N F A T Vals : ordType).
  
  (** Field 
      It corresponds to a field's name and list of arguments but without
      its associated value.
   **)
  Record fld := Field {
                   label : F;
                   args : {fmap A -> Vals}
                 }.



  
  Definition prod_of_fld (f : fld) := let: Field l a := f in (l, a).
  Definition fld_of_prod (p : prod F {fmap A -> Vals}) := let: (l, a) := p in Field l a.

  Lemma can_fld_of_prod : cancel prod_of_fld fld_of_prod.
  Proof. by case. Qed.

  Definition fld_eqMixin := CanEqMixin can_fld_of_prod.
  Canonical fld_eqType := EqType fld fld_eqMixin.
  Definition fld_choiceMixin := CanChoiceMixin can_fld_of_prod.
  Canonical fld_choiceType := ChoiceType fld fld_choiceMixin.
  Definition fld_ordMixin := CanOrdMixin can_fld_of_prod.
  Canonical fld_ordType := OrdType fld fld_ordMixin.
  


  


  (*
  Definition graph_sub : @subType {set N * fld * N} xpredT.
    apply: (@NewType _ _ set_of_graph Graph); last by case.
    by move=> P K s; have := K s.
  Defined.

Canonical egraph_subType      := Eval hnf in egraph_sub.
Canonical egraph_eqType       := Eval hnf in EqType _     [eqMixin     of @egraph by <: ].
Canonical egraph_choiceType   := Eval hnf in ChoiceType _ [choiceMixin of @egraph by <: ].
Canonical egraph_countType    := Eval hnf in CountType  _ [countMixin  of @egraph by <: ].
Canonical egraph_subCountType := Eval hnf in [subCountType of egraph].
Canonical egraph_finType      := Eval hnf in FinType    _ [finMixin    of @egraph by <: ].
Canonical egraph_subFinType   := Eval hnf in [subFinType of egraph]. 
*)

  

  
  (** GraphQL Graph 
      The collection of edges, tau, lambda and a root node 
   **)
  Record graphQLGraph := GraphQLGraph {
                            r : N;
                            E : {fset N * fld * N};
                            τ : {fmap N -> T};
                            λ : {fmap prod_ordType N fld_ordType -> (Vals + (seq Vals)) }
                          }.

  

  Definition prod_of_graph (g : graphQLGraph) := let: GraphQLGraph r e t l := g in (r, e, t, l).
  Definition graph_of_prod (p : N * {fset N * fld * N} * {fmap N -> T} * {fmap (N * fld) -> (Vals + (seq Vals)) }) :=
    let: (r, e, t, l) := p in GraphQLGraph r e t l.

  Definition prod_of_graphK : cancel prod_of_graph graph_of_prod.
  Proof. by case. Qed.
  
  Definition graph_eqMixin := CanEqMixin prod_of_graphK.
  Canonical graph_eqType := EqType graphQLGraph graph_eqMixin.
  Definition graph_choiceMixin := CanChoiceMixin prod_of_graphK.
  Canonical graph_choiceType := ChoiceType graphQLGraph graph_choiceMixin.
  Definition graph_ordMixin := CanOrdMixin prod_of_graphK.
  Canonical graph_ordType := OrdType graphQLGraph graph_ordMixin.
  
  
  Coercion label_of_fld (f : fld) := let: Field l a := f in l.
  Coercion fun_of_fld (f : fld) := let: Field l a := f in a.

  
    

  Definition fun_of_edges (E : {fset N * fld * N}) := fun v1 f v2 => (v1, f, v2) \in val E.
 

 

  Coercion root_of_graph (g : graphQLGraph) := let: GraphQLGraph r _ _ _ := g in r.
  Coercion edges_of_graph (g : graphQLGraph) := let: GraphQLGraph _ E _ _ := g in E.


End GraphQLGraph.

Check root.

Arguments fld [F] [A] [Vals].
Arguments graphQLGraph [N] [F] [A] [T] [Vals].

  