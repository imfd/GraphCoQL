From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section GraphQLGraph.


  Variables (N F A T Vals: finType).

  (** Field 
      It corresponds to a field's name and list of arguments but without
      its associated value.
   **)
  Record fld := Field {
                   label : F;
                   args : {ffun A -> option Vals}
                 }.



  
  Definition prod_of_fld (f : fld) := let: Field l a := f in (l, a).
  Definition fld_of_prod (p : prod F {ffun A -> option Vals}) := let: (l, a) := p in Field l a.

  Lemma can_fld_of_prod : cancel prod_of_fld fld_of_prod.
  Proof. by case. Qed.

  Definition fld_eqMixin := CanEqMixin can_fld_of_prod.
  Canonical fld_eqType := EqType fld fld_eqMixin.
  Definition fld_choiceMixin := CanChoiceMixin can_fld_of_prod.
  Canonical fld_choiceType := ChoiceType fld fld_choiceMixin.
  Definition fld_countMixin := CanCountMixin can_fld_of_prod.
  Canonical fld_countType := CountType fld fld_countMixin.
  Definition fld_finMixin := CanFinMixin can_fld_of_prod.
  Canonical fld_finType := FinType fld fld_finMixin.


  
  (** Edges 
      Directed and "labeled" edges of a graph.
      It is a set of 3-tuples: node * fld * node
   **)
  Record edges := Edges { val : {set N * fld * N} }.


  Coercion set_of_edges (E : edges) := val E.

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

  
  (** Tau
      A function that assigns a type name to every node
   **)
  Inductive tau : Type := Tau of {ffun N -> T}.

  
  (** Lambda
      A partial function that assigns a scalar value or list of scalar values to some pairs
      of the form (u, f[alpha]), where u ∈ N and f ∈ fld.
   **)
  Inductive lambda : Type := Lambda of {ffun N * fld -> option (Vals + (seq Vals)) }.



  
  (** GraphQL Graph 
      The collection of edges, tau, lambda and a root node 
   **)
  Record graphQLGraph := GraphQLGraph {
                            root : N;
                            E : edges;
                            t : tau;
                            lam : lambda
                          }.

  

  Coercion label_of_fld (f : fld) := let: Field l a := f in l.
  Coercion fun_of_fld (f : fld) := let: Field l a := f in a.

  Definition fieldArgsSupport (f : fld) : {set A} := [set a | None != f a].

    

  Definition fun_of_edges (E : edges) := fun v1 f v2 => (v1, f, v2) \in val E.
  Coercion fun_of_edges : edges >-> Funclass.

  Definition E0 := Edges set0.

  Lemma edgesE (E : edges) v1 f v2 : E v1 f v2 = ((v1, f, v2) \in E).
  Proof. by []. Qed.

  Coercion fun_of_tau (t : tau) := let: Tau f := t in f.

  Canonical tau_subType       := Eval hnf in [newType for fun_of_tau].
  Canonical tau_eqType        := Eval hnf in EqType _     [eqMixin     of @tau by <: ].

  
  Coercion fun_of_lambda (l : lambda) := let: Lambda f := l in f.

  Canonical lambda_subType       := Eval hnf in [newType for fun_of_lambda].
  Canonical lambda_eqType        := Eval hnf in EqType _     [eqMixin     of @lambda by <: ].


  Coercion root_of_graph (g : graphQLGraph) := let: GraphQLGraph r _ _ _ := g in r.
  Coercion edges_of_graph (g : graphQLGraph) := let: GraphQLGraph _ E _ _ := g in E.


End GraphQLGraph.

Check root.

Arguments fld [F] [A] [Vals].
Arguments tau [N] [T]. 
Arguments lambda [N] [F] [A] [Vals].
Arguments graphQLGraph [N] [F] [A] [T] [Vals].

  