From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section PropertyLabeledGraph.


  Variables (N F A T Vals: finType).
  Variable root: N.

  (** Field **)
  Record fld := Field {
                   name : F;
                   args : {ffun A -> option Vals}
                 }.

  Definition prod_of_fld (f : fld) := let: Field n a := f in (n, a).
  Definition fld_of_prod (p : prod F {ffun A -> option Vals}) := let: (n, a) := p in Field n a.

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


  
  (** A graph (actually edges...) is a set of 3-tuples: node * field * node **)
  Record graph := Graph { val : {set N * fld * N} }.


  Coercion set_of_graph (g : graph) := val g.

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

  Definition fun_of_graph (g : graph) := fun v1 f v2 => (v1, f, v2) \in val g.
  Coercion fun_of_graph : graph >-> Funclass.

  Definition g0 := Graph set0.

  Lemma graphE (g : graph) v1 f v2 : g v1 f v2 = ((v1, f, v2) \in g).
  Proof. by []. Qed.
  
  (** Tau : assigns a type to every node **)
  Inductive tau : Type := Tau of {ffun N -> T}.

  (** Lambda : partial function that assigns a scalar value V to some pairs
      of the form (u, f[alpha]) **)
  Inductive lambda : Type := Lambda of {ffun N * fld -> option (Vals + (seq Vals)) }.

  

End PropertyLabeledGraph.
      