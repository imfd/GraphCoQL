From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section PropertyLabeledGraph.


  Variables (N F A T Vals: finType).
  Variable root: N.

  (** Field **)
  Record fld := Field {
                   label : F;
                   args : {ffun A -> option Vals}
                 }.


  Coercion name_of_fld (f : fld) := let: Field l a := f in l.
  Coercion fun_of_fld (f : fld) := let: Field l a := f in a.
  
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


  Definition fieldArgsSupport (f : fld) : {set A} := [set a | None != f a].
  
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

  Coercion fun_of_tau (t : tau) := let: Tau f := t in f.

  Canonical tau_subType       := Eval hnf in [newType for fun_of_tau].
  Canonical tau_eqType        := Eval hnf in EqType _     [eqMixin     of @tau by <: ].
  
  (** Lambda : partial function that assigns a scalar value V to some pairs
      of the form (u, f[alpha]) **)
  Inductive lambda : Type := Lambda of {ffun N * fld -> option (Vals + (seq Vals)) }.

  Coercion fun_of_lambda (l : lambda) := let: Lambda f := l in f.

  Canonical lambda_subType       := Eval hnf in [newType for fun_of_lambda].
  Canonical lambda_eqType        := Eval hnf in EqType _     [eqMixin     of @lambda by <: ].
  

End PropertyLabeledGraph.

Check root.

Arguments fld [F] [A] [Vals].
Arguments tau [N] [T].

  