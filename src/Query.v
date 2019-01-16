From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Asymmetric Patterns.

From extructures Require Import ord fmap.

Require Import treeordtype.
Require Import Schema.
Require Import SchemaAux.


Require Import CpdtTactics.


Section Query.


  Variables Name Vals : ordType.

  
  Unset Elimination Schemes.
  Inductive QuerySet : Type :=
  | SingleQuery : Query -> QuerySet
  | SelectionSet : Query -> QuerySet -> QuerySet
  with Query : Type :=
       | SingleField : Name -> {fmap Name -> Vals} -> Query
       | LabeledField : Name -> Name -> {fmap Name -> Vals} -> Query
       | NestedField : Name -> {fmap Name -> Vals} -> QuerySet -> Query
       | NestedLabeledField : Name -> Name -> {fmap Name -> Vals} -> QuerySet -> Query
       | InlineFragment : @NamedType Name -> QuerySet -> Query.


  Inductive Result : Type :=
  | Results : list ResponseObject -> Result
  with ResponseObject : Type :=
       | Null : Name -> ResponseObject
       | SingleResult : Name -> Vals -> ResponseObject
       | ListResult : Name -> list Vals -> ResponseObject
       | NestedResult : Name -> Result -> ResponseObject
       | NestedListResult : Name -> list Result -> ResponseObject.
  
  Set Elimination Schemes.

  Scheme QuerySet_ind := Induction for QuerySet Sort Prop
    with Query_ind := Induction for Query Sort Prop.

  Coercion responses_of_result (result : Result) := let: Results rs := result in rs.







  
  Fixpoint tree_of_query_set query_set : GenTree.tree (Name * Name * {fmap Name -> Vals}) :=
    match query_set with
    | SingleQuery q => GenTree.Node 0 [:: tree_of_query q]
    | SelectionSet q q' => GenTree.Node 1 [:: (tree_of_query q) ; (tree_of_query_set q')]
    end
  with tree_of_query query : GenTree.tree (Name * Name * {fmap Name -> Vals}) :=
         match query with
         | SingleField n args => GenTree.Node 2 [:: GenTree.Leaf (n, n, args)]
         | LabeledField l n args => GenTree.Node 3 [:: GenTree.Leaf (l, n, args)]
         | NestedField n args ϕ => GenTree.Node 4 [:: GenTree.Leaf (n, n, args) ; (tree_of_query_set ϕ)]
         | NestedLabeledField l n args ϕ => GenTree.Node 5 [:: GenTree.Leaf (l, n, args) ; (tree_of_query_set ϕ)]
         | InlineFragment t ϕ => GenTree.Node 6 [:: GenTree.Leaf (t, t, emptym) ; (tree_of_query_set ϕ)]
         end.

  Fixpoint query_set_of_tree tree : option QuerySet :=
    match tree with
    | GenTree.Node 0 [:: t] =>
      if query_of_tree t is Some ϕ then
        Some (SingleQuery ϕ)
      else
        None
    | GenTree.Node 1 [:: t ; t'] =>
      if (query_of_tree t, query_set_of_tree t') is (Some ϕ, Some ϕ') then
        Some (SelectionSet ϕ ϕ')
      else
        None
    | _ => None
    end
  with
  query_of_tree tree : option Query :=
    match tree with
    | GenTree.Node 2 [:: GenTree.Leaf (_, n, args)] => Some (SingleField n args)
    | GenTree.Node 3 [:: GenTree.Leaf (l, n, args)] => Some (LabeledField l n args)
    | GenTree.Node 4 [:: GenTree.Leaf (_, n, args) ; t] =>
      if (query_set_of_tree t) is Some ϕ then
        Some (NestedField n args ϕ)
      else
        None
    | GenTree.Node 5 [:: GenTree.Leaf (l, n, args) ; t] =>
       if (query_set_of_tree t) is Some ϕ then
        Some (NestedLabeledField l n args ϕ)
      else
        None
    | GenTree.Node 6 [:: GenTree.Leaf (_, t, emptym) ; tree'] =>
      if (query_set_of_tree tree') is Some ϕ then
        Some (InlineFragment t ϕ)
      else
        None
    | _ => None
    end.


  Lemma pcan_tree_of_query_set : pcancel tree_of_query_set query_set_of_tree.
  Proof.
    rewrite /pcancel => qs.    
    elim qs using QuerySet_ind with (P0 := fun q : Query => query_of_tree (tree_of_query q) = Some q).
      by move=> q /= ->.
      by move=> q H q' Hq /=; rewrite H Hq.
      by move=> *.
      by move=> *.  
      by move=> n args ϕ /= ->.
      by move=> l n args ϕ /= ->.
      by move=> t ϕ /= ->.
  Qed.
  Lemma pcan_tree_of_query : pcancel tree_of_query query_of_tree.
  Proof.
    move=> q; elim q using Query_ind with (P := fun qs => query_set_of_tree (tree_of_query_set qs) = Some qs).
    by move=> *; apply pcan_tree_of_query_set.
    by move=> *; apply pcan_tree_of_query_set.
    by move=> *.
    by move=> *.  
    by move=> n args ϕ /= ->.
    by move=> l n args ϕ /= ->.
    by move=> t ϕ /= ->.
  Qed.
    
    
  Definition query_set_eqMixin := PcanEqMixin pcan_tree_of_query_set.
  Canonical query_set_eqType := EqType QuerySet query_set_eqMixin.
  Definition query_eqMixin := PcanEqMixin pcan_tree_of_query.
  Canonical query_eqType := EqType Query query_eqMixin.

  Definition query_set_choiceMixin := PcanChoiceMixin pcan_tree_of_query_set.
  Canonical query_set_choiceType := ChoiceType QuerySet query_set_choiceMixin.
  Definition query_choiceMixin := PcanChoiceMixin pcan_tree_of_query.
  Canonical query_choiceType := ChoiceType Query query_choiceMixin.


  Definition query_set_ordMixin := PcanOrdMixin pcan_tree_of_query_set.
  Canonical query_set_ordType := OrdType QuerySet query_set_ordMixin.
  Definition query_ordMixin := PcanOrdMixin pcan_tree_of_query.
  Canonical query_ordType := OrdType Query query_ordMixin.
  


  Fixpoint list_of_query_set (query_set : QuerySet) : seq Query :=
    match query_set with
    | SingleQuery q => [:: q]
    | SelectionSet q q' => q :: (list_of_query_set q')
    end.
  
  Coercion list_of_query_set : QuerySet >-> seq.

  Definition pred_of_query_set (query_set : QuerySet) : collective_pred Query :=
    [pred q : Query | mem_seq query_set q].

  Canonical query_set_predType := mkPredType pred_of_query_set.
  

End Query.


Arguments QuerySet [Name Vals].
Arguments Query [Name Vals].
Arguments SingleField [Name Vals].
Arguments LabeledField [Name Vals].
Arguments NestedField [Name Vals].
Arguments NestedLabeledField [Name Vals].
Arguments InlineFragment [Name Vals].
Arguments SelectionSet [Name Vals].

Arguments Results [Name Vals].
Arguments ResponseObject [Name Vals].
Arguments Null [Name Vals].
Arguments SingleResult [Name Vals].


