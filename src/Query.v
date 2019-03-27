Require Import List.

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Asymmetric Patterns.

From Equations Require Import Equations.
From extructures Require Import ord fmap.


Require Import treeordtype.
Require Import Schema.
Require Import SchemaAux.


Require Import CpdtTactics.


Delimit Scope query_scope with QUERY.
Open Scope query_scope.


Section Forallt.
    Inductive Forallt {A : Type} (P : A -> Type) : list A -> Type :=
      Forallt_nil : Forallt P nil
    | Forallt_cons : forall (x : A) (l : list A),
        P x -> Forallt P l -> Forallt P (x :: l).

End Forallt.

Section Query.
  
  Variables Name Vals : ordType.

  Unset Elimination Schemes.
  Inductive Query : Type :=
  | SingleField : Name -> {fmap Name -> Vals} -> Query
  | LabeledField : Name -> Name -> {fmap Name -> Vals} -> Query
  | NestedField : Name -> {fmap Name -> Vals} -> seq Query -> Query
  | NestedLabeledField : Name -> Name -> {fmap Name -> Vals} -> seq Query -> Query
  | InlineFragment : @NamedType Name -> seq Query -> Query.


  Inductive ResponseObject : Type :=
  | Null : Name -> ResponseObject
  | SingleResult : Name -> Vals -> ResponseObject
  | ListResult : Name -> seq Vals -> ResponseObject
  | NestedResult : Name -> seq ResponseObject -> ResponseObject
  | NestedListResult : Name -> seq (seq ResponseObject) -> ResponseObject.
  
  Set Elimination Schemes.
  
  Definition Query_rect (P : Query -> Type)
             (Pl : seq Query -> Type)
             (IH_SF : forall n α, P (SingleField n α))
             (IH_LF : forall l n α, P (LabeledField l n α))
             (IH_NF : forall n α ϕ, Pl ϕ -> P (NestedField n α ϕ))
             (IH_NLF : forall l n α ϕ, Pl ϕ -> P (NestedLabeledField l n α ϕ))
             (IH_IF : forall t ϕ, Pl ϕ -> P (InlineFragment t ϕ))
             (IH_Nil : Pl [::])
             (IH_Cons : forall q, P q -> forall qs, Pl qs -> Pl (q :: qs))
    :=
    fix loop query : P query :=
      let fix F (qs : seq Query) : Pl qs :=
          match qs with
          | [::] => IH_Nil
          | hd :: tl => IH_Cons hd (loop hd) tl (F tl)
          end
      in
      match query with
      | SingleField n α => IH_SF n α
      | LabeledField l n α => IH_LF l n α
      | NestedField n α ϕ => IH_NF n α ϕ (F ϕ)
      | NestedLabeledField l n α ϕ => IH_NLF l n α ϕ (F ϕ)
      | InlineFragment t ϕ => IH_IF t ϕ (F ϕ)
      end.

  Definition Query_rec (P : Query -> Set) := @Query_rect P.

  Definition Query_ind (P : Query -> Prop)
             (Pl : seq Query -> Prop)
            (IH_SF : forall n α, P (SingleField n α))
            (IH_LF : forall l n α, P (LabeledField l n α))
            (IH_NF : forall n α ϕ, Pl ϕ -> P (NestedField n α ϕ))
            (IH_NLF : forall l n α ϕ, Pl ϕ -> P (NestedLabeledField l n α ϕ))
            (IH_IF : forall t ϕ, Pl ϕ -> P (InlineFragment t ϕ))
            (IH_Nil : Pl [::])
            (IH_Cons : forall q, P q -> forall qs, Pl qs -> Pl (q :: qs))
    :=
      fix loop query : P query :=
        let fix F (qs : seq Query) : Pl qs :=
          match qs with
          | [::] => IH_Nil
          | hd :: tl => IH_Cons hd (loop hd) tl (F tl)
          end
        in
        match query with
        | SingleField n α => IH_SF n α
        | LabeledField l n α => IH_LF l n α
        | NestedField n α ϕ => IH_NF n α ϕ (F ϕ)
        | NestedLabeledField l n α ϕ => IH_NLF l n α ϕ (F ϕ)
        | InlineFragment t ϕ => IH_IF t ϕ (F ϕ)
        end.

  
  Definition ResponseObject_rect (P : ResponseObject -> Type)
             (IH_Null : forall n, P (Null n))
             (IH_SR : forall n v, P (SingleResult n v))
             (IH_LR : forall n vals, P (ListResult n vals))
             (IH_NR : forall n ρ, Forallt P ρ -> P (NestedResult n ρ))
             (IH_NLR : forall n ρ, Forallt (fun rs => Forallt P rs) ρ -> P (NestedListResult n ρ)) :=
      fix loop response : P response :=
        let fix F0 (ρ : seq ResponseObject) : Forallt P ρ :=
            match ρ with
            | [::] => Forallt_nil _
            | hd :: tl => @Forallt_cons _ P hd tl (loop hd) (F0 tl)
            end
        in
        let fix F1 (ρ : seq (seq ResponseObject)) : Forallt (fun rs => Forallt P rs) ρ :=
            match ρ as r with
            | [::] => Forallt_nil _
            | hd :: tl => @Forallt_cons _ (fun rs => Forallt P rs) hd tl (F0 hd) (F1 tl)
            end
        in
        match response with
        | Null n => IH_Null n
        | SingleResult n v => IH_SR n v
        | ListResult n vals => IH_LR n vals
        | NestedResult n ρ => IH_NR n ρ (F0 ρ)
        | NestedListResult n ρ => IH_NLR n ρ (F1 ρ)                                                
      end.

  Definition ResponseObject_rec (P : ResponseObject -> Set) := @ResponseObject_rect P.

  Definition ResponseObject_ind (P : ResponseObject -> Prop)
             (IH_Null : forall n, P (Null n))
             (IH_SR : forall n v, P (SingleResult n v))
             (IH_LR : forall n vals, P (ListResult n vals))
             (IH_NR : forall n ρ, Forall P ρ -> P (NestedResult n ρ))
             (IH_NLR : forall n ρ, Forall (fun rs => Forall P rs) ρ -> P (NestedListResult n ρ))
    :=
      fix loop response : P response :=
        let fix F0 (ρ : seq ResponseObject) : Forall P ρ :=
            match ρ with
            | [::] => Forall_nil _
            | hd :: tl => @Forall_cons _ P hd tl (loop hd) (F0 tl)
            end
        in
        let fix F1 (ρ : seq (seq ResponseObject)) : Forall (fun rs => Forall P rs) ρ :=
            match ρ as r with
            | [::] => Forall_nil _
            | hd :: tl => @Forall_cons _ (fun rs => Forall P rs) hd tl (F0 hd) (F1 tl)
            end
        in
        match response with
        | Null n => IH_Null n
        | SingleResult n v => IH_SR n v
        | ListResult n vals => IH_LR n vals
        | NestedResult n ρ => IH_NR n ρ (F0 ρ)
        | NestedListResult n ρ => IH_NLR n ρ (F1 ρ)
      end.
  
  

  (** Boolean predicate to state equivalence between queries, needed for canonical instance.

   Maybe an isomorphism to another structure would be better (tree) but it was a bit chaotic,
   so I left it there hanging for a while. **)
  Equations query_eq (q1 q2 : Query) : bool :=
    {
      query_eq (SingleField n α) (SingleField n' α') := (n == n') && (α == α');
      query_eq (LabeledField l n α) (LabeledField l' n' α') := [&& (l == l'), (n == n') & (α == α')];
      query_eq (NestedField n α ϕ) (NestedField n' α' ϕ') := [&& (n == n'), (α == α') & queries_eq ϕ ϕ'];
      query_eq (NestedLabeledField l n α ϕ) (NestedLabeledField l' n' α' ϕ') := [&& (l == l'), (n == n'), (α == α') & queries_eq ϕ ϕ'];
      query_eq (InlineFragment t ϕ) (InlineFragment t' ϕ') := (t == t') && (queries_eq ϕ ϕ');
      query_eq _ _ := false
    }
  where
  queries_eq (q1 q2 : seq Query) : bool :=
    {
      queries_eq [::] [::] := true;
      queries_eq (cons hd tl) (cons hd' tl') := query_eq hd hd' && queries_eq tl tl';
      queries_eq _ _ := false
    }.

  Lemma Forall_cons_inv {A : Type} (P : A -> Prop) x s : Forall P (x :: s) -> P x /\ Forall P s.
  Proof. by move=> H; inversion H. Qed.
    
  

  Lemma query_eqP : Equality.axiom query_eq.
  Proof.
    move=> q1 q2; apply (iffP idP) => [| <-].
    move: q2.
    elim q1 using Query_ind with (Pl := (fun qs => forall qs', queries_eq qs qs' -> qs = qs')).
    by move=> n α; case=> // n' α'; rewrite query_eq_equation_1; move/andP=> [/eqP -> /eqP ->].
    by move=> l n α; case=> // l' n' α'; rewrite query_eq_equation_7; move/and3P=> [/eqP -> /eqP -> /eqP ->].
  Admitted.


  Fixpoint tree_of_query query : GenTree.tree (option Name * Name * {fmap Name -> Vals}):=
    match query with
    | SingleField f α => GenTree.Node 0 [:: GenTree.Leaf  (None, f, α)]
    | LabeledField l f α => GenTree.Node 1 [:: GenTree.Leaf (Some l, f, α)]
    | NestedField f α φ => GenTree.Node 2  (GenTree.Leaf (@None Name, f, α) :: [seq (tree_of_query subquery) | subquery <- φ])
    | NestedLabeledField l f α φ => GenTree.Node 3 (GenTree.Leaf (Some l, f, α) :: [seq (tree_of_query subquery) | subquery <- φ])
    | InlineFragment t φ => GenTree.Node 4 (GenTree.Leaf (None, t, emptym) :: [seq (tree_of_query subquery) | subquery <- φ])
    end.

 (* Equations get_subqueries : seq (option Query) -> seq Query :=
    {
      get_subqueries [::] := [::];
      get_subqueries ((Some q) :: tl) := q :: get_subqueries tl;
      get_subqueries (None :: tl) := get_subqueries tl
    }.
*)

  Fixpoint get_subqueries (queries : seq (option Query)) : seq Query :=
    match queries with
      | [::] => [::]
      | ((Some q) :: tl) => q :: get_subqueries tl
      | (None :: tl) => get_subqueries tl
    end.

  Fixpoint query_of_tree tree : option Query :=
    match tree with
    | (GenTree.Node 0 [:: GenTree.Leaf  (None, f, α)]) => Some (SingleField f α)
      | (GenTree.Node 1 [:: GenTree.Leaf (Some l, f, α)]) => Some (LabeledField l f α)
      | (GenTree.Node 2  (GenTree.Leaf (None, f, α) :: subtree)) =>
        Some (NestedField f α (get_subqueries [seq (query_of_tree t) | t <- subtree]))
      
      | (GenTree.Node 3  (GenTree.Leaf (Some l, f, α) :: subtree)) =>
          Some (NestedLabeledField l f α (get_subqueries [seq (query_of_tree t) | t <- subtree]))
      
      | (GenTree.Node 4  (GenTree.Leaf (None, t, emptym) :: subtree)) =>
        Some (InlineFragment t (get_subqueries [seq (query_of_tree t) | t <- subtree]))
         

      | _ => None
    end.

  (*
  Equations query_of_tree (tree : GenTree.tree (option Name * Name * {fmap Name -> Vals})) : option Query :=
    {
      query_of_tree (GenTree.Node 0 [:: GenTree.Leaf  (None, f, α)]) := Some (SingleField f α);
      query_of_tree (GenTree.Node 1 [:: GenTree.Leaf (Some l, f, α)]) := Some (LabeledField l f α);
      query_of_tree (GenTree.Node 2  (GenTree.Leaf (None, f, α) :: subtree)) :=
        Some (NestedField f α (get_subqueries [seq (query_of_tree t) | t <- subtree]));
      
      query_of_tree (GenTree.Node 3  (GenTree.Leaf (Some l, f, α) :: subtree)) :=
          Some (NestedLabeledField l f α (get_subqueries [seq (query_of_tree t) | t <- subtree]));
      
      query_of_tree (GenTree.Node 4  (GenTree.Leaf (None, t, emptym) :: subtree)) :=
        Some (InlineFragment t (get_subqueries [seq (query_of_tree t) | t <- subtree]));
         

      query_of_tree _ := None

    }. *)
  (*
  Next Obligation.
    elim: tree => //.
    - case=> [[l f] α] => //=.
      by rewrite query_of_tree_equation_1; constructor.
    - case=> //=.
      * case=> //= [| hd tl].
          by rewrite query_of_tree_equation_2; constructor.
        case: hd => //=.
        case=> [[l f] α].
        case: l => [l|].
          by rewrite query_of_tree_equation_3; constructor.
          case: tl.
            by rewrite query_of_tree_equation_4; constructor.
            by intros; rewrite query_of_tree_equation_5; constructor.
        by intros; rewrite query_of_tree_equation_6; constructor.

      * case.
        case; [rewrite query_of_tree_equation_7; constructor| move=> hd tl].
        case: hd.
        case=> [[l f] α].
        case: l => [l|]; [| by rewrite query_of_tree_equation_10; constructor].
        case: tl; intros; rewrite ?query_of_tree_equation_8 ?query_of_tree_equation_9 ; constructor.
        by intros; rewrite query_of_tree_equation_11; constructor.
      * case.
        case; [rewrite query_of_tree_equation_12; constructor| move=> hd tl].
        case: hd.
        case=> [[l f] α].
        case: l => [l|]; [by rewrite query_of_tree_equation_13; constructor |].
        case: tl; intros.
        rewrite query_of_tree_equation_14 /= get_subqueries_equation_1.
        constructor.
        move=> t. apply: x1.
        ?query_of_tree_equation_15 ; constructor.
        by intros; rewrite query_of_tree_equation_17; constructor. *)

  Lemma tree_of_queryK : pcancel tree_of_query query_of_tree.
  Proof.
    move=> q.
    elim q using Query_ind with
        (Pl := fun qs =>
                Forall (fun q' => query_of_tree (tree_of_query q') = Some q') qs) => //=
    [ f α φ /Forall_forall H
    | l f α φ /Forall_forall H
    | t φ /Forall_forall H
    | hd IH tl IH'];
    rewrite -?map_comp; try congr Some;
      [congr (NestedField f α) | congr (NestedLabeledField l f α) | congr (InlineFragment t) | ].

    all: do ?[elim: φ H => //= hd tl IH H;
              have Heq : (hd = hd \/ In hd tl) by left].
    all: do ?[by rewrite (H hd Heq); congr cons; apply: IH => x Hin; apply: H; right].
    by apply: Forall_cons.
  Qed.

  

  Canonical query_eqType := EqType Query (PcanEqMixin tree_of_queryK).
  Canonical query_choiceType := ChoiceType Query (PcanChoiceMixin tree_of_queryK).
  Canonical query_ordType := OrdType Query (PcanOrdMixin tree_of_queryK).

  
  (** Extractors for queries **)
  Definition qname query : option Name :=
    match query with
    | SingleField name _
    | LabeledField _ name _
    | NestedField name _ _
    | NestedLabeledField _ name _ _ => Some name
    | _ => None
    end.

  Definition qlabel query : option Name :=
    match query with
    | LabeledField label _ _
    | NestedLabeledField label _ _ _ => Some label
    | _ => None
    end.
  
  Definition qsubquery query : seq Query :=
    match query with
    | NestedField _ _ ϕ
    | NestedLabeledField _ _ _ ϕ
    | InlineFragment _ ϕ => ϕ
    | _ => [::]
    end.

  Definition qargs query : {fmap Name -> Vals} :=
    match query with
    | SingleField _ α
    | LabeledField _ _ α
    | NestedField _ α _
    | NestedLabeledField _ _ α _ => α
    | _ => emptym
    end.


  (** Extractors for response objects **)
  Definition rname response : Name :=
    match response with
    | Null name
    | SingleResult name _
    | ListResult name _
    | NestedResult name _
    | NestedListResult name _ => name
    end.
  
  
End Query.

Arguments Query [Name Vals].
Arguments SingleField [Name Vals].
Arguments LabeledField [Name Vals].
Arguments NestedField [Name Vals].
Arguments NestedLabeledField [Name Vals].
Arguments InlineFragment [Name Vals].

Arguments ResponseObject [Name Vals].
Arguments Null [Name Vals].