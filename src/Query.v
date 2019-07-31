Require Import List.

From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Asymmetric Patterns.

From Equations Require Import Equations.
From extructures Require Import ord fmap.


Require Import treeordtype.
Require Import Schema.
Require Import SchemaAux.

Require Import SeqExtra.
Require Import Ssromega.

Delimit Scope query_scope with QUERY.
Open Scope query_scope.

Require Import Arith.

Section Query.

  Variables Name Vals : ordType.

  Unset Elimination Schemes.
  Inductive Query : Type :=
  | SingleField : Name -> {fmap Name -> Vals} -> Query
  | LabeledField : Name -> Name -> {fmap Name -> Vals} -> Query
  | NestedField : Name -> {fmap Name -> Vals} -> seq Query -> Query
  | NestedLabeledField : Name -> Name -> {fmap Name -> Vals} -> seq Query -> Query
  | InlineFragment : @NamedType Name -> seq Query -> Query.

 
  
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



  Fixpoint tree_of_query query : GenTree.tree (option Name * Name * {fmap Name -> Vals}):=
    match query with
    | SingleField f α => GenTree.Node 0 [:: GenTree.Leaf  (None, f, α)]
    | LabeledField l f α => GenTree.Node 1 [:: GenTree.Leaf (Some l, f, α)]
    | NestedField f α φ => GenTree.Node 2  (GenTree.Leaf (@None Name, f, α) :: [seq (tree_of_query subquery) | subquery <- φ])
    | NestedLabeledField l f α φ => GenTree.Node 3 (GenTree.Leaf (Some l, f, α) :: [seq (tree_of_query subquery) | subquery <- φ])
    | InlineFragment t φ => GenTree.Node 4 (GenTree.Leaf (None, t, emptym) :: [seq (tree_of_query subquery) | subquery <- φ])
    end.



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


   (** Boolean predicates to check what type the query is:
      - Fields : Everything not an inline fragment
      - Inline : An inline fragment 
   **)
  Equations is_field (query : Query) : bool :=
    is_field (InlineFragment _ _) := false;
    is_field _ := true.

  Equations is_inline_fragment (query : Query) : bool :=
    is_inline_fragment (InlineFragment _ _) := true;
    is_inline_fragment _ := false.       

  Definition is_labeled (query : Query) : bool :=
    match query with
    | LabeledField _ _ _
    | NestedLabeledField _ _ _ _ => true
    | _ => false
    end.

  Definition has_subqueries (query : Query) : bool :=
    match query with
    | SingleField _ _
    | LabeledField _ _ _ => false
    | _ => true
    end.
  
  (** Extractors for queries **)
  Equations qname query (Hfld : query.(is_field)) :  Name :=
    {
      qname (SingleField f _) _ := f;
      qname (LabeledField _ f _) _ := f;
      qname (NestedField f _ _) _ := f;
      qname (NestedLabeledField _ f _ _) _ := f;
      qname (InlineFragment _ _) Hfld := _
    }.

  Equations oqname (query : Query) : option Name :=
    {
      oqname (InlineFragment _ _) := None;
      oqname q := Some (qname q _)
    }.

    
  Equations qlabel query (Hlab : query.(is_labeled)) : Name :=
    {
      qlabel (LabeledField label _ _) _ := label;
      qlabel (NestedLabeledField label _ _ _) _ := label;
      qlabel _ Hlab := _
    }.

  Equations oqlabel (query : Query) : option Name :=
    {
      oqlabel (LabeledField label _ _) := Some label;
      oqlabel (NestedLabeledField label _ _ _) := Some label;
      oqlabel _ := None
    }.
                         
    
  Definition qsubqueries query : seq Query :=
    match query with
    | NestedField _ _ ϕ
    | NestedLabeledField _ _ _ ϕ
    | InlineFragment _ ϕ => ϕ
    | _ => [::]
    end.

  Equations qsubqueries' (query : Query) (Hhas : query.(has_subqueries)) : seq Query :=
    {
      qsubqueries' query Hhas := query.(qsubqueries)
    }.
 
  
  Equations qargs query (Hfld : query.(is_field)) :  {fmap Name -> Vals} :=
    {
      qargs (SingleField _ α) _ := α;
      qargs (LabeledField _ _ α) _ := α;
      qargs (NestedField _ α _) _ := α;
      qargs (NestedLabeledField _ _ α _) _ := α;
      qargs (InlineFragment _ _) Hfld := _
    }.

  Equations oqargs (query : Query) : option {fmap Name -> Vals} :=
    {
      oqargs (InlineFragment _ _) := None;
      oqargs q := Some (qargs q _)
    }.

  
  Equations qresponse_name query (Hfld : query.(is_field)) :  Name :=
    {
      qresponse_name (SingleField f _) _ := f;
      qresponse_name (LabeledField l _ _) _ := l;
      qresponse_name (NestedField f _ _) _ := f;
      qresponse_name (NestedLabeledField l _ _ _) _ := l;
      qresponse_name (InlineFragment _ _) Hfld := _
    }.

  Equations oqresponse_name (query : Query) : option Name :=
    {
      oqresponse_name (InlineFragment _ _) := None;
      oqresponse_name q := Some (qresponse_name q _)
    }.


    
End Query.

Arguments Query [Name Vals].
Arguments SingleField [Name Vals].
Arguments LabeledField [Name Vals].
Arguments NestedField [Name Vals].
Arguments NestedLabeledField [Name Vals].
Arguments InlineFragment [Name Vals].


Arguments is_field [Name Vals].
Arguments is_inline_fragment [Name Vals].
Arguments is_labeled [Name Vals].
Arguments has_subqueries [Name Vals].

Arguments qname [Name Vals].
Arguments oqname [Name Vals].
Arguments qlabel [Name Vals].
Arguments oqlabel [Name Vals].
Arguments qargs [Name Vals].
Arguments oqargs [Name Vals].
Arguments qsubqueries [Name Vals].
Arguments qsubqueries' [Name Vals].
Arguments qresponse_name [Name Vals].
Arguments oqresponse_name [Name Vals].