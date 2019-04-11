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


Require Import Ssromega.

Delimit Scope query_scope with QUERY.
Open Scope query_scope.


Section Forallt.
    Inductive Forallt {A : Type} (P : A -> Type) : list A -> Type :=
      Forallt_nil : Forallt P nil
    | Forallt_cons : forall (x : A) (l : list A),
        P x -> Forallt P l -> Forallt P (x :: l).

End Forallt.

Section ListIn.
  
  Equations map_In {A B : Type}
     (l : list A) (f : forall (x : A), In x l -> B) : list B :=
    map_In nil _ := nil;
    map_In (cons x xs) f := cons (f x _) (map_In xs (fun x H => f x _)).

End ListIn.

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
             (Pl : seq ResponseObject -> Prop)
             (Pl2 : seq (seq ResponseObject) -> Prop) 
             (IH_Null : forall n, P (Null n))
             (IH_SR : forall n v, P (SingleResult n v))
             (IH_LR : forall n vals, P (ListResult n vals))
             (IH_NR : forall n ρ, Pl ρ -> P (NestedResult n ρ))
             (IH_NLR : forall n ρ, Pl2 ρ -> P (NestedListResult n ρ))
             (IH_Nil : Pl [::])
             (IH_Cons : forall r, P r -> forall rs, Pl rs -> Pl (r :: rs))
             (IH_Nil2 : Pl2 [::])
             (IH_Cons2 : forall rs, Pl rs -> forall rss, Pl2 rss -> Pl2 (rs :: rss))

    :=
      fix loop response : P response :=
        let fix F0 (ρ : seq ResponseObject) : Pl ρ :=
            match ρ with
            | [::] => IH_Nil
            | hd :: tl => IH_Cons hd (loop hd) tl (F0 tl)
            end
        in
        let fix F1 (ρ : seq (seq ResponseObject)) : Pl2 ρ :=
            match ρ as r with
            | [::] => IH_Nil2
            | hd :: tl => IH_Cons2 hd (F0 hd) tl (F1 tl)
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
             (Pl : seq ResponseObject -> Prop)
             (Pl2 : seq (seq ResponseObject) -> Prop) 
             (IH_Null : forall n, P (Null n))
             (IH_SR : forall n v, P (SingleResult n v))
             (IH_LR : forall n vals, P (ListResult n vals))
             (IH_NR : forall n ρ, Pl ρ -> P (NestedResult n ρ))
             (IH_NLR : forall n ρ, Pl2 ρ -> P (NestedListResult n ρ))
             (IH_Nil : Pl [::])
             (IH_Cons : forall r, P r -> forall rs, Pl rs -> Pl (r :: rs))
             (IH_Nil2 : Pl2 [::])
             (IH_Cons2 : forall rs, Pl rs -> forall rss, Pl2 rss -> Pl2 (rs :: rss))

    :=
      fix loop response : P response :=
        let fix F0 (ρ : seq ResponseObject) : Pl ρ :=
            match ρ with
            | [::] => IH_Nil
            | hd :: tl => IH_Cons hd (loop hd) tl (F0 tl)
            end
        in
        let fix F1 (ρ : seq (seq ResponseObject)) : Pl2 ρ :=
            match ρ as r with
            | [::] => IH_Nil2
            | hd :: tl => IH_Cons2 hd (F0 hd) tl (F1 tl)
            end
        in
        match response with
        | Null n => IH_Null n
        | SingleResult n v => IH_SR n v
        | ListResult n vals => IH_LR n vals
        | NestedResult n ρ => IH_NR n ρ (F0 ρ)
        | NestedListResult n ρ => IH_NLR n ρ (F1 ρ)
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


  

  Fixpoint tree_of_response response : GenTree.tree (Name * option (Vals + seq Vals)) :=
    match response with
    | Null l => GenTree.Node 0 [:: GenTree.Leaf (l, None)]
    | SingleResult l v => GenTree.Node 1 [:: GenTree.Leaf (l, Some (inl v))]
    | ListResult l vs => GenTree.Node 2 [:: GenTree.Leaf (l, Some (inr vs))]
    | NestedResult l ρ => GenTree.Node 3 (GenTree.Leaf (l, None) :: [seq tree_of_response r | r <- ρ])
    | NestedListResult l ρs =>
      GenTree.Node 4 (GenTree.Leaf (l, None) :: [seq GenTree.Node 5 [seq tree_of_response r | r <- ρ] | ρ <- ρs])
    end.
  
  Fixpoint get_subresponses (responses : seq (option ResponseObject)) : seq ResponseObject :=
    match responses with
      | [::] => [::]
      | ((Some r) :: tl) => r :: get_subresponses tl
      | (None :: tl) => get_subresponses tl
    end.

  Definition get_subtree tree : seq (GenTree.tree (Name * option (Vals + seq Vals))) :=
    match tree with
    | GenTree.Node 5 st =>  st
    | _ => [::]
    end.


  Equations(noind) response_tree_size (tree : GenTree.tree (Name * option (Vals + seq Vals))) : nat 
    :=
    {
      response_tree_size (GenTree.Node 0 [:: GenTree.Leaf (l, None)]) := 3;
      response_tree_size (GenTree.Node 1 [:: GenTree.Leaf (l, Some (inl v))]) := 3;
      response_tree_size (GenTree.Node 2 [:: GenTree.Leaf (l, Some (inr vs))]) := 4 + size vs;
      response_tree_size (GenTree.Node 3 (GenTree.Leaf (l, None) :: subtree)) := 4 + sumn [seq response_tree_size t | t <- subtree];
      response_tree_size (GenTree.Node 4 (GenTree.Leaf (l, None) :: subtree)) :=
          4 + 2 * size subtree + sumn [seq response_tree_size t | t <- subtree];
      response_tree_size (GenTree.Node 5 subtree) := sumn [seq response_tree_size t | t <- subtree];
      response_tree_size _ := 0
    }.


  Lemma response_tree_size_lt x s :
    In x s ->
    response_tree_size x <= sumn [seq response_tree_size t | t <- s].
  Proof.
    elim: s x => //= hd tl IH x.
    case=> [->| Hin].
      by ssromega.
    move: (IH x Hin) => Hlt.
      by ssromega.
  Qed.

   Lemma get_subtree_size_lt s :
     sumn [seq response_tree_size t | t <- get_subtree s] <= response_tree_size s.
   Proof.
     case: s => //.
     do ?[case => //].
   Qed.
 
  
  Equations response_of_tree (tree : GenTree.tree (Name * option (Vals + seq Vals))) : option ResponseObject
    by wf (response_tree_size tree) lt 
    :=
    {
      response_of_tree (GenTree.Node 0 [:: GenTree.Leaf (l, None)]) := Some (Null l);
      response_of_tree (GenTree.Node 1 [:: GenTree.Leaf (l, Some (inl v))]) := Some (SingleResult l v);
      response_of_tree (GenTree.Node 2 [:: GenTree.Leaf (l, Some (inr vs))]) := Some (ListResult l vs);
      response_of_tree (GenTree.Node 3 (GenTree.Leaf (l, None) :: subtree)) :=
        Some (NestedResult l (get_subresponses (map_In subtree (fun t H => response_of_tree t))));


      response_of_tree (GenTree.Node 4 (GenTree.Leaf (l, None) :: subtree)) :=
        Some (NestedListResult l (map_In subtree (fun st H1 =>
                                                    get_subresponses (map_In (get_subtree st) (fun t H2 => response_of_tree t)))));

      response_of_tree _ := None

    }.
  Next Obligation.
    simp response_tree_size.
    move: (response_tree_size_lt t subtree H) => Hlt.
      by ssromega.

  Qed.
  Next Obligation.
    simp response_tree_size.
    move: (response_tree_size_lt st subtree H1) => Hlt1.
    move: (response_tree_size_lt t _ H2) => Hlt.
    move: (get_subtree_size_lt st) => Hlt3.
      by ssromega.
  Qed.

  Lemma tree_of_responseK : pcancel tree_of_response response_of_tree.
  Proof.
    move=> r.
    elim r using ResponseObject_ind with
        (Pl := fun rs =>
                Forall (fun r => response_of_tree (tree_of_response r) = Some r) rs)
        (Pl2 := fun rss =>
                 Forall (fun rs => Forall (fun r => response_of_tree (tree_of_response r) = Some r) rs) rss) => //.

    - move=> l ρ IH /=.
      simp response_of_tree.
      congr Some.
  Admitted.

  
  Canonical response_eqType := EqType ResponseObject (PcanEqMixin tree_of_responseK).
  Canonical response_choiceType := ChoiceType ResponseObject (PcanChoiceMixin tree_of_responseK).
  Canonical response_ordType := OrdType ResponseObject (PcanOrdMixin tree_of_responseK).

  
End Query.

Arguments Query [Name Vals].
Arguments SingleField [Name Vals].
Arguments LabeledField [Name Vals].
Arguments NestedField [Name Vals].
Arguments NestedLabeledField [Name Vals].
Arguments InlineFragment [Name Vals].

Arguments ResponseObject [Name Vals].
Arguments Null [Name Vals].
Arguments SingleResult [Name Vals].
Arguments ListResult [Name Vals].
Arguments NestedResult [Name Vals].
Arguments NestedListResult [Name Vals].


Arguments rname [Name Vals].