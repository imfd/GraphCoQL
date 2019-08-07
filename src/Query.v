Require Import List.

From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Asymmetric Patterns.

From CoqUtils Require Import string.

Require Import Base.


Section Query.

  Variables Vals : eqType.

  (** Unsetting because the automatically generated induction principle 
      is not good enough. *)
  Unset Elimination Schemes.

  (** ** Query 


  ----
  **** Observations
  1. Naming : In the spec, an atomic query is referred as "Selection" and 
     the collective as "Selection Sets". Here we preferred to give the 
     name "Query" to an atomic selection instead.
  1. Directives : Currently not implemented.
  2. Syntax : According to the spec, the "opt" keyword means 
     there are two constructors; one with the element and one without. 
     For arguments we just decided to use a list, and represent the optional 
     via the empty list.
  3. J&O : Jorge and Olaf put the list of queries at the same level as the 
     "atomic" selections. We consider them separately, because allowing 
     both at the same level would permit weirdly shaped trees which would have 
     to be flattened eventually (eg. the first element of a list of queries 
     could be another list, with nested lists inside, etc.).

  https://graphql.github.io/graphql-spec/June2018/#sec-Selection-Sets 
  *)
  Inductive Query : Type :=
  | SingleField (response_name : Name)
                (arguments : seq (Name * Vals))
                
  | LabeledField (label : Name)
                 (response_name : Name)
                 (arguments : seq (Name * Vals))
                 
  | NestedField (response_name : Name)
                (arguments : seq (Name * Vals))
                (subqueries : seq Query)
                
  | NestedLabeledField (label : Name)
                       (response_name : Name)
                       (arguments : seq (Name * Vals))
                       (subqueries : seq Query)

  | InlineFragment (type_condition : Name)
                   (subqueries : seq Query).

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




  
  Fixpoint tree_of_query query : GenTree.tree (option Name * Name * seq (Name * Vals)):=
    match query with
    | SingleField f α => GenTree.Node 0 [:: GenTree.Leaf  (None, f, α)]
    | LabeledField l f α => GenTree.Node 1 [:: GenTree.Leaf (Some l, f, α)]
    | NestedField f α φ => GenTree.Node 2  (GenTree.Leaf (None, f, α) :: [seq (tree_of_query subquery) | subquery <- φ])
    | NestedLabeledField l f α φ => GenTree.Node 3 (GenTree.Leaf (Some l, f, α) :: [seq (tree_of_query subquery) | subquery <- φ])
    | InlineFragment t φ => GenTree.Node 4 (GenTree.Leaf (None, t, [::]) :: [seq (tree_of_query subquery) | subquery <- φ])
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



  

    
End Query.

Arguments Query [Vals].
Arguments SingleField [Vals].
Arguments LabeledField [Vals].
Arguments NestedField [Vals].
Arguments NestedLabeledField [Vals].
Arguments InlineFragment [Vals].

Delimit Scope query_scope with QUERY.
Open Scope query_scope.


Notation "f [[ α ]]" := (SingleField f α) (at level 20, α at next level) : query_scope.
Notation "l : f [[ α ]]" := (LabeledField l f α) (at level 20, f at next level, α at next level)  : query_scope.
Notation "f [[ α ]] { φ }" := (NestedField f α φ) (at level 20, α at next level, φ at next level) : query_scope.
Notation "l : f [[ α ]] { φ }" := (NestedLabeledField l f α φ)
                                 (at level 20, f at next level, α at next level, φ at next level)  : query_scope.
Notation "'on' t { φ }" := (InlineFragment t φ) (t at next level, φ at next level) : query_scope.
