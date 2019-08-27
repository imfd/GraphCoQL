(* begin hide *)

Require Import List.

From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Asymmetric Patterns.

Require Import String.
Require Import QString.


Notation Name := string.

(* end hide *)

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">GraphQL Query</h1>
        <p class="lead">
         This file contains the basic definitions necessary to build a GraphQL Query. 
        </p>
         <p>
        These definitions allow building a Query but they do not guarantee that it is valid wrt. to a Schema.
        This notion of conformance/validation is covered in the <a href='GraphCoQL.QueryConformance.html'>QueryConformance</a> file.
    
        </p>
  </div>
</div>#
 *)

Section Query.
  
  Variables Vals : eqType.

  (**
     We start by defining the Query syntax.
   *)
  
  (* Unsetting because the automatically generated induction principle is not good enough. *)
  Unset Elimination Schemes.

  (** ** Query 
      
      A Query corresponds to an atomic selection one may perform in a GraphQL service. 
      It can either be a field selection or an inline fragment.
      
      A query can be seen as a tree, where fields without subqueries would 
      represent the leaves of the tree and fields with subqueries, as well as 
      inline fragments with represent inner nodes.

      #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
      **** Observations

      - Naming : In the spec, an atomic query is referred as a "Selection" and 
        the collective as "Selection Sets". Here, we preferred to give the 
        name "Query" to the type of an atomic selection instead and a list of Query will 
        be referred as queries. Both "query" and "queries" might be used interchangeably, 
        assuming that it is understood by context.

      - Directives : Currently not implemented.

      - Syntax : According to the spec, the "opt" keyword means 
        there are two constructors; one with the element and one without. 
        For arguments we just decided to use a list, and represent the optional 
        via the empty list.

      - P&H : Pérez & Hartig put the list of queries at the same level as the 
        atomic selections. This differs from the spec and from our implementation, 
        where we consider them separately. Allowing both at the same level would
        permit any shape of query tree to be generated (eg. the first element of a list of queries 
        could be another list, with nested lists inside, etc.). This would 
        require to flatten the queries eventually to check for conformance or other properties.

      - Fragment spread : Currently not implemented. As pointed out in J&O, fragment spreads are a 
        convenience over inline fragments, therefore we prefer not to include them for the moment.

      - Variables : Currently not implemented. Similarly to fragment spreads, we prefer to not
      include them for the moment.

      #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
      **** Spec Reference
     
      - #<a href='https://graphql.github.io/graphql-spec/June2018/##Selection'>Selection</a>#      
      - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Selection-Sets'>Selection Sets</a>#
      
  *)
  Inductive Query : Type :=
  | SingleField (name : Name)
                (arguments : seq (Name * Vals))
                
  | LabeledField (alias : Name)
                 (name : Name)
                 (arguments : seq (Name * Vals))
                 
  | NestedField (name : Name)
                (arguments : seq (Name * Vals))
                (subqueries : seq Query)
                
  | NestedLabeledField (alias : Name)
                       (name : Name)
                       (arguments : seq (Name * Vals))
                       (subqueries : seq Query)

  | InlineFragment (type_condition : Name)
                   (subqueries : seq Query).

  
  Set Elimination Schemes.


  (**
     Defining the induction principles for Query.
   *)
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




  (**
     Declaring functions to establish isomorphism of Query to GenTree, allowing us 
     to later prove that Query has a decidable equality procedure.
     
     We could define our own procedure but this way we may also benefit from other properties
     defined for GenTree already.
   *)
  (* Maybe not... we are not really using anything else *)
  
  (**
     tree_of_query : Query -> GenTree.tree (option Name * Name * List (Name * Vals))

     Converts a Query into a tree.
   *)
  Fixpoint tree_of_query query : GenTree.tree (option Name * Name * seq (Name * Vals)):=
    match query with
    | SingleField f α => GenTree.Node 0 [:: GenTree.Leaf  (None, f, α)]
    | LabeledField l f α => GenTree.Node 1 [:: GenTree.Leaf (Some l, f, α)]
    | NestedField f α φ => GenTree.Node 2  (GenTree.Leaf (None, f, α) :: [seq (tree_of_query subquery) | subquery <- φ])
    | NestedLabeledField l f α φ => GenTree.Node 3 (GenTree.Leaf (Some l, f, α) :: [seq (tree_of_query subquery) | subquery <- φ])
    | InlineFragment t φ => GenTree.Node 4 (GenTree.Leaf (None, t, [::]) :: [seq (tree_of_query subquery) | subquery <- φ])
    end.


  (**
     get_subqueries : List (option Query) -> List Query 

     Retrieves elements of a list of options which are not None.

     This could be generalised.
   *)
  Fixpoint get_subqueries (queries : seq (option Query)) : seq Query :=
    match queries with
      | [::] => [::]
      | ((Some q) :: tl) => q :: get_subqueries tl
      | (None :: tl) => get_subqueries tl
    end.

  (**
     query_of_tree : GenTree.tree -> option Query 

     Converts a tree into a Query.

     If the tree cannot be converted then it returns None.
   *)
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


  (**
     Proving cancelling lemma, used to establish isomorphism between Query 
     and GenTree, which can be used to establish that Query is in eqType.
   *)
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

  
  (**
     Defining query_eqType.
   *)
  Canonical query_eqType := EqType Query (PcanEqMixin tree_of_queryK).



  

    
End Query.

Arguments Query [Vals].
Arguments SingleField [Vals].
Arguments LabeledField [Vals].
Arguments NestedField [Vals].
Arguments NestedLabeledField [Vals].
Arguments InlineFragment [Vals].


(**
   Notations follow closely to the ones used in J&O.
 *)
Delimit Scope query_scope with QUERY.
Open Scope query_scope.

(* Maybe we could add formatting *)

Notation "f [[ α ]]" := (SingleField f α) (at level 20, α at next level) : query_scope.
Notation "l : f [[ α ]]" := (LabeledField l f α) (at level 20, f at next level, α at next level)  : query_scope.
Notation "f [[ α ]] { φ }" := (NestedField f α φ) (at level 20, α at next level, φ at next level) : query_scope.
Notation "l : f [[ α ]] { φ }" := (NestedLabeledField l f α φ)
                                 (at level 20, f at next level, α at next level, φ at next level)  : query_scope.
Notation "'on' t { φ }" := (InlineFragment t φ) (t at next level, φ at next level) : query_scope.
