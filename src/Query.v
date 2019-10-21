(* begin hide *)

Require Import List.

From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Asymmetric Patterns.
From Equations Require Import Equations.

Require Import String.
Require Import QString.

Require Import Value.

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
  
  Variable (Scalar : eqType).

  
  (* Unsetting because the automatically generated induction principle is not good enough. *)
  Unset Elimination Schemes.

  (** * Selection 
      (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##Selection'><span>&#167;</span>2.4</a>#)
      ----

      A Selection corresponds to an atomic piece of information one may request from a GraphQL service. 
      It can either be a field selection or an inline fragment.
      
      A selection can be seen as a tree, where fields without subqueries 
      represent the leaves of the tree and fields with subqueries, as well as 
      inline fragments represent inner nodes.

      #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
      **** Observations

      - SelectionSets (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##SelectionSet'><span>&#167;</span>2.4</a>#): 
        The Spec defines a mutually inductive type, using 
        SelectionSets and Selection, where the former represents a non-empty list.
        We decide to separate them and define selections as a list.      
  *)
  Inductive Selection : Type :=
  | SingleField (name : Name)
                (arguments : seq (Name * @Value Scalar))
                
  | SingleAliasedField (alias : Name)
                       (name : Name)
                       (arguments : seq (Name * @Value Scalar))
                 
  | NestedField (name : Name)
                (arguments : seq (Name * @Value Scalar))
                (subselections : seq Selection)
                
  | NestedAliasedField (alias : Name)
                       (name : Name)
                       (arguments : seq (Name * @Value Scalar))
                       (subselections : seq Selection)

  | InlineFragment (type_condition : Name)
                   (subselections : seq Selection).

  
  Set Elimination Schemes.

  
  (**
     Defining the induction principle for Selection.
   *)
  (** ---- *)
  Definition Selection_rect (P : Selection -> Type)
             (Pl : seq Selection -> Type)
             (IH_SF : forall n α, P (SingleField n α))
             (IH_LF : forall l n α, P (SingleAliasedField l n α))
             (IH_NF : forall n α σs, Pl σs -> P (NestedField n α σs))
             (IH_NLF : forall l n α σs, Pl σs -> P (NestedAliasedField l n α σs))
             (IH_IF : forall t σs, Pl σs -> P (InlineFragment t σs))
             (IH_Nil : Pl [::])
             (IH_Cons : forall q, P q -> forall qs, Pl qs -> Pl (q :: qs))
    :=
    fix loop selection : P selection :=
      let fix F (qs : seq Selection) : Pl qs :=
          match qs with
          | [::] => IH_Nil
          | hd :: tl => IH_Cons hd (loop hd) tl (F tl)
          end
      in
      match selection with
      | SingleField n α => IH_SF n α
      | SingleAliasedField l n α => IH_LF l n α
      | NestedField n α σs => IH_NF n α σs (F σs)
      | NestedAliasedField l n α σs => IH_NLF l n α σs (F σs)
      | InlineFragment t σs => IH_IF t σs (F σs)
      end.

  Definition Selection_rec (P : Selection -> Set) := @Selection_rect P.

  Definition Selection_ind (P : Selection -> Prop)
             (Pl : seq Selection -> Prop)
            (IH_SF : forall n α, P (SingleField n α))
            (IH_LF : forall l n α, P (SingleAliasedField l n α))
            (IH_NF : forall n α σs, Pl σs -> P (NestedField n α σs))
            (IH_NLF : forall l n α σs, Pl σs -> P (NestedAliasedField l n α σs))
            (IH_IF : forall t σs, Pl σs -> P (InlineFragment t σs))
            (IH_Nil : Pl [::])
            (IH_Cons : forall σ, P σ -> forall σs, Pl σs -> Pl (σ :: σs))
    :=
      fix loop selection : P selection :=
        let fix F (qs : seq Selection) : Pl qs :=
          match qs with
          | [::] => IH_Nil
          | hd :: tl => IH_Cons hd (loop hd) tl (F tl)
          end
        in
        match selection with
        | SingleField n α => IH_SF n α
        | SingleAliasedField l n α => IH_LF l n α
        | NestedField n α σs => IH_NF n α σs (F σs)
        | NestedAliasedField l n α σs => IH_NLF l n α σs (F σs)
        | InlineFragment t σs => IH_IF t σs (F σs)
        end.


  (** * Query 
      (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Language.Operations'><span>&#167;</span>2.3</a>#)
      ----

     A query is one of the three operations executable in a GraphQL service
     and it is formed by an optional name and a list of selections.

   *)
  Record query := Query {
                     qname : option string;
                     selection_set : seq Selection
                   }.


    
End Query.

(* begin hide *)
Arguments Selection [Scalar].
Arguments SingleField [Scalar].
Arguments SingleAliasedField [Scalar].
Arguments NestedField [Scalar].
Arguments NestedAliasedField [Scalar].
Arguments InlineFragment [Scalar].

Arguments query [Scalar].
Arguments Query [Scalar].
Arguments qname [Scalar].
Arguments selection_set [Scalar].
(* end hide *)

(** *** Notations 
    ----

    Notations follow closely to the ones used in Hartig & Pérez.
 *)
Delimit Scope selection_scope with QUERY.
Open Scope selection_scope.

(* Maybe we could add formatting *)
(* We are using double brackets because there is too much conflict with these notations and
   others already used... And I don't really get how to fix it *)
Notation "f [[ α ]]" := (SingleField f α) (at level 20, α at next level) : selection_scope.
Notation "l : f [[ α ]]" := (SingleAliasedField l f α) (at level 20, f at next level, α at next level)  : selection_scope.
Notation "f [[ α ]] { σs }" := (NestedField f α σs) (at level 20, α at next level, σs at next level) : selection_scope.
Notation "l : f [[ α ]] { σs }" := (NestedAliasedField l f α σs)
                                 (at level 20, f at next level, α at next level, σs at next level)  : selection_scope.
Notation "'on' t { σs }" := (InlineFragment t σs) (t at next level, σs at next level) : selection_scope.

(** ---- *)


(**
   We also establish that all these structures have a decidable procedure for equality but 
   we omit them here to unclutter the doc (they may still be seen in the source code).
 *)


(* begin hide *)
Section Equality.

  Variable (Scalar : eqType).
  
  (** * Equality 
     This section deals with some SSReflect bureaucratic things, in particular 
     establishing that a Selection has decidable procedure to establish equality (they belong to the 
     SSReflect type - eqType).
   *)

  (**
     #<strong>selection_eq</strong# : Selection → Selection → Bool 

     The equality procedure.
   *)
  Equations selection_eq (σ1 σ2 : @Selection Scalar) : bool :=
    {
      selection_eq (f1[[α1]]) (f2[[α2]]) := (f1 == f2) && (α1 == α2);
      selection_eq (a1:f1[[α1]]) (a2:f2[[α2]]) := [&& a1 == a2, f1 == f2 & α1 == α2];
      selection_eq (f1[[α1]] { σs1 }) (f2[[α2]] { σs2 }) :=
        [&& f1 == f2, α1 == α2 & selections_eq σs1 σs2];
      selection_eq (a1:f1[[α1]] { σs1 }) (a2:f2[[α2]] { σs2 }) :=
        [&& a1 == a2, f1 == f2, α1 == α2 & selections_eq σs1 σs2];
      selection_eq (on t1 { σs1 }) (on t2 { σs2 }) :=
        (t1 == t2) && (selections_eq σs1 σs2);
      selection_eq _ _ := false 
    }
  where selections_eq (σs1 σs2 : seq (@Selection Scalar)) : bool :=
          {
            selections_eq [::] [::] := true;
            selections_eq (σ1 :: σs1) (σ2 :: σs2) := selection_eq σ1 σ2 && selections_eq σs1 σs2;
            selections_eq _ _ := false
          }.

  (**
     This lemma states that indeed the equality procedure coincides
     with equality of the terms.
   *)
  Transparent selection_eq.
  Lemma selection_eqP : Equality.axiom selection_eq.
  Proof.
    rewrite /Equality.axiom => x y.
    apply: (iffP idP) => //= [| ->]; last first.
    - elim y using Selection_ind with
          (Pl := fun σs => selections_eq σs σs) => //=;
                                                intros; simp selection_eq.
      all: do ? [apply/andP; split=> //].
      
    - move: y.
      elim x using Selection_ind with
          (Pl := fun σs => forall σs2, selections_eq σs σs2 -> σs = σs2); intros.

      * by case: y H => //= n2 α2 /andP [/eqP -> /eqP ->].
      * by case: y H => //= a2 n2 α2 /and3P [/eqP -> /eqP -> /eqP ->]. 
      * case: y H0 => // n2 α2 σs2; simp selection_eq => /and3P [/eqP -> /eqP -> Hsseq].
          by rewrite (H _ Hsseq).
      * case: y H0 => // a2 n2 α2 σs2; simp selection_eq => /and4P [/eqP -> /eqP -> /eqP -> Hsseq].
          by rewrite (H _ Hsseq).
          
      * case: y H0 => // t2 σs2; simp selection_eq => /andP [/eqP -> Hsseq].
          by rewrite (H _ Hsseq).

      * by case: σs2 H => //.
      * case: σs2 H1 => // σ2 σs2; rewrite selections_eq_equation_4 => /andP [Heq1 Heq2].
          by congr cons; [apply: H | apply: H0].
  Qed.
      
  
  (**
     Defining selection_eqType.
   *)
  Canonical selection_eqType := EqType Selection (EqMixin selection_eqP).

  Definition tuple_of_query (q : @query Scalar) := let: (Query n b) := q in (n, b).
  Definition query_of_tuple (nb : option Name * seq (@Selection Scalar)) := let: (n, b) := nb in Query n b.

  Lemma tuple_of_queryK : cancel tuple_of_query query_of_tuple.
  Proof. by case. Qed.

  Canonical query_eqType := EqType query (CanEqMixin tuple_of_queryK).

End Equality.

(* end hide *)


(** ---- *)
(** 
    #<div>
        <a href='GraphCoQL.GraphConformance.html' class="btn btn-light" role='button'> Previous ← Graph Conformance  </a>
        <a href='GraphCoQL.QueryConformance.html' class="btn btn-info" role='button'>Continue Reading → Query Conformance </a>
    </div>#
*)