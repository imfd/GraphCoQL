Require Import List.
From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.
From extructures Require Import ord fmap.


Require Import Query.
Require Import QueryAux.
Require Import SchemaWellFormedness.

Require Import Schema.
Require Import SchemaAux.

Require Import CpdtTactics.

Section NRGTNF.

  Variables Name Vals : ordType.
  
  Implicit Type queries : seq (@Query Name Vals).
  Implicit Type query : @Query Name Vals.

    
  Equations is_field query : bool :=
    is_field (InlineFragment _ _) := false;
    is_field _ := true.

  Definition is_inline_fragment query : bool := ~~ is_field query.

      
  Equations is_in_normal_form (query : @Query Name Vals) : bool :=
    {
      is_in_normal_form (NestedField _ _ ϕ) := (all is_field ϕ || all is_inline_fragment ϕ) && all is_in_normal_form ϕ;
      is_in_normal_form (NestedLabeledField _ _ _ ϕ) := (all is_field ϕ || all is_inline_fragment ϕ) && all is_in_normal_form ϕ;
      is_in_normal_form (InlineFragment _ ϕ) := (all is_field ϕ) && all is_in_normal_form ϕ;
      is_in_normal_form _ := true
    }.
  
  Definition are_in_normal_form (queries : seq (@Query Name Vals)) : bool :=
    (all is_field queries || all is_inline_fragment queries) && all is_in_normal_form queries.  

  Fixpoint no_repeated_query (queries : list (@Query Name Vals)) : bool :=
     match queries with
        | [::] => true
        | hd :: tl => if has (partial_query_eq hd) tl then
                       false
                     else
                       no_repeated_query tl
     end.


  Equations is_non_redundant (query : @Query Name Vals) : bool :=
    {
      is_non_redundant (NestedField _ _ ϕ) := no_repeated_query ϕ && all is_non_redundant ϕ;
      is_non_redundant (NestedLabeledField _ _ _ ϕ) := no_repeated_query ϕ && all is_non_redundant ϕ;
      is_non_redundant (InlineFragment _ ϕ) := no_repeated_query ϕ && all is_non_redundant ϕ;
      is_non_redundant _ := true
    }.

  Definition are_non_redundant (queries : seq (@Query Name Vals)) : bool :=
    no_repeated_query queries && all is_non_redundant queries.

  Lemma is_are_non_redundant_nf n α ϕ :
    is_non_redundant (NestedField n α ϕ) = are_non_redundant ϕ.
  Proof. done. Qed.

  Lemma is_are_non_redundant_nlf l n α ϕ :
    is_non_redundant (NestedLabeledField l n α ϕ) = are_non_redundant ϕ.
  Proof. done. Qed.

  Lemma is_are_non_redundant_if t ϕ :
    is_non_redundant (InlineFragment t ϕ) = are_non_redundant ϕ.
  Proof. done. Qed.
      

End NRGTNF.