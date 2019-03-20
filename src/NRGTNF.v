Require Import List.
From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.
From extructures Require Import ord fmap.


Require Import Query.
Require Import QueryAux.
Require Import SchemaWellFormedness.

Require Import Schema.
Require Import SchemaAux.

Require Import QueryConformance.

Require Import CpdtTactics.

Section NRGTNF.

  Variables Name Vals : ordType.
  
  Implicit Type schema : @wfSchema Name Vals.
  Implicit Type queries : seq (@Query Name Vals).
  Implicit Type query : @Query Name Vals.
  Notation is_field := (@is_field Name Vals).
  Notation is_inline_fragment := (@QueryAux.is_inline_fragment Name Vals).

  
  
  Equations is_in_normal_form schema (query : @Query Name Vals) : bool :=
    {
      is_in_normal_form schema (NestedField _ _ ϕ) := (all is_field ϕ || all is_inline_fragment ϕ)
                                                       && all (is_in_normal_form schema) ϕ;
      is_in_normal_form schema (NestedLabeledField _ _ _ ϕ) := (all is_field ϕ || all is_inline_fragment ϕ)
                                                                && all (is_in_normal_form schema) ϕ;
      is_in_normal_form schema (InlineFragment t ϕ) := [&& (is_object_type schema t), (all is_field ϕ) & all (is_in_normal_form schema) ϕ];
      is_in_normal_form _ _ := true
    }.


  Definition are_in_normal_form schema (queries : seq (@Query Name Vals)) : bool :=
    (all is_field queries || all is_inline_fragment queries) && all (is_in_normal_form schema) queries.


  Lemma are_in_normal_form_E schema queries :
    are_in_normal_form schema queries ->
    (all is_field queries \/ all is_inline_fragment queries) /\ all (is_in_normal_form schema) queries.
  Proof.
    rewrite /are_in_normal_form.
    by move/andP=> [/orP H H'].
  Qed.


  Lemma all_inlines_shape queries :
    all is_inline_fragment queries ->
    forall query, query \in queries ->
                       exists t ϕ, query = InlineFragment t ϕ.
  Proof.
    move=> /allP H q Hin.
    move: (H q Hin) => {Hin}.
    funelim (is_inline_fragment q) => // _.
    by exists s5; exists l1.
  Qed.
  

    
  Lemma inlines_in_normal_form_have_object_guards schema queries :
    all is_inline_fragment queries ->
    all (is_in_normal_form schema) queries ->
    forall query, query \in queries ->
                       exists t ϕ, query = InlineFragment t ϕ /\ is_object_type schema t.
  Proof.
    move=> Hinlines Hnf q Hin.
    move: (all_inlines_shape queries Hinlines q Hin).
    case=> t; case=> ϕ Heq.    
    move/allP: Hnf; move/(_ q Hin).
    rewrite Heq.
    rewrite is_in_normal_form_equation_5.
    move/and3P=> [Hobj _ _].
      by exists t; exists ϕ.
  Qed.

 
  
  
  Equations is_non_redundant (query : @Query Name Vals) : bool :=
    {
      is_non_redundant (NestedField _ _ φ) := are_non_redundant φ;
      is_non_redundant (NestedLabeledField _ _ _ φ) := are_non_redundant φ;
      is_non_redundant (InlineFragment _ φ) := are_non_redundant φ;
      is_non_redundant _ := true
                             
    }
  where are_non_redundant (queries : seq (@Query Name Vals)) : bool :=
    {
      are_non_redundant [::] := true;
      are_non_redundant (hd :: tl)
        with has (partial_query_eq hd) tl :=
        {
        | true := false;
        | _ := (is_non_redundant hd) && are_non_redundant tl
             
        }
    }.



  Lemma sub_nf schema ty ϕ ϕ' :
    ϕ = [:: InlineFragment ty ϕ'] ->
    are_in_normal_form schema ϕ ->
    all is_field ϕ' /\ all (is_in_normal_form schema) ϕ'.
  Proof.
    move=> -> H.
    move: (are_in_normal_form_E _ _ H) => [_ Hnf].
    move: Hnf; rewrite {1}/all is_in_normal_form_equation_5.
      by move/andP=> [/and3P [Hobj Hfld H'] _].
  Qed.

  




  
End NRGTNF.

Arguments are_in_normal_form [Name Vals].
Arguments are_non_redundant [Name Vals].
Arguments is_non_redundant  [Name Vals].