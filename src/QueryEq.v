From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From Equations Require Import Equations.
From extructures Require Import ord fset fmap.


Require Import SeqExtra.

Require Import Schema.
Require Import SchemaAux.

Require Import SchemaWellFormedness.
Require Import Query.
Require Import QueryAux.

Require Import Graph.
Require Import GraphAux.

Require Import GraphConformance.
Require Import QueryConformance.
Require Import QuerySemantic.
Require Import NRGTNF.

Require Import ValidFragments.

Require Import QueryRewrite.

Section Eq.

  Variables N Name Vals : ordType.
  Implicit Type schema : @wfSchema Name Vals.


  Ltac orL := apply/orP; left.
  Ltac orR := apply/orP; right.
  
  Ltac apply_andP := apply/andP; split=> //.
  Ltac apply_and3P := apply/and3P; split=> //.
  Ltac are_in_normal_form := rewrite /are_in_normal_form => /andP; case.
  Ltac all_cons := rewrite {1}/all -/(all _ _) => /andP; case.
  Ltac query_conforms := rewrite /query_conforms -/(query_conforms _ _); try move/and4P; try apply/and4P.
  
 

  
 


  Open Scope fset.

 
 
    
  
  Lemma nrl_subqueries (n : Name) (ϕ ϕ' : seq (seq (@ResponseObject Name Vals))) : ϕ = ϕ' -> NestedListResult n ϕ = NestedListResult n ϕ'. Proof. by move=> ->. Qed.


 
  Lemma inlined_query_eq_eval schema (g : @conformedGraph Name Vals schema) u ty φ :
    query_conforms schema ty φ ->
    get_possible_types schema ty <> [::] ->
    eval schema g u φ =
    eval_queries schema g u [seq InlineFragment t [:: φ] | t <- get_possible_types schema ty].
  Proof.
  Admitted.
    

  Lemma map_normalize_eval_eq :
    forall schema ty φ (g : @conformedGraph Name Vals schema) (nodes : seq node),
      (forall u, eval_queries schema g u φ = eval_queries schema g u (normalize__φ schema ty φ)) ->
      [seq eval_queries schema g v φ | v <- nodes] =
      [seq eval_queries schema g v (normalize__φ schema ty φ) | v <- nodes].
  Proof.
    move=> schema ty φ g nodes H.
    elim: nodes => //= hd tl IH.
    rewrite IH.
    congr cons.
    by rewrite (H hd).
  Qed.
    
  Lemma normalize_preserves_eval :
    forall schema ty φ (g : @conformedGraph Name Vals schema) u,
      query_conforms schema ty φ ->
      has_valid_fragments schema ty φ ->
      eval schema g u φ =  eval_queries schema g u (normalize schema ty φ).
  Proof.
    apply (normalize_elim
             (fun schema ty q nqs =>
                forall (g : @conformedGraph Name Vals schema) u,
                  query_conforms schema ty q ->
                  has_valid_fragments schema ty q ->
                  eval schema g u q = eval_queries schema g u nqs)
             (fun schema ty qs nqs =>
                forall (g : @conformedGraph Name Vals schema) u,
                  all (query_conforms schema ty) qs ->
                  all (has_valid_fragments schema ty) qs ->
                  eval_queries schema g u qs = eval_queries schema g u nqs)) => schema //.

    - move=> ty f α Hscope g u Hqc Hv.
      simp try_inline_query.
      case: eqP => //= Hpty.
      by apply: inlined_query_eq_eval.

    - move=> ty l f α Hscope g u Hqc Hv.
      simp try_inline_query.
      case: eqP => //= Hpty.
        by apply: inlined_query_eq_eval.

    all: do ?[by intros; rewrite /query_conforms Heq in H].

    - move=> ty f fld α φ IH Hscope Hlook g u Hqc Hv /=.
      simp eval => /=.
      move: Hqc; rewrite /query_conforms Hlook => /and4P [_ _ _ Hqsc].
      move: Hv; simp has_valid_fragments; rewrite Hlook => Hv.
      case: lookup_field_type => [rty|] //=.
      case: rty => [nty | lty].
      case: ohead => [v |] //=.
        by rewrite IH.
      congr cons.
      congr (NestedListResult f).  
      apply: map_normalize_eval_eq => v.
        by apply: (IH g v).

    - move=> ty f fld α φ IH Hscope Hlook g u Hqc Hv /=.
      simp try_inline_query.
      case: eqP => //= Hpty.
      simp eval => /=.
      move: Hqc; rewrite /query_conforms Hlook => /and4P [_ _ _ Hqsc].
      move: Hv; simp has_valid_fragments; rewrite Hlook => Hv.
      case: lookup_field_type => [rty|] //=.
      case: rty => [nty | lty].
      case: ohead => [v |] //=.
        by rewrite IH.
      congr cons.
      congr (NestedListResult f).  
      apply: map_normalize_eval_eq => v.
        by apply: (IH g v).

        admit.
        Admitted.
        

  
  Lemma normalize_preserves_valid_fragments :
    forall schema ty q,
      has_valid_fragments schema ty q ->
      all (has_valid_fragments schema ty) (normalize schema ty q).
  Admitted.

   Lemma normalize__φ_preserves_valid_fragments :
    forall schema ty qs,
      all (has_valid_fragments schema ty) qs ->
      all (has_valid_fragments schema ty) (normalize__φ schema ty qs).
  Admitted.
  
  Lemma remove_redundancies_eval_eq schema (g : @conformedGraph Name Vals schema) u φ φs :
    eval schema g u φ = eval_queries schema g u φs ->
    eval schema g u φ = eval_queries schema g u (remove_redundancies φs).
  Proof.
    apply_funelim (remove_redundancies φs) => //.

    intros => /=.
    case: γ__φ.
    Admitted.
  
  Theorem all_q_has_nrgtnf_q schema (g : @conformedGraph Name Vals schema):
    forall (φ : @Query Name Vals) ty,
      query_conforms schema ty φ ->
      has_valid_fragments schema ty φ ->

      exists (φ' : seq Query),
        [/\
         all (query_conforms schema ty) φ',
         all (has_valid_fragments schema ty) φ',
         are_in_normal_form schema φ',
         are_non_redundant φ' &
         forall u, eval schema g u φ = eval_queries schema g u φ'].
  Proof.
    case=> [f α | l f α | f α φ | l f α φ | t φ] ty Hqc Hv;
    [ exists [:: SingleField f α]
    | exists [:: LabeledField l f α]
    | exists (remove_redundancies (normalize schema ty (NestedField f α φ)))
    | exists (remove_redundancies (normalize schema ty (NestedLabeledField l f α φ)))
    | exists (remove_redundancies (normalize schema ty (InlineFragment t φ)))]; split=> //.

    all: do ?[by rewrite all_seq1].
    all: do ?[by apply: remove_redundancies_preserves_conformance; apply: normalize_preserves_conformance].
    all: do ?[by apply: remove_redundancies_preserves_valid_fragments; apply: normalize_preserves_valid_fragments].
    all: do ?[by apply: remove_redundancies_normalize_preserves_normal_form].
    all: do ?[by apply: remove_redundancies_is_non_redundant].
    all: do ?[by move=> u; apply: remove_redundancies_eval_eq; apply: normalize_preserves_eval].
  Qed.
      
       
End Eq.