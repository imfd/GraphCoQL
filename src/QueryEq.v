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


  Lemma implementation_nil_for_union schema ty :
    is_union_type schema ty ->
    implementation schema ty = fset0.
  Admitted.

  Lemma collect_nested_cat (s1 s2 : seq (@ResponseObject Name Vals)) :
    collect (collect s1 ++ collect s2) = collect (s1 ++ s2).
  Admitted.
  
  Lemma eval_collect_cat schema graph u qs1 qs2 :
    collect (eval_queries schema graph u qs1 ++ eval_queries schema graph u qs2) =
    eval_queries schema graph u (qs1 ++ qs2).
  Proof.
    rewrite [RHS]eval_queries_collect_same.
    congr collect.
  Abort.
    
  Lemma normalize_preserves_eval :
    forall schema ty φ (g : @conformedGraph Name Vals schema) u,
      u \in g.(nodes) ->
      u.(type) \in get_possible_types schema ty ->
      query_conforms schema ty φ ->
      has_valid_fragments schema ty φ ->
      eval schema g u φ =  eval_queries schema g u (normalize schema ty φ).
  Proof.
    apply (normalize_elim
             (fun schema ty q nqs =>
                forall (g : @conformedGraph Name Vals schema) u,
                  u \in g.(nodes) ->
                  u.(type) \in get_possible_types schema ty ->
                  query_conforms schema ty q ->
                  has_valid_fragments schema ty q ->
                  eval schema g u q = eval_queries schema g u nqs)
             (fun schema ty qs nqs =>
                forall (g : @conformedGraph Name Vals schema) u,
                  u \in g.(nodes) ->
                  u.(type) \in get_possible_types schema ty ->
                  queries_conform schema ty qs ->
                  all (has_valid_fragments schema ty) qs ->
                  eval_queries schema g u qs = eval_queries schema g u nqs)) => schema //.
    

    all: do ?[by intros; apply: eval_same_query_in_list].
    all: do ?[by intros; simp query_conforms in H1; rewrite Heq /= in H1].
     
    - move=> ty f α Hscope g u Hin Hupty Gqc Hv.
      simp try_inline_query.
      case: eqP => //= Hpty.
      * by rewrite cats0; apply: eval_collect_same.
      * by apply: inlined_query_eq_eval.
        
     
    - move=> ty l f α Hscope g u _ _ Hqc Hv.
      simp try_inline_query.
      case: eqP => //= Hpty.
      * by rewrite cats0; apply: eval_collect_same.
      * by apply: inlined_query_eq_eval.

    
    - admit.
    - admit.
    - admit.
    - admit.
       
    - move=> t b ty φ IH Ht Hscope g u Hin.
      rewrite get_possible_types_objectE //= inE => Huty /and5P [_ _ _ Hqsc Hmerge].
      simp has_valid_fragments; rewrite Hscope /= => /andP [/eqP Hteq Hv].
      rewrite -Hteq in Huty.
      simp eval; rewrite Huty /=.
      apply: IH => //=.
        by rewrite get_possible_types_objectE //= inE -Hteq.
      by rewrite /queries_conform Hteq in Hqsc Hmerge *; apply/andP; split.
          
    - move=> t ty φ IH Ht Hscope g u Hin Hpty Hqc Hv.
      move: Hqc => /= /and5P [_ _ _ Hqsc Hmerge].
      move: Hv; simp has_valid_fragments; rewrite Hscope /= => /andP [_] Hv.  
 
      simp eval; case: eqP => Heq //=.
      * rewrite cats0.
        rewrite -IH //.
          by apply: eval_queries_collect_same.
          by rewrite get_possible_types_objectE //= inE Heq.
          by rewrite /queries_conform; apply/andP; split.
          by rewrite implementation_nil_for_object //= union_nil_for_object.
            
    - move=> t ty φ IH Ht Hscope g u Hin Hpty Hqc Hv; simp eval.
      case: eqP => //= Heq.
      * move: (node_in_graph_has_object_type Hin) => Huty.
        by rewrite Heq Ht in Huty.

      * move: (type_in_scope_N_obj_is_abstract _ _ _ _ _  Hqc Hscope).
        move: Hv; simp has_valid_fragments; rewrite Hscope /= => {Heq} /andP [/orP [/eqP Heq | Hcontr] Hv]; last first.
          by rewrite Hcontr in Ht.
        rewrite /is_abstract_type => /orP [Hintf | Hunion].
        rewrite get_possible_types_interfaceE // in Hpty IH.
        rewrite -Heq in Hpty IH *.
        rewrite Hpty /=.
        apply: IH => //.
          by move: Hqc; simp query_conforms => /and5P [_ _ _ Hqsc Hmerge]; rewrite /queries_conform; apply/andP; split.

        rewrite get_possible_types_unionE // in Hpty IH.
        rewrite -Heq in Hpty IH Hunion *.

        rewrite implementation_nil_for_union //= Hpty /=.
        apply: IH => //.
          by move: Hqc; simp query_conforms => /and5P [_ _ _ Hqsc Hmerge]; rewrite /queries_conform; apply/andP; split.

    - move=> ty hd tl IHhd IHtl g u Hin Hpty.
      rewrite /queries_conform. case/andP.
      all_cons => [Hqc Hqsc] /=.
      all_cons => [Hmerge Hmerges].
      all_cons => [Hv Hvs].
      rewrite IHhd // IHtl //; last first.
        by rewrite /queries_conform; apply/andP; split.
        by apply: collect_eval_cat.
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

   Lemma remove_redundancies_eval_eq schema (g : @conformedGraph Name Vals schema) φ :
     forall ty u,
       u \in g.(nodes) ->
       u.(type) \in get_possible_types schema ty ->
       all (query_conforms schema ty) φ ->
       all (has_valid_fragments schema ty) φ ->
       eval_queries schema g u φ = eval_queries schema g u (remove_redundancies φ).
   Proof.
     funelim (remove_redundancies φ) => // ty u Hin Hpty;
     all_cons => [Hqc Hqsc];
     all_cons => [Hv Hvs] /=.

     all: do ?[rewrite -(H schema g ty u) // -?eval_queries_equation_2].
     all: do ?[by apply: filter_preserves_pred].
     admit.
     admit.


     rewrite -(H0 schema g ty u) //.
     simp eval => /=.
     case Hlook : lookup_field_type => [rty |] //.
     case: rty Hlook => rty Hlook.
     case ohead => [v |] //=.
     rewrite -(H schema g rty v) //=.
     simp collect.
     congr cons. congr NestedResult.
     
     rewrite eval_collect_cat.
     rewrite (collect_collect_2_cat Name Vals (responses_size (eval_queries schema g v l0 ++ eval_queries schema g v (β__φ s2 l)))) //.
     rewrite -catA.
     rewrite (β_filter_nil Name Vals s2 (eval_queries schema g u (γ__φ _ _))).
     rewrite cats0.
     admit.
     admit.
     exact: Name. (* ?? *)
     rewrite (γ_filter_same_with_no_eq Name Vals (NestedResult s2 _) (eval_queries schema g u (γ__φ _ _))).
     γ_filter_same_eq

     Lemma remove_redundancies__φ_eval_eq schema (g : @conformedGraph Name Vals schema) φ :
     forall ty u,
       u \in g.(nodes) ->
       u.(type) \in get_possible_types schema ty ->
       query_conforms schema ty φ ->
       has_valid_fragments schema ty φ ->
       eval schema g u φ = eval schema g u (remove_redundancies__φ φ).
   Proof.
     elim φ using Query_ind with
         (Pl := fun qs =>
                 forall ty u,
                  u \in g.(nodes) ->
                  u.(type) \in get_possible_types schema ty ->
                  all (query_conforms schema ty) qs ->
                  all (has_valid_fragments schema ty) qs ->
                  eval_queries schema g u qs = eval_queries schema g u (remove_redundancies qs)) => {φ}.

     all: do ?[by intros; simp remove_redundancies__φ].

     - move=> f α φ IH ty u Hin Hpty Hqc Hv.
       simp remove_redundancies__φ.
       simp eval => /=.
       case Hlook: lookup_field_type => [rty |] //.
       case: rty Hlook => // rty Hlook.
       case Hohead: ohead => [v|] //.
       rewrite (IH rty v) //.
       admit.
       admit.
       move: Hqc. admit. 
       move: Hv; simp has_valid_fragments. admit.
       congr cons; congr NestedListResult.
       admit.
       
     - move=> l f α φ IH ty u Hin Hpty Hqc Hv.
       simp remove_redundancies__φ.
       simp eval => /=.
       case Hlook: lookup_field_type => [rty |] //.
       case: rty Hlook => // rty Hlook.
       case Hohead: ohead => [v|] //.
       rewrite (IH rty v) //.
       admit.
       admit.
       move: Hqc. admit. 
       move: Hv; simp has_valid_fragments. admit.
       congr cons; congr NestedListResult. admit.

     - move=> t φ IH ty u Hin Hpty Hqc Hv.
       simp remove_redundancies__φ.
       simp eval.
       move: (node_in_graph_has_object_type Hin) => Huty.
       case: eqP => Heq /=.
       rewrite Heq in Huty.
       apply: (IH t) => //.
       by rewrite Heq get_possible_types_objectE //= inE.
       by move: Hqc; rewrite /query_conforms => /and4P [_ _ _ Hqsc].
       move: Hv; simp has_valid_fragments; case is_object_type => //= /andP.
         by move=> [/eqP -> Hv].
         by case.

       case Himpl: in_mem => //=.
       admit.
       case Hunion: in_mem => //=.
       admit.

     - move=> hd IHhd tl IHtl ty u Hin Hpty.
       all_cons=> [Hqc Hqsc].
       all_cons=> [Hv Hvs] /=.
       case: hd IHhd Hqc Hv.
       intros; simp remove_redundancies => /=.
       admit.
       intros; simp remove_redundancies => /=.
       admit.
       intros; simp remove_redundancies => /=.
       simp eval => /=.
       case Hlook: lookup_field_type => [rty|] //=.
       case: rty Hlook => rty Hlook.
       case ohead => [v |] //=.
       
  Lemma remove_redundancies_eval_eq schema (g : @conformedGraph Name Vals schema) u φs :
    eval_queries schema g u φs = eval_queries schema g u (remove_redundancies φs).
  Proof.
    apply_funelim (remove_redundancies φs) => //.
    - move=> f α tl IH /=.

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
         forall u, u \in g.(nodes) ->
              u.(type) \in get_possible_types schema ty ->
                    eval schema g u φ = eval_queries schema g u φ'].
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
    all: do ?[by move=> u Hin Hty; rewrite -remove_redundancies_eval_eq; apply: normalize_preserves_eval].
  Qed.
      

   Theorem bleble schema (g : @conformedGraph Name Vals schema) :
    forall (φ : @Query Name Vals),
      query_conforms schema schema.(query_type) φ ->
      has_valid_fragments schema schema.(query_type) φ ->

      exists (φ' : seq Query),
        [/\
         all (query_conforms schema schema.(query_type)) φ',
         all (has_valid_fragments schema schema.(query_type)) φ',
         are_in_normal_form schema φ',
         are_non_redundant φ' &
         eval schema g g.(root) φ = eval_queries schema g g.(root) φ'].
  Proof.
    case=> [f α | l f α | f α φ | l f α φ | t φ] Hqc Hv;
    [ exists [:: SingleField f α]
    | exists [:: LabeledField l f α]
    | exists (remove_redundancies (normalize schema schema.(query_type) (NestedField f α φ)))
    | exists (remove_redundancies (normalize schema schema.(query_type) (NestedLabeledField l f α φ)))
    | exists (remove_redundancies (normalize schema schema.(query_type) (InlineFragment t φ)))]; split=> //.

    all: do ?[by rewrite all_seq1].
    all: do ?[by apply: remove_redundancies_preserves_conformance; apply: normalize_preserves_conformance].
    all: do ?[by apply: remove_redundancies_preserves_valid_fragments; apply: normalize_preserves_valid_fragments].
    all: do ?[by apply: remove_redundancies_normalize_preserves_normal_form].
    all: do ?[by apply: remove_redundancies_is_non_redundant].

    rewrite -remove_redundancies_eval_eq.
    apply: normalize_preserves_eval => //.
    apply: root_in_nodes.
    rewrite get_possible_types_objectE //=.
    rewrite mem_seq1.
    apply/eqP. apply: root_query_type.
    apply: query_has_object_type.

    rewrite -remove_redundancies_eval_eq.
    apply: normalize_preserves_eval => //.
    apply: root_in_nodes.
    rewrite get_possible_types_objectE //=.
    rewrite mem_seq1.
    apply/eqP. apply: root_query_type.
    apply: query_has_object_type.

    rewrite -remove_redundancies_eval_eq.
    apply: normalize_preserves_eval => //.
    apply: root_in_nodes.
    rewrite get_possible_types_objectE //=.
    rewrite mem_seq1.
    apply/eqP. apply: root_query_type.
    apply: query_has_object_type.
  Qed.
  
End Eq.