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


  Lemma wf_responses_catE rs1 rs2 :
    wf_responses (rs1 ++ rs2) = [&& wf_responses rs1,
                                 wf_responses rs2 &
                                 all (fun r1 => all (fun r2 => @have_compatible_shapes Name Vals r1 r2) rs2) rs1].
  Proof.
    elim: rs1 rs2 => //= [| hd tl IH] rs2.
    - by rewrite andbT.
    - rewrite all_cat.
      rewrite IH.
      set A := wf_response hd.
      set B := all _ tl.
      set C := all _ rs2.
      set D := wf_responses tl.
      set E := wf_responses rs2.
      set F := all _ _.
      rewrite -[(B && C) && _]andbA.
      rewrite -[RHS]andbA.
      rewrite -[(B && D) && _]andbA.
      rewrite [E && (C && _)]andbCA.
      by rewrite [D && (C && _)]andbCA.
  Qed.

  
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

    - move=> ty f fld α φ IH Hscope Hlook g u Hin Hpty Hqc Hv /=.
      rewrite cats0.
      simp eval => /=.
      case Hlookty : lookup_field_type => [rty|]; last by simp collect.
      case: rty Hlookty => //= rty Hlookty.
      * case Hohead: ohead => [v|]; simp collect => //.
        simp β_filter; rewrite cats0 IH //.
        by rewrite -eval_queries_collect_same.
        admit.
        admit.
        by simp query_conforms in Hqc; rewrite Hlook /= in Hqc; case/and4P: Hqc.
          by simp has_valid_fragments in Hv; rewrite Hlook /= in Hv.
      * simp collect. (* indexed map can be removed && can use map_normalize lemma from above *)
        rewrite indexed_map_β_nil.
        rewrite indexed_map_eq_map.
        rewrite (map_normalize_eval_eq _ ty _ g _).
        rewrite -map_comp.
        rewrite /funcomp.
        (* rewrite eval_queries_collect_same. *)
        admit.
        admit.
        
    - move=> ty f fld α φ IH Hscope Hlook g u Hin Hupty Hqc Hv /=.
      simp try_inline_query.
      case: eqP => //= Hpty.
      * rewrite cats0.
        simp eval => /=.
        case Hlookty : lookup_field_type => [rty|]; last by simp collect.
        case: rty Hlookty => //= rty Hlookty.
        + case Hohead: ohead => [v|]; simp collect => //.
          simp β_filter; rewrite cats0 IH //.
            by rewrite -eval_queries_collect_same.
            admit.
            admit.
            by simp query_conforms in Hqc; rewrite Hlook /= in Hqc; case/and4P: Hqc.
          by simp has_valid_fragments in Hv; rewrite Hlook /= in Hv.
        + simp collect. (* indexed map can be removed *)
          admit.

       * admit.

    - move=> ty f fld l α φ IH Hscope Hlook g u Hin Hpty Hqc Hv /=.
      rewrite cats0.
      simp eval => /=.
      case Hlookty : lookup_field_type => [rty|]; last by simp collect.
      case: rty Hlookty => //= rty Hlookty.
      * case Hohead: ohead => [v|]; simp collect => //.
        simp β_filter; rewrite cats0 IH //.
        by rewrite -eval_queries_collect_same.
        admit.
        admit.
        by simp query_conforms in Hqc; rewrite Hlook /= in Hqc; case/and4P: Hqc.
          by simp has_valid_fragments in Hv; rewrite Hlook /= in Hv.
      * simp collect. (* indexed map can be removed *)
        admit.

    - move=> ty f fld l α φ IH Hscope Hlook g u Hin Hupty Hqc Hv /=.
      simp try_inline_query.
      case: eqP => //= Hpty.
      * rewrite cats0.
        simp eval => /=.
        case Hlookty : lookup_field_type => [rty|]; last by simp collect.
        case: rty Hlookty => //= rty Hlookty.
        + case Hohead: ohead => [v|]; simp collect => //.
          simp β_filter; rewrite cats0 IH //.
            by rewrite -eval_queries_collect_same.
            admit.
            admit.
            by simp query_conforms in Hqc; rewrite Hlook /= in Hqc; case/and4P: Hqc.
          by simp has_valid_fragments in Hv; rewrite Hlook /= in Hv.
        + simp collect. (* indexed map can be removed *)
          admit.

       * admit.

         
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
        rewrite eval_collect_cat //.
        rewrite wf_responses_catE.
        apply/and3P; split; do ? by apply: eval_queries_response_are_wf.
        rewrite -IHhd // -IHtl //; last by rewrite /queries_conform; apply/andP; split.
        apply/allP => r Hevin.
        apply/allP => r2 Hevin2.
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
       queries_conform schema ty φ ->
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


     rewrite -(H0 schema g ty u) //; do ?[by apply: filter_preserves_pred].
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
   Admitted.



   forall schema graph φ ty,
     
     query_conforms schema ty φ ->
     has_valid_fragments schema ty φ ->

     exists φ',
       multi Rewrite φ φ' /\
       all (query_conforms schema ty) φ' /\
       all (has_valid_fragments schema ty) φ' /\
       are_in_normal_form schema φ' /\
       are_non_redundant φ' /\
         forall u, u \in g.(nodes) ->
              u.(type) \in get_possible_types schema ty ->
                           eval schema g u φ = eval_queries schema g u φ'].
     
  
       
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
    all: do ?[by intros => /=; rewrite cats0; apply: eval_collect_same].
    intros.
    rewrite -(remove_redundancies_eval_eq _ _ _ ty u) //.
    apply: normalize_preserves_eval => //.
    by apply: normalize_preserves_conformance.
    by apply: normalize_preserves_valid_fragments.

    intros.
    rewrite -(remove_redundancies_eval_eq _ _ _ ty u) //.
    apply: normalize_preserves_eval => //.
    by apply: normalize_preserves_conformance.
    by apply: normalize_preserves_valid_fragments.

    intros.
    rewrite -(remove_redundancies_eval_eq _ _ _ ty u) //.
    apply: normalize_preserves_eval => //.
    by apply: normalize_preserves_conformance.
      by apply: normalize_preserves_valid_fragments.
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
    all: do ?[by intros => /=; rewrite cats0; apply: eval_collect_same].
    
    intros.
    move: (root_in_nodes g) => Hin.
    have Hpty :  type (root g) \in get_possible_types schema (query_type schema).
    rewrite get_possible_types_objectE //=.
    rewrite mem_seq1.
      by apply/eqP; apply: root_query_type.
      by apply: query_has_object_type.
    rewrite -(remove_redundancies_eval_eq _ _ _ schema.(query_type)) //.
    apply: normalize_preserves_eval => //.
    
    by apply: normalize_preserves_conformance.
    by apply: normalize_preserves_valid_fragments.

    intros.
    move: (root_in_nodes g) => Hin.
    have Hpty :  type (root g) \in get_possible_types schema (query_type schema).
    rewrite get_possible_types_objectE //=.
    rewrite mem_seq1.
      by apply/eqP; apply: root_query_type.
      by apply: query_has_object_type.
    rewrite -(remove_redundancies_eval_eq _ _ _ schema.(query_type)) //.
    apply: normalize_preserves_eval => //.
    
    by apply: normalize_preserves_conformance.
    by apply: normalize_preserves_valid_fragments.

    intros.
    move: (root_in_nodes g) => Hin.
    have Hpty :  type (root g) \in get_possible_types schema (query_type schema).
    rewrite get_possible_types_objectE //=.
    rewrite mem_seq1.
      by apply/eqP; apply: root_query_type.
      by apply: query_has_object_type.
    rewrite -(remove_redundancies_eval_eq _ _ _ schema.(query_type)) //.
    apply: normalize_preserves_eval => //.
    
    by apply: normalize_preserves_conformance.
    by apply: normalize_preserves_valid_fragments.
  Qed.
  
End Eq.