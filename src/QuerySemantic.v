Require Import List.

From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From extructures Require Import ord fmap fset.
From Equations Require Import Equations.


Require Import SchemaWellFormedness.
Require Import GraphConformance.
Require Import QueryConformance.
Require Import SchemaAux.
Require Import GraphAux.
Require Import QueryAux.

Require Import Schema.
Require Import Query.
Require Import Response.

Require Import Graph.

Require Import Ssromega.

Require Import SeqExtra.

Require Import ValidFragments.
Require Import QueryRewrite.

Require Import NRGTNF.


Section QuerySemantic.

  Variables N Name Vals : ordType.
  
  
  Ltac case_response r := case: r => [l | l v | l vs | l ρ | l ρs].
  Ltac apply_andP := apply/andP; split=> //.
  Ltac apply_and3P := apply/and3P; split=> //.
  
  Variable s : @wfSchema Name Vals.
  Variable g : @conformedGraph Name Vals s.
  
  Implicit Type u : @node Name Vals.
  Implicit Type query : @Query Name Vals.

  Transparent query_size.

  Reserved Notation "⟦ φ 'in' u ⟧ˢ" (at level 40).
  
  Equations? execute_selection_set u (queries : seq (@Query Name Vals)) :
    seq (Name * ResponseNode) by wf (queries_size queries) :=
    {
      execute_selection_set _ [::] := [::];
      
      execute_selection_set u (InlineFragment t φ :: qs)
        with does_fragment_type_apply s u.(type) t :=
        {
        | true := execute_selection_set u (φ ++ qs);
        | _ := execute_selection_set u qs
        };

      execute_selection_set u (SingleField f α :: qs)
        with u.(fields) (Field f α) :=
        {
        | Some (inl value) => (f, Leaf (SingleValue value)) :: execute_selection_set u (filter_queries_with_label f qs);
        | Some (inr values) => (f, Array (map (Leaf \o SingleValue) values)) :: execute_selection_set u (filter_queries_with_label f qs);
        | None => (f, Leaf Null) :: execute_selection_set u (filter_queries_with_label f qs)
        };
      
      execute_selection_set u (LabeledField l f α :: qs)
        with u.(fields) (Field f α) :=
        {
        | Some (inl value) => (l, Leaf (SingleValue value)) :: execute_selection_set u (filter_queries_with_label l qs);
        | Some (inr values) => (l, Array (map (Leaf \o SingleValue) values)) :: execute_selection_set u (filter_queries_with_label l qs);
        | None => (l, Leaf Null) :: execute_selection_set u (filter_queries_with_label l qs)
        };

      
      execute_selection_set u (NestedField f α φ :: qs)
        with lookup_field_in_type s u.(type) f :=
        {
        | Some (Schema.Field _ _ (ListType ty)) => (f, Array [seq Object (execute_selection_set v (φ ++ merge_selection_sets (find_queries_with_label s v.(type) f qs))) | v <- neighbours_with_field g u (Field f α)]) :: execute_selection_set u (filter_queries_with_label f qs);
        
        | Some (Schema.Field _ _ (NT ty))
            with ohead (neighbours_with_field g u (Field f α)) :=
            {
            | Some v => (f, Object (execute_selection_set v (φ ++ merge_selection_sets (find_queries_with_label s v.(type) f qs)))) :: execute_selection_set u (filter_queries_with_label f qs);
            
            | _ =>  (f, Leaf Null) :: execute_selection_set u (filter_queries_with_label f qs)
            };

        | None => (f, Leaf Null) :: execute_selection_set u (filter_queries_with_label f qs)
        };

       execute_selection_set u (NestedLabeledField l f α φ :: qs)
        with lookup_field_in_type s u.(type) f :=
        {
        | Some (Schema.Field _ _ (ListType ty)) => (l, Array [seq Object (execute_selection_set v (φ ++ merge_selection_sets (find_queries_with_label s v.(type) l qs))) | v <- neighbours_with_field g u (Field f α)]) :: execute_selection_set u (filter_queries_with_label l qs);
        
        | Some (Schema.Field _ _ (NT ty))
            with ohead (neighbours_with_field g u (Field f α)) :=
            {
            | Some v => (l, Object (execute_selection_set v (φ ++ merge_selection_sets (find_queries_with_label s v.(type) l qs)))) :: execute_selection_set u (filter_queries_with_label l qs);
            
            | _ =>  (l, Leaf Null) :: execute_selection_set u (filter_queries_with_label l qs)
            };

        | None => (l, Leaf Null) :: execute_selection_set u (filter_queries_with_label l qs)
        }

    }
  where "⟦ queries 'in' u ⟧ˢ" := (execute_selection_set u queries).
  
  all: do ?[by have Hleq := (filter_queries_with_label_leq_size f qs); ssromega].
  all: do ?[by have Hleq := (filter_queries_with_label_leq_size l qs); ssromega].

  all: do ?[by rewrite -/(queries_size φ) queries_size_app;
            have Hleq1 := (found_queries_leq_size s v.(type) f qs);
            have Hleq2 := (merged_selections_leq (find_queries_with_label s v.(type) f qs)); ssromega].

  all: do ?[by rewrite -/(queries_size φ) queries_size_app;
            have Hleq1 := (found_queries_leq_size s v.(type) l qs);
            have Hleq2 := (merged_selections_leq (find_queries_with_label s v.(type) l qs)); ssromega].


  all: do ? [by rewrite -/(queries_size φ) ?queries_size_app; ssromega].
  Qed.

  Equations has_response_name : Name -> @Query Name Vals -> bool :=
    {
      has_response_name l (InlineFragment _ φ) := has (has_response_name l) φ;

      has_response_name l q := (qresponse_name q _) == l
    }.

  Lemma filtered_queries_hasN_response_name l qs :
    all (fun q => ~~has_response_name l q) (filter_queries_with_label l qs).
  Proof.
    funelim (filter_queries_with_label l qs) => //=; simp has_response_name => /=; do ? apply_andP.
    by apply/hasPn/allP.
  Qed.

  Lemma filter_queries_preserves_non_existent l qs l' :
    all (fun q => ~~has_response_name l q) qs ->
    all (fun q => ~~has_response_name l q) (filter_queries_with_label l' qs).
  Proof.
    funelim (filter_queries_with_label l' qs) => //= /andP [Hp Hall]; simp has_response_name; apply_andP.
    - apply/hasPn/allP. apply: H. simp has_response_name in Hp. move/hasPn/allP in Hp. done.
    all: do ? by apply: H0.
    all: do ? by apply: H.
  Qed.
  
  Transparent qresponse_name.
  
  Lemma exec_preserves_non_existent_label u qs l :
    all (fun q => ~~has_response_name l q) qs ->
    all (fun kq => kq.1 != l) (⟦ qs in u ⟧ˢ).
  Proof.
    funelim (execute_selection_set u qs) => //=; simp has_response_name => /= /andP [Hne Hall]; do ? apply_andP.

    all: do ?[by apply: H; apply: filter_queries_preserves_non_existent].
    all: do ?[by apply: H0; apply: filter_queries_preserves_non_existent].

    by apply: H; rewrite all_cat; apply_andP; apply/allP/hasPn.
    by apply: H.
  Qed.

  
  Lemma exec_responses_are_non_redundant u qs :
    Response.are_non_redundant (execute_selection_set u qs).
  Proof.
    apply_funelim (execute_selection_set u qs) => //=; clear u qs => u.
    - move=> f α v qs IH Hv; simp is_non_redundant; rewrite andTb; apply_andP.
      apply: exec_preserves_non_existent_label.
      apply: filtered_queries_hasN_response_name.
    - move=> f α vs qs IH Hv; simp is_non_redundant; apply_and3P.
      * by rewrite all_map; apply/allP.
      * apply: exec_preserves_non_existent_label.
        apply: filtered_queries_hasN_response_name.

    - move=> f α qs IH Hnull; simp is_non_redundant; rewrite andTb; apply_andP.
      apply: exec_preserves_non_existent_label.
      apply: filtered_queries_hasN_response_name.
      
    - move=> l f α v qs IH Hv; simp is_non_redundant; rewrite andTb; apply_andP.
      apply: exec_preserves_non_existent_label.
      apply: filtered_queries_hasN_response_name.
    - move=> l f α vs qs IH Hv; simp is_non_redundant; apply_and3P.
      * by rewrite all_map; apply/allP.
      * apply: exec_preserves_non_existent_label.
        apply: filtered_queries_hasN_response_name.

    - move=> l f α qs IH Hnull; simp is_non_redundant; rewrite andTb; apply_andP.
      apply: exec_preserves_non_existent_label.
      apply: filtered_queries_hasN_response_name.

    - move=> f f' args ftype α φ qs IH IHqs Hlook; simp is_non_redundant. apply_and3P.
      * rewrite all_map; apply/allP => v Hin /=; simp is_non_redundant.
      * apply: exec_preserves_non_existent_label.
        apply: filtered_queries_hasN_response_name.

    - move=> f α φ qs IH Hlook; simp is_non_redundant; rewrite andTb; apply_andP.
      apply: exec_preserves_non_existent_label.
      apply: filtered_queries_hasN_response_name.

    - move=> f α f' args v ty φ qs IH IHqs Hv Hlook; simp is_non_redundant; apply_and3P.
      apply: exec_preserves_non_existent_label.
      apply: filtered_queries_hasN_response_name.

    - move=> f α f' args ty φ qs IHqs Hv Hlook; simp is_non_redundant; apply_and3P.
      apply: exec_preserves_non_existent_label.
      apply: filtered_queries_hasN_response_name.

    - move=> l f' args ftype f α φ qs IH IHqs Hlook; simp is_non_redundant; apply_and3P.
      * rewrite all_map; apply/allP => v Hin /=; simp is_non_redundant.
      * apply: exec_preserves_non_existent_label.
        apply: filtered_queries_hasN_response_name.

    - move=> l f α φ qs IH Hlook; simp is_non_redundant; rewrite andTb; apply_andP.
      apply: exec_preserves_non_existent_label.
      apply: filtered_queries_hasN_response_name.

    - move=> f α v f' args ty l φ qs IH IHqs Hv Hlook; simp is_non_redundant; apply_and3P.
      apply: exec_preserves_non_existent_label.
      apply: filtered_queries_hasN_response_name.

    - move=> f α f' args ty l φ qs IHqs Hv Hlook; simp is_non_redundant; apply_and3P.
      apply: exec_preserves_non_existent_label.
      apply: filtered_queries_hasN_response_name.
  Qed.

  Reserved Notation "⦃ queries 'in' u ⦄" (at level 50).
  
   Equations? execute_selection_set2 u (queries : seq (@Query Name Vals)) :
    seq (Name * ResponseNode) by wf (queries_size queries) :=
    {
      execute_selection_set2 _ [::] := [::];

      execute_selection_set2 u (SingleField f α :: qs)
        with u.(fields) (Field f α) :=
        {
        | Some (inl value) => (f, Leaf (SingleValue value)) :: ⦃ qs in u ⦄;
        | Some (inr values) => (f, Array (map (Leaf \o SingleValue) values)) :: ⦃ qs in u ⦄;
        | None => (f, Leaf Null) :: ⦃ qs in u ⦄
        };
      
      execute_selection_set2 u (LabeledField l f α :: qs)
        with u.(fields) (Field f α) :=
        {
        | Some (inl value) => (l, Leaf (SingleValue value)) :: ⦃ qs in u ⦄;
        | Some (inr values) => (l, Array (map (Leaf \o SingleValue) values)) :: ⦃ qs in u ⦄;
        | None => (l, Leaf Null) :: ⦃ qs in u ⦄
        };

      
      execute_selection_set2 u (NestedField f α φ :: qs)
        with lookup_field_in_type s u.(type) f :=
        {
        | Some (Schema.Field _ _ (ListType ty)) => (f, Array [seq Object (⦃ φ in v ⦄) | v <- neighbours_with_field g u (Field f α)]) :: ⦃ qs in u ⦄;
        
        | Some (Schema.Field _ _ (NT ty))
            with ohead (neighbours_with_field g u (Field f α)) :=
            {
            | Some v => (f, Object (⦃ φ in v ⦄)) :: ⦃ qs in u ⦄;
            
            | _ =>  (f, Leaf Null) :: ⦃ qs in u ⦄
            };

        | None => (f, Leaf Null) :: ⦃ qs in u ⦄
        };

       execute_selection_set2 u (NestedLabeledField l f α φ :: qs)
        with lookup_field_in_type s u.(type) f :=
        {
        | Some (Schema.Field _ _ (ListType ty)) => (l, Array [seq Object (⦃ φ in v ⦄) | v <- neighbours_with_field g u (Field f α)]) :: ⦃ qs in u ⦄;
        
        | Some (Schema.Field _ _ (NT ty))
            with ohead (neighbours_with_field g u (Field f α)) :=
            {
            | Some v => (l, Object (⦃ φ in v ⦄)) :: ⦃ qs in u ⦄;
            
            | _ =>  (l, Leaf Null) :: ⦃ qs in u ⦄
            };

        | None => (l, Leaf Null) :: ⦃ qs in u ⦄
        };

       
        execute_selection_set2 u (InlineFragment t φ :: qs)
        with does_fragment_type_apply s u.(type) t :=
        {
        | true := ⦃ φ ++ qs in u ⦄;
        | _ := ⦃ qs in u ⦄
        }

    }
   where "⦃ queries 'in' u ⦄" := (execute_selection_set2 u queries).
   all: do ? by ssromega.
   all: do [by rewrite ?queries_size_app -/(queries_size φ); ssromega].
  Qed.

 
  Lemma filter_queries_with_label_cat l (qs1 qs2 : seq (@Query Name Vals)) :
    filter_queries_with_label l (qs1 ++ qs2) = filter_queries_with_label l qs1 ++ filter_queries_with_label l qs2.
  Proof.
    elim: qs1  => //= hd tl IH.
    case: hd => //=; intros; simp filter_queries_with_label; do ?[by case: eqP => //= Heq; rewrite IH].
      by rewrite IH.
  Qed.
    
  Lemma normalize_filter_swap label ty qs :
    is_object_type s ty ->
    filter_queries_with_label label (normalize__φ s ty qs) = normalize__φ s ty (filter_queries_with_label label qs).
  Proof.
    move=> Hscope.
    move: {2}(queries_size _) (leqnn (queries_size qs)) => n.
    elim: n qs => //= [| n IH].
    - admit.
    - case=> //; case=> [f α | l f α | f α φ | l f α φ | t φ] qs /= Hleq;
                            simp normalize; rewrite ?Hscope /=; simp filter_queries_with_label => /=.

    all: do ?[by case: eqP => //= Heq; simp normalize; rewrite Hscope /= IH].

    * case Hlook : lookup_field_in_type => [fld|] //=; rewrite ?Hscope /=; simp filter_queries_with_label => /=.
      case: eqP => //= Heq; simp normalize.
      + rewrite IH //; ssromega. 
      + rewrite Hlook /= Hscope /= IH //; ssromega.
      + case: eqP => //= Heq; simp normalize; rewrite ?Hlook /= IH //; ssromega.

    * case Hlook : lookup_field_in_type => [fld|] //=; rewrite ?Hscope /=; simp filter_queries_with_label => /=.
      case: eqP => //= Heq; simp normalize.
      + rewrite IH //; ssromega. 
      + rewrite Hlook /= Hscope /= IH //; ssromega.
      + case: eqP => //= Heq; simp normalize; rewrite ?Hlook /= IH //; ssromega.


    * simp normalize; rewrite Hscope /= filter_queries_with_label_cat.
      rewrite (IH qs) //; do ? ssromega.
      rewrite (IH φ) //; rewrite -/(queries_size φ) in Hleq; ssromega.
  Admitted.     

  Lemma lookup_field_return_type ty f fld :
    lookup_field_in_type s ty f = Some fld ->
    lookup_field_type s ty f = Some (fld.(return_type)).
  Admitted.

   
  Transparent is_field is_inline_fragment qresponse_name qsubqueries.

  Lemma are_similar_fields_share_response_name (q1 q2 : @Query Name Vals) (Hfield1 : q1.(is_field)) (Hfield2 : q2.(is_field)) :
    are_similar q1 q2 -> (qresponse_name q1 Hfield1) == (qresponse_name q2 Hfield2).
  Proof.
    funelim (are_similar q1 q2) => //=.
  Qed.

   Lemma are_N_similar_fields_N_response_name (q1 q2 : @Query Name Vals) (Hfield1 : q1.(is_field)) (Hfield2 : q2.(is_field)) :
     ~~are_similar q1 q2 -> (qresponse_name q1 Hfield1) != (qresponse_name q2 Hfield2).
  Proof.
    funelim (are_similar q1 q2) => //=.
  Qed.
  
  Lemma filter_not_similar_preserves_list (q : @Query Name Vals) qs (Hfield : q.(is_field)) :
    all (fun q' => ~~are_similar q' q) qs ->
    all (fun q' => q'.(is_field)) qs ->
    filter_queries_with_label (qresponse_name q Hfield) qs = qs.
  Proof.
    funelim (filter_queries_with_label _ qs) => //= /andP [Hsim Hall] Hfields; do ? by rewrite H.

    all: do ?[have := (are_N_similar_fields_N_response_name _ q _ Hfield Hsim) => /=-/(_ is_true_true) Hcontr;
                by rewrite Hcontr in Heq].
  Qed.

  Lemma find_not_similar_is_nil ty (q : @Query Name Vals) qs (Hfield : q.(is_field)) :
    all (fun q' => ~~are_similar q' q) qs ->
    all (fun q' => q'.(is_field)) qs ->
    find_queries_with_label s ty (qresponse_name q Hfield) qs = [::].
  Proof.
  Admitted.

  Lemma asdf qs : all (fun q => q.(is_field)) qs ->
                  all (is_in_normal_form s) qs ->
                  are_in_normal_form s qs.
  Admitted.
  
  Theorem execs_on_nrgtnf_are_equivalent u φ :
    are_in_normal_form s φ ->
    are_non_redundant φ ->
    ⦃ φ in u ⦄ = ⟦ φ in u ⟧ˢ.
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n φ u => [| n IH] φ u.
    - admit.
    - case: φ => //=; case=> /= [f α | l f α | f α φ | l f α φ | t φ] qs Hleq.
      * rewrite /are_in_normal_form /= orbF; simp is_in_normal_form; rewrite andTb => /andP [Hflds Hnf].
        simp are_non_redundant; rewrite andTb => /=-/andP [Hneq Hnr].
        simp execute_selection_set; simp execute_selection_set2.
        case: (u.(fields) _) => //=; [case=> // v|];
                                 rewrite (filter_not_similar_preserves_list (SingleField f α)) // IH //; by apply: asdf.
      
      * rewrite /are_in_normal_form /= orbF; simp is_in_normal_form; rewrite andTb => /andP [Hflds Hnf].
        simp are_non_redundant; rewrite andTb => /=-/andP [Hneq Hnr].
        simp execute_selection_set; simp execute_selection_set2.
        case: (u.(fields) _) => //=; [case=> // v|];
                                 rewrite (filter_not_similar_preserves_list (LabeledField l f α)) // IH //; by apply: asdf.

        
      * rewrite /are_in_normal_form /= orbF; simp is_in_normal_form => /and3P [Hfld /andP [Hty Hnf] Hnfs].
        simp are_non_redundant => /= /and3P [Hsim Hnr Hnrs]. 
        simp execute_selection_set; simp execute_selection_set2.
        case Hlook : lookup_field_in_type => [fld|] //=; last rewrite (filter_not_similar_preserves_list (NestedField f α φ)) //.
        case: fld Hlook => f' args; case=> ty Hlook /=. 
        + case ohead => //= [v|]; rewrite (filter_not_similar_preserves_list (NestedField f α φ)) //.
          rewrite (find_not_similar_is_nil v.(type) (NestedField f α φ)) //; simp merge_selection_sets.
          rewrite cats0 !IH //; admit.
          rewrite IH //; admit.

        + rewrite (filter_not_similar_preserves_list (NestedField f α φ)) //. 
          congr cons; [| apply: IH; admit].
          congr pair; congr Array. apply/eq_in_map => v Hin.
          rewrite (find_not_similar_is_nil v.(type) (NestedField f α φ)) //; simp merge_selection_sets.
          rewrite cats0 IH //; admit.
        + rewrite IH //; admit.

             
      * rewrite /are_in_normal_form /= orbF; simp is_in_normal_form => /and3P [Hfld /andP [Hty Hnf] Hnfs].
        simp are_non_redundant => /= /and3P [Hsim Hnr Hnrs]. 
        simp execute_selection_set; simp execute_selection_set2.
        case Hlook : lookup_field_in_type => [fld|] //=; last rewrite (filter_not_similar_preserves_list (NestedLabeledField l f α φ)) //.
        case: fld Hlook => f' args; case=> ty Hlook /=. 
        + case ohead => //= [v|]; rewrite (filter_not_similar_preserves_list (NestedLabeledField l f α φ)) //.
          rewrite (find_not_similar_is_nil v.(type) (NestedLabeledField l f α φ)) //; simp merge_selection_sets.
          rewrite cats0 !IH //; admit.
          rewrite IH //; admit.

        + rewrite (filter_not_similar_preserves_list (NestedLabeledField l f α φ)) //. 
          congr cons; [| apply: IH; admit].
          congr pair; congr Array. apply/eq_in_map => v Hin.
          rewrite (find_not_similar_is_nil v.(type) (NestedLabeledField l f α φ)) //; simp merge_selection_sets.
          rewrite cats0 IH //; admit.
        + rewrite IH //; admit.


      * rewrite /are_in_normal_form /=; simp is_in_normal_form => Hnf.
        simp are_non_redundant => /= /and3P [Hsim Hnr Hnrs].
        simp execute_selection_set; simp execute_selection_set2.
        case: does_fragment_type_apply => //=; apply: IH.
  Admitted.

        
  
  Theorem execs_are_equivalent u φ :
    all (has_valid_fragments s u.(type)) φ ->
    (⦃ (remove_redundancies s u.(type) (normalize__φ s u.(type) φ)) in u ⦄) = (⟦ φ in u ⟧ˢ).
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n φ u => /= [| n IH].
    - admit.
    - move=> φ u Hleq Hin; have Hscope := (node_in_graph_has_object_type Hin).
      case: φ Hleq => //.
      case=> [f α | l f α | f α φ | l f α φ | t φ] qs /= Hleq -/andP [Hv Hvs]; simp normalize;
              rewrite ?Hscope /=; simp remove_redundancies; simp execute_selection_set.

      * simp execute_selection_set2.
        case : (u.(fields) _) => //=.
        + case=> //= v; rewrite normalize_filter_swap // IH //;
                             do ?[by have Hleq2 := (filter_queries_with_label_leq_size f qs); ssromega].
          admit.
          admit.
        + rewrite normalize_filter_swap // IH //; [by have Hleq2 := (filter_queries_with_label_leq_size f qs); ssromega|].
          admit.
      * simp execute_selection_set2.
        case : (u.(fields) _) => //=.
        + case=> //= v; rewrite normalize_filter_swap // IH //;
                             do ?[by have Hleq2 := (filter_queries_with_label_leq_size l qs); ssromega].
          admit.
          admit.
        + rewrite normalize_filter_swap // IH //; [by have Hleq2 := (filter_queries_with_label_leq_size l qs); ssromega|].
          admit.

      * case Hlook: lookup_field_in_type => [fld|] //=.
        rewrite Hscope /=; simp remove_redundancies; simp execute_selection_set2.
        case: fld Hlook => f' args rty Hlook; rewrite Hlook /=.
        simp execute_selection_set2. rewrite Hlook /=.
        case: rty Hlook => //= ty Hlook.
        + case ohead => //= [v|].
          congr cons; last first.
          rewrite normalize_filter_swap //.
          admit.
          
          IH //. admit. admit.
          rewrite normalize_filter_swap // IH.
   

  Equations resolve_field_value u (field_name : Name) (argument_values : {fmap Name -> Vals}) : option ((Vals + seq Vals) + (@node Name Vals) + seq (@node Name Vals)) :=
    {
      resolve_field_value u f α
        with u.(fields) (Field f α) :=
        {
        | Some value := Some (inl (inl value));
        | _ with neighbours_with_field g u (Field f α) :=
            {
            | [::] := None;
            | [:: v] => Some (inl (inr v));
            | vs := Some (inr vs)
            }
        }
    }.


  Equations? execute_selection_set2 u (queries : seq (@Query Name Vals)) :
    seq (Name * ResponseNode) by wf (queries_size queries) :=
    {
      execute_selection_set2 _ [::] := [::];
      
      execute_selection_set2 u (InlineFragment t φ :: qs)
        with does_fragment_type_apply u.(type) t :=
        {
        | true := execute_selection_set u (φ ++ qs);
        | _ := execute_selection_set u qs
        };

      execute_selection_set2 u (q :: qs)
        with lookup_field_type s u.(type) (qname q _) :=
        {
        | Some (ListType ty) := ((qresponse_name q _), complete_value (resolve_field_value u (qname q _) (qargs q _)))
                         :: execute_selection_set2 u (filter_queries_with_label (qresponse_name q _) qs)

           where complete_value (result : option ((Vals + seq Vals) + (@node Name Vals) + seq (@node Name Vals))) : ResponseNode :=
                   {
                     complete_value None := Leaf Null;

                     complete_value (Some (inr vs)) := Array
                                                        [seq Object
                                                             (execute_selection_set v (q.(qsubqueries) ++ merge_selection_sets (find_queries_with_label v.(type) (qresponse_name q _) qs))) | v <- vs];

                     complete_value _ := Leaf Null
                   };

        | Some (NT ty) := ((qresponse_name q _), complete_value (resolve_field_value u (qname q _) (qargs q _)))
                         :: execute_selection_set2 u (filter_queries_with_label (qresponse_name q _) qs)

           where complete_value (result : option ((Vals + seq Vals) + (@node Name Vals) + seq (@node Name Vals))) : ResponseNode :=
                   {
                     complete_value None := Leaf Null;

                     complete_value (Some (inl (inl value)))
                       with value :=
                       {
                       | inl v := Leaf (SingleValue v);
                       | inr vs := Array (map (Leaf \o SingleValue) vs)
                       };

                     complete_value (Some (inl (inr v))) := Object (execute_selection_set v (q.(qsubqueries) ++ merge_selection_sets (find_queries_with_label v.(type) (qresponse_name q _) qs)));

                     complete_value _ := Leaf Null
                   };

        | _ := ((qresponse_name q _), Leaf Null) :: execute_selection_set2 u (filter_queries_with_label (qresponse_name q _) qs)
        }
    }.
  Proof.
    all: do ?[by have Hleq := (filter_queries_with_label_leq_size unknown3 qs); ssromega].
    all: do ?[by have Hleq := (filter_queries_with_label_leq_size unknown5 qs); ssromega].
    all: do ?[by have Hleq := (filter_queries_with_label_leq_size unknown2 qs); ssromega].
    all: do ?[by have Hleq := (filter_queries_with_label_leq_size unknown8 qs); ssromega].
    
    - by have Hleq := (filter_queries_with_label_leq_size unknown1 qs); ssromega.
    - by have Hleq := (filter_queries_with_label_leq_size unknown7 qs); ssromega.
    - by have Hleq := (filter_queries_with_label_leq_size unknown11 qs); ssromega.
  Qed.

  
  
  

        
End QuerySemantic.

Arguments β [Name Vals].
Arguments collect [Name Vals].
Arguments eval [Name Vals].
Arguments eval_queries [Name Vals].
