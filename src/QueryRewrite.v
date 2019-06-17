
From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From Equations Require Import Equations.

From extructures Require Import ord fset fmap.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaWellFormedness.
Require Import Query.
Require Import QueryAux.
Require Import QueryConformance.

Require Import Graph.
Require Import GraphAux.
Require Import GraphConformance.

Require Import NRGTNF.

Require Import ValidFragments.

Require Import Ssromega.

Require Import SeqExtra.

Section QueryRewrite.

  Variables Name Vals : ordType.
  Implicit Type schema : @wfSchema Name Vals.
  Implicit Type query : @Query Name Vals.


  Variable s : @wfSchema Name Vals.
  
  Notation is_field := (@Query.is_field Name Vals).
  Notation is_inline_fragment := (@Query.is_inline_fragment Name Vals).


  

  Ltac orL := apply/orP; left.
  Ltac orR := apply/orP; right.
  
  Ltac apply_andP := apply/andP; split=> //.
  Ltac apply_and3P := apply/and3P; split=> //.
  Ltac all_cons := rewrite {1}/all -/(all _ _) => /andP; case.
  Ltac query_conforms := simp query_conforms; try move/and5P; try apply/and5P.


  Equations try_inline_query query (possible_types : seq (@NamedType Name)) : seq (@Query Name Vals) :=
    {
      try_inline_query q types with types != [::] :=
        {
        | true := [seq InlineFragment ty [:: q] | ty <- types];
        | _ := [:: q]
        }
    }.

  Equations? ground (type_in_scope : @NamedType Name) (queries : seq (@Query Name Vals)) :
    seq (@Query Name Vals) by wf (queries_size queries) :=
    {
      ground _ [::] := [::];

      ground ty (SingleField f α :: qs)
        with is_object_type s ty :=
        {
        | true := SingleField f α :: ground ty qs;
        | _ := try_inline_query (SingleField f α) (get_possible_types s ty) ++ ground ty qs
        };

      
      ground ty (LabeledField l f α :: qs)
        with is_object_type s ty :=
        {
        | true := LabeledField l f α :: ground ty qs;
        | _ := try_inline_query (LabeledField l f α) (get_possible_types s ty) ++ ground ty qs
        };

      ground ty (NestedField f α φ :: qs)
        with lookup_field_in_type s ty f :=
        {
        | Some fld
            with is_object_type s ty :=
            {
            | true := NestedField f α (ground fld.(return_type) φ) :: ground ty qs;
            | _ := try_inline_query (NestedField f α (ground fld.(return_type) φ)) (get_possible_types s ty) ++ ground ty qs
            };
        | _ => ground ty qs
        };

      ground ty (NestedLabeledField l f α φ :: qs)
        with lookup_field_in_type s ty f :=
        {
        | Some fld
            with is_object_type s ty :=
            {
            | true := NestedLabeledField l f α (ground fld.(return_type) φ) :: ground ty qs;
              | _ := try_inline_query (NestedLabeledField l f α (ground fld.(return_type) φ)) (get_possible_types s ty) ++ ground ty qs
              };
          | _ => ground ty qs
         };
        

       ground ty (InlineFragment t φ :: qs)
        with is_object_type s ty :=
         {
           
         | true with does_fragment_type_apply s ty t :=
             {
             | true := (ground ty φ) ++ ground ty qs;
             | _ := ground ty qs
             };
         
         | _ with is_object_type s t :=
             {
             | true with does_fragment_type_apply s t ty :=
                 {
                 | true := InlineFragment t (ground t φ) :: ground ty qs;
                 | _ := ground ty qs
                 };
             | _ := [seq InlineFragment sty (ground sty φ) | sty <- (get_possible_types s ty :&: get_possible_types s t)%SEQ]
                     ++ ground ty qs   
             }
         }

      
    }.
  Proof.
    all: do [by simp query_size; ssromega].
  Qed.

  Lemma get_possible_types_N_nil_are_Ot ty :
    get_possible_types s ty != [::] ->
    all (is_object_type s) (get_possible_types s ty).
  Proof.
    funelim (get_possible_types s ty) => //= _.
    - by simp is_object_type; rewrite Heq.
    - apply/allP=> x; apply: in_implementation_is_object.
    - apply/allP=> x.
      have <- : union_members s ty = f0 by rewrite /union_members Heq. 
      by apply: in_union_is_object.
  Qed.

  Lemma inlined_fields_are_grounded2 ty q pty :
    is_object_type s ty = false ->
    (get_possible_types s ty == [::]) = false ->
    all (is_object_type s) pty ->
    q.(is_field) ->
    (forall t, is_grounded2 s t q) ->
    are_grounded2 s ty [seq InlineFragment t [:: q] | t <- pty].
  Proof.
    move=> Hscope Hptys Hobjs Hfield Hg.
    elim: pty Hobjs => //= hd tl IH /andP [Hobj Hobjs].
    rewrite are_grounded2_clause_2_equation_1 Hscope Hptys /=; apply_and3P; last by apply: IH.
    simp is_grounded2; apply_andP.
    rewrite Hobj; case: eqP => //=; first by have := (get_possible_types_objectE Hobj) => -> /=.
    intros; apply_and3P.
  Qed.

  
  Lemma ground_are_grounded2 ty qs :
    are_grounded2 s ty (ground ty qs).
  Proof.
    funelim (ground ty qs) => //=.
    - case Hscope : is_object_type => //=; rewrite are_grounded2_clause_2_equation_1; case: eqP => //=.
        by have := (get_possible_types_objectE Hscope) => -> /=.
        by rewrite Heq in Hscope.
        simp try_inline_query; case: eqP => /= [| /eqP-/negbTE] Hpty.
        rewrite Heq are_grounded2_clause_2_equation_1 Hpty /=; apply_and3P.
        rewrite are_grounded2_cat; apply_andP.
        admit.
        (*
        apply: inlined_fields_are_grounded2 => //=; apply: get_possible_types_N_nil_are_Ot => //.
        by move/negbT in Hpty.
         *)
    - case Hscope : is_object_type => //=; rewrite are_grounded2_clause_2_equation_1; case: eqP => //=.
        by have := (get_possible_types_objectE Hscope) => -> /=.
        by rewrite Heq in Hscope.
        simp try_inline_query; case: eqP => /= [| /eqP-/negbTE] Hpty.
        rewrite Heq are_grounded2_clause_2_equation_1 Hpty /=; apply_and3P.
        rewrite are_grounded2_cat; apply_andP.
        admit.
        (*
        apply: inlined_fields_are_grounded2 => //=; apply: get_possible_types_N_nil_are_Ot => //.
        by move/negbT in Hpty.
         *)
          
    - case Hscope : is_object_type => //=; rewrite are_grounded2_clause_2_equation_1; case: eqP => //=.
        by have := (get_possible_types_objectE Hscope) => -> /=.
        by move=> Hpty; apply_and3P; simp is_grounded2; rewrite Heq0 /=.
        by rewrite Heq in Hscope.
        by rewrite Heq in Hscope.
        simp try_inline_query; case: eqP => /= [| /eqP-/negbTE] Hpty.
        rewrite Heq are_grounded2_clause_2_equation_1 Hpty /=; apply_and3P.
        by simp is_grounded2; rewrite Heq0.
        rewrite are_grounded2_cat; apply_andP.
       admit.
        (*
        apply: inlined_fields_are_grounded2 => //=; apply: get_possible_types_N_nil_are_Ot => //.
        by move/negbT in Hpty.
         *)
       
    - case Hscope : is_object_type => //=; rewrite are_grounded2_clause_2_equation_1; case: eqP => //=.
        by have := (get_possible_types_objectE Hscope) => -> /=.
        by move=> Hpty; apply_and3P; simp is_grounded2; rewrite Heq0 /=.
        by rewrite Heq in Hscope.
        by rewrite Heq in Hscope.
        simp try_inline_query; case: eqP => //= Hpty.
        rewrite Heq are_grounded2_clause_2_equation_1 Hpty /=; apply_and3P.
        by simp is_grounded2; rewrite Heq0.
        rewrite are_grounded2_cat; apply_andP.
        admit.

    - by rewrite are_grounded2_cat; apply_andP.

    - rewrite are_grounded2_cat; apply_andP.
      admit.

    - rewrite are_grounded2_clause_2_equation_1 Heq1; case: eqP => //= Hpty.
      admit. (* Contradiction *)
      apply_and3P; simp is_grounded2; apply_andP.
  Admitted.
      
        
  Lemma ground_cat ty qs1 qs2 :
    ground ty (qs1 ++ qs2) = ground ty qs1 ++ ground ty qs2.
  Proof.
    elim: qs1 => //=; case; intros; simp ground; do ? [case lookup_field_in_type => //=; case; intros]; case is_object_type => //=.
    all: do ? by rewrite -?catA H //=.

    by case: does_fragment_type_apply => //=; rewrite -catA H.
    case is_object_type => //=; last by rewrite -catA H.
    by case: does_fragment_type_apply => //=; rewrite H.
    Qed.
      
  Lemma ground_are_grounded ty qs :
    are_grounded s (ground ty qs).
  Proof.
      by apply: are_grounded2_are_grounded; apply: ground_are_grounded2.
  Qed.
 

   
 
  Equations filter_fragments_with_guard : @NamedType Name -> seq (@Query Name Vals) -> seq (@Query Name Vals) :=
    {
      filter_fragments_with_guard _ [::] := [::];
      
      filter_fragments_with_guard t (InlineFragment t' φ :: qs)
        with t' == t :=
        {
        | true := filter_fragments_with_guard t qs;
        | _ := InlineFragment t' φ :: filter_fragments_with_guard t qs
        };

      filter_fragments_with_guard t (_ :: qs) := filter_fragments_with_guard t qs
    }.

  Lemma filter_fragments_leq_size t qs :
    queries_size (filter_fragments_with_guard t qs) <= queries_size qs.
  Proof.
    funelim (filter_fragments_with_guard t qs) => //=; simp query_size; ssromega.
  Qed.

  Equations find_fields_with_response_name : Name -> seq (@Query Name Vals) -> seq (@Query Name Vals) :=
    {
       find_fields_with_response_name _ [::] := [::];

       find_fields_with_response_name k (InlineFragment t φ :: qs) := find_fields_with_response_name k qs;

      find_fields_with_response_name k (SingleField f α :: qs)
        with f == k :=
        {
        | true := SingleField f α :: find_fields_with_response_name k qs;
        | _ := find_fields_with_response_name k qs
        };
      
      find_fields_with_response_name k (LabeledField l f α :: qs)
        with l == k :=
        {
        | true := LabeledField l f α :: find_fields_with_response_name k qs;
        | _ := find_fields_with_response_name k qs
        };

      
      find_fields_with_response_name k (NestedField f α φ :: qs)
        with f == k :=
        {
        | true := NestedField f α φ :: find_fields_with_response_name k qs;
        | _ := find_fields_with_response_name k qs
        };
      
      find_fields_with_response_name k (NestedLabeledField l f α φ :: qs)
        with l == k :=
        {
        | true := NestedLabeledField l f α φ  :: find_fields_with_response_name k qs;
        | _ := find_fields_with_response_name k qs
        }
    }.

  Lemma all_found_fields_are_fields k qs :
    all is_field (find_fields_with_response_name k qs).
  Proof.
      by funelim (find_fields_with_response_name k qs).
  Qed.

  Lemma found_fields_leq_size k qs :
    queries_size (find_fields_with_response_name k qs) <= queries_size qs.
  Proof.
      by funelim (find_fields_with_response_name k qs) => //=; simp query_size; ssromega.
  Qed.
  
  Equations find_fragments_with_guard : @NamedType Name -> seq (@Query Name Vals) -> seq (@Query Name Vals) :=
    {
      find_fragments_with_guard _ [::] := [::];
      
      find_fragments_with_guard t (InlineFragment t' φ :: qs)
        with t' == t :=
        {
        | true := (InlineFragment t' φ :: find_fragments_with_guard t qs);
        | _ := find_fragments_with_guard t qs
        };

      find_fragments_with_guard t (q :: qs) := find_fragments_with_guard t qs
    }.

  Lemma found_fragments_leq_size t queries :
    queries_size (find_fragments_with_guard t queries) <= queries_size queries.
  Proof.
    funelim (find_fragments_with_guard t queries) => //=; simp query_size; ssromega.
  Qed.
  
  Obligation Tactic := intros; simp query_size; do ? ssromega; rewrite ?queries_size_app.  
  Equations remove_redundancies (queries : seq (@Query Name Vals)) :
    seq (@Query Name Vals) by wf (queries_size queries) lt :=
    {
      remove_redundancies [::] := [::];
      
      remove_redundancies (SingleField f α :: queries) :=
        (SingleField f α) :: remove_redundancies (filter_queries_with_label f queries);
      
      remove_redundancies (LabeledField l f α :: queries) :=
        (LabeledField l f α) :: remove_redundancies (filter_queries_with_label l queries);

      remove_redundancies (NestedField f α φ :: queries) :=
        NestedField f α (remove_redundancies (φ ++ (merge_selection_sets (find_fields_with_response_name f queries))))
                    :: remove_redundancies (filter_queries_with_label f queries);


      remove_redundancies (NestedLabeledField l f α φ :: queries) :=
        NestedLabeledField l f α (remove_redundancies (φ ++ (merge_selection_sets (find_fields_with_response_name l queries))))
                           :: remove_redundancies (filter_queries_with_label l queries);


      remove_redundancies ((InlineFragment t φ) :: queries) :=
        InlineFragment t (remove_redundancies (φ ++ (merge_selection_sets (find_fragments_with_guard t queries))))
                       :: remove_redundancies (filter_fragments_with_guard t queries)
      
    }.
  Solve Obligations with intros; simp query_size; move: (filter_queries_with_label_leq_size f queries) => Hlt; ssromega.
  Solve Obligations with intros; simp query_size; move: (filter_queries_with_label_leq_size l queries) => Hlt; ssromega.
  
  Next Obligation.
    have Hleq1 := (found_fields_leq_size f queries).
    have Hleq2 := (merged_selections_leq (find_fields_with_response_name f queries)).
    by ssromega.
  Qed.
  
  Next Obligation.
    have Hleq1 := (found_fields_leq_size l queries).
    have Hleq2 := (merged_selections_leq (find_fields_with_response_name l queries)).
    by ssromega.
  Qed.
  Next Obligation.
    have Hleq1 := (found_fragments_leq_size t queries).
    have Hleq2 := (merged_selections_leq (find_fragments_with_guard t queries)).
    by ssromega.
  Qed.
  Next Obligation.
    have Hleq := (filter_fragments_leq_size t queries); ssromega.
  Qed.


  Lemma filter_fields_preserves_not_similar q k (qs : seq (@Query Name Vals)) :
    all (fun q' => ~~ are_similar q' q) qs ->
    all (fun q' => ~~ are_similar q' q) (filter_queries_with_label k qs).
  Proof.
    funelim (filter_queries_with_label _ qs) => //= /andP [Hsim Hall]; simp are_similar; apply_andP.
    all: do ? by apply: H.
    by apply: H0.
  Qed.

  Transparent qresponse_name.
  Lemma all_not_similar_to_query_after_filter_fields q qs (Hfield : q.(is_field)) :
    all (fun q' => ~~ are_similar q' q) (filter_queries_with_label (qresponse_name q Hfield) qs).
  Proof.
    funelim (filter_queries_with_label _ qs) => //=; apply_andP; simp are_similar.
    case: q Hfield H H0 => //=.
    all: do ? by case: q Hfield H Heq => /=; intros; simp are_similar => /=.
  Qed.

  
  Lemma filter_fragments_preserves_not_similar q t (qs : seq (@Query Name Vals)) :
    all (fun q' => ~~ are_similar q' q) qs ->
    all (fun q' => ~~ are_similar q' q) (filter_fragments_with_guard t qs).
  Proof.
    by funelim (filter_fragments_with_guard _ qs) => //= /andP [Hsim Hall]; simp are_similar; apply_andP; apply: H.
  Qed.

  Lemma all_not_similar_to_fragment_after_filter qs :
    forall t φ,
    all (fun q' => ~~ are_similar q' (InlineFragment t φ)) (filter_fragments_with_guard t qs).
  Proof.
    move=> t φ.
    funelim (filter_fragments_with_guard _ qs) => //=; apply_andP; simp are_similar.
    by apply/negbT.
  Qed.

  (*
  Lemma filter_fields_preserves_not_similar qs q (Hfield : q.(is_field)) :
    all (fun q' => ~~ are_similar q' q) qs ->
    all (fun q' => ~~ are_similar q' q) (filter_queries_with_label (qresponse_name q Hfield) qs).
  Proof.
    funelim (filter_queries_with_label _ qs) => //= /andP [Hsim Hall]; simp are_similar; apply_andP.
    all: do ? by apply: H.
    by apply: H0.
  Qed. 
  
   *)
  
  Lemma remove_redundancies_preserves_not_similar_queries qs q :
    all (fun q' => ~~are_similar q' q) qs ->
    all (fun q' => ~~are_similar q' q) (remove_redundancies qs).
  Proof.
    funelim (remove_redundancies qs) => //= /andP [Hnsim Hall]; apply_andP;
    do ? apply: H => //; do ? apply: H0 => //; do ? by apply: filter_fields_preserves_not_similar.

    by apply: filter_fragments_preserves_not_similar.
  Qed.      
    

    
  Lemma remove_redundancies_is_non_redundant queries :
    are_non_redundant (remove_redundancies queries).
  Proof.
    funelim (remove_redundancies queries) => //=; simp are_non_redundant; apply_and3P.
    all: do ?[apply: remove_redundancies_preserves_not_similar_queries => //;
                by apply: all_not_similar_to_query_after_filter_fields].

    apply: remove_redundancies_preserves_not_similar_queries.
    by apply: all_not_similar_to_fragment_after_filter.
  Qed.

  Lemma filter_fields_preserves_grounded2 ty k qs :
    are_grounded2 s ty qs ->
    are_grounded2 s ty (filter_queries_with_label k qs).
  Proof.
    funelim (filter_queries_with_label k qs) => //=; rewrite !are_grounded2_clause_2_equation_1;
                                                 case Hscope : is_object_type;
                                                 case: eqP => //= Hpty;
                                                               case/and3P; intros; do ? apply_and3P; do ? by apply: H.
    - by move: p0; simp is_grounded2; case/andP; intros; apply_andP; apply: H.
    - by apply: H0.
  Qed.
    
  Lemma remove_redundancies_preserves_grounded2 ty qs :
    are_grounded2 s ty qs ->
    are_grounded2 s ty (remove_redundancies qs).
  Proof.
    funelim (remove_redundancies qs) => //=; case Hscope : is_object_type => /=;
    rewrite !are_grounded2_clause_2_equation_1; case: eqP => //= Hpty.
    all: do ? by case/and3P; intros; apply_and3P; apply: H; apply: filter_fields_preserves_grounded2.
    - case/and3P; intros; apply_and3P; move: p0; simp is_grounded2.
      case lookup_field_in_type => //; case => /=; intros.
      apply: H.
      rewrite are_grounded2_cat; apply_andP.
      admit.
  Admitted.

  Lemma remove_redundancies_in_grounding_are_grounded2 ty qs :
    are_grounded2 s ty (remove_redundancies (ground ty qs)).
  Proof.
    apply: remove_redundancies_preserves_grounded2.
      by apply: ground_are_grounded2.
  Qed.

  Lemma remove_redundancies_in_grounding_are_grounded ty qs :
    are_grounded s (remove_redundancies (ground ty qs)).
  Proof.
    apply: are_grounded2_are_grounded.
    by apply: remove_redundancies_in_grounding_are_grounded2.
  Qed.

  Definition normalize type_in_scope queries : seq Query := (remove_redundancies \o (ground type_in_scope)) queries.

  Lemma normalized_queries_are_in_normal_form ty qs :
    are_grounded s (normalize ty qs) /\ are_non_redundant (normalize ty qs).
  Proof.
    split; rewrite /normalize /=.
    - by apply: remove_redundancies_in_grounding_are_grounded.
    - by apply: remove_redundancies_is_non_redundant.
  Qed.


(*
  Lemma remove_redundancies_preserves_all_fields queries :
    all is_field queries ->
    all is_field (remove_redundancies queries).
  Proof.
    funelim (remove_redundancies queries) => //= /andP [Hfld Hflds]; apply_andP.
    all: do ?[by apply: H; apply: filter_preserves_pred].
    all: do ?[by apply: H0; apply: filter_preserves_pred].
  Qed.

  Lemma remove_redundancies_preserves_all_inlines queries :
    all is_inline_fragment queries ->
    all is_inline_fragment (remove_redundancies queries).
  Proof.
    funelim (remove_redundancies queries) => //= /andP [Hinl Hinls]; apply_andP.
    all: do ?[by apply: H; apply: filter_preserves_pred].
    all: do ?[by apply: H0; apply: filter_preserves_pred].
  Qed.
  


  Lemma notin_in_false {T : eqType} (x : T) (xs : mem_pred T) :
    x \notin xs -> x \in xs = false.
  Proof.
      by rewrite /negb; case: ifP.
  Qed.

 

  Lemma remove_redundancies_inlined_query schema type_in_scope q :
    remove_redundancies [seq InlineFragment ty [:: q] | ty <- get_possible_types schema type_in_scope] =
    [seq InlineFragment ty (remove_redundancies [:: q]) | ty <- get_possible_types schema type_in_scope].
  Proof.
    elim: get_possible_types => //= hd tl IH.
    simp remove_redundancies => /=.
     
  Admitted.
  
   
  Hint Resolve γ__φ_preserves_non_redundancy.
  Lemma non_redundant_eq_remove qs :
    are_non_redundant qs ->
    remove_redundancies qs = qs.
  Proof.
    apply_funelim (remove_redundancies qs) => //= [f α | l f α | f α φ | l f α φ | t φ] χ IH.
    all: do ?[by simp are_non_redundant; simp qresponse_name => /and3P [Hall Hnr Hnrs];
              congr cons;
              rewrite IH; [apply: γ__φ_no_repetition_eq | apply: γ__φ_preserves_non_redundancy]].
    

    all: do ?[by move=> IH2;
              simp are_non_redundant; simp qresponse_name => /and3P [Hall /= Hnr Hnrs];
              rewrite IH ?β__φ_has_none_nil ?cats0 //; congr cons;
              rewrite IH2; [apply: γ__φ_no_repetition_eq | apply: γ__φ_preserves_non_redundancy]].
  Qed.
  
      

  Lemma are_grounded_nil {schema ty} : are_grounded_2 schema ty [::]. Proof. done. Qed.
  Lemma are_non_redundant_nil : @are_non_redundant Name Vals [::]. Proof. done. Qed.


 


  Ltac resolve_grounded := case Hobj : is_object_type => //=; [| case: eqP => //= /eqP Heq].

  
  Lemma remove_redundancies_preserves_grounded schema qs ty :
      are_grounded_2 schema ty qs ->
      are_grounded_2 schema ty (remove_redundancies qs).
  Proof.
    funelim (remove_redundancies qs) => //=; case Hscope: is_object_type => //=.
    
    all: do ?[case: eqP => //= Hpty].
    all: do ?[move/and3P=> [Hty Hg Hgs]; apply_and3P].
    
    all: do ?[move: Hg; simp is_grounded_2; case Hlook: lookup_field_in_type => [fld|] //= Hg].
    all: do ?[by apply: H; apply: γ__φ_preserves_grounded].
    apply: H. rewrite -are_grounded_2_cat; split=> //.
  Admitted.
  

  Lemma obj_spreads_if_in_possible_types_of_interface schema ty ti :
    is_object_type schema ty ->
    is_interface_type schema ti ->
    ty \in get_possible_types schema ti ->
           is_fragment_spread_possible schema ti ty.
  Proof.
    move=> Hobj Hintf Hin.
    rewrite /is_fragment_spread_possible.
    rewrite (get_possible_types_interfaceE Hintf) in Hin *.
    by rewrite get_possible_types_objectE // seq1I Hin.
  Qed.

 
  Lemma map_N_nil {A B : eqType} (xs : seq A) (f : A -> B) :
    xs != [::] ->
    map f xs != [::].
  Proof.
      by case: xs.
  Qed.
        
  Lemma cat_N_nil {T : eqType} (xs xs' : seq T) :

    xs != [::] ->
    xs ++ xs' != [::].

  Proof. by case: xs.
  Qed.
  
  Lemma normalize_N_nil :
    forall schema ty q,
      query_conforms schema ty q ->
      has_valid_fragments schema ty q ->
      normalize schema ty q != [::].
  Proof.
    apply (normalize_elim
             (fun schema ty q nqs =>
                query_conforms schema ty q ->
                has_valid_fragments schema ty q ->
                nqs != [::])
             (fun schema ty qs nqs =>
                qs != [::] ->
                queries_conform schema ty qs ->
                all (has_valid_fragments schema ty) qs ->
                nqs != [::])) => //.
    all: do ?[intros => /=; simp try_inline_query;
              case Hpty: (_ != [::]) => //=;
                by apply: map_N_nil].
    all: do ?[by intros; simp query_conforms in H; rewrite Heq in H].

    - move=> schema t b ty φ IH Ht Hscope.
      query_conforms; move=> [_ _ Hne Hqsc Hmerge].
      simp has_valid_fragments; rewrite Hscope /= => /andP [/eqP Heq Hv].
      rewrite Heq in Hqsc.
       apply: IH => //; rewrite /queries_conform -?Heq; apply_andP.
       by rewrite Heq.
    - move=> schema t ty φ IH Ht Hscope.
      query_conforms; move=> [_ _ Hne Hqsc Hmerge].
      simp has_valid_fragments; rewrite Hscope /= => /andP [/orP [/eqP Heq | Hcontr] Hv].
      rewrite Heq in Hqsc Hv; apply: IH => //; rewrite  /queries_conform; apply_andP.
        by rewrite -Heq.
        by rewrite Ht in Hcontr.

    - move=> schema ty hd tl IHhd IHtl Hne.
      rewrite /queries_conform; case/andP.
      all_cons=> [Hqc Hqsc] _.      
      all_cons=> [Hv Hvs].
      by apply: cat_N_nil; apply: IHhd.
  Qed.
      
        
  Lemma normalize__φ_N_nil schema ty φ :
    φ != [::] ->
    queries_conform schema ty φ ->
    all (has_valid_fragments schema ty) φ ->
    normalize__φ schema ty φ != [::].
  Proof.
    case: φ => //= hd tl _.
    rewrite /queries_conform; case/andP.
    all_cons => [Hqc _] _.
    all_cons => [Hv _].
    apply: cat_N_nil.
    by apply: normalize_N_nil.
  Qed.
    

  Lemma normalize_preserves_conformance :
    forall schema ty q,
      query_conforms schema ty q ->
      has_valid_fragments schema ty q ->
      all (query_conforms schema ty) (normalize schema ty q).
  Proof.
    apply (normalize_elim
             (fun schema ty q nqs =>
                 query_conforms schema ty q ->
                 has_valid_fragments schema ty q ->
                 all (query_conforms schema ty) nqs)
             (fun schema ty qs nqs =>
                 all (query_conforms schema ty) qs ->
                 all (has_valid_fragments schema ty) qs ->
                 all (query_conforms schema ty) nqs)) => schema.
    Proof.
      all: do ?[by intros; rewrite all_seq1].
      all: do ?[intros; simp try_inline_query;
                case: eqP => //= Hpty; rewrite ?andbT //].

      - apply/allP=> x /mapP [q Hin ->].
        simp query_conforms.
        apply/and5P; split=> //.
        * by apply/or3P; constructor 1; apply (in_possible_types_is_object Hin).
        * move: (in_possible_types_is_object Hin) => Hobj.
          have Hfld : is_field (SingleField s0 f) by [].
          move: (scope_is_obj_or_abstract_for_field _ _ _ _ _ Hfld H) => [Hcontr | Hintf]; [by rewrite Heq in Hcontr|].
            by apply: obj_spreads_if_in_possible_types_of_interface.
        * rewrite all_seq1 //.
          have Hfld : is_field (SingleField s0 f) by [].
          move: (scope_is_obj_or_abstract_for_field _ _ _ _ _ Hfld H) => [Hcontr | Hintf]; [by rewrite Heq in Hcontr|].
          rewrite get_possible_types_interfaceE // in Hin.
            by apply (sf_conforms_in_interface_in_obj _ _ _ _ _ _ _ Hin).
            
      - apply/allP=> x /mapP [q Hin ->]; simp query_conforms.
        apply/and5P; split=> //.
        * by apply/or3P; constructor 1; apply (in_possible_types_is_object Hin).
        * move: (in_possible_types_is_object Hin) => Hobj.
          have Hfld : is_field (LabeledField s1 s2 f0) by [].
          move: (scope_is_obj_or_abstract_for_field _ _ _ _ _ Hfld H) => [Hcontr | Hintf]; [by rewrite Heq in Hcontr|].
            by apply: obj_spreads_if_in_possible_types_of_interface.
        * rewrite all_seq1.
          have Hfld : is_field (LabeledField s1 s2 f0) by [].
          move: (scope_is_obj_or_abstract_for_field _ _ _ _ _ Hfld H) => [Hcontr | Hintf]; [by rewrite Heq in Hcontr|].
          rewrite get_possible_types_interfaceE // in Hin.
            
    Admitted.





       
  Lemma normalize__φ_preserves_conformance schema ty qs :
    all (query_conforms schema ty) qs ->
    all (has_valid_fragments schema ty) qs ->
    all (query_conforms schema ty) (normalize__φ schema ty qs).
  Proof.
    
    elim: qs => // hd tl IH /= /andP [Hqc Hqsc] /andP [Hv Hvs].
    rewrite all_cat; apply_andP.
      by apply: normalize_preserves_conformance.
        by apply: IH.
  Qed.


  Lemma remove_redundancies_preserves_grounded_normalize schema ty qs :
    query_conforms schema ty qs ->
    has_valid_fragments schema ty qs ->
    are_grounded_2 schema ty (remove_redundancies (normalize schema ty qs)).
  Proof.
    move=> Hqc Hv.
    apply: remove_redundancies_preserves_grounded.
      by apply: normalize_is_grounded.
  Qed.
        
  Lemma remove_redundancies_preserves_grounded_normalize__φ schema ty qs :
    all (query_conforms schema ty) qs ->
    all (has_valid_fragments schema ty) qs ->
    are_grounded_2 schema ty (remove_redundancies (normalize__φ schema ty qs)).
  Proof.
    move=> Hqsc Hvs.
    apply: remove_redundancies_preserves_grounded => //.
      by apply: normalize__φ_are_grounded.
  Qed.




      
  
  Lemma remove_redundancies_preserves_normal_form_cat :
    forall schema ty qs qs',
      all (query_conforms schema ty) qs ->
      all (has_valid_fragments schema ty) qs ->
      all (query_conforms schema ty) qs' ->
      all (has_valid_fragments schema ty) qs' ->
      are_grounded_2 schema ty qs' ->
      are_grounded_2 schema ty (remove_redundancies (normalize__φ schema ty qs ++ qs')).
  Proof.
    intros.
    apply: remove_redundancies_preserves_grounded.
    rewrite -are_grounded_2_cat; split => //.
      by apply: normalize__φ_are_grounded.
  Qed.


  Lemma remove_redundancies_in_nil_N_nil qs :
    qs != [::] ->
    remove_redundancies qs != [::].
  Proof. by funelim (remove_redundancies qs). Qed.
  
  Lemma remove_redundancies_preserves_conformance schema ty qs :
    all (query_conforms schema ty) qs ->
    all (query_conforms schema ty) (remove_redundancies qs).
  Proof.
    funelim (remove_redundancies qs) => //; all_cons => [Hqc Hqsc].

    all: do ?[by rewrite /all; apply_andP; apply: filter_preserves_pred; apply: H].

    all: do ?[rewrite /all; apply_andP; last by apply: filter_preserves_pred; apply: H].

    all: do [pose Hqc' := Hqc].
    all: do ?[move/nf_conformsP: Hqc' => [fld Hlook /and5P [Hty Hargs Hne Hqc' Hmerge]]; simp query_conforms; rewrite Hlook /=].
    all: do ?[move/nlf_conformsP: Hqc' => [fld Hlook /and5P [Hty Hargs Hne Hqc' Hmerge]]; simp query_conforms; rewrite Hlook /=].
    all: do ?[move: Hqc'; query_conforms; move=> [Hty Hspread Hne Hqc' Hmerge']].
    all: do ?[apply/and5P; split => //].
    all: do ?[by apply: remove_redundancies_in_nil_N_nil; apply: cat_N_nil].
    all: do ?[apply: H0; rewrite all_cat; apply_andP].
    -
      admit.
    -  admit.
    -  admit.
  Admitted.
  
  Lemma remove_redundancies_normalize_preserves_normal_form :
    forall schema type_in_scope query,
      query_conforms schema type_in_scope query ->
      has_valid_fragments schema type_in_scope query -> 
      are_in_normal_form schema (remove_redundancies (normalize schema type_in_scope query)).
  Proof.
    move=> schema ty query Hqc Hv.
    move: (normalize_is_grounded schema ty query Hqc Hv) => Hg.
    move: (remove_redundancies_preserves_grounded_normalize schema ty query Hqc Hv).
    apply: are_grounded_2_in_normal_form.
    apply: remove_redundancies_preserves_conformance.
      by apply: normalize_preserves_conformance.
  Qed.

  Lemma remove_redundancies_normalize__φ_are_in_normal_form :
    forall schema type_in_scope queries,
      all (query_conforms schema type_in_scope) queries ->
      all (has_valid_fragments schema type_in_scope) queries -> 
      are_in_normal_form schema (remove_redundancies (normalize__φ schema type_in_scope queries)).
  Proof.
    move=> schema ty qs Hqc Hv.
    move: (normalize__φ_are_grounded _ _ _ Hqc Hv) => Hg.
    move: (remove_redundancies_preserves_grounded_normalize__φ _ _ _ Hqc Hv).
    apply are_grounded_2_in_normal_form.
     apply: remove_redundancies_preserves_conformance.
      by apply: normalize__φ_preserves_conformance.
  Qed.


  Lemma remove_redundancies_preserves_valid_fragments schema ty queries :
    all (has_valid_fragments schema ty) queries ->
    all (has_valid_fragments schema ty) (remove_redundancies queries).
  Admitted.
 
        *)
    
    
      
End QueryRewrite.


Arguments ground [Name Vals].


Arguments remove_redundancies [Name Vals].
