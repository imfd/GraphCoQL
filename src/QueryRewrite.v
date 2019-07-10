
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
        | _ := [seq InlineFragment t [:: SingleField f α] | t <- (get_possible_types s ty)] ++ ground ty qs
        };
      
      ground ty (LabeledField l f α :: qs)
        with is_object_type s ty :=
        {
        | true := LabeledField l f α :: ground ty qs;
        | _ := [seq InlineFragment t [:: LabeledField l f α] | t <- (get_possible_types s ty)] ++ ground ty qs
        };

      ground ty (NestedField f α φ :: qs)
        with lookup_field_in_type s ty f :=
        {
        | Some fld
            with is_object_type s ty :=
            {
            | true := NestedField f α (ground fld.(return_type) φ) :: ground ty qs;
            | _ := [seq InlineFragment t [:: NestedField f α (ground fld.(return_type) φ)] | t <- (get_possible_types s ty)] ++ ground ty qs
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
              | _ := [seq InlineFragment t [:: NestedLabeledField l f α (ground fld.(return_type) φ)] | t <- (get_possible_types s ty)] ++ ground ty qs
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
    Admitted.

  
  Lemma ground_are_grounded2 ty qs :
    are_grounded2 s ty (ground ty qs).
  Proof.
    funelim (ground ty qs) => //=.
    - case Hscope : is_object_type => //=.
      * by rewrite Heq in Hscope.

      * rewrite are_grounded2_cat; apply_andP.
        admit.

    - case Hscope : is_object_type => //=.
      * by rewrite Heq in Hscope.

      * rewrite are_grounded2_cat; apply_andP.
        admit.


    - case Hscope : is_object_type => //=; apply_and3P.

      * by simp is_grounded2; rewrite Heq0 /=.
      * by rewrite Heq in Hscope.
      * by simp is_grounded2; rewrite Heq0 /=.
      * rewrite are_grounded2_cat; apply_andP.
        admit.
        
    - case Hscope : is_object_type => //=; apply_and3P.

      * by simp is_grounded2; rewrite Heq0 /=.
      * by rewrite Heq in Hscope.
      * by simp is_grounded2; rewrite Heq0 /=.
      * rewrite are_grounded2_cat; apply_andP.
        admit.


    - by rewrite are_grounded2_cat; apply_andP.

    - rewrite are_grounded2_cat; apply_andP.
      admit.

    - by rewrite Heq1 /=; apply_and3P; simp is_grounded2; apply_andP.
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

  Lemma filter_preserves_grounded2 ty f qs :
    are_grounded2 s ty qs ->
    are_grounded2 s ty (filter_queries_with_label f qs).
  Proof.
    funelim (filter_queries_with_label f qs) => //=; case Hscope: is_object_type => //=.
    
    - simp is_grounded2 => /and3P [_ /andP [Hobj Hg] Hgs]; apply_and3P.
      * by apply_andP; apply: H.
      * by apply: H0.

        all: do [by case/and3P => *; do ? apply_and3P; apply: H].
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

      filter_fragments_with_guard t (q :: qs) := q :: filter_fragments_with_guard t qs
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


    
  Lemma remove_redundancies_preserves_grounded2 ty qs :
    are_grounded2 s ty qs ->
    are_grounded2 s ty (remove_redundancies qs).
  Proof.
    funelim (remove_redundancies qs) => //=; case Hscope : is_object_type => /=.

    all: do ? [case/and3P=> *; apply_and3P; do ? [by apply: H; apply: filter_preserves_grounded2]].

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

    
    
      
End QueryRewrite.


Arguments ground [Name Vals].

Arguments find_fragments_with_guard [Name Vals].
Arguments filter_fragments_with_guard [Name Vals].

Arguments remove_redundancies [Name Vals].

Arguments normalize [Name Vals].
