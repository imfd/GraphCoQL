From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.
From extructures Require Import ord fmap fset.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaWellFormedness.

Require Import Query.

Require Import Ssromega.

Require Import SeqExtra.

Require Import Arith.

Section QueryAux.

  Ltac case_response r := case: r => [l | l v | l vs | l ρ | l ρs].
  Ltac apply_andP := apply/andP; split => //.
  
  Variables Name Vals : ordType.

  Implicit Type queries : seq (@Query Name Vals).
  Implicit Type query : @Query Name Vals.

  
  (** Get the query's size, according to Jorge and Olaf's version **)
  Equations query_size query : nat :=
    {
      query_size (NestedField _ _ q') := 1 + queries_size q';
      query_size (NestedLabeledField _ _ _ q') => 1 + (queries_size q');
      query_size (InlineFragment _ q') => 1 + (queries_size q');
      query_size _ := 1
    }
  where
  queries_size queries : nat :=
    {
      queries_size [::] := 0;
      queries_size (cons hd tl) := query_size hd + queries_size tl
    }.

  Lemma queries_size_cat qs qs' :
    queries_size (qs ++ qs') = queries_size qs + queries_size qs'.
  Proof.
    elim: qs qs' => //= hd tl IH qs'.
    by rewrite (IH qs') addnA.
  Qed.

  Lemma query_size_gtn_0 q :
    0 < query_size q.
  Proof.
      by case: q.
  Qed.

  Lemma subqueries_lt_query q :
    queries_size q.(qsubqueries) < query_size q.
  Proof.
      by case: q.
  Qed.

  Lemma in_queries_lt q qs :
    q \in qs ->
          query_size q <= queries_size qs.
  Proof.
    elim: qs => //= hd tl IH.
    rewrite inE => /orP [/eqP -> | Hin].
      by ssromega.
      by move: (IH Hin) => Hlt; ssromega.
  Qed.

  Lemma in_subqueries_size_lt q1 q :
    q1 \in q.(qsubqueries) ->
           query_size q1 < query_size q.
  Proof.
    move=> Hin.
    have Hlt := (subqueries_lt_query q).
    have Hleq := (in_queries_lt Hin).
    ssromega.
  Qed.
    
  (** Partial equality between queries.
      It basically ignores subqueries and only checks labels, names and arguments **)
  Definition partial_query_eq (q1 q2 : @Query Name Vals) : bool :=
    match q1, q2 with
    | SingleField n α, SingleField n' α'
    | NestedField n α _, NestedField n' α' _ => (n == n') && (α == α')
    | LabeledField l n α, LabeledField l' n' α'
    | NestedLabeledField l n α _, NestedLabeledField l' n' α' _ => [&& (l == l'), (n == n') & (α == α')]
    | InlineFragment t _, InlineFragment t' _ => t == t'
    | _, _ => false
    end.


  
  Equations has_response_name : Name -> @Query Name Vals -> bool :=
    {
      has_response_name _ (InlineFragment _ _) := false;
      has_response_name rname q := (qresponse_name q _) == rname
    }.

  Equations has_field_name : Name -> @Query Name Vals -> bool :=
    {
      has_field_name _ (InlineFragment _ _) := false;
      has_field_name rname q := (qname q _) == rname
    }.
  
  Equations have_same_field_name : @Query Name Vals -> @Query Name Vals -> bool :=
    {
      have_same_field_name (InlineFragment _ _) _ := false;
      have_same_field_name _ (InlineFragment _ _) := false;
      have_same_field_name q1 q2 := (qname q1 _) == (qname q2 _)
    }.

  Equations have_same_arguments : @Query Name Vals -> @Query Name Vals -> bool :=
    {
      have_same_arguments (InlineFragment _ _) _ := false;
      have_same_arguments _ (InlineFragment _ _) := false;
      have_same_arguments q1 q2 := (qargs q1 _) == (qargs q2 _)
    }.

  

   Equations is_simple_field_selection : @Query Name Vals -> bool :=
    {
      is_simple_field_selection (SingleField _ _) := true;
      is_simple_field_selection (LabeledField _ _ _) := true;
      is_simple_field_selection _ := false
    }.
  
  Equations is_nested_field_selection : @Query Name Vals -> bool :=
    {
      is_nested_field_selection (NestedField _ _ _) := true;
      is_nested_field_selection (NestedLabeledField _ _ _ _) := true;
      is_nested_field_selection _ := false
    }.

  
  Definition are_equivalent (q1 q2 : @Query Name Vals) : bool :=
    [&& (q1.(is_simple_field_selection) && (q2.(is_simple_field_selection)) ||
         q1.(is_nested_field_selection) && q2.(is_nested_field_selection)),
        have_same_field_name q1 q2 & have_same_arguments q1 q2].
  
 
  Variable s : @wfSchema Name Vals.

  
  (**
     Checks whether the type guard in a fragment is valid wrt the
     actual type of the data (Object type).

    https://graphql.github.io/graphql-spec/June2018/#DoesFragmentTypeApply() 
   **)
  Definition does_fragment_type_apply object_type fragment_type :=
    if is_object_type s fragment_type then
      object_type == fragment_type
    else
      if is_interface_type s fragment_type then
        object_type \in implementation s fragment_type
      else
        if is_union_type s fragment_type then
          object_type \in union_members s fragment_type
        else
          false.

 

   Equations? find_queries_with_label (label : Name) (object_type : @NamedType Name) (queries : seq (@Query Name Vals)) :
    seq (@Query Name Vals) by wf (queries_size queries) :=
    {
      find_queries_with_label _ _ [::] := [::];

      find_queries_with_label k O__t (InlineFragment t φ :: qs)
        with does_fragment_type_apply O__t t :=
        {
        | true := find_queries_with_label k O__t φ ++ find_queries_with_label k O__t qs;
        | _ := find_queries_with_label k O__t qs
        };

      find_queries_with_label k O__t (SingleField f α :: qs)
        with f == k :=
        {
        | true := SingleField f α :: find_queries_with_label k O__t qs;
        | _ := find_queries_with_label k O__t qs
        };
      
      find_queries_with_label k O__t (LabeledField l f α :: qs)
        with l == k :=
        {
        | true := LabeledField l f α :: find_queries_with_label k O__t qs;
        | _ := find_queries_with_label k O__t qs
        };

      
      find_queries_with_label k O__t (NestedField f α φ :: qs)
        with f == k :=
        {
        | true := NestedField f α φ :: find_queries_with_label k O__t qs;
        | _ := find_queries_with_label k O__t qs
        };
      
      find_queries_with_label k O__t (NestedLabeledField l f α φ :: qs)
        with l == k :=
        {
        | true := NestedLabeledField l f α φ  :: find_queries_with_label k O__t qs;
        | _ := find_queries_with_label k O__t qs
        }
    }.
  all: do ?simp query_size; ssromega.
  Qed.

  Lemma found_queries_leq_size l O__t qs :
    queries_size (find_queries_with_label l O__t qs) <= queries_size qs.
  Proof.
    funelim (find_queries_with_label _ _ qs) => //=; simp query_size; rewrite ?queries_size_cat; ssromega.
  Qed.

  Lemma found_queries_are_fields k O__t qs :
    all (fun q => q.(is_field)) (find_queries_with_label k O__t qs).
  Proof.
    funelim (find_queries_with_label k O__t qs) => //=.
    rewrite all_cat; apply_andP.
  Qed.
  

  Lemma found_queries_are_fieldsP k O__t qs :
    forall q, q \in (find_queries_with_label k O__t qs) -> q.(is_field).
  Proof.
      by apply/allP; apply: found_queries_are_fields.
  Qed.


  Lemma all_same_label label O__t qs :
    all (fun q => match q with
               | InlineFragment _ _ => true
               | SingleField f _
               | NestedField f _ _ => f == label 
               | LabeledField l _ _
               | NestedLabeledField l _ _ _ => l == label
               end) (find_queries_with_label label O__t qs).
  Proof.
    funelim (find_queries_with_label label O__t qs) => //=; rewrite ?Heq ?andTb //.
    rewrite all_cat; apply_andP.
  Qed.

  Transparent oqresponse_name qresponse_name.
  Lemma found_queries_have_response_name rname O__t qs :
    forall q, q \in find_queries_with_label rname O__t qs ->
               q.(oqresponse_name) = Some rname.
  Proof.
    funelim (find_queries_with_label rname O__t qs) => //= q; rewrite ?inE.

    all: do ? [move=> /orP [/eqP -> /= | Hin]].
    all: do ? [by move/eqP in Heq; rewrite Heq].
    all: do ?[by apply: H].
    by rewrite mem_cat => /orP [Hin1 | Hin2]; [apply: H | apply: H0].
  Qed.
        
  Lemma all_in_same_label label O__t qs :
    forall q (Hfield : q.(is_field)), q \in find_queries_with_label label O__t qs ->
                                       (qresponse_name q Hfield) = label.
  Proof.
    move=> q Hfield Hin.
      by have /allP-/(_ q Hin) := (all_same_label label O__t qs);
                                   case: q Hfield Hin => //=; intros; simp qresponse_name; apply/eqP.
  Qed.
    
  Hint Resolve found_queries_leq_size.
  
  Equations? filter_queries_with_label (label : Name) (queries : seq (@Query Name Vals)) :
    seq (@Query Name Vals) by wf (queries_size queries) :=
    {
      filter_queries_with_label _ [::] := [::];

      filter_queries_with_label l (InlineFragment t φ :: qs) :=
        InlineFragment t (filter_queries_with_label l φ) :: filter_queries_with_label l qs;

      filter_queries_with_label l (q :: qs)
        with (qresponse_name q _) != l :=
        {
        | true := q :: filter_queries_with_label l qs;
        | _ := filter_queries_with_label l qs
        }     

    }.
  all: do ?[simp query_size; ssromega].
  Qed.

  Lemma filter_queries_with_label_leq_size l qs :
    queries_size (filter_queries_with_label l qs) <= queries_size qs.
  Proof.
    funelim (filter_queries_with_label l qs) => //=; do ?[simp query_size; ssromega]. 
  Qed.

  Transparent qresponse_name.
  Lemma filter_fields_spec l φ :
    all (fun q => q.(is_field)) φ ->
    filter_queries_with_label l φ = [seq q <- φ | match q with
                                                 | SingleField f _
                                                 | NestedField f _ _ => f != l
                                                 | LabeledField l' _ _
                                                 | NestedLabeledField l' _ _ _ => l' != l
                                                 | _ => false
                                                 end ].
  Proof.
      by funelim (filter_queries_with_label l φ) => //= /andP [Hf Hflds]; rewrite Heq H.
  Qed.
    

                                    
  Equations merge_selection_sets : seq (@Query Name Vals) -> seq (@Query Name Vals) :=
    {
      merge_selection_sets [::] := [::];
      merge_selection_sets (q :: qs) := q.(qsubqueries) ++ merge_selection_sets qs
    }.

  Transparent merge_selection_sets qsubqueries.
  
  Lemma merge_selection_sets_cat (qs1 qs2 : seq (@Query Name Vals)) :
    merge_selection_sets (qs1 ++ qs2) = merge_selection_sets qs1 ++ merge_selection_sets qs2.
  Proof.
      by elim: qs1 qs2 => //=; case; intros; simp merge_selection_sets => /=; rewrite H catA.
  Qed.
  
  Lemma merged_selections_lt qs :
    qs != [::] ->
    queries_size (merge_selection_sets qs) < queries_size qs.
  Proof.
    funelim (merge_selection_sets qs) => //=.
    case: q; intros => //=; simp query_size; rewrite ?queries_size_cat;
    case: l H => //= hd tl /(_ is_true_true) H; ssromega.
  Qed.

  Lemma merged_selections_leq qs :
    queries_size (merge_selection_sets qs) <= queries_size qs.
  Proof.
    funelim (merge_selection_sets qs) => //=.
    case: q; intros => //=; simp query_size; rewrite ?queries_size_cat;
     ssromega.
  Qed.


  
 Lemma queries_size_0_nil (qs : seq (@Query Name Vals)) : queries_size qs == 0 -> qs = [::].
  Proof.
    by elim: qs => //=; case=> [f α | l f α | f α φ | l f α φ | t φ] qs IH /=; rewrite addn_eq0.
  Qed.
  

  Lemma filter_queries_with_label_cat l (qs1 qs2 : seq (@Query Name Vals)) :
    filter_queries_with_label l (qs1 ++ qs2) = filter_queries_with_label l qs1 ++ filter_queries_with_label l qs2.
  Proof.
    elim: qs1  => //= hd tl IH.
    case: hd => //=; intros; simp filter_queries_with_label; do ?[by case: eqP => //= Heq; rewrite IH].
    by rewrite IH.
  Qed.
  
  Lemma find_queries_with_label_cat l ty (qs1 qs2 : seq (@Query Name Vals)):
    find_queries_with_label l ty (qs1 ++ qs2) = find_queries_with_label l ty qs1 ++ find_queries_with_label l ty qs2.
  Admitted.

  Lemma filter_swap f1 f2 (φ : seq (@Query Name Vals)) :
    filter_queries_with_label f1 (filter_queries_with_label f2 φ) =
    filter_queries_with_label f2 (filter_queries_with_label f1 φ).
  Admitted.
  
  Lemma filter_filter_absorb k (qs : seq (@Query Name Vals)) :
    filter_queries_with_label k (filter_queries_with_label k qs) = filter_queries_with_label k qs.
  Admitted.
  
  
  Equations? find_fields_with_response_name (rname : Name) (φ : seq (@Query Name Vals)) :
    seq (@Query Name Vals) by wf (queries_size φ) :=
    {
      find_fields_with_response_name _ [::] := [::];
      
      
      find_fields_with_response_name rname (SingleField f α :: qs)
        with f == rname :=
        {
        | true := SingleField f α :: find_fields_with_response_name rname qs;
        | _ := find_fields_with_response_name rname qs
        };
      
      find_fields_with_response_name rname (LabeledField l f α :: qs)
        with l == rname :=
        {
        | true := LabeledField l f α :: find_fields_with_response_name rname qs;
        | _ := find_fields_with_response_name rname qs
        };

      
      find_fields_with_response_name rname (NestedField f α φ :: qs)
        with f == rname :=
        {
        | true := NestedField f α φ :: find_fields_with_response_name rname qs;
        | _ := find_fields_with_response_name rname qs
        };
      
      find_fields_with_response_name rname (NestedLabeledField l f α φ :: qs)
        with l == rname :=
        {
        | true := NestedLabeledField l f α φ  :: find_fields_with_response_name rname qs;
        | _ := find_fields_with_response_name rname qs
        };
      
      find_fields_with_response_name rname (InlineFragment t φ :: qs) :=
        find_fields_with_response_name rname φ ++ find_fields_with_response_name rname qs
    }.
  Proof.
    all: do [by simp query_size; ssromega].
  Qed.

  Lemma all_found_fields_are_fields k qs :
    all (fun q => q.(is_field)) (find_fields_with_response_name k qs).
  Proof.
    funelim (find_fields_with_response_name k qs) => //=.
      by rewrite all_cat; apply_andP.
  Qed.

  Lemma found_fields_leq_size k qs :
    queries_size (find_fields_with_response_name k qs) <= queries_size qs.
  Proof.
    funelim (find_fields_with_response_name k qs) => //=; simp query_size; do ? ssromega.
      by rewrite queries_size_cat; ssromega.
  Qed.


  Lemma merge_simple_fields_is_empty φ :
    all is_simple_field_selection φ ->
    merge_selection_sets φ = [::].
  Proof.
    by elim: φ => //=; case.
  Qed.

  

  Lemma find_all_q_equiv_to_sf_are_simple ty f α φ :
    all (are_equivalent (SingleField f α)) (find_queries_with_label f ty φ) ->
    all (fun q => q.(is_simple_field_selection)) (find_queries_with_label f ty φ).
  Proof.
    funelim (find_queries_with_label f ty φ) => //=.

    all: do ? by case/andP=> *; apply_andP; apply: (H α).
    all: do ? by move=> *; apply: (H α).

    by rewrite 2!all_cat => /andP [Hall1 Hall2]; apply_andP; [apply: (H α) | apply: (H0 α)].

  Qed.

  Lemma find_all_f_equiv_to_sf_are_simple ty f α (φ : seq (@Query Name Vals)) :
    all (are_equivalent (SingleField f α)) (find_fields_with_response_name f φ) ->
    all (fun q => q.(is_simple_field_selection)) (find_queries_with_label f ty φ).
  Proof.
    funelim (find_queries_with_label f ty φ) => //=.

    all: do ?[by simp find_fields_with_response_name; rewrite Heq /= => /andP [Hequiv Hequivs]; apply_andP; apply: (H α)].

    all: do ? by simp find_fields_with_response_name; rewrite Heq /= => *; apply: (H α).

    - by simp find_fields_with_response_name; rewrite 2!all_cat => /andP [Hequiv Hequivs]; apply_andP; [apply: (H α) | apply: (H0 α)].
    - by simp find_fields_with_response_name; rewrite all_cat => /andP [Hequiv Hequivs]; apply: (H α).
        
  Qed.



  Lemma find_queries_subseq_find_fields ty f φ :
    subseq (find_queries_with_label f ty φ) (find_fields_with_response_name f φ).
  Proof.
    funelim (find_queries_with_label f ty φ) => //=.
    all: do ?[simp find_fields_with_response_name; rewrite Heq /=; case: ifP => //=; by move/negbT/eqP].

    all: do ? by simp find_fields_with_response_name; rewrite Heq /=.

    by simp find_fields_with_response_name; rewrite cat_subseq.
    simp find_fields_with_response_name.
    rewrite -[find_queries_with_label _ _ _]cat0s; rewrite cat_subseq //=.
    apply: sub0seq.
  Qed. 

  Lemma find_fields_cat rname φ1 φ2 :
    find_fields_with_response_name rname (φ1 ++ φ2) =
    find_fields_with_response_name rname φ1 ++ find_fields_with_response_name rname φ2.
  Admitted.
    
    
End QueryAux.

Arguments has_response_name [Name Vals].
Arguments has_field_name [Name Vals].
Arguments have_same_field_name [Name Vals].
Arguments have_same_arguments [Name Vals].
Arguments are_equivalent [Name Vals].
Arguments filter_queries_with_label [Name Vals].
Arguments find_queries_with_label [Name Vals].
Arguments find_fields_with_response_name [Name Vals].