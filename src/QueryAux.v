From mathcomp Require Import all_ssreflect.
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

  Ltac apply_andP := apply/andP; split => //.
  
  Variables Name Vals : ordType.

  Implicit Type queries : seq (@Query Name Vals).
  Implicit Type query : @Query Name Vals.

  Transparent qname oqresponse_name qresponse_name.
   
  Section Size.
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
        queries_size (hd :: tl) := query_size hd + queries_size tl
      }.

    
    Lemma queries_size_sumn φ :
      queries_size φ = sumn [seq query_size q | q <- φ].
    Proof.
      by elim: φ => //= q φ IH; case: q => /= *; simp query_size; rewrite IH.
    Qed.
      
      
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
      have Hleq := (in_queries_lt _ _ Hin).
      ssromega.
    Qed.

    
  
    Lemma queries_size_0_nil (qs : seq (@Query Name Vals)) : queries_size qs == 0 -> qs = [::].
    Proof.
        by elim: qs => //=; case=> [f α | l f α | f α φ | l f α φ | t φ] qs IH /=; rewrite addn_eq0.
    Qed.
    

    Equations max_query_size query : nat :=
      {
        max_query_size (NestedField _ _ φ) := (max_queries_size φ).+1;
        max_query_size (NestedLabeledField _ _ _ φ) := (max_queries_size φ).+1;
        max_query_size (InlineFragment _ φ) := (max_queries_size φ).+1;
        max_query_size _ := 0
      }
    where max_queries_size queries : nat :=
            {
              max_queries_size [::] := 0;
              max_queries_size (q :: φ) := max (max_query_size q) (max_queries_size φ)
            }.

    

  End Size.
    

  
  
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

  (** Checks whether the field selection is defined in the given name *)
  Equations is_defined query (Hfield : query.(is_field)) (ty : Name) : bool :=
    {
      is_defined q Hfield ty := isSome (lookup_field_in_type s ty (qname q Hfield))
    }.

  Equations? are_defined queries (ty : Name) : bool by wf (queries_size queries) :=
    {
      are_defined [::] _ := true;

      are_defined (InlineFragment t β :: φ) ty := are_defined β t && are_defined φ ty;

      are_defined (q :: φ) ty := is_defined q _ ty && are_defined φ ty
    }.
  Proof.
    all: do ? [simp query_size; ssromega].
  Qed.

  Lemma is_definedE q (Hfield : q.(is_field)) ty :
    is_defined q Hfield ty ->
    exists fld, lookup_field_in_type s ty (qname q Hfield) = Some fld.
  Proof.
    funelim (is_defined _ _ _) => //=.
    by rewrite /isSome; case lookup_field_in_type => //= fld _; exists fld.
  Qed.

  Lemma are_defined_cat φ1 φ2 ty :
    are_defined (φ1 ++ φ2) ty = are_defined φ1 ty && are_defined φ2 ty.
  Proof.
    funelim (are_defined φ1 ty) => //=; simp are_defined is_defined => /=; rewrite ?H ?H0 ?andbA //.
  Qed.
    
    
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

 

  Section Find.

    (** Find all queries with response name equal to given parameter.
        In case there is a fragment, it first checks that the fragments' guard 
        applies to the given object type, then it may proceed to collect in its
        subqueries **)
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

        find_queries_with_label k O__t (q :: qs)
          with (qresponse_name q _) == k :=
          {
          | true := q :: find_queries_with_label k O__t qs;
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

    Lemma find_queries_with_label_cat l ty (qs1 qs2 : seq (@Query Name Vals)):
      find_queries_with_label l ty (qs1 ++ qs2) = find_queries_with_label l ty qs1 ++ find_queries_with_label l ty qs2.
    Proof.
      funelim (find_queries_with_label l ty qs1) => //=.
      all: do ? by simp find_queries_with_label; rewrite Heq /= H.
        by simp find_queries_with_label; rewrite Heq /= H0 catA.
    Qed.
    


    
    Lemma found_queries_have_response_name rname O__t qs :
      forall q, q \in find_queries_with_label rname O__t qs ->
                 q.(oqresponse_name) = Some rname.
    Proof.
      funelim (find_queries_with_label rname O__t qs) => //= q; rewrite ?inE.

      all: do ? [move=> /orP [/eqP -> /= | Hin]].
      all: do ? [by simpl in Heq; move/eqP in Heq; congr Some].
      all: do ?[by apply: H].    
        by rewrite mem_cat => /orP [Hin1 | Hin2]; [apply: H | apply: H0].
    Qed.
    

   
      
  

    (** Find all field selections with response name equal to the one given as parameter.
        It collects all, regardless of fragments' guards 
     **)
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


  End Find.
    
  Hint Resolve found_queries_leq_size.

  Section Filter.
    (** Filters all selections with response name equal to the one given as parameter **)
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

    
    Lemma filter_queries_with_label_cat l (qs1 qs2 : seq (@Query Name Vals)) :
      filter_queries_with_label l (qs1 ++ qs2) = filter_queries_with_label l qs1 ++ filter_queries_with_label l qs2.
    Proof.
      elim: qs1  => //= hd tl IH.
      case: hd => //=; intros; simp filter_queries_with_label; do ?[by case: eqP => //= Heq; rewrite IH].
        by rewrite IH.
    Qed.

    Lemma filter_all rname (φ : seq (@Query Name Vals)) :
      all (has_response_name rname) φ ->
      filter_queries_with_label rname φ = [::].
    Proof.
        by elim: φ => //=; case=> //= [f' α | l f' α | f' α β | l f' α β] φ IH; simp has_response_name => /= /andP [/eqP Heq Hsame];
                                                                                                         simp filter_queries_with_label => /=; 
                                                                                                                                            rewrite Heq /=; case: eqP => //= _; apply: IH.
    Qed.
    
    
    Lemma filter_frag (ptys : seq (@NamedType Name)) f φ :
      all (has_response_name f) φ ->
      filter_queries_with_label f [seq InlineFragment t φ | t <- ptys] =
      [seq InlineFragment t [::] | t <- ptys].
    Proof.
      move=> /filter_all Heq.
      elim: ptys => //= q qs IHqs; simp filter_queries_with_label => /=.
        by rewrite Heq IHqs.
    Qed.

    Lemma filter_swap f1 f2 (φ : seq (@Query Name Vals)) :
      filter_queries_with_label f1 (filter_queries_with_label f2 φ) =
      filter_queries_with_label f2 (filter_queries_with_label f1 φ).
    Admitted.
    
    Lemma filter_filter_absorb k (qs : seq (@Query Name Vals)) :
      filter_queries_with_label k (filter_queries_with_label k qs) = filter_queries_with_label k qs.
    Admitted.

    Lemma filter_preserves_definition rname qs ty :
      are_defined qs ty ->
      are_defined (filter_queries_with_label rname qs) ty.
    Proof.
      funelim (filter_queries_with_label rname qs) => //=; simp are_defined.
      - by move=> /andP [Hdef Hdefs]; apply_andP; [apply: H| apply: H0].
      all: do ? by move=> /andP [Hdef Hdefs]; apply_andP; apply: H.
      all: do ? by move=> /andP [Hdef Hdefs]; apply: H.
    Qed.

    Lemma find_filter_nil rname O__t qs :
      find_queries_with_label rname O__t (filter_queries_with_label rname qs) = [::].
    Proof.
      funelim (filter_queries_with_label rname qs) => //=; do ? by simp find_queries_with_label; move/negbTE in Heq; rewrite Heq /=.
      by simp find_queries_with_label; case: does_fragment_type_apply => //=; rewrite H H0 /=.
    Qed.
      
  End Filter.

  Section Merging.
    Definition merge_selection_sets queries := flatten [seq q.(qsubqueries) | q <- queries].
    
    (* Equations merge_selection_sets : seq (@Query Name Vals) -> seq (@Query Name Vals) := *)
    (*   { *)
    (*     merge_selection_sets [::] := [::]; *)
    (*     merge_selection_sets (q :: qs) := q.(qsubqueries) ++ merge_selection_sets qs *)
    (*   }. *)

    (* Transparent merge_selection_sets qsubqueries. *)
    
    Lemma merge_selection_sets_cat (qs1 qs2 : seq (@Query Name Vals)) :
      merge_selection_sets (qs1 ++ qs2) = merge_selection_sets qs1 ++ merge_selection_sets qs2.
    Proof.
        by rewrite /merge_selection_sets map_cat flatten_cat.
    Qed.
    

    Lemma merged_selections_leq qs :
      queries_size (merge_selection_sets qs) <= queries_size qs.
    Proof.
      rewrite /merge_selection_sets.
        by elim: qs => //=; case=> //= *; simp query_size; rewrite ?queries_size_cat; ssromega.
    Qed.

    
    Lemma merge_simple_fields_is_empty φ :
      all is_simple_field_selection φ ->
      merge_selection_sets φ = [::].
    Proof.
        by elim: φ => //=; case.
    Qed.

    
  End Merging.




  Lemma find_all_q_equiv_to_sf_are_simple α f ty φ :
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


  Lemma find_filter_swap f1 f2 ty φ :
    f1 == f2 = false ->
    find_queries_with_label f1 ty (filter_queries_with_label f2 φ) = (find_queries_with_label f1 ty φ).
  Proof.
    elim: φ => //=; case=> [f α | l f α | f α β | l f α β | t β] φ IH Hneq; simp filter_queries_with_label; simp find_queries_with_label => /=.
  Admitted.

  Lemma find_absorb f ty φ :
    find_queries_with_label f ty (find_queries_with_label f ty φ) = find_queries_with_label f ty φ.
  Admitted.

  Lemma filter_find_nil f ty φ :
    filter_queries_with_label f (find_queries_with_label f ty φ) = [::].
  Admitted.

  Lemma filter_find_swap f1 f2 ty φ :
   filter_queries_with_label f1 (find_queries_with_label f2 ty φ) = find_queries_with_label f2 ty (filter_queries_with_label f1 φ).
  Admitted. 
    
End QueryAux.

Arguments query_size [Name Vals].
Arguments queries_size [Name Vals].
Arguments has_response_name [Name Vals].
Arguments has_field_name [Name Vals].
Arguments have_same_field_name [Name Vals].
Arguments have_same_arguments [Name Vals].
Arguments are_equivalent [Name Vals].
Arguments is_defined [Name Vals].
Arguments are_defined [Name Vals].
Arguments does_fragment_type_apply [Name Vals].
Arguments filter_queries_with_label [Name Vals].
Arguments filter_queries_with_label_leq_size [Name Vals].
Arguments find_queries_with_label [Name Vals].
Arguments found_queries_leq_size [Name Vals].
Arguments find_fields_with_response_name [Name Vals].
Arguments found_fields_leq_size [Name Vals].
Arguments merge_selection_sets [Name Vals].
Arguments merged_selections_leq [Name Vals].