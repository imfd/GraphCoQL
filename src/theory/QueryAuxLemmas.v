From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From extructures Require Import ord.

From Equations Require Import Equations.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaAuxLemmas.
Require Import SchemaWellFormedness.
Require Import SchemaWFLemmas.

Require Import Query.
Require Import QueryAux.

Require Import SeqExtra.
Require Import Ssromega.


Section Theory.
  Ltac apply_andP := apply/andP; split => //.
  Transparent qname oqresponse_name qresponse_name.

  Variables Name Vals : ordType.

  Implicit Type φ : seq (@Query Name Vals).
  Implicit Type query : @Query Name Vals.


  Section DefPreds.
    Variable (s : @wfSchema Name Vals).
    
    Lemma object_applies_to_itself ty :
      is_object_type s ty ->
      does_fragment_type_apply s ty ty.
    Proof.
        by rewrite /does_fragment_type_apply => ->.
    Qed.
  End DefPreds.
  
  Section Size.
    
    Lemma queries_size_sumn φ :
      queries_size φ = sumn [seq query_size q | q <- φ].
    Proof.
        by elim: φ => //= q φ IH; case: q => /= *; simp query_size; rewrite IH.
    Qed.
    
    
    Lemma queries_size_cat φ φ' :
      queries_size (φ ++ φ') = queries_size φ + queries_size φ'.
    Proof.
      elim: φ φ' => //= hd tl IH φ'.
        by rewrite (IH φ') addnA.
    Qed.

    Lemma query_size_gtn_0 query :
      0 < query_size query.
    Proof.
        by case: query.
    Qed.

    Lemma subqueries_lt_query query :
      queries_size query.(qsubqueries) < query_size query.
    Proof.
        by case: query.
    Qed.


    
    Lemma in_queries_lt query φ :
      query \in φ ->
            query_size query <= queries_size φ.
    Proof.
      elim: φ => //= q φ IH.
      rewrite inE => /orP [/eqP -> | Hin].
        by ssromega.
          by move: (IH Hin) => Hlt; ssromega.
    Qed.

    Lemma in_subqueries_size_lt query1 query :
      query1 \in query.(qsubqueries) ->
             query_size query1 < query_size query.
    Proof.
      move=> Hin.
      have Hlt := (subqueries_lt_query query).
      have Hleq := (in_queries_lt Hin).
      ssromega.
    Qed.

    
    
    Lemma queries_size_0_nil (qs : seq (@Query Name Vals)) : queries_size qs == 0 -> qs = [::].
    Proof.
        by elim: qs => //=; case=> [f α | l f α | f α φ | l f α φ | t φ] qs IH /=; rewrite addn_eq0.
    Qed.
    
  End Size.


  (* Section DefPreds. *)
    
  (*   Variable (s : @wfSchema Name Vals). *)
    
  (*   Lemma is_definedE q (Hfield : q.(is_field)) ty : *)
  (*     is_defined s q Hfield ty -> *)
  (*     exists fld, lookup_field_in_type s ty (qname q Hfield) = Some fld. *)
  (*   Proof. *)
  (*     funelim (is_defined _ _ _ _) => //=. *)
  (*       by rewrite /isSome; case lookup_field_in_type => //= fld _; exists fld. *)
  (*   Qed. *)

  (*   Lemma are_defined_cat φ1 φ2 ty : *)
  (*     are_defined s (φ1 ++ φ2) ty = are_defined s φ1 ty && are_defined φ2 ty. *)
  (*   Proof. *)
  (*     funelim (are_defined φ1 ty) => //=; simp are_defined is_defined => /=; rewrite ?H ?H0 ?andbA //. *)
  (*   Qed. *)
  (* End DefPreds. *)

  Section Find.
    Variable (s : @wfSchema Name Vals).
    
    Lemma found_queries_leq_size l O__t qs :
      queries_size (find_queries_with_label s l O__t qs) <= queries_size qs.
    Proof.
      funelim (find_queries_with_label _ _ _ qs) => //=; simp query_size; rewrite ?queries_size_cat; ssromega.
    Qed.

    Lemma found_queries_are_fields k O__t qs :
      all (fun q => q.(is_field)) (find_queries_with_label s k O__t qs).
    Proof.
      funelim (find_queries_with_label s k O__t qs) => //=.
      rewrite all_cat; apply_andP.
    Qed.

    Lemma find_queries_with_label_cat l ty (qs1 qs2 : seq (@Query Name Vals)):
      find_queries_with_label s l ty (qs1 ++ qs2) = find_queries_with_label s l ty qs1 ++ find_queries_with_label s l ty qs2.
    Proof.
      funelim (find_queries_with_label s l ty qs1) => //=.
      all: do ? by simp find_queries_with_label; rewrite Heq /= H.
        by simp find_queries_with_label; rewrite Heq /= H0 catA.
    Qed.

    
    Lemma found_queries_have_response_name rname O__t qs :
      forall q, q \in find_queries_with_label s rname O__t qs ->
                 q.(oqresponse_name) = Some rname.
    Proof.
      funelim (find_queries_with_label s rname O__t qs) => //= q; rewrite ?inE.

      all: do ? [move=> /orP [/eqP -> /= | Hin]].
      all: do ? [by simpl in Heq; move/eqP in Heq; congr Some].
      all: do ?[by apply: H].    
        by rewrite mem_cat => /orP [Hin1 | Hin2]; [apply: H | apply: H0].
    Qed.
    

    
    Lemma all_found_fields_are_fields k φ :
      all (fun query => query.(is_field)) (find_fields_with_response_name k φ).                  
    Proof.
      funelim (find_fields_with_response_name k φ) => //=.
        by rewrite all_cat; apply_andP.
    Qed.

    Lemma found_fields_leq_size k φ :
      queries_size (find_fields_with_response_name k φ) <= queries_size φ.
    Proof.
      funelim (find_fields_with_response_name k φ) => //=; simp query_size; do ? ssromega.
        by rewrite queries_size_cat; ssromega.
    Qed.

    Lemma find_map_inline_nil_func (f : Name -> seq (@Query Name Vals) -> seq Query) rname t ptys φ :
      uniq ptys ->
      all (is_object_type s) ptys ->
      t \notin ptys ->
      find_queries_with_label s rname t [seq InlineFragment t' (f t' φ) | t' <- ptys] = [::].
    Proof.      
      elim: ptys => //= t' ptys IH /andP [Hnin Huniq] /andP [Hobj Hinobj] Htnin.
      simp find_queries_with_label.
      have -> /= : does_fragment_type_apply s t t' = false.
      rewrite /does_fragment_type_apply Hobj /=. 
        by move/memPn: Htnin => /(_ t' (mem_head t' ptys)) /negbTE; rewrite eq_sym.
        apply: IH => //=.
          by move: Htnin; rewrite /negb; case: ifP => //=; case: ifP => //= Hcontr <- _; apply: mem_tail.
    Qed.

    
    Lemma find_map_inline_nil rname t ptys φ :
      uniq ptys ->
      all (is_object_type s) ptys ->
      t \notin ptys ->
      find_queries_with_label s rname t [seq InlineFragment t' φ | t' <- ptys] = [::].
    Proof.
      
      elim: ptys => //= t' ptys IH /andP [Hnin Huniq] /andP [Hobj Hinobj] Htnin.
      simp find_queries_with_label.
      have -> /= : does_fragment_type_apply s t t' = false.
      rewrite /does_fragment_type_apply Hobj /=. 
        by move/memPn: Htnin => /(_ t' (mem_head t' ptys)) /negbTE; rewrite eq_sym.
        apply: IH => //=.
          by move: Htnin; rewrite /negb; case: ifP => //=; case: ifP => //= Hcontr <- _; apply: mem_tail.
    Qed.

    Lemma find_map_inline_nil_get_types rname t ty φ :
      t \notin get_possible_types s ty ->
      find_queries_with_label s rname t [seq InlineFragment t' φ | t' <- get_possible_types s ty] = [::].
    Proof.
        by move=> Hnin; apply: find_map_inline_nil => //=; [apply: uniq_get_possible_types | apply/allP; apply: in_possible_types_is_object].
    Qed.

    
    Lemma find_all_q_equiv_to_sf_are_simple α f ty φ :
      all (are_equivalent (SingleField f α)) (find_queries_with_label s f ty φ) ->
      all (fun query => query.(is_simple_field_selection)) (find_queries_with_label s f ty φ).
    Proof.
      funelim (find_queries_with_label s f ty φ) => //=.

      all: do ? by case/andP=> *; apply_andP; apply: (H α).
      all: do ? by move=> *; apply: (H α).

        by rewrite 2!all_cat => /andP [Hall1 Hall2]; apply_andP; [apply: (H α) | apply: (H0 α)].

    Qed.

    
    Lemma find_all_f_equiv_to_sf_are_simple ty f α (φ : seq (@Query Name Vals)) :
      all (are_equivalent (SingleField f α)) (find_fields_with_response_name f φ) ->
      all (fun q => q.(is_simple_field_selection)) (find_queries_with_label s f ty φ).
    Proof.
      funelim (find_queries_with_label s f ty φ) => //=.

      all: do ?[by simp find_fields_with_response_name; rewrite Heq /= => /andP [Hequiv Hequivs]; apply_andP; apply: (H α)].

      all: do ? by simp find_fields_with_response_name; rewrite Heq /= => *; apply: (H α).

      - by simp find_fields_with_response_name; rewrite 2!all_cat => /andP [Hequiv Hequivs]; apply_andP; [apply: (H α) | apply: (H0 α)].
      - by simp find_fields_with_response_name; rewrite all_cat => /andP [Hequiv Hequivs]; apply: (H α).
        
    Qed.



    Lemma find_queries_subseq_find_fields ty f φ :
      subseq (find_queries_with_label s f ty φ) (find_fields_with_response_name f φ).
    Proof.
      funelim (find_queries_with_label s f ty φ) => //=.
      all: do ?[simp find_fields_with_response_name; rewrite Heq /=; case: ifP => //=; by move/negbT/eqP].

      all: do ? by simp find_fields_with_response_name; rewrite Heq /=.

        by simp find_fields_with_response_name; rewrite cat_subseq.
        simp find_fields_with_response_name.
        rewrite -[find_queries_with_label _ _ _ _]cat0s; rewrite cat_subseq //=.
        apply: sub0seq.
    Qed. 

    
    Lemma find_fields_cat rname φ1 φ2 :
      find_fields_with_response_name rname (φ1 ++ φ2) =
      find_fields_with_response_name rname φ1 ++ find_fields_with_response_name rname φ2.
    Admitted.


    Lemma find_filter_swap f1 f2 ty φ :
      f1 == f2 = false ->
      find_queries_with_label s f1 ty (filter_queries_with_label f2 φ) = (find_queries_with_label s f1 ty φ).
    Proof.
      elim: φ => //=; case=> [f α | l f α | f α β | l f α β | t β] φ IH Hneq; simp filter_queries_with_label; simp find_queries_with_label => /=.
    Admitted.

    Lemma find_absorb f ty φ :
      find_queries_with_label s f ty (find_queries_with_label s f ty φ) = find_queries_with_label s f ty φ.
    Admitted.

     Lemma find_filter_nil rname O__t φ :
      find_queries_with_label s rname O__t (filter_queries_with_label rname φ) = [::].
    Proof.
      funelim (filter_queries_with_label rname φ) => //=; do ? by simp find_queries_with_label; move/negbTE in Heq; rewrite Heq /=.
        by simp find_queries_with_label; case: does_fragment_type_apply => //=; rewrite H H0 /=.
    Qed.
    
  End Find.

  Section Filter.
    Hint Resolve found_queries_leq_size.

    
    Lemma filter_queries_with_label_leq_size l φ :
      queries_size (filter_queries_with_label l φ) <= queries_size φ.
    Proof.
      funelim (filter_queries_with_label l φ) => //=; do ?[simp query_size; ssromega]. 
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
    
    
    Lemma filter_frag (ptys : seq Name) f φ :
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

    (* Lemma filter_preserves_definition rname qs ty : *)
    (*   are_defined qs ty -> *)
    (*   are_defined (filter_queries_with_label rname qs) ty. *)
    (* Proof. *)
    (*   funelim (filter_queries_with_label rname qs) => //=; simp are_defined. *)
    (*   - by move=> /andP [Hdef Hdefs]; apply_andP; [apply: H| apply: H0]. *)
    (*     all: do ? by move=> /andP [Hdef Hdefs]; apply_andP; apply: H. *)
    (*     all: do ? by move=> /andP [Hdef Hdefs]; apply: H. *)
    (* Qed. *)

   

    Lemma filter_map_inline_func (f : Name -> seq (@Query Name Vals) -> seq Query) rname φ ptys :
      filter_queries_with_label rname [seq InlineFragment t (f t φ) | t <- ptys] =
      [seq @InlineFragment Name Vals t (filter_queries_with_label rname (f t φ)) | t <- ptys].
    Proof.
        by elim: ptys => //= t ptys IH; simp filter_queries_with_label; rewrite IH.
    Qed.
    
    Lemma filter_map_inline rname φ ptys :
      filter_queries_with_label rname [seq InlineFragment t φ | t <- ptys] =
      [seq InlineFragment t (filter_queries_with_label rname φ) | t <- ptys].
    Proof.
        by elim: ptys => //= t ptys IH; simp filter_queries_with_label; rewrite IH.
    Qed.

    
    (* Lemma filter_find_nil f ty φ : *)
    (*   filter_queries_with_label f (find_queries_with_label s f ty φ) = [::]. *)
    (* Admitted. *)

    (* Lemma filter_find_swap f1 f2 ty φ : *)
    (*   filter_queries_with_label f1 (find_queries_with_label f2 ty φ) = find_queries_with_label f2 ty (filter_queries_with_label f1 φ). *)
    (* Admitted.  *)

    
  End Filter.

  Section Merging.
    
    Lemma merge_selection_sets_cat (qs1 qs2 : seq (@Query Name Vals)) :
      merge_selection_sets (qs1 ++ qs2) = merge_selection_sets qs1 ++ merge_selection_sets qs2.
    Proof.
        by rewrite /merge_selection_sets map_cat flatten_cat.
    Qed.
    

    Lemma merged_selections_leq φ :
      queries_size (merge_selection_sets φ) <= queries_size φ.
    Proof.
      rewrite /merge_selection_sets.
        by elim: φ => //=; case=> //= *; simp query_size; rewrite ?queries_size_cat; ssromega.
    Qed.

    
    Lemma merge_simple_fields_is_empty φ :
      all (fun query => query.(is_simple_field_selection)) φ ->
      merge_selection_sets φ = [::].
    Proof.
        by elim: φ => //=; case.
    Qed.
    
  End Merging.

End Theory.