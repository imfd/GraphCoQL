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

Section QuerySemantic.

  Variables N Name Vals : ordType.
  
  
  Ltac case_response r := case: r => [l | l v | l vs | l ρ | l ρs].
  Ltac apply_andP := apply/andP; split=> //.
  Ltac apply_and3P := apply/and3P; split=> //.
  
  Variable s : @wfSchema Name Vals.

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
          false .

  Equations? ble (label : Name) (object_type : @NamedType Name) (queries : seq (@Query Name Vals)) (p : Name -> Name -> bool) :
    seq (@Query Name Vals) by wf (queries_size queries) :=
    {
      ble _ _ [::] _ := [::];

      ble k O__t (InlineFragment t φ :: qs) p
        with does_fragment_type_apply O__t t :=
        {
        | true := ble k O__t φ p ++ ble k O__t qs p;
        | _ := ble k O__t qs p
        };

      ble k O__t (SingleField f α :: qs) p
        with p f k :=
        {
        | true := SingleField f α :: ble k O__t qs p;
        | _ := ble k O__t qs p
        };
      
      ble k O__t (LabeledField l f α :: qs) p
        with  p l k :=
        {
        | true := LabeledField l f α :: ble k O__t qs p;
        | _ := ble k O__t qs p
        };

      
      ble k O__t (NestedField f α φ :: qs) p
        with p f k :=
        {
        | true := NestedField f α φ :: ble k O__t qs p;
        | _ := ble k O__t qs p
        };
      
      ble k O__t (NestedLabeledField l f α φ :: qs) p
        with p l k :=
        {
        | true := NestedLabeledField l f α φ  :: ble k O__t qs p;
        | _ := ble k O__t qs p
        }
    }.
  all: do ?simp query_size; ssromega.
  Qed.

  Lemma ble_leq_size l O__t qs p :
    queries_size (ble l O__t qs p) <= queries_size qs.
  Proof.
    funelim (ble _ _ qs _) => //=; simp query_size; rewrite ?queries_size_app; ssromega.
  Qed.
  
  
  Definition find_queries_with_label (label : Name) (object_type : @NamedType Name) (queries : seq (@Query Name Vals)) :=
    ble label object_type queries (fun f label => f == label).


  Lemma found_queries_are_fields k O__t qs :
    all (fun q => q.(is_field)) (find_queries_with_label k O__t qs).
  Proof.
    rewrite /find_queries_with_label.
    funelim (ble k O__t qs (fun f label => f == label)) => //=.
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
    rewrite /find_queries_with_label.
    funelim (ble label O__t qs _) => //=; rewrite ?Heq ?andTb //.
    rewrite all_cat; apply_andP.
  Qed.

  Lemma found_queries_leq_size l O__t qs :
    queries_size (find_queries_with_label l O__t qs) <= queries_size qs.
  Proof.
      by rewrite /find_queries_with_label; apply: ble_leq_size.
  Qed.

  Hint Resolve found_queries_leq_size.
  
   Equations? filter_queries_with_label (label : Name) (queries : seq (@Query Name Vals)) :
    seq (@Query Name Vals) by wf (queries_size queries) :=
    {
      filter_queries_with_label _ [::] := [::];

      filter_queries_with_label l (InlineFragment t φ :: qs) := InlineFragment t (filter_queries_with_label l φ) :: filter_queries_with_label l qs;

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
  
    
  Equations merge_selection_sets : seq (@Query Name Vals) -> seq (@Query Name Vals) :=
    {
      merge_selection_sets [::] := [::];
      merge_selection_sets (q :: qs) := q.(qsubqueries) ++ merge_selection_sets qs
    }.
      
  Lemma merged_selections_lt qs :
    qs != [::] ->
    queries_size (merge_selection_sets qs) < queries_size qs.
  Proof.
    funelim (merge_selection_sets qs) => //=.
    case: q; intros => //=; simp query_size; rewrite ?queries_size_app;
    case: l H => //= hd tl /(_ is_true_true) H; ssromega.
  Qed.

  Lemma merged_selections_leq qs :
    queries_size (merge_selection_sets qs) <= queries_size qs.
  Proof.
    funelim (merge_selection_sets qs) => //=.
    case: q; intros => //=; simp query_size; rewrite ?queries_size_app;
     ssromega.
  Qed.

 
  
  Variable g : @graphQLGraph Name Vals.
  Implicit Type u : @node Name Vals.
  Implicit Type query : @Query Name Vals.

  Transparent query_size.
  
  Equations? execute_selection_set u (queries : seq (@Query Name Vals)) :
    seq (Name * ResponseNode) by wf (queries_size queries) :=
    {
      execute_selection_set _ [::] := [::];
      
      execute_selection_set u (InlineFragment t φ :: qs)
        with does_fragment_type_apply u.(type) t :=
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
        with lookup_field_type s u.(type) f :=
        {
        | Some (ListType ty) => (f, Array [seq Object (execute_selection_set v (φ ++ merge_selection_sets (find_queries_with_label v.(type) f qs))) | v <- neighbours_with_field g u (Field f α)]) :: execute_selection_set u (filter_queries_with_label f qs);
        
        | Some (NT ty)
            with ohead (neighbours_with_field g u (Field f α)) :=
            {
            | Some v => (f, Object (execute_selection_set v (φ ++ merge_selection_sets (find_queries_with_label v.(type) f qs)))) :: execute_selection_set u (filter_queries_with_label f qs);
            
            | _ =>  (f, Leaf Null) :: execute_selection_set u (filter_queries_with_label f qs)
            };

        | None => (f, Leaf Null) :: execute_selection_set u (filter_queries_with_label f qs)
        };

       execute_selection_set u (NestedLabeledField l f α φ :: qs)
        with lookup_field_type s u.(type) f :=
        {
        | Some (ListType ty) => (l, Array [seq Object (execute_selection_set v (φ ++ merge_selection_sets (find_queries_with_label v.(type) l qs))) | v <- neighbours_with_field g u (Field f α)]) :: execute_selection_set u (filter_queries_with_label l qs);
        
        | Some (NT ty)
            with ohead (neighbours_with_field g u (Field f α)) :=
            {
            | Some v => (l, Object (execute_selection_set v (φ ++ merge_selection_sets (find_queries_with_label v.(type) l qs)))) :: execute_selection_set u (filter_queries_with_label l qs);
            
            | _ =>  (l, Leaf Null) :: execute_selection_set u (filter_queries_with_label l qs)
            };

        | None => (l, Leaf Null) :: execute_selection_set u (filter_queries_with_label l qs)
        }

    }.
  all: do ?[by have Hleq := (filter_queries_with_label_leq_size f qs); ssromega].
  all: do ?[by have Hleq := (filter_queries_with_label_leq_size l qs); ssromega].

  all: do ?[by rewrite -/(queries_size φ) queries_size_app;
            have Hleq1 := (found_queries_leq_size v.(type) f qs);
            have Hleq2 := (merged_selections_leq (find_queries_with_label v.(type) f qs)); ssromega].

  all: do ?[by rewrite -/(queries_size φ) queries_size_app;
            have Hleq1 := (found_queries_leq_size v.(type) l qs);
            have Hleq2 := (merged_selections_leq (find_queries_with_label v.(type) l qs)); ssromega].


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
    all (fun kq => kq.1 != l) (execute_selection_set u qs).
  Proof.
    funelim (execute_selection_set u qs) => //=; simp has_response_name => /= /andP [Hne Hall]; do ? apply_andP.

    all: do ?[by apply: H; apply: filter_queries_preserves_non_existent].
    all: do ?[by apply: H0; apply: filter_queries_preserves_non_existent].

    by apply: H; rewrite all_cat; apply_andP; apply/allP/hasPn.
    by apply: H.
  Qed.

  
  Lemma exec_responses_are_non_redundant u qs :
    are_non_redundant (execute_selection_set u qs).
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

    - move=> f ftype α φ qs IH IHqs Hlook; simp is_non_redundant; apply_and3P.
      * rewrite all_map; apply/allP => v Hin /=; simp is_non_redundant.
      * apply: exec_preserves_non_existent_label.
        apply: filtered_queries_hasN_response_name.

    - move=> f α φ qs IH Hlook; simp is_non_redundant; rewrite andTb; apply_andP.
      apply: exec_preserves_non_existent_label.
      apply: filtered_queries_hasN_response_name.

    - move=> f α v ty φ qs IH IHqs Hv Hlook; simp is_non_redundant; apply_and3P.
      apply: exec_preserves_non_existent_label.
      apply: filtered_queries_hasN_response_name.

    - move=> f α ty φ qs IHqs Hv Hlook; simp is_non_redundant; apply_and3P.
      apply: exec_preserves_non_existent_label.
      apply: filtered_queries_hasN_response_name.

    - move=> l ftype f α φ qs IH IHqs Hlook; simp is_non_redundant; apply_and3P.
      * rewrite all_map; apply/allP => v Hin /=; simp is_non_redundant.
      * apply: exec_preserves_non_existent_label.
        apply: filtered_queries_hasN_response_name.

    - move=> l f α φ qs IH Hlook; simp is_non_redundant; rewrite andTb; apply_andP.
      apply: exec_preserves_non_existent_label.
      apply: filtered_queries_hasN_response_name.

    - move=> f α v ty l φ qs IH IHqs Hv Hlook; simp is_non_redundant; apply_and3P.
      apply: exec_preserves_non_existent_label.
      apply: filtered_queries_hasN_response_name.

    - move=> f α ty l φ qs IHqs Hv Hlook; simp is_non_redundant; apply_and3P.
      apply: exec_preserves_non_existent_label.
      apply: filtered_queries_hasN_response_name.
  Qed.

  


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
