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
  
  Definition filter_queries_with_label (label : Name) (object_type : @NamedType Name) (queries : seq (@Query Name Vals)) :=
    ble label object_type queries (fun f label => f != label).
  

  
  Lemma filter_queries_with_label_leq_size l O__t qs :
    queries_size (filter_queries_with_label l O__t qs) <= queries_size qs.
  Proof.
    rewrite /filter_queries_with_label.
      by apply: ble_leq_size.
  Qed.
  
     
  Equations? collect (object_type : @NamedType Name) (queries : seq (@Query Name Vals)) : seq (Name * seq (@Query Name Vals)) by wf (queries_size queries) :=
    {
      collect _ [::] := [::];
      collect O__t (InlineFragment t φ :: qs)
        with does_fragment_type_apply O__t t :=
        {
        | true := collect O__t (φ ++ qs);
        | _ := collect O__t qs
        };

      collect O__t (SingleField f α :: qs) := (f, SingleField f α :: find_queries_with_label f O__t qs) :: collect O__t (filter_queries_with_label f O__t qs);

       collect O__t (LabeledField l f α :: qs) := (l, LabeledField l f α :: find_queries_with_label l O__t qs) :: collect O__t (filter_queries_with_label l O__t qs);

       collect O__t (NestedField f α φ :: qs) := (f, NestedField f α φ :: find_queries_with_label f O__t qs) :: collect O__t (filter_queries_with_label f O__t qs);

       collect O__t (NestedLabeledField l f α φ :: qs) := (l, NestedLabeledField l f α φ :: find_queries_with_label l O__t qs) :: collect O__t (filter_queries_with_label l O__t qs)
       
    }.
  Proof.
    all: do [simp query_size].
    all: do ? [by have Hleq := filter_queries_with_label_leq_size f O__t qs; ssromega].
    all: do ? [by have Hleq := filter_queries_with_label_leq_size l O__t qs; ssromega].
    - by rewrite queries_size_app; ssromega.
    - ssromega.
  Qed.

  Lemma all_fields_in_collect O__t qs :
    all (fun (kqs : Name * seq Query) =>
           let (_, qs) := kqs in
           all (fun q => q.(is_field)) qs) (collect O__t qs).
  Proof.
    funelim (collect _ qs) => //=; simp is_field; rewrite andTb; apply_andP; apply: found_queries_are_fields.
  Qed.

  Lemma all_N_nil_in_collect O__t qs :
    all (fun (kqs : Name * seq Query) => kqs.2 != [::]) (collect O__t qs).
  Proof.
      by funelim (collect _ qs).
  Qed.


  Lemma in_collect_leq O__t kq qs :
    kq \in collect O__t qs ->
           queries_size kq.2 <= queries_size qs.
  Proof.
    funelim (collect O__t qs) => //=.
    case/predU1P => [-> | Hin] /=; have Hleq := (found_queries_leq_size s0 object_type l).
    ssromega.
    have Hleq' := (H kq Hin); simp query_size.
  Admitted.

 
    
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
        | Some (inl value) => (f, Leaf (SingleValue value)) :: execute_selection_set u (filter_queries_with_label u.(type) f qs);
        | Some (inr values) => (f, Array (map (Leaf \o SingleValue) values)) :: execute_selection_set u (filter_queries_with_label u.(type) f qs);
        | None => (f, Leaf Null) :: execute_selection_set u (filter_queries_with_label u.(type) f qs)
        };
      
      execute_selection_set u (LabeledField l f α :: qs)
        with u.(fields) (Field f α) :=
        {
        | Some (inl value) => (l, Leaf (SingleValue value)) :: execute_selection_set u (filter_queries_with_label u.(type) l qs);
        | Some (inr values) => (l, Array (map (Leaf \o SingleValue) values)) :: execute_selection_set u (filter_queries_with_label u.(type) l qs);
        | None => (l, Leaf Null) :: execute_selection_set u (filter_queries_with_label u.(type) l qs)
        };

      
      execute_selection_set u (NestedField f α φ :: qs)
        with lookup_field_type s u.(type) f :=
        {
        | Some (ListType ty) => (f, Array [seq Object (execute_selection_set v (φ ++ merge_selection_sets (find_queries_with_label v.(type) f qs))) | v <- neighbours_with_field g u (Field f α)]) :: execute_selection_set u (filter_queries_with_label u.(type) f qs);
        
        | Some (NT ty)
            with ohead (neighbours_with_field g u (Field f α)) :=
            {
            | Some v => (f, Object (execute_selection_set v (φ ++ merge_selection_sets (find_queries_with_label v.(type) f qs)))) :: execute_selection_set u (filter_queries_with_label u.(type) f qs);
            
            | _ =>  (f, Leaf Null) :: execute_selection_set u (filter_queries_with_label u.(type) f qs)
            };

        | None => (f, Leaf Null) :: execute_selection_set u (filter_queries_with_label u.(type) f qs)
        };


      execute_selection_set u (NestedLabeledField l f α φ :: qs) := [:: (l, Leaf Null)]
    }.
  all: do ?[by have Hleq := (filter_queries_with_label_leq_size u.(type) f qs); ssromega].
  all: do ?[by have Hleq := (filter_queries_with_label_leq_size u.(type) l qs); ssromega].

  all: do ?[by rewrite -/(queries_size φ) queries_size_app;
            have Hleq1 := (found_queries_leq_size v.(type) f qs);
            have Hleq2 := (merged_selections_leq (find_queries_with_label v.(type) f qs)); ssromega].

  all: do [by rewrite -/(queries_size φ) ?queries_size_app; ssromega].
  Qed.


  Lemma 
  
   Fixpoint eval schema graph u query : seq ResponseObject :=
    match query with
    | (SingleField name args) =>
      match u.(fields) (Field name args) with
        | Some (inl value) =>  [:: SingleResult name value]
        | Some (inr values) => [:: ListResult name values]
        | _ => [:: Null name]
      end
        
     | (LabeledField label name args) => 
         match u.(fields) (Field name args) with
         | Some (inl value) =>  [:: SingleResult label value]
         | Some (inr values) => [:: ListResult label values]
         | _ => [:: Null label]
         end
      
     | (NestedField name args ϕ) =>
        let target_nodes := neighbours_with_field graph u (Field name args) in
        match lookup_field_type schema u.(type) name with
        | Some (ListType _) =>
          [:: NestedListResult name [seq collect ( [seq eval schema graph v q | q <- ϕ]) | v <- target_nodes]]
            
        | Some (NT _) =>
          match ohead target_nodes with
          | Some v => [:: NestedResult name (collect ( [seq eval schema graph v q | q <- ϕ]))]
          | _ =>  [:: Null name]
          end
        | _ => [:: Null name]         (* If the field ∉ fields(u) then it's null, right? *)
        end
                                  
     | (NestedLabeledField label name args ϕ) =>
       let target_nodes := neighbours_with_field graph u (Field name args) in
        match lookup_field_type schema u.(type) name with
        | Some (ListType _) =>
          [:: NestedListResult label [seq collect ( [seq eval schema graph v q | q <- ϕ]) | v <- target_nodes]]
            
        | Some (NT _) =>
          match ohead target_nodes with
          | Some v => [:: NestedResult label (collect ( [seq eval schema graph v q | q <- ϕ]))]
          | _ =>  [:: Null label]
          end
        | _ => [:: Null label]         (* If the field ∉ fields(u) then it's null, right? *)
        end
      
     | (InlineFragment t ϕ) => 
        if u.(type) == t then 
          collect ( [seq eval schema graph u q | q <- ϕ])
        else if u.(type) \in implementation schema t then
          collect ( [seq eval schema graph u q | q <- ϕ])
        else if u.(type) \in union_members schema t then
          collect ( [seq eval schema graph u q | q <- ϕ])
        else
          [::]
               
    end.
   
  Proof.
    all: do ?[have Hne : (q :: qs) != [::] by [];
              have Hleq' := (merged_selections_lt (q :: qs) Hne);
              rewrite /q /= in Hleq' *; ssromega].
    all: do ?[ have Hleq' := (in_result_rsize_leq r res Hin2); ssromega].
    - by move/allP: Hflds => /=; simp is_field.
    - have Hne := (all_N_nil_in_collect O__t queries).
        by move/allP: Hne => /(_ kq Hin).
    - have Hflds := (all_fields_in_collect O__t queries).
      move/allP: Hflds => /(_ kq Hin) /=.
      case: kq Hin H => k qs' /= Hin Hqin /allP H.
      exact: H.
    - by apply: (in_collect_leq O__t).
  Qed.
  Next Obligation.
    rewrite /execute_selection_set.
    rewrite /execute_selection_set_unfold.
    elim: queries => //= hd tl IH.
    funelim (collect O__t queries) => //=.
    rewrite -[X in _ = LRTree (map_in X _)]Heqcall.
    
  
  Lemma eval_produces_non_redundant_responses O__T init qs :
    is_non_redundant Labeled (execute_selection_set O__T init qs).
  Proof.
    apply (





  
  Lemma are_non_redundant_cat (rs1 rs2 : seq (@ResponseObject Name Vals)) :
    are_non_redundant__ρ (rs1 ++ rs2) = [&& are_non_redundant__ρ rs1,
                                       are_non_redundant__ρ rs2 &
                                       all (fun r => all (fun r' => r'.(rname) != r.(rname)) rs2) rs1].
  Proof.
    elim: rs1 => //= [| hd tl IH]; first by rewrite andbT.
    rewrite all_cat.
    rewrite IH.
    set A := all _ tl.
    set B := all _ rs2.
    set C := is_non_redundant__ρ hd.
    set D := are_non_redundant__ρ tl.
    rewrite -andbACA.
    rewrite [B && (D && _)]andbCA.
  Admitted.
    
  Lemma are_non_redundant_rcons (rs : seq (@ResponseObject Name Vals)) r :
    are_non_redundant__ρ (rcons rs r) = [&& are_non_redundant__ρ rs,
                                       is_non_redundant__ρ r &
                                       all (fun r' => r.(rname) != r'.(rname)) rs].
    rewrite -cats1.
    rewrite are_non_redundant_cat /= andbT.
  Admitted.
  

    
  (*
  Lemma collect_non_redundant_eq ρ :
    are_non_redundant__ρ ρ ->
    collect ρ = ρ.
  Proof.
      by rewrite /collect; apply: β_non_redundant_nil_eq.
  Qed.
  
  Lemma collect_preserves_non_redundancy ρs :
    are_non_redundant__ρ ρs ->
    are_non_redundant__ρ (collect ρs).
  Proof.
      by move=> Hnr; rewrite collect_non_redundant_eq.
  Qed.
  *)  
(*
  Lemma collect_all_not_eq flt ρ :
    all (fun r => r.(rname) != flt) ρ ->
    collect (γ_filter flt ρ) = collect ρ.
  Proof.
    by move=> Hall; rewrite γ_filter_neq_preserves_list //.
  Qed.
*)


  (*
  Lemma collect_preserves_all_not_eq flt ρ :
    all (fun r => r.(rname) != flt) ρ ->
    all (fun r => r.(rname) != flt) (collect ρ).
  Proof.
    rewrite /collect /=.
    funelim (β ρ) => //= /andP [Hneq Hall]; apply/andP; split=> //.
    all: do ?[by apply: filter_preserves_pred; apply: H].
    all: do ?[by apply: filter_preserves_pred; apply: H0].
  Qed.*)
  

  Lemma non_redundant_rcons (s1 : seq (@ResponseObject Name Vals)) x :
    are_non_redundant__ρ (rcons s1 x) = [&& are_non_redundant__ρ s1,
                                       is_non_redundant__ρ x &
                                       all (fun r => r.(rname) != x.(rname)) s1].
  Proof.
    elim: s1 => //= hd tl IH.
    rewrite all_rcons.
    rewrite eq_sym.
    rewrite IH.
    set A := rname hd != rname x.
    set B := all _ tl.
    set C := all _ tl.
  Admitted.
  
  Lemma collect_are_non_redundant ρs :
    are_non_redundant__ρ (collect ρs).
  Proof.
     Admitted. (* apply (collect_elim
             (fun ρs res =>
                are_non_redundant__ρ res)
             (fun _ acc ρs res =>
                are_non_redundant__ρ acc ->
                are_non_redundant__ρ res)) => //; clear ρs.
    - by intros; apply: H => //; apply/allP.
    - move=> acc l ρs tl IH /hasPn-/allP Hhas Hnr.
      apply: IH.
      rewrite non_redundant_rcons; apply/and3P; split=> //.
    - move=> acc l v ρs tl IH /hasPn-/allP Hhas Hnr.
      apply: IH.
      rewrite non_redundant_rcons; apply/and3P; split=> //.

    - move=> acc l vs ρs tl IH /hasPn-/allP Hhas Hnr.
      apply: IH.
      rewrite non_redundant_rcons; apply/and3P; split=> //.

    - move=> acc l σ ρ tl /= /(_ is_true_true) Hnr IH /hasPn Hhas Hnracc.
      apply: IH.
      rewrite non_redundant_rcons.
      apply/and3P; split=> //.
        by apply/allP=> r Hin /=; apply: Hhas.

    - move=> acc l σs ρ tl /= IH H /hasPn-/allP Hall Hnr.
      apply: H.
      rewrite map_in_eq non_redundant_rcons.
      apply/and3P; split=> //.
      simp is_non_redundant__ρ.
      apply/allP=> r /mapP [x Hin ->].
      by apply: IH.
  Qed.
    
  Hint Resolve collect_are_non_redundant.
  Lemma collect_collect_same (r : seq (@ResponseObject Name Vals)) :
    collect r = collect (collect r).
  Proof.
    rewrite [collect (collect r)]collect_non_redundant_eq //.
  Qed.
 

  Lemma collect_preserves_wf rs :
    wf_responses rs ->
    wf_responses (collect rs).
  Proof.
    by intros; apply: non_redundant_are_wf.
  Qed.

  Lemma collect_preserves_compatible_shapes r rs :
    all (have_compatible_shapes r) rs ->
    all (have_compatible_shapes r) (collect rs).
  Proof.
    
    Admitted.
  
*)

  Hint Resolve collect_are_non_redundant.

  
  Implicit Type schema : @wfSchema Name Vals.
  Implicit Type graph : @graphQLGraph Name Vals.
  Implicit Type u : @node Name Vals.
  Implicit Type query : @Query Name Vals.


  Fixpoint eval schema graph u query : seq ResponseObject :=
    match query with
    | (SingleField name args) =>
      match u.(fields) (Field name args) with
        | Some (inl value) =>  [:: SingleResult name value]
        | Some (inr values) => [:: ListResult name values]
        | _ => [:: Null name]
      end
        
     | (LabeledField label name args) => 
         match u.(fields) (Field name args) with
         | Some (inl value) =>  [:: SingleResult label value]
         | Some (inr values) => [:: ListResult label values]
         | _ => [:: Null label]
         end
      
     | (NestedField name args ϕ) =>
        let target_nodes := neighbours_with_field graph u (Field name args) in
        match lookup_field_type schema u.(type) name with
        | Some (ListType _) =>
          [:: NestedListResult name [seq collect ( [seq eval schema graph v q | q <- ϕ]) | v <- target_nodes]]
            
        | Some (NT _) =>
          match ohead target_nodes with
          | Some v => [:: NestedResult name (collect ( [seq eval schema graph v q | q <- ϕ]))]
          | _ =>  [:: Null name]
          end
        | _ => [:: Null name]         (* If the field ∉ fields(u) then it's null, right? *)
        end
                                  
     | (NestedLabeledField label name args ϕ) =>
       let target_nodes := neighbours_with_field graph u (Field name args) in
        match lookup_field_type schema u.(type) name with
        | Some (ListType _) =>
          [:: NestedListResult label [seq collect ( [seq eval schema graph v q | q <- ϕ]) | v <- target_nodes]]
            
        | Some (NT _) =>
          match ohead target_nodes with
          | Some v => [:: NestedResult label (collect ( [seq eval schema graph v q | q <- ϕ]))]
          | _ =>  [:: Null label]
          end
        | _ => [:: Null label]         (* If the field ∉ fields(u) then it's null, right? *)
        end
      
     | (InlineFragment t ϕ) => 
        if u.(type) == t then 
          collect ( [seq eval schema graph u q | q <- ϕ])
        else if u.(type) \in implementation schema t then
          collect ( [seq eval schema graph u q | q <- ϕ])
        else if u.(type) \in union_members schema t then
          collect ( [seq eval schema graph u q | q <- ϕ])
        else
          [::]
               
    end.

  Definition eval_queries schema g u queries := collect ([seq eval schema g u q | q <- queries]).

  
  Lemma eval_sf schema g u f α :
    let res := eval schema g u (SingleField f α) in
    [\/ exists v, res = [:: SingleResult f v],
       exists vs, res = [:: ListResult f vs] |
     res = [:: Null f]].
  Proof.
    rewrite /eval.
    case: (u.(fields) _) => //=; last by constructor 3.
    by case=> v; [constructor 1 | constructor 2]; exists v.
  Qed.

  Lemma eval_lf schema g u l f α :
    let res := eval schema g u (LabeledField l f α) in
    [\/ exists v, res = [:: SingleResult l v],
       exists vs, res = [:: ListResult l vs] |
     res = [:: Null l]].
  Proof.
    rewrite /eval.
    case: (u.(fields) _) => //=; last by constructor 3.
    by case=> v; [constructor 1 | constructor 2]; exists v.
  Qed.

  Lemma eval_nf schema g u f α φ :
    let res := eval schema g u (NestedField f α φ) in
    [\/ exists v, res = [:: NestedResult f v],
       exists vs, res = [:: NestedListResult f vs] |
     res = [:: Null f]].
  Proof.
    rewrite /eval.
    case: lookup_field_type => //=; last by constructor 3.
    case=> rty; last first.
    by constructor 2; exists [seq eval_queries schema g v φ | v <- neighbours_with_field g u {| label := f; args := α |}].
    case ohead; last by constructor 3.
    by move=> v; constructor 1; exists (eval_queries schema g v φ).
  Qed.

  Lemma eval_nlf schema g u l f α φ :
    let res := eval schema g u (NestedLabeledField l f α φ) in
    [\/ exists v, res = [:: NestedResult l v],
       exists vs, res = [:: NestedListResult l vs] |
     res = [:: Null l]].
  Proof.
    rewrite /eval.
    case: lookup_field_type => //=; last by constructor 3.
    case=> rty; last first.
    by constructor 2; exists [seq eval_queries schema g v φ | v <- neighbours_with_field g u {| label := f; args := α |}].
    case ohead; last by constructor 3.
    by move=> v; constructor 1; exists (eval_queries schema g v φ).
  Qed.

  Lemma eval_inline schema g u t φ :
    let res := eval schema g u (InlineFragment t φ) in
    res = (eval_queries schema g u φ) \/ res = [::].
  Proof.
    rewrite /eval.
    case: eqP=> /=; [by constructor 1|].
    case: in_mem=> /=; [by constructor 1|].
    case: in_mem; [by constructor 1 | by constructor 2].
  Qed.


   Lemma size_leq schema g u qs1 qs2 :
    responses_size (eval_queries schema g u (qs1 ++ qs2)) <= responses_size (eval_queries schema g u qs1) + responses_size (eval_queries schema g u qs2).
  Admitted.

   (*
   Lemma eval_queries_collect_same schema graph u qs :
    eval_queries schema graph u qs = collect (eval_queries schema graph u qs).
   Proof.
   Admitted.
    *)
   Lemma β__Laux_nil_tail rs :
     β__Laux rs [::] = rs.
   Proof.
       by elim: rs.
   Qed.

   
   Lemma β_β_eq (s1 acc : seq (@ResponseObject Name Vals)) :
     are_non_redundant__ρ s1 ->
     all (fun r1 => all (fun r2 => r2.(rname) != r1.(rname)) acc) s1 ->
     β acc s1 = acc ++ s1.
   Proof.
     funelim (β acc s1) => //=; first by rewrite cats0.
     all: do ?[move=> _ /= /andP [Hdiff Halldiff];
               move/hasP: Heq => [r Hin /eqP-/= Heq];
                 by move/allP: Hdiff => /(_ r Hin) /eqP Hcontr; rewrite Heq in Hcontr].
     all: do ?[move=> /and3P [Hallnr Hnr Hnrs] /= /andP [Hdiff Halldiff];
               rewrite -cat_rcons;
               apply: H => //=;
               apply/allP=> r Hin; rewrite all_rcons /=;
               apply_andP;
                 [ by move/allP: Hallnr => /(_ r Hin); rewrite eq_sym
                 | by move/allP: Halldiff => /(_ r Hin)]].
     
     - move=> /and3P [Hallnr Hnr Hnrs] /= /andP [Hdiff Halldiff].
       rewrite -cat_rcons.
       rewrite θ_nil_if_all_neq // ?cats0 in H H0 *.
       rewrite H // ?cat0s in H0 *; last by apply/allP.
       apply: H0 => //=.
       apply/allP=> r Hin; rewrite all_rcons; apply_andP => /=.
         by move/allP: Hallnr => /(_ r Hin); rewrite eq_sym.
         by move/allP: Halldiff => /(_ r Hin).

     - move=> /and3P [Hallnr Hnr Hnrs] /= /andP [Hdiff Halldiff].
       rewrite -cat_rcons.
       rewrite !map_in_eq in H0 *.
   Admitted.
   
   Definition filter__acc (acc rs : seq (@ResponseObject Name Vals)) := filter (fun r1 => all (fun r2 => r2.(rname) != r1.(rname)) acc) rs.

  Lemma filter_acc_cat acc rs1 rs2 :
     filter__acc acc (rs1 ++ rs2) = filter__acc acc rs1 ++ filter__acc acc rs2.
   Proof.
       by rewrite /filter__acc filter_cat.
   Qed.

   Lemma filter_swap {A : eqType} (p1 p2 : A -> bool) (s : seq A) :
     filter p1 (filter p2 s) = filter p2 (filter p1 s).
   Proof.
     elim: s => //= hd tl IH.
     by case Hp2: (p2 hd) => //=; case Hp1: (p1 hd) => //=; rewrite Hp2 // IH.
   Qed.

   Lemma filter_acc_swap acc1 acc2 rs :
     filter__acc acc1 (filter__acc acc2 rs) = filter__acc acc2 (filter__acc acc1 rs).
   Proof.
       by rewrite /filter__acc filter_swap.
   Qed.

   Lemma filter_acc_rcons acc x rs :
     filter__acc (rcons acc x) rs = filter__acc [:: x] (filter__acc acc rs).
   Proof.
     rewrite -cats1.
     elim: rs => //= hd tl IH.
     case: ifP; rewrite all_cat.
     - by move=> /andP [Hacc /= Hx]; rewrite Hacc /= Hx IH.
     - move/negbT/nandP=> [/negbTE Hacc | /negbTE-/= Hx].
       rewrite Hacc; apply: IH.
       case: ifP => Hacc /=; last by apply: IH.
       rewrite Hx; apply: IH.
   Qed.
   
   Lemma filter_acc_responses_size_leq acc rs :
     responses_size (filter__acc acc rs) <= responses_size rs.
   Admitted.

   Lemma θ_eq_with_filter l acc rs :
     all (fun r => r.(rname) != l) acc ->
     θ l (filter__acc acc rs) = θ l rs.
   Proof.
     move=> Hall.
     elim: rs l acc Hall => //= hd tl IH l acc Hall.
     case: ifP => //; case: hd => [l' | l' v | l' vs | l' ρ | l' ρs] Hacc /=; do ? by apply: IH.
     case: eqP => //= Heq; by rewrite IH.
     case: eqP => //= Heq; last by apply: IH.
     move/allPn: Hacc => [r Hin /negbTE-/= Hneq].
     move/allP: Hall => /(_ r Hin).
     by rewrite Heq Hneq.
   Qed.

   Lemma responses_size0nil (rs : seq (@ResponseObject Name Vals)) :
     responses_size rs = 0 -> rs = [::].
   Proof.
     elim: rs => //= hd tl IH; case: hd; intros; inversion H.
   Qed.

   
   Lemma β_spread acc rs :
     β acc rs = acc ++ β [::] (filter__acc acc rs).
   Proof.
     move: {2}(responses_size _) (leqnn (responses_size rs)) => n.
     elim: n rs acc => //= [| n IH] rs acc.
     - by rewrite leqn0 => /eqP-/responses_size0nil -> /=; simp β; rewrite cats0.
     - case: rs => //= [| hd tl] Hleq.
       * by simp β; rewrite cats0.
       * case: ifP => //= /allP-/hasPn Hhas; last first.
           by case: hd Hleq Hhas; intros; simp response_size in Hleq; simp β; rewrite Hhas /=; apply: IH; ssromega.
           
       move/negbTE in Hhas.
       case: hd Hleq Hhas; intros; simp response_size in Hleq; simp β; rewrite Hhas /=;
       rewrite [X in _ = acc ++ X]IH //= ?cat_rcons; do ? [by move: (filter_acc_responses_size_leq acc tl) => Hfleq; ssromega].
       
       all: do ?[rewrite IH; do ? ssromega; rewrite filter_acc_rcons -cat_rcons] => //.
       rewrite θ_eq_with_filter //.
         by move/hasPn/allP: Hhas.

       rewrite ?map_in_eq.
   Admitted.

   Lemma filter_β_eq acc rs :
     filter__acc acc (β [::] (filter__acc acc rs)) = β [::] (filter__acc acc rs).
   Proof.
   Admitted.

 

   Lemma filter_acc_nested acc1 acc2 rs :
     filter__acc acc1 (filter__acc acc2 rs) = filter__acc acc1 (filter__acc (filter__acc acc1 acc2) rs).
   Admitted.

   (* Lemma filter_acc_β_nil acc1 acc2 rs :
     filter__acc acc (β [::] rs) = β [::] (filter__acc acc rs).
   Proof.
     move: {2}(responses_size _) (leqnn (responses_size rs)) => n.
     elim: n rs acc => //= [| n IH] rs acc.
     - by rewrite leqn0 => /eqP-/responses_size0nil -> /=; simp β. 
     - case: rs => //= hd tl Hleq.
       case: ifP => //=; case: hd Hleq; intros; simp response_size in Hleq; simp β => /=.
       
       * by simp β; rewrite cats0. *)
   
         
   Lemma filter_acc_β_nil acc rs :
     filter__acc acc (β [::] rs) = β [::] (filter__acc acc rs).
   Proof.
     move: {2}(responses_size _) (leqnn (responses_size rs)) => n.
     elim: n rs acc => //= [| n IH] rs acc.
     - by rewrite leqn0 => /eqP-/responses_size0nil -> /=; simp β. 
     - case: rs => //= hd tl Hleq.
       case: ifP => //=; case: hd Hleq; intros; simp response_size in Hleq; simp β => /=.
       
     
     
   Admitted.

   Lemma filter_acc_nil rs :
     filter__acc [::] rs = rs.
   Admitted.



   Lemma filter_responses_size_leq p (rs : seq (@ResponseObject Name Vals)) :
     responses_size [seq r <- rs | p r] <= responses_size rs.
   Proof.
     elim: rs => //= hd tl IH.
     case: ifP => //= _; ssromega.
   Qed.
   
   Lemma β_preserves_all_neq l rs :
     all (fun r => r.(rname) != l) rs ->
     all (fun r => r.(rname) != l) (β [::] rs).
   Proof.
     move: {2}(responses_size _) (leqnn (responses_size rs)) => n.
     elim: n rs => //= [| n IH] rs.
     - by rewrite leqn0 => /eqP-/responses_size0nil -> /=; simp β; rewrite cat0s.
     - case: rs => //= hd tl Hleq /andP [Heq Hall].
       case: hd Hleq Heq; intros; simp response_size in Hleq; simp β => /=; rewrite β_spread all_cat /= Heq ?andTb; apply: IH.
       all: do ?rewrite /filter__acc /=.
       all: do ?[move: (filter_responses_size_leq (fun r => (s != rname r) && true) tl ) => Hfleq; ssromega].
       all: do ?[rewrite /filter__acc /=;
                 apply/allP=> r; rewrite mem_filter andbT => /andP [_ Hin];
                   by move/allP: Hall => /(_ r Hin)].
   Qed.

   Lemma filter_acc_id acc rs :
     filter__acc acc (filter__acc acc rs) = filter__acc acc rs.
   Proof.
       by rewrite /filter__acc filter_id.
   Qed.

   (*
   Lemma β_nested_cat acc rs1 rs2 :
     β acc (β [::] rs1 ++ rs2) = β acc (rs1 ++ rs2).
   Proof.
     move: {2}(responses_size _) (leqnn (responses_size rs1)) => n.
     elim: n rs1 rs2 acc => [| n IH] rs1 rs2 acc.
     - by rewrite leqn0 => /eqP-/responses_size0nil -> /=; simp β; rewrite cat0s.
     - case: rs1 => //= r1 rs1' Hleq.
       case: r1 Hleq => [l | l v | l vs | l ρ | l ρs]; simp response_size => Hleq;
       rewrite β_spread [RHS]β_spread;
       rewrite -cat_cons 2!filter_acc_cat filter_acc_β_nil /=;
       set rs2' := filter__acc acc rs2;
       case: ifP => //= Hall.

       all: do ?[rewrite IH //; move: (filter_acc_responses_size_leq acc rs1') => Hfleq; ssromega].
      
       * simp β => /=; rewrite [β [:: Null l] _]β_spread [β [:: Null l] _ in RHS]β_spread /=.
         simp β => /=; rewrite [β [:: Null l] _]β_spread /= 2!filter_acc_cat.
         rewrite filter_acc_β_nil filter_acc_id -?filter_acc_rcons IH //=.
         move: (filter_acc_responses_size_leq (rcons acc (Null l)) rs1') => Hfleq; ssromega.
         
       * simp β => /=; rewrite [β [:: SingleResult l v] _]β_spread [β [:: SingleResult l v] _ in RHS]β_spread /=.
         simp β => /=; rewrite [β [:: SingleResult l v] _]β_spread /= 2!filter_acc_cat.
         rewrite filter_acc_β_nil filter_acc_id -?filter_acc_rcons IH //=.
         move: (filter_acc_responses_size_leq (rcons acc (SingleResult l v)) rs1') => Hfleq; ssromega.

       * admit.

       * simp β => /=; rewrite θ_cat catA; congr cat.
         set ρ' := β [::] (ρ ++ _).
         set σ := β [::] ((ρ ++ _) ++ _).
         rewrite [β [:: NestedResult _ _] _]β_spread [β [:: NestedResult _ _] _ in RHS]β_spread /=.
         simp β => /=; rewrite [β [:: NestedResult _ _] _]β_spread /= 2!filter_acc_cat.
         rewrite filter_acc_β_nil filter_acc_id θ_cat θ_nil_if_all_neq ?cat0s.
         have -> : β [::] (ρ' ++ θ l rs2') = σ.
         apply: IH;          rewrite responses_size_app.

          move: (θ_responses_size_leq l (filter__acc acc rs1')) => Htleq.
          move: (filter_acc_responses_size_leq acc rs1') => Hfleq; ssromega.
          set rs2'' := filter__acc _ rs2'.
          rewrite IH //.
          rewrite -filter_acc_rcons.
          move: (filter_acc_responses_size_leq (rcons acc (NestedResult l σ)) rs1') => Hfleq; ssromega.

          apply: β_preserves_all_neq.
          rewrite /filter__acc /=.
            by apply/allP=> r; rewrite mem_filter andbT eq_sym => /andP [H].

       * congr cat.
         set filter1 := filter__acc _ rs1'.
         simp β => /=; rewrite ?map_in_eq.
         set ρs' := [seq β [::] i | i <- _].
         set σ := [seq β [::] i | i <- _].
         set r1' := NestedListResult l _.
         set r1'' := NestedListResult l _.
         rewrite [β [:: r1'] _]β_spread [β [:: r1''] _]β_spread /=.
         rewrite filter_acc_cat -?filter_acc_rcons.
         simp β => /=; rewrite ?map_in_eq.
         have -> : [seq β [::] i | i <- γ l ρs' (β [::] (filter__acc (rcons acc r1') rs1') ++ rs2')] = σ.
         rewrite {}/r1'' {}/σ.
         elim: rs2' => //.
         
         have Heq : γ l ρs' (β [::] ((filter__acc (rcons acc r1') rs1') ++ rs2')) = γ l ρs (filter1 ++ rs2').
         rewrite {1}/γ.
         rewrite foldl_cat.
         
         simp β.
         
       *)
       
       
        
   (*
  Lemma collect_eval schema g u qs1 qs2 :
    collect (eval_queries schema g u qs1 ++ eval_queries schema g u qs2) =
    eval_queries schema g u (qs1 ++ qs2).
  Proof.
    rewrite /collect.
    move: {2}(responses_size _)
             (leqnn (responses_size (eval_queries schema g u qs1))) => n.
    elim: n qs1 qs2 => [| n IH] qs1 qs2.
    admit.
    case: qs1 => //= [| hd tl].
    rewrite β_β_eq //. admit. by apply/allP.
    rewrite /collect => Hleq.
    rewrite -IH.
    * case: hd Hleq => [f α | l f α | f α φ | l f α φ | t φ]; last first.
      move: (eval_inline schema g u t φ) => [-> | ->] /= Hleq.
      
      move: (eval_sf schema g u f α) => /= [[v ->] | [vs ->] | ->] /= Hleq.
      rewrite /collect. simp β => /=.
      rewrite -IH.
        rewrite !β_β_eq //.
        admit.
        by apply/allP.
        rewrite cat0s. admit.
        admit.
        by apply/allP.
        rewrite cat0s.
        rewrite all_cat; apply_andP => /=.
  Abort.

  
  Lemma eval_query_same_response_name schema g u q (H : forall t φ, q <> InlineFragment t φ) :
    forall r, r \in (eval schema g u q) ->
               r.(rname) = (qresponse_name q H).
  Proof.
    case: q H => //= [f α | l f α | f α φ | l f α φ | t φ] H r; simp eval.
    - case: (u.(fields) _) => //=.
      by case=> [v | vs] => //=; rewrite mem_seq1 => /eqP -> /=; simp qresponse_name.
        by rewrite mem_seq1 => /eqP ->; simp qresponse_name.
    - case: (u.(fields) _) => //=.
      by case=> [v | vs] => //=; rewrite mem_seq1 => /eqP -> /=; simp qresponse_name.
      by rewrite mem_seq1 => /eqP ->; simp qresponse_name.
    - case lookup_field_type => //= [rty|].
      case: rty => rty.
      by case: ohead => [v |]; rewrite mem_seq1 => /eqP ->; simp qresponse_name.
      by rewrite mem_seq1 => /eqP ->; simp qresponse_name.
      by rewrite mem_seq1 => /eqP ->; simp qresponse_name.
    - case lookup_field_type => //= [rty|].
      case: rty => rty.
      by case: ohead => [v |]; rewrite mem_seq1 => /eqP ->; simp qresponse_name.
      by rewrite mem_seq1 => /eqP ->; simp qresponse_name.
        by rewrite mem_seq1 => /eqP ->; simp qresponse_name.

    - by move: (H t φ).
  Qed.

  Lemma eval_queries_diff_response_name schema g u q1 q2
        (H1 : forall t φ, q1 <> InlineFragment t φ)
        (H2 : forall t φ, q2 <> InlineFragment t φ):
    (qresponse_name q1 H1) != (qresponse_name q2 H2) ->
    forall r1, r1 \in (eval schema g u q1) ->
    forall r2, r2 \in (eval schema g u q2) ->     
                 r1.(rname) != r2.(rname).
    move=> Hneq r Hin r2 Hin2.
    move: (eval_query_same_response_name _ _ _ q1 H1 r Hin) (eval_query_same_response_name _ _ _ q2 H2 r2 Hin2) => Hreq1 Hreq2.
    case: q1 H1 Hneq Hreq1 Hin => //= [f α | l f α | f α φ | l f α φ | t φ] H1; simp qresponse_name => Hneq ->; last by move: (H1 t φ).
    
    all: do ?[by case: q2 H2 Hneq Hreq2 Hin2 => //= [f' α' | l' f' α' | f' α' χ | l' f' α' χ | t' χ] H2; simp qresponse_name => Hneq -> _ _].
  Qed.
  
    *)
   
  Lemma eval_non_redundant schema g u φ :
    are_non_redundant__ρ (eval schema g u φ).
  Proof.
    elim φ using Query_ind with
        (Pl := fun qs =>
                forall v,
                  are_non_redundant__ρ (eval_queries schema g v qs)).
    - by move=> f α; move: (eval_sf schema g u f α) => [[v ->] | [vs ->] | ->].
    - by move=> l f α; move: (eval_lf schema g u l f α) => [[v ->] | [vs ->] | ->].
    
    - intros; rewrite /eval.
      case Hlook: lookup_field_type => [rty|] //.
      case: rty Hlook => //= ty Hlook.
      case: ohead => [fld|] //=; rewrite andbT; simp is_non_redundant__ρ; apply: H => //; exact: (NT ty).
      rewrite andbT; simp is_non_redundant__ρ.
      apply/allP => x /mapP [r Hin ->]; apply: H; exact: ty.

    - intros; rewrite /eval.
      case Hlook: lookup_field_type => [rty|] //.
      case: rty Hlook => //= ty Hlook.
      case: ohead => [fld|] //=; rewrite andbT; simp is_non_redundant__ρ; apply: H => //; exact: (NT ty).
      rewrite andbT; simp is_non_redundant__ρ.
      apply/allP => x /mapP [r Hin ->]; apply: H; exact: ty.

    - intros; rewrite /eval; case: ifP => //= _.
      case: ifP => // _.
        by case: ifP.

    - by rewrite /eval_queries /= /collect; simp β.
    - move=> hd IH tl IHtl v.
      rewrite /eval_queries /=.
  Admitted.
  
  Lemma eval_queries_are_non_redundant schema g u φ :
    are_non_redundant__ρ (eval_queries schema g u φ).
  Proof.
    rewrite /eval_queries.
    by apply: collect_are_non_redundant.
  Qed.

  Hint Resolve eval_non_redundant eval_queries_are_non_redundant.

  
  Lemma eval_queries_response_are_wf schema g u qs :
    wf_responses (eval_queries schema g u qs).
  Proof.
    by apply: non_redundant_are_wf.
  Qed.

  Lemma eval_query_responses_are_wf schema g u q :
    wf_responses (eval schema g u q).
  Proof.
      by apply: non_redundant_are_wf.
  Qed.

 

 




(*
    
  Lemma qweqw schema g u ty q1 q2 :
    is_field_merging_possible schema q1 ty q2 ty ->
    all (fun r1 => all (fun r2 => have_compatible_shapes r1 r2) (eval schema g u q2)) (eval schema g u q1).
  Proof.
    case: q1 => [f α | l f α | f α φ | l f α φ | t φ].
    case: q2 => [f' α' | l' f' α' | f' α' χ | l' f' α' χ | t' χ]; simp is_field_merging_possible; simp qname.
    case Hlook1: lookup_field_type => [rty1|] //=; simp qresponse_name;
                                       case Hlook2: lookup_field_type => [rty2|] //=; simp qargs; simp qresponse_name.
    
  Admitted.
 
  Lemma asdfasfd schema g u ty q s :
    all ((is_field_merging_possible schema q ty) ^~ ty) s ->
    all (fun r1 => all (fun r2 => have_compatible_shapes r1 r2) (eval_queries schema g u s)) (eval schema g u q).
  Proof.
    elim: s => // [| hd tl IH].
    - by move=> _; apply/allP.
    - move=> /= /andP [Hmerge Hall].
      apply/allP => r Hin.
      apply/allP => r2 Hin2.
      
  Admitted.
      
  Lemma eval_two_merging_queries_are_wf schema g u ty q1 q2 :
    is_field_merging_possible schema q1 ty q2 ty ->
    wf_responses ((eval schema g u q1) ++ (eval schema g u q2)).
  Proof.
    case: q1 => [f α | l f α | f α φ | l f α φ | t φ].
    case: q2 => [f' α' | l' f' α' | f' α' χ | l' f' α' χ | t' χ]; simp is_field_merging_possible; simp qname.

    all: do ?[case Hlook1: lookup_field_type => [rty1|] //=; simp qresponse_name;
              case Hlook2: lookup_field_type => [rty2|] //=; simp qargs; simp qresponse_name;
              case Hfeq: (f == f') => //= /andP [Hshape]; rewrite ?eqxx /=].
    
    all: do ?[by move/andP=> [/eqP Hargs Hall]; move/eqP in Hfeq; rewrite Hfeq Hargs wf_responses_cat_same //;
              apply: eval_query_responses_are_wf].
    all: do ?[move=> _;
              rewrite wf_responses_cat_neq;
              [by apply/andP; split=> //; apply: eval_query_responses_are_wf 
              | move/negbT in Hfeq;
                have Hninl1 : forall t φ, (SingleField f α) <> InlineFragment t φ by [];
               have Hninl2 : forall t φ, (SingleField f' α') <> InlineFragment t φ by [];
               apply/allP => r1 Hin1; apply/allP=> r2 Hin2;
               move: (eval_queries_diff_response_name schema g u (SingleField f α) (SingleField f' α') Hninl1 Hninl2 Hfeq);
                 by move/(_ r1 Hin1 r2 Hin2) => H; rewrite /negb ifN_eqC]].

    case Hleq: (f == l') => //=.
    move/andP=> [/eqP Hargs Hall].
    move/eqP in Hfeq; rewrite Hfeq Hargs.
    simp eval. case : (u.(fields) _) => //=.
    case=> //=.

    move=> _; rewrite wf_responses_cat_neq;
             [by apply/andP; split=> //; apply: eval_query_responses_are_wf 
              | move/negbT in Hleq;
                have Hninl1 : forall t φ, (SingleField f α) <> InlineFragment t φ by [];
               have Hninl2 : forall t φ, (LabeledField l' f' α') <> InlineFragment t φ by [];
               apply/allP => r1 Hin1; apply/allP=> r2 Hin2;
               move: (eval_queries_diff_response_name schema g u (SingleField f α) (LabeledField l' f' α') Hninl1 Hninl2 Hleq);
                 by move/(_ r1 Hin1 r2 Hin2) => H; rewrite /negb ifN_eqC].
    
    all: do ?[rewrite implybF].

    admit. 
    move: Hshape; simp have_compatible_response_shapes; simp qresponse_name.
    rewrite Hfeq /= Hlook1 Hlook2.
    (* Missing info on query conformance *)
  Admitted.

  Lemma eval_merging_queries_are_wf schema g u ty q1 qs :
    all ((is_field_merging_possible schema q1 ty) ^~ ty) qs ->
    wf_responses ((eval schema g u q1) ++ (eval_queries schema g u qs)).
  Proof.
    elim: qs => //= [_| hd tl IH].
    - rewrite cats0; apply: eval_query_responses_are_wf.
    - move/andP=> [Hmerge Hall].
  Abort.
    *)

  (*
  Lemma eval_collect_same :
    forall schema graph u query,
      eval schema graph u query = collect (eval schema graph u query).
  Proof.
    by intros; rewrite collect_non_redundant_eq.
  Qed.
 

  
  Lemma eval_same_query_in_list schema graph u query :
    eval schema graph u query = eval_queries schema graph u [:: query].
  Proof.
    rewrite /eval_queries /=
    rewrite /eval_queries /= cats0.
      by apply: eval_collect_same.
  Qed.
  
  Lemma eval_query_inline schema (g : conformedGraph schema) qs :
    eval schema g g.(root) (InlineFragment schema.(query_type) qs) = eval_queries schema g g.(root) qs.
  Proof.
    rewrite /eval.
    move: (root_query_type  g) => -> /=.
    by case: eqP.
  Qed.

*)
    
  (*
  Lemma collect_collect_2_cat :
    forall n s1 s2,
      n >= responses_size s1 ->
      collect (collect s1 ++ s2) = collect (s1 ++ s2).
  Proof.
    
    elim=> // [| n IH].
    - case=> //= r tl s2.
      rewrite leqn0 addn_eq0 => /andP [/eqP Hcontr _].
      move: (response_size_n_0 r); rewrite lt0n => /eqP.
        by rewrite Hcontr.
        
    - case => //= hd tl s2 Hlt.
      case: hd Hlt => [l | l v | l vs | l ρ | l ρs].
      simp response_size => Hleq. simp collect.
      rewrite cat0s /=.
      rewrite -/collect_equation_1.
      
      all: do ?[simp response_size => /= Hlt; simp collect;
                rewrite -/cat !γ_filter_cat /= (γ_collect_γ (size tl) l tl) // IH //;
                move: (γ_responses_size_reduced l tl) => Hltg; ssromega].

      * move=> Hlt; simp collect; rewrite -/cat.
        rewrite β_filter_cat.
        rewrite (β_filter_nil l (collect _)) ?cat0s.
        rewrite IH.
        rewrite -catA -β_filter_cat.
        congr cons.
        rewrite !γ_filter_cat.
        rewrite (γ_collect_γ (size tl) l tl) //.
        rewrite IH //.
        move: (γ_responses_size_reduced l tl) => Hlt'.
        move: Hlt; simp response_size => /= Hlt; ssromega.
        rewrite responses_size_app.
        move: Hlt; simp response_size => /= Hlt.        
        move: (β_responses_size_reduced l tl) => Hlt'; ssromega.

        by apply: collect_preserves_all_not_eq; apply: γ_filter_all.

      * move=> Hlt; simp collect; rewrite -/cat !γ_filter_cat.
        rewrite (γ_collect_γ (size tl) l) //.
        
        rewrite IH.
        congr cons. congr NestedListResult.
        rewrite /indexed_map.
        rewrite indexed_map_In_β.
        rewrite indexed_map_In_nested_map.
        have H : forall n,
            indexed_map_In ρs
               (fun i r _ =>
                  collect (collect (r ++ indexed_β_filter l tl i) ++ indexed_β_filter l s2 i)) n =
            indexed_map_In ρs
               (fun i r _ =>
                  collect (r ++ indexed_β_filter l (tl ++ s2) i)) n.
        elim: ρs Hlt => //= hd' tl' IH' Hlt n'.
        simp indexed_map_In.
        rewrite IH.
        rewrite -catA indexed_β_cat.
        congr cons; apply: IH'.
        move: Hlt; simp response_size => /= Hlt. ssromega.
        move: Hlt; simp response_size => /= Hlt.
        move: (indexed_β_size_reduced l tl n') => Hltb.
        rewrite responses_size_app. ssromega.
        by rewrite H.
       
        move: (γ_responses_size_reduced l tl) => Hltg.
        move: Hlt; simp response_size => /= Hlt. ssromega.
          all: do ?[by rewrite /partial_response_eq].    
  Qed.

  Lemma collect_size_leq s :
    size (collect s) <= size s.
  Proof.
    apply_funelim (collect s) => //= [l | l v | l vs | l ρ | l ρs] tl.
    all: do ?[by move: (γ_size_le l tl) => Hlt Hleq; ssromega].
    all: do ?[by move: (γ_size_le l tl) => Hlt IH Hleq; ssromega].
  Qed.

  
  Hint Resolve responses_size_γ_leq.
  Lemma collect_collect_cat_tail s1 s2 :
    wf_responses (s1 ++ s2) ->
    collect (s1 ++ collect s2) = collect (s1 ++ s2).
  Proof.
    move: {2}(responses_size _) (leqnn (responses_size s1)) => n.
    elim: n s1 s2 => [| n IH].
    - case=> [| hd tl] s2 /= Hlt Hcomp.
      * by rewrite -collect_collect_same.
      * move: Hlt; rewrite leqn0 addn_eq0 => /andP [/eqP Hcontr _].
        move: (response_size_n_0 hd); rewrite lt0n => /eqP.
        by rewrite Hcontr.
    - case=> [| hd tl] s2 /= Hlt.
      * by rewrite -collect_collect_same.
      * case: hd Hlt => [l | l v | l vs | l ρ | l ρs]; simp response_size => Hlt;
        have Htllt : responses_size tl < n by ssromega.   

        all: do ?[by move/and3P=> [_ Hall Hwf]; simp collect => /=; congr cons;
                  rewrite 2!γ_filter_cat γ_collect; apply: IH;[ by apply: responses_size_γ_leq
                                                              | rewrite -γ_filter_cat; apply: γ_filter_preserves_wf]].
        
        
        move/and3P=> [Hwf Hall Hwfs]; simp collect => /=; congr cons; last first.
        by rewrite 2!γ_filter_cat γ_collect; apply: IH;  [ apply: responses_size_γ_leq
                                                         | rewrite -γ_filter_cat; apply: γ_filter_preserves_wf].
             
        congr NestedResult.
        rewrite 2!β_filter_cat 2!catA.
        rewrite β_collect_swap //.
        apply: IH.
        by rewrite responses_size_app; move: (β_responses_size_reduced l tl) => Hbleq; ssromega.
        rewrite -catA -β_filter_cat.
        by apply: (β_filter_preserves_wf l ρ).
        by case: (wf_responses_cat Hwfs).


        move/and3P=> [Hwf Hall Hwfs]; simp collect => /=; congr cons; last first.
        by rewrite 2!γ_filter_cat γ_collect; apply: IH;  [ apply: responses_size_γ_leq
                                                         | rewrite -γ_filter_cat; apply: γ_filter_preserves_wf].
      
        congr NestedListResult.
        rewrite /indexed_map.  
        have H : forall n,
            indexed_map_In ρs
              (fun i r _ =>
                 collect (r ++ indexed_β_filter l (tl ++ collect s2) i)) n =
            indexed_map_In ρs
              (fun i r _ =>
                 collect (r ++ indexed_β_filter l (tl ++ s2) i)) n.
        
  Admitted.



  



      
  Lemma eval_collect_cat schema g u s1 s2 :
    wf_responses (eval_queries schema g u s1 ++ eval_queries schema g u s2) ->
    eval_queries schema g u (s1 ++ s2) =
    collect (eval_queries schema g u s1 ++ eval_queries schema g u s2).
  Proof.
    elim: s1 s2 => [ /= | hd tl IH] s2 Hwf.
    - by apply: eval_queries_collect_same.
    - rewrite {2}/eval_queries -/eval_queries cat_cons /= IH.
      rewrite (collect_collect_2_cat (responses_size (eval schema g u hd ++ eval_queries schema g u tl)) _ _) // -catA.

      rewrite (collect_collect_cat_tail) //.
      
      simpl in Hwf.
  Admitted.

      
  Lemma collect_eval_cat schema g u s1 s2 :
    collect (eval_queries schema g u s1 ++ eval_queries schema g u s2) =
    eval_queries schema g u (s1 ++ s2).
  Proof.
    elim: s2 s1 => //= [| hd tl IH] s1.
    - by rewrite !cats0 -eval_queries_collect_same.

    - elim: s1 => //= [ | hd' tl' IH'].
        by rewrite [collect(collect _)]collect_non_redundant_eq //.
        
      
  Admitted.
   *)

  
  Lemma implementation_nil_for_object schema ty :
    is_object_type schema ty ->
    implementation schema ty = fset0.
  Proof.
    funelim (is_object_type schema ty) => //= _.
    rewrite /implementation.
  Admitted.

  Lemma union_nil_for_object schema ty :
    is_object_type schema ty ->
    union_members schema ty = fset0.
  Admitted.
    

  (*
  Lemma inline_nested_empty schema (g : @conformedGraph Name Vals schema) :
    forall t1 t2 ϕ,
      is_object_type schema t1 ->
      is_object_type schema t2 ->
      t1 <> t2 ->
      eval schema g g.(root) (InlineFragment t1 [:: (InlineFragment t2 ϕ)]) = [::].
  Proof.
    move=> t1 t2 ϕ Hobj Hobj' /eqP /negbTE Hneq /=.
    move: (query_has_object_type schema).
    move: (root_query_type g) => <- Hscope.
    simp eval.
    case: eqP => //= Heq; [simp eval; rewrite Heq Hneq /=|];
    rewrite implementation_nil_for_object //=;
    rewrite union_nil_for_object //=.
  Qed.
  

  Lemma inline_query_preserves schema (g : @conformedGraph Name Vals schema):
    forall ϕ u,
      u \in nodes g.(graph) ->
      eval schema g u ϕ = eval schema g u (InlineFragment u.(type) [:: ϕ]).
  Proof.
    move=> ϕ u Hin; case: g Hin.
    move=> g Hr He Hf Hn /= Hin.
    rewrite /nodes_have_object_type in Hn.
    move/seq.allP /(_ u Hin): Hn.
    case: u Hin => ty flds Hin. rewrite /type. funelim (is_object_type schema ty) => //.
    move=> _.
    Admitted.

  Lemma asf schema (g : @conformedGraph Name Vals schema)  u type_in_scope ti ϕ :
     query_conforms schema type_in_scope (InlineFragment ti ϕ) ->
     type_in_scope \in implementation schema ti ->
            eval schema g u (InlineFragment ti ϕ) = eval schema g u (InlineFragment type_in_scope ϕ). 
  Proof.
    move=> Hqc Himpl.
    move: (has_implementation_is_interface Himpl) => Hint.
    rewrite !eval_equation_5.
    funelim (is_interface_type schema ti) => //.
    
    Abort.
  (* Missing info on node -> type of node should be same as the one in scope *)
  

  
  

  Lemma nf_queries_eq schema (g : @conformedGraph Name Vals schema) u n α ϕ ϕ' :
    (forall v, eval_queries schema g v ϕ = eval_queries schema g v ϕ') ->
    eval schema g u (NestedField n α ϕ) = eval schema g u (NestedField n α ϕ').
  Proof.
    move=> Hqs.
    do 2 rewrite eval_equation_3.
    case lookup_field_type => //=.
    case=> [nt | lt].
    case neighbours_with_field => // v1 vn /=.
      by rewrite Hqs.
    case neighbours_with_field => // v1 vn /=.
    congr cons.
    congr NestedListResult.
    rewrite Hqs.
    congr cons.
  Admitted.

  
    
    *)
      
End QuerySemantic.

Arguments β [Name Vals].
Arguments collect [Name Vals].
Arguments eval [Name Vals].
Arguments eval_queries [Name Vals].
