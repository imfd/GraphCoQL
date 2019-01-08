From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


From extructures Require Import ord fmap.

Require Import List.

Require Import Query.
Require Import QueryAux.
Require Import SchemaWellFormedness.

Require Import Schema.
Require Import SchemaAux.

Require Import CpdtTactics.

Section NRGTNF.

  Variables Name Vals : ordType.
  
  Implicit Type query_set : @QuerySet Name Vals.
  Implicit Type query : @Query Name Vals.

    

  Definition is_field_query query : bool :=
    if query is InlineFragment _ _ then false else true.

  Definition is_inline_fragment query : bool :=
    if query is InlineFragment _ _ then true else false.

  
  Inductive GroundTypedNormalForm : QuerySet -> Prop :=
  | GT_SingleQuery : forall query,
      qGroundTypedNormalForm query ->
      GroundTypedNormalForm (SingleQuery query)
                            
  | GT_MultipleSelection : forall (q : Query) (q' : QuerySet),
      ((all is_field_query (SelectionSet q q')) || (all is_inline_fragment (SelectionSet q q'))) ->
      qGroundTypedNormalForm q ->
      GroundTypedNormalForm q' ->
      GroundTypedNormalForm (SelectionSet q q')
                            
  with qGroundTypedNormalForm : Query -> Prop :=
       | GT_Field : forall f args,
           qGroundTypedNormalForm (SingleField f args)

       | GT_LabeledField : forall label f args,
           qGroundTypedNormalForm (LabeledField label f args)

       | GT_NestedField : forall f args ϕ,
           GroundTypedNormalForm ϕ ->
           qGroundTypedNormalForm (NestedField f args ϕ)

       | GT_NestedLabeledField : forall label f args ϕ,
           GroundTypedNormalForm ϕ ->
           qGroundTypedNormalForm (NestedLabeledField label f args ϕ)

       | GT_InlineFragment : forall t (ϕ : QuerySet),
           all is_field_query ϕ ->      (* repeated in next check? *)
           GroundTypedNormalForm ϕ  ->
           qGroundTypedNormalForm (InlineFragment t ϕ).
  

      
   
  Fixpoint is_ground_typed_normal_form (query_set : QuerySet) : bool :=
    match query_set with
    | SingleQuery q => is_query_in_normal_form q
    | SelectionSet q q' => ((all is_field_query query_set) || (all is_inline_fragment query_set))
                            &&
                            is_query_in_normal_form q
                            &&
                            is_ground_typed_normal_form q'
      
    end
  with
  is_query_in_normal_form (query : Query) : bool :=
    match query with
    | NestedField _ _ ϕ => is_ground_typed_normal_form ϕ
    | NestedLabeledField _ _ _ ϕ => is_ground_typed_normal_form ϕ
    | InlineFragment _ ϕ => (all is_field_query ϕ) && is_ground_typed_normal_form ϕ
    | _ => true
    end.


  Lemma normal_formP query_set : reflect (GroundTypedNormalForm query_set) (is_ground_typed_normal_form query_set).
  Proof.
    apply: (iffP idP).
    + elim query_set using QuerySet_ind with
          (P0 := fun q => (is_query_in_normal_form q) -> qGroundTypedNormalForm q); do ?[by intros; constructor].
      - by move=> q IH /= H; constructor; apply: IH.
      - move=> q IH q' IHq /=.
        by move/andP=> [/andP [Hor Hq] Hq']; constructor; [| apply: IH | apply: IHq].
      - by move=> n args ϕ IH /= H; constructor; apply: IH.
      - by move=> l n args ϕ IH /= H; constructor; apply: IH.
      - by move=> t ϕ IH /= /andP [Hall H]; constructor => //; apply: IH.
    + elim query_set using QuerySet_ind with
        (P0 := fun q => qGroundTypedNormalForm q -> (is_query_in_normal_form q)); do ?[by intros].
      - by move=> q IH /= H; apply: IH; inversion H. 
      - move=> q IH q' IHq H /=; inversion H.
        simpl in H2; apply IH in H3; apply IHq in H4.
        by rewrite andb_true_intro //; rewrite andb_true_intro //.
      - by move=> n args ϕ IH H /=; inversion H; apply: IH.
      - by move=> l n args ϕ IH H /=; inversion H; apply: IH.
      - by move=> t ϕ IH H /=; inversion H; rewrite andb_true_intro //; split; [| apply IH].
  Qed.

  

  Fixpoint no_repeated_query (queries : list (@Query Name Vals)) : bool :=
     match queries with
        | [::] => true
        | hd :: tl => if has (partial_query_eq hd) tl then
                       false
                     else
                       no_repeated_query tl
     end.


  Equations is_non_redundant (queries : @QuerySet Name Vals) : bool :=
    {
      is_non_redundant (SingleQuery q) := is_query_non_redundant q;
      is_non_redundant (SelectionSet q q') := is_query_non_redundant q && is_non_redundant q'
    }
  where
  is_query_non_redundant (query : @Query Name Vals) : bool :=
    {
      is_query_non_redundant (NestedField _ _ ϕ) := is_non_redundant ϕ;
      is_query_non_redundant (NestedLabeledField _ _ _ ϕ) := is_non_redundant ϕ;
      is_query_non_redundant (InlineFragment _ ϕ) := is_non_redundant ϕ;
      is_query_non_redundant _ := true

    }.
  Next Obligation.
    elim queries using QuerySet_ind with (P0 := fun q => P0 q (is_query_non_redundant q)); do ?[by intros].
    by move=> q IH; rewrite is_non_redundant_equation_1; apply: f.
    by move=> q IH q' IHq; rewrite is_non_redundant_equation_2; apply: f0.
    by move=> n args ϕ IH; rewrite is_non_redundant_helper_1_equation_3; apply: f3.
    by move=> l n args ϕ IH; rewrite is_non_redundant_helper_1_equation_4; apply: f4.
    by move=> t ϕ IH; rewrite is_non_redundant_helper_1_equation_5; apply: f5.
  Defined.


    Structure normalizedSelection := NormalizedSelection {
                                    selection : QuerySet;
                                    _ : is_non_redundant selection;
                                    _ : is_ground_typed_normal_form selection
                              }.

    Coercion selection_of_normalized_selection (s : normalizedSelection) := let: NormalizedSelection s _ _ := s in s.


                                         

    Program Fixpoint normalize_list schema (queries : seq.seq (@Query Name Vals)) {measure (queries_size queries)} : seq.seq Query :=
       match queries with
          | [::] => [::]
          | hd :: tl =>
            match hd with
            | SingleField _ _
            | LabeledField _ _ _ => hd :: normalize_list schema (filter (fun q => ~~(partial_query_eq q hd)) tl)
            | NestedField n α (SelectionSet ϕ) =>
              let collected_subqueries :=
                  (foldr (fun q acc => if q is NestedField n' α' (SelectionSet β) then
                                      if (n == n') && (α == α') then
                                        acc ++ β
                                      else
                                        acc
                                    else
                                      acc)
                         ϕ tl)
              in
              (NestedField n α (SelectionSet (normalize_list schema collected_subqueries))) :: normalize_list schema (filter (fun q => ~~(partial_query_eq q hd)) tl)
            | InlineFragment t (SelectionSet [:: (InlineFragment t' ϕ)]) =>
              (InlineFragment t ϕ) :: normalize_list schema tl
            | InlineFragment t (SelectionSet ϕ) =>
              let norm := normalize_list schema ϕ in
              let possible_types := get_possible_types schema (NamedType t) in
              (map (fun t' => InlineFragment (name_of_type t') (SelectionSet norm)) possible_types) ++ normalize_list schema tl
            | _ => normalize_list schema tl
            end
          end.

    Fixpoint normalize query_set : QuerySet :=
      let fix normalize_list (queries : seq Query) : seq Query :=
          match queries with
          | [::] => [::]
          | hd :: tl =>
            match hd with
            | SingleField l args => hd :: (filter (fun q => q != hd) tl) 
            | LabeledField
            | NestedField
            | NestedLabeledField
            | InlineFragment
            end
          end
      in
      let: SelectionSet queries := query_set in
          SelectionSet (normalize_list queries)

      

End NRGTNF.

Arguments normalizedSelection [Name Vals].