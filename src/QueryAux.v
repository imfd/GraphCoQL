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

  Lemma queries_size_app qs qs' :
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

 
                                      

   
End QueryAux.


Arguments filter_queries_with_label [Name Vals].