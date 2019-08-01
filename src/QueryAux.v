From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.
From extructures Require Import ord fmap fset.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaWellFormedness.

Require Import Query.


Require Import SeqExtra.

Require Import Ssromega.

(* Require Import Arith. *)

Section QueryAux.

  
  Variables Name Vals : ordType.

  Implicit Type queries : seq (@Query Name Vals).
  Implicit Type query : @Query Name Vals.


  Section Base.
    (** Boolean predicates to check what type the query is:
      - Fields : Everything not an inline fragment
      - Inline : An inline fragment 
     **)
    Equations is_field query : bool :=
      {
        is_field (InlineFragment _ _) := false;
        is_field _ := true
      }.

    Equations is_inline_fragment query : bool :=
      {
        is_inline_fragment (InlineFragment _ _) := true;
        is_inline_fragment _ := false
      }.

    Definition is_labeled query : bool :=
      match query with
      | LabeledField _ _ _
      | NestedLabeledField _ _ _ _ => true
      | _ => false
      end.

    Definition has_subqueries query : bool :=
      match query with
      | SingleField _ _
      | LabeledField _ _ _ => false
      | _ => true
      end.
    
    (** Extractors for queries **)
    Equations qname query (Hfld : query.(is_field)) :  Name :=
      {
        qname (SingleField f _) _ := f;
        qname (LabeledField _ f _) _ := f;
        qname (NestedField f _ _) _ := f;
        qname (NestedLabeledField _ f _ _) _ := f;
        qname (InlineFragment _ _) Hfld := _
      }.

    Equations oqname query : option Name :=
      {
        oqname (InlineFragment _ _) := None;
        oqname q := Some (qname q _)
      }.

    
    Equations qlabel query (Hlab : query.(is_labeled)) : Name :=
      {
        qlabel (LabeledField label _ _) _ := label;
        qlabel (NestedLabeledField label _ _ _) _ := label;
        qlabel _ Hlab := _
      }.

    Equations oqlabel query : option Name :=
      {
        oqlabel (LabeledField label _ _) := Some label;
        oqlabel (NestedLabeledField label _ _ _) := Some label;
        oqlabel _ := None
      }.
    
    
    Definition qsubqueries query : seq Query :=
      match query with
      | NestedField _ _ ϕ
      | NestedLabeledField _ _ _ ϕ
      | InlineFragment _ ϕ => ϕ
      | _ => [::]
      end.

    
    Equations qsubqueries' query (Hhas : query.(has_subqueries)) : seq (@Query Name Vals) :=
      {
        qsubqueries' query Hhas := query.(qsubqueries)
      }.
    
    
    Equations qargs query (Hfld : query.(is_field)) :  {fmap Name -> Vals} :=
      {
        qargs (SingleField _ α) _ := α;
        qargs (LabeledField _ _ α) _ := α;
        qargs (NestedField _ α _) _ := α;
        qargs (NestedLabeledField _ _ α _) _ := α;
        qargs (InlineFragment _ _) Hfld := _
      }.

    Equations oqargs query : option {fmap Name -> Vals} :=
      {
        oqargs (InlineFragment _ _) := None;
        oqargs q := Some (qargs q _)
      }.

    
    Equations qresponse_name query (Hfld : query.(is_field)) :  Name :=
      {
        qresponse_name (SingleField f _) _ := f;
        qresponse_name (LabeledField l _ _) _ := l;
        qresponse_name (NestedField f _ _) _ := f;
        qresponse_name (NestedLabeledField l _ _ _) _ := l;
        qresponse_name (InlineFragment _ _) Hfld := _
      }.

    Equations oqresponse_name query : option Name :=
      {
        oqresponse_name (InlineFragment _ _) := None;
        oqresponse_name q := Some (qresponse_name q _)
      }.

    
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
    
  End Base.
  
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
  

  
  Section DefPreds.
    
    Variable s : @wfSchema Name Vals.

    (* (** Checks whether the field selection is defined in the given name *) *)
    (* Equations is_defined query (Hfield : query.(is_field)) (ty : Name) : bool := *)
    (*   { *)
    (*     is_defined q Hfield ty := isSome (lookup_field_in_type s ty (qname q Hfield)) *)
    (*   }. *)

    (* Equations? are_defined queries (ty : Name) : bool by wf (queries_size queries) := *)
    (*   { *)
    (*     are_defined [::] _ := true; *)

    (*     are_defined (InlineFragment t β :: φ) ty := are_defined β t && are_defined φ ty; *)

    (*     are_defined (q :: φ) ty := is_defined q _ ty && are_defined φ ty *)
    (*   }. *)
    (* Proof. *)
    (*   all: do ? [simp query_size; ssromega]. *)
    (* Qed. *)

    
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
    
  End DefPreds.
  
  

  

  Section Find.

    Variable (s : @wfSchema Name Vals).
    
    (** Find all queries with response name equal to given parameter.
        In case there is a fragment, it first checks that the fragments' guard 
        applies to the given object type, then it may proceed to collect in its
        subqueries **)
    Equations? find_queries_with_label (label : Name) (object_type : @NamedType Name) (queries : seq (@Query Name Vals)) :
      seq (@Query Name Vals) by wf (queries_size queries) :=
      {
        find_queries_with_label _ _ [::] := [::];

        find_queries_with_label k O__t (InlineFragment t φ :: qs)
          with does_fragment_type_apply s O__t t :=
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

    



  End Find.
  

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

    
    

    
  End Filter.

  Section Merging.
    Definition merge_selection_sets queries := flatten [seq q.(qsubqueries) | q <- queries].
    

    
  End Merging.


End QueryAux.



Arguments is_field [Name Vals].
Arguments is_inline_fragment [Name Vals].
Arguments is_labeled [Name Vals].
Arguments has_subqueries [Name Vals].
Arguments is_simple_field_selection [Name Vals].
Arguments is_nested_field_selection [Name Vals].

Arguments qname [Name Vals].
Arguments oqname [Name Vals].
Arguments qlabel [Name Vals].
Arguments oqlabel [Name Vals].
Arguments qargs [Name Vals].
Arguments oqargs [Name Vals].
Arguments qsubqueries [Name Vals].
Arguments qsubqueries' [Name Vals].
Arguments qresponse_name [Name Vals].
Arguments oqresponse_name [Name Vals].

Arguments query_size [Name Vals].
Arguments queries_size [Name Vals].
Arguments has_response_name [Name Vals].
Arguments has_field_name [Name Vals].
Arguments have_same_field_name [Name Vals].
Arguments have_same_arguments [Name Vals].
Arguments are_equivalent [Name Vals].

Arguments does_fragment_type_apply [Name Vals].
Arguments filter_queries_with_label [Name Vals].

Arguments find_queries_with_label [Name Vals].
Arguments find_fields_with_response_name [Name Vals].

Arguments merge_selection_sets [Name Vals].
