From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

From CoqUtils Require Import string.

Require Import Base.
Require Import Schema.
Require Import SchemaAux.
Require Import SchemaWellFormedness.

Require Import Query.


Require Import SeqExtra.

Require Import Ssromega.


Section QueryAux.

  
  Variable Vals : eqType.

  Implicit Type queries : seq (@Query Vals).
  Implicit Type query : @Query Vals.


  Section Base.
    (** 
        Checks whether the given query is a field selection.
     *)
    Equations is_field query : bool :=
      {
        is_field (on _ { _ }) := false;
        is_field _ := true
      }.

    (**
       Checks whether the given query is an inline fragment.
     *)
    Equations is_inline_fragment query : bool :=
      {
        is_inline_fragment (on _ { _ }) := true;
        is_inline_fragment _ := false
      }.
    

    (**
       Checks whether the given query is labeled (ie. l:f or l:f { φ })
     *)
    Definition is_labeled query : bool :=
      match query with
      | _ : _ [[ _ ]]
      | _ : _ [[ _ ]] { _ } => true
      | _ => false
      end.

    (**
       Checks whether the given query has subqueries.
     *)
    Definition has_subqueries query : bool :=
      match query with
      | _ [[ _ ]]
      | _ : _ [[ _ ]] => false
      | _ => true
      end.
    
    (** **** Extractors for queries *)

    (**
       Get the response name of the given query. 
       Inline fragment do not have a response name, therefore 
       it is required that the given query is a field.
     *)
   
    Equations qresponse_name query (Hfld : query.(is_field)) :  Name :=
      {
        qresponse_name (f [[ _ ]]) _ := f;
        qresponse_name (l : _ [[ _ ]]) _ := l;
        qresponse_name (f [[ _ ]] { _ }) _ := f;
        qresponse_name (l : _ [[ _ ]] { _ }) _ := l;
        qresponse_name (on _ { _ }) Hfld := _
      }.

    (**
       Get the response name of the given query or none if it 
       is an inline fragment.
     *)
    Equations oqresponse_name query : option Name :=
      {
        oqresponse_name (on _ { _ }) := None;
        oqresponse_name q := Some (qresponse_name q _)
      }.

    (**
       Checks whether the given query has the given response name.
       This is always false for inline fragments.
     *)
    Equations has_response_name : Name -> @Query Vals -> bool :=
      {
        has_response_name _ (on _ { _ }) := false;
        has_response_name rname q := (qresponse_name q _) == rname
      }.

   

    (**
       Get the label of the given query.
       It is required that the query is actually labeled.
     *)
    Equations qlabel query (Hlab : query.(is_labeled)) : Name :=
      {
        qlabel (label : _ [[ _ ]]) _ := label;
        qlabel (label : _ [[ _ ]] { _ }) _ := label;
        qlabel _ Hlab := _
      }.

    (**
       Get the label of the given query or none if
       the query does not have a label.
     *)
    Equations oqlabel query : option Name :=
      {
        oqlabel (label : _ [[ _ ]]) := Some label;
        oqlabel (label : _ [[ _ ]] { _ }) := Some label;
        oqlabel _ := None
      }.
    
    (**
       Get the given query's subqueries.
       If the query does not have subqueries, then it returns
       an empty list.
     *)
    Definition qsubqueries query : seq Query :=
      match query with
      | _ [[ _ ]] { φ }
      | _ : _ [[ _ ]] { φ }
      | on _ { φ } => φ
      | _ => [::]
      end.

    
    Equations qsubqueries' query (Hhas : query.(has_subqueries)) : seq (@Query Vals) :=
      {
        qsubqueries' query Hhas := query.(qsubqueries)
      }.
    
    (**
       Get the given query's arguments.
       It is required that the query is not an inline fragment.
     *)
    Equations qargs query (Hfld : query.(is_field)) :  seq (Name * Vals) :=
      {
        qargs (_ [[ α ]]) _ := α;
        qargs (_ : _ [[ α ]]) _ := α;
        qargs (_ [[ α ]] { _ }) _ := α;
        qargs (_ : _ [[ α ]] { _ }) _ := α;
        qargs (on _ { _ }) Hfld := _
      }.


    

    (**
       Checks whether two queries have the same response name.

       It is always false if either is an inline fragment.
     *)
    Equations have_same_response_name : @Query Vals -> @Query Vals -> bool :=
      {
        have_same_response_name (on _ { _ }) _ := false;
        have_same_response_name _ (on _ { _ }) := false;
        have_same_response_name q1 q2 := (qresponse_name q1 _) == (qresponse_name q2 _)
      }.

    Equations have_same_arguments : @Query Vals -> @Query Vals -> bool :=
      {
        have_same_arguments (on _ { _ }) _ := false;
        have_same_arguments _ (on _ { _ }) := false;
        have_same_arguments q1 q2 := (qargs q1 _) == (qargs q2 _)
      }.

    (**
       Checks whether the given query is a simple field selection.
       Simple field selections are fields without subqueries.
     *)
    Equations is_simple_field_selection : @Query Vals -> bool :=
      {
        is_simple_field_selection (_ [[_]]) := true;
        is_simple_field_selection (_ : _ [[_]]) := true;
        is_simple_field_selection _ := false
      }.

    
    (**
       Checks whether the given query is a nested field selection.
       Nested field selections are fields with subqueries.
     *)
    Equations is_nested_field_selection : @Query Vals -> bool :=
      {
        is_nested_field_selection (_ [[_]] { _ }) := true;
        is_nested_field_selection (_ : _ [[_]] { _ }) := true;
        is_nested_field_selection _ := false
      }.

    (**
       Checks whether two queries are equivalent.
       This equivalence refers to whether both queries will
       produce responses with the same name and if both 
       share the same arguments.
     *)
    (* FIXME : Rename *)
    Definition are_equivalent (q1 q2 : @Query Vals) : bool :=
      [&& (q1.(is_simple_field_selection) && (q2.(is_simple_field_selection)) ||
           q1.(is_nested_field_selection) && q2.(is_nested_field_selection)),
       have_same_response_name q1 q2 & have_same_arguments q1 q2].
    
  End Base.
  
  Section Size.
    
    (** Get the query's size, according to Jorge and Olaf's version **)
    Equations query_size query : nat :=
      {
        query_size (_ [[_]] { φ }) := 1 + queries_size φ;
        query_size (_ : _ [[_]] { φ }) := 1 + (queries_size φ);
        query_size (on _ { φ }) := 1 + (queries_size φ);
        query_size _ := 1
      }
    where
    queries_size queries : nat :=
      {
        queries_size [::] := 0;
        queries_size (hd :: tl) := query_size hd + queries_size tl
      }.


    
    (* Equations max_query_size query : nat := *)
    (*   { *)
    (*     max_query_size (NestedField _ _ φ) := (max_queries_size φ).+1; *)
    (*     max_query_size (NestedLabeledField _ _ _ φ) := (max_queries_size φ).+1; *)
    (*     max_query_size (InlineFragment _ φ) := (max_queries_size φ).+1; *)
    (*     max_query_size _ := 0 *)
    (*   } *)
    (* where max_queries_size queries : nat := *)
    (*         { *)
    (*           max_queries_size [::] := 0; *)
    (*           max_queries_size (q :: φ) := max (max_query_size q) (max_queries_size φ) *)
    (*         }. *)
    

  End Size.
  

  
  Section DefPreds.
    
    Variable s : @wfGraphQLSchema Vals.


    
    (**
     Checks whether a type is valid with respect to another type. 

     This is used when checking that a fragment's type guard is 
     valid with respect to the actual type of the data where the 
     fragment is being evaluated (which corresponds to an object type).

     fragment_type ∈ Ot 
     fragment_type = object_type
     [――――――――――――――――――――――――――]
       fragment_type applies

    https://graphql.github.io/graphql-spec/June2018/#DoesFragmentTypeApply() 
     *)
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

    Variable (s : @wfGraphQLSchema Vals).
    
    (** Find all queries with response name equal to given parameter.
        In case there is a fragment, it first checks that the fragments' guard 
        applies to the given object type, then it may proceed to collect in its
        subqueries **)
    Equations? find_queries_with_label (label : Name) (object_type : Name) (queries : seq (@Query Vals)) :
      seq (@Query Vals) by wf (queries_size queries) :=
      {
        find_queries_with_label _ _ [::] := [::];

        find_queries_with_label k O__t (on t { φ } :: qs)
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
    Equations? find_fields_with_response_name (rname : Name) (φ : seq (@Query Vals)) :
      seq (@Query Vals) by wf (queries_size φ) :=
      {
        find_fields_with_response_name _ [::] := [::];
        
        
        find_fields_with_response_name rname (f [[α]] :: qs)
          with f == rname :=
          {
          | true := f [[α]] :: find_fields_with_response_name rname qs;
          | _ := find_fields_with_response_name rname qs
          };
        
        find_fields_with_response_name rname (l : f [[α]] :: qs)
          with l == rname :=
          {
          | true := l : f [[α]] :: find_fields_with_response_name rname qs;
          | _ := find_fields_with_response_name rname qs
          };

        
        find_fields_with_response_name rname (f [[α]] { φ } :: qs)
          with f == rname :=
          {
          | true := f [[α]] { φ } :: find_fields_with_response_name rname qs;
          | _ := find_fields_with_response_name rname qs
          };
        
        find_fields_with_response_name rname (l : f [[α]] { φ }:: qs)
          with l == rname :=
          {
          | true := l : f [[α]] { φ } :: find_fields_with_response_name rname qs;
          | _ := find_fields_with_response_name rname qs
          };
        
        find_fields_with_response_name rname (on t { φ } :: qs) :=
          find_fields_with_response_name rname φ ++ find_fields_with_response_name rname qs
      }.
    Proof.
      all: do [by simp query_size; ssromega].
    Qed.

    



  End Find.
  

  Section Filter.
    (** Filters all selections with response name equal to the one given as parameter **)
    Equations? filter_queries_with_label (label : Name) (queries : seq (@Query Vals)) :
      seq (@Query Vals) by wf (queries_size queries) :=
      {
        filter_queries_with_label _ [::] := [::];

        filter_queries_with_label l (on t { φ } :: qs) :=
          on t { filter_queries_with_label l φ } :: filter_queries_with_label l qs;

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



Arguments is_field [Vals].
Arguments is_inline_fragment [Vals].
Arguments is_labeled [Vals].
Arguments has_subqueries [Vals].
Arguments is_simple_field_selection [Vals].
Arguments is_nested_field_selection [Vals].

Arguments qresponse_name [Vals].
Arguments oqresponse_name [Vals].
Arguments qlabel [Vals].
Arguments oqlabel [Vals].
Arguments qargs [Vals].
(* Arguments oqargs [Vals]. *)
Arguments qsubqueries [Vals].
Arguments qsubqueries' [Vals].
Arguments qresponse_name [Vals].
Arguments oqresponse_name [Vals].

Arguments query_size [Vals].
Arguments queries_size [Vals].
Arguments has_response_name [Vals].
Arguments have_same_response_name [Vals].
Arguments have_same_arguments [Vals].
Arguments are_equivalent [Vals].

Arguments does_fragment_type_apply [Vals].
Arguments filter_queries_with_label [Vals].

Arguments find_queries_with_label [Vals].
Arguments find_fields_with_response_name [Vals].

Arguments merge_selection_sets [Vals].
