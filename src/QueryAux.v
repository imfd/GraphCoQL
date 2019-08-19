From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

Require Import String.
Require Import QString.

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

    (** **** General boolean predicates for Query
       
     *)

    
    (** 
        is_field : Query → Bool 

        Checks whether the given query is a field selection.
     *)
    Equations is_field query : bool :=
      {
        is_field (on _ { _ }) := false;
        is_field _ := true
      }.

    (**
       is_inline_fragment : Query → Bool 

       Checks whether the given query is an inline fragment.
     *)
    Equations is_inline_fragment query : bool :=
      {
        is_inline_fragment (on _ { _ }) := true;
        is_inline_fragment _ := false
      }.
    

    (**
       is_aliased : Query → Bool

       Checks whether the given query is aliased (ie. l:f or l:f { φ })
     *)
    Definition is_aliased query : bool :=
      match query with
      | _ : _ [[ _ ]]
      | _ : _ [[ _ ]] { _ } => true
      | _ => false
      end.

    (**
       has_subqueries : Query → Bool

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
       qname : ∀ query, query.is_field → Name

       Gets the name of the given query. 
       
       Inline fragments do not have a name, therefore 
       it is required that the given query is a field.
     *)
    (* Not actually using this def *)
    Equations qname query (Hfield : query.(is_field)) : Name :=
      {
        qname (name[[ _ ]]) _ := name;
        qname (_:name[[ _ ]]) _ := name;
        qname (name[[ _ ]] { _ }) _ := name;
        qname (_:name[[ _ ]] { _ }) _ := name;
        qname (on _ { _ }) Hfld := _
      }.
        
    (**
       qalias : ∀ query, query.is_aliased → Name

       Gets the alias of the given query.

       It is required that the query is actually aliased.
     *)
    (* Not actually using this def *)
    Equations qalias query (Halias : query.(is_aliased)) : Name :=
      {
        qalias (alias : _ [[ _ ]]) _ := alias;
        qalias (alias : _ [[ _ ]] { _ }) _ := alias;
        qalias _ Halias := _
      }.
    
    (**
       oqalias : Query → option Name 

       Gets the alias of the given query or none if
       the query does not have a label.
     *)
    (* Not actually using this def *)
    Equations oqalias query : option Name :=
      {
        oqalias (label : _ [[ _ ]]) := Some label;
        oqalias (label : _ [[ _ ]] { _ }) := Some label;
        oqalias _ := None
      }.
    
    (**
       qresponse_name : ∀ query, query.is_field → Name 

       Gets the response name of the given query.
       
       For aliased fields this corresponds to their alias, while for 
       non-aliased fields it corresponds to their name.

       Inline fragment do not have a response name, therefore 
       it is required that the given query is a field.
     *)   
    Equations qresponse_name query (Hfld : query.(is_field)) :  Name :=
      {
        qresponse_name (name [[ _ ]]) _ := name;
        qresponse_name (alias : _ [[ _ ]]) _ := alias;
        qresponse_name (name [[ _ ]] { _ }) _ := name;
        qresponse_name (alias : _ [[ _ ]] { _ }) _ := alias;
        qresponse_name (on _ { _ }) Hfld := _
      }.

    (**
       oqresponse_name : Query → option Name
    
       Gets the response name of the given query or none if it 
       is an inline fragment.
     *)
    (* Not actually using this def *)
    Equations oqresponse_name query : option Name :=
      {
        oqresponse_name (on _ { _ }) := None;
        oqresponse_name q := Some (qresponse_name q _)
      }.

    (**
       has_response_name : Name → Query → Bool 

       Checks whether the given query has the given response name.

       This is always false for inline fragments.
     *)
    (* Not actually using this def *)
    Equations has_response_name : Name -> @Query Vals -> bool :=
      {
        has_response_name _ (on _ { _ }) := false;
        has_response_name rname q := (qresponse_name q _) == rname
      }.

    
    (**
       qsubqueries : Query → List Query

       Gets the given query's subqueries.

       For field selections without subqueries, it returns an empty list.
     *)
    Definition qsubqueries query : seq Query :=
      match query with
      | _ [[ _ ]] { φ }
      | _ : _ [[ _ ]] { φ }
      | on _ { φ } => φ
      | _ => [::]
      end.

    
    (**
       qargs : ∀ query, query.is_field → List (Name * Vals) 

       Gets the given query's arguments.

       Inline fragment do not have arguments, therefore 
       it is required that the given query is a field.
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
       have_same_name : Query → Query → Bool 

       Checks whether two queries have the same field name.

       It is always false if either is an inline fragment.
     *)
    Equations have_same_name : @Query Vals -> @Query Vals -> bool :=
      {
        have_same_name (on _ { _ }) _ := false;
        have_same_name _ (on _ { _ }) := false;
        have_same_name q1 q2 := (qname q1 _) == (qname q2 _)
      }.
    
    (**
       have_same_response_name : Query → Query → Bool 

       Checks whether two queries have the same response name.

       It is always false if either is an inline fragment.
     *)
    Equations have_same_response_name : @Query Vals -> @Query Vals -> bool :=
      {
        have_same_response_name (on _ { _ }) _ := false;
        have_same_response_name _ (on _ { _ }) := false;
        have_same_response_name q1 q2 := (qresponse_name q1 _) == (qresponse_name q2 _)
      }.

    (**
       have_same_arguments : Query → Query → Bool
       
       Checks whether two queries have the same arguments.

       It is always false if either is an inline fragment.
     *)
    Equations have_same_arguments : @Query Vals -> @Query Vals -> bool :=
      {
        have_same_arguments (on _ { _ }) _ := false;
        have_same_arguments _ (on _ { _ }) := false;
        have_same_arguments q1 q2 := (qargs q1 _) == (qargs q2 _)
      }.

    (**
       is_simple_field_selection : Query → Bool 

       Checks whether the given query is either a [SingleField] or [LabeledField].
     *)
    Equations is_simple_field_selection query : bool :=
      {
        is_simple_field_selection (_ [[_]]) := true;
        is_simple_field_selection (_ : _ [[_]]) := true;
        is_simple_field_selection _ := false
      }.

    
    (**
       is_nested_field_selection : Query → Bool 

       Checks whether the given query is either a [NestedField] or [LabeledNestedField].
     *)
    Equations is_nested_field_selection query : bool :=
      {
        is_nested_field_selection (_ [[_]] { _ }) := true;
        is_nested_field_selection (_ : _ [[_]] { _ }) := true;
        is_nested_field_selection _ := false
      }.

    (**
       are_equivalent : Query → Query → Bool 

       Checks whether two queries are equivalent.

       This equivalence refers to whether both queries will
       produce responses with the same name and if both 
       share the same arguments.

       ---- 
       See also : [is_field_merging_possible] (QueryConformance)
     *)
    (* FIXME : Rename *)
    Definition are_equivalent (q1 q2 : @Query Vals) : bool :=
      [&& (q1.(is_simple_field_selection) && (q2.(is_simple_field_selection)) ||
           q1.(is_nested_field_selection) && q2.(is_nested_field_selection)),
       have_same_name q1 q2 & have_same_arguments q1 q2].
    
  End Base.
  
  Section Size.

    (** **** Functions related to size of Queries
     *)
    
    (**
       query_size : Query → Nat 
       queries_size : List Query → Nat 

       Get the query's size, according to Jorge and Olaf's definition.
     *)
    Equations query_size query : nat :=
      {
        query_size (_ [[_]] { φ }) := 1 + queries_size φ;
        query_size (_ : _ [[_]] { φ }) := 1 + queries_size φ;
        query_size (on _ { φ }) := 1 + (queries_size φ);
        query_size _ := 1
      }
    where
    queries_size queries : nat :=
      {
        queries_size [::] := 0;
        queries_size (q :: φ) := query_size q + queries_size φ
      }.

    (**

     *)
    Definition queries_size_aux (queries : seq (Name * Query)) :=
      queries_size [seq nq.2 | nq <- queries].

  End Size.
  

  
  Section DefPreds.
    
    Variable s : @wfGraphQLSchema Vals.

    (** **** Other type of boolean predicates
     *)
    
    (**       
       does_fragment_type_apply : Name → Name → Bool 

       Checks whether a type is valid with respect to another type. 

       This is used when checking that a fragment's type condition is 
       valid with respect to the actual type of the data where the 
       fragment is being evaluated (which corresponds to an object type).

           fragment_type ∈ Ot             #<br>#
       fragment_type = object_type        #<br>#
      [――――――――――――――――――――――――――]        #<br>#
        fragment_type applies


                  fragment_type ∈ It                    #<br>#
       object_type ∈ implementation fragment_type       #<br>#
      [――――――――――――――――――――――――――――――――――――――――――]      #<br>#
               fragment_type applies


                  fragment_type ∈ Ut                    #<br>#
       object_type ∈ union_members fragment_type        #<br>#
      [――――――――――――――――――――――――――――――――――――――――――]      #<br>#
               fragment_type applies

    ----
    See also
    
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

    (** **** Functions related to finding queries that satisfy a predicate.
     *)
    
    Variable (s : @wfGraphQLSchema Vals).
    
    (**
       find_queries_with_label : Name → Name → List Query → List Query 

       Find all queries with response name equal to the given parameter.
       In case there is a fragment, it first checks that the fragment's type condition 
       applies to the given object type, then it may proceed to find more queries in its
       subqueries.

       This function can be related to the _CollectFields_ function defined in the specification.
       The CollectFields function returns a map of names to list of queries, effectively collecting 
       every possible _valid_ field (there is also a check for inline fragments - see subpoint "e"
       of the CollectFields definition) in a list of queries.

       In our case, instead of generating a map of every possible field and name, we take 
       the first element of a list and try to find every other possible query that is related 
       (has the same response name). Once we get all queries with a given response name, 
       we proceed to perform other operations over that collection. This is similar to how 
       J&O defined their _collect_ function.
       
       This choice is mostly to facilitate reasoning over the semantics.

       ---- 
       See also 
        
        - [execute_selection_set]

        https://graphql.github.io/graphql-spec/June2018/#sec-Executing-Selection-Sets

        https://graphql.github.io/graphql-spec/June2018/#sec-Field-Collection
        
        https://graphql.github.io/graphql-spec/June2018/#CollectFields()
     *)
    (* FIXME : Rename to something that makes sense - find_fields_with_response_name ? *)
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

    

    (** 
        find_fields_with_response_name : Name → List Query → List Query 

        Find all field selections with response name equal to the one given as parameter.
        It collects every field, regardless of fragment's type condition. This differs 
        with [find_queries_with_label], where the type condition _is_ important.

        This function is used when checking the conformance of queries, in particular when
        checking that field merging is possible. In this process, you have to check every possible 
        field with a given response name and validate they are mergeable (further discussion 
        on this can be found at [is_field_merging_possible].

        Not using fold mostly because of the nested recursion appearing in inline fragments. 

        ---- 
        See also 

        https://graphql.github.io/graphql-spec/June2018/#sec-Field-Selection-Merging

        https://graphql.github.io/graphql-spec/June2018/#FieldsInSetCanMerge()

        https://github.com/graphql/graphql-spec/issues/367
     **)
    (* FIXME : Rename considering previous def *)
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

    (**

     *)
    Equations? find_pairs_with_response_name (rname : Name) (φ : seq (Name * @Query Vals)) :
      seq (Name * @Query Vals) by wf (queries_size_aux φ) :=
      {
        find_pairs_with_response_name _ [::] := [::];
        
        find_pairs_with_response_name rname ((ty, f[[α]]) :: qs)
          with f == rname :=
          {
          | true := (ty, f[[α]]) :: find_pairs_with_response_name rname qs;
          | _ := find_pairs_with_response_name rname qs
          };
        
        find_pairs_with_response_name rname ((ty, l:f[[α]]) :: qs)
          with l == rname :=
          {
          | true := (ty, l:f[[α]]) :: find_pairs_with_response_name rname qs;
          | _ := find_pairs_with_response_name rname qs
          };

        
        find_pairs_with_response_name rname ((ty, f[[α]] { φ }) :: qs)
          with f == rname :=
          {
          | true := (ty, f[[α]] { φ }) :: find_pairs_with_response_name rname qs;
          | _ := find_pairs_with_response_name rname qs
          };
        
        find_pairs_with_response_name rname ((ty, l:f[[α]] { φ }) :: qs)
          with l == rname :=
          {
          | true := (ty, l:f[[α]] { φ }) :: find_pairs_with_response_name rname qs;
          | _ := find_pairs_with_response_name rname qs
          };
        
        find_pairs_with_response_name rname ((_, on t { φ }) :: qs) :=
          find_pairs_with_response_name rname [seq (t, q) | q <- φ] ++ find_pairs_with_response_name rname qs
      }.
    Proof.
      all: do ? [by rewrite /queries_size_aux /=; simp query_size; ssromega].
      rewrite /queries_size_aux /=; simp query_size.
      have -> : forall xs y, [seq x.2 | x <- [seq (y, q) | q <- xs] ] = xs.
        by intros; elim: xs => //= x xs ->.
        by ssromega.
    Qed.


    



  End Find.
  

  Section Filter.
    (** **** Functions related to filtering queries according to some predicate
     *)
    
    (** 
        filter_queries_with_label : Name → List Query → List Query 
        
        Filters all fields with response name equal to the one given as parameter.
        This also filters inline fragments' subqueries.

        This definition follows a similar approach as the one in [find_queries_with_label], 
        considering how collection and evaluation is done in the spec. Similarly, we 
        preferred this approach to ease reasoning over the semantics. 

        This is similar to how J&O defined their _collect_ function.

        ----
        See also:
        
        - [execute_selection_set]

        https://graphql.github.io/graphql-spec/June2018/#sec-Executing-Selection-Sets

        https://graphql.github.io/graphql-spec/June2018/#sec-Field-Collection
        
        https://graphql.github.io/graphql-spec/June2018/#CollectFields()
        
     *)
    Equations? filter_queries_with_label (label : Name) (queries : seq (@Query Vals)) :
      seq (@Query Vals) by wf (queries_size queries) :=
      {
        filter_queries_with_label _ [::] := [::];

        filter_queries_with_label l (on t { β } :: φ) :=
          on t { filter_queries_with_label l β } :: filter_queries_with_label l φ;

        filter_queries_with_label l (q :: φ)
          with (qresponse_name q _) != l :=
          {
          | true := q :: filter_queries_with_label l φ;
          | _ := filter_queries_with_label l φ
          }     

      }.
    all: do ?[simp query_size; ssromega].
    Qed.


    (**

     *)
     Equations? filter_pairs_with_response_name (response_name : Name) (queries : seq (Name * @Query Vals)) :
      seq (Name * @Query Vals) by wf (queries_size_aux queries) :=
      {
        filter_pairs_with_response_name _ [::] := [::];

        filter_pairs_with_response_name l ((ty, on t { β }) :: φ) :=
          (ty, on t { filter_queries_with_label l β }) :: filter_pairs_with_response_name l φ;

        filter_pairs_with_response_name l ((ty, q) :: φ)
          with (qresponse_name q _) != l :=
          {
          | true := (ty, q) :: filter_pairs_with_response_name l φ;
          | _ := filter_pairs_with_response_name l φ
          }     

      }.
     Proof.
       all: do ? [by rewrite /queries_size_aux /=; simp query_size; ssromega].
    Qed.
    
    

    
  End Filter.

  Section Merging.

    (** **** Functions related to merging queries.
     *)

    (**
       merge_selection_sets : List Query → List Query 

       Concatenates the subqueries of every query in the given list.

       ---- 
       https://graphql.github.io/graphql-spec/June2018/#MergeSelectionSets()
     *)
    Definition merge_selection_sets queries := flatten [seq q.(qsubqueries) | q <- queries].


    Variable (s : @wfGraphQLSchema Vals).
    
    (**

     *)
    Equations merge_pairs_selection_sets (nq : seq (Name * @Query Vals)) : seq (Name * @Query Vals) :=
      {
        merge_pairs_selection_sets [::] := [::];

        merge_pairs_selection_sets ((ty, f[[ _ ]] { β }) :: φ)
          with lookup_field_in_type s ty f :=
          {
          | Some fld := [seq (fld.(return_type).(tname), q) | q <- β] ++ merge_pairs_selection_sets φ;
          | _ := merge_pairs_selection_sets φ
          };

        merge_pairs_selection_sets ((ty, _:f[[ _ ]] { β }) :: φ)
          with lookup_field_in_type s ty f :=
          {
          | Some fld := [seq (fld.(return_type).(tname), q) | q <- β] ++ merge_pairs_selection_sets φ;
          | _ := merge_pairs_selection_sets φ
          };

        merge_pairs_selection_sets ((_, on t { β }) :: φ) :=
          [seq (t, q) | q <- β] ++ merge_pairs_selection_sets φ;
        
        merge_pairs_selection_sets (nq :: φ) := merge_pairs_selection_sets φ
      }.

    
  End Merging.


End QueryAux.



Arguments is_field [Vals].
Arguments is_inline_fragment [Vals].
Arguments is_aliased [Vals].
Arguments has_subqueries [Vals].
Arguments is_simple_field_selection [Vals].
Arguments is_nested_field_selection [Vals].

Arguments qresponse_name [Vals].
Arguments oqresponse_name [Vals].
Arguments qalias [Vals].
Arguments oqalias [Vals].
Arguments qargs [Vals].

Arguments qsubqueries [Vals].
Arguments qresponse_name [Vals].
Arguments oqresponse_name [Vals].

Arguments query_size [Vals].
Arguments queries_size [Vals].
Arguments queries_size_aux [Vals].

Arguments has_response_name [Vals].
Arguments have_same_name [Vals].
Arguments have_same_response_name [Vals].
Arguments have_same_arguments [Vals].
Arguments are_equivalent [Vals].

Arguments does_fragment_type_apply [Vals].
Arguments filter_queries_with_label [Vals].
Arguments filter_pairs_with_response_name [Vals].

Arguments find_queries_with_label [Vals].
Arguments find_fields_with_response_name [Vals].
Arguments find_pairs_with_response_name [Vals].

Arguments merge_selection_sets [Vals].
Arguments merge_pairs_selection_sets [Vals].
