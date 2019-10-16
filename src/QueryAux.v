(* begin hide *)

From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

Require Import String.
Require Import QString.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaWellFormedness.

Require Import Query.


Require Import SeqExtra.

Require Import Ssromega.

(* end hide *)

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">GraphQL Query Auxiliary</h1>
        <p class="lead">
         This file contains auxiliary definitions used with a GraphQL Query.
        </p>

        <p>
         Some of these are: query size, extractors for queries, general purpose predicates, etc.
        </p>
  </div>
</div>#
 *)

Section QueryAux.

  
  Variable Value : eqType.

  Implicit Type queries : seq (@Selection Value).
  Implicit Type query : @Selection Value.


  (** ---- *)
  (** *** General purpose predicates *)
  Section Base.


    (** ---- *)
    (** 
        is_field : Query → Bool 

        Checks whether the given query is a field selection.
     *)
    Equations is_field query : bool :=
      {
        is_field (on _ { _ }) := false;
        is_field _ := true
      }.

    
    (** ---- *)
    (**
       is_inline_fragment : Query → Bool 

       Checks whether the given query is an inline fragment.
     *)
    Equations is_inline_fragment query : bool :=
      {
        is_inline_fragment (on _ { _ }) := true;
        is_inline_fragment _ := false
      }.

    
    (** ---- *)
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

    
    (** ---- *)
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



    (** ---- *)
    (** *** Extractors for queries *)

    (** ---- *)
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


    (** ---- *)
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


    (** ---- *)
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


    (** ---- *)
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


    (** ---- *)
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
    
    (** ---- *)
    (**
       has_response_name : Name → Query → Bool 

       Checks whether the given query has the given response name.

       This is always false for inline fragments.
     *)
    (* Not actually using this def *)
    Equations has_response_name : Name -> @Selection Value -> bool :=
      {
        has_response_name _ (on _ { _ }) := false;
        has_response_name rname q := (qresponse_name q _) == rname
      }.


    (** ---- *)
    (**
       qsubqueries : Selection → List Selection

       Gets the given query's subqueries.

       For field selections without subqueries, it returns an empty list.
     *)
    Definition qsubqueries query : seq Selection :=
      match query with
      | _ [[ _ ]] { φ }
      | _ : _ [[ _ ]] { φ }
      | on _ { φ } => φ
      | _ => [::]
      end.


    (** ---- *)
    (**
       qargs : ∀ query, query.is_field → List (Name * Value) 

       Gets the given query's arguments.

       Inline fragment do not have arguments, therefore 
       it is required that the given query is a field.
     *)
    Equations qargs query (Hfld : query.(is_field)) :  seq (Name * Value) :=
      {
        qargs (_ [[ α ]]) _ := α;
        qargs (_ : _ [[ α ]]) _ := α;
        qargs (_ [[ α ]] { _ }) _ := α;
        qargs (_ : _ [[ α ]] { _ }) _ := α;
        qargs (on _ { _ }) Hfld := _
      }.


    
    (** ---- *)
    (**
       have_same_name : Selection → Selection → Bool 

       Checks whether two queries have the same field name.

       It is always false if either is an inline fragment.
     *)
    Equations have_same_name : @Selection Value -> @Selection Value -> bool :=
      {
        have_same_name (on _ { _ }) _ := false;
        have_same_name _ (on _ { _ }) := false;
        have_same_name q1 q2 := (qname q1 _) == (qname q2 _)
      }.


    (** ---- *)
    (**
       have_same_response_name : Selection → Selection → Bool 

       Checks whether two queries have the same response name.

       It is always false if either is an inline fragment.
     *)
    Equations have_same_response_name : @Selection Value -> @Selection Value -> bool :=
      {
        have_same_response_name (on _ { _ }) _ := false;
        have_same_response_name _ (on _ { _ }) := false;
        have_same_response_name q1 q2 := (qresponse_name q1 _) == (qresponse_name q2 _)
      }.


    (** ---- *)
    (**
       have_same_arguments : Selection → Selection → Bool
       
       Checks whether two queries have the same arguments.

       It is always false if either is an inline fragment.
     *)
    Equations have_same_arguments : @Selection Value -> @Selection Value -> bool :=
      {
        have_same_arguments (on _ { _ }) _ := false;
        have_same_arguments _ (on _ { _ }) := false;
        have_same_arguments q1 q2 := (qargs q1 _) == (qargs q2 _)
      }.


    (** ---- *)
    (**
       is_simple_field_selection : Selection → Bool 

       Checks whether the given query is either a [SingleField] or [LabeledField].
     *)
    Equations is_simple_field_selection query : bool :=
      {
        is_simple_field_selection (_ [[_]]) := true;
        is_simple_field_selection (_ : _ [[_]]) := true;
        is_simple_field_selection _ := false
      }.


    (** ---- *)
    (**
       is_nested_field_selection : Selection → Bool 

       Checks whether the given query is either a [NestedField] or [LabeledNestedField].
     *)
    Equations is_nested_field_selection query : bool :=
      {
        is_nested_field_selection (_ [[_]] { _ }) := true;
        is_nested_field_selection (_ : _ [[_]] { _ }) := true;
        is_nested_field_selection _ := false
      }.

    (**
       #<strong>selection_perm_eq</strong# : Selection → Selection → Bool 

       Decides whether two selections are equal, considering possible permutation
       of arguments in field selections.
     *)
    Equations selection_perm_eq (σ1 σ2 : @Selection Value) : bool :=
      {
        selection_perm_eq (f1[[α1]]) (f2[[α2]]) := (f1 == f2) && perm_eq α1 α2;
        selection_perm_eq (a1:f1[[α1]]) (a2:f2[[α2]]) := [&& a1 == a2, f1 == f2 & perm_eq α1 α2];
        selection_perm_eq (f1[[α1]] { σs1 }) (f2[[α2]] { σs2 }) :=
          [&& f1 == f2, perm_eq α1 α2 & selections_perm_eq σs1 σs2];
        selection_perm_eq (a1:f1[[α1]] { σs1 }) (a2:f2[[α2]] { σs2 }) :=
          [&& a1 == a2, f1 == f2, perm_eq α1 α2 & selections_perm_eq σs1 σs2];
        selection_perm_eq (on t1 { σs1 }) (on t2 { σs2 }) :=
          (t1 == t2) && (selections_perm_eq σs1 σs2);
        selection_perm_eq _ _ := false
      }
    where selections_perm_eq (σs1 σs2 : seq (@Selection Value)) : bool :=
            {
              selections_perm_eq [::] [::] := true;
              selections_perm_eq (σ1 :: σs1) (σ2 :: σs2) := selection_perm_eq σ1 σ2 && selections_perm_eq σs1 σs2;
              selections_perm_eq _ _ := false
            }.
    
    (** ---- *)
    (**
       are_equivalent : Selection → Selection → Bool 

       Checks whether two queries are equivalent.

       This equivalence refers to whether both queries will
       produce responses with the same name and if both 
       share the same arguments.

       
       **** See also
       - [is_field_merging_possible] (_SelectionConformance_)
     *)
    (* FIXME : Rename *)
    Definition are_equivalent (q1 q2 : @Selection Value) : bool :=
      [&& (q1.(is_simple_field_selection) && (q2.(is_simple_field_selection)) ||
           q1.(is_nested_field_selection) && q2.(is_nested_field_selection)),
       have_same_name q1 q2 & have_same_arguments q1 q2].


   

    
  End Base.

  (** ---- *)
  (** *** Size functions 
      
      In this section we define functions related to
      the size of queries.
   *)
  Section Size.

    (** ---- *)
    (**
       query_size : Selection → Nat 
       queries_size : List Selection → Nat 

       Get the query's size, according to Jorge and Olaf's definition.
     *)
    Equations selection_size query : nat :=
      {
        selection_size (_ [[_]] { φ }) := 1 + queries_size φ;
        selection_size (_ : _ [[_]] { φ }) := 1 + queries_size φ;
        selection_size (on _ { φ }) := 1 + (queries_size φ);
        selection_size _ := 1
      }
    where
    queries_size queries : nat :=
      {
        queries_size [::] := 0;
        queries_size (q :: φ) := selection_size q + queries_size φ
      }.

    (** ---- *)
    (**

     *)
    Definition queries_size_aux (queries : seq (Name * Selection)) :=
      queries_size [seq nq.2 | nq <- queries].

    Definition query_size (φ : @query Value) :=
      queries_size φ.(selection_set).
      

  End Size.
  


  (** ---- *)
  (** *** Other type of predicates *)
    
  Section DefPreds.
    
    Variable s : @wfGraphQLSchema Value.

    (** ---- *)
    (**       
       does_fragment_type_apply : Name → Name → Bool 

       This predicate checks whether a type condition is valid in 
       a given object type. 
       
       This is used to check if we have to evaluate a fragment.
   
       This definition is similar to the one #<a href='https://graphql.github.io/graphql-spec/June2018/#DoesFragmentTypeApply()'>in the spec</a>#. This one is a bit different to make it clearer and easier to reason about. 
     
     *)
    Definition does_fragment_type_apply object_type fragment_type :=
      match lookup_type s object_type, lookup_type s fragment_type with
      | Some (Object oname implements _ { _ }), Some (Object name implements _ { _ }) =>
        object_type == name
      | Some (Object _ implements interfaces { _ }), Some (Interface name { _ }) =>
        name \in interfaces
      | Some (Object oname implements _ { _ }), Some (Union name { members }) =>
        oname \in members
      | _, _ => false
      end.

     (** ---- *)
    (**
     #<strong>is_fragment_spread_possible</strong># : Name → Name → Bool 
     
     Checks whether a given type can be used as an inline fragment's type condition 
     in a given context with another type in scope (parent type).

     It basically amounts to intersecting the possible subtypes of each
     and checking that the intersection is not empty.     
     *)
    Definition is_fragment_spread_possible parent_type fragment_type : bool :=
      let ty_possible_types := get_possible_types s fragment_type in
      let parent_possible_types := get_possible_types s parent_type in
      let applicable_types := (ty_possible_types :&: parent_possible_types)%SEQ in
      applicable_types != [::].
    
    
  End DefPreds.
  
  

  
  (** ---- *)
  (** *** Functions related to finding queries that satisfy a predicate *)
  Section Find.

    
    Variable (s : @wfGraphQLSchema Value).

    (** ---- *)
    (**
       find_queries_with_label : Name → Name → List Selection → List Selection 

       Find all queries with response name equal to a given name.
       In case there is a fragment, it first checks that the fragment's type condition 
       applies to the given object type, then it may proceed to find more queries in its
       subqueries.

     *)
    (* FIXME : Rename to something that makes sense - find_fields_with_response_name ? *)
    Equations? find_queries_with_label (label : Name) (object_type : Name) (queries : seq (@Selection Value)) :
      seq (@Selection Value) by wf (queries_size queries) :=
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
    all: do ?simp selection_size; ssromega.
    Qed.

    Equations? find_valid_pairs_with_response_name (ts : Name) (rname : Name) (σs : seq (Name * @Selection Value)) :
      seq (Name * @Selection Value) by wf (queries_size_aux σs) :=
      {
        find_valid_pairs_with_response_name _ _ [::] := [::];

        find_valid_pairs_with_response_name ts rname ((_, on t { βs }) :: qs)
          with does_fragment_type_apply s ts t :=
          {
          | true := find_valid_pairs_with_response_name rname ts [seq (t, β) | β <- βs] ++ find_valid_pairs_with_response_name ts rname qs;
          | _ := find_valid_pairs_with_response_name ts rname qs
          };

        find_valid_pairs_with_response_name ts rname ((t, σ) :: σs)
          with (qresponse_name σ _) == rname :=
          {
          | true := (t, σ) :: find_valid_pairs_with_response_name rname ts σs;
          | _ := find_valid_pairs_with_response_name rname ts σs
          }
      }.
    all: do ? [rewrite /queries_size_aux /=; simp selection_size; rewrite -/(queries_size_aux _); ssromega].
      by rewrite /queries_size_aux /=; simp selection_size; rewrite -map_comp /funcomp /= map_id; ssromega.
    Qed.
    
    (** ---- *)
    (** 
        find_fields_with_response_name : Name → List Selection → List Selection 

        Find all queries with response name equal to a given name.
        It collects every field, regardless of fragment's type condition. This differs 
        with [find_queries_with_label], where the type condition _is_ important.
     *)
    (* FIXME : Rename considering previous def *)
    Equations? find_fields_with_response_name (rname : Name) (φ : seq (@Selection Value)) :
      seq (@Selection Value) by wf (queries_size φ) :=
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
      all: do [by simp selection_size; ssromega].
    Qed.


    (** ---- *)
    (**
       
     *)
    Equations? find_pairs_with_response_name (rname : Name) (φ : seq (Name * @Selection Value)) :
      seq (Name * @Selection Value) by wf (queries_size_aux φ) :=
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
      all: do ? [by rewrite /queries_size_aux /=; simp selection_size; ssromega].
      rewrite /queries_size_aux /=; simp selection_size.
      have -> : forall xs y, [seq x.2 | x <- [seq (y, q) | q <- xs] ] = xs.
        by intros; elim: xs => //= x xs ->.
        by ssromega.
    Qed.

     


    (** ---- *)
    (**
       find_fragment_with_type_condition : Name → List Selection → List Selection 

       Find all fragments with type condition equal to a given type.
     *)
    Equations find_fragment_with_type_condition : Name -> seq (@Selection Value) -> seq (@Selection Value) :=
      {
        find_fragment_with_type_condition _ [::] := [::];

        find_fragment_with_type_condition t (on t' { β } :: φ)
          with t == t' :=
          {
          | true := on t { β } :: find_fragment_with_type_condition t φ;
          | _ := find_fragment_with_type_condition t φ
          };

        find_fragment_with_type_condition t (q :: φ) := find_fragment_with_type_condition t φ
      }.


  End Find.
  
  (** ---- *)
  (** *** Functions related to filtering queries according to some predicate *)
  Section Filter.

    (** ---- *)
    (** 
        filter_queries_with_label : Name → List Selection → List Selection 
        
        Remove all fields with a given response name.
     *)
    Equations? filter_queries_with_label (label : Name) (queries : seq (@Selection Value)) :
      seq (@Selection Value) by wf (queries_size queries) :=
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
    all: do ?[simp selection_size; ssromega].
    Qed.


    (** ---- *)
    (**

     *)
     Equations? filter_pairs_with_response_name (response_name : Name) (queries : seq (Name * @Selection Value)) :
      seq (Name * @Selection Value) by wf (queries_size_aux queries) :=
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
       all: do ? [by rewrite /queries_size_aux /=; simp selection_size; ssromega].
    Qed.
    
    

    
  End Filter.

  (** ---- *)
  (** *** Functions related to merging queries *)
  Section Merging.

    (** ---- *)
    (**
       merge_selection_sets : List Selection → List Selection 
       
       Concatenates the subqueries of every query in the given list.
     *)
    Definition merge_selection_sets queries := flatten [seq q.(qsubqueries) | q <- queries].
    

    Variable (s : @wfGraphQLSchema Value).

    (** ---- *)
    (**

     *)
    Equations merge_pairs_selection_sets (nq : seq (Name * @Selection Value)) : seq (Name * @Selection Value) :=
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




(** ---- *)

(** 
    #<div>
        <a href='GraphCoQL.Selection.html' class="btn btn-light" role='button'> Previous ← Selection  </a>
        <a href='GraphCoQL.SelectionConformance.html' class="btn btn-info" role='button'>Next → Selection Conformance</a>
    </div>#
 *)


(** ---- *)

Arguments is_field [Value].
Arguments is_inline_fragment [Value].
Arguments is_aliased [Value].
Arguments has_subqueries [Value].
Arguments is_simple_field_selection [Value].
Arguments is_nested_field_selection [Value].

Arguments qresponse_name [Value].
Arguments oqresponse_name [Value].
Arguments qalias [Value].
Arguments oqalias [Value].
Arguments qargs [Value].

Arguments qsubqueries [Value].
Arguments qresponse_name [Value].
Arguments oqresponse_name [Value].

Arguments selection_size [Value].
Arguments queries_size [Value].
Arguments queries_size_aux [Value].
Arguments query_size [Value].

Arguments has_response_name [Value].
Arguments have_same_name [Value].
Arguments have_same_response_name [Value].
Arguments have_same_arguments [Value].
Arguments are_equivalent [Value].

Arguments does_fragment_type_apply [Value].
Arguments is_fragment_spread_possible [Value].

Arguments filter_queries_with_label [Value].
Arguments filter_pairs_with_response_name [Value].

Arguments find_queries_with_label [Value].
Arguments find_valid_pairs_with_response_name [Value].
Arguments find_fields_with_response_name [Value].
Arguments find_pairs_with_response_name [Value].
Arguments find_fragment_with_type_condition [Value].

Arguments merge_selection_sets [Value].
Arguments merge_pairs_selection_sets [Value].


