(* begin hide *)

From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

Require Import String.
Require Import QString.

Require Import Query.
Require Import QueryAux.
Require Import QueryAuxLemmas.
Require Import SchemaWellFormedness.

Require Import Schema.
Require Import SchemaAux.

Require Import QueryConformance.

Require Import SeqExtra.

Require Import Ssromega.


Require Import QueryTactics.

(* end hide *)

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">Normal Form</h1>
        <p class="lead">
         This file contains the basic predicates for non-redundancy and groundness of queries,
         and also contains the normalisation procedure.
        </p>
         
  </div>
</div>#
 *)

Section NormalForm.

  Variables Vals : eqType.
  Variables (s : @wfGraphQLSchema Vals).
  
  Implicit Type queries : seq (@Selection Vals).
  Implicit Type query : @Selection Vals.
  

  (** * Definitions *)
  
  (** ** Groundedness
      In this section we define the predicates to establish when a 
      GraphQL Selection is grounded.
   *)
  (** ---- *)
  (**
     #<strong>is_in_ground_typed_nf</strong># : Selection → Bool 

     Checks whether the given selection is in ground-typed normal form, as described in HP.
   *)
  Fixpoint is_in_ground_typed_nf (selection : @Selection Vals) : bool :=
    match selection with
    | _[[_]] { ss } => (all (fun s => s.(is_field)) ss || all (fun s => s.(is_inline_fragment)) ss) && all is_in_ground_typed_nf ss
    | _:_[[_]] { ss } => (all (fun s => s.(is_field)) ss || all (fun s => s.(is_inline_fragment)) ss) && all is_in_ground_typed_nf ss  
    | on t { ss } => is_object_type s t && all (fun s => s.(is_field) && s.(is_in_ground_typed_nf)) ss
    | _ => true
    end.

  (** ---- *)
  (**
     #<strong>are_in_ground_typed_nf</strong># : List Selection → Bool 

     Checks whether the given selection set is in ground-typed normal form, as described in HP.
   *)
  Definition are_in_ground_typed_nf (ss : seq (@Selection Vals)) : bool :=
    (all (fun s => s.(is_field)) ss || all (fun s => s.(is_inline_fragment)) ss) && all is_in_ground_typed_nf ss.

  (** ---- *)
  (**
    #<strong>is_a_ground_typed_nf_query</strong># : Query → Bool 

     Checks whether the given query is in ground-typed normal form, by checking that its selection set is
     in ground-typed normal form.
   *)
  Definition is_a_grounded_typed_nf_query (q : @query Vals) :=
    all (fun s => s.(is_field) && s.(is_in_ground_typed_nf)) q.(selection_set).
  

  (** ---- *)
  (**
     #<strong>is_grounded</strong># : Name → Selection → Bool 

     #<strong>are_grounded2</strong># : Name → List Selection → Bool

     #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
     Checks whether the given query is grounded v.2.0.
     
     This predicate uses information on the type in context where queries might be defined.
     - If the type in context is an Object type, then it expects to find only fields.
     - If the type in context is an Abstract type, then it expects to find only fragments.
     
   *)
  Fixpoint is_grounded (ts : Name) (selection : @Selection Vals) : bool :=
    if is_object_type s ts then
      (* Fields are valid in object scope *)
      match selection with
      | _[[_]]
      | _:_[[_]] => true
      | f[[_]] { ss } =>
        if lookup_field_in_type s ts f is Some fld then
          all (is_grounded fld.(return_type)) ss
        else
          false
            
      | _:f[[_]] { ss } =>
        if lookup_field_in_type s ts f is Some fld then
          all (is_grounded fld.(return_type)) ss
        else
          false
            
      | _ => false
      end
    else
      (* Only inline fragments are valid in abstract scope *)
      if selection is on t { ss } then
        (is_object_type s t) && all (is_grounded t) ss
      else
        false.
                     
  Definition are_grounded (ts : Name) (ss : seq (@Selection Vals)) : bool :=
    all (is_grounded ts) ss.

    


  (** ** Non-redundancy
      
      In this section we define the predicate to establish when a GraphQL Selection 
      is non-redundant.
   *)
  (** ---- *)
  (**
     #<strong>are_non_redundant</strong># : List Selection → Bool 

     Checks whether the selection set is non-redundant.
     This checks that :
     - There are no inline fragments with the same type condition.
     - There are no field selections with the same response name.
   *)
  Equations? are_non_redundant (ss : seq (@Selection Vals)) : bool
    by wf (queries_size ss) :=
    {
      are_non_redundant [::] := true;
      
      are_non_redundant (on t { β } :: φ) :=
        [&& find_fragment_with_type_condition t φ == [::],
            are_non_redundant β &
            are_non_redundant φ];

      are_non_redundant (q :: φ) :=
        [&& find_fields_with_response_name (qresponse_name q _) φ == [::],
            are_non_redundant q.(qsubqueries) &
            are_non_redundant φ]

    }.                 
  Proof.
    all: do ? [case: q].
    all: do ? intros; simp selection_size; ssromega.
  Qed.


  (** ---- *)
  (**
     #<strong>is_non_redundant</strong># : Query → Bool 

     Checks whether the query is non-redundant by checking that its selection set is 
     non-redundant.
   *)
  Definition is_non_redundant (q : @query Vals) : bool := q.(selection_set).(are_non_redundant).

  
  (** ---- *)
  (**
     #<strong>is_in_normal_form</strong># : Query → Bool 

     Checks whether a query is in normal form.
   *)
  Definition is_in_normal_form (q : @query Vals) := q.(is_a_grounded_typed_nf_query) && q.(is_non_redundant).


  (** ---- *)  
End NormalForm.

Arguments is_in_ground_typed_nf [Vals].
Arguments are_in_ground_typed_nf [Vals].
Arguments is_grounded [Vals].
Arguments are_grounded [Vals].
Arguments are_non_redundant [Vals].
Arguments is_non_redundant [Vals].
Arguments is_in_normal_form [Vals].



Section Normalisation.

  Variables Vals : eqType.
  Implicit Type schema : @wfGraphQLSchema Vals.
  Implicit Type query : @Selection Vals.


  Variable s : @wfGraphQLSchema Vals.

  (** * Normalisation
      
      In this section we will define a normalisation procedure, which 
      takes a GraphQL Selection and outputs another one in normal form.
      
      The proof of this is in the file _SelectionNormalizationLemmas_.
   *)
  (** ---- *)
  (**
     #<strong>normalize_selections</strong># : Name → List Selection → List Selection 

     Normalizes the given list of selections. 
     The resulting list are non-redundant and in ground-type 
     normal form.
     
     Normalization consists of two main processes :
     
     - Eliminating redundancies via merging : Fields which share 
        a response name are collapsed/collected into the first occurrence of 
        this set of common fields. This resembles the process carried out 
        by the semantics (CollectFields & MergeSelectionSets).

     - Grounding : Queries which are supposed to occur in abstract types 
        (be it an inline fragment with an abstract type condition or a    
        field with an abstract return type) are specialized into every
        possible subtype of the given abstract type (minus the abstract type itself). 
        This means that fragments might be "lifted" (its type condition is removed and its 
        subqueries lifted) or removed if they do not make sense in the context
        On the other hand, fields' subqueries might be wrapped in fragments, specializing their contents.


     This definition assumes that the given type in scope is actually an Object type.
   *)
  Equations? normalize_selections (type_in_scope : Name) (ss : seq (@Selection Vals)) :
    seq (@Selection Vals) by wf (queries_size ss) :=
    {
      normalize_selections _ [::] := [::];

      normalize_selections ty (f[[α]] :: φ)
        with lookup_field_in_type s ty f :=
        {
        | Some _ := f[[α]] :: normalize_selections ty (filter_queries_with_label f φ);
        | _ := normalize_selections ty φ
        };
      
      normalize_selections ty (l:f[[α]] :: φ)
        with lookup_field_in_type s ty f :=
        {
        | Some _ := l:f[[α]] :: normalize_selections ty (filter_queries_with_label l φ);
        | _ := normalize_selections ty φ
        };

      normalize_selections ty (f[[α]] { β } :: φ)
        with lookup_field_in_type s ty f :=
        {
        | Some fld
            with is_object_type s fld.(return_type) :=
            {
            | true := f[[α]] { normalize_selections fld.(return_type) (β ++ merge_selection_sets (find_queries_with_label s f ty φ)) }
                                 :: normalize_selections ty (filter_queries_with_label f φ);
            | _ := f[[α]] { [seq on t { normalize_selections t (β ++ merge_selection_sets (find_queries_with_label s f ty φ)) } | t <- get_possible_types s fld.(return_type)] } ::
                              normalize_selections ty (filter_queries_with_label f φ)
            };
        
        | _ => normalize_selections ty φ
        };
      
      normalize_selections ty (l:f[[α]] { β } :: φ)
        with lookup_field_in_type s ty f :=
        {
        | Some fld
            with is_object_type s fld.(return_type) :=
            {
            | true := l:f[[α]] { normalize_selections fld.(return_type) (β ++ merge_selection_sets (find_queries_with_label s l ty φ)) }
                                        :: normalize_selections ty (filter_queries_with_label l φ);
            | _ := l:f[[α]] { [seq on t { normalize_selections t (β ++ merge_selection_sets (find_queries_with_label s l ty φ)) } | t <- get_possible_types s fld.(return_type)] }
                     :: normalize_selections ty (filter_queries_with_label l φ)
            };
        
        | _ => normalize_selections ty φ
        };
        
      
      normalize_selections ty (on t { β } :: φ)
        with does_fragment_type_apply s ty t :=
        {
        | true := normalize_selections ty (β ++ φ);
        | _ := normalize_selections ty φ
        }

    }.
  Proof. 
    all: do [leq_queries_size].
  Qed.

  (** ---- *)
  (**
     #<strong>gnormalize_selections</strong># : Name → List Selection → List Selection 

     Normalizes a list of selections.
     
     Unlike [normalize_selections], this definition does not assume that the type given 
     is an object type. It only checks the type and either calls [normalize_selections] 
     on the list of selections if the type is an object type, or wraps them
     in fragments with type conditions equal to the given type's subtypes 
     (minus the abstract type itself).
   *)
  Definition gnormalize_selections (type_in_scope : Name) (queries : seq (@Selection Vals)) :
    seq (@Selection Vals) :=
    if is_object_type s type_in_scope then
      normalize_selections type_in_scope queries
    else
      [seq on t { normalize_selections t queries } | t <- get_possible_types s type_in_scope].


  (** ---- *)
  (**
     #<strong>normalize</strong># : Query → Query 

     Normalizes a query, using the Query type to normalize the selection set.
   *)
  Definition normalize (q : @query Vals) : @query Vals :=
    let: Query n ss := q in
    Query n (normalize_selections s.(query_type) q.(selection_set)).
  
  (** ---- *)
End Normalisation.

Arguments normalize_selections [Vals].
Arguments gnormalize_selections [Vals].
Arguments normalize [Vals].


(** ---- *)
(** 
    #<div>
        <a href='GraphCoQL.SelectionConformance.html' class="btn btn-light" role='button'> Previous ← Selection Conformance  </a>
        <a href='GraphCoQL.Graph.html' class="btn btn-info" role='button'>Continue Reading → GraphQL Graph </a>
    </div>#
*)