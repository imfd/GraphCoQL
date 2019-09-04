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
  
  Implicit Type queries : seq (@Query Vals).
  Implicit Type query : @Query Vals.
  

  (** * Definitions *)
  
  (** ** Groundness
      In this section we define the predicates to establish when a 
      GraphQL Query is grounded.
   *)
  (** ---- *)
  (**
     #<strong>is_grounded</strong># : Query → Bool 

     #<strong>are_grounded_fields</strong># : List Query → Bool

     #<strong>are_grounded_inlines</strong># : List Query → Bool

     #<strong>are_grounded</strong># : List Query → Bool

     #<div class="hidden-xs hidden-md hidden-lg"><br></div>#

     Checks whether the given queries are grounded.

     Differently from Pérez & Hartig, we call this property _groundness_ and not 
     include the _normal form_ part in the name.
   *)
  Equations is_grounded query : bool  :=
    {
      is_grounded (_[[_]] { φ }) := are_grounded φ;
      
      is_grounded (_:_[[_]] { φ }) := are_grounded φ;
      
      is_grounded (on t { φ }) := (is_object_type s t) && are_grounded_fields φ;
      
      is_grounded  _ := true
    }
 
  where are_grounded_fields queries : bool :=
          {
            are_grounded_fields [::] := true;
            are_grounded_fields (q :: φ) := [&& q.(is_field), q.(is_grounded) & are_grounded_fields φ]
          }

  where are_grounded_inlines queries : bool :=
          {
            are_grounded_inlines [::] := true;
            are_grounded_inlines (q :: φ) := [&& q.(is_inline_fragment), q.(is_grounded) & are_grounded_inlines φ]
          }
 
  where are_grounded queries : bool :=
          {
            are_grounded [::] := true;
            are_grounded (q :: φ) := q.(is_grounded) && if q.(is_field) then are_grounded_fields φ else are_grounded_inlines φ
                                                                                                                              
          }.


  (** ---- *)
  (**
     #<strong>is_grounded2</strong># : Name → Query → Bool 

     #<strong>are_grounded2</strong># : Name → List Query → Bool

     #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
     Checks whether the given query is grounded v.2.0.
     
     This predicate uses information on the type in context where queries might be defined.
     - If the type in context is an Object type, then it expects to find only fields.
     - If the type in context is an Abstract type, then it expects to find only fragments.
     
   *)
  (* TODO : Rename ! *)
  Equations is_grounded2 (type_in_scope : Name) (query : @Query Vals) : bool :=
    {
      is_grounded2 ty (f[[_]] { φ })
        with lookup_field_in_type s ty f :=
        {
        | Some fld := are_grounded2 fld.(return_type) φ;
        | _ := false
        };

      is_grounded2 ty (_:f[[_]] { φ })
        with lookup_field_in_type s ty f :=
        {
        | Some fld := are_grounded2 fld.(return_type) φ;
        | _ := false
        };

      is_grounded2 ty (on t { φ }) := (is_object_type s t) && are_grounded2 t φ;
      
      is_grounded2 _ _ := true
    }
   where
   are_grounded2 (type_in_scope : Name) (queries : seq (@Query Vals)) : bool :=
     {
       are_grounded2 _ [::] := true;
       
       are_grounded2 ty (hd :: tl)
         with is_object_type s ty :=
         {
         | true  := [&& is_field hd, is_grounded2 ty hd & are_grounded2 ty tl];
         | _ := [&& is_inline_fragment hd, is_grounded2 ty hd & are_grounded2 ty tl]
         }
     }.


  (** ** Non-redundancy
      
      In this section we define the predicate to establish when a GraphQL Query 
      is non-redundant.
   *)
  (** ---- *)
  (**
     #<strong>are_non_redundant</strong># : List Query → Bool 

     Checks whether the list of queries are non-redundant.
     This checks that :
     - There are no inline fragments with the same type condition.
     - There are no field selections with the same response name.
   *)
  Equations? are_non_redundant (queries : seq (@Query Vals)) : bool
    by wf (queries_size queries) :=
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
    all: do ? intros; simp query_size; ssromega.
  Qed.


  
  (** ---- *)
  (**
     #<strong>are_in_normal_form</strong># : List Query → Bool 

     Checks whether a list of queries are in normal form.

     We differ from the naming used in J&O, where they use "normal form" 
     when referring to the _ground-typed normal form_. We use it instead, 
     to refer to both a query that is non-redundant and in ground form.

   *)
  Definition are_in_normal_form queries := are_grounded queries && are_non_redundant queries.


  (** ---- *)  
End NormalForm.

Arguments is_grounded [Vals].
Arguments are_grounded_fields [Vals].
Arguments are_grounded_inlines [Vals].
Arguments are_grounded [Vals].
Arguments is_grounded2 [Vals].
Arguments are_grounded2 [Vals].
Arguments are_non_redundant [Vals].
Arguments are_in_normal_form [Vals].



Section Normalisation.

  Variables Vals : eqType.
  Implicit Type schema : @wfGraphQLSchema Vals.
  Implicit Type query : @Query Vals.


  Variable s : @wfGraphQLSchema Vals.

  (** * Normalisation
      
      In this section we will define a normalisation procedure, which 
      takes a GraphQL Query and outputs another one in normal form.
      
      The proof of this is in the file _QueryNormalizationLemmas_.
   *)
  (** ---- *)
  (**
     #<strong>normalize</strong># : Name → List Query → List Query 

     Normalizes the given list of queries. 
     The resulting list of queries are non-redundant and in ground-type 
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
  Equations? normalize (type_in_scope : Name) (queries : seq (@Query Vals)) :
    seq (@Query Vals) by wf (queries_size queries) :=
    {
      normalize _ [::] := [::];

      normalize ty (f[[α]] :: φ)
        with lookup_field_in_type s ty f :=
        {
        | Some _ := f[[α]] :: normalize ty (filter_queries_with_label f φ);
        | _ := normalize ty φ
        };
      
      normalize ty (l:f[[α]] :: φ)
        with lookup_field_in_type s ty f :=
        {
        | Some _ := l:f[[α]] :: normalize ty (filter_queries_with_label l φ);
        | _ := normalize ty φ
        };

      normalize ty (f[[α]] { β } :: φ)
        with lookup_field_in_type s ty f :=
        {
        | Some fld
            with is_object_type s fld.(return_type) :=
            {
            | true := f[[α]] { normalize fld.(return_type) (β ++ merge_selection_sets (find_queries_with_label s f ty φ)) }
                                 :: normalize ty (filter_queries_with_label f φ);
            | _ := f[[α]] { [seq on t { normalize t (β ++ merge_selection_sets (find_queries_with_label s f ty φ)) } | t <- get_possible_types s fld.(return_type)] } ::
                              normalize ty (filter_queries_with_label f φ)
            };
        
        | _ => normalize ty φ
        };
      
      normalize ty (l:f[[α]] { β } :: φ)
        with lookup_field_in_type s ty f :=
        {
        | Some fld
            with is_object_type s fld.(return_type) :=
            {
            | true := l:f[[α]] { normalize fld.(return_type) (β ++ merge_selection_sets (find_queries_with_label s l ty φ)) }
                                        :: normalize ty (filter_queries_with_label l φ);
            | _ := l:f[[α]] { [seq on t { normalize t (β ++ merge_selection_sets (find_queries_with_label s l ty φ)) } | t <- get_possible_types s fld.(return_type)] }
                     :: normalize ty (filter_queries_with_label l φ)
            };
        
        | _ => normalize ty φ
        };
        
      
      normalize ty (on t { β } :: φ)
        with does_fragment_type_apply s ty t :=
        {
        | true := normalize ty (β ++ φ);
        | _ := normalize ty φ
        }

    }.
  Proof. 
    all: do [leq_queries_size].
  Qed.

  (** ---- *)
  (**
     #<strong>normalize_queries</strong># : Name → List Query → List Query 

     Normalizes a list of queries.
     
     Unlike [normalize], this definition does not assume that the type given 
     is an Object type. It only checks the type and either calls [normalize] 
     on the list of queries if the type is an Object type, or wraps the queries
     in fragments with type conditions equal to the given type's subtypes 
     (minus the abstract type itself).
   *)
  Equations normalize_queries (type_in_scope : Name) (queries : seq (@Query Vals)) :
    seq (@Query Vals) :=
    {
      normalize_queries ty qs
        with is_object_type s ty :=
        {
              | true := normalize ty qs;
              | _ := [seq on t { normalize t qs } | t <- get_possible_types s ty]
        }
    }.


  (** ---- *)
End Normalisation.


Arguments normalize [Vals].
Arguments normalize_queries [Vals].


(** ---- *)
(** 
    #<div>
        <a href='GraphCoQL.QueryConformance.html' class="btn btn-light" role='button'> Previous ← Query Conformance  </a>
        <a href='GraphCoQL.Graph.html' class="btn btn-info" role='button'>Continue Reading → GraphQL Graph </a>
    </div>#
*)