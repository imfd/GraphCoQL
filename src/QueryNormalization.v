(* begin hide *)

From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From Equations Require Import Equations.


Require Import Schema.
Require Import SchemaAux.
Require Import SchemaWellFormedness.
Require Import Query.
Require Import QueryAux.
Require Import QueryAuxLemmas.
Require Import QueryConformance.


Require Import NRGTNF.

Require Import Ssromega.

Require Import SeqExtra.

Require Import QueryTactics.

(* end hide *)

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">Query Normalisation</h1>
        <p class="lead">
         This file contains the definition of the normalisation procedure.
        </p>
         
  </div>
</div>#
 *)

Section QueryRewrite.

  Variables Vals : eqType.
  Implicit Type schema : @wfGraphQLSchema Vals.
  Implicit Type query : @Query Vals.


  Variable s : @wfGraphQLSchema Vals.
  
  (** ---- *)
  (**
     #<strong>normalize</strong># : Name → List Query → List Query 

     Normalizes the given list of queries. 
     The resulting list of queries are non-redundant and in ground-type 
     normal form.
     
     Normalization consists of two main processes :
     
     1. Eliminating redundancies via merging : Fields which share 
        a response name are collapsed/collected into the first occurrence of 
        this set of common fields. This resembles the process carried out 
        by the semantics (CollectFields & MergeSelectionSets).

     2. Grounding : Queries which are supposed to occur in abstract types 
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
End QueryRewrite.


Arguments normalize [Vals].
Arguments normalize_queries [Vals].



(** ---- *)
(** 
    #<div>
        <a href='GraphCoQL.NRGTNF.html' class="btn btn-light" role='button'> Previous ← Non-redundancy and Groundness  </a>
        <a href='GraphCoQL.Graph.html' class="btn btn-info" role='button'>Continue Reading → GraphQL Graph</a>
    </div>#
*)