(* begin hide *)

Require Import List.
From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

Require Import String.
Require Import QString.

Require Import Query.
Require Import QueryAux.
Require Import SchemaWellFormedness.

Require Import Schema.
Require Import SchemaAux.

Require Import QueryConformance.

Require Import SeqExtra.

Require Import Ssromega.

(* end hide *)

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">Non-redundant Ground-typed Normal Form</h1>
        <p class="lead">
         This file contains the necessary definitions to establish when a GraphQL
         Query is non-redundant and in ground-typed normal form.
        </p>
         
  </div>
</div>#
 *)

Section NRGTNF.

  Variables Vals : eqType.
  Variables (s : @wfGraphQLSchema Vals).
  
  Implicit Type queries : seq (@Query Vals).
  Implicit Type query : @Query Vals.
  
  
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
End NRGTNF.

Arguments is_grounded [Vals].
Arguments are_grounded_fields [Vals].
Arguments are_grounded_inlines [Vals].
Arguments are_grounded [Vals].
Arguments is_grounded2 [Vals].
Arguments are_grounded2 [Vals].
Arguments are_non_redundant [Vals].
Arguments are_in_normal_form [Vals].

(** ---- *)
(** 
    #<div>
        <a href='GraphCoQL.QueryConformance.html' class="btn btn-light" role='button'> Previous ← Query Conformance  </a>
        <a href='GraphCoQL.QueryNormalization.html' class="btn btn-info" role='button'>Continue Reading → Normalisation </a>
    </div>#
*)