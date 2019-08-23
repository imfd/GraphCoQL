Require Import List.
From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

Require Import String.
Require Import QString.

Require Import Base.
Require Import Query.
Require Import QueryAux.
Require Import SchemaWellFormedness.

Require Import Schema.
Require Import SchemaAux.

Require Import QueryConformance.

Require Import SeqExtra.

Require Import Ssromega.

Section NRGTNF.

  Variables Vals : eqType.
  Variables (s : @wfGraphQLSchema Vals).
  
  Implicit Type queries : seq (@Query Vals).
  Implicit Type query : @Query Vals.
  
  
  
  (**
     is_grounded : Query → Bool 
     are_grounded_fields : List Query → Bool
     are_grounded_inlines : List Query → Bool
     are_grounded : List Query → Bool

     Checks whether the given queries are in ground-typed normal form.
     
     This follows the definition as specified in Jorge and Olaf's paper.
     As per their definition, there is no restriction over the kind of queries in
     the subqueries of a field selection; they can either be all fragments or all fields.
     This means that if there are two occurrences of the same field, its subqueries can 
     be fields in the first ocurrence and inline fragments in the second one.

     Example:

     query {
           friends {
                   name 
                   age 
           }
           friends {
                   ... on Human {
                       name
                       age
                   }
                   ... on Droid {
                       name
                       age
                   }
           }
    } 

    Both queries are in ground-typed normal form, but in the first case, 
    its subqueries are all fields, while in the second one, all are inline 
    fragments.
    
    This looseness in the definition made it a bit harder to reason about, 
    basically because there is no way of telling how your queries are structured
    and what you can apply on them (this mostly appeared during the proof that 
    the normalization function returned a grounded query).
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



  (**
     is_grounded2 : Name → Query → Bool 
     are_grounded2 : Name → List Query → Bool

     Checks whether the given query is in ground-typed normal form v2.0.
     
     This notion of groundness is a stronger definition of groundness than the one in 
     Jorge and Olaf's paper. This definition uses information of the type where the queries 
     are defined to determine the kind of queries allowed (fragments or fields).
     
     The main difference wrt. to the original definition is that subqueries of field 
     selections must all be inline fragments IF the return type of the field is an Abstract 
     type, and if the return type is an Object type, then all its subqueries must be fields.

     The reason behind this decision is the following:
     
     If we are querying something that is an object, then it doesn't make sense 
     that you may want to specialize the query with inline fragments.
     On the other hand, if you are querying something that is abstract, then a priori you don't 
     know which object that implements the interface will be used to evaluate the query. 
     Therefore, you want to cover all possible implementors with inline fragments.
     
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


  (**
     are_similar : Query → Query → Bool
     
     Checks whether two queries might produce the same response.
     
     This is used when checking that queries are non-redundant, as per 
     the definition in Jorge and Olaf's paper. 

   *)
  (* TODO : Rename? *)
  Equations are_similar (q1 q2 : @Query Vals) : bool :=
    {
      are_similar (on t { _ }) (on t' { _ }) := t == t';
      are_similar (on _ { _ }) _ := false;
      are_similar _ (on _ { _ }) := false;
      are_similar q1 q2 := ((qresponse_name q1 _) == (qresponse_name q2 _)) && ((qargs q1 _) == (qargs q2 _))
    }.

  (**
     are_non_redundant : List Query → Bool 

     Checks whether the list of queries are non-redundant, as per
     the definition in Jorge and Olaf's paper.
     
     #### Observations
     1. Response name check : Differently from the definition by J&O, 
        we check that two queries share their _response name_. In their paper, 
        they check unaliased field selections between themselves, but they 
        do not check whether an aliased field might be "equal" to an unaliased one.
        
        Example: 
                 f[α] & f[α] are redundant.

                 l:f[α] & l:f[α] are redundant.

                 f:_[α] & f[α] are not redundant (as per J&O), even though they may produce the same result. 

      

     ----
     See also:
     
     https://graphql.github.io/graphql-spec/June2018/#sec-Field-Selection-Merging

     https://graphql.github.io/graphql-spec/June2018/#FieldsInSetCanMerge()
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


  
  
  (**
     are_in_normal_form : List Query → Bool 

     Checks whether a list of queries are in normal form.

     We differ from the naming used in J&O, where they use "normal form" 
     when referring to the _ground-typed normal form_. We use it instead, 
     to refer to both a query that is non-redundant and in ground form.

   *)
  Definition are_in_normal_form queries := are_grounded queries && are_non_redundant queries.


  
End NRGTNF.

Arguments is_grounded [Vals].
Arguments are_grounded_fields [Vals].
Arguments are_grounded_inlines [Vals].
Arguments are_grounded [Vals].
Arguments is_grounded2 [Vals].
Arguments are_grounded2 [Vals].
Arguments are_non_redundant [Vals].


Arguments are_similar [Vals].

Arguments are_in_normal_form [Vals].