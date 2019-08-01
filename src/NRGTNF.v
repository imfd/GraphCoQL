Require Import List.
From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.
From extructures Require Import ord fmap fset.


Require Import Query.
Require Import QueryAux.
Require Import SchemaWellFormedness.

Require Import Schema.
Require Import SchemaAux.

Require Import QueryConformance.

Require Import SeqExtra.

Require Import Ssromega.

Section NRGTNF.

  Variables Name Vals : ordType.
  Variables (s : @wfSchema Name Vals).
  
  Implicit Type queries : seq (@Query Name Vals).
  Implicit Type query : @Query Name Vals.
  
  
  
  
  Equations is_grounded query : bool  :=
    {
      is_grounded (NestedField _ _ φ) := are_grounded φ;
      
      is_grounded (NestedLabeledField _ _ _ φ) := are_grounded φ;
      
      is_grounded (InlineFragment t φ) := (is_object_type s t) && are_grounded_fields φ; (* (all is_field φ) & all is_grounded φ *)
      
      is_grounded  _ := true
    }
  where are_grounded_fields queries : bool :=
          {
            are_grounded_fields [::] := true;
            are_grounded_fields (q :: qs) := [&& q.(is_field), q.(is_grounded) & are_grounded_fields qs]
          }
  where are_grounded_inlines queries : bool :=
          {
            are_grounded_inlines [::] := true;
            are_grounded_inlines (q :: qs) := [&& q.(is_inline_fragment), q.(is_grounded) & are_grounded_inlines qs]
          }
  where are_grounded queries : bool :=
          {
            are_grounded [::] := true;
            are_grounded (q :: qs) := q.(is_grounded) && if q.(is_field) then are_grounded_fields qs else are_grounded_inlines qs
                                                                                                                              
          }.

 
  Equations is_grounded2 (type_in_scope : Name) (query : @Query Name Vals) : bool :=
    {
      is_grounded2 ty (NestedField f _ φ)
        with lookup_field_in_type s ty f :=
        {
        | Some fld := are_grounded2 fld.(return_type) φ;
        | _ := false
        };

      is_grounded2 ty (NestedLabeledField _ f _ φ)
        with lookup_field_in_type s ty f :=
        {
        | Some fld := are_grounded2 fld.(return_type) φ;
        | _ := false
        };

      is_grounded2 ty (InlineFragment t φ) := (is_object_type s t) && are_grounded2 t φ;
      
      is_grounded2 _ _ := true
    }
   where
   are_grounded2 (type_in_scope : Name) (queries : seq (@Query Name Vals)) : bool :=
     {
       are_grounded2 _ [::] := true;
       are_grounded2 ty (hd :: tl)
         with is_object_type s ty :=
         {
         | true  := [&& is_field hd, is_grounded2 ty hd & are_grounded2 ty tl];
         | _ := [&& is_inline_fragment hd, is_grounded2 ty hd & are_grounded2 ty tl]
         }
     }.

  
  Equations are_similar (q1 q2 : @Query Name Vals) : bool :=
    {
      are_similar (InlineFragment t _) (InlineFragment t' _) := t == t';
      are_similar (InlineFragment _ _) _ := false;
      are_similar _ (InlineFragment _ _) := false;
      are_similar q1 q2 := ((qresponse_name q1 _) == (qresponse_name q2 _)) && ((qargs q1 _) == (qargs q2 _))
    }.
   
  Equations? are_non_redundant (queries : seq (@Query Name Vals)) : bool
    by wf (queries_size queries) :=
    {
      are_non_redundant [::] := true;
      
      are_non_redundant (hd :: tl) :=
        [&& all (fun q => ~~are_similar q hd) tl,
         are_non_redundant hd.(qsubqueries) &
         are_non_redundant tl]
    }.                 
  Proof.
    all: do [case: hd are_non_redundant; intros; simp query_size; ssromega].
  Qed.
  
  Definition is_non_redundant query :=
    are_non_redundant query.(qsubqueries).
  

  Definition are_in_normal_form queries := are_grounded queries && are_non_redundant queries.


  
End NRGTNF.

Arguments is_grounded [Name Vals].
Arguments are_grounded_fields [Name Vals].
Arguments are_grounded_inlines [Name Vals].
Arguments are_grounded [Name Vals].
Arguments is_grounded2 [Name Vals].
Arguments are_grounded2 [Name Vals].
Arguments are_non_redundant [Name Vals].
Arguments is_non_redundant  [Name Vals].

Arguments are_similar [Name Vals].

Arguments are_in_normal_form [Name Vals].