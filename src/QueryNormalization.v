From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From Equations Require Import Equations.


Require Import Base.
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

Section QueryRewrite.

  Variables Vals : eqType.
  Implicit Type schema : @wfGraphQLSchema Vals.
  Implicit Type query : @Query Vals.


  Variable s : @wfGraphQLSchema Vals.
  

  
  (* Supposed to be applied over an object type *)
  Equations? reground (type_in_scope : Name) (queries : seq (@Query Vals)) :
    seq (@Query Vals) by wf (queries_size queries) :=
    {
      reground _ [::] := [::];

      reground ty (f[[α]] :: φ)
        with lookup_field_in_type s ty f :=
        {
        | Some _ := f[[α]] :: reground ty (filter_queries_with_label f φ);
        | _ := reground ty φ
        };
      
      reground ty (l:f[[α]] :: φ)
        with lookup_field_in_type s ty f :=
        {
        | Some _ := l:f[[α]] :: reground ty (filter_queries_with_label l φ);
        | _ := reground ty φ
        };

      reground ty (f[[α]] { β } :: φ)
        with lookup_field_in_type s ty f :=
        {
        | Some fld
            with is_object_type s fld.(return_type) :=
            {
            | true := f[[α]] { reground fld.(return_type) (β ++ merge_selection_sets (find_queries_with_label s f ty φ)) }
                                 :: reground ty (filter_queries_with_label f φ);
            | _ := f[[α]] { [seq on t { reground t (β ++ merge_selection_sets (find_queries_with_label s f ty φ)) } | t <- get_possible_types s fld.(return_type)] } ::
                              reground ty (filter_queries_with_label f φ)
            };
        
        | _ => reground ty φ
        };
      
      reground ty (l:f[[α]] { β } :: φ)
        with lookup_field_in_type s ty f :=
        {
        | Some fld
            with is_object_type s fld.(return_type) :=
            {
            | true := l:f[[α]] { reground fld.(return_type) (β ++ merge_selection_sets (find_queries_with_label s l ty φ)) }
                                        :: reground ty (filter_queries_with_label l φ);
            | _ := l:f[[α]] { [seq on t { reground t (β ++ merge_selection_sets (find_queries_with_label s l ty φ)) } | t <- get_possible_types s fld.(return_type)] }
                     :: reground ty (filter_queries_with_label l φ)
            };
        
        | _ => reground ty φ
        };
        
      
      reground ty (on t { β } :: φ)
        with does_fragment_type_apply s ty t :=
        {
        | true := reground ty (β ++ φ);
        | _ := reground ty φ
        }

    }.
  Proof.
    all: do [leq_queries_size].
  Qed.

  Equations ground_queries (type_in_scope : Name) (queries : seq (@Query Vals)) :
    seq (@Query Vals) :=
    {
      ground_queries ty qs
        with is_object_type s ty :=
        {
              | true := reground ty qs;
              | _ := [seq on t { reground t qs } | t <- get_possible_types s ty]
        }
    }.

 
End QueryRewrite.


Arguments reground [Vals].
Arguments ground_queries [Vals].