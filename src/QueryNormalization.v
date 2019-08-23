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

Section QueryRewrite.

  Variables Vals : eqType.
  Implicit Type schema : @wfGraphQLSchema Vals.
  Implicit Type query : @Query Vals.


  Variable s : @wfGraphQLSchema Vals.
  

  (**
     normalize : Name → List Query → List Query 

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
        possible subtype of the given abstract type (minus itself). This means 
        that fragments might be "lifted" (its type condition is removed and its 
        subqueries lifted) or removed if they do not make sense in the context
        (See discussion in [is_field_merging_possible]). On the other hand,
        fields' subqueries might be wrapped in fragments, specializing their contents.


     This definition assumes that the given type in scope is actually an Object type.
     The following definition, [normalize_queries], does not make an assumption about
     the type in scope, but still relies on this normalization function.
     
     - ty : Type in scope (Object type).

     - lookup (f) : Searches the field definition with name "f" in ty.

     - filter f φ : filters every field selection with response name "f" in φ (see [filter_queries_with_label]).

     - collect ty f φ : finds every field selection with response name "f" in φ (see [find_queries_with_label]).

     - merge φ : Extracts subqueries of queries in φ (see [merge_selection_sets]).

     - Not showing aliased fields because they are the same as unaliased.



         normalize [] := []
                                               ⎧
         normalize ty (f[α] :: φ_1 ... φ_n) := ⎨ f[α] :: (normalize ty (filter f (φ_1 ... φ_n)))   if (lookup (f) = f (Args) : rty)
                                               |
                                               ⎩  normalize ty (φ_1 ... φ_n)                       if (lookup (f) = ⊥)

                                                
                                                                ⎧
         normalize ty (f[α] { β_1 ... β_k } :: φ_1 ... φ_n) :=  ⎨ f [α] { normalize rty (β1 ... β_k ++ merge (collect ty f (φ_1 ... φ_n))) } :: (normalize ty (filter f (φ_1 ... φ_n))) 
                                                                |
                                                                |         if (lookup (f) = f (Args) : rty) ∧ ty ∈ Ot 
                                                                | 
                                                                | 
                                                                | f [α] { map (λ t => normalize t (β1 ... β_k ++ merge (collect ty f (φ_1 ... φ_n)))) (get_possible_types ty) }
                                                                |     :: (normalize ty (filter f (φ_1 ... φ_n))) 
                                                                |
                                                                |         if (lookup (f) = f (Args) : rty) ∧ rty ∈ At
                                                                |
                                                                |
                                                                | normalize ty (φ_1 ... φ_n)                  if (lookup (f) = ⊥)
                                                                ⎩
               
                                                               ⎧
         normalize ty (on t { β_1 ... β_k } :: φ_1 ... φ_n) := ⎨ normalize ty (β_1 ... β_k ++ φ_1 ... φ_n)       if (does_fragment_type_apply ty t) 
                                                               |
                                                               |        
                                                               | normalize ty (φ_1 ... φ_n)                      ~
                                                               ⎩

                                               
     #### Observations 
     1. Split : In a previous version we attempted to split the normalization 
        process into these two steps; removing redundancies and grounding.
        This separation made the proof of semantics preservation actually harder,
        resulting in inductive hypotheses that would not be directly usable.
        Presumably it was due to the non compositional definition of the semantics vs.
        the more compositional (not entirely...) of the other definitions.


     2. J&O : 
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


  (**
     normalize_queries : Name → List Query → List Query 

     Normalizes a list of queries.
     
     Unlike [normalize], this definition does not assume that the type given 
     is an Object type. It only checks the type and either calls [normalize] 
     on the list of queries if the type is an Object type, or wraps the queries
     in fragments with type conditions equal to the given type's subtypes 
     (minus itself).

                                        ⎧
     normalize_queries ty (φ_1 ... φ_n) := ⎨ normalize ty (φ_1 ... φ_n)                                                    if (ty ∈ Ot)
                                        |
                                        | map (λ t => on t { normalize t (φ_1 ... φ_n) }) (get_possible_types ty)       ~
                                        ⎩


   *)
  (* TODO : Rename ! *)
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

 
End QueryRewrite.


Arguments normalize [Vals].
Arguments normalize_queries [Vals].