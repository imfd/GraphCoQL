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
         This file contains the basic predicates for groundedness and non-redundancy of queries,
         and also contains the normalization procedure.
        </p>
         
  </div>
</div>#
 *)


(** * Definitions *)
(** ---- *)
Section NormalForm.

  Variables Scalar : eqType.
  Variables (s : wfGraphQLSchema).
  
  Implicit Type σs : seq (@Selection Scalar).
  Implicit Type σ : @Selection Scalar.
  

  
  (** ** Groundedness
      ----

      In this section we define the predicates to establish when a 
      GraphQL Selection is in ground-typed normal form (grounded for short).
   *)
  (**
     Checks whether the given selection is in ground-typed normal form, as defined in H&P.
     
     A selection set σ̅ is in ground-typed normal form if it satisfies the following grammar, 
     where t is an object type.
     
     #<img src='../imgs/GTNF/gtnf.png' class='img-fluid' alt='Ground-typed normal form grammar'>#     
   *)
  Fixpoint is_in_ground_typed_nf (σ : @Selection Scalar) : bool :=
    match σ with
    | _[[_]] { σs } => (all (fun s => s.(is_field)) σs || all (fun s => s.(is_inline_fragment)) σs) && all is_in_ground_typed_nf σs
    | _:_[[_]] { σs } => (all (fun s => s.(is_field)) σs || all (fun s => s.(is_inline_fragment)) σs) && all is_in_ground_typed_nf σs  
    | on t { σs } => is_object_type s t && all (fun s => s.(is_field) && s.(is_in_ground_typed_nf)) σs
    | _ => true
    end.

  (** ---- *)
  (**
     Checks whether the given selection set is in ground-typed normal form, as defined in H&P.
   *)
  Definition are_in_ground_typed_nf (σs : seq (@Selection Scalar)) : bool :=
    (all (@is_field Scalar) σs || all (@is_inline_fragment Scalar) σs) && all is_in_ground_typed_nf σs.

  (** ---- *)
  (**
     Checks whether the given query is in ground-typed normal form, by checking that its selection set is
     in ground-typed normal form.
   *)
  Definition is_a_ground_typed_nf_query (φ : @query Scalar) :=
    φ.(selection_set).(are_in_ground_typed_nf).
  
   


  (** ** Non-redundancy
      ----

      In this section we define the predicate to establish when a GraphQL Selection 
      is non-redundant.
   *)
  (**
     Checks whether a selection set is non-redundant.
     This checks that :
     - There are no inline fragments with the same type condition.
     - There are no field selections with the same response name.
   *)
  Equations? are_non_redundant (σs : seq (@Selection Scalar)) : bool
    by wf (selections_size σs) :=
    {
      are_non_redundant [::] := true;
      
      are_non_redundant (on t { β } :: σs) :=
        [&& find_fragment_with_type_condition t σs == [::],
            are_non_redundant β &
            are_non_redundant σs];

      are_non_redundant (q :: σs) :=
        [&& find_fields_with_response_name (qresponse_name q _) σs == [::],
            are_non_redundant q.(subselections) &
            are_non_redundant σs]

    }.                 
  Proof.
    all: do ? [case: q].
    all: do ? intros; simp selection_size; ssromega.
  Qed.


  (** ---- *)
  (**
     Checks whether a query is non-redundant by checking that its selection set is 
     non-redundant.
   *)
  Definition is_non_redundant (φ : @query Scalar) : bool := φ.(selection_set).(are_non_redundant).

  
  (** ** Normal form *)
  (** ---- *)
                                                
  (**
     Checks whether a selection set is in normal form.
   *)
  Definition are_in_normal_form (σs : seq Selection) :=
    σs.(are_in_ground_typed_nf) && σs.(are_non_redundant).
    
  (** ---- *)
  (**
     Checks whether a query is in normal form.
   *)
  Definition is_in_normal_form (φ : @query Scalar) := φ.(selection_set).(are_in_normal_form).


End NormalForm.


(* begin hide *)
Arguments is_in_ground_typed_nf [Scalar].
Arguments are_in_ground_typed_nf [Scalar].
Arguments is_a_ground_typed_nf_query [Scalar].

Arguments are_non_redundant [Scalar].
Arguments is_non_redundant [Scalar].

Arguments are_in_normal_form [Scalar].
Arguments is_in_normal_form [Scalar].
(* end hide *)


(** * Normalization
    ----
      
      In this section we will define a normalization procedure, which 
      takes a GraphQL Selection and outputs another one in normal form.
      
   *)
Section Normalization.

  Variables Scalar : eqType.
  
  Implicit Type σ : @Selection Scalar.


  Variable s : wfGraphQLSchema.

  (**
     Normalizes the given list of selections. 
     The resulting list are non-redundant and in ground-type 
     normal form.
     
     Normalization consists of two main processes :
     
     - Eliminating redundancies via merging : Fields which share 
        a response name are collapsed/collected into the first occurrence of 
        this set of common fields. This resembles the process carried out 
        by the semantics in _CollectFields_ (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##CollectFields()'><span>&#167;</span>6.3.2</a>#)
        and _MergeSelectionSets_ (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##MergeSelectionSets()'><span>&#167;</span>6.4.3</a>#).

     - Grounding : Queries which are supposed to occur in abstract types 
        (be it an inline fragment with an abstract type condition or a    
        field with an abstract return type) are specialized into every
        possible concrete object subtype.
        This means that fragments might be "lifted" (its type condition is removed and its 
        subselections lifted) or removed if they do not make sense in the context
        On the other hand, fields' subselections might be wrapped in fragments, specializing their contents.
   *)
  Equations? normalize_selections (type_in_scope : Name) (σs : seq (@Selection Scalar)) :
    seq (@Selection Scalar) by wf (selections_size σs) :=
    {
      normalize_selections _ [::] := [::];

      normalize_selections ty (f[[α]] :: σs)
        with lookup_field_in_type s ty f :=
        {
        | Some _ := f[[α]] :: normalize_selections ty (filter_fields_with_response_name f σs);
        | _ := normalize_selections ty σs
        };
      
      normalize_selections ty (l:f[[α]] :: σs)
        with lookup_field_in_type s ty f :=
        {
        | Some _ := l:f[[α]] :: normalize_selections ty (filter_fields_with_response_name l σs);
        | _ := normalize_selections ty σs
        };

      normalize_selections ty (f[[α]] { β } :: σs)
        with lookup_field_in_type s ty f :=
        {
        | Some fld
            with is_object_type s fld.(ftype) :=
            {
            | true := f[[α]] { normalize_selections fld.(ftype) (β ++ merge_selection_sets (find_valid_fields_with_response_name s f ty σs)) }
                                 :: normalize_selections ty (filter_fields_with_response_name f σs);
            | _ := f[[α]] { [seq on t { normalize_selections t (β ++ merge_selection_sets (find_valid_fields_with_response_name s f ty σs)) } | t <- get_possible_types s fld.(ftype)] } ::
                              normalize_selections ty (filter_fields_with_response_name f σs)
            };
        
        | _ => normalize_selections ty σs
        };
      
      normalize_selections ty (l:f[[α]] { β } :: σs)
        with lookup_field_in_type s ty f :=
        {
        | Some fld
            with is_object_type s fld.(ftype) :=
            {
            | true := l:f[[α]] { normalize_selections fld.(ftype) (β ++ merge_selection_sets (find_valid_fields_with_response_name s l ty σs)) }
                                        :: normalize_selections ty (filter_fields_with_response_name l σs);
            | _ := l:f[[α]] { [seq on t { normalize_selections t (β ++ merge_selection_sets (find_valid_fields_with_response_name s l ty σs)) } | t <- get_possible_types s fld.(ftype)] }
                     :: normalize_selections ty (filter_fields_with_response_name l σs)
            };
        
        | _ => normalize_selections ty σs
        };
        
      
      normalize_selections ty (on t { β } :: σs)
        with does_fragment_type_apply s ty t :=
        {
        | true := normalize_selections ty (β ++ σs);
        | _ := normalize_selections ty σs
        }

    }.
  Proof. 
    all: do [leq_selections_size].
  Qed.


  (** ---- *)
  (**
     Normalizes a query, using the _Query_ type to normalize the selection set.
   *)
  Definition normalize (φ : @query Scalar) : @query Scalar :=
    let: Query n ss := φ in
    Query n (normalize_selections s.(query_type) φ.(selection_set)).
  
End Normalization.

(* begin hide *)
Arguments normalize_selections [Scalar].
Arguments normalize [Scalar].
(* end hide *)

(** ---- *)
(** 
    #<div>
        <a href='GraphCoQL.QueryConformance.html' class="btn btn-light" role='button'> Previous ← Query Conformance  </a>
        <a href='GraphCoQL.theory.QueryNormalFormLemmas.html' class="btn btn-info" role='button'>Continue Reading → Normal Form Proofs </a>
    </div>#
*)