(* begin hide *)

From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

Require Import String.
Require Import QString.

Require Import Value.

Require Import Schema.
Require Import SchemaAux.
Require Import Query.
Require Import QueryAux.
Require Import QueryAuxLemmas.
Require Import SchemaWellFormedness.
Require Import SeqExtra.

Require Import QueryTactics.
Require Import Ssromega.

(* end hide *)


(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">Query Conformance</h1>
        <p class="lead">
         This file contains the necessary definitions to validate when a GraphQL Query
         is valid wrt. to a Schema. 
        </p>
         <p>
         This notion includes things such as: 
          <ul>
           <li> Field selection over a type is actually defined in that type. </li>
           <li> Arguments have valid names </li>
           <li> Inline fragments are applied on valid types </li>
           <li> Etc. </li>
         </ul>
        </p>
         <p>
         We will progressively define predicates that check different aspects of a query;
         check if an argument conforms, do fields merge, etc. 
         From these we will ultimately define the predicate for conformed queries.
        </p>
  </div>
</div>#
 *)


Section QueryConformance.

  Variables (Scalar : eqType)
            (is_valid_scalar_value : graphQLSchema -> Name -> Scalar -> bool).
  
  
  Implicit Type selections : seq (@Selection Scalar).
  Implicit Type selection : @Selection Scalar.


  Variable s : wfGraphQLSchema.
 
  (** * Conformance Predicates *)
  (** ---- *)
  
  (** ** Are selections consistent ?
      ----

      First we define the necessary predicates to establish that a query is consistent 
      by itself.
   *)
  
  (** *** Arguments conform  
      ----

      The following predicate checks whether a list of arguments (described as a pairing between names and values)
      conform to a list of field arguments.
      
      This is used when checking whether a field selection is consistent with a type in the schema.

      For a query argument to be valid it must satisfy the following:
      - There exists an argument definition with the same name (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Argument-Names'><span>&#167;</span>5.4.1</a>#).
      - The value given to the query argument must be valid w.r.t. its expected type (#<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Values-of-Correct-Type'><span>&#167;</span>5.6.1</a>#).      
     
   **)
  Definition arguments_conform (args : seq FieldArgumentDefinition) (α : seq (Name * @Value Scalar)) : bool :=
    let argument_conforms (arg : Name * @Value Scalar) : bool :=
        let: (name, value) := arg in
        has (fun argdef => (argdef.(argname) == name) && is_valid_value s is_valid_scalar_value argdef.(argtype) value) args
    in
    all argument_conforms α && uniq [seq arg.1 | arg <- α].
     





  (** ---- *)
  (** *** Is selection consistent ? 
    
      Checks whether a query is consistent to a given type in the schema.

      This checks the following:

      - Fields are defined in the type in scope (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Field-Selections-on-Objects-Interfaces-and-Unions-Types'><span>&#167;</span>5.3.1</a>#)

      - Field selection's arguments should conform to the arguments declared in the field definition obtained previously.

      - Leaf field selections should have Scalar or Enum return type (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Leaf-Field-Selections'><span>&#167;</span>5.3.3</a>#).

      - Node field selections should have Object, Interface or Union return type (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Leaf-Field-Selections'><span>&#167;</span>5.3.3</a>#).

      - Nested subqueries should not be empty (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Leaf-Field-Selections'><span>&#167;</span>5.3.3</a>#).

      - Nested subqueries should be consistent wrt. to its parent type (return type for fields or type condition for fragments).

      - Fragments' type condition must spread in the type in context (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Fragment-spread-is-possible'><span>&#167;</span>5.5.2.3</a>#).
     
   *)
  Fixpoint is_consistent (type_in_scope : Name) selection : bool :=
    match selection with
    | f[[α]] =>
      if lookup_field_in_type s type_in_scope f is Some fld then
        (is_scalar_type s fld.(return_type) || is_enum_type s fld.(return_type)) && arguments_conform fld.(fargs) α
      else
        false

    | _:f[[α]] =>
      if lookup_field_in_type s type_in_scope f is Some fld then
        (is_scalar_type s fld.(return_type) || is_enum_type s fld.(return_type)) && arguments_conform fld.(fargs) α
      else
        false

    | f[[α]] { φ } => 
      if lookup_field_in_type s type_in_scope f is Some fld then
        [&& (is_object_type s fld.(return_type) || is_abstract_type s fld.(return_type)),
         arguments_conform fld.(fargs) α,
         φ != [::] &
         all (is_consistent fld.(return_type)) φ]
      else
        false 

    | _:f[[α]] { φ } =>
      if lookup_field_in_type s type_in_scope f is Some fld then
        [&& (is_object_type s fld.(return_type) || is_abstract_type s fld.(return_type)),
         arguments_conform fld.(fargs) α,
         φ != [::] &
         all (is_consistent fld.(return_type)) φ]
      else
        false 

    | on t { φ } => [&& is_fragment_spread_possible s type_in_scope t,
                    φ != [::] &
                    all (is_consistent t) φ]
    end.
  


  (** ** Are selections type-compatible ?
      ----

      In this segment we define the necessary predicates to establish if selections 
      are type-compatible.

      Intuitively, this validation forbids selections with the same response name producing 
      results associated to values of different types 
      (e.g. a key associated to string values in one case and integer in others).
   *)

  (** ---- *)
  (**
    Checks whether two types are compatible. 
    
    This corresponds to steps 3-6 used in the spec's definition for _SameResponseShape_ 
    (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##SameResponseShape()'><span>&#167;</span>5.3.2</a>#).
    spec.  
  *)
  Fixpoint are_compatible_types (ty ty' : type) : bool :=
    match ty, ty' with
    | NamedType rty, NamedType rty' =>
      if (is_scalar_type s rty || is_enum_type s rty) then
        rty == rty'
      else
        is_composite_type s rty'
    | ListType rty, ListType rty' => are_compatible_types rty rty'
    | _, _ => false
    end.

  
 (** ---- *)
 (**
    Checks whether a given selection has a return type compatible to the 
    one given as parameter. 

    The first parameter corresponds to the type of another field to which we 
    wish to know if they are type compatible.

    The pair correspond to the selection along with the type where it was defined. 

    Inline fragments do not have a return type, therefore this always 
    returns false for these cases.
  *)
  Fixpoint has_compatible_type (rty : type) (nq : Name * @Selection Scalar) : bool :=
    match nq with
    | (ty, f[[ _ ]]) =>
      if lookup_field_in_type s ty f is Some fld then
        are_compatible_types fld.(return_type) rty
      else
        false
          
    | (ty, _:f[[ _ ]]) =>
      if lookup_field_in_type s ty f is Some fld then
        are_compatible_types fld.(return_type) rty
      else
        false
          
    | (ty, f[[ _ ]] { _ }) =>
      if lookup_field_in_type s ty f is Some fld then
        are_compatible_types fld.(return_type) rty
      else
        false

    | (ty, _:f[[ _ ]] { _ }) =>
       if lookup_field_in_type s ty f is Some fld then
        are_compatible_types fld.(return_type) rty
      else
        false

    | (_, on _ { _ }) => false
    end.

  
  (** *** Type-Compatible 
      ----

    Checks whether a list of selections have compatible return types.
    
    Two nested field selections are type-compatible if whenever
    they have the same response name, any two fields in the concatenation of their
    subselections are also type-compatible. Two single field selections
    are always type-compatible, unless they have the same response
    name and different (scalar or enum) type.
    Fragments are simply lifted, taking care to wrap each subselection with the type condition.

    We have to wrap each query with its parent type in order to find their appropriate return type.

    This definition roughly translate to the _SameResponseShape_ function defined in the Spec 
    (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##SameResponseShape()'><span>&#167;</span>5.3.2</a>#). 
    However, we noticed that there are redundant recursive calls between this function and the function _FieldsInSetCanMerge_
    (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##FieldsInSetCanMerge()'><span>&#167;</span>5.3.2</a>#), 
    which meant definition was hard in Coq plus possibly costly (due to repeated recursive calls).

    We also notice that this definition is a little bit conservative, in the sense that it
    may consider valid queries invalid (See #<a href='https://tinyurl.com/y4uxz3gu'>example</a>#),
    due to an issue with inline fragments possibly allowing selections over any type
    (See #<a href='https://github.com/graphql/graphql-spec/issues/367'>issue</a>#).
  *)
 Equations? are_type_compatible (selections : seq (Name * @Selection Scalar)) :
   bool by wf (queries_size_aux selections) :=
   {
     are_type_compatible [::] := true ;

     are_type_compatible ((ty, f[[ _ ]]) :: φ)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := all (has_compatible_type fld.(return_type)) (find_pairs_with_response_name f φ)
                        && are_type_compatible (filter_pairs_with_response_name f φ);
       
       | _ := false (* If the field is not defined in its own type in scope it should fail *)
       };

     are_type_compatible ((ty, l:f[[ _ ]]) :: φ)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := all (has_compatible_type fld.(return_type)) (find_pairs_with_response_name l φ)
                        && are_type_compatible (filter_pairs_with_response_name l φ);
       
       | _ := false (* If the field is not defined in its own type in scope it should fail *)
       };

      are_type_compatible ((ty, f[[ _ ]] { β }) :: φ)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := let similar_queries := find_pairs_with_response_name f φ in
                    [&& all (has_compatible_type fld.(return_type)) similar_queries,
                     are_type_compatible ([seq (fld.(return_type).(tname), q) | q <- β] ++ merge_pairs_selection_sets s similar_queries) &
                     are_type_compatible (filter_pairs_with_response_name f φ)];
                     
                        
       | _ := false (* If the field is not defined in its own type in scope it should fail *)
       };
      
      are_type_compatible ((ty, l:f[[ _ ]] { β }) :: φ)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := let similar_queries := find_pairs_with_response_name l φ in
                    [&& all (has_compatible_type fld.(return_type)) similar_queries,
                     are_type_compatible ([seq (fld.(return_type).(tname), q) | q <- β] ++ merge_pairs_selection_sets s similar_queries) &
                     are_type_compatible (filter_pairs_with_response_name f φ)];
                     
                        
       | _ := false (* If the field is not defined in its own type in scope it should fail *)
       };

      
      are_type_compatible ((ty, on t { β }) :: φ) := are_type_compatible ([seq (t, q) | q <- β] ++ φ)
                                                                                                      
   }.
 all: do ? [rewrite ?/similar_queries; leq_queries_size].
  Qed.
  Next Obligation.
     move: {2}(queries_size_aux _) (leqnn (queries_size_aux selections)) => n.
     elim: n selections => /= [| n IH] selections; first by rewrite leqn0 => /queries_size_aux_0_nil ->; constructor.
     case: selections => /= [| q selections]; first by constructor.
     case: q => ts q.
     case_selection q; rewrite /queries_size_aux /= -/(queries_size_aux _); simp selection_size => Hleq;
     simp are_type_compatible; constructor; do ? [lookup; constructor]; apply: IH; leq_queries_size.
  Defined.



 (** ** Are selections renaming-consistent ?
     ----
     
     Checks whether a list of selections are renaming-consistent.

     Two field selections are _renaming-consistent_ if whenever they have the
     same response name and lie under overlapping types in context
     they have the same (actual) name, the same arguments and any two
     fields in the concatenation of their subselections are also
     renaming-consistent.

     This definition roughly corresponds to 
     (cf. #<a href='https://graphql.github.io/graphql-spec/June2018/##FieldsInSetCanMerge()'><span>&#167;</span>5.3.2</a>#).
     The differences are due to the same reasons given in [are_type_compatible].
  *)
 Equations? are_renaming_consistent (selections : seq (Name * @Selection Scalar)) :
   bool by wf (queries_size_aux selections) :=
   {
     are_renaming_consistent [::] := true;

     are_renaming_consistent ((ty, f[[α]]) :: φ)
       with is_object_type s ty :=
       {
       | true := all (are_equivalent (f[[α]])) [seq p.2 | p <- (find_valid_pairs_with_response_name s ty f φ)] &&
                 are_renaming_consistent (filter_pairs_with_response_name f φ);
       
       | _ := all (are_equivalent (f[[α]])) [seq p.2 | p <- (find_pairs_with_response_name f φ)] &&
                 are_renaming_consistent (filter_pairs_with_response_name f φ)
       };

     are_renaming_consistent ((ty, l:f[[α]]) :: φ)
       with is_object_type s ty :=
       {
       | true := all (are_equivalent (l:f[[α]])) [seq p.2 | p <- (find_valid_pairs_with_response_name s ty l φ)] &&
                 are_renaming_consistent (filter_pairs_with_response_name l φ);
       
       | _ := all (are_equivalent (l:f[[α]])) [seq p.2 | p <- (find_pairs_with_response_name l φ)] &&
                 are_renaming_consistent (filter_pairs_with_response_name l φ)
       };
     
     are_renaming_consistent ((ty, f[[α]] { β }) :: φ)
       with lookup_field_in_type s ty f :=
       {
       | Some fld
           with is_object_type s ty :=
           {
           | true := let similar_queries := find_valid_pairs_with_response_name s ty f φ in
                 [&& all (are_equivalent (f[[α]] { β })) [seq p.2 | p <- similar_queries],
                  are_renaming_consistent ([seq (fld.(return_type).(tname), q) | q <- β] ++ merge_pairs_selection_sets s similar_queries) &
                  are_renaming_consistent (filter_pairs_with_response_name f φ)];
           
           | _ := let similar_queries := find_pairs_with_response_name f φ in
                 [&& all (are_equivalent (f[[α]] { β })) [seq p.2 | p <- similar_queries],
                  are_renaming_consistent ([seq (fld.(return_type).(tname), q) | q <- β] ++ merge_pairs_selection_sets s similar_queries) &
                  are_renaming_consistent (filter_pairs_with_response_name f φ)]
           };
       
       | _ := false 
       };

     are_renaming_consistent ((ty, l:f[[α]] { β }) :: φ)
       with lookup_field_in_type s ty f :=
       {
       | Some fld
           with is_object_type s ty :=
           {
           | true := let similar_queries := find_valid_pairs_with_response_name s ty l φ in
                 [&& all (are_equivalent (l:f[[α]] { β })) [seq p.2 | p <- similar_queries],
                  are_renaming_consistent ([seq (fld.(return_type).(tname), q) | q <- β] ++ merge_pairs_selection_sets s similar_queries) &
                  are_renaming_consistent (filter_pairs_with_response_name l φ)];
           
           | _ := let similar_queries := find_pairs_with_response_name l φ in
                 [&& all (are_equivalent (l:f[[α]] { β })) [seq p.2 | p <- similar_queries],
                  are_renaming_consistent ([seq (fld.(return_type).(tname), q) | q <- β] ++ merge_pairs_selection_sets s similar_queries) &
                  are_renaming_consistent (filter_pairs_with_response_name l φ)]
           };
          
       | _ := false 
       };

     are_renaming_consistent ((ty, on t { β }) :: φ)
       with is_fragment_spread_possible s ty t :=
       {
       | true := are_renaming_consistent ([seq (t, sel) | sel <- β] ++ φ);
       | _ := are_renaming_consistent φ
       }
   }.
 Proof.
   all: do ? [rewrite ?/similar_queries; leq_queries_size].
 Qed.
 Next Obligation.
   move: {2}(queries_size_aux _) (leqnn (queries_size_aux selections)) => n.
   elim: n selections => /= [| n IH] selections; first by rewrite leqn0 => /queries_size_aux_0_nil ->; constructor.
   case: selections => /= [| q selections]; first by constructor.
   case: q => ts q.
   case_selection q; rewrite /queries_size_aux /= -/(queries_size_aux _); simp selection_size => Hle;
   simp are_renaming_consistent; constructor; do ? [lookup; constructor]; last first.
   case is_fragment_spread_possible; constructor; last by apply: IH; leq_queries_size.

   all: do ? [case is_object_type; constructor].
   all: do ? [by apply: IH; leq_queries_size].
   
 Defined.
 

 (** ** Selection Conformance
     ----

     Check whether a list of selections conform to a given type in the schema.
     
     This definition captures the previous validation predicates:

     - Evey selection is consistent,

     - selections are type-compatible, and

     - are renaming-consistent.

   *)
  Definition selections_conform (ty : Name) σs : bool :=
    let σs_with_scope := [seq (ty, σ) | σ <- σs] in 
    [&& all (is_consistent ty) σs,
        σs_with_scope.(are_type_compatible) &
        σs_with_scope.(are_renaming_consistent)].


  (** ---- *)
  (** * Query conformance
      
      A query conforms if its selection set conforms to the Query type.
   *)
  Definition query_conforms (q : query) : bool :=
    selections_conform s.(query_type) q.(selection_set).
  
 
End QueryConformance.

(* begin hide *)
Arguments arguments_conform [Scalar].
Arguments are_type_compatible [Scalar].
Arguments are_renaming_consistent [Scalar].
Arguments is_consistent [Scalar].
Arguments selections_conform [Scalar].
Arguments query_conforms [Scalar].
(* end hide *)

(** ---- *)
(** 
    #<div>
        <a href='GraphCoQL.Query.html' class="btn btn-light" role='button'> Previous ← Query  </a>
        <a href='GraphCoQL.QueryNormalForm.html' class="btn btn-info" role='button'>Continue Reading → Normal Form </a>
    </div>#
*)