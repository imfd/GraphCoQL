(* begin hide *)

From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

Require Import String.
Require Import QString.

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

  Variables Vals : eqType.
  
  
  Implicit Type queries : seq (@Selection Vals).
  Implicit Type query : @Selection Vals.


  Variable s : @wfGraphQLSchema Vals.
 
  (** * Conformance Predicates *)
  (** ---- *)
  
  (** ** Are queries consistent ?
      
      First we define the necessary predicates to establish that a query is consistent 
      by itself.
   *)
  (** ---- *)
  (** 
      #<strong>arguments_conform</strong># : List FieldArgumentDefinition → List (Name * Vals) → Bool

      The following predicate checks whether a list of arguments (described as a pairing between names and values)
      conform to a list of field arguments.
      
      This is used when checking whether a field selection is consistent with a type in the schema.

      For a query argument to be valid it must satisfy the following:
      - There exists an argument definition with the same name.
      - The value given to the query argument must be of the "same type" as the type 
        associated to the argument definition in the Schema (eg. if the argument requires 
        an Int, then an "Int" value must be passed on when querying).      
      

      #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
      **** Observations

      - Required arguments : Since NonNull types are not implemented, we are not checking for required 
         arguments.
   **)
  Definition arguments_conform (args : seq FieldArgumentDefinition) (α : seq (Name * Vals)) : bool :=
    let argument_conforms (arg : Name * Vals) : bool :=
        let: (name, value) := arg in
        has (fun argdef => (argdef.(argname) == name) && s.(is_valid_value) argdef.(argtype) value) args
    in
    all argument_conforms α && uniq [seq arg.1 | arg <- α].
     


  (** ---- *)
  (**
     #<strong>is_fragment_spread_possible</strong># : Name → Name → Bool 
     
     Checks whether a given type can be used as an inline fragment's type condition 
     in a given context with another type in scope (parent type).

     It basically amounts to intersecting the possible subtypes of each
     and checking that the intersection is not empty.     
   *)
  Definition is_fragment_spread_possible parent_type fragment_type : bool :=
    let ty_possible_types := get_possible_types s fragment_type in
    let parent_possible_types := get_possible_types s parent_type in
    let applicable_types := (ty_possible_types :&: parent_possible_types)%SEQ in
    applicable_types != [::].


  (** ---- *)
  (** 
     #<strong>is_consistent</strong># : Name → Selection → Bool 

      Checks whether a query is consistent to a given type in the schema.

      This checks the following things specified in the spec :

      - Fields are defined (if we lookup the field selection's name in our type in context, we must find a field definition).

      - Field selection's arguments should conform to the arguments declared in the field definition obtained previously.

      - Leaf field selections should have Scalar or Enum return type.

      - Node field selections should have Object, Interface or Union return type.

      - Nested subqueries should not be empty.

      - Nested subqueries should be consistent wrt. to its parent type (return type for fields or type condition for fragments).

      - Fragments' type condition must spread in the type in context.
     
   *)
 (* TODO: Rename? It is only a part of the whole validation process *)
  Fixpoint is_consistent (type_in_scope : Name) query : bool :=
    match query with
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

    | on t { φ } => [&& is_fragment_spread_possible type_in_scope t,
                    φ != [::] &
                    all (is_consistent t) φ]
    end.
  

  (** ---- *)
  (** ** Do queries have compatible response shapes ?

      In this segment we define the necessary predicates to establish if the queries 
      have compatible response shapes.
   *)
  (** ---- *)
  (**
    #<strong>are_compatible_types</strong># : Type → Type → Bool

    Checks whether two types are compatible. 
    This is posteriorly used to check if two queries have compatible response shapes.

    This corresponds to steps 3-6 used in the definition given in _SameResponseShape_ in the 
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
    #<strong>has_compatible_type</strong># : Name → Type → Selection → Bool 

    Checks whether a given query has a return type compatible to the 
    one given as parameter. This is posteriorly used to check whether
    two queries have compatible response shapes. 

    The first parameter corresponds to the type in context where the 
    query might live.

    Inline fragments do not have a return type, therefore this always 
    returns false for these cases.

    There is a lot of code repetition, which is there only for reading purposes.
  *)
  Fixpoint has_compatible_type (rty : type) (nq : Name * @Selection Vals) : bool :=
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

  
  (** ---- *)
  (**
    #<strong>have_compatible_response_shapes</strong># : Name → List (Name * Selection) → Bool 

    Checks whether a list of queries have compatible return types.
    This means that queries with the same response name should have types that are 
    somewhat "similar". This ensures that their outputs will also be consistent.

    For example, it doesn't make sense to have two queries with response name "age" but 
    one is an Int and the other is a String. Both should be Int or Float.

    We have to wrap each query with its parent type in order to find their appropriate return type.
    
  *)
 (* Equations is not able to build the graph - hence we use noind *)
 Equations(noind) have_compatible_response_shapes (queries : seq (Name * @Selection Vals)) :
   bool by wf (queries_size_aux queries) :=
   {
     have_compatible_response_shapes [::] := true ;

     have_compatible_response_shapes ((ty, f[[ _ ]]) :: φ)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := all (has_compatible_type fld.(return_type)) (find_pairs_with_response_name f φ)
                        && have_compatible_response_shapes (filter_pairs_with_response_name f φ);
       
       | _ := have_compatible_response_shapes φ
       };

     have_compatible_response_shapes ((ty, l:f[[ _ ]]) :: φ)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := all (has_compatible_type fld.(return_type)) (find_pairs_with_response_name l φ)
                        && have_compatible_response_shapes (filter_pairs_with_response_name l φ);
       
       | _ := have_compatible_response_shapes φ
       };

      have_compatible_response_shapes ((ty, f[[ _ ]] { β }) :: φ)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := let similar_queries := find_pairs_with_response_name f φ in
                    [&& all (has_compatible_type fld.(return_type)) similar_queries,
                     have_compatible_response_shapes ([seq (fld.(return_type).(tname), q) | q <- β] ++ merge_pairs_selection_sets s similar_queries) &
                     have_compatible_response_shapes (filter_pairs_with_response_name f φ)];
                     
                        
       | _ := have_compatible_response_shapes φ
       };
      
      have_compatible_response_shapes ((ty, l:f[[ _ ]] { β }) :: φ)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := let similar_queries := find_pairs_with_response_name l φ in
                    [&& all (has_compatible_type fld.(return_type)) similar_queries,
                     have_compatible_response_shapes ([seq (fld.(return_type).(tname), q) | q <- β] ++ merge_pairs_selection_sets s similar_queries) &
                     have_compatible_response_shapes (filter_pairs_with_response_name f φ)];
                     
                        
       | _ := have_compatible_response_shapes φ
       };

      
      have_compatible_response_shapes ((ty, on t { β }) :: φ) := have_compatible_response_shapes ([seq (t, q) | q <- β] ++ φ)
                                                                                                      
   }.
 Solve Obligations with intros; leq_queries_size.
 Next Obligation.
   rewrite /queries_size_aux /= map_cat queries_size_cat; simp selection_size.
   have -> : forall xs y, [seq x.2 | x <- [seq (y, q) | q <- xs] ] = xs by intros; elim: xs => //= x xs ->.
   have Hmleq := (merge_pair_selections_leq s (find_pairs_with_response_name f φ)).
   rewrite /queries_size_aux in Hmleq *.
   have Hfleq : queries_size [seq nq.2 | nq <- find_pairs_with_response_name f φ] <=
                queries_size [seq nq.2 | nq <- φ].
     by rewrite find_pairs_spec; apply: found_fields_leq_size.
       by ssromega.
 Qed.
 Next Obligation.
   rewrite /queries_size_aux /= map_cat queries_size_cat; simp selection_size.
   have -> : forall xs y, [seq x.2 | x <- [seq (y, q) | q <- xs] ] = xs by intros; elim: xs => //= x xs ->.
   have Hmleq := (merge_pair_selections_leq s (find_pairs_with_response_name l φ)).
   rewrite /queries_size_aux in Hmleq *.
   have Hfleq : queries_size [seq nq.2 | nq <- find_pairs_with_response_name l φ] <=
                queries_size [seq nq.2 | nq <- φ].
     by rewrite find_pairs_spec; apply: found_fields_leq_size.
       by ssromega.
 Qed.
 Next Obligation.
   rewrite /queries_size_aux /= map_cat queries_size_cat; simp selection_size.
   have -> : forall xs y, [seq x.2 | x <- [seq (y, q) | q <- xs] ] = xs by intros; elim: xs => //= x xs ->.       
     by ssromega.
 Qed.



 (** ---- *)
 (** ** Is field merging possible ?
     In this section we define the predicate that checks if field merging is possible.
  *)
 (** ---- *)
 (**
    #<strong>is_field_merging_possible</strong># : Name → List Selection → Bool

    Checks whether a list of queries are mergeable.

    In a nutshell, what we do is look for fields with the same _response name_ and then check that:
    - They are all leaf fields or all node fields.
    - They all have the same _field name_.
    - They all have the same arguments.

    We use the type in context to find only the fields that make sense 
    (because with fragments we can create queries that don't make sense).
  *)
 Equations? is_field_merging_possible (type_in_scope : Name) queries : bool by wf (queries_size queries)  :=
   {
     is_field_merging_possible _ [::] := true;

     is_field_merging_possible ty (f[[α]] :: φ)
       with is_object_type s ty :=
       {
       | true := all (are_equivalent (f[[α]])) (find_queries_with_label s f ty φ) &&
                    is_field_merging_possible ty (filter_queries_with_label f φ);
       
       | _ := all (are_equivalent (f[[α]])) (find_fields_with_response_name f φ) &&
                 is_field_merging_possible ty (filter_queries_with_label f φ)
       };

     is_field_merging_possible ty (l:f[[α]] :: φ)
       with is_object_type s ty :=
       {
       | true := all (are_equivalent (l:f[[α]])) (find_queries_with_label s l ty φ) &&
                    is_field_merging_possible ty (filter_queries_with_label l φ);
       
       | _ := all (are_equivalent (l:f[[α]])) (find_fields_with_response_name l φ) &&
                 is_field_merging_possible ty (filter_queries_with_label l φ)
       };
     
     is_field_merging_possible ty (f[[α]] { β } :: φ)
       with lookup_field_in_type s ty f :=
       {
       | Some fld 
           with is_object_type s ty :=
           {
           | true := let similar_queries := find_queries_with_label s f ty φ in
                    [&& all (are_equivalent (f[[α]] { β })) similar_queries,
                     is_field_merging_possible fld.(return_type) (β ++ merge_selection_sets similar_queries) &
                     is_field_merging_possible ty (filter_queries_with_label f φ)];
           
       
           | _ := let similar_queries := find_fields_with_response_name f φ in
                 [&& all (are_equivalent (f[[α]] { β })) similar_queries,
                  is_field_merging_possible fld.(return_type) (β ++ merge_selection_sets similar_queries) &
                  is_field_merging_possible ty (filter_queries_with_label f φ)]
           };
       
       | _ := false 
       };

     is_field_merging_possible ty (l:f[[α]] { β } :: φ)
       with lookup_field_in_type s ty f :=
       {
       | Some fld 
           with is_object_type s ty :=
           {
           | true := let similar_queries := find_queries_with_label s l ty φ in
                    [&& all (are_equivalent (l:f[[α]] { β })) similar_queries,
                     is_field_merging_possible fld.(return_type) (β ++ merge_selection_sets similar_queries) &
                     is_field_merging_possible ty (filter_queries_with_label l φ)];
           
       
           | _ := let similar_queries := find_fields_with_response_name l φ in
                 [&& all (are_equivalent (l:f[[α]] { β })) similar_queries,
                  is_field_merging_possible fld.(return_type) (β ++ merge_selection_sets similar_queries) &
                  is_field_merging_possible ty (filter_queries_with_label l φ)]
           };
       
       | _ := false 
       };

     is_field_merging_possible ty (on t { β } :: φ)
       with is_fragment_spread_possible t ty :=
       {
       | true with is_object_type s ty :=
           {
           | true := is_field_merging_possible ty (β ++ φ);

           (* This can be improved. For instance, if t = ty, then we can simply 
              lift β *)
           | _ := is_field_merging_possible t (β ++ φ) && is_field_merging_possible ty φ
           };
       
       | _ := is_field_merging_possible ty φ
       }
   }.
 Proof.
   all: do ? [rewrite ?/similar_queries; leq_queries_size].
 Qed.
 (* Equations can't build the graph *)
 Next Obligation.
   move: {2}(queries_size _) (leqnn (queries_size queries)) => n.
   elim: n type_in_scope queries => /= [| n IH] type_in_scope queries; first by rewrite leqn0 => /queries_size_0_nil ->; constructor.
   case: queries => /= [| q queries]; first by constructor.
   case_selection q; simp selection_size => Hleq;
   simp is_field_merging_possible; constructor; do ? [lookup; constructor]; last first.
   case is_fragment_spread_possible; constructor; last by apply: IH; leq_queries_size.
   all: do ? [case is_object_type => /=; by constructor; apply: IH; leq_queries_size].
 Defined.
 

 (** ---- *)
 (** * Selection Conformance *)
 (** ---- *)
 (**
     #<strong>queries_conform</strong># : Name -> List Selection -> Bool 

     Check whether a list of queries conform to a given type in the schema.
     
     This definition captures the previous validation predicates:

     - ∀ query ∈ queries, query is consistent to the type in scope.

     - Queries have compatible response shapes.

     - Field merging is possible.

   *)
  Definition queries_conform (ty : Name) queries : bool :=
    [&& all (is_consistent ty) queries,
        have_compatible_response_shapes [seq (ty, q) | q <- queries] &
        is_field_merging_possible ty queries].
    
  
 
End QueryConformance.
(** ---- *)

Arguments arguments_conform [Vals].
Arguments is_fragment_spread_possible [Vals].
Arguments have_compatible_response_shapes [Vals].
Arguments is_field_merging_possible [Vals].
Arguments is_consistent [Vals].
Arguments queries_conform [Vals].

(** ---- *)
(** 
    #<div>
        <a href='GraphCoQL.Selection.html' class="btn btn-light" role='button'> Previous ← Selection  </a>
        <a href='GraphCoQL.SelectionNormalForm.html' class="btn btn-info" role='button'>Continue Reading → Normal Form </a>
    </div>#
*)