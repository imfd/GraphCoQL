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
         This file contains the necessarty definitions to validate when a GraphQL Query
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
  
  
  Implicit Type queries : seq (@Query Vals).
  Implicit Type query : @Query Vals.


  Variable s : @wfGraphQLSchema Vals.
 
  (**
     First of all, we will begin by establishing some basic properties that queries must satisfy and then 
     we will move onto some more involved ones. Some of these basic properties are: 
     - The arguments of a field selection must be valid.
     - The field name used to query is actually defined in the Schema.
     - Fragments' types are valid 
     - etc. 
     
     One important notion that we must keep at all times is that queries are evaluated with a given type in context.
     This means that when we check if a field selection is valid, it is valid wrt. the given type in context.

     For example, we might have the following type :
     
     #<img src='../imgs/Schema/type_query.png'>#

     Followed by this query:

     #<img src='../imgs/Query/query1.png'>#

     
     We know that the field selection _hero_ is performed over the type _Query_, then if we want to validate _hero_ it has to be wrt. _Query_.

     Similarly, we know that _name_ nested inside _hero_ is defined in a context with _Character_ as its type, 
     while the field selection _name_ nested inside _droid_ is defined in a context where its type is _Droid_.     
     
     Therefore, whenever we want to validate queries we must do it keeping in mind the type where it's being applied.
     
     
     Having said that, we can now begin defining the necessary properties.

     We will start by establishing when arguments are valid wrt. a list of Field Arguments obtained from a 
     particular type and field.
   *)
  
  
  (** ---- *)
  (** *** Arguments conform 

      #<strong>arguments_conform</strong># : List FieldArgumentDefinition → List (Name * Vals) → Bool

      The following predicate checks whether a list of arguments (described as a pairing between names and values)
      conform to a list of field arguments.
      
      This is used when checking whether a field selection conforms to a type in the schema.

      For a query argument to be valid it must satisfy the following:
      - There exists an argument definition with the same name.
      - The value given to the query argument must be of the "same type" as the type 
        associated to the argument definition in the Schema (eg. if the argument requires 
        an Int, then an "Int" value must be passed on when querying).      
      

      #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
      **** Observations

      - Required arguments : Since NonNull types are not implemented, we are not checking for required 
         arguments.
      
      - P&H : We do not have a complete definition of conformance to which we could compare.

      
      #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
      **** Spec Reference 
      - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Validation.Arguments'>Validation - Arguments</a># 
      - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Argument-Names'>Argument Names</a>#
      - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Argument-Uniqueness'>Argument Uniqueness</a>#
      - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Required-Arguments'>Required Arguments</a>#
      - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Values-of-Correct-Type'>Values of Correct Type</a>#

   **)
  Definition arguments_conform (args : seq FieldArgumentDefinition) (α : seq (Name * Vals)) : bool :=
    let argument_conforms (arg : Name * Vals) : bool :=
        let: (name, value) := arg in
        has (fun argdef => (argdef.(argname) == name) && s.(has_type) argdef.(argtype) value) args
    in
    all argument_conforms α && uniq [seq arg.1 | arg <- α].
     


  (** ---- *)
  (**
     is_fragment_spread_possible : Name → Name → Bool 
     
     Checks whether a given type can be used as an inline fragment's type condition 
     in a given context with another type in scope (parent type).

     It basically amounts to intersecting the possible types of each
     and checking that the intersection is not empty.


     #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
     **** Spec Reference
     - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Fragment-spread-is-possible'>Fragment spread is possible</a>#
     - #<a href='https://facebook.github.io/graphql/June2018/##GetPossibleTypes()'>GetPossibleTypes()</a>#
        
      
   *)
  Definition is_fragment_spread_possible parent_type fragment_type : bool :=
    let ty_possible_types := get_possible_types s fragment_type in
    let parent_possible_types := get_possible_types s parent_type in
    let applicable_types := (ty_possible_types :&: parent_possible_types)%SEQ in
    applicable_types != [::].


   (** ---- *)
 (** 
      query_conforms : Name → Query → Bool 

      Checks whether a query conforms to a given type in the schema.
      
      The first parameter corresponds to the type in context where
      the queries might live.


      This checks the following things specified in the spec :

      1. Fields are defined in the type in context.
      
      2. If return type is a Scalar or Enum, then it doesn't have subqueries.

      3. If return type is an Object, Interface or Union, then it must have non-empty subqueries.

      4. Arguments conform to the type in context.

      6. Inline fragments can be spread in the given type in context.

      
      #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
      **** Observations 
      
      - Fragments on composite types : The spec states that a fragment's type condition must 
        be an Object, Interface or Union type. We argue that adding this check is a bit 
        redundant along with [is_fragment_spread_possible], because if the type condition 
        is not any of the previous one, then its possible types would be empty (meaning 
        the previous predicate would be false).

      - Fragment spread type existence : Similar to the previous one, the spec states that 
        the type condition must exist in the schema. We argue again that adding this check 
        would be a bit redundant, for similar reasons.

      - P&H : We do not have a complete definition of conformance to which we could compare.
        They mention a notion of conformance of a query wrt. the Query type.


     #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
     **** Spec Reference
     
     - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Field-Selections-on-Objects-Interfaces-and-Unions-Types'>Field Selections on Objects, Interfaces and Unions Types</a>#
     - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Leaf-Field-Selections'>Leaf Field Selections</a>#
     - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Fragment-Spread-Type-Existence'>Fragment Spread Type Existence</a>#
     - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Fragments-On-Composite-Types'>Fragments on Composite Types</a>#
     - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Fragment-spread-is-possible'>Fragment spread is possible</a>#  

     
   *)
 (* TODO: Rename? It is only a part of the whole validation process *)
  Fixpoint query_conforms (type_in_scope : Name) query : bool :=
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
         all (query_conforms fld.(return_type)) φ]
      else
        false 

    | _:f[[α]] { φ } =>
      if lookup_field_in_type s type_in_scope f is Some fld then
        [&& (is_object_type s fld.(return_type) || is_abstract_type s fld.(return_type)),
         arguments_conform fld.(fargs) α,
         φ != [::] &
         all (query_conforms fld.(return_type)) φ]
      else
        false 

    | on t { φ } => [&& is_fragment_spread_possible type_in_scope t,
                    φ != [::] &
                    all (query_conforms t) φ]
    end.
  

  (** ---- *)
  (**
    are_compatible_types : Type → Type → Bool

    Checks whether two types are compatible. 
    This is posteriorly used to check if two queries have compatible response shapes.

    This corresponds to steps 3-6 used in the definition given in _SameResponseShape_ in the 
    spec.

    #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
    **** Spec Reference 

    - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Field-Selection-Merging'>Field Selection Merging</a>#
    - #<a href='https://graphql.github.io/graphql-spec/June2018/##SameResponseShape()'>SameResponseShape()</a>#
    
  *)
 Equations are_compatible_types : type -> type -> bool :=
   {
     are_compatible_types (NamedType rty) (NamedType rty')
       with (is_scalar_type s rty || is_enum_type s rty) :=
       {
       | true := rty == rty';
       | _ := is_composite_type s rty'
       };
     are_compatible_types (ListType rty) (ListType rty') := are_compatible_types rty rty';
     are_compatible_types _ _ := false
   }.

 (** ---- *)
 (**
    has_compatible_type : Name → Type → Query → Bool 

    Checks whether a given query has a return type compatible to the 
    one given as parameter. This is posteriorly used to check whether
    two queries have compatible response shapes. 

    The first parameter corresponds to the type in context where the 
    query might live.

    Inline fragments do not have a return type, therefore this always 
    returns false for these cases.

    #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
    **** Spec Reference
    
    - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Field-Selection-Merging'>Field Selection Merging</a>#
    - #<a href='https://graphql.github.io/graphql-spec/June2018/##SameResponseShape()'>SameResponseShape()</a>#
 

  *)
 Equations has_compatible_type (return_type : type) (nq : Name * @Query Vals) : bool :=
   {
     has_compatible_type rty (ty, f[[ _ ]])
       with lookup_field_in_type s ty f :=
       {
       | Some fld := are_compatible_types fld.(return_type) rty;
       | _ := false
       };
     has_compatible_type rty (ty, _:f[[ _ ]])
       with lookup_field_in_type s ty f :=
       {
       | Some fld := are_compatible_types fld.(return_type) rty;
       | _ := false
       };
     
     has_compatible_type rty (ty, f[[ _ ]] { _ })
       with lookup_field_in_type s ty f :=
       {
       | Some fld := are_compatible_types fld.(return_type) rty;
       | _ := false
       };
     
     has_compatible_type rty (ty, _:f[[ _ ]] { _ })
       with lookup_field_in_type s ty f :=
       {
       | Some fld := are_compatible_types fld.(return_type) rty;
       | _ := false
       };

     has_compatible_type _ (_, on _ { _ }) := false
   }.

 (** ---- *)
 (**
    have_compatible_response_shapes : Name → List Query → Bool 

    Checks whether a list of queries have compatible return types.

    The spec works directly with a list of queries that share a given 
    response name, but in this case we work with any list of queries, 
    which might not share response names.

    Due to this, we first collect queries which share the response name 
    ([find_fields_with_response_name] and [filter_queries_with_label])
    and proceed to check that their types are compatible to the return 
    type of the first query found. 

    We renamed it to _compatible response shapes_ because of the fact 
    we are not working with queries with the same response name and because 
    it seems more adequate to say that their shapes are compatible rather than
    the same. 

    The first parameter corresponds to the type in context where the queries 
    might live.

    #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
    **** Observations
    
    - Redundant recursion : We argue that the definitions given in the spec for _FieldsInSetCanMerge_ and _SameResponseShape_
       make two recursive calls that are redundant (Section 2.iv and 9.a respectively). You can separate this 
       calls and work separately, checking equality of names and arguments on one hand and checking types on the 
       other (or try and mix both to optimize calls - in this case we prefer to split to facilitate reasoning).

    - Redundant pair-check : The spec checks _SameResponseShape_ for every pair of queries sharing a response name.
       We argue that it should suffice to check every query against a single one (as we do here) and via transitivity 
       validate that they all have compatible return types.

    
    #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
    **** Spec Reference

    - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Field-Selection-Merging'>Field Selection Merging</a>#
    - #<a href='https://graphql.github.io/graphql-spec/June2018/##SameResponseShape()'>SameResponseShape()</a>#
 
  *)
 (* I am pretty sure about claim (2) but we should confirm it somehow.. right xd? *)
 (* Equations is not able to build the graph *)
 Equations(noind) have_compatible_response_shapes (* (type_in_scope : Name) *) (queries : seq (Name * @Query Vals)) :
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
 (* begin hide *)
 (* Not showing this in the doc to ease reading *)
 Solve Obligations with intros; leq_queries_size.
 Next Obligation.
   rewrite /queries_size_aux /= map_cat queries_size_cat; simp query_size.
   have -> : forall xs y, [seq x.2 | x <- [seq (y, q) | q <- xs] ] = xs by intros; elim: xs => //= x xs ->.
   have Hmleq := (merge_pair_selections_leq s (find_pairs_with_response_name f φ)).
   rewrite /queries_size_aux in Hmleq *.
   have Hfleq : queries_size [seq nq.2 | nq <- find_pairs_with_response_name f φ] <=
                queries_size [seq nq.2 | nq <- φ].
     by rewrite find_pairs_spec; apply: found_fields_leq_size.
       by ssromega.
 Qed.
 Next Obligation.
   rewrite /queries_size_aux /= map_cat queries_size_cat; simp query_size.
   have -> : forall xs y, [seq x.2 | x <- [seq (y, q) | q <- xs] ] = xs by intros; elim: xs => //= x xs ->.
   have Hmleq := (merge_pair_selections_leq s (find_pairs_with_response_name l φ)).
   rewrite /queries_size_aux in Hmleq *.
   have Hfleq : queries_size [seq nq.2 | nq <- find_pairs_with_response_name l φ] <=
                queries_size [seq nq.2 | nq <- φ].
     by rewrite find_pairs_spec; apply: found_fields_leq_size.
       by ssromega.
 Qed.
 Next Obligation.
   rewrite /queries_size_aux /= map_cat queries_size_cat; simp query_size.
   have -> : forall xs y, [seq x.2 | x <- [seq (y, q) | q <- xs] ] = xs by intros; elim: xs => //= x xs ->.       
     by ssromega.
 Qed.
(* end hide *)

 (** ---- *)
 (**
    is_field_merging_possible : Name → List Query → Bool

    Checks whether a list of queries are mergeable.

    The first parameter corresponds to the type in context where
    the queries might live.

    Our definition differs in three main aspects and a minor one with respect
    to the spec's definition (_FieldsInSetCanMerge_):

    The first difference is that the spec's definition works directly with a list of queries
    that share a given response name. In our case we work with any list of queries, 
    which might not share response names.

    The second difference comes from the fact that the spec's definition is too conservative in our 
    opinion. Due to this, valid queries might be considered invalid (https://tinyurl.com/y4zkoofg).
    The main issue comes from the fact that invalid inline fragments may be introduced,
    causing the check to fail even though those subqueries will never be evaluated
    (https://github.com/graphql/graphql-spec/issues/367). Our definition ignores this invalid 
    fragments and, supposedly, provides a more accurate validation.

    The third difference is that we separate the notion of _mergeable_
    from the one checking that their types are compatible (See [have_compatible_response_shapes] 
    observation on redundant pair-check).

    The fourth difference is that we do not directly perform the check in point 2.b of the 
    spec's definition. This is a side effect of the previous differences.

    All of these difference are reflected in the definition, in particular when checking 
    that the type in context is an object type or not. Depending on this, we might 
    collect queries with either [find_queries_with_label] or [find_fields_with_response_name], 
    respectively. This way, we can actually check merging on fields that make sense 
    and not on all fields that share a response name.

    #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
    **** Observations

    - Implicit type : The spec refers to the _parent types_ of each field but they 
       are not given as parameter.
      

    #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
    **** Spec Reference

    - #<a href='https://graphql.github.io/graphql-spec/June2018/##sec-Field-Selection-Merging'>Field Selection Merging</a>#
    - #<a href='https://graphql.github.io/graphql-spec/June2018/#FieldsInSetCanMerge()'>FieldsInSetCanMerge()</a>#
    
    **** See also
    
    - #<a href='https://tinyurl.com/y4zkoofg'>Query example</a># 

    - #<a href='https://github.com/graphql/graphql-spec/issues/367'>Fragments issue</a># 

    - #<a href='https://github.com/graphql/graphql-spec/issues/399'>Discussion on fragments</a># 
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
 (* begin hide *)
 (* Not showing this on docs to ease reading *)
 Proof.
   all: do ? [rewrite ?/similar_queries; leq_queries_size].
 Qed.
 (* Equations can't build the graph *)
 Next Obligation.
   move: {2}(queries_size _) (leqnn (queries_size queries)) => n.
   elim: n type_in_scope queries => /= [| n IH] type_in_scope queries; first by rewrite leqn0 => /queries_size_0_nil ->; constructor.
   case: queries => /= [| q queries]; first by constructor.
   case_query q; simp query_size => Hleq;
   simp is_field_merging_possible; constructor; do ? [lookup; constructor]; last first.
   case is_fragment_spread_possible; constructor; last by apply: IH; leq_queries_size.
   all: do ? [case is_object_type => /=; by constructor; apply: IH; leq_queries_size].
 Defined.
 (* end hide *)
 


  (** ---- *)
  (**
     queries_conform : Name -> List Query -> Bool 

     Check whether a list of queries conform to a given type in the schema.
     
     This definition captures the previous validation predicates:

     - ∀ query ∈ queries, query conforms to type in scope.

     - queries have compatible response shapes.

     - field merging is possible.

     #<div class="hidden-xs hidden-md hidden-lg"><br></div>#
     **** Observations
     
     - Empty lists : Our definition allows for a list of queries to be empty.
       We argue that this is not an issue, since we do check that subqueries 
       are not empty. If this list is empty and then evaluated, it would just 
       result in an empty list of results.

   *)
  Definition queries_conform (ty : Name) queries : bool :=
    [&& all (query_conforms ty) queries,
        have_compatible_response_shapes [seq (ty, q) | q <- queries] &
        is_field_merging_possible ty queries].
    
  
 
End QueryConformance.

Arguments arguments_conform [Vals].

Arguments is_fragment_spread_possible [Vals].
Arguments have_compatible_response_shapes [Vals].
Arguments is_field_merging_possible [Vals].
Arguments query_conforms [Vals].
Arguments queries_conform [Vals].

(** 
    #<div>
        <a href='GraphCoQL.Query.html' class="btn btn-light" role='button'> Previous ← Query  </a>
        <a href='GraphCoQL.QuerySemantic.html' class="btn btn-info" role='button'>Continue Reading → QuerySemantics </a>
    </div>#
*)