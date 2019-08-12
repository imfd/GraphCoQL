From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

From CoqUtils Require Import string.

Require Import Base.
Require Import Schema.
Require Import SchemaAux.
Require Import Query.
Require Import QueryAux.
Require Import QueryAuxLemmas.
Require Import SchemaWellFormedness.
Require Import SeqExtra.

Require Import QueryTactics.
Require Import Ssromega.

Section QueryConformance.

  Variables Vals : eqType.
  
  
  Implicit Type queries : seq (@Query Vals).
  Implicit Type query : @Query Vals.


  Variable s : @wfGraphQLSchema Vals.
 
 
  
  (** 
      argument_conforms : List FieldArgumentDefinition → Name * Vals → Bool 

      Checks whether a query's argument (argument name & value associated) conforms to an argument
      of a field defined in the schema.
      
      This is used when checking whether a field selection conforms to a type in the schema.
      The arguments passed on to the field selection must actually exist for the corresponding 
      field defined in the schema and the values must be of a valid type (eg. if argument requires 
      an Int, then an "Int" value must be passed on when querying).

      ∃ argument ∈ Args, argument.argname = α.name ∧ α.value has_type argument.argtype     #<br>#
      [―――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――――]    #<br>#
                                 α conforms Args


     ----
     See also:
     
     https://graphql.github.io/graphql-spec/June2018/#sec-Validation.Arguments

     https://graphql.github.io/graphql-spec/June2018/#sec-Argument-Names

   **)
  Definition argument_conforms (args : seq FieldArgumentDefinition) (arg : Name * Vals) : bool :=
    let: (argname, value) := arg in
    has (fun argdef => let: FieldArgument name ty := argdef in
                    (name == argname) && s.(has_type) ty value) args.
  

  (** 
      arguments_conform : List FieldArgumentDefinition → List (Name * Vals) → Bool

      Checks whether a list of arguments (described as a pairing between names and values)
      conform to a set of fields defined in the schema.

      This is used when checking whether a field selection conforms to a type in the schema.
      The arguments passed on to the field selection must actually exist for the corresponding 
      field defined in the schema and the values must be of a valid type (eg. if argument requires 
      an Int, then an "Int" value must be passed on when querying).


      ∀ argument ∈ α, argument conforms Args ∧ α.names are_unique    #<br>#
      [――――――――――――――――――――――――――――――――――――――――――――――――――――――――――]   #<br>#
                    α conform Args                                                 
      

      ---- 
      **** Observations

      1. Required arguments : Since NonNull types are not implemented, we are not checking for required 
         arguments.
      
      3. J&O : We do not have a complete definition of conformance to which we could compare.

      ---- 
      
      See also:

      - [arguments_conforms].

      https://graphql.github.io/graphql-spec/June2018/#sec-Argument-Uniqueness
      
      https://graphql.github.io/graphql-spec/June2018/#sec-Required-Arguments

      https://graphql.github.io/graphql-spec/June2018/#sec-Values-of-Correct-Type
   **)
  Definition arguments_conform (args : seq FieldArgumentDefinition) (α : seq (Name * Vals)) : bool :=
    all (argument_conforms args) α && uniq [seq arg.1 | arg <- α].
     

  
  (**
     is_fragment_spread_possible : Name → Name → Bool 
     
     Checks whether a given type can be used as an inline fragment's type condition 
     in a given context with another type in scope (parent type).

     It basically amounts to intersecting the possible types of each
     and checking that the intersection is not empty.


      ---- 
      See also:
      
      - [get_possible_types]     

      https://graphql.github.io/graphql-spec/June2018/#sec-Fragment-spread-is-possible

      https://facebook.github.io/graphql/June2018/#GetPossibleTypes()
   *)
  Definition is_fragment_spread_possible parent_type fragment_type : bool :=
    let ty_possible_types := get_possible_types s fragment_type in
    let parent_possible_types := get_possible_types s parent_type in
    let applicable_types := (ty_possible_types :&: parent_possible_types)%SEQ in
    applicable_types != [::].

  


 (**
    are_compatible_types : Type → Type → Bool

    Checks whether two types are compatible. 
    This is posteriorly used to check if two queries have compatible response shapes.

    This corresponds to steps 3-6 used in the definition given in _SameResponseShape_ in the 
    spec.

    ----
    See also:

    - [have_compatible_shapes]

    https://graphql.github.io/graphql-spec/June2018/#sec-Field-Selection-Merging
    
    https://graphql.github.io/graphql-spec/June2018/#SameResponseShape()
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


 (**
    has_compatible_type : Name → Type → Query → Bool 

    Checks whether a given query has a return type compatible to the 
    one given as parameter. This is posteriorly used to check whether
    two queries have compatible response shapes. 

    The first parameter corresponds to the type in context where the 
    query might live.

    Inline fragments do not have a return type, therefore this always 
    returns false for these cases.

    ----
    See also:

    - [have_compatible_shapes]

    https://graphql.github.io/graphql-spec/June2018/#sec-Field-Selection-Merging
    
    https://graphql.github.io/graphql-spec/June2018/#SameResponseShape()

  *)
 Equations has_compatible_type (type_in_context : Name) (return_type : type) query : bool :=
   {
     has_compatible_type ty rty (SingleField f _)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := are_compatible_types fld.(return_type) rty;
       | _ := false
       };
     has_compatible_type ty rty (LabeledField _ f _)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := are_compatible_types fld.(return_type) rty;
       | _ := false
       };
     
     has_compatible_type ty rty (NestedField f _ _)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := are_compatible_types fld.(return_type) rty;
       | _ := false
       };
     
     has_compatible_type ty rty (NestedLabeledField _ f _ _)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := are_compatible_types fld.(return_type) rty;
       | _ := false
       };

     has_compatible_type _ _ (InlineFragment _ _) := false
   }.


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

    ---- 
    **** Observations
    
    1. Redundant recursion : We argue that the definitions given in the spec for _FieldsInSetCanMerge_ and _SameResponseShape_
       make two recursive calls that are redundant (Section 2.iv and 9.a respectively). You can separate this 
       calls and work separately, checking equality of names and arguments on one hand and checking types on the 
       other (or try and mix both to optimize calls - in this case we prefer to split to facilitate reasoning).

    2. Redundant pair-check : The spec checks _SameResponseShape_ for every pair of queries sharing a response name.
       We argue that it should suffice to check every query against a single one (as we do here) and via transitivity 
       validate that they all have compatible return types.

    ----
    See also:

    
    https://graphql.github.io/graphql-spec/June2018/#sec-Field-Selection-Merging
    
    https://graphql.github.io/graphql-spec/June2018/#SameResponseShape()    

  *)
 (* I am pretty sure about claim (2) but we should confirm it somehow.. right xd? *)
 Equations? have_compatible_response_shapes (type_in_scope : Name) queries : bool by wf (queries_size queries) :=
   {
     have_compatible_response_shapes _ [::] := true ;

     have_compatible_response_shapes ty (f[[ _ ]] :: φ)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := all (has_compatible_type ty fld.(return_type)) (find_fields_with_response_name f φ)
                        && have_compatible_response_shapes ty (filter_queries_with_label f φ);
       | _ := false
       };

     have_compatible_response_shapes ty (l:f[[ _ ]] :: φ)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := all (has_compatible_type ty fld.(return_type)) (find_fields_with_response_name l φ)
                         && have_compatible_response_shapes ty (filter_queries_with_label l φ);
       | _ := false
       };

      have_compatible_response_shapes ty (f[[ _ ]] { β } :: φ)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := let similar_queries := find_fields_with_response_name f φ in
                    [&& all (has_compatible_type ty fld.(return_type)) similar_queries,
                     have_compatible_response_shapes fld.(return_type) (β ++ merge_selection_sets similar_queries) &
                     have_compatible_response_shapes ty (filter_queries_with_label f φ)];
                     
                        
       | _ := false
       };
      
      have_compatible_response_shapes ty (l:f[[ _ ]] { β } :: φ)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := let similar_queries := find_fields_with_response_name l φ in
                    [&& all (has_compatible_type ty fld.(return_type)) similar_queries,
                     have_compatible_response_shapes fld.(return_type) (β ++ merge_selection_sets similar_queries) &
                     have_compatible_response_shapes ty (filter_queries_with_label f φ)];
                     
                        
       | _ := false
       };

      
      have_compatible_response_shapes ty (on t { β } :: φ) := have_compatible_response_shapes ty (β ++ φ)
                                                                                                      
   }.
 Proof.
   all: do [rewrite ?/similar_queries; leq_queries_size].
 Qed.
 (* Equations is not able to build the graph *)
 Next Obligation.
   move: {2}(queries_size _) (leqnn (queries_size queries)) => n.
   elim: n queries type_in_scope => /= [| n IH] queries type_in_scope ; first by rewrite leqn0 => /queries_size_0_nil ->; constructor.
   case: queries => //= [| q queries]; first by constructor.
   case_query q; simp query_size => Hleq;
   simp have_compatible_response_shapes; constructor; do ? [lookup => /=; constructor]; apply: IH; leq_queries_size.
 Defined.



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

    ---- 
    **** Observations

    1. Implicit type : The spec refers to the _parent types_ of each field but they 
       are not given as parameter.
      

    ---- 
    See also:
    - [are_equivalent]
    - [find_queries_with_label]
    - [find_fields_with_response_name]
    - [have_compatible_response_shapes]

    https://graphql.github.io/graphql-spec/June2018/#sec-Field-Selection-Merging

    https://graphql.github.io/graphql-spec/June2018/#FieldsInSetCanMerge()

    https://tinyurl.com/y4zkoofg

    https://github.com/graphql/graphql-spec/issues/367

    https://github.com/graphql/graphql-spec/issues/399
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
   case_query q; simp query_size => Hleq;
   simp is_field_merging_possible; constructor; do ? [lookup; constructor]; last first.
   case is_fragment_spread_possible; constructor; last by apply: IH; leq_queries_size.
   all: do ? [case is_object_type => /=; by constructor; apply: IH; leq_queries_size].
 Defined.
 
        
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

      ---- 
      **** Observations 
      
      1. Fragments on composite types : The spec states that a fragment's type condition must 
         be an Object, Interface or Union type. We argue that adding this check is a bit 
         redundant along with [is_fragment_spread_possible], because if the type condition 
         is not any of the previous one, then its possible types would be empty (meaning 
         the previous predicate would be false).

      2. Fragment spread type existence : Similar to the previous one, the spec states that 
         the type condition must exist in the schema. We argue again that adding this check 
         would be a bit redundant, for similar reasons.

      3. J&O : We do not have a complete definition of conformance to which we could compare.
         They mention a notion of conformance of a query wrt. the Query type.


     ---- 
     See also
     
     - [arguments_conform]

     - [is_fragment_spread_possible]

     https://graphql.github.io/graphql-spec/June2018/#sec-Field-Selections-on-Objects-Interfaces-and-Unions-Types

     https://graphql.github.io/graphql-spec/June2018/#sec-Leaf-Field-Selections

     https://graphql.github.io/graphql-spec/June2018/#sec-Fragment-Spread-Type-Existence

     https://graphql.github.io/graphql-spec/June2018/#sec-Fragments-On-Composite-Types

     https://graphql.github.io/graphql-spec/June2018/#sec-Fragment-spread-is-possible
   *)
 (* TODO: Rename? It is only a part of the whole validation process *)
  Equations query_conforms (type_in_scope : Name) query : bool :=
    {
      query_conforms ty (f[[α]])
        with lookup_field_in_type s ty f :=
        {
        | Some fld => (is_scalar_type s fld.(return_type) ||
                      is_enum_type s fld.(return_type)) &&
                      arguments_conform fld.(fargs) α;
        | _ => false
        };

      query_conforms ty (_:f[[α]])
        with lookup_field_in_type s ty f :=
        {
        | Some fld => (is_scalar_type s fld.(return_type) ||
                      is_enum_type s fld.(return_type)) &&
                      arguments_conform fld.(fargs) α;
        | _ => false
        };

      query_conforms ty (f[[α]] { φ })
        with lookup_field_in_type s ty f :=
        {
        | Some fld => [&& (is_object_type s fld.(return_type) || is_abstract_type s fld.(return_type)),
                         arguments_conform fld.(fargs) α,
                         φ != [::] &
                         all (query_conforms fld.(return_type)) φ];
        | _ => false
        };

      query_conforms ty (_:f[[α]] { φ })
        with lookup_field_in_type s ty f :=
        {
        | Some fld => [&& (is_object_type s fld.(return_type) || is_abstract_type s fld.(return_type)),
                         arguments_conform fld.(fargs) α,
                         φ != [::] &
                         all (query_conforms fld.(return_type)) φ];
        | _ => false
        };

      query_conforms ty (on t { φ }) :=
        [&& is_fragment_spread_possible ty t,
         φ != [::] &
         all (query_conforms t) φ]
    }.

  (**
     queries_conform : Name -> List Query -> Bool 

     Check whether a list of queries conform to a given type in the schema.
     
     This definition captures the previous validation predicates:

     - ∀ query ∈ queries, query conforms to type in scope.

     - queries have compatible response shapes.

     - field merging is possible.

     ---- 
     **** Observations
     
     1. Empty lists : Our definition allows for a list of queries to be empty.
        We argue that this is not an issue, since we do check that subqueries 
        are not empty. If this list is empty and then evaluated, it would just 
        result in an empty list of results.

   *)
  Definition queries_conform (ty : Name) queries : bool :=
    [&& all (query_conforms ty) queries,
        have_compatible_response_shapes ty queries &
        is_field_merging_possible ty queries].
    
  
 
End QueryConformance.

Arguments argument_conforms [Vals].
Arguments arguments_conform [Vals].

Arguments is_fragment_spread_possible [Vals].
Arguments have_compatible_response_shapes [Vals].
Arguments is_field_merging_possible [Vals].
Arguments query_conforms [Vals].
Arguments queries_conform [Vals].