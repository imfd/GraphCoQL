From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

From extructures Require Import ord fset fmap.

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

  Variables Name Vals : ordType.
  
  
  Implicit Type queries : seq (@Query Name Vals).
  Implicit Type query : @Query Name Vals.
  Implicit Type type : @type Name.


  Variable s : @wfSchema Name Vals.
 
 
  
  (** Checks whether a query's argument (arg name + value associated) conforms to an argument
      of a field defined in the schema.
      
      It basically consists on checking whether the field has an argument with the same name
      as the query's argument, and whether the type of the value associated matches the
      type of the field's argument (as defined in the schema).

      ∃ argument ∈ field, name(argument) = name(α) ∧ value(α) has_type type(argument)
   **)
  Definition argument_conforms (args : seq FieldArgumentDefinition) (arg : Name * Vals) : bool :=
    let: (argname, value) := arg in
    has (fun argdef => let: FieldArgument name ty := argdef in
                    (name == argname) && s.(hasType) ty value) args.
  

  (** Checks whether a set of arguments (described as a partial mapping between names and values)
      conform to a set of fields. 

      See also [arguments_conforms].
   **)
  Definition arguments_conform (args : seq.seq FieldArgumentDefinition) (α : {fmap Name -> Vals}) : bool :=
    all (argument_conforms args) α.
     

  
  (** Checks whether a type can be used as an inline fragment's guard 
      in a given context with another type in scope (parent type).

      It basically amounts to intersecting the possible types of each
      and check that the intersection is not empty.


      See also [SchemaAux - get_possible_types].

     https://facebook.github.io/graphql/June2018/#sec-Fragment-spread-is-possible
     https://facebook.github.io/graphql/June2018/#GetPossibleTypes()
   **)
  Definition is_fragment_spread_possible parent_type ty : bool :=
    let ty_possible_types := get_possible_types s ty in
    let parent_possible_types := get_possible_types s parent_type in
    let applicable_types := (ty_possible_types :&: parent_possible_types)%SEQ in
    applicable_types != [::].

  


 
 Equations are_compatible_types : @type Name -> @type Name -> bool :=
   {
     are_compatible_types (NT rty) (NT rty')
       with (is_scalar_type s rty || is_enum_type s rty) :=
       {
       | true := rty == rty';
       | _ := is_composite_type s rty'
       };
     are_compatible_types (ListType rty) (ListType rty') := are_compatible_types rty rty';
     are_compatible_types _ _ := false
   }.

 Equations has_compatible_type (ty : Name) (rty : @type Name) query : bool :=
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

 (* Equations can't generate the graph *)
 (* This approach considers two field selections invalid, even if one of them
    will never be evaluated. For instance:
      https://tinyurl.com/y39tojbq
  *)
 Equations? have_compatible_response_shapes (ty : Name) queries : bool by wf (queries_size queries) :=
   {
     have_compatible_response_shapes _ [::] := true ;

     have_compatible_response_shapes ty (SingleField f _ :: qs)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := all (has_compatible_type ty fld.(return_type)) (find_fields_with_response_name f qs)
                        && have_compatible_response_shapes ty (filter_queries_with_label f qs);
       | _ := false
       };

     have_compatible_response_shapes ty (LabeledField l f _ :: qs)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := all (has_compatible_type ty fld.(return_type)) (find_fields_with_response_name l qs)
                         && have_compatible_response_shapes ty (filter_queries_with_label l qs);
       | _ := false
       };

      have_compatible_response_shapes ty (NestedField f _ β :: qs)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := let similar_queries := find_fields_with_response_name f qs in
                    [&& all (has_compatible_type ty fld.(return_type)) similar_queries,
                     have_compatible_response_shapes fld.(return_type) (β ++ merge_selection_sets similar_queries) &
                     have_compatible_response_shapes ty (filter_queries_with_label f qs)];
                     
                        
       | _ := false
       };
      
      have_compatible_response_shapes ty (NestedLabeledField l f _ β :: qs)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := let similar_queries := find_fields_with_response_name l qs in
                    [&& all (has_compatible_type ty fld.(return_type)) similar_queries,
                     have_compatible_response_shapes fld.(return_type) (β ++ merge_selection_sets similar_queries) &
                     have_compatible_response_shapes ty (filter_queries_with_label f qs)];
                     
                        
       | _ := false
       };

      
      have_compatible_response_shapes ty (InlineFragment t β :: qs) := have_compatible_response_shapes ty (β ++ qs)
                                                                                                      
   }.
 Proof.
   all: do [rewrite ?/similar_queries; leq_queries_size].
 Qed.
 Next Obligation.
   move: {2}(queries_size _) (leqnn (queries_size queries)) => n.
   elim: n queries ty => /= [| n IH] queries ty ; first by rewrite leqn0 => /queries_size_0_nil ->; constructor.
   case: queries => //= [| q queries]; first by constructor.
   case_query q; simp query_size => Hleq;
   simp have_compatible_response_shapes; constructor; do ? [lookup => /=; constructor]; apply: IH; leq_queries_size.
 Defined.



 
 Equations? is_field_merging_possible (ty : Name) queries : bool by wf (queries_size queries)  :=
   {
     is_field_merging_possible _ [::] := true;

     is_field_merging_possible ty (SingleField f α :: qs)
       with is_object_type s ty :=
       {
       | true := all (are_equivalent (SingleField f α)) (find_queries_with_label s f ty qs) &&
                    is_field_merging_possible ty (filter_queries_with_label f qs);
       
       | _ := all (are_equivalent (SingleField f α)) (find_fields_with_response_name f qs) &&
                 is_field_merging_possible ty (filter_queries_with_label f qs)
       };

     is_field_merging_possible ty (LabeledField l f α :: qs)
       with is_object_type s ty :=
       {
       | true := all (are_equivalent (LabeledField l f α)) (find_queries_with_label s l ty qs) &&
                    is_field_merging_possible ty (filter_queries_with_label l qs);
       
       | _ := all (are_equivalent (LabeledField l f α)) (find_fields_with_response_name l qs) &&
                 is_field_merging_possible ty (filter_queries_with_label l qs)
       };
     
     is_field_merging_possible ty (NestedField f α β :: qs)
       with lookup_field_in_type s ty f :=
       {
       | Some fld 
           with is_object_type s ty :=
           {
           | true := let similar_queries := find_queries_with_label s f ty qs in
                    [&& all (are_equivalent (NestedField f α β)) similar_queries,
                     is_field_merging_possible fld.(return_type) (β ++ merge_selection_sets similar_queries) &
                     is_field_merging_possible ty (filter_queries_with_label f qs)];
           
       
           | _ := let similar_queries := find_fields_with_response_name f qs in
                 [&& all (are_equivalent (NestedField f α β)) similar_queries,
                  is_field_merging_possible fld.(return_type) (β ++ merge_selection_sets similar_queries) &
                  is_field_merging_possible ty (filter_queries_with_label f qs)]
           };
       
       | _ := false 
       };

     is_field_merging_possible ty (NestedLabeledField l f α β :: qs)
       with lookup_field_in_type s ty f :=
       {
       | Some fld 
           with is_object_type s ty :=
           {
           | true := let similar_queries := find_queries_with_label s l ty qs in
                    [&& all (are_equivalent (NestedLabeledField l f α β)) similar_queries,
                     is_field_merging_possible fld.(return_type) (β ++ merge_selection_sets similar_queries) &
                     is_field_merging_possible ty (filter_queries_with_label l qs)];
           
       
           | _ := let similar_queries := find_fields_with_response_name l qs in
                 [&& all (are_equivalent (NestedLabeledField l f α β)) similar_queries,
                  is_field_merging_possible fld.(return_type) (β ++ merge_selection_sets similar_queries) &
                  is_field_merging_possible ty (filter_queries_with_label l qs)]
           };
       
       | _ := false 
       };

     is_field_merging_possible ty (InlineFragment t β :: qs)
       with is_fragment_spread_possible t ty :=
       {
       | true with is_object_type s ty :=
           {
           | true := is_field_merging_possible ty (β ++ qs);
           | _ := is_field_merging_possible t (β ++ qs) &&
                                           is_field_merging_possible ty qs
           };
       
       | _ := is_field_merging_possible ty qs
       }
   }.
 Proof.
   all: do ? [rewrite ?/similar_queries; leq_queries_size].
 Qed.
 Next Obligation.
   move: {2}(queries_size _) (leqnn (queries_size queries)) => n.
   elim: n ty queries => /= [| n IH] ty queries; first by rewrite leqn0 => /queries_size_0_nil ->; constructor.
   case: queries => /= [| q queries]; first by constructor.
   case_query q; simp query_size => Hleq;
   simp is_field_merging_possible; constructor; do ? [lookup; constructor]; last first.
   case is_fragment_spread_possible; constructor; last by apply: IH; leq_queries_size.
   all: do ? [case is_object_type => /=; by constructor; apply: IH; leq_queries_size].
 Defined.
 
        
  (** Checks whether a query conforms to a given schema.
      
      Every query (or selection of fields) is set in a given context
      of a particular type, therefore, the conformance is checked
      based on the schema and the current type in context.

     This checks the following things specified in the spec :
     1. Fields are defined (https://graphql.github.io/graphql-spec/June2018/#sec-Field-Selections-on-Objects-Interfaces-and-Unions-Types)
     2. Selection type is correct (https://graphql.github.io/graphql-spec/June2018/#sec-Leaf-Field-Selections)

     3. Arguments (https://graphql.github.io/graphql-spec/June2018/#sec-Argument-Names)

     4. Inline fragments are possible (https://graphql.github.io/graphql-spec/June2018/#sec-Fragment-spread-is-possible)
   **)
  Equations query_conforms (ty : Name) query : bool :=
    {
      query_conforms ty (SingleField fname α)
        with lookup_field_in_type s ty fname :=
        {
        | Some fld => (is_scalar_type s fld.(return_type) ||
                      is_enum_type s fld.(return_type)) &&
                      arguments_conform fld.(fargs) α;
        | _ => false
        };

      query_conforms ty (LabeledField _ fname α)
        with lookup_field_in_type s ty fname :=
        {
        | Some fld => (is_scalar_type s fld.(return_type) ||
                      is_enum_type s fld.(return_type)) &&
                      arguments_conform fld.(fargs) α;
        | _ => false
        };

      query_conforms ty (NestedField fname α φ)
        with lookup_field_in_type s ty fname :=
        {
        | Some fld => [&& (is_object_type s fld.(return_type) || is_abstract_type s fld.(return_type)),
                      arguments_conform fld.(fargs) α,
                      φ != [::] &
                      all (query_conforms fld.(return_type)) φ];
        | _ => false
        };

      query_conforms ty (NestedLabeledField _ fname α φ)
        with lookup_field_in_type s ty fname :=
        {
        | Some fld => [&& (is_object_type s fld.(return_type) || is_abstract_type s fld.(return_type)),
                      arguments_conform fld.(fargs) α,
                      φ != [::] &
                      all (query_conforms fld.(return_type)) φ];
        | _ => false
        };

      query_conforms ty (InlineFragment t φ) :=
        (* [&& [|| is_object_type s t, is_interface_type s t | is_union_type s t], (* This might be a bit redundant *) *)
        [&& is_fragment_spread_possible ty t,
         φ != [::] &
         all (query_conforms t) φ]
    }.


  (* Ignoring emptyness *)
  Definition queries_conform (ty : Name) queries : bool :=
    [&& all (query_conforms ty) queries,
     have_compatible_response_shapes ty queries &
     is_field_merging_possible ty queries].
    
  
 
End QueryConformance.

Arguments argument_conforms [Name Vals].
Arguments arguments_conform [Name Vals].

Arguments is_fragment_spread_possible [Name Vals].
Arguments have_compatible_response_shapes [Name Vals].
Arguments is_field_merging_possible [Name Vals].
Arguments query_conforms [Name Vals].
Arguments queries_conform [Name Vals].