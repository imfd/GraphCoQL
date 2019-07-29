From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

From extructures Require Import ord fset fmap.

Require Import Schema.
Require Import SchemaAux.
Require Import Query.
Require Import QueryAux.
Require Import SchemaWellFormedness.
Require Import SeqExtra.


Require Import Ssromega.

Section QueryConformance.

  Variables Name Vals : ordType.
  
  Implicit Type schema : @wfSchema Name Vals.  
  Implicit Type queries : seq (@Query Name Vals).
  Implicit Type query : @Query Name Vals.
  Implicit Type type : @type Name.

  Notation is_inline_fragment := (@is_inline_fragment Name Vals).

  Variable s : @wfSchema Name Vals.
 
  
  Lemma fset1I_eq {A : ordType} (a b : A) :
    (fset1 a :&: fset1 b)%fset != fset0 -> a = b.
  Proof.
    rewrite fset1I.
    case: ifP => //.
    by move/fset1P => //.
  Qed.

  Lemma fset1I_N_fset0 {A : ordType} (a : A) :
    (fset1 a :&: fset1 a)%fset != fset0.
  Proof.
    rewrite fset1I.
    case: ifP => //.
      by rewrite in_fset1 eqxx.
  Qed.
  
  (** Checks whether a query's argument (arg name + value associated) conforms to an argument
      of a field defined in the schema.
      
      It basically consists on checking whether the field has an argument with the same name
      as the query's argument, and whether the type of the value associated matches the
      type of the field's argument (as defined in the schema).

      ∃ argument ∈ field, name(argument) = name(α) ∧ value(α) has_type type(argument)
   **)
  Definition argument_conforms schema (args : seq FieldArgumentDefinition) (arg : Name * Vals) : bool :=
    let: (argname, value) := arg in
    has (fun argdef => let: FieldArgument name ty := argdef in
                    (name == argname) && schema.(hasType) ty value) args.
  

  (** Checks whether a set of arguments (described as a partial mapping between names and values)
      conform to a set of fields. 

      See also [arguments_conforms].
   **)
  Definition arguments_conform schema (args : seq.seq FieldArgumentDefinition) (α : {fmap Name -> Vals}) : bool :=
    all (argument_conforms schema args) α.
     

  
  (** Checks whether a type can be used as an inline fragment's guard 
      in a given context with another type in scope (parent type).

      It basically amounts to intersecting the possible types of each
      and check that the intersection is not empty.


      See also [SchemaAux - get_possible_types].

     https://facebook.github.io/graphql/June2018/#sec-Fragment-spread-is-possible
     https://facebook.github.io/graphql/June2018/#GetPossibleTypes()
   **)
  Definition is_fragment_spread_possible schema parent_type ty : bool :=
    let ty_possible_types := get_possible_types schema ty in
    let parent_possible_types := get_possible_types schema parent_type in
    let applicable_types := (ty_possible_types :&: parent_possible_types)%SEQ in
    applicable_types != [::].

  
  (* TODO: rename **)
  Lemma object_spreads_E schema parent_type ty :
    is_object_type schema ty ->
    is_fragment_spread_possible schema parent_type ty ->
    [\/ ty = parent_type,
     ty \in implementation schema parent_type |
     ty \in union_members schema parent_type].
  Proof.
    case: schema=> sch Hty Hwf Hobj Hspread.
    apply/in_possible_typesPwf=> //.
    move: Hspread.
    rewrite /is_fragment_spread_possible.
    simp get_possible_types.
    move/is_object_type_wfP: Hobj => [intfs [flds Hlook]].
    rewrite Hlook /=.
    by case lookup_type => [t|] //=; case: t => //=; intros; apply: seq1I_N_nil.
    
  Qed.


  

 
 Equations are_compatible_types schema : @type Name -> @type Name -> bool :=
   {
     are_compatible_types schema (NT rty) (NT rty')
       with (is_scalar_type schema rty || is_enum_type schema rty) :=
       {
       | true := rty == rty';
       | _ := is_composite_type schema rty'
       };
     are_compatible_types schema (ListType rty) (ListType rty') := are_compatible_types schema rty rty';
     are_compatible_types _ _ _ := false
   }.

 Equations has_compatible_type (ty : Name) (rty : @type Name) query : bool :=
   {
     has_compatible_type ty rty (SingleField f _)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := are_compatible_types s fld.(return_type) rty;
       | _ := false
       };
     has_compatible_type ty rty (LabeledField _ f _)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := are_compatible_types s fld.(return_type) rty;
       | _ := false
       };
     
     has_compatible_type ty rty (NestedField f _ _)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := are_compatible_types s fld.(return_type) rty;
       | _ := false
       };
     
     has_compatible_type ty rty (NestedLabeledField _ f _ _)
       with lookup_field_in_type s ty f :=
       {
       | Some fld := are_compatible_types s fld.(return_type) rty;
       | _ := false
       };

     has_compatible_type _ _ (InlineFragment _ _) := false
   }.

 (* Equations can't generate the graph *)
 (* This approach considers two field selections invalid, even if one of them
    will never be evaluated. For instance:
      https://tinyurl.com/y39tojbq
  *)
 Equations(noind) have_compatible_response_shapes (ty : Name) queries : bool by wf (queries_size queries) :=
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
 Solve Obligations with intros; simp query_size; have Hleq := (filter_queries_with_label_leq_size f qs); ssromega.
 Solve Obligations with intros; simp query_size; have Hleq := (filter_queries_with_label_leq_size l qs); ssromega.
 Next Obligation.
   simp query_size; rewrite queries_size_cat.
   have Hleq1 := (found_fields_leq_size f qs).
   have Hleq2 := (merged_selections_leq (find_fields_with_response_name f qs)); ssromega.
 Qed.
 Next Obligation.
   simp query_size; rewrite queries_size_cat.
   have Hleq1 := (found_fields_leq_size l qs).
   have Hleq2 := (merged_selections_leq (find_fields_with_response_name l qs)); ssromega.
 Qed.
 Next Obligation.
   by rewrite queries_size_cat; simp query_size.
 Qed.
 

 Equations is_field_merging_possible (ty : Name) queries : bool by wf (queries_size queries)  :=
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
       with is_fragment_spread_possible s t ty :=
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
 
 Solve Obligations with intros; simp query_size; rewrite ?queries_size_cat; do ? ssromega.
 Solve Obligations with intros; simp query_size; have Hleq := (filter_queries_with_label_leq_size f qs); ssromega.
 Solve Obligations with intros; simp query_size; have Hleq := (filter_queries_with_label_leq_size l qs); ssromega.

 Next Obligation.
   simp query_size; rewrite queries_size_cat.
   have Hleq1 := (found_queries_leq_size s f ty qs).
   have Hleq2 := (merged_selections_leq (find_queries_with_label s f ty qs)); ssromega.
 Qed.
 Next Obligation.
   simp query_size; rewrite queries_size_cat.
   have Hleq1 := (found_fields_leq_size f qs).
   have Hleq2 := (merged_selections_leq (find_fields_with_response_name f qs)); ssromega.
 Qed.
 Next Obligation.
   simp query_size; rewrite queries_size_cat.
   have Hleq1 := (found_queries_leq_size s l ty qs).
   have Hleq2 := (merged_selections_leq (find_queries_with_label s l ty qs)); ssromega.
 Qed.
  Next Obligation.
   simp query_size; rewrite queries_size_cat.
   have Hleq1 := (found_fields_leq_size l qs).
   have Hleq2 := (merged_selections_leq (find_fields_with_response_name l qs)); ssromega.
  Qed.
  Next Obligation.
    move: {2}(queries_size _) (leqnn (queries_size queries)) => n.
    elim: n ty queries => /= [| n IH] ty queries.
    by rewrite leqn0 => /queries_size_0_nil ->; constructor.
    
    case: queries => //=; first by constructor.
    case=> //= [f α | l f α | f α β | l f α β | t β] qs; simp query_size => Hleq.
    - rewrite is_field_merging_possible_equation_2.
      apply: is_field_merging_possible_graph_refinement_2.
      case Hscope : is_object_type => /=.
      * rewrite is_field_merging_possible_clause_2_equation_1.
        apply: is_field_merging_possible_clause_2_graph_equation_1.
        apply: IH => //=.
          by have Hfleq := (filter_queries_with_label_leq_size f qs); ssromega.

      * rewrite is_field_merging_possible_clause_2_equation_2.
        apply: is_field_merging_possible_clause_2_graph_equation_2.
        apply: IH => //=.
          by have Hfleq := (filter_queries_with_label_leq_size f qs); ssromega.

    - rewrite is_field_merging_possible_equation_3.
      have Hfleq := (filter_queries_with_label_leq_size l qs).
      apply: is_field_merging_possible_graph_refinement_3.
      case Hscope : is_object_type => /=.
      * rewrite is_field_merging_possible_clause_3_equation_1.
        apply: is_field_merging_possible_clause_3_graph_equation_1.
        by apply: IH => //=; ssromega.

      * rewrite is_field_merging_possible_clause_3_equation_2.
        apply: is_field_merging_possible_clause_3_graph_equation_2.
        apply: IH => //=; ssromega.

    - rewrite is_field_merging_possible_equation_4.
      have Hfleq := (filter_queries_with_label_leq_size f qs).
      have Hfoundleq1 := (found_queries_leq_size s f ty qs).
      have Hfoundleq2 := (found_fields_leq_size f qs).
      have Hmleq1 := (merged_selections_leq (find_queries_with_label s f ty qs)).
      have Hmleq2 := (merged_selections_leq (find_fields_with_response_name f qs)).
      apply: is_field_merging_possible_graph_refinement_4.
      case Hlook : lookup_field_in_type => [fld|] //=.
      * apply: is_field_merging_possible_clause_4_graph_refinement_1.
        case Hscope : is_object_type => /=.
        + rewrite is_field_merging_possible_clause_4_clause_1_equation_1.
          apply: is_field_merging_possible_clause_4_clause_1_graph_equation_1 => /=.
          by apply: IH => //=; rewrite queries_size_cat; ssromega.
          by apply: IH => //=; ssromega.
            
        + rewrite is_field_merging_possible_clause_4_clause_1_equation_2.
          apply: is_field_merging_possible_clause_4_clause_1_graph_equation_2 => /=.
          by apply: IH => //=; rewrite queries_size_cat; ssromega.
          by apply: IH => //=; ssromega.

      * rewrite is_field_merging_possible_clause_4_equation_2 //=.
        by apply: is_field_merging_possible_clause_4_graph_equation_2.

    - rewrite is_field_merging_possible_equation_5.
      have Hfleq := (filter_queries_with_label_leq_size l qs).
      have Hfoundleq1 := (found_queries_leq_size s l ty qs).
      have Hfoundleq2 := (found_fields_leq_size l qs).
      have Hmleq1 := (merged_selections_leq (find_queries_with_label s l ty qs)).
      have Hmleq2 := (merged_selections_leq (find_fields_with_response_name l qs)).
      apply: is_field_merging_possible_graph_refinement_5.
      case Hlook : lookup_field_in_type => [fld|] //=.
      * apply: is_field_merging_possible_clause_5_graph_refinement_1.
        case Hscope : is_object_type => /=.
        + rewrite is_field_merging_possible_clause_5_clause_1_equation_1.
          apply: is_field_merging_possible_clause_5_clause_1_graph_equation_1 => /=.
          by apply: IH => //=; rewrite queries_size_cat; ssromega.
          by apply: IH => //=; ssromega.
            
        + rewrite is_field_merging_possible_clause_5_clause_1_equation_2.
          apply: is_field_merging_possible_clause_5_clause_1_graph_equation_2 => /=.
          by apply: IH => //=; rewrite queries_size_cat; ssromega.
          by apply: IH => //=; ssromega.

      * rewrite is_field_merging_possible_clause_5_equation_2 //=.
        by apply: is_field_merging_possible_clause_5_graph_equation_2.

    - rewrite is_field_merging_possible_equation_6.
      apply: is_field_merging_possible_graph_refinement_6.
      case Hspreads : is_fragment_spread_possible => /=.
      * rewrite is_field_merging_possible_clause_6_equation_1 //=.
        apply: is_field_merging_possible_clause_6_graph_refinement_1.
        case Hscope : is_object_type => /=.
        + rewrite is_field_merging_possible_clause_6_clause_1_equation_1.
          apply: is_field_merging_possible_clause_6_clause_1_graph_equation_1.
          by apply: IH => //=; rewrite queries_size_cat.

        + rewrite is_field_merging_possible_clause_6_clause_1_equation_2.
          apply: is_field_merging_possible_clause_6_clause_1_graph_equation_2.
          by apply: IH; rewrite queries_size_cat.
          by apply: IH; ssromega.

      * rewrite is_field_merging_possible_clause_6_equation_2 //=.
        apply: is_field_merging_possible_clause_6_graph_equation_2.
        by apply: IH => //=; ssromega.
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

  (* Equations? selections_are_defined (ty : Name) (φ : seq (@Query Name Vals)) : bool by wf (queries_size φ) := *)
  (*   { *)
  (*     selections_are_defined _ [::] := true; *)
      
  (*     selections_are_defined ty (InlineFragment t β :: φ) := *)
  (*       selections_are_defined t β && selections_are_defined ty φ; *)

  (*     selections_are_defined ty (q :: φ) := *)
  (*       isSome (lookup_field_in_type s ty (qname q _)) && selections_are_defined ty φ *)
  (*   }. *)
  (* Proof. *)
  (*   all: do [simp query_size; ssromega]. *)
  (* Qed. *)

  (* Equations? selections_have_appropriate_types (ty : Name) (φ : seq (@Query Name Vals)) : bool := *)
  (*   { *)
  (*     selections_have_appropriate_types _ [::] := true; *)

      
  
                                      
      
  
  Equations query_conforms (ty : Name) query : bool :=
    {
      query_conforms ty (SingleField fname α)
        with lookup_field_in_type s ty fname :=
        {
        | Some fld => (is_scalar_type s fld.(return_type) ||
                      is_enum_type s fld.(return_type)) &&
                      arguments_conform s fld.(fargs) α;
        | _ => false
        };

      query_conforms ty (LabeledField _ fname α)
        with lookup_field_in_type s ty fname :=
        {
        | Some fld => (is_scalar_type s fld.(return_type) ||
                      is_enum_type s fld.(return_type)) &&
                      arguments_conform s fld.(fargs) α;
        | _ => false
        };

      query_conforms ty (NestedField fname α φ)
        with lookup_field_in_type s ty fname :=
        {
        | Some fld => [&& (is_object_type s fld.(return_type) || is_abstract_type s fld.(return_type)),
                      arguments_conform s fld.(fargs) α,
                      φ != [::] &
                      all (query_conforms fld.(return_type)) φ];
        | _ => false
        };

      query_conforms ty (NestedLabeledField _ fname α φ)
        with lookup_field_in_type s ty fname :=
        {
        | Some fld => [&& (is_object_type s fld.(return_type) || is_abstract_type s fld.(return_type)),
                      arguments_conform s fld.(fargs) α,
                      φ != [::] &
                      all (query_conforms fld.(return_type)) φ];
        | _ => false
        };

      query_conforms ty (InlineFragment t φ) :=
        (* [&& [|| is_object_type s t, is_interface_type s t | is_union_type s t], (* This might be a bit redundant *) *)
        [&& is_fragment_spread_possible s ty t,
         φ != [::] &
         all (query_conforms t) φ]
    }.


  (* Ignoring emptyness *)
  Definition queries_conform (ty : Name) queries : bool :=
    [&& all (query_conforms ty) queries,
     have_compatible_response_shapes ty queries &
     is_field_merging_possible ty queries].
    
  Definition queries_conform_inv ty φ :
    all (query_conforms ty) φ ->
    have_compatible_response_shapes ty φ ->
    is_field_merging_possible ty φ ->
    queries_conform ty φ.
  Proof.
    by intros; rewrite /queries_conform; apply/and3P; split.
  Qed.

  Transparent qname.
  Lemma conformed_fields_lookup ty φ :
    queries_conform ty φ ->
    forall q (Hfield : q.(is_field)),
      q \in φ ->
            exists fld,
              lookup_field_in_type s ty (qname q Hfield) = Some fld.
  Proof.
    elim: φ => //=; case=> [f α | l f α | f α β | l f α β | t β] φ IH Hqsc q Hfield.

    - rewrite inE => /orP [/eqP Heq | Hin].
      * move: Hfield; rewrite Heq /= => Hfield.
        move: Hqsc; rewrite /queries_conform /=; simp query_conforms; case lookup_field_in_type => //= fld _.
          by exists fld.
      * apply: IH => //=.
        move: Hqsc; rewrite /queries_conform /=; case/and3P=> [/andP [_ Hqsc]].
        simp have_compatible_response_shapes; case lookup_field_in_type => //= fld.
  Abort.
    

  Lemma found_fields_with_response_name_share_field_name_in_obj ty rname φ :
    is_object_type s ty ->
    is_field_merging_possible ty φ ->
    forall fname,
      all (has_field_name fname) (find_queries_with_label s rname ty φ).
  Proof.
    elim: φ => //=; case=> [f α | l f α | f α β | l f α β | t β] φ IH Hscope; simp is_field_merging_possible.

    - rewrite Hscope /=; simp are_equivalent => /andP [Hequiv Hmerge] fname.
  Admitted.
                           
    

(*
  Lemma queries_conform_inv schema ty queries :
    queries != [::] ->
    all (query_conforms schema ty) queries ->
    queries_conform schema ty queries.
  Proof. by move=> *; rewrite /queries_conform; apply/andP. Qed.
*)
  
  Lemma nf_conformsP type_in_scope f α φ :
    reflect (exists2 fld, lookup_field_in_type s type_in_scope f = Some fld &
                          [&& (is_object_type s fld.(return_type) || is_abstract_type s fld.(return_type)),
                           arguments_conform s fld.(fargs) α,
                           φ != [::] &
                           all (query_conforms fld.(return_type)) φ])
            (query_conforms type_in_scope (NestedField f α φ)).
  Proof.
    apply: (iffP idP).
    - simp query_conforms.
      case Hlook : lookup_field_in_type => [fld |] //= H.
      by exists fld.
    - move=> [fld Hlook H].
      by simp query_conforms; rewrite Hlook. 
  Qed.

  Lemma nlf_conformsP type_in_scope l f α φ :
    reflect (exists2 fld, lookup_field_in_type s type_in_scope f = Some fld &
                          [&& (is_object_type s fld.(return_type) || is_abstract_type s fld.(return_type)),
                           arguments_conform s fld.(fargs) α,
                           φ != [::] &
                           all (query_conforms fld.(return_type)) φ])
            (query_conforms type_in_scope (NestedLabeledField l f α φ)).
  Proof.
    apply: (iffP idP).
    - simp query_conforms.
      case Hlook : lookup_field_in_type => [fld |] // H.
      by exists fld.
    - move=> [fld Hlook H].
      by simp query_conforms; rewrite Hlook. 
  Qed.
             
  Lemma ty_not_scalar_or_enum schema ty tdef:
    lookup_type schema ty = Some tdef ->
    ~~(is_scalar_type schema ty || is_enum_type schema ty) ->
    [\/ is_object_type schema ty, is_interface_type schema ty | is_union_type schema ty].
  Proof. 
    rewrite /negb.
    case: ifP => //.
    rewrite /is_scalar_type /is_enum_type.
    case Hlook: lookup_type => [sm|] //.
    case: sm Hlook => //.
    by move=> o intfs flds Hlook _ _ _; constructor; rewrite is_object_type_equation_1 Hlook.
    by move=> i flds Hlook _ _; constructor; rewrite is_interface_type_equation_1 Hlook.
    by move=> u mbs Hlook _ _; constructor; rewrite is_union_type_equation_1 Hlook.
  Qed.



  Ltac wfquery := case: schema=> sch Hhasty Hwf.
 
  Lemma object_spreads_in_object_scope type_in_scope t ϕ :
    is_object_type s type_in_scope ->
    is_object_type s t ->
    ϕ != [::] ->
    queries_conform t ϕ -> 
    query_conforms type_in_scope (InlineFragment t ϕ) <->
    t = type_in_scope.
  Proof.
  Admitted.
  (* wfquery.
    move=> Hobj'.
    pose H' := Hobj'.
    move/is_object_type_E: H' => [obj [intfs [flds H]]] Hobj Hne Hqsc.
    split.
    - simp query_conforms.
      move/and4P=> [/or3P _ Hspread _ _].
      move: (object_spreads_E _ _ _ Hobj Hspread)=> [||] //.
      * move/has_implementation_is_interface=> Hcontr.
        move: (is_object_type_interfaceN Hobj') => //.
          by rewrite Hcontr.
      * move/in_union => Hcontr.
        move: (is_object_type_unionN Hobj').
          by rewrite Hcontr.
    - move=> Heq; rewrite Heq /=.
      move: Hqsc; rewrite /queries_conform.
      move/andP=> [Hall Hmerge].
      apply/and5P; split=> //.
        by apply/or3P; constructor 1.
        rewrite /is_fragment_spread_possible; simp get_possible_types => /=.
        by rewrite H /= /seqI /=; case: ifP => //=; rewrite inE => /eqP.
      by rewrite Heq in Hall.
      by rewrite -Heq.
  Qed.
*)

  Lemma interface_spreads_in_object_scope type_in_scope t ϕ :
    is_object_type s type_in_scope ->
    is_interface_type s t ->
    query_conforms type_in_scope (InlineFragment t ϕ) ->
    type_in_scope \in implementation s t.
  Proof.
    move/is_object_type_wfP=> [intfs [flds Hlook]].
    move/is_interface_type_wfP=> [iflds Hlook'].
    simp query_conforms=> /and3P [Hspread _ _].
    move: Hspread; rewrite /is_fragment_spread_possible; simp get_possible_types; rewrite Hlook Hlook' /=.
    by rewrite -seq1IC; apply: seq1I_N_nil.
  Qed.

  Lemma union_spreads_in_object_scope type_in_scope t ϕ :
    is_object_type s type_in_scope ->
    is_union_type s t ->
    query_conforms type_in_scope (InlineFragment t ϕ) ->
    type_in_scope \in union_members s t.
  Proof.
    funelim (is_object_type s type_in_scope) => // _.
    funelim (is_union_type s t) => // _.
    simp query_conforms.
    move/and3P=> [Hspread _ _].
    move: Hspread; rewrite /is_fragment_spread_possible; simp get_possible_types; rewrite Heq Heq0 /=.
    rewrite /union_members Heq.
    by rewrite -seq1IC; apply: seq1I_N_nil.
  Qed.

  Lemma abstract_spreads_in_object_scope type_in_scope t ϕ :
    is_object_type s type_in_scope ->
    ϕ != [::] ->
    queries_conform t ϕ ->
    (is_interface_type s t \/ is_union_type s t) ->
    reflect (type_in_scope \in implementation s t \/ type_in_scope \in union_members s t)
            (query_conforms type_in_scope (InlineFragment t ϕ)).
  Proof.
    move=> Hobj Hne Hqsc Htype.
    apply: (iffP idP).
    - case: Htype => [Hint | Hunion].
        by move/(interface_spreads_in_object_scope _ _ _ Hobj Hint); left.
      by move/(union_spreads_in_object_scope _ _ _ Hobj Hunion); right.
    - move: Hqsc; rewrite /queries_conform => /andP [Hall Hmerge].
      move=> H.      
      simp query_conforms; apply/and3P; split=> //.
      * move/is_object_type_wfP: Hobj => [intfs [flds Holook]].
        case: H => [Himpl | Hmb]; 
        rewrite /is_fragment_spread_possible; simp get_possible_types.
        move: (has_implementation_is_interface Himpl) => /is_interface_type_wfP [iflds Hilook].
          by rewrite Holook Hilook /= -seq1IC seq1I Himpl.
          
        move: (in_union Hmb) => /is_union_type_wfP [mbs Hulook].
        rewrite Holook Hulook /= -seq1IC seq1I.
        rewrite /union_members Hulook in Hmb.
        by rewrite Hmb.
  Qed.

  Ltac query_conforms := simp query_conforms; try move/and5P; try apply/and5P.




  
  
  Lemma object_spreads_in_interface_scope type_in_scope t ϕ :
    is_object_type s t ->
    is_interface_type s type_in_scope ->
    ϕ != [::] ->
    queries_conform t ϕ ->
    reflect (t \in implementation s type_in_scope)
            (query_conforms type_in_scope (InlineFragment t ϕ)).
  Proof.
    move=> Hobj Hintf Hne Hqsc.
    apply: (iffP idP).
    - simp query_conforms => /and3P [Hspread _ _].
      move: (object_spreads_E _ _ _ Hobj Hspread) => [Heq | // | /in_union Hun].
      * move: (is_object_type_interfaceN Hobj); rewrite Heq.
        by rewrite /negb Hintf.
      * by move: (is_interface_type_unionN Hintf); rewrite /negb Hun.
    - move=> Himpl; simp query_conforms.
      apply/and3P; split=> //=.
      * rewrite /is_fragment_spread_possible.
        move/get_possible_types_interfaceE: Hintf => ->.
        move/get_possible_types_objectE: Hobj => ->.
          by rewrite seq1I Himpl.

            by move: Hqsc; rewrite /queries_conform => /andP [H1 H2].
  Qed.


  Lemma scope_is_obj_or_abstract_for_field ty q :
    is_field q ->
    query_conforms ty q ->
    is_object_type s ty \/ is_interface_type s ty.
  Proof.
    case: q => //= [f α | l f α | f α φ | l f α φ] _; simp query_conforms;
    case Hlook: lookup_field_in_type => [fld|] // _;
    have H: lookup_field_in_type s ty f by rewrite /isSome Hlook.

    all: by apply: (lookup_field_in_type_is_obj_or_intf H).
  Qed.
  
  Lemma nested_field_is_obj_or_abstract ty n α ϕ :
    query_conforms ty (NestedField n α ϕ) ->
    is_object_type s ty \/ is_interface_type s ty.
  Proof.
    simp query_conforms.
    case Hlook: lookup_field_in_type => [fld|] // _.
    have H: lookup_field_in_type s ty n by rewrite /isSome Hlook.
      by apply: (lookup_field_in_type_is_obj_or_intf H).
  Qed.

  Lemma scope_is_obj_or_abstract_for_nlf ty l f α φ :
    query_conforms ty (NestedLabeledField l f α φ) ->
    is_object_type s ty \/ is_interface_type s ty.
  Proof.
    simp query_conforms.
    case Hlook: lookup_field_in_type => [fld|] // _.
    have H: lookup_field_in_type s ty f by rewrite /isSome Hlook.
      by apply: (lookup_field_in_type_is_obj_or_intf H).
  Qed.
  



    
 
  

            
    
  Lemma type_in_scope_N_scalar_enum :
    forall type_in_scope ϕ,
    query_conforms type_in_scope ϕ ->
    [\/ is_object_type s type_in_scope,
     is_interface_type s type_in_scope |
     is_union_type s type_in_scope].
  Proof.
    move=> ty.
    case=> [f α |  l f α |  f α ϕ |  l f α ϕ |  t ϕ]; simp query_conforms.
    all: do ?[case Hlook: lookup_field_in_type => [fld|] //= _;
              have H: lookup_field_in_type ty f by rewrite /isSome Hlook].
    all: do ?[by move: (lookup_field_in_type_is_obj_or_intf H) => [Hobj | Hint]; [constructor 1 | constructor 2]].
    
    (*
    case Hlook: lookup_type => [tdef|] //.
    by case: tdef Hlook => //=; do ?[rewrite fset0I //=];
                         [constructor 1; simp is_object_type
                         | constructor 2; simp is_interface_type
                         | constructor 3; simp is_union_type]; rewrite Hlook.
    
    by rewrite fset0I /=.
  Qed.*)
  Admitted.

  Lemma type_in_scope_N_scalar type_in_scope φ :
    query_conforms type_in_scope φ ->
    is_scalar_type s type_in_scope = false.
  Admitted.

  Lemma type_in_scope_N_enum type_in_scope φ :
    query_conforms type_in_scope φ ->
    is_enum_type s type_in_scope = false.
  Admitted.

  Lemma type_in_scope_N_obj_is_abstract type_in_scope φ :
    query_conforms type_in_scope φ ->
    is_object_type s type_in_scope = false ->
    is_abstract_type s type_in_scope.
  Proof.
    by move/type_in_scope_N_scalar_enum => [-> | Hintf | Hunion ] _ //; rewrite /is_abstract_type; apply/orP; [left | right].
  Qed.
  
  Lemma queries_conform_obj_int_union type_in_scope ϕ :
    ϕ != [::] ->
    queries_conform type_in_scope ϕ ->
    [\/ is_object_type s type_in_scope,
     is_interface_type s type_in_scope |
     is_union_type s type_in_scope].
  Proof.
    rewrite /queries_conform.
    case: ϕ => //= hd tl _.
    move/andP => [/andP [Hqc Hqsc] _].
    apply (type_in_scope_N_scalar_enum _ _ Hqc).
  Qed.

 

 
  
   Lemma nlf_conforms_lookup_some ty l n α ϕ :
    query_conforms ty (NestedLabeledField l n α ϕ) ->
    exists fld, lookup_field_in_type s ty n = Some fld.
  Proof. simp query_conforms.
    case Hlook : lookup_field_in_type => [fld'|] //.
    by exists fld'.
  Qed.

  Lemma queries_conform_int_impl ty ti qs :
    ty \in implementation s ti ->
    all (@is_field Name Vals) qs ->
    queries_conform ti qs ->       
    queries_conform ty qs.
  Proof.
    move=> Himpl Hflds.
    rewrite /queries_conform.
    move/andP=> [/allP Hqsc Hmerge].
    apply/andP; split=> //.
    apply/allP.
    move=> x Hin.
    move: (Hqsc x Hin) => {Hin}.
    case: x => //; [move=> f α | move=> l f α | move=> f α ϕ | move=> l f α ϕ | move=> t ϕ];
    simp query_conforms; do ? rewrite (field_in_interface_in_object f Himpl);
     do ? case lookup_field_in_type => //.
    - Admitted. (* Invalid case - all fields *)

  (* Not valid 
  Lemma inline_conforms_to_same_type t ϕ :
    [\/ is_object_type t, is_interface_type t | is_union_type t] ->
    queries_conform t ϕ ->
    query_conforms t (InlineFragment t ϕ).
  Proof.
    move=> Hty Hqsc /=; apply/and3P; split=> //.
    by apply/or3P.
    case: Hty => [Hobj | Hintf | Hunion]; rewrite /is_fragment_spread_possible;
    [rewrite (get_possible_types_objectE Hobj) | rewrite (get_possible_types_interfaceE Hintf)|  ]. apply: fset1I_N_fset0.
      by apply: eq_spreads.
  Qed. *)

  

  Lemma inline_preserves_conformance type_in_scope ϕ :
    query_conforms type_in_scope ϕ ->
    query_conforms type_in_scope (InlineFragment type_in_scope [:: ϕ]).
  Proof.
    simp query_conforms => Hqc.
    apply/and3P; split=> //.
    rewrite /is_fragment_spread_possible; simp get_possible_types.
    
    move: (type_in_scope_N_scalar_enum _ _ Hqc) => [Hobj | Hint | Hunion].
    funelim (is_object_type s type_in_scope) => //.
    Admitted.
 

  


  Lemma nested_conforms_list ty n α ϕ :
    query_conforms ty (NestedField n α ϕ) -> ϕ != [::].
  Proof.
    simp query_conforms.
    case lookup_field_in_type => // f.
      by move/and4P=> [_ _ Hne _].
  Qed.

   Lemma inline_subqueries_conform ty t ϕ :
    query_conforms ty (InlineFragment t ϕ) ->
    all (query_conforms t) ϕ.
  Proof.
    by simp query_conforms; case/and3P.
  Qed.

  Lemma sf_conforms_in_interface_in_obj ti tyo f α :
    tyo \in implementation s ti ->
            query_conforms ti (SingleField f α) ->
            query_conforms tyo (SingleField f α).
  Proof.
    move=> Hin.
    simp query_conforms.
    case Hlook : lookup_field_in_type => [fld |] //= /andP [Hty Hα].
    move: (in_implementation_is_object Hin) => Hobj.
    move: (field_in_interface_in_object_same_return_type Hin Hlook) => [fld' Hlook' Hrty].
    rewrite Hlook' /= -Hrty.
    apply/andP; split => //.
    move: Hα; rewrite /arguments_conform.
    move/allP=> Hα.
    apply/allP=> arg Hain.
    move: (Hα arg Hain) => {Hα Hain}.
    case: arg => n v.
    have: lookup_field_in_type s ti f = Some fld -> fld \in fields s ti.
    move: (has_implementation_is_interface Hin) => /is_interface_type_E.
    case=> [i [flds Hilook]].
    
    rewrite /fields /lookup_field_in_type Hilook.
  Admitted.

  Transparent qresponse_name.


  Ltac apply_and3P := apply/and3P; split=> //.
  
  Lemma filter_preserves_conformance label ty φ :
    queries_conform ty φ ->
    queries_conform ty (filter_queries_with_label label φ).
  Proof.
    Abort.
    
  
  
 
End QueryConformance.

Arguments have_compatible_response_shapes [Name Vals].
Arguments is_field_merging_possible [Name Vals].
Arguments is_fragment_spread_possible [Name Vals].
Arguments query_conforms [Name Vals].
Arguments queries_conform [Name Vals].