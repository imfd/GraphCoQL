From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

From extructures Require Import ord fset fmap.

Require Import Schema.
Require Import SchemaAux.
Require Import Query.
Require Import QueryAux.
Require Import SchemaWellFormedness.


Section QueryConformance.

  Variables Name Vals : ordType.
  
  Implicit Type schema : @wfSchema Name Vals.  
  Implicit Type queries : seq (@Query Name Vals).
  Implicit Type query : @Query Name Vals.
  Implicit Type type : @type Name.


  
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
    let applicable_types := (ty_possible_types :&: parent_possible_types)%fset in
    applicable_types != fset0.

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
    case lookup_type; case.
    - by move=> s; rewrite fsetI0.
    - by move=> o i fs /fset1I_eq ->; rewrite in_fset1.
    - by move=> i ifldsc; rewrite fset1I; case: ifP => //.
    - by move=> u mbs; rewrite fset1I; case: ifP.
    - by move=> e ev; rewrite fsetI0.
    - by rewrite fsetI0.
  Qed.


  (*Lemma eq_spreads schema ty :
    [\/ is_object_type schema ty, is_interface_type schema ty | is_union_type schema ty] ->
    is_fragment_spread_possible schema ty ty.
  Proof.
    case.
    - move/is_object_type_E=> [obj [intf [flds Hlook]]].
      rewrite /is_fragment_spread_possible /get_possible_types Hlook.
        by apply: fset1I_N_fset0.
    - move/is_interface_type_E => [intf [flds Hlook]].
      rewrite /is_fragment_spread_possible /get_possible_types Hlook.
   *)

      
  (** Checks whether a query conforms to a given schema.
      
      Every query (or selection of fields) is set in a given context
      of a particular type, therefore, the conformance is checked
      based on the schema and the current type in context.

  **)
  Fixpoint query_conforms schema ty query :=
    match query with
    | SingleField fname α => match lookup_field_in_type schema ty fname with
                            | Some fld => (is_scalar_type schema fld.(return_type) ||
                                          is_enum_type schema fld.(return_type)) &&
                                          arguments_conform schema fld.(fargs) α
                            | _ => false
                            end
    | LabeledField _ fname α =>  match lookup_field_in_type schema ty fname with
                                | Some fld => (is_scalar_type schema fld.(return_type) ||
                                              is_enum_type schema fld.(return_type)) &&
                                              arguments_conform schema fld.(fargs) α
                                  
                                | _ => false
                                end
    | NestedField fname α ϕ =>
      match lookup_field_in_type schema ty fname with
      | Some fld => [&& ~~(is_scalar_type schema fld.(return_type) || is_enum_type schema fld.(return_type)),
                    arguments_conform schema fld.(fargs) α,
                    ϕ != [::] &
                    all (query_conforms schema fld.(return_type)) ϕ]
      | _ => false
      end
      
    | NestedLabeledField _ fname α ϕ =>
        match lookup_field_in_type schema ty fname with
        | Some fld => [&& ~~(is_scalar_type schema fld.(return_type) || is_enum_type schema fld.(return_type)),
                      arguments_conform schema fld.(fargs) α,
                       ϕ != [::] &
                      all (query_conforms schema fld.(return_type)) ϕ]
        | _ => false
        end
        
    | InlineFragment t ϕ =>
      [&& [|| is_object_type schema t, is_interface_type schema t | is_union_type schema t], (* This might be a bit redundant *)
       is_fragment_spread_possible schema ty t,
       ϕ != [::] &
       all (query_conforms schema t) ϕ]
    end.

  Definition queries_conform schema ty queries := (queries != [::]) && (all (query_conforms schema ty) queries).

 (* Lemma queries_conformE schema ty queries :
    queries_conform schema ty queries ->
    queries != [::] /\ all (query_conforms schema ty) queries.
  Proof. by rewrite /queries_conform; move/andP. Qed.
  *)

  Lemma queries_conform_cons schema ty x s :
    queries_conform schema ty (x :: s) = (query_conforms schema ty x && all (query_conforms schema ty) s).
  Proof.
      by rewrite /queries_conform => /=.
  Qed.

  Lemma queries_conform_inv schema ty queries :
    queries != [::] ->
    all (query_conforms schema ty) queries ->
    queries_conform schema ty queries.
  Proof. by move=> *; rewrite /queries_conform; apply/andP. Qed.

  
  Lemma nf_conformsP schema type_in_scope f α φ :
    reflect (exists2 fld, lookup_field_in_type schema type_in_scope f = Some fld &
                          [&& ~~(is_scalar_type schema fld.(return_type) || is_enum_type schema fld.(return_type)),
                           arguments_conform schema fld.(fargs) α &
                           queries_conform schema fld.(return_type) φ])
            (query_conforms schema type_in_scope (NestedField f α φ)).
  Proof.
    apply: (iffP idP).
    - rewrite /query_conforms.
      case Hlook : lookup_field_in_type => [fld |] // H.
      by exists fld.
    - move=> [fld Hlook H].
      by rewrite /query_conforms Hlook. 
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
 
  Lemma object_spreads_in_object_scope schema type_in_scope t ϕ :
    is_object_type schema type_in_scope ->
    is_object_type schema t ->
    queries_conform schema t ϕ -> 
    query_conforms schema type_in_scope (InlineFragment t ϕ) <->
    t = type_in_scope.
  Proof.
    wfquery.
    move=> Hobj'.
    pose H' := Hobj'.
    move/is_object_type_E: H' => [obj [intfs [flds H]]].
    move=> Hobj.
    move=> Hqsc.
    split.
    - rewrite /query_conforms.
      move/and4P=> [/or3P _ Hspread _ _].
      move: (object_spreads_E Hobj Hspread)=> [||] //.
      * move/has_implementation_is_interface=> Hcontr.
        move: (is_object_type_interfaceN Hobj') => //.
          by rewrite Hcontr.
      * move/in_union => Hcontr.
        move: (is_object_type_unionN Hobj').
          by rewrite Hcontr.
    - move=> Heq; rewrite Heq /=.
      move: Hqsc; rewrite /queries_conform.
      move/andP=> [Hne Hall].
      apply/and4P; split=> //.
        by apply/or3P; constructor 1.
        rewrite /is_fragment_spread_possible. simp get_possible_types => /=.
        by rewrite H; apply: fset1I_N_fset0.
      by rewrite Heq in Hall.
  Qed.

  Lemma interface_spreads_in_object_scope schema type_in_scope t ϕ :
    is_object_type schema type_in_scope ->
    is_interface_type schema t ->
    query_conforms schema type_in_scope (InlineFragment t ϕ) ->
    type_in_scope \in implementation schema t.
  Proof.
    move/is_object_type_wfP=> [intfs [flds Hlook]].
    move/is_interface_type_wfP=> [iflds Hlook'].
    rewrite /query_conforms=> /and4P [_ Hspread _ _].
    move: Hspread; rewrite /is_fragment_spread_possible; simp get_possible_types; rewrite Hlook Hlook' /=.
    rewrite fsetIC fset1I.
    by case: ifP.
  Qed.

  Lemma union_spreads_in_object_scope schema type_in_scope t ϕ :
    is_object_type schema type_in_scope ->
    is_union_type schema t ->
    query_conforms schema type_in_scope (InlineFragment t ϕ) ->
    type_in_scope \in union_members schema t.
  Proof.
    funelim (is_object_type schema type_in_scope) => // _.
    funelim (is_union_type schema t) => // _.
    rewrite /query_conforms.
    move/and4P=> [_ Hspread _ _].
    move: Hspread; rewrite /is_fragment_spread_possible; simp get_possible_types; rewrite Heq Heq0 /=.
    rewrite fsetIC fset1I.
    case: ifP => //.
    by rewrite /union_members Heq.
  Qed.

  Lemma abstract_spreads_in_object_scope schema type_in_scope t ϕ :
    is_object_type schema type_in_scope ->
    queries_conform schema t ϕ ->
    (is_interface_type schema t \/ is_union_type schema t) ->
    reflect (type_in_scope \in implementation schema t \/ type_in_scope \in union_members schema t)
            (query_conforms schema type_in_scope (InlineFragment t ϕ)).
  Proof.
    move=> Hobj Hqsc Htype.
    apply: (iffP idP).
    - case: Htype => [Hint | Hunion].
        by move/(interface_spreads_in_object_scope Hobj Hint); left.
      by move/(union_spreads_in_object_scope Hobj Hunion); right.
    - move: Hqsc; rewrite /queries_conform => /andP [Hne Hall].
      move=> H.      
      rewrite /query_conforms; apply/and4P; split=> //.
      * by apply/or3P; case: Htype; [constructor 2 | constructor 3].
      * move/is_object_type_wfP: Hobj => [intfs [flds Holook]].
        case: H => [Himpl | Hmb]; 
        rewrite /is_fragment_spread_possible; simp get_possible_types.
        move: (has_implementation_is_interface Himpl) => /is_interface_type_wfP [iflds Hilook].
        by rewrite Holook Hilook fsetIC fset1I Himpl.
        move: (in_union Hmb) => /is_union_type_wfP [mbs Hulook].
        rewrite Holook Hulook fsetIC fset1I.
        rewrite /union_members Hulook in Hmb.
        by rewrite Hmb.
  Qed.

  Ltac query_conforms := rewrite /query_conforms -/(query_conforms _ _); try move/and4P; try apply/and4P.




  
  
  Lemma object_spreads_in_interface_scope schema type_in_scope t ϕ :
    is_object_type schema t ->
    is_interface_type schema type_in_scope ->
    queries_conform schema t ϕ ->
    reflect (t \in implementation schema type_in_scope)
            (query_conforms schema type_in_scope (InlineFragment t ϕ)).
  Proof.
    move=> Hobj Hintf Hqsc.
    apply: (iffP idP).
    - query_conforms.
      move=> [_ Hspread _ _].
      move: (object_spreads_E Hobj Hspread) => [Heq | // | /in_union Hun].
      * move: (is_object_type_interfaceN Hobj); rewrite Heq.
        by rewrite /negb Hintf.
      * by move: (is_interface_type_unionN Hintf); rewrite /negb Hun.
    - move=> Himpl.
      query_conforms; split.
      * by apply/or3P; constructor 1.
      * rewrite /is_fragment_spread_possible.
        move/get_possible_types_interfaceE: Hintf => ->.
        move/get_possible_types_objectE: Hobj => ->.
        by rewrite fset1I Himpl.
      * by move: Hqsc; rewrite /queries_conform => /andP [H _].
      * by move: Hqsc; rewrite /queries_conform => /andP [_ H].
  Qed.
        
  Lemma nested_field_is_obj_or_abstract schema ty n α ϕ :
    query_conforms schema ty (NestedField n α ϕ) ->
    is_object_type schema ty \/ is_interface_type schema ty.
  Proof.
    rewrite /query_conforms.
    case Hlook: lookup_field_in_type => [fld|] // _.
    have H: lookup_field_in_type schema ty n by rewrite /isSome Hlook.
      by apply: (lookup_field_in_type_is_obj_or_intf H).
  Qed.


  Notation is_inline_fragment := (@is_inline_fragment Name Vals).


    
 
  

            
    
  Lemma type_in_scope_N_scalar_enum schema type_in_scope ϕ :
    query_conforms schema type_in_scope ϕ ->
    [\/ is_object_type schema type_in_scope,
     is_interface_type schema type_in_scope |
     is_union_type schema type_in_scope].
  Proof.
    case: ϕ; [move=> f α | move=> l f α | move=> f α ϕ | move=> l f α ϕ | move=> t ϕ];
    do ?[rewrite /query_conforms;
         case Hlook: lookup_field_in_type => [fld|] // _;
         have H: lookup_field_in_type schema type_in_scope f by rewrite /isSome Hlook].
    all: do ?[by move: (lookup_field_in_type_is_obj_or_intf H) => [Hobj | Hint]; [constructor 1 | constructor 2]].

    move/and4P=> [/or3P Hty Hspread Hne _] => //.
    move: Hspread.
    rewrite /is_fragment_spread_possible.
    simp get_possible_types; rewrite fsetIC /=.
    case Hlook: lookup_type => [tdef|] //.
    by case: tdef Hlook => //=; do ?[rewrite fset0I //=];
                         [constructor 1; simp is_object_type
                         | constructor 2; simp is_interface_type
                         | constructor 3; simp is_union_type]; rewrite Hlook.
    
    by rewrite fset0I /=.
  Qed.

  Lemma type_in_scope_N_obj_is_abstract schema type_in_scope φ :
    query_conforms schema type_in_scope φ ->
    is_object_type schema type_in_scope = false ->
    is_abstract_type schema type_in_scope.
  Proof.
    by move/type_in_scope_N_scalar_enum => [-> | Hintf | Hunion ] _ //; rewrite /is_abstract_type; apply/orP; [left | right].
  Qed.
  
  Lemma queries_conform_obj_int_union schema type_in_scope ϕ :
    queries_conform schema type_in_scope ϕ ->
    [\/ is_object_type schema type_in_scope,
     is_interface_type schema type_in_scope |
     is_union_type schema type_in_scope].
  Proof.
    rewrite /queries_conform.
    case: ϕ => // hd tl.
    move/andP=> [Hnil /= /andP [Hhd _]].
    by apply: (type_in_scope_N_scalar_enum Hhd).
  Qed.

 

 
  
   Lemma nlf_conforms_lookup_some schema ty l n α ϕ :
    query_conforms schema ty (NestedLabeledField l n α ϕ) ->
    exists fld, lookup_field_in_type schema ty n = Some fld.
  Proof. rewrite /query_conforms.
    case Hlook : lookup_field_in_type => [fld'|] //.
    by exists fld'.
  Qed.

  Lemma queries_conform_int_impl schema ty ti qs :
    ty \in implementation schema ti ->
    all (@is_field Name Vals) qs ->
    queries_conform schema ti qs ->       
    queries_conform schema ty qs.
  Proof.
    move=> Himpl Hflds.
    rewrite /queries_conform.
    move/andP=> [Hne /allP Hqsc].
    apply/andP; split=> //.
    apply/allP.
    move=> x Hin.
    move: (Hqsc x Hin) => {Hin}.
    case: x => //; [move=> f α | move=> l f α | move=> f α ϕ | move=> l f α ϕ | move=> t ϕ];
    rewrite /query_conforms; do ? rewrite (field_in_interface_in_object schema f Himpl);
     do ? case lookup_field_in_type => //.
    - Admitted. (* Invalid case - all fields *)

  (* Not valid 
  Lemma inline_conforms_to_same_type schema t ϕ :
    [\/ is_object_type schema t, is_interface_type schema t | is_union_type schema t] ->
    queries_conform schema t ϕ ->
    query_conforms schema t (InlineFragment t ϕ).
  Proof.
    move=> Hty Hqsc /=; apply/and3P; split=> //.
    by apply/or3P.
    case: Hty => [Hobj | Hintf | Hunion]; rewrite /is_fragment_spread_possible;
    [rewrite (get_possible_types_objectE Hobj) | rewrite (get_possible_types_interfaceE Hintf)|  ]. apply: fset1I_N_fset0.
      by apply: eq_spreads.
  Qed. *)

  

  Lemma inline_preserves_conformance schema type_in_scope ϕ :
    query_conforms schema type_in_scope ϕ ->
    query_conforms schema type_in_scope (InlineFragment type_in_scope [:: ϕ]).
  Proof.
    rewrite {2}/query_conforms.
    move=> Hqc.
    apply/and4P; split=> //.
    apply/or3P. apply: (type_in_scope_N_scalar_enum Hqc).
    rewrite /is_fragment_spread_possible; simp get_possible_types.
    
    move: (type_in_scope_N_scalar_enum Hqc) => [Hobj | Hint | Hunion].
    funelim (is_object_type schema type_in_scope) => //.
    Admitted.
 

  


  Lemma nested_conforms_list schema ty n α ϕ :
    query_conforms schema ty (NestedField n α ϕ) -> ϕ != [::].
  Proof.
    rewrite /query_conforms.
    case lookup_field_in_type => // f.
      by move/and4P=> [_ _ Hne _].
  Qed.

   Lemma inline_subqueries_conform schema ty t ϕ :
    query_conforms schema ty (InlineFragment t ϕ) ->
    queries_conform schema t ϕ.
  Proof.
    rewrite /query_conforms.
    move/and4P=> [_ _ Hne H].
    by rewrite /queries_conform; apply/andP. 
  Qed.

  
  
 
End QueryConformance.
