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

  Definition argument_conforms schema (args : seq FieldArgumentDefinition) (arg : Name * Vals) : bool :=
    let: (argname, value) := arg in
    has (fun argdef => let: FieldArgument name ty := argdef in
                    (name == argname) && schema.(hasType) ty value) args.
  

  Definition arguments_conform schema (args : seq.seq FieldArgumentDefinition) (α : {fmap Name -> Vals}) : bool :=
    all (argument_conforms schema args) α.
     

  Definition is_fragment_spread_possible schema parent_type ty : bool :=
    let ty_possible_types := get_possible_types schema ty in
    let parent_possible_types := get_possible_types schema parent_type in
    let applicable_types := (ty_possible_types :&: parent_possible_types)%fset in
    applicable_types != fset0.

  Lemma object_spreads_E schema parent_type ty :
    is_object_type schema ty ->
    is_fragment_spread_possible schema parent_type ty ->
    [\/ ty = parent_type,
     ty \in implementation schema parent_type |
     ty \in union_members schema parent_type].
  Proof.
    move/is_object_type_E=> [obj [intfs [flds Hlook]]].
    rewrite /is_fragment_spread_possible.
    rewrite {1}/get_possible_types Hlook fset1I.
    case: ifP => //.
      by move/in_possible_types_E.
  Qed.

  Lemma eq_spreads schema ty :
    [\/ is_object_type schema ty, is_interface_type schema ty | is_union_type schema ty] ->
    is_fragment_spread_possible schema ty ty.
  Proof.
    case.
    move/is_object_type_E=> [obj [intf [flds Hlook]]].
    rewrite /is_fragment_spread_possible /get_possible_types Hlook.
    rewrite fset1I /= inE.
    case: ifP=> //. case: eqP => //.
  Admitted.

  
  Fixpoint query_conforms schema ty query :=
    match query with
    | SingleField fname α => match lookup_field_in_type schema ty fname with
                            | Some fld =>
                              if is_scalar_type schema fld.(return_type) || is_enum_type schema fld.(return_type) then
                                arguments_conform schema fld.(args) α
                              else
                                false
                            | _ => false
                            end
    | LabeledField _ fname α =>  match lookup_field_in_type schema ty fname with
                                | Some fld =>
                                   if is_scalar_type schema fld.(return_type) || is_enum_type schema fld.(return_type) then
                                     arguments_conform schema fld.(args) α
                                   else
                                     false
                                | _ => false
                                end
    | NestedField fname α ϕ =>
      match lookup_field_in_type schema ty fname with
      | Some fld => if is_scalar_type schema fld.(return_type) || is_enum_type schema fld.(return_type) then
                     false
                   else
                     [&& ϕ != [::],
                      arguments_conform schema fld.(args) α &
                      all (query_conforms schema fld.(return_type)) ϕ]
      | _ => false
      end
      
    | NestedLabeledField _ fname α ϕ =>
        match lookup_field_in_type schema ty fname with
        | Some fld => if is_scalar_type schema fld.(return_type) || is_enum_type schema fld.(return_type) then
                       false
                     else
                       [&& ϕ != [::],
                        arguments_conform schema fld.(args) α &
                        all (query_conforms schema fld.(return_type)) ϕ]
        | _ => false
        end
        
    | InlineFragment t ϕ =>
      [&& [|| is_object_type schema t, is_interface_type schema t | is_union_type schema t],
       is_fragment_spread_possible schema ty t,
       ϕ != [::] &
       all (query_conforms schema t) ϕ]
    end.

  Definition queries_conform schema ty queries := (queries != [::]) && (all (query_conforms schema ty) queries).

  Lemma queries_conformE schema ty queries :
    queries_conform schema ty queries ->
    queries != [::] /\ all (query_conforms schema ty) queries.
  Proof. by rewrite /queries_conform; move/andP. Qed.
  
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
    by move=> o intfs flds Hlook _ _ _; constructor; rewrite /is_object_type Hlook.
    by move=> i flds Hlook _ _; constructor; rewrite /is_interface_type Hlook.
    by move=> u mbs Hlook _ _; constructor; rewrite /is_union_type Hlook.
  Qed.


  Lemma fset1I_N_fset0 {A : ordType} (a b : A) :
    (fset1 a :&: fset1 b)%fset != fset0 -> a = b.
  Proof.
    rewrite fset1I.
    case: ifP => //.
    move/fset1P => //.
  Qed.

 
  Lemma object_spreads_in_object_scope schema type_in_scope t ϕ :
    is_object_type schema type_in_scope ->
    is_object_type schema t ->
    queries_conform schema t ϕ -> 
    query_conforms schema type_in_scope (InlineFragment t ϕ) <->
    t = type_in_scope.
  Proof.
    move=> Hobj'.
    pose H' := Hobj'.
    move/is_object_type_E: H' => [obj [intfs [flds H]]].
    move=> Hobj.
    move=> Hqsc.
    split.
    - rewrite /query_conforms.
      move/and4P=> [/or3P _ Hspread _ _].
      move: (object_spreads_E Hobj Hspread)=> [||] //.
        by rewrite /implementation H.
      by rewrite /union_members H.
    - move=> Heq; rewrite Heq /=.
      move: Hqsc; rewrite /queries_conform.
      move/andP=> [Hne Hall].
      apply/and4P; split=> //.
        by apply/or3P; constructor 1.
        by apply: eq_spreads; constructor 1.
      by rewrite Heq in Hall.
  Qed.

  Lemma interface_spreads_in_object_scope schema type_in_scope t ϕ :
    is_object_type schema type_in_scope ->
    is_interface_type schema t ->
    query_conforms schema type_in_scope (InlineFragment t ϕ) ->
    type_in_scope \in implementation schema t.
  Proof.
    funelim (is_object_type schema type_in_scope) => // _.
    funelim (is_interface_type schema0 t) => // _.
    rewrite /query_conforms.
    move/and4P=> [_ Hspread _ _].
    move: Hspread; rewrite /is_fragment_spread_possible /get_possible_types Heq Heq0.
    rewrite fsetIC fset1I.
    case: ifP => //.
      by rewrite /implementation Heq in_fset.
  Qed.

  Lemma union_spreads_in_object_scope schema type_in_scope t ϕ :
    is_object_type schema type_in_scope ->
    is_union_type schema t ->
    query_conforms schema type_in_scope (InlineFragment t ϕ) ->
    type_in_scope \in union_members schema t.
  Proof.
    funelim (is_object_type schema type_in_scope) => // _.
    funelim (is_union_type schema0 t) => // _.
    rewrite /query_conforms.
    move/and4P=> [_ Hspread _ _].
    move: Hspread; rewrite /is_fragment_spread_possible /get_possible_types Heq Heq0.
    rewrite fsetIC fset1I.
    case: ifP => //.
    by rewrite /union_members Heq in_fset.
  Qed.

  Lemma abstract_spreads_in_object_scope schema type_in_scope t ϕ :
    is_object_type schema type_in_scope ->
    queries_conform schema t ϕ ->
    (is_interface_type schema t \/ is_union_type schema t) ->
    query_conforms schema type_in_scope (InlineFragment t ϕ) <->
    (type_in_scope \in implementation schema t \/ type_in_scope \in union_members schema t).
  Proof.
    move=> Hobj Hqsc Htype.
    split.
    - case: Htype => [Hint | Hunion].
        by move/(interface_spreads_in_object_scope Hobj Hint); left.
      by move/(union_spreads_in_object_scope Hobj Hunion); right.
    - move: Hqsc; rewrite /queries_conform; move/andP=> [Hne Hall].
      move=> H.      
      rewrite /query_conforms; apply/and4P; split=> //.
      apply/or3P.
      by case: Htype; [constructor 2 | constructor 3].
      rewrite /is_fragment_spread_possible.
      Admitted.

      
  Lemma object_spreads_in_interface_scope schema type_in_scope t ϕ :
    is_object_type schema t ->
    is_interface_type schema type_in_scope ->
    queries_conform schema t ϕ ->
    query_conforms schema type_in_scope (InlineFragment t ϕ) <->
    t \in implementation schema type_in_scope.
  Proof.
  Admitted.



  
  Lemma nested_field_obj_int_union schema ty n α ϕ :
    query_conforms schema ty (NestedField n α ϕ) ->
    is_object_type schema n \/ is_interface_type schema n \/ is_union_type schema n.
  Proof.
  Admitted.

  Definition is_inline_fragment := @is_inline_fragment Name Vals.


    
  Lemma nf_union_subqueries_inlines schema ty f α ϕ :
    is_union_type schema f ->
    query_conforms schema ty (NestedField f α ϕ) ->
    all is_inline_fragment ϕ.
  Proof.
    rewrite is_union_type_E.
    case=> u; case=> mbs Hlook.
    rewrite /query_conforms.
    case Hlookf : lookup_field_in_type => [fld|] //.
  Abort.

  Lemma lookup_field_object_or_interface schema ty fname fld :
    lookup_field_in_type schema ty fname = Some fld ->
    is_object_type schema ty \/ is_interface_type schema ty.
  Proof.
    rewrite /lookup_field_in_type /fields.
    case Hlook: lookup_type => [tdef|] //.
    case: tdef Hlook => // [o intfs flds | i flds] Hlook _.
    by left; rewrite /is_object_type Hlook.
    by right; rewrite /is_interface_type Hlook.
  Qed.

  Lemma has_implementation_is_interface schema ty ty' :
    ty' \in implementation schema ty ->
            is_interface_type schema ty.
  Proof.
    rewrite /implementation.
    case Hlook: lookup_type => [tdef|] //.
    case: tdef Hlook => // i flds Hlook _.
      by rewrite /is_interface_type Hlook.
  Qed.

  Lemma in_implementation_is_object schema ty :
    forall ty', ty' \in implementation schema ty ->
                   is_object_type schema ty'.
    Admitted.

  Lemma has_members_is_union schema ty ty' :
    ty' \in union_members schema ty ->
            is_union_type schema ty.
  Proof.
    rewrite /union_members.
    case Hlook: lookup_type => [tdef|] //.
    case: tdef Hlook => // i flds Hlook _.
      by rewrite /is_union_type Hlook.
  Qed.

  Lemma in_union_is_object schema ty :
    forall ty',
      ty' \in union_members schema ty ->
              is_object_type schema ty'.
  Proof.
    Admitted.
            
    
  Lemma type_in_scope_N_scalar_enum schema type_in_scope ϕ :
    query_conforms schema type_in_scope ϕ ->
    [\/ is_object_type schema type_in_scope,
     is_interface_type schema type_in_scope |
     is_union_type schema type_in_scope].
  Proof.
    case: ϕ.
    - move=> f α.
      rewrite /query_conforms.
      case Hlook: lookup_field_in_type => [fld|] // _.
      move: (lookup_field_object_or_interface Hlook) => [Hobj | Hint].
        by constructor 1.
        by constructor 2.
    - move=> l f α.
      rewrite /query_conforms.
      case Hlook: lookup_field_in_type => [fld|] // _.
      move: (lookup_field_object_or_interface Hlook) => [Hobj | Hint].
        by constructor 1.
        by constructor 2.
    - move=> f α ϕ.
      rewrite /query_conforms.
      case Hlook: lookup_field_in_type => [fld|] // _.
      move: (lookup_field_object_or_interface Hlook) => [Hobj | Hint].
        by constructor 1.
        by constructor 2.
    - move=> l f α ϕ.
      rewrite /query_conforms.
      case Hlook: lookup_field_in_type => [fld|] // _.
      move: (lookup_field_object_or_interface Hlook) => [Hobj | Hint].
        by constructor 1.
        by constructor 2.
    - move=> t ϕ.
      rewrite /query_conforms.
      move/and4P=> [/or3P Hty Hspread Hne _] => //.
      move: Hspread.
      rewrite /is_fragment_spread_possible.
      rewrite /get_possible_types fsetIC.
      case Hlook: lookup_type => [tdef|] //.
      case: tdef Hlook => //; do ?[rewrite fset0I //=].
      move=> obj intfs flds Hlook _.
      by constructor 1; rewrite /is_object_type Hlook /=.
      move=> i flds Hlook _.
        by constructor 2; rewrite /is_interface_type Hlook /=.
      move=> u mbs Hlook _.
        by constructor 3; rewrite /is_union_type Hlook /=.  
      by rewrite fset0I /=.
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
    apply: (type_in_scope_N_scalar_enum Hhd).
  Qed.

  
  Lemma nf_queries_conform schema ty fld n α ϕ :
    lookup_field_in_type schema ty n = Some fld ->
    query_conforms schema ty (NestedField n α ϕ) ->
    queries_conform schema fld.(return_type) ϕ.
  Proof.
    rewrite /query_conforms.
    move=> Hlook; rewrite Hlook.
    case: ifP => // _; rewrite -/(query_conforms schema fld.(return_type)).
    move/and3P=> [HNempty Hargs Hall].
    rewrite /queries_conform. 
    by apply/andP.  
  Qed.

  Lemma nf_conforms_lookup_some schema ty  n α ϕ :
    query_conforms schema ty (NestedField n α ϕ) ->
    exists fld, lookup_field_in_type schema ty n = Some fld.
  Proof. rewrite /query_conforms.
    case Hlook : lookup_field_in_type => [fld'|] //.
    by exists fld'.
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

  Lemma inline_conforms_to_same_type schema t ϕ :
    [\/ is_object_type schema t, is_interface_type schema t | is_union_type schema t] ->
    queries_conform schema t ϕ ->
    query_conforms schema t (InlineFragment t ϕ).
  Proof.
    move=> Hty Hqsc /=; apply/and3P; split=> //.
    by apply/or3P.
    by apply: eq_spreads.
  Qed.
  
End QueryConformance.
