From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

From extructures Require Import ord fmap.

Require Import Schema.
Require Import SchemaAux.
Require Import Query.
Require Import SchemaWellFormedness.
Require Import NRGTNF.


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
      if is_object_type schema t then
        if [|| (t == ty), (t \in implementation schema ty) | (t \in union_members schema ty)] then
          (ϕ != [::]) && all (query_conforms schema t) ϕ
        else
          false
      else
      if is_interface_type schema t then
        if (t == ty) || (ty \in implementation schema t) then
          (ϕ != [::]) && all (query_conforms schema t) ϕ
        else
          false
      else
      if is_union_type schema t then
        if (t == ty) || (ty \in union_members schema t) then
          (ϕ != [::]) && all (query_conforms schema t) ϕ
        else
          false
      else
        false
    end.

  Definition queries_conform schema ty queries := (queries != [::]) && (all (query_conforms schema ty) queries).

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
  
 
    
  Lemma nested_field_obj_int_union schema ty n α ϕ :
    query_conforms schema ty (NestedField n α ϕ) ->
    is_object_type schema n \/ is_interface_type schema n \/ is_union_type schema n.
  Proof.
  Admitted.

  Definition is_inline_fragment := @is_inline_fragment Name Vals.

  Lemma union_type_lookup_union schema ty:
    is_union_type schema ty ->
    exists u mbs, lookup_type schema ty = Some (UnionTypeDefinition u mbs).
  Proof.
    rewrite /is_union_type.
    case Hlook: lookup_type => [tdef|] //.
    case: tdef Hlook => // u mbs. exists u. exists mbs. done.
  Qed.
    
  Lemma nf_union_subqueries_inlines schema ty f α ϕ :
    is_union_type schema f ->
    query_conforms schema ty (NestedField f α ϕ) ->
    all is_inline_fragment ϕ.
  Proof.
    move=> Hunion; move: (union_type_lookup_union Hunion).
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
      case: ifP => //.
      case: ifP => //.
      move/or3P=> [/eqP -> | Himpl | Hunion].
        by move=> Hobj _; constructor 1.
        move: (has_implementation_is_interface Himpl) => Hint _ _.
        by constructor 2.
        move: (has_members_is_union Hunion).
        by constructor 3.
      case: ifP => //.
      case: ifP => //.
      move/orP=> [/eqP -> | Himpl].
        by move=> Hint _ _; constructor 2.
        move: (in_implementation_is_object Himpl) => Hobj _ _ _.
        by constructor 1.
      case: ifP => //.
      case: ifP => /orP. move=> [/eqP -> | Hunion].
        by move=> Hunion _ _ _; constructor 3.
        rewrite -/query_conforms.
        inversion schema.
        move: (in_union_is_object Hunion) => Hobj _ _ _ _.
          by constructor 1.
          done.
  Qed.
      
End QueryConformance.
