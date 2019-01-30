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
  
End QueryConformance.
