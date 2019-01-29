From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


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

  Definition argumentConforms schema (α : {fmap Name -> Vals}) (arg : FieldArgumentDefinition) : bool :=
    match arg with
    | (FieldArgument argname ty) => match (α argname) with
                                   | Some value => schema.(hasType) ty value
                                   | _ => false
                                   end
    end.
  

  Definition argumentsConform schema (α : {fmap Name -> Vals}) (args : seq.seq FieldArgumentDefinition) : bool :=
    all (argumentConforms schema α) args.
     

  
  Fixpoint query_conforms schema ty query :=
    match query with
    | SingleField fname α => match lookup_field_in_type schema ty fname with
                            | Some fld => if is_scalar_type fld.(return_type) || is_enum_type fld.(return_type) then
                                           α = emptym
                                         else
                                           argumentsConform schema α fld.(args)
                            | _ => false
                            end
    | LabeledField _ fname α =>  match lookup_field_in_type schema ty fname with
                                | Some fld => argumentsConform schema α fld.(args)
                                | _ => false
                                end
    | NestedField fname α ϕ =>
      ~~(nilp ϕ) &&  
        match lookup_field_in_type schema ty fname with
        | Some fld => argumentsConform schema α fld.(args) && all (query_conforms schema fld.(return_type)) ϕ
        | _ => false
        end
      
    | NestedLabeledField _ fname α ϕ =>
      ~~(nilp ϕ) &&
        match lookup_field_in_type schema ty fname with
        | Some fld => argumentsConform schema α fld.(args) && all (query_conforms schema fld.(return_type)) ϕ
        | _ => false
        end
        
    | InlineFragment t ϕ =>
      ~~(nilp ϕ) &&
        if is_object_type schema t then
          if [|| (t == ty), (t \in implementation schema ty) | (t \in union_members schema ty)] then
            all (query_conforms schema t) ϕ
          else
            false
        else
        if is_interface_type schema t then
          if (t == ty) || (ty \in implementation schema t) then
            all (query_conforms schema t) ϕ
          else
            false
        else
        if is_union_type schema t then
          if (t == ty) || (ty \in union_members schema t) then
            all (query_conforms schema t) ϕ
          else
            false
        else
          false
    end.

  Definition queries_conform schema ty queries := (queries != [::]) && (all (query_conforms schema ty) queries).

  Lemma nested_field_obj_int_union schema ty n α ϕ :
    query_conforms schema ty (NestedField n α ϕ) ->
    is_object_type schema n \/ is_interface_type schema n \/ is_union_type schema n.
  Proof.
    rewrite /query_conforms.
    move/andP=> [/nilP HNnil].
    case Hlook : lookup_field_in_type => [sm|] //.
    move/andP=> [_].
    rewrite -/(query_conforms schema sm).
 
End QueryConformance.
