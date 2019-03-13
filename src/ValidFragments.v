From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From extructures Require Import ord fset.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaWellFormedness.
Require Import Query.
Require Import QueryConformance.

Require Import Graph.
Require Import GraphAux.
Require Import GraphConformance.

Require Import NRGTNF.

Section ValidFragments.

  Variables N Name Vals : ordType.
  Implicit Type schema : @wfSchema Name Vals.

  Fixpoint has_valid_fragments schema graph (u : @node Name Vals) (type_in_scope : NamedType) query : bool :=
    match query with
    | SingleField f α
    | LabeledField _ f α => lookup_field_in_type schema u.(type) f
                                                                
    | NestedField f α φ
    | NestedLabeledField _ f α φ =>
      let target_nodes := neighbours_with_field graph u (Field f α) in
      match lookup_field_type schema u.(type) f with
      | Some (ListType return_type) =>
        all (fun v => all (has_valid_fragments schema graph v return_type) φ) target_nodes
          
      | Some (NT return_type) =>
        match ohead target_nodes with
        | Some v => all (has_valid_fragments schema graph v return_type) φ
        | _ =>  false
        end
      | _ => false         (* If the field ∉ fields(u) then it's null, right? *)
      end

    | InlineFragment t φ =>
      if is_union_type schema type_in_scope then
        (is_subtype schema (NT u.(type)) (NT t)) ==> all (has_valid_fragments schema graph u t) φ
      else
      if is_interface_type schema type_in_scope then
        is_subtype schema (NT u.(type)) (NT t) &&  
        all (has_valid_fragments schema graph u type_in_scope) φ                                        
      else
        is_subtype schema (NT u.(type)) (NT t) &&
        all (has_valid_fragments schema graph u type_in_scope) φ
    end.

  Ltac query_conforms := rewrite /query_conforms -/(query_conforms _ _); try move/and4P; try apply/and4P.

  Lemma valid_fragments_inline_guard_supertype_of_node schema graph u type_in_scope t φ :
    is_object_type schema type_in_scope ->
    has_valid_fragments schema graph u type_in_scope (InlineFragment t φ) ->
    is_subtype schema (NT u.(type)) (NT t).
  Proof.
    move=> Hobj.
    rewrite /has_valid_fragments.
    rewrite (is_object_ifunionF _ _ Hobj).
    by rewrite (is_object_ifinterfaceF _ _ Hobj) => /andP [H _].
  Qed.

  

  
End ValidFragments.