From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From extructures Require Import ord fset.

From Equations Require Import Equations.

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
  Implicit Type query : @Query Name Vals.


  Equations has_valid_fragments schema (type_in_scope : @NamedType Name) query : bool :=
    {
      has_valid_fragments schema ty (NestedField f _ φ)
        with lookup_field_in_type schema ty f :=
        {
        | Some fld := all (has_valid_fragments schema fld.(return_type)) φ;
        | _ := false
        };
      has_valid_fragments schema ty (NestedLabeledField _ f _ φ)
        with lookup_field_in_type schema ty f :=
        {
        | Some fld := all (has_valid_fragments schema fld.(return_type)) φ;
        | _ := false
        };

      has_valid_fragments schema ty (InlineFragment t φ)
        with is_object_type schema ty :=
        {
        | true := (t == ty) && all (has_valid_fragments schema ty) φ;
        | false := ((t == ty) || is_object_type schema t) && all (has_valid_fragments schema t) φ
        }; 
      
      has_valid_fragments _ _ _ := true
    }.


  Lemma valid_fragments_inline_obj schema ty t φ :
    is_object_type schema ty ->
    has_valid_fragments schema ty (InlineFragment t φ) ->
    t = ty.
  Proof.
    move=> Hobj.
    simp has_valid_fragments.
    by rewrite Hobj /= => /andP [/eqP].
  Qed.
  

  
End ValidFragments.