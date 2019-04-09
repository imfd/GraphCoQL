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

Require Import SeqExtra.

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


  Lemma wf_inline_with_valid_fragments_is_same_or_subtype schema ty t φ :
    query_conforms schema ty (InlineFragment t φ) ->
    has_valid_fragments schema ty (InlineFragment t φ) ->
    t = ty \/ t \in get_possible_types schema ty.
  Proof.
    rewrite /query_conforms => /and4P [Hty Hspread _ _].
    simp has_valid_fragments; case Hscope : is_object_type => //= /andP.
    - by case=> /eqP Heq _; left.
    - move=> [/orP [/eqP Heq | /get_possible_types_objectE Ht] _]; [by left | right].
      move: Hspread; rewrite /is_fragment_spread_possible.
      rewrite Ht.
      apply: seq1I_N_nil.
  Qed.
      
End ValidFragments.