(* begin hide *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From Equations Require Import Equations.

Require Import String.
Require Import QString.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaAuxLemmas.
Require Import SchemaWellFormedness.
Require Import SchemaWFLemmas.

Require Import Query.
Require Import QueryAux.
Require Import QueryAuxLemmas.
Require Import QueryConformance.


Require Import QueryNormalForm.
Require Import QueryNormalFormLemmas.

Require Import Ssromega.

Require Import SeqExtra.

Require Import QueryTactics.
Require Import GeneralTactics.

(* end hide *)

(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">Query Normalisation</h1>
        <p class="lead">
         This file contains lemmas and theory about the normalisation of queries.
        </p>         
        <p>
        In particular, we prove here that the normalisation procedures actually do
        what they are supposed to do.
        </p>
  </div>
</div>#
 *)

Section Theory.
  
 
  Transparent qresponse_name.

    
  Variables (Vals : eqType).
  
  Variable (s : @wfGraphQLSchema Vals).

  (** ---- *)
  (**
     This lemma states that the order of filtering queries by response name 
     and normalizing does not affect the result.
   *)
  Lemma filter_normalize_swap rname ty φ :
    filter_queries_with_label rname (normalize s ty φ) = normalize s ty (filter_queries_with_label rname φ).
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n φ rname => /= [| n IH] φ rname ; first by rewrite leqn0 => /queries_size_0_nil ->.
    case: φ => //= q φ.
    case_query q => /=; simp query_size => Hleq; simp normalize.
    - lookup => //=; simp filter_queries_with_label; case: eqP => /= [/= Heq | Hneq].
      * by rewrite Heq -IH // filter_filter_absorb.
      * simp normalize; rewrite Hlook /= IH //; [by rewrite filter_swap | by leq_queries_size].
      * by apply: IH.
      * by simp normalize; rewrite Hlook /=; apply: IH.
    - lookup => //=; simp filter_queries_with_label; case: eqP => /= Heq.
      * by rewrite Heq -IH // filter_filter_absorb.
      * simp normalize; rewrite Hlook /= IH //; [by rewrite filter_swap | by leq_queries_size].
      * by apply: IH.
      * by simp normalize; rewrite Hlook /=; apply: IH.

    - lookup => //=; simp filter_queries_with_label; case: eqP => /= Heq; do ? by apply: IH; leq_queries_size.
      * case Hscope : is_object_type => //=; simp filter_queries_with_label => //=; case: eqP => //= _;
                                                                                                by rewrite Heq -IH // ?filter_filter_absorb; leq_queries_size.

      * case Hscope : is_object_type => //=; simp filter_queries_with_label => //=; case: eqP => //= _;
                                                                                                simp normalize; rewrite Hlook /= Hscope /= find_filter_swap; do ? by apply/eqP.
        all: do ? [rewrite IH ?filter_filter_absorb; leq_queries_size; by rewrite filter_swap].

      * by simp normalize; rewrite Hlook /=; apply: IH; leq_queries_size.

    - lookup => //=; simp filter_queries_with_label; case: eqP => /= Heq; do ? by apply: IH; leq_queries_size.
      * case Hscope : is_object_type => //=; simp filter_queries_with_label => //=; case: eqP => //= _;
                                                                                                by rewrite Heq -IH // ?filter_filter_absorb; leq_queries_size.

      * case Hscope : is_object_type => //=; simp filter_queries_with_label => //=; case: eqP => //= _;
                                                                                                simp normalize; rewrite Hlook /= Hscope /= find_filter_swap; do ? by apply/eqP.
        all: do ? [rewrite IH ?filter_filter_absorb; leq_queries_size; by rewrite filter_swap].

      * by simp normalize; rewrite Hlook /=; apply: IH; leq_queries_size.

    - case Hfapplies : does_fragment_type_apply => //=; simp filter_queries_with_label.
      * by simp normalize; rewrite Hfapplies /= -filter_queries_with_label_cat; apply: IH; leq_queries_size.
      * by simp normalize; rewrite Hfapplies /=; apply: IH; leq_queries_size.
  Qed.

  (** * Groundness *)
  (** ---- *)
  (**
     This lemma states that the result of [normalize] are 
     in ground form v2.0, whenever the type used to normalize is
     an Object type.
   *)
  Lemma normalize_are_grounded2 ty φ :
    is_object_type s ty ->
    are_grounded2 s ty (normalize s ty φ).
  Proof.
    apply_funelim (normalize s ty φ) => //=; clear ty φ.
    - by move=> ty f fld α φ IH Hlook Hscope; rewrite Hscope /=; apply_and3P; apply: IH.

    - by move=> ty f fld l α φ IH Hlook Hscope; rewrite Hscope /= ; apply_and3P; apply: IH.

    - move=> ty f fld α β φ IHsub IH Hrty Hlook Hscope; rewrite Hscope /=; apply_and3P; last by apply: IH.
        by simp is_grounded2; rewrite Hlook /=; apply: IHsub.

    - move=> fld ty f α β φ IHsub IH Hrty Hlook Hscope; rewrite Hscope /=; apply_and3P; last by apply: IH.
      simp is_grounded2; rewrite Hlook /=.
      have := (@in_possible_types_is_object Vals s fld.(return_type)).
      elim: get_possible_types => //= t ptys IHptys Hinobj.
      rewrite Hrty /=; apply_and3P.
      simp is_grounded2; apply_andP.
        by apply: Hinobj; apply: mem_head.
          by apply: IHsub; apply: Hinobj; apply: mem_head.
            by apply: IHptys => t' Hin'; apply: Hinobj; apply: mem_tail.     
            
    - move=> fld ty f l α β φ IHsub IH Hrty Hlook Hscope; rewrite Hscope /=; apply_and3P; last by apply: IH.
        by simp is_grounded2; rewrite Hlook /=; apply: IHsub.

    - move=> fld ty f l α β φ IHsub IH Hrty Hlook Hscope; rewrite Hscope /=; apply_and3P; last by apply: IH.
      simp is_grounded2; rewrite Hlook /=.
      have := (@in_possible_types_is_object Vals s fld.(return_type)).
      elim: get_possible_types => //= t ptys IHptys Hinobj.
      rewrite Hrty /=; apply_and3P.
      simp is_grounded2; apply_andP.
        by apply: Hinobj; apply: mem_head.
          by apply: IHsub; apply: Hinobj; apply: mem_head.
            by apply: IHptys => t' Hin'; apply: Hinobj; apply: mem_tail.     
  Qed.


  (**
     This corollary states that the result of [normalize] are grounded.
   *)
  Corollary normalize_are_grounded ty φ : is_object_type s ty -> are_grounded s (normalize s ty φ).
  Proof.
      by intros; apply: are_grounded2_are_grounded; apply: normalize_are_grounded2.
  Qed.


  (**
     This lemma states that the result of [normalize_queries] are 
     in ground form v2.0, regardless of the type used to normalize.
   *)
  Lemma normalize_queries_are_grounded2 ty φ :
    are_grounded2 s ty (normalize_queries s ty φ).
  Proof.
    apply_funelim (normalize_queries s ty φ) => /=; clear ty φ.
    - by move=> ty φ Hscope; apply: normalize_are_grounded2.
    - move=> ty φ Hscope.
      have := (@in_possible_types_is_object Vals s ty).
      elim: get_possible_types => //= t ptys IH Hinobj.
      rewrite Hscope /=; apply_and3P.
      * simp is_grounded2; apply_andP; [| apply: normalize_are_grounded2]; by apply: Hinobj; apply: mem_head.
      * by apply: IH => t' Hin; apply: Hinobj; apply: mem_tail.
  Qed.




  (** * Non-redundancy *)
  (** ---- *)
  (**
     This lemma states that the result of [normalize] are
     non-redundant, whenever the type used to normalize 
     is an Object type.
   *)
  Lemma normalize_are_non_redundant ty φ :
    is_object_type s ty ->
    are_non_redundant (normalize s ty φ).
  Proof.
    apply_funelim (normalize s ty φ) => //=.

    all: do ? [by intros; non_red; apply_and3P; [ by rewrite -filter_normalize_swap /= find_fields_filter_nil | by apply: H] ].
    all: do ? [by intros; non_red; apply_and3P => /=; [ by rewrite -filter_normalize_swap /= find_fields_filter_nil | by apply: H | by apply: H0] ].

    all: do [intros; non_red; apply_and3P => /=; [ by rewrite -filter_normalize_swap /= find_fields_filter_nil | | by apply: H0] ].
    all: do [have  := (@in_possible_types_is_object Vals s f.(return_type))].
    all: do [have  := (uniq_get_possible_types s f.(return_type))].
    all: do [elim: get_possible_types => //= t ptys IH /andP [Hnin Huniq] Hinobj].
    all: do [non_red; apply_and3P => /=; last by apply: IH => //= t' Hin'; apply: Hinobj; apply: mem_tail].
    all: do ? by apply/eqP; apply: find_fragment_inlined_nil_func.
    all: do [by apply: H; apply: Hinobj; apply: mem_head].
  Qed.

  (**
     This lemma states that the result of [normalize_queries] are
     non-redundant, regardless of the type used to normalize.
   *)
  Lemma normalize_queries_are_non_redundant ty φ :
    are_non_redundant (normalize_queries s ty φ).
  Proof.
    apply_funelim (normalize_queries s ty φ) => //=; clear ty φ; first by intros; apply: normalize_are_non_redundant.
    move=> ty φ Hscope.
    have  := (@in_possible_types_is_object Vals s ty).
    have  := (uniq_get_possible_types s ty).
    elim: get_possible_types => //= t ptys IH /andP [Hnin Huniq] Hinobj.
    simp are_non_redundant; apply_and3P => /=; last by apply: IH => //= t' Hin'; apply: Hinobj; apply: mem_tail.
      by apply/eqP; apply: find_fragment_inlined_nil_func.
      by apply: normalize_are_non_redundant; apply: Hinobj; apply: mem_head.
  Qed.


 

  (**
     This lemma states that if a query conforms to the Query type, then 
     normalizing results in a query in normal form.
   *)
  (* Conformance is not really needed... *)
  Lemma normalize_root_query_is_in_normal_form φ :
    queries_conform s s.(query_type) φ ->
    are_non_redundant (normalize s s.(query_type) φ) /\
    are_grounded s (normalize s s.(query_type) φ).
  Proof.
    intros; split.
    - by apply: normalize_are_non_redundant; apply: query_has_object_type.
    - apply: are_grounded2_are_grounded.
        by apply: normalize_are_grounded2; apply: query_has_object_type.
  Qed.

End Theory.

