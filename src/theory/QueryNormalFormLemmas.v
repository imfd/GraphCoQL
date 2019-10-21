(* begin hide *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.

Require Import SeqExtra.
Require Import Ssromega.
Require Import GeneralTactics.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaLemmas.
Require Import SchemaWellFormedness.

Require Import Query.
Require Import QueryAux.
Require Import QueryAuxLemmas.
Require Import QueryTactics.
Require Import QueryConformance.


Require Import QueryNormalForm.


(* end hide *)


(**
   #<div class="jumbotron">
      <div class="container">
        <h1 class="display-4">Normal Form Proofs</h1>
        <p class="lead">
         This file contains proofs about normal form and the normalization procedure.
        </p>         
        <p>
        In particular, we prove here that the correctness of the normalzation procedure, 
        meaning that the resulting queries are in normal form. 
        </p>
  </div>
</div>#
 *)

(** * Normal Form 
    ----
    
    In this section we prove several lemmas about groundness and non-redundancy.
   *)
Section NormalForm.

  
  Variables (Scalar : eqType) (s : wfGraphQLSchema).


  (** ** Groundedness *)
  (** ---- *)
  
  (**
     This lemma states that
   *)
  (* Unused *)
  Lemma grounded_fields_are_grounded (σ : seq (@Selection Scalar)) :
    all (fun σ__i => σ__i.(is_field) && is_in_ground_typed_nf s σ__i) σ ->
    are_in_ground_typed_nf s σ.
  Proof.
    elim: σ => //= σ__i σ IH => /andP [/andP [Hf Hg] /allP Hgs].
    rewrite /are_in_ground_typed_nf; apply_andP => /=; [apply/orP; left|]; apply_andP.
    all: do [by apply/allP=> sel Hin; have /(_ sel Hin) := Hgs; case/andP].
  Qed.

  (** ---- **)
  (**
   This lemma states that
   *)
  Lemma grounded_fragments_are_grounded (σ : seq (@Selection Scalar)) :
    all (fun σ__i => σ__i.(is_inline_fragment) && is_in_ground_typed_nf s σ__i) σ ->
    are_in_ground_typed_nf s σ.
  Proof.
    elim: σ => //= σ__i σ IH => /andP [/andP [Hf Hg] /allP Hgs].
    rewrite /are_in_ground_typed_nf; apply_andP => /=; [apply/orP; right|]; apply_andP.
    all: do [by apply/allP=> sel Hin; have /(_ sel Hin) := Hgs; case/andP].
  Qed.

  
  
  (** ** Non-redundancy *)
  (** ---- *)
  Section NonRedundant.

    
    Implicit Type φ : seq (@Selection Scalar).

    
    Section Filter.

      Transparent qresponse_name.
           
      (**
         This lemma states that filtering preserves non-redundancy of the selections.
       *)
      Lemma filter_preserves_non_redundancy rname φ :
        are_non_redundant φ ->
        are_non_redundant (filter_queries_with_label rname φ).
      Proof.
        funelim (filter_queries_with_label rname φ) => //=; simp are_non_redundant; bcase; do ? by apply: H.
        all: do [apply_and3P].
        all: do ? by apply/eqP; apply: filter_preserves_find_frags_nil; apply/eqP.
        all: do ? by apply: H.
        all: do ? by apply: H0.
        all: do [by apply/eqP; apply: filter_preserves_find_fields_nil; apply/eqP].
      Qed.
        
    End Filter.

  End NonRedundant.
End NormalForm.

(** ---- *)
(**
   This tactic reduces some burdain on proofs with non-redundancy.
 *)
Ltac non_red :=
  repeat match goal with
         | [|- is_true (are_non_redundant (filter_queries_with_label _ _))] =>
             by apply: filter_preserves_non_redundancy
         | [|- context [are_non_redundant (_ :: _)] ] => simp are_non_redundant
         | [|- is_true (are_non_redundant (_ :: _)) -> _] => simp are_non_redundant
         | [|- is_true (are_non_redundant _)] => simp are_non_redundant
         end.


(** * Normalization 
    ----
    In this section we prove that the normalization procedure returns queries in normal form.
 *)
Section Normalization.

  Transparent qresponse_name.
  
  Variables (Scalar : eqType) (s : wfGraphQLSchema).

  (**
     This lemma states that the order of filtering selections by response name 
     and normalizing does not affect the result.
   *)
  Lemma filter_normalize_swap rname ty (φ : seq (@Selection Scalar)) :
    filter_queries_with_label rname (normalize_selections s ty φ) = normalize_selections s ty (filter_queries_with_label rname φ).
  Proof.
    move: {2}(selections_size _) (leqnn (selections_size φ)) => n.
    elim: n φ rname => /= [| n IH] φ rname ; first by rewrite leqn0 => /selections_size_0_nil ->.
    case: φ => //= q φ.
    case_selection q => /=; simp selection_size => Hleq; simp normalize_selections.
    - lookup => //=; simp filter_queries_with_label; case: eqP => /= [/= Heq | Hneq].
      * by rewrite Heq -IH // filter_filter_absorb.
      * simp normalize_selections; rewrite Hlook /= IH //; [by rewrite filter_swap | by leq_selections_size].
      * by apply: IH.
      * by simp normalize_selections; rewrite Hlook /=; apply: IH.
    - lookup => //=; simp filter_queries_with_label; case: eqP => /= Heq.
      * by rewrite Heq -IH // filter_filter_absorb.
      * simp normalize_selections; rewrite Hlook /= IH //; [by rewrite filter_swap | by leq_selections_size].
      * by apply: IH.
      * by simp normalize_selections; rewrite Hlook /=; apply: IH.

    - lookup => //=; simp filter_queries_with_label; case: eqP => /= Heq; do ? by apply: IH; leq_selections_size.
      * case Hscope : is_object_type => //=; simp filter_queries_with_label => //=; case: eqP => //= _;
                                                                                                by rewrite Heq -IH // ?filter_filter_absorb; leq_selections_size.

      * case Hscope : is_object_type => //=; simp filter_queries_with_label => //=; case: eqP => //= _;
                                                                                                simp normalize_selections; rewrite Hlook /= Hscope /= find_filter_swap; do ? by apply/eqP.
        all: do ? [rewrite IH ?filter_filter_absorb; leq_selections_size; by rewrite filter_swap].

      * by simp normalize_selections; rewrite Hlook /=; apply: IH; leq_selections_size.

    - lookup => //=; simp filter_queries_with_label; case: eqP => /= Heq; do ? by apply: IH; leq_selections_size.
      * case Hscope : is_object_type => //=; simp filter_queries_with_label => //=; case: eqP => //= _;
                                                                                                by rewrite Heq -IH // ?filter_filter_absorb; leq_selections_size.

      * case Hscope : is_object_type => //=; simp filter_queries_with_label => //=; case: eqP => //= _;
                                                                                                simp normalize_selections; rewrite Hlook /= Hscope /= find_filter_swap; do ? by apply/eqP.
        all: do ? [rewrite IH ?filter_filter_absorb; leq_selections_size; by rewrite filter_swap].

      * by simp normalize_selections; rewrite Hlook /=; apply: IH; leq_selections_size.

    - case Hfapplies : does_fragment_type_apply => //=; simp filter_queries_with_label.
      * by simp normalize_selections; rewrite Hfapplies /= -filter_queries_with_label_cat; apply: IH; leq_selections_size.
      * by simp normalize_selections; rewrite Hfapplies /=; apply: IH; leq_selections_size.
  Qed.

  (** ** Groundedness *)
  (** ---- *)

  (**
     This lemma states that [normalize_selections] returns fields.
   *)
  Lemma normalized_selections_are_fields ts ss :
    all (@is_field Scalar) (normalize_selections s ts ss).
  Proof.
      by funelim (normalize_selections s ts ss).
  Qed.

  (** ---- *)
  (**
     This lemma states that [normalize_selections] returns selections 
     in ground-typed normal form.
   *)
  Lemma normalized_selections_are_in_gt_nf ts (ss : seq (@Selection Scalar)) :
    all (is_in_ground_typed_nf s) (normalize_selections s ts ss).
  Proof.
    funelim (normalize_selections s ts ss) => //=.
    - apply_andP; first apply_andP;
        by [ apply/orP; left; apply: normalized_selections_are_fields
           | apply: H
           | apply: H0
           ].
    - apply_andP; first apply_andP.
      * apply/orP; right; by elim: get_possible_types.
      * have := (@in_possible_types_is_object s f.(ftype)).
        generalize (get_possible_types s f.(ftype)).
        elim=> //= t ptys IHptys Hinobj.
        have Htobj := (Hinobj t (mem_head _ _)).
        rewrite Htobj andTb.
        apply_andP.
        apply/allP=> sel Hin; apply_andP.
          by move/allP: (normalized_selections_are_fields
                           t
                 (subselections ++
                             merge_selection_sets (find_queries_with_label s name1 type_in_scope l))) => /(_ sel Hin).
        
        by move/allP: (H t) => /(_ sel Hin).
        by apply: IHptys; intros; apply: Hinobj; apply: mem_tail.

     
    - apply_andP; first apply_andP;
        by [ apply/orP; left; apply: normalized_selections_are_fields
           | apply: H
           | apply: H0
           ].
    - apply_andP; first apply_andP.
      * apply/orP; right; by elim: get_possible_types.
      * have := (@in_possible_types_is_object s f.(ftype)).
        generalize (get_possible_types s f.(ftype)).
        elim=> //= t ptys IHptys Hinobj.
        have Htobj := (Hinobj t (mem_head _ _)).
        rewrite Htobj andTb.
        apply_andP.
        apply/allP=> sel Hin; apply_andP.
        by move/allP: (normalized_selections_are_fields t
                 (subselections0 ++
                              merge_selection_sets (find_queries_with_label s alias0 type_in_scope l))) => /(_ sel Hin).
        by move/allP: (H t) => /(_ sel Hin).
        by apply: IHptys; intros; apply: Hinobj; apply: mem_tail.
  Qed.

  (** ---- *)
  (**
     This corollary is just the conjunction that the normalized selections are 
     both fields and in ground-typed normal form.
   *)
  Corollary normalized_selections_are_grounded ts (ss : seq (@Selection Scalar)) :
    are_in_ground_typed_nf s (normalize_selections s ts ss).
  Proof.
    rewrite /are_in_ground_typed_nf.
    apply_andP.
    - by apply/orP; left; apply: normalized_selections_are_fields.
    - by apply: normalized_selections_are_in_gt_nf.
  Qed. 

  
  (** ** Non-redundancy *)
  (** ---- *)
  (**
     This lemma states that the result of [normalize_selections] are
     non-redundant.
   *)
  Lemma normalized_selections_are_non_redundant ty (φ : seq (@Selection Scalar)) :
    are_non_redundant (normalize_selections s ty φ).
  Proof.
    apply_funelim (normalize_selections s ty φ) => //=.


    all: do ? [by intros; non_red; apply_and3P; by rewrite -filter_normalize_swap /= find_fields_filter_nil].
    
    all: do [intros; non_red; apply_and3P => /=; [ by rewrite -filter_normalize_swap /= find_fields_filter_nil |] ].
    all: do [have  := (@in_possible_types_is_object s f.(ftype))].
    all: do [have  := (uniq_get_possible_types s f.(ftype))].
    all: do [elim: get_possible_types => //= t ptys IH /andP [Hnin Huniq] Hinobj].
    all: do [non_red; apply_and3P => /=; last by apply: IH => //= t' Hin'; apply: Hinobj; apply: mem_tail].
    all: do ? by apply/eqP; apply: find_fragment_inlined_nil_func.
  Qed.



  (** ---- **)
  (**
     This lemma states that normalized selections are in normal form.
   *)
  Lemma normalized_selections_are_in_nf ts (σs : seq (@Selection Scalar)) :
    are_in_normal_form s (normalize_selections s ts σs).
  Proof.
    rewrite /are_in_normal_form; apply_andP; [ by apply: normalized_selections_are_grounded
                                             | by apply: normalized_selections_are_non_redundant
                                             ].
  Qed.
    
      
    
  (** ---- *)
  (**
     This theorem states that [normalize] returns a query in normal form, thus proving 
     its correctness.
   *)
  Theorem normalized_query_is_in_nf (q : @query Scalar) :
    is_in_normal_form s (normalize s q).
  Proof.
    by case: q; intros; rewrite /is_in_normal_form /normalize /=; apply: normalized_selections_are_in_nf.
  Qed.

   
  

End Normalization.

(** ---- *)
(** 
    #<div>
        <a href='GraphCoQL.QueryNormalForm.html' class="btn btn-light" role='button'> Previous ← Query Normal Form  </a>
        <a href='GraphCoQL.QuerySemantics.html' class="btn btn-info" role='button'>Continue Reading → Query Semantics</a>
    </div>#
*)