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
        <h1 class="display-4">Normal Form Theory</h1>
        <p class="lead">
         This file contains lemmas and theory about non-redundancy, groundness and the normalisation procedure.
        </p>         
        <p>
        In particular, we prove here that the normalisation procedures actually do
        what they are supposed to do.
        </p>
  </div>
</div>#
 *)

Section NormalForm.

  (** * Normal Form 

      In this section we prove several lemmas about groundness and non-redundancy.
   *)

  Variables (Vals : eqType).


  
  (** ** Non-redundancy *)
  (** ---- *)
  Section NonRedundant.

    
    Implicit Type φ : seq (@Selection Vals).

    
    Section Filter.

      Transparent qresponse_name.
           

      (**
         This lemma states that filtering according to a response name preserves non-redundancy
         of the queries.
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

Ltac non_red :=
  repeat match goal with
         | [|- is_true (are_non_redundant (filter_queries_with_label _ _))] =>
             by apply: filter_preserves_non_redundancy
         | [|- context [are_non_redundant (_ :: _)] ] => simp are_non_redundant
         | [|- is_true (are_non_redundant (_ :: _)) -> _] => simp are_non_redundant
         | [|- is_true (are_non_redundant _)] => simp are_non_redundant
         end.
(** ---- *)


(** * Normalisation 

    In this section we prove things related to the normalisation procedure.
    
    In particular, we prove that it does what it is supposed to do
 *)
(** ---- *)
Section Normalisation.

  
  Transparent qresponse_name.
  
  Variables (Vals : eqType) (s : @wfGraphQLSchema Vals).

  (** ---- *)
  (**
     This lemma states that the order of filtering queries by response name 
     and normalizing does not affect the result.
   *)
  Lemma filter_normalize_swap rname ty φ :
    filter_queries_with_label rname (normalize_selections s ty φ) = normalize_selections s ty (filter_queries_with_label rname φ).
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n φ rname => /= [| n IH] φ rname ; first by rewrite leqn0 => /queries_size_0_nil ->.
    case: φ => //= q φ.
    case_selection q => /=; simp selection_size => Hleq; simp normalize_selections.
    - lookup => //=; simp filter_queries_with_label; case: eqP => /= [/= Heq | Hneq].
      * by rewrite Heq -IH // filter_filter_absorb.
      * simp normalize_selections; rewrite Hlook /= IH //; [by rewrite filter_swap | by leq_queries_size].
      * by apply: IH.
      * by simp normalize_selections; rewrite Hlook /=; apply: IH.
    - lookup => //=; simp filter_queries_with_label; case: eqP => /= Heq.
      * by rewrite Heq -IH // filter_filter_absorb.
      * simp normalize_selections; rewrite Hlook /= IH //; [by rewrite filter_swap | by leq_queries_size].
      * by apply: IH.
      * by simp normalize_selections; rewrite Hlook /=; apply: IH.

    - lookup => //=; simp filter_queries_with_label; case: eqP => /= Heq; do ? by apply: IH; leq_queries_size.
      * case Hscope : is_object_type => //=; simp filter_queries_with_label => //=; case: eqP => //= _;
                                                                                                by rewrite Heq -IH // ?filter_filter_absorb; leq_queries_size.

      * case Hscope : is_object_type => //=; simp filter_queries_with_label => //=; case: eqP => //= _;
                                                                                                simp normalize_selections; rewrite Hlook /= Hscope /= find_filter_swap; do ? by apply/eqP.
        all: do ? [rewrite IH ?filter_filter_absorb; leq_queries_size; by rewrite filter_swap].

      * by simp normalize_selections; rewrite Hlook /=; apply: IH; leq_queries_size.

    - lookup => //=; simp filter_queries_with_label; case: eqP => /= Heq; do ? by apply: IH; leq_queries_size.
      * case Hscope : is_object_type => //=; simp filter_queries_with_label => //=; case: eqP => //= _;
                                                                                                by rewrite Heq -IH // ?filter_filter_absorb; leq_queries_size.

      * case Hscope : is_object_type => //=; simp filter_queries_with_label => //=; case: eqP => //= _;
                                                                                                simp normalize_selections; rewrite Hlook /= Hscope /= find_filter_swap; do ? by apply/eqP.
        all: do ? [rewrite IH ?filter_filter_absorb; leq_queries_size; by rewrite filter_swap].

      * by simp normalize_selections; rewrite Hlook /=; apply: IH; leq_queries_size.

    - case Hfapplies : does_fragment_type_apply => //=; simp filter_queries_with_label.
      * by simp normalize_selections; rewrite Hfapplies /= -filter_queries_with_label_cat; apply: IH; leq_queries_size.
      * by simp normalize_selections; rewrite Hfapplies /=; apply: IH; leq_queries_size.
  Qed.

  (** ** Groundedness *)

  (** ---- *)
  (**
     This lemma states that [normalize_selections] returns fields.
   *)
  Lemma normalized_selections_are_fields ts ss :
    all (fun s => s.(is_field)) (normalize_selections s ts ss).
  Proof.
      by funelim (normalize_selections s ts ss).
  Qed.

  (** ---- *)
  (**
     This lemma states that the resulting selections of [normalize_selections] are 
     in ground-typed normal form.
   *)
  Lemma normalized_selections_are_in_gt_nf ts ss :
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
      * have := (@in_possible_types_is_object Vals s f.(return_type)).
        generalize (get_possible_types s f.(return_type)).
        elim=> //= t ptys IHptys Hinobj.
        have Htobj := (Hinobj t (mem_head _ _)).
        rewrite Htobj andTb.
        apply_andP.
        apply/allP=> sel Hin; apply_andP.
          by move/allP: (normalized_selections_are_fields
                           t
                 (subqueries ++
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
      * have := (@in_possible_types_is_object Vals s f.(return_type)).
        generalize (get_possible_types s f.(return_type)).
        elim=> //= t ptys IHptys Hinobj.
        have Htobj := (Hinobj t (mem_head _ _)).
        rewrite Htobj andTb.
        apply_andP.
        apply/allP=> sel Hin; apply_andP.
        by move/allP: (normalized_selections_are_fields t
                 (subqueries0 ++
                              merge_selection_sets (find_queries_with_label s alias0 type_in_scope l))) => /(_ sel Hin).
        by move/allP: (H t) => /(_ sel Hin).
        by apply: IHptys; intros; apply: Hinobj; apply: mem_tail.
  Qed.

  (** ---- *)
  (**
     This corollary is just the conjunction that the normalized selections are 
     both fields and in ground-typed normal form.
   *)
  Corollary normalized_selections_are_grounded_fields ts ss :
    all (fun sel => sel.(is_field) && is_in_ground_typed_nf s sel) (normalize_selections s ts ss).
  Proof.
    apply/allP=> sel Hin; apply_andP.
      by have/allP-/(_ sel Hin) := (normalized_selections_are_fields ts ss).
        by have/allP-/(_ sel Hin) := (normalized_selections_are_in_gt_nf ts ss).
  Qed.
  

  (* (** ---- *) *)
  (* Lemma normalize_selections_are_in_ground_typed_nf ts ss : *)
  (*   all (is_in_ground_typed_nf s) (gnormalize_selections s ts ss). *)
  (* Proof. *)
  (*   rewrite /gnormalize_selections => /=; case: ifP => /= Hscope. *)
  (*     by apply: normalized_selections_are_in_gt_nf. *)
  (*     apply/allP=> sel. *)
  (*   have  := (@in_possible_types_is_object Vals s ts). *)
  (*   generalize (get_possible_types s ts). *)
  (*   elim=> //= t types IHtypes Hinobj. *)
  (*   have Htobj := (Hinobj t (mem_head _ _)). *)
  (*   rewrite inE => /orP [/eqP -> // | Hin]. *)
  (*   rewrite /is_in_ground_typed_nf; apply_andP. *)
  (*   apply/allP=> nsel Hin; apply_andP. *)
  (*     by have/allP-/(_ nsel Hin):= (normalized_selections_are_fields t ss). *)
  (*     by have/allP-/(_ nsel Hin) := (normalized_selections_are_in_gt_nf t ss). *)
  (*       by apply: IHtypes => //; intros; apply: Hinobj; apply: mem_tail. *)
  (* Qed. *)
  


  (** ---- *)
  (** ** Non-redundancy *)
  (** ---- *)
  (**
     This lemma states that the result of [normalize_selections] are
     non-redundant, whenever the type used to normalize 
     is an Object type.
   *)
  Lemma normalized_selections_are_non_redundant ty φ :
    are_non_redundant (normalize_selections s ty φ).
  Proof.
    apply_funelim (normalize_selections s ty φ) => //=.


    all: do ? [by intros; non_red; apply_and3P; by rewrite -filter_normalize_swap /= find_fields_filter_nil].
    
    all: do [intros; non_red; apply_and3P => /=; [ by rewrite -filter_normalize_swap /= find_fields_filter_nil |] ].
    all: do [have  := (@in_possible_types_is_object Vals s f.(return_type))].
    all: do [have  := (uniq_get_possible_types s f.(return_type))].
    all: do [elim: get_possible_types => //= t ptys IH /andP [Hnin Huniq] Hinobj].
    all: do [non_red; apply_and3P => /=; last by apply: IH => //= t' Hin'; apply: Hinobj; apply: mem_tail].
    all: do ? by apply/eqP; apply: find_fragment_inlined_nil_func.
  Qed.

  (* (** ---- *) *)
  (* (** *)
  (*    This lemma states that the result of [normalize_queries] are *)
  (*    non-redundant, regardless of the type used to normalize. *)
  (*  *) *)
  (* Lemma normalize_gselections_are_non_redundant ty φ : *)
  (*   are_non_redundant (gnormalize_selections s ty φ). *)
  (* Proof. *)
  (*   rewrite /gnormalize_selections => /=; case: ifP => /= Hscope; first by apply: normalized_selections_are_non_redundant. *)
  (*   have  := (@in_possible_types_is_object Vals s ty). *)
  (*   have  := (uniq_get_possible_types s ty). *)
  (*   elim: get_possible_types => //= t ptys IH /andP [Hnin Huniq] Hinobj. *)
  (*   simp are_non_redundant; apply_and3P => /=; last by apply: IH => //= t' Hin'; apply: Hinobj; apply: mem_tail. *)
  (*     by apply/eqP; apply: find_fragment_inlined_nil_func. *)
  (*     by apply: normalized_selections_are_non_redundant; apply: Hinobj; apply: mem_head. *)
  (* Qed. *)


  (** ---- *)
  (**
     This theorem states that [normalize] returns a query in normal form. 
   *)
  Theorem normalized_query_is_in_nf (q : @query Vals) :
    is_in_normal_form s (normalize s q).
  Proof.
    case: q; intros.
    rewrite /is_in_normal_form /normalize /=; apply_andP.
    - rewrite /is_a_grounded_typed_nf_query /=.
        by apply: normalized_selections_are_grounded_fields.
    - rewrite /is_non_redundant.
        by apply: normalized_selections_are_non_redundant.
  Qed.

   
  

End Normalisation.
