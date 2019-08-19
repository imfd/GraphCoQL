From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From Equations Require Import Equations.

Require Import String.
Require Import QString.

Require Import Base. 
Require Import Schema.
Require Import SchemaAux.
Require Import SchemaAuxLemmas.
Require Import SchemaWellFormedness.
Require Import SchemaWFLemmas.

Require Import Query.
Require Import QueryAux.
Require Import QueryAuxLemmas.
Require Import QueryConformance.


Require Import NRGTNF.
Require Import NRGTNFLemmas.
Require Import QueryNormalization.

Require Import Ssromega.

Require Import SeqExtra.

Require Import QueryTactics.
Require Import GeneralTactics.


Section Theory.
  
 
  Transparent qresponse_name.

    
  Variables (Vals : eqType).
  
  Variable (s : @wfGraphQLSchema Vals).

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


  (**
     This lemma states that 
   *)
  Lemma normalize_preserves_not_similar q (Hfield : q.(is_field)) φ ty :
    ~~has (fun q' => are_similar q' q) (normalize s ty (filter_queries_with_label (qresponse_name q Hfield) φ)).
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n φ => /= [| n IH] φ; first by rewrite leqn0 => /queries_size_0_nil ->.
    case: φ => // q' φ.
    case_query q'; simp query_size => Hleq; simp filter_queries_with_label.
    - case: eqP => //= Heq.
        by apply: IH.
        simp normalize; lookup; last by apply: IH.
        apply/norP; split=> //; last by rewrite filter_swap //; apply: IH; leq_queries_size.
          by case_query q => //=; intros; simp are_similar => /=; apply/nandP; left; apply/eqP.
    - case: eqP => //= Heq.
        by apply: IH.
        simp normalize; lookup; last by apply: IH.
        apply/norP; split=> //; last by rewrite filter_swap //; apply: IH; leq_queries_size.
          by case_query q => //=; intros; simp are_similar => /=; apply/nandP; left; apply/eqP.

    - case: eqP => //= Heq.
        by apply: IH; leq_queries_size.
        simp normalize; lookup; last by apply: IH; leq_queries_size.
        case is_object_type => //=; apply/norP; split=> //; do ? by rewrite filter_swap //; apply: IH; leq_queries_size.
        all: do ?by case_query q => //=; intros; simp are_similar => /=; apply/nandP; left; apply/eqP.

    - case: eqP => //= Heq.
        by apply: IH; leq_queries_size.
        simp normalize; lookup; last by apply: IH; leq_queries_size.
        case is_object_type => //=; apply/norP; split; do ? by rewrite filter_swap //; apply: IH; leq_queries_size.
        all: do ?by case_query q => //=; intros; simp are_similar => /=; apply/nandP; left; apply/eqP.

    - simp normalize; case does_fragment_type_apply => //=; last by apply: IH; leq_queries_size.
        by rewrite -filter_queries_with_label_cat; apply: IH; leq_queries_size.
  Qed.
  
  
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
    - intros; simp are_non_redundant; apply_and3P; [ by apply: normalize_preserves_not_similar | by apply: H].
      
    - intros; simp are_non_redundant; apply_and3P; [ by apply: normalize_preserves_not_similar | by apply: H].
      
    - intros; simp are_non_redundant; apply_and3P => /=; [ by apply: normalize_preserves_not_similar | by apply: H | by apply: H0].

    - intros; simp are_non_redundant; apply_and3P => /=; [ by apply: normalize_preserves_not_similar | | by apply: H0].
      have  := (@in_possible_types_is_object Vals s f.(return_type)).
      have  := (uniq_get_possible_types s f.(return_type)).
      elim: get_possible_types => //= t ptys IH /andP [Hnin Huniq] Hinobj.
      simp are_non_redundant; apply_and3P => /=; last by apply: IH => //= t' Hin'; apply: Hinobj; apply: mem_tail.
      apply/hasPn=> frag /mapP [t' Htin ->]; simp are_similar.
        by move/memPn: Hnin => /(_ t' Htin).
          by apply: H; apply: Hinobj; apply: mem_head.
          
    - intros; simp are_non_redundant; apply_and3P => /=; [ by apply: normalize_preserves_not_similar | by apply: H | by apply: H0].

    - intros; simp are_non_redundant; apply_and3P => /=; [ by apply: normalize_preserves_not_similar | | by apply: H0].
      have  := (@in_possible_types_is_object Vals s f.(return_type)).
      have  := (uniq_get_possible_types s f.(return_type)).
      elim: get_possible_types => //= t ptys IH /andP [Hnin Huniq] Hinobj.
      simp are_non_redundant; apply_and3P => /=; last by apply: IH => //= t' Hin'; apply: Hinobj; apply: mem_tail.
      apply/hasPn=> frag /mapP [t' Htin ->]; simp are_similar.
        by move/memPn: Hnin => /(_ t' Htin).
          by apply: H; apply: Hinobj; apply: mem_head.
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
    apply/hasPn=> frag /mapP [t' Htin ->]; simp are_similar.
      by move/memPn: Hnin => /(_ t' Htin).
        by apply: normalize_are_non_redundant; apply: Hinobj; apply: mem_head.
  Qed.


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
  

End Theory.




(* Lemma inlining_preserves_non_redundancy (φ : seq (@Query Vals)) (ptys : seq Name) : *)
  (*   are_non_redundant φ -> *)
  (*   uniq ptys -> *)
  (*   are_non_redundant [seq InlineFragment t φ | t <- ptys]. *)
  (* Proof. *)
  (*   elim: ptys => //= t ptys IH Hnr /andP [Hnin Huniq]. *)
  (*   simp are_non_redundant; apply_and3P => /=; last by apply: IH. *)
  (*   apply/hasPn=> frag /mapP [t' Hin ->]; simp are_similar. *)
  (*     by move/memPn: Hnin => /(_ t' Hin). *)
  (* Qed. *)