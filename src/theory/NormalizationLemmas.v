From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From Equations Require Import Equations.

From extructures Require Import ord.

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
Require Import QueryRewrite.

Require Import Ssromega.

Require Import SeqExtra.

Require Import QueryTactics.


Section Theory.
  
  Ltac orL := apply/orP; left.
  Ltac orR := apply/orP; right.
  
  Ltac apply_andP := apply/andP; split=> //.
  Ltac apply_and3P := apply/and3P; split=> //.
  Ltac all_cons := rewrite {1}/all -/(all _ _) => /andP; case.
  Ltac query_conforms := simp query_conforms; try move/and5P; try apply/and5P.


  Transparent qresponse_name.

    
  Variables (Name Vals : ordType).
  
  Variable (s : @wfSchema Name Vals).

  Lemma reground_are_grounded2 ty φ :
    is_object_type s ty ->
    are_grounded2 s ty (reground s ty φ).
  Proof.
    apply_funelim (reground s ty φ) => //=; clear ty φ.
    - by move=> ty f fld α φ IH Hlook Hscope; rewrite Hscope /=; apply_and3P; apply: IH.

    - by move=> ty f fld l α φ IH Hlook Hscope; rewrite Hscope /= ; apply_and3P; apply: IH.

    - move=> ty f fld α β φ IHsub IH Hrty Hlook Hscope; rewrite Hscope /=; apply_and3P; last by apply: IH.
        by simp is_grounded2; rewrite Hlook /=; apply: IHsub.

    - move=> fld ty f α β φ IHsub IH Hrty Hlook Hscope; rewrite Hscope /=; apply_and3P; last by apply: IH.
      simp is_grounded2; rewrite Hlook /=.
      have := (@in_possible_types_is_object Name Vals s fld.(return_type)).
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
      have := (@in_possible_types_is_object Name Vals s fld.(return_type)).
      elim: get_possible_types => //= t ptys IHptys Hinobj.
      rewrite Hrty /=; apply_and3P.
      simp is_grounded2; apply_andP.
        by apply: Hinobj; apply: mem_head.
          by apply: IHsub; apply: Hinobj; apply: mem_head.
            by apply: IHptys => t' Hin'; apply: Hinobj; apply: mem_tail.     
  Qed.
  
  Lemma ground_queries_are_grounded2 ty φ :
    are_grounded2 s ty (ground_queries s ty φ).
  Proof.
    apply_funelim (ground_queries s ty φ) => /=; clear ty φ.
    - by move=> ty φ Hscope; apply: reground_are_grounded2.
    - move=> ty φ Hscope.
      have := (@in_possible_types_is_object Name Vals s ty).
      elim: get_possible_types => //= t ptys IH Hinobj.
      rewrite Hscope /=; apply_and3P.
      * simp is_grounded2; apply_andP; [| apply: reground_are_grounded2]; by apply: Hinobj; apply: mem_head.
      * by apply: IH => t' Hin; apply: Hinobj; apply: mem_tail.
  Qed.

  Lemma reground_preserves_not_similar q (Hfield : q.(is_field)) φ ty :
    all (fun q' => ~~are_similar q' q) (reground s ty (filter_queries_with_label (qresponse_name q Hfield) φ)).
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n φ => /= [| n IH] φ; first by rewrite leqn0 => /queries_size_0_nil ->.
    case: φ => // q' φ.
    case_query q'; simp query_size => Hleq; simp filter_queries_with_label.
    - case: eqP => //= Heq.
        by apply: IH.
        simp reground; lookup; last by apply: IH.
        apply_andP; last by rewrite filter_swap //; apply: IH; leq_queries_size.
          by case_query q => //=; intros; simp are_similar => /=; apply/nandP; left; apply/eqP.
    - case: eqP => //= Heq.
        by apply: IH.
        simp reground; lookup; last by apply: IH.
        apply_andP; last by rewrite filter_swap //; apply: IH; leq_queries_size.
          by case_query q => //=; intros; simp are_similar => /=; apply/nandP; left; apply/eqP.

    - case: eqP => //= Heq.
        by apply: IH; leq_queries_size.
        simp reground; lookup; last by apply: IH; leq_queries_size.
        case is_object_type => //=; apply_andP; do ? by rewrite filter_swap //; apply: IH; leq_queries_size.
        all: do ?by case_query q => //=; intros; simp are_similar => /=; apply/nandP; left; apply/eqP.

    - case: eqP => //= Heq.
        by apply: IH; leq_queries_size.
        simp reground; lookup; last by apply: IH; leq_queries_size.
        case is_object_type => //=; apply_andP; do ? by rewrite filter_swap //; apply: IH; leq_queries_size.
        all: do ?by case_query q => //=; intros; simp are_similar => /=; apply/nandP; left; apply/eqP.

    - simp reground; case does_fragment_type_apply => //=; last by apply: IH; leq_queries_size.
        by rewrite -filter_queries_with_label_cat; apply: IH; leq_queries_size.
  Qed.
  
  
  Lemma inlining_preserves_non_redundancy (φ : seq (@Query Name Vals)) ptys :
    are_non_redundant φ ->
    uniq ptys ->
    are_non_redundant [seq InlineFragment t φ | t <- ptys].
  Proof.
    elim: ptys => //= t ptys IH Hnr /andP [Hnin Huniq].
    simp are_non_redundant; apply_and3P => /=; last by apply: IH.
    apply/allP=> frag /mapP [t' Hin ->]; simp are_similar.
      by move/memPn: Hnin => /(_ t' Hin).
  Qed.
  
  Lemma reground_are_non_redundant ty φ :
    is_object_type s ty ->
    are_non_redundant (reground s ty φ).
  Proof.
    apply_funelim (reground s ty φ) => //=.
    - intros; simp are_non_redundant; apply_and3P; [ by apply: reground_preserves_not_similar | by apply: H].
      
    - intros; simp are_non_redundant; apply_and3P; [ by apply: reground_preserves_not_similar | by apply: H].
      
    - intros; simp are_non_redundant; apply_and3P => /=; [ by apply: reground_preserves_not_similar | by apply: H | by apply: H0].

    - intros; simp are_non_redundant; apply_and3P => /=; [ by apply: reground_preserves_not_similar | | by apply: H0].
      have  := (@in_possible_types_is_object Name Vals s f.(return_type)).
      have  := (uniq_get_possible_types s f.(return_type)).
      elim: get_possible_types => //= t ptys IH /andP [Hnin Huniq] Hinobj.
      simp are_non_redundant; apply_and3P => /=; last by apply: IH => //= t' Hin'; apply: Hinobj; apply: mem_tail.
      apply/allP=> frag /mapP [t' Htin ->]; simp are_similar.
        by move/memPn: Hnin => /(_ t' Htin).
          by apply: H; apply: Hinobj; apply: mem_head.
          
    - intros; simp are_non_redundant; apply_and3P => /=; [ by apply: reground_preserves_not_similar | by apply: H | by apply: H0].

    - intros; simp are_non_redundant; apply_and3P => /=; [ by apply: reground_preserves_not_similar | | by apply: H0].
      have  := (@in_possible_types_is_object Name Vals s f.(return_type)).
      have  := (uniq_get_possible_types s f.(return_type)).
      elim: get_possible_types => //= t ptys IH /andP [Hnin Huniq] Hinobj.
      simp are_non_redundant; apply_and3P => /=; last by apply: IH => //= t' Hin'; apply: Hinobj; apply: mem_tail.
      apply/allP=> frag /mapP [t' Htin ->]; simp are_similar.
        by move/memPn: Hnin => /(_ t' Htin).
          by apply: H; apply: Hinobj; apply: mem_head.
  Qed.
  

  Lemma ground_queries_are_non_redundant ty φ :
    are_non_redundant (ground_queries s ty φ).
  Proof.
    apply_funelim (ground_queries s ty φ) => //=; clear ty φ; first by intros; apply: reground_are_non_redundant.
    move=> ty φ Hscope.
    have  := (@in_possible_types_is_object Name Vals s ty).
    have  := (uniq_get_possible_types s ty).
    elim: get_possible_types => //= t ptys IH /andP [Hnin Huniq] Hinobj.
    simp are_non_redundant; apply_and3P => /=; last by apply: IH => //= t' Hin'; apply: Hinobj; apply: mem_tail.
    apply/allP=> frag /mapP [t' Htin ->]; simp are_similar.
      by move/memPn: Hnin => /(_ t' Htin).
        by apply: reground_are_non_redundant; apply: Hinobj; apply: mem_head.
  Qed.


  Lemma filter_reground_swap rname ty φ :
    filter_queries_with_label rname (reground s ty φ) = reground s ty (filter_queries_with_label rname φ).
  Proof.
    move: {2}(queries_size _) (leqnn (queries_size φ)) => n.
    elim: n φ rname => /= [| n IH] φ rname ; first by rewrite leqn0 => /queries_size_0_nil ->.
    case: φ => //= q φ.
    case_query q => /=; simp query_size => Hleq; simp reground.
    - lookup => //=; simp filter_queries_with_label; case: eqP => /= [/= Heq | Hneq].
      * by rewrite Heq -IH // filter_filter_absorb.
      * simp reground; rewrite Hlook /= IH //; [by rewrite filter_swap | by leq_queries_size].
      * by apply: IH.
      * by simp reground; rewrite Hlook /=; apply: IH.
    - lookup => //=; simp filter_queries_with_label; case: eqP => /= Heq.
      * by rewrite Heq -IH // filter_filter_absorb.
      * simp reground; rewrite Hlook /= IH //; [by rewrite filter_swap | by leq_queries_size].
      * by apply: IH.
      * by simp reground; rewrite Hlook /=; apply: IH.

    - lookup => //=; simp filter_queries_with_label; case: eqP => /= Heq; do ? by apply: IH; leq_queries_size.
      * case Hscope : is_object_type => //=; simp filter_queries_with_label => //=; case: eqP => //= _;
                                                                                                by rewrite Heq -IH // ?filter_filter_absorb; leq_queries_size.

      * case Hscope : is_object_type => //=; simp filter_queries_with_label => //=; case: eqP => //= _;
                                                                                                simp reground; rewrite Hlook /= Hscope /= find_filter_swap; do ? by apply/eqP.
        all: do ? [rewrite IH ?filter_filter_absorb; leq_queries_size; by rewrite filter_swap].

      * by simp reground; rewrite Hlook /=; apply: IH; leq_queries_size.

    - lookup => //=; simp filter_queries_with_label; case: eqP => /= Heq; do ? by apply: IH; leq_queries_size.
      * case Hscope : is_object_type => //=; simp filter_queries_with_label => //=; case: eqP => //= _;
                                                                                                by rewrite Heq -IH // ?filter_filter_absorb; leq_queries_size.

      * case Hscope : is_object_type => //=; simp filter_queries_with_label => //=; case: eqP => //= _;
                                                                                                simp reground; rewrite Hlook /= Hscope /= find_filter_swap; do ? by apply/eqP.
        all: do ? [rewrite IH ?filter_filter_absorb; leq_queries_size; by rewrite filter_swap].

      * by simp reground; rewrite Hlook /=; apply: IH; leq_queries_size.

    - case Hfapplies : does_fragment_type_apply => //=; simp filter_queries_with_label.
      * by simp reground; rewrite Hfapplies /= -filter_queries_with_label_cat; apply: IH; leq_queries_size.
      * by simp reground; rewrite Hfapplies /=; apply: IH; leq_queries_size.
  Qed.
  

End Theory.