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
Require Import SchemaAuxLemmas.
Require Import SchemaWellFormedness.
Require Import SchemaWFLemmas.

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
        <h1 class="display-4">Normal Form</h1>
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


  Variables (Vals : eqType).

  Section Ground.
    Variable (s : @wfGraphQLSchema Vals).

    (**
       Elimination lemma for [are_grounded_fields].
     *)
    Lemma are_grounded_fields_E φ :
      are_grounded_fields s φ = all (fun q => q.(is_field)) φ && all (is_grounded s) φ.
    Proof.
      elim: φ => //= q φ ->.
        by rewrite andbACA -[RHS]andbA.
    Qed.

    (**
       This lemma states that if some queries [are_grounded_fields] then 
       they [are_grounded].
     *)
    Lemma are_grounded_fields_grounded φ :
      are_grounded_fields s φ ->
      are_grounded s φ.
    Proof.
        by case: φ => //= q φ; case_query q.
    Qed.

    (**
       Elimination lemma for [are_grounded_fields].
     *)
    Lemma are_grounded_inlines_E qs : are_grounded_inlines s qs = all (fun q => q.(is_inline_fragment)) qs && all (is_grounded s) qs.
    Proof.
      elim: qs => //= q qs ->.
        by rewrite andbACA -[RHS]andbA.
    Qed.

    (**
       This lemma states that if some queries [are_grounded_inlines] then 
       they [are_grounded].
     *)
    Lemma are_grounded_inlines_grounded φ :
      are_grounded_inlines s φ ->
      are_grounded s φ.
    Proof.
        by case: φ => //= q φ; case_query q.
    Qed.

      
    
    (**
       This lemma states that the predicate [are_grounded2] distributes over list concatenation.
     *)
    Lemma are_grounded2_cat ty qs1 qs2 :
      are_grounded2 s ty (qs1 ++ qs2) = are_grounded2 s ty qs1 && are_grounded2 s ty qs2 .
    Proof.
      elim: qs1 => //= q qs1 IH.
        by case is_object_type => /=; rewrite IH //=;
                                     rewrite -[RHS]andbA -[(_ && are_grounded2 s ty qs1) && are_grounded2 s ty qs2]andbA.
    Qed.


    (**
       This lemma states that [are_grounded2] implies [are_grounded].
     *)
    Lemma are_grounded2_are_grounded :
      forall queries ty,
        are_grounded2 s ty queries ->
        are_grounded s queries.
    Proof.
      apply (is_grounded_elim Vals s
               (fun q b =>
                  forall ty,
                    is_grounded2 s ty q ->
                    b)
               (fun qs b =>
                  forall ty,
                    is_object_type s ty ->
                    are_grounded2 s ty qs ->
                    b)
               (fun qs b =>
                  forall ty,
                    is_object_type s ty = false ->
                    are_grounded2 s ty qs ->
                    b)
               (fun qs b =>
                  forall ty,
                    are_grounded2 s ty qs ->
                    b)
            ) => //=.
      
      - move=> f α φ IH ty; simp is_grounded2.
        case lookup_field_in_type => //=; case; intros; apply: IH; exact: H.
      - move=> l f α φ IH ty; simp is_grounded2.
        case lookup_field_in_type => //=; case; intros; apply: IH; exact: H.
      - by move=> t φ IH ty; simp is_grounded2 => /andP [Ht Hg]; apply_andP; apply: (IH t) => //.

      - by move=> q qs IHq IHqs ty Hcond /=; rewrite Hcond /= => /and3P [Hf Hg Hgs]; apply_and3P; [ apply: (IHq ty) | apply: (IHqs ty)].
      -  by move=> q qs IHq IHqs ty Hscope; rewrite Hscope /=; case/and3P=> *; apply_and3P; [apply: (IHq ty) | apply: (IHqs ty)].
         
      - move=> q qs IHq IHflds IHinls ty.
        case Hscope : is_object_type => //= /and3P [Htype Hg Hgs].
        * by rewrite Htype; apply_andP; [apply: (IHq ty) | apply: (IHflds ty)].
        * have : forall (q : @Query Vals), q.(is_inline_fragment) -> q.(is_field) = false by case.
            by move/(_ q Htype) ->; apply_andP; [apply : (IHq ty) | apply: (IHinls ty)].
    Qed.


   

    Section Filter.

      Transparent is_field.

      (**
         This lemma states that filtering according to a particular
         response name preserves [are_grounded_fields].
       *)
      Lemma filter_preserves_field_grounding rname φ :
        are_grounded_fields s φ ->
        are_grounded_fields s (filter_queries_with_label rname φ).
      Proof.
        funelim (filter_queries_with_label rname φ) => //= /andP [Hg Hgs]; do ? apply_andP; by apply: H.
      Qed.

      (**
         This lemma states that filtering according to a particular
         response name preserves [are_grounded_inlines].
       *)
      Lemma filter_preserves_inline_grounding rname φ :
        are_grounded_inlines s φ ->
        are_grounded_inlines s (filter_queries_with_label rname φ).
      Proof.
        funelim (filter_queries_with_label rname φ) => //=.
        simp is_grounded => /and3P [_ /andP [Hobj Hsg] Hgs].
        apply_and3P; last by apply: H0.
          by apply_andP; apply: filter_preserves_field_grounding.
      Qed.

      (**
         This lemma states that filtering according to a particular
         response name preserves [are_grounded].
       *)
      Lemma filter_preserves_grounding rname φ :
        are_grounded s φ ->
        are_grounded s (filter_queries_with_label rname φ).
      Proof.
        funelim (filter_queries_with_label rname φ) => //=; simp is_grounded => /=.
        - move=> /andP [/andP [Hobj Hg] Hgs]; apply_andP.
          * by apply_andP; apply: filter_preserves_field_grounding.
          * by apply: filter_preserves_inline_grounding.

            all: do ? case/andP.
            all: do [intros].
            all: do ? apply_andP.
            all: do ? apply: H.      
            all: do ? [by apply: filter_preserves_field_grounding].
            all: do ? [by apply: are_grounded_fields_grounded].
      Qed.
      
    End Filter.
    
  End Ground.

  Section NonRedundant.

    
    Implicit Type φ : seq (@Query Vals).

    
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


Ltac grounding :=
  repeat match goal with
         (* | [|- context [are_grounded (_ ++ _)] ] => rewrite are_grounded_cat *)
         | [|- is_true (are_grounded _ (filter_queries_with_label _ _))] =>
           apply: filter_preserves_grounding
                    
         | [H : ?P |- ?P] => exact: H
         | [H : is_true (are_grounded_fields _ ?φ) |- is_true (are_grounded _ ?φ)] => by apply: are_grounded_fields_grounded
         | [H : is_true (are_grounded_inlines _ ?φ) |- is_true (are_grounded _ ?φ)] => by apply: are_grounded_inlines_grounded
                                                                                                 
         | [|- context [are_grounded _ (_ :: _)] ] => rewrite are_grounded_equation_2 /=
                                                            (* | [|- context [is_grounded _ _] ] => simp is_grounded *)
         end.

Ltac non_red :=
  repeat match goal with
         | [|- is_true (are_non_redundant (filter_queries_with_label _ _))] =>
             by apply: filter_preserves_non_redundancy
         | [|- context [are_non_redundant (_ :: _)] ] => simp are_non_redundant
         | [|- is_true (are_non_redundant (_ :: _)) -> _] => simp are_non_redundant
         | [|- is_true (are_non_redundant _)] => simp are_non_redundant
         end.



Section Normalisation.

  
  Transparent qresponse_name.
  
  Variables (Vals : eqType) (s : @wfGraphQLSchema Vals).

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

End Normalisation.








(* Unused lemmas *)


 (* 
    
    (* Lemma are_grounded_inlines_E qs : are_grounded_inlines s qs = all (fun q => q.(is_inline_fragment)) qs && all (is_grounded s) qs. *)
    (* Proof. *)
    (*   elim: qs => //= q qs ->. *)
    (*     by rewrite andbACA -[RHS]andbA. *)
    (* Qed. *)


  (* Lemma are_grounded2_consE ty q qs : *)
    (*   are_grounded2 s ty (q :: qs) -> *)
    (*   are_grounded2 s ty qs. *)
    (* Proof. *)
    (*     by case: q => //= [f α | l f α | f α φ | l f α φ | t φ]; case: is_object_type => /=; case/and3P. *)
    (* Qed. *)

    (* Lemma grounded2_are_fields_in_object_scope : *)
    (*   forall ty qs, *)
    (*     is_object_type s ty -> *)
    (*     are_grounded2 s ty qs -> *)
    (*     all (fun q => q.(is_field)) qs. *)
    (* Proof. *)
    (*   apply (is_grounded2_elim Vals s *)
    (*            (fun ty q b => true) *)
    (*            (fun ty qs b => *)
    (*               is_object_type s ty -> *)
    (*               b -> *)
    (*               all (fun q => q.(is_field)) qs)) => //. *)
    (*   - by intros => /=; case/and3P: H2 => *; apply_andP; apply: H0. *)
    (*   - by intros; rewrite H1 in Heq. *)
    (* Qed. 
*)
*)