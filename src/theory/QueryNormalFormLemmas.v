(* begin hide *)

From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.


Require Import Query.
Require Import QueryAux.
Require Import QueryAuxLemmas.
Require Import QueryTactics.

Require Import SchemaWellFormedness.

Require Import Schema.
Require Import SchemaAux.


Require Import SeqExtra.

Require Import Ssromega.

Require Import QueryNormalForm.

Require Import GeneralTactics.

(* end hide *)


Section Theory.


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

  
End Theory.


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