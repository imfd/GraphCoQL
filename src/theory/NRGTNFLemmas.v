From mathcomp Require Import all_ssreflect.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.
From extructures Require Import ord.


Require Import Query.
Require Import QueryAux.
Require Import SchemaWellFormedness.

Require Import Schema.
Require Import SchemaAux.

Require Import QueryConformance.

Require Import SeqExtra.

Require Import Ssromega.

Require Import NRGTNF.

Section Theory.

  Ltac apply_andP := apply/andP; split=> //.
  Ltac apply_and3P := apply/and3P; split=> //.

  Variables (Name Vals : ordType).

  Section Ground.
    Variable (s : @wfSchema Name Vals).
    
    Lemma are_grounded_fields_E qs : are_grounded_fields s qs = all (fun q => q.(is_field)) qs && all (is_grounded s) qs.
    Proof.
      elim: qs => //= q qs ->.
        by rewrite andbACA -[RHS]andbA.
    Qed.
    
    Lemma are_grounded_inlines_E qs : are_grounded_inlines s qs = all (fun q => q.(is_inline_fragment)) qs && all (is_grounded s) qs.
    Proof.
      elim: qs => //= q qs ->.
        by rewrite andbACA -[RHS]andbA.
    Qed.

    
    Lemma are_grounded2_cat ty qs1 qs2 :
      are_grounded2 s ty (qs1 ++ qs2) = are_grounded2 s ty qs1 && are_grounded2 s ty qs2 .
    Proof.
      elim: qs1 => //= q qs1 IH.
        by case is_object_type => /=; rewrite IH //=;
                                     rewrite -[RHS]andbA -[(_ && are_grounded2 s ty qs1) && are_grounded2 s ty qs2]andbA.
    Qed.

    Lemma are_grounded2_consE ty q qs :
      are_grounded2 s ty (q :: qs) ->
      are_grounded2 s ty qs.
    Proof.
        by case: q => //= [f α | l f α | f α φ | l f α φ | t φ]; case: is_object_type => /=; case/and3P.
    Qed.

    Lemma grounded2_are_fields_in_object_scope :
      forall ty qs,
        is_object_type s ty ->
        are_grounded2 s ty qs ->
        all (fun q => q.(is_field)) qs.
    Proof.
      apply (is_grounded2_elim Name Vals s
               (fun ty q b => true)
               (fun ty qs b =>
                  is_object_type s ty ->
                  b ->
                  all (fun q => q.(is_field)) qs)) => //.
      - by intros => /=; case/and3P: H2 => *; apply_andP; apply: H0.
      - by intros; rewrite H1 in Heq.
    Qed.


    Lemma are_grounded2_are_grounded :
      forall queries ty,
        are_grounded2 s ty queries ->
        are_grounded s queries.
    Proof.
      apply (is_grounded_elim Name Vals s
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
        * have : forall (q : @Query Name Vals), q.(is_inline_fragment) -> q.(is_field) = false by case.
            by move/(_ q Htype) ->; apply_andP; [apply : (IHq ty) | apply: (IHinls ty)].
    Qed.
    
  End Ground.

  Section NonRedundant.

  End NonRedundant.

  
End Theory.
