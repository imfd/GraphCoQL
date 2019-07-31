Require Import List.
From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

From Equations Require Import Equations.
From extructures Require Import ord fmap fset.


Require Import Query.
Require Import QueryAux.
Require Import SchemaWellFormedness.

Require Import Schema.
Require Import SchemaAux.

Require Import QueryConformance.

Require Import SeqExtra.

Require Import Ssromega.

Section NRGTNF.

  Variables Name Vals : ordType.
  Variable s : @wfSchema Name Vals.
  
  Implicit Type queries : seq (@Query Name Vals).
  Implicit Type query : @Query Name Vals.
  Notation is_field := (@is_field Name Vals).
  Notation is_inline_fragment := (@Query.is_inline_fragment Name Vals).

  Ltac apply_andP := apply/andP; split=> //.
  Ltac apply_and3P := apply/and3P; split=> //.

  
  Equations is_grounded query : bool  :=
    {
      is_grounded (NestedField _ _ φ) := are_grounded φ;
      
      is_grounded (NestedLabeledField _ _ _ φ) := are_grounded φ;
      
      is_grounded (InlineFragment t φ) := (is_object_type s t) && are_grounded_fields φ; (* (all is_field φ) & all is_grounded φ *)
      
      is_grounded  _ := true
    }
  where are_grounded_fields queries : bool :=
          {
            are_grounded_fields [::] := true;
            are_grounded_fields (q :: qs) := [&& q.(is_field), q.(is_grounded) & are_grounded_fields qs]
          }
  where are_grounded_inlines queries : bool :=
          {
            are_grounded_inlines [::] := true;
            are_grounded_inlines (q :: qs) := [&& q.(is_inline_fragment), q.(is_grounded) & are_grounded_inlines qs]
          }
  where are_grounded queries : bool :=
          {
            are_grounded [::] := true;
            are_grounded (q :: qs) := q.(is_grounded) && if q.(is_field) then are_grounded_fields qs else are_grounded_inlines qs
                                                                                                                              
          }.
  
      
  Lemma are_grounded_fields_E qs : are_grounded_fields qs = all is_field qs && all is_grounded qs.
  Proof.
    elim: qs => //= q qs ->.
      by rewrite andbACA -[RHS]andbA.
  Qed.
  
  Lemma are_grounded_inlines_E qs : are_grounded_inlines qs = all is_inline_fragment qs && all is_grounded qs.
  Proof.
    elim: qs => //= q qs ->.
      by rewrite andbACA -[RHS]andbA.
  Qed.
 
  Equations is_grounded2 (type_in_scope : @NamedType Name) (query : @Query Name Vals) : bool :=
    {
      is_grounded2 ty (NestedField f _ φ)
        with lookup_field_in_type s ty f :=
        {
        | Some fld := are_grounded2 fld.(return_type) φ;
        | _ := false
        };

      is_grounded2 ty (NestedLabeledField _ f _ φ)
        with lookup_field_in_type s ty f :=
        {
        | Some fld := are_grounded2 fld.(return_type) φ;
        | _ := false
        };

      is_grounded2 ty (InlineFragment t φ) := (is_object_type s t) && are_grounded2 t φ;
      
      is_grounded2 _ _ := true
    }
   where
   are_grounded2 (type_in_scope : @NamedType Name) (queries : seq (@Query Name Vals)) : bool :=
     {
       are_grounded2 _ [::] := true;
       are_grounded2 ty (hd :: tl)
         with is_object_type s ty :=
         {
         | true  := [&& is_field hd, is_grounded2 ty hd & are_grounded2 ty tl];
         | _ := [&& is_inline_fragment hd, is_grounded2 ty hd & are_grounded2 ty tl]
         }
     }.


  Lemma are_grounded2_cat ty qs1 qs2 :
    are_grounded2 ty (qs1 ++ qs2) = are_grounded2 ty qs1 && are_grounded2 ty qs2 .
  Proof.
    elim: qs1 => //= q qs1 IH.
    by case is_object_type => /=; rewrite IH //=;
    rewrite -[RHS]andbA -[(_ && are_grounded2 ty qs1) && are_grounded2 ty qs2]andbA.
  Qed.

  Lemma are_grounded2_consE ty q qs :
    are_grounded2 ty (q :: qs) ->
    are_grounded2 ty qs.
  Proof.
    by case: q => //= [f α | l f α | f α φ | l f α φ | t φ]; case: is_object_type => /=; case/and3P.
  Qed.

    
  
   (*
  
   Lemma are_grounded_in_abstract_scope_are_any schema ty queries :
     is_abstract_type schema ty ->
     are_grounded_2 schema ty queries ->
     all is_field queries \/ all is_inline_fragment queries.
   Proof.
     move=> Habs; rewrite are_grounded_2E.
     rewrite abstract_type_N_obj //=.
     by move/andP=> [/orP [/andP [_ Hinl] | /andP [_ Hflds]] _]; [right | left].
   Qed.
   
   Lemma all_grounded_fields_in_object_scope_are_grounded schema ty queries :
     is_object_type schema ty ->
     all is_field queries ->
     all (is_grounded_2 schema ty) queries ->
     are_grounded_2 schema ty queries.
   Proof.
       by move=> Hobj; rewrite are_grounded_2E Hobj /= orbF => Hflds Hgs; apply/andP.
   Qed.
    *)

   (* Lemma is_grounded_2_in_normal_form schema query :
     forall ty,
       query_conforms schema ty query ->
       is_grounded_2 schema ty query ->
       is_grounded query.
   Proof.
     elim query using Query_ind with
         (Pl := fun qs =>
                 forall ty,
                   all (query_conforms schema ty) qs ->
                   are_grounded_2 schema ty qs ->
                   all (is_grounded) qs) => // [f α | l f α | t | hd IHhd tl IHtl ]; last first.
     - move=> ty.
       all_cons => [Hqc Hqsc] /=.
       case: is_object_type => //=; [| case get_possible_types => //= [| hd' tl']]; move/and3P=> [Hty Hg Hgs];
       by apply/andP; split; [apply: (IHhd ty) | apply: (IHtl ty)].
       
     all: do [move=> φ IH ty]; simp is_grounded_2; simp is_in_normal_form.

     - simp query_conforms => /and5P [_ _ Hne Hqsc _] /and3P [Hobj Hflds Hg].
       apply/and3P; split => //.
       apply: (IH t) => //= {IH}.
         by apply: all_grounded_fields_in_object_scope_are_grounded.

     - move/nlf_conformsP=> [fld Hlook /and3P [/orP [Hobj | Habs] _]];
       rewrite /queries_conform Hlook /= => /and3P [Hne Hqsc _] Hg; apply/andP.
       * split.
           by apply/orP; left; apply: (are_grounded_in_object_scope_are_fields schema fld.(return_type)).
           by apply: (IH fld.(return_type)).

       * split.
           by apply/orP; apply: (are_grounded_in_abstract_scope_are_any schema fld.(return_type)).
           by apply: (IH fld.(return_type)).
 
      - move/nf_conformsP=> [fld Hlook /and3P [/orP [Hobj | Habs] _]];
       rewrite /queries_conform Hlook /= => /and3P [Hne Hqsc _] Hg; apply/andP.
       * split.
           by apply/orP; left; apply: (are_grounded_in_object_scope_are_fields schema fld.(return_type)).
           by apply: (IH fld.(return_type)).

       * split.
           by apply/orP; apply: (are_grounded_in_abstract_scope_are_any schema fld.(return_type)).
           by apply: (IH fld.(return_type)).
   Qed.*)

   Lemma grounded2_are_fields_in_object_scope :
     forall ty qs,
       is_object_type s ty ->
       are_grounded2 ty qs ->
       all is_field qs.
   Proof.
      apply (is_grounded2_elim
              (fun ty q b => true)
              (fun ty qs b =>
                 is_object_type s ty ->
                 b ->
                 all is_field qs)) => //.
      - by intros => /=; case/and3P: H2 => *; apply_andP; apply: H0.
      - by intros; rewrite H1 in Heq.
   Qed.


   Lemma are_grounded2_are_grounded :
     forall queries ty,
       are_grounded2 ty queries ->
       are_grounded queries.
   Proof.
     apply (is_grounded_elim 
              (fun q b =>
                 forall ty,
                   is_grounded2 ty q ->
                   b)
              (fun qs b =>
                 forall ty,
                   is_object_type s ty ->
                   are_grounded2 ty qs ->
                   b)
              (fun qs b =>
                 forall ty,
                   is_object_type s ty = false ->
                   are_grounded2 ty qs ->
                   b)
              (fun qs b =>
                 forall ty,
                   are_grounded2 ty qs ->
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
       * have : forall q, q.(is_inline_fragment) -> q.(is_field) = false by case.
         by move/(_ q Htype) ->; apply_andP; [apply : (IHq ty) | apply: (IHinls ty)].
   Qed.

   
  Equations are_similar (q1 q2 : @Query Name Vals) : bool :=
    {
      are_similar (InlineFragment t _) (InlineFragment t' _) := t == t';
      are_similar (InlineFragment _ _) _ := false;
      are_similar _ (InlineFragment _ _) := false;
      are_similar q1 q2 := ((qresponse_name q1 _) == (qresponse_name q2 _)) && ((qargs q1 _) == (qargs q2 _))
    }.
   
  Equations? are_non_redundant (queries : seq (@Query Name Vals)) : bool
    by wf (queries_size queries) :=
    {
      are_non_redundant [::] := true;
      
      are_non_redundant (hd :: tl) :=
        [&& all (fun q => ~~are_similar q hd) tl,
         are_non_redundant hd.(qsubqueries) &
         are_non_redundant tl]
    }.                 
  Proof.
    all: do [case: hd are_non_redundant; intros; simp query_size; ssromega].
  Qed.
  
  Definition is_non_redundant query :=
    are_non_redundant query.(qsubqueries).
  




  
End NRGTNF.

Arguments is_grounded [Name Vals].
Arguments are_grounded_fields [Name Vals].
Arguments are_grounded_inlines [Name Vals].
Arguments are_grounded [Name Vals].
Arguments is_grounded2 [Name Vals].
Arguments are_grounded2 [Name Vals].
Arguments are_non_redundant [Name Vals].
Arguments is_non_redundant  [Name Vals].

Arguments are_similar [Name Vals].