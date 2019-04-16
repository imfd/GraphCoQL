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

Section NRGTNF.

  Variables Name Vals : ordType.
  
  Implicit Type schema : @wfSchema Name Vals.
  Implicit Type queries : seq (@Query Name Vals).
  Implicit Type query : @Query Name Vals.
  Notation is_field := (@is_field Name Vals).
  Notation is_inline_fragment := (@QueryAux.is_inline_fragment Name Vals).

  
  
  Equations is_in_normal_form schema (query : @Query Name Vals) : bool :=
    {
      is_in_normal_form schema (NestedField _ _ ϕ) := (all is_field ϕ || all is_inline_fragment ϕ)
                                                       && all (is_in_normal_form schema) ϕ;
      is_in_normal_form schema (NestedLabeledField _ _ _ ϕ) := (all is_field ϕ || all is_inline_fragment ϕ)
                                                                && all (is_in_normal_form schema) ϕ;
      is_in_normal_form schema (InlineFragment t ϕ) := [&& (is_object_type schema t), (all is_field ϕ) & all (is_in_normal_form schema) ϕ];
      is_in_normal_form _ _ := true
    }.


  Definition are_in_normal_form schema (queries : seq (@Query Name Vals)) : bool :=
    (all is_field queries || all is_inline_fragment queries) && all (is_in_normal_form schema) queries.


  Lemma are_in_normal_form_E schema queries :
    are_in_normal_form schema queries ->
    (all is_field queries \/ all is_inline_fragment queries) /\ all (is_in_normal_form schema) queries.
  Proof.
    rewrite /are_in_normal_form.
    by move/andP=> [/orP H H'].
  Qed.

  Lemma are_in_normal_form_fields_inv schema queries :
    all is_field queries ->
    all (is_in_normal_form schema) queries ->
    are_in_normal_form schema queries.
  Proof.
    move=> Hf Hnf; rewrite /are_in_normal_form.
    by apply/andP; split; [apply/orP; left|].
  Qed.

  Lemma all_inlines_shape queries :
    all is_inline_fragment queries ->
    forall query, query \in queries ->
                       exists t ϕ, query = InlineFragment t ϕ.
  Proof.
    move=> /allP H q Hin.
    move: (H q Hin) => {Hin}.
    funelim (is_inline_fragment q) => // _.
    by exists s5; exists l1.
  Qed.


   Equations is_grounded_2 schema (type_in_scope : @NamedType Name) (query : @Query Name Vals) : bool :=
    {
      is_grounded_2 schema type_in_scope (NestedField f _ φ)
        with lookup_field_in_type schema type_in_scope f :=
        {
        | Some fld := are_grounded_2 schema fld.(return_type) φ;
        | _ := false
        };

      is_grounded_2 schema type_in_scope (NestedLabeledField _ f _ φ)
        with lookup_field_in_type schema type_in_scope f :=
        {
        | Some fld := are_grounded_2 schema fld.(return_type) φ;
        | _ := false
        };

      is_grounded_2 schema type_in_scope(InlineFragment t ϕ) := [&& (is_object_type schema t), (all is_field ϕ) & all (is_grounded_2 schema t) ϕ];
      
      is_grounded_2 _ _ _ := true
    }
   where
   are_grounded_2 schema (type_in_scope : @NamedType Name) (queries : seq (@Query Name Vals)) : bool :=
     {
       are_grounded_2 _ _ [::] := true;
       are_grounded_2 schema ty (hd :: tl)
         with is_object_type schema ty :=
         {
         | true := [&& is_field hd, is_grounded_2 schema ty hd & are_grounded_2 schema ty tl];
         | _ with get_possible_types schema ty != fset0 :=
             {
             | true := [&& is_inline_fragment hd, is_grounded_2 schema ty hd & are_grounded_2 schema ty tl];
             | _ := [&& is_field hd, is_grounded_2 schema ty hd & are_grounded_2 schema ty tl]
             }
         }
     }.


   Lemma are_grounded_2E schema ty queries :
     are_grounded_2 schema ty queries = [|| (is_object_type schema ty && all is_field queries),
                                         [&& ~~is_object_type schema ty,
                                          get_possible_types schema ty != fset0 &
                                          all is_inline_fragment queries] |
                                         [&& ~~is_object_type schema ty,
                                          get_possible_types schema ty == fset0 &
                                          all is_field queries]]
                                         
                                          && all (is_grounded_2 schema ty) queries.
   Proof.
     elim: queries => //=.
     - case is_object_type => //=.
         by case get_possible_types.
     - move=> hd tl IH.
       case Hobj: is_object_type => //=.
       by rewrite IH Hobj !orbF /=  [is_grounded_2 _ _ _ && _]andbCA andbA.
       case: eqP => //= /eqP Heq;
       rewrite IH Heq /= ?andbF ?orFb Hobj /=.
       * by rewrite -[RHS]andbA [all is_field tl && _ in RHS]andbCA.
       * move/negbTE: Heq => -> /=; rewrite ! orbF. 
         by rewrite -[RHS]andbA [all is_inline_fragment tl && _ in RHS]andbCA.
   Qed.

   
   Lemma are_grounded_2E2 schema ty queries :
     all (query_conforms schema ty) queries ->
     are_grounded_2 schema ty queries = ((is_object_type schema ty && all is_field queries) ||
                                         (is_abstract_type schema ty && all is_inline_fragment queries))
                                          && all (is_grounded_2 schema ty) queries.
   Proof.
     elim: queries => //.
     - case Hobj: is_object_type => //=.
   Admitted.  


   Lemma are_grounded_2_cons schema ty q qs :
     are_grounded_2 schema ty (q :: qs) ->
     is_grounded_2 schema ty q && are_grounded_2 schema ty qs.
   Proof.
     rewrite are_grounded_2_equation_2.
     case is_object_type => //=; [by move/and3P=> [_ Hg Hgs]; apply/andP; split |].
     by case get_possible_types => //= [| hd tl] /and3P [_ Hg Hgs]; apply/andP; split.
   Qed.
   
   Lemma are_grounded_2_cat schema ty qs qs' :
     are_grounded_2 schema ty qs /\  are_grounded_2 schema ty qs' <->
     are_grounded_2 schema ty (qs ++ qs').
   Proof.
     split.
     - elim: qs qs' => [qs' | hd tl IH qs'] //=.
       * by case.

       * case Hobj : is_object_type => //=.
         + move=> [/and3P [Hf Hg Hgs] Hgs'];
           apply/and3P; split=> //;
             by apply: IH.

         + case get_possible_types => //= [| hd' tl'] [/and3P [Hty Hg Hgs] Hgs']; apply/and3P; split=> //;
             by apply: IH.
     - elim: qs qs' => // hd tl IH qs'.
       rewrite cat_cons /=.
       case is_object_type => /=.
       
       * move=> /= /and3P [Hty Hg Hgs].
         move: (IH qs' Hgs) => [Htlg Hgs'].
           by split=> //; apply/and3P; split.

       * case get_possible_types => //= [| hd' tl'];
         move/and3P=> [Hty Hg Hgs]; 
         move: (IH qs' Hgs) => [Htlg Hgs'];
           by split=> //; apply/and3P; split.
                       
   Qed.
   
         
   Ltac all_cons := rewrite {1}/all -/(all _ _) => /andP; case.
  
   Lemma are_grounded_in_object_scope_are_fields schema ty queries :
     is_object_type schema ty ->
     are_grounded_2 schema ty queries ->
     all is_field queries.
   Proof.
     move=> Hobj.
     by rewrite are_grounded_2E Hobj /= orbF => /andP [H _].
   Qed.

  
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
   
   Lemma is_grounded_2_in_normal_form schema query :
     forall ty,
       query_conforms schema ty query ->
       is_grounded_2 schema ty query ->
       is_in_normal_form schema query.
   Proof.
     elim query using Query_ind with
         (Pl := fun qs =>
                 forall ty,
                   all (query_conforms schema ty) qs ->
                   are_grounded_2 schema ty qs ->
                   all (is_in_normal_form schema) qs) => // [f α | l f α | t | hd IHhd tl IHtl ]; last first.
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
   Qed.

   Lemma are_grounded_2_in_normal_form schema queries :
     forall ty,
       all (query_conforms schema ty) queries ->
       are_grounded_2 schema ty queries ->
       are_in_normal_form schema queries.
   Proof.
     elim: queries => // hd tl IH ty.
     all_cons => [Hqc Hqsc].
     rewrite are_grounded_2_equation_2; case Hobj: is_object_type => /=;
     [| case eqP => //= /eqP Heq];
     move/and3P=> [Hf Hg Hgs];
     move: (IH ty Hqsc Hgs); rewrite /are_in_normal_form => /andP [_ Hnfs];
     move: Hgs; rewrite are_grounded_2E Hobj /= ?orbF => /andP [Hty Hgs];
     rewrite /are_in_normal_form;
     apply/and3P; split => //=.
     - apply/orP; left; apply/andP; split=> //.
       by apply: (is_grounded_2_in_normal_form schema hd ty).
     - apply/orP; left; apply/andP; split=> //.
         by move: Hty; rewrite Heq.
       by apply: (is_grounded_2_in_normal_form schema hd ty).

     - apply/orP; right; apply/andP; split=> //.
         by move: Hty; move/negbTE: Heq => -> /=; rewrite orbF.
       by apply: (is_grounded_2_in_normal_form schema hd ty).
   Qed.


     
    
  Lemma inlines_in_normal_form_have_object_guards schema queries :
    all is_inline_fragment queries ->
    all (is_in_normal_form schema) queries ->
    forall query, query \in queries ->
                       exists t ϕ, query = InlineFragment t ϕ /\ is_object_type schema t.
  Proof.
    move=> Hinlines Hnf q Hin.
    move: (all_inlines_shape queries Hinlines q Hin).
    case=> t; case=> ϕ Heq.    
    move/allP: Hnf; move/(_ q Hin).
    rewrite Heq.
    rewrite is_in_normal_form_equation_5.
    move/and3P=> [Hobj _ _].
      by exists t; exists ϕ.
  Qed.

 
  
  
  Equations is_non_redundant (query : @Query Name Vals) : bool :=
    {
      is_non_redundant (NestedField _ _ φ) := are_non_redundant φ;
      is_non_redundant (NestedLabeledField _ _ _ φ) := are_non_redundant φ;
      is_non_redundant (InlineFragment _ φ) := are_non_redundant φ;
      is_non_redundant _ := true
                             
    }
  where are_non_redundant (queries : seq (@Query Name Vals)) : bool :=
    {
      are_non_redundant [::] := true;
      are_non_redundant (hd :: tl)
        with has (partial_query_eq hd) tl :=
        {
        | true := false;
        | _ := (is_non_redundant hd) && are_non_redundant tl
             
        }
    }.

  



  Lemma sub_nf schema ty ϕ ϕ' :
    ϕ = [:: InlineFragment ty ϕ'] ->
    are_in_normal_form schema ϕ ->
    all is_field ϕ' /\ all (is_in_normal_form schema) ϕ'.
  Proof.
    move=> -> H.
    move: (are_in_normal_form_E _ _ H) => [_ Hnf].
    move: Hnf; rewrite {1}/all is_in_normal_form_equation_5.
      by move/andP=> [/and3P [Hobj Hfld H'] _].
  Qed.

  




  
End NRGTNF.

Arguments is_in_normal_form [Name Vals].
Arguments are_in_normal_form [Name Vals].
Arguments is_grounded_2 [Name Vals].
Arguments are_grounded_2 [Name Vals].
Arguments are_non_redundant [Name Vals].
Arguments is_non_redundant  [Name Vals].
Arguments are_grounded_in_object_scope_are_fields [Name Vals].
Arguments are_grounded_2_in_normal_form [Name Vals].
Arguments are_grounded_in_abstract_scope_are_any [Name Vals].