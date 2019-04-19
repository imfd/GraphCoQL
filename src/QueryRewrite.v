
From mathcomp Require Import all_ssreflect.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Asymmetric Patterns.

From Equations Require Import Equations.

From extructures Require Import ord fset fmap.

Require Import Schema.
Require Import SchemaAux.
Require Import SchemaWellFormedness.
Require Import Query.
Require Import QueryAux.
Require Import QueryConformance.

Require Import Graph.
Require Import GraphAux.
Require Import GraphConformance.

Require Import NRGTNF.

Require Import ValidFragments.

Require Import Ssromega.

Require Import SeqExtra.

Section QueryRewrite.

  Variables Name Vals : ordType.
  Implicit Type schema : @wfSchema Name Vals.
  Implicit Type query : @Query Name Vals.

  Notation is_field := (@QueryAux.is_field Name Vals).
  Notation is_inline_fragment := (@QueryAux.is_inline_fragment Name Vals).


  

  Ltac orL := apply/orP; left.
  Ltac orR := apply/orP; right.
  
  Ltac apply_andP := apply/andP; split=> //.
  Ltac apply_and3P := apply/and3P; split=> //.
  Ltac are_in_normal_form := rewrite /are_in_normal_form => /andP; case.
  Ltac all_cons := rewrite {1}/all -/(all _ _) => /andP; case.
  Ltac query_conforms := simp query_conforms; try move/and5P; try apply/and5P.

  Open Scope fset.

  Equations try_inline_query query (possible_types : seq (@NamedType Name)) : seq (@Query Name Vals) :=
    {
      try_inline_query q types with types != [::] :=
        {
        | true := [seq InlineFragment ty [:: q] | ty <- types];
        | _ := [:: q]
        }
    }.
      
  Equations normalize schema : @NamedType Name -> @Query Name Vals -> seq (@Query Name Vals) :=
    {
      normalize _ type_in_scope (SingleField f α)
        with is_object_type schema type_in_scope :=
        {
        | true := [:: SingleField f α];
        | _ := try_inline_query (SingleField f α) (get_possible_types schema type_in_scope)
        };

       normalize schema  type_in_scope (LabeledField l f α)
        with is_object_type schema type_in_scope :=
        {
        | true := [:: LabeledField l f α];
        | _ := try_inline_query (LabeledField l f α) (get_possible_types schema type_in_scope)
        };
      
                                                                                    
       normalize schema  type_in_scope (NestedField f α φ)
         with lookup_field_in_type schema type_in_scope f :=
         {
          | Some fld
              with is_object_type schema type_in_scope :=
              {
              | true := [:: NestedField f α (normalize__φ schema fld.(return_type) φ)];
              | _ := let normalized_head := normalize__φ schema fld.(return_type) φ in
                    try_inline_query (NestedField f α normalized_head) (get_possible_types schema type_in_scope)
              };
          | _ => [::]
         };
        


      normalize schema  type_in_scope (NestedLabeledField l f α φ)
       with lookup_field_in_type schema type_in_scope f :=
         {
          | Some fld
              with is_object_type schema type_in_scope :=
              {
              | true := [:: NestedLabeledField l f α (normalize__φ schema fld.(return_type) φ)];
              | _ := let normalized_head := normalize__φ schema fld.(return_type) φ in
                    try_inline_query (NestedLabeledField l f α normalized_head) (get_possible_types schema type_in_scope)
            };
          | _ => [::]
         };
              
              
      normalize schema  type_in_scope (InlineFragment t φ)
        with is_object_type schema type_in_scope, is_object_type schema t :=
        {
        | true | _ := (normalize__φ schema type_in_scope φ);
        | false | true := [:: InlineFragment t (normalize__φ schema t φ)];
        | false | false := (normalize__φ schema type_in_scope φ)     
        }
    }
  where
   normalize__φ schema (type_in_scope : @NamedType Name) (queries : seq (@Query Name Vals))  : seq (@Query Name Vals) :=
    {
      normalize__φ _ _ [::] := [::];
      normalize__φ schema type_in_scope (query :: queries) :=
        (normalize schema type_in_scope query) ++ (normalize__φ schema  type_in_scope queries)
      
    }.


  Lemma normalize__φ_cat schema type_in_scope qs qs' :
    normalize__φ schema type_in_scope qs ++ normalize__φ schema type_in_scope qs' =
    normalize__φ schema type_in_scope (qs ++ qs').
  Proof.
    elim: qs qs' => // hd tl IH qs'.
    by rewrite cat_cons ! normalize__φ_equation_2 -catA (IH qs').
  Qed.

 

 
  Lemma normalize_in_object_scope_are_fields :
    forall schema type_in_scope query,
    query_conforms schema type_in_scope query ->
    has_valid_fragments schema type_in_scope query ->
    is_object_type schema type_in_scope ->
    all is_field (normalize schema type_in_scope query).
  Proof.
    apply (normalize_elim
             (fun s type_in_scope query nq =>
                 query_conforms s type_in_scope query ->
                 has_valid_fragments s type_in_scope query ->
                 is_object_type s type_in_scope ->
                 all is_field (normalize s type_in_scope query))
             (fun schema ty qs nqs =>
                all (query_conforms schema ty) qs ->
                all (has_valid_fragments schema ty) qs ->
                is_object_type schema ty ->
                all is_field (normalize__φ schema ty qs))) => //;
      move=> schema ty.
   
    all: do ?[intros; simp normalize; rewrite H1 /=; simp is_field].
    - move=> f α φ Hlook.
      by simp normalize; rewrite Hlook /=.
    - move=> f rty α φ IH Hobj Hlook Hqc Hv _.
        by simp normalize; rewrite Hlook /= Hobj.
    - by move=> f rty α φ H Hcontr _ _ _ Hobj; rewrite Hcontr in Hobj.
    - move=> l f α φ Hlook.
      by simp normalize; rewrite Hlook.
    - move=> l rty f α φ IH Hobj Hlook Hqc Hv _.
        by simp normalize; rewrite Hlook /= Hobj.
    - by move=> l rty f α φ H Hcontr _ _ _ Hobj; rewrite Hcontr in Hobj.

    - move=> b t φ IH Hobj Hinobj Hqc Hval _.
      simp normalize; rewrite Hobj /= Hinobj /=.
      move: Hqc; query_conforms; move=> [_ _ _ Hqsc _].
      move: Hval; simp has_valid_fragments; rewrite Hinobj /=; move/andP=> [/eqP Heq Hvs].
      by rewrite Heq in Hqsc; apply: IH.
    - by move=> t φ _ _ Hcontr _ _ Hobj; rewrite Hcontr in Hobj.
    - by move=> t φ _ _ Hcontr _ _ Hobj; rewrite Hcontr in Hobj.
            
    - move=> hd tl IH IH'.
      rewrite {1}/all -/(all _ _) => /andP [Hqc Hqsc].
      rewrite {1}/all -/(all _ _) => /andP [Hv Hvs] Hobj.
      rewrite normalize__φ_equation_2 all_cat; apply/andP.
        by split; [apply: IH | apply: IH'].
  Qed.
  
 
    
  Lemma normalize__φ_in_object_scope_are_fields :
    forall schema ty qs,
      all (query_conforms schema ty) qs ->
      all (has_valid_fragments schema ty) qs ->
      is_object_type schema ty ->
      all is_field (normalize__φ schema ty qs).
  Proof.
    move=> schema ty.
    elim=> // hd tl IH.
    rewrite {1}/all -/(all _ _) => /andP [Hqc Hqsc].
    rewrite {1}/all -/(all _ _) => /andP [Hv Hvs] Hobj.
    rewrite normalize__φ_equation_2 all_cat; apply/andP; split.
    by apply: normalize_in_object_scope_are_fields.
      by apply IH.
  Qed.

  Lemma imfset_inline_are_inlines qs sbq :
    all is_inline_fragment ((fun q => InlineFragment q sbq) @: qs).
  Proof.
    elim/fset_ind: qs => //=.
    - by rewrite imfset0.
    - move=> x tl Hnin IH.
      by rewrite imfsetU all_fsetU imfset1; apply_andP.
  Qed.

  
  Lemma normalize__φ_in_abstract_scope_are_any :
    forall schema ty qs,
      all (query_conforms schema ty) qs ->
      all (has_valid_fragments schema ty) qs ->
      is_abstract_type schema ty ->
      (all is_field (normalize__φ schema ty qs)) \/ all is_inline_fragment (normalize__φ schema ty qs).
  Proof.
  Admitted.
  (*
    apply (normalize_elim
             (fun schema ty q nq =>
                query_conforms schema ty q ->
                has_valid_fragments schema ty q ->
                is_abstract_type schema ty ->
                all is_inline_fragment (normalize schema ty q))
             (fun schema ty qs nqs =>
                 all (query_conforms schema ty) qs ->
                 all (has_valid_fragments schema ty) qs ->
                 is_abstract_type schema ty ->
                 all is_inline_fragment (normalize__φ schema ty qs)));
      move=> schema ty.
      all: do ?[by intros; move: (abstract_type_N_obj H1) => Hcontr; rewrite Hcontr in Heq].
      all: do ?[by intros; rewrite /query_conforms in H; case Hlook : lookup_field_in_type in H; rewrite Hlook in Heq].
      all: do ?[by intros; simp normalize; rewrite Heq /=; apply: imfset_inline_are_inlines].
      all: do ?[by intros; move: (abstract_type_N_obj H2) => Hcontr; rewrite Heq in Hcontr].
      all: do ?[by intros; simp normalize; rewrite Heq0 /= Heq /=; apply: imfset_inline_are_inlines].
      intros; simp normalize; rewrite Heq /=.
      simp try_inline_query.
      case: eqP => //=.
    - by intros; move: (abstract_type_N_obj H2) => Hcontr; rewrite Hcontr in Heq0.
    - by intros; simp normalize; rewrite Heq Heq0 /=.
    - intros; simp normalize; rewrite Heq Heq0 /=.
      move: H0; query_conforms.
      move=> [_ _ _ Hqc].
      move: H1; simp has_valid_fragments; rewrite Heq0 /= => /andP [/orP [/eqP Heq' | Hcontr] Hv]; last first.
      by rewrite Hcontr in Heq.
      by apply: H; rewrite -Heq' in H2 * => //.
      
    - move=> hd tl IH IH'.
      rewrite {1}/all -/(all _ _) => /andP [Hqc Hqsc].
      rewrite {1}/all -/(all _ _) => /andP [Hv Hvs] Hobj.
      by rewrite normalize__φ_equation_2 all_cat; apply/andP; split; [apply: IH | apply: IH'].
    
  Qed. *)

  
   Lemma normalize_in_abstract_scope_are_any :
    forall schema ty q,
      query_conforms schema ty q ->
      has_valid_fragments schema ty q ->
      is_abstract_type schema ty ->
      all is_field (normalize schema ty q) \/ all is_inline_fragment (normalize schema ty q).
   Proof.
   Admitted.
     (*
    move=> schema ty; case; intros; simp normalize.
    all: do ?[by move: (abstract_type_N_obj H1) => -> /=; apply: imfset_inline_are_inlines].
    all: do ?[by case: lookup_field_in_type => [fld|] //=;
              move: (abstract_type_N_obj H1) => -> /=; apply: imfset_inline_are_inlines].
           
    move: H0; simp has_valid_fragments.
    move: (abstract_type_N_obj H1) => Hnobj.
    rewrite Hnobj /= => /andP [/orP [/eqP Heq | Hobj] Hv].
    move: H; query_conforms.
    move=> [_ _ _ Hqsc].
    rewrite Heq Hnobj in Hqsc Hv *.
      by apply: normalize__φ_in_abstract_scope_are_inlines.
        by rewrite Hobj /=; apply/andP.
  Qed.
   *)

  
  Lemma map_inline_are_grounded_in_interface schema ty sbq :
    is_interface_type schema ty ->
    all is_field sbq ->
    all (is_grounded_2 schema ty) sbq -> 
    all (is_grounded_2 schema ty) [seq InlineFragment t sbq | t <- (get_possible_types schema ty)].
  Proof.
    move=> Hintf Hflds Hg.
    move: (@in_possible_types_is_object Name Vals schema ty).
    elim: get_possible_types => //= hd tl IH Hin.
    apply_andP.
  Admitted.
      
  
      
  Lemma fset1UNfset0 {A : ordType} (x : A) (xs : {fset A}) :
    x |: xs != fset0.
  Proof.
    by rewrite /fsetU /= fset_N_fset0. 
  Qed.

  Lemma normalize_is_grounded :
    forall schema ty query,
      query_conforms schema ty query ->
      has_valid_fragments schema ty query ->
      are_grounded_2 schema ty (normalize schema ty query).
  Proof.
    apply (normalize_elim
             (fun schema type_in_scope query qn =>
                query_conforms schema type_in_scope query ->
                has_valid_fragments schema type_in_scope query ->
                are_grounded_2 schema type_in_scope qn)
             (fun schema type_in_scope queries qsn =>
                all (query_conforms schema type_in_scope) queries ->
                all (has_valid_fragments schema type_in_scope) queries ->
                are_grounded_2 schema type_in_scope qsn))
    => // schema.
    
    all: do?[by intros => /=; rewrite Heq /=; apply/and3P; split].

    - intros => /=; rewrite are_grounded_2E Heq /=; apply_andP.

      (* elim/fset_ind: (get_possible_types schema s) => //= hd tl Hnin IH.
      orL; apply_andP.
        by apply: fset1UNfset0.
        simp try_inline_query; rewrite fset1UNfset0 /=.
        by apply: imfset_inline_are_inlines.
      move: (@in_possible_types_is_object Name Vals schema s).
      rewrite get_possible_types_interfaceE //. *)
      Admitted.
      (*
      elim/fset_ind: (implementation schema s); [by rewrite imfset0|].
      move=> x tl Hnin IH Hin.
      rewrite imfsetU all_fsetU; apply_andP.
      rewrite imfset1 /=; apply_andP; simp is_grounded_2; apply_andP.
        by have/Hin: x \in x |: tl by rewrite in_fsetU1; orL.
          by apply: IH => t Htlin; apply: Hin; rewrite in_fsetU1; orR.
    have/scope_is_obj_or_abstract_for_field : is_field (SingleField s0 f) by [].
      by move/(_ schema s H) => [Hcontr |//]; rewrite Heq in Hcontr.

    - intros => /=; rewrite are_grounded_2E Heq /=; apply_andP.
    apply: imfset_inline_are_inlines.
    move: (@in_possible_types_is_object Name Vals schema s).
    rewrite get_possible_types_interfaceE //.
    elim/fset_ind: (implementation schema s); [by rewrite imfset0|].
    move=> x tl Hnin IH Hin.
    rewrite imfsetU all_fsetU; apply_andP.
    rewrite imfset1 /=; apply_andP; simp is_grounded_2; apply_andP.
      by have/Hin: x \in x |: tl by rewrite in_fsetU1; orL.
      by apply: IH => t Htlin; apply: Hin; rewrite in_fsetU1; orR.
    have/scope_is_obj_or_abstract_for_field : is_field (LabeledField s1 s2 f0) by [].
      by move/(_ schema s H) => [Hcontr |//]; rewrite Heq in Hcontr.


     
  
    all: do?[intros => /=; rewrite Heq /=; apply/and3P; split=> //;
             simp is_grounded_2; rewrite Heq0 /=;
             move: H0; rewrite /query_conforms Heq0 => /and4P [_ _ _ Hqsc];
             move: H1; simp has_valid_fragments; rewrite Heq0 /= => Hv;
                                                                     by apply: H].
     - intros => /=; rewrite are_grounded_2E Heq /=; apply_andP.
    apply: imfset_inline_are_inlines.
    move: (@in_possible_types_is_object Name Vals schema s).
    rewrite get_possible_types_interfaceE //.
    elim/fset_ind: (implementation schema s); [by rewrite imfset0|].
    move=> x tl Hnin IH Hin.
    rewrite imfsetU all_fsetU; apply_andP.
    rewrite imfset1 /=; apply_andP; simp is_grounded_2; apply_andP.
      by have/Hin: x \in x |: tl by rewrite in_fsetU1; orL.
      apply_andP; rewrite all_seq1; simp is_grounded_2.

  Admitted. *)
  (*rewrite Heq /=.
      by apply: IH => t Htlin; apply: Hin; rewrite in_fsetU1; orR.
    have/scope_is_obj_or_abstract_for_field : is_field (LabeledField s1 s2 f0) by [].
      by move/(_ schema s H) => [Hcontr |//]; rewrite Heq in Hcontr.

      

    - intros => /=
    - move=> t b ty φ IH Ht Hscope Hqc Hv.
      move: Hqc; rewrite /query_conforms => /and4P [_ _ _ Hqsc].
      move: Hv; simp has_valid_fragments; rewrite Hscope /= => /andP [/eqP Htyeq Hv].
      rewrite Htyeq in Hqsc.
        by apply: IH.

    -  move=> t ty φ IH Ht Hscope Hqc Hv /=.
       rewrite Hscope /=; apply/and3P; split=> //.
       simp is_grounded_2.
       apply_andP.
       move: Hqc; query_conforms.
       move=> [_ _ _ Hqsc].
       move: Hv; simp has_valid_fragments; rewrite Hscope /= => /andP [/orP [/eqP Hcontr | _] Hv].
         by rewrite Hcontr in Ht; rewrite Ht in Hscope.
       move: (IH Hqsc Hv); rewrite are_grounded_2E => /andP [/orP [/andP [_ Hf] | /andP [Hcontr _]] Hg].
       apply_andP.
         by rewrite Ht in Hcontr.

    - move=> t ty φ IH Ht Hscope.
      query_conforms; move=> [_ _ _ Hqsc].
      simp has_valid_fragments; rewrite Hscope /= => /andP [/orP [/eqP Heq | Hcontr] Hv].
        by rewrite Heq in Hv Hqsc; apply: IH.
        by rewrite Ht in Hcontr.

    - move=> ty hd tl IH IH'.
      all_cons => [Hqc Hqsc].
      all_cons => [Hv Hvs].
      by rewrite -are_grounded_2_cat; split; [apply: IH | apply: IH'].
  Qed.
  *)

  Lemma normalize__φ_are_grounded schema ty qs :
    all (query_conforms schema ty) qs ->
    all (has_valid_fragments schema ty) qs ->
    are_grounded_2 schema ty (normalize__φ schema ty qs).
  Proof.
    elim: qs => //= hd tl IH /andP [Hqc Hqsc] /andP [Hv Hvs].
    rewrite -are_grounded_2_cat.
    split.
      by apply: normalize_is_grounded.
    by apply: IH.
  Qed.
  
  Lemma normalize_in_normal_form :
    forall schema type_in_scope query,
      query_conforms schema type_in_scope query ->
      has_valid_fragments schema type_in_scope query ->
      are_in_normal_form schema (normalize schema type_in_scope query).
  Proof.
    apply (normalize_elim
             (fun schema type_in_scope query qn =>
                query_conforms schema type_in_scope query ->
                has_valid_fragments schema type_in_scope query ->
                are_in_normal_form schema (normalize schema type_in_scope query))
             (fun schema type_in_scope queries qsn =>
                all (query_conforms schema type_in_scope) queries ->
                all (has_valid_fragments schema type_in_scope) queries ->
                are_in_normal_form schema (normalize__φ schema type_in_scope queries))) => //;
    move=> schema; [ move=> ty f α Hobj Hqc Hv
                  | move=> ty f α Hobj Hqc Hv
                  | move=> ty l f α Hobj Hqc Hv
                  | move=> ty l f α Hobj Hqc Hv
                  | move=> ty f α φ Hlook
                  | move=> ty f fld α φ IH Hobj Hlook Hqc Hv
                  | move=> ty f fld α φ IH Hobj Hlook Hqc Hv
                  | move=> ty l f α φ Hlook
                  | move=> ty l f fld α φ IH Hobj Hlook Hqc Hv
                  | move=> ty l f fld α φ IH Hobj Hlook Hqc Hv
                  | move=> t b ty φ IH Hobj Hinobj Hqc Hv
                  | move=> t ty φ IH Hinty Hobj Hqc Hv
                  | move=> t ty φ IH Hinty Hscope Hqc Hv
                  | move=> ty q qs IH IH'
                  ];
          rewrite ?/are_in_normal_form;
          simp normalize.
    Admitted.
    (*
    - by rewrite Hobj; apply/andP; split.
    - rewrite Hobj /=.
      apply/andP; split => //.
      *  apply/orP; right. apply/allP=> x /mapP [t Hin ->] /=.
           by simp is_inline_fragment.
      *  apply/allP => x /mapP [t Hpty ->].
         simp is_in_normal_form.
         apply/and3P; split => //=.
         move: (type_in_scope_N_scalar_enum Hqc) => [Hcontr | Hintf | Hunion].
      + by rewrite Hobj in Hcontr.
      + rewrite (get_possible_types_interfaceE Hintf) in Hpty.
        by apply: (in_implementation_is_object Hpty).
      + rewrite (get_possible_types_unionE Hunion) in Hpty.
          by apply: (in_union_is_object Hpty).

    - by rewrite Hobj; apply/andP; split.

    - rewrite Hobj /=.
      apply/andP; split => //.
      *  apply/orP; right. apply/allP=> x /mapP [t Hin ->] /=.
           by simp is_inline_fragment.
      *  apply/allP => x /mapP [t Hpty ->].
         simp is_in_normal_form.
         apply/and3P; split => //=.
         move: (type_in_scope_N_scalar_enum Hqc) => [Hcontr | Hintf | Hunion].
      + by rewrite Hobj in Hcontr.
      + rewrite (get_possible_types_interfaceE Hintf) in Hpty.
        by apply: (in_implementation_is_object Hpty).
      + rewrite (get_possible_types_unionE Hunion) in Hpty.
          by apply: (in_union_is_object Hpty).

    - by rewrite Hlook.
    - move: Hv; simp has_valid_fragments; rewrite Hlook /= Hobj /= => Hvals.
      apply/and3P; split => //.
      simp is_in_normal_form.
      rewrite -/(are_in_normal_form _ _).
      apply: IH => //.
      by move: Hqc; rewrite {1}/query_conforms Hlook => /and4P [_ _ _ H].

    - move: Hv; simp has_valid_fragments; rewrite Hlook /= Hobj /= => Hvals.
      apply/andP; split => //.
      * apply/orP; right.
          by apply/allP => x /mapP [t Hin ->].
      * apply/allP=> x /mapP [t Hin ->]; simp is_in_normal_form.
        move: (type_in_scope_N_scalar_enum Hqc) => [Hcontr | Hintf | Hunion].
        + by rewrite Hobj in Hcontr.
        + rewrite (get_possible_types_interfaceE Hintf) in Hin.
          apply/and3P; split=> //.
            by apply: (in_implementation_is_object Hin).
            rewrite all_seq1; simp is_in_normal_form.
            rewrite -/(are_in_normal_form _ _).
            apply: IH => //.
              by move: Hqc; rewrite {1}/query_conforms Hlook => /and4P [_ _ _ H].

        + rewrite (get_possible_types_unionE Hunion) in Hin.     
          move/in_union_is_object: Hin => Hobj'.
          apply/and3P; split=> //.
          rewrite all_seq1; simp is_in_normal_form.
            rewrite -/(are_in_normal_form _ _).
            apply: IH => //.
              by move: Hqc; rewrite {1}/query_conforms Hlook => /and4P [_ _ _ H].

    - by rewrite Hlook.
    - move: Hv; simp has_valid_fragments; rewrite Hlook /= Hobj /= => Hvals.
      apply/and3P; split => //.
      simp is_in_normal_form.
      rewrite -/(are_in_normal_form _ _).
      apply: IH => //.
      by move: Hqc; rewrite {1}/query_conforms Hlook => /and4P [_ _ _ H].

    - move: Hv; simp has_valid_fragments; rewrite Hlook /= Hobj /= => Hvals.
      apply/andP; split => //.
      * apply/orP; right.
          by apply/allP => x /mapP [t Hin ->].
      * apply/allP=> x /mapP [t Hin ->]; simp is_in_normal_form.
        move: (type_in_scope_N_scalar_enum Hqc) => [Hcontr | Hintf | Hunion].
        + by rewrite Hobj in Hcontr.
        + rewrite (get_possible_types_interfaceE Hintf) in Hin.
          apply/and3P; split=> //.
            by apply: (in_implementation_is_object Hin).
            rewrite all_seq1; simp is_in_normal_form.
            rewrite -/(are_in_normal_form _ _).
            apply: IH => //.
              by move: Hqc; rewrite {1}/query_conforms Hlook => /and4P [_ _ _ H].

        + rewrite (get_possible_types_unionE Hunion) in Hin.     
          move/in_union_is_object: Hin => Hobj'.
          apply/and3P; split=> //.
          rewrite all_seq1; simp is_in_normal_form.
            rewrite -/(are_in_normal_form _ _).
            apply: IH => //.
              by move: Hqc; rewrite {1}/query_conforms Hlook => /and4P [_ _ _ H].
    - rewrite Hobj Hinobj /=.
      rewrite -/(are_in_normal_form _ _).
      move: Hv. simp has_valid_fragments; rewrite Hinobj /= => /andP [/eqP Heq Hvs]. 
      apply: IH => //.
      rewrite Heq in Hqc.
      move: Hqc; query_conforms.
      by move=> [_ _ _ Hqsc].        
    - rewrite Hobj Hinty /=.
      apply/andP; split => //.
      apply/andP; split=> //.
      simp is_in_normal_form.
      move: Hqc; query_conforms.
      move=> [_ _ _ Hqsc].
      move: Hv; simp has_valid_fragments; rewrite Hobj /= => /andP [_ Hvs].
      apply/and3P; split=> //.
        by apply: normalize__φ_in_object_scope_are_fields.
      by move: (IH Hqsc Hvs); rewrite /are_in_normal_form => /andP [_ H].

    - rewrite Hscope Hinty /=.
      move: Hqc; query_conforms.
      move=> [_ _ _ Hqsc].
      move: Hv; simp has_valid_fragments; rewrite Hscope /= => /andP [/orP [/eqP Heq | Hcontr] Hv].     
      rewrite -/(are_in_normal_form _ _); apply: IH; rewrite Heq in Hqsc Hv => //.
      by rewrite Hcontr in Hinty.
        

    - rewrite {1}/all -/(all _ _) => /andP [Hqc Hqsc].
      rewrite {1}/all -/(all _ _) => /andP [Hv Hvs].
      
      move: (IH Hqc Hv) => Hnf {IH}.
      move: (IH' Hqsc Hvs) => Hnfs {IH'}.
      rewrite ! all_cat;  apply/andP; split; first last.
        by apply/andP; split; [move: Hnf | move: Hnfs]; rewrite /are_in_normal_form => /andP [_ H].
       
      case: q Hqc Hv Hnf => [f α | l f α | f α φ | l f α φ | t φ] Hqc Hv Hnf.
      * simp normalize; case Hobj : is_object_type => //=; apply/orP.
        + left.
          apply/andP=> //; split => //.
            by apply: normalize__φ_in_object_scope_are_fields.
        + right.
          apply/andP; split=> //.
            by apply/allP=> x /mapP [t H ->].
          move: (type_in_scope_N_obj_is_abstract Hqc Hobj) => Habs.
          by apply: normalize__φ_in_abstract_scope_are_inlines.
      * simp normalize; case Hobj : is_object_type => //=; apply/orP.
        + left.
          apply/andP=> //; split => //.
            by apply: normalize__φ_in_object_scope_are_fields.
        + right.
          apply/andP; split=> //.
            by apply/allP=> x /mapP [t H ->].
          move: (type_in_scope_N_obj_is_abstract Hqc Hobj) => Habs.
          by apply: normalize__φ_in_abstract_scope_are_inlines.
      * simp normalize; case Hlook: lookup_field_in_type => [fld|] //=.
          case Hobj : is_object_type => //=; apply/orP.
        + left.
          apply/andP=> //; split => //.
            by apply: normalize__φ_in_object_scope_are_fields.
        + right.
          apply/andP; split=> //.
            by apply/allP=> x /mapP [t H ->].
          move: (type_in_scope_N_obj_is_abstract Hqc Hobj) => Habs.
          by apply: normalize__φ_in_abstract_scope_are_inlines.
          move/nf_conformsP: Hqc => [fld Hcontr _].
          by rewrite Hcontr in Hlook.

      * simp normalize; case Hlook: lookup_field_in_type => [fld|] //=.
          case Hobj : is_object_type => //=; apply/orP.
        + left.
          apply/andP=> //; split => //.
            by apply: normalize__φ_in_object_scope_are_fields.
        + right.
          apply/andP; split=> //.
            by apply/allP=> x /mapP [t H ->].
          move: (type_in_scope_N_obj_is_abstract Hqc Hobj) => Habs.
          by apply: normalize__φ_in_abstract_scope_are_inlines.
          move/nf_conformsP: Hqc => [fld Hcontr _].
          by rewrite Hcontr in Hlook.

      * simp normalize; case Hscope : (is_object_type _ ty) => //=.  
        +  orL; apply/andP; split.
           move: Hqc; query_conforms.
           move=> [_ _ _ Hqsc'].
           move: Hv; simp has_valid_fragments. rewrite Hscope /= => /andP [/eqP Heq Hvs'].
           rewrite Heq in Hqsc' Hvs' *.
           by apply: normalize__φ_in_object_scope_are_fields.
           by apply: normalize__φ_in_object_scope_are_fields.
        + case Ht : is_object_type.
          orR; apply/andP; split.
            by rewrite all_seq1.
          move: (type_in_scope_N_obj_is_abstract Hqc Hscope) => Habs.
            by apply: normalize__φ_in_abstract_scope_are_inlines.

            
          move: (type_in_scope_N_obj_is_abstract Hqc Hscope) => Habs.
          move: (normalize__φ_in_abstract_scope_are_inlines _ _ _ Hqsc Hvs Habs) => Hinlines {Hqsc Hvs}.
          move: Hqc; query_conforms.
          move=> [_ _ _ Hqsc].
          move: Hv; simp has_valid_fragments; rewrite Hscope /= => /andP [/orP [/eqP Heq | Hcontr] Hv].
          rewrite -Heq in Habs Hinlines.
          move: (normalize__φ_in_abstract_scope_are_inlines _ _ _ Hqsc Hv Habs) => Hinlines'.
          by orR; apply/andP; split; rewrite -Heq.
          by rewrite Hcontr in Ht.
  Qed.

    *)

  Lemma normalize__φ_in_normal_form schema type_in_scope queries :
     all (query_conforms schema type_in_scope) queries ->
     all (has_valid_fragments schema type_in_scope) queries ->
     are_in_normal_form schema (normalize__φ schema type_in_scope queries).
   Proof.
     
    elim: queries type_in_scope => // hd tl IH ty.
    rewrite {1}/all -/(all _ _) => /andP [Hqc Hqsc].
    rewrite {1}/all -/(all _ _) => /andP [Hv Hvs].
    rewrite normalize__φ_equation_2.
    move: (normalize_in_normal_form _ _ _ Hqc Hv).
    move: (IH ty Hqsc Hvs).
    rewrite /are_in_normal_form ! all_cat => /andP [Htys Hnfs] /andP [Hty Hnf].
    apply/andP; split; last first.
      by apply/andP; split.
      case Hobj: (is_object_type schema ty).
      move: (normalize_in_object_scope_are_fields _ _ _ Hqc Hv Hobj) => Hfld.
      move: (normalize__φ_in_object_scope_are_fields _ _ _ Hqsc Hvs Hobj) => Hflds.
      by orL; apply/andP.
      move: (type_in_scope_N_obj_is_abstract _ _ _ _ _ Hqc Hobj) => Habs.
      move: (normalize_in_abstract_scope_are_any _ _ _ Hqc Hv Habs) => Hinline.
      move: (normalize__φ_in_abstract_scope_are_any _ _ _ Hqsc Hvs Habs) => Hinlines.
      (* Change lemmas to use info on get possible types *)

   Admitted.


   
   Section Beta.
 
     Equations β__φ (flt : Name) (queries : seq (@Query Name Vals)) : seq (@Query Name Vals) :=
       {
         β__φ _ [::] := [::];
         
         β__φ flt (q :: tl)
           with has_same_response_name_or_guard flt q :=
           {
           | true := q.(qsubquery) ++ β__φ flt tl;
           | _ := β__φ flt tl
           }
       }.

     Lemma β__φ_size_reduced flt queries :
       queries_size (β__φ flt queries) <= queries_size queries.
     Proof.
       funelim (β__φ flt queries) => //=.
       move: (subqueries_lt_query q) => Hlt. 
         by rewrite queries_size_app; ssromega.
           by case: q Heq; intros; ssromega.
     Qed.



  
     Lemma cat2s {T : Type} (x y : T) (s : seq T) :
       [:: x] ++ (y :: s) = [:: x, y & s].
     Proof. by case: s. Qed.

     Lemma β__φ_cons q x qs : 
       β__φ q (x :: qs) = (β__φ q [:: x]) ++ (β__φ q qs).
     Proof.
         by funelim (β__φ q (x :: qs)) => //=; simp β__φ; rewrite Heq /=; simp β__φ; rewrite ?cats0 ?cat0s.
     Qed.
  
      
     Lemma β__φ_cat q qs qs' :
       β__φ q (qs ++ qs') = (β__φ q qs) ++ (β__φ q qs').
     Proof.
       elim: qs qs' => // hd tl IH qs'.    
       rewrite cat_cons.
       rewrite β__φ_cons [β__φ q (hd :: tl)]β__φ_cons.
         by rewrite (IH qs') catA.
     Qed.

     Lemma β__φ_has_none_nil flt queries :
       all (fun q => ~~has_same_response_name_or_guard flt q) queries ->
       β__φ flt queries = [::].
     Proof.
       elim: queries => //= hd tl IH /andP [/negbTE Hneq Hall].
       rewrite β__φ_cons. 
       rewrite (IH Hall) cats0.
       by simp β__φ; rewrite Hneq /=.
     Qed.



     Lemma β__φ_preserves_conformance schema flt qs :
       forall ty,
         all (query_conforms schema ty) qs ->
         exists ty', all (query_conforms schema ty') (β__φ flt qs).
     Proof.
       funelim (β__φ flt qs) => //= ty /andP [Hqc Hqsc].
       all: do [move: (H _ _ Hqsc) => [ty' Hqsc']];
         exists ty' => //.
       rewrite all_cat; apply_andP.
     Abort.

     Lemma β__φ_preserves_grounded schema ty flt qs :
       are_grounded_2 schema ty qs ->
       are_grounded_2 schema ty (β__φ flt qs).
     Proof.
       funelim (β__φ flt qs) => //=; case Hscope: is_object_type => //=.
       move/and3P=> [Hty Hg Hgs].
       rewrite -are_grounded_2_cat; split=> //.
       case: q Hg Heq Hty => //=.
     Abort.

       
     
   End Beta.


  Section Gamma.
    
    Definition γ__φ (flt : Name) (queries : seq (@Query Name Vals)) :=
      [seq q <- queries | ~~(has_same_response_name_or_guard flt q)].


    Lemma γ__φ_queries_size_reduced flt queries :
      queries_size (γ__φ flt queries) <= queries_size queries.
    Proof.
      elim: queries => //= hd tl IH.
      by case: ifP => //= Heq; ssromega.
    Qed.
    
    Lemma γ__φ_all_neq flt queries :
      all (fun q => ~~has_same_response_name_or_guard flt q) (γ__φ flt queries).
    Proof.
      apply/allP => q.
      rewrite /γ__φ mem_filter => /andP [H _].
        by move: H; rewrite /negb; case: ifP.
    Qed.

    Lemma γ__φ_N_has flt queries :
      forall q, q \in (γ__φ flt queries) ->
                 has_same_response_name_or_guard flt q = false.

    Proof.
      move=> q.
      rewrite /γ__φ mem_filter => /andP [H _].
        by move: H; rewrite /negb; case: ifP.
    Qed.

    
    Lemma γ__φ_no_repetition_eq flt qs :
      all (fun q => ~~has_same_response_name_or_guard flt q) qs ->
      γ__φ flt qs = qs.
    Proof.
      elim: qs => //= hd tl IH /andP [Hneq Hall].
      case: ifP => Hf.
      by rewrite (IH Hall).
      by rewrite Hneq in Hf.
    Qed.

  
    Lemma γ__φ_preserves_non_redundancy flt queries :
      are_non_redundant queries ->
      are_non_redundant (γ__φ flt queries).
    Proof.
      elim: queries => // hd tl IH.
      case: hd => //= [f α | l f α | f α φ | l f α φ | t φ]; simp are_non_redundant; simp qresponse_name => /and3P [Hall Hnr Hnrs]; case: ifP => //= Heq; last first.
      all: do ?[by apply: IH].

      all: do ?[simp are_non_redundant; apply_and3P].
      all: do ?[move/allP: Hall => Hall;
                apply/allP => q; rewrite mem_filter => /andP [_ Hin];
                apply: (Hall q Hin)].
    Qed.

    Lemma γ__φ_preserves_grounded schema ty flt qs :
      are_grounded_2 schema ty qs ->
      are_grounded_2 schema ty (γ__φ flt qs).
    Proof.
      elim: qs => //= hd tl IH;
      case: ifP => //= _;
      case Hobj : is_object_type => //=.
      all: do ?[case: eqP => //= /eqP Heq].
      all: do ?[move=> /and3P [Hty Hg Hgs]].
      all: do ?[apply_and3P].
      all: do ?[by apply: IH].
    Qed.
    
  End Gamma.

    
  Obligation Tactic := intros; simp query_size; do ? ssromega; rewrite ?queries_size_app.  
  Equations remove_redundancies (queries : seq (@Query Name Vals)) : seq (@Query Name Vals)
    by wf (queries_size queries) lt :=
    {
      remove_redundancies [::] := [::];
      
      remove_redundancies ((SingleField f α) :: queries) :=
        (SingleField f α) :: remove_redundancies (γ__φ f queries);
      
      remove_redundancies ((LabeledField l f α) :: queries) :=
        (LabeledField l f α) :: remove_redundancies (γ__φ l queries);

      remove_redundancies ((NestedField f α φ) :: queries) :=
        (NestedField f α (remove_redundancies (φ ++ (β__φ f queries)))) :: remove_redundancies (γ__φ f queries);

      remove_redundancies ((NestedLabeledField l f α φ) :: queries) :=
        (NestedLabeledField l f α (remove_redundancies (φ ++ (β__φ l queries)))) :: remove_redundancies (γ__φ l queries);

      remove_redundancies ((InlineFragment t φ) :: queries) :=
        (InlineFragment t (remove_redundancies (φ ++ (β__φ t queries)))) :: remove_redundancies (γ__φ t queries)
      
    }.
  Solve Obligations with intros; simp query_size; move: (γ__φ_queries_size_reduced f queries) => Hlt; ssromega.
  Solve Obligations with intros; simp query_size; move: (γ__φ_queries_size_reduced l queries) => Hlt; ssromega.
  
  Next Obligation.
    by move: (β__φ_size_reduced f queries) => Hlt; ssromega.
  Qed.
  Next Obligation.
     by move: (β__φ_size_reduced l queries) => Hlt; ssromega.
  Qed.
  Next Obligation.
    by move: (β__φ_size_reduced t queries) => Hlt; ssromega.
  Qed.
  Next Obligation.
    move: (γ__φ_queries_size_reduced t queries) => Hlt; ssromega.
  Qed.
  
  Equations remove_redundancies__φ query : @Query Name Vals  :=
    {
      remove_redundancies__φ (SingleField f α) := (SingleField f α);
      
      remove_redundancies__φ (LabeledField l f α)  :=   (LabeledField l f α);

      remove_redundancies__φ (NestedField f α φ) := (NestedField f α (remove_redundancies φ)) ;

      remove_redundancies__φ (NestedLabeledField l f α φ) :=
        (NestedLabeledField l f α (remove_redundancies φ)) ;

      remove_redundancies__φ (InlineFragment t φ) :=
        (InlineFragment t (remove_redundancies φ)) 
    }.


  Lemma remove_redundancies_preserves_all_neq flt queries :
    all (fun q => ~~has_same_response_name_or_guard flt q) queries ->
    all (fun q => ~~has_same_response_name_or_guard flt q) (remove_redundancies queries).
  Proof.
    funelim (remove_redundancies queries) => //= /andP [Hneq Hall]; apply_andP.
     
    all: do ?[by apply: H; move/allP: Hall => Hall;
              apply/allP => x; rewrite mem_filter => /andP [_ Hin]; apply: Hall].
    all: do ?[by apply: H0; move/allP: Hall => Hall;
              apply/allP => x; rewrite mem_filter => /andP [_ Hin]; apply: Hall].

  Qed.
    
 

    
  Lemma remove_redundancies_is_non_redundant queries :
    are_non_redundant (remove_redundancies queries).
  Proof.
    funelim (remove_redundancies queries) => //=;
    simp are_non_redundant; simp qresponse_name; apply_and3P;
    apply: remove_redundancies_preserves_all_neq; apply: γ__φ_all_neq.
  Qed.

  Lemma remove_redundancies_preserves_all_fields queries :
    all is_field queries ->
    all is_field (remove_redundancies queries).
  Proof.
    funelim (remove_redundancies queries) => //= /andP [Hfld Hflds]; apply_andP.
    all: do ?[by apply: H; apply: filter_preserves_pred].
    all: do ?[by apply: H0; apply: filter_preserves_pred].
  Qed.

  Lemma remove_redundancies_preserves_all_inlines queries :
    all is_inline_fragment queries ->
    all is_inline_fragment (remove_redundancies queries).
  Proof.
    funelim (remove_redundancies queries) => //= /andP [Hinl Hinls]; apply_andP.
    all: do ?[by apply: H; apply: filter_preserves_pred].
    all: do ?[by apply: H0; apply: filter_preserves_pred].
  Qed.
  


  Lemma notin_in_false {T : eqType} (x : T) (xs : mem_pred T) :
    x \notin xs -> x \in xs = false.
  Proof.
      by rewrite /negb; case: ifP.
  Qed.

 

  Lemma remove_redundancies_inlined_query schema type_in_scope q :
    remove_redundancies [seq InlineFragment ty [:: q] | ty <- get_possible_types schema type_in_scope] =
    [seq InlineFragment ty (remove_redundancies [:: q]) | ty <- get_possible_types schema type_in_scope].
  Proof.
    elim: get_possible_types => //= hd tl IH.
    simp remove_redundancies => /=.
     
  Admitted.
  
   
  Hint Resolve γ__φ_preserves_non_redundancy.
  Lemma non_redundant_eq_remove qs :
    are_non_redundant qs ->
    remove_redundancies qs = qs.
  Proof.
    apply_funelim (remove_redundancies qs) => //= [f α | l f α | f α φ | l f α φ | t φ] χ IH.
    all: do ?[by simp are_non_redundant; simp qresponse_name => /and3P [Hall Hnr Hnrs];
              congr cons;
              rewrite IH; [apply: γ__φ_no_repetition_eq | apply: γ__φ_preserves_non_redundancy]].
    

    all: do ?[by move=> IH2;
              simp are_non_redundant; simp qresponse_name => /and3P [Hall /= Hnr Hnrs];
              rewrite IH ?β__φ_has_none_nil ?cats0 //; congr cons;
              rewrite IH2; [apply: γ__φ_no_repetition_eq | apply: γ__φ_preserves_non_redundancy]].
  Qed.
  
      

  Lemma are_grounded_nil {schema ty} : are_grounded_2 schema ty [::]. Proof. done. Qed.
  Lemma are_non_redundant_nil : @are_non_redundant Name Vals [::]. Proof. done. Qed.


 


  Ltac resolve_grounded := case Hobj : is_object_type => //=; [| case: eqP => //= /eqP Heq].

  
  Lemma remove_redundancies_preserves_grounded schema qs ty :
      are_grounded_2 schema ty qs ->
      are_grounded_2 schema ty (remove_redundancies qs).
  Proof.
    funelim (remove_redundancies qs) => //=; case Hscope: is_object_type => //=.
    
    all: do ?[case: eqP => //= Hpty].
    all: do ?[move/and3P=> [Hty Hg Hgs]; apply_and3P].
    
    all: do ?[move: Hg; simp is_grounded_2; case Hlook: lookup_field_in_type => [fld|] //= Hg].
    all: do ?[by apply: H; apply: γ__φ_preserves_grounded].
    apply: H. rewrite -are_grounded_2_cat; split=> //.
  Admitted.
  

  Lemma obj_spreads_if_in_possible_types_of_interface schema ty ti :
    is_object_type schema ty ->
    is_interface_type schema ti ->
    ty \in get_possible_types schema ti ->
           is_fragment_spread_possible schema ti ty.
  Proof.
    move=> Hobj Hintf Hin.
    rewrite /is_fragment_spread_possible.
    rewrite (get_possible_types_interfaceE Hintf) in Hin *.
    by rewrite get_possible_types_objectE // seq1I Hin.
  Qed.

 
  Lemma map_N_nil {A B : eqType} (xs : seq A) (f : A -> B) :
    xs != [::] ->
    map f xs != [::].
  Proof.
      by case: xs.
  Qed.
        
  Lemma cat_N_nil {T : eqType} (xs xs' : seq T) :

    xs != [::] ->
    xs ++ xs' != [::].

  Proof. by case: xs.
  Qed.
  
  Lemma normalize_N_nil :
    forall schema ty q,
      query_conforms schema ty q ->
      has_valid_fragments schema ty q ->
      normalize schema ty q != [::].
  Proof.
    apply (normalize_elim
             (fun schema ty q nqs =>
                query_conforms schema ty q ->
                has_valid_fragments schema ty q ->
                nqs != [::])
             (fun schema ty qs nqs =>
                qs != [::] ->
                queries_conform schema ty qs ->
                all (has_valid_fragments schema ty) qs ->
                nqs != [::])) => //.
    all: do ?[intros => /=; simp try_inline_query;
              case Hpty: (_ != [::]) => //=;
                by apply: map_N_nil].
    all: do ?[by intros; simp query_conforms in H; rewrite Heq in H].

    - move=> schema t b ty φ IH Ht Hscope.
      query_conforms; move=> [_ _ Hne Hqsc Hmerge].
      simp has_valid_fragments; rewrite Hscope /= => /andP [/eqP Heq Hv].
      rewrite Heq in Hqsc.
       apply: IH => //; rewrite /queries_conform -?Heq; apply_andP.
       by rewrite Heq.
    - move=> schema t ty φ IH Ht Hscope.
      query_conforms; move=> [_ _ Hne Hqsc Hmerge].
      simp has_valid_fragments; rewrite Hscope /= => /andP [/orP [/eqP Heq | Hcontr] Hv].
      rewrite Heq in Hqsc Hv; apply: IH => //; rewrite  /queries_conform; apply_andP.
        by rewrite -Heq.
        by rewrite Ht in Hcontr.

    - move=> schema ty hd tl IHhd IHtl Hne.
      rewrite /queries_conform; case/andP.
      all_cons=> [Hqc Hqsc] _.      
      all_cons=> [Hv Hvs].
      by apply: cat_N_nil; apply: IHhd.
  Qed.
      
        
  Lemma normalize__φ_N_nil schema ty φ :
    φ != [::] ->
    queries_conform schema ty φ ->
    all (has_valid_fragments schema ty) φ ->
    normalize__φ schema ty φ != [::].
  Proof.
    case: φ => //= hd tl _.
    rewrite /queries_conform; case/andP.
    all_cons => [Hqc _] _.
    all_cons => [Hv _].
    apply: cat_N_nil.
    by apply: normalize_N_nil.
  Qed.
    

  Lemma normalize_preserves_conformance :
    forall schema ty q,
      query_conforms schema ty q ->
      has_valid_fragments schema ty q ->
      all (query_conforms schema ty) (normalize schema ty q).
  Proof.
    apply (normalize_elim
             (fun schema ty q nqs =>
                 query_conforms schema ty q ->
                 has_valid_fragments schema ty q ->
                 all (query_conforms schema ty) nqs)
             (fun schema ty qs nqs =>
                 all (query_conforms schema ty) qs ->
                 all (has_valid_fragments schema ty) qs ->
                 all (query_conforms schema ty) nqs)) => schema.
    Proof.
      all: do ?[by intros; rewrite all_seq1].
      all: do ?[intros; simp try_inline_query;
                case: eqP => //= Hpty; rewrite ?andbT //].

      - apply/allP=> x /mapP [q Hin ->].
        simp query_conforms.
        apply/and5P; split=> //.
        * by apply/or3P; constructor 1; apply (in_possible_types_is_object Hin).
        * move: (in_possible_types_is_object Hin) => Hobj.
          have Hfld : is_field (SingleField s0 f) by [].
          move: (scope_is_obj_or_abstract_for_field _ _ _ _ _ Hfld H) => [Hcontr | Hintf]; [by rewrite Heq in Hcontr|].
            by apply: obj_spreads_if_in_possible_types_of_interface.
        * rewrite all_seq1 //.
          have Hfld : is_field (SingleField s0 f) by [].
          move: (scope_is_obj_or_abstract_for_field _ _ _ _ _ Hfld H) => [Hcontr | Hintf]; [by rewrite Heq in Hcontr|].
          rewrite get_possible_types_interfaceE // in Hin.
            by apply (sf_conforms_in_interface_in_obj _ _ _ _ _ _ _ Hin).
            
      - apply/allP=> x /mapP [q Hin ->]; simp query_conforms.
        apply/and5P; split=> //.
        * by apply/or3P; constructor 1; apply (in_possible_types_is_object Hin).
        * move: (in_possible_types_is_object Hin) => Hobj.
          have Hfld : is_field (LabeledField s1 s2 f0) by [].
          move: (scope_is_obj_or_abstract_for_field _ _ _ _ _ Hfld H) => [Hcontr | Hintf]; [by rewrite Heq in Hcontr|].
            by apply: obj_spreads_if_in_possible_types_of_interface.
        * rewrite all_seq1.
          have Hfld : is_field (LabeledField s1 s2 f0) by [].
          move: (scope_is_obj_or_abstract_for_field _ _ _ _ _ Hfld H) => [Hcontr | Hintf]; [by rewrite Heq in Hcontr|].
          rewrite get_possible_types_interfaceE // in Hin.
            
    Admitted.





       
  Lemma normalize__φ_preserves_conformance schema ty qs :
    all (query_conforms schema ty) qs ->
    all (has_valid_fragments schema ty) qs ->
    all (query_conforms schema ty) (normalize__φ schema ty qs).
  Proof.
    
    elim: qs => // hd tl IH /= /andP [Hqc Hqsc] /andP [Hv Hvs].
    rewrite all_cat; apply_andP.
      by apply: normalize_preserves_conformance.
        by apply: IH.
  Qed.


  Lemma remove_redundancies_preserves_grounded_normalize schema ty qs :
    query_conforms schema ty qs ->
    has_valid_fragments schema ty qs ->
    are_grounded_2 schema ty (remove_redundancies (normalize schema ty qs)).
  Proof.
    move=> Hqc Hv.
    apply: remove_redundancies_preserves_grounded.
      by apply: normalize_is_grounded.
  Qed.
        
  Lemma remove_redundancies_preserves_grounded_normalize__φ schema ty qs :
    all (query_conforms schema ty) qs ->
    all (has_valid_fragments schema ty) qs ->
    are_grounded_2 schema ty (remove_redundancies (normalize__φ schema ty qs)).
  Proof.
    move=> Hqsc Hvs.
    apply: remove_redundancies_preserves_grounded => //.
      by apply: normalize__φ_are_grounded.
  Qed.




      
  
  Lemma remove_redundancies_preserves_normal_form_cat :
    forall schema ty qs qs',
      all (query_conforms schema ty) qs ->
      all (has_valid_fragments schema ty) qs ->
      all (query_conforms schema ty) qs' ->
      all (has_valid_fragments schema ty) qs' ->
      are_grounded_2 schema ty qs' ->
      are_grounded_2 schema ty (remove_redundancies (normalize__φ schema ty qs ++ qs')).
  Proof.
    intros.
    apply: remove_redundancies_preserves_grounded.
    rewrite -are_grounded_2_cat; split => //.
      by apply: normalize__φ_are_grounded.
  Qed.


  Lemma remove_redundancies_in_nil_N_nil qs :
    qs != [::] ->
    remove_redundancies qs != [::].
  Proof. by funelim (remove_redundancies qs). Qed.
  
  Lemma remove_redundancies_preserves_conformance schema ty qs :
    all (query_conforms schema ty) qs ->
    all (query_conforms schema ty) (remove_redundancies qs).
  Proof.
    funelim (remove_redundancies qs) => //; all_cons => [Hqc Hqsc].

    all: do ?[by rewrite /all; apply_andP; apply: filter_preserves_pred; apply: H].

    all: do ?[rewrite /all; apply_andP; last by apply: filter_preserves_pred; apply: H].

    all: do [pose Hqc' := Hqc].
    all: do ?[move/nf_conformsP: Hqc' => [fld Hlook /and5P [Hty Hargs Hne Hqc' Hmerge]]; simp query_conforms; rewrite Hlook /=].
    all: do ?[move/nlf_conformsP: Hqc' => [fld Hlook /and5P [Hty Hargs Hne Hqc' Hmerge]]; simp query_conforms; rewrite Hlook /=].
    all: do ?[move: Hqc'; query_conforms; move=> [Hty Hspread Hne Hqc' Hmerge']].
    all: do ?[apply/and5P; split => //].
    all: do ?[by apply: remove_redundancies_in_nil_N_nil; apply: cat_N_nil].
    all: do ?[apply: H0; rewrite all_cat; apply_andP].
    -
      admit.
    -  admit.
    -  admit.
  Admitted.
  
  Lemma remove_redundancies_normalize_preserves_normal_form :
    forall schema type_in_scope query,
      query_conforms schema type_in_scope query ->
      has_valid_fragments schema type_in_scope query -> 
      are_in_normal_form schema (remove_redundancies (normalize schema type_in_scope query)).
  Proof.
    move=> schema ty query Hqc Hv.
    move: (normalize_is_grounded schema ty query Hqc Hv) => Hg.
    move: (remove_redundancies_preserves_grounded_normalize schema ty query Hqc Hv).
    apply: are_grounded_2_in_normal_form.
    apply: remove_redundancies_preserves_conformance.
      by apply: normalize_preserves_conformance.
  Qed.

  Lemma remove_redundancies_normalize__φ_are_in_normal_form :
    forall schema type_in_scope queries,
      all (query_conforms schema type_in_scope) queries ->
      all (has_valid_fragments schema type_in_scope) queries -> 
      are_in_normal_form schema (remove_redundancies (normalize__φ schema type_in_scope queries)).
  Proof.
    move=> schema ty qs Hqc Hv.
    move: (normalize__φ_are_grounded _ _ _ Hqc Hv) => Hg.
    move: (remove_redundancies_preserves_grounded_normalize__φ _ _ _ Hqc Hv).
    apply are_grounded_2_in_normal_form.
     apply: remove_redundancies_preserves_conformance.
      by apply: normalize__φ_preserves_conformance.
  Qed.


  Lemma remove_redundancies_preserves_valid_fragments schema ty queries :
    all (has_valid_fragments schema ty) queries ->
    all (has_valid_fragments schema ty) (remove_redundancies queries).
  Admitted.
 
        
    
    
      
End QueryRewrite.


Arguments normalize [Name Vals].
Arguments normalize_elim [Name Vals].
Arguments normalize__φ [Name Vals].

Arguments γ__φ [Name Vals].
Arguments β__φ [Name Vals].

Arguments remove_redundancies [Name Vals].
Arguments remove_redundancies__φ [Name Vals].
Arguments normalize_preserves_conformance [Name Vals].

Arguments normalize_in_normal_form [Name Vals].